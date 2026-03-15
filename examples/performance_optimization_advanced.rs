//! # 高级性能优化示例
//!
//! 展示 OTLP Rust 的高级性能优化技巧：
//! - 内存池化
//! - 零拷贝序列化
//! - SIMD 加速
//! - 异步批处理
//! - 锁-free 数据结构
//! - CPU 亲和性

use anyhow::Result;
use crossbeam::queue::ArrayQueue;
use std::alloc::{alloc, dealloc, Layout};
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Instant;
use tokio::sync::mpsc;

/// ============================================
/// 1. 内存池化 - 减少分配开销
/// ============================================

pub struct ByteBufferPool {
    pool: ArrayQueue<Vec<u8>>,
    buffer_size: usize,
    max_size: usize,
    allocated: AtomicU64,
}

impl ByteBufferPool {
    pub fn new(buffer_size: usize, max_size: usize) -> Self {
        let pool = ArrayQueue::new(max_size);
        
        // 预分配缓冲区
        for _ in 0..max_size {
            let buffer = vec![0u8; buffer_size];
            let _ = pool.push(buffer);
        }
        
        Self {
            pool,
            buffer_size,
            max_size,
            allocated: AtomicU64::new(max_size as u64),
        }
    }

    pub fn acquire(&self) -> PooledBuffer {
        match self.pool.pop() {
            Some(mut buffer) => {
                buffer.clear();
                PooledBuffer {
                    buffer: Some(buffer),
                    pool: self,
                }
            }
            None => {
                self.allocated.fetch_add(1, Ordering::Relaxed);
                PooledBuffer {
                    buffer: Some(vec![0u8; self.buffer_size]),
                    pool: self,
                }
            }
        }
    }

    fn release(&self, buffer: Vec<u8>) {
        let _ = self.pool.push(buffer);
    }

    pub fn stats(&self) -> PoolStats {
        PoolStats {
            available: self.pool.len(),
            max_size: self.max_size,
            total_allocated: self.allocated.load(Ordering::Relaxed),
        }
    }
}

pub struct PoolStats {
    pub available: usize,
    pub max_size: usize,
    pub total_allocated: u64,
}

pub struct PooledBuffer<'a> {
    buffer: Option<Vec<u8>>,
    pool: &'a ByteBufferPool,
}

impl<'a> std::ops::Deref for PooledBuffer<'a> {
    type Target = Vec<u8>;
    fn deref(&self) -> &Self::Target {
        self.buffer.as_ref().unwrap()
    }
}

impl<'a> std::ops::DerefMut for PooledBuffer<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.buffer.as_mut().unwrap()
    }
}

impl<'a> Drop for PooledBuffer<'a> {
    fn drop(&mut self) {
        if let Some(buffer) = self.buffer.take() {
            self.pool.release(buffer);
        }
    }
}

/// ============================================
/// 2. 零拷贝序列化
/// ============================================

/// 使用 FlatBuffers 风格的直接内存写入
pub struct ZeroCopySerializer {
    buffer: Vec<u8>,
    offset: usize,
}

impl ZeroCopySerializer {
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            buffer: Vec::with_capacity(capacity),
            offset: 0,
        }
    }

    /// 直接写入 u64 而不创建临时对象
    #[inline(always)]
    pub fn write_u64(&mut self, value: u64) {
        self.buffer.extend_from_slice(&value.to_le_bytes());
        self.offset += 8;
    }

    #[inline(always)]
    pub fn write_u32(&mut self, value: u32) {
        self.buffer.extend_from_slice(&value.to_le_bytes());
        self.offset += 4;
    }

    #[inline(always)]
    pub fn write_bytes(&mut self, bytes: &[u8]) {
        self.write_u32(bytes.len() as u32);
        self.buffer.extend_from_slice(bytes);
        self.offset += 4 + bytes.len();
    }

    #[inline(always)]
    pub fn write_str(&mut self, s: &str) {
        self.write_bytes(s.as_bytes());
    }

    pub fn into_vec(self) -> Vec<u8> {
        self.buffer
    }
}

/// ============================================
/// 3. SIMD 加速处理
/// ============================================

#[cfg(target_arch = "x86_64")]
pub mod simd {
    use std::arch::x86_64::*;

    /// 使用 AVX2 批量计算指标聚合
    pub unsafe fn sum_f32_avx2(values: &[f32]) -> f32 {
        let mut sum_vec = _mm256_setzero_ps();
        let chunks = values.chunks_exact(8);
        let remainder = chunks.remainder();

        for chunk in chunks {
            let vec = _mm256_loadu_ps(chunk.as_ptr());
            sum_vec = _mm256_add_ps(sum_vec, vec);
        }

        // 水平求和
        let sum_128 = _mm_add_ps(
            _mm256_castps256_ps128(sum_vec),
            _mm256_extractf128_ps(sum_vec, 1)
        );
        let sum_64 = _mm_add_ps(sum_128, _mm_movehl_ps(sum_128, sum_128));
        let sum_32 = _mm_add_ss(sum_64, _mm_shuffle_ps(sum_64, sum_64, 0x55));
        
        let mut sum = _mm_cvtss_f32(sum_32);
        
        // 处理剩余元素
        for &val in remainder {
            sum += val;
        }
        
        sum
    }

    /// 使用 SSE2 批量比较字符串
    pub unsafe fn fast_string_compare_sse2(a: &[u8], b: &[u8]) -> bool {
        if a.len() != b.len() {
            return false;
        }

        let chunks = a.chunks_exact(16);
        let b_chunks = b.chunks_exact(16);
        let a_remainder = chunks.remainder();
        let b_remainder = b_chunks.remainder();

        for (a_chunk, b_chunk) in chunks.zip(b_chunks) {
            let a_vec = _mm_loadu_si128(a_chunk.as_ptr() as *const __m128i);
            let b_vec = _mm_loadu_si128(b_chunk.as_ptr() as *const __m128i);
            let cmp = _mm_cmpeq_epi8(a_vec, b_vec);
            let mask = _mm_movemask_epi8(cmp);
            if mask != 0xFFFF {
                return false;
            }
        }

        a_remainder == b_remainder
    }
}

/// ============================================
/// 4. 锁-free 计数器
/// ============================================

pub struct LockFreeMetrics {
    counters: Vec<AtomicU64>,
    names: Vec<String>,
}

impl LockFreeMetrics {
    pub fn new(names: Vec<String>) -> Self {
        let counters: Vec<AtomicU64> = (0..names.len())
            .map(|_| AtomicU64::new(0))
            .collect();
        
        Self { counters, names }
    }

    #[inline(always)]
    pub fn increment(&self, index: usize) {
        if index < self.counters.len() {
            self.counters[index].fetch_add(1, Ordering::Relaxed);
        }
    }

    #[inline(always)]
    pub fn add(&self, index: usize, value: u64) {
        if index < self.counters.len() {
            self.counters[index].fetch_add(value, Ordering::Relaxed);
        }
    }

    pub fn snapshot(&self) -> HashMap<String, u64> {
        self.names
            .iter()
            .zip(self.counters.iter())
            .map(|(name, counter)| (name.clone(), counter.load(Ordering::Relaxed)))
            .collect()
    }

    pub fn reset(&self) {
        for counter in &self.counters {
            counter.store(0, Ordering::Relaxed);
        }
    }
}

/// ============================================
/// 5. 批量异步处理器
/// ============================================

pub struct OptimizedBatchProcessor<T> {
    sender: mpsc::Sender<T>,
    batch_size: usize,
    flush_interval_ms: u64,
}

impl<T: Send + 'static> OptimizedBatchProcessor<T> {
    pub fn new<F>(
        batch_size: usize,
        flush_interval_ms: u64,
        mut handler: F,
    ) -> (Self, mpsc::Receiver<()>) where
        F: FnMut(Vec<T>) + Send + 'static,
    {
        let (sender, mut receiver) = mpsc::channel::<T>(batch_size * 2);
        let (control_sender, control_receiver) = mpsc::channel(1);

        tokio::spawn(async move {
            let mut batch = Vec::with_capacity(batch_size);
            let mut interval = tokio::time::interval(
                tokio::time::Duration::from_millis(flush_interval_ms)
            );

            loop {
                tokio::select! {
                    Some(item) = receiver.recv() => {
                        batch.push(item);
                        if batch.len() >= batch_size {
                            handler(std::mem::replace(
                                &mut batch,
                                Vec::with_capacity(batch_size)
                            ));
                        }
                    }
                    _ = interval.tick() => {
                        if !batch.is_empty() {
                            handler(std::mem::replace(
                                &mut batch,
                                Vec::with_capacity(batch_size)
                            ));
                        }
                    }
                    else => break,
                }
            }
            
            // 处理剩余数据
            if !batch.is_empty() {
                handler(batch);
            }
            
            let _ = control_sender.send(()).await;
        });

        let processor = Self {
            sender,
            batch_size,
            flush_interval_ms,
        };

        (processor, control_receiver)
    }

    pub async fn send(&self, item: T) -> Result<()> {
        self.sender.send(item).await?;
        Ok(())
    }
}

/// ============================================
/// 6. 性能测试基准
/// ============================================

pub struct Benchmark {
    name: String,
    iterations: u64,
    total_duration_ns: u64,
}

impl Benchmark {
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            iterations: 0,
            total_duration_ns: 0,
        }
    }

    pub fn run<F, T>(&mut self, f: F) -> T
    where
        F: FnOnce() -> T,
    {
        let start = Instant::now();
        let result = f();
        self.total_duration_ns += start.elapsed().as_nanos() as u64;
        self.iterations += 1;
        result
    }

    pub fn report(&self) {
        if self.iterations > 0 {
            let avg_ns = self.total_duration_ns / self.iterations;
            println!(
                "Benchmark [{}]: {} iterations, avg {} ns/op, {} ops/sec",
                self.name,
                self.iterations,
                avg_ns,
                1_000_000_000 / avg_ns
            );
        }
    }
}

/// ============================================
/// 演示主程序
/// ============================================

#[tokio::main]
async fn main() -> Result<()> {
    println!("=== 高级性能优化示例 ===\n");

    // 1. 内存池化性能测试
    println!("1. 内存池化性能测试:");
    {
        let pool = Arc::new(ByteBufferPool::new(1024, 100));
        
        let mut bench = Benchmark::new("pooled_buffer");
        for _ in 0..10000 {
            bench.run(|| {
                let mut buffer = pool.acquire();
                buffer.extend_from_slice(b"test data");
                // buffer 自动归还
            });
        }
        bench.report();

        let stats = pool.stats();
        println!("   池统计: 可用 {}, 总分配 {}\n", stats.available, stats.total_allocated);
    }

    // 2. 零拷贝序列化性能测试
    println!("2. 零拷贝序列化性能测试:");
    {
        let mut bench = Benchmark::new("zero_copy_serialize");
        
        for _ in 0..100000 {
            bench.run(|| {
                let mut serializer = ZeroCopySerializer::with_capacity(256);
                serializer.write_u64(123456789);
                serializer.write_str("test_metric");
                serializer.write_f64(99.99);
                serializer.into_vec()
            });
        }
        bench.report();
        println!();
    }

    // 3. SIMD 计算测试
    #[cfg(target_arch = "x86_64")]
    {
        println!("3. SIMD 计算性能测试:");
        let values: Vec<f32> = (0..1000).map(|i| i as f32).collect();
        
        // 标量求和
        let mut bench_scalar = Benchmark::new("scalar_sum");
        for _ in 0..10000 {
            bench_scalar.run(|| {
                values.iter().sum::<f32>()
            });
        }
        bench_scalar.report();

        // AVX2 求和
        let mut bench_simd = Benchmark::new("avx2_sum");
        for _ in 0..10000 {
            bench_simd.run(|| unsafe {
                simd::sum_f32_avx2(&values)
            });
        }
        bench_simd.report();
        println!();
    }

    // 4. 锁-free 计数器测试
    println!("4. 锁-free 计数器测试:");
    {
        let metrics = Arc::new(LockFreeMetrics::new(vec![
            "requests".to_string(),
            "errors".to_string(),
            "latency".to_string(),
        ]));

        let mut handles = vec![];
        
        for thread_id in 0..4 {
            let metrics = metrics.clone();
            handles.push(std::thread::spawn(move || {
                for i in 0..100000 {
                    metrics.increment(0); // requests
                    if i % 100 == 0 {
                        metrics.increment(1); // errors
                    }
                    metrics.add(2, i as u64 % 100); // latency
                }
                thread_id
            }));
        }

        for handle in handles {
            handle.join().unwrap();
        }

        let snapshot = metrics.snapshot();
        println!("   最终指标:");
        for (name, value) in snapshot {
            println!("     {}: {}", name, value);
        }
        println!();
    }

    // 5. 批量处理器测试
    println!("5. 批量异步处理器测试:");
    {
        let processed = Arc::new(AtomicU64::new(0));
        let processed_clone = processed.clone();

        let (processor, mut done) = OptimizedBatchProcessor::new(
            100,
            100,
            move |batch: Vec<u64>| {
                processed_clone.fetch_add(batch.len() as u64, Ordering::Relaxed);
            },
        );

        let start = Instant::now();
        
        // 发送 1000 个任务
        for i in 0..1000 {
            processor.send(i).await?;
        }

        // 等待处理完成
        drop(processor);
        let _ = done.recv().await;

        println!("   处理 {} 个任务, 耗时 {:?}", 
            processed.load(Ordering::Relaxed),
            start.elapsed()
        );
        println!();
    }

    println!("=== 示例完成 ===");
    Ok(())
}
