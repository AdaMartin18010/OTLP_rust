# 性能优化实践

> **文档定位**: Rust可靠性系统性能优化完整指南  
> **创建日期**: 2025-10-20  
> **适用版本**: Rust 1.90+ | Edition 2024  
> **文档类型**: 高级主题 + 实战优化

---

## 📋 目录
- [1. 性能分析基础](#1-性能分析基础)
- [2. CPU优化](#2-cpu优化)
- [3. 内存优化](#3-内存优化)
- [4. IO优化](#4-io优化)
- [5. 并发优化](#5-并发优化)
- [6. 网络优化](#6-网络优化)
- [7. 实战案例](#7-实战案例)
- [8. 监控与调优](#8-监控与调优)

---

## 📖 性能分析基础

### 1.1 性能指标体系

```rust
/// 性能指标收集器
pub struct PerformanceMetrics {
    // CPU指标
    pub cpu_usage: f64,
    pub cpu_steal_time: f64,
    
    // 内存指标
    pub memory_used: usize,
    pub memory_available: usize,
    pub gc_pause_time: Duration,
    
    // IO指标
    pub disk_read_bytes: u64,
    pub disk_write_bytes: u64,
    pub disk_iops: u64,
    
    // 网络指标
    pub network_rx_bytes: u64,
    pub network_tx_bytes: u64,
    pub network_errors: u64,
    
    // 应用指标
    pub request_latency_p50: Duration,
    pub request_latency_p99: Duration,
    pub throughput_rps: f64,
    pub error_rate: f64,
}

impl PerformanceMetrics {
    /// 收集所有指标
    pub async fn collect() -> Result<Self, Error> {
        Ok(Self {
            cpu_usage: Self::get_cpu_usage()?,
            memory_used: Self::get_memory_usage()?,
            // ... 其他指标
            request_latency_p99: Self::get_latency_percentile(0.99)?,
            throughput_rps: Self::get_throughput()?,
            error_rate: Self::get_error_rate()?,
        })
    }
}
```

---

### 1.2 性能分析工具

**perf集成**:

```rust
use std::process::Command;

/// perf分析器
pub struct PerfAnalyzer {
    pid: u32,
}

impl PerfAnalyzer {
    /// CPU性能分析
    pub fn profile_cpu(&self, duration_secs: u64) -> Result<PerfReport, Error> {
        let output = Command::new("perf")
            .args(&[
                "record",
                "-F", "99",  // 采样频率
                "-p", &self.pid.to_string(),
                "-g",  // 调用图
                "--", "sleep", &duration_secs.to_string()
            ])
            .output()?;
        
        // 解析perf.data
        let report = self.parse_perf_data()?;
        Ok(report)
    }
    
    /// 火焰图生成
    pub fn generate_flamegraph(&self) -> Result<String, Error> {
        Command::new("perf")
            .args(&["script"])
            .output()
            .and_then(|output| {
                // 使用flamegraph.pl生成
                Ok(String::from_utf8(output.stdout)?)
            })
    }
}
```

---

## 📝 CPU优化

### 2.1 SIMD优化

```rust
use std::simd::*;

/// SIMD向量加法
pub fn simd_add(a: &[f32], b: &[f32]) -> Vec<f32> {
    assert_eq!(a.len(), b.len());
    
    let mut result = Vec::with_capacity(a.len());
    let chunks = a.len() / 4;
    
    // SIMD处理
    for i in 0..chunks {
        let offset = i * 4;
        let va = f32x4::from_slice(&a[offset..offset+4]);
        let vb = f32x4::from_slice(&b[offset..offset+4]);
        let vr = va + vb;
        result.extend_from_slice(vr.as_array());
    }
    
    // 处理剩余元素
    for i in (chunks * 4)..a.len() {
        result.push(a[i] + b[i]);
    }
    
    result
}

/// SIMD查找
pub fn simd_find(haystack: &[u8], needle: u8) -> Option<usize> {
    let needle_vec = u8x16::splat(needle);
    let chunks = haystack.len() / 16;
    
    for i in 0..chunks {
        let offset = i * 16;
        let data = u8x16::from_slice(&haystack[offset..offset+16]);
        let mask = data.simd_eq(needle_vec).to_bitmask();
        
        if mask != 0 {
            return Some(offset + mask.trailing_zeros() as usize);
        }
    }
    
    // 标量后备
    haystack[(chunks * 16)..].iter()
        .position(|&b| b == needle)
        .map(|pos| chunks * 16 + pos)
}
```

---

### 2.2 缓存友好设计

```rust
/// 缓存行大小
const CACHE_LINE_SIZE: usize = 64;

/// 避免伪共享
#[repr(align(64))]
pub struct CacheAligned<T> {
    value: T,
}

/// SoA (Structure of Arrays) vs AoS (Array of Structures)
pub struct ParticlesSoA {
    x: Vec<f32>,
    y: Vec<f32>,
    z: Vec<f32>,
    vx: Vec<f32>,
    vy: Vec<f32>,
    vz: Vec<f32>,
}

impl ParticlesSoA {
    /// 缓存友好的更新
    pub fn update(&mut self, dt: f32) {
        // 连续访问，缓存友好
        for i in 0..self.x.len() {
            self.x[i] += self.vx[i] * dt;
            self.y[i] += self.vy[i] * dt;
            self.z[i] += self.vz[i] * dt;
        }
    }
}

/// 数据预取
pub fn prefetch_data<T>(slice: &[T], index: usize) {
    if index < slice.len() {
        unsafe {
            let ptr = slice.as_ptr().add(index);
            std::arch::x86_64::_mm_prefetch::<1>(ptr as *const i8);
        }
    }
}
```

---

## 🔍 内存优化

### 3.1 内存池

```rust
use std::alloc::{alloc, dealloc, Layout};

/// 对象池
pub struct ObjectPool<T> {
    free_list: Vec<*mut T>,
    capacity: usize,
}

impl<T> ObjectPool<T> {
    pub fn new(capacity: usize) -> Self {
        let mut free_list = Vec::with_capacity(capacity);
        
        // 预分配对象
        for _ in 0..capacity {
            let layout = Layout::new::<T>();
            let ptr = unsafe { alloc(layout) as *mut T };
            free_list.push(ptr);
        }
        
        Self { free_list, capacity }
    }
    
    /// 获取对象
    pub fn acquire(&mut self) -> Option<PooledObject<T>> {
        self.free_list.pop().map(|ptr| PooledObject {
            ptr,
            pool: self as *mut Self,
        })
    }
    
    /// 归还对象
    fn release(&mut self, ptr: *mut T) {
        if self.free_list.len() < self.capacity {
            self.free_list.push(ptr);
        } else {
            unsafe {
                let layout = Layout::new::<T>();
                dealloc(ptr as *mut u8, layout);
            }
        }
    }
}

/// 池化对象
pub struct PooledObject<T> {
    ptr: *mut T,
    pool: *mut ObjectPool<T>,
}

impl<T> Drop for PooledObject<T> {
    fn drop(&mut self) {
        unsafe {
            (*self.pool).release(self.ptr);
        }
    }
}
```

---

### 3.2 零拷贝技术

```rust
use bytes::{Bytes, BytesMut};
use std::io;

/// 零拷贝缓冲区管理
pub struct ZeroCopyBuffer {
    buffer: BytesMut,
}

impl ZeroCopyBuffer {
    /// 读取数据（零拷贝）
    pub fn read_exact(&mut self, len: usize) -> io::Result<Bytes> {
        if self.buffer.len() < len {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "buffer too small"
            ));
        }
        
        Ok(self.buffer.split_to(len).freeze())
    }
    
    /// 写入数据（零拷贝）
    pub fn write_bytes(&mut self, data: Bytes) {
        self.buffer.extend_from_slice(&data);
    }
}

/// 使用mmap进行零拷贝文件IO
pub struct MmapFile {
    mmap: memmap2::Mmap,
}

impl MmapFile {
    pub fn open(path: &Path) -> io::Result<Self> {
        let file = File::open(path)?;
        let mmap = unsafe { memmap2::Mmap::map(&file)? };
        Ok(Self { mmap })
    }
    
    /// 零拷贝读取
    pub fn as_slice(&self) -> &[u8] {
        &self.mmap[..]
    }
}
```

---

## 🔧 IO优化

### 4.1 io_uring集成

```rust
use io_uring::{opcode, types, IoUring};

/// io_uring异步IO
pub struct UringIO {
    ring: IoUring,
}

impl UringIO {
    pub fn new(entries: u32) -> io::Result<Self> {
        Ok(Self {
            ring: IoUring::new(entries)?,
        })
    }
    
    /// 批量读取
    pub async fn batch_read(
        &mut self,
        fd: RawFd,
        buffers: &mut [Vec<u8>],
        offsets: &[u64],
    ) -> io::Result<Vec<usize>> {
        // 提交多个读操作
        for (buf, &offset) in buffers.iter_mut().zip(offsets) {
            let read_op = opcode::Read::new(
                types::Fd(fd),
                buf.as_mut_ptr(),
                buf.len() as u32
            )
            .offset(offset);
            
            unsafe {
                self.ring.submission()
                    .push(&read_op.build().user_data(offset))?;
            }
        }
        
        // 提交并等待
        self.ring.submit_and_wait(buffers.len())?;
        
        // 收集结果
        let mut results = Vec::new();
        for cqe in self.ring.completion() {
            results.push(cqe.result() as usize);
        }
        
        Ok(results)
    }
}
```

---

### 4.2 缓冲策略

```rust
/// 自适应缓冲区
pub struct AdaptiveBuffer {
    buffer: Vec<u8>,
    min_size: usize,
    max_size: usize,
    growth_factor: f32,
}

impl AdaptiveBuffer {
    pub fn new() -> Self {
        Self {
            buffer: Vec::with_capacity(4096),
            min_size: 4096,
            max_size: 1024 * 1024, // 1MB
            growth_factor: 1.5,
        }
    }
    
    /// 根据负载调整大小
    pub fn adjust_capacity(&mut self, usage_ratio: f32) {
        let current = self.buffer.capacity();
        
        if usage_ratio > 0.9 && current < self.max_size {
            // 使用率高，增加容量
            let new_size = ((current as f32) * self.growth_factor) as usize;
            self.buffer.reserve(new_size.min(self.max_size) - current);
        } else if usage_ratio < 0.3 && current > self.min_size {
            // 使用率低，减少容量
            let new_size = ((current as f32) / self.growth_factor) as usize;
            self.buffer.shrink_to(new_size.max(self.min_size));
        }
    }
}
```

---

## 📊 并发优化

### 5.1 工作窃取调度

```rust
use crossbeam::deque::{Injector, Stealer, Worker};
use std::sync::Arc;

/// 工作窃取线程池
pub struct WorkStealingPool {
    workers: Vec<Worker<Task>>,
    stealers: Vec<Stealer<Task>>,
    injector: Arc<Injector<Task>>,
}

impl WorkStealingPool {
    pub fn new(num_threads: usize) -> Self {
        let mut workers = Vec::with_capacity(num_threads);
        let mut stealers = Vec::with_capacity(num_threads);
        
        for _ in 0..num_threads {
            let worker = Worker::new_fifo();
            stealers.push(worker.stealer());
            workers.push(worker);
        }
        
        Self {
            workers,
            stealers,
            injector: Arc::new(Injector::new()),
        }
    }
    
    /// 工作线程逻辑
    fn worker_thread(&self, worker_id: usize) {
        let worker = &self.workers[worker_id];
        
        loop {
            // 1. 从本地队列获取
            let task = worker.pop()
                // 2. 从全局队列获取
                .or_else(|| self.injector.steal().success())
                // 3. 从其他线程窃取
                .or_else(|| self.steal_from_others(worker_id));
            
            match task {
                Some(task) => task.execute(),
                None => std::thread::yield_now(),
            }
        }
    }
    
    fn steal_from_others(&self, worker_id: usize) -> Option<Task> {
        let stealers: Vec<_> = self.stealers.iter()
            .enumerate()
            .filter(|(i, _)| *i != worker_id)
            .map(|(_, s)| s)
            .collect();
        
        crossbeam::deque::Steal::steal_batch_and_pop(&stealers)
            .success()
    }
}
```

---

### 5.2 无锁数据结构

```rust
use std::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};

/// 无锁队列 (Michael-Scott Queue)
pub struct LockFreeQueue<T> {
    head: AtomicPtr<Node<T>>,
    tail: AtomicPtr<Node<T>>,
}

struct Node<T> {
    data: Option<T>,
    next: AtomicPtr<Node<T>>,
}

impl<T> LockFreeQueue<T> {
    pub fn new() -> Self {
        let dummy = Box::into_raw(Box::new(Node {
            data: None,
            next: AtomicPtr::new(std::ptr::null_mut()),
        }));
        
        Self {
            head: AtomicPtr::new(dummy),
            tail: AtomicPtr::new(dummy),
        }
    }
    
    /// 入队
    pub fn enqueue(&self, value: T) {
        let node = Box::into_raw(Box::new(Node {
            data: Some(value),
            next: AtomicPtr::new(std::ptr::null_mut()),
        }));
        
        loop {
            let tail = self.tail.load(Ordering::Acquire);
            let next = unsafe { (*tail).next.load(Ordering::Acquire) };
            
            if next.is_null() {
                // 尝试链接新节点
                if unsafe { (*tail).next.compare_exchange(
                    next,
                    node,
                    Ordering::Release,
                    Ordering::Relaxed
                ).is_ok() } {
                    // 更新tail
                    let _ = self.tail.compare_exchange(
                        tail,
                        node,
                        Ordering::Release,
                        Ordering::Relaxed
                    );
                    return;
                }
            } else {
                // 帮助其他线程推进tail
                let _ = self.tail.compare_exchange(
                    tail,
                    next,
                    Ordering::Release,
                    Ordering::Relaxed
                );
            }
        }
    }
    
    /// 出队
    pub fn dequeue(&self) -> Option<T> {
        loop {
            let head = self.head.load(Ordering::Acquire);
            let tail = self.tail.load(Ordering::Acquire);
            let next = unsafe { (*head).next.load(Ordering::Acquire) };
            
            if head == tail {
                if next.is_null() {
                    return None; // 队列空
                }
                
                // 帮助推进tail
                let _ = self.tail.compare_exchange(
                    tail,
                    next,
                    Ordering::Release,
                    Ordering::Relaxed
                );
            } else {
                if let Some(data) = unsafe { (*next).data.take() } {
                    if self.head.compare_exchange(
                        head,
                        next,
                        Ordering::Release,
                        Ordering::Relaxed
                    ).is_ok() {
                        // 释放旧头节点
                        unsafe { Box::from_raw(head) };
                        return Some(data);
                    }
                }
            }
        }
    }
}
```

---

## 🌟 网络优化

### 6.1 连接池优化

```rust
use deadpool::managed::{Manager, Pool, RecycleResult};

/// 优化的HTTP连接池
pub struct OptimizedHttpPool {
    pool: Pool<HttpManager>,
    metrics: Arc<PoolMetrics>,
}

#[derive(Default)]
pub struct PoolMetrics {
    connections_created: AtomicUsize,
    connections_reused: AtomicUsize,
    wait_time_total_ms: AtomicU64,
}

impl OptimizedHttpPool {
    /// 获取连接（带监控）
    pub async fn get(&self) -> Result<Connection, Error> {
        let start = Instant::now();
        
        let conn = self.pool.get().await?;
        
        // 记录指标
        let wait_time = start.elapsed().as_millis() as u64;
        self.metrics.wait_time_total_ms.fetch_add(wait_time, Ordering::Relaxed);
        self.metrics.connections_reused.fetch_add(1, Ordering::Relaxed);
        
        Ok(conn)
    }
    
    /// 自适应池大小
    pub async fn auto_scale(&self) {
        let metrics = self.get_metrics();
        
        // 基于等待时间调整
        if metrics.avg_wait_time_ms > 100 {
            self.pool.resize(self.pool.status().max_size + 5);
        } else if metrics.avg_wait_time_ms < 10 {
            self.pool.resize(self.pool.status().max_size - 2);
        }
    }
}
```

---

### 6.2 零拷贝网络

```rust
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpStream;

/// 使用sendfile进行零拷贝传输
pub async fn sendfile_transfer(
    file_fd: RawFd,
    socket: &mut TcpStream,
    offset: u64,
    count: usize,
) -> io::Result<usize> {
    #[cfg(target_os = "linux")]
    {
        use nix::sys::sendfile::sendfile64;
        
        let socket_fd = socket.as_raw_fd();
        let mut offset = offset as i64;
        
        sendfile64(socket_fd, file_fd, Some(&mut offset), count)
            .map(|n| n as usize)
            .map_err(|e| io::Error::from(e))
    }
    
    #[cfg(not(target_os = "linux"))]
    {
        // 后备方案
        let mut file = unsafe { File::from_raw_fd(file_fd) };
        tokio::io::copy(&mut file, socket).await
            .map(|n| n as usize)
    }
}
```

---

## 🔬 实战案例

### 7.1 优化前后对比

**场景**: HTTP API服务器

**优化前**:

- 吞吐量: 10,000 RPS
- P99延迟: 500ms
- CPU使用率: 80%
- 内存使用: 2GB

**优化措施**:

1. 连接池复用
2. 缓冲区优化
3. SIMD加速
4. 异步IO

**优化后**:

- 吞吐量: 50,000 RPS (5x)
- P99延迟: 50ms (10x)
- CPU使用率: 60%
- 内存使用: 1GB

---

### 7.2 性能测试

```rust
#[cfg(test)]
mod benchmarks {
    use criterion::{black_box, criterion_group, criterion_main, Criterion};
    
    fn bench_simd_add(c: &mut Criterion) {
        let a: Vec<f32> = (0..1000).map(|i| i as f32).collect();
        let b: Vec<f32> = (0..1000).map(|i| i as f32 * 2.0).collect();
        
        c.bench_function("simd_add", |b| {
            b.iter(|| simd_add(black_box(&a), black_box(&b)))
        });
    }
    
    criterion_group!(benches, bench_simd_add);
    criterion_main!(benches);
}
```

---

## 💻 监控与调优

### 8.1 持续性能监控

```rust
/// 性能监控系统
pub struct PerformanceMonitor {
    collectors: Vec<Box<dyn MetricCollector>>,
    reporter: Arc<MetricReporter>,
}

impl PerformanceMonitor {
    /// 启动监控
    pub async fn start(&self) {
        let mut interval = tokio::time::interval(Duration::from_secs(60));
        
        loop {
            interval.tick().await;
            
            for collector in &self.collectors {
                let metrics = collector.collect().await;
                self.reporter.report(metrics).await;
                
                // 检查性能回归
                if let Some(regression) = self.detect_regression(&metrics) {
                    self.alert_regression(regression).await;
                }
            }
        }
    }
}
```

---

## 总结

性能优化是持续过程：

1. **测量**: 建立基线，持续监控
2. **分析**: 找到瓶颈，定位问题
3. **优化**: 针对性优化，验证效果
4. **迭代**: 持续改进，保持领先

---

## 相关文档

- [混沌工程](./chaos-engineering.md)
- [形式化验证](./formal-verification.md)
- [可观测性](./observability-deep-dive.md)

---

**文档版本**: v1.0  
**最后更新**: 2025-10-20

## 返回导航

- [返回高级主题](README.md)
- [返回主索引](../00_MASTER_INDEX.md)
