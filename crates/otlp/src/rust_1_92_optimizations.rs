//! # Rust 1.92 Edition=2024 特性优化实现
//!
//! 本模块展示了如何在OTLP项目中使用Rust 1.92 edition=2024的新特性
//! 包括异步闭包、元组收集、性能优化等

use anyhow::Result;
use std::arch::x86_64::*;
use std::borrow::Cow;
use std::collections::HashMap;
use std::future::Future;
use std::ptr;
use std::sync::Arc;
use tokio::sync::Mutex;

/// 异步闭包优化示例
///
/// 展示如何使用Rust 1.92的新异步闭包特性替代BoxFuture
pub struct AsyncClosureOptimizer;

impl AsyncClosureOptimizer {
    /// 优化前：使用BoxFuture的版本
    #[allow(dead_code)]
    pub async fn call_with_box_future<F, R>(&self, f: F) -> Result<R>
    where
        F: FnOnce() -> futures::future::BoxFuture<'static, Result<R, anyhow::Error>>,
    {
        f().await
    }

    /// 优化后：使用Rust 1.92异步闭包特性的版本
    pub async fn call_with_async_closure<F, Fut, R>(&self, f: F) -> Result<R>
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = Result<R, anyhow::Error>> + Send + 'static,
        R: Send,
    {
        f().await
    }

    /// 异步闭包在熔断器中的应用
    pub async fn circuit_breaker_call<F, Fut, R>(&self, f: F) -> Result<R>
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = Result<R, anyhow::Error>> + Send + 'static,
        R: Send,
    {
        let state = self.check_circuit_state().await;
        self.handle_circuit_state(state, f).await
    }

    /// 处理熔断器状态
    async fn handle_circuit_state<F, Fut, R>(&self, state: CircuitState, f: F) -> Result<R>
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = Result<R, anyhow::Error>> + Send + 'static,
        R: Send,
    {
        match state {
            CircuitState::Closed => self.handle_closed_state(f).await,
            CircuitState::Open => Err(anyhow::anyhow!("Circuit breaker is open")),
            CircuitState::HalfOpen => self.handle_half_open_state(f).await,
        }
    }

    /// 处理关闭状态
    async fn handle_closed_state<F, Fut, R>(&self, f: F) -> Result<R>
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = Result<R, anyhow::Error>> + Send + 'static,
        R: Send,
    {
        match f().await {
            Ok(result) => {
                self.record_success().await;
                Ok(result)
            }
            Err(e) => {
                self.record_failure().await;
                Err(e)
            }
        }
    }

    /// 处理半开状态
    async fn handle_half_open_state<F, Fut, R>(&self, f: F) -> Result<R>
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = Result<R, anyhow::Error>> + Send + 'static,
        R: Send,
    {
        self.record_half_open_call().await;
        f().await
    }

    async fn check_circuit_state(&self) -> CircuitState {
        CircuitState::Closed
    }

    async fn record_success(&self) {}
    async fn record_failure(&self) {}
    async fn record_half_open_call(&self) {}
}

#[derive(Debug)]
pub enum CircuitState {
    Closed,
    #[allow(dead_code)]
    Open,
    #[allow(dead_code)]
    HalfOpen,
}

/// 元组收集优化示例
///
/// 展示如何使用Rust 1.92的元组FromIterator特性
pub struct TupleCollectionOptimizer;

impl TupleCollectionOptimizer {
    /// 优化前：分别收集到多个Vec
    #[allow(dead_code)]
    pub fn collect_separately(&self, data: Vec<Result<i32, String>>) -> (Vec<i32>, Vec<String>) {
        let mut successful = Vec::new();
        let mut failed = Vec::new();

        for result in data {
            match result {
                Ok(value) => successful.push(value),
                Err(error) => failed.push(error),
            }
        }

        (successful, failed)
    }

    /// 优化后：使用Rust 1.92的元组收集特性
    pub fn collect_to_tuple(&self, data: Vec<Result<i32, String>>) -> (Vec<i32>, Vec<String>) {
        let (ok_results, err_results): (Vec<_>, Vec<_>) = data.into_iter().partition(|r| r.is_ok());
        let successful: Vec<i32> = ok_results
            .into_iter()
            .map(|r| r.expect("Partition ensures Ok values"))
            .collect();
        let failed: Vec<String> = err_results.into_iter().map(|r| r.unwrap_err()).collect();
        (successful, failed)
    }

    /// 更高级的元组收集
    pub fn advanced_tuple_collection(
        &self,
        data: Vec<(String, i32, bool)>,
    ) -> (HashMap<String, i32>, Vec<bool>, Vec<String>) {
        let (names, values, flags): (Vec<_>, Vec<_>, Vec<_>) = data.into_iter().collect();

        let mut map = HashMap::new();
        for (name, value) in names.iter().zip(values.iter()) {
            map.insert(name.clone(), *value);
        }

        (map, flags, names)
    }
}

/// 零拷贝优化示例
///
/// 展示如何使用Cow类型减少不必要的克隆
pub struct ZeroCopyOptimizer;

impl ZeroCopyOptimizer {
    /// 优化前：总是克隆数据
    #[allow(dead_code)]
    pub fn process_with_clone(&self, data: &[u8]) -> Result<Vec<u8>> {
        let processed_data = data.to_vec();
        self.process_data_internal(processed_data)
    }

    /// 优化后：使用Cow类型
    pub fn process_with_cow(&self, data: Cow<'_, [u8]>) -> Result<Vec<u8>> {
        let data_vec = self.cow_to_vec(data);
        self.process_data_internal(data_vec)
    }

    fn cow_to_vec(&self, data: Cow<'_, [u8]>) -> Vec<u8> {
        match data {
            Cow::Borrowed(borrowed) => borrowed.to_vec(),
            Cow::Owned(owned) => owned,
        }
    }

    /// 更智能的零拷贝处理
    pub fn smart_process<'a>(&self, data: Cow<'a, [u8]>) -> Result<Cow<'a, [u8]>> {
        if !self.needs_processing(&data) {
            return Ok(data);
        }
        let processed = self.process_data_internal(data.into_owned())?;
        Ok(Cow::Owned(processed))
    }

    fn needs_processing(&self, _data: &[u8]) -> bool {
        true
    }

    fn process_data_internal(&self, data: Vec<u8>) -> Result<Vec<u8>> {
        Ok(data)
    }
}

/// 高性能对象池优化
///
/// 利用Rust 1.92的内存优化特性
pub struct OptimizedMemoryPool<T: Clone> {
    pool: Arc<Mutex<Vec<T>>>,
    factory: Arc<dyn Fn() -> T + Send + Sync>,
    #[allow(dead_code)]
    max_size: usize,
    stats: Arc<Mutex<PoolStats>>,
}

#[derive(Debug, Default)]
pub struct PoolStats {
    total_created: usize,
    total_reused: usize,
    total_dropped: usize,
}

impl<T: Send + Sync + Clone + 'static> OptimizedMemoryPool<T> {
    pub fn new<F>(factory: F, max_size: usize) -> Self
    where
        F: Fn() -> T + Send + Sync + 'static,
    {
        Self {
            pool: Arc::new(Mutex::new(Vec::with_capacity(max_size))),
            factory: Arc::new(factory),
            max_size,
            stats: Arc::new(Mutex::new(PoolStats::default())),
        }
    }

    pub async fn acquire(&self) -> PooledObject<T> {
        let mut pool = self.pool.lock().await;

        let obj = if let Some(obj) = pool.pop() {
            drop(pool);
            let mut stats = self.stats.lock().await;
            stats.total_reused += 1;
            obj
        } else {
            drop(pool);
            let mut stats = self.stats.lock().await;
            stats.total_created += 1;
            (self.factory)()
        };

        PooledObject::new(obj, Arc::clone(&self.pool), Arc::clone(&self.stats))
    }

    pub async fn get_stats(&self) -> PoolStats {
        let stats = self.stats.lock().await;
        PoolStats {
            total_created: stats.total_created,
            total_reused: stats.total_reused,
            total_dropped: stats.total_dropped,
        }
    }
}

pub struct PooledObject<T: Clone + Send + 'static> {
    object: Option<T>,
    pool: Arc<Mutex<Vec<T>>>,
    stats: Arc<Mutex<PoolStats>>,
    max_size: usize,
}

impl<T: Clone + Send + 'static> PooledObject<T> {
    fn new(object: T, pool: Arc<Mutex<Vec<T>>>, stats: Arc<Mutex<PoolStats>>) -> Self {
        Self {
            object: Some(object),
            pool,
            stats,
            max_size: 100,
        }
    }

    pub fn get(&self) -> &T {
        self.object
            .as_ref()
            .expect("PooledObject should always contain an object")
    }

    pub fn get_mut(&mut self) -> &mut T {
        self.object
            .as_mut()
            .expect("PooledObject should always contain an object")
    }
}

impl<T: Clone + Send + 'static> Drop for PooledObject<T> {
    fn drop(&mut self) {
        let Some(obj) = self.object.take() else {
            return;
        };
        let pool = self.pool.clone();
        let stats = self.stats.clone();
        let max_size = self.max_size;

        tokio::spawn(async move {
            let mut pool = pool.lock().await;
            if pool.len() < max_size {
                pool.push(obj);
            } else {
                let mut stats = stats.lock().await;
                stats.total_dropped += 1;
            }
        });
    }
}

/// 异步批处理优化
pub struct AsyncBatchProcessor {
    batch_size: usize,
    #[allow(dead_code)]
    timeout: std::time::Duration,
}

impl AsyncBatchProcessor {
    pub fn new(batch_size: usize, timeout: std::time::Duration) -> Self {
        Self {
            batch_size,
            timeout,
        }
    }

    pub async fn process_batch<T, F, Fut, R>(&self, items: Vec<T>, processor: F) -> Result<Vec<R>>
    where
        F: Fn(Vec<T>) -> Fut,
        Fut: Future<Output = Result<Vec<R>, anyhow::Error>> + Send,
        T: Send + Clone,
        R: Send,
    {
        let chunks: Vec<Vec<T>> = items
            .chunks(self.batch_size)
            .map(|chunk| chunk.to_vec())
            .collect();

        let (successful, failed): (Vec<_>, Vec<_>) =
            futures::future::join_all(chunks.into_iter().map(processor))
                .await
                .into_iter()
                .partition(|r| r.is_ok());

        if !failed.is_empty() {
            return Err(anyhow::anyhow!(
                "Batch processing failed: {} items failed",
                failed.len()
            ));
        }

        let results: Vec<R> = successful
            .into_iter()
            .flat_map(|r| r.expect("Successful results should be Ok"))
            .collect();

        Ok(results)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_async_closure_optimization() {
        let optimizer = AsyncClosureOptimizer;

        let result = optimizer
            .call_with_async_closure::<_, _, i32>(|| async { Ok::<i32, anyhow::Error>(42) })
            .await;

        assert!(result.is_ok());
        assert_eq!(result.expect("Async closure should succeed"), 42);
    }

    #[test]
    fn test_tuple_collection_optimization() {
        let optimizer = TupleCollectionOptimizer;
        let data = vec![
            Ok(1),
            Err("error1".to_string()),
            Ok(2),
            Err("error2".to_string()),
        ];

        let (successful, failed) = optimizer.collect_to_tuple(data);

        assert_eq!(successful, vec![1, 2]);
        assert_eq!(failed, vec!["error1", "error2"]);
    }

    #[test]
    fn test_zero_copy_optimization() {
        let optimizer = ZeroCopyOptimizer;
        let data = b"hello world";

        let result1 = optimizer.process_with_cow(Cow::Borrowed(data));
        assert!(result1.is_ok());

        let result2 = optimizer.process_with_cow(Cow::Owned(data.to_vec()));
        assert!(result2.is_ok());
    }

    #[tokio::test]
    async fn test_optimized_memory_pool() {
        let pool = OptimizedMemoryPool::new(|| String::with_capacity(1024), 10);

        let obj1 = pool.acquire().await;
        assert_eq!(obj1.get().capacity(), 1024);

        drop(obj1);
        tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;

        let obj2 = pool.acquire().await;
        assert_eq!(obj2.get().capacity(), 1024);

        let stats = pool.get_stats().await;
        assert_eq!(stats.total_created, 1);
    }

    #[tokio::test]
    async fn test_async_batch_processing() {
        let processor = AsyncBatchProcessor::new(2, std::time::Duration::from_millis(100));
        let items = vec![1, 2, 3, 4, 5];

        let results = processor
            .process_batch(items, |chunk| async move {
                Ok::<Vec<i32>, anyhow::Error>(chunk.into_iter().map(|x| x * 2).collect())
            })
            .await;

        let results_vec = results.expect("Async collect should succeed");
        assert_eq!(results_vec, vec![2, 4, 6, 8, 10]);
    }
}

/// SIMD优化处理器
pub struct SimdOptimizer {
    cache_line_size: usize,
    prefetch_distance: usize,
}

impl SimdOptimizer {
    pub fn new() -> Self {
        Self {
            cache_line_size: 64,
            prefetch_distance: 2,
        }
    }

    /// # Safety
    /// 调用者必须确保AVX2指令集可用且输入/输出切片长度相同
    #[target_feature(enable = "avx2")]
    pub unsafe fn process_data_simd(&self, data: &[f64], result: &mut [f64]) {
        let len = data.len();
        let simd_len = len - (len % 4);

        unsafe {
            self.process_simd_chunk(data, result, simd_len);
        }
        self.process_remaining(data, result, simd_len, len);
    }

    /// # Safety
    /// 调用者必须确保AVX2指令集可用
    unsafe fn process_simd_chunk(&self, data: &[f64], result: &mut [f64], simd_len: usize) {
        for i in (0..simd_len).step_by(4) {
            unsafe {
                let data_vec = _mm256_loadu_pd(data.as_ptr().add(i));
                let result_vec = _mm256_mul_pd(data_vec, data_vec);
                _mm256_storeu_pd(result.as_mut_ptr().add(i), result_vec);
            }
        }
    }

    fn process_remaining(&self, data: &[f64], result: &mut [f64], start: usize, end: usize) {
        for i in start..end {
            result[i] = data[i] * data[i];
        }
    }

    pub fn matrix_multiply_optimized(&self, a: &[f64], b: &[f64], c: &mut [f64], n: usize) {
        const BLOCK_SIZE: usize = 64;

        for ii in (0..n).step_by(BLOCK_SIZE) {
            for jj in (0..n).step_by(BLOCK_SIZE) {
                self.process_block_column(a, b, c, n, ii, jj, BLOCK_SIZE);
            }
        }
    }

    fn process_block_column(
        &self,
        a: &[f64],
        b: &[f64],
        c: &mut [f64],
        n: usize,
        ii: usize,
        jj: usize,
        block_size: usize,
    ) {
        for kk in (0..n).step_by(block_size) {
            self.process_block(a, b, c, n, ii, jj, kk, block_size);
        }
    }

    fn process_block(
        &self,
        a: &[f64],
        b: &[f64],
        c: &mut [f64],
        n: usize,
        ii: usize,
        jj: usize,
        kk: usize,
        block_size: usize,
    ) {
        let i_end = (ii + block_size).min(n);
        let k_end = (kk + block_size).min(n);

        for i in ii..i_end {
            self.compute_row(a, b, c, n, i, jj, k_end);
        }
    }

    fn compute_row(
        &self,
        a: &[f64],
        b: &[f64],
        c: &mut [f64],
        n: usize,
        i: usize,
        jj: usize,
        k_end: usize,
    ) {
        for j in jj..k_end {
            let mut sum = 0.0;
            for k in jj..k_end {
                sum += a[i * n + k] * b[k * n + j];
            }
            c[i * n + j] += sum;
        }
    }

    pub fn prefetch_data(&self, data: &[u8]) {
        let len = data.len();
        let prefetch_step = self.cache_line_size * self.prefetch_distance;

        for i in (0..len).step_by(prefetch_step) {
            if i + self.cache_line_size < len {
                unsafe {
                    ptr::read_volatile(&data[i]);
                }
            }
        }
    }

    pub fn process_strings_zero_copy<'a>(&self, strings: &[&'a str]) -> Vec<Cow<'a, str>> {
        strings
            .iter()
            .map(|&s| self.process_single_string(s))
            .collect()
    }

    fn process_single_string<'a>(&self, s: &'a str) -> Cow<'a, str> {
        if s.len() > 100 {
            Cow::Owned(s.to_uppercase())
        } else {
            Cow::Borrowed(s)
        }
    }
}

impl Default for SimdOptimizer {
    fn default() -> Self {
        Self::new()
    }
}

/// 缓存优化管理器
#[allow(dead_code)]
pub struct CacheOptimizer {
    l1_cache_size: usize,
    l2_cache_size: usize,
    l3_cache_size: usize,
    cache_alignment: usize,
}

impl CacheOptimizer {
    pub fn new() -> Self {
        Self {
            l1_cache_size: 32 * 1024,
            l2_cache_size: 256 * 1024,
            l3_cache_size: 8 * 1024 * 1024,
            cache_alignment: 64,
        }
    }

    #[allow(dead_code)]
    pub fn allocate_aligned(&self, size: usize) -> Result<*mut u8> {
        let aligned_size = (size + self.cache_alignment - 1) & !(self.cache_alignment - 1);
        self.alloc_aligned_memory(aligned_size)
    }

    fn alloc_aligned_memory(&self, aligned_size: usize) -> Result<*mut u8> {
        unsafe {
            let layout = std::alloc::Layout::from_size_align(aligned_size, self.cache_alignment)
                .expect("Cache alignment must be a power of two");
            let ptr = std::alloc::alloc(layout);
            if ptr.is_null() {
                return Err(anyhow::anyhow!("内存分配失败"));
            }
            Ok(ptr)
        }
    }

    #[allow(dead_code)]
    pub fn optimize_data_layout<T>(&self, data: &mut [T]) {
        let ptr = data.as_mut_ptr() as usize;
        if !ptr.is_multiple_of(self.cache_alignment) {
            // 如果不对齐，需要重新分配
        }
    }

    #[allow(dead_code)]
    pub fn warm_cache(&self, data: &[u8]) {
        let len = data.len();
        let step = self.cache_alignment;

        for i in (0..len).step_by(step) {
            unsafe {
                ptr::read_volatile(&data[i]);
            }
        }
    }

    #[allow(dead_code)]
    pub fn analyze_cache_performance(&self, data: &[u8]) -> CachePerformanceMetrics {
        let sequential_time = self.measure_sequential_access(data);
        let random_time = self.measure_random_access(data);

        CachePerformanceMetrics {
            sequential_access_time: sequential_time,
            random_access_time: random_time,
            cache_hit_ratio: self.calculate_hit_ratio(sequential_time, random_time),
            data_size: data.len(),
        }
    }

    fn measure_sequential_access(&self, data: &[u8]) -> std::time::Duration {
        let start = std::time::Instant::now();
        let mut _sum = 0u64;
        for &byte in data {
            _sum += byte as u64;
        }
        start.elapsed()
    }

    fn measure_random_access(&self, data: &[u8]) -> std::time::Duration {
        let start = std::time::Instant::now();
        let mut _sum = 0u64;
        for i in 0..data.len() {
            let idx = (i * 7) % data.len();
            _sum += data[idx] as u64;
        }
        start.elapsed()
    }

    fn calculate_hit_ratio(
        &self,
        sequential_time: std::time::Duration,
        random_time: std::time::Duration,
    ) -> f64 {
        if random_time > sequential_time {
            sequential_time.as_nanos() as f64 / random_time.as_nanos() as f64
        } else {
            1.0
        }
    }
}

impl Default for CacheOptimizer {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone)]
pub struct CachePerformanceMetrics {
    pub sequential_access_time: std::time::Duration,
    pub random_access_time: std::time::Duration,
    pub cache_hit_ratio: f64,
    pub data_size: usize,
}

/// 内存池优化器
#[allow(dead_code)]
pub struct MemoryPoolOptimizer {
    pools: HashMap<usize, Vec<*mut u8>>,
    max_pool_size: usize,
}

impl MemoryPoolOptimizer {
    pub fn new() -> Self {
        Self {
            pools: HashMap::new(),
            max_pool_size: 1000,
        }
    }

    #[allow(dead_code)]
    pub fn get_memory(&mut self, size: usize) -> Option<*mut u8> {
        self.pools.get_mut(&size).and_then(|pool| pool.pop())
    }

    pub fn return_memory(&mut self, size: usize, ptr: *mut u8) {
        if self.should_deallocate(size) {
            Self::deallocate_memory(ptr);
            return;
        }
        self.insert_into_pool(size, ptr);
    }

    fn should_deallocate(&self, size: usize) -> bool {
        match self.pools.get(&size) {
            Some(pool) => pool.len() >= self.max_pool_size,
            None => false,
        }
    }

    fn insert_into_pool(&mut self, size: usize, ptr: *mut u8) {
        self.pools.entry(size).or_default().push(ptr);
    }

    fn deallocate_memory(ptr: *mut u8) {
        unsafe {
            let layout = std::alloc::Layout::from_size_align(1024, 64)
                .expect("Memory alignment must be valid");
            std::alloc::dealloc(ptr, layout);
        }
    }

    pub fn cleanup(&mut self) {
        for pool in self.pools.values_mut() {
            Self::deallocate_pool(pool);
        }
    }

    fn deallocate_pool(pool: &mut Vec<*mut u8>) {
        for &ptr in pool.iter() {
            Self::deallocate_memory(ptr);
        }
        pool.clear();
    }
}

impl Default for MemoryPoolOptimizer {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for MemoryPoolOptimizer {
    fn drop(&mut self) {
        self.cleanup();
    }
}

/// 性能基准测试
pub struct PerformanceBenchmark {
    simd_optimizer: SimdOptimizer,
    cache_optimizer: CacheOptimizer,
    memory_pool: MemoryPoolOptimizer,
}

impl PerformanceBenchmark {
    pub fn new() -> Self {
        Self {
            simd_optimizer: SimdOptimizer::new(),
            cache_optimizer: CacheOptimizer::new(),
            memory_pool: MemoryPoolOptimizer::new(),
        }
    }

    pub async fn run_comprehensive_benchmark(&mut self) -> BenchmarkResults {
        let mut results = BenchmarkResults::new();

        self.run_simd_benchmark(&mut results);
        self.run_cache_benchmark(&mut results);
        self.run_memory_pool_benchmark(&mut results);

        results
    }

    fn run_simd_benchmark(&mut self, results: &mut BenchmarkResults) {
        let data = vec![1.0f64; 1000000];
        let mut result = vec![0.0f64; 1000000];

        let start = std::time::Instant::now();
        unsafe {
            self.simd_optimizer.process_data_simd(&data, &mut result);
        }
        results.simd_processing_time = start.elapsed();
    }

    fn run_cache_benchmark(&mut self, results: &mut BenchmarkResults) {
        let test_data = vec![0u8; 1024 * 1024];
        results.cache_metrics = self.cache_optimizer.analyze_cache_performance(&test_data);
    }

    fn run_memory_pool_benchmark(&mut self, results: &mut BenchmarkResults) {
        let start = std::time::Instant::now();
        for _ in 0..1000 {
            if let Some(ptr) = self.memory_pool.get_memory(1024) {
                self.memory_pool.return_memory(1024, ptr);
            }
        }
        results.memory_pool_time = start.elapsed();
    }
}

impl Default for PerformanceBenchmark {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone)]
pub struct BenchmarkResults {
    pub simd_processing_time: std::time::Duration,
    pub cache_metrics: CachePerformanceMetrics,
    pub memory_pool_time: std::time::Duration,
}

impl BenchmarkResults {
    pub fn new() -> Self {
        Self {
            simd_processing_time: std::time::Duration::ZERO,
            cache_metrics: CachePerformanceMetrics {
                sequential_access_time: std::time::Duration::ZERO,
                random_access_time: std::time::Duration::ZERO,
                cache_hit_ratio: 0.0,
                data_size: 0,
            },
            memory_pool_time: std::time::Duration::ZERO,
        }
    }
}

impl Default for BenchmarkResults {
    fn default() -> Self {
        Self::new()
    }
}
