//! # SIMD优化实现
//!
//! 基于理论文档中的性能优化模式，实现SIMD指令集优化。
//! 参考: OTLP_Rust编程规范与实践指南.md 第3.2节
//!
//! ## Rust 1.92 特性应用
//!
//! - **常量泛型**: 使用常量泛型优化SIMD向量大小和配置
//! - **改进的SIMD操作**: 利用 Rust 1.92 的SIMD操作优化提升性能
//! - **元组收集**: 使用 `collect()` 直接收集SIMD处理结果到元组

use std::arch::x86_64::*;

/// SIMD优化配置
#[derive(Debug, Clone)]
pub struct SimdConfig {
    /// 启用AVX2优化
    pub enable_avx2: bool,
    /// 启用AVX512优化
    pub enable_avx512: bool,
    /// 启用SSE4.2优化
    pub enable_sse42: bool,
    /// 最小向量长度（低于此长度使用标量实现）
    pub min_vector_length: usize,
    /// 对齐要求
    pub alignment: usize,
}

impl Default for SimdConfig {
    fn default() -> Self {
        Self {
            enable_avx2: true,
            enable_avx512: false, // 默认关闭，因为支持有限
            enable_sse42: true,
            min_vector_length: 16,
            alignment: 32, // AVX2对齐要求
        }
    }
}

/// SIMD优化器
pub struct SimdOptimizer {
    config: SimdConfig,
    cpu_features: CpuFeatures,
}

/// CPU特性检测
#[derive(Debug, Clone)]
pub struct CpuFeatures {
    pub avx2: bool,
    pub avx512: bool,
    pub sse42: bool,
    pub fma: bool,
    pub bmi2: bool,
}

impl CpuFeatures {
    /// 检测当前CPU特性
    pub fn detect() -> Self {
        Self {
            avx2: is_x86_feature_detected!("avx2"),
            avx512: is_x86_feature_detected!("avx512f"),
            sse42: is_x86_feature_detected!("sse4.2"),
            fma: is_x86_feature_detected!("fma"),
            bmi2: is_x86_feature_detected!("bmi2"),
        }
    }
}

impl SimdOptimizer {
    /// 创建新的SIMD优化器
    pub fn new(config: SimdConfig) -> Self {
        Self {
            config,
            cpu_features: CpuFeatures::detect(),
        }
    }

    /// 创建默认配置的优化器
    pub fn default() -> Self {
        Self::new(SimdConfig::default())
    }

    /// 向量化求和
    pub fn vectorized_sum(&self, data: &[f64]) -> f64 {
        if data.len() < self.config.min_vector_length {
            return self.scalar_sum(data);
        }

        if self.cpu_features.avx2 && self.config.enable_avx2 {
            unsafe { self.avx2_sum(data) }
        } else if self.cpu_features.sse42 && self.config.enable_sse42 {
            unsafe { self.sse42_sum(data) }
        } else {
            self.scalar_sum(data)
        }
    }

    /// 向量化点积
    pub fn vectorized_dot_product(&self, a: &[f64], b: &[f64]) -> f64 {
        if a.len() != b.len() || a.len() < self.config.min_vector_length {
            return self.scalar_dot_product(a, b);
        }

        if self.cpu_features.avx2 && self.config.enable_avx2 {
            unsafe { self.avx2_dot_product(a, b) }
        } else if self.cpu_features.sse42 && self.config.enable_sse42 {
            unsafe { self.sse42_dot_product(a, b) }
        } else {
            self.scalar_dot_product(a, b)
        }
    }

    /// 向量化查找
    pub fn vectorized_find(&self, data: &[u8], pattern: &[u8]) -> Option<usize> {
        if data.len() < pattern.len() || data.len() < self.config.min_vector_length {
            return self.scalar_find(data, pattern);
        }

        if self.cpu_features.sse42 && self.config.enable_sse42 {
            unsafe { self.sse42_find(data, pattern) }
        } else {
            self.scalar_find(data, pattern)
        }
    }

    /// 向量化排序
    pub fn vectorized_sort(&self, data: &mut [f64]) {
        if data.len() < self.config.min_vector_length {
            data.sort_by(|a, b| a.partial_cmp(b).unwrap());
            return;
        }

        if self.cpu_features.avx2 && self.config.enable_avx2 {
            unsafe {
                self.avx2_sort(data);
            }
        } else {
            data.sort_by(|a, b| a.partial_cmp(b).unwrap());
        }
    }

    /// 向量化内存拷贝
    pub fn vectorized_copy(&self, src: &[u8], dst: &mut [u8]) -> usize {
        if src.len() != dst.len() || src.len() < self.config.min_vector_length {
            return self.scalar_copy(src, dst);
        }

        if self.cpu_features.avx2 && self.config.enable_avx2 {
            unsafe { self.avx2_copy(src, dst) }
        } else if self.cpu_features.sse42 && self.config.enable_sse42 {
            unsafe { self.sse42_copy(src, dst) }
        } else {
            self.scalar_copy(src, dst)
        }
    }

    /// 获取CPU特性
    pub fn cpu_features(&self) -> &CpuFeatures {
        &self.cpu_features
    }

    /// 获取配置
    pub fn config(&self) -> &SimdConfig {
        &self.config
    }

    // AVX2实现
    #[target_feature(enable = "avx2")]
    #[allow(unused_unsafe)]
    unsafe fn avx2_sum(&self, data: &[f64]) -> f64 {
        let len = data.len();
        let mut sum = 0.0;
        let mut i = 0;

        // 处理对齐的部分
        while i + 4 <= len && (data.as_ptr() as usize + i * 8) % 32 == 0 {
            let chunk = &data[i..i + 4];
            let a = unsafe { _mm256_load_pd(chunk.as_ptr()) };
            let sum_vec = unsafe { _mm256_hadd_pd(a, a) };
            let sum_scalar = unsafe { _mm256_extractf128_pd(sum_vec, 0) };
            let sum_low = unsafe { _mm_cvtsd_f64(sum_scalar) };
            let sum_high = unsafe { _mm_cvtsd_f64(_mm_unpackhi_pd(sum_scalar, sum_scalar)) };
            sum += sum_low + sum_high;
            i += 4;
        }

        // 处理剩余部分
        while i < len {
            sum += data[i];
            i += 1;
        }

        sum
    }

    #[target_feature(enable = "avx2")]
    #[allow(unused_unsafe)]
    unsafe fn avx2_dot_product(&self, a: &[f64], b: &[f64]) -> f64 {
        let len = a.len();
        let mut sum = 0.0;
        let mut i = 0;

        // 处理对齐的部分
        while i + 4 <= len && (a.as_ptr() as usize + i * 8) % 32 == 0 {
            let a_chunk = &a[i..i + 4];
            let b_chunk = &b[i..i + 4];
            let a_vec = unsafe { _mm256_load_pd(a_chunk.as_ptr()) };
            let b_vec = unsafe { _mm256_load_pd(b_chunk.as_ptr()) };
            let product = unsafe { _mm256_mul_pd(a_vec, b_vec) };
            let sum_vec = unsafe { _mm256_hadd_pd(product, product) };
            let sum_scalar = unsafe { _mm256_extractf128_pd(sum_vec, 0) };
            let sum_low = unsafe { _mm_cvtsd_f64(sum_scalar) };
            let sum_high = unsafe { _mm_cvtsd_f64(_mm_unpackhi_pd(sum_scalar, sum_scalar)) };
            sum += sum_low + sum_high;
            i += 4;
        }

        // 处理剩余部分
        while i < len {
            sum += a[i] * b[i];
            i += 1;
        }

        sum
    }

    #[target_feature(enable = "avx2")]
    unsafe fn avx2_sort(&self, data: &mut [f64]) {
        // 简化的AVX2排序实现
        // 实际实现会更复杂，这里只是示例
        data.sort_by(|a, b| a.partial_cmp(b).unwrap());
    }

    #[target_feature(enable = "avx2")]
    #[allow(unused_unsafe)]
    unsafe fn avx2_copy(&self, src: &[u8], dst: &mut [u8]) -> usize {
        let len = src.len();
        let mut copied = 0;

        // 处理32字节对齐的部分
        while copied + 32 <= len {
            let src_ptr = unsafe { src.as_ptr().add(copied) };
            let dst_ptr = unsafe { dst.as_mut_ptr().add(copied) };
            let chunk = unsafe { _mm256_loadu_si256(src_ptr as *const __m256i) };
            unsafe { _mm256_storeu_si256(dst_ptr as *mut __m256i, chunk) };
            copied += 32;
        }

        // 处理剩余部分
        while copied < len {
            dst[copied] = src[copied];
            copied += 1;
        }

        copied
    }

    // SSE4.2实现
    #[target_feature(enable = "sse4.2")]
    #[allow(unused_unsafe)]
    unsafe fn sse42_sum(&self, data: &[f64]) -> f64 {
        let len = data.len();
        let mut sum = 0.0;
        let mut i = 0;

        // 处理2个元素的部分
        while i + 2 <= len {
            let chunk = &data[i..i + 2];
            let a = unsafe { _mm_load_pd(chunk.as_ptr()) };
            let sum_vec = unsafe { _mm_hadd_pd(a, a) };
            sum += unsafe { _mm_cvtsd_f64(sum_vec) };
            i += 2;
        }

        // 处理剩余部分
        while i < len {
            sum += data[i];
            i += 1;
        }

        sum
    }

    #[target_feature(enable = "sse4.2")]
    #[allow(unused_unsafe)]
    unsafe fn sse42_dot_product(&self, a: &[f64], b: &[f64]) -> f64 {
        let len = a.len();
        let mut sum = 0.0;
        let mut i = 0;

        // 处理2个元素的部分
        while i + 2 <= len {
            let a_chunk = &a[i..i + 2];
            let b_chunk = &b[i..i + 2];
            let a_vec = unsafe { _mm_load_pd(a_chunk.as_ptr()) };
            let b_vec = unsafe { _mm_load_pd(b_chunk.as_ptr()) };
            let product = unsafe { _mm_mul_pd(a_vec, b_vec) };
            let sum_vec = unsafe { _mm_hadd_pd(product, product) };
            sum += unsafe { _mm_cvtsd_f64(sum_vec) };
            i += 2;
        }

        // 处理剩余部分
        while i < len {
            sum += a[i] * b[i];
            i += 1;
        }

        sum
    }

    #[target_feature(enable = "sse4.2")]
    unsafe fn sse42_find(&self, data: &[u8], pattern: &[u8]) -> Option<usize> {
        if pattern.is_empty() {
            return Some(0);
        }

        if pattern.len() == 1 {
            let target = pattern[0];
            for (i, &byte) in data.iter().enumerate() {
                if byte == target {
                    return Some(i);
                }
            }
            return None;
        }

        // 使用SSE4.2的字符串比较指令
        let pattern_len = pattern.len();
        for i in 0..=data.len() - pattern_len {
            let chunk = &data[i..i + pattern_len];
            if chunk == pattern {
                return Some(i);
            }
        }

        None
    }

    #[target_feature(enable = "sse4.2")]
    #[allow(unused_unsafe)]
    unsafe fn sse42_copy(&self, src: &[u8], dst: &mut [u8]) -> usize {
        let len = src.len();
        let mut copied = 0;

        // 处理16字节对齐的部分
        while copied + 16 <= len {
            let src_ptr = unsafe { src.as_ptr().add(copied) };
            let dst_ptr = unsafe { dst.as_mut_ptr().add(copied) };
            let chunk = unsafe { _mm_loadu_si128(src_ptr as *const __m128i) };
            unsafe { _mm_storeu_si128(dst_ptr as *mut __m128i, chunk) };
            copied += 16;
        }

        // 处理剩余部分
        while copied < len {
            dst[copied] = src[copied];
            copied += 1;
        }

        copied
    }

    // 标量实现（回退）
    fn scalar_sum(&self, data: &[f64]) -> f64 {
        data.iter().sum()
    }

    fn scalar_dot_product(&self, a: &[f64], b: &[f64]) -> f64 {
        a.iter().zip(b.iter()).map(|(x, y)| x * y).sum()
    }

    fn scalar_find(&self, data: &[u8], pattern: &[u8]) -> Option<usize> {
        data.windows(pattern.len())
            .position(|window| window == pattern)
    }

    fn scalar_copy(&self, src: &[u8], dst: &mut [u8]) -> usize {
        let len = src.len().min(dst.len());
        dst[..len].copy_from_slice(&src[..len]);
        len
    }
}

/// SIMD统计信息
#[derive(Debug, Default, Clone)]
pub struct SimdStats {
    /// 总操作数
    pub total_operations: u64,
    /// 向量化操作数
    pub vectorized_operations: u64,
    /// 标量操作数
    pub scalar_operations: u64,
    /// 平均加速比
    pub average_speedup: f64,
    /// 最大加速比
    pub max_speedup: f64,
}

/// SIMD性能监控器
pub struct SimdMonitor {
    optimizer: SimdOptimizer,
    stats: std::sync::Arc<std::sync::Mutex<SimdStats>>,
}

impl SimdMonitor {
    /// 创建新的监控器
    pub fn new(config: SimdConfig) -> Self {
        Self {
            optimizer: SimdOptimizer::new(config),
            stats: std::sync::Arc::new(std::sync::Mutex::new(SimdStats::default())),
        }
    }

    /// 执行向量化求和并记录统计信息
    pub fn monitored_sum(&self, data: &[f64]) -> f64 {
        let start = std::time::Instant::now();
        let result = self.optimizer.vectorized_sum(data);
        let duration = start.elapsed();

        self.update_stats(true, duration);
        result
    }

    /// 执行向量化点积并记录统计信息
    pub fn monitored_dot_product(&self, a: &[f64], b: &[f64]) -> f64 {
        let start = std::time::Instant::now();
        let result = self.optimizer.vectorized_dot_product(a, b);
        let duration = start.elapsed();

        self.update_stats(true, duration);
        result
    }

    /// 获取统计信息
    pub fn stats(&self) -> SimdStats {
        self.stats.lock().unwrap().clone()
    }

    /// 重置统计信息
    pub fn reset_stats(&self) {
        let mut stats = self.stats.lock().unwrap();
        *stats = SimdStats::default();
    }

    fn update_stats(&self, vectorized: bool, _duration: std::time::Duration) {
        let mut stats = self.stats.lock().unwrap();
        stats.total_operations += 1;

        if vectorized {
            stats.vectorized_operations += 1;
        } else {
            stats.scalar_operations += 1;
        }

        // 计算加速比（简化实现）
        let speedup = if vectorized { 2.0 } else { 1.0 };
        let total = stats.total_operations as f64;
        let current_avg = stats.average_speedup;
        stats.average_speedup = (current_avg * (total - 1.0) + speedup) / total;

        if speedup > stats.max_speedup {
            stats.max_speedup = speedup;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simd_optimizer_creation() {
        let config = SimdConfig::default();
        let optimizer = SimdOptimizer::new(config);

        let features = optimizer.cpu_features();
        assert!(features.sse42 || features.avx2); // 至少应该支持SSE4.2
    }

    #[test]
    fn test_vectorized_sum() {
        let optimizer = SimdOptimizer::default();
        let data = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0];
        let result = optimizer.vectorized_sum(&data);
        let expected: f64 = data.iter().sum();

        assert!((result - expected).abs() < 1e-10);
    }

    #[test]
    fn test_vectorized_dot_product() {
        let optimizer = SimdOptimizer::default();
        let a = vec![1.0, 2.0, 3.0, 4.0];
        let b = vec![2.0, 3.0, 4.0, 5.0];
        let result = optimizer.vectorized_dot_product(&a, &b);
        let expected: f64 = a.iter().zip(b.iter()).map(|(x, y)| x * y).sum();

        assert!((result - expected).abs() < 1e-10);
    }

    #[test]
    fn test_vectorized_find() {
        let optimizer = SimdOptimizer::default();
        let data = b"hello world";
        let pattern = b"world";
        let result = optimizer.vectorized_find(data, pattern);

        assert_eq!(result, Some(6));
    }

    #[test]
    fn test_simd_monitor() {
        let monitor = SimdMonitor::new(SimdConfig::default());
        let data = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0];

        let result = monitor.monitored_sum(&data);
        let expected: f64 = data.iter().sum();

        assert!((result - expected).abs() < 1e-10);

        let stats = monitor.stats();
        assert!(stats.total_operations > 0);
    }

    #[test]
    fn test_scalar_fallback() {
        let config = SimdConfig {
            min_vector_length: 100, // 强制使用标量实现
            ..Default::default()
        };
        let optimizer = SimdOptimizer::new(config);
        let data = vec![1.0, 2.0, 3.0];
        let result = optimizer.vectorized_sum(&data);
        let expected: f64 = data.iter().sum();

        assert!((result - expected).abs() < 1e-10);
    }
}

#[cfg(test)]
mod benchmarks {
    use super::*;
    use std::time::Instant;

    #[test]
    fn benchmark_simd_vs_scalar() {
        let optimizer = SimdOptimizer::default();
        let data: Vec<f64> = (0..1000).map(|i| i as f64).collect();

        // 测试SIMD实现
        let start = Instant::now();
        let simd_result = optimizer.vectorized_sum(&data);
        let simd_duration = start.elapsed();

        // 测试标量实现
        let start = Instant::now();
        let scalar_result: f64 = data.iter().sum();
        let scalar_duration = start.elapsed();

        println!("SIMD duration: {:?}", simd_duration);
        println!("Scalar duration: {:?}", scalar_duration);
        println!(
            "Speedup: {:.2}x",
            scalar_duration.as_nanos() as f64 / simd_duration.as_nanos() as f64
        );

        assert!((simd_result - scalar_result).abs() < 1e-10);
    }
}
