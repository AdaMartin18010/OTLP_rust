//! # Rust 1.94 特性应用示例
//!
//! 本模块展示 Rust 1.94 新特性的实际应用

use std::sync::LazyLock;

/// 全局配置 - 使用 LazyLock 延迟初始化
pub static GLOBAL_CONFIG: LazyLock<ClientConfig> = LazyLock::new(|| {
    tracing::info!("Initializing global config with LazyLock (Rust 1.94)");
    ClientConfig::default()
});

/// 导出器注册表 - 使用 LazyLock
pub static EXPORTER_REGISTRY: LazyLock<ExporterRegistry> = LazyLock::new(|| {
    ExporterRegistry::new()
});

/// 客户端配置
#[derive(Debug, Clone)]
pub struct ClientConfig {
    pub endpoint: String,
    pub timeout: std::time::Duration,
    pub compression: CompressionType,
}

impl Default for ClientConfig {
    fn default() -> Self {
        Self {
            endpoint: "http://localhost:4317".to_string(),
            timeout: std::time::Duration::from_secs(30),
            compression: CompressionType::Gzip,
        }
    }
}

/// 压缩类型
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum CompressionType {
    None,
    Gzip,
    Zstd,
}

/// 导出器注册表
#[derive(Debug)]
pub struct ExporterRegistry {
    exporters: std::collections::HashMap<String, Box<dyn SpanExporter>>,
}

impl ExporterRegistry {
    fn new() -> Self {
        Self {
            exporters: std::collections::HashMap::new(),
        }
    }

    /// 注册导出器
    pub fn register(&mut self, name: &str, exporter: Box<dyn SpanExporter>) {
        self.exporters.insert(name.to_string(), exporter);
    }

    /// 获取导出器
    pub fn get(&self, name: &str) -> Option<&Box<dyn SpanExporter>> {
        self.exporters.get(name)
    }
}

/// Span 导出器 trait
pub trait SpanExporter: Send + Sync + std::fmt::Debug {
    fn export(&self, spans: &[SpanData]);
}

/// Span 数据
#[derive(Debug, Clone)]
pub struct SpanData {
    pub name: String,
    pub trace_id: u64,
    pub span_id: u64,
}

/// 使用 Rust 1.94 数学常量
pub mod math_consts {
    use std::f64::consts::{EULER_GAMMA, GOLDEN_RATIO};

    /// 计算调整后的采样率
    /// 使用欧拉-马斯刻若尼常数作为调整因子
    pub fn adjusted_sampling_rate(base_rate: f64) -> f64 {
        // EULER_GAMMA ≈ 0.5772156649015329
        let adjusted = base_rate * (1.0 + EULER_GAMMA * 0.1);
        adjusted.min(1.0).max(0.0)
    }

    /// 使用黄金比例计算斐波那契式退避
    /// GOLDEN_RATIO ≈ 1.618033988749895
    pub fn golden_backoff(attempt: u32, base_delay_ms: u64) -> u64 {
        let phi = GOLDEN_RATIO;
        let delay = base_delay_ms as f64 * phi.powi(attempt as i32);
        delay.min(u64::MAX as f64) as u64
    }
}

/// 使用 Rust 1.94 array_windows 的算法
pub mod array_window_algorithms {
    /// 计算序列差分
    /// 使用 Rust 1.94 array_windows 优化
    pub fn differences(data: &[f64]) -> Vec<f64> {
        if data.len() <= 1 {
            return Vec::new();
        }

        // Rust 1.94: array_windows 提供编译时确定的窗口大小
        data.array_windows()
            .map(|[prev, curr]| curr - prev)
            .collect()
    }

    /// 检测序列中的突变点
    /// 使用 array_windows 进行滑动窗口分析
    pub fn detect_anomalies(data: &[f64], threshold: f64) -> Vec<usize> {
        data.array_windows()
            .enumerate()
            .filter(|(_, [a, b])| (b - a).abs() > threshold)
            .map(|(idx, _)| idx)
            .collect()
    }

    /// 计算移动平均
    pub fn moving_average<const N: usize>(data: &[f64]) -> Vec<f64> {
        if data.len() < N {
            return Vec::new();
        }

        data.array_windows::<N>()
            .map(|window| window.iter().sum::<f64>() / N as f64)
            .collect()
    }

    /// 验证序列单调性
    pub fn is_monotonic_increasing(data: &[f64]) -> bool {
        data.array_windows().all(|[a, b]| a <= b)
    }

    /// 验证序列单调递减
    pub fn is_monotonic_decreasing(data: &[f64]) -> bool {
        data.array_windows().all(|[a, b]| a >= b)
    }
}

/// 使用 element_offset 的内存优化
pub mod memory_optimizations {
    /// 计算数组元素偏移量
    /// Rust 1.94: `[T]::element_offset` 稳定
    /// 返回 Some(index) 如果元素在数组中，否则返回 None
    pub fn calculate_offset<T>(arr: &[T], element: &T) -> Option<usize> {
        // element_offset 返回 Option<usize>
        arr.element_offset(element)
    }

    /// 批量处理时使用偏移量优化
    pub fn batch_process_with_offsets(data: &[u8], chunk_size: usize) -> Vec<Vec<u8>> {
        data.chunks(chunk_size)
            .enumerate()
            .map(|(idx, chunk)| {
                let offset = idx * chunk_size;
                tracing::debug!("Processing chunk at offset {}", offset);
                chunk.to_vec()
            })
            .collect()
    }
}

/// 使用 Peekable::next_if_map 的解析器
pub mod parser_utilities {
    /// 条件解析工具
    pub struct ConditionalParser<I: Iterator> {
        inner: std::iter::Peekable<I>,
    }

    impl<I: Iterator> ConditionalParser<I> {
        pub fn new(iter: I) -> Self {
            Self {
                inner: iter.peekable(),
            }
        }

        /// Rust 1.94: 使用 next_if_map 进行条件解析
        /// next_if_map 接受 FnOnce(I::Item) -> Result<R, I::Item>
        /// 成功时返回 Some(R)，失败时元素被放回
        pub fn parse_if<F, R>(&mut self, f: F) -> Option<R>
        where
            F: FnOnce(I::Item) -> Result<R, I::Item>,
        {
            self.inner.next_if_map(f)
        }

        /// 使用 peek 和 next_if 的组合
        pub fn parse_if_ref<F, R>(&mut self, f: F) -> Option<R>
        where
            F: FnOnce(&I::Item) -> Option<R>,
            I::Item: Clone,
        {
            // 先 peek，如果匹配则 next 并转换
            if let Some(item) = self.inner.peek() {
                let result = f(item);
                if result.is_some() {
                    self.inner.next();
                }
                result
            } else {
                None
            }
        }
    }
}

/// AVX-512 FP16 支持检测 (Rust 1.94)
#[cfg(all(target_arch = "x86_64", target_feature = "avx512fp16"))]
pub mod avx512_fp16 {
    use std::arch::x86_64::*;

    /// 检测 AVX-512 FP16 支持
    pub fn is_supported() -> bool {
        is_x86_feature_detected!("avx512fp16")
    }

    /// FP16 向量加法示例
    /// 注意: 需要实际 fp16 数据类型支持
    pub unsafe fn fp16_add(a: __m256h, b: __m256h) -> __m256h {
        _mm256_add_ph(a, b)
    }
}

/// AArch64 NEON FP16 支持
#[cfg(all(target_arch = "aarch64", target_feature = "fp16"))]
pub mod neon_fp16 {
    use std::arch::aarch64::*;

    /// 检测 NEON FP16 支持
    pub fn is_supported() -> bool {
        // 在实际硬件上检测
        cfg!(target_feature = "fp16")
    }

    /// FP16 向量操作示例
    pub unsafe fn fp16_mul(a: float16x8_t, b: float16x8_t) -> float16x8_t {
        vmulq_f16(a, b)
    }
}

/// 使用 const mul_add 的数学计算
pub mod const_math {
    /// 在 const 上下文中使用 mul_add (Rust 1.94)
    pub const fn linear_combination(a: f64, x: f64, b: f64, y: f64) -> f64 {
        // mul_add 在 const 上下文稳定
        a.mul_add(x, b * y)
    }

    /// 计算多项式 (const 上下文)
    pub const fn polynomial_2(a: f64, x: f64, b: f64, x2: f64, c: f64) -> f64 {
        a.mul_add(x, b.mul_add(x2, c))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_array_windows_differences() {
        let data = [1.0, 3.0, 6.0, 10.0];
        let diffs = array_window_algorithms::differences(&data);
        assert_eq!(diffs, vec![2.0, 3.0, 4.0]);
    }

    #[test]
    fn test_array_windows_anomalies() {
        let data = [1.0, 2.0, 10.0, 4.0, 5.0];
        let anomalies = array_window_algorithms::detect_anomalies(&data, 5.0);
        // 两个异常点: 2.0->10.0 (索引1) 和 10.0->4.0 (索引2)
        assert_eq!(anomalies, vec![1, 2]);
    }

    #[test]
    fn test_moving_average() {
        let data = [1.0, 2.0, 3.0, 4.0, 5.0];
        let avg = array_window_algorithms::moving_average::<3>(&data);
        assert_eq!(avg, vec![2.0, 3.0, 4.0]);
    }

    #[test]
    fn test_monotonic() {
        assert!(array_window_algorithms::is_monotonic_increasing(&[1.0, 2.0, 3.0]));
        assert!(!array_window_algorithms::is_monotonic_increasing(&[1.0, 3.0, 2.0]));
    }

    #[test]
    fn test_euler_gamma() {
        let rate = math_consts::adjusted_sampling_rate(0.5);
        assert!(rate > 0.5 && rate < 1.0);
    }

    #[test]
    fn test_golden_backoff() {
        let delay = math_consts::golden_backoff(2, 100);
        assert!(delay > 200); // phi^2 * 100 ≈ 262
    }

    #[test]
    fn test_const_mul_add() {
        let result = const_math::linear_combination(2.0, 3.0, 4.0, 5.0);
        assert_eq!(result, 2.0 * 3.0 + 4.0 * 5.0);
    }

    #[test]
    fn test_lazy_lock_get() {
        // Rust 1.94: LazyLock::get 返回 Option<&T>
        // 注意: 如果 LazyLock 未初始化，get() 返回 None
        // 使用 deref 强制初始化
        let _ = &*GLOBAL_CONFIG; // 强制初始化
        let config = LazyLock::get(&GLOBAL_CONFIG);
        assert!(config.is_some());
        assert_eq!(config.unwrap().endpoint, "http://localhost:4317");
    }

    #[test]
    fn test_element_offset() {
        let arr = [10, 20, 30, 40, 50];
        // element_offset 直接返回 usize
        let offset = arr.element_offset(&arr[2]);
        assert_eq!(offset, Some(2));
        
        // 验证第一个和最后一个元素
        assert_eq!(arr.element_offset(&arr[0]), Some(0));
        assert_eq!(arr.element_offset(&arr[4]), Some(4));
    }

    #[test]
    fn test_peekable_next_if_map() {
        let data = vec![2, 4, 6, 8]; // 全是偶数
        let mut parser = parser_utilities::ConditionalParser::new(data.into_iter());

        // next_if_map 使用 Result
        // Ok(R) 表示匹配成功，返回 R
        // Err(item) 表示匹配失败，元素被放回
        
        // 第一个元素 2 是偶数，匹配成功，返回 4
        let result = parser.parse_if(|x| if x % 2 == 0 { Ok(x * 2) } else { Err(x) });
        assert_eq!(result, Some(4));

        // 下一个元素 4，返回 8
        let result = parser.parse_if(|x| if x % 2 == 0 { Ok(x * 2) } else { Err(x) });
        assert_eq!(result, Some(8));
        
        // 继续消费剩余元素
        assert_eq!(parser.parse_if(|x| Ok(x)), Some(6));
        assert_eq!(parser.parse_if(|x| Ok(x)), Some(8));
        assert_eq!(parser.parse_if(|x| Ok(x)), None); // 迭代器耗尽
    }
}
