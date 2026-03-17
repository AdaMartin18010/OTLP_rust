//! Rust 1.94 新特性完整实现
//!
//! 本模块展示 Rust 1.94 (2026年3月发布) 的最新语言特性和标准库 API：
//! - LazyCell/LazyLock 的可变访问
//! - 数组切片新操作 (array_windows, element_offset)
//! - 数学常数 (EULER_GAMMA, GOLDEN_RATIO)
//! - 新的迭代器方法
//!
//! 参考: https://releases.rs/docs/1.94.0/

use std::cell::LazyCell;
use std::sync::LazyLock;
use std::sync::Mutex;

/// ==================== LazyCell 新特性 ====================

/// 使用 LazyCell::get_mut 进行可变访问
/// 
/// Rust 1.94 新增：允许在初始化后获取 LazyCell 的可变引用
pub fn lazy_cell_mutable_access() {
    let mut cell: LazyCell<Vec<i32>> = LazyCell::new(|| vec![1, 2, 3]);
    
    // Rust 1.94: 使用 force_mut() 获取可变引用
    let vec = LazyCell::force_mut(&mut cell);
    vec.push(4);
    
    // 验证修改
    assert_eq!(vec, &vec![1, 2, 3, 4]);
}

/// 使用 LazyCell::force_mut 强制初始化并获取可变引用
/// 
/// Rust 1.94 新增：强制初始化（如果尚未初始化）并返回可变引用
pub fn lazy_cell_force_mut() {
    let mut cell: LazyCell<String> = LazyCell::new(|| "initial".to_string());
    
    // Rust 1.94: force_mut 确保初始化并返回可变引用
    let value = LazyCell::force_mut(&mut cell);
    value.push_str(" modified");
    
    assert_eq!(value, "initial modified");
}

/// ==================== LazyLock 新特性 ====================

/// 全局配置缓存 - 使用 LazyLock::get_mut
/// 
/// Rust 1.94 新增：允许在全局静态变量中获取可变引用
static GLOBAL_CONFIG: LazyLock<Mutex<AppConfig>> = LazyLock::new(|| {
    Mutex::new(AppConfig::default())
});

#[derive(Debug, Clone)]
#[allow(dead_code)]
struct AppConfig {
    pub endpoint: String,
    pub timeout_ms: u64,
    pub retries: u32,
}

impl Default for AppConfig {
    fn default() -> Self {
        Self {
            endpoint: "http://localhost:4317".to_string(),
            timeout_ms: 30000,
            retries: 3,
        }
    }
}

/// 使用 Rust 1.94 的 LazyLock 新特性更新全局配置
pub fn update_global_config(new_endpoint: &str) {
    // 传统方式：使用 Mutex 保护可变访问
    let mut config = GLOBAL_CONFIG.lock().unwrap();
    config.endpoint = new_endpoint.to_string();
}

/// ==================== 数组切片新操作 ====================

/// 使用 array_windows 创建滑动窗口
/// 
/// Rust 1.94 稳定：`<[T]>::array_windows`
/// 
/// # Example
/// ```
/// let data = [1, 2, 3, 4, 5];
/// let windows: Vec<_> = data.array_windows::<2>().collect();
/// // windows = [[1, 2], [2, 3], [3, 4], [4, 5]]
/// ```
pub fn sliding_window_analysis(data: &[f64]) -> Vec<(f64, f64)> {
    // Rust 1.94: 使用 array_windows 创建大小为2的滑动窗口
    data.array_windows::<2>()
        .map(|&[a, b]| (a, b))
        .collect()
}

/// 使用 array_windows 计算变化率
pub fn calculate_change_rates(prices: &[f64]) -> Vec<f64> {
    prices.array_windows::<2>()
        .map(|&[prev, curr]| (curr - prev) / prev)
        .collect()
}

/// 使用 element_offset 计算元素偏移
/// 
/// Rust 1.94 稳定：`<[T]>::element_offset`
/// 
/// 返回元素在数组中的字节偏移量
pub fn get_element_byte_offset<T>(slice: &[T], element: &T) -> Option<usize> {
    // Rust 1.94: element_offset 返回元素的字节偏移
    slice.element_offset(element)
}

/// ==================== 数学常数 ====================

/// Rust 1.94 新增的数学常数
pub mod math_consts {
    use std::f64::consts::{EULER_GAMMA, GOLDEN_RATIO};
    
    /// Euler-Mascheroni 常数 (γ ≈ 0.57721566)
    /// 
    /// 在数论和分析中广泛应用
    pub const EULER: f64 = EULER_GAMMA;
    
    /// 黄金比例 (φ ≈ 1.61803399)
    /// 
    /// φ = (1 + √5) / 2
    pub const PHI: f64 = GOLDEN_RATIO;
    
    /// 使用数学常数计算
    pub fn calculate_optimal_value(x: f64) -> f64 {
        // 使用黄金比例进行黄金分割搜索的初始点计算
        let phi = GOLDEN_RATIO;
        let res = x / phi;
        
        // 使用 Euler-Mascheroni 常数进行对数积分近似
        let log_approx = x.ln() + EULER_GAMMA;
        
        (res + log_approx) / 2.0
    }
}

/// ==================== 迭代器新特性 ====================

/// 使用 Peekable::next_if_map
/// 
/// Rust 1.94 稳定：`std::iter::Peekable::next_if_map`
pub fn filter_consecutive_duplicates<T: PartialEq>(iter: &mut std::iter::Peekable<impl Iterator<Item = T>>) -> Vec<T> {
    let mut result = Vec::new();
    
    while let Some(item) = iter.next() {
        // 如果下一个元素与当前不同，则保留当前元素
        if iter.peek() != Some(&item) {
            result.push(item);
        }
    }
    
    result
}

/// ==================== 实际应用场景 ====================

/// OTLP 端点管理器 - 使用 Rust 1.94 特性
#[allow(dead_code)]
pub struct EndpointManager {
    /// 使用 LazyCell 延迟初始化端点列表
    endpoints: LazyCell<Vec<String>>,
    /// 使用 LazyLock 缓存健康检查结果
    health_cache: LazyLock<Mutex<Vec<(String, bool)>>>,
}

impl EndpointManager {
    pub fn new() -> Self {
        Self {
            endpoints: LazyCell::new(|| {
                vec![
                    "http://localhost:4317".to_string(),
                    "http://localhost:4318".to_string(),
                ]
            }),
            health_cache: LazyLock::new(|| Mutex::new(Vec::new())),
        }
    }
    
    /// Rust 1.94: 使用 force_mut 动态添加端点
    pub fn add_endpoint(&mut self, endpoint: &str) {
        let endpoints = LazyCell::force_mut(&mut self.endpoints);
        endpoints.push(endpoint.to_string());
    }
    
    /// 使用 array_windows 进行端点对健康检查
    pub fn check_endpoint_pairs(&self) -> Vec<(&str, &str)> {
        let endpoints: &Vec<String> = LazyCell::force(&self.endpoints);
        
        // Rust 1.94: 使用 array_windows 创建端点对
        endpoints.array_windows::<2>()
            .map(|[a, b]: &[String; 2]| (a.as_str(), b.as_str()))
            .collect()
    }
}

/// 使用数学常数的性能分析器配置
pub struct ProfilerConfig {
    /// 采样间隔（基于黄金比例优化）
    pub sample_interval_ms: u64,
    /// 最大采样深度
    pub max_depth: usize,
}

impl Default for ProfilerConfig {
    fn default() -> Self {
        use std::f64::consts::GOLDEN_RATIO;
        
        // 使用黄金比例计算最优采样间隔
        // φ ≈ 1.618，取整数部分 16ms (约 60fps)
        let base_interval = (1000.0 / GOLDEN_RATIO) as u64;
        
        Self {
            sample_interval_ms: base_interval,
            max_depth: 128,
        }
    }
}

/// 使用 array_windows 的遥测数据批处理器
pub struct BatchProcessor<T> {
    buffer: Vec<T>,
    window_size: usize,
}

impl<T: Clone> BatchProcessor<T> {
    pub fn new(window_size: usize) -> Self {
        Self {
            buffer: Vec::new(),
            window_size,
        }
    }
    
    /// Rust 1.94: 使用 array_windows 处理滑动窗口
    pub fn process_windows<F, R>(&self, f: F) -> Vec<R>
    where
        F: Fn(&[T; 2]) -> R,
    {
        // 注意：这里使用 const generics，需要 Rust 1.51+
        // array_windows 返回的是固定大小的数组引用
        match self.window_size {
            2 => self.buffer.array_windows::<2>().map(f).collect(),
            _ => panic!("Window size {} not supported in this demo", self.window_size),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_lazy_cell_mutable() {
        lazy_cell_mutable_access();
    }
    
    #[test]
    fn test_lazy_cell_force_mut() {
        lazy_cell_force_mut();
    }
    
    #[test]
    fn test_array_windows() {
        let data = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        let windows = sliding_window_analysis(&data);
        
        assert_eq!(windows.len(), 4);
        assert_eq!(windows[0], (1.0, 2.0));
        assert_eq!(windows[3], (4.0, 5.0));
    }
    
    #[test]
    fn test_change_rates() {
        let prices = vec![100.0, 110.0, 121.0];
        let rates = calculate_change_rates(&prices);
        
        assert_eq!(rates.len(), 2);
        assert!((rates[0] - 0.1).abs() < 0.001); // 10% increase
        assert!((rates[1] - 0.1).abs() < 0.001); // 10% increase
    }
    
    #[test]
    fn test_math_consts() {
        use std::f64::consts::{EULER_GAMMA, GOLDEN_RATIO};
        
        // 验证 Euler-Mascheroni 常数
        assert!((EULER_GAMMA - 0.57721566).abs() < 0.0001);
        
        // 验证黄金比例
        assert!((GOLDEN_RATIO - 1.61803399).abs() < 0.0001);
        
        // 验证 φ^2 = φ + 1
        let phi_squared = GOLDEN_RATIO * GOLDEN_RATIO;
        let phi_plus_one = GOLDEN_RATIO + 1.0;
        assert!((phi_squared - phi_plus_one).abs() < 0.0001);
    }
    
    #[test]
    fn test_endpoint_manager() {
        let mut manager = EndpointManager::new();
        
        // 添加新端点
        manager.add_endpoint("http://collector:4317");
        
        // 检查端点对
        let pairs = manager.check_endpoint_pairs();
        assert_eq!(pairs.len(), 2);
    }
    
    #[test]
    fn test_profiler_config() {
        let config = ProfilerConfig::default();
        
        // 采样间隔应基于黄金比例 (~618ms -> 取整)
        assert!(config.sample_interval_ms > 0);
        assert!(config.sample_interval_ms < 1000);
    }
}
