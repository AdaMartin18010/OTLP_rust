//! Rust 1.90 新特性模型实现
//!
//! 本模块展示 Rust 1.90 引入的新特性在模型实现中的应用：
//! - 常量泛型推断改进
//! - 生命周期省略规则优化
//! - 函数指针类型安全增强

use std::fmt::Debug;

/// 常量泛型模型配置
/// 
/// 使用 const generics 实现编译时确定大小的模型配置
#[derive(Debug, Clone)]
pub struct ModelConfig<const N: usize> {
    pub parameters: [f64; N],
    pub name: String,
}

impl<const N: usize> ModelConfig<N> {
    /// 创建新的模型配置
    pub fn new(parameters: [f64; N], name: String) -> Self {
        Self { parameters, name }
    }
    
    /// 从切片创建配置（长度必须在编译时确定）
    pub fn from_slice(data: &[f64], name: String) -> Self {
        let mut params = [0.0; N];
        let len = data.len().min(N);
        params[..len].copy_from_slice(&data[..len]);
        Self { parameters: params, name }
    }
    
    /// 获取配置维度（编译时常量）
    pub const fn dimension() -> usize {
        N
    }
    
    /// 计算统计信息
    pub fn statistics(&self) -> ConfigStatistics {
        let sum: f64 = self.parameters.iter().sum();
        let mean = sum / N as f64;
        let variance = self.parameters.iter()
            .map(|&x| (x - mean).powi(2))
            .sum::<f64>() / N as f64;
        
        ConfigStatistics {
            mean,
            variance,
            std_dev: variance.sqrt(),
            min: self.parameters.iter().copied().fold(f64::INFINITY, f64::min),
            max: self.parameters.iter().copied().fold(f64::NEG_INFINITY, f64::max),
        }
    }
}

/// 配置统计信息
#[derive(Debug, Clone, Copy)]
pub struct ConfigStatistics {
    pub mean: f64,
    pub variance: f64,
    pub std_dev: f64,
    pub min: f64,
    pub max: f64,
}

/// 数据处理结果
#[derive(Debug, Clone, Copy)]
pub struct DataProcessingResult {
    pub mean: f64,
    pub variance: f64,
    pub std_dev: f64,
    pub processor_id: usize,
}

/// 数据处理器
/// 
/// 展示生命周期优化和性能提升
pub struct DataProcessor<'a> {
    data: &'a [f64],
    processor_id: usize,
}

impl<'a> DataProcessor<'a> {
    /// 创建新的数据处理器
    pub fn new(data: &'a [f64], processor_id: usize) -> Self {
        Self { data, processor_id }
    }
    
    /// 处理数据并返回统计结果
    pub fn process_data(&self) -> DataProcessingResult {
        let n = self.data.len();
        if n == 0 {
            return DataProcessingResult {
                mean: 0.0,
                variance: 0.0,
                std_dev: 0.0,
                processor_id: self.processor_id,
            };
        }
        
        let sum: f64 = self.data.iter().sum();
        let mean = sum / n as f64;
        let variance = self.data.iter()
            .map(|&x| (x - mean).powi(2))
            .sum::<f64>() / n as f64;
        
        DataProcessingResult {
            mean,
            variance,
            std_dev: variance.sqrt(),
            processor_id: self.processor_id,
        }
    }
    
    /// 计算指定分位数
    pub fn quantiles(&self, q: f64) -> f64 {
        if self.data.is_empty() {
            return 0.0;
        }
        
        let mut sorted: Vec<f64> = self.data.to_vec();
        sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());
        
        let index = (q * (sorted.len() - 1) as f64) as usize;
        sorted[index.min(sorted.len() - 1)]
    }
    
    /// 获取处理器ID
    pub fn processor_id(&self) -> usize {
        self.processor_id
    }
}

/// 优化算法类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AlgorithmType {
    GradientDescent,
    NewtonMethod,
    GeneticAlgorithm,
    SimulatedAnnealing,
}

/// 优化结果
#[derive(Debug, Clone)]
pub struct OptimizationResult {
    pub optimal_point: Vec<f64>,
    pub optimal_value: f64,
    pub iterations: usize,
    pub converged: bool,
}

/// 优化引擎
/// 
/// 展示函数指针的类型安全使用
pub struct OptimizationEngine {
    algorithm: AlgorithmType,
    max_iterations: usize,
    tolerance: f64,
}

impl OptimizationEngine {
    /// 创建新的优化引擎
    pub fn new(algorithm: AlgorithmType) -> Self {
        Self {
            algorithm,
            max_iterations: 1000,
            tolerance: 1e-6,
        }
    }
    
    /// 执行优化
    /// 
    /// 使用函数指针传递目标函数
    pub fn optimize<F>(
        &self,
        objective: F,
        _gradient: Option<F>,
        initial: &[f64],
        max_iter: usize,
    ) -> OptimizationResult
    where
        F: Fn(&[f64]) -> f64,
    {
        let mut current = initial.to_vec();
        let mut best_value = objective(&current);
        let mut iterations = 0;
        
        match self.algorithm {
            AlgorithmType::GradientDescent => {
                // 简化的梯度下降实现
                let learning_rate = 0.01;
                for _ in 0..max_iter.min(self.max_iterations) {
                    // 数值梯度估计
                    let gradient: Vec<f64> = (0..current.len())
                        .map(|i| {
                            let mut perturbed = current.clone();
                            perturbed[i] += 1e-8;
                            (objective(&perturbed) - best_value) / 1e-8
                        })
                        .collect();
                    
                    // 更新参数
                    for i in 0..current.len() {
                        current[i] -= learning_rate * gradient[i];
                    }
                    
                    best_value = objective(&current);
                    iterations += 1;
                    
                    // 检查收敛
                    let grad_norm: f64 = gradient.iter().map(|&g| g * g).sum::<f64>().sqrt();
                    if grad_norm < self.tolerance {
                        break;
                    }
                }
            }
            _ => {
                // 其他算法使用简化的随机搜索
                for _ in 0..max_iter.min(self.max_iterations) {
                    let candidate: Vec<f64> = current.iter()
                        .map(|&x| x + fastrand::f64() * 0.2 - 0.1)
                        .collect();
                    let value = objective(&candidate);
                    
                    if value < best_value {
                        best_value = value;
                        current = candidate;
                        iterations += 1;
                    }
                }
            }
        }
        
        OptimizationResult {
            optimal_point: current,
            optimal_value: best_value,
            iterations,
            converged: iterations < max_iter.min(self.max_iterations),
        }
    }
}

/// 优化矩阵
/// 
/// 使用 const generics 实现编译时确定大小的矩阵
#[derive(Debug, Clone)]
pub struct OptimizedMatrix<const ROWS: usize, const COLS: usize> {
    data: [[f64; COLS]; ROWS],
}

impl<const ROWS: usize, const COLS: usize> OptimizedMatrix<ROWS, COLS> {
    /// 创建新的矩阵
    pub fn new() -> Self {
        Self {
            data: [[0.0; COLS]; ROWS],
        }
    }
    
    /// 设置元素值
    pub fn set(&mut self, row: usize, col: usize, value: f64) -> bool {
        if row < ROWS && col < COLS {
            self.data[row][col] = value;
            true
        } else {
            false
        }
    }
    
    /// 获取元素值
    pub fn get(&self, row: usize, col: usize) -> Option<f64> {
        if row < ROWS && col < COLS {
            Some(self.data[row][col])
        } else {
            None
        }
    }
    
    /// 矩阵乘法
    pub fn multiply<const OTHER_COLS: usize>(
        &self,
        other: &OptimizedMatrix<COLS, OTHER_COLS>,
    ) -> OptimizedMatrix<ROWS, OTHER_COLS> {
        let mut result = OptimizedMatrix::<ROWS, OTHER_COLS>::new();
        
        for i in 0..ROWS {
            for j in 0..OTHER_COLS {
                let mut sum = 0.0;
                for k in 0..COLS {
                    sum += self.data[i][k] * other.data[k][j];
                }
                result.data[i][j] = sum;
            }
        }
        
        result
    }
    
    /// 矩阵转置
    pub fn transpose(&self) -> OptimizedMatrix<COLS, ROWS> {
        let mut result = OptimizedMatrix::<COLS, ROWS>::new();
        
        for i in 0..ROWS {
            for j in 0..COLS {
                result.data[j][i] = self.data[i][j];
            }
        }
        
        result
    }
    
    /// 获取矩阵数据（用于测试）
    pub fn data(&self) -> &[[f64; COLS]; ROWS] {
        &self.data
    }
}

impl<const ROWS: usize, const COLS: usize> Default for OptimizedMatrix<ROWS, COLS> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_model_config() {
        let config = ModelConfig::<4>::new([1.0, 2.0, 3.0, 4.0], "test".to_string());
        assert_eq!(ModelConfig::<4>::dimension(), 4);
        
        let stats = config.statistics();
        assert!((stats.mean - 2.5).abs() < 1e-10);
    }

    #[test]
    fn test_data_processor() {
        let data = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        let processor = DataProcessor::new(&data, 1);
        
        let result = processor.process_data();
        assert!((result.mean - 3.0).abs() < 1e-10);
        assert_eq!(result.processor_id, 1);
    }

    #[test]
    fn test_optimization_engine() {
        let engine = OptimizationEngine::new(AlgorithmType::GradientDescent);
        
        fn sphere(x: &[f64]) -> f64 {
            x.iter().map(|&xi| xi * xi).sum()
        }
        
        let result = engine.optimize(sphere, None, &[1.0, 1.0], 100);
        assert!(result.optimal_value < 1.0); // 应该收敛到接近0
    }

    #[test]
    fn test_optimized_matrix() {
        let mut a = OptimizedMatrix::<2, 2>::new();
        a.set(0, 0, 1.0);
        a.set(0, 1, 2.0);
        a.set(1, 0, 3.0);
        a.set(1, 1, 4.0);
        
        let mut b = OptimizedMatrix::<2, 2>::new();
        b.set(0, 0, 5.0);
        b.set(0, 1, 6.0);
        b.set(1, 0, 7.0);
        b.set(1, 1, 8.0);
        
        let c = a.multiply(&b);
        assert_eq!(c.get(0, 0), Some(19.0)); // 1*5 + 2*7 = 19
        assert_eq!(c.get(0, 1), Some(22.0)); // 1*6 + 2*8 = 22
    }
}
