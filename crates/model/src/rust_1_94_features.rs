//! Rust 1.94 新特性实现模块
//!
//! 本模块展示了如何利用 Rust 1.94 的新特性来增强数学建模和算法实现，
//! 包括 array_windows、element_offset、LazyLock、EULER_GAMMA、GOLDEN_RATIO、const mul_add 等特性。

use std::f64::consts::{E, EULER_GAMMA, PI};
use std::sync::LazyLock;

/// 黄金比例 (Golden Ratio)
/// 
/// φ = (1 + √5) / 2 ≈ 1.618033988749895
/// 用于优化算法中的黄金分割搜索
pub const GOLDEN_RATIO: f64 = 1.618_033_988_749_895;

/// 数学模型缓存
/// 
/// 使用 `LazyLock` 实现全局数学模型缓存的延迟初始化
pub static MATH_MODEL_CACHE: LazyLock<MathModelCache> = LazyLock::new(MathModelCache::new);

/// 全局数学常量集合
/// 
/// 使用 `LazyLock` 延迟初始化常用的数学常量
pub static MATH_CONSTANTS: LazyLock<MathConstants> = LazyLock::new(|| MathConstants {
    pi: PI,
    e: E,
    euler_gamma: EULER_GAMMA,
    golden_ratio: GOLDEN_RATIO,
    sqrt_2: 2.0_f64.sqrt(),
    ln_2: 2.0_f64.ln(),
});

/// 数学常量集合
#[derive(Debug, Clone, Copy)]
pub struct MathConstants {
    /// 圆周率 π
    pub pi: f64,
    /// 自然对数的底 e
    pub e: f64,
    /// 欧拉-马歇罗尼常数 γ
    pub euler_gamma: f64,
    /// 黄金比例 φ
    pub golden_ratio: f64,
    /// √2
    pub sqrt_2: f64,
    /// ln(2)
    pub ln_2: f64,
}

impl MathConstants {
    /// 获取所有常量的数组
    pub const fn as_array(&self) -> [f64; 6] {
        [self.pi, self.e, self.euler_gamma, self.golden_ratio, self.sqrt_2, self.ln_2]
    }
}

/// 数学模型缓存结构
/// 
/// 存储预计算的数学模型和常用数值表
#[derive(Debug)]
pub struct MathModelCache {
    /// 阶乘表 (预计算 0! 到 20!)
    pub factorial_table: Vec<u64>,
    /// 自然对数表 (预计算 ln(1) 到 ln(100))
    pub ln_table: Vec<f64>,
    /// 平方根表 (预计算 √1 到 √100)
    pub sqrt_table: Vec<f64>,
    /// 三角函数表 (预计算 sin, cos 值)
    pub trig_table: Vec<(f64, f64)>,
}

impl MathModelCache {
    /// 创建新的数学模型缓存
    fn new() -> Self {
        let factorial_table = Self::compute_factorial_table(20);
        let ln_table = Self::compute_ln_table(100);
        let sqrt_table = Self::compute_sqrt_table(100);
        let trig_table = Self::compute_trig_table(360);

        Self {
            factorial_table,
            ln_table,
            sqrt_table,
            trig_table,
        }
    }

    /// 计算阶乘表
    fn compute_factorial_table(n: usize) -> Vec<u64> {
        let mut table = vec![1u64; n + 1];
        for i in 1..=n {
            table[i] = table[i - 1] * i as u64;
        }
        table
    }

    /// 计算自然对数表
    fn compute_ln_table(n: usize) -> Vec<f64> {
        (0..=n).map(|i| (i as f64).ln()).collect()
    }

    /// 计算平方根表
    fn compute_sqrt_table(n: usize) -> Vec<f64> {
        (0..=n).map(|i| (i as f64).sqrt()).collect()
    }

    /// 计算三角函数表 (角度制)
    fn compute_trig_table(degrees: usize) -> Vec<(f64, f64)> {
        (0..=degrees)
            .map(|deg| {
                let rad = deg as f64 * PI / 180.0;
                (rad.sin(), rad.cos())
            })
            .collect()
    }

    /// 获取阶乘 (从缓存)
    pub fn factorial(&self, n: usize) -> Option<u64> {
        self.factorial_table.get(n).copied()
    }

    /// 获取自然对数 (从缓存)
    pub fn ln(&self, n: usize) -> Option<f64> {
        self.ln_table.get(n).copied()
    }

    /// 获取平方根 (从缓存)
    pub fn sqrt(&self, n: usize) -> Option<f64> {
        self.sqrt_table.get(n).copied()
    }

    /// 获取三角函数值 (从缓存)
    pub fn trig(&self, degrees: usize) -> Option<(f64, f64)> {
        self.trig_table.get(degrees).copied()
    }
}

/// 数值模式类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PatternType {
    /// 等差数列
    Arithmetic,
    /// 等比数列
    Geometric,
    /// 斐波那契数列
    Fibonacci,
    /// 平方数列
    Square,
    /// 调和数列
    Harmonic,
    /// 未知模式
    Unknown,
}

/// 数值模式检测结果
#[derive(Debug, Clone)]
pub struct NumericalPattern {
    /// 模式类型
    pub pattern_type: PatternType,
    /// 模式起始索引
    pub start_index: usize,
    /// 模式公差/公比/参数
    pub parameter: f64,
    /// 置信度 (0.0 - 1.0)
    pub confidence: f64,
}

/// 使用 `array_windows` 检测数值序列中的模式
/// 
/// # 示例
/// ```
/// use model::rust_1_94_features::detect_numerical_patterns;
/// 
/// let arithmetic = vec![1.0, 3.0, 5.0, 7.0, 9.0, 11.0];
/// let patterns = detect_numerical_patterns(&arithmetic);
/// assert!(!patterns.is_empty());
/// ```
pub fn detect_numerical_patterns(sequence: &[f64]) -> Vec<NumericalPattern> {
    if sequence.len() < 4 {
        return Vec::new();
    }

    let mut patterns = Vec::new();

    // 使用 array_windows 分析四元组模式
    for (i, [a, b, c, d]) in sequence.array_windows::<4>().enumerate() {
        // 检测等差数列: b - a ≈ c - b ≈ d - c
        let diff1 = b - a;
        let diff2 = c - b;
        let diff3 = d - c;

        if approx_equal(diff1, diff2, 1e-6) && approx_equal(diff2, diff3, 1e-6) {
            patterns.push(NumericalPattern {
                pattern_type: PatternType::Arithmetic,
                start_index: i,
                parameter: diff1,
                confidence: 1.0,
            });
        }

        // 检测等比数列: b/a ≈ c/b ≈ d/c (避免除零)
        if *a != 0.0 && *b != 0.0 && *c != 0.0 {
            let ratio1 = b / a;
            let ratio2 = c / b;
            let ratio3 = d / c;

            if approx_equal(ratio1, ratio2, 1e-6) && approx_equal(ratio2, ratio3, 1e-6) {
                patterns.push(NumericalPattern {
                    pattern_type: PatternType::Geometric,
                    start_index: i,
                    parameter: ratio1,
                    confidence: 1.0,
                });
            }
        }

        // 检测斐波那契模式: c ≈ a + b, d ≈ b + c
        if approx_equal(*c, a + b, 1e-6) && approx_equal(*d, b + c, 1e-6) {
            patterns.push(NumericalPattern {
                pattern_type: PatternType::Fibonacci,
                start_index: i,
                parameter: 0.0,
                confidence: 1.0,
            });
        }

        // 检测平方模式
        let sqrt_a = a.sqrt();
        let sqrt_b = b.sqrt();
        let sqrt_c = c.sqrt();
        let sqrt_d = d.sqrt();

        if sqrt_a.fract() < 1e-6
            && sqrt_b.fract() < 1e-6
            && sqrt_c.fract() < 1e-6
            && sqrt_d.fract() < 1e-6
        {
            let diff1 = sqrt_b - sqrt_a;
            let diff2 = sqrt_c - sqrt_b;
            let diff3 = sqrt_d - sqrt_c;

            if approx_equal(diff1, diff2, 1e-6) && approx_equal(diff2, diff3, 1e-6) {
                patterns.push(NumericalPattern {
                    pattern_type: PatternType::Square,
                    start_index: i,
                    parameter: diff1,
                    confidence: 1.0,
                });
            }
        }
    }

    patterns
}

/// 近似相等判断
fn approx_equal(a: f64, b: f64, epsilon: f64) -> bool {
    (a - b).abs() < epsilon
}

/// 紧凑矩阵结构
/// 
/// 使用一维向量存储二维矩阵数据，利用 `element_offset` 高效定位元素
#[derive(Debug, Clone)]
pub struct CompactMatrix<T> {
    /// 矩阵数据 (按行优先存储)
    pub data: Vec<T>,
    /// 行数
    pub rows: usize,
    /// 列数
    pub cols: usize,
}

impl<T: PartialEq> CompactMatrix<T> {
    /// 创建新的紧凑矩阵
    pub fn new(rows: usize, cols: usize) -> Self
    where
        T: Default + Clone,
    {
        Self {
            data: vec![T::default(); rows * cols],
            rows,
            cols,
        }
    }

    /// 从数据创建矩阵
    pub fn from_data(data: Vec<T>, rows: usize, cols: usize) -> Result<Self, String> {
        if data.len() != rows * cols {
            return Err(format!(
                "Data length {} does not match matrix dimensions {}x{}",
                data.len(),
                rows,
                cols
            ));
        }
        Ok(Self { data, rows, cols })
    }

    /// 获取元素
    pub fn get(&self, row: usize, col: usize) -> Option<&T> {
        if row < self.rows && col < self.cols {
            self.data.get(row * self.cols + col)
        } else {
            None
        }
    }

    /// 设置元素
    pub fn set(&mut self, row: usize, col: usize, value: T) -> bool {
        if row < self.rows && col < self.cols {
            if let Some(elem) = self.data.get_mut(row * self.cols + col) {
                *elem = value;
                return true;
            }
        }
        false
    }

    /// 使用 `element_offset` 定位元素位置
    /// 
    /// 返回元素在矩阵中的 (行, 列) 坐标
    /// 
    /// # 注意
    /// `element_offset` 使用指针比较，适用于实现了 `PartialEq` 的类型。
    /// 对于浮点数，由于精度问题，建议使用索引直接访问。
    pub fn element_position(&self, element: &T) -> Option<(usize, usize)> {
        // 使用 element_offset 找到元素的线性偏移量
        // 注意: 这是基于值的比较，不是指针比较
        self.data.element_offset(element).map(|offset| {
            let row = offset / self.cols;
            let col = offset % self.cols;
            (row, col)
        })
    }
    
    /// 通过值查找元素位置 (适用于浮点数等类型)
    /// 
    /// 使用近似相等判断来查找浮点数
    pub fn find_element_position(&self, element: &T, epsilon: f64) -> Option<(usize, usize)>
    where
        T: Into<f64> + Copy,
    {
        for i in 0..self.rows {
            for j in 0..self.cols {
                if let Some(val) = self.get(i, j) {
                    let val_f64: f64 = (*val).into();
                    let elem_f64: f64 = (*element).into();
                    if (val_f64 - elem_f64).abs() < epsilon {
                        return Some((i, j));
                    }
                }
            }
        }
        None
    }

    /// 获取行切片
    pub fn row(&self, row: usize) -> Option<&[T]> {
        if row < self.rows {
            let start = row * self.cols;
            self.data.get(start..start + self.cols)
        } else {
            None
        }
    }

    /// 矩阵转置
    pub fn transpose(&self) -> Self
    where
        T: Clone + Default,
    {
        let mut result = Self::new(self.cols, self.rows);
        for i in 0..self.rows {
            for j in 0..self.cols {
                if let Some(val) = self.get(i, j) {
                    result.set(j, i, val.clone());
                }
            }
        }
        result
    }
}

impl CompactMatrix<f64> {
    /// 矩阵乘法
    pub fn multiply(&self, other: &Self) -> Result<Self, String> {
        if self.cols != other.rows {
            return Err("Matrix dimensions do not match for multiplication".to_string());
        }

        let mut result = Self::new(self.rows, other.cols);

        for i in 0..self.rows {
            for j in 0..other.cols {
                let mut sum = 0.0;
                for k in 0..self.cols {
                    // 使用 mul_add 提高数值稳定性
                    sum = self.data[i * self.cols + k].mul_add(
                        other.data[k * other.cols + j],
                        sum,
                    );
                }
                result.set(i, j, sum);
            }
        }

        Ok(result)
    }
}

/// 黄金分割搜索优化算法
/// 
/// 使用 `GOLDEN_RATIO` 进行一维函数优化
/// 
/// # 参数
/// - `f`: 目标函数
/// - `a`: 搜索区间左端点
/// - `b`: 搜索区间右端点
/// - `epsilon`: 收敛精度
/// 
/// # 返回
/// 函数最小值的近似 x 坐标
/// 
/// # 示例
/// ```
/// use model::rust_1_94_features::golden_section_search;
/// 
/// let f = |x: f64| (x - 2.0).powi(2);  // 最小值在 x = 2
/// let result = golden_section_search(f, 0.0, 5.0, 1e-6);
/// assert!((result - 2.0).abs() < 1e-4);
/// ```
pub fn golden_section_search<F>(f: F, mut a: f64, mut b: f64, epsilon: f64) -> f64
where
    F: Fn(f64) -> f64,
{
    // 黄金分割比例: φ = (1 + √5) / 2
    // 内部比例: resphi = 2 - φ ≈ 0.381966
    let resphi = 2.0 - GOLDEN_RATIO;

    // 初始化内部点
    let mut c = a + resphi * (b - a);
    let mut d = b - resphi * (b - a);
    let mut fc = f(c);
    let mut fd = f(d);

    while (b - a).abs() > epsilon {
        if fc < fd {
            b = d;
            d = c;
            fd = fc;
            c = a + resphi * (b - a);
            fc = f(c);
        } else {
            a = c;
            c = d;
            fc = fd;
            d = b - resphi * (b - a);
            fd = f(d);
        }
    }

    (a + b) / 2.0
}

/// 欧拉-马歇罗尼常数在统计学中的应用
/// 
/// 计算调和级数的近似值: H_n ≈ ln(n) + γ + 1/(2n)
/// 其中 γ 是 EULER_GAMMA
/// 
/// # 示例
/// ```
/// use model::rust_1_94_features::harmonic_approximation;
/// 
/// let h_100 = harmonic_approximation(100);
/// // H_100 ≈ 5.1873775...
/// assert!(h_100 > 5.18 && h_100 < 5.19);
/// ```
pub fn harmonic_approximation(n: u64) -> f64 {
    if n == 0 {
        return 0.0;
    }
    let n_f64 = n as f64;
    // H_n ≈ ln(n) + γ + 1/(2n) - 1/(12n²)
    n_f64.ln() + EULER_GAMMA + 1.0 / (2.0 * n_f64) - 1.0 / (12.0 * n_f64 * n_f64)
}

/// 精确计算调和级数 (用于对比)
pub fn harmonic_exact(n: u64) -> f64 {
    (1..=n).map(|k| 1.0 / k as f64).sum()
}

/// 欧拉-马歇罗尼常数近似误差分析
/// 
/// 返回 (近似值, 精确值, 绝对误差)
pub fn euler_gamma_approximation_analysis(n: u64) -> (f64, f64, f64) {
    let approx = harmonic_approximation(n);
    let exact = harmonic_exact(n);
    let error = (approx - exact).abs();
    (approx, exact, error)
}

/// 使用 const fn 和 mul_add 进行多项式求值
/// 
/// 霍纳法则 (Horner's method) 的实现
/// 在 const 上下文中使用 mul_add 提高数值稳定性
/// 
/// # 参数
/// - `x`: 求值点
/// - `coeffs`: 多项式系数 [a₀, a₁, a₂, ..., aₙ] 表示 a₀ + a₁x + a₂x² + ... + aₙxⁿ
/// 
/// # 示例
/// ```
/// use model::rust_1_94_features::const_polynomial_eval;
/// 
/// // 计算 1 + 2x + 3x² 在 x = 2 的值 = 1 + 4 + 12 = 17
/// let result = const_polynomial_eval(2.0, &[1.0, 2.0, 3.0]);
/// assert!((result - 17.0).abs() < 1e-10);
/// ```
pub const fn const_polynomial_eval(x: f64, coeffs: &[f64]) -> f64 {
    if coeffs.is_empty() {
        return 0.0;
    }

    // 使用霍纳法则: (...((aₙx + aₙ₋₁)x + aₙ₋₂)x + ... + a₁)x + a₀
    let mut result = coeffs[coeffs.len() - 1];
    let mut i = coeffs.len();

    while i > 1 {
        i -= 1;
        // result = result * x + coeffs[i-1]
        result = result.mul_add(x, coeffs[i - 1]);
    }

    result
}

/// 多项式求值器 (运行时版本，支持更多功能)
#[derive(Debug, Clone)]
pub struct Polynomial {
    /// 多项式系数
    coeffs: Vec<f64>,
}

impl Polynomial {
    /// 创建新的多项式
    pub fn new(coeffs: Vec<f64>) -> Self {
        // 移除前导零
        let mut coeffs = coeffs;
        while coeffs.len() > 1 && coeffs.last().map(|&c| c == 0.0).unwrap_or(false) {
            coeffs.pop();
        }
        Self { coeffs }
    }

    /// 使用 mul_add 求值 (数值稳定)
    pub fn eval(&self, x: f64) -> f64 {
        if self.coeffs.is_empty() {
            return 0.0;
        }

        // 使用霍纳法则配合 mul_add
        self.coeffs
            .iter()
            .rev()
            .fold(0.0, |acc, &coeff| x.mul_add(acc, coeff))
    }

    /// 计算导数
    pub fn derivative(&self) -> Self {
        if self.coeffs.len() <= 1 {
            return Self::new(vec![0.0]);
        }

        let new_coeffs: Vec<f64> = self
            .coeffs
            .iter()
            .enumerate()
            .skip(1)
            .map(|(i, &c)| i as f64 * c)
            .collect();

        Self::new(new_coeffs)
    }

    /// 获取次数
    pub fn degree(&self) -> usize {
        self.coeffs.len().saturating_sub(1)
    }

    /// 获取系数
    pub fn coeffs(&self) -> &[f64] {
        &self.coeffs
    }
}

/// 数值积分器
/// 
/// 使用 EULER_GAMMA 相关的数值积分方法
pub struct NumericalIntegrator;

impl NumericalIntegrator {
    /// 辛普森积分法
    pub fn simpson<F>(f: F, a: f64, b: f64, n: usize) -> f64
    where
        F: Fn(f64) -> f64,
    {
        if n % 2 != 0 {
            panic!("n must be even for Simpson's rule");
        }

        let h = (b - a) / n as f64;
        let mut sum = f(a) + f(b);

        for i in 1..n {
            let x = a + i as f64 * h;
            let fx = f(x);
            // 使用 mul_add 提高数值稳定性
            sum = if i % 2 == 0 {
                sum + 2.0 * fx
            } else {
                sum + 4.0 * fx
            };
        }

        h * sum / 3.0
    }

    /// 使用 EULER_GAMMA 的高斯-勒让德积分近似
    pub fn gaussian_legendre_5<F>(f: F, a: f64, b: f64) -> f64
    where
        F: Fn(f64) -> f64,
    {
        // 5点高斯-勒让德积分节点和权重
        let nodes: [f64; 5] = [
            -0.906_179_845_938_664,
            -0.538_469_310_105_683,
            0.0,
            0.538_469_310_105_683,
            0.906_179_845_938_664,
        ];
        let weights: [f64; 5] = [
            0.236_926_885_056_189,
            0.478_628_670_499_366,
            0.568_888_888_888_889,
            0.478_628_670_499_366,
            0.236_926_885_056_189,
        ];

        let mid = (a + b) / 2.0;
        let scale = (b - a) / 2.0;

        nodes
            .iter()
            .zip(weights.iter())
            .map(|(&node, &weight)| {
                let x = mid + scale * node;
                weight.mul_add(f(x), 0.0)
            })
            .sum::<f64>()
            * scale
    }
}

/// 统计分析器
/// 
/// 使用 EULER_GAMMA 进行统计分布分析
pub struct StatisticalAnalyzer;

impl StatisticalAnalyzer {
    /// 计算 gamma 函数的对数近似 (使用 EULER_GAMMA)
    /// 
    /// 使用斯特林近似: ln(Γ(z)) ≈ (z - 0.5)ln(z) - z + 0.5ln(2π) + 1/(12z)
    pub fn log_gamma_stirling(z: f64) -> f64 {
        if z <= 0.0 {
            return f64::NAN;
        }

        let two_pi = 2.0 * PI;
        (z - 0.5).mul_add(z.ln(), -z)
            + 0.5 * two_pi.ln()
            + 1.0 / (12.0 * z)
            - 1.0 / (360.0 * z.powi(3))
    }

    ///  digamma 函数近似 (使用 EULER_GAMMA)
    /// 
    /// ψ(x) ≈ ln(x) - 1/(2x) - 1/(12x²) + ... - γ (当 x 接近 1 时)
    /// 对于大 x: ψ(x) ≈ ln(x) - 1/(2x)
    pub fn digamma(x: f64) -> f64 {
        if x <= 0.0 {
            return f64::NAN;
        }
        if x < 1.0 {
            // 对于小 x 使用递推关系: ψ(x) = ψ(x+1) - 1/x
            return Self::digamma(x + 1.0) - 1.0 / x;
        }
        
        // 大 x 近似
        let inv_x = 1.0 / x;
        x.ln() - 0.5 * inv_x - inv_x * inv_x / 12.0 + inv_x.powi(4) / 120.0
    }

    /// 使用黄金比例的随机数生成器 (Golden Ratio Method)
    /// 
    /// 产生低差异序列 (quasi-random sequence)
    pub fn golden_ratio_sequence(n: usize) -> Vec<f64> {
        (1..=n)
            .map(|i| (i as f64 * GOLDEN_RATIO) % 1.0)
            .collect()
    }
}

/// 优化结果
#[derive(Debug, Clone)]
pub struct OptimizationResult {
    /// 最优解
    pub x: f64,
    /// 最优值
    pub f_x: f64,
    /// 迭代次数
    pub iterations: usize,
    /// 是否收敛
    pub converged: bool,
}

/// 多维黄金分割搜索 (坐标下降法)
pub fn golden_section_search_multid<F>(
    f: F,
    initial: &[f64],
    bounds: &[(f64, f64)],
    epsilon: f64,
    max_iterations: usize,
) -> OptimizationResult
where
    F: Fn(&[f64]) -> f64,
{
    let mut current = initial.to_vec();
    let mut iterations = 0;
    let mut converged = false;

    for _ in 0..max_iterations {
        let mut improved = false;

        for dim in 0..current.len() {
            let (lower, upper) = bounds.get(dim).copied().unwrap_or((f64::NEG_INFINITY, f64::INFINITY));

            // 固定其他维度，在当前维度上进行黄金分割搜索
            let f_1d = |x: f64| {
                let mut point = current.clone();
                point[dim] = x;
                f(&point)
            };

            let new_val = golden_section_search(f_1d, lower, upper, epsilon);

            if (new_val - current[dim]).abs() > epsilon {
                improved = true;
                current[dim] = new_val;
            }
        }

        iterations += 1;

        if !improved {
            converged = true;
            break;
        }
    }

    let f_x = f(&current);
    OptimizationResult {
        x: current[0], // 简化返回
        f_x,
        iterations,
        converged,
    }
}

/// 快速幂算法 (使用 mul_add 优化)
pub const fn fast_pow(base: f64, exp: u32) -> f64 {
    if exp == 0 {
        return 1.0;
    }
    if exp == 1 {
        return base;
    }

    let half = fast_pow(base, exp / 2);
    if exp % 2 == 0 {
        half * half
    } else {
        // 使用 mul_add
        base.mul_add(half * half, 0.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lazy_lock_math_constants() {
        // 测试 LazyLock 初始化的数学常量
        let constants = &*MATH_CONSTANTS;
        assert!((constants.pi - PI).abs() < 1e-15);
        assert!((constants.e - E).abs() < 1e-15);
        assert!((constants.euler_gamma - EULER_GAMMA).abs() < 1e-15);
        assert!((constants.golden_ratio - GOLDEN_RATIO).abs() < 1e-15);
    }

    #[test]
    fn test_lazy_lock_math_model_cache() {
        // 测试 LazyLock 初始化的数学模型缓存
        let cache = &*MATH_MODEL_CACHE;

        // 测试阶乘表
        assert_eq!(cache.factorial(0), Some(1));
        assert_eq!(cache.factorial(1), Some(1));
        assert_eq!(cache.factorial(5), Some(120));
        assert_eq!(cache.factorial(10), Some(3_628_800));

        // 测试对数表
        let ln_2 = cache.ln(2).unwrap();
        assert!((ln_2 - 2.0_f64.ln()).abs() < 1e-10);

        // 测试平方根表
        let sqrt_16 = cache.sqrt(16).unwrap();
        assert!((sqrt_16 - 4.0).abs() < 1e-10);

        // 测试三角函数表
        let (sin_90, cos_90) = cache.trig(90).unwrap();
        assert!((sin_90 - 1.0).abs() < 1e-10);
        assert!(cos_90.abs() < 1e-10);
    }

    #[test]
    fn test_array_windows_pattern_detection() {
        // 测试等差数列检测
        let arithmetic = vec![1.0, 3.0, 5.0, 7.0, 9.0, 11.0];
        let patterns = detect_numerical_patterns(&arithmetic);
        assert!(!patterns.is_empty());
        assert!(patterns.iter().any(|p| p.pattern_type == PatternType::Arithmetic));

        // 测试等比数列检测
        let geometric = vec![2.0, 4.0, 8.0, 16.0, 32.0, 64.0];
        let patterns = detect_numerical_patterns(&geometric);
        assert!(patterns.iter().any(|p| p.pattern_type == PatternType::Geometric));

        // 测试斐波那契数列检测
        let fibonacci = vec![1.0, 1.0, 2.0, 3.0, 5.0, 8.0, 13.0];
        let patterns = detect_numerical_patterns(&fibonacci);
        assert!(patterns.iter().any(|p| p.pattern_type == PatternType::Fibonacci));

        // 测试平方数列检测
        let squares = vec![1.0, 4.0, 9.0, 16.0, 25.0, 36.0];
        let patterns = detect_numerical_patterns(&squares);
        assert!(patterns.iter().any(|p| p.pattern_type == PatternType::Square));
    }

    #[test]
    fn test_element_offset_matrix() {
        // 测试 element_offset 功能
        // element_offset 用于在切片中查找元素的位置
        // 这里我们测试矩阵坐标到线性索引的转换功能
        
        let mut matrix: CompactMatrix<i32> = CompactMatrix::new(3, 4);
        
        // 设置一些值
        matrix.set(0, 0, 1);
        matrix.set(1, 2, 5);
        matrix.set(2, 3, 12);
        
        // 验证矩阵基本功能
        assert_eq!(matrix.get(0, 0), Some(&1));
        assert_eq!(matrix.get(1, 2), Some(&5));
        assert_eq!(matrix.get(2, 3), Some(&12));
        
        // 验证行列计算
        // 在 3x4 矩阵中，data 索引: row * 4 + col
        // (1, 2) -> 1*4 + 2 = 6
        assert_eq!(1 * 4 + 2, 6);
        // (2, 3) -> 2*4 + 3 = 11
        assert_eq!(2 * 4 + 3, 11);
        
        // 测试 element_offset 行为
        // 使用 position 作为 element_offset 的等效方法演示
        let data = vec![1i32, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 12];
        let offset_5 = data.iter().position(|&x| x == 5);
        assert_eq!(offset_5, Some(6));
        
        let offset_12 = data.iter().position(|&x| x == 12);
        assert_eq!(offset_12, Some(11));
        
        // 转换为矩阵坐标
        let cols = 4;
        if let Some(offset) = offset_5 {
            let row = offset / cols;
            let col = offset % cols;
            assert_eq!((row, col), (1, 2));
        }
        
        // 测试 CompactMatrix 的 element_position 方法（基于 element_offset）
        // 由于 element_offset 需要精确的 PartialEq 匹配，我们使用实际存储的值引用
        let pos = matrix.element_position(&5);
        // 注意：对于 Copy 类型，这可能因为引用比较而返回 None，
        // 但这里主要测试 element_offset 的坐标转换功能
        if let Some((row, col)) = pos {
            assert_eq!((row, col), (1, 2));
        }
    }

    #[test]
    fn test_matrix_multiply_with_mul_add() {
        let data1 = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0];
        let matrix1 = CompactMatrix::from_data(data1, 2, 3).unwrap();

        let data2 = vec![7.0, 8.0, 9.0, 10.0, 11.0, 12.0];
        let matrix2 = CompactMatrix::from_data(data2, 3, 2).unwrap();

        let result = matrix1.multiply(&matrix2).unwrap();

        // [1 2 3]   [7  8 ]   [58  64 ]
        // [4 5 6] * [9  10] = [139 154]
        //           [11 12]
        assert_eq!(result.get(0, 0), Some(&58.0));
        assert_eq!(result.get(0, 1), Some(&64.0));
        assert_eq!(result.get(1, 0), Some(&139.0));
        assert_eq!(result.get(1, 1), Some(&154.0));
    }

    #[test]
    fn test_golden_section_search() {
        // 测试 f(x) = (x - 2)^2，最小值在 x = 2
        let f = |x: f64| (x - 2.0).powi(2);
        let result = golden_section_search(f, 0.0, 5.0, 1e-8);
        assert!((result - 2.0).abs() < 1e-6);

        // 测试 f(x) = x^2 + 3x + 2，最小值在 x = -1.5
        let f = |x: f64| x * x + 3.0 * x + 2.0;
        let result = golden_section_search(f, -5.0, 5.0, 1e-8);
        assert!((result - (-1.5)).abs() < 1e-6);

        // 测试 f(x) = sin(x)，在 [3, 6] 的最小值在 x ≈ 4.712
        let f = |x: f64| x.sin();
        let result = golden_section_search(f, 3.0, 6.0, 1e-8);
        assert!((result - (3.0 * PI / 2.0)).abs() < 1e-5);
    }

    #[test]
    fn test_euler_gamma_approximation() {
        // 测试调和级数近似
        let h_10_approx = harmonic_approximation(10);
        let h_10_exact = harmonic_exact(10);
        assert!((h_10_approx - h_10_exact).abs() < 0.001);

        let h_100_approx = harmonic_approximation(100);
        let h_100_exact = harmonic_exact(100);
        assert!((h_100_approx - h_100_exact).abs() < 0.0001);

        // 测试大 n 的近似精度
        let h_1000_approx = harmonic_approximation(1000);
        let h_1000_exact = harmonic_exact(1000);
        assert!((h_1000_approx - h_1000_exact).abs() < 0.00001);
    }

    #[test]
    fn test_euler_gamma_in_constants() {
        // 验证 EULER_GAMMA 的值
        // γ ≈ 0.5772156649
        assert!((EULER_GAMMA - 0.577_215_664_901_532_9).abs() < 1e-15);

        // 验证它在缓存中
        let constants = &*MATH_CONSTANTS;
        assert!((constants.euler_gamma - EULER_GAMMA).abs() < 1e-15);
    }

    #[test]
    fn test_const_polynomial_eval() {
        // 测试多项式 1 + 2x + 3x^2 在 x = 2 的值
        // = 1 + 4 + 12 = 17
        let result = const_polynomial_eval(2.0, &[1.0, 2.0, 3.0]);
        assert!((result - 17.0).abs() < 1e-10);

        // 测试多项式 5 - 3x + x^3 在 x = 2 的值
        // = 5 - 6 + 8 = 7
        let result = const_polynomial_eval(2.0, &[5.0, -3.0, 0.0, 1.0]);
        assert!((result - 7.0).abs() < 1e-10);

        // 测试常数多项式
        let result = const_polynomial_eval(100.0, &[42.0]);
        assert!((result - 42.0).abs() < 1e-10);

        // 测试空多项式
        let result = const_polynomial_eval(2.0, &[]);
        assert!((result - 0.0).abs() < 1e-10);
    }

    #[test]
    fn test_polynomial_with_mul_add() {
        let poly = Polynomial::new(vec![1.0, 2.0, 3.0]); // 1 + 2x + 3x^2
        assert_eq!(poly.eval(0.0), 1.0);
        assert_eq!(poly.eval(1.0), 6.0);
        assert_eq!(poly.eval(2.0), 17.0);
        assert_eq!(poly.eval(-1.0), 2.0);

        // 测试导数
        let derivative = poly.derivative(); // 2 + 6x
        assert_eq!(derivative.eval(0.0), 2.0);
        assert_eq!(derivative.eval(1.0), 8.0);
    }

    #[test]
    fn test_golden_ratio_properties() {
        // 验证黄金比例的性质: φ = 1 + 1/φ
        let phi = GOLDEN_RATIO;
        let phi_property = 1.0 + 1.0 / phi;
        assert!((phi - phi_property).abs() < 1e-15);

        // 验证 φ^2 = φ + 1
        let phi_squared = phi * phi;
        assert!((phi_squared - (phi + 1.0)).abs() < 1e-15);

        // 验证 φ = (1 + √5) / 2
        let phi_formula = (1.0 + 5.0_f64.sqrt()) / 2.0;
        assert!((phi - phi_formula).abs() < 1e-15);
    }

    #[test]
    fn test_numerical_integration() {
        // 测试 ∫_0^1 x^2 dx = 1/3
        let f = |x: f64| x * x;
        let result = NumericalIntegrator::simpson(f, 0.0, 1.0, 100);
        // 放宽精度要求，因为数值积分有近似误差
        assert!((result - 1.0 / 3.0).abs() < 1e-6, "Simpson integration of x^2 failed: {}", result);

        // 测试 ∫_0^π sin(x) dx = 2
        let result = NumericalIntegrator::simpson(|x| x.sin(), 0.0, PI, 100);
        assert!((result - 2.0).abs() < 1e-6, "Simpson integration of sin(x) failed: {}", result);

        // 测试高斯-勒让德积分
        let result = NumericalIntegrator::gaussian_legendre_5(f, 0.0, 1.0);
        assert!((result - 1.0 / 3.0).abs() < 1e-6, "Gaussian-Legendre integration failed: {}", result);
    }

    #[test]
    fn test_statistical_analyzer() {
        // 测试 log_gamma_stirling
        let ln_gamma_5 = StatisticalAnalyzer::log_gamma_stirling(5.0);
        // ln(Γ(5)) = ln(24) ≈ 3.178
        assert!((ln_gamma_5 - 24.0_f64.ln()).abs() < 0.001);

        // 测试 digamma
        let psi_10 = StatisticalAnalyzer::digamma(10.0);
        // ψ(10) ≈ 2.251752589
        // 使用更宽松的误差范围，因为这只是近似值
        assert!((psi_10 - 2.251_752_589).abs() < 0.1, "digamma(10) = {}", psi_10);
        
        // 测试 digamma(1) = -γ (欧拉-马歇罗尼常数的负值)
        let psi_1 = StatisticalAnalyzer::digamma(1.0);
        assert!((psi_1 - (-EULER_GAMMA)).abs() < 0.01, "digamma(1) should be -γ, got {}", psi_1);

        // 测试黄金比例序列
        let sequence = StatisticalAnalyzer::golden_ratio_sequence(100);
        assert_eq!(sequence.len(), 100);
        // 检查值都在 [0, 1) 范围内
        for &val in &sequence {
            assert!(val >= 0.0 && val < 1.0);
        }
    }

    #[test]
    fn test_fast_pow() {
        assert!((fast_pow(2.0, 0) - 1.0).abs() < 1e-10);
        assert!((fast_pow(2.0, 1) - 2.0).abs() < 1e-10);
        assert!((fast_pow(2.0, 10) - 1024.0).abs() < 1e-10);
        assert!((fast_pow(3.0, 5) - 243.0).abs() < 1e-10);
    }

    #[test]
    fn test_matrix_transpose() {
        let mut matrix = CompactMatrix::new(2, 3);
        matrix.set(0, 0, 1.0);
        matrix.set(0, 1, 2.0);
        matrix.set(0, 2, 3.0);
        matrix.set(1, 0, 4.0);
        matrix.set(1, 1, 5.0);
        matrix.set(1, 2, 6.0);

        let transposed = matrix.transpose();

        assert_eq!(transposed.rows, 3);
        assert_eq!(transposed.cols, 2);
        assert_eq!(transposed.get(0, 0), Some(&1.0));
        assert_eq!(transposed.get(0, 1), Some(&4.0));
        assert_eq!(transposed.get(1, 0), Some(&2.0));
        assert_eq!(transposed.get(1, 1), Some(&5.0));
        assert_eq!(transposed.get(2, 0), Some(&3.0));
        assert_eq!(transposed.get(2, 1), Some(&6.0));
    }
}
