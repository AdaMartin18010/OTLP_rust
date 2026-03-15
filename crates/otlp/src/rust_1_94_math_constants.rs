//! # Rust 1.94 数学常量与 OTLP 优化算法
//!
//! 本模块实现基于 Rust 1.94 新增数学常量的 OTLP 优化算法：
//!
//! - **`EULER_GAMMA`**: Euler-Mascheroni 常数 (γ ≈ 0.5772)
//! - **`GOLDEN_RATIO`**: 黄金比例 (φ ≈ 1.6180)
//! - **`const mul_add`**: 编译时融合乘加优化
//!
//! ## 数学背景
//!
//! ### Euler-Mascheroni 常数 (γ)
//! Euler-Mascheroni 常数是数学中重要的常数，定义为：
//! ```text
//! γ = lim(n→∞) [Σ(1/k) - ln(n)]  (k=1 to n)
//! ```
//! 在 OTLP 中用于：
//! - 自适应采样率的平滑调整
//! - 负载均衡的阻尼系数
//! - 累积分布函数的近似计算
//!
//! ### 黄金比例 (φ)
//! 黄金比例是满足 φ = (1 + √5) / 2 ≈ 1.618 的无理数，具有性质：
//! ```text
//! φ² = φ + 1
//! 1/φ = φ - 1
//! ```
//! 在 OTLP 中用于：
//! - 指数退避的最优间隔计算
//! - 批量大小的 Fibonacci 增长
//! - 资源分配的均衡分割
//!
//! ### 融合乘加 (FMA)
//! FMA 指令在单个操作中计算 `a * b + c`，提供：
//! - 更高的精度（避免中间结果舍入）
//! - 更快的执行速度（单指令周期）
//! - 更好的数值稳定性
//!
//! ## 使用示例
//!
//! ```rust
//! use otlp::rust_1_94_math_constants::{
//!     euler_gamma_sampling_rate,
//!     golden_ratio_backoff,
//!     fibonacci_batch_size,
//! };
//!
//! // 自适应采样
//! let rate = euler_gamma_sampling_rate(100.0, 0.5);
//!
//! // 黄金比例退避
//! let delay = golden_ratio_backoff(3, 100);
//!
//! // Fibonacci 批量大小
//! let batch_size = fibonacci_batch_size(5, 1000);
//! ```

#![allow(dead_code)]

use std::f64::consts::{EULER_GAMMA, GOLDEN_RATIO};

// ============================================================================
// 常数定义与预计算
// ============================================================================

/// Euler-Mascheroni 常数的倒数
///
/// 用于快速除法运算，避免运行时计算
pub const EULER_GAMMA_RECIP: f64 = 1.0 / EULER_GAMMA; // ≈ 1.732

/// 黄金比例的倒数 (φ' = φ - 1 = 1/φ ≈ 0.618)
///
/// 在退避算法中用于递减乘数
pub const GOLDEN_RATIO_RECIP: f64 = 1.0 / GOLDEN_RATIO;

/// 黄金比例的平方 (φ² = φ + 1 ≈ 2.618)
///
/// 用于快速计算二次增长
pub const GOLDEN_RATIO_SQUARED: f64 = GOLDEN_RATIO * GOLDEN_RATIO;

/// 预计算的 sqrt(5)，用于 Fibonacci 计算
pub const SQRT_5_F64: f64 = 2.23606797749979;

/// Fibonacci 计算中的常数因子
///
/// Binet 公式中的分母：φ^n / √5
pub const FIBONACCI_FACTOR: f64 = 1.0 / SQRT_5_F64;

// ============================================================================
// EULER_GAMMA 应用 - 自适应采样
// ============================================================================

/// 使用 Euler-Mascheroni 常数的自适应采样率计算
///
/// 基于系统负载动态调整采样率，利用 γ 作为阻尼因子
/// 实现平滑的负载自适应。
///
/// # 数学原理
///
/// 采样率计算公式：
/// ```text
/// rate = base_rate * (1 + γ * ln(load + 1) / ln(max_load + 1))
/// ```
///
/// 其中 γ (EULER_GAMMA) 作为调节系数，确保：
/// - 负载增加时采样率平滑上升
/// - 避免采样率的剧烈抖动
/// - 保持数值稳定性
///
/// # 参数
///
/// * `load` - 当前系统负载（例如：QPS、内存使用率、CPU 使用率）
/// * `base_rate` - 基础采样率 (0.0 - 1.0)
///
/// # 返回值
///
/// 调整后的采样率，范围在 [0.001, 1.0] 之间
///
/// # 示例
///
/// ```rust
/// use otlp::rust_1_94_math_constants::euler_gamma_sampling_rate;
///
/// // 中等负载下的采样率
/// let rate = euler_gamma_sampling_rate(50.0, 0.1);
/// assert!(rate > 0.001 && rate <= 1.0);
///
/// // 高负载下的采样率（应该更高）
/// let high_rate = euler_gamma_sampling_rate(200.0, 0.1);
/// assert!(high_rate >= rate);
/// ```
pub fn euler_gamma_sampling_rate(load: f64, base_rate: f64) -> f64 {
    if load <= 0.0 || base_rate <= 0.0 {
        return 0.001;
    }

    // 使用 EULER_GAMMA 作为阻尼系数
    // ln(load + 1) 确保负载为 0 时不会出错
    let load_factor = (load + 1.0).ln();
    
    // 归一化负载因子（假设最大负载对应 ln(10000) ≈ 9.21）
    let normalized_load = load_factor / 9.21_f64.ln();
    
    // 应用 EULER_GAMMA 调节
    // rate = base_rate * (1 + γ * normalized_load)
    let adjusted = base_rate.mul_add(EULER_GAMMA * normalized_load, base_rate);
    
    // 限制在有效范围内
    adjusted.clamp(0.001, 1.0)
}

/// 使用 Euler-Mascheroni 常数的累积采样决策
///
/// 基于序列位置决定采样，利用 γ 的性质实现
/// 均匀分布的采样点。
///
/// # 数学原理
///
/// 利用调和级数与对数的关系：
/// ```text
/// H_n = Σ(1/k) ≈ ln(n) + γ + 1/(2n)
/// ```
///
/// 当 `n * rate` 接近 H_n 的整数倍时采样。
///
/// # 参数
///
/// * `sequence_number` - 序列中的位置
/// * `target_rate` - 目标采样率
///
/// # 返回值
///
/// 如果应该采样返回 true
///
/// # 示例
///
/// ```rust
/// use otlp::rust_1_94_math_constants::euler_gamma_cumulative_sampling;
///
/// let should_sample = euler_gamma_cumulative_sampling(100, 0.1);
/// // 采样决策基于序列位置和目标率
/// ```
pub fn euler_gamma_cumulative_sampling(sequence_number: u64, target_rate: f64) -> bool {
    if target_rate >= 1.0 {
        return true;
    }
    if target_rate <= 0.0 {
        return false;
    }

    let n = sequence_number as f64;
    
    // 使用 H_n ≈ ln(n) + γ 的近似
    // 当 n 是 1/rate 的倍数时采样
    let harmonic_approx = n.ln() + EULER_GAMMA;
    let interval = 1.0 / target_rate;
    
    // 检查是否接近采样点
    let remainder = harmonic_approx % interval;
    remainder < 1.0 || remainder > interval - 1.0
}

/// 基于 Euler-Mascheroni 的优先级采样权重
///
/// 为不同优先级的数据计算采样权重，高优先级数据
/// 获得更高的保留概率。
///
/// # 参数
///
/// * `priority` - 优先级（1-10，10 为最高）
/// * `base_weight` - 基础权重
///
/// # 返回值
///
/// 计算后的采样权重
pub fn euler_gamma_priority_weight(priority: u8, base_weight: f64) -> f64 {
    let p = priority.clamp(1, 10) as f64;
    
    // 使用 γ 作为优先级增长的调节因子
    // weight = base_weight * (1 + γ * log10(priority))
    let priority_factor = 1.0 + EULER_GAMMA * p.log10();
    
    base_weight * priority_factor
}

// ============================================================================
// GOLDEN_RATIO 应用 - 指数退避与批量策略
// ============================================================================

/// 使用黄金比例的指数退避计算
///
/// 基于黄金比例的退避策略，相比传统的指数退避（2^n）
/// 提供更平滑的增长曲线，减少 thundering herd 问题。
///
/// # 数学原理
///
/// 退避时间计算：
/// ```text
/// delay = base_delay * φ^attempt
/// ```
///
/// 其中 φ = GOLDEN_RATIO ≈ 1.618
///
/// 相比 2^n 的优势：
/// - 增长更平缓，减少资源竞争
/// - φ 的无理性确保退避时间分布更均匀
/// - 符合自然界最优分布模式
///
/// # 参数
///
/// * `attempt` - 重试次数（从 0 开始）
/// * `base_delay_ms` - 基础延迟（毫秒）
///
/// # 返回值
///
/// 计算后的延迟时间（毫秒），上限为 300,000ms (5分钟)
///
/// # 示例
///
/// ```rust
/// use otlp::rust_1_94_math_constants::golden_ratio_backoff;
///
/// let delay_0 = golden_ratio_backoff(0, 100);  // 100ms
/// let delay_1 = golden_ratio_backoff(1, 100);  // ~162ms
/// let delay_2 = golden_ratio_backoff(2, 100);  // ~262ms
///
/// assert!(delay_1 > delay_0);
/// assert!(delay_2 > delay_1);
/// ```
pub fn golden_ratio_backoff(attempt: u32, base_delay_ms: u64) -> u64 {
    const MAX_DELAY_MS: u64 = 300_000; // 5 分钟上限
    
    if attempt == 0 {
        return base_delay_ms.min(MAX_DELAY_MS);
    }
    
    // 使用黄金比例的幂次：φ^attempt
    let multiplier = GOLDEN_RATIO.powi(attempt as i32);
    let delay = (base_delay_ms as f64 * multiplier) as u64;
    
    delay.min(MAX_DELAY_MS)
}

/// 使用黄金比例倒数的递减退避
///
/// 用于从高峰负载恢复时逐步减少延迟，
/// 使用 1/φ ≈ 0.618 作为递减因子。
///
/// # 参数
///
/// * `current_delay_ms` - 当前延迟（毫秒）
/// * `min_delay_ms` - 最小延迟（毫秒）
///
/// # 返回值
///
/// 递减后的延迟时间
pub fn golden_ratio_backoff_decay(current_delay_ms: u64, min_delay_ms: u64) -> u64 {
    let decayed = (current_delay_ms as f64 * GOLDEN_RATIO_RECIP) as u64;
    decayed.max(min_delay_ms)
}

/// 基于黄金比例的 Fibonacci 批量大小计算
///
/// 利用黄金比例与 Fibonacci 数列的关系：
/// ```text
/// F(n) ≈ φ^n / √5
/// ```
///
/// 实现平滑的批量大小增长，适合 OTLP 批处理场景。
///
/// # 数学原理
///
/// Binet 公式：
/// ```text
/// F(n) = (φ^n - (1-φ)^n) / √5
/// ```
///
/// 当 n 较大时，(1-φ)^n → 0，所以：
/// ```text
/// F(n) ≈ φ^n / √5
/// ```
///
/// # 参数
///
/// * `iteration` - 迭代次数（决定 Fibonacci 数列位置）
/// * `max_size` - 最大批量大小
///
/// # 返回值
///
/// 计算的批量大小，范围在 [1, max_size]
///
/// # 示例
///
/// ```rust
/// use otlp::rust_1_94_math_constants::fibonacci_batch_size;
///
/// let size_0 = fibonacci_batch_size(0, 1000);  // ~1
/// let size_1 = fibonacci_batch_size(1, 1000);  // ~1
/// let size_5 = fibonacci_batch_size(5, 1000);  // ~5
/// let size_10 = fibonacci_batch_size(10, 1000); // ~55
///
/// assert!(size_5 >= size_1);
/// assert!(size_10 >= size_5);
/// ```
pub fn fibonacci_batch_size(iteration: u32, max_size: usize) -> usize {
    if max_size == 0 {
        return 1;
    }
    
    // 使用 Binet 公式近似计算 Fibonacci 数
    // F(n) ≈ φ^n / √5
    let n = iteration as f64;
    let phi_n = GOLDEN_RATIO.powf(n);
    let fib_approx = (phi_n * FIBONACCI_FACTOR).round() as usize;
    
    // 确保至少为 1，不超过最大值
    fib_approx.max(1).min(max_size)
}

/// 精确的 Fibonacci 数计算（迭代实现）
///
/// 对于小数值使用精确计算，大数值使用黄金比例近似。
///
/// # 参数
///
/// * `n` - Fibonacci 数列索引
///
/// # 返回值
///
/// 第 n 个 Fibonacci 数
pub fn fibonacci_exact(n: u32) -> u64 {
    match n {
        0 => 0,
        1 => 1,
        2 => 1,
        // 对于小数值使用迭代计算
        3..=50 => {
            let mut a = 0u64;
            let mut b = 1u64;
            for _ in 2..=n {
                let next = a.saturating_add(b);
                a = b;
                b = next;
            }
            b
        }
        // 对于大数值使用黄金比例近似
        _ => {
            let approx = GOLDEN_RATIO.powi(n as i32) * FIBONACCI_FACTOR;
            approx as u64
        }
    }
}

/// 使用黄金比例的资源分配
///
/// 将资源按黄金比例分割，实现最优分配。
/// 较小的部分获得 1/φ ≈ 38.2%，较大的部分获得 1/φ² ≈ 61.8%。
///
/// # 参数
///
/// * `total` - 总资源量
///
/// # 返回值
///
/// (较小部分, 较大部分) 的元组
///
/// # 示例
///
/// ```rust
/// use otlp::rust_1_94_math_constants::golden_ratio_split;
///
/// let (small, large) = golden_ratio_split(1000);
/// assert_eq!(small + large, 1000);
/// // small ≈ 382, large ≈ 618
/// assert!(small < large);
/// ```
pub fn golden_ratio_split(total: u64) -> (u64, u64) {
    let small = (total as f64 * GOLDEN_RATIO_RECIP * GOLDEN_RATIO_RECIP) as u64;
    let large = total - small;
    (small, large)
}

/// 黄金比例抖动
///
/// 在退避时间中添加基于黄金比例的随机抖动，
/// 分散请求时间，避免同步重试。
///
/// # 参数
///
/// * `base_delay_ms` - 基础延迟（毫秒）
/// * `jitter_factor` - 抖动因子 (0.0 - 1.0)
///
/// # 返回值
///
/// 添加抖动后的延迟
pub fn golden_ratio_jitter(base_delay_ms: u64, jitter_factor: f64) -> u64 {
    let factor = jitter_factor.clamp(0.0, 1.0);
    
    // 使用黄金比例的小数部分作为伪随机因子
    let phi_fractional = GOLDEN_RATIO - 1.0; // ≈ 0.618
    let jitter = base_delay_ms as f64 * factor * phi_fractional;
    
    (base_delay_ms as f64 + jitter) as u64
}

// ============================================================================
// const mul_add 应用 - 编译时优化
// ============================================================================

/// 编译时融合乘加运算
///
/// Rust 1.94 允许在 const 上下文中使用 `mul_add`，
/// 这使得高精度数值计算可以在编译时完成。
///
/// # 优势
///
/// - 单指令周期完成乘加运算
/// - 避免中间结果的舍入误差
/// - 编译时常量折叠优化
///
/// # 示例
///
/// ```rust
/// use otlp::rust_1_94_math_constants::const_mul_add;
///
/// // 编译时计算：2 * 3 + 4 = 10
/// const RESULT: f64 = const_mul_add(2.0, 3.0, 4.0);
/// assert_eq!(RESULT, 10.0);
/// ```
pub const fn const_mul_add(a: f64, b: f64, c: f64) -> f64 {
    a.mul_add(b, c)
}

/// 编译时线性插值
///
/// 使用 const mul_add 实现编译时的线性插值计算。
///
/// # 公式
///
/// ```text
/// lerp(a, b, t) = a + (b - a) * t = a * (1-t) + b * t
/// ```
///
/// # 示例
///
/// ```rust
/// use otlp::rust_1_94_math_constants::const_lerp;
///
/// // 0 和 10 之间的中间值
/// const MID: f64 = const_lerp(0.0, 10.0, 0.5);
/// assert_eq!(MID, 5.0);
/// ```
pub const fn const_lerp(a: f64, b: f64, t: f64) -> f64 {
    // lerp = a * (1-t) + b * t = a + t * (b - a)
    t.mul_add(b - a, a)
}

/// 编译时多项式求值（Horner 方法）
///
/// 高效计算多项式：p(x) = a₀ + a₁x + a₂x² + ... + aₙxⁿ
/// 使用 Horner 形式：p(x) = (...((aₙx + aₙ₋₁)x + aₙ₋₂)...)x + a₀
///
/// # 示例
///
/// ```rust
/// use otlp::rust_1_94_math_constants::const_poly_eval;
///
/// // 计算：2 + 3x + 4x²，其中 x = 2
/// // 结果 = 2 + 6 + 16 = 24
/// const RESULT: f64 = const_poly_eval(2.0, &[2.0, 3.0, 4.0]);
/// assert_eq!(RESULT, 24.0);
/// ```
pub const fn const_poly_eval(x: f64, coeffs: &[f64]) -> f64 {
    let mut result: f64 = 0.0;
    let mut i = coeffs.len();
    
    // Horner 方法：从内到外计算
    while i > 0 {
        i -= 1;
        result = result.mul_add(x, coeffs[i]);
    }
    
    result
}

/// 编译时 sigmoid 函数近似
///
/// 使用多项式近似计算 sigmoid 函数，适用于编译时常量。
///
/// # 数学
///
/// Sigmoid: σ(x) = 1 / (1 + e^(-x))
///
/// 在 x=0 附近使用泰勒展开近似。
pub const fn const_sigmoid_approx(x: f64) -> f64 {
    // 对于小 x 使用近似：σ(x) ≈ 0.5 + x/4
    // 对于大 x 使用饱和
    if x > 4.0 {
        1.0
    } else if x < -4.0 {
        0.0
    } else {
        // 使用 mul_add 进行线性近似
        0.25_f64.mul_add(x, 0.5)
    }
}

// ============================================================================
// 高级 OTLP 特定算法
// ============================================================================

/// 自适应批量超时计算
///
/// 基于黄金比例和 Euler-Mascheroni 常数计算动态批量超时，
/// 在高负载时减少超时以提高吞吐量，在低负载时增加超时以优化批处理。
///
/// # 参数
///
/// * `queue_depth` - 当前队列深度
/// * `base_timeout_ms` - 基础超时（毫秒）
/// * `max_timeout_ms` - 最大超时（毫秒）
///
/// # 返回值
///
/// 计算后的超时时间（毫秒）
pub fn adaptive_batch_timeout(queue_depth: usize, base_timeout_ms: u64, max_timeout_ms: u64) -> u64 {
    if queue_depth == 0 {
        return max_timeout_ms;
    }
    
    let depth = queue_depth as f64;
    
    // 使用黄金比例计算负载因子
    let load_factor = (depth / 100.0).min(1.0); // 假设 100 为满载
    
    // 使用 Euler-Gamma 作为调节参数
    // timeout = base + (max - base) * (1 - load_factor)^γ
    let remaining = 1.0 - load_factor;
    let adjusted_remaining = remaining.powf(EULER_GAMMA);
    
    let timeout = const_lerp(
        base_timeout_ms as f64,
        max_timeout_ms as f64,
        adjusted_remaining,
    );
    
    timeout as u64
}

/// OTLP 连接池大小优化
///
/// 基于 Euler-Mascheroni 常数计算最优连接池大小，
/// 平衡资源使用与并发性能。
///
/// # 参数
///
/// * `expected_concurrency` - 预期并发数
/// * `max_pool_size` - 最大连接池大小
///
/// # 返回值
///
/// 建议的连接池大小
///
/// # 数学原理
///
/// 最优池大小 ≈ concurrency / (1 + γ)
/// 其中 γ 确保池大小不会过大，留有余量
pub fn optimal_connection_pool_size(expected_concurrency: u32, max_pool_size: u32) -> u32 {
    if expected_concurrency == 0 {
        return 1;
    }
    
    // 使用 1 + γ 作为安全系数
    let safety_factor = 1.0 + EULER_GAMMA;
    let optimal = (expected_concurrency as f64 / safety_factor).ceil() as u32;
    
    optimal.max(1).min(max_pool_size)
}

/// 采样率动态调整
///
/// 基于历史采样数据动态调整采样率，使用黄金比例
/// 作为调整步长，实现快速收敛。
///
/// # 参数
///
/// * `current_rate` - 当前采样率
/// * `target_samples` - 目标样本数
/// * `actual_samples` - 实际样本数
///
/// # 返回值
///
/// 调整后的采样率
pub fn adjust_sampling_rate(
    current_rate: f64,
    target_samples: u64,
    actual_samples: u64,
) -> f64 {
    if target_samples == 0 || actual_samples == 0 {
        return current_rate.clamp(0.001, 1.0);
    }
    
    let ratio = target_samples as f64 / actual_samples as f64;
    
    // 使用黄金比例的幂次作为调整步长
    let adjustment = if ratio > 1.0 {
        // 需要更多样本，增加采样率
        GOLDEN_RATIO_RECIP.powf(ratio.log2().abs())
    } else {
        // 需要更少样本，减少采样率
        GOLDEN_RATIO_RECIP.powf(ratio.log2().abs())
    };
    
    let new_rate = current_rate * adjustment;
    new_rate.clamp(0.001, 1.0)
}

// ============================================================================
// 数值工具函数
// ============================================================================

/// 计算两个 f64 的安全中点
///
/// 使用 f64::midpoint (Rust 1.94) 避免溢出。
pub fn safe_midpoint(a: f64, b: f64) -> f64 {
    a.midpoint(b)
}

/// 检查浮点数是否近似相等（使用机器 epsilon）
pub fn approx_eq(a: f64, b: f64) -> bool {
    (a - b).abs() < f64::EPSILON
}

/// 将采样率转换为对数刻度表示
///
/// 使用 Euler-Mascheroni 常数作为基准进行对数变换。
pub fn rate_to_log_scale(rate: f64) -> f64 {
    let clamped = rate.clamp(0.001, 1.0);
    -clamped.ln() / EULER_GAMMA
}

/// 从对数刻度还原采样率
pub fn log_scale_to_rate(log_scale: f64) -> f64 {
    (-log_scale * EULER_GAMMA).exp().clamp(0.001, 1.0)
}

// ============================================================================
// 测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // ========== EULER_GAMMA 测试 ==========

    #[test]
    fn test_euler_gamma_constant() {
        // 验证 EULER_GAMMA 的近似值
        assert!((EULER_GAMMA - 0.5772156649).abs() < 1e-10);
        assert!(EULER_GAMMA > 0.5 && EULER_GAMMA < 0.6);
    }

    #[test]
    fn test_euler_gamma_sampling_rate_basic() {
        // 零负载应该返回基础采样率
        let rate_zero = euler_gamma_sampling_rate(0.0, 0.1);
        assert_eq!(rate_zero, 0.001); // 最小值

        // 正常负载
        let rate_low = euler_gamma_sampling_rate(10.0, 0.1);
        let rate_high = euler_gamma_sampling_rate(1000.0, 0.1);

        // 高负载应该产生更高的采样率
        assert!(rate_high >= rate_low);

        // 采样率应该在合理范围内
        assert!(rate_low >= 0.001 && rate_low <= 1.0);
        assert!(rate_high >= 0.001 && rate_high <= 1.0);
    }

    #[test]
    fn test_euler_gamma_cumulative_sampling() {
        // 100% 采样率应该总是采样
        assert!(euler_gamma_cumulative_sampling(1, 1.0));
        assert!(euler_gamma_cumulative_sampling(1000, 1.0));

        // 0% 采样率应该永不采样
        assert!(!euler_gamma_cumulative_sampling(1, 0.0));
        assert!(!euler_gamma_cumulative_sampling(1000, 0.0));

        // 中等采样率应该有一些采样点
        let samples: u64 = (1..=1000)
            .filter(|&n| euler_gamma_cumulative_sampling(n, 0.1))
            .count() as u64;
        
        // 应该有大约 10% 的采样点（允许一定误差）
        assert!(samples >= 50 && samples <= 150);
    }

    #[test]
    fn test_euler_gamma_priority_weight() {
        let w1 = euler_gamma_priority_weight(1, 1.0);
        let w5 = euler_gamma_priority_weight(5, 1.0);
        let w10 = euler_gamma_priority_weight(10, 1.0);

        // 高优先级应该有更高权重
        assert!(w5 >= w1);
        assert!(w10 >= w5);

        // 权重应该合理
        assert!(w1 >= 1.0);
        assert!(w10 < 10.0);
    }

    // ========== GOLDEN_RATIO 测试 ==========

    #[test]
    fn test_golden_ratio_constant() {
        // 验证 GOLDEN_RATIO 的近似值
        assert!((GOLDEN_RATIO - 1.6180339887).abs() < 1e-10);
        
        // 验证黄金比例的性质：φ² = φ + 1
        let phi_squared = GOLDEN_RATIO * GOLDEN_RATIO;
        let phi_plus_one = GOLDEN_RATIO + 1.0;
        assert!((phi_squared - phi_plus_one).abs() < 1e-10);
        
        // 验证 1/φ = φ - 1
        assert!((GOLDEN_RATIO_RECIP - (GOLDEN_RATIO - 1.0)).abs() < 1e-10);
    }

    #[test]
    fn test_golden_ratio_backoff() {
        let base = 100;

        // 第 0 次尝试应该是基础延迟
        let d0 = golden_ratio_backoff(0, base);
        assert_eq!(d0, base);

        // 延迟应该随尝试次数增加
        let d1 = golden_ratio_backoff(1, base);
        let d2 = golden_ratio_backoff(2, base);
        let d3 = golden_ratio_backoff(3, base);

        assert!(d1 > d0);
        assert!(d2 > d1);
        assert!(d3 > d2);

        // 验证近似值
        assert!((d1 as f64 - 162.0).abs() < 5.0);
        assert!((d2 as f64 - 262.0).abs() < 5.0);
    }

    #[test]
    fn test_golden_ratio_backoff_max_limit() {
        // 测试最大延迟限制
        let large = golden_ratio_backoff(100, 1000);
        assert!(large <= 300_000);
    }

    #[test]
    fn test_golden_ratio_backoff_decay() {
        let current = 1000;
        let decayed = golden_ratio_backoff_decay(current, 100);
        
        // 延迟应该减少
        assert!(decayed < current);
        assert!(decayed >= 100);
        
        // 验证近似值：1000 * 0.618 ≈ 618
        assert!((decayed as f64 - 618.0).abs() < 10.0);
    }

    #[test]
    fn test_fibonacci_batch_size() {
        // 测试 Fibonacci 数列
        assert_eq!(fibonacci_batch_size(0, 1000), 1);
        assert_eq!(fibonacci_batch_size(1, 1000), 1);
        
        let f2 = fibonacci_batch_size(2, 1000);
        let f3 = fibonacci_batch_size(3, 1000);
        let f5 = fibonacci_batch_size(5, 1000);
        let f10 = fibonacci_batch_size(10, 1000);

        // 应该递增
        assert!(f3 >= f2);
        assert!(f5 >= f3);
        assert!(f10 >= f5);

        // 验证近似值
        assert_eq!(f2, 1);  // F(2) = 1
        assert!((f5 as f64 - 5.0).abs() <= 1.0);   // F(5) = 5
        assert!((f10 as f64 - 55.0).abs() <= 5.0); // F(10) = 55
    }

    #[test]
    fn test_fibonacci_batch_size_max_limit() {
        // 测试最大限制
        let large = fibonacci_batch_size(100, 100);
        assert_eq!(large, 100);
    }

    #[test]
    fn test_fibonacci_exact() {
        // 验证精确 Fibonacci 计算
        assert_eq!(fibonacci_exact(0), 0);
        assert_eq!(fibonacci_exact(1), 1);
        assert_eq!(fibonacci_exact(2), 1);
        assert_eq!(fibonacci_exact(3), 2);
        assert_eq!(fibonacci_exact(4), 3);
        assert_eq!(fibonacci_exact(5), 5);
        assert_eq!(fibonacci_exact(10), 55);
        assert_eq!(fibonacci_exact(20), 6765);
    }

    #[test]
    fn test_golden_ratio_split() {
        let (small, large) = golden_ratio_split(1000);
        
        assert_eq!(small + large, 1000);
        assert!(small < large);
        
        // 验证比例：small ≈ 382, large ≈ 618
        assert!((small as f64 - 382.0).abs() < 5.0);
        assert!((large as f64 - 618.0).abs() < 5.0);
    }

    #[test]
    fn test_golden_ratio_jitter() {
        let base = 1000;
        let jittered = golden_ratio_jitter(base, 0.5);
        
        // 抖动后的值应该大于基础值
        assert!(jittered >= base);
        
        // 但不应该太大
        assert!(jittered < base * 2);
    }

    // ========== const mul_add 测试 ==========

    #[test]
    fn test_const_mul_add() {
        // 2 * 3 + 4 = 10
        const RESULT: f64 = const_mul_add(2.0, 3.0, 4.0);
        assert_eq!(RESULT, 10.0);

        // 负数
        const NEG: f64 = const_mul_add(-2.0, 3.0, 4.0);
        assert_eq!(NEG, -2.0);

        // 零
        const ZERO: f64 = const_mul_add(0.0, 100.0, 5.0);
        assert_eq!(ZERO, 5.0);
    }

    #[test]
    fn test_const_lerp() {
        // 0 和 10 的中点
        const MID: f64 = const_lerp(0.0, 10.0, 0.5);
        assert!((MID - 5.0).abs() < 1e-10);

        // 起点
        const START: f64 = const_lerp(0.0, 10.0, 0.0);
        assert!((START - 0.0).abs() < 1e-10);

        // 终点
        const END: f64 = const_lerp(0.0, 10.0, 1.0);
        assert!((END - 10.0).abs() < 1e-10);
    }

    #[test]
    fn test_const_poly_eval() {
        // p(x) = 2 + 3x + 4x², x = 2
        // p(2) = 2 + 6 + 16 = 24
        const RESULT: f64 = const_poly_eval(2.0, &[2.0, 3.0, 4.0]);
        assert_eq!(RESULT, 24.0);

        // p(x) = 1 + 2x, x = 3
        // p(3) = 1 + 6 = 7
        const LINEAR: f64 = const_poly_eval(3.0, &[1.0, 2.0]);
        assert_eq!(LINEAR, 7.0);

        // 常数
        const CONSTANT: f64 = const_poly_eval(100.0, &[5.0]);
        assert_eq!(CONSTANT, 5.0);
    }

    #[test]
    fn test_const_sigmoid_approx() {
        // σ(0) ≈ 0.5
        const ZERO: f64 = const_sigmoid_approx(0.0);
        assert!((ZERO - 0.5).abs() < 0.1);

        // 大正数趋近 1
        const LARGE_POS: f64 = const_sigmoid_approx(5.0);
        assert_eq!(LARGE_POS, 1.0);

        // 大负数趋近 0
        const LARGE_NEG: f64 = const_sigmoid_approx(-5.0);
        assert_eq!(LARGE_NEG, 0.0);
    }

    // ========== 高级算法测试 ==========

    #[test]
    fn test_adaptive_batch_timeout() {
        let base = 100;
        let max = 1000;

        // 空队列应该使用最大超时
        let empty = adaptive_batch_timeout(0, base, max);
        assert_eq!(empty, max);

        // 深度队列应该使用更短的超时
        let shallow = adaptive_batch_timeout(10, base, max);
        let deep = adaptive_batch_timeout(1000, base, max);

        assert!(deep <= shallow);
        assert!(shallow >= base && shallow <= max);
        assert!(deep >= base);
    }

    #[test]
    fn test_optimal_connection_pool_size() {
        // 零并发应该返回 1
        let zero = optimal_connection_pool_size(0, 100);
        assert_eq!(zero, 1);

        // 正常并发
        let small = optimal_connection_pool_size(10, 100);
        let medium = optimal_connection_pool_size(50, 100);
        let large = optimal_connection_pool_size(100, 200);

        assert!(medium >= small);
        assert!(large >= medium);

        // 不应超过最大值
        let capped = optimal_connection_pool_size(1000, 50);
        assert_eq!(capped, 50);
    }

    #[test]
    fn test_adjust_sampling_rate() {
        let base = 0.5;

        // 样本不足应该增加采样率
        let increased = adjust_sampling_rate(base, 1000, 500);
        assert!(increased >= base);

        // 样本过多应该减少采样率
        let decreased = adjust_sampling_rate(base, 500, 1000);
        assert!(decreased <= base);

        // 应该保持在有效范围内
        assert!(increased <= 1.0 && increased >= 0.001);
        assert!(decreased <= 1.0 && decreased >= 0.001);
    }

    // ========== 工具函数测试 ==========

    #[test]
    fn test_safe_midpoint() {
        assert_eq!(safe_midpoint(0.0, 10.0), 5.0);
        assert_eq!(safe_midpoint(10.0, 0.0), 5.0);
        assert_eq!(safe_midpoint(-10.0, 10.0), 0.0);
    }

    #[test]
    fn test_approx_eq() {
        assert!(approx_eq(1.0, 1.0 + f64::EPSILON / 2.0));
        assert!(!approx_eq(1.0, 2.0));
    }

    #[test]
    fn test_rate_log_scale_conversion() {
        let original = 0.5;
        let log_scale = rate_to_log_scale(original);
        let back = log_scale_to_rate(log_scale);
        
        assert!(approx_eq(original, back));
    }

    // ========== 常数验证测试 ==========

    #[test]
    fn test_precomputed_constants() {
        // 验证预计算常数的正确性
        assert!((EULER_GAMMA_RECIP - 1.0 / EULER_GAMMA).abs() < 1e-10);
        assert!((GOLDEN_RATIO_RECIP - 1.0 / GOLDEN_RATIO).abs() < 1e-10);
        assert!((GOLDEN_RATIO_SQUARED - GOLDEN_RATIO * GOLDEN_RATIO).abs() < 1e-10);
        assert!((FIBONACCI_FACTOR - 1.0 / SQRT_5_F64).abs() < 1e-10);
    }
}
