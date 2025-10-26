# Reliability API 参考

## 概述

本文档提供了可靠性框架 (`crates/reliability`) 的完整 API 参考。
该框架提供统一的错误处理、容错机制、运行时监控和环境适配功能。

## 核心 API

### 统一错误处理

#### UnifiedError

统一的错误类型，提供类型安全的错误处理。

```rust
#[derive(Debug, thiserror::Error)]
pub enum UnifiedError {
    /// 系统错误
    #[error("System error: {0}")]
    System(String),
    
    /// 网络错误
    #[error("Network error: {0}")]
    Network(#[from] reqwest::Error),
    
    /// 配置错误
    #[error("Configuration error: {0}")]
    Configuration(String),
    
    /// 超时错误
    #[error("Timeout error: {0}")]
    Timeout(String),
    
    /// 资源错误
    #[error("Resource error: {0}")]
    Resource(String),
    
    /// 验证错误
    #[error("Validation error: {0}")]
    Validation(String),
}
```

#### ErrorContext

错误上下文信息，提供丰富的错误上下文。

```rust
pub struct ErrorContext {
    /// 错误 ID
    pub error_id: String,
    
    /// 错误时间戳
    pub timestamp: SystemTime,
    
    /// 错误来源
    pub source: String,
    
    /// 错误严重程度
    pub severity: ErrorSeverity,
    
    /// 错误标签
    pub tags: HashMap<String, String>,
    
    /// 错误堆栈
    pub stack_trace: Option<String>,
    
    /// 相关指标
    pub metrics: HashMap<String, f64>,
}

pub enum ErrorSeverity {
    /// 低严重程度
    Low,
    /// 中等严重程度
    Medium,
    /// 高严重程度
    High,
    /// 严重程度
    Critical,
}
```

#### GlobalErrorMonitor

全局错误监控器，提供统一的错误监控和报告。

```rust
pub struct GlobalErrorMonitor {
    // 内部实现
}

impl GlobalErrorMonitor {
    /// 初始化全局错误监控器
    pub async fn init() -> Result<(), UnifiedError>;
    
    /// 关闭全局错误监控器
    pub async fn shutdown() -> Result<(), UnifiedError>;
    
    /// 记录错误
    pub async fn record_error(&self, error: UnifiedError, context: ErrorContext) -> Result<()>;
    
    /// 获取错误统计
    pub fn get_error_stats(&self) -> ErrorStats;
    
    /// 获取错误趋势
    pub fn get_error_trends(&self, duration: Duration) -> Vec<ErrorTrend>;
}
```

### 容错机制

#### CircuitBreaker

断路器模式实现，防止级联故障。

```rust
pub struct CircuitBreaker {
    /// 失败阈值
    failure_threshold: u32,
    
    /// 恢复超时
    recovery_timeout: Duration,
    
    /// 当前状态
    state: CircuitBreakerState,
    
    /// 失败计数
    failure_count: AtomicU32,
    
    /// 最后失败时间
    last_failure_time: AtomicSystemTime,
}

pub enum CircuitBreakerState {
    /// 关闭状态（正常）
    Closed,
    /// 打开状态（断路）
    Open,
    /// 半开状态（测试）
    HalfOpen,
}

impl CircuitBreaker {
    /// 创建新的断路器
    pub fn new(failure_threshold: u32, recovery_timeout: Duration) -> Self;
    
    /// 执行操作
    pub async fn execute<F, T, E>(&self, operation: F) -> Result<T, E>
    where
        F: Future<Output = Result<T, E>>,
        E: Into<UnifiedError>;
    
    /// 获取当前状态
    pub fn state(&self) -> CircuitBreakerState;
    
    /// 重置断路器
    pub fn reset(&self);
}
```

#### RetryPolicy

重试策略实现，支持多种重试模式。

```rust
pub struct RetryPolicy {
    /// 最大重试次数
    max_attempts: u32,
    
    /// 初始延迟
    initial_delay: Duration,
    
    /// 最大延迟
    max_delay: Duration,
    
    /// 延迟乘数
    multiplier: f64,
    
    /// 随机化因子
    jitter_factor: f64,
    
    /// 重试策略类型
    strategy: RetryStrategy,
}

pub enum RetryStrategy {
    /// 固定延迟
    Fixed,
    /// 指数退避
    ExponentialBackoff,
    /// 线性退避
    LinearBackoff,
    /// 自定义策略
    Custom(Box<dyn Fn(u32) -> Duration>),
}

impl RetryPolicy {
    /// 创建固定延迟重试策略
    pub fn fixed(max_attempts: u32, delay: Duration) -> Self;
    
    /// 创建指数退避重试策略
    pub fn exponential_backoff(
        max_attempts: u32,
        initial_delay: Duration,
        max_delay: Duration,
        multiplier: f64,
    ) -> Self;
    
    /// 执行重试操作
    pub async fn execute<F, T, E>(&self, operation: F) -> Result<T, E>
    where
        F: Fn() -> Future<Output = Result<T, E>>,
        E: Into<UnifiedError>;
}
```

#### Timeout

超时控制实现，提供多层超时保护。

```rust
pub struct Timeout {
    /// 超时时间
    duration: Duration,
    
    /// 超时处理策略
    strategy: TimeoutStrategy,
}

pub enum TimeoutStrategy {
    /// 立即失败
    FailFast,
    /// 优雅降级
    GracefulDegradation,
    /// 使用默认值
    UseDefault,
}

impl Timeout {
    /// 创建超时控制器
    pub fn new(duration: Duration, strategy: TimeoutStrategy) -> Self;
    
    /// 执行带超时的操作
    pub async fn execute<F, T>(&self, operation: F) -> Result<T, UnifiedError>
    where
        F: Future<Output = T>;
    
    /// 执行带超时和默认值的操作
    pub async fn execute_with_default<F, T>(
        &self,
        operation: F,
        default_value: T,
    ) -> Result<T, UnifiedError>
    where
        F: Future<Output = T>;
}
```

#### Bulkhead

舱壁模式实现，提供资源隔离。

```rust
pub struct Bulkhead {
    /// 最大并发数
    max_concurrency: usize,
    
    /// 当前并发数
    current_concurrency: AtomicUsize,
    
    /// 等待队列
    waiting_queue: Arc<Mutex<VecDeque<Waiter>>>,
}

impl Bulkhead {
    /// 创建舱壁
    pub fn new(max_concurrency: usize) -> Self;
    
    /// 执行操作
    pub async fn execute<F, T>(&self, operation: F) -> Result<T, UnifiedError>
    where
        F: Future<Output = T>;
    
    /// 获取当前并发数
    pub fn current_concurrency(&self) -> usize;
    
    /// 获取等待队列大小
    pub fn waiting_queue_size(&self) -> usize;
}
```

### 运行时监控

#### HealthChecker

健康检查器，提供系统健康状态监控。

```rust
pub struct HealthChecker {
    /// 健康检查配置
    config: HealthCheckConfig,
    
    /// 检查器注册表
    checkers: HashMap<String, Box<dyn HealthCheckTrait>>,
}

pub struct HealthCheckConfig {
    /// 检查间隔
    pub check_interval: Duration,
    
    /// 超时时间
    pub timeout: Duration,
    
    /// 失败阈值
    pub failure_threshold: u32,
}

pub trait HealthCheckTrait: Send + Sync {
    /// 执行健康检查
    fn check(&self) -> Future<Output = HealthCheckResult>;
    
    /// 获取检查名称
    fn name(&self) -> &str;
}

pub struct HealthCheckResult {
    /// 检查状态
    pub status: HealthStatus,
    
    /// 检查消息
    pub message: Option<String>,
    
    /// 检查持续时间
    pub duration: Duration,
    
    /// 检查详情
    pub details: HashMap<String, Value>,
}

pub enum HealthStatus {
    /// 健康
    Healthy,
    /// 不健康
    Unhealthy,
    /// 降级
    Degraded,
    /// 未知
    Unknown,
}

impl HealthChecker {
    /// 创建健康检查器
    pub fn new(config: HealthCheckConfig) -> Self;
    
    /// 注册健康检查
    pub fn register_checker(&mut self, name: String, checker: Box<dyn HealthCheckTrait>);
    
    /// 执行所有健康检查
    pub async fn check_all(&self) -> HashMap<String, HealthCheckResult>;
    
    /// 获取整体健康状态
    pub async fn get_overall_status(&self) -> HealthStatus;
}
```

#### PerformanceMonitor

性能监控器，提供系统性能指标监控。

```rust
pub struct PerformanceMonitor {
    /// 监控配置
    config: MonitoringConfig,
    
    /// 指标收集器
    collectors: HashMap<String, Box<dyn MetricCollector>>,
}

pub struct MonitoringConfig {
    /// 收集间隔
    pub collection_interval: Duration,
    
    /// 保留时间
    pub retention_period: Duration,
    
    /// 告警阈值
    pub alert_thresholds: HashMap<String, f64>,
}

pub trait MetricCollector: Send + Sync {
    /// 收集指标
    fn collect(&self) -> Future<Output = Vec<Metric>>;
    
    /// 获取收集器名称
    fn name(&self) -> &str;
}

pub struct Metric {
    /// 指标名称
    pub name: String,
    
    /// 指标值
    pub value: f64,
    
    /// 指标标签
    pub labels: HashMap<String, String>,
    
    /// 时间戳
    pub timestamp: SystemTime,
}

impl PerformanceMonitor {
    /// 创建性能监控器
    pub fn new(config: MonitoringConfig) -> Self;
    
    /// 注册指标收集器
    pub fn register_collector(&mut self, name: String, collector: Box<dyn MetricCollector>);
    
    /// 收集所有指标
    pub async fn collect_all(&self) -> HashMap<String, Vec<Metric>>;
    
    /// 获取性能报告
    pub async fn get_performance_report(&self) -> PerformanceReport;
}
```

#### ResourceMonitor

资源监控器，提供系统资源使用情况监控。

```rust
pub struct ResourceMonitor {
    /// 监控配置
    config: ResourceMonitoringConfig,
    
    /// 资源使用历史
    usage_history: VecDeque<ResourceUsage>,
}

pub struct ResourceMonitoringConfig {
    /// 监控间隔
    pub monitoring_interval: Duration,
    
    /// 历史保留数量
    pub history_size: usize,
    
    /// 告警阈值
    pub alert_thresholds: ResourceThresholds,
}

pub struct ResourceUsage {
    /// 时间戳
    pub timestamp: SystemTime,
    
    /// CPU 使用率
    pub cpu_usage: f64,
    
    /// 内存使用率
    pub memory_usage: f64,
    
    /// 磁盘使用率
    pub disk_usage: f64,
    
    /// 网络使用率
    pub network_usage: f64,
    
    /// 连接数
    pub connection_count: u32,
}

pub struct ResourceThresholds {
    /// CPU 告警阈值
    pub cpu_threshold: f64,
    
    /// 内存告警阈值
    pub memory_threshold: f64,
    
    /// 磁盘告警阈值
    pub disk_threshold: f64,
    
    /// 网络告警阈值
    pub network_threshold: f64,
}

impl ResourceMonitor {
    /// 创建资源监控器
    pub fn new(config: ResourceMonitoringConfig) -> Self;
    
    /// 开始监控
    pub async fn start_monitoring(&mut self);
    
    /// 停止监控
    pub async fn stop_monitoring(&mut self);
    
    /// 获取当前资源使用情况
    pub async fn get_current_usage(&self) -> ResourceUsage;
    
    /// 获取资源使用历史
    pub fn get_usage_history(&self) -> &VecDeque<ResourceUsage>;
    
    /// 检查资源告警
    pub fn check_alerts(&self) -> Vec<ResourceAlert>;
}
```

### 环境适配

#### RuntimeEnvironmentManager

运行时环境管理器，提供不同环境的适配。

```rust
pub struct RuntimeEnvironmentManager {
    /// 当前环境
    current_environment: RuntimeEnvironment,
    
    /// 环境适配器
    adapters: HashMap<RuntimeEnvironment, Box<dyn EnvironmentAdapter>>,
}

pub enum RuntimeEnvironment {
    /// 操作系统环境
    OS,
    /// 容器环境
    Container,
    /// Kubernetes 环境
    Kubernetes,
    /// 嵌入式环境
    Embedded,
    /// 边缘计算环境
    Edge,
    /// WebAssembly 环境
    WebAssembly,
}

pub trait EnvironmentAdapter: Send + Sync {
    /// 检测环境
    fn detect(&self) -> Future<Output = bool>;
    
    /// 获取环境信息
    fn get_info(&self) -> Future<Output = EnvironmentInfo>;
    
    /// 获取环境能力
    fn get_capabilities(&self) -> EnvironmentCapabilities;
}

pub struct EnvironmentInfo {
    /// 环境名称
    pub name: String,
    
    /// 环境版本
    pub version: String,
    
    /// 环境特性
    pub features: Vec<String>,
    
    /// 资源限制
    pub resource_limits: ResourceLimits,
}

pub struct EnvironmentCapabilities {
    /// 支持的功能
    pub supported_features: Vec<String>,
    
    /// 性能特性
    pub performance_characteristics: PerformanceCharacteristics,
    
    /// 限制
    pub limitations: Vec<String>,
}

impl RuntimeEnvironmentManager {
    /// 创建环境管理器
    pub fn new() -> Self;
    
    /// 自动检测环境
    pub async fn auto_detect(&mut self) -> RuntimeEnvironment;
    
    /// 设置环境
    pub fn set_environment(&mut self, environment: RuntimeEnvironment);
    
    /// 获取当前环境
    pub fn current_environment(&self) -> &RuntimeEnvironment;
    
    /// 获取环境信息
    pub async fn get_environment_info(&self) -> EnvironmentInfo;
    
    /// 获取环境能力
    pub fn get_environment_capabilities(&self) -> EnvironmentCapabilities;
}
```

### 混沌工程

#### FaultInjector

故障注入器，用于混沌工程测试。

```rust
pub struct FaultInjector {
    /// 故障配置
    config: FaultConfig,
    
    /// 故障历史
    fault_history: VecDeque<FaultRecord>,
}

pub struct FaultConfig {
    /// 故障类型
    pub fault_type: FaultType,
    
    /// 故障概率
    pub probability: f64,
    
    /// 故障持续时间
    pub duration: Duration,
    
    /// 故障影响范围
    pub scope: FaultScope,
}

pub enum FaultType {
    /// 网络延迟
    NetworkLatency(Duration),
    /// 网络丢包
    NetworkPacketLoss(f64),
    /// 服务不可用
    ServiceUnavailable,
    /// 资源耗尽
    ResourceExhaustion,
    /// 随机故障
    RandomFailure,
}

pub enum FaultScope {
    /// 全局
    Global,
    /// 特定服务
    Service(String),
    /// 特定实例
    Instance(String),
    /// 特定操作
    Operation(String),
}

impl FaultInjector {
    /// 创建故障注入器
    pub fn new(config: FaultConfig) -> Self;
    
    /// 注入故障
    pub async fn inject_fault(&mut self) -> Result<FaultResult, UnifiedError>;
    
    /// 停止故障注入
    pub async fn stop_fault_injection(&mut self);
    
    /// 获取故障历史
    pub fn get_fault_history(&self) -> &VecDeque<FaultRecord>;
    
    /// 分析故障影响
    pub async fn analyze_fault_impact(&self) -> FaultImpactAnalysis;
}
```

## 使用示例

### 基本错误处理

```rust
use reliability::prelude::*;

#[tokio::main]
async fn main() -> Result<(), UnifiedError> {
    // 初始化错误监控
    GlobalErrorMonitor::init().await?;
    
    // 创建错误上下文
    let context = ErrorContext {
        error_id: "ERR-001".to_string(),
        timestamp: SystemTime::now(),
        source: "my-service".to_string(),
        severity: ErrorSeverity::Medium,
        tags: HashMap::new(),
        stack_trace: None,
        metrics: HashMap::new(),
    };
    
    // 记录错误
    let error = UnifiedError::System("Something went wrong".to_string());
    GlobalErrorMonitor::record_error(error, context).await?;
    
    Ok(())
}
```

### 容错机制使用

```rust
use reliability::prelude::*;

#[tokio::main]
async fn main() -> Result<(), UnifiedError> {
    // 创建断路器
    let circuit_breaker = CircuitBreaker::new(5, Duration::from_secs(60));
    
    // 创建重试策略
    let retry_policy = RetryPolicy::exponential_backoff(
        3,
        Duration::from_millis(100),
        Duration::from_secs(5),
        2.0,
    );
    
    // 创建超时控制器
    let timeout = Timeout::new(Duration::from_secs(30), TimeoutStrategy::FailFast);
    
    // 执行带容错的操作
    let result = circuit_breaker
        .execute(|| async {
            timeout.execute(|| async {
                retry_policy.execute(|| async {
                    // 你的业务逻辑
                    Ok::<String, UnifiedError>("success".to_string())
                }).await
            }).await
        })
        .await?;
    
    println!("操作结果: {}", result);
    Ok(())
}
```

### 健康检查使用

```rust
use reliability::prelude::*;

#[tokio::main]
async fn main() -> Result<(), UnifiedError> {
    // 创建健康检查配置
    let config = HealthCheckConfig {
        check_interval: Duration::from_secs(30),
        timeout: Duration::from_secs(5),
        failure_threshold: 3,
    };
    
    // 创建健康检查器
    let mut health_checker = HealthChecker::new(config);
    
    // 注册自定义健康检查
    health_checker.register_checker(
        "database".to_string(),
        Box::new(DatabaseHealthCheck::new()),
    );
    
    // 执行健康检查
    let results = health_checker.check_all().await;
    
    for (name, result) in results {
        println!("{}: {:?}", name, result.status);
    }
    
    Ok(())
}
```

### 环境适配使用

```rust
use reliability::prelude::*;

#[tokio::main]
async fn main() -> Result<(), UnifiedError> {
    // 创建环境管理器
    let mut env_manager = RuntimeEnvironmentManager::new();
    
    // 自动检测环境
    let environment = env_manager.auto_detect().await;
    println!("检测到环境: {:?}", environment);
    
    // 获取环境信息
    let info = env_manager.get_environment_info().await;
    println!("环境信息: {:?}", info);
    
    // 获取环境能力
    let capabilities = env_manager.get_environment_capabilities();
    println!("环境能力: {:?}", capabilities);
    
    Ok(())
}
```

### 混沌工程使用

```rust
use reliability::prelude::*;

#[tokio::main]
async fn main() -> Result<(), UnifiedError> {
    // 创建故障配置
    let config = FaultConfig {
        fault_type: FaultType::NetworkLatency(Duration::from_millis(100)),
        probability: 0.1,
        duration: Duration::from_secs(60),
        scope: FaultScope::Global,
    };
    
    // 创建故障注入器
    let mut fault_injector = FaultInjector::new(config);
    
    // 注入故障
    let result = fault_injector.inject_fault().await?;
    println!("故障注入结果: {:?}", result);
    
    // 分析故障影响
    let analysis = fault_injector.analyze_fault_impact().await;
    println!("故障影响分析: {:?}", analysis);
    
    Ok(())
}
```

## 配置示例

### 错误处理配置

```toml
[error_handling]
# 错误监控配置
monitoring_enabled = true
error_retention_days = 30
alert_threshold = 10

# 错误恢复配置
auto_recovery_enabled = true
recovery_timeout = "30s"
max_recovery_attempts = 3
```

### 容错机制配置

```toml
[fault_tolerance]
# 断路器配置
circuit_breaker_enabled = true
failure_threshold = 5
recovery_timeout = "60s"

# 重试配置
retry_enabled = true
max_attempts = 3
initial_delay = "100ms"
max_delay = "5s"
multiplier = 2.0

# 超时配置
timeout_enabled = true
default_timeout = "30s"
```

### 监控配置

```toml
[monitoring]
# 健康检查配置
health_check_enabled = true
check_interval = "30s"
timeout = "5s"
failure_threshold = 3

# 性能监控配置
performance_monitoring_enabled = true
collection_interval = "10s"
retention_period = "24h"

# 资源监控配置
resource_monitoring_enabled = true
monitoring_interval = "5s"
cpu_threshold = 80.0
memory_threshold = 85.0
```

---

*本文档最后更新: 2025年10月20日*-
