# OTLP Rust API 使用指南

## 概述

本指南提供了OTLP Rust库的完整API使用说明，包括基础用法、高级特性、最佳实践和故障排除。

## 快速开始

### 1. 添加依赖

在`Cargo.toml`中添加依赖：

```toml
[dependencies]
otlp = "0.1.0"
tokio = { version = "1.0", features = ["full"] }
serde = { version = "1.0", features = ["derive"] }
tracing = "0.1"
```

### 2. 基础使用

```rust
use otlp::{OtlpClient, OtlpConfig, TraceData, ErrorSeverity};
use std::collections::HashMap;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建OTLP配置
    let config = OtlpConfig::new()
        .with_endpoint("http://localhost:4317")
        .with_timeout(std::time::Duration::from_secs(30));

    // 创建OTLP客户端
    let client = OtlpClient::new(config)?;

    // 创建追踪数据
    let trace_data = TraceData {
        trace_id: "example-trace-id".to_string(),
        span_id: "example-span-id".to_string(),
        parent_span_id: None,
        name: "example-operation".to_string(),
        span_kind: otlp::data::SpanKind::Internal,
        start_time: 0,
        end_time: 1000000,
        status: otlp::data::SpanStatus::default(),
        attributes: HashMap::new(),
        events: vec![],
        links: vec![],
    };

    // 发送追踪数据
    client.export_trace(trace_data).await?;

    println!("追踪数据发送成功");
    Ok(())
}
```

## 核心API详解

### 1. 错误处理模块

#### 错误类型创建

```rust
use otlp::error::{OtlpError, ErrorSeverity, ErrorCategory};

// 创建网络错误
let network_error = OtlpError::Transport(
    otlp::error::TransportError::Connection {
        endpoint: "http://example.com".to_string(),
        reason: "Connection timeout".to_string(),
    }
);

// 检查错误属性
assert_eq!(network_error.severity(), ErrorSeverity::High);
assert_eq!(network_error.category(), ErrorCategory::Network);
assert!(network_error.is_retryable());

// 获取恢复建议
if let Some(suggestion) = network_error.recovery_suggestion() {
    println!("恢复建议: {}", suggestion);
}

// 获取错误上下文
let context = network_error.context();
println!("错误上下文: {:?}", context);
```

#### 错误处理最佳实践

```rust
use otlp::error::{OtlpError, Result};

async fn handle_operation() -> Result<String> {
    match risky_operation().await {
        Ok(result) => Ok(result),
        Err(err) => {
            // 检查是否可重试
            if err.is_retryable() {
                // 执行重试逻辑
                retry_operation().await
            } else {
                // 记录错误并返回
                tracing::error!("操作失败: {}", err);
                Err(err)
            }
        }
    }
}

async fn retry_operation() -> Result<String> {
    let mut attempts = 0;
    let max_attempts = 3;
    
    while attempts < max_attempts {
        match risky_operation().await {
            Ok(result) => return Ok(result),
            Err(err) if err.is_retryable() => {
                attempts += 1;
                let delay = std::time::Duration::from_millis(100 * attempts);
                tokio::time::sleep(delay).await;
                continue;
            }
            Err(err) => return Err(err),
        }
    }
    
    Err(OtlpError::Internal("重试次数耗尽".to_string()))
}
```

### 2. 机器学习错误预测

#### 初始化预测系统

```rust
use otlp::ml_error_prediction::{MLErrorPrediction, MLPredictionConfig, SystemContext};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建ML预测配置
    let config = MLPredictionConfig::default();
    
    // 初始化预测系统
    let predictor = MLErrorPrediction::new(config)?;
    
    // 构建系统上下文
    let context = SystemContext {
        timestamp: std::time::SystemTime::now(),
        cpu_usage: 0.8,
        memory_usage: 0.9,
        system_load: 2.5,
        active_services: 10,
        network_latency: std::time::Duration::from_millis(500),
        error_history: vec![],
        service_health: std::collections::HashMap::new(),
        resource_metrics: otlp::ml_error_prediction::ResourceMetrics {
            cpu_cores: 4,
            total_memory: 8192,
            available_memory: 1024,
            disk_usage: 0.7,
            network_bandwidth: 1000,
        },
    };
    
    // 进行错误预测
    let prediction = predictor.predict_error_probability(&context).await?;
    
    println!("错误概率: {:.2}%", prediction.probability * 100.0);
    println!("置信度: {:.2}%", prediction.confidence * 100.0);
    println!("推荐措施: {:?}", prediction.recommended_actions);
    
    Ok(())
}
```

#### 模型训练和更新

```rust
use otlp::ml_error_prediction::{ErrorSample, PredictionFeedback, ActualOutcome};

// 训练模型
async fn train_model(predictor: &MLErrorPrediction) -> Result<()> {
    let training_data = vec![
        ErrorSample {
            id: "sample-1".to_string(),
            timestamp: std::time::SystemTime::now(),
            context: create_sample_context(),
            actual_error: Some(create_sample_error()),
            predicted_error: None,
            prediction_accuracy: None,
        },
        // 更多训练样本...
    ];
    
    let result = predictor.train_model(&training_data).await?;
    println!("训练结果: {:?}", result);
    Ok(())
}

// 在线学习
async fn online_learning(predictor: &MLErrorPrediction) -> Result<()> {
    let feedback = PredictionFeedback {
        prediction_id: "prediction-123".to_string(),
        actual_outcome: ActualOutcome::ErrorOccurred(create_sample_error()),
        feedback_type: otlp::ml_error_prediction::FeedbackType::Negative,
        timestamp: std::time::SystemTime::now(),
        context: create_sample_context(),
    };
    
    predictor.online_learn(feedback).await?;
    Ok(())
}
```

### 3. 分布式协调

#### 初始化协调器

```rust
use otlp::distributed_coordination::{DistributedErrorCoordinator, DistributedConfig, DistributedError};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建分布式配置
    let config = DistributedConfig::default();
    
    // 初始化协调器
    let coordinator = DistributedErrorCoordinator::new(config)?;
    
    // 启动协调器
    coordinator.start().await?;
    
    // 加入集群
    coordinator.join_cluster("http://cluster.example.com:8080").await?;
    
    // 处理分布式错误
    let error = DistributedError {
        id: "error-001".to_string(),
        error_type: "network_timeout".to_string(),
        severity: otlp::error::ErrorSeverity::High,
        message: "Network timeout occurred".to_string(),
        source: "service-a".to_string(),
        context: std::collections::HashMap::new(),
        timestamp: std::time::SystemTime::now(),
        affected_services: vec!["service-a".to_string(), "service-b".to_string()],
        propagation_path: vec!["service-a".to_string()],
    };
    
    let result = coordinator.handle_distributed_error(error).await?;
    println!("协调结果: {:?}", result);
    
    // 获取集群状态
    let status = coordinator.get_cluster_status().await?;
    println!("集群状态: {:?}", status);
    
    Ok(())
}
```

#### 集群管理

```rust
// 获取集群状态
async fn monitor_cluster(coordinator: &DistributedErrorCoordinator) -> Result<()> {
    let status = coordinator.get_cluster_status().await?;
    
    println!("集群总节点数: {}", status.total_nodes);
    println!("活跃节点数: {}", status.active_nodes);
    println!("集群健康状态: {:?}", status.cluster_health);
    
    // 检查集群健康状态
    match status.cluster_health {
        otlp::distributed_coordination::ClusterHealth::Healthy => {
            println!("集群运行正常");
        }
        otlp::distributed_coordination::ClusterHealth::Degraded => {
            println!("集群性能下降，需要关注");
        }
        otlp::distributed_coordination::ClusterHealth::Unhealthy => {
            println!("集群不健康，需要立即处理");
        }
        _ => {
            println!("集群状态未知");
        }
    }
    
    Ok(())
}
```

### 4. 弹性机制

#### 使用弹性管理器

```rust
use otlp::resilience::{ResilienceManager, ResilienceConfig};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建弹性配置
    let config = ResilienceConfig::default();
    
    // 创建弹性管理器
    let manager = ResilienceManager::new(config);
    
    // 执行带弹性的操作
    let result = manager.execute_with_resilience("database_query", || {
        Box::pin(async move {
            // 模拟数据库查询操作
            tokio::time::sleep(std::time::Duration::from_millis(100)).await;
            Ok::<String, anyhow::Error>("查询结果".to_string())
        })
    }).await;
    
    match result {
        Ok(data) => println!("操作成功: {}", data),
        Err(err) => println!("操作失败: {}", err),
    }
    
    Ok(())
}
```

#### 自定义弹性配置

```rust
use otlp::resilience::{
    ResilienceConfig, RetryConfig, CircuitBreakerConfig, 
    TimeoutConfig, GracefulDegradationConfig
};

fn create_custom_resilience_config() -> ResilienceConfig {
    ResilienceConfig {
        retry: RetryConfig {
            max_attempts: 5,
            base_delay: std::time::Duration::from_millis(100),
            max_delay: std::time::Duration::from_secs(10),
            backoff_multiplier: 2.0,
            jitter: true,
            retryable_errors: vec![
                "timeout".to_string(),
                "connection_failed".to_string(),
                "rate_limited".to_string(),
            ],
        },
        circuit_breaker: CircuitBreakerConfig {
            failure_threshold: 10,
            recovery_timeout: std::time::Duration::from_secs(120),
            half_open_max_calls: 5,
            sliding_window_size: std::time::Duration::from_secs(60),
            minimum_calls: 20,
        },
        timeout: TimeoutConfig {
            connect_timeout: std::time::Duration::from_secs(10),
            read_timeout: std::time::Duration::from_secs(60),
            write_timeout: std::time::Duration::from_secs(60),
            operation_timeout: std::time::Duration::from_secs(120),
        },
        graceful_degradation: GracefulDegradationConfig {
            enabled: true,
            strategies: vec![
                otlp::resilience::DegradationStrategy::UseCache,
                otlp::resilience::DegradationStrategy::UseFallback,
                otlp::resilience::DegradationStrategy::ReduceQuality,
            ],
            trigger_conditions: vec![
                otlp::resilience::TriggerCondition::HighErrorRate { threshold: 0.5 },
                otlp::resilience::TriggerCondition::HighLatency {
                    threshold: std::time::Duration::from_secs(10),
                },
            ],
        },
        health_check: otlp::resilience::HealthCheckConfig::default(),
    }
}
```

### 5. 监控和指标

#### 设置监控系统

```rust
use otlp::monitoring::{ErrorMonitoringSystem, MonitoringConfig, AlertRule};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建监控配置
    let config = MonitoringConfig {
        collection_interval: std::time::Duration::from_secs(30),
        retention_period: std::time::Duration::from_hours(24),
        alert_enabled: true,
        alert_rules: vec![
            AlertRule {
                name: "high_error_rate".to_string(),
                condition: otlp::monitoring::AlertCondition::ErrorRateThreshold {
                    threshold: 0.1,
                    time_window: std::time::Duration::from_minutes(5),
                },
                severity: otlp::error::ErrorSeverity::High,
                enabled: true,
            },
        ],
    };
    
    // 创建监控系统
    let monitoring = ErrorMonitoringSystem::new(config)?;
    
    // 启动监控
    monitoring.start().await?;
    
    // 记录错误事件
    let error_event = otlp::monitoring::ErrorEvent {
        id: "error-001".to_string(),
        timestamp: std::time::SystemTime::now(),
        error_type: "database_connection".to_string(),
        severity: otlp::error::ErrorSeverity::High,
        source: "user-service".to_string(),
        message: "Database connection failed".to_string(),
        context: std::collections::HashMap::new(),
    };
    
    monitoring.record_error(error_event).await?;
    
    // 获取监控指标
    let metrics = monitoring.get_metrics().await?;
    println!("监控指标: {:?}", metrics);
    
    Ok(())
}
```

## 高级用法

### 1. 自定义错误类型

```rust
use otlp::error::{OtlpError, ErrorSeverity, ErrorCategory};

// 定义自定义错误类型
#[derive(Debug, thiserror::Error)]
pub enum CustomError {
    #[error("业务逻辑错误: {0}")]
    BusinessLogic(String),
    
    #[error("外部服务错误: {service} - {reason}")]
    ExternalService { service: String, reason: String },
}

// 实现错误转换
impl From<CustomError> for OtlpError {
    fn from(err: CustomError) -> Self {
        match err {
            CustomError::BusinessLogic(msg) => {
                OtlpError::BusinessLogic(msg)
            }
            CustomError::ExternalService { service, reason } => {
                OtlpError::DependencyService { service, reason }
            }
        }
    }
}

// 使用自定义错误
async fn business_operation() -> Result<String, CustomError> {
    // 业务逻辑
    if some_condition() {
        Err(CustomError::BusinessLogic("业务条件不满足".to_string()))
    } else {
        Ok("操作成功".to_string())
    }
}
```

### 2. 自定义传输协议

```rust
use otlp::transport::{Transport, TransportFactory};

// 实现自定义传输协议
pub struct CustomTransport {
    endpoint: String,
    // 其他配置
}

impl Transport for CustomTransport {
    async fn send(&self, data: &[u8]) -> Result<(), otlp::error::OtlpError> {
        // 自定义发送逻辑
        println!("发送数据到: {}", self.endpoint);
        Ok(())
    }
}

// 注册自定义传输协议
pub struct CustomTransportFactory;

impl TransportFactory for CustomTransportFactory {
    fn create_transport(&self, endpoint: &str) -> Result<Box<dyn Transport>, otlp::error::OtlpError> {
        Ok(Box::new(CustomTransport {
            endpoint: endpoint.to_string(),
        }))
    }
}
```

### 3. 插件系统

```rust
use otlp::processor::{OtlpProcessor, ProcessingConfig};

// 定义自定义处理器
pub struct CustomProcessor {
    config: ProcessingConfig,
}

impl CustomProcessor {
    pub fn new(config: ProcessingConfig) -> Self {
        Self { config }
    }
    
    async fn custom_processing(&self, data: &[u8]) -> Result<Vec<u8>, otlp::error::OtlpError> {
        // 自定义处理逻辑
        let processed_data = data.to_vec(); // 示例处理
        Ok(processed_data)
    }
}

// 集成到OTLP处理器
impl OtlpProcessor for CustomProcessor {
    async fn process(&self, data: &[u8]) -> Result<Vec<u8>, otlp::error::OtlpError> {
        self.custom_processing(data).await
    }
    
    fn get_metrics(&self) -> otlp::processor::ProcessorMetrics {
        otlp::processor::ProcessorMetrics::default()
    }
}
```

## 性能优化

### 1. 批量处理

```rust
use otlp::client::OtlpClient;
use std::collections::VecDeque;

pub struct BatchProcessor {
    client: OtlpClient,
    batch_size: usize,
    batch_timeout: std::time::Duration,
    buffer: VecDeque<TraceData>,
}

impl BatchProcessor {
    pub async fn add_trace(&mut self, trace: TraceData) -> Result<()> {
        self.buffer.push_back(trace);
        
        if self.buffer.len() >= self.batch_size {
            self.flush().await?;
        }
        
        Ok(())
    }
    
    pub async fn flush(&mut self) -> Result<()> {
        if self.buffer.is_empty() {
            return Ok(());
        }
        
        let traces: Vec<TraceData> = self.buffer.drain(..).collect();
        
        // 批量发送
        for trace in traces {
            self.client.export_trace(trace).await?;
        }
        
        Ok(())
    }
}
```

### 2. 连接池优化

```rust
use std::sync::Arc;
use tokio::sync::RwLock;

pub struct ConnectionPool {
    connections: Arc<RwLock<Vec<Connection>>>,
    max_connections: usize,
}

impl ConnectionPool {
    pub async fn get_connection(&self) -> Result<Connection, otlp::error::OtlpError> {
        let mut connections = self.connections.write().await;
        
        // 查找可用连接
        if let Some(conn) = connections.iter_mut().find(|c| c.is_available()) {
            conn.mark_in_use();
            return Ok(conn.clone());
        }
        
        // 创建新连接
        if connections.len() < self.max_connections {
            let new_conn = Connection::new().await?;
            new_conn.mark_in_use();
            connections.push(new_conn.clone());
            return Ok(new_conn);
        }
        
        Err(otlp::error::OtlpError::Internal("连接池已满".to_string()))
    }
    
    pub async fn return_connection(&self, conn: Connection) {
        conn.mark_available();
    }
}
```

### 3. 缓存优化

```rust
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use std::time::{Duration, Instant};

pub struct CacheManager {
    cache: Arc<RwLock<HashMap<String, CacheEntry>>>,
    ttl: Duration,
}

struct CacheEntry {
    value: Vec<u8>,
    created_at: Instant,
}

impl CacheManager {
    pub async fn get(&self, key: &str) -> Option<Vec<u8>> {
        let cache = self.cache.read().await;
        
        if let Some(entry) = cache.get(key) {
            if entry.created_at.elapsed() < self.ttl {
                return Some(entry.value.clone());
            }
        }
        
        None
    }
    
    pub async fn set(&self, key: String, value: Vec<u8>) {
        let entry = CacheEntry {
            value,
            created_at: Instant::now(),
        };
        
        let mut cache = self.cache.write().await;
        cache.insert(key, entry);
        
        // 清理过期条目
        self.cleanup_expired().await;
    }
    
    async fn cleanup_expired(&self) {
        let mut cache = self.cache.write().await;
        let now = Instant::now();
        
        cache.retain(|_, entry| now.duration_since(entry.created_at) < self.ttl);
    }
}
```

## 故障排除

### 1. 常见错误

#### 连接错误

```rust
// 错误: 连接超时
match client.export_trace(trace).await {
    Err(OtlpError::Transport(TransportError::Connection { endpoint, reason })) => {
        println!("连接失败: {} - {}", endpoint, reason);
        // 检查网络连接和端点配置
    }
    _ => {}
}
```

#### 序列化错误

```rust
// 错误: 序列化失败
match client.export_trace(trace).await {
    Err(OtlpError::Serialization(err)) => {
        println!("序列化失败: {}", err);
        // 检查数据格式和字段类型
    }
    _ => {}
}
```

#### 配置错误

```rust
// 错误: 配置无效
match OtlpClient::new(config) {
    Err(OtlpError::Configuration(err)) => {
        println!("配置错误: {}", err);
        // 检查配置参数和格式
    }
    _ => {}
}
```

### 2. 调试技巧

#### 启用详细日志

```rust
use tracing::{info, debug, error};

// 在main函数中初始化日志
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 启用详细日志
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::DEBUG)
        .init();
    
    // 你的代码...
    Ok(())
}
```

#### 性能监控

```rust
use std::time::Instant;

async fn monitored_operation() -> Result<()> {
    let start = Instant::now();
    
    // 执行操作
    let result = some_operation().await?;
    
    let duration = start.elapsed();
    info!("操作耗时: {:?}", duration);
    
    Ok(result)
}
```

#### 错误统计

```rust
use std::sync::atomic::{AtomicU64, Ordering};

pub struct ErrorCounter {
    total_errors: AtomicU64,
    retryable_errors: AtomicU64,
    non_retryable_errors: AtomicU64,
}

impl ErrorCounter {
    pub fn record_error(&self, error: &OtlpError) {
        self.total_errors.fetch_add(1, Ordering::Relaxed);
        
        if error.is_retryable() {
            self.retryable_errors.fetch_add(1, Ordering::Relaxed);
        } else {
            self.non_retryable_errors.fetch_add(1, Ordering::Relaxed);
        }
    }
    
    pub fn get_stats(&self) -> (u64, u64, u64) {
        (
            self.total_errors.load(Ordering::Relaxed),
            self.retryable_errors.load(Ordering::Relaxed),
            self.non_retryable_errors.load(Ordering::Relaxed),
        )
    }
}
```

## 最佳实践

### 1. 错误处理

- 始终使用Result类型，避免panic
- 根据错误类型选择合适的处理策略
- 记录详细的错误上下文信息
- 实现适当的重试和恢复机制

### 2. 性能优化

- 使用批量处理减少网络开销
- 实现连接池复用连接
- 使用缓存减少重复计算
- 监控性能指标并持续优化

### 3. 配置管理

- 使用配置文件管理参数
- 支持环境变量覆盖
- 实现配置热更新
- 提供配置验证和默认值

### 4. 监控和告警

- 设置关键指标的监控
- 配置合理的告警阈值
- 建立故障处理流程
- 定期进行故障演练

### 5. 测试策略

- 编写单元测试覆盖核心逻辑
- 实现集成测试验证整体功能
- 进行性能测试验证性能指标
- 使用混沌工程测试故障场景

## 总结

本指南提供了OTLP Rust库的完整使用说明，包括基础用法、高级特性、性能优化和故障排除。通过遵循这些最佳实践，您可以构建高性能、可靠的分布式系统。

### 示例与运行

- 入门：`examples/simple_usage.rs` → `cargo run -p otlp --example simple_usage`
- 基础：`examples/simple_demo.rs` → `cargo run -p otlp --example simple_demo`
- 综合：`examples/comprehensive_usage.rs` → `cargo run -p otlp --example comprehensive_usage`
- 高级：`examples/advanced_patterns.rs` → `cargo run -p otlp --example advanced_patterns`
- 监控：`examples/monitoring_demo.rs` → `cargo run -p otlp --example monitoring_demo`
- 弹性：`examples/resilience_usage.rs` → `cargo run -p otlp --example resilience_usage`
- 分布式：`examples/distributed_coordination_demo.rs` → `cargo run -p otlp --example distributed_coordination_demo`
- 性能：`examples/performance_optimization_demo.rs` → `cargo run -p otlp --example performance_optimization_demo`

更多详细信息请参考：

- API 文档：`https://docs.rs/otlp`
- 仓库示例：`otlp/examples/`
