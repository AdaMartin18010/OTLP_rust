# OTLP Rust API 文档

## 概述

本文档详细介绍了OTLP Rust项目的API接口、使用方法和最佳实践。
该项目是一个基于Rust 1.90的OpenTelemetry协议实现，提供了完整的遥测数据收集、处理和传输功能。

## 目录

1. [核心API](#核心api)
2. [错误处理系统](#错误处理系统)
3. [机器学习集成](#机器学习集成)
4. [监控系统](#监控系统)
5. [性能优化](#性能优化)
6. [使用示例](#使用示例)
7. [最佳实践](#最佳实践)

## 核心API

### OtlpClient

`OtlpClient` 是OTLP协议的主要客户端接口，支持同步和异步操作。

```rust
use otlp::{OtlpClient, OtlpConfig, TransportProtocol};

// 创建客户端
let config = OtlpConfig::default()
    .with_endpoint("http://localhost:4317")
    .with_protocol(TransportProtocol::Http)
    .with_service("my-service", "1.0.0");

let client = OtlpClient::new(config).await?;
```

#### 主要方法

- `new(config: OtlpConfig) -> Result<Self>`: 创建新的OTLP客户端
- `initialize() -> Result<()>`: 初始化客户端连接
- `send_trace(name: &str) -> Result<TraceBuilder>`: 发送追踪数据
- `send_metric(name: &str, value: f64) -> Result<MetricBuilder>`: 发送指标数据
- `send_log(message: &str, severity: LogSeverity) -> Result<LogBuilder>`: 发送日志数据
- `shutdown() -> Result<()>`: 关闭客户端

### 数据构建器

#### TraceBuilder

用于构建和发送追踪数据：

```rust
let trace_builder = client.send_trace("user-operation").await?;
let result = trace_builder
    .with_attribute("user.id", "12345")
    .with_attribute("operation.type", "login")
    .with_numeric_attribute("duration", 150.0)
    .with_status(StatusCode::Ok, Some("success".to_string()))
    .finish()
    .await?;
```

#### MetricBuilder

用于构建和发送指标数据：

```rust
let metric_builder = client.send_metric("request_count", 1.0).await?;
let result = metric_builder
    .with_label("service", "api")
    .with_label("method", "GET")
    .with_description("Total number of requests")
    .with_unit("count")
    .send()
    .await?;
```

#### LogBuilder

用于构建和发送日志数据：

```rust
let log_builder = client.send_log("User login successful", LogSeverity::Info).await?;
let result = log_builder
    .with_attribute("user.id", "12345")
    .with_attribute("ip.address", "192.168.1.1")
    .with_trace_context("trace-id", "span-id")
    .send()
    .await?;
```

## 错误处理系统

### 错误类型

项目提供了全面的错误处理系统，包含100+种错误类型：

```rust
use otlp::error::{OtlpError, ErrorCategory, ErrorSeverity};

// 网络错误
let network_error = OtlpError::Transport(TransportError::Connection {
    endpoint: "http://example.com".to_string(),
    reason: "Connection refused".to_string(),
});

// 机器学习错误
let ml_error = OtlpError::MachineLearning {
    model_type: "neural_network".to_string(),
    reason: "Model training failed".to_string(),
};

// 微服务错误
let microservice_error = OtlpError::Microservice {
    service_name: "user-service".to_string(),
    reason: "Service unavailable".to_string(),
};
```

### 错误分类

错误按以下类别进行分类：

- **网络错误** (Network): 网络连接、传输相关错误
- **数据错误** (Data): 数据格式、验证相关错误
- **配置错误** (Configuration): 配置参数相关错误
- **处理错误** (Processing): 数据处理相关错误
- **导出错误** (Export): 数据导出相关错误
- **性能错误** (Performance): 性能相关错误
- **并发错误** (Concurrency): 并发控制相关错误
- **资源错误** (Resource): 资源管理相关错误
- **兼容性错误** (Compatibility): 版本兼容性相关错误
- **系统错误** (System): 系统级错误
- **业务错误** (Business): 业务逻辑相关错误
- **安全错误** (Security): 安全相关错误
- **依赖错误** (Dependency): 外部依赖相关错误
- **机器学习错误** (ML): ML模型相关错误
- **监控错误** (Monitoring): 监控系统相关错误
- **分布式错误** (Distributed): 分布式协调相关错误
- **边缘计算错误** (Edge): 边缘计算相关错误
- **区块链错误** (Blockchain): 区块链集成相关错误
- **微服务错误** (Microservice): 微服务相关错误
- **缓存错误** (Cache): 缓存系统相关错误
- **数据库错误** (Database): 数据库相关错误
- **文件系统错误** (FileSystem): 文件系统相关错误
- **负载均衡错误** (LoadBalancing): 负载均衡相关错误
- **服务发现错误** (ServiceDiscovery): 服务发现相关错误
- **健康检查错误** (Health): 健康检查相关错误
- **指标错误** (Metrics): 指标收集相关错误
- **告警错误** (Alerting): 告警系统相关错误
- **版本控制错误** (VersionControl): 版本控制相关错误
- **部署错误** (Deployment): 部署相关错误
- **备份错误** (Backup): 备份相关错误
- **恢复错误** (Recovery): 恢复相关错误
- **迁移错误** (Migration): 迁移相关错误
- **升级错误** (Upgrade): 升级相关错误
- **降级错误** (Downgrade): 降级相关错误
- **扩展错误** (Scaling): 扩展相关错误
- **压缩错误** (Compression): 压缩相关错误
- **编码错误** (Encoding): 编码相关错误
- **转换错误** (Conversion): 数据转换相关错误
- **验证错误** (Validation): 数据验证相关错误
- **会话错误** (Session): 会话管理相关错误
- **连接错误** (Connection): 连接管理相关错误
- **事务错误** (Transaction): 事务管理相关错误
- **内存错误** (Memory): 内存管理相关错误
- **类型错误** (Type): 类型系统相关错误
- **设计模式错误** (Design): 设计模式相关错误

### 错误严重程度

错误按严重程度分为四个级别：

- **低** (Low): 不影响系统正常运行
- **中等** (Medium): 可能影响部分功能
- **高** (High): 严重影响系统功能
- **严重** (Critical): 系统不可用

### 错误处理最佳实践

```rust
use otlp::error::{OtlpError, Result};

async fn handle_operation() -> Result<()> {
    match some_operation().await {
        Ok(result) => Ok(result),
        Err(error) => {
            // 记录错误
            tracing::error!("操作失败: {}", error);
            
            // 检查错误类型和严重程度
            match error.category() {
                ErrorCategory::Network => {
                    // 网络错误处理
                    if error.is_retryable() {
                        // 可重试错误
                        retry_operation().await
                    } else {
                        // 不可重试错误
                        Err(error)
                    }
                }
                ErrorCategory::Configuration => {
                    // 配置错误处理
                    tracing::error!("配置错误: {}", error);
                    Err(error)
                }
                _ => {
                    // 其他错误处理
                    Err(error)
                }
            }
        }
    }
}
```

## 机器学习集成

### MLErrorPrediction

机器学习错误预测系统提供了智能的错误预测和预防功能：

```rust
use otlp::ml_error_prediction::{
    MLErrorPrediction, MLPredictionConfig, SystemContext
};

// 创建ML预测系统
let config = MLPredictionConfig {
    model: MLModelConfig {
        model_type: ModelType::RandomForest,
        parameters: HashMap::new(),
        training_data_size: 1000,
        validation_split: 0.2,
        learning_rate: 0.01,
        max_iterations: 1000,
    },
    // ... 其他配置
};

let ml_system = MLErrorPrediction::new(config)?;

// 创建系统上下文
let context = SystemContext {
    timestamp: SystemTime::now(),
    cpu_usage: 0.75,
    memory_usage: 0.60,
    system_load: 2.5,
    active_services: 15,
    network_latency: Duration::from_millis(50),
    error_history: vec![],
    service_health: HashMap::new(),
    resource_metrics: HashMap::new(),
};

// 预测错误概率
let prediction = ml_system.predict_error_probability(&context).await?;
println!("错误概率: {:.2}%", prediction.probability * 100.0);
println!("置信度: {:.2}%", prediction.confidence * 100.0);
```

### 预测结果

预测结果包含以下信息：

- `probability`: 错误发生概率 (0.0-1.0)
- `confidence`: 预测置信度 (0.0-1.0)
- `error_types`: 可能发生的错误类型
- `time_window`: 预计错误发生时间窗口
- `explanation`: 预测解释
- `recommended_actions`: 推荐的预防措施
- `feature_importance`: 特征重要性
- `anomaly_score`: 异常分数
- `trend_analysis`: 趋势分析结果
- `ensemble_confidence`: 集成模型置信度

### 反馈机制

系统支持预测反馈，用于改进模型性能：

```rust
use otlp::ml_error_prediction::PredictionFeedback;

let feedback = PredictionFeedback {
    prediction_id: "pred-001".to_string(),
    timestamp: SystemTime::now(),
    actual_outcome: true,
    feedback_type: "accuracy".to_string(),
    context: context.clone(),
};

ml_system.process_feedback(&feedback).await?;
```

## 监控系统

### ErrorMonitoringSystem

错误监控系统提供实时错误监控和告警功能：

```rust
use otlp::monitoring::{ErrorMonitoringSystem, MonitoringConfig};

let config = MonitoringConfig {
    collection_interval: Duration::from_secs(30),
    alert_thresholds: HashMap::new(),
    retention_period: Duration::from_secs(86400 * 7), // 7天
};

let monitoring = ErrorMonitoringSystem::new(config)?;

// 开始监控
monitoring.start_monitoring().await?;

// 添加告警规则
let alert_rule = AlertRule {
    name: "high_error_rate".to_string(),
    condition: AlertCondition::ErrorRateAbove { threshold: 0.05 },
    severity: AlertSeverity::High,
    enabled: true,
};

monitoring.add_alert_rule(alert_rule).await?;
```

## 性能优化

### PerformanceOptimizer

性能优化器提供系统性能监控和优化建议：

```rust
use otlp::performance_optimization::PerformanceOptimizer;

let optimizer = PerformanceOptimizer::new()?;

// 获取性能指标
let metrics = optimizer.get_performance_metrics().await?;
println!("CPU使用率: {:.2}%", metrics.cpu_usage * 100.0);
println!("内存使用率: {:.2}%", metrics.memory_usage * 100.0);

// 获取优化建议
let suggestions = optimizer.get_optimization_suggestions().await?;
for suggestion in suggestions {
    println!("优化建议: {}", suggestion.description);
}
```

## 使用示例

### 基本使用

```rust
use otlp::{OtlpClient, OtlpConfig, TransportProtocol, LogSeverity};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建OTLP客户端
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Http)
        .with_service("example-service", "1.0.0")
        .with_request_timeout(Duration::from_secs(30));

    let client = OtlpClient::new(config).await?;
    client.initialize().await?;

    // 发送追踪数据
    let trace_result = client
        .send_trace("user-operation")
        .await?
        .with_attribute("user.id", "12345")
        .with_attribute("operation.type", "login")
        .with_numeric_attribute("duration", 150.0)
        .finish()
        .await?;

    println!("追踪发送结果: {:?}", trace_result);

    // 发送指标数据
    let metric_result = client
        .send_metric("request_count", 1.0)
        .await?
        .with_label("service", "api")
        .with_label("method", "GET")
        .send()
        .await?;

    println!("指标发送结果: {:?}", metric_result);

    // 发送日志数据
    let log_result = client
        .send_log("User login successful", LogSeverity::Info)
        .await?
        .with_attribute("user.id", "12345")
        .send()
        .await?;

    println!("日志发送结果: {:?}", log_result);

    // 关闭客户端
    client.shutdown().await?;

    Ok(())
}
```

### 示例与运行

- 入门示例：`examples/simple_usage.rs`
  - 运行：`cargo run -p otlp --example simple_usage`
- 基础演示：`examples/simple_demo.rs`
  - 运行：`cargo run -p otlp --example simple_demo`
- 综合用法：`examples/comprehensive_usage.rs`, `examples/comprehensive_demo.rs`
  - 运行：`cargo run -p otlp --example comprehensive_usage`
- 高级模式：`examples/advanced_patterns.rs`, `examples/advanced_microservices_demo.rs`
  - 运行：`cargo run -p otlp --example advanced_patterns`
- 可靠性与弹性：`examples/resilience_usage.rs`, `examples/microservices_demo.rs`
  - 运行：`cargo run -p otlp --example resilience_usage`
- 监控与告警：`examples/monitoring_demo.rs`
  - 运行：`cargo run -p otlp --example monitoring_demo`
- 性能基准与优化：`examples/performance_benchmarks.rs`, `examples/performance_optimization_demo.rs`
  - 运行：`cargo run -p otlp --example performance_optimization_demo`
- 分布式协调：`examples/distributed_coordination_demo.rs`
  - 运行：`cargo run -p otlp --example distributed_coordination_demo`

### 错误处理示例

```rust
use otlp::error::{OtlpError, ErrorCategory, Result};

async fn robust_operation() -> Result<()> {
    let mut retry_count = 0;
    let max_retries = 3;

    loop {
        match perform_operation().await {
            Ok(result) => return Ok(result),
            Err(error) => {
                retry_count += 1;
                
                // 检查错误类型和可重试性
                if error.is_retryable() && retry_count <= max_retries {
                    let delay = Duration::from_millis(1000 * retry_count);
                    tokio::time::sleep(delay).await;
                    continue;
                }
                
                // 记录错误信息
                tracing::error!(
                    "操作失败 (尝试 {}/{}): {}",
                    retry_count,
                    max_retries,
                    error
                );
                
                // 获取恢复建议
                if let Some(suggestion) = error.recovery_suggestion() {
                    tracing::info!("恢复建议: {}", suggestion);
                }
                
                return Err(error);
            }
        }
    }
}
```

### ML预测示例

```rust
use otlp::ml_error_prediction::{MLErrorPrediction, SystemContext};

async fn predictive_monitoring() -> Result<()> {
    let ml_system = MLErrorPrediction::new(MLPredictionConfig::default())?;
    
    // 模拟系统监控循环
    loop {
        let context = collect_system_context().await;
        let prediction = ml_system.predict_error_probability(&context).await?;
        
        if prediction.probability > 0.8 {
            tracing::warn!(
                "高错误概率预警: {:.2}% (置信度: {:.2}%)",
                prediction.probability * 100.0,
                prediction.confidence * 100.0
            );
            
            // 执行预防措施
            for action in prediction.recommended_actions {
                tracing::info!("执行预防措施: {}", action.description);
                execute_preventive_action(&action).await?;
            }
        }
        
        tokio::time::sleep(Duration::from_secs(60)).await;
    }
}
```

## 最佳实践

### 1. 错误处理

- 始终检查错误类型和严重程度
- 使用适当的重试策略
- 记录详细的错误信息
- 提供有意义的错误消息

### 2. 性能优化

- 使用连接池管理网络连接
- 批量发送数据以减少网络开销
- 合理设置超时时间
- 监控系统资源使用情况

### 3. 监控和告警

- 设置合理的告警阈值
- 使用多层次的监控策略
- 定期检查监控系统健康状态
- 建立完善的告警响应流程

### 4. 机器学习集成

- 定期更新训练数据
- 监控模型性能指标
- 使用集成学习提高预测准确性
- 建立反馈循环改进模型

### 5. 配置管理

- 使用环境变量管理配置
- 提供合理的默认值
- 支持配置热更新
- 验证配置参数的有效性

## 总结

OTLP Rust项目提供了一个完整的、高性能的OpenTelemetry协议实现，具有以下特点：

- **全面的错误处理**: 100+种错误类型，智能分类和恢复建议
- **智能预测**: 基于机器学习的错误预测和预防
- **高性能**: 基于Rust 1.90的零拷贝优化
- **易用性**: 简洁的API设计和丰富的文档
- **可扩展性**: 模块化设计，支持自定义扩展
- **生产就绪**: 完善的监控、告警和性能优化功能

通过遵循本文档中的最佳实践，您可以充分利用OTLP Rust项目的强大功能，构建可靠、高性能的分布式系统。
