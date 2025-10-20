# OTLP Rust API 参考文档

## 目录

1. [核心API](#核心api)
2. [传输层API](#传输层api)
3. [数据处理API](#数据处理api)
4. [分布式协调API](#分布式协调api)
5. [机器学习API](#机器学习api)
6. [监控API](#监控api)
7. [配置API](#配置api)
8. [工具API](#工具api)

## 示例与运行

- 简单示例：`examples/simple_usage.rs` → `cargo run -p otlp --example simple_usage`
- 综合示例：`examples/comprehensive_demo.rs` → `cargo run -p otlp --example comprehensive_demo`
- 高级模式：`examples/advanced_microservices_demo.rs` → `cargo run -p otlp --example advanced_microservices_demo`

## 核心API

### OtlpClient

OTLP客户端的主要入口点，提供统一的API接口。

```rust
use otlp::{OtlpClient, OtlpClientBuilder, OtlpConfig};

// 构建客户端
let client = OtlpClientBuilder::new()
    .with_endpoint("http://collector:4317")
    .with_timeout(Duration::from_secs(30))
    .with_retry_config(RetryConfig {
        max_attempts: 3,
        base_delay: Duration::from_millis(100),
        ..Default::default()
    })
    .build()
    .await?;

// 发送追踪数据
let span = client.start_span("operation_name", |span| {
    span.set_attribute("key", "value");
    span.set_attribute("number", 42);
});

// 发送指标数据
client.record_metric("request_count", 1.0, vec![
    ("method", "GET"),
    ("status", "200"),
]).await?;

// 发送日志数据
client.emit_log(LogLevel::Info, "Application started", vec![
    ("service", "my-service"),
    ("version", "1.0.0"),
]).await?;
```

#### 主要方法

```rust
impl OtlpClient {
    // 创建span
    pub fn start_span<F>(&self, name: &str, f: F) -> Span
    where F: FnOnce(&mut Span);

    // 异步创建span
    pub async fn start_span_async<F, R>(&self, name: &str, f: F) -> R
    where F: FnOnce(&mut Span) -> R;

    // 记录指标
    pub async fn record_metric(
        &self, 
        name: &str, 
        value: f64, 
        labels: Vec<(&str, &str)>
    ) -> Result<(), OtlpError>;

    // 发送日志
    pub async fn emit_log(
        &self, 
        level: LogLevel, 
        message: &str, 
        attributes: Vec<(&str, &str)>
    ) -> Result<(), OtlpError>;

    // 批量发送
    pub async fn send_batch(&self, batch: TelemetryBatch) -> Result<(), OtlpError>;

    // 健康检查
    pub async fn health_check(&self) -> Result<HealthStatus, OtlpError>;
}
```

### Span

表示分布式追踪中的一个操作。

```rust
use otlp::{Span, SpanContext, SpanKind, StatusCode};

// 创建span
let span = client.start_span("database_query", |span| {
    span.set_kind(SpanKind::Client);
    span.set_attribute("db.system", "postgresql");
    span.set_attribute("db.statement", "SELECT * FROM users");
    span.set_attribute("db.operation", "SELECT");
});

// 设置span状态
span.set_status(StatusCode::Ok, "Query executed successfully");

// 添加事件
span.add_event("query_started", vec![
    ("timestamp", "2024-01-01T00:00:00Z"),
]);

// 结束span
span.end();
```

#### 主要方法1

```rust
impl Span {
    // 设置属性
    pub fn set_attribute<K, V>(&self, key: K, value: V)
    where K: Into<String>, V: Into<AttributeValue>;

    // 设置状态
    pub fn set_status(&self, code: StatusCode, message: &str);

    // 添加事件
    pub fn add_event(&self, name: &str, attributes: Vec<(&str, &str)>);

    // 设置span种类
    pub fn set_kind(&self, kind: SpanKind);

    // 结束span
    pub fn end(self);

    // 获取span上下文
    pub fn context(&self) -> SpanContext;
}
```

### TelemetryBatch

批量发送遥测数据的容器。

```rust
use otlp::{TelemetryBatch, TraceData, MetricData, LogData};

let mut batch = TelemetryBatch::new();

// 添加追踪数据
batch.add_trace(TraceData {
    trace_id: "trace-123".to_string(),
    spans: vec![span_data],
});

// 添加指标数据
batch.add_metric(MetricData {
    name: "request_count".to_string(),
    value: 1.0,
    labels: vec![("method", "GET")],
});

// 添加日志数据
batch.add_log(LogData {
    level: LogLevel::Info,
    message: "Request processed".to_string(),
    attributes: vec![("service", "api")],
});

// 发送批量数据
client.send_batch(batch).await?;
```

## 传输层API

### Transport

传输层的抽象接口。

```rust
use otlp::transport::{Transport, GrpcTransport, HttpTransport, TransportConfig};

// gRPC传输
let grpc_transport = GrpcTransport::new(TransportConfig {
    endpoint: "http://collector:4317".to_string(),
    timeout: Duration::from_secs(30),
    retry_config: RetryConfig::default(),
    compression: Compression::Gzip,
});

// HTTP传输
let http_transport = HttpTransport::new(TransportConfig {
    endpoint: "http://collector:4318".to_string(),
    timeout: Duration::from_secs(30),
    retry_config: RetryConfig::default(),
    compression: Compression::Gzip,
});

// 发送数据
grpc_transport.send_traces(traces).await?;
http_transport.send_metrics(metrics).await?;
```

### ConnectionPool

连接池管理。

```rust
use otlp::transport::{ConnectionPool, PoolConfig};

let pool_config = PoolConfig {
    max_connections: 100,
    min_connections: 10,
    connection_timeout: Duration::from_secs(5),
    idle_timeout: Duration::from_secs(300),
    max_lifetime: Duration::from_secs(3600),
    health_check_interval: Duration::from_secs(60),
};

let connection_pool = ConnectionPool::new(pool_config).await?;

// 获取连接
let connection = connection_pool.get_connection().await?;

// 使用连接
let result = connection.send_data(data).await?;

// 归还连接
connection_pool.return_connection(connection);
```

## 数据处理API

### BatchProcessor

批量数据处理器。

```rust
use otlp::processing::{BatchProcessor, BatchConfig, ProcessingResult};

let batch_config = BatchConfig {
    max_batch_size: 1000,
    max_wait_time: Duration::from_millis(100),
    max_memory_size: 10 * 1024 * 1024, // 10MB
    compression_enabled: true,
    parallel_processing: true,
    worker_threads: 4,
};

let mut batch_processor = BatchProcessor::new(batch_config);

// 启动处理
batch_processor.start().await?;

// 添加数据
batch_processor.add_trace(trace_data).await?;
batch_processor.add_metric(metric_data).await?;
batch_processor.add_log(log_data).await?;

// 停止处理
batch_processor.stop().await?;
```

### DataFilter

数据过滤器。

```rust
use otlp::processing::{DataFilter, FilterRule, FilterAction};

let filter_rules = vec![
    FilterRule {
        field: "trace_id".to_string(),
        operator: FilterOperator::StartsWith,
        value: "test-".to_string(),
        action: FilterAction::Drop,
    },
    FilterRule {
        field: "span.duration".to_string(),
        operator: FilterOperator::LessThan,
        value: "1ms".to_string(),
        action: FilterAction::Drop,
    },
];

let data_filter = DataFilter::new(filter_rules);

// 过滤数据
let filtered_data = data_filter.filter(trace_data).await?;
```

### DataAggregator

数据聚合器。

```rust
use otlp::processing::{DataAggregator, AggregationConfig, AggregationFunction};

let aggregation_config = AggregationConfig {
    time_window: Duration::from_secs(60),
    aggregation_functions: vec![
        AggregationFunction::Count,
        AggregationFunction::Sum,
        AggregationFunction::Average,
        AggregationFunction::Max,
        AggregationFunction::Min,
    ],
    group_by: vec!["service".to_string(), "method".to_string()],
};

let data_aggregator = DataAggregator::new(aggregation_config);

// 聚合数据
let aggregated_data = data_aggregator.aggregate(metric_data).await?;
```

## 分布式协调API

### ClusterManager

集群管理器。

```rust
use otlp::distributed::{ClusterManager, ClusterConfig, NodeInfo};

let cluster_config = ClusterConfig {
    consensus_algorithm: ConsensusAlgorithm::Raft,
    cluster_size: 5,
    election_timeout: Duration::from_millis(1000),
    heartbeat_interval: Duration::from_millis(500),
    data_dir: "/var/lib/otlp-rust/data".to_string(),
};

let mut cluster_manager = ClusterManager::new(cluster_config).await?;

// 启动集群
cluster_manager.start().await?;

// 添加节点
let node_info = NodeInfo {
    id: "node-1".to_string(),
    address: "127.0.0.1:8080".to_string(),
    role: NodeRole::Follower,
    status: NodeStatus::Healthy,
};

cluster_manager.add_node(node_info).await?;

// 获取集群状态
let cluster_status = cluster_manager.get_status().await?;
```

### ConsensusProtocol

共识协议接口。

```rust
use otlp::distributed::{ConsensusProtocol, RaftProtocol, PBFTProtocol};

// Raft协议
let raft_protocol = RaftProtocol::new(RaftConfig {
    election_timeout: Duration::from_millis(1000),
    heartbeat_interval: Duration::from_millis(500),
    log_replication_timeout: Duration::from_millis(1000),
});

// PBFT协议
let pbft_protocol = PBFTProtocol::new(PBFTConfig {
    view_change_timeout: Duration::from_millis(2000),
    checkpoint_interval: 100,
    max_faulty_nodes: 1,
});

// 提交提案
let proposal = Proposal {
    id: "proposal-1".to_string(),
    data: "some data".to_string(),
    timestamp: SystemTime::now(),
};

let result = raft_protocol.propose(proposal).await?;
```

### ErrorPropagation

错误传播管理器。

```rust
use otlp::distributed::{ErrorPropagation, PropagationConfig, ErrorGraph};

let propagation_config = PropagationConfig {
    max_propagation_depth: 10,
    propagation_timeout: Duration::from_secs(30),
    retry_attempts: 3,
    backoff_strategy: BackoffStrategy::Exponential,
};

let error_propagation = ErrorPropagation::new(propagation_config);

// 构建错误传播图
let error_graph = ErrorGraph::new();
error_graph.add_node("service-a".to_string());
error_graph.add_node("service-b".to_string());
error_graph.add_edge("service-a".to_string(), "service-b".to_string(), 0.8);

// 传播错误
error_propagation.propagate_error("service-a".to_string(), error_graph).await?;
```

## 机器学习API

### MLPredictor

机器学习预测器。

```rust
use otlp::ml_prediction::{MLPredictor, ModelConfig, PredictionResult, FeatureExtractor};

let model_config = ModelConfig {
    algorithm: "random_forest".to_string(),
    parameters: serde_json::json!({
        "n_estimators": 100,
        "max_depth": 10,
        "min_samples_split": 5,
    }),
    training_data_path: "/var/lib/otlp-rust/ml-data".to_string(),
    model_path: "/var/lib/otlp-rust/models".to_string(),
};

let mut ml_predictor = MLPredictor::new(model_config).await?;

// 训练模型
let training_data = load_training_data().await?;
ml_predictor.train(&training_data).await?;

// 进行预测
let features = extract_features(&system_metrics).await?;
let prediction = ml_predictor.predict(&features).await?;

println!("错误概率: {:.2}%", prediction.error_probability * 100.0);
println!("置信度: {:.2}%", prediction.confidence * 100.0);
```

### FeatureExtractor

特征提取器。

```rust
use otlp::ml_prediction::{FeatureExtractor, SystemMetrics, FeatureVector};

struct CustomFeatureExtractor {
    window_size: Duration,
    feature_cache: HashMap<String, Vec<f64>>,
}

impl FeatureExtractor for CustomFeatureExtractor {
    fn extract_features(&mut self, metrics: &SystemMetrics) -> FeatureVector {
        let mut features = FeatureVector::new();
        
        // 基础指标
        features.push("cpu_usage", metrics.cpu_usage);
        features.push("memory_usage", metrics.memory_usage);
        features.push("network_io", metrics.network_io);
        features.push("disk_io", metrics.disk_io);
        
        // 时间序列特征
        if let Some(historical) = self.feature_cache.get(&metrics.timestamp.to_string()) {
            let moving_avg = historical.iter().sum::<f64>() / historical.len() as f64;
            features.push("moving_average", moving_avg);
            
            if historical.len() >= 2 {
                let trend = historical.last().unwrap() - historical.first().unwrap();
                features.push("trend", trend);
            }
        }
        
        // 更新缓存
        self.update_cache(metrics);
        
        features
    }
}
```

### ModelManager

模型管理器。

```rust
use otlp::ml_prediction::{ModelManager, ModelInfo, ModelVersion};

let model_manager = ModelManager::new(ModelManagerConfig {
    model_registry_path: "/var/lib/otlp-rust/models".to_string(),
    auto_update: true,
    update_interval: Duration::from_secs(300),
    version_control: true,
});

// 注册模型
let model_info = ModelInfo {
    name: "error_prediction".to_string(),
    version: ModelVersion::new(1, 0, 0),
    algorithm: "random_forest".to_string(),
    accuracy: 0.95,
    created_at: SystemTime::now(),
};

model_manager.register_model(model_info).await?;

// 获取最佳模型
let best_model = model_manager.get_best_model("error_prediction").await?;

// 更新模型
model_manager.update_model("error_prediction", new_model_data).await?;
```

## 监控API

### MetricsCollector

指标收集器。

```rust
use otlp::monitoring::{MetricsCollector, MetricConfig, MetricType, MetricValue};

let metric_config = MetricConfig {
    endpoint: "http://prometheus:9090".to_string(),
    interval: Duration::from_secs(15),
    batch_size: 1000,
    compression: true,
    labels: vec![
        ("service", "otlp-rust"),
        ("version", "1.0.0"),
    ],
};

let metrics_collector = MetricsCollector::new(metric_config);

// 注册指标
metrics_collector.register_counter("requests_total", "Total number of requests")?;
metrics_collector.register_histogram("request_duration_seconds", "Request duration")?;
metrics_collector.register_gauge("active_connections", "Active connections")?;

// 记录指标
metrics_collector.increment_counter("requests_total", vec![("method", "GET")])?;
metrics_collector.record_histogram("request_duration_seconds", 0.5, vec![("endpoint", "/api")])?;
metrics_collector.set_gauge("active_connections", 42.0, vec![])?;

// 启动收集
metrics_collector.start().await?;
```

### AlertManager

告警管理器。

```rust
use otlp::monitoring::{AlertManager, AlertRule, AlertSeverity, AlertChannel};

let alert_rules = vec![
    AlertRule {
        name: "high_error_rate".to_string(),
        condition: "error_rate > 0.05".to_string(),
        severity: AlertSeverity::Critical,
        duration: Duration::from_secs(300),
        message: "Error rate is too high".to_string(),
        channels: vec![AlertChannel::Slack, AlertChannel::Email],
    },
    AlertRule {
        name: "high_latency".to_string(),
        condition: "p99_latency > 5".to_string(),
        severity: AlertSeverity::Warning,
        duration: Duration::from_secs(600),
        message: "P99 latency is too high".to_string(),
        channels: vec![AlertChannel::Slack],
    },
];

let alert_manager = AlertManager::new(AlertConfig {
    rules: alert_rules,
    webhook_url: "http://alertmanager:9093/api/v1/alerts".to_string(),
    slack_webhook: "https://hooks.slack.com/services/...".to_string(),
    email_config: EmailConfig {
        smtp_server: "smtp.gmail.com".to_string(),
        port: 587,
        username: "alerts@company.com".to_string(),
        password: "password".to_string(),
    },
});

// 启动告警管理
alert_manager.start().await?;
```

### HealthChecker

健康检查器。

```rust
use otlp::monitoring::{HealthChecker, HealthCheck, HealthStatus, HealthConfig};

let health_checks = vec![
    HealthCheck {
        name: "database".to_string(),
        endpoint: "http://database:5432/health".to_string(),
        timeout: Duration::from_secs(5),
        interval: Duration::from_secs(30),
    },
    HealthCheck {
        name: "redis".to_string(),
        endpoint: "http://redis:6379/ping".to_string(),
        timeout: Duration::from_secs(3),
        interval: Duration::from_secs(30),
    },
];

let health_checker = HealthChecker::new(HealthConfig {
    checks: health_checks,
    overall_timeout: Duration::from_secs(10),
    retry_attempts: 3,
});

// 执行健康检查
let health_status = health_checker.check_all().await?;

match health_status {
    HealthStatus::Healthy => println!("✅ All services healthy"),
    HealthStatus::Degraded(issues) => println!("⚠️ Services degraded: {:?}", issues),
    HealthStatus::Unhealthy(issues) => println!("❌ Services unhealthy: {:?}", issues),
}
```

## 配置API

### ConfigManager

配置管理器。

```rust
use otlp::config::{ConfigManager, ConfigValidator, ConfigWatcher};

let config_manager = ConfigManager::new(ConfigManagerConfig {
    config_path: "config/production.toml".to_string(),
    watch_changes: true,
    auto_reload: true,
    validation_enabled: true,
});

// 加载配置
let config = config_manager.load_config().await?;

// 验证配置
let validator = ConfigValidator::new();
validator.validate_config(&config).await?;

// 监听配置变化
let config_watcher = ConfigWatcher::new(config_manager.clone());
config_watcher.watch(|new_config| {
    println!("配置已更新: {:?}", new_config);
}).await?;

// 获取配置值
let endpoint = config_manager.get_string("otlp.transport.endpoint").await?;
let timeout = config_manager.get_duration("otlp.transport.timeout").await?;
let enabled = config_manager.get_bool("otlp.ml_prediction.enabled").await?;
```

### EnvironmentConfig

环境配置。

```rust
use otlp::config::{EnvironmentConfig, EnvVar, EnvPrefix};

let env_config = EnvironmentConfig::new(EnvConfig {
    prefix: "OTLP_".to_string(),
    case_sensitive: false,
    parse_types: true,
    required_vars: vec![
        "OTLP_ENDPOINT".to_string(),
        "OTLP_LOG_LEVEL".to_string(),
    ],
});

// 从环境变量加载配置
let config = env_config.load_from_env().await?;

// 设置环境变量
env_config.set_env_var("OTLP_ENDPOINT", "http://collector:4317")?;
env_config.set_env_var("OTLP_LOG_LEVEL", "info")?;
env_config.set_env_var("OTLP_TIMEOUT", "30")?;

// 获取环境变量
let endpoint = env_config.get_env_var("OTLP_ENDPOINT")?;
let log_level = env_config.get_env_var("OTLP_LOG_LEVEL")?;
```

## 工具API

### DiagnosticTool

诊断工具。

```rust
use otlp::diagnostics::{DiagnosticTool, DiagnosticResult, DiagnosticConfig};

let diagnostic_config = DiagnosticConfig {
    timeout: Duration::from_secs(30),
    retry_attempts: 3,
    verbose: true,
    output_format: OutputFormat::Json,
};

let diagnostic_tool = DiagnosticTool::new(diagnostic_config);

// 运行完整诊断
let results = diagnostic_tool.run_full_diagnosis().await?;

for result in results {
    match result {
        DiagnosticResult::Success(message) => println!("✅ {}", message),
        DiagnosticResult::Warning(message) => println!("⚠️ {}", message),
        DiagnosticResult::Error(message) => println!("❌ {}", message),
    }
}

// 运行特定诊断
let connection_result = diagnostic_tool.diagnose_connection("http://collector:4317").await?;
let performance_result = diagnostic_tool.diagnose_performance().await?;
let memory_result = diagnostic_tool.diagnose_memory().await?;
```

### BenchmarkTool

基准测试工具。

```rust
use otlp::benchmark::{BenchmarkTool, BenchmarkConfig, BenchmarkResult, WorkloadType};

let benchmark_config = BenchmarkConfig {
    duration: Duration::from_secs(60),
    concurrency: 100,
    batch_size: 1000,
    workload_type: WorkloadType::Mixed,
    warmup_duration: Duration::from_secs(10),
    cooldown_duration: Duration::from_secs(5),
};

let benchmark_tool = BenchmarkTool::new(benchmark_config);

// 运行基准测试
let results = benchmark_tool.run_benchmark().await?;

println!("=== 基准测试结果 ===");
println!("吞吐量: {:.2} ops/sec", results.throughput);
println!("平均延迟: {:.2} ms", results.avg_latency.as_millis());
println!("P95延迟: {:.2} ms", results.p95_latency.as_millis());
println!("P99延迟: {:.2} ms", results.p99_latency.as_millis());
println!("错误率: {:.2}%", results.error_rate * 100.0);

// 生成报告
benchmark_tool.generate_report(&results, "benchmark-report.json").await?;
```

### Profiler

性能分析器。

```rust
use otlp::profiling::{Profiler, ProfileConfig, ProfileResult, ProfileOutput};

let profile_config = ProfileConfig {
    duration: Duration::from_secs(30),
    sample_rate: 1000,
    output_format: ProfileOutput::FlameGraph,
    include_system_calls: true,
    memory_profiling: true,
    cpu_profiling: true,
};

let profiler = Profiler::new(profile_config);

// 开始性能分析
profiler.start().await?;

// 运行负载
run_workload().await?;

// 停止分析
let profile_result = profiler.stop().await?;

// 分析结果
println!("=== 性能分析结果 ===");
for (function, stats) in profile_result.function_stats {
    println!("函数: {}", function);
    println!("  调用次数: {}", stats.call_count);
    println!("  总时间: {:.2} ms", stats.total_time.as_millis());
    println!("  平均时间: {:.2} ms", stats.avg_time.as_millis());
    println!("  最大时间: {:.2} ms", stats.max_time.as_millis());
}

// 生成火焰图
profiler.generate_flame_graph(&profile_result, "flame-graph.svg").await?;
```

## 总结

本文档提供了OTLP Rust项目的完整API参考，包括：

1. **核心API**：OtlpClient、Span、TelemetryBatch等核心接口
2. **传输层API**：Transport、ConnectionPool等传输相关接口
3. **数据处理API**：BatchProcessor、DataFilter、DataAggregator等处理接口
4. **分布式协调API**：ClusterManager、ConsensusProtocol、ErrorPropagation等协调接口
5. **机器学习API**：MLPredictor、FeatureExtractor、ModelManager等ML接口
6. **监控API**：MetricsCollector、AlertManager、HealthChecker等监控接口
7. **配置API**：ConfigManager、EnvironmentConfig等配置接口
8. **工具API**：DiagnosticTool、BenchmarkTool、Profiler等工具接口

这些API提供了完整的OTLP Rust项目功能，支持高性能、高可用的分布式可观测性系统构建。通过合理使用这些API，您可以构建出满足各种需求的监控和追踪系统。
