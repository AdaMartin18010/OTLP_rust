# OTLP Rust 示例代码集合

## 目录

1. [基础示例](#基础示例)
2. [Web应用示例](#web应用示例)
3. [微服务示例](#微服务示例)
4. [数据处理示例](#数据处理示例)
5. [机器学习示例](#机器学习示例)
6. [分布式系统示例](#分布式系统示例)
7. [监控告警示例](#监控告警示例)
8. [性能优化示例](#性能优化示例)

## 基础示例

### 1. 简单客户端示例

```rust
// examples/basic_client.rs
use otlp::{OtlpClient, OtlpClientBuilder};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建客户端
    let client = OtlpClientBuilder::new()
        .with_endpoint("http://localhost:4317")
        .with_timeout(Duration::from_secs(30))
        .build()
        .await?;

    // 发送追踪
    let span = client.start_span("basic_operation", |span| {
        span.set_attribute("service", "basic-example");
        span.set_attribute("operation", "test");
    });

    // 模拟工作
    tokio::time::sleep(Duration::from_millis(100)).await;
    
    // 记录指标
    client.record_metric("operation_count", 1.0, vec![
        ("type", "basic"),
        ("status", "success"),
    ]).await?;

    span.end();
    println!("基础示例完成！");
    Ok(())
}
```

### 2. 批量数据发送示例

```rust
// examples/batch_sending.rs
use otlp::{OtlpClient, TelemetryBatch, TraceData, MetricData, LogData, LogLevel};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = OtlpClientBuilder::new()
        .with_endpoint("http://localhost:4317")
        .build()
        .await?;

    // 创建批量数据
    let mut batch = TelemetryBatch::new();

    // 添加追踪数据
    for i in 0..10 {
        batch.add_trace(TraceData {
            trace_id: format!("trace-{}", i),
            spans: vec![create_sample_span(i)],
        });
    }

    // 添加指标数据
    for i in 0..100 {
        batch.add_metric(MetricData {
            name: "request_count".to_string(),
            value: 1.0,
            labels: vec![
                ("method", "GET"),
                ("status", "200"),
                ("endpoint", &format!("/api/{}", i)),
            ],
        });
    }

    // 添加日志数据
    for i in 0..50 {
        batch.add_log(LogData {
            level: LogLevel::Info,
            message: format!("Processing request {}", i),
            attributes: vec![
                ("request_id", &format!("req-{}", i)),
                ("service", "api-server"),
            ],
        });
    }

    // 发送批量数据
    client.send_batch(batch).await?;
    println!("批量数据发送完成！");
    Ok(())
}

fn create_sample_span(id: u32) -> SpanData {
    // 创建示例span数据
    SpanData::new("sample_operation")
        .with_attribute("span_id", format!("span-{}", id))
        .with_attribute("duration", 100 + id)
}
```

## Web应用示例

### 1. Axum集成示例

```rust
// examples/axum_integration.rs
use axum::{
    extract::{Path, Query, State},
    http::StatusCode,
    response::Json,
    routing::{get, post},
    Router,
};
use otlp::{OtlpClient, Span, middleware::OtlpMiddleware};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use tower::ServiceBuilder;

#[derive(Clone)]
struct AppState {
    otlp_client: OtlpClient,
}

#[derive(Serialize, Deserialize)]
struct User {
    id: u32,
    name: String,
    email: String,
}

#[derive(Deserialize)]
struct CreateUser {
    name: String,
    email: String,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建OTLP客户端
    let otlp_client = OtlpClientBuilder::new()
        .with_endpoint("http://localhost:4317")
        .build()
        .await?;

    let app_state = AppState {
        otlp_client: otlp_client.clone(),
    };

    // 创建路由
    let app = Router::new()
        .route("/users", get(get_users).post(create_user))
        .route("/users/:id", get(get_user))
        .route("/health", get(health_check))
        .layer(
            ServiceBuilder::new()
                .layer(middleware::from_fn_with_state(
                    otlp_client,
                    OtlpMiddleware::tracing,
                ))
        )
        .with_state(app_state);

    // 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
    println!("服务器启动在 http://0.0.0.0:3000");
    axum::serve(listener, app).await?;

    Ok(())
}

async fn get_users(
    State(state): State<AppState>,
    Query(params): Query<HashMap<String, String>>,
) -> Result<Json<Vec<User>>, StatusCode> {
    let span = state.otlp_client.start_span("get_users", |span| {
        span.set_attribute("endpoint", "/users");
        span.set_attribute("method", "GET");
    });

    // 模拟数据库查询
    let users = vec![
        User {
            id: 1,
            name: "Alice".to_string(),
            email: "alice@example.com".to_string(),
        },
        User {
            id: 2,
            name: "Bob".to_string(),
            email: "bob@example.com".to_string(),
        },
    ];

    span.set_attribute("user_count", users.len() as i64);
    span.end();

    Ok(Json(users))
}

async fn create_user(
    State(state): State<AppState>,
    Json(payload): Json<CreateUser>,
) -> Result<Json<User>, StatusCode> {
    let span = state.otlp_client.start_span("create_user", |span| {
        span.set_attribute("endpoint", "/users");
        span.set_attribute("method", "POST");
        span.set_attribute("user.name", &payload.name);
        span.set_attribute("user.email", &payload.email);
    });

    // 模拟用户创建
    let user = User {
        id: 3,
        name: payload.name,
        email: payload.email,
    };

    span.set_attribute("user.id", user.id as i64);
    span.end();

    Ok(Json(user))
}

async fn get_user(
    State(state): State<AppState>,
    Path(id): Path<u32>,
) -> Result<Json<User>, StatusCode> {
    let span = state.otlp_client.start_span("get_user", |span| {
        span.set_attribute("endpoint", "/users/:id");
        span.set_attribute("method", "GET");
        span.set_attribute("user.id", id as i64);
    });

    // 模拟用户查询
    let user = User {
        id,
        name: format!("User {}", id),
        email: format!("user{}@example.com", id),
    };

    span.end();
    Ok(Json(user))
}

async fn health_check() -> Result<Json<serde_json::Value>, StatusCode> {
    Ok(Json(serde_json::json!({
        "status": "healthy",
        "timestamp": chrono::Utc::now()
    })))
}
```

### 2. Actix Web集成示例

```rust
// examples/actix_integration.rs
use actix_web::{web, App, HttpServer, Result, middleware::Logger};
use otlp::{OtlpClient, OtlpClientBuilder};
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
struct Response {
    message: String,
    timestamp: String,
}

async fn index() -> Result<web::Json<Response>> {
    Ok(web::Json(Response {
        message: "Hello OTLP Rust!".to_string(),
        timestamp: chrono::Utc::now().to_rfc3339(),
    }))
}

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    // 创建OTLP客户端
    let otlp_client = OtlpClientBuilder::new()
        .with_endpoint("http://localhost:4317")
        .build()
        .await
        .unwrap();

    HttpServer::new(move || {
        App::new()
            .app_data(web::Data::new(otlp_client.clone()))
            .wrap(Logger::default())
            .service(web::resource("/").route(web::get().to(index)))
    })
    .bind("127.0.0.1:8080")?
    .run()
    .await
}
```

## 微服务示例

### 1. 服务间通信追踪

```rust
// examples/microservice_tracing.rs
use otlp::{OtlpClient, Span, TraceContext};
use reqwest::Client;
use serde_json::json;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let otlp_client = OtlpClientBuilder::new()
        .with_endpoint("http://localhost:4317")
        .build()
        .await?;

    // 模拟微服务调用链
    let root_span = otlp_client.start_span("order_processing", |span| {
        span.set_attribute("order.id", "12345");
        span.set_attribute("customer.id", "67890");
    });

    let trace_context = root_span.context();

    // 调用用户服务
    let user_info = call_user_service(&otlp_client, &trace_context, "67890").await?;
    root_span.set_attribute("user.name", &user_info.name);

    // 调用库存服务
    let inventory_result = call_inventory_service(&otlp_client, &trace_context, "12345").await?;
    root_span.set_attribute("inventory.available", inventory_result.available);

    // 调用支付服务
    let payment_result = call_payment_service(&otlp_client, &trace_context, &user_info, 100.0).await?;
    root_span.set_attribute("payment.status", payment_result.status);

    root_span.end();
    println!("微服务调用链完成！");
    Ok(())
}

async fn call_user_service(
    otlp_client: &OtlpClient,
    trace_context: &TraceContext,
    user_id: &str,
) -> Result<UserInfo, Box<dyn std::error::Error>> {
    let span = otlp_client.start_span_with_context(
        "user_service.get_user",
        trace_context,
        |span| {
            span.set_attribute("user.id", user_id);
            span.set_attribute("service.name", "user-service");
        },
    );

    // 模拟HTTP调用
    let client = Client::new();
    let response = client
        .get(&format!("http://user-service/users/{}", user_id))
        .header("traceparent", trace_context.to_header())
        .send()
        .await?;

    let user_info: UserInfo = response.json().await?;
    
    span.set_attribute("user.name", &user_info.name);
    span.set_attribute("response.status", response.status().as_u16());
    span.end();

    Ok(user_info)
}

async fn call_inventory_service(
    otlp_client: &OtlpClient,
    trace_context: &TraceContext,
    product_id: &str,
) -> Result<InventoryResult, Box<dyn std::error::Error>> {
    let span = otlp_client.start_span_with_context(
        "inventory_service.check_stock",
        trace_context,
        |span| {
            span.set_attribute("product.id", product_id);
            span.set_attribute("service.name", "inventory-service");
        },
    );

    // 模拟库存检查
    let inventory_result = InventoryResult {
        available: true,
        quantity: 100,
    };

    span.set_attribute("inventory.available", inventory_result.available);
    span.set_attribute("inventory.quantity", inventory_result.quantity);
    span.end();

    Ok(inventory_result)
}

async fn call_payment_service(
    otlp_client: &OtlpClient,
    trace_context: &TraceContext,
    user_info: &UserInfo,
    amount: f64,
) -> Result<PaymentResult, Box<dyn std::error::Error>> {
    let span = otlp_client.start_span_with_context(
        "payment_service.process_payment",
        trace_context,
        |span| {
            span.set_attribute("user.id", &user_info.id);
            span.set_attribute("amount", amount);
            span.set_attribute("service.name", "payment-service");
        },
    );

    // 模拟支付处理
    let payment_result = PaymentResult {
        status: "success".to_string(),
        transaction_id: "txn-12345".to_string(),
    };

    span.set_attribute("payment.status", &payment_result.status);
    span.set_attribute("payment.transaction_id", &payment_result.transaction_id);
    span.end();

    Ok(payment_result)
}

#[derive(serde::Deserialize)]
struct UserInfo {
    id: String,
    name: String,
    email: String,
}

struct InventoryResult {
    available: bool,
    quantity: i32,
}

struct PaymentResult {
    status: String,
    transaction_id: String,
}
```

## 数据处理示例

### 1. 批量处理示例

```rust
// examples/batch_processing.rs
use otlp::processing::{BatchProcessor, BatchConfig, DataFilter, FilterRule, FilterAction, FilterOperator};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 配置批量处理器
    let batch_config = BatchConfig {
        max_batch_size: 1000,
        max_wait_time: Duration::from_millis(100),
        max_memory_size: 10 * 1024 * 1024, // 10MB
        compression_enabled: true,
        parallel_processing: true,
        worker_threads: 4,
    };

    let mut batch_processor = BatchProcessor::new(batch_config);

    // 配置数据过滤器
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

    // 启动批量处理
    batch_processor.start().await?;

    // 模拟数据产生
    for i in 0..10000 {
        let trace_data = create_sample_trace(i);
        
        // 应用过滤器
        if data_filter.should_process(&trace_data).await? {
            batch_processor.add_trace(trace_data).await?;
        }

        if i % 1000 == 0 {
            println!("已处理 {} 条数据", i);
        }
    }

    // 停止处理
    batch_processor.stop().await?;
    println!("批量处理完成！");
    Ok(())
}

fn create_sample_trace(id: u32) -> TraceData {
    TraceData {
        trace_id: format!("trace-{}", id),
        spans: vec![SpanData::new("sample_operation")
            .with_attribute("span_id", format!("span-{}", id))
            .with_attribute("duration", 100 + (id % 1000))],
    }
}
```

### 2. 数据聚合示例

```rust
// examples/data_aggregation.rs
use otlp::processing::{DataAggregator, AggregationConfig, AggregationFunction};
use std::time::Duration;
use std::collections::HashMap;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
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

    // 模拟指标数据
    let mut metric_data = Vec::new();
    for i in 0..1000 {
        metric_data.push(MetricData {
            name: "request_duration".to_string(),
            value: 100.0 + (i as f64 * 0.1),
            labels: vec![
                ("service", if i % 2 == 0 { "api" } else { "web" }),
                ("method", if i % 3 == 0 { "GET" } else { "POST" }),
            ],
            timestamp: std::time::SystemTime::now(),
        });
    }

    // 聚合数据
    let aggregated_data = data_aggregator.aggregate(&metric_data).await?;

    println!("聚合结果:");
    for (group, stats) in aggregated_data {
        println!("组: {:?}", group);
        println!("  计数: {}", stats.count);
        println!("  总和: {:.2}", stats.sum);
        println!("  平均值: {:.2}", stats.average);
        println!("  最大值: {:.2}", stats.max);
        println!("  最小值: {:.2}", stats.min);
        println!();
    }

    Ok(())
}

#[derive(Debug, Clone)]
struct MetricData {
    name: String,
    value: f64,
    labels: Vec<(&'static str, &'static str)>,
    timestamp: std::time::SystemTime,
}

#[derive(Debug)]
struct AggregationStats {
    count: usize,
    sum: f64,
    average: f64,
    max: f64,
    min: f64,
}
```

## 机器学习示例

### 1. 错误预测示例

```rust
// examples/ml_prediction.rs
use otlp::ml_prediction::{MLPredictor, ModelConfig, FeatureExtractor, SystemMetrics};
use std::collections::HashMap;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 配置模型
    let model_config = ModelConfig {
        algorithm: "random_forest".to_string(),
        parameters: serde_json::json!({
            "n_estimators": 100,
            "max_depth": 10,
            "min_samples_split": 5,
        }),
        training_data_path: "/tmp/ml-data".to_string(),
        model_path: "/tmp/models".to_string(),
    };

    let mut ml_predictor = MLPredictor::new(model_config).await?;

    // 加载训练数据
    let training_data = load_training_data().await?;
    ml_predictor.train(&training_data).await?;

    // 创建特征提取器
    let mut feature_extractor = SystemMetricsExtractor {
        window_size: Duration::from_secs(60),
        feature_cache: HashMap::new(),
    };

    // 实时预测循环
    for i in 0..100 {
        // 收集系统指标
        let metrics = collect_system_metrics(i).await?;
        
        // 提取特征
        let features = feature_extractor.extract_features(&metrics);
        
        // 进行预测
        let prediction = ml_predictor.predict(&features).await?;
        
        // 处理预测结果
        if prediction.confidence > 0.8 && prediction.error_probability > 0.7 {
            println!("⚠️ 高风险预警 (第{}次): 错误概率 {:.2}%, 置信度 {:.2}%", 
                i, 
                prediction.error_probability * 100.0, 
                prediction.confidence * 100.0
            );
            
            // 触发预防措施
            trigger_preventive_measures(&prediction).await?;
        } else {
            println!("✅ 系统正常 (第{}次): 错误概率 {:.2}%", 
                i, 
                prediction.error_probability * 100.0
            );
        }

        tokio::time::sleep(Duration::from_secs(10)).await;
    }

    Ok(())
}

struct SystemMetricsExtractor {
    window_size: Duration,
    feature_cache: HashMap<String, Vec<f64>>,
}

impl FeatureExtractor for SystemMetricsExtractor {
    fn extract_features(&mut self, metrics: &SystemMetrics) -> Vec<f64> {
        let mut features = Vec::new();

        // 基础指标特征
        features.push(metrics.cpu_usage);
        features.push(metrics.memory_usage);
        features.push(metrics.network_io);
        features.push(metrics.disk_io);

        // 时间序列特征
        let key = format!("{}", metrics.timestamp.duration_since(std::time::UNIX_EPOCH).unwrap().as_secs());
        if let Some(historical) = self.feature_cache.get(&key) {
            // 计算移动平均
            let moving_avg = historical.iter().sum::<f64>() / historical.len() as f64;
            features.push(moving_avg);

            // 计算趋势
            if historical.len() >= 2 {
                let trend = historical.last().unwrap() - historical.first().unwrap();
                features.push(trend);
            }
        }

        // 更新缓存
        self.update_cache(metrics);

        features
    }
}

impl SystemMetricsExtractor {
    fn update_cache(&mut self, metrics: &SystemMetrics) {
        let key = format!("{}", metrics.timestamp.duration_since(std::time::UNIX_EPOCH).unwrap().as_secs());
        let entry = self.feature_cache.entry(key).or_insert_with(Vec::new);
        
        entry.push(metrics.cpu_usage);
        
        // 保持窗口大小
        if entry.len() > 10 {
            entry.remove(0);
        }
    }
}

async fn load_training_data() -> Result<Vec<TrainingSample>, Box<dyn std::error::Error>> {
    // 模拟加载训练数据
    let mut training_data = Vec::new();
    
    for i in 0..1000 {
        let features = vec![
            (i as f64 * 0.1) % 100.0, // CPU使用率
            (i as f64 * 0.2) % 100.0, // 内存使用率
            (i as f64 * 0.3) % 1000.0, // 网络I/O
            (i as f64 * 0.4) % 1000.0, // 磁盘I/O
        ];
        
        let error_occurred = features[0] > 80.0 || features[1] > 90.0;
        
        training_data.push(TrainingSample {
            features,
            label: if error_occurred { 1.0 } else { 0.0 },
        });
    }
    
    Ok(training_data)
}

async fn collect_system_metrics(iteration: u32) -> Result<SystemMetrics, Box<dyn std::error::Error>> {
    // 模拟收集系统指标
    Ok(SystemMetrics {
        cpu_usage: 50.0 + (iteration as f64 * 0.1) % 50.0,
        memory_usage: 60.0 + (iteration as f64 * 0.2) % 40.0,
        network_io: 100.0 + (iteration as f64 * 0.3) % 900.0,
        disk_io: 200.0 + (iteration as f64 * 0.4) % 800.0,
        timestamp: std::time::SystemTime::now(),
    })
}

async fn trigger_preventive_measures(prediction: &PredictionResult) -> Result<(), Box<dyn std::error::Error>> {
    match prediction.error_type.as_str() {
        "memory_leak" => {
            println!("🔧 触发内存清理");
        },
        "network_congestion" => {
            println!("🔧 调整网络配置");
        },
        "cpu_overload" => {
            println!("🔧 启动负载均衡");
        },
        _ => {
            println!("🔧 执行通用预防措施");
        }
    }
    Ok(())
}

#[derive(Debug)]
struct SystemMetrics {
    cpu_usage: f64,
    memory_usage: f64,
    network_io: f64,
    disk_io: f64,
    timestamp: std::time::SystemTime,
}

#[derive(Debug)]
struct TrainingSample {
    features: Vec<f64>,
    label: f64,
}

#[derive(Debug)]
struct PredictionResult {
    error_probability: f64,
    confidence: f64,
    error_type: String,
}
```

## 分布式系统示例

### 1. 集群管理示例

```rust
// examples/cluster_management.rs
use otlp::distributed::{ClusterManager, ClusterConfig, NodeInfo, NodeRole, NodeStatus};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cluster_config = ClusterConfig {
        consensus_algorithm: ConsensusAlgorithm::Raft,
        cluster_size: 5,
        election_timeout: Duration::from_millis(1000),
        heartbeat_interval: Duration::from_millis(500),
        data_dir: "/tmp/otlp-cluster".to_string(),
    };

    let mut cluster_manager = ClusterManager::new(cluster_config).await?;

    // 启动集群
    cluster_manager.start().await?;

    // 添加节点
    for i in 1..=5 {
        let node_info = NodeInfo {
            id: format!("node-{}", i),
            address: format!("127.0.0.1:{}", 8080 + i),
            role: if i == 1 { NodeRole::Leader } else { NodeRole::Follower },
            status: NodeStatus::Healthy,
            last_heartbeat: std::time::SystemTime::now(),
        };

        cluster_manager.add_node(node_info).await?;
        println!("添加节点: node-{}", i);
    }

    // 监控集群状态
    for _ in 0..10 {
        let cluster_status = cluster_manager.get_status().await?;
        println!("集群状态: {:?}", cluster_status);
        
        tokio::time::sleep(Duration::from_secs(5)).await;
    }

    Ok(())
}
```

### 2. 错误传播示例

```rust
// examples/error_propagation.rs
use otlp::distributed::{ErrorPropagation, PropagationConfig, ErrorGraph};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let propagation_config = PropagationConfig {
        max_propagation_depth: 10,
        propagation_timeout: Duration::from_secs(30),
        retry_attempts: 3,
        backoff_strategy: BackoffStrategy::Exponential,
    };

    let error_propagation = ErrorPropagation::new(propagation_config);

    // 构建错误传播图
    let mut error_graph = ErrorGraph::new();
    
    // 添加节点
    error_graph.add_node("api-gateway".to_string());
    error_graph.add_node("user-service".to_string());
    error_graph.add_node("order-service".to_string());
    error_graph.add_node("payment-service".to_string());
    error_graph.add_node("inventory-service".to_string());
    error_graph.add_node("database".to_string());

    // 添加依赖关系
    error_graph.add_edge("api-gateway".to_string(), "user-service".to_string(), 0.8);
    error_graph.add_edge("api-gateway".to_string(), "order-service".to_string(), 0.9);
    error_graph.add_edge("order-service".to_string(), "payment-service".to_string(), 0.7);
    error_graph.add_edge("order-service".to_string(), "inventory-service".to_string(), 0.6);
    error_graph.add_edge("payment-service".to_string(), "database".to_string(), 0.5);
    error_graph.add_edge("inventory-service".to_string(), "database".to_string(), 0.5);

    // 模拟数据库故障
    println!("🔴 数据库发生故障");
    error_propagation.propagate_error("database".to_string(), error_graph).await?;

    // 等待传播完成
    tokio::time::sleep(Duration::from_secs(5)).await;

    println!("错误传播分析完成");
    Ok(())
}
```

## 监控告警示例

### 1. 指标收集示例

```rust
// examples/metrics_collection.rs
use otlp::monitoring::{MetricsCollector, MetricConfig, MetricType};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let metric_config = MetricConfig {
        endpoint: "http://localhost:9090".to_string(),
        interval: Duration::from_secs(15),
        batch_size: 1000,
        compression: true,
        labels: vec![
            ("service", "otlp-rust"),
            ("version", "1.0.0"),
            ("environment", "development"),
        ],
    };

    let metrics_collector = MetricsCollector::new(metric_config);

    // 注册指标
    metrics_collector.register_counter("requests_total", "Total number of requests")?;
    metrics_collector.register_histogram("request_duration_seconds", "Request duration")?;
    metrics_collector.register_gauge("active_connections", "Active connections")?;

    // 启动收集
    metrics_collector.start().await?;

    // 模拟应用运行
    for i in 0..100 {
        // 记录请求指标
        metrics_collector.increment_counter("requests_total", vec![
            ("method", if i % 2 == 0 { "GET" } else { "POST" }),
            ("status", if i % 10 == 0 { "500" } else { "200" }),
        ])?;

        // 记录延迟指标
        let duration = 0.1 + (i as f64 * 0.001);
        metrics_collector.record_histogram("request_duration_seconds", duration, vec![
            ("endpoint", "/api/users"),
        ])?;

        // 记录连接数指标
        let connections = 50 + (i % 20);
        metrics_collector.set_gauge("active_connections", connections as f64, vec![])?;

        tokio::time::sleep(Duration::from_millis(100)).await;
    }

    println!("指标收集示例完成");
    Ok(())
}
```

### 2. 告警管理示例

```rust
// examples/alert_management.rs
use otlp::monitoring::{AlertManager, AlertRule, AlertSeverity, AlertChannel};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let alert_rules = vec![
        AlertRule {
            name: "high_error_rate".to_string(),
            condition: "error_rate > 0.05".to_string(),
            severity: AlertSeverity::Critical,
            duration: Duration::from_secs(300),
            message: "错误率过高，需要立即处理".to_string(),
            channels: vec![AlertChannel::Slack, AlertChannel::Email],
        },
        AlertRule {
            name: "high_latency".to_string(),
            condition: "p99_latency > 5".to_string(),
            severity: AlertSeverity::Warning,
            duration: Duration::from_secs(600),
            message: "P99延迟过高，建议优化".to_string(),
            channels: vec![AlertChannel::Slack],
        },
        AlertRule {
            name: "low_disk_space".to_string(),
            condition: "disk_usage > 0.9".to_string(),
            severity: AlertSeverity::Critical,
            duration: Duration::from_secs(60),
            message: "磁盘空间不足，需要清理".to_string(),
            channels: vec![AlertChannel::Email, AlertChannel::PagerDuty],
        },
    ];

    let alert_manager = AlertManager::new(AlertConfig {
        rules: alert_rules,
        webhook_url: "http://localhost:9093/api/v1/alerts".to_string(),
        slack_webhook: "https://hooks.slack.com/services/...".to_string(),
        email_config: EmailConfig {
            smtp_server: "smtp.gmail.com".to_string(),
            port: 587,
            username: "alerts@company.com".to_string(),
            password: "password".to_string(),
        },
        pagerduty_config: PagerDutyConfig {
            integration_key: "your-integration-key".to_string(),
        },
    });

    // 启动告警管理
    alert_manager.start().await?;

    // 模拟触发告警
    println!("模拟触发告警...");
    
    // 模拟高错误率
    alert_manager.check_condition("error_rate", 0.08).await?;
    
    // 模拟高延迟
    alert_manager.check_condition("p99_latency", 6.5).await?;
    
    // 模拟磁盘空间不足
    alert_manager.check_condition("disk_usage", 0.95).await?;

    // 等待告警处理
    tokio::time::sleep(Duration::from_secs(10)).await;

    println!("告警管理示例完成");
    Ok(())
}

#[derive(Debug)]
struct EmailConfig {
    smtp_server: String,
    port: u16,
    username: String,
    password: String,
}

#[derive(Debug)]
struct PagerDutyConfig {
    integration_key: String,
}

#[derive(Debug)]
struct AlertConfig {
    rules: Vec<AlertRule>,
    webhook_url: String,
    slack_webhook: String,
    email_config: EmailConfig,
    pagerduty_config: PagerDutyConfig,
}
```

## 性能优化示例

### 1. 连接池优化示例

```rust
// examples/connection_pool_optimization.rs
use otlp::transport::{ConnectionPool, PoolConfig};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let pool_config = PoolConfig {
        max_connections: 100,
        min_connections: 10,
        connection_timeout: Duration::from_secs(5),
        idle_timeout: Duration::from_secs(300),
        max_lifetime: Duration::from_secs(3600),
        health_check_interval: Duration::from_secs(60),
    };

    let connection_pool = ConnectionPool::new(pool_config).await?;

    // 预热连接池
    connection_pool.warmup().await?;

    // 并发使用连接池
    let mut handles = Vec::new();
    for i in 0..1000 {
        let pool = connection_pool.clone();
        let handle = tokio::spawn(async move {
            let connection = pool.get_connection().await?;
            
            // 模拟OTLP请求
            let result = connection.send_trace_data(&create_sample_trace(i)).await?;
            
            pool.return_connection(connection);
            Ok::<_, Box<dyn std::error::Error>>(result)
        });
        handles.push(handle);
    }

    // 等待所有任务完成
    for handle in handles {
        handle.await??;
    }

    println!("连接池优化示例完成");
    Ok(())
}

fn create_sample_trace(id: u32) -> TraceData {
    TraceData {
        trace_id: format!("trace-{}", id),
        spans: vec![SpanData::new("sample_operation")
            .with_attribute("span_id", format!("span-{}", id))],
    }
}
```

### 2. 内存优化示例

```rust
// examples/memory_optimization.rs
use otlp::processing::{MemoryOptimizer, ObjectPool, ZeroCopyProcessor};
use std::sync::Arc;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建对象池
    let trace_pool = ObjectPool::new(1000, || TraceData::new());
    let span_pool = ObjectPool::new(5000, || SpanData::new());

    // 创建零拷贝处理器
    let zero_copy_processor = ZeroCopyProcessor::new(
        trace_pool.clone(),
        span_pool.clone(),
    );

    // 创建内存优化器
    let memory_optimizer = MemoryOptimizer::new(MemoryConfig {
        max_memory_usage: 100 * 1024 * 1024, // 100MB
        gc_threshold: 0.8,
        gc_interval: Duration::from_secs(30),
    });

    // 启动内存优化
    memory_optimizer.start().await?;

    // 模拟大量数据处理
    for i in 0..100000 {
        // 从对象池获取对象
        let mut trace_data = trace_pool.get().await?;
        let mut span_data = span_pool.get().await?;

        // 填充数据
        trace_data.trace_id = format!("trace-{}", i);
        span_data.name = "optimized_operation".to_string();
        span_data.set_attribute("iteration", i);

        trace_data.spans.push(span_data);

        // 零拷贝处理
        zero_copy_processor.process(trace_data).await?;

        if i % 10000 == 0 {
            println!("已处理 {} 条数据", i);
            memory_optimizer.print_memory_stats().await?;
        }
    }

    println!("内存优化示例完成");
    Ok(())
}

#[derive(Debug)]
struct MemoryConfig {
    max_memory_usage: usize,
    gc_threshold: f64,
    gc_interval: Duration,
}
```

## 总结

本文档提供了OTLP Rust项目的完整示例代码集合，包括：

1. **基础示例**：简单客户端、批量数据发送
2. **Web应用示例**：Axum集成、Actix Web集成
3. **微服务示例**：服务间通信追踪
4. **数据处理示例**：批量处理、数据聚合
5. **机器学习示例**：错误预测、特征提取
6. **分布式系统示例**：集群管理、错误传播
7. **监控告警示例**：指标收集、告警管理
8. **性能优化示例**：连接池优化、内存优化

这些示例代码展示了OTLP Rust项目的各种使用场景和最佳实践，可以作为开发参考和起点。每个示例都包含完整的代码实现和详细说明，帮助开发者快速上手和深入理解项目功能。
