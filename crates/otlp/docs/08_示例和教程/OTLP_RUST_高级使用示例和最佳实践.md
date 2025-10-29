# OTLP Rust 高级使用示例和最佳实践

## 📋 目录
1. [高级配置示例](#高级配置示例)
2. [分布式系统集成](#分布式系统集成)
3. [机器学习错误预测实战](#机器学习错误预测实战)
4. [边缘计算场景](#边缘计算场景)
5. [性能优化最佳实践](#性能优化最佳实践)
6. [生产环境部署](#生产环境部署)
7. [监控和告警配置](#监控和告警配置)

## 高级配置示例

### 1. 多环境配置管理

```rust
// config/production.toml
[otlp]
environment = "production"
log_level = "info"

[otlp.transport]
protocol = "grpc"
endpoints = [
    "https://collector-1.prod.company.com:4317",
    "https://collector-2.prod.company.com:4317"
]
timeout = 30
retry_attempts = 3

[otlp.resilience]
circuit_breaker = { failure_threshold = 5, recovery_timeout = 60 }
retry = { max_attempts = 3, base_delay = 100, max_delay = 5000 }
timeout = { connect = 5, read = 30, write = 30 }

[otlp.ml_prediction]
enabled = true
models = ["random_forest", "neural_network"]
update_interval = 300
confidence_threshold = 0.8

[otlp.distributed]
consensus = "raft"
cluster_size = 5
election_timeout = 1000
heartbeat_interval = 500
```

### 2. 动态配置更新

```rust
use otlp::config::ConfigManager;
use tokio::time::{interval, Duration};

async fn dynamic_config_example() -> Result<(), Box<dyn std::error::Error>> {
    let mut config_manager = ConfigManager::new("config/production.toml")?;
    
    // 启动配置监听
    let mut interval = interval(Duration::from_secs(30));
    loop {
        interval.tick().await;
        
        // 检查配置文件更新
        if config_manager.has_changes()? {
            println!("配置文件已更新，重新加载...");
            config_manager.reload()?;
            
            // 通知相关组件更新配置
            config_manager.notify_subscribers().await?;
        }
    }
}
```

## 分布式系统集成

### 1. 微服务架构集成

```rust
use otlp::{OtlpClient, TraceConfig, MetricConfig};
use axum::{Router, middleware};
use tower::ServiceBuilder;

async fn setup_microservice_observability() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化OTLP客户端
    let otlp_client = OtlpClient::builder()
        .with_transport_grpc("http://collector:4317")
        .with_resilience_config(ResilienceConfig {
            circuit_breaker: CircuitBreakerConfig {
                failure_threshold: 3,
                recovery_timeout: Duration::from_secs(60),
                ..Default::default()
            },
            retry: RetryConfig {
                max_attempts: 3,
                base_delay: Duration::from_millis(100),
                ..Default::default()
            },
            ..Default::default()
        })
        .build()
        .await?;

    // 配置追踪
    let trace_config = TraceConfig {
        service_name: "user-service".to_string(),
        service_version: "1.0.0".to_string(),
        resource_attributes: vec![
            ("deployment.environment", "production".to_string()),
            ("service.instance.id", "user-svc-001".to_string()),
        ],
        ..Default::default()
    };

    // 配置指标
    let metric_config = MetricConfig {
        service_name: "user-service".to_string(),
        metrics_endpoint: "http://collector:4318".to_string(),
        ..Default::default()
    };

    // 创建Axum应用
    let app = Router::new()
        .route("/users", get(get_users))
        .route("/users/:id", get(get_user))
        .layer(
            ServiceBuilder::new()
                .layer(middleware::from_fn_with_state(
                    otlp_client.clone(),
                    otlp_tracing_middleware,
                ))
                .layer(middleware::from_fn_with_state(
                    otlp_client.clone(),
                    otlp_metrics_middleware,
                ))
        );

    Ok(())
}

async fn otlp_tracing_middleware(
    State(otlp_client): State<OtlpClient>,
    request: Request<Body>,
    next: Next<Body>,
) -> Response {
    let span = otlp_client.start_span("http_request", |span| {
        span.set_attribute("http.method", request.method().as_str());
        span.set_attribute("http.url", request.uri().to_string());
    });

    let response = next.run(request).await;

    span.set_attribute("http.status_code", response.status().as_u16());
    span.end();

    response
}
```

### 2. 分布式追踪链路

```rust
use otlp::{Span, TraceContext};

async fn distributed_tracing_example() -> Result<(), Box<dyn std::error::Error>> {
    // 创建根span
    let root_span = OtlpClient::start_span("order_processing", |span| {
        span.set_attribute("order.id", "12345");
        span.set_attribute("customer.id", "67890");
    });

    // 传递追踪上下文
    let trace_context = root_span.context();
    
    // 调用用户服务
    let user_info = call_user_service(&trace_context, "67890").await?;
    root_span.set_attribute("user.name", user_info.name);

    // 调用库存服务
    let inventory_result = call_inventory_service(&trace_context, "12345").await?;
    root_span.set_attribute("inventory.available", inventory_result.available);

    // 调用支付服务
    let payment_result = call_payment_service(&trace_context, &user_info, 100.0).await?;
    root_span.set_attribute("payment.status", payment_result.status);

    root_span.end();
    Ok(())
}

async fn call_user_service(
    trace_context: &TraceContext,
    user_id: &str,
) -> Result<UserInfo, Box<dyn std::error::Error>> {
    let span = OtlpClient::start_span_with_context(
        "user_service.get_user",
        trace_context,
        |span| {
            span.set_attribute("user.id", user_id);
        },
    );

    // 模拟HTTP调用
    let response = reqwest::Client::new()
        .get(&format!("http://user-service/users/{}", user_id))
        .header("traceparent", trace_context.to_header())
        .send()
        .await?;

    let user_info: UserInfo = response.json().await?;
    
    span.set_attribute("user.name", &user_info.name);
    span.end();

    Ok(user_info)
}
```

## 机器学习错误预测实战

### 1. 自定义特征工程

```rust
use otlp::ml_error_prediction::{FeatureExtractor, MLPredictor, PredictionResult};

#[derive(Clone)]
struct CustomFeatureExtractor {
    window_size: Duration,
    feature_cache: HashMap<String, Vec<f64>>,
}

impl FeatureExtractor for CustomFeatureExtractor {
    fn extract_features(&mut self, metrics: &SystemMetrics) -> Vec<f64> {
        let mut features = Vec::new();

        // 基础指标特征
        features.push(metrics.cpu_usage);
        features.push(metrics.memory_usage);
        features.push(metrics.network_io);
        features.push(metrics.disk_io);

        // 时间序列特征
        let key = format!("{}", metrics.timestamp.timestamp());
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

    fn feature_names(&self) -> Vec<String> {
        vec![
            "cpu_usage".to_string(),
            "memory_usage".to_string(),
            "network_io".to_string(),
            "disk_io".to_string(),
            "moving_average".to_string(),
            "trend".to_string(),
        ]
    }
}

impl CustomFeatureExtractor {
    fn update_cache(&mut self, metrics: &SystemMetrics) {
        let key = format!("{}", metrics.timestamp.timestamp());
        let entry = self.feature_cache.entry(key).or_insert_with(Vec::new);
        
        entry.push(metrics.cpu_usage);
        
        // 保持窗口大小
        if entry.len() > 10 {
            entry.remove(0);
        }
    }
}
```

### 2. 模型训练和预测

```rust
use otlp::ml_error_prediction::{MLPredictor, ModelConfig, TrainingData};

async fn ml_prediction_example() -> Result<(), Box<dyn std::error::Error>> {
    // 配置模型
    let model_config = ModelConfig {
        algorithm: "random_forest".to_string(),
        parameters: serde_json::json!({
            "n_estimators": 100,
            "max_depth": 10,
            "min_samples_split": 5,
            "min_samples_leaf": 2
        }),
        ..Default::default()
    };

    // 创建预测器
    let mut predictor = MLPredictor::new(model_config).await?;

    // 加载训练数据
    let training_data = load_training_data().await?;
    predictor.train(&training_data).await?;

    // 实时预测
    let mut feature_extractor = CustomFeatureExtractor {
        window_size: Duration::from_secs(60),
        feature_cache: HashMap::new(),
    };

    loop {
        // 收集系统指标
        let metrics = collect_system_metrics().await?;
        
        // 提取特征
        let features = feature_extractor.extract_features(&metrics);
        
        // 进行预测
        let prediction = predictor.predict(&features).await?;
        
        // 处理预测结果
        if prediction.confidence > 0.8 && prediction.error_probability > 0.7 {
            println!("高风险预警: 错误概率 {:.2}%, 置信度 {:.2}%", 
                prediction.error_probability * 100.0, 
                prediction.confidence * 100.0);
            
            // 触发预防措施
            trigger_preventive_measures(&prediction).await?;
        }

        tokio::time::sleep(Duration::from_secs(10)).await;
    }
}

async fn trigger_preventive_measures(prediction: &PredictionResult) -> Result<(), Box<dyn std::error::Error>> {
    match prediction.error_type.as_str() {
        "memory_leak" => {
            // 触发内存清理
            trigger_memory_cleanup().await?;
        },
        "network_congestion" => {
            // 调整网络配置
            adjust_network_config().await?;
        },
        "cpu_overload" => {
            // 启动负载均衡
            enable_load_balancing().await?;
        },
        _ => {
            // 通用预防措施
            trigger_general_prevention().await?;
        }
    }
    Ok(())
}
```

## 边缘计算场景

### 1. 边缘节点管理

```rust
use otlp::edge_computing::{EdgeNode, EdgeManager, TaskScheduler};

async fn edge_computing_example() -> Result<(), Box<dyn std::error::Error>> {
    // 创建边缘管理器
    let mut edge_manager = EdgeManager::new(EdgeConfig {
        discovery_interval: Duration::from_secs(30),
        heartbeat_timeout: Duration::from_secs(60),
        max_nodes: 100,
        ..Default::default()
    });

    // 启动节点发现
    edge_manager.start_discovery().await?;

    // 注册边缘节点
    let edge_node = EdgeNode {
        id: "edge-001".to_string(),
        location: "datacenter-1".to_string(),
        capabilities: vec!["cpu_intensive".to_string(), "memory_intensive".to_string()],
        resources: ResourceInfo {
            cpu_cores: 8,
            memory_gb: 16,
            storage_gb: 100,
            network_bandwidth_mbps: 1000,
        },
        status: NodeStatus::Healthy,
        last_heartbeat: SystemTime::now(),
    };

    edge_manager.register_node(edge_node).await?;

    // 创建任务调度器
    let task_scheduler = TaskScheduler::new(edge_manager.clone());

    // 提交任务
    let task = Task {
        id: "task-001".to_string(),
        name: "data_processing".to_string(),
        requirements: TaskRequirements {
            cpu_cores: 4,
            memory_gb: 8,
            storage_gb: 50,
            network_bandwidth_mbps: 100,
        },
        priority: TaskPriority::High,
        deadline: SystemTime::now() + Duration::from_secs(3600),
        dependencies: vec![],
    };

    let scheduled_node = task_scheduler.schedule_task(task).await?;
    println!("任务已调度到节点: {}", scheduled_node);

    Ok(())
}
```

### 2. 自适应调度策略

```rust
use otlp::edge_computing::{AdaptiveScheduler, SchedulingStrategy, LoadBalancer};

async fn adaptive_scheduling_example() -> Result<(), Box<dyn std::error::Error>> {
    let mut scheduler = AdaptiveScheduler::new(AdaptiveConfig {
        strategy: SchedulingStrategy::LoadBalanced,
        rebalance_threshold: 0.8,
        rebalance_interval: Duration::from_secs(300),
        ..Default::default()
    });

    // 监控节点负载
    let load_balancer = LoadBalancer::new(LoadBalancerConfig {
        algorithm: "least_connections".to_string(),
        health_check_interval: Duration::from_secs(30),
        ..Default::default()
    });

    // 启动自适应调度
    scheduler.start_adaptive_scheduling().await?;

    // 模拟任务提交
    for i in 0..100 {
        let task = Task {
            id: format!("task-{:03}", i),
            name: "processing_task".to_string(),
            requirements: TaskRequirements {
                cpu_cores: rand::thread_rng().gen_range(1..=4),
                memory_gb: rand::thread_rng().gen_range(1..=8),
                ..Default::default()
            },
            priority: TaskPriority::Normal,
            deadline: SystemTime::now() + Duration::from_secs(1800),
            dependencies: vec![],
        };

        // 使用负载均衡器选择节点
        let selected_node = load_balancer.select_node(&task.requirements).await?;
        
        // 调度任务
        scheduler.schedule_task_to_node(task, selected_node).await?;

        tokio::time::sleep(Duration::from_millis(100)).await;
    }

    Ok(())
}
```

## 性能优化最佳实践

### 1. 连接池优化

```rust
use otlp::transport::{ConnectionPool, PoolConfig};

async fn connection_pool_optimization() -> Result<(), Box<dyn std::error::Error>> {
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

    // 使用连接池
    let mut handles = Vec::new();
    for i in 0..1000 {
        let pool = connection_pool.clone();
        let handle = tokio::spawn(async move {
            let connection = pool.get_connection().await?;
            
            // 执行OTLP请求
            let result = connection.send_trace_data(&create_sample_trace()).await?;
            
            pool.return_connection(connection);
            Ok::<_, Box<dyn std::error::Error>>(result)
        });
        handles.push(handle);
    }

    // 等待所有任务完成
    for handle in handles {
        handle.await??;
    }

    Ok(())
}
```

### 2. 批量处理优化

```rust
use otlp::processing::{BatchProcessor, BatchConfig};

async fn batch_processing_optimization() -> Result<(), Box<dyn std::error::Error>> {
    let batch_config = BatchConfig {
        max_batch_size: 1000,
        max_wait_time: Duration::from_millis(100),
        max_memory_size: 10 * 1024 * 1024, // 10MB
        compression_enabled: true,
        ..Default::default()
    };

    let mut batch_processor = BatchProcessor::new(batch_config);

    // 启动批量处理
    let processor_handle = tokio::spawn(async move {
        batch_processor.start_processing().await
    });

    // 模拟数据产生
    let mut handles = Vec::new();
    for i in 0..10 {
        let handle = tokio::spawn(async move {
            for j in 0..100 {
                let trace_data = create_sample_trace();
                batch_processor.add_trace(trace_data).await?;
                
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
            Ok::<_, Box<dyn std::error::Error>>(())
        });
        handles.push(handle);
    }

    // 等待数据产生完成
    for handle in handles {
        handle.await??;
    }

    // 停止批量处理
    batch_processor.stop().await?;
    processor_handle.await??;

    Ok(())
}
```

## 生产环境部署

### 1. Docker部署配置

```dockerfile
# Dockerfile
FROM rust:1.90-slim as builder

WORKDIR /app
COPY Cargo.toml Cargo.lock ./
COPY src ./src

RUN cargo build --release

FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

COPY --from=builder /app/target/release/otlp-server /usr/local/bin/

EXPOSE 8080 4317 4318

CMD ["otlp-server"]
```

```yaml
# docker-compose.yml
version: '3.8'

services:
  otlp-collector:
    build: .
    ports:
      - "4317:4317"  # gRPC
      - "4318:4318"  # HTTP
      - "8080:8080"  # Admin API
    environment:
      - RUST_LOG=info
      - OTLP_CONFIG_PATH=/config/production.toml
    volumes:
      - ./config:/config
      - ./data:/data
    deploy:
      resources:
        limits:
          cpus: '2'
          memory: 4G
        reservations:
          cpus: '1'
          memory: 2G

  otlp-agent:
    build: .
    command: ["otlp-agent"]
    environment:
      - RUST_LOG=info
      - OTLP_COLLECTOR_ENDPOINT=http://otlp-collector:4317
    depends_on:
      - otlp-collector
    deploy:
      replicas: 3
      resources:
        limits:
          cpus: '0.5'
          memory: 512M
```

### 2. Kubernetes部署配置

```yaml
# k8s-deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otlp-collector
spec:
  replicas: 3
  selector:
    matchLabels:
      app: otlp-collector
  template:
    metadata:
      labels:
        app: otlp-collector
    spec:
      containers:
      - name: otlp-collector
        image: otlp-rust:latest
        ports:
        - containerPort: 4317
          name: grpc
        - containerPort: 4318
          name: http
        - containerPort: 8080
          name: admin
        env:
        - name: RUST_LOG
          value: "info"
        - name: OTLP_CONFIG_PATH
          value: "/config/production.toml"
        resources:
          requests:
            memory: "2Gi"
            cpu: "1000m"
          limits:
            memory: "4Gi"
            cpu: "2000m"
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /ready
            port: 8080
          initialDelaySeconds: 5
          periodSeconds: 5
        volumeMounts:
        - name: config
          mountPath: /config
        - name: data
          mountPath: /data
      volumes:
      - name: config
        configMap:
          name: otlp-config
      - name: data
        persistentVolumeClaim:
          claimName: otlp-data

---
apiVersion: v1
kind: Service
metadata:
  name: otlp-collector
spec:
  selector:
    app: otlp-collector
  ports:
  - name: grpc
    port: 4317
    targetPort: 4317
  - name: http
    port: 4318
    targetPort: 4318
  - name: admin
    port: 8080
    targetPort: 8080
  type: ClusterIP
```

## 监控和告警配置

### 1. Prometheus指标配置

```rust
use otlp::monitoring::{MetricsCollector, AlertManager};

async fn monitoring_setup() -> Result<(), Box<dyn std::error::Error>> {
    let metrics_collector = MetricsCollector::new(MetricsConfig {
        endpoint: "http://prometheus:9090".to_string(),
        interval: Duration::from_secs(15),
        ..Default::default()
    });

    // 注册自定义指标
    metrics_collector.register_counter("otlp_traces_sent_total", "Total traces sent")?;
    metrics_collector.register_histogram("otlp_trace_duration_seconds", "Trace processing duration")?;
    metrics_collector.register_gauge("otlp_active_connections", "Active connections")?;

    // 启动指标收集
    metrics_collector.start().await?;

    // 配置告警
    let alert_manager = AlertManager::new(AlertConfig {
        webhook_url: "http://alertmanager:9093/api/v1/alerts".to_string(),
        ..Default::default()
    });

    // 定义告警规则
    alert_manager.add_rule(AlertRule {
        name: "high_error_rate".to_string(),
        condition: "error_rate > 0.05".to_string(),
        severity: AlertSeverity::Critical,
        message: "Error rate is too high".to_string(),
        duration: Duration::from_secs(300),
    });

    alert_manager.add_rule(AlertRule {
        name: "high_latency".to_string(),
        condition: "p99_latency > 5".to_string(),
        severity: AlertSeverity::Warning,
        message: "P99 latency is too high".to_string(),
        duration: Duration::from_secs(600),
    });

    alert_manager.start().await?;

    Ok(())
}
```

### 2. Grafana仪表板配置

```json
{
  "dashboard": {
    "title": "OTLP Rust Monitoring",
    "panels": [
      {
        "title": "Request Rate",
        "type": "graph",
        "targets": [
          {
            "expr": "rate(otlp_requests_total[5m])",
            "legendFormat": "Requests/sec"
          }
        ]
      },
      {
        "title": "Error Rate",
        "type": "graph",
        "targets": [
          {
            "expr": "rate(otlp_errors_total[5m]) / rate(otlp_requests_total[5m])",
            "legendFormat": "Error Rate"
          }
        ]
      },
      {
        "title": "Latency",
        "type": "graph",
        "targets": [
          {
            "expr": "histogram_quantile(0.95, rate(otlp_latency_seconds_bucket[5m]))",
            "legendFormat": "P95 Latency"
          },
          {
            "expr": "histogram_quantile(0.99, rate(otlp_latency_seconds_bucket[5m]))",
            "legendFormat": "P99 Latency"
          }
        ]
      }
    ]
  }
}
```

## 总结

本文档提供了OTLP Rust项目的高级使用示例和最佳实践，涵盖了：

1. **高级配置管理**：多环境配置、动态配置更新
2. **分布式系统集成**：微服务架构、分布式追踪
3. **机器学习实战**：特征工程、模型训练、实时预测
4. **边缘计算场景**：节点管理、自适应调度
5. **性能优化**：连接池、批量处理
6. **生产部署**：Docker、Kubernetes部署
7. **监控告警**：Prometheus、Grafana集成

这些示例和最佳实践将帮助您在生产环境中更好地使用OTLP Rust项目，实现高性能、高可用的分布式可观测性系统。
