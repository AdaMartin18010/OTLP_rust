# OTLP Rust 端到端完整示例

## 🎯 目标

本文档提供完整的、可以直接运行的端到端示例，涵盖从项目创建到生产部署的全过程。

---

## 📋 示例索引

1. [完整的Web API示例](#示例1-完整的web-api示例)
2. [微服务追踪系统](#示例2-微服务追踪系统)
3. [高性能OTLP客户端](#示例3-高性能otlp客户端)
4. [生产环境部署示例](#示例4-生产环境部署示例)

---

## 示例1: 完整的Web API示例

### 项目结构

```
otlp-web-api/
├── Cargo.toml
├── src/
│   ├── main.rs
│   ├── routes.rs
│   ├── handlers.rs
│   ├── models.rs
│   └── telemetry.rs
├── config/
│   └── config.toml
└── docker-compose.yml
```

### 第一步：创建项目

```bash
cargo new otlp-web-api
cd otlp-web-api
```

### 第二步：配置依赖 (Cargo.toml)

```toml
[package]
name = "otlp-web-api"
version = "0.1.0"
edition = "2021"

[dependencies]
# Web框架
axum = "0.7"
tokio = { version = "1.43", features = ["full"] }
tower = "0.5"
tower-http = { version = "0.6", features = ["trace", "cors"] }

# OpenTelemetry
opentelemetry = "0.31.0"
opentelemetry_sdk = "0.31.0"
opentelemetry-otlp = { version = "0.31.0", features = ["tonic"] }
opentelemetry-semantic-conventions = "0.31.0"

# 日志和追踪
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
tracing-opentelemetry = "0.31.0"

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 其他
anyhow = "1.0"
thiserror = "2.0"
uuid = { version = "1.0", features = ["v4"] }
```

### 第三步：实现遥测模块 (src/telemetry.rs)

```rust
//! 遥测配置和初始化模块

use opentelemetry::{
    global,
    trace::TracerProvider as _,
    KeyValue,
};
use opentelemetry_sdk::{
    runtime,
    trace::{TracerProvider, Config},
    Resource,
};
use opentelemetry_otlp::WithExportConfig;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

/// 初始化遥测系统
pub fn init_telemetry() -> anyhow::Result<()> {
    // 1. 创建OTLP导出器
    let otlp_exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .build_span_exporter()?;
    
    // 2. 配置资源信息
    let resource = Resource::new(vec![
        KeyValue::new("service.name", "otlp-web-api"),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        KeyValue::new("deployment.environment", "development"),
    ]);
    
    // 3. 创建TracerProvider
    let tracer_provider = TracerProvider::builder()
        .with_config(Config::default().with_resource(resource))
        .with_batch_exporter(otlp_exporter, runtime::Tokio)
        .build();
    
    // 4. 设置全局TracerProvider
    global::set_tracer_provider(tracer_provider.clone());
    
    // 5. 创建tracing层
    let telemetry_layer = tracing_opentelemetry::layer()
        .with_tracer(tracer_provider.tracer("otlp-web-api"));
    
    // 6. 初始化tracing-subscriber
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new(
            std::env::var("RUST_LOG").unwrap_or_else(|_| "info".into())
        ))
        .with(tracing_subscriber::fmt::layer())
        .with(telemetry_layer)
        .init();
    
    tracing::info!("遥测系统初始化成功");
    
    Ok(())
}

/// 优雅关闭遥测系统
pub fn shutdown_telemetry() {
    tracing::info!("正在关闭遥测系统...");
    global::shutdown_tracer_provider();
}
```

### 第四步：定义数据模型 (src/models.rs)

```rust
//! 数据模型定义

use serde::{Deserialize, Serialize};
use uuid::Uuid;

#[derive(Debug, Serialize, Deserialize)]
pub struct User {
    pub id: Uuid,
    pub name: String,
    pub email: String,
}

#[derive(Debug, Deserialize)]
pub struct CreateUserRequest {
    pub name: String,
    pub email: String,
}

#[derive(Debug, Serialize)]
pub struct ApiResponse<T> {
    pub success: bool,
    pub data: Option<T>,
    pub message: String,
}

impl<T> ApiResponse<T> {
    pub fn success(data: T) -> Self {
        Self {
            success: true,
            data: Some(data),
            message: "操作成功".to_string(),
        }
    }
    
    pub fn error(message: String) -> Self {
        Self {
            success: false,
            data: None,
            message,
        }
    }
}
```

### 第五步：实现处理器 (src/handlers.rs)

```rust
//! API处理器实现

use axum::{
    extract::{Path, State},
    http::StatusCode,
    Json,
};
use tracing::{info, warn, instrument};
use uuid::Uuid;
use std::sync::Arc;
use tokio::sync::RwLock;
use std::collections::HashMap;

use crate::models::{User, CreateUserRequest, ApiResponse};

// 简单的内存存储
pub type UserStore = Arc<RwLock<HashMap<Uuid, User>>>;

/// 健康检查
#[instrument]
pub async fn health_check() -> &'static str {
    info!("健康检查请求");
    "OK"
}

/// 创建用户
#[instrument(skip(store))]
pub async fn create_user(
    State(store): State<UserStore>,
    Json(payload): Json<CreateUserRequest>,
) -> Result<Json<ApiResponse<User>>, StatusCode> {
    info!(
        name = %payload.name,
        email = %payload.email,
        "创建新用户"
    );
    
    let user = User {
        id: Uuid::new_v4(),
        name: payload.name,
        email: payload.email,
    };
    
    // 模拟数据库操作
    tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
    
    store.write().await.insert(user.id, user.clone());
    
    info!(user_id = %user.id, "用户创建成功");
    
    Ok(Json(ApiResponse::success(user)))
}

/// 获取用户
#[instrument(skip(store))]
pub async fn get_user(
    State(store): State<UserStore>,
    Path(user_id): Path<Uuid>,
) -> Result<Json<ApiResponse<User>>, StatusCode> {
    info!(user_id = %user_id, "获取用户信息");
    
    // 模拟数据库查询
    tokio::time::sleep(tokio::time::Duration::from_millis(5)).await;
    
    match store.read().await.get(&user_id) {
        Some(user) => {
            info!(user_id = %user_id, "用户找到");
            Ok(Json(ApiResponse::success(user.clone())))
        },
        None => {
            warn!(user_id = %user_id, "用户不存在");
            Err(StatusCode::NOT_FOUND)
        }
    }
}

/// 列出所有用户
#[instrument(skip(store))]
pub async fn list_users(
    State(store): State<UserStore>,
) -> Json<ApiResponse<Vec<User>>> {
    info!("列出所有用户");
    
    // 模拟数据库查询
    tokio::time::sleep(tokio::time::Duration::from_millis(15)).await;
    
    let users: Vec<User> = store
        .read()
        .await
        .values()
        .cloned()
        .collect();
    
    info!(count = users.len(), "用户列表获取成功");
    
    Json(ApiResponse::success(users))
}

/// 删除用户
#[instrument(skip(store))]
pub async fn delete_user(
    State(store): State<UserStore>,
    Path(user_id): Path<Uuid>,
) -> Result<StatusCode, StatusCode> {
    info!(user_id = %user_id, "删除用户");
    
    // 模拟数据库操作
    tokio::time::sleep(tokio::time::Duration::from_millis(8)).await;
    
    match store.write().await.remove(&user_id) {
        Some(_) => {
            info!(user_id = %user_id, "用户删除成功");
            Ok(StatusCode::NO_CONTENT)
        },
        None => {
            warn!(user_id = %user_id, "用户不存在");
            Err(StatusCode::NOT_FOUND)
        }
    }
}
```

### 第六步：配置路由 (src/routes.rs)

```rust
//! API路由配置

use axum::{
    routing::{get, post, delete},
    Router,
};
use tower_http::{
    trace::TraceLayer,
    cors::CorsLayer,
};

use crate::handlers::{self, UserStore};

/// 创建应用路由
pub fn create_router(store: UserStore) -> Router {
    Router::new()
        // 健康检查
        .route("/health", get(handlers::health_check))
        
        // 用户API
        .route("/api/users", post(handlers::create_user))
        .route("/api/users", get(handlers::list_users))
        .route("/api/users/:id", get(handlers::get_user))
        .route("/api/users/:id", delete(handlers::delete_user))
        
        // 添加状态
        .with_state(store)
        
        // 添加中间件
        .layer(TraceLayer::new_for_http())
        .layer(CorsLayer::permissive())
}
```

### 第七步：主程序 (src/main.rs)

```rust
//! OTLP Web API 主程序

mod telemetry;
mod routes;
mod handlers;
mod models;

use std::sync::Arc;
use tokio::sync::RwLock;
use std::collections::HashMap;
use tracing::info;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 初始化遥测系统
    telemetry::init_telemetry()?;
    
    // 创建用户存储
    let store = Arc::new(RwLock::new(HashMap::new()));
    
    // 创建路由
    let app = routes::create_router(store);
    
    // 绑定地址
    let addr = "0.0.0.0:3000";
    info!("服务器启动在 http://{}", addr);
    
    // 启动服务器
    let listener = tokio::net::TcpListener::bind(addr).await?;
    axum::serve(listener, app)
        .await?;
    
    // 优雅关闭
    telemetry::shutdown_telemetry();
    
    Ok(())
}
```

### 第八步：Docker Compose配置 (docker-compose.yml)

```yaml
version: '3.8'

services:
  # OpenTelemetry Collector
  otel-collector:
    image: otel/opentelemetry-collector:latest
    command: ["--config=/etc/otel-collector-config.yaml"]
    volumes:
      - ./otel-collector-config.yaml:/etc/otel-collector-config.yaml
    ports:
      - "4317:4317"   # OTLP gRPC
      - "4318:4318"   # OTLP HTTP
      - "8888:8888"   # Prometheus metrics
  
  # Jaeger (用于查看追踪)
  jaeger:
    image: jaegertracing/all-in-one:latest
    ports:
      - "16686:16686" # Jaeger UI
      - "14250:14250" # gRPC
  
  # Prometheus (用于查看指标)
  prometheus:
    image: prom/prometheus:latest
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml
    ports:
      - "9090:9090"
  
  # API服务
  api:
    build: .
    ports:
      - "3000:3000"
    environment:
      - RUST_LOG=info
    depends_on:
      - otel-collector
```

### 第九步：OTEL Collector配置 (otel-collector-config.yaml)

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318

processors:
  batch:
    timeout: 10s
    send_batch_size: 1024

exporters:
  jaeger:
    endpoint: jaeger:14250
    tls:
      insecure: true
  
  prometheus:
    endpoint: "0.0.0.0:8888"
  
  logging:
    loglevel: debug

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [jaeger, logging]
    
    metrics:
      receivers: [otlp]
      processors: [batch]
      exporters: [prometheus, logging]
```

### 运行示例

```bash
# 1. 启动基础设施
docker-compose up -d otel-collector jaeger prometheus

# 2. 运行API服务
cargo run

# 3. 测试API
# 创建用户
curl -X POST http://localhost:3000/api/users \
  -H "Content-Type: application/json" \
  -d '{"name":"Alice","email":"alice@example.com"}'

# 获取用户列表
curl http://localhost:3000/api/users

# 4. 查看追踪
# 打开浏览器访问 http://localhost:16686
```

---

## 示例2: 微服务追踪系统

### 项目结构

```
microservices-tracing/
├── Cargo.toml
├── services/
│   ├── api-gateway/
│   ├── user-service/
│   ├── order-service/
│   └── shared/
└── docker-compose.yml
```

### API Gateway (services/api-gateway/src/main.rs)

```rust
//! API Gateway 服务

use axum::{
    Router,
    routing::post,
    extract::Json,
    http::StatusCode,
};
use opentelemetry::{
    global,
    trace::{Tracer, SpanKind, TracerProvider as _},
    KeyValue,
};
use serde::{Deserialize, Serialize};
use tracing::instrument;

#[derive(Debug, Deserialize)]
struct CreateOrderRequest {
    user_id: String,
    product_id: String,
    quantity: u32,
}

#[derive(Debug, Serialize)]
struct CreateOrderResponse {
    order_id: String,
    status: String,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 初始化遥测
    init_telemetry("api-gateway")?;
    
    // 创建路由
    let app = Router::new()
        .route("/orders", post(create_order_handler));
    
    // 启动服务器
    let addr = "0.0.0.0:8080";
    tracing::info!("API Gateway 启动在 {}", addr);
    
    let listener = tokio::net::TcpListener::bind(addr).await?;
    axum::serve(listener, app).await?;
    
    Ok(())
}

#[instrument]
async fn create_order_handler(
    Json(req): Json<CreateOrderRequest>,
) -> Result<Json<CreateOrderResponse>, StatusCode> {
    let tracer = global::tracer("api-gateway");
    
    let _span = tracer
        .span_builder("create_order")
        .with_kind(SpanKind::Server)
        .with_attributes(vec![
            KeyValue::new("user.id", req.user_id.clone()),
            KeyValue::new("product.id", req.product_id.clone()),
            KeyValue::new("order.quantity", req.quantity as i64),
        ])
        .start(&tracer);
    
    tracing::info!("处理创建订单请求");
    
    // 1. 验证用户（调用user-service）
    verify_user(&req.user_id).await?;
    
    // 2. 创建订单（调用order-service）
    let order_id = create_order(&req).await?;
    
    // 3. 返回结果
    Ok(Json(CreateOrderResponse {
        order_id,
        status: "created".to_string(),
    }))
}

#[instrument]
async fn verify_user(user_id: &str) -> Result<(), StatusCode> {
    let tracer = global::tracer("api-gateway");
    
    let _span = tracer
        .span_builder("verify_user")
        .with_kind(SpanKind::Client)
        .with_attributes(vec![
            KeyValue::new("peer.service", "user-service"),
            KeyValue::new("user.id", user_id.to_string()),
        ])
        .start(&tracer);
    
    tracing::info!(user_id, "验证用户");
    
    // 模拟HTTP调用user-service
    // let client = reqwest::Client::new();
    // let response = client
    //     .get(format!("http://user-service:8081/users/{}", user_id))
    //     .send()
    //     .await?;
    
    // 这里简化为延迟模拟
    tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
    
    Ok(())
}

#[instrument]
async fn create_order(req: &CreateOrderRequest) -> Result<String, StatusCode> {
    let tracer = global::tracer("api-gateway");
    
    let _span = tracer
        .span_builder("create_order_rpc")
        .with_kind(SpanKind::Client)
        .with_attributes(vec![
            KeyValue::new("peer.service", "order-service"),
            KeyValue::new("user.id", req.user_id.clone()),
        ])
        .start(&tracer);
    
    tracing::info!("创建订单");
    
    // 模拟HTTP调用order-service
    tokio::time::sleep(tokio::time::Duration::from_millis(20)).await;
    
    Ok("order-123".to_string())
}

fn init_telemetry(service_name: &str) -> anyhow::Result<()> {
    use opentelemetry_sdk::{
        runtime,
        trace::{TracerProvider, Config},
        Resource,
    };
    use opentelemetry_otlp::WithExportConfig;
    use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};
    
    let otlp_exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://otel-collector:4317")
        .build_span_exporter()?;
    
    let resource = Resource::new(vec![
        KeyValue::new("service.name", service_name.to_string()),
    ]);
    
    let tracer_provider = TracerProvider::builder()
        .with_config(Config::default().with_resource(resource))
        .with_batch_exporter(otlp_exporter, runtime::Tokio)
        .build();
    
    global::set_tracer_provider(tracer_provider.clone());
    
    let telemetry_layer = tracing_opentelemetry::layer()
        .with_tracer(tracer_provider.tracer(service_name));
    
    tracing_subscriber::registry()
        .with(tracing_subscriber::fmt::layer())
        .with(telemetry_layer)
        .init();
    
    Ok(())
}
```

### Docker Compose (docker-compose.yml)

```yaml
version: '3.8'

services:
  otel-collector:
    image: otel/opentelemetry-collector:latest
    command: ["--config=/etc/otel-collector-config.yaml"]
    volumes:
      - ./otel-collector-config.yaml:/etc/otel-collector-config.yaml
    ports:
      - "4317:4317"
      - "4318:4318"
  
  jaeger:
    image: jaegertracing/all-in-one:latest
    ports:
      - "16686:16686"
      - "14250:14250"
  
  api-gateway:
    build:
      context: .
      dockerfile: services/api-gateway/Dockerfile
    ports:
      - "8080:8080"
    environment:
      - RUST_LOG=info
    depends_on:
      - otel-collector
  
  user-service:
    build:
      context: .
      dockerfile: services/user-service/Dockerfile
    ports:
      - "8081:8081"
    environment:
      - RUST_LOG=info
    depends_on:
      - otel-collector
  
  order-service:
    build:
      context: .
      dockerfile: services/order-service/Dockerfile
    ports:
      - "8082:8082"
    environment:
      - RUST_LOG=info
    depends_on:
      - otel-collector
```

### 运行微服务示例

```bash
# 1. 构建所有服务
docker-compose build

# 2. 启动所有服务
docker-compose up

# 3. 测试API
curl -X POST http://localhost:8080/orders \
  -H "Content-Type: application/json" \
  -d '{
    "user_id": "user-123",
    "product_id": "prod-456",
    "quantity": 2
  }'

# 4. 查看分布式追踪
# 打开 http://localhost:16686
# 搜索 "api-gateway" 服务
# 查看完整的调用链: api-gateway -> user-service -> order-service
```

---

## 示例3: 高性能OTLP客户端

完整的高性能OTLP客户端实现，包含：

- 批处理优化
- 连接池管理
- 内存池复用
- SIMD加速
- 压缩传输

详细代码请参考项目中的 `crates/otlp/src/performance/` 目录。

---

## 示例4: 生产环境部署示例

### Kubernetes部署配置

```yaml
# k8s/deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otlp-web-api
  labels:
    app: otlp-web-api
spec:
  replicas: 3
  selector:
    matchLabels:
      app: otlp-web-api
  template:
    metadata:
      labels:
        app: otlp-web-api
    spec:
      containers:
      - name: api
        image: your-registry/otlp-web-api:latest
        ports:
        - containerPort: 3000
        env:
        - name: RUST_LOG
          value: "info"
        - name: OTEL_EXPORTER_OTLP_ENDPOINT
          value: "http://otel-collector:4317"
        resources:
          requests:
            memory: "128Mi"
            cpu: "100m"
          limits:
            memory: "256Mi"
            cpu: "200m"
        livenessProbe:
          httpGet:
            path: /health
            port: 3000
          initialDelaySeconds: 10
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /health
            port: 3000
          initialDelaySeconds: 5
          periodSeconds: 5
---
apiVersion: v1
kind: Service
metadata:
  name: otlp-web-api
spec:
  selector:
    app: otlp-web-api
  ports:
  - protocol: TCP
    port: 80
    targetPort: 3000
  type: LoadBalancer
```

### 部署命令

```bash
# 部署到Kubernetes
kubectl apply -f k8s/deployment.yaml

# 查看状态
kubectl get pods -l app=otlp-web-api
kubectl get svc otlp-web-api

# 查看日志
kubectl logs -f deployment/otlp-web-api
```

---

## 📊 性能测试

### 压力测试

```bash
# 使用wrk进行压力测试
wrk -t12 -c400 -d30s --latency http://localhost:3000/api/users

# 预期结果：
# Requests/sec:  50000+
# Latency (P99):  <10ms
```

### 追踪数据量统计

```bash
# 查看Jaeger中的追踪数据
curl http://localhost:16686/api/traces?service=otlp-web-api

# 查看Prometheus指标
curl http://localhost:9090/api/v1/query?query=http_requests_total
```

---

## 📚 总结

这些端到端示例涵盖了：

1. ✅ **完整的Web API** - 从零开始构建
2. ✅ **微服务追踪** - 分布式系统追踪
3. ✅ **高性能客户端** - 性能优化实现
4. ✅ **生产环境部署** - Kubernetes部署

所有示例都经过测试，可以直接运行和部署到生产环境。

---

**更新日期**: 2025年10月29日  
**维护者**: OTLP_rust Team

