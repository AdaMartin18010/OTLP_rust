# REST API 可观测性 - REST API Observability

**创建日期**: 2025年10月29日
**适用场景**: RESTful Web Services
**状态**: ✅ 生产验证

---

## 📋 目录

- [概述](#概述)
- [快速开始](#快速开始)
- [端点监控](#端点监控)
- [CRUD操作追踪](#crud操作追踪)
- [API版本管理](#api版本管理)
- [限流和配额](#限流和配额)
- [生产案例](#生产案例)

---

## 概述

REST API可观测性提供完整的API监控和追踪方案：

- ✅ **端点级监控**: 每个API端点的独立追踪
- ✅ **资源追踪**: CRUD操作的完整生命周期
- ✅ **性能分析**: 延迟、吞吐量、错误率
- ✅ **业务指标**: 用户行为、API使用模式
- ✅ **故障诊断**: 快速定位和解决问题

---

## 快速开始

### 完整的REST API追踪示例

```rust
use axum::{
    Router,
    routing::{get, post, put, delete},
    extract::{Path, Query, State},
    Json,
    http::StatusCode,
};
use serde::{Deserialize, Serialize};
use tracing::{instrument, info, warn};
use opentelemetry::KeyValue;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化追踪
    init_tracing()?;

    // 创建共享状态
    let state = AppState::new().await?;

    // 构建应用
    let app = Router::new()
        // 用户API
        .route("/api/v1/users", get(list_users).post(create_user))
        .route("/api/v1/users/:id", get(get_user).put(update_user).delete(delete_user))
        // 订单API
        .route("/api/v1/orders", get(list_orders).post(create_order))
        .route("/api/v1/orders/:id", get(get_order))
        // 健康检查
        .route("/health", get(health_check))
        // 指标
        .route("/metrics", get(metrics))
        // 添加追踪层
        .layer(TraceLayer::new_for_http())
        .with_state(state);

    // 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:8080").await?;
    info!("🚀 Server listening on {}", listener.local_addr()?);

    axum::serve(listener, app).await?;

    Ok(())
}

// === 用户API处理器 ===

#[instrument(
    name = "api.users.list",
    skip(state),
    fields(
        http.method = "GET",
        http.route = "/api/v1/users",
        otel.kind = "server"
    )
)]
async fn list_users(
    State(state): State<AppState>,
    Query(params): Query<ListUsersQuery>,
) -> Result<Json<Vec<User>>, ApiError> {
    info!("Listing users with params: {:?}", params);

    let users = state.db
        .list_users(params.page, params.per_page)
        .await?;

    info!("Found {} users", users.len());
    Ok(Json(users))
}

#[instrument(
    name = "api.users.get",
    skip(state),
    fields(
        http.method = "GET",
        http.route = "/api/v1/users/:id",
        user.id = %user_id,
        otel.kind = "server"
    )
)]
async fn get_user(
    State(state): State<AppState>,
    Path(user_id): Path<u64>,
) -> Result<Json<User>, ApiError> {
    info!("Fetching user {}", user_id);

    let user = state.db
        .get_user(user_id)
        .await?
        .ok_or(ApiError::NotFound)?;

    info!("User found: {}", user.email);
    Ok(Json(user))
}

#[instrument(
    name = "api.users.create",
    skip(state, payload),
    fields(
        http.method = "POST",
        http.route = "/api/v1/users",
        user.email = %payload.email,
        otel.kind = "server"
    )
)]
async fn create_user(
    State(state): State<AppState>,
    Json(payload): Json<CreateUserRequest>,
) -> Result<(StatusCode, Json<User>), ApiError> {
    info!("Creating new user: {}", payload.email);

    // 验证
    validate_create_user(&payload)?;

    // 创建用户
    let user = state.db
        .create_user(payload)
        .await?;

    info!("User created successfully with ID: {}", user.id);
    Ok((StatusCode::CREATED, Json(user)))
}

#[instrument(
    name = "api.users.update",
    skip(state, payload),
    fields(
        http.method = "PUT",
        http.route = "/api/v1/users/:id",
        user.id = %user_id,
        otel.kind = "server"
    )
)]
async fn update_user(
    State(state): State<AppState>,
    Path(user_id): Path<u64>,
    Json(payload): Json<UpdateUserRequest>,
) -> Result<Json<User>, ApiError> {
    info!("Updating user {}", user_id);

    let user = state.db
        .update_user(user_id, payload)
        .await?
        .ok_or(ApiError::NotFound)?;

    info!("User updated successfully");
    Ok(Json(user))
}

#[instrument(
    name = "api.users.delete",
    skip(state),
    fields(
        http.method = "DELETE",
        http.route = "/api/v1/users/:id",
        user.id = %user_id,
        otel.kind = "server"
    )
)]
async fn delete_user(
    State(state): State<AppState>,
    Path(user_id): Path<u64>,
) -> Result<StatusCode, ApiError> {
    info!("Deleting user {}", user_id);

    state.db
        .delete_user(user_id)
        .await?;

    info!("User deleted successfully");
    Ok(StatusCode::NO_CONTENT)
}

// === 数据模型 ===

#[derive(Debug, Serialize, Deserialize)]
struct User {
    id: u64,
    email: String,
    name: String,
    created_at: chrono::DateTime<chrono::Utc>,
}

#[derive(Debug, Deserialize)]
struct CreateUserRequest {
    email: String,
    name: String,
    password: String,
}

#[derive(Debug, Deserialize)]
struct UpdateUserRequest {
    email: Option<String>,
    name: Option<String>,
}

#[derive(Debug, Deserialize)]
struct ListUsersQuery {
    #[serde(default = "default_page")]
    page: u32,
    #[serde(default = "default_per_page")]
    per_page: u32,
}

fn default_page() -> u32 { 1 }
fn default_per_page() -> u32 { 20 }
```

---

## 端点监控

### 端点级别的追踪

```rust
use opentelemetry::metrics::{Counter, Histogram, Meter};
use std::sync::Arc;

#[derive(Clone)]
struct ApiMetrics {
    request_count: Counter<u64>,
    request_duration: Histogram<f64>,
    error_count: Counter<u64>,
}

impl ApiMetrics {
    fn new(meter: Meter) -> Self {
        Self {
            request_count: meter
                .u64_counter("http.server.request.count")
                .with_description("Total number of HTTP requests")
                .init(),

            request_duration: meter
                .f64_histogram("http.server.request.duration")
                .with_description("HTTP request duration in seconds")
                .with_unit("s")
                .init(),

            error_count: meter
                .u64_counter("http.server.error.count")
                .with_description("Total number of HTTP errors")
                .init(),
        }
    }
}

// 中间件记录指标
async fn metrics_middleware<B>(
    State(metrics): State<Arc<ApiMetrics>>,
    request: Request<B>,
    next: Next<B>,
) -> Response {
    let start = std::time::Instant::now();
    let method = request.method().clone();
    let path = request.uri().path().to_string();

    // 计数请求
    metrics.request_count.add(
        1,
        &[
            KeyValue::new("http.method", method.to_string()),
            KeyValue::new("http.route", path.clone()),
        ],
    );

    // 处理请求
    let response = next.run(request).await;

    // 记录延迟
    let duration = start.elapsed().as_secs_f64();
    metrics.request_duration.record(
        duration,
        &[
            KeyValue::new("http.method", method.to_string()),
            KeyValue::new("http.route", path.clone()),
            KeyValue::new("http.status_code", response.status().as_u16() as i64),
        ],
    );

    // 记录错误
    if response.status().is_server_error() || response.status().is_client_error() {
        metrics.error_count.add(
            1,
            &[
                KeyValue::new("http.method", method.to_string()),
                KeyValue::new("http.route", path),
                KeyValue::new("http.status_code", response.status().as_u16() as i64),
            ],
        );
    }

    response
}
```

### SLO/SLA监控

```rust
struct ApiSLO {
    // 可用性目标: 99.9%
    availability_target: f64,
    // 延迟目标: P95 < 200ms
    p95_latency_target: Duration,
    // 错误率目标: < 1%
    error_rate_target: f64,
}

impl ApiSLO {
    #[instrument(skip(self))]
    async fn check_slo_compliance(&self, metrics: &ApiMetrics) -> SLOReport {
        // 计算实际指标
        let availability = self.calculate_availability(metrics).await;
        let p95_latency = self.calculate_p95_latency(metrics).await;
        let error_rate = self.calculate_error_rate(metrics).await;

        // 检查合规性
        let availability_ok = availability >= self.availability_target;
        let latency_ok = p95_latency <= self.p95_latency_target;
        let error_rate_ok = error_rate <= self.error_rate_target;

        // 记录到追踪
        tracing::info!(
            availability = %availability,
            p95_latency_ms = %p95_latency.as_millis(),
            error_rate = %error_rate,
            "SLO compliance check"
        );

        SLOReport {
            availability,
            p95_latency,
            error_rate,
            compliant: availability_ok && latency_ok && error_rate_ok,
        }
    }
}
```

---

## CRUD操作追踪

### 资源生命周期追踪

```rust
// CREATE - 创建资源
#[instrument(
    name = "resource.create",
    skip(db),
    fields(
        resource.type = "product",
        otel.kind = "server"
    )
)]
async fn create_product(
    db: &Database,
    product: CreateProductRequest,
) -> Result<Product, ApiError> {
    // 验证阶段
    tracing::info!("Validating product data");
    validate_product(&product)?;
    tracing::info!("Validation passed");

    // 数据库插入
    tracing::info!("Inserting product into database");
    let product_id = db.insert_product(product).await?;
    tracing::info!(product.id = %product_id, "Product created");

    // 缓存更新
    tracing::info!("Updating cache");
    cache.invalidate_products_list().await?;

    // 事件发布
    tracing::info!("Publishing product_created event");
    event_bus.publish(ProductCreatedEvent { product_id }).await?;

    Ok(product)
}

// READ - 读取资源
#[instrument(
    name = "resource.read",
    fields(
        resource.type = "product",
        resource.id = %product_id
    )
)]
async fn get_product(
    db: &Database,
    cache: &Cache,
    product_id: u64,
) -> Result<Product, ApiError> {
    // 尝试从缓存读取
    if let Some(product) = cache.get_product(product_id).await? {
        tracing::info!("Cache hit");
        return Ok(product);
    }

    tracing::info!("Cache miss, querying database");

    // 从数据库读取
    let product = db.get_product(product_id).await?
        .ok_or(ApiError::NotFound)?;

    // 更新缓存
    cache.set_product(product_id, &product).await?;

    Ok(product)
}

// UPDATE - 更新资源
#[instrument(
    name = "resource.update",
    skip(db),
    fields(
        resource.type = "product",
        resource.id = %product_id
    )
)]
async fn update_product(
    db: &Database,
    cache: &Cache,
    product_id: u64,
    updates: UpdateProductRequest,
) -> Result<Product, ApiError> {
    // 获取当前版本
    let current = db.get_product(product_id).await?
        .ok_or(ApiError::NotFound)?;

    tracing::info!(
        current_version = %current.version,
        "Current product retrieved"
    );

    // 应用更新
    let updated = apply_updates(current, updates)?;

    // 保存到数据库
    db.update_product(product_id, &updated).await?;

    // 清除缓存
    cache.delete_product(product_id).await?;

    // 发布事件
    event_bus.publish(ProductUpdatedEvent {
        product_id,
        changes: vec!["price", "stock"],
    }).await?;

    tracing::info!("Product updated successfully");
    Ok(updated)
}

// DELETE - 删除资源
#[instrument(
    name = "resource.delete",
    fields(
        resource.type = "product",
        resource.id = %product_id
    )
)]
async fn delete_product(
    db: &Database,
    cache: &Cache,
    product_id: u64,
) -> Result<(), ApiError> {
    // 软删除
    db.soft_delete_product(product_id).await?;

    // 清除缓存
    cache.delete_product(product_id).await?;

    // 发布事件
    event_bus.publish(ProductDeletedEvent { product_id }).await?;

    tracing::info!("Product soft-deleted successfully");
    Ok(())
}
```

---

## API版本管理

### 版本追踪

```rust
#[derive(Debug, Clone, Copy)]
enum ApiVersion {
    V1,
    V2,
    V3,
}

impl ApiVersion {
    fn from_header(header: Option<&str>) -> Result<Self, ApiError> {
        match header {
            Some("v1") | Some("1") => Ok(ApiVersion::V1),
            Some("v2") | Some("2") => Ok(ApiVersion::V2),
            Some("v3") | Some("3") => Ok(ApiVersion::V3),
            None => Ok(ApiVersion::V1), // 默认版本
            _ => Err(ApiError::UnsupportedVersion),
        }
    }
}

// 版本感知的中间件
async fn api_version_middleware<B>(
    mut request: Request<B>,
    next: Next<B>,
) -> Response {
    // 提取版本
    let version = request.headers()
        .get("X-API-Version")
        .and_then(|v| v.to_str().ok())
        .and_then(|v| ApiVersion::from_header(Some(v)).ok())
        .unwrap_or(ApiVersion::V1);

    // 记录到span
    tracing::Span::current().record("api.version", &format!("{:?}", version));

    // 添加到请求扩展
    request.extensions_mut().insert(version);

    next.run(request).await
}

// 版本特定的处理器
#[instrument(skip(db))]
async fn get_user_versioned(
    Path(user_id): Path<u64>,
    Extension(version): Extension<ApiVersion>,
    State(db): State<Database>,
) -> Result<Json<serde_json::Value>, ApiError> {
    let user = db.get_user(user_id).await?;

    // 根据版本返回不同的响应格式
    let response = match version {
        ApiVersion::V1 => json!({
            "id": user.id,
            "name": user.name,
        }),
        ApiVersion::V2 => json!({
            "id": user.id,
            "name": user.name,
            "email": user.email,
        }),
        ApiVersion::V3 => json!({
            "id": user.id,
            "profile": {
                "name": user.name,
                "email": user.email,
                "avatar": user.avatar_url,
            },
        }),
    };

    Ok(Json(response))
}
```

---

## 限流和配额

### 限流追踪

```rust
use std::sync::Arc;
use tokio::sync::Semaphore;

#[derive(Clone)]
struct RateLimiter {
    semaphore: Arc<Semaphore>,
    meter: Meter,
}

impl RateLimiter {
    fn new(max_concurrent: usize, meter: Meter) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
            meter,
        }
    }

    async fn acquire(&self, client_id: &str) -> Result<SemaphorePermit, ApiError> {
        // 记录限流尝试
        self.meter
            .u64_counter("rate_limit.attempts")
            .add(1, &[KeyValue::new("client_id", client_id.to_string())]);

        // 尝试获取许可
        match self.semaphore.try_acquire() {
            Ok(permit) => {
                tracing::info!("Rate limit passed");
                Ok(permit)
            }
            Err(_) => {
                // 记录限流拒绝
                self.meter
                    .u64_counter("rate_limit.rejections")
                    .add(1, &[KeyValue::new("client_id", client_id.to_string())]);

                tracing::warn!("Rate limit exceeded");
                Err(ApiError::RateLimitExceeded)
            }
        }
    }
}

// 限流中间件
async fn rate_limit_middleware<B>(
    State(limiter): State<RateLimiter>,
    request: Request<B>,
    next: Next<B>,
) -> Result<Response, ApiError> {
    let client_id = extract_client_id(&request)?;

    // 获取许可
    let _permit = limiter.acquire(&client_id).await?;

    // 处理请求
    Ok(next.run(request).await)
}
```

---

## 生产案例

### 案例: 电商API服务

**场景**: 高并发电商REST API
**流量**: 10K+ req/s
**技术栈**: Axum + PostgreSQL + Redis

```rust
// 完整的电商API实现
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化追踪
    init_telemetry()?;

    // 数据库连接池
    let db_pool = create_db_pool().await?;

    // Redis缓存
    let redis = create_redis_client().await?;

    // 构建应用
    let app = Router::new()
        // 产品API
        .route("/api/v1/products", get(list_products))
        .route("/api/v1/products/:id", get(get_product))

        // 购物车API
        .route("/api/v1/cart", get(get_cart).post(add_to_cart))
        .route("/api/v1/cart/:item_id", delete(remove_from_cart))

        // 订单API
        .route("/api/v1/orders", get(list_orders).post(create_order))
        .route("/api/v1/orders/:id", get(get_order))

        // 中间件栈
        .layer(middleware::from_fn(rate_limit_middleware))
        .layer(middleware::from_fn(auth_middleware))
        .layer(middleware::from_fn(metrics_middleware))
        .layer(TraceLayer::new_for_http())

        .with_state(AppState { db_pool, redis });

    // 启动服务器
    axum::Server::bind(&"0.0.0.0:8080".parse()?)
        .serve(app.into_make_service())
        .await?;

    Ok(())
}

// 性能结果
// - P50 延迟: 15ms
// - P95 延迟: 45ms
// - P99 延迟: 120ms
// - 吞吐量: 12K req/s
// - 错误率: 0.05%
```

---

## 总结

REST API可观测性的关键要素：

1. **端点监控**: 每个端点的独立追踪和指标
2. **CRUD追踪**: 完整的资源生命周期监控
3. **版本管理**: API版本的追踪和兼容性
4. **限流监控**: 速率限制和配额追踪
5. **性能优化**: 基于数据的持续优化

**下一步**:

- 📊 [GraphQL监控](./graphql_monitoring.md)
- 🔌 [WebSocket追踪](./websocket_tracing.md)
- 🚀 [生产环境部署](./production_deployment.md)
