# GraphQL Rust 完整追踪集成指南

## 目录

- [GraphQL Rust 完整追踪集成指南](#graphql-rust-完整追踪集成指南)
  - [目录](#目录)
  - [一、GraphQL 架构与追踪概述](#一graphql-架构与追踪概述)
    - [1.1 GraphQL 核心组件](#11-graphql-核心组件)
    - [1.2 追踪目标](#12-追踪目标)
  - [二、依赖配置](#二依赖配置)
    - [2.1 Cargo.toml](#21-cargotoml)
  - [三、GraphQL 语义约定](#三graphql-语义约定)
    - [3.1 OpenTelemetry 属性](#31-opentelemetry-属性)
  - [四、基础追踪实现](#四基础追踪实现)
    - [4.1 OpenTelemetry 扩展](#41-opentelemetry-扩展)
  - [五、查询追踪](#五查询追踪)
    - [5.1 Schema 定义](#51-schema-定义)
  - [六、变更追踪](#六变更追踪)
    - [6.1 Mutation 定义](#61-mutation-定义)
  - [七、订阅追踪](#七订阅追踪)
    - [7.1 Subscription 定义](#71-subscription-定义)
  - [八、解析器追踪](#八解析器追踪)
    - [8.1 自定义解析器](#81-自定义解析器)
  - [九、数据加载器追踪](#九数据加载器追踪)
    - [9.1 DataLoader 实现](#91-dataloader-实现)
  - [十、错误处理](#十错误处理)
    - [10.1 自定义错误](#101-自定义错误)
  - [十一、性能监控](#十一性能监控)
    - [11.1 性能指标](#111-性能指标)
  - [十二、生产环境完整示例](#十二生产环境完整示例)
    - [12.1 完整应用](#121-完整应用)
    - [12.2 示例查询](#122-示例查询)
    - [12.3 Docker Compose 配置](#123-docker-compose-配置)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [最佳实践](#最佳实践)
    - [性能考虑](#性能考虑)

---

## 一、GraphQL 架构与追踪概述

### 1.1 GraphQL 核心组件

````text
┌─────────────────────────────────────────┐
│          GraphQL Server (async-graphql) │
├─────────────────────────────────────────┤
│  - Schema 定义                          │
│  - Query/Mutation/Subscription          │
│  - Resolver（解析器）                    │
│  - DataLoader（数据加载器）              │
│  - Context（上下文传播）                 │
└─────────────────────────────────────────┘
         ↓           ↓           ↓
    [Query]    [Mutation]   [Subscription]
````

### 1.2 追踪目标

- **操作级别**：Query、Mutation、Subscription
- **解析器级别**：字段解析、嵌套查询
- **数据加载器**：批量加载、缓存命中
- **性能级别**：查询耗时、解析深度、字段数量

---

## 二、依赖配置

### 2.1 Cargo.toml

````toml
[dependencies]
# OpenTelemetry 核心
opentelemetry = { version = "0.31.0", features = ["trace"] }
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.24.0", features = ["grpc-tonic", "trace"] }

# GraphQL
async-graphql = { version = "7.0", features = ["tracing"] }
async-graphql-axum = "7.0"

# Web 框架
axum = { version = "0.8.7", features = ["macros"] }

# 异步运行时
tokio = { version = "1.47.1", features = ["full"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 错误处理
anyhow = "1.0"
thiserror = "2.0"

# 日志
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
tracing-opentelemetry = "0.28"
````

---

## 三、GraphQL 语义约定

### 3.1 OpenTelemetry 属性

````rust
use opentelemetry::KeyValue;

pub struct GraphQLSpanAttributes;

impl GraphQLSpanAttributes {
    /// GraphQL 操作类型
    pub const GRAPHQL_OPERATION_TYPE: &'static str = "graphql.operation.type";
    
    /// GraphQL 操作名称
    pub const GRAPHQL_OPERATION_NAME: &'static str = "graphql.operation.name";
    
    /// GraphQL 文档（查询字符串）
    pub const GRAPHQL_DOCUMENT: &'static str = "graphql.document";
    
    /// 解析器字段路径
    pub const GRAPHQL_FIELD_PATH: &'static str = "graphql.field.path";
    
    /// 解析器字段名称
    pub const GRAPHQL_FIELD_NAME: &'static str = "graphql.field.name";
    
    /// 解析器父类型
    pub const GRAPHQL_PARENT_TYPE: &'static str = "graphql.parent.type";
    
    /// 返回类型
    pub const GRAPHQL_RETURN_TYPE: &'static str = "graphql.return.type";
    
    /// 错误数量
    pub const GRAPHQL_ERROR_COUNT: &'static str = "graphql.error.count";
    
    /// 查询深度
    pub const GRAPHQL_QUERY_DEPTH: &'static str = "graphql.query.depth";
    
    /// 查询复杂度
    pub const GRAPHQL_QUERY_COMPLEXITY: &'static str = "graphql.query.complexity";
}
````

---

## 四、基础追踪实现

### 4.1 OpenTelemetry 扩展

````rust
use async_graphql::{
    extensions::{Extension, ExtensionContext, ExtensionFactory, NextExecute, NextParseQuery, NextResolve},
    parser::types::ExecutableDocument,
    Response, ServerResult, Value,
};
use opentelemetry::trace::{Span, SpanKind, Status, Tracer};
use opentelemetry::{global, KeyValue};
use std::sync::Arc;

/// OpenTelemetry 追踪扩展
pub struct OpenTelemetryExtension {
    tracer: Arc<dyn Tracer + Send + Sync>,
}

impl OpenTelemetryExtension {
    pub fn new() -> Self {
        let tracer = global::tracer("graphql");
        Self {
            tracer: Arc::new(tracer),
        }
    }
}

impl ExtensionFactory for OpenTelemetryExtension {
    fn create(&self) -> Arc<dyn Extension> {
        Arc::new(OpenTelemetryExtensionImpl {
            tracer: self.tracer.clone(),
        })
    }
}

struct OpenTelemetryExtensionImpl {
    tracer: Arc<dyn Tracer + Send + Sync>,
}

#[async_trait::async_trait]
impl Extension for OpenTelemetryExtensionImpl {
    /// 解析查询
    async fn parse_query(
        &self,
        ctx: &ExtensionContext<'_>,
        query: &str,
        _variables: &Variables,
        next: NextParseQuery<'_>,
    ) -> ServerResult<ExecutableDocument> {
        let mut span = self.tracer
            .span_builder("graphql.parse")
            .with_kind(SpanKind::Internal)
            .start(&*self.tracer);
        
        span.set_attribute(KeyValue::new("graphql.document_length", query.len() as i64));
        
        let result = next.run(ctx, query, _variables).await;
        
        if result.is_err() {
            span.set_status(Status::error("解析失败"));
        }
        
        result
    }
    
    /// 执行操作
    async fn execute(
        &self,
        ctx: &ExtensionContext<'_>,
        operation_name: Option<&str>,
        next: NextExecute<'_>,
    ) -> Response {
        let mut span = self.tracer
            .span_builder("graphql.execute")
            .with_kind(SpanKind::Server)
            .start(&*self.tracer);
        
        // 记录操作名称
        if let Some(name) = operation_name {
            span.set_attribute(KeyValue::new(
                GraphQLSpanAttributes::GRAPHQL_OPERATION_NAME,
                name.to_string(),
            ));
        }
        
        // 记录操作类型
        if let Some(operation) = ctx.query_env.operation {
            let op_type = match operation.node.ty {
                async_graphql::parser::types::OperationType::Query => "query",
                async_graphql::parser::types::OperationType::Mutation => "mutation",
                async_graphql::parser::types::OperationType::Subscription => "subscription",
            };
            span.set_attribute(KeyValue::new(
                GraphQLSpanAttributes::GRAPHQL_OPERATION_TYPE,
                op_type,
            ));
        }
        
        let start = std::time::Instant::now();
        let response = next.run(ctx, operation_name).await;
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new("duration_ms", duration.as_millis() as i64));
        
        // 记录错误
        if !response.errors.is_empty() {
            span.set_status(Status::error("GraphQL errors"));
            span.set_attribute(KeyValue::new(
                GraphQLSpanAttributes::GRAPHQL_ERROR_COUNT,
                response.errors.len() as i64,
            ));
        }
        
        response
    }
    
    /// 解析字段
    async fn resolve(
        &self,
        ctx: &ExtensionContext<'_>,
        info: async_graphql::extensions::ResolveInfo<'_>,
        next: NextResolve<'_>,
    ) -> ServerResult<Option<Value>> {
        let mut span = self.tracer
            .span_builder(format!("graphql.resolve.{}", info.path_node.field_name()))
            .with_kind(SpanKind::Internal)
            .start(&*self.tracer);
        
        span.set_attribute(KeyValue::new(
            GraphQLSpanAttributes::GRAPHQL_FIELD_NAME,
            info.path_node.field_name().to_string(),
        ));
        span.set_attribute(KeyValue::new(
            GraphQLSpanAttributes::GRAPHQL_PARENT_TYPE,
            info.parent_type.to_string(),
        ));
        span.set_attribute(KeyValue::new(
            GraphQLSpanAttributes::GRAPHQL_RETURN_TYPE,
            info.return_type.to_string(),
        ));
        
        let start = std::time::Instant::now();
        let result = next.run(ctx, info).await;
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new("duration_ms", duration.as_millis() as i64));
        
        if result.is_err() {
            span.set_status(Status::error("解析失败"));
        }
        
        result
    }
}
````

---

## 五、查询追踪

### 5.1 Schema 定义

````rust
use async_graphql::*;

/// 用户类型
#[derive(SimpleObject, Clone)]
pub struct User {
    pub id: ID,
    pub name: String,
    pub email: String,
}

/// 查询根
pub struct Query;

#[Object]
impl Query {
    /// 获取用户
    #[tracing::instrument(skip(self, ctx))]
    async fn user(&self, ctx: &Context<'_>, id: ID) -> Result<User> {
        // 从 Context 获取数据库连接等
        tracing::info!(user_id = %id, "查询用户");
        
        Ok(User {
            id: id.clone(),
            name: "Alice".to_string(),
            email: "alice@example.com".to_string(),
        })
    }
    
    /// 获取所有用户
    #[tracing::instrument(skip(self, ctx))]
    async fn users(&self, ctx: &Context<'_>, limit: Option<i32>) -> Result<Vec<User>> {
        let limit = limit.unwrap_or(10);
        
        tracing::info!(limit = limit, "查询用户列表");
        
        Ok(vec![
            User {
                id: ID::from("1"),
                name: "Alice".to_string(),
                email: "alice@example.com".to_string(),
            },
            User {
                id: ID::from("2"),
                name: "Bob".to_string(),
                email: "bob@example.com".to_string(),
            },
        ])
    }
}
````

---

## 六、变更追踪

### 6.1 Mutation 定义

````rust
/// 变更根
pub struct Mutation;

#[Object]
impl Mutation {
    /// 创建用户
    #[tracing::instrument(skip(self, ctx))]
    async fn create_user(
        &self,
        ctx: &Context<'_>,
        name: String,
        email: String,
    ) -> Result<User> {
        tracing::info!(name = %name, email = %email, "创建用户");
        
        // 生成 ID
        let id = ID::from(uuid::Uuid::new_v4().to_string());
        
        Ok(User { id, name, email })
    }
    
    /// 更新用户
    #[tracing::instrument(skip(self, ctx))]
    async fn update_user(
        &self,
        ctx: &Context<'_>,
        id: ID,
        name: Option<String>,
        email: Option<String>,
    ) -> Result<User> {
        tracing::info!(user_id = %id, "更新用户");
        
        Ok(User {
            id: id.clone(),
            name: name.unwrap_or_else(|| "Updated".to_string()),
            email: email.unwrap_or_else(|| "updated@example.com".to_string()),
        })
    }
    
    /// 删除用户
    #[tracing::instrument(skip(self, ctx))]
    async fn delete_user(&self, ctx: &Context<'_>, id: ID) -> Result<bool> {
        tracing::info!(user_id = %id, "删除用户");
        
        Ok(true)
    }
}
````

---

## 七、订阅追踪

### 7.1 Subscription 定义

````rust
use futures_util::Stream;
use std::time::Duration;
use tokio_stream::StreamExt;

/// 订阅根
pub struct Subscription;

#[Subscription]
impl Subscription {
    /// 订阅用户变更
    #[tracing::instrument(skip(self))]
    async fn user_changed(&self, id: ID) -> impl Stream<Item = User> {
        tracing::info!(user_id = %id, "开始订阅用户变更");
        
        // 模拟实时更新
        tokio_stream::wrappers::IntervalStream::new(
            tokio::time::interval(Duration::from_secs(5))
        )
        .map(move |_| {
            tracing::debug!(user_id = %id, "推送用户更新");
            
            User {
                id: id.clone(),
                name: format!("User at {}", chrono::Utc::now()),
                email: "changed@example.com".to_string(),
            }
        })
    }
}
````

---

## 八、解析器追踪

### 8.1 自定义解析器

````rust
use async_graphql::{ComplexObject, Context, Result};

/// 扩展 User 类型
#[derive(SimpleObject)]
#[graphql(complex)]
pub struct UserExtended {
    pub id: ID,
    pub name: String,
    pub email: String,
    #[graphql(skip)]
    pub created_at: i64,
}

#[ComplexObject]
impl UserExtended {
    /// 获取用户文章（懒加载）
    #[tracing::instrument(skip(self, ctx))]
    async fn posts(&self, ctx: &Context<'_>) -> Result<Vec<Post>> {
        tracing::info!(user_id = %self.id, "查询用户文章");
        
        // 从数据库加载
        Ok(vec![
            Post {
                id: ID::from("post1"),
                title: "First Post".to_string(),
                content: "Content here".to_string(),
            },
        ])
    }
    
    /// 获取用户好友数量
    #[tracing::instrument(skip(self, ctx))]
    async fn friend_count(&self, ctx: &Context<'_>) -> Result<i32> {
        tracing::info!(user_id = %self.id, "统计好友数量");
        
        Ok(42)
    }
}

#[derive(SimpleObject, Clone)]
pub struct Post {
    pub id: ID,
    pub title: String,
    pub content: String,
}
````

---

## 九、数据加载器追踪

### 9.1 DataLoader 实现

````rust
use async_graphql::dataloader::{DataLoader, Loader};
use std::collections::HashMap;

/// 用户数据加载器
pub struct UserLoader;

#[async_trait::async_trait]
impl Loader<ID> for UserLoader {
    type Value = User;
    type Error = Arc<anyhow::Error>;
    
    #[tracing::instrument(skip(self, keys))]
    async fn load(&self, keys: &[ID]) -> Result<HashMap<ID, Self::Value>, Self::Error> {
        tracing::info!(count = keys.len(), "批量加载用户");
        
        // 模拟数据库批量查询
        let mut users = HashMap::new();
        for key in keys {
            users.insert(
                key.clone(),
                User {
                    id: key.clone(),
                    name: format!("User {}", key),
                    email: format!("user{}@example.com", key),
                },
            );
        }
        
        Ok(users)
    }
}

// 使用示例
#[Object]
impl Query {
    #[tracing::instrument(skip(self, ctx))]
    async fn user_with_loader(&self, ctx: &Context<'_>, id: ID) -> Result<User> {
        let loader = ctx.data::<DataLoader<UserLoader>>()?;
        
        loader
            .load_one(id.clone())
            .await?
            .ok_or_else(|| "用户不存在".into())
    }
}
````

---

## 十、错误处理

### 10.1 自定义错误

````rust
use async_graphql::{Error, ErrorExtensions};
use std::fmt;

#[derive(Debug)]
pub enum AppError {
    NotFound(String),
    Unauthorized,
    DatabaseError(String),
}

impl fmt::Display for AppError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotFound(msg) => write!(f, "未找到: {}", msg),
            Self::Unauthorized => write!(f, "未授权"),
            Self::DatabaseError(msg) => write!(f, "数据库错误: {}", msg),
        }
    }
}

impl std::error::Error for AppError {}

impl ErrorExtensions for AppError {
    fn extend(&self) -> Error {
        let mut err = Error::new(self.to_string());
        
        match self {
            Self::NotFound(_) => {
                err = err.extend_with(|_, e| {
                    e.set("code", "NOT_FOUND");
                });
            }
            Self::Unauthorized => {
                err = err.extend_with(|_, e| {
                    e.set("code", "UNAUTHORIZED");
                });
            }
            Self::DatabaseError(_) => {
                err = err.extend_with(|_, e| {
                    e.set("code", "DATABASE_ERROR");
                });
            }
        }
        
        err
    }
}
````

---

## 十一、性能监控

### 11.1 性能指标

````rust
use opentelemetry::metrics::{Histogram, Counter};

pub struct GraphQLMetrics {
    operation_duration: Histogram<f64>,
    operation_count: Counter<u64>,
    error_count: Counter<u64>,
    resolver_duration: Histogram<f64>,
}

impl GraphQLMetrics {
    pub fn new() -> Self {
        let meter = opentelemetry::global::meter("graphql");
        
        Self {
            operation_duration: meter
                .f64_histogram("graphql.operation.duration")
                .with_description("操作耗时（毫秒）")
                .with_unit("ms")
                .build(),
            operation_count: meter
                .u64_counter("graphql.operation.count")
                .with_description("操作次数")
                .build(),
            error_count: meter
                .u64_counter("graphql.operation.errors")
                .with_description("操作错误次数")
                .build(),
            resolver_duration: meter
                .f64_histogram("graphql.resolver.duration")
                .with_description("解析器耗时（毫秒）")
                .with_unit("ms")
                .build(),
        }
    }
    
    pub fn record_operation(
        &self,
        operation_type: &str,
        operation_name: Option<&str>,
        duration_ms: f64,
        error_count: usize,
    ) {
        let mut labels = vec![KeyValue::new("operation_type", operation_type.to_string())];
        if let Some(name) = operation_name {
            labels.push(KeyValue::new("operation_name", name.to_string()));
        }
        
        self.operation_duration.record(duration_ms, &labels);
        self.operation_count.add(1, &labels);
        
        if error_count > 0 {
            self.error_count.add(error_count as u64, &labels);
        }
    }
    
    pub fn record_resolver(&self, field_name: &str, parent_type: &str, duration_ms: f64) {
        let labels = &[
            KeyValue::new("field_name", field_name.to_string()),
            KeyValue::new("parent_type", parent_type.to_string()),
        ];
        
        self.resolver_duration.record(duration_ms, labels);
    }
}
````

---

## 十二、生产环境完整示例

### 12.1 完整应用

````rust
use async_graphql::{EmptySubscription, Schema};
use async_graphql_axum::{GraphQLRequest, GraphQLResponse};
use axum::{
    extract::Extension,
    routing::post,
    Router,
};
use opentelemetry::global;
use opentelemetry_sdk::trace::TracerProvider;
use opentelemetry_otlp::WithExportConfig;

type MySchema = Schema<Query, Mutation, EmptySubscription>;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 初始化追踪
    let tracer_provider = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317"),
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    global::set_tracer_provider(tracer_provider.clone());
    
    // 初始化日志
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .init();
    
    // 创建 GraphQL Schema
    let schema = Schema::build(Query, Mutation, EmptySubscription)
        .extension(OpenTelemetryExtension::new())
        .finish();
    
    // 创建 Axum 应用
    let app = Router::new()
        .route("/graphql", post(graphql_handler))
        .layer(Extension(schema));
    
    // 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:8000").await?;
    tracing::info!("GraphQL 服务器启动: http://localhost:8000/graphql");
    
    axum::serve(listener, app).await?;
    
    // 优雅关闭
    global::shutdown_tracer_provider();
    
    Ok(())
}

async fn graphql_handler(
    schema: Extension<MySchema>,
    req: GraphQLRequest,
) -> GraphQLResponse {
    schema.execute(req.into_inner()).await.into()
}
````

### 12.2 示例查询

````graphql
# 查询用户
query GetUser {
  user(id: "123") {
    id
    name
    email
  }
}

# 创建用户
mutation CreateUser {
  createUser(name: "Charlie", email: "charlie@example.com") {
    id
    name
    email
  }
}

# 嵌套查询（触发 DataLoader）
query GetUsersWithPosts {
  users(limit: 5) {
    id
    name
    posts {
      id
      title
    }
    friendCount
  }
}
````

### 12.3 Docker Compose 配置

````yaml
version: '3.8'

services:
  graphql-server:
    build: .
    ports:
      - "8000:8000"
    environment:
      OTLP_ENDPOINT: http://jaeger:4317
  
  jaeger:
    image: jaegertracing/all-in-one:1.66
    ports:
      - "4317:4317"   # OTLP gRPC
      - "16686:16686" # Jaeger UI
    environment:
      COLLECTOR_OTLP_ENABLED: "true"
````

---

## 总结

### 核心要点

1. **完整追踪**：覆盖 Query、Mutation、Subscription、Resolver
2. **语义约定**：遵循 OpenTelemetry GraphQL 属性规范
3. **数据加载器**：批量加载优化，减少 N+1 查询
4. **错误处理**：统一错误扩展，携带错误码
5. **性能优化**：解析器级别追踪，识别性能瓶颈

### 最佳实践

- 使用 `OpenTelemetryExtension` 自动追踪所有操作
- 为每个解析器添加 `#[tracing::instrument]` 宏
- DataLoader 批量加载应记录批次大小
- 限制记录的查询文档大小（< 2KB）
- 生产环境启用查询复杂度限制

### 性能考虑

- 避免在高频解析器中记录大量属性
- 使用 DataLoader 减少数据库查询
- 合理设置查询深度限制（推荐 ≤ 5）
- 对复杂查询启用持久化查询
- 监控解析器耗时，优化慢查询

---

**文档版本**: v1.0  
**最后更新**: 2025-10-09  
**Rust 版本**: 1.90+  
**async-graphql 版本**: 7.0+  
**OpenTelemetry 版本**: 0.31.0+
