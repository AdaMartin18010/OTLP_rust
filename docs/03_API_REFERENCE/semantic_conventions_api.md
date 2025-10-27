# 🏷️ Semantic Conventions API 参考

**模块**: `otlp::semantic_conventions`  
**版本**: 1.0  
**状态**: ✅ 生产就绪  
**标准版本**: OpenTelemetry v1.29.0  
**最后更新**: 2025年10月26日

> **简介**: 类型安全的 OpenTelemetry 语义约定实现 - 确保所有遥测信号使用一致的属性命名和值。

---

## 📋 目录

- [🏷️ Semantic Conventions API 参考](#️-semantic-conventions-api-参考)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
    - [核心特性](#核心特性)
  - [🚀 快速开始](#-快速开始)
  - [📚 HTTP约定](#-http约定)
    - [HttpAttributesBuilder](#httpattributesbuilder)
    - [HttpMethod](#httpmethod)
    - [HttpAttributes](#httpattributes)
  - [🗄️ Database约定](#️-database约定)
    - [DatabaseAttributesBuilder](#databaseattributesbuilder)
    - [DatabaseSystem](#databasesystem)
  - [📮 Messaging约定](#-messaging约定)
    - [MessagingAttributesBuilder](#messagingattributesbuilder)
    - [MessagingSystem](#messagingsystem)
  - [☸️ Kubernetes约定](#️-kubernetes约定)
    - [K8sAttributesBuilder](#k8sattributesbuilder)
    - [K8sResourceType](#k8sresourcetype)
  - [🌐 通用资源约定](#-通用资源约定)
  - [💡 使用示例](#-使用示例)
  - [🔧 类型安全保证](#-类型安全保证)
  - [📚 参考资源](#-参考资源)

---

## 📋 概述

Semantic Conventions模块提供类型安全的OpenTelemetry语义约定实现，确保所有遥测信号使用一致的属性命名和值。完全基于[OpenTelemetry Semantic Conventions v1.29.0](https://opentelemetry.io/docs/specs/semconv/)。

### 核心特性

- ✅ **HTTP约定** - 客户端和服务器HTTP属性
- ✅ **数据库约定** - 数据库操作属性
- ✅ **消息队列约定** - 消息系统属性
- ✅ **Kubernetes约定** - K8s资源属性
- ✅ **通用资源约定** - 服务和部署属性
- ✅ **类型安全** - 编译时验证属性名称和类型
- ✅ **Builder模式** - 流畅的API构建

---

## 🚀 快速开始

```rust
use otlp::semantic_conventions::http::{HttpAttributesBuilder, HttpMethod};

// 构建HTTP属性
let attrs = HttpAttributesBuilder::new()
    .method(HttpMethod::Get)
    .url("https://api.example.com/users")
    .status_code(200)
    .user_agent("MyApp/1.0")
    .build()?;

// 添加到span
span.set_attributes(attrs.into_map());
```

---

## 📚 HTTP约定

### HttpAttributesBuilder

构建HTTP请求/响应属性。

```rust
pub struct HttpAttributesBuilder {
    // 内部实现
}

impl HttpAttributesBuilder {
    /// 创建新的builder
    pub fn new() -> Self;
    
    /// HTTP方法
    pub fn method(mut self, method: HttpMethod) -> Self;
    
    /// 完整URL
    pub fn url(mut self, url: impl Into<String>) -> Self;
    
    /// URL scheme (http/https)
    pub fn scheme(mut self, scheme: HttpScheme) -> Self;
    
    /// 目标主机
    pub fn host(mut self, host: impl Into<String>) -> Self;
    
    /// 目标端口
    pub fn port(mut self, port: u16) -> Self;
    
    /// URL路径
    pub fn target(mut self, target: impl Into<String>) -> Self;
    
    /// HTTP状态码
    pub fn status_code(mut self, code: u16) -> Self;
    
    /// User-Agent头
    pub fn user_agent(mut self, ua: impl Into<String>) -> Self;
    
    /// 请求大小（字节）
    pub fn request_content_length(mut self, len: u64) -> Self;
    
    /// 响应大小（字节）
    pub fn response_content_length(mut self, len: u64) -> Self;
    
    /// 服务器名称
    pub fn server_name(mut self, name: impl Into<String>) -> Self;
    
    /// 路由模板
    pub fn route(mut self, route: impl Into<String>) -> Self;
    
    /// 客户端IP
    pub fn client_ip(mut self, ip: impl Into<String>) -> Self;
    
    /// 构建属性集合
    pub fn build(self) -> Result<HttpAttributes, SemanticConventionError>;
}
```

### HttpMethod

HTTP方法枚举。

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HttpMethod {
    Get,
    Post,
    Put,
    Delete,
    Patch,
    Head,
    Options,
    Trace,
    Connect,
}

impl fmt::Display for HttpMethod {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", match self {
            HttpMethod::Get => "GET",
            HttpMethod::Post => "POST",
            // ... 其他方法
        })
    }
}
```

### 使用示例

```rust
use otlp::semantic_conventions::http::*;

// HTTP客户端请求
let client_attrs = HttpAttributesBuilder::new()
    .method(HttpMethod::Post)
    .url("https://api.github.com/repos")
    .scheme(HttpScheme::Https)
    .host("api.github.com")
    .port(443)
    .target("/repos")
    .user_agent("rust-otlp/0.5.0")
    .request_content_length(1024)
    .build()?;

// HTTP服务器响应
let server_attrs = HttpAttributesBuilder::new()
    .method(HttpMethod::Get)
    .target("/api/users/123")
    .route("/api/users/:id")
    .status_code(200)
    .response_content_length(2048)
    .server_name("user-service")
    .client_ip("192.168.1.100")
    .build()?;
```

---

## 💾 数据库约定

### DatabaseAttributesBuilder

构建数据库操作属性。

```rust
pub struct DatabaseAttributesBuilder {
    // 内部实现
}

impl DatabaseAttributesBuilder {
    /// 创建新的builder
    pub fn new() -> Self;
    
    /// 数据库系统
    pub fn system(mut self, system: DatabaseSystem) -> Self;
    
    /// 数据库名称
    pub fn name(mut self, name: impl Into<String>) -> Self;
    
    /// 连接字符串
    pub fn connection_string(mut self, conn: impl Into<String>) -> Self;
    
    /// 数据库用户
    pub fn user(mut self, user: impl Into<String>) -> Self;
    
    /// SQL语句
    pub fn statement(mut self, stmt: impl Into<String>) -> Self;
    
    /// 操作类型
    pub fn operation(mut self, op: DatabaseOperation) -> Self;
    
    /// 表名
    pub fn table(mut self, table: impl Into<String>) -> Self;
    
    /// 构建属性
    pub fn build(self) -> Result<DatabaseAttributes, SemanticConventionError>;
}
```

### DatabaseSystem

支持的数据库系统。

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DatabaseSystem {
    PostgreSQL,
    MySQL,
    Redis,
    MongoDB,
    Cassandra,
    Elasticsearch,
    DynamoDB,
    ClickHouse,
    // ... 更多
}
```

### DatabaseOperation

数据库操作类型。

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DatabaseOperation {
    Select,
    Insert,
    Update,
    Delete,
    Create,
    Drop,
    Alter,
    // ... 更多
}
```

### 使用示例1

```rust
use otlp::semantic_conventions::database::*;

// PostgreSQL查询
let pg_attrs = DatabaseAttributesBuilder::new()
    .system(DatabaseSystem::PostgreSQL)
    .name("production_db")
    .user("app_user")
    .statement("SELECT * FROM users WHERE id = $1")
    .operation(DatabaseOperation::Select)
    .table("users")
    .build()?;

// Redis操作
let redis_attrs = DatabaseAttributesBuilder::new()
    .system(DatabaseSystem::Redis)
    .statement("GET user:123")
    .operation(DatabaseOperation::Select)
    .build()?;

// MongoDB查询
let mongo_attrs = DatabaseAttributesBuilder::new()
    .system(DatabaseSystem::MongoDB)
    .name("app_db")
    .statement(r#"{"find": "users", "filter": {"age": {"$gt": 25}}}"#)
    .operation(DatabaseOperation::Select)
    .table("users")
    .build()?;
```

---

## 📨 消息队列约定

### MessagingAttributesBuilder

构建消息系统属性。

```rust
pub struct MessagingAttributesBuilder {
    // 内部实现
}

impl MessagingAttributesBuilder {
    /// 创建新的builder
    pub fn new() -> Self;
    
    /// 消息系统
    pub fn system(mut self, system: MessagingSystem) -> Self;
    
    /// 目标名称（队列/主题）
    pub fn destination(mut self, dest: impl Into<String>) -> Self;
    
    /// 目标类型
    pub fn destination_kind(mut self, kind: DestinationKind) -> Self;
    
    /// 操作类型
    pub fn operation(mut self, op: MessagingOperation) -> Self;
    
    /// 消息ID
    pub fn message_id(mut self, id: impl Into<String>) -> Self;
    
    /// 会话ID
    pub fn conversation_id(mut self, id: impl Into<String>) -> Self;
    
    /// 消息大小（字节）
    pub fn payload_size(mut self, size: u64) -> Self;
    
    /// 构建属性
    pub fn build(self) -> Result<MessagingAttributes, SemanticConventionError>;
}
```

### MessagingSystem

支持的消息系统。

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MessagingSystem {
    Kafka,
    RabbitMQ,
    AWS_SQS,
    AWS_SNS,
    NATS,
    Redis,
    Pulsar,
    // ... 更多
}
```

### 使用示例2

```rust
use otlp::semantic_conventions::messaging::*;

// Kafka生产者
let kafka_attrs = MessagingAttributesBuilder::new()
    .system(MessagingSystem::Kafka)
    .destination("user-events")
    .destination_kind(DestinationKind::Topic)
    .operation(MessagingOperation::Publish)
    .message_id("msg-12345")
    .payload_size(2048)
    .build()?;

// RabbitMQ消费者
let rabbitmq_attrs = MessagingAttributesBuilder::new()
    .system(MessagingSystem::RabbitMQ)
    .destination("task-queue")
    .destination_kind(DestinationKind::Queue)
    .operation(MessagingOperation::Receive)
    .message_id("msg-67890")
    .build()?;
```

---

## ☸️ Kubernetes约定

### K8sAttributesBuilder

构建Kubernetes资源属性。

```rust
pub struct K8sAttributesBuilder {
    // 内部实现
}

impl K8sAttributesBuilder {
    /// 创建新的builder
    pub fn new() -> Self;
    
    /// 命名空间
    pub fn namespace(mut self, ns: impl Into<String>) -> Self;
    
    /// Pod名称
    pub fn pod_name(mut self, name: impl Into<String>) -> Self;
    
    /// Pod UID
    pub fn pod_uid(mut self, uid: impl Into<String>) -> Self;
    
    /// 容器名称
    pub fn container_name(mut self, name: impl Into<String>) -> Self;
    
    /// Deployment名称
    pub fn deployment_name(mut self, name: impl Into<String>) -> Self;
    
    /// Service名称
    pub fn service_name(mut self, name: impl Into<String>) -> Self;
    
    /// Node名称
    pub fn node_name(mut self, name: impl Into<String>) -> Self;
    
    /// 集群名称
    pub fn cluster_name(mut self, name: impl Into<String>) -> Self;
    
    /// 构建属性
    pub fn build(self) -> Result<K8sAttributes, SemanticConventionError>;
}
```

### 使用示例3

```rust
use otlp::semantic_conventions::k8s::*;

let k8s_attrs = K8sAttributesBuilder::new()
    .namespace("production")
    .pod_name("user-service-7d8f9c-xyz")
    .pod_uid("a1b2c3d4-e5f6-g7h8-i9j0-k1l2m3n4o5p6")
    .container_name("user-service")
    .deployment_name("user-service")
    .cluster_name("prod-cluster-1")
    .node_name("node-01")
    .build()?;
```

---

## 🔧 通用约定

### 资源属性

```rust
use otlp::semantic_conventions::common::*;

// 服务资源
let service_attrs = vec![
    ("service.name", "user-service"),
    ("service.version", "1.2.3"),
    ("service.namespace", "production"),
    ("service.instance.id", "instance-123"),
];

// 部署环境
let deployment_attrs = vec![
    ("deployment.environment", "production"),
    ("cloud.provider", "aws"),
    ("cloud.region", "us-east-1"),
    ("cloud.availability_zone", "us-east-1a"),
];

// 主机信息
let host_attrs = vec![
    ("host.name", "prod-server-01"),
    ("host.type", "m5.large"),
    ("host.arch", "amd64"),
    ("os.type", "linux"),
];
```

---

## 📝 完整示例

### HTTP服务器追踪

```rust
use otlp::semantic_conventions::{http::*, common::*};
use otlp::profiling::link_profile_to_current_trace;

#[tokio::main]
async fn main() -> Result<()> {
    // 1. 创建HTTP span
    let mut span = tracer.span_builder("handle_request")
        .with_kind(SpanKind::Server)
        .start();
    
    // 2. 添加HTTP语义约定属性
    let http_attrs = HttpAttributesBuilder::new()
        .method(HttpMethod::Post)
        .target("/api/users")
        .route("/api/users")
        .scheme(HttpScheme::Https)
        .host("api.example.com")
        .status_code(201)
        .request_content_length(1024)
        .response_content_length(512)
        .client_ip("192.168.1.100")
        .user_agent("Mozilla/5.0")
        .build()?;
    
    span.set_attributes(http_attrs.into_map());
    
    // 3. 处理请求
    let result = handle_user_creation().await?;
    
    // 4. 设置状态
    span.set_status(SpanStatus::Ok, None);
    span.end();
    
    Ok(())
}
```

### 数据库操作追踪

```rust
use otlp::semantic_conventions::database::*;

async fn query_user(id: i64) -> Result<User> {
    let mut span = tracer.span_builder("db.query")
        .with_kind(SpanKind::Client)
        .start();
    
    // 添加数据库语义约定
    let db_attrs = DatabaseAttributesBuilder::new()
        .system(DatabaseSystem::PostgreSQL)
        .name("production_db")
        .user("app_user")
        .statement("SELECT * FROM users WHERE id = $1")
        .operation(DatabaseOperation::Select)
        .table("users")
        .build()?;
    
    span.set_attributes(db_attrs.into_map());
    
    // 执行查询
    let user = execute_query(id).await?;
    
    span.end();
    Ok(user)
}
```

### 微服务间消息传递

```rust
use otlp::semantic_conventions::messaging::*;

async fn publish_event(event: UserEvent) -> Result<()> {
    let mut span = tracer.span_builder("publish.user_event")
        .with_kind(SpanKind::Producer)
        .start();
    
    // Kafka producer属性
    let msg_attrs = MessagingAttributesBuilder::new()
        .system(MessagingSystem::Kafka)
        .destination("user-events")
        .destination_kind(DestinationKind::Topic)
        .operation(MessagingOperation::Publish)
        .message_id(&event.id)
        .payload_size(event.size_bytes())
        .build()?;
    
    span.set_attributes(msg_attrs.into_map());
    
    // 发布消息
    kafka_producer.send(&event).await?;
    
    span.set_status(SpanStatus::Ok, None);
    span.end();
    Ok(())
}
```

---

## 📊 标准化属性对照

### HTTP标准属性

| 属性名 | 类型 | 示例 | 说明 |
|--------|------|------|------|
| `http.method` | string | "GET" | HTTP方法 |
| `http.url` | string | "<https://api.example.com>" | 完整URL |
| `http.status_code` | int | 200 | HTTP状态码 |
| `http.scheme` | string | "https" | URL scheme |
| `http.target` | string | "/api/users" | 请求目标 |
| `http.route` | string | "/api/users/:id" | 路由模板 |

### 数据库标准属性

| 属性名 | 类型 | 示例 | 说明 |
|--------|------|------|------|
| `db.system` | string | "postgresql" | 数据库系统 |
| `db.name` | string | "production_db" | 数据库名称 |
| `db.statement` | string | "SELECT * FROM users" | SQL语句 |
| `db.operation` | string | "SELECT" | 操作类型 |
| `db.sql.table` | string | "users" | 表名 |

### 消息系统标准属性

| 属性名 | 类型 | 示例 | 说明 |
|--------|------|------|------|
| `messaging.system` | string | "kafka" | 消息系统 |
| `messaging.destination` | string | "user-events" | 目标名称 |
| `messaging.destination_kind` | string | "topic" | 目标类型 |
| `messaging.operation` | string | "publish" | 操作类型 |
| `messaging.message_id` | string | "msg-123" | 消息ID |

---

## ✅ 验证和错误处理

```rust
use otlp::semantic_conventions::http::*;

// 验证URL格式
let result = HttpAttributesBuilder::new()
    .url("invalid-url")  // 无效URL
    .build();

match result {
    Ok(attrs) => println!("Attributes created successfully"),
    Err(SemanticConventionError::InvalidUrl(url)) => {
        eprintln!("Invalid URL: {}", url);
    }
    Err(e) => eprintln!("Error: {}", e),
}

// 必需字段验证
let result = HttpAttributesBuilder::new()
    .status_code(200)
    // 缺少method
    .build();

if let Err(SemanticConventionError::MissingRequired(field)) = result {
    eprintln!("Missing required field: {}", field);
}
```

---

## 🔗 相关文档

- [OTLP标准对齐](../08_REFERENCE/otlp_standards_alignment.md)
- [最佳实践指南](../08_REFERENCE/best_practices.md)
- [实现指南](../05_IMPLEMENTATION/README.md)

---

**模块版本**: 0.5.0  
**语义约定版本**: v1.29.0  
**最后更新**: 2025年10月26日  
**维护状态**: ✅ 活跃维护
