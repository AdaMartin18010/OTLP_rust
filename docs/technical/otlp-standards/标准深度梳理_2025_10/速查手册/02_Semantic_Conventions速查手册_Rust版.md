# 🦀 Semantic Conventions速查手册 - Rust 1.90版

> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **Semantic Conventions**: 1.27.0  
> **最后更新**: 2025年10月11日

---

## 📋 快速索引

- [🦀 Semantic Conventions速查手册 - Rust 1.90版](#-semantic-conventions速查手册---rust-190版)
  - [📋 快速索引](#-快速索引)
  - [🎯 资源属性 (Resource)](#-资源属性-resource)
    - [Service属性](#service属性)
    - [部署属性](#部署属性)
    - [云平台属性](#云平台属性)
  - [🌐 HTTP语义](#-http语义)
    - [HTTP Server Span](#http-server-span)
    - [HTTP Client Span](#http-client-span)
    - [HTTP指标](#http指标)
  - [🗄️ 数据库语义](#️-数据库语义)
    - [SQL数据库](#sql数据库)
    - [数据库系统标识符](#数据库系统标识符)
    - [Redis示例](#redis示例)
    - [MongoDB示例](#mongodb示例)
  - [📡 RPC语义](#-rpc语义)
    - [gRPC Server](#grpc-server)
    - [gRPC Client](#grpc-client)
    - [gRPC状态码](#grpc状态码)
  - [📨 消息系统](#-消息系统)
    - [Kafka Producer](#kafka-producer)
    - [Kafka Consumer](#kafka-consumer)
    - [RabbitMQ](#rabbitmq)
  - [💻 系统指标](#-系统指标)
    - [CPU指标](#cpu指标)
    - [内存指标](#内存指标)
    - [网络指标](#网络指标)
    - [磁盘指标](#磁盘指标)
  - [🔥 运行时指标 (Rust)](#-运行时指标-rust)
    - [进程指标](#进程指标)
  - [🏷️ 自定义属性最佳实践](#️-自定义属性最佳实践)
    - [命名规范](#命名规范)
    - [基数控制](#基数控制)
  - [📊 完整示例](#-完整示例)
    - [HTTP服务器完整追踪](#http服务器完整追踪)
  - [📚 参考资源](#-参考资源)

---

## 🎯 资源属性 (Resource)

### Service属性

```rust
use opentelemetry::{KeyValue, sdk::Resource};

let resource = Resource::new(vec![
    // 必需: 服务名称
    KeyValue::new("service.name", "my-rust-service"),
    
    // 推荐: 服务版本
    KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
    
    // 可选: 服务实例ID
    KeyValue::new("service.instance.id", "instance-123"),
    
    // 可选: 服务命名空间
    KeyValue::new("service.namespace", "production"),
]);
```

### 部署属性

```rust
vec![
    KeyValue::new("deployment.environment", "production"),
    KeyValue::new("deployment.environment.name", "prod-us-west"),
]
```

### 云平台属性

```rust
// AWS
vec![
    KeyValue::new("cloud.provider", "aws"),
    KeyValue::new("cloud.platform", "aws_ec2"),
    KeyValue::new("cloud.region", "us-west-2"),
    KeyValue::new("cloud.availability_zone", "us-west-2a"),
    KeyValue::new("cloud.account.id", "123456789012"),
]

// 阿里云
vec![
    KeyValue::new("cloud.provider", "alibaba_cloud"),
    KeyValue::new("cloud.platform", "alibaba_cloud_ecs"),
    KeyValue::new("cloud.region", "cn-hangzhou"),
]

// Kubernetes
vec![
    KeyValue::new("k8s.cluster.name", "prod-cluster"),
    KeyValue::new("k8s.namespace.name", "default"),
    KeyValue::new("k8s.pod.name", "my-pod-123"),
    KeyValue::new("k8s.deployment.name", "my-deployment"),
]
```

---

## 🌐 HTTP语义

### HTTP Server Span

```rust
use opentelemetry::trace::{Span, Tracer, SpanKind};

let mut span = tracer
    .span_builder("GET /api/users")
    .with_kind(SpanKind::Server)
    .start(&tracer);

// 必需属性
span.set_attribute(KeyValue::new("http.method", "GET"));
span.set_attribute(KeyValue::new("http.route", "/api/users"));
span.set_attribute(KeyValue::new("http.scheme", "https"));
span.set_attribute(KeyValue::new("http.status_code", 200));

// 推荐属性
span.set_attribute(KeyValue::new("http.url", "https://api.example.com/api/users"));
span.set_attribute(KeyValue::new("http.target", "/api/users?page=1"));
span.set_attribute(KeyValue::new("http.host", "api.example.com"));
span.set_attribute(KeyValue::new("http.user_agent", "Mozilla/5.0..."));

// 可选属性
span.set_attribute(KeyValue::new("http.request_content_length", 1024));
span.set_attribute(KeyValue::new("http.response_content_length", 2048));
span.set_attribute(KeyValue::new("http.flavor", "2.0")); // HTTP/2

// 网络属性
span.set_attribute(KeyValue::new("net.host.name", "api.example.com"));
span.set_attribute(KeyValue::new("net.host.port", 443));
span.set_attribute(KeyValue::new("net.peer.ip", "192.168.1.100"));
```

### HTTP Client Span

```rust
let mut span = tracer
    .span_builder("GET https://external-api.com")
    .with_kind(SpanKind::Client)
    .start(&tracer);

span.set_attribute(KeyValue::new("http.method", "GET"));
span.set_attribute(KeyValue::new("http.url", "https://external-api.com/data"));
span.set_attribute(KeyValue::new("http.status_code", 200));
span.set_attribute(KeyValue::new("http.resend_count", 1)); // 重试次数
```

### HTTP指标

```rust
use opentelemetry::metrics::Meter;

let meter = global::meter("http-server");

// 请求计数
let requests_total = meter
    .u64_counter("http.server.requests")
    .with_description("Total HTTP requests")
    .init();

requests_total.add(1, &[
    KeyValue::new("http.method", "GET"),
    KeyValue::new("http.status_code", 200),
    KeyValue::new("http.route", "/api/users"),
]);

// 请求时长
let request_duration = meter
    .f64_histogram("http.server.duration")
    .with_unit("ms")
    .init();

request_duration.record(125.5, &[
    KeyValue::new("http.method", "GET"),
    KeyValue::new("http.route", "/api/users"),
]);

// 活跃请求
let active_requests = meter
    .i64_up_down_counter("http.server.active_requests")
    .init();

active_requests.add(1, &[]); // 请求开始
// ... 处理请求 ...
active_requests.add(-1, &[]); // 请求结束
```

---

## 🗄️ 数据库语义

### SQL数据库

```rust
let mut span = tracer
    .span_builder("SELECT users")
    .with_kind(SpanKind::Client)
    .start(&tracer);

// 必需属性
span.set_attribute(KeyValue::new("db.system", "postgresql"));
span.set_attribute(KeyValue::new("db.operation", "SELECT"));

// 推荐属性
span.set_attribute(KeyValue::new("db.name", "mydb"));
span.set_attribute(KeyValue::new("db.sql.table", "users"));
span.set_attribute(KeyValue::new("db.user", "dbuser"));

// 可选属性 (生产环境慎用)
span.set_attribute(KeyValue::new(
    "db.statement",
    "SELECT id, name FROM users WHERE age > 18"
));

// 连接属性
span.set_attribute(KeyValue::new("net.peer.name", "db.example.com"));
span.set_attribute(KeyValue::new("net.peer.port", 5432));
```

### 数据库系统标识符

```rust
// 关系型数据库
"db.system" => "postgresql"
"db.system" => "mysql"
"db.system" => "mssql"
"db.system" => "oracle"

// NoSQL
"db.system" => "mongodb"
"db.system" => "redis"
"db.system" => "cassandra"
"db.system" => "dynamodb"
```

### Redis示例

```rust
span.set_attribute(KeyValue::new("db.system", "redis"));
span.set_attribute(KeyValue::new("db.operation", "GET"));
span.set_attribute(KeyValue::new("db.statement", "GET user:123"));
span.set_attribute(KeyValue::new("db.redis.database_index", 0));
```

### MongoDB示例

```rust
span.set_attribute(KeyValue::new("db.system", "mongodb"));
span.set_attribute(KeyValue::new("db.operation", "find"));
span.set_attribute(KeyValue::new("db.name", "mydb"));
span.set_attribute(KeyValue::new("db.mongodb.collection", "users"));
```

---

## 📡 RPC语义

### gRPC Server

```rust
let mut span = tracer
    .span_builder("grpc.UserService/GetUser")
    .with_kind(SpanKind::Server)
    .start(&tracer);

// 必需属性
span.set_attribute(KeyValue::new("rpc.system", "grpc"));
span.set_attribute(KeyValue::new("rpc.service", "UserService"));
span.set_attribute(KeyValue::new("rpc.method", "GetUser"));

// gRPC特定
span.set_attribute(KeyValue::new("rpc.grpc.status_code", 0)); // OK
span.set_attribute(KeyValue::new("rpc.grpc.request.metadata.user-agent", "grpc-rust"));

// 网络属性
span.set_attribute(KeyValue::new("net.peer.ip", "192.168.1.100"));
span.set_attribute(KeyValue::new("net.peer.port", 50051));
```

### gRPC Client

```rust
let mut span = tracer
    .span_builder("grpc.UserService/GetUser")
    .with_kind(SpanKind::Client)
    .start(&tracer);

span.set_attribute(KeyValue::new("rpc.system", "grpc"));
span.set_attribute(KeyValue::new("rpc.service", "UserService"));
span.set_attribute(KeyValue::new("rpc.method", "GetUser"));
span.set_attribute(KeyValue::new("net.peer.name", "grpc-server.example.com"));
span.set_attribute(KeyValue::new("net.peer.port", 50051));
```

### gRPC状态码

```rust
// 成功
span.set_attribute(KeyValue::new("rpc.grpc.status_code", 0)); // OK

// 错误
span.set_attribute(KeyValue::new("rpc.grpc.status_code", 3)); // INVALID_ARGUMENT
span.set_attribute(KeyValue::new("rpc.grpc.status_code", 5)); // NOT_FOUND
span.set_attribute(KeyValue::new("rpc.grpc.status_code", 14)); // UNAVAILABLE
```

---

## 📨 消息系统

### Kafka Producer

```rust
let mut span = tracer
    .span_builder("send my-topic")
    .with_kind(SpanKind::Producer)
    .start(&tracer);

span.set_attribute(KeyValue::new("messaging.system", "kafka"));
span.set_attribute(KeyValue::new("messaging.destination.name", "my-topic"));
span.set_attribute(KeyValue::new("messaging.operation", "publish"));
span.set_attribute(KeyValue::new("messaging.kafka.partition", 0));
span.set_attribute(KeyValue::new("messaging.message.id", "msg-123"));

// 网络属性
span.set_attribute(KeyValue::new("net.peer.name", "kafka.example.com"));
span.set_attribute(KeyValue::new("net.peer.port", 9092));
```

### Kafka Consumer

```rust
let mut span = tracer
    .span_builder("receive my-topic")
    .with_kind(SpanKind::Consumer)
    .start(&tracer);

span.set_attribute(KeyValue::new("messaging.system", "kafka"));
span.set_attribute(KeyValue::new("messaging.destination.name", "my-topic"));
span.set_attribute(KeyValue::new("messaging.operation", "receive"));
span.set_attribute(KeyValue::new("messaging.kafka.consumer.group", "my-group"));
span.set_attribute(KeyValue::new("messaging.kafka.partition", 0));
span.set_attribute(KeyValue::new("messaging.kafka.message.offset", 12345));
```

### RabbitMQ

```rust
span.set_attribute(KeyValue::new("messaging.system", "rabbitmq"));
span.set_attribute(KeyValue::new("messaging.destination.name", "my-queue"));
span.set_attribute(KeyValue::new("messaging.rabbitmq.routing_key", "user.created"));
```

---

## 💻 系统指标

### CPU指标

```rust
let meter = global::meter("system");

// CPU使用率
let cpu_usage = meter
    .f64_observable_gauge("system.cpu.utilization")
    .with_description("CPU utilization")
    .with_unit("1") // 百分比 0-1
    .init();

// 按状态分类
cpu_usage.observe(0.75, &[
    KeyValue::new("cpu", "0"),
    KeyValue::new("state", "user"),
]);
```

### 内存指标

```rust
// 内存使用量
let memory_usage = meter
    .u64_observable_gauge("system.memory.usage")
    .with_unit("By") // 字节
    .init();

memory_usage.observe(1073741824, &[
    KeyValue::new("state", "used"),
]);

// 内存利用率
let memory_utilization = meter
    .f64_observable_gauge("system.memory.utilization")
    .with_unit("1")
    .init();

memory_utilization.observe(0.65, &[]);
```

### 网络指标

```rust
// 网络IO
let network_io = meter
    .u64_counter("system.network.io")
    .with_unit("By")
    .init();

network_io.add(1024, &[
    KeyValue::new("device", "eth0"),
    KeyValue::new("direction", "transmit"),
]);

// 网络错误
let network_errors = meter
    .u64_counter("system.network.errors")
    .init();

network_errors.add(1, &[
    KeyValue::new("device", "eth0"),
    KeyValue::new("direction", "receive"),
]);
```

### 磁盘指标

```rust
// 磁盘IO
let disk_io = meter
    .u64_counter("system.disk.io")
    .with_unit("By")
    .init();

disk_io.add(4096, &[
    KeyValue::new("device", "sda"),
    KeyValue::new("direction", "read"),
]);

// 磁盘使用率
let disk_usage = meter
    .f64_observable_gauge("system.filesystem.utilization")
    .with_unit("1")
    .init();

disk_usage.observe(0.80, &[
    KeyValue::new("device", "/dev/sda1"),
    KeyValue::new("mountpoint", "/"),
]);
```

---

## 🔥 运行时指标 (Rust)

### 进程指标

```rust
let meter = global::meter("runtime");

// CPU时间
let process_cpu_time = meter
    .f64_counter("process.cpu.time")
    .with_unit("s")
    .init();

process_cpu_time.add(1.25, &[
    KeyValue::new("state", "user"),
]);

// 内存使用
let process_memory = meter
    .u64_observable_gauge("process.runtime.memory")
    .with_unit("By")
    .init();

// Tokio任务数
let tokio_tasks = meter
    .i64_up_down_counter("runtime.tokio.tasks")
    .init();
```

---

## 🏷️ 自定义属性最佳实践

### 命名规范

```rust
// ✅ 好的命名
KeyValue::new("app.user.id", user_id)
KeyValue::new("app.feature.name", "search")
KeyValue::new("app.cache.hit", true)

// ❌ 避免
KeyValue::new("userId", user_id)           // 不使用驼峰
KeyValue::new("app_user_id", user_id)      // 不使用下划线
KeyValue::new("UserID", user_id)           // 不使用大写
```

### 基数控制

```rust
// ✅ 低基数 (适合作为标签)
KeyValue::new("http.method", "GET")        // ~10种值
KeyValue::new("http.status_code", 200)     // ~50种值
KeyValue::new("environment", "production") // ~3种值

// ❌ 高基数 (避免作为标签)
KeyValue::new("user.id", "12345")          // 百万级别
KeyValue::new("request.id", "uuid")        // 无限
KeyValue::new("timestamp", "2025-10-11")   // 时间序列
```

---

## 📊 完整示例

### HTTP服务器完整追踪

```rust
use axum::{extract::Request, middleware::Next, response::Response};
use opentelemetry::{global, trace::{Span, Tracer}, KeyValue};

pub async fn tracing_middleware(
    req: Request,
    next: Next,
) -> Response {
    let tracer = global::tracer("http-server");
    let method = req.method().clone();
    let uri = req.uri().clone();
    
    let mut span = tracer
        .span_builder(format!("{} {}", method, uri.path()))
        .with_kind(opentelemetry::trace::SpanKind::Server)
        .with_attributes(vec![
            // HTTP必需属性
            KeyValue::new("http.method", method.to_string()),
            KeyValue::new("http.scheme", uri.scheme_str().unwrap_or("http")),
            KeyValue::new("http.target", uri.path()),
            
            // 网络属性
            KeyValue::new("net.host.name", uri.host().unwrap_or("localhost")),
            KeyValue::new("net.host.port", uri.port_u16().unwrap_or(8080) as i64),
            
            // 自定义属性
            KeyValue::new("app.version", env!("CARGO_PKG_VERSION")),
        ])
        .start(&tracer);
    
    let response = next.run(req).await;
    
    // 添加响应属性
    span.set_attribute(KeyValue::new(
        "http.status_code",
        response.status().as_u16() as i64
    ));
    
    if response.status().is_success() {
        span.set_status(opentelemetry::trace::Status::Ok);
    } else {
        span.set_status(opentelemetry::trace::Status::error(
            format!("HTTP {}", response.status())
        ));
    }
    
    span.end();
    response
}
```

---

## 📚 参考资源

| 资源 | 链接 |
|------|------|
| **Semantic Conventions** | <https://opentelemetry.io/docs/specs/semconv/> |
| **HTTP Conventions** | <https://opentelemetry.io/docs/specs/semconv/http/> |
| **Database Conventions** | <https://opentelemetry.io/docs/specs/semconv/database/> |
| **Rust SDK** | <https://github.com/open-telemetry/opentelemetry-rust> |

---

**最后更新**: 2025年10月11日  
**Rust版本**: 1.90+  
**OpenTelemetry**: 0.31.0  
**上一篇**: [OTLP协议速查手册_Rust版](./01_OTLP协议速查手册_Rust版.md)  
**下一篇**: [Collector配置速查手册_Rust版](./03_Collector配置速查手册_Rust版.md)
