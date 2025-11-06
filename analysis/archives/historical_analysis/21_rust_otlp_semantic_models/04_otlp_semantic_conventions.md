# OTLP 语义约定与资源模型深度解析

> **版本**: OpenTelemetry 1.30+ (2025年规范)
> **日期**: 2025年10月2日
> **主题**: 语义约定、资源模型、属性架构、自解释数据

---

## 📋 目录

- [OTLP 语义约定与资源模型深度解析](#otlp-语义约定与资源模型深度解析)
  - [📋 目录](#-目录)
  - [OTLP 语义层架构](#otlp-语义层架构)
    - [1.1 三层语义模型](#11-三层语义模型)
    - [1.2 自解释数据原则](#12-自解释数据原则)
  - [Resource 资源模型](#resource-资源模型)
    - [2.1 Resource 定义](#21-resource-定义)
      - [Protobuf 定义](#protobuf-定义)
    - [2.2 标准资源属性](#22-标准资源属性)
      - [服务属性 (Service Attributes)](#服务属性-service-attributes)
      - [Kubernetes 属性](#kubernetes-属性)
      - [主机属性 (Host Attributes)](#主机属性-host-attributes)
      - [云平台属性 (Cloud Attributes)](#云平台属性-cloud-attributes)
    - [2.3 Rust 实现](#23-rust-实现)
  - [Semantic Conventions 语义约定](#semantic-conventions-语义约定)
    - [3.1 HTTP 语义约定 (v1.0 - 2025年冻结)](#31-http-语义约定-v10---2025年冻结)
      - [HTTP 请求属性](#http-请求属性)
      - [HTTP Span 示例](#http-span-示例)
    - [3.2 数据库语义约定](#32-数据库语义约定)
      - [通用数据库属性](#通用数据库属性)
      - [SQL 数据库特定属性](#sql-数据库特定属性)
      - [NoSQL 数据库特定属性](#nosql-数据库特定属性)
    - [3.3 消息队列语义约定](#33-消息队列语义约定)
      - [Kafka 属性](#kafka-属性)
      - [RabbitMQ 属性](#rabbitmq-属性)
    - [3.4 Gen-AI 语义约定 (Experimental - 2025)](#34-gen-ai-语义约定-experimental---2025)
      - [LLM 调用属性](#llm-调用属性)
  - [Trace 语义模型](#trace-语义模型)
    - [4.1 Span 结构](#41-span-结构)
    - [4.2 因果链模型](#42-因果链模型)
    - [4.3 Rust 实现](#43-rust-实现)
  - [Metric 语义模型](#metric-语义模型)
    - [5.1 Metric 类型](#51-metric-类型)
      - [Counter (计数器)](#counter-计数器)
      - [Gauge (仪表盘)](#gauge-仪表盘)
      - [Histogram (直方图)](#histogram-直方图)
    - [5.2 标准 Metric 命名约定](#52-标准-metric-命名约定)
      - [系统指标](#系统指标)
      - [HTTP 指标](#http-指标)
      - [数据库指标](#数据库指标)
  - [Log 语义模型](#log-语义模型)
    - [6.1 LogRecord 结构](#61-logrecord-结构)
    - [6.2 Rust 实现](#62-rust-实现)
  - [Profile 语义模型 (eBPF)](#profile-语义模型-ebpf)
    - [7.1 Profile 类型](#71-profile-类型)
    - [7.2 Profile 属性](#72-profile-属性)
  - [语义自省与机器可理解性](#语义自省与机器可理解性)
    - [8.1 自解释数据三元组](#81-自解释数据三元组)
    - [8.2 因果关联](#82-因果关联)
    - [8.3 机器决策能力](#83-机器决策能力)
  - [Rust 实现映射](#rust-实现映射)
    - [9.1 完整示例：OTLP 客户端](#91-完整示例otlp-客户端)
  - [📚 参考文献](#-参考文献)

---

## OTLP 语义层架构

### 1.1 三层语义模型

```text
┌─────────────────────────────────────────────────────────┐
│              应用层 (Application Layer)                  │
│  - 业务逻辑                                              │
│  - 领域模型                                              │
└───────────────────────────┬─────────────────────────────┘
                            │
┌───────────────────────────▼─────────────────────────────┐
│           语义层 (Semantic Layer) - OTLP                 │
├─────────────────────────────────────────────────────────┤
│  1. Resource Schema      │  service.name                 │
│                          │  k8s.pod.name                 │
│                          │  host.name                    │
├──────────────────────────┼──────────────────────────────┤
│  2. Signal Schema        │  Trace (Span)                 │
│                          │  Metric (DataPoint)           │
│                          │  Log (LogRecord)              │
│                          │  Profile (Sample)             │
├──────────────────────────┼──────────────────────────────┤
│  3. Attribute Schema     │  http.method = "GET"          │
│                          │  db.system = "postgresql"     │
│                          │  messaging.system = "kafka"   │
└───────────────────────────┬─────────────────────────────┘
                            │
┌───────────────────────────▼─────────────────────────────┐
│           传输层 (Transport Layer)                       │
│  - gRPC (Binary Protobuf)                               │
│  - HTTP (JSON / Protobuf)                               │
└─────────────────────────────────────────────────────────┘
```

### 1.2 自解释数据原则

OTLP 的核心设计理念是 **"数据即模型"**：

```text
传统日志：
  "User logged in from 192.168.1.1"
  ❌ 需要人工解析，机器无法理解

OTLP 日志：
  {
    "resource": {
      "service.name": "auth-service",
      "service.version": "1.2.3",
      "deployment.environment": "production"
    },
    "body": "User logged in",
    "attributes": {
      "user.id": "12345",
      "user.ip": "192.168.1.1",
      "event.name": "login",
      "event.outcome": "success"
    },
    "trace_id": "abc123...",
    "span_id": "def456..."
  }
  ✅ 机器可直接理解：谁、何时、何地、做了什么
```

---

## Resource 资源模型

### 2.1 Resource 定义

Resource 表示产生遥测数据的 **实体**，是所有信号的共享上下文。

#### Protobuf 定义

```protobuf
message Resource {
  // 属性列表
  repeated KeyValue attributes = 1;

  // 已丢弃的属性数量
  uint32 dropped_attributes_count = 2;
}

message KeyValue {
  string key = 1;
  AnyValue value = 2;
}

message AnyValue {
  oneof value {
    string string_value = 1;
    bool bool_value = 2;
    int64 int_value = 3;
    double double_value = 4;
    ArrayValue array_value = 5;
    KeyValueList kvlist_value = 6;
    bytes bytes_value = 7;
  }
}
```

### 2.2 标准资源属性

#### 服务属性 (Service Attributes)

| 属性名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `service.name` | string | **必填** 服务名称 | `auth-service` |
| `service.version` | string | 服务版本 | `1.2.3` |
| `service.namespace` | string | 服务命名空间 | `production` |
| `service.instance.id` | string | 服务实例 ID | `pod-abc123` |

#### Kubernetes 属性

| 属性名 | 类型 | 描述 |
|--------|------|------|
| `k8s.cluster.name` | string | 集群名称 |
| `k8s.namespace.name` | string | 命名空间 |
| `k8s.pod.name` | string | Pod 名称 |
| `k8s.pod.uid` | string | Pod UID |
| `k8s.node.name` | string | 节点名称 |
| `k8s.deployment.name` | string | Deployment 名称 |

#### 主机属性 (Host Attributes)

| 属性名 | 类型 | 描述 |
|--------|------|------|
| `host.name` | string | 主机名 |
| `host.id` | string | 主机唯一 ID |
| `host.type` | string | 主机类型 (`physical`, `virtual`) |
| `host.arch` | string | CPU 架构 (`amd64`, `arm64`) |
| `host.ip` | string[] | IP 地址列表 |

#### 云平台属性 (Cloud Attributes)

| 属性名 | 类型 | 描述 |
|--------|------|------|
| `cloud.provider` | string | `aws`, `gcp`, `azure` |
| `cloud.account.id` | string | 账户 ID |
| `cloud.region` | string | 区域 (`us-west-2`) |
| `cloud.availability_zone` | string | 可用区 |
| `cloud.platform` | string | `aws_ec2`, `gcp_compute_engine` |

### 2.3 Rust 实现

```rust
use std::collections::HashMap;
use serde::{Serialize, Deserialize};

/// Resource 资源模型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Resource {
    pub attributes: HashMap<String, AttributeValue>,
    pub dropped_attributes_count: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
pub enum AttributeValue {
    String(String),
    Bool(bool),
    Int(i64),
    Double(f64),
    Array(Vec<AttributeValue>),
    Map(HashMap<String, AttributeValue>),
}

impl Resource {
    /// 创建新的 Resource
    pub fn new() -> Self {
        Self {
            attributes: HashMap::new(),
            dropped_attributes_count: 0,
        }
    }

    /// 添加服务信息
    pub fn with_service(mut self, name: &str, version: &str) -> Self {
        self.attributes.insert(
            "service.name".to_string(),
            AttributeValue::String(name.to_string()),
        );
        self.attributes.insert(
            "service.version".to_string(),
            AttributeValue::String(version.to_string()),
        );
        self
    }

    /// 添加 Kubernetes 信息
    pub fn with_kubernetes(
        mut self,
        namespace: &str,
        pod_name: &str,
        cluster: &str,
    ) -> Self {
        self.attributes.insert(
            "k8s.namespace.name".to_string(),
            AttributeValue::String(namespace.to_string()),
        );
        self.attributes.insert(
            "k8s.pod.name".to_string(),
            AttributeValue::String(pod_name.to_string()),
        );
        self.attributes.insert(
            "k8s.cluster.name".to_string(),
            AttributeValue::String(cluster.to_string()),
        );
        self
    }

    /// 添加主机信息
    pub fn with_host(mut self, name: &str, arch: &str) -> Self {
        self.attributes.insert(
            "host.name".to_string(),
            AttributeValue::String(name.to_string()),
        );
        self.attributes.insert(
            "host.arch".to_string(),
            AttributeValue::String(arch.to_string()),
        );
        self
    }

    /// 添加云平台信息
    pub fn with_cloud(mut self, provider: &str, region: &str) -> Self {
        self.attributes.insert(
            "cloud.provider".to_string(),
            AttributeValue::String(provider.to_string()),
        );
        self.attributes.insert(
            "cloud.region".to_string(),
            AttributeValue::String(region.to_string()),
        );
        self
    }
}

/// 使用示例
fn resource_example() {
    let resource = Resource::new()
        .with_service("payment-service", "2.1.0")
        .with_kubernetes("production", "payment-pod-abc", "prod-cluster")
        .with_host("node-01", "amd64")
        .with_cloud("aws", "us-west-2");

    println!("{:?}", resource);
}
```

---

## Semantic Conventions 语义约定

### 3.1 HTTP 语义约定 (v1.0 - 2025年冻结)

#### HTTP 请求属性

| 属性名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `http.method` | string | HTTP 方法 | `GET`, `POST` |
| `http.url` | string | 完整 URL | `https://api.example.com/v1/users` |
| `http.target` | string | 请求目标 | `/v1/users?id=123` |
| `http.host` | string | 主机名 | `api.example.com` |
| `http.scheme` | string | 协议 | `http`, `https` |
| `http.status_code` | int | 状态码 | `200`, `404` |
| `http.user_agent` | string | User-Agent | `Mozilla/5.0...` |
| `http.request_content_length` | int | 请求体大小 | `1024` |
| `http.response_content_length` | int | 响应体大小 | `2048` |

#### HTTP Span 示例

```rust
use opentelemetry::trace::{Tracer, SpanKind};
use opentelemetry::KeyValue;

async fn http_request_span(tracer: &dyn Tracer) {
    let span = tracer
        .span_builder("HTTP GET /v1/users")
        .with_kind(SpanKind::Client)
        .with_attributes(vec![
            KeyValue::new("http.method", "GET"),
            KeyValue::new("http.url", "https://api.example.com/v1/users"),
            KeyValue::new("http.target", "/v1/users"),
            KeyValue::new("http.host", "api.example.com"),
            KeyValue::new("http.scheme", "https"),
            KeyValue::new("http.status_code", 200),
        ])
        .start(tracer);

    // 执行请求...

    drop(span); // 结束 Span
}
```

### 3.2 数据库语义约定

#### 通用数据库属性

| 属性名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `db.system` | string | 数据库类型 | `postgresql`, `mysql`, `mongodb` |
| `db.connection_string` | string | 连接字符串 (脱敏) | `Server=localhost;Database=mydb` |
| `db.user` | string | 数据库用户 | `app_user` |
| `db.name` | string | 数据库名称 | `customer_db` |
| `db.statement` | string | SQL 语句 | `SELECT * FROM users WHERE id = ?` |
| `db.operation` | string | 操作类型 | `SELECT`, `INSERT`, `UPDATE` |

#### SQL 数据库特定属性

| 属性名 | 类型 | 描述 |
|--------|------|------|
| `db.sql.table` | string | 表名 |
| `db.sql.primary_key` | string | 主键值 |

#### NoSQL 数据库特定属性

| 属性名 | 类型 | 描述 |
|--------|------|------|
| `db.mongodb.collection` | string | MongoDB 集合 |
| `db.cassandra.keyspace` | string | Cassandra Keyspace |
| `db.redis.database_index` | int | Redis 数据库索引 |

### 3.3 消息队列语义约定

#### Kafka 属性

| 属性名 | 类型 | 描述 |
|--------|------|------|
| `messaging.system` | string | `kafka` |
| `messaging.destination` | string | Topic 名称 |
| `messaging.destination_kind` | string | `topic` |
| `messaging.kafka.partition` | int | 分区号 |
| `messaging.kafka.message_key` | string | 消息 Key |
| `messaging.kafka.consumer_group` | string | 消费者组 |

#### RabbitMQ 属性

| 属性名 | 类型 | 描述 |
|--------|------|------|
| `messaging.system` | string | `rabbitmq` |
| `messaging.destination` | string | Queue 名称 |
| `messaging.rabbitmq.routing_key` | string | 路由键 |

### 3.4 Gen-AI 语义约定 (Experimental - 2025)

#### LLM 调用属性

| 属性名 | 类型 | 描述 |
|--------|------|------|
| `gen_ai.system` | string | `openai`, `anthropic`, `huggingface` |
| `gen_ai.request.model` | string | 模型名称 (`gpt-4`, `claude-3`) |
| `gen_ai.request.max_tokens` | int | 最大 Token 数 |
| `gen_ai.request.temperature` | float | 温度参数 |
| `gen_ai.response.id` | string | 响应 ID |
| `gen_ai.response.model` | string | 实际使用的模型 |
| `gen_ai.usage.input_tokens` | int | 输入 Token 数 |
| `gen_ai.usage.output_tokens` | int | 输出 Token 数 |

---

## Trace 语义模型

### 4.1 Span 结构

```protobuf
message Span {
  bytes trace_id = 1;              // 128-bit Trace ID
  bytes span_id = 2;               // 64-bit Span ID
  string trace_state = 3;          // W3C Trace State
  bytes parent_span_id = 4;        // 父 Span ID
  string name = 5;                 // Span 名称
  SpanKind kind = 6;               // Span 类型
  fixed64 start_time_unix_nano = 7;
  fixed64 end_time_unix_nano = 8;
  repeated KeyValue attributes = 9;
  uint32 dropped_attributes_count = 10;
  repeated Event events = 11;
  repeated Link links = 12;
  Status status = 13;
}

enum SpanKind {
  SPAN_KIND_UNSPECIFIED = 0;
  SPAN_KIND_INTERNAL = 1;    // 内部操作
  SPAN_KIND_SERVER = 2;      // 服务端接收请求
  SPAN_KIND_CLIENT = 3;      // 客户端发起请求
  SPAN_KIND_PRODUCER = 4;    // 消息生产者
  SPAN_KIND_CONSUMER = 5;    // 消息消费者
}
```

### 4.2 因果链模型

```text
Trace: abc123...
  ├─ Span A (Server)     span_id=001, parent=null
  │  ├─ Span B (Internal) span_id=002, parent=001
  │  │  ├─ Span C (Client)  span_id=003, parent=002
  │  │  └─ Span D (Client)  span_id=004, parent=002
  │  └─ Span E (Internal) span_id=005, parent=001
  └─ (跨服务边界)
     └─ Span F (Server)   span_id=006, parent=003, trace_id=abc123
```

### 4.3 Rust 实现

```rust
use opentelemetry::{
    trace::{Tracer, TracerProvider, Span, SpanKind, Status},
    KeyValue,
};
use opentelemetry_sdk::trace::{self, Sampler, Config};
use opentelemetry_otlp::WithExportConfig;

/// 创建 Tracer
pub fn create_tracer() -> trace::Tracer {
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .build_span_exporter()
        .expect("Failed to create exporter");

    let provider = trace::TracerProvider::builder()
        .with_batch_exporter(exporter, opentelemetry_sdk::runtime::Tokio)
        .with_config(
            Config::default()
                .with_sampler(Sampler::AlwaysOn)
                .with_max_events_per_span(128)
                .with_max_attributes_per_span(128),
        )
        .build();

    opentelemetry::global::set_tracer_provider(provider.clone());
    provider.tracer("otlp-example")
}

/// 分布式追踪示例
async fn distributed_trace_example() {
    let tracer = create_tracer();

    // 父 Span (服务端)
    let mut parent_span = tracer
        .span_builder("handle_request")
        .with_kind(SpanKind::Server)
        .with_attributes(vec![
            KeyValue::new("http.method", "POST"),
            KeyValue::new("http.target", "/api/v1/order"),
        ])
        .start(&tracer);

    // 嵌套 Span (内部操作)
    {
        let _guard = parent_span.enter();
        let mut internal_span = tracer
            .span_builder("process_payment")
            .with_kind(SpanKind::Internal)
            .start(&tracer);

        // 业务逻辑...

        internal_span.set_attribute(KeyValue::new("payment.amount", 99.99));
        internal_span.set_status(Status::Ok);
    }

    // 子 Span (客户端调用)
    {
        let _guard = parent_span.enter();
        let mut client_span = tracer
            .span_builder("call_inventory_service")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("peer.service", "inventory-service"),
                KeyValue::new("rpc.system", "grpc"),
            ])
            .start(&tracer);

        // gRPC 调用...

        client_span.set_status(Status::Ok);
    }

    parent_span.set_status(Status::Ok);
}
```

---

## Metric 语义模型

### 5.1 Metric 类型

#### Counter (计数器)

单调递增，用于统计事件次数：

```rust
use opentelemetry::metrics::{Counter, MeterProvider};

fn counter_example(meter_provider: &dyn MeterProvider) {
    let meter = meter_provider.meter("app");
    let counter = meter
        .u64_counter("http.server.requests")
        .with_description("HTTP 请求总数")
        .with_unit("{request}")
        .build();

    counter.add(1, &[
        KeyValue::new("http.method", "GET"),
        KeyValue::new("http.status_code", 200),
    ]);
}
```

#### Gauge (仪表盘)

瞬时值，可增可减：

```rust
use opentelemetry::metrics::Gauge;

fn gauge_example(meter_provider: &dyn MeterProvider) {
    let meter = meter_provider.meter("app");
    let gauge = meter
        .i64_gauge("system.cpu.utilization")
        .with_description("CPU 使用率")
        .with_unit("1")  // 无单位
        .build();

    gauge.record(75, &[
        KeyValue::new("cpu.id", "0"),
    ]);
}
```

#### Histogram (直方图)

分布统计，记录值的范围：

```rust
use opentelemetry::metrics::Histogram;

fn histogram_example(meter_provider: &dyn MeterProvider) {
    let meter = meter_provider.meter("app");
    let histogram = meter
        .f64_histogram("http.server.duration")
        .with_description("HTTP 请求时长")
        .with_unit("ms")
        .build();

    histogram.record(123.45, &[
        KeyValue::new("http.method", "POST"),
        KeyValue::new("http.route", "/api/v1/users"),
    ]);
}
```

### 5.2 标准 Metric 命名约定

#### 系统指标

- `system.cpu.utilization` - CPU 使用率 (0-1)
- `system.memory.usage` - 内存使用量 (bytes)
- `system.disk.io` - 磁盘 I/O (bytes)
- `system.network.io` - 网络 I/O (bytes)

#### HTTP 指标

- `http.server.requests` - 服务端请求数
- `http.server.duration` - 服务端请求时长 (ms)
- `http.client.requests` - 客户端请求数
- `http.client.duration` - 客户端请求时长 (ms)

#### 数据库指标

- `db.client.calls` - 数据库调用次数
- `db.client.duration` - 数据库调用时长 (ms)
- `db.client.connections.usage` - 连接池使用量

---

## Log 语义模型

### 6.1 LogRecord 结构

```protobuf
message LogRecord {
  fixed64 time_unix_nano = 1;
  fixed64 observed_time_unix_nano = 2;
  SeverityNumber severity_number = 3;
  string severity_text = 4;
  AnyValue body = 5;
  repeated KeyValue attributes = 6;
  uint32 dropped_attributes_count = 7;
  uint32 flags = 8;
  bytes trace_id = 9;     // 关联 Trace
  bytes span_id = 10;     // 关联 Span
}

enum SeverityNumber {
  SEVERITY_NUMBER_UNSPECIFIED = 0;
  SEVERITY_NUMBER_TRACE = 1;
  SEVERITY_NUMBER_DEBUG = 5;
  SEVERITY_NUMBER_INFO = 9;
  SEVERITY_NUMBER_WARN = 13;
  SEVERITY_NUMBER_ERROR = 17;
  SEVERITY_NUMBER_FATAL = 21;
}
```

### 6.2 Rust 实现

```rust
use opentelemetry::logs::{Logger, LogRecord, Severity};
use opentelemetry::KeyValue;

fn log_example() {
    let logger = opentelemetry::global::logger("app");

    logger.emit(
        LogRecord::builder()
            .with_severity_number(Severity::Error)
            .with_severity_text("ERROR")
            .with_body("Database connection failed")
            .with_attributes(vec![
                KeyValue::new("error.type", "ConnectionError"),
                KeyValue::new("db.system", "postgresql"),
                KeyValue::new("db.host", "db.example.com"),
            ])
            .build()
    );
}
```

---

## Profile 语义模型 (eBPF)

### 7.1 Profile 类型

基于 Google pprof 格式：

```protobuf
message Profile {
  repeated Sample sample = 1;
  repeated Location location = 2;
  repeated Function function = 3;
  repeated string string_table = 4;
  int64 time_nanos = 5;
  int64 duration_nanos = 6;
  ProfileType profile_type = 7;
}

message Sample {
  repeated uint64 location_id = 1;
  repeated int64 value = 2;
  repeated Label label = 3;
}
```

### 7.2 Profile 属性

| 属性名 | 类型 | 描述 |
|--------|------|------|
| `profile.type` | string | `cpu`, `heap`, `lock`, `wall` |
| `profile.sample_period` | int | 采样周期 (Hz) |
| `profile.collision` | string | `kernel`, `user`, `mixed` |

---

## 语义自省与机器可理解性

### 8.1 自解释数据三元组

```text
数据 = (Resource, Signal, Attributes)

其中：
  Resource  → 回答 "Who/Where"  (谁产生的数据，在哪里)
  Signal    → 回答 "What"        (什么类型的数据)
  Attributes → 回答 "How/Why"    (如何发生的，为什么)
```

### 8.2 因果关联

通过 `TraceId` 和 `SpanId` 自动拼接：

```rust
// Trace Span
span_id = "abc123"
trace_id = "def456"

// Metric DataPoint
attributes = [
  ("trace_id", "def456"),
  ("span_id", "abc123"),
]

// Log Record
trace_id = "def456"
span_id = "abc123"

// Profile Sample
labels = [
  ("trace_id", "def456"),
  ("span_id", "abc123"),
]

// 结果：四支柱数据自动关联，形成统一视图
```

### 8.3 机器决策能力

```rust
/// OTTL 规则示例
/// 自动检测慢 HTTP 请求并标记
pub fn ottl_slow_request_detection() {
    let ottl_rule = r#"
        set(span.status.message, "slow_request_detected")
        where span.kind == SPAN_KIND_SERVER
        and span.attributes["http.method"] == "GET"
        and duration > 3s
    "#;

    // OTTL 引擎可在 Collector 中实时执行
}

/// 基于语义属性的自动路由
pub fn semantic_routing() {
    let ottl_rule = r#"
        route() where resource.attributes["tenant"] == "premium"
        → kafka_exporter(topic="premium-traces")

        route() where resource.attributes["tenant"] == "free"
        → sampling_processor(ratio=0.01)
        → kafka_exporter(topic="free-traces")
    "#;
}
```

---

## Rust 实现映射

### 9.1 完整示例：OTLP 客户端

```rust
use opentelemetry::{
    global,
    trace::{Tracer, TracerProvider},
    metrics::MeterProvider,
    logs::LoggerProvider,
    KeyValue,
};
use opentelemetry_sdk::{
    trace::{self as sdk_trace, Sampler},
    metrics::{self as sdk_metrics, PeriodicReader},
    logs::{self as sdk_logs},
    Resource,
};
use opentelemetry_otlp::{
    WithExportConfig,
    Protocol,
};
use opentelemetry_semantic_conventions as semcov;

/// 初始化 OTLP 客户端（三支柱）
pub async fn init_otlp_client() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 创建 Resource
    let resource = Resource::new(vec![
        KeyValue::new(semcov::resource::SERVICE_NAME, "my-service"),
        KeyValue::new(semcov::resource::SERVICE_VERSION, "1.0.0"),
        KeyValue::new(semcov::resource::DEPLOYMENT_ENVIRONMENT, "production"),
        KeyValue::new("k8s.pod.name", "my-pod-abc"),
        KeyValue::new("k8s.namespace.name", "default"),
    ]);

    // 2. 初始化 Trace Provider
    let tracer_provider = sdk_trace::TracerProvider::builder()
        .with_batch_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
                .with_protocol(Protocol::Grpc)
                .build_span_exporter()?,
            opentelemetry_sdk::runtime::Tokio,
        )
        .with_config(
            sdk_trace::Config::default()
                .with_resource(resource.clone())
                .with_sampler(Sampler::TraceIdRatioBased(0.1)),
        )
        .build();

    global::set_tracer_provider(tracer_provider.clone());

    // 3. 初始化 Meter Provider
    let meter_provider = sdk_metrics::MeterProvider::builder()
        .with_reader(
            PeriodicReader::builder(
                opentelemetry_otlp::new_exporter()
                    .tonic()
                    .build_metrics_exporter(
                        Box::new(opentelemetry_sdk::metrics::aggregation::DefaultAggregationSelector::new()),
                        Box::new(opentelemetry_sdk::metrics::data::Temporality::Cumulative),
                    )?,
                opentelemetry_sdk::runtime::Tokio,
            )
            .with_interval(std::time::Duration::from_secs(30))
            .build(),
        )
        .with_resource(resource.clone())
        .build();

    global::set_meter_provider(meter_provider);

    // 4. 初始化 Logger Provider
    let logger_provider = sdk_logs::LoggerProvider::builder()
        .with_batch_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .build_log_exporter()?,
            opentelemetry_sdk::runtime::Tokio,
        )
        .with_resource(resource)
        .build();

    global::set_logger_provider(logger_provider);

    Ok(())
}

/// 使用三支柱
pub async fn use_three_pillars() {
    // Trace
    let tracer = global::tracer("my-tracer");
    let span = tracer.span_builder("my-operation").start(&tracer);

    // Metric
    let meter = global::meter("my-meter");
    let counter = meter.u64_counter("my_counter").build();
    counter.add(1, &[KeyValue::new("key", "value")]);

    // Log
    let logger = global::logger("my-logger");
    // logger.emit(...);
}
```

---

## 📚 参考文献

1. **OpenTelemetry Specification**: <https://opentelemetry.io/docs/specs/otel/>
2. **Semantic Conventions**: <https://opentelemetry.io/docs/specs/semconv/>
3. **OTLP Protocol**: <https://opentelemetry.io/docs/specs/otlp/>
4. **Resource Semantic Conventions**: <https://opentelemetry.io/docs/specs/semconv/resource/>
5. **HTTP Semantic Conventions**: <https://opentelemetry.io/docs/specs/semconv/http/>

---

**最后更新**: 2025年10月2日
**作者**: OTLP Rust 项目组
