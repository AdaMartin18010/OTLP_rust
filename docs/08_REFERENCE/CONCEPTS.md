# 参考文档核心概念

**版本**: 2.0
**日期**: 2025年10月28日
**状态**: ✅ 完整

---

## 📋 目录

- [参考文档核心概念](#参考文档核心概念)
  - [📋 目录](#-目录)
  - [📖 语义约定](#-语义约定)
    - [1.1 OpenTelemetry语义约定](#11-opentelemetry语义约定)
      - [定义](#定义)
      - [内涵（本质特征）](#内涵本质特征)
      - [外延（涵盖范围）](#外延涵盖范围)
      - [属性](#属性)
      - [关系](#关系)
      - [示例](#示例)
  - [🔍 资源属性](#-资源属性)
    - [2.1 标准资源属性](#21-标准资源属性)
      - [定义](#定义-1)
      - [内涵（本质特征）](#内涵本质特征-1)
      - [外延（涵盖范围）](#外延涵盖范围-1)
      - [属性](#属性-1)
      - [关系](#关系-1)
      - [示例](#示例-1)
  - [💡 Span属性](#-span属性)
    - [3.1 Span生命周期](#31-span生命周期)
      - [定义](#定义-2)
      - [内涵（本质特征）](#内涵本质特征-2)
      - [外延（涵盖范围）](#外延涵盖范围-2)
      - [属性](#属性-2)
      - [关系](#关系-2)
      - [示例](#示例-2)
  - [⚙️ 指标命名](#️-指标命名)
    - [4.1 指标命名约定](#41-指标命名约定)
      - [定义](#定义-3)
      - [内涵（本质特征）](#内涵本质特征-3)
      - [外延（涵盖范围）](#外延涵盖范围-3)
      - [属性](#属性-3)
      - [关系](#关系-3)
      - [示例](#示例-3)
  - [🔗 相关资源](#-相关资源)

---

## 📖 语义约定

### 1.1 OpenTelemetry语义约定

#### 定义

**形式化定义**: Semantic Conventions SC = (namespace, attributes, conventions)

**命名规范**:

```text
namespace.attribute_name

示例:
- http.method
- db.system
- messaging.operation
```

**通俗解释**: 统一的命名规范，确保不同实现之间的互操作性。

#### 内涵（本质特征）

- **标准化**: 统一命名，避免歧义
- **分层次**: namespace组织
- **可扩展**: 支持自定义
- **向后兼容**: 稳定演进

#### 外延（涵盖范围）

- 包含: HTTP、数据库、消息队列、RPC等
- 不包含: 业务特定属性（需自定义）

#### 属性

| 属性类别 | 命名空间 | 示例 |
|---------|---------|------|
| HTTP | `http.*` | http.method, http.status_code |
| 数据库 | `db.*` | db.system, db.statement |
| RPC | `rpc.*` | rpc.service, rpc.method |
| 消息 | `messaging.*` | messaging.system, messaging.operation |
| 网络 | `net.*` | net.peer.name, net.peer.port |

#### 关系

- 与**互操作性**的关系: 语义约定是互操作的基础
- 与**兼容性**的关系: 遵循约定保证兼容
- 与**工具生态**的关系: 工具基于约定工作

#### 示例

```rust
use opentelemetry::KeyValue;
use opentelemetry_semantic_conventions as semconv;

// 1. HTTP语义约定
fn add_http_attributes(span: &mut Span, req: &Request, resp: &Response) {
    // 请求属性
    span.set_attribute(KeyValue::new(
        semconv::trace::HTTP_METHOD,  // "http.method"
        req.method().to_string()
    ));

    span.set_attribute(KeyValue::new(
        semconv::trace::HTTP_URL,     // "http.url"
        req.uri().to_string()
    ));

    span.set_attribute(KeyValue::new(
        semconv::trace::HTTP_TARGET,  // "http.target"
        req.uri().path()
    ));

    // 响应属性
    span.set_attribute(KeyValue::new(
        semconv::trace::HTTP_STATUS_CODE,  // "http.status_code"
        resp.status().as_u16()
    ));

    // 客户端信息
    if let Some(user_agent) = req.headers().get("user-agent") {
        span.set_attribute(KeyValue::new(
            semconv::trace::HTTP_USER_AGENT,  // "http.user_agent"
            user_agent.to_str().unwrap_or("")
        ));
    }
}

// 2. 数据库语义约定
fn add_db_attributes(span: &mut Span, query: &Query) {
    span.set_attribute(KeyValue::new(
        semconv::trace::DB_SYSTEM,     // "db.system"
        "postgresql"
    ));

    span.set_attribute(KeyValue::new(
        semconv::trace::DB_NAME,       // "db.name"
        query.database()
    ));

    span.set_attribute(KeyValue::new(
        semconv::trace::DB_STATEMENT,  // "db.statement"
        query.sql()
    ));

    span.set_attribute(KeyValue::new(
        semconv::trace::DB_OPERATION,  // "db.operation"
        query.operation()  // SELECT, INSERT, UPDATE, DELETE
    ));

    // 连接信息
    span.set_attribute(KeyValue::new(
        semconv::trace::NET_PEER_NAME,  // "net.peer.name"
        query.host()
    ));

    span.set_attribute(KeyValue::new(
        semconv::trace::NET_PEER_PORT,  // "net.peer.port"
        query.port()
    ));
}

// 3. RPC语义约定
fn add_rpc_attributes(span: &mut Span, call: &RpcCall) {
    span.set_attribute(KeyValue::new(
        semconv::trace::RPC_SYSTEM,    // "rpc.system"
        "grpc"
    ));

    span.set_attribute(KeyValue::new(
        semconv::trace::RPC_SERVICE,   // "rpc.service"
        call.service()
    ));

    span.set_attribute(KeyValue::new(
        semconv::trace::RPC_METHOD,    // "rpc.method"
        call.method()
    ));

    // gRPC特定
    span.set_attribute(KeyValue::new(
        "rpc.grpc.status_code",        // gRPC状态码
        call.status_code()
    ));
}

// 4. 消息队列语义约定
fn add_messaging_attributes(span: &mut Span, msg: &Message) {
    span.set_attribute(KeyValue::new(
        semconv::trace::MESSAGING_SYSTEM,     // "messaging.system"
        "kafka"
    ));

    span.set_attribute(KeyValue::new(
        semconv::trace::MESSAGING_DESTINATION,  // "messaging.destination"
        msg.topic()
    ));

    span.set_attribute(KeyValue::new(
        semconv::trace::MESSAGING_OPERATION,   // "messaging.operation"
        "publish"  // 或 "receive", "process"
    ));

    span.set_attribute(KeyValue::new(
        "messaging.message_id",               // 消息ID
        msg.id()
    ));

    span.set_attribute(KeyValue::new(
        "messaging.kafka.partition",          // Kafka特定
        msg.partition()
    ));
}

// 5. 完整示例：HTTP服务器
#[instrument(
    fields(
        %http.method = req.method(),
        %http.url = req.uri(),
        http.status_code = tracing::field::Empty,
    )
)]
async fn handle_http_request(req: Request) -> Result<Response> {
    let span = Span::current();

    // 处理请求
    let response = process_request(&req).await?;

    // 记录响应状态
    span.record("http.status_code", response.status().as_u16());

    Ok(response)
}

// 语义约定的好处
/*
1. 互操作性：
   - 不同SDK生成的数据可以统一分析
   - 工具可以识别标准属性

2. 可发现性：
   - 标准属性有明确含义
   - 容易理解和查询

3. 生态集成：
   - 监控工具自动识别标准属性
   - 自动生成有意义的图表

示例查询：
SELECT * FROM spans
WHERE "http.method" = 'POST'
  AND "http.status_code" >= 500
  AND "db.system" = 'postgresql'
*/
```

---

## 🔍 资源属性

### 2.1 标准资源属性

#### 定义

**形式化定义**: Resource R = {(key, value)} where key ∈ StandardAttributes

**常用属性**:

```text
service.name         - 服务名称 (必需)
service.version      - 服务版本
service.namespace    - 命名空间
deployment.environment - 环境 (prod/dev)
host.name            - 主机名
container.name       - 容器名
k8s.pod.name         - Pod名称
```

**通俗解释**: 描述产生遥测数据的实体的标准属性。

#### 内涵（本质特征）

- **全局性**: 对所有信号生效
- **标识性**: 唯一标识数据源
- **分层性**: 服务→实例→容器→Pod
- **标准化**: 使用语义约定

#### 外延（涵盖范围）

- 包含: 服务、部署、主机、容器、K8s
- 不包含: 请求级属性（在Span中）

#### 属性

| 类别 | 属性名 | 示例值 | 说明 |
|------|--------|--------|------|
| 服务 | service.name | "otlp-receiver" | 服务名 |
| 服务 | service.version | "1.0.0" | 版本 |
| 部署 | deployment.environment | "production" | 环境 |
| 主机 | host.name | "server-01" | 主机 |
| 容器 | container.name | "otlp-receiver-abc" | 容器 |
| K8s | k8s.pod.name | "otlp-receiver-7d8f4b" | Pod |
| K8s | k8s.namespace.name | "observability" | 命名空间 |

#### 关系

- 与**Service**的关系: service.name标识服务
- 与**部署**的关系: 环境和版本信息
- 与**基础设施**的关系: 主机和容器信息

#### 示例

```rust
use opentelemetry::sdk::Resource;
use opentelemetry::KeyValue;
use opentelemetry_semantic_conventions as semconv;

// 1. 创建标准Resource
pub fn create_resource() -> Resource {
    Resource::new(vec![
        // 服务信息 (必需)
        KeyValue::new(
            semconv::resource::SERVICE_NAME,
            "otlp-receiver"
        ),
        KeyValue::new(
            semconv::resource::SERVICE_VERSION,
            env!("CARGO_PKG_VERSION")
        ),
        KeyValue::new(
            semconv::resource::SERVICE_NAMESPACE,
            "production"
        ),

        // 部署信息
        KeyValue::new(
            semconv::resource::DEPLOYMENT_ENVIRONMENT,
            std::env::var("ENVIRONMENT").unwrap_or_else(|_| "dev".to_string())
        ),

        // 主机信息
        KeyValue::new(
            semconv::resource::HOST_NAME,
            hostname::get()
                .unwrap_or_default()
                .to_string_lossy()
                .to_string()
        ),
        KeyValue::new(
            semconv::resource::HOST_ARCH,
            std::env::consts::ARCH
        ),

        // 容器信息（如果在容器中）
        KeyValue::new(
            semconv::resource::CONTAINER_NAME,
            std::env::var("HOSTNAME").unwrap_or_default()
        ),
        KeyValue::new(
            semconv::resource::CONTAINER_ID,
            read_container_id().unwrap_or_default()
        ),

        // Kubernetes信息（如果在K8s中）
        KeyValue::new(
            semconv::resource::K8S_POD_NAME,
            std::env::var("K8S_POD_NAME").unwrap_or_default()
        ),
        KeyValue::new(
            semconv::resource::K8S_NAMESPACE_NAME,
            std::env::var("K8S_NAMESPACE").unwrap_or_default()
        ),
        KeyValue::new(
            semconv::resource::K8S_DEPLOYMENT_NAME,
            std::env::var("K8S_DEPLOYMENT_NAME").unwrap_or_default()
        ),
    ])
}

// 2. 自动检测Resource
pub fn create_resource_with_detection() -> Resource {
    let mut resource = Resource::default();

    // 检测服务信息
    resource = resource.merge(&Resource::new(vec![
        KeyValue::new(semconv::resource::SERVICE_NAME, detect_service_name()),
        KeyValue::new(semconv::resource::SERVICE_VERSION, detect_version()),
    ]));

    // 检测主机信息
    if let Some(host_resource) = detect_host() {
        resource = resource.merge(&host_resource);
    }

    // 检测容器信息
    if let Some(container_resource) = detect_container() {
        resource = resource.merge(&container_resource);
    }

    // 检测K8s信息
    if let Some(k8s_resource) = detect_kubernetes() {
        resource = resource.merge(&k8s_resource);
    }

    resource
}

// 3. Resource查询示例
/*
查询某个服务的所有traces：
SELECT * FROM traces
WHERE resource["service.name"] = 'otlp-receiver'

查询生产环境的错误：
SELECT * FROM traces
WHERE resource["deployment.environment"] = 'production'
  AND status = 'ERROR'

按Pod聚合：
SELECT resource["k8s.pod.name"], COUNT(*)
FROM traces
GROUP BY resource["k8s.pod.name"]

多维度过滤：
SELECT * FROM traces
WHERE resource["service.name"] = 'otlp-receiver'
  AND resource["service.version"] = '1.0.0'
  AND resource["k8s.namespace.name"] = 'production'
  AND "http.status_code" >= 500
*/
```

---

## 💡 Span属性

### 3.1 Span生命周期

#### 定义

**形式化定义**: Span Lifecycle = (Create, Start, AddAttributes, AddEvents, End)

**状态流转**:

```text
创建 → 启动 → 活动中 → 结束
           ↓
    添加属性/事件
```

**通俗解释**: Span从创建到结束的完整生命周期管理。

#### 内涵（本质特征）

- **时间范围**: 有明确开始和结束
- **可修改**: 活动期间可添加属性
- **不可变**: 结束后不可修改
- **传播**: Context自动传播

#### 外延（涵盖范围）

- 包含: 创建、属性、事件、状态、结束
- 不包含: Span之后的处理（导出）

#### 属性

| 阶段 | 操作 | 时机 | 注意事项 |
|------|------|------|----------|
| Create | SpanBuilder | 方法入口 | 设置name和kind |
| Start | start() | 开始执行 | 记录开始时间 |
| Active | set_attribute() | 执行过程 | 动态添加 |
| Active | add_event() | 关键点 | 记录事件 |
| End | end() | 方法退出 | 自动或手动 |

#### 关系

- 与**Context**的关系: Span附加到Context
- 与**Tracer**的关系: Tracer创建Span
- 与**Exporter**的关系: 结束后导出

#### 示例

```rust
use opentelemetry::trace::{Span, Tracer, TracerProvider, Status};

// 1. 完整的Span生命周期
async fn process_order(order_id: i64) -> Result<()> {
    let tracer = global::tracer("order-service");

    // 创建Span
    let mut span = tracer
        .span_builder("process_order")
        .with_kind(SpanKind::Internal)
        .with_attributes(vec![
            KeyValue::new("order.id", order_id),
        ])
        .start(&tracer);  // 启动（记录开始时间）

    // 添加属性
    span.set_attribute(KeyValue::new("order.priority", "high"));

    // 记录事件
    span.add_event("validation_started", vec![]);

    // 业务逻辑
    validate_order(order_id).await?;

    span.add_event("validation_completed", vec![
        KeyValue::new("validation.result", "success"),
    ]);

    // 处理订单
    span.add_event("processing_started", vec![]);
    let result = execute_order(order_id).await;

    // 根据结果设置状态
    match result {
        Ok(_) => {
            span.set_status(Status::Ok);
            span.add_event("processing_completed", vec![
                KeyValue::new("success", true),
            ]);
        }
        Err(e) => {
            span.set_status(Status::error(e.to_string()));
            span.record_error(&e);
            span.add_event("processing_failed", vec![
                KeyValue::new("error", e.to_string()),
            ]);
        }
    }

    // Span自动在drop时结束
    result
}

// 2. 使用#[instrument]宏（简化）
use tracing::{instrument, info, error};

#[instrument(
    fields(
        order.id = order_id,
        order.status = tracing::field::Empty,
    )
)]
async fn process_order_simple(order_id: i64) -> Result<()> {
    let span = Span::current();

    info!("Validation started");
    validate_order(order_id).await?;

    info!("Processing started");
    let result = execute_order(order_id).await?;

    span.record("order.status", "completed");
    Ok(result)
}

// 3. 嵌套Span
#[instrument]
async fn validate_order(order_id: i64) -> Result<()> {
    // 自动成为子Span
    check_inventory().await?;
    check_payment().await?;
    Ok(())
}

#[instrument]
async fn check_inventory() -> Result<()> {
    // 又一个子Span
    info!("Checking inventory");
    tokio::time::sleep(Duration::from_millis(10)).await;
    Ok(())
}

// 生成的Trace树:
/*
process_order (100ms)
├─ event: validation_started (t=0ms)
├─ validate_order (30ms)
│  ├─ check_inventory (10ms)
│  └─ check_payment (20ms)
├─ event: validation_completed (t=30ms)
├─ event: processing_started (t=35ms)
├─ execute_order (60ms)
└─ event: processing_completed (t=95ms)
*/
```

---

## ⚙️ 指标命名

### 4.1 指标命名约定

#### 定义

**形式化定义**: Metric Name = instrument_type.unit.description

**命名规则**:

```text
<what>.<unit>

示例:
- http.server.duration (持续时间)
- http.server.request.size (请求大小)
- db.client.connections.usage (连接使用)
```

**通俗解释**: 统一的指标命名，便于理解和查询。

#### 内涵（本质特征）

- **描述性**: 名称清晰表达含义
- **单位明确**: 包含或暗示单位
- **分层次**: 使用点号分隔
- **一致性**: 遵循约定

#### 外延（涵盖范围）

- 包含: Counter、Histogram、Gauge
- 不包含: 业务特定指标（需自定义）

#### 属性

| 指标类型 | 命名模式 | 示例 | 单位 |
|---------|---------|------|------|
| Duration | `*.duration` | http.server.duration | ms |
| Size | `*.size` | http.request.body.size | bytes |
| Count | `*.count` | http.server.requests | 1 |
| Usage | `*.usage` | system.memory.usage | bytes |
| Utilization | `*.utilization` | system.cpu.utilization | 1 (%) |

#### 关系

- 与**可视化**的关系: 标准命名便于图表生成
- 与**告警**的关系: 标准命名便于规则编写
- 与**聚合**的关系: 统一命名便于聚合

#### 示例

```rust
use opentelemetry::metrics::{Counter, Histogram, Meter};

// 1. 创建标准指标
pub struct HttpMetrics {
    // 请求计数
    requests_total: Counter<u64>,

    // 请求持续时间
    request_duration: Histogram<f64>,

    // 请求大小
    request_size: Histogram<u64>,

    // 响应大小
    response_size: Histogram<u64>,
}

impl HttpMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            // 标准命名: http.server.requests
            requests_total: meter
                .u64_counter("http.server.requests")
                .with_description("Total HTTP requests")
                .with_unit("1")
                .init(),

            // 标准命名: http.server.duration
            request_duration: meter
                .f64_histogram("http.server.duration")
                .with_description("HTTP request duration")
                .with_unit("ms")
                .init(),

            // 标准命名: http.server.request.size
            request_size: meter
                .u64_histogram("http.server.request.size")
                .with_description("HTTP request body size")
                .with_unit("bytes")
                .init(),

            // 标准命名: http.server.response.size
            response_size: meter
                .u64_histogram("http.server.response.size")
                .with_description("HTTP response body size")
                .with_unit("bytes")
                .init(),
        }
    }

    pub fn record_request(
        &self,
        method: &str,
        route: &str,
        status: u16,
        duration: Duration,
        request_size: u64,
        response_size: u64,
    ) {
        let labels = &[
            KeyValue::new("http.method", method.to_string()),
            KeyValue::new("http.route", route.to_string()),
            KeyValue::new("http.status_code", status),
        ];

        self.requests_total.add(1, labels);
        self.request_duration.record(duration.as_millis() as f64, labels);
        self.request_size.record(request_size, labels);
        self.response_size.record(response_size, labels);
    }
}

// 2. 数据库指标
pub struct DatabaseMetrics {
    // db.client.connections.usage
    connections_usage: Histogram<u64>,

    // db.client.operation.duration
    operation_duration: Histogram<f64>,

    // db.client.operations
    operations_total: Counter<u64>,
}

// 3. 系统指标
pub struct SystemMetrics {
    // system.cpu.utilization
    cpu_utilization: Histogram<f64>,

    // system.memory.usage
    memory_usage: Histogram<u64>,

    // system.network.io
    network_io: Counter<u64>,
}

// 4. Prometheus查询示例
/*
# 请求速率
rate(http_server_requests_total[5m])

# P99延迟
histogram_quantile(0.99, http_server_duration_bucket)

# 按状态码分组的请求数
sum by (http_status_code) (http_server_requests_total)

# 平均请求大小
avg(http_server_request_size)

# CPU使用率
avg(system_cpu_utilization) by (host_name)
*/
```

---

## 🔗 相关资源

- [知识图谱](./KNOWLEDGE_GRAPH.md)
- [对比矩阵](./COMPARISON_MATRIX.md)
- [API参考README](./README.md)
- [语义约定完整列表](https://opentelemetry.io/docs/specs/semconv/)

---

**版本**: 2.0
**创建日期**: 2025-10-28
**最后更新**: 2025-10-28
**维护团队**: OTLP_rust参考团队

---

> **💡 提示**: 遵循OpenTelemetry语义约定是实现互操作性的关键，建议优先使用标准属性，自定义属性使用清晰的命名空间。
