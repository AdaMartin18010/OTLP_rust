# OpenTelemetry 语义约定指南

**版本**: 1.0
**OTLP 版本**: 1.10
**更新日期**: 2026-03-15

---

## 📋 概述

OpenTelemetry 语义约定定义了跨所有信号（追踪、指标、日志）的标准属性名称和值。遵循这些约定确保：

- **互操作性**: 不同实现之间的兼容性
- **一致性**: 统一的命名和分类
- **可查询性**: 标准化的查询和分析
- **工具支持**: 与可视化工具的集成

---

## 🏷️ 通用属性

### 服务标识

| 属性 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `service.name` | string | 服务唯一标识 | `checkout-service` |
| `service.version` | string | 服务版本 | `1.2.3` |
| `service.namespace` | string | 服务命名空间 | `ecommerce` |
| `service.instance.id` | string | 实例唯一ID | `checkout-01` |

### 部署环境

| 属性 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `deployment.environment` | string | 部署环境 | `production`, `staging`, `development` |
| `deployment.region` | string | 部署区域 | `us-east-1`, `eu-west-1` |
| `deployment.datacenter` | string | 数据中心 | `dc1`, `us-east-1a` |

### 主机信息

| 属性 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `host.name` | string | 主机名 | `web-server-01` |
| `host.id` | string | 主机唯一ID | `i-1234567890abcdef0` |
| `host.type` | string | 主机类型 | `t3.medium` |
| `host.arch` | string | 架构 | `x86_64`, `aarch64` |

---

## 🌐 HTTP 属性

### 请求属性

| 属性 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `http.request.method` | string | HTTP 方法 | `GET`, `POST`, `PUT` |
| `http.request.body.size` | int | 请求体大小 | `1024` |
| `http.request.header.content_type` | string | Content-Type | `application/json` |
| `http.request.header.user_agent` | string | User-Agent | `Mozilla/5.0...` |

### 响应属性

| 属性 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `http.response.status_code` | int | 状态码 | `200`, `404`, `500` |
| `http.response.body.size` | int | 响应体大小 | `2048` |
| `http.response.header.content_type` | string | Content-Type | `application/json` |

### URL 属性

| 属性 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `url.full` | string | 完整 URL | `https://example.com/api/users` |
| `url.scheme` | string | 协议 | `https`, `http` |
| `url.path` | string | 路径 | `/api/users` |
| `url.query` | string | 查询参数 | `page=1&limit=10` |

### 路由属性

| 属性 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `http.route` | string | 路由模板 | `/api/users/{id}` |
| `http.target` | string | 请求目标 | `/api/users/123` |

### Rust 实现

```rust
use otlp::data::{TelemetryData, AttributeValue};

fn create_http_span(method: &str, path: &str, status: u16) -> TelemetryData {
    TelemetryData::trace("http_request")
        .with_attribute("http.request.method", method)
        .with_attribute("url.path", path)
        .with_attribute("http.route", "/api/users/{id}")
        .with_numeric_attribute("http.response.status_code", status as f64)
        .with_attribute("url.scheme", "https")
}
```

---

## 🗄️ 数据库属性

### 通用属性

| 属性 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `db.system` | string | 数据库系统 | `postgresql`, `mysql`, `redis` |
| `db.name` | string | 数据库名称 | `myapp_production` |
| `db.user` | string | 用户名 | `readonly_user` |
| `db.operation.name` | string | 操作名称 | `SELECT`, `INSERT`, `UPDATE` |
| `db.statement` | string | SQL 语句 | `SELECT * FROM users` |

### 连接属性

| 属性 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `db.connection.string` | string | 连接字符串 | `postgresql://localhost:5432` |
| `db.connection.id` | string | 连接ID | `conn-12345` |

### Rust 实现

```rust
fn create_db_span(operation: &str, table: &str, duration_ms: u64) -> TelemetryData {
    TelemetryData::trace("database_operation")
        .with_attribute("db.system", "postgresql")
        .with_attribute("db.operation.name", operation)
        .with_attribute("db.sql.table", table)
        .with_attribute("db.name", "production_db")
}
```

---

## 📨 消息队列属性

### 通用属性

| 属性 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `messaging.system` | string | 消息系统 | `kafka`, `rabbitmq`, `sqs` |
| `messaging.destination` | string | 目标名称 | `orders_topic` |
| `messaging.destination.kind` | string | 类型 | `topic`, `queue` |
| `messaging.operation.type` | string | 操作类型 | `publish`, `receive`, `process` |

### Kafka 特定

| 属性 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `messaging.kafka.topic` | string | Topic 名称 | `orders` |
| `messaging.kafka.partition` | int | 分区 | `0`, `1`, `2` |
| `messaging.kafka.offset` | int | 偏移量 | `12345` |
| `messaging.kafka.consumer.group` | string | 消费者组 | `order-processors` |

---

## ☁️ 云属性

### 通用云属性

| 属性 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `cloud.provider` | string | 云提供商 | `aws`, `gcp`, `azure` |
| `cloud.region` | string | 区域 | `us-east-1` |
| `cloud.availability_zone` | string | 可用区 | `us-east-1a` |
| `cloud.account.id` | string | 账户ID | `123456789012` |

### AWS 特定

| 属性 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `aws.ec2.instance.id` | string | EC2 实例ID | `i-1234567890abcdef0` |
| `aws.ec2.instance.type` | string | 实例类型 | `t3.medium` |
| `aws.ec2.availability_zone` | string | 可用区 | `us-east-1a` |
| `aws.lambda.function.name` | string | Lambda 函数名 | `process-order` |
| `aws.lambda.function.arn` | string | Lambda ARN | `arn:aws:lambda:...` |

### Kubernetes 属性

| 属性 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `k8s.cluster.name` | string | 集群名 | `production-cluster` |
| `k8s.namespace.name` | string | 命名空间 | `default`, `production` |
| `k8s.pod.name` | string | Pod 名 | `web-server-12345` |
| `k8s.pod.uid` | string | Pod UID | `12345678-1234-1234-1234-123456789012` |
| `k8s.container.name` | string | 容器名 | `app`, `sidecar` |
| `k8s.node.name` | string | 节点名 | `node-01` |

---

## ⚠️ 错误属性

### 通用错误

| 属性 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `error.type` | string | 错误类型 | `java.net.UnknownHostException` |
| `error.message` | string | 错误消息 | `Connection refused` |
| `error.stack_trace` | string | 堆栈跟踪 | (stack trace) |

### HTTP 错误

| 属性 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `http.error.name` | string | HTTP 错误名 | `timeout`, `connection_refused` |

### Rust 实现

```rust
fn create_error_span(error: &dyn std::error::Error) -> TelemetryData {
    TelemetryData::trace("error_operation")
        .with_attribute("error.type", std::any::type_name_of_val(error))
        .with_attribute("error.message", error.to_string())
        .with_status(StatusCode::Error, Some(error.to_string()))
}
```

---

## 📊 指标特定属性

### 指标类型

| 属性 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `metric.name` | string | 指标名称 | `http_requests_total` |
| `metric.unit` | string | 单位 | `ms`, `bytes`, `count` |
| `metric.type` | string | 指标类型 | `counter`, `gauge`, `histogram` |

### 直方图桶

| 属性 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `histogram.bucket.bound` | double | 桶边界 | `0.005`, `0.01`, `0.025` |
| `histogram.bucket.count` | int | 桶计数 | `10`, `25`, `50` |

---

## 📝 日志特定属性

### 日志级别

| 属性 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `log.level` | string | 日志级别 | `INFO`, `WARN`, `ERROR` |
| `log.severity_number` | int | 严重级别数值 | `9`, `13`, `17` |
| `log.severity_text` | string | 严重级别文本 | `INFO`, `WARNING`, `ERROR` |

### 日志来源

| 属性 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `log.logger.name` | string | Logger 名称 | `com.example.MyClass` |
| `log.file.name` | string | 文件名 | `main.rs` |
| `log.file.path` | string | 文件路径 | `/app/src/main.rs` |
| `log.file.line` | int | 行号 | `42` |

### Rust 实现

```rust
use otlp::data::{TelemetryData, LogSeverity};

fn create_log(message: &str, level: LogSeverity) -> TelemetryData {
    TelemetryData::log(message, level)
        .with_attribute("log.logger.name", module_path!())
        .with_attribute("log.file.name", file!())
        .with_attribute("log.file.line", line!())
}
```

---

## 🏢 组织特定约定

### 命名空间建议

```rust
// 组织级属性
const ORG_PREFIX: &str = "mycompany";

// 应用级属性
fn with_org_attributes(data: TelemetryData) -> TelemetryData {
    data.with_attribute(format!("{}.team", ORG_PREFIX), "platform")
        .with_attribute(format!("{}.cost_center", ORG_PREFIX), "cc12345")
        .with_attribute(format!("{}.environment.tier", ORG_PREFIX), "critical")
}

// 业务级属性
fn with_business_attributes(data: TelemetryData, order_id: &str) -> TelemetryData {
    data.with_attribute("business.order.id", order_id)
        .with_attribute("business.customer.tier", "premium")
}
```

---

## ✅ 验证清单

在部署前检查以下约定：

- [ ] 所有属性使用小写字母和下划线
- [ ] 使用点号分隔命名空间（如 `http.request.method`）
- [ ] 遵循标准属性名称，不创建自定义变体
- [ ] 属性值使用正确的数据类型
- [ ] 敏感数据已脱敏或移除
- [ ] 资源属性在初始化时设置
- [ ] 事件属性在运行时动态添加

---

## 📚 参考资源

- [OpenTelemetry Semantic Conventions](https://opentelemetry.io/docs/concepts/semantic-conventions/)
- [Semantic Conventions Registry](https://opentelemetry.io/docs/specs/semconv/)
- [HTTP Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/http/)
- [Database Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/database/)

---

**文档维护**: OTLP Rust Team
**最后更新**: 2026-03-15
