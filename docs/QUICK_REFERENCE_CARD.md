# OTLP Rust 快速参考卡片

**版本**: 0.6.0
**Rust**: 1.94+
**OTLP**: 1.10

---

## 🚀 5分钟快速开始

### 安装依赖

```toml
[dependencies]
otlp = { version = "0.6.0", features = ["async", "grpc", "http"] }
tokio = { version = "1", features = ["full"] }
```

### 基础用法

```rust
use otlp::{OtlpClientBuilder, TraceBuilder, MetricBuilder};
use otlp::data::MetricType;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 创建客户端
    let client = OtlpClientBuilder::new()
        .endpoint("http://localhost:4317")
        .service("my-service", "1.0.0")
        .build()
        .await?;

    // 2. 发送追踪
    TraceBuilder::new("process_order", client.config())
        .with_attribute("order.id", "12345")
        .finish()
        .await?;

    // 3. 发送指标
    MetricBuilder::new("request_count", 1.0, client.config())
        .with_label("method", "GET")
        .send()
        .await?;

    Ok(())
}
```

---

## 📋 常用 API

### 配置

```rust
use otlp::config::{OtlpConfig, TransportProtocol, BatchConfig};
use std::time::Duration;

let config = OtlpConfig::new()
    .with_endpoint("http://localhost:4317")
    .with_protocol(TransportProtocol::Grpc)
    .with_timeout(Duration::from_secs(10))
    .with_batch_config(BatchConfig::new()
        .with_max_queue_size(2048)
        .with_scheduled_delay(Duration::from_millis(5000)));
```

### 追踪

```rust
use otlp::client::TraceBuilder;
use otlp::data::StatusCode;

TraceBuilder::new("operation_name", config)
    .with_attribute("key", "value")
    .with_numeric_attribute("count", 42.0)
    .with_status(StatusCode::Ok, None)
    .with_duration(100)
    .finish()
    .await?;
```

### 指标

```rust
use otlp::client::MetricBuilder;
use otlp::data::MetricType;

MetricBuilder::new("metric_name", 1.0, config)
    .with_label("dimension", "value")
    .with_description("Description")
    .with_unit("count")
    .send()
    .await?;
```

### 日志

```rust
use otlp::client::LogBuilder;
use otlp::data::LogSeverity;

LogBuilder::new("Log message", config)
    .with_severity(LogSeverity::Info)
    .with_attribute("request.id", "123")
    .send()
    .await?;
```

---

## 🏷️ 语义约定速查

### 资源属性

```rust
// 必须设置
"service.name"              // 服务名称
"service.version"           // 服务版本
"deployment.environment"    // 环境: production/staging/development

// 推荐设置
"service.namespace"         // 命名空间
"host.name"                 // 主机名
```

### HTTP 属性

```rust
"http.request.method"       // GET/POST/PUT/DELETE
"http.response.status_code" // 200/404/500
"url.path"                  // /api/users
"http.route"                // /api/users/{id}
```

### 数据库属性

```rust
"db.system"                 // postgresql/mysql/redis
"db.operation.name"         // SELECT/INSERT/UPDATE
"db.sql.table"              // users/orders
```

---

## ⚙️ 采样配置

```rust
use otlp::config::SamplerType;

// 开发环境 - 全采样
config.with_sampler(SamplerType::AlwaysOn);

// 生产环境 - 10% 采样
config.with_sampler(SamplerType::Probabilistic)
     .with_sampling_ratio(0.1);

// 高流量 - 限流采样
config.with_sampler(SamplerType::RateLimiting)
     .with_rate_limit(1000);

// 分布式 - 基于父级
config.with_sampler(SamplerType::ParentBased)
     .with_sampling_ratio(0.1);
```

---

## 🔒 安全检查清单

- [ ] `service.name` 已设置
- [ ] `deployment.environment` 已设置
- [ ] 无敏感数据（密码、令牌）
- [ ] 采样策略合适
- [ ] TLS 已启用（生产）

---

## 🐛 故障排除

### 无法连接

```rust
// 检查端点
println!("Endpoint: {}", config.endpoint);

// 检查协议
println!("Protocol: {:?}", config.protocol);
```

### 数据未显示

```rust
// 检查采样
println!("Sampler: {:?}", config.sampler);

// 强制采样
config.with_sampler(SamplerType::AlwaysOn);
```

### 性能问题

```rust
// 增加批处理大小
config.with_batch_config(BatchConfig::new()
    .with_max_export_batch_size(512));
```

---

## 📚 参考链接

| 文档 | 链接 |
|------|------|
| 最佳实践 | [BEST_PRACTICES.md](BEST_PRACTICES.md) |
| 语义约定 | [SEMANTIC_CONVENTIONS.md](SEMANTIC_CONVENTIONS.md) |
| 完整 API | [API_REFERENCE_COMPLETE.md](API_REFERENCE_COMPLETE.md) |
| 架构总览 | [ARCHITECTURE_OVERVIEW.md](ARCHITECTURE_OVERVIEW.md) |

---

## 💡 常用命令

```bash
# 编译检查
cargo check --features async,grpc,http

# 运行测试
cargo test --features async,grpc,http

# 构建发布
cargo build --release --features async,grpc,http

# 文档生成
cargo doc --features async,grpc,http --open
```

---

**打印此卡片，随时参考！**

**维护**: OTLP Rust Team
**更新**: 2026-03-15
