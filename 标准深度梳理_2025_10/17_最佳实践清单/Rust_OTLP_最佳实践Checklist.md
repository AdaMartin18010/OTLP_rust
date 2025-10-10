# Rust OTLP 最佳实践 Checklist

> **生产环境必备**: 完整的检查清单与实施指南  
> **适用场景**: 从开发到生产的全生命周期  
> **最后更新**: 2025年10月10日

---

## 📚 目录

- [Rust OTLP 最佳实践 Checklist](#rust-otlp-最佳实践-checklist)
  - [📚 目录](#-目录)
  - [🎯 检查清单概览](#-检查清单概览)
  - [📦 1. 项目初始化 Checklist](#-1-项目初始化-checklist)
    - [1.1 依赖管理](#11-依赖管理)
      - [✅ 必须包含的依赖](#-必须包含的依赖)
      - [✅ 版本管理](#-版本管理)
    - [1.2 项目结构](#12-项目结构)
      - [✅ 推荐的目录结构](#-推荐的目录结构)
  - [🔧 2. 配置最佳实践 Checklist](#-2-配置最佳实践-checklist)
    - [2.1 资源 (Resource) 配置](#21-资源-resource-配置)
      - [✅ 必需的 Resource 属性](#-必需的-resource-属性)
    - [2.2 导出器 (Exporter) 配置](#22-导出器-exporter-配置)
      - [✅ OTLP Exporter 配置](#-otlp-exporter-配置)
    - [2.3 采样 (Sampling) 配置](#23-采样-sampling-配置)
      - [✅ 采样策略](#-采样策略)
  - [📊 3. 追踪 (Tracing) 最佳实践 Checklist](#-3-追踪-tracing-最佳实践-checklist)
    - [3.1 Span 管理](#31-span-管理)
      - [✅ Span 创建](#-span-创建)
    - [3.2 属性设置](#32-属性设置)
      - [✅ 语义约定 (Semantic Conventions)](#-语义约定-semantic-conventions)
    - [3.3 错误处理](#33-错误处理)
      - [✅ 异常记录](#-异常记录)
  - [📈 4. Metrics 最佳实践 Checklist](#-4-metrics-最佳实践-checklist)
    - [4.1 Instrument 选择](#41-instrument-选择)
      - [✅ Instrument 类型选择](#-instrument-类型选择)
    - [4.2 标签管理](#42-标签管理)
      - [✅ 标签 (Labels) 最佳实践](#-标签-labels-最佳实践)
  - [🚀 5. 性能优化 Checklist](#-5-性能优化-checklist)
    - [5.1 批量导出](#51-批量导出)
      - [✅ 批量导出配置](#-批量导出配置)
    - [5.2 异步处理](#52-异步处理)
      - [✅ 异步最佳实践](#-异步最佳实践)
    - [5.3 内存优化](#53-内存优化)
      - [✅ 内存管理](#-内存管理)
  - [🔒 6. 安全性 Checklist](#-6-安全性-checklist)
    - [6.1 敏感数据保护](#61-敏感数据保护)
      - [✅ 数据脱敏](#-数据脱敏)
    - [6.2 TLS/SSL 配置](#62-tlsssl-配置)
      - [✅ 加密传输](#-加密传输)
  - [🧪 7. 测试 Checklist](#-7-测试-checklist)
    - [7.1 单元测试](#71-单元测试)
      - [✅ 测试示例](#-测试示例)
    - [7.2 集成测试](#72-集成测试)
      - [✅ 集成测试](#-集成测试)
  - [📦 8. 生产部署 Checklist](#-8-生产部署-checklist)
    - [8.1 环境配置](#81-环境配置)
      - [✅ 环境变量](#-环境变量)
    - [8.2 监控设置](#82-监控设置)
      - [✅ 关键指标监控](#-关键指标监控)
    - [8.3 告警配置](#83-告警配置)
      - [✅ 告警规则](#-告警规则)
  - [🔍 9. 可观测性成熟度评估](#-9-可观测性成熟度评估)
    - [Level 1: 基础 (Basic)](#level-1-基础-basic)
    - [Level 2: 中级 (Intermediate)](#level-2-中级-intermediate)
    - [Level 3: 高级 (Advanced)](#level-3-高级-advanced)
    - [Level 4: 专家 (Expert)](#level-4-专家-expert)
  - [📋 10. 快速检查清单](#-10-快速检查清单)
    - [🔴 生产部署前必查 (P0)](#-生产部署前必查-p0)
    - [🟡 优化项 (P1)](#-优化项-p1)

---

## 🎯 检查清单概览

本文档提供从开发到生产的完整检查清单：

| 阶段 | 检查项 | 优先级 |
|------|---------|--------|
| 🛠️ **项目初始化** | 依赖、结构 | 🔴 P0 |
| 🔧 **配置** | Resource、Exporter、Sampling | 🔴 P0 |
| 📊 **追踪** | Span、属性、错误 | 🔴 P0 |
| 📈 **Metrics** | Instrument、标签 | 🟡 P1 |
| 🚀 **性能** | 批量、异步、内存 | 🟡 P1 |
| 🔒 **安全** | 数据保护、TLS | 🔴 P0 |
| 🧪 **测试** | 单元、集成 | 🟡 P1 |
| 📦 **部署** | 环境、监控、告警 | 🔴 P0 |

---

## 📦 1. 项目初始化 Checklist

### 1.1 依赖管理

#### ✅ 必须包含的依赖

```toml
[dependencies]
# 核心库
- [ ] opentelemetry = { version = "0.22", features = ["trace", "metrics"] }
- [ ] opentelemetry_sdk = { version = "0.22", features = ["rt-tokio"] }

# OTLP 导出器
- [ ] opentelemetry-otlp = { version = "0.15", features = ["tonic"] }

# 异步运行时
- [ ] tokio = { version = "1", features = ["full"] }

# 日志集成 (推荐)
- [ ] tracing = "0.1"
- [ ] tracing-subscriber = "0.3"
- [ ] tracing-opentelemetry = "0.23"
```

#### ✅ 版本管理

```toml
- [ ] 使用兼容的版本组合
- [ ] 定期更新到最新稳定版
- [ ] 使用 Cargo.lock 锁定生产版本
```

**示例 `Cargo.toml`**:

```toml
[package]
name = "my-service"
version = "1.0.0"
edition = "2021"

[dependencies]
opentelemetry = { version = "0.22", features = ["trace", "metrics"] }
opentelemetry_sdk = { version = "0.22", features = ["rt-tokio", "trace", "metrics"] }
opentelemetry-otlp = { version = "0.15", features = ["tonic", "metrics"] }
tokio = { version = "1", features = ["full"] }
anyhow = "1.0"

# 日志
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.23"

[dev-dependencies]
tokio-test = "0.4"
```

### 1.2 项目结构

#### ✅ 推荐的目录结构

```text
my-service/
├── src/
│   ├── main.rs              # 入口文件
│   ├── telemetry/
│   │   ├── mod.rs           # ✅ Telemetry 模块
│   │   ├── tracer.rs        # ✅ Tracer 初始化
│   │   ├── metrics.rs       # ✅ Metrics 初始化
│   │   └── config.rs        # ✅ 配置管理
│   ├── handlers/            # 业务逻辑
│   └── models/              # 数据模型
├── Cargo.toml
├── .env                     # ✅ 环境变量
└── config/
    ├── dev.yaml             # ✅ 开发环境配置
    ├── staging.yaml         # ✅ 测试环境配置
    └── prod.yaml            # ✅ 生产环境配置
```

**Checklist**:

```text
- [ ] 独立的 telemetry 模块
- [ ] 分离的配置文件
- [ ] 环境变量管理
- [ ] 清晰的代码组织
```

---

## 🔧 2. 配置最佳实践 Checklist

### 2.1 资源 (Resource) 配置

#### ✅ 必需的 Resource 属性

```rust
use opentelemetry::{KeyValue, Resource};

fn create_resource() -> Resource {
    Resource::new(vec![
        // ✅ 必需: 服务标识
        KeyValue::new("service.name", env::var("SERVICE_NAME")
            .unwrap_or_else(|_| "my-service".to_string())),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        KeyValue::new("service.namespace", "production"),
        
        // ✅ 必需: 部署信息
        KeyValue::new("deployment.environment", 
            env::var("ENVIRONMENT").unwrap_or_else(|_| "dev".to_string())),
        
        // ✅ 推荐: 主机信息
        KeyValue::new("host.name", hostname::get()
            .unwrap_or_default()
            .to_string_lossy()
            .to_string()),
        
        // ✅ 推荐: 云环境
        KeyValue::new("cloud.provider", "aws"),  // 如适用
        KeyValue::new("cloud.region", "us-east-1"),
        
        // ✅ 推荐: 容器/K8s
        KeyValue::new("container.id", env::var("HOSTNAME").unwrap_or_default()),
        KeyValue::new("k8s.namespace.name", env::var("K8S_NAMESPACE").unwrap_or_default()),
        KeyValue::new("k8s.pod.name", env::var("K8S_POD_NAME").unwrap_or_default()),
    ])
}
```

**Checklist**:

```text
- [ ] service.name (必需)
- [ ] service.version (必需)
- [ ] deployment.environment (必需)
- [ ] 云/容器信息 (如适用)
- [ ] 从环境变量读取
```

### 2.2 导出器 (Exporter) 配置

#### ✅ OTLP Exporter 配置

```rust
use opentelemetry_otlp::WithExportConfig;
use std::time::Duration;

fn create_otlp_exporter() -> Result<SpanExporter> {
    let otlp_endpoint = env::var("OTLP_ENDPOINT")
        .unwrap_or_else(|_| "http://localhost:4317".to_string());
    
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint(otlp_endpoint)
        .with_timeout(Duration::from_secs(3))  // ✅ 设置超时
        .with_metadata({                       // ✅ 添加认证头
            let mut map = tonic::metadata::MetadataMap::new();
            if let Ok(token) = env::var("OTLP_AUTH_TOKEN") {
                map.insert("authorization", token.parse().unwrap());
            }
            map
        })
        .build_span_exporter()?;
    
    Ok(exporter)
}
```

**Checklist**:

```text
- [ ] Endpoint 可配置
- [ ] 超时设置
- [ ] 认证配置
- [ ] TLS 配置 (生产环境)
- [ ] 重试策略
- [ ] 批量大小配置
```

### 2.3 采样 (Sampling) 配置

#### ✅ 采样策略

```rust
use opentelemetry_sdk::trace::{Sampler, Config};

fn create_sampler() -> Sampler {
    let sample_rate = env::var("TRACE_SAMPLE_RATE")
        .ok()
        .and_then(|s| s.parse::<f64>().ok())
        .unwrap_or(1.0);  // 默认 100%
    
    if sample_rate >= 1.0 {
        Sampler::AlwaysOn       // ✅ 开发: 全部采样
    } else if sample_rate <= 0.0 {
        Sampler::AlwaysOff      // ✅ 关闭采样
    } else {
        Sampler::TraceIdRatioBased(sample_rate)  // ✅ 生产: 部分采样
    }
}

fn create_tracer_provider() -> TracerProvider {
    TracerProvider::builder()
        .with_config(
            Config::default()
                .with_sampler(create_sampler())  // ✅ 应用采样器
                .with_resource(create_resource())
        )
        .with_batch_exporter(create_otlp_exporter()?, opentelemetry_sdk::runtime::Tokio)
        .build()
}
```

**Checklist**:

```text
- [ ] 开发环境: AlwaysOn (100%)
- [ ] 生产环境: TraceIdRatioBased (10-50%)
- [ ] 可配置采样率
- [ ] 考虑成本与可见性平衡
```

**推荐采样率**:

| 环境 | 采样率 | 说明 |
|------|--------|------|
| 开发 | 100% | 全部追踪 |
| 测试 | 50% | 平衡测试 |
| 生产 (低流量) | 50-100% | 高可见性 |
| 生产 (高流量) | 10-20% | 降低成本 |

---

## 📊 3. 追踪 (Tracing) 最佳实践 Checklist

### 3.1 Span 管理

#### ✅ Span 创建

```rust
use opentelemetry::trace::{Span, Tracer, SpanKind, Status};

// ✅ 好的做法
async fn handle_request() -> Result<()> {
    let tracer = global::tracer("my-service");
    
    // ✅ 使用有意义的名称
    let mut span = tracer
        .span_builder("handle_user_request")  // ✅ 描述性名称
        .with_kind(SpanKind::Server)          // ✅ 设置 SpanKind
        .start(&tracer);
    
    // ✅ 设置属性
    span.set_attribute(KeyValue::new("http.method", "POST"));
    span.set_attribute(KeyValue::new("http.route", "/api/users"));
    
    // 执行业务逻辑
    match process_user().await {
        Ok(result) => {
            span.set_status(Status::Ok);  // ✅ 设置成功状态
            Ok(result)
        }
        Err(e) => {
            span.record_exception(&e);    // ✅ 记录异常
            span.set_status(Status::error(e.to_string()));  // ✅ 设置错误状态
            Err(e)
        }
    }
}  // ✅ Span 自动结束

// ❌ 不好的做法
async fn bad_handle_request() -> Result<()> {
    let mut span = tracer
        .span_builder("op")            // ❌ 名称不清晰
        .start(&tracer);
    
    // ❌ 没有设置 SpanKind
    // ❌ 没有设置属性
    // ❌ 没有错误处理
    
    process_user().await?;
    
    // ❌ 忘记设置状态
    Ok(())
}
```

**Checklist**:

```text
- [ ] 使用描述性 Span 名称
- [ ] 设置 SpanKind (Server/Client/Producer/Consumer/Internal)
- [ ] 添加上下文属性
- [ ] 记录异常 (record_exception)
- [ ] 设置 Span 状态 (Ok/Error)
- [ ] Span 自动结束 (作用域管理)
```

### 3.2 属性设置

#### ✅ 语义约定 (Semantic Conventions)

```rust
// ✅ HTTP 属性
span.set_attribute(KeyValue::new("http.method", "GET"));
span.set_attribute(KeyValue::new("http.url", "https://api.example.com/users"));
span.set_attribute(KeyValue::new("http.status_code", 200));
span.set_attribute(KeyValue::new("http.user_agent", user_agent));

// ✅ 数据库属性
span.set_attribute(KeyValue::new("db.system", "postgresql"));
span.set_attribute(KeyValue::new("db.name", "users_db"));
span.set_attribute(KeyValue::new("db.statement", "SELECT * FROM users WHERE id = $1"));
span.set_attribute(KeyValue::new("db.operation", "SELECT"));

// ✅ 消息队列属性
span.set_attribute(KeyValue::new("messaging.system", "kafka"));
span.set_attribute(KeyValue::new("messaging.destination", "user-events"));
span.set_attribute(KeyValue::new("messaging.operation", "publish"));

// ✅ 业务属性
span.set_attribute(KeyValue::new("user.id", user_id));
span.set_attribute(KeyValue::new("order.id", order_id));
span.set_attribute(KeyValue::new("transaction.amount", amount));
```

**Checklist**:

```text
- [ ] 遵循 OpenTelemetry 语义约定
- [ ] 添加业务上下文属性
- [ ] 属性值类型正确
- [ ] 不记录敏感信息 (PII)
```

### 3.3 错误处理

#### ✅ 异常记录

```rust
use opentelemetry::trace::Status;

async fn process_with_error_handling() -> Result<()> {
    let tracer = global::tracer("my-service");
    let mut span = tracer.span_builder("process").start(&tracer);
    
    match risky_operation().await {
        Ok(result) => {
            span.set_status(Status::Ok);  // ✅ 成功
            Ok(result)
        }
        Err(e) => {
            // ✅ 记录异常详情
            span.record_exception(&e);
            
            // ✅ 设置错误状态
            span.set_status(Status::error(format!("Operation failed: {}", e)));
            
            // ✅ 添加错误上下文
            span.set_attribute(KeyValue::new("error.type", e.type_name()));
            span.set_attribute(KeyValue::new("error.phase", "processing"));
            
            Err(e)
        }
    }
}
```

**Checklist**:

```text
- [ ] 使用 record_exception 记录异常
- [ ] 设置 Span 状态为 Error
- [ ] 添加错误类型和消息
- [ ] 包含错误堆栈 (如需要)
- [ ] 不泄露敏感信息
```

---

## 📈 4. Metrics 最佳实践 Checklist

### 4.1 Instrument 选择

#### ✅ Instrument 类型选择

```rust
use opentelemetry::metrics::{Counter, Histogram, Gauge, Meter};

fn setup_metrics(meter: &Meter) {
    // ✅ Counter: 只增计数
    let request_counter = meter
        .u64_counter("http.server.requests")
        .with_description("Total HTTP requests")
        .with_unit("1")
        .init();
    
    // ✅ Histogram: 分布统计
    let latency_histogram = meter
        .f64_histogram("http.server.duration")
        .with_description("HTTP request duration")
        .with_unit("s")
        .init();
    
    // ✅ Gauge: 瞬时值
    let active_connections = meter
        .i64_gauge("http.server.active_connections")
        .with_description("Active HTTP connections")
        .init();
    
    // ✅ UpDownCounter: 可增可减计数
    let queue_size = meter
        .i64_up_down_counter("queue.size")
        .with_description("Message queue size")
        .init();
}
```

**Checklist**:

```text
- [ ] Counter: 累计计数 (requests, errors, bytes)
- [ ] Histogram: 分布测量 (latency, size)
- [ ] Gauge: 当前值 (connections, memory, CPU)
- [ ] UpDownCounter: 可增可减 (queue size, active sessions)
- [ ] 命名遵循语义约定
- [ ] 添加描述和单位
```

### 4.2 标签管理

#### ✅ 标签 (Labels) 最佳实践

```rust
// ✅ 好的做法: 低基数标签
let labels = [
    KeyValue::new("http.method", "GET"),     // ✅ 有限值
    KeyValue::new("http.status_code", "200"), // ✅ 有限值
    KeyValue::new("service.name", "api"),    // ✅ 有限值
];
request_counter.add(1, &labels);

// ❌ 坏的做法: 高基数标签
let bad_labels = [
    KeyValue::new("user.id", "12345"),       // ❌ 高基数!
    KeyValue::new("request.id", "uuid"),     // ❌ 高基数!
    KeyValue::new("timestamp", "2025..."),   // ❌ 高基数!
];
```

**Checklist**:

```text
- [ ] 标签基数 < 10 (低基数)
- [ ] 不使用用户 ID、请求 ID 作为标签
- [ ] 标签值有限且已知
- [ ] 标签名称符合命名约定
```

**标签基数指南**:

| 标签 | 基数 | 推荐 |
|------|------|------|
| http.method | ~10 | ✅ 低 |
| http.status_code | ~60 | ✅ 低 |
| region | ~20 | ✅ 低 |
| user.id | 百万+ | ❌ 高 |
| request.id | 无限 | ❌ 高 |

---

## 🚀 5. 性能优化 Checklist

### 5.1 批量导出

#### ✅ 批量导出配置

```rust
use opentelemetry_sdk::trace::{BatchConfig, BatchSpanProcessor};
use std::time::Duration;

fn create_batch_processor(exporter: SpanExporter) -> BatchSpanProcessor {
    BatchSpanProcessor::builder(exporter, opentelemetry_sdk::runtime::Tokio)
        .with_batch_config(
            BatchConfig::default()
                .with_max_queue_size(2048)              // ✅ 队列大小
                .with_scheduled_delay(Duration::from_secs(5))  // ✅ 导出间隔
                .with_max_export_batch_size(512)        // ✅ 批量大小
                .with_max_concurrent_exports(1)         // ✅ 并发导出
        )
        .build()
}
```

**Checklist**:

```text
- [ ] 使用 BatchSpanProcessor (而非 SimpleSpanProcessor)
- [ ] 设置合理的队列大小
- [ ] 配置导出间隔
- [ ] 设置批量大小
- [ ] 限制并发导出
```

**推荐配置**:

| 环境 | 队列大小 | 导出间隔 | 批量大小 |
|------|---------|---------|---------|
| 开发 | 512 | 1s | 128 |
| 生产 (低流量) | 2048 | 5s | 512 |
| 生产 (高流量) | 4096 | 10s | 1024 |

### 5.2 异步处理

#### ✅ 异步最佳实践

```rust
// ✅ 好的做法: 非阻塞操作
async fn handle_request() -> Result<()> {
    let span = tracer.span_builder("handle_request").start(&tracer);
    
    // ✅ 异步操作不阻塞
    let result = async_operation().await?;
    
    // ✅ Span 在 await 点保持活跃
    span.set_status(Status::Ok);
    
    Ok(result)
}

// ❌ 坏的做法: 阻塞操作
fn bad_handle_request() -> Result<()> {
    let span = tracer.span_builder("handle_request").start(&tracer);
    
    // ❌ 同步阻塞操作
    std::thread::sleep(Duration::from_secs(1));
    
    Ok(())
}
```

**Checklist**:

```text
- [ ] 使用异步操作 (async/await)
- [ ] 避免阻塞调用
- [ ] 使用 Tokio 运行时
- [ ] Span 正确跨 await 点
```

### 5.3 内存优化

#### ✅ 内存管理

```rust
// ✅ 限制 Span 属性数量
const MAX_ATTRIBUTES: usize = 128;

// ✅ 限制字符串长度
fn truncate_attribute(value: &str) -> String {
    if value.len() > 1024 {
        format!("{}...", &value[..1024])
    } else {
        value.to_string()
    }
}

// ✅ 避免大对象作为属性
span.set_attribute(KeyValue::new("response.size", response.len()));  // ✅ 记录大小
// ❌ 不要这样做:
// span.set_attribute(KeyValue::new("response.body", response));  // ❌ 记录整个响应体
```

**Checklist**:

```text
- [ ] 限制 Span 属性数量 (< 128)
- [ ] 限制属性值长度 (< 1KB)
- [ ] 避免记录大对象
- [ ] 定期监控内存使用
```

---

## 🔒 6. 安全性 Checklist

### 6.1 敏感数据保护

#### ✅ 数据脱敏

```rust
// ✅ 脱敏工具
fn sanitize_sql(sql: &str) -> String {
    // 移除参数值
    sql.split_whitespace()
        .map(|word| if word.contains('\'') { "?" } else { word })
        .collect::<Vec<_>>()
        .join(" ")
}

fn mask_email(email: &str) -> String {
    if let Some(at_pos) = email.find('@') {
        let (name, domain) = email.split_at(at_pos);
        format!("{}***@{}", &name[..name.len().min(2)], domain.split_at(1).1)
    } else {
        "***".to_string()
    }
}

// ✅ 使用脱敏数据
span.set_attribute(KeyValue::new("db.statement", sanitize_sql(sql)));
span.set_attribute(KeyValue::new("user.email", mask_email(email)));
```

**Checklist**:

```text
- [ ] 不记录密码
- [ ] 不记录信用卡号
- [ ] 不记录 API 密钥/Token
- [ ] 脱敏邮箱地址
- [ ] 脱敏 SQL 语句
- [ ] 脱敏 URL 参数
```

**禁止记录的信息**:

```text
❌ 密码 (password, passwd, pwd)
❌ 密钥 (secret, api_key, token)
❌ 信用卡 (credit_card, ccn)
❌ SSN (social_security_number)
❌ 个人身份信息 (PII)
```

### 6.2 TLS/SSL 配置

#### ✅ 加密传输

```rust
use tonic::transport::ClientTlsConfig;

fn create_secure_exporter() -> Result<SpanExporter> {
    let tls_config = ClientTlsConfig::new()
        .domain_name("otlp.example.com")              // ✅ 域名验证
        .ca_certificate(Certificate::from_pem(ca))    // ✅ CA 证书
        .identity(Identity::from_pem(cert, key));     // ✅ 客户端证书
    
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("https://otlp.example.com:4317")  // ✅ HTTPS
        .with_tls_config(tls_config)                     // ✅ TLS 配置
        .build_span_exporter()?;
    
    Ok(exporter)
}
```

**Checklist**:

```text
- [ ] 生产环境使用 HTTPS/TLS
- [ ] 配置 CA 证书
- [ ] 启用域名验证
- [ ] 使用客户端证书 (如需要)
- [ ] 定期更新证书
```

---

## 🧪 7. 测试 Checklist

### 7.1 单元测试

#### ✅ 测试示例

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use opentelemetry::{global, testing::TestSpan};
    
    #[tokio::test]
    async fn test_span_creation() {
        // ✅ 初始化测试 tracer
        let tracer_provider = TracerProvider::builder()
            .with_simple_exporter(TestExporter::new())
            .build();
        global::set_tracer_provider(tracer_provider);
        
        // ✅ 测试 Span 创建
        let tracer = global::tracer("test");
        let span = tracer.span_builder("test_span").start(&tracer);
        
        assert_eq!(span.span_context().is_valid(), true);
    }
    
    #[tokio::test]
    async fn test_span_attributes() {
        let tracer = global::tracer("test");
        let mut span = tracer.span_builder("test").start(&tracer);
        
        // ✅ 测试属性设置
        span.set_attribute(KeyValue::new("test.key", "test.value"));
        
        // 验证属性
        // ...
    }
}
```

**Checklist**:

```text
- [ ] 测试 Span 创建
- [ ] 测试属性设置
- [ ] 测试错误处理
- [ ] 测试 Context 传播
- [ ] 测试采样逻辑
```

### 7.2 集成测试

#### ✅ 集成测试

```rust
#[tokio::test]
async fn integration_test_http_tracing() {
    // ✅ 启动测试服务器
    let app = create_app();
    let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let addr = listener.local_addr().unwrap();
    
    tokio::spawn(async move {
        axum::serve(listener, app).await.unwrap();
    });
    
    // ✅ 发送请求
    let response = reqwest::get(format!("http://{}/health", addr))
        .await
        .unwrap();
    
    // ✅ 验证响应
    assert_eq!(response.status(), 200);
    
    // ✅ 验证 Span 被创建 (需要 TestExporter)
}
```

**Checklist**:

```text
- [ ] HTTP 端到端测试
- [ ] 数据库集成测试
- [ ] 消息队列集成测试
- [ ] 分布式追踪测试
```

---

## 📦 8. 生产部署 Checklist

### 8.1 环境配置

#### ✅ 环境变量

```bash
# ✅ 必需的环境变量
export SERVICE_NAME=my-service
export SERVICE_VERSION=1.0.0
export ENVIRONMENT=production

# ✅ OTLP 配置
export OTLP_ENDPOINT=https://otlp.example.com:4317
export OTLP_AUTH_TOKEN=secret-token

# ✅ 采样配置
export TRACE_SAMPLE_RATE=0.1  # 10% 采样

# ✅ 资源配置
export K8S_NAMESPACE=production
export K8S_POD_NAME=$HOSTNAME

# ✅ 日志级别
export RUST_LOG=info,opentelemetry=debug
```

**Checklist**:

```text
- [ ] SERVICE_NAME 已设置
- [ ] OTLP_ENDPOINT 已配置
- [ ] 采样率已调整
- [ ] 认证已配置
- [ ] 日志级别合理
```

### 8.2 监控设置

#### ✅ 关键指标监控

```text
- [ ] Span 导出成功率 > 99%
- [ ] Span 导出延迟 < 100ms (p99)
- [ ] Metrics 导出成功率 > 99%
- [ ] 队列溢出次数 = 0
- [ ] 内存使用 < 阈值
- [ ] CPU 使用 < 阈值
```

### 8.3 告警配置

#### ✅ 告警规则

```yaml
# ✅ Span 导出失败告警
- alert: SpanExportFailure
  expr: rate(otlp_exporter_failed_total[5m]) > 0.01
  severity: warning
  
# ✅ 队列溢出告警
- alert: QueueOverflow
  expr: otlp_queue_dropped_total > 0
  severity: critical
  
# ✅ 导出延迟告警
- alert: HighExportLatency
  expr: histogram_quantile(0.99, otlp_export_duration_seconds) > 0.5
  severity: warning
```

**Checklist**:

```text
- [ ] 导出失败告警
- [ ] 队列溢出告警
- [ ] 高延迟告警
- [ ] 资源使用告警
```

---

## 🔍 9. 可观测性成熟度评估

### Level 1: 基础 (Basic)

```text
- [ ] 服务有基本的追踪
- [ ] 记录 HTTP 请求
- [ ] 有基本的 Metrics
- [ ] 数据导出到 Collector
```

### Level 2: 中级 (Intermediate)

```text
- [ ] 完整的分布式追踪
- [ ] Context 跨服务传播
- [ ] 数据库操作追踪
- [ ] 消息队列追踪
- [ ] 完整的 Metrics 覆盖
- [ ] 告警规则配置
```

### Level 3: 高级 (Advanced)

```text
- [ ] 自定义 Span 处理器
- [ ] 动态采样
- [ ] 完整的安全配置
- [ ] 性能优化完成
- [ ] 自动化测试覆盖
- [ ] 完整的文档
```

### Level 4: 专家 (Expert)

```text
- [ ] 自定义 Exporter
- [ ] 实时流处理
- [ ] ML 驱动的异常检测
- [ ] 自动化 SLO 监控
- [ ] 完整的可观测性平台
```

---

## 📋 10. 快速检查清单

### 🔴 生产部署前必查 (P0)

```text
开发阶段:
- [ ] ✅ 依赖版本兼容
- [ ] ✅ Resource 配置完整
- [ ] ✅ Exporter 可连接
- [ ] ✅ 采样率已设置

安全检查:
- [ ] 🔒 敏感数据已脱敏
- [ ] 🔒 TLS 已启用
- [ ] 🔒 认证已配置

性能检查:
- [ ] 🚀 使用批量导出
- [ ] 🚀 队列大小合理
- [ ] 🚀 内存使用可控

监控告警:
- [ ] 📊 关键指标已监控
- [ ] 📊 告警规则已配置
- [ ] 📊 仪表盘已创建
```

### 🟡 优化项 (P1)

```text
- [ ] 完整的单元测试
- [ ] 完整的集成测试
- [ ] 性能基准测试
- [ ] 压力测试
- [ ] 文档完整
```

---

**文档版本**: v1.0  
**最后更新**: 2025-10-10  
**作者**: OTLP Rust 标准深度梳理团队

**下一步**: 定期审查本清单，持续提升可观测性成熟度！
