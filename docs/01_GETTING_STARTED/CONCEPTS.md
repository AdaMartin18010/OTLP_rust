# 快速入门核心概念

**版本**: 2.0  
**日期**: 2025年10月28日  
**状态**: ✅ 完整  
**面向**: 新手开发者

---

## 📋 目录

1. [OTLP基础概念](#1-otlp基础概念)
2. [第一个追踪应用](#2-第一个追踪应用)
3. [基本配置](#3-基本配置)
4. [常见问题](#4-常见问题)

---

## 1. OTLP基础概念

### 1.1 什么是OTLP

#### 定义

**OpenTelemetry Protocol (OTLP)** 是一个开放标准的遥测数据传输协议。

**简单理解**:
```
应用程序 → 生成追踪数据 → OTLP传输 → 后端存储 → 可视化分析
```

**通俗解释**: 就像给你的程序装上"GPS定位器"，记录每个请求的完整路径。

#### 核心组件

```
┌─────────────────────────────────────────┐
│           应用程序                      │
│  ┌─────────┐  ┌─────────┐  ┌─────────┐ │
│  │  Span   │→ │Processor│→ │Exporter │ │
│  │(追踪点) │  │(处理器) │  │(导出器) │ │
│  └─────────┘  └─────────┘  └─────────┘ │
└─────────────────────────────────────────┘
              ↓
     ┌─────────────────┐
     │  OTLP Collector │ (可选)
     └─────────────────┘
              ↓
     ┌─────────────────┐
     │  后端存储       │
     │ (Jaeger/Tempo)  │
     └─────────────────┘
```

#### 关键术语

| 术语 | 说明 | 类比 |
|------|------|------|
| **Trace** | 完整的请求链路 | 快递的完整配送路径 |
| **Span** | 单个操作 | 快递在某个中转站 |
| **Attribute** | 描述信息 | 快递的重量、尺寸 |
| **Event** | 重要时刻 | 快递签收时间 |

---

## 2. 第一个追踪应用

### 2.1 5分钟快速开始

#### 步骤1: 创建项目

```bash
# 创建新项目
cargo new my-otlp-app
cd my-otlp-app

# 添加依赖
cargo add opentelemetry
cargo add opentelemetry_sdk
cargo add opentelemetry-otlp
cargo add tokio --features full
cargo add tracing
cargo add tracing-opentelemetry
cargo add tracing-subscriber
```

#### 步骤2: 最简单的示例

```rust
// src/main.rs
use opentelemetry::global;
use opentelemetry::trace::Tracer;
use opentelemetry_sdk::trace::TracerProvider;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1️⃣ 初始化 (只需要一次)
    let tracer_provider = TracerProvider::builder().build();
    global::set_tracer_provider(tracer_provider);
    
    // 2️⃣ 创建tracer
    let tracer = global::tracer("my-app");
    
    // 3️⃣ 创建span (追踪点)
    let span = tracer
        .span_builder("my-operation")
        .start(&tracer);
    
    // 4️⃣ 你的业务代码
    println!("Hello, OTLP!");
    
    // 5️⃣ 结束span
    drop(span);
    
    // 6️⃣ 清理
    global::shutdown_tracer_provider();
    
    Ok(())
}
```

**运行**:
```bash
cargo run
```

**输出**:
```
Hello, OTLP!
```

✅ 恭喜！你已经创建了第一个OTLP应用（虽然还没有导出数据）。

---

### 2.2 带导出功能的完整示例

#### 步骤1: 启动OTLP Collector (Docker)

```bash
# 创建配置文件
cat > otel-collector-config.yaml << EOF
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317

exporters:
  logging:
    loglevel: debug

service:
  pipelines:
    traces:
      receivers: [otlp]
      exporters: [logging]
EOF

# 启动collector
docker run -d \
  -p 4317:4317 \
  -v $(pwd)/otel-collector-config.yaml:/etc/otel-collector-config.yaml \
  otel/opentelemetry-collector:latest \
  --config=/etc/otel-collector-config.yaml
```

#### 步骤2: 更新代码添加导出

```rust
// src/main.rs
use opentelemetry::{global, trace::Tracer, KeyValue};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{
    trace::{self, TracerProvider},
    Resource,
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1️⃣ 创建OTLP导出器
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .build()?;
    
    // 2️⃣ 创建TracerProvider
    let tracer_provider = TracerProvider::builder()
        .with_batch_exporter(exporter)
        .with_resource(Resource::new(vec![
            KeyValue::new("service.name", "my-first-app"),
        ]))
        .build();
    
    global::set_tracer_provider(tracer_provider);
    
    // 3️⃣ 获取tracer
    let tracer = global::tracer("my-app");
    
    // 4️⃣ 创建span
    let mut span = tracer
        .span_builder("hello-operation")
        .start(&tracer);
    
    // 5️⃣ 添加属性
    span.set_attribute(KeyValue::new("user.id", 123));
    span.set_attribute(KeyValue::new("user.name", "Alice"));
    
    // 6️⃣ 模拟业务逻辑
    println!("Processing request...");
    tokio::time::sleep(std::time::Duration::from_millis(100)).await;
    
    // 7️⃣ 添加事件
    span.add_event("Request completed", vec![]);
    
    println!("Done!");
    
    // 8️⃣ span自动结束 (drop)
    drop(span);
    
    // 9️⃣ 等待数据发送
    tokio::time::sleep(std::time::Duration::from_secs(1)).await;
    
    // 🔟 清理
    global::shutdown_tracer_provider();
    
    Ok(())
}
```

**运行并查看结果**:
```bash
cargo run

# 查看collector日志
docker logs -f <container-id>
```

**你会看到**:
```json
{
  "resourceSpans": [{
    "resource": {
      "attributes": [{
        "key": "service.name",
        "value": "my-first-app"
      }]
    },
    "scopeSpans": [{
      "spans": [{
        "name": "hello-operation",
        "attributes": [
          {"key": "user.id", "value": 123},
          {"key": "user.name", "value": "Alice"}
        ],
        "events": [{
          "name": "Request completed"
        }]
      }]
    }]
  }]
}
```

✅ 完美！你已经成功发送了第一个trace！

---

### 2.3 使用tracing宏（推荐方式）

#### 更简洁的写法

```rust
// Cargo.toml添加
// tracing = "0.1"
// tracing-subscriber = "0.3"

use tracing::{info, instrument};
use tracing_subscriber::layer::SubscriberExt;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1️⃣ 初始化tracing
    let tracer = init_tracer()?;
    let telemetry = tracing_opentelemetry::layer().with_tracer(tracer);
    
    tracing_subscriber::registry()
        .with(telemetry)
        .init();
    
    // 2️⃣ 调用业务函数
    process_request(123, "Alice").await?;
    
    // 3️⃣ 清理
    opentelemetry::global::shutdown_tracer_provider();
    
    Ok(())
}

// 3️⃣ 使用#[instrument]自动追踪
#[instrument]
async fn process_request(user_id: i64, user_name: &str) -> Result<(), Box<dyn std::error::Error>> {
    info!("Processing request");  // 自动附加到span
    
    // 调用其他函数（自动成为子span）
    fetch_data().await?;
    
    info!("Request completed");
    Ok(())
}

#[instrument]
async fn fetch_data() -> Result<(), Box<dyn std::error::Error>> {
    info!("Fetching data from database");
    tokio::time::sleep(std::time::Duration::from_millis(50)).await;
    Ok(())
}

fn init_tracer() -> Result<opentelemetry_sdk::trace::Tracer, Box<dyn std::error::Error>> {
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .build()?;
    
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(exporter)
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    Ok(tracer)
}
```

**生成的Trace树**:
```
process_request (user_id=123, user_name="Alice")
├─ log: Processing request
├─ fetch_data
│  └─ log: Fetching data from database
└─ log: Request completed
```

✅ 这是推荐的方式！代码更简洁，自动追踪。

---

## 3. 基本配置

### 3.1 常用配置选项

#### 导出器配置

```rust
use opentelemetry_otlp::WithExportConfig;

// 基本配置
let exporter = opentelemetry_otlp::new_exporter()
    .tonic()
    .with_endpoint("http://localhost:4317")  // Collector地址
    .with_timeout(std::time::Duration::from_secs(3))  // 超时时间
    .build()?;

// 生产环境配置
let exporter = opentelemetry_otlp::new_exporter()
    .tonic()
    .with_endpoint("https://otlp.example.com:4317")
    .with_timeout(std::time::Duration::from_secs(10))
    // 添加认证（如果需要）
    .with_metadata(metadata)
    .build()?;
```

#### 批处理配置

```rust
use opentelemetry_sdk::trace::BatchConfig;

let tracer_provider = TracerProvider::builder()
    .with_batch_exporter(
        exporter,
        BatchConfig::default()
            .with_max_queue_size(2048)           // 队列大小
            .with_max_export_batch_size(512)     // 批次大小
            .with_scheduled_delay(std::time::Duration::from_secs(5))  // 导出间隔
    )
    .build();
```

#### 采样配置

```rust
use opentelemetry_sdk::trace::{Sampler, SamplingResult};

// 固定比例采样 (10%)
let sampler = Sampler::TraceIdRatioBased(0.1);

// 总是采样 (开发环境)
let sampler = Sampler::AlwaysOn;

// 使用采样器
let tracer_provider = TracerProvider::builder()
    .with_config(
        opentelemetry_sdk::trace::config()
            .with_sampler(sampler)
    )
    .with_batch_exporter(exporter)
    .build();
```

---

### 3.2 环境变量配置

```bash
# 推荐: 使用环境变量配置
export OTEL_EXPORTER_OTLP_ENDPOINT="http://localhost:4317"
export OTEL_SERVICE_NAME="my-service"
export OTEL_TRACES_SAMPLER="traceidratio"
export OTEL_TRACES_SAMPLER_ARG="0.1"

# 运行应用
cargo run
```

**代码中读取环境变量**:
```rust
use std::env;

let endpoint = env::var("OTEL_EXPORTER_OTLP_ENDPOINT")
    .unwrap_or_else(|_| "http://localhost:4317".to_string());

let service_name = env::var("OTEL_SERVICE_NAME")
    .unwrap_or_else(|_| "unknown-service".to_string());
```

---

## 4. 常见问题

### 4.1 为什么看不到数据？

#### 检查清单

```
□ Collector是否运行？
  docker ps | grep otel

□ 端口是否正确？
  默认: gRPC 4317, HTTP 4318

□ 是否等待数据发送？
  添加: tokio::time::sleep(Duration::from_secs(1)).await;

□ 是否调用shutdown？
  global::shutdown_tracer_provider();

□ 防火墙是否阻止？
  telnet localhost 4317
```

#### 调试技巧

```rust
// 1. 使用Console导出器（调试用）
use opentelemetry_stdout::SpanExporter;

let exporter = SpanExporter::default();
// 数据会打印到控制台

// 2. 启用日志
env_logger::init();
// 设置环境变量: RUST_LOG=debug

// 3. 检查连接
use tokio::net::TcpStream;

if TcpStream::connect("localhost:4317").await.is_ok() {
    println!("✅ Collector可连接");
} else {
    println!("❌ 无法连接到Collector");
}
```

---

### 4.2 性能影响

#### 典型开销

```
无追踪:          10,000 QPS
有追踪(不采样):   9,900 QPS  (-1%)
有追踪(10%采样):  9,800 QPS  (-2%)
有追踪(100%采样): 8,000 QPS  (-20%)
```

**建议**:
- ✅ 开发环境: 100%采样
- ✅ 生产环境: 10%采样
- ✅ 错误请求: 100%采样 (智能采样)

---

### 4.3 常见错误

#### 错误1: "connection refused"

```
原因: Collector未运行或端口错误
解决: 
1. 检查Collector: docker ps
2. 检查端口: netstat -an | grep 4317
3. 检查配置: echo $OTEL_EXPORTER_OTLP_ENDPOINT
```

#### 错误2: "spans dropped"

```
原因: 生成速度 > 导出速度
解决:
1. 增加批次大小: with_max_export_batch_size(1024)
2. 增加队列: with_max_queue_size(4096)
3. 降低采样率: TraceIdRatioBased(0.1)
```

#### 错误3: "no data in backend"

```
原因: Collector配置问题
解决:
1. 检查Collector配置
2. 检查backend连接
3. 查看Collector日志
```

---

### 4.4 最佳实践

#### DO ✅

```rust
// ✅ 使用tracing宏
#[instrument]
async fn my_function() {}

// ✅ 添加有意义的属性
span.set_attribute(KeyValue::new("user.id", user_id));

// ✅ 记录重要事件
span.add_event("payment_processed", vec![]);

// ✅ 使用批处理
.with_batch_exporter(exporter)

// ✅ 合理采样
.with_sampler(Sampler::TraceIdRatioBased(0.1))

// ✅ 调用shutdown
global::shutdown_tracer_provider();
```

#### DON'T ❌

```rust
// ❌ 不要在循环中创建tracer
for _ in 0..1000 {
    let tracer = global::tracer("app");  // 错误！
}

// ❌ 不要添加过多属性
span.set_attribute(KeyValue::new("huge.data", huge_json));  // 错误！

// ❌ 不要忘记结束span
let span = tracer.span_builder("op").start(&tracer);
// 忘记drop(span) - 错误！

// ❌ 不要100%采样生产环境
.with_sampler(Sampler::AlwaysOn)  // 生产环境错误！

// ❌ 不要阻塞主线程
std::thread::sleep(Duration::from_secs(5));  // 错误！
// 应该用: tokio::time::sleep
```

---

## 5. 下一步

### 5.1 学习路径

```
第1天: 快速开始 (本文档) ✅
  └─ 运行第一个示例

第2-3天: 基础追踪
  └─ 学习Span、Attribute、Event

第4-5天: HTTP集成
  └─ 集成到Web框架

第6-7天: 数据库追踪
  └─ 自动追踪DB查询

第2周: 高级特性
  └─ 采样、批处理、性能优化

第3周: 生产部署
  └─ Collector、后端、监控
```

### 5.2 推荐资源

- 📚 [OTLP完整文档](../03_API_REFERENCE/)
- 🎯 [最佳实践](../12_GUIDES/)
- 💻 [代码示例](../11_EXAMPLES/)
- 🏗️ [架构设计](../04_ARCHITECTURE/)

---

## 🔗 相关资源

- [对比矩阵](./COMPARISON_MATRIX.md)
- [知识图谱](./KNOWLEDGE_GRAPH.md)
- [API参考](../03_API_REFERENCE/)
- [完整指南](../12_GUIDES/)
- [OpenTelemetry官方文档](https://opentelemetry.io/docs/)

---

**版本**: 2.0  
**创建日期**: 2025-10-28  
**最后更新**: 2025-10-28  
**维护团队**: OTLP_rust入门团队

---

> **💡 新手提示**: 不要被复杂的概念吓倒！从最简单的示例开始，一步一步学习。OTLP的核心其实很简单：创建span → 添加信息 → 导出数据。

