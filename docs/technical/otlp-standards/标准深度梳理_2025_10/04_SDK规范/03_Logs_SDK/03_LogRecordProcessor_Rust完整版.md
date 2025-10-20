# LogRecordProcessor - Rust 完整实现指南

## 📋 目录

- [LogRecordProcessor - Rust 完整实现指南](#logrecordprocessor---rust-完整实现指南)
  - [📋 目录](#-目录)
  - [核心概念](#核心概念)
  - [Processor 类型](#processor-类型)
  - [Rust 实现](#rust-实现)
    - [BatchLogProcessor](#batchlogprocessor)
      - [**基础配置**](#基础配置)
      - [**高级配置**](#高级配置)
    - [SimpleLogProcessor](#simplelogprocessor)
    - [自定义 Processor](#自定义-processor)
      - [**实现过滤 Processor**](#实现过滤-processor)
      - [**实现采样 Processor**](#实现采样-processor)
      - [**实现属性增强 Processor**](#实现属性增强-processor)
  - [多 Processor 配置](#多-processor-配置)
  - [性能优化](#性能优化)
    - [**1. 调整队列大小**](#1-调整队列大小)
    - [**2. 批次大小优化**](#2-批次大小优化)
    - [**3. 导出间隔平衡**](#3-导出间隔平衡)
    - [**4. 避免阻塞**](#4-避免阻塞)
  - [最佳实践](#最佳实践)
    - [✅ **推荐**](#-推荐)
    - [❌ **避免**](#-避免)
  - [依赖库](#依赖库)
    - [**核心依赖**](#核心依赖)
    - [**自定义 Processor 依赖**](#自定义-processor-依赖)
  - [总结](#总结)

---

## 核心概念

**LogRecordProcessor** 是日志生命周期的钩子，负责：

1. **处理日志**：过滤、采样、增强
2. **批量聚合**：减少导出频率
3. **触发导出**：调用 LogRecordExporter

```text
┌─────────────────────────────────────────────┐
│          Logger.emit(LogRecord)             │
│                     ↓                       │
│  ┌───────────────────────────────────────┐  │
│  │ LogRecordProcessor                    │  │
│  │  - 过滤/采样                           │  │
│  │  - 批量聚合                            │  │
│  │  - 属性增强                            │  │
│  └───────────────────────────────────────┘  │
│                     ↓                       │
│  ┌───────────────────────────────────────┐  │
│  │ LogRecordExporter                     │  │
│  │  - 导出到 OTLP/File/Stdout            │  │
│  └───────────────────────────────────────┘  │
└─────────────────────────────────────────────┘
```

---

## Processor 类型

| 类型 | 行为 | 适用场景 |
|------|------|---------|
| **BatchLogProcessor** | 异步批量导出 | 生产环境（高性能） |
| **SimpleLogProcessor** | 同步立即导出 | 调试、关键日志 |
| **自定义 Processor** | 自定义逻辑 | 过滤、采样、增强 |

---

## Rust 实现

### BatchLogProcessor

**异步批量导出，推荐用于生产环境**-

#### **基础配置**

```rust
use opentelemetry_sdk::logs::{BatchLogProcessor, LoggerProvider};
use opentelemetry_otlp::WithExportConfig;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 创建 Exporter
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .build_log_exporter()?;

    // 2. 创建 BatchLogProcessor
    let processor = BatchLogProcessor::builder(exporter)
        .with_max_queue_size(2048)               // 队列大小
        .with_max_export_batch_size(512)         // 批次大小
        .with_scheduled_delay(Duration::from_secs(5))  // 导出间隔
        .with_max_export_timeout(Duration::from_secs(30))  // 导出超时
        .build();

    // 3. 创建 LoggerProvider
    let provider = LoggerProvider::builder()
        .with_log_processor(processor)
        .build();

    global::set_logger_provider(provider.clone());

    // 4. 使用日志
    tracing::info!("Application started");
    
    // 批量处理会自动在后台执行
    tokio::time::sleep(Duration::from_secs(10)).await;

    provider.shutdown()?;
    Ok(())
}
```

---

#### **高级配置**

```rust
use opentelemetry_sdk::logs::BatchConfig;

let batch_config = BatchConfig::default()
    .with_max_queue_size(4096)               // 增大队列（高流量）
    .with_max_export_batch_size(1024)        // 增大批次
    .with_scheduled_delay(Duration::from_secs(3))   // 缩短间隔
    .with_max_export_timeout(Duration::from_secs(10));

let processor = BatchLogProcessor::builder(exporter)
    .with_batch_config(batch_config)
    .build();
```

**配置建议**：

| 流量级别 | 队列大小 | 批次大小 | 导出间隔 |
|---------|---------|---------|---------|
| 低（< 100 log/s） | 1024 | 256 | 10s |
| 中（100-1000 log/s） | 2048 | 512 | 5s |
| 高（> 1000 log/s） | 4096 | 1024 | 3s |

---

### SimpleLogProcessor

**同步立即导出，适用于调试或关键日志**-

```rust
use opentelemetry_sdk::logs::SimpleLogProcessor;

let exporter = opentelemetry_stdout::LogExporter::default();

let processor = SimpleLogProcessor::new(Box::new(exporter));

let provider = LoggerProvider::builder()
    .with_log_processor(processor)
    .build();

// 每条日志立即导出（会阻塞业务线程）
tracing::error!("Critical error - immediate export");
```

**注意**：SimpleLogProcessor 会阻塞业务逻辑，仅用于：

- 本地调试
- 关键错误日志（需要确保导出）
- 测试环境

---

### 自定义 Processor

#### **实现过滤 Processor**

```rust
use opentelemetry::logs::LogRecord;
use opentelemetry_sdk::logs::{LogProcessor, LogResult};
use async_trait::async_trait;

struct FilteringProcessor {
    inner: Box<dyn LogProcessor>,
    min_severity: i32,  // 最小严重等级
}

impl FilteringProcessor {
    fn new(inner: Box<dyn LogProcessor>, min_severity: i32) -> Self {
        Self { inner, min_severity }
    }
}

#[async_trait]
impl LogProcessor for FilteringProcessor {
    fn emit(&self, record: &mut LogRecord) {
        // 过滤低等级日志
        if record.severity_number.unwrap_or(0) >= self.min_severity {
            self.inner.emit(record);
        }
    }

    fn force_flush(&self) -> LogResult<()> {
        self.inner.force_flush()
    }

    fn shutdown(&self) -> LogResult<()> {
        self.inner.shutdown()
    }
}

// 使用示例：仅导出 WARN 及以上等级
let base_processor = BatchLogProcessor::builder(exporter).build();
let filtering_processor = FilteringProcessor::new(
    Box::new(base_processor),
    13  // WARN
);

let provider = LoggerProvider::builder()
    .with_log_processor(filtering_processor)
    .build();
```

---

#### **实现采样 Processor**

```rust
use rand::Rng;

struct SamplingProcessor {
    inner: Box<dyn LogProcessor>,
    sample_rate: f64,  // 0.0 - 1.0
}

impl SamplingProcessor {
    fn new(inner: Box<dyn LogProcessor>, sample_rate: f64) -> Self {
        Self { inner, sample_rate }
    }
}

#[async_trait]
impl LogProcessor for SamplingProcessor {
    fn emit(&self, record: &mut LogRecord) {
        // 按比例采样
        if rand::thread_rng().gen_bool(self.sample_rate) {
            self.inner.emit(record);
        }
    }

    fn force_flush(&self) -> LogResult<()> {
        self.inner.force_flush()
    }

    fn shutdown(&self) -> LogResult<()> {
        self.inner.shutdown()
    }
}

// 使用示例：采样 20% 的日志
let base_processor = BatchLogProcessor::builder(exporter).build();
let sampling_processor = SamplingProcessor::new(
    Box::new(base_processor),
    0.2
);
```

---

#### **实现属性增强 Processor**

```rust
use opentelemetry::KeyValue;

struct EnrichingProcessor {
    inner: Box<dyn LogProcessor>,
    extra_attributes: Vec<KeyValue>,
}

impl EnrichingProcessor {
    fn new(inner: Box<dyn LogProcessor>, extra_attributes: Vec<KeyValue>) -> Self {
        Self { inner, extra_attributes }
    }
}

#[async_trait]
impl LogProcessor for EnrichingProcessor {
    fn emit(&self, record: &mut LogRecord) {
        // 添加额外属性
        let mut attrs = record.attributes.clone().unwrap_or_default();
        attrs.extend(self.extra_attributes.clone());
        record.attributes = Some(attrs);
        
        self.inner.emit(record);
    }

    fn force_flush(&self) -> LogResult<()> {
        self.inner.force_flush()
    }

    fn shutdown(&self) -> LogResult<()> {
        self.inner.shutdown()
    }
}

// 使用示例：为所有日志添加环境信息
let base_processor = BatchLogProcessor::builder(exporter).build();
let enriching_processor = EnrichingProcessor::new(
    Box::new(base_processor),
    vec![
        KeyValue::new("environment", "production"),
        KeyValue::new("region", "us-west-2"),
        KeyValue::new("version", env!("CARGO_PKG_VERSION")),
    ]
);
```

---

## 多 Processor 配置

**同时使用多个 Processor**-

```rust
let provider = LoggerProvider::builder()
    .with_resource(Resource::new(vec![
        KeyValue::new("service.name", "multi-processor-demo"),
    ]))
    // Processor 1: OTLP 批量导出
    .with_log_processor(
        BatchLogProcessor::builder(otlp_exporter).build()
    )
    // Processor 2: 本地文件同步导出
    .with_log_processor(
        SimpleLogProcessor::new(Box::new(file_exporter))
    )
    // Processor 3: Stdout 调试输出
    .with_log_processor(
        SimpleLogProcessor::new(Box::new(stdout_exporter))
    )
    .build();
```

**执行顺序**：按添加顺序依次执行

---

## 性能优化

### **1. 调整队列大小**

```rust
// ❌ 队列过小：高流量时丢失日志
let processor = BatchLogProcessor::builder(exporter)
    .with_max_queue_size(128)
    .build();

// ✅ 队列合理：缓冲突发流量
let processor = BatchLogProcessor::builder(exporter)
    .with_max_queue_size(4096)
    .build();
```

---

### **2. 批次大小优化**

```rust
// ❌ 批次过小：导出频繁，开销大
let processor = BatchLogProcessor::builder(exporter)
    .with_max_export_batch_size(10)
    .build();

// ✅ 批次合理：减少网络开销
let processor = BatchLogProcessor::builder(exporter)
    .with_max_export_batch_size(512)
    .build();
```

---

### **3. 导出间隔平衡**

```rust
// ❌ 间隔过长：日志延迟高
let processor = BatchLogProcessor::builder(exporter)
    .with_scheduled_delay(Duration::from_secs(60))
    .build();

// ✅ 间隔合理：平衡延迟和性能
let processor = BatchLogProcessor::builder(exporter)
    .with_scheduled_delay(Duration::from_secs(5))
    .build();
```

---

### **4. 避免阻塞**

```rust
// ❌ SimpleProcessor 阻塞业务线程
let processor = SimpleLogProcessor::new(Box::new(slow_exporter));

// ✅ BatchProcessor 异步导出
let processor = BatchLogProcessor::builder(slow_exporter).build();
```

---

## 最佳实践

### ✅ **推荐**

1. **生产环境使用 BatchLogProcessor**：异步批量导出
2. **合理配置队列大小**：根据流量级别调整
3. **组合 Processor**：
   - 主流量 → OTLP BatchProcessor
   - ERROR 级别 → 本地文件 SimpleProcessor（备份）
4. **自定义 Processor 链**：

   ```text
   FilteringProcessor → SamplingProcessor → EnrichingProcessor → BatchLogProcessor
   ```

5. **监控队列使用率**：避免队列满导致丢失
6. **优雅关闭**：调用 `shutdown()` 确保刷新

### ❌ **避免**

1. **过小的队列**：高流量时丢失日志
2. **过度使用 SimpleProcessor**：同步导出阻塞业务
3. **忘记调用 shutdown()**：可能丢失队列中的日志
4. **过长的导出间隔**：导致日志延迟
5. **自定义 Processor 阻塞**：应避免 I/O 操作

---

## 依赖库

### **核心依赖**

```toml
[dependencies]
opentelemetry = "0.24"
opentelemetry-sdk = "0.24"
tokio = { version = "1", features = ["full"] }
```

### **自定义 Processor 依赖**

```toml
async-trait = "0.1"
rand = "0.8"           # 采样控制
```

---

## 总结

| Processor 类型 | 模式 | 适用场景 | 配置要点 |
|--------------|------|---------|---------|
| **BatchLogProcessor** | 异步批量 | 生产环境 | 调整队列、批次、间隔 |
| **SimpleLogProcessor** | 同步立即 | 调试/关键日志 | 避免阻塞业务线程 |
| **FilteringProcessor** | 过滤 | 减少日志量 | 设置最小等级 |
| **SamplingProcessor** | 采样 | 高频日志 | 控制采样率 |
| **EnrichingProcessor** | 增强 | 添加元数据 | 附加上下文属性 |

**下一步**：[04_LogRecordExporter_Rust完整版.md](./04_LogRecordExporter_Rust完整版.md) - 学习日志导出器的实现
