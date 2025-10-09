# LoggerProvider - Rust 完整实现指南

## 📋 目录

- [LoggerProvider - Rust 完整实现指南](#loggerprovider---rust-完整实现指南)
  - [📋 目录](#-目录)
  - [核心概念](#核心概念)
  - [LoggerProvider 的职责](#loggerprovider-的职责)
    - [1. **全局配置**](#1-全局配置)
    - [2. **Logger 管理**](#2-logger-管理)
    - [3. **生命周期钩子**](#3-生命周期钩子)
  - [Rust 实现](#rust-实现)
    - [基础配置](#基础配置)
    - [生产级配置](#生产级配置)
      - [**多 Processor 支持**](#多-processor-支持)
      - [**Resource 自动检测**](#resource-自动检测)
    - [与 tracing 集成](#与-tracing-集成)
  - [生命周期管理](#生命周期管理)
    - [**优雅关闭**](#优雅关闭)
    - [**ForceFlush：确保导出**](#forceflush确保导出)
  - [最佳实践](#最佳实践)
    - [✅ **推荐**](#-推荐)
    - [❌ **避免**](#-避免)
  - [依赖库](#依赖库)
    - [**核心依赖**](#核心依赖)
    - [**tracing 集成**](#tracing-集成)
    - [**可选增强**](#可选增强)
  - [总结](#总结)

---

## 核心概念

**LoggerProvider** 是 OpenTelemetry Logs SDK 的入口点，负责：

1. **全局配置管理**：Resource、LogRecordProcessor
2. **Logger 工厂**：创建和管理 Logger 实例
3. **生命周期管理**：初始化、运行时配置、优雅关闭

```text
┌─────────────────────────────────────────────────┐
│            LoggerProvider                       │
│  ┌───────────────────────────────────────────┐  │
│  │ Resource: service.name, host.name, ...    │  │
│  ├───────────────────────────────────────────┤  │
│  │ LogRecordProcessor: Batch/Simple          │  │
│  ├───────────────────────────────────────────┤  │
│  │ LogRecordExporter: OTLP/Stdout/File       │  │
│  └───────────────────────────────────────────┘  │
│                     ↓                           │
│     ┌─────────────────────────────────┐         │
│     │ Logger("my-service", "1.0.0")   │         │
│     └─────────────────────────────────┘         │
└─────────────────────────────────────────────────┘
```

---

## LoggerProvider 的职责

### 1. **全局配置**

- **Resource**：描述服务的元数据（服务名、版本、环境）
- **LogRecordProcessor**：定义日志处理策略（批量/同步）
- **LogRecordExporter**：指定日志导出目标（OTLP、文件、stdout）

### 2. **Logger 管理**

- 根据 `instrumentation_scope`（库名 + 版本）创建 Logger
- 缓存 Logger 实例以避免重复创建
- 支持动态配置更新

### 3. **生命周期钩子**

- **初始化**：加载配置、启动 Processor
- **Shutdown**：刷新所有未导出的日志、清理资源
- **ForceFlush**：强制导出所有待处理的日志

---

## Rust 实现

### 基础配置

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    logs::{LoggerProvider, BatchLogProcessor},
    Resource,
};
use opentelemetry_otlp::WithExportConfig;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 创建 OTLP Exporter
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .build_log_exporter()?;

    // 2. 创建 BatchLogProcessor（异步批量导出）
    let processor = BatchLogProcessor::builder(exporter)
        .with_max_queue_size(2048)
        .with_max_export_batch_size(512)
        .with_scheduled_delay(Duration::from_secs(5))
        .build();

    // 3. 定义 Resource
    let resource = Resource::new(vec![
        KeyValue::new("service.name", "my-rust-service"),
        KeyValue::new("service.version", "1.0.0"),
        KeyValue::new("deployment.environment", "production"),
    ]);

    // 4. 创建 LoggerProvider
    let provider = LoggerProvider::builder()
        .with_resource(resource)
        .with_log_processor(processor)
        .build();

    // 5. 设置为全局 LoggerProvider
    global::set_logger_provider(provider.clone());

    // 6. 使用 Logger 记录日志
    let logger = global::logger("my-service");
    logger.emit(
        opentelemetry::logs::LogRecord::builder()
            .with_severity_text("INFO")
            .with_body("Application started")
            .build()
    );

    // 7. 优雅关闭
    provider.shutdown()?;
    Ok(())
}
```

**依赖 (Cargo.toml)**：

```toml
[dependencies]
opentelemetry = "0.24"
opentelemetry-sdk = "0.24"
opentelemetry-otlp = "0.24"
tokio = { version = "1", features = ["full"] }
```

---

### 生产级配置

#### **多 Processor 支持**

```rust
use opentelemetry_sdk::logs::{
    BatchLogProcessor, SimpleLogProcessor, LoggerProvider,
};

async fn init_provider() -> Result<LoggerProvider, Box<dyn std::error::Error>> {
    // Processor 1: OTLP 批量导出（生产环境）
    let otlp_exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://otlp-collector:4317")
        .build_log_exporter()?;
    
    let batch_processor = BatchLogProcessor::builder(otlp_exporter)
        .with_max_queue_size(4096)
        .with_max_export_batch_size(512)
        .with_scheduled_delay(Duration::from_secs(5))
        .with_max_export_timeout(Duration::from_secs(30))
        .build();

    // Processor 2: 本地文件同步导出（备份）
    let file_exporter = FileLogExporter::new("logs/app.log")?;
    let simple_processor = SimpleLogProcessor::new(Box::new(file_exporter));

    // 同时使用两个 Processor
    let provider = LoggerProvider::builder()
        .with_resource(detect_resource())
        .with_log_processor(batch_processor)
        .with_log_processor(simple_processor)
        .build();

    Ok(provider)
}
```

---

#### **Resource 自动检测**

```rust
use opentelemetry_sdk::Resource;
use opentelemetry_semantic_conventions as semconv;

fn detect_resource() -> Resource {
    let mut resource = Resource::default();

    // 1. 从环境变量读取
    if let Ok(service_name) = std::env::var("OTEL_SERVICE_NAME") {
        resource = resource.merge(&Resource::new(vec![
            KeyValue::new(semconv::resource::SERVICE_NAME, service_name),
        ]));
    }

    // 2. 检测部署环境
    let environment = std::env::var("DEPLOY_ENV").unwrap_or_else(|_| "development".to_string());
    resource = resource.merge(&Resource::new(vec![
        KeyValue::new("deployment.environment", environment),
    ]));

    // 3. 自动检测主机信息
    resource = resource.merge(&Resource::new(vec![
        KeyValue::new(
            semconv::resource::HOST_NAME,
            hostname::get()
                .unwrap_or_default()
                .to_string_lossy()
                .to_string(),
        ),
        KeyValue::new(
            semconv::resource::OS_TYPE,
            std::env::consts::OS,
        ),
        KeyValue::new(
            semconv::resource::OS_VERSION,
            std::env::consts::ARCH,
        ),
    ]));

    // 4. 检测 Kubernetes 环境
    if let Ok(pod_name) = std::env::var("HOSTNAME") {
        resource = resource.merge(&Resource::new(vec![
            KeyValue::new("k8s.pod.name", pod_name),
        ]));
        
        if let Ok(namespace) = std::env::var("POD_NAMESPACE") {
            resource = resource.merge(&Resource::new(vec![
                KeyValue::new("k8s.namespace.name", namespace),
            ]));
        }
    }

    resource
}
```

**依赖**：

```toml
[dependencies]
opentelemetry-semantic-conventions = "0.16"
hostname = "0.4"
```

---

### 与 tracing 集成

**OpenTelemetry Logs 与 Rust `tracing` 生态深度集成**：

```rust
use tracing_subscriber::{layer::SubscriberExt, Registry};
use opentelemetry_appender_tracing::layer::OpenTelemetryTracingBridge;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 创建 LoggerProvider
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .build_log_exporter()?;
    
    let processor = BatchLogProcessor::builder(exporter).build();
    
    let provider = LoggerProvider::builder()
        .with_resource(Resource::new(vec![
            KeyValue::new("service.name", "tracing-bridge-demo"),
        ]))
        .with_log_processor(processor)
        .build();

    global::set_logger_provider(provider.clone());

    // 2. 创建 OpenTelemetry Layer
    let otel_layer = OpenTelemetryTracingBridge::new(&provider);

    // 3. 组合订阅者（同时输出到控制台和 OTLP）
    let subscriber = Registry::default()
        .with(tracing_subscriber::fmt::layer())  // 控制台输出
        .with(otel_layer);                        // OTLP 导出

    tracing::subscriber::set_global_default(subscriber)?;

    // 4. 使用 tracing 宏（自动桥接到 OpenTelemetry）
    tracing::info!("Application started");
    tracing::warn!(user_id = 123, "User authentication failed");
    tracing::error!(error = %"Connection timeout", "Database error");

    // 5. 优雅关闭
    provider.shutdown()?;
    Ok(())
}
```

**依赖**：

```toml
[dependencies]
tracing = "0.1"
tracing-subscriber = "0.3"
opentelemetry-appender-tracing = "0.5"
```

---

## 生命周期管理

### **优雅关闭**

```rust
use tokio::signal;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let provider = init_logger_provider().await?;
    global::set_logger_provider(provider.clone());

    // 应用逻辑
    tokio::spawn(async {
        tracing::info!("Background task started");
        loop {
            tracing::debug!("Heartbeat");
            tokio::time::sleep(Duration::from_secs(30)).await;
        }
    });

    // 等待 SIGTERM/SIGINT
    signal::ctrl_c().await?;
    tracing::info!("Shutting down gracefully...");

    // 强制刷新 + 关闭
    provider.force_flush()?;
    provider.shutdown()?;
    
    println!("All logs exported successfully");
    Ok(())
}
```

---

### **ForceFlush：确保导出**

```rust
async fn critical_operation(provider: &LoggerProvider) -> Result<(), Box<dyn std::error::Error>> {
    let logger = provider.logger("critical-ops");
    
    logger.emit(
        opentelemetry::logs::LogRecord::builder()
            .with_severity_text("CRITICAL")
            .with_body("Payment processed: $10,000")
            .with_attributes(vec![
                KeyValue::new("transaction_id", "TXN-12345"),
                KeyValue::new("amount", 10000),
            ])
            .build()
    );
    
    // 立即导出（不等待批处理触发）
    provider.force_flush()?;
    
    Ok(())
}
```

---

## 最佳实践

### ✅ **推荐**

1. **全局单例**：使用 `global::set_logger_provider` 设置一次
2. **Resource 检测**：自动检测环境信息（K8s、云平台）
3. **批量处理**：生产环境使用 `BatchLogProcessor` 减少开销
4. **多 Processor**：同时导出到 OTLP 和本地文件（备份）
5. **tracing 集成**：使用 `opentelemetry-appender-tracing` 桥接
6. **优雅关闭**：监听系统信号，调用 `shutdown()` 前先 `force_flush()`
7. **结构化日志**：使用 `with_attributes()` 而非嵌入文本

### ❌ **避免**

1. **频繁创建 Provider**：应缓存和复用
2. **忘记调用 shutdown()**：可能导致日志丢失
3. **过度使用 SimpleProcessor**：同步导出会阻塞业务逻辑
4. **忽略错误处理**：Exporter 失败时应记录到本地文件
5. **高频 ForceFlush**：仅在关键路径使用

---

## 依赖库

### **核心依赖**

```toml
[dependencies]
opentelemetry = "0.24"
opentelemetry-sdk = "0.24"
opentelemetry-otlp = "0.24"          # OTLP 导出
opentelemetry-stdout = "0.24"        # Stdout 导出
tokio = { version = "1", features = ["full"] }
```

### **tracing 集成**

```toml
tracing = "0.1"
tracing-subscriber = "0.3"
opentelemetry-appender-tracing = "0.5"
```

### **可选增强**

```toml
opentelemetry-semantic-conventions = "0.16"  # 语义约定
hostname = "0.4"                             # 主机名检测
```

---

## 总结

| 功能 | 实现方式 |
|------|---------|
| 全局配置 | `LoggerProvider::builder()` |
| OTLP 导出 | `BatchLogProcessor` + `opentelemetry_otlp` |
| 本地文件 | `SimpleLogProcessor` + 自定义 `FileLogExporter` |
| tracing 桥接 | `OpenTelemetryTracingBridge` |
| Resource 检测 | `Resource::default()` + 环境变量 |
| 优雅关闭 | `force_flush()` + `shutdown()` |

**下一步**：[02_Logger_Rust完整版.md](./02_Logger_Rust完整版.md) - 学习如何使用 Logger 记录结构化日志
