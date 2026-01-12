# OTLP 导出器指南 2025

**创建日期**: 2025年1月
**状态**: 📚 使用指南
**Rust 版本**: 1.92+

---

## 📋 概述

OTLP 导出器模块 (`crates/otlp/src/exporter.rs`) 实现了 OTLP 数据的导出功能，支持多种传输方式、重试机制和异步导出。

---

## 🚀 快速开始

### 基本使用

```rust
use otlp::{OtlpExporter, OtlpConfig};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = OtlpConfig::default();
    let exporter = OtlpExporter::new(config);

    // 初始化
    exporter.initialize().await?;

    // 导出数据
    let result = exporter.export(data).await?;

    // 关闭
    exporter.shutdown().await?;

    Ok(())
}
```

---

## 📖 详细说明

### 核心类型

#### OtlpExporter

主要的导出器结构体，负责数据的导出。

**主要方法**:
- `new(config: OtlpConfig) -> Self` - 创建导出器
- `initialize() -> Result<()>` - 初始化导出器
- `export(data: Vec<TelemetryData>) -> Result<ExportResult>` - 导出数据
- `export_single(data: TelemetryData) -> Result<ExportResult>` - 导出单个数据
- `export_async_enqueue(data: Vec<TelemetryData>) -> Result<()>` - 异步入队导出
- `shutdown() -> Result<()>` - 关闭导出器
- `get_metrics() -> ExporterMetrics` - 获取指标

#### ExportResult

导出结果，包含成功/失败统计。

**字段**:
- `success_count: usize` - 成功数量
- `failure_count: usize` - 失败数量
- `duration: Duration` - 导出耗时
- `errors: Vec<String>` - 错误信息

**方法**:
- `is_success() -> bool` - 是否完全成功
- `is_failure() -> bool` - 是否完全失败
- `total_count() -> usize` - 总数量
- `success_rate() -> f64` - 成功率

#### ExporterMetrics

导出器指标，用于监控导出性能。

**字段**:
- `total_exports: u64` - 总导出次数
- `successful_exports: u64` - 成功次数
- `failed_exports: u64` - 失败次数
- `total_data_exported: u64` - 总导出数据量
- `average_export_latency: Duration` - 平均延迟
- `max_export_latency: Duration` - 最大延迟
- `total_retries: u64` - 总重试次数
- `current_queue_size: usize` - 当前队列大小

---

## 💡 示例代码

### 示例 1: 基本导出

```rust
use otlp::{OtlpExporter, OtlpConfig, TelemetryData};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = OtlpConfig::default();
    let exporter = OtlpExporter::new(config);

    exporter.initialize().await?;

    let data = vec![/* TelemetryData */];
    let result = exporter.export(data).await?;

    println!("导出结果: 成功 {} 个, 失败 {} 个",
        result.success_count, result.failure_count);

    exporter.shutdown().await?;
    Ok(())
}
```

### 示例 2: 单个数据导出

```rust
use otlp::{OtlpExporter, TelemetryData};

async fn export_single(exporter: &OtlpExporter, data: TelemetryData) -> Result<(), Box<dyn std::error::Error>> {
    let result = exporter.export_single(data).await?;

    if result.is_success() {
        println!("导出成功");
    } else {
        eprintln!("导出失败: {:?}", result.errors);
    }

    Ok(())
}
```

### 示例 3: 异步导出

```rust
use otlp::{OtlpExporter, TelemetryData};

async fn export_async(exporter: &OtlpExporter, data: Vec<TelemetryData>) -> Result<(), Box<dyn std::error::Error>> {
    // 异步入队
    exporter.export_async_enqueue(data).await?;

    // 数据会在后台异步导出
    Ok(())
}
```

### 示例 4: 监控指标

```rust
use otlp::OtlpExporter;

async fn monitor_metrics(exporter: &OtlpExporter) {
    let metrics = exporter.get_metrics().await;

    println!("总导出次数: {}", metrics.total_exports);
    println!("成功次数: {}", metrics.successful_exports);
    println!("失败次数: {}", metrics.failed_exports);
    println!("平均延迟: {:?}", metrics.average_export_latency);
    println!("当前队列大小: {}", metrics.current_queue_size);
}
```

---

## 🎯 最佳实践

### 1. 初始化导出器

在使用导出器之前，必须调用 `initialize()`：

```rust
exporter.initialize().await?;
```

### 2. 批量导出

对于多个数据，使用批量导出以提高效率：

```rust
// ✅ 推荐：批量导出
let result = exporter.export(data_vec).await?;

// ❌ 不推荐：逐个导出
for data in data_vec {
    exporter.export_single(data).await?;
}
```

### 3. 错误处理

始终检查导出结果：

```rust
let result = exporter.export(data).await?;

if !result.is_success() {
    eprintln!("导出失败: {:?}", result.errors);
    // 处理错误...
}
```

### 4. 监控队列大小

定期检查队列大小，避免队列溢出：

```rust
let metrics = exporter.get_metrics().await;
if metrics.current_queue_size > threshold {
    // 队列过大，需要处理
}
```

---

## ⚠️ 注意事项

### 1. 初始化顺序

必须先初始化导出器才能使用：

```rust
// ❌ 错误：未初始化
let result = exporter.export(data).await?;  // 会返回错误

// ✅ 正确：先初始化
exporter.initialize().await?;
let result = exporter.export(data).await?;
```

### 2. 队列容量

异步导出使用有界队列，队列满时会返回错误：

```rust
match exporter.export_async_enqueue(data).await {
    Ok(()) => println!("入队成功"),
    Err(e) => {
        if e.is_queue_full() {
            eprintln!("队列已满，需要等待或使用同步导出");
        }
    }
}
```

### 3. 优雅关闭

在程序退出前，调用 `shutdown()` 来优雅关闭：

```rust
exporter.shutdown().await?;
```

---

## 📚 参考资源

### 相关文档

- [配置指南](./CONFIG_GUIDE_2025.md) - 导出器配置
- [错误处理指南](./ERROR_HANDLING_GUIDE_2025.md) - 导出错误处理
- [客户端指南](./CLIENT_GUIDE_2025.md) - 客户端使用导出器

### API 参考

- `OtlpExporter` - 导出器结构体
- `ExportResult` - 导出结果
- `ExporterMetrics` - 导出器指标
- `BatchExporter` - 批处理导出器
- `AsyncExporter` - 异步导出器

---

**状态**: 📚 使用指南
**最后更新**: 2025年1月
