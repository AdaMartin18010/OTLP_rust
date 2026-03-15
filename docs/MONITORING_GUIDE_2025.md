# 监控与可观测性指南 2025

**创建日期**: 2025年1月
**状态**: 📚 使用指南
**Rust 版本**: 1.92+

---

## 📋 概述

监控与可观测性模块 (`crates/otlp/src/monitoring/`) 提供了完整的监控、指标收集、日志聚合和分布式追踪功能，包括错误监控系统、实时仪表板、告警管理和趋势分析。

---

## 🚀 快速开始

### 基本使用

```rust
use otlp::monitoring::{ErrorMonitoringSystem, ErrorMonitoringConfig};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = ErrorMonitoringConfig::default();
    let mut system = ErrorMonitoringSystem::new(config);

    system.start().await?;

    // 记录错误事件
    system.record_error(ErrorEvent {
        // ...
    }).await?;

    Ok(())
}
```

---

## 📖 详细说明

### 核心类型

#### ErrorMonitoringSystem

错误监控系统，用于监控和分析错误。

**方法**:

- `new(config: ErrorMonitoringConfig) -> Self` - 创建系统
- `start() -> Result<()>` - 启动系统
- `record_error(event: ErrorEvent) -> Result<()>` - 记录错误
- `get_metrics() -> ErrorMonitoringMetrics` - 获取指标

#### MetricsCollector

指标收集器，用于收集和聚合指标。

**方法**:

- `new(config: MetricsCollectorConfig) -> Self` - 创建收集器
- `record_metric(metric: MetricDataPoint) -> Result<()>` - 记录指标
- `get_stats() -> MetricsCollectorStats` - 获取统计信息

#### PrometheusExporter

Prometheus 导出器，用于导出指标到 Prometheus。

**方法**:

- `new(config: PrometheusExporterConfig) -> Self` - 创建导出器
- `export() -> Result<String>` - 导出指标
- `get_stats() -> PrometheusExporterStats` - 获取统计信息

---

## 💡 示例代码

### 示例 1: 错误监控

```rust
use otlp::monitoring::{ErrorMonitoringSystem, ErrorEvent, ErrorSeverity};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = ErrorMonitoringConfig::default();
    let mut system = ErrorMonitoringSystem::new(config);
    system.start().await?;

    let event = ErrorEvent {
        severity: ErrorSeverity::Error,
        message: "Database connection failed".to_string(),
        // ...
    };

    system.record_error(event).await?;

    let metrics = system.get_metrics().await;
    println!("总错误数: {}", metrics.total_errors);

    Ok(())
}
```

### 示例 2: 指标收集

```rust
use otlp::monitoring::{MetricsCollector, MetricDataPoint, MetricType};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = MetricsCollectorConfig::default();
    let mut collector = MetricsCollector::new(config);

    let metric = MetricDataPoint {
        name: "requests_per_second".to_string(),
        value: MetricValue::Counter(100.0),
        labels: vec![],
        timestamp: SystemTime::now(),
    };

    collector.record_metric(metric).await?;

    let stats = collector.get_stats();
    println!("总指标数: {}", stats.total_metrics);

    Ok(())
}
```

---

## 🎯 最佳实践

### 1. 错误分类

根据严重程度分类错误：

```rust
match error_severity {
    ErrorSeverity::Critical => {
        // 立即告警
    }
    ErrorSeverity::Error => {
        // 记录并监控
    }
    ErrorSeverity::Warning => {
        // 记录
    }
    ErrorSeverity::Info => {
        // 仅记录
    }
}
```

---

## 📚 参考资源

### API 参考

- `ErrorMonitoringSystem` - 错误监控系统
- `MetricsCollector` - 指标收集器
- `PrometheusExporter` - Prometheus 导出器

---

**状态**: 📚 使用指南
**最后更新**: 2025年1月
