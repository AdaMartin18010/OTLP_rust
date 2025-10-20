# OpenTelemetry Metrics 规范

## 📋 目录

- [OpenTelemetry Metrics 规范](#opentelemetry-metrics-规范)
  - [📋 目录](#-目录)
  - [📊 OpenTelemetry Metrics 规范概览](#-opentelemetry-metrics-规范概览)
  - [🎯 OpenTelemetry Metrics 规范目标](#-opentelemetry-metrics-规范目标)
    - [主要目标](#主要目标)
    - [成功标准](#成功标准)
  - [目录](#目录)
  - [1. 概述](#1-概述)
  - [2. 核心概念](#2-核心概念)
    - [2.1 Metric](#21-metric)
    - [2.2 Instrument](#22-instrument)
    - [2.3 Meter](#23-meter)
  - [3. 数据类型](#3-数据类型)
    - [3.1 Counter](#31-counter)
    - [3.2 Gauge](#32-gauge)
    - [3.3 Histogram](#33-histogram)
    - [3.4 ExponentialHistogram](#34-exponentialhistogram)
    - [3.5 Summary](#35-summary)
  - [4. 数据模型](#4-数据模型)
    - [4.1 Metric结构](#41-metric结构)
    - [4.2 Gauge](#42-gauge)
    - [4.3 Sum](#43-sum)
    - [4.4 Histogram](#44-histogram)
  - [5. 语义约定](#5-语义约定)
    - [5.1 HTTP指标](#51-http指标)
    - [5.2 数据库指标](#52-数据库指标)
    - [5.3 系统指标](#53-系统指标)
  - [6. 聚合和导出](#6-聚合和导出)
    - [6.1 聚合器类型](#61-聚合器类型)
    - [6.2 导出配置](#62-导出配置)
  - [7. 性能优化](#7-性能优化)
    - [7.1 批处理](#71-批处理)
    - [7.2 内存管理](#72-内存管理)
  - [8. 视图和过滤](#8-视图和过滤)
    - [8.1 视图配置](#81-视图配置)
    - [8.2 属性过滤](#82-属性过滤)
  - [9. 最佳实践](#9-最佳实践)
    - [9.1 指标命名](#91-指标命名)
    - [9.2 属性设计](#92-属性设计)
    - [9.3 单位使用](#93-单位使用)
  - [10. 监控和告警](#10-监控和告警)
    - [10.1 Prometheus集成](#101-prometheus集成)
    - [10.2 告警规则](#102-告警规则)
  - [11. 故障排除](#11-故障排除)
    - [11.1 常见问题](#111-常见问题)
    - [11.2 调试工具](#112-调试工具)
  - [12. 总结](#12-总结)
  - [2025 指标标准对齐（权威与中性）](#2025-指标标准对齐权威与中性)

## 📊 OpenTelemetry Metrics 规范概览

**创建时间**: 2025年09月22日  
**文档版本**: 2.0.0  
**维护者**: OpenTelemetry 2025 团队  
**状态**: 知识理论模型分析梳理项目  
**OpenTelemetry Metrics 规范范围**: OpenTelemetry Metrics 规范分析

## 🎯 OpenTelemetry Metrics 规范目标

### 主要目标

1. **目标1**: 实现OpenTelemetry Metrics 规范的核心功能
2. **目标2**: 确保OpenTelemetry Metrics 规范的质量和可靠性
3. **目标3**: 提供OpenTelemetry Metrics 规范的完整解决方案
4. **目标4**: 建立OpenTelemetry Metrics 规范的最佳实践
5. **目标5**: 推动OpenTelemetry Metrics 规范的持续改进

### 成功标准

- **标准1**: 100%功能实现
- **标准2**: 高质量标准达成
- **标准3**: 完整解决方案提供
- **标准4**: 最佳实践建立
- **标准5**: 持续改进机制

## 目录

- [OpenTelemetry Metrics 规范](#opentelemetry-metrics-规范)

---

## 1. 概述

指标（Metrics）是OpenTelemetry的三大信号之一，用于监控系统的性能、健康状态和业务指标。

## 2. 核心概念

### 2.1 Metric

- **定义**: 表示一个可测量的数值
- **类型**: 支持多种数据类型和聚合方式
- **生命周期**: 持续收集和报告

### 2.2 Instrument

- **定义**: 用于记录指标数据的工具
- **类型**: Counter、Gauge、Histogram等
- **作用域**: 绑定到特定的Meter

### 2.3 Meter

- **定义**: 创建和管理Instrument的工厂
- **命名**: 通常以库或服务名命名
- **版本**: 支持版本管理

## 3. 数据类型

### 3.1 Counter

```go
// 单调递增计数器
counter, err := meter.Int64Counter(
    "http_requests_total",
    metric.WithDescription("Total HTTP requests"),
    metric.WithUnit("1"),
)

counter.Add(ctx, 1, attribute.String("method", "POST"))
```

### 3.2 Gauge

```go
// 瞬时值测量
gauge, err := meter.Float64Gauge(
    "memory_usage_bytes",
    metric.WithDescription("Memory usage in bytes"),
    metric.WithUnit("By"),
)

gauge.Record(ctx, 1024*1024, attribute.String("type", "heap"))
```

### 3.3 Histogram

```go
// 分布值测量
histogram, err := meter.Float64Histogram(
    "http_request_duration_seconds",
    metric.WithDescription("HTTP request duration"),
    metric.WithUnit("s"),
)

histogram.Record(ctx, 0.5, attribute.String("method", "GET"))
```

### 3.4 ExponentialHistogram

```go
// 指数直方图
expHistogram, err := meter.Float64ExponentialHistogram(
    "request_size_bytes",
    metric.WithDescription("Request size distribution"),
    metric.WithUnit("By"),
)

expHistogram.Record(ctx, 1024, attribute.String("service", "api"))
```

### 3.5 Summary

```go
// 预聚合统计
summary, err := meter.Float64Summary(
    "response_time_seconds",
    metric.WithDescription("Response time summary"),
    metric.WithUnit("s"),
)

summary.Record(ctx, 0.1, attribute.String("endpoint", "/users"))
```

## 4. 数据模型

### 4.1 Metric结构

```protobuf
message Metric {
  string name = 1;
  string description = 2;
  string unit = 3;
  oneof data {
    Gauge gauge = 5;
    Sum sum = 7;
    Histogram histogram = 9;
    ExponentialHistogram exponential_histogram = 10;
    Summary summary = 11;
  }
}
```

### 4.2 Gauge

```protobuf
message Gauge {
  repeated NumberDataPoint data_points = 1;
}

message NumberDataPoint {
  repeated KeyValue attributes = 1;
  fixed64 start_time_unix_nano = 2;
  fixed64 time_unix_nano = 3;
  oneof value {
    double as_double = 4;
    sfixed64 as_int = 6;
  }
  repeated Exemplar exemplars = 5;
  uint32 flags = 8;
}
```

### 4.3 Sum

```protobuf
message Sum {
  repeated NumberDataPoint data_points = 1;
  AggregationTemporality aggregation_temporality = 2;
  bool is_monotonic = 3;
}

enum AggregationTemporality {
  AGGREGATION_TEMPORALITY_UNSPECIFIED = 0;
  AGGREGATION_TEMPORALITY_DELTA = 1;
  AGGREGATION_TEMPORALITY_CUMULATIVE = 2;
}
```

### 4.4 Histogram

```protobuf
message Histogram {
  repeated HistogramDataPoint data_points = 1;
  AggregationTemporality aggregation_temporality = 2;
}

message HistogramDataPoint {
  repeated KeyValue attributes = 1;
  fixed64 start_time_unix_nano = 2;
  fixed64 time_unix_nano = 3;
  uint64 count = 4;
  double sum = 5;
  repeated double bucket_counts = 6;
  repeated double explicit_bounds = 7;
  repeated Exemplar exemplars = 8;
  uint32 flags = 9;
  double min = 10;
  double max = 11;
}
```

## 5. 语义约定

### 5.1 HTTP指标

```go
// 请求计数
httpRequestsTotal, _ := meter.Int64Counter(
    "http_requests_total",
    metric.WithDescription("Total HTTP requests"),
    metric.WithUnit("1"),
)

// 请求持续时间
httpRequestDuration, _ := meter.Float64Histogram(
    "http_request_duration_seconds",
    metric.WithDescription("HTTP request duration"),
    metric.WithUnit("s"),
)

// 请求大小
httpRequestSize, _ := meter.Int64Histogram(
    "http_request_size_bytes",
    metric.WithDescription("HTTP request size"),
    metric.WithUnit("By"),
)

// 响应大小
httpResponseSize, _ := meter.Int64Histogram(
    "http_response_size_bytes",
    metric.WithDescription("HTTP response size"),
    metric.WithUnit("By"),
)
```

### 5.2 数据库指标

```go
// 连接数
dbConnections, _ := meter.Int64Gauge(
    "db_connections_active",
    metric.WithDescription("Active database connections"),
    metric.WithUnit("1"),
)

// 查询持续时间
dbQueryDuration, _ := meter.Float64Histogram(
    "db_query_duration_seconds",
    metric.WithDescription("Database query duration"),
    metric.WithUnit("s"),
)

// 查询计数
dbQueriesTotal, _ := meter.Int64Counter(
    "db_queries_total",
    metric.WithDescription("Total database queries"),
    metric.WithUnit("1"),
)
```

### 5.3 系统指标

```go
// CPU使用率
cpuUsage, _ := meter.Float64Gauge(
    "system_cpu_usage",
    metric.WithDescription("CPU usage percentage"),
    metric.WithUnit("1"),
)

// 内存使用
memoryUsage, _ := meter.Int64Gauge(
    "system_memory_usage_bytes",
    metric.WithDescription("Memory usage in bytes"),
    metric.WithUnit("By"),
)

// 磁盘使用
diskUsage, _ := meter.Int64Gauge(
    "system_disk_usage_bytes",
    metric.WithDescription("Disk usage in bytes"),
    metric.WithUnit("By"),
)
```

## 6. 聚合和导出

### 6.1 聚合器类型

```go
// 默认聚合器
meter := global.Meter("example")

// 自定义聚合器
meter := global.Meter("example", metric.WithResource(resource))
```

### 6.2 导出配置

```go
// 创建导出器
exporter, err := otlpmetricgrpc.New(ctx,
    otlpmetricgrpc.WithEndpoint("localhost:4317"),
    otlpmetricgrpc.WithInsecure(),
)

// 创建读取器
reader := metric.NewPeriodicReader(exporter,
    metric.WithInterval(time.Second*10),
    metric.WithTimeout(time.Second*5),
)

// 创建MeterProvider
meterProvider := metric.NewMeterProvider(
    metric.WithReader(reader),
    metric.WithResource(resource),
)
```

## 7. 性能优化

### 7.1 批处理

```go
// 批处理配置
reader := metric.NewPeriodicReader(exporter,
    metric.WithInterval(time.Second*10),
    metric.WithTimeout(time.Second*5),
    metric.WithTemporalitySelector(metric.DefaultTemporalitySelector),
)
```

### 7.2 内存管理

```go
// 限制数据点数量
meterProvider := metric.NewMeterProvider(
    metric.WithReader(reader),
    metric.WithResource(resource),
    metric.WithView(metric.NewView(
        metric.Instrument{Name: "*"},
        metric.Stream{
            AttributeFilter: attribute.NewAllowKeysFilter("method", "status"),
        },
    )),
)
```

## 8. 视图和过滤

### 8.1 视图配置

```go
// 创建视图
view := metric.NewView(
    metric.Instrument{Name: "http_requests_total"},
    metric.Stream{
        Name: "http_requests_total_filtered",
        AttributeFilter: attribute.NewAllowKeysFilter("method", "status"),
    },
)

// 应用视图
meterProvider := metric.NewMeterProvider(
    metric.WithReader(reader),
    metric.WithView(view),
)
```

### 8.2 属性过滤

```go
// 允许特定属性
filter := attribute.NewAllowKeysFilter("method", "status", "endpoint")

// 拒绝特定属性
filter := attribute.NewDenyKeysFilter("user_id", "password")

// 自定义过滤
filter := attribute.NewFilter(func(kv attribute.KeyValue) bool {
    return kv.Key == "method" || kv.Key == "status"
})
```

## 9. 最佳实践

### 9.1 指标命名

```go
// 好的命名
counter, _ := meter.Int64Counter("http_requests_total")
histogram, _ := meter.Float64Histogram("http_request_duration_seconds")
gauge, _ := meter.Int64Gauge("memory_usage_bytes")

// 避免的命名
counter, _ := meter.Int64Counter("requests")
histogram, _ := meter.Float64Histogram("duration")
gauge, _ := meter.Int64Gauge("memory")
```

### 9.2 属性设计

```go
// 好的属性设计
counter.Add(ctx, 1,
    attribute.String("method", "POST"),
    attribute.String("status", "200"),
    attribute.String("endpoint", "/users"),
)

// 避免的属性设计
counter.Add(ctx, 1,
    attribute.String("HTTP_METHOD", "POST"),    // 大写命名
    attribute.String("status_code", "200"),      // 不一致命名
    attribute.String("path", "/users"),          // 缺少命名空间
)
```

### 9.3 单位使用

```go
// 标准单位
counter, _ := meter.Int64Counter("requests_total", metric.WithUnit("1"))
histogram, _ := meter.Float64Histogram("duration_seconds", metric.WithUnit("s"))
gauge, _ := meter.Int64Gauge("memory_bytes", metric.WithUnit("By"))

// 自定义单位
counter, _ := meter.Int64Counter("users_active", metric.WithUnit("users"))
histogram, _ := meter.Float64Histogram("response_size", metric.WithUnit("bytes"))
```

## 10. 监控和告警

### 10.1 Prometheus集成

```yaml
# Prometheus配置
scrape_configs:
- job_name: 'otel-metrics'
  static_configs:
  - targets: ['localhost:9464']
  metrics_path: '/metrics'
```

### 10.2 告警规则

```yaml
# 告警规则
groups:
- name: otel-metrics
  rules:
  - alert: HighErrorRate
    expr: rate(http_requests_total{status="error"}[5m]) > 0.1
    for: 2m
    labels:
      severity: warning
    annotations:
      summary: "High error rate detected"
  
  - alert: HighLatency
    expr: histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m])) > 1
    for: 5m
    labels:
      severity: critical
    annotations:
      summary: "High latency detected"
```

## 11. 故障排除

### 11.1 常见问题

1. **指标丢失**: 检查导出器配置
2. **性能问题**: 检查聚合器配置
3. **内存泄漏**: 检查数据点限制
4. **数据不一致**: 检查时间戳设置

### 11.2 调试工具

```go
// 启用调试日志
import "go.opentelemetry.io/otel/sdk/metric"

meterProvider := metric.NewMeterProvider(
    metric.WithReader(metric.NewPeriodicReader(exporter)),
    metric.WithView(metric.NewView(
        metric.Instrument{Name: "*"},
        metric.Stream{Name: "debug_*"},
    )),
)
```

## 12. 总结

OpenTelemetry Metrics提供了强大的指标收集和监控能力，通过合理的设计和使用，可以实现：

- **性能监控**: 实时监控系统性能指标
- **业务监控**: 跟踪业务关键指标
- **告警系统**: 基于指标设置告警规则
- **容量规划**: 基于历史数据预测容量需求

选择合适的指标类型、设计合理的属性结构、配置适当的聚合策略，是成功实施指标监控的关键。

---

## 2025 指标标准对齐（权威与中性）

- **指标名称长度**: 最大 255 字符（由 63 提升，2025 对齐）。在命名中保持小写+下划线/点号的约定，并结合命名空间（如 `http.request.duration` 或 `http_request_duration_seconds`）确保跨生态可读性。
- **聚合时序（Temporality）**: 建议遵循默认时序选择器（Delta/Cumulative）与后端一致；跨 Prometheus 场景需明确 Delta→Rate、Histogram→*_bucket 的映射关系。
- **直方图策略**: 优先使用常规 Histogram 配合业务自定义边界；高基数、宽量级分布时评估 ExponentialHistogram 的空间效率与查询适配。
- **视图（Views）与属性基数**: 用 Views 限制属性维度与重命名流（Stream），在高基数标签前置做白/黑名单；为热点路径准备降维视图以保护采样与成本。
- **单位标准**: 采用 UCUM（如 `s`, `ms`, `By`, `1`）；名称后缀与 `unit` 保持一致性（例如 `*_seconds` 与 `unit: s`）。
- **示例值（Exemplars）**: 在高阶分析/关联 traces 时启用 Exemplars；注意与采样策略、压缩与导出成本的权衡。
- **导出与重试**: 指标导出遵循 OTLP 可重试/不可重试错误语义，仅对瞬态错误指数退避。
- **成熟实现与建议**:
  - SDK: Go / Java / Python / .NET / Rust 均提供稳定的 Metrics API/SDK 与 OTLP metric exporter（gRPC/HTTP）。
  - Collector: 建议使用稳定版本的 `otlp` receiver + `prometheusremotewrite`/`otlp` exporter；按需启用 `transformprocessor`/`filterprocessor` 控制维度与速率。
  - Prometheus: 通过 Collector 执行 OTLP→Prometheus 的一致性映射；或在边车模式暴露 `:9464`/Prometheus exporter。

权威来源：`opentelemetry.io` 与 GitHub `open-telemetry/*`（specification、proto、collector、各语言 SDK）发布与变更日志。
