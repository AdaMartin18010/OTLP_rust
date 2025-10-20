# OpenTelemetry Logs 规范

## 📋 目录

- [OpenTelemetry Logs 规范](#opentelemetry-logs-规范)
  - [📋 目录](#-目录)
  - [📊 OpenTelemetry Logs 规范概览](#-opentelemetry-logs-规范概览)
  - [🎯 OpenTelemetry Logs 规范目标](#-opentelemetry-logs-规范目标)
    - [主要目标](#主要目标)
    - [成功标准](#成功标准)
  - [概述](#概述)
  - [核心概念](#核心概念)
    - [LogRecord](#logrecord)
    - [Severity](#severity)
    - [LogBody](#logbody)
  - [数据模型](#数据模型)
    - [LogRecord结构](#logrecord结构)
    - [严重级别](#严重级别)
  - [语义约定](#语义约定)
    - [日志属性](#日志属性)
    - [错误日志](#错误日志)
    - [业务日志](#业务日志)
  - [日志框架集成](#日志框架集成)
    - [Log4j集成](#log4j集成)
    - [Logback集成](#logback集成)
    - [Python Logging集成](#python-logging集成)
  - [结构化日志](#结构化日志)
    - [JSON格式](#json格式)
    - [键值对格式](#键值对格式)
  - [日志关联](#日志关联)
    - [与Trace关联](#与trace关联)
    - [与Metrics关联](#与metrics关联)
  - [日志处理](#日志处理)
    - [过滤和转换](#过滤和转换)
    - [采样策略](#采样策略)
  - [性能优化](#性能优化)
    - [异步处理](#异步处理)
    - [批处理](#批处理)
  - [最佳实践](#最佳实践)
    - [1. 日志级别使用](#1-日志级别使用)
    - [2. 结构化日志](#2-结构化日志)
    - [3. 敏感信息处理](#3-敏感信息处理)
  - [监控和告警](#监控和告警)
    - [日志指标](#日志指标)
    - [告警规则](#告警规则)
  - [故障排除](#故障排除)
    - [常见问题](#常见问题)
    - [调试工具](#调试工具)
  - [总结](#总结)

## 📊 OpenTelemetry Logs 规范概览

**创建时间**: 2025年09月22日  
**文档版本**: 2.0.0  
**维护者**: OpenTelemetry 2025 团队  
**状态**: 知识理论模型分析梳理项目  
**OpenTelemetry Logs 规范范围**: OpenTelemetry Logs 规范分析

## 🎯 OpenTelemetry Logs 规范目标

### 主要目标

1. **目标1**: 实现OpenTelemetry Logs 规范的核心功能
2. **目标2**: 确保OpenTelemetry Logs 规范的质量和可靠性
3. **目标3**: 提供OpenTelemetry Logs 规范的完整解决方案
4. **目标4**: 建立OpenTelemetry Logs 规范的最佳实践
5. **目标5**: 推动OpenTelemetry Logs 规范的持续改进

### 成功标准

- **标准1**: 100%功能实现
- **标准2**: 高质量标准达成
- **标准3**: 完整解决方案提供
- **标准4**: 最佳实践建立
- **标准5**: 持续改进机制

## 概述

日志（Logs）是OpenTelemetry的三大信号之一，用于记录应用程序的运行时信息、错误和调试信息。

## 核心概念

### LogRecord

- **定义**: 表示一个日志记录
- **内容**: 时间戳、严重级别、消息、属性
- **关联**: 可以与Trace和Span关联

### Severity

- **定义**: 日志的严重级别
- **标准**: 遵循RFC 5424标准
- **映射**: 支持多种日志框架

### LogBody

- **定义**: 日志的主体内容
- **类型**: 支持字符串、结构化数据
- **格式**: 支持多种格式

## 数据模型

### LogRecord结构

```protobuf
message LogRecord {
  fixed64 time_unix_nano = 1;                    // 时间戳
  fixed64 observed_time_unix_nano = 2;           // 观察时间
  SeverityNumber severity_number = 3;            // 严重级别数字
  string severity_text = 4;                      // 严重级别文本
  AnyValue body = 5;                             // 日志主体
  repeated KeyValue attributes = 6;              // 属性
  uint32 dropped_attributes_count = 7;           // 丢弃的属性数量
  uint32 flags = 8;                              // 标志位
  bytes trace_id = 9;                            // 关联的TraceId
  bytes span_id = 10;                            // 关联的SpanId
}
```

### 严重级别

```protobuf
enum SeverityNumber {
  SEVERITY_NUMBER_UNSPECIFIED = 0;
  SEVERITY_NUMBER_TRACE = 1;
  SEVERITY_NUMBER_TRACE2 = 2;
  SEVERITY_NUMBER_TRACE3 = 3;
  SEVERITY_NUMBER_TRACE4 = 4;
  SEVERITY_NUMBER_DEBUG = 5;
  SEVERITY_NUMBER_DEBUG2 = 6;
  SEVERITY_NUMBER_DEBUG3 = 7;
  SEVERITY_NUMBER_DEBUG4 = 8;
  SEVERITY_NUMBER_INFO = 9;
  SEVERITY_NUMBER_INFO2 = 10;
  SEVERITY_NUMBER_INFO3 = 11;
  SEVERITY_NUMBER_INFO4 = 12;
  SEVERITY_NUMBER_WARN = 13;
  SEVERITY_NUMBER_WARN2 = 14;
  SEVERITY_NUMBER_WARN3 = 15;
  SEVERITY_NUMBER_WARN4 = 16;
  SEVERITY_NUMBER_ERROR = 17;
  SEVERITY_NUMBER_ERROR2 = 18;
  SEVERITY_NUMBER_ERROR3 = 19;
  SEVERITY_NUMBER_ERROR4 = 20;
  SEVERITY_NUMBER_FATAL = 21;
  SEVERITY_NUMBER_FATAL2 = 22;
  SEVERITY_NUMBER_FATAL3 = 23;
  SEVERITY_NUMBER_FATAL4 = 24;
}
```

## 语义约定

### 日志属性

```go
// 标准日志属性
attribute.String("log.level", "INFO")
attribute.String("log.message", "User login successful")
attribute.String("log.logger", "com.example.UserService")
attribute.String("log.thread", "main")
attribute.String("log.source", "UserService.java:123")
```

### 错误日志

```go
// 错误相关属性
attribute.String("error.type", "java.lang.NullPointerException")
attribute.String("error.message", "Cannot invoke method on null object")
attribute.String("error.stacktrace", "java.lang.NullPointerException...")
attribute.Bool("error.retryable", false)
```

### 业务日志

```go
// 业务相关属性
attribute.String("user.id", "12345")
attribute.String("user.email", "user@example.com")
attribute.String("action", "login")
attribute.String("resource", "/api/users")
attribute.String("result", "success")
```

## 日志框架集成

### Log4j集成

```xml
<!-- Log4j配置 -->
<Configuration>
    <Appenders>
        <Console name="Console" target="SYSTEM_OUT">
            <PatternLayout pattern="%d{HH:mm:ss.SSS} [%t] %-5level %logger{36} - %msg%n"/>
        </Console>
        <OtlpAppender name="OtlpAppender">
            <Endpoint>http://localhost:4317</Endpoint>
        </OtlpAppender>
    </Appenders>
    <Loggers>
        <Root level="INFO">
            <AppenderRef ref="Console"/>
            <AppenderRef ref="OtlpAppender"/>
        </Root>
    </Loggers>
</Configuration>
```

### Logback集成

```xml
<!-- Logback配置 -->
<configuration>
    <appender name="STDOUT" class="ch.qos.logback.core.ConsoleAppender">
        <encoder>
            <pattern>%d{HH:mm:ss.SSS} [%thread] %-5level %logger{36} - %msg%n</pattern>
        </encoder>
    </appender>
    
    <appender name="OTLP" class="io.opentelemetry.instrumentation.logback.appender.v1_0.OpenTelemetryAppender">
        <endpoint>http://localhost:4317</endpoint>
    </appender>
    
    <root level="INFO">
        <appender-ref ref="STDOUT"/>
        <appender-ref ref="OTLP"/>
    </root>
</configuration>
```

### Python Logging集成

```python
import logging
from opentelemetry.instrumentation.logging import LoggingInstrumentor

# 启用日志检测
LoggingInstrumentor().instrument()

# 配置日志
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# 使用日志
logger.info("User login successful", extra={
    "user_id": "12345",
    "action": "login"
})
```

## 结构化日志

### JSON格式

```json
{
  "timestamp": "2023-12-01T10:30:00.000Z",
  "level": "INFO",
  "message": "User login successful",
  "logger": "com.example.UserService",
  "thread": "main",
  "attributes": {
    "user.id": "12345",
    "user.email": "user@example.com",
    "action": "login",
    "result": "success"
  },
  "trace_id": "1234567890abcdef",
  "span_id": "abcdef1234567890"
}
```

### 键值对格式

```text
timestamp=2023-12-01T10:30:00.000Z level=INFO message="User login successful" logger=com.example.UserService thread=main user.id=12345 user.email=user@example.com action=login result=success trace_id=1234567890abcdef span_id=abcdef1234567890
```

## 日志关联

### 与Trace关联

```go
// 在Span上下文中记录日志
func handleRequest(ctx context.Context, req *Request) {
    ctx, span := tracer.Start(ctx, "handleRequest")
    defer span.End()
    
    // 记录日志，自动关联TraceId和SpanId
    logger.InfoContext(ctx, "Processing request",
        "request.id", req.ID,
        "request.type", req.Type,
    )
    
    // 处理请求
    err := processRequest(ctx, req)
    if err != nil {
        logger.ErrorContext(ctx, "Request processing failed",
            "error", err,
            "request.id", req.ID,
        )
        span.RecordError(err)
        return
    }
    
    logger.InfoContext(ctx, "Request processed successfully",
        "request.id", req.ID,
    )
}
```

### 与Metrics关联

```go
// 记录业务指标
func recordBusinessMetric(ctx context.Context, action string, result string) {
    // 记录指标
    businessCounter.Add(ctx, 1,
        attribute.String("action", action),
        attribute.String("result", result),
    )
    
    // 记录日志
    logger.InfoContext(ctx, "Business action completed",
        "action", action,
        "result", result,
    )
}
```

## 日志处理

### 过滤和转换

```go
// 日志处理器
type LogProcessor struct {
    filters []LogFilter
    transformers []LogTransformer
}

type LogFilter interface {
    Filter(record LogRecord) bool
}

type LogTransformer interface {
    Transform(record LogRecord) LogRecord
}

// 实现过滤器
type SeverityFilter struct {
    minLevel SeverityNumber
}

func (f *SeverityFilter) Filter(record LogRecord) bool {
    return record.SeverityNumber >= f.minLevel
}

// 实现转换器
type AttributeTransformer struct {
    attributes map[string]string
}

func (t *AttributeTransformer) Transform(record LogRecord) LogRecord {
    for key, value := range t.attributes {
        record.Attributes = append(record.Attributes, 
            attribute.String(key, value))
    }
    return record
}
```

### 采样策略

```go
// 日志采样器
type LogSampler interface {
    ShouldSample(record LogRecord) bool
}

// 基于严重级别的采样
type SeveritySampler struct {
    levels map[SeverityNumber]float64
}

func (s *SeveritySampler) ShouldSample(record LogRecord) bool {
    rate, exists := s.levels[record.SeverityNumber]
    if !exists {
        return false
    }
    return rand.Float64() < rate
}

// 基于属性的采样
type AttributeSampler struct {
    key    string
    values map[string]float64
}

func (s *AttributeSampler) ShouldSample(record LogRecord) bool {
    for _, attr := range record.Attributes {
        if string(attr.Key) == s.key {
            if rate, exists := s.values[attr.Value.AsString()]; exists {
                return rand.Float64() < rate
            }
        }
    }
    return false
}
```

## 性能优化

### 异步处理

```go
// 异步日志处理器
type AsyncLogProcessor struct {
    queue chan LogRecord
    workers int
}

func (p *AsyncLogProcessor) Process(record LogRecord) {
    select {
    case p.queue <- record:
        // 成功入队
    default:
        // 队列满，丢弃日志
        logDroppedCounter.Add(context.Background(), 1)
    }
}

func (p *AsyncLogProcessor) worker() {
    for record := range p.queue {
        p.processRecord(record)
    }
}
```

### 批处理

```go
// 批处理日志导出器
type BatchLogExporter struct {
    batchSize int
    timeout   time.Duration
    records   []LogRecord
    mutex     sync.Mutex
}

func (e *BatchLogExporter) Export(record LogRecord) {
    e.mutex.Lock()
    defer e.mutex.Unlock()
    
    e.records = append(e.records, record)
    
    if len(e.records) >= e.batchSize {
        e.flush()
    }
}

func (e *BatchLogExporter) flush() {
    if len(e.records) == 0 {
        return
    }
    
    // 导出批次
    e.exportBatch(e.records)
    e.records = e.records[:0]
}
```

## 最佳实践

### 1. 日志级别使用

```go
// 正确的级别使用
logger.Trace("Detailed debugging information")
logger.Debug("Debug information for development")
logger.Info("General information about application flow")
logger.Warn("Warning about potential issues")
logger.Error("Error occurred but application can continue")
logger.Fatal("Critical error, application cannot continue")
```

### 2. 结构化日志

```go
// 好的结构化日志
logger.Info("User action completed",
    "user.id", userID,
    "action", action,
    "result", result,
    "duration_ms", duration.Milliseconds(),
)

// 避免的非结构化日志
logger.Info(fmt.Sprintf("User %s completed action %s with result %s in %dms", 
    userID, action, result, duration.Milliseconds()))
```

### 3. 敏感信息处理

```go
// 敏感信息脱敏
func sanitizeLogRecord(record LogRecord) LogRecord {
    for i, attr := range record.Attributes {
        if isSensitive(attr.Key) {
            record.Attributes[i] = attribute.String(string(attr.Key), "[REDACTED]")
        }
    }
    return record
}

func isSensitive(key attribute.Key) bool {
    sensitiveKeys := []string{
        "password", "token", "secret", "key",
        "credit_card", "ssn", "email", "phone",
    }
    
    keyStr := string(key)
    for _, sensitive := range sensitiveKeys {
        if strings.Contains(strings.ToLower(keyStr), sensitive) {
            return true
        }
    }
    return false
}
```

## 监控和告警

### 日志指标

```go
// 日志相关指标
logCount, _ := meter.Int64Counter("logs_total")
logDropped, _ := meter.Int64Counter("logs_dropped_total")
logProcessingDuration, _ := meter.Float64Histogram("log_processing_duration_seconds")
```

### 告警规则

```yaml
# 基于日志的告警
groups:
- name: log-alerts
  rules:
  - alert: HighErrorLogRate
    expr: rate(logs_total{level="ERROR"}[5m]) > 10
    for: 2m
    labels:
      severity: warning
    annotations:
      summary: "High error log rate detected"
  
  - alert: LogProcessingLatency
    expr: histogram_quantile(0.95, rate(log_processing_duration_seconds_bucket[5m])) > 0.1
    for: 5m
    labels:
      severity: critical
    annotations:
      summary: "High log processing latency"
```

## 故障排除

### 常见问题

1. **日志丢失**: 检查采样配置和队列大小
2. **性能问题**: 检查异步处理和批处理配置
3. **格式问题**: 检查结构化日志格式
4. **关联问题**: 检查TraceId和SpanId设置

### 调试工具

```go
// 启用调试日志
import "go.opentelemetry.io/otel/sdk/log"

loggerProvider := log.NewLoggerProvider(
    log.WithProcessor(log.NewBatchProcessor(exporter)),
    log.WithResource(resource),
)
```

## 总结

OpenTelemetry Logs提供了强大的日志收集和处理能力，通过合理的配置和使用，可以实现：

- **统一日志格式**: 跨语言、跨框架的一致性
- **日志关联**: 与Trace和Metrics的关联
- **结构化日志**: 便于查询和分析
- **性能优化**: 异步处理和批处理

---

**文档创建完成时间**: 2025年09月22日  
**文档版本**: 2.0.0  
**维护者**: OpenTelemetry 2025 团队  
**下次审查**: 2025年10月22日
