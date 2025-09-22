# OpenTelemetry Protocol (OTLP) 规范详解

## 📊 OTLP规范概览

**创建时间**: 2025年1月27日  
**文档版本**: 1.0.0  
**维护者**: OpenTelemetry 2025 标准团队  
**状态**: 活跃开发中  

## 🎯 OTLP规范目标

### 主要目标

1. **协议标准化**: 建立统一的遥测数据协议
2. **数据模型**: 定义标准的数据模型
3. **传输协议**: 支持多种传输协议
4. **互操作性**: 确保系统间互操作性

### 成功标准

- **协议完整性**: 100%完整
- **数据模型**: 标准化
- **传输支持**: 多协议支持
- **互操作性**: 完全互操作

## 🏗️ OTLP协议架构

### 协议层次

```text
应用层
├── 遥测数据 (Traces, Metrics, Logs)
├── 资源信息 (Resource)
└── 属性信息 (Attributes)

协议层
├── OTLP协议定义
├── 数据序列化
└── 消息格式

传输层
├── gRPC传输
├── HTTP传输
└── 其他传输协议

网络层
├── TCP/IP
├── TLS/SSL
└── 其他网络协议
```

### 数据模型

#### 1. 遥测数据模型

```protobuf
// 遥测数据包
message TelemetryData {
  repeated ResourceSpans resource_spans = 1;
  repeated ResourceMetrics resource_metrics = 2;
  repeated ResourceLogs resource_logs = 3;
}

// 资源Span
message ResourceSpans {
  Resource resource = 1;
  repeated ScopeSpans scope_spans = 2;
}

// 资源指标
message ResourceMetrics {
  Resource resource = 1;
  repeated ScopeMetrics scope_metrics = 2;
}

// 资源日志
message ResourceLogs {
  Resource resource = 1;
  repeated ScopeLogs scope_logs = 2;
}
```

#### 2. 资源模型

```protobuf
// 资源信息
message Resource {
  repeated KeyValue attributes = 1;
  uint32 dropped_attributes_count = 2;
}

// 键值对
message KeyValue {
  string key = 1;
  AnyValue value = 2;
}

// 任意值
message AnyValue {
  oneof value {
    string string_value = 1;
    bool bool_value = 2;
    int64 int_value = 3;
    double double_value = 4;
    ArrayValue array_value = 5;
    KeyValueList kvlist_value = 6;
    bytes bytes_value = 7;
  }
}
```

#### 3. 追踪数据模型

```protobuf
// Span
message Span {
  bytes trace_id = 1;
  bytes span_id = 2;
  string trace_state = 3;
  bytes parent_span_id = 4;
  string name = 5;
  SpanKind kind = 6;
  fixed64 start_time_unix_nano = 7;
  fixed64 end_time_unix_nano = 8;
  repeated KeyValue attributes = 9;
  uint32 dropped_attributes_count = 10;
  repeated Event events = 11;
  uint32 dropped_events_count = 12;
  repeated Link links = 13;
  uint32 dropped_links_count = 14;
  Status status = 15;
}

// Span类型
enum SpanKind {
  SPAN_KIND_UNSPECIFIED = 0;
  SPAN_KIND_INTERNAL = 1;
  SPAN_KIND_SERVER = 2;
  SPAN_KIND_CLIENT = 3;
  SPAN_KIND_PRODUCER = 4;
  SPAN_KIND_CONSUMER = 5;
}
```

#### 4. 指标数据模型

```protobuf
// 指标
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

// 仪表
message Gauge {
  repeated NumberDataPoint data_points = 1;
}

// 求和
message Sum {
  repeated NumberDataPoint data_points = 1;
  AggregationTemporality aggregation_temporality = 2;
  bool is_monotonic = 3;
}

// 直方图
message Histogram {
  repeated HistogramDataPoint data_points = 1;
  AggregationTemporality aggregation_temporality = 2;
}
```

#### 5. 日志数据模型

```protobuf
// 日志记录
message LogRecord {
  fixed64 time_unix_nano = 1;
  fixed64 observed_time_unix_nano = 2;
  SeverityNumber severity_number = 3;
  string severity_text = 4;
  AnyValue body = 5;
  repeated KeyValue attributes = 6;
  uint32 dropped_attributes_count = 7;
  uint32 flags = 8;
  bytes trace_id = 9;
  bytes span_id = 10;
}

// 严重程度
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

## 🔧 传输协议

### 1. gRPC传输

#### 服务定义

```protobuf
service TraceService {
  rpc Export(ExportTraceServiceRequest) returns (ExportTraceServiceResponse);
}

service MetricsService {
  rpc Export(ExportMetricsServiceRequest) returns (ExportMetricsServiceResponse);
}

service LogsService {
  rpc Export(ExportLogsServiceRequest) returns (ExportLogsServiceResponse);
}
```

#### 请求/响应格式

```protobuf
// 导出追踪请求
message ExportTraceServiceRequest {
  repeated ResourceSpans resource_spans = 1;
}

// 导出追踪响应
message ExportTraceServiceResponse {
  ExportTracePartialSuccess partial_success = 1;
}

// 导出指标请求
message ExportMetricsServiceRequest {
  repeated ResourceMetrics resource_metrics = 1;
}

// 导出指标响应
message ExportMetricsServiceResponse {
  ExportMetricsPartialSuccess partial_success = 1;
}

// 导出日志请求
message ExportLogsServiceRequest {
  repeated ResourceLogs resource_logs = 1;
}

// 导出日志响应
message ExportLogsServiceResponse {
  ExportLogsPartialSuccess partial_success = 1;
}
```

### 2. HTTP传输

#### 端点定义

```text
POST /v1/traces
POST /v1/metrics
POST /v1/logs
```

#### 请求格式

```http
POST /v1/traces HTTP/1.1
Host: collector.example.com
Content-Type: application/x-protobuf
Content-Encoding: gzip

[Binary protobuf data]
```

#### 响应格式

```http
HTTP/1.1 200 OK
Content-Type: application/json

{
  "partialSuccess": {
    "rejectedSpans": 0,
    "errorMessage": ""
  }
}
```

## 📊 语义约定

### 1. 资源语义约定

#### 服务信息

```text
service.name: 服务名称
service.version: 服务版本
service.instance.id: 服务实例ID
service.namespace: 服务命名空间
```

#### 部署信息

```text
deployment.environment: 部署环境
deployment.version: 部署版本
deployment.name: 部署名称
```

#### 主机信息

```text
host.name: 主机名称
host.id: 主机ID
host.type: 主机类型
host.arch: 主机架构
```

### 2. 追踪语义约定

#### HTTP请求

```text
http.method: HTTP方法
http.url: HTTP URL
http.status_code: HTTP状态码
http.request.header.*: HTTP请求头
http.response.header.*: HTTP响应头
```

#### 数据库操作

```text
db.system: 数据库系统
db.name: 数据库名称
db.operation: 数据库操作
db.sql.table: SQL表名
db.redis.database_index: Redis数据库索引
```

#### RPC调用

```text
rpc.system: RPC系统
rpc.service: RPC服务
rpc.method: RPC方法
rpc.grpc.status_code: gRPC状态码
```

### 3. 指标语义约定

#### 系统指标

```text
system.cpu.usage: CPU使用率
system.memory.usage: 内存使用量
system.disk.io: 磁盘I/O
system.network.io: 网络I/O
```

#### 应用指标

```text
http.server.request.duration: HTTP请求持续时间
http.server.request.size: HTTP请求大小
http.server.response.size: HTTP响应大小
```

### 4. 日志语义约定

#### 日志级别

```text
log.level: 日志级别
log.message: 日志消息
log.source: 日志来源
log.timestamp: 日志时间戳
```

#### 错误信息

```text
error.name: 错误名称
error.message: 错误消息
error.stack: 错误堆栈
error.type: 错误类型
```

## 🚀 实施指南

### 1. 客户端实现

#### 基本配置

```yaml
exporters:
  otlp:
    endpoint: http://localhost:4317
    protocol: grpc
    headers:
      api-key: "your-api-key"
    compression: gzip
    timeout: 30s
    retry:
      enabled: true
      initial_interval: 1s
      max_interval: 5s
      max_elapsed_time: 30s
```

#### 高级配置

```yaml
exporters:
  otlp:
    endpoint: https://collector.example.com:4317
    protocol: grpc
    tls:
      insecure: false
      cert_file: /path/to/cert.pem
      key_file: /path/to/key.pem
      ca_file: /path/to/ca.pem
    headers:
      authorization: "Bearer your-token"
    compression: gzip
    timeout: 30s
    retry:
      enabled: true
      initial_interval: 1s
      max_interval: 5s
      max_elapsed_time: 30s
      max_retries: 5
```

### 2. 服务端实现

#### 收集器配置

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318

processors:
  batch:
    timeout: 1s
    send_batch_size: 1024
    send_batch_max_size: 2048

exporters:
  jaeger:
    endpoint: jaeger:14250
    tls:
      insecure: true

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [jaeger]
```

### 3. 错误处理

#### 客户端错误处理

```go
func handleExportError(err error) {
    if err != nil {
        switch {
        case errors.Is(err, context.DeadlineExceeded):
            log.Warn("Export timeout")
        case errors.Is(err, context.Canceled):
            log.Warn("Export canceled")
        default:
            log.Error("Export failed", "error", err)
        }
    }
}
```

#### 服务端错误处理

```go
func (s *Server) ExportTraces(ctx context.Context, req *pb.ExportTraceServiceRequest) (*pb.ExportTraceServiceResponse, error) {
    if err := s.validateRequest(req); err != nil {
        return &pb.ExportTraceServiceResponse{
            PartialSuccess: &pb.ExportTracePartialSuccess{
                RejectedSpans: int64(len(req.ResourceSpans)),
                ErrorMessage:  err.Error(),
            },
        }, nil
    }
    
    // 处理请求
    return &pb.ExportTraceServiceResponse{}, nil
}
```

## 📊 性能优化

### 1. 批处理优化

#### 批处理配置

```yaml
processors:
  batch:
    timeout: 1s
    send_batch_size: 1024
    send_batch_max_size: 2048
    metadata_keys:
      - "service.name"
      - "service.version"
```

#### 内存优化

```yaml
processors:
  memory_limiter:
    limit_mib: 512
    spike_limit_mib: 128
    check_interval: 5s
```

### 2. 压缩优化

#### 压缩配置

```yaml
exporters:
  otlp:
    compression: gzip
    compression_level: 6
```

#### 网络优化

```yaml
exporters:
  otlp:
    endpoint: https://collector.example.com:4317
    protocol: grpc
    keepalive:
      time: 30s
      timeout: 5s
      permit_without_stream: true
```

### 3. 重试优化

#### 重试配置

```yaml
exporters:
  otlp:
    retry:
      enabled: true
      initial_interval: 1s
      max_interval: 5s
      max_elapsed_time: 30s
      max_retries: 5
      multiplier: 2.0
```

## 🎉 总结

通过建立完整的OTLP规范体系，OpenTelemetry项目将：

1. **协议标准化**: 建立统一的遥测数据协议
2. **数据模型**: 定义标准的数据模型
3. **传输协议**: 支持多种传输协议
4. **互操作性**: 确保系统间互操作性

这个OTLP规范体系将显著提升遥测数据的标准化和互操作性，为OpenTelemetry生态系统的发展奠定坚实基础。

---

**OTLP规范建立时间**: 2025年1月27日  
**文档版本**: 1.0.0  
**维护者**: OpenTelemetry 2025 标准团队  
**下次审查**: 2025年2月27日
