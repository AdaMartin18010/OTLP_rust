# 🦀 Collector配置速查手册 - Rust应用视角

> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **Collector版本**: 0.115.0+  
> **最后更新**: 2025年10月11日

---

## 📋 快速索引

- [🦀 Collector配置速查手册 - Rust应用视角](#-collector配置速查手册---rust应用视角)
  - [📋 快速索引](#-快速索引)
  - [⚙️ 基础配置](#️-基础配置)
    - [最小化配置](#最小化配置)
    - [Rust应用连接](#rust应用连接)
  - [📥 Receivers配置](#-receivers配置)
    - [OTLP Receiver (推荐Rust)](#otlp-receiver-推荐rust)
    - [Prometheus Receiver (for Metrics)](#prometheus-receiver-for-metrics)
  - [🔧 Processors配置](#-processors配置)
    - [Batch Processor (必需)](#batch-processor-必需)
    - [Memory Limiter (生产必需)](#memory-limiter-生产必需)
    - [Resource Processor](#resource-processor)
    - [Attributes Processor](#attributes-processor)
    - [Tail Sampling Processor](#tail-sampling-processor)
  - [📤 Exporters配置](#-exporters配置)
    - [OTLP Exporter (转发)](#otlp-exporter-转发)
    - [云平台Exporters](#云平台exporters)
      - [阿里云SLS](#阿里云sls)
      - [腾讯云CLS](#腾讯云cls)
      - [华为云LTS](#华为云lts)
    - [Prometheus Remote Write](#prometheus-remote-write)
  - [🔄 Pipelines配置](#-pipelines配置)
    - [Traces Pipeline](#traces-pipeline)
    - [Metrics Pipeline](#metrics-pipeline)
    - [Logs Pipeline](#logs-pipeline)
  - [🎯 常见场景配置](#-常见场景配置)
    - [场景1: 生产环境 - 高性能](#场景1-生产环境---高性能)
    - [场景2: 开发环境 - 调试友好](#场景2-开发环境---调试友好)
    - [场景3: 混合云 - 多后端](#场景3-混合云---多后端)
  - [🔒 安全配置](#-安全配置)
    - [TLS双向认证](#tls双向认证)
  - [📊 监控Collector本身](#-监控collector本身)
    - [Health Check](#health-check)
    - [Prometheus Metrics](#prometheus-metrics)
  - [🐳 Docker Compose示例](#-docker-compose示例)
  - [🔍 故障诊断](#-故障诊断)
    - [开启详细日志](#开启详细日志)
    - [常见问题](#常见问题)
      - [1. 数据丢失](#1-数据丢失)
      - [2. 内存占用高](#2-内存占用高)
      - [3. 连接超时](#3-连接超时)
  - [📚 参考资源](#-参考资源)

---

## ⚙️ 基础配置

### 最小化配置

```yaml
# otelcol-config.yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318

processors:
  batch:
    timeout: 10s
    send_batch_size: 1024

exporters:
  logging:
    loglevel: info

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [logging]
```

### Rust应用连接

```rust
use opentelemetry_otlp::SpanExporter;

let exporter = SpanExporter::builder()
    .with_tonic()
    .with_endpoint("http://localhost:4317") // gRPC
    .build()?;

// 或使用HTTP
let exporter = SpanExporter::builder()
    .with_http()
    .with_endpoint("http://localhost:4318/v1/traces") // HTTP
    .build()?;
```

---

## 📥 Receivers配置

### OTLP Receiver (推荐Rust)

```yaml
receivers:
  otlp:
    protocols:
      # gRPC协议 (推荐)
      grpc:
        endpoint: 0.0.0.0:4317
        max_recv_msg_size_mib: 4  # 4MB
        max_concurrent_streams: 100
        read_buffer_size: 524288
        write_buffer_size: 524288
        
        # TLS配置
        tls:
          cert_file: /path/to/cert.pem
          key_file: /path/to/key.pem
          client_ca_file: /path/to/ca.pem
      
      # HTTP协议
      http:
        endpoint: 0.0.0.0:4318
        cors:
          allowed_origins:
            - http://localhost:*
            - https://app.example.com
```

**Rust客户端配置**:

```rust
// gRPC + TLS
let exporter = SpanExporter::builder()
    .with_tonic()
    .with_endpoint("https://collector.example.com:4317")
    .with_tls_config(
        tonic::transport::ClientTlsConfig::new()
            .ca_certificate(tonic::transport::Certificate::from_pem(ca_cert))
            .domain_name("collector.example.com")
    )
    .build()?;
```

### Prometheus Receiver (for Metrics)

```yaml
receivers:
  prometheus:
    config:
      scrape_configs:
        - job_name: 'rust-app'
          scrape_interval: 30s
          static_configs:
            - targets: ['localhost:9090']
```

---

## 🔧 Processors配置

### Batch Processor (必需)

```yaml
processors:
  batch:
    # 超时时间
    timeout: 10s
    
    # 批次大小
    send_batch_size: 1024
    send_batch_max_size: 2048
```

**Rust端对应配置**:

```rust
use opentelemetry_sdk::trace::Config;

let config = Config::default()
    .with_max_export_batch_size(1024)
    .with_max_queue_size(2048);
```

### Memory Limiter (生产必需)

```yaml
processors:
  memory_limiter:
    check_interval: 1s
    limit_mib: 512      # 软限制
    spike_limit_mib: 128 # 硬限制
```

### Resource Processor

```yaml
processors:
  resource:
    attributes:
      - key: environment
        value: production
        action: insert
      - key: cluster
        value: us-west-2
        action: upsert
```

**Rust端设置Resource**:

```rust
use opentelemetry_sdk::Resource;

let resource = Resource::new(vec![
    KeyValue::new("environment", "production"),
    KeyValue::new("cluster", "us-west-2"),
]);
```

### Attributes Processor

```yaml
processors:
  attributes:
    actions:
      # 删除敏感信息
      - key: http.request.header.authorization
        action: delete
      
      # 重命名
      - key: db.instance
        from_attribute: db.name
        action: update
      
      # 提取值
      - key: http.url
        pattern: ^(?P<http_protocol>.*):\/\/(?P<http_domain>.*)\/
        action: extract
```

### Tail Sampling Processor

```yaml
processors:
  tail_sampling:
    decision_wait: 10s
    num_traces: 1000
    policies:
      # 100%采样错误
      - name: error-traces
        type: status_code
        status_code:
          status_codes: [ERROR]
      
      # 10%采样正常请求
      - name: probabilistic-policy
        type: probabilistic
        probabilistic:
          sampling_percentage: 10
      
      # 100%采样慢请求
      - name: latency-policy
        type: latency
        latency:
          threshold_ms: 1000
```

---

## 📤 Exporters配置

### OTLP Exporter (转发)

```yaml
exporters:
  otlp:
    endpoint: backend-collector:4317
    compression: gzip
    timeout: 30s
    
    # 重试配置
    retry_on_failure:
      enabled: true
      initial_interval: 5s
      max_interval: 30s
      max_elapsed_time: 300s
    
    # 队列配置
    sending_queue:
      enabled: true
      num_consumers: 10
      queue_size: 5000
```

### 云平台Exporters

#### 阿里云SLS

```yaml
exporters:
  alibabacloud_logservice/sls:
    endpoint: "cn-hangzhou.log.aliyuncs.com"
    project: "my-otlp-project"
    logstore: "otlp-traces"
    access_key_id: "${ALIYUN_ACCESS_KEY_ID}"
    access_key_secret: "${ALIYUN_ACCESS_KEY_SECRET}"
```

**Rust直连配置**:

```rust
let mut metadata = tonic::metadata::MetadataMap::new();
metadata.insert("x-log-apiversion", "0.6.0".parse()?);
metadata.insert("Authorization", format!(
    "ACS {}:{}", access_key_id, signature
).parse()?);

let exporter = SpanExporter::builder()
    .with_endpoint("https://cn-hangzhou.log.aliyuncs.com/v1/traces")
    .with_metadata(metadata)
    .build()?;
```

#### 腾讯云CLS

```yaml
exporters:
  tencentcloud_cls:
    endpoint: "ap-guangzhou.cls.tencentcs.com"
    secret_id: "${TENCENT_SECRET_ID}"
    secret_key: "${TENCENT_SECRET_KEY}"
    topic_id: "xxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx"
```

#### 华为云LTS

```yaml
exporters:
  huaweicloud_lts:
    endpoint: "lts.cn-north-4.myhuaweicloud.com"
    access_key: "${HUAWEI_ACCESS_KEY}"
    secret_key: "${HUAWEI_SECRET_KEY}"
    project_id: "xxxxxxxxxxxxxxxxxxxx"
    log_group_id: "xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx"
    log_stream_id: "xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx"
```

### Prometheus Remote Write

```yaml
exporters:
  prometheusremotewrite:
    endpoint: "https://prometheus.example.com/api/v1/write"
    compression: snappy
    
    headers:
      Authorization: "Bearer ${PROMETHEUS_TOKEN}"
    
    resource_to_telemetry_conversion:
      enabled: true
```

---

## 🔄 Pipelines配置

### Traces Pipeline

```yaml
service:
  pipelines:
    traces:
      receivers: [otlp]
      processors:
        - memory_limiter
        - resource
        - batch
        - tail_sampling
      exporters:
        - otlp
        - alibabacloud_logservice/sls
```

### Metrics Pipeline

```yaml
service:
  pipelines:
    metrics:
      receivers: [otlp, prometheus]
      processors:
        - memory_limiter
        - batch
        - resource
      exporters:
        - prometheusremotewrite
        - otlp
```

### Logs Pipeline

```yaml
service:
  pipelines:
    logs:
      receivers: [otlp]
      processors:
        - memory_limiter
        - batch
        - attributes  # 删除敏感信息
      exporters:
        - alibabacloud_logservice/sls
```

---

## 🎯 常见场景配置

### 场景1: 生产环境 - 高性能

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        max_concurrent_streams: 500

processors:
  memory_limiter:
    limit_mib: 1024
    spike_limit_mib: 256
  
  batch:
    timeout: 5s
    send_batch_size: 2048
    send_batch_max_size: 4096
  
  tail_sampling:
    decision_wait: 10s
    policies:
      - name: errors
        type: status_code
        status_code: {status_codes: [ERROR]}
      - name: slow
        type: latency
        latency: {threshold_ms: 1000}
      - name: probabilistic
        type: probabilistic
        probabilistic: {sampling_percentage: 5}

exporters:
  otlp:
    endpoint: backend:4317
    compression: gzip
    sending_queue:
      queue_size: 10000
      num_consumers: 20

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, batch, tail_sampling]
      exporters: [otlp]
```

**Rust应用配置**:

```rust
let exporter = SpanExporter::builder()
    .with_endpoint("http://collector:4317")
    .with_compression(tonic::codec::CompressionEncoding::Gzip)
    .build()?;

let config = Config::default()
    .with_max_export_batch_size(2048)
    .with_max_queue_size(10000);
```

### 场景2: 开发环境 - 调试友好

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318
        cors:
          allowed_origins: ["*"]

processors:
  batch:
    timeout: 1s  # 快速导出

exporters:
  logging:
    loglevel: debug
    sampling_initial: 5
    sampling_thereafter: 200

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [logging]
```

### 场景3: 混合云 - 多后端

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317

processors:
  memory_limiter:
    limit_mib: 512
  
  batch:
    timeout: 10s
    send_batch_size: 1024

exporters:
  # 阿里云
  alibabacloud_logservice/aliyun:
    endpoint: "cn-hangzhou.log.aliyuncs.com"
    project: "prod-otlp"
    logstore: "traces"
    access_key_id: "${ALIYUN_AK}"
    access_key_secret: "${ALIYUN_SK}"
  
  # 腾讯云
  tencentcloud_cls/tencent:
    endpoint: "ap-guangzhou.cls.tencentcs.com"
    secret_id: "${TENCENT_ID}"
    secret_key: "${TENCENT_KEY}"
    topic_id: "${TENCENT_TOPIC}"
  
  # 本地Jaeger
  otlp/jaeger:
    endpoint: jaeger:4317
    tls:
      insecure: true

service:
  pipelines:
    traces/aliyun:
      receivers: [otlp]
      processors: [memory_limiter, batch]
      exporters: [alibabacloud_logservice/aliyun]
    
    traces/tencent:
      receivers: [otlp]
      processors: [memory_limiter, batch]
      exporters: [tencentcloud_cls/tencent]
    
    traces/local:
      receivers: [otlp]
      processors: [batch]
      exporters: [otlp/jaeger]
```

---

## 🔒 安全配置

### TLS双向认证

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        tls:
          cert_file: /etc/otel/server.crt
          key_file: /etc/otel/server.key
          client_ca_file: /etc/otel/ca.crt
          client_auth_type: RequireAndVerifyClientCert

exporters:
  otlp:
    endpoint: backend:4317
    tls:
      cert_file: /etc/otel/client.crt
      key_file: /etc/otel/client.key
      ca_file: /etc/otel/ca.crt
```

**Rust客户端**:

```rust
let cert = tokio::fs::read("/etc/otel/client.crt").await?;
let key = tokio::fs::read("/etc/otel/client.key").await?;
let ca = tokio::fs::read("/etc/otel/ca.crt").await?;

let identity = tonic::transport::Identity::from_pem(cert, key);
let ca_cert = tonic::transport::Certificate::from_pem(ca);

let tls_config = tonic::transport::ClientTlsConfig::new()
    .identity(identity)
    .ca_certificate(ca_cert)
    .domain_name("collector.example.com");

let exporter = SpanExporter::builder()
    .with_tonic()
    .with_endpoint("https://collector.example.com:4317")
    .with_tls_config(tls_config)
    .build()?;
```

---

## 📊 监控Collector本身

### Health Check

```yaml
extensions:
  health_check:
    endpoint: 0.0.0.0:13133
    path: "/health"

service:
  extensions: [health_check]
```

**检测Collector健康**:

```rust
let client = reqwest::Client::new();
let response = client
    .get("http://collector:13133/health")
    .send()
    .await?;

if response.status().is_success() {
    println!("✅ Collector is healthy");
}
```

### Prometheus Metrics

```yaml
extensions:
  pprof:
    endpoint: 0.0.0.0:1777
  
  zpages:
    endpoint: 0.0.0.0:55679

service:
  telemetry:
    metrics:
      level: detailed
      address: 0.0.0.0:8888
  
  extensions: [pprof, zpages]
```

访问指标: `http://collector:8888/metrics`

---

## 🐳 Docker Compose示例

```yaml
version: '3.8'

services:
  otel-collector:
    image: otel/opentelemetry-collector-contrib:0.115.0
    command: ["--config=/etc/otel-collector-config.yaml"]
    volumes:
      - ./otel-collector-config.yaml:/etc/otel-collector-config.yaml
    ports:
      - "4317:4317"   # OTLP gRPC
      - "4318:4318"   # OTLP HTTP
      - "8888:8888"   # Prometheus metrics
      - "13133:13133" # Health check
    environment:
      - ALIYUN_ACCESS_KEY_ID=${ALIYUN_ACCESS_KEY_ID}
      - ALIYUN_ACCESS_KEY_SECRET=${ALIYUN_ACCESS_KEY_SECRET}
  
  rust-app:
    build: .
    environment:
      - OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4317
      - OTEL_SERVICE_NAME=my-rust-app
    depends_on:
      - otel-collector
```

---

## 🔍 故障诊断

### 开启详细日志

```yaml
service:
  telemetry:
    logs:
      level: debug
      development: true
```

### 常见问题

#### 1. 数据丢失

```yaml
# 增大队列
exporters:
  otlp:
    sending_queue:
      queue_size: 10000  # 默认5000

# 增大批次超时
processors:
  batch:
    timeout: 30s  # 默认10s
```

#### 2. 内存占用高

```yaml
# 严格限制
processors:
  memory_limiter:
    limit_mib: 256
    spike_limit_mib: 64
    check_interval: 1s
```

#### 3. 连接超时

```yaml
exporters:
  otlp:
    timeout: 60s  # 增加超时
    retry_on_failure:
      max_elapsed_time: 600s
```

---

## 📚 参考资源

| 资源 | 链接 |
|------|------|
| **Collector文档** | <https://opentelemetry.io/docs/collector/> |
| **Receiver参考** | <https://github.com/open-telemetry/opentelemetry-collector/tree/main/receiver> |
| **Processor参考** | <https://github.com/open-telemetry/opentelemetry-collector/tree/main/processor> |
| **Exporter参考** | <https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/exporter> |

---

**最后更新**: 2025年10月11日  
**Rust版本**: 1.90+  
**OpenTelemetry**: 0.31.0  
**上一篇**: [Semantic_Conventions速查手册_Rust版](./02_Semantic_Conventions速查手册_Rust版.md)  
**下一篇**: [故障排查速查手册_Rust版](./04_故障排查速查手册_Rust版.md)
