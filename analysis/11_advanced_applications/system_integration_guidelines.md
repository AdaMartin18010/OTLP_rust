# OTLP 系统集成指南

## 概述

本文档提供OpenTelemetry Protocol (OTLP)系统集成的全面指南，包括与各种技术栈的集成、部署策略、配置管理、安全考虑等，为实际生产环境的系统集成提供详细指导。

## 1. 技术栈集成指南

### 1.1 云平台集成

#### AWS集成

```rust
// AWS CloudWatch集成
pub struct AWSCloudWatchExporter {
    client: aws_sdk_cloudwatch::Client,
    namespace: String,
    region: String,
}

impl AWSCloudWatchExporter {
    pub async fn export_metrics(&self, metrics: Vec<Metric>) -> Result<(), ExportError> {
        let mut cloudwatch_metrics = Vec::new();
        
        for metric in metrics {
            let cloudwatch_metric = aws_sdk_cloudwatch::types::MetricDatum::builder()
                .metric_name(&metric.name)
                .value(metric.value)
                .unit(aws_sdk_cloudwatch::types::StandardUnit::Count)
                .timestamp(aws_sdk_cloudwatch::types::DateTime::from_secs(
                    metric.timestamp.unix_timestamp()
                ))
                .dimensions(
                    metric.attributes
                        .iter()
                        .map(|(k, v)| {
                            aws_sdk_cloudwatch::types::Dimension::builder()
                                .name(k)
                                .value(v)
                                .build()
                        })
                        .collect()
                )
                .build()?;

            cloudwatch_metrics.push(cloudwatch_metric);
        }

        // 分批发送到CloudWatch
        for chunk in cloudwatch_metrics.chunks(20) {
            let request = aws_sdk_cloudwatch::operation::put_metric_data::PutMetricDataInput::builder()
                .namespace(&self.namespace)
                .set_metric_data(Some(chunk.to_vec()))
                .build()?;

            self.client.put_metric_data().send().await?;
        }

        Ok(())
    }
}

// AWS X-Ray集成
pub struct AWSXRayExporter {
    client: aws_sdk_xray::Client,
}

impl AWSXRayExporter {
    pub async fn export_traces(&self, traces: Vec<Trace>) -> Result<(), ExportError> {
        for trace in traces {
            let xray_documents: Vec<String> = trace.spans
                .into_iter()
                .map(|span| self.convert_span_to_xray_document(span))
                .collect();

            let request = aws_sdk_xray::operation::put_trace_segments::PutTraceSegmentsInput::builder()
                .trace_segment_documents(xray_documents)
                .build()?;

            self.client.put_trace_segments().send().await?;
        }

        Ok(())
    }

    fn convert_span_to_xray_document(&self, span: Span) -> String {
        let xray_segment = XRaySegment {
            id: span.id.clone(),
            trace_id: span.trace_id.clone(),
            parent_id: span.parent_id,
            name: span.name,
            start_time: span.start_time,
            end_time: span.end_time,
            http: Some(XRayHTTP {
                request: XRayHTTPRequest {
                    method: span.attributes.get("http.method").cloned(),
                    url: span.attributes.get("http.url").cloned(),
                    user_agent: span.attributes.get("http.user_agent").cloned(),
                },
                response: XRayHTTPResponse {
                    status: span.attributes.get("http.status_code").and_then(|s| s.parse().ok()),
                },
            }),
            aws: Some(XRayAWS {
                service: span.attributes.get("aws.service").cloned(),
                operation: span.attributes.get("aws.operation").cloned(),
                region: span.attributes.get("aws.region").cloned(),
            }),
            metadata: span.attributes,
        };

        serde_json::to_string(&xray_segment).unwrap()
    }
}
```

#### Azure集成

```rust
// Azure Monitor集成
pub struct AzureMonitorExporter {
    client: azure_core::Client,
    instrumentation_key: String,
    connection_string: String,
}

impl AzureMonitorExporter {
    pub async fn export_telemetry(&self, telemetry: TelemetryData) -> Result<(), ExportError> {
        match telemetry {
            TelemetryData::Trace(trace) => self.export_trace(trace).await,
            TelemetryData::Metric(metric) => self.export_metric(metric).await,
            TelemetryData::Log(log) => self.export_log(log).await,
        }
    }

    async fn export_trace(&self, trace: Trace) -> Result<(), ExportError> {
        let telemetry_items: Vec<AzureTelemetryItem> = trace.spans
            .into_iter()
            .map(|span| AzureTelemetryItem {
                name: format!("Microsoft.ApplicationInsights.{}.Request", self.instrumentation_key),
                time: span.start_time.to_rfc3339(),
                i_key: self.instrumentation_key.clone(),
                tags: self.build_azure_tags(&span),
                data: AzureTelemetryData {
                    base_type: "RequestData".to_string(),
                    base_data: AzureRequestData {
                        id: span.id.clone(),
                        name: span.name,
                        duration: format!("PT{:.3}S", span.duration.as_secs_f64()),
                        success: span.status_code == StatusCode::Ok,
                        response_code: span.attributes.get("http.status_code").cloned(),
                        url: span.attributes.get("http.url").cloned(),
                        properties: span.attributes,
                    },
                },
            })
            .collect();

        self.send_to_azure_monitor(telemetry_items).await
    }

    async fn send_to_azure_monitor(&self, items: Vec<AzureTelemetryItem>) -> Result<(), ExportError> {
        let endpoint = format!("https://dc.applicationinsights.azure.com/v2/track");
        let body = serde_json::to_string(&items)?;

        let response = self.client
            .post(&endpoint)
            .header("Content-Type", "application/json")
            .header("Content-Encoding", "gzip")
            .body(body)
            .send()
            .await?;

        if response.status().is_success() {
            Ok(())
        } else {
            Err(ExportError::AzureMonitorError(response.status()))
        }
    }
}
```

#### Google Cloud集成

```rust
// Google Cloud Monitoring集成
pub struct GoogleCloudMonitoringExporter {
    client: google_cloud_monitoring::Client,
    project_id: String,
}

impl GoogleCloudMonitoringExporter {
    pub async fn export_metrics(&self, metrics: Vec<Metric>) -> Result<(), ExportError> {
        for metric in metrics {
            let time_series = google_cloud_monitoring::types::TimeSeries {
                metric: google_cloud_monitoring::types::Metric {
                    type_: format!("custom.googleapis.com/{}", metric.name),
                    labels: metric.attributes,
                },
                resource: google_cloud_monitoring::types::MonitoredResource {
                    type_: "global".to_string(),
                    labels: std::collections::HashMap::new(),
                },
                metric_kind: google_cloud_monitoring::types::MetricDescriptor_MetricKind::GAUGE,
                value_type: google_cloud_monitoring::types::MetricDescriptor_ValueType::DOUBLE,
                points: vec![google_cloud_monitoring::types::Point {
                    interval: google_cloud_monitoring::types::TimeInterval {
                        end_time: Some(google_cloud_monitoring::types::Timestamp {
                            seconds: metric.timestamp.unix_timestamp(),
                            nanos: 0,
                        }),
                    },
                    value: google_cloud_monitoring::types::TypedValue {
                        double_value: Some(metric.value),
                    },
                }],
            };

            let request = google_cloud_monitoring::types::CreateTimeSeriesRequest {
                name: format!("projects/{}", self.project_id),
                time_series: vec![time_series],
            };

            self.client.create_time_series(request).await?;
        }

        Ok(())
    }
}
```

### 1.2 数据库集成

#### PostgreSQL集成

```rust
// PostgreSQL可观测性集成
pub struct PostgreSQLObservability {
    connection_pool: Arc<deadpool_postgres::Pool>,
    tracer: Tracer,
    metrics: MetricsCollector,
}

impl PostgreSQLObservability {
    pub async fn execute_query(&self, query: &str, params: &[&dyn ToSql]) -> Result<Vec<Row>, DatabaseError> {
        let span = self.tracer
            .span_builder("postgresql_query")
            .with_attributes(vec![
                KeyValue::new("db.system", "postgresql"),
                KeyValue::new("db.statement", query.to_string()),
                KeyValue::new("db.operation", self.extract_operation(query)),
            ])
            .start(&self.tracer);

        let start_time = Instant::now();

        let result = async {
            let client = self.connection_pool.get().await?;
            
            // 执行查询
            let rows = client.query(query, params).await?;
            
            // 记录查询指标
            self.metrics.record_histogram(
                "database_query_duration",
                start_time.elapsed().as_secs_f64(),
                vec![
                    KeyValue::new("database", "postgresql"),
                    KeyValue::new("operation", self.extract_operation(query)),
                ]
            );

            Ok::<Vec<Row>, DatabaseError>(rows)
        }.await;

        match &result {
            Ok(rows) => {
                span.set_attribute(KeyValue::new("db.rows_returned", rows.len() as f64));
                span.set_status(StatusCode::Ok, "Query executed successfully");
            }
            Err(error) => {
                span.set_attribute(KeyValue::new("db.error", error.to_string()));
                span.set_status(StatusCode::Error, error.to_string());
            }
        }

        span.end();
        result
    }

    fn extract_operation(&self, query: &str) -> String {
        let query_upper = query.trim().to_uppercase();
        if query_upper.starts_with("SELECT") {
            "SELECT".to_string()
        } else if query_upper.starts_with("INSERT") {
            "INSERT".to_string()
        } else if query_upper.starts_with("UPDATE") {
            "UPDATE".to_string()
        } else if query_upper.starts_with("DELETE") {
            "DELETE".to_string()
        } else {
            "OTHER".to_string()
        }
    }
}
```

#### Redis集成

```rust
// Redis可观测性集成
pub struct RedisObservability {
    client: Arc<redis::Client>,
    tracer: Tracer,
    metrics: MetricsCollector,
}

impl RedisObservability {
    pub async fn execute_command(&self, cmd: &str, args: &[String]) -> Result<redis::Value, RedisError> {
        let span = self.tracer
            .span_builder("redis_command")
            .with_attributes(vec![
                KeyValue::new("db.system", "redis"),
                KeyValue::new("db.operation", cmd.to_string()),
                KeyValue::new("db.redis.database_index", 0),
            ])
            .start(&self.tracer);

        let start_time = Instant::now();

        let result = async {
            let mut conn = self.client.get_async_connection().await?;
            
            // 执行Redis命令
            let value = redis::cmd(cmd)
                .arg(args)
                .query_async(&mut conn)
                .await?;

            // 记录命令指标
            self.metrics.record_histogram(
                "redis_command_duration",
                start_time.elapsed().as_secs_f64(),
                vec![
                    KeyValue::new("command", cmd.to_string()),
                ]
            );

            Ok::<redis::Value, RedisError>(value)
        }.await;

        match &result {
            Ok(_) => {
                span.set_status(StatusCode::Ok, "Command executed successfully");
            }
            Err(error) => {
                span.set_attribute(KeyValue::new("db.error", error.to_string()));
                span.set_status(StatusCode::Error, error.to_string());
            }
        }

        span.end();
        result
    }
}
```

### 1.3 消息队列集成

#### Apache Kafka集成

```rust
// Kafka可观测性集成
pub struct KafkaObservability {
    producer: Arc<FutureProducer>,
    consumer: Arc<StreamConsumer>,
    tracer: Tracer,
    metrics: MetricsCollector,
}

impl KafkaObservability {
    pub async fn send_message(&self, topic: &str, key: &str, payload: &[u8]) -> Result<(), KafkaError> {
        let span = self.tracer
            .span_builder("kafka_produce")
            .with_attributes(vec![
                KeyValue::new("messaging.system", "kafka"),
                KeyValue::new("messaging.destination", topic.to_string()),
                KeyValue::new("messaging.destination_kind", "topic"),
                KeyValue::new("messaging.message_key", key.to_string()),
                KeyValue::new("messaging.message_size", payload.len() as f64),
            ])
            .start(&self.tracer);

        let start_time = Instant::now();

        let result = async {
            let record = FutureRecord::to(topic)
                .key(key)
                .payload(payload)
                .headers(self.create_trace_headers(&span));

            let delivery_result = self.producer.send(record, Duration::from_secs(0)).await?;
            
            // 记录生产指标
            self.metrics.increment_counter("kafka_messages_produced", 1, vec![
                KeyValue::new("topic", topic.to_string()),
            ]);

            Ok::<(), KafkaError>(())
        }.await;

        match &result {
            Ok(_) => {
                span.set_status(StatusCode::Ok, "Message sent successfully");
            }
            Err(error) => {
                span.set_attribute(KeyValue::new("messaging.error", error.to_string()));
                span.set_status(StatusCode::Error, error.to_string());
            }
        }

        span.end();
        result
    }

    pub async fn consume_messages(&self, topics: &[&str]) -> Result<(), KafkaError> {
        self.consumer.subscribe(topics)?;

        loop {
            match self.consumer.recv().await {
                Ok(message) => {
                    let span = self.tracer
                        .span_builder("kafka_consume")
                        .with_attributes(vec![
                            KeyValue::new("messaging.system", "kafka"),
                            KeyValue::new("messaging.destination", message.topic().to_string()),
                            KeyValue::new("messaging.destination_kind", "topic"),
                            KeyValue::new("messaging.message_key", message.key().unwrap_or(&[]).to_string()),
                            KeyValue::new("messaging.message_size", message.payload().len() as f64),
                            KeyValue::new("messaging.kafka.partition", message.partition() as f64),
                            KeyValue::new("messaging.kafka.offset", message.offset() as f64),
                        ])
                        .start(&self.tracer);

                    // 提取追踪上下文
                    if let Some(headers) = message.headers() {
                        self.extract_trace_context(headers, &span);
                    }

                    // 记录消费指标
                    self.metrics.increment_counter("kafka_messages_consumed", 1, vec![
                        KeyValue::new("topic", message.topic().to_string()),
                    ]);

                    span.end();
                }
                Err(e) => {
                    return Err(e.into());
                }
            }
        }
    }

    fn create_trace_headers(&self, span: &Span) -> Headers {
        let mut headers = Headers::new();
        
        headers.insert("traceparent", format!("00-{}-{}-01", 
            span.span_context().trace_id(),
            span.span_context().span_id()
        ));
        
        headers
    }

    fn extract_trace_context(&self, headers: &Headers, span: &Span) {
        if let Some(traceparent) = headers.get("traceparent") {
            // 解析traceparent头部
            let parts: Vec<&str> = traceparent.split('-').collect();
            if parts.len() >= 3 {
                let trace_id = parts[1];
                let span_id = parts[2];
                // 设置追踪上下文
            }
        }
    }
}
```

## 2. 部署策略指南

### 2.1 容器化部署

```yaml
# Dockerfile示例
FROM rust:1.75-slim as builder

WORKDIR /app
COPY . .

RUN cargo build --release

FROM debian:bullseye-slim

RUN apt-get update && apt-get install -y \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

COPY --from=builder /app/target/release/otlp-collector /usr/local/bin/

EXPOSE 4317 4318

CMD ["otlp-collector"]
```

```yaml
# docker-compose.yml示例
version: '3.8'

services:
  otlp-collector:
    build: .
    ports:
      - "4317:4317"  # OTLP gRPC
      - "4318:4318"  # OTLP HTTP
    environment:
      - OTLP_EXPORTER_ENDPOINT=http://jaeger:14250
      - OTLP_BATCH_SIZE=512
      - OTLP_EXPORT_TIMEOUT=30s
    volumes:
      - ./config:/etc/otlp
    depends_on:
      - jaeger
      - prometheus

  jaeger:
    image: jaegertracing/all-in-one:latest
    ports:
      - "16686:16686"
      - "14250:14250"
    environment:
      - COLLECTOR_OTLP_ENABLED=true

  prometheus:
    image: prom/prometheus:latest
    ports:
      - "9090:9090"
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml

  grafana:
    image: grafana/grafana:latest
    ports:
      - "3000:3000"
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=admin
    volumes:
      - grafana-storage:/var/lib/grafana

volumes:
  grafana-storage:
```

### 2.2 Kubernetes部署

```yaml
# otlp-collector-deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otlp-collector
  labels:
    app: otlp-collector
spec:
  replicas: 3
  selector:
    matchLabels:
      app: otlp-collector
  template:
    metadata:
      labels:
        app: otlp-collector
    spec:
      containers:
      - name: otlp-collector
        image: otlp-collector:latest
        ports:
        - containerPort: 4317
          name: otlp-grpc
        - containerPort: 4318
          name: otlp-http
        env:
        - name: OTLP_EXPORTER_ENDPOINT
          value: "http://jaeger-collector:14250"
        - name: OTLP_BATCH_SIZE
          value: "512"
        - name: OTLP_EXPORT_TIMEOUT
          value: "30s"
        resources:
          requests:
            memory: "256Mi"
            cpu: "250m"
          limits:
            memory: "512Mi"
            cpu: "500m"
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /ready
            port: 8080
          initialDelaySeconds: 5
          periodSeconds: 5
---
apiVersion: v1
kind: Service
metadata:
  name: otlp-collector-service
spec:
  selector:
    app: otlp-collector
  ports:
  - name: otlp-grpc
    port: 4317
    targetPort: 4317
  - name: otlp-http
    port: 4318
    targetPort: 4318
  type: ClusterIP
```

### 2.3 Helm Chart部署

```yaml
# Chart.yaml
apiVersion: v2
name: otlp-collector
description: OpenTelemetry Protocol Collector
version: 0.1.0
appVersion: "1.0.0"

# values.yaml
replicaCount: 3

image:
  repository: otlp-collector
  tag: latest
  pullPolicy: IfNotPresent

service:
  type: ClusterIP
  port: 4317
  httpPort: 4318

resources:
  limits:
    cpu: 500m
    memory: 512Mi
  requests:
    cpu: 250m
    memory: 256Mi

config:
  exporters:
    jaeger:
      endpoint: "http://jaeger-collector:14250"
    prometheus:
      endpoint: "0.0.0.0:8889"
  
  processors:
    batch:
      send_batch_size: 512
      timeout: 30s
  
  receivers:
    otlp:
      protocols:
        grpc:
          endpoint: 0.0.0.0:4317
        http:
          endpoint: 0.0.0.0:4318
```

## 3. 配置管理

### 3.1 环境配置

```rust
// 配置管理实现
use serde::{Deserialize, Serialize};
use std::env;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OtlpConfig {
    pub exporters: ExporterConfig,
    pub receivers: ReceiverConfig,
    pub processors: ProcessorConfig,
    pub service: ServiceConfig,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExporterConfig {
    pub jaeger: Option<JaegerExporterConfig>,
    pub prometheus: Option<PrometheusExporterConfig>,
    pub otlp: Option<OtlpExporterConfig>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct JaegerExporterConfig {
    pub endpoint: String,
    pub timeout: Option<Duration>,
    pub batch_size: Option<usize>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReceiverConfig {
    pub otlp: OtlpReceiverConfig,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OtlpReceiverConfig {
    pub protocols: OtlpProtocolsConfig,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OtlpProtocolsConfig {
    pub grpc: Option<GrpcConfig>,
    pub http: Option<HttpConfig>,
}

impl OtlpConfig {
    pub fn from_env() -> Result<Self, ConfigError> {
        let config = OtlpConfig {
            exporters: ExporterConfig {
                jaeger: env::var("JAEGER_ENDPOINT")
                    .ok()
                    .map(|endpoint| JaegerExporterConfig {
                        endpoint,
                        timeout: env::var("JAEGER_TIMEOUT")
                            .ok()
                            .and_then(|s| s.parse().ok())
                            .map(Duration::from_secs),
                        batch_size: env::var("JAEGER_BATCH_SIZE")
                            .ok()
                            .and_then(|s| s.parse().ok()),
                    }),
                prometheus: env::var("PROMETHEUS_ENDPOINT")
                    .ok()
                    .map(|endpoint| PrometheusExporterConfig { endpoint }),
                otlp: env::var("OTLP_EXPORTER_ENDPOINT")
                    .ok()
                    .map(|endpoint| OtlpExporterConfig { endpoint }),
            },
            receivers: ReceiverConfig {
                otlp: OtlpReceiverConfig {
                    protocols: OtlpProtocolsConfig {
                        grpc: Some(GrpcConfig {
                            endpoint: env::var("OTLP_GRPC_ENDPOINT")
                                .unwrap_or_else(|_| "0.0.0.0:4317".to_string()),
                        }),
                        http: Some(HttpConfig {
                            endpoint: env::var("OTLP_HTTP_ENDPOINT")
                                .unwrap_or_else(|_| "0.0.0.0:4318".to_string()),
                        }),
                    },
                },
            },
            processors: ProcessorConfig {
                batch: BatchProcessorConfig {
                    send_batch_size: env::var("BATCH_SIZE")
                        .ok()
                        .and_then(|s| s.parse().ok())
                        .unwrap_or(512),
                    timeout: env::var("BATCH_TIMEOUT")
                        .ok()
                        .and_then(|s| s.parse().ok())
                        .map(Duration::from_secs)
                        .unwrap_or(Duration::from_secs(30)),
                },
            },
            service: ServiceConfig {
                pipelines: ServicePipelinesConfig {
                    traces: PipelineConfig {
                        receivers: vec!["otlp".to_string()],
                        processors: vec!["batch".to_string()],
                        exporters: vec!["jaeger".to_string()],
                    },
                    metrics: PipelineConfig {
                        receivers: vec!["otlp".to_string()],
                        processors: vec!["batch".to_string()],
                        exporters: vec!["prometheus".to_string()],
                    },
                    logs: PipelineConfig {
                        receivers: vec!["otlp".to_string()],
                        processors: vec!["batch".to_string()],
                        exporters: vec!["otlp".to_string()],
                    },
                },
            },
        };

        Ok(config)
    }

    pub fn from_file(path: &str) -> Result<Self, ConfigError> {
        let content = std::fs::read_to_string(path)?;
        let config: OtlpConfig = serde_yaml::from_str(&content)?;
        Ok(config)
    }

    pub fn validate(&self) -> Result<(), ConfigError> {
        // 验证配置的完整性和正确性
        if self.exporters.jaeger.is_none() && 
           self.exporters.prometheus.is_none() && 
           self.exporters.otlp.is_none() {
            return Err(ConfigError::NoExporters);
        }

        if self.receivers.otlp.protocols.grpc.is_none() && 
           self.receivers.otlp.protocols.http.is_none() {
            return Err(ConfigError::NoReceivers);
        }

        Ok(())
    }
}
```

### 3.2 动态配置更新

```rust
// 动态配置更新
pub struct DynamicConfigManager {
    current_config: Arc<RwLock<OtlpConfig>>,
    config_watcher: ConfigWatcher,
    update_handlers: Vec<Box<dyn ConfigUpdateHandler>>,
}

impl DynamicConfigManager {
    pub async fn start_watching(&self) -> Result<(), ConfigError> {
        let mut receiver = self.config_watcher.watch().await?;
        
        while let Some(new_config) = receiver.recv().await {
            let mut config = self.current_config.write().unwrap();
            *config = new_config;
            drop(config);

            // 通知所有处理器配置已更新
            for handler in &self.update_handlers {
                handler.on_config_updated(&self.current_config.read().unwrap()).await?;
            }
        }

        Ok(())
    }

    pub fn get_current_config(&self) -> OtlpConfig {
        self.current_config.read().unwrap().clone()
    }
}

pub trait ConfigUpdateHandler: Send + Sync {
    async fn on_config_updated(&self, config: &OtlpConfig) -> Result<(), ConfigError>;
}
```

## 4. 安全考虑

### 4.1 认证和授权

```rust
// mTLS认证实现
pub struct MtlsAuthenticator {
    ca_cert: Certificate,
    server_cert: Certificate,
    server_key: PrivateKey,
}

impl MtlsAuthenticator {
    pub fn new(ca_cert_path: &str, server_cert_path: &str, server_key_path: &str) -> Result<Self, AuthError> {
        let ca_cert = Certificate::from_pem(&std::fs::read(ca_cert_path)?)?;
        let server_cert = Certificate::from_pem(&std::fs::read(server_cert_path)?)?;
        let server_key = PrivateKey::from_pem(&std::fs::read(server_key_path)?)?;

        Ok(Self {
            ca_cert,
            server_cert,
            server_key,
        })
    }

    pub fn create_server_config(&self) -> Result<ServerConfig, AuthError> {
        let mut tls_config = ServerConfig::new(NoClientAuth::new());
        tls_config.set_single_cert(self.server_cert.clone(), self.server_key.clone())?;
        tls_config.set_client_certificate_verifier(self.create_cert_verifier());
        
        Ok(tls_config)
    }

    fn create_cert_verifier(&self) -> Arc<dyn ClientCertVerifier> {
        Arc::new(CustomCertVerifier::new(self.ca_cert.clone()))
    }
}

pub struct CustomCertVerifier {
    ca_cert: Certificate,
}

impl CustomCertVerifier {
    pub fn new(ca_cert: Certificate) -> Self {
        Self { ca_cert }
    }
}

impl ClientCertVerifier for CustomCertVerifier {
    fn verify_client_cert(
        &self,
        certs: &[Certificate],
        sni: Option<&webpki::DNSNameRef>,
    ) -> Result<ClientCertVerified, rustls::TLSError> {
        if certs.is_empty() {
            return Err(rustls::TLSError::NoCertificatesPresented);
        }

        let leaf_cert = &certs[0];
        
        // 验证证书链
        let mut chain = webpki::CertificateChain::new();
        for cert in certs {
            chain.add(cert)?;
        }

        // 验证签名
        let trust_anchor = webpki::TrustAnchor::try_from_cert_der(&self.ca_cert.0)?;
        let trust_anchors = &[trust_anchor];
        
        leaf_cert.verify_is_valid_tls_client_cert(
            webpki::EndEntityCert::try_from(&leaf_cert.0)?,
            &webpki::TlsClientTrustAnchors(trust_anchors),
            &webpki::TlsSignatureAlgorithm::all(),
            webpki::Time::try_from(std::time::SystemTime::now())?,
        )?;

        Ok(ClientCertVerified::assertion())
    }

    fn client_auth_root_subjects(&self) -> webpki::DistinguishedNames {
        webpki::DistinguishedNames::new()
    }
}
```

### 4.2 数据加密

```rust
// 数据加密实现
pub struct DataEncryption {
    encryption_key: [u8; 32],
    encryption_algorithm: EncryptionAlgorithm,
}

impl DataEncryption {
    pub fn new(key: &[u8]) -> Result<Self, EncryptionError> {
        if key.len() != 32 {
            return Err(EncryptionError::InvalidKeyLength);
        }

        let mut encryption_key = [0u8; 32];
        encryption_key.copy_from_slice(key);

        Ok(Self {
            encryption_key,
            encryption_algorithm: EncryptionAlgorithm::Aes256Gcm,
        })
    }

    pub fn encrypt(&self, data: &[u8]) -> Result<EncryptedData, EncryptionError> {
        match self.encryption_algorithm {
            EncryptionAlgorithm::Aes256Gcm => {
                let cipher = aes_gcm::Aes256Gcm::new(&self.encryption_key.into());
                let nonce = aes_gcm::Nonce::from_slice(b"unique nonce");
                let ciphertext = cipher.encrypt(nonce, data)?;

                Ok(EncryptedData {
                    algorithm: self.encryption_algorithm,
                    ciphertext,
                    nonce: nonce.to_vec(),
                })
            }
        }
    }

    pub fn decrypt(&self, encrypted_data: &EncryptedData) -> Result<Vec<u8>, EncryptionError> {
        match encrypted_data.algorithm {
            EncryptionAlgorithm::Aes256Gcm => {
                let cipher = aes_gcm::Aes256Gcm::new(&self.encryption_key.into());
                let nonce = aes_gcm::Nonce::from_slice(&encrypted_data.nonce);
                let plaintext = cipher.decrypt(nonce, encrypted_data.ciphertext.as_ref())?;

                Ok(plaintext)
            }
        }
    }
}
```

## 5. 监控和告警

### 5.1 健康检查

```rust
// 健康检查实现
pub struct HealthChecker {
    components: Vec<Box<dyn HealthCheckable>>,
    tracer: Tracer,
    metrics: MetricsCollector,
}

pub trait HealthCheckable: Send + Sync {
    fn name(&self) -> &str;
    async fn check_health(&self) -> HealthStatus;
}

impl HealthChecker {
    pub async fn check_all_components(&self) -> HealthReport {
        let span = self.tracer
            .span_builder("health_check")
            .start(&self.tracer);

        let mut report = HealthReport {
            overall_status: HealthStatus::Healthy,
            components: Vec::new(),
            timestamp: SystemTime::now(),
        };

        for component in &self.components {
            let component_span = self.tracer
                .span_builder("component_health_check")
                .with_attributes(vec![
                    KeyValue::new("component.name", component.name().to_string()),
                ])
                .start(&self.tracer);

            let start_time = Instant::now();
            let status = component.check_health().await;
            let check_duration = start_time.elapsed();

            let component_report = ComponentHealthReport {
                name: component.name().to_string(),
                status: status.clone(),
                check_duration,
                last_check: SystemTime::now(),
            };

            report.components.push(component_report);

            // 更新整体状态
            if status == HealthStatus::Unhealthy {
                report.overall_status = HealthStatus::Unhealthy;
            } else if status == HealthStatus::Degraded && report.overall_status == HealthStatus::Healthy {
                report.overall_status = HealthStatus::Degraded;
            }

            component_span.set_attribute(KeyValue::new("health.status", status.to_string()));
            component_span.end();
        }

        // 记录健康检查指标
        self.metrics.record_gauge("health_check_duration", span.start_time().elapsed().as_secs_f64());
        
        span.end();
        report
    }
}
```

### 5.2 告警系统

```rust
// 告警系统实现
pub struct AlertingSystem {
    alert_rules: Vec<AlertRule>,
    notification_channels: Vec<Box<dyn NotificationChannel>>,
    alert_history: Arc<Mutex<Vec<AlertEvent>>>,
    tracer: Tracer,
}

pub struct AlertRule {
    pub name: String,
    pub condition: AlertCondition,
    pub severity: AlertSeverity,
    pub notification_channels: Vec<String>,
    pub cooldown_period: Duration,
}

impl AlertingSystem {
    pub async fn evaluate_alerts(&self, metrics: &SystemMetrics) -> Vec<Alert> {
        let mut alerts = Vec::new();

        for rule in &self.alert_rules {
            if self.should_evaluate_rule(rule, metrics).await {
                if self.evaluate_condition(&rule.condition, metrics) {
                    let alert = Alert {
                        id: Uuid::new_v4().to_string(),
                        rule_name: rule.name.clone(),
                        severity: rule.severity.clone(),
                        message: self.generate_alert_message(rule, metrics),
                        timestamp: SystemTime::now(),
                        metrics: metrics.clone(),
                    };

                    alerts.push(alert);
                }
            }
        }

        alerts
    }

    pub async fn send_alert(&self, alert: Alert) -> Result<(), NotificationError> {
        let span = self.tracer
            .span_builder("alert_notification")
            .with_attributes(vec![
                KeyValue::new("alert.id", alert.id.clone()),
                KeyValue::new("alert.severity", alert.severity.to_string()),
                KeyValue::new("alert.rule", alert.rule_name.clone()),
            ])
            .start(&self.tracer);

        // 记录告警事件
        let alert_event = AlertEvent {
            alert: alert.clone(),
            sent_at: SystemTime::now(),
            status: AlertStatus::Sent,
        };

        self.alert_history.lock().unwrap().push(alert_event);

        // 发送通知
        for channel in &self.notification_channels {
            match channel.send_notification(&alert).await {
                Ok(_) => {
                    self.tracer.increment_counter("alert_notifications_sent", 1);
                }
                Err(error) => {
                    span.set_attribute(KeyValue::new("notification.error", error.to_string()));
                    span.set_status(StatusCode::Error, error.to_string());
                }
            }
        }

        span.end();
        Ok(())
    }
}
```

## 6. 最佳实践总结

### 6.1 集成最佳实践

1. **渐进式集成**: 从核心组件开始，逐步扩展到整个系统
2. **配置管理**: 使用环境变量和配置文件管理不同环境的配置
3. **错误处理**: 完善的错误处理和重试机制
4. **性能监控**: 集成性能监控和告警系统
5. **安全考虑**: 实施适当的安全措施，包括认证、授权和加密

### 6.2 部署最佳实践

1. **容器化**: 使用Docker容器化应用
2. **编排**: 使用Kubernetes进行容器编排
3. **配置管理**: 使用ConfigMap和Secret管理配置
4. **资源管理**: 合理设置资源请求和限制
5. **健康检查**: 实施完善的健康检查机制

### 6.3 运维最佳实践

1. **监控告警**: 建立完善的监控和告警体系
2. **日志管理**: 集中化日志收集和分析
3. **备份恢复**: 定期备份重要数据
4. **容量规划**: 基于历史数据进行容量规划
5. **文档维护**: 保持文档的及时更新

---

*本文档提供了OTLP系统集成的全面指南，为实际生产环境的部署和运维提供详细指导。*
