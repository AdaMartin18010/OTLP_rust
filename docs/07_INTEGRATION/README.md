# 🔗 集成指南

**版本**: 1.0
**最后更新**: 2025年10月26日
**状态**: 🟢 活跃维护

> **简介**: OTLP Rust 集成指南 - OpenTelemetry生态、服务网格、云原生部署和第三方工具集成。

---

## 📋 目录

- [🔗 集成指南](#-集成指南)
  - [📋 目录](#-目录)
  - [🌐 OpenTelemetry 生态集成](#-opentelemetry-生态集成)
    - [Collector 集成](#collector-集成)
      - [Collector 配置](#collector-配置)
      - [客户端配置](#客户端配置)
    - [SDK 集成](#sdk-集成)
      - [自动 Instrumentation](#自动-instrumentation)
    - [Instrumentation 集成](#instrumentation-集成)
      - [HTTP 客户端 Instrumentation](#http-客户端-instrumentation)
      - [数据库 Instrumentation](#数据库-instrumentation)
    - [Exporters 集成](#exporters-集成)
      - [多 Exporter 配置](#多-exporter-配置)
  - [🕸️ 服务网格集成](#️-服务网格集成)
    - [Istio 集成](#istio-集成)
      - [VirtualService 配置](#virtualservice-配置)
      - [DestinationRule 配置](#destinationrule-配置)
      - [客户端配置1](#客户端配置1)
    - [Linkerd 集成](#linkerd-集成)
      - [ServiceProfile 配置](#serviceprofile-配置)
      - [客户端集成](#客户端集成)
    - [Envoy 集成](#envoy-集成)
      - [Envoy 配置](#envoy-配置)
    - [Consul Connect 集成](#consul-connect-集成)
      - [Consul 配置](#consul-配置)
      - [服务注册](#服务注册)
  - [☁️ 云原生部署](#️-云原生部署)
    - [Kubernetes 集成](#kubernetes-集成)
      - [Operator 配置](#operator-配置)
    - [Docker 集成](#docker-集成)
      - [多架构构建](#多架构构建)
      - [Docker Compose 多服务](#docker-compose-多服务)
    - [Helm 集成](#helm-集成)
      - [Chart 结构](#chart-结构)
      - [Chart.yaml](#chartyaml)
    - [Operator 集成](#operator-集成)
      - [Operator 实现](#operator-实现)
  - [🛠️ 第三方工具集成](#️-第三方工具集成)
    - [监控工具集成](#监控工具集成)
      - [Grafana 集成](#grafana-集成)
      - [Datadog 集成](#datadog-集成)
    - [日志工具集成](#日志工具集成)
      - [ELK Stack 集成](#elk-stack-集成)
      - [Fluentd 集成](#fluentd-集成)
    - [APM 工具集成](#apm-工具集成)
      - [New Relic 集成](#new-relic-集成)
      - [AppDynamics 集成](#appdynamics-集成)
    - [CI/CD 工具集成](#cicd-工具集成)
      - [Jenkins 集成](#jenkins-集成)
      - [GitLab CI 集成](#gitlab-ci-集成)
  - [🔧 自定义集成](#-自定义集成)
    - [自定义 Exporter](#自定义-exporter)
    - [自定义 Processor](#自定义-processor)
  - [📊 集成测试](#-集成测试)
    - [端到端测试](#端到端测试)
    - [性能测试](#性能测试)
  - [🔗 相关文档](#-相关文档)

## 🌐 OpenTelemetry 生态集成

### Collector 集成

#### Collector 配置

```yaml
# collector-config.yaml
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

  memory_limiter:
    limit_mib: 512
    spike_limit_mib: 128
    check_interval: 5s

  attributes:
    actions:
      - key: service.name
        value: otlp-client
        action: upsert
      - key: service.version
        value: "1.0.0"
        action: upsert

exporters:
  jaeger:
    endpoint: jaeger:14250
    tls:
      insecure: true

  prometheus:
    endpoint: "0.0.0.0:8889"
    namespace: otlp

  logging:
    loglevel: info

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, attributes, batch]
      exporters: [jaeger, logging]

    metrics:
      receivers: [otlp]
      processors: [memory_limiter, attributes, batch]
      exporters: [prometheus, logging]

    logs:
      receivers: [otlp]
      processors: [memory_limiter, attributes, batch]
      exporters: [logging]
```

#### 客户端配置

```rust
use opentelemetry::trace::TracerProvider;
use opentelemetry_sdk::trace::TracerProvider as SdkTracerProvider;
use opentelemetry_otlp::SpanExporter;

// OTLP 客户端配置
pub async fn setup_otlp_client() -> Result<OtlpClient, OtlpError> {
    let config = OtlpConfig::default()
        .with_endpoint("http://collector:4317")
        .with_protocol(TransportProtocol::Grpc)
        .with_timeout(Duration::from_secs(10))
        .with_batch_config(BatchConfig {
            max_export_batch_size: 512,
            export_timeout: Duration::from_millis(5000),
            max_queue_size: 2048,
            scheduled_delay: Duration::from_millis(5000),
        });

    OtlpClient::new(config).await
}
```

### SDK 集成

#### 自动 Instrumentation

```rust
use opentelemetry::trace::{Tracer, TracerProvider};
use opentelemetry_sdk::trace::TracerProvider as SdkTracerProvider;
use opentelemetry_otlp::SpanExporter;
use tracing_opentelemetry::OpenTelemetrySpanExt;

// 自动 Instrumentation 设置
pub fn setup_auto_instrumentation() -> Result<(), Box<dyn std::error::Error>> {
    // 创建 OTLP Exporter
    let exporter = SpanExporter::new(
        opentelemetry_otlp::new_exporter()
            .tonic()
            .with_endpoint("http://collector:4317")
    )?;

    // 创建 TracerProvider
    let provider = SdkTracerProvider::builder()
        .with_batch_exporter(exporter)
        .build();

    // 设置全局 TracerProvider
    opentelemetry::global::set_tracer_provider(provider);

    // 初始化 tracing
    tracing_subscriber::registry()
        .with(tracing_opentelemetry::layer())
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .init();

    Ok(())
}

// 使用自动 Instrumentation
pub async fn process_request(request: &Request) -> Result<Response, Error> {
    let span = tracing::info_span!("process_request");
    let _enter = span.enter();

    // 业务逻辑会自动创建子 span
    let result = business_logic(request).await;

    result
}
```

### Instrumentation 集成

#### HTTP 客户端 Instrumentation

```rust
use opentelemetry::trace::Tracer;
use opentelemetry_http::HttpClientTraceLayer;
use tower::ServiceBuilder;

// HTTP 客户端自动 Instrumentation
pub fn create_instrumented_http_client() -> reqwest::Client {
    let client = reqwest::Client::builder()
        .build()
        .unwrap();

    // 添加 tracing 中间件
    let service = ServiceBuilder::new()
        .layer(HttpClientTraceLayer::new())
        .service(client);

    service
}
```

#### 数据库 Instrumentation

```rust
use opentelemetry::trace::Tracer;
use sqlx::PgPool;

// 数据库 Instrumentation
pub struct InstrumentedDatabase {
    pool: PgPool,
    tracer: Tracer,
}

impl InstrumentedDatabase {
    pub async fn query<T>(&self, query: &str) -> Result<Vec<T>, sqlx::Error>
    where
        T: for<'r> sqlx::FromRow<'r, sqlx::postgres::PgRow> + Send + Unpin,
    {
        let span = self.tracer.start("database.query");
        let _enter = span.enter();

        span.set_attribute("db.statement", query.into());

        let result = sqlx::query_as::<_, T>(query)
            .fetch_all(&self.pool)
            .await;

        match &result {
            Ok(rows) => {
                span.set_attribute("db.rows_affected", rows.len() as i64);
            }
            Err(e) => {
                span.record_error(e);
            }
        }

        result
    }
}
```

### Exporters 集成

#### 多 Exporter 配置

```rust
use opentelemetry::trace::TracerProvider;
use opentelemetry_sdk::trace::TracerProvider as SdkTracerProvider;
use opentelemetry_otlp::SpanExporter;
use opentelemetry_jaeger::new_agent_pipeline;

// 多 Exporter 配置
pub fn setup_multi_exporter() -> Result<(), Box<dyn std::error::Error>> {
    // OTLP Exporter
    let otlp_exporter = SpanExporter::new(
        opentelemetry_otlp::new_exporter()
            .tonic()
            .with_endpoint("http://collector:4317")
    )?;

    // Jaeger Exporter
    let jaeger_exporter = new_agent_pipeline()
        .with_service_name("otlp-client")
        .with_endpoint("http://jaeger:14268/api/traces")
        .install_simple()?;

    // 创建 TracerProvider
    let provider = SdkTracerProvider::builder()
        .with_batch_exporter(otlp_exporter)
        .with_simple_exporter(jaeger_exporter)
        .build();

    opentelemetry::global::set_tracer_provider(provider);

    Ok(())
}
```

## 🕸️ 服务网格集成

### Istio 集成

#### VirtualService 配置

```yaml
apiVersion: networking.istio.io/v1alpha3
kind: VirtualService
metadata:
  name: otlp-client
  namespace: otlp
spec:
  hosts:
  - otlp-client
  http:
  - match:
    - headers:
        x-otlp-version:
          exact: "1.0"
    route:
    - destination:
        host: otlp-client
        subset: v1
      weight: 90
    - destination:
        host: otlp-client
        subset: v2
      weight: 10
  - route:
    - destination:
        host: otlp-client
        subset: v1
    timeout: 30s
    retries:
      attempts: 3
      perTryTimeout: 10s
      retryOn: 5xx,reset,connect-failure,refused-stream
```

#### DestinationRule 配置

```yaml
apiVersion: networking.istio.io/v1alpha3
kind: DestinationRule
metadata:
  name: otlp-client
  namespace: otlp
spec:
  host: otlp-client
  trafficPolicy:
    loadBalancer:
      simple: LEAST_CONN
    connectionPool:
      tcp:
        maxConnections: 100
      http:
        http1MaxPendingRequests: 50
        http2MaxRequests: 100
        maxRequestsPerConnection: 2
        maxRetries: 3
        consecutiveGatewayErrors: 3
        interval: 30s
        baseEjectionTime: 30s
        maxEjectionPercent: 50
  subsets:
  - name: v1
    labels:
      version: v1.0.0
  - name: v2
    labels:
      version: v2.0.0
```

#### 客户端配置1

```rust
// Istio 集成配置
pub struct IstioConfig {
    pub service_mesh: bool,
    pub mTLS: bool,
    pub tracing: bool,
    pub metrics: bool,
}

impl IstioConfig {
    pub fn from_env() -> Self {
        Self {
            service_mesh: std::env::var("ISTIO_SERVICE_MESH")
                .unwrap_or_default()
                .parse()
                .unwrap_or(false),
            mTLS: std::env::var("ISTIO_MTLS")
                .unwrap_or_default()
                .parse()
                .unwrap_or(true),
            tracing: std::env::var("ISTIO_TRACING")
                .unwrap_or_default()
                .parse()
                .unwrap_or(true),
            metrics: std::env::var("ISTIO_METRICS")
                .unwrap_or_default()
                .parse()
                .unwrap_or(true),
        }
    }
}
```

### Linkerd 集成

#### ServiceProfile 配置

```yaml
apiVersion: linkerd.io/v1alpha2
kind: ServiceProfile
metadata:
  name: otlp-client
  namespace: otlp
spec:
  routes:
  - name: POST /v1/traces
    condition:
      method: POST
      pathRegex: /v1/traces
    isRetryable: true
    timeout: 10s
  - name: POST /v1/metrics
    condition:
      method: POST
      pathRegex: /v1/metrics
    isRetryable: true
    timeout: 10s
  - name: POST /v1/logs
    condition:
      method: POST
      pathRegex: /v1/logs
    isRetryable: true
    timeout: 10s
  retryBudget:
    retryRatio: 0.2
    minRetriesPerSecond: 10
    ttl: 10s
```

#### 客户端集成

```rust
// Linkerd 集成
pub struct LinkerdIntegration {
    service_mesh: bool,
    auto_inject: bool,
}

impl LinkerdIntegration {
    pub fn new() -> Self {
        Self {
            service_mesh: std::env::var("LINKERD_SERVICE_MESH")
                .unwrap_or_default()
                .parse()
                .unwrap_or(false),
            auto_inject: std::env::var("LINKERD_AUTO_INJECT")
                .unwrap_or_default()
                .parse()
                .unwrap_or(true),
        }
    }

    pub async fn setup_linkerd_tracing(&self) -> Result<(), Box<dyn std::error::Error>> {
        if self.service_mesh {
            // 配置 Linkerd 特定的 tracing
            tracing_subscriber::registry()
                .with(tracing_linkerd::layer())
                .with(tracing_subscriber::EnvFilter::from_default_env())
                .init();
        }
        Ok(())
    }
}
```

### Envoy 集成

#### Envoy 配置

```yaml
static_resources:
  listeners:
  - name: otlp_listener
    address:
      socket_address:
        address: 0.0.0.0
        port_value: 4317
    filter_chains:
    - filters:
      - name: envoy.filters.network.http_connection_manager
        typed_config:
          "@type": type.googleapis.com/envoy.extensions.filters.network.http_connection_manager.v3.HttpConnectionManager
          stat_prefix: otlp
          access_log:
          - name: envoy.access_loggers.stdout
            typed_config:
              "@type": type.googleapis.com/envoy.extensions.access_loggers.stream.v3.StdoutAccessLog
          http_filters:
          - name: envoy.filters.http.router
          route_config:
            name: local_route
            virtual_hosts:
            - name: local_service
              domains: ["*"]
              routes:
              - match:
                  prefix: "/"
                route:
                  cluster: otlp_backend
                  timeout: 30s
                  retry_policy:
                    retry_on: 5xx,reset,connect-failure,refused-stream
                    num_retries: 3
                    per_try_timeout: 10s
  clusters:
  - name: otlp_backend
    connect_timeout: 30s
    type: STRICT_DNS
    lb_policy: ROUND_ROBIN
    load_assignment:
      cluster_name: otlp_backend
      endpoints:
      - lb_endpoints:
        - endpoint:
            address:
              socket_address:
                address: otlp-client
                port_value: 8080
```

### Consul Connect 集成

#### Consul 配置

```hcl
# consul.hcl
datacenter = "dc1"
data_dir = "/opt/consul"
log_level = "INFO"
server = true
bootstrap_expect = 3
ui = true
connect {
  enabled = true
}
ports {
  grpc = 8502
}
```

#### 服务注册

```rust
use consul::{Client, Config};

// Consul 服务注册
pub struct ConsulIntegration {
    client: Client,
}

impl ConsulIntegration {
    pub async fn new(consul_url: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let config = Config {
            address: consul_url.to_string(),
            ..Default::default()
        };

        let client = Client::new(config)?;

        Ok(Self { client })
    }

    pub async fn register_service(&self, service_name: &str, port: u16) -> Result<(), Box<dyn std::error::Error>> {
        let service = consul::catalog::CatalogRegistration {
            node: "otlp-client".to_string(),
            address: Some("127.0.0.1".to_string()),
            service: Some(consul::catalog::CatalogService {
                id: Some(format!("{}-1", service_name)),
                service: service_name.to_string(),
                tags: Some(vec!["otlp".to_string(), "rust".to_string()]),
                port: Some(port),
                ..Default::default()
            }),
            ..Default::default()
        };

        self.client.agent().service_register(&service).await?;
        Ok(())
    }
}
```

## ☁️ 云原生部署

### Kubernetes 集成

#### Operator 配置

```yaml
apiVersion: apiextensions.k8s.io/v1
kind: CustomResourceDefinition
metadata:
  name: otlpclients.otlp.rust.io
spec:
  group: otlp.rust.io
  versions:
  - name: v1
    served: true
    storage: true
    schema:
      openAPIV3Schema:
        type: object
        properties:
          spec:
            type: object
            properties:
              replicas:
                type: integer
                minimum: 1
              image:
                type: string
              config:
                type: object
          status:
            type: object
            properties:
              ready:
                type: boolean
              replicas:
                type: integer
  scope: Namespaced
  names:
    plural: otlpclients
    singular: otlpclient
    kind: OtlpClient
---
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otlp-client-operator
spec:
  replicas: 1
  selector:
    matchLabels:
      app: otlp-client-operator
  template:
    metadata:
      labels:
        app: otlp-client-operator
    spec:
      containers:
      - name: operator
        image: otlp-client-operator:latest
        env:
        - name: WATCH_NAMESPACE
          value: ""
```

### Docker 集成

#### 多架构构建

```dockerfile
# Dockerfile.multiarch
FROM --platform=$BUILDPLATFORM rust:1.90-alpine AS builder

ARG TARGETPLATFORM
ARG BUILDPLATFORM

RUN apk add --no-cache musl-dev openssl-dev pkgconfig

WORKDIR /app
COPY . .

RUN cargo build --release --target $(echo $TARGETPLATFORM | sed 's/linux\///')

FROM --platform=$TARGETPLATFORM alpine:latest

RUN apk --no-cache add ca-certificates tzdata

WORKDIR /app
COPY --from=builder /app/target/*/release/otlp-client ./

EXPOSE 8080
CMD ["./otlp-client"]
```

#### Docker Compose 多服务

```yaml
version: '3.8'

services:
  otlp-client:
    build:
      context: .
      dockerfile: Dockerfile.multiarch
    ports:
      - "8080:8080"
    environment:
      - RUST_LOG=info
      - OTLP_ENDPOINT=http://collector:4317
    depends_on:
      - collector
      - jaeger
      - prometheus
    networks:
      - otlp-network

  collector:
    image: otel/opentelemetry-collector:latest
    ports:
      - "4317:4317"
      - "4318:4318"
    volumes:
      - ./collector-config.yaml:/etc/collector-config.yaml:ro
    command: ["--config=/etc/collector-config.yaml"]
    networks:
      - otlp-network

  jaeger:
    image: jaegertracing/all-in-one:latest
    ports:
      - "16686:16686"
      - "14268:14268"
    environment:
      - COLLECTOR_OTLP_ENABLED=true
    networks:
      - otlp-network

  prometheus:
    image: prom/prometheus:latest
    ports:
      - "9090:9090"
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml:ro
    networks:
      - otlp-network

  grafana:
    image: grafana/grafana:latest
    ports:
      - "3000:3000"
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=admin
    networks:
      - otlp-network

networks:
  otlp-network:
    driver: bridge
```

### Helm 集成

#### Chart 结构

```text
otlp-client/
├── Chart.yaml
├── values.yaml
├── templates/
│   ├── deployment.yaml
│   ├── service.yaml
│   ├── configmap.yaml
│   ├── secret.yaml
│   └── ingress.yaml
└── charts/
```

#### Chart.yaml

```yaml
apiVersion: v2
name: otlp-client
description: OTLP Rust Client Helm Chart
type: application
version: 1.0.0
appVersion: "1.0.0"
keywords:
  - otlp
  - opentelemetry
  - rust
  - observability
home: https://github.com/example/otlp-rust
sources:
  - https://github.com/example/otlp-rust
maintainers:
  - name: OTLP Team
    email: team@example.com
```

### Operator 集成

#### Operator 实现

```rust
use kube::{
    api::{Api, ResourceExt},
    Client, CustomResourceExt,
};
use kube_runtime::{
    controller::{Action, Controller},
    watcher,
};
use serde::{Deserialize, Serialize};

#[derive(CustomResource, Deserialize, Serialize, Clone, Debug)]
#[kube(
    group = "otlp.rust.io",
    version = "v1",
    kind = "OtlpClient",
    namespaced
)]
pub struct OtlpClientSpec {
    pub replicas: i32,
    pub image: String,
    pub config: OtlpConfig,
}

#[derive(Deserialize, Serialize, Clone, Debug, Default)]
pub struct OtlpClientStatus {
    pub ready: bool,
    pub replicas: i32,
}

// Operator 控制器
pub struct OtlpClientController {
    client: Client,
}

impl OtlpClientController {
    pub fn new(client: Client) -> Self {
        Self { client }
    }

    pub async fn reconcile(
        &self,
        otlp_client: OtlpClient,
        _ctx: kube_runtime::controller::Context<Self>,
    ) -> Result<Action, kube::Error> {
        // 实现协调逻辑
        let api: Api<OtlpClient> = Api::namespaced(self.client.clone(), &otlp_client.namespace().unwrap());

        // 创建或更新 Deployment
        self.create_or_update_deployment(&otlp_client).await?;

        // 更新状态
        self.update_status(&api, &otlp_client).await?;

        Ok(Action::requeue(Duration::from_secs(300)))
    }
}
```

## 🛠️ 第三方工具集成

### 监控工具集成

#### Grafana 集成

```json
{
  "dashboard": {
    "title": "OTLP Client Dashboard",
    "panels": [
      {
        "title": "Request Rate",
        "type": "graph",
        "targets": [
          {
            "expr": "rate(otlp_requests_total[5m])",
            "legendFormat": "Requests/sec"
          }
        ]
      },
      {
        "title": "Error Rate",
        "type": "graph",
        "targets": [
          {
            "expr": "rate(otlp_errors_total[5m])",
            "legendFormat": "Errors/sec"
          }
        ]
      },
      {
        "title": "Latency",
        "type": "graph",
        "targets": [
          {
            "expr": "histogram_quantile(0.95, rate(otlp_request_duration_seconds_bucket[5m]))",
            "legendFormat": "95th percentile"
          }
        ]
      }
    ]
  }
}
```

#### Datadog 集成

```rust
use datadog_apm::Tracer;

// Datadog 集成
pub struct DatadogIntegration {
    tracer: Tracer,
}

impl DatadogIntegration {
    pub fn new(service_name: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let tracer = Tracer::new(service_name)?;
        Ok(Self { tracer })
    }

    pub async fn trace_operation<F, T>(&self, operation: &str, f: F) -> Result<T, OtlpError>
    where
        F: Future<Output = Result<T, OtlpError>>,
    {
        let span = self.tracer.start_span(operation);
        let _enter = span.enter();

        let result = f.await;

        match &result {
            Ok(_) => span.set_tag("status", "success"),
            Err(e) => {
                span.set_tag("status", "error");
                span.set_tag("error.message", e.to_string());
            }
        }

        result
    }
}
```

### 日志工具集成

#### ELK Stack 集成

```rust
use elasticsearch::{Elasticsearch, http::transport::Transport};
use serde_json::{json, Value};

// ELK Stack 集成
pub struct ElkIntegration {
    client: Elasticsearch,
}

impl ElkIntegration {
    pub async fn new(elasticsearch_url: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let transport = Transport::single_node(elasticsearch_url)?;
        let client = Elasticsearch::new(transport);

        Ok(Self { client })
    }

    pub async fn index_log(&self, log_data: &Value) -> Result<(), Box<dyn std::error::Error>> {
        let response = self.client
            .index(elasticsearch::IndexParts::Index("otlp-logs"))
            .body(log_data)
            .send()
            .await?;

        if !response.status_code().is_success() {
            return Err("Failed to index log".into());
        }

        Ok(())
    }
}
```

#### Fluentd 集成

```xml
<!-- fluentd.conf -->
<source>
  @type http
  port 9880
  bind 0.0.0.0
</source>

<filter otlp.**>
  @type parser
  key_name message
  reserve_data true
  <parse>
    @type json
  </parse>
</filter>

<match otlp.**>
  @type elasticsearch
  host elasticsearch
  port 9200
  index_name otlp-logs
  type_name _doc
</match>
```

### APM 工具集成

#### New Relic 集成

```rust
use newrelic::{App, Config};

// New Relic 集成
pub struct NewRelicIntegration {
    app: App,
}

impl NewRelicIntegration {
    pub async fn new(license_key: &str, app_name: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let config = Config::new(license_key, app_name);
        let app = App::new(config).await?;

        Ok(Self { app })
    }

    pub async fn record_metric(&self, name: &str, value: f64) -> Result<(), Box<dyn std::error::Error>> {
        self.app.record_custom_metric(name, value).await?;
        Ok(())
    }

    pub async fn start_transaction(&self, name: &str) -> Result<(), Box<dyn std::error::Error>> {
        self.app.start_web_transaction(name).await?;
        Ok(())
    }
}
```

#### AppDynamics 集成

```rust
use appdynamics::AppDynamics;

// AppDynamics 集成
pub struct AppDynamicsIntegration {
    app: AppDynamics,
}

impl AppDynamicsIntegration {
    pub fn new(controller_url: &str, account: &str, username: &str, password: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let app = AppDynamics::new(controller_url, account, username, password)?;
        Ok(Self { app })
    }

    pub async fn start_business_transaction(&self, name: &str) -> Result<(), Box<dyn std::error::Error>> {
        self.app.start_business_transaction(name).await?;
        Ok(())
    }
}
```

### CI/CD 工具集成

#### Jenkins 集成

```groovy
// Jenkinsfile
pipeline {
    agent any

    environment {
        RUST_VERSION = '1.90.0'
        DOCKER_REGISTRY = 'registry.example.com'
        IMAGE_NAME = 'otlp-client'
    }

    stages {
        stage('Checkout') {
            steps {
                checkout scm
            }
        }

        stage('Test') {
            steps {
                sh 'cargo test --all-features'
                sh 'cargo clippy --all-features -- -D warnings'
                sh 'cargo fmt -- --check'
            }
        }

        stage('Build') {
            steps {
                sh 'cargo build --release'
            }
        }

        stage('Docker Build') {
            steps {
                script {
                    def image = docker.build("${DOCKER_REGISTRY}/${IMAGE_NAME}:${env.BUILD_NUMBER}")
                    image.push()
                    image.push("latest")
                }
            }
        }

        stage('Deploy') {
            when {
                branch 'main'
            }
            steps {
                sh 'kubectl set image deployment/otlp-client otlp-client=${DOCKER_REGISTRY}/${IMAGE_NAME}:${env.BUILD_NUMBER}'
                sh 'kubectl rollout status deployment/otlp-client'
            }
        }
    }

    post {
        always {
            cleanWs()
        }
        success {
            echo 'Pipeline succeeded!'
        }
        failure {
            echo 'Pipeline failed!'
        }
    }
}
```

#### GitLab CI 集成

```yaml
# .gitlab-ci.yml
stages:
  - test
  - build
  - deploy

variables:
  RUST_VERSION: "1.90.0"
  DOCKER_REGISTRY: "registry.gitlab.com"
  IMAGE_NAME: "$CI_REGISTRY_IMAGE"

test:
  stage: test
  image: rust:$RUST_VERSION
  script:
    - cargo test --all-features
    - cargo clippy --all-features -- -D warnings
    - cargo fmt -- --check
  coverage: '/coverage: \d+\.\d+%/'

build:
  stage: build
  image: docker:latest
  services:
    - docker:dind
  before_script:
    - docker login -u $CI_REGISTRY_USER -p $CI_REGISTRY_PASSWORD $CI_REGISTRY
  script:
    - docker build -t $IMAGE_NAME:$CI_COMMIT_SHA .
    - docker push $IMAGE_NAME:$CI_COMMIT_SHA
    - docker tag $IMAGE_NAME:$CI_COMMIT_SHA $IMAGE_NAME:latest
    - docker push $IMAGE_NAME:latest
  only:
    - main

deploy:
  stage: deploy
  image: bitnami/kubectl:latest
  script:
    - kubectl set image deployment/otlp-client otlp-client=$IMAGE_NAME:$CI_COMMIT_SHA
    - kubectl rollout status deployment/otlp-client
  only:
    - main
  when: manual
```

## 🔧 自定义集成

### 自定义 Exporter

```rust
use opentelemetry::trace::{SpanExporter, SpanData};
use async_trait::async_trait;

// 自定义 Exporter
pub struct CustomExporter {
    endpoint: String,
    client: reqwest::Client,
}

impl CustomExporter {
    pub fn new(endpoint: String) -> Self {
        Self {
            endpoint,
            client: reqwest::Client::new(),
        }
    }
}

#[async_trait]
impl SpanExporter for CustomExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> opentelemetry::trace::ExportResult {
        let json_data = serde_json::to_string(&batch)
            .map_err(|_| opentelemetry::trace::TraceError::Other("Serialization failed".into()))?;

        let response = self.client
            .post(&self.endpoint)
            .header("Content-Type", "application/json")
            .body(json_data)
            .send()
            .await
            .map_err(|e| opentelemetry::trace::TraceError::Other(e.into()))?;

        if response.status().is_success() {
            Ok(())
        } else {
            Err(opentelemetry::trace::TraceError::Other("Export failed".into()))
        }
    }

    fn shutdown(&mut self) {
        // 清理资源
    }
}
```

### 自定义 Processor

```rust
use opentelemetry::trace::{SpanProcessor, SpanData};
use async_trait::async_trait;

// 自定义 Processor
pub struct CustomProcessor {
    next: Box<dyn SpanProcessor>,
    filter: Box<dyn Fn(&SpanData) -> bool + Send + Sync>,
}

impl CustomProcessor {
    pub fn new<F>(next: Box<dyn SpanProcessor>, filter: F) -> Self
    where
        F: Fn(&SpanData) -> bool + Send + Sync + 'static,
    {
        Self {
            next,
            filter: Box::new(filter),
        }
    }
}

#[async_trait]
impl SpanProcessor for CustomProcessor {
    async fn on_start(&mut self, span: &mut opentelemetry::trace::Span) {
        self.next.on_start(span).await;
    }

    async fn on_end(&mut self, span: SpanData) {
        if (self.filter)(&span) {
            self.next.on_end(span).await;
        }
    }

    async fn force_flush(&mut self) -> opentelemetry::trace::ExportResult {
        self.next.force_flush().await
    }

    async fn shutdown(&mut self) -> opentelemetry::trace::ExportResult {
        self.next.shutdown().await
    }
}
```

## 📊 集成测试

### 端到端测试

```rust
#[cfg(test)]
mod integration_tests {
    use super::*;
    use tokio_test;

    #[tokio::test]
    async fn test_full_integration() {
        // 启动测试环境
        let test_env = TestEnvironment::new().await;

        // 创建客户端
        let client = OtlpClient::new(test_env.config()).await.unwrap();

        // 发送测试数据
        let trace_data = TelemetryData::trace("integration-test");
        let result = client.send_trace_data(trace_data).await;

        assert!(result.is_ok());

        // 验证数据到达收集器
        assert!(test_env.collector().received_data().await);

        // 验证数据到达后端
        assert!(test_env.jaeger().has_trace("integration-test").await);

        // 清理
        test_env.cleanup().await;
    }
}
```

### 性能测试

```rust
#[cfg(test)]
mod performance_tests {
    use super::*;
    use criterion::{black_box, criterion_group, criterion_main, Criterion};

    fn bench_integration_throughput(c: &mut Criterion) {
        c.bench_function("integration_throughput", |b| {
            b.to_async(tokio::runtime::Runtime::new().unwrap())
                .iter(|| async {
                    let client = OtlpClient::new(test_config()).await.unwrap();
                    let data = generate_test_data(1000);
                    client.send_batch(data).await
                });
        });
    }

    criterion_group!(benches, bench_integration_throughput);
    criterion_main!(benches);
}
```

## 🔗 相关文档

- [快速开始指南](../01_GETTING_STARTED/README.md)
- [API 参考文档](../03_API_REFERENCE/README.md)
- [架构设计文档](../04_ARCHITECTURE/README.md)
- [实现指南](../05_IMPLEMENTATION/README.md)
- [部署运维指南](../06_DEPLOYMENT/README.md)

---

**集成指南版本**: 1.0.0
**最后更新**: 2025年1月
**维护者**: OTLP Rust 集成团队
