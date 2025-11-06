# Docker 容器可观测性 - Docker Container Observability

**创建日期**: 2025年10月29日
**最后更新**: 2025年10月29日
**状态**: ✅ 完整
**优先级**: 🔴 高

---

## 📋 目录

- [Docker 容器可观测性 - Docker Container Observability](#docker-容器可观测性---docker-container-observability)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [为什么需要容器可观测性？](#为什么需要容器可观测性)
    - [核心目标](#核心目标)
  - [Docker 与 OTLP 集成](#docker-与-otlp-集成)
    - [1. 基础集成架构](#1-基础集成架构)
    - [2. Dockerfile 配置示例](#2-dockerfile-配置示例)
    - [3. Docker Compose 配置](#3-docker-compose-配置)
    - [4. OpenTelemetry Collector 配置](#4-opentelemetry-collector-配置)
  - [容器追踪架构](#容器追踪架构)
    - [1. 容器元数据注入](#1-容器元数据注入)
    - [2. Docker 标签注入](#2-docker-标签注入)
  - [实践指南](#实践指南)
    - [1. 应用代码集成](#1-应用代码集成)
    - [2. 本地开发和测试](#2-本地开发和测试)
  - [性能优化](#性能优化)
    - [1. 镜像大小优化](#1-镜像大小优化)
    - [2. 构建缓存优化](#2-构建缓存优化)
    - [3. 运行时性能优化](#3-运行时性能优化)
  - [生产部署](#生产部署)
    - [1. Kubernetes 部署](#1-kubernetes-部署)
    - [2. 自动扩缩容](#2-自动扩缩容)
  - [故障排查](#故障排查)
    - [1. 常见问题](#1-常见问题)
    - [2. 调试工具](#2-调试工具)
  - [最佳实践](#最佳实践)
    - [1. 镜像安全](#1-镜像安全)
    - [2. 性能最佳实践](#2-性能最佳实践)
    - [3. 可观测性最佳实践](#3-可观测性最佳实践)
    - [4. 开发体验](#4-开发体验)
  - [工具和资源](#工具和资源)
    - [相关工具](#相关工具)
    - [学习资源](#学习资源)

---

## 概述

### 为什么需要容器可观测性？

在容器化环境中，应用程序的可观测性面临独特挑战：

- 🔄 **短生命周期**: 容器可能频繁创建和销毁
- 🌐 **动态网络**: 容器IP地址动态分配
- 📦 **多层架构**: 应用、容器运行时、主机OS
- 🔍 **分布式追踪**: 跨容器的请求链路追踪
- 📊 **资源监控**: CPU、内存、网络、磁盘IO

### 核心目标

- ✅ 全面追踪容器内应用的行为
- ✅ 关联容器元数据与应用追踪数据
- ✅ 优化容器镜像的可观测性配置
- ✅ 实现高效的日志、指标和追踪收集
- ✅ 最小化性能开销

---

## Docker 与 OTLP 集成

### 1. 基础集成架构

```text
┌────────────────────────────────────────────────────────┐
│                    Docker Host                         │
│                                                        │
│  ┌──────────────┐    ┌──────────────┐                  │
│  │  Container 1 │    │  Container 2 │                  │
│  │              │    │              │                  │
│  │  ┌────────┐  │    │  ┌────────┐  │                  │
│  │  │  App   │  │    │  │  App   │  │                  │
│  │  │  OTLP  │  │    │  │  OTLP  │  │                  │
│  │  │  SDK   │  │    │  │  SDK   │  │                  │
│  │  └────┬───┘  │    │  └────┬───┘  │                  │
│  └───────┼──────┘    └───────┼──────┘                  │
│          │                   │                         │
│          └───────┬───────────┘                         │
│                  │                                     │
│         ┌────────▼────────┐                            │
│         │  OTLP Collector │                            │
│         │   (Sidecar)     │                            │
│         └────────┬────────┘                            │
└──────────────────┼─────────────────────────────────────┘
                   │
          ┌────────▼────────┐
          │   Jaeger/Tempo  │
          │   Prometheus    │
          └─────────────────┘
```

### 2. Dockerfile 配置示例

**多阶段构建 - 开发环境**:

```dockerfile
# ========================================
# Stage 1: 构建阶段
# ========================================
FROM rust:1.90-bookworm AS builder

# 设置工作目录
WORKDIR /app

# 安装依赖
RUN apt-get update && apt-get install -y \
    protobuf-compiler \
    libssl-dev \
    pkg-config \
    && rm -rf /var/lib/apt/lists/*

# 复制依赖文件
COPY Cargo.toml Cargo.lock ./
COPY crates ./crates

# 构建发布版本
RUN cargo build --release

# ========================================
# Stage 2: 运行阶段
# ========================================
FROM debian:bookworm-slim

# 安装运行时依赖
RUN apt-get update && apt-get install -y \
    ca-certificates \
    libssl3 \
    curl \
    && rm -rf /var/lib/apt/lists/*

# 创建非root用户
RUN useradd -m -u 1000 appuser

# 设置工作目录
WORKDIR /app

# 从构建阶段复制二进制文件
COPY --from=builder /app/target/release/otlp-web-service /usr/local/bin/

# 复制配置文件
COPY config/production.toml /app/config/config.toml

# 设置权限
RUN chown -R appuser:appuser /app

# 切换到非root用户
USER appuser

# 暴露端口
EXPOSE 8080 9090

# 环境变量
ENV RUST_LOG=info
ENV OTLP_EXPORTER_ENDPOINT=http://otel-collector:4317
ENV OTLP_SERVICE_NAME=web-service
ENV OTLP_RESOURCE_ATTRIBUTES="service.namespace=production,deployment.environment=prod"

# 健康检查
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
  CMD curl -f http://localhost:8080/health || exit 1

# 启动命令
CMD ["otlp-web-service"]
```

**优化的生产环境 Dockerfile**:

```dockerfile
# ========================================
# Stage 1: 缓存依赖
# ========================================
FROM rust:1.90-alpine AS deps

WORKDIR /app

# 安装构建依赖
RUN apk add --no-cache musl-dev pkgconfig openssl-dev protobuf-dev

# 只复制依赖文件，利用Docker缓存
COPY Cargo.toml Cargo.lock ./
RUN mkdir src && echo "fn main() {}" > src/main.rs
RUN cargo build --release
RUN rm -rf src

# ========================================
# Stage 2: 构建应用
# ========================================
FROM rust:1.90-alpine AS builder

WORKDIR /app

# 安装构建依赖
RUN apk add --no-cache musl-dev pkgconfig openssl-dev protobuf-dev

# 从deps阶段复制依赖
COPY --from=deps /app/target /app/target
COPY --from=deps /usr/local/cargo /usr/local/cargo

# 复制源代码
COPY . .

# 构建应用
RUN cargo build --release --bin otlp-web-service

# Strip 二进制文件以减小体积
RUN strip /app/target/release/otlp-web-service

# ========================================
# Stage 3: 最小运行时镜像
# ========================================
FROM alpine:3.19

# 安装最小运行时依赖
RUN apk add --no-cache \
    ca-certificates \
    libgcc \
    curl \
    && rm -rf /var/cache/apk/*

# 创建非root用户
RUN addgroup -g 1000 appuser && \
    adduser -D -u 1000 -G appuser appuser

WORKDIR /app

# 从构建阶段复制二进制文件
COPY --from=builder /app/target/release/otlp-web-service /usr/local/bin/

# 设置权限
RUN chown -R appuser:appuser /app

USER appuser

EXPOSE 8080

ENV RUST_LOG=info
ENV RUST_BACKTRACE=1
ENV OTLP_EXPORTER_ENDPOINT=http://otel-collector:4317

HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
  CMD curl -f http://localhost:8080/health || exit 1

CMD ["otlp-web-service"]
```

### 3. Docker Compose 配置

**完整的可观测性栈**:

```yaml
version: '3.9'

services:
  # ========================================
  # Web 应用服务
  # ========================================
  web-service:
    build:
      context: .
      dockerfile: docker/Dockerfile.production
    container_name: otlp-web-service
    ports:
      - "8080:8080"
    environment:
      RUST_LOG: info
      OTLP_EXPORTER_ENDPOINT: http://otel-collector:4317
      OTLP_SERVICE_NAME: web-service
      OTLP_SERVICE_VERSION: 1.0.0
      OTLP_DEPLOYMENT_ENVIRONMENT: docker-compose
    depends_on:
      - otel-collector
      - postgres
      - redis
    networks:
      - otlp-network
    restart: unless-stopped
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:8080/health"]
      interval: 30s
      timeout: 3s
      retries: 3
      start_period: 10s

  # ========================================
  # OpenTelemetry Collector
  # ========================================
  otel-collector:
    image: otel/opentelemetry-collector-contrib:0.95.0
    container_name: otel-collector
    command: ["--config=/etc/otel-collector-config.yaml"]
    volumes:
      - ./config/otel-collector-config.yaml:/etc/otel-collector-config.yaml
    ports:
      - "4317:4317"   # OTLP gRPC receiver
      - "4318:4318"   # OTLP HTTP receiver
      - "8888:8888"   # Prometheus metrics
      - "13133:13133" # Health check
    networks:
      - otlp-network
    restart: unless-stopped

  # ========================================
  # Jaeger - 分布式追踪后端
  # ========================================
  jaeger:
    image: jaegertracing/all-in-one:1.54
    container_name: jaeger
    ports:
      - "16686:16686" # Jaeger UI
      - "14250:14250" # gRPC
      - "14268:14268" # HTTP
    environment:
      COLLECTOR_OTLP_ENABLED: "true"
    networks:
      - otlp-network
    restart: unless-stopped

  # ========================================
  # Prometheus - 指标存储
  # ========================================
  prometheus:
    image: prom/prometheus:v2.50.0
    container_name: prometheus
    command:
      - '--config.file=/etc/prometheus/prometheus.yml'
      - '--storage.tsdb.path=/prometheus'
      - '--web.console.libraries=/usr/share/prometheus/console_libraries'
      - '--web.console.templates=/usr/share/prometheus/consoles'
    volumes:
      - ./config/prometheus.yml:/etc/prometheus/prometheus.yml
      - prometheus-data:/prometheus
    ports:
      - "9090:9090"
    networks:
      - otlp-network
    restart: unless-stopped

  # ========================================
  # Grafana - 可视化
  # ========================================
  grafana:
    image: grafana/grafana:10.3.3
    container_name: grafana
    ports:
      - "3000:3000"
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=admin
      - GF_USERS_ALLOW_SIGN_UP=false
    volumes:
      - grafana-data:/var/lib/grafana
      - ./config/grafana/dashboards:/etc/grafana/provisioning/dashboards
      - ./config/grafana/datasources:/etc/grafana/provisioning/datasources
    networks:
      - otlp-network
    restart: unless-stopped
    depends_on:
      - prometheus
      - jaeger

  # ========================================
  # PostgreSQL - 数据库
  # ========================================
  postgres:
    image: postgres:16-alpine
    container_name: postgres
    environment:
      POSTGRES_USER: appuser
      POSTGRES_PASSWORD: apppass
      POSTGRES_DB: appdb
    volumes:
      - postgres-data:/var/lib/postgresql/data
    ports:
      - "5432:5432"
    networks:
      - otlp-network
    restart: unless-stopped
    healthcheck:
      test: ["CMD-SHELL", "pg_isready -U appuser"]
      interval: 10s
      timeout: 5s
      retries: 5

  # ========================================
  # Redis - 缓存
  # ========================================
  redis:
    image: redis:7-alpine
    container_name: redis
    ports:
      - "6379:6379"
    volumes:
      - redis-data:/data
    networks:
      - otlp-network
    restart: unless-stopped
    healthcheck:
      test: ["CMD", "redis-cli", "ping"]
      interval: 10s
      timeout: 3s
      retries: 3

networks:
  otlp-network:
    driver: bridge

volumes:
  prometheus-data:
  grafana-data:
  postgres-data:
  redis-data:
```

### 4. OpenTelemetry Collector 配置

**config/otel-collector-config.yaml**:

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318

  # Prometheus 指标收集
  prometheus:
    config:
      scrape_configs:
        - job_name: 'otel-collector'
          scrape_interval: 10s
          static_configs:
            - targets: ['localhost:8888']

processors:
  # 批处理器 - 提高性能
  batch:
    timeout: 10s
    send_batch_size: 1024

  # 资源处理器 - 添加容器元数据
  resource:
    attributes:
      - key: deployment.environment
        value: docker-compose
        action: insert
      - key: service.instance.id
        from_attribute: container.id
        action: insert

  # 资源检测器 - 自动检测容器信息
  resourcedetection:
    detectors: [docker, system, env]
    timeout: 5s

  # 内存限制器 - 防止OOM
  memory_limiter:
    check_interval: 1s
    limit_mib: 512
    spike_limit_mib: 128

  # 采样处理器 - 降低数据量
  probabilistic_sampler:
    sampling_percentage: 100  # 生产环境可降低到10-20

exporters:
  # Jaeger 导出器
  otlp/jaeger:
    endpoint: jaeger:4317
    tls:
      insecure: true

  # Prometheus 导出器
  prometheus:
    endpoint: "0.0.0.0:8889"
    namespace: otlp

  # 日志导出器（调试用）
  logging:
    loglevel: debug

  # 文件导出器（备份）
  file:
    path: /var/log/otel/traces.json

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, resourcedetection, resource, batch, probabilistic_sampler]
      exporters: [otlp/jaeger, logging]

    metrics:
      receivers: [otlp, prometheus]
      processors: [memory_limiter, resourcedetection, resource, batch]
      exporters: [prometheus, logging]

    logs:
      receivers: [otlp]
      processors: [memory_limiter, resourcedetection, resource, batch]
      exporters: [logging, file]

  extensions: [health_check, pprof]

extensions:
  health_check:
    endpoint: 0.0.0.0:13133
  pprof:
    endpoint: 0.0.0.0:1777
```

---

## 容器追踪架构

### 1. 容器元数据注入

**自动注入容器信息**:

```rust
use opentelemetry::sdk::Resource;
use opentelemetry::KeyValue;
use std::env;

/// 构建包含容器元数据的资源
pub fn build_container_resource() -> Resource {
    let mut attributes = vec![
        // 基础服务信息
        KeyValue::new("service.name", env::var("OTLP_SERVICE_NAME").unwrap_or_else(|_| "unknown".to_string())),
        KeyValue::new("service.version", env::var("OTLP_SERVICE_VERSION").unwrap_or_else(|_| "0.0.0".to_string())),

        // 容器信息
        KeyValue::new("container.id", get_container_id()),
        KeyValue::new("container.name", hostname()),
        KeyValue::new("container.runtime", "docker"),

        // 部署信息
        KeyValue::new("deployment.environment", env::var("OTLP_DEPLOYMENT_ENVIRONMENT").unwrap_or_else(|_| "development".to_string())),
    ];

    // 从环境变量添加额外的资源属性
    if let Ok(attrs) = env::var("OTLP_RESOURCE_ATTRIBUTES") {
        for attr in attrs.split(',') {
            if let Some((key, value)) = attr.split_once('=') {
                attributes.push(KeyValue::new(key.to_string(), value.to_string()));
            }
        }
    }

    Resource::new(attributes)
}

/// 获取容器ID（从cgroup信息）
fn get_container_id() -> String {
    use std::fs;

    // 从 /proc/self/cgroup 读取容器ID
    if let Ok(content) = fs::read_to_string("/proc/self/cgroup") {
        for line in content.lines() {
            if line.contains("docker") {
                if let Some(id) = line.split('/').last() {
                    return id.to_string();
                }
            }
        }
    }

    // 备选：从 HOSTNAME 环境变量获取
    env::var("HOSTNAME").unwrap_or_else(|_| "unknown".to_string())
}

/// 获取主机名
fn hostname() -> String {
    env::var("HOSTNAME").unwrap_or_else(|_| "unknown".to_string())
}
```

### 2. Docker 标签注入

**docker-compose.yml 标签配置**:

```yaml
services:
  web-service:
    labels:
      # OpenTelemetry 标签
      io.opentelemetry.service.name: "web-service"
      io.opentelemetry.service.version: "1.0.0"
      io.opentelemetry.deployment.environment: "production"

      # 自定义业务标签
      app.team: "platform"
      app.component: "api-gateway"
      app.tier: "frontend"
```

**从标签读取配置**:

```rust
use bollard::Docker;
use bollard::container::InspectContainerOptions;

/// 从 Docker 标签读取配置
pub async fn load_config_from_labels() -> Result<HashMap<String, String>, Box<dyn std::error::Error>> {
    let docker = Docker::connect_with_local_defaults()?;
    let container_id = get_container_id();

    let container = docker
        .inspect_container(&container_id, None::<InspectContainerOptions>)
        .await?;

    if let Some(config) = container.config {
        if let Some(labels) = config.labels {
            return Ok(labels);
        }
    }

    Ok(HashMap::new())
}
```

---

## 实践指南

### 1. 应用代码集成

**Axum 应用完整示例**:

```rust
use axum::{
    routing::get,
    Router,
    Extension,
};
use opentelemetry::sdk::Resource;
use opentelemetry::trace::TracerProvider;
use opentelemetry_otlp::WithExportConfig;
use std::env;
use tower_http::trace::TraceLayer;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 初始化追踪
    let tracer_provider = init_tracer_provider()?;

    // 2. 设置全局追踪器
    opentelemetry::global::set_tracer_provider(tracer_provider.clone());

    // 3. 初始化 tracing subscriber
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_opentelemetry::layer().with_tracer(tracer_provider.tracer("web-service")))
        .init();

    // 4. 构建应用
    let app = Router::new()
        .route("/", get(handler))
        .route("/health", get(health_check))
        .layer(TraceLayer::new_for_http())
        .layer(Extension(tracer_provider));

    // 5. 启动服务器
    let addr = "0.0.0.0:8080".parse()?;
    tracing::info!("Starting server on {}", addr);

    axum::Server::bind(&addr)
        .serve(app.into_make_service())
        .with_graceful_shutdown(shutdown_signal())
        .await?;

    // 6. 清理
    opentelemetry::global::shutdown_tracer_provider();

    Ok(())
}

/// 初始化追踪提供器
fn init_tracer_provider() -> Result<opentelemetry::sdk::trace::TracerProvider, Box<dyn std::error::Error>> {
    let endpoint = env::var("OTLP_EXPORTER_ENDPOINT")
        .unwrap_or_else(|_| "http://localhost:4317".to_string());

    let otlp_exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint(&endpoint);

    let tracer_provider = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(otlp_exporter)
        .with_trace_config(
            opentelemetry::sdk::trace::config()
                .with_resource(build_container_resource())
                .with_sampler(opentelemetry::sdk::trace::Sampler::AlwaysOn)
        )
        .install_batch(opentelemetry::runtime::Tokio)?;

    Ok(tracer_provider)
}

/// 处理器示例
#[tracing::instrument]
async fn handler() -> &'static str {
    tracing::info!("Handling request");
    "Hello from Docker container!"
}

/// 健康检查
async fn health_check() -> &'static str {
    "OK"
}

/// 优雅关闭信号
async fn shutdown_signal() {
    use tokio::signal;

    let ctrl_c = async {
        signal::ctrl_c()
            .await
            .expect("failed to install Ctrl+C handler");
    };

    #[cfg(unix)]
    let terminate = async {
        signal::unix::signal(signal::unix::SignalKind::terminate())
            .expect("failed to install signal handler")
            .recv()
            .await;
    };

    #[cfg(not(unix))]
    let terminate = std::future::pending::<()>();

    tokio::select! {
        _ = ctrl_c => {},
        _ = terminate => {},
    }

    tracing::info!("Signal received, starting graceful shutdown");
}
```

### 2. 本地开发和测试

**快速启动命令**:

```bash
# 构建并启动所有服务
docker-compose up -d

# 查看日志
docker-compose logs -f web-service

# 测试API
curl http://localhost:8080/

# 访问 Jaeger UI
open http://localhost:16686

# 访问 Grafana
open http://localhost:3000  # admin/admin

# 停止服务
docker-compose down

# 清理数据卷
docker-compose down -v
```

**Makefile 自动化**:

```makefile
.PHONY: build run logs stop clean test

# 构建镜像
build:
 docker-compose build

# 启动服务
run:
 docker-compose up -d

# 查看日志
logs:
 docker-compose logs -f web-service

# 停止服务
stop:
 docker-compose down

# 清理
clean:
 docker-compose down -v
 docker system prune -f

# 测试
test:
 curl -s http://localhost:8080/health
 @echo "\nJaeger UI: http://localhost:16686"
 @echo "Grafana: http://localhost:3000"

# 重启
restart: stop run

# 完整重建
rebuild: clean build run
```

---

## 性能优化

### 1. 镜像大小优化

**优化对比**:

| 策略 | 镜像大小 | 构建时间 | 性能 |
|------|---------|---------|------|
| 基础Rust镜像 | ~1.5GB | 快 | 好 |
| Debian Slim | ~150MB | 中 | 好 |
| Alpine | ~50MB | 慢 | 很好 |
| Distroless | ~30MB | 慢 | 优秀 |

**使用 Distroless**:

```dockerfile
FROM gcr.io/distroless/cc-debian12

COPY --from=builder /app/target/release/otlp-web-service /usr/local/bin/

EXPOSE 8080

CMD ["/usr/local/bin/otlp-web-service"]
```

### 2. 构建缓存优化

```dockerfile
# 利用 Docker BuildKit 缓存
# syntax=docker/dockerfile:1

FROM rust:1.90 AS builder

WORKDIR /app

# 启用 BuildKit 缓存挂载
RUN --mount=type=cache,target=/usr/local/cargo/registry \
    --mount=type=cache,target=/app/target \
    cargo build --release

# 复制最终产物
RUN --mount=type=cache,target=/app/target \
    cp /app/target/release/otlp-web-service /usr/local/bin/
```

**构建命令**:

```bash
# 使用 BuildKit
DOCKER_BUILDKIT=1 docker build -t otlp-web-service:latest .

# 使用 docker buildx
docker buildx build --cache-from=type=local,src=/tmp/cache \
    --cache-to=type=local,dest=/tmp/cache \
    -t otlp-web-service:latest .
```

### 3. 运行时性能优化

**资源限制**:

```yaml
services:
  web-service:
    deploy:
      resources:
        limits:
          cpus: '2.0'
          memory: 1G
        reservations:
          cpus: '1.0'
          memory: 512M

    # 日志驱动优化
    logging:
      driver: "json-file"
      options:
        max-size: "10m"
        max-file: "3"

    # 安全选项
    security_opt:
      - no-new-privileges:true

    # 只读根文件系统
    read_only: true
    tmpfs:
      - /tmp
      - /app/tmp
```

---

## 生产部署

### 1. Kubernetes 部署

**Deployment 配置**:

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otlp-web-service
  namespace: production
  labels:
    app: otlp-web-service
    version: v1.0.0
spec:
  replicas: 3
  selector:
    matchLabels:
      app: otlp-web-service
  template:
    metadata:
      labels:
        app: otlp-web-service
        version: v1.0.0
      annotations:
        prometheus.io/scrape: "true"
        prometheus.io/port: "9090"
        prometheus.io/path: "/metrics"
    spec:
      containers:
      - name: web-service
        image: registry.example.com/otlp-web-service:v1.0.0
        ports:
        - containerPort: 8080
          name: http
          protocol: TCP
        - containerPort: 9090
          name: metrics
          protocol: TCP
        env:
        - name: RUST_LOG
          value: "info"
        - name: OTLP_EXPORTER_ENDPOINT
          value: "http://otel-collector.observability.svc.cluster.local:4317"
        - name: OTLP_SERVICE_NAME
          value: "web-service"
        - name: OTLP_SERVICE_VERSION
          value: "1.0.0"
        - name: OTLP_DEPLOYMENT_ENVIRONMENT
          value: "production"
        - name: OTLP_RESOURCE_ATTRIBUTES
          value: "k8s.namespace=production,k8s.cluster.name=prod-cluster"
        resources:
          requests:
            cpu: "500m"
            memory: "512Mi"
          limits:
            cpu: "2000m"
            memory: "1Gi"
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 10
          periodSeconds: 30
          timeoutSeconds: 5
          failureThreshold: 3
        readinessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 5
          periodSeconds: 10
          timeoutSeconds: 3
          failureThreshold: 3
        securityContext:
          runAsNonRoot: true
          runAsUser: 1000
          readOnlyRootFilesystem: true
          allowPrivilegeEscalation: false
          capabilities:
            drop:
            - ALL
      securityContext:
        fsGroup: 1000
```

### 2. 自动扩缩容

**HPA 配置**:

```yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: otlp-web-service-hpa
  namespace: production
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: otlp-web-service
  minReplicas: 3
  maxReplicas: 20
  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
  - type: Resource
    resource:
      name: memory
      target:
        type: Utilization
        averageUtilization: 80
  - type: Pods
    pods:
      metric:
        name: http_requests_per_second
      target:
        type: AverageValue
        averageValue: "1000"
  behavior:
    scaleDown:
      stabilizationWindowSeconds: 300
      policies:
      - type: Percent
        value: 50
        periodSeconds: 60
    scaleUp:
      stabilizationWindowSeconds: 0
      policies:
      - type: Percent
        value: 100
        periodSeconds: 60
      - type: Pods
        value: 4
        periodSeconds: 60
      selectPolicy: Max
```

---

## 故障排查

### 1. 常见问题

**问题 1: 无法连接到 OTLP Collector**:

```bash
# 检查网络连通性
docker exec web-service curl -v http://otel-collector:4317

# 检查 Collector 日志
docker logs otel-collector

# 检查容器网络
docker network inspect otlp-network
```

**问题 2: 追踪数据丢失**:

```rust
// 确保在应用退出前刷新追踪数据
opentelemetry::global::shutdown_tracer_provider();

// 或使用更长的批处理超时
.with_batch_config(
    opentelemetry::sdk::trace::BatchConfig::default()
        .with_max_queue_size(2048)
        .with_scheduled_delay(std::time::Duration::from_secs(5))
)
```

**问题 3: 容器内存溢出**:

```yaml
# 限制 OTLP SDK 内存使用
services:
  web-service:
    environment:
      OTEL_BSP_MAX_QUEUE_SIZE: "1024"
      OTEL_BSP_SCHEDULE_DELAY: "5000"
      OTEL_BSP_EXPORT_TIMEOUT: "30000"
```

### 2. 调试工具

**容器内调试**:

```bash
# 进入容器
docker exec -it web-service sh

# 检查环境变量
env | grep OTLP

# 测试网络
nc -zv otel-collector 4317

# 检查日志
tail -f /var/log/app.log
```

---

## 最佳实践

### 1. 镜像安全

- ✅ 使用非 root 用户运行
- ✅ 只读根文件系统
- ✅ 最小化镜像层数
- ✅ 定期扫描漏洞
- ✅ 使用私有镜像仓库
- ✅ 启用内容信任

### 2. 性能最佳实践

- ✅ 使用多阶段构建减小镜像
- ✅ 利用BuildKit缓存加速构建
- ✅ 合理设置资源限制
- ✅ 启用日志轮转
- ✅ 使用健康检查

### 3. 可观测性最佳实践

- ✅ 注入容器元数据
- ✅ 使用统一的追踪上下文
- ✅ 配置合理的采样率
- ✅ 监控容器资源使用
- ✅ 设置告警规则

### 4. 开发体验

- ✅ 使用 docker-compose 本地开发
- ✅ 配置热重载
- ✅ 统一环境变量管理
- ✅ 文档化部署流程
- ✅ 自动化测试

---

## 工具和资源

### 相关工具

- **[Docker BuildKit](https://docs.docker.com/build/buildkit/)** - 高级构建引擎
- **[Hadolint](https://github.com/hadolint/hadolint)** - Dockerfile linter
- **[Dive](https://github.com/wagoodman/dive)** - 镜像层分析工具
- **[Trivy](https://github.com/aquasecurity/trivy)** - 漏洞扫描器

### 学习资源

- [Docker 最佳实践](https://docs.docker.com/develop/dev-best-practices/)
- [OpenTelemetry Docker 集成](https://opentelemetry.io/docs/instrumentation/docker/)
- [Rust Docker 指南](https://docs.docker.com/language/rust/)

---

**维护者**: OTLP_rust 项目团队
**最后更新**: 2025年10月29日
**下一步**: 探索 [WasmEdge 可观测性](./wasmedge_observability.md)
