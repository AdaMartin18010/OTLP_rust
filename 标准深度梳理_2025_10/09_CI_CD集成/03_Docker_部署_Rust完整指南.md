# Docker 部署 Rust 完整指南

## 目录

- [Docker 部署 Rust 完整指南](#docker-部署-rust-完整指南)
  - [目录](#目录)
  - [一、Docker 架构与概述](#一docker-架构与概述)
    - [1.1 Rust Docker 部署架构](#11-rust-docker-部署架构)
    - [1.2 关键目标](#12-关键目标)
  - [二、基础 Dockerfile](#二基础-dockerfile)
    - [2.1 简单 Dockerfile](#21-简单-dockerfile)
  - [三、多阶段构建优化](#三多阶段构建优化)
    - [3.1 优化 Dockerfile](#31-优化-dockerfile)
    - [3.2 Alpine 最小化镜像](#32-alpine-最小化镜像)
  - [四、OTLP 集成配置](#四otlp-集成配置)
    - [4.1 环境变量配置](#41-环境变量配置)
  - [五、Docker Compose 编排](#五docker-compose-编排)
    - [5.1 完整 Docker Compose](#51-完整-docker-compose)
    - [5.2 prometheus.yml 配置](#52-prometheusyml-配置)
  - [六、生产环境优化](#六生产环境优化)
    - [6.1 生产 Dockerfile](#61-生产-dockerfile)
    - [6.2 .dockerignore 优化](#62-dockerignore-优化)
  - [七、健康检查](#七健康检查)
    - [7.1 HTTP 健康检查](#71-http-健康检查)
    - [7.2 Dockerfile 健康检查](#72-dockerfile-健康检查)
  - [八、日志与监控](#八日志与监控)
    - [8.1 结构化日志](#81-结构化日志)
    - [8.2 Docker 日志配置](#82-docker-日志配置)
  - [九、Kubernetes 部署](#九kubernetes-部署)
    - [9.1 Deployment](#91-deployment)
    - [9.2 Service](#92-service)
  - [十、安全加固](#十安全加固)
    - [10.1 安全扫描](#101-安全扫描)
    - [10.2 安全最佳实践](#102-安全最佳实践)
  - [十一、镜像优化](#十一镜像优化)
    - [11.1 镜像大小对比](#111-镜像大小对比)
    - [11.2 优化技巧](#112-优化技巧)
  - [十二、故障排查](#十二故障排查)
    - [12.1 常见问题](#121-常见问题)
      - [问题1：容器启动失败](#问题1容器启动失败)
      - [问题2：OTLP 连接失败](#问题2otlp-连接失败)
      - [问题3：依赖缺失](#问题3依赖缺失)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [最佳实践](#最佳实践)
    - [性能优化](#性能优化)
    - [生产检查清单](#生产检查清单)

---

## 一、Docker 架构与概述

### 1.1 Rust Docker 部署架构

````text
┌─────────────────────────────────────────┐
│         Rust Application                │
│  (Axum/Tonic + OpenTelemetry)           │
└──────────────┬──────────────────────────┘
               ↓
     ┌─────────────────────┐
     │  Docker Container   │
     │  (Debian/Alpine)    │
     └──────────┬──────────┘
                ↓
     ┌──────────────────────┐
     │  Docker Network      │
     │  - Jaeger (OTLP)     │
     │  - PostgreSQL        │
     │  - Redis             │
     └──────────────────────┘
````

### 1.2 关键目标

- **最小化镜像**：减小镜像体积（< 50MB）
- **快速构建**：利用缓存层（< 5分钟）
- **安全性**：非 root 用户、漏洞扫描
- **可观测性**：OTLP 追踪、日志聚合

---

## 二、基础 Dockerfile

### 2.1 简单 Dockerfile

````dockerfile
# Dockerfile - 基础版本

FROM rust:1.90 as builder

WORKDIR /app

# 复制依赖文件
COPY Cargo.toml Cargo.lock ./

# 复制源代码
COPY src ./src

# 构建 Release 版本
RUN cargo build --release

# 运行镜像
FROM debian:bookworm-slim

# 安装运行时依赖
RUN apt-get update && apt-get install -y \
    ca-certificates \
    libssl3 \
    && rm -rf /var/lib/apt/lists/*

# 复制二进制文件
COPY --from=builder /app/target/release/myapp /usr/local/bin/

# 暴露端口
EXPOSE 8000

# 启动应用
CMD ["myapp"]
````

---

## 三、多阶段构建优化

### 3.1 优化 Dockerfile

````dockerfile
# Dockerfile - 优化版本

# 构建阶段
FROM rust:1.90-slim as builder

# 安装构建依赖
RUN apt-get update && apt-get install -y \
    protobuf-compiler \
    pkg-config \
    libssl-dev \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app

# 1. 预构建依赖层（利用缓存）
COPY Cargo.toml Cargo.lock ./
RUN mkdir src && \
    echo "fn main() {println!(\"placeholder\");}" > src/main.rs && \
    cargo build --release && \
    rm -rf src target/release/deps/myapp*

# 2. 构建应用
COPY src ./src
RUN touch src/main.rs && \
    cargo build --release && \
    strip target/release/myapp

# 运行阶段
FROM debian:bookworm-slim

# 安装运行时依赖
RUN apt-get update && apt-get install -y \
    ca-certificates \
    libssl3 \
    && rm -rf /var/lib/apt/lists/* \
    && useradd -m -u 1000 appuser

# 复制二进制文件
COPY --from=builder /app/target/release/myapp /usr/local/bin/

# 切换到非 root 用户
USER appuser

# 健康检查
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
    CMD ["/usr/local/bin/myapp", "--health"]

EXPOSE 8000

CMD ["myapp"]
````

### 3.2 Alpine 最小化镜像

````dockerfile
# Dockerfile.alpine - 最小化版本

FROM rust:1.90-alpine as builder

RUN apk add --no-cache \
    musl-dev \
    protobuf-dev \
    openssl-dev

WORKDIR /app

COPY Cargo.toml Cargo.lock ./
RUN mkdir src && \
    echo "fn main() {}" > src/main.rs && \
    cargo build --release --target x86_64-unknown-linux-musl && \
    rm -rf src

COPY src ./src
RUN touch src/main.rs && \
    cargo build --release --target x86_64-unknown-linux-musl && \
    strip target/x86_64-unknown-linux-musl/release/myapp

# 运行阶段 - 使用 scratch 或 alpine
FROM alpine:3.21

RUN apk add --no-cache ca-certificates && \
    adduser -D -u 1000 appuser

COPY --from=builder /app/target/x86_64-unknown-linux-musl/release/myapp /usr/local/bin/

USER appuser

EXPOSE 8000

CMD ["myapp"]
````

---

## 四、OTLP 集成配置

### 4.1 环境变量配置

````dockerfile
# Dockerfile.otlp - OTLP 集成

FROM rust:1.90-slim as builder

# ... (构建步骤同上) ...

FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y \
    ca-certificates \
    libssl3 \
    && rm -rf /var/lib/apt/lists/* \
    && useradd -m -u 1000 appuser

COPY --from=builder /app/target/release/myapp /usr/local/bin/

USER appuser

# OTLP 环境变量
ENV OTEL_EXPORTER_OTLP_ENDPOINT=http://jaeger:4317
ENV OTEL_SERVICE_NAME=rust-app
ENV OTEL_RESOURCE_ATTRIBUTES=service.version=1.0.0,deployment.environment=production
ENV RUST_LOG=info

EXPOSE 8000

HEALTHCHECK --interval=30s --timeout=3s \
    CMD curl -f http://localhost:8000/health || exit 1

CMD ["myapp"]
````

---

## 五、Docker Compose 编排

### 5.1 完整 Docker Compose

````yaml
# docker-compose.yml

version: '3.8'

services:
  # Rust 应用
  app:
    build:
      context: .
      dockerfile: Dockerfile
    ports:
      - "8000:8000"
    environment:
      OTEL_EXPORTER_OTLP_ENDPOINT: http://jaeger:4317
      OTEL_SERVICE_NAME: rust-app
      RUST_LOG: info
      DATABASE_URL: postgresql://user:password@postgres:5432/mydb
      REDIS_URL: redis://redis:6379
    depends_on:
      postgres:
        condition: service_healthy
      redis:
        condition: service_started
      jaeger:
        condition: service_started
    networks:
      - app-network
    restart: unless-stopped
  
  # PostgreSQL
  postgres:
    image: postgres:17
    environment:
      POSTGRES_USER: user
      POSTGRES_PASSWORD: password
      POSTGRES_DB: mydb
    volumes:
      - postgres-data:/var/lib/postgresql/data
    ports:
      - "5432:5432"
    healthcheck:
      test: ["CMD-SHELL", "pg_isready -U user"]
      interval: 10s
      timeout: 5s
      retries: 5
    networks:
      - app-network
  
  # Redis
  redis:
    image: redis:8.0-alpine
    ports:
      - "6379:6379"
    volumes:
      - redis-data:/data
    networks:
      - app-network
  
  # Jaeger (OTLP)
  jaeger:
    image: jaegertracing/all-in-one:1.66
    ports:
      - "4317:4317"   # OTLP gRPC
      - "16686:16686" # Jaeger UI
    environment:
      COLLECTOR_OTLP_ENABLED: "true"
    networks:
      - app-network
  
  # Prometheus
  prometheus:
    image: prom/prometheus:v3.3.0
    ports:
      - "9090:9090"
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml
      - prometheus-data:/prometheus
    command:
      - '--config.file=/etc/prometheus/prometheus.yml'
      - '--storage.tsdb.path=/prometheus'
    networks:
      - app-network
  
  # Grafana
  grafana:
    image: grafana/grafana:11.5.0
    ports:
      - "3000:3000"
    environment:
      GF_SECURITY_ADMIN_PASSWORD: admin
    volumes:
      - grafana-data:/var/lib/grafana
    networks:
      - app-network

volumes:
  postgres-data:
  redis-data:
  prometheus-data:
  grafana-data:

networks:
  app-network:
    driver: bridge
````

### 5.2 prometheus.yml 配置

````yaml
# prometheus.yml

global:
  scrape_interval: 15s
  evaluation_interval: 15s

scrape_configs:
  - job_name: 'rust-app'
    static_configs:
      - targets: ['app:8000']
    metrics_path: '/metrics'
````

---

## 六、生产环境优化

### 6.1 生产 Dockerfile

````dockerfile
# Dockerfile.production

FROM rust:1.90-slim as builder

# 安装依赖
RUN apt-get update && apt-get install -y \
    protobuf-compiler \
    pkg-config \
    libssl-dev \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app

# 依赖缓存层
COPY Cargo.toml Cargo.lock ./
RUN mkdir src && \
    echo "fn main() {}" > src/main.rs && \
    cargo build --release && \
    rm -rf src target/release/deps/myapp*

# 构建应用
COPY . .
RUN cargo build --release && \
    strip target/release/myapp

# 最终镜像
FROM gcr.io/distroless/cc-debian12

COPY --from=builder /app/target/release/myapp /usr/local/bin/myapp

EXPOSE 8000

USER nonroot:nonroot

CMD ["/usr/local/bin/myapp"]
````

### 6.2 .dockerignore 优化

````text
# .dockerignore

# Rust
target/
**/*.rs.bk
Cargo.lock

# Git
.git/
.gitignore

# CI/CD
.github/
.gitlab-ci.yml

# 文档
*.md
docs/

# 测试
tests/
benches/

# IDE
.vscode/
.idea/
*.swp

# 临时文件
*.log
*.tmp
.DS_Store
````

---

## 七、健康检查

### 7.1 HTTP 健康检查

````rust
// src/health.rs

use axum::{
    extract::State,
    http::StatusCode,
    response::Json,
    routing::get,
    Router,
};
use serde::Serialize;

#[derive(Serialize)]
pub struct HealthResponse {
    status: String,
    version: String,
    uptime_seconds: u64,
}

pub async fn health_check(
    State(start_time): State<std::time::Instant>,
) -> Result<Json<HealthResponse>, StatusCode> {
    let uptime = start_time.elapsed().as_secs();
    
    Ok(Json(HealthResponse {
        status: "healthy".to_string(),
        version: env!("CARGO_PKG_VERSION").to_string(),
        uptime_seconds: uptime,
    }))
}

pub fn health_routes(start_time: std::time::Instant) -> Router {
    Router::new()
        .route("/health", get(health_check))
        .route("/ready", get(health_check))
        .with_state(start_time)
}
````

### 7.2 Dockerfile 健康检查

````dockerfile
# 健康检查配置
HEALTHCHECK --interval=30s --timeout=5s --start-period=10s --retries=3 \
    CMD curl -f http://localhost:8000/health || exit 1
````

---

## 八、日志与监控

### 8.1 结构化日志

````rust
// src/logging.rs

use tracing_subscriber::{
    fmt,
    layer::SubscriberExt,
    util::SubscriberInitExt,
    EnvFilter,
};

pub fn init_logging() {
    tracing_subscriber::registry()
        .with(EnvFilter::from_default_env())
        .with(fmt::layer().json())
        .init();
}
````

### 8.2 Docker 日志配置

````yaml
# docker-compose.yml 日志配置

services:
  app:
    logging:
      driver: "json-file"
      options:
        max-size: "10m"
        max-file: "3"
        labels: "service,environment"
````

---

## 九、Kubernetes 部署

### 9.1 Deployment

````yaml
# k8s/deployment.yaml

apiVersion: apps/v1
kind: Deployment
metadata:
  name: rust-app
  labels:
    app: rust-app
spec:
  replicas: 3
  selector:
    matchLabels:
      app: rust-app
  template:
    metadata:
      labels:
        app: rust-app
    spec:
      containers:
      - name: rust-app
        image: myregistry/rust-app:latest
        ports:
        - containerPort: 8000
        env:
        - name: OTEL_EXPORTER_OTLP_ENDPOINT
          value: "http://jaeger-collector:4317"
        - name: OTEL_SERVICE_NAME
          value: "rust-app"
        - name: RUST_LOG
          value: "info"
        resources:
          requests:
            memory: "128Mi"
            cpu: "100m"
          limits:
            memory: "512Mi"
            cpu: "500m"
        livenessProbe:
          httpGet:
            path: /health
            port: 8000
          initialDelaySeconds: 10
          periodSeconds: 30
        readinessProbe:
          httpGet:
            path: /ready
            port: 8000
          initialDelaySeconds: 5
          periodSeconds: 10
````

### 9.2 Service

````yaml
# k8s/service.yaml

apiVersion: v1
kind: Service
metadata:
  name: rust-app
spec:
  selector:
    app: rust-app
  ports:
  - protocol: TCP
    port: 80
    targetPort: 8000
  type: LoadBalancer
````

---

## 十、安全加固

### 10.1 安全扫描

````bash
# Trivy 漏洞扫描
docker run --rm \
  -v /var/run/docker.sock:/var/run/docker.sock \
  aquasec/trivy:latest image myregistry/rust-app:latest

# Snyk 扫描
snyk container test myregistry/rust-app:latest
````

### 10.2 安全最佳实践

````dockerfile
# Dockerfile.secure

FROM rust:1.90-slim as builder

# 非 root 用户构建
RUN useradd -m -u 1000 builder
USER builder

WORKDIR /home/builder/app

# ... (构建步骤) ...

FROM gcr.io/distroless/cc-debian12

COPY --from=builder /home/builder/app/target/release/myapp /usr/local/bin/myapp

# Distroless 默认非 root
USER nonroot:nonroot

# 只读文件系统
VOLUME /tmp

CMD ["/usr/local/bin/myapp"]
````

---

## 十一、镜像优化

### 11.1 镜像大小对比

````text
| 基础镜像            | 应用镜像大小 |
|-------------------|------------|
| rust:1.90         | ~1.5 GB    |
| debian:bookworm   | ~150 MB    |
| alpine:3.21       | ~30 MB     |
| distroless/cc     | ~25 MB     |
````

### 11.2 优化技巧

````bash
# 1. Strip 二进制文件
strip target/release/myapp

# 2. 使用 UPX 压缩
upx --best --lzma target/release/myapp

# 3. 使用 cargo-bloat 分析
cargo install cargo-bloat
cargo bloat --release

# 4. 启用 LTO
# Cargo.toml
[profile.release]
lto = true
codegen-units = 1
opt-level = "z"
strip = true
````

---

## 十二、故障排查

### 12.1 常见问题

#### 问题1：容器启动失败

````bash
# 查看日志
docker logs <container-id>

# 进入容器调试
docker exec -it <container-id> /bin/bash

# 检查端口占用
docker ps -a
netstat -tulpn | grep 8000
````

#### 问题2：OTLP 连接失败

````bash
# 测试网络连通性
docker exec <container-id> ping jaeger

# 检查 DNS 解析
docker exec <container-id> nslookup jaeger

# 检查环境变量
docker exec <container-id> env | grep OTEL
````

#### 问题3：依赖缺失

````bash
# 检查动态库
docker exec <container-id> ldd /usr/local/bin/myapp

# 安装缺失库
apt-get update && apt-get install -y libssl3
````

---

## 总结

### 核心要点

1. **多阶段构建**：分离构建和运行环境
2. **镜像优化**：最小化镜像（< 50MB）
3. **安全加固**：非 root 用户、漏洞扫描
4. **OTLP 集成**：环境变量配置
5. **健康检查**：HTTP 端点监控

### 最佳实践

- 使用 `.dockerignore` 减少上下文
- 利用缓存层加速构建
- 使用 `distroless` 最小化攻击面
- 配置健康检查和就绪探针
- 结构化日志（JSON 格式）

### 性能优化

- **构建速度**：依赖缓存层 + sccache
- **镜像大小**：Alpine/Distroless + Strip/UPX
- **运行时**：资源限制 + 水平扩展
- **网络**：Docker Network 隔离
- **监控**：Prometheus + Grafana

### 生产检查清单

- [ ] 使用多阶段构建
- [ ] 非 root 用户运行
- [ ] 配置健康检查
- [ ] 启用日志聚合
- [ ] 漏洞扫描通过
- [ ] 资源限制配置
- [ ] OTLP 追踪启用
- [ ] 备份策略制定

---

**文档版本**: v1.0  
**最后更新**: 2025-10-09  
**Rust 版本**: 1.90+  
**Docker 版本**: 27+  
**OpenTelemetry 版本**: 0.31.0+
