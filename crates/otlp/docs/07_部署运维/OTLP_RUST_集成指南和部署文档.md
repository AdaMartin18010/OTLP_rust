# OTLP Rust 集成指南和部署文档

## 📋 目录

- [快速开始](#快速开始)
- [集成指南](#集成指南)
- [部署方案](#部署方案)
- [配置管理](#配置管理)
- [安全配置](#安全配置)
- [高可用部署](#高可用部署)
- [故障恢复](#故障恢复)

## 快速开始

### 1. 环境要求

```bash
# 系统要求
- Rust 1.90+
- Linux/macOS/Windows
- 内存: 最少2GB，推荐8GB+
- 磁盘: 最少10GB可用空间
- 网络: 支持HTTP/2和gRPC

# 依赖检查
rustc --version  # 确保 >= 1.90.0
cargo --version  # 确保 >= 1.90.0
```

### 2. 安装步骤

```bash
# 克隆项目
git clone https://github.com/your-org/otlp-rust.git
cd otlp-rust

# 构建项目
cargo build --release

# 运行测试
cargo test

# 安装到系统
cargo install --path .
```

### 3. 基本配置

```toml
# config/basic.toml
[otlp]
environment = "development"
log_level = "info"

[otlp.transport]
protocol = "grpc"
endpoint = "http://localhost:4317"
timeout = 30

[otlp.resilience]
retry = { max_attempts = 3, base_delay = 100 }
timeout = { connect = 5, read = 30 }
```

### 4. 快速验证

```rust
use otlp::{OtlpClient, TraceConfig};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建客户端
    let client = OtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .build()
        .await?;

    // 发送测试追踪
    let span = client.start_span("test_span", |span| {
        span.set_attribute("test.key", "test.value");
    });

    // 模拟一些工作
    tokio::time::sleep(std::time::Duration::from_millis(100)).await;

    span.end();

    println!("测试追踪已发送！");
    Ok(())
}
```

## 集成指南

### 1. 现有项目集成

#### Web应用集成 (Axum)

```rust
// Cargo.toml
[dependencies]
otlp = "0.1.0"
axum = "0.8"
tokio = { version = "1.0", features = ["full"] }
tower = "0.5"

// main.rs
use axum::{Router, middleware, response::Json};
use otlp::{OtlpClient, middleware::OtlpMiddleware};
use tower::ServiceBuilder;

async fn setup_web_app() -> Result<Router, Box<dyn std::error::Error>> {
    // 初始化OTLP客户端
    let otlp_client = OtlpClient::builder()
        .with_endpoint("http://collector:4317")
        .build()
        .await?;

    // 创建应用
    let app = Router::new()
        .route("/api/users", get(get_users))
        .route("/api/orders", get(get_orders))
        .layer(
            ServiceBuilder::new()
                .layer(middleware::from_fn_with_state(
                    otlp_client.clone(),
                    OtlpMiddleware::tracing,
                ))
                .layer(middleware::from_fn_with_state(
                    otlp_client.clone(),
                    OtlpMiddleware::metrics,
                ))
        );

    Ok(app)
}

async fn get_users() -> Json<Vec<User>> {
    // 业务逻辑
    Json(vec![])
}

async fn get_orders() -> Json<Vec<Order>> {
    // 业务逻辑
    Json(vec![])
}
```

#### 数据库应用集成 (SQLx)

```rust
use sqlx::{PgPool, Row};
use otlp::{OtlpClient, Span};

async fn database_integration_example() -> Result<(), Box<dyn std::error::Error>> {
    let pool = PgPool::connect("postgres://user:pass@localhost/db").await?;
    let otlp_client = OtlpClient::builder()
        .with_endpoint("http://collector:4317")
        .build()
        .await?;

    // 数据库操作包装
    let result = execute_with_tracing(&otlp_client, &pool, |span, conn| async move {
        span.set_attribute("db.operation", "SELECT");
        span.set_attribute("db.table", "users");

        let rows = sqlx::query("SELECT * FROM users WHERE active = $1")
            .bind(true)
            .fetch_all(conn)
            .await?;

        span.set_attribute("db.rows_affected", rows.len() as i64);
        Ok(rows)
    }).await?;

    Ok(())
}

async fn execute_with_tracing<F, R>(
    otlp_client: &OtlpClient,
    pool: &PgPool,
    operation: F,
) -> Result<R, Box<dyn std::error::Error>>
where
    F: FnOnce(Span, &PgPool) -> R,
    R: std::future::Future<Output = Result<R, sqlx::Error>>,
{
    let span = otlp_client.start_span("database.query", |span| {
        span.set_attribute("db.system", "postgresql");
    });

    let result = operation(span.clone(), pool).await?;
    span.end();

    Ok(result)
}
```

#### 消息队列集成 (Redis)

```rust
use redis::{Client, Commands};
use otlp::{OtlpClient, Span};

async fn redis_integration_example() -> Result<(), Box<dyn std::error::Error>> {
    let client = Client::open("redis://127.0.0.1/")?;
    let mut conn = client.get_connection()?;
    let otlp_client = OtlpClient::builder()
        .with_endpoint("http://collector:4317")
        .build()
        .await?;

    // Redis操作包装
    let span = otlp_client.start_span("redis.operation", |span| {
        span.set_attribute("db.system", "redis");
        span.set_attribute("db.operation", "SET");
    });

    let result: String = conn.set("key", "value")?;

    span.set_attribute("redis.key", "key");
    span.set_attribute("redis.value", "value");
    span.end();

    Ok(())
}
```

### 2. 微服务架构集成

#### 服务发现集成 (Consul)

```rust
use consul::{Client, Config};
use otlp::{OtlpClient, ServiceRegistry};

async fn consul_integration() -> Result<(), Box<dyn std::error::Error>> {
    let consul_client = Client::new(Config::default())?;
    let otlp_client = OtlpClient::builder()
        .with_endpoint("http://collector:4317")
        .build()
        .await?;

    // 注册服务
    let service_registry = ServiceRegistry::new(consul_client, otlp_client);

    service_registry.register_service(ServiceInfo {
        name: "user-service".to_string(),
        address: "127.0.0.1".to_string(),
        port: 8080,
        health_check: "/health".to_string(),
        tags: vec!["api".to_string(), "user".to_string()],
    }).await?;

    // 服务发现
    let instances = service_registry.discover_service("user-service").await?;
    println!("发现服务实例: {:?}", instances);

    Ok(())
}
```

#### 负载均衡集成 (Nginx)

```nginx
# nginx.conf
upstream otlp_backend {
    least_conn;
    server otlp-collector-1:4317 weight=3;
    server otlp-collector-2:4317 weight=3;
    server otlp-collector-3:4317 weight=2;

    keepalive 32;
}

server {
    listen 4317;

    location / {
        grpc_pass grpc://otlp_backend;
        grpc_set_header Host $host;
        grpc_set_header X-Real-IP $remote_addr;

        # 健康检查
        health_check;
    }
}
```

### 3. 云平台集成

#### AWS集成

```rust
use aws_sdk_s3::Client as S3Client;
use otlp::{OtlpClient, CloudProvider};

async fn aws_integration() -> Result<(), Box<dyn std::error::Error>> {
    let config = aws_config::load_from_env().await;
    let s3_client = S3Client::new(&config);
    let otlp_client = OtlpClient::builder()
        .with_endpoint("http://collector:4317")
        .with_cloud_provider(CloudProvider::AWS {
            region: "us-west-2".to_string(),
            account_id: "123456789012".to_string(),
        })
        .build()
        .await?;

    // S3操作追踪
    let span = otlp_client.start_span("aws.s3.operation", |span| {
        span.set_attribute("cloud.provider", "aws");
        span.set_attribute("cloud.region", "us-west-2");
        span.set_attribute("aws.service", "s3");
    });

    // 执行S3操作
    let result = s3_client
        .put_object()
        .bucket("my-bucket")
        .key("my-key")
        .body("data".into())
        .send()
        .await?;

    span.set_attribute("aws.s3.bucket", "my-bucket");
    span.set_attribute("aws.s3.key", "my-key");
    span.end();

    Ok(())
}
```

#### Kubernetes集成

```rust
use k8s_openapi::api::core::v1::Pod;
use kube::{Api, Client};
use otlp::{OtlpClient, K8sMetadata};

async fn kubernetes_integration() -> Result<(), Box<dyn std::error::Error>> {
    let k8s_client = Client::try_default().await?;
    let pods: Api<Pod> = Api::default_namespaced(k8s_client);

    let otlp_client = OtlpClient::builder()
        .with_endpoint("http://collector:4317")
        .with_k8s_metadata(K8sMetadata {
            namespace: "default".to_string(),
            pod_name: "otlp-collector".to_string(),
            node_name: "worker-1".to_string(),
        })
        .build()
        .await?;

    // K8s操作追踪
    let span = otlp_client.start_span("k8s.pod.list", |span| {
        span.set_attribute("k8s.namespace", "default");
        span.set_attribute("k8s.operation", "list");
    });

    let pod_list = pods.list(&Default::default()).await?;

    span.set_attribute("k8s.pods.count", pod_list.items.len() as i64);
    span.end();

    Ok(())
}
```

## 部署方案

### 1. 单机部署

#### 直接运行

```bash
# 创建配置目录
mkdir -p /etc/otlp-rust
mkdir -p /var/log/otlp-rust
mkdir -p /var/lib/otlp-rust

# 复制配置文件
cp config/production.toml /etc/otlp-rust/
cp config/log4rs.yaml /etc/otlp-rust/

# 创建系统用户
useradd -r -s /bin/false otlp-rust

# 设置权限
chown -R otlp-rust:otlp-rust /var/lib/otlp-rust
chown -R otlp-rust:otlp-rust /var/log/otlp-rust

# 启动服务
sudo -u otlp-rust ./target/release/otlp-server \
    --config /etc/otlp-rust/production.toml \
    --log-config /etc/otlp-rust/log4rs.yaml
```

#### Systemd服务

```ini
# /etc/systemd/system/otlp-rust.service
[Unit]
Description=OTLP Rust Collector
After=network.target

[Service]
Type=simple
User=otlp-rust
Group=otlp-rust
ExecStart=/usr/local/bin/otlp-server \
    --config /etc/otlp-rust/production.toml \
    --log-config /etc/otlp-rust/log4rs.yaml
ExecReload=/bin/kill -HUP $MAINPID
Restart=always
RestartSec=5
StandardOutput=journal
StandardError=journal
SyslogIdentifier=otlp-rust

# 资源限制
LimitNOFILE=65536
LimitNPROC=32768

# 安全设置
NoNewPrivileges=true
ProtectSystem=strict
ProtectHome=true
ReadWritePaths=/var/lib/otlp-rust /var/log/otlp-rust

[Install]
WantedBy=multi-user.target
```

```bash
# 启用服务
sudo systemctl daemon-reload
sudo systemctl enable otlp-rust
sudo systemctl start otlp-rust

# 检查状态
sudo systemctl status otlp-rust
```

### 2. Docker部署

#### 单容器部署

```dockerfile
# Dockerfile
FROM rust:1.90-slim as builder

# 安装系统依赖
RUN apt-get update && apt-get install -y \
    pkg-config \
    libssl-dev \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app
COPY Cargo.toml Cargo.lock ./
COPY src ./src

# 构建
RUN cargo build --release

# 运行时镜像
FROM debian:bookworm-slim

# 安装运行时依赖
RUN apt-get update && apt-get install -y \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# 创建用户
RUN useradd -r -s /bin/false otlp-rust

# 复制二进制文件
COPY --from=builder /app/target/release/otlp-server /usr/local/bin/

# 创建目录
RUN mkdir -p /etc/otlp-rust /var/lib/otlp-rust /var/log/otlp-rust \
    && chown -R otlp-rust:otlp-rust /var/lib/otlp-rust /var/log/otlp-rust

# 暴露端口
EXPOSE 4317 4318 8080

# 切换用户
USER otlp-rust

# 启动命令
CMD ["otlp-server", "--config", "/etc/otlp-rust/config.toml"]
```

```bash
# 构建镜像
docker build -t otlp-rust:latest .

# 运行容器
docker run -d \
    --name otlp-collector \
    -p 4317:4317 \
    -p 4318:4318 \
    -p 8080:8080 \
    -v $(pwd)/config:/etc/otlp-rust \
    -v otlp-data:/var/lib/otlp-rust \
    otlp-rust:latest
```

#### Docker Compose部署

```yaml
# docker-compose.yml
version: '3.8'

services:
  otlp-collector:
    build: .
    container_name: otlp-collector
    ports:
      - "4317:4317"  # gRPC
      - "4318:4318"  # HTTP
      - "8080:8080"  # Admin
    environment:
      - RUST_LOG=info
      - OTLP_CONFIG_PATH=/etc/otlp-rust/config.toml
    volumes:
      - ./config:/etc/otlp-rust:ro
      - otlp-data:/var/lib/otlp-rust
      - otlp-logs:/var/log/otlp-rust
    restart: unless-stopped
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:8080/health"]
      interval: 30s
      timeout: 10s
      retries: 3
      start_period: 40s
    deploy:
      resources:
        limits:
          cpus: '2'
          memory: 4G
        reservations:
          cpus: '1'
          memory: 2G

  otlp-agent:
    build: .
    command: ["otlp-agent"]
    container_name: otlp-agent
    environment:
      - RUST_LOG=info
      - OTLP_COLLECTOR_ENDPOINT=http://otlp-collector:4317
    depends_on:
      - otlp-collector
    restart: unless-stopped
    deploy:
      replicas: 3
      resources:
        limits:
          cpus: '0.5'
          memory: 512M

volumes:
  otlp-data:
  otlp-logs:
```

### 3. Kubernetes部署

#### 基础部署

```yaml
# k8s-namespace.yaml
apiVersion: v1
kind: Namespace
metadata:
  name: otlp-system

---
# k8s-configmap.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: otlp-config
  namespace: otlp-system
data:
  config.toml: |
    [otlp]
    environment = "production"
    log_level = "info"

    [otlp.transport]
    protocol = "grpc"
    endpoints = [
        "http://otlp-collector:4317"
    ]

    [otlp.resilience]
    circuit_breaker = { failure_threshold = 5, recovery_timeout = 60 }
    retry = { max_attempts = 3, base_delay = 100 }

---
# k8s-deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otlp-collector
  namespace: otlp-system
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
        image: otlp-rust:latest
        ports:
        - containerPort: 4317
          name: grpc
        - containerPort: 4318
          name: http
        - containerPort: 8080
          name: admin
        env:
        - name: RUST_LOG
          value: "info"
        - name: OTLP_CONFIG_PATH
          value: "/etc/otlp-rust/config.toml"
        volumeMounts:
        - name: config
          mountPath: /etc/otlp-rust
        - name: data
          mountPath: /var/lib/otlp-rust
        resources:
          requests:
            memory: "2Gi"
            cpu: "1000m"
          limits:
            memory: "4Gi"
            cpu: "2000m"
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
      volumes:
      - name: config
        configMap:
          name: otlp-config
      - name: data
        persistentVolumeClaim:
          claimName: otlp-data

---
# k8s-service.yaml
apiVersion: v1
kind: Service
metadata:
  name: otlp-collector
  namespace: otlp-system
spec:
  selector:
    app: otlp-collector
  ports:
  - name: grpc
    port: 4317
    targetPort: 4317
  - name: http
    port: 4318
    targetPort: 4318
  - name: admin
    port: 8080
    targetPort: 8080
  type: ClusterIP
```

#### 高可用部署

```yaml
# k8s-hpa.yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: otlp-collector-hpa
  namespace: otlp-system
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: otlp-collector
  minReplicas: 3
  maxReplicas: 10
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

---
# k8s-pdb.yaml
apiVersion: policy/v1
kind: PodDisruptionBudget
metadata:
  name: otlp-collector-pdb
  namespace: otlp-system
spec:
  minAvailable: 2
  selector:
    matchLabels:
      app: otlp-collector
```

## 配置管理

### 1. 环境变量配置

```bash
# 基础配置
export OTLP_LOG_LEVEL=info
export OTLP_ENVIRONMENT=production
export OTLP_CONFIG_PATH=/etc/otlp-rust/config.toml

# 传输配置
export OTLP_TRANSPORT_PROTOCOL=grpc
export OTLP_TRANSPORT_ENDPOINT=http://collector:4317
export OTLP_TRANSPORT_TIMEOUT=30

# 弹性配置
export OTLP_CIRCUIT_BREAKER_THRESHOLD=5
export OTLP_RETRY_MAX_ATTEMPTS=3
export OTLP_TIMEOUT_CONNECT=5

# 分布式配置
export OTLP_CONSENSUS_ALGORITHM=raft
export OTLP_CLUSTER_SIZE=5
export OTLP_NODE_ID=node-001
```

### 2. 配置文件模板

```toml
# config/production.toml
[otlp]
environment = "production"
log_level = "info"
config_version = "1.0"

[otlp.transport]
protocol = "grpc"
endpoints = [
    "http://collector-1:4317",
    "http://collector-2:4317",
    "http://collector-3:4317"
]
timeout = 30
retry_attempts = 3
compression = "gzip"

[otlp.resilience]
circuit_breaker = {
    failure_threshold = 5,
    recovery_timeout = 60,
    half_open_max_calls = 3
}
retry = {
    max_attempts = 3,
    base_delay = 100,
    max_delay = 5000,
    backoff_multiplier = 2.0
}
timeout = {
    connect = 5,
    read = 30,
    write = 30
}

[otlp.distributed]
consensus = "raft"
cluster_size = 5
election_timeout = 1000
heartbeat_interval = 500
data_dir = "/var/lib/otlp-rust/data"

[otlp.ml_prediction]
enabled = true
models = ["random_forest", "neural_network"]
update_interval = 300
confidence_threshold = 0.8
training_data_path = "/var/lib/otlp-rust/ml-data"

[otlp.monitoring]
metrics_endpoint = "http://prometheus:9090"
alert_webhook = "http://alertmanager:9093/api/v1/alerts"
health_check_interval = 30

[otlp.security]
tls_enabled = true
cert_path = "/etc/otlp-rust/tls/cert.pem"
key_path = "/etc/otlp-rust/tls/key.pem"
ca_path = "/etc/otlp-rust/tls/ca.pem"
```

### 3. 配置验证

```rust
use otlp::config::ConfigValidator;
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
struct OtlpConfig {
    environment: String,
    log_level: String,
    transport: TransportConfig,
    resilience: ResilienceConfig,
    // ... 其他配置
}

async fn validate_config() -> Result<(), Box<dyn std::error::Error>> {
    let validator = ConfigValidator::new();

    // 验证配置文件
    let config = validator.validate_file("config/production.toml").await?;

    // 验证环境变量
    validator.validate_env_vars().await?;

    // 验证依赖服务
    validator.validate_dependencies(&config).await?;

    println!("配置验证通过！");
    Ok(())
}
```

## 安全配置

### 1. TLS配置

```toml
# config/security.toml
[otlp.security]
tls_enabled = true
cert_path = "/etc/otlp-rust/tls/server.crt"
key_path = "/etc/otlp-rust/tls/server.key"
ca_path = "/etc/otlp-rust/tls/ca.crt"
client_auth = "require"

[otlp.security.tls]
min_version = "TLSv1.2"
max_version = "TLSv1.3"
ciphers = [
    "TLS_AES_256_GCM_SHA384",
    "TLS_CHACHA20_POLY1305_SHA256",
    "TLS_AES_128_GCM_SHA256"
]
```

```bash
# 生成TLS证书
openssl genrsa -out server.key 2048
openssl req -new -key server.key -out server.csr
openssl x509 -req -days 365 -in server.csr -signkey server.key -out server.crt
```

### 2. 认证授权

```rust
use otlp::security::{AuthProvider, AuthConfig, JwtValidator};

async fn setup_authentication() -> Result<(), Box<dyn std::error::Error>> {
    let auth_config = AuthConfig {
        provider: AuthProvider::JWT {
            secret: "your-secret-key".to_string(),
            algorithm: "HS256".to_string(),
            issuer: "otlp-rust".to_string(),
            audience: "otlp-clients".to_string(),
        },
        token_expiry: Duration::from_secs(3600),
        refresh_token_expiry: Duration::from_secs(86400),
    };

    let auth_provider = AuthProvider::new(auth_config).await?;

    // 验证JWT token
    let validator = JwtValidator::new(auth_provider);

    Ok(())
}
```

### 3. 网络安全

```bash
# iptables规则
# 允许gRPC端口
iptables -A INPUT -p tcp --dport 4317 -j ACCEPT

# 允许HTTP端口
iptables -A INPUT -p tcp --dport 4318 -j ACCEPT

# 允许管理端口（仅内网）
iptables -A INPUT -p tcp --dport 8080 -s 10.0.0.0/8 -j ACCEPT

# 拒绝其他连接
iptables -A INPUT -p tcp --dport 8080 -j DROP
```

## 高可用部署1

### 1. 负载均衡配置

```nginx
# nginx-lb.conf
upstream otlp_backend {
    least_conn;
    server otlp-collector-1:4317 weight=3 max_fails=3 fail_timeout=30s;
    server otlp-collector-2:4317 weight=3 max_fails=3 fail_timeout=30s;
    server otlp-collector-3:4317 weight=2 max_fails=3 fail_timeout=30s;

    keepalive 32;
    keepalive_requests 100;
    keepalive_timeout 60s;
}

server {
    listen 4317;

    location / {
        grpc_pass grpc://otlp_backend;

        # 健康检查
        health_check uri=/health interval=10s fails=3 passes=2;

        # 错误处理
        error_page 502 503 504 /50x.html;

        # 超时设置
        grpc_read_timeout 30s;
        grpc_send_timeout 30s;
    }
}
```

### 2. 数据备份策略

```bash
#!/bin/bash
# backup.sh

# 配置
BACKUP_DIR="/var/backups/otlp-rust"
DATA_DIR="/var/lib/otlp-rust"
RETENTION_DAYS=30

# 创建备份目录
mkdir -p $BACKUP_DIR

# 创建备份
timestamp=$(date +%Y%m%d_%H%M%S)
backup_file="$BACKUP_DIR/otlp-data-$timestamp.tar.gz"

tar -czf $backup_file -C $DATA_DIR .

# 清理旧备份
find $BACKUP_DIR -name "otlp-data-*.tar.gz" -mtime +$RETENTION_DAYS -delete

echo "备份完成: $backup_file"
```

### 3. 监控告警

```yaml
# prometheus-rules.yml
groups:
- name: otlp-rust
  rules:
  - alert: OtlpCollectorDown
    expr: up{job="otlp-collector"} == 0
    for: 1m
    labels:
      severity: critical
    annotations:
      summary: "OTLP Collector is down"
      description: "OTLP Collector instance {{ $labels.instance }} is down"

  - alert: OtlpHighErrorRate
    expr: rate(otlp_errors_total[5m]) / rate(otlp_requests_total[5m]) > 0.05
    for: 2m
    labels:
      severity: warning
    annotations:
      summary: "High error rate"
      description: "Error rate is {{ $value | humanizePercentage }}"

  - alert: OtlpHighLatency
    expr: histogram_quantile(0.99, rate(otlp_latency_seconds_bucket[5m])) > 5
    for: 5m
    labels:
      severity: warning
    annotations:
      summary: "High latency"
      description: "P99 latency is {{ $value }}s"
```

## 故障恢复

### 1. 自动恢复机制

```rust
use otlp::resilience::{AutoRecovery, RecoveryStrategy};

async fn setup_auto_recovery() -> Result<(), Box<dyn std::error::Error>> {
    let recovery_strategies = vec![
        RecoveryStrategy::Restart {
            max_attempts: 3,
            backoff_duration: Duration::from_secs(5),
        },
        RecoveryStrategy::Failover {
            backup_endpoints: vec![
                "http://backup-collector-1:4317".to_string(),
                "http://backup-collector-2:4317".to_string(),
            ],
        },
        RecoveryStrategy::CircuitBreaker {
            failure_threshold: 5,
            recovery_timeout: Duration::from_secs(60),
        },
    ];

    let auto_recovery = AutoRecovery::new(recovery_strategies);
    auto_recovery.start().await?;

    Ok(())
}
```

### 2. 灾难恢复计划

```bash
#!/bin/bash
# disaster-recovery.sh

# 1. 停止服务
systemctl stop otlp-rust

# 2. 恢复数据
tar -xzf /var/backups/otlp-rust/otlp-data-latest.tar.gz -C /var/lib/otlp-rust/

# 3. 验证配置
otlp-server --config /etc/otlp-rust/config.toml --validate

# 4. 启动服务
systemctl start otlp-rust

# 5. 验证服务
curl -f http://localhost:8080/health

echo "灾难恢复完成"
```

### 3. 故障排查指南

```markdown
# 故障排查检查清单

## 📖 服务状态检查
- [ ] 服务是否正在运行？
- [ ] 端口是否正常监听？
- [ ] 健康检查是否通过？

## 📝 日志检查
- [ ] 应用日志是否有错误？
- [ ] 系统日志是否有异常？
- [ ] 网络连接是否正常？

## 🔍 资源检查
- [ ] CPU使用率是否过高？
- [ ] 内存使用率是否过高？
- [ ] 磁盘空间是否充足？
- [ ] 网络带宽是否充足？

## ⚙️ 配置检查
- [ ] 配置文件是否正确？
- [ ] 环境变量是否设置？
- [ ] 依赖服务是否可用？

## ⚡ 性能检查
- [ ] 响应时间是否正常？
- [ ] 吞吐量是否正常？
- [ ] 错误率是否正常？
```

## 总结

本文档提供了OTLP Rust项目的完整集成指南和部署文档，包括：

1. **快速开始**：环境要求、安装步骤、基本配置
2. **集成指南**：Web应用、数据库、消息队列、微服务、云平台集成
3. **部署方案**：单机、Docker、Kubernetes部署
4. **配置管理**：环境变量、配置文件、配置验证
5. **安全配置**：TLS、认证授权、网络安全
6. **高可用部署**：负载均衡、数据备份、监控告警
7. **故障恢复**：自动恢复、灾难恢复、故障排查

这些指南将帮助您在不同环境中成功部署和运维OTLP Rust项目，确保系统的高可用性和稳定性。

