# 🚀 OTLP Rust 部署和运维指南

## 📋 概述

本指南提供了 OTLP Rust 项目的完整部署和运维方案，包括开发环境搭建、生产环境部署、监控配置和故障排除等内容。

## 🛠️ 开发环境

### 系统要求

- **Rust**: 1.90+
- **操作系统**: Linux, macOS, Windows
- **内存**: 最少 4GB RAM
- **磁盘**: 最少 2GB 可用空间

### 环境搭建

```bash
# 1. 安装 Rust (如果未安装)
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source ~/.cargo/env

# 2. 克隆项目
git clone <repository-url>
cd OTLP_rust/otlp

# 3. 安装依赖
cargo build

# 4. 运行测试
cargo test

# 5. 运行示例
cargo run --example resilience_usage
```

### 开发工具配置

```toml
# .vscode/settings.json
{
    "rust-analyzer.checkOnSave.command": "clippy",
    "rust-analyzer.checkOnSave.extraArgs": ["--", "-W", "clippy::all"],
    "editor.formatOnSave": true,
    "rust-analyzer.cargo.features": "all"
}
```

## 🏭 生产环境部署

### 1. 二进制部署

#### 构建发布版本

```bash
# 构建优化版本
cargo build --release

# 检查二进制文件
ls -la target/release/otlp
```

#### 系统服务配置

```ini
# /etc/systemd/system/otlp.service
[Unit]
Description=OTLP Rust Service
After=network.target

[Service]
Type=simple
User=otlp
Group=otlp
WorkingDirectory=/opt/otlp
ExecStart=/opt/otlp/bin/otlp
Restart=always
RestartSec=5
Environment=RUST_LOG=info

[Install]
WantedBy=multi-user.target
```

#### 启动服务

```bash
# 启用并启动服务
sudo systemctl enable otlp
sudo systemctl start otlp

# 检查服务状态
sudo systemctl status otlp
```

### 2. Docker 部署

#### Dockerfile

```dockerfile
# 多阶段构建
FROM rust:1.90-slim as builder

# 安装系统依赖
RUN apt-get update && apt-get install -y \
    pkg-config \
    libssl-dev \
    && rm -rf /var/lib/apt/lists/*

# 设置工作目录
WORKDIR /app

# 复制源代码
COPY Cargo.toml Cargo.lock ./
COPY src/ ./src/

# 构建发布版本
RUN cargo build --release

# 运行时镜像
FROM debian:bullseye-slim

# 安装运行时依赖
RUN apt-get update && apt-get install -y \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# 创建用户
RUN useradd -r -s /bin/false otlp

# 复制二进制文件
COPY --from=builder /app/target/release/otlp /usr/local/bin/

# 设置权限
RUN chmod +x /usr/local/bin/otlp

# 切换到非 root 用户
USER otlp

# 暴露端口
EXPOSE 8080

# 启动命令
CMD ["otlp"]
```

#### Docker Compose

```yaml
# docker-compose.yml
version: '3.8'

services:
  otlp:
    build: .
    ports:
      - "8080:8080"
    environment:
      - RUST_LOG=info
      - OTLP_ENDPOINT=http://collector:4317
    depends_on:
      - collector
    restart: unless-stopped

  collector:
    image: otel/opentelemetry-collector-contrib:latest
    ports:
      - "4317:4317"
      - "4318:4318"
    volumes:
      - ./collector-config.yaml:/etc/otelcol-contrib/otel-collector-config.yaml
    command: ["--config=/etc/otelcol-contrib/otel-collector-config.yaml"]

  prometheus:
    image: prom/prometheus:latest
    ports:
      - "9090:9090"
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml
    command:
      - '--config.file=/etc/prometheus/prometheus.yml'
      - '--storage.tsdb.path=/prometheus'
      - '--web.console.libraries=/etc/prometheus/console_libraries'
      - '--web.console.templates=/etc/prometheus/consoles'

  grafana:
    image: grafana/grafana:latest
    ports:
      - "3000:3000"
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=admin
    volumes:
      - grafana-storage:/var/lib/grafana
      - ./grafana-dashboards:/etc/grafana/provisioning/dashboards

volumes:
  grafana-storage:
```

### 3. Kubernetes 部署

#### Namespace

```yaml
# k8s/namespace.yaml
apiVersion: v1
kind: Namespace
metadata:
  name: otlp-system
```

#### ConfigMap

```yaml
# k8s/configmap.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: otlp-config
  namespace: otlp-system
data:
  config.yaml: |
    endpoint: "http://otel-collector:4317"
    timeout: "30s"
    retry:
      max_attempts: 3
      base_delay: "100ms"
      max_delay: "5s"
    circuit_breaker:
      failure_threshold: 5
      recovery_timeout: "60s"
    logging:
      level: "info"
      format: "json"
```

#### Deployment

```yaml
# k8s/deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otlp-deployment
  namespace: otlp-system
spec:
  replicas: 3
  selector:
    matchLabels:
      app: otlp
  template:
    metadata:
      labels:
        app: otlp
    spec:
      containers:
      - name: otlp
        image: otlp:latest
        ports:
        - containerPort: 8080
        env:
        - name: RUST_LOG
          value: "info"
        - name: OTLP_CONFIG_PATH
          value: "/etc/otlp/config.yaml"
        volumeMounts:
        - name: config
          mountPath: /etc/otlp
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
      volumes:
      - name: config
        configMap:
          name: otlp-config
```

#### Service

```yaml
# k8s/service.yaml
apiVersion: v1
kind: Service
metadata:
  name: otlp-service
  namespace: otlp-system
spec:
  selector:
    app: otlp
  ports:
  - port: 8080
    targetPort: 8080
    protocol: TCP
  type: ClusterIP
```

#### Ingress

```yaml
# k8s/ingress.yaml
apiVersion: networking.k8s.io/v1
kind: Ingress
metadata:
  name: otlp-ingress
  namespace: otlp-system
  annotations:
    nginx.ingress.kubernetes.io/rewrite-target: /
spec:
  rules:
  - host: otlp.example.com
    http:
      paths:
      - path: /
        pathType: Prefix
        backend:
          service:
            name: otlp-service
            port:
              number: 8080
```

## 📊 监控配置

### 1. Prometheus 配置

```yaml
# prometheus.yml
global:
  scrape_interval: 15s
  evaluation_interval: 15s

rule_files:
  - "otlp_rules.yml"

scrape_configs:
  - job_name: 'otlp'
    static_configs:
      - targets: ['otlp:8080']
    metrics_path: '/metrics'
    scrape_interval: 10s

  - job_name: 'otel-collector'
    static_configs:
      - targets: ['otel-collector:8888']

alerting:
  alertmanagers:
    - static_configs:
        - targets:
          - alertmanager:9093
```

### 2. Grafana 仪表板

```json
{
  "dashboard": {
    "title": "OTLP Rust Dashboard",
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
        "title": "Response Time",
        "type": "graph",
        "targets": [
          {
            "expr": "histogram_quantile(0.95, rate(otlp_request_duration_seconds_bucket[5m]))",
            "legendFormat": "95th percentile"
          }
        ]
      },
      {
        "title": "Circuit Breaker Status",
        "type": "stat",
        "targets": [
          {
            "expr": "otlp_circuit_breaker_state",
            "legendFormat": "State"
          }
        ]
      }
    ]
  }
}
```

### 3. 告警规则

```yaml
# otlp_rules.yml
groups:
- name: otlp_alerts
  rules:
  - alert: HighErrorRate
    expr: rate(otlp_errors_total[5m]) > 0.1
    for: 2m
    labels:
      severity: warning
    annotations:
      summary: "High error rate detected"
      description: "Error rate is {{ $value }} errors per second"

  - alert: HighLatency
    expr: histogram_quantile(0.95, rate(otlp_request_duration_seconds_bucket[5m])) > 1
    for: 5m
    labels:
      severity: warning
    annotations:
      summary: "High latency detected"
      description: "95th percentile latency is {{ $value }} seconds"

  - alert: CircuitBreakerOpen
    expr: otlp_circuit_breaker_state == 1
    for: 1m
    labels:
      severity: critical
    annotations:
      summary: "Circuit breaker is open"
      description: "Circuit breaker has been open for more than 1 minute"
```

## 🔧 配置管理

### 环境变量

```bash
# 基本配置
export OTLP_ENDPOINT="http://collector:4317"
export RUST_LOG="info"
export OTLP_TIMEOUT="30s"

# 重试配置
export OTLP_RETRY_MAX_ATTEMPTS="3"
export OTLP_RETRY_BASE_DELAY="100ms"
export OTLP_RETRY_MAX_DELAY="5s"

# 熔断器配置
export OTLP_CIRCUIT_BREAKER_FAILURE_THRESHOLD="5"
export OTLP_CIRCUIT_BREAKER_RECOVERY_TIMEOUT="60s"

# 监控配置
export OTLP_METRICS_ENABLED="true"
export OTLP_METRICS_PORT="9090"
export OTLP_TRACING_ENABLED="true"
```

### 配置文件

```yaml
# config.yaml
endpoint: "http://collector:4317"
timeout: "30s"

retry:
  max_attempts: 3
  base_delay: "100ms"
  max_delay: "5s"
  backoff_multiplier: 2.0
  jitter: true
  retryable_errors:
    - "timeout"
    - "connection"
    - "temporary"

circuit_breaker:
  failure_threshold: 5
  recovery_timeout: "60s"
  half_open_max_calls: 3
  sliding_window_size: "60s"
  minimum_calls: 10

timeout:
  connect_timeout: "5s"
  read_timeout: "30s"
  write_timeout: "30s"
  operation_timeout: "60s"

graceful_degradation:
  enabled: true
  strategies:
    - "use_cache"
    - "use_fallback"
    - "reduce_quality"
  trigger_conditions:
    - type: "high_error_rate"
      threshold: 0.5
    - type: "high_latency"
      threshold: "2s"

health_check:
  interval: "30s"
  timeout: "5s"
  path: "/health"
  unhealthy_threshold: 3
  healthy_threshold: 2

logging:
  level: "info"
  format: "json"
  output: "stdout"

monitoring:
  metrics_enabled: true
  metrics_port: 9090
  tracing_enabled: true
  tracing_endpoint: "http://jaeger:14268/api/traces"
```

## 🚨 故障排除

### 常见问题

#### 1. 连接失败

```bash
# 检查网络连接
curl -v http://collector:4317

# 检查防火墙
sudo ufw status
sudo iptables -L

# 检查 DNS 解析
nslookup collector
```

#### 2. 高内存使用

```bash
# 检查内存使用
top -p $(pgrep otlp)

# 检查内存泄漏
valgrind --tool=massif ./target/release/otlp

# 调整配置
export RUST_LOG="warn"
export OTLP_BATCH_SIZE="100"
```

#### 3. 高 CPU 使用

```bash
# 检查 CPU 使用
htop -p $(pgrep otlp)

# 分析性能瓶颈
perf record -p $(pgrep otlp)
perf report

# 调整并发配置
export OTLP_WORKER_THREADS="4"
export OTLP_ASYNC_THREADS="2"
```

#### 4. 熔断器频繁开启

```bash
# 检查服务健康状态
curl http://collector:4317/health

# 调整熔断器配置
export OTLP_CIRCUIT_BREAKER_FAILURE_THRESHOLD="10"
export OTLP_CIRCUIT_BREAKER_RECOVERY_TIMEOUT="120s"

# 检查依赖服务
kubectl get pods -l app=collector
```

### 日志分析

```bash
# 查看实时日志
journalctl -u otlp -f

# 查看错误日志
journalctl -u otlp --since "1 hour ago" | grep ERROR

# 分析日志模式
grep "circuit_breaker" /var/log/otlp.log | tail -100

# 统计错误类型
grep "ERROR" /var/log/otlp.log | awk '{print $4}' | sort | uniq -c
```

### 性能调优

#### 1. 系统级优化

```bash
# 调整文件描述符限制
echo "* soft nofile 65536" >> /etc/security/limits.conf
echo "* hard nofile 65536" >> /etc/security/limits.conf

# 调整网络参数
echo "net.core.somaxconn = 65536" >> /etc/sysctl.conf
echo "net.ipv4.tcp_max_syn_backlog = 65536" >> /etc/sysctl.conf
sysctl -p
```

#### 2. 应用级优化

```yaml
# 优化配置
batch_size: 1000
flush_interval: "1s"
max_concurrent_requests: 100
connection_pool_size: 50
```

## 📈 扩展和升级

### 水平扩展

```yaml
# 增加副本数
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otlp-deployment
spec:
  replicas: 5  # 从 3 增加到 5
```

### 垂直扩展

```yaml
# 增加资源限制
resources:
  requests:
    memory: "512Mi"  # 从 256Mi 增加
    cpu: "500m"      # 从 250m 增加
  limits:
    memory: "1Gi"    # 从 512Mi 增加
    cpu: "1000m"     # 从 500m 增加
```

### 版本升级

```bash
# 滚动更新
kubectl set image deployment/otlp-deployment otlp=otlp:v2.0.0

# 检查更新状态
kubectl rollout status deployment/otlp-deployment

# 回滚（如果需要）
kubectl rollout undo deployment/otlp-deployment
```

## 🔐 安全配置

### TLS 配置

```yaml
# TLS 配置
tls:
  enabled: true
  cert_file: "/etc/ssl/certs/otlp.crt"
  key_file: "/etc/ssl/private/otlp.key"
  ca_file: "/etc/ssl/certs/ca.crt"
```

### 认证配置

```yaml
# 认证配置
auth:
  type: "oauth2"
  client_id: "otlp-client"
  client_secret: "your-secret"
  token_url: "https://auth.example.com/oauth/token"
```

### 网络安全

```yaml
# NetworkPolicy
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: otlp-netpol
spec:
  podSelector:
    matchLabels:
      app: otlp
  policyTypes:
  - Ingress
  - Egress
  ingress:
  - from:
    - namespaceSelector:
        matchLabels:
          name: monitoring
    ports:
    - protocol: TCP
      port: 8080
  egress:
  - to:
    - namespaceSelector:
        matchLabels:
          name: observability
    ports:
    - protocol: TCP
      port: 4317
```

## 📚 最佳实践

### 1. 配置管理

- 使用 ConfigMap 或 Secret 管理配置
- 敏感信息使用 Secret
- 配置变更使用滚动更新

### 2. 监控告警

- 设置合理的告警阈值
- 使用多级告警（warning, critical）
- 定期检查和调整告警规则

### 3. 日志管理

- 使用结构化日志（JSON 格式）
- 设置合适的日志级别
- 定期轮转和清理日志

### 4. 安全实践

- 使用非 root 用户运行
- 启用 TLS 加密
- 定期更新依赖和镜像

### 5. 备份恢复

- 定期备份配置和状态
- 测试恢复流程
- 文档化恢复步骤

---

**文档版本**: v1.0
**最后更新**: 2025年1月
**维护者**: OTLP Rust 团队
