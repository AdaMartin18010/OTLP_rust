# 📋 最佳实践指南

本文档提供了 OTLP Rust 项目的最佳实践指南，包括开发实践、部署实践、运维实践和安全实践。

## 📋 目录

- [📋 最佳实践指南](#-最佳实践指南)
  - [📋 目录](#-目录)
  - [💻 开发最佳实践](#-开发最佳实践)
    - [代码质量](#代码质量)
      - [代码风格](#代码风格)
      - [类型安全](#类型安全)
    - [错误处理](#错误处理)
      - [错误类型设计](#错误类型设计)
      - [错误处理模式](#错误处理模式)
    - [性能优化](#性能优化)
      - [内存管理](#内存管理)
      - [异步优化](#异步优化)
    - [测试策略](#测试策略)
      - [单元测试](#单元测试)
      - [集成测试](#集成测试)
  - [🚀 部署最佳实践](#-部署最佳实践)
    - [环境配置](#环境配置)
      - [配置管理](#配置管理)
      - [环境变量](#环境变量)
    - [容器化](#容器化)
      - [Dockerfile 最佳实践](#dockerfile-最佳实践)
    - [Kubernetes 部署](#kubernetes-部署)
      - [资源限制](#资源限制)
      - [安全配置](#安全配置)
    - [监控配置](#监控配置)
      - [指标收集](#指标收集)
  - [🔧 运维最佳实践](#-运维最佳实践)
    - [日志管理](#日志管理)
      - [结构化日志](#结构化日志)
    - [性能监控](#性能监控)
      - [性能指标](#性能指标)
    - [故障处理](#故障处理)
      - [故障检测](#故障检测)
    - [容量规划](#容量规划)
      - [资源规划](#资源规划)
  - [🔒 安全最佳实践](#-安全最佳实践)
    - [认证授权](#认证授权)
      - [JWT 认证](#jwt-认证)
    - [数据保护](#数据保护)
      - [数据加密](#数据加密)
    - [网络安全](#网络安全)
      - [TLS 配置](#tls-配置)
    - [审计日志](#审计日志)
      - [审计日志记录](#审计日志记录)
  - [📊 性能最佳实践](#-性能最佳实践)
    - [内存管理1](#内存管理1)
      - [内存池使用](#内存池使用)
    - [CPU 优化](#cpu-优化)
      - [并行处理](#并行处理)
    - [I/O 优化](#io-优化)
      - [异步 I/O](#异步-io)
    - [网络优化](#网络优化)
      - [连接复用](#连接复用)
  - [🔗 相关文档](#-相关文档)

## 💻 开发最佳实践

### 代码质量

#### 代码风格

```rust
// ✅ 好的实践：清晰的命名和结构
pub struct OtlpClient {
    inner: Arc<ClientInner>,
    config: OtlpConfig,
}

impl OtlpClient {
    /// 创建新的 OTLP 客户端
    /// 
    /// # Arguments
    /// 
    /// * `config` - 客户端配置
    /// 
    /// # Returns
    /// 
    /// 返回配置好的客户端实例
    /// 
    /// # Errors
    /// 
    /// 如果配置无效或网络连接失败，返回错误
    pub async fn new(config: OtlpConfig) -> Result<Self, OtlpError> {
        let inner = ClientInner::new(config.clone()).await?;
        Ok(Self {
            inner: Arc::new(inner),
            config,
        })
    }
}

// ❌ 避免：模糊的命名和缺少文档
pub struct Client {
    i: Arc<Inner>,
    c: Config,
}

impl Client {
    pub async fn new(c: Config) -> Result<Self, Error> {
        let i = Inner::new(c.clone()).await?;
        Ok(Self { i: Arc::new(i), c })
    }
}
```

#### 类型安全

```rust
// ✅ 好的实践：使用强类型
#[derive(Debug, Clone, PartialEq)]
pub struct Endpoint(String);

impl Endpoint {
    pub fn new(url: &str) -> Result<Self, InvalidEndpoint> {
        if url.starts_with("http://") || url.starts_with("https://") {
            Ok(Self(url.to_string()))
        } else {
            Err(InvalidEndpoint::new(url))
        }
    }
    
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

// ✅ 使用 Newtype 模式
pub struct BatchSize(usize);

impl BatchSize {
    pub fn new(size: usize) -> Result<Self, InvalidBatchSize> {
        if size > 0 && size <= 10000 {
            Ok(Self(size))
        } else {
            Err(InvalidBatchSize::new(size))
        }
    }
    
    pub fn get(&self) -> usize {
        self.0
    }
}
```

### 错误处理

#### 错误类型设计

```rust
use thiserror::Error;

// ✅ 好的实践：详细的错误类型
#[derive(Error, Debug)]
pub enum OtlpError {
    #[error("Network error: {0}")]
    Network(#[from] reqwest::Error),
    
    #[error("gRPC error: {0}")]
    Grpc(#[from] tonic::Status),
    
    #[error("Serialization error: {0}")]
    Serialization(#[from] serde_json::Error),
    
    #[error("Configuration error: {0}")]
    Config(#[from] ConfigError),
    
    #[error("Timeout after {duration:?}")]
    Timeout { duration: Duration },
    
    #[error("Batch processing failed: {reason}")]
    Batch { reason: String },
    
    #[error("Authentication failed: {message}")]
    Auth { message: String },
}

// ✅ 错误上下文
impl OtlpError {
    pub fn with_context<C>(self, context: C) -> ContextualError<C>
    where
        C: std::fmt::Display + Send + Sync + 'static,
    {
        ContextualError {
            error: self,
            context: Some(Box::new(context)),
        }
    }
}
```

#### 错误处理模式

```rust
// ✅ 好的实践：使用 Result 和 ? 操作符
pub async fn send_data(&self, data: TelemetryData) -> Result<SendResult, OtlpError> {
    let serialized = serde_json::to_string(&data)?;
    let response = self.transport.send(&serialized).await?;
    
    if response.status().is_success() {
        Ok(SendResult::success())
    } else {
        Err(OtlpError::Network(
            reqwest::Error::from(response.error_for_status().unwrap_err())
        ))
    }
}

// ✅ 使用 match 进行详细错误处理
pub async fn process_with_retry(&self, data: TelemetryData) -> Result<(), OtlpError> {
    let mut last_error = None;
    
    for attempt in 1..=self.config.max_retries {
        match self.send_data(data.clone()).await {
            Ok(_) => return Ok(()),
            Err(e) => {
                last_error = Some(e);
                if attempt < self.config.max_retries {
                    tokio::time::sleep(self.calculate_backoff(attempt)).await;
                }
            }
        }
    }
    
    Err(last_error.unwrap_or_else(|| OtlpError::Custom("Unknown error".to_string())))
}
```

### 性能优化

#### 内存管理

```rust
// ✅ 好的实践：使用内存池
pub struct MemoryPool {
    buffers: Vec<Vec<u8>>,
    max_size: usize,
}

impl MemoryPool {
    pub fn new(pool_size: usize, buffer_size: usize) -> Self {
        let mut buffers = Vec::with_capacity(pool_size);
        for _ in 0..pool_size {
            buffers.push(Vec::with_capacity(buffer_size));
        }
        
        Self {
            buffers,
            max_size: buffer_size,
        }
    }
    
    pub fn get_buffer(&mut self) -> Option<Vec<u8>> {
        self.buffers.pop().map(|mut buffer| {
            buffer.clear();
            buffer
        })
    }
    
    pub fn return_buffer(&mut self, mut buffer: Vec<u8>) {
        if buffer.capacity() <= self.max_size && self.buffers.len() < self.buffers.capacity() {
            buffer.clear();
            self.buffers.push(buffer);
        }
    }
}

// ✅ 使用零拷贝技术
pub struct ZeroCopyBuffer<'a> {
    data: &'a [u8],
}

impl<'a> ZeroCopyBuffer<'a> {
    pub fn new(data: &'a [u8]) -> Self {
        Self { data }
    }
    
    pub fn as_slice(&self) -> &[u8] {
        self.data
    }
}
```

#### 异步优化

```rust
// ✅ 好的实践：合理的并发控制
pub struct ConcurrencyLimiter {
    semaphore: Semaphore,
}

impl ConcurrencyLimiter {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            semaphore: Semaphore::new(max_concurrent),
        }
    }
    
    pub async fn execute<F, T>(&self, future: F) -> Result<T, OtlpError>
    where
        F: Future<Output = Result<T, OtlpError>>,
    {
        let _permit = self.semaphore.acquire().await
            .map_err(|_| OtlpError::ConcurrencyLimit)?;
        
        future.await
    }
}

// ✅ 使用 select! 进行并发操作
pub async fn process_with_timeout(&self, data: TelemetryData) -> Result<(), OtlpError> {
    tokio::select! {
        result = self.send_data(data) => result,
        _ = tokio::time::sleep(self.config.timeout) => {
            Err(OtlpError::Timeout { 
                duration: self.config.timeout 
            })
        }
    }
}
```

### 测试策略

#### 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use tokio_test;
    
    // ✅ 好的实践：清晰的测试结构
    #[tokio::test]
    async fn test_client_creation_success() {
        // Arrange
        let config = OtlpConfig::default()
            .with_endpoint("http://localhost:4317");
        
        // Act
        let client = OtlpClient::new(config).await;
        
        // Assert
        assert!(client.is_ok());
    }
    
    #[tokio::test]
    async fn test_client_creation_invalid_endpoint() {
        // Arrange
        let config = OtlpConfig::default()
            .with_endpoint("invalid-url");
        
        // Act
        let client = OtlpClient::new(config).await;
        
        // Assert
        assert!(client.is_err());
        match client.unwrap_err() {
            OtlpError::Config(_) => {}, // 期望的错误类型
            other => panic!("Expected ConfigError, got {:?}", other),
        }
    }
    
    // ✅ 使用参数化测试
    #[tokio::test]
    async fn test_batch_processing() {
        let test_cases = vec![
            (1, 1),
            (100, 1),
            (512, 1),
            (1000, 2),
            (2000, 4),
        ];
        
        for (input_size, expected_batches) in test_cases {
            let processor = BatchProcessor::new(512);
            let data = generate_test_data(input_size);
            let batches = processor.process(data).await.unwrap();
            
            assert_eq!(batches.len(), expected_batches);
        }
    }
}
```

#### 集成测试

```rust
#[cfg(test)]
mod integration_tests {
    use super::*;
    
    // ✅ 使用测试容器
    #[tokio::test]
    async fn test_with_testcontainers() {
        let docker = testcontainers::clients::Cli::default();
        let collector = docker.run(testcontainers::images::generic::GenericImage::new("otel/opentelemetry-collector", "latest"));
        
        let config = OtlpConfig::default()
            .with_endpoint(&format!("http://localhost:{}", collector.get_host_port_ipv4(4317)));
        
        let client = OtlpClient::new(config).await.unwrap();
        
        // 测试逻辑
        let result = client.send_trace("test-operation").await;
        assert!(result.is_ok());
    }
    
    // ✅ 模拟外部依赖
    #[tokio::test]
    async fn test_with_mock_server() {
        let server = mockito::Server::new_async().await;
        let mock = server
            .mock("POST", "/v1/traces")
            .with_status(200)
            .create_async()
            .await;
        
        let config = OtlpConfig::default()
            .with_endpoint(&server.url());
        
        let client = OtlpClient::new(config).await.unwrap();
        let result = client.send_trace("test-operation").await;
        
        assert!(result.is_ok());
        mock.assert_async().await;
    }
}
```

## 🚀 部署最佳实践

### 环境配置

#### 配置管理

```yaml
# ✅ 好的实践：环境特定的配置
# config/development.yaml
server:
  host: "0.0.0.0"
  port: 8080
  workers: 2

otlp:
  endpoint: "http://localhost:4317"
  protocol: "grpc"
  timeout: "5s"

logging:
  level: "debug"
  format: "pretty"

# config/production.yaml
server:
  host: "0.0.0.0"
  port: 8080
  workers: 8

otlp:
  endpoint: "http://collector:4317"
  protocol: "grpc"
  timeout: "10s"
  retry:
    max_retries: 5
    initial_delay: "100ms"
    max_delay: "30s"

logging:
  level: "info"
  format: "json"
  output: "stdout"
```

#### 环境变量

```bash
# ✅ 好的实践：使用环境变量
export RUST_LOG=info
export OTLP_ENDPOINT=http://collector:4317
export OTLP_PROTOCOL=grpc
export OTLP_TIMEOUT=10s
export OTLP_MAX_RETRIES=5
export OTLP_BATCH_SIZE=512
export OTLP_QUEUE_SIZE=2048

# ❌ 避免：硬编码配置
# export OTLP_ENDPOINT=http://localhost:4317
```

### 容器化

#### Dockerfile 最佳实践

```dockerfile
# ✅ 好的实践：多阶段构建
FROM rust:1.90-alpine AS builder

# 安装构建依赖
RUN apk add --no-cache musl-dev openssl-dev pkgconfig

WORKDIR /app

# 复制依赖文件
COPY Cargo.toml Cargo.lock ./

# 构建依赖缓存
RUN cargo fetch

# 复制源代码
COPY src ./src
COPY otlp ./otlp

# 构建应用
RUN cargo build --release --target x86_64-unknown-linux-musl

# 运行时镜像
FROM alpine:latest

# 安装运行时依赖
RUN apk --no-cache add ca-certificates tzdata

# 创建非 root 用户
RUN addgroup -g 1001 -S otlp && \
    adduser -u 1001 -S otlp -G otlp

WORKDIR /app

# 复制二进制文件
COPY --from=builder /app/target/x86_64-unknown-linux-musl/release/otlp-client ./

# 设置权限
RUN chown -R otlp:otlp /app
USER otlp

# 健康检查
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD wget --no-verbose --tries=1 --spider http://localhost:8080/health || exit 1

# 暴露端口
EXPOSE 8080

# 启动应用
CMD ["./otlp-client"]
```

### Kubernetes 部署

#### 资源限制

```yaml
# ✅ 好的实践：合理的资源限制
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otlp-client
spec:
  template:
    spec:
      containers:
      - name: otlp-client
        image: otlp-client:latest
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
          timeoutSeconds: 5
          failureThreshold: 3
        readinessProbe:
          httpGet:
            path: /ready
            port: 8080
          initialDelaySeconds: 5
          periodSeconds: 5
          timeoutSeconds: 3
          failureThreshold: 3
```

#### 安全配置

```yaml
# ✅ 好的实践：安全配置
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otlp-client
spec:
  template:
    spec:
      securityContext:
        runAsNonRoot: true
        runAsUser: 1001
        runAsGroup: 1001
        fsGroup: 1001
      containers:
      - name: otlp-client
        securityContext:
          allowPrivilegeEscalation: false
          readOnlyRootFilesystem: true
          runAsNonRoot: true
          runAsUser: 1001
          capabilities:
            drop:
            - ALL
```

### 监控配置

#### 指标收集

```rust
// ✅ 好的实践：结构化指标
use prometheus::{Counter, Histogram, Gauge, register_counter, register_histogram, register_gauge};

pub struct Metrics {
    pub requests_total: Counter,
    pub request_duration: Histogram,
    pub active_connections: Gauge,
    pub batch_size: Histogram,
    pub errors_total: Counter,
}

impl Metrics {
    pub fn new() -> Self {
        Self {
            requests_total: register_counter!(
                "otlp_requests_total",
                "Total number of requests",
                &["method", "endpoint", "status"]
            ).unwrap(),
            request_duration: register_histogram!(
                "otlp_request_duration_seconds",
                "Request duration in seconds",
                &["method", "endpoint"]
            ).unwrap(),
            active_connections: register_gauge!(
                "otlp_active_connections",
                "Number of active connections"
            ).unwrap(),
            batch_size: register_histogram!(
                "otlp_batch_size",
                "Batch size distribution"
            ).unwrap(),
            errors_total: register_counter!(
                "otlp_errors_total",
                "Total number of errors",
                &["error_type", "endpoint"]
            ).unwrap(),
        }
    }
}
```

## 🔧 运维最佳实践

### 日志管理

#### 结构化日志

```rust
// ✅ 好的实践：结构化日志
use tracing::{info, warn, error, debug};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

pub fn init_logging() {
    tracing_subscriber::registry()
        .with(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| "otlp_client=info".into()),
        )
        .with(tracing_subscriber::fmt::layer()
            .with_target(false)
            .with_thread_ids(true)
            .with_file(true)
            .with_line_number(true)
            .json()
        )
        .init();
}

// ✅ 使用结构化字段
pub async fn process_request(request: &Request) -> Result<Response, Error> {
    let span = tracing::info_span!("process_request", 
        request_id = %request.id,
        method = %request.method,
        path = %request.path,
        user_id = %request.user_id
    );
    
    let _enter = span.enter();
    
    info!(
        request_id = %request.id,
        method = %request.method,
        path = %request.path,
        user_id = %request.user_id,
        "Processing request"
    );
    
    // 处理逻辑
    let result = handle_request(request).await;
    
    match &result {
        Ok(response) => {
            info!(
                request_id = %request.id,
                status_code = response.status_code,
                duration_ms = response.duration.as_millis(),
                "Request completed successfully"
            );
        }
        Err(error) => {
            error!(
                request_id = %request.id,
                error = %error,
                error_type = %std::any::type_name_of_val(error),
                "Request failed"
            );
        }
    }
    
    result
}
```

### 性能监控

#### 性能指标

```rust
// ✅ 好的实践：全面的性能监控
pub struct PerformanceMonitor {
    metrics: Metrics,
    start_time: Instant,
}

impl PerformanceMonitor {
    pub fn new() -> Self {
        Self {
            metrics: Metrics::new(),
            start_time: Instant::now(),
        }
    }
    
    pub fn record_request(&self, method: &str, endpoint: &str, duration: Duration, status: u16) {
        self.metrics.requests_total
            .with_label_values(&[method, endpoint, &status.to_string()])
            .inc();
        
        self.metrics.request_duration
            .with_label_values(&[method, endpoint])
            .observe(duration.as_secs_f64());
    }
    
    pub fn record_error(&self, error_type: &str, endpoint: &str) {
        self.metrics.errors_total
            .with_label_values(&[error_type, endpoint])
            .inc();
    }
    
    pub fn update_connections(&self, count: usize) {
        self.metrics.active_connections.set(count as f64);
    }
}
```

### 故障处理

#### 故障检测

```rust
// ✅ 好的实践：主动故障检测
pub struct HealthChecker {
    checks: Vec<Box<dyn HealthCheck + Send + Sync>>,
    interval: Duration,
}

impl HealthChecker {
    pub fn new(interval: Duration) -> Self {
        Self {
            checks: Vec::new(),
            interval,
        }
    }
    
    pub fn add_check<C>(&mut self, check: C)
    where
        C: HealthCheck + Send + Sync + 'static,
    {
        self.checks.push(Box::new(check));
    }
    
    pub async fn start_monitoring(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut interval = tokio::time::interval(self.interval);
        
        loop {
            interval.tick().await;
            
            for check in &self.checks {
                match check.check().await {
                    Ok(_) => {
                        info!(check_name = %check.name(), "Health check passed");
                    }
                    Err(e) => {
                        error!(check_name = %check.name(), error = %e, "Health check failed");
                        // 触发告警或故障处理
                    }
                }
            }
        }
    }
}

pub trait HealthCheck {
    fn name(&self) -> &str;
    async fn check(&self) -> Result<(), Box<dyn std::error::Error>>;
}
```

### 容量规划

#### 资源规划

```rust
// ✅ 好的实践：基于指标的容量规划
pub struct CapacityPlanner {
    metrics: Metrics,
    thresholds: CapacityThresholds,
}

impl CapacityPlanner {
    pub fn new(thresholds: CapacityThresholds) -> Self {
        Self {
            metrics: Metrics::new(),
            thresholds,
        }
    }
    
    pub async fn check_capacity(&self) -> CapacityStatus {
        let cpu_usage = self.get_cpu_usage().await;
        let memory_usage = self.get_memory_usage().await;
        let request_rate = self.get_request_rate().await;
        
        CapacityStatus {
            cpu_usage,
            memory_usage,
            request_rate,
            recommendations: self.generate_recommendations(cpu_usage, memory_usage, request_rate),
        }
    }
    
    fn generate_recommendations(&self, cpu: f64, memory: f64, requests: f64) -> Vec<String> {
        let mut recommendations = Vec::new();
        
        if cpu > self.thresholds.cpu_warning {
            recommendations.push("Consider scaling up CPU resources".to_string());
        }
        
        if memory > self.thresholds.memory_warning {
            recommendations.push("Consider scaling up memory resources".to_string());
        }
        
        if requests > self.thresholds.request_rate_warning {
            recommendations.push("Consider horizontal scaling".to_string());
        }
        
        recommendations
    }
}
```

## 🔒 安全最佳实践

### 认证授权

#### JWT 认证

```rust
// ✅ 好的实践：安全的 JWT 处理
use jsonwebtoken::{decode, encode, Algorithm, DecodingKey, EncodingKey, Header, Validation};

pub struct JwtAuth {
    encoding_key: EncodingKey,
    decoding_key: DecodingKey,
    validation: Validation,
}

impl JwtAuth {
    pub fn new(secret: &str) -> Self {
        let encoding_key = EncodingKey::from_secret(secret.as_bytes());
        let decoding_key = DecodingKey::from_secret(secret.as_bytes());
        let mut validation = Validation::new(Algorithm::HS256);
        validation.set_required_spec_claims(&["exp", "iat", "sub"]);
        
        Self {
            encoding_key,
            decoding_key,
            validation,
        }
    }
    
    pub fn generate_token(&self, claims: &Claims) -> Result<String, JwtError> {
        encode(&Header::default(), claims, &self.encoding_key)
    }
    
    pub fn verify_token(&self, token: &str) -> Result<Claims, JwtError> {
        let token_data = decode::<Claims>(token, &self.decoding_key, &self.validation)?;
        Ok(token_data.claims)
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Claims {
    pub sub: String,
    pub exp: usize,
    pub iat: usize,
    pub roles: Vec<String>,
}
```

### 数据保护

#### 数据加密

```rust
// ✅ 好的实践：数据加密
use aes_gcm::{Aes256Gcm, Key, Nonce};
use aes_gcm::aead::{Aead, NewAead};

pub struct DataEncryption {
    cipher: Aes256Gcm,
}

impl DataEncryption {
    pub fn new(key: &[u8; 32]) -> Self {
        let key = Key::from_slice(key);
        let cipher = Aes256Gcm::new(key);
        
        Self { cipher }
    }
    
    pub fn encrypt(&self, plaintext: &[u8]) -> Result<Vec<u8>, EncryptionError> {
        let nonce = Nonce::from_slice(&[0; 12]); // 在生产环境中使用随机 nonce
        self.cipher.encrypt(nonce, plaintext)
            .map_err(|e| EncryptionError::EncryptionFailed(e.to_string()))
    }
    
    pub fn decrypt(&self, ciphertext: &[u8]) -> Result<Vec<u8>, EncryptionError> {
        let nonce = Nonce::from_slice(&[0; 12]);
        self.cipher.decrypt(nonce, ciphertext)
            .map_err(|e| EncryptionError::DecryptionFailed(e.to_string()))
    }
}
```

### 网络安全

#### TLS 配置

```rust
// ✅ 好的实践：安全的 TLS 配置
use rustls::{ClientConfig, RootCertStore};
use std::sync::Arc;

pub fn create_secure_client_config() -> Result<ClientConfig, Box<dyn std::error::Error>> {
    let mut root_store = RootCertStore::empty();
    
    // 添加系统根证书
    for cert in rustls_native_certs::load_native_certs()? {
        root_store.add(&rustls::Certificate(cert.0))?;
    }
    
    let config = ClientConfig::builder()
        .with_safe_defaults()
        .with_root_certificates(root_store)
        .with_no_client_auth();
    
    Ok(config)
}
```

### 审计日志

#### 审计日志记录

```rust
// ✅ 好的实践：完整的审计日志
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};

#[derive(Debug, Serialize, Deserialize)]
pub struct AuditLog {
    pub timestamp: DateTime<Utc>,
    pub user_id: String,
    pub action: String,
    pub resource: String,
    pub result: AuditResult,
    pub ip_address: String,
    pub user_agent: String,
    pub session_id: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub enum AuditResult {
    Success,
    Failure { reason: String },
}

pub struct AuditLogger {
    writer: Arc<Mutex<dyn std::io::Write + Send>>,
}

impl AuditLogger {
    pub fn new(writer: Box<dyn std::io::Write + Send>) -> Self {
        Self {
            writer: Arc::new(Mutex::new(writer)),
        }
    }
    
    pub async fn log(&self, log: AuditLog) -> Result<(), Box<dyn std::error::Error>> {
        let json = serde_json::to_string(&log)?;
        let mut writer = self.writer.lock().await;
        writeln!(writer, "{}", json)?;
        Ok(())
    }
}
```

## 📊 性能最佳实践

### 内存管理1

#### 内存池使用

```rust
// ✅ 好的实践：高效的内存池
use std::sync::Arc;
use tokio::sync::Mutex;

pub struct MemoryPool {
    pools: Arc<Mutex<Vec<Vec<u8>>>>,
    pool_size: usize,
    buffer_size: usize,
}

impl MemoryPool {
    pub fn new(pool_size: usize, buffer_size: usize) -> Self {
        let mut pools = Vec::with_capacity(pool_size);
        for _ in 0..pool_size {
            pools.push(Vec::with_capacity(buffer_size));
        }
        
        Self {
            pools: Arc::new(Mutex::new(pools)),
            pool_size,
            buffer_size,
        }
    }
    
    pub async fn get_buffer(&self) -> Option<PooledBuffer> {
        let mut pools = self.pools.lock().await;
        pools.pop().map(|mut buffer| {
            buffer.clear();
            PooledBuffer {
                buffer,
                pool: Arc::clone(&self.pools),
            }
        })
    }
}

pub struct PooledBuffer {
    buffer: Vec<u8>,
    pool: Arc<Mutex<Vec<Vec<u8>>>>,
}

impl Drop for PooledBuffer {
    fn drop(&mut self) {
        let pool = Arc::clone(&self.pool);
        let buffer = std::mem::take(&mut self.buffer);
        tokio::spawn(async move {
            let mut pools = pool.lock().await;
            if pools.len() < pools.capacity() {
                pools.push(buffer);
            }
        });
    }
}
```

### CPU 优化

#### 并行处理

```rust
// ✅ 好的实践：合理的并行处理
use rayon::prelude::*;

pub struct ParallelProcessor {
    num_threads: usize,
}

impl ParallelProcessor {
    pub fn new(num_threads: usize) -> Self {
        Self { num_threads }
    }
    
    pub fn process_batch<T, F, R>(&self, items: Vec<T>, processor: F) -> Vec<R>
    where
        T: Send,
        F: Fn(T) -> R + Sync,
        R: Send,
    {
        items.into_par_iter()
            .with_min_len(self.num_threads)
            .map(processor)
            .collect()
    }
}
```

### I/O 优化

#### 异步 I/O

```rust
// ✅ 好的实践：高效的异步 I/O
use tokio::io::{AsyncRead, AsyncWrite};
use tokio::net::TcpStream;

pub struct AsyncIoProcessor {
    buffer_size: usize,
}

impl AsyncIoProcessor {
    pub fn new(buffer_size: usize) -> Self {
        Self { buffer_size }
    }
    
    pub async fn process_stream<R, W>(
        &self,
        mut reader: R,
        mut writer: W,
    ) -> Result<(), std::io::Error>
    where
        R: AsyncRead + Unpin,
        W: AsyncWrite + Unpin,
    {
        let mut buffer = vec![0u8; self.buffer_size];
        
        loop {
            let bytes_read = reader.read(&mut buffer).await?;
            if bytes_read == 0 {
                break;
            }
            
            writer.write_all(&buffer[..bytes_read]).await?;
        }
        
        writer.flush().await?;
        Ok(())
    }
}
```

### 网络优化

#### 连接复用

```rust
// ✅ 好的实践：连接池管理
use std::collections::HashMap;
use tokio::sync::RwLock;

pub struct ConnectionPool<T> {
    connections: Arc<RwLock<HashMap<String, Vec<T>>>>,
    max_connections_per_host: usize,
}

impl<T> ConnectionPool<T> {
    pub fn new(max_connections_per_host: usize) -> Self {
        Self {
            connections: Arc::new(RwLock::new(HashMap::new())),
            max_connections_per_host,
        }
    }
    
    pub async fn get_connection(&self, host: &str) -> Option<PooledConnection<T>> {
        let mut connections = self.connections.write().await;
        let host_connections = connections.entry(host.to_string()).or_insert_with(Vec::new);
        
        host_connections.pop().map(|conn| PooledConnection {
            connection: conn,
            host: host.to_string(),
            pool: Arc::clone(&self.connections),
        })
    }
    
    pub async fn return_connection(&self, host: &str, connection: T) {
        let mut connections = self.connections.write().await;
        let host_connections = connections.entry(host.to_string()).or_insert_with(Vec::new);
        
        if host_connections.len() < self.max_connections_per_host {
            host_connections.push(connection);
        }
    }
}
```

## 🔗 相关文档

- [快速开始指南](../01_GETTING_STARTED/README.md)
- [API 参考文档](../03_API_REFERENCE/README.md)
- [架构设计文档](../04_ARCHITECTURE/README.md)
- [实现指南](../05_IMPLEMENTATION/README.md)
- [部署运维指南](../06_DEPLOYMENT/README.md)
- [集成指南](../07_INTEGRATION/README.md)

---

**最佳实践指南版本**: 1.0.0  
**最后更新**: 2025年1月  
**维护者**: OTLP Rust 团队
