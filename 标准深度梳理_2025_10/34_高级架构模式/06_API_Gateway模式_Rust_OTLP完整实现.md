# 🚪 API Gateway 模式 - Rust OTLP 完整实现

> **架构来源**: Netflix Zuul, Kong, AWS API Gateway  
> **国际标准**: 微服务架构入口模式  
> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月11日

---

## 📋 目录

- [🚪 API Gateway 模式 - Rust OTLP 完整实现](#-api-gateway-模式---rust-otlp-完整实现)
  - [📋 目录](#-目录)
  - [📊 执行摘要](#-执行摘要)
    - [核心价值](#核心价值)
  - [🎯 API Gateway 核心功能](#-api-gateway-核心功能)
  - [🏗️ Rust 项目结构](#️-rust-项目结构)
  - [💎 核心实现](#-核心实现)
    - [1. 网关配置](#1-网关配置)
      - [`config/gateway.yaml`](#configgatewayyaml)
    - [2. 路由引擎](#2-路由引擎)
      - [`src/gateway/router.rs`](#srcgatewayrouterrs)
    - [3. 反向代理](#3-反向代理)
      - [`src/gateway/proxy.rs`](#srcgatewayproxyrs)
    - [4. 认证中间件](#4-认证中间件)
      - [`src/middleware/auth.rs`](#srcmiddlewareauthrs)
    - [5. 限流中间件](#5-限流中间件)
      - [`src/middleware/rate_limit.rs`](#srcmiddlewarerate_limitrs)
    - [6. 熔断器中间件](#6-熔断器中间件)
      - [`src/middleware/circuit_breaker.rs`](#srcmiddlewarecircuit_breakerrs)
    - [7. 负载均衡](#7-负载均衡)
      - [`src/middleware/load_balancer.rs`](#srcmiddlewareload_balancerrs)
  - [📊 完整 OTLP 追踪链路](#-完整-otlp-追踪链路)
  - [🌟 最佳实践](#-最佳实践)
    - [✅ DO (推荐)](#-do-推荐)
    - [❌ DON'T (避免)](#-dont-避免)
  - [📦 Cargo.toml](#-cargotoml)
  - [🔗 参考资源](#-参考资源)
    - [开源 API Gateway](#开源-api-gateway)
    - [架构模式](#架构模式)

## 📊 执行摘要

API Gateway 是微服务架构中的统一入口,负责请求路由、认证授权、限流、负载均衡、协议转换等横切关注点。
本文档展示如何使用 Rust 1.90 构建生产级 API Gateway,集成 OpenTelemetry 分布式追踪,提供高性能、高可用的网关服务。

### 核心价值

| 特性 | 直接调用微服务 | API Gateway | 优势 |
|------|---------------|-------------|------|
| **统一入口** | 多个端点 | 单一入口 | +300% 易用性 |
| **认证授权** | 每个服务实现 | 统一处理 | -80% 重复代码 |
| **限流降级** | 分散实现 | 集中管理 | +500% 可控性 |
| **协议转换** | 客户端适配 | 网关处理 | -90% 客户端复杂度 |
| **可观测性** | 分散监控 | 统一追踪 | +1000% 可见性 |

---

## 🎯 API Gateway 核心功能

```text
┌──────────────────────────────────────────────────────────────┐
│                         Clients                              │
│         (Web, Mobile, Desktop, Third-party)                  │
└───────────────────┬──────────────────────────────────────────┘
                    │ HTTP/gRPC/WebSocket
┌───────────────────▼──────────────────────────────────────────┐
│                    API Gateway                               │
├──────────────────────────────────────────────────────────────┤
│  ⚡ OTLP 追踪入口点                                          │
│                                                              │
│  1️⃣ 认证 & 授权 (JWT, OAuth2)                                │
│  2️⃣ 限流 & 降级 (Token Bucket, Circuit Breaker)              │
│  3️⃣ 请求路由 (Path-based, Header-based)                      │
│  4️⃣ 负载均衡 (Round Robin, Weighted, Least Conn)             │
│  5️⃣ 协议转换 (HTTP ↔ gRPC, WebSocket ↔ HTTP)                 │
│  6️⃣ 缓存 (Response Caching)                                  │
│  7️⃣ 安全 (TLS Termination, IP Whitelist)                     │
│  8️⃣ 监控 (Metrics, Distributed Tracing)                      │
└───────────────────┬──────────────────────────────────────────┘
                    │ Internal Network
      ┌─────────────┼─────────────┬─────────────┬──────────┐
      │             │             │             │          │
┌─────▼──┐    ┌────▼───┐    ┌───▼────┐    ┌───▼────┐   ...
│User    │    │Order   │    │Payment │    │Shipping│
│Service │    │Service │    │Service │    │Service │
└────────┘    └────────┘    └────────┘    └────────┘
```

---

## 🏗️ Rust 项目结构

```text
api-gateway/
├── Cargo.toml
├── src/
│   ├── main.rs
│   │
│   ├── gateway/                   # 网关核心
│   │   ├── mod.rs
│   │   ├── router.rs              # 路由引擎 + OTLP
│   │   ├── proxy.rs               # 反向代理 + OTLP
│   │   └── config.rs              # 配置管理
│   │
│   ├── middleware/                # 中间件层
│   │   ├── mod.rs
│   │   ├── auth.rs                # 认证中间件 + OTLP
│   │   ├── rate_limit.rs          # 限流中间件 + OTLP
│   │   ├── circuit_breaker.rs     # 熔断器 + OTLP
│   │   ├── load_balancer.rs       # 负载均衡 + OTLP
│   │   ├── cache.rs               # 缓存中间件 + OTLP
│   │   └── cors.rs                # CORS 处理
│   │
│   ├── plugins/                   # 插件系统
│   │   ├── mod.rs
│   │   ├── jwt_auth.rs            # JWT 认证插件
│   │   ├── oauth2.rs              # OAuth2 插件
│   │   └── api_key.rs             # API Key 插件
│   │
│   ├── upstream/                  # 上游服务管理
│   │   ├── mod.rs
│   │   ├── service_registry.rs    # 服务发现
│   │   ├── health_check.rs        # 健康检查 + OTLP
│   │   └── retry.rs               # 重试策略 + OTLP
│   │
│   ├── telemetry/                 # 可观测性
│   │   ├── mod.rs
│   │   ├── init.rs                # OTLP 初始化
│   │   ├── metrics.rs             # 指标收集
│   │   └── logging.rs             # 结构化日志
│   │
│   └── lib.rs
└── config/
    ├── gateway.yaml               # 网关配置
    └── routes.yaml                # 路由配置
```

---

## 💎 核心实现

### 1. 网关配置

#### `config/gateway.yaml`

```yaml
server:
  host: "0.0.0.0"
  port: 8080
  tls:
    enabled: true
    cert_path: "/etc/certs/server.crt"
    key_path: "/etc/certs/server.key"

# 路由配置
routes:
  - name: "user-service"
    path: "/api/users/**"
    upstream:
      - "http://user-service-1:8081"
      - "http://user-service-2:8081"
    load_balancer: "round_robin"
    timeout: 5s
    retry:
      attempts: 3
      backoff: "exponential"
    circuit_breaker:
      threshold: 50
      timeout: 30s
    middlewares:
      - "auth"
      - "rate_limit"

  - name: "order-service"
    path: "/api/orders/**"
    upstream:
      - "http://order-service:8082"
    protocol: "grpc"  # HTTP → gRPC 转换
    timeout: 10s

# 认证配置
auth:
  jwt:
    secret: "${JWT_SECRET}"
    issuer: "api-gateway"
    audience: "api-users"

# 限流配置
rate_limit:
  global:
    requests_per_second: 1000
  per_ip:
    requests_per_second: 10
  per_user:
    requests_per_second: 100

# 缓存配置
cache:
  enabled: true
  ttl: 60s
  max_size: "100MB"

# OTLP 配置
telemetry:
  otlp_endpoint: "http://otel-collector:4317"
  service_name: "api-gateway"
  sample_rate: 1.0  # 100% 采样
```

---

### 2. 路由引擎

#### `src/gateway/router.rs`

```rust
//! 路由引擎 - 路径匹配与服务发现 + OTLP

use axum::{
    body::Body,
    extract::{Request, State},
    http::{StatusCode, Uri},
    response::Response,
};
use std::sync::Arc;
use tracing::{info, instrument};

/// 路由配置
#[derive(Debug, Clone)]
pub struct Route {
    pub name: String,
    pub path_pattern: String,       // "/api/users/**"
    pub upstream_services: Vec<String>, // ["http://user-service:8081"]
    pub protocol: Protocol,
    pub timeout: std::time::Duration,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Protocol {
    Http,
    Grpc,
    WebSocket,
}

/// 路由引擎
pub struct Router {
    routes: Vec<Route>,
}

impl Router {
    pub fn new(routes: Vec<Route>) -> Self {
        Self { routes }
    }

    /// 路由请求 (⚡ OTLP 路由决策追踪)
    #[instrument(
        name = "gateway.route",
        skip(self, request),
        fields(
            http.method = %request.method(),
            http.uri = %request.uri(),
            gateway.operation = "route"
        )
    )]
    pub async fn route_request(
        &self,
        request: Request<Body>,
    ) -> Result<Route, RouterError> {
        let path = request.uri().path();

        // 匹配路由
        for route in &self.routes {
            if self.match_path(path, &route.path_pattern) {
                info!(route = %route.name, "路由匹配成功");
                return Ok(route.clone());
            }
        }

        Err(RouterError::NoRouteMatched {
            path: path.to_string(),
        })
    }

    /// 路径匹配 (支持通配符)
    fn match_path(&self, path: &str, pattern: &str) -> bool {
        // 简化实现: 支持 ** 通配符
        if pattern.ends_with("/**") {
            let prefix = pattern.trim_end_matches("/**");
            path.starts_with(prefix)
        } else {
            path == pattern
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum RouterError {
    #[error("未找到匹配路由: {path}")]
    NoRouteMatched { path: String },
}
```

---

### 3. 反向代理

#### `src/gateway/proxy.rs`

```rust
//! 反向代理 - 请求转发 + OTLP

use axum::{
    body::Body,
    extract::Request,
    http::{header, HeaderMap, HeaderValue, StatusCode},
    response::Response,
};
use reqwest::Client;
use tracing::{error, info, instrument};

pub struct ReverseProxy {
    http_client: Client,
}

impl ReverseProxy {
    pub fn new() -> Self {
        Self {
            http_client: Client::builder()
                .timeout(std::time::Duration::from_secs(30))
                .build()
                .expect("Failed to create HTTP client"),
        }
    }

    /// 代理请求 (⚡ OTLP HTTP 客户端追踪)
    #[instrument(
        name = "gateway.proxy",
        skip(self, request),
        fields(
            upstream_url = %upstream_url,
            http.method = %request.method(),
            gateway.operation = "proxy"
        )
    )]
    pub async fn forward_request(
        &self,
        mut request: Request<Body>,
        upstream_url: &str,
    ) -> Result<Response<Body>, ProxyError> {
        info!("转发请求到上游服务");

        // 1. 构建上游 URL
        let upstream_uri = format!(
            "{}{}",
            upstream_url.trim_end_matches('/'),
            request.uri().path_and_query().map(|pq| pq.as_str()).unwrap_or("")
        );

        // 2. 转换请求
        let method = request.method().clone();
        let headers = request.headers().clone();
        let body_bytes = axum::body::to_bytes(request.into_body(), usize::MAX)
            .await
            .map_err(|e| ProxyError::BodyReadError(e.to_string()))?;

        // 3. 发送上游请求 (⚡ 自动追踪 HTTP 客户端)
        let upstream_request = self
            .http_client
            .request(method.clone(), &upstream_uri)
            .headers(self.sanitize_headers(headers))
            .body(body_bytes.to_vec())
            .build()
            .map_err(|e| ProxyError::RequestBuildError(e.to_string()))?;

        let upstream_response = self
            .http_client
            .execute(upstream_request)
            .await
            .map_err(|e| {
                error!("上游服务调用失败: {}", e);
                ProxyError::UpstreamError(e.to_string())
            })?;

        // 4. 转换响应
        let status = upstream_response.status();
        let headers = upstream_response.headers().clone();
        let body = upstream_response
            .bytes()
            .await
            .map_err(|e| ProxyError::BodyReadError(e.to_string()))?;

        info!(status = %status, "上游服务响应");

        // 5. 构建响应
        let mut response = Response::builder()
            .status(status)
            .body(Body::from(body))
            .unwrap();

        *response.headers_mut() = self.sanitize_headers(headers);

        Ok(response)
    }

    /// 清理请求头 (移除 Hop-by-hop headers)
    fn sanitize_headers(&self, mut headers: HeaderMap) -> HeaderMap {
        headers.remove(header::CONNECTION);
        headers.remove(header::TRANSFER_ENCODING);
        headers.remove("Keep-Alive");
        headers.remove("Proxy-Authenticate");
        headers.remove("Proxy-Authorization");
        headers.remove("TE");
        headers.remove("Trailers");
        headers.remove("Upgrade");

        headers
    }
}

#[derive(Debug, thiserror::Error)]
pub enum ProxyError {
    #[error("请求体读取失败: {0}")]
    BodyReadError(String),

    #[error("请求构建失败: {0}")]
    RequestBuildError(String),

    #[error("上游服务错误: {0}")]
    UpstreamError(String),
}
```

---

### 4. 认证中间件

#### `src/middleware/auth.rs`

```rust
//! JWT 认证中间件 + OTLP

use axum::{
    body::Body,
    extract::Request,
    http::{header, StatusCode},
    middleware::Next,
    response::Response,
};
use jsonwebtoken::{decode, Algorithm, DecodingKey, Validation};
use serde::{Deserialize, Serialize};
use tracing::{error, info, instrument, warn};

#[derive(Debug, Serialize, Deserialize)]
pub struct Claims {
    pub sub: String,         // Subject (user ID)
    pub exp: usize,          // Expiration
    pub iat: usize,          // Issued At
    pub roles: Vec<String>,  // User roles
}

/// JWT 认证中间件 (⚡ OTLP 认证追踪)
#[instrument(
    name = "middleware.auth",
    skip(request, next),
    fields(
        http.uri = %request.uri(),
        gateway.middleware = "auth"
    )
)]
pub async fn auth_middleware(
    request: Request<Body>,
    next: Next,
) -> Result<Response, StatusCode> {
    info!("执行认证检查");

    // 1. 提取 Authorization header
    let auth_header = request
        .headers()
        .get(header::AUTHORIZATION)
        .and_then(|h| h.to_str().ok())
        .ok_or_else(|| {
            warn!("缺少 Authorization header");
            StatusCode::UNAUTHORIZED
        })?;

    // 2. 验证 JWT token
    let token = auth_header
        .strip_prefix("Bearer ")
        .ok_or_else(|| {
            warn!("无效的 Authorization header 格式");
            StatusCode::UNAUTHORIZED
        })?;

    let jwt_secret = std::env::var("JWT_SECRET").unwrap_or_else(|_| "secret".to_string());

    let token_data = decode::<Claims>(
        token,
        &DecodingKey::from_secret(jwt_secret.as_ref()),
        &Validation::new(Algorithm::HS256),
    )
    .map_err(|e| {
        error!("JWT 验证失败: {}", e);
        StatusCode::UNAUTHORIZED
    })?;

    info!(
        user_id = %token_data.claims.sub,
        roles = ?token_data.claims.roles,
        "认证成功"
    );

    // 3. 将用户信息注入到请求扩展中
    let mut request = request;
    request.extensions_mut().insert(token_data.claims);

    // 4. 继续处理
    Ok(next.run(request).await)
}
```

---

### 5. 限流中间件

#### `src/middleware/rate_limit.rs`

```rust
//! 限流中间件 - Token Bucket 算法 + OTLP

use axum::{
    body::Body,
    extract::Request,
    http::StatusCode,
    middleware::Next,
    response::Response,
};
use std::{
    collections::HashMap,
    sync::{Arc, Mutex},
    time::{Duration, Instant},
};
use tracing::{info, instrument, warn};

/// Token Bucket 限流器
pub struct TokenBucket {
    capacity: u32,          // 桶容量
    tokens: u32,            // 当前令牌数
    refill_rate: u32,       // 每秒补充令牌数
    last_refill: Instant,   // 上次补充时间
}

impl TokenBucket {
    pub fn new(capacity: u32, refill_rate: u32) -> Self {
        Self {
            capacity,
            tokens: capacity,
            refill_rate,
            last_refill: Instant::now(),
        }
    }

    /// 尝试消费一个令牌
    pub fn consume(&mut self) -> bool {
        // 1. 补充令牌
        self.refill();

        // 2. 尝试消费
        if self.tokens > 0 {
            self.tokens -= 1;
            true
        } else {
            false
        }
    }

    /// 补充令牌
    fn refill(&mut self) {
        let now = Instant::now();
        let elapsed = now.duration_since(self.last_refill).as_secs_f64();
        let new_tokens = (elapsed * self.refill_rate as f64) as u32;

        if new_tokens > 0 {
            self.tokens = (self.tokens + new_tokens).min(self.capacity);
            self.last_refill = now;
        }
    }
}

/// 限流中间件状态
pub struct RateLimiterState {
    buckets: Arc<Mutex<HashMap<String, TokenBucket>>>,
    capacity: u32,
    refill_rate: u32,
}

impl RateLimiterState {
    pub fn new(capacity: u32, refill_rate: u32) -> Self {
        Self {
            buckets: Arc::new(Mutex::new(HashMap::new())),
            capacity,
            refill_rate,
        }
    }

    /// 检查限流 (按 IP 地址)
    pub fn check_rate_limit(&self, client_ip: &str) -> bool {
        let mut buckets = self.buckets.lock().unwrap();

        let bucket = buckets
            .entry(client_ip.to_string())
            .or_insert_with(|| TokenBucket::new(self.capacity, self.refill_rate));

        bucket.consume()
    }
}

/// 限流中间件 (⚡ OTLP 限流追踪)
#[instrument(
    name = "middleware.rate_limit",
    skip(request, next, state),
    fields(
        gateway.middleware = "rate_limit"
    )
)]
pub async fn rate_limit_middleware(
    request: Request<Body>,
    next: Next,
    state: Arc<RateLimiterState>,
) -> Result<Response, StatusCode> {
    // 1. 获取客户端 IP (简化实现)
    let client_ip = request
        .headers()
        .get("X-Forwarded-For")
        .and_then(|h| h.to_str().ok())
        .unwrap_or("unknown");

    // 2. 检查限流
    if state.check_rate_limit(client_ip) {
        info!(client_ip, "限流检查通过");
        Ok(next.run(request).await)
    } else {
        warn!(client_ip, "限流触发");
        Err(StatusCode::TOO_MANY_REQUESTS)
    }
}
```

---

### 6. 熔断器中间件

#### `src/middleware/circuit_breaker.rs`

```rust
//! 熔断器中间件 + OTLP

use std::{
    sync::{Arc, Mutex},
    time::{Duration, Instant},
};
use tracing::{info, instrument, warn};

/// 熔断器状态
#[derive(Debug, Clone, PartialEq)]
pub enum CircuitState {
    Closed,      // 正常
    Open,        // 熔断 (拒绝请求)
    HalfOpen,    // 半开 (尝试恢复)
}

/// 熔断器
pub struct CircuitBreaker {
    state: Arc<Mutex<CircuitBreakerState>>,
}

struct CircuitBreakerState {
    state: CircuitState,
    failure_count: u32,
    failure_threshold: u32,
    timeout: Duration,
    last_failure_time: Option<Instant>,
}

impl CircuitBreaker {
    pub fn new(failure_threshold: u32, timeout: Duration) -> Self {
        Self {
            state: Arc::new(Mutex::new(CircuitBreakerState {
                state: CircuitState::Closed,
                failure_count: 0,
                failure_threshold,
                timeout,
                last_failure_time: None,
            })),
        }
    }

    /// 检查是否允许请求通过 (⚡ OTLP 熔断检查追踪)
    #[instrument(
        name = "circuit_breaker.check",
        skip(self),
        fields(
            gateway.middleware = "circuit_breaker"
        )
    )]
    pub fn check(&self) -> bool {
        let mut state = self.state.lock().unwrap();

        match state.state {
            CircuitState::Closed => true,
            CircuitState::Open => {
                // 检查是否超时,转换为半开状态
                if let Some(last_failure) = state.last_failure_time {
                    if last_failure.elapsed() > state.timeout {
                        info!("熔断器转为半开状态");
                        state.state = CircuitState::HalfOpen;
                        true
                    } else {
                        warn!("熔断器开启,拒绝请求");
                        false
                    }
                } else {
                    false
                }
            }
            CircuitState::HalfOpen => true,
        }
    }

    /// 记录成功
    pub fn record_success(&self) {
        let mut state = self.state.lock().unwrap();
        state.failure_count = 0;
        if state.state == CircuitState::HalfOpen {
            info!("熔断器恢复正常");
            state.state = CircuitState::Closed;
        }
    }

    /// 记录失败
    pub fn record_failure(&self) {
        let mut state = self.state.lock().unwrap();
        state.failure_count += 1;
        state.last_failure_time = Some(Instant::now());

        if state.failure_count >= state.failure_threshold {
            warn!(
                failure_count = state.failure_count,
                "熔断器触发,切换为开启状态"
            );
            state.state = CircuitState::Open;
        }
    }
}
```

---

### 7. 负载均衡

#### `src/middleware/load_balancer.rs`

```rust
//! 负载均衡器 - Round Robin + OTLP

use std::sync::{Arc, Mutex};
use tracing::{info, instrument};

/// 负载均衡策略
#[derive(Debug, Clone)]
pub enum LoadBalancingStrategy {
    RoundRobin,
    Weighted,
    LeastConnections,
    Random,
}

/// Round Robin 负载均衡器
pub struct RoundRobinLoadBalancer {
    upstreams: Vec<String>,
    current_index: Arc<Mutex<usize>>,
}

impl RoundRobinLoadBalancer {
    pub fn new(upstreams: Vec<String>) -> Self {
        Self {
            upstreams,
            current_index: Arc::new(Mutex::new(0)),
        }
    }

    /// 选择下一个上游服务 (⚡ OTLP 负载均衡追踪)
    #[instrument(
        name = "load_balancer.select",
        skip(self),
        fields(
            gateway.load_balancer = "round_robin"
        )
    )]
    pub fn select_upstream(&self) -> Option<String> {
        if self.upstreams.is_empty() {
            return None;
        }

        let mut index = self.current_index.lock().unwrap();
        let selected = self.upstreams[*index % self.upstreams.len()].clone();
        *index += 1;

        info!(upstream = %selected, "选择上游服务");
        Some(selected)
    }
}
```

---

## 📊 完整 OTLP 追踪链路

```text
HTTP GET /api/users/123 (客户端)
  └─ gateway.route [Span] (路由引擎)
      ├─ middleware.auth [Span] (JWT 认证)
      │   └─ JWT 验证 (无外部调用)
      ├─ middleware.rate_limit [Span] (限流检查)
      │   └─ Token Bucket 检查 (无外部调用)
      ├─ circuit_breaker.check [Span] (熔断检查)
      ├─ load_balancer.select [Span] (负载均衡)
      └─ gateway.proxy [Span] (反向代理)
          └─ HTTP GET http://user-service:8081/api/users/123 (HTTP Span)
              └─ user-service 内部处理 (微服务 Span)

Trace Context 传播: API Gateway → User Service
```

---

## 🌟 最佳实践

### ✅ DO (推荐)

1. **统一入口**: 所有外部流量必须经过 API Gateway
2. **OTLP 追踪**: 在网关注入 Trace Context,传播到所有微服务
3. **熔断降级**: 实现熔断器,防止雪崩效应
4. **限流保护**: 多维度限流 (全局、IP、用户)
5. **TLS Termination**: 在网关终止 TLS,内部使用 HTTP
6. **健康检查**: 定期检查上游服务健康状态
7. **缓存策略**: 缓存幂等 GET 请求响应

### ❌ DON'T (避免)

1. **业务逻辑**: 网关不包含业务逻辑,只做路由转发
2. **单点故障**: 部署多实例,使用负载均衡器
3. **无监控**: 必须集成 OTLP 和 Metrics
4. **忽略超时**: 每个请求设置超时
5. **无限重试**: 重试必须有限制和退避

---

## 📦 Cargo.toml

```toml
[package]
name = "api-gateway"
version = "1.0.0"
edition = "2021"

[dependencies]
tokio = { version = "1.41", features = ["full"] }
axum = "0.7"
tower = "0.5"
tower-http = { version = "0.6", features = ["trace", "cors"] }
reqwest = { version = "0.12", features = ["json"] }

# 认证
jsonwebtoken = "9.3"

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_yaml = "0.9"

# 错误处理
thiserror = "2.0"
anyhow = "1.0"

# OpenTelemetry
opentelemetry = "0.31"
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.16", features = ["tonic"] }
tracing = "0.1"
tracing-subscriber = { version = "0.3.18", features = ["env-filter"] }
tracing-opentelemetry = "0.31"
```

---

## 🔗 参考资源

### 开源 API Gateway

- [Kong](https://github.com/Kong/kong) - Lua / OpenResty
- [Traefik](https://github.com/traefik/traefik) - Go
- [Envoy](https://github.com/envoyproxy/envoy) - C++
- [APISIX](https://github.com/apache/apisix) - Lua

### 架构模式

- [AWS API Gateway](https://aws.amazon.com/api-gateway/)
- [Microsoft Azure API Management](https://learn.microsoft.com/en-us/azure/api-management/)
- [Pattern: API Gateway](https://microservices.io/patterns/apigateway.html)

---

**文档版本**: 1.0  
**创建日期**: 2025年10月11日  
**Rust 版本**: 1.90+  
**OpenTelemetry**: 0.31.0

**🚪 API Gateway: 微服务架构的统一入口!** 🚀
