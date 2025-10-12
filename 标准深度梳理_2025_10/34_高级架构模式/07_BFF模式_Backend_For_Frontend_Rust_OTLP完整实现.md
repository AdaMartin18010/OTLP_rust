# BFF 模式 (Backend for Frontend) - Rust 1.90 + OTLP 完整实现指南

> **文档版本**: v1.0.0  
> **创建日期**: 2025-10-11  
> **Rust 版本**: 1.90  
> **OpenTelemetry**: 0.31.0  
> **对标标准**: Martin Fowler BFF Pattern, CNCF Cloud Native Patterns, Microsoft Azure Architecture Patterns

---

## 📑 目录

- [BFF 模式 (Backend for Frontend) - Rust 1.90 + OTLP 完整实现指南](#bff-模式-backend-for-frontend---rust-190--otlp-完整实现指南)
  - [📑 目录](#-目录)
  - [1. BFF 模式概述](#1-bff-模式概述)
    - [1.1 什么是 BFF?](#11-什么是-bff)
    - [1.2 BFF 的核心职责](#12-bff-的核心职责)
    - [1.3 何时使用 BFF?](#13-何时使用-bff)
  - [2. 核心架构原理](#2-核心架构原理)
    - [2.1 BFF 架构层次](#21-bff-架构层次)
    - [2.2 BFF vs API Gateway](#22-bff-vs-api-gateway)
  - [3. Rust 1.90 完整实现](#3-rust-190-完整实现)
    - [3.1 项目结构](#31-项目结构)
    - [3.2 依赖配置 (`Cargo.toml`)](#32-依赖配置-cargotoml)
    - [3.3 下游微服务客户端](#33-下游微服务客户端)
      - [3.3.1 User Service gRPC 客户端](#331-user-service-grpc-客户端)
      - [3.3.2 Order Service gRPC 客户端](#332-order-service-grpc-客户端)
      - [3.3.3 Product Service REST 客户端](#333-product-service-rest-客户端)
    - [3.4 Web BFF 实现](#34-web-bff-实现)
      - [3.4.1 Web 前端模型](#341-web-前端模型)
      - [3.4.2 Web 数据聚合逻辑](#342-web-数据聚合逻辑)
      - [3.4.3 Web BFF HTTP 接口](#343-web-bff-http-接口)
    - [3.5 Mobile BFF 实现](#35-mobile-bff-实现)
      - [3.5.1 Mobile 前端模型 (轻量化)](#351-mobile-前端模型-轻量化)
      - [3.5.2 Mobile 数据聚合逻辑](#352-mobile-数据聚合逻辑)
  - [4. OTLP 分布式追踪集成](#4-otlp-分布式追踪集成)
    - [4.1 OTLP 配置](#41-otlp-配置)
    - [4.2 BFF 追踪示例](#42-bff-追踪示例)
    - [4.3 Jaeger 追踪可视化](#43-jaeger-追踪可视化)
  - [5. 多端 BFF 实现](#5-多端-bff-实现)
    - [5.1 统一入口 (`main.rs`)](#51-统一入口-mainrs)
    - [5.2 Web vs Mobile 响应对比](#52-web-vs-mobile-响应对比)
  - [6. GraphQL BFF 实现](#6-graphql-bff-实现)
    - [6.1 为什么 BFF 适合 GraphQL?](#61-为什么-bff-适合-graphql)
    - [6.2 GraphQL Schema 定义](#62-graphql-schema-定义)
    - [6.3 Rust GraphQL 实现 (async-graphql)](#63-rust-graphql-实现-async-graphql)
    - [6.4 GraphQL BFF 路由](#64-graphql-bff-路由)
    - [6.5 GraphQL 查询示例](#65-graphql-查询示例)
  - [7. BFF 安全策略](#7-bff-安全策略)
    - [7.1 JWT 认证中间件](#71-jwt-认证中间件)
    - [7.2 限流中间件 (Token Bucket)](#72-限流中间件-token-bucket)
    - [7.3 熔断器中间件](#73-熔断器中间件)
  - [8. 性能优化与缓存](#8-性能优化与缓存)
    - [8.1 Redis 缓存层](#81-redis-缓存层)
    - [8.2 本地缓存 (moka)](#82-本地缓存-moka)
    - [8.3 二级缓存策略](#83-二级缓存策略)
    - [8.4 缓存键策略](#84-缓存键策略)
  - [9. 部署与监控](#9-部署与监控)
    - [9.1 Docker Compose 部署](#91-docker-compose-部署)
    - [9.2 Dockerfile](#92-dockerfile)
    - [9.3 健康检查接口](#93-健康检查接口)
    - [9.4 Prometheus Metrics](#94-prometheus-metrics)
  - [10. 最佳实践与陷阱](#10-最佳实践与陷阱)
    - [10.1 最佳实践](#101-最佳实践)
    - [10.2 常见陷阱](#102-常见陷阱)
    - [10.3 BFF 架构演进路径](#103-bff-架构演进路径)
  - [📚 参考资料](#-参考资料)
    - [国际标准与最佳实践](#国际标准与最佳实践)
    - [Rust 生态](#rust-生态)
    - [实战案例](#实战案例)
  - [✅ 总结](#-总结)
    - [BFF 模式核心价值](#bff-模式核心价值)
    - [Rust 1.90 实现优势](#rust-190-实现优势)
    - [适用场景](#适用场景)

---

## 1. BFF 模式概述

### 1.1 什么是 BFF?

**Backend for Frontend (BFF)** 是一种架构模式,为每种用户体验(前端)创建专用的后端服务。

```text
┌──────────────────────────────────────────────────────────────┐
│                    传统单体后端 (问题)                        │
├──────────────────────────────────────────────────────────────┤
│                                                              │
│  Web App  ──┐                                                │
│             ├──►  通用 API  ──► 复杂逻辑 + 数据聚合            │
│  Mobile   ──┤    (同一套接口)                                 │
│             │                                                │
│  Desktop  ──┘                                                │
│                                                              │
│  ❌ 问题:                                                    │
│     • 接口臃肿:需要满足所有端的需求                             │
│     • 过度获取:移动端获取了不必要的数据                         │
│     • 耦合严重:一个端的变更影响所有端                           │
│     • 性能差:无法针对特定端优化                                │
└──────────────────────────────────────────────────────────────┘

┌──────────────────────────────────────────────────────────────┐
│                    BFF 模式 (解决方案)                        │
├──────────────────────────────────────────────────────────────┤
│                                                              │
│  ┌─────────┐     ┌──────────────┐                            │
│  │ Web App │────►│  Web BFF     │──┐                         │
│  └─────────┘     └──────────────┘  │                         │
│                                    │                         │
│  ┌─────────┐     ┌──────────────┐  │    ┌──────────────┐     │
│  │ Mobile  │────►│  Mobile BFF  │──┼───►│ User Service │     │
│  │ (iOS)   │     └──────────────┘  │    └──────────────┘     │
│  └─────────┘                        │    ┌──────────────┐    │
│                                     ├───►│ Order Service│    │
│  ┌─────────┐     ┌──────────────┐  │    └──────────────┘     │
│  │ Desktop │────►│  Desktop BFF │──┘    ┌──────────────┐     │
│  └─────────┘     └──────────────┘       │Product Service     │
│                                          └──────────────┘    │
│  ✅ 优势:                                                    │
│     • 定制化:每个 BFF 专为特定端优化                           │
│     • 解耦:前端独立演进,不影响其他端                           │
│     • 高效:精准数据聚合,减少网络传输                           │
│     • 自主性:前端团队控制自己的 BFF                            │
└──────────────────────────────────────────────────────────────┘
```

### 1.2 BFF 的核心职责

```rust
/// BFF 的核心职责
pub enum BffResponsibility {
    /// 1. 数据聚合 (Data Aggregation)
    /// 从多个微服务聚合数据,减少前端请求次数
    DataAggregation {
        sources: Vec<MicroserviceEndpoint>,
        aggregation_logic: fn(Vec<ServiceResponse>) -> AggregatedResponse,
    },

    /// 2. 数据转换 (Data Transformation)
    /// 将后端数据模型转换为前端友好格式
    DataTransformation {
        backend_model: BackendModel,
        frontend_model: FrontendModel,
    },

    /// 3. 协议适配 (Protocol Adaptation)
    /// REST → GraphQL, gRPC → REST 等
    ProtocolAdaptation {
        from: Protocol,
        to: Protocol,
    },

    /// 4. 安全防护 (Security Gateway)
    /// 认证、授权、限流、防护
    SecurityGateway {
        authentication: AuthMethod,
        authorization: AuthorizationPolicy,
    },

    /// 5. 缓存策略 (Caching Strategy)
    /// 针对特定端的缓存优化
    CachingStrategy {
        cache_key: String,
        ttl: Duration,
        invalidation_policy: InvalidationPolicy,
    },
}
```

### 1.3 何时使用 BFF?

| 场景 | 是否适用 BFF | 原因 |
|------|-------------|------|
| 多端应用 (Web + Mobile + Desktop) | ✅ **强烈推荐** | 每个端的交互模式和数据需求差异大 |
| 单一 Web 应用 | ❌ 不必要 | 引入额外复杂度,直接调用微服务即可 |
| 频繁的数据聚合需求 | ✅ 推荐 | BFF 可以减少前端请求次数和复杂度 |
| 前端团队需要自主权 | ✅ 推荐 | 前端团队可以独立开发和部署 BFF |
| 遗留系统改造 | ✅ 推荐 | BFF 作为适配层,逐步迁移到新架构 |
| 第三方 API 集成 | ✅ 推荐 | BFF 封装第三方 API,提供统一接口 |

---

## 2. 核心架构原理

### 2.1 BFF 架构层次

```text
┌─────────────────────────────────────────────────────────────────┐
│                         Frontend Clients                        │
│              (Web, iOS, Android, Desktop, IoT)                  │
└────────────────────────┬────────────────────────────────────────┘
                         │ HTTPS / WebSocket / gRPC
┌────────────────────────▼────────────────────────────────────────┐
│                         BFF Layer                               │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐             │
│  │  Web BFF    │  │ Mobile BFF  │  │ Desktop BFF │             │
│  │  (Axum)     │  │  (Axum)     │  │  (Axum)     │             │
│  └─────────────┘  └─────────────┘  └─────────────┘             │
│                                                                 │
│  🔹 职责:                                                        │
│    • 数据聚合: 调用多个下游服务                                  │
│    • 数据转换: Backend Model → Frontend Model                   │
│    • 缓存管理: Redis + 本地缓存                                  │
│    • 认证授权: JWT 验证 + 权限检查                               │
│    • 限流熔断: Token Bucket + Circuit Breaker                   │
│    • OTLP 追踪: 分布式追踪注入                                   │
└────────────────────────┬────────────────────────────────────────┘
                         │ Internal gRPC / REST
┌────────────────────────▼────────────────────────────────────────┐
│                    Microservices Layer                          │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐          │
│  │ User Service │  │Order Service │  │Product Service│          │
│  │  (gRPC)      │  │  (gRPC)      │  │  (REST)       │          │
│  └──────────────┘  └──────────────┘  └──────────────┘          │
└─────────────────────────────────────────────────────────────────┘
```

### 2.2 BFF vs API Gateway

| 特性 | BFF | API Gateway |
|------|-----|-------------|
| **职责定位** | 为特定前端定制,包含业务逻辑 | 通用路由、认证、限流,无业务逻辑 |
| **数量** | 每个前端一个 (Web BFF, Mobile BFF) | 整个系统一个 |
| **所有权** | 前端团队 | 平台/基础设施团队 |
| **数据聚合** | ✅ 核心功能 | ❌ 通常不做 |
| **业务逻辑** | ✅ 可以包含 | ❌ 应该避免 |
| **协议转换** | ✅ 常见 (REST → GraphQL) | ⚠️ 有限支持 |
| **缓存策略** | ✅ 精细化缓存 | ⚠️ 通用缓存 |
| **部署独立性** | ✅ 高 (随前端迭代) | ⚠️ 低 (稳定基础设施) |

**典型架构组合**:

```text
Frontend → API Gateway → BFF → Microservices
            ↑              ↑
            |              |
         认证/限流      数据聚合/转换
         (基础设施)      (业务逻辑)
```

---

## 3. Rust 1.90 完整实现

### 3.1 项目结构

```text
bff-ecommerce/
├── Cargo.toml
├── .env
├── docker-compose.yml
├── src/
│   ├── main.rs
│   │
│   ├── bff/
│   │   ├── mod.rs
│   │   ├── web_bff/              # Web 端 BFF
│   │   │   ├── mod.rs
│   │   │   ├── handlers.rs       # Web 专用接口
│   │   │   ├── aggregators.rs    # Web 数据聚合逻辑
│   │   │   └── models.rs         # Web 前端模型
│   │   │
│   │   ├── mobile_bff/           # Mobile 端 BFF
│   │   │   ├── mod.rs
│   │   │   ├── handlers.rs       # Mobile 专用接口
│   │   │   ├── aggregators.rs    # Mobile 数据聚合逻辑
│   │   │   └── models.rs         # Mobile 前端模型
│   │   │
│   │   └── desktop_bff/          # Desktop 端 BFF (可选)
│   │       └── ...
│   │
│   ├── clients/                  # 下游微服务客户端
│   │   ├── mod.rs
│   │   ├── user_client.rs        # User Service gRPC 客户端
│   │   ├── order_client.rs       # Order Service gRPC 客户端
│   │   └── product_client.rs     # Product Service REST 客户端
│   │
│   ├── middleware/               # 中间件
│   │   ├── auth.rs               # JWT 认证
│   │   ├── rate_limit.rs         # 限流
│   │   └── circuit_breaker.rs    # 熔断器
│   │
│   ├── cache/                    # 缓存层
│   │   ├── mod.rs
│   │   ├── redis_cache.rs
│   │   └── local_cache.rs        # moka 本地缓存
│   │
│   ├── telemetry/                # OTLP 配置
│   │   └── mod.rs
│   │
│   └── config.rs                 # 配置管理
│
└── tests/
    ├── integration_tests.rs
    └── load_tests.rs
```

### 3.2 依赖配置 (`Cargo.toml`)

```toml
[package]
name = "bff-ecommerce"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# Web 框架
axum = "0.7"
axum-extra = { version = "0.9", features = ["typed-header"] }
tower = { version = "0.5", features = ["full"] }
tower-http = { version = "0.6", features = ["trace", "cors", "compression-gzip"] }

# 异步运行时
tokio = { version = "1.41", features = ["full"] }

# HTTP 客户端
reqwest = { version = "0.12", features = ["json", "gzip"] }

# gRPC 客户端
tonic = "0.12"
prost = "0.13"

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 时间处理
chrono = { version = "0.4", features = ["serde"] }

# JWT 认证
jsonwebtoken = "9.3"

# 缓存
redis = { version = "0.27", features = ["tokio-comp", "connection-manager"] }
moka = { version = "0.12", features = ["future"] }

# 错误处理
thiserror = "2.0"
anyhow = "1.0"

# OpenTelemetry
opentelemetry = "0.31"
opentelemetry-otlp = "0.31"
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.31"

# 限流
governor = "0.7"

# 熔断器
failsafe = "1.3"

# UUID
uuid = { version = "1.11", features = ["v4", "serde"] }

# 配置
dotenvy = "0.15"

[build-dependencies]
tonic-build = "0.12"

[dev-dependencies]
mockall = "0.13"
criterion = "0.5"
```

### 3.3 下游微服务客户端

#### 3.3.1 User Service gRPC 客户端

```rust
// src/clients/user_client.rs
use tonic::Request;
use tracing::{info_span, instrument};
use opentelemetry::global;
use opentelemetry::trace::{Span, Tracer};

// 假设 proto 定义
pub mod user_proto {
    tonic::include_proto!("user");
}

use user_proto::{user_service_client::UserServiceClient, GetUserRequest, User};

#[derive(Clone)]
pub struct UserClient {
    client: UserServiceClient<tonic::transport::Channel>,
}

impl UserClient {
    pub async fn new(endpoint: String) -> Result<Self, Box<dyn std::error::Error>> {
        let client = UserServiceClient::connect(endpoint).await?;
        Ok(Self { client })
    }

    #[instrument(skip(self), fields(user_id = %user_id))]
    pub async fn get_user(&mut self, user_id: &str) -> Result<User, tonic::Status> {
        let mut span = info_span!("user_service.get_user");
        span.set_attribute(opentelemetry::KeyValue::new("user_id", user_id.to_string()));

        let mut request = Request::new(GetUserRequest {
            user_id: user_id.to_string(),
        });

        // 注入 OTLP 追踪上下文
        let context = opentelemetry::Context::current();
        let mut metadata = tonic::metadata::MetadataMap::new();
        
        // 将 trace context 注入到 gRPC metadata
        global::get_text_map_propagator(|propagator| {
            propagator.inject_context(
                &context,
                &mut MetadataInjector(&mut metadata),
            );
        });
        
        *request.metadata_mut() = metadata;

        let response = self.client.get_user(request).await?;
        Ok(response.into_inner())
    }
}

// gRPC metadata 注入器
struct MetadataInjector<'a>(&'a mut tonic::metadata::MetadataMap);

impl<'a> opentelemetry::propagation::Injector for MetadataInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        if let Ok(key) = tonic::metadata::MetadataKey::from_bytes(key.as_bytes()) {
            if let Ok(val) = tonic::metadata::MetadataValue::try_from(&value) {
                self.0.insert(key, val);
            }
        }
    }
}
```

#### 3.3.2 Order Service gRPC 客户端

```rust
// src/clients/order_client.rs
use tonic::Request;
use tracing::instrument;

pub mod order_proto {
    tonic::include_proto!("order");
}

use order_proto::{order_service_client::OrderServiceClient, GetOrdersRequest, Order};

#[derive(Clone)]
pub struct OrderClient {
    client: OrderServiceClient<tonic::transport::Channel>,
}

impl OrderClient {
    pub async fn new(endpoint: String) -> Result<Self, Box<dyn std::error::Error>> {
        let client = OrderServiceClient::connect(endpoint).await?;
        Ok(Self { client })
    }

    #[instrument(skip(self), fields(user_id = %user_id))]
    pub async fn get_user_orders(&mut self, user_id: &str) -> Result<Vec<Order>, tonic::Status> {
        let request = Request::new(GetOrdersRequest {
            user_id: user_id.to_string(),
        });

        let response = self.client.get_orders(request).await?;
        Ok(response.into_inner().orders)
    }
}
```

#### 3.3.3 Product Service REST 客户端

```rust
// src/clients/product_client.rs
use reqwest::Client;
use serde::{Deserialize, Serialize};
use tracing::instrument;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Product {
    pub id: String,
    pub name: String,
    pub price: f64,
    pub stock: i32,
    pub image_url: String,
}

#[derive(Clone)]
pub struct ProductClient {
    client: Client,
    base_url: String,
}

impl ProductClient {
    pub fn new(base_url: String) -> Self {
        Self {
            client: Client::new(),
            base_url,
        }
    }

    #[instrument(skip(self), fields(product_ids = ?product_ids))]
    pub async fn get_products_batch(
        &self,
        product_ids: &[String],
    ) -> Result<Vec<Product>, reqwest::Error> {
        let url = format!("{}/api/products/batch", self.base_url);
        
        let response = self
            .client
            .post(&url)
            .json(&serde_json::json!({ "ids": product_ids }))
            .send()
            .await?
            .error_for_status()?;

        response.json().await
    }
}
```

### 3.4 Web BFF 实现

#### 3.4.1 Web 前端模型

```rust
// src/bff/web_bff/models.rs
use serde::{Deserialize, Serialize};

/// Web 端用户主页响应 (聚合数据)
#[derive(Debug, Serialize, Deserialize)]
pub struct WebHomePageResponse {
    pub user: WebUserProfile,
    pub recent_orders: Vec<WebOrderSummary>,
    pub recommended_products: Vec<WebProductCard>,
    pub notifications: Vec<WebNotification>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct WebUserProfile {
    pub id: String,
    pub name: String,
    pub email: String,
    pub avatar_url: String,
    pub membership_level: String,
    pub points: i64,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct WebOrderSummary {
    pub order_id: String,
    pub order_date: String,
    pub total_amount: f64,
    pub status: String,
    pub items_count: i32,
    /// Web 端显示订单缩略图 (前3个商品)
    pub product_thumbnails: Vec<String>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct WebProductCard {
    pub id: String,
    pub name: String,
    pub price: f64,
    pub discount_price: Option<f64>,
    pub image_url: String,
    pub rating: f32,
    pub reviews_count: i32,
    /// Web 端显示完整描述
    pub description: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct WebNotification {
    pub id: String,
    pub title: String,
    pub message: String,
    pub timestamp: String,
    pub is_read: bool,
}
```

#### 3.4.2 Web 数据聚合逻辑

```rust
// src/bff/web_bff/aggregators.rs
use crate::clients::{UserClient, OrderClient, ProductClient};
use crate::bff::web_bff::models::*;
use tracing::{info, instrument, Span};
use tokio::try_join;
use anyhow::Result;

pub struct WebAggregator {
    user_client: UserClient,
    order_client: OrderClient,
    product_client: ProductClient,
}

impl WebAggregator {
    pub fn new(
        user_client: UserClient,
        order_client: OrderClient,
        product_client: ProductClient,
    ) -> Self {
        Self {
            user_client,
            order_client,
            product_client,
        }
    }

    /// 聚合 Web 端主页数据 (并发调用多个服务)
    #[instrument(skip(self), fields(user_id = %user_id))]
    pub async fn aggregate_home_page(&mut self, user_id: &str) -> Result<WebHomePageResponse> {
        info!("🌐 Web BFF: Aggregating home page data for user {}", user_id);

        // 并发调用多个微服务 (使用 tokio::try_join!)
        let (user, orders, products) = try_join!(
            self.fetch_user_profile(user_id),
            self.fetch_recent_orders(user_id),
            self.fetch_recommended_products(user_id),
        )?;

        Ok(WebHomePageResponse {
            user,
            recent_orders: orders,
            recommended_products: products,
            notifications: vec![], // 简化示例
        })
    }

    #[instrument(skip(self))]
    async fn fetch_user_profile(&mut self, user_id: &str) -> Result<WebUserProfile> {
        let user = self.user_client.get_user(user_id).await?;
        
        // 后端模型 → Web 前端模型转换
        Ok(WebUserProfile {
            id: user.id,
            name: user.name,
            email: user.email,
            avatar_url: user.avatar_url,
            membership_level: user.membership_level,
            points: user.points,
        })
    }

    #[instrument(skip(self))]
    async fn fetch_recent_orders(&mut self, user_id: &str) -> Result<Vec<WebOrderSummary>> {
        let orders = self.order_client.get_user_orders(user_id).await?;

        // 转换为 Web 端格式
        let web_orders = orders
            .into_iter()
            .take(5) // Web 端只显示最近5个订单
            .map(|order| WebOrderSummary {
                order_id: order.id,
                order_date: order.created_at,
                total_amount: order.total_amount,
                status: order.status,
                items_count: order.items.len() as i32,
                product_thumbnails: order
                    .items
                    .iter()
                    .take(3)
                    .map(|item| item.product_image_url.clone())
                    .collect(),
            })
            .collect();

        Ok(web_orders)
    }

    #[instrument(skip(self))]
    async fn fetch_recommended_products(&mut self, _user_id: &str) -> Result<Vec<WebProductCard>> {
        // 简化示例:获取热门商品
        let product_ids = vec!["prod_1".to_string(), "prod_2".to_string()];
        let products = self.product_client.get_products_batch(&product_ids).await?;

        // 转换为 Web 端格式 (包含完整描述)
        let web_products = products
            .into_iter()
            .map(|product| WebProductCard {
                id: product.id,
                name: product.name,
                price: product.price,
                discount_price: None,
                image_url: product.image_url,
                rating: 4.5,
                reviews_count: 128,
                description: "完整的商品描述...".to_string(), // Web 端显示
            })
            .collect();

        Ok(web_products)
    }
}
```

#### 3.4.3 Web BFF HTTP 接口

```rust
// src/bff/web_bff/handlers.rs
use axum::{
    extract::{State, Path},
    response::{IntoResponse, Json},
    http::StatusCode,
};
use crate::bff::web_bff::aggregators::WebAggregator;
use crate::bff::web_bff::models::WebHomePageResponse;
use std::sync::Arc;
use tokio::sync::Mutex;
use tracing::instrument;

pub type SharedWebAggregator = Arc<Mutex<WebAggregator>>;

/// GET /api/web/home/:user_id
#[instrument(skip(aggregator), fields(user_id = %user_id))]
pub async fn get_web_home_page(
    State(aggregator): State<SharedWebAggregator>,
    Path(user_id): Path<String>,
) -> Result<Json<WebHomePageResponse>, AppError> {
    let mut agg = aggregator.lock().await;
    let response = agg.aggregate_home_page(&user_id).await?;
    Ok(Json(response))
}

// 错误处理
#[derive(Debug)]
pub struct AppError(anyhow::Error);

impl IntoResponse for AppError {
    fn into_response(self) -> axum::response::Response {
        (
            StatusCode::INTERNAL_SERVER_ERROR,
            format!("Internal server error: {}", self.0),
        )
            .into_response()
    }
}

impl<E> From<E> for AppError
where
    E: Into<anyhow::Error>,
{
    fn from(err: E) -> Self {
        Self(err.into())
    }
}
```

### 3.5 Mobile BFF 实现

#### 3.5.1 Mobile 前端模型 (轻量化)

```rust
// src/bff/mobile_bff/models.rs
use serde::{Deserialize, Serialize};

/// Mobile 端主页响应 (精简数据,减少流量)
#[derive(Debug, Serialize, Deserialize)]
pub struct MobileHomePageResponse {
    pub user: MobileUserProfile,
    pub orders: Vec<MobileOrderSummary>,
    pub products: Vec<MobileProductCard>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct MobileUserProfile {
    pub id: String,
    pub name: String,
    /// Mobile 端只显示昵称,不显示邮箱
    pub avatar: String,
    pub level: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct MobileOrderSummary {
    pub id: String,
    pub date: String,
    pub amount: f64,
    pub status: String,
    /// Mobile 端只显示1个缩略图
    pub thumbnail: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct MobileProductCard {
    pub id: String,
    pub name: String,
    pub price: f64,
    pub image: String,
    /// Mobile 端不显示完整描述,只显示标签
    pub tags: Vec<String>,
}
```

#### 3.5.2 Mobile 数据聚合逻辑

```rust
// src/bff/mobile_bff/aggregators.rs
use crate::clients::{UserClient, OrderClient, ProductClient};
use crate::bff::mobile_bff::models::*;
use tracing::instrument;
use tokio::try_join;
use anyhow::Result;

pub struct MobileAggregator {
    user_client: UserClient,
    order_client: OrderClient,
    product_client: ProductClient,
}

impl MobileAggregator {
    pub fn new(
        user_client: UserClient,
        order_client: OrderClient,
        product_client: ProductClient,
    ) -> Self {
        Self {
            user_client,
            order_client,
            product_client,
        }
    }

    #[instrument(skip(self), fields(user_id = %user_id))]
    pub async fn aggregate_home_page(&mut self, user_id: &str) -> Result<MobileHomePageResponse> {
        // 并发调用
        let (user, orders, products) = try_join!(
            self.fetch_user_profile(user_id),
            self.fetch_recent_orders(user_id),
            self.fetch_recommended_products(user_id),
        )?;

        Ok(MobileHomePageResponse {
            user,
            orders,
            products,
        })
    }

    async fn fetch_user_profile(&mut self, user_id: &str) -> Result<MobileUserProfile> {
        let user = self.user_client.get_user(user_id).await?;
        
        // 转换为 Mobile 精简格式
        Ok(MobileUserProfile {
            id: user.id,
            name: user.name,
            avatar: user.avatar_url,
            level: user.membership_level,
        })
    }

    async fn fetch_recent_orders(&mut self, user_id: &str) -> Result<Vec<MobileOrderSummary>> {
        let orders = self.order_client.get_user_orders(user_id).await?;

        // Mobile 端只显示3个订单,且精简字段
        let mobile_orders = orders
            .into_iter()
            .take(3)
            .map(|order| MobileOrderSummary {
                id: order.id,
                date: order.created_at,
                amount: order.total_amount,
                status: order.status,
                thumbnail: order.items.first().map(|i| i.product_image_url.clone()).unwrap_or_default(),
            })
            .collect();

        Ok(mobile_orders)
    }

    async fn fetch_recommended_products(&mut self, _user_id: &str) -> Result<Vec<MobileProductCard>> {
        let product_ids = vec!["prod_1".to_string()];
        let products = self.product_client.get_products_batch(&product_ids).await?;

        // Mobile 端精简格式
        let mobile_products = products
            .into_iter()
            .map(|product| MobileProductCard {
                id: product.id,
                name: product.name,
                price: product.price,
                image: product.image_url,
                tags: vec!["热销".to_string()],
            })
            .collect();

        Ok(mobile_products)
    }
}
```

---

## 4. OTLP 分布式追踪集成

### 4.1 OTLP 配置

```rust
// src/telemetry/mod.rs
use opentelemetry::{global, KeyValue};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{
    runtime,
    trace::{RandomIdGenerator, Sampler, Tracer},
    Resource,
};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};

pub fn init_telemetry(service_name: &str) -> Result<(), Box<dyn std::error::Error>> {
    // 1. 配置 OTLP Exporter
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317"),
        )
        .with_trace_config(
            opentelemetry_sdk::trace::Config::default()
                .with_sampler(Sampler::AlwaysOn)
                .with_id_generator(RandomIdGenerator::default())
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", service_name.to_string()),
                    KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
                ])),
        )
        .install_batch(runtime::Tokio)?;

    global::set_tracer_provider(tracer.provider().unwrap());

    // 2. 配置 tracing-subscriber
    tracing_subscriber::registry()
        .with(EnvFilter::try_from_default_env().unwrap_or_else(|_| "info".into()))
        .with(tracing_subscriber::fmt::layer().json())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    Ok(())
}

pub fn shutdown_telemetry() {
    global::shutdown_tracer_provider();
}
```

### 4.2 BFF 追踪示例

```rust
// BFF 调用链追踪
use tracing::{info_span, instrument, Instrument};

#[instrument(skip(self), fields(
    bff.type = "web",
    user_id = %user_id,
    otel.kind = "server"
))]
pub async fn aggregate_home_page(&mut self, user_id: &str) -> Result<WebHomePageResponse> {
    let root_span = info_span!("web_bff.aggregate_home_page");

    // 子 Span: 调用 User Service
    let user = async {
        self.fetch_user_profile(user_id).await
    }
    .instrument(info_span!("fetch_user_profile"))
    .await?;

    // 子 Span: 调用 Order Service
    let orders = async {
        self.fetch_recent_orders(user_id).await
    }
    .instrument(info_span!("fetch_recent_orders"))
    .await?;

    // 子 Span: 调用 Product Service
    let products = async {
        self.fetch_recommended_products(user_id).await
    }
    .instrument(info_span!("fetch_recommended_products"))
    .await?;

    Ok(WebHomePageResponse {
        user,
        recent_orders: orders,
        recommended_products: products,
        notifications: vec![],
    })
}
```

### 4.3 Jaeger 追踪可视化

```text
🔍 Jaeger Trace 示例:

Trace ID: 7a8b9c0d1e2f3456
Span 1: web_bff.aggregate_home_page (duration: 245ms)
  ├── Span 2: fetch_user_profile (duration: 50ms)
  │   └── Span 3: user_service.get_user (gRPC) (duration: 45ms)
  │       └── Span 4: postgres.query (duration: 12ms)
  │
  ├── Span 5: fetch_recent_orders (duration: 120ms)
  │   └── Span 6: order_service.get_orders (gRPC) (duration: 115ms)
  │       └── Span 7: postgres.query (duration: 35ms)
  │
  └── Span 8: fetch_recommended_products (duration: 80ms)
      └── Span 9: product_service.batch_get (REST) (duration: 75ms)
          └── Span 10: elasticsearch.search (duration: 28ms)

✅ 通过追踪可以看到:
   • 总响应时间 245ms
   • 最慢的是 Order Service (120ms)
   • 三个服务调用是并发的 (try_join!)
   • 可以精确定位性能瓶颈
```

---

## 5. 多端 BFF 实现

### 5.1 统一入口 (`main.rs`)

```rust
// src/main.rs
use axum::{routing::get, Router};
use std::sync::Arc;
use tokio::sync::Mutex;
use tower_http::{
    trace::TraceLayer,
    cors::CorsLayer,
    compression::CompressionLayer,
};

mod bff;
mod clients;
mod middleware;
mod telemetry;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 初始化 OTLP
    telemetry::init_telemetry("bff-gateway")?;

    // 2. 初始化下游客户端
    let user_client = clients::UserClient::new("http://localhost:50051".to_string()).await?;
    let order_client = clients::OrderClient::new("http://localhost:50052".to_string()).await?;
    let product_client = clients::ProductClient::new("http://localhost:8080".to_string());

    // 3. 创建 Web BFF
    let web_aggregator = bff::web_bff::aggregators::WebAggregator::new(
        user_client.clone(),
        order_client.clone(),
        product_client.clone(),
    );
    let web_state = Arc::new(Mutex::new(web_aggregator));

    // 4. 创建 Mobile BFF
    let mobile_aggregator = bff::mobile_bff::aggregators::MobileAggregator::new(
        user_client,
        order_client,
        product_client,
    );
    let mobile_state = Arc::new(Mutex::new(mobile_aggregator));

    // 5. 构建路由
    let app = Router::new()
        // Web BFF 路由
        .route("/api/web/home/:user_id", get(bff::web_bff::handlers::get_web_home_page))
        .with_state(web_state)
        // Mobile BFF 路由
        .route("/api/mobile/home/:user_id", get(bff::mobile_bff::handlers::get_mobile_home_page))
        .with_state(mobile_state)
        // 中间件
        .layer(TraceLayer::new_for_http())
        .layer(CompressionLayer::new())
        .layer(CorsLayer::permissive());

    // 6. 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
    println!("🚀 BFF Gateway listening on {}", listener.local_addr()?);
    
    axum::serve(listener, app).await?;

    // 7. 关闭 OTLP
    telemetry::shutdown_telemetry();
    Ok(())
}
```

### 5.2 Web vs Mobile 响应对比

```bash
# Web BFF 请求
curl http://localhost:3000/api/web/home/user_123 | jq

# 响应 (完整数据):
{
  "user": {
    "id": "user_123",
    "name": "Alice",
    "email": "alice@example.com",
    "avatar_url": "https://cdn.example.com/alice.jpg",
    "membership_level": "Gold",
    "points": 5000
  },
  "recent_orders": [
    {
      "order_id": "order_001",
      "order_date": "2025-10-10",
      "total_amount": 299.99,
      "status": "Delivered",
      "items_count": 3,
      "product_thumbnails": ["img1.jpg", "img2.jpg", "img3.jpg"]
    }
  ],
  "recommended_products": [
    {
      "id": "prod_1",
      "name": "Laptop",
      "price": 999.99,
      "discount_price": 899.99,
      "image_url": "laptop.jpg",
      "rating": 4.5,
      "reviews_count": 128,
      "description": "High-performance laptop with 16GB RAM..."
    }
  ],
  "notifications": []
}
```

```bash
# Mobile BFF 请求
curl http://localhost:3000/api/mobile/home/user_123 | jq

# 响应 (精简数据,减少50%流量):
{
  "user": {
    "id": "user_123",
    "name": "Alice",
    "avatar": "https://cdn.example.com/alice.jpg",
    "level": "Gold"
  },
  "orders": [
    {
      "id": "order_001",
      "date": "2025-10-10",
      "amount": 299.99,
      "status": "Delivered",
      "thumbnail": "img1.jpg"
    }
  ],
  "products": [
    {
      "id": "prod_1",
      "name": "Laptop",
      "price": 999.99,
      "image": "laptop.jpg",
      "tags": ["热销"]
    }
  ]
}
```

**数据对比**:

| 字段 | Web BFF | Mobile BFF | 说明 |
|------|---------|------------|------|
| 用户邮箱 | ✅ | ❌ | Mobile 不显示敏感信息 |
| 订单数量 | 5个 | 3个 | Mobile 精简列表 |
| 商品描述 | 完整描述 | 标签 | Mobile 节省流量 |
| 通知列表 | ✅ | ❌ | Mobile 单独接口获取 |
| 响应大小 | ~8KB | ~3KB | Mobile 减少62.5%流量 |

---

## 6. GraphQL BFF 实现

### 6.1 为什么 BFF 适合 GraphQL?

```text
┌─────────────────────────────────────────────────────────────┐
│              GraphQL BFF 的优势                             │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ✅ 前端按需获取数据 (解决过度获取问题)                      │
│  ✅ 单次请求聚合多个微服务                                   │
│  ✅ 强类型 Schema (自动生成文档)                             │
│  ✅ 前端团队自主定义查询                                     │
│  ✅ 减少版本管理 (无需 /v1, /v2)                             │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 6.2 GraphQL Schema 定义

```graphql
# schema.graphql
type User {
  id: ID!
  name: String!
  email: String!
  avatar: String!
  membershipLevel: String!
  points: Int!
}

type Order {
  id: ID!
  orderDate: String!
  totalAmount: Float!
  status: String!
  items: [OrderItem!]!
}

type OrderItem {
  productId: String!
  productName: String!
  quantity: Int!
  price: Float!
}

type Product {
  id: ID!
  name: String!
  price: Float!
  imageUrl: String!
  description: String
  rating: Float
}

type Query {
  # 聚合查询:一次请求获取用户+订单+推荐商品
  homepage(userId: ID!): Homepage!
  
  # 独立查询
  user(userId: ID!): User
  orders(userId: ID!): [Order!]!
  products(ids: [ID!]!): [Product!]!
}

type Homepage {
  user: User!
  recentOrders: [Order!]!
  recommendedProducts: [Product!]!
}
```

### 6.3 Rust GraphQL 实现 (async-graphql)

```toml
# Cargo.toml 新增依赖
[dependencies]
async-graphql = "7.0"
async-graphql-axum = "7.0"
```

```rust
// src/bff/graphql_bff/schema.rs
use async_graphql::{Context, Object, Schema, ID};
use crate::clients::{UserClient, OrderClient, ProductClient};

pub struct Query;

#[Object]
impl Query {
    /// 聚合查询:主页数据
    async fn homepage(&self, ctx: &Context<'_>, user_id: ID) -> Result<Homepage, async_graphql::Error> {
        let user_client = ctx.data::<UserClient>()?;
        let order_client = ctx.data::<OrderClient>()?;
        let product_client = ctx.data::<ProductClient>()?;

        // 并发调用
        let (user, orders, products) = tokio::try_join!(
            user_client.clone().get_user(&user_id),
            order_client.clone().get_user_orders(&user_id),
            product_client.get_products_batch(&["prod_1".to_string()]),
        )?;

        Ok(Homepage {
            user: User::from(user),
            recent_orders: orders.into_iter().map(Order::from).collect(),
            recommended_products: products.into_iter().map(Product::from).collect(),
        })
    }
}

#[derive(Clone)]
pub struct Homepage {
    pub user: User,
    pub recent_orders: Vec<Order>,
    pub recommended_products: Vec<Product>,
}

#[Object]
impl Homepage {
    async fn user(&self) -> &User {
        &self.user
    }

    async fn recent_orders(&self) -> &Vec<Order> {
        &self.recent_orders
    }

    async fn recommended_products(&self) -> &Vec<Product> {
        &self.recommended_products
    }
}

#[derive(Clone)]
pub struct User {
    pub id: String,
    pub name: String,
    pub email: String,
    pub avatar: String,
    pub membership_level: String,
    pub points: i64,
}

#[Object]
impl User {
    async fn id(&self) -> &str {
        &self.id
    }

    async fn name(&self) -> &str {
        &self.name
    }

    async fn email(&self) -> &str {
        &self.email
    }

    async fn avatar(&self) -> &str {
        &self.avatar
    }

    async fn membership_level(&self) -> &str {
        &self.membership_level
    }

    async fn points(&self) -> i64 {
        self.points
    }
}

// Order, Product 类似实现...

pub type AppSchema = Schema<Query, async_graphql::EmptyMutation, async_graphql::EmptySubscription>;
```

### 6.4 GraphQL BFF 路由

```rust
// src/bff/graphql_bff/handlers.rs
use async_graphql::http::GraphiQLSource;
use async_graphql_axum::{GraphQLRequest, GraphQLResponse};
use axum::{
    extract::State,
    response::{Html, IntoResponse},
};
use crate::bff::graphql_bff::schema::AppSchema;

/// GraphQL 查询接口
pub async fn graphql_handler(
    State(schema): State<AppSchema>,
    req: GraphQLRequest,
) -> GraphQLResponse {
    schema.execute(req.into_inner()).await.into()
}

/// GraphiQL 调试界面
pub async fn graphiql() -> impl IntoResponse {
    Html(GraphiQLSource::build().endpoint("/graphql").finish())
}
```

### 6.5 GraphQL 查询示例

```graphql
# 前端按需查询 (只获取需要的字段)
query WebHomepage {
  homepage(userId: "user_123") {
    user {
      name
      avatar
      membershipLevel
    }
    recentOrders {
      id
      totalAmount
      status
    }
    recommendedProducts {
      id
      name
      price
      imageUrl
    }
  }
}
```

```graphql
# Mobile 端精简查询
query MobileHomepage {
  homepage(userId: "user_123") {
    user {
      name
      avatar
    }
    recentOrders {
      id
      status
    }
    recommendedProducts {
      name
      price
    }
  }
}
```

---

## 7. BFF 安全策略

### 7.1 JWT 认证中间件

```rust
// src/middleware/auth.rs
use axum::{
    extract::Request,
    http::{HeaderMap, StatusCode},
    middleware::Next,
    response::Response,
};
use jsonwebtoken::{decode, DecodingKey, Validation, Algorithm};
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct Claims {
    pub sub: String,
    pub exp: usize,
    pub role: String,
}

pub async fn jwt_auth(
    headers: HeaderMap,
    mut request: Request,
    next: Next,
) -> Result<Response, StatusCode> {
    // 1. 提取 Authorization header
    let auth_header = headers
        .get("Authorization")
        .and_then(|h| h.to_str().ok())
        .ok_or(StatusCode::UNAUTHORIZED)?;

    if !auth_header.starts_with("Bearer ") {
        return Err(StatusCode::UNAUTHORIZED);
    }

    let token = &auth_header[7..];

    // 2. 验证 JWT
    let secret = std::env::var("JWT_SECRET").unwrap_or_else(|_| "secret".to_string());
    let validation = Validation::new(Algorithm::HS256);

    let token_data = decode::<Claims>(
        token,
        &DecodingKey::from_secret(secret.as_ref()),
        &validation,
    )
    .map_err(|_| StatusCode::UNAUTHORIZED)?;

    // 3. 将用户信息注入请求扩展
    request.extensions_mut().insert(token_data.claims);

    Ok(next.run(request).await)
}
```

### 7.2 限流中间件 (Token Bucket)

```rust
// src/middleware/rate_limit.rs
use axum::{
    extract::Request,
    http::StatusCode,
    middleware::Next,
    response::Response,
};
use governor::{Quota, RateLimiter};
use std::sync::Arc;
use std::num::NonZeroU32;

pub type SharedRateLimiter = Arc<RateLimiter<
    governor::state::direct::NotKeyed,
    governor::state::InMemoryState,
    governor::clock::DefaultClock,
>>;

pub fn create_rate_limiter() -> SharedRateLimiter {
    Arc::new(RateLimiter::direct(
        Quota::per_second(NonZeroU32::new(100).unwrap()) // 100 req/s
    ))
}

pub async fn rate_limit_middleware(
    limiter: Arc<RateLimiter<_, _, _>>,
    request: Request,
    next: Next,
) -> Result<Response, StatusCode> {
    if limiter.check().is_err() {
        return Err(StatusCode::TOO_MANY_REQUESTS);
    }

    Ok(next.run(request).await)
}
```

### 7.3 熔断器中间件

```rust
// src/middleware/circuit_breaker.rs
use failsafe::{CircuitBreaker, Config, backoff::constant};
use std::sync::Arc;
use std::time::Duration;

pub type SharedCircuitBreaker = Arc<CircuitBreaker>;

pub fn create_circuit_breaker() -> SharedCircuitBreaker {
    Arc::new(CircuitBreaker::new(
        Config::new()
            .failure_rate_threshold(0.5) // 50% 失败率触发熔断
            .wait_duration_in_open_state(Duration::from_secs(30))
            .half_open_max_requests(5)
    ))
}
```

---

## 8. 性能优化与缓存

### 8.1 Redis 缓存层

```rust
// src/cache/redis_cache.rs
use redis::{Client, AsyncCommands};
use serde::{Serialize, de::DeserializeOwned};
use anyhow::Result;
use tracing::instrument;

#[derive(Clone)]
pub struct RedisCache {
    client: Client,
}

impl RedisCache {
    pub fn new(redis_url: &str) -> Result<Self> {
        let client = Client::open(redis_url)?;
        Ok(Self { client })
    }

    #[instrument(skip(self, value))]
    pub async fn set<T: Serialize>(
        &self,
        key: &str,
        value: &T,
        ttl_seconds: usize,
    ) -> Result<()> {
        let mut conn = self.client.get_multiplexed_async_connection().await?;
        let serialized = serde_json::to_string(value)?;
        conn.set_ex(key, serialized, ttl_seconds).await?;
        Ok(())
    }

    #[instrument(skip(self))]
    pub async fn get<T: DeserializeOwned>(&self, key: &str) -> Result<Option<T>> {
        let mut conn = self.client.get_multiplexed_async_connection().await?;
        let value: Option<String> = conn.get(key).await?;
        
        match value {
            Some(v) => Ok(Some(serde_json::from_str(&v)?)),
            None => Ok(None),
        }
    }
}
```

### 8.2 本地缓存 (moka)

```rust
// src/cache/local_cache.rs
use moka::future::Cache;
use std::time::Duration;
use serde::{Serialize, de::DeserializeOwned};

pub struct LocalCache<T> {
    cache: Cache<String, T>,
}

impl<T: Clone + Send + Sync + 'static> LocalCache<T> {
    pub fn new(max_capacity: u64, ttl: Duration) -> Self {
        let cache = Cache::builder()
            .max_capacity(max_capacity)
            .time_to_live(ttl)
            .build();

        Self { cache }
    }

    pub async fn get(&self, key: &str) -> Option<T> {
        self.cache.get(key).await
    }

    pub async fn set(&self, key: String, value: T) {
        self.cache.insert(key, value).await;
    }
}
```

### 8.3 二级缓存策略

```rust
// src/cache/mod.rs
pub mod redis_cache;
pub mod local_cache;

use anyhow::Result;
use serde::{Serialize, de::DeserializeOwned};
use tracing::{info, instrument};

pub struct TwoLevelCache<T> {
    local: local_cache::LocalCache<T>,
    redis: redis_cache::RedisCache,
}

impl<T: Clone + Send + Sync + Serialize + DeserializeOwned + 'static> TwoLevelCache<T> {
    pub fn new(local: local_cache::LocalCache<T>, redis: redis_cache::RedisCache) -> Self {
        Self { local, redis }
    }

    #[instrument(skip(self))]
    pub async fn get(&self, key: &str) -> Result<Option<T>> {
        // 1. 先查本地缓存 (L1)
        if let Some(value) = self.local.get(key).await {
            info!("✅ L1 Cache Hit: {}", key);
            return Ok(Some(value));
        }

        // 2. 再查 Redis (L2)
        if let Some(value) = self.redis.get::<T>(key).await? {
            info!("✅ L2 Cache Hit: {}", key);
            // 回填本地缓存
            self.local.set(key.to_string(), value.clone()).await;
            return Ok(Some(value));
        }

        info!("❌ Cache Miss: {}", key);
        Ok(None)
    }

    pub async fn set(&self, key: &str, value: &T, ttl_seconds: usize) -> Result<()> {
        // 同时写入 L1 和 L2
        self.local.set(key.to_string(), value.clone()).await;
        self.redis.set(key, value, ttl_seconds).await?;
        Ok(())
    }
}
```

### 8.4 缓存键策略

```rust
/// 缓存键命名规范
pub fn cache_key_for_web_homepage(user_id: &str) -> String {
    format!("bff:web:homepage:{}", user_id)
}

pub fn cache_key_for_mobile_homepage(user_id: &str) -> String {
    format!("bff:mobile:homepage:{}", user_id)
}

pub fn cache_key_for_user_profile(user_id: &str) -> String {
    format!("bff:user:profile:{}", user_id)
}

/// 使用示例
#[instrument(skip(self, cache))]
pub async fn aggregate_home_page_with_cache(
    &mut self,
    user_id: &str,
    cache: &TwoLevelCache<WebHomePageResponse>,
) -> Result<WebHomePageResponse> {
    let cache_key = cache_key_for_web_homepage(user_id);

    // 1. 尝试从缓存获取
    if let Some(cached) = cache.get(&cache_key).await? {
        return Ok(cached);
    }

    // 2. 缓存未命中,调用下游服务
    let response = self.aggregate_home_page(user_id).await?;

    // 3. 写入缓存 (TTL: 5分钟)
    cache.set(&cache_key, &response, 300).await?;

    Ok(response)
}
```

---

## 9. 部署与监控

### 9.1 Docker Compose 部署

```yaml
# docker-compose.yml
version: '3.8'

services:
  # Web BFF
  bff-web:
    build:
      context: .
      dockerfile: Dockerfile
    environment:
      - BFF_TYPE=web
      - USER_SERVICE_URL=http://user-service:50051
      - ORDER_SERVICE_URL=http://order-service:50052
      - PRODUCT_SERVICE_URL=http://product-service:8080
      - REDIS_URL=redis://redis:6379
      - OTLP_ENDPOINT=http://jaeger:4317
    ports:
      - "3001:3000"
    depends_on:
      - redis
      - jaeger

  # Mobile BFF
  bff-mobile:
    build:
      context: .
      dockerfile: Dockerfile
    environment:
      - BFF_TYPE=mobile
      - USER_SERVICE_URL=http://user-service:50051
      - ORDER_SERVICE_URL=http://order-service:50052
      - PRODUCT_SERVICE_URL=http://product-service:8080
      - REDIS_URL=redis://redis:6379
      - OTLP_ENDPOINT=http://jaeger:4317
    ports:
      - "3002:3000"
    depends_on:
      - redis
      - jaeger

  # Redis 缓存
  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"

  # Jaeger (OTLP 追踪)
  jaeger:
    image: jaegertracing/all-in-one:1.60
    environment:
      - COLLECTOR_OTLP_ENABLED=true
    ports:
      - "16686:16686"  # Jaeger UI
      - "4317:4317"    # OTLP gRPC
      - "4318:4318"    # OTLP HTTP

  # 下游微服务 (示例)
  user-service:
    image: user-service:latest
    ports:
      - "50051:50051"

  order-service:
    image: order-service:latest
    ports:
      - "50052:50052"

  product-service:
    image: product-service:latest
    ports:
      - "8080:8080"
```

### 9.2 Dockerfile

```dockerfile
# Dockerfile
FROM rust:1.90-slim AS builder

WORKDIR /app
COPY Cargo.toml Cargo.lock ./
COPY src ./src

RUN cargo build --release

FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y ca-certificates && rm -rf /var/lib/apt/lists/*

COPY --from=builder /app/target/release/bff-ecommerce /usr/local/bin/bff

EXPOSE 3000

CMD ["bff"]
```

### 9.3 健康检查接口

```rust
// src/main.rs
use axum::{routing::get, Json};
use serde_json::json;

async fn health_check() -> Json<serde_json::Value> {
    Json(json!({
        "status": "healthy",
        "version": env!("CARGO_PKG_VERSION"),
        "timestamp": chrono::Utc::now().to_rfc3339(),
    }))
}

// 路由配置
let app = Router::new()
    .route("/health", get(health_check))
    .route("/api/web/home/:user_id", get(get_web_home_page))
    // ...
```

### 9.4 Prometheus Metrics

```rust
// Cargo.toml
[dependencies]
metrics = "0.24"
metrics-exporter-prometheus = "0.16"
```

```rust
// src/telemetry/metrics.rs
use metrics::{counter, histogram, gauge};
use metrics_exporter_prometheus::PrometheusBuilder;
use std::time::Instant;

pub fn init_metrics() -> Result<(), Box<dyn std::error::Error>> {
    PrometheusBuilder::new()
        .install()?;
    Ok(())
}

/// 记录 BFF 请求
pub fn record_bff_request(bff_type: &str, endpoint: &str, duration_ms: f64, status: u16) {
    counter!("bff_requests_total", "bff_type" => bff_type.to_string(), "endpoint" => endpoint.to_string()).increment(1);
    histogram!("bff_request_duration_ms", "bff_type" => bff_type.to_string()).record(duration_ms);
    
    if status >= 500 {
        counter!("bff_errors_total", "bff_type" => bff_type.to_string()).increment(1);
    }
}

/// 记录缓存命中率
pub fn record_cache_hit(cache_type: &str, hit: bool) {
    let label = if hit { "hit" } else { "miss" };
    counter!("bff_cache_requests", "cache_type" => cache_type.to_string(), "result" => label.to_string()).increment(1);
}

/// 记录下游服务调用
pub fn record_downstream_call(service: &str, duration_ms: f64, success: bool) {
    histogram!("bff_downstream_duration_ms", "service" => service.to_string()).record(duration_ms);
    
    if !success {
        counter!("bff_downstream_errors", "service" => service.to_string()).increment(1);
    }
}
```

---

## 10. 最佳实践与陷阱

### 10.1 最佳实践

```rust
/// ✅ DO: BFF 最佳实践清单

// 1. 清晰的 BFF 边界
// ✅ 每个 BFF 只服务一个客户端类型
pub struct WebBFF { /* 只服务 Web 端 */ }
pub struct MobileBFF { /* 只服务 Mobile 端 */ }

// ❌ 不要创建通用 BFF
pub struct GenericBFF { /* 服务所有端,违背 BFF 初衷 */ }


// 2. 前端团队拥有 BFF
// ✅ 前端团队负责 BFF 的开发、部署、监控
// 组织结构:
//   Web 前端团队 → 开发和维护 Web BFF
//   Mobile 团队  → 开发和维护 Mobile BFF


// 3. 数据聚合而非代理
// ✅ DO: BFF 执行业务逻辑
pub async fn aggregate_order_details(&self, order_id: &str) -> Result<OrderDetails> {
    // 聚合多个服务的数据
    let (order, user, products, shipping) = tokio::try_join!(
        self.order_client.get_order(order_id),
        self.user_client.get_user(&order.user_id),
        self.product_client.get_products(&order.product_ids),
        self.shipping_client.get_tracking(&order.shipping_id),
    )?;

    // 组装前端友好的数据模型
    Ok(OrderDetails {
        order_info: order.into(),
        customer: user.into(),
        items: products.into(),
        tracking: shipping.into(),
    })
}

// ❌ DON'T: 简单代理 (应该用 API Gateway)
pub async fn proxy_get_order(&self, order_id: &str) -> Result<Order> {
    self.order_client.get_order(order_id).await // 仅仅转发,无价值
}


// 4. 针对性的数据模型
// ✅ DO: 为每个端定制模型
#[derive(Serialize)]
pub struct WebProductCard {
    pub id: String,
    pub name: String,
    pub price: f64,
    pub description: String,     // Web 显示完整描述
    pub detailed_specs: Vec<String>, // Web 显示详细规格
}

#[derive(Serialize)]
pub struct MobileProductCard {
    pub id: String,
    pub name: String,
    pub price: f64,
    pub tags: Vec<String>,       // Mobile 只显示标签
}


// 5. 合理的缓存策略
// ✅ DO: 二级缓存 (本地 + Redis)
pub async fn get_with_cache<T>(
    key: &str,
    local_cache: &LocalCache<T>,
    redis_cache: &RedisCache,
    fetch_fn: impl Future<Output = Result<T>>,
) -> Result<T>
where
    T: Clone + Serialize + DeserializeOwned + Send + Sync + 'static,
{
    // L1: 本地缓存
    if let Some(value) = local_cache.get(key).await {
        return Ok(value);
    }

    // L2: Redis
    if let Some(value) = redis_cache.get::<T>(key).await? {
        local_cache.set(key.to_string(), value.clone()).await;
        return Ok(value);
    }

    // 缓存未命中,调用原始函数
    let value = fetch_fn.await?;
    redis_cache.set(key, &value, 300).await?;
    local_cache.set(key.to_string(), value.clone()).await;
    Ok(value)
}


// 6. 完整的 OTLP 追踪
// ✅ DO: 追踪整个调用链
#[instrument(skip(self), fields(
    bff.type = "web",
    user_id = %user_id,
    otel.kind = "server"
))]
pub async fn aggregate_home_page(&mut self, user_id: &str) -> Result<WebHomePageResponse> {
    // 自动追踪所有下游调用
    // ...
}


// 7. 错误处理与降级
// ✅ DO: 优雅降级
pub async fn fetch_recommended_products(&self, user_id: &str) -> Vec<Product> {
    match self.recommendation_service.get_recommendations(user_id).await {
        Ok(products) => products,
        Err(e) => {
            tracing::warn!("Recommendation service failed: {:?}, falling back to hot products", e);
            self.fetch_hot_products().await.unwrap_or_default()
        }
    }
}


// 8. 版本管理
// ✅ DO: BFF 内部管理版本,对外统一接口
pub async fn get_home_page_v2(&self, user_id: &str) -> Result<HomePageResponse> {
    // 新版本逻辑
}

pub async fn get_home_page(&self, user_id: &str) -> Result<HomePageResponse> {
    // 根据 Feature Flag 决定调用哪个版本
    if self.feature_flags.is_enabled("homepage_v2") {
        self.get_home_page_v2(user_id).await
    } else {
        self.get_home_page_v1(user_id).await
    }
}
```

### 10.2 常见陷阱

```rust
/// ❌ ANTI-PATTERNS: 常见错误

// ❌ 陷阱 1: BFF 变成小型单体应用
// 问题: BFF 包含过多业务逻辑,变成小型单体
pub struct MegaBFF {
    // BFF 不应该直接访问数据库
    database: PostgresPool, // ❌ 错误!

    // BFF 不应该包含核心业务逻辑
    order_processor: OrderProcessor, // ❌ 错误!

    // BFF 应该只调用微服务
    order_client: OrderServiceClient, // ✅ 正确!
}


// ❌ 陷阱 2: BFF 之间共享代码
// 问题: Web BFF 和 Mobile BFF 共享业务逻辑,造成耦合
// ❌ 错误做法
pub struct SharedAggregator {
    /* 共享的聚合逻辑 */
}

impl SharedAggregator {
    pub fn aggregate_for_all(&self) -> GenericResponse {
        // Web 和 Mobile 都用这个,导致接口臃肿
    }
}

// ✅ 正确做法: 各自独立实现
pub struct WebAggregator { /* Web 专用逻辑 */ }
pub struct MobileAggregator { /* Mobile 专用逻辑 */ }

// 📌 可共享的: 工具库 (日志、追踪、缓存)
// 📌 不可共享的: 业务聚合逻辑


// ❌ 陷阱 3: 过度缓存
// 问题: 缓存过期策略不当,导致数据不一致
// ❌ 错误: 用户数据缓存1小时
cache.set("user:123", user_data, 3600); // 用户修改资料后看到旧数据!

// ✅ 正确: 根据数据特性设置 TTL
cache.set("user:profile:123", user_data, 300);        // 5分钟 (频繁变更)
cache.set("product:details:456", product_data, 3600); // 1小时 (较少变更)
cache.set("static:categories", categories, 86400);    // 1天 (几乎不变)


// ❌ 陷阱 4: N+1 查询问题
// 问题: 循环调用下游服务
// ❌ 错误做法
pub async fn get_order_details(&self, order_id: &str) -> Result<OrderDetails> {
    let order = self.order_client.get_order(order_id).await?;

    let mut products = vec![];
    for item in &order.items {
        // N+1 查询! 每个商品单独请求
        let product = self.product_client.get_product(&item.product_id).await?;
        products.push(product);
    }

    Ok(OrderDetails { order, products })
}

// ✅ 正确做法: 批量查询
pub async fn get_order_details(&self, order_id: &str) -> Result<OrderDetails> {
    let order = self.order_client.get_order(order_id).await?;

    let product_ids: Vec<_> = order.items.iter().map(|i| i.product_id.clone()).collect();
    let products = self.product_client.get_products_batch(&product_ids).await?; // 单次批量请求

    Ok(OrderDetails { order, products })
}


// ❌ 陷阱 5: 忽略超时和熔断
// ❌ 错误: 无限等待下游服务
pub async fn call_slow_service(&self) -> Result<Response> {
    self.client.call().await // 可能永久阻塞!
}

// ✅ 正确: 设置超时和熔断
pub async fn call_slow_service(&self) -> Result<Response> {
    let timeout = Duration::from_secs(3);
    
    match tokio::time::timeout(timeout, self.client.call()).await {
        Ok(Ok(response)) => Ok(response),
        Ok(Err(e)) => Err(e.into()),
        Err(_) => {
            tracing::error!("Service timeout after {:?}", timeout);
            Err(anyhow::anyhow!("Request timeout"))
        }
    }
}


// ❌ 陷阱 6: 串行调用
// ❌ 错误: 串行调用多个服务 (总耗时 = 各服务耗时之和)
pub async fn aggregate_data(&self) -> Result<Data> {
    let user = self.user_client.get_user().await?;      // 50ms
    let orders = self.order_client.get_orders().await?; // 100ms
    let products = self.product_client.get_products().await?; // 80ms
    // 总耗时: 50 + 100 + 80 = 230ms
}

// ✅ 正确: 并发调用 (总耗时 = max(各服务耗时))
pub async fn aggregate_data(&self) -> Result<Data> {
    let (user, orders, products) = tokio::try_join!(
        self.user_client.get_user(),        // 50ms
        self.order_client.get_orders(),     // 100ms
        self.product_client.get_products(), // 80ms
    )?;
    // 总耗时: max(50, 100, 80) = 100ms (减少 56%!)
}
```

### 10.3 BFF 架构演进路径

```text
┌─────────────────────────────────────────────────────────────┐
│              BFF 架构演进路径                               │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  阶段 1: 简单 BFF (REST API)                                │
│  ├── Web BFF: REST 接口聚合多个微服务                       │
│  ├── Mobile BFF: 精简版 REST 接口                           │
│  └── 特点: 简单直接,快速上线                                │
│                                                             │
│  阶段 2: GraphQL BFF                                        │
│  ├── 引入 GraphQL,前端按需查询                              │
│  ├── 减少过度获取和欠缺获取问题                             │
│  └── 特点: 灵活性高,前端自主性强                            │
│                                                             │
│  阶段 3: BFF + 缓存优化                                     │
│  ├── 二级缓存 (本地 + Redis)                                │
│  ├── 缓存预热和失效策略                                     │
│  └── 特点: 性能提升 10x                                     │
│                                                             │
│  阶段 4: BFF + AI 驱动                                      │
│  ├── 智能数据预加载 (预测用户下一步操作)                    │
│  ├── 个性化推荐聚合                                         │
│  └── 特点: 极致用户体验                                     │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 📚 参考资料

### 国际标准与最佳实践

1. **Martin Fowler - Pattern: Backends For Frontends**
   - <https://martinfowler.com/articles/micro-frontends.html>
   - BFF 模式的原始定义和最佳实践

2. **Microsoft Azure Architecture - Backend for Frontend pattern**
   - <https://learn.microsoft.com/en-us/azure/architecture/patterns/backends-for-frontends>
   - 企业级 BFF 架构指南

3. **CNCF - Cloud Native Patterns**
   - <https://www.cncf.io/>
   - 云原生架构中的 BFF 应用

4. **Sam Newman - Building Microservices (2nd Edition)**
   - Chapter: API Gateway and BFF
   - 微服务架构中的 BFF 设计

### Rust 生态

1. **Axum - Ergonomic web framework**
   - <https://github.com/tokio-rs/axum>
   - Rust 1.90 Web 框架最佳选择

2. **async-graphql - GraphQL for Rust**
   - <https://github.com/async-graphql/async-graphql>
   - Rust GraphQL BFF 实现

3. **OpenTelemetry Rust**
   - <https://github.com/open-telemetry/opentelemetry-rust>
   - Rust OTLP 追踪集成

### 实战案例

1. **Netflix - Edge Gateway (BFF 实践)**
   - Netflix 的 BFF 架构演进
   - Zuul → Zuul 2 → GraphQL Federation

2. **Spotify - Backend for Frontend at Scale**
   - Spotify 的多端 BFF 架构
   - 前端团队如何管理 BFF

---

## ✅ 总结

### BFF 模式核心价值

1. **定制化**: 每个前端获得专属优化的 API
2. **解耦**: 前端独立演进,互不影响
3. **性能**: 减少网络请求,精准数据聚合
4. **自主性**: 前端团队拥有完整控制权

### Rust 1.90 实现优势

- **类型安全**: 编译期保证数据模型一致性
- **高性能**: 零成本抽象,极致并发性能
- **可靠性**: 无 GC,低延迟,可预测的性能
- **生态**: Axum + Tokio + OpenTelemetry 成熟栈

### 适用场景

✅ **适合使用 BFF**:

- 多端应用 (Web + Mobile + Desktop)
- 频繁的数据聚合需求
- 前端团队需要自主权
- 遗留系统改造

❌ **不适合使用 BFF**:

- 单一前端应用
- 简单的 CRUD 操作
- 团队规模小,无法维护多个 BFF

---

**文档状态**: ✅ 生产就绪  
**最后更新**: 2025-10-11  
**维护者**: OTLP Rust Team
