# Strangler Fig 模式 (遗留系统改造) - Rust 1.90 + OTLP 完整实现指南

> **文档版本**: v1.0.0  
> **创建日期**: 2025-10-11  
> **Rust 版本**: 1.90  
> **OpenTelemetry**: 0.31.0  
> **对标标准**: Martin Fowler Strangler Fig Pattern, AWS Strangler Pattern, Microsoft Azure Migration Patterns

---

## 📑 目录

- [Strangler Fig 模式 (遗留系统改造) - Rust 1.90 + OTLP 完整实现指南](#strangler-fig-模式-遗留系统改造---rust-190--otlp-完整实现指南)
  - [📑 目录](#-目录)
  - [1. Strangler Fig 模式概述](#1-strangler-fig-模式概述)
    - [1.1 什么是 Strangler Fig?](#11-什么是-strangler-fig)
    - [1.2 核心组件](#12-核心组件)
    - [1.3 何时使用 Strangler Fig?](#13-何时使用-strangler-fig)
  - [2. 核心架构原理](#2-核心架构原理)
    - [2.1 Strangler Fig 架构层次](#21-strangler-fig-架构层次)
    - [2.2 迁移策略对比](#22-迁移策略对比)
  - [3. Rust 1.90 完整实现](#3-rust-190-完整实现)
    - [3.1 项目结构](#31-项目结构)
    - [3.2 依赖配置 (`Cargo.toml`)](#32-依赖配置-cargotoml)
    - [3.3 路由策略](#33-路由策略)
    - [3.4 Strangler Facade 实现](#34-strangler-facade-实现)
    - [3.5 新系统实现 (用户服务)](#35-新系统实现-用户服务)
    - [3.6 旧系统适配器](#36-旧系统适配器)
  - [4. 路由层设计](#4-路由层设计)
    - [4.1 路由策略配置](#41-路由策略配置)
    - [4.2 路由决策流程](#42-路由决策流程)
  - [5. 逐步迁移策略](#5-逐步迁移策略)
    - [5.1 迁移路线图](#51-迁移路线图)
    - [5.2 迁移步骤示例](#52-迁移步骤示例)
  - [6. 数据迁移方案](#6-数据迁移方案)
    - [6.1 双写策略](#61-双写策略)
    - [6.2 Change Data Capture (CDC)](#62-change-data-capture-cdc)
  - [7. OTLP 双系统追踪](#7-otlp-双系统追踪)
    - [7.1 追踪配置](#71-追踪配置)
    - [7.2 追踪示例](#72-追踪示例)
  - [8. 灰度发布与回滚](#8-灰度发布与回滚)
    - [8.1 灰度发布策略](#81-灰度发布策略)
    - [8.2 灰度发布流程](#82-灰度发布流程)
  - [9. 部署与监控](#9-部署与监控)
    - [9.1 Docker Compose 部署](#91-docker-compose-部署)
    - [9.2 监控指标](#92-监控指标)
  - [10. 最佳实践与陷阱](#10-最佳实践与陷阱)
    - [10.1 最佳实践](#101-最佳实践)
    - [10.2 常见陷阱](#102-常见陷阱)
    - [10.3 迁移检查清单](#103-迁移检查清单)
  - [📚 参考资料](#-参考资料)
    - [国际标准与最佳实践](#国际标准与最佳实践)
    - [实战案例](#实战案例)
  - [✅ 总结](#-总结)
    - [Strangler Fig 模式核心价值](#strangler-fig-模式核心价值)
    - [关键成功因素](#关键成功因素)
    - [适用场景](#适用场景)

---

## 1. Strangler Fig 模式概述

### 1.1 什么是 Strangler Fig?

**Strangler Fig Pattern** (绞杀者模式) 是一种逐步替换遗留系统的架构模式,通过在旧系统外围逐步构建新系统,最终完全取代旧系统。

**名称由来**: 源于热带雨林中的绞杀榕 (Strangler Fig Tree),这种植物从宿主树根部开始生长,逐渐包裹并最终取代宿主树。

```text
┌─────────────────────────────────────────────────────────────┐
│              传统"大爆炸"式重写 (Big Bang Rewrite)            │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  第1年: 停止所有功能开发,全力重写                            │
│  第2年: 继续重写...业务需求积压...                           │
│  第3年: 上线新系统 → 💥 灾难性失败                            │
│                                                             │
│  ❌ 问题:                                                    │
│     • 长期无新功能上线,业务受损                              │
│     • 需求变化,重写系统已过时                                │
│     • 一次性切换风险极高                                     │
│     • 投入巨大,很可能中途失败                                │
│                                                             │
└─────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────┐
│              Strangler Fig 模式 (渐进式替换)                 │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  阶段 1: 新增功能在新系统开发 (旧系统保持运行)               │
│  ┌───────────────┐                                          │
│  │  New System   │──┐                                       │
│  │  (20% 功能)   │  │                                       │
│  └───────────────┘  │    ┌──────────────────┐              │
│                     ├───►│  Routing Layer   │              │
│  ┌───────────────┐  │    └──────────────────┘              │
│  │  Old System   │──┘                                       │
│  │  (80% 功能)   │                                          │
│  └───────────────┘                                          │
│                                                             │
│  阶段 2: 逐步迁移旧功能到新系统                              │
│  ┌───────────────┐                                          │
│  │  New System   │──┐                                       │
│  │  (60% 功能)   │  │                                       │
│  └───────────────┘  │    ┌──────────────────┐              │
│                     ├───►│  Routing Layer   │              │
│  ┌───────────────┐  │    └──────────────────┘              │
│  │  Old System   │──┘                                       │
│  │  (40% 功能)   │                                          │
│  └───────────────┘                                          │
│                                                             │
│  阶段 3: 新系统完全取代旧系统                                │
│  ┌───────────────┐                                          │
│  │  New System   │                                          │
│  │  (100% 功能)  │──────► ✅ 旧系统下线                      │
│  └───────────────┘                                          │
│                                                             │
│  ✅ 优势:                                                    │
│     • 持续交付新功能,业务不中断                              │
│     • 小步迁移,风险可控                                      │
│     • 随时可回滚                                             │
│     • 团队逐步学习新技术                                     │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 1.2 核心组件

```rust
/// Strangler Fig 模式的核心组件
pub struct StranglerFigArchitecture {
    /// 1. 路由层 (Routing Layer / Facade)
    /// 作为单一入口,决定请求由新系统还是旧系统处理
    routing_layer: RoutingFacade,

    /// 2. 新系统 (New System)
    /// 用现代技术栈 (Rust, OTLP) 构建的新功能
    new_system: ModernRustService,

    /// 3. 旧系统 (Legacy System)
    /// 保持运行的遗留系统 (如 Java/PHP 单体应用)
    legacy_system: LegacySystemAdapter,

    /// 4. 迁移追踪器 (Migration Tracker)
    /// 记录哪些功能已迁移,哪些还在旧系统
    migration_tracker: MigrationTracker,
}

/// 路由决策逻辑
#[derive(Debug, Clone)]
pub enum RouteTarget {
    /// 路由到新系统
    NewSystem {
        reason: String,
    },

    /// 路由到旧系统
    LegacySystem {
        reason: String,
    },

    /// 混合模式 (部分由新系统处理,部分由旧系统处理)
    Hybrid {
        primary: Box<RouteTarget>,
        fallback: Box<RouteTarget>,
    },
}
```

### 1.3 何时使用 Strangler Fig?

| 场景 | 是否适用 | 原因 |
|------|---------|------|
| 遗留单体应用现代化 | ✅ **强烈推荐** | 渐进式迁移,风险可控 |
| 技术栈升级 (Java → Rust) | ✅ 推荐 | 逐步学习新技术,避免"大爆炸" |
| 数据库迁移 (SQL → NoSQL) | ✅ 推荐 | 双写策略,逐步验证新数据库 |
| 全新业务系统 | ❌ 不必要 | 直接用新技术栈从零构建 |
| 小型应用 (< 1万行代码) | ❌ 过度工程 | 直接重写即可 |
| 旧系统即将下线 | ⚠️ 视情况 | 如果下线时间 < 6个月,不值得迁移 |

---

## 2. 核心架构原理

### 2.1 Strangler Fig 架构层次

```text
┌────────────────────────────────────────────────────────────────┐
│                         Clients                                │
│           (Web, Mobile, Desktop, APIs)                         │
└────────────────────┬───────────────────────────────────────────┘
                     │ HTTPS
┌────────────────────▼───────────────────────────────────────────┐
│               Strangler Facade (路由层)                         │
│  ┌────────────────────────────────────────────────────────┐    │
│  │  Routing Logic (Rust + Axum)                           │    │
│  │  • 基于路径路由: /api/v2/* → New System                │    │
│  │  • 基于特性标志: Feature Flag → New System             │    │
│  │  • 基于用户: Beta Users → New System                   │    │
│  │  • 基于百分比: 10% Traffic → New System                │    │
│  └────────────────────────────────────────────────────────┘    │
│                                                                │
│  ⚡ OTLP 追踪注入点                                             │
└────────────────────┬───────────────────┬───────────────────────┘
                     │                   │
         ┌───────────▼─────────┐  ┌──────▼──────────────┐
         │   New System        │  │  Legacy System      │
         │   (Rust + OTLP)     │  │  (Java/PHP)         │
         ├─────────────────────┤  ├─────────────────────┤
         │ • Modern Stack      │  │ • Monolithic App    │
         │ • Microservices     │  │ • MySQL Database    │
         │ • PostgreSQL        │  │ • No Observability  │
         │ • Full Observability│  │ • Legacy Code       │
         └─────────────────────┘  └─────────────────────┘
                     │                   │
         ┌───────────▼───────────────────▼──────────────┐
         │       Shared Data Layer (过渡期)             │
         │  • Dual Writes (同时写新旧数据库)            │
         │  • Event Streaming (CDC)                     │
         │  • API Contracts (数据同步)                  │
         └──────────────────────────────────────────────┘
```

### 2.2 迁移策略对比

| 策略 | 说明 | 优势 | 劣势 | 适用场景 |
|------|------|------|------|---------|
| **按路径迁移** | `/api/v2/*` → 新系统 `/api/v1/*` → 旧系统 | 简单清晰,易于管理 | 需要客户端改 API | 有版本控制的 API |
| **按功能迁移** | `/users` → 新系统 `/orders` → 旧系统 | 业务逻辑清晰 | 需要拆分数据库 | 功能模块独立 |
| **按灰度发布** | 10% 流量 → 新系统 90% 流量 → 旧系统 | 风险可控,可随时回滚 | 需要流量管理 | 高风险功能迁移 |
| **按用户分组** | Beta 用户 → 新系统 普通用户 → 旧系统 | 可收集真实反馈 | 需要用户管理系统 | 面向用户的功能 |

---

## 3. Rust 1.90 完整实现

### 3.1 项目结构

```text
strangler-migration/
├── Cargo.toml
├── .env
├── docker-compose.yml
├── src/
│   ├── main.rs
│   │
│   ├── routing/                  # 路由层 (核心)
│   │   ├── mod.rs
│   │   ├── facade.rs             # Strangler Facade
│   │   ├── strategies.rs         # 路由策略
│   │   └── feature_flags.rs      # 特性标志
│   │
│   ├── new_system/               # 新系统 (Rust 实现)
│   │   ├── mod.rs
│   │   ├── user_service.rs       # 用户服务 (已迁移)
│   │   └── handlers.rs
│   │
│   ├── legacy/                   # 旧系统适配器
│   │   ├── mod.rs
│   │   ├── adapter.rs            # HTTP 代理到旧系统
│   │   └── models.rs             # 旧系统数据模型
│   │
│   ├── data_sync/                # 数据同步
│   │   ├── mod.rs
│   │   ├── dual_write.rs         # 双写策略
│   │   └── cdc.rs                # Change Data Capture
│   │
│   ├── migration/                # 迁移管理
│   │   ├── mod.rs
│   │   ├── tracker.rs            # 迁移进度追踪
│   │   └── rollback.rs           # 回滚机制
│   │
│   ├── telemetry/                # OTLP 配置
│   │   └── mod.rs
│   │
│   └── config.rs
│
└── tests/
    ├── integration_tests.rs
    └── migration_tests.rs
```

### 3.2 依赖配置 (`Cargo.toml`)

```toml
[package]
name = "strangler-migration"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# Web 框架
axum = "0.7"
tower = { version = "0.5", features = ["full"] }
tower-http = { version = "0.6", features = ["trace", "cors"] }

# 异步运行时
tokio = { version = "1.41", features = ["full"] }

# HTTP 客户端 (代理到旧系统)
reqwest = { version = "0.12", features = ["json"] }
hyper = { version = "1.5", features = ["full"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 数据库 (新系统)
sqlx = { version = "0.8", features = ["runtime-tokio", "postgres"] }

# 特性标志
launchdarkly-server-sdk = "1.1"  # LaunchDarkly SDK

# OpenTelemetry
opentelemetry = "0.31"
opentelemetry-otlp = "0.31"
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
tracing-opentelemetry = "0.31"

# 错误处理
thiserror = "2.0"
anyhow = "1.0"

# 配置
dotenvy = "0.15"

# UUID
uuid = { version = "1.11", features = ["v4", "serde"] }
```

### 3.3 路由策略

```rust
// src/routing/strategies.rs
use axum::http::{Request, Uri};
use tracing::{info, instrument};

/// 路由策略
#[derive(Debug, Clone)]
pub enum RoutingStrategy {
    /// 基于路径路由
    PathBased {
        new_system_prefixes: Vec<String>,
    },

    /// 基于特性标志
    FeatureFlag {
        flag_key: String,
    },

    /// 基于用户分组
    UserBased {
        beta_user_ids: Vec<String>,
    },

    /// 基于流量百分比 (灰度发布)
    PercentageBased {
        new_system_percentage: u8, // 0-100
    },

    /// 组合策略
    Combined {
        strategies: Vec<RoutingStrategy>,
    },
}

impl RoutingStrategy {
    /// 决定请求路由到新系统还是旧系统
    #[instrument(skip(self, request))]
    pub fn should_route_to_new_system<B>(
        &self,
        request: &Request<B>,
        user_id: Option<&str>,
    ) -> bool {
        match self {
            Self::PathBased { new_system_prefixes } => {
                let path = request.uri().path();
                new_system_prefixes.iter().any(|prefix| path.starts_with(prefix))
            }

            Self::FeatureFlag { flag_key } => {
                // 集成特性标志服务 (如 LaunchDarkly)
                self.check_feature_flag(flag_key, user_id)
            }

            Self::UserBased { beta_user_ids } => {
                user_id.map_or(false, |id| beta_user_ids.contains(&id.to_string()))
            }

            Self::PercentageBased { new_system_percentage } => {
                // 基于请求 ID 的一致性哈希
                let request_id = self.extract_request_id(request);
                let hash = self.hash_request_id(&request_id);
                (hash % 100) < (*new_system_percentage as u64)
            }

            Self::Combined { strategies } => {
                // 任意一个策略匹配即路由到新系统
                strategies.iter().any(|s| s.should_route_to_new_system(request, user_id))
            }
        }
    }

    fn check_feature_flag(&self, flag_key: &str, user_id: Option<&str>) -> bool {
        // 简化示例:实际应集成 LaunchDarkly/Unleash
        // let client = LaunchDarklyClient::new();
        // client.variation(flag_key, user_id, false)
        
        // 示例:硬编码特性标志
        match flag_key {
            "new_user_service" => true,
            "new_order_service" => false,
            _ => false,
        }
    }

    fn extract_request_id<B>(&self, request: &Request<B>) -> String {
        request
            .headers()
            .get("X-Request-ID")
            .and_then(|v| v.to_str().ok())
            .unwrap_or("default")
            .to_string()
    }

    fn hash_request_id(&self, request_id: &str) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut hasher = DefaultHasher::new();
        request_id.hash(&mut hasher);
        hasher.finish()
    }
}
```

### 3.4 Strangler Facade 实现

```rust
// src/routing/facade.rs
use axum::{
    body::Body,
    extract::{Request, State},
    http::{StatusCode, HeaderMap},
    response::{IntoResponse, Response},
};
use reqwest::Client;
use tracing::{info, warn, instrument, Span};
use opentelemetry::trace::{Span as OtelSpan, Tracer};
use opentelemetry::global;
use crate::routing::strategies::RoutingStrategy;

#[derive(Clone)]
pub struct StranglerFacade {
    /// 路由策略
    strategy: RoutingStrategy,

    /// 旧系统 URL
    legacy_base_url: String,

    /// HTTP 客户端 (代理到旧系统)
    http_client: Client,
}

impl StranglerFacade {
    pub fn new(strategy: RoutingStrategy, legacy_base_url: String) -> Self {
        Self {
            strategy,
            legacy_base_url,
            http_client: Client::new(),
        }
    }

    /// 路由决策入口
    #[instrument(skip(self, request), fields(
        request_path = %request.uri().path(),
        otel.kind = "server"
    ))]
    pub async fn route(&self, request: Request) -> Result<Response, StranglerError> {
        let user_id = self.extract_user_id(&request);

        // 1. 决定路由目标
        let should_use_new_system = self.strategy.should_route_to_new_system(&request, user_id.as_deref());

        if should_use_new_system {
            info!("🆕 Routing to NEW SYSTEM: {}", request.uri().path());
            Span::current().record("routing.target", "new_system");
            
            // 路由到新系统 (通过 Axum 路由)
            // 实际实现中,这里会调用新系统的 handler
            Ok(self.handle_new_system(request).await?)
        } else {
            info!("🕰️ Routing to LEGACY SYSTEM: {}", request.uri().path());
            Span::current().record("routing.target", "legacy_system");

            // 代理到旧系统
            Ok(self.proxy_to_legacy(request).await?)
        }
    }

    /// 处理新系统请求
    async fn handle_new_system(&self, request: Request) -> Result<Response, StranglerError> {
        // 在实际实现中,这里会根据路径调用对应的新系统 handler
        // 这里简化为直接返回成功
        Ok(Response::builder()
            .status(StatusCode::OK)
            .header("X-Served-By", "NewSystem")
            .body(Body::from("Handled by new Rust system"))
            .unwrap())
    }

    /// 代理到旧系统
    #[instrument(skip(self, request))]
    async fn proxy_to_legacy(&self, request: Request) -> Result<Response, StranglerError> {
        let (parts, body) = request.into_parts();
        
        // 构建旧系统 URL
        let legacy_url = format!("{}{}", self.legacy_base_url, parts.uri.path());
        
        info!("📡 Proxying to legacy system: {}", legacy_url);

        // 转换请求方法
        let method = match parts.method.as_str() {
            "GET" => reqwest::Method::GET,
            "POST" => reqwest::Method::POST,
            "PUT" => reqwest::Method::PUT,
            "DELETE" => reqwest::Method::DELETE,
            _ => reqwest::Method::GET,
        };

        // 转发请求到旧系统
        let legacy_response = self
            .http_client
            .request(method, &legacy_url)
            .headers(Self::convert_headers(&parts.headers))
            .send()
            .await
            .map_err(|e| StranglerError::LegacySystemError(e.to_string()))?;

        // 转换响应
        let status = legacy_response.status();
        let response_body = legacy_response
            .text()
            .await
            .map_err(|e| StranglerError::LegacySystemError(e.to_string()))?;

        Ok(Response::builder()
            .status(status)
            .header("X-Served-By", "LegacySystem")
            .body(Body::from(response_body))
            .unwrap())
    }

    fn extract_user_id(&self, request: &Request) -> Option<String> {
        // 从 JWT 或 Header 中提取用户 ID
        request
            .headers()
            .get("X-User-ID")
            .and_then(|v| v.to_str().ok())
            .map(|s| s.to_string())
    }

    fn convert_headers(headers: &HeaderMap) -> reqwest::header::HeaderMap {
        let mut new_headers = reqwest::header::HeaderMap::new();
        for (key, value) in headers.iter() {
            if let Ok(value) = reqwest::header::HeaderValue::from_bytes(value.as_bytes()) {
                new_headers.insert(key.clone(), value);
            }
        }
        new_headers
    }
}

#[derive(Debug, thiserror::Error)]
pub enum StranglerError {
    #[error("Legacy system error: {0}")]
    LegacySystemError(String),

    #[error("New system error: {0}")]
    NewSystemError(String),
}

impl IntoResponse for StranglerError {
    fn into_response(self) -> Response {
        let (status, message) = match self {
            Self::LegacySystemError(msg) => (StatusCode::BAD_GATEWAY, msg),
            Self::NewSystemError(msg) => (StatusCode::INTERNAL_SERVER_ERROR, msg),
        };

        (status, message).into_response()
    }
}
```

### 3.5 新系统实现 (用户服务)

```rust
// src/new_system/user_service.rs
use sqlx::PgPool;
use serde::{Deserialize, Serialize};
use tracing::instrument;
use uuid::Uuid;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct User {
    pub id: Uuid,
    pub name: String,
    pub email: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

pub struct UserService {
    db: PgPool,
}

impl UserService {
    pub fn new(db: PgPool) -> Self {
        Self { db }
    }

    #[instrument(skip(self))]
    pub async fn get_user(&self, user_id: Uuid) -> Result<User, sqlx::Error> {
        let user = sqlx::query_as!(
            User,
            r#"
            SELECT id, name, email, created_at
            FROM users
            WHERE id = $1
            "#,
            user_id
        )
        .fetch_one(&self.db)
        .await?;

        Ok(user)
    }

    #[instrument(skip(self))]
    pub async fn create_user(&self, name: String, email: String) -> Result<User, sqlx::Error> {
        let user = sqlx::query_as!(
            User,
            r#"
            INSERT INTO users (id, name, email, created_at)
            VALUES ($1, $2, $3, $4)
            RETURNING id, name, email, created_at
            "#,
            Uuid::new_v4(),
            name,
            email,
            chrono::Utc::now()
        )
        .fetch_one(&self.db)
        .await?;

        Ok(user)
    }
}
```

### 3.6 旧系统适配器

```rust
// src/legacy/adapter.rs
use reqwest::Client;
use serde::{Deserialize, Serialize};
use tracing::instrument;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LegacyUser {
    pub user_id: i64,
    pub username: String,
    pub email_address: String,
}

pub struct LegacyAdapter {
    client: Client,
    base_url: String,
}

impl LegacyAdapter {
    pub fn new(base_url: String) -> Self {
        Self {
            client: Client::new(),
            base_url,
        }
    }

    #[instrument(skip(self))]
    pub async fn get_user(&self, user_id: i64) -> Result<LegacyUser, reqwest::Error> {
        let url = format!("{}/api/users/{}", self.base_url, user_id);
        
        let user = self
            .client
            .get(&url)
            .send()
            .await?
            .error_for_status()?
            .json::<LegacyUser>()
            .await?;

        Ok(user)
    }
}
```

---

## 4. 路由层设计

### 4.1 路由策略配置

```rust
// src/main.rs
use axum::{routing::any, Router};
use crate::routing::{facade::StranglerFacade, strategies::RoutingStrategy};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 初始化 OTLP
    telemetry::init_telemetry("strangler-facade")?;

    // 2. 配置路由策略
    let strategy = RoutingStrategy::Combined {
        strategies: vec![
            // 策略 1: 所有 /api/v2/* 路由到新系统
            RoutingStrategy::PathBased {
                new_system_prefixes: vec!["/api/v2/".to_string()],
            },
            // 策略 2: 特性标志控制
            RoutingStrategy::FeatureFlag {
                flag_key: "new_user_service".to_string(),
            },
            // 策略 3: 10% 流量灰度
            RoutingStrategy::PercentageBased {
                new_system_percentage: 10,
            },
        ],
    };

    // 3. 创建 Strangler Facade
    let facade = StranglerFacade::new(
        strategy,
        "http://legacy-system:8080".to_string(),
    );

    // 4. 构建路由
    let app = Router::new()
        .route("/*path", any(|req| async move {
            facade.route(req).await
        }));

    // 5. 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
    println!("🚀 Strangler Facade listening on {}", listener.local_addr()?);
    
    axum::serve(listener, app).await?;

    telemetry::shutdown_telemetry();
    Ok(())
}
```

### 4.2 路由决策流程

```text
┌────────────────────────────────────────────────────────────┐
│           路由决策流程 (Strangler Facade)                  │
├────────────────────────────────────────────────────────────┤
│                                                            │
│  1️⃣ 接收请求                                               │
│     GET /api/users/123                                     │
│     Headers: X-User-ID: user_456                           │
│                                                            │
│  2️⃣ 提取上下文                                             │
│     • 路径: /api/users/123                                 │
│     • 用户 ID: user_456                                    │
│     • 请求 ID: req_789                                     │
│                                                            │
│  3️⃣ 执行路由策略 (Combined)                                │
│     ┌─────────────────────────────────────────┐           │
│     │ 策略 1: PathBased                        │           │
│     │   /api/users/123 starts with /api/v2/?  │           │
│     │   ❌ NO                                   │           │
│     └─────────────────────────────────────────┘           │
│     ┌─────────────────────────────────────────┐           │
│     │ 策略 2: FeatureFlag                      │           │
│     │   Check flag "new_user_service"         │           │
│     │   ✅ YES (flag enabled)                  │           │
│     └─────────────────────────────────────────┘           │
│                                                            │
│  4️⃣ 路由到新系统 ✅                                         │
│     • 记录追踪 Span: routing.target = "new_system"        │
│     • 调用新系统 User Service                              │
│     • 返回响应                                             │
│                                                            │
│  5️⃣ 如果策略都不匹配                                       │
│     • 路由到旧系统 🕰️                                       │
│     • HTTP 代理到 http://legacy-system:8080/api/users/123 │
│     • 返回响应                                             │
│                                                            │
└────────────────────────────────────────────────────────────┘
```

---

## 5. 逐步迁移策略

### 5.1 迁移路线图

```rust
// src/migration/tracker.rs
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use chrono::{DateTime, Utc};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MigrationPlan {
    pub phases: Vec<MigrationPhase>,
    pub current_phase: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MigrationPhase {
    pub phase_number: usize,
    pub name: String,
    pub start_date: DateTime<Utc>,
    pub target_end_date: DateTime<Utc>,
    pub features: Vec<Feature>,
    pub status: PhaseStatus,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Feature {
    pub name: String,
    pub endpoints: Vec<String>,
    pub status: FeatureStatus,
    pub migration_percentage: u8, // 0-100
    pub rollback_plan: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum PhaseStatus {
    Planned,
    InProgress,
    Testing,
    Completed,
    Rollback,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum FeatureStatus {
    NotStarted,
    Development,
    Testing,
    Migrating,      // 灰度发布中
    Completed,
    Rollback,
}

impl MigrationPlan {
    /// 创建示例迁移计划
    pub fn create_example() -> Self {
        Self {
            current_phase: 1,
            phases: vec![
                MigrationPhase {
                    phase_number: 1,
                    name: "用户服务迁移".to_string(),
                    start_date: Utc::now(),
                    target_end_date: Utc::now() + chrono::Duration::days(30),
                    features: vec![
                        Feature {
                            name: "用户注册".to_string(),
                            endpoints: vec!["/api/users/register".to_string()],
                            status: FeatureStatus::Completed,
                            migration_percentage: 100,
                            rollback_plan: "切换路由回旧系统".to_string(),
                        },
                        Feature {
                            name: "用户登录".to_string(),
                            endpoints: vec!["/api/users/login".to_string()],
                            status: FeatureStatus::Migrating,
                            migration_percentage: 50,
                            rollback_plan: "关闭特性标志".to_string(),
                        },
                    ],
                    status: PhaseStatus::InProgress,
                },
                MigrationPhase {
                    phase_number: 2,
                    name: "订单服务迁移".to_string(),
                    start_date: Utc::now() + chrono::Duration::days(30),
                    target_end_date: Utc::now() + chrono::Duration::days(60),
                    features: vec![
                        Feature {
                            name: "创建订单".to_string(),
                            endpoints: vec!["/api/orders".to_string()],
                            status: FeatureStatus::NotStarted,
                            migration_percentage: 0,
                            rollback_plan: "数据双写回滚".to_string(),
                        },
                    ],
                    status: PhaseStatus::Planned,
                },
            ],
        }
    }

    /// 获取当前阶段
    pub fn get_current_phase(&self) -> Option<&MigrationPhase> {
        self.phases.get(self.current_phase)
    }

    /// 更新功能迁移进度
    pub fn update_feature_progress(&mut self, feature_name: &str, percentage: u8) {
        for phase in &mut self.phases {
            for feature in &mut phase.features {
                if feature.name == feature_name {
                    feature.migration_percentage = percentage;
                    
                    // 自动更新状态
                    feature.status = match percentage {
                        0 => FeatureStatus::NotStarted,
                        1..=99 => FeatureStatus::Migrating,
                        100 => FeatureStatus::Completed,
                        _ => feature.status.clone(),
                    };
                }
            }
        }
    }
}
```

### 5.2 迁移步骤示例

```text
┌────────────────────────────────────────────────────────────┐
│              阶段 1: 用户服务迁移 (30天)                   │
├────────────────────────────────────────────────────────────┤
│                                                            │
│  Week 1: 开发新用户服务                                    │
│    ✅ Day 1-2: 设计数据模型 (PostgreSQL)                   │
│    ✅ Day 3-5: 实现核心 API (Rust + Axum)                  │
│    ✅ Day 6-7: 单元测试 + 集成测试                         │
│                                                            │
│  Week 2: 双写策略                                          │
│    ✅ Day 8-10: 实现双写逻辑 (写新旧数据库)                │
│    ✅ Day 11-12: 数据一致性验证                            │
│    ✅ Day 13-14: 灰度发布准备 (Feature Flag)               │
│                                                            │
│  Week 3: 灰度发布                                          │
│    ✅ Day 15-16: 1% 流量到新系统                           │
│    ✅ Day 17-18: 10% 流量 (监控指标)                       │
│    ✅ Day 19-20: 50% 流量                                  │
│    ✅ Day 21: 100% 流量 (完全迁移)                         │
│                                                            │
│  Week 4: 清理与优化                                        │
│    ✅ Day 22-24: 数据一致性检查                            │
│    ✅ Day 25-27: 停止双写,迁移历史数据                     │
│    ✅ Day 28-30: 下线旧用户服务代码                        │
│                                                            │
└────────────────────────────────────────────────────────────┘
```

---

## 6. 数据迁移方案

### 6.1 双写策略

```rust
// src/data_sync/dual_write.rs
use sqlx::PgPool;
use tracing::{info, warn, instrument};
use anyhow::Result;

pub struct DualWriteService {
    /// 新系统数据库
    new_db: PgPool,

    /// 旧系统数据库 (或 HTTP API)
    legacy_adapter: crate::legacy::adapter::LegacyAdapter,
}

impl DualWriteService {
    pub fn new(new_db: PgPool, legacy_adapter: crate::legacy::adapter::LegacyAdapter) -> Self {
        Self {
            new_db,
            legacy_adapter,
        }
    }

    /// 创建用户 (双写)
    #[instrument(skip(self))]
    pub async fn create_user_dual_write(
        &self,
        name: String,
        email: String,
    ) -> Result<uuid::Uuid> {
        info!("📝 Dual Write: Creating user in both systems");

        // 1. 写入新系统 (PostgreSQL)
        let new_user_id = sqlx::query_scalar!(
            r#"
            INSERT INTO users (id, name, email, created_at)
            VALUES ($1, $2, $3, $4)
            RETURNING id
            "#,
            uuid::Uuid::new_v4(),
            name.clone(),
            email.clone(),
            chrono::Utc::now()
        )
        .fetch_one(&self.new_db)
        .await?;

        info!("✅ New system write successful: {}", new_user_id);

        // 2. 写入旧系统 (HTTP API)
        match self.write_to_legacy_system(&name, &email).await {
            Ok(legacy_id) => {
                info!("✅ Legacy system write successful: {}", legacy_id);
            }
            Err(e) => {
                // 旧系统写入失败,记录警告但不阻塞 (优雅降级)
                warn!("⚠️ Legacy system write failed: {:?}", e);
                warn!("   New system data is still valid, will sync later");
            }
        }

        Ok(new_user_id)
    }

    async fn write_to_legacy_system(&self, name: &str, email: &str) -> Result<i64> {
        // 调用旧系统 API 创建用户
        // 实际实现中,这里会调用旧系统的 HTTP API
        Ok(12345) // 简化示例
    }
}
```

### 6.2 Change Data Capture (CDC)

```rust
// src/data_sync/cdc.rs
use sqlx::PgPool;
use tokio::time::{interval, Duration};
use tracing::{info, instrument};

/// CDC 同步服务 (从旧系统同步到新系统)
pub struct CdcSyncService {
    legacy_db: PgPool,
    new_db: PgPool,
}

impl CdcSyncService {
    pub fn new(legacy_db: PgPool, new_db: PgPool) -> Self {
        Self { legacy_db, new_db }
    }

    /// 启动 CDC 同步 (定期轮询)
    #[instrument(skip(self))]
    pub async fn start_sync(&self) {
        let mut tick = interval(Duration::from_secs(60)); // 每分钟同步一次

        loop {
            tick.tick().await;
            info!("🔄 CDC Sync: Fetching changes from legacy system");

            match self.sync_user_changes().await {
                Ok(count) => info!("✅ Synced {} users from legacy system", count),
                Err(e) => tracing::error!("❌ CDC Sync failed: {:?}", e),
            }
        }
    }

    async fn sync_user_changes(&self) -> Result<usize, sqlx::Error> {
        // 1. 从旧系统获取最近修改的用户
        let legacy_users = sqlx::query!(
            r#"
            SELECT user_id, username, email_address, updated_at
            FROM users
            WHERE updated_at > NOW() - INTERVAL '1 minute'
            "#
        )
        .fetch_all(&self.legacy_db)
        .await?;

        let mut synced_count = 0;

        // 2. 同步到新系统
        for user in legacy_users {
            sqlx::query!(
                r#"
                INSERT INTO users (id, name, email, created_at)
                VALUES ($1, $2, $3, $4)
                ON CONFLICT (id) DO UPDATE
                SET name = EXCLUDED.name,
                    email = EXCLUDED.email
                "#,
                uuid::Uuid::new_v4(), // 实际应映射旧系统 ID
                user.username,
                user.email_address,
                user.updated_at.unwrap_or_else(chrono::Utc::now)
            )
            .execute(&self.new_db)
            .await?;

            synced_count += 1;
        }

        Ok(synced_count)
    }
}
```

---

## 7. OTLP 双系统追踪

### 7.1 追踪配置

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
                    KeyValue::new("deployment.environment", "migration"),
                ])),
        )
        .install_batch(runtime::Tokio)?;

    global::set_tracer_provider(tracer.provider().unwrap());

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

### 7.2 追踪示例

```text
🔍 Jaeger Trace 示例 (Strangler Fig):

Trace ID: abc123def456
Span 1: strangler_facade.route (duration: 150ms)
  ├── Attribute: routing.strategy = "Combined"
  ├── Attribute: routing.target = "new_system"
  ├── Attribute: request.path = "/api/users/login"
  │
  ├── Span 2: routing_strategy.evaluate (duration: 5ms)
  │   ├── Attribute: strategy.type = "PathBased"
  │   └── Attribute: strategy.result = "false"
  │
  ├── Span 3: routing_strategy.evaluate (duration: 10ms)
  │   ├── Attribute: strategy.type = "FeatureFlag"
  │   ├── Attribute: flag.key = "new_user_service"
  │   └── Attribute: strategy.result = "true" ✅
  │
  └── Span 4: new_system.user_service.login (duration: 120ms)
      ├── Span 5: postgres.query (duration: 45ms)
      │   └── SQL: SELECT * FROM users WHERE email = ?
      │
      └── Span 6: jwt.generate (duration: 15ms)

✅ 通过追踪可以看到:
   • 请求被路由到新系统
   • FeatureFlag 策略匹配成功
   • 新系统处理耗时 120ms
   • 数据库查询耗时 45ms
```

---

## 8. 灰度发布与回滚

### 8.1 灰度发布策略

```rust
// src/migration/rollback.rs
use tracing::{info, warn};

pub struct GrayReleaseController {
    current_percentage: u8,
}

impl GrayReleaseController {
    pub fn new() -> Self {
        Self {
            current_percentage: 0,
        }
    }

    /// 逐步增加新系统流量
    pub fn increase_traffic(&mut self, increment: u8) -> u8 {
        self.current_percentage = (self.current_percentage + increment).min(100);
        info!("📈 Gray Release: New system traffic increased to {}%", self.current_percentage);
        self.current_percentage
    }

    /// 回滚到旧系统
    pub fn rollback(&mut self) {
        warn!("🔙 Rollback: Routing 100% traffic back to legacy system");
        self.current_percentage = 0;
    }

    /// 获取当前流量百分比
    pub fn get_percentage(&self) -> u8 {
        self.current_percentage
    }
}
```

### 8.2 灰度发布流程

```text
┌────────────────────────────────────────────────────────────┐
│              灰度发布流程 (金丝雀部署)                      │
├────────────────────────────────────────────────────────────┤
│                                                            │
│  Day 1: 1% 流量到新系统                                    │
│    • 监控错误率、延迟、吞吐量                              │
│    • 如果指标正常,24小时后继续                             │
│                                                            │
│  Day 2: 5% 流量                                            │
│    • 继续监控                                              │
│    • 收集用户反馈                                          │
│                                                            │
│  Day 3: 10% 流量                                           │
│    • 监控数据库性能                                        │
│    • 验证数据一致性                                        │
│                                                            │
│  Day 4: 25% 流量                                           │
│    • 负载测试                                              │
│    • 监控资源使用                                          │
│                                                            │
│  Day 5: 50% 流量                                           │
│    • 关键指标对比 (新 vs 旧)                               │
│    • 性能回归测试                                          │
│                                                            │
│  Day 6: 100% 流量 ✅                                        │
│    • 完全迁移到新系统                                      │
│    • 保留旧系统1周以备回滚                                 │
│                                                            │
│  ⚠️ 任何阶段出现问题:                                       │
│    • 立即回滚到旧系统 (设置流量百分比为 0)                 │
│    • 分析问题,修复后重新开始灰度                           │
│                                                            │
└────────────────────────────────────────────────────────────┘
```

---

## 9. 部署与监控

### 9.1 Docker Compose 部署

```yaml
# docker-compose.yml
version: '3.8'

services:
  # Strangler Facade (路由层)
  strangler-facade:
    build:
      context: .
      dockerfile: Dockerfile
    environment:
      - LEGACY_BASE_URL=http://legacy-system:8080
      - NEW_SYSTEM_DB=postgres://postgres:password@new-db:5432/new_system
      - OTLP_ENDPOINT=http://jaeger:4317
    ports:
      - "3000:3000"
    depends_on:
      - legacy-system
      - new-db
      - jaeger

  # 新系统数据库 (PostgreSQL)
  new-db:
    image: postgres:16
    environment:
      - POSTGRES_USER=postgres
      - POSTGRES_PASSWORD=password
      - POSTGRES_DB=new_system
    ports:
      - "5432:5432"

  # 旧系统 (模拟)
  legacy-system:
    image: legacy-app:latest
    environment:
      - DATABASE_URL=mysql://root:password@legacy-db:3306/legacy_db
    ports:
      - "8080:8080"
    depends_on:
      - legacy-db

  # 旧系统数据库 (MySQL)
  legacy-db:
    image: mysql:8
    environment:
      - MYSQL_ROOT_PASSWORD=password
      - MYSQL_DATABASE=legacy_db
    ports:
      - "3306:3306"

  # Jaeger (OTLP 追踪)
  jaeger:
    image: jaegertracing/all-in-one:1.60
    environment:
      - COLLECTOR_OTLP_ENABLED=true
    ports:
      - "16686:16686"  # Jaeger UI
      - "4317:4317"    # OTLP gRPC
```

### 9.2 监控指标

```rust
// src/telemetry/metrics.rs
use metrics::{counter, histogram};

/// 记录路由决策
pub fn record_routing_decision(target: &str, path: &str) {
    counter!("strangler.routing.decisions", "target" => target.to_string(), "path" => path.to_string()).increment(1);
}

/// 记录迁移进度
pub fn record_migration_progress(feature: &str, percentage: u8) {
    metrics::gauge!("strangler.migration.progress", "feature" => feature.to_string()).set(percentage as f64);
}

/// 记录系统响应时间对比
pub fn record_system_latency(system: &str, duration_ms: f64) {
    histogram!("strangler.latency.ms", "system" => system.to_string()).record(duration_ms);
}
```

---

## 10. 最佳实践与陷阱

### 10.1 最佳实践

```rust
/// ✅ DO: Strangler Fig 最佳实践

// 1. 增量迁移,而非一次性重写
// ✅ 正确: 每2周迁移一个微服务
pub struct IncrementalMigration {
    week_1_2: "User Service",
    week_3_4: "Product Service",
    week_5_6: "Order Service",
}

// ❌ 错误: 6个月后一次性上线
pub struct BigBangRewrite {
    month_6: "All services at once", // 💥 灾难性风险
}


// 2. 始终保持回滚能力
// ✅ 正确: 特性标志控制路由
pub async fn route_with_rollback_capability(&self, request: Request) -> Response {
    if self.feature_flags.is_enabled("new_user_service") {
        self.route_to_new_system(request).await
    } else {
        self.route_to_legacy_system(request).await // 可随时切换
    }
}


// 3. 双写策略保证数据一致性
// ✅ 正确: 同时写入新旧系统
pub async fn create_user_with_dual_write(&self, user: User) -> Result<()> {
    // 主写: 新系统
    self.new_db.insert_user(&user).await?;

    // 副写: 旧系统 (失败不阻塞)
    if let Err(e) = self.legacy_db.insert_user(&user).await {
        warn!("Legacy write failed: {:?}, will sync later", e);
    }

    Ok(())
}


// 4. 完整的监控与告警
// ✅ 正确: 对比新旧系统指标
pub async fn compare_system_metrics(&self) {
    let new_latency = self.metrics.get_avg_latency("new_system");
    let legacy_latency = self.metrics.get_avg_latency("legacy_system");

    if new_latency > legacy_latency * 1.5 {
        alert!("New system latency 50% worse than legacy!");
        self.consider_rollback();
    }
}


// 5. 灰度发布,逐步放量
// ✅ 正确: 1% → 5% → 10% → 50% → 100%
pub struct GrayReleaseSchedule {
    day_1: "1% traffic",
    day_2: "5% traffic",
    day_3: "10% traffic",
    day_4: "50% traffic",
    day_5: "100% traffic (if all metrics are healthy)",
}


// 6. 先迁移读操作,再迁移写操作
// ✅ 正确: 降低风险
pub enum MigrationOrder {
    Phase1: "Migrate read-only endpoints (GET /users/:id)",
    Phase2: "Migrate write endpoints (POST /users)",
    Phase3: "Migrate complex workflows (transactions)",
}


// 7. 定期数据一致性验证
// ✅ 正确: 每天对比新旧数据库
pub async fn verify_data_consistency(&self) -> Result<()> {
    let new_user_count = self.new_db.count_users().await?;
    let legacy_user_count = self.legacy_db.count_users().await?;

    let diff = (new_user_count as f64 - legacy_user_count as f64).abs();
    let threshold = legacy_user_count as f64 * 0.01; // 允许1%误差

    if diff > threshold {
        alert!("Data inconsistency detected: {} users difference", diff);
    }

    Ok(())
}
```

### 10.2 常见陷阱

```rust
/// ❌ ANTI-PATTERNS: 常见错误

// ❌ 陷阱 1: 忘记迁移历史数据
// 问题: 新系统上线后,历史订单无法查询
// ✅ 解决: 在迁移前批量导入历史数据,或实现混合查询
pub async fn query_order_with_fallback(&self, order_id: &str) -> Result<Order> {
    // 先查新系统
    if let Some(order) = self.new_db.get_order(order_id).await? {
        return Ok(order);
    }

    // 回退到旧系统查询历史订单
    self.legacy_db.get_order(order_id).await
}


// ❌ 陷阱 2: 双写顺序错误
// 问题: 先写旧系统,再写新系统,如果新系统失败,数据不一致
// ✅ 解决: 先写新系统 (主),再写旧系统 (副)
pub async fn create_user(&self, user: User) -> Result<Uuid> {
    // 1. 主写: 新系统 (失败则中止)
    let user_id = self.new_db.insert_user(&user).await?;

    // 2. 副写: 旧系统 (失败不阻塞,异步补偿)
    tokio::spawn({
        let legacy_db = self.legacy_db.clone();
        let user = user.clone();
        async move {
            if let Err(e) = legacy_db.insert_user(&user).await {
                warn!("Legacy write failed, queuing for retry: {:?}", e);
            }
        }
    });

    Ok(user_id)
}


// ❌ 陷阱 3: 没有回滚计划
// 问题: 新系统上线后出现严重 bug,无法快速回滚
// ✅ 解决: 始终保留特性标志,可一键切换回旧系统
pub struct EmergencyRollback {
    /// 特性标志: 一键关闭新系统路由
    feature_flag: "new_system_enabled",
    
    /// 回滚 SOP (标准操作流程)
    rollback_steps: vec![
        "1. 关闭特性标志: new_system_enabled = false",
        "2. 验证所有流量路由回旧系统",
        "3. 检查旧系统健康状态",
        "4. 通知团队回滚完成",
    ],
}


// ❌ 陷阱 4: 新旧系统 API 不兼容
// 问题: 新系统返回的 JSON 格式与旧系统不同,客户端报错
// ✅ 解决: Strangler Facade 负责协议适配
pub async fn adapt_response(&self, new_response: NewUserResponse) -> LegacyUserResponse {
    LegacyUserResponse {
        user_id: new_response.id.to_string().parse().unwrap(),
        username: new_response.name,
        email_address: new_response.email,
        // 新系统返回 ISO 8601,转换为旧系统的时间戳格式
        created_at: new_response.created_at.timestamp(),
    }
}


// ❌ 陷阱 5: 忽略数据库事务边界
// 问题: 旧系统是单体应用,事务跨多个表;新系统拆分为微服务,无法保证事务
// ✅ 解决: 使用 Saga 模式或两阶段提交
pub async fn create_order_with_saga(&self, order: Order) -> Result<OrderId> {
    // Saga 协调器
    let saga = SagaOrchestrator::new();

    // Step 1: 创建订单
    let order_id = saga.execute(|| self.new_db.create_order(&order)).await?;

    // Step 2: 扣减库存
    saga.execute(|| self.inventory_service.reduce_stock(&order.items)).await?;

    // Step 3: 扣款
    saga.execute(|| self.payment_service.charge(&order.total)).await?;

    // 如果任何步骤失败,自动执行补偿事务
    Ok(order_id)
}


// ❌ 陷阱 6: 过早下线旧系统
// 问题: 迁移后1周就下线旧系统,后来发现新系统有 bug,无法回滚
// ✅ 解决: 保留旧系统至少1个月,并持续监控
pub struct SystemRetentionPolicy {
    new_system_launch_date: "2025-10-01",
    legacy_system_retention_period: "至少 30 天",
    final_decommission_date: "2025-11-01 (如果无问题)",
}
```

### 10.3 迁移检查清单

```text
┌────────────────────────────────────────────────────────────┐
│         Strangler Fig 迁移检查清单                         │
├────────────────────────────────────────────────────────────┤
│                                                            │
│  ✅ 迁移前准备                                             │
│     □ 完整的迁移计划和时间表                               │
│     □ 新系统功能与旧系统对比验证                           │
│     □ 数据模型映射文档                                     │
│     □ 回滚计划和应急预案                                   │
│     □ 监控和告警配置                                       │
│                                                            │
│  ✅ 迁移中监控                                             │
│     □ 新旧系统响应时间对比                                 │
│     □ 错误率监控 (新系统不应高于旧系统)                    │
│     □ 数据一致性验证 (每日对比)                            │
│     □ 用户反馈收集                                         │
│     □ 资源使用监控 (CPU, 内存, 数据库连接)                 │
│                                                            │
│  ✅ 迁移后验证                                             │
│     □ 所有功能测试通过                                     │
│     □ 性能基准测试 (不低于旧系统)                          │
│     □ 历史数据迁移完成                                     │
│     □ 双写停止,切换到单写新系统                            │
│     □ 旧系统代码归档,保留1个月                             │
│                                                            │
└────────────────────────────────────────────────────────────┘
```

---

## 📚 参考资料

### 国际标准与最佳实践

1. **Martin Fowler - StranglerFigApplication**
   - <https://martinfowler.com/bliki/StranglerFigApplication.html>
   - Strangler Fig 模式的原始定义

2. **AWS - Strangler Fig Pattern for Modernization**
   - <https://docs.aws.amazon.com/prescriptive-guidance/latest/migration-strangler-fig/welcome.html>
   - AWS 迁移指南

3. **Microsoft Azure - Strangler pattern**
   - <https://learn.microsoft.com/en-us/azure/architecture/patterns/strangler-fig>
   - Azure 架构模式文档

4. **Sam Newman - Monolith to Microservices**
   - Chapter: Decomposition Patterns
   - 详细的遗留系统拆分策略

### 实战案例

1. **Shopify - Deconstructing the Monolith**
   - Shopify 如何用 Strangler Fig 拆分单体应用
   - <https://shopify.engineering/deconstructing-monolith-designing-software-maximizes-developer-productivity>

2. **SoundCloud - Building Products at SoundCloud**
   - SoundCloud 的微服务迁移之旅
   - <https://developers.soundcloud.com/blog/building-products-at-soundcloud-part-2-breaking-the-monolith>

---

## ✅ 总结

### Strangler Fig 模式核心价值

1. **风险可控**: 小步迁移,随时回滚
2. **业务不中断**: 持续交付新功能
3. **团队学习**: 逐步掌握新技术栈
4. **成本可控**: 避免"大爆炸"式重写的巨额投入

### 关键成功因素

1. **清晰的迁移路线图**: 分阶段,可衡量
2. **完善的监控体系**: 新旧系统对比
3. **灰度发布机制**: 逐步放量,风险可控
4. **回滚能力**: 特性标志,一键切换

### 适用场景

✅ **适合使用 Strangler Fig**:

- 遗留单体应用现代化
- 技术栈升级 (Java → Rust)
- 数据库迁移
- 长期维护的系统

❌ **不适合使用 Strangler Fig**:

- 全新业务系统 (直接用新技术)
- 小型应用 (< 1万行代码)
- 即将下线的系统

---

**文档状态**: ✅ 生产就绪  
**最后更新**: 2025-10-11  
**维护者**: OTLP Rust Team
