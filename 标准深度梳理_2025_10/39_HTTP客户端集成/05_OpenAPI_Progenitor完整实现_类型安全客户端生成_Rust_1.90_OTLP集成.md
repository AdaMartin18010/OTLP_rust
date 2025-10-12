# OpenAPI 客户端生成 - Progenitor 完整实现指南

## 目录

- [OpenAPI 客户端生成 - Progenitor 完整实现指南](#openapi-客户端生成---progenitor-完整实现指南)
  - [目录](#目录)
  - [1. OpenAPI 与 Progenitor 概述](#1-openapi-与-progenitor-概述)
    - [1.1 OpenAPI 规范](#11-openapi-规范)
    - [1.2 Progenitor 特性](#12-progenitor-特性)
  - [2. 核心架构](#2-核心架构)
  - [3. 项目设置](#3-项目设置)
    - [3.1 Cargo.toml](#31-cargotoml)
  - [4. OpenAPI Schema 定义](#4-openapi-schema-定义)
    - [4.1 完整的 OpenAPI 3.1 Schema](#41-完整的-openapi-31-schema)
  - [5. 客户端代码生成](#5-客户端代码生成)
    - [5.1 build.rs 自动生成](#51-buildrs-自动生成)
    - [5.2 生成的客户端结构](#52-生成的客户端结构)
  - [6. 生成的客户端使用](#6-生成的客户端使用)
    - [6.1 基础使用](#61-基础使用)
  - [7. 高级功能](#7-高级功能)
    - [7.1 自定义 Reqwest 客户端](#71-自定义-reqwest-客户端)
    - [7.2 批量操作封装](#72-批量操作封装)
    - [7.3 分页遍历](#73-分页遍历)
  - [8. 错误处理](#8-错误处理)
    - [8.1 自定义错误类型](#81-自定义错误类型)
    - [7.2 重试机制](#72-重试机制)
  - [9. OTLP 可观测性集成](#9-otlp-可观测性集成)
    - [9.1 追踪初始化](#91-追踪初始化)
    - [9.2 带追踪的客户端](#92-带追踪的客户端)
  - [10. 测试策略](#10-测试策略)
    - [10.1 Mock Server 测试](#101-mock-server-测试)
  - [11. 生产实践](#11-生产实践)
    - [11.1 完整的客户端封装](#111-完整的客户端封装)
    - [11.2 配置管理](#112-配置管理)
  - [12. 国际标准对齐](#12-国际标准对齐)
    - [12.1 OpenAPI 3.1 规范](#121-openapi-31-规范)
    - [12.2 REST API 最佳实践](#122-rest-api-最佳实践)
    - [12.3 OpenTelemetry 语义约定](#123-opentelemetry-语义约定)
  - [总结](#总结)

---

## 1. OpenAPI 与 Progenitor 概述

### 1.1 OpenAPI 规范

**OpenAPI 3.1** 是一种标准化的 API 描述格式，提供：

- **类型安全**: 强类型 Schema 定义
- **文档生成**: 自动生成 API 文档
- **客户端生成**: 自动生成多语言客户端
- **验证**: 请求/响应验证

### 1.2 Progenitor 特性

**Progenitor** 是 Oxide Computer 开发的 Rust OpenAPI 客户端生成器：

- ✅ **编译期类型安全**: 所有 API 调用在编译时验证
- ✅ **Derive 宏驱动**: 自动生成 Serde 序列化代码
- ✅ **Reqwest 集成**: 基于 Reqwest 的异步 HTTP 客户端
- ✅ **枚举与 Tagged Union**: 完整支持 OpenAPI `oneOf`/`anyOf`
- ✅ **分页支持**: 内置 Cursor-based 和 Offset-based 分页
- ✅ **Builder 模式**: 流畅的 API 调用接口

---

## 2. 核心架构

```text
┌─────────────────────────────────────────────────────────────┐
│                      OpenAPI Schema                         │
│                    (openapi.yaml/json)                      │
└────────────────────────┬────────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────────┐
│                  Progenitor 代码生成器                       │
│  cargo install progenitor / build.rs                        │
└────────────────────────┬────────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────────┐
│                   生成的 Rust 客户端                         │
│  • 类型定义 (struct/enum)                                    │
│  • API 方法 (async fn)                                      │
│  • Builder 模式                                             │
└────────────────────────┬────────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────────┐
│                    应用层调用                                │
│  • 类型安全的 API 调用                                       │
│  • 编译期错误检测                                            │
│  • OTLP 追踪集成                                            │
└─────────────────────────────────────────────────────────────┘
```

---

## 3. 项目设置

### 3.1 Cargo.toml

```toml
[package]
name = "openapi-client-progenitor"
version = "0.1.0"
edition = "2021"

[dependencies]
# HTTP 客户端
reqwest = { version = "0.12", features = ["json", "rustls-tls"] }
tokio = { version = "1", features = ["full"] }

# 序列化
serde = { version = "1", features = ["derive"] }
serde_json = "1"

# OpenAPI 客户端生成
progenitor = "0.8"

# 错误处理
thiserror = "1"
anyhow = "1"

# 日志与追踪
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.25"

# OpenTelemetry
opentelemetry = "0.25"
opentelemetry-otlp = { version = "0.25", features = ["grpc-tonic"] }
opentelemetry_sdk = { version = "0.25", features = ["rt-tokio"] }

# 日期时间
chrono = { version = "0.4", features = ["serde"] }

[build-dependencies]
progenitor = "0.8"

[dev-dependencies]
wiremock = "0.6"
```

---

## 4. OpenAPI Schema 定义

### 4.1 完整的 OpenAPI 3.1 Schema

```yaml
# openapi.yaml
openapi: 3.1.0
info:
  title: Example API
  version: 1.0.0
  description: 示例 RESTful API

servers:
  - url: https://api.example.com/v1
    description: 生产环境

paths:
  /users:
    get:
      operationId: listUsers
      summary: 获取用户列表
      parameters:
        - name: page
          in: query
          schema:
            type: integer
            default: 1
        - name: per_page
          in: query
          schema:
            type: integer
            default: 20
      responses:
        '200':
          description: 成功
          content:
            application/json:
              schema:
                $ref: '#/components/schemas/UserListResponse'
    
    post:
      operationId: createUser
      summary: 创建用户
      requestBody:
        required: true
        content:
          application/json:
            schema:
              $ref: '#/components/schemas/CreateUserRequest'
      responses:
        '201':
          description: 创建成功
          content:
            application/json:
              schema:
                $ref: '#/components/schemas/User'

  /users/{user_id}:
    get:
      operationId: getUser
      summary: 获取用户详情
      parameters:
        - name: user_id
          in: path
          required: true
          schema:
            type: string
            format: uuid
      responses:
        '200':
          description: 成功
          content:
            application/json:
              schema:
                $ref: '#/components/schemas/User'
        '404':
          description: 用户不存在
          content:
            application/json:
              schema:
                $ref: '#/components/schemas/ErrorResponse'
    
    put:
      operationId: updateUser
      summary: 更新用户
      parameters:
        - name: user_id
          in: path
          required: true
          schema:
            type: string
            format: uuid
      requestBody:
        required: true
        content:
          application/json:
            schema:
              $ref: '#/components/schemas/UpdateUserRequest'
      responses:
        '200':
          description: 更新成功
          content:
            application/json:
              schema:
                $ref: '#/components/schemas/User'
    
    delete:
      operationId: deleteUser
      summary: 删除用户
      parameters:
        - name: user_id
          in: path
          required: true
          schema:
            type: string
            format: uuid
      responses:
        '204':
          description: 删除成功

components:
  schemas:
    User:
      type: object
      required:
        - id
        - email
        - name
        - role
        - created_at
      properties:
        id:
          type: string
          format: uuid
        email:
          type: string
          format: email
        name:
          type: string
        role:
          $ref: '#/components/schemas/UserRole'
        created_at:
          type: string
          format: date-time
        metadata:
          type: object
          additionalProperties:
            type: string

    UserRole:
      type: string
      enum:
        - admin
        - user
        - guest

    CreateUserRequest:
      type: object
      required:
        - email
        - name
        - role
      properties:
        email:
          type: string
          format: email
        name:
          type: string
        role:
          $ref: '#/components/schemas/UserRole'

    UpdateUserRequest:
      type: object
      properties:
        name:
          type: string
        role:
          $ref: '#/components/schemas/UserRole'

    UserListResponse:
      type: object
      required:
        - data
        - pagination
      properties:
        data:
          type: array
          items:
            $ref: '#/components/schemas/User'
        pagination:
          $ref: '#/components/schemas/Pagination'

    Pagination:
      type: object
      required:
        - page
        - per_page
        - total
      properties:
        page:
          type: integer
        per_page:
          type: integer
        total:
          type: integer

    ErrorResponse:
      type: object
      required:
        - error
        - message
      properties:
        error:
          type: string
        message:
          type: string
        details:
          type: object
          additionalProperties: true

  securitySchemes:
    BearerAuth:
      type: http
      scheme: bearer
      bearerFormat: JWT

security:
  - BearerAuth: []
```

---

## 5. 客户端代码生成

### 5.1 build.rs 自动生成

```rust
// build.rs
use progenitor::GenerationSettings;
use std::path::Path;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 读取 OpenAPI Schema
    let spec_path = Path::new("openapi.yaml");
    let spec_content = std::fs::read_to_string(spec_path)?;
    
    // 配置生成设置
    let settings = GenerationSettings::default()
        .with_tag("rust-client")
        .with_derive("serde::Serialize")
        .with_derive("serde::Deserialize");
    
    // 生成客户端代码
    let generated_code = progenitor::Generator::new(&settings)
        .generate_text(&spec_content)?;
    
    // 写入到 src/generated.rs
    let output_path = Path::new("src/generated.rs");
    std::fs::write(output_path, generated_code)?;
    
    println!("cargo:rerun-if-changed=openapi.yaml");
    
    Ok(())
}
```

### 5.2 生成的客户端结构

```rust
// src/generated.rs (Progenitor 自动生成)

use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};

/// 用户实体
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct User {
    pub id: uuid::Uuid,
    pub email: String,
    pub name: String,
    pub role: UserRole,
    pub created_at: DateTime<Utc>,
    #[serde(default)]
    pub metadata: std::collections::HashMap<String, String>,
}

/// 用户角色枚举
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum UserRole {
    Admin,
    User,
    Guest,
}

/// 创建用户请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CreateUserRequest {
    pub email: String,
    pub name: String,
    pub role: UserRole,
}

/// 更新用户请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UpdateUserRequest {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub role: Option<UserRole>,
}

/// 用户列表响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UserListResponse {
    pub data: Vec<User>,
    pub pagination: Pagination,
}

/// 分页信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Pagination {
    pub page: i32,
    pub per_page: i32,
    pub total: i32,
}

/// 错误响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorResponse {
    pub error: String,
    pub message: String,
    #[serde(default)]
    pub details: serde_json::Value,
}

/// API 客户端
pub struct Client {
    client: reqwest::Client,
    base_url: String,
    auth_token: Option<String>,
}

impl Client {
    /// 创建新客户端
    pub fn new(base_url: impl Into<String>) -> Self {
        Self {
            client: reqwest::Client::new(),
            base_url: base_url.into(),
            auth_token: None,
        }
    }

    /// 设置认证 Token
    pub fn with_auth_token(mut self, token: impl Into<String>) -> Self {
        self.auth_token = Some(token.into());
        self
    }

    /// 获取用户列表
    pub async fn list_users(
        &self,
        page: Option<i32>,
        per_page: Option<i32>,
    ) -> Result<UserListResponse, reqwest::Error> {
        let mut request = self.client
            .get(format!("{}/users", self.base_url))
            .query(&[
                ("page", page.unwrap_or(1).to_string()),
                ("per_page", per_page.unwrap_or(20).to_string()),
            ]);

        if let Some(token) = &self.auth_token {
            request = request.bearer_auth(token);
        }

        request.send().await?.json().await
    }

    /// 创建用户
    pub async fn create_user(
        &self,
        req: &CreateUserRequest,
    ) -> Result<User, reqwest::Error> {
        let mut request = self.client
            .post(format!("{}/users", self.base_url))
            .json(req);

        if let Some(token) = &self.auth_token {
            request = request.bearer_auth(token);
        }

        request.send().await?.json().await
    }

    /// 获取用户详情
    pub async fn get_user(
        &self,
        user_id: uuid::Uuid,
    ) -> Result<User, reqwest::Error> {
        let mut request = self.client
            .get(format!("{}/users/{}", self.base_url, user_id));

        if let Some(token) = &self.auth_token {
            request = request.bearer_auth(token);
        }

        request.send().await?.json().await
    }

    /// 更新用户
    pub async fn update_user(
        &self,
        user_id: uuid::Uuid,
        req: &UpdateUserRequest,
    ) -> Result<User, reqwest::Error> {
        let mut request = self.client
            .put(format!("{}/users/{}", self.base_url, user_id))
            .json(req);

        if let Some(token) = &self.auth_token {
            request = request.bearer_auth(token);
        }

        request.send().await?.json().await
    }

    /// 删除用户
    pub async fn delete_user(
        &self,
        user_id: uuid::Uuid,
    ) -> Result<(), reqwest::Error> {
        let mut request = self.client
            .delete(format!("{}/users/{}", self.base_url, user_id));

        if let Some(token) = &self.auth_token {
            request = request.bearer_auth(token);
        }

        let response = request.send().await?;
        response.error_for_status()?;
        Ok(())
    }
}
```

---

## 6. 生成的客户端使用

### 6.1 基础使用

```rust
use crate::generated::{Client, CreateUserRequest, UserRole};

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 创建客户端
    let client = Client::new("https://api.example.com/v1")
        .with_auth_token("your-jwt-token");

    // 1. 获取用户列表
    let users = client.list_users(Some(1), Some(10)).await?;
    println!("Total users: {}", users.pagination.total);
    for user in users.data {
        println!("User: {} ({})", user.name, user.email);
    }

    // 2. 创建用户
    let new_user = client.create_user(&CreateUserRequest {
        email: "alice@example.com".to_string(),
        name: "Alice".to_string(),
        role: UserRole::User,
    }).await?;
    println!("Created user: {:?}", new_user);

    // 3. 获取用户详情
    let user = client.get_user(new_user.id).await?;
    println!("User details: {:?}", user);

    Ok(())
}
```

---

## 7. 高级功能

### 7.1 自定义 Reqwest 客户端

```rust
use reqwest::ClientBuilder;
use std::time::Duration;

/// 创建优化的客户端
pub fn create_optimized_client(base_url: &str, token: &str) -> Client {
    let http_client = ClientBuilder::new()
        .timeout(Duration::from_secs(30))
        .connect_timeout(Duration::from_secs(10))
        .pool_max_idle_per_host(10)
        .http2_adaptive_window(true)
        .build()
        .expect("Failed to build HTTP client");

    Client {
        client: http_client,
        base_url: base_url.to_string(),
        auth_token: Some(token.to_string()),
    }
}
```

### 7.2 批量操作封装

```rust
use futures::stream::{self, StreamExt};

/// 批量创建用户
pub async fn batch_create_users(
    client: &Client,
    requests: Vec<CreateUserRequest>,
    concurrency: usize,
) -> Vec<Result<User, reqwest::Error>> {
    stream::iter(requests)
        .map(|req| client.create_user(&req))
        .buffer_unordered(concurrency)
        .collect()
        .await
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let client = create_optimized_client("https://api.example.com/v1", "token");

    let requests = vec![
        CreateUserRequest {
            email: "user1@example.com".to_string(),
            name: "User 1".to_string(),
            role: UserRole::User,
        },
        CreateUserRequest {
            email: "user2@example.com".to_string(),
            name: "User 2".to_string(),
            role: UserRole::Admin,
        },
    ];

    let results = batch_create_users(&client, requests, 5).await;
    for result in results {
        match result {
            Ok(user) => println!("Created: {}", user.name),
            Err(e) => eprintln!("Error: {}", e),
        }
    }

    Ok(())
}
```

### 7.3 分页遍历

```rust
/// 遍历所有用户（自动处理分页）
pub async fn iterate_all_users(client: &Client) -> anyhow::Result<Vec<User>> {
    let mut all_users = Vec::new();
    let mut page = 1;
    let per_page = 100;

    loop {
        let response = client.list_users(Some(page), Some(per_page)).await?;
        let total_pages = (response.pagination.total + per_page - 1) / per_page;

        all_users.extend(response.data);

        if page >= total_pages {
            break;
        }
        page += 1;
    }

    Ok(all_users)
}
```

---

## 8. 错误处理

### 8.1 自定义错误类型

```rust
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ApiError {
    #[error("HTTP request failed: {0}")]
    RequestFailed(#[from] reqwest::Error),

    #[error("API error: {code} - {message}")]
    ApiError {
        code: String,
        message: String,
        details: serde_json::Value,
    },

    #[error("Authentication failed")]
    AuthenticationFailed,

    #[error("Resource not found: {0}")]
    NotFound(String),

    #[error("Rate limit exceeded")]
    RateLimitExceeded,
}

/// 增强的客户端封装
pub struct SafeClient {
    inner: Client,
}

impl SafeClient {
    pub fn new(client: Client) -> Self {
        Self { inner: client }
    }

    pub async fn get_user(&self, user_id: uuid::Uuid) -> Result<User, ApiError> {
        let response = self.inner.client
            .get(format!("{}/users/{}", self.inner.base_url, user_id))
            .bearer_auth(self.inner.auth_token.as_ref().ok_or(ApiError::AuthenticationFailed)?)
            .send()
            .await?;

        match response.status() {
            reqwest::StatusCode::OK => {
                Ok(response.json().await?)
            }
            reqwest::StatusCode::NOT_FOUND => {
                Err(ApiError::NotFound(format!("User {}", user_id)))
            }
            reqwest::StatusCode::TOO_MANY_REQUESTS => {
                Err(ApiError::RateLimitExceeded)
            }
            _ => {
                let error: ErrorResponse = response.json().await?;
                Err(ApiError::ApiError {
                    code: error.error,
                    message: error.message,
                    details: error.details,
                })
            }
        }
    }
}
```

### 7.2 重试机制

```rust
use tokio::time::{sleep, Duration};

/// 带重试的 API 调用
pub async fn retry_api_call<F, Fut, T>(
    f: F,
    max_retries: u32,
) -> Result<T, ApiError>
where
    F: Fn() -> Fut,
    Fut: std::future::Future<Output = Result<T, ApiError>>,
{
    let mut retries = 0;
    
    loop {
        match f().await {
            Ok(result) => return Ok(result),
            Err(e) => {
                if retries >= max_retries {
                    return Err(e);
                }
                
                if matches!(e, ApiError::RateLimitExceeded) {
                    let delay = Duration::from_secs(2u64.pow(retries));
                    tracing::warn!("Rate limited, retrying in {:?}", delay);
                    sleep(delay).await;
                    retries += 1;
                } else {
                    return Err(e);
                }
            }
        }
    }
}

// 使用示例
async fn example_with_retry(client: &SafeClient, user_id: uuid::Uuid) -> Result<User, ApiError> {
    retry_api_call(|| client.get_user(user_id), 3).await
}
```

---

## 9. OTLP 可观测性集成

### 9.1 追踪初始化

```rust
use opentelemetry::{global, trace::{TraceContextExt, Tracer}, KeyValue};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{runtime, trace as sdktrace, Resource};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

pub fn init_telemetry() -> anyhow::Result<()> {
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .with_trace_config(
            sdktrace::Config::default().with_resource(Resource::new(vec![
                KeyValue::new("service.name", "openapi-client"),
                KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
            ]))
        )
        .install_batch(runtime::Tokio)?;

    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new("info"))
        .with(tracing_subscriber::fmt::layer().json())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    Ok(())
}
```

### 9.2 带追踪的客户端

```rust
use opentelemetry::{global, trace::{SpanKind, Tracer, Status}, KeyValue};
use tracing::instrument;

impl SafeClient {
    #[instrument(skip(self), fields(
        http.method = "GET",
        http.url = %format!("{}/users/{}", self.inner.base_url, user_id),
        user.id = %user_id
    ))]
    pub async fn traced_get_user(&self, user_id: uuid::Uuid) -> Result<User, ApiError> {
        let tracer = global::tracer("openapi-client");
        
        let mut span = tracer
            .span_builder(format!("GET /users/{}", user_id))
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("http.method", "GET"),
                KeyValue::new("http.url", format!("{}/users/{}", self.inner.base_url, user_id)),
                KeyValue::new("user.id", user_id.to_string()),
            ])
            .start(&tracer);
        
        let start = std::time::Instant::now();
        
        let result = self.get_user(user_id).await;
        
        let duration = start.elapsed();
        
        match &result {
            Ok(user) => {
                span.set_attribute(KeyValue::new("http.status_code", 200));
                span.set_attribute(KeyValue::new("user.name", user.name.clone()));
                span.set_attribute(KeyValue::new("http.response_time_ms", duration.as_millis() as i64));
            }
            Err(e) => {
                span.set_status(Status::error(e.to_string()));
                span.set_attribute(KeyValue::new("error", true));
                span.set_attribute(KeyValue::new("error.type", format!("{:?}", e)));
            }
        }
        
        span.end();
        
        result
    }
}
```

---

## 10. 测试策略

### 10.1 Mock Server 测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use wiremock::{MockServer, Mock, ResponseTemplate};
    use wiremock::matchers::{method, path};

    #[tokio::test]
    async fn test_get_user() {
        let mock_server = MockServer::start().await;

        let user_id = uuid::Uuid::new_v4();
        let mock_user = User {
            id: user_id,
            email: "test@example.com".to_string(),
            name: "Test User".to_string(),
            role: UserRole::User,
            created_at: chrono::Utc::now(),
            metadata: Default::default(),
        };

        Mock::given(method("GET"))
            .and(path(format!("/users/{}", user_id)))
            .respond_with(ResponseTemplate::new(200).set_body_json(&mock_user))
            .mount(&mock_server)
            .await;

        let client = Client::new(mock_server.uri())
            .with_auth_token("test-token");

        let result = client.get_user(user_id).await.unwrap();

        assert_eq!(result.id, user_id);
        assert_eq!(result.email, "test@example.com");
    }

    #[tokio::test]
    async fn test_create_user() {
        let mock_server = MockServer::start().await;

        let mock_user = User {
            id: uuid::Uuid::new_v4(),
            email: "new@example.com".to_string(),
            name: "New User".to_string(),
            role: UserRole::User,
            created_at: chrono::Utc::now(),
            metadata: Default::default(),
        };

        Mock::given(method("POST"))
            .and(path("/users"))
            .respond_with(ResponseTemplate::new(201).set_body_json(&mock_user))
            .mount(&mock_server)
            .await;

        let client = Client::new(mock_server.uri())
            .with_auth_token("test-token");

        let result = client.create_user(&CreateUserRequest {
            email: "new@example.com".to_string(),
            name: "New User".to_string(),
            role: UserRole::User,
        }).await.unwrap();

        assert_eq!(result.email, "new@example.com");
    }
}
```

---

## 11. 生产实践

### 11.1 完整的客户端封装

```rust
use std::sync::Arc;
use tokio::sync::RwLock;

/// 生产级客户端（支持 Token 刷新）
pub struct ProductionClient {
    client: Client,
    token: Arc<RwLock<String>>,
}

impl ProductionClient {
    pub fn new(base_url: impl Into<String>, token: impl Into<String>) -> Self {
        let token = token.into();
        Self {
            client: Client::new(base_url).with_auth_token(&token),
            token: Arc::new(RwLock::new(token)),
        }
    }

    /// 刷新 Token
    pub async fn refresh_token(&self, new_token: String) {
        let mut token = self.token.write().await;
        *token = new_token;
    }

    /// 带自动重试和追踪的 API 调用
    #[instrument(skip(self))]
    pub async fn get_user_safe(&self, user_id: uuid::Uuid) -> Result<User, ApiError> {
        let safe_client = SafeClient::new(self.client.clone());
        retry_api_call(|| safe_client.traced_get_user(user_id), 3).await
    }
}
```

### 11.2 配置管理

```rust
use serde::Deserialize;

#[derive(Debug, Deserialize)]
pub struct ClientConfig {
    pub base_url: String,
    pub auth_token: String,
    pub timeout_secs: u64,
    pub max_retries: u32,
}

impl ClientConfig {
    pub fn from_env() -> anyhow::Result<Self> {
        Ok(Self {
            base_url: std::env::var("API_BASE_URL")?,
            auth_token: std::env::var("API_AUTH_TOKEN")?,
            timeout_secs: std::env::var("API_TIMEOUT_SECS")
                .unwrap_or_else(|_| "30".to_string())
                .parse()?,
            max_retries: std::env::var("API_MAX_RETRIES")
                .unwrap_or_else(|_| "3".to_string())
                .parse()?,
        })
    }

    pub fn build_client(&self) -> ProductionClient {
        ProductionClient::new(&self.base_url, &self.auth_token)
    }
}
```

---

## 12. 国际标准对齐

### 12.1 OpenAPI 3.1 规范

- ✅ **完整的 Schema 定义**: 所有类型使用 JSON Schema 验证
- ✅ **安全方案**: Bearer Token (RFC 6750), OAuth 2.0 (RFC 6749)
- ✅ **HTTP 语义**: 遵循 RFC 7231 (HTTP/1.1 Semantics)
- ✅ **内容协商**: `application/json` (RFC 8259)

### 12.2 REST API 最佳实践

- ✅ **资源命名**: 使用名词复数形式 (`/users`, `/orders`)
- ✅ **HTTP 方法语义**:
  - `GET`: 幂等只读操作
  - `POST`: 创建资源
  - `PUT`: 完整更新资源（幂等）
  - `PATCH`: 部分更新资源
  - `DELETE`: 删除资源（幂等）
- ✅ **状态码使用**:
  - `200 OK`: 成功
  - `201 Created`: 创建成功
  - `204 No Content`: 删除成功
  - `400 Bad Request`: 客户端错误
  - `401 Unauthorized`: 未认证
  - `403 Forbidden`: 无权限
  - `404 Not Found`: 资源不存在
  - `429 Too Many Requests`: 限流
  - `500 Internal Server Error`: 服务器错误

### 12.3 OpenTelemetry 语义约定

```rust
// HTTP Semantic Conventions (v1.21.0)
span.set_attribute(KeyValue::new("http.method", "GET"));
span.set_attribute(KeyValue::new("http.url", "https://api.example.com/users/123"));
span.set_attribute(KeyValue::new("http.status_code", 200));
span.set_attribute(KeyValue::new("http.response_content_length", 1024));

// Service 标识
span.set_attribute(KeyValue::new("service.name", "openapi-client"));
span.set_attribute(KeyValue::new("service.version", "1.0.0"));
```

---

## 总结

| 特性 | Progenitor | openapi-generator |
|------|-----------|-------------------|
| **编译期类型安全** | ✅ 完整支持 | ⚠️ 部分支持 |
| **Rust 惯用法** | ✅ async/await, Result | ⚠️ 较旧的模式 |
| **生成代码质量** | ✅ 简洁清晰 | ⚠️ 较冗长 |
| **Reqwest 集成** | ✅ 原生支持 | ⚠️ 需手动集成 |
| **分页支持** | ✅ 内置 | ❌ 需手动实现 |
| **社区支持** | ⚠️ 较小 | ✅ 广泛 |

**Progenitor 优势**:

1. **类型安全**: 编译期捕获所有 API 不匹配
2. **简洁代码**: 生成的代码易读易维护
3. **现代 Rust**: 完整的 async/await 支持
4. **生产就绪**: Oxide Computer 内部大规模使用

**适用场景**:

- ✅ 新项目采用 Rust 1.90+ 和 OpenAPI 3.1
- ✅ 需要高类型安全的企业级应用
- ✅ 微服务间的类型安全通信
- ✅ 需要完整 OTLP 可观测性的系统

---

**版权**: MIT License  
**作者**: OTLP Rust 项目组  
**最后更新**: 2025-10-11
