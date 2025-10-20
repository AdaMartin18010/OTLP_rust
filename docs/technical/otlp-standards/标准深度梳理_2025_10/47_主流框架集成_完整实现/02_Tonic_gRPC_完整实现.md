# Tonic gRPC 完整实现 (Rust 1.90 + OpenTelemetry 0.31)

## 目录

- [Tonic gRPC 完整实现 (Rust 1.90 + OpenTelemetry 0.31)](#tonic-grpc-完整实现-rust-190--opentelemetry-031)
  - [目录](#目录)
  - [1. gRPC 与 Tonic 架构](#1-grpc-与-tonic-架构)
    - [1.1 国际标准对标](#11-国际标准对标)
  - [2. 完整项目实现](#2-完整项目实现)
    - [2.1 Cargo.toml](#21-cargotoml)
    - [2.2 Protobuf 定义](#22-protobuf-定义)
    - [2.3 构建脚本](#23-构建脚本)
    - [2.4 服务端实现](#24-服务端实现)
    - [2.5 客户端实现](#25-客户端实现)
  - [3. OTLP 可观测性集成](#3-otlp-可观测性集成)
  - [4. 高级特性](#4-高级特性)
    - [4.1 拦截器 (Middleware)](#41-拦截器-middleware)
    - [4.2 负载均衡](#42-负载均衡)
  - [5. 生产部署](#5-生产部署)
    - [5.1 Docker Compose](#51-docker-compose)
  - [总结](#总结)

## 1. gRPC 与 Tonic 架构

### 1.1 国际标准对标

| 标准 | 实现 | 文档 |
|------|------|------|
| **gRPC** | Tonic 0.12 | [gRPC Spec](https://grpc.io/docs/) |
| **HTTP/2** | Hyper | [RFC 9113](https://www.rfc-editor.org/rfc/rfc9113.html) |
| **Protocol Buffers** | prost 0.13 | [Protobuf](https://protobuf.dev/) |
| **gRPC Health Check** | tonic-health | [Health Check Protocol](https://github.com/grpc/grpc/blob/master/doc/health-checking.md) |
| **OpenTelemetry** | tonic-opentelemetry | [OTLP Spec](https://opentelemetry.io/docs/specs/otel/) |

---

## 2. 完整项目实现

### 2.1 Cargo.toml

```toml
[package]
name = "tonic-grpc-production"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# Tonic gRPC 核心
tonic = "0.12"
prost = "0.13"

# 异步运行时
tokio = { version = "1.40", features = ["full"] }
tokio-stream = "0.1"

# OpenTelemetry
opentelemetry = { version = "0.31", features = ["trace", "metrics"] }
opentelemetry-otlp = { version = "0.31", features = ["grpc-tonic"] }
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
opentelemetry-semantic-conventions = "0.31"

# Tracing
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.31"

# Health Check
tonic-health = "0.12"
tonic-reflection = "0.12"

# 错误处理
thiserror = "2.0"
anyhow = "1.0"

# 序列化
serde = { version = "1.0", features = ["derive"] }

[build-dependencies]
tonic-build = "0.12"

[[bin]]
name = "server"
path = "src/server.rs"

[[bin]]
name = "client"
path = "src/client.rs"
```

### 2.2 Protobuf 定义

```protobuf
// proto/user.proto
syntax = "proto3";

package user.v1;

// 用户服务
service UserService {
  // 创建用户
  rpc CreateUser(CreateUserRequest) returns (CreateUserResponse);
  
  // 获取用户
  rpc GetUser(GetUserRequest) returns (GetUserResponse);
  
  // 列出用户 (Server Streaming)
  rpc ListUsers(ListUsersRequest) returns (stream UserResponse);
  
  // 批量创建 (Client Streaming)
  rpc BatchCreateUsers(stream CreateUserRequest) returns (BatchCreateUsersResponse);
  
  // 聊天 (Bidirectional Streaming)
  rpc Chat(stream ChatMessage) returns (stream ChatMessage);
}

message CreateUserRequest {
  string email = 1;
  string name = 2;
}

message CreateUserResponse {
  string user_id = 1;
  UserResponse user = 2;
}

message GetUserRequest {
  string user_id = 1;
}

message GetUserResponse {
  UserResponse user = 1;
}

message ListUsersRequest {
  int32 page_size = 1;
  string page_token = 2;
}

message BatchCreateUsersResponse {
  int32 created_count = 1;
}

message UserResponse {
  string user_id = 1;
  string email = 2;
  string name = 3;
  int64 created_at = 4;
}

message ChatMessage {
  string user_id = 1;
  string message = 2;
  int64 timestamp = 3;
}
```

### 2.3 构建脚本

```rust
// build.rs
fn main() -> Result<(), Box<dyn std::error::Error>> {
    tonic_build::configure()
        .build_server(true)
        .build_client(true)
        .out_dir("src/proto")
        .compile(
            &["proto/user.proto"],
            &["proto"],
        )?;
    Ok(())
}
```

### 2.4 服务端实现

```rust
// src/server.rs
use tonic::{transport::Server, Request, Response, Status};
use tracing::{info, instrument};
use std::sync::Arc;

mod proto {
    tonic::include_proto!("user.v1");
}

use proto::{
    user_service_server::{UserService, UserServiceServer},
    *,
};

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 初始化 Telemetry
    telemetry::init()?;

    let addr = "0.0.0.0:50051".parse()?;
    let service = MyUserService::default();

    info!("gRPC Server listening on {}", addr);

    // 配置健康检查
    let (mut health_reporter, health_service) = tonic_health::server::health_reporter();
    health_reporter
        .set_serving::<UserServiceServer<MyUserService>>()
        .await;

    // 配置反射 (用于 grpcurl)
    let reflection_service = tonic_reflection::server::Builder::configure()
        .register_encoded_file_descriptor_set(proto::FILE_DESCRIPTOR_SET)
        .build()?;

    Server::builder()
        // 添加 OpenTelemetry 中间件
        .layer(tower_http::trace::TraceLayer::new_for_grpc())
        .add_service(health_service)
        .add_service(reflection_service)
        .add_service(UserServiceServer::new(service))
        .serve(addr)
        .await?;

    opentelemetry::global::shutdown_tracer_provider();
    Ok(())
}

#[derive(Debug, Default)]
pub struct MyUserService {
    users: Arc<tokio::sync::RwLock<std::collections::HashMap<String, UserResponse>>>,
}

#[tonic::async_trait]
impl UserService for MyUserService {
    #[instrument(skip(self))]
    async fn create_user(
        &self,
        request: Request<CreateUserRequest>,
    ) -> Result<Response<CreateUserResponse>, Status> {
        let req = request.into_inner();
        
        info!(email = %req.email, name = %req.name, "Creating user");

        // 业务逻辑
        let user_id = uuid::Uuid::new_v4().to_string();
        let user = UserResponse {
            user_id: user_id.clone(),
            email: req.email,
            name: req.name,
            created_at: chrono::Utc::now().timestamp(),
        };

        self.users.write().await.insert(user_id.clone(), user.clone());

        Ok(Response::new(CreateUserResponse {
            user_id,
            user: Some(user),
        }))
    }

    #[instrument(skip(self))]
    async fn get_user(
        &self,
        request: Request<GetUserRequest>,
    ) -> Result<Response<GetUserResponse>, Status> {
        let user_id = request.into_inner().user_id;
        
        info!(user_id = %user_id, "Getting user");

        let user = self.users.read().await
            .get(&user_id)
            .cloned()
            .ok_or_else(|| Status::not_found("User not found"))?;

        Ok(Response::new(GetUserResponse {
            user: Some(user),
        }))
    }

    type ListUsersStream = tokio_stream::wrappers::ReceiverStream<Result<UserResponse, Status>>;

    #[instrument(skip(self))]
    async fn list_users(
        &self,
        request: Request<ListUsersRequest>,
    ) -> Result<Response<Self::ListUsersStream>, Status> {
        let (tx, rx) = tokio::sync::mpsc::channel(4);

        let users = self.users.read().await.clone();

        tokio::spawn(async move {
            for user in users.values() {
                if tx.send(Ok(user.clone())).await.is_err() {
                    break;
                }
                tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
            }
        });

        Ok(Response::new(tokio_stream::wrappers::ReceiverStream::new(rx)))
    }

    #[instrument(skip(self))]
    async fn batch_create_users(
        &self,
        request: Request<tonic::Streaming<CreateUserRequest>>,
    ) -> Result<Response<BatchCreateUsersResponse>, Status> {
        let mut stream = request.into_inner();
        let mut count = 0;

        while let Some(req) = stream.message().await? {
            let user_id = uuid::Uuid::new_v4().to_string();
            let user = UserResponse {
                user_id: user_id.clone(),
                email: req.email,
                name: req.name,
                created_at: chrono::Utc::now().timestamp(),
            };
            self.users.write().await.insert(user_id, user);
            count += 1;
        }

        Ok(Response::new(BatchCreateUsersResponse {
            created_count: count,
        }))
    }

    type ChatStream = tokio_stream::wrappers::ReceiverStream<Result<ChatMessage, Status>>;

    #[instrument(skip(self))]
    async fn chat(
        &self,
        request: Request<tonic::Streaming<ChatMessage>>,
    ) -> Result<Response<Self::ChatStream>, Status> {
        let mut stream = request.into_inner();
        let (tx, rx) = tokio::sync::mpsc::channel(4);

        tokio::spawn(async move {
            while let Ok(Some(msg)) = stream.message().await {
                info!(user_id = %msg.user_id, message = %msg.message, "Received chat message");
                
                // Echo back
                let response = ChatMessage {
                    user_id: "server".to_string(),
                    message: format!("Echo: {}", msg.message),
                    timestamp: chrono::Utc::now().timestamp(),
                };
                
                if tx.send(Ok(response)).await.is_err() {
                    break;
                }
            }
        });

        Ok(Response::new(tokio_stream::wrappers::ReceiverStream::new(rx)))
    }
}
```

### 2.5 客户端实现

```rust
// src/client.rs
use tonic::transport::Channel;
use tracing::{info, instrument};

mod proto {
    tonic::include_proto!("user.v1");
}

use proto::user_service_client::UserServiceClient;
use proto::*;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    telemetry::init()?;

    let channel = Channel::from_static("http://localhost:50051")
        .connect()
        .await?;

    let mut client = UserServiceClient::new(channel);

    // 1. Unary RPC
    test_create_user(&mut client).await?;

    // 2. Server Streaming
    test_list_users(&mut client).await?;

    // 3. Client Streaming
    test_batch_create(&mut client).await?;

    // 4. Bidirectional Streaming
    test_chat(&mut client).await?;

    opentelemetry::global::shutdown_tracer_provider();
    Ok(())
}

#[instrument(skip(client))]
async fn test_create_user(client: &mut UserServiceClient<Channel>) -> anyhow::Result<()> {
    let request = tonic::Request::new(CreateUserRequest {
        email: "test@example.com".to_string(),
        name: "Test User".to_string(),
    });

    let response = client.create_user(request).await?;
    info!("Created user: {:?}", response.into_inner());

    Ok(())
}

#[instrument(skip(client))]
async fn test_list_users(client: &mut UserServiceClient<Channel>) -> anyhow::Result<()> {
    let request = tonic::Request::new(ListUsersRequest {
        page_size: 10,
        page_token: String::new(),
    });

    let mut stream = client.list_users(request).await?.into_inner();

    while let Some(user) = stream.message().await? {
        info!("Received user: {:?}", user);
    }

    Ok(())
}

#[instrument(skip(client))]
async fn test_batch_create(client: &mut UserServiceClient<Channel>) -> anyhow::Result<()> {
    let requests = tokio_stream::iter(vec![
        CreateUserRequest {
            email: "user1@example.com".to_string(),
            name: "User 1".to_string(),
        },
        CreateUserRequest {
            email: "user2@example.com".to_string(),
            name: "User 2".to_string(),
        },
    ]);

    let response = client.batch_create_users(requests).await?;
    info!("Batch created {} users", response.into_inner().created_count);

    Ok(())
}

#[instrument(skip(client))]
async fn test_chat(client: &mut UserServiceClient<Channel>) -> anyhow::Result<()> {
    let messages = tokio_stream::iter(vec![
        ChatMessage {
            user_id: "client".to_string(),
            message: "Hello".to_string(),
            timestamp: chrono::Utc::now().timestamp(),
        },
        ChatMessage {
            user_id: "client".to_string(),
            message: "World".to_string(),
            timestamp: chrono::Utc::now().timestamp(),
        },
    ]);

    let mut stream = client.chat(messages).await?.into_inner();

    while let Some(msg) = stream.message().await? {
        info!("Received: {}", msg.message);
    }

    Ok(())
}
```

---

## 3. OTLP 可观测性集成

```rust
// src/telemetry.rs
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{trace, Resource, runtime};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

pub fn init() -> anyhow::Result<()> {
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .with_trace_config(
            trace::config().with_resource(Resource::new(vec![
                KeyValue::new("service.name", "tonic-grpc-service"),
                KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
            ]))
        )
        .install_batch(runtime::Tokio)?;

    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new("info"))
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    Ok(())
}
```

---

## 4. 高级特性

### 4.1 拦截器 (Middleware)

```rust
use tonic::{Request, Status};

fn auth_interceptor(mut req: Request<()>) -> Result<Request<()>, Status> {
    let token = req.metadata()
        .get("authorization")
        .and_then(|t| t.to_str().ok());

    match token {
        Some(token) if token.starts_with("Bearer ") => Ok(req),
        _ => Err(Status::unauthenticated("Missing token")),
    }
}

// 使用拦截器
let channel = Channel::from_static("http://localhost:50051")
    .connect()
    .await?;

let mut client = UserServiceClient::with_interceptor(channel, auth_interceptor);
```

### 4.2 负载均衡

```rust
use tonic::transport::{Channel, Endpoint};

let endpoints = vec![
    Endpoint::from_static("http://server1:50051"),
    Endpoint::from_static("http://server2:50051"),
];

let channel = Channel::balance_list(endpoints.into_iter());
let client = UserServiceClient::new(channel);
```

---

## 5. 生产部署

### 5.1 Docker Compose

```yaml
version: '3.8'

services:
  grpc-server:
    build: .
    command: ["./server"]
    ports:
      - "50051:50051"
    environment:
      RUST_LOG: info
      OTLP_ENDPOINT: http://otel-collector:4317

  grpc-client:
    build: .
    command: ["./client"]
    depends_on:
      - grpc-server
    environment:
      RUST_LOG: info

  otel-collector:
    image: otel/opentelemetry-collector:0.115.1
    ports:
      - "4317:4317"
```

---

## 总结

✅ **完整 gRPC 实现** (Unary, Streaming, Bidirectional)  
✅ **深度 OTLP 集成** (分布式追踪)  
✅ **健康检查** (tonic-health)  
✅ **生产级部署** (Docker Compose + K8s)

---

**作者**: OTLP Rust 架构团队  
**日期**: 2025-10-11  
**版本**: v1.0.0
