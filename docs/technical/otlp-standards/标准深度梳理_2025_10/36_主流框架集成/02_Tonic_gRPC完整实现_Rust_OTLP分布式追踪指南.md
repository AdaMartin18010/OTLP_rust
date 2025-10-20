# Tonic gRPC 完整实现 - Rust 1.90 + OTLP 分布式追踪指南

> **文档版本**: v1.0.0  
> **创建日期**: 2025-10-11  
> **Rust 版本**: 1.90+  
> **核心依赖**: tonic 0.12, tonic-build 0.12, prost 0.13, tokio 1.40, opentelemetry 0.31  
> **对齐标准**: gRPC Official, CNCF OpenTelemetry, Google Cloud Best Practices

---

## 目录

- [Tonic gRPC 完整实现 - Rust 1.90 + OTLP 分布式追踪指南](#tonic-grpc-完整实现---rust-190--otlp-分布式追踪指南)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 什么是 gRPC？](#11-什么是-grpc)
    - [1.2 Tonic 框架优势](#12-tonic-框架优势)
    - [1.3 本文档目标](#13-本文档目标)
  - [2. gRPC 核心概念](#2-grpc-核心概念)
    - [2.1 四种 RPC 模式](#21-四种-rpc-模式)
    - [2.2 Protocol Buffers 核心](#22-protocol-buffers-核心)
    - [2.3 HTTP/2 核心特性](#23-http2-核心特性)
  - [3. 环境准备与依赖配置](#3-环境准备与依赖配置)
    - [3.1 Cargo.toml 依赖](#31-cargotoml-依赖)
    - [3.2 构建脚本 build.rs](#32-构建脚本-buildrs)
  - [4. Proto 定义与代码生成](#4-proto-定义与代码生成)
    - [4.1 用户服务 Proto 定义](#41-用户服务-proto-定义)
    - [4.2 订单服务 Proto 定义](#42-订单服务-proto-定义)
    - [4.3 生成的 Rust 代码结构](#43-生成的-rust-代码结构)
  - [5. Tonic Server 完整实现](#5-tonic-server-完整实现)
    - [5.1 用户服务实现](#51-用户服务实现)
    - [5.2 订单服务实现](#52-订单服务实现)
    - [5.3 Server 启动代码](#53-server-启动代码)
  - [6. Tonic Client 完整实现](#6-tonic-client-完整实现)
    - [6.1 基础客户端实现](#61-基础客户端实现)
    - [6.2 客户端使用示例](#62-客户端使用示例)
  - [7. OTLP 分布式追踪集成](#7-otlp-分布式追踪集成)
    - [7.1 OTLP 初始化配置](#71-otlp-初始化配置)
    - [7.2 服务端集成 OTLP](#72-服务端集成-otlp)
    - [7.3 客户端集成 OTLP](#73-客户端集成-otlp)
    - [7.4 OTLP 追踪效果](#74-otlp-追踪效果)
  - [8. 四种 RPC 模式实现](#8-四种-rpc-模式实现)
    - [8.1 Unary RPC（一请求一响应）](#81-unary-rpc一请求一响应)
    - [8.2 Server Streaming（一请求多响应）](#82-server-streaming一请求多响应)
    - [8.3 Client Streaming（多请求一响应）](#83-client-streaming多请求一响应)
    - [8.4 Bidirectional Streaming（多请求多响应）](#84-bidirectional-streaming多请求多响应)
  - [9. 拦截器 Interceptor 深度应用](#9-拦截器-interceptor-深度应用)
    - [9.1 认证拦截器](#91-认证拦截器)
    - [9.2 日志拦截器](#92-日志拦截器)
    - [9.3 限流拦截器](#93-限流拦截器)
    - [9.4 应用拦截器到服务](#94-应用拦截器到服务)
  - [10. 健康检查与反射服务](#10-健康检查与反射服务)
    - [10.1 健康检查服务](#101-健康检查服务)
    - [10.2 客户端健康检查](#102-客户端健康检查)
    - [10.3 反射服务](#103-反射服务)
  - [11. 错误处理与状态码](#11-错误处理与状态码)
    - [11.1 gRPC 状态码](#111-grpc-状态码)
    - [11.2 自定义错误类型](#112-自定义错误类型)
    - [11.3 错误详情扩展](#113-错误详情扩展)
  - [12. 负载均衡与服务发现](#12-负载均衡与服务发现)
    - [12.1 客户端负载均衡](#121-客户端负载均衡)
    - [12.2 Consul 服务发现](#122-consul-服务发现)
  - [13. TLS/mTLS 安全通信](#13-tlsmtls-安全通信)
    - [13.1 生成证书](#131-生成证书)
    - [13.2 Server 端 TLS 配置](#132-server-端-tls-配置)
    - [13.3 Client 端 TLS 配置](#133-client-端-tls-配置)
  - [14. 性能优化与最佳实践](#14-性能优化与最佳实践)
    - [14.1 连接池配置](#141-连接池配置)
    - [14.2 消息压缩](#142-消息压缩)
    - [14.3 流式背压控制](#143-流式背压控制)
    - [14.4 超时与重试](#144-超时与重试)
    - [14.5 批量处理优化](#145-批量处理优化)
    - [14.6 Prometheus 指标导出](#146-prometheus-指标导出)
  - [15. 部署与监控](#15-部署与监控)
    - [15.1 Docker Compose 部署](#151-docker-compose-部署)
    - [15.2 Dockerfile](#152-dockerfile)
    - [15.3 Prometheus 配置](#153-prometheus-配置)
    - [15.4 Grafana Dashboard](#154-grafana-dashboard)
  - [16. 国际标准对齐](#16-国际标准对齐)
    - [16.1 gRPC 官方标准](#161-grpc-官方标准)
    - [16.2 CNCF OpenTelemetry](#162-cncf-opentelemetry)
    - [16.3 Google Cloud Best Practices](#163-google-cloud-best-practices)
    - [16.4 Rust 1.90 特性](#164-rust-190-特性)
  - [17. 总结](#17-总结)
    - [17.1 核心要点](#171-核心要点)
    - [17.2 生产检查清单](#172-生产检查清单)
    - [17.3 性能优化建议](#173-性能优化建议)
    - [17.4 学习路径](#174-学习路径)
  - [附录 A: 完整项目结构](#附录-a-完整项目结构)
  - [附录 B: 参考资源](#附录-b-参考资源)
    - [官方文档](#官方文档)
    - [标准规范](#标准规范)
    - [最佳实践](#最佳实践)

---

## 1. 概述

### 1.1 什么是 gRPC？

**gRPC** 是由 Google 开发的高性能、开源、通用的 RPC (Remote Procedure Call) 框架。它基于 **HTTP/2** 协议，使用 **Protocol Buffers** (protobuf) 作为接口定义语言 (IDL) 和序列化格式。

**核心特性**：

- **高性能**: HTTP/2 多路复用、头部压缩、二进制传输
- **跨语言**: 支持 20+ 种编程语言
- **流式通信**: 支持单向流和双向流
- **强类型**: 通过 protobuf 定义严格的类型契约
- **插件化**: 拦截器、负载均衡、服务发现等扩展机制

### 1.2 Tonic 框架优势

**Tonic** 是 Rust 生态中最成熟的 gRPC 实现，完全基于 async/await 和 Tokio 运行时。

**核心优势**：

- **纯 Rust 实现**: 无 C/C++ 依赖，编译快速
- **异步原生**: 基于 `tokio` 和 `async-trait`
- **类型安全**: 利用 Rust 类型系统在编译时保证正确性
- **性能卓越**: 零拷贝、内存安全、无 GC
- **生态完善**: 与 `tower`、`hyper`、`tracing` 深度集成

### 1.3 本文档目标

1. **完整实现**：从 Proto 定义到生产部署的完整链路
2. **OTLP 集成**：分布式追踪、指标、日志的深度集成
3. **生产级实践**：错误处理、重试、超时、安全、监控
4. **国际标准对齐**：对标 Google、CNCF 最佳实践

---

## 2. gRPC 核心概念

### 2.1 四种 RPC 模式

| 模式 | 描述 | 使用场景 |
|------|------|----------|
| **Unary RPC** | 一请求一响应 | 普通 API 调用、查询操作 |
| **Server Streaming** | 一请求多响应 | 日志推送、实时数据流 |
| **Client Streaming** | 多请求一响应 | 文件上传、批量数据提交 |
| **Bidirectional Streaming** | 多请求多响应 | 聊天、实时协作、股票行情 |

### 2.2 Protocol Buffers 核心

**Protobuf** 是 Google 的结构化数据序列化协议，比 JSON/XML 更高效。

**优势**：

- **紧凑**: 二进制编码，体积小 3-10 倍
- **快速**: 解析速度比 JSON 快 20-100 倍
- **强类型**: 向前/向后兼容
- **跨语言**: 一次定义，多语言生成

### 2.3 HTTP/2 核心特性

gRPC 充分利用 HTTP/2 的优势：

| 特性 | 说明 | 收益 |
|------|------|------|
| **多路复用** | 单连接多并发请求 | 减少连接开销 |
| **头部压缩** | HPACK 算法压缩 | 降低带宽 |
| **流量控制** | 接收方背压控制 | 防止内存溢出 |
| **服务端推送** | 主动推送资源 | 支持流式 |

---

## 3. 环境准备与依赖配置

### 3.1 Cargo.toml 依赖

```toml
[package]
name = "tonic-otlp-example"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# Tonic gRPC 核心
tonic = { version = "0.12", features = ["tls", "gzip", "zstd"] }
prost = "0.13"
prost-types = "0.13"

# Tokio 异步运行时
tokio = { version = "1.40", features = ["full"] }
tokio-stream = "0.1"

# OpenTelemetry 可观测性
opentelemetry = { version = "0.31", features = ["trace", "metrics", "logs"] }
opentelemetry-otlp = { version = "0.24", features = ["grpc-tonic", "trace", "metrics", "logs"] }
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
opentelemetry-semantic-conventions = "0.31"
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.28"

# 错误处理
thiserror = "2.0"
anyhow = "1.0"

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 工具库
uuid = { version = "1.11", features = ["v4", "serde"] }
chrono = { version = "0.4", features = ["serde"] }
tower = "0.5"
tower-http = { version = "0.6", features = ["trace", "timeout", "compression-gzip"] }

# 健康检查
tonic-health = "0.12"
# 反射服务
tonic-reflection = "0.12"

[build-dependencies]
tonic-build = "0.12"

[dev-dependencies]
mockall = "0.13"
tokio-test = "0.4"
```

### 3.2 构建脚本 build.rs

**Tonic** 使用 `tonic-build` 在编译时从 `.proto` 文件生成 Rust 代码。

```rust
// build.rs
fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 配置代码生成选项
    tonic_build::configure()
        // 启用类型属性宏（用于 serde）
        .type_attribute(".", "#[derive(serde::Serialize, serde::Deserialize)]")
        // 为所有消息添加 Clone
        .type_attribute(".", "#[derive(Clone)]")
        // 启用服务端代码生成
        .build_server(true)
        // 启用客户端代码生成
        .build_client(true)
        // 启用流式传输
        .build_transport(true)
        // 编译 proto 文件
        .compile(
            &[
                "proto/user_service.proto",
                "proto/order_service.proto",
            ],
            &["proto"], // include 目录
        )?;

    // 监听 proto 文件变化自动重新编译
    println!("cargo:rerun-if-changed=proto/");
    
    Ok(())
}
```

---

## 4. Proto 定义与代码生成

### 4.1 用户服务 Proto 定义

```protobuf
// proto/user_service.proto
syntax = "proto3";

package user.v1;

import "google/protobuf/timestamp.proto";
import "google/protobuf/empty.proto";

// 用户服务定义
service UserService {
  // Unary RPC: 创建用户
  rpc CreateUser(CreateUserRequest) returns (User);
  
  // Unary RPC: 获取用户
  rpc GetUser(GetUserRequest) returns (User);
  
  // Server Streaming: 批量查询用户
  rpc ListUsers(ListUsersRequest) returns (stream User);
  
  // Client Streaming: 批量创建用户
  rpc BatchCreateUsers(stream CreateUserRequest) returns (BatchCreateUsersResponse);
  
  // Bidirectional Streaming: 实时聊天
  rpc Chat(stream ChatMessage) returns (stream ChatMessage);
}

// 用户模型
message User {
  string id = 1;
  string username = 2;
  string email = 3;
  google.protobuf.Timestamp created_at = 4;
  google.protobuf.Timestamp updated_at = 5;
  UserStatus status = 6;
}

// 用户状态枚举
enum UserStatus {
  USER_STATUS_UNSPECIFIED = 0;
  USER_STATUS_ACTIVE = 1;
  USER_STATUS_INACTIVE = 2;
  USER_STATUS_BANNED = 3;
}

// 创建用户请求
message CreateUserRequest {
  string username = 1;
  string email = 2;
}

// 获取用户请求
message GetUserRequest {
  string id = 1;
}

// 列表查询请求
message ListUsersRequest {
  int32 page = 1;
  int32 page_size = 2;
  string filter = 3;
}

// 批量创建响应
message BatchCreateUsersResponse {
  repeated User users = 1;
  int32 success_count = 2;
  int32 failure_count = 3;
}

// 聊天消息
message ChatMessage {
  string user_id = 1;
  string content = 2;
  google.protobuf.Timestamp timestamp = 3;
}
```

### 4.2 订单服务 Proto 定义

```protobuf
// proto/order_service.proto
syntax = "proto3";

package order.v1;

import "google/protobuf/timestamp.proto";

service OrderService {
  rpc CreateOrder(CreateOrderRequest) returns (Order);
  rpc GetOrder(GetOrderRequest) returns (Order);
  rpc CancelOrder(CancelOrderRequest) returns (Order);
  rpc StreamOrders(StreamOrdersRequest) returns (stream Order);
}

message Order {
  string id = 1;
  string user_id = 2;
  repeated OrderItem items = 3;
  double total_amount = 4;
  OrderStatus status = 5;
  google.protobuf.Timestamp created_at = 6;
}

message OrderItem {
  string product_id = 1;
  int32 quantity = 2;
  double price = 3;
}

enum OrderStatus {
  ORDER_STATUS_UNSPECIFIED = 0;
  ORDER_STATUS_PENDING = 1;
  ORDER_STATUS_CONFIRMED = 2;
  ORDER_STATUS_SHIPPED = 3;
  ORDER_STATUS_DELIVERED = 4;
  ORDER_STATUS_CANCELLED = 5;
}

message CreateOrderRequest {
  string user_id = 1;
  repeated OrderItem items = 2;
}

message GetOrderRequest {
  string id = 1;
}

message CancelOrderRequest {
  string id = 1;
}

message StreamOrdersRequest {
  string user_id = 1;
}
```

### 4.3 生成的 Rust 代码结构

运行 `cargo build` 后，`tonic-build` 会生成：

```text
target/
└── debug/
    └── build/
        └── tonic-otlp-example-xxx/
            └── out/
                ├── user.v1.rs         # 用户服务代码
                └── order.v1.rs        # 订单服务代码
```

在代码中引用：

```rust
// src/lib.rs
pub mod user {
    pub mod v1 {
        tonic::include_proto!("user.v1");
    }
}

pub mod order {
    pub mod v1 {
        tonic::include_proto!("order.v1");
    }
}
```

---

## 5. Tonic Server 完整实现

### 5.1 用户服务实现

```rust
// src/services/user_service.rs
use tonic::{Request, Response, Status, Streaming};
use tokio_stream::wrappers::ReceiverStream;
use tokio::sync::mpsc;
use tracing::{info, error, instrument};
use uuid::Uuid;
use std::sync::Arc;
use std::collections::HashMap;
use tokio::sync::RwLock;
use chrono::Utc;

use crate::user::v1::{
    user_service_server::{UserService, UserServiceServer},
    User, CreateUserRequest, GetUserRequest, ListUsersRequest,
    BatchCreateUsersResponse, ChatMessage, UserStatus,
};

/// 用户存储（生产环境应使用数据库）
type UserStore = Arc<RwLock<HashMap<String, User>>>;

/// 用户服务实现
pub struct UserServiceImpl {
    store: UserStore,
}

impl UserServiceImpl {
    pub fn new() -> Self {
        Self {
            store: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    pub fn into_server(self) -> UserServiceServer<Self> {
        UserServiceServer::new(self)
    }
}

#[tonic::async_trait]
impl UserService for UserServiceImpl {
    /// Unary RPC: 创建用户
    #[instrument(skip(self, request), fields(otel.kind = "server", rpc.service = "UserService", rpc.method = "CreateUser"))]
    async fn create_user(
        &self,
        request: Request<CreateUserRequest>,
    ) -> Result<Response<User>, Status> {
        let req = request.into_inner();
        
        info!(
            username = %req.username,
            email = %req.email,
            "Creating new user"
        );
        
        // 验证输入
        if req.username.is_empty() {
            error!("Username cannot be empty");
            return Err(Status::invalid_argument("username cannot be empty"));
        }
        
        if !req.email.contains('@') {
            error!(email = %req.email, "Invalid email format");
            return Err(Status::invalid_argument("invalid email format"));
        }
        
        // 创建用户
        let now = Some(prost_types::Timestamp {
            seconds: Utc::now().timestamp(),
            nanos: 0,
        });
        
        let user = User {
            id: Uuid::new_v4().to_string(),
            username: req.username,
            email: req.email,
            created_at: now.clone(),
            updated_at: now,
            status: UserStatus::Active as i32,
        };
        
        // 存储用户
        self.store.write().await.insert(user.id.clone(), user.clone());
        
        info!(user_id = %user.id, "User created successfully");
        
        Ok(Response::new(user))
    }
    
    /// Unary RPC: 获取用户
    #[instrument(skip(self, request), fields(otel.kind = "server", rpc.service = "UserService", rpc.method = "GetUser"))]
    async fn get_user(
        &self,
        request: Request<GetUserRequest>,
    ) -> Result<Response<User>, Status> {
        let user_id = request.into_inner().id;
        
        info!(user_id = %user_id, "Fetching user");
        
        let store = self.store.read().await;
        
        match store.get(&user_id) {
            Some(user) => {
                info!(user_id = %user_id, "User found");
                Ok(Response::new(user.clone()))
            }
            None => {
                error!(user_id = %user_id, "User not found");
                Err(Status::not_found(format!("User {} not found", user_id)))
            }
        }
    }
    
    /// Server Streaming: 批量查询用户
    type ListUsersStream = ReceiverStream<Result<User, Status>>;
    
    #[instrument(skip(self, request), fields(otel.kind = "server", rpc.service = "UserService", rpc.method = "ListUsers"))]
    async fn list_users(
        &self,
        request: Request<ListUsersRequest>,
    ) -> Result<Response<Self::ListUsersStream>, Status> {
        let req = request.into_inner();
        
        info!(
            page = req.page,
            page_size = req.page_size,
            filter = %req.filter,
            "Listing users"
        );
        
        let (tx, rx) = mpsc::channel(100);
        
        let store = self.store.clone();
        
        // 在后台任务中流式发送用户
        tokio::spawn(async move {
            let users = store.read().await;
            
            for user in users.values() {
                // 简单过滤逻辑
                if !req.filter.is_empty() && !user.username.contains(&req.filter) {
                    continue;
                }
                
                if tx.send(Ok(user.clone())).await.is_err() {
                    error!("Client disconnected during streaming");
                    break;
                }
                
                // 模拟延迟
                tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
            }
        });
        
        Ok(Response::new(ReceiverStream::new(rx)))
    }
    
    /// Client Streaming: 批量创建用户
    #[instrument(skip(self, request), fields(otel.kind = "server", rpc.service = "UserService", rpc.method = "BatchCreateUsers"))]
    async fn batch_create_users(
        &self,
        request: Request<Streaming<CreateUserRequest>>,
    ) -> Result<Response<BatchCreateUsersResponse>, Status> {
        let mut stream = request.into_inner();
        
        info!("Starting batch user creation");
        
        let mut users = Vec::new();
        let mut success_count = 0;
        let mut failure_count = 0;
        
        while let Some(result) = stream.message().await? {
            match self.create_user_internal(&result).await {
                Ok(user) => {
                    users.push(user);
                    success_count += 1;
                }
                Err(e) => {
                    error!(error = %e, "Failed to create user");
                    failure_count += 1;
                }
            }
        }
        
        info!(
            success_count = success_count,
            failure_count = failure_count,
            "Batch user creation completed"
        );
        
        let response = BatchCreateUsersResponse {
            users,
            success_count,
            failure_count,
        };
        
        Ok(Response::new(response))
    }
    
    /// Bidirectional Streaming: 实时聊天
    type ChatStream = ReceiverStream<Result<ChatMessage, Status>>;
    
    #[instrument(skip(self, request), fields(otel.kind = "server", rpc.service = "UserService", rpc.method = "Chat"))]
    async fn chat(
        &self,
        request: Request<Streaming<ChatMessage>>,
    ) -> Result<Response<Self::ChatStream>, Status> {
        let mut in_stream = request.into_inner();
        let (tx, rx) = mpsc::channel(100);
        
        info!("Chat stream established");
        
        tokio::spawn(async move {
            while let Some(result) = in_stream.message().await.transpose() {
                match result {
                    Ok(msg) => {
                        info!(
                            user_id = %msg.user_id,
                            content = %msg.content,
                            "Received chat message"
                        );
                        
                        // 回显消息（生产环境应广播到所有客户端）
                        let echo = ChatMessage {
                            user_id: format!("echo-{}", msg.user_id),
                            content: format!("Echo: {}", msg.content),
                            timestamp: Some(prost_types::Timestamp {
                                seconds: Utc::now().timestamp(),
                                nanos: 0,
                            }),
                        };
                        
                        if tx.send(Ok(echo)).await.is_err() {
                            error!("Client disconnected");
                            break;
                        }
                    }
                    Err(e) => {
                        error!(error = %e, "Error receiving message");
                        let _ = tx.send(Err(e)).await;
                        break;
                    }
                }
            }
        });
        
        Ok(Response::new(ReceiverStream::new(rx)))
    }
}

impl UserServiceImpl {
    /// 内部创建用户方法（无 RPC 包装）
    async fn create_user_internal(&self, req: &CreateUserRequest) -> Result<User, Status> {
        if req.username.is_empty() {
            return Err(Status::invalid_argument("username cannot be empty"));
        }
        
        let now = Some(prost_types::Timestamp {
            seconds: Utc::now().timestamp(),
            nanos: 0,
        });
        
        let user = User {
            id: Uuid::new_v4().to_string(),
            username: req.username.clone(),
            email: req.email.clone(),
            created_at: now.clone(),
            updated_at: now,
            status: UserStatus::Active as i32,
        };
        
        self.store.write().await.insert(user.id.clone(), user.clone());
        
        Ok(user)
    }
}
```

### 5.2 订单服务实现

```rust
// src/services/order_service.rs
use tonic::{Request, Response, Status};
use tokio_stream::wrappers::ReceiverStream;
use tokio::sync::mpsc;
use tracing::{info, error, instrument};
use uuid::Uuid;
use std::sync::Arc;
use std::collections::HashMap;
use tokio::sync::RwLock;
use chrono::Utc;

use crate::order::v1::{
    order_service_server::{OrderService, OrderServiceServer},
    Order, CreateOrderRequest, GetOrderRequest, CancelOrderRequest,
    StreamOrdersRequest, OrderStatus,
};

type OrderStore = Arc<RwLock<HashMap<String, Order>>>;

pub struct OrderServiceImpl {
    store: OrderStore,
}

impl OrderServiceImpl {
    pub fn new() -> Self {
        Self {
            store: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    pub fn into_server(self) -> OrderServiceServer<Self> {
        OrderServiceServer::new(self)
    }
}

#[tonic::async_trait]
impl OrderService for OrderServiceImpl {
    #[instrument(skip(self, request), fields(otel.kind = "server", rpc.service = "OrderService", rpc.method = "CreateOrder"))]
    async fn create_order(
        &self,
        request: Request<CreateOrderRequest>,
    ) -> Result<Response<Order>, Status> {
        let req = request.into_inner();
        
        info!(user_id = %req.user_id, "Creating order");
        
        if req.items.is_empty() {
            return Err(Status::invalid_argument("Order must have at least one item"));
        }
        
        let total_amount: f64 = req.items.iter()
            .map(|item| item.price * item.quantity as f64)
            .sum();
        
        let order = Order {
            id: Uuid::new_v4().to_string(),
            user_id: req.user_id,
            items: req.items,
            total_amount,
            status: OrderStatus::Pending as i32,
            created_at: Some(prost_types::Timestamp {
                seconds: Utc::now().timestamp(),
                nanos: 0,
            }),
        };
        
        self.store.write().await.insert(order.id.clone(), order.clone());
        
        info!(order_id = %order.id, total_amount = total_amount, "Order created");
        
        Ok(Response::new(order))
    }
    
    #[instrument(skip(self, request), fields(otel.kind = "server", rpc.service = "OrderService", rpc.method = "GetOrder"))]
    async fn get_order(
        &self,
        request: Request<GetOrderRequest>,
    ) -> Result<Response<Order>, Status> {
        let order_id = request.into_inner().id;
        
        info!(order_id = %order_id, "Fetching order");
        
        let store = self.store.read().await;
        
        match store.get(&order_id) {
            Some(order) => Ok(Response::new(order.clone())),
            None => Err(Status::not_found(format!("Order {} not found", order_id))),
        }
    }
    
    #[instrument(skip(self, request), fields(otel.kind = "server", rpc.service = "OrderService", rpc.method = "CancelOrder"))]
    async fn cancel_order(
        &self,
        request: Request<CancelOrderRequest>,
    ) -> Result<Response<Order>, Status> {
        let order_id = request.into_inner().id;
        
        info!(order_id = %order_id, "Cancelling order");
        
        let mut store = self.store.write().await;
        
        match store.get_mut(&order_id) {
            Some(order) => {
                order.status = OrderStatus::Cancelled as i32;
                info!(order_id = %order_id, "Order cancelled");
                Ok(Response::new(order.clone()))
            }
            None => Err(Status::not_found(format!("Order {} not found", order_id))),
        }
    }
    
    type StreamOrdersStream = ReceiverStream<Result<Order, Status>>;
    
    #[instrument(skip(self, request), fields(otel.kind = "server", rpc.service = "OrderService", rpc.method = "StreamOrders"))]
    async fn stream_orders(
        &self,
        request: Request<StreamOrdersRequest>,
    ) -> Result<Response<Self::StreamOrdersStream>, Status> {
        let user_id = request.into_inner().user_id;
        
        info!(user_id = %user_id, "Streaming user orders");
        
        let (tx, rx) = mpsc::channel(100);
        let store = self.store.clone();
        
        tokio::spawn(async move {
            let orders = store.read().await;
            
            for order in orders.values() {
                if order.user_id == user_id {
                    if tx.send(Ok(order.clone())).await.is_err() {
                        break;
                    }
                    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
                }
            }
        });
        
        Ok(Response::new(ReceiverStream::new(rx)))
    }
}
```

### 5.3 Server 启动代码

```rust
// src/bin/server.rs
use tonic::transport::Server;
use tonic_health::server::health_reporter;
use tonic_reflection::server::Builder as ReflectionBuilder;
use tracing::{info, error};
use anyhow::Result;

mod services;
use services::{UserServiceImpl, OrderServiceImpl};

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化 OTLP 追踪（下文详述）
    init_otlp_tracing()?;
    
    let addr = "0.0.0.0:50051".parse()?;
    
    info!("Starting gRPC server on {}", addr);
    
    // 健康检查服务
    let (mut health_reporter, health_service) = health_reporter();
    health_reporter.set_serving::<UserServiceServer<UserServiceImpl>>().await;
    health_reporter.set_serving::<OrderServiceServer<OrderServiceImpl>>().await;
    
    // 反射服务（用于 grpcurl 调试）
    let reflection_service = ReflectionBuilder::configure()
        .register_encoded_file_descriptor_set(crate::user::v1::FILE_DESCRIPTOR_SET)
        .register_encoded_file_descriptor_set(crate::order::v1::FILE_DESCRIPTOR_SET)
        .build()?;
    
    // 启动服务器
    Server::builder()
        // 添加 OTLP 拦截器层
        .layer(tower::ServiceBuilder::new()
            .layer(tower_http::trace::TraceLayer::new_for_grpc())
            .into_inner())
        // 注册业务服务
        .add_service(UserServiceImpl::new().into_server())
        .add_service(OrderServiceImpl::new().into_server())
        // 注册健康检查
        .add_service(health_service)
        // 注册反射服务
        .add_service(reflection_service)
        .serve(addr)
        .await?;
    
    Ok(())
}

fn init_otlp_tracing() -> Result<()> {
    // 下文第 7 节详细实现
    Ok(())
}
```

---

## 6. Tonic Client 完整实现

### 6.1 基础客户端实现

```rust
// src/client/user_client.rs
use tonic::{transport::Channel, Request, Status};
use tokio_stream::StreamExt;
use tracing::{info, error, instrument};
use anyhow::Result;

use crate::user::v1::{
    user_service_client::UserServiceClient,
    CreateUserRequest, GetUserRequest, ListUsersRequest, ChatMessage,
};

pub struct UserClient {
    client: UserServiceClient<Channel>,
}

impl UserClient {
    /// 连接到服务器
    pub async fn connect(endpoint: &str) -> Result<Self> {
        info!(endpoint = %endpoint, "Connecting to UserService");
        
        let channel = Channel::from_shared(endpoint.to_string())?
            .connect()
            .await?;
        
        let client = UserServiceClient::new(channel);
        
        Ok(Self { client })
    }
    
    /// Unary RPC: 创建用户
    #[instrument(skip(self), fields(otel.kind = "client", rpc.service = "UserService", rpc.method = "CreateUser"))]
    pub async fn create_user(
        &mut self,
        username: &str,
        email: &str,
    ) -> Result<String, Status> {
        info!(username = %username, email = %email, "Creating user");
        
        let request = Request::new(CreateUserRequest {
            username: username.to_string(),
            email: email.to_string(),
        });
        
        let response = self.client.create_user(request).await?;
        let user = response.into_inner();
        
        info!(user_id = %user.id, "User created successfully");
        
        Ok(user.id)
    }
    
    /// Unary RPC: 获取用户
    #[instrument(skip(self), fields(otel.kind = "client", rpc.service = "UserService", rpc.method = "GetUser"))]
    pub async fn get_user(&mut self, user_id: &str) -> Result<(), Status> {
        info!(user_id = %user_id, "Fetching user");
        
        let request = Request::new(GetUserRequest {
            id: user_id.to_string(),
        });
        
        let response = self.client.get_user(request).await?;
        let user = response.into_inner();
        
        info!(
            user_id = %user.id,
            username = %user.username,
            email = %user.email,
            "User retrieved"
        );
        
        Ok(())
    }
    
    /// Server Streaming: 列表查询
    #[instrument(skip(self), fields(otel.kind = "client", rpc.service = "UserService", rpc.method = "ListUsers"))]
    pub async fn list_users(&mut self, filter: &str) -> Result<(), Status> {
        info!(filter = %filter, "Listing users");
        
        let request = Request::new(ListUsersRequest {
            page: 1,
            page_size: 10,
            filter: filter.to_string(),
        });
        
        let mut stream = self.client.list_users(request).await?.into_inner();
        
        let mut count = 0;
        while let Some(user) = stream.next().await {
            match user {
                Ok(u) => {
                    info!(
                        user_id = %u.id,
                        username = %u.username,
                        "Received user from stream"
                    );
                    count += 1;
                }
                Err(e) => {
                    error!(error = %e, "Error in stream");
                    return Err(e);
                }
            }
        }
        
        info!(total_users = count, "Stream completed");
        
        Ok(())
    }
    
    /// Client Streaming: 批量创建
    #[instrument(skip(self), fields(otel.kind = "client", rpc.service = "UserService", rpc.method = "BatchCreateUsers"))]
    pub async fn batch_create_users(&mut self, users: Vec<(&str, &str)>) -> Result<(), Status> {
        info!(count = users.len(), "Batch creating users");
        
        let requests = tokio_stream::iter(users.into_iter().map(|(username, email)| {
            CreateUserRequest {
                username: username.to_string(),
                email: email.to_string(),
            }
        }));
        
        let request = Request::new(requests);
        
        let response = self.client.batch_create_users(request).await?;
        let result = response.into_inner();
        
        info!(
            success_count = result.success_count,
            failure_count = result.failure_count,
            "Batch creation completed"
        );
        
        Ok(())
    }
    
    /// Bidirectional Streaming: 聊天
    #[instrument(skip(self), fields(otel.kind = "client", rpc.service = "UserService", rpc.method = "Chat"))]
    pub async fn chat(&mut self, user_id: &str, messages: Vec<&str>) -> Result<(), Status> {
        info!(user_id = %user_id, "Starting chat session");
        
        let (tx, rx) = tokio::sync::mpsc::channel(100);
        
        let outbound = tokio_stream::wrappers::ReceiverStream::new(rx);
        let request = Request::new(outbound);
        
        let mut inbound = self.client.chat(request).await?.into_inner();
        
        // 发送消息任务
        let user_id_clone = user_id.to_string();
        tokio::spawn(async move {
            for msg in messages {
                let chat_msg = ChatMessage {
                    user_id: user_id_clone.clone(),
                    content: msg.to_string(),
                    timestamp: Some(prost_types::Timestamp {
                        seconds: chrono::Utc::now().timestamp(),
                        nanos: 0,
                    }),
                };
                
                if tx.send(chat_msg).await.is_err() {
                    error!("Failed to send message");
                    break;
                }
                
                tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
            }
        });
        
        // 接收消息
        while let Some(result) = inbound.next().await {
            match result {
                Ok(msg) => {
                    info!(
                        user_id = %msg.user_id,
                        content = %msg.content,
                        "Received message"
                    );
                }
                Err(e) => {
                    error!(error = %e, "Chat error");
                    return Err(e);
                }
            }
        }
        
        info!("Chat session ended");
        
        Ok(())
    }
}
```

### 6.2 客户端使用示例

```rust
// src/bin/client.rs
use anyhow::Result;
use tracing::info;

mod client;
use client::UserClient;

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化 OTLP 追踪
    init_otlp_tracing()?;
    
    let mut client = UserClient::connect("http://localhost:50051").await?;
    
    // 1. Unary RPC: 创建用户
    let user_id = client.create_user("alice", "alice@example.com").await?;
    info!(user_id = %user_id, "User created");
    
    // 2. Unary RPC: 获取用户
    client.get_user(&user_id).await?;
    
    // 3. Server Streaming: 列表查询
    client.list_users("alice").await?;
    
    // 4. Client Streaming: 批量创建
    client.batch_create_users(vec![
        ("bob", "bob@example.com"),
        ("charlie", "charlie@example.com"),
    ]).await?;
    
    // 5. Bidirectional Streaming: 聊天
    client.chat(&user_id, vec![
        "Hello!",
        "How are you?",
        "Goodbye!",
    ]).await?;
    
    Ok(())
}

fn init_otlp_tracing() -> Result<()> {
    // 下文详细实现
    Ok(())
}
```

---

## 7. OTLP 分布式追踪集成

### 7.1 OTLP 初始化配置

```rust
// src/telemetry/otlp.rs
use opentelemetry::{
    global,
    trace::{TracerProvider as _, TraceError},
    KeyValue,
};
use opentelemetry_sdk::{
    trace::{self, RandomIdGenerator, Sampler},
    Resource,
};
use opentelemetry_otlp::WithExportConfig;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};
use anyhow::Result;

pub fn init_otlp_tracing(service_name: &str) -> Result<()> {
    // 配置 OpenTelemetry 导出器
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317") // Jaeger OTLP endpoint
        )
        .with_trace_config(
            trace::config()
                // 服务标识
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", service_name.to_string()),
                    KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
                    KeyValue::new("deployment.environment", "production"),
                ]))
                // 采样策略：全采样（生产环境应配置合理采样率）
                .with_sampler(Sampler::AlwaysOn)
                // ID 生成器
                .with_id_generator(RandomIdGenerator::default())
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    // 配置 tracing 订阅器
    tracing_subscriber::registry()
        // OpenTelemetry 层
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        // 控制台输出层
        .with(
            tracing_subscriber::fmt::layer()
                .with_target(true)
                .with_level(true)
                .with_thread_ids(true)
        )
        // 环境变量过滤器
        .with(EnvFilter::from_default_env().add_directive(tracing::Level::INFO.into()))
        .init();
    
    Ok(())
}

pub fn shutdown_otlp_tracing() {
    global::shutdown_tracer_provider();
}
```

### 7.2 服务端集成 OTLP

```rust
// src/bin/server.rs
use anyhow::Result;
use tracing::info;

mod telemetry;
use telemetry::{init_otlp_tracing, shutdown_otlp_tracing};

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化 OTLP
    init_otlp_tracing("user-service")?;
    
    let addr = "0.0.0.0:50051".parse()?;
    info!("Starting gRPC server on {}", addr);
    
    // 启动服务器（使用第 5.3 节代码）
    start_server(addr).await?;
    
    // 优雅关闭
    shutdown_otlp_tracing();
    
    Ok(())
}
```

### 7.3 客户端集成 OTLP

```rust
// src/bin/client.rs
use anyhow::Result;

mod telemetry;
use telemetry::{init_otlp_tracing, shutdown_otlp_tracing};

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化 OTLP
    init_otlp_tracing("user-client")?;
    
    // 执行客户端调用（使用第 6.2 节代码）
    run_client().await?;
    
    // 优雅关闭
    shutdown_otlp_tracing();
    
    Ok(())
}
```

### 7.4 OTLP 追踪效果

在 Jaeger UI 中可以看到完整的分布式追踪链：

```text
user-client: CreateUser
├─ gRPC Call (client span)
│  └─ user-service: CreateUser (server span)
│     ├─ Validate Input
│     ├─ Generate User ID
│     └─ Store User
```

**关键指标**：

- **span.kind**: `client` / `server`
- **rpc.service**: `UserService`
- **rpc.method**: `CreateUser`
- **rpc.system**: `grpc`
- **net.peer.name**: `localhost`
- **net.peer.port**: `50051`

---

## 8. 四种 RPC 模式实现

### 8.1 Unary RPC（一请求一响应）

**适用场景**：标准 CRUD 操作、查询单个资源

```rust
// Server
async fn create_user(
    &self,
    request: Request<CreateUserRequest>,
) -> Result<Response<User>, Status> {
    // 处理请求，返回单个响应
    Ok(Response::new(user))
}

// Client
let response = client.create_user(request).await?;
let user = response.into_inner();
```

### 8.2 Server Streaming（一请求多响应）

**适用场景**：分页查询、日志流、实时数据推送

```rust
// Server
type ListUsersStream = ReceiverStream<Result<User, Status>>;

async fn list_users(
    &self,
    request: Request<ListUsersRequest>,
) -> Result<Response<Self::ListUsersStream>, Status> {
    let (tx, rx) = mpsc::channel(100);
    
    tokio::spawn(async move {
        for user in users {
            tx.send(Ok(user)).await.unwrap();
        }
    });
    
    Ok(Response::new(ReceiverStream::new(rx)))
}

// Client
let mut stream = client.list_users(request).await?.into_inner();

while let Some(user) = stream.next().await {
    println!("User: {:?}", user?);
}
```

### 8.3 Client Streaming（多请求一响应）

**适用场景**：文件上传、批量数据提交、聚合统计

```rust
// Server
async fn batch_create_users(
    &self,
    request: Request<Streaming<CreateUserRequest>>,
) -> Result<Response<BatchCreateUsersResponse>, Status> {
    let mut stream = request.into_inner();
    let mut users = Vec::new();
    
    while let Some(req) = stream.message().await? {
        users.push(create_user(req).await?);
    }
    
    Ok(Response::new(BatchCreateUsersResponse { users }))
}

// Client
let requests = tokio_stream::iter(vec![req1, req2, req3]);
let response = client.batch_create_users(Request::new(requests)).await?;
```

### 8.4 Bidirectional Streaming（多请求多响应）

**适用场景**：实时聊天、协作编辑、股票行情

```rust
// Server
type ChatStream = ReceiverStream<Result<ChatMessage, Status>>;

async fn chat(
    &self,
    request: Request<Streaming<ChatMessage>>,
) -> Result<Response<Self::ChatStream>, Status> {
    let mut in_stream = request.into_inner();
    let (tx, rx) = mpsc::channel(100);
    
    tokio::spawn(async move {
        while let Some(msg) = in_stream.message().await.transpose() {
            let echo = process_message(msg?);
            tx.send(Ok(echo)).await.unwrap();
        }
    });
    
    Ok(Response::new(ReceiverStream::new(rx)))
}

// Client
let (tx, rx) = mpsc::channel(100);
let outbound = ReceiverStream::new(rx);
let mut inbound = client.chat(Request::new(outbound)).await?.into_inner();

// 发送消息
tokio::spawn(async move {
    tx.send(msg1).await.unwrap();
    tx.send(msg2).await.unwrap();
});

// 接收响应
while let Some(msg) = inbound.next().await {
    println!("Received: {:?}", msg?);
}
```

---

## 9. 拦截器 Interceptor 深度应用

### 9.1 认证拦截器

```rust
// src/interceptors/auth.rs
use tonic::{Request, Status};
use tracing::{info, warn};

/// JWT 认证拦截器
pub fn auth_interceptor(mut req: Request<()>) -> Result<Request<()>, Status> {
    let token = req.metadata()
        .get("authorization")
        .and_then(|v| v.to_str().ok())
        .ok_or_else(|| Status::unauthenticated("Missing authorization token"))?;
    
    if !token.starts_with("Bearer ") {
        warn!("Invalid authorization header format");
        return Err(Status::unauthenticated("Invalid authorization header"));
    }
    
    let token = &token[7..]; // 移除 "Bearer " 前缀
    
    // 验证 JWT（生产环境应使用 jsonwebtoken 库）
    if !validate_jwt(token) {
        warn!(token = %token, "Invalid JWT token");
        return Err(Status::unauthenticated("Invalid token"));
    }
    
    // 将用户 ID 注入到 extensions
    req.extensions_mut().insert(UserId(extract_user_id(token)));
    
    info!(user_id = %extract_user_id(token), "Request authenticated");
    
    Ok(req)
}

fn validate_jwt(token: &str) -> bool {
    // 简化示例
    !token.is_empty()
}

fn extract_user_id(token: &str) -> String {
    // 简化示例
    "user_123".to_string()
}

#[derive(Clone)]
pub struct UserId(pub String);
```

### 9.2 日志拦截器

```rust
// src/interceptors/logging.rs
use tonic::{Request, Status};
use tracing::{info, Span};
use opentelemetry::trace::TraceContextExt;

pub fn logging_interceptor(req: Request<()>) -> Result<Request<()>, Status> {
    let method = req.uri().path();
    let metadata = req.metadata();
    
    // 提取 trace context
    let cx = opentelemetry::global::get_text_map_propagator(|propagator| {
        propagator.extract(&MetadataMap(metadata))
    });
    
    let span = Span::current();
    span.set_parent(cx);
    
    info!(
        method = %method,
        remote_addr = ?metadata.get("remote-addr"),
        "Incoming gRPC request"
    );
    
    Ok(req)
}

struct MetadataMap<'a>(&'a tonic::metadata::MetadataMap);

impl<'a> opentelemetry::propagation::Extractor for MetadataMap<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.0.get(key).and_then(|v| v.to_str().ok())
    }
    
    fn keys(&self) -> Vec<&str> {
        self.0.keys().map(|k| k.as_str()).collect()
    }
}
```

### 9.3 限流拦截器

```rust
// src/interceptors/rate_limit.rs
use tonic::{Request, Status};
use std::sync::Arc;
use governor::{Quota, RateLimiter, state::direct::NotKeyed, state::InMemoryState, clock::DefaultClock};
use std::num::NonZeroU32;

pub struct RateLimitInterceptor {
    limiter: Arc<RateLimiter<NotKeyed, InMemoryState, DefaultClock>>,
}

impl RateLimitInterceptor {
    pub fn new(requests_per_second: u32) -> Self {
        let quota = Quota::per_second(NonZeroU32::new(requests_per_second).unwrap());
        let limiter = Arc::new(RateLimiter::direct(quota));
        
        Self { limiter }
    }
    
    pub fn intercept(&self, req: Request<()>) -> Result<Request<()>, Status> {
        match self.limiter.check() {
            Ok(_) => Ok(req),
            Err(_) => {
                tracing::warn!("Rate limit exceeded");
                Err(Status::resource_exhausted("Rate limit exceeded"))
            }
        }
    }
}
```

### 9.4 应用拦截器到服务

```rust
// Server 端
let user_service = UserServiceImpl::new().into_server();

// 应用拦截器
let user_service_with_auth = UserServiceServer::with_interceptor(
    user_service,
    auth_interceptor,
);

Server::builder()
    .add_service(user_service_with_auth)
    .serve(addr)
    .await?;

// Client 端
let channel = Channel::from_shared("http://localhost:50051")?
    .connect()
    .await?;

let mut client = UserServiceClient::with_interceptor(
    channel,
    |mut req: Request<()>| {
        req.metadata_mut().insert(
            "authorization",
            "Bearer my_jwt_token".parse().unwrap(),
        );
        Ok(req)
    },
);
```

---

## 10. 健康检查与反射服务

### 10.1 健康检查服务

```rust
// src/bin/server.rs
use tonic_health::server::{health_reporter, HealthReporter};

#[tokio::main]
async fn main() -> Result<()> {
    // 创建健康检查服务
    let (mut health_reporter, health_service) = health_reporter();
    
    // 注册服务健康状态
    health_reporter
        .set_serving::<UserServiceServer<UserServiceImpl>>()
        .await;
    
    health_reporter
        .set_serving::<OrderServiceServer<OrderServiceImpl>>()
        .await;
    
    // 添加到服务器
    Server::builder()
        .add_service(health_service)
        .add_service(user_service)
        .add_service(order_service)
        .serve(addr)
        .await?;
    
    Ok(())
}
```

### 10.2 客户端健康检查

```bash
# 使用 grpcurl 检查健康状态
grpcurl -plaintext localhost:50051 grpc.health.v1.Health/Check

# 响应
{
  "status": "SERVING"
}
```

### 10.3 反射服务

**gRPC Reflection** 允许客户端动态发现服务定义，无需 `.proto` 文件。

```rust
use tonic_reflection::server::Builder as ReflectionBuilder;

// 构建反射服务
let reflection_service = ReflectionBuilder::configure()
    .register_encoded_file_descriptor_set(crate::user::v1::FILE_DESCRIPTOR_SET)
    .register_encoded_file_descriptor_set(crate::order::v1::FILE_DESCRIPTOR_SET)
    .build()?;

Server::builder()
    .add_service(reflection_service)
    .serve(addr)
    .await?;
```

**使用 grpcurl 调试**：

```bash
# 列出所有服务
grpcurl -plaintext localhost:50051 list

# 输出
grpc.health.v1.Health
grpc.reflection.v1alpha.ServerReflection
user.v1.UserService
order.v1.OrderService

# 查看服务方法
grpcurl -plaintext localhost:50051 list user.v1.UserService

# 输出
user.v1.UserService.CreateUser
user.v1.UserService.GetUser
user.v1.UserService.ListUsers
user.v1.UserService.BatchCreateUsers
user.v1.UserService.Chat

# 调用方法
grpcurl -plaintext -d '{"username":"alice","email":"alice@example.com"}' \
    localhost:50051 user.v1.UserService/CreateUser
```

---

## 11. 错误处理与状态码

### 11.1 gRPC 状态码

| 状态码 | 说明 | HTTP 映射 | 使用场景 |
|--------|------|-----------|----------|
| `OK` | 成功 | 200 | 正常返回 |
| `CANCELLED` | 请求取消 | 499 | 客户端取消 |
| `INVALID_ARGUMENT` | 参数无效 | 400 | 验证失败 |
| `DEADLINE_EXCEEDED` | 超时 | 504 | 请求超时 |
| `NOT_FOUND` | 资源不存在 | 404 | 查询失败 |
| `ALREADY_EXISTS` | 资源已存在 | 409 | 重复创建 |
| `PERMISSION_DENIED` | 权限拒绝 | 403 | 鉴权失败 |
| `UNAUTHENTICATED` | 未认证 | 401 | 未登录 |
| `RESOURCE_EXHAUSTED` | 资源耗尽 | 429 | 限流 |
| `INTERNAL` | 内部错误 | 500 | 服务器错误 |
| `UNAVAILABLE` | 服务不可用 | 503 | 服务宕机 |

### 11.2 自定义错误类型

```rust
// src/errors.rs
use tonic::{Code, Status};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ServiceError {
    #[error("User not found: {0}")]
    UserNotFound(String),
    
    #[error("Invalid email format: {0}")]
    InvalidEmail(String),
    
    #[error("Database error: {0}")]
    DatabaseError(#[from] sqlx::Error),
    
    #[error("Internal error: {0}")]
    InternalError(String),
}

impl From<ServiceError> for Status {
    fn from(err: ServiceError) -> Self {
        match err {
            ServiceError::UserNotFound(id) => {
                Status::not_found(format!("User {} not found", id))
            }
            ServiceError::InvalidEmail(email) => {
                Status::invalid_argument(format!("Invalid email: {}", email))
            }
            ServiceError::DatabaseError(e) => {
                tracing::error!(error = %e, "Database error");
                Status::internal("Database error")
            }
            ServiceError::InternalError(msg) => {
                tracing::error!(error = %msg, "Internal error");
                Status::internal(msg)
            }
        }
    }
}
```

### 11.3 错误详情扩展

使用 **Rich Error Model** 提供更详细的错误信息：

```rust
use tonic::{Status, metadata::MetadataMap};
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize)]
struct ErrorDetails {
    code: String,
    message: String,
    field: Option<String>,
}

fn create_detailed_error(code: Code, details: ErrorDetails) -> Status {
    let json = serde_json::to_string(&details).unwrap();
    
    let mut status = Status::new(code, details.message.clone());
    status.metadata_mut().insert(
        "error-details",
        json.parse().unwrap(),
    );
    
    status
}

// 使用示例
let error = create_detailed_error(
    Code::InvalidArgument,
    ErrorDetails {
        code: "INVALID_EMAIL".to_string(),
        message: "Email format is invalid".to_string(),
        field: Some("email".to_string()),
    },
);

return Err(error);
```

---

## 12. 负载均衡与服务发现

### 12.1 客户端负载均衡

使用 **Tower** 中间件实现客户端负载均衡：

```rust
// Cargo.toml
tower = { version = "0.5", features = ["balance", "discover"] }

// src/client/load_balancer.rs
use tonic::transport::{Channel, Endpoint};
use tower::discover::Change;
use tower::balance::p2c::Balance;
use std::sync::Arc;
use tokio::sync::mpsc;

pub async fn create_balanced_channel(endpoints: Vec<String>) -> Result<Channel> {
    let (tx, rx) = mpsc::channel(100);
    
    // 发送服务端点变更
    for (i, endpoint) in endpoints.into_iter().enumerate() {
        let channel = Endpoint::from_shared(endpoint)?
            .connect()
            .await?;
        
        tx.send(Change::Insert(i, channel)).await.unwrap();
    }
    
    // 创建 P2C 负载均衡器
    let balancer = Balance::new(rx);
    
    // 包装为 Channel
    Ok(Channel::balance_channel(balancer))
}

// 使用示例
let channel = create_balanced_channel(vec![
    "http://localhost:50051".to_string(),
    "http://localhost:50052".to_string(),
    "http://localhost:50053".to_string(),
]).await?;

let mut client = UserServiceClient::new(channel);
```

### 12.2 Consul 服务发现

```rust
// src/discovery/consul.rs
use consul::Client as ConsulClient;
use tonic::transport::Endpoint;
use anyhow::Result;

pub struct ConsulServiceDiscovery {
    client: ConsulClient,
    service_name: String,
}

impl ConsulServiceDiscovery {
    pub fn new(consul_addr: &str, service_name: &str) -> Self {
        let client = ConsulClient::new(consul_addr);
        
        Self {
            client,
            service_name: service_name.to_string(),
        }
    }
    
    pub async fn discover_endpoints(&self) -> Result<Vec<Endpoint>> {
        let services = self.client
            .health()
            .service(&self.service_name, None, true, None)
            .await?;
        
        let endpoints: Vec<Endpoint> = services
            .into_iter()
            .map(|service| {
                let addr = format!(
                    "http://{}:{}",
                    service.Service.Address,
                    service.Service.Port
                );
                Endpoint::from_shared(addr).unwrap()
            })
            .collect();
        
        Ok(endpoints)
    }
    
    pub async fn register_service(&self, port: u16) -> Result<()> {
        let registration = consul::ServiceRegistration {
            name: self.service_name.clone(),
            address: "127.0.0.1".to_string(),
            port,
            check: Some(consul::Check {
                grpc: format!("127.0.0.1:{}", port),
                interval: "10s".to_string(),
                timeout: "5s".to_string(),
            }),
            ..Default::default()
        };
        
        self.client.agent().register_service(registration).await?;
        
        Ok(())
    }
}

// Server 端注册
let discovery = ConsulServiceDiscovery::new("http://localhost:8500", "user-service");
discovery.register_service(50051).await?;

// Client 端发现
let endpoints = discovery.discover_endpoints().await?;
let channel = create_balanced_channel(endpoints).await?;
```

---

## 13. TLS/mTLS 安全通信

### 13.1 生成证书

```bash
# 生成 CA 证书
openssl req -x509 -newkey rsa:4096 -days 365 -nodes \
    -keyout ca-key.pem -out ca-cert.pem \
    -subj "/CN=My CA"

# 生成服务器私钥
openssl req -newkey rsa:4096 -nodes \
    -keyout server-key.pem -out server-req.pem \
    -subj "/CN=localhost"

# 签发服务器证书
openssl x509 -req -in server-req.pem -days 365 \
    -CA ca-cert.pem -CAkey ca-key.pem -CAcreateserial \
    -out server-cert.pem

# 生成客户端证书（mTLS）
openssl req -newkey rsa:4096 -nodes \
    -keyout client-key.pem -out client-req.pem \
    -subj "/CN=client"

openssl x509 -req -in client-req.pem -days 365 \
    -CA ca-cert.pem -CAkey ca-key.pem -CAcreateserial \
    -out client-cert.pem
```

### 13.2 Server 端 TLS 配置

```rust
// src/bin/server.rs
use tonic::transport::{Server, ServerTlsConfig, Identity, Certificate};
use std::fs;

#[tokio::main]
async fn main() -> Result<()> {
    let addr = "0.0.0.0:50051".parse()?;
    
    // 加载服务器证书
    let cert = fs::read_to_string("certs/server-cert.pem")?;
    let key = fs::read_to_string("certs/server-key.pem")?;
    let identity = Identity::from_pem(cert, key);
    
    // 加载 CA 证书（用于 mTLS）
    let ca_cert = fs::read_to_string("certs/ca-cert.pem")?;
    let ca_cert = Certificate::from_pem(ca_cert);
    
    // 配置 TLS
    let tls_config = ServerTlsConfig::new()
        .identity(identity)
        .client_ca_root(ca_cert); // 启用 mTLS
    
    // 启动服务器
    Server::builder()
        .tls_config(tls_config)?
        .add_service(user_service)
        .serve(addr)
        .await?;
    
    Ok(())
}
```

### 13.3 Client 端 TLS 配置

```rust
// src/bin/client.rs
use tonic::transport::{Channel, ClientTlsConfig, Certificate, Identity};
use std::fs;

#[tokio::main]
async fn main() -> Result<()> {
    // 加载 CA 证书
    let ca_cert = fs::read_to_string("certs/ca-cert.pem")?;
    let ca_cert = Certificate::from_pem(ca_cert);
    
    // 加载客户端证书（mTLS）
    let client_cert = fs::read_to_string("certs/client-cert.pem")?;
    let client_key = fs::read_to_string("certs/client-key.pem")?;
    let identity = Identity::from_pem(client_cert, client_key);
    
    // 配置 TLS
    let tls_config = ClientTlsConfig::new()
        .ca_certificate(ca_cert)
        .identity(identity) // 启用 mTLS
        .domain_name("localhost");
    
    // 连接服务器
    let channel = Channel::from_static("https://localhost:50051")
        .tls_config(tls_config)?
        .connect()
        .await?;
    
    let mut client = UserServiceClient::new(channel);
    
    Ok(())
}
```

---

## 14. 性能优化与最佳实践

### 14.1 连接池配置

```rust
// 配置连接参数
let channel = Channel::from_shared("http://localhost:50051")?
    // TCP keepalive
    .tcp_keepalive(Some(Duration::from_secs(60)))
    // 连接超时
    .connect_timeout(Duration::from_secs(5))
    // HTTP2 设置
    .http2_keep_alive_interval(Duration::from_secs(30))
    .http2_adaptive_window(true)
    // 初始流窗口大小
    .initial_stream_window_size(1024 * 1024) // 1MB
    // 初始连接窗口大小
    .initial_connection_window_size(1024 * 1024 * 10) // 10MB
    .connect()
    .await?;
```

### 14.2 消息压缩

```rust
// Server 端启用压缩
Server::builder()
    .add_service(
        UserServiceServer::new(service)
            .accept_compressed(CompressionEncoding::Gzip)
            .send_compressed(CompressionEncoding::Gzip)
    )
    .serve(addr)
    .await?;

// Client 端启用压缩
let mut client = UserServiceClient::new(channel)
    .accept_compressed(CompressionEncoding::Gzip)
    .send_compressed(CompressionEncoding::Gzip);
```

### 14.3 流式背压控制

```rust
// Server 端流式背压
async fn list_users(&self, request: Request<ListUsersRequest>) 
    -> Result<Response<Self::ListUsersStream>, Status> 
{
    let (tx, rx) = mpsc::channel(10); // 限制缓冲区大小
    
    tokio::spawn(async move {
        for user in users {
            // 如果接收方处理慢，send 会阻塞
            if tx.send(Ok(user)).await.is_err() {
                break;
            }
        }
    });
    
    Ok(Response::new(ReceiverStream::new(rx)))
}
```

### 14.4 超时与重试

```rust
// Client 端超时
use tower::timeout::Timeout;
use std::time::Duration;

let channel = Channel::from_shared("http://localhost:50051")?
    .timeout(Duration::from_secs(5))
    .connect()
    .await?;

// 重试策略
use tower::retry::Retry;

let retry_policy = tower::retry::Policy::retry(|error: &Status| {
    matches!(error.code(), Code::Unavailable | Code::DeadlineExceeded)
});

let channel = Channel::from_shared("http://localhost:50051")?
    .connect()
    .await?;

let service = Retry::new(retry_policy, channel);
```

### 14.5 批量处理优化

```rust
// 使用 Client Streaming 批量处理
pub async fn batch_process(items: Vec<Item>) -> Result<()> {
    const BATCH_SIZE: usize = 100;
    
    for chunk in items.chunks(BATCH_SIZE) {
        let stream = tokio_stream::iter(chunk.iter().cloned());
        client.batch_process(Request::new(stream)).await?;
    }
    
    Ok(())
}
```

### 14.6 Prometheus 指标导出

```rust
// Cargo.toml
prometheus = "0.13"
prometheus-static-metric = "0.5"

// src/metrics.rs
use prometheus::{IntCounter, HistogramVec, Registry};
use lazy_static::lazy_static;

lazy_static! {
    static ref RPC_REQUESTS_TOTAL: IntCounter = IntCounter::new(
        "grpc_requests_total",
        "Total number of gRPC requests"
    ).unwrap();
    
    static ref RPC_DURATION_SECONDS: HistogramVec = HistogramVec::new(
        prometheus::HistogramOpts::new(
            "grpc_request_duration_seconds",
            "gRPC request duration in seconds"
        ),
        &["service", "method", "status"]
    ).unwrap();
}

pub fn register_metrics(registry: &Registry) -> Result<()> {
    registry.register(Box::new(RPC_REQUESTS_TOTAL.clone()))?;
    registry.register(Box::new(RPC_DURATION_SECONDS.clone()))?;
    Ok(())
}

// 在 interceptor 中记录指标
pub fn metrics_interceptor(req: Request<()>) -> Result<Request<()>, Status> {
    RPC_REQUESTS_TOTAL.inc();
    
    let start = std::time::Instant::now();
    let method = req.uri().path().to_string();
    
    req.extensions_mut().insert(MetricsContext {
        method,
        start,
    });
    
    Ok(req)
}

struct MetricsContext {
    method: String,
    start: std::time::Instant,
}

impl Drop for MetricsContext {
    fn drop(&mut self) {
        let duration = self.start.elapsed().as_secs_f64();
        RPC_DURATION_SECONDS
            .with_label_values(&["UserService", &self.method, "ok"])
            .observe(duration);
    }
}
```

---

## 15. 部署与监控

### 15.1 Docker Compose 部署

```yaml
# docker-compose.yml
version: '3.8'

services:
  # gRPC 服务器
  user-service:
    build:
      context: .
      dockerfile: Dockerfile
    ports:
      - "50051:50051"
    environment:
      - RUST_LOG=info
      - OTEL_EXPORTER_OTLP_ENDPOINT=http://jaeger:4317
    depends_on:
      - postgres
      - jaeger
    networks:
      - grpc-network
  
  # PostgreSQL 数据库
  postgres:
    image: postgres:16
    environment:
      POSTGRES_DB: userdb
      POSTGRES_USER: admin
      POSTGRES_PASSWORD: admin123
    ports:
      - "5432:5432"
    volumes:
      - postgres-data:/var/lib/postgresql/data
    networks:
      - grpc-network
  
  # Jaeger 分布式追踪
  jaeger:
    image: jaegertracing/all-in-one:1.60
    ports:
      - "16686:16686"  # UI
      - "4317:4317"    # OTLP gRPC
      - "4318:4318"    # OTLP HTTP
    environment:
      - COLLECTOR_OTLP_ENABLED=true
    networks:
      - grpc-network
  
  # Prometheus 监控
  prometheus:
    image: prom/prometheus:v2.54.0
    ports:
      - "9090:9090"
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml
      - prometheus-data:/prometheus
    command:
      - '--config.file=/etc/prometheus/prometheus.yml'
      - '--storage.tsdb.path=/prometheus'
    networks:
      - grpc-network
  
  # Grafana 可视化
  grafana:
    image: grafana/grafana:11.2.0
    ports:
      - "3000:3000"
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=admin
    volumes:
      - grafana-data:/var/lib/grafana
    depends_on:
      - prometheus
    networks:
      - grpc-network

volumes:
  postgres-data:
  prometheus-data:
  grafana-data:

networks:
  grpc-network:
    driver: bridge
```

### 15.2 Dockerfile

```dockerfile
# Dockerfile
FROM rust:1.90 as builder

WORKDIR /app

# 复制依赖文件
COPY Cargo.toml Cargo.lock ./
COPY proto ./proto
COPY build.rs ./

# 预构建依赖
RUN mkdir src && echo "fn main() {}" > src/main.rs
RUN cargo build --release
RUN rm -rf src

# 复制源代码
COPY src ./src

# 构建应用
RUN cargo build --release

# 运行时镜像
FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y \
    ca-certificates \
    libssl3 \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app

COPY --from=builder /app/target/release/server /app/server

EXPOSE 50051

CMD ["/app/server"]
```

### 15.3 Prometheus 配置

```yaml
# prometheus.yml
global:
  scrape_interval: 15s
  evaluation_interval: 15s

scrape_configs:
  - job_name: 'user-service'
    static_configs:
      - targets: ['user-service:9090']
    metric_path: '/metrics'
```

### 15.4 Grafana Dashboard

导入 **gRPC Dashboard** JSON：

```json
{
  "dashboard": {
    "title": "gRPC Service Metrics",
    "panels": [
      {
        "title": "Request Rate",
        "targets": [
          {
            "expr": "rate(grpc_requests_total[5m])"
          }
        ]
      },
      {
        "title": "Request Duration (p95)",
        "targets": [
          {
            "expr": "histogram_quantile(0.95, rate(grpc_request_duration_seconds_bucket[5m]))"
          }
        ]
      },
      {
        "title": "Error Rate",
        "targets": [
          {
            "expr": "rate(grpc_requests_total{status!=\"ok\"}[5m])"
          }
        ]
      }
    ]
  }
}
```

---

## 16. 国际标准对齐

### 16.1 gRPC 官方标准

本文档完全对齐 **gRPC Official Documentation**：

- **四种 RPC 模式**: Unary, Server Streaming, Client Streaming, Bidirectional Streaming
- **状态码**: 严格遵循 gRPC Status Code 定义
- **元数据**: 使用 Metadata 传递跨层信息
- **拦截器**: 实现 Interceptor 模式进行横切关注点处理
- **健康检查**: 使用 `grpc.health.v1.Health` 标准服务
- **反射**: 使用 `grpc.reflection.v1alpha.ServerReflection` 标准服务

### 16.2 CNCF OpenTelemetry

对齐 **OpenTelemetry Specification v1.38.0**：

- **语义约定**: 使用 `opentelemetry-semantic-conventions` 库
- **分布式追踪**: 完整的 Trace Context 传播
- **指标**: Prometheus 格式导出
- **资源属性**: `service.name`, `service.version`, `deployment.environment`
- **RPC 属性**: `rpc.service`, `rpc.method`, `rpc.system`, `net.peer.name`, `net.peer.port`

### 16.3 Google Cloud Best Practices

对齐 **Google Cloud gRPC Best Practices**：

- **连接管理**: 复用连接，避免频繁创建/销毁
- **负载均衡**: 客户端负载均衡（P2C, Round Robin）
- **错误处理**: Rich Error Model，结构化错误信息
- **安全通信**: TLS/mTLS 加密
- **监控**: 指标导出到 Prometheus

### 16.4 Rust 1.90 特性

本文档充分利用 **Rust 1.90** 最新特性：

- **Async/Await**: 所有 RPC 方法使用 `async fn`
- **Trait Bounds**: 使用 `#[tonic::async_trait]` 简化异步 trait 实现
- **Error Handling**: `thiserror` + `anyhow` 现代错误处理
- **Type Safety**: 利用 Rust 类型系统在编译时保证正确性

---

## 17. 总结

### 17.1 核心要点

| 维度 | 关键技术 | 生产实践 |
|------|----------|----------|
| **协议** | gRPC + HTTP/2 + Protobuf | 二进制高效传输 |
| **框架** | Tonic 0.12 + Tokio 1.40 | 纯 Rust 异步实现 |
| **可观测性** | OpenTelemetry 0.31 | OTLP 分布式追踪 |
| **安全** | TLS/mTLS | 双向认证加密 |
| **弹性** | 重试 + 超时 + 限流 | Tower 中间件 |
| **部署** | Docker Compose | Jaeger + Prometheus + Grafana |

### 17.2 生产检查清单

- [ ] **Proto 定义**: 使用语义化版本控制（如 `user.v1`, `user.v2`）
- [ ] **错误处理**: 所有错误映射到合适的 gRPC Status Code
- [ ] **健康检查**: 实现 `grpc.health.v1.Health` 服务
- [ ] **反射服务**: 启用 `grpc.reflection` 便于调试
- [ ] **分布式追踪**: 集成 OpenTelemetry OTLP Exporter
- [ ] **指标监控**: 导出 Prometheus 指标
- [ ] **TLS/mTLS**: 生产环境启用加密通信
- [ ] **负载均衡**: 使用客户端负载均衡或服务网格
- [ ] **限流降级**: 实现 Rate Limiting 和 Circuit Breaker
- [ ] **优雅关闭**: 正确处理 Ctrl+C 信号，优雅关闭连接

### 17.3 性能优化建议

1. **连接复用**: 客户端使用长连接，避免频繁建立 TCP 连接
2. **批量处理**: 使用 Client Streaming 或 Bidirectional Streaming 批量处理数据
3. **消息压缩**: 启用 Gzip/Zstd 压缩减少网络传输
4. **流式背压**: 合理设置 Channel Buffer 大小，防止内存溢出
5. **超时控制**: 为所有 RPC 设置合理的超时时间
6. **预热连接**: 启动时预先建立连接，避免冷启动延迟

### 17.4 学习路径

1. **基础**: 掌握 Protobuf 语法和 gRPC 四种 RPC 模式
2. **进阶**: 实现拦截器、健康检查、反射服务
3. **生产**: 集成 TLS、负载均衡、服务发现、分布式追踪
4. **优化**: 性能调优、监控告警、故障排查

---

## 附录 A: 完整项目结构

```text
tonic-otlp-example/
├── Cargo.toml
├── Cargo.lock
├── build.rs
├── proto/
│   ├── user_service.proto
│   └── order_service.proto
├── src/
│   ├── lib.rs
│   ├── bin/
│   │   ├── server.rs
│   │   └── client.rs
│   ├── services/
│   │   ├── mod.rs
│   │   ├── user_service.rs
│   │   └── order_service.rs
│   ├── client/
│   │   ├── mod.rs
│   │   └── user_client.rs
│   ├── interceptors/
│   │   ├── mod.rs
│   │   ├── auth.rs
│   │   ├── logging.rs
│   │   └── rate_limit.rs
│   ├── telemetry/
│   │   ├── mod.rs
│   │   └── otlp.rs
│   ├── errors.rs
│   └── metrics.rs
├── certs/
│   ├── ca-cert.pem
│   ├── ca-key.pem
│   ├── server-cert.pem
│   ├── server-key.pem
│   ├── client-cert.pem
│   └── client-key.pem
├── docker-compose.yml
├── Dockerfile
├── prometheus.yml
└── README.md
```

---

## 附录 B: 参考资源

### 官方文档

- **gRPC**: <https://grpc.io/docs/>
- **Tonic**: <https://docs.rs/tonic/>
- **Protobuf**: <https://protobuf.dev/>
- **OpenTelemetry**: <https://opentelemetry.io/docs/>

### 标准规范

- **gRPC Status Code**: <https://grpc.github.io/grpc/core/md_doc_statuscodes.html>
- **OTLP Specification**: <https://opentelemetry.io/docs/specs/otlp/>
- **HTTP/2 RFC**: <https://datatracker.ietf.org/doc/html/rfc7540>

### 最佳实践

- **Google Cloud gRPC Best Practices**: <https://cloud.google.com/apis/design/errors>
- **Microsoft gRPC for WCF Developers**: <https://learn.microsoft.com/en-us/dotnet/architecture/grpc-for-wcf-developers/>
- **CNCF Service Mesh Patterns**: <https://www.cncf.io/blog/2021/07/19/understanding-service-mesh-patterns/>

---

**文档完成**。本文档提供了 Tonic gRPC 在 Rust 1.90 环境下的完整实现指南，涵盖从 Proto 定义到生产部署的全流程，并深度集成 OpenTelemetry OTLP 分布式追踪，完全对齐国际标准和最佳实践。
