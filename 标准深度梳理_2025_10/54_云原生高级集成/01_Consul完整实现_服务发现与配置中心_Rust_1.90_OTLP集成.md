# Consul 完整实现：服务发现与配置中心（Rust 1.90 + OTLP 集成）

## 目录

- [Consul 完整实现：服务发现与配置中心（Rust 1.90 + OTLP 集成）](#consul-完整实现服务发现与配置中心rust-190--otlp-集成)
  - [目录](#目录)
  - [1. Consul 概述](#1-consul-概述)
    - [1.1 核心特性](#11-核心特性)
    - [1.2 架构组件](#12-架构组件)
    - [1.3 Consul vs 其他方案](#13-consul-vs-其他方案)
  - [2. 国际标准对齐](#2-国际标准对齐)
    - [2.1 网络协议标准](#21-网络协议标准)
    - [2.2 分布式系统标准](#22-分布式系统标准)
    - [2.3 安全标准](#23-安全标准)
  - [3. 项目初始化](#3-项目初始化)
    - [3.1 依赖配置](#31-依赖配置)
    - [3.2 Consul 部署](#32-consul-部署)
    - [3.3 项目结构](#33-项目结构)
  - [4. 服务注册与发现](#4-服务注册与发现)
    - [4.1 服务注册](#41-服务注册)
    - [4.2 服务发现](#42-服务发现)
    - [4.3 健康检查](#43-健康检查)
  - [5. 配置管理](#5-配置管理)
    - [5.1 KV Store 读写](#51-kv-store-读写)
    - [5.2 动态配置更新](#52-动态配置更新)
    - [5.3 配置版本管理](#53-配置版本管理)
  - [6. 分布式锁](#6-分布式锁)
    - [6.1 Session 管理](#61-session-管理)
    - [6.2 Lock 实现](#62-lock-实现)
    - [6.3 Leader Election](#63-leader-election)
  - [7. Service Mesh 集成](#7-service-mesh-集成)
    - [7.1 Consul Connect](#71-consul-connect)
    - [7.2 Sidecar Proxy](#72-sidecar-proxy)
    - [7.3 Intentions (访问控制)](#73-intentions-访问控制)
  - [8. 多数据中心](#8-多数据中心)
    - [8.1 WAN 联邦](#81-wan-联邦)
    - [8.2 跨数据中心服务发现](#82-跨数据中心服务发现)
    - [8.3 网关配置](#83-网关配置)
  - [9. OTLP 集成](#9-otlp-集成)
    - [9.1 服务注册追踪](#91-服务注册追踪)
    - [9.2 服务调用链追踪](#92-服务调用链追踪)
    - [9.3 健康检查监控](#93-健康检查监控)
  - [10. 生产最佳实践](#10-生产最佳实践)
    - [10.1 高可用部署](#101-高可用部署)
    - [10.2 备份与恢复](#102-备份与恢复)
    - [10.3 性能优化](#103-性能优化)
  - [11. 测试策略](#11-测试策略)
    - [11.1 单元测试](#111-单元测试)
    - [11.2 集成测试](#112-集成测试)
    - [11.3 混沌测试](#113-混沌测试)
  - [12. 生产部署](#12-生产部署)
    - [12.1 Kubernetes 部署](#121-kubernetes-部署)
    - [12.2 Docker Compose 部署](#122-docker-compose-部署)
    - [12.3 监控告警](#123-监控告警)
  - [总结](#总结)
    - [核心优势](#核心优势)
    - [国际标准对齐](#国际标准对齐)
    - [适用场景](#适用场景)

---

## 1. Consul 概述

**Consul** 是 HashiCorp 开发的分布式服务网格解决方案，提供 **服务发现、配置管理、健康检查、分布式锁** 等核心功能。

### 1.1 核心特性

| 特性 | 说明 | 技术实现 |
|------|------|----------|
| **服务发现** | 自动注册与发现微服务 | DNS + HTTP API |
| **健康检查** | 多种健康检查机制 | HTTP, TCP, gRPC, Script |
| **KV Store** | 分布式键值存储 | Raft 一致性协议 |
| **多数据中心** | WAN 联邦支持 | Gossip 协议 |
| **Service Mesh** | Consul Connect (mTLS) | Envoy Proxy |
| **分布式锁** | Session + Lock 机制 | Raft 协议 |

### 1.2 架构组件

```text
┌─────────────────────────────────────────────┐
│           Consul Architecture               │
└─────────────────────────────────────────────┘

Client Layer:
┌─────────────┐  ┌─────────────┐  ┌─────────────┐
│   Service   │  │   Service   │  │   Service   │
│      A      │  │      B      │  │      C      │
└──────┬──────┘  └──────┬──────┘  └──────┬──────┘
       │                 │                 │
       │ Register/Query  │                 │
       └─────────┬───────┴─────────────────┘
                 │
┌────────────────▼─────────────────────────────┐
│         Consul Agent (Client)                │
│  - Service Registration                      │
│  - Health Checks                             │
│  - DNS Interface                             │
└────────────────┬─────────────────────────────┘
                 │ Gossip (LAN)
┌────────────────▼─────────────────────────────┐
│         Consul Servers (Cluster)             │
│  ┌────────────┐  ┌────────────┐             │
│  │   Leader   │  │  Follower  │             │
│  │  (Raft)    │◄─┤  (Raft)    │             │
│  └────────────┘  └────────────┘             │
│  - Service Catalog                           │
│  - KV Store                                  │
│  - Health Checks                             │
│  - ACL / Policies                            │
└──────────────────────────────────────────────┘
                 │ WAN Gossip
┌────────────────▼─────────────────────────────┐
│         Other Datacenters                    │
└──────────────────────────────────────────────┘
```

### 1.3 Consul vs 其他方案

| 维度 | Consul | etcd | Zookeeper | Eureka |
|------|--------|------|-----------|--------|
| **服务发现** | DNS + HTTP | HTTP | TCP | HTTP |
| **一致性协议** | Raft | Raft | ZAB | AP (最终一致性) |
| **健康检查** | 内置多种 | 外部实现 | 外部实现 | 内置 |
| **多数据中心** | 原生支持 | 需要外部工具 | 需要外部工具 | 不支持 |
| **Service Mesh** | Consul Connect | 不支持 | 不支持 | 不支持 |
| **KV Store** | 内置 | 核心功能 | 内置 | 不支持 |
| **成熟度** | 高 (2014+) | 高 (2013+) | 高 (2007+) | 中 (2015+) |

---

## 2. 国际标准对齐

### 2.1 网络协议标准

| 标准 | 版本 | 说明 |
|------|------|------|
| **HTTP/1.1** | RFC 7230-7235 | REST API |
| **HTTP/2** | RFC 7540 | gRPC 健康检查 |
| **DNS** | RFC 1035 | 服务发现 (DNS 接口) |
| **Gossip Protocol** | SWIM | 节点发现与故障检测 |
| **mTLS** | TLS 1.3 | Consul Connect |

### 2.2 分布式系统标准

| 标准 | 说明 |
|------|------|
| **Raft 一致性协议** | Consul Server 集群 |
| **CAP Theorem** | CP (一致性 + 分区容错性) |
| **Eventual Consistency** | Gossip 协议 (LAN/WAN) |

### 2.3 安全标准

| 标准 | 说明 |
|------|------|
| **ACL (Access Control List)** | 基于令牌的访问控制 |
| **mTLS (Mutual TLS)** | Service Mesh 双向认证 |
| **Vault Integration** | 密钥管理 |

---

## 3. 项目初始化

### 3.1 依赖配置

**Cargo.toml**:

```toml
[package]
name = "consul-service"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# Consul 客户端
consul = "0.5"

# HTTP 客户端
reqwest = { version = "0.12", features = ["json"] }

# 异步运行时
tokio = { version = "1", features = ["full"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# Web 框架
axum = "0.7"
tower = "0.4"

# 日志
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }

# OpenTelemetry
opentelemetry = "0.25"
opentelemetry-otlp = "0.25"
tracing-opentelemetry = "0.26"
opentelemetry-sdk = "0.25"

# 错误处理
anyhow = "1.0"
thiserror = "1.0"

# 配置
config = "0.14"

# UUID
uuid = { version = "1.0", features = ["v4", "serde"] }
```

### 3.2 Consul 部署

**docker-compose.yml**:

```yaml
version: '3.9'

services:
  # Consul Server (3-node cluster)
  consul-server-1:
    image: hashicorp/consul:1.18
    container_name: consul-server-1
    command: >
      agent -server -bootstrap-expect=3
      -ui -client=0.0.0.0
      -bind=0.0.0.0
      -datacenter=dc1
      -node=consul-server-1
      -retry-join=consul-server-2
      -retry-join=consul-server-3
    ports:
      - "8500:8500"   # HTTP API + UI
      - "8600:8600/udp"   # DNS
    volumes:
      - consul-server-1-data:/consul/data
    networks:
      - consul-net

  consul-server-2:
    image: hashicorp/consul:1.18
    container_name: consul-server-2
    command: >
      agent -server -bootstrap-expect=3
      -bind=0.0.0.0
      -datacenter=dc1
      -node=consul-server-2
      -retry-join=consul-server-1
      -retry-join=consul-server-3
    volumes:
      - consul-server-2-data:/consul/data
    networks:
      - consul-net

  consul-server-3:
    image: hashicorp/consul:1.18
    container_name: consul-server-3
    command: >
      agent -server -bootstrap-expect=3
      -bind=0.0.0.0
      -datacenter=dc1
      -node=consul-server-3
      -retry-join=consul-server-1
      -retry-join=consul-server-2
    volumes:
      - consul-server-3-data:/consul/data
    networks:
      - consul-net

  # Consul Client
  consul-client:
    image: hashicorp/consul:1.18
    container_name: consul-client
    command: >
      agent -client=0.0.0.0
      -bind=0.0.0.0
      -datacenter=dc1
      -node=consul-client
      -retry-join=consul-server-1
    networks:
      - consul-net

volumes:
  consul-server-1-data:
  consul-server-2-data:
  consul-server-3-data:

networks:
  consul-net:
    driver: bridge
```

### 3.3 项目结构

```text
consul-service/
├── Cargo.toml
├── src/
│   ├── main.rs                 # 入口
│   ├── consul/
│   │   ├── mod.rs
│   │   ├── client.rs           # Consul 客户端封装
│   │   ├── service.rs          # 服务注册/发现
│   │   ├── health.rs           # 健康检查
│   │   ├── kv.rs               # KV Store
│   │   └── lock.rs             # 分布式锁
│   ├── config/
│   │   ├── mod.rs
│   │   └── settings.rs         # 配置管理
│   ├── handlers/
│   │   ├── mod.rs
│   │   └── api.rs              # HTTP API
│   └── telemetry/
│       ├── mod.rs
│       └── otlp.rs             # OpenTelemetry
├── config/
│   └── default.toml
└── docker-compose.yml
```

---

## 4. 服务注册与发现

### 4.1 服务注册

**src/consul/service.rs**:

```rust
use consul::Client;
use consul::catalog::ServiceRegistration;
use serde::{Deserialize, Serialize};
use anyhow::Result;
use tracing::{info, instrument};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceConfig {
    pub id: String,
    pub name: String,
    pub address: String,
    pub port: u16,
    pub tags: Vec<String>,
    pub meta: std::collections::HashMap<String, String>,
}

/// Consul 服务管理器
pub struct ConsulServiceManager {
    client: Client,
    config: ServiceConfig,
}

impl ConsulServiceManager {
    pub fn new(consul_addr: &str, config: ServiceConfig) -> Result<Self> {
        let client = Client::new(consul_addr)?;
        Ok(Self { client, config })
    }

    /// 注册服务
    #[instrument(skip(self))]
    pub async fn register(&self) -> Result<()> {
        info!(
            service_id = %self.config.id,
            service_name = %self.config.name,
            address = %self.config.address,
            port = %self.config.port,
            "Registering service with Consul"
        );

        let registration = ServiceRegistration {
            id: Some(self.config.id.clone()),
            name: self.config.name.clone(),
            address: Some(self.config.address.clone()),
            port: Some(self.config.port),
            tags: Some(self.config.tags.clone()),
            meta: Some(self.config.meta.clone()),
            check: Some(consul::catalog::ServiceCheck {
                http: Some(format!(
                    "http://{}:{}/health",
                    self.config.address, self.config.port
                )),
                interval: Some("10s".to_string()),
                timeout: Some("5s".to_string()),
                deregister_critical_service_after: Some("30s".to_string()),
                ..Default::default()
            }),
            ..Default::default()
        };

        self.client.agent().register_service(&registration).await?;

        info!(
            service_id = %self.config.id,
            "Service registered successfully"
        );

        Ok(())
    }

    /// 注销服务
    #[instrument(skip(self))]
    pub async fn deregister(&self) -> Result<()> {
        info!(service_id = %self.config.id, "Deregistering service");

        self.client
            .agent()
            .deregister_service(&self.config.id)
            .await?;

        info!(service_id = %self.config.id, "Service deregistered");

        Ok(())
    }
}
```

### 4.2 服务发现

**服务查询**:

```rust
use consul::health::HealthService;

/// 服务发现
pub struct ServiceDiscovery {
    client: Client,
}

impl ServiceDiscovery {
    pub fn new(consul_addr: &str) -> Result<Self> {
        let client = Client::new(consul_addr)?;
        Ok(Self { client })
    }

    /// 查询健康的服务实例
    #[instrument(skip(self))]
    pub async fn get_healthy_services(
        &self,
        service_name: &str,
    ) -> Result<Vec<ServiceInstance>> {
        info!(service_name = %service_name, "Discovering healthy services");

        let services = self
            .client
            .health()
            .get_service(service_name, None, true, None)
            .await?;

        let instances: Vec<ServiceInstance> = services
            .iter()
            .map(|svc| ServiceInstance {
                id: svc.service.id.clone(),
                name: svc.service.service.clone(),
                address: svc.service.address.clone(),
                port: svc.service.port,
                tags: svc.service.tags.clone().unwrap_or_default(),
                meta: svc.service.meta.clone().unwrap_or_default(),
            })
            .collect();

        info!(
            service_name = %service_name,
            instances_count = %instances.len(),
            "Healthy services discovered"
        );

        Ok(instances)
    }

    /// 负载均衡选择实例 (轮询)
    pub fn select_instance(&self, instances: &[ServiceInstance]) -> Option<&ServiceInstance> {
        if instances.is_empty() {
            return None;
        }

        // 简单轮询 (生产环境可使用更复杂的策略)
        let index = (std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs() as usize)
            % instances.len();

        Some(&instances[index])
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceInstance {
    pub id: String,
    pub name: String,
    pub address: String,
    pub port: u16,
    pub tags: Vec<String>,
    pub meta: std::collections::HashMap<String, String>,
}
```

### 4.3 健康检查

**HTTP 健康检查端点**:

```rust
use axum::{http::StatusCode, response::IntoResponse, Json, Router, routing::get};
use serde_json::json;

/// 健康检查路由
pub fn health_routes() -> Router {
    Router::new()
        .route("/health", get(health_check))
        .route("/health/ready", get(readiness_check))
        .route("/health/live", get(liveness_check))
}

/// 健康检查 (Consul 使用)
async fn health_check() -> impl IntoResponse {
    (StatusCode::OK, Json(json!({ "status": "healthy" })))
}

/// 就绪检查
async fn readiness_check() -> impl IntoResponse {
    // 检查依赖服务 (数据库, 缓存等)
    let is_ready = check_dependencies().await;

    if is_ready {
        (StatusCode::OK, Json(json!({ "status": "ready" })))
    } else {
        (
            StatusCode::SERVICE_UNAVAILABLE,
            Json(json!({ "status": "not ready" })),
        )
    }
}

/// 存活检查
async fn liveness_check() -> impl IntoResponse {
    (StatusCode::OK, Json(json!({ "status": "alive" })))
}

async fn check_dependencies() -> bool {
    // 实际生产环境中检查数据库连接等
    true
}
```

---

## 5. 配置管理

### 5.1 KV Store 读写

**src/consul/kv.rs**:

```rust
use consul::Client;
use anyhow::Result;
use tracing::{info, instrument};

pub struct ConsulKVStore {
    client: Client,
}

impl ConsulKVStore {
    pub fn new(consul_addr: &str) -> Result<Self> {
        let client = Client::new(consul_addr)?;
        Ok(Self { client })
    }

    /// 写入配置
    #[instrument(skip(self, value))]
    pub async fn put(&self, key: &str, value: &[u8]) -> Result<()> {
        info!(key = %key, "Writing to Consul KV");

        self.client.kv().put(key, value, None).await?;

        info!(key = %key, "Value written successfully");

        Ok(())
    }

    /// 读取配置
    #[instrument(skip(self))]
    pub async fn get(&self, key: &str) -> Result<Option<Vec<u8>>> {
        info!(key = %key, "Reading from Consul KV");

        let response = self.client.kv().get(key, None).await?;

        if let Some(kv) = response {
            info!(key = %key, "Value retrieved");
            Ok(Some(kv.value))
        } else {
            info!(key = %key, "Key not found");
            Ok(None)
        }
    }

    /// 删除配置
    #[instrument(skip(self))]
    pub async fn delete(&self, key: &str) -> Result<()> {
        info!(key = %key, "Deleting from Consul KV");

        self.client.kv().delete(key, None).await?;

        info!(key = %key, "Value deleted");

        Ok(())
    }

    /// 列出键
    #[instrument(skip(self))]
    pub async fn list(&self, prefix: &str) -> Result<Vec<String>> {
        info!(prefix = %prefix, "Listing keys with prefix");

        let keys = self.client.kv().list(prefix, None).await?;

        let key_list: Vec<String> = keys.iter().map(|kv| kv.key.clone()).collect();

        info!(
            prefix = %prefix,
            count = %key_list.len(),
            "Keys retrieved"
        );

        Ok(key_list)
    }
}
```

### 5.2 动态配置更新

**配置监听**:

```rust
use tokio::time::{interval, Duration};

pub struct ConfigWatcher {
    kv_store: ConsulKVStore,
    key: String,
    last_value: Option<Vec<u8>>,
}

impl ConfigWatcher {
    pub fn new(kv_store: ConsulKVStore, key: String) -> Self {
        Self {
            kv_store,
            key,
            last_value: None,
        }
    }

    /// 持续监听配置变化
    #[instrument(skip(self))]
    pub async fn watch<F>(&mut self, mut on_change: F) -> Result<()>
    where
        F: FnMut(&[u8]) -> Result<()>,
    {
        let mut ticker = interval(Duration::from_secs(5));

        loop {
            ticker.tick().await;

            match self.kv_store.get(&self.key).await? {
                Some(value) => {
                    if self.last_value.as_ref() != Some(&value) {
                        info!(key = %self.key, "Config changed, applying update");

                        on_change(&value)?;

                        self.last_value = Some(value);
                    }
                }
                None => {
                    if self.last_value.is_some() {
                        info!(key = %self.key, "Config deleted");
                        self.last_value = None;
                    }
                }
            }
        }
    }
}
```

### 5.3 配置版本管理

**CAS (Compare-And-Swap)**:

```rust
impl ConsulKVStore {
    /// 原子更新 (CAS)
    #[instrument(skip(self, value))]
    pub async fn cas(
        &self,
        key: &str,
        value: &[u8],
        expected_index: u64,
    ) -> Result<bool> {
        info!(
            key = %key,
            expected_index = %expected_index,
            "Performing CAS operation"
        );

        let success = self
            .client
            .kv()
            .put_with_index(key, value, expected_index, None)
            .await?;

        if success {
            info!(key = %key, "CAS succeeded");
        } else {
            info!(key = %key, "CAS failed (index mismatch)");
        }

        Ok(success)
    }
}
```

---

## 6. 分布式锁

### 6.1 Session 管理

**src/consul/lock.rs**:

```rust
use consul::session::{SessionCreate, SessionBehavior};
use std::time::Duration;

pub struct ConsulSession {
    client: Client,
    session_id: Option<String>,
}

impl ConsulSession {
    pub fn new(consul_addr: &str) -> Result<Self> {
        let client = Client::new(consul_addr)?;
        Ok(Self {
            client,
            session_id: None,
        })
    }

    /// 创建 Session
    #[instrument(skip(self))]
    pub async fn create(&mut self, ttl: Duration) -> Result<String> {
        info!(ttl_secs = %ttl.as_secs(), "Creating Consul session");

        let session = SessionCreate {
            lock_delay: Some(Duration::from_secs(15)),
            ttl: Some(ttl),
            behavior: Some(SessionBehavior::Delete),
            ..Default::default()
        };

        let session_id = self.client.session().create(&session, None).await?;

        info!(session_id = %session_id, "Session created");

        self.session_id = Some(session_id.clone());

        Ok(session_id)
    }

    /// 续期 Session
    #[instrument(skip(self))]
    pub async fn renew(&self) -> Result<()> {
        if let Some(session_id) = &self.session_id {
            info!(session_id = %session_id, "Renewing session");

            self.client.session().renew(session_id, None).await?;

            info!(session_id = %session_id, "Session renewed");
        }

        Ok(())
    }

    /// 销毁 Session
    #[instrument(skip(self))]
    pub async fn destroy(&mut self) -> Result<()> {
        if let Some(session_id) = self.session_id.take() {
            info!(session_id = %session_id, "Destroying session");

            self.client.session().destroy(&session_id, None).await?;

            info!(session_id = %session_id, "Session destroyed");
        }

        Ok(())
    }
}
```

### 6.2 Lock 实现

**分布式锁**:

```rust
pub struct ConsulLock {
    kv_store: ConsulKVStore,
    session: ConsulSession,
    key: String,
}

impl ConsulLock {
    pub async fn new(consul_addr: &str, key: String) -> Result<Self> {
        let kv_store = ConsulKVStore::new(consul_addr)?;
        let mut session = ConsulSession::new(consul_addr)?;

        // 创建 Session (30s TTL)
        session.create(Duration::from_secs(30)).await?;

        Ok(Self {
            kv_store,
            session,
            key,
        })
    }

    /// 获取锁
    #[instrument(skip(self))]
    pub async fn acquire(&self) -> Result<bool> {
        info!(key = %self.key, "Attempting to acquire lock");

        let session_id = self
            .session
            .session_id
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("Session not created"))?;

        let acquired = self
            .kv_store
            .client
            .kv()
            .acquire(&self.key, b"", session_id, None)
            .await?;

        if acquired {
            info!(key = %self.key, "Lock acquired");
        } else {
            info!(key = %self.key, "Lock acquisition failed");
        }

        Ok(acquired)
    }

    /// 释放锁
    #[instrument(skip(self))]
    pub async fn release(&self) -> Result<bool> {
        info!(key = %self.key, "Releasing lock");

        let session_id = self
            .session
            .session_id
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("Session not created"))?;

        let released = self
            .kv_store
            .client
            .kv()
            .release(&self.key, session_id, None)
            .await?;

        if released {
            info!(key = %self.key, "Lock released");
        } else {
            info!(key = %self.key, "Lock release failed");
        }

        Ok(released)
    }

    /// 自动续期锁
    pub async fn with_lock<F, Fut, T>(&mut self, f: F) -> Result<T>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<T>>,
    {
        // 自动续期任务
        let session = self.session.clone();
        let renew_task = tokio::spawn(async move {
            let mut ticker = interval(Duration::from_secs(10));
            loop {
                ticker.tick().await;
                if let Err(e) = session.renew().await {
                    eprintln!("Failed to renew session: {}", e);
                    break;
                }
            }
        });

        // 执行业务逻辑
        let result = f().await;

        // 停止续期任务
        renew_task.abort();

        result
    }
}
```

### 6.3 Leader Election

**Leader 选举**:

```rust
pub struct LeaderElection {
    lock: ConsulLock,
}

impl LeaderElection {
    pub async fn new(consul_addr: &str, election_key: String) -> Result<Self> {
        let lock = ConsulLock::new(consul_addr, election_key).await?;
        Ok(Self { lock })
    }

    /// 竞选 Leader
    #[instrument(skip(self))]
    pub async fn campaign(&mut self) -> Result<bool> {
        info!("Campaigning for leadership");

        let is_leader = self.lock.acquire().await?;

        if is_leader {
            info!("Became leader");

            // 持续续期
            tokio::spawn(async move {
                let mut ticker = interval(Duration::from_secs(10));
                loop {
                    ticker.tick().await;
                    // 续期逻辑
                }
            });
        } else {
            info!("Lost leadership election");
        }

        Ok(is_leader)
    }

    /// 放弃 Leader
    #[instrument(skip(self))]
    pub async fn resign(&self) -> Result<()> {
        info!("Resigning from leadership");

        self.lock.release().await?;

        info!("Leadership resigned");

        Ok(())
    }
}
```

---

## 7. Service Mesh 集成

### 7.1 Consul Connect

**启用 Connect**:

```yaml
# Consul 配置
connect:
  enabled: true
```

**服务注册 (Connect-aware)**:

```rust
let registration = ServiceRegistration {
    id: Some(service_id.clone()),
    name: service_name.clone(),
    address: Some(service_address.clone()),
    port: Some(service_port),
    connect: Some(consul::catalog::ServiceConnect {
        sidecar_service: Some(consul::catalog::SidecarService {
            port: Some(sidecar_port),
            proxy: Some(consul::catalog::ServiceProxy {
                upstreams: Some(vec![consul::catalog::Upstream {
                    destination_name: "backend-service".to_string(),
                    local_bind_port: 9191,
                    ..Default::default()
                }]),
                ..Default::default()
            }),
            ..Default::default()
        }),
        ..Default::default()
    }),
    ..Default::default()
};
```

### 7.2 Sidecar Proxy

**Envoy 配置**:

```bash
# 启动 Envoy Sidecar
consul connect envoy -sidecar-for=my-service \
    -admin-bind=127.0.0.1:19000 \
    -http-addr=http://localhost:8500
```

### 7.3 Intentions (访问控制)

**配置 Intentions**:

```bash
# 允许 web-service 访问 api-service
consul intention create web-service api-service

# 拒绝 guest-service 访问 admin-service
consul intention create -deny guest-service admin-service

# 查看 Intentions
consul intention list
```

---

## 8. 多数据中心

### 8.1 WAN 联邦

**配置 WAN Join**:

```yaml
# dc1 Consul Server
datacenter: dc1
retry_join_wan:
  - "consul-server-dc2:8302"

# dc2 Consul Server
datacenter: dc2
retry_join_wan:
  - "consul-server-dc1:8302"
```

### 8.2 跨数据中心服务发现

**查询远程数据中心服务**:

```rust
/// 跨数据中心服务发现
pub async fn get_services_in_datacenter(
    &self,
    service_name: &str,
    datacenter: &str,
) -> Result<Vec<ServiceInstance>> {
    info!(
        service_name = %service_name,
        datacenter = %datacenter,
        "Querying service in remote datacenter"
    );

    let query_options = Some(consul::QueryOptions {
        datacenter: Some(datacenter.to_string()),
        ..Default::default()
    });

    let services = self
        .client
        .health()
        .get_service(service_name, None, true, query_options)
        .await?;

    let instances: Vec<ServiceInstance> = services
        .iter()
        .map(|svc| ServiceInstance::from(svc))
        .collect();

    Ok(instances)
}
```

### 8.3 网关配置

**Mesh Gateway**:

```hcl
Kind = "mesh-gateway"
Name = "mesh-gateway"

Proxy {
  Config {
    bind_address = "0.0.0.0:443"
  }
}
```

---

## 9. OTLP 集成

### 9.1 服务注册追踪

**src/telemetry/otlp.rs**:

```rust
use opentelemetry::{global, trace::TracerProvider, KeyValue};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{runtime, trace::Config, Resource};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};

pub fn init_telemetry(service_name: &str) -> anyhow::Result<()> {
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .http()
                .with_endpoint("http://localhost:4318/v1/traces"),
        )
        .with_trace_config(
            Config::default().with_resource(Resource::new(vec![
                KeyValue::new("service.name", service_name.to_string()),
                KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
                KeyValue::new("deployment.environment", "production"),
            ])),
        )
        .install_batch(runtime::Tokio)?;

    tracing_subscriber::registry()
        .with(EnvFilter::from_default_env())
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    Ok(())
}
```

### 9.2 服务调用链追踪

**跨服务调用追踪**:

```rust
use opentelemetry::global;
use tracing::{info_span, Instrument};

/// 调用下游服务
#[instrument(skip(client))]
pub async fn call_downstream_service(
    client: &reqwest::Client,
    service_name: &str,
) -> Result<String> {
    // 服务发现
    let discovery = ServiceDiscovery::new("http://localhost:8500")?;
    let instances = discovery.get_healthy_services(service_name).await?;

    let instance = discovery
        .select_instance(&instances)
        .ok_or_else(|| anyhow::anyhow!("No healthy instance found"))?;

    // HTTP 调用 (自动注入 Trace Context)
    let span = info_span!("http_call", target_service = %service_name);

    let url = format!("http://{}:{}/api/endpoint", instance.address, instance.port);

    let response = client
        .get(&url)
        .send()
        .instrument(span)
        .await?
        .text()
        .await?;

    Ok(response)
}
```

### 9.3 健康检查监控

**自定义 Metrics**:

```rust
use opentelemetry::metrics::{Meter, Counter};

pub struct ConsulMetrics {
    service_registrations: Counter<u64>,
    service_discoveries: Counter<u64>,
    health_checks: Counter<u64>,
}

impl ConsulMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            service_registrations: meter
                .u64_counter("consul.service.registrations")
                .with_description("Number of service registrations")
                .init(),
            service_discoveries: meter
                .u64_counter("consul.service.discoveries")
                .with_description("Number of service discoveries")
                .init(),
            health_checks: meter
                .u64_counter("consul.health.checks")
                .with_description("Number of health checks")
                .init(),
        }
    }

    pub fn record_registration(&self) {
        self.service_registrations.add(1, &[]);
    }

    pub fn record_discovery(&self) {
        self.service_discoveries.add(1, &[]);
    }

    pub fn record_health_check(&self) {
        self.health_checks.add(1, &[]);
    }
}
```

---

## 10. 生产最佳实践

### 10.1 高可用部署

**3-node Consul Server Cluster**:

- 最小 3 个 Server 节点 (容忍 1 个故障)
- 推荐 5 个 Server 节点 (容忍 2 个故障)
- 跨可用区部署

**Consul Client 部署**:

- 每台应用服务器运行 1 个 Client Agent
- Client Agent 本地缓存服务目录

### 10.2 备份与恢复

**Snapshot 备份**:

```bash
# 创建快照
consul snapshot save backup.snap

# 恢复快照
consul snapshot restore backup.snap

# 自动化备份 (Cron)
0 */6 * * * consul snapshot save /backups/consul-$(date +\%Y\%m\%d-\%H\%M\%S).snap
```

### 10.3 性能优化

1. **启用 gRPC**: 健康检查使用 gRPC (低延迟)
2. **调整 Gossip 间隔**: 减少网络开销
3. **使用 DNS 缓存**: 减少 DNS 查询
4. **启用 Autopilot**: 自动移除故障节点

---

## 11. 测试策略

### 11.1 单元测试

**tests/consul_test.rs**:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_service_registration() {
        let config = ServiceConfig {
            id: "test-service-1".to_string(),
            name: "test-service".to_string(),
            address: "127.0.0.1".to_string(),
            port: 8080,
            tags: vec!["test".to_string()],
            meta: Default::default(),
        };

        let manager = ConsulServiceManager::new("http://localhost:8500", config)
            .expect("Failed to create manager");

        manager
            .register()
            .await
            .expect("Failed to register service");

        // 清理
        manager
            .deregister()
            .await
            .expect("Failed to deregister service");
    }
}
```

### 11.2 集成测试

**Testcontainers**:

```rust
use testcontainers::{clients, images::generic::GenericImage};

#[tokio::test]
async fn test_consul_integration() {
    let docker = clients::Cli::default();

    let consul = docker.run(
        GenericImage::new("hashicorp/consul", "latest")
            .with_wait_for(testcontainers::core::WaitFor::message_on_stdout(
                "Synced node info",
            )),
    );

    let consul_port = consul.get_host_port_ipv4(8500);
    let consul_addr = format!("http://localhost:{}", consul_port);

    // 运行测试...
}
```

### 11.3 混沌测试

**故障注入**:

```bash
# 模拟网络分区
iptables -A INPUT -s <consul-server-ip> -j DROP

# 停止 Consul Server
docker stop consul-server-1

# 模拟高延迟
tc qdisc add dev eth0 root netem delay 500ms

# 验证系统行为
```

---

## 12. 生产部署

### 12.1 Kubernetes 部署

**consul-helm-values.yaml**:

```yaml
global:
  name: consul
  datacenter: dc1

server:
  replicas: 3
  bootstrapExpect: 3
  storage: 10Gi
  resources:
    requests:
      memory: "1Gi"
      cpu: "500m"
    limits:
      memory: "2Gi"
      cpu: "1000m"

client:
  enabled: true

connectInject:
  enabled: true

ui:
  enabled: true
  service:
    type: LoadBalancer
```

**部署**:

```bash
# 添加 Helm Repo
helm repo add hashicorp https://helm.releases.hashicorp.com

# 安装 Consul
helm install consul hashicorp/consul -f consul-helm-values.yaml
```

### 12.2 Docker Compose 部署

见前文 `docker-compose.yml`。

### 12.3 监控告警

**Prometheus 指标**:

```yaml
# prometheus.yml
scrape_configs:
  - job_name: 'consul'
    consul_sd_configs:
      - server: 'localhost:8500'
    relabel_configs:
      - source_labels: [__meta_consul_service]
        target_label: service
```

**Grafana Dashboard**:

- Consul Server 健康状态
- 服务注册数量
- 健康检查失败率
- Raft Leader 切换次数

---

## 总结

Consul 是一个功能完备的服务网格解决方案，提供了 **服务发现、配置管理、健康检查、分布式锁** 等核心能力。

### 核心优势

1. **多功能集成**: 服务发现 + 配置中心 + Service Mesh
2. **高可用**: Raft 协议保证一致性
3. **多数据中心**: WAN 联邦支持
4. **Service Mesh**: Consul Connect (mTLS)
5. **成熟生态**: 与 Kubernetes, Nomad, Vault 深度集成

### 国际标准对齐

- **网络协议**: HTTP/1.1, HTTP/2, DNS, Gossip (SWIM)
- **一致性**: Raft 协议
- **安全**: mTLS, ACL
- **可观测性**: OpenTelemetry Protocol, Prometheus Metrics

### 适用场景

- 微服务架构 (服务发现与注册)
- 分布式配置管理
- Service Mesh (零信任网络)
- 多数据中心部署
- 分布式锁与 Leader 选举

Consul 是构建现代云原生应用的核心基础设施组件，适合需要 **高可用、多数据中心、Service Mesh** 的生产环境。
