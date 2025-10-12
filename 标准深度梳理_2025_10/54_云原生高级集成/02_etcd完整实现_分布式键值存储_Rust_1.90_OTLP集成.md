# etcd 完整实现：分布式键值存储（Rust 1.90 + OTLP 集成）

## 目录

- [etcd 完整实现：分布式键值存储（Rust 1.90 + OTLP 集成）](#etcd-完整实现分布式键值存储rust-190--otlp-集成)
  - [目录](#目录)
  - [1. etcd 概述](#1-etcd-概述)
    - [1.1 核心特性](#11-核心特性)
    - [1.2 架构设计](#12-架构设计)
    - [1.3 etcd vs 其他 KV 存储](#13-etcd-vs-其他-kv-存储)
  - [2. 国际标准对齐](#2-国际标准对齐)
  - [3. 项目初始化](#3-项目初始化)
    - [3.1 依赖配置](#31-依赖配置)
    - [3.2 etcd 集群部署](#32-etcd-集群部署)
    - [3.3 项目结构](#33-项目结构)
  - [4. 基础 KV 操作](#4-基础-kv-操作)
    - [4.1 Put/Get/Delete](#41-putgetdelete)
    - [4.2 批量操作](#42-批量操作)
    - [4.3 范围查询](#43-范围查询)
  - [5. Watch 机制](#5-watch-机制)
    - [5.1 单键 Watch](#51-单键-watch)
    - [5.2 前缀 Watch](#52-前缀-watch)
    - [5.3 历史事件回放](#53-历史事件回放)
  - [6. 事务与锁](#6-事务与锁)
    - [6.1 事务 (Transaction)](#61-事务-transaction)
    - [6.2 分布式锁](#62-分布式锁)
    - [6.3 STM (Software Transactional Memory)](#63-stm-software-transactional-memory)
  - [7. Lease 租约](#7-lease-租约)
    - [7.1 创建与续期](#71-创建与续期)
    - [7.2 TTL 键](#72-ttl-键)
    - [7.3 KeepAlive](#73-keepalive)
  - [8. 服务发现](#8-服务发现)
    - [8.1 服务注册](#81-服务注册)
    - [8.2 服务发现](#82-服务发现)
    - [8.3 健康检查](#83-健康检查)
  - [9. 分布式协调](#9-分布式协调)
    - [9.1 Leader Election](#91-leader-election)
    - [9.2 分布式屏障](#92-分布式屏障)
    - [9.3 分布式队列](#93-分布式队列)
  - [10. OTLP 集成](#10-otlp-集成)
  - [11. 运维管理](#11-运维管理)
    - [11.1 集群管理](#111-集群管理)
    - [11.2 备份恢复](#112-备份恢复)
    - [11.3 性能优化](#113-性能优化)
  - [12. 生产部署](#12-生产部署)
    - [12.1 Kubernetes 部署](#121-kubernetes-部署)
    - [12.2 监控告警](#122-监控告警)
  - [总结](#总结)
    - [核心优势](#核心优势)
    - [国际标准对齐](#国际标准对齐)
    - [适用场景](#适用场景)

---

## 1. etcd 概述

**etcd** 是 CoreOS 开发的分布式键值存储系统，基于 **Raft 一致性协议**，为 Kubernetes 等云原生系统提供可靠的元数据存储。

### 1.1 核心特性

| 特性 | 说明 | 技术实现 |
|------|------|----------|
| **强一致性** | Raft 协议保证 | Linearizable Reads |
| **Watch 机制** | 实时监听键变化 | gRPC Streaming |
| **分布式锁** | 基于 Lease 和 Transaction | Compare-And-Swap |
| **Multi-Version** | MVCC 多版本并发控制 | B-tree 索引 |
| **高可用** | 自动 Leader 选举 | Raft |
| **事务支持** | IF-THEN-ELSE 语义 | Transaction API |

### 1.2 架构设计

```text
┌─────────────────────────────────────────────┐
│           etcd Architecture                 │
└─────────────────────────────────────────────┘

Client Layer:
┌──────────────┐  ┌──────────────┐  ┌──────────────┐
│   Client 1   │  │   Client 2   │  │   Client 3   │
│  (gRPC API)  │  │  (gRPC API)  │  │  (gRPC API)  │
└──────┬───────┘  └──────┬───────┘  └──────┬───────┘
       │                 │                 │
       └─────────────────┼─────────────────┘
                         │
┌────────────────────────▼─────────────────────────┐
│         etcd Server (Cluster)                    │
│  ┌────────────┐  ┌────────────┐  ┌────────────┐ │
│  │   Leader   │  │  Follower  │  │  Follower  │ │
│  │  (Write)   │◄─┤  (Read)    │◄─┤  (Read)    │ │
│  └─────┬──────┘  └─────┬──────┘  └─────┬──────┘ │
│        │ Raft Log     │               │         │
│        ▼               ▼               ▼         │
│  ┌─────────────────────────────────────────┐    │
│  │         MVCC Storage (BoltDB)           │    │
│  │  - B-tree Index                         │    │
│  │  - Versioned Data                       │    │
│  └─────────────────────────────────────────┘    │
└──────────────────────────────────────────────────┘
```

### 1.3 etcd vs 其他 KV 存储

| 维度 | etcd | Consul | Zookeeper | Redis |
|------|------|--------|-----------|-------|
| **一致性协议** | Raft | Raft | ZAB | Replication |
| **数据模型** | KV (MVCC) | KV | Hierarchical | KV + 数据结构 |
| **Watch 机制** | gRPC Stream | HTTP Long Poll | Watcher | Pub/Sub |
| **事务支持** | IF-THEN-ELSE | CAS | Multi-op | Multi/Exec |
| **性能** | 中 (强一致性) | 中 | 中 | 高 (最终一致性) |
| **主要用途** | Kubernetes 元数据 | 服务发现 | 分布式协调 | 缓存 + 队列 |

---

## 2. 国际标准对齐

| 标准 | 版本 | 说明 |
|------|------|------|
| **gRPC** | gRPC Core | 客户端 API |
| **HTTP/2** | RFC 7540 | 传输层 |
| **Protobuf** | Proto3 | 序列化格式 |
| **Raft** | Raft Paper (2014) | 一致性协议 |
| **MVCC** | 多版本并发控制 | 存储引擎 |
| **TLS 1.3** | RFC 8446 | 传输安全 |

---

## 3. 项目初始化

### 3.1 依赖配置

**Cargo.toml**:

```toml
[package]
name = "etcd-service"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# etcd 客户端
etcd-client = "0.14"

# 异步运行时
tokio = { version = "1", features = ["full"] }
tokio-stream = "0.1"

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 日志
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }

# OpenTelemetry
opentelemetry = "0.25"
opentelemetry-otlp = "0.25"
tracing-opentelemetry = "0.26"

# 错误处理
anyhow = "1.0"
thiserror = "1.0"

# 时间
chrono = "0.4"
```

### 3.2 etcd 集群部署

**docker-compose.yml**:

```yaml
version: '3.9'

services:
  etcd-1:
    image: quay.io/coreos/etcd:v3.5.11
    container_name: etcd-1
    command:
      - /usr/local/bin/etcd
      - --name=etcd-1
      - --data-dir=/etcd-data
      - --listen-client-urls=http://0.0.0.0:2379
      - --advertise-client-urls=http://etcd-1:2379
      - --listen-peer-urls=http://0.0.0.0:2380
      - --initial-advertise-peer-urls=http://etcd-1:2380
      - --initial-cluster=etcd-1=http://etcd-1:2380,etcd-2=http://etcd-2:2380,etcd-3=http://etcd-3:2380
      - --initial-cluster-token=etcd-cluster
      - --initial-cluster-state=new
    ports:
      - "2379:2379"
    volumes:
      - etcd-1-data:/etcd-data
    networks:
      - etcd-net

  etcd-2:
    image: quay.io/coreos/etcd:v3.5.11
    container_name: etcd-2
    command:
      - /usr/local/bin/etcd
      - --name=etcd-2
      - --data-dir=/etcd-data
      - --listen-client-urls=http://0.0.0.0:2379
      - --advertise-client-urls=http://etcd-2:2379
      - --listen-peer-urls=http://0.0.0.0:2380
      - --initial-advertise-peer-urls=http://etcd-2:2380
      - --initial-cluster=etcd-1=http://etcd-1:2380,etcd-2=http://etcd-2:2380,etcd-3=http://etcd-3:2380
      - --initial-cluster-token=etcd-cluster
      - --initial-cluster-state=new
    volumes:
      - etcd-2-data:/etcd-data
    networks:
      - etcd-net

  etcd-3:
    image: quay.io/coreos/etcd:v3.5.11
    container_name: etcd-3
    command:
      - /usr/local/bin/etcd
      - --name=etcd-3
      - --data-dir=/etcd-data
      - --listen-client-urls=http://0.0.0.0:2379
      - --advertise-client-urls=http://etcd-3:2379
      - --listen-peer-urls=http://0.0.0.0:2380
      - --initial-advertise-peer-urls=http://etcd-3:2380
      - --initial-cluster=etcd-1=http://etcd-1:2380,etcd-2=http://etcd-2:2380,etcd-3=http://etcd-3:2380
      - --initial-cluster-token=etcd-cluster
      - --initial-cluster-state=new
    volumes:
      - etcd-3-data:/etcd-data
    networks:
      - etcd-net

volumes:
  etcd-1-data:
  etcd-2-data:
  etcd-3-data:

networks:
  etcd-net:
    driver: bridge
```

### 3.3 项目结构

```text
etcd-service/
├── Cargo.toml
├── src/
│   ├── main.rs
│   ├── etcd/
│   │   ├── mod.rs
│   │   ├── client.rs       # 客户端封装
│   │   ├── kv.rs           # KV 操作
│   │   ├── watch.rs        # Watch 机制
│   │   ├── lease.rs        # Lease 管理
│   │   ├── lock.rs         # 分布式锁
│   │   └── election.rs     # Leader Election
│   ├── service/
│   │   ├── mod.rs
│   │   └── discovery.rs    # 服务发现
│   └── telemetry/
│       └── otlp.rs
└── docker-compose.yml
```

---

## 4. 基础 KV 操作

### 4.1 Put/Get/Delete

**src/etcd/kv.rs**:

```rust
use etcd_client::{Client, GetOptions, PutOptions};
use anyhow::Result;
use tracing::{info, instrument};

pub struct EtcdKVStore {
    client: Client,
}

impl EtcdKVStore {
    pub async fn new(endpoints: Vec<String>) -> Result<Self> {
        let client = Client::connect(endpoints, None).await?;
        Ok(Self { client })
    }

    /// Put: 写入键值
    #[instrument(skip(self, value))]
    pub async fn put(&mut self, key: &str, value: &str) -> Result<()> {
        info!(key = %key, "Putting key-value");

        self.client.put(key, value, None).await?;

        info!(key = %key, "Key-value put successfully");

        Ok(())
    }

    /// Get: 读取键值
    #[instrument(skip(self))]
    pub async fn get(&mut self, key: &str) -> Result<Option<String>> {
        info!(key = %key, "Getting key-value");

        let response = self.client.get(key, None).await?;

        if let Some(kv) = response.kvs().first() {
            let value = String::from_utf8(kv.value().to_vec())?;
            info!(key = %key, "Key-value retrieved");
            Ok(Some(value))
        } else {
            info!(key = %key, "Key not found");
            Ok(None)
        }
    }

    /// Delete: 删除键
    #[instrument(skip(self))]
    pub async fn delete(&mut self, key: &str) -> Result<()> {
        info!(key = %key, "Deleting key");

        self.client.delete(key, None).await?;

        info!(key = %key, "Key deleted");

        Ok(())
    }

    /// Get with revision (时间旅行)
    #[instrument(skip(self))]
    pub async fn get_at_revision(&mut self, key: &str, revision: i64) -> Result<Option<String>> {
        info!(key = %key, revision = %revision, "Getting key at specific revision");

        let options = GetOptions::new().with_revision(revision);
        let response = self.client.get(key, Some(options)).await?;

        if let Some(kv) = response.kvs().first() {
            let value = String::from_utf8(kv.value().to_vec())?;
            Ok(Some(value))
        } else {
            Ok(None)
        }
    }
}
```

### 4.2 批量操作

**批量读取**:

```rust
impl EtcdKVStore {
    /// 批量 Get (范围查询)
    #[instrument(skip(self))]
    pub async fn get_range(
        &mut self,
        start_key: &str,
        end_key: &str,
    ) -> Result<Vec<(String, String)>> {
        info!(start_key = %start_key, end_key = %end_key, "Getting range");

        let options = GetOptions::new().with_range(end_key);
        let response = self.client.get(start_key, Some(options)).await?;

        let kvs: Vec<(String, String)> = response
            .kvs()
            .iter()
            .map(|kv| {
                let key = String::from_utf8(kv.key().to_vec()).unwrap();
                let value = String::from_utf8(kv.value().to_vec()).unwrap();
                (key, value)
            })
            .collect();

        info!(start_key = %start_key, end_key = %end_key, count = %kvs.len(), "Range retrieved");

        Ok(kvs)
    }
}
```

### 4.3 范围查询

**前缀查询**:

```rust
impl EtcdKVStore {
    /// 前缀查询
    #[instrument(skip(self))]
    pub async fn get_prefix(&mut self, prefix: &str) -> Result<Vec<(String, String)>> {
        info!(prefix = %prefix, "Getting keys with prefix");

        let options = GetOptions::new().with_prefix();
        let response = self.client.get(prefix, Some(options)).await?;

        let kvs: Vec<(String, String)> = response
            .kvs()
            .iter()
            .map(|kv| {
                let key = String::from_utf8(kv.key().to_vec()).unwrap();
                let value = String::from_utf8(kv.value().to_vec()).unwrap();
                (key, value)
            })
            .collect();

        info!(prefix = %prefix, count = %kvs.len(), "Prefix query completed");

        Ok(kvs)
    }
}
```

---

## 5. Watch 机制

### 5.1 单键 Watch

**src/etcd/watch.rs**:

```rust
use etcd_client::{Client, WatchOptions};
use tokio_stream::StreamExt;
use anyhow::Result;
use tracing::{info, instrument};

pub struct EtcdWatcher {
    client: Client,
}

impl EtcdWatcher {
    pub async fn new(endpoints: Vec<String>) -> Result<Self> {
        let client = Client::connect(endpoints, None).await?;
        Ok(Self { client })
    }

    /// Watch 单个键
    #[instrument(skip(self, callback))]
    pub async fn watch_key<F>(&mut self, key: &str, mut callback: F) -> Result<()>
    where
        F: FnMut(&str, &str, WatchEventType) -> Result<()>,
    {
        info!(key = %key, "Starting watch on key");

        let (mut watcher, mut stream) = self.client.watch(key, None).await?;

        while let Some(response) = stream.next().await {
            match response {
                Ok(watch_response) => {
                    for event in watch_response.events() {
                        let key_str = String::from_utf8(event.kv().unwrap().key().to_vec())?;
                        let value_str = String::from_utf8(event.kv().unwrap().value().to_vec())?;

                        let event_type = match event.event_type() {
                            etcd_client::EventType::Put => WatchEventType::Put,
                            etcd_client::EventType::Delete => WatchEventType::Delete,
                        };

                        info!(
                            key = %key_str,
                            event_type = ?event_type,
                            "Watch event received"
                        );

                        callback(&key_str, &value_str, event_type)?;
                    }
                }
                Err(e) => {
                    tracing::error!(error = %e, "Watch error");
                    break;
                }
            }
        }

        watcher.cancel().await?;

        Ok(())
    }
}

#[derive(Debug)]
pub enum WatchEventType {
    Put,
    Delete,
}
```

### 5.2 前缀 Watch

**前缀监听**:

```rust
impl EtcdWatcher {
    /// Watch 前缀
    #[instrument(skip(self, callback))]
    pub async fn watch_prefix<F>(&mut self, prefix: &str, mut callback: F) -> Result<()>
    where
        F: FnMut(&str, &str, WatchEventType) -> Result<()>,
    {
        info!(prefix = %prefix, "Starting watch on prefix");

        let options = WatchOptions::new().with_prefix();
        let (mut watcher, mut stream) = self.client.watch(prefix, Some(options)).await?;

        while let Some(response) = stream.next().await {
            match response {
                Ok(watch_response) => {
                    for event in watch_response.events() {
                        let key_str = String::from_utf8(event.kv().unwrap().key().to_vec())?;
                        let value_str = String::from_utf8(event.kv().unwrap().value().to_vec())?;

                        let event_type = match event.event_type() {
                            etcd_client::EventType::Put => WatchEventType::Put,
                            etcd_client::EventType::Delete => WatchEventType::Delete,
                        };

                        info!(
                            key = %key_str,
                            event_type = ?event_type,
                            "Prefix watch event received"
                        );

                        callback(&key_str, &value_str, event_type)?;
                    }
                }
                Err(e) => {
                    tracing::error!(error = %e, "Watch error");
                    break;
                }
            }
        }

        watcher.cancel().await?;

        Ok(())
    }
}
```

### 5.3 历史事件回放

**从特定 Revision 开始 Watch**:

```rust
impl EtcdWatcher {
    /// 从指定 Revision 开始 Watch
    #[instrument(skip(self, callback))]
    pub async fn watch_from_revision<F>(
        &mut self,
        key: &str,
        start_revision: i64,
        mut callback: F,
    ) -> Result<()>
    where
        F: FnMut(&str, &str, WatchEventType) -> Result<()>,
    {
        info!(
            key = %key,
            start_revision = %start_revision,
            "Starting watch from revision"
        );

        let options = WatchOptions::new().with_start_revision(start_revision);
        let (mut watcher, mut stream) = self.client.watch(key, Some(options)).await?;

        while let Some(response) = stream.next().await {
            // ... 处理事件
        }

        watcher.cancel().await?;

        Ok(())
    }
}
```

---

## 6. 事务与锁

### 6.1 事务 (Transaction)

**src/etcd/kv.rs (续)**:

```rust
use etcd_client::{Txn, TxnOp, Compare, CompareOp};

impl EtcdKVStore {
    /// 事务: Compare-And-Swap
    #[instrument(skip(self, new_value))]
    pub async fn cas(
        &mut self,
        key: &str,
        expected_value: &str,
        new_value: &str,
    ) -> Result<bool> {
        info!(
            key = %key,
            "Performing CAS transaction"
        );

        let txn = Txn::new()
            .when([Compare::value(key, CompareOp::Equal, expected_value)])
            .and_then([TxnOp::put(key, new_value, None)])
            .or_else([TxnOp::get(key, None)]);

        let response = self.client.txn(txn).await?;

        let succeeded = response.succeeded();

        if succeeded {
            info!(key = %key, "CAS succeeded");
        } else {
            info!(key = %key, "CAS failed");
        }

        Ok(succeeded)
    }

    /// 原子递增
    #[instrument(skip(self))]
    pub async fn increment(&mut self, key: &str) -> Result<i64> {
        loop {
            // 读取当前值
            let current_value = self.get(key).await?.unwrap_or_else(|| "0".to_string());
            let current: i64 = current_value.parse()?;

            // CAS 更新
            let new_value = (current + 1).to_string();
            let succeeded = self.cas(key, &current_value, &new_value).await?;

            if succeeded {
                return Ok(current + 1);
            }

            // 重试
            tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
        }
    }
}
```

### 6.2 分布式锁

**src/etcd/lock.rs**:

```rust
use etcd_client::{Client, LockOptions};
use anyhow::Result;
use tracing::{info, instrument};

pub struct EtcdLock {
    client: Client,
    lock_key: String,
}

impl EtcdLock {
    pub async fn new(endpoints: Vec<String>, lock_key: String) -> Result<Self> {
        let client = Client::connect(endpoints, None).await?;
        Ok(Self { client, lock_key })
    }

    /// 获取锁
    #[instrument(skip(self))]
    pub async fn lock(&mut self) -> Result<Vec<u8>> {
        info!(lock_key = %self.lock_key, "Acquiring lock");

        let response = self.client.lock(&self.lock_key, None).await?;

        let lock_key = response.key().to_vec();

        info!(lock_key = %self.lock_key, "Lock acquired");

        Ok(lock_key)
    }

    /// 释放锁
    #[instrument(skip(self, lock_key))]
    pub async fn unlock(&mut self, lock_key: &[u8]) -> Result<()> {
        info!(lock_key = %self.lock_key, "Releasing lock");

        self.client.unlock(lock_key).await?;

        info!(lock_key = %self.lock_key, "Lock released");

        Ok(())
    }

    /// 自动管理锁 (RAII)
    pub async fn with_lock<F, Fut, T>(&mut self, f: F) -> Result<T>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<T>>,
    {
        let lock_key = self.lock().await?;

        let result = f().await;

        self.unlock(&lock_key).await?;

        result
    }
}
```

### 6.3 STM (Software Transactional Memory)

**使用示例**:

```rust
/// 银行转账 (原子操作)
pub async fn transfer(
    kv_store: &mut EtcdKVStore,
    from_account: &str,
    to_account: &str,
    amount: i64,
) -> Result<()> {
    loop {
        // 读取账户余额
        let from_balance: i64 = kv_store
            .get(from_account)
            .await?
            .unwrap_or_else(|| "0".to_string())
            .parse()?;

        let to_balance: i64 = kv_store
            .get(to_account)
            .await?
            .unwrap_or_else(|| "0".to_string())
            .parse()?;

        // 检查余额
        if from_balance < amount {
            anyhow::bail!("Insufficient balance");
        }

        // 构建事务
        let txn = Txn::new()
            .when([
                Compare::value(from_account, CompareOp::Equal, from_balance.to_string()),
                Compare::value(to_account, CompareOp::Equal, to_balance.to_string()),
            ])
            .and_then([
                TxnOp::put(from_account, (from_balance - amount).to_string(), None),
                TxnOp::put(to_account, (to_balance + amount).to_string(), None),
            ])
            .or_else([]);

        let response = kv_store.client.txn(txn).await?;

        if response.succeeded() {
            info!("Transfer succeeded");
            return Ok(());
        }

        // 重试
        tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
    }
}
```

---

## 7. Lease 租约

### 7.1 创建与续期

**src/etcd/lease.rs**:

```rust
use etcd_client::{Client, LeaseGrantOptions, LeaseKeepAliveStream};
use tokio_stream::StreamExt;
use anyhow::Result;
use tracing::{info, instrument};

pub struct EtcdLease {
    client: Client,
    lease_id: i64,
}

impl EtcdLease {
    /// 创建 Lease
    #[instrument(skip(client))]
    pub async fn new(mut client: Client, ttl: i64) -> Result<Self> {
        info!(ttl = %ttl, "Creating lease");

        let response = client.lease_grant(ttl, None).await?;

        let lease_id = response.id();

        info!(lease_id = %lease_id, ttl = %ttl, "Lease created");

        Ok(Self { client, lease_id })
    }

    pub fn id(&self) -> i64 {
        self.lease_id
    }

    /// KeepAlive (持续续期)
    #[instrument(skip(self))]
    pub async fn keep_alive(&mut self) -> Result<()> {
        info!(lease_id = %self.lease_id, "Starting lease keep-alive");

        let (mut keeper, mut stream) = self.client.lease_keep_alive(self.lease_id).await?;

        // 发送 KeepAlive 请求
        keeper.keep_alive().await?;

        // 监听 KeepAlive 响应
        tokio::spawn(async move {
            while let Some(response) = stream.next().await {
                match response {
                    Ok(keep_alive_response) => {
                        info!(
                            lease_id = %keep_alive_response.id(),
                            ttl = %keep_alive_response.ttl(),
                            "Lease kept alive"
                        );
                    }
                    Err(e) => {
                        tracing::error!(error = %e, "KeepAlive error");
                        break;
                    }
                }
            }
        });

        Ok(())
    }

    /// 撤销 Lease
    #[instrument(skip(self))]
    pub async fn revoke(&mut self) -> Result<()> {
        info!(lease_id = %self.lease_id, "Revoking lease");

        self.client.lease_revoke(self.lease_id).await?;

        info!(lease_id = %self.lease_id, "Lease revoked");

        Ok(())
    }
}
```

### 7.2 TTL 键

**带 TTL 的键**:

```rust
use etcd_client::PutOptions;

impl EtcdKVStore {
    /// Put with Lease (TTL 键)
    #[instrument(skip(self, value))]
    pub async fn put_with_ttl(
        &mut self,
        key: &str,
        value: &str,
        ttl: i64,
    ) -> Result<()> {
        info!(key = %key, ttl = %ttl, "Putting key with TTL");

        // 创建 Lease
        let lease_response = self.client.lease_grant(ttl, None).await?;
        let lease_id = lease_response.id();

        // Put with Lease
        let options = PutOptions::new().with_lease(lease_id);
        self.client.put(key, value, Some(options)).await?;

        info!(key = %key, lease_id = %lease_id, "Key put with TTL");

        Ok(())
    }
}
```

### 7.3 KeepAlive

**自动续期**:

```rust
pub async fn auto_renew_lease(mut client: Client, lease_id: i64) -> Result<()> {
    let (mut keeper, mut stream) = client.lease_keep_alive(lease_id).await?;

    // 定期发送 KeepAlive
    tokio::spawn(async move {
        let mut interval = tokio::time::interval(tokio::time::Duration::from_secs(5));

        loop {
            interval.tick().await;

            if let Err(e) = keeper.keep_alive().await {
                tracing::error!(error = %e, "Failed to keep alive");
                break;
            }
        }
    });

    // 监听响应
    while let Some(response) = stream.next().await {
        match response {
            Ok(keep_alive_response) => {
                info!(
                    lease_id = %keep_alive_response.id(),
                    ttl = %keep_alive_response.ttl(),
                    "Lease renewed"
                );
            }
            Err(e) => {
                tracing::error!(error = %e, "KeepAlive error");
                break;
            }
        }
    }

    Ok(())
}
```

---

## 8. 服务发现

### 8.1 服务注册

**src/service/discovery.rs**:

```rust
use crate::etcd::{EtcdKVStore, EtcdLease};
use serde::{Deserialize, Serialize};
use anyhow::Result;
use tracing::{info, instrument};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceInfo {
    pub id: String,
    pub name: String,
    pub address: String,
    pub port: u16,
    pub metadata: std::collections::HashMap<String, String>,
}

pub struct ServiceRegistry {
    kv_store: EtcdKVStore,
}

impl ServiceRegistry {
    pub async fn new(endpoints: Vec<String>) -> Result<Self> {
        let kv_store = EtcdKVStore::new(endpoints).await?;
        Ok(Self { kv_store })
    }

    /// 注册服务 (带 TTL)
    #[instrument(skip(self, info))]
    pub async fn register(&mut self, info: ServiceInfo, ttl: i64) -> Result<i64> {
        info!(
            service_id = %info.id,
            service_name = %info.name,
            "Registering service"
        );

        let key = format!("/services/{}/{}", info.name, info.id);
        let value = serde_json::to_string(&info)?;

        // 创建 Lease
        let lease_response = self.kv_store.client.lease_grant(ttl, None).await?;
        let lease_id = lease_response.id();

        // 注册服务 (关联 Lease)
        let options = etcd_client::PutOptions::new().with_lease(lease_id);
        self.kv_store.client.put(&key, &value, Some(options)).await?;

        info!(
            service_id = %info.id,
            lease_id = %lease_id,
            "Service registered"
        );

        Ok(lease_id)
    }

    /// 注销服务
    #[instrument(skip(self))]
    pub async fn deregister(&mut self, service_name: &str, service_id: &str) -> Result<()> {
        info!(
            service_id = %service_id,
            service_name = %service_name,
            "Deregistering service"
        );

        let key = format!("/services/{}/{}", service_name, service_id);
        self.kv_store.delete(&key).await?;

        info!(service_id = %service_id, "Service deregistered");

        Ok(())
    }
}
```

### 8.2 服务发现

**查询服务**:

```rust
impl ServiceRegistry {
    /// 发现服务实例
    #[instrument(skip(self))]
    pub async fn discover(&mut self, service_name: &str) -> Result<Vec<ServiceInfo>> {
        info!(service_name = %service_name, "Discovering services");

        let prefix = format!("/services/{}/", service_name);
        let kvs = self.kv_store.get_prefix(&prefix).await?;

        let services: Vec<ServiceInfo> = kvs
            .iter()
            .filter_map(|(_, value)| serde_json::from_str(value).ok())
            .collect();

        info!(
            service_name = %service_name,
            count = %services.len(),
            "Services discovered"
        );

        Ok(services)
    }

    /// Watch 服务变化
    pub async fn watch_services<F>(
        &mut self,
        service_name: &str,
        callback: F,
    ) -> Result<()>
    where
        F: FnMut(&str, &ServiceInfo, crate::etcd::watch::WatchEventType) -> Result<()>,
    {
        let prefix = format!("/services/{}/", service_name);

        let mut watcher = crate::etcd::watch::EtcdWatcher::new(vec!["http://localhost:2379".to_string()]).await?;

        watcher.watch_prefix(&prefix, |key, value, event_type| {
            if let Ok(service_info) = serde_json::from_str::<ServiceInfo>(value) {
                callback(key, &service_info, event_type)?;
            }
            Ok(())
        }).await?;

        Ok(())
    }
}
```

### 8.3 健康检查

**定期续期 Lease**:

```rust
pub async fn maintain_service_registration(
    mut client: etcd_client::Client,
    lease_id: i64,
) -> Result<()> {
    let (mut keeper, mut stream) = client.lease_keep_alive(lease_id).await?;

    // 定期续期
    tokio::spawn(async move {
        let mut interval = tokio::time::interval(tokio::time::Duration::from_secs(5));

        loop {
            interval.tick().await;

            if let Err(e) = keeper.keep_alive().await {
                tracing::error!(error = %e, "Failed to keep service alive");
                break;
            }
        }
    });

    // 监听 KeepAlive 响应
    while let Some(response) = stream.next().await {
        match response {
            Ok(keep_alive_response) => {
                info!(
                    lease_id = %keep_alive_response.id(),
                    ttl = %keep_alive_response.ttl(),
                    "Service lease renewed"
                );
            }
            Err(e) => {
                tracing::error!(error = %e, "Service KeepAlive error");
                break;
            }
        }
    }

    Ok(())
}
```

---

## 9. 分布式协调

### 9.1 Leader Election

**src/etcd/election.rs**:

```rust
use etcd_client::{Client, ElectionClient};
use anyhow::Result;
use tracing::{info, instrument};

pub struct LeaderElection {
    client: Client,
    election_name: String,
}

impl LeaderElection {
    pub async fn new(endpoints: Vec<String>, election_name: String) -> Result<Self> {
        let client = Client::connect(endpoints, None).await?;
        Ok(Self {
            client,
            election_name,
        })
    }

    /// 竞选 Leader
    #[instrument(skip(self, value))]
    pub async fn campaign(&mut self, value: &str) -> Result<()> {
        info!(election_name = %self.election_name, "Campaigning for leadership");

        // 创建 Lease
        let lease_response = self.client.lease_grant(30, None).await?;
        let lease_id = lease_response.id();

        // Campaign
        let response = self
            .client
            .campaign(&self.election_name, value, lease_id)
            .await?;

        info!(
            election_name = %self.election_name,
            leader_key = ?response.leader().unwrap().name(),
            "Became leader"
        );

        Ok(())
    }

    /// 获取当前 Leader
    #[instrument(skip(self))]
    pub async fn get_leader(&mut self) -> Result<Option<String>> {
        let response = self.client.leader(&self.election_name).await?;

        if let Some(leader) = response.leader() {
            let value = String::from_utf8(leader.value().to_vec())?;
            info!(election_name = %self.election_name, leader = %value, "Leader found");
            Ok(Some(value))
        } else {
            info!(election_name = %self.election_name, "No leader found");
            Ok(None)
        }
    }

    /// 放弃 Leader
    #[instrument(skip(self, leader_key))]
    pub async fn resign(&mut self, leader_key: &[u8]) -> Result<()> {
        info!(election_name = %self.election_name, "Resigning from leadership");

        self.client.resign(leader_key).await?;

        info!(election_name = %self.election_name, "Leadership resigned");

        Ok(())
    }
}
```

### 9.2 分布式屏障

**Barrier 实现**:

```rust
pub struct Barrier {
    kv_store: EtcdKVStore,
    barrier_key: String,
    expected_count: usize,
}

impl Barrier {
    pub async fn new(
        endpoints: Vec<String>,
        barrier_key: String,
        expected_count: usize,
    ) -> Result<Self> {
        let kv_store = EtcdKVStore::new(endpoints).await?;
        Ok(Self {
            kv_store,
            barrier_key,
            expected_count,
        })
    }

    /// 等待所有参与者到达
    pub async fn wait(&mut self, participant_id: &str) -> Result<()> {
        info!(
            barrier_key = %self.barrier_key,
            participant_id = %participant_id,
            "Participant waiting at barrier"
        );

        // 注册参与者
        let participant_key = format!("{}/{}", self.barrier_key, participant_id);
        self.kv_store.put(&participant_key, "ready").await?;

        // 等待所有参与者
        loop {
            let participants = self.kv_store.get_prefix(&self.barrier_key).await?;

            if participants.len() >= self.expected_count {
                info!(
                    barrier_key = %self.barrier_key,
                    "All participants arrived at barrier"
                );
                break;
            }

            tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        }

        Ok(())
    }
}
```

### 9.3 分布式队列

**FIFO Queue 实现**:

```rust
pub struct DistributedQueue {
    kv_store: EtcdKVStore,
    queue_prefix: String,
}

impl DistributedQueue {
    pub async fn new(endpoints: Vec<String>, queue_prefix: String) -> Result<Self> {
        let kv_store = EtcdKVStore::new(endpoints).await?;
        Ok(Self {
            kv_store,
            queue_prefix,
        })
    }

    /// 入队
    pub async fn enqueue(&mut self, value: &str) -> Result<()> {
        let timestamp = chrono::Utc::now().timestamp_nanos();
        let key = format!("{}/{:020}", self.queue_prefix, timestamp);

        self.kv_store.put(&key, value).await?;

        info!(queue_prefix = %self.queue_prefix, "Item enqueued");

        Ok(())
    }

    /// 出队 (FIFO)
    pub async fn dequeue(&mut self) -> Result<Option<String>> {
        let items = self.kv_store.get_prefix(&self.queue_prefix).await?;

        if items.is_empty() {
            return Ok(None);
        }

        // 获取最早的项 (字典序最小)
        let (key, value) = &items[0];

        // 删除项
        self.kv_store.delete(key).await?;

        info!(queue_prefix = %self.queue_prefix, "Item dequeued");

        Ok(Some(value.clone()))
    }
}
```

---

## 10. OTLP 集成

**服务注册追踪**:

```rust
use opentelemetry::{global, trace::Tracer, KeyValue};
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

---

## 11. 运维管理

### 11.1 集群管理

**查看集群状态**:

```bash
# 查看成员
etcdctl member list

# 查看集群健康状态
etcdctl endpoint health --cluster

# 查看 Leader
etcdctl endpoint status --cluster
```

### 11.2 备份恢复

**Snapshot 备份**:

```bash
# 创建快照
etcdctl snapshot save backup.db

# 恢复快照
etcdctl snapshot restore backup.db \
    --name=etcd-1 \
    --initial-cluster=etcd-1=http://etcd-1:2380 \
    --initial-advertise-peer-urls=http://etcd-1:2380
```

### 11.3 性能优化

1. **调整快照间隔**: `--snapshot-count=10000`
2. **启用压缩**: `etcdctl compact <revision>`
3. **碎片整理**: `etcdctl defrag`
4. **调整 Raft 参数**: `--heartbeat-interval`, `--election-timeout`

---

## 12. 生产部署

### 12.1 Kubernetes 部署

**StatefulSet**:

```yaml
apiVersion: apps/v1
kind: StatefulSet
metadata:
  name: etcd
spec:
  serviceName: etcd
  replicas: 3
  selector:
    matchLabels:
      app: etcd
  template:
    metadata:
      labels:
        app: etcd
    spec:
      containers:
      - name: etcd
        image: quay.io/coreos/etcd:v3.5.11
        ports:
        - containerPort: 2379
          name: client
        - containerPort: 2380
          name: peer
        volumeMounts:
        - name: data
          mountPath: /var/lib/etcd
        env:
        - name: ETCD_NAME
          valueFrom:
            fieldRef:
              fieldPath: metadata.name
        - name: ETCD_INITIAL_CLUSTER
          value: "etcd-0=http://etcd-0.etcd:2380,etcd-1=http://etcd-1.etcd:2380,etcd-2=http://etcd-2.etcd:2380"
        - name: ETCD_INITIAL_CLUSTER_STATE
          value: "new"
  volumeClaimTemplates:
  - metadata:
      name: data
    spec:
      accessModes: ["ReadWriteOnce"]
      resources:
        requests:
          storage: 10Gi
```

### 12.2 监控告警

**Prometheus 指标**:

```yaml
- job_name: 'etcd'
  static_configs:
    - targets: ['etcd-1:2379', 'etcd-2:2379', 'etcd-3:2379']
```

**关键指标**:

- `etcd_server_has_leader`: Leader 状态
- `etcd_server_leader_changes_seen_total`: Leader 切换次数
- `etcd_disk_backend_commit_duration_seconds`: 磁盘提交延迟
- `etcd_network_peer_round_trip_time_seconds`: 节点间 RTT

---

## 总结

etcd 是 Kubernetes 的核心组件，提供了强一致性的分布式键值存储，是构建云原生应用的基础设施。

### 核心优势

1. **强一致性**: Raft 协议保证线性化读写
2. **Watch 机制**: gRPC Stream 实时监听变化
3. **MVCC**: 多版本并发控制,支持时间旅行
4. **事务支持**: IF-THEN-ELSE 语义
5. **Lease 租约**: 自动过期机制

### 国际标准对齐

- **gRPC/Protobuf**: 客户端 API
- **Raft**: 一致性协议
- **MVCC**: 存储引擎
- **TLS 1.3**: 传输安全

### 适用场景

- Kubernetes 元数据存储
- 服务发现与注册
- 配置中心
- 分布式锁与 Leader 选举
- 分布式协调 (Barrier, Queue)

etcd 是云原生生态的基石，适合需要 **强一致性、高可用、实时监听** 的分布式系统。
