# 📚 事件溯源 (Event Sourcing) - Rust OTLP 完整追踪指南

> **架构来源**: Martin Fowler (2005)  
> **国际标准**: 金融系统、审计系统标准架构  
> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月11日

---

## 📋 目录

- [📚 事件溯源 (Event Sourcing) - Rust OTLP 完整追踪指南](#-事件溯源-event-sourcing---rust-otlp-完整追踪指南)
  - [📋 目录](#-目录)
  - [📊 执行摘要](#-执行摘要)
    - [核心价值](#核心价值)
  - [🎯 事件溯源核心概念](#-事件溯源核心概念)
    - [1. 架构对比](#1-架构对比)
    - [2. 核心组件](#2-核心组件)
  - [🏗️ Rust 项目结构](#️-rust-项目结构)
  - [💎 核心实现](#-核心实现)
    - [1. Domain Events (领域事件)](#1-domain-events-领域事件)
      - [`src/domain/events/mod.rs`](#srcdomaineventsmodrs)
    - [2. Aggregate Root (聚合根 - 事件重放)](#2-aggregate-root-聚合根---事件重放)
      - [`src/domain/aggregates/account.rs`](#srcdomainaggregatesaccountrs)
    - [3. Event Store (事件存储)](#3-event-store-事件存储)
      - [`src/event_store/postgres_store.rs`](#srcevent_storepostgres_storers)
    - [4. Snapshot (快照优化)](#4-snapshot-快照优化)
      - [`src/event_store/snapshots.rs`](#srcevent_storesnapshotsrs)
    - [5. Command Handler (带快照优化)](#5-command-handler-带快照优化)
      - [`src/commands/handlers/deposit_handler.rs`](#srccommandshandlersdeposit_handlerrs)
  - [📊 完整 OTLP 追踪链路](#-完整-otlp-追踪链路)
  - [📦 数据库迁移](#-数据库迁移)
    - [`migrations/001_create_events_table.sql`](#migrations001_create_events_tablesql)
  - [🌟 最佳实践](#-最佳实践)
    - [✅ DO (推荐)](#-do-推荐)
    - [❌ DON'T (避免)](#-dont-避免)
  - [🔗 参考资源](#-参考资源)
    - [架构模式](#架构模式)
    - [Rust 实现](#rust-实现)

## 📊 执行摘要

事件溯源(Event Sourcing)是一种将所有状态变更以**事件序列**形式存储的架构模式,而不是直接保存当前状态。
本文档展示如何在 Rust 1.90 中实现完整的事件溯源系统,包括事件存储、事件重放、快照优化,并集成 OpenTelemetry 分布式追踪。

### 核心价值

| 特性 | 传统状态存储 | 事件溯源 | 优势 |
|------|-------------|----------|------|
| **审计能力** | 需额外日志 | 天然完整审计 | +1000% 审计性 |
| **时间旅行** | 不支持 | 完整历史 | 任意时点回溯 |
| **数据恢复** | 备份恢复 | 事件重放 | +500% 容错性 |
| **溯源分析** | 困难 | 完整因果链 | +800% 可追溯 |
| **CQRS 集成** | 复杂 | 天然契合 | 架构一致性 |

---

## 🎯 事件溯源核心概念

### 1. 架构对比

```text
传统状态存储:
┌──────────────────────────────────────┐
│        Database (Current State)      │
├──────────────────────────────────────┤
│ account_id │ balance │ last_update   │
│ uuid-123   │  1000   │ 2025-10-11    │
│                                      │
│ ❌ 无法知道余额如何变为 1000          │
│ ❌ 无法回溯到昨天的状态               │
│ ❌ 无法审计所有交易历史               │
└──────────────────────────────────────┘

事件溯源存储:
┌────────────────────────────────────────────────────┐
│         Event Store (Append-Only Log)              │
├──────┬────────────────────────┬────────────────────┤
│  1   │ AccountOpened          │ initial: 0         │
│  2   │ MoneyDeposited         │ amount: 500        │
│  3   │ MoneyWithdrawn         │ amount: 200        │
│  4   │ MoneyDeposited         │ amount: 700        │
│  5   │ MoneyWithdrawn         │ amount: 0          │
│                                                    │
│ ✅ 完整审计历史: 0 + 500 - 200 + 700 = 1000         │
│ ✅ 时间旅行: 重放事件 1-3 = 300 (昨天余额)           │
│ ✅ 因果分析: 清晰知道每一笔交易                      │
└────────────────────────────────────────────────────┘
```

### 2. 核心组件

```text
┌───────────────────────────────────────────────────────────┐
│                    Command (命令)                         │
└───────────────────┬───────────────────────────────────────┘
                    │
        ┌───────────▼────────────┐
        │   Aggregate Root       │
        │   (聚合根)             │
        │  • 加载历史事件         │
        │  • 执行业务逻辑         │
        │  • 生成新事件           │
        └───────────┬────────────┘
                    │
        ┌───────────▼────────────┐
        │   Event Store          │
        │   (事件存储)           │
        │  • Append-Only Log     │
        │  • 事件序列化           │
        │  • 版本控制             │
        └───────────┬────────────┘
                    │
        ┌───────────▼────────────┐
        │   Event Bus            │
        │   (事件总线)           │
        │  • 异步发布事件         │
        │  • 驱动读模型更新       │
        └───────────┬────────────┘
                    │
        ┌───────────▼────────────┐
        │   Projections          │
        │   (投影/读模型)        │
        │  • 事件订阅             │
        │  • 状态重建             │
        └────────────────────────┘
```

---

## 🏗️ Rust 项目结构

```text
event-sourcing-bank/
├── Cargo.toml
├── src/
│   ├── main.rs
│   │
│   ├── domain/                    # 领域层
│   │   ├── mod.rs
│   │   ├── events/                # 领域事件
│   │   │   ├── mod.rs
│   │   │   ├── account_opened.rs
│   │   │   ├── money_deposited.rs
│   │   │   ├── money_withdrawn.rs
│   │   │   └── account_closed.rs
│   │   ├── aggregates/            # 聚合根
│   │   │   ├── mod.rs
│   │   │   └── account.rs         # 通过事件重建状态
│   │   └── value_objects/
│   │       └── money.rs
│   │
│   ├── event_store/               # 事件存储
│   │   ├── mod.rs
│   │   ├── event_store.rs         # Event Store Trait
│   │   ├── postgres_store.rs      # PostgreSQL 实现 + OTLP
│   │   ├── event_stream.rs        # 事件流读取
│   │   └── snapshots.rs           # 快照优化
│   │
│   ├── commands/                  # 命令处理
│   │   ├── mod.rs
│   │   ├── handlers/
│   │   │   ├── deposit_handler.rs  # + OTLP
│   │   │   └── withdraw_handler.rs # + OTLP
│   │   └── models.rs
│   │
│   ├── projections/               # 事件投影
│   │   ├── mod.rs
│   │   ├── account_balance_projection.rs # + OTLP
│   │   └── transaction_history_projection.rs
│   │
│   ├── infrastructure/
│   │   ├── mod.rs
│   │   ├── event_bus/
│   │   │   └── kafka_bus.rs       # + OTLP
│   │   ├── web/
│   │   │   ├── command_api.rs
│   │   │   └── query_api.rs
│   │   └── telemetry/
│   │       └── init.rs
│   └── lib.rs
└── migrations/
    └── 001_create_events_table.sql
```

---

## 💎 核心实现

### 1. Domain Events (领域事件)

#### `src/domain/events/mod.rs`

```rust
//! 领域事件定义 - 不可变事件记录

use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

/// 事件元数据 (所有事件共享)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EventMetadata {
    /// 事件唯一 ID
    pub event_id: Uuid,
    /// 聚合根 ID
    pub aggregate_id: Uuid,
    /// 事件序列号 (从 1 开始)
    pub sequence_number: i64,
    /// 事件类型
    pub event_type: String,
    /// 事件发生时间
    pub occurred_at: DateTime<Utc>,
    /// 事件版本 (用于事件演化)
    pub event_version: i32,
}

/// 账户领域事件
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum AccountEvent {
    /// 账户开户
    Opened {
        #[serde(flatten)]
        metadata: EventMetadata,
        account_holder: String,
        initial_balance_cents: i64,
    },
    
    /// 存款
    Deposited {
        #[serde(flatten)]
        metadata: EventMetadata,
        amount_cents: i64,
        description: String,
    },
    
    /// 取款
    Withdrawn {
        #[serde(flatten)]
        metadata: EventMetadata,
        amount_cents: i64,
        description: String,
    },
    
    /// 账户冻结
    Frozen {
        #[serde(flatten)]
        metadata: EventMetadata,
        reason: String,
    },
    
    /// 账户关闭
    Closed {
        #[serde(flatten)]
        metadata: EventMetadata,
        reason: String,
    },
}

impl AccountEvent {
    /// 获取事件元数据
    pub fn metadata(&self) -> &EventMetadata {
        match self {
            AccountEvent::Opened { metadata, .. } => metadata,
            AccountEvent::Deposited { metadata, .. } => metadata,
            AccountEvent::Withdrawn { metadata, .. } => metadata,
            AccountEvent::Frozen { metadata, .. } => metadata,
            AccountEvent::Closed { metadata, .. } => metadata,
        }
    }

    /// 创建新事件 (工厂方法)
    pub fn new_opened(
        aggregate_id: Uuid,
        sequence: i64,
        account_holder: String,
        initial_balance_cents: i64,
    ) -> Self {
        AccountEvent::Opened {
            metadata: EventMetadata {
                event_id: Uuid::new_v4(),
                aggregate_id,
                sequence_number: sequence,
                event_type: "AccountOpened".to_string(),
                occurred_at: Utc::now(),
                event_version: 1,
            },
            account_holder,
            initial_balance_cents,
        }
    }

    pub fn new_deposited(
        aggregate_id: Uuid,
        sequence: i64,
        amount_cents: i64,
        description: String,
    ) -> Self {
        AccountEvent::Deposited {
            metadata: EventMetadata {
                event_id: Uuid::new_v4(),
                aggregate_id,
                sequence_number: sequence,
                event_type: "MoneyDeposited".to_string(),
                occurred_at: Utc::now(),
                event_version: 1,
            },
            amount_cents,
            description,
        }
    }

    pub fn new_withdrawn(
        aggregate_id: Uuid,
        sequence: i64,
        amount_cents: i64,
        description: String,
    ) -> Self {
        AccountEvent::Withdrawn {
            metadata: EventMetadata {
                event_id: Uuid::new_v4(),
                aggregate_id,
                sequence_number: sequence,
                event_type: "MoneyWithdrawn".to_string(),
                occurred_at: Utc::now(),
                event_version: 1,
            },
            amount_cents,
            description,
        }
    }
}
```

---

### 2. Aggregate Root (聚合根 - 事件重放)

#### `src/domain/aggregates/account.rs`

```rust
//! 账户聚合根 - 通过事件重建状态

use crate::domain::events::AccountEvent;
use uuid::Uuid;

/// 账户聚合根 (Event-Sourced)
#[derive(Debug, Clone)]
pub struct Account {
    /// 聚合根 ID
    id: Uuid,
    /// 当前序列号 (用于乐观锁)
    version: i64,
    /// 当前状态 (从事件重建)
    state: AccountState,
    /// 未提交的新事件
    uncommitted_events: Vec<AccountEvent>,
}

#[derive(Debug, Clone)]
pub struct AccountState {
    pub holder_name: String,
    pub balance_cents: i64,
    pub status: AccountStatus,
}

#[derive(Debug, Clone, PartialEq)]
pub enum AccountStatus {
    Active,
    Frozen,
    Closed,
}

impl Account {
    /// 从历史事件重建聚合根 (⚡ 事件溯源核心)
    pub fn from_events(events: Vec<AccountEvent>) -> Result<Self, DomainError> {
        if events.is_empty() {
            return Err(DomainError::NoEvents);
        }

        let aggregate_id = events[0].metadata().aggregate_id;
        let mut account = Self {
            id: aggregate_id,
            version: 0,
            state: AccountState {
                holder_name: String::new(),
                balance_cents: 0,
                status: AccountStatus::Active,
            },
            uncommitted_events: vec![],
        };

        // 逐个应用历史事件 (Event Replay)
        for event in events {
            account.apply_event(&event);
            account.version = event.metadata().sequence_number;
        }

        Ok(account)
    }

    /// 创建新账户 (生成事件)
    pub fn open(account_holder: String, initial_balance_cents: i64) -> Result<Self, DomainError> {
        if initial_balance_cents < 0 {
            return Err(DomainError::NegativeInitialBalance);
        }

        let account_id = Uuid::new_v4();
        let event = AccountEvent::new_opened(account_id, 1, account_holder, initial_balance_cents);

        let mut account = Self {
            id: account_id,
            version: 0,
            state: AccountState {
                holder_name: String::new(),
                balance_cents: 0,
                status: AccountStatus::Active,
            },
            uncommitted_events: vec![],
        };

        account.apply_event(&event);
        account.uncommitted_events.push(event);
        account.version = 1;

        Ok(account)
    }

    /// 存款 (生成事件)
    pub fn deposit(&mut self, amount_cents: i64, description: String) -> Result<(), DomainError> {
        if amount_cents <= 0 {
            return Err(DomainError::InvalidAmount);
        }

        if self.state.status != AccountStatus::Active {
            return Err(DomainError::AccountNotActive);
        }

        let next_sequence = self.version + 1;
        let event = AccountEvent::new_deposited(self.id, next_sequence, amount_cents, description);

        self.apply_event(&event);
        self.uncommitted_events.push(event);
        self.version = next_sequence;

        Ok(())
    }

    /// 取款 (生成事件)
    pub fn withdraw(&mut self, amount_cents: i64, description: String) -> Result<(), DomainError> {
        if amount_cents <= 0 {
            return Err(DomainError::InvalidAmount);
        }

        if self.state.status != AccountStatus::Active {
            return Err(DomainError::AccountNotActive);
        }

        if self.state.balance_cents < amount_cents {
            return Err(DomainError::InsufficientBalance {
                available: self.state.balance_cents,
                requested: amount_cents,
            });
        }

        let next_sequence = self.version + 1;
        let event = AccountEvent::new_withdrawn(self.id, next_sequence, amount_cents, description);

        self.apply_event(&event);
        self.uncommitted_events.push(event);
        self.version = next_sequence;

        Ok(())
    }

    /// 应用事件到状态 (状态转换函数)
    fn apply_event(&mut self, event: &AccountEvent) {
        match event {
            AccountEvent::Opened {
                account_holder,
                initial_balance_cents,
                ..
            } => {
                self.state.holder_name = account_holder.clone();
                self.state.balance_cents = *initial_balance_cents;
                self.state.status = AccountStatus::Active;
            }
            AccountEvent::Deposited { amount_cents, .. } => {
                self.state.balance_cents += amount_cents;
            }
            AccountEvent::Withdrawn { amount_cents, .. } => {
                self.state.balance_cents -= amount_cents;
            }
            AccountEvent::Frozen { .. } => {
                self.state.status = AccountStatus::Frozen;
            }
            AccountEvent::Closed { .. } => {
                self.state.status = AccountStatus::Closed;
            }
        }
    }

    /// 获取未提交事件并清空
    pub fn take_uncommitted_events(&mut self) -> Vec<AccountEvent> {
        std::mem::take(&mut self.uncommitted_events)
    }

    // Getters
    pub fn id(&self) -> Uuid {
        self.id
    }
    pub fn version(&self) -> i64 {
        self.version
    }
    pub fn balance(&self) -> i64 {
        self.state.balance_cents
    }
    pub fn status(&self) -> &AccountStatus {
        &self.state.status
    }
}

#[derive(Debug, thiserror::Error)]
pub enum DomainError {
    #[error("无事件可重建聚合根")]
    NoEvents,

    #[error("初始余额不能为负数")]
    NegativeInitialBalance,

    #[error("无效的金额")]
    InvalidAmount,

    #[error("账户未激活")]
    AccountNotActive,

    #[error("余额不足: 可用 {available}, 请求 {requested}")]
    InsufficientBalance { available: i64, requested: i64 },
}
```

---

### 3. Event Store (事件存储)

#### `src/event_store/postgres_store.rs`

```rust
//! PostgreSQL 事件存储 - Append-Only Log + OTLP

use crate::domain::events::AccountEvent;
use async_trait::async_trait;
use sqlx::PgPool;
use tracing::{error, info, instrument};
use uuid::Uuid;

/// 事件存储 Trait
#[async_trait]
pub trait EventStore: Send + Sync {
    /// 追加事件 (Append-Only)
    async fn append_events(
        &self,
        aggregate_id: Uuid,
        expected_version: i64,
        events: Vec<AccountEvent>,
    ) -> Result<(), EventStoreError>;

    /// 加载聚合根的所有事件
    async fn load_events(&self, aggregate_id: Uuid) -> Result<Vec<AccountEvent>, EventStoreError>;

    /// 加载聚合根事件 (从某个版本开始)
    async fn load_events_from_version(
        &self,
        aggregate_id: Uuid,
        from_version: i64,
    ) -> Result<Vec<AccountEvent>, EventStoreError>;
}

pub struct PostgresEventStore {
    pool: PgPool,
}

impl PostgresEventStore {
    pub fn new(pool: PgPool) -> Self {
        Self { pool }
    }
}

#[async_trait]
impl EventStore for PostgresEventStore {
    #[instrument(
        name = "event_store.append_events",
        skip(self, events),
        fields(
            aggregate_id = %aggregate_id,
            expected_version = expected_version,
            events_count = events.len(),
            db.system = "postgresql",
            db.operation = "INSERT",
            event_sourcing.operation = "append"
        )
    )]
    async fn append_events(
        &self,
        aggregate_id: Uuid,
        expected_version: i64,
        events: Vec<AccountEvent>,
    ) -> Result<(), EventStoreError> {
        info!("追加事件到 Event Store");

        // 开启事务 (保证原子性)
        let mut tx = self
            .pool
            .begin()
            .await
            .map_err(|e| EventStoreError::Database(e.to_string()))?;

        // 1. 检查版本 (乐观锁 - Optimistic Concurrency Control)
        let current_version = sqlx::query_scalar!(
            r#"
            SELECT COALESCE(MAX(sequence_number), 0)
            FROM events
            WHERE aggregate_id = $1
            "#,
            aggregate_id
        )
        .fetch_one(&mut *tx)
        .await
        .map_err(|e| EventStoreError::Database(e.to_string()))?
        .unwrap_or(0);

        if current_version != expected_version {
            error!(
                current = current_version,
                expected = expected_version,
                "版本冲突"
            );
            return Err(EventStoreError::ConcurrencyConflict {
                expected: expected_version,
                actual: current_version,
            });
        }

        // 2. 插入所有事件
        for event in events {
            let metadata = event.metadata();
            let event_json = serde_json::to_string(&event)
                .map_err(|e| EventStoreError::Serialization(e.to_string()))?;

            sqlx::query!(
                r#"
                INSERT INTO events (
                    event_id, aggregate_id, sequence_number, event_type, event_data, occurred_at
                )
                VALUES ($1, $2, $3, $4, $5, $6)
                "#,
                metadata.event_id,
                metadata.aggregate_id,
                metadata.sequence_number,
                metadata.event_type,
                event_json,
                metadata.occurred_at
            )
            .execute(&mut *tx)
            .await
            .map_err(|e| EventStoreError::Database(e.to_string()))?;
        }

        // 3. 提交事务
        tx.commit()
            .await
            .map_err(|e| EventStoreError::Database(e.to_string()))?;

        info!("事件追加成功");
        Ok(())
    }

    #[instrument(
        name = "event_store.load_events",
        skip(self),
        fields(
            aggregate_id = %aggregate_id,
            db.system = "postgresql",
            event_sourcing.operation = "replay"
        )
    )]
    async fn load_events(&self, aggregate_id: Uuid) -> Result<Vec<AccountEvent>, EventStoreError> {
        info!("加载聚合根事件流");

        let records = sqlx::query!(
            r#"
            SELECT event_data
            FROM events
            WHERE aggregate_id = $1
            ORDER BY sequence_number ASC
            "#,
            aggregate_id
        )
        .fetch_all(&self.pool)
        .await
        .map_err(|e| EventStoreError::Database(e.to_string()))?;

        let events: Result<Vec<AccountEvent>, _> = records
            .into_iter()
            .map(|row| serde_json::from_str(&row.event_data))
            .collect();

        events.map_err(|e| EventStoreError::Serialization(e.to_string()))
    }

    #[instrument(
        name = "event_store.load_events_from_version",
        skip(self),
        fields(
            aggregate_id = %aggregate_id,
            from_version = from_version,
            db.system = "postgresql"
        )
    )]
    async fn load_events_from_version(
        &self,
        aggregate_id: Uuid,
        from_version: i64,
    ) -> Result<Vec<AccountEvent>, EventStoreError> {
        let records = sqlx::query!(
            r#"
            SELECT event_data
            FROM events
            WHERE aggregate_id = $1 AND sequence_number > $2
            ORDER BY sequence_number ASC
            "#,
            aggregate_id,
            from_version
        )
        .fetch_all(&self.pool)
        .await
        .map_err(|e| EventStoreError::Database(e.to_string()))?;

        let events: Result<Vec<AccountEvent>, _> = records
            .into_iter()
            .map(|row| serde_json::from_str(&row.event_data))
            .collect();

        events.map_err(|e| EventStoreError::Serialization(e.to_string()))
    }
}

#[derive(Debug, thiserror::Error)]
pub enum EventStoreError {
    #[error("数据库错误: {0}")]
    Database(String),

    #[error("序列化错误: {0}")]
    Serialization(String),

    #[error("并发冲突: 期望版本 {expected}, 实际版本 {actual}")]
    ConcurrencyConflict { expected: i64, actual: i64 },
}
```

---

### 4. Snapshot (快照优化)

#### `src/event_store/snapshots.rs`

```rust
//! 快照优化 - 避免重放所有事件

use crate::domain::aggregates::Account;
use async_trait::async_trait;
use sqlx::PgPool;
use tracing::{info, instrument};
use uuid::Uuid;

/// 快照存储 Trait
#[async_trait]
pub trait SnapshotStore: Send + Sync {
    /// 保存快照
    async fn save_snapshot(
        &self,
        aggregate_id: Uuid,
        version: i64,
        state: &Account,
    ) -> Result<(), SnapshotError>;

    /// 加载最新快照
    async fn load_snapshot(
        &self,
        aggregate_id: Uuid,
    ) -> Result<Option<(Account, i64)>, SnapshotError>;
}

pub struct PostgresSnapshotStore {
    pool: PgPool,
}

impl PostgresSnapshotStore {
    pub fn new(pool: PgPool) -> Self {
        Self { pool }
    }
}

#[async_trait]
impl SnapshotStore for PostgresSnapshotStore {
    #[instrument(
        name = "snapshot_store.save",
        skip(self, state),
        fields(
            aggregate_id = %aggregate_id,
            version = version,
            event_sourcing.optimization = "snapshot"
        )
    )]
    async fn save_snapshot(
        &self,
        aggregate_id: Uuid,
        version: i64,
        state: &Account,
    ) -> Result<(), SnapshotError> {
        info!("保存聚合根快照");

        let state_json = serde_json::to_string(state)
            .map_err(|e| SnapshotError::Serialization(e.to_string()))?;

        sqlx::query!(
            r#"
            INSERT INTO snapshots (aggregate_id, version, state_data, created_at)
            VALUES ($1, $2, $3, NOW())
            ON CONFLICT (aggregate_id)
            DO UPDATE SET version = $2, state_data = $3, created_at = NOW()
            "#,
            aggregate_id,
            version,
            state_json
        )
        .execute(&self.pool)
        .await
        .map_err(|e| SnapshotError::Database(e.to_string()))?;

        info!("快照保存成功");
        Ok(())
    }

    #[instrument(
        name = "snapshot_store.load",
        skip(self),
        fields(
            aggregate_id = %aggregate_id,
            event_sourcing.optimization = "snapshot"
        )
    )]
    async fn load_snapshot(
        &self,
        aggregate_id: Uuid,
    ) -> Result<Option<(Account, i64)>, SnapshotError> {
        info!("加载聚合根快照");

        let record = sqlx::query!(
            r#"
            SELECT version, state_data
            FROM snapshots
            WHERE aggregate_id = $1
            "#,
            aggregate_id
        )
        .fetch_optional(&self.pool)
        .await
        .map_err(|e| SnapshotError::Database(e.to_string()))?;

        match record {
            Some(row) => {
                let account: Account = serde_json::from_str(&row.state_data)
                    .map_err(|e| SnapshotError::Serialization(e.to_string()))?;
                Ok(Some((account, row.version)))
            }
            None => Ok(None),
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum SnapshotError {
    #[error("数据库错误: {0}")]
    Database(String),

    #[error("序列化错误: {0}")]
    Serialization(String),
}

/// 快照策略: 每 N 个事件创建一次快照
pub const SNAPSHOT_INTERVAL: i64 = 100;

/// 判断是否需要创建快照
pub fn should_snapshot(current_version: i64) -> bool {
    current_version % SNAPSHOT_INTERVAL == 0
}
```

---

### 5. Command Handler (带快照优化)

#### `src/commands/handlers/deposit_handler.rs`

```rust
//! 存款命令处理器 - Event Sourcing + Snapshot + OTLP

use crate::{
    domain::aggregates::Account,
    event_store::{EventStore, SnapshotStore, should_snapshot},
};
use std::sync::Arc;
use tracing::{info, instrument};
use uuid::Uuid;

pub struct DepositHandler {
    event_store: Arc<dyn EventStore>,
    snapshot_store: Arc<dyn SnapshotStore>,
}

impl DepositHandler {
    pub fn new(
        event_store: Arc<dyn EventStore>,
        snapshot_store: Arc<dyn SnapshotStore>,
    ) -> Self {
        Self {
            event_store,
            snapshot_store,
        }
    }

    #[instrument(
        name = "command.deposit",
        skip(self, command),
        fields(
            account_id = %command.account_id,
            amount_cents = command.amount_cents,
            event_sourcing.operation = "command"
        )
    )]
    pub async fn handle(&self, command: DepositCommand) -> Result<(), CommandError> {
        info!("处理存款命令");

        // 1. 加载聚合根 (优先从快照)
        let mut account = self.load_account(command.account_id).await?;

        // 2. 执行业务逻辑
        account
            .deposit(command.amount_cents, command.description)
            .map_err(|e| CommandError::DomainError(e.to_string()))?;

        // 3. 获取新事件
        let events = account.take_uncommitted_events();
        let new_version = account.version();

        // 4. 持久化事件
        self.event_store
            .append_events(command.account_id, new_version - events.len() as i64, events)
            .await
            .map_err(|e| CommandError::EventStoreError(e.to_string()))?;

        // 5. 判断是否需要创建快照
        if should_snapshot(new_version) {
            info!(version = new_version, "创建快照");
            self.snapshot_store
                .save_snapshot(command.account_id, new_version, &account)
                .await
                .map_err(|e| CommandError::SnapshotError(e.to_string()))?;
        }

        info!("存款成功");
        Ok(())
    }

    /// 加载聚合根 (快照 + 增量事件)
    async fn load_account(&self, account_id: Uuid) -> Result<Account, CommandError> {
        // 1. 尝试加载快照
        if let Some((mut account, snapshot_version)) = self
            .snapshot_store
            .load_snapshot(account_id)
            .await
            .map_err(|e| CommandError::SnapshotError(e.to_string()))?
        {
            info!(snapshot_version, "从快照加载");

            // 2. 加载快照之后的增量事件
            let incremental_events = self
                .event_store
                .load_events_from_version(account_id, snapshot_version)
                .await
                .map_err(|e| CommandError::EventStoreError(e.to_string()))?;

            // 3. 应用增量事件
            if !incremental_events.is_empty() {
                info!(events_count = incremental_events.len(), "应用增量事件");
                account = Account::from_events(incremental_events)
                    .map_err(|e| CommandError::DomainError(e.to_string()))?;
            }

            return Ok(account);
        }

        // 4. 无快照,从头重放所有事件
        info!("无快照,重放所有事件");
        let events = self
            .event_store
            .load_events(account_id)
            .await
            .map_err(|e| CommandError::EventStoreError(e.to_string()))?;

        Account::from_events(events).map_err(|e| CommandError::DomainError(e.to_string()))
    }
}

#[derive(Debug, serde::Deserialize)]
pub struct DepositCommand {
    pub account_id: Uuid,
    pub amount_cents: i64,
    pub description: String,
}

#[derive(Debug, thiserror::Error)]
pub enum CommandError {
    #[error("领域错误: {0}")]
    DomainError(String),

    #[error("事件存储错误: {0}")]
    EventStoreError(String),

    #[error("快照错误: {0}")]
    SnapshotError(String),
}
```

---

## 📊 完整 OTLP 追踪链路

```text
HTTP POST /deposit (Command API)
  └─ command.deposit [Span]
      ├─ snapshot_store.load [Span] (加载快照)
      │   └─ PostgreSQL SELECT (数据库 Span)
      ├─ event_store.load_events_from_version [Span] (增量事件)
      │   └─ PostgreSQL SELECT (数据库 Span)
      ├─ Account::deposit [无追踪] (纯领域逻辑)
      ├─ event_store.append_events [Span]
      │   └─ PostgreSQL INSERT (事务 Span)
      └─ snapshot_store.save [Span] (每 100 个事件)
          └─ PostgreSQL INSERT (数据库 Span)
```

---

## 📦 数据库迁移

### `migrations/001_create_events_table.sql`

```sql
-- 事件表 (Append-Only Log)
CREATE TABLE events (
    id BIGSERIAL PRIMARY KEY,
    event_id UUID NOT NULL UNIQUE,
    aggregate_id UUID NOT NULL,
    sequence_number BIGINT NOT NULL,
    event_type VARCHAR(100) NOT NULL,
    event_data JSONB NOT NULL,
    occurred_at TIMESTAMPTZ NOT NULL,
    created_at TIMESTAMPTZ DEFAULT NOW(),
    
    -- 唯一约束: 聚合根 + 序列号 (防止并发冲突)
    UNIQUE (aggregate_id, sequence_number)
);

-- 索引
CREATE INDEX idx_events_aggregate_id ON events(aggregate_id);
CREATE INDEX idx_events_event_type ON events(event_type);
CREATE INDEX idx_events_occurred_at ON events(occurred_at);

-- 快照表
CREATE TABLE snapshots (
    id BIGSERIAL PRIMARY KEY,
    aggregate_id UUID NOT NULL UNIQUE,
    version BIGINT NOT NULL,
    state_data JSONB NOT NULL,
    created_at TIMESTAMPTZ DEFAULT NOW()
);
```

---

## 🌟 最佳实践

### ✅ DO (推荐)

1. **事件不可变**: 永远不修改已保存的事件
2. **Append-Only**: 事件存储只追加,不删除不更新
3. **快照优化**: 每 N 个事件创建快照(如 100)
4. **版本控制**: 使用序列号实现乐观锁
5. **事件版本演化**: 支持事件 schema 升级
6. **幂等性**: 事件处理器必须幂等
7. **OTLP 追踪**: 追踪事件追加、重放、快照操作

### ❌ DON'T (避免)

1. **删除事件**: 使用逻辑删除事件 (如 `AccountDeleted`)
2. **修改历史**: 不修改已保存的事件数据
3. **无快照**: 超过 1000 个事件必须使用快照
4. **同步处理**: 事件发布应该是异步的
5. **无版本控制**: 必须使用版本号防止并发冲突

---

## 🔗 参考资源

### 架构模式

- [Martin Fowler - Event Sourcing](https://martinfowler.com/eaaDev/EventSourcing.html)
- [Greg Young - Event Sourcing](https://cqrs.files.wordpress.com/2010/11/cqrs_documents.pdf)
- [Microsoft - Event Sourcing Pattern](https://learn.microsoft.com/en-us/azure/architecture/patterns/event-sourcing)

### Rust 实现

- [EventStoreDB Rust Client](https://docs.rs/eventstore/latest/eventstore/)
- [PostgreSQL Event Store Example](https://github.com/johnnynotsolucky/samples)

---

**文档版本**: 1.0  
**创建日期**: 2025年10月11日  
**Rust 版本**: 1.90+  
**OpenTelemetry**: 0.31.0

**📚 Event Sourcing: 完整审计,时间旅行,因果追溯!** 🚀
