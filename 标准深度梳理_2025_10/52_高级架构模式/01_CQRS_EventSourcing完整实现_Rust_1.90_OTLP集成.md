# CQRS + Event Sourcing 完整实现指南

## 目录

- [CQRS + Event Sourcing 完整实现指南](#cqrs--event-sourcing-完整实现指南)
  - [目录](#目录)
  - [1. CQRS + Event Sourcing 概述](#1-cqrs--event-sourcing-概述)
    - [1.1 什么是 CQRS?](#11-什么是-cqrs)
    - [1.2 什么是 Event Sourcing?](#12-什么是-event-sourcing)
    - [1.3 CQRS + ES 优势](#13-cqrs--es-优势)
  - [2. 核心架构](#2-核心架构)
  - [3. 项目设置](#3-项目设置)
    - [3.1 Cargo.toml](#31-cargotoml)
  - [4. Event Sourcing 实现](#4-event-sourcing-实现)
    - [4.1 领域事件](#41-领域事件)
    - [4.2 聚合根 (Aggregate)](#42-聚合根-aggregate)
  - [5. CQRS 实现](#5-cqrs-实现)
    - [5.1 命令处理器](#51-命令处理器)
    - [5.2 查询模型](#52-查询模型)
  - [6. Event Store 实现](#6-event-store-实现)
    - [6.1 PostgreSQL Event Store](#61-postgresql-event-store)
  - [7. 投影 (Projections)](#7-投影-projections)
    - [7.1 账户投影](#71-账户投影)
  - [8. Saga 模式](#8-saga-模式)
    - [8.1 转账 Saga](#81-转账-saga)
  - [9. OTLP 可观测性集成](#9-otlp-可观测性集成)
    - [9.1 命令追踪](#91-命令追踪)
  - [10. 测试策略](#10-测试策略)
    - [10.1 聚合测试](#101-聚合测试)
  - [11. 生产实践](#11-生产实践)
    - [11.1 Docker Compose 部署](#111-docker-compose-部署)
  - [12. 国际标准对齐](#12-国际标准对齐)
    - [12.1 CQRS 模式](#121-cqrs-模式)
    - [12.2 OpenTelemetry 语义约定](#122-opentelemetry-语义约定)
  - [总结](#总结)

---

## 1. CQRS + Event Sourcing 概述

### 1.1 什么是 CQRS?

**CQRS (Command Query Responsibility Segregation)** 分离命令和查询的职责:

- **Command (命令)**: 修改状态的操作 (Create, Update, Delete)
- **Query (查询)**: 读取状态的操作 (Read)
- **职责分离**: 写入和读取使用不同的模型

### 1.2 什么是 Event Sourcing?

**Event Sourcing** 将所有状态变更存储为事件序列:

- **事件日志**: 不可变的事件流
- **状态重建**: 通过重放事件恢复状态
- **审计追踪**: 完整的历史记录
- **时间旅行**: 查询任意时间点的状态

### 1.3 CQRS + ES 优势

| 特性 | CRUD | CQRS + ES |
|------|------|-----------|
| **读写分离** | ❌ 同一模型 | ✅ 独立优化 |
| **审计追踪** | ⚠️ 需额外实现 | ✅ 原生支持 |
| **性能** | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| **复杂度** | ⭐ | ⭐⭐⭐⭐ |
| **可扩展性** | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ |

---

## 2. 核心架构

```text
┌─────────────────────────────────────────────────────────────┐
│                  CQRS + Event Sourcing 架构                  │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  ┌────────────┐         ┌────────────────────┐             │
│  │  Command   │────────>│  Command Handler   │             │
│  │   (写入)   │         │  (业务逻辑)         │             │
│  └────────────┘         └──────────┬─────────┘             │
│                                    │                        │
│                                    ▼                        │
│                         ┌────────────────────┐             │
│                         │    Event Store     │             │
│                         │  (事件日志)         │             │
│                         └──────────┬─────────┘             │
│                                    │                        │
│                          ┌─────────┴─────────┐             │
│                          │                   │             │
│                          ▼                   ▼             │
│                  ┌───────────────┐   ┌──────────────┐     │
│                  │  Projection 1 │   │ Projection 2 │     │
│                  │  (读取模型1)   │   │ (读取模型2)   │     │
│                  └───────────────┘   └──────────────┘     │
│                          │                   │             │
│  ┌────────────┐          │                   │             │
│  │   Query    │<─────────┴───────────────────┘             │
│  │   (读取)   │                                            │
│  └────────────┘                                            │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

---

## 3. 项目设置

### 3.1 Cargo.toml

```toml
[package]
name = "cqrs-es-example"
version = "0.1.0"
edition = "2021"

[dependencies]
# 异步运行时
tokio = { version = "1", features = ["full"] }

# CQRS/ES 框架
cqrs-es = "0.4"
async-trait = "0.1"

# 序列化
serde = { version = "1", features = ["derive"] }
serde_json = "1"

# 数据库
sqlx = { version = "0.8", features = ["runtime-tokio-rustls", "postgres", "uuid", "chrono", "json"] }

# 消息队列 (Event Bus)
rdkafka = { version = "0.36", features = ["ssl", "tracing"] }

# UUID
uuid = { version = "1", features = ["v4", "serde"] }

# 时间处理
chrono = { version = "0.4", features = ["serde"] }

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
```

---

## 4. Event Sourcing 实现

### 4.1 领域事件

```rust
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use uuid::Uuid;

/// 账户事件
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum AccountEvent {
    AccountOpened {
        account_id: Uuid,
        owner_name: String,
        initial_balance: i64,
        opened_at: DateTime<Utc>,
    },
    MoneyDeposited {
        amount: i64,
        deposited_at: DateTime<Utc>,
    },
    MoneyWithdrawn {
        amount: i64,
        withdrawn_at: DateTime<Utc>,
    },
    AccountClosed {
        closed_at: DateTime<Utc>,
    },
}

/// 事件元数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EventMetadata {
    pub event_id: Uuid,
    pub aggregate_id: Uuid,
    pub sequence: u64,
    pub timestamp: DateTime<Utc>,
    pub correlation_id: Option<Uuid>,
    pub causation_id: Option<Uuid>,
}

/// 事件包装
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EventEnvelope<E> {
    pub metadata: EventMetadata,
    pub event: E,
}
```

### 4.2 聚合根 (Aggregate)

```rust
use cqrs_es::{Aggregate, AggregateError};

/// 账户聚合
#[derive(Debug, Clone, Default)]
pub struct Account {
    pub account_id: Option<Uuid>,
    pub owner_name: String,
    pub balance: i64,
    pub is_active: bool,
}

impl Aggregate for Account {
    type Command = AccountCommand;
    type Event = AccountEvent;
    type Error = AccountError;
    type Services = ();

    fn aggregate_type() -> String {
        "account".to_string()
    }

    /// 处理命令 (Command Handler)
    fn handle(
        &self,
        command: Self::Command,
        _services: &Self::Services,
    ) -> Result<Vec<Self::Event>, Self::Error> {
        use AccountCommand::*;
        use AccountEvent::*;

        match command {
            OpenAccount { account_id, owner_name, initial_balance } => {
                // 验证
                if self.account_id.is_some() {
                    return Err(AccountError::AccountAlreadyExists);
                }
                if initial_balance < 0 {
                    return Err(AccountError::InvalidAmount);
                }

                // 生成事件
                Ok(vec![AccountOpened {
                    account_id,
                    owner_name,
                    initial_balance,
                    opened_at: Utc::now(),
                }])
            }

            DepositMoney { amount } => {
                if !self.is_active {
                    return Err(AccountError::AccountClosed);
                }
                if amount <= 0 {
                    return Err(AccountError::InvalidAmount);
                }

                Ok(vec![MoneyDeposited {
                    amount,
                    deposited_at: Utc::now(),
                }])
            }

            WithdrawMoney { amount } => {
                if !self.is_active {
                    return Err(AccountError::AccountClosed);
                }
                if amount <= 0 {
                    return Err(AccountError::InvalidAmount);
                }
                if self.balance < amount {
                    return Err(AccountError::InsufficientFunds);
                }

                Ok(vec![MoneyWithdrawn {
                    amount,
                    withdrawn_at: Utc::now(),
                }])
            }

            CloseAccount => {
                if !self.is_active {
                    return Err(AccountError::AccountClosed);
                }
                if self.balance != 0 {
                    return Err(AccountError::BalanceNotZero);
                }

                Ok(vec![AccountClosed {
                    closed_at: Utc::now(),
                }])
            }
        }
    }

    /// 应用事件 (Event Sourcing)
    fn apply(&mut self, event: Self::Event) {
        use AccountEvent::*;

        match event {
            AccountOpened { account_id, owner_name, initial_balance, .. } => {
                self.account_id = Some(account_id);
                self.owner_name = owner_name;
                self.balance = initial_balance;
                self.is_active = true;
            }
            MoneyDeposited { amount, .. } => {
                self.balance += amount;
            }
            MoneyWithdrawn { amount, .. } => {
                self.balance -= amount;
            }
            AccountClosed { .. } => {
                self.is_active = false;
            }
        }
    }
}

/// 账户命令
#[derive(Debug, Clone)]
pub enum AccountCommand {
    OpenAccount {
        account_id: Uuid,
        owner_name: String,
        initial_balance: i64,
    },
    DepositMoney {
        amount: i64,
    },
    WithdrawMoney {
        amount: i64,
    },
    CloseAccount,
}

/// 账户错误
#[derive(Debug, thiserror::Error)]
pub enum AccountError {
    #[error("Account already exists")]
    AccountAlreadyExists,
    #[error("Account is closed")]
    AccountClosed,
    #[error("Invalid amount")]
    InvalidAmount,
    #[error("Insufficient funds")]
    InsufficientFunds,
    #[error("Balance must be zero to close account")]
    BalanceNotZero,
}
```

---

## 5. CQRS 实现

### 5.1 命令处理器

```rust
use cqrs_es::CqrsFramework;
use std::sync::Arc;

/// 命令服务
pub struct AccountCommandService {
    cqrs: Arc<CqrsFramework<Account, PostgresEventStore>>,
}

impl AccountCommandService {
    pub fn new(event_store: PostgresEventStore) -> Self {
        let cqrs = CqrsFramework::new(event_store, vec![], ());
        Self {
            cqrs: Arc::new(cqrs),
        }
    }

    /// 执行命令
    pub async fn execute(
        &self,
        aggregate_id: &str,
        command: AccountCommand,
    ) -> Result<(), AccountError> {
        self.cqrs.execute(aggregate_id, command).await?;
        Ok(())
    }

    /// 加载聚合
    pub async fn load(&self, aggregate_id: &str) -> Result<Account, AccountError> {
        let aggregate = self.cqrs.load(aggregate_id).await?;
        Ok(aggregate)
    }
}
```

### 5.2 查询模型

```rust
use sqlx::{PgPool, FromRow};

/// 账户查询模型 (读取优化)
#[derive(Debug, Clone, FromRow)]
pub struct AccountQueryModel {
    pub account_id: Uuid,
    pub owner_name: String,
    pub balance: i64,
    pub is_active: bool,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

/// 查询服务
pub struct AccountQueryService {
    pool: PgPool,
}

impl AccountQueryService {
    pub fn new(pool: PgPool) -> Self {
        Self { pool }
    }

    /// 获取账户
    pub async fn get_account(&self, account_id: Uuid) -> Result<Option<AccountQueryModel>, sqlx::Error> {
        sqlx::query_as!(
            AccountQueryModel,
            r#"
            SELECT account_id, owner_name, balance, is_active, created_at, updated_at
            FROM account_query_model
            WHERE account_id = $1
            "#,
            account_id
        )
        .fetch_optional(&self.pool)
        .await
    }

    /// 列出所有活跃账户
    pub async fn list_active_accounts(&self) -> Result<Vec<AccountQueryModel>, sqlx::Error> {
        sqlx::query_as!(
            AccountQueryModel,
            r#"
            SELECT account_id, owner_name, balance, is_active, created_at, updated_at
            FROM account_query_model
            WHERE is_active = true
            ORDER BY created_at DESC
            "#
        )
        .fetch_all(&self.pool)
        .await
    }

    /// 获取总余额
    pub async fn get_total_balance(&self) -> Result<i64, sqlx::Error> {
        let result: (Option<i64>,) = sqlx::query_as(
            "SELECT COALESCE(SUM(balance), 0) FROM account_query_model WHERE is_active = true"
        )
        .fetch_one(&self.pool)
        .await?;

        Ok(result.0.unwrap_or(0))
    }
}
```

---

## 6. Event Store 实现

### 6.1 PostgreSQL Event Store

```rust
use cqrs_es::{EventStore, EventEnvelope};
use sqlx::{PgPool, Postgres, Transaction};
use async_trait::async_trait;

pub struct PostgresEventStore {
    pool: PgPool,
}

impl PostgresEventStore {
    pub fn new(pool: PgPool) -> Self {
        Self { pool }
    }

    /// 初始化数据库表
    pub async fn init_schema(&self) -> Result<(), sqlx::Error> {
        sqlx::query(
            r#"
            CREATE TABLE IF NOT EXISTS events (
                aggregate_type TEXT NOT NULL,
                aggregate_id TEXT NOT NULL,
                sequence BIGINT NOT NULL,
                event_type TEXT NOT NULL,
                event_version TEXT NOT NULL,
                payload JSONB NOT NULL,
                metadata JSONB NOT NULL,
                timestamp TIMESTAMPTZ NOT NULL DEFAULT NOW(),
                PRIMARY KEY (aggregate_type, aggregate_id, sequence)
            )
            "#
        )
        .execute(&self.pool)
        .await?;

        // 创建索引
        sqlx::query(
            "CREATE INDEX IF NOT EXISTS idx_events_aggregate ON events(aggregate_type, aggregate_id)"
        )
        .execute(&self.pool)
        .await?;

        Ok(())
    }
}

#[async_trait]
impl EventStore for PostgresEventStore {
    type Aggregate = Account;

    async fn load_events(
        &self,
        aggregate_id: &str,
    ) -> Result<Vec<EventEnvelope<AccountEvent>>, cqrs_es::persist::PersistenceError> {
        let rows = sqlx::query_as!(
            EventRow,
            r#"
            SELECT aggregate_id, sequence, payload, metadata, timestamp
            FROM events
            WHERE aggregate_type = 'account' AND aggregate_id = $1
            ORDER BY sequence
            "#,
            aggregate_id
        )
        .fetch_all(&self.pool)
        .await?;

        let envelopes = rows.into_iter()
            .map(|row| {
                let event: AccountEvent = serde_json::from_value(row.payload)?;
                let metadata: EventMetadata = serde_json::from_value(row.metadata)?;
                Ok(EventEnvelope { metadata, event })
            })
            .collect::<Result<Vec<_>, serde_json::Error>>()?;

        Ok(envelopes)
    }

    async fn save_events(
        &self,
        aggregate_id: &str,
        events: &[EventEnvelope<AccountEvent>],
        expected_version: u64,
    ) -> Result<(), cqrs_es::persist::PersistenceError> {
        let mut tx = self.pool.begin().await?;

        // 检查版本
        let current_version: Option<(i64,)> = sqlx::query_as(
            "SELECT MAX(sequence) FROM events WHERE aggregate_type = 'account' AND aggregate_id = $1"
        )
        .bind(aggregate_id)
        .fetch_optional(&mut *tx)
        .await?;

        let current = current_version.and_then(|(v,)| v).unwrap_or(-1) as u64;

        if current != expected_version {
            return Err(cqrs_es::persist::PersistenceError::OptimisticLockError);
        }

        // 插入事件
        for envelope in events {
            sqlx::query(
                r#"
                INSERT INTO events (aggregate_type, aggregate_id, sequence, event_type, event_version, payload, metadata, timestamp)
                VALUES ('account', $1, $2, $3, '1.0', $4, $5, $6)
                "#
            )
            .bind(aggregate_id)
            .bind(envelope.metadata.sequence as i64)
            .bind(format!("{:?}", envelope.event))
            .bind(serde_json::to_value(&envelope.event)?)
            .bind(serde_json::to_value(&envelope.metadata)?)
            .bind(envelope.metadata.timestamp)
            .execute(&mut *tx)
            .await?;
        }

        tx.commit().await?;

        Ok(())
    }
}

#[derive(sqlx::FromRow)]
struct EventRow {
    aggregate_id: String,
    sequence: i64,
    payload: serde_json::Value,
    metadata: serde_json::Value,
    timestamp: DateTime<Utc>,
}
```

---

## 7. 投影 (Projections)

### 7.1 账户投影

```rust
use cqrs_es::persist::{GenericQuery, ViewRepository};
use async_trait::async_trait;

pub struct AccountProjection {
    pool: PgPool,
}

impl AccountProjection {
    pub fn new(pool: PgPool) -> Self {
        Self { pool }
    }

    /// 初始化投影表
    pub async fn init_schema(&self) -> Result<(), sqlx::Error> {
        sqlx::query(
            r#"
            CREATE TABLE IF NOT EXISTS account_query_model (
                account_id UUID PRIMARY KEY,
                owner_name TEXT NOT NULL,
                balance BIGINT NOT NULL,
                is_active BOOLEAN NOT NULL,
                created_at TIMESTAMPTZ NOT NULL,
                updated_at TIMESTAMPTZ NOT NULL
            )
            "#
        )
        .execute(&self.pool)
        .await?;

        Ok(())
    }
}

#[async_trait]
impl GenericQuery for AccountProjection {
    type Aggregate = Account;

    async fn dispatch(
        &self,
        aggregate_id: &str,
        events: &[EventEnvelope<AccountEvent>],
    ) -> Result<(), cqrs_es::persist::PersistenceError> {
        for envelope in events {
            self.apply_event(aggregate_id, &envelope.event).await?;
        }
        Ok(())
    }
}

impl AccountProjection {
    async fn apply_event(
        &self,
        aggregate_id: &str,
        event: &AccountEvent,
    ) -> Result<(), cqrs_es::persist::PersistenceError> {
        use AccountEvent::*;

        match event {
            AccountOpened { account_id, owner_name, initial_balance, opened_at } => {
                sqlx::query(
                    r#"
                    INSERT INTO account_query_model (account_id, owner_name, balance, is_active, created_at, updated_at)
                    VALUES ($1, $2, $3, true, $4, $4)
                    "#
                )
                .bind(account_id)
                .bind(owner_name)
                .bind(initial_balance)
                .bind(opened_at)
                .execute(&self.pool)
                .await?;
            }
            MoneyDeposited { amount, deposited_at } => {
                sqlx::query(
                    "UPDATE account_query_model SET balance = balance + $1, updated_at = $2 WHERE account_id = $3"
                )
                .bind(amount)
                .bind(deposited_at)
                .bind(Uuid::parse_str(aggregate_id).unwrap())
                .execute(&self.pool)
                .await?;
            }
            MoneyWithdrawn { amount, withdrawn_at } => {
                sqlx::query(
                    "UPDATE account_query_model SET balance = balance - $1, updated_at = $2 WHERE account_id = $3"
                )
                .bind(amount)
                .bind(withdrawn_at)
                .bind(Uuid::parse_str(aggregate_id).unwrap())
                .execute(&self.pool)
                .await?;
            }
            AccountClosed { closed_at } => {
                sqlx::query(
                    "UPDATE account_query_model SET is_active = false, updated_at = $1 WHERE account_id = $2"
                )
                .bind(closed_at)
                .bind(Uuid::parse_str(aggregate_id).unwrap())
                .execute(&self.pool)
                .await?;
            }
        }

        Ok(())
    }
}
```

---

## 8. Saga 模式

### 8.1 转账 Saga

```rust
use tokio::time::{sleep, Duration};

/// 转账 Saga (分布式事务)
pub struct TransferSaga {
    command_service: Arc<AccountCommandService>,
}

impl TransferSaga {
    pub fn new(command_service: Arc<AccountCommandService>) -> Self {
        Self { command_service }
    }

    /// 执行转账 (Orchestration Saga)
    pub async fn transfer(
        &self,
        from_account_id: Uuid,
        to_account_id: Uuid,
        amount: i64,
    ) -> Result<(), SagaError> {
        // Step 1: 从源账户扣款
        match self.command_service
            .execute(
                &from_account_id.to_string(),
                AccountCommand::WithdrawMoney { amount },
            )
            .await
        {
            Ok(_) => {}
            Err(e) => {
                return Err(SagaError::WithdrawFailed(e));
            }
        }

        // Step 2: 向目标账户存款
        match self.command_service
            .execute(
                &to_account_id.to_string(),
                AccountCommand::DepositMoney { amount },
            )
            .await
        {
            Ok(_) => Ok(()),
            Err(e) => {
                // 补偿操作: 退款到源账户
                tracing::warn!("Deposit failed, compensating...");
                self.command_service
                    .execute(
                        &from_account_id.to_string(),
                        AccountCommand::DepositMoney { amount },
                    )
                    .await
                    .map_err(|ce| SagaError::CompensationFailed(ce))?;

                Err(SagaError::DepositFailed(e))
            }
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum SagaError {
    #[error("Withdraw failed: {0}")]
    WithdrawFailed(AccountError),
    #[error("Deposit failed: {0}")]
    DepositFailed(AccountError),
    #[error("Compensation failed: {0}")]
    CompensationFailed(AccountError),
}
```

---

## 9. OTLP 可观测性集成

### 9.1 命令追踪

```rust
use opentelemetry::{global, trace::{SpanKind, Tracer, Status}, KeyValue};
use tracing::instrument;

#[instrument(skip(command_service), fields(
    aggregate_id = %aggregate_id,
    command = ?command
))]
pub async fn traced_execute_command(
    command_service: &AccountCommandService,
    aggregate_id: Uuid,
    command: AccountCommand,
) -> Result<(), AccountError> {
    let tracer = global::tracer("cqrs-command");
    
    let mut span = tracer
        .span_builder(format!("Command: {:?}", command))
        .with_kind(SpanKind::Internal)
        .with_attributes(vec![
            KeyValue::new("aggregate.id", aggregate_id.to_string()),
            KeyValue::new("command.type", format!("{:?}", command)),
        ])
        .start(&tracer);
    
    let start = std::time::Instant::now();
    
    let result = command_service.execute(&aggregate_id.to_string(), command).await;
    
    let duration = start.elapsed();
    
    match &result {
        Ok(_) => {
            span.set_attribute(KeyValue::new("duration_ms", duration.as_millis() as i64));
        }
        Err(e) => {
            span.set_status(Status::error(e.to_string()));
            span.set_attribute(KeyValue::new("error", true));
        }
    }
    
    span.end();
    
    result
}
```

---

## 10. 测试策略

### 10.1 聚合测试

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_open_account() {
        let mut account = Account::default();
        
        let command = AccountCommand::OpenAccount {
            account_id: Uuid::new_v4(),
            owner_name: "Alice".to_string(),
            initial_balance: 1000,
        };
        
        let events = account.handle(command, &()).unwrap();
        
        assert_eq!(events.len(), 1);
        
        for event in events {
            account.apply(event);
        }
        
        assert_eq!(account.balance, 1000);
        assert!(account.is_active);
    }

    #[test]
    fn test_insufficient_funds() {
        let mut account = Account {
            account_id: Some(Uuid::new_v4()),
            owner_name: "Bob".to_string(),
            balance: 100,
            is_active: true,
        };
        
        let command = AccountCommand::WithdrawMoney { amount: 200 };
        
        let result = account.handle(command, &());
        
        assert!(matches!(result, Err(AccountError::InsufficientFunds)));
    }
}
```

---

## 11. 生产实践

### 11.1 Docker Compose 部署

```yaml
# docker-compose.yml
version: '3.8'

services:
  postgres:
    image: postgres:16
    environment:
      POSTGRES_DB: cqrs_es
      POSTGRES_USER: user
      POSTGRES_PASSWORD: password
    ports:
      - "5432:5432"
    volumes:
      - postgres_data:/var/lib/postgresql/data

  app:
    build: .
    depends_on:
      - postgres
    environment:
      DATABASE_URL: postgres://user:password@postgres:5432/cqrs_es
      RUST_LOG: info

volumes:
  postgres_data:
```

---

## 12. 国际标准对齐

### 12.1 CQRS 模式

- ✅ **Martin Fowler CQRS Pattern**: 命令查询职责分离
- ✅ **Greg Young Event Sourcing**: 事件溯源
- ✅ **DDD (Domain-Driven Design)**: 领域驱动设计

### 12.2 OpenTelemetry 语义约定

```rust
// CQRS Semantic Conventions
span.set_attribute(KeyValue::new("cqrs.command", "OpenAccount"));
span.set_attribute(KeyValue::new("cqrs.aggregate_id", aggregate_id.to_string()));
span.set_attribute(KeyValue::new("cqrs.event_count", events.len() as i64));
```

---

## 总结

**CQRS + Event Sourcing 优势**:

1. **读写分离**: 独立优化性能
2. **完整审计**: 不可变事件日志
3. **时间旅行**: 查询任意时间点状态
4. **可扩展性**: 水平扩展读取模型

**适用场景**:

- ✅ 金融系统（审计要求）
- ✅ 高并发系统（读写分离）
- ✅ 事件驱动架构
- ✅ 微服务架构

---

**版权**: MIT License  
**作者**: OTLP Rust 项目组  
**最后更新**: 2025-10-11
