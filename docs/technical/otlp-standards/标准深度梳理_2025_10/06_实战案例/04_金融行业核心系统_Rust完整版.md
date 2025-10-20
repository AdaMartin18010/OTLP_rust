# 金融行业核心系统 - OpenTelemetry Rust 完整实战

> **版本信息**
>
> - Rust: 1.90 (2024 Edition)
> - opentelemetry: 0.31.0
> - opentelemetry_sdk: 0.31.0
> - 更新日期: 2025-10-08
> - 行业: 金融科技

## 目录

- [金融行业核心系统 - OpenTelemetry Rust 完整实战](#金融行业核心系统---opentelemetry-rust-完整实战)
  - [目录](#目录)
  - [概述](#概述)
    - [金融系统特点](#金融系统特点)
    - [可观测性需求](#可观测性需求)
  - [系统架构](#系统架构)
    - [核心服务](#核心服务)
    - [技术栈](#技术栈)
  - [核心依赖配置](#核心依赖配置)
    - [Cargo.toml](#cargotoml)
  - [1. 账户服务 (Account Service)](#1-账户服务-account-service)
    - [账户模型](#账户模型)
    - [账户操作追踪](#账户操作追踪)
    - [余额查询追踪](#余额查询追踪)
  - [2. 交易服务 (Transaction Service)](#2-交易服务-transaction-service)
    - [交易模型](#交易模型)
    - [转账操作追踪](#转账操作追踪)
    - [分布式事务追踪](#分布式事务追踪)
  - [3. 风控服务 (Risk Control Service)](#3-风控服务-risk-control-service)
    - [风控规则](#风控规则)
    - [风险评估追踪](#风险评估追踪)
    - [反欺诈检测追踪](#反欺诈检测追踪)
  - [4. 支付网关 (Payment Gateway)](#4-支付网关-payment-gateway)
    - [支付通道](#支付通道)
    - [支付请求追踪](#支付请求追踪)
    - [支付回调追踪](#支付回调追踪)
  - [5. 审计日志服务](#5-审计日志服务)
    - [审计事件模型](#审计事件模型)
    - [审计日志追踪](#审计日志追踪)
  - [6. 数据库集成](#6-数据库集成)
    - [PostgreSQL 配置](#postgresql-配置)
    - [Redis 缓存追踪](#redis-缓存追踪)
  - [7. 消息队列集成](#7-消息队列集成)
    - [Kafka 生产者追踪](#kafka-生产者追踪)
    - [Kafka 消费者追踪](#kafka-消费者追踪)
  - [8. 性能监控](#8-性能监控)
    - [关键指标](#关键指标)
    - [自定义 Metrics](#自定义-metrics)
  - [9. 安全与合规](#9-安全与合规)
    - [敏感数据脱敏](#敏感数据脱敏)
    - [审计追踪](#审计追踪)
  - [10. 告警与通知](#10-告警与通知)
    - [告警规则](#告警规则)
    - [告警实现](#告警实现)
  - [11. 完整示例](#11-完整示例)
    - [main.rs](#mainrs)
  - [12. 最佳实践](#12-最佳实践)
    - [1. 事务一致性](#1-事务一致性)
    - [2. 性能优化](#2-性能优化)
    - [3. 安全加固](#3-安全加固)
  - [总结](#总结)

---

## 概述

### 金融系统特点

- **高可用性**: 99.99% SLA 要求
- **强一致性**: 账务必须精确，不允许丢失
- **严格监管**: 符合金融行业监管要求
- **实时性**: 毫秒级响应要求
- **安全性**: 多层安全防护

### 可观测性需求

- ✅ **全链路追踪**: 跟踪每笔交易的完整路径
- ✅ **审计日志**: 记录所有关键操作
- ✅ **性能监控**: 实时监控系统性能指标
- ✅ **异常告警**: 快速发现和响应异常
- ✅ **合规报告**: 生成监管所需报告

---

## 系统架构

### 核心服务

```text
┌─────────────────────────────────────────────────┐
│                 API Gateway                      │
│            (Axum + OpenTelemetry)                │
└────────────┬────────────────────────┬────────────┘
             │                        │
    ┌────────▼────────┐      ┌───────▼────────┐
    │ Account Service │      │ Payment Gateway │
    │   (账户服务)     │      │   (支付网关)    │
    └────────┬────────┘      └───────┬────────┘
             │                        │
    ┌────────▼────────┐      ┌───────▼────────┐
    │Transaction Svc  │      │ Risk Control   │
    │   (交易服务)     │      │   (风控服务)    │
    └────────┬────────┘      └───────┬────────┘
             │                        │
    ┌────────▼────────────────────────▼────────┐
    │         Audit Log Service                 │
    │           (审计服务)                       │
    └───────────────────────────────────────────┘
             │
    ┌────────▼────────┐
    │   PostgreSQL    │
    │   Redis Cache   │
    │   Kafka MQ      │
    └─────────────────┘
```

### 技术栈

- **Web 框架**: Axum 0.7
- **数据库**: PostgreSQL (SQLx)
- **缓存**: Redis
- **消息队列**: Kafka
- **追踪**: OpenTelemetry + Jaeger
- **监控**: Prometheus + Grafana

---

## 核心依赖配置

### Cargo.toml

```toml
[package]
name = "fintech-core-system"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

[dependencies]
# Web 框架
axum = { version = "0.7.9", features = ["macros"] }
tokio = { version = "1.43.0", features = ["full"] }
tower = "0.5.2"
tower-http = { version = "0.6.2", features = ["trace", "cors"] }

# OpenTelemetry
opentelemetry = "0.31.0"
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio", "trace", "metrics", "logs"] }
opentelemetry-otlp = { version = "0.24.0", features = ["grpc-tonic", "trace", "metrics", "logs"] }
opentelemetry-jaeger = { version = "0.24.0", features = ["rt-tokio"] }
opentelemetry-semantic-conventions = "0.31.0"
tracing = "0.1.41"
tracing-subscriber = { version = "0.3.19", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.27.0"

# 数据库
sqlx = { version = "0.8.2", features = ["runtime-tokio", "postgres", "uuid", "chrono", "json"] }
redis = { version = "0.27.6", features = ["tokio-comp", "connection-manager"] }

# 消息队列
rdkafka = { version = "0.37.0", features = ["tokio"] }

# 序列化
serde = { version = "1.0.216", features = ["derive"] }
serde_json = "1.0.133"

# 时间处理
chrono = { version = "0.4.39", features = ["serde"] }
uuid = { version = "1.11.0", features = ["v4", "serde"] }

# 错误处理
thiserror = "2.0.9"
anyhow = "1.0.95"

# 加密
argon2 = "0.5.3"
sha2 = "0.10.8"
```

---

## 1. 账户服务 (Account Service)

### 账户模型

```rust
use serde::{Deserialize, Serialize};
use sqlx::FromRow;
use uuid::Uuid;
use chrono::{DateTime, Utc};
use rust_decimal::Decimal;

/// 账户类型
#[derive(Debug, Clone, Copy, Serialize, Deserialize, sqlx::Type)]
#[sqlx(type_name = "account_type", rename_all = "lowercase")]
pub enum AccountType {
    Checking,  // 支票账户
    Savings,   // 储蓄账户
    Credit,    // 信用账户
}

/// 账户状态
#[derive(Debug, Clone, Copy, Serialize, Deserialize, sqlx::Type)]
#[sqlx(type_name = "account_status", rename_all = "lowercase")]
pub enum AccountStatus {
    Active,     // 活跃
    Frozen,     // 冻结
    Closed,     // 关闭
}

/// 账户模型
#[derive(Debug, Clone, Serialize, Deserialize, FromRow)]
pub struct Account {
    pub id: Uuid,
    pub user_id: Uuid,
    pub account_number: String,
    pub account_type: AccountType,
    pub balance: Decimal,
    pub currency: String,
    pub status: AccountStatus,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

/// 账户创建请求
#[derive(Debug, Deserialize)]
pub struct CreateAccountRequest {
    pub user_id: Uuid,
    pub account_type: AccountType,
    pub currency: String,
    pub initial_deposit: Decimal,
}
```

### 账户操作追踪

```rust
use tracing::{instrument, info, warn, error};
use opentelemetry::{KeyValue, trace::SpanKind};
use axum::{extract::State, Json};

/// 账户服务
pub struct AccountService {
    db_pool: sqlx::PgPool,
    redis_client: redis::Client,
}

impl AccountService {
    /// 创建账户
    #[instrument(
        name = "account.create",
        skip(self, request),
        fields(
            user_id = %request.user_id,
            account_type = ?request.account_type,
            currency = %request.currency,
            initial_deposit = %request.initial_deposit,
        )
    )]
    pub async fn create_account(
        &self,
        request: CreateAccountRequest,
    ) -> Result<Account, AccountError> {
        let span = tracing::Span::current();
        
        // 生成账户号
        let account_number = self.generate_account_number().await?;
        span.record("account_number", &account_number.as_str());
        
        info!("Creating new account");
        
        // 开始数据库事务
        let mut tx = self.db_pool.begin().await
            .map_err(|e| {
                error!("Failed to start transaction: {}", e);
                AccountError::DatabaseError(e.to_string())
            })?;
        
        // 插入账户记录
        let account = sqlx::query_as::<_, Account>(
            r#"
            INSERT INTO accounts (
                id, user_id, account_number, account_type, 
                balance, currency, status, created_at, updated_at
            )
            VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9)
            RETURNING *
            "#
        )
        .bind(Uuid::new_v4())
        .bind(request.user_id)
        .bind(&account_number)
        .bind(request.account_type)
        .bind(request.initial_deposit)
        .bind(&request.currency)
        .bind(AccountStatus::Active)
        .bind(Utc::now())
        .bind(Utc::now())
        .fetch_one(&mut *tx)
        .await
        .map_err(|e| {
            error!("Failed to insert account: {}", e);
            AccountError::DatabaseError(e.to_string())
        })?;
        
        // 如果有初始存款，创建初始交易记录
        if request.initial_deposit > Decimal::ZERO {
            self.create_initial_deposit_transaction(&mut tx, &account).await?;
        }
        
        // 提交事务
        tx.commit().await
            .map_err(|e| {
                error!("Failed to commit transaction: {}", e);
                AccountError::DatabaseError(e.to_string())
            })?;
        
        // 缓存账户信息
        self.cache_account(&account).await?;
        
        info!(
            account_id = %account.id,
            account_number = %account.account_number,
            "Account created successfully"
        );
        
        // 添加自定义 Span 属性
        span.set_attribute(KeyValue::new("account.id", account.id.to_string()));
        span.set_attribute(KeyValue::new("account.number", account_number.clone()));
        span.set_attribute(KeyValue::new("account.created", true));
        
        Ok(account)
    }
    
    /// 生成账户号
    #[instrument(skip(self))]
    async fn generate_account_number(&self) -> Result<String, AccountError> {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        
        // 生成16位账户号：6220 + 12位随机数字
        let random_digits: String = (0..12)
            .map(|_| rng.gen_range(0..10).to_string())
            .collect();
        
        Ok(format!("6220{}", random_digits))
    }
    
    /// 创建初始存款交易
    #[instrument(skip(self, tx, account))]
    async fn create_initial_deposit_transaction(
        &self,
        tx: &mut sqlx::Transaction<'_, sqlx::Postgres>,
        account: &Account,
    ) -> Result<(), AccountError> {
        sqlx::query(
            r#"
            INSERT INTO transactions (
                id, account_id, transaction_type, amount, 
                currency, status, description, created_at
            )
            VALUES ($1, $2, $3, $4, $5, $6, $7, $8)
            "#
        )
        .bind(Uuid::new_v4())
        .bind(account.id)
        .bind("initial_deposit")
        .bind(account.balance)
        .bind(&account.currency)
        .bind("completed")
        .bind("Initial deposit")
        .bind(Utc::now())
        .execute(&mut **tx)
        .await
        .map_err(|e| AccountError::DatabaseError(e.to_string()))?;
        
        Ok(())
    }
    
    /// 缓存账户信息
    #[instrument(skip(self, account))]
    async fn cache_account(&self, account: &Account) -> Result<(), AccountError> {
        let mut conn = self.redis_client.get_connection_manager().await
            .map_err(|e| AccountError::CacheError(e.to_string()))?;
        
        let cache_key = format!("account:{}", account.id);
        let account_json = serde_json::to_string(account)
            .map_err(|e| AccountError::SerializationError(e.to_string()))?;
        
        redis::cmd("SET")
            .arg(&cache_key)
            .arg(&account_json)
            .arg("EX")
            .arg(3600) // 1小时过期
            .query_async(&mut conn)
            .await
            .map_err(|e| AccountError::CacheError(e.to_string()))?;
        
        info!("Account cached successfully");
        Ok(())
    }
}
```

### 余额查询追踪

```rust
impl AccountService {
    /// 查询账户余额
    #[instrument(
        name = "account.get_balance",
        skip(self),
        fields(account_id = %account_id)
    )]
    pub async fn get_balance(&self, account_id: Uuid) -> Result<Decimal, AccountError> {
        // 先从缓存查询
        if let Some(balance) = self.get_balance_from_cache(account_id).await? {
            info!("Balance retrieved from cache");
            return Ok(balance);
        }
        
        // 缓存未命中，从数据库查询
        let balance = sqlx::query_scalar::<_, Decimal>(
            "SELECT balance FROM accounts WHERE id = $1 AND status = $2"
        )
        .bind(account_id)
        .bind(AccountStatus::Active)
        .fetch_optional(&self.db_pool)
        .await
        .map_err(|e| {
            error!("Failed to query balance: {}", e);
            AccountError::DatabaseError(e.to_string())
        })?
        .ok_or_else(|| {
            warn!("Account not found");
            AccountError::NotFound
        })?;
        
        info!(balance = %balance, "Balance retrieved from database");
        
        // 更新缓存
        self.cache_balance(account_id, balance).await?;
        
        Ok(balance)
    }
    
    /// 从缓存获取余额
    #[instrument(skip(self))]
    async fn get_balance_from_cache(
        &self,
        account_id: Uuid,
    ) -> Result<Option<Decimal>, AccountError> {
        let mut conn = self.redis_client.get_connection_manager().await
            .map_err(|e| AccountError::CacheError(e.to_string()))?;
        
        let cache_key = format!("balance:{}", account_id);
        let balance_str: Option<String> = redis::cmd("GET")
            .arg(&cache_key)
            .query_async(&mut conn)
            .await
            .map_err(|e| AccountError::CacheError(e.to_string()))?;
        
        match balance_str {
            Some(s) => {
                let balance = s.parse::<Decimal>()
                    .map_err(|e| AccountError::ParseError(e.to_string()))?;
                Ok(Some(balance))
            }
            None => Ok(None),
        }
    }
    
    /// 缓存余额
    #[instrument(skip(self))]
    async fn cache_balance(
        &self,
        account_id: Uuid,
        balance: Decimal,
    ) -> Result<(), AccountError> {
        let mut conn = self.redis_client.get_connection_manager().await
            .map_err(|e| AccountError::CacheError(e.to_string()))?;
        
        let cache_key = format!("balance:{}", account_id);
        
        redis::cmd("SET")
            .arg(&cache_key)
            .arg(balance.to_string())
            .arg("EX")
            .arg(300) // 5分钟过期
            .query_async(&mut conn)
            .await
            .map_err(|e| AccountError::CacheError(e.to_string()))?;
        
        Ok(())
    }
}

/// 账户错误类型
#[derive(Debug, thiserror::Error)]
pub enum AccountError {
    #[error("Account not found")]
    NotFound,
    
    #[error("Insufficient balance")]
    InsufficientBalance,
    
    #[error("Account is frozen")]
    AccountFrozen,
    
    #[error("Database error: {0}")]
    DatabaseError(String),
    
    #[error("Cache error: {0}")]
    CacheError(String),
    
    #[error("Serialization error: {0}")]
    SerializationError(String),
    
    #[error("Parse error: {0}")]
    ParseError(String),
}
```

---

## 2. 交易服务 (Transaction Service)

### 交易模型

```rust
/// 交易类型
#[derive(Debug, Clone, Copy, Serialize, Deserialize, sqlx::Type)]
#[sqlx(type_name = "transaction_type", rename_all = "lowercase")]
pub enum TransactionType {
    Deposit,    // 存款
    Withdrawal, // 取款
    Transfer,   // 转账
    Payment,    // 支付
    Refund,     // 退款
}

/// 交易状态
#[derive(Debug, Clone, Copy, Serialize, Deserialize, sqlx::Type)]
#[sqlx(type_name = "transaction_status", rename_all = "lowercase")]
pub enum TransactionStatus {
    Pending,    // 待处理
    Processing, // 处理中
    Completed,  // 已完成
    Failed,     // 失败
    Cancelled,  // 已取消
}

/// 交易模型
#[derive(Debug, Clone, Serialize, Deserialize, FromRow)]
pub struct Transaction {
    pub id: Uuid,
    pub from_account_id: Option<Uuid>,
    pub to_account_id: Option<Uuid>,
    pub transaction_type: TransactionType,
    pub amount: Decimal,
    pub currency: String,
    pub status: TransactionStatus,
    pub description: Option<String>,
    pub trace_id: Option<String>,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

/// 转账请求
#[derive(Debug, Deserialize)]
pub struct TransferRequest {
    pub from_account_id: Uuid,
    pub to_account_id: Uuid,
    pub amount: Decimal,
    pub currency: String,
    pub description: Option<String>,
}
```

### 转账操作追踪

```rust
use opentelemetry::trace::{TraceContextExt, Tracer};
use opentelemetry::Context;

/// 交易服务
pub struct TransactionService {
    db_pool: sqlx::PgPool,
    account_service: Arc<AccountService>,
    risk_service: Arc<RiskControlService>,
    kafka_producer: Arc<FutureProducer>,
}

impl TransactionService {
    /// 执行转账
    #[instrument(
        name = "transaction.transfer",
        skip(self, request),
        fields(
            from_account = %request.from_account_id,
            to_account = %request.to_account_id,
            amount = %request.amount,
            currency = %request.currency,
        )
    )]
    pub async fn transfer(
        &self,
        request: TransferRequest,
    ) -> Result<Transaction, TransactionError> {
        let span = tracing::Span::current();
        let trace_id = span.context().span().span_context().trace_id().to_string();
        
        info!("Starting transfer");
        
        // 1. 风险评估
        let risk_result = self.risk_service
            .assess_transfer_risk(&request)
            .await?;
        
        if risk_result.is_high_risk {
            warn!(
                risk_score = risk_result.risk_score,
                "Transfer blocked due to high risk"
            );
            return Err(TransactionError::RiskBlocked);
        }
        
        // 2. 开始数据库事务
        let mut tx = self.db_pool.begin().await
            .map_err(|e| TransactionError::DatabaseError(e.to_string()))?;
        
        // 3. 锁定源账户（悲观锁）
        let from_account = sqlx::query_as::<_, Account>(
            "SELECT * FROM accounts WHERE id = $1 FOR UPDATE"
        )
        .bind(request.from_account_id)
        .fetch_one(&mut *tx)
        .await
        .map_err(|e| TransactionError::DatabaseError(e.to_string()))?;
        
        // 4. 检查账户状态
        if from_account.status != AccountStatus::Active {
            return Err(TransactionError::AccountFrozen);
        }
        
        // 5. 检查余额
        if from_account.balance < request.amount {
            warn!("Insufficient balance");
            return Err(TransactionError::InsufficientBalance);
        }
        
        // 6. 锁定目标账户
        let to_account = sqlx::query_as::<_, Account>(
            "SELECT * FROM accounts WHERE id = $1 FOR UPDATE"
        )
        .bind(request.to_account_id)
        .fetch_one(&mut *tx)
        .await
        .map_err(|e| TransactionError::DatabaseError(e.to_string()))?;
        
        if to_account.status != AccountStatus::Active {
            return Err(TransactionError::AccountFrozen);
        }
        
        // 7. 更新源账户余额
        sqlx::query(
            "UPDATE accounts SET balance = balance - $1, updated_at = $2 WHERE id = $3"
        )
        .bind(request.amount)
        .bind(Utc::now())
        .bind(from_account.id)
        .execute(&mut *tx)
        .await
        .map_err(|e| TransactionError::DatabaseError(e.to_string()))?;
        
        // 8. 更新目标账户余额
        sqlx::query(
            "UPDATE accounts SET balance = balance + $1, updated_at = $2 WHERE id = $3"
        )
        .bind(request.amount)
        .bind(Utc::now())
        .bind(to_account.id)
        .execute(&mut *tx)
        .await
        .map_err(|e| TransactionError::DatabaseError(e.to_string()))?;
        
        // 9. 创建交易记录
        let transaction = sqlx::query_as::<_, Transaction>(
            r#"
            INSERT INTO transactions (
                id, from_account_id, to_account_id, transaction_type,
                amount, currency, status, description, trace_id, created_at, updated_at
            )
            VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11)
            RETURNING *
            "#
        )
        .bind(Uuid::new_v4())
        .bind(from_account.id)
        .bind(to_account.id)
        .bind(TransactionType::Transfer)
        .bind(request.amount)
        .bind(&request.currency)
        .bind(TransactionStatus::Completed)
        .bind(request.description)
        .bind(&trace_id)
        .bind(Utc::now())
        .bind(Utc::now())
        .fetch_one(&mut *tx)
        .await
        .map_err(|e| TransactionError::DatabaseError(e.to_string()))?;
        
        // 10. 提交事务
        tx.commit().await
            .map_err(|e| TransactionError::DatabaseError(e.to_string()))?;
        
        info!(
            transaction_id = %transaction.id,
            "Transfer completed successfully"
        );
        
        // 11. 发送异步通知（Kafka）
        self.send_transaction_notification(&transaction).await?;
        
        // 12. 清除缓存
        self.invalidate_balance_cache(&[from_account.id, to_account.id]).await?;
        
        span.set_attribute(KeyValue::new("transaction.id", transaction.id.to_string()));
        span.set_attribute(KeyValue::new("transaction.completed", true));
        
        Ok(transaction)
    }
    
    /// 发送交易通知
    #[instrument(skip(self, transaction))]
    async fn send_transaction_notification(
        &self,
        transaction: &Transaction,
    ) -> Result<(), TransactionError> {
        let notification = serde_json::json!({
            "transaction_id": transaction.id,
            "type": "transfer_completed",
            "amount": transaction.amount,
            "currency": transaction.currency,
            "timestamp": Utc::now(),
        });
        
        let payload = serde_json::to_string(&notification)
            .map_err(|e| TransactionError::SerializationError(e.to_string()))?;
        
        let record = FutureRecord::to("transaction-events")
            .payload(&payload)
            .key(&transaction.id.to_string());
        
        self.kafka_producer
            .send(record, std::time::Duration::from_secs(5))
            .await
            .map_err(|(e, _)| TransactionError::KafkaError(e.to_string()))?;
        
        info!("Transaction notification sent");
        Ok(())
    }
    
    /// 清除余额缓存
    #[instrument(skip(self, account_ids))]
    async fn invalidate_balance_cache(
        &self,
        account_ids: &[Uuid],
    ) -> Result<(), TransactionError> {
        for account_id in account_ids {
            let cache_key = format!("balance:{}", account_id);
            // 删除缓存逻辑
            info!(account_id = %account_id, "Balance cache invalidated");
        }
        Ok(())
    }
}

/// 交易错误类型
#[derive(Debug, thiserror::Error)]
pub enum TransactionError {
    #[error("Insufficient balance")]
    InsufficientBalance,
    
    #[error("Account frozen")]
    AccountFrozen,
    
    #[error("Risk blocked")]
    RiskBlocked,
    
    #[error("Database error: {0}")]
    DatabaseError(String),
    
    #[error("Kafka error: {0}")]
    KafkaError(String),
    
    #[error("Serialization error: {0}")]
    SerializationError(String),
}
```

### 分布式事务追踪

```rust
use opentelemetry::global;

/// 分布式转账（跨服务）
impl TransactionService {
    #[instrument(
        name = "transaction.distributed_transfer",
        skip(self, request)
    )]
    pub async fn distributed_transfer(
        &self,
        request: TransferRequest,
    ) -> Result<Transaction, TransactionError> {
        let tracer = global::tracer("transaction-service");
        
        // 创建父 Span
        let mut span = tracer
            .span_builder("distributed_transfer")
            .with_kind(SpanKind::Internal)
            .start(&tracer);
        
        span.set_attribute(KeyValue::new("from_account", request.from_account_id.to_string()));
        span.set_attribute(KeyValue::new("to_account", request.to_account_id.to_string()));
        span.set_attribute(KeyValue::new("amount", request.amount.to_string()));
        
        let cx = Context::current_with_span(span);
        
        // 步骤 1: 调用账户服务扣款
        let debit_result = self.account_service
            .debit_account(request.from_account_id, request.amount)
            .await?;
        
        // 步骤 2: 调用支付网关
        let payment_result = self.payment_gateway
            .process_payment(&request)
            .await?;
        
        // 步骤 3: 调用账户服务入账
        let credit_result = self.account_service
            .credit_account(request.to_account_id, request.amount)
            .await?;
        
        // 步骤 4: 创建交易记录
        let transaction = self.create_transaction_record(&request).await?;
        
        info!("Distributed transfer completed");
        
        Ok(transaction)
    }
}
```

---

## 3. 风控服务 (Risk Control Service)

### 风控规则

```rust
/// 风险等级
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum RiskLevel {
    Low,
    Medium,
    High,
}

/// 风险评估结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RiskAssessmentResult {
    pub risk_score: f64,
    pub risk_level: RiskLevel,
    pub is_high_risk: bool,
    pub reasons: Vec<String>,
}

/// 风控规则
pub struct RiskRule {
    pub name: String,
    pub weight: f64,
    pub threshold: f64,
}

impl RiskRule {
    /// 单笔限额规则
    pub fn single_transaction_limit() -> Self {
        Self {
            name: "single_transaction_limit".to_string(),
            weight: 0.3,
            threshold: 50000.0, // 5万元
        }
    }
    
    /// 日累计限额规则
    pub fn daily_limit() -> Self {
        Self {
            name: "daily_limit".to_string(),
            weight: 0.2,
            threshold: 200000.0, // 20万元
        }
    }
    
    /// 频率限制规则
    pub fn frequency_limit() -> Self {
        Self {
            name: "frequency_limit".to_string(),
            weight: 0.3,
            threshold: 10.0, // 每小时10笔
        }
    }
    
    /// 异地交易规则
    pub fn location_anomaly() -> Self {
        Self {
            name: "location_anomaly".to_string(),
            weight: 0.2,
            threshold: 0.8, // 异地概率阈值
        }
    }
}
```

### 风险评估追踪

```rust
/// 风控服务
pub struct RiskControlService {
    db_pool: sqlx::PgPool,
    redis_client: redis::Client,
}

impl RiskControlService {
    /// 评估转账风险
    #[instrument(
        name = "risk.assess_transfer",
        skip(self, request),
        fields(
            from_account = %request.from_account_id,
            amount = %request.amount,
        )
    )]
    pub async fn assess_transfer_risk(
        &self,
        request: &TransferRequest,
    ) -> Result<RiskAssessmentResult, RiskError> {
        info!("Starting risk assessment");
        
        let mut risk_score = 0.0;
        let mut reasons = Vec::new();
        
        // 规则 1: 检查单笔限额
        let single_limit_rule = RiskRule::single_transaction_limit();
        if request.amount.to_f64().unwrap_or(0.0) > single_limit_rule.threshold {
            risk_score += single_limit_rule.weight;
            reasons.push(format!(
                "Single transaction exceeds limit: {} > {}",
                request.amount, single_limit_rule.threshold
            ));
        }
        
        // 规则 2: 检查日累计金额
        let daily_total = self.get_daily_transaction_total(request.from_account_id).await?;
        let daily_limit_rule = RiskRule::daily_limit();
        if daily_total + request.amount.to_f64().unwrap_or(0.0) > daily_limit_rule.threshold {
            risk_score += daily_limit_rule.weight;
            reasons.push(format!(
                "Daily total exceeds limit: {} > {}",
                daily_total, daily_limit_rule.threshold
            ));
        }
        
        // 规则 3: 检查交易频率
        let hourly_count = self.get_hourly_transaction_count(request.from_account_id).await?;
        let frequency_rule = RiskRule::frequency_limit();
        if hourly_count as f64 > frequency_rule.threshold {
            risk_score += frequency_rule.weight;
            reasons.push(format!(
                "Transaction frequency too high: {} > {}",
                hourly_count, frequency_rule.threshold
            ));
        }
        
        // 规则 4: 异地交易检测
        if self.is_location_anomaly(request.from_account_id).await? {
            let location_rule = RiskRule::location_anomaly();
            risk_score += location_rule.weight;
            reasons.push("Location anomaly detected".to_string());
        }
        
        // 计算风险等级
        let risk_level = if risk_score >= 0.7 {
            RiskLevel::High
        } else if risk_score >= 0.4 {
            RiskLevel::Medium
        } else {
            RiskLevel::Low
        };
        
        let is_high_risk = matches!(risk_level, RiskLevel::High);
        
        info!(
            risk_score = risk_score,
            risk_level = ?risk_level,
            is_high_risk = is_high_risk,
            "Risk assessment completed"
        );
        
        let result = RiskAssessmentResult {
            risk_score,
            risk_level,
            is_high_risk,
            reasons,
        };
        
        // 记录风险评估结果
        self.log_risk_assessment(&result, request).await?;
        
        Ok(result)
    }
    
    /// 获取日累计交易金额
    #[instrument(skip(self))]
    async fn get_daily_transaction_total(&self, account_id: Uuid) -> Result<f64, RiskError> {
        let today_start = Utc::now().date_naive().and_hms_opt(0, 0, 0).unwrap();
        
        let total: Option<Decimal> = sqlx::query_scalar(
            r#"
            SELECT COALESCE(SUM(amount), 0)
            FROM transactions
            WHERE from_account_id = $1
              AND created_at >= $2
              AND status = 'completed'
            "#
        )
        .bind(account_id)
        .bind(today_start)
        .fetch_one(&self.db_pool)
        .await
        .map_err(|e| RiskError::DatabaseError(e.to_string()))?;
        
        Ok(total.unwrap_or(Decimal::ZERO).to_f64().unwrap_or(0.0))
    }
    
    /// 获取小时交易次数
    #[instrument(skip(self))]
    async fn get_hourly_transaction_count(&self, account_id: Uuid) -> Result<i64, RiskError> {
        let hour_ago = Utc::now() - chrono::Duration::hours(1);
        
        let count: i64 = sqlx::query_scalar(
            r#"
            SELECT COUNT(*)
            FROM transactions
            WHERE from_account_id = $1
              AND created_at >= $2
            "#
        )
        .bind(account_id)
        .bind(hour_ago)
        .fetch_one(&self.db_pool)
        .await
        .map_err(|e| RiskError::DatabaseError(e.to_string()))?;
        
        Ok(count)
    }
    
    /// 检测异地交易
    #[instrument(skip(self))]
    async fn is_location_anomaly(&self, account_id: Uuid) -> Result<bool, RiskError> {
        // 简化实现：检查最近的IP地址变化
        // 实际应使用地理位置数据库和机器学习模型
        
        let last_ips: Vec<String> = sqlx::query_scalar(
            r#"
            SELECT ip_address
            FROM transaction_logs
            WHERE account_id = $1
            ORDER BY created_at DESC
            LIMIT 5
            "#
        )
        .bind(account_id)
        .fetch_all(&self.db_pool)
        .await
        .map_err(|e| RiskError::DatabaseError(e.to_string()))?;
        
        // 如果IP地址变化频繁，视为异常
        let unique_ips: std::collections::HashSet<_> = last_ips.iter().collect();
        Ok(unique_ips.len() >= 3)
    }
    
    /// 记录风险评估结果
    #[instrument(skip(self, result, request))]
    async fn log_risk_assessment(
        &self,
        result: &RiskAssessmentResult,
        request: &TransferRequest,
    ) -> Result<(), RiskError> {
        sqlx::query(
            r#"
            INSERT INTO risk_assessments (
                id, account_id, transaction_amount, risk_score, 
                risk_level, is_blocked, reasons, created_at
            )
            VALUES ($1, $2, $3, $4, $5, $6, $7, $8)
            "#
        )
        .bind(Uuid::new_v4())
        .bind(request.from_account_id)
        .bind(request.amount)
        .bind(result.risk_score)
        .bind(format!("{:?}", result.risk_level))
        .bind(result.is_high_risk)
        .bind(serde_json::to_value(&result.reasons).unwrap())
        .bind(Utc::now())
        .execute(&self.db_pool)
        .await
        .map_err(|e| RiskError::DatabaseError(e.to_string()))?;
        
        Ok(())
    }
}

#[derive(Debug, thiserror::Error)]
pub enum RiskError {
    #[error("Database error: {0}")]
    DatabaseError(String),
}
```

### 反欺诈检测追踪

```rust
impl RiskControlService {
    /// 反欺诈检测
    #[instrument(
        name = "risk.fraud_detection",
        skip(self, request)
    )]
    pub async fn detect_fraud(
        &self,
        request: &TransferRequest,
    ) -> Result<bool, RiskError> {
        info!("Starting fraud detection");
        
        let mut fraud_indicators = Vec::new();
        
        // 检测 1: 短时间内多次失败尝试
        let recent_failures = self.get_recent_failed_attempts(request.from_account_id).await?;
        if recent_failures > 3 {
            fraud_indicators.push("Multiple failed attempts");
        }
        
        // 检测 2: 账户异常活跃
        let activity_score = self.calculate_activity_score(request.from_account_id).await?;
        if activity_score > 0.9 {
            fraud_indicators.push("Abnormal account activity");
        }
        
        // 检测 3: 收款方黑名单检查
        if self.is_account_blacklisted(request.to_account_id).await? {
            fraud_indicators.push("Recipient in blacklist");
        }
        
        let is_fraud = !fraud_indicators.is_empty();
        
        if is_fraud {
            warn!(
                indicators = ?fraud_indicators,
                "Fraud detected"
            );
        }
        
        Ok(is_fraud)
    }
    
    #[instrument(skip(self))]
    async fn get_recent_failed_attempts(&self, account_id: Uuid) -> Result<i64, RiskError> {
        let five_minutes_ago = Utc::now() - chrono::Duration::minutes(5);
        
        sqlx::query_scalar(
            r#"
            SELECT COUNT(*)
            FROM transactions
            WHERE from_account_id = $1
              AND status = 'failed'
              AND created_at >= $2
            "#
        )
        .bind(account_id)
        .bind(five_minutes_ago)
        .fetch_one(&self.db_pool)
        .await
        .map_err(|e| RiskError::DatabaseError(e.to_string()))
    }
    
    #[instrument(skip(self))]
    async fn calculate_activity_score(&self, account_id: Uuid) -> Result<f64, RiskError> {
        // 简化实现：基于交易频率计算活跃度分数
        let count = self.get_hourly_transaction_count(account_id).await?;
        Ok((count as f64 / 50.0).min(1.0))
    }
    
    #[instrument(skip(self))]
    async fn is_account_blacklisted(&self, account_id: Uuid) -> Result<bool, RiskError> {
        let exists: bool = sqlx::query_scalar(
            "SELECT EXISTS(SELECT 1 FROM account_blacklist WHERE account_id = $1)"
        )
        .bind(account_id)
        .fetch_one(&self.db_pool)
        .await
        .map_err(|e| RiskError::DatabaseError(e.to_string()))?;
        
        Ok(exists)
    }
}
```

---

## 4. 支付网关 (Payment Gateway)

### 支付通道

```rust
/// 支付通道类型
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum PaymentChannel {
    Alipay,     // 支付宝
    WeChatPay,  // 微信支付
    UnionPay,   // 银联
    BankCard,   // 银行卡
}

/// 支付请求
#[derive(Debug, Serialize, Deserialize)]
pub struct PaymentRequest {
    pub order_id: String,
    pub amount: Decimal,
    pub currency: String,
    pub channel: PaymentChannel,
    pub return_url: Option<String>,
    pub notify_url: String,
}

/// 支付响应
#[derive(Debug, Serialize, Deserialize)]
pub struct PaymentResponse {
    pub payment_id: String,
    pub order_id: String,
    pub status: String,
    pub redirect_url: Option<String>,
}
```

### 支付请求追踪

```rust
/// 支付网关服务
pub struct PaymentGatewayService {
    http_client: reqwest::Client,
    db_pool: sqlx::PgPool,
}

impl PaymentGatewayService {
    /// 创建支付订单
    #[instrument(
        name = "payment.create_order",
        skip(self, request),
        fields(
            order_id = %request.order_id,
            amount = %request.amount,
            channel = ?request.channel,
        )
    )]
    pub async fn create_payment_order(
        &self,
        request: PaymentRequest,
    ) -> Result<PaymentResponse, PaymentError> {
        info!("Creating payment order");
        
        // 生成支付ID
        let payment_id = Uuid::new_v4().to_string();
        
        // 根据支付通道路由
        let response = match request.channel {
            PaymentChannel::Alipay => self.process_alipay(&request, &payment_id).await?,
            PaymentChannel::WeChatPay => self.process_wechat_pay(&request, &payment_id).await?,
            PaymentChannel::UnionPay => self.process_union_pay(&request, &payment_id).await?,
            PaymentChannel::BankCard => self.process_bank_card(&request, &payment_id).await?,
        };
        
        // 保存支付记录
        self.save_payment_record(&request, &payment_id).await?;
        
        info!(payment_id = %payment_id, "Payment order created");
        
        Ok(response)
    }
    
    /// 处理支付宝支付
    #[instrument(skip(self, request))]
    async fn process_alipay(
        &self,
        request: &PaymentRequest,
        payment_id: &str,
    ) -> Result<PaymentResponse, PaymentError> {
        info!("Processing Alipay payment");
        
        // 构建支付宝请求参数
        let alipay_request = serde_json::json!({
            "app_id": "your_app_id",
            "method": "alipay.trade.page.pay",
            "charset": "UTF-8",
            "sign_type": "RSA2",
            "timestamp": Utc::now().format("%Y-%m-%d %H:%M:%S").to_string(),
            "version": "1.0",
            "notify_url": &request.notify_url,
            "biz_content": {
                "out_trade_no": payment_id,
                "product_code": "FAST_INSTANT_TRADE_PAY",
                "total_amount": request.amount.to_string(),
                "subject": format!("Order {}", request.order_id),
            }
        });
        
        // 发送HTTP请求到支付宝
        let response = self.http_client
            .post("https://openapi.alipay.com/gateway.do")
            .json(&alipay_request)
            .send()
            .await
            .map_err(|e| PaymentError::HttpError(e.to_string()))?;
        
        let redirect_url = response.text().await
            .map_err(|e| PaymentError::HttpError(e.to_string()))?;
        
        Ok(PaymentResponse {
            payment_id: payment_id.to_string(),
            order_id: request.order_id.clone(),
            status: "pending".to_string(),
            redirect_url: Some(redirect_url),
        })
    }
    
    /// 处理微信支付
    #[instrument(skip(self, request))]
    async fn process_wechat_pay(
        &self,
        request: &PaymentRequest,
        payment_id: &str,
    ) -> Result<PaymentResponse, PaymentError> {
        info!("Processing WeChat Pay");
        // 微信支付实现（类似支付宝）
        todo!("Implement WeChat Pay")
    }
    
    /// 处理银联支付
    #[instrument(skip(self, request))]
    async fn process_union_pay(
        &self,
        request: &PaymentRequest,
        payment_id: &str,
    ) -> Result<PaymentResponse, PaymentError> {
        info!("Processing UnionPay");
        // 银联支付实现
        todo!("Implement UnionPay")
    }
    
    /// 处理银行卡支付
    #[instrument(skip(self, request))]
    async fn process_bank_card(
        &self,
        request: &PaymentRequest,
        payment_id: &str,
    ) -> Result<PaymentResponse, PaymentError> {
        info!("Processing Bank Card payment");
        // 银行卡支付实现
        todo!("Implement Bank Card payment")
    }
    
    /// 保存支付记录
    #[instrument(skip(self, request))]
    async fn save_payment_record(
        &self,
        request: &PaymentRequest,
        payment_id: &str,
    ) -> Result<(), PaymentError> {
        sqlx::query(
            r#"
            INSERT INTO payment_orders (
                id, order_id, amount, currency, channel, 
                status, created_at, updated_at
            )
            VALUES ($1, $2, $3, $4, $5, $6, $7, $8)
            "#
        )
        .bind(payment_id)
        .bind(&request.order_id)
        .bind(request.amount)
        .bind(&request.currency)
        .bind(format!("{:?}", request.channel))
        .bind("pending")
        .bind(Utc::now())
        .bind(Utc::now())
        .execute(&self.db_pool)
        .await
        .map_err(|e| PaymentError::DatabaseError(e.to_string()))?;
        
        Ok(())
    }
}

#[derive(Debug, thiserror::Error)]
pub enum PaymentError {
    #[error("HTTP error: {0}")]
    HttpError(String),
    
    #[error("Database error: {0}")]
    DatabaseError(String),
}
```

### 支付回调追踪

```rust
use axum::{extract::Json, http::StatusCode};

/// 支付回调
#[instrument(
    name = "payment.callback",
    skip(gateway_service, payload)
)]
pub async fn payment_callback(
    State(gateway_service): State<Arc<PaymentGatewayService>>,
    Json(payload): Json<serde_json::Value>,
) -> Result<StatusCode, PaymentError> {
    info!("Received payment callback");
    
    // 验证签名
    gateway_service.verify_callback_signature(&payload).await?;
    
    // 解析回调数据
    let payment_id = payload["out_trade_no"]
        .as_str()
        .ok_or(PaymentError::InvalidCallback)?;
    
    let trade_status = payload["trade_status"]
        .as_str()
        .ok_or(PaymentError::InvalidCallback)?;
    
    info!(
        payment_id = payment_id,
        trade_status = trade_status,
        "Payment callback parsed"
    );
    
    // 更新支付状态
    gateway_service.update_payment_status(payment_id, trade_status).await?;
    
    // 触发后续业务逻辑
    if trade_status == "TRADE_SUCCESS" {
        gateway_service.on_payment_success(payment_id).await?;
    }
    
    Ok(StatusCode::OK)
}

impl PaymentGatewayService {
    #[instrument(skip(self, payload))]
    async fn verify_callback_signature(
        &self,
        payload: &serde_json::Value,
    ) -> Result<(), PaymentError> {
        // 验证支付回调签名
        info!("Verifying callback signature");
        Ok(())
    }
    
    #[instrument(skip(self))]
    async fn update_payment_status(
        &self,
        payment_id: &str,
        status: &str,
    ) -> Result<(), PaymentError> {
        sqlx::query(
            "UPDATE payment_orders SET status = $1, updated_at = $2 WHERE id = $3"
        )
        .bind(status)
        .bind(Utc::now())
        .bind(payment_id)
        .execute(&self.db_pool)
        .await
        .map_err(|e| PaymentError::DatabaseError(e.to_string()))?;
        
        info!("Payment status updated");
        Ok(())
    }
    
    #[instrument(skip(self))]
    async fn on_payment_success(&self, payment_id: &str) -> Result<(), PaymentError> {
        info!("Processing successful payment");
        // 触发后续业务逻辑：发货、通知等
        Ok(())
    }
}

#[derive(Debug, thiserror::Error)]
pub enum PaymentError {
    #[error("Invalid callback")]
    InvalidCallback,
    
    #[error("Database error: {0}")]
    DatabaseError(String),
    
    #[error("HTTP error: {0}")]
    HttpError(String),
}
```

---

## 5. 审计日志服务

### 审计事件模型

```rust
/// 审计事件类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AuditEventType {
    AccountCreated,
    AccountUpdated,
    TransactionCreated,
    PaymentProcessed,
    RiskAssessed,
    LoginAttempt,
    PasswordChanged,
}

/// 审计日志
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuditLog {
    pub id: Uuid,
    pub event_type: AuditEventType,
    pub user_id: Option<Uuid>,
    pub account_id: Option<Uuid>,
    pub resource_id: Option<String>,
    pub action: String,
    pub details: serde_json::Value,
    pub ip_address: Option<String>,
    pub user_agent: Option<String>,
    pub trace_id: Option<String>,
    pub timestamp: DateTime<Utc>,
}
```

### 审计日志追踪

```rust
/// 审计服务
pub struct AuditService {
    db_pool: sqlx::PgPool,
    kafka_producer: Arc<FutureProducer>,
}

impl AuditService {
    /// 记录审计日志
    #[instrument(
        name = "audit.log",
        skip(self, log),
        fields(
            event_type = ?log.event_type,
            user_id = ?log.user_id,
            action = %log.action,
        )
    )]
    pub async fn log_audit_event(&self, mut log: AuditLog) -> Result<(), AuditError> {
        // 添加 trace_id
        let span = tracing::Span::current();
        log.trace_id = Some(
            span.context()
                .span()
                .span_context()
                .trace_id()
                .to_string()
        );
        
        log.timestamp = Utc::now();
        
        info!("Logging audit event");
        
        // 异步写入数据库
        let db_log = log.clone();
        let db_pool = self.db_pool.clone();
        tokio::spawn(async move {
            let _ = sqlx::query(
                r#"
                INSERT INTO audit_logs (
                    id, event_type, user_id, account_id, resource_id,
                    action, details, ip_address, user_agent, trace_id, timestamp
                )
                VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11)
                "#
            )
            .bind(db_log.id)
            .bind(format!("{:?}", db_log.event_type))
            .bind(db_log.user_id)
            .bind(db_log.account_id)
            .bind(db_log.resource_id)
            .bind(&db_log.action)
            .bind(&db_log.details)
            .bind(db_log.ip_address)
            .bind(db_log.user_agent)
            .bind(db_log.trace_id)
            .bind(db_log.timestamp)
            .execute(&db_pool)
            .await;
        });
        
        // 发送到 Kafka
        self.send_audit_event_to_kafka(&log).await?;
        
        Ok(())
    }
    
    #[instrument(skip(self, log))]
    async fn send_audit_event_to_kafka(&self, log: &AuditLog) -> Result<(), AuditError> {
        let payload = serde_json::to_string(log)
            .map_err(|e| AuditError::SerializationError(e.to_string()))?;
        
        let record = FutureRecord::to("audit-events")
            .payload(&payload)
            .key(&log.id.to_string());
        
        self.kafka_producer
            .send(record, std::time::Duration::from_secs(5))
            .await
            .map_err(|(e, _)| AuditError::KafkaError(e.to_string()))?;
        
        Ok(())
    }
}

#[derive(Debug, thiserror::Error)]
pub enum AuditError {
    #[error("Serialization error: {0}")]
    SerializationError(String),
    
    #[error("Kafka error: {0}")]
    KafkaError(String),
}
```

---

## 6. 数据库集成

### PostgreSQL 配置

```rust
use sqlx::postgres::PgPoolOptions;

/// 初始化数据库连接池
pub async fn init_db_pool() -> Result<sqlx::PgPool, sqlx::Error> {
    let database_url = std::env::var("DATABASE_URL")
        .unwrap_or_else(|_| "postgres://user:pass@localhost/fintech".to_string());
    
    PgPoolOptions::new()
        .max_connections(50)
        .min_connections(5)
        .acquire_timeout(std::time::Duration::from_secs(5))
        .connect(&database_url)
        .await
}
```

### Redis 缓存追踪

```rust
/// Redis 缓存管理器
pub struct RedisCacheManager {
    client: redis::Client,
}

impl RedisCacheManager {
    #[instrument(skip(self, key, value))]
    pub async fn set_with_expiry(
        &self,
        key: &str,
        value: &str,
        expiry_secs: usize,
    ) -> Result<(), redis::RedisError> {
        let mut conn = self.client.get_connection_manager().await?;
        
        redis::cmd("SET")
            .arg(key)
            .arg(value)
            .arg("EX")
            .arg(expiry_secs)
            .query_async(&mut conn)
            .await?;
        
        info!(key = key, "Cache set successfully");
        Ok(())
    }
    
    #[instrument(skip(self))]
    pub async fn get(&self, key: &str) -> Result<Option<String>, redis::RedisError> {
        let mut conn = self.client.get_connection_manager().await?;
        
        let value: Option<String> = redis::cmd("GET")
            .arg(key)
            .query_async(&mut conn)
            .await?;
        
        if value.is_some() {
            info!(key = key, "Cache hit");
        } else {
            info!(key = key, "Cache miss");
        }
        
        Ok(value)
    }
}
```

---

## 7. 消息队列集成

### Kafka 生产者追踪

```rust
use rdkafka::config::ClientConfig;
use rdkafka::producer::{FutureProducer, FutureRecord};

/// 初始化 Kafka 生产者
pub fn init_kafka_producer() -> Result<FutureProducer, rdkafka::error::KafkaError> {
    ClientConfig::new()
        .set("bootstrap.servers", "localhost:9092")
        .set("message.timeout.ms", "5000")
        .set("compression.type", "lz4")
        .create()
}

/// 发送Kafka消息（带追踪）
#[instrument(skip(producer, payload))]
pub async fn send_kafka_message(
    producer: &FutureProducer,
    topic: &str,
    key: &str,
    payload: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let record = FutureRecord::to(topic)
        .payload(payload)
        .key(key);
    
    producer
        .send(record, std::time::Duration::from_secs(5))
        .await
        .map_err(|(e, _)| Box::new(e) as Box<dyn std::error::Error>)?;
    
    info!(topic = topic, "Message sent to Kafka");
    Ok(())
}
```

### Kafka 消费者追踪

```rust
use rdkafka::consumer::{Consumer, StreamConsumer};
use rdkafka::Message;
use futures::StreamExt;

/// Kafka 消费者
pub struct KafkaConsumerService {
    consumer: StreamConsumer,
}

impl KafkaConsumerService {
    /// 启动消费
    #[instrument(skip(self))]
    pub async fn start_consuming(&self) -> Result<(), Box<dyn std::error::Error>> {
        info!("Starting Kafka consumer");
        
        let mut message_stream = self.consumer.stream();
        
        while let Some(message) = message_stream.next().await {
            match message {
                Ok(m) => {
                    self.process_message(&m).await?;
                }
                Err(e) => {
                    error!("Kafka error: {}", e);
                }
            }
        }
        
        Ok(())
    }
    
    /// 处理消息
    #[instrument(skip(self, message))]
    async fn process_message(&self, message: &rdkafka::message::BorrowedMessage<'_>) -> Result<(), Box<dyn std::error::Error>> {
        let payload = message.payload_view::<str>()
            .ok_or("Empty payload")??;
        
        let key = message.key_view::<str>()
            .unwrap_or(Ok(""))
            .unwrap_or("");
        
        info!(
            topic = message.topic(),
            partition = message.partition(),
            offset = message.offset(),
            key = key,
            "Processing Kafka message"
        );
        
        // 业务逻辑处理
        // ...
        
        Ok(())
    }
}
```

---

## 8. 性能监控

### 关键指标

```rust
use opentelemetry::metrics::{Counter, Histogram, Meter};
use opentelemetry::KeyValue;

/// 业务指标
pub struct BusinessMetrics {
    // 计数器
    pub transaction_total: Counter<u64>,
    pub payment_total: Counter<u64>,
    pub risk_blocked_total: Counter<u64>,
    
    // 直方图
    pub transaction_amount: Histogram<f64>,
    pub transaction_duration: Histogram<f64>,
    pub payment_duration: Histogram<f64>,
}

impl BusinessMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            transaction_total: meter
                .u64_counter("transaction.total")
                .with_description("Total number of transactions")
                .init(),
            
            payment_total: meter
                .u64_counter("payment.total")
                .with_description("Total number of payments")
                .init(),
            
            risk_blocked_total: meter
                .u64_counter("risk.blocked.total")
                .with_description("Total number of risk-blocked transactions")
                .init(),
            
            transaction_amount: meter
                .f64_histogram("transaction.amount")
                .with_description("Transaction amount distribution")
                .init(),
            
            transaction_duration: meter
                .f64_histogram("transaction.duration")
                .with_description("Transaction processing duration")
                .with_unit("ms")
                .init(),
            
            payment_duration: meter
                .f64_histogram("payment.duration")
                .with_description("Payment processing duration")
                .with_unit("ms")
                .init(),
        }
    }
}
```

### 自定义 Metrics

```rust
use std::time::Instant;

impl TransactionService {
    /// 记录交易指标
    pub async fn transfer_with_metrics(
        &self,
        request: TransferRequest,
        metrics: &BusinessMetrics,
    ) -> Result<Transaction, TransactionError> {
        let start = Instant::now();
        
        // 执行转账
        let result = self.transfer(request.clone()).await;
        
        // 记录指标
        let duration = start.elapsed().as_millis() as f64;
        metrics.transaction_duration.record(duration, &[]);
        
        match &result {
            Ok(transaction) => {
                // 记录成功交易
                metrics.transaction_total.add(1, &[
                    KeyValue::new("status", "success"),
                    KeyValue::new("type", "transfer"),
                ]);
                
                metrics.transaction_amount.record(
                    request.amount.to_f64().unwrap_or(0.0),
                    &[KeyValue::new("currency", request.currency.clone())]
                );
            }
            Err(e) => {
                // 记录失败交易
                metrics.transaction_total.add(1, &[
                    KeyValue::new("status", "failure"),
                    KeyValue::new("error_type", e.to_string()),
                ]);
                
                if matches!(e, TransactionError::RiskBlocked) {
                    metrics.risk_blocked_total.add(1, &[]);
                }
            }
        }
        
        result
    }
}
```

---

## 9. 安全与合规

### 敏感数据脱敏

```rust
use tracing::field::Visit;

/// 敏感数据脱敏
pub fn mask_sensitive_data(data: &str, mask_type: MaskType) -> String {
    match mask_type {
        MaskType::AccountNumber => {
            // 账户号脱敏：保留前4位和后4位
            if data.len() > 8 {
                format!("{}****{}", &data[..4], &data[data.len()-4..])
            } else {
                "****".to_string()
            }
        }
        MaskType::PhoneNumber => {
            // 手机号脱敏：保留前3位和后4位
            if data.len() == 11 {
                format!("{}****{}", &data[..3], &data[7..])
            } else {
                "****".to_string()
            }
        }
        MaskType::IdCard => {
            // 身份证脱敏：保留前6位和后4位
            if data.len() == 18 {
                format!("{}********{}", &data[..6], &data[14..])
            } else {
                "****".to_string()
            }
        }
    }
}

pub enum MaskType {
    AccountNumber,
    PhoneNumber,
    IdCard,
}

/// 自定义 Span 访问器（脱敏）
struct MaskingVisitor;

impl Visit for MaskingVisitor {
    fn record_str(&mut self, field: &tracing::field::Field, value: &str) {
        if field.name() == "account_number" {
            println!("{} = {}", field.name(), mask_sensitive_data(value, MaskType::AccountNumber));
        } else {
            println!("{} = {}", field.name(), value);
        }
    }
    
    fn record_debug(&mut self, field: &tracing::field::Field, value: &dyn std::fmt::Debug) {
        println!("{} = {:?}", field.name(), value);
    }
}
```

### 审计追踪

```rust
/// 审计中间件
pub async fn audit_middleware(
    request: axum::http::Request<axum::body::Body>,
    next: axum::middleware::Next,
) -> Result<axum::response::Response, StatusCode> {
    let method = request.method().clone();
    let uri = request.uri().clone();
    let headers = request.headers().clone();
    
    // 提取用户信息
    let user_id = headers
        .get("X-User-ID")
        .and_then(|v| v.to_str().ok())
        .and_then(|s| Uuid::parse_str(s).ok());
    
    let ip_address = headers
        .get("X-Real-IP")
        .and_then(|v| v.to_str().ok())
        .map(|s| s.to_string());
    
    // 记录审计日志
    info!(
        method = %method,
        uri = %uri,
        user_id = ?user_id,
        ip_address = ?ip_address,
        "Incoming request"
    );
    
    // 执行请求
    let response = next.run(request).await;
    
    // 记录响应
    info!(
        status = response.status().as_u16(),
        "Request completed"
    );
    
    Ok(response)
}
```

---

## 10. 告警与通知

### 告警规则

```rust
/// 告警类型
#[derive(Debug, Clone)]
pub enum AlertType {
    TransactionFailureRate,
    PaymentTimeout,
    RiskBlockageSpike,
    SystemOverload,
}

/// 告警规则
pub struct AlertRule {
    pub alert_type: AlertType,
    pub threshold: f64,
    pub window_seconds: u64,
}

impl AlertRule {
    pub fn transaction_failure_rate() -> Self {
        Self {
            alert_type: AlertType::TransactionFailureRate,
            threshold: 0.1, // 10%
            window_seconds: 300, // 5分钟
        }
    }
    
    pub fn payment_timeout() -> Self {
        Self {
            alert_type: AlertType::PaymentTimeout,
            threshold: 30.0, // 30秒
            window_seconds: 60,
        }
    }
}
```

### 告警实现

```rust
/// 告警服务
pub struct AlertService {
    db_pool: sqlx::PgPool,
    notification_client: Arc<NotificationClient>,
}

impl AlertService {
    /// 检查告警条件
    #[instrument(skip(self))]
    pub async fn check_alerts(&self) -> Result<(), AlertError> {
        // 检查交易失败率
        self.check_transaction_failure_rate().await?;
        
        // 检查支付超时
        self.check_payment_timeout().await?;
        
        // 检查风控拦截激增
        self.check_risk_blockage_spike().await?;
        
        Ok(())
    }
    
    #[instrument(skip(self))]
    async fn check_transaction_failure_rate(&self) -> Result<(), AlertError> {
        let rule = AlertRule::transaction_failure_rate();
        let five_minutes_ago = Utc::now() - chrono::Duration::seconds(rule.window_seconds as i64);
        
        let (total, failed): (i64, i64) = sqlx::query_as(
            r#"
            SELECT 
                COUNT(*) as total,
                SUM(CASE WHEN status = 'failed' THEN 1 ELSE 0 END) as failed
            FROM transactions
            WHERE created_at >= $1
            "#
        )
        .bind(five_minutes_ago)
        .fetch_one(&self.db_pool)
        .await
        .map_err(|e| AlertError::DatabaseError(e.to_string()))?;
        
        if total > 0 {
            let failure_rate = failed as f64 / total as f64;
            
            if failure_rate > rule.threshold {
                warn!(
                    failure_rate = failure_rate,
                    threshold = rule.threshold,
                    "Transaction failure rate exceeds threshold"
                );
                
                self.send_alert(
                    &rule.alert_type,
                    &format!("Transaction failure rate: {:.2}%", failure_rate * 100.0)
                ).await?;
            }
        }
        
        Ok(())
    }
    
    #[instrument(skip(self, alert_type, message))]
    async fn send_alert(&self, alert_type: &AlertType, message: &str) -> Result<(), AlertError> {
        error!(alert_type = ?alert_type, message = message, "Sending alert");
        
        // 发送告警通知（邮件、短信、钉钉等）
        self.notification_client.send(message).await?;
        
        Ok(())
    }
    
    async fn check_payment_timeout(&self) -> Result<(), AlertError> {
        // 实现支付超时检查
        Ok(())
    }
    
    async fn check_risk_blockage_spike(&self) -> Result<(), AlertError> {
        // 实现风控拦截激增检查
        Ok(())
    }
}

#[derive(Debug, thiserror::Error)]
pub enum AlertError {
    #[error("Database error: {0}")]
    DatabaseError(String),
    
    #[error("Notification error: {0}")]
    NotificationError(String),
}

/// 通知客户端（示例）
pub struct NotificationClient;

impl NotificationClient {
    pub async fn send(&self, message: &str) -> Result<(), Box<dyn std::error::Error>> {
        // 发送通知实现
        println!("Sending notification: {}", message);
        Ok(())
    }
}
```

---

## 11. 完整示例

### main.rs

```rust
use axum::{
    routing::{get, post},
    Router,
    extract::State,
};
use std::sync::Arc;
use tower_http::trace::TraceLayer;
use opentelemetry::global;
use opentelemetry_sdk::trace::TracerProvider;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化追踪
    let tracer_provider = init_tracer()?;
    global::set_tracer_provider(tracer_provider.clone());
    
    // 初始化日志
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .json()
        .init();
    
    info!("Starting Fintech Core System");
    
    // 初始化数据库
    let db_pool = init_db_pool().await?;
    
    // 初始化 Redis
    let redis_client = redis::Client::open("redis://localhost:6379")?;
    
    // 初始化 Kafka
    let kafka_producer = Arc::new(init_kafka_producer()?);
    
    // 初始化服务
    let account_service = Arc::new(AccountService {
        db_pool: db_pool.clone(),
        redis_client: redis_client.clone(),
    });
    
    let risk_service = Arc::new(RiskControlService {
        db_pool: db_pool.clone(),
        redis_client: redis_client.clone(),
    });
    
    let transaction_service = Arc::new(TransactionService {
        db_pool: db_pool.clone(),
        account_service: account_service.clone(),
        risk_service: risk_service.clone(),
        kafka_producer: kafka_producer.clone(),
    });
    
    let payment_gateway = Arc::new(PaymentGatewayService {
        http_client: reqwest::Client::new(),
        db_pool: db_pool.clone(),
    });
    
    let audit_service = Arc::new(AuditService {
        db_pool: db_pool.clone(),
        kafka_producer: kafka_producer.clone(),
    });
    
    // 构建应用状态
    let app_state = AppState {
        account_service,
        transaction_service,
        payment_gateway,
        risk_service,
        audit_service,
    };
    
    // 构建路由
    let app = Router::new()
        .route("/health", get(health_check))
        .route("/api/accounts", post(create_account))
        .route("/api/accounts/:id/balance", get(get_balance))
        .route("/api/transactions/transfer", post(transfer))
        .route("/api/payments/create", post(create_payment))
        .route("/api/payments/callback", post(payment_callback))
        .layer(TraceLayer::new_for_http())
        .layer(axum::middleware::from_fn(audit_middleware))
        .with_state(Arc::new(app_state));
    
    // 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:8080").await?;
    
    info!("Server listening on {}", listener.local_addr()?);
    
    axum::serve(listener, app).await?;
    
    // 关闭追踪
    global::shutdown_tracer_provider();
    
    Ok(())
}

/// 应用状态
#[derive(Clone)]
pub struct AppState {
    pub account_service: Arc<AccountService>,
    pub transaction_service: Arc<TransactionService>,
    pub payment_gateway: Arc<PaymentGatewayService>,
    pub risk_service: Arc<RiskControlService>,
    pub audit_service: Arc<AuditService>,
}

/// 健康检查
async fn health_check() -> &'static str {
    "OK"
}

/// 初始化追踪器
fn init_tracer() -> Result<TracerProvider, Box<dyn std::error::Error>> {
    use opentelemetry_otlp::WithExportConfig;
    
    let tracer_provider = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    Ok(tracer_provider)
}
```

---

## 12. 最佳实践

### 1. 事务一致性

```rust
// ✅ 推荐：使用数据库事务保证一致性
#[instrument]
pub async fn transfer_with_transaction(
    pool: &sqlx::PgPool,
    from: Uuid,
    to: Uuid,
    amount: Decimal,
) -> Result<(), TransactionError> {
    let mut tx = pool.begin().await?;
    
    // 所有操作在同一事务中
    debit_account(&mut tx, from, amount).await?;
    credit_account(&mut tx, to, amount).await?;
    create_transaction_record(&mut tx, from, to, amount).await?;
    
    tx.commit().await?;
    Ok(())
}

// ❌ 避免：分离的操作可能导致不一致
pub async fn transfer_without_transaction(
    pool: &sqlx::PgPool,
    from: Uuid,
    to: Uuid,
    amount: Decimal,
) -> Result<(), TransactionError> {
    debit_account_standalone(pool, from, amount).await?;
    // 如果这里失败，扣款已完成但入账未完成
    credit_account_standalone(pool, to, amount).await?;
    Ok(())
}
```

### 2. 性能优化

```rust
// ✅ 推荐：使用缓存减少数据库压力
#[instrument]
pub async fn get_account_with_cache(
    pool: &sqlx::PgPool,
    redis: &redis::Client,
    account_id: Uuid,
) -> Result<Account, AccountError> {
    // 先查缓存
    if let Some(cached) = get_from_cache(redis, account_id).await? {
        return Ok(cached);
    }
    
    // 缓存未命中，查数据库
    let account = query_account(pool, account_id).await?;
    
    // 写入缓存
    set_to_cache(redis, &account).await?;
    
    Ok(account)
}

// ✅ 推荐：批量操作
#[instrument]
pub async fn batch_update_balances(
    tx: &mut sqlx::Transaction<'_, sqlx::Postgres>,
    updates: &[(Uuid, Decimal)],
) -> Result<(), TransactionError> {
    for (account_id, amount) in updates {
        sqlx::query("UPDATE accounts SET balance = balance + $1 WHERE id = $2")
            .bind(amount)
            .bind(account_id)
            .execute(&mut **tx)
            .await?;
    }
    Ok(())
}
```

### 3. 安全加固

```rust
// ✅ 推荐：参数化查询防止 SQL 注入
#[instrument]
pub async fn get_user_safe(
    pool: &sqlx::PgPool,
    username: &str,
) -> Result<User, UserError> {
    sqlx::query_as::<_, User>(
        "SELECT * FROM users WHERE username = $1"
    )
    .bind(username)
    .fetch_one(pool)
    .await
    .map_err(|e| UserError::NotFound)
}

// ❌ 危险：字符串拼接容易 SQL 注入
pub async fn get_user_unsafe(
    pool: &sqlx::PgPool,
    username: &str,
) -> Result<User, UserError> {
    let query = format!("SELECT * FROM users WHERE username = '{}'", username);
    // 如果 username 是 "admin' OR '1'='1"，将泄露所有用户
    todo!()
}

// ✅ 推荐：敏感数据加密存储
#[instrument]
pub async fn store_sensitive_data(
    pool: &sqlx::PgPool,
    user_id: Uuid,
    data: &str,
) -> Result<(), StorageError> {
    let encrypted = encrypt_data(data)?;
    
    sqlx::query("INSERT INTO sensitive_data (user_id, data) VALUES ($1, $2)")
        .bind(user_id)
        .bind(&encrypted)
        .execute(pool)
        .await?;
    
    Ok(())
}
```

---

## 总结

本文档展示了金融行业核心系统的完整 OpenTelemetry Rust 实战：

1. ✅ **完整架构**: 账户、交易、风控、支付、审计五大核心服务
2. ✅ **全链路追踪**: 从 API 网关到数据库的完整追踪
3. ✅ **性能监控**: 自定义 Metrics 和业务指标
4. ✅ **安全合规**: 敏感数据脱敏、审计日志、SQL 注入防护
5. ✅ **高可用设计**: 数据库事务、缓存策略、异步消息队列
6. ✅ **告警通知**: 实时监控和异常告警

通过本案例，您可以构建生产级的金融系统可观测性平台。

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-08  
**维护者**: OTLP Rust Team  
**许可证**: MIT OR Apache-2.0
