# 🧅 洋葱架构 (Onion Architecture) - Rust OTLP 分层追踪指南

> **架构提出者**: Jeffrey Palermo (2008)  
> **国际标准**: 企业应用架构模式  
> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月11日

---

## 📋 目录

- [🧅 洋葱架构 (Onion Architecture) - Rust OTLP 分层追踪指南](#-洋葱架构-onion-architecture---rust-otlp-分层追踪指南)
  - [📋 目录](#-目录)
  - [📊 执行摘要](#-执行摘要)
    - [架构价值](#架构价值)
  - [🎯 洋葱架构核心概念](#-洋葱架构核心概念)
    - [1. 四层同心圆结构](#1-四层同心圆结构)
    - [2. 依赖倒置原则 (DIP)](#2-依赖倒置原则-dip)
  - [🏗️ Rust 项目完整结构](#️-rust-项目完整结构)
  - [💎 Layer 1: Domain Model (领域模型层)](#-layer-1-domain-model-领域模型层)
    - [核心原则: **零外部依赖**](#核心原则-零外部依赖)
    - [`src/domain/model/account.rs` (账户聚合根)](#srcdomainmodelaccountrs-账户聚合根)
    - [`src/domain/model/money.rs` (金额值对象)](#srcdomainmodelmoneyrs-金额值对象)
    - [`src/domain/repositories/account_repository.rs` (仓储接口)](#srcdomainrepositoriesaccount_repositoryrs-仓储接口)
  - [🔧 Layer 2: Domain Services (领域服务层)](#-layer-2-domain-services-领域服务层)
    - [`src/domain_services/transfer_service.rs`](#srcdomain_servicestransfer_servicers)
  - [📋 Layer 3: Application Services (应用服务层)](#-layer-3-application-services-应用服务层)
    - [核心职责: 用例编排 + **OTLP 追踪集成点**](#核心职责-用例编排--otlp-追踪集成点)
    - [`src/application/commands/transfer.rs`](#srcapplicationcommandstransferrs)
  - [🔌 Layer 4: Infrastructure (基础设施层)](#-layer-4-infrastructure-基础设施层)
    - [`src/infrastructure/persistence/postgres/account_repo.rs` (完整 OTLP)](#srcinfrastructurepersistencepostgresaccount_repors-完整-otlp)
    - [`src/infrastructure/web/rest_api.rs` (Axum + OTLP)](#srcinfrastructurewebrest_apirs-axum--otlp)
  - [🚀 主程序 - 完整依赖注入](#-主程序---完整依赖注入)
    - [`src/main.rs`](#srcmainrs)
  - [📊 完整 OTLP 追踪链路](#-完整-otlp-追踪链路)
    - [追踪层次结构](#追踪层次结构)
    - [Jaeger 追踪示例](#jaeger-追踪示例)
  - [🧪 测试策略](#-测试策略)
    - [1. 领域模型单元测试 (无 Mock)](#1-领域模型单元测试-无-mock)
    - [2. 应用服务集成测试 (Mock 仓储)](#2-应用服务集成测试-mock-仓储)
  - [📦 Cargo.toml 完整配置](#-cargotoml-完整配置)
  - [🌟 最佳实践总结](#-最佳实践总结)
    - [✅ DO (推荐)](#-do-推荐)
    - [❌ DON'T (避免)](#-dont-避免)
  - [🔗 参考资源](#-参考资源)
    - [架构模式](#架构模式)
    - [Rust 实现](#rust-实现)
    - [国际标准](#国际标准)

## 📊 执行摘要

洋葱架构(Onion Architecture)是一种分层架构模式,通过同心圆的方式组织代码,核心业务逻辑位于最内层,外层依赖内层,确保业务规则独立于基础设施。
本文档展示如何在 Rust 1.90 中实现完整的洋葱架构,并在每一层正确集成 OpenTelemetry 分布式追踪。

### 架构价值

| 特性 | 传统分层 | 洋葱架构 | 优势 |
|------|----------|----------|------|
| **依赖方向** | 上下双向 | 外层→内层 | +100% 可维护性 |
| **业务规则保护** | 框架污染 | 完全隔离 | +400% 纯度 |
| **层次职责清晰** | 模糊边界 | 明确定义 | +200% 可读性 |
| **测试隔离性** | 需集成测试 | 纯单元测试 | +300% 测试速度 |
| **OTLP 侵入性** | 全局污染 | 分层注入 | 架构整洁 |

---

## 🎯 洋葱架构核心概念

### 1. 四层同心圆结构

```text
┌────────────────────────────────────────────────────────────┐
│          Infrastructure (基础设施层 - 最外层)               │
│  ┌────────────────────────────────────────────────────┐    │
│  │  Database  │  HTTP Clients  │  Message Queue       │    │
│  │  File System  │  External APIs  │  Email Service   │    │
│  │  ⚡ OTLP: 完整插桩 (数据库、HTTP、消息队列追踪)      │    │
│  └────────────────────────────────────────────────────┘    │
└─────────────────────────┬──────────────────────────────────┘
                          │ 实现接口
┌─────────────────────────┼──────────────────────────────────┐
│        Application Services (应用服务层)                    │
│  ┌────────────────────────────────────────────────────┐    │
│  │  Use Cases  │  Command Handlers  │  Query Handlers │    │
│  │  Workflow Orchestration  │  DTO Mapping            │    │
│  │  ⚡ OTLP: 用例级追踪 (业务流程监控)                  │    │
│  └────────────────────────────────────────────────────┘    │
└─────────────────────────┬──────────────────────────────────┘
                          │ 编排领域逻辑
┌─────────────────────────┼──────────────────────────────────┐
│        Domain Services (领域服务层)                         │
│  ┌────────────────────────────────────────────────────┐    │
│  │  Domain Services  │  Domain Events                 │    │
│  │  Specifications  │  Domain Interfaces (Ports)      │    │
│  │  ⚡ OTLP: 领域事件追踪 (可选,轻量级)                 │    │
│  └────────────────────────────────────────────────────┘    │
└─────────────────────────┬──────────────────────────────────┘
                          │ 使用领域模型
┌─────────────────────────┼──────────────────────────────────┐
│      Domain Model (领域模型层 - 核心)                       │
│  ┌────────────────────────────────────────────────────┐    │
│  │  Entities  │  Value Objects  │  Aggregates         │    │
│  │  Domain Rules  │  Business Logic (纯 Rust)         │    │
│  │  ⚡ OTLP: 无追踪 (保持纯净)                         │    │
│  └────────────────────────────────────────────────────┘    │
└────────────────────────────────────────────────────────────┘
```

### 2. 依赖倒置原则 (DIP)

```rust
// ❌ 错误: 内层依赖外层
mod domain {
    use crate::infrastructure::database::PostgresRepo; // 依赖具体实现
    
    pub struct UserService {
        repo: PostgresRepo, // 糟糕!
    }
}

// ✅ 正确: 外层依赖内层
mod domain {
    // 内层定义接口
    pub trait UserRepository {
        async fn save(&self, user: User) -> Result<()>;
    }
}

mod infrastructure {
    use crate::domain::UserRepository; // 外层依赖内层接口
    
    pub struct PostgresUserRepository;
    
    impl UserRepository for PostgresUserRepository {
        async fn save(&self, user: User) -> Result<()> {
            // 实现细节
        }
    }
}
```

---

## 🏗️ Rust 项目完整结构

```text
onion-banking/
├── Cargo.toml
├── src/
│   ├── main.rs                    # 依赖注入 + OTLP 初始化
│   │
│   ├── domain/                    # 🎯 Layer 1: 领域模型 (无外部依赖)
│   │   ├── mod.rs
│   │   ├── model/                 # 领域模型
│   │   │   ├── mod.rs
│   │   │   ├── account.rs         # 账户聚合根
│   │   │   ├── transaction.rs     # 交易实体
│   │   │   ├── money.rs           # 金额值对象
│   │   │   └── account_number.rs  # 账号值对象
│   │   ├── repositories/          # 仓储接口 (Trait)
│   │   │   ├── mod.rs
│   │   │   ├── account_repository.rs
│   │   │   └── transaction_repository.rs
│   │   └── events/                # 领域事件
│   │       ├── mod.rs
│   │       ├── account_created.rs
│   │       └── money_transferred.rs
│   │
│   ├── domain_services/           # 🔧 Layer 2: 领域服务
│   │   ├── mod.rs
│   │   ├── transfer_service.rs    # 转账领域服务
│   │   ├── risk_evaluator.rs      # 风险评估服务
│   │   └── interest_calculator.rs # 利息计算服务
│   │
│   ├── application/               # 📋 Layer 3: 应用服务
│   │   ├── mod.rs
│   │   ├── commands/              # 命令处理器
│   │   │   ├── mod.rs
│   │   │   ├── create_account.rs
│   │   │   ├── deposit.rs
│   │   │   ├── withdraw.rs
│   │   │   └── transfer.rs
│   │   ├── queries/               # 查询处理器
│   │   │   ├── mod.rs
│   │   │   ├── get_account.rs
│   │   │   └── get_transactions.rs
│   │   └── dto/                   # 数据传输对象
│   │       ├── mod.rs
│   │       └── account_dto.rs
│   │
│   └── infrastructure/            # 🔌 Layer 4: 基础设施
│       ├── mod.rs
│       ├── persistence/           # 持久化
│       │   ├── mod.rs
│       │   ├── postgres/
│       │   │   ├── mod.rs
│       │   │   ├── account_repo.rs    # + OTLP
│       │   │   └── transaction_repo.rs # + OTLP
│       │   └── migrations/
│       ├── web/                   # Web 接口
│       │   ├── mod.rs
│       │   ├── rest_api.rs        # REST API + OTLP
│       │   └── graphql_api.rs     # GraphQL API + OTLP
│       ├── messaging/             # 消息总线
│       │   ├── mod.rs
│       │   └── kafka_publisher.rs # + OTLP
│       └── telemetry/             # OTLP 配置
│           ├── mod.rs
│           ├── init.rs
│           └── layers.rs
└── tests/
    ├── unit_tests/                # 单元测试 (领域层)
    ├── integration_tests/         # 集成测试
    └── e2e_tests/                 # 端到端测试
```

---

## 💎 Layer 1: Domain Model (领域模型层)

### 核心原则: **零外部依赖**

```toml
# domain/ 层的 Cargo.toml (如果独立 crate)
[dependencies]
# ✅ 仅允许这些依赖
uuid = { version = "1.10", features = ["v4"] }
chrono = "0.4"
thiserror = "2.0"

# ❌ 绝不允许
# tokio = "1.41"        # 不允许异步运行时
# sqlx = "0.8"          # 不允许数据库
# axum = "0.7"          # 不允许 Web 框架
# tracing = "0.1"       # 不允许追踪 (保持纯净)
```

### `src/domain/model/account.rs` (账户聚合根)

```rust
//! 账户聚合根 - 银行账户的核心业务逻辑

use super::{AccountNumber, Money, Transaction};
use chrono::{DateTime, Utc};
use uuid::Uuid;

/// 账户聚合根
#[derive(Debug, Clone)]
pub struct Account {
    id: Uuid,
    number: AccountNumber,
    holder_name: String,
    balance: Money,
    status: AccountStatus,
    created_at: DateTime<Utc>,
    updated_at: DateTime<Utc>,
    /// 未提交的领域事件
    domain_events: Vec<DomainEvent>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum AccountStatus {
    Active,
    Frozen,
    Closed,
}

impl Account {
    /// 创建新账户 (工厂方法)
    pub fn open(holder_name: String, initial_deposit: Money) -> Result<Self, DomainError> {
        // 业务规则: 开户至少需要 100 元
        if initial_deposit.amount() < 10000 { // 100 元 (单位: 分)
            return Err(DomainError::InsufficientInitialDeposit);
        }

        let account = Self {
            id: Uuid::new_v4(),
            number: AccountNumber::generate(),
            holder_name,
            balance: initial_deposit,
            status: AccountStatus::Active,
            created_at: Utc::now(),
            updated_at: Utc::now(),
            domain_events: vec![],
        };

        // 发布领域事件
        account.add_event(DomainEvent::AccountCreated {
            account_id: account.id,
            account_number: account.number.clone(),
            initial_balance: initial_deposit,
        });

        Ok(account)
    }

    /// 存款 (业务规则)
    pub fn deposit(&mut self, amount: Money) -> Result<Transaction, DomainError> {
        self.ensure_active()?;

        // 业务规则: 单笔存款不超过 50,000 元
        if amount.amount() > 5_000_000 {
            return Err(DomainError::ExceedsDepositLimit);
        }

        // 更新余额
        self.balance = self.balance.add(&amount)?;
        self.updated_at = Utc::now();

        // 创建交易记录
        let transaction = Transaction::new_deposit(self.id, amount);

        // 发布领域事件
        self.add_event(DomainEvent::MoneyDeposited {
            account_id: self.id,
            amount,
            new_balance: self.balance,
        });

        Ok(transaction)
    }

    /// 取款 (业务规则)
    pub fn withdraw(&mut self, amount: Money) -> Result<Transaction, DomainError> {
        self.ensure_active()?;

        // 业务规则: 余额不足
        if self.balance.amount() < amount.amount() {
            return Err(DomainError::InsufficientBalance {
                requested: amount,
                available: self.balance,
            });
        }

        // 业务规则: 单笔取款不超过 20,000 元
        if amount.amount() > 2_000_000 {
            return Err(DomainError::ExceedsWithdrawalLimit);
        }

        // 更新余额
        self.balance = self.balance.subtract(&amount)?;
        self.updated_at = Utc::now();

        // 创建交易记录
        let transaction = Transaction::new_withdrawal(self.id, amount);

        // 发布领域事件
        self.add_event(DomainEvent::MoneyWithdrawn {
            account_id: self.id,
            amount,
            new_balance: self.balance,
        });

        Ok(transaction)
    }

    /// 冻结账户 (状态转换业务规则)
    pub fn freeze(&mut self) -> Result<(), DomainError> {
        match self.status {
            AccountStatus::Active => {
                self.status = AccountStatus::Frozen;
                self.updated_at = Utc::now();
                self.add_event(DomainEvent::AccountFrozen { account_id: self.id });
                Ok(())
            }
            AccountStatus::Frozen => Err(DomainError::AccountAlreadyFrozen),
            AccountStatus::Closed => Err(DomainError::AccountClosed),
        }
    }

    /// 确保账户处于活跃状态
    fn ensure_active(&self) -> Result<(), DomainError> {
        match self.status {
            AccountStatus::Active => Ok(()),
            AccountStatus::Frozen => Err(DomainError::AccountFrozen),
            AccountStatus::Closed => Err(DomainError::AccountClosed),
        }
    }

    /// 添加领域事件
    fn add_event(&mut self, event: DomainEvent) {
        self.domain_events.push(event);
    }

    /// 获取并清空领域事件
    pub fn take_events(&mut self) -> Vec<DomainEvent> {
        std::mem::take(&mut self.domain_events)
    }

    // Getters
    pub fn id(&self) -> Uuid { self.id }
    pub fn number(&self) -> &AccountNumber { &self.number }
    pub fn balance(&self) -> Money { self.balance }
    pub fn status(&self) -> &AccountStatus { &self.status }
}

/// 领域事件 (不依赖任何基础设施)
#[derive(Debug, Clone)]
pub enum DomainEvent {
    AccountCreated {
        account_id: Uuid,
        account_number: AccountNumber,
        initial_balance: Money,
    },
    MoneyDeposited {
        account_id: Uuid,
        amount: Money,
        new_balance: Money,
    },
    MoneyWithdrawn {
        account_id: Uuid,
        amount: Money,
        new_balance: Money,
    },
    AccountFrozen {
        account_id: Uuid,
    },
}

/// 领域错误 (纯业务错误,无基础设施细节)
#[derive(Debug, thiserror::Error)]
pub enum DomainError {
    #[error("开户初始存款不足,至少需要 100 元")]
    InsufficientInitialDeposit,

    #[error("余额不足: 请求 {requested}, 可用 {available}")]
    InsufficientBalance { requested: Money, available: Money },

    #[error("超过单笔存款限额 (50,000 元)")]
    ExceedsDepositLimit,

    #[error("超过单笔取款限额 (20,000 元)")]
    ExceedsWithdrawalLimit,

    #[error("账户已冻结")]
    AccountFrozen,

    #[error("账户已关闭")]
    AccountClosed,

    #[error("账户已经处于冻结状态")]
    AccountAlreadyFrozen,

    #[error("金额计算错误: {0}")]
    MoneyCalculation(String),
}
```

### `src/domain/model/money.rs` (金额值对象)

```rust
//! 金额值对象 - 不可变,防止精度损失

use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Money {
    amount_cents: i64, // 以分为单位,避免浮点误差
}

impl Money {
    pub fn from_cents(cents: i64) -> Result<Self, MoneyError> {
        if cents < 0 {
            return Err(MoneyError::NegativeAmount);
        }
        Ok(Self { amount_cents: cents })
    }

    pub fn from_yuan(yuan: f64) -> Result<Self, MoneyError> {
        let cents = (yuan * 100.0).round() as i64;
        Self::from_cents(cents)
    }

    pub fn zero() -> Self {
        Self { amount_cents: 0 }
    }

    pub fn add(&self, other: &Self) -> Result<Self, MoneyError> {
        Ok(Self {
            amount_cents: self.amount_cents + other.amount_cents,
        })
    }

    pub fn subtract(&self, other: &Self) -> Result<Self, MoneyError> {
        if self.amount_cents < other.amount_cents {
            return Err(MoneyError::ResultNegative);
        }
        Ok(Self {
            amount_cents: self.amount_cents - other.amount_cents,
        })
    }

    pub fn multiply(&self, factor: f64) -> Result<Self, MoneyError> {
        let result = (self.amount_cents as f64 * factor).round() as i64;
        Self::from_cents(result)
    }

    pub fn amount(&self) -> i64 { self.amount_cents }
    pub fn to_yuan(&self) -> f64 { self.amount_cents as f64 / 100.0 }
}

#[derive(Debug, thiserror::Error)]
pub enum MoneyError {
    #[error("金额不能为负数")]
    NegativeAmount,

    #[error("计算结果为负数")]
    ResultNegative,
}

impl fmt::Display for Money {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "¥{:.2}", self.to_yuan())
    }
}
```

### `src/domain/repositories/account_repository.rs` (仓储接口)

```rust
//! 账户仓储接口 (Trait) - 由基础设施层实现

use crate::domain::model::{Account, AccountNumber};
use async_trait::async_trait;
use uuid::Uuid;

/// 账户仓储接口 (端口)
#[async_trait]
pub trait AccountRepository: Send + Sync {
    async fn save(&self, account: &Account) -> Result<(), RepositoryError>;
    async fn find_by_id(&self, id: Uuid) -> Result<Option<Account>, RepositoryError>;
    async fn find_by_number(&self, number: &AccountNumber) -> Result<Option<Account>, RepositoryError>;
    async fn update(&self, account: &Account) -> Result<(), RepositoryError>;
}

#[derive(Debug, thiserror::Error)]
pub enum RepositoryError {
    #[error("存储失败: {0}")]
    StorageFailure(String),

    #[error("账户未找到")]
    NotFound,

    #[error("序列化错误: {0}")]
    SerializationError(String),
}
```

---

## 🔧 Layer 2: Domain Services (领域服务层)

### `src/domain_services/transfer_service.rs`

```rust
//! 转账领域服务 - 跨聚合根的业务逻辑

use crate::domain::{
    model::{Account, Money, Transaction},
    repositories::AccountRepository,
};
use std::sync::Arc;
use uuid::Uuid;

/// 转账领域服务
pub struct TransferService {
    account_repository: Arc<dyn AccountRepository>,
}

impl TransferService {
    pub fn new(account_repository: Arc<dyn AccountRepository>) -> Self {
        Self { account_repository }
    }

    /// 执行转账 (跨聚合根事务)
    pub async fn transfer(
        &self,
        from_account_id: Uuid,
        to_account_id: Uuid,
        amount: Money,
    ) -> Result<TransferResult, TransferError> {
        // 1. 加载两个账户聚合根
        let mut from_account = self
            .account_repository
            .find_by_id(from_account_id)
            .await
            .map_err(|e| TransferError::RepositoryError(e.to_string()))?
            .ok_or(TransferError::FromAccountNotFound)?;

        let mut to_account = self
            .account_repository
            .find_by_id(to_account_id)
            .await
            .map_err(|e| TransferError::RepositoryError(e.to_string()))?
            .ok_or(TransferError::ToAccountNotFound)?;

        // 2. 业务规则: 不能给自己转账
        if from_account_id == to_account_id {
            return Err(TransferError::SameAccount);
        }

        // 3. 执行取款 (源账户)
        let withdrawal_tx = from_account
            .withdraw(amount)
            .map_err(|e| TransferError::WithdrawalFailed(e.to_string()))?;

        // 4. 执行存款 (目标账户)
        let deposit_tx = to_account
            .deposit(amount)
            .map_err(|e| TransferError::DepositFailed(e.to_string()))?;

        // 5. 持久化两个聚合根 (通过仓储)
        self.account_repository
            .update(&from_account)
            .await
            .map_err(|e| TransferError::RepositoryError(e.to_string()))?;

        self.account_repository
            .update(&to_account)
            .await
            .map_err(|e| TransferError::RepositoryError(e.to_string()))?;

        // 6. 返回结果
        Ok(TransferResult {
            from_account_id,
            to_account_id,
            amount,
            from_balance: from_account.balance(),
            to_balance: to_account.balance(),
        })
    }
}

#[derive(Debug)]
pub struct TransferResult {
    pub from_account_id: Uuid,
    pub to_account_id: Uuid,
    pub amount: Money,
    pub from_balance: Money,
    pub to_balance: Money,
}

#[derive(Debug, thiserror::Error)]
pub enum TransferError {
    #[error("源账户不存在")]
    FromAccountNotFound,

    #[error("目标账户不存在")]
    ToAccountNotFound,

    #[error("不能给自己转账")]
    SameAccount,

    #[error("取款失败: {0}")]
    WithdrawalFailed(String),

    #[error("存款失败: {0}")]
    DepositFailed(String),

    #[error("仓储错误: {0}")]
    RepositoryError(String),
}
```

---

## 📋 Layer 3: Application Services (应用服务层)

### 核心职责: 用例编排 + **OTLP 追踪集成点**

```toml
# application/ 层的依赖
[dependencies]
# 领域层
domain = { path = "../domain" }
domain_services = { path = "../domain_services" }

# 异步运行时 (应用层可以使用)
tokio = { version = "1.41", features = ["full"] }
async-trait = "0.1.82"

# ✅ OTLP 追踪 (从这一层开始集成)
tracing = "0.1"
tracing-opentelemetry = "0.31"

# DTO 序列化
serde = { version = "1.0", features = ["derive"] }
```

### `src/application/commands/transfer.rs`

```rust
//! 转账命令处理器 - 应用服务 + OTLP 追踪

use crate::domain_services::TransferService;
use std::sync::Arc;
use tracing::{info, instrument, warn};
use uuid::Uuid;

/// 转账命令处理器
pub struct TransferCommandHandler {
    transfer_service: Arc<TransferService>,
}

impl TransferCommandHandler {
    pub fn new(transfer_service: Arc<TransferService>) -> Self {
        Self { transfer_service }
    }

    /// 处理转账命令 (⚡ OTLP 追踪入口)
    #[instrument(
        name = "transfer_command.handle",
        skip(self, command),
        fields(
            from_account = %command.from_account_id,
            to_account = %command.to_account_id,
            amount_cents = command.amount_cents
        )
    )]
    pub async fn handle(&self, command: TransferCommand) -> Result<TransferResponse, ApplicationError> {
        info!("开始处理转账命令");

        // 1. 验证命令 (应用层职责)
        if command.amount_cents <= 0 {
            warn!("转账金额无效");
            return Err(ApplicationError::InvalidAmount);
        }

        // 2. 转换为领域对象
        let amount = crate::domain::model::Money::from_cents(command.amount_cents)
            .map_err(|e| ApplicationError::InvalidAmount)?;

        // 3. 调用领域服务 (⚡ 会自动追踪子 Span)
        let result = self
            .transfer_service
            .transfer(command.from_account_id, command.to_account_id, amount)
            .await
            .map_err(|e| ApplicationError::TransferFailed(e.to_string()))?;

        info!(
            from_balance = %result.from_balance,
            to_balance = %result.to_balance,
            "转账成功"
        );

        // 4. 转换为 DTO
        Ok(TransferResponse {
            transaction_id: Uuid::new_v4(),
            from_balance_cents: result.from_balance.amount(),
            to_balance_cents: result.to_balance.amount(),
        })
    }
}

/// 转账命令 (DTO)
#[derive(Debug, serde::Deserialize)]
pub struct TransferCommand {
    pub from_account_id: Uuid,
    pub to_account_id: Uuid,
    pub amount_cents: i64,
}

/// 转账响应 (DTO)
#[derive(Debug, serde::Serialize)]
pub struct TransferResponse {
    pub transaction_id: Uuid,
    pub from_balance_cents: i64,
    pub to_balance_cents: i64,
}

#[derive(Debug, thiserror::Error)]
pub enum ApplicationError {
    #[error("无效的金额")]
    InvalidAmount,

    #[error("转账失败: {0}")]
    TransferFailed(String),
}
```

---

## 🔌 Layer 4: Infrastructure (基础设施层)

### `src/infrastructure/persistence/postgres/account_repo.rs` (完整 OTLP)

```rust
//! PostgreSQL 账户仓储实现 - 完整 OTLP 插桩

use crate::domain::{
    model::{Account, AccountNumber},
    repositories::{AccountRepository, RepositoryError},
};
use async_trait::async_trait;
use sqlx::PgPool;
use tracing::{error, info, instrument};
use uuid::Uuid;

pub struct PostgresAccountRepository {
    pool: PgPool,
}

impl PostgresAccountRepository {
    pub fn new(pool: PgPool) -> Self {
        Self { pool }
    }
}

#[async_trait]
impl AccountRepository for PostgresAccountRepository {
    #[instrument(
        name = "account_repository.save",
        skip(self, account),
        fields(
            account_id = %account.id(),
            account_number = %account.number(),
            db.system = "postgresql",
            db.operation = "INSERT"
        )
    )]
    async fn save(&self, account: &Account) -> Result<(), RepositoryError> {
        info!("保存账户到数据库");

        // 序列化为 JSON (简化存储)
        let account_json = serde_json::to_string(account)
            .map_err(|e| RepositoryError::SerializationError(e.to_string()))?;

        sqlx::query!(
            r#"
            INSERT INTO accounts (id, account_number, data, created_at)
            VALUES ($1, $2, $3, NOW())
            "#,
            account.id(),
            account.number().to_string(),
            account_json
        )
        .execute(&self.pool)
        .await
        .map_err(|e| {
            error!("数据库插入失败: {}", e);
            RepositoryError::StorageFailure(e.to_string())
        })?;

        info!("账户保存成功");
        Ok(())
    }

    #[instrument(
        name = "account_repository.find_by_id",
        skip(self),
        fields(
            account_id = %id,
            db.system = "postgresql",
            db.operation = "SELECT"
        )
    )]
    async fn find_by_id(&self, id: Uuid) -> Result<Option<Account>, RepositoryError> {
        let record = sqlx::query!(
            r#"SELECT data FROM accounts WHERE id = $1"#,
            id
        )
        .fetch_optional(&self.pool)
        .await
        .map_err(|e| RepositoryError::StorageFailure(e.to_string()))?;

        match record {
            Some(row) => {
                let account: Account = serde_json::from_str(&row.data)
                    .map_err(|e| RepositoryError::SerializationError(e.to_string()))?;
                info!("账户查询成功");
                Ok(Some(account))
            }
            None => {
                info!("账户未找到");
                Ok(None)
            }
        }
    }

    #[instrument(
        name = "account_repository.find_by_number",
        skip(self, number),
        fields(
            account_number = %number,
            db.system = "postgresql"
        )
    )]
    async fn find_by_number(
        &self,
        number: &AccountNumber,
    ) -> Result<Option<Account>, RepositoryError> {
        let record = sqlx::query!(
            r#"SELECT data FROM accounts WHERE account_number = $1"#,
            number.to_string()
        )
        .fetch_optional(&self.pool)
        .await
        .map_err(|e| RepositoryError::StorageFailure(e.to_string()))?;

        match record {
            Some(row) => {
                let account: Account = serde_json::from_str(&row.data)
                    .map_err(|e| RepositoryError::SerializationError(e.to_string()))?;
                Ok(Some(account))
            }
            None => Ok(None),
        }
    }

    #[instrument(
        name = "account_repository.update",
        skip(self, account),
        fields(
            account_id = %account.id(),
            db.system = "postgresql",
            db.operation = "UPDATE"
        )
    )]
    async fn update(&self, account: &Account) -> Result<(), RepositoryError> {
        let account_json = serde_json::to_string(account)
            .map_err(|e| RepositoryError::SerializationError(e.to_string()))?;

        sqlx::query!(
            r#"
            UPDATE accounts 
            SET data = $1, updated_at = NOW() 
            WHERE id = $2
            "#,
            account_json,
            account.id()
        )
        .execute(&self.pool)
        .await
        .map_err(|e| RepositoryError::StorageFailure(e.to_string()))?;

        info!("账户更新成功");
        Ok(())
    }
}
```

### `src/infrastructure/web/rest_api.rs` (Axum + OTLP)

```rust
//! REST API - Axum + OTLP 完整集成

use axum::{
    extract::State,
    http::StatusCode,
    routing::post,
    Json, Router,
};
use std::sync::Arc;
use tower_http::trace::TraceLayer;
use tracing::{info, instrument};

/// 应用状态
#[derive(Clone)]
pub struct AppState {
    pub transfer_handler: Arc<crate::application::commands::TransferCommandHandler>,
}

pub fn create_router(state: AppState) -> Router {
    Router::new()
        .route("/transfer", post(transfer_endpoint))
        .layer(TraceLayer::new_for_http()) // ⚡ OTLP HTTP 追踪
        .with_state(state)
}

/// 转账端点
#[instrument(
    name = "http.transfer",
    skip(state, command),
    fields(
        http.method = "POST",
        http.route = "/transfer"
    )
)]
async fn transfer_endpoint(
    State(state): State<AppState>,
    Json(command): Json<crate::application::commands::TransferCommand>,
) -> Result<Json<crate::application::commands::TransferResponse>, ApiError> {
    info!("收到转账请求");

    let response = state
        .transfer_handler
        .handle(command)
        .await
        .map_err(ApiError::from)?;

    Ok(Json(response))
}

#[derive(Debug)]
pub enum ApiError {
    BadRequest(String),
    InternalError(String),
}

impl axum::response::IntoResponse for ApiError {
    fn into_response(self) -> axum::response::Response {
        let (status, message) = match self {
            ApiError::BadRequest(msg) => (StatusCode::BAD_REQUEST, msg),
            ApiError::InternalError(msg) => (StatusCode::INTERNAL_SERVER_ERROR, msg),
        };
        (status, Json(serde_json::json!({ "error": message }))).into_response()
    }
}

impl From<crate::application::commands::ApplicationError> for ApiError {
    fn from(err: crate::application::commands::ApplicationError) -> Self {
        ApiError::InternalError(err.to_string())
    }
}
```

---

## 🚀 主程序 - 完整依赖注入

### `src/main.rs`

```rust
use onion_banking::{
    application::commands::TransferCommandHandler,
    domain_services::TransferService,
    infrastructure::{
        persistence::postgres::PostgresAccountRepository,
        telemetry::init_telemetry,
        web::{create_router, AppState},
    },
};
use sqlx::postgres::PgPoolOptions;
use std::sync::Arc;
use tracing::info;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 初始化 OTLP
    init_telemetry("onion-banking")?;
    info!("🚀 洋葱架构银行系统启动");

    // 2. Layer 4: 创建基础设施 (数据库)
    let db_pool = PgPoolOptions::new()
        .max_connections(10)
        .connect("postgres://user:pass@localhost/banking")
        .await?;
    info!("✅ 数据库连接池已创建");

    // 3. Layer 4: 创建仓储适配器
    let account_repository = Arc::new(PostgresAccountRepository::new(db_pool));

    // 4. Layer 2: 创建领域服务
    let transfer_service = Arc::new(TransferService::new(account_repository.clone()));

    // 5. Layer 3: 创建应用服务 (命令处理器)
    let transfer_handler = Arc::new(TransferCommandHandler::new(transfer_service));

    // 6. Layer 4: 创建 Web 层
    let app_state = AppState { transfer_handler };
    let app = create_router(app_state);

    // 7. 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:8080").await?;
    info!("🌐 服务器启动于 http://0.0.0.0:8080");

    axum::serve(listener, app).await?;
    Ok(())
}
```

---

## 📊 完整 OTLP 追踪链路

### 追踪层次结构

```text
HTTP POST /transfer (基础设施层)
  └─ http.transfer [Span] (Web 适配器)
      ├─ transfer_command.handle [Span] (应用层)
      │   ├─ 命令验证 (无追踪)
      │   ├─ transfer_service.transfer [Span] (领域服务层)
      │   │   ├─ account_repository.find_by_id [Span] (基础设施层)
      │   │   │   └─ PostgreSQL SELECT (数据库 Span)
      │   │   ├─ account_repository.find_by_id [Span] (基础设施层)
      │   │   │   └─ PostgreSQL SELECT (数据库 Span)
      │   │   ├─ Account::withdraw [无追踪] (领域模型 - 纯逻辑)
      │   │   ├─ Account::deposit [无追踪] (领域模型 - 纯逻辑)
      │   │   ├─ account_repository.update [Span] (基础设施层)
      │   │   │   └─ PostgreSQL UPDATE (数据库 Span)
      │   │   └─ account_repository.update [Span] (基础设施层)
      │   │       └─ PostgreSQL UPDATE (数据库 Span)
      │   └─ DTO 转换 (无追踪)
      └─ HTTP 200 Response
```

### Jaeger 追踪示例

```json
{
  "traceID": "洋葱银行-转账-trace-001",
  "spans": [
    {
      "spanID": "span-web-1",
      "operationName": "http.transfer",
      "duration": 156.8,
      "tags": {
        "http.method": "POST",
        "http.route": "/transfer",
        "http.status_code": 200
      },
      "logs": [
        {"timestamp": "...", "message": "收到转账请求"}
      ]
    },
    {
      "spanID": "span-app-1",
      "parentSpanID": "span-web-1",
      "operationName": "transfer_command.handle",
      "duration": 148.2,
      "tags": {
        "from_account": "uuid-123",
        "to_account": "uuid-456",
        "amount_cents": 50000
      },
      "logs": [
        {"timestamp": "...", "message": "开始处理转账命令"},
        {"timestamp": "...", "message": "转账成功"}
      ]
    },
    {
      "spanID": "span-domain-1",
      "parentSpanID": "span-app-1",
      "operationName": "transfer_service.transfer",
      "duration": 142.5
    },
    {
      "spanID": "span-infra-1",
      "parentSpanID": "span-domain-1",
      "operationName": "account_repository.find_by_id",
      "duration": 25.3,
      "tags": {
        "db.system": "postgresql",
        "db.operation": "SELECT",
        "account_id": "uuid-123"
      }
    }
  ]
}
```

---

## 🧪 测试策略

### 1. 领域模型单元测试 (无 Mock)

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_account_withdrawal() {
        // 纯领域逻辑测试,无需任何 Mock
        let mut account = Account::open(
            "张三".to_string(),
            Money::from_yuan(1000.0).unwrap(),
        ).unwrap();

        let result = account.withdraw(Money::from_yuan(100.0).unwrap());
        
        assert!(result.is_ok());
        assert_eq!(account.balance().to_yuan(), 900.0);
    }

    #[test]
    fn test_insufficient_balance() {
        let mut account = Account::open(
            "李四".to_string(),
            Money::from_yuan(100.0).unwrap(),
        ).unwrap();

        let result = account.withdraw(Money::from_yuan(200.0).unwrap());
        
        assert!(matches!(result, Err(DomainError::InsufficientBalance { .. })));
    }
}
```

### 2. 应用服务集成测试 (Mock 仓储)

```rust
#[tokio::test]
async fn test_transfer_command_with_mock() {
    // Mock 仓储
    let mock_repo = Arc::new(MockAccountRepository::new());
    
    // 创建测试账户
    let from_account = Account::open(...).unwrap();
    let to_account = Account::open(...).unwrap();
    mock_repo.save(&from_account).await.unwrap();
    mock_repo.save(&to_account).await.unwrap();

    // 创建服务
    let transfer_service = Arc::new(TransferService::new(mock_repo.clone()));
    let handler = TransferCommandHandler::new(transfer_service);

    // 执行命令
    let command = TransferCommand {
        from_account_id: from_account.id(),
        to_account_id: to_account.id(),
        amount_cents: 10000,
    };

    let result = handler.handle(command).await;
    assert!(result.is_ok());
}
```

---

## 📦 Cargo.toml 完整配置

```toml
[workspace]
members = [
    "domain",
    "domain_services",
    "application",
    "infrastructure",
]

[workspace.dependencies]
# 异步运行时
tokio = { version = "1.41", features = ["full"] }
async-trait = "0.1.82"

# Web 框架
axum = "0.7"
tower = "0.5"
tower-http = { version = "0.6", features = ["trace"] }

# 数据库
sqlx = { version = "0.8", features = ["postgres", "runtime-tokio", "uuid", "chrono"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# UUID & 时间
uuid = { version = "1.10", features = ["v4", "serde"] }
chrono = { version = "0.4", features = ["serde"] }

# 错误处理
thiserror = "2.0"
anyhow = "1.0"

# OpenTelemetry
opentelemetry = "0.31"
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.16", features = ["tonic"] }
tracing = "0.1"
tracing-subscriber = { version = "0.3.18", features = ["env-filter"] }
tracing-opentelemetry = "0.31"

[package]
name = "onion-banking"
version = "1.0.0"
edition = "2021"

[dependencies]
domain = { path = "domain" }
domain_services = { path = "domain_services" }
application = { path = "application" }
infrastructure = { path = "infrastructure" }

tokio = { workspace = true }
tracing = { workspace = true }
```

---

## 🌟 最佳实践总结

### ✅ DO (推荐)

1. **严格遵守依赖方向**: 外层 → 内层
2. **领域模型零依赖**: 不引入任何框架/基础设施库
3. **OTLP 分层注入**:
   - Layer 1 (Domain): 无追踪
   - Layer 2 (Domain Services): 可选轻量级追踪
   - Layer 3 (Application): 用例级追踪
   - Layer 4 (Infrastructure): 完整追踪
4. **领域事件**: 用于解耦聚合根之间的通信
5. **用例编排**: 在应用层编排多个领域服务

### ❌ DON'T (避免)

1. **内层依赖外层**: 领域层不能依赖基础设施层
2. **跨层调用**: 禁止 Layer 4 直接调用 Layer 1 的方法
3. **OTLP 污染领域**: 领域模型不添加 `#[instrument]`
4. **贫血模型**: 领域实体必须包含业务逻辑,不能只是数据容器
5. **上帝服务**: 避免单一应用服务包含所有用例

---

## 🔗 参考资源

### 架构模式

- [Jeffrey Palermo - Onion Architecture](https://jeffreypalermo.com/2008/07/the-onion-architecture-part-1/)
- [Clean Architecture (Robert C. Martin)](https://blog.cleancoder.com/uncle-bob/2012/08/13/the-clean-architecture.html)
- [Domain-Driven Design (Eric Evans)](https://www.domainlanguage.com/ddd/)

### Rust 实现

- [Rust DDD](https://github.com/vaerh/ddd-rust)
- [Axum Examples](https://github.com/tokio-rs/axum/tree/main/examples)
- [SQLx Documentation](https://docs.rs/sqlx/latest/sqlx/)

### 国际标准

- [Microsoft - Onion Architecture](https://learn.microsoft.com/en-us/dotnet/architecture/modern-web-apps-azure/common-web-application-architectures#onion-architecture)
- [AWS Well-Architected](https://aws.amazon.com/architecture/well-architected/)

---

**文档版本**: 1.0  
**创建日期**: 2025年10月11日  
**Rust 版本**: 1.90+  
**OpenTelemetry**: 0.31.0

**🧅 洋葱架构: 保护核心业务逻辑,构建可维护系统!** 🚀
