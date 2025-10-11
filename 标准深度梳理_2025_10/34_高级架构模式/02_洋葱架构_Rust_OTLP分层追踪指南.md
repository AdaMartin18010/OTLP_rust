# 洋葱架构 (Onion Architecture) - Rust OTLP 分层追踪指南

> **架构模式**: Onion Architecture  
> **提出者**: Jeffrey Palermo (2008)  
> **国际标准**: 企业应用架构标准，微软推荐模式  
> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **更新日期**: 2025年10月11日

---

## 📋 目录

- [洋葱架构 (Onion Architecture) - Rust OTLP 分层追踪指南](#洋葱架构-onion-architecture---rust-otlp-分层追踪指南)
  - [📋 目录](#-目录)
  - [🏛️ 架构概述](#️-架构概述)
    - [什么是洋葱架构?](#什么是洋葱架构)
      - [核心思想](#核心思想)
      - [洋葱的"层"](#洋葱的层)
    - [国际标准对标](#国际标准对标)
  - [🎯 核心概念](#-核心概念)
    - [1. 依赖倒置原则 (DIP)](#1-依赖倒置原则-dip)
    - [2. 关注点分离 (Separation of Concerns)](#2-关注点分离-separation-of-concerns)
    - [3. 内层稳定性](#3-内层稳定性)
  - [🔄 与六边形架构对比](#-与六边形架构对比)
    - [相同点](#相同点)
    - [不同点](#不同点)
    - [架构图对比](#架构图对比)
      - [洋葱架构](#洋葱架构)
      - [六边形架构](#六边形架构)
  - [🦀 Rust 实现设计](#-rust-实现设计)
    - [项目结构](#项目结构)
  - [🔭 OTLP 分层集成](#-otlp-分层集成)
    - [策略: 从外到内的追踪传播](#策略-从外到内的追踪传播)
  - [🏦 完整银行示例](#-完整银行示例)
    - [Layer 1: Domain Model (核心层)](#layer-1-domain-model-核心层)
      - [1.1 实体 (Entity)](#11-实体-entity)
      - [1.2 值对象 (Value Objects)](#12-值对象-value-objects)
      - [1.3 仓储接口 (Repository Port)](#13-仓储接口-repository-port)
    - [Layer 2: Domain Services (领域服务层)](#layer-2-domain-services-领域服务层)
    - [Layer 3: Application Services (应用服务层)](#layer-3-application-services-应用服务层)
    - [Layer 4: Infrastructure (基础设施层)](#layer-4-infrastructure-基础设施层)
      - [4.1 Web Handler (HTTP)](#41-web-handler-http)
      - [4.2 数据库适配器 (PostgreSQL)](#42-数据库适配器-postgresql)
  - [🧪 测试策略](#-测试策略)
    - [1. 单元测试 (Domain Model - 零依赖)](#1-单元测试-domain-model---零依赖)
    - [2. 集成测试 (Application + Infrastructure)](#2-集成测试-application--infrastructure)
  - [⚡ 性能优化](#-性能优化)
    - [1. 事务管理](#1-事务管理)
  - [🚀 生产部署](#-生产部署)
    - [Cargo.toml](#cargotoml)
    - [Docker Compose](#docker-compose)
  - [✅ 最佳实践清单](#-最佳实践清单)
    - [洋葱架构设计](#洋葱架构设计)
    - [OTLP 集成](#otlp-集成)
    - [Rust 特性](#rust-特性)
  - [📚 参考资源](#-参考资源)
    - [国际标准](#国际标准)
    - [Rust 生态](#rust-生态)
  - [🎉 总结](#-总结)

---

## 🏛️ 架构概述

### 什么是洋葱架构?

**洋葱架构** (Onion Architecture) 是一种分层架构模式，由 Jeffrey Palermo 于 2008 年提出，强调**依赖倒置**和**关注点分离**。

#### 核心思想

```text
                    ┌─────────────────────┐
                    │   Infrastructure    │  外层
                    │  (数据库/Web/外部)   │
                    └──────────┬──────────┘
                               │
                    ┌──────────▼──────────┐
                    │  Application Core   │  应用层
                    │   (用例/服务)        │
                    └──────────┬──────────┘
                               │
                    ┌──────────▼──────────┐
                    │   Domain Services   │  领域服务层
                    │   (业务规则)         │
                    └──────────┬──────────┘
                               │
                    ┌──────────▼──────────┐
                    │   Domain Model      │  核心层
                    │  (实体/值对象)       │  (最内层)
                    └─────────────────────┘

依赖方向: 外层 → 内层 (单向依赖)
```

#### 洋葱的"层"

像剥洋葱一样，从外到内：

1. **基础设施层 (Infrastructure Layer)** - 最外层
   - 数据库访问
   - Web API 控制器
   - 外部服务调用
   - 消息队列
   - 文件系统

2. **应用服务层 (Application Services Layer)**
   - 用例编排
   - 业务工作流
   - DTO 转换
   - **OTLP 集成点** ⭐

3. **领域服务层 (Domain Services Layer)**
   - 跨实体的业务逻辑
   - 领域事件
   - 规则引擎

4. **领域模型层 (Domain Model Layer)** - 最内层（核心）
   - 实体 (Entities)
   - 值对象 (Value Objects)
   - 聚合根 (Aggregate Roots)
   - 仓储接口 (Repository Interfaces)
   - **完全无外部依赖**

---

### 国际标准对标

| 标准/框架 | 提出者 | 年份 | 洋葱架构对标 |
|----------|-------|------|-------------|
| **Onion Architecture** | Jeffrey Palermo | 2008 | ✅ 本架构 |
| **Clean Architecture** | Robert C. Martin | 2012 | ✅ 依赖规则一致 |
| **DDD (Domain-Driven Design)** | Eric Evans | 2003 | ✅ 领域建模核心 |
| **Hexagonal Architecture** | Alistair Cockburn | 2005 | ✅ 端口适配器思想 |
| **Dependency Inversion Principle** | Robert C. Martin | - | ✅ 核心原则 |
| **Microsoft Architecture Guide** | Microsoft | 2009 | ✅ 企业应用推荐 |

---

## 🎯 核心概念

### 1. 依赖倒置原则 (DIP)

**核心规则**: 所有依赖指向内层，内层不依赖外层。

```rust
// ❌ 错误: 内层依赖外层
// domain/account.rs
use infrastructure::database::PostgresConnection;  // ❌ 不能依赖基础设施层

pub struct Account {
    db: PostgresConnection,  // ❌ 违反依赖倒置
}

// ✅ 正确: 内层定义接口，外层实现
// domain/repositories/account_repository.rs
#[async_trait]
pub trait AccountRepositoryPort: Send + Sync {
    async fn save(&self, account: &Account) -> Result<()>;
    async fn find_by_id(&self, id: AccountId) -> Result<Option<Account>>;
}

// infrastructure/persistence/postgres_account_repository.rs
pub struct PostgresAccountRepository {
    pool: PgPool,
}

#[async_trait]
impl AccountRepositoryPort for PostgresAccountRepository {
    async fn save(&self, account: &Account) -> Result<()> {
        // 实现细节
    }
}
```

---

### 2. 关注点分离 (Separation of Concerns)

每一层只关注自己的职责：

| 层级 | 职责 | 不关心 |
|------|------|--------|
| **Domain Model** | 业务规则、实体状态 | 如何持久化、如何展示 |
| **Domain Services** | 跨实体业务逻辑 | 数据库、API |
| **Application Services** | 用例编排、工作流 | 具体实现技术 |
| **Infrastructure** | 技术实现细节 | 业务规则 |

---

### 3. 内层稳定性

```text
变化频率:

Infrastructure  →  经常变化 (数据库换 Redis, Web 框架换 Actix)
Application     →  偶尔变化 (业务流程调整)
Domain Services →  很少变化 (业务规则相对稳定)
Domain Model    →  最稳定 (核心业务概念)
```

---

## 🔄 与六边形架构对比

### 相同点

| 特性 | 洋葱架构 | 六边形架构 |
|------|---------|-----------|
| **依赖方向** | ✅ 外层→内层 | ✅ 外层→内层 |
| **核心保护** | ✅ 领域模型不依赖外部 | ✅ 领域模型不依赖外部 |
| **接口定义** | ✅ 内层定义接口 | ✅ 内层定义端口 |
| **可测试性** | ✅ 高 (可 Mock 外层) | ✅ 高 (可 Mock 适配器) |

### 不同点

| 维度 | 洋葱架构 | 六边形架构 |
|------|---------|-----------|
| **结构隐喻** | 🧅 同心圆层次 | ⬡ 六边形端口 |
| **层次数量** | 通常 4 层 | 通常 3 层 |
| **强调点** | 强调**分层** | 强调**端口与适配器** |
| **领域服务层** | ✅ 明确分离 | ❌ 通常包含在领域层 |
| **应用服务** | ✅ 独立一层 | ✅ 独立一层 (用例) |

### 架构图对比

#### 洋葱架构

```text
┌─────────────────────────────────────────┐
│      Infrastructure Layer (外层)        │
│  ┌───────────────────────────────────┐  │
│  │   Application Services Layer     │  │
│  │  ┌─────────────────────────────┐ │  │
│  │  │  Domain Services Layer      │ │  │
│  │  │  ┌───────────────────────┐  │ │  │
│  │  │  │   Domain Model Layer  │  │ │  │
│  │  │  │   (核心/最稳定)       │  │ │  │
│  │  │  └───────────────────────┘  │ │  │
│  │  └─────────────────────────────┘ │  │
│  └───────────────────────────────────┘  │
└─────────────────────────────────────────┘

依赖: 外→内 (单向)
```

#### 六边形架构

```text
        入站适配器
         ↓
    ┌────────────┐
    │   Ports    │
    ├────────────┤
    │  Domain    │
    │   Core     │
    ├────────────┤
    │   Ports    │
    └────────────┘
         ↑
        出站适配器

依赖: 适配器→端口→核心
```

---

## 🦀 Rust 实现设计

### 项目结构

```text
banking-service/
├── Cargo.toml
├── src/
│   ├── main.rs
│   │
│   ├── domain/                           # 🟢 Layer 1: Domain Model (最内层)
│   │   ├── mod.rs
│   │   ├── model/
│   │   │   ├── mod.rs
│   │   │   ├── account.rs                # 账户实体
│   │   │   ├── transaction.rs            # 交易实体
│   │   │   └── customer.rs               # 客户实体
│   │   ├── value_objects/
│   │   │   ├── mod.rs
│   │   │   ├── account_id.rs
│   │   │   ├── money.rs
│   │   │   ├── account_number.rs
│   │   │   └── transaction_type.rs
│   │   └── repositories/                 # 仓储接口 (Trait)
│   │       ├── mod.rs
│   │       ├── account_repository.rs
│   │       └── transaction_repository.rs
│   │
│   ├── domain_services/                  # 🟡 Layer 2: Domain Services
│   │   ├── mod.rs
│   │   ├── transfer_service.rs           # 转账服务 (跨账户业务逻辑)
│   │   ├── interest_calculator.rs        # 利息计算服务
│   │   └── validation_service.rs         # 业务规则验证
│   │
│   ├── application/                      # 🟠 Layer 3: Application Services
│   │   ├── mod.rs
│   │   ├── use_cases/
│   │   │   ├── mod.rs
│   │   │   ├── create_account.rs         # 开户用例
│   │   │   ├── deposit_money.rs          # 存款用例
│   │   │   ├── withdraw_money.rs         # 取款用例
│   │   │   └── transfer_money.rs         # 转账用例 (OTLP 集成点)
│   │   └── dto/
│   │       ├── mod.rs
│   │       ├── account_dto.rs
│   │       └── transaction_dto.rs
│   │
│   └── infrastructure/                   # 🔴 Layer 4: Infrastructure (最外层)
│       ├── mod.rs
│       ├── web/
│       │   ├── mod.rs
│       │   ├── server.rs
│       │   ├── handlers/
│       │   │   └── account_handler.rs
│       │   └── middleware/
│       │       └── telemetry.rs          # OTLP 中间件
│       ├── persistence/
│       │   ├── mod.rs
│       │   ├── postgres_account_repo.rs  # 实现 AccountRepositoryPort
│       │   └── postgres_transaction_repo.rs
│       ├── notifications/
│       │   ├── mod.rs
│       │   └── email_notifier.rs
│       └── telemetry/
│           ├── mod.rs
│           └── init.rs                   # OTLP 初始化
│
└── tests/
    ├── integration/
    └── unit/
```

---

## 🔭 OTLP 分层集成

### 策略: 从外到内的追踪传播

```text
┌─────────────────────────────────────────┐
│  Infrastructure Layer                   │
│  ✅ 完整 OTLP 插桩                      │
│  - HTTP Handler (#[instrument])         │
│  - DB Repository (#[instrument])        │
│  - External APIs (#[instrument])        │
└────────────────┬────────────────────────┘
                 │ 追踪上下文传播
                 ▼
┌─────────────────────────────────────────┐
│  Application Services Layer             │
│  ✅ OTLP 集成点                         │
│  - Use Cases (#[instrument])            │
│  - 用例级别追踪                         │
└────────────────┬────────────────────────┘
                 │ 通过返回值传递领域事件
                 ▼
┌─────────────────────────────────────────┐
│  Domain Services Layer                  │
│  ⚠️ 最小化 OTLP                        │
│  - 可选择性添加 (#[instrument])         │
│  - 复杂业务逻辑追踪                     │
└────────────────┬────────────────────────┘
                 │ 纯函数调用
                 ▼
┌─────────────────────────────────────────┐
│  Domain Model Layer                     │
│  ❌ 零 OTLP 依赖                        │
│  - 纯业务逻辑                           │
│  - 通过领域事件记录状态变化             │
└─────────────────────────────────────────┘
```

---

## 🏦 完整银行示例

### Layer 1: Domain Model (核心层)

#### 1.1 实体 (Entity)

```rust
// domain/model/account.rs
use crate::domain::value_objects::{AccountId, AccountNumber, Money, AccountType};
use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};

/// 银行账户实体
/// 
/// 核心领域层: 无任何外部依赖 (包括 OTLP)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Account {
    id: AccountId,
    account_number: AccountNumber,
    customer_id: CustomerId,
    account_type: AccountType,
    balance: Money,
    status: AccountStatus,
    opened_at: DateTime<Utc>,
    updated_at: DateTime<Utc>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum AccountStatus {
    Active,
    Frozen,
    Closed,
}

impl Account {
    /// 创建新账户 (纯业务逻辑)
    pub fn open(
        customer_id: CustomerId,
        account_type: AccountType,
        initial_deposit: Money,
    ) -> Result<(Self, AccountEvent), DomainError> {
        // 业务规则验证
        if initial_deposit.amount() < account_type.minimum_deposit() {
            return Err(DomainError::InsufficientInitialDeposit {
                required: account_type.minimum_deposit(),
                provided: initial_deposit.amount(),
            });
        }
        
        let now = Utc::now();
        let account = Self {
            id: AccountId::new(),
            account_number: AccountNumber::generate(),
            customer_id,
            account_type,
            balance: initial_deposit,
            status: AccountStatus::Active,
            opened_at: now,
            updated_at: now,
        };
        
        // 领域事件 (代替直接日志)
        let event = AccountEvent::AccountOpened {
            account_id: account.id,
            customer_id: account.customer_id,
            account_number: account.account_number,
            initial_balance: account.balance,
            opened_at: account.opened_at,
        };
        
        Ok((account, event))
    }
    
    /// 存款
    pub fn deposit(&mut self, amount: Money) -> Result<AccountEvent, DomainError> {
        // 业务规则
        if self.status != AccountStatus::Active {
            return Err(DomainError::AccountNotActive(self.status));
        }
        
        if amount.amount() <= 0.0 {
            return Err(DomainError::InvalidAmount(amount.amount()));
        }
        
        // 单笔存款限额
        if amount.amount() > 50000.0 {
            return Err(DomainError::ExceedsDepositLimit(amount.amount()));
        }
        
        // 更新余额
        self.balance = self.balance.add(&amount);
        self.updated_at = Utc::now();
        
        Ok(AccountEvent::MoneyDeposited {
            account_id: self.id,
            amount,
            new_balance: self.balance,
            deposited_at: self.updated_at,
        })
    }
    
    /// 取款
    pub fn withdraw(&mut self, amount: Money) -> Result<AccountEvent, DomainError> {
        // 业务规则
        if self.status != AccountStatus::Active {
            return Err(DomainError::AccountNotActive(self.status));
        }
        
        if amount.amount() <= 0.0 {
            return Err(DomainError::InvalidAmount(amount.amount()));
        }
        
        // 余额检查
        if self.balance.amount() < amount.amount() {
            return Err(DomainError::InsufficientBalance {
                available: self.balance.amount(),
                requested: amount.amount(),
            });
        }
        
        // 每日取款限额 (由领域服务检查)
        
        // 更新余额
        self.balance = self.balance.subtract(&amount)?;
        self.updated_at = Utc::now();
        
        Ok(AccountEvent::MoneyWithdrawn {
            account_id: self.id,
            amount,
            new_balance: self.balance,
            withdrawn_at: self.updated_at,
        })
    }
    
    /// 冻结账户
    pub fn freeze(&mut self, reason: String) -> Result<AccountEvent, DomainError> {
        if self.status == AccountStatus::Closed {
            return Err(DomainError::CannotFreezeClosedAccount);
        }
        
        self.status = AccountStatus::Frozen;
        self.updated_at = Utc::now();
        
        Ok(AccountEvent::AccountFrozen {
            account_id: self.id,
            reason,
            frozen_at: self.updated_at,
        })
    }
    
    // Getters
    pub fn id(&self) -> AccountId { self.id }
    pub fn account_number(&self) -> &AccountNumber { &self.account_number }
    pub fn balance(&self) -> &Money { &self.balance }
    pub fn status(&self) -> AccountStatus { self.status }
}

/// 领域事件 (记录状态变化,无 OTLP 依赖)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AccountEvent {
    AccountOpened {
        account_id: AccountId,
        customer_id: CustomerId,
        account_number: AccountNumber,
        initial_balance: Money,
        opened_at: DateTime<Utc>,
    },
    MoneyDeposited {
        account_id: AccountId,
        amount: Money,
        new_balance: Money,
        deposited_at: DateTime<Utc>,
    },
    MoneyWithdrawn {
        account_id: AccountId,
        amount: Money,
        new_balance: Money,
        withdrawn_at: DateTime<Utc>,
    },
    AccountFrozen {
        account_id: AccountId,
        reason: String,
        frozen_at: DateTime<Utc>,
    },
}

#[derive(Debug, thiserror::Error)]
pub enum DomainError {
    #[error("Insufficient initial deposit: required ${required}, provided ${provided}")]
    InsufficientInitialDeposit { required: f64, provided: f64 },
    
    #[error("Account is not active: {0:?}")]
    AccountNotActive(AccountStatus),
    
    #[error("Invalid amount: ${0}")]
    InvalidAmount(f64),
    
    #[error("Insufficient balance: available ${available}, requested ${requested}")]
    InsufficientBalance { available: f64, requested: f64 },
    
    #[error("Exceeds deposit limit: ${0}")]
    ExceedsDepositLimit(f64),
    
    #[error("Cannot freeze closed account")]
    CannotFreezeClosedAccount,
}
```

#### 1.2 值对象 (Value Objects)

```rust
// domain/value_objects/money.rs
use serde::{Deserialize, Serialize};
use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct Money {
    amount: f64,
    currency: Currency,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Currency {
    USD,
    EUR,
    CNY,
}

impl Money {
    pub fn new(amount: f64, currency: Currency) -> Result<Self, DomainError> {
        if amount < 0.0 {
            return Err(DomainError::NegativeAmount);
        }
        Ok(Self { amount, currency })
    }
    
    pub fn zero(currency: Currency) -> Self {
        Self { amount: 0.0, currency }
    }
    
    pub fn amount(&self) -> f64 { self.amount }
    pub fn currency(&self) -> Currency { self.currency }
    
    pub fn add(&self, other: &Self) -> Self {
        assert_eq!(self.currency, other.currency);
        Self {
            amount: self.amount + other.amount,
            currency: self.currency,
        }
    }
    
    pub fn subtract(&self, other: &Self) -> Result<Self, DomainError> {
        assert_eq!(self.currency, other.currency);
        if self.amount < other.amount {
            return Err(DomainError::InsufficientBalance {
                available: self.amount,
                requested: other.amount,
            });
        }
        Ok(Self {
            amount: self.amount - other.amount,
            currency: self.currency,
        })
    }
}

impl fmt::Display for Money {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.currency {
            Currency::USD => write!(f, "${:.2}", self.amount),
            Currency::EUR => write!(f, "€{:.2}", self.amount),
            Currency::CNY => write!(f, "¥{:.2}", self.amount),
        }
    }
}

// domain/value_objects/account_number.rs
use rand::Rng;
use serde::{Deserialize, Serialize};
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct AccountNumber(String);

impl AccountNumber {
    /// 生成账户号 (格式: 6222-0000-1234-5678)
    pub fn generate() -> Self {
        let mut rng = rand::thread_rng();
        let parts: Vec<String> = (0..4)
            .map(|i| {
                if i == 0 {
                    format!("{:04}", 6222)  // 固定银行代码
                } else {
                    format!("{:04}", rng.gen_range(0..10000))
                }
            })
            .collect();
        
        Self(parts.join("-"))
    }
    
    pub fn from_string(s: String) -> Result<Self, DomainError> {
        if !Self::is_valid(&s) {
            return Err(DomainError::InvalidAccountNumber);
        }
        Ok(Self(s))
    }
    
    fn is_valid(s: &str) -> bool {
        s.len() == 19 && s.chars().filter(|c| c == &'-').count() == 3
    }
    
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for AccountNumber {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
```

#### 1.3 仓储接口 (Repository Port)

```rust
// domain/repositories/account_repository.rs
use crate::domain::model::Account;
use crate::domain::value_objects::{AccountId, AccountNumber};
use async_trait::async_trait;

/// 账户仓储接口 (领域层定义,基础设施层实现)
#[async_trait]
pub trait AccountRepositoryPort: Send + Sync {
    async fn save(&self, account: &Account) -> Result<(), RepositoryError>;
    async fn find_by_id(&self, id: AccountId) -> Result<Option<Account>, RepositoryError>;
    async fn find_by_number(&self, number: &AccountNumber) -> Result<Option<Account>, RepositoryError>;
    async fn find_by_customer_id(&self, customer_id: CustomerId) -> Result<Vec<Account>, RepositoryError>;
    async fn delete(&self, id: AccountId) -> Result<(), RepositoryError>;
}

#[derive(Debug, thiserror::Error)]
pub enum RepositoryError {
    #[error("Database error: {0}")]
    DatabaseError(String),
    
    #[error("Account not found: {0}")]
    NotFound(AccountId),
    
    #[error("Serialization error: {0}")]
    SerializationError(String),
}
```

---

### Layer 2: Domain Services (领域服务层)

```rust
// domain_services/transfer_service.rs
use crate::domain::model::Account;
use crate::domain::value_objects::Money;
use tracing::{instrument, info, warn};

/// 转账领域服务
/// 
/// 处理跨账户的业务逻辑
/// 注意: 这一层可以选择性添加 OTLP
pub struct TransferService;

impl TransferService {
    /// 转账 (跨两个账户的操作)
    /// 
    /// 可选择性添加 #[instrument],但要最小化
    #[instrument(
        name = "domain_service_transfer",
        skip(from_account, to_account),
        fields(
            from_account_id = %from_account.id(),
            to_account_id = %to_account.id(),
            amount = %amount,
        )
    )]
    pub fn transfer(
        from_account: &mut Account,
        to_account: &mut Account,
        amount: Money,
    ) -> Result<Vec<AccountEvent>, DomainError> {
        info!("🔄 Executing transfer in domain service");
        
        // 业务规则: 不能自己转给自己
        if from_account.id() == to_account.id() {
            warn!("❌ Attempted self-transfer");
            return Err(DomainError::SelfTransferNotAllowed);
        }
        
        // 业务规则: 币种必须一致
        if from_account.balance().currency() != to_account.balance().currency() {
            warn!("❌ Currency mismatch");
            return Err(DomainError::CurrencyMismatch);
        }
        
        // 业务规则: 转账金额限制
        if amount.amount() > 100000.0 {
            warn!(amount = %amount, "❌ Exceeds transfer limit");
            return Err(DomainError::ExceedsTransferLimit(amount.amount()));
        }
        
        // 执行转账 (调用实体方法)
        let withdraw_event = from_account.withdraw(amount)?;
        let deposit_event = to_account.deposit(amount)?;
        
        info!("✅ Transfer completed in domain service");
        
        Ok(vec![withdraw_event, deposit_event])
    }
    
    /// 验证转账是否在每日限额内
    pub fn validate_daily_limit(
        account: &Account,
        amount: Money,
        today_total_withdrawn: Money,
    ) -> Result<(), DomainError> {
        let daily_limit = account.account_type().daily_withdraw_limit();
        let new_total = today_total_withdrawn.amount() + amount.amount();
        
        if new_total > daily_limit {
            return Err(DomainError::ExceedsDailyLimit {
                limit: daily_limit,
                current: today_total_withdrawn.amount(),
                requested: amount.amount(),
            });
        }
        
        Ok(())
    }
}
```

---

### Layer 3: Application Services (应用服务层)

```rust
// application/use_cases/transfer_money.rs
use crate::application::dto::{TransferRequestDto, TransferResponseDto};
use crate::domain::repositories::AccountRepositoryPort;
use crate::domain_services::TransferService;
use std::sync::Arc;
use tracing::{instrument, info, error, warn};

/// 转账用例
/// 
/// 应用服务层: OTLP 集成点
pub struct TransferMoneyUseCase<R: AccountRepositoryPort> {
    account_repo: Arc<R>,
    transfer_service: Arc<TransferService>,
}

impl<R: AccountRepositoryPort> TransferMoneyUseCase<R> {
    pub fn new(account_repo: Arc<R>, transfer_service: Arc<TransferService>) -> Self {
        Self {
            account_repo,
            transfer_service,
        }
    }
    
    /// 执行转账用例
    /// 
    /// OTLP 集成: 在这一层添加完整的分布式追踪
    #[instrument(
        name = "transfer_money_use_case",
        skip(self, request),
        fields(
            use_case = "transfer_money",
            from_account_number = %request.from_account_number,
            to_account_number = %request.to_account_number,
            amount = %request.amount,
            otel.kind = "internal",
        )
    )]
    pub async fn execute(
        &self,
        request: TransferRequestDto,
    ) -> Result<TransferResponseDto, AppError> {
        info!("💸 Executing transfer money use case");
        
        // Step 1: 查找源账户
        let mut from_account = self.account_repo
            .find_by_number(&request.from_account_number)
            .await
            .map_err(|e| {
                error!(error = ?e, "❌ Failed to find source account");
                AppError::RepositoryError(e)
            })?
            .ok_or_else(|| {
                warn!("⚠️ Source account not found");
                AppError::AccountNotFound(request.from_account_number.clone())
            })?;
        
        info!(
            from_account_id = %from_account.id(),
            balance = %from_account.balance(),
            "✅ Source account found"
        );
        
        // Step 2: 查找目标账户
        let mut to_account = self.account_repo
            .find_by_number(&request.to_account_number)
            .await
            .map_err(|e| {
                error!(error = ?e, "❌ Failed to find target account");
                AppError::RepositoryError(e)
            })?
            .ok_or_else(|| {
                warn!("⚠️ Target account not found");
                AppError::AccountNotFound(request.to_account_number.clone())
            })?;
        
        info!(
            to_account_id = %to_account.id(),
            balance = %to_account.balance(),
            "✅ Target account found"
        );
        
        // Step 3: 执行转账 (调用领域服务)
        let events = self.transfer_service
            .transfer(&mut from_account, &mut to_account, request.amount)
            .map_err(|e| {
                error!(error = ?e, "❌ Transfer failed in domain service");
                AppError::DomainError(e)
            })?;
        
        info!(event_count = events.len(), "✅ Transfer completed in domain");
        
        // Step 4: 持久化账户状态
        self.account_repo.save(&from_account).await.map_err(|e| {
            error!(error = ?e, "❌ Failed to save source account");
            AppError::RepositoryError(e)
        })?;
        
        self.account_repo.save(&to_account).await.map_err(|e| {
            error!(error = ?e, "❌ Failed to save target account");
            // TODO: 补偿逻辑 - 回滚源账户
            AppError::RepositoryError(e)
        })?;
        
        info!("💾 Accounts saved to database");
        
        // Step 5: 发布领域事件 (可选)
        for event in events {
            info!(event = ?event, "📤 Domain event published");
            // TODO: 发送到消息队列
        }
        
        info!(
            from_balance = %from_account.balance(),
            to_balance = %to_account.balance(),
            "🎉 Transfer completed successfully"
        );
        
        Ok(TransferResponseDto {
            transaction_id: TransactionId::new(),
            from_account_id: from_account.id(),
            to_account_id: to_account.id(),
            amount: request.amount,
            new_from_balance: *from_account.balance(),
            new_to_balance: *to_account.balance(),
            completed_at: Utc::now(),
        })
    }
}
```

---

### Layer 4: Infrastructure (基础设施层)

#### 4.1 Web Handler (HTTP)

```rust
// infrastructure/web/handlers/account_handler.rs
use axum::{
    extract::{Path, State},
    http::StatusCode,
    response::{IntoResponse, Response},
    Json,
};
use crate::application::use_cases::TransferMoneyUseCase;
use crate::application::dto::TransferRequestDto;
use serde_json::json;
use tracing::{instrument, info, error};
use std::sync::Arc;

pub struct AccountHandler<R: AccountRepositoryPort> {
    transfer_use_case: Arc<TransferMoneyUseCase<R>>,
}

impl<R: AccountRepositoryPort> AccountHandler<R> {
    pub fn new(transfer_use_case: Arc<TransferMoneyUseCase<R>>) -> Self {
        Self { transfer_use_case }
    }
    
    /// POST /api/accounts/transfer - 转账
    #[instrument(
        name = "http_post_transfer",
        skip(self, payload),
        fields(
            http.method = "POST",
            http.route = "/api/accounts/transfer",
            http.status_code = tracing::field::Empty,
            otel.kind = "server",
        )
    )]
    pub async fn transfer(
        State(handler): State<Arc<Self>>,
        Json(payload): Json<TransferRequestDto>,
    ) -> Response {
        info!("📨 Received transfer request");
        
        match handler.transfer_use_case.execute(payload).await {
            Ok(response) => {
                info!(
                    transaction_id = %response.transaction_id,
                    "✅ Transfer successful"
                );
                tracing::Span::current().record("http.status_code", 200);
                (StatusCode::OK, Json(response)).into_response()
            }
            Err(e) => {
                error!(error = ?e, "❌ Transfer failed");
                
                let (status, message) = match e {
                    AppError::AccountNotFound(_) => (StatusCode::NOT_FOUND, e.to_string()),
                    AppError::DomainError(_) => (StatusCode::BAD_REQUEST, e.to_string()),
                    _ => (StatusCode::INTERNAL_SERVER_ERROR, "Internal error".to_string()),
                };
                
                tracing::Span::current().record("http.status_code", status.as_u16());
                
                (
                    status,
                    Json(json!({
                        "error": "Transfer failed",
                        "message": message
                    }))
                ).into_response()
            }
        }
    }
}
```

#### 4.2 数据库适配器 (PostgreSQL)

```rust
// infrastructure/persistence/postgres_account_repository.rs
use crate::domain::model::Account;
use crate::domain::repositories::{AccountRepositoryPort, RepositoryError};
use crate::domain::value_objects::{AccountId, AccountNumber};
use sqlx::{PgPool, Row};
use async_trait::async_trait;
use tracing::{instrument, info, error};

pub struct PostgresAccountRepository {
    pool: PgPool,
}

impl PostgresAccountRepository {
    pub fn new(pool: PgPool) -> Self {
        Self { pool }
    }
}

#[async_trait]
impl AccountRepositoryPort for PostgresAccountRepository {
    #[instrument(
        name = "postgres_save_account",
        skip(self, account),
        fields(
            db.system = "postgresql",
            db.operation = "UPSERT",
            db.table = "accounts",
            account_id = %account.id(),
            otel.kind = "client",
        )
    )]
    async fn save(&self, account: &Account) -> Result<(), RepositoryError> {
        info!("💾 Saving account to PostgreSQL");
        
        sqlx::query!(
            r#"
            INSERT INTO accounts (id, account_number, customer_id, account_type, balance, currency, status, opened_at, updated_at)
            VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9)
            ON CONFLICT (id)
            DO UPDATE SET
                balance = EXCLUDED.balance,
                status = EXCLUDED.status,
                updated_at = EXCLUDED.updated_at
            "#,
            account.id().as_uuid(),
            account.account_number().as_str(),
            account.customer_id().as_uuid(),
            account.account_type().to_string(),
            account.balance().amount(),
            account.balance().currency().to_string(),
            account.status().to_string(),
            account.opened_at(),
            account.updated_at(),
        )
        .execute(&self.pool)
        .await
        .map_err(|e| {
            error!(error = ?e, "❌ Database insert failed");
            RepositoryError::DatabaseError(e.to_string())
        })?;
        
        info!(account_id = %account.id(), "✅ Account saved successfully");
        Ok(())
    }
    
    #[instrument(
        name = "postgres_find_account_by_number",
        skip(self),
        fields(
            db.system = "postgresql",
            db.operation = "SELECT",
            db.table = "accounts",
            account_number = %number,
            otel.kind = "client",
        )
    )]
    async fn find_by_number(
        &self,
        number: &AccountNumber,
    ) -> Result<Option<Account>, RepositoryError> {
        info!(account_number = %number, "🔍 Querying account by number");
        
        let row = sqlx::query!(
            r#"
            SELECT id, account_number, customer_id, account_type, balance, currency, status, opened_at, updated_at
            FROM accounts
            WHERE account_number = $1
            "#,
            number.as_str(),
        )
        .fetch_optional(&self.pool)
        .await
        .map_err(|e| {
            error!(error = ?e, "❌ Database query failed");
            RepositoryError::DatabaseError(e.to_string())
        })?;
        
        match row {
            Some(r) => {
                info!("✅ Account found");
                Ok(Some(Account::reconstruct(
                    AccountId::from_uuid(r.id),
                    AccountNumber::from_string(r.account_number)?,
                    CustomerId::from_uuid(r.customer_id),
                    AccountType::from_str(&r.account_type)?,
                    Money::new(r.balance, Currency::from_str(&r.currency)?)?,
                    AccountStatus::from_str(&r.status)?,
                    r.opened_at,
                    r.updated_at,
                )?))
            }
            None => {
                info!("⚠️ Account not found");
                Ok(None)
            }
        }
    }
}
```

---

## 🧪 测试策略

### 1. 单元测试 (Domain Model - 零依赖)

```rust
// tests/unit/account_test.rs
use banking_service::domain::model::Account;
use banking_service::domain::value_objects::{Money, Currency, AccountType};
    
    #[test]
fn test_open_account_with_sufficient_deposit() {
    // Arrange
    let customer_id = CustomerId::new();
    let account_type = AccountType::Savings;
    let initial_deposit = Money::new(1000.0, Currency::USD).unwrap();
    
    // Act
    let result = Account::open(customer_id, account_type, initial_deposit);
    
    // Assert
    assert!(result.is_ok());
    let (account, event) = result.unwrap();
    assert_eq!(account.balance().amount(), 1000.0);
    
    match event {
        AccountEvent::AccountOpened { initial_balance, .. } => {
            assert_eq!(initial_balance.amount(), 1000.0);
        }
        _ => panic!("Wrong event type"),
    }
    }
    
    #[test]
fn test_withdraw_insufficient_balance() {
    // Arrange
    let customer_id = CustomerId::new();
    let initial_deposit = Money::new(100.0, Currency::USD).unwrap();
    let (mut account, _) = Account::open(customer_id, AccountType::Checking, initial_deposit).unwrap();
    
    // Act
    let withdraw_amount = Money::new(200.0, Currency::USD).unwrap();
    let result = account.withdraw(withdraw_amount);
    
    // Assert
    assert!(result.is_err());
    assert!(matches!(result.unwrap_err(), DomainError::InsufficientBalance { .. }));
}
```

---

### 2. 集成测试 (Application + Infrastructure)

```rust
// tests/integration/transfer_test.rs
use banking_service::*;
use testcontainers::{clients, images};
use sqlx::PgPool;

#[tokio::test]
async fn test_transfer_end_to_end() {
    // 1. 启动 PostgreSQL 容器
    let docker = clients::Cli::default();
    let postgres = docker.run(images::postgres::Postgres::default());
    let port = postgres.get_host_port_ipv4(5432);
    let db_url = format!("postgres://postgres:postgres@localhost:{}/postgres", port);
    
    // 2. 初始化数据库
    let pool = PgPool::connect(&db_url).await.unwrap();
    sqlx::migrate!("./migrations").run(&pool).await.unwrap();
    
    // 3. 创建服务
    let account_repo = Arc::new(PostgresAccountRepository::new(pool.clone()));
    let transfer_service = Arc::new(TransferService);
    let transfer_use_case = Arc::new(TransferMoneyUseCase::new(
        account_repo.clone(),
        transfer_service,
    ));
    
    // 4. 创建测试账户
    let from_account = Account::open(
        CustomerId::new(),
        AccountType::Checking,
        Money::new(1000.0, Currency::USD).unwrap(),
    ).unwrap().0;
    
    let to_account = Account::open(
        CustomerId::new(),
        AccountType::Savings,
        Money::new(500.0, Currency::USD).unwrap(),
    ).unwrap().0;
    
    account_repo.save(&from_account).await.unwrap();
    account_repo.save(&to_account).await.unwrap();
    
    // 5. 执行转账
    let request = TransferRequestDto {
        from_account_number: from_account.account_number().clone(),
        to_account_number: to_account.account_number().clone(),
        amount: Money::new(300.0, Currency::USD).unwrap(),
    };
    
    let response = transfer_use_case.execute(request).await.unwrap();
    
    // 6. 验证结果
    assert_eq!(response.new_from_balance.amount(), 700.0);
    assert_eq!(response.new_to_balance.amount(), 800.0);
    
    // 7. 验证数据库
    let from_db = account_repo.find_by_id(from_account.id()).await.unwrap().unwrap();
    assert_eq!(from_db.balance().amount(), 700.0);
}
```

---

## ⚡ 性能优化

### 1. 事务管理

```rust
// infrastructure/persistence/transaction.rs
use sqlx::{Postgres, Transaction};

pub struct UnitOfWork<'a> {
    tx: Transaction<'a, Postgres>,
}

impl<'a> UnitOfWork<'a> {
    pub async fn begin(pool: &'a PgPool) -> Result<Self, sqlx::Error> {
        let tx = pool.begin().await?;
        Ok(Self { tx })
    }
    
    #[instrument(name = "commit_transaction")]
    pub async fn commit(self) -> Result<(), sqlx::Error> {
        self.tx.commit().await
    }
    
    pub async fn rollback(self) -> Result<(), sqlx::Error> {
        self.tx.rollback().await
    }
}

// 使用示例
pub async fn transfer_with_transaction(
    pool: &PgPool,
    from_account: &Account,
    to_account: &Account,
) -> Result<()> {
    let mut uow = UnitOfWork::begin(pool).await?;
    
    // 保存账户 (使用事务)
    save_account_tx(&mut uow.tx, from_account).await?;
    save_account_tx(&mut uow.tx, to_account).await?;
    
    // 提交事务
    uow.commit().await?;
    
    Ok(())
}
```

---

## 🚀 生产部署

### Cargo.toml

```toml
[package]
name = "banking-service"
version = "1.0.0"
edition = "2024"
rust-version = "1.90"

[dependencies]
# Async runtime
tokio = { version = "1.41", features = ["full"] }
async-trait = "0.1.82"

# Web framework
axum = { version = "0.7", features = ["macros"] }
tower = "0.5"
tower-http = { version = "0.6", features = ["trace"] }

# Database
sqlx = { version = "0.8", features = ["postgres", "runtime-tokio", "macros", "uuid", "chrono"] }

# Serialization
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# Error handling
anyhow = "1.0"
thiserror = "2.0"

# UUID & Time
uuid = { version = "1.11", features = ["serde", "v4"] }
chrono = { version = "0.4", features = ["serde"] }

# Tracing & OTLP
tracing = "0.1"
tracing-subscriber = { version = "0.3.18", features = ["env-filter"] }
tracing-opentelemetry = "0.31"
opentelemetry = "0.31"
opentelemetry_sdk = "0.31"
opentelemetry-otlp = "0.16"

# Random
rand = "0.8"

[dev-dependencies]
tokio-test = "0.4"
testcontainers = "0.23"
```

---

### Docker Compose

```yaml
version: '3.9'

services:
  banking-service:
    build: .
    ports:
      - "8080:8080"
    environment:
      - DATABASE_URL=postgres://postgres:password@postgres:5432/banking
      - OTLP_ENDPOINT=http://otel-collector:4317
    depends_on:
      - postgres
      - otel-collector

  postgres:
    image: postgres:16-alpine
    environment:
      POSTGRES_PASSWORD: password
      POSTGRES_DB: banking
    ports:
      - "5432:5432"
    volumes:
      - postgres_data:/var/lib/postgresql/data

  otel-collector:
    image: otel/opentelemetry-collector:0.111.0
    command: ["--config=/etc/otel-config.yaml"]
    volumes:
      - ./otel-config.yaml:/etc/otel-config.yaml
    ports:
      - "4317:4317"
      - "4318:4318"

  jaeger:
    image: jaegertracing/all-in-one:1.62
    ports:
      - "16686:16686"
    environment:
      - COLLECTOR_OTLP_ENABLED=true

volumes:
  postgres_data:
```

---

## ✅ 最佳实践清单

### 洋葱架构设计

- [x] **严格依赖方向**: 外层→内层，内层永不依赖外层
- [x] **层次清晰**: Domain Model → Domain Services → Application → Infrastructure
- [x] **接口隔离**: 每层定义自己的接口
- [x] **DTO 转换**: 在 Application 层转换 DTO ↔ Domain Model
- [x] **领域事件**: 用事件记录状态变化，而非直接日志

### OTLP 集成

- [x] **Domain Model 层**: 零 OTLP 依赖
- [x] **Domain Services 层**: 最小化 OTLP (仅复杂逻辑)
- [x] **Application 层**: 主要 OTLP 集成点
- [x] **Infrastructure 层**: 完整 OTLP 插桩
- [x] **追踪传播**: 通过 async context 自动传播

### Rust 特性

- [x] **async-trait**: 异步仓储接口
- [x] **Arc**: 共享所有权
- [x] **NewType 模式**: AccountId, Money 等值对象
- [x] **thiserror**: 领域错误定义
- [x] **Result 类型**: 错误传播

---

## 📚 参考资源

### 国际标准

1. **Onion Architecture**: [Jeffrey Palermo's Blog](https://jeffreypalermo.com/2008/07/the-onion-architecture-part-1/)
2. **Clean Architecture**: Robert C. Martin, 2012
3. **Domain-Driven Design**: Eric Evans, 2003
4. **Microsoft .NET Architecture Guide**: [docs.microsoft.com](https://docs.microsoft.com/architecture)

### Rust 生态

1. **Axum**: [docs.rs/axum](https://docs.rs/axum)
2. **SQLx**: [docs.rs/sqlx](https://docs.rs/sqlx)
3. **async-trait**: [docs.rs/async-trait](https://docs.rs/async-trait)
4. **OpenTelemetry**: [docs.rs/opentelemetry](https://docs.rs/opentelemetry)

---

## 🎉 总结

洋葱架构是一种**企业级架构模式**，强调:

1. **严格的层次结构**: 4 层清晰分离
2. **依赖倒置**: 外层依赖内层，内层定义接口
3. **核心稳定**: 领域模型层最稳定，完全无外部依赖
4. **可测试性**: 每层独立测试，Mock 外层依赖

在 Rust 1.90 + OTLP 中:

- ✅ 使用 **trait** 定义接口 (仓储、服务)
- ✅ **Arc** 共享所有权
- ✅ **async-trait** 异步方法
- ✅ **分层追踪**: Domain Model (零) → Application (集成点) → Infrastructure (完整)

---

**文档版本**: v1.0  
**创建日期**: 2025年10月11日  
**Rust 版本**: 1.90+  
**OpenTelemetry**: 0.31.0

---

**🧅 洋葱架构 - 构建可维护、可扩展的企业级 Rust 应用！**
