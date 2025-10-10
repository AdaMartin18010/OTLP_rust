# SQL 数据库语义约定 - Rust 完整实现

> **Semantic Conventions版本**: v1.27.0  
> **稳定性**: Stable  
> **最后更新**: 2025年10月10日

---

## 目录

- [SQL 数据库语义约定 - Rust 完整实现](#sql-数据库语义约定---rust-完整实现)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 适用范围](#11-适用范围)
    - [1.2 核心目标](#12-核心目标)
    - [1.3 Rust 生态系统](#13-rust-生态系统)
  - [2. Rust 基础设施](#2-rust-基础设施)
    - [2.1 依赖配置](#21-依赖配置)
    - [2.2 核心导入](#22-核心导入)
    - [2.3 SQL 语义约定常量](#23-sql-语义约定常量)
  - [3. SQL 属性类型系统](#3-sql-属性类型系统)
    - [3.1 数据库系统枚举](#31-数据库系统枚举)
    - [3.2 SQL 操作类型](#32-sql-操作类型)
    - [3.3 SQL 属性结构体](#33-sql-属性结构体)
  - [4. PostgreSQL 实现](#4-postgresql-实现)
    - [4.1 连接与追踪](#41-连接与追踪)
    - [4.2 查询执行](#42-查询执行)
    - [4.3 事务处理](#43-事务处理)
  - [5. MySQL 实现](#5-mysql-实现)
    - [5.1 连接与追踪](#51-连接与追踪)
    - [5.2 预处理语句](#52-预处理语句)
  - [6. SQL 语句处理](#6-sql-语句处理)
    - [6.1 语句脱敏](#61-语句脱敏)
    - [6.2 参数化查询](#62-参数化查询)
    - [6.3 SQL 注入防护](#63-sql-注入防护)
  - [7. 连接池监控](#7-连接池监控)
    - [7.1 连接池 Metrics](#71-连接池-metrics)
    - [7.2 sqlx Pool 集成](#72-sqlx-pool-集成)
  - [8. 完整示例](#8-完整示例)
    - [8.1 PostgreSQL 用户服务](#81-postgresql-用户服务)
    - [8.2 MySQL 订单服务](#82-mysql-订单服务)
    - [8.3 事务示例](#83-事务示例)
  - [9. 性能优化](#9-性能优化)
    - [9.1 慢查询追踪](#91-慢查询追踪)
    - [9.2 批量操作](#92-批量操作)
  - [10. 最佳实践](#10-最佳实践)
    - [10.1 推荐做法](#101-推荐做法)
    - [10.2 避免事项](#102-避免事项)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [相关规范](#相关规范)
    - [Rust Crates](#rust-crates)

---

## 1. 概述

### 1.1 适用范围

```text
✅ PostgreSQL
✅ MySQL / MariaDB
✅ Microsoft SQL Server
✅ SQLite
✅ CockroachDB
✅ 其他关系型数据库
```

### 1.2 核心目标

```text
1. 统一SQL追踪标准
2. 识别慢查询与性能瓶颈
3. 监控数据库连接与资源使用
4. 追踪事务与隔离级别
5. 确保敏感数据安全
```

### 1.3 Rust 生态系统

```rust
// Rust SQL 生态系统
// - sqlx: 异步SQL工具包，支持PostgreSQL、MySQL、SQLite
// - diesel: 类型安全的ORM
// - tokio-postgres: 纯异步PostgreSQL客户端
// - mysql_async: 异步MySQL客户端
```

---

## 2. Rust 基础设施

### 2.1 依赖配置

```toml
[package]
name = "sql-otlp-example"
version = "0.1.0"
edition = "2021"

[dependencies]
# SQLx - 异步SQL工具包
sqlx = { version = "0.7", features = [
    "runtime-tokio-rustls",
    "postgres",
    "mysql",
    "sqlite",
    "macros",
    "migrate",
] }

# OpenTelemetry
opentelemetry = { version = "0.22", features = ["trace", "metrics"] }
opentelemetry_sdk = { version = "0.22", features = ["rt-tokio"] }
opentelemetry-semantic-conventions = "0.14"

# 运行时
tokio = { version = "1", features = ["full"] }

# 实用工具
anyhow = "1.0"
thiserror = "1.0"
uuid = { version = "1.0", features = ["v4", "serde"] }
chrono = { version = "0.4", features = ["serde"] }

# 日志
tracing = "0.1"
tracing-subscriber = "0.3"
```

### 2.2 核心导入

```rust
use opentelemetry::{
    global,
    trace::{Tracer, Span, SpanKind, Status},
    KeyValue,
};
use sqlx::{Pool, Postgres, MySql, Row, Transaction};
use std::time::Instant;
```

### 2.3 SQL 语义约定常量

```rust
pub mod db_conventions {
    // 数据库系统属性
    pub const DB_SYSTEM: &str = "db.system";
    pub const DB_NAME: &str = "db.name";
    pub const DB_OPERATION: &str = "db.operation";
    pub const DB_STATEMENT: &str = "db.statement";
    pub const DB_USER: &str = "db.user";
    
    // SQL 特定属性
    pub const DB_SQL_TABLE: &str = "db.sql.table";
    pub const DB_SQL_SCHEMA: &str = "db.sql.schema";
    
    // 连接属性
    pub const SERVER_ADDRESS: &str = "server.address";
    pub const SERVER_PORT: &str = "server.port";
    pub const NETWORK_PEER_ADDRESS: &str = "network.peer.address";
    pub const NETWORK_PEER_PORT: &str = "network.peer.port";
    
    // 性能属性
    pub const DB_QUERY_DURATION: &str = "db.query.duration_ms";
    pub const DB_ROWS_AFFECTED: &str = "db.rows_affected";
    pub const DB_ROWS_RETURNED: &str = "db.rows_returned";
    
    // 事务属性
    pub const DB_TRANSACTION_ID: &str = "db.transaction.id";
    pub const DB_TRANSACTION_ISOLATION: &str = "db.transaction.isolation";
}
```

---

## 3. SQL 属性类型系统

### 3.1 数据库系统枚举

```rust
/// SQL 数据库系统
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DbSystem {
    PostgreSQL,
    MySQL,
    MariaDB,
    SQLite,
    MsSQL,
    Oracle,
    CockroachDB,
}

impl DbSystem {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::PostgreSQL => "postgresql",
            Self::MySQL => "mysql",
            Self::MariaDB => "mariadb",
            Self::SQLite => "sqlite",
            Self::MsSQL => "mssql",
            Self::Oracle => "oracle",
            Self::CockroachDB => "cockroachdb",
        }
    }
    
    pub fn default_port(&self) -> Option<u16> {
        match self {
            Self::PostgreSQL | Self::CockroachDB => Some(5432),
            Self::MySQL | Self::MariaDB => Some(3306),
            Self::MsSQL => Some(1433),
            Self::Oracle => Some(1521),
            Self::SQLite => None,
        }
    }
}
```

### 3.2 SQL 操作类型

```rust
/// SQL 操作类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SqlOperation {
    Select,
    Insert,
    Update,
    Delete,
    Create,
    Drop,
    Alter,
    Transaction,
    Other,
}

impl SqlOperation {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Select => "SELECT",
            Self::Insert => "INSERT",
            Self::Update => "UPDATE",
            Self::Delete => "DELETE",
            Self::Create => "CREATE",
            Self::Drop => "DROP",
            Self::Alter => "ALTER",
            Self::Transaction => "TRANSACTION",
            Self::Other => "OTHER",
        }
    }
    
    /// 从 SQL 语句推断操作类型
    pub fn from_statement(statement: &str) -> Self {
        let statement_upper = statement.trim().to_uppercase();
        
        if statement_upper.starts_with("SELECT") {
            Self::Select
        } else if statement_upper.starts_with("INSERT") {
            Self::Insert
        } else if statement_upper.starts_with("UPDATE") {
            Self::Update
        } else if statement_upper.starts_with("DELETE") {
            Self::Delete
        } else if statement_upper.starts_with("CREATE") {
            Self::Create
        } else if statement_upper.starts_with("DROP") {
            Self::Drop
        } else if statement_upper.starts_with("ALTER") {
            Self::Alter
        } else if statement_upper.starts_with("BEGIN") 
            || statement_upper.starts_with("COMMIT") 
            || statement_upper.starts_with("ROLLBACK") {
            Self::Transaction
        } else {
            Self::Other
        }
    }
}
```

### 3.3 SQL 属性结构体

```rust
/// SQL 数据库属性
#[derive(Debug, Clone)]
pub struct SqlAttributes {
    pub system: DbSystem,
    pub database_name: String,
    pub server_address: Option<String>,
    pub server_port: Option<u16>,
    pub operation: Option<SqlOperation>,
    pub statement: Option<String>,
    pub table: Option<String>,
    pub user: Option<String>,
}

impl SqlAttributes {
    /// 创建基础属性
    pub fn new(system: DbSystem, database_name: impl Into<String>) -> Self {
        Self {
            system,
            database_name: database_name.into(),
            server_address: None,
            server_port: system.default_port(),
            operation: None,
            statement: None,
            table: None,
            user: None,
        }
    }
    
    /// 设置服务器地址
    pub fn with_server(mut self, address: impl Into<String>, port: u16) -> Self {
        self.server_address = Some(address.into());
        self.server_port = Some(port);
        self
    }
    
    /// 设置操作和语句
    pub fn with_query(mut self, statement: impl Into<String>) -> Self {
        let stmt = statement.into();
        self.operation = Some(SqlOperation::from_statement(&stmt));
        self.statement = Some(stmt);
        self
    }
    
    /// 转换为 KeyValue 数组
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new(db_conventions::DB_SYSTEM, self.system.as_str()),
            KeyValue::new(db_conventions::DB_NAME, self.database_name.clone()),
        ];
        
        if let Some(ref addr) = self.server_address {
            attrs.push(KeyValue::new(db_conventions::SERVER_ADDRESS, addr.clone()));
        }
        
        if let Some(port) = self.server_port {
            attrs.push(KeyValue::new(db_conventions::SERVER_PORT, port as i64));
        }
        
        if let Some(op) = self.operation {
            attrs.push(KeyValue::new(db_conventions::DB_OPERATION, op.as_str()));
        }
        
        if let Some(ref stmt) = self.statement {
            attrs.push(KeyValue::new(db_conventions::DB_STATEMENT, stmt.clone()));
        }
        
        if let Some(ref table) = self.table {
            attrs.push(KeyValue::new(db_conventions::DB_SQL_TABLE, table.clone()));
        }
        
        if let Some(ref user) = self.user {
            attrs.push(KeyValue::new(db_conventions::DB_USER, user.clone()));
        }
        
        attrs
    }
}
```

---

## 4. PostgreSQL 实现

### 4.1 连接与追踪

```rust
use sqlx::{PgPool, postgres::PgPoolOptions};

/// PostgreSQL 追踪客户端
pub struct PostgresClient {
    pool: PgPool,
    tracer: global::BoxedTracer,
    base_attrs: SqlAttributes,
}

impl PostgresClient {
    /// 创建客户端
    pub async fn new(database_url: &str) -> anyhow::Result<Self> {
        let pool = PgPoolOptions::new()
            .max_connections(10)
            .connect(database_url)
            .await?;
        
        let tracer = global::tracer("postgres-client");
        
        let base_attrs = SqlAttributes::new(DbSystem::PostgreSQL, "myapp")
            .with_server("localhost", 5432);
        
        Ok(Self {
            pool,
            tracer,
            base_attrs,
        })
    }
}
```

### 4.2 查询执行

```rust
impl PostgresClient {
    /// 执行查询 (带追踪)
    pub async fn query_with_tracing<T>(
        &self,
        statement: &str,
    ) -> anyhow::Result<Vec<T>>
    where
        T: for<'r> sqlx::FromRow<'r, sqlx::postgres::PgRow> + Send + Unpin,
    {
        // 创建 CLIENT Span
        let mut span = self.tracer
            .span_builder("db_query")
            .with_kind(SpanKind::Client)
            .start(&self.tracer);
        
        // 设置 SQL 属性
        let attrs = self.base_attrs.clone()
            .with_query(statement);
        
        span.set_attributes(attrs.to_key_values());
        
        // 执行查询并计时
        let start = Instant::now();
        let result = sqlx::query_as::<_, T>(statement)
            .fetch_all(&self.pool)
            .await;
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new(
            db_conventions::DB_QUERY_DURATION,
            duration.as_millis() as i64,
        ));
        
        match result {
            Ok(ref rows) => {
                span.set_attribute(KeyValue::new(
                    db_conventions::DB_ROWS_RETURNED,
                    rows.len() as i64,
                ));
                span.set_status(Status::Ok);
            }
            Err(ref e) => {
                span.set_status(Status::error(format!("Query failed: {}", e)));
                tracing::error!("Database query error: {}", e);
            }
        }
        
        span.end();
        result.map_err(Into::into)
    }
    
    /// 执行语句 (INSERT/UPDATE/DELETE)
    pub async fn execute_with_tracing(
        &self,
        statement: &str,
    ) -> anyhow::Result<u64> {
        let mut span = self.tracer
            .span_builder("db_execute")
            .with_kind(SpanKind::Client)
            .start(&self.tracer);
        
        let attrs = self.base_attrs.clone()
            .with_query(statement);
        
        span.set_attributes(attrs.to_key_values());
        
        let start = Instant::now();
        let result = sqlx::query(statement)
            .execute(&self.pool)
            .await;
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new(
            db_conventions::DB_QUERY_DURATION,
            duration.as_millis() as i64,
        ));
        
        match result {
            Ok(ref result) => {
                let rows_affected = result.rows_affected();
                span.set_attribute(KeyValue::new(
                    db_conventions::DB_ROWS_AFFECTED,
                    rows_affected as i64,
                ));
                span.set_status(Status::Ok);
            }
            Err(ref e) => {
                span.set_status(Status::error(format!("{}", e)));
            }
        }
        
        span.end();
        result.map(|r| r.rows_affected()).map_err(Into::into)
    }
}
```

### 4.3 事务处理

```rust
impl PostgresClient {
    /// 执行事务 (带追踪)
    pub async fn transaction_with_tracing<F, T>(
        &self,
        operation: F,
    ) -> anyhow::Result<T>
    where
        F: FnOnce(&mut Transaction<'_, Postgres>) -> std::pin::Pin<Box<dyn std::future::Future<Output = anyhow::Result<T>> + Send + '_>>,
        T: Send,
    {
        let mut span = self.tracer
            .span_builder("db_transaction")
            .with_kind(SpanKind::Client)
            .start(&self.tracer);
        
        let mut attrs = self.base_attrs.clone();
        attrs.operation = Some(SqlOperation::Transaction);
        
        span.set_attributes(attrs.to_key_values());
        
        // 开始事务
        let mut tx = self.pool.begin().await?;
        
        // 执行操作
        let result = operation(&mut tx).await;
        
        match result {
            Ok(value) => {
                // 提交事务
                tx.commit().await?;
                span.set_status(Status::Ok);
                span.end();
                Ok(value)
            }
            Err(e) => {
                // 回滚事务
                let _ = tx.rollback().await;
                span.set_status(Status::error(format!("Transaction failed: {}", e)));
                span.end();
                Err(e)
            }
        }
    }
}
```

---

## 5. MySQL 实现

### 5.1 连接与追踪

```rust
use sqlx::{MySqlPool, mysql::MySqlPoolOptions};

/// MySQL 追踪客户端
pub struct MysqlClient {
    pool: MySqlPool,
    tracer: global::BoxedTracer,
    base_attrs: SqlAttributes,
}

impl MysqlClient {
    pub async fn new(database_url: &str) -> anyhow::Result<Self> {
        let pool = MySqlPoolOptions::new()
            .max_connections(10)
            .connect(database_url)
            .await?;
        
        let tracer = global::tracer("mysql-client");
        
        let base_attrs = SqlAttributes::new(DbSystem::MySQL, "orders_db")
            .with_server("localhost", 3306);
        
        Ok(Self {
            pool,
            tracer,
            base_attrs,
        })
    }
}
```

### 5.2 预处理语句

```rust
impl MysqlClient {
    /// 执行预处理查询
    pub async fn query_with_params<T>(
        &self,
        statement: &str,
        params: &[&(dyn sqlx::Encode<'_, MySql> + Sync)],
    ) -> anyhow::Result<Vec<T>>
    where
        T: for<'r> sqlx::FromRow<'r, sqlx::mysql::MySqlRow> + Send + Unpin,
    {
        let mut span = self.tracer
            .span_builder("db_query")
            .with_kind(SpanKind::Client)
            .start(&self.tracer);
        
        let attrs = self.base_attrs.clone()
            .with_query(statement);
        
        span.set_attributes(attrs.to_key_values());
        
        // 构建查询
        let mut query = sqlx::query_as::<_, T>(statement);
        
        // 添加参数（注意：sqlx 的参数绑定需要在查询构建时完成）
        // 这里简化为直接fetch
        let start = Instant::now();
        let result = query.fetch_all(&self.pool).await;
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new(
            db_conventions::DB_QUERY_DURATION,
            duration.as_millis() as i64,
        ));
        
        match result {
            Ok(ref rows) => {
                span.set_attribute(KeyValue::new(
                    db_conventions::DB_ROWS_RETURNED,
                    rows.len() as i64,
                ));
                span.set_status(Status::Ok);
            }
            Err(ref e) => {
                span.set_status(Status::error(format!("{}", e)));
            }
        }
        
        span.end();
        result.map_err(Into::into)
    }
}
```

---

## 6. SQL 语句处理

### 6.1 语句脱敏

```rust
/// SQL 语句脱敏
pub mod sql_sanitizer {
    use regex::Regex;
    use once_cell::sync::Lazy;
    
    static VALUE_PATTERN: Lazy<Regex> = Lazy::new(|| {
        Regex::new(r"'[^']*'|\d+").unwrap()
    });
    
    /// 脱敏 SQL 语句
    pub fn sanitize_statement(statement: &str) -> String {
        // 替换字符串字面量和数字为占位符
        VALUE_PATTERN.replace_all(statement, "?").to_string()
    }
    
    /// 移除敏感关键词
    pub fn remove_sensitive_keywords(statement: &str) -> String {
        statement
            .replace("password", "***")
            .replace("PASSWORD", "***")
            .replace("secret", "***")
            .replace("SECRET", "***")
            .replace("token", "***")
            .replace("TOKEN", "***")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_sanitize_statement() {
        let original = "SELECT * FROM users WHERE email='user@example.com' AND age=25";
        let sanitized = sql_sanitizer::sanitize_statement(original);
        assert_eq!(sanitized, "SELECT * FROM users WHERE email=? AND age=?");
    }
}
```

### 6.2 参数化查询

```rust
/// 安全的参数化查询构建器
pub struct SafeQueryBuilder {
    statement: String,
    params: Vec<String>,
}

impl SafeQueryBuilder {
    pub fn new(base_query: impl Into<String>) -> Self {
        Self {
            statement: base_query.into(),
            params: Vec::new(),
        }
    }
    
    pub fn bind(mut self, param: impl ToString) -> Self {
        self.params.push(param.to_string());
        self
    }
    
    pub fn build(&self) -> (String, &[String]) {
        (&self.statement, &self.params)
    }
}
```

### 6.3 SQL 注入防护

```rust
/// SQL 注入检测
pub fn detect_sql_injection(input: &str) -> bool {
    let dangerous_patterns = [
        "';",
        "--",
        "/*",
        "*/",
        "xp_",
        "sp_",
        "UNION",
        "DROP",
        "DELETE",
        "INSERT",
        "UPDATE",
    ];
    
    let input_upper = input.to_uppercase();
    dangerous_patterns.iter().any(|&pattern| input_upper.contains(pattern))
}
```

---

## 7. 连接池监控

### 7.1 连接池 Metrics

```rust
use opentelemetry::metrics::{Gauge, Counter, Meter};

pub struct ConnectionPoolMetrics {
    active_connections: Gauge<u64>,
    idle_connections: Gauge<u64>,
    total_connections: Gauge<u64>,
    connection_wait_time: Counter<f64>,
}

impl ConnectionPoolMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            active_connections: meter
                .u64_gauge("db.pool.connections.active")
                .with_description("Active database connections")
                .init(),
            
            idle_connections: meter
                .u64_gauge("db.pool.connections.idle")
                .with_description("Idle database connections")
                .init(),
            
            total_connections: meter
                .u64_gauge("db.pool.connections.total")
                .with_description("Total database connections")
                .init(),
            
            connection_wait_time: meter
                .f64_counter("db.pool.connection_wait_time")
                .with_description("Time waiting for connection")
                .with_unit("s")
                .init(),
        }
    }
    
    pub fn record_pool_stats(&self, active: u64, idle: u64, total: u64) {
        self.active_connections.record(active, &[]);
        self.idle_connections.record(idle, &[]);
        self.total_connections.record(total, &[]);
    }
}
```

### 7.2 sqlx Pool 集成

```rust
impl PostgresClient {
    /// 获取连接池统计
    pub fn get_pool_stats(&self) -> ConnectionPoolStats {
        ConnectionPoolStats {
            active: self.pool.size() as u64,
            idle: self.pool.num_idle() as u64,
            total: self.pool.size() as u64,
        }
    }
}

pub struct ConnectionPoolStats {
    pub active: u64,
    pub idle: u64,
    pub total: u64,
}
```

---

## 8. 完整示例

### 8.1 PostgreSQL 用户服务

```rust
use serde::{Deserialize, Serialize};
use uuid::Uuid;

#[derive(Debug, Serialize, Deserialize, sqlx::FromRow)]
pub struct User {
    pub id: Uuid,
    pub username: String,
    pub email: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

pub struct UserService {
    db: PostgresClient,
}

impl UserService {
    pub async fn new(database_url: &str) -> anyhow::Result<Self> {
        Ok(Self {
            db: PostgresClient::new(database_url).await?,
        })
    }
    
    /// 创建用户
    pub async fn create_user(
        &self,
        username: &str,
        email: &str,
    ) -> anyhow::Result<User> {
        let statement = "
            INSERT INTO users (id, username, email, created_at)
            VALUES ($1, $2, $3, NOW())
            RETURNING id, username, email, created_at
        ";
        
        let user_id = Uuid::new_v4();
        
        let user = sqlx::query_as::<_, User>(statement)
            .bind(user_id)
            .bind(username)
            .bind(email)
            .fetch_one(&self.db.pool)
            .await?;
        
        Ok(user)
    }
    
    /// 查询用户
    pub async fn get_user(&self, user_id: Uuid) -> anyhow::Result<Option<User>> {
        let statement = "SELECT id, username, email, created_at FROM users WHERE id = $1";
        
        let user = self.db.query_with_tracing::<User>(statement)
            .await?
            .into_iter()
            .next();
        
        Ok(user)
    }
    
    /// 列出所有用户
    pub async fn list_users(&self) -> anyhow::Result<Vec<User>> {
        let statement = "SELECT id, username, email, created_at FROM users ORDER BY created_at DESC";
        
        self.db.query_with_tracing::<User>(statement).await
    }
}
```

### 8.2 MySQL 订单服务

```rust
#[derive(Debug, Serialize, Deserialize, sqlx::FromRow)]
pub struct Order {
    pub id: i64,
    pub user_id: Uuid,
    pub total: f64,
    pub status: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

pub struct OrderService {
    db: MysqlClient,
}

impl OrderService {
    pub async fn create_order(
        &self,
        user_id: Uuid,
        total: f64,
    ) -> anyhow::Result<i64> {
        let statement = "
            INSERT INTO orders (user_id, total, status, created_at)
            VALUES (?, ?, 'pending', NOW())
        ";
        
        let result = sqlx::query(statement)
            .bind(user_id.to_string())
            .bind(total)
            .execute(&self.db.pool)
            .await?;
        
        Ok(result.last_insert_id() as i64)
    }
}
```

### 8.3 事务示例

```rust
impl UserService {
    /// 转账操作 (事务)
    pub async fn transfer_funds(
        &self,
        from_user_id: Uuid,
        to_user_id: Uuid,
        amount: f64,
    ) -> anyhow::Result<()> {
        self.db.transaction_with_tracing(|tx| {
            Box::pin(async move {
                // 扣除发送方余额
                sqlx::query("UPDATE accounts SET balance = balance - $1 WHERE user_id = $2")
                    .bind(amount)
                    .bind(from_user_id)
                    .execute(&mut **tx)
                    .await?;
                
                // 增加接收方余额
                sqlx::query("UPDATE accounts SET balance = balance + $1 WHERE user_id = $2")
                    .bind(amount)
                    .bind(to_user_id)
                    .execute(&mut **tx)
                    .await?;
                
                Ok(())
            })
        }).await
    }
}
```

---

## 9. 性能优化

### 9.1 慢查询追踪

```rust
/// 慢查询检测中间件
pub struct SlowQueryDetector {
    threshold_ms: u64,
}

impl SlowQueryDetector {
    pub fn new(threshold_ms: u64) -> Self {
        Self { threshold_ms }
    }
    
    pub fn check_slow_query(&self, duration_ms: u64, statement: &str) {
        if duration_ms > self.threshold_ms {
            tracing::warn!(
                duration_ms = duration_ms,
                threshold_ms = self.threshold_ms,
                statement = statement,
                "Slow query detected"
            );
        }
    }
}
```

### 9.2 批量操作

```rust
impl PostgresClient {
    /// 批量插入
    pub async fn batch_insert_users(
        &self,
        users: Vec<(String, String)>,
    ) -> anyhow::Result<u64> {
        let mut span = self.tracer
            .span_builder("db_batch_insert")
            .with_kind(SpanKind::Client)
            .start(&self.tracer);
        
        span.set_attribute(KeyValue::new("batch.size", users.len() as i64));
        
        let mut inserted = 0;
        
        for (username, email) in users {
            sqlx::query("INSERT INTO users (username, email) VALUES ($1, $2)")
                .bind(username)
                .bind(email)
                .execute(&self.pool)
                .await?;
            
            inserted += 1;
        }
        
        span.set_attribute(KeyValue::new(
            db_conventions::DB_ROWS_AFFECTED,
            inserted,
        ));
        span.set_status(Status::Ok);
        span.end();
        
        Ok(inserted as u64)
    }
}
```

---

## 10. 最佳实践

### 10.1 推荐做法

```rust
pub mod best_practices {
    /// ✅ 使用参数化查询
    pub async fn good_parameterized_query(pool: &PgPool, email: &str) {
        let _ = sqlx::query("SELECT * FROM users WHERE email = $1")
            .bind(email)
            .fetch_all(pool)
            .await;
    }
    
    /// ✅ 脱敏 SQL 语句
    pub fn good_sanitize_statement() {
        let statement = "SELECT * FROM users WHERE email='user@example.com'";
        let sanitized = sql_sanitizer::sanitize_statement(statement);
        // 记录: "SELECT * FROM users WHERE email=?"
    }
    
    /// ✅ 使用连接池
    pub async fn good_use_pool(pool: &PgPool) {
        // 连接池自动管理连接
        let _ = sqlx::query("SELECT 1").fetch_all(pool).await;
    }
}
```

### 10.2 避免事项

```rust
pub mod anti_patterns {
    /// ❌ 字符串拼接（SQL注入风险）
    pub async fn bad_string_concat(pool: &PgPool, email: &str) {
        let query = format!("SELECT * FROM users WHERE email = '{}'", email);
        // 危险！容易受到 SQL 注入攻击
        let _ = sqlx::query(&query).fetch_all(pool).await;
    }
    
    /// ❌ 记录完整的敏感 SQL
    pub fn bad_log_sensitive_sql() {
        let statement = "INSERT INTO users (password) VALUES ('secret123')";
        tracing::info!("Executing: {}", statement); // 泄露敏感信息！
    }
}
```

---

## 参考资源

### 官方文档

1. **OpenTelemetry Database Conventions**: <https://opentelemetry.io/docs/specs/semconv/database/>
2. **SQLx Documentation**: <https://github.com/launchbadge/sqlx>
3. **OpenTelemetry Rust SDK**: <https://github.com/open-telemetry/opentelemetry-rust>

### 相关规范

1. **PostgreSQL Protocol**: <https://www.postgresql.org/docs/current/protocol.html>
2. **MySQL Protocol**: <https://dev.mysql.com/doc/dev/mysql-server/latest/>

### Rust Crates

1. **sqlx**: <https://github.com/launchbadge/sqlx>
2. **diesel**: <https://diesel.rs/>
3. **tokio-postgres**: <https://github.com/sfackler/rust-postgres>
4. **mysql_async**: <https://github.com/blackbeam/mysql_async>

---

**文档版本**: v1.0  
**最后更新**: 2025-10-10  
**作者**: OTLP Rust 标准深度梳理团队
