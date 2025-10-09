# SQLx 数据库追踪 - Rust 完整实现

> **Rust版本**: 1.90+  
> **SQLx**: 0.8.2  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月9日

---

## 目录

- [SQLx 数据库追踪 - Rust 完整实现](#sqlx-数据库追踪---rust-完整实现)
  - [目录](#目录)
  - [1. SQLx 追踪概述](#1-sqlx-追踪概述)
  - [2. 依赖配置](#2-依赖配置)
  - [3. SQLx 中间件实现](#3-sqlx-中间件实现)
  - [4. PostgreSQL 追踪](#4-postgresql-追踪)
  - [5. MySQL 追踪](#5-mysql-追踪)
  - [6. SQLite 追踪](#6-sqlite-追踪)
  - [7. 事务追踪](#7-事务追踪)
  - [8. 连接池监控](#8-连接池监控)
  - [9. 完整示例](#9-完整示例)

---

## 1. SQLx 追踪概述

**数据库追踪语义约定**:

```rust
use opentelemetry_semantic_conventions::trace::{
    DB_SYSTEM,           // 数据库类型: "postgresql", "mysql", "sqlite"
    DB_NAME,             // 数据库名称
    DB_STATEMENT,        // SQL 语句
    DB_OPERATION,        // 操作类型: "SELECT", "INSERT", "UPDATE", "DELETE"
    DB_SQL_TABLE,        // 表名
    DB_USER,             // 数据库用户
    DB_CONNECTION_STRING, // 连接字符串 (不含密码)
};

/// 数据库 Span 属性
#[derive(Debug, Clone)]
pub struct DbSpanAttributes {
    pub system: String,        // "postgresql"
    pub name: String,          // "mydb"
    pub statement: String,     // "SELECT * FROM users WHERE id = $1"
    pub operation: String,     // "SELECT"
    pub table: Option<String>, // "users"
    pub user: Option<String>,  // "dbuser"
}
```

---

## 2. 依赖配置

```toml
[dependencies]
# SQLx
sqlx = { version = "0.8.2", features = [
    "runtime-tokio",
    "postgres",
    "mysql",
    "sqlite",
    "uuid",
    "chrono",
    "json",
] }

# OpenTelemetry
opentelemetry = { version = "0.31.0", features = ["trace"] }
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio", "trace"] }
opentelemetry-semantic-conventions = "0.31.0"

# Tracing
tracing = "0.1.40"
tracing-opentelemetry = "0.31.0"

# Async runtime
tokio = { version = "1.47", features = ["full"] }
```

---

## 3. SQLx 中间件实现

**自定义 Executor 包装器**:

```rust
use sqlx::{Database, Executor, postgres::PgRow};
use tracing::{instrument, info};
use opentelemetry::trace::{SpanKind, TraceContextExt};

/// 带追踪的 SQLx Executor 包装器
pub struct TracedExecutor<'a, DB: Database> {
    executor: &'a mut dyn Executor<'a, Database = DB>,
    db_system: &'static str,
    db_name: String,
}

impl<'a, DB: Database> TracedExecutor<'a, DB> {
    pub fn new(
        executor: &'a mut dyn Executor<'a, Database = DB>,
        db_system: &'static str,
        db_name: String,
    ) -> Self {
        Self {
            executor,
            db_system,
            db_name,
        }
    }
    
    /// 执行带追踪的查询
    #[instrument(skip(self, query))]
    pub async fn execute_traced<'q>(
        &mut self,
        query: &'q str,
    ) -> Result<u64, sqlx::Error> {
        let span = tracing::Span::current();
        
        // 设置数据库属性
        span.record("db.system", self.db_system);
        span.record("db.name", &self.db_name);
        span.record("db.statement", query);
        
        // 提取操作类型
        if let Some(operation) = extract_operation(query) {
            span.record("db.operation", operation);
        }
        
        // 执行查询
        let start = std::time::Instant::now();
        let result = sqlx::query(query).execute(self.executor).await;
        let duration = start.elapsed();
        
        // 记录性能
        info!(
            duration_ms = duration.as_millis(),
            "Query executed"
        );
        
        result.map(|r| r.rows_affected())
    }
}

/// 提取 SQL 操作类型
fn extract_operation(sql: &str) -> Option<&str> {
    let sql = sql.trim().to_uppercase();
    
    if sql.starts_with("SELECT") {
        Some("SELECT")
    } else if sql.starts_with("INSERT") {
        Some("INSERT")
    } else if sql.starts_with("UPDATE") {
        Some("UPDATE")
    } else if sql.starts_with("DELETE") {
        Some("DELETE")
    } else if sql.starts_with("CREATE") {
        Some("CREATE")
    } else if sql.starts_with("DROP") {
        Some("DROP")
    } else {
        None
    }
}
```

---

## 4. PostgreSQL 追踪

**完整 PostgreSQL 集成**:

```rust
use sqlx::postgres::{PgPool, PgPoolOptions};
use sqlx::Row;

/// 带追踪的 PostgreSQL 连接池
pub struct TracedPgPool {
    pool: PgPool,
    db_name: String,
}

impl TracedPgPool {
    /// 创建连接池
    pub async fn connect(database_url: &str) -> Result<Self, sqlx::Error> {
        let pool = PgPoolOptions::new()
            .max_connections(5)
            .connect(database_url)
            .await?;
        
        let db_name = pool.connect_options()
            .get_database()
            .unwrap_or("unknown")
            .to_string();
        
        Ok(Self { pool, db_name })
    }
    
    /// 执行查询
    #[instrument(skip(self, query))]
    pub async fn query(&self, query: &str) -> Result<Vec<PgRow>, sqlx::Error> {
        let span = tracing::Span::current();
        
        // 设置属性
        span.record("db.system", "postgresql");
        span.record("db.name", &self.db_name);
        span.record("db.statement", query);
        
        if let Some(op) = extract_operation(query) {
            span.record("db.operation", op);
        }
        
        // 执行查询
        let rows = sqlx::query(query)
            .fetch_all(&self.pool)
            .await?;
        
        tracing::info!(rows_count = rows.len(), "Query completed");
        
        Ok(rows)
    }
    
    /// 查询单行
    #[instrument(skip(self, query))]
    pub async fn query_one(&self, query: &str) -> Result<PgRow, sqlx::Error> {
        span_attributes!(
            "db.system" => "postgresql",
            "db.name" => &self.db_name,
            "db.statement" => query
        );
        
        sqlx::query(query).fetch_one(&self.pool).await
    }
    
    /// 执行语句
    #[instrument(skip(self, query))]
    pub async fn execute(&self, query: &str) -> Result<u64, sqlx::Error> {
        span_attributes!(
            "db.system" => "postgresql",
            "db.name" => &self.db_name,
            "db.statement" => query
        );
        
        let result = sqlx::query(query).execute(&self.pool).await?;
        
        Ok(result.rows_affected())
    }
}

/// 使用示例
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 连接数据库
    let pool = TracedPgPool::connect("postgres://user:pass@localhost/mydb").await?;
    
    // 查询用户
    let users = pool.query("SELECT * FROM users WHERE active = true").await?;
    
    println!("Found {} users", users.len());
    
    // 插入用户
    let rows_affected = pool.execute(
        "INSERT INTO users (name, email) VALUES ('Alice', 'alice@example.com')"
    ).await?;
    
    println!("Inserted {} rows", rows_affected);
    
    Ok(())
}
```

**类型安全的查询**:

```rust
use sqlx::FromRow;

#[derive(Debug, FromRow)]
pub struct User {
    pub id: i32,
    pub name: String,
    pub email: String,
}

impl TracedPgPool {
    /// 查询用户列表
    #[instrument(skip(self))]
    pub async fn get_users(&self) -> Result<Vec<User>, sqlx::Error> {
        span_attributes!("db.operation" => "SELECT", "db.table" => "users");
        
        let users = sqlx::query_as::<_, User>("SELECT id, name, email FROM users")
            .fetch_all(&self.pool)
            .await?;
        
        tracing::info!(count = users.len(), "Users fetched");
        
        Ok(users)
    }
    
    /// 根据ID获取用户
    #[instrument(skip(self))]
    pub async fn get_user_by_id(&self, id: i32) -> Result<User, sqlx::Error> {
        span_attributes!(
            "db.operation" => "SELECT",
            "db.table" => "users",
            "user.id" => id
        );
        
        let user = sqlx::query_as::<_, User>(
            "SELECT id, name, email FROM users WHERE id = $1"
        )
        .bind(id)
        .fetch_one(&self.pool)
        .await?;
        
        Ok(user)
    }
}
```

---

## 5. MySQL 追踪

**MySQL 实现**:

```rust
use sqlx::mysql::{MySqlPool, MySqlPoolOptions};

pub struct TracedMySqlPool {
    pool: MySqlPool,
    db_name: String,
}

impl TracedMySqlPool {
    pub async fn connect(database_url: &str) -> Result<Self, sqlx::Error> {
        let pool = MySqlPoolOptions::new()
            .max_connections(5)
            .connect(database_url)
            .await?;
        
        let db_name = "mydb".to_string(); // 从 URL 提取
        
        Ok(Self { pool, db_name })
    }
    
    #[instrument(skip(self, query))]
    pub async fn query(&self, query: &str) -> Result<Vec<sqlx::mysql::MySqlRow>, sqlx::Error> {
        span_attributes!(
            "db.system" => "mysql",
            "db.name" => &self.db_name,
            "db.statement" => query
        );
        
        sqlx::query(query).fetch_all(&self.pool).await
    }
}
```

---

## 6. SQLite 追踪

**SQLite 实现**:

```rust
use sqlx::sqlite::{SqlitePool, SqlitePoolOptions};

pub struct TracedSqlitePool {
    pool: SqlitePool,
    db_path: String,
}

impl TracedSqlitePool {
    pub async fn connect(database_url: &str) -> Result<Self, sqlx::Error> {
        let pool = SqlitePoolOptions::new()
            .max_connections(5)
            .connect(database_url)
            .await?;
        
        let db_path = database_url.replace("sqlite:", "");
        
        Ok(Self { pool, db_path })
    }
    
    #[instrument(skip(self, query))]
    pub async fn query(&self, query: &str) -> Result<Vec<sqlx::sqlite::SqliteRow>, sqlx::Error> {
        span_attributes!(
            "db.system" => "sqlite",
            "db.name" => &self.db_path,
            "db.statement" => query
        );
        
        sqlx::query(query).fetch_all(&self.pool).await
    }
}
```

---

## 7. 事务追踪

**完整事务追踪**:

```rust
use sqlx::Transaction;
use sqlx::postgres::Postgres;

impl TracedPgPool {
    /// 执行事务
    #[instrument(skip(self, f))]
    pub async fn transaction<F, T>(&self, f: F) -> Result<T, sqlx::Error>
    where
        F: for<'c> FnOnce(&'c mut Transaction<'_, Postgres>) -> 
            std::pin::Pin<Box<dyn std::future::Future<Output = Result<T, sqlx::Error>> + Send + 'c>>,
    {
        let mut tx = self.pool.begin().await?;
        
        tracing::info!("Transaction started");
        
        // 执行事务逻辑
        match f(&mut tx).await {
            Ok(result) => {
                tx.commit().await?;
                tracing::info!("Transaction committed");
                Ok(result)
            }
            Err(e) => {
                tx.rollback().await?;
                tracing::error!("Transaction rolled back: {:?}", e);
                Err(e)
            }
        }
    }
}

/// 使用示例
async fn transfer_funds(
    pool: &TracedPgPool,
    from_id: i32,
    to_id: i32,
    amount: f64,
) -> Result<(), sqlx::Error> {
    pool.transaction(|tx| {
        Box::pin(async move {
            // 扣款
            sqlx::query("UPDATE accounts SET balance = balance - $1 WHERE id = $2")
                .bind(amount)
                .bind(from_id)
                .execute(&mut **tx)
                .await?;
            
            // 入账
            sqlx::query("UPDATE accounts SET balance = balance + $1 WHERE id = $2")
                .bind(amount)
                .bind(to_id)
                .execute(&mut **tx)
                .await?;
            
            Ok(())
        })
    }).await
}
```

---

## 8. 连接池监控

**连接池指标**:

```rust
use opentelemetry::metrics::{Counter, Histogram, Meter};

pub struct PoolMetrics {
    connections_active: Histogram<u64>,
    connections_idle: Histogram<u64>,
    connection_acquire_duration: Histogram<f64>,
    queries_executed: Counter<u64>,
}

impl PoolMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            connections_active: meter
                .u64_histogram("db.connections.active")
                .with_description("Active database connections")
                .init(),
            
            connections_idle: meter
                .u64_histogram("db.connections.idle")
                .with_description("Idle database connections")
                .init(),
            
            connection_acquire_duration: meter
                .f64_histogram("db.connection.acquire_duration")
                .with_unit("ms")
                .init(),
            
            queries_executed: meter
                .u64_counter("db.queries.executed")
                .with_description("Total queries executed")
                .init(),
        }
    }
    
    pub fn record_pool_state(&self, pool: &PgPool) {
        self.connections_active.record(pool.size() as u64, &[]);
        self.connections_idle.record(pool.num_idle() as u64, &[]);
    }
}
```

---

## 9. 完整示例

**生产级应用**:

```rust
use sqlx::postgres::PgPool;
use opentelemetry::{global, KeyValue};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化 OpenTelemetry
    init_telemetry().await?;
    
    // 连接数据库
    let pool = TracedPgPool::connect("postgres://user:pass@localhost/mydb").await?;
    
    // 创建用户
    let user_id = create_user(&pool, "Alice", "alice@example.com").await?;
    println!("Created user: {}", user_id);
    
    // 查询用户
    let user = pool.get_user_by_id(user_id).await?;
    println!("User: {:?}", user);
    
    // 更新用户
    update_user(&pool, user_id, "Alice Smith").await?;
    
    // 删除用户
    delete_user(&pool, user_id).await?;
    
    // 关闭
    global::shutdown_tracer_provider();
    
    Ok(())
}

#[instrument(skip(pool))]
async fn create_user(
    pool: &TracedPgPool,
    name: &str,
    email: &str,
) -> Result<i32, sqlx::Error> {
    let row = sqlx::query(
        "INSERT INTO users (name, email) VALUES ($1, $2) RETURNING id"
    )
    .bind(name)
    .bind(email)
    .fetch_one(&pool.pool)
    .await?;
    
    Ok(row.get(0))
}

#[instrument(skip(pool))]
async fn update_user(
    pool: &TracedPgPool,
    id: i32,
    name: &str,
) -> Result<(), sqlx::Error> {
    sqlx::query("UPDATE users SET name = $1 WHERE id = $2")
        .bind(name)
        .bind(id)
        .execute(&pool.pool)
        .await?;
    
    Ok(())
}

#[instrument(skip(pool))]
async fn delete_user(pool: &TracedPgPool, id: i32) -> Result<(), sqlx::Error> {
    sqlx::query("DELETE FROM users WHERE id = $1")
        .bind(id)
        .execute(&pool.pool)
        .await?;
    
    Ok(())
}
```

---

**相关文档**:
- [HTTP追踪 Rust实现](../02_追踪属性/01_HTTP_Rust完整版.md)
- [Context Propagation](../../04_核心组件/04_Context_Propagation详解_Rust完整版.md)

**文档状态**: ✅ 完成  
**最后更新**: 2025年10月9日
