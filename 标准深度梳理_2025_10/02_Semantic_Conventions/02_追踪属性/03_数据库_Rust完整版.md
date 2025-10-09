# 数据库语义约定 - Rust 完整实现

> **Rust版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **SQLx**: 0.8+  
> **SeaORM**: 0.12+  
> **Diesel**: 2.2+  
> **MongoDB**: 3.0+  
> **Redis**: 0.24+  
> **最后更新**: 2025年10月9日

---

## 目录

- [数据库语义约定 - Rust 完整实现](#数据库语义约定---rust-完整实现)
  - [目录](#目录)
  - [1. 数据库语义约定概述](#1-数据库语义约定概述)
    - [1.1 核心属性](#11-核心属性)
    - [1.2 数据库系统分类](#12-数据库系统分类)
  - [2. SQL 数据库追踪](#2-sql-数据库追踪)
    - [2.1 SQLx 集成](#21-sqlx-集成)
    - [2.2 SeaORM 集成](#22-seaorm-集成)
    - [2.3 Diesel 集成](#23-diesel-集成)
  - [3. NoSQL 数据库追踪](#3-nosql-数据库追踪)
    - [3.1 MongoDB 追踪](#31-mongodb-追踪)
    - [3.2 Redis 追踪](#32-redis-追踪)
    - [3.3 Cassandra 追踪](#33-cassandra-追踪)
  - [4. 连接池追踪](#4-连接池追踪)
  - [5. 事务追踪](#5-事务追踪)
  - [6. 性能优化](#6-性能优化)
    - [6.1 批量操作](#61-批量操作)
    - [6.2 查询缓存](#62-查询缓存)
  - [7. 完整示例](#7-完整示例)
  - [8. 最佳实践](#8-最佳实践)
    - [8.1 PII 数据脱敏](#81-pii-数据脱敏)
    - [8.2 连接池监控](#82-连接池监控)
    - [8.3 慢查询追踪](#83-慢查询追踪)
    - [8.4 Cargo.toml 配置](#84-cargotoml-配置)
  - [总结](#总结)

---

## 1. 数据库语义约定概述

### 1.1 核心属性

根据 OpenTelemetry 规范，数据库追踪需要记录以下属性：

```rust
use opentelemetry::KeyValue;
use opentelemetry_semantic_conventions::trace::{
    DB_SYSTEM,
    DB_CONNECTION_STRING,
    DB_USER,
    DB_NAME,
    DB_STATEMENT,
    DB_OPERATION,
    NET_PEER_NAME,
    NET_PEER_PORT,
};

/// 数据库 Span 属性构建器
#[derive(Debug, Clone)]
pub struct DbSpanAttributes {
    /// 数据库系统 (postgresql, mysql, mongodb, redis, etc.)
    pub system: String,
    
    /// 连接字符串 (脱敏后)
    pub connection_string: Option<String>,
    
    /// 数据库用户
    pub user: Option<String>,
    
    /// 数据库名称
    pub name: Option<String>,
    
    /// SQL 语句或操作命令
    pub statement: Option<String>,
    
    /// 操作类型 (SELECT, INSERT, UPDATE, DELETE, etc.)
    pub operation: Option<String>,
    
    /// 服务器主机名
    pub peer_name: Option<String>,
    
    /// 服务器端口
    pub peer_port: Option<u16>,
}

impl DbSpanAttributes {
    /// 创建新的数据库属性构建器
    pub fn new(system: impl Into<String>) -> Self {
        Self {
            system: system.into(),
            connection_string: None,
            user: None,
            name: None,
            statement: None,
            operation: None,
            peer_name: None,
            peer_port: None,
        }
    }
    
    /// 构建 KeyValue 向量
    pub fn build(self) -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new(DB_SYSTEM, self.system),
        ];
        
        if let Some(conn) = self.connection_string {
            attrs.push(KeyValue::new(DB_CONNECTION_STRING, sanitize_connection_string(&conn)));
        }
        if let Some(user) = self.user {
            attrs.push(KeyValue::new(DB_USER, user));
        }
        if let Some(name) = self.name {
            attrs.push(KeyValue::new(DB_NAME, name));
        }
        if let Some(statement) = self.statement {
            attrs.push(KeyValue::new(DB_STATEMENT, statement));
        }
        if let Some(operation) = self.operation {
            attrs.push(KeyValue::new(DB_OPERATION, operation));
        }
        if let Some(peer_name) = self.peer_name {
            attrs.push(KeyValue::new(NET_PEER_NAME, peer_name));
        }
        if let Some(peer_port) = self.peer_port {
            attrs.push(KeyValue::new(NET_PEER_PORT, peer_port as i64));
        }
        
        attrs
    }
}

/// 脱敏连接字符串 (移除密码)
fn sanitize_connection_string(conn_str: &str) -> String {
    // 移除密码等敏感信息
    let re = regex::Regex::new(r"password=[^&;]*").unwrap();
    re.replace_all(conn_str, "password=***").to_string()
}
```

### 1.2 数据库系统分类

```rust
/// 支持的数据库系统
#[derive(Debug, Clone, Copy)]
pub enum DatabaseSystem {
    // SQL 数据库
    PostgreSQL,
    MySQL,
    SQLite,
    MSSQL,
    Oracle,
    
    // NoSQL 数据库
    MongoDB,
    Redis,
    Cassandra,
    DynamoDB,
    Elasticsearch,
    
    // 其他
    Other,
}

impl DatabaseSystem {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::PostgreSQL => "postgresql",
            Self::MySQL => "mysql",
            Self::SQLite => "sqlite",
            Self::MSSQL => "mssql",
            Self::Oracle => "oracle",
            Self::MongoDB => "mongodb",
            Self::Redis => "redis",
            Self::Cassandra => "cassandra",
            Self::DynamoDB => "dynamodb",
            Self::Elasticsearch => "elasticsearch",
            Self::Other => "other",
        }
    }
}
```

---

## 2. SQL 数据库追踪

### 2.1 SQLx 集成

**自动追踪扩展**:

```rust
use sqlx::{PgPool, Postgres, Row};
use opentelemetry::trace::{Tracer, SpanKind, TraceContextExt};
use opentelemetry::{global, KeyValue, Context};
use anyhow::Result;

/// SQLx 数据库操作 trait
#[async_trait::async_trait]
pub trait TracedDatabase {
    async fn execute_traced(
        &self,
        query: &str,
        params: &[&str],
        cx: &Context,
    ) -> Result<()>;
    
    async fn fetch_one_traced<T>(
        &self,
        query: &str,
        params: &[&str],
        cx: &Context,
    ) -> Result<T>
    where
        T: for<'r> sqlx::FromRow<'r, sqlx::postgres::PgRow> + Send + Unpin;
}

#[async_trait::async_trait]
impl TracedDatabase for PgPool {
    async fn execute_traced(
        &self,
        query: &str,
        params: &[&str],
        cx: &Context,
    ) -> Result<()> {
        let tracer = global::tracer("sqlx");
        
        let mut span = tracer
            .span_builder("db.execute")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new(DB_SYSTEM, "postgresql"),
                KeyValue::new(DB_STATEMENT, query.to_string()),
                KeyValue::new(DB_OPERATION, extract_operation(query)),
            ])
            .start_with_context(&tracer, cx);
        
        let cx = cx.with_span(span.clone());
        
        // 执行查询
        let result = sqlx::query(query)
            .execute(self)
            .await;
        
        // 记录结果
        match &result {
            Ok(result) => {
                span.set_attribute(KeyValue::new("db.rows_affected", result.rows_affected() as i64));
            }
            Err(e) => {
                span.record_error(e);
                span.set_status(opentelemetry::trace::Status::error(e.to_string()));
            }
        }
        
        span.end();
        result?;
        Ok(())
    }
    
    async fn fetch_one_traced<T>(
        &self,
        query: &str,
        params: &[&str],
        cx: &Context,
    ) -> Result<T>
    where
        T: for<'r> sqlx::FromRow<'r, sqlx::postgres::PgRow> + Send + Unpin,
    {
        let tracer = global::tracer("sqlx");
        
        let mut span = tracer
            .span_builder("db.query")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new(DB_SYSTEM, "postgresql"),
                KeyValue::new(DB_STATEMENT, query.to_string()),
                KeyValue::new(DB_OPERATION, "SELECT"),
            ])
            .start_with_context(&tracer, cx);
        
        let cx = cx.with_span(span.clone());
        
        // 执行查询
        let result = sqlx::query_as::<_, T>(query)
            .fetch_one(self)
            .await;
        
        match &result {
            Ok(_) => {
                span.set_attribute(KeyValue::new("db.rows_affected", 1i64));
            }
            Err(e) => {
                span.record_error(e);
                span.set_status(opentelemetry::trace::Status::error(e.to_string()));
            }
        }
        
        span.end();
        Ok(result?)
    }
}

/// 从 SQL 语句提取操作类型
fn extract_operation(sql: &str) -> String {
    let sql_upper = sql.trim().to_uppercase();
    if sql_upper.starts_with("SELECT") {
        "SELECT".to_string()
    } else if sql_upper.starts_with("INSERT") {
        "INSERT".to_string()
    } else if sql_upper.starts_with("UPDATE") {
        "UPDATE".to_string()
    } else if sql_upper.starts_with("DELETE") {
        "DELETE".to_string()
    } else if sql_upper.starts_with("CREATE") {
        "CREATE".to_string()
    } else {
        "OTHER".to_string()
    }
}

/// 使用示例
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化 OpenTelemetry
    let tracer = init_tracer()?;
    
    // 创建数据库连接池
    let pool = PgPool::connect("postgres://user:pass@localhost/mydb").await?;
    
    // 在 span 中执行数据库操作
    let cx = Context::current();
    let span = tracer.start_with_context("user.create", &cx);
    let cx = cx.with_span(span);
    
    pool.execute_traced(
        "INSERT INTO users (name, email) VALUES ($1, $2)",
        &["Alice", "alice@example.com"],
        &cx,
    ).await?;
    
    Ok(())
}
```

### 2.2 SeaORM 集成

**实体模型追踪**:

```rust
use sea_orm::*;
use opentelemetry::trace::{Tracer, SpanKind, TraceContextExt};
use opentelemetry::{global, KeyValue};

/// 用户实体
#[derive(Clone, Debug, PartialEq, DeriveEntityModel)]
#[sea_orm(table_name = "users")]
pub struct Model {
    #[sea_orm(primary_key)]
    pub id: i32,
    pub name: String,
    pub email: String,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}

/// 带追踪的数据库操作
pub struct TracedDb {
    db: DatabaseConnection,
}

impl TracedDb {
    pub fn new(db: DatabaseConnection) -> Self {
        Self { db }
    }
    
    /// 插入用户 (带追踪)
    pub async fn insert_user(&self, name: String, email: String) -> Result<Model, DbErr> {
        let tracer = global::tracer("sea-orm");
        let cx = Context::current();
        
        let mut span = tracer
            .span_builder("db.insert_user")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new(DB_SYSTEM, "postgresql"),
                KeyValue::new(DB_OPERATION, "INSERT"),
                KeyValue::new("db.table", "users"),
            ])
            .start_with_context(&tracer, &cx);
        
        let user = user::ActiveModel {
            name: Set(name),
            email: Set(email),
            ..Default::default()
        };
        
        let result = user.insert(&self.db).await;
        
        match &result {
            Ok(model) => {
                span.set_attribute(KeyValue::new("db.user_id", model.id as i64));
            }
            Err(e) => {
                span.record_error(e);
                span.set_status(opentelemetry::trace::Status::error(e.to_string()));
            }
        }
        
        span.end();
        result
    }
    
    /// 查询用户 (带追踪)
    pub async fn find_user_by_email(&self, email: &str) -> Result<Option<Model>, DbErr> {
        let tracer = global::tracer("sea-orm");
        let cx = Context::current();
        
        let mut span = tracer
            .span_builder("db.find_user")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new(DB_SYSTEM, "postgresql"),
                KeyValue::new(DB_OPERATION, "SELECT"),
                KeyValue::new("db.table", "users"),
                KeyValue::new("db.where", format!("email = '{}'", email)),
            ])
            .start_with_context(&tracer, &cx);
        
        let result = User::find()
            .filter(user::Column::Email.eq(email))
            .one(&self.db)
            .await;
        
        match &result {
            Ok(Some(_)) => {
                span.set_attribute(KeyValue::new("db.found", true));
            }
            Ok(None) => {
                span.set_attribute(KeyValue::new("db.found", false));
            }
            Err(e) => {
                span.record_error(e);
                span.set_status(opentelemetry::trace::Status::error(e.to_string()));
            }
        }
        
        span.end();
        result
    }
}
```

### 2.3 Diesel 集成

**连接池和查询追踪**:

```rust
use diesel::prelude::*;
use diesel::pg::PgConnection;
use diesel::r2d2::{self, ConnectionManager};
use opentelemetry::trace::{Tracer, SpanKind, TraceContextExt};
use opentelemetry::{global, KeyValue};

/// Diesel 连接池类型
pub type DbPool = r2d2::Pool<ConnectionManager<PgConnection>>;

/// 用户 schema
table! {
    users (id) {
        id -> Int4,
        name -> Varchar,
        email -> Varchar,
    }
}

#[derive(Queryable, Insertable, Debug)]
#[diesel(table_name = users)]
pub struct User {
    pub id: i32,
    pub name: String,
    pub email: String,
}

#[derive(Insertable, Debug)]
#[diesel(table_name = users)]
pub struct NewUser {
    pub name: String,
    pub email: String,
}

/// 带追踪的 Diesel 操作
pub struct TracedDiesel {
    pool: DbPool,
}

impl TracedDiesel {
    pub fn new(pool: DbPool) -> Self {
        Self { pool }
    }
    
    /// 插入用户 (带追踪)
    pub fn insert_user(&self, new_user: NewUser) -> Result<User, diesel::result::Error> {
        let tracer = global::tracer("diesel");
        let cx = Context::current();
        
        let mut span = tracer
            .span_builder("db.insert_user")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new(DB_SYSTEM, "postgresql"),
                KeyValue::new(DB_OPERATION, "INSERT"),
                KeyValue::new("db.table", "users"),
            ])
            .start_with_context(&tracer, &cx);
        
        let mut conn = self.pool.get().unwrap();
        
        let result = diesel::insert_into(users::table)
            .values(&new_user)
            .get_result::<User>(&mut conn);
        
        match &result {
            Ok(user) => {
                span.set_attribute(KeyValue::new("db.user_id", user.id as i64));
            }
            Err(e) => {
                span.record_error(e);
                span.set_status(opentelemetry::trace::Status::error(e.to_string()));
            }
        }
        
        span.end();
        result
    }
    
    /// 查询所有用户 (带追踪)
    pub fn find_all_users(&self) -> Result<Vec<User>, diesel::result::Error> {
        let tracer = global::tracer("diesel");
        let cx = Context::current();
        
        let mut span = tracer
            .span_builder("db.find_all_users")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new(DB_SYSTEM, "postgresql"),
                KeyValue::new(DB_OPERATION, "SELECT"),
                KeyValue::new("db.table", "users"),
            ])
            .start_with_context(&tracer, &cx);
        
        let mut conn = self.pool.get().unwrap();
        
        let result = users::table.load::<User>(&mut conn);
        
        match &result {
            Ok(users) => {
                span.set_attribute(KeyValue::new("db.rows_count", users.len() as i64));
            }
            Err(e) => {
                span.record_error(e);
                span.set_status(opentelemetry::trace::Status::error(e.to_string()));
            }
        }
        
        span.end();
        result
    }
}
```

---

## 3. NoSQL 数据库追踪

### 3.1 MongoDB 追踪

```rust
use mongodb::{Client, Collection, bson::doc};
use opentelemetry::trace::{Tracer, SpanKind, TraceContextExt};
use opentelemetry::{global, KeyValue};
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct User {
    pub name: String,
    pub email: String,
}

/// 带追踪的 MongoDB 客户端
pub struct TracedMongoClient {
    client: Client,
}

impl TracedMongoClient {
    pub fn new(client: Client) -> Self {
        Self { client }
    }
    
    /// 插入文档 (带追踪)
    pub async fn insert_user(&self, db: &str, collection: &str, user: User) -> mongodb::error::Result<()> {
        let tracer = global::tracer("mongodb");
        let cx = Context::current();
        
        let mut span = tracer
            .span_builder("db.insert_document")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new(DB_SYSTEM, "mongodb"),
                KeyValue::new(DB_NAME, db.to_string()),
                KeyValue::new(DB_OPERATION, "insert"),
                KeyValue::new("db.collection", collection.to_string()),
            ])
            .start_with_context(&tracer, &cx);
        
        let coll: Collection<User> = self.client
            .database(db)
            .collection(collection);
        
        let result = coll.insert_one(user, None).await;
        
        match &result {
            Ok(result) => {
                span.set_attribute(KeyValue::new("db.inserted_id", result.inserted_id.to_string()));
            }
            Err(e) => {
                span.record_error(e);
                span.set_status(opentelemetry::trace::Status::error(e.to_string()));
            }
        }
        
        span.end();
        result.map(|_| ())
    }
    
    /// 查询文档 (带追踪)
    pub async fn find_user(&self, db: &str, collection: &str, email: &str) -> mongodb::error::Result<Option<User>> {
        let tracer = global::tracer("mongodb");
        let cx = Context::current();
        
        let mut span = tracer
            .span_builder("db.find_document")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new(DB_SYSTEM, "mongodb"),
                KeyValue::new(DB_NAME, db.to_string()),
                KeyValue::new(DB_OPERATION, "find"),
                KeyValue::new("db.collection", collection.to_string()),
            ])
            .start_with_context(&tracer, &cx);
        
        let coll: Collection<User> = self.client
            .database(db)
            .collection(collection);
        
        let result = coll.find_one(doc! { "email": email }, None).await;
        
        match &result {
            Ok(Some(_)) => {
                span.set_attribute(KeyValue::new("db.found", true));
            }
            Ok(None) => {
                span.set_attribute(KeyValue::new("db.found", false));
            }
            Err(e) => {
                span.record_error(e);
                span.set_status(opentelemetry::trace::Status::error(e.to_string()));
            }
        }
        
        span.end();
        result
    }
}
```

### 3.2 Redis 追踪

```rust
use redis::{Client, Commands, Connection};
use opentelemetry::trace::{Tracer, SpanKind, TraceContextExt};
use opentelemetry::{global, KeyValue};

/// 带追踪的 Redis 客户端
pub struct TracedRedisClient {
    client: Client,
}

impl TracedRedisClient {
    pub fn new(client: Client) -> Self {
        Self { client }
    }
    
    /// 获取连接
    pub fn get_connection(&self) -> redis::RedisResult<Connection> {
        self.client.get_connection()
    }
    
    /// SET 操作 (带追踪)
    pub fn set(&self, key: &str, value: &str) -> redis::RedisResult<()> {
        let tracer = global::tracer("redis");
        let cx = Context::current();
        
        let mut span = tracer
            .span_builder("db.redis_set")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new(DB_SYSTEM, "redis"),
                KeyValue::new(DB_OPERATION, "SET"),
                KeyValue::new("db.redis.key", key.to_string()),
            ])
            .start_with_context(&tracer, &cx);
        
        let mut conn = self.get_connection()?;
        let result: redis::RedisResult<()> = conn.set(key, value);
        
        match &result {
            Ok(_) => {
                span.set_attribute(KeyValue::new("db.success", true));
            }
            Err(e) => {
                span.record_error(e);
                span.set_status(opentelemetry::trace::Status::error(e.to_string()));
            }
        }
        
        span.end();
        result
    }
    
    /// GET 操作 (带追踪)
    pub fn get(&self, key: &str) -> redis::RedisResult<String> {
        let tracer = global::tracer("redis");
        let cx = Context::current();
        
        let mut span = tracer
            .span_builder("db.redis_get")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new(DB_SYSTEM, "redis"),
                KeyValue::new(DB_OPERATION, "GET"),
                KeyValue::new("db.redis.key", key.to_string()),
            ])
            .start_with_context(&tracer, &cx);
        
        let mut conn = self.get_connection()?;
        let result: redis::RedisResult<String> = conn.get(key);
        
        match &result {
            Ok(value) => {
                span.set_attribute(KeyValue::new("db.value_length", value.len() as i64));
            }
            Err(e) => {
                span.record_error(e);
                span.set_status(opentelemetry::trace::Status::error(e.to_string()));
            }
        }
        
        span.end();
        result
    }
}
```

### 3.3 Cassandra 追踪

```rust
use scylla::{Session, SessionBuilder};
use opentelemetry::trace::{Tracer, SpanKind, TraceContextExt};
use opentelemetry::{global, KeyValue};

/// 带追踪的 Cassandra/ScyllaDB 客户端
pub struct TracedCassandraClient {
    session: Session,
}

impl TracedCassandraClient {
    pub async fn new(uri: &str) -> Result<Self, scylla::transport::errors::NewSessionError> {
        let session = SessionBuilder::new()
            .known_node(uri)
            .build()
            .await?;
        
        Ok(Self { session })
    }
    
    /// 执行 CQL 查询 (带追踪)
    pub async fn execute_query(&self, query: &str) -> Result<(), scylla::transport::errors::QueryError> {
        let tracer = global::tracer("cassandra");
        let cx = Context::current();
        
        let mut span = tracer
            .span_builder("db.cassandra_query")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new(DB_SYSTEM, "cassandra"),
                KeyValue::new(DB_STATEMENT, query.to_string()),
                KeyValue::new(DB_OPERATION, extract_operation(query)),
            ])
            .start_with_context(&tracer, &cx);
        
        let result = self.session.query(query, &[]).await;
        
        match &result {
            Ok(_) => {
                span.set_attribute(KeyValue::new("db.success", true));
            }
            Err(e) => {
                span.record_error(e);
                span.set_status(opentelemetry::trace::Status::error(e.to_string()));
            }
        }
        
        span.end();
        result.map(|_| ())
    }
}
```

---

## 4. 连接池追踪

```rust
use deadpool_postgres::{Pool, Config};
use tokio_postgres::NoTls;
use opentelemetry::trace::{Tracer, TraceContextExt};
use opentelemetry::{global, KeyValue};

/// 带监控的连接池
pub struct MonitoredPool {
    pool: Pool,
}

impl MonitoredPool {
    pub fn new(config: Config) -> Result<Self, deadpool_postgres::BuildError> {
        let pool = config.create_pool(None, NoTls)?;
        Ok(Self { pool })
    }
    
    /// 获取连接并记录指标
    pub async fn get_connection(&self) -> Result<deadpool_postgres::Client, deadpool_postgres::PoolError> {
        let tracer = global::tracer("connection-pool");
        let cx = Context::current();
        
        let mut span = tracer
            .span_builder("pool.get_connection")
            .with_attributes(vec![
                KeyValue::new("pool.size", self.pool.status().size as i64),
                KeyValue::new("pool.available", self.pool.status().available as i64),
            ])
            .start_with_context(&tracer, &cx);
        
        let start = std::time::Instant::now();
        let result = self.pool.get().await;
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new("pool.wait_time_ms", duration.as_millis() as i64));
        
        match &result {
            Ok(_) => {
                span.set_attribute(KeyValue::new("pool.success", true));
            }
            Err(e) => {
                span.record_error(e);
                span.set_status(opentelemetry::trace::Status::error(e.to_string()));
            }
        }
        
        span.end();
        result
    }
}
```

---

## 5. 事务追踪

```rust
use sqlx::{PgPool, Postgres, Transaction};
use opentelemetry::trace::{Tracer, SpanKind, TraceContextExt};
use opentelemetry::{global, KeyValue, Context};

/// 事务追踪包装器
pub struct TracedTransaction<'a> {
    tx: Transaction<'a, Postgres>,
    span: opentelemetry::trace::BoxedSpan,
}

impl<'a> TracedTransaction<'a> {
    /// 开始新事务
    pub async fn begin(pool: &PgPool, cx: &Context) -> Result<Self, sqlx::Error> {
        let tracer = global::tracer("transaction");
        
        let span = tracer
            .span_builder("db.transaction")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new(DB_SYSTEM, "postgresql"),
                KeyValue::new("db.transaction", "begin"),
            ])
            .start_with_context(&tracer, cx);
        
        let tx = pool.begin().await?;
        
        Ok(Self { tx, span })
    }
    
    /// 提交事务
    pub async fn commit(mut self) -> Result<(), sqlx::Error> {
        self.span.set_attribute(KeyValue::new("db.transaction", "commit"));
        
        let result = self.tx.commit().await;
        
        match &result {
            Ok(_) => {
                self.span.set_attribute(KeyValue::new("db.success", true));
            }
            Err(e) => {
                self.span.record_error(e);
                self.span.set_status(opentelemetry::trace::Status::error(e.to_string()));
            }
        }
        
        self.span.end();
        result
    }
    
    /// 回滚事务
    pub async fn rollback(mut self) -> Result<(), sqlx::Error> {
        self.span.set_attribute(KeyValue::new("db.transaction", "rollback"));
        
        let result = self.tx.rollback().await;
        
        self.span.set_attribute(KeyValue::new("db.rolled_back", true));
        self.span.end();
        result
    }
    
    /// 获取底层事务引用
    pub fn transaction_mut(&mut self) -> &mut Transaction<'a, Postgres> {
        &mut self.tx
    }
}

/// 使用示例
async fn transfer_money(pool: &PgPool, from: i32, to: i32, amount: f64) -> Result<(), sqlx::Error> {
    let cx = Context::current();
    let mut tx = TracedTransaction::begin(pool, &cx).await?;
    
    // 扣款
    sqlx::query("UPDATE accounts SET balance = balance - $1 WHERE id = $2")
        .bind(amount)
        .bind(from)
        .execute(tx.transaction_mut())
        .await?;
    
    // 入账
    sqlx::query("UPDATE accounts SET balance = balance + $1 WHERE id = $2")
        .bind(amount)
        .bind(to)
        .execute(tx.transaction_mut())
        .await?;
    
    // 提交事务
    tx.commit().await
}
```

---

## 6. 性能优化

### 6.1 批量操作

```rust
use sqlx::{PgPool, Postgres};
use opentelemetry::trace::{Tracer, SpanKind, TraceContextExt};
use opentelemetry::{global, KeyValue};

/// 批量插入 (带追踪)
pub async fn batch_insert_users(
    pool: &PgPool,
    users: Vec<(String, String)>,
) -> Result<(), sqlx::Error> {
    let tracer = global::tracer("batch-insert");
    let cx = Context::current();
    
    let mut span = tracer
        .span_builder("db.batch_insert")
        .with_kind(SpanKind::Client)
        .with_attributes(vec![
            KeyValue::new(DB_SYSTEM, "postgresql"),
            KeyValue::new(DB_OPERATION, "INSERT"),
            KeyValue::new("db.batch_size", users.len() as i64),
        ])
        .start_with_context(&tracer, &cx);
    
    // 构建批量 INSERT 语句
    let mut query_builder = sqlx::QueryBuilder::<Postgres>::new(
        "INSERT INTO users (name, email) "
    );
    
    query_builder.push_values(users.iter(), |mut b, (name, email)| {
        b.push_bind(name).push_bind(email);
    });
    
    let query = query_builder.build();
    let result = query.execute(pool).await;
    
    match &result {
        Ok(result) => {
            span.set_attribute(KeyValue::new("db.rows_affected", result.rows_affected() as i64));
        }
        Err(e) => {
            span.record_error(e);
            span.set_status(opentelemetry::trace::Status::error(e.to_string()));
        }
    }
    
    span.end();
    result.map(|_| ())
}
```

### 6.2 查询缓存

```rust
use std::sync::Arc;
use dashmap::DashMap;
use opentelemetry::trace::{Tracer, TraceContextExt};
use opentelemetry::{global, KeyValue};

/// 带缓存的数据库查询
pub struct CachedQuery {
    pool: PgPool,
    cache: Arc<DashMap<String, String>>,
}

impl CachedQuery {
    pub fn new(pool: PgPool) -> Self {
        Self {
            pool,
            cache: Arc::new(DashMap::new()),
        }
    }
    
    /// 查询用户邮箱 (带缓存)
    pub async fn get_user_email(&self, user_id: i32) -> Result<String, sqlx::Error> {
        let tracer = global::tracer("cached-query");
        let cx = Context::current();
        
        let cache_key = format!("user:{}:email", user_id);
        
        // 检查缓存
        if let Some(email) = self.cache.get(&cache_key) {
            let mut span = tracer
                .span_builder("db.cache_hit")
                .with_attributes(vec![
                    KeyValue::new("cache.hit", true),
                    KeyValue::new("cache.key", cache_key.clone()),
                ])
                .start_with_context(&tracer, &cx);
            
            span.end();
            return Ok(email.clone());
        }
        
        // 缓存未命中，查询数据库
        let mut span = tracer
            .span_builder("db.cache_miss")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("cache.hit", false),
                KeyValue::new("cache.key", cache_key.clone()),
                KeyValue::new(DB_SYSTEM, "postgresql"),
            ])
            .start_with_context(&tracer, &cx);
        
        let email: (String,) = sqlx::query_as(
            "SELECT email FROM users WHERE id = $1"
        )
        .bind(user_id)
        .fetch_one(&self.pool)
        .await?;
        
        // 更新缓存
        self.cache.insert(cache_key, email.0.clone());
        
        span.end();
        Ok(email.0)
    }
}
```

---

## 7. 完整示例

```rust
use sqlx::PgPool;
use opentelemetry::{global, trace::{Tracer, TraceContextExt}, KeyValue};
use anyhow::Result;

/// 完整的数据库追踪示例
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化 OpenTelemetry
    init_tracing()?;
    
    // 创建数据库连接池
    let pool = PgPool::connect("postgres://user:pass@localhost/mydb").await?;
    
    // 创建根 span
    let tracer = global::tracer("database-example");
    let span = tracer.start("process_user");
    let cx = Context::current_with_span(span);
    
    // 插入用户
    let user_id = insert_user(&pool, "Alice", "alice@example.com", &cx).await?;
    println!("Inserted user: {}", user_id);
    
    // 查询用户
    let user = find_user(&pool, user_id, &cx).await?;
    println!("Found user: {:?}", user);
    
    // 更新用户
    update_user(&pool, user_id, "alice.smith@example.com", &cx).await?;
    println!("Updated user");
    
    // 删除用户
    delete_user(&pool, user_id, &cx).await?;
    println!("Deleted user");
    
    Ok(())
}

/// 插入用户
async fn insert_user(
    pool: &PgPool,
    name: &str,
    email: &str,
    cx: &Context,
) -> Result<i32> {
    let tracer = global::tracer("database");
    let mut span = tracer
        .span_builder("db.insert_user")
        .start_with_context(&tracer, cx);
    
    let result: (i32,) = sqlx::query_as(
        "INSERT INTO users (name, email) VALUES ($1, $2) RETURNING id"
    )
    .bind(name)
    .bind(email)
    .fetch_one(pool)
    .await?;
    
    span.set_attribute(KeyValue::new("user.id", result.0 as i64));
    span.end();
    
    Ok(result.0)
}

/// 查询用户
async fn find_user(pool: &PgPool, id: i32, cx: &Context) -> Result<(i32, String, String)> {
    let tracer = global::tracer("database");
    let mut span = tracer
        .span_builder("db.find_user")
        .start_with_context(&tracer, cx);
    
    let result: (i32, String, String) = sqlx::query_as(
        "SELECT id, name, email FROM users WHERE id = $1"
    )
    .bind(id)
    .fetch_one(pool)
    .await?;
    
    span.end();
    Ok(result)
}

/// 更新用户
async fn update_user(pool: &PgPool, id: i32, email: &str, cx: &Context) -> Result<()> {
    let tracer = global::tracer("database");
    let mut span = tracer
        .span_builder("db.update_user")
        .start_with_context(&tracer, cx);
    
    sqlx::query("UPDATE users SET email = $1 WHERE id = $2")
        .bind(email)
        .bind(id)
        .execute(pool)
        .await?;
    
    span.end();
    Ok(())
}

/// 删除用户
async fn delete_user(pool: &PgPool, id: i32, cx: &Context) -> Result<()> {
    let tracer = global::tracer("database");
    let mut span = tracer
        .span_builder("db.delete_user")
        .start_with_context(&tracer, cx);
    
    sqlx::query("DELETE FROM users WHERE id = $1")
        .bind(id)
        .execute(pool)
        .await?;
    
    span.end();
    Ok(())
}

/// 初始化追踪
fn init_tracing() -> Result<()> {
    use opentelemetry_otlp::WithExportConfig;
    
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    global::set_tracer_provider(tracer.provider().unwrap());
    
    Ok(())
}
```

---

## 8. 最佳实践

### 8.1 PII 数据脱敏

```rust
/// 脱敏敏感字段
fn sanitize_sql_statement(sql: &str) -> String {
    // 移除 WHERE 子句中的具体值
    let re = regex::Regex::new(r"WHERE\s+.*").unwrap();
    re.replace_all(sql, "WHERE ***").to_string()
}

/// 不要记录敏感数据
// ❌ 不好
span.set_attribute(KeyValue::new("user.password", password));

// ✅ 好
span.set_attribute(KeyValue::new("user.id", user_id));
```

### 8.2 连接池监控

```rust
/// 定期记录连接池指标
async fn monitor_pool_metrics(pool: &PgPool) {
    let meter = global::meter("database-pool");
    let pool_size = meter
        .u64_observable_gauge("db.pool.size")
        .with_description("Database connection pool size")
        .init();
    
    let pool_available = meter
        .u64_observable_gauge("db.pool.available")
        .with_description("Available database connections")
        .init();
    
    // 定期更新指标
    tokio::spawn(async move {
        loop {
            let status = pool.status();
            pool_size.observe(status.size as u64, &[]);
            pool_available.observe(status.available as u64, &[]);
            
            tokio::time::sleep(Duration::from_secs(10)).await;
        }
    });
}
```

### 8.3 慢查询追踪

```rust
/// 记录慢查询
async fn execute_with_slow_query_detection(
    pool: &PgPool,
    query: &str,
    threshold_ms: u64,
) -> Result<(), sqlx::Error> {
    let start = std::time::Instant::now();
    
    let result = sqlx::query(query)
        .execute(pool)
        .await;
    
    let duration = start.elapsed();
    
    if duration.as_millis() > threshold_ms as u128 {
        tracing::warn!(
            query = query,
            duration_ms = duration.as_millis(),
            "Slow query detected"
        );
    }
    
    result.map(|_| ())
}
```

### 8.4 Cargo.toml 配置

```toml
[dependencies]
# SQL 数据库
sqlx = { version = "0.8", features = ["runtime-tokio", "postgres", "macros"] }
sea-orm = { version = "0.12", features = ["sqlx-postgres", "runtime-tokio-rustls"] }
diesel = { version = "2.2", features = ["postgres", "r2d2"] }

# NoSQL 数据库
mongodb = "3.0"
redis = { version = "0.24", features = ["tokio-comp", "connection-manager"] }
scylla = "0.13"

# 连接池
deadpool-postgres = "0.14"
r2d2 = "0.8"

# OpenTelemetry
opentelemetry = "0.31"
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.24", features = ["grpc-tonic"] }
opentelemetry-semantic-conventions = "0.31"

# 异步运行时
tokio = { version = "1.47", features = ["full"] }
async-trait = "0.1"

# 工具
anyhow = "1.0"
thiserror = "2.0"
regex = "1.11"
dashmap = "6.1"
```

---

## 总结

本文档提供了 Rust 中所有主流数据库的 OpenTelemetry 追踪集成方案：

1. **SQL 数据库**: SQLx, SeaORM, Diesel
2. **NoSQL 数据库**: MongoDB, Redis, Cassandra
3. **连接池**: 监控和追踪
4. **事务**: 完整生命周期追踪
5. **性能优化**: 批量操作、查询缓存
6. **最佳实践**: PII 脱敏、慢查询检测

所有示例都基于 **Rust 1.90**、**async/await** 和最新的 OpenTelemetry SDK。

**下一步**: 查看 [消息队列追踪](../03_消息队列属性/01_Kafka_Rust.md) 和 [缓存追踪](../06_缓存属性/01_Redis_缓存追踪_Rust完整版.md)。
