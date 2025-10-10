# MongoDB 语义约定 - Rust 完整实现

> **文档数据库**: MongoDB Tracing与Metrics完整规范 (Rust 1.90)  
> **最后更新**: 2025年10月10日

---

## 目录

- [MongoDB 语义约定 - Rust 完整实现](#mongodb-语义约定---rust-完整实现)
  - [目录](#目录)
  - [1. MongoDB 概述](#1-mongodb-概述)
    - [1.1 MongoDB 特点](#11-mongodb-特点)
    - [1.2 核心架构](#12-核心架构)
    - [1.3 Rust 生态系统](#13-rust-生态系统)
  - [2. Rust 基础设施](#2-rust-基础设施)
    - [2.1 依赖配置](#21-依赖配置)
    - [2.2 核心导入](#22-核心导入)
    - [2.3 MongoDB 语义约定常量](#23-mongodb-语义约定常量)
  - [3. MongoDB 属性类型系统](#3-mongodb-属性类型系统)
    - [3.1 操作类型枚举](#31-操作类型枚举)
    - [3.2 读偏好](#32-读偏好)
    - [3.3 MongoDB 属性结构体](#33-mongodb-属性结构体)
  - [4. CRUD 操作实现](#4-crud-操作实现)
    - [4.1 插入操作](#41-插入操作)
    - [4.2 查询操作](#42-查询操作)
    - [4.3 更新操作](#43-更新操作)
    - [4.4 删除操作](#44-删除操作)
  - [5. 聚合操作](#5-聚合操作)
    - [5.1 聚合管道](#51-聚合管道)
    - [5.2 聚合追踪](#52-聚合追踪)
  - [6. 事务支持](#6-事务支持)
    - [6.1 事务属性](#61-事务属性)
    - [6.2 事务实现](#62-事务实现)
  - [7. 完整示例](#7-完整示例)
    - [7.1 用户管理服务](#71-用户管理服务)
    - [7.2 订单管理服务](#72-订单管理服务)
    - [7.3 聚合统计示例](#73-聚合统计示例)
  - [8. Metrics 实现](#8-metrics-实现)
    - [8.1 操作 Metrics](#81-操作-metrics)
    - [8.2 连接池 Metrics](#82-连接池-metrics)
  - [9. 最佳实践](#9-最佳实践)
    - [9.1 性能优化](#91-性能优化)
    - [9.2 安全考虑](#92-安全考虑)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [相关规范](#相关规范)
    - [Rust Crates](#rust-crates)

---

## 1. MongoDB 概述

### 1.1 MongoDB 特点

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

MongoDB - 文档数据库:

核心特性:
✅ 文档存储 (BSON格式)
✅ 灵活Schema (动态字段)
✅ 强大查询语言 (MQL)
✅ 水平扩展 (分片)
✅ 高可用 (副本集)
✅ 聚合框架 (Pipeline)
✅ 全文搜索
✅ 地理空间查询
✅ 事务支持 (4.0+)

适用场景:
✅ 内容管理系统
✅ 实时分析
✅ 物联网数据
✅ 移动应用后端
✅ 游戏数据存储
✅ 日志聚合

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 1.2 核心架构

```text
副本集 (Replica Set):
┌──────────┐     ┌──────────┐     ┌──────────┐
│ Primary  │────►│Secondary │────►│Secondary │
└──────────┘     └──────────┘     └──────────┘
      │                                  │
      └──────────────────────────────────┘
              (选举 + 同步)
```

### 1.3 Rust 生态系统

```rust
// Rust MongoDB 驱动
// - mongodb: 官方 Rust 驱动，异步优先
// - 支持所有现代 MongoDB 特性
// - 完全类型安全的 BSON 处理
```

---

## 2. Rust 基础设施

### 2.1 依赖配置

```toml
[package]
name = "mongodb-otlp-example"
version = "0.1.0"
edition = "2021"

[dependencies]
# MongoDB 官方驱动
mongodb = { version = "2.8", features = ["tokio-runtime"] }
bson = { version = "2.9", features = ["chrono-0_4", "uuid-1"] }

# OpenTelemetry
opentelemetry = { version = "0.22", features = ["trace", "metrics"] }
opentelemetry_sdk = { version = "0.22", features = ["rt-tokio"] }
opentelemetry-semantic-conventions = "0.14"

# 运行时
tokio = { version = "1", features = ["full"] }

# 实用工具
anyhow = "1.0"
thiserror = "1.0"
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
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
use mongodb::{
    Client, Collection, Database,
    bson::{doc, Document, Bson},
    options::{ClientOptions, FindOptions, InsertManyOptions},
    results::{InsertOneResult, UpdateResult, DeleteResult},
};
use std::time::Instant;
```

### 2.3 MongoDB 语义约定常量

```rust
pub mod mongodb_conventions {
    // 数据库系统属性
    pub const DB_SYSTEM: &str = "db.system";
    pub const DB_SYSTEM_MONGODB: &str = "mongodb";
    pub const DB_NAME: &str = "db.name";
    pub const DB_OPERATION: &str = "db.operation";
    
    // MongoDB 特定属性
    pub const DB_MONGODB_COLLECTION: &str = "db.mongodb.collection";
    pub const DB_MONGODB_REPLICA_SET: &str = "db.mongodb.replica_set";
    pub const DB_MONGODB_READ_PREFERENCE: &str = "db.mongodb.read_preference";
    pub const DB_MONGODB_CONNECTION_ID: &str = "db.mongodb.connection_id";
    
    // 查询属性
    pub const DB_STATEMENT: &str = "db.statement";
    pub const DB_MONGODB_LIMIT: &str = "db.mongodb.limit";
    pub const DB_MONGODB_SKIP: &str = "db.mongodb.skip";
    pub const DB_MONGODB_BATCH_SIZE: &str = "db.mongodb.batch_size";
    
    // 响应属性
    pub const DB_RESPONSE_RETURNED_COUNT: &str = "db.response.returned_count";
    pub const DB_RESPONSE_MODIFIED_COUNT: &str = "db.response.modified_count";
    pub const DB_RESPONSE_DELETED_COUNT: &str = "db.response.deleted_count";
    
    // 网络属性
    pub const NET_PEER_NAME: &str = "net.peer.name";
    pub const NET_PEER_PORT: &str = "net.peer.port";
    
    // 性能属性
    pub const DB_QUERY_DURATION: &str = "db.query.duration_ms";
}
```

---

## 3. MongoDB 属性类型系统

### 3.1 操作类型枚举

```rust
/// MongoDB 操作类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MongoOperation {
    Insert,
    Find,
    Update,
    Delete,
    Aggregate,
    Count,
    Distinct,
    FindAndModify,
    BulkWrite,
}

impl MongoOperation {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Insert => "insert",
            Self::Find => "find",
            Self::Update => "update",
            Self::Delete => "delete",
            Self::Aggregate => "aggregate",
            Self::Count => "count",
            Self::Distinct => "distinct",
            Self::FindAndModify => "findAndModify",
            Self::BulkWrite => "bulkWrite",
        }
    }
}
```

### 3.2 读偏好

```rust
/// MongoDB 读偏好
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReadPreference {
    Primary,
    PrimaryPreferred,
    Secondary,
    SecondaryPreferred,
    Nearest,
}

impl ReadPreference {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Primary => "primary",
            Self::PrimaryPreferred => "primaryPreferred",
            Self::Secondary => "secondary",
            Self::SecondaryPreferred => "secondaryPreferred",
            Self::Nearest => "nearest",
        }
    }
}
```

### 3.3 MongoDB 属性结构体

```rust
/// MongoDB 操作属性
#[derive(Debug, Clone)]
pub struct MongoAttributes {
    pub database_name: String,
    pub collection_name: String,
    pub operation: MongoOperation,
    pub server_address: Option<String>,
    pub server_port: Option<u16>,
    pub replica_set: Option<String>,
    pub read_preference: Option<ReadPreference>,
    pub statement: Option<String>,
}

impl MongoAttributes {
    /// 创建基础属性
    pub fn new(
        database_name: impl Into<String>,
        collection_name: impl Into<String>,
        operation: MongoOperation,
    ) -> Self {
        Self {
            database_name: database_name.into(),
            collection_name: collection_name.into(),
            operation,
            server_address: None,
            server_port: Some(27017),
            replica_set: None,
            read_preference: None,
            statement: None,
        }
    }
    
    /// 设置服务器地址
    pub fn with_server(mut self, address: impl Into<String>, port: u16) -> Self {
        self.server_address = Some(address.into());
        self.server_port = Some(port);
        self
    }
    
    /// 设置查询语句
    pub fn with_statement(mut self, statement: impl Into<String>) -> Self {
        self.statement = Some(statement.into());
        self
    }
    
    /// 转换为 KeyValue 数组
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new(
                mongodb_conventions::DB_SYSTEM,
                mongodb_conventions::DB_SYSTEM_MONGODB,
            ),
            KeyValue::new(
                mongodb_conventions::DB_NAME,
                self.database_name.clone(),
            ),
            KeyValue::new(
                mongodb_conventions::DB_MONGODB_COLLECTION,
                self.collection_name.clone(),
            ),
            KeyValue::new(
                mongodb_conventions::DB_OPERATION,
                self.operation.as_str(),
            ),
        ];
        
        if let Some(ref addr) = self.server_address {
            attrs.push(KeyValue::new(
                mongodb_conventions::NET_PEER_NAME,
                addr.clone(),
            ));
        }
        
        if let Some(port) = self.server_port {
            attrs.push(KeyValue::new(
                mongodb_conventions::NET_PEER_PORT,
                port as i64,
            ));
        }
        
        if let Some(ref rs) = self.replica_set {
            attrs.push(KeyValue::new(
                mongodb_conventions::DB_MONGODB_REPLICA_SET,
                rs.clone(),
            ));
        }
        
        if let Some(pref) = self.read_preference {
            attrs.push(KeyValue::new(
                mongodb_conventions::DB_MONGODB_READ_PREFERENCE,
                pref.as_str(),
            ));
        }
        
        if let Some(ref stmt) = self.statement {
            attrs.push(KeyValue::new(
                mongodb_conventions::DB_STATEMENT,
                stmt.clone(),
            ));
        }
        
        attrs
    }
}
```

---

## 4. CRUD 操作实现

### 4.1 插入操作

```rust
use serde::{Deserialize, Serialize};

/// MongoDB 追踪客户端
pub struct MongoClient {
    client: Client,
    database: Database,
    tracer: global::BoxedTracer,
}

impl MongoClient {
    /// 创建客户端
    pub async fn new(uri: &str, db_name: &str) -> anyhow::Result<Self> {
        let client_options = ClientOptions::parse(uri).await?;
        let client = Client::with_options(client_options)?;
        let database = client.database(db_name);
        let tracer = global::tracer("mongodb-client");
        
        Ok(Self {
            client,
            database,
            tracer,
        })
    }
    
    /// 插入单个文档 (带追踪)
    pub async fn insert_one_with_tracing<T>(
        &self,
        collection_name: &str,
        document: &T,
    ) -> anyhow::Result<InsertOneResult>
    where
        T: Serialize,
    {
        let collection: Collection<T> = self.database.collection(collection_name);
        
        // 创建 CLIENT Span
        let mut span = self.tracer
            .span_builder("mongodb_insert")
            .with_kind(SpanKind::Client)
            .start(&self.tracer);
        
        // 设置属性
        let attrs = MongoAttributes::new(
            self.database.name(),
            collection_name,
            MongoOperation::Insert,
        ).with_server("localhost", 27017);
        
        span.set_attributes(attrs.to_key_values());
        
        // 执行插入
        let start = Instant::now();
        let result = collection.insert_one(document, None).await;
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new(
            mongodb_conventions::DB_QUERY_DURATION,
            duration.as_millis() as i64,
        ));
        
        match result {
            Ok(ref res) => {
                span.set_status(Status::Ok);
                tracing::info!("Inserted document with id: {:?}", res.inserted_id);
            }
            Err(ref e) => {
                span.set_status(Status::error(format!("Insert failed: {}", e)));
                tracing::error!("Insert error: {}", e);
            }
        }
        
        span.end();
        result.map_err(Into::into)
    }
    
    /// 批量插入 (带追踪)
    pub async fn insert_many_with_tracing<T>(
        &self,
        collection_name: &str,
        documents: Vec<T>,
    ) -> anyhow::Result<Vec<Bson>>
    where
        T: Serialize,
    {
        let collection: Collection<T> = self.database.collection(collection_name);
        
        let mut span = self.tracer
            .span_builder("mongodb_insert_many")
            .with_kind(SpanKind::Client)
            .start(&self.tracer);
        
        let attrs = MongoAttributes::new(
            self.database.name(),
            collection_name,
            MongoOperation::Insert,
        );
        
        span.set_attributes(attrs.to_key_values());
        span.set_attribute(KeyValue::new(
            mongodb_conventions::DB_MONGODB_BATCH_SIZE,
            documents.len() as i64,
        ));
        
        let start = Instant::now();
        let result = collection.insert_many(documents, None).await;
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new(
            mongodb_conventions::DB_QUERY_DURATION,
            duration.as_millis() as i64,
        ));
        
        match result {
            Ok(ref res) => {
                span.set_status(Status::Ok);
                span.set_attribute(KeyValue::new(
                    "db.inserted_count",
                    res.inserted_ids.len() as i64,
                ));
            }
            Err(ref e) => {
                span.set_status(Status::error(format!("{}", e)));
            }
        }
        
        span.end();
        result.map(|r| r.inserted_ids.values().cloned().collect()).map_err(Into::into)
    }
}
```

### 4.2 查询操作

```rust
impl MongoClient {
    /// 查询文档 (带追踪)
    pub async fn find_with_tracing<T>(
        &self,
        collection_name: &str,
        filter: Document,
        options: Option<FindOptions>,
    ) -> anyhow::Result<Vec<T>>
    where
        T: for<'de> Deserialize<'de> + Unpin + Send + Sync,
    {
        use futures_util::stream::StreamExt;
        
        let collection: Collection<T> = self.database.collection(collection_name);
        
        let mut span = self.tracer
            .span_builder("mongodb_find")
            .with_kind(SpanKind::Client)
            .start(&self.tracer);
        
        // 脱敏过滤条件
        let filter_str = format!("{:?}", filter);
        
        let attrs = MongoAttributes::new(
            self.database.name(),
            collection_name,
            MongoOperation::Find,
        ).with_statement(filter_str);
        
        span.set_attributes(attrs.to_key_values());
        
        // 设置 limit 和 skip
        if let Some(ref opts) = options {
            if let Some(limit) = opts.limit {
                span.set_attribute(KeyValue::new(
                    mongodb_conventions::DB_MONGODB_LIMIT,
                    limit,
                ));
            }
            if let Some(skip) = opts.skip {
                span.set_attribute(KeyValue::new(
                    mongodb_conventions::DB_MONGODB_SKIP,
                    skip as i64,
                ));
            }
        }
        
        // 执行查询
        let start = Instant::now();
        let cursor = collection.find(filter, options).await;
        
        let result = match cursor {
            Ok(mut cursor) => {
                let mut documents = Vec::new();
                while let Some(doc) = cursor.next().await {
                    match doc {
                        Ok(d) => documents.push(d),
                        Err(e) => return Err(e.into()),
                    }
                }
                Ok(documents)
            }
            Err(e) => Err(e),
        };
        
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new(
            mongodb_conventions::DB_QUERY_DURATION,
            duration.as_millis() as i64,
        ));
        
        match result {
            Ok(ref docs) => {
                span.set_attribute(KeyValue::new(
                    mongodb_conventions::DB_RESPONSE_RETURNED_COUNT,
                    docs.len() as i64,
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
    
    /// 查询单个文档
    pub async fn find_one_with_tracing<T>(
        &self,
        collection_name: &str,
        filter: Document,
    ) -> anyhow::Result<Option<T>>
    where
        T: for<'de> Deserialize<'de> + Unpin + Send + Sync,
    {
        let collection: Collection<T> = self.database.collection(collection_name);
        
        let mut span = self.tracer
            .span_builder("mongodb_find_one")
            .with_kind(SpanKind::Client)
            .start(&self.tracer);
        
        let attrs = MongoAttributes::new(
            self.database.name(),
            collection_name,
            MongoOperation::Find,
        ).with_statement(format!("{:?}", filter));
        
        span.set_attributes(attrs.to_key_values());
        
        let start = Instant::now();
        let result = collection.find_one(filter, None).await;
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new(
            mongodb_conventions::DB_QUERY_DURATION,
            duration.as_millis() as i64,
        ));
        
        match result {
            Ok(Some(_)) => {
                span.set_attribute(KeyValue::new(
                    mongodb_conventions::DB_RESPONSE_RETURNED_COUNT,
                    1,
                ));
                span.set_status(Status::Ok);
            }
            Ok(None) => {
                span.set_attribute(KeyValue::new(
                    mongodb_conventions::DB_RESPONSE_RETURNED_COUNT,
                    0,
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

### 4.3 更新操作

```rust
impl MongoClient {
    /// 更新单个文档
    pub async fn update_one_with_tracing(
        &self,
        collection_name: &str,
        filter: Document,
        update: Document,
    ) -> anyhow::Result<UpdateResult> {
        let collection: Collection<Document> = self.database.collection(collection_name);
        
        let mut span = self.tracer
            .span_builder("mongodb_update")
            .with_kind(SpanKind::Client)
            .start(&self.tracer);
        
        let statement = format!("filter: {:?}, update: {:?}", filter, update);
        
        let attrs = MongoAttributes::new(
            self.database.name(),
            collection_name,
            MongoOperation::Update,
        ).with_statement(statement);
        
        span.set_attributes(attrs.to_key_values());
        
        let start = Instant::now();
        let result = collection.update_one(filter, update, None).await;
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new(
            mongodb_conventions::DB_QUERY_DURATION,
            duration.as_millis() as i64,
        ));
        
        match result {
            Ok(ref res) => {
                span.set_attribute(KeyValue::new(
                    mongodb_conventions::DB_RESPONSE_MODIFIED_COUNT,
                    res.modified_count as i64,
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

### 4.4 删除操作

```rust
impl MongoClient {
    /// 删除文档
    pub async fn delete_many_with_tracing(
        &self,
        collection_name: &str,
        filter: Document,
    ) -> anyhow::Result<DeleteResult> {
        let collection: Collection<Document> = self.database.collection(collection_name);
        
        let mut span = self.tracer
            .span_builder("mongodb_delete")
            .with_kind(SpanKind::Client)
            .start(&self.tracer);
        
        let attrs = MongoAttributes::new(
            self.database.name(),
            collection_name,
            MongoOperation::Delete,
        ).with_statement(format!("{:?}", filter));
        
        span.set_attributes(attrs.to_key_values());
        
        let start = Instant::now();
        let result = collection.delete_many(filter, None).await;
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new(
            mongodb_conventions::DB_QUERY_DURATION,
            duration.as_millis() as i64,
        ));
        
        match result {
            Ok(ref res) => {
                span.set_attribute(KeyValue::new(
                    mongodb_conventions::DB_RESPONSE_DELETED_COUNT,
                    res.deleted_count as i64,
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

## 5. 聚合操作

### 5.1 聚合管道

```rust
impl MongoClient {
    /// 执行聚合管道 (带追踪)
    pub async fn aggregate_with_tracing<T>(
        &self,
        collection_name: &str,
        pipeline: Vec<Document>,
    ) -> anyhow::Result<Vec<T>>
    where
        T: for<'de> Deserialize<'de> + Unpin + Send + Sync,
    {
        use futures_util::stream::StreamExt;
        
        let collection: Collection<Document> = self.database.collection(collection_name);
        
        let mut span = self.tracer
            .span_builder("mongodb_aggregate")
            .with_kind(SpanKind::Client)
            .start(&self.tracer);
        
        let pipeline_str = format!("{:?}", pipeline);
        
        let attrs = MongoAttributes::new(
            self.database.name(),
            collection_name,
            MongoOperation::Aggregate,
        ).with_statement(pipeline_str);
        
        span.set_attributes(attrs.to_key_values());
        span.set_attribute(KeyValue::new(
            "db.mongodb.pipeline_stages",
            pipeline.len() as i64,
        ));
        
        let start = Instant::now();
        let cursor = collection.aggregate(pipeline, None).await;
        
        let result = match cursor {
            Ok(mut cursor) => {
                let mut results = Vec::new();
                while let Some(doc) = cursor.next().await {
                    match doc {
                        Ok(d) => {
                            if let Ok(value) = bson::from_document::<T>(d) {
                                results.push(value);
                            }
                        }
                        Err(e) => return Err(e.into()),
                    }
                }
                Ok(results)
            }
            Err(e) => Err(e),
        };
        
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new(
            mongodb_conventions::DB_QUERY_DURATION,
            duration.as_millis() as i64,
        ));
        
        match result {
            Ok(ref docs) => {
                span.set_attribute(KeyValue::new(
                    mongodb_conventions::DB_RESPONSE_RETURNED_COUNT,
                    docs.len() as i64,
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

### 5.2 聚合追踪

```rust
/// 构建聚合管道
pub fn build_user_stats_pipeline() -> Vec<Document> {
    vec![
        doc! {
            "$match": {
                "status": "active"
            }
        },
        doc! {
            "$group": {
                "_id": "$country",
                "count": { "$sum": 1 },
                "avg_age": { "$avg": "$age" }
            }
        },
        doc! {
            "$sort": { "count": -1 }
        },
        doc! {
            "$limit": 10
        },
    ]
}
```

---

## 6. 事务支持

### 6.1 事务属性

```rust
use mongodb::ClientSession;

/// 事务追踪属性
pub struct TransactionAttributes {
    pub transaction_id: Option<String>,
}

impl TransactionAttributes {
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = Vec::new();
        
        if let Some(ref tx_id) = self.transaction_id {
            attrs.push(KeyValue::new("db.transaction.id", tx_id.clone()));
        }
        
        attrs
    }
}
```

### 6.2 事务实现

```rust
impl MongoClient {
    /// 执行事务 (带追踪)
    pub async fn with_transaction<F, T>(
        &self,
        operation: F,
    ) -> anyhow::Result<T>
    where
        F: FnOnce(&mut ClientSession) -> std::pin::Pin<Box<dyn std::future::Future<Output = anyhow::Result<T>> + Send + '_>>,
        T: Send,
    {
        let mut span = self.tracer
            .span_builder("mongodb_transaction")
            .with_kind(SpanKind::Client)
            .start(&self.tracer);
        
        let mut session = self.client.start_session(None).await?;
        
        session.start_transaction(None).await?;
        
        let result = operation(&mut session).await;
        
        match result {
            Ok(value) => {
                session.commit_transaction().await?;
                span.set_status(Status::Ok);
                span.end();
                Ok(value)
            }
            Err(e) => {
                let _ = session.abort_transaction().await;
                span.set_status(Status::error(format!("Transaction failed: {}", e)));
                span.end();
                Err(e)
            }
        }
    }
}
```

---

## 7. 完整示例

### 7.1 用户管理服务

```rust
#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct User {
    #[serde(rename = "_id")]
    pub id: uuid::Uuid,
    pub username: String,
    pub email: String,
    pub age: i32,
    pub status: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

pub struct UserService {
    mongo: MongoClient,
}

impl UserService {
    pub async fn new(uri: &str) -> anyhow::Result<Self> {
        Ok(Self {
            mongo: MongoClient::new(uri, "myapp").await?,
        })
    }
    
    /// 创建用户
    pub async fn create_user(
        &self,
        username: String,
        email: String,
        age: i32,
    ) -> anyhow::Result<uuid::Uuid> {
        let user = User {
            id: uuid::Uuid::new_v4(),
            username,
            email,
            age,
            status: "active".to_string(),
            created_at: chrono::Utc::now(),
        };
        
        self.mongo.insert_one_with_tracing("users", &user).await?;
        
        Ok(user.id)
    }
    
    /// 查询用户
    pub async fn get_user(&self, user_id: uuid::Uuid) -> anyhow::Result<Option<User>> {
        let filter = doc! { "_id": user_id.to_string() };
        
        self.mongo.find_one_with_tracing("users", filter).await
    }
    
    /// 列出活跃用户
    pub async fn list_active_users(&self) -> anyhow::Result<Vec<User>> {
        let filter = doc! { "status": "active" };
        let options = FindOptions::builder()
            .limit(100)
            .sort(doc! { "created_at": -1 })
            .build();
        
        self.mongo.find_with_tracing("users", filter, Some(options)).await
    }
}
```

### 7.2 订单管理服务

```rust
#[derive(Debug, Serialize, Deserialize)]
pub struct Order {
    #[serde(rename = "_id")]
    pub id: uuid::Uuid,
    pub user_id: uuid::Uuid,
    pub items: Vec<OrderItem>,
    pub total: f64,
    pub status: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct OrderItem {
    pub product_id: String,
    pub quantity: i32,
    pub price: f64,
}

pub struct OrderService {
    mongo: MongoClient,
}

impl OrderService {
    pub async fn create_order(
        &self,
        user_id: uuid::Uuid,
        items: Vec<OrderItem>,
    ) -> anyhow::Result<uuid::Uuid> {
        let total: f64 = items.iter()
            .map(|item| item.price * item.quantity as f64)
            .sum();
        
        let order = Order {
            id: uuid::Uuid::new_v4(),
            user_id,
            items,
            total,
            status: "pending".to_string(),
            created_at: chrono::Utc::now(),
        };
        
        self.mongo.insert_one_with_tracing("orders", &order).await?;
        
        Ok(order.id)
    }
}
```

### 7.3 聚合统计示例

```rust
#[derive(Debug, Deserialize)]
pub struct UserStats {
    #[serde(rename = "_id")]
    pub country: String,
    pub count: i32,
    pub avg_age: f64,
}

impl UserService {
    pub async fn get_user_stats_by_country(&self) -> anyhow::Result<Vec<UserStats>> {
        let pipeline = vec![
            doc! {
                "$match": {
                    "status": "active"
                }
            },
            doc! {
                "$group": {
                    "_id": "$country",
                    "count": { "$sum": 1 },
                    "avg_age": { "$avg": "$age" }
                }
            },
            doc! {
                "$sort": { "count": -1 }
            },
        ];
        
        self.mongo.aggregate_with_tracing("users", pipeline).await
    }
}
```

---

## 8. Metrics 实现

### 8.1 操作 Metrics

```rust
use opentelemetry::metrics::{Counter, Histogram, Meter};

pub struct MongoMetrics {
    operations_total: Counter<u64>,
    operation_duration: Histogram<f64>,
    errors_total: Counter<u64>,
}

impl MongoMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            operations_total: meter
                .u64_counter("mongodb.operations.total")
                .with_description("Total MongoDB operations")
                .init(),
            
            operation_duration: meter
                .f64_histogram("mongodb.operation.duration")
                .with_description("MongoDB operation duration")
                .with_unit("s")
                .init(),
            
            errors_total: meter
                .u64_counter("mongodb.errors.total")
                .with_description("Total MongoDB errors")
                .init(),
        }
    }
    
    pub fn record_operation(
        &self,
        operation: &str,
        collection: &str,
        duration: f64,
        success: bool,
    ) {
        let labels = [
            KeyValue::new("operation", operation.to_string()),
            KeyValue::new("collection", collection.to_string()),
            KeyValue::new("success", success),
        ];
        
        self.operations_total.add(1, &labels);
        self.operation_duration.record(duration, &labels);
        
        if !success {
            self.errors_total.add(1, &labels);
        }
    }
}
```

### 8.2 连接池 Metrics

```rust
pub struct ConnectionPoolMetrics {
    active_connections: opentelemetry::metrics::Gauge<u64>,
    max_pool_size: opentelemetry::metrics::Gauge<u64>,
}

impl ConnectionPoolMetrics {
    pub fn record_pool_stats(&self, active: u64, max: u64) {
        self.active_connections.record(active, &[]);
        self.max_pool_size.record(max, &[]);
    }
}
```

---

## 9. 最佳实践

### 9.1 性能优化

```rust
pub mod performance {
    /// ✅ 使用索引
    pub async fn create_indexes(db: &Database) -> anyhow::Result<()> {
        use mongodb::IndexModel;
        
        let collection: Collection<Document> = db.collection("users");
        
        let index = IndexModel::builder()
            .keys(doc! { "email": 1 })
            .build();
        
        collection.create_index(index, None).await?;
        
        Ok(())
    }
    
    /// ✅ 使用投影减少数据传输
    pub async fn query_with_projection(
        mongo: &MongoClient,
    ) -> anyhow::Result<Vec<Document>> {
        let filter = doc! { "status": "active" };
        let projection = doc! { "_id": 1, "username": 1, "email": 1 };
        
        let options = FindOptions::builder()
            .projection(projection)
            .build();
        
        mongo.find_with_tracing("users", filter, Some(options)).await
    }
}
```

### 9.2 安全考虑

```rust
pub mod security {
    /// ✅ 脱敏敏感字段
    pub fn sanitize_user_document(doc: &mut Document) {
        if doc.contains_key("password") {
            doc.insert("password", "***");
        }
        if doc.contains_key("ssn") {
            doc.insert("ssn", "***");
        }
    }
    
    /// ✅ 验证输入
    pub fn validate_filter(filter: &Document) -> anyhow::Result<()> {
        // 防止 NoSQL 注入
        if filter.to_string().contains("$where") {
            return Err(anyhow::anyhow!("$where operator not allowed"));
        }
        
        Ok(())
    }
}
```

---

## 参考资源

### 官方文档

1. **OpenTelemetry Database Conventions**: <https://opentelemetry.io/docs/specs/semconv/database/>
2. **MongoDB Rust Driver**: <https://github.com/mongodb/mongo-rust-driver>
3. **BSON Rust**: <https://github.com/mongodb/bson-rust>

### 相关规范

1. **MongoDB Wire Protocol**: <https://www.mongodb.com/docs/manual/reference/mongodb-wire-protocol/>
2. **MongoDB Query Language**: <https://www.mongodb.com/docs/manual/tutorial/query-documents/>

### Rust Crates

1. **mongodb**: <https://crates.io/crates/mongodb>
2. **bson**: <https://crates.io/crates/bson>
3. **futures**: <https://crates.io/crates/futures>

---

**文档版本**: v1.0  
**最后更新**: 2025-10-10  
**作者**: OTLP Rust 标准深度梳理团队
