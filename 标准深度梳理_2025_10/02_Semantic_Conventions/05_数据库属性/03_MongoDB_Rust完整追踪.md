# MongoDB Rust 完整追踪集成指南

## 目录

- [MongoDB Rust 完整追踪集成指南](#mongodb-rust-完整追踪集成指南)
  - [目录](#目录)
  - [一、MongoDB 架构与追踪概述](#一mongodb-架构与追踪概述)
    - [1.1 MongoDB 核心组件](#11-mongodb-核心组件)
    - [1.2 追踪目标](#12-追踪目标)
  - [二、依赖配置](#二依赖配置)
    - [2.1 Cargo.toml](#21-cargotoml)
  - [三、MongoDB 语义约定](#三mongodb-语义约定)
    - [3.1 OpenTelemetry 属性](#31-opentelemetry-属性)
  - [四、基础追踪实现](#四基础追踪实现)
    - [4.1 MongoDB 客户端包装器](#41-mongodb-客户端包装器)
  - [五、CRUD 操作追踪](#五crud-操作追踪)
    - [5.1 插入文档](#51-插入文档)
    - [5.2 查询文档](#52-查询文档)
    - [5.3 更新文档](#53-更新文档)
    - [5.4 删除文档](#54-删除文档)
  - [六、聚合管道追踪](#六聚合管道追踪)
    - [6.1 聚合操作](#61-聚合操作)
  - [七、事务追踪](#七事务追踪)
    - [7.1 事务支持](#71-事务支持)
  - [八、变更流追踪](#八变更流追踪)
    - [8.1 变更流监听](#81-变更流监听)
  - [九、连接池监控](#九连接池监控)
    - [9.1 连接池配置](#91-连接池配置)
    - [9.2 连接池指标](#92-连接池指标)
  - [十、错误处理与重试](#十错误处理与重试)
    - [10.1 重试机制](#101-重试机制)
  - [十一、性能监控](#十一性能监控)
    - [11.1 性能指标](#111-性能指标)
  - [十二、生产环境完整示例](#十二生产环境完整示例)
    - [12.1 完整应用](#121-完整应用)
    - [12.2 Docker Compose 配置](#122-docker-compose-配置)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [最佳实践](#最佳实践)
    - [性能考虑](#性能考虑)

---

## 一、MongoDB 架构与追踪概述

### 1.1 MongoDB 核心组件

````text
┌─────────────────────────────────────────┐
│         MongoDB Rust Driver             │
├─────────────────────────────────────────┤
│  - 异步操作（Tokio）                     │
│  - 连接池管理                            │
│  - BSON 序列化/反序列化                  │
│  - 事务支持                              │
│  - 变更流（Change Streams）              │
└─────────────────────────────────────────┘
         ↓           ↓           ↓
    [Connection] [Session] [Transaction]
````

### 1.2 追踪目标

- **操作级别**：CRUD、聚合、索引、事务
- **连接级别**：连接池、连接复用、超时
- **性能级别**：查询耗时、网络延迟、文档大小

---

## 二、依赖配置

### 2.1 Cargo.toml

````toml
[dependencies]
# OpenTelemetry 核心
opentelemetry = { version = "0.31.0", features = ["trace"] }
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.24.0", features = ["grpc-tonic", "trace"] }

# MongoDB
mongodb = { version = "3.2.0", features = ["bson-chrono-0_4"] }
bson = "2.15.0"

# 异步运行时
tokio = { version = "1.47.1", features = ["full"] }

# 错误处理
anyhow = "1.0"
thiserror = "2.0"

# 日志
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
````

---

## 三、MongoDB 语义约定

### 3.1 OpenTelemetry 属性

````rust
use opentelemetry::trace::{Span, SpanKind};
use opentelemetry::{global, KeyValue};

pub struct MongoSpanAttributes;

impl MongoSpanAttributes {
    /// 数据库系统
    pub const DB_SYSTEM: &'static str = "db.system";
    
    /// 数据库名称
    pub const DB_NAME: &'static str = "db.name";
    
    /// 集合名称
    pub const DB_MONGODB_COLLECTION: &'static str = "db.mongodb.collection";
    
    /// 操作类型
    pub const DB_OPERATION: &'static str = "db.operation";
    
    /// 连接字符串（去除敏感信息）
    pub const DB_CONNECTION_STRING: &'static str = "db.connection_string";
    
    /// 服务器地址
    pub const NET_PEER_NAME: &'static str = "net.peer.name";
    pub const NET_PEER_PORT: &'static str = "net.peer.port";
    
    /// 查询语句（可选，注意敏感信息）
    pub const DB_STATEMENT: &'static str = "db.statement";
    
    /// 文档数量
    pub const DB_MONGODB_DOCUMENT_COUNT: &'static str = "db.mongodb.document_count";
}
````

---

## 四、基础追踪实现

### 4.1 MongoDB 客户端包装器

````rust
use mongodb::{Client, Database, Collection};
use opentelemetry::trace::Tracer;
use std::sync::Arc;

/// 支持追踪的 MongoDB 客户端
pub struct TracedMongoClient {
    client: Client,
    tracer: Arc<dyn Tracer + Send + Sync>,
}

impl TracedMongoClient {
    pub async fn new(uri: &str) -> anyhow::Result<Self> {
        let client = Client::with_uri_str(uri).await?;
        let tracer = global::tracer("mongodb-client");
        
        Ok(Self {
            client,
            tracer: Arc::new(tracer),
        })
    }
    
    pub fn database(&self, name: &str) -> TracedDatabase {
        TracedDatabase {
            db: self.client.database(name),
            db_name: name.to_string(),
            tracer: self.tracer.clone(),
        }
    }
}

/// 支持追踪的数据库
pub struct TracedDatabase {
    db: Database,
    db_name: String,
    tracer: Arc<dyn Tracer + Send + Sync>,
}

impl TracedDatabase {
    pub fn collection<T>(&self, name: &str) -> TracedCollection<T> {
        TracedCollection {
            coll: self.db.collection::<T>(name),
            db_name: self.db_name.clone(),
            coll_name: name.to_string(),
            tracer: self.tracer.clone(),
        }
    }
}

/// 支持追踪的集合
pub struct TracedCollection<T> {
    coll: Collection<T>,
    db_name: String,
    coll_name: String,
    tracer: Arc<dyn Tracer + Send + Sync>,
}
````

---

## 五、CRUD 操作追踪

### 5.1 插入文档

````rust
use mongodb::bson::doc;
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct User {
    pub id: String,
    pub name: String,
    pub email: String,
}

impl<T: Serialize + Send + Sync> TracedCollection<T> {
    /// 插入单个文档
    pub async fn insert_one(&self, doc: impl Into<T>) -> anyhow::Result<mongodb::results::InsertOneResult> {
        let mut span = self.tracer.start("mongodb.insert_one");
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_SYSTEM, "mongodb"));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_NAME, self.db_name.clone()));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_MONGODB_COLLECTION, self.coll_name.clone()));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_OPERATION, "insert"));
        
        let start = std::time::Instant::now();
        let result = self.coll.insert_one(doc).await;
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new("db.duration_ms", duration.as_millis() as i64));
        
        match &result {
            Ok(_) => span.set_attribute(KeyValue::new("db.success", true)),
            Err(e) => {
                span.set_attribute(KeyValue::new("db.success", false));
                span.set_attribute(KeyValue::new("error.message", e.to_string()));
            }
        }
        
        result.map_err(Into::into)
    }
    
    /// 插入多个文档
    pub async fn insert_many(&self, docs: Vec<T>) -> anyhow::Result<mongodb::results::InsertManyResult> {
        let mut span = self.tracer.start("mongodb.insert_many");
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_SYSTEM, "mongodb"));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_NAME, self.db_name.clone()));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_MONGODB_COLLECTION, self.coll_name.clone()));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_OPERATION, "insert"));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_MONGODB_DOCUMENT_COUNT, docs.len() as i64));
        
        let start = std::time::Instant::now();
        let result = self.coll.insert_many(docs).await;
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new("db.duration_ms", duration.as_millis() as i64));
        
        result.map_err(Into::into)
    }
}
````

### 5.2 查询文档

````rust
use mongodb::bson::Document;
use futures::stream::TryStreamExt;

impl<T: DeserializeOwned + Unpin + Send + Sync> TracedCollection<T> {
    /// 查找单个文档
    pub async fn find_one(&self, filter: Document) -> anyhow::Result<Option<T>> {
        let mut span = self.tracer.start("mongodb.find_one");
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_SYSTEM, "mongodb"));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_NAME, self.db_name.clone()));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_MONGODB_COLLECTION, self.coll_name.clone()));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_OPERATION, "find"));
        
        let start = std::time::Instant::now();
        let result = self.coll.find_one(filter).await;
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new("db.duration_ms", duration.as_millis() as i64));
        span.set_attribute(KeyValue::new("db.found", result.as_ref().map_or(false, |r| r.is_some())));
        
        result.map_err(Into::into)
    }
    
    /// 查找多个文档
    pub async fn find(&self, filter: Document) -> anyhow::Result<Vec<T>> {
        let mut span = self.tracer.start("mongodb.find");
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_SYSTEM, "mongodb"));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_NAME, self.db_name.clone()));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_MONGODB_COLLECTION, self.coll_name.clone()));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_OPERATION, "find"));
        
        let start = std::time::Instant::now();
        let cursor = self.coll.find(filter).await?;
        let docs: Vec<T> = cursor.try_collect().await?;
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new("db.duration_ms", duration.as_millis() as i64));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_MONGODB_DOCUMENT_COUNT, docs.len() as i64));
        
        Ok(docs)
    }
}
````

### 5.3 更新文档

````rust
impl<T> TracedCollection<T> {
    /// 更新单个文档
    pub async fn update_one(
        &self,
        filter: Document,
        update: Document,
    ) -> anyhow::Result<mongodb::results::UpdateResult> {
        let mut span = self.tracer.start("mongodb.update_one");
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_SYSTEM, "mongodb"));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_NAME, self.db_name.clone()));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_MONGODB_COLLECTION, self.coll_name.clone()));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_OPERATION, "update"));
        
        let start = std::time::Instant::now();
        let result = self.coll.update_one(filter, update).await?;
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new("db.duration_ms", duration.as_millis() as i64));
        span.set_attribute(KeyValue::new("db.matched_count", result.matched_count as i64));
        span.set_attribute(KeyValue::new("db.modified_count", result.modified_count as i64));
        
        Ok(result)
    }
    
    /// 更新多个文档
    pub async fn update_many(
        &self,
        filter: Document,
        update: Document,
    ) -> anyhow::Result<mongodb::results::UpdateResult> {
        let mut span = self.tracer.start("mongodb.update_many");
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_SYSTEM, "mongodb"));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_NAME, self.db_name.clone()));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_MONGODB_COLLECTION, self.coll_name.clone()));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_OPERATION, "update"));
        
        let start = std::time::Instant::now();
        let result = self.coll.update_many(filter, update).await?;
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new("db.duration_ms", duration.as_millis() as i64));
        span.set_attribute(KeyValue::new("db.matched_count", result.matched_count as i64));
        span.set_attribute(KeyValue::new("db.modified_count", result.modified_count as i64));
        
        Ok(result)
    }
}
````

### 5.4 删除文档

````rust
impl<T> TracedCollection<T> {
    /// 删除单个文档
    pub async fn delete_one(&self, filter: Document) -> anyhow::Result<mongodb::results::DeleteResult> {
        let mut span = self.tracer.start("mongodb.delete_one");
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_SYSTEM, "mongodb"));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_NAME, self.db_name.clone()));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_MONGODB_COLLECTION, self.coll_name.clone()));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_OPERATION, "delete"));
        
        let start = std::time::Instant::now();
        let result = self.coll.delete_one(filter).await?;
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new("db.duration_ms", duration.as_millis() as i64));
        span.set_attribute(KeyValue::new("db.deleted_count", result.deleted_count as i64));
        
        Ok(result)
    }
    
    /// 删除多个文档
    pub async fn delete_many(&self, filter: Document) -> anyhow::Result<mongodb::results::DeleteResult> {
        let mut span = self.tracer.start("mongodb.delete_many");
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_SYSTEM, "mongodb"));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_NAME, self.db_name.clone()));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_MONGODB_COLLECTION, self.coll_name.clone()));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_OPERATION, "delete"));
        
        let start = std::time::Instant::now();
        let result = self.coll.delete_many(filter).await?;
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new("db.duration_ms", duration.as_millis() as i64));
        span.set_attribute(KeyValue::new("db.deleted_count", result.deleted_count as i64));
        
        Ok(result)
    }
}
````

---

## 六、聚合管道追踪

### 6.1 聚合操作

````rust
use mongodb::bson::doc;

impl<T: DeserializeOwned + Unpin + Send + Sync> TracedCollection<T> {
    /// 执行聚合管道
    pub async fn aggregate(&self, pipeline: Vec<Document>) -> anyhow::Result<Vec<Document>> {
        let mut span = self.tracer.start("mongodb.aggregate");
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_SYSTEM, "mongodb"));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_NAME, self.db_name.clone()));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_MONGODB_COLLECTION, self.coll_name.clone()));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_OPERATION, "aggregate"));
        span.set_attribute(KeyValue::new("db.pipeline_stages", pipeline.len() as i64));
        
        let start = std::time::Instant::now();
        let cursor = self.coll.aggregate(pipeline).await?;
        let docs: Vec<Document> = cursor.try_collect().await?;
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new("db.duration_ms", duration.as_millis() as i64));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_MONGODB_DOCUMENT_COUNT, docs.len() as i64));
        
        Ok(docs)
    }
}

// 使用示例
async fn example_aggregation(coll: &TracedCollection<User>) -> anyhow::Result<()> {
    let pipeline = vec![
        doc! { "$match": { "age": { "$gte": 18 } } },
        doc! { "$group": {
            "_id": "$city",
            "count": { "$sum": 1 },
            "avgAge": { "$avg": "$age" }
        }},
        doc! { "$sort": { "count": -1 } },
    ];
    
    let results = coll.aggregate(pipeline).await?;
    println!("聚合结果: {:?}", results);
    
    Ok(())
}
````

---

## 七、事务追踪

### 7.1 事务支持

````rust
use mongodb::ClientSession;
use mongodb::options::{TransactionOptions, ReadConcern, WriteConcern};

impl TracedMongoClient {
    /// 执行事务
    pub async fn with_transaction<F, T>(&self, f: F) -> anyhow::Result<T>
    where
        F: FnOnce(&mut ClientSession) -> futures::future::BoxFuture<'_, anyhow::Result<T>>,
    {
        let mut span = self.tracer.start("mongodb.transaction");
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_SYSTEM, "mongodb"));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_OPERATION, "transaction"));
        
        let mut session = self.client.start_session().await?;
        
        let options = TransactionOptions::builder()
            .read_concern(ReadConcern::snapshot())
            .write_concern(WriteConcern::majority())
            .build();
        
        session.start_transaction(options).await?;
        
        let start = std::time::Instant::now();
        let result = match f(&mut session).await {
            Ok(r) => {
                session.commit_transaction().await?;
                span.set_attribute(KeyValue::new("db.transaction_result", "committed"));
                Ok(r)
            }
            Err(e) => {
                session.abort_transaction().await?;
                span.set_attribute(KeyValue::new("db.transaction_result", "aborted"));
                span.set_attribute(KeyValue::new("error.message", e.to_string()));
                Err(e)
            }
        };
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new("db.duration_ms", duration.as_millis() as i64));
        
        result
    }
}

// 使用示例
async fn transfer_funds(client: &TracedMongoClient) -> anyhow::Result<()> {
    client.with_transaction(|session| {
        Box::pin(async move {
            let db = client.client.database("bank");
            
            // 从账户A扣款
            db.collection::<Document>("accounts")
                .update_one(
                    doc! { "account_id": "A" },
                    doc! { "$inc": { "balance": -100 } },
                )
                .session(session)
                .await?;
            
            // 向账户B加款
            db.collection::<Document>("accounts")
                .update_one(
                    doc! { "account_id": "B" },
                    doc! { "$inc": { "balance": 100 } },
                )
                .session(session)
                .await?;
            
            Ok(())
        })
    }).await
}
````

---

## 八、变更流追踪

### 8.1 变更流监听

````rust
use mongodb::change_stream::event::ChangeStreamEvent;
use futures::StreamExt;

impl<T: DeserializeOwned + Unpin + Send + Sync> TracedCollection<T> {
    /// 监听变更流
    pub async fn watch_changes(&self) -> anyhow::Result<()> {
        let mut span = self.tracer.start("mongodb.watch");
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_SYSTEM, "mongodb"));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_NAME, self.db_name.clone()));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_MONGODB_COLLECTION, self.coll_name.clone()));
        span.set_attribute(KeyValue::new(MongoSpanAttributes::DB_OPERATION, "watch"));
        
        let mut change_stream = self.coll.watch().await?;
        
        let mut event_count = 0u64;
        while let Some(event) = change_stream.next().await {
            match event {
                Ok(change) => {
                    event_count += 1;
                    
                    let mut event_span = self.tracer.start("mongodb.change_event");
                    event_span.set_attribute(KeyValue::new("db.change_type", format!("{:?}", change.operation_type)));
                    
                    tracing::info!(
                        db.name = %self.db_name,
                        collection = %self.coll_name,
                        operation = ?change.operation_type,
                        "变更事件接收"
                    );
                }
                Err(e) => {
                    tracing::error!(error = %e, "变更流错误");
                }
            }
        }
        
        span.set_attribute(KeyValue::new("db.events_processed", event_count as i64));
        
        Ok(())
    }
}
````

---

## 九、连接池监控

### 9.1 连接池配置

````rust
use mongodb::options::ClientOptions;

pub async fn create_monitored_client(uri: &str) -> anyhow::Result<TracedMongoClient> {
    let mut options = ClientOptions::parse(uri).await?;
    
    // 连接池配置
    options.max_pool_size = Some(100);
    options.min_pool_size = Some(10);
    options.connect_timeout = Some(std::time::Duration::from_secs(5));
    options.server_selection_timeout = Some(std::time::Duration::from_secs(10));
    
    let client = Client::with_options(options)?;
    
    let tracer = global::tracer("mongodb-client");
    
    Ok(TracedMongoClient {
        client,
        tracer: Arc::new(tracer),
    })
}
````

### 9.2 连接池指标

````rust
use opentelemetry::metrics::{Counter, Histogram};

pub struct MongoPoolMetrics {
    connections_created: Counter<u64>,
    connections_closed: Counter<u64>,
    connection_duration: Histogram<f64>,
}

impl MongoPoolMetrics {
    pub fn new() -> Self {
        let meter = global::meter("mongodb-pool");
        
        Self {
            connections_created: meter
                .u64_counter("mongodb.pool.connections_created")
                .with_description("连接池创建连接数")
                .build(),
            connections_closed: meter
                .u64_counter("mongodb.pool.connections_closed")
                .with_description("连接池关闭连接数")
                .build(),
            connection_duration: meter
                .f64_histogram("mongodb.pool.connection_duration")
                .with_description("连接持续时间（秒）")
                .build(),
        }
    }
    
    pub fn record_connection_created(&self) {
        self.connections_created.add(1, &[]);
    }
    
    pub fn record_connection_closed(&self, duration_secs: f64) {
        self.connections_closed.add(1, &[]);
        self.connection_duration.record(duration_secs, &[]);
    }
}
````

---

## 十、错误处理与重试

### 10.1 重试机制

````rust
use std::time::Duration;
use tokio::time::sleep;

pub async fn with_retry<F, T, E>(
    mut f: F,
    max_retries: u32,
) -> Result<T, E>
where
    F: FnMut() -> futures::future::BoxFuture<'static, Result<T, E>>,
    E: std::fmt::Display,
{
    let mut attempt = 0;
    
    loop {
        match f().await {
            Ok(result) => return Ok(result),
            Err(e) if attempt < max_retries => {
                attempt += 1;
                let backoff = Duration::from_millis(100 * 2u64.pow(attempt));
                
                tracing::warn!(
                    attempt = attempt,
                    max_retries = max_retries,
                    backoff_ms = backoff.as_millis(),
                    error = %e,
                    "MongoDB 操作失败，准备重试"
                );
                
                sleep(backoff).await;
            }
            Err(e) => {
                tracing::error!(
                    attempts = attempt + 1,
                    error = %e,
                    "MongoDB 操作失败，已达最大重试次数"
                );
                return Err(e);
            }
        }
    }
}

// 使用示例
async fn retry_insert(coll: &TracedCollection<User>, user: User) -> anyhow::Result<()> {
    with_retry(
        || {
            let coll = coll.clone();
            let user = user.clone();
            Box::pin(async move {
                coll.insert_one(user).await
            })
        },
        3,
    ).await?;
    
    Ok(())
}
````

---

## 十一、性能监控

### 11.1 性能指标

````rust
use opentelemetry::metrics::{Histogram, Counter};

pub struct MongoPerformanceMetrics {
    operation_duration: Histogram<f64>,
    operation_count: Counter<u64>,
    error_count: Counter<u64>,
    document_size: Histogram<f64>,
}

impl MongoPerformanceMetrics {
    pub fn new() -> Self {
        let meter = global::meter("mongodb-performance");
        
        Self {
            operation_duration: meter
                .f64_histogram("mongodb.operation.duration")
                .with_description("操作耗时（毫秒）")
                .with_unit("ms")
                .build(),
            operation_count: meter
                .u64_counter("mongodb.operation.count")
                .with_description("操作次数")
                .build(),
            error_count: meter
                .u64_counter("mongodb.operation.errors")
                .with_description("操作错误次数")
                .build(),
            document_size: meter
                .f64_histogram("mongodb.document.size")
                .with_description("文档大小（字节）")
                .with_unit("By")
                .build(),
        }
    }
    
    pub fn record_operation(
        &self,
        operation: &str,
        collection: &str,
        duration_ms: f64,
        success: bool,
    ) {
        let labels = &[
            KeyValue::new("operation", operation.to_string()),
            KeyValue::new("collection", collection.to_string()),
        ];
        
        self.operation_duration.record(duration_ms, labels);
        self.operation_count.add(1, labels);
        
        if !success {
            self.error_count.add(1, labels);
        }
    }
    
    pub fn record_document_size(&self, collection: &str, size_bytes: f64) {
        let labels = &[KeyValue::new("collection", collection.to_string())];
        self.document_size.record(size_bytes, labels);
    }
}
````

---

## 十二、生产环境完整示例

### 12.1 完整应用

````rust
use mongodb::bson::{doc, Document};
use opentelemetry::global;
use opentelemetry_sdk::trace::TracerProvider;
use opentelemetry_otlp::WithExportConfig;
use std::sync::Arc;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 初始化追踪
    let tracer_provider = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317"),
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    global::set_tracer_provider(tracer_provider.clone());
    
    // 初始化日志
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .init();
    
    // 创建 MongoDB 客户端
    let client = TracedMongoClient::new("mongodb://localhost:27017").await?;
    let db = client.database("myapp");
    let users = db.collection::<User>("users");
    
    // 插入用户
    let user = User {
        id: "user123".to_string(),
        name: "Alice".to_string(),
        email: "alice@example.com".to_string(),
    };
    users.insert_one(user).await?;
    
    // 查询用户
    let found = users.find_one(doc! { "id": "user123" }).await?;
    println!("找到用户: {:?}", found);
    
    // 更新用户
    users.update_one(
        doc! { "id": "user123" },
        doc! { "$set": { "name": "Alice Updated" } },
    ).await?;
    
    // 聚合查询
    let pipeline = vec![
        doc! { "$group": {
            "_id": "$city",
            "count": { "$sum": 1 }
        }},
    ];
    let agg_results = users.aggregate(pipeline).await?;
    println!("聚合结果: {:?}", agg_results);
    
    // 事务示例
    client.with_transaction(|session| {
        Box::pin(async move {
            let db = client.client.database("myapp");
            db.collection::<Document>("accounts")
                .update_one(doc! { "id": "A" }, doc! { "$inc": { "balance": -50 } })
                .session(session)
                .await?;
            db.collection::<Document>("accounts")
                .update_one(doc! { "id": "B" }, doc! { "$inc": { "balance": 50 } })
                .session(session)
                .await?;
            Ok(())
        })
    }).await?;
    
    // 优雅关闭
    global::shutdown_tracer_provider();
    
    Ok(())
}
````

### 12.2 Docker Compose 配置

````yaml
version: '3.8'

services:
  mongodb:
    image: mongo:8.0
    ports:
      - "27017:27017"
    environment:
      MONGO_INITDB_ROOT_USERNAME: admin
      MONGO_INITDB_ROOT_PASSWORD: password
    volumes:
      - mongo-data:/data/db
  
  jaeger:
    image: jaegertracing/all-in-one:1.66
    ports:
      - "4317:4317"   # OTLP gRPC
      - "16686:16686" # Jaeger UI
    environment:
      COLLECTOR_OTLP_ENABLED: "true"

volumes:
  mongo-data:
````

---

## 总结

### 核心要点

1. **完整追踪**：覆盖 CRUD、聚合、事务、变更流
2. **语义约定**：遵循 OpenTelemetry 数据库属性规范
3. **连接池**：监控连接创建、复用、超时
4. **错误处理**：重试机制、超时控制、错误记录
5. **性能优化**：批量操作、索引优化、连接复用

### 最佳实践

- 使用 `TracedCollection` 包装器自动追踪所有操作
- 为聚合管道记录阶段数量
- 事务追踪应包含提交/回滚状态
- 变更流监听应记录事件类型和数量
- 连接池配置应根据负载调整
- 生产环境启用 TLS 和认证

### 性能考虑

- 避免在高频路径上记录完整查询语句（敏感信息）
- 使用批量操作减少网络往返
- 合理设置连接池大小（max: 100, min: 10）
- 对大文档启用 `allowDiskUse` 聚合选项
- 使用索引优化查询性能

---

**文档版本**: v1.0  
**最后更新**: 2025-10-09  
**Rust 版本**: 1.90+  
**MongoDB 版本**: 3.2.0+  
**OpenTelemetry 版本**: 0.31.0+
