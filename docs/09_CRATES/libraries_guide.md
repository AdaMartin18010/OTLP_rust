# 📚 Libraries Crate 使用指南

**版本**: 1.0
**定位**: Rust生态成熟的常用开源库的介绍、封装和示例
**最后更新**: 2025年10月26日
**状态**: 🟢 活跃维护

> **简介**: Libraries Crate 使用指南 - Rust 生态常用开源库的集成和示例。

---

## 📋 目录

- [📚 Libraries Crate 使用指南](#-libraries-crate-使用指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [核心功能](#核心功能)
    - [📦 支持的库分类](#-支持的库分类)
  - [快速开始](#快速开始)
    - [安装依赖](#安装依赖)
    - [基础示例](#基础示例)
  - [数据库集成](#数据库集成)
    - [PostgreSQL](#postgresql)
      - [使用 SQLx (推荐)](#使用-sqlx-推荐)
      - [使用 Diesel](#使用-diesel)
      - [使用 SeaORM](#使用-seaorm)
    - [MySQL](#mysql)
    - [SQLite](#sqlite)
    - [Redis](#redis)
    - [MongoDB](#mongodb)
  - [缓存系统](#缓存系统)
    - [Redis 缓存](#redis-缓存)
    - [Moka 内存缓存](#moka-内存缓存)
    - [DashMap 并发哈希表](#dashmap-并发哈希表)
  - [消息队列](#消息队列)
    - [Kafka](#kafka)
    - [NATS](#nats)
    - [MQTT](#mqtt)
    - [RabbitMQ](#rabbitmq)
  - [HTTP框架](#http框架)
    - [Axum](#axum)
    - [Actix-web](#actix-web)
    - [Reqwest (HTTP 客户端)](#reqwest-http-客户端)
  - [异步运行时](#异步运行时)
    - [Tokio](#tokio)
    - [async-std](#async-std)
    - [Glommio (io\_uring)](#glommio-io_uring)
  - [最佳实践](#最佳实践)
    - [数据库连接池配置](#数据库连接池配置)
    - [缓存策略](#缓存策略)
    - [消息队列重试](#消息队列重试)
    - [HTTP 超时和重试](#http-超时和重试)
    - [异步任务并发控制](#异步任务并发控制)
  - [完整文档](#完整文档)
    - [📚 详细文档](#-详细文档)
    - [📖 主要文档索引](#-主要文档索引)
    - [📦 核心库详解 (135+ 库)](#-核心库详解-135-库)
    - [🎯 示例代码](#-示例代码)
  - [🔗 相关资源](#-相关资源)
    - [项目文档](#项目文档)
    - [架构文档](#架构文档)
    - [主文档](#主文档)
  - [🤝 贡献](#-贡献)

---

## 概述

`libraries` crate 提供了 Rust 生态中成熟的常用开源库的标准化封装和使用示例。它专注于:

- ✅ **库的介绍和对比**: 详细分析各库的特性、优缺点和适用场景
- ✅ **统一的封装接口**: 提供一致的使用体验
- ✅ **生产级示例**: 可直接用于生产的代码示例
- ✅ **最佳实践**: 基于真实项目经验的使用建议

---

## 核心功能

### 📦 支持的库分类

```text
libraries/
├── 🗄️ 数据库 (database/)
│   ├── PostgreSQL (sqlx, diesel, sea-orm)
│   ├── MySQL (sqlx, diesel)
│   ├── SQLite (rusqlite, sqlx)
│   ├── Redis (redis-rs, fred)
│   └── MongoDB (mongodb)
│
├── ⚡ 缓存 (cache/)
│   ├── Redis (redis-rs)
│   ├── Moka (内存缓存)
│   └── DashMap (并发哈希表)
│
├── 📨 消息队列 (mq/)
│   ├── Kafka (rdkafka)
│   ├── NATS (nats)
│   ├── MQTT (rumqtt)
│   └── RabbitMQ (lapin)
│
├── 🌐 HTTP (http/)
│   ├── Axum (web框架)
│   ├── Actix-web (web框架)
│   ├── Reqwest (HTTP客户端)
│   └── Pingora (反向代理)
│
└── ⏱️ 运行时 (runtime/)
    ├── Tokio (异步运行时)
    ├── async-std (异步运行时)
    └── Glommio (io_uring运行时)
```

---

## 快速开始

### 安装依赖

在 `Cargo.toml` 中添加:

```toml
[dependencies]
libraries = { path = "crates/libraries" }

# 或使用特性标志选择性启用
libraries = { path = "crates/libraries", features = ["database", "cache", "mq", "http"] }
```

### 基础示例

```rust
use libraries::prelude::*;

#[tokio::main]
async fn main() -> Result<()> {
    // PostgreSQL 连接
    let db = DatabaseClient::postgres("postgresql://localhost/mydb").await?;

    // Redis 缓存
    let cache = CacheClient::redis("redis://localhost").await?;

    // Kafka 消息队列
    let mq = MqClient::kafka("localhost:9092").await?;

    // Axum Web 服务
    let app = HttpServer::axum()
        .route("/", get(handler))
        .build();

    Ok(())
}
```

---

## 数据库集成

### PostgreSQL

#### 使用 SQLx (推荐)

**特点**:

- ✅ 编译时 SQL 验证
- ✅ 异步支持
- ✅ 连接池内置
- ✅ 类型安全

**示例**:

```rust
use libraries::database::postgres::*;
use sqlx::postgres::PgPoolOptions;

#[tokio::main]
async fn main() -> Result<()> {
    // 创建连接池
    let pool = PgPoolOptions::new()
        .max_connections(20)
        .connect("postgresql://user:password@localhost/mydb")
        .await?;

    // 查询示例
    let users = sqlx::query_as::<_, User>("SELECT * FROM users WHERE active = $1")
        .bind(true)
        .fetch_all(&pool)
        .await?;

    // 事务示例
    let mut tx = pool.begin().await?;

    sqlx::query("INSERT INTO users (name, email) VALUES ($1, $2)")
        .bind("Alice")
        .bind("alice@example.com")
        .execute(&mut *tx)
        .await?;

    tx.commit().await?;

    Ok(())
}

#[derive(sqlx::FromRow)]
struct User {
    id: i32,
    name: String,
    email: String,
    active: bool,
}
```

#### 使用 Diesel

**特点**:

- ✅ 类型安全的 ORM
- ✅ 迁移工具
- ✅ 丰富的查询 DSL
- ❌ 不支持异步 (需要 diesel-async)

**示例**:

```rust
use libraries::database::postgres::diesel::*;
use diesel::prelude::*;

#[derive(Queryable, Selectable)]
#[diesel(table_name = users)]
struct User {
    id: i32,
    name: String,
    email: String,
}

fn main() -> Result<()> {
    let conn = &mut establish_connection();

    // 查询
    let results = users::table
        .filter(users::active.eq(true))
        .select(User::as_select())
        .load(conn)?;

    // 插入
    let new_user = NewUser {
        name: "Bob",
        email: "bob@example.com",
    };

    diesel::insert_into(users::table)
        .values(&new_user)
        .execute(conn)?;

    Ok(())
}
```

#### 使用 SeaORM

**特点**:

- ✅ 异步 ORM
- ✅ 关系处理强大
- ✅ 迁移工具
- ✅ 多数据库支持

**示例**:

```rust
use libraries::database::postgres::sea_orm::*;
use sea_orm::*;

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

#[tokio::main]
async fn main() -> Result<()> {
    let db = Database::connect("postgresql://localhost/mydb").await?;

    // 查询
    let users = Entity::find()
        .filter(Column::Active.eq(true))
        .all(&db)
        .await?;

    // 插入
    let user = ActiveModel {
        name: Set("Charlie".to_string()),
        email: Set("charlie@example.com".to_string()),
        ..Default::default()
    };

    user.insert(&db).await?;

    Ok(())
}
```

### MySQL

支持库: SQLx, Diesel

配置示例:

```rust
// SQLx
let pool = MySqlPoolOptions::new()
    .connect("mysql://user:password@localhost/mydb")
    .await?;

// Diesel
let conn = &mut MysqlConnection::establish("mysql://user:password@localhost/mydb")?;
```

### SQLite

支持库: rusqlite, SQLx

**轻量级本地数据库，适合**:

- 嵌入式应用
- 本地缓存
- 配置存储
- 测试环境

```rust
use rusqlite::{Connection, Result};

fn main() -> Result<()> {
    let conn = Connection::open("my_database.db")?;

    conn.execute(
        "CREATE TABLE IF NOT EXISTS users (
            id INTEGER PRIMARY KEY,
            name TEXT NOT NULL,
            email TEXT NOT NULL UNIQUE
        )",
        [],
    )?;

    conn.execute(
        "INSERT INTO users (name, email) VALUES (?1, ?2)",
        ["Alice", "alice@example.com"],
    )?;

    let mut stmt = conn.prepare("SELECT * FROM users")?;
    let users = stmt.query_map([], |row| {
        Ok(User {
            id: row.get(0)?,
            name: row.get(1)?,
            email: row.get(2)?,
        })
    })?;

    Ok(())
}
```

### Redis

支持库: redis-rs, fred

**用途**:

- 缓存
- 会话存储
- 分布式锁
- 消息队列
- 实时排行榜

```rust
use libraries::cache::redis::*;
use redis::AsyncCommands;

#[tokio::main]
async fn main() -> Result<()> {
    let client = redis::Client::open("redis://localhost")?;
    let mut conn = client.get_async_connection().await?;

    // 字符串操作
    conn.set("key", "value").await?;
    let value: String = conn.get("key").await?;

    // 设置过期时间
    conn.set_ex("session:123", "user_data", 3600).await?;

    // 哈希操作
    conn.hset("user:1", "name", "Alice").await?;
    conn.hset("user:1", "email", "alice@example.com").await?;
    let name: String = conn.hget("user:1", "name").await?;

    // 列表操作
    conn.lpush("queue", "job1").await?;
    conn.lpush("queue", "job2").await?;
    let job: String = conn.rpop("queue", None).await?;

    // 发布订阅
    let mut pubsub = conn.into_pubsub();
    pubsub.subscribe("notifications").await?;

    Ok(())
}
```

### MongoDB

支持库: mongodb

**用途**:

- 文档存储
- 灵活的数据模型
- 大数据分析
- 实时应用

```rust
use libraries::database::mongodb::*;
use mongodb::{Client, options::ClientOptions};
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize)]
struct User {
    name: String,
    email: String,
    age: i32,
}

#[tokio::main]
async fn main() -> Result<()> {
    let client_options = ClientOptions::parse("mongodb://localhost:27017").await?;
    let client = Client::with_options(client_options)?;

    let db = client.database("mydb");
    let collection = db.collection::<User>("users");

    // 插入
    let user = User {
        name: "Alice".to_string(),
        email: "alice@example.com".to_string(),
        age: 30,
    };
    collection.insert_one(user, None).await?;

    // 查询
    let filter = doc! { "age": { "$gt": 25 } };
    let users = collection.find(filter, None).await?;

    Ok(())
}
```

---

## 缓存系统

### Redis 缓存

详见 [数据库集成 - Redis](#redis)

### Moka 内存缓存

**特点**:

- ✅ 高性能并发缓存
- ✅ 多种驱逐策略 (LRU, LFU, TTL)
- ✅ 异步支持
- ✅ 零依赖

**示例**:

```rust
use libraries::cache::moka::*;
use moka::future::Cache;
use std::time::Duration;

#[tokio::main]
async fn main() {
    // 创建缓存 (最大10000个条目, TTL 60秒)
    let cache: Cache<String, String> = Cache::builder()
        .max_capacity(10_000)
        .time_to_live(Duration::from_secs(60))
        .time_to_idle(Duration::from_secs(30))
        .build();

    // 插入
    cache.insert("key".to_string(), "value".to_string()).await;

    // 获取
    if let Some(value) = cache.get(&"key".to_string()).await {
        println!("Found: {}", value);
    }

    // 带加载器
    let value = cache.try_get_with("key".to_string(), async {
        // 如果缓存未命中，执行此函数
        Ok::<String, anyhow::Error>(fetch_from_database().await?)
    }).await?;

    // 统计信息
    println!("Cache hit rate: {:.2}%", cache.weighted_size() as f64 / cache.entry_count() as f64);
}
```

### DashMap 并发哈希表

**特点**:

- ✅ 无锁并发哈希表
- ✅ 高性能读写
- ✅ 类似 std::HashMap API
- ✅ 适合高并发场景

**示例**:

```rust
use libraries::cache::dashmap::*;
use dashmap::DashMap;
use std::sync::Arc;

#[tokio::main]
async fn main() {
    let cache: Arc<DashMap<String, i32>> = Arc::new(DashMap::new());

    // 插入
    cache.insert("counter".to_string(), 0);

    // 读取
    if let Some(value) = cache.get("counter") {
        println!("Counter: {}", *value);
    }

    // 修改
    cache.alter("counter", |_, v| v + 1);

    // 多线程访问
    let handles: Vec<_> = (0..10).map(|i| {
        let cache = Arc::clone(&cache);
        tokio::spawn(async move {
            cache.insert(format!("key{}", i), i);
        })
    }).collect();

    for handle in handles {
        handle.await.unwrap();
    }

    println!("Total entries: {}", cache.len());
}
```

---

## 消息队列

### Kafka

支持库: rdkafka

**特点**:

- ✅ 高吞吐量
- ✅ 持久化
- ✅ 水平扩展
- ✅ 适合大数据流处理

**生产者示例**:

```rust
use libraries::mq::kafka::*;
use rdkafka::producer::{FutureProducer, FutureRecord};
use rdkafka::ClientConfig;

#[tokio::main]
async fn main() -> Result<()> {
    let producer: FutureProducer = ClientConfig::new()
        .set("bootstrap.servers", "localhost:9092")
        .set("message.timeout.ms", "5000")
        .create()?;

    let topic = "my-topic";
    let key = "key";
    let payload = "Hello, Kafka!";

    producer.send(
        FutureRecord::to(topic)
            .key(key)
            .payload(payload),
        Duration::from_secs(0),
    ).await?;

    Ok(())
}
```

**消费者示例**:

```rust
use rdkafka::consumer::{StreamConsumer, Consumer};
use rdkafka::{ClientConfig, Message};

#[tokio::main]
async fn main() -> Result<()> {
    let consumer: StreamConsumer = ClientConfig::new()
        .set("bootstrap.servers", "localhost:9092")
        .set("group.id", "my-group")
        .set("auto.offset.reset", "earliest")
        .create()?;

    consumer.subscribe(&["my-topic"])?;

    loop {
        match consumer.recv().await {
            Ok(msg) => {
                if let Some(payload) = msg.payload() {
                    let data = String::from_utf8_lossy(payload);
                    println!("Received: {}", data);
                }
            }
            Err(e) => eprintln!("Error: {}", e),
        }
    }
}
```

### NATS

支持库: nats

**特点**:

- ✅ 轻量级
- ✅ 低延迟
- ✅ 简单易用
- ✅ 支持 Request-Reply

**示例**:

```rust
use libraries::mq::nats::*;

#[tokio::main]
async fn main() -> Result<()> {
    let nc = async_nats::connect("localhost:4222").await?;

    // 发布
    nc.publish("my.subject", "Hello, NATS!".into()).await?;

    // 订阅
    let mut sub = nc.subscribe("my.subject").await?;

    while let Some(msg) = sub.next().await {
        let data = String::from_utf8_lossy(&msg.payload);
        println!("Received: {}", data);
    }

    // Request-Reply
    let response = nc.request("my.service", "request".into()).await?;
    println!("Response: {}", String::from_utf8_lossy(&response.payload));

    Ok(())
}
```

### MQTT

支持库: rumqtt

**特点**:

- ✅ IoT 标准协议
- ✅ QoS 支持
- ✅ 轻量级
- ✅ 适合物联网

**示例**:

```rust
use libraries::mq::mqtt::*;
use rumqttc::{AsyncClient, MqttOptions, QoS};

#[tokio::main]
async fn main() -> Result<()> {
    let mut mqttoptions = MqttOptions::new("client-id", "localhost", 1883);
    mqttoptions.set_keep_alive(Duration::from_secs(5));

    let (client, mut eventloop) = AsyncClient::new(mqttoptions, 10);

    // 订阅
    client.subscribe("my/topic", QoS::AtMostOnce).await?;

    // 发布
    client.publish("my/topic", QoS::AtLeastOnce, false, "Hello, MQTT!").await?;

    // 事件循环
    loop {
        match eventloop.poll().await {
            Ok(event) => println!("Event: {:?}", event),
            Err(e) => eprintln!("Error: {}", e),
        }
    }
}
```

### RabbitMQ

支持库: lapin

**特点**:

- ✅ 功能丰富
- ✅ 灵活的路由
- ✅ 持久化
- ✅ 消息确认

**示例**:

```rust
use libraries::mq::rabbitmq::*;
use lapin::{Connection, ConnectionProperties, options::*, types::FieldTable};

#[tokio::main]
async fn main() -> Result<()> {
    let conn = Connection::connect(
        "amqp://localhost:5672",
        ConnectionProperties::default(),
    ).await?;

    let channel = conn.create_channel().await?;

    // 声明队列
    channel.queue_declare(
        "my-queue",
        QueueDeclareOptions::default(),
        FieldTable::default(),
    ).await?;

    // 发布消息
    channel.basic_publish(
        "",
        "my-queue",
        BasicPublishOptions::default(),
        b"Hello, RabbitMQ!",
        BasicProperties::default(),
    ).await?;

    // 消费消息
    let consumer = channel.basic_consume(
        "my-queue",
        "my-consumer",
        BasicConsumeOptions::default(),
        FieldTable::default(),
    ).await?;

    Ok(())
}
```

---

## HTTP框架

### Axum

**特点**:

- ✅ 基于 Tower
- ✅ 类型安全
- ✅ 优秀的错误处理
- ✅ 性能优异

**示例**:

```rust
use libraries::http::axum::*;
use axum::{
    routing::{get, post},
    Router, Json, extract::Path,
};
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
struct User {
    id: u64,
    name: String,
}

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/", get(|| async { "Hello, Axum!" }))
        .route("/users/:id", get(get_user))
        .route("/users", post(create_user));

    let listener = tokio::net::TcpListener::bind("127.0.0.1:3000")
        .await
        .unwrap();

    axum::serve(listener, app).await.unwrap();
}

async fn get_user(Path(id): Path<u64>) -> Json<User> {
    Json(User {
        id,
        name: "Alice".to_string(),
    })
}

async fn create_user(Json(user): Json<User>) -> Json<User> {
    // 保存用户...
    Json(user)
}
```

### Actix-web

**特点**:

- ✅ Actor 模型
- ✅ 成熟稳定
- ✅ 功能丰富
- ✅ 高性能

**示例**:

```rust
use libraries::http::actix_web::*;
use actix_web::{get, post, web, App, HttpResponse, HttpServer, Responder};

#[get("/")]
async fn hello() -> impl Responder {
    HttpResponse::Ok().body("Hello, Actix-web!")
}

#[get("/users/{id}")]
async fn get_user(path: web::Path<u64>) -> impl Responder {
    let id = path.into_inner();
    HttpResponse::Ok().json(User {
        id,
        name: "Alice".to_string(),
    })
}

#[post("/users")]
async fn create_user(user: web::Json<User>) -> impl Responder {
    HttpResponse::Ok().json(user.into_inner())
}

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    HttpServer::new(|| {
        App::new()
            .service(hello)
            .service(get_user)
            .service(create_user)
    })
    .bind(("127.0.0.1", 8080))?
    .run()
    .await
}
```

### Reqwest (HTTP 客户端)

**特点**:

- ✅ 易用的HTTP客户端
- ✅ 异步支持
- ✅ 支持 HTTP/2
- ✅ 自动重试

**示例**:

```rust
use libraries::http::reqwest::*;
use reqwest::Client;
use serde::Deserialize;

#[derive(Deserialize)]
struct ApiResponse {
    data: String,
}

#[tokio::main]
async fn main() -> Result<()> {
    let client = Client::new();

    // GET 请求
    let response = client.get("https://api.example.com/data")
        .header("Authorization", "Bearer token")
        .send()
        .await?;

    let body: ApiResponse = response.json().await?;
    println!("Data: {}", body.data);

    // POST 请求
    let user = User {
        name: "Alice".to_string(),
        email: "alice@example.com".to_string(),
    };

    let response = client.post("https://api.example.com/users")
        .json(&user)
        .send()
        .await?;

    println!("Status: {}", response.status());

    Ok(())
}
```

---

## 异步运行时

### Tokio

**特点**:

- ✅ Rust 标准异步运行时
- ✅ 功能全面
- ✅ 生态丰富
- ✅ 高性能

**基础用法**:

```rust
use libraries::runtime::tokio::*;
use tokio::time::{sleep, Duration};

#[tokio::main]
async fn main() {
    // 并发执行
    let task1 = tokio::spawn(async {
        sleep(Duration::from_secs(1)).await;
        println!("Task 1 completed");
    });

    let task2 = tokio::spawn(async {
        sleep(Duration::from_secs(1)).await;
        println!("Task 2 completed");
    });

    task1.await.unwrap();
    task2.await.unwrap();

    // 超时控制
    let result = tokio::time::timeout(
        Duration::from_secs(2),
        slow_operation(),
    ).await;

    match result {
        Ok(value) => println!("Completed: {:?}", value),
        Err(_) => println!("Timeout!"),
    }

    // 通道
    let (tx, mut rx) = tokio::sync::mpsc::channel(32);

    tokio::spawn(async move {
        tx.send("message").await.unwrap();
    });

    while let Some(msg) = rx.recv().await {
        println!("Received: {}", msg);
    }
}

async fn slow_operation() -> Result<String> {
    sleep(Duration::from_secs(5)).await;
    Ok("done".to_string())
}
```

### async-std

**特点**:

- ✅ 类似标准库 API
- ✅ 简单易用
- ✅ 跨平台
- ✅ 适合新手

**示例**:

```rust
use libraries::runtime::async_std::*;
use async_std::task;
use async_std::prelude::*;

#[async_std::main]
async fn main() {
    // 并发执行
    let handle1 = task::spawn(async {
        task::sleep(Duration::from_secs(1)).await;
        println!("Task 1 completed");
    });

    let handle2 = task::spawn(async {
        task::sleep(Duration::from_secs(1)).await;
        println!("Task 2 completed");
    });

    handle1.await;
    handle2.await;

    // 通道
    let (sender, receiver) = async_std::channel::bounded(10);

    task::spawn(async move {
        sender.send("message").await.unwrap();
    });

    while let Ok(msg) = receiver.recv().await {
        println!("Received: {}", msg);
    }
}
```

### Glommio (io_uring)

**特点**:

- ✅ 基于 io_uring
- ✅ 极致性能
- ✅ 线程 per-core 模型
- ❌ 仅 Linux 5.8+

**示例**:

```rust
use libraries::runtime::glommio::*;
use glommio::{LocalExecutor, LocalExecutorBuilder};

fn main() {
    let ex = LocalExecutorBuilder::default()
        .spawn(|| async move {
            // 高性能 I/O 操作
            let file = glommio::io::open("file.txt").await.unwrap();
            let contents = glommio::io::read_to_string(&file).await.unwrap();
            println!("Contents: {}", contents);
        })
        .unwrap();

    ex.join().unwrap();
}
```

---

## 最佳实践

### 数据库连接池配置

```rust
use sqlx::postgres::PgPoolOptions;
use std::time::Duration;

let pool = PgPoolOptions::new()
    .max_connections(20)                          // 最大连接数
    .min_connections(5)                           // 最小连接数
    .acquire_timeout(Duration::from_secs(30))     // 获取连接超时
    .idle_timeout(Duration::from_secs(600))       // 空闲连接超时
    .max_lifetime(Duration::from_secs(1800))      // 连接最大生命周期
    .connect("postgresql://localhost/mydb")
    .await?;
```

### 缓存策略

```rust
use moka::future::Cache;

// 双层缓存: L1 内存 + L2 Redis
struct TwoTierCache {
    l1: Cache<String, String>,          // 内存缓存
    l2: redis::aio::MultiplexedConnection, // Redis缓存
}

impl TwoTierCache {
    async fn get(&self, key: &str) -> Option<String> {
        // 先查 L1
        if let Some(value) = self.l1.get(key).await {
            return Some(value);
        }

        // 再查 L2
        if let Ok(value) = self.l2.get::<_, String>(key).await {
            self.l1.insert(key.to_string(), value.clone()).await;
            return Some(value);
        }

        None
    }
}
```

### 消息队列重试

```rust
use rdkafka::producer::{FutureProducer, FutureRecord};

async fn send_with_retry(
    producer: &FutureProducer,
    topic: &str,
    key: &str,
    payload: &str,
    max_retries: u32,
) -> Result<()> {
    let mut attempts = 0;

    loop {
        match producer.send(
            FutureRecord::to(topic).key(key).payload(payload),
            Duration::from_secs(0),
        ).await {
            Ok(_) => return Ok(()),
            Err(e) if attempts < max_retries => {
                attempts += 1;
                tokio::time::sleep(Duration::from_millis(100 * attempts as u64)).await;
            }
            Err(e) => return Err(e.into()),
        }
    }
}
```

### HTTP 超时和重试

```rust
use reqwest::{Client, ClientBuilder};
use std::time::Duration;

let client = ClientBuilder::new()
    .timeout(Duration::from_secs(30))     // 总超时
    .connect_timeout(Duration::from_secs(10)) // 连接超时
    .pool_max_idle_per_host(10)           // 连接池大小
    .http2_prior_knowledge()              // HTTP/2
    .build()?;

// 自动重试
let response = client.get("https://api.example.com")
    .send()
    .await?
    .error_for_status()?;
```

### 异步任务并发控制

```rust
use tokio::sync::Semaphore;
use std::sync::Arc;

async fn process_with_concurrency_limit(items: Vec<Item>) -> Result<()> {
    let semaphore = Arc::new(Semaphore::new(10)); // 最多10个并发

    let tasks: Vec<_> = items.into_iter().map(|item| {
        let semaphore = Arc::clone(&semaphore);
        tokio::spawn(async move {
            let _permit = semaphore.acquire().await.unwrap();
            process_item(item).await
        })
    }).collect();

    for task in tasks {
        task.await??;
    }

    Ok(())
}
```

---

## 完整文档

### 📚 详细文档

libraries crate 包含 **248+ 篇** 详细文档，覆盖:

- **135+ 个库的详细介绍** (位于 `crates/libraries/docs/essential_crates/`)
- **5大实践指南** (数据库、缓存、消息队列、Web框架、异步运行时)
- **Rust 1.90 生态分析** (9篇深度分析)
- **完整术语表和FAQ**

访问: [crates/libraries/docs/](../../crates/libraries/docs/)

### 📖 主要文档索引

| 文档 | 说明 | 行数 |
|------|------|------|
| [主索引导航](../../crates/libraries/docs/1.1_主索引导航.md) | 完整导航、学习路径 | 1,800+ |
| [术语表](../../crates/libraries/docs/1.2_术语表.md) | 标准化术语定义 | 2,318 |
| [数据库集成指南](../../crates/libraries/docs/guides/2.1_数据库集成指南.md) | SQLx, SeaORM, Diesel | 1,238 |
| [缓存系统指南](../../crates/libraries/docs/guides/2.2_缓存系统指南.md) | Redis, Moka | 1,326 |
| [消息队列指南](../../crates/libraries/docs/guides/2.3_消息队列指南.md) | Kafka, RabbitMQ, NATS | 1,400+ |
| [Web框架指南](../../crates/libraries/docs/guides/2.4_Web框架指南.md) | Axum, Actix-web, Rocket | 1,492 |
| [异步运行时指南](../../crates/libraries/docs/guides/2.5_异步运行时指南.md) | Tokio, async-std | 1,192 |
| [Rust 1.90 特性解析](../../crates/libraries/docs/references/3.1_Rust_1.90_特性全解析.md) | 最新特性 + 迁移指南 | 1,097 |
| [开源库生态全景图](../../crates/libraries/docs/references/3.2_开源库生态全景图.md) | 250+ 库分类对比 | 1,085 |
| [库成熟度评估矩阵](../../crates/libraries/docs/references/3.3_库成熟度评估矩阵.md) | 7维度评估 + 决策树 | 978 |

### 📦 核心库详解 (135+ 库)

详细介绍位于 `crates/libraries/docs/essential_crates/`:

- **数据库**: PostgreSQL, MySQL, SQLite, Redis, MongoDB 等
- **Web**: Axum, Actix-web, Rocket, Warp 等
- **异步**: Tokio, async-std, futures 等
- **序列化**: Serde, bincode, msgpack 等
- **CLI**: clap, structopt 等
- **更多**: 日志、错误处理、测试、加密等

### 🎯 示例代码

8个完整示例位于 `crates/libraries/examples/`:

```bash
# 运行示例
cd crates/libraries

# 消息队列示例
cargo run --example message_queue

# 中间件示例
cargo run --example middleware_basic_usage
cargo run --example middleware_comprehensive_demo

# 高级示例
cargo run --example advanced_middleware_patterns
cargo run --example advanced_benchmarking_demo

# Rust 1.90 特性示例
cargo run --example rust190_features_demo
cargo run --example rust190_simple_demo

# Glommio 性能对比
cargo run --example glommio_performance_comparison
```

---

## 🔗 相关资源

### 项目文档

- [返回 Crates 总览](README.md)
- [model 使用指南](model_guide.md)
- [reliability 使用指南](reliability_guide.md)
- [otlp 使用指南](otlp_guide.md)

### 架构文档

- [架构重组计划](../CRATES_ARCHITECTURE_REORG_2025_10_26.md)
- [知识图谱](../CRATES_KNOWLEDGE_GRAPH_2025_10_26.md)
- [矩阵对比](../CRATES_MATRIX_COMPARISON_2025_10_26.md)

### 主文档

- [项目主文档](../README.md)
- [文档导航](../DOCUMENTATION_GUIDE.md)
- [快速开始](../01_GETTING_STARTED/README.md)

---

## 🤝 贡献

欢迎贡献！

1. **添加新库**: 补充更多成熟库的介绍和示例
2. **改进文档**: 完善使用指南和最佳实践
3. **提供示例**: 分享实际项目经验
4. **报告问题**: 反馈使用中的问题

详见: [贡献指南](../guides/CONTRIBUTING.md)

---

**最后更新**: 2025年10月26日
**文档版本**: v1.0.0
**维护状态**: 🔄 持续维护中
