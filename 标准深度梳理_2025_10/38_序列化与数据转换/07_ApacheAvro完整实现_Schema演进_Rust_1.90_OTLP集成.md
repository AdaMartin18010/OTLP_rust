# Apache Avro 序列化 - Schema 演进完整实现指南

## 目录

- [1. Apache Avro 概述](#1-apache-avro-概述)
- [2. 核心架构](#2-核心架构)
- [3. 项目设置](#3-项目设置)
- [4. Schema 定义](#4-schema-定义)
- [5. 基础序列化与反序列化](#5-基础序列化与反序列化)
- [6. Schema 演进](#6-schema-演进)
- [7. Schema Registry 集成](#7-schema-registry-集成)
- [8. 高级功能](#8-高级功能)
- [9. 性能优化](#9-性能优化)
- [10. OTLP 可观测性集成](#10-otlp-可观测性集成)
- [11. 测试策略](#11-测试策略)
- [12. 生产实践](#12-生产实践)
- [13. 国际标准对齐](#13-国际标准对齐)

---

## 1. Apache Avro 概述

### 1.1 什么是 Avro?

**Apache Avro** 是一个数据序列化系统，提供：

- **丰富的数据结构**: 支持复杂嵌套类型
- **紧凑的二进制格式**: 比 JSON/XML 更高效
- **Schema 演进**: 支持向前/向后兼容
- **动态类型**: 无需代码生成即可使用
- **RPC 支持**: 内置远程过程调用

### 1.2 Avro vs 其他格式

| 特性 | Avro | Protobuf | JSON | MessagePack |
|------|------|----------|------|-------------|
| **Schema 演进** | ✅ 完整支持 | ✅ 支持 | ❌ 无 | ❌ 无 |
| **自描述** | ✅ Schema 嵌入数据 | ❌ 需额外传输 | ✅ 自描述 | ❌ 需额外定义 |
| **压缩率** | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐ |
| **代码生成** | 可选 | 必需 | 无 | 无 |
| **动态类型** | ✅ 支持 | ❌ 不支持 | ✅ 支持 | ⚠️ 有限 |
| **Kafka 集成** | ✅ 一流支持 | ⚠️ 需插件 | ✅ 原生支持 | ⚠️ 需手动集成 |

### 1.3 典型应用场景

- ✅ **大数据处理**: Hadoop, Spark, Kafka
- ✅ **事件流**: Schema Registry + Kafka
- ✅ **服务间通信**: 需要 Schema 演进的 RPC
- ✅ **长期数据存储**: 支持 Schema 版本升级

---

## 2. 核心架构

```text
┌─────────────────────────────────────────────────────────────┐
│                      Avro Schema (JSON)                     │
│  • 类型定义 (record, enum, array, map)                      │
│  • 字段默认值                                               │
│  • 文档注释                                                 │
└────────────────────────┬────────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────────┐
│                    Avro 编码/解码                            │
│  • 二进制编码 (Binary Encoder)                               │
│  • JSON 编码 (JSON Encoder)                                 │
│  • Schema 解析 (Schema Parser)                              │
└────────────────────────┬────────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────────┐
│                   Rust 数据结构                              │
│  • Serde 集成 (自动序列化/反序列化)                           │
│  • 手动编码 (GenericRecord)                                  │
└────────────────────────┬────────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────────┐
│                    应用层                                    │
│  • Kafka Producer/Consumer                                  │
│  • Schema Registry 集成                                     │
│  • OTLP 追踪                                                │
└─────────────────────────────────────────────────────────────┘
```

---

## 3. 项目设置

### 3.1 Cargo.toml

```toml
[package]
name = "avro-example"
version = "0.1.0"
edition = "2021"

[dependencies]
# Avro 库
apache-avro = { version = "0.16", features = ["derive"] }

# 序列化
serde = { version = "1", features = ["derive"] }
serde_json = "1"

# Kafka 集成
rdkafka = { version = "0.36", features = ["ssl", "tracing"] }

# 错误处理
thiserror = "1"
anyhow = "1"

# 异步运行时
tokio = { version = "1", features = ["full"] }

# 日志与追踪
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.25"

# OpenTelemetry
opentelemetry = "0.25"
opentelemetry-otlp = { version = "0.25", features = ["grpc-tonic"] }
opentelemetry_sdk = { version = "0.25", features = ["rt-tokio"] }

# HTTP 客户端 (Schema Registry)
reqwest = { version = "0.12", features = ["json"] }

[dev-dependencies]
proptest = "1"
```

---

## 4. Schema 定义

### 4.1 基础 Avro Schema (JSON)

```json
{
  "type": "record",
  "name": "User",
  "namespace": "com.example.models",
  "doc": "用户实体",
  "fields": [
    {
      "name": "id",
      "type": "string",
      "doc": "用户唯一标识 (UUID)"
    },
    {
      "name": "email",
      "type": "string",
      "doc": "电子邮件地址"
    },
    {
      "name": "name",
      "type": "string"
    },
    {
      "name": "age",
      "type": ["null", "int"],
      "default": null,
      "doc": "年龄（可选）"
    },
    {
      "name": "roles",
      "type": {
        "type": "array",
        "items": "string"
      },
      "default": []
    },
    {
      "name": "metadata",
      "type": {
        "type": "map",
        "values": "string"
      },
      "default": {}
    },
    {
      "name": "created_at",
      "type": {
        "type": "long",
        "logicalType": "timestamp-millis"
      },
      "doc": "创建时间 (Unix 时间戳)"
    }
  ]
}
```

### 4.2 Rust 结构体 (Serde 集成)

```rust
use serde::{Deserialize, Serialize};
use apache_avro::types::Value;
use apache_avro::{Schema, Writer, Reader, from_value, to_value};
use std::collections::HashMap;

/// 用户实体
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct User {
    pub id: String,
    pub email: String,
    pub name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub age: Option<i32>,
    #[serde(default)]
    pub roles: Vec<String>,
    #[serde(default)]
    pub metadata: HashMap<String, String>,
    pub created_at: i64, // Unix 时间戳 (毫秒)
}

impl User {
    pub fn new(email: String, name: String) -> Self {
        Self {
            id: uuid::Uuid::new_v4().to_string(),
            email,
            name,
            age: None,
            roles: vec!["user".to_string()],
            metadata: HashMap::new(),
            created_at: chrono::Utc::now().timestamp_millis(),
        }
    }
}
```

---

## 5. 基础序列化与反序列化

### 5.1 Schema 加载

```rust
use apache_avro::Schema;
use anyhow::Result;

/// 加载 Avro Schema
pub fn load_user_schema() -> Result<Schema> {
    let schema_json = r#"
    {
      "type": "record",
      "name": "User",
      "namespace": "com.example.models",
      "fields": [
        {"name": "id", "type": "string"},
        {"name": "email", "type": "string"},
        {"name": "name", "type": "string"},
        {"name": "age", "type": ["null", "int"], "default": null},
        {"name": "roles", "type": {"type": "array", "items": "string"}, "default": []},
        {"name": "metadata", "type": {"type": "map", "values": "string"}, "default": {}},
        {"name": "created_at", "type": {"type": "long", "logicalType": "timestamp-millis"}}
      ]
    }
    "#;

    Ok(Schema::parse_str(schema_json)?)
}
```

### 5.2 序列化

```rust
use apache_avro::{Writer, to_value};

/// 序列化用户到 Avro 二进制格式
pub fn serialize_user(user: &User) -> Result<Vec<u8>> {
    let schema = load_user_schema()?;
    let mut writer = Writer::new(&schema, Vec::new());

    // 方法 1: 使用 Serde (推荐)
    let value = to_value(user)?;
    writer.append(value)?;

    Ok(writer.into_inner()?)
}

// 使用示例
fn main() -> Result<()> {
    let user = User::new("alice@example.com".to_string(), "Alice".to_string());
    let bytes = serialize_user(&user)?;
    println!("Serialized {} bytes", bytes.len());
    Ok(())
}
```

### 5.3 反序列化

```rust
use apache_avro::{Reader, from_value};

/// 反序列化 Avro 二进制格式到用户
pub fn deserialize_user(bytes: &[u8]) -> Result<User> {
    let schema = load_user_schema()?;
    let reader = Reader::with_schema(&schema, bytes)?;

    for value in reader {
        let value = value?;
        let user: User = from_value(&value)?;
        return Ok(user);
    }

    Err(anyhow::anyhow!("No user found in Avro data"))
}

// 使用示例
fn main() -> Result<()> {
    let user = User::new("alice@example.com".to_string(), "Alice".to_string());
    let bytes = serialize_user(&user)?;
    let deserialized = deserialize_user(&bytes)?;
    
    assert_eq!(user, deserialized);
    Ok(())
}
```

---

## 6. Schema 演进

### 6.1 向后兼容（Backward Compatibility）

**旧 Schema**:

```json
{
  "type": "record",
  "name": "User",
  "fields": [
    {"name": "id", "type": "string"},
    {"name": "email", "type": "string"},
    {"name": "name", "type": "string"}
  ]
}
```

**新 Schema** (添加字段 + 默认值):

```json
{
  "type": "record",
  "name": "User",
  "fields": [
    {"name": "id", "type": "string"},
    {"name": "email", "type": "string"},
    {"name": "name", "type": "string"},
    {"name": "age", "type": ["null", "int"], "default": null},
    {"name": "roles", "type": {"type": "array", "items": "string"}, "default": []}
  ]
}
```

**测试向后兼容**:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_backward_compatibility() {
        // 使用旧 Schema 序列化
        let old_schema_json = r#"
        {
          "type": "record",
          "name": "User",
          "fields": [
            {"name": "id", "type": "string"},
            {"name": "email", "type": "string"},
            {"name": "name", "type": "string"}
          ]
        }
        "#;
        let old_schema = Schema::parse_str(old_schema_json).unwrap();
        
        let mut writer = Writer::new(&old_schema, Vec::new());
        writer.append(apache_avro::types::Record::from([
            ("id".to_string(), Value::String("123".to_string())),
            ("email".to_string(), Value::String("old@example.com".to_string())),
            ("name".to_string(), Value::String("Old User".to_string())),
        ])).unwrap();
        let old_bytes = writer.into_inner().unwrap();

        // 使用新 Schema 反序列化（应该成功）
        let new_schema = load_user_schema().unwrap();
        let reader = Reader::with_schema(&new_schema, &old_bytes[..]).unwrap();

        for value in reader {
            let value = value.unwrap();
            let user: User = from_value(&value).unwrap();
            
            // 新字段应该有默认值
            assert_eq!(user.age, None);
            assert_eq!(user.roles, Vec::<String>::new());
        }
    }
}
```

### 6.2 向前兼容（Forward Compatibility）

**规则**: 旧代码可以读取新数据

- ✅ **删除字段**: 旧代码忽略新字段
- ❌ **添加字段（无默认值）**: 不兼容

```rust
#[test]
fn test_forward_compatibility() {
    // 使用新 Schema 序列化
    let user = User {
        id: "456".to_string(),
        email: "new@example.com".to_string(),
        name: "New User".to_string(),
        age: Some(25),
        roles: vec!["admin".to_string()],
        metadata: HashMap::new(),
        created_at: chrono::Utc::now().timestamp_millis(),
    };
    let new_bytes = serialize_user(&user).unwrap();

    // 使用旧 Schema 反序列化（应该成功，忽略新字段）
    let old_schema_json = r#"
    {
      "type": "record",
      "name": "User",
      "fields": [
        {"name": "id", "type": "string"},
        {"name": "email", "type": "string"},
        {"name": "name", "type": "string"}
      ]
    }
    "#;
    let old_schema = Schema::parse_str(old_schema_json).unwrap();
    let reader = Reader::with_schema(&old_schema, &new_bytes[..]).unwrap();

    for value in reader {
        let value = value.unwrap();
        // 旧结构体应该只包含 id, email, name
        println!("{:?}", value);
    }
}
```

### 6.3 完全兼容（Full Compatibility）

同时满足向后和向前兼容：

- ✅ **添加字段（带默认值）**
- ✅ **删除字段（带默认值）**
- ❌ **修改字段类型**

---

## 7. Schema Registry 集成

### 7.1 Schema Registry 架构

```text
┌─────────────────────────────────────────────────────────────┐
│                   Kafka Producer/Consumer                   │
└────────────────────────┬────────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────────┐
│                    Schema Registry                          │
│  • 注册 Schema                                              │
│  • 获取 Schema (by ID/Subject)                              │
│  • 验证兼容性                                                │
└────────────────────────┬────────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────────┐
│                    Avro 编码/解码                            │
│  • Magic Byte (0x00)                                        │
│  • Schema ID (4 bytes)                                      │
│  • Avro Payload                                             │
└─────────────────────────────────────────────────────────────┘
```

### 7.2 Schema Registry 客户端

```rust
use reqwest::Client;
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize)]
struct RegisterSchemaRequest {
    schema: String,
}

#[derive(Debug, Deserialize)]
struct RegisterSchemaResponse {
    id: i32,
}

/// Schema Registry 客户端
pub struct SchemaRegistry {
    client: Client,
    base_url: String,
}

impl SchemaRegistry {
    pub fn new(base_url: impl Into<String>) -> Self {
        Self {
            client: Client::new(),
            base_url: base_url.into(),
        }
    }

    /// 注册 Schema
    pub async fn register_schema(
        &self,
        subject: &str,
        schema: &Schema,
    ) -> Result<i32> {
        let url = format!("{}/subjects/{}/versions", self.base_url, subject);
        
        let request = RegisterSchemaRequest {
            schema: schema.canonical_form(),
        };

        let response: RegisterSchemaResponse = self.client
            .post(&url)
            .json(&request)
            .send()
            .await?
            .json()
            .await?;

        Ok(response.id)
    }

    /// 获取 Schema (by ID)
    pub async fn get_schema_by_id(&self, schema_id: i32) -> Result<Schema> {
        let url = format!("{}/schemas/ids/{}", self.base_url, schema_id);
        
        #[derive(Deserialize)]
        struct SchemaResponse {
            schema: String,
        }

        let response: SchemaResponse = self.client
            .get(&url)
            .send()
            .await?
            .json()
            .await?;

        Ok(Schema::parse_str(&response.schema)?)
    }

    /// 获取最新 Schema (by Subject)
    pub async fn get_latest_schema(&self, subject: &str) -> Result<(i32, Schema)> {
        let url = format!("{}/subjects/{}/versions/latest", self.base_url, subject);
        
        #[derive(Deserialize)]
        struct LatestSchemaResponse {
            id: i32,
            schema: String,
        }

        let response: LatestSchemaResponse = self.client
            .get(&url)
            .send()
            .await?
            .json()
            .await?;

        Ok((response.id, Schema::parse_str(&response.schema)?))
    }
}
```

### 7.3 Kafka Producer (Schema Registry 集成)

```rust
use rdkafka::producer::{FutureProducer, FutureRecord};
use rdkafka::config::ClientConfig;

/// Avro 编码器（Schema Registry 格式）
pub struct AvroEncoder {
    registry: SchemaRegistry,
}

impl AvroEncoder {
    pub fn new(registry: SchemaRegistry) -> Self {
        Self { registry }
    }

    /// 编码消息（包含 Magic Byte + Schema ID）
    pub async fn encode(&self, subject: &str, user: &User) -> Result<Vec<u8>> {
        // 1. 获取 Schema ID
        let schema = load_user_schema()?;
        let schema_id = self.registry.register_schema(subject, &schema).await?;

        // 2. 序列化 Avro 数据
        let mut writer = Writer::new(&schema, Vec::new());
        writer.append(to_value(user)?)?;
        let avro_bytes = writer.into_inner()?;

        // 3. 组装消息: Magic Byte (0x00) + Schema ID (4 bytes) + Avro Payload
        let mut message = Vec::new();
        message.push(0x00); // Magic Byte
        message.extend_from_slice(&schema_id.to_be_bytes()); // Schema ID (Big Endian)
        message.extend_from_slice(&avro_bytes);

        Ok(message)
    }

    /// 解码消息
    pub async fn decode(&self, bytes: &[u8]) -> Result<User> {
        if bytes[0] != 0x00 {
            return Err(anyhow::anyhow!("Invalid magic byte"));
        }

        // 解析 Schema ID
        let schema_id = i32::from_be_bytes([bytes[1], bytes[2], bytes[3], bytes[4]]);
        
        // 获取 Schema
        let schema = self.registry.get_schema_by_id(schema_id).await?;

        // 反序列化
        let reader = Reader::with_schema(&schema, &bytes[5..])?;
        for value in reader {
            return Ok(from_value(&value?)?);
        }

        Err(anyhow::anyhow!("No data found"))
    }
}

/// Kafka Producer
pub async fn send_user_to_kafka(
    producer: &FutureProducer,
    encoder: &AvroEncoder,
    user: &User,
) -> Result<()> {
    let topic = "users";
    let subject = format!("{}-value", topic);

    let payload = encoder.encode(&subject, user).await?;

    producer.send(
        FutureRecord::to(topic)
            .key(&user.id)
            .payload(&payload),
        tokio::time::Duration::from_secs(5),
    ).await
    .map_err(|(e, _)| anyhow::anyhow!("Kafka send error: {:?}", e))?;

    Ok(())
}
```

---

## 8. 高级功能

### 8.1 Generic Record (无 Serde)

```rust
use apache_avro::types::{Record, Value};

/// 手动构建 Avro Record
pub fn create_generic_user(id: &str, email: &str, name: &str) -> Record<'static> {
    let schema = load_user_schema().unwrap();
    
    let mut record = Record::new(&schema).unwrap();
    record.put("id", Value::String(id.to_string()));
    record.put("email", Value::String(email.to_string()));
    record.put("name", Value::String(name.to_string()));
    record.put("age", Value::Union(0, Box::new(Value::Null)));
    record.put("roles", Value::Array(vec![]));
    record.put("metadata", Value::Map(HashMap::new()));
    record.put("created_at", Value::TimestampMillis(chrono::Utc::now().timestamp_millis()));

    record
}
```

### 8.2 Logical Types

```rust
// Avro 支持的 Logical Types:
// - decimal: 高精度小数
// - uuid: UUID 字符串
// - date: 日期 (天数)
// - time-millis: 时间 (毫秒)
// - time-micros: 时间 (微秒)
// - timestamp-millis: 时间戳 (毫秒)
// - timestamp-micros: 时间戳 (微秒)
// - duration: 持续时间

use apache_avro::types::Value;
use chrono::{NaiveDate, Utc};

/// 使用 Logical Types
pub fn example_logical_types() {
    // UUID
    let uuid_value = Value::Uuid(uuid::Uuid::new_v4());

    // Date (天数，从 1970-01-01 开始)
    let date = NaiveDate::from_ymd_opt(2025, 10, 11).unwrap();
    let days = date.signed_duration_since(NaiveDate::from_ymd_opt(1970, 1, 1).unwrap()).num_days();
    let date_value = Value::Date(days as i32);

    // Timestamp Millis
    let timestamp_value = Value::TimestampMillis(Utc::now().timestamp_millis());

    println!("{:?}", uuid_value);
    println!("{:?}", date_value);
    println!("{:?}", timestamp_value);
}
```

---

## 9. 性能优化

### 9.1 对象池复用

```rust
use std::sync::Arc;
use tokio::sync::Mutex;

/// Schema 缓存
pub struct SchemaCache {
    schemas: Arc<Mutex<HashMap<String, Schema>>>,
}

impl SchemaCache {
    pub fn new() -> Self {
        Self {
            schemas: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    pub async fn get_or_load(&self, subject: &str) -> Result<Schema> {
        let mut cache = self.schemas.lock().await;
        
        if let Some(schema) = cache.get(subject) {
            return Ok(schema.clone());
        }

        // 加载 Schema
        let schema = load_user_schema()?;
        cache.insert(subject.to_string(), schema.clone());

        Ok(schema)
    }
}
```

### 9.2 批量编码

```rust
use rayon::prelude::*;

/// 并发批量序列化
pub fn batch_serialize(users: Vec<User>) -> Result<Vec<Vec<u8>>> {
    users.par_iter()
        .map(|user| serialize_user(user))
        .collect()
}
```

---

## 10. OTLP 可观测性集成

### 10.1 追踪初始化

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{runtime, trace as sdktrace, Resource};

pub fn init_telemetry() -> anyhow::Result<()> {
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .with_trace_config(
            sdktrace::Config::default().with_resource(Resource::new(vec![
                KeyValue::new("service.name", "avro-service"),
                KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
            ]))
        )
        .install_batch(runtime::Tokio)?;

    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new("info"))
        .with(tracing_subscriber::fmt::layer().json())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    Ok(())
}
```

### 10.2 带追踪的序列化

```rust
use opentelemetry::{global, trace::{SpanKind, Tracer, Status}, KeyValue};
use tracing::instrument;

#[instrument(skip(user), fields(
    avro.format = "binary",
    user.id = %user.id
))]
pub fn traced_serialize_user(user: &User) -> Result<Vec<u8>> {
    let tracer = global::tracer("avro-encoder");
    
    let mut span = tracer
        .span_builder("Avro Serialize")
        .with_kind(SpanKind::Internal)
        .with_attributes(vec![
            KeyValue::new("avro.format", "binary"),
            KeyValue::new("user.id", user.id.clone()),
        ])
        .start(&tracer);
    
    let start = std::time::Instant::now();
    
    let result = serialize_user(user);
    
    let duration = start.elapsed();
    
    match &result {
        Ok(bytes) => {
            span.set_attribute(KeyValue::new("avro.serialized_bytes", bytes.len() as i64));
            span.set_attribute(KeyValue::new("avro.serialize_time_us", duration.as_micros() as i64));
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

## 11. 测试策略

### 11.1 属性测试（Roundtrip）

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_roundtrip_serialization(
            id in "[a-z0-9\\-]{36}",
            email in "[a-z]{5,10}@example\\.com",
            name in "[A-Z][a-z]{3,10}",
            age in proptest::option::of(0..150i32),
        ) {
            let user = User {
                id,
                email,
                name,
                age,
                roles: vec!["user".to_string()],
                metadata: HashMap::new(),
                created_at: chrono::Utc::now().timestamp_millis(),
            };

            let bytes = serialize_user(&user).unwrap();
            let deserialized = deserialize_user(&bytes).unwrap();

            assert_eq!(user, deserialized);
        }
    }
}
```

---

## 12. 生产实践

### 12.1 完整的 Kafka 集成

```yaml
# docker-compose.yml
version: '3.8'

services:
  zookeeper:
    image: confluentinc/cp-zookeeper:7.6.0
    environment:
      ZOOKEEPER_CLIENT_PORT: 2181

  kafka:
    image: confluentinc/cp-kafka:7.6.0
    depends_on:
      - zookeeper
    ports:
      - "9092:9092"
    environment:
      KAFKA_BROKER_ID: 1
      KAFKA_ZOOKEEPER_CONNECT: zookeeper:2181
      KAFKA_ADVERTISED_LISTENERS: PLAINTEXT://localhost:9092

  schema-registry:
    image: confluentinc/cp-schema-registry:7.6.0
    depends_on:
      - kafka
    ports:
      - "8081:8081"
    environment:
      SCHEMA_REGISTRY_HOST_NAME: schema-registry
      SCHEMA_REGISTRY_KAFKASTORE_BOOTSTRAP_SERVERS: kafka:9092
```

---

## 13. 国际标准对齐

### 13.1 Apache Avro 规范

- ✅ **Avro 1.11 Specification**: 完整支持
- ✅ **Schema 演进规则**: Backward/Forward/Full Compatibility
- ✅ **Logical Types**: UUID, Date, Timestamp, Decimal

### 13.2 Kafka Schema Registry

- ✅ **Confluent Schema Registry API**: 兼容
- ✅ **Serialization Format**: Magic Byte (0x00) + Schema ID (4 bytes) + Payload

### 13.3 OpenTelemetry 语义约定

```rust
// Messaging Semantic Conventions (v1.21.0)
span.set_attribute(KeyValue::new("messaging.system", "kafka"));
span.set_attribute(KeyValue::new("messaging.destination", "users"));
span.set_attribute(KeyValue::new("messaging.kafka.message_key", "user-123"));
span.set_attribute(KeyValue::new("avro.schema_id", 42));
```

---

## 总结

**Apache Avro 优势**:

1. **Schema 演进**: 生产级 Schema 版本管理
2. **紧凑编码**: 比 JSON 节省 50%+ 空间
3. **Kafka 生态**: Schema Registry 一流支持
4. **动态类型**: 无需重新编译即可处理新 Schema

**适用场景**:

- ✅ 大数据处理（Hadoop/Spark）
- ✅ Kafka 事件流
- ✅ 需要 Schema 演进的长期存储
- ✅ 跨语言数据交换

---

**版权**: MIT License  
**作者**: OTLP Rust 项目组  
**最后更新**: 2025-10-11
