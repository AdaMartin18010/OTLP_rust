# Elasticsearch 语义约定 - Rust 完整实现

> **搜索与分析引擎**: Elasticsearch Tracing与Metrics完整规范 (Rust 1.90)  
> **最后更新**: 2025年10月10日

---

## 目录

- [Elasticsearch 语义约定 - Rust 完整实现](#elasticsearch-语义约定---rust-完整实现)
  - [目录](#目录)
  - [1. Elasticsearch 概述](#1-elasticsearch-概述)
    - [1.1 核心特性](#11-核心特性)
    - [1.2 核心架构](#12-核心架构)
    - [1.3 Rust 生态系统](#13-rust-生态系统)
  - [2. Rust 基础设施](#2-rust-基础设施)
    - [2.1 依赖配置](#21-依赖配置)
    - [2.2 核心导入](#22-核心导入)
    - [2.3 Elasticsearch 语义约定常量](#23-elasticsearch-语义约定常量)
  - [3. Elasticsearch 属性类型系统](#3-elasticsearch-属性类型系统)
    - [3.1 操作类型枚举](#31-操作类型枚举)
    - [3.2 Elasticsearch 属性结构体](#32-elasticsearch-属性结构体)
  - [4. 索引操作](#4-索引操作)
    - [4.1 索引文档](#41-索引文档)
    - [4.2 批量索引](#42-批量索引)
    - [4.3 更新文档](#43-更新文档)
    - [4.4 删除文档](#44-删除文档)
  - [5. 搜索操作](#5-搜索操作)
    - [5.1 基本搜索](#51-基本搜索)
    - [5.2 聚合查询](#52-聚合查询)
    - [5.3 滚动查询](#53-滚动查询)
  - [6. 查询DSL构建](#6-查询dsl构建)
    - [6.1 Match查询](#61-match查询)
    - [6.2 Term查询](#62-term查询)
    - [6.3 Bool查询](#63-bool查询)
  - [7. 完整示例](#7-完整示例)
    - [7.1 日志索引服务](#71-日志索引服务)
    - [7.2 日志搜索服务](#72-日志搜索服务)
    - [7.3 聚合分析示例](#73-聚合分析示例)
  - [8. Metrics 实现](#8-metrics-实现)
    - [8.1 操作 Metrics](#81-操作-metrics)
    - [8.2 性能 Metrics](#82-性能-metrics)
  - [9. 最佳实践](#9-最佳实践)
    - [9.1 性能优化](#91-性能优化)
    - [9.2 索引管理](#92-索引管理)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [相关规范](#相关规范)
    - [Rust Crates](#rust-crates)

---

## 1. Elasticsearch 概述

### 1.1 核心特性

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Elasticsearch - 分布式搜索与分析引擎

核心特性:
✅ 全文搜索 (基于Lucene)
✅ 实时索引与查询
✅ RESTful API
✅ 分布式架构
✅ JSON文档存储
✅ 强大的聚合分析
✅ 地理空间查询
✅ 近实时搜索 (NRT)
✅ 自动分片与副本

适用场景:
✅ 日志与事件数据分析
✅ 全文搜索引擎
✅ 应用性能监控 (APM)
✅ 安全分析 (SIEM)
✅ 业务指标分析
✅ 推荐系统

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 1.2 核心架构

```text
Cluster → Nodes → Indices → Shards → Documents

集群架构:
┌────────────┐
│  Master    │ (集群管理)
│   Node     │
└─────┬──────┘
      │
   ┌──┴──┐
   │     │
┌──▼──┐ ┌▼────┐
│Data │ │Data │ (数据节点)
│Node │ │Node │
└─────┘ └─────┘
```

### 1.3 Rust 生态系统

```rust
// Rust Elasticsearch 客户端
// - elasticsearch: 官方 Rust 客户端
// - 完整的 REST API 支持
// - 异步优先设计
// - 强类型查询构建器
```

---

## 2. Rust 基础设施

### 2.1 依赖配置

```toml
[package]
name = "elasticsearch-otlp-example"
version = "0.1.0"
edition = "2021"

[dependencies]
# Elasticsearch 官方客户端
elasticsearch = "8.5.0-alpha.1"

# OpenTelemetry
opentelemetry = { version = "0.22", features = ["trace", "metrics"] }
opentelemetry_sdk = { version = "0.22", features = ["rt-tokio"] }
opentelemetry-semantic-conventions = "0.14"

# 运行时
tokio = { version = "1", features = ["full"] }

# JSON 处理
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 实用工具
anyhow = "1.0"
thiserror = "1.0"
chrono = { version = "0.4", features = ["serde"] }
uuid = { version = "1.0", features = ["v4", "serde"] }

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
use elasticsearch::{
    Elasticsearch,
    IndexParts, SearchParts, DeleteParts, BulkParts,
    http::transport::{Transport, SingleNodeConnectionPool},
};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::time::Instant;
```

### 2.3 Elasticsearch 语义约定常量

```rust
pub mod es_conventions {
    // 数据库系统属性
    pub const DB_SYSTEM: &str = "db.system";
    pub const DB_SYSTEM_ELASTICSEARCH: &str = "elasticsearch";
    pub const DB_OPERATION: &str = "db.operation";
    
    // Elasticsearch 特定属性
    pub const DB_ELASTICSEARCH_INDEX: &str = "db.elasticsearch.index";
    pub const DB_ELASTICSEARCH_CLUSTER_NAME: &str = "db.elasticsearch.cluster.name";
    pub const DB_ELASTICSEARCH_NODE_NAME: &str = "db.elasticsearch.node.name";
    pub const DB_ELASTICSEARCH_BULK_SIZE: &str = "db.elasticsearch.bulk_size";
    
    // 查询属性
    pub const DB_STATEMENT: &str = "db.statement";
    
    // 响应属性
    pub const DB_RESPONSE_RETURNED_COUNT: &str = "db.response.returned_count";
    pub const DB_RESPONSE_TOOK_MS: &str = "db.response.took_ms";
    
    // 网络属性
    pub const NET_PEER_NAME: &str = "net.peer.name";
    pub const NET_PEER_PORT: &str = "net.peer.port";
}
```

---

## 3. Elasticsearch 属性类型系统

### 3.1 操作类型枚举

```rust
/// Elasticsearch 操作类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EsOperation {
    Index,
    Search,
    Update,
    Delete,
    Bulk,
    Count,
    Scroll,
    Aggregate,
}

impl EsOperation {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Index => "index",
            Self::Search => "search",
            Self::Update => "update",
            Self::Delete => "delete",
            Self::Bulk => "bulk",
            Self::Count => "count",
            Self::Scroll => "scroll",
            Self::Aggregate => "aggregate",
        }
    }
}
```

### 3.2 Elasticsearch 属性结构体

```rust
/// Elasticsearch 操作属性
#[derive(Debug, Clone)]
pub struct EsAttributes {
    pub index_name: String,
    pub operation: EsOperation,
    pub server_address: Option<String>,
    pub server_port: Option<u16>,
    pub cluster_name: Option<String>,
    pub statement: Option<String>,
}

impl EsAttributes {
    /// 创建基础属性
    pub fn new(index_name: impl Into<String>, operation: EsOperation) -> Self {
        Self {
            index_name: index_name.into(),
            operation,
            server_address: None,
            server_port: Some(9200),
            cluster_name: None,
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
                es_conventions::DB_SYSTEM,
                es_conventions::DB_SYSTEM_ELASTICSEARCH,
            ),
            KeyValue::new(
                es_conventions::DB_ELASTICSEARCH_INDEX,
                self.index_name.clone(),
            ),
            KeyValue::new(
                es_conventions::DB_OPERATION,
                self.operation.as_str(),
            ),
        ];
        
        if let Some(ref addr) = self.server_address {
            attrs.push(KeyValue::new(es_conventions::NET_PEER_NAME, addr.clone()));
        }
        
        if let Some(port) = self.server_port {
            attrs.push(KeyValue::new(es_conventions::NET_PEER_PORT, port as i64));
        }
        
        if let Some(ref cluster) = self.cluster_name {
            attrs.push(KeyValue::new(
                es_conventions::DB_ELASTICSEARCH_CLUSTER_NAME,
                cluster.clone(),
            ));
        }
        
        if let Some(ref stmt) = self.statement {
            attrs.push(KeyValue::new(es_conventions::DB_STATEMENT, stmt.clone()));
        }
        
        attrs
    }
}
```

---

## 4. 索引操作

### 4.1 索引文档

```rust
/// Elasticsearch 追踪客户端
pub struct EsClient {
    client: Elasticsearch,
    tracer: global::BoxedTracer,
}

impl EsClient {
    /// 创建客户端
    pub fn new(url: &str) -> anyhow::Result<Self> {
        let transport = Transport::single_node(url)?;
        let client = Elasticsearch::new(transport);
        let tracer = global::tracer("elasticsearch-client");
        
        Ok(Self { client, tracer })
    }
    
    /// 索引文档 (带追踪)
    pub async fn index_document<T>(
        &self,
        index: &str,
        id: Option<&str>,
        document: &T,
    ) -> anyhow::Result<Value>
    where
        T: Serialize,
    {
        // 创建 CLIENT Span
        let mut span = self.tracer
            .span_builder("elasticsearch_index")
            .with_kind(SpanKind::Client)
            .start(&self.tracer);
        
        // 设置属性
        let attrs = EsAttributes::new(index, EsOperation::Index)
            .with_server("localhost", 9200);
        
        span.set_attributes(attrs.to_key_values());
        
        // 序列化文档
        let body = serde_json::to_vec(document)?;
        
        // 执行索引操作
        let start = Instant::now();
        
        let response = match id {
            Some(doc_id) => {
                self.client
                    .index(IndexParts::IndexId(index, doc_id))
                    .body(body)
                    .send()
                    .await
            }
            None => {
                self.client
                    .index(IndexParts::Index(index))
                    .body(body)
                    .send()
                    .await
            }
        };
        
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new(
            "db.operation.duration_ms",
            duration.as_millis() as i64,
        ));
        
        match response {
            Ok(res) => {
                let status_code = res.status_code().as_u16();
                span.set_attribute(KeyValue::new("http.status_code", status_code as i64));
                
                if res.status_code().is_success() {
                    span.set_status(Status::Ok);
                    let json = res.json::<Value>().await?;
                    span.end();
                    Ok(json)
                } else {
                    let error = res.text().await?;
                    span.set_status(Status::error(format!("Index failed: {}", error)));
                    span.end();
                    Err(anyhow::anyhow!("Index failed: {}", error))
                }
            }
            Err(e) => {
                span.set_status(Status::error(format!("{}", e)));
                span.end();
                Err(e.into())
            }
        }
    }
}
```

### 4.2 批量索引

```rust
impl EsClient {
    /// 批量索引文档
    pub async fn bulk_index<T>(
        &self,
        index: &str,
        documents: Vec<T>,
    ) -> anyhow::Result<Value>
    where
        T: Serialize,
    {
        let mut span = self.tracer
            .span_builder("elasticsearch_bulk")
            .with_kind(SpanKind::Client)
            .start(&self.tracer);
        
        let attrs = EsAttributes::new(index, EsOperation::Bulk);
        span.set_attributes(attrs.to_key_values());
        span.set_attribute(KeyValue::new(
            es_conventions::DB_ELASTICSEARCH_BULK_SIZE,
            documents.len() as i64,
        ));
        
        // 构建批量请求体
        let mut body = Vec::new();
        
        for doc in documents {
            // 操作元数据
            let action = json!({ "index": { "_index": index } });
            body.push(serde_json::to_vec(&action)?);
            body.push(b"\n".to_vec());
            
            // 文档数据
            body.push(serde_json::to_vec(&doc)?);
            body.push(b"\n".to_vec());
        }
        
        let body_bytes: Vec<u8> = body.into_iter().flatten().collect();
        
        // 执行批量操作
        let start = Instant::now();
        let response = self.client
            .bulk(BulkParts::None)
            .body(body_bytes)
            .send()
            .await;
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new(
            "db.operation.duration_ms",
            duration.as_millis() as i64,
        ));
        
        match response {
            Ok(res) => {
                if res.status_code().is_success() {
                    span.set_status(Status::Ok);
                    let json = res.json::<Value>().await?;
                    span.end();
                    Ok(json)
                } else {
                    let error = res.text().await?;
                    span.set_status(Status::error(format!("Bulk failed: {}", error)));
                    span.end();
                    Err(anyhow::anyhow!("Bulk failed: {}", error))
                }
            }
            Err(e) => {
                span.set_status(Status::error(format!("{}", e)));
                span.end();
                Err(e.into())
            }
        }
    }
}
```

### 4.3 更新文档

```rust
impl EsClient {
    /// 更新文档
    pub async fn update_document<T>(
        &self,
        index: &str,
        id: &str,
        doc: &T,
    ) -> anyhow::Result<Value>
    where
        T: Serialize,
    {
        let mut span = self.tracer
            .span_builder("elasticsearch_update")
            .with_kind(SpanKind::Client)
            .start(&self.tracer);
        
        let attrs = EsAttributes::new(index, EsOperation::Update);
        span.set_attributes(attrs.to_key_values());
        
        let body = json!({
            "doc": doc
        });
        
        let start = Instant::now();
        let response = self.client
            .update(elasticsearch::UpdateParts::IndexId(index, id))
            .body(body)
            .send()
            .await;
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new(
            "db.operation.duration_ms",
            duration.as_millis() as i64,
        ));
        
        match response {
            Ok(res) => {
                if res.status_code().is_success() {
                    span.set_status(Status::Ok);
                    let json = res.json::<Value>().await?;
                    span.end();
                    Ok(json)
                } else {
                    let error = res.text().await?;
                    span.set_status(Status::error(error.clone()));
                    span.end();
                    Err(anyhow::anyhow!(error))
                }
            }
            Err(e) => {
                span.set_status(Status::error(format!("{}", e)));
                span.end();
                Err(e.into())
            }
        }
    }
}
```

### 4.4 删除文档

```rust
impl EsClient {
    /// 删除文档
    pub async fn delete_document(
        &self,
        index: &str,
        id: &str,
    ) -> anyhow::Result<Value> {
        let mut span = self.tracer
            .span_builder("elasticsearch_delete")
            .with_kind(SpanKind::Client)
            .start(&self.tracer);
        
        let attrs = EsAttributes::new(index, EsOperation::Delete);
        span.set_attributes(attrs.to_key_values());
        
        let start = Instant::now();
        let response = self.client
            .delete(DeleteParts::IndexId(index, id))
            .send()
            .await;
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new(
            "db.operation.duration_ms",
            duration.as_millis() as i64,
        ));
        
        match response {
            Ok(res) => {
                if res.status_code().is_success() {
                    span.set_status(Status::Ok);
                    let json = res.json::<Value>().await?;
                    span.end();
                    Ok(json)
                } else {
                    let error = res.text().await?;
                    span.set_status(Status::error(error.clone()));
                    span.end();
                    Err(anyhow::anyhow!(error))
                }
            }
            Err(e) => {
                span.set_status(Status::error(format!("{}", e)));
                span.end();
                Err(e.into())
            }
        }
    }
}
```

---

## 5. 搜索操作

### 5.1 基本搜索

```rust
impl EsClient {
    /// 搜索文档 (带追踪)
    pub async fn search<T>(
        &self,
        index: &str,
        query: Value,
    ) -> anyhow::Result<SearchResponse<T>>
    where
        T: for<'de> Deserialize<'de>,
    {
        let mut span = self.tracer
            .span_builder("elasticsearch_search")
            .with_kind(SpanKind::Client)
            .start(&self.tracer);
        
        // 序列化查询DSL
        let query_str = serde_json::to_string(&query)?;
        
        let attrs = EsAttributes::new(index, EsOperation::Search)
            .with_statement(query_str);
        
        span.set_attributes(attrs.to_key_values());
        
        // 执行搜索
        let start = Instant::now();
        let response = self.client
            .search(SearchParts::Index(&[index]))
            .body(query)
            .send()
            .await;
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new(
            "db.operation.duration_ms",
            duration.as_millis() as i64,
        ));
        
        match response {
            Ok(res) => {
                if res.status_code().is_success() {
                    let search_result = res.json::<SearchResponse<T>>().await?;
                    
                    span.set_attribute(KeyValue::new(
                        es_conventions::DB_RESPONSE_RETURNED_COUNT,
                        search_result.hits.total.value as i64,
                    ));
                    
                    if let Some(took) = search_result.took {
                        span.set_attribute(KeyValue::new(
                            es_conventions::DB_RESPONSE_TOOK_MS,
                            took as i64,
                        ));
                    }
                    
                    span.set_status(Status::Ok);
                    span.end();
                    Ok(search_result)
                } else {
                    let error = res.text().await?;
                    span.set_status(Status::error(error.clone()));
                    span.end();
                    Err(anyhow::anyhow!(error))
                }
            }
            Err(e) => {
                span.set_status(Status::error(format!("{}", e)));
                span.end();
                Err(e.into())
            }
        }
    }
}

/// 搜索响应结构
#[derive(Debug, Deserialize)]
pub struct SearchResponse<T> {
    pub took: Option<u64>,
    pub hits: Hits<T>,
}

#[derive(Debug, Deserialize)]
pub struct Hits<T> {
    pub total: Total,
    pub hits: Vec<Hit<T>>,
}

#[derive(Debug, Deserialize)]
pub struct Total {
    pub value: u64,
    pub relation: String,
}

#[derive(Debug, Deserialize)]
pub struct Hit<T> {
    #[serde(rename = "_source")]
    pub source: T,
    #[serde(rename = "_score")]
    pub score: Option<f64>,
}
```

### 5.2 聚合查询

```rust
impl EsClient {
    /// 执行聚合查询
    pub async fn aggregate(
        &self,
        index: &str,
        aggregations: Value,
    ) -> anyhow::Result<Value> {
        let mut span = self.tracer
            .span_builder("elasticsearch_aggregate")
            .with_kind(SpanKind::Client)
            .start(&self.tracer);
        
        let attrs = EsAttributes::new(index, EsOperation::Aggregate);
        span.set_attributes(attrs.to_key_values());
        
        let body = json!({
            "size": 0,
            "aggs": aggregations
        });
        
        let start = Instant::now();
        let response = self.client
            .search(SearchParts::Index(&[index]))
            .body(body)
            .send()
            .await;
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new(
            "db.operation.duration_ms",
            duration.as_millis() as i64,
        ));
        
        match response {
            Ok(res) => {
                if res.status_code().is_success() {
                    span.set_status(Status::Ok);
                    let json = res.json::<Value>().await?;
                    span.end();
                    Ok(json)
                } else {
                    let error = res.text().await?;
                    span.set_status(Status::error(error.clone()));
                    span.end();
                    Err(anyhow::anyhow!(error))
                }
            }
            Err(e) => {
                span.set_status(Status::error(format!("{}", e)));
                span.end();
                Err(e.into())
            }
        }
    }
}
```

### 5.3 滚动查询

```rust
impl EsClient {
    /// 滚动查询 (用于大量数据)
    pub async fn scroll_search<T>(
        &self,
        index: &str,
        query: Value,
        scroll_duration: &str,
    ) -> anyhow::Result<Vec<T>>
    where
        T: for<'de> Deserialize<'de>,
    {
        let mut span = self.tracer
            .span_builder("elasticsearch_scroll")
            .with_kind(SpanKind::Client)
            .start(&self.tracer);
        
        let attrs = EsAttributes::new(index, EsOperation::Scroll);
        span.set_attributes(attrs.to_key_values());
        
        let mut all_results = Vec::new();
        
        // 初始搜索
        let response = self.client
            .search(SearchParts::Index(&[index]))
            .scroll(scroll_duration)
            .body(query)
            .send()
            .await?;
        
        let mut search_result = response.json::<SearchResponse<T>>().await?;
        let mut scroll_id = search_result.hits.hits.iter()
            .map(|h| h.source.clone())
            .collect::<Vec<_>>();
        
        all_results.append(&mut scroll_id);
        
        // 继续滚动
        // 注意: 实际实现需要从响应中提取 scroll_id
        
        span.set_attribute(KeyValue::new(
            es_conventions::DB_RESPONSE_RETURNED_COUNT,
            all_results.len() as i64,
        ));
        span.set_status(Status::Ok);
        span.end();
        
        Ok(all_results)
    }
}
```

---

## 6. 查询DSL构建

### 6.1 Match查询

```rust
/// 构建 Match 查询
pub fn match_query(field: &str, value: &str) -> Value {
    json!({
        "query": {
            "match": {
                field: value
            }
        }
    })
}
```

### 6.2 Term查询

```rust
/// 构建 Term 查询
pub fn term_query(field: &str, value: &str) -> Value {
    json!({
        "query": {
            "term": {
                field: value
            }
        }
    })
}
```

### 6.3 Bool查询

```rust
/// 构建 Bool 查询
pub fn bool_query(must: Vec<Value>, should: Vec<Value>, must_not: Vec<Value>) -> Value {
    json!({
        "query": {
            "bool": {
                "must": must,
                "should": should,
                "must_not": must_not
            }
        }
    })
}
```

---

## 7. 完整示例

### 7.1 日志索引服务

```rust
#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct LogEntry {
    pub timestamp: String,
    pub level: String,
    pub message: String,
    pub service: String,
    pub trace_id: Option<String>,
}

pub struct LogIndexService {
    es: EsClient,
}

impl LogIndexService {
    pub fn new(es_url: &str) -> anyhow::Result<Self> {
        Ok(Self {
            es: EsClient::new(es_url)?,
        })
    }
    
    /// 索引单条日志
    pub async fn index_log(&self, log: &LogEntry) -> anyhow::Result<()> {
        let index = format!("logs-{}", chrono::Utc::now().format("%Y.%m.%d"));
        
        self.es.index_document(&index, None, log).await?;
        
        Ok(())
    }
    
    /// 批量索引日志
    pub async fn bulk_index_logs(&self, logs: Vec<LogEntry>) -> anyhow::Result<()> {
        let index = format!("logs-{}", chrono::Utc::now().format("%Y.%m.%d"));
        
        self.es.bulk_index(&index, logs).await?;
        
        Ok(())
    }
}
```

### 7.2 日志搜索服务

```rust
pub struct LogSearchService {
    es: EsClient,
}

impl LogSearchService {
    /// 搜索日志
    pub async fn search_logs(
        &self,
        query_text: &str,
        level: Option<&str>,
    ) -> anyhow::Result<Vec<LogEntry>> {
        let index = "logs-*";
        
        let mut must_clauses = vec![
            json!({
                "match": {
                    "message": query_text
                }
            })
        ];
        
        if let Some(log_level) = level {
            must_clauses.push(json!({
                "term": {
                    "level": log_level
                }
            }));
        }
        
        let query = json!({
            "query": {
                "bool": {
                    "must": must_clauses
                }
            },
            "sort": [
                { "timestamp": "desc" }
            ],
            "size": 100
        });
        
        let response = self.es.search::<LogEntry>(index, query).await?;
        
        Ok(response.hits.hits.into_iter().map(|h| h.source).collect())
    }
    
    /// 按 trace_id 搜索
    pub async fn search_by_trace_id(
        &self,
        trace_id: &str,
    ) -> anyhow::Result<Vec<LogEntry>> {
        let index = "logs-*";
        
        let query = json!({
            "query": {
                "term": {
                    "trace_id": trace_id
                }
            },
            "sort": [
                { "timestamp": "asc" }
            ]
        });
        
        let response = self.es.search::<LogEntry>(index, query).await?;
        
        Ok(response.hits.hits.into_iter().map(|h| h.source).collect())
    }
}
```

### 7.3 聚合分析示例

```rust
impl LogSearchService {
    /// 日志级别统计
    pub async fn log_level_stats(&self) -> anyhow::Result<Value> {
        let index = "logs-*";
        
        let aggregations = json!({
            "level_stats": {
                "terms": {
                    "field": "level.keyword",
                    "size": 10
                }
            }
        });
        
        self.es.aggregate(index, aggregations).await
    }
    
    /// 服务错误率统计
    pub async fn service_error_rate(&self) -> anyhow::Result<Value> {
        let index = "logs-*";
        
        let aggregations = json!({
            "services": {
                "terms": {
                    "field": "service.keyword"
                },
                "aggs": {
                    "error_rate": {
                        "filter": {
                            "term": {
                                "level": "ERROR"
                            }
                        }
                    }
                }
            }
        });
        
        self.es.aggregate(index, aggregations).await
    }
}
```

---

## 8. Metrics 实现

### 8.1 操作 Metrics

```rust
use opentelemetry::metrics::{Counter, Histogram, Meter};

pub struct EsMetrics {
    operations_total: Counter<u64>,
    operation_duration: Histogram<f64>,
    errors_total: Counter<u64>,
    documents_indexed: Counter<u64>,
}

impl EsMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            operations_total: meter
                .u64_counter("elasticsearch.operations.total")
                .with_description("Total Elasticsearch operations")
                .init(),
            
            operation_duration: meter
                .f64_histogram("elasticsearch.operation.duration")
                .with_description("Operation duration")
                .with_unit("s")
                .init(),
            
            errors_total: meter
                .u64_counter("elasticsearch.errors.total")
                .with_description("Total errors")
                .init(),
            
            documents_indexed: meter
                .u64_counter("elasticsearch.documents.indexed")
                .with_description("Total documents indexed")
                .init(),
        }
    }
    
    pub fn record_operation(
        &self,
        operation: &str,
        index: &str,
        duration: f64,
        success: bool,
    ) {
        let labels = [
            KeyValue::new("operation", operation.to_string()),
            KeyValue::new("index", index.to_string()),
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

### 8.2 性能 Metrics

```rust
pub struct EsPerformanceMetrics {
    query_cache_hit_rate: opentelemetry::metrics::Gauge<f64>,
    search_latency: Histogram<f64>,
}

impl EsPerformanceMetrics {
    pub fn record_search_latency(&self, latency_ms: f64, index: &str) {
        let labels = [KeyValue::new("index", index.to_string())];
        self.search_latency.record(latency_ms / 1000.0, &labels);
    }
}
```

---

## 9. 最佳实践

### 9.1 性能优化

```rust
pub mod performance {
    /// ✅ 使用批量操作
    pub async fn batch_indexing(es: &EsClient, logs: Vec<LogEntry>) -> anyhow::Result<()> {
        // 每次批量索引 1000 条
        for chunk in logs.chunks(1000) {
            es.bulk_index("logs-*", chunk.to_vec()).await?;
        }
        
        Ok(())
    }
    
    /// ✅ 使用过滤器而非查询
    pub fn use_filter_context() -> Value {
        json!({
            "query": {
                "bool": {
                    "filter": [
                        { "term": { "status": "active" } }
                    ]
                }
            }
        })
    }
}
```

### 9.2 索引管理

```rust
pub mod index_management {
    /// ✅ 使用索引模板
    pub fn create_index_template() -> Value {
        json!({
            "index_patterns": ["logs-*"],
            "settings": {
                "number_of_shards": 3,
                "number_of_replicas": 1,
                "refresh_interval": "30s"
            },
            "mappings": {
                "properties": {
                    "timestamp": { "type": "date" },
                    "level": { "type": "keyword" },
                    "message": { "type": "text" },
                    "service": { "type": "keyword" }
                }
            }
        })
    }
}
```

---

## 参考资源

### 官方文档

1. **OpenTelemetry Database Conventions**: <https://opentelemetry.io/docs/specs/semconv/database/>
2. **Elasticsearch Rust Client**: <https://github.com/elastic/elasticsearch-rs>
3. **Elasticsearch REST API**: <https://www.elastic.co/guide/en/elasticsearch/reference/current/rest-apis.html>

### 相关规范

1. **Elasticsearch Query DSL**: <https://www.elastic.co/guide/en/elasticsearch/reference/current/query-dsl.html>
2. **Elasticsearch Aggregations**: <https://www.elastic.co/guide/en/elasticsearch/reference/current/search-aggregations.html>

### Rust Crates

1. **elasticsearch**: <https://crates.io/crates/elasticsearch>
2. **serde_json**: <https://crates.io/crates/serde_json>

---

**文档版本**: v1.0  
**最后更新**: 2025-10-10  
**作者**: OTLP Rust 标准深度梳理团队
