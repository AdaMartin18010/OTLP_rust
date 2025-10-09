# Elasticsearch Rust 完整追踪集成指南

## 目录

- [Elasticsearch Rust 完整追踪集成指南](#elasticsearch-rust-完整追踪集成指南)
  - [目录](#目录)
  - [一、Elasticsearch 架构与追踪概述](#一elasticsearch-架构与追踪概述)
    - [1.1 Elasticsearch 核心组件](#11-elasticsearch-核心组件)
    - [1.2 追踪目标](#12-追踪目标)
  - [二、依赖配置](#二依赖配置)
    - [2.1 Cargo.toml](#21-cargotoml)
  - [三、Elasticsearch 语义约定](#三elasticsearch-语义约定)
    - [3.1 OpenTelemetry 属性](#31-opentelemetry-属性)
  - [四、基础追踪实现](#四基础追踪实现)
    - [4.1 Elasticsearch 客户端包装器](#41-elasticsearch-客户端包装器)
    - [4.2 追踪工具函数](#42-追踪工具函数)
  - [五、索引操作追踪](#五索引操作追踪)
    - [5.1 创建文档](#51-创建文档)
  - [六、搜索操作追踪](#六搜索操作追踪)
    - [6.1 基本搜索](#61-基本搜索)
  - [七、批量操作追踪](#七批量操作追踪)
    - [7.1 Bulk API](#71-bulk-api)
  - [八、聚合查询追踪](#八聚合查询追踪)
    - [8.1 聚合操作](#81-聚合操作)
  - [九、滚动查询追踪](#九滚动查询追踪)
    - [9.1 Scroll API](#91-scroll-api)
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

## 一、Elasticsearch 架构与追踪概述

### 1.1 Elasticsearch 核心组件

````text
┌─────────────────────────────────────────┐
│      Elasticsearch Rust Client          │
├─────────────────────────────────────────┤
│  - RESTful API (HTTP)                   │
│  - 异步操作（Tokio + Reqwest）          │
│  - JSON 序列化（serde_json）            │
│  - 批量操作（Bulk API）                 │
│  - 滚动查询（Scroll API）               │
└─────────────────────────────────────────┘
         ↓           ↓           ↓
    [Index]     [Search]     [Aggregate]
````

### 1.2 追踪目标

- **索引级别**：创建、更新、删除文档
- **搜索级别**：查询、过滤、排序、分页
- **聚合级别**：指标聚合、桶聚合
- **性能级别**：查询耗时、网络延迟、命中率

---

## 二、依赖配置

### 2.1 Cargo.toml

````toml
[dependencies]
# OpenTelemetry 核心
opentelemetry = { version = "0.31.0", features = ["trace"] }
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.24.0", features = ["grpc-tonic", "trace"] }

# Elasticsearch
elasticsearch = "8.17"
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# HTTP 客户端
reqwest = { version = "0.12", features = ["json"] }

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

## 三、Elasticsearch 语义约定

### 3.1 OpenTelemetry 属性

````rust
use opentelemetry::KeyValue;

pub struct ElasticsearchSpanAttributes;

impl ElasticsearchSpanAttributes {
    /// 数据库系统
    pub const DB_SYSTEM: &'static str = "db.system";
    
    /// Elasticsearch 集群名称
    pub const DB_NAME: &'static str = "db.name";
    
    /// 索引名称
    pub const DB_ELASTICSEARCH_INDEX: &'static str = "db.elasticsearch.index";
    
    /// 操作类型
    pub const DB_OPERATION: &'static str = "db.operation";
    
    /// 请求方法
    pub const HTTP_METHOD: &'static str = "http.method";
    
    /// HTTP 状态码
    pub const HTTP_STATUS_CODE: &'static str = "http.status_code";
    
    /// 服务器地址
    pub const NET_PEER_NAME: &'static str = "net.peer.name";
    pub const NET_PEER_PORT: &'static str = "net.peer.port";
    
    /// 查询 DSL（可选，注意大小）
    pub const DB_STATEMENT: &'static str = "db.statement";
    
    /// 命中文档数量
    pub const DB_ELASTICSEARCH_HIT_COUNT: &'static str = "db.elasticsearch.hit_count";
    
    /// 查询耗时（Elasticsearch 内部）
    pub const DB_ELASTICSEARCH_TOOK_MS: &'static str = "db.elasticsearch.took_ms";
}
````

---

## 四、基础追踪实现

### 4.1 Elasticsearch 客户端包装器

````rust
use elasticsearch::{Elasticsearch, http::transport::Transport};
use opentelemetry::trace::Tracer;
use std::sync::Arc;

/// 支持追踪的 Elasticsearch 客户端
pub struct TracedElasticsearch {
    client: Elasticsearch,
    tracer: Arc<dyn Tracer + Send + Sync>,
    cluster_name: String,
}

impl TracedElasticsearch {
    pub async fn new(url: &str, cluster_name: String) -> anyhow::Result<Self> {
        let transport = Transport::single_node(url)?;
        let client = Elasticsearch::new(transport);
        let tracer = opentelemetry::global::tracer("elasticsearch-client");
        
        Ok(Self {
            client,
            tracer: Arc::new(tracer),
            cluster_name,
        })
    }
    
    pub fn client(&self) -> &Elasticsearch {
        &self.client
    }
}
````

### 4.2 追踪工具函数

````rust
use opentelemetry::trace::{Span, SpanKind, Status};
use std::time::Instant;

impl TracedElasticsearch {
    /// 创建操作 Span
    fn start_span(&self, operation: &str, index: Option<&str>) -> Box<dyn Span> {
        let mut span = self.tracer
            .span_builder(format!("elasticsearch.{}", operation))
            .with_kind(SpanKind::Client)
            .start(&*self.tracer);
        
        span.set_attribute(KeyValue::new(
            ElasticsearchSpanAttributes::DB_SYSTEM,
            "elasticsearch",
        ));
        span.set_attribute(KeyValue::new(
            ElasticsearchSpanAttributes::DB_NAME,
            self.cluster_name.clone(),
        ));
        span.set_attribute(KeyValue::new(
            ElasticsearchSpanAttributes::DB_OPERATION,
            operation.to_string(),
        ));
        
        if let Some(idx) = index {
            span.set_attribute(KeyValue::new(
                ElasticsearchSpanAttributes::DB_ELASTICSEARCH_INDEX,
                idx.to_string(),
            ));
        }
        
        Box::new(span)
    }
}
````

---

## 五、索引操作追踪

### 5.1 创建文档

````rust
use serde::{Deserialize, Serialize};
use elasticsearch::IndexParts;

#[derive(Debug, Serialize, Deserialize)]
pub struct Document {
    pub id: String,
    pub title: String,
    pub content: String,
    pub timestamp: i64,
}

impl TracedElasticsearch {
    /// 索引单个文档
    pub async fn index_document<T: Serialize>(
        &self,
        index: &str,
        id: &str,
        doc: &T,
    ) -> anyhow::Result<()> {
        let mut span = self.start_span("index", Some(index));
        let start = Instant::now();
        
        let response = self.client
            .index(IndexParts::IndexId(index, id))
            .body(doc)
            .send()
            .await?;
        
        let duration = start.elapsed();
        span.set_attribute(KeyValue::new("db.duration_ms", duration.as_millis() as i64));
        
        let status_code = response.status_code().as_u16();
        span.set_attribute(KeyValue::new(ElasticsearchSpanAttributes::HTTP_STATUS_CODE, status_code as i64));
        
        if response.status_code().is_success() {
            span.set_status(Status::Ok);
        } else {
            span.set_status(Status::error(format!("HTTP {}", status_code)));
        }
        
        response.error_for_status_code()?;
        Ok(())
    }
    
    /// 更新文档
    pub async fn update_document<T: Serialize>(
        &self,
        index: &str,
        id: &str,
        doc: &T,
    ) -> anyhow::Result<()> {
        let mut span = self.start_span("update", Some(index));
        let start = Instant::now();
        
        let body = serde_json::json!({
            "doc": doc
        });
        
        let response = self.client
            .update(elasticsearch::UpdateParts::IndexId(index, id))
            .body(body)
            .send()
            .await?;
        
        let duration = start.elapsed();
        span.set_attribute(KeyValue::new("db.duration_ms", duration.as_millis() as i64));
        span.set_attribute(KeyValue::new(
            ElasticsearchSpanAttributes::HTTP_STATUS_CODE,
            response.status_code().as_u16() as i64,
        ));
        
        response.error_for_status_code()?;
        Ok(())
    }
    
    /// 删除文档
    pub async fn delete_document(&self, index: &str, id: &str) -> anyhow::Result<()> {
        let mut span = self.start_span("delete", Some(index));
        let start = Instant::now();
        
        let response = self.client
            .delete(elasticsearch::DeleteParts::IndexId(index, id))
            .send()
            .await?;
        
        let duration = start.elapsed();
        span.set_attribute(KeyValue::new("db.duration_ms", duration.as_millis() as i64));
        span.set_attribute(KeyValue::new(
            ElasticsearchSpanAttributes::HTTP_STATUS_CODE,
            response.status_code().as_u16() as i64,
        ));
        
        response.error_for_status_code()?;
        Ok(())
    }
}
````

---

## 六、搜索操作追踪

### 6.1 基本搜索

````rust
use elasticsearch::SearchParts;
use serde_json::Value;

#[derive(Debug, Deserialize)]
pub struct SearchResponse {
    pub took: i64,
    pub hits: SearchHits,
}

#[derive(Debug, Deserialize)]
pub struct SearchHits {
    pub total: SearchTotal,
    pub hits: Vec<SearchHit>,
}

#[derive(Debug, Deserialize)]
pub struct SearchTotal {
    pub value: i64,
}

#[derive(Debug, Deserialize)]
pub struct SearchHit {
    #[serde(rename = "_source")]
    pub source: Value,
}

impl TracedElasticsearch {
    /// 执行搜索
    pub async fn search(
        &self,
        index: &str,
        query: Value,
    ) -> anyhow::Result<SearchResponse> {
        let mut span = self.start_span("search", Some(index));
        let start = Instant::now();
        
        // 记录查询 DSL（限制大小）
        let query_str = serde_json::to_string(&query)?;
        if query_str.len() < 1000 {
            span.set_attribute(KeyValue::new(
                ElasticsearchSpanAttributes::DB_STATEMENT,
                query_str,
            ));
        }
        
        let response = self.client
            .search(SearchParts::Index(&[index]))
            .body(serde_json::json!({ "query": query }))
            .send()
            .await?;
        
        let duration = start.elapsed();
        span.set_attribute(KeyValue::new("db.duration_ms", duration.as_millis() as i64));
        span.set_attribute(KeyValue::new(
            ElasticsearchSpanAttributes::HTTP_STATUS_CODE,
            response.status_code().as_u16() as i64,
        ));
        
        let result: SearchResponse = response.json().await?;
        
        // 记录搜索结果元数据
        span.set_attribute(KeyValue::new(
            ElasticsearchSpanAttributes::DB_ELASTICSEARCH_HIT_COUNT,
            result.hits.total.value,
        ));
        span.set_attribute(KeyValue::new(
            ElasticsearchSpanAttributes::DB_ELASTICSEARCH_TOOK_MS,
            result.took,
        ));
        
        Ok(result)
    }
    
    /// 全文搜索
    pub async fn full_text_search(
        &self,
        index: &str,
        field: &str,
        query_text: &str,
    ) -> anyhow::Result<SearchResponse> {
        let query = serde_json::json!({
            "match": {
                field: query_text
            }
        });
        
        self.search(index, query).await
    }
    
    /// 精确匹配
    pub async fn term_search(
        &self,
        index: &str,
        field: &str,
        value: &str,
    ) -> anyhow::Result<SearchResponse> {
        let query = serde_json::json!({
            "term": {
                field: value
            }
        });
        
        self.search(index, query).await
    }
    
    /// 范围查询
    pub async fn range_search(
        &self,
        index: &str,
        field: &str,
        from: i64,
        to: i64,
    ) -> anyhow::Result<SearchResponse> {
        let query = serde_json::json!({
            "range": {
                field: {
                    "gte": from,
                    "lte": to
                }
            }
        });
        
        self.search(index, query).await
    }
}
````

---

## 七、批量操作追踪

### 7.1 Bulk API

````rust
use elasticsearch::BulkParts;

impl TracedElasticsearch {
    /// 批量索引文档
    pub async fn bulk_index<T: Serialize>(
        &self,
        index: &str,
        documents: Vec<(String, T)>,
    ) -> anyhow::Result<()> {
        let mut span = self.start_span("bulk_index", Some(index));
        span.set_attribute(KeyValue::new("db.bulk_size", documents.len() as i64));
        
        let start = Instant::now();
        
        let mut body: Vec<Value> = Vec::new();
        for (id, doc) in documents {
            body.push(serde_json::json!({
                "index": { "_id": id }
            }));
            body.push(serde_json::to_value(doc)?);
        }
        
        let response = self.client
            .bulk(BulkParts::Index(index))
            .body(body)
            .send()
            .await?;
        
        let duration = start.elapsed();
        span.set_attribute(KeyValue::new("db.duration_ms", duration.as_millis() as i64));
        span.set_attribute(KeyValue::new(
            ElasticsearchSpanAttributes::HTTP_STATUS_CODE,
            response.status_code().as_u16() as i64,
        ));
        
        let result: Value = response.json().await?;
        
        // 检查错误
        if let Some(errors) = result["errors"].as_bool() {
            if errors {
                span.set_status(Status::error("批量操作包含错误"));
                tracing::warn!("批量操作部分失败: {:?}", result["items"]);
            }
        }
        
        Ok(())
    }
}
````

---

## 八、聚合查询追踪

### 8.1 聚合操作

````rust
impl TracedElasticsearch {
    /// 执行聚合查询
    pub async fn aggregate(
        &self,
        index: &str,
        aggregations: Value,
    ) -> anyhow::Result<Value> {
        let mut span = self.start_span("aggregate", Some(index));
        let start = Instant::now();
        
        let body = serde_json::json!({
            "size": 0,
            "aggs": aggregations
        });
        
        let response = self.client
            .search(SearchParts::Index(&[index]))
            .body(body)
            .send()
            .await?;
        
        let duration = start.elapsed();
        span.set_attribute(KeyValue::new("db.duration_ms", duration.as_millis() as i64));
        
        let result: Value = response.json().await?;
        
        if let Some(took) = result["took"].as_i64() {
            span.set_attribute(KeyValue::new(
                ElasticsearchSpanAttributes::DB_ELASTICSEARCH_TOOK_MS,
                took,
            ));
        }
        
        Ok(result)
    }
    
    /// 指标聚合（平均值）
    pub async fn avg_aggregation(
        &self,
        index: &str,
        field: &str,
    ) -> anyhow::Result<f64> {
        let aggs = serde_json::json!({
            "avg_value": {
                "avg": { "field": field }
            }
        });
        
        let result = self.aggregate(index, aggs).await?;
        
        let avg = result["aggregations"]["avg_value"]["value"]
            .as_f64()
            .ok_or_else(|| anyhow::anyhow!("无法解析平均值"))?;
        
        Ok(avg)
    }
    
    /// 桶聚合（分组统计）
    pub async fn terms_aggregation(
        &self,
        index: &str,
        field: &str,
        size: i64,
    ) -> anyhow::Result<Vec<(String, i64)>> {
        let aggs = serde_json::json!({
            "group_by_field": {
                "terms": {
                    "field": field,
                    "size": size
                }
            }
        });
        
        let result = self.aggregate(index, aggs).await?;
        
        let buckets = result["aggregations"]["group_by_field"]["buckets"]
            .as_array()
            .ok_or_else(|| anyhow::anyhow!("无法解析桶"))?;
        
        let mut groups = Vec::new();
        for bucket in buckets {
            let key = bucket["key"].as_str().unwrap_or("").to_string();
            let count = bucket["doc_count"].as_i64().unwrap_or(0);
            groups.push((key, count));
        }
        
        Ok(groups)
    }
}
````

---

## 九、滚动查询追踪

### 9.1 Scroll API

````rust
use elasticsearch::{ScrollParts, ClearScrollParts};

impl TracedElasticsearch {
    /// 滚动查询（大数据集）
    pub async fn scroll_search(
        &self,
        index: &str,
        query: Value,
        batch_size: i64,
    ) -> anyhow::Result<Vec<Value>> {
        let mut span = self.start_span("scroll_search", Some(index));
        let start = Instant::now();
        
        // 初始搜索
        let response = self.client
            .search(SearchParts::Index(&[index]))
            .scroll("5m")
            .size(batch_size)
            .body(serde_json::json!({ "query": query }))
            .send()
            .await?;
        
        let mut result: SearchResponse = response.json().await?;
        let scroll_id = result.hits.hits.first()
            .and_then(|h| h.source.get("_scroll_id"))
            .and_then(|v| v.as_str())
            .map(|s| s.to_string());
        
        let mut all_hits = result.hits.hits.into_iter()
            .map(|h| h.source)
            .collect::<Vec<_>>();
        
        let mut total_fetched = all_hits.len();
        
        // 继续滚动
        if let Some(mut sid) = scroll_id {
            loop {
                let scroll_response = self.client
                    .scroll(ScrollParts::None)
                    .body(serde_json::json!({
                        "scroll": "5m",
                        "scroll_id": sid
                    }))
                    .send()
                    .await?;
                
                let scroll_result: SearchResponse = scroll_response.json().await?;
                
                if scroll_result.hits.hits.is_empty() {
                    break;
                }
                
                all_hits.extend(scroll_result.hits.hits.into_iter().map(|h| h.source));
                total_fetched = all_hits.len();
            }
            
            // 清理滚动上下文
            let _ = self.client
                .clear_scroll(ClearScrollParts::None)
                .body(serde_json::json!({ "scroll_id": sid }))
                .send()
                .await;
        }
        
        let duration = start.elapsed();
        span.set_attribute(KeyValue::new("db.duration_ms", duration.as_millis() as i64));
        span.set_attribute(KeyValue::new("db.total_fetched", total_fetched as i64));
        
        Ok(all_hits)
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
                    "Elasticsearch 操作失败，准备重试"
                );
                
                sleep(backoff).await;
            }
            Err(e) => {
                tracing::error!(
                    attempts = attempt + 1,
                    error = %e,
                    "Elasticsearch 操作失败，已达最大重试次数"
                );
                return Err(e);
            }
        }
    }
}
````

---

## 十一、性能监控

### 11.1 性能指标

````rust
use opentelemetry::metrics::{Histogram, Counter};

pub struct ElasticsearchMetrics {
    operation_duration: Histogram<f64>,
    operation_count: Counter<u64>,
    error_count: Counter<u64>,
    search_hit_count: Histogram<f64>,
}

impl ElasticsearchMetrics {
    pub fn new() -> Self {
        let meter = opentelemetry::global::meter("elasticsearch");
        
        Self {
            operation_duration: meter
                .f64_histogram("elasticsearch.operation.duration")
                .with_description("操作耗时（毫秒）")
                .with_unit("ms")
                .build(),
            operation_count: meter
                .u64_counter("elasticsearch.operation.count")
                .with_description("操作次数")
                .build(),
            error_count: meter
                .u64_counter("elasticsearch.operation.errors")
                .with_description("操作错误次数")
                .build(),
            search_hit_count: meter
                .f64_histogram("elasticsearch.search.hits")
                .with_description("搜索命中文档数")
                .build(),
        }
    }
    
    pub fn record_operation(
        &self,
        operation: &str,
        index: &str,
        duration_ms: f64,
        success: bool,
    ) {
        let labels = &[
            KeyValue::new("operation", operation.to_string()),
            KeyValue::new("index", index.to_string()),
        ];
        
        self.operation_duration.record(duration_ms, labels);
        self.operation_count.add(1, labels);
        
        if !success {
            self.error_count.add(1, labels);
        }
    }
    
    pub fn record_search_hits(&self, index: &str, hit_count: i64) {
        let labels = &[KeyValue::new("index", index.to_string())];
        self.search_hit_count.record(hit_count as f64, labels);
    }
}
````

---

## 十二、生产环境完整示例

### 12.1 完整应用

````rust
use opentelemetry::global;
use opentelemetry_sdk::trace::TracerProvider;
use opentelemetry_otlp::WithExportConfig;

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
    
    // 创建 Elasticsearch 客户端
    let es = TracedElasticsearch::new(
        "http://localhost:9200",
        "my-cluster".to_string(),
    ).await?;
    
    // 索引文档
    let doc = Document {
        id: "doc123".to_string(),
        title: "Rust OTLP Guide".to_string(),
        content: "Comprehensive guide to OpenTelemetry in Rust".to_string(),
        timestamp: chrono::Utc::now().timestamp(),
    };
    es.index_document("articles", "doc123", &doc).await?;
    
    // 全文搜索
    let results = es.full_text_search("articles", "content", "OpenTelemetry").await?;
    println!("搜索结果: {} 条", results.hits.total.value);
    
    // 聚合查询
    let avg_timestamp = es.avg_aggregation("articles", "timestamp").await?;
    println!("平均时间戳: {}", avg_timestamp);
    
    // 批量索引
    let bulk_docs = vec![
        ("doc456".to_string(), doc.clone()),
        ("doc789".to_string(), doc.clone()),
    ];
    es.bulk_index("articles", bulk_docs).await?;
    
    // 优雅关闭
    global::shutdown_tracer_provider();
    
    Ok(())
}
````

### 12.2 Docker Compose 配置

````yaml
version: '3.8'

services:
  elasticsearch:
    image: docker.elastic.co/elasticsearch/elasticsearch:8.17.0
    ports:
      - "9200:9200"
    environment:
      - discovery.type=single-node
      - xpack.security.enabled=false
    volumes:
      - es-data:/usr/share/elasticsearch/data
  
  jaeger:
    image: jaegertracing/all-in-one:1.66
    ports:
      - "4317:4317"   # OTLP gRPC
      - "16686:16686" # Jaeger UI
    environment:
      COLLECTOR_OTLP_ENABLED: "true"

volumes:
  es-data:
````

---

## 总结

### 核心要点

1. **完整追踪**：覆盖索引、搜索、聚合、滚动查询
2. **语义约定**：遵循 OpenTelemetry 数据库属性规范
3. **批量操作**：使用 Bulk API 提升性能
4. **错误处理**：重试机制、超时控制、错误记录
5. **性能优化**：批量索引、滚动查询、连接复用

### 最佳实践

- 使用 `TracedElasticsearch` 包装器自动追踪所有操作
- 为搜索记录命中数和查询耗时
- 批量操作应检查 `errors` 字段
- 滚动查询完成后清理滚动上下文
- 限制记录的查询 DSL 大小（< 1KB）

### 性能考虑

- 避免在高频路径上记录完整查询 DSL
- 使用批量操作减少网络往返
- 合理设置分页大小（默认 10，最大 10000）
- 对大数据集使用 Scroll API 或 Search After
- 生产环境启用 TLS 和认证

---

**文档版本**: v1.0  
**最后更新**: 2025-10-09  
**Rust 版本**: 1.90+  
**Elasticsearch 版本**: 8.17+  
**OpenTelemetry 版本**: 0.31.0+
