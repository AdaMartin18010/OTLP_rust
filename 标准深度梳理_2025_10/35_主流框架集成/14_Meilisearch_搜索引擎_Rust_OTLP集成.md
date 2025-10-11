# Meilisearch 搜索引擎 - Rust + OTLP 完整集成指南

## 📋 目录

- [Meilisearch 搜索引擎 - Rust + OTLP 完整集成指南](#meilisearch-搜索引擎---rust--otlp-完整集成指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [什么是 Meilisearch?](#什么是-meilisearch)
    - [为什么选择 Meilisearch + Rust?](#为什么选择-meilisearch--rust)
    - [OTLP 集成价值](#otlp-集成价值)
  - [核心概念](#核心概念)
    - [1. 搜索引擎架构](#1-搜索引擎架构)
    - [2. Meilisearch 特性](#2-meilisearch-特性)
  - [环境准备](#环境准备)
    - [1. 安装 Meilisearch](#1-安装-meilisearch)
    - [2. Rust 项目配置](#2-rust-项目配置)
  - [基础集成](#基础集成)
    - [1. 客户端初始化](#1-客户端初始化)
    - [2. 索引管理](#2-索引管理)
    - [3. 文档操作](#3-文档操作)
  - [OTLP 追踪集成](#otlp-追踪集成)
    - [1. 搜索追踪](#1-搜索追踪)
    - [2. 索引更新追踪](#2-索引更新追踪)
    - [3. 任务监控](#3-任务监控)
  - [高级搜索特性](#高级搜索特性)
    - [1. 过滤搜索](#1-过滤搜索)
    - [2. 分面搜索](#2-分面搜索)
    - [3. 地理搜索](#3-地理搜索)
  - [性能优化](#性能优化)
    - [1. 索引设置](#1-索引设置)
    - [2. 批量操作](#2-批量操作)
    - [3. 缓存策略](#3-缓存策略)
  - [多租户支持](#多租户支持)
    - [1. 租户隔离](#1-租户隔离)
    - [2. API Key 管理](#2-api-key-管理)
  - [实时搜索](#实时搜索)
    - [1. Typo Tolerance](#1-typo-tolerance)
    - [2. 同义词](#2-同义词)
    - [3. 停用词](#3-停用词)
  - [完整示例](#完整示例)
    - [1. 电商产品搜索](#1-电商产品搜索)
    - [2. 内容管理系统](#2-内容管理系统)
  - [监控与告警](#监控与告警)
    - [1. Health Check](#1-health-check)
    - [2. 性能指标](#2-性能指标)
  - [最佳实践](#最佳实践)
    - [1. 索引优化](#1-索引优化)
    - [2. 查询优化](#2-查询优化)
    - [3. 部署建议](#3-部署建议)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [Meilisearch vs 其他搜索引擎](#meilisearch-vs-其他搜索引擎)
    - [下一步](#下一步)
  - [参考资料](#参考资料)

---

## 概述

### 什么是 Meilisearch?

**Meilisearch** 是用 Rust 编写的快速、相关性强的搜索引擎:

```text
┌────────────────────────────────────┐
│        Meilisearch Engine          │
├────────────────────────────────────┤
│  • 即时搜索 (<50ms)                 │
│  • Typo-tolerant (容错搜索)         │
│  • Faceted Search (分面搜索)        │
│  • RESTful API                     │
│  • 多语言支持                       │
└────────────────────────────────────┘
```

**核心特性**:

- **极速**: 搜索响应 <50ms
- **容错**: 自动纠正拼写错误
- **相关性**: 智能排序算法
- **易用**: RESTful API, 5分钟快速开始
- **多语言**: 支持中文、日文等

### 为什么选择 Meilisearch + Rust?

| 优势 | 说明 |
|------|------|
| **同语言** | Meilisearch 本身 Rust 写,SDK 原生高效 |
| **性能** | 零序列化开销 |
| **类型安全** | 编译期检查文档结构 |
| **异步** | Tokio 原生支持 |
| **小内存** | 适合嵌入式和边缘部署 |

### OTLP 集成价值

```text
应用 → Meilisearch SDK → OTLP → Observability
  ↓         ↓              ↓         ↓
搜索请求   索引操作       分布式追踪  性能分析
```

**可追踪操作**:

- Search Query 延迟和相关性
- Index Update 任务进度
- Document Ingestion 速率
- Typo Correction 效果
- Filter Performance

---

## 核心概念

### 1. 搜索引擎架构

```text
┌─────────────────────────────────────┐
│           User Query                │
└──────────────┬──────────────────────┘
               │
┌──────────────▼──────────────────────┐
│      Query Preprocessor             │
│  • Tokenization                     │
│  • Typo Correction                  │
│  • Synonym Expansion                │
└──────────────┬──────────────────────┘
               │
┌──────────────▼──────────────────────┐
│       Inverted Index                │
│  Term → [Doc IDs]                   │
└──────────────┬──────────────────────┘
               │
┌──────────────▼──────────────────────┐
│       Ranking Algorithm             │
│  • BM25                             │
│  • Field Weights                    │
│  • Custom Rules                     │
└──────────────┬──────────────────────┘
               │
┌──────────────▼──────────────────────┐
│      Search Results                 │
└─────────────────────────────────────┘
```

### 2. Meilisearch 特性

**索引结构**:

```text
Index (movies)
  ├─ Documents (JSON)
  ├─ Searchable Attributes [title, overview]
  ├─ Filterable Attributes [genre, year]
  ├─ Sortable Attributes [rating, release_date]
  ├─ Ranking Rules [words, typo, proximity, ...]
  └─ Synonyms [movie → film, actor → star]
```

---

## 环境准备

### 1. 安装 Meilisearch

```bash
# Docker 方式
docker run -d \
  -p 7700:7700 \
  -v $(pwd)/meili_data:/meili_data \
  --env MEILI_MASTER_KEY=your_master_key \
  getmeili/meilisearch:v1.7

# 二进制方式 (Linux/macOS)
curl -L https://install.meilisearch.com | sh
./meilisearch --master-key your_master_key

# Kubernetes
helm repo add meilisearch https://meilisearch.github.io/meilisearch-kubernetes
helm install meilisearch meilisearch/meilisearch \
  --set environment.MEILI_MASTER_KEY=your_master_key
```

### 2. Rust 项目配置

```toml
# Cargo.toml
[package]
name = "meilisearch-otlp-example"
version = "0.1.0"
edition = "2021"

[dependencies]
# Meilisearch SDK
meilisearch-sdk = "0.26"

# 异步运行时
tokio = { version = "1.37", features = ["full"] }

# OTLP
opentelemetry = "0.30"
opentelemetry-otlp = "0.30"
opentelemetry_sdk = { version = "0.30", features = ["rt-tokio"] }
tracing = "0.1"
tracing-subscriber = "0.3"
tracing-opentelemetry = "0.31"

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 错误处理
anyhow = "1.0"
thiserror = "1.0"

# HTTP
reqwest = { version = "0.12", features = ["json"] }

# 其他
uuid = { version = "1.8", features = ["v4", "serde"] }
chrono = { version = "0.4", features = ["serde"] }

[profile.release]
opt-level = 3
lto = true
```

---

## 基础集成

### 1. 客户端初始化

```rust
// src/client.rs
use meilisearch_sdk::{client::Client, errors::Error as MeiliError};
use tracing::{info, instrument};
use anyhow::Result;

pub struct MeilisearchClientWithTracing {
    client: Client,
}

impl MeilisearchClientWithTracing {
    #[instrument(skip(url, api_key))]
    pub async fn new(url: &str, api_key: Option<&str>) -> Result<Self> {
        info!("Connecting to Meilisearch at {}", url);
        
        let client = Client::new(url, api_key)?;
        
        // 测试连接
        client.health().await?;
        info!("Meilisearch connection established");
        
        Ok(Self { client })
    }
    
    pub fn client(&self) -> &Client {
        &self.client
    }
    
    #[instrument(skip(self))]
    pub async fn get_version(&self) -> Result<meilisearch_sdk::Version> {
        let version = self.client.get_version().await?;
        info!("Meilisearch version: {}", version.pkg_version);
        Ok(version)
    }
}
```

### 2. 索引管理

```rust
// src/index.rs
use meilisearch_sdk::{
    indexes::{Index, IndexUpdatesQuery},
    settings::Settings,
};
use serde::{Deserialize, Serialize};

impl MeilisearchClientWithTracing {
    #[instrument(skip(self))]
    pub async fn create_index(&self, uid: &str, primary_key: Option<&str>) -> Result<Index> {
        info!("Creating index: {}", uid);
        
        let task = self.client
            .create_index(uid, primary_key)
            .await?;
        
        // 等待任务完成
        task.wait_for_completion(&self.client, None, None).await?;
        
        let index = self.client.index(uid);
        info!("Index {} created successfully", uid);
        
        Ok(index)
    }
    
    #[instrument(skip(self))]
    pub async fn delete_index(&self, uid: &str) -> Result<()> {
        info!("Deleting index: {}", uid);
        
        let task = self.client
            .delete_index(uid)
            .await?;
        
        task.wait_for_completion(&self.client, None, None).await?;
        
        info!("Index {} deleted", uid);
        Ok(())
    }
    
    #[instrument(skip(self))]
    pub async fn list_indexes(&self) -> Result<Vec<String>> {
        let indexes = self.client.list_all_indexes().await?;
        
        let uids = indexes
            .results
            .into_iter()
            .map(|idx| idx.uid)
            .collect();
        
        Ok(uids)
    }
    
    #[instrument(skip(self, settings))]
    pub async fn update_index_settings(
        &self,
        index_uid: &str,
        settings: Settings,
    ) -> Result<()> {
        let index = self.client.index(index_uid);
        
        let task = index.set_settings(&settings).await?;
        task.wait_for_completion(&self.client, None, None).await?;
        
        info!("Index {} settings updated", index_uid);
        Ok(())
    }
}
```

### 3. 文档操作

```rust
// src/document.rs
use meilisearch_sdk::documents::{DocumentsQuery, DocumentQuery};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Movie {
    pub id: u64,
    pub title: String,
    pub overview: String,
    pub genres: Vec<String>,
    pub release_date: String,
    pub rating: f32,
}

impl MeilisearchClientWithTracing {
    #[instrument(skip(self, documents))]
    pub async fn add_documents<T: Serialize + Send + Sync>(
        &self,
        index_uid: &str,
        documents: &[T],
        primary_key: Option<&str>,
    ) -> Result<()> {
        info!("Adding {} documents to index {}", documents.len(), index_uid);
        
        let index = self.client.index(index_uid);
        
        let task = index
            .add_documents(documents, primary_key)
            .await?;
        
        task.wait_for_completion(&self.client, None, None).await?;
        
        info!("Documents added successfully");
        Ok(())
    }
    
    #[instrument(skip(self))]
    pub async fn get_document<T: for<'de> Deserialize<'de>>(
        &self,
        index_uid: &str,
        document_id: &str,
    ) -> Result<T> {
        let index = self.client.index(index_uid);
        let document = index.get_document::<T>(document_id).await?;
        
        Ok(document)
    }
    
    #[instrument(skip(self))]
    pub async fn delete_document(
        &self,
        index_uid: &str,
        document_id: &str,
    ) -> Result<()> {
        let index = self.client.index(index_uid);
        
        let task = index.delete_document(document_id).await?;
        task.wait_for_completion(&self.client, None, None).await?;
        
        info!("Document {} deleted", document_id);
        Ok(())
    }
    
    #[instrument(skip(self, documents))]
    pub async fn update_documents<T: Serialize + Send + Sync>(
        &self,
        index_uid: &str,
        documents: &[T],
        primary_key: Option<&str>,
    ) -> Result<()> {
        let index = self.client.index(index_uid);
        
        let task = index
            .add_or_update(documents, primary_key)
            .await?;
        
        task.wait_for_completion(&self.client, None, None).await?;
        
        Ok(())
    }
}
```

---

## OTLP 追踪集成

### 1. 搜索追踪

```rust
// src/search_tracing.rs
use meilisearch_sdk::search::{SearchQuery, SearchResults};
use opentelemetry::{
    global,
    trace::{Span, Tracer},
    KeyValue,
};
use tracing::{info_span, Instrument};

impl MeilisearchClientWithTracing {
    #[instrument(skip(self))]
    pub async fn search_traced<T: for<'de> Deserialize<'de> + Send>(
        &self,
        index_uid: &str,
        query: &str,
        limit: usize,
    ) -> Result<SearchResults<T>> {
        let tracer = global::tracer("meilisearch-client");
        
        let mut span = tracer
            .span_builder("meilisearch.search")
            .with_attributes(vec![
                KeyValue::new("db.system", "meilisearch"),
                KeyValue::new("db.operation", "search"),
                KeyValue::new("meilisearch.index", index_uid.to_string()),
                KeyValue::new("meilisearch.query", query.to_string()),
                KeyValue::new("meilisearch.limit", limit as i64),
            ])
            .start(&tracer);
        
        let start = std::time::Instant::now();
        
        let index = self.client.index(index_uid);
        let result = index
            .search()
            .with_query(query)
            .with_limit(limit)
            .execute::<T>()
            .await;
        
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new("meilisearch.duration_ms", duration.as_millis() as i64));
        
        match &result {
            Ok(search_results) => {
                span.set_attribute(KeyValue::new("meilisearch.hits", search_results.hits.len() as i64));
                span.set_attribute(KeyValue::new("meilisearch.processing_time_ms", search_results.processing_time_ms as i64));
                span.set_attribute(KeyValue::new("meilisearch.status", "success"));
                
                // 记录查询统计
                if let Some(estimated_total_hits) = search_results.estimated_total_hits {
                    span.set_attribute(KeyValue::new("meilisearch.estimated_total_hits", estimated_total_hits as i64));
                }
            }
            Err(e) => {
                span.record_error(e);
                span.set_attribute(KeyValue::new("meilisearch.status", "error"));
            }
        }
        
        span.end();
        result.map_err(Into::into)
    }
    
    #[instrument(skip(self, query))]
    pub async fn search_with_filter<T: for<'de> Deserialize<'de> + Send>(
        &self,
        index_uid: &str,
        query: &str,
        filter: &str,
        limit: usize,
    ) -> Result<SearchResults<T>> {
        let tracer = global::tracer("meilisearch-client");
        
        let span = tracer
            .span_builder("meilisearch.search_filtered")
            .with_attributes(vec![
                KeyValue::new("meilisearch.filter", filter.to_string()),
            ])
            .start(&tracer);
        
        let index = self.client.index(index_uid);
        let result = index
            .search()
            .with_query(query)
            .with_filter(filter)
            .with_limit(limit)
            .execute::<T>()
            .await?;
        
        span.end();
        Ok(result)
    }
}
```

### 2. 索引更新追踪

```rust
#[instrument(skip(self, documents))]
pub async fn add_documents_traced<T: Serialize + Send + Sync>(
    &self,
    index_uid: &str,
    documents: &[T],
) -> Result<()> {
    let tracer = global::tracer("meilisearch-client");
    
    let mut span = tracer
        .span_builder("meilisearch.add_documents")
        .with_attributes(vec![
            KeyValue::new("db.system", "meilisearch"),
            KeyValue::new("db.operation", "insert"),
            KeyValue::new("meilisearch.index", index_uid.to_string()),
            KeyValue::new("meilisearch.document_count", documents.len() as i64),
        ])
        .start(&tracer);
    
    let start = std::time::Instant::now();
    
    let index = self.client.index(index_uid);
    let task = index.add_documents(documents, None).await?;
    
    span.add_event("documents_submitted", vec![
        KeyValue::new("task_uid", task.get_task_uid() as i64),
    ]);
    
    // 等待任务完成
    let task_result = task.wait_for_completion(&self.client, None, None).await?;
    
    let duration = start.elapsed();
    
    span.set_attribute(KeyValue::new("meilisearch.duration_ms", duration.as_millis() as i64));
    span.set_attribute(KeyValue::new("meilisearch.task_status", format!("{:?}", task_result.status)));
    
    span.end();
    Ok(())
}
```

### 3. 任务监控

```rust
use meilisearch_sdk::tasks::{Task, TaskStatus};

#[instrument(skip(self))]
pub async fn monitor_task(&self, task_uid: u32) -> Result<Task> {
    let tracer = global::tracer("meilisearch-client");
    
    let span = tracer
        .span_builder("meilisearch.task_monitoring")
        .with_attributes(vec![
            KeyValue::new("meilisearch.task_uid", task_uid as i64),
        ])
        .start(&tracer);
    
    let task = self.client.get_task(task_uid).await?;
    
    span.set_attribute(KeyValue::new("meilisearch.task_status", format!("{:?}", task.status)));
    span.set_attribute(KeyValue::new("meilisearch.task_type", format!("{:?}", task.task_type)));
    
    span.end();
    Ok(task)
}
```

---

## 高级搜索特性

### 1. 过滤搜索

```rust
// src/advanced_search.rs
pub async fn search_with_complex_filter(
    &self,
    index_uid: &str,
    query: &str,
) -> Result<SearchResults<Movie>> {
    let filter = "genres = 'Action' AND rating > 7.5 AND release_date > '2020-01-01'";
    
    self.search_with_filter(index_uid, query, filter, 20).await
}

pub async fn search_with_or_filter(
    &self,
    index_uid: &str,
    query: &str,
) -> Result<SearchResults<Movie>> {
    let filter = "(genres = 'Action' OR genres = 'Adventure') AND rating > 8.0";
    
    self.search_with_filter(index_uid, query, filter, 20).await
}
```

### 2. 分面搜索

```rust
use meilisearch_sdk::search::Selectors;

pub async fn faceted_search(
    &self,
    index_uid: &str,
    query: &str,
) -> Result<SearchResults<Movie>> {
    let index = self.client.index(index_uid);
    
    let results = index
        .search()
        .with_query(query)
        .with_facets(Selectors::All)
        .execute::<Movie>()
        .await?;
    
    // 打印分面结果
    if let Some(facet_distribution) = &results.facet_distribution {
        for (facet_name, facet_values) in facet_distribution {
            tracing::info!("Facet {}: {:?}", facet_name, facet_values);
        }
    }
    
    Ok(results)
}
```

### 3. 地理搜索

```rust
#[derive(Debug, Serialize, Deserialize)]
pub struct Restaurant {
    pub id: u64,
    pub name: String,
    pub cuisine: String,
    #[serde(rename = "_geo")]
    pub geo: GeoPoint,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct GeoPoint {
    pub lat: f64,
    pub lng: f64,
}

pub async fn search_nearby_restaurants(
    &self,
    index_uid: &str,
    lat: f64,
    lng: f64,
    radius_meters: u32,
) -> Result<SearchResults<Restaurant>> {
    let index = self.client.index(index_uid);
    
    let results = index
        .search()
        .with_query("")
        .with_filter(&format!("_geoRadius({}, {}, {})", lat, lng, radius_meters))
        .with_sort(&["_geoPoint({}, {}):asc".to_string(), lat.to_string(), lng.to_string()])
        .execute::<Restaurant>()
        .await?;
    
    Ok(results)
}
```

---

## 性能优化

### 1. 索引设置

```rust
use meilisearch_sdk::settings::Settings;

pub async fn optimize_index_settings(&self, index_uid: &str) -> Result<()> {
    let mut settings = Settings::new();
    
    // 可搜索字段
    settings.searchable_attributes = Some(vec![
        "title".to_string(),
        "overview".to_string(),
        "genres".to_string(),
    ]);
    
    // 可过滤字段
    settings.filterable_attributes = Some(vec![
        "genres".to_string(),
        "rating".to_string(),
        "release_date".to_string(),
    ]);
    
    // 可排序字段
    settings.sortable_attributes = Some(vec![
        "rating".to_string(),
        "release_date".to_string(),
    ]);
    
    // 排名规则
    settings.ranking_rules = Some(vec![
        "words".to_string(),
        "typo".to_string(),
        "proximity".to_string(),
        "attribute".to_string(),
        "sort".to_string(),
        "exactness".to_string(),
        "rating:desc".to_string(),  // 自定义规则
    ]);
    
    // 显示字段
    settings.displayed_attributes = Some(vec![
        "id".to_string(),
        "title".to_string(),
        "overview".to_string(),
        "rating".to_string(),
    ]);
    
    self.update_index_settings(index_uid, settings).await?;
    Ok(())
}
```

### 2. 批量操作

```rust
pub async fn bulk_index_documents(
    &self,
    index_uid: &str,
    documents: Vec<Movie>,
) -> Result<()> {
    const BATCH_SIZE: usize = 1000;
    
    let tracer = global::tracer("meilisearch-client");
    let span = tracer
        .span_builder("meilisearch.bulk_index")
        .with_attributes(vec![
            KeyValue::new("meilisearch.total_documents", documents.len() as i64),
        ])
        .start(&tracer);
    
    for (i, chunk) in documents.chunks(BATCH_SIZE).enumerate() {
        let chunk_span = tracer
            .span_builder("meilisearch.bulk_chunk")
            .with_attributes(vec![
                KeyValue::new("meilisearch.chunk_index", i as i64),
                KeyValue::new("meilisearch.chunk_size", chunk.len() as i64),
            ])
            .start(&tracer);
        
        self.add_documents(index_uid, chunk, None).await?;
        
        chunk_span.end();
    }
    
    span.end();
    Ok(())
}
```

### 3. 缓存策略

```rust
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use std::time::{Duration, Instant};

pub struct SearchCache {
    cache: Arc<RwLock<HashMap<String, CachedResult>>>,
    ttl: Duration,
}

struct CachedResult {
    data: serde_json::Value,
    timestamp: Instant,
}

impl SearchCache {
    pub fn new(ttl_seconds: u64) -> Self {
        Self {
            cache: Arc::new(RwLock::new(HashMap::new())),
            ttl: Duration::from_secs(ttl_seconds),
        }
    }
    
    pub async fn get(&self, key: &str) -> Option<serde_json::Value> {
        let cache = self.cache.read().await;
        
        if let Some(cached) = cache.get(key) {
            if cached.timestamp.elapsed() < self.ttl {
                return Some(cached.data.clone());
            }
        }
        
        None
    }
    
    pub async fn set(&self, key: String, data: serde_json::Value) {
        let mut cache = self.cache.write().await;
        cache.insert(key, CachedResult {
            data,
            timestamp: Instant::now(),
        });
    }
}
```

---

## 多租户支持

### 1. 租户隔离

```rust
pub struct TenantManager {
    client: MeilisearchClientWithTracing,
}

impl TenantManager {
    pub async fn create_tenant_index(&self, tenant_id: &str) -> Result<()> {
        let index_uid = format!("tenant_{}", tenant_id);
        self.client.create_index(&index_uid, Some("id")).await?;
        
        // 设置租户特定配置
        let mut settings = Settings::new();
        settings.searchable_attributes = Some(vec!["title".to_string(), "content".to_string()]);
        
        self.client.update_index_settings(&index_uid, settings).await?;
        
        Ok(())
    }
    
    pub async fn search_tenant_data<T: for<'de> Deserialize<'de> + Send>(
        &self,
        tenant_id: &str,
        query: &str,
    ) -> Result<SearchResults<T>> {
        let index_uid = format!("tenant_{}", tenant_id);
        self.client.search_traced(&index_uid, query, 20).await
    }
}
```

### 2. API Key 管理

```rust
use meilisearch_sdk::key::{Action, Key, KeyBuilder};

pub async fn create_tenant_api_key(
    &self,
    tenant_id: &str,
    permissions: Vec<Action>,
) -> Result<Key> {
    let index_pattern = format!("tenant_{}/*", tenant_id);
    
    let key = KeyBuilder::new()
        .with_name(&format!("Tenant {} Key", tenant_id))
        .with_description(&format!("API key for tenant {}", tenant_id))
        .with_actions(permissions)
        .with_indexes(vec![index_pattern])
        .with_expires_at(None)  // 永久有效
        .execute(&self.client.client)
        .await?;
    
    Ok(key)
}
```

---

## 实时搜索

### 1. Typo Tolerance

```rust
pub async fn search_with_typo_tolerance(
    &self,
    index_uid: &str,
    query: &str,
) -> Result<SearchResults<Movie>> {
    let index = self.client.index(index_uid);
    
    // Meilisearch 默认启用 typo tolerance
    // 可以配置每个单词最大允许的错误数
    let mut settings = Settings::new();
    settings.typo_tolerance = Some(TypoToleranceSettings {
        enabled: Some(true),
        min_word_size_for_typos: Some(MinWordSizeForTypos {
            one_typo: Some(5),
            two_typos: Some(9),
        }),
        disable_on_words: Some(vec!["matrix".to_string()]),  // 不容错的词
        disable_on_attributes: Some(vec![]),
    });
    
    self.update_index_settings(index_uid, settings).await?;
    
    // 搜索 "matirx" 仍能找到 "matrix"
    let results = index
        .search()
        .with_query(query)
        .execute::<Movie>()
        .await?;
    
    Ok(results)
}
```

### 2. 同义词

```rust
use std::collections::HashMap;

pub async fn setup_synonyms(&self, index_uid: &str) -> Result<()> {
    let mut synonyms = HashMap::new();
    
    synonyms.insert("movie".to_string(), vec!["film".to_string(), "picture".to_string()]);
    synonyms.insert("actor".to_string(), vec!["star".to_string(), "performer".to_string()]);
    
    let index = self.client.index(index_uid);
    let task = index.set_synonyms(&synonyms).await?;
    task.wait_for_completion(&self.client.client, None, None).await?;
    
    Ok(())
}
```

### 3. 停用词

```rust
pub async fn setup_stop_words(&self, index_uid: &str) -> Result<()> {
    let stop_words = vec![
        "the".to_string(),
        "a".to_string(),
        "an".to_string(),
        "and".to_string(),
        "or".to_string(),
        "but".to_string(),
    ];
    
    let index = self.client.index(index_uid);
    let task = index.set_stop_words(&stop_words).await?;
    task.wait_for_completion(&self.client.client, None, None).await?;
    
    Ok(())
}
```

---

## 完整示例

### 1. 电商产品搜索

```rust
// src/examples/ecommerce.rs
#[derive(Debug, Serialize, Deserialize)]
pub struct Product {
    pub id: String,
    pub name: String,
    pub description: String,
    pub category: String,
    pub price: f64,
    pub stock: u32,
    pub brand: String,
    pub rating: f32,
}

pub async fn ecommerce_search_example() -> Result<()> {
    // 初始化客户端
    let client = MeilisearchClientWithTracing::new(
        "http://localhost:7700",
        Some("your_master_key"),
    ).await?;
    
    let index_uid = "products";
    
    // 创建索引
    client.create_index(index_uid, Some("id")).await?;
    
    // 配置索引
    let mut settings = Settings::new();
    settings.searchable_attributes = Some(vec![
        "name".to_string(),
        "description".to_string(),
        "brand".to_string(),
    ]);
    settings.filterable_attributes = Some(vec![
        "category".to_string(),
        "price".to_string(),
        "rating".to_string(),
        "stock".to_string(),
    ]);
    settings.sortable_attributes = Some(vec![
        "price".to_string(),
        "rating".to_string(),
    ]);
    
    client.update_index_settings(index_uid, settings).await?;
    
    // 添加产品
    let products = vec![
        Product {
            id: "1".to_string(),
            name: "Rust Programming Book".to_string(),
            description: "Learn Rust from scratch".to_string(),
            category: "Books".to_string(),
            price: 39.99,
            stock: 100,
            brand: "OReilly".to_string(),
            rating: 4.8,
        },
        // ... 更多产品
    ];
    
    client.add_documents_traced(index_uid, &products).await?;
    
    // 搜索: 按相关性排序
    let results = client.search_traced::<Product>(
        index_uid,
        "rust programming",
        20,
    ).await?;
    
    // 搜索: 过滤 + 排序
    let index = client.client().index(index_uid);
    let filtered_results = index
        .search()
        .with_query("book")
        .with_filter("category = 'Books' AND price < 50")
        .with_sort(&["rating:desc".to_string()])
        .execute::<Product>()
        .await?;
    
    println!("Found {} products", filtered_results.hits.len());
    
    Ok(())
}
```

### 2. 内容管理系统

```rust
// src/examples/cms.rs
#[derive(Debug, Serialize, Deserialize)]
pub struct Article {
    pub id: String,
    pub title: String,
    pub content: String,
    pub author: String,
    pub tags: Vec<String>,
    pub published_at: String,
    pub views: u64,
}

pub async fn cms_search_example() -> Result<()> {
    let client = MeilisearchClientWithTracing::new(
        "http://localhost:7700",
        Some("your_master_key"),
    ).await?;
    
    let index_uid = "articles";
    
    // 创建索引
    client.create_index(index_uid, Some("id")).await?;
    
    // 配置索引
    let mut settings = Settings::new();
    settings.searchable_attributes = Some(vec![
        "title".to_string(),
        "content".to_string(),
        "author".to_string(),
        "tags".to_string(),
    ]);
    settings.filterable_attributes = Some(vec![
        "author".to_string(),
        "tags".to_string(),
        "published_at".to_string(),
    ]);
    
    client.update_index_settings(index_uid, settings).await?;
    
    // 全文搜索
    let results = client.search_traced::<Article>(
        index_uid,
        "rust concurrency",
        10,
    ).await?;
    
    // 按标签过滤
    let filtered_results = client.search_with_filter::<Article>(
        index_uid,
        "programming",
        "tags = 'rust' AND published_at > '2024-01-01'",
        10,
    ).await?;
    
    Ok(())
}
```

---

## 监控与告警

### 1. Health Check

```rust
pub async fn health_check(&self) -> Result<bool> {
    let health = self.client.client.health().await?;
    Ok(health.status == "available")
}

pub async fn continuous_health_check(&self, interval_secs: u64) {
    let mut interval = tokio::time::interval(Duration::from_secs(interval_secs));
    
    loop {
        interval.tick().await;
        
        match self.health_check().await {
            Ok(true) => tracing::info!("Meilisearch is healthy"),
            Ok(false) => tracing::warn!("Meilisearch is unhealthy"),
            Err(e) => tracing::error!("Health check failed: {}", e),
        }
    }
}
```

### 2. 性能指标

```rust
use opentelemetry::metrics::{Counter, Histogram};

pub struct MeilisearchMetrics {
    search_duration: Histogram<f64>,
    search_count: Counter<u64>,
    index_size: Counter<u64>,
}

impl MeilisearchMetrics {
    pub fn new() -> Self {
        let meter = global::meter("meilisearch-client");
        
        Self {
            search_duration: meter
                .f64_histogram("meilisearch.search.duration")
                .with_description("Search query duration")
                .with_unit("ms")
                .init(),
            search_count: meter
                .u64_counter("meilisearch.search.count")
                .with_description("Total number of searches")
                .init(),
            index_size: meter
                .u64_counter("meilisearch.index.documents")
                .with_description("Number of documents in index")
                .init(),
        }
    }
    
    pub fn record_search(&self, duration_ms: f64, index: &str, hits: usize) {
        let attributes = vec![
            KeyValue::new("index", index.to_string()),
            KeyValue::new("hits", hits as i64),
        ];
        
        self.search_duration.record(duration_ms, &attributes);
        self.search_count.add(1, &attributes);
    }
}
```

---

## 最佳实践

### 1. 索引优化

```rust
// 只索引需要搜索的字段
settings.searchable_attributes = Some(vec!["title".to_string(), "content".to_string()]);

// 只存储需要显示的字段
settings.displayed_attributes = Some(vec!["id".to_string(), "title".to_string()]);

// 合理设置排名规则
settings.ranking_rules = Some(vec![
    "words".to_string(),
    "typo".to_string(),
    "proximity".to_string(),
    "attribute".to_string(),
    "sort".to_string(),
    "exactness".to_string(),
]);
```

### 2. 查询优化

```rust
// 限制返回结果数量
.with_limit(20)

// 使用分页
.with_offset(20)

// 只返回必要字段
.with_attributes_to_retrieve(&["id", "title"])

// 高亮搜索词
.with_attributes_to_highlight(&["title", "content"])
```

### 3. 部署建议

```yaml
# docker-compose.yml (生产环境)
version: '3.8'
services:
  meilisearch:
    image: getmeili/meilisearch:v1.7
    ports:
      - "7700:7700"
    volumes:
      - ./meili_data:/meili_data
    environment:
      - MEILI_MASTER_KEY=${MEILI_MASTER_KEY}
      - MEILI_ENV=production
      - MEILI_MAX_INDEXING_MEMORY=2GB
      - MEILI_MAX_INDEXING_THREADS=4
    restart: always
    deploy:
      resources:
        limits:
          cpus: '4'
          memory: 4G
        reservations:
          cpus: '2'
          memory: 2G
```

---

## 总结

### 核心要点

1. **Meilisearch**: 极速搜索引擎 (<50ms)
2. **容错搜索**: 自动纠正拼写错误
3. **OTLP 集成**: 追踪搜索性能
4. **易用**: RESTful API, 简单配置
5. **Rust 原生**: 高性能,类型安全

### Meilisearch vs 其他搜索引擎

| 特性 | Meilisearch | Elasticsearch | Algolia | Typesense |
|------|-------------|---------------|---------|-----------|
| **性能** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ |
| **易用性** | ⭐⭐⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ |
| **容错** | ✅ 内置 | ⚠️ 需配置 | ✅ | ✅ |
| **部署** | 简单 | 复杂 | 托管 | 简单 |
| **价格** | 免费 | 免费/付费 | 付费 | 免费 |

### 下一步

- **Meilisearch Cloud**: 托管服务
- **Multi-Search**: 多索引搜索
- **Vector Search**: AI 驱动的语义搜索

---

## 参考资料

- [Meilisearch 官方文档](https://www.meilisearch.com/docs)
- [Meilisearch Rust SDK](https://github.com/meilisearch/meilisearch-rust)
- [Search Relevance Guide](https://www.meilisearch.com/docs/learn/relevancy/relevancy)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-11  
**Rust 版本**: 1.90+  
**Meilisearch 版本**: 1.7+  
**OpenTelemetry**: 0.30+
