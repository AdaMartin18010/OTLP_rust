# Qdrant 向量数据库 - Rust + OTLP 完整集成指南

## 📋 目录

- [Qdrant 向量数据库 - Rust + OTLP 完整集成指南](#qdrant-向量数据库---rust--otlp-完整集成指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [什么是 Qdrant?](#什么是-qdrant)
    - [为什么选择 Qdrant + Rust?](#为什么选择-qdrant--rust)
    - [OTLP 集成价值](#otlp-集成价值)
  - [核心概念](#核心概念)
    - [1. 向量数据库基础](#1-向量数据库基础)
    - [2. Qdrant 架构](#2-qdrant-架构)
  - [环境准备](#环境准备)
    - [1. 安装 Qdrant](#1-安装-qdrant)
    - [2. Rust 项目配置](#2-rust-项目配置)
  - [基础集成](#基础集成)
    - [1. 客户端初始化](#1-客户端初始化)
    - [2. Collection 管理](#2-collection-管理)
    - [3. 向量操作](#3-向量操作)
  - [OTLP 追踪集成](#otlp-追踪集成)
    - [1. 查询追踪](#1-查询追踪)
    - [2. 批量操作追踪](#2-批量操作追踪)
    - [3. 索引构建追踪](#3-索引构建追踪)
  - [性能监控](#性能监控)
    - [1. 查询性能](#1-查询性能)
    - [2. 索引性能](#2-索引性能)
    - [3. 内存监控](#3-内存监控)
  - [高级特性](#高级特性)
    - [1. 过滤查询](#1-过滤查询)
    - [2. 多向量搜索](#2-多向量搜索)
    - [3. 推荐系统](#3-推荐系统)
  - [AI/ML 集成](#aiml-集成)
    - [1. Embedding 生成](#1-embedding-生成)
    - [2. RAG 系统](#2-rag-系统)
    - [3. 语义搜索](#3-语义搜索)
  - [分布式部署](#分布式部署)
    - [1. 集群配置](#1-集群配置)
    - [2. 分片策略](#2-分片策略)
    - [3. 副本管理](#3-副本管理)
  - [完整示例](#完整示例)
    - [1. 文档搜索系统](#1-文档搜索系统)
    - [2. 图片相似度搜索](#2-图片相似度搜索)
  - [最佳实践](#最佳实践)
    - [1. 性能优化](#1-性能优化)
    - [2. 数据管理](#2-数据管理)
    - [3. 监控告警](#3-监控告警)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [Qdrant vs 其他向量数据库](#qdrant-vs-其他向量数据库)
    - [下一步](#下一步)
  - [参考资料](#参考资料)

---

## 概述

### 什么是 Qdrant?

**Qdrant** 是用 Rust 编写的高性能向量数据库,专为 AI/ML 应用设计:

```text
┌──────────────────────────────────┐
│      Qdrant Vector Database      │
├──────────────────────────────────┤
│  • 向量相似度搜索                 │
│  • 高维数据索引 (HNSW)            │
│  • 过滤和 Payload 查询            │
│  • 分布式架构                     │
│  • RESTful + gRPC API            │
└──────────────────────────────────┘
```

**核心特性**:

- **高性能**: Rust 实现,HNSW 索引
- **灵活过滤**: 结合向量搜索和结构化过滤
- **Payload 支持**: 存储额外元数据
- **云原生**: Kubernetes-ready
- **多语言SDK**: Rust, Python, TypeScript, Go

### 为什么选择 Qdrant + Rust?

| 优势 | 说明 |
|------|------|
| **原生 Rust** | Qdrant 本身用 Rust 写,API 天然契合 |
| **零序列化开销** | 直接使用 Rust 结构体 |
| **类型安全** | 编译期检查向量维度 |
| **异步优先** | Tokio 原生支持 |
| **性能极致** | 比 Python SDK 快 10x+ |

### OTLP 集成价值

```text
应用 → Qdrant SDK → OTLP Tracing → Observability Backend
  ↓         ↓            ↓                ↓
查询请求   向量搜索    分布式追踪      性能分析
```

**可追踪的操作**:

- Vector Search 查询延迟
- Collection 管理操作
- 批量插入性能
- 索引构建进度
- 分布式查询路由

---

## 核心概念

### 1. 向量数据库基础

```text
传统数据库:
SELECT * FROM users WHERE age > 30

向量数据库:
SELECT * FROM documents 
ORDER BY cosine_similarity(embedding, query_vector) 
LIMIT 10
```

**向量相似度度量**:

- **Cosine Similarity**: 角度相似度 (文本)
- **Euclidean Distance**: 欧氏距离 (图像)
- **Dot Product**: 点积 (推荐系统)

### 2. Qdrant 架构

```text
┌─────────────────────────────────────┐
│         Qdrant Cluster              │
│  ┌─────────┐  ┌─────────┐          │
│  │ Node 1  │  │ Node 2  │  ...     │
│  │ Shard 1 │  │ Shard 2 │          │
│  └─────────┘  └─────────┘          │
└─────────────────────────────────────┘
         ↓
┌─────────────────────────────────────┐
│       Collection (documents)        │
│  ┌──────────────────────────────┐  │
│  │ Points (Vectors + Payload)   │  │
│  │  • id: 1                     │  │
│  │  • vector: [0.1, 0.2, ...]   │  │
│  │  • payload: { title: "..." } │  │
│  └──────────────────────────────┘  │
└─────────────────────────────────────┘
```

---

## 环境准备

### 1. 安装 Qdrant

```bash
# Docker 方式
docker run -p 6333:6333 -p 6334:6334 \
  -v $(pwd)/qdrant_storage:/qdrant/storage:z \
  qdrant/qdrant

# Docker Compose
cat <<EOF > docker-compose.yml
version: '3.8'
services:
  qdrant:
    image: qdrant/qdrant:latest
    ports:
      - "6333:6333"
      - "6334:6334"
    volumes:
      - ./qdrant_storage:/qdrant/storage
    environment:
      - QDRANT_TELEMETRY_DISABLED=true
EOF

docker-compose up -d

# Kubernetes
helm repo add qdrant https://qdrant.to/helm
helm install qdrant qdrant/qdrant
```

### 2. Rust 项目配置

```toml
# Cargo.toml
[package]
name = "qdrant-otlp-example"
version = "0.1.0"
edition = "2021"

[dependencies]
# Qdrant SDK
qdrant-client = "1.9"

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

# 其他
uuid = { version = "1.8", features = ["v4", "serde"] }

[profile.release]
opt-level = 3
lto = true
```

---

## 基础集成

### 1. 客户端初始化

```rust
// src/client.rs
use qdrant_client::{
    prelude::*,
    qdrant::{CreateCollection, Distance, VectorParams, VectorsConfig},
};
use tracing::{info, instrument};
use anyhow::Result;

pub struct QdrantClientWithTracing {
    client: QdrantClient,
}

impl QdrantClientWithTracing {
    #[instrument(skip(url))]
    pub async fn new(url: &str) -> Result<Self> {
        info!("Connecting to Qdrant at {}", url);
        
        let client = QdrantClient::from_url(url)
            .timeout(std::time::Duration::from_secs(30))
            .build()?;
        
        // 测试连接
        client.health_check().await?;
        info!("Qdrant connection established");
        
        Ok(Self { client })
    }
    
    pub fn client(&self) -> &QdrantClient {
        &self.client
    }
}
```

### 2. Collection 管理

```rust
// src/collection.rs
use qdrant_client::qdrant::{
    CreateCollection, DeleteCollection, Distance, VectorParams, VectorsConfig,
};
use tracing::{info, instrument};

impl QdrantClientWithTracing {
    #[instrument(skip(self))]
    pub async fn create_collection(
        &self,
        collection_name: &str,
        vector_size: u64,
        distance: Distance,
    ) -> Result<()> {
        info!("Creating collection: {}", collection_name);
        
        self.client
            .create_collection(&CreateCollection {
                collection_name: collection_name.to_string(),
                vectors_config: Some(VectorsConfig {
                    config: Some(qdrant_client::qdrant::vectors_config::Config::Params(
                        VectorParams {
                            size: vector_size,
                            distance: distance.into(),
                            ..Default::default()
                        },
                    )),
                }),
                ..Default::default()
            })
            .await?;
        
        info!("Collection {} created successfully", collection_name);
        Ok(())
    }
    
    #[instrument(skip(self))]
    pub async fn delete_collection(&self, collection_name: &str) -> Result<()> {
        info!("Deleting collection: {}", collection_name);
        
        self.client
            .delete_collection(collection_name)
            .await?;
        
        info!("Collection {} deleted", collection_name);
        Ok(())
    }
    
    #[instrument(skip(self))]
    pub async fn list_collections(&self) -> Result<Vec<String>> {
        let response = self.client.list_collections().await?;
        
        let collections = response
            .collections
            .into_iter()
            .map(|c| c.name)
            .collect();
        
        Ok(collections)
    }
}
```

### 3. 向量操作

```rust
// src/vector_ops.rs
use qdrant_client::qdrant::{
    PointStruct, SearchPoints, UpsertPointsBuilder, Condition, Filter, FieldCondition,
};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Document {
    pub id: Uuid,
    pub title: String,
    pub content: String,
    pub embedding: Vec<f32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub metadata: Option<serde_json::Value>,
}

impl QdrantClientWithTracing {
    /// 插入单个向量
    #[instrument(skip(self, vector, payload))]
    pub async fn upsert_vector(
        &self,
        collection_name: &str,
        id: Uuid,
        vector: Vec<f32>,
        payload: serde_json::Value,
    ) -> Result<()> {
        let point = PointStruct::new(
            id.to_string(),
            vector,
            payload,
        );
        
        self.client
            .upsert_points(UpsertPointsBuilder::new(
                collection_name,
                vec![point],
            ))
            .await?;
        
        info!("Upserted vector with id: {}", id);
        Ok(())
    }
    
    /// 批量插入
    #[instrument(skip(self, documents))]
    pub async fn upsert_documents(
        &self,
        collection_name: &str,
        documents: Vec<Document>,
    ) -> Result<()> {
        let points: Vec<PointStruct> = documents
            .into_iter()
            .map(|doc| {
                let payload = serde_json::json!({
                    "title": doc.title,
                    "content": doc.content,
                    "metadata": doc.metadata,
                });
                
                PointStruct::new(
                    doc.id.to_string(),
                    doc.embedding,
                    payload,
                )
            })
            .collect();
        
        info!("Upserting {} documents", points.len());
        
        self.client
            .upsert_points(UpsertPointsBuilder::new(collection_name, points))
            .await?;
        
        Ok(())
    }
    
    /// 向量搜索
    #[instrument(skip(self, query_vector))]
    pub async fn search(
        &self,
        collection_name: &str,
        query_vector: Vec<f32>,
        limit: u64,
    ) -> Result<Vec<ScoredPoint>> {
        info!("Searching with limit: {}", limit);
        
        let search_result = self.client
            .search_points(&SearchPoints {
                collection_name: collection_name.to_string(),
                vector: query_vector,
                limit,
                with_payload: Some(true.into()),
                ..Default::default()
            })
            .await?;
        
        info!("Found {} results", search_result.result.len());
        Ok(search_result.result)
    }
    
    /// 带过滤的搜索
    #[instrument(skip(self, query_vector, filter))]
    pub async fn search_with_filter(
        &self,
        collection_name: &str,
        query_vector: Vec<f32>,
        filter: Filter,
        limit: u64,
    ) -> Result<Vec<ScoredPoint>> {
        let search_result = self.client
            .search_points(&SearchPoints {
                collection_name: collection_name.to_string(),
                vector: query_vector,
                filter: Some(filter),
                limit,
                with_payload: Some(true.into()),
                ..Default::default()
            })
            .await?;
        
        Ok(search_result.result)
    }
}
```

---

## OTLP 追踪集成

### 1. 查询追踪

```rust
// src/tracing.rs
use opentelemetry::{
    global,
    trace::{Span, Tracer},
    KeyValue,
};
use tracing::{info_span, Instrument};

impl QdrantClientWithTracing {
    #[instrument(skip(self, query_vector))]
    pub async fn search_traced(
        &self,
        collection_name: &str,
        query_vector: Vec<f32>,
        limit: u64,
    ) -> Result<Vec<ScoredPoint>> {
        let tracer = global::tracer("qdrant-client");
        
        let mut span = tracer
            .span_builder("qdrant.search")
            .with_attributes(vec![
                KeyValue::new("db.system", "qdrant"),
                KeyValue::new("db.operation", "search"),
                KeyValue::new("qdrant.collection", collection_name.to_string()),
                KeyValue::new("qdrant.limit", limit as i64),
                KeyValue::new("qdrant.vector_size", query_vector.len() as i64),
            ])
            .start(&tracer);
        
        let start = std::time::Instant::now();
        
        let result = self.search(collection_name, query_vector, limit).await;
        
        let duration = start.elapsed();
        
        span.set_attribute(KeyValue::new("qdrant.duration_ms", duration.as_millis() as i64));
        
        match &result {
            Ok(points) => {
                span.set_attribute(KeyValue::new("qdrant.results_count", points.len() as i64));
                span.set_attribute(KeyValue::new("qdrant.status", "success"));
            }
            Err(e) => {
                span.record_error(e);
                span.set_attribute(KeyValue::new("qdrant.status", "error"));
            }
        }
        
        span.end();
        result
    }
}
```

### 2. 批量操作追踪

```rust
#[instrument(skip(self, documents))]
pub async fn batch_upsert_traced(
    &self,
    collection_name: &str,
    documents: Vec<Document>,
) -> Result<()> {
    let tracer = global::tracer("qdrant-client");
    
    let mut span = tracer
        .span_builder("qdrant.batch_upsert")
        .with_attributes(vec![
            KeyValue::new("db.system", "qdrant"),
            KeyValue::new("db.operation", "upsert"),
            KeyValue::new("qdrant.collection", collection_name.to_string()),
            KeyValue::new("qdrant.batch_size", documents.len() as i64),
        ])
        .start(&tracer);
    
    // 分批处理
    const BATCH_SIZE: usize = 100;
    let mut processed = 0;
    
    for chunk in documents.chunks(BATCH_SIZE) {
        let chunk_span = tracer
            .span_builder("qdrant.batch_chunk")
            .with_attributes(vec![
                KeyValue::new("qdrant.chunk_size", chunk.len() as i64),
                KeyValue::new("qdrant.chunk_offset", processed as i64),
            ])
            .start(&tracer);
        
        self.upsert_documents(collection_name, chunk.to_vec()).await?;
        
        processed += chunk.len();
        chunk_span.end();
        
        span.add_event(
            "batch_chunk_completed",
            vec![KeyValue::new("processed", processed as i64)],
        );
    }
    
    span.set_attribute(KeyValue::new("qdrant.total_processed", processed as i64));
    span.end();
    
    Ok(())
}
```

### 3. 索引构建追踪

```rust
#[instrument(skip(self))]
pub async fn rebuild_index_traced(
    &self,
    collection_name: &str,
) -> Result<()> {
    let tracer = global::tracer("qdrant-client");
    
    let mut span = tracer
        .span_builder("qdrant.rebuild_index")
        .with_attributes(vec![
            KeyValue::new("db.system", "qdrant"),
            KeyValue::new("qdrant.collection", collection_name.to_string()),
        ])
        .start(&tracer);
    
    span.add_event("index_rebuild_started", vec![]);
    
    // 触发索引重建 (Qdrant 自动管理)
    // 这里模拟监控索引状态
    
    span.add_event("index_rebuild_completed", vec![]);
    span.end();
    
    Ok(())
}
```

---

## 性能监控

### 1. 查询性能

```rust
// src/metrics.rs
use opentelemetry::metrics::{Counter, Histogram};

pub struct QdrantMetrics {
    search_duration: Histogram<f64>,
    search_count: Counter<u64>,
    vector_count: Counter<u64>,
}

impl QdrantMetrics {
    pub fn new() -> Self {
        let meter = global::meter("qdrant-client");
        
        Self {
            search_duration: meter
                .f64_histogram("qdrant.search.duration")
                .with_description("Search query duration")
                .with_unit("ms")
                .init(),
            search_count: meter
                .u64_counter("qdrant.search.count")
                .with_description("Total number of searches")
                .init(),
            vector_count: meter
                .u64_counter("qdrant.vectors.count")
                .with_description("Total number of vectors")
                .init(),
        }
    }
    
    pub fn record_search(&self, duration_ms: f64, collection: &str) {
        let attributes = vec![
            KeyValue::new("collection", collection.to_string()),
        ];
        
        self.search_duration.record(duration_ms, &attributes);
        self.search_count.add(1, &attributes);
    }
    
    pub fn record_upsert(&self, count: u64, collection: &str) {
        let attributes = vec![
            KeyValue::new("collection", collection.to_string()),
        ];
        
        self.vector_count.add(count, &attributes);
    }
}
```

### 2. 索引性能

```promql
# Prometheus 查询

# 平均查询延迟
histogram_quantile(0.95, 
  rate(qdrant_search_duration_bucket[5m])
)

# QPS
rate(qdrant_search_count[1m])

# 向量数增长
rate(qdrant_vectors_count[5m])
```

### 3. 内存监控

```rust
pub async fn get_collection_info(
    &self,
    collection_name: &str,
) -> Result<CollectionInfo> {
    let info = self.client
        .collection_info(collection_name)
        .await?;
    
    let tracer = global::tracer("qdrant-client");
    let span = tracer
        .span_builder("qdrant.collection_info")
        .with_attributes(vec![
            KeyValue::new("qdrant.collection", collection_name.to_string()),
            KeyValue::new("qdrant.vectors_count", info.vectors_count as i64),
            KeyValue::new("qdrant.points_count", info.points_count as i64),
            KeyValue::new("qdrant.segments_count", info.segments_count as i64),
        ])
        .start(&tracer);
    
    span.end();
    Ok(info)
}
```

---

## 高级特性

### 1. 过滤查询

```rust
use qdrant_client::qdrant::{Condition, Filter, FieldCondition, Range};

pub async fn search_with_metadata_filter(
    &self,
    collection_name: &str,
    query_vector: Vec<f32>,
    category: &str,
    min_score: f64,
) -> Result<Vec<ScoredPoint>> {
    let filter = Filter::must([
        Condition::field("metadata.category", category),
        Condition::range("metadata.score", Range {
            gte: Some(min_score),
            ..Default::default()
        }),
    ]);
    
    self.search_with_filter(collection_name, query_vector, filter, 10).await
}
```

### 2. 多向量搜索

```rust
pub async fn multi_vector_search(
    &self,
    collection_name: &str,
    query_vectors: Vec<Vec<f32>>,
    limit: u64,
) -> Result<Vec<Vec<ScoredPoint>>> {
    let mut results = Vec::new();
    
    for query_vector in query_vectors {
        let result = self.search(collection_name, query_vector, limit).await?;
        results.push(result);
    }
    
    Ok(results)
}
```

### 3. 推荐系统

```rust
use qdrant_client::qdrant::{RecommendPoints, RecommendStrategy};

pub async fn recommend_similar(
    &self,
    collection_name: &str,
    positive_ids: Vec<String>,
    negative_ids: Vec<String>,
    limit: u64,
) -> Result<Vec<ScoredPoint>> {
    let result = self.client
        .recommend(&RecommendPoints {
            collection_name: collection_name.to_string(),
            positive: positive_ids.into_iter().map(|id| id.into()).collect(),
            negative: negative_ids.into_iter().map(|id| id.into()).collect(),
            limit,
            with_payload: Some(true.into()),
            strategy: Some(RecommendStrategy::AverageVector.into()),
            ..Default::default()
        })
        .await?;
    
    Ok(result.result)
}
```

---

## AI/ML 集成

### 1. Embedding 生成

```rust
// src/embeddings.rs
use rust_bert::pipelines::sentence_embeddings::{
    SentenceEmbeddingsBuilder, SentenceEmbeddingsModelType,
};

pub struct EmbeddingGenerator {
    model: SentenceEmbeddingsModel,
}

impl EmbeddingGenerator {
    pub fn new() -> Result<Self> {
        let model = SentenceEmbeddingsBuilder::remote(
            SentenceEmbeddingsModelType::AllMiniLmL12V2
        )
        .create_model()?;
        
        Ok(Self { model })
    }
    
    #[instrument(skip(self, texts))]
    pub fn generate_embeddings(&self, texts: &[&str]) -> Result<Vec<Vec<f32>>> {
        let embeddings = self.model.encode(texts)?;
        Ok(embeddings)
    }
}
```

### 2. RAG 系统

```rust
// src/rag.rs
pub struct RagSystem {
    qdrant: QdrantClientWithTracing,
    embedder: EmbeddingGenerator,
    collection: String,
}

impl RagSystem {
    #[instrument(skip(self, query))]
    pub async fn query(&self, query: &str, top_k: usize) -> Result<String> {
        // 1. 生成查询向量
        let query_embedding = self.embedder
            .generate_embeddings(&[query])?
            .into_iter()
            .next()
            .unwrap();
        
        // 2. 向量搜索
        let results = self.qdrant
            .search_traced(&self.collection, query_embedding, top_k as u64)
            .await?;
        
        // 3. 提取上下文
        let contexts: Vec<String> = results
            .iter()
            .filter_map(|point| {
                point.payload.get("content").and_then(|v| v.as_str()).map(String::from)
            })
            .collect();
        
        // 4. 生成回答 (调用 LLM)
        let context = contexts.join("\n\n");
        let prompt = format!(
            "Context:\n{}\n\nQuestion: {}\n\nAnswer:",
            context, query
        );
        
        // 这里应该调用 LLM API
        Ok(format!("Generated answer based on {} documents", results.len()))
    }
}
```

### 3. 语义搜索

```rust
pub async fn semantic_search(
    &self,
    query: &str,
    limit: usize,
) -> Result<Vec<SearchResult>> {
    // 生成 embedding
    let query_embedding = self.embedder.generate_embeddings(&[query])?[0].clone();
    
    // 向量搜索
    let results = self.qdrant
        .search_traced(&self.collection, query_embedding, limit as u64)
        .await?;
    
    // 转换结果
    let search_results = results
        .into_iter()
        .map(|point| SearchResult {
            id: point.id.unwrap().to_string(),
            score: point.score,
            title: point.payload.get("title")
                .and_then(|v| v.as_str())
                .unwrap_or(""),
            content: point.payload.get("content")
                .and_then(|v| v.as_str())
                .unwrap_or(""),
        })
        .collect();
    
    Ok(search_results)
}
```

---

## 分布式部署

### 1. 集群配置

```yaml
# qdrant-cluster.yaml
apiVersion: apps/v1
kind: StatefulSet
metadata:
  name: qdrant
spec:
  serviceName: qdrant
  replicas: 3
  selector:
    matchLabels:
      app: qdrant
  template:
    metadata:
      labels:
        app: qdrant
    spec:
      containers:
      - name: qdrant
        image: qdrant/qdrant:v1.9.0
        ports:
        - containerPort: 6333
          name: rest
        - containerPort: 6334
          name: grpc
        env:
        - name: QDRANT__CLUSTER__ENABLED
          value: "true"
        - name: QDRANT__CLUSTER__P2P__PORT
          value: "6335"
        volumeMounts:
        - name: qdrant-storage
          mountPath: /qdrant/storage
  volumeClaimTemplates:
  - metadata:
      name: qdrant-storage
    spec:
      accessModes: [ "ReadWriteOnce" ]
      resources:
        requests:
          storage: 10Gi
```

### 2. 分片策略

```rust
pub async fn create_sharded_collection(
    &self,
    collection_name: &str,
    vector_size: u64,
    shard_number: u32,
    replication_factor: u32,
) -> Result<()> {
    self.client
        .create_collection(&CreateCollection {
            collection_name: collection_name.to_string(),
            vectors_config: Some(VectorsConfig {
                config: Some(qdrant_client::qdrant::vectors_config::Config::Params(
                    VectorParams {
                        size: vector_size,
                        distance: Distance::Cosine.into(),
                        ..Default::default()
                    },
                )),
            }),
            shard_number: Some(shard_number),
            replication_factor: Some(replication_factor),
            ..Default::default()
        })
        .await?;
    
    Ok(())
}
```

### 3. 副本管理

```rust
pub async fn update_collection_replicas(
    &self,
    collection_name: &str,
    replication_factor: u32,
) -> Result<()> {
    self.client
        .update_collection(
            collection_name,
            &UpdateCollection {
                replication_factor: Some(replication_factor),
                ..Default::default()
            },
        )
        .await?;
    
    Ok(())
}
```

---

## 完整示例

### 1. 文档搜索系统

```rust
// src/examples/document_search.rs
use crate::*;

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化 OTLP
    init_otlp()?;
    
    // 连接 Qdrant
    let client = QdrantClientWithTracing::new("http://localhost:6334").await?;
    let collection_name = "documents";
    
    // 创建 collection
    client.create_collection(collection_name, 384, Distance::Cosine).await?;
    
    // 初始化 embedding 生成器
    let embedder = EmbeddingGenerator::new()?;
    
    // 插入文档
    let docs = vec![
        "Rust is a systems programming language",
        "Vector databases store high-dimensional vectors",
        "OpenTelemetry provides observability",
    ];
    
    let embeddings = embedder.generate_embeddings(&docs)?;
    
    let documents: Vec<Document> = docs
        .into_iter()
        .zip(embeddings)
        .enumerate()
        .map(|(i, (content, embedding))| Document {
            id: Uuid::new_v4(),
            title: format!("Document {}", i),
            content: content.to_string(),
            embedding,
            metadata: None,
        })
        .collect();
    
    client.upsert_documents(collection_name, documents).await?;
    
    // 查询
    let query = "What is Rust?";
    let query_embedding = embedder.generate_embeddings(&[query])?[0].clone();
    
    let results = client
        .search_traced(collection_name, query_embedding, 5)
        .await?;
    
    for result in results {
        println!("Score: {:.4}, Content: {:?}", 
            result.score,
            result.payload.get("content")
        );
    }
    
    Ok(())
}
```

### 2. 图片相似度搜索

```rust
// src/examples/image_search.rs
pub async fn image_similarity_search() -> Result<()> {
    let client = QdrantClientWithTracing::new("http://localhost:6334").await?;
    let collection_name = "images";
    
    // 创建 collection (使用图像 embedding 维度)
    client.create_collection(collection_name, 2048, Distance::Euclidean).await?;
    
    // 使用 CLIP 或 ResNet 生成图像 embeddings
    // (这里简化处理)
    let image_embeddings = generate_image_embeddings(&["image1.jpg", "image2.jpg"])?;
    
    // 插入图像向量
    for (i, embedding) in image_embeddings.into_iter().enumerate() {
        let payload = serde_json::json!({
            "filename": format!("image{}.jpg", i + 1),
            "category": "nature",
        });
        
        client.upsert_vector(
            collection_name,
            Uuid::new_v4(),
            embedding,
            payload,
        ).await?;
    }
    
    // 查询相似图片
    let query_image_embedding = generate_image_embeddings(&["query.jpg"])?[0].clone();
    
    let similar_images = client
        .search_traced(collection_name, query_image_embedding, 10)
        .await?;
    
    for (rank, image) in similar_images.iter().enumerate() {
        println!("Rank {}: {:?} (similarity: {:.4})",
            rank + 1,
            image.payload.get("filename"),
            image.score
        );
    }
    
    Ok(())
}
```

---

## 最佳实践

### 1. 性能优化

```rust
// 批量插入优化
pub async fn optimized_bulk_insert(
    &self,
    collection_name: &str,
    documents: Vec<Document>,
) -> Result<()> {
    const OPTIMAL_BATCH_SIZE: usize = 100;
    
    // 并行批量插入
    let chunks: Vec<_> = documents
        .chunks(OPTIMAL_BATCH_SIZE)
        .map(|chunk| chunk.to_vec())
        .collect();
    
    let tasks: Vec<_> = chunks
        .into_iter()
        .map(|chunk| {
            let client = self.clone();
            let collection = collection_name.to_string();
            tokio::spawn(async move {
                client.upsert_documents(&collection, chunk).await
            })
        })
        .collect();
    
    for task in tasks {
        task.await??;
    }
    
    Ok(())
}
```

### 2. 数据管理

```rust
// 定期清理旧数据
pub async fn cleanup_old_vectors(
    &self,
    collection_name: &str,
    older_than_days: i64,
) -> Result<()> {
    let cutoff_timestamp = chrono::Utc::now()
        .timestamp() - (older_than_days * 86400);
    
    let filter = Filter::must([
        Condition::range("metadata.timestamp", Range {
            lt: Some(cutoff_timestamp as f64),
            ..Default::default()
        }),
    ]);
    
    self.client
        .delete_points_by_filter(collection_name, &filter)
        .await?;
    
    Ok(())
}
```

### 3. 监控告警

```yaml
# Prometheus 告警规则
groups:
  - name: qdrant_alerts
    rules:
      - alert: QdrantHighLatency
        expr: histogram_quantile(0.95, rate(qdrant_search_duration_bucket[5m])) > 100
        for: 5m
        annotations:
          summary: "Qdrant search latency is high"
      
      - alert: QdrantLowHitRate
        expr: rate(qdrant_search_count[5m]) == 0
        for: 10m
        annotations:
          summary: "No searches in last 10 minutes"
```

---

## 总结

### 核心要点

1. **Qdrant**: 原生 Rust 向量数据库
2. **OTLP**: 追踪向量操作全流程
3. **高性能**: HNSW 索引 + Rust 性能
4. **灵活过滤**: 结合向量搜索和结构化查询
5. **云原生**: Kubernetes-ready

### Qdrant vs 其他向量数据库

| 特性 | Qdrant | Milvus | Weaviate | Pinecone |
|------|--------|--------|----------|----------|
| **语言** | Rust | C++/Python | Go | Managed |
| **性能** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ |
| **过滤** | ✅ 强大 | ✅ | ✅ | ⚠️ 有限 |
| **部署** | Self-hosted | Self-hosted | Self-hosted | Cloud |
| **价格** | 开源免费 | 开源免费 | 开源免费 | 付费 |

### 下一步

- **Hybrid Search**: 结合全文搜索 + 向量搜索
- **Quantization**: 向量量化降低内存
- **Multi-tenancy**: 多租户隔离

---

## 参考资料

- [Qdrant 官方文档](https://qdrant.tech/documentation/)
- [Qdrant Rust Client](https://github.com/qdrant/rust-client)
- [Vector Database Benchmark](https://github.com/qdrant/vector-db-benchmark)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-11  
**Rust 版本**: 1.90+  
**Qdrant 版本**: 1.9+  
**OpenTelemetry**: 0.30+
