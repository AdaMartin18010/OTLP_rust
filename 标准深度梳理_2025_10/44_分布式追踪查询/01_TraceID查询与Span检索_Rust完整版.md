# TraceID 查询与 Span 检索 - Rust 完整实现

> **文档版本**: v1.0.0  
> **Rust 版本**: 1.90+  
> **最后更新**: 2025-10-10

---

## 📋 目录

- [TraceID 查询与 Span 检索 - Rust 完整实现](#traceid-查询与-span-检索---rust-完整实现)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [核心功能](#核心功能)
    - [技术挑战](#技术挑战)
  - [🔍 TraceID 精确查询](#-traceid-精确查询)
    - [1. TraceID 查询器](#1-traceid-查询器)
    - [2. 分区定位器](#2-分区定位器)
    - [3. 并行查询执行器](#3-并行查询执行器)
  - [📊 Span 属性检索](#-span-属性检索)
    - [1. Span 过滤器](#1-span-过滤器)
    - [2. 属性索引查询](#2-属性索引查询)
    - [3. 复合条件查询](#3-复合条件查询)
  - [🔗 Span 关联查询](#-span-关联查询)
    - [1. 父子关系查询](#1-父子关系查询)
    - [2. Trace 重建器](#2-trace-重建器)
    - [3. 依赖图构建](#3-依赖图构建)
  - [⚡ 性能优化](#-性能优化)
    - [1. 查询缓存](#1-查询缓存)
    - [2. 预取策略](#2-预取策略)
    - [3. 批量查询](#3-批量查询)
  - [📈 聚合统计](#-聚合统计)
    - [1. Span 统计器](#1-span-统计器)
    - [2. 时间范围聚合](#2-时间范围聚合)
  - [🔄 流式查询](#-流式查询)
    - [1. 流式 TraceID 查询](#1-流式-traceid-查询)
    - [2. 分页查询](#2-分页查询)
  - [📊 完整示例：分布式 Trace 查询系统](#-完整示例分布式-trace-查询系统)
  - [🎯 最佳实践](#-最佳实践)
    - [查询优化](#查询优化)
    - [缓存策略](#缓存策略)
    - [错误处理](#错误处理)
  - [📚 参考资源](#-参考资源)

---

## 🎯 概述

分布式追踪查询是 OTLP 系统的核心功能，需要高效地从海量数据中精确定位 TraceID、检索相关 Span 并重建完整的调用链路。

### 核心功能

- ✅ **TraceID 精确查询** - 快速定位特定 Trace
- ✅ **Span 属性检索** - 基于属性过滤 Span
- ✅ **关联查询** - 父子关系、依赖图构建
- ✅ **性能优化** - 缓存、预取、批量查询
- ✅ **流式查询** - 大结果集分页处理
- ✅ **聚合统计** - Trace 级别的统计分析

### 技术挑战

- 🔧 **数据分散** - Trace 数据分布在多个分区/节点
- 🔧 **关联复杂** - Span 之间的父子关系需要重建
- 🔧 **性能要求** - 毫秒级查询响应
- 🔧 **数据量大** - PB 级数据存储

---

## 🔍 TraceID 精确查询

### 1. TraceID 查询器

```rust
use std::sync::Arc;
use tokio::sync::RwLock;
use std::collections::HashMap;
use chrono::{DateTime, Utc};

/// TraceID 查询器
pub struct TraceIdQueryEngine {
    shard_manager: Arc<ShardManager>,
    bloom_index: Arc<BloomIndex>,
    lsm_index: Arc<LsmIndex>,
    cache: Arc<TraceCache>,
}

impl TraceIdQueryEngine {
    pub fn new(
        shard_manager: Arc<ShardManager>,
        bloom_index: Arc<BloomIndex>,
        lsm_index: Arc<LsmIndex>,
        cache: Arc<TraceCache>,
    ) -> Self {
        Self {
            shard_manager,
            bloom_index,
            lsm_index,
            cache,
        }
    }
    
    /// 查询单个 TraceID
    pub async fn query_trace(
        &self,
        trace_id: &TraceId,
    ) -> Result<Option<CompleteTrace>, QueryError> {
        // 1. 检查缓存
        if let Some(cached_trace) = self.cache.get(trace_id).await {
            tracing::debug!("TraceID {} found in cache", trace_id);
            return Ok(Some(cached_trace));
        }
        
        // 2. 确定可能的分区
        let partitions = self.shard_manager.get_partitions_for_trace(trace_id).await?;
        
        tracing::debug!("TraceID {} may be in {} partitions", trace_id, partitions.len());
        
        // 3. 并行查询所有可能的分区
        let mut handles = Vec::new();
        
        for partition in partitions {
            let trace_id = trace_id.clone();
            let bloom_index = self.bloom_index.clone();
            let lsm_index = self.lsm_index.clone();
            
            let handle = tokio::spawn(async move {
                // 使用 Bloom Filter 快速排除
                if !bloom_index.might_contain(&partition, &trace_id).await {
                    return None;
                }
                
                // 从 LSM-Tree 查询
                lsm_index.get_trace(&partition, &trace_id).await
            });
            
            handles.push(handle);
        }
        
        // 4. 等待所有查询完成
        for handle in handles {
            if let Ok(Some(trace)) = handle.await {
                // 找到 Trace，放入缓存
                self.cache.put(trace_id.clone(), trace.clone()).await;
                return Ok(Some(trace));
            }
        }
        
        Ok(None)
    }
    
    /// 批量查询多个 TraceID
    pub async fn query_traces_batch(
        &self,
        trace_ids: Vec<TraceId>,
    ) -> Result<Vec<(TraceId, Option<CompleteTrace>)>, QueryError> {
        let mut results = Vec::new();
        
        // 分组：按分区聚合 TraceID
        let mut partition_groups: HashMap<String, Vec<TraceId>> = HashMap::new();
        
        for trace_id in trace_ids {
            let partitions = self.shard_manager.get_partitions_for_trace(&trace_id).await?;
            
            for partition in partitions {
                partition_groups
                    .entry(partition.clone())
                    .or_insert_with(Vec::new)
                    .push(trace_id.clone());
            }
        }
        
        // 并行查询每个分区
        let mut handles = Vec::new();
        
        for (partition, trace_ids) in partition_groups {
            let bloom_index = self.bloom_index.clone();
            let lsm_index = self.lsm_index.clone();
            
            let handle = tokio::spawn(async move {
                let mut batch_results = Vec::new();
                
                for trace_id in trace_ids {
                    if bloom_index.might_contain(&partition, &trace_id).await {
                        let trace = lsm_index.get_trace(&partition, &trace_id).await;
                        batch_results.push((trace_id, trace));
                    } else {
                        batch_results.push((trace_id, None));
                    }
                }
                
                batch_results
            });
            
            handles.push(handle);
        }
        
        // 收集结果
        for handle in handles {
            if let Ok(batch_results) = handle.await {
                results.extend(batch_results);
            }
        }
        
        Ok(results)
    }
}

/// 完整的 Trace
#[derive(Debug, Clone)]
pub struct CompleteTrace {
    pub trace_id: TraceId,
    pub spans: Vec<SpanRecord>,
    pub start_time: DateTime<Utc>,
    pub end_time: DateTime<Utc>,
    pub duration_ms: i64,
    pub service_count: usize,
    pub span_count: usize,
}

#[derive(Debug, Clone)]
pub struct SpanRecord {
    pub span_id: SpanId,
    pub parent_span_id: Option<SpanId>,
    pub trace_id: TraceId,
    pub name: String,
    pub start_time: DateTime<Utc>,
    pub end_time: DateTime<Utc>,
    pub duration_ms: i64,
    pub service_name: String,
    pub attributes: HashMap<String, String>,
    pub status: SpanStatus,
}

#[derive(Debug, Clone)]
pub enum SpanStatus {
    Ok,
    Error { message: String },
}

pub type TraceId = [u8; 16];
pub type SpanId = [u8; 8];

#[derive(Debug)]
pub enum QueryError {
    NotFound,
    PartitionError(String),
    IndexError(String),
    NetworkError(String),
}
```

---

### 2. 分区定位器

```rust
/// 分区定位器
pub struct PartitionLocator {
    time_partitioner: Arc<TimeRangePartitioner>,
    hash_partitioner: Arc<HashPartitioner>,
}

impl PartitionLocator {
    pub fn new(
        time_partitioner: Arc<TimeRangePartitioner>,
        hash_partitioner: Arc<HashPartitioner>,
    ) -> Self {
        Self {
            time_partitioner,
            hash_partitioner,
        }
    }
    
    /// 根据 TraceID 定位分区
    pub async fn locate_partitions(
        &self,
        trace_id: &TraceId,
        time_hint: Option<DateTime<Utc>>,
    ) -> Result<Vec<String>, String> {
        let mut partitions = Vec::new();
        
        if let Some(timestamp) = time_hint {
            // 有时间提示，精确定位
            let time_partition = self.time_partitioner.get_partition(timestamp);
            let hash_key = self.hash_partitioner.hash_trace_id(trace_id);
            
            partitions.push(format!("{}-{}", time_partition, hash_key));
        } else {
            // 无时间提示，需要查询所有可能的时间分区
            let all_time_partitions = self.time_partitioner.get_all_active_partitions().await?;
            
            let hash_key = self.hash_partitioner.hash_trace_id(trace_id);
            
            for time_partition in all_time_partitions {
                partitions.push(format!("{}-{}", time_partition, hash_key));
            }
        }
        
        Ok(partitions)
    }
    
    /// 根据时间范围获取分区
    pub async fn locate_partitions_by_time_range(
        &self,
        start_time: DateTime<Utc>,
        end_time: DateTime<Utc>,
    ) -> Result<Vec<String>, String> {
        let time_partitions = self.time_partitioner
            .get_partitions_in_range(start_time, end_time);
        
        let mut all_partitions = Vec::new();
        
        for time_partition in time_partitions {
            // 每个时间分区包含多个哈希分区
            let hash_partitions = self.hash_partitioner.get_all_partitions();
            
            for hash_key in hash_partitions {
                all_partitions.push(format!("{}-{}", time_partition, hash_key));
            }
        }
        
        Ok(all_partitions)
    }
}
```

---

### 3. 并行查询执行器

```rust
/// 并行查询执行器
pub struct ParallelTraceQueryExecutor {
    query_engine: Arc<TraceIdQueryEngine>,
    worker_pool_size: usize,
}

impl ParallelTraceQueryExecutor {
    pub fn new(query_engine: Arc<TraceIdQueryEngine>, worker_pool_size: usize) -> Self {
        Self {
            query_engine,
            worker_pool_size,
        }
    }
    
    /// 并行查询多个 TraceID
    pub async fn execute_parallel_query(
        &self,
        trace_ids: Vec<TraceId>,
    ) -> Result<Vec<(TraceId, Option<CompleteTrace>)>, QueryError> {
        let chunk_size = (trace_ids.len() + self.worker_pool_size - 1) / self.worker_pool_size;
        
        let mut handles = Vec::new();
        
        for chunk in trace_ids.chunks(chunk_size) {
            let query_engine = self.query_engine.clone();
            let chunk = chunk.to_vec();
            
            let handle = tokio::spawn(async move {
                let mut results = Vec::new();
                
                for trace_id in chunk {
                    match query_engine.query_trace(&trace_id).await {
                        Ok(trace) => results.push((trace_id, trace)),
                        Err(e) => {
                            tracing::error!("Failed to query TraceID {:?}: {:?}", trace_id, e);
                            results.push((trace_id, None));
                        }
                    }
                }
                
                results
            });
            
            handles.push(handle);
        }
        
        let mut all_results = Vec::new();
        
        for handle in handles {
            if let Ok(results) = handle.await {
                all_results.extend(results);
            }
        }
        
        Ok(all_results)
    }
}
```

---

## 📊 Span 属性检索

### 1. Span 过滤器

```rust
/// Span 过滤器
pub struct SpanFilter {
    inverted_index: Arc<InvertedIndex>,
}

impl SpanFilter {
    pub fn new(inverted_index: Arc<InvertedIndex>) -> Self {
        Self { inverted_index }
    }
    
    /// 根据属性过滤 Span
    pub async fn filter_spans_by_attributes(
        &self,
        conditions: Vec<AttributeCondition>,
    ) -> Result<Vec<TraceId>, QueryError> {
        if conditions.is_empty() {
            return Ok(Vec::new());
        }
        
        // 将条件转换为倒排索引查询
        let attribute_queries: Vec<(String, String)> = conditions
            .into_iter()
            .map(|c| (c.key, c.value))
            .collect();
        
        // 使用倒排索引查询
        let trace_ids = self.inverted_index.query_and(attribute_queries).await;
        
        Ok(trace_ids)
    }
    
    /// 根据服务名过滤
    pub async fn filter_by_service(
        &self,
        service_name: &str,
    ) -> Result<Vec<TraceId>, QueryError> {
        let trace_ids = self.inverted_index
            .query("service.name", service_name)
            .await;
        
        Ok(trace_ids)
    }
    
    /// 根据 Span 名称前缀过滤
    pub async fn filter_by_span_name_prefix(
        &self,
        prefix: &str,
    ) -> Result<Vec<TraceId>, QueryError> {
        // 使用 Trie 索引查找匹配的 Span 名称
        let span_names = self.inverted_index
            .trie_index
            .starts_with(prefix)
            .await;
        
        let mut all_trace_ids = Vec::new();
        
        for span_name in span_names {
            let trace_ids = self.inverted_index
                .query("span.name", &span_name)
                .await;
            
            all_trace_ids.extend(trace_ids);
        }
        
        // 去重
        all_trace_ids.sort();
        all_trace_ids.dedup();
        
        Ok(all_trace_ids)
    }
}

#[derive(Debug, Clone)]
pub struct AttributeCondition {
    pub key: String,
    pub value: String,
}
```

---

### 2. 属性索引查询

```rust
/// 属性索引查询器
pub struct AttributeIndexQuery {
    inverted_index: Arc<RwLock<HashMap<(String, String), Vec<TraceId>>>>,
}

impl AttributeIndexQuery {
    pub fn new() -> Self {
        Self {
            inverted_index: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    /// 插入 Span 属性到索引
    pub async fn index_span(
        &self,
        trace_id: TraceId,
        attributes: HashMap<String, String>,
    ) {
        let mut index = self.inverted_index.write().await;
        
        for (key, value) in attributes {
            index
                .entry((key, value))
                .or_insert_with(Vec::new)
                .push(trace_id);
        }
    }
    
    /// 查询属性
    pub async fn query_attribute(
        &self,
        key: &str,
        value: &str,
    ) -> Vec<TraceId> {
        let index = self.inverted_index.read().await;
        
        index
            .get(&(key.to_string(), value.to_string()))
            .cloned()
            .unwrap_or_default()
    }
    
    /// AND 查询（所有条件都满足）
    pub async fn query_and(
        &self,
        conditions: Vec<(String, String)>,
    ) -> Vec<TraceId> {
        if conditions.is_empty() {
            return Vec::new();
        }
        
        let index = self.inverted_index.read().await;
        
        // 获取第一个条件的结果
        let mut result_set: Vec<TraceId> = index
            .get(&conditions[0])
            .cloned()
            .unwrap_or_default();
        
        result_set.sort();
        
        // 对每个后续条件进行交集
        for condition in conditions.iter().skip(1) {
            let mut condition_set = index
                .get(condition)
                .cloned()
                .unwrap_or_default();
            
            condition_set.sort();
            
            // 计算交集
            result_set = result_set
                .into_iter()
                .filter(|id| condition_set.binary_search(id).is_ok())
                .collect();
            
            if result_set.is_empty() {
                break;
            }
        }
        
        result_set
    }
    
    /// OR 查询（任一条件满足）
    pub async fn query_or(
        &self,
        conditions: Vec<(String, String)>,
    ) -> Vec<TraceId> {
        if conditions.is_empty() {
            return Vec::new();
        }
        
        let index = self.inverted_index.read().await;
        
        let mut result_set = Vec::new();
        
        for condition in conditions {
            if let Some(ids) = index.get(&condition) {
                result_set.extend_from_slice(ids);
            }
        }
        
        // 去重
        result_set.sort();
        result_set.dedup();
        
        result_set
    }
}
```

---

### 3. 复合条件查询

```rust
/// 复合条件查询器
pub struct CompositeQueryEngine {
    span_filter: Arc<SpanFilter>,
    time_range_index: Arc<TimeRangeIndex>,
}

impl CompositeQueryEngine {
    pub fn new(
        span_filter: Arc<SpanFilter>,
        time_range_index: Arc<TimeRangeIndex>,
    ) -> Self {
        Self {
            span_filter,
            time_range_index,
        }
    }
    
    /// 执行复合查询
    pub async fn execute_composite_query(
        &self,
        query: CompositeQuery,
    ) -> Result<Vec<TraceId>, QueryError> {
        let mut candidate_trace_ids: Option<Vec<TraceId>> = None;
        
        // 1. 时间范围过滤（最高选择性）
        if let Some(time_range) = query.time_range {
            let time_filtered = self.time_range_index
                .query_range(time_range.start, time_range.end)
                .await;
            
            candidate_trace_ids = Some(time_filtered);
        }
        
        // 2. 属性过滤
        if !query.attributes.is_empty() {
            let attribute_filtered = self.span_filter
                .filter_spans_by_attributes(query.attributes)
                .await?;
            
            candidate_trace_ids = match candidate_trace_ids {
                Some(existing) => {
                    // 计算交集
                    let intersection = Self::intersect(existing, attribute_filtered);
                    Some(intersection)
                }
                None => Some(attribute_filtered),
            };
        }
        
        // 3. 服务名过滤
        if let Some(service_name) = query.service_name {
            let service_filtered = self.span_filter
                .filter_by_service(&service_name)
                .await?;
            
            candidate_trace_ids = match candidate_trace_ids {
                Some(existing) => {
                    let intersection = Self::intersect(existing, service_filtered);
                    Some(intersection)
                }
                None => Some(service_filtered),
            };
        }
        
        Ok(candidate_trace_ids.unwrap_or_default())
    }
    
    /// 计算两个有序列表的交集
    fn intersect(mut a: Vec<TraceId>, mut b: Vec<TraceId>) -> Vec<TraceId> {
        a.sort();
        b.sort();
        
        let mut result = Vec::new();
        let mut i = 0;
        let mut j = 0;
        
        while i < a.len() && j < b.len() {
            match a[i].cmp(&b[j]) {
                std::cmp::Ordering::Equal => {
                    result.push(a[i]);
                    i += 1;
                    j += 1;
                }
                std::cmp::Ordering::Less => i += 1,
                std::cmp::Ordering::Greater => j += 1,
            }
        }
        
        result
    }
}

#[derive(Debug, Clone)]
pub struct CompositeQuery {
    pub time_range: Option<TimeRange>,
    pub service_name: Option<String>,
    pub attributes: Vec<AttributeCondition>,
}

#[derive(Debug, Clone)]
pub struct TimeRange {
    pub start: DateTime<Utc>,
    pub end: DateTime<Utc>,
}
```

---

## 🔗 Span 关联查询

### 1. 父子关系查询

```rust
/// Span 关联查询器
pub struct SpanRelationshipQuery {
    trace_query_engine: Arc<TraceIdQueryEngine>,
}

impl SpanRelationshipQuery {
    pub fn new(trace_query_engine: Arc<TraceIdQueryEngine>) -> Self {
        Self { trace_query_engine }
    }
    
    /// 查询 Span 的所有子 Span
    pub async fn get_children(
        &self,
        trace_id: &TraceId,
        parent_span_id: &SpanId,
    ) -> Result<Vec<SpanRecord>, QueryError> {
        let trace = self.trace_query_engine
            .query_trace(trace_id)
            .await?
            .ok_or(QueryError::NotFound)?;
        
        let children: Vec<SpanRecord> = trace
            .spans
            .into_iter()
            .filter(|span| {
                span.parent_span_id.as_ref() == Some(parent_span_id)
            })
            .collect();
        
        Ok(children)
    }
    
    /// 查询 Span 的父 Span
    pub async fn get_parent(
        &self,
        trace_id: &TraceId,
        span_id: &SpanId,
    ) -> Result<Option<SpanRecord>, QueryError> {
        let trace = self.trace_query_engine
            .query_trace(trace_id)
            .await?
            .ok_or(QueryError::NotFound)?;
        
        // 找到当前 Span
        let current_span = trace
            .spans
            .iter()
            .find(|span| &span.span_id == span_id)
            .ok_or(QueryError::NotFound)?;
        
        // 查找父 Span
        if let Some(parent_id) = &current_span.parent_span_id {
            let parent = trace
                .spans
                .into_iter()
                .find(|span| &span.span_id == parent_id);
            
            Ok(parent)
        } else {
            Ok(None)
        }
    }
    
    /// 查询 Span 的所有祖先
    pub async fn get_ancestors(
        &self,
        trace_id: &TraceId,
        span_id: &SpanId,
    ) -> Result<Vec<SpanRecord>, QueryError> {
        let trace = self.trace_query_engine
            .query_trace(trace_id)
            .await?
            .ok_or(QueryError::NotFound)?;
        
        let mut ancestors = Vec::new();
        let mut current_span_id = *span_id;
        
        loop {
            // 查找当前 Span
            let current_span = trace
                .spans
                .iter()
                .find(|span| span.span_id == current_span_id);
            
            match current_span {
                Some(span) => {
                    if let Some(parent_id) = span.parent_span_id {
                        // 找到父 Span
                        if let Some(parent_span) = trace.spans.iter().find(|s| s.span_id == parent_id) {
                            ancestors.push(parent_span.clone());
                            current_span_id = parent_id;
                        } else {
                            break;
                        }
                    } else {
                        // 没有父 Span，结束
                        break;
                    }
                }
                None => break,
            }
        }
        
        Ok(ancestors)
    }
}
```

---

### 2. Trace 重建器

```rust
/// Trace 重建器
pub struct TraceReconstructor {
    trace_query_engine: Arc<TraceIdQueryEngine>,
}

impl TraceReconstructor {
    pub fn new(trace_query_engine: Arc<TraceIdQueryEngine>) -> Self {
        Self { trace_query_engine }
    }
    
    /// 重建完整的 Trace 树
    pub async fn reconstruct_trace_tree(
        &self,
        trace_id: &TraceId,
    ) -> Result<TraceTree, QueryError> {
        let trace = self.trace_query_engine
            .query_trace(trace_id)
            .await?
            .ok_or(QueryError::NotFound)?;
        
        // 构建 Span 映射
        let mut span_map: HashMap<SpanId, SpanRecord> = trace
            .spans
            .into_iter()
            .map(|span| (span.span_id, span))
            .collect();
        
        // 找到根 Span（没有父 Span 的）
        let root_spans: Vec<SpanRecord> = span_map
            .values()
            .filter(|span| span.parent_span_id.is_none())
            .cloned()
            .collect();
        
        // 构建树
        let mut root_nodes = Vec::new();
        
        for root_span in root_spans {
            let root_node = self.build_tree_node(root_span, &span_map);
            root_nodes.push(root_node);
        }
        
        Ok(TraceTree {
            trace_id: *trace_id,
            root_nodes,
        })
    }
    
    /// 递归构建树节点
    fn build_tree_node(
        &self,
        span: SpanRecord,
        span_map: &HashMap<SpanId, SpanRecord>,
    ) -> TraceTreeNode {
        // 查找子 Span
        let children: Vec<SpanRecord> = span_map
            .values()
            .filter(|child| child.parent_span_id == Some(span.span_id))
            .cloned()
            .collect();
        
        let child_nodes: Vec<TraceTreeNode> = children
            .into_iter()
            .map(|child| self.build_tree_node(child, span_map))
            .collect();
        
        TraceTreeNode {
            span,
            children: child_nodes,
        }
    }
}

#[derive(Debug, Clone)]
pub struct TraceTree {
    pub trace_id: TraceId,
    pub root_nodes: Vec<TraceTreeNode>,
}

#[derive(Debug, Clone)]
pub struct TraceTreeNode {
    pub span: SpanRecord,
    pub children: Vec<TraceTreeNode>,
}
```

---

### 3. 依赖图构建

```rust
/// 依赖图构建器
pub struct DependencyGraphBuilder {
    trace_reconstructor: Arc<TraceReconstructor>,
}

impl DependencyGraphBuilder {
    pub fn new(trace_reconstructor: Arc<TraceReconstructor>) -> Self {
        Self { trace_reconstructor }
    }
    
    /// 构建服务依赖图
    pub async fn build_service_dependency_graph(
        &self,
        trace_id: &TraceId,
    ) -> Result<ServiceDependencyGraph, QueryError> {
        let trace_tree = self.trace_reconstructor
            .reconstruct_trace_tree(trace_id)
            .await?;
        
        let mut graph = ServiceDependencyGraph {
            nodes: HashMap::new(),
            edges: Vec::new(),
        };
        
        // 遍历树，构建依赖关系
        for root in trace_tree.root_nodes {
            self.traverse_and_build_graph(None, &root, &mut graph);
        }
        
        Ok(graph)
    }
    
    /// 遍历并构建图
    fn traverse_and_build_graph(
        &self,
        parent_service: Option<String>,
        node: &TraceTreeNode,
        graph: &mut ServiceDependencyGraph,
    ) {
        let current_service = node.span.service_name.clone();
        
        // 添加节点
        graph.nodes
            .entry(current_service.clone())
            .or_insert_with(|| ServiceNode {
                service_name: current_service.clone(),
                span_count: 0,
                total_duration_ms: 0,
            })
            .span_count += 1;
        
        graph.nodes
            .get_mut(&current_service)
            .unwrap()
            .total_duration_ms += node.span.duration_ms;
        
        // 添加边
        if let Some(parent) = parent_service {
            if parent != current_service {
                graph.edges.push(ServiceDependencyEdge {
                    from: parent,
                    to: current_service.clone(),
                    call_count: 1,
                });
            }
        }
        
        // 递归处理子节点
        for child in &node.children {
            self.traverse_and_build_graph(Some(current_service.clone()), child, graph);
        }
    }
}

#[derive(Debug, Clone)]
pub struct ServiceDependencyGraph {
    pub nodes: HashMap<String, ServiceNode>,
    pub edges: Vec<ServiceDependencyEdge>,
}

#[derive(Debug, Clone)]
pub struct ServiceNode {
    pub service_name: String,
    pub span_count: usize,
    pub total_duration_ms: i64,
}

#[derive(Debug, Clone)]
pub struct ServiceDependencyEdge {
    pub from: String,
    pub to: String,
    pub call_count: usize,
}
```

---

## ⚡ 性能优化

### 1. 查询缓存

```rust
use lru::LruCache;
use std::num::NonZeroUsize;

/// Trace 缓存
pub struct TraceCache {
    cache: Arc<tokio::sync::Mutex<LruCache<TraceId, CompleteTrace>>>,
}

impl TraceCache {
    pub fn new(capacity: usize) -> Self {
        Self {
            cache: Arc::new(tokio::sync::Mutex::new(
                LruCache::new(NonZeroUsize::new(capacity).unwrap())
            )),
        }
    }
    
    /// 获取缓存
    pub async fn get(&self, trace_id: &TraceId) -> Option<CompleteTrace> {
        let mut cache = self.cache.lock().await;
        cache.get(trace_id).cloned()
    }
    
    /// 放入缓存
    pub async fn put(&self, trace_id: TraceId, trace: CompleteTrace) {
        let mut cache = self.cache.lock().await;
        cache.put(trace_id, trace);
    }
    
    /// 清除缓存
    pub async fn invalidate(&self, trace_id: &TraceId) {
        let mut cache = self.cache.lock().await;
        cache.pop(trace_id);
    }
    
    /// 获取缓存统计
    pub async fn get_stats(&self) -> CacheStats {
        let cache = self.cache.lock().await;
        
        CacheStats {
            size: cache.len(),
            capacity: cache.cap().get(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct CacheStats {
    pub size: usize,
    pub capacity: usize,
}
```

---

### 2. 预取策略

```rust
/// 预取管理器
pub struct PrefetchManager {
    trace_query_engine: Arc<TraceIdQueryEngine>,
    cache: Arc<TraceCache>,
}

impl PrefetchManager {
    pub fn new(
        trace_query_engine: Arc<TraceIdQueryEngine>,
        cache: Arc<TraceCache>,
    ) -> Self {
        Self {
            trace_query_engine,
            cache,
        }
    }
    
    /// 预取相关的 Trace
    pub async fn prefetch_related_traces(
        &self,
        trace_id: &TraceId,
    ) -> Result<(), QueryError> {
        // 查询当前 Trace
        let trace = self.trace_query_engine
            .query_trace(trace_id)
            .await?
            .ok_or(QueryError::NotFound)?;
        
        // 提取相关的 TraceID（例如，从属性中）
        let related_trace_ids = self.extract_related_trace_ids(&trace);
        
        // 异步预取
        for related_id in related_trace_ids {
            let query_engine = self.trace_query_engine.clone();
            let cache = self.cache.clone();
            
            tokio::spawn(async move {
                if let Ok(Some(related_trace)) = query_engine.query_trace(&related_id).await {
                    cache.put(related_id, related_trace).await;
                }
            });
        }
        
        Ok(())
    }
    
    fn extract_related_trace_ids(&self, trace: &CompleteTrace) -> Vec<TraceId> {
        let mut related_ids = Vec::new();
        
        for span in &trace.spans {
            // 从属性中提取相关的 TraceID
            if let Some(related_trace_str) = span.attributes.get("related.trace_id") {
                // 解析 TraceID
                if let Ok(related_id) = Self::parse_trace_id(related_trace_str) {
                    related_ids.push(related_id);
                }
            }
        }
        
        related_ids
    }
    
    fn parse_trace_id(s: &str) -> Result<TraceId, ()> {
        let bytes = hex::decode(s).map_err(|_| ())?;
        
        if bytes.len() != 16 {
            return Err(());
        }
        
        let mut trace_id = [0u8; 16];
        trace_id.copy_from_slice(&bytes);
        
        Ok(trace_id)
    }
}
```

---

### 3. 批量查询

```rust
/// 批量查询优化器
pub struct BatchQueryOptimizer {
    query_engine: Arc<TraceIdQueryEngine>,
}

impl BatchQueryOptimizer {
    pub fn new(query_engine: Arc<TraceIdQueryEngine>) -> Self {
        Self { query_engine }
    }
    
    /// 批量查询（分组优化）
    pub async fn batch_query_optimized(
        &self,
        trace_ids: Vec<TraceId>,
        batch_size: usize,
    ) -> Result<Vec<(TraceId, Option<CompleteTrace>)>, QueryError> {
        let mut all_results = Vec::new();
        
        for chunk in trace_ids.chunks(batch_size) {
            let results = self.query_engine
                .query_traces_batch(chunk.to_vec())
                .await?;
            
            all_results.extend(results);
        }
        
        Ok(all_results)
    }
}
```

---

## 📈 聚合统计

### 1. Span 统计器

```rust
/// Span 统计器
pub struct SpanAggregator {
    trace_query_engine: Arc<TraceIdQueryEngine>,
}

impl SpanAggregator {
    pub fn new(trace_query_engine: Arc<TraceIdQueryEngine>) -> Self {
        Self { trace_query_engine }
    }
    
    /// 计算 Trace 统计信息
    pub async fn aggregate_trace_stats(
        &self,
        trace_id: &TraceId,
    ) -> Result<TraceStats, QueryError> {
        let trace = self.trace_query_engine
            .query_trace(trace_id)
            .await?
            .ok_or(QueryError::NotFound)?;
        
        let total_duration = trace.duration_ms;
        let span_count = trace.spans.len();
        
        // 统计每个服务的 Span 数量和耗时
        let mut service_stats: HashMap<String, ServiceStats> = HashMap::new();
        
        for span in &trace.spans {
            let stats = service_stats
                .entry(span.service_name.clone())
                .or_insert_with(|| ServiceStats {
                    service_name: span.service_name.clone(),
                    span_count: 0,
                    total_duration_ms: 0,
                    error_count: 0,
                });
            
            stats.span_count += 1;
            stats.total_duration_ms += span.duration_ms;
            
            if matches!(span.status, SpanStatus::Error { .. }) {
                stats.error_count += 1;
            }
        }
        
        // 找到最慢的 Span
        let slowest_span = trace
            .spans
            .iter()
            .max_by_key(|span| span.duration_ms)
            .cloned();
        
        Ok(TraceStats {
            trace_id: *trace_id,
            total_duration_ms: total_duration,
            span_count,
            service_stats: service_stats.into_values().collect(),
            slowest_span,
        })
    }
}

#[derive(Debug, Clone)]
pub struct TraceStats {
    pub trace_id: TraceId,
    pub total_duration_ms: i64,
    pub span_count: usize,
    pub service_stats: Vec<ServiceStats>,
    pub slowest_span: Option<SpanRecord>,
}

#[derive(Debug, Clone)]
pub struct ServiceStats {
    pub service_name: String,
    pub span_count: usize,
    pub total_duration_ms: i64,
    pub error_count: usize,
}
```

---

### 2. 时间范围聚合

```rust
/// 时间范围聚合器
pub struct TimeRangeAggregator {
    trace_query_engine: Arc<TraceIdQueryEngine>,
    span_filter: Arc<SpanFilter>,
}

impl TimeRangeAggregator {
    pub fn new(
        trace_query_engine: Arc<TraceIdQueryEngine>,
        span_filter: Arc<SpanFilter>,
    ) -> Self {
        Self {
            trace_query_engine,
            span_filter,
        }
    }
    
    /// 聚合时间范围内的 Trace 统计
    pub async fn aggregate_time_range(
        &self,
        start_time: DateTime<Utc>,
        end_time: DateTime<Utc>,
        service_name: Option<String>,
    ) -> Result<TimeRangeStats, QueryError> {
        // 1. 根据时间范围和服务名过滤 TraceID
        let query = CompositeQuery {
            time_range: Some(TimeRange {
                start: start_time,
                end: end_time,
            }),
            service_name,
            attributes: Vec::new(),
        };
        
        // 这里需要实现查询引擎...
        let trace_ids: Vec<TraceId> = Vec::new(); // 简化
        
        // 2. 统计
        let mut total_traces = 0;
        let mut total_spans = 0;
        let mut total_duration_ms = 0i64;
        let mut error_count = 0;
        
        for trace_id in trace_ids {
            if let Ok(Some(trace)) = self.trace_query_engine.query_trace(&trace_id).await {
                total_traces += 1;
                total_spans += trace.span_count;
                total_duration_ms += trace.duration_ms;
                
                // 统计错误
                error_count += trace
                    .spans
                    .iter()
                    .filter(|span| matches!(span.status, SpanStatus::Error { .. }))
                    .count();
            }
        }
        
        Ok(TimeRangeStats {
            start_time,
            end_time,
            total_traces,
            total_spans,
            avg_duration_ms: if total_traces > 0 {
                total_duration_ms / total_traces as i64
            } else {
                0
            },
            error_count,
        })
    }
}

#[derive(Debug, Clone)]
pub struct TimeRangeStats {
    pub start_time: DateTime<Utc>,
    pub end_time: DateTime<Utc>,
    pub total_traces: usize,
    pub total_spans: usize,
    pub avg_duration_ms: i64,
    pub error_count: usize,
}
```

---

## 🔄 流式查询

### 1. 流式 TraceID 查询

```rust
use futures::stream::{Stream, StreamExt};
use std::pin::Pin;

/// 流式查询处理器
pub struct StreamingQueryProcessor {
    query_engine: Arc<TraceIdQueryEngine>,
}

impl StreamingQueryProcessor {
    pub fn new(query_engine: Arc<TraceIdQueryEngine>) -> Self {
        Self { query_engine }
    }
    
    /// 流式查询多个 TraceID
    pub fn stream_traces(
        &self,
        trace_ids: Vec<TraceId>,
    ) -> Pin<Box<dyn Stream<Item = (TraceId, Option<CompleteTrace>)> + Send>> {
        let query_engine = self.query_engine.clone();
        
        Box::pin(futures::stream::iter(trace_ids).then(move |trace_id| {
            let query_engine = query_engine.clone();
            
            async move {
                let trace = query_engine.query_trace(&trace_id).await.ok().flatten();
                (trace_id, trace)
            }
        }))
    }
}
```

---

### 2. 分页查询

```rust
/// 分页查询器
pub struct PaginatedQueryEngine {
    composite_query: Arc<CompositeQueryEngine>,
    trace_query_engine: Arc<TraceIdQueryEngine>,
}

impl PaginatedQueryEngine {
    pub fn new(
        composite_query: Arc<CompositeQueryEngine>,
        trace_query_engine: Arc<TraceIdQueryEngine>,
    ) -> Self {
        Self {
            composite_query,
            trace_query_engine,
        }
    }
    
    /// 分页查询
    pub async fn query_paginated(
        &self,
        query: CompositeQuery,
        page: usize,
        page_size: usize,
    ) -> Result<PaginatedResult, QueryError> {
        // 1. 执行复合查询，获取所有匹配的 TraceID
        let all_trace_ids = self.composite_query
            .execute_composite_query(query)
            .await?;
        
        let total_count = all_trace_ids.len();
        
        // 2. 计算分页
        let start_idx = page * page_size;
        let end_idx = std::cmp::min(start_idx + page_size, total_count);
        
        if start_idx >= total_count {
            return Ok(PaginatedResult {
                page,
                page_size,
                total_count,
                traces: Vec::new(),
            });
        }
        
        let page_trace_ids = &all_trace_ids[start_idx..end_idx];
        
        // 3. 查询该页的完整 Trace 数据
        let mut traces = Vec::new();
        
        for trace_id in page_trace_ids {
            if let Ok(Some(trace)) = self.trace_query_engine.query_trace(trace_id).await {
                traces.push(trace);
            }
        }
        
        Ok(PaginatedResult {
            page,
            page_size,
            total_count,
            traces,
        })
    }
}

#[derive(Debug, Clone)]
pub struct PaginatedResult {
    pub page: usize,
    pub page_size: usize,
    pub total_count: usize,
    pub traces: Vec<CompleteTrace>,
}
```

---

## 📊 完整示例：分布式 Trace 查询系统

```rust
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt::init();
    
    // 初始化各个组件
    let shard_manager = Arc::new(ShardManager::new());
    let bloom_index = Arc::new(BloomIndex::new());
    let lsm_index = Arc::new(LsmIndex::new());
    let cache = Arc::new(TraceCache::new(1000));
    
    // 创建查询引擎
    let trace_query_engine = Arc::new(TraceIdQueryEngine::new(
        shard_manager.clone(),
        bloom_index.clone(),
        lsm_index.clone(),
        cache.clone(),
    ));
    
    // 创建 Span 过滤器
    let inverted_index = Arc::new(InvertedIndex::new());
    let span_filter = Arc::new(SpanFilter::new(inverted_index.clone()));
    
    // 创建复合查询引擎
    let time_range_index = Arc::new(TimeRangeIndex::new());
    let composite_query = Arc::new(CompositeQueryEngine::new(
        span_filter.clone(),
        time_range_index.clone(),
    ));
    
    // 创建分页查询器
    let paginated_query = Arc::new(PaginatedQueryEngine::new(
        composite_query.clone(),
        trace_query_engine.clone(),
    ));
    
    println!("🎯 分布式 Trace 查询系统已启动！");
    
    // 示例1：查询单个 TraceID
    let trace_id = [1u8; 16];
    
    match trace_query_engine.query_trace(&trace_id).await {
        Ok(Some(trace)) => {
            println!("\n✅ 找到 Trace:");
            println!("  TraceID: {:?}", trace.trace_id);
            println!("  Span 数量: {}", trace.span_count);
            println!("  持续时间: {}ms", trace.duration_ms);
        }
        Ok(None) => println!("\n❌ Trace 未找到"),
        Err(e) => println!("\n⚠️ 查询失败: {:?}", e),
    }
    
    // 示例2：复合条件查询
    let query = CompositeQuery {
        time_range: Some(TimeRange {
            start: Utc::now() - chrono::Duration::hours(1),
            end: Utc::now(),
        }),
        service_name: Some("my-service".to_string()),
        attributes: vec![
            AttributeCondition {
                key: "http.status_code".to_string(),
                value: "500".to_string(),
            },
        ],
    };
    
    let trace_ids = composite_query.execute_composite_query(query).await?;
    
    println!("\n🔍 复合查询结果: 找到 {} 个 Trace", trace_ids.len());
    
    // 示例3：分页查询
    let page_result = paginated_query
        .query_paginated(
            CompositeQuery {
                time_range: Some(TimeRange {
                    start: Utc::now() - chrono::Duration::hours(1),
                    end: Utc::now(),
                }),
                service_name: None,
                attributes: Vec::new(),
            },
            0,
            10,
        )
        .await?;
    
    println!("\n📄 分页查询结果:");
    println!("  页码: {}", page_result.page);
    println!("  每页大小: {}", page_result.page_size);
    println!("  总数: {}", page_result.total_count);
    println!("  当前页 Trace 数: {}", page_result.traces.len());
    
    // 示例4：重建 Trace 树
    let reconstructor = Arc::new(TraceReconstructor::new(trace_query_engine.clone()));
    
    if let Ok(tree) = reconstructor.reconstruct_trace_tree(&trace_id).await {
        println!("\n🌲 Trace 树:");
        println!("  根节点数: {}", tree.root_nodes.len());
        
        for root in &tree.root_nodes {
            print_tree_node(root, 0);
        }
    }
    
    // 示例5：构建服务依赖图
    let dependency_builder = Arc::new(DependencyGraphBuilder::new(reconstructor.clone()));
    
    if let Ok(graph) = dependency_builder.build_service_dependency_graph(&trace_id).await {
        println!("\n🔗 服务依赖图:");
        println!("  服务数: {}", graph.nodes.len());
        println!("  依赖边数: {}", graph.edges.len());
        
        for edge in &graph.edges {
            println!("  {} → {}", edge.from, edge.to);
        }
    }
    
    Ok(())
}

fn print_tree_node(node: &TraceTreeNode, depth: usize) {
    let indent = "  ".repeat(depth);
    
    println!(
        "{}├─ {} ({}ms)",
        indent,
        node.span.name,
        node.span.duration_ms
    );
    
    for child in &node.children {
        print_tree_node(child, depth + 1);
    }
}

// 占位实现
pub struct ShardManager {}
impl ShardManager {
    pub fn new() -> Self { Self {} }
    pub async fn get_partitions_for_trace(&self, _trace_id: &TraceId) -> Result<Vec<String>, QueryError> {
        Ok(vec!["partition_1".to_string()])
    }
}

pub struct BloomIndex {}
impl BloomIndex {
    pub fn new() -> Self { Self {} }
    pub async fn might_contain(&self, _partition: &str, _trace_id: &TraceId) -> bool {
        true
    }
}

pub struct LsmIndex {}
impl LsmIndex {
    pub fn new() -> Self { Self {} }
    pub async fn get_trace(&self, _partition: &str, _trace_id: &TraceId) -> Option<CompleteTrace> {
        None
    }
}

pub struct InvertedIndex {}
impl InvertedIndex {
    pub fn new() -> Self { Self {} }
    pub async fn query_and(&self, _conditions: Vec<(String, String)>) -> Vec<TraceId> {
        Vec::new()
    }
    pub async fn query(&self, _key: &str, _value: &str) -> Vec<TraceId> {
        Vec::new()
    }
    pub trie_index: TrieIndexPlaceholder = TrieIndexPlaceholder {};
}

pub struct TrieIndexPlaceholder {}
impl TrieIndexPlaceholder {
    pub async fn starts_with(&self, _prefix: &str) -> Vec<String> {
        Vec::new()
    }
}

pub struct TimeRangeIndex {}
impl TimeRangeIndex {
    pub fn new() -> Self { Self {} }
    pub async fn query_range(&self, _start: DateTime<Utc>, _end: DateTime<Utc>) -> Vec<TraceId> {
        Vec::new()
    }
}
```

---

## 🎯 最佳实践

### 查询优化

1. **时间范围优先** - 先按时间过滤，减少数据量
2. **Bloom Filter 预过滤** - 避免无效的 LSM-Tree 查询
3. **批量查询** - 减少网络开销

### 缓存策略

1. **热点 Trace 缓存** - LRU 策略
2. **预取相关 Trace** - 根据依赖关系
3. **定期清理** - 避免缓存膨胀

### 错误处理

1. **超时控制** - 避免长时间等待
2. **降级策略** - 部分失败时返回部分结果
3. **重试机制** - 网络错误自动重试

---

## 📚 参考资源

- [Jaeger Query Service](https://www.jaegertracing.io/docs/latest/apis/)
- [Zipkin API](https://zipkin.io/zipkin-api/)
- [OpenTelemetry Trace Query](https://opentelemetry.io/docs/specs/otel/trace/api/)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-10  
**作者**: OTLP Rust 项目组
