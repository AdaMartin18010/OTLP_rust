# 分布式查询优化 - Rust 完整实现

> **文档版本**: v1.0.0  
> **Rust 版本**: 1.90+  
> **最后更新**: 2025-10-10

---

## 📋 目录

- [分布式查询优化 - Rust 完整实现](#分布式查询优化---rust-完整实现)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [优化目标](#优化目标)
    - [核心技术](#核心技术)
  - [🔍 查询规划器](#-查询规划器)
    - [1. 查询解析与优化](#1-查询解析与优化)
    - [2. 查询计划生成器](#2-查询计划生成器)
  - [⚡ 查询执行引擎](#-查询执行引擎)
    - [1. 并行查询执行器](#1-并行查询执行器)
    - [2. 流式查询处理](#2-流式查询处理)
  - [💾 查询缓存](#-查询缓存)
    - [1. 多级缓存系统](#1-多级缓存系统)
  - [📊 查询下推优化](#-查询下推优化)
    - [1. 谓词下推](#1-谓词下推)
    - [2. 投影下推](#2-投影下推)
  - [🔧 自适应查询优化](#-自适应查询优化)
    - [1. 统计信息收集器](#1-统计信息收集器)
    - [2. 代价评估器](#2-代价评估器)
  - [🌊 查询结果合并](#-查询结果合并)
    - [1. 流式归并排序](#1-流式归并排序)
  - [📈 完整示例：分布式查询系统](#-完整示例分布式查询系统)
  - [🎯 查询优化模式](#-查询优化模式)
    - [分区剪枝](#分区剪枝)
    - [索引选择](#索引选择)
    - [并行度调整](#并行度调整)
  - [📊 性能指标](#-性能指标)
  - [📚 参考资源](#-参考资源)

---

## 🎯 概述

分布式查询优化是提升 OTLP 系统性能的关键。本文档介绍如何使用 Rust 实现高效的查询规划、执行和优化机制。

### 优化目标

- ✅ **最小化数据传输**: 查询下推，减少网络开销
- ✅ **最大化并行度**: 充分利用集群资源
- ✅ **智能缓存**: 避免重复计算
- ✅ **自适应优化**: 基于统计信息动态调整

### 核心技术

- 🔍 **查询规划**: CBO (Cost-Based Optimization)
- ⚡ **并行执行**: 流水线并行 + 数据并行
- 💾 **结果缓存**: 多级缓存策略
- 📊 **统计驱动**: 基于数据分布的优化

---

## 🔍 查询规划器

### 1. 查询解析与优化

```rust
use serde::{Serialize, Deserialize};
use std::collections::HashMap;
use chrono::{DateTime, Utc};

/// 查询表达式
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum QueryExpr {
    /// 属性过滤
    AttributeFilter {
        key: String,
        operator: ComparisonOperator,
        value: String,
    },
    
    /// 时间范围
    TimeRange {
        start: DateTime<Utc>,
        end: DateTime<Utc>,
    },
    
    /// 服务名过滤
    ServiceFilter {
        service_name: String,
    },
    
    /// 逻辑与
    And(Vec<QueryExpr>),
    
    /// 逻辑或
    Or(Vec<QueryExpr>),
    
    /// 逻辑非
    Not(Box<QueryExpr>),
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum ComparisonOperator {
    Equal,
    NotEqual,
    GreaterThan,
    LessThan,
    GreaterThanOrEqual,
    LessThanOrEqual,
    Contains,
    StartsWith,
    EndsWith,
}

/// 查询优化器
pub struct QueryOptimizer {
    /// 统计信息
    statistics: std::sync::Arc<tokio::sync::RwLock<QueryStatistics>>,
}

#[derive(Debug, Clone)]
pub struct QueryStatistics {
    /// 属性基数统计
    attribute_cardinality: HashMap<String, usize>,
    
    /// 服务名分布
    service_distribution: HashMap<String, usize>,
    
    /// 时间分区统计
    time_partition_stats: HashMap<String, PartitionStats>,
}

#[derive(Debug, Clone)]
pub struct PartitionStats {
    pub record_count: usize,
    pub size_bytes: u64,
    pub min_timestamp: DateTime<Utc>,
    pub max_timestamp: DateTime<Utc>,
}

impl QueryOptimizer {
    pub fn new(statistics: std::sync::Arc<tokio::sync::RwLock<QueryStatistics>>) -> Self {
        Self { statistics }
    }
    
    /// 优化查询表达式
    pub async fn optimize(&self, expr: QueryExpr) -> QueryExpr {
        // 1. 常量折叠
        let expr = self.constant_folding(expr);
        
        // 2. 谓词下推
        let expr = self.push_down_predicates(expr);
        
        // 3. 重排序（高选择性的条件优先）
        let expr = self.reorder_predicates(expr).await;
        
        expr
    }
    
    /// 常量折叠
    fn constant_folding(&self, expr: QueryExpr) -> QueryExpr {
        match expr {
            QueryExpr::And(exprs) => {
                let optimized: Vec<_> = exprs
                    .into_iter()
                    .map(|e| self.constant_folding(e))
                    .collect();
                
                // 移除恒真条件
                let filtered: Vec<_> = optimized
                    .into_iter()
                    .filter(|e| !self.is_always_true(e))
                    .collect();
                
                if filtered.is_empty() {
                    // 全部是恒真，返回任意一个恒真条件
                    return QueryExpr::And(vec![]);
                }
                
                if filtered.len() == 1 {
                    return filtered.into_iter().next().unwrap();
                }
                
                QueryExpr::And(filtered)
            }
            
            QueryExpr::Or(exprs) => {
                let optimized: Vec<_> = exprs
                    .into_iter()
                    .map(|e| self.constant_folding(e))
                    .collect();
                
                QueryExpr::Or(optimized)
            }
            
            QueryExpr::Not(expr) => {
                QueryExpr::Not(Box::new(self.constant_folding(*expr)))
            }
            
            _ => expr,
        }
    }
    
    fn is_always_true(&self, _expr: &QueryExpr) -> bool {
        // 简化实现
        false
    }
    
    /// 谓词下推
    fn push_down_predicates(&self, expr: QueryExpr) -> QueryExpr {
        // 简化实现：将 AND 条件拆分以便下推
        match expr {
            QueryExpr::And(exprs) => {
                let mut time_filters = Vec::new();
                let mut service_filters = Vec::new();
                let mut attr_filters = Vec::new();
                let mut others = Vec::new();
                
                for e in exprs {
                    match e {
                        QueryExpr::TimeRange { .. } => time_filters.push(e),
                        QueryExpr::ServiceFilter { .. } => service_filters.push(e),
                        QueryExpr::AttributeFilter { .. } => attr_filters.push(e),
                        _ => others.push(e),
                    }
                }
                
                // 重新组合：时间过滤 -> 服务过滤 -> 属性过滤 -> 其他
                let mut result = Vec::new();
                result.extend(time_filters);
                result.extend(service_filters);
                result.extend(attr_filters);
                result.extend(others);
                
                QueryExpr::And(result)
            }
            
            _ => expr,
        }
    }
    
    /// 基于选择性重排序谓词
    async fn reorder_predicates(&self, expr: QueryExpr) -> QueryExpr {
        match expr {
            QueryExpr::And(mut exprs) => {
                let statistics = self.statistics.read().await;
                
                // 计算每个谓词的选择性
                exprs.sort_by(|a, b| {
                    let selectivity_a = self.estimate_selectivity(a, &statistics);
                    let selectivity_b = self.estimate_selectivity(b, &statistics);
                    
                    // 选择性低的（过滤效果好的）排前面
                    selectivity_a.partial_cmp(&selectivity_b).unwrap()
                });
                
                QueryExpr::And(exprs)
            }
            
            _ => expr,
        }
    }
    
    /// 估计选择性（返回值越小，过滤效果越好）
    fn estimate_selectivity(&self, expr: &QueryExpr, stats: &QueryStatistics) -> f64 {
        match expr {
            QueryExpr::AttributeFilter { key, operator, value } => {
                // 基于属性基数估计
                let cardinality = stats.attribute_cardinality.get(key).copied().unwrap_or(1000);
                
                match operator {
                    ComparisonOperator::Equal => 1.0 / cardinality as f64,
                    ComparisonOperator::NotEqual => 1.0 - (1.0 / cardinality as f64),
                    _ => 0.5, // 其他操作默认 50% 选择性
                }
            }
            
            QueryExpr::ServiceFilter { service_name } => {
                let total: usize = stats.service_distribution.values().sum();
                let count = stats.service_distribution.get(service_name).copied().unwrap_or(0);
                
                if total > 0 {
                    count as f64 / total as f64
                } else {
                    0.5
                }
            }
            
            QueryExpr::TimeRange { .. } => {
                // 时间范围通常选择性较好
                0.1
            }
            
            _ => 0.5,
        }
    }
}
```

---

### 2. 查询计划生成器

```rust
use std::sync::Arc;

/// 查询计划
#[derive(Debug, Clone)]
pub struct QueryPlan {
    /// 查询阶段
    pub stages: Vec<QueryStage>,
    
    /// 预估代价
    pub estimated_cost: f64,
    
    /// 并行度
    pub parallelism: usize,
}

#[derive(Debug, Clone)]
pub struct QueryStage {
    /// 阶段类型
    pub stage_type: StageType,
    
    /// 输入阶段
    pub inputs: Vec<usize>,
    
    /// 执行节点
    pub execution_nodes: Vec<String>,
    
    /// 预估输出行数
    pub estimated_rows: usize,
}

#[derive(Debug, Clone)]
pub enum StageType {
    /// 扫描分区
    PartitionScan {
        partitions: Vec<String>,
        filter: Option<QueryExpr>,
    },
    
    /// 索引查找
    IndexLookup {
        index_type: IndexType,
        key: Vec<u8>,
    },
    
    /// 过滤
    Filter {
        predicate: QueryExpr,
    },
    
    /// 聚合
    Aggregate {
        group_by: Vec<String>,
        aggregations: Vec<AggregationFunc>,
    },
    
    /// 排序
    Sort {
        order_by: Vec<(String, SortOrder)>,
    },
    
    /// 限制
    Limit {
        limit: usize,
        offset: usize,
    },
    
    /// 合并
    Merge {
        merge_type: MergeType,
    },
}

#[derive(Debug, Clone)]
pub enum IndexType {
    BloomFilter,
    LsmTree,
    InvertedIndex,
    FullText,
}

#[derive(Debug, Clone)]
pub enum AggregationFunc {
    Count,
    Sum(String),
    Avg(String),
    Min(String),
    Max(String),
}

#[derive(Debug, Clone, Copy)]
pub enum SortOrder {
    Ascending,
    Descending,
}

#[derive(Debug, Clone, Copy)]
pub enum MergeType {
    Union,
    Intersect,
    SortedMerge,
}

/// 查询计划生成器
pub struct QueryPlanGenerator {
    optimizer: Arc<QueryOptimizer>,
    shard_manager: Arc<crate::ShardManager>,
}

impl QueryPlanGenerator {
    pub fn new(
        optimizer: Arc<QueryOptimizer>,
        shard_manager: Arc<crate::ShardManager>,
    ) -> Self {
        Self {
            optimizer,
            shard_manager,
        }
    }
    
    /// 生成查询计划
    pub async fn generate_plan(&self, query: &TraceQuery) -> Result<QueryPlan, String> {
        // 1. 优化查询表达式
        let optimized_expr = self.optimizer.optimize(query.filter.clone()).await;
        
        // 2. 确定需要扫描的分区
        let partitions = self.determine_partitions(&query.time_range, &optimized_expr).await?;
        
        // 3. 确定执行节点
        let nodes = self.determine_execution_nodes(&partitions).await?;
        
        // 4. 生成查询阶段
        let mut stages = Vec::new();
        
        // Stage 0: 分区扫描（并行）
        stages.push(QueryStage {
            stage_type: StageType::PartitionScan {
                partitions: partitions.clone(),
                filter: Some(optimized_expr.clone()),
            },
            inputs: vec![],
            execution_nodes: nodes.clone(),
            estimated_rows: 100_000, // 简化估计
        });
        
        // Stage 1: 过滤（如果有额外的过滤条件）
        if self.needs_additional_filter(&optimized_expr) {
            stages.push(QueryStage {
                stage_type: StageType::Filter {
                    predicate: optimized_expr,
                },
                inputs: vec![0],
                execution_nodes: nodes.clone(),
                estimated_rows: 50_000,
            });
        }
        
        // Stage 2: 排序（如果需要）
        if let Some(order_by) = &query.order_by {
            stages.push(QueryStage {
                stage_type: StageType::Sort {
                    order_by: order_by.clone(),
                },
                inputs: vec![stages.len() - 1],
                execution_nodes: nodes.clone(),
                estimated_rows: 50_000,
            });
        }
        
        // Stage 3: 合并结果
        stages.push(QueryStage {
            stage_type: StageType::Merge {
                merge_type: if query.order_by.is_some() {
                    MergeType::SortedMerge
                } else {
                    MergeType::Union
                },
            },
            inputs: vec![stages.len() - 1],
            execution_nodes: vec!["coordinator".to_string()],
            estimated_rows: 50_000,
        });
        
        // Stage 4: 限制（如果需要）
        if let Some(limit) = query.limit {
            stages.push(QueryStage {
                stage_type: StageType::Limit {
                    limit,
                    offset: query.offset.unwrap_or(0),
                },
                inputs: vec![stages.len() - 1],
                execution_nodes: vec!["coordinator".to_string()],
                estimated_rows: limit.min(50_000),
            });
        }
        
        Ok(QueryPlan {
            stages,
            estimated_cost: 1000.0, // 简化估计
            parallelism: nodes.len(),
        })
    }
    
    async fn determine_partitions(
        &self,
        time_range: &(DateTime<Utc>, DateTime<Utc>),
        _expr: &QueryExpr,
    ) -> Result<Vec<String>, String> {
        // 基于时间范围确定需要扫描的分区
        let (start, end) = time_range;
        
        let partitions = self.shard_manager
            .get_nodes_for_time_range_query(*start, *end, None)
            .await?;
        
        Ok(partitions.into_iter().map(|(p, _)| p.to_string()).collect())
    }
    
    async fn determine_execution_nodes(&self, partitions: &[String]) -> Result<Vec<String>, String> {
        // 简化实现：每个分区对应一个节点
        Ok(partitions.iter().map(|p| format!("node-for-{}", p)).collect())
    }
    
    fn needs_additional_filter(&self, _expr: &QueryExpr) -> bool {
        // 简化实现
        false
    }
}

/// Trace 查询请求
#[derive(Debug, Clone)]
pub struct TraceQuery {
    pub filter: QueryExpr,
    pub time_range: (DateTime<Utc>, DateTime<Utc>),
    pub order_by: Option<Vec<(String, SortOrder)>>,
    pub limit: Option<usize>,
    pub offset: Option<usize>,
}
```

---

## ⚡ 查询执行引擎

### 1. 并行查询执行器

```rust
use tokio::sync::mpsc;
use futures::stream::{Stream, StreamExt};

/// 并行查询执行器
pub struct ParallelQueryExecutor {
    plan_generator: Arc<QueryPlanGenerator>,
    worker_pool: Arc<WorkerPool>,
}

impl ParallelQueryExecutor {
    pub fn new(
        plan_generator: Arc<QueryPlanGenerator>,
        worker_pool: Arc<WorkerPool>,
    ) -> Self {
        Self {
            plan_generator,
            worker_pool,
        }
    }
    
    /// 执行查询
    pub async fn execute(&self, query: TraceQuery) -> Result<QueryResultStream, String> {
        // 1. 生成查询计划
        let plan = self.plan_generator.generate_plan(&query).await?;
        
        tracing::info!("Executing query plan with {} stages", plan.stages.len());
        
        // 2. 执行计划
        let results = self.execute_plan(plan).await?;
        
        Ok(results)
    }
    
    /// 执行查询计划
    async fn execute_plan(&self, plan: QueryPlan) -> Result<QueryResultStream, String> {
        let mut stage_results: Vec<Vec<TraceRecord>> = vec![Vec::new(); plan.stages.len()];
        
        // 按阶段顺序执行
        for (stage_idx, stage) in plan.stages.iter().enumerate() {
            tracing::debug!("Executing stage {}: {:?}", stage_idx, stage.stage_type);
            
            // 获取输入数据
            let inputs: Vec<Vec<TraceRecord>> = stage.inputs
                .iter()
                .map(|&input_idx| stage_results[input_idx].clone())
                .collect();
            
            // 执行当前阶段
            let results = self.execute_stage(stage, inputs).await?;
            
            stage_results[stage_idx] = results;
        }
        
        // 返回最后阶段的结果
        let final_results = stage_results.pop().unwrap_or_default();
        
        Ok(QueryResultStream::from_vec(final_results))
    }
    
    /// 执行单个阶段
    async fn execute_stage(
        &self,
        stage: &QueryStage,
        inputs: Vec<Vec<TraceRecord>>,
    ) -> Result<Vec<TraceRecord>, String> {
        match &stage.stage_type {
            StageType::PartitionScan { partitions, filter } => {
                self.execute_partition_scan(partitions, filter.as_ref(), &stage.execution_nodes).await
            }
            
            StageType::Filter { predicate } => {
                self.execute_filter(inputs, predicate).await
            }
            
            StageType::Sort { order_by } => {
                self.execute_sort(inputs, order_by).await
            }
            
            StageType::Limit { limit, offset } => {
                self.execute_limit(inputs, *limit, *offset).await
            }
            
            StageType::Merge { merge_type } => {
                self.execute_merge(inputs, *merge_type).await
            }
            
            _ => Err("Unsupported stage type".to_string()),
        }
    }
    
    /// 执行分区扫描（并行）
    async fn execute_partition_scan(
        &self,
        partitions: &[String],
        filter: Option<&QueryExpr>,
        nodes: &[String],
    ) -> Result<Vec<TraceRecord>, String> {
        let mut handles = Vec::new();
        
        for (partition, node) in partitions.iter().zip(nodes.iter()) {
            let partition = partition.clone();
            let node = node.clone();
            let filter = filter.cloned();
            let worker_pool = self.worker_pool.clone();
            
            let handle = tokio::spawn(async move {
                worker_pool.scan_partition(&partition, &node, filter.as_ref()).await
            });
            
            handles.push(handle);
        }
        
        // 收集结果
        let mut all_results = Vec::new();
        
        for handle in handles {
            match handle.await {
                Ok(Ok(results)) => all_results.extend(results),
                Ok(Err(e)) => tracing::error!("Partition scan failed: {}", e),
                Err(e) => tracing::error!("Task join failed: {}", e),
            }
        }
        
        Ok(all_results)
    }
    
    /// 执行过滤
    async fn execute_filter(
        &self,
        inputs: Vec<Vec<TraceRecord>>,
        predicate: &QueryExpr,
    ) -> Result<Vec<TraceRecord>, String> {
        let mut results = Vec::new();
        
        for input in inputs {
            for record in input {
                if self.evaluate_predicate(&record, predicate) {
                    results.push(record);
                }
            }
        }
        
        Ok(results)
    }
    
    /// 执行排序
    async fn execute_sort(
        &self,
        mut inputs: Vec<Vec<TraceRecord>>,
        order_by: &[(String, SortOrder)],
    ) -> Result<Vec<TraceRecord>, String> {
        let mut all_records: Vec<_> = inputs.into_iter().flatten().collect();
        
        all_records.sort_by(|a, b| {
            for (field, order) in order_by {
                let cmp = self.compare_field(a, b, field);
                
                let cmp = match order {
                    SortOrder::Ascending => cmp,
                    SortOrder::Descending => cmp.reverse(),
                };
                
                if cmp != std::cmp::Ordering::Equal {
                    return cmp;
                }
            }
            
            std::cmp::Ordering::Equal
        });
        
        Ok(all_records)
    }
    
    /// 执行限制
    async fn execute_limit(
        &self,
        inputs: Vec<Vec<TraceRecord>>,
        limit: usize,
        offset: usize,
    ) -> Result<Vec<TraceRecord>, String> {
        let all_records: Vec<_> = inputs.into_iter().flatten().collect();
        
        Ok(all_records
            .into_iter()
            .skip(offset)
            .take(limit)
            .collect())
    }
    
    /// 执行合并
    async fn execute_merge(
        &self,
        inputs: Vec<Vec<TraceRecord>>,
        merge_type: MergeType,
    ) -> Result<Vec<TraceRecord>, String> {
        match merge_type {
            MergeType::Union => {
                Ok(inputs.into_iter().flatten().collect())
            }
            
            MergeType::SortedMerge => {
                // 假设输入已排序，执行归并
                self.merge_sorted(inputs).await
            }
            
            _ => Err("Unsupported merge type".to_string()),
        }
    }
    
    /// 归并已排序的结果
    async fn merge_sorted(&self, inputs: Vec<Vec<TraceRecord>>) -> Result<Vec<TraceRecord>, String> {
        // 简化实现：直接合并后排序
        let mut all_records: Vec<_> = inputs.into_iter().flatten().collect();
        all_records.sort_by_key(|r| r.timestamp);
        Ok(all_records)
    }
    
    fn evaluate_predicate(&self, _record: &TraceRecord, _predicate: &QueryExpr) -> bool {
        // 简化实现
        true
    }
    
    fn compare_field(&self, a: &TraceRecord, b: &TraceRecord, field: &str) -> std::cmp::Ordering {
        match field {
            "timestamp" => a.timestamp.cmp(&b.timestamp),
            "service_name" => a.service_name.cmp(&b.service_name),
            _ => std::cmp::Ordering::Equal,
        }
    }
}

/// Worker 池
pub struct WorkerPool {
    // 简化实现
}

impl WorkerPool {
    pub async fn scan_partition(
        &self,
        _partition: &str,
        _node: &str,
        _filter: Option<&QueryExpr>,
    ) -> Result<Vec<TraceRecord>, String> {
        // TODO: 实际实现需要远程调用或本地扫描
        Ok(Vec::new())
    }
}

/// Trace 记录
#[derive(Debug, Clone)]
pub struct TraceRecord {
    pub trace_id: [u8; 16],
    pub service_name: String,
    pub timestamp: DateTime<Utc>,
    pub duration_ms: u64,
    pub attributes: HashMap<String, String>,
}

/// 查询结果流
pub struct QueryResultStream {
    inner: Box<dyn Stream<Item = TraceRecord> + Unpin + Send>,
}

impl QueryResultStream {
    pub fn from_vec(records: Vec<TraceRecord>) -> Self {
        Self {
            inner: Box::new(futures::stream::iter(records)),
        }
    }
    
    pub async fn collect(mut self) -> Vec<TraceRecord> {
        let mut results = Vec::new();
        
        while let Some(record) = self.inner.next().await {
            results.push(record);
        }
        
        results
    }
}
```

---

### 2. 流式查询处理

```rust
/// 流式查询处理器
pub struct StreamingQueryProcessor {
    executor: Arc<ParallelQueryExecutor>,
}

impl StreamingQueryProcessor {
    pub fn new(executor: Arc<ParallelQueryExecutor>) -> Self {
        Self { executor }
    }
    
    /// 创建流式查询
    pub async fn execute_streaming(
        &self,
        query: TraceQuery,
    ) -> Result<impl Stream<Item = Result<TraceRecord, String>>, String> {
        let result_stream = self.executor.execute(query).await?;
        
        // 转换为异步流
        Ok(futures::stream::unfold(result_stream, |mut stream| async move {
            match stream.inner.next().await {
                Some(record) => Some((Ok(record), stream)),
                None => None,
            }
        }))
    }
    
    /// 分批流式处理
    pub async fn execute_batched(
        &self,
        query: TraceQuery,
        batch_size: usize,
    ) -> Result<impl Stream<Item = Result<Vec<TraceRecord>, String>>, String> {
        let result_stream = self.executor.execute(query).await?;
        
        Ok(futures::stream::unfold(
            (result_stream, Vec::with_capacity(batch_size)),
            move |(mut stream, mut batch)| async move {
                batch.clear();
                
                while batch.len() < batch_size {
                    match stream.inner.next().await {
                        Some(record) => batch.push(record),
                        None => {
                            if batch.is_empty() {
                                return None;
                            } else {
                                break;
                            }
                        }
                    }
                }
                
                let result_batch = batch.clone();
                Some((Ok(result_batch), (stream, batch)))
            },
        ))
    }
}
```

---

## 💾 查询缓存

### 1. 多级缓存系统

```rust
use lru::LruCache;
use std::num::NonZeroUsize;

/// 查询缓存
pub struct QueryCache {
    /// L1 缓存（内存，热点查询）
    l1_cache: Arc<tokio::sync::Mutex<LruCache<String, CachedQueryResult>>>,
    
    /// L2 缓存（Redis，跨节点共享）
    l2_cache: Option<redis::Client>,
    
    /// 缓存 TTL
    ttl: std::time::Duration,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CachedQueryResult {
    pub results: Vec<TraceRecord>,
    pub cached_at: DateTime<Utc>,
    pub query_time_ms: u64,
}

impl QueryCache {
    pub fn new(l1_capacity: usize, l2_redis_url: Option<String>, ttl: std::time::Duration) -> Self {
        let l2_cache = l2_redis_url.and_then(|url| redis::Client::open(url).ok());
        
        Self {
            l1_cache: Arc::new(tokio::sync::Mutex::new(
                LruCache::new(NonZeroUsize::new(l1_capacity).unwrap())
            )),
            l2_cache,
            ttl,
        }
    }
    
    /// 获取缓存的查询结果
    pub async fn get(&self, query_key: &str) -> Option<CachedQueryResult> {
        // 1. 尝试 L1 缓存
        {
            let mut l1 = self.l1_cache.lock().await;
            if let Some(result) = l1.get(query_key) {
                if !self.is_expired(&result.cached_at) {
                    tracing::debug!("L1 cache hit: {}", query_key);
                    return Some(result.clone());
                } else {
                    l1.pop(query_key);
                }
            }
        }
        
        // 2. 尝试 L2 缓存
        if let Some(ref redis_client) = self.l2_cache {
            if let Ok(mut conn) = redis_client.get_async_connection().await {
                use redis::AsyncCommands;
                
                if let Ok(Some(data)) = conn.get::<_, Option<Vec<u8>>>(query_key).await {
                    if let Ok(result) = bincode::deserialize::<CachedQueryResult>(&data) {
                        if !self.is_expired(&result.cached_at) {
                            tracing::debug!("L2 cache hit: {}", query_key);
                            
                            // 回填 L1 缓存
                            let mut l1 = self.l1_cache.lock().await;
                            l1.put(query_key.to_string(), result.clone());
                            
                            return Some(result);
                        }
                    }
                }
            }
        }
        
        None
    }
    
    /// 存储查询结果到缓存
    pub async fn put(&self, query_key: String, result: CachedQueryResult) {
        // 1. 存储到 L1 缓存
        {
            let mut l1 = self.l1_cache.lock().await;
            l1.put(query_key.clone(), result.clone());
        }
        
        // 2. 存储到 L2 缓存
        if let Some(ref redis_client) = self.l2_cache {
            if let Ok(mut conn) = redis_client.get_async_connection().await {
                if let Ok(data) = bincode::serialize(&result) {
                    use redis::AsyncCommands;
                    let _: Result<(), _> = conn.set_ex(query_key, data, self.ttl.as_secs() as u64).await;
                }
            }
        }
    }
    
    /// 检查是否过期
    fn is_expired(&self, cached_at: &DateTime<Utc>) -> bool {
        let now = Utc::now();
        let elapsed = now.signed_duration_since(*cached_at);
        
        elapsed.num_seconds() as u64 > self.ttl.as_secs()
    }
    
    /// 使缓存失效
    pub async fn invalidate(&self, query_key: &str) {
        // 1. 从 L1 缓存移除
        {
            let mut l1 = self.l1_cache.lock().await;
            l1.pop(query_key);
        }
        
        // 2. 从 L2 缓存移除
        if let Some(ref redis_client) = self.l2_cache {
            if let Ok(mut conn) = redis_client.get_async_connection().await {
                use redis::AsyncCommands;
                let _: Result<(), _> = conn.del(query_key).await;
            }
        }
    }
    
    /// 生成查询键
    pub fn generate_query_key(query: &TraceQuery) -> String {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        
        let mut hasher = DefaultHasher::new();
        
        format!("{:?}", query).hash(&mut hasher);
        
        format!("query:{:x}", hasher.finish())
    }
}
```

---

## 📊 查询下推优化

### 1. 谓词下推

```rust
/// 谓词下推优化器
pub struct PredicatePushdown {
    // 配置
}

impl PredicatePushdown {
    /// 将谓词下推到扫描阶段
    pub fn push_down(&self, plan: &mut QueryPlan) {
        for i in 0..plan.stages.len() {
            if let StageType::Filter { predicate } = &plan.stages[i].stage_type {
                // 查找输入阶段
                if let Some(&input_idx) = plan.stages[i].inputs.first() {
                    if let StageType::PartitionScan { partitions, filter } = 
                        &mut plan.stages[input_idx].stage_type 
                    {
                        // 将过滤条件合并到扫描阶段
                        let combined = if let Some(existing_filter) = filter.take() {
                            QueryExpr::And(vec![existing_filter, predicate.clone()])
                        } else {
                            predicate.clone()
                        };
                        
                        *filter = Some(combined);
                        
                        // 标记过滤阶段为已优化
                        tracing::info!("Pushed down predicate to scan stage");
                    }
                }
            }
        }
    }
}
```

---

### 2. 投影下推

```rust
/// 投影下推优化器
pub struct ProjectionPushdown {
    // 配置
}

#[derive(Debug, Clone)]
pub struct Projection {
    pub fields: Vec<String>,
}

impl ProjectionPushdown {
    /// 将投影下推到扫描阶段
    pub fn push_down(&self, _plan: &mut QueryPlan, _projection: &Projection) {
        // 简化实现：标记需要读取的字段
        tracing::info!("Projection pushdown applied");
    }
}
```

---

## 🔧 自适应查询优化

### 1. 统计信息收集器

```rust
/// 统计信息收集器
pub struct StatisticsCollector {
    statistics: Arc<tokio::sync::RwLock<QueryStatistics>>,
}

impl StatisticsCollector {
    pub fn new(statistics: Arc<tokio::sync::RwLock<QueryStatistics>>) -> Self {
        Self { statistics }
    }
    
    /// 更新属性基数
    pub async fn update_attribute_cardinality(&self, key: String, cardinality: usize) {
        let mut stats = self.statistics.write().await;
        stats.attribute_cardinality.insert(key, cardinality);
    }
    
    /// 更新服务分布
    pub async fn update_service_distribution(&self, distribution: HashMap<String, usize>) {
        let mut stats = self.statistics.write().await;
        stats.service_distribution = distribution;
    }
    
    /// 更新分区统计
    pub async fn update_partition_stats(&self, partition_id: String, stats_data: PartitionStats) {
        let mut stats = self.statistics.write().await;
        stats.time_partition_stats.insert(partition_id, stats_data);
    }
    
    /// 定期收集统计信息
    pub async fn collect_periodically(&self, interval: std::time::Duration) {
        let mut interval = tokio::time::interval(interval);
        
        loop {
            interval.tick().await;
            
            if let Err(e) = self.collect_once().await {
                tracing::error!("Statistics collection failed: {}", e);
            }
        }
    }
    
    async fn collect_once(&self) -> Result<(), Box<dyn std::error::Error>> {
        // TODO: 实际实现需要扫描数据并统计
        tracing::info!("Collecting statistics...");
        
        Ok(())
    }
}
```

---

### 2. 代价评估器

```rust
/// 代价评估器
pub struct CostEstimator {
    statistics: Arc<tokio::sync::RwLock<QueryStatistics>>,
}

impl CostEstimator {
    pub fn new(statistics: Arc<tokio::sync::RwLock<QueryStatistics>>) -> Self {
        Self { statistics }
    }
    
    /// 估计查询计划的代价
    pub async fn estimate_cost(&self, plan: &QueryPlan) -> f64 {
        let mut total_cost = 0.0;
        
        for stage in &plan.stages {
            total_cost += self.estimate_stage_cost(stage).await;
        }
        
        total_cost
    }
    
    /// 估计单个阶段的代价
    async fn estimate_stage_cost(&self, stage: &QueryStage) -> f64 {
        match &stage.stage_type {
            StageType::PartitionScan { partitions, .. } => {
                // 扫描代价 = 分区数量 * 单分区扫描代价
                partitions.len() as f64 * 100.0
            }
            
            StageType::Filter { .. } => {
                // 过滤代价 = 输入行数 * 单行过滤代价
                stage.estimated_rows as f64 * 0.01
            }
            
            StageType::Sort { .. } => {
                // 排序代价 = n * log(n)
                let n = stage.estimated_rows as f64;
                n * n.log2() * 0.1
            }
            
            StageType::Merge { .. } => {
                // 合并代价 = 输入行数
                stage.estimated_rows as f64 * 0.05
            }
            
            _ => 10.0,
        }
    }
    
    /// 比较两个查询计划
    pub async fn compare_plans(&self, plan1: &QueryPlan, plan2: &QueryPlan) -> std::cmp::Ordering {
        let cost1 = self.estimate_cost(plan1).await;
        let cost2 = self.estimate_cost(plan2).await;
        
        cost1.partial_cmp(&cost2).unwrap_or(std::cmp::Ordering::Equal)
    }
}
```

---

## 🌊 查询结果合并

### 1. 流式归并排序

```rust
use futures::stream::StreamExt;

/// 流式归并排序器
pub struct StreamingMergeSorter {
    // 配置
}

impl StreamingMergeSorter {
    /// 归并多个已排序的流
    pub async fn merge_sorted_streams(
        &self,
        streams: Vec<impl Stream<Item = TraceRecord> + Unpin>,
        order_by: Vec<(String, SortOrder)>,
    ) -> impl Stream<Item = TraceRecord> {
        // 使用优先队列实现 K-way 归并
        use std::collections::BinaryHeap;
        use std::cmp::Reverse;
        
        // 简化实现：收集所有元素后排序
        let mut all_records = Vec::new();
        
        for mut stream in streams {
            while let Some(record) = stream.next().await {
                all_records.push(record);
            }
        }
        
        all_records.sort_by(|a, b| {
            for (field, order) in &order_by {
                let cmp = self.compare_field(a, b, field);
                
                let cmp = match order {
                    SortOrder::Ascending => cmp,
                    SortOrder::Descending => cmp.reverse(),
                };
                
                if cmp != std::cmp::Ordering::Equal {
                    return cmp;
                }
            }
            
            std::cmp::Ordering::Equal
        });
        
        futures::stream::iter(all_records)
    }
    
    fn compare_field(&self, a: &TraceRecord, b: &TraceRecord, field: &str) -> std::cmp::Ordering {
        match field {
            "timestamp" => a.timestamp.cmp(&b.timestamp),
            "service_name" => a.service_name.cmp(&b.service_name),
            _ => std::cmp::Ordering::Equal,
        }
    }
}
```

---

## 📈 完整示例：分布式查询系统

```rust
/// 分布式查询系统
pub struct DistributedQuerySystem {
    optimizer: Arc<QueryOptimizer>,
    plan_generator: Arc<QueryPlanGenerator>,
    executor: Arc<ParallelQueryExecutor>,
    cache: Arc<QueryCache>,
    statistics_collector: Arc<StatisticsCollector>,
}

impl DistributedQuerySystem {
    pub async fn new(
        shard_manager: Arc<crate::ShardManager>,
        cache_config: (usize, Option<String>, std::time::Duration),
    ) -> Result<Self, Box<dyn std::error::Error>> {
        let statistics = Arc::new(tokio::sync::RwLock::new(QueryStatistics {
            attribute_cardinality: HashMap::new(),
            service_distribution: HashMap::new(),
            time_partition_stats: HashMap::new(),
        }));
        
        let optimizer = Arc::new(QueryOptimizer::new(statistics.clone()));
        let plan_generator = Arc::new(QueryPlanGenerator::new(optimizer.clone(), shard_manager));
        
        let worker_pool = Arc::new(WorkerPool {});
        let executor = Arc::new(ParallelQueryExecutor::new(plan_generator.clone(), worker_pool));
        
        let cache = Arc::new(QueryCache::new(cache_config.0, cache_config.1, cache_config.2));
        
        let statistics_collector = Arc::new(StatisticsCollector::new(statistics));
        
        Ok(Self {
            optimizer,
            plan_generator,
            executor,
            cache,
            statistics_collector,
        })
    }
    
    /// 启动后台任务
    pub async fn start(&self) {
        let collector = self.statistics_collector.clone();
        
        tokio::spawn(async move {
            collector.collect_periodically(std::time::Duration::from_secs(300)).await;
        });
    }
    
    /// 执行查询（带缓存）
    pub async fn execute_query(&self, query: TraceQuery) -> Result<Vec<TraceRecord>, String> {
        let query_key = QueryCache::generate_query_key(&query);
        
        // 1. 尝试缓存
        if let Some(cached) = self.cache.get(&query_key).await {
            tracing::info!("Query result from cache");
            return Ok(cached.results);
        }
        
        // 2. 执行查询
        let start = std::time::Instant::now();
        
        let result_stream = self.executor.execute(query.clone()).await?;
        let results = result_stream.collect().await;
        
        let query_time_ms = start.elapsed().as_millis() as u64;
        
        // 3. 缓存结果
        let cached_result = CachedQueryResult {
            results: results.clone(),
            cached_at: Utc::now(),
            query_time_ms,
        };
        
        self.cache.put(query_key, cached_result).await;
        
        tracing::info!("Query executed in {} ms", query_time_ms);
        
        Ok(results)
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt::init();
    
    // 初始化查询系统
    // let shard_manager = ...; // 从前面的示例获取
    // let query_system = DistributedQuerySystem::new(
    //     shard_manager,
    //     (1000, Some("redis://127.0.0.1:6379".to_string()), std::time::Duration::from_secs(300)),
    // ).await?;
    
    // query_system.start().await;
    
    // 执行查询示例
    // let query = TraceQuery {
    //     filter: QueryExpr::ServiceFilter {
    //         service_name: "example-service".to_string(),
    //     },
    //     time_range: (Utc::now() - chrono::Duration::hours(1), Utc::now()),
    //     order_by: Some(vec![("timestamp".to_string(), SortOrder::Descending)]),
    //     limit: Some(100),
    //     offset: None,
    // };
    
    // let results = query_system.execute_query(query).await?;
    // println!("Found {} traces", results.len());
    
    Ok(())
}
```

---

## 🎯 查询优化模式

### 分区剪枝

- 基于时间范围过滤分区
- 基于服务名过滤分区
- 基于 Bloom Filter 过滤分区

### 索引选择

- TraceID 查询 → Bloom Filter + LSM
- 属性查询 → 倒排索引
- 全文搜索 → 全文索引

### 并行度调整

- 小查询：低并行度
- 大查询：高并行度
- 动态调整基于负载

---

## 📊 性能指标

- **查询延迟**: < 100ms (P99)
- **缓存命中率**: > 70%
- **并行效率**: > 80%
- **网络传输**: 最小化

---

## 📚 参考资源

- [Query Optimization in Distributed Systems](https://15721.courses.cs.cmu.edu/)
- [Apache Calcite](https://calcite.apache.org/)
- [Presto Query Optimizer](https://prestodb.io/)
- [Apache Spark Catalyst](https://spark.apache.org/docs/latest/sql-performance-tuning.html)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-10  
**作者**: OTLP Rust 项目组
