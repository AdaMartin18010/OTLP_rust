# 分布式数据建模与分区策略 - Rust 完整实现

> **文档版本**: v1.0.0  
> **Rust 版本**: 1.90+  
> **最后更新**: 2025-10-10

---

## 📋 目录

- [分布式数据建模与分区策略 - Rust 完整实现](#分布式数据建模与分区策略---rust-完整实现)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [核心目标](#核心目标)
    - [关键挑战](#关键挑战)
  - [🏗️ 分布式数据模型设计](#️-分布式数据模型设计)
    - [1. Trace 数据模型](#1-trace-数据模型)
    - [2. Metric 数据模型](#2-metric-数据模型)
    - [3. Log 数据模型](#3-log-数据模型)
  - [📊 数据分区策略](#-数据分区策略)
    - [1. 时间范围分区 (Time-Range Partitioning)](#1-时间范围分区-time-range-partitioning)
    - [2. 哈希分区 (Hash Partitioning)](#2-哈希分区-hash-partitioning)
    - [3. 范围分区 (Range Partitioning)](#3-范围分区-range-partitioning)
    - [4. 复合分区策略](#4-复合分区策略)
  - [🔍 数据定位与路由](#-数据定位与路由)
    - [1. 一致性哈希路由](#1-一致性哈希路由)
    - [2. 元数据服务](#2-元数据服务)
    - [3. 分片管理器](#3-分片管理器)
  - [⚡ 分区重平衡](#-分区重平衡)
    - [1. 自动重平衡管理器](#1-自动重平衡管理器)
  - [💾 数据本地化优化](#-数据本地化优化)
    - [1. 数据局部性感知路由](#1-数据局部性感知路由)
  - [📈 完整示例：分布式 OTLP 存储系统](#-完整示例分布式-otlp-存储系统)
  - [🎯 最佳实践](#-最佳实践)
    - [分区大小](#分区大小)
    - [分区键选择](#分区键选择)
    - [副本策略](#副本策略)
  - [📊 性能指标](#-性能指标)
  - [🔧 故障处理](#-故障处理)
  - [📚 参考资源](#-参考资源)

---

## 🎯 概述

分布式 OTLP 数据模型需要在**可扩展性**、**查询性能**和**数据一致性**之间取得平衡。
本文档详细介绍如何使用 Rust 实现高性能的分布式数据建模与分区策略。

### 核心目标

- ✅ **水平扩展**: 支持 PB 级数据存储
- ✅ **查询优化**: 通过智能分区提升查询性能
- ✅ **负载均衡**: 数据均匀分布到各节点
- ✅ **高可用性**: 多副本保证数据可靠性
- ✅ **弹性伸缩**: 动态增减节点

### 关键挑战

- 🔴 **热点问题**: 避免数据倾斜
- 🔴 **跨分区查询**: 最小化分布式查询开销
- 🔴 **数据迁移**: 平滑的重平衡过程
- 🔴 **时间序列特性**: 处理时序数据的特殊性

---

## 🏗️ 分布式数据模型设计

### 1. Trace 数据模型

**核心字段与分区键**:

```rust
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use chrono::{DateTime, Utc};

/// Trace 数据模型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DistributedTrace {
    /// 全局唯一的 Trace ID (128-bit)
    pub trace_id: TraceId,
    
    /// Spans 列表
    pub spans: Vec<DistributedSpan>,
    
    /// Resource 属性
    pub resource: ResourceAttributes,
    
    /// 创建时间（用于时间分区）
    pub timestamp: DateTime<Utc>,
    
    /// 分区键（用于数据定位）
    pub partition_key: PartitionKey,
}

#[derive(Debug, Clone, Serialize, Deserialize, Hash, PartialEq, Eq)]
pub struct TraceId([u8; 16]);

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DistributedSpan {
    pub span_id: SpanId,
    pub trace_id: TraceId,
    pub parent_span_id: Option<SpanId>,
    pub name: String,
    pub start_time: DateTime<Utc>,
    pub end_time: DateTime<Utc>,
    pub attributes: HashMap<String, AttributeValue>,
    pub events: Vec<SpanEvent>,
    pub links: Vec<SpanLink>,
    pub status: SpanStatus,
}

#[derive(Debug, Clone, Serialize, Deserialize, Hash, PartialEq, Eq)]
pub struct SpanId([u8; 8]);

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceAttributes {
    pub service_name: String,
    pub service_namespace: Option<String>,
    pub service_instance_id: Option<String>,
    pub deployment_environment: Option<String>,
    pub attributes: HashMap<String, String>,
}

/// 分区键设计
#[derive(Debug, Clone, Serialize, Deserialize, Hash, PartialEq, Eq)]
pub struct PartitionKey {
    /// 服务名（用于服务级别分区）
    pub service_name: String,
    
    /// 时间桶（小时级）
    pub time_bucket: String, // format: "2025-10-10-14"
    
    /// TraceID 的哈希（用于负载均衡）
    pub trace_hash: u64,
}

impl PartitionKey {
    pub fn from_trace(trace: &DistributedTrace) -> Self {
        let time_bucket = trace.timestamp.format("%Y-%m-%d-%H").to_string();
        let trace_hash = Self::hash_trace_id(&trace.trace_id);
        
        Self {
            service_name: trace.resource.service_name.clone(),
            time_bucket,
            trace_hash,
        }
    }
    
    fn hash_trace_id(trace_id: &TraceId) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        
        let mut hasher = DefaultHasher::new();
        trace_id.hash(&mut hasher);
        hasher.finish()
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AttributeValue {
    String(String),
    Int(i64),
    Double(f64),
    Bool(bool),
    Array(Vec<AttributeValue>),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpanEvent {
    pub name: String,
    pub timestamp: DateTime<Utc>,
    pub attributes: HashMap<String, AttributeValue>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpanLink {
    pub trace_id: TraceId,
    pub span_id: SpanId,
    pub attributes: HashMap<String, AttributeValue>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SpanStatus {
    Unset,
    Ok,
    Error { message: String },
}
```

---

### 2. Metric 数据模型

```rust
/// Metric 数据模型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DistributedMetric {
    /// Metric 名称
    pub name: String,
    
    /// Metric 类型
    pub metric_type: MetricType,
    
    /// 数据点
    pub data_points: Vec<DataPoint>,
    
    /// Resource 属性
    pub resource: ResourceAttributes,
    
    /// 时间戳
    pub timestamp: DateTime<Utc>,
    
    /// 分区键
    pub partition_key: MetricPartitionKey,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MetricType {
    Counter,
    Gauge,
    Histogram,
    Summary,
    ExponentialHistogram,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DataPoint {
    pub timestamp: DateTime<Utc>,
    pub value: MetricValue,
    pub attributes: HashMap<String, String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MetricValue {
    Int(i64),
    Double(f64),
    Histogram {
        count: u64,
        sum: f64,
        buckets: Vec<HistogramBucket>,
    },
    Summary {
        count: u64,
        sum: f64,
        quantiles: Vec<Quantile>,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HistogramBucket {
    pub upper_bound: f64,
    pub count: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Quantile {
    pub quantile: f64,
    pub value: f64,
}

/// Metric 分区键（基于名称和时间）
#[derive(Debug, Clone, Serialize, Deserialize, Hash, PartialEq, Eq)]
pub struct MetricPartitionKey {
    /// Metric 名称
    pub name: String,
    
    /// 服务名
    pub service_name: String,
    
    /// 时间桶（小时级）
    pub time_bucket: String,
    
    /// 标签哈希（用于高基数标签处理）
    pub label_hash: u64,
}

impl MetricPartitionKey {
    pub fn from_metric(metric: &DistributedMetric) -> Self {
        let time_bucket = metric.timestamp.format("%Y-%m-%d-%H").to_string();
        
        // 计算标签哈希以处理高基数场景
        let label_hash = if let Some(first_dp) = metric.data_points.first() {
            Self::hash_labels(&first_dp.attributes)
        } else {
            0
        };
        
        Self {
            name: metric.name.clone(),
            service_name: metric.resource.service_name.clone(),
            time_bucket,
            label_hash,
        }
    }
    
    fn hash_labels(labels: &HashMap<String, String>) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        
        let mut hasher = DefaultHasher::new();
        
        // 按 key 排序以保证一致性
        let mut keys: Vec<_> = labels.keys().collect();
        keys.sort();
        
        for key in keys {
            key.hash(&mut hasher);
            labels[key].hash(&mut hasher);
        }
        
        hasher.finish()
    }
}
```

---

### 3. Log 数据模型

```rust
/// Log 数据模型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DistributedLog {
    /// 日志内容
    pub body: LogBody,
    
    /// 严重程度
    pub severity: SeverityLevel,
    
    /// 时间戳
    pub timestamp: DateTime<Utc>,
    
    /// Trace 上下文（如果有）
    pub trace_context: Option<TraceContext>,
    
    /// Resource 属性
    pub resource: ResourceAttributes,
    
    /// 日志属性
    pub attributes: HashMap<String, AttributeValue>,
    
    /// 分区键
    pub partition_key: LogPartitionKey,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum LogBody {
    String(String),
    Structured(serde_json::Value),
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
pub enum SeverityLevel {
    Trace = 1,
    Debug = 5,
    Info = 9,
    Warn = 13,
    Error = 17,
    Fatal = 21,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraceContext {
    pub trace_id: TraceId,
    pub span_id: SpanId,
}

/// Log 分区键（基于时间和严重程度）
#[derive(Debug, Clone, Serialize, Deserialize, Hash, PartialEq, Eq)]
pub struct LogPartitionKey {
    /// 服务名
    pub service_name: String,
    
    /// 时间桶（小时级）
    pub time_bucket: String,
    
    /// 严重程度（用于快速过滤）
    pub severity_level: u8,
    
    /// 内容哈希（用于去重）
    pub content_hash: u64,
}

impl LogPartitionKey {
    pub fn from_log(log: &DistributedLog) -> Self {
        let time_bucket = log.timestamp.format("%Y-%m-%d-%H").to_string();
        let severity_level = log.severity.clone() as u8;
        let content_hash = Self::hash_content(&log.body);
        
        Self {
            service_name: log.resource.service_name.clone(),
            time_bucket,
            severity_level,
            content_hash,
        }
    }
    
    fn hash_content(body: &LogBody) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        
        let mut hasher = DefaultHasher::new();
        match body {
            LogBody::String(s) => s.hash(&mut hasher),
            LogBody::Structured(v) => v.to_string().hash(&mut hasher),
        }
        hasher.finish()
    }
}
```

---

## 📊 数据分区策略

### 1. 时间范围分区 (Time-Range Partitioning)

**适用场景**: 时序数据，支持时间范围查询

```rust
use std::ops::Range;

/// 时间范围分区器
pub struct TimeRangePartitioner {
    /// 分区粒度（小时）
    granularity_hours: u32,
    
    /// 分区保留时间（天）
    retention_days: u32,
}

impl TimeRangePartitioner {
    pub fn new(granularity_hours: u32, retention_days: u32) -> Self {
        Self {
            granularity_hours,
            retention_days,
        }
    }
    
    /// 计算数据点所属的分区
    pub fn get_partition(&self, timestamp: DateTime<Utc>) -> TimePartition {
        let hour_bucket = timestamp.timestamp() / (self.granularity_hours as i64 * 3600);
        
        TimePartition {
            bucket_id: hour_bucket,
            start_time: DateTime::from_timestamp(
                hour_bucket * self.granularity_hours as i64 * 3600,
                0
            ).unwrap(),
            end_time: DateTime::from_timestamp(
                (hour_bucket + 1) * self.granularity_hours as i64 * 3600,
                0
            ).unwrap(),
        }
    }
    
    /// 获取时间范围内的所有分区
    pub fn get_partitions_in_range(
        &self,
        start: DateTime<Utc>,
        end: DateTime<Utc>,
    ) -> Vec<TimePartition> {
        let mut partitions = Vec::new();
        let mut current = start;
        
        while current < end {
            partitions.push(self.get_partition(current));
            current += chrono::Duration::hours(self.granularity_hours as i64);
        }
        
        partitions
    }
    
    /// 获取需要清理的过期分区
    pub fn get_expired_partitions(&self, now: DateTime<Utc>) -> Vec<TimePartition> {
        let retention_timestamp = now - chrono::Duration::days(self.retention_days as i64);
        let mut partitions = Vec::new();
        
        let start = DateTime::from_timestamp(0, 0).unwrap();
        let mut current = start;
        
        while current < retention_timestamp {
            partitions.push(self.get_partition(current));
            current += chrono::Duration::hours(self.granularity_hours as i64);
        }
        
        partitions
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TimePartition {
    pub bucket_id: i64,
    pub start_time: DateTime<Utc>,
    pub end_time: DateTime<Utc>,
}

impl TimePartition {
    pub fn to_string(&self) -> String {
        format!("time_partition_{}", self.bucket_id)
    }
}
```

---

### 2. 哈希分区 (Hash Partitioning)

**适用场景**: 负载均衡，避免热点

```rust
use std::sync::Arc;

/// 哈希分区器
pub struct HashPartitioner {
    /// 分区数量
    num_partitions: usize,
    
    /// 虚拟节点数量（用于一致性哈希）
    virtual_nodes: usize,
}

impl HashPartitioner {
    pub fn new(num_partitions: usize, virtual_nodes: usize) -> Self {
        Self {
            num_partitions,
            virtual_nodes,
        }
    }
    
    /// 基于 TraceID 计算分区
    pub fn get_partition_for_trace(&self, trace_id: &TraceId) -> usize {
        self.hash(trace_id) % self.num_partitions
    }
    
    /// 基于 MetricName + Labels 计算分区
    pub fn get_partition_for_metric(&self, key: &MetricPartitionKey) -> usize {
        self.hash(key) % self.num_partitions
    }
    
    /// 基于日志内容计算分区
    pub fn get_partition_for_log(&self, key: &LogPartitionKey) -> usize {
        self.hash(key) % self.num_partitions
    }
    
    fn hash<T: std::hash::Hash>(&self, value: &T) -> usize {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::Hasher;
        
        let mut hasher = DefaultHasher::new();
        value.hash(&mut hasher);
        hasher.finish() as usize
    }
}
```

---

### 3. 范围分区 (Range Partitioning)

**适用场景**: 顺序访问，范围查询

```rust
use std::cmp::Ordering;

/// 范围分区器
pub struct RangePartitioner<K: Ord> {
    /// 分区边界
    boundaries: Vec<K>,
}

impl<K: Ord + Clone> RangePartitioner<K> {
    pub fn new(boundaries: Vec<K>) -> Self {
        Self { boundaries }
    }
    
    /// 查找数据点所属的分区
    pub fn get_partition(&self, key: &K) -> usize {
        match self.boundaries.binary_search(key) {
            Ok(index) => index,
            Err(index) => index.saturating_sub(1),
        }
    }
    
    /// 获取范围内的所有分区
    pub fn get_partitions_in_range(&self, start: &K, end: &K) -> Vec<usize> {
        let start_partition = self.get_partition(start);
        let end_partition = self.get_partition(end);
        
        (start_partition..=end_partition).collect()
    }
}

/// 服务名范围分区示例
pub type ServiceNameRangePartitioner = RangePartitioner<String>;

impl ServiceNameRangePartitioner {
    /// 基于字母顺序创建分区
    pub fn new_alphabetic(num_partitions: usize) -> Self {
        let mut boundaries = Vec::new();
        let step = 26 / num_partitions;
        
        for i in 0..num_partitions {
            let letter = (b'a' + (i * step) as u8) as char;
            boundaries.push(letter.to_string());
        }
        
        Self::new(boundaries)
    }
}
```

---

### 4. 复合分区策略

**结合时间和哈希分区**:

```rust
use std::sync::Arc;

/// 复合分区器（时间 + 哈希）
pub struct CompositePartitioner {
    time_partitioner: Arc<TimeRangePartitioner>,
    hash_partitioner: Arc<HashPartitioner>,
}

impl CompositePartitioner {
    pub fn new(
        time_partitioner: Arc<TimeRangePartitioner>,
        hash_partitioner: Arc<HashPartitioner>,
    ) -> Self {
        Self {
            time_partitioner,
            hash_partitioner,
        }
    }
    
    /// 为 Trace 计算复合分区
    pub fn get_partition_for_trace(&self, trace: &DistributedTrace) -> CompositePartition {
        let time_partition = self.time_partitioner.get_partition(trace.timestamp);
        let hash_partition = self.hash_partitioner.get_partition_for_trace(&trace.trace_id);
        
        CompositePartition {
            time_partition,
            hash_partition,
        }
    }
    
    /// 为 Metric 计算复合分区
    pub fn get_partition_for_metric(&self, metric: &DistributedMetric) -> CompositePartition {
        let time_partition = self.time_partitioner.get_partition(metric.timestamp);
        let hash_partition = self.hash_partitioner.get_partition_for_metric(&metric.partition_key);
        
        CompositePartition {
            time_partition,
            hash_partition,
        }
    }
    
    /// 获取时间范围和哈希桶内的所有分区
    pub fn get_partitions_in_range(
        &self,
        start_time: DateTime<Utc>,
        end_time: DateTime<Utc>,
        hash_buckets: Option<Vec<usize>>,
    ) -> Vec<CompositePartition> {
        let time_partitions = self.time_partitioner.get_partitions_in_range(start_time, end_time);
        
        let hash_buckets = hash_buckets.unwrap_or_else(|| {
            (0..self.hash_partitioner.num_partitions).collect()
        });
        
        let mut composite_partitions = Vec::new();
        
        for time_partition in time_partitions {
            for &hash_partition in &hash_buckets {
                composite_partitions.push(CompositePartition {
                    time_partition: time_partition.clone(),
                    hash_partition,
                });
            }
        }
        
        composite_partitions
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CompositePartition {
    pub time_partition: TimePartition,
    pub hash_partition: usize,
}

impl CompositePartition {
    pub fn to_string(&self) -> String {
        format!(
            "partition_{}_{:04}",
            self.time_partition.bucket_id,
            self.hash_partition
        )
    }
}
```

---

## 🔍 数据定位与路由

### 1. 一致性哈希路由

```rust
use std::collections::BTreeMap;
use std::sync::RwLock;

/// 一致性哈希环
pub struct ConsistentHashRing {
    /// 虚拟节点映射：哈希值 -> 物理节点
    ring: Arc<RwLock<BTreeMap<u64, String>>>,
    
    /// 每个物理节点的虚拟节点数
    virtual_nodes_per_node: usize,
}

impl ConsistentHashRing {
    pub fn new(virtual_nodes_per_node: usize) -> Self {
        Self {
            ring: Arc::new(RwLock::new(BTreeMap::new())),
            virtual_nodes_per_node,
        }
    }
    
    /// 添加节点到哈希环
    pub fn add_node(&self, node_id: String) {
        let mut ring = self.ring.write().unwrap();
        
        for i in 0..self.virtual_nodes_per_node {
            let virtual_node_key = format!("{}:{}", node_id, i);
            let hash = self.hash_string(&virtual_node_key);
            ring.insert(hash, node_id.clone());
        }
    }
    
    /// 从哈希环移除节点
    pub fn remove_node(&self, node_id: &str) {
        let mut ring = self.ring.write().unwrap();
        
        for i in 0..self.virtual_nodes_per_node {
            let virtual_node_key = format!("{}:{}", node_id, i);
            let hash = self.hash_string(&virtual_node_key);
            ring.remove(&hash);
        }
    }
    
    /// 查找 key 对应的节点
    pub fn get_node(&self, key: &str) -> Option<String> {
        let ring = self.ring.read().unwrap();
        
        if ring.is_empty() {
            return None;
        }
        
        let hash = self.hash_string(key);
        
        // 找到第一个 >= hash 的节点
        for (_, node_id) in ring.range(hash..) {
            return Some(node_id.clone());
        }
        
        // 如果没找到，返回第一个节点（环形）
        ring.values().next().cloned()
    }
    
    /// 获取 N 个副本节点
    pub fn get_nodes(&self, key: &str, replica_count: usize) -> Vec<String> {
        let ring = self.ring.read().unwrap();
        
        if ring.is_empty() {
            return Vec::new();
        }
        
        let hash = self.hash_string(key);
        let mut nodes = Vec::new();
        let mut seen = std::collections::HashSet::new();
        
        // 从 hash 位置开始遍历
        for (_, node_id) in ring.range(hash..) {
            if seen.insert(node_id.clone()) {
                nodes.push(node_id.clone());
                if nodes.len() >= replica_count {
                    return nodes;
                }
            }
        }
        
        // 环形，从头继续
        for (_, node_id) in ring.iter() {
            if seen.insert(node_id.clone()) {
                nodes.push(node_id.clone());
                if nodes.len() >= replica_count {
                    return nodes;
                }
            }
        }
        
        nodes
    }
    
    fn hash_string(&self, s: &str) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        
        let mut hasher = DefaultHasher::new();
        s.hash(&mut hasher);
        hasher.finish()
    }
}
```

---

### 2. 元数据服务

```rust
use tokio::sync::RwLock as TokioRwLock;

/// 分区元数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PartitionMetadata {
    pub partition_id: String,
    pub nodes: Vec<String>,
    pub leader: String,
    pub state: PartitionState,
    pub size_bytes: u64,
    pub record_count: u64,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum PartitionState {
    Active,
    Rebalancing,
    Migrating,
    ReadOnly,
}

/// 元数据服务
pub struct MetadataService {
    /// 分区元数据缓存
    partitions: Arc<TokioRwLock<HashMap<String, PartitionMetadata>>>,
    
    /// etcd 客户端（持久化）
    etcd_client: Option<etcd_client::Client>,
}

impl MetadataService {
    pub async fn new(etcd_endpoints: Vec<String>) -> Result<Self, Box<dyn std::error::Error>> {
        let etcd_client = if !etcd_endpoints.is_empty() {
            Some(etcd_client::Client::connect(etcd_endpoints, None).await?)
        } else {
            None
        };
        
        Ok(Self {
            partitions: Arc::new(TokioRwLock::new(HashMap::new())),
            etcd_client,
        })
    }
    
    /// 注册新分区
    pub async fn register_partition(
        &self,
        partition_id: String,
        nodes: Vec<String>,
        leader: String,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let metadata = PartitionMetadata {
            partition_id: partition_id.clone(),
            nodes,
            leader,
            state: PartitionState::Active,
            size_bytes: 0,
            record_count: 0,
            created_at: Utc::now(),
            updated_at: Utc::now(),
        };
        
        // 更新本地缓存
        {
            let mut partitions = self.partitions.write().await;
            partitions.insert(partition_id.clone(), metadata.clone());
        }
        
        // 持久化到 etcd
        if let Some(ref mut client) = self.etcd_client.as_ref() {
            let key = format!("/otlp/partitions/{}", partition_id);
            let value = serde_json::to_string(&metadata)?;
            let mut client = client.clone();
            client.put(key, value, None).await?;
        }
        
        Ok(())
    }
    
    /// 获取分区元数据
    pub async fn get_partition(&self, partition_id: &str) -> Option<PartitionMetadata> {
        let partitions = self.partitions.read().await;
        partitions.get(partition_id).cloned()
    }
    
    /// 获取所有活跃分区
    pub async fn get_active_partitions(&self) -> Vec<PartitionMetadata> {
        let partitions = self.partitions.read().await;
        partitions
            .values()
            .filter(|p| p.state == PartitionState::Active)
            .cloned()
            .collect()
    }
    
    /// 更新分区状态
    pub async fn update_partition_state(
        &self,
        partition_id: &str,
        new_state: PartitionState,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut partitions = self.partitions.write().await;
        
        if let Some(metadata) = partitions.get_mut(partition_id) {
            metadata.state = new_state;
            metadata.updated_at = Utc::now();
            
            // 持久化
            if let Some(ref mut client) = self.etcd_client.as_ref() {
                let key = format!("/otlp/partitions/{}", partition_id);
                let value = serde_json::to_string(metadata)?;
                let mut client = client.clone();
                client.put(key, value, None).await?;
            }
        }
        
        Ok(())
    }
    
    /// 从 etcd 加载所有分区元数据
    pub async fn load_from_etcd(&self) -> Result<(), Box<dyn std::error::Error>> {
        if let Some(ref mut client) = self.etcd_client.as_ref() {
            let mut client = client.clone();
            let resp = client.get("/otlp/partitions/", Some(etcd_client::GetOptions::new().with_prefix())).await?;
            
            let mut partitions = self.partitions.write().await;
            
            for kv in resp.kvs() {
                if let Ok(metadata) = serde_json::from_slice::<PartitionMetadata>(kv.value()) {
                    partitions.insert(metadata.partition_id.clone(), metadata);
                }
            }
        }
        
        Ok(())
    }
}
```

---

### 3. 分片管理器

```rust
/// 分片管理器（整合分区和路由）
pub struct ShardManager {
    composite_partitioner: Arc<CompositePartitioner>,
    consistent_hash_ring: Arc<ConsistentHashRing>,
    metadata_service: Arc<MetadataService>,
}

impl ShardManager {
    pub fn new(
        composite_partitioner: Arc<CompositePartitioner>,
        consistent_hash_ring: Arc<ConsistentHashRing>,
        metadata_service: Arc<MetadataService>,
    ) -> Self {
        Self {
            composite_partitioner,
            consistent_hash_ring,
            metadata_service,
        }
    }
    
    /// 为 Trace 确定目标节点
    pub async fn get_nodes_for_trace(
        &self,
        trace: &DistributedTrace,
        replica_count: usize,
    ) -> Result<Vec<String>, String> {
        // 1. 计算复合分区
        let partition = self.composite_partitioner.get_partition_for_trace(trace);
        let partition_key = partition.to_string();
        
        // 2. 使用一致性哈希查找节点
        let nodes = self.consistent_hash_ring.get_nodes(&partition_key, replica_count);
        
        if nodes.is_empty() {
            return Err("No available nodes".to_string());
        }
        
        Ok(nodes)
    }
    
    /// 为时间范围查询确定需要访问的所有节点
    pub async fn get_nodes_for_time_range_query(
        &self,
        start_time: DateTime<Utc>,
        end_time: DateTime<Utc>,
        service_name: Option<String>,
    ) -> Result<Vec<(CompositePartition, Vec<String>)>, String> {
        // 1. 获取时间范围内的所有分区
        let partitions = self.composite_partitioner.get_partitions_in_range(
            start_time,
            end_time,
            None, // 查询所有哈希桶
        );
        
        // 2. 为每个分区查找节点
        let mut result = Vec::new();
        
        for partition in partitions {
            let partition_key = partition.to_string();
            let nodes = self.consistent_hash_ring.get_nodes(&partition_key, 1);
            
            if !nodes.is_empty() {
                result.push((partition, nodes));
            }
        }
        
        Ok(result)
    }
}
```

---

## ⚡ 分区重平衡

### 1. 自动重平衡管理器

```rust
/// 重平衡管理器
pub struct RebalanceManager {
    shard_manager: Arc<ShardManager>,
    metadata_service: Arc<MetadataService>,
    config: RebalanceConfig,
}

#[derive(Debug, Clone)]
pub struct RebalanceConfig {
    /// 负载差异阈值（触发重平衡）
    pub imbalance_threshold: f64,
    
    /// 检查间隔
    pub check_interval: Duration,
    
    /// 每次迁移的最大分区数
    pub max_concurrent_migrations: usize,
}

impl Default for RebalanceConfig {
    fn default() -> Self {
        Self {
            imbalance_threshold: 0.2, // 20%
            check_interval: Duration::from_secs(300), // 5分钟
            max_concurrent_migrations: 3,
        }
    }
}

impl RebalanceManager {
    pub fn new(
        shard_manager: Arc<ShardManager>,
        metadata_service: Arc<MetadataService>,
        config: RebalanceConfig,
    ) -> Self {
        Self {
            shard_manager,
            metadata_service,
            config,
        }
    }
    
    /// 启动自动重平衡
    pub async fn start_auto_rebalance(&self) {
        let mut interval = tokio::time::interval(self.config.check_interval);
        
        loop {
            interval.tick().await;
            
            if let Err(e) = self.check_and_rebalance().await {
                tracing::error!("Rebalance failed: {}", e);
            }
        }
    }
    
    /// 检查并执行重平衡
    async fn check_and_rebalance(&self) -> Result<(), Box<dyn std::error::Error>> {
        // 1. 获取所有分区的负载信息
        let partitions = self.metadata_service.get_active_partitions().await;
        
        if partitions.is_empty() {
            return Ok(());
        }
        
        // 2. 按节点聚合负载
        let mut node_loads: HashMap<String, u64> = HashMap::new();
        
        for partition in &partitions {
            *node_loads.entry(partition.leader.clone()).or_insert(0) += partition.size_bytes;
        }
        
        // 3. 计算平均负载和偏差
        let total_load: u64 = node_loads.values().sum();
        let avg_load = total_load as f64 / node_loads.len() as f64;
        
        // 4. 查找过载和空闲节点
        let mut overloaded: Vec<_> = node_loads
            .iter()
            .filter(|(_, &load)| load as f64 > avg_load * (1.0 + self.config.imbalance_threshold))
            .collect();
        
        let mut underloaded: Vec<_> = node_loads
            .iter()
            .filter(|(_, &load)| load as f64 < avg_load * (1.0 - self.config.imbalance_threshold))
            .collect();
        
        if overloaded.is_empty() || underloaded.is_empty() {
            tracing::info!("Cluster is balanced");
            return Ok(());
        }
        
        // 5. 生成迁移计划
        overloaded.sort_by_key(|(_, load)| std::cmp::Reverse(*load));
        underloaded.sort_by_key(|(_, load)| *load);
        
        let migrations = self.plan_migrations(&overloaded, &underloaded, &partitions);
        
        // 6. 执行迁移
        self.execute_migrations(migrations).await?;
        
        Ok(())
    }
    
    fn plan_migrations(
        &self,
        overloaded: &[(&String, &u64)],
        underloaded: &[(&String, &u64)],
        partitions: &[PartitionMetadata],
    ) -> Vec<Migration> {
        let mut migrations = Vec::new();
        let mut overloaded_iter = overloaded.iter();
        let mut underloaded_iter = underloaded.iter();
        
        'outer: for _ in 0..self.config.max_concurrent_migrations {
            if let (Some((from_node, _)), Some((to_node, _))) =
                (overloaded_iter.next(), underloaded_iter.next())
            {
                // 找到该节点上的一个分区
                if let Some(partition) = partitions.iter().find(|p| &p.leader == *from_node) {
                    migrations.push(Migration {
                        partition_id: partition.partition_id.clone(),
                        from_node: (*from_node).clone(),
                        to_node: (*to_node).clone(),
                    });
                }
            } else {
                break 'outer;
            }
        }
        
        migrations
    }
    
    async fn execute_migrations(
        &self,
        migrations: Vec<Migration>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        for migration in migrations {
            tracing::info!(
                "Migrating partition {} from {} to {}",
                migration.partition_id,
                migration.from_node,
                migration.to_node
            );
            
            // 1. 标记分区为 Migrating 状态
            self.metadata_service
                .update_partition_state(&migration.partition_id, PartitionState::Migrating)
                .await?;
            
            // 2. 执行数据迁移（这里简化处理）
            // TODO: 实际实现需要流式传输数据
            
            // 3. 更新元数据
            if let Some(mut metadata) = self.metadata_service.get_partition(&migration.partition_id).await {
                metadata.leader = migration.to_node.clone();
                metadata.state = PartitionState::Active;
                metadata.updated_at = Utc::now();
                
                // 重新注册
                self.metadata_service
                    .register_partition(
                        metadata.partition_id.clone(),
                        metadata.nodes.clone(),
                        metadata.leader.clone(),
                    )
                    .await?;
            }
            
            tracing::info!("Migration completed for partition {}", migration.partition_id);
        }
        
        Ok(())
    }
}

#[derive(Debug, Clone)]
struct Migration {
    partition_id: String,
    from_node: String,
    to_node: String,
}
```

---

## 💾 数据本地化优化

### 1. 数据局部性感知路由

```rust
/// 数据局部性感知的路由器
pub struct LocalityAwareRouter {
    shard_manager: Arc<ShardManager>,
    
    /// 当前节点 ID
    local_node_id: String,
    
    /// 节点位置信息（数据中心、可用区）
    node_locations: Arc<RwLock<HashMap<String, NodeLocation>>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NodeLocation {
    pub data_center: String,
    pub availability_zone: String,
    pub region: String,
}

impl LocalityAwareRouter {
    pub fn new(
        shard_manager: Arc<ShardManager>,
        local_node_id: String,
    ) -> Self {
        Self {
            shard_manager,
            local_node_id,
            node_locations: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    /// 注册节点位置
    pub fn register_node_location(&self, node_id: String, location: NodeLocation) {
        let mut locations = self.node_locations.write().unwrap();
        locations.insert(node_id, location);
    }
    
    /// 选择最近的节点
    pub async fn select_nearest_node(
        &self,
        candidate_nodes: Vec<String>,
    ) -> Option<String> {
        let locations = self.node_locations.read().unwrap();
        
        let local_location = locations.get(&self.local_node_id)?;
        
        // 优先选择同一数据中心的节点
        for node in &candidate_nodes {
            if let Some(location) = locations.get(node) {
                if location.data_center == local_location.data_center {
                    return Some(node.clone());
                }
            }
        }
        
        // 其次选择同一可用区的节点
        for node in &candidate_nodes {
            if let Some(location) = locations.get(node) {
                if location.availability_zone == local_location.availability_zone {
                    return Some(node.clone());
                }
            }
        }
        
        // 最后选择同一区域的节点
        for node in &candidate_nodes {
            if let Some(location) = locations.get(node) {
                if location.region == local_location.region {
                    return Some(node.clone());
                }
            }
        }
        
        // 随机选择
        candidate_nodes.into_iter().next()
    }
    
    /// 为查询选择最优节点集合
    pub async fn select_optimal_nodes_for_query(
        &self,
        required_partitions: Vec<(CompositePartition, Vec<String>)>,
    ) -> HashMap<CompositePartition, String> {
        let mut result = HashMap::new();
        
        for (partition, candidate_nodes) in required_partitions {
            if let Some(node) = self.select_nearest_node(candidate_nodes).await {
                result.insert(partition, node);
            }
        }
        
        result
    }
}
```

---

## 📈 完整示例：分布式 OTLP 存储系统

```rust
use tokio;

/// 分布式 OTLP 存储系统
pub struct DistributedOtlpStorage {
    shard_manager: Arc<ShardManager>,
    locality_router: Arc<LocalityAwareRouter>,
    rebalance_manager: Arc<RebalanceManager>,
}

impl DistributedOtlpStorage {
    pub async fn new(
        nodes: Vec<String>,
        local_node_id: String,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        // 1. 创建时间分区器（按小时）
        let time_partitioner = Arc::new(TimeRangePartitioner::new(
            1,  // 1小时一个分区
            30, // 保留30天
        ));
        
        // 2. 创建哈希分区器（256个哈希桶）
        let hash_partitioner = Arc::new(HashPartitioner::new(256, 100));
        
        // 3. 创建复合分区器
        let composite_partitioner = Arc::new(CompositePartitioner::new(
            time_partitioner,
            hash_partitioner,
        ));
        
        // 4. 创建一致性哈希环
        let consistent_hash_ring = Arc::new(ConsistentHashRing::new(150));
        for node in &nodes {
            consistent_hash_ring.add_node(node.clone());
        }
        
        // 5. 创建元数据服务
        let metadata_service = Arc::new(
            MetadataService::new(vec!["127.0.0.1:2379".to_string()]).await?
        );
        metadata_service.load_from_etcd().await?;
        
        // 6. 创建分片管理器
        let shard_manager = Arc::new(ShardManager::new(
            composite_partitioner,
            consistent_hash_ring,
            metadata_service.clone(),
        ));
        
        // 7. 创建局部性感知路由器
        let locality_router = Arc::new(LocalityAwareRouter::new(
            shard_manager.clone(),
            local_node_id,
        ));
        
        // 8. 创建重平衡管理器
        let rebalance_manager = Arc::new(RebalanceManager::new(
            shard_manager.clone(),
            metadata_service,
            RebalanceConfig::default(),
        ));
        
        Ok(Self {
            shard_manager,
            locality_router,
            rebalance_manager,
        })
    }
    
    /// 启动后台任务
    pub async fn start(&self) {
        let rebalance_manager = self.rebalance_manager.clone();
        
        tokio::spawn(async move {
            rebalance_manager.start_auto_rebalance().await;
        });
    }
    
    /// 写入 Trace
    pub async fn write_trace(&self, trace: DistributedTrace) -> Result<(), String> {
        // 1. 确定目标节点
        let nodes = self.shard_manager.get_nodes_for_trace(&trace, 3).await?;
        
        tracing::info!("Writing trace {} to nodes: {:?}", 
            format!("{:?}", trace.trace_id), nodes);
        
        // 2. 选择最近的节点写入
        if let Some(primary_node) = self.locality_router.select_nearest_node(nodes.clone()).await {
            // TODO: 实际发送数据到节点
            tracing::info!("Primary write to node: {}", primary_node);
        }
        
        // 3. 异步复制到副本节点
        for node in nodes.iter().skip(1) {
            let node = node.clone();
            tokio::spawn(async move {
                // TODO: 异步复制
                tracing::info!("Async replication to node: {}", node);
            });
        }
        
        Ok(())
    }
    
    /// 查询时间范围内的 Traces
    pub async fn query_traces(
        &self,
        start_time: DateTime<Utc>,
        end_time: DateTime<Utc>,
        service_name: Option<String>,
    ) -> Result<Vec<DistributedTrace>, String> {
        // 1. 确定需要查询的分区和节点
        let partitions = self.shard_manager
            .get_nodes_for_time_range_query(start_time, end_time, service_name)
            .await?;
        
        // 2. 为每个分区选择最优节点
        let optimal_nodes = self.locality_router
            .select_optimal_nodes_for_query(partitions)
            .await;
        
        // 3. 并发查询所有节点
        let mut handles = Vec::new();
        
        for (partition, node) in optimal_nodes {
            let handle = tokio::spawn(async move {
                // TODO: 实际查询节点
                tracing::info!("Querying partition {} from node {}", 
                    partition.to_string(), node);
                
                Vec::<DistributedTrace>::new()
            });
            
            handles.push(handle);
        }
        
        // 4. 收集结果
        let mut results = Vec::new();
        
        for handle in handles {
            if let Ok(traces) = handle.await {
                results.extend(traces);
            }
        }
        
        Ok(results)
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt::init();
    
    // 初始化集群节点
    let nodes = vec![
        "node-1".to_string(),
        "node-2".to_string(),
        "node-3".to_string(),
        "node-4".to_string(),
    ];
    
    // 创建存储系统
    let storage = DistributedOtlpStorage::new(nodes, "node-1".to_string()).await?;
    
    // 启动后台任务
    storage.start().await;
    
    // 写入示例 Trace
    let trace = DistributedTrace {
        trace_id: TraceId([1; 16]),
        spans: vec![],
        resource: ResourceAttributes {
            service_name: "example-service".to_string(),
            service_namespace: Some("production".to_string()),
            service_instance_id: Some("instance-1".to_string()),
            deployment_environment: Some("prod".to_string()),
            attributes: HashMap::new(),
        },
        timestamp: Utc::now(),
        partition_key: PartitionKey {
            service_name: "example-service".to_string(),
            time_bucket: Utc::now().format("%Y-%m-%d-%H").to_string(),
            trace_hash: 12345,
        },
    };
    
    storage.write_trace(trace).await?;
    
    // 查询示例
    let start = Utc::now() - chrono::Duration::hours(1);
    let end = Utc::now();
    
    let traces = storage.query_traces(start, end, Some("example-service".to_string())).await?;
    
    println!("Found {} traces", traces.len());
    
    Ok(())
}
```

---

## 🎯 最佳实践

### 分区大小

- **Trace 分区**: 每个分区 1-5 GB
- **Metric 分区**: 每个分区 100-500 MB
- **Log 分区**: 每个分区 500 MB - 2 GB

### 分区键选择

1. **高基数字段**: TraceID, SpanID
2. **时间维度**: 必须包含时间字段
3. **查询模式**: 基于常见查询选择

### 副本策略

- **生产环境**: 3 副本
- **开发环境**: 1 副本
- **关键数据**: 5 副本

---

## 📊 性能指标

- **写入吞吐量**: > 100K traces/s
- **查询延迟**: < 100ms (P99)
- **分区重平衡**: < 10% 性能影响
- **数据倾斜率**: < 10%

---

## 🔧 故障处理

- **节点故障**: 自动故障转移到副本
- **网络分区**: 最终一致性保证
- **数据损坏**: CRC 校验和修复
- **分区过大**: 自动分裂

---

## 📚 参考资源

- [Consistent Hashing](https://en.wikipedia.org/wiki/Consistent_hashing)
- [Time-Series Data Partitioning](https://docs.timescale.com/)
- [Distributed Systems Patterns](https://martinfowler.com/articles/patterns-of-distributed-systems/)
- [Apache Cassandra Data Model](https://cassandra.apache.org/doc/latest/data_modeling/)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-10  
**作者**: OTLP Rust 项目组
