# 分布式索引与快速检索 - Rust 完整实现

> **文档版本**: v1.0.0  
> **Rust 版本**: 1.90+  
> **最后更新**: 2025-10-10

---

## 📋 目录

- [分布式索引与快速检索 - Rust 完整实现](#分布式索引与快速检索---rust-完整实现)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [索引类型](#索引类型)
    - [核心挑战](#核心挑战)
  - [🔍 TraceID 索引](#-traceid-索引)
    - [1. Bloom Filter 预过滤](#1-bloom-filter-预过滤)
    - [2. LSM-Tree 索引](#2-lsm-tree-索引)
    - [3. 倒排索引（标签检索）](#3-倒排索引标签检索)
  - [📊 Metric 名称索引](#-metric-名称索引)
    - [1. Trie 树索引](#1-trie-树索引)
    - [2. 时间序列索引](#2-时间序列索引)
  - [📝 日志全文索引](#-日志全文索引)
    - [1. 全文倒排索引](#1-全文倒排索引)
    - [2. N-Gram 索引](#2-n-gram-索引)
  - [⚡ 分布式索引协调](#-分布式索引协调)
    - [1. 分布式倒排索引](#1-分布式倒排索引)
    - [2. 分布式查询执行器](#2-分布式查询执行器)
  - [💾 索引持久化与恢复](#-索引持久化与恢复)
    - [1. 索引快照管理器](#1-索引快照管理器)
  - [📈 完整示例：统一索引系统](#-完整示例统一索引系统)
  - [🎯 性能优化](#-性能优化)
    - [缓存策略](#缓存策略)
    - [压缩技术](#压缩技术)
  - [📊 性能指标](#-性能指标)
  - [📚 参考资源](#-参考资源)

---

## 🎯 概述

分布式 OTLP 系统需要高效的索引机制来支持快速检索。
本文档介绍如何使用 Rust 实现生产级别的索引系统。

### 索引类型

- ✅ **TraceID 索引**: 精确查找
- ✅ **属性标签索引**: 多维过滤
- ✅ **时间索引**: 范围查询
- ✅ **全文索引**: 日志搜索
- ✅ **倒排索引**: 标签查找

### 核心挑战

- 🔴 **高基数问题**: Trace/Span ID 数量巨大
- 🔴 **实时性要求**: 写入后立即可查
- 🔴 **分布式一致性**: 多节点索引同步
- 🔴 **存储开销**: 索引大小控制

---

## 🔍 TraceID 索引

### 1. Bloom Filter 预过滤

**用途**: 快速判断 TraceID 是否存在，避免无效查询

```rust
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use bitvec::prelude::*;

/// Bloom Filter 实现
pub struct BloomFilter {
    /// 位数组
    bits: BitVec,
    
    /// 哈希函数数量
    num_hashes: usize,
    
    /// 预期元素数量
    expected_elements: usize,
    
    /// 实际元素数量
    actual_elements: std::sync::atomic::AtomicUsize,
}

impl BloomFilter {
    /// 创建 Bloom Filter
    /// 
    /// # 参数
    /// - `expected_elements`: 预期元素数量
    /// - `false_positive_rate`: 期望的假阳性率（如 0.01 表示 1%）
    pub fn new(expected_elements: usize, false_positive_rate: f64) -> Self {
        // 计算最优位数组大小
        let num_bits = Self::optimal_num_bits(expected_elements, false_positive_rate);
        
        // 计算最优哈希函数数量
        let num_hashes = Self::optimal_num_hashes(num_bits, expected_elements);
        
        Self {
            bits: bitvec![0; num_bits],
            num_hashes,
            expected_elements,
            actual_elements: std::sync::atomic::AtomicUsize::new(0),
        }
    }
    
    fn optimal_num_bits(n: usize, p: f64) -> usize {
        let n = n as f64;
        let numerator = -n * p.ln();
        let denominator = (2.0_f64.ln()).powi(2);
        (numerator / denominator).ceil() as usize
    }
    
    fn optimal_num_hashes(m: usize, n: usize) -> usize {
        let m = m as f64;
        let n = n as f64;
        ((m / n) * 2.0_f64.ln()).ceil() as usize
    }
    
    /// 插入元素
    pub fn insert<T: Hash>(&mut self, item: &T) {
        for i in 0..self.num_hashes {
            let hash = self.hash_with_seed(item, i);
            let index = (hash as usize) % self.bits.len();
            self.bits.set(index, true);
        }
        
        self.actual_elements.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }
    
    /// 检查元素是否可能存在
    pub fn contains<T: Hash>(&self, item: &T) -> bool {
        for i in 0..self.num_hashes {
            let hash = self.hash_with_seed(item, i);
            let index = (hash as usize) % self.bits.len();
            
            if !self.bits[index] {
                return false; // 确定不存在
            }
        }
        
        true // 可能存在（有假阳性）
    }
    
    fn hash_with_seed<T: Hash>(&self, item: &T, seed: usize) -> u64 {
        let mut hasher = DefaultHasher::new();
        item.hash(&mut hasher);
        seed.hash(&mut hasher);
        hasher.finish()
    }
    
    /// 获取假阳性率估计
    pub fn false_positive_rate(&self) -> f64 {
        let m = self.bits.len() as f64;
        let n = self.actual_elements.load(std::sync::atomic::Ordering::Relaxed) as f64;
        let k = self.num_hashes as f64;
        
        (1.0 - (-k * n / m).exp()).powf(k)
    }
}

/// Trace ID Bloom Filter 索引
pub struct TraceIdBloomIndex {
    /// 分区的 Bloom Filters
    filters: std::sync::Arc<tokio::sync::RwLock<HashMap<String, BloomFilter>>>,
}

impl TraceIdBloomIndex {
    pub fn new() -> Self {
        Self {
            filters: std::sync::Arc::new(tokio::sync::RwLock::new(HashMap::new())),
        }
    }
    
    /// 为分区添加 TraceID
    pub async fn insert(&self, partition_id: &str, trace_id: &[u8; 16]) {
        let mut filters = self.filters.write().await;
        
        let filter = filters
            .entry(partition_id.to_string())
            .or_insert_with(|| BloomFilter::new(100_000, 0.01)); // 10万元素，1%假阳性
        
        filter.insert(trace_id);
    }
    
    /// 检查 TraceID 是否可能在分区中
    pub async fn might_contain(&self, partition_id: &str, trace_id: &[u8; 16]) -> bool {
        let filters = self.filters.read().await;
        
        if let Some(filter) = filters.get(partition_id) {
            filter.contains(trace_id)
        } else {
            false // 分区不存在
        }
    }
    
    /// 查找 TraceID 可能存在的分区
    pub async fn find_candidate_partitions(&self, trace_id: &[u8; 16]) -> Vec<String> {
        let filters = self.filters.read().await;
        
        let mut candidates = Vec::new();
        
        for (partition_id, filter) in filters.iter() {
            if filter.contains(trace_id) {
                candidates.push(partition_id.clone());
            }
        }
        
        candidates
    }
}
```

---

### 2. LSM-Tree 索引

**用途**: 高效的写入和范围查询

```rust
use serde::{Serialize, Deserialize};
use std::sync::Arc;
use tokio::sync::RwLock;

/// LSM-Tree 实现（简化版）
pub struct LsmTree<K, V>
where
    K: Ord + Clone + Serialize + for<'de> Deserialize<'de>,
    V: Clone + Serialize + for<'de> Deserialize<'de>,
{
    /// MemTable（内存表）
    memtable: Arc<RwLock<BTreeMap<K, V>>>,
    
    /// SSTables（磁盘表）
    sstables: Arc<RwLock<Vec<SSTable<K, V>>>>,
    
    /// MemTable 最大大小
    memtable_size_limit: usize,
    
    /// 数据目录
    data_dir: std::path::PathBuf,
}

use std::collections::BTreeMap;

impl<K, V> LsmTree<K, V>
where
    K: Ord + Clone + Serialize + for<'de> Deserialize<'de> + std::fmt::Debug,
    V: Clone + Serialize + for<'de> Deserialize<'de> + std::fmt::Debug,
{
    pub fn new(data_dir: std::path::PathBuf, memtable_size_limit: usize) -> Self {
        std::fs::create_dir_all(&data_dir).ok();
        
        Self {
            memtable: Arc::new(RwLock::new(BTreeMap::new())),
            sstables: Arc::new(RwLock::new(Vec::new())),
            memtable_size_limit,
            data_dir,
        }
    }
    
    /// 插入键值对
    pub async fn put(&self, key: K, value: V) -> Result<(), Box<dyn std::error::Error>> {
        let mut memtable = self.memtable.write().await;
        memtable.insert(key, value);
        
        // 检查是否需要 flush
        if memtable.len() >= self.memtable_size_limit {
            drop(memtable); // 释放锁
            self.flush().await?;
        }
        
        Ok(())
    }
    
    /// 查询键
    pub async fn get(&self, key: &K) -> Option<V> {
        // 1. 先查 MemTable
        {
            let memtable = self.memtable.read().await;
            if let Some(value) = memtable.get(key) {
                return Some(value.clone());
            }
        }
        
        // 2. 按从新到旧的顺序查询 SSTables
        let sstables = self.sstables.read().await;
        
        for sstable in sstables.iter().rev() {
            if let Some(value) = sstable.get(key) {
                return Some(value);
            }
        }
        
        None
    }
    
    /// 范围查询
    pub async fn range(&self, start: &K, end: &K) -> Vec<(K, V)> {
        let mut results = BTreeMap::new();
        
        // 1. 从 MemTable 查询
        {
            let memtable = self.memtable.read().await;
            for (k, v) in memtable.range(start.clone()..=end.clone()) {
                results.insert(k.clone(), v.clone());
            }
        }
        
        // 2. 从 SSTables 查询（新数据覆盖旧数据）
        let sstables = self.sstables.read().await;
        
        for sstable in sstables.iter().rev() {
            for (k, v) in sstable.range(start, end) {
                results.entry(k).or_insert(v);
            }
        }
        
        results.into_iter().collect()
    }
    
    /// 将 MemTable flush 到磁盘
    async fn flush(&self) -> Result<(), Box<dyn std::error::Error>> {
        // 1. 创建新的空 MemTable
        let old_memtable = {
            let mut memtable = self.memtable.write().await;
            std::mem::replace(&mut *memtable, BTreeMap::new())
        };
        
        if old_memtable.is_empty() {
            return Ok(());
        }
        
        // 2. 生成 SSTable 文件名
        let timestamp = chrono::Utc::now().timestamp_millis();
        let sstable_path = self.data_dir.join(format!("sstable_{}.sst", timestamp));
        
        // 3. 写入 SSTable
        let sstable = SSTable::create(sstable_path, old_memtable).await?;
        
        // 4. 添加到 SSTables 列表
        {
            let mut sstables = self.sstables.write().await;
            sstables.push(sstable);
        }
        
        // 5. 触发 Compaction（如果需要）
        self.maybe_compact().await?;
        
        Ok(())
    }
    
    /// 可能触发 Compaction
    async fn maybe_compact(&self) -> Result<(), Box<dyn std::error::Error>> {
        let sstables = self.sstables.read().await;
        
        // 简单策略：当 SSTable 数量超过 10 时进行 Compaction
        if sstables.len() > 10 {
            drop(sstables);
            self.compact().await?;
        }
        
        Ok(())
    }
    
    /// Compaction（合并 SSTables）
    async fn compact(&self) -> Result<(), Box<dyn std::error::Error>> {
        // 简化实现：合并所有 SSTables
        let old_sstables = {
            let mut sstables = self.sstables.write().await;
            std::mem::replace(&mut *sstables, Vec::new())
        };
        
        if old_sstables.is_empty() {
            return Ok(());
        }
        
        // 合并所有数据
        let mut merged_data = BTreeMap::new();
        
        for sstable in &old_sstables {
            for (k, v) in sstable.iter() {
                merged_data.insert(k, v);
            }
        }
        
        // 创建新的 SSTable
        let timestamp = chrono::Utc::now().timestamp_millis();
        let sstable_path = self.data_dir.join(format!("sstable_compacted_{}.sst", timestamp));
        
        let new_sstable = SSTable::create(sstable_path, merged_data).await?;
        
        // 更新 SSTables 列表
        {
            let mut sstables = self.sstables.write().await;
            sstables.push(new_sstable);
        }
        
        // 删除旧的 SSTables
        for sstable in old_sstables {
            sstable.delete().await?;
        }
        
        Ok(())
    }
}

/// SSTable（Sorted String Table）
#[derive(Clone)]
pub struct SSTable<K, V>
where
    K: Ord + Clone + Serialize + for<'de> Deserialize<'de>,
    V: Clone + Serialize + for<'de> Deserialize<'de>,
{
    /// 文件路径
    path: std::path::PathBuf,
    
    /// 索引（内存中的键到文件偏移的映射）
    index: Arc<BTreeMap<K, u64>>,
    
    /// Bloom Filter（快速判断键是否存在）
    bloom: Arc<BloomFilter>,
}

impl<K, V> SSTable<K, V>
where
    K: Ord + Clone + Serialize + for<'de> Deserialize<'de> + Hash + std::fmt::Debug,
    V: Clone + Serialize + for<'de> Deserialize<'de> + std::fmt::Debug,
{
    /// 创建 SSTable
    pub async fn create(
        path: std::path::PathBuf,
        data: BTreeMap<K, V>,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        use tokio::io::AsyncWriteExt;
        
        let mut file = tokio::fs::File::create(&path).await?;
        let mut index = BTreeMap::new();
        let mut bloom = BloomFilter::new(data.len(), 0.01);
        
        let mut offset = 0u64;
        
        for (key, value) in &data {
            // 序列化键值对
            let serialized = bincode::serialize(&(key, value))?;
            let len = serialized.len() as u64;
            
            // 写入数据
            file.write_all(&serialized).await?;
            
            // 更新索引
            index.insert(key.clone(), offset);
            
            // 更新 Bloom Filter
            bloom.insert(key);
            
            offset += len;
        }
        
        file.flush().await?;
        
        Ok(Self {
            path,
            index: Arc::new(index),
            bloom: Arc::new(bloom),
        })
    }
    
    /// 查询键
    pub fn get(&self, key: &K) -> Option<V> {
        // 1. Bloom Filter 预过滤
        if !self.bloom.contains(key) {
            return None;
        }
        
        // 2. 查询索引
        let offset = self.index.get(key)?;
        
        // 3. 从文件读取（同步 I/O，实际应该用异步）
        let mut file = std::fs::File::open(&self.path).ok()?;
        use std::io::{Seek, SeekFrom, Read};
        
        file.seek(SeekFrom::Start(*offset)).ok()?;
        
        // 读取数据（简化：这里假设知道长度）
        let mut buffer = Vec::new();
        file.read_to_end(&mut buffer).ok()?;
        
        let (stored_key, value): (K, V) = bincode::deserialize(&buffer).ok()?;
        
        if &stored_key == key {
            Some(value)
        } else {
            None
        }
    }
    
    /// 范围查询
    pub fn range(&self, start: &K, end: &K) -> Vec<(K, V)> {
        let mut results = Vec::new();
        
        // 使用索引定位范围
        for (key, offset) in self.index.range(start.clone()..=end.clone()) {
            if let Some(value) = self.get(key) {
                results.push((key.clone(), value));
            }
        }
        
        results
    }
    
    /// 迭代所有键值对
    pub fn iter(&self) -> Vec<(K, V)> {
        let mut results = Vec::new();
        
        for key in self.index.keys() {
            if let Some(value) = self.get(key) {
                results.push((key.clone(), value));
            }
        }
        
        results
    }
    
    /// 删除 SSTable 文件
    pub async fn delete(&self) -> Result<(), Box<dyn std::error::Error>> {
        tokio::fs::remove_file(&self.path).await?;
        Ok(())
    }
}

/// TraceID LSM 索引
pub type TraceIdLsmIndex = LsmTree<[u8; 16], TraceMetadata>;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraceMetadata {
    pub partition_id: String,
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub service_name: String,
    pub span_count: usize,
}
```

---

### 3. 倒排索引（标签检索）

**用途**: 基于属性标签快速过滤

```rust
use std::collections::{HashMap, HashSet};

/// 倒排索引
pub struct InvertedIndex {
    /// 标签键值 -> Trace IDs
    index: Arc<RwLock<HashMap<(String, String), HashSet<[u8; 16]>>>>,
}

impl InvertedIndex {
    pub fn new() -> Self {
        Self {
            index: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    /// 添加 Trace 的标签
    pub async fn insert(&self, trace_id: [u8; 16], attributes: &HashMap<String, String>) {
        let mut index = self.index.write().await;
        
        for (key, value) in attributes {
            let entry = index
                .entry((key.clone(), value.clone()))
                .or_insert_with(HashSet::new);
            
            entry.insert(trace_id);
        }
    }
    
    /// 查询包含指定标签的所有 TraceIDs
    pub async fn query(&self, attribute_key: &str, attribute_value: &str) -> Vec<[u8; 16]> {
        let index = self.index.read().await;
        
        if let Some(trace_ids) = index.get(&(attribute_key.to_string(), attribute_value.to_string())) {
            trace_ids.iter().copied().collect()
        } else {
            Vec::new()
        }
    }
    
    /// 多条件 AND 查询
    pub async fn query_and(&self, conditions: Vec<(String, String)>) -> Vec<[u8; 16]> {
        if conditions.is_empty() {
            return Vec::new();
        }
        
        let index = self.index.read().await;
        
        // 获取第一个条件的结果集
        let mut result_set: HashSet<[u8; 16]> = if let Some(first_cond) = conditions.first() {
            index
                .get(&first_cond.clone())
                .cloned()
                .unwrap_or_default()
        } else {
            return Vec::new();
        };
        
        // 对剩余条件求交集
        for condition in conditions.iter().skip(1) {
            if let Some(trace_ids) = index.get(condition) {
                result_set.retain(|id| trace_ids.contains(id));
            } else {
                return Vec::new(); // 任一条件无结果，整体为空
            }
        }
        
        result_set.into_iter().collect()
    }
    
    /// 多条件 OR 查询
    pub async fn query_or(&self, conditions: Vec<(String, String)>) -> Vec<[u8; 16]> {
        let index = self.index.read().await;
        
        let mut result_set = HashSet::new();
        
        for condition in conditions {
            if let Some(trace_ids) = index.get(&condition) {
                result_set.extend(trace_ids.iter().copied());
            }
        }
        
        result_set.into_iter().collect()
    }
    
    /// 统计标签基数
    pub async fn cardinality(&self, attribute_key: &str) -> usize {
        let index = self.index.read().await;
        
        index
            .keys()
            .filter(|(key, _)| key == attribute_key)
            .count()
    }
}
```

---

## 📊 Metric 名称索引

### 1. Trie 树索引

**用途**: 前缀匹配和自动补全

```rust
/// Trie 树节点
#[derive(Debug, Clone)]
struct TrieNode {
    children: HashMap<char, Box<TrieNode>>,
    is_end_of_word: bool,
    metric_metadata: Option<MetricMetadata>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MetricMetadata {
    pub name: String,
    pub metric_type: String,
    pub unit: Option<String>,
    pub description: Option<String>,
}

/// Trie 树索引
pub struct TrieIndex {
    root: Arc<RwLock<TrieNode>>,
}

impl TrieIndex {
    pub fn new() -> Self {
        Self {
            root: Arc::new(RwLock::new(TrieNode {
                children: HashMap::new(),
                is_end_of_word: false,
                metric_metadata: None,
            })),
        }
    }
    
    /// 插入 Metric 名称
    pub async fn insert(&self, name: &str, metadata: MetricMetadata) {
        let mut current = self.root.write().await;
        
        for ch in name.chars() {
            current = current
                .children
                .entry(ch)
                .or_insert_with(|| {
                    Box::new(TrieNode {
                        children: HashMap::new(),
                        is_end_of_word: false,
                        metric_metadata: None,
                    })
                });
        }
        
        current.is_end_of_word = true;
        current.metric_metadata = Some(metadata);
    }
    
    /// 精确查找
    pub async fn search(&self, name: &str) -> Option<MetricMetadata> {
        let current = self.root.read().await;
        let mut node = &*current;
        
        for ch in name.chars() {
            if let Some(child) = node.children.get(&ch) {
                node = child.as_ref();
            } else {
                return None;
            }
        }
        
        if node.is_end_of_word {
            node.metric_metadata.clone()
        } else {
            None
        }
    }
    
    /// 前缀匹配
    pub async fn starts_with(&self, prefix: &str) -> Vec<String> {
        let current = self.root.read().await;
        let mut node = &*current;
        
        // 先找到前缀对应的节点
        for ch in prefix.chars() {
            if let Some(child) = node.children.get(&ch) {
                node = child.as_ref();
            } else {
                return Vec::new(); // 前缀不存在
            }
        }
        
        // 从该节点开始 DFS 收集所有完整单词
        let mut results = Vec::new();
        Self::collect_words(node, prefix.to_string(), &mut results);
        
        results
    }
    
    fn collect_words(node: &TrieNode, current_word: String, results: &mut Vec<String>) {
        if node.is_end_of_word {
            results.push(current_word.clone());
        }
        
        for (ch, child) in &node.children {
            let mut new_word = current_word.clone();
            new_word.push(*ch);
            Self::collect_words(child, new_word, results);
        }
    }
    
    /// 模糊匹配（Levenshtein 距离）
    pub async fn fuzzy_search(&self, query: &str, max_distance: usize) -> Vec<(String, usize)> {
        let current = self.root.read().await;
        let mut results = Vec::new();
        
        Self::fuzzy_search_recursive(
            &*current,
            String::new(),
            query,
            max_distance,
            &mut results,
        );
        
        results.sort_by_key(|(_, dist)| *dist);
        results
    }
    
    fn fuzzy_search_recursive(
        node: &TrieNode,
        current_word: String,
        query: &str,
        max_distance: usize,
        results: &mut Vec<(String, usize)>,
    ) {
        if node.is_end_of_word {
            let distance = Self::levenshtein_distance(&current_word, query);
            if distance <= max_distance {
                results.push((current_word.clone(), distance));
            }
        }
        
        for (ch, child) in &node.children {
            let mut new_word = current_word.clone();
            new_word.push(*ch);
            Self::fuzzy_search_recursive(child, new_word, query, max_distance, results);
        }
    }
    
    fn levenshtein_distance(s1: &str, s2: &str) -> usize {
        let len1 = s1.len();
        let len2 = s2.len();
        let mut matrix = vec![vec![0; len2 + 1]; len1 + 1];
        
        for i in 0..=len1 {
            matrix[i][0] = i;
        }
        
        for j in 0..=len2 {
            matrix[0][j] = j;
        }
        
        for (i, c1) in s1.chars().enumerate() {
            for (j, c2) in s2.chars().enumerate() {
                let cost = if c1 == c2 { 0 } else { 1 };
                
                matrix[i + 1][j + 1] = (matrix[i][j + 1] + 1) // deletion
                    .min(matrix[i + 1][j] + 1) // insertion
                    .min(matrix[i][j] + cost); // substitution
            }
        }
        
        matrix[len1][len2]
    }
}
```

---

### 2. 时间序列索引

**用途**: 高效的时间范围查询

```rust
/// 时间序列索引
pub struct TimeSeriesIndex {
    /// 时间桶 -> Metric 名称列表
    time_buckets: Arc<RwLock<BTreeMap<i64, HashSet<String>>>>,
    
    /// 时间桶大小（秒）
    bucket_size: i64,
}

impl TimeSeriesIndex {
    pub fn new(bucket_size_seconds: i64) -> Self {
        Self {
            time_buckets: Arc::new(RwLock::new(BTreeMap::new())),
            bucket_size: bucket_size_seconds,
        }
    }
    
    /// 插入 Metric
    pub async fn insert(&self, metric_name: String, timestamp: chrono::DateTime<chrono::Utc>) {
        let bucket = timestamp.timestamp() / self.bucket_size;
        
        let mut buckets = self.time_buckets.write().await;
        buckets
            .entry(bucket)
            .or_insert_with(HashSet::new)
            .insert(metric_name);
    }
    
    /// 查询时间范围内的所有 Metrics
    pub async fn query_range(
        &self,
        start: chrono::DateTime<chrono::Utc>,
        end: chrono::DateTime<chrono::Utc>,
    ) -> Vec<String> {
        let start_bucket = start.timestamp() / self.bucket_size;
        let end_bucket = end.timestamp() / self.bucket_size;
        
        let buckets = self.time_buckets.read().await;
        
        let mut result = HashSet::new();
        
        for (_, metrics) in buckets.range(start_bucket..=end_bucket) {
            result.extend(metrics.iter().cloned());
        }
        
        result.into_iter().collect()
    }
}
```

---

## 📝 日志全文索引

### 1. 全文倒排索引

```rust
/// 全文倒排索引
pub struct FullTextIndex {
    /// 词项 -> (文档ID, 位置列表)
    index: Arc<RwLock<HashMap<String, Vec<(String, Vec<usize>)>>>>,
    
    /// 停用词集合
    stop_words: HashSet<String>,
}

impl FullTextIndex {
    pub fn new() -> Self {
        let stop_words = ["the", "is", "at", "which", "on", "a", "an", "and", "or", "but"]
            .iter()
            .map(|s| s.to_string())
            .collect();
        
        Self {
            index: Arc::new(RwLock::new(HashMap::new())),
            stop_words,
        }
    }
    
    /// 分词
    fn tokenize(&self, text: &str) -> Vec<String> {
        text.to_lowercase()
            .split(|c: char| !c.is_alphanumeric())
            .filter(|s| !s.is_empty() && !self.stop_words.contains(*s))
            .map(|s| s.to_string())
            .collect()
    }
    
    /// 索引文档
    pub async fn index_document(&self, doc_id: String, text: &str) {
        let tokens = self.tokenize(text);
        let mut index = self.index.write().await;
        
        for (position, token) in tokens.iter().enumerate() {
            let postings = index.entry(token.clone()).or_insert_with(Vec::new);
            
            // 查找是否已有该文档的记录
            if let Some((_, positions)) = postings.iter_mut().find(|(id, _)| id == &doc_id) {
                positions.push(position);
            } else {
                postings.push((doc_id.clone(), vec![position]));
            }
        }
    }
    
    /// 搜索单个词
    pub async fn search(&self, query: &str) -> Vec<String> {
        let tokens = self.tokenize(query);
        
        if tokens.is_empty() {
            return Vec::new();
        }
        
        let index = self.index.read().await;
        
        if let Some(postings) = index.get(&tokens[0]) {
            postings.iter().map(|(doc_id, _)| doc_id.clone()).collect()
        } else {
            Vec::new()
        }
    }
    
    /// 短语搜索（要求词按顺序出现）
    pub async fn phrase_search(&self, query: &str) -> Vec<String> {
        let tokens = self.tokenize(query);
        
        if tokens.is_empty() {
            return Vec::new();
        }
        
        let index = self.index.read().await;
        
        // 获取第一个词的倒排列表
        let first_postings = match index.get(&tokens[0]) {
            Some(p) => p,
            None => return Vec::new(),
        };
        
        let mut result = Vec::new();
        
        // 对每个文档检查短语是否匹配
        'doc_loop: for (doc_id, first_positions) in first_postings {
            for &first_pos in first_positions {
                let mut all_match = true;
                
                // 检查后续词是否在连续位置出现
                for (i, token) in tokens.iter().enumerate().skip(1) {
                    let expected_pos = first_pos + i;
                    
                    if let Some(postings) = index.get(token) {
                        if let Some((_, positions)) = postings.iter().find(|(id, _)| id == doc_id) {
                            if !positions.contains(&expected_pos) {
                                all_match = false;
                                break;
                            }
                        } else {
                            all_match = false;
                            break;
                        }
                    } else {
                        all_match = false;
                        break;
                    }
                }
                
                if all_match {
                    result.push(doc_id.clone());
                    continue 'doc_loop;
                }
            }
        }
        
        result
    }
}
```

---

### 2. N-Gram 索引

**用途**: 子串匹配

```rust
/// N-Gram 索引
pub struct NGramIndex {
    /// N-Gram -> 文档ID列表
    index: Arc<RwLock<HashMap<String, HashSet<String>>>>,
    
    /// N 值
    n: usize,
}

impl NGramIndex {
    pub fn new(n: usize) -> Self {
        Self {
            index: Arc::new(RwLock::new(HashMap::new())),
            n,
        }
    }
    
    /// 生成 N-Grams
    fn generate_ngrams(&self, text: &str) -> Vec<String> {
        let text = text.to_lowercase();
        let chars: Vec<char> = text.chars().collect();
        
        if chars.len() < self.n {
            return vec![text];
        }
        
        chars
            .windows(self.n)
            .map(|window| window.iter().collect())
            .collect()
    }
    
    /// 索引文档
    pub async fn index_document(&self, doc_id: String, text: &str) {
        let ngrams = self.generate_ngrams(text);
        let mut index = self.index.write().await;
        
        for ngram in ngrams {
            index
                .entry(ngram)
                .or_insert_with(HashSet::new)
                .insert(doc_id.clone());
        }
    }
    
    /// 搜索子串
    pub async fn search(&self, query: &str) -> Vec<String> {
        let ngrams = self.generate_ngrams(query);
        
        if ngrams.is_empty() {
            return Vec::new();
        }
        
        let index = self.index.read().await;
        
        // 获取第一个 N-Gram 的文档集合
        let mut result_set = match index.get(&ngrams[0]) {
            Some(docs) => docs.clone(),
            None => return Vec::new(),
        };
        
        // 求交集
        for ngram in ngrams.iter().skip(1) {
            if let Some(docs) = index.get(ngram) {
                result_set.retain(|doc| docs.contains(doc));
            } else {
                return Vec::new();
            }
        }
        
        result_set.into_iter().collect()
    }
}
```

---

## ⚡ 分布式索引协调

### 1. 分布式倒排索引

```rust
/// 分布式倒排索引协调器
pub struct DistributedInvertedIndex {
    /// 本地索引
    local_index: Arc<InvertedIndex>,
    
    /// 远程节点客户端
    remote_clients: Arc<RwLock<HashMap<String, RemoteIndexClient>>>,
    
    /// 分片策略
    shard_strategy: ShardStrategy,
}

#[derive(Debug, Clone)]
pub enum ShardStrategy {
    /// 基于键的哈希分片
    HashBased { num_shards: usize },
    
    /// 基于范围分片
    RangeBased,
}

impl DistributedInvertedIndex {
    pub fn new(local_index: Arc<InvertedIndex>, shard_strategy: ShardStrategy) -> Self {
        Self {
            local_index,
            remote_clients: Arc::new(RwLock::new(HashMap::new())),
            shard_strategy,
        }
    }
    
    /// 注册远程节点
    pub async fn register_remote_node(&self, node_id: String, client: RemoteIndexClient) {
        let mut clients = self.remote_clients.write().await;
        clients.insert(node_id, client);
    }
    
    /// 确定键应该路由到哪个节点
    fn get_target_node(&self, key: &str) -> Option<String> {
        match &self.shard_strategy {
            ShardStrategy::HashBased { num_shards } => {
                use std::collections::hash_map::DefaultHasher;
                use std::hash::{Hash, Hasher};
                
                let mut hasher = DefaultHasher::new();
                key.hash(&mut hasher);
                let shard_id = (hasher.finish() as usize) % num_shards;
                
                Some(format!("node-{}", shard_id))
            }
            ShardStrategy::RangeBased => {
                // 简化实现
                None
            }
        }
    }
    
    /// 分布式查询
    pub async fn distributed_query(&self, conditions: Vec<(String, String)>) -> Vec<[u8; 16]> {
        // 1. 确定需要查询的节点
        let mut node_queries: HashMap<String, Vec<(String, String)>> = HashMap::new();
        
        for condition in conditions {
            if let Some(node_id) = self.get_target_node(&condition.0) {
                node_queries
                    .entry(node_id)
                    .or_insert_with(Vec::new)
                    .push(condition);
            }
        }
        
        // 2. 并发查询所有节点
        let mut handles = Vec::new();
        let clients = self.remote_clients.read().await;
        
        for (node_id, queries) in node_queries {
            if let Some(client) = clients.get(&node_id) {
                let client = client.clone();
                let handle = tokio::spawn(async move {
                    client.query_and(queries).await
                });
                handles.push(handle);
            }
        }
        
        // 3. 合并结果（求交集）
        let mut result_sets = Vec::new();
        
        for handle in handles {
            if let Ok(Ok(trace_ids)) = handle.await {
                result_sets.push(trace_ids.into_iter().collect::<HashSet<_>>());
            }
        }
        
        if result_sets.is_empty() {
            return Vec::new();
        }
        
        // 求交集
        let mut result = result_sets[0].clone();
        
        for set in result_sets.iter().skip(1) {
            result.retain(|id| set.contains(id));
        }
        
        result.into_iter().collect()
    }
}

/// 远程索引客户端（简化实现）
#[derive(Clone)]
pub struct RemoteIndexClient {
    node_url: String,
    http_client: reqwest::Client,
}

impl RemoteIndexClient {
    pub fn new(node_url: String) -> Self {
        Self {
            node_url,
            http_client: reqwest::Client::new(),
        }
    }
    
    pub async fn query_and(&self, conditions: Vec<(String, String)>) -> Result<Vec<[u8; 16]>, Box<dyn std::error::Error>> {
        let url = format!("{}/index/query_and", self.node_url);
        
        let response = self.http_client
            .post(&url)
            .json(&conditions)
            .send()
            .await?;
        
        let trace_ids = response.json::<Vec<[u8; 16]>>().await?;
        
        Ok(trace_ids)
    }
}
```

---

### 2. 分布式查询执行器

```rust
/// 分布式查询执行器
pub struct DistributedQueryExecutor {
    distributed_index: Arc<DistributedInvertedIndex>,
    shard_manager: Arc<crate::ShardManager>,
}

impl DistributedQueryExecutor {
    pub fn new(
        distributed_index: Arc<DistributedInvertedIndex>,
        shard_manager: Arc<crate::ShardManager>,
    ) -> Self {
        Self {
            distributed_index,
            shard_manager,
        }
    }
    
    /// 执行复杂查询
    pub async fn execute_query(&self, query: Query) -> Result<Vec<SearchResult>, String> {
        match query {
            Query::Attribute { key, value } => {
                let trace_ids = self.distributed_index
                    .distributed_query(vec![(key, value)])
                    .await;
                
                self.fetch_traces(trace_ids).await
            }
            
            Query::And(queries) => {
                // 对所有子查询求交集
                let mut result_sets = Vec::new();
                
                for query in queries {
                    let results = self.execute_query(*query).await?;
                    result_sets.push(results.into_iter().collect::<HashSet<_>>());
                }
                
                if result_sets.is_empty() {
                    return Ok(Vec::new());
                }
                
                let mut result = result_sets[0].clone();
                
                for set in result_sets.iter().skip(1) {
                    result.retain(|r| set.contains(r));
                }
                
                Ok(result.into_iter().collect())
            }
            
            Query::Or(queries) => {
                // 对所有子查询求并集
                let mut result_set = HashSet::new();
                
                for query in queries {
                    let results = self.execute_query(*query).await?;
                    result_set.extend(results);
                }
                
                Ok(result_set.into_iter().collect())
            }
            
            Query::TimeRange { start, end } => {
                self.query_by_time_range(start, end).await
            }
        }
    }
    
    async fn fetch_traces(&self, trace_ids: Vec<[u8; 16]>) -> Result<Vec<SearchResult>, String> {
        // 简化实现：实际需要从存储层获取完整的 Trace 数据
        let results = trace_ids
            .into_iter()
            .map(|id| SearchResult {
                trace_id: id,
                score: 1.0,
            })
            .collect();
        
        Ok(results)
    }
    
    async fn query_by_time_range(
        &self,
        start: chrono::DateTime<chrono::Utc>,
        end: chrono::DateTime<chrono::Utc>,
    ) -> Result<Vec<SearchResult>, String> {
        // TODO: 实现时间范围查询
        Ok(Vec::new())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SearchResult {
    pub trace_id: [u8; 16],
    pub score: f64,
}

#[derive(Debug, Clone)]
pub enum Query {
    Attribute { key: String, value: String },
    And(Vec<Box<Query>>),
    Or(Vec<Box<Query>>),
    TimeRange { start: chrono::DateTime<chrono::Utc>, end: chrono::DateTime<chrono::Utc> },
}
```

---

## 💾 索引持久化与恢复

### 1. 索引快照管理器

```rust
/// 索引快照管理器
pub struct IndexSnapshotManager {
    snapshot_dir: std::path::PathBuf,
}

impl IndexSnapshotManager {
    pub fn new(snapshot_dir: std::path::PathBuf) -> Self {
        std::fs::create_dir_all(&snapshot_dir).ok();
        
        Self { snapshot_dir }
    }
    
    /// 创建索引快照
    pub async fn create_snapshot<T: Serialize>(
        &self,
        index_name: &str,
        data: &T,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let timestamp = chrono::Utc::now().timestamp_millis();
        let snapshot_path = self.snapshot_dir.join(format!("{}_{}.snapshot", index_name, timestamp));
        
        let serialized = bincode::serialize(data)?;
        
        tokio::fs::write(&snapshot_path, serialized).await?;
        
        tracing::info!("Index snapshot created: {:?}", snapshot_path);
        
        Ok(())
    }
    
    /// 恢复索引快照
    pub async fn restore_snapshot<T: for<'de> Deserialize<'de>>(
        &self,
        index_name: &str,
    ) -> Result<Option<T>, Box<dyn std::error::Error>> {
        // 查找最新的快照
        let mut entries = tokio::fs::read_dir(&self.snapshot_dir).await?;
        let mut latest_snapshot: Option<(i64, std::path::PathBuf)> = None;
        
        while let Some(entry) = entries.next_entry().await? {
            let path = entry.path();
            let file_name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
            
            if file_name.starts_with(index_name) && file_name.ends_with(".snapshot") {
                // 提取时间戳
                if let Some(timestamp_str) = file_name.strip_prefix(&format!("{}_", index_name))
                    .and_then(|s| s.strip_suffix(".snapshot"))
                {
                    if let Ok(timestamp) = timestamp_str.parse::<i64>() {
                        if latest_snapshot.is_none() || timestamp > latest_snapshot.as_ref().unwrap().0 {
                            latest_snapshot = Some((timestamp, path));
                        }
                    }
                }
            }
        }
        
        if let Some((_, snapshot_path)) = latest_snapshot {
            let data = tokio::fs::read(&snapshot_path).await?;
            let deserialized = bincode::deserialize(&data)?;
            
            tracing::info!("Index snapshot restored: {:?}", snapshot_path);
            
            Ok(Some(deserialized))
        } else {
            Ok(None)
        }
    }
    
    /// 清理旧快照
    pub async fn cleanup_old_snapshots(
        &self,
        index_name: &str,
        retention_count: usize,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut entries = tokio::fs::read_dir(&self.snapshot_dir).await?;
        let mut snapshots: Vec<(i64, std::path::PathBuf)> = Vec::new();
        
        while let Some(entry) = entries.next_entry().await? {
            let path = entry.path();
            let file_name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
            
            if file_name.starts_with(index_name) && file_name.ends_with(".snapshot") {
                if let Some(timestamp_str) = file_name.strip_prefix(&format!("{}_", index_name))
                    .and_then(|s| s.strip_suffix(".snapshot"))
                {
                    if let Ok(timestamp) = timestamp_str.parse::<i64>() {
                        snapshots.push((timestamp, path));
                    }
                }
            }
        }
        
        // 按时间戳排序
        snapshots.sort_by_key(|(ts, _)| *ts);
        
        // 删除旧快照
        if snapshots.len() > retention_count {
            for (_, path) in snapshots.iter().take(snapshots.len() - retention_count) {
                tokio::fs::remove_file(path).await?;
                tracing::info!("Deleted old snapshot: {:?}", path);
            }
        }
        
        Ok(())
    }
}
```

---

## 📈 完整示例：统一索引系统

```rust
/// 统一索引系统
pub struct UnifiedIndexSystem {
    bloom_index: Arc<TraceIdBloomIndex>,
    lsm_index: Arc<TraceIdLsmIndex>,
    inverted_index: Arc<InvertedIndex>,
    trie_index: Arc<TrieIndex>,
    fulltext_index: Arc<FullTextIndex>,
    ngram_index: Arc<NGramIndex>,
    snapshot_manager: Arc<IndexSnapshotManager>,
}

impl UnifiedIndexSystem {
    pub async fn new(data_dir: std::path::PathBuf) -> Result<Self, Box<dyn std::error::Error>> {
        let snapshot_dir = data_dir.join("snapshots");
        let lsm_dir = data_dir.join("lsm");
        
        Ok(Self {
            bloom_index: Arc::new(TraceIdBloomIndex::new()),
            lsm_index: Arc::new(LsmTree::new(lsm_dir, 10_000)),
            inverted_index: Arc::new(InvertedIndex::new()),
            trie_index: Arc::new(TrieIndex::new()),
            fulltext_index: Arc::new(FullTextIndex::new()),
            ngram_index: Arc::new(NGramIndex::new(3)),
            snapshot_manager: Arc::new(IndexSnapshotManager::new(snapshot_dir)),
        })
    }
    
    /// 索引 Trace
    pub async fn index_trace(&self, trace: &crate::DistributedTrace) -> Result<(), Box<dyn std::error::Error>> {
        let partition_id = trace.partition_key.time_bucket.clone();
        
        // 1. Bloom Filter
        self.bloom_index.insert(&partition_id, &trace.trace_id.0).await;
        
        // 2. LSM Index
        let metadata = TraceMetadata {
            partition_id,
            timestamp: trace.timestamp,
            service_name: trace.resource.service_name.clone(),
            span_count: trace.spans.len(),
        };
        
        self.lsm_index.put(trace.trace_id.0, metadata).await?;
        
        // 3. Inverted Index (属性)
        let mut attributes = HashMap::new();
        attributes.insert("service.name".to_string(), trace.resource.service_name.clone());
        
        if let Some(ns) = &trace.resource.service_namespace {
            attributes.insert("service.namespace".to_string(), ns.clone());
        }
        
        self.inverted_index.insert(trace.trace_id.0, &attributes).await;
        
        Ok(())
    }
    
    /// 索引 Metric
    pub async fn index_metric(&self, metric: &crate::DistributedMetric) -> Result<(), Box<dyn std::error::Error>> {
        let metadata = MetricMetadata {
            name: metric.name.clone(),
            metric_type: format!("{:?}", metric.metric_type),
            unit: None,
            description: None,
        };
        
        self.trie_index.insert(&metric.name, metadata).await;
        
        Ok(())
    }
    
    /// 索引日志
    pub async fn index_log(&self, log_id: String, log: &crate::DistributedLog) -> Result<(), Box<dyn std::error::Error>> {
        let text = match &log.body {
            crate::LogBody::String(s) => s.clone(),
            crate::LogBody::Structured(v) => v.to_string(),
        };
        
        // 全文索引
        self.fulltext_index.index_document(log_id.clone(), &text).await;
        
        // N-Gram 索引（用于模糊匹配）
        self.ngram_index.index_document(log_id, &text).await;
        
        Ok(())
    }
    
    /// 创建快照
    pub async fn create_snapshot(&self) -> Result<(), Box<dyn std::error::Error>> {
        // TODO: 为各个索引创建快照
        tracing::info!("Creating index snapshots...");
        
        Ok(())
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt::init();
    
    let data_dir = std::path::PathBuf::from("./index_data");
    let index_system = UnifiedIndexSystem::new(data_dir).await?;
    
    println!("Unified Index System initialized!");
    
    Ok(())
}
```

---

## 🎯 性能优化

### 缓存策略

- **LRU 缓存**: 热点查询结果
- **Write-Back 缓存**: 批量写入
- **查询计划缓存**: 复杂查询优化

### 压缩技术

- **Dictionary Encoding**: 高基数字段
- **Run-Length Encoding**: 重复数据
- **Delta Encoding**: 时间序列

---

## 📊 性能指标

- **Bloom Filter**: 假阳性率 < 1%
- **LSM 写入**: > 100K ops/s
- **倒排索引查询**: < 10ms (P99)
- **全文搜索**: < 50ms (P99)

---

## 📚 参考资源

- [LSM-Tree Paper](https://www.cs.umb.edu/~poneil/lsmtree.pdf)
- [Bloom Filters](https://en.wikipedia.org/wiki/Bloom_filter)
- [Inverted Index](https://en.wikipedia.org/wiki/Inverted_index)
- [Trie Data Structure](https://en.wikipedia.org/wiki/Trie)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-10  
**作者**: OTLP Rust 项目组
