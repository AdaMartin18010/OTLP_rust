# 日志全文搜索 - Rust 完整实现

> **文档版本**: v1.0.0  
> **Rust 版本**: 1.90+  
> **最后更新**: 2025-10-10

---

## 📋 目录

- [日志全文搜索 - Rust 完整实现](#日志全文搜索---rust-完整实现)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [核心功能](#核心功能)
    - [应用场景](#应用场景)
  - [🔍 全文索引](#-全文索引)
    - [1. 倒排索引构建](#1-倒排索引构建)
    - [2. 分词器](#2-分词器)
    - [3. 索引优化](#3-索引优化)
  - [🔎 搜索查询](#-搜索查询)
    - [1. 关键词搜索](#1-关键词搜索)
    - [2. 短语搜索](#2-短语搜索)
    - [3. 模糊搜索](#3-模糊搜索)
  - [📝 正则表达式搜索](#-正则表达式搜索)
    - [1. 正则查询引擎](#1-正则查询引擎)
    - [2. 正则优化](#2-正则优化)
  - [🎯 高级查询](#-高级查询)
    - [1. 布尔查询](#1-布尔查询)
    - [2. 范围查询](#2-范围查询)
    - [3. 聚合查询](#3-聚合查询)
  - [📊 日志分析](#-日志分析)
    - [1. 日志模式识别](#1-日志模式识别)
    - [2. 异常检测](#2-异常检测)
  - [⚡ 性能优化](#-性能优化)
    - [1. 查询缓存](#1-查询缓存)
    - [2. 分片搜索](#2-分片搜索)
  - [📊 完整示例：日志搜索系统](#-完整示例日志搜索系统)
  - [🎯 最佳实践](#-最佳实践)
    - [索引优化](#索引优化)
    - [查询优化](#查询优化)
    - [存储优化](#存储优化)
  - [📚 参考资源](#-参考资源)

---

## 🎯 概述

日志全文搜索是 OTLP Logs 系统的核心功能，通过高效的全文索引和灵活的查询语言，帮助开发者快速定位和分析海量日志数据。

### 核心功能

- ✅ **全文索引** - 倒排索引、N-Gram、前缀索引
- ✅ **关键词搜索** - 精确匹配、模糊匹配
- ✅ **正则表达式** - 复杂模式匹配
- ✅ **布尔查询** - AND/OR/NOT 组合查询
- ✅ **日志分析** - 模式识别、异常检测
- ✅ **性能优化** - 查询缓存、分片搜索

### 应用场景

- 🔧 **故障排查** - 快速定位错误日志
- 🔧 **安全审计** - 安全事件检索
- 🔧 **业务分析** - 用户行为日志分析
- 🔧 **性能调优** - 慢查询日志分析

---

## 🔍 全文索引

### 1. 倒排索引构建

```rust
use std::sync::Arc;
use std::collections::{HashMap, HashSet};
use tokio::sync::RwLock;
use chrono::{DateTime, Utc};

/// 倒排索引构建器
pub struct InvertedIndexBuilder {
    index: Arc<RwLock<HashMap<String, PostingList>>>,
    tokenizer: Arc<Tokenizer>,
}

impl InvertedIndexBuilder {
    pub fn new(tokenizer: Arc<Tokenizer>) -> Self {
        Self {
            index: Arc::new(RwLock::new(HashMap::new())),
            tokenizer,
        }
    }
    
    /// 索引单条日志
    pub async fn index_log(&self, log: &LogRecord) {
        // 分词
        let tokens = self.tokenizer.tokenize(&log.message);
        
        let mut index = self.index.write().await;
        
        // 构建倒排索引
        for (position, token) in tokens.iter().enumerate() {
            let posting_list = index
                .entry(token.clone())
                .or_insert_with(PostingList::new);
            
            posting_list.add_posting(Posting {
                log_id: log.id.clone(),
                position,
                timestamp: log.timestamp,
            });
        }
    }
    
    /// 批量索引
    pub async fn index_logs_batch(&self, logs: Vec<LogRecord>) {
        for log in logs {
            self.index_log(&log).await;
        }
    }
    
    /// 搜索
    pub async fn search(&self, query: &str) -> Vec<String> {
        let tokens = self.tokenizer.tokenize(query);
        
        if tokens.is_empty() {
            return Vec::new();
        }
        
        let index = self.index.read().await;
        
        // 获取第一个词的posting list
        let mut result_set: Option<HashSet<String>> = None;
        
        for token in &tokens {
            if let Some(posting_list) = index.get(token) {
                let log_ids: HashSet<String> = posting_list
                    .postings
                    .iter()
                    .map(|p| p.log_id.clone())
                    .collect();
                
                result_set = match result_set {
                    Some(existing) => {
                        // 计算交集（AND 语义）
                        Some(existing.intersection(&log_ids).cloned().collect())
                    }
                    None => Some(log_ids),
                };
            } else {
                // 词不存在，返回空结果
                return Vec::new();
            }
        }
        
        result_set.unwrap_or_default().into_iter().collect()
    }
}

#[derive(Debug, Clone)]
pub struct LogRecord {
    pub id: String,
    pub timestamp: DateTime<Utc>,
    pub level: LogLevel,
    pub message: String,
    pub attributes: HashMap<String, String>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LogLevel {
    Trace,
    Debug,
    Info,
    Warn,
    Error,
}

#[derive(Debug, Clone)]
pub struct PostingList {
    pub postings: Vec<Posting>,
}

impl PostingList {
    fn new() -> Self {
        Self {
            postings: Vec::new(),
        }
    }
    
    fn add_posting(&mut self, posting: Posting) {
        self.postings.push(posting);
    }
}

#[derive(Debug, Clone)]
pub struct Posting {
    pub log_id: String,
    pub position: usize,
    pub timestamp: DateTime<Utc>,
}
```

---

### 2. 分词器

```rust
/// 分词器
pub struct Tokenizer {
    stop_words: HashSet<String>,
}

impl Tokenizer {
    pub fn new() -> Self {
        let stop_words: HashSet<String> = [
            "the", "a", "an", "and", "or", "but", "is", "are", "was", "were",
            "in", "on", "at", "to", "from", "with", "by", "for",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect();
        
        Self { stop_words }
    }
    
    /// 分词
    pub fn tokenize(&self, text: &str) -> Vec<String> {
        text.to_lowercase()
            .split(|c: char| !c.is_alphanumeric())
            .filter(|s| !s.is_empty())
            .filter(|s| !self.stop_words.contains(*s))
            .map(|s| s.to_string())
            .collect()
    }
    
    /// 带位置的分词
    pub fn tokenize_with_positions(&self, text: &str) -> Vec<(String, usize)> {
        text.to_lowercase()
            .split(|c: char| !c.is_alphanumeric())
            .filter(|s| !s.is_empty())
            .filter(|s| !self.stop_words.contains(*s))
            .enumerate()
            .map(|(pos, s)| (s.to_string(), pos))
            .collect()
    }
    
    /// N-Gram 分词
    pub fn ngram_tokenize(&self, text: &str, n: usize) -> Vec<String> {
        let chars: Vec<char> = text.chars().collect();
        
        if chars.len() < n {
            return vec![text.to_string()];
        }
        
        (0..=chars.len() - n)
            .map(|i| chars[i..i + n].iter().collect())
            .collect()
    }
}
```

---

### 3. 索引优化

```rust
/// 索引压缩器（前端编码）
pub struct IndexCompressor;

impl IndexCompressor {
    /// 压缩 posting list（增量编码）
    pub fn compress_postings(postings: &[Posting]) -> Vec<u8> {
        if postings.is_empty() {
            return Vec::new();
        }
        
        let mut compressed = Vec::new();
        
        // 第一个文档ID
        compressed.extend_from_slice(&postings[0].log_id.as_bytes());
        compressed.push(b'\0'); // 分隔符
        
        // 后续文档使用增量编码（简化版本）
        for i in 1..postings.len() {
            compressed.extend_from_slice(&postings[i].log_id.as_bytes());
            compressed.push(b'\0');
        }
        
        compressed
    }
    
    /// 解压 posting list
    pub fn decompress_postings(compressed: &[u8]) -> Vec<String> {
        compressed
            .split(|&b| b == b'\0')
            .filter(|s| !s.is_empty())
            .map(|s| String::from_utf8_lossy(s).to_string())
            .collect()
    }
}

/// 索引合并器
pub struct IndexMerger;

impl IndexMerger {
    /// 合并多个索引
    pub fn merge_indices(
        indices: Vec<HashMap<String, PostingList>>,
    ) -> HashMap<String, PostingList> {
        let mut merged = HashMap::new();
        
        for index in indices {
            for (term, posting_list) in index {
                merged
                    .entry(term)
                    .or_insert_with(PostingList::new)
                    .postings
                    .extend(posting_list.postings);
            }
        }
        
        // 排序每个posting list
        for posting_list in merged.values_mut() {
            posting_list.postings.sort_by_key(|p| p.timestamp);
        }
        
        merged
    }
}
```

---

## 🔎 搜索查询

### 1. 关键词搜索

```rust
/// 关键词搜索引擎
pub struct KeywordSearchEngine {
    index_builder: Arc<InvertedIndexBuilder>,
}

impl KeywordSearchEngine {
    pub fn new(index_builder: Arc<InvertedIndexBuilder>) -> Self {
        Self { index_builder }
    }
    
    /// 精确搜索
    pub async fn exact_search(&self, keyword: &str) -> Vec<String> {
        self.index_builder.search(keyword).await
    }
    
    /// 前缀搜索
    pub async fn prefix_search(&self, prefix: &str) -> Vec<String> {
        let index = self.index_builder.index.read().await;
        
        let mut result_set = HashSet::new();
        
        for (term, posting_list) in index.iter() {
            if term.starts_with(prefix) {
                for posting in &posting_list.postings {
                    result_set.insert(posting.log_id.clone());
                }
            }
        }
        
        result_set.into_iter().collect()
    }
    
    /// 通配符搜索
    pub async fn wildcard_search(&self, pattern: &str) -> Vec<String> {
        let index = self.index_builder.index.read().await;
        
        let mut result_set = HashSet::new();
        
        // 将通配符转换为正则表达式
        let regex_pattern = pattern.replace('*', ".*").replace('?', ".");
        let regex = regex::Regex::new(&regex_pattern).unwrap();
        
        for (term, posting_list) in index.iter() {
            if regex.is_match(term) {
                for posting in &posting_list.postings {
                    result_set.insert(posting.log_id.clone());
                }
            }
        }
        
        result_set.into_iter().collect()
    }
}
```

---

### 2. 短语搜索

```rust
/// 短语搜索引擎
pub struct PhraseSearchEngine {
    index_builder: Arc<InvertedIndexBuilder>,
}

impl PhraseSearchEngine {
    pub fn new(index_builder: Arc<InvertedIndexBuilder>) -> Self {
        Self { index_builder }
    }
    
    /// 短语搜索（精确位置匹配）
    pub async fn phrase_search(&self, phrase: &str) -> Vec<String> {
        let tokens = self.index_builder.tokenizer.tokenize(phrase);
        
        if tokens.is_empty() {
            return Vec::new();
        }
        
        let index = self.index_builder.index.read().await;
        
        // 获取第一个词的 posting list
        let first_postings = match index.get(&tokens[0]) {
            Some(list) => &list.postings,
            None => return Vec::new(),
        };
        
        let mut result_set = Vec::new();
        
        // 对每个文档，检查后续词是否在连续位置
        for posting in first_postings {
            let mut all_found = true;
            
            for (i, token) in tokens.iter().enumerate().skip(1) {
                if let Some(posting_list) = index.get(token) {
                    // 检查是否有在正确位置的 posting
                    let found = posting_list.postings.iter().any(|p| {
                        p.log_id == posting.log_id && p.position == posting.position + i
                    });
                    
                    if !found {
                        all_found = false;
                        break;
                    }
                } else {
                    all_found = false;
                    break;
                }
            }
            
            if all_found {
                result_set.push(posting.log_id.clone());
            }
        }
        
        result_set
    }
}
```

---

### 3. 模糊搜索

```rust
/// 模糊搜索引擎（基于编辑距离）
pub struct FuzzySearchEngine {
    index_builder: Arc<InvertedIndexBuilder>,
    max_distance: usize,
}

impl FuzzySearchEngine {
    pub fn new(index_builder: Arc<InvertedIndexBuilder>, max_distance: usize) -> Self {
        Self {
            index_builder,
            max_distance,
        }
    }
    
    /// 模糊搜索
    pub async fn fuzzy_search(&self, query: &str) -> Vec<String> {
        let index = self.index_builder.index.read().await;
        
        let mut result_set = HashSet::new();
        
        // 查找编辑距离在阈值内的所有词
        for (term, posting_list) in index.iter() {
            let distance = Self::levenshtein_distance(query, term);
            
            if distance <= self.max_distance {
                for posting in &posting_list.postings {
                    result_set.insert(posting.log_id.clone());
                }
            }
        }
        
        result_set.into_iter().collect()
    }
    
    /// Levenshtein 编辑距离
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
        
        let s1_chars: Vec<char> = s1.chars().collect();
        let s2_chars: Vec<char> = s2.chars().collect();
        
        for i in 1..=len1 {
            for j in 1..=len2 {
                let cost = if s1_chars[i - 1] == s2_chars[j - 1] {
                    0
                } else {
                    1
                };
                
                matrix[i][j] = (matrix[i - 1][j] + 1)
                    .min(matrix[i][j - 1] + 1)
                    .min(matrix[i - 1][j - 1] + cost);
            }
        }
        
        matrix[len1][len2]
    }
}
```

---

## 📝 正则表达式搜索

### 1. 正则查询引擎

```rust
use regex::Regex;

/// 正则查询引擎
pub struct RegexQueryEngine {
    log_storage: Arc<LogStorage>,
}

impl RegexQueryEngine {
    pub fn new(log_storage: Arc<LogStorage>) -> Self {
        Self { log_storage }
    }
    
    /// 正则搜索
    pub async fn regex_search(&self, pattern: &str) -> Result<Vec<LogRecord>, Box<dyn std::error::Error>> {
        let regex = Regex::new(pattern)?;
        
        let all_logs = self.log_storage.get_all_logs().await;
        
        let matching_logs: Vec<LogRecord> = all_logs
            .into_iter()
            .filter(|log| regex.is_match(&log.message))
            .collect();
        
        Ok(matching_logs)
    }
    
    /// 正则搜索（并行）
    pub async fn regex_search_parallel(
        &self,
        pattern: &str,
    ) -> Result<Vec<LogRecord>, Box<dyn std::error::Error>> {
        let regex = Arc::new(Regex::new(pattern)?);
        
        let all_logs = self.log_storage.get_all_logs().await;
        
        let chunk_size = (all_logs.len() + 7) / 8; // 8 个线程
        let mut handles = Vec::new();
        
        for chunk in all_logs.chunks(chunk_size) {
            let regex = regex.clone();
            let chunk = chunk.to_vec();
            
            let handle = tokio::spawn(async move {
                chunk
                    .into_iter()
                    .filter(|log| regex.is_match(&log.message))
                    .collect::<Vec<LogRecord>>()
            });
            
            handles.push(handle);
        }
        
        let mut results = Vec::new();
        
        for handle in handles {
            if let Ok(chunk_results) = handle.await {
                results.extend(chunk_results);
            }
        }
        
        Ok(results)
    }
}
```

---

### 2. 正则优化

```rust
/// 正则查询优化器
pub struct RegexOptimizer;

impl RegexOptimizer {
    /// 提取正则中的固定前缀
    pub fn extract_prefix(pattern: &str) -> Option<String> {
        let mut prefix = String::new();
        
        for ch in pattern.chars() {
            if ch.is_alphanumeric() || ch == '_' {
                prefix.push(ch);
            } else {
                break;
            }
        }
        
        if prefix.is_empty() {
            None
        } else {
            Some(prefix)
        }
    }
    
    /// 优化正则查询（先用前缀索引过滤）
    pub async fn optimized_regex_search(
        &self,
        pattern: &str,
        index_builder: Arc<InvertedIndexBuilder>,
        log_storage: Arc<LogStorage>,
    ) -> Result<Vec<LogRecord>, Box<dyn std::error::Error>> {
        // 提取固定前缀
        if let Some(prefix) = Self::extract_prefix(pattern) {
            // 使用前缀索引预过滤
            let candidate_ids = KeywordSearchEngine::new(index_builder)
                .prefix_search(&prefix)
                .await;
            
            // 只对候选日志应用正则
            let regex = Regex::new(pattern)?;
            
            let mut results = Vec::new();
            
            for log_id in candidate_ids {
                if let Some(log) = log_storage.get_log(&log_id).await {
                    if regex.is_match(&log.message) {
                        results.push(log);
                    }
                }
            }
            
            Ok(results)
        } else {
            // 无法优化，全量扫描
            let regex_engine = RegexQueryEngine::new(log_storage);
            regex_engine.regex_search(pattern).await
        }
    }
}
```

---

## 🎯 高级查询

### 1. 布尔查询

```rust
/// 布尔查询引擎
pub struct BooleanQueryEngine {
    index_builder: Arc<InvertedIndexBuilder>,
}

impl BooleanQueryEngine {
    pub fn new(index_builder: Arc<InvertedIndexBuilder>) -> Self {
        Self { index_builder }
    }
    
    /// AND 查询
    pub async fn and_query(&self, terms: Vec<String>) -> Vec<String> {
        if terms.is_empty() {
            return Vec::new();
        }
        
        let index = self.index_builder.index.read().await;
        
        // 获取第一个词的结果
        let mut result_set: HashSet<String> = match index.get(&terms[0]) {
            Some(posting_list) => posting_list
                .postings
                .iter()
                .map(|p| p.log_id.clone())
                .collect(),
            None => return Vec::new(),
        };
        
        // 对后续词取交集
        for term in terms.iter().skip(1) {
            if let Some(posting_list) = index.get(term) {
                let term_set: HashSet<String> = posting_list
                    .postings
                    .iter()
                    .map(|p| p.log_id.clone())
                    .collect();
                
                result_set = result_set.intersection(&term_set).cloned().collect();
            } else {
                return Vec::new();
            }
        }
        
        result_set.into_iter().collect()
    }
    
    /// OR 查询
    pub async fn or_query(&self, terms: Vec<String>) -> Vec<String> {
        let index = self.index_builder.index.read().await;
        
        let mut result_set = HashSet::new();
        
        for term in terms {
            if let Some(posting_list) = index.get(&term) {
                for posting in &posting_list.postings {
                    result_set.insert(posting.log_id.clone());
                }
            }
        }
        
        result_set.into_iter().collect()
    }
    
    /// NOT 查询
    pub async fn not_query(&self, include: Vec<String>, exclude: Vec<String>) -> Vec<String> {
        let include_set: HashSet<String> = self.or_query(include).await.into_iter().collect();
        let exclude_set: HashSet<String> = self.or_query(exclude).await.into_iter().collect();
        
        include_set.difference(&exclude_set).cloned().collect()
    }
    
    /// 复合查询
    pub async fn complex_query(&self, query: BooleanQuery) -> Vec<String> {
        match query {
            BooleanQuery::And(queries) => {
                let mut results = Vec::new();
                
                for q in queries {
                    let sub_results = self.complex_query(*q).await;
                    results.push(sub_results);
                }
                
                // 计算交集
                if results.is_empty() {
                    return Vec::new();
                }
                
                let mut intersection: HashSet<String> = results[0].iter().cloned().collect();
                
                for result in results.iter().skip(1) {
                    let set: HashSet<String> = result.iter().cloned().collect();
                    intersection = intersection.intersection(&set).cloned().collect();
                }
                
                intersection.into_iter().collect()
            }
            BooleanQuery::Or(queries) => {
                let mut result_set = HashSet::new();
                
                for q in queries {
                    let sub_results = self.complex_query(*q).await;
                    result_set.extend(sub_results);
                }
                
                result_set.into_iter().collect()
            }
            BooleanQuery::Not(query) => {
                // 简化实现
                Vec::new()
            }
            BooleanQuery::Term(term) => {
                self.and_query(vec![term]).await
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum BooleanQuery {
    And(Vec<Box<BooleanQuery>>),
    Or(Vec<Box<BooleanQuery>>),
    Not(Box<BooleanQuery>),
    Term(String),
}
```

---

### 2. 范围查询

```rust
/// 范围查询引擎
pub struct RangeQueryEngine {
    log_storage: Arc<LogStorage>,
}

impl RangeQueryEngine {
    pub fn new(log_storage: Arc<LogStorage>) -> Self {
        Self { log_storage }
    }
    
    /// 时间范围查询
    pub async fn time_range_query(
        &self,
        start: DateTime<Utc>,
        end: DateTime<Utc>,
    ) -> Vec<LogRecord> {
        let all_logs = self.log_storage.get_all_logs().await;
        
        all_logs
            .into_iter()
            .filter(|log| log.timestamp >= start && log.timestamp <= end)
            .collect()
    }
    
    /// 级别过滤
    pub async fn level_filter(
        &self,
        min_level: LogLevel,
    ) -> Vec<LogRecord> {
        let all_logs = self.log_storage.get_all_logs().await;
        
        all_logs
            .into_iter()
            .filter(|log| Self::level_ge(&log.level, &min_level))
            .collect()
    }
    
    fn level_ge(level: &LogLevel, min: &LogLevel) -> bool {
        let level_order = |l: &LogLevel| match l {
            LogLevel::Trace => 0,
            LogLevel::Debug => 1,
            LogLevel::Info => 2,
            LogLevel::Warn => 3,
            LogLevel::Error => 4,
        };
        
        level_order(level) >= level_order(min)
    }
}
```

---

### 3. 聚合查询

```rust
/// 聚合查询引擎
pub struct AggregationQueryEngine {
    log_storage: Arc<LogStorage>,
}

impl AggregationQueryEngine {
    pub fn new(log_storage: Arc<LogStorage>) -> Self {
        Self { log_storage }
    }
    
    /// 按级别聚合
    pub async fn aggregate_by_level(&self) -> HashMap<LogLevel, usize> {
        let all_logs = self.log_storage.get_all_logs().await;
        
        let mut counts = HashMap::new();
        
        for log in all_logs {
            *counts.entry(log.level).or_insert(0) += 1;
        }
        
        counts
    }
    
    /// 按时间窗口聚合
    pub async fn aggregate_by_time_window(
        &self,
        window_size: chrono::Duration,
    ) -> HashMap<DateTime<Utc>, usize> {
        let all_logs = self.log_storage.get_all_logs().await;
        
        let mut counts = HashMap::new();
        
        for log in all_logs {
            let window_key = log.timestamp.timestamp() / window_size.num_seconds();
            let window_start = DateTime::from_timestamp(window_key * window_size.num_seconds(), 0).unwrap();
            
            *counts.entry(window_start).or_insert(0) += 1;
        }
        
        counts
    }
    
    /// Top N 错误消息
    pub async fn top_errors(&self, n: usize) -> Vec<(String, usize)> {
        let all_logs = self.log_storage.get_all_logs().await;
        
        let mut error_counts = HashMap::new();
        
        for log in all_logs {
            if log.level == LogLevel::Error {
                *error_counts.entry(log.message.clone()).or_insert(0) += 1;
            }
        }
        
        let mut sorted: Vec<(String, usize)> = error_counts.into_iter().collect();
        sorted.sort_by(|a, b| b.1.cmp(&a.1));
        
        sorted.into_iter().take(n).collect()
    }
}
```

---

## 📊 日志分析

### 1. 日志模式识别

```rust
/// 日志模式识别器
pub struct LogPatternRecognizer {
    patterns: Vec<LogPattern>,
}

impl LogPatternRecognizer {
    pub fn new() -> Self {
        Self {
            patterns: Vec::new(),
        }
    }
    
    /// 训练（提取常见模式）
    pub fn train(&mut self, logs: Vec<LogRecord>) {
        // 简化版：基于词频统计
        let mut pattern_counts: HashMap<String, usize> = HashMap::new();
        
        for log in logs {
            // 提取模式（移除数字和变量）
            let pattern = Self::extract_pattern(&log.message);
            *pattern_counts.entry(pattern).or_insert(0) += 1;
        }
        
        // 保留频繁模式
        self.patterns = pattern_counts
            .into_iter()
            .filter(|(_, count)| *count >= 10) // 至少出现10次
            .map(|(pattern, count)| LogPattern { pattern, count })
            .collect();
        
        // 按频率排序
        self.patterns.sort_by(|a, b| b.count.cmp(&a.count));
    }
    
    /// 提取模式（移除变量部分）
    fn extract_pattern(message: &str) -> String {
        message
            .split_whitespace()
            .map(|word| {
                if word.chars().all(|c| c.is_numeric() || c == '.') {
                    "<NUM>"
                } else if word.starts_with('"') && word.ends_with('"') {
                    "<STR>"
                } else {
                    word
                }
            })
            .collect::<Vec<&str>>()
            .join(" ")
    }
    
    /// 识别日志所属模式
    pub fn recognize(&self, log: &LogRecord) -> Option<usize> {
        let pattern = Self::extract_pattern(&log.message);
        
        self.patterns
            .iter()
            .position(|p| p.pattern == pattern)
    }
}

#[derive(Debug, Clone)]
pub struct LogPattern {
    pub pattern: String,
    pub count: usize,
}
```

---

### 2. 异常检测

```rust
/// 异常检测器
pub struct AnomalyDetector {
    normal_patterns: HashSet<String>,
    threshold: f64,
}

impl AnomalyDetector {
    pub fn new(threshold: f64) -> Self {
        Self {
            normal_patterns: HashSet::new(),
            threshold,
        }
    }
    
    /// 训练正常模式
    pub fn train(&mut self, logs: Vec<LogRecord>) {
        let mut pattern_freq: HashMap<String, usize> = HashMap::new();
        
        for log in &logs {
            let pattern = Self::extract_pattern(&log.message);
            *pattern_freq.entry(pattern).or_insert(0) += 1;
        }
        
        let total = logs.len() as f64;
        
        // 保存频率超过阈值的模式
        for (pattern, count) in pattern_freq {
            if (count as f64 / total) >= self.threshold {
                self.normal_patterns.insert(pattern);
            }
        }
    }
    
    /// 检测异常日志
    pub fn detect_anomalies(&self, logs: Vec<LogRecord>) -> Vec<LogRecord> {
        logs.into_iter()
            .filter(|log| {
                let pattern = Self::extract_pattern(&log.message);
                !self.normal_patterns.contains(&pattern)
            })
            .collect()
    }
    
    fn extract_pattern(message: &str) -> String {
        LogPatternRecognizer::extract_pattern(message)
    }
}
```

---

## ⚡ 性能优化

### 1. 查询缓存

```rust
use lru::LruCache;
use std::num::NonZeroUsize;

/// 查询缓存
pub struct QueryCache {
    cache: Arc<tokio::sync::Mutex<LruCache<String, Vec<String>>>>,
}

impl QueryCache {
    pub fn new(capacity: usize) -> Self {
        Self {
            cache: Arc::new(tokio::sync::Mutex::new(
                LruCache::new(NonZeroUsize::new(capacity).unwrap())
            )),
        }
    }
    
    /// 获取缓存
    pub async fn get(&self, query: &str) -> Option<Vec<String>> {
        let mut cache = self.cache.lock().await;
        cache.get(query).cloned()
    }
    
    /// 放入缓存
    pub async fn put(&self, query: String, results: Vec<String>) {
        let mut cache = self.cache.lock().await;
        cache.put(query, results);
    }
}
```

---

### 2. 分片搜索

```rust
/// 分片搜索引擎
pub struct ShardedSearchEngine {
    shards: Vec<Arc<InvertedIndexBuilder>>,
}

impl ShardedSearchEngine {
    pub fn new(num_shards: usize, tokenizer: Arc<Tokenizer>) -> Self {
        let shards = (0..num_shards)
            .map(|_| Arc::new(InvertedIndexBuilder::new(tokenizer.clone())))
            .collect();
        
        Self { shards }
    }
    
    /// 索引日志（自动分片）
    pub async fn index_log(&self, log: &LogRecord) {
        let shard_id = Self::get_shard_id(&log.id, self.shards.len());
        self.shards[shard_id].index_log(log).await;
    }
    
    /// 并行搜索所有分片
    pub async fn search(&self, query: &str) -> Vec<String> {
        let mut handles = Vec::new();
        
        for shard in &self.shards {
            let shard = shard.clone();
            let query = query.to_string();
            
            let handle = tokio::spawn(async move {
                shard.search(&query).await
            });
            
            handles.push(handle);
        }
        
        let mut results = Vec::new();
        
        for handle in handles {
            if let Ok(shard_results) = handle.await {
                results.extend(shard_results);
            }
        }
        
        results
    }
    
    fn get_shard_id(log_id: &str, num_shards: usize) -> usize {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        
        let mut hasher = DefaultHasher::new();
        log_id.hash(&mut hasher);
        
        (hasher.finish() as usize) % num_shards
    }
}
```

---

## 📊 完整示例：日志搜索系统

```rust
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt::init();
    
    println!("🎯 日志搜索系统启动中...\n");
    
    // 创建分词器
    let tokenizer = Arc::new(Tokenizer::new());
    
    // 创建倒排索引
    let index_builder = Arc::new(InvertedIndexBuilder::new(tokenizer.clone()));
    
    // 创建日志存储
    let log_storage = Arc::new(LogStorage::new());
    
    // 模拟日志数据
    let logs = vec![
        LogRecord {
            id: "1".to_string(),
            timestamp: Utc::now(),
            level: LogLevel::Error,
            message: "Database connection failed".to_string(),
            attributes: HashMap::new(),
        },
        LogRecord {
            id: "2".to_string(),
            timestamp: Utc::now(),
            level: LogLevel::Info,
            message: "User logged in successfully".to_string(),
            attributes: HashMap::new(),
        },
        LogRecord {
            id: "3".to_string(),
            timestamp: Utc::now(),
            level: LogLevel::Warn,
            message: "Database query slow".to_string(),
            attributes: HashMap::new(),
        },
    ];
    
    // 索引日志
    index_builder.index_logs_batch(logs.clone()).await;
    log_storage.store_logs(logs.clone()).await;
    
    println!("✅ 索引了 {} 条日志\n", logs.len());
    
    // 1. 关键词搜索
    let keyword_engine = KeywordSearchEngine::new(index_builder.clone());
    let results = keyword_engine.exact_search("database").await;
    
    println!("🔍 关键词搜索 'database': {} 条结果", results.len());
    
    // 2. 短语搜索
    let phrase_engine = PhraseSearchEngine::new(index_builder.clone());
    let results = phrase_engine.phrase_search("connection failed").await;
    
    println!("🔍 短语搜索 'connection failed': {} 条结果", results.len());
    
    // 3. 模糊搜索
    let fuzzy_engine = FuzzySearchEngine::new(index_builder.clone(), 2);
    let results = fuzzy_engine.fuzzy_search("databse").await; // 拼写错误
    
    println!("🔍 模糊搜索 'databse': {} 条结果", results.len());
    
    // 4. 聚合查询
    let aggregation_engine = AggregationQueryEngine::new(log_storage.clone());
    let level_counts = aggregation_engine.aggregate_by_level().await;
    
    println!("\n📊 按级别聚合:");
    for (level, count) in level_counts {
        println!("  {:?}: {}", level, count);
    }
    
    println!("\n✅ 搜索系统运行正常！");
    
    Ok(())
}

// 占位实现
pub struct LogStorage {
    logs: Arc<RwLock<Vec<LogRecord>>>,
}

impl LogStorage {
    pub fn new() -> Self {
        Self {
            logs: Arc::new(RwLock::new(Vec::new())),
        }
    }
    
    pub async fn store_logs(&self, logs: Vec<LogRecord>) {
        let mut storage = self.logs.write().await;
        storage.extend(logs);
    }
    
    pub async fn get_all_logs(&self) -> Vec<LogRecord> {
        let storage = self.logs.read().await;
        storage.clone()
    }
    
    pub async fn get_log(&self, log_id: &str) -> Option<LogRecord> {
        let storage = self.logs.read().await;
        storage.iter().find(|log| log.id == log_id).cloned()
    }
}
```

---

## 🎯 最佳实践

### 索引优化

1. **分片索引** - 按时间或日志量分片
2. **增量索引** - 实时索引新日志
3. **定期合并** - 合并小索引段

### 查询优化

1. **前缀过滤** - 正则查询先用前缀索引过滤
2. **并行搜索** - 多分片并行查询
3. **查询缓存** - 缓存热点查询结果

### 存储优化

1. **压缩存储** - 使用 Snappy/Zstd 压缩
2. **TTL 策略** - 定期清理旧日志
3. **冷热分离** - 热数据内存，冷数据磁盘

---

## 📚 参考资源

- [Elasticsearch](https://www.elastic.co/guide/en/elasticsearch/reference/current/index.html)
- [Lucene](https://lucene.apache.org/)
- [Tantivy](https://github.com/quickwit-oss/tantivy)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-10  
**作者**: OTLP Rust 项目组
