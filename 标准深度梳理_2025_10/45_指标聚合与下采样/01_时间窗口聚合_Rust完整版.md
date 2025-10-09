# 时间窗口聚合 - Rust 完整实现

> **文档版本**: v1.0.0  
> **Rust 版本**: 1.90+  
> **最后更新**: 2025-10-10

---

## 📋 目录

- [时间窗口聚合 - Rust 完整实现](#时间窗口聚合---rust-完整实现)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [核心功能](#核心功能)
    - [应用场景](#应用场景)
  - [⏰ 时间窗口聚合](#-时间窗口聚合)
    - [1. 固定窗口聚合](#1-固定窗口聚合)
    - [2. 滑动窗口聚合](#2-滑动窗口聚合)
    - [3. 会话窗口聚合](#3-会话窗口聚合)
  - [📊 聚合函数](#-聚合函数)
    - [1. 基础聚合函数](#1-基础聚合函数)
    - [2. 分位数聚合](#2-分位数聚合)
    - [3. Histogram 聚合](#3-histogram-聚合)
  - [🔄 流式聚合](#-流式聚合)
    - [1. 流式聚合处理器](#1-流式聚合处理器)
    - [2. 增量聚合](#2-增量聚合)
  - [💾 聚合结果存储](#-聚合结果存储)
    - [1. 聚合结果写入](#1-聚合结果写入)
    - [2. 物化视图](#2-物化视图)
  - [📈 多级聚合](#-多级聚合)
    - [1. 分层聚合器](#1-分层聚合器)
  - [📊 完整示例：Metrics 聚合系统](#-完整示例metrics-聚合系统)
  - [🎯 最佳实践](#-最佳实践)
    - [窗口选择](#窗口选择)
    - [性能优化](#性能优化)
    - [存储优化](#存储优化)
  - [📚 参考资源](#-参考资源)

---

## 🎯 概述

时间窗口聚合是 OTLP Metrics 系统的核心功能，通过对指标数据进行时间维度的聚合，可以有效减少数据量、提升查询性能，并提供不同粒度的数据视图。

### 核心功能

- ✅ **固定窗口聚合** - 按固定时间间隔聚合
- ✅ **滑动窗口聚合** - 连续的时间窗口聚合
- ✅ **会话窗口聚合** - 基于活动间隔的聚合
- ✅ **多种聚合函数** - Sum, Avg, Min, Max, Count, P95, P99
- ✅ **流式聚合** - 实时增量聚合
- ✅ **多级聚合** - 1分钟 → 1小时 → 1天

### 应用场景

- 🔧 **实时监控** - 1分钟级别的实时聚合
- 🔧 **历史分析** - 小时/天级别的历史数据
- 🔧 **存储优化** - 减少原始数据存储量
- 🔧 **查询加速** - 预聚合提升查询性能

---

## ⏰ 时间窗口聚合

### 1. 固定窗口聚合

```rust
use std::sync::Arc;
use std::collections::HashMap;
use chrono::{DateTime, Utc, Duration};
use tokio::sync::RwLock;

/// 固定窗口聚合器
pub struct FixedWindowAggregator {
    window_size: Duration,
    aggregated_data: Arc<RwLock<HashMap<(String, i64), AggregatedMetric>>>,
}

impl FixedWindowAggregator {
    pub fn new(window_size: Duration) -> Self {
        Self {
            window_size,
            aggregated_data: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    /// 聚合单个数据点
    pub async fn aggregate(
        &self,
        metric_name: String,
        timestamp: DateTime<Utc>,
        value: f64,
    ) {
        // 计算窗口键
        let window_key = self.get_window_key(timestamp);
        
        let mut data = self.aggregated_data.write().await;
        
        let aggregated = data
            .entry((metric_name.clone(), window_key))
            .or_insert_with(|| AggregatedMetric {
                metric_name: metric_name.clone(),
                window_start: self.window_key_to_timestamp(window_key),
                window_end: self.window_key_to_timestamp(window_key) + self.window_size,
                count: 0,
                sum: 0.0,
                min: f64::MAX,
                max: f64::MIN,
                values: Vec::new(),
            });
        
        // 更新聚合值
        aggregated.count += 1;
        aggregated.sum += value;
        aggregated.min = aggregated.min.min(value);
        aggregated.max = aggregated.max.max(value);
        aggregated.values.push(value);
    }
    
    /// 获取窗口键
    fn get_window_key(&self, timestamp: DateTime<Utc>) -> i64 {
        timestamp.timestamp() / self.window_size.num_seconds()
    }
    
    /// 窗口键转时间戳
    fn window_key_to_timestamp(&self, window_key: i64) -> DateTime<Utc> {
        DateTime::from_timestamp(window_key * self.window_size.num_seconds(), 0).unwrap()
    }
    
    /// 获取聚合结果
    pub async fn get_aggregated_results(&self) -> Vec<AggregatedMetric> {
        let data = self.aggregated_data.read().await;
        
        data.values()
            .map(|metric| {
                let mut result = metric.clone();
                
                // 计算平均值
                result.avg = if result.count > 0 {
                    Some(result.sum / result.count as f64)
                } else {
                    None
                };
                
                // 计算分位数
                result.calculate_percentiles();
                
                result
            })
            .collect()
    }
    
    /// 清除过期窗口
    pub async fn evict_old_windows(&self, retention: Duration) {
        let cutoff_key = self.get_window_key(Utc::now() - retention);
        
        let mut data = self.aggregated_data.write().await;
        
        data.retain(|(_, window_key), _| *window_key >= cutoff_key);
    }
}

#[derive(Debug, Clone)]
pub struct AggregatedMetric {
    pub metric_name: String,
    pub window_start: DateTime<Utc>,
    pub window_end: DateTime<Utc>,
    pub count: usize,
    pub sum: f64,
    pub min: f64,
    pub max: f64,
    pub avg: Option<f64>,
    pub values: Vec<f64>,
    pub p50: Option<f64>,
    pub p95: Option<f64>,
    pub p99: Option<f64>,
}

impl AggregatedMetric {
    /// 计算分位数
    fn calculate_percentiles(&mut self) {
        if self.values.is_empty() {
            return;
        }
        
        self.values.sort_by(|a, b| a.partial_cmp(b).unwrap());
        
        let len = self.values.len();
        
        self.p50 = Some(self.values[len / 2]);
        self.p95 = Some(self.values[len * 95 / 100]);
        self.p99 = Some(self.values[len * 99 / 100]);
    }
}
```

---

### 2. 滑动窗口聚合

```rust
/// 滑动窗口聚合器
pub struct SlidingWindowAggregator {
    window_size: Duration,
    slide_interval: Duration,
    data_points: Arc<RwLock<Vec<DataPoint>>>,
}

impl SlidingWindowAggregator {
    pub fn new(window_size: Duration, slide_interval: Duration) -> Self {
        Self {
            window_size,
            slide_interval,
            data_points: Arc::new(RwLock::new(Vec::new())),
        }
    }
    
    /// 添加数据点
    pub async fn add_data_point(
        &self,
        metric_name: String,
        timestamp: DateTime<Utc>,
        value: f64,
    ) {
        let mut points = self.data_points.write().await;
        
        points.push(DataPoint {
            metric_name,
            timestamp,
            value,
        });
        
        // 清理过期数据点
        let cutoff = Utc::now() - self.window_size;
        points.retain(|p| p.timestamp >= cutoff);
    }
    
    /// 计算滑动窗口聚合
    pub async fn compute_sliding_windows(&self) -> Vec<SlidingWindowResult> {
        let points = self.data_points.read().await;
        
        if points.is_empty() {
            return Vec::new();
        }
        
        let mut results = Vec::new();
        
        let now = Utc::now();
        let mut window_start = now - self.window_size;
        
        while window_start <= now {
            let window_end = window_start + self.window_size;
            
            // 收集窗口内的数据点
            let window_points: Vec<&DataPoint> = points
                .iter()
                .filter(|p| p.timestamp >= window_start && p.timestamp < window_end)
                .collect();
            
            if !window_points.is_empty() {
                // 按指标名称分组
                let mut metric_groups: HashMap<String, Vec<f64>> = HashMap::new();
                
                for point in window_points {
                    metric_groups
                        .entry(point.metric_name.clone())
                        .or_insert_with(Vec::new)
                        .push(point.value);
                }
                
                // 对每个指标计算聚合
                for (metric_name, values) in metric_groups {
                    let count = values.len();
                    let sum: f64 = values.iter().sum();
                    let avg = sum / count as f64;
                    
                    results.push(SlidingWindowResult {
                        metric_name,
                        window_start,
                        window_end,
                        count,
                        sum,
                        avg,
                    });
                }
            }
            
            window_start = window_start + self.slide_interval;
        }
        
        results
    }
}

#[derive(Debug, Clone)]
pub struct DataPoint {
    pub metric_name: String,
    pub timestamp: DateTime<Utc>,
    pub value: f64,
}

#[derive(Debug, Clone)]
pub struct SlidingWindowResult {
    pub metric_name: String,
    pub window_start: DateTime<Utc>,
    pub window_end: DateTime<Utc>,
    pub count: usize,
    pub sum: f64,
    pub avg: f64,
}
```

---

### 3. 会话窗口聚合

```rust
/// 会话窗口聚合器
pub struct SessionWindowAggregator {
    gap_duration: Duration,
    sessions: Arc<RwLock<HashMap<String, Session>>>,
}

impl SessionWindowAggregator {
    pub fn new(gap_duration: Duration) -> Self {
        Self {
            gap_duration,
            sessions: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    /// 处理数据点
    pub async fn process_data_point(
        &self,
        metric_name: String,
        timestamp: DateTime<Utc>,
        value: f64,
    ) {
        let mut sessions = self.sessions.write().await;
        
        let session = sessions
            .entry(metric_name.clone())
            .or_insert_with(|| Session {
                metric_name: metric_name.clone(),
                start_time: timestamp,
                last_activity: timestamp,
                values: Vec::new(),
            });
        
        // 检查是否属于当前会话
        if timestamp - session.last_activity > self.gap_duration {
            // 开始新会话
            *session = Session {
                metric_name: metric_name.clone(),
                start_time: timestamp,
                last_activity: timestamp,
                values: vec![value],
            };
        } else {
            // 继续当前会话
            session.last_activity = timestamp;
            session.values.push(value);
        }
    }
    
    /// 获取已完成的会话
    pub async fn get_completed_sessions(&self) -> Vec<SessionResult> {
        let mut sessions = self.sessions.write().await;
        
        let now = Utc::now();
        let mut completed = Vec::new();
        
        sessions.retain(|_, session| {
            if now - session.last_activity > self.gap_duration {
                // 会话已结束
                completed.push(SessionResult::from_session(session));
                false
            } else {
                true
            }
        });
        
        completed
    }
}

#[derive(Debug, Clone)]
pub struct Session {
    pub metric_name: String,
    pub start_time: DateTime<Utc>,
    pub last_activity: DateTime<Utc>,
    pub values: Vec<f64>,
}

#[derive(Debug, Clone)]
pub struct SessionResult {
    pub metric_name: String,
    pub start_time: DateTime<Utc>,
    pub end_time: DateTime<Utc>,
    pub duration: Duration,
    pub count: usize,
    pub sum: f64,
    pub avg: f64,
}

impl SessionResult {
    fn from_session(session: &Session) -> Self {
        let count = session.values.len();
        let sum: f64 = session.values.iter().sum();
        let avg = if count > 0 { sum / count as f64 } else { 0.0 };
        
        Self {
            metric_name: session.metric_name.clone(),
            start_time: session.start_time,
            end_time: session.last_activity,
            duration: session.last_activity - session.start_time,
            count,
            sum,
            avg,
        }
    }
}
```

---

## 📊 聚合函数

### 1. 基础聚合函数

```rust
/// 聚合函数集合
pub struct AggregationFunctions;

impl AggregationFunctions {
    /// Sum 聚合
    pub fn sum(values: &[f64]) -> f64 {
        values.iter().sum()
    }
    
    /// Average 聚合
    pub fn avg(values: &[f64]) -> Option<f64> {
        if values.is_empty() {
            return None;
        }
        
        Some(Self::sum(values) / values.len() as f64)
    }
    
    /// Min 聚合
    pub fn min(values: &[f64]) -> Option<f64> {
        values.iter().min_by(|a, b| a.partial_cmp(b).unwrap()).copied()
    }
    
    /// Max 聚合
    pub fn max(values: &[f64]) -> Option<f64> {
        values.iter().max_by(|a, b| a.partial_cmp(b).unwrap()).copied()
    }
    
    /// Count 聚合
    pub fn count(values: &[f64]) -> usize {
        values.len()
    }
    
    /// 标准差
    pub fn std_dev(values: &[f64]) -> Option<f64> {
        let avg = Self::avg(values)?;
        
        let variance = values
            .iter()
            .map(|v| {
                let diff = v - avg;
                diff * diff
            })
            .sum::<f64>()
            / values.len() as f64;
        
        Some(variance.sqrt())
    }
}
```

---

### 2. 分位数聚合

```rust
/// 分位数聚合器
pub struct PercentileAggregator;

impl PercentileAggregator {
    /// 计算分位数
    pub fn calculate_percentile(values: &[f64], percentile: f64) -> Option<f64> {
        if values.is_empty() {
            return None;
        }
        
        let mut sorted = values.to_vec();
        sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());
        
        let index = (sorted.len() as f64 * percentile / 100.0).ceil() as usize - 1;
        let index = index.min(sorted.len() - 1);
        
        Some(sorted[index])
    }
    
    /// 计算多个分位数
    pub fn calculate_percentiles(values: &[f64], percentiles: &[f64]) -> HashMap<String, f64> {
        let mut results = HashMap::new();
        
        for &percentile in percentiles {
            if let Some(value) = Self::calculate_percentile(values, percentile) {
                results.insert(format!("p{}", percentile as i32), value);
            }
        }
        
        results
    }
    
    /// T-Digest 近似分位数（适合大数据集）
    pub fn approximate_percentile(values: &[f64], percentile: f64) -> Option<f64> {
        // 简化实现：使用采样
        if values.is_empty() {
            return None;
        }
        
        let sample_size = 1000.min(values.len());
        let step = values.len() / sample_size;
        
        let samples: Vec<f64> = values
            .iter()
            .step_by(step)
            .copied()
            .collect();
        
        Self::calculate_percentile(&samples, percentile)
    }
}
```

---

### 3. Histogram 聚合

```rust
/// Histogram 聚合器
pub struct HistogramAggregator {
    buckets: Vec<f64>,
}

impl HistogramAggregator {
    pub fn new(buckets: Vec<f64>) -> Self {
        let mut sorted_buckets = buckets;
        sorted_buckets.sort_by(|a, b| a.partial_cmp(b).unwrap());
        
        Self { buckets: sorted_buckets }
    }
    
    /// 聚合 Histogram
    pub fn aggregate(&self, values: &[f64]) -> HistogramResult {
        let mut bucket_counts = vec![0usize; self.buckets.len()];
        
        for &value in values {
            for (i, &boundary) in self.buckets.iter().enumerate() {
                if value <= boundary {
                    bucket_counts[i] += 1;
                    break;
                }
            }
        }
        
        HistogramResult {
            buckets: self.buckets.clone(),
            counts: bucket_counts,
            total_count: values.len(),
            sum: values.iter().sum(),
        }
    }
    
    /// 合并多个 Histogram
    pub fn merge(&self, histograms: Vec<HistogramResult>) -> HistogramResult {
        if histograms.is_empty() {
            return HistogramResult {
                buckets: self.buckets.clone(),
                counts: vec![0; self.buckets.len()],
                total_count: 0,
                sum: 0.0,
            };
        }
        
        let mut merged_counts = vec![0usize; self.buckets.len()];
        let mut total_count = 0;
        let mut total_sum = 0.0;
        
        for hist in histograms {
            for (i, count) in hist.counts.iter().enumerate() {
                merged_counts[i] += count;
            }
            
            total_count += hist.total_count;
            total_sum += hist.sum;
        }
        
        HistogramResult {
            buckets: self.buckets.clone(),
            counts: merged_counts,
            total_count,
            sum: total_sum,
        }
    }
}

#[derive(Debug, Clone)]
pub struct HistogramResult {
    pub buckets: Vec<f64>,
    pub counts: Vec<usize>,
    pub total_count: usize,
    pub sum: f64,
}
```

---

## 🔄 流式聚合

### 1. 流式聚合处理器

```rust
use futures::stream::{Stream, StreamExt};
use std::pin::Pin;

/// 流式聚合处理器
pub struct StreamingAggregationProcessor {
    aggregator: Arc<FixedWindowAggregator>,
}

impl StreamingAggregationProcessor {
    pub fn new(aggregator: Arc<FixedWindowAggregator>) -> Self {
        Self { aggregator }
    }
    
    /// 处理数据流
    pub async fn process_stream(
        &self,
        mut stream: Pin<Box<dyn Stream<Item = DataPoint> + Send>>,
    ) {
        while let Some(point) = stream.next().await {
            self.aggregator
                .aggregate(
                    point.metric_name,
                    point.timestamp,
                    point.value,
                )
                .await;
        }
    }
    
    /// 定期输出聚合结果
    pub async fn emit_aggregated_results(
        &self,
        interval: std::time::Duration,
    ) {
        let mut interval_timer = tokio::time::interval(interval);
        
        loop {
            interval_timer.tick().await;
            
            let results = self.aggregator.get_aggregated_results().await;
            
            tracing::info!("Emitting {} aggregated metrics", results.len());
            
            // 这里可以将结果写入存储或发送到下游
            self.emit_results(results).await;
        }
    }
    
    async fn emit_results(&self, results: Vec<AggregatedMetric>) {
        // 实现结果输出逻辑
        for result in results {
            tracing::debug!(
                "Metric: {}, Window: {} - {}, Count: {}, Avg: {:?}",
                result.metric_name,
                result.window_start,
                result.window_end,
                result.count,
                result.avg
            );
        }
    }
}
```

---

### 2. 增量聚合

```rust
/// 增量聚合器（空间高效）
pub struct IncrementalAggregator {
    state: Arc<RwLock<HashMap<String, IncrementalState>>>,
}

impl IncrementalAggregator {
    pub fn new() -> Self {
        Self {
            state: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    /// 增量更新
    pub async fn update(&self, metric_name: String, value: f64) {
        let mut state_map = self.state.write().await;
        
        let state = state_map
            .entry(metric_name)
            .or_insert_with(IncrementalState::new);
        
        state.update(value);
    }
    
    /// 获取聚合结果
    pub async fn get_result(&self, metric_name: &str) -> Option<IncrementalResult> {
        let state_map = self.state.read().await;
        
        state_map
            .get(metric_name)
            .map(|state| state.to_result(metric_name))
    }
    
    /// 重置状态
    pub async fn reset(&self, metric_name: &str) {
        let mut state_map = self.state.write().await;
        state_map.remove(metric_name);
    }
}

#[derive(Debug, Clone)]
pub struct IncrementalState {
    count: usize,
    sum: f64,
    sum_of_squares: f64,
    min: f64,
    max: f64,
}

impl IncrementalState {
    fn new() -> Self {
        Self {
            count: 0,
            sum: 0.0,
            sum_of_squares: 0.0,
            min: f64::MAX,
            max: f64::MIN,
        }
    }
    
    fn update(&mut self, value: f64) {
        self.count += 1;
        self.sum += value;
        self.sum_of_squares += value * value;
        self.min = self.min.min(value);
        self.max = self.max.max(value);
    }
    
    fn to_result(&self, metric_name: &str) -> IncrementalResult {
        let avg = if self.count > 0 {
            self.sum / self.count as f64
        } else {
            0.0
        };
        
        let variance = if self.count > 0 {
            (self.sum_of_squares / self.count as f64) - (avg * avg)
        } else {
            0.0
        };
        
        IncrementalResult {
            metric_name: metric_name.to_string(),
            count: self.count,
            sum: self.sum,
            avg,
            min: self.min,
            max: self.max,
            std_dev: variance.sqrt(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct IncrementalResult {
    pub metric_name: String,
    pub count: usize,
    pub sum: f64,
    pub avg: f64,
    pub min: f64,
    pub max: f64,
    pub std_dev: f64,
}
```

---

## 💾 聚合结果存储

### 1. 聚合结果写入

```rust
/// 聚合结果存储器
pub struct AggregationStorage {
    timescaledb: Arc<TimescaleDbClient>,
}

impl AggregationStorage {
    pub fn new(timescaledb: Arc<TimescaleDbClient>) -> Self {
        Self { timescaledb }
    }
    
    /// 写入聚合结果
    pub async fn write_aggregated_metrics(
        &self,
        metrics: Vec<AggregatedMetric>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        for metric in metrics {
            self.timescaledb
                .execute(
                    "INSERT INTO aggregated_metrics (time, metric_name, count, sum, avg, min, max, p50, p95, p99)
                     VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10)
                     ON CONFLICT (time, metric_name) DO UPDATE SET
                         count = EXCLUDED.count,
                         sum = EXCLUDED.sum,
                         avg = EXCLUDED.avg,
                         min = EXCLUDED.min,
                         max = EXCLUDED.max,
                         p50 = EXCLUDED.p50,
                         p95 = EXCLUDED.p95,
                         p99 = EXCLUDED.p99",
                    &[
                        &metric.window_start,
                        &metric.metric_name,
                        &(metric.count as i64),
                        &metric.sum,
                        &metric.avg.unwrap_or(0.0),
                        &metric.min,
                        &metric.max,
                        &metric.p50.unwrap_or(0.0),
                        &metric.p95.unwrap_or(0.0),
                        &metric.p99.unwrap_or(0.0),
                    ],
                )
                .await?;
        }
        
        Ok(())
    }
}
```

---

### 2. 物化视图

```rust
/// 物化视图管理器
pub struct MaterializedViewManager {
    timescaledb: Arc<TimescaleDbClient>,
}

impl MaterializedViewManager {
    pub fn new(timescaledb: Arc<TimescaleDbClient>) -> Self {
        Self { timescaledb }
    }
    
    /// 创建连续聚合视图
    pub async fn create_continuous_aggregate(
        &self,
        view_name: &str,
        source_table: &str,
        window_size: &str,
    ) -> Result<(), Box<dyn std::error::Error>> {
        self.timescaledb
            .execute(
                &format!(
                    "CREATE MATERIALIZED VIEW {} WITH (timescaledb.continuous) AS
                     SELECT time_bucket('{}', time) AS bucket,
                            metric_name,
                            COUNT(*) as count,
                            SUM(value) as sum,
                            AVG(value) as avg,
                            MIN(value) as min,
                            MAX(value) as max
                     FROM {}
                     GROUP BY bucket, metric_name",
                    view_name, window_size, source_table
                ),
                &[],
            )
            .await?;
        
        // 设置刷新策略
        self.timescaledb
            .execute(
                &format!(
                    "SELECT add_continuous_aggregate_policy('{}',
                        start_offset => INTERVAL '1 month',
                        end_offset => INTERVAL '1 minute',
                        schedule_interval => INTERVAL '1 minute')",
                    view_name
                ),
                &[],
            )
            .await?;
        
        Ok(())
    }
}

// 占位实现
pub struct TimescaleDbClient {}
impl TimescaleDbClient {
    pub async fn execute(&self, _query: &str, _params: &[&dyn std::any::Any]) -> Result<(), Box<dyn std::error::Error>> {
        Ok(())
    }
}
```

---

## 📈 多级聚合

### 1. 分层聚合器

```rust
/// 分层聚合器（1分钟 → 1小时 → 1天）
pub struct HierarchicalAggregator {
    minute_aggregator: Arc<FixedWindowAggregator>,
    hour_aggregator: Arc<FixedWindowAggregator>,
    day_aggregator: Arc<FixedWindowAggregator>,
}

impl HierarchicalAggregator {
    pub fn new() -> Self {
        Self {
            minute_aggregator: Arc::new(FixedWindowAggregator::new(Duration::minutes(1))),
            hour_aggregator: Arc::new(FixedWindowAggregator::new(Duration::hours(1))),
            day_aggregator: Arc::new(FixedWindowAggregator::new(Duration::days(1))),
        }
    }
    
    /// 处理原始数据点
    pub async fn process(&self, metric_name: String, timestamp: DateTime<Utc>, value: f64) {
        // 写入1分钟聚合
        self.minute_aggregator
            .aggregate(metric_name.clone(), timestamp, value)
            .await;
    }
    
    /// 从分钟聚合Rollup到小时聚合
    pub async fn rollup_to_hour(&self) -> Result<(), Box<dyn std::error::Error>> {
        let minute_results = self.minute_aggregator.get_aggregated_results().await;
        
        for result in minute_results {
            // 将分钟级数据的sum重新聚合到小时级
            self.hour_aggregator
                .aggregate(
                    result.metric_name,
                    result.window_start,
                    result.sum,
                )
                .await;
        }
        
        Ok(())
    }
    
    /// 从小时聚合Rollup到天聚合
    pub async fn rollup_to_day(&self) -> Result<(), Box<dyn std::error::Error>> {
        let hour_results = self.hour_aggregator.get_aggregated_results().await;
        
        for result in hour_results {
            self.day_aggregator
                .aggregate(
                    result.metric_name,
                    result.window_start,
                    result.sum,
                )
                .await;
        }
        
        Ok(())
    }
    
    /// 启动定期Rollup任务
    pub async fn start_rollup_tasks(&self) {
        // 每小时Rollup一次
        let hour_aggregator = self.hour_aggregator.clone();
        let minute_aggregator = self.minute_aggregator.clone();
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(std::time::Duration::from_secs(3600));
            
            loop {
                interval.tick().await;
                
                let minute_results = minute_aggregator.get_aggregated_results().await;
                
                for result in minute_results {
                    hour_aggregator
                        .aggregate(result.metric_name, result.window_start, result.sum)
                        .await;
                }
            }
        });
        
        // 每天Rollup一次
        let day_aggregator = self.day_aggregator.clone();
        let hour_aggregator = self.hour_aggregator.clone();
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(std::time::Duration::from_secs(86400));
            
            loop {
                interval.tick().await;
                
                let hour_results = hour_aggregator.get_aggregated_results().await;
                
                for result in hour_results {
                    day_aggregator
                        .aggregate(result.metric_name, result.window_start, result.sum)
                        .await;
                }
            }
        });
    }
}
```

---

## 📊 完整示例：Metrics 聚合系统

```rust
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt::init();
    
    println!("🎯 Metrics 聚合系统启动中...\n");
    
    // 创建分层聚合器
    let hierarchical_aggregator = Arc::new(HierarchicalAggregator::new());
    
    // 启动Rollup任务
    hierarchical_aggregator.start_rollup_tasks().await;
    
    println!("✅ Rollup 任务已启动\n");
    
    // 模拟数据点
    let metric_name = "http_requests_total".to_string();
    
    for i in 0..1000 {
        let timestamp = Utc::now();
        let value = 100.0 + (i as f64 % 50.0);
        
        hierarchical_aggregator
            .process(metric_name.clone(), timestamp, value)
            .await;
        
        tokio::time::sleep(std::time::Duration::from_millis(10)).await;
    }
    
    println!("📊 处理了 1000 个数据点\n");
    
    // 获取聚合结果
    let minute_results = hierarchical_aggregator
        .minute_aggregator
        .get_aggregated_results()
        .await;
    
    println!("📈 1分钟级聚合结果:");
    
    for result in minute_results.iter().take(5) {
        println!(
            "  {} | 窗口: {} - {} | 计数: {} | 平均: {:.2}",
            result.metric_name,
            result.window_start.format("%H:%M:%S"),
            result.window_end.format("%H:%M:%S"),
            result.count,
            result.avg.unwrap_or(0.0)
        );
    }
    
    println!("\n✅ 聚合系统运行正常！");
    
    Ok(())
}
```

---

## 🎯 最佳实践

### 窗口选择

1. **实时监控** - 1分钟固定窗口
2. **短期分析** - 5分钟或15分钟窗口
3. **长期存储** - 1小时或1天窗口

### 性能优化

1. **增量聚合** - 避免全量重新计算
2. **并行处理** - 多个窗口并行聚合
3. **延迟计算** - 懒计算分位数等昂贵操作

### 存储优化

1. **多级Rollup** - 1分钟 → 1小时 → 1天
2. **TTL策略** - 原始数据7天，聚合数据90天
3. **压缩** - 使用时序数据库的原生压缩

---

## 📚 参考资源

- [Apache Flink Windowing](https://nightlies.apache.org/flink/flink-docs-master/docs/dev/datastream/operators/windows/)
- [TimescaleDB Continuous Aggregates](https://docs.timescale.com/timescaledb/latest/how-to-guides/continuous-aggregates/)
- [Prometheus Downsampling](https://prometheus.io/docs/prometheus/latest/querying/basics/)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-10  
**作者**: OTLP Rust 项目组
