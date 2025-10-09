# 时序数据库集成 - Rust 完整实现

> **文档版本**: v1.0.0  
> **Rust 版本**: 1.90+  
> **最后更新**: 2025-10-10

---

## 📋 目录

- [时序数据库集成 - Rust 完整实现](#时序数据库集成---rust-完整实现)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [支持的时序数据库](#支持的时序数据库)
    - [核心特性](#核心特性)
  - [🔧 InfluxDB 集成](#-influxdb-集成)
    - [1. InfluxDB 客户端封装](#1-influxdb-客户端封装)
    - [2. OTLP 到 InfluxDB 转换器](#2-otlp-到-influxdb-转换器)
  - [📊 TimescaleDB 集成](#-timescaledb-集成)
    - [1. TimescaleDB 客户端](#1-timescaledb-客户端)
    - [2. Hypertable 管理](#2-hypertable-管理)
  - [⚡ Prometheus 集成](#-prometheus-集成)
    - [1. Prometheus 远程写入](#1-prometheus-远程写入)
  - [🔍 VictoriaMetrics 集成](#-victoriametrics-集成)
    - [1. VictoriaMetrics 客户端](#1-victoriametrics-客户端)
  - [💾 列式存储引擎](#-列式存储引擎)
    - [1. Apache Parquet 集成](#1-apache-parquet-集成)
    - [2. 列式数据写入器](#2-列式数据写入器)
  - [🗜️ 数据压缩](#️-数据压缩)
    - [1. 时序压缩算法](#1-时序压缩算法)
    - [2. Gorilla 压缩](#2-gorilla-压缩)
    - [3. Delta-of-Delta 编码](#3-delta-of-delta-编码)
  - [📈 数据保留策略](#-数据保留策略)
    - [1. TTL 管理器](#1-ttl-管理器)
    - [2. 数据降采样](#2-数据降采样)
  - [🔄 统一存储抽象](#-统一存储抽象)
    - [1. 存储后端 Trait](#1-存储后端-trait)
  - [📊 完整示例：多后端存储系统](#-完整示例多后端存储系统)
  - [🎯 最佳实践](#-最佳实践)
    - [数据建模](#数据建模)
    - [写入优化](#写入优化)
    - [查询优化](#查询优化)
  - [📚 参考资源](#-参考资源)

---

## 🎯 概述

OTLP 数据本质上是时序数据，选择合适的时序数据库对系统性能至关重要。
本文档介绍如何集成主流时序数据库并实现高效的数据压缩。

### 支持的时序数据库

- ✅ **InfluxDB**: 专业时序数据库
- ✅ **TimescaleDB**: PostgreSQL 扩展
- ✅ **Prometheus**: 监控系统
- ✅ **VictoriaMetrics**: 高性能时序数据库
- ✅ **ClickHouse**: 列式 OLAP 数据库
- ✅ **Apache Parquet**: 列式文件格式

### 核心特性

- 🔧 **统一接口**: 抽象不同数据库的差异
- ⚡ **批量写入**: 提升写入性能
- 🗜️ **智能压缩**: 减少存储成本
- 📊 **自动降采样**: 长期数据归档
- 🔍 **高效查询**: 时间范围查询优化

---

## 🔧 InfluxDB 集成

### 1. InfluxDB 客户端封装

```rust
use serde::{Serialize, Deserialize};
use reqwest::Client;
use std::collections::HashMap;
use chrono::{DateTime, Utc};

/// InfluxDB 客户端
pub struct InfluxDbClient {
    base_url: String,
    token: String,
    org: String,
    bucket: String,
    http_client: Client,
}

impl InfluxDbClient {
    pub fn new(base_url: String, token: String, org: String, bucket: String) -> Self {
        Self {
            base_url,
            token,
            org,
            bucket,
            http_client: Client::new(),
        }
    }
    
    /// 写入数据点
    pub async fn write_points(&self, points: Vec<InfluxPoint>) -> Result<(), Box<dyn std::error::Error>> {
        let line_protocol = self.to_line_protocol(&points);
        
        let url = format!("{}/api/v2/write?org={}&bucket={}", 
            self.base_url, self.org, self.bucket);
        
        let response = self.http_client
            .post(&url)
            .header("Authorization", format!("Token {}", self.token))
            .header("Content-Type", "text/plain; charset=utf-8")
            .body(line_protocol)
            .send()
            .await?;
        
        if !response.status().is_success() {
            let error_text = response.text().await?;
            return Err(format!("InfluxDB write failed: {}", error_text).into());
        }
        
        Ok(())
    }
    
    /// 批量写入
    pub async fn write_batch(&self, points: Vec<InfluxPoint>, batch_size: usize) -> Result<(), Box<dyn std::error::Error>> {
        for chunk in points.chunks(batch_size) {
            self.write_points(chunk.to_vec()).await?;
        }
        
        Ok(())
    }
    
    /// 转换为 Line Protocol
    fn to_line_protocol(&self, points: &[InfluxPoint]) -> String {
        points
            .iter()
            .map(|p| p.to_line_protocol())
            .collect::<Vec<_>>()
            .join("\n")
    }
    
    /// 查询数据
    pub async fn query(&self, flux_query: &str) -> Result<Vec<HashMap<String, serde_json::Value>>, Box<dyn std::error::Error>> {
        let url = format!("{}/api/v2/query?org={}", self.base_url, self.org);
        
        let request_body = serde_json::json!({
            "query": flux_query,
            "type": "flux"
        });
        
        let response = self.http_client
            .post(&url)
            .header("Authorization", format!("Token {}", self.token))
            .header("Content-Type", "application/json")
            .json(&request_body)
            .send()
            .await?;
        
        let csv_text = response.text().await?;
        let results = self.parse_csv_result(&csv_text)?;
        
        Ok(results)
    }
    
    fn parse_csv_result(&self, csv: &str) -> Result<Vec<HashMap<String, serde_json::Value>>, Box<dyn std::error::Error>> {
        // 简化实现：解析 CSV 格式的查询结果
        let mut results = Vec::new();
        
        let lines: Vec<&str> = csv.lines().collect();
        if lines.len() < 2 {
            return Ok(results);
        }
        
        // 第一行是表头
        let headers: Vec<&str> = lines[0].split(',').collect();
        
        // 解析数据行
        for line in lines.iter().skip(1) {
            let values: Vec<&str> = line.split(',').collect();
            
            if values.len() == headers.len() {
                let mut row = HashMap::new();
                
                for (header, value) in headers.iter().zip(values.iter()) {
                    row.insert(header.to_string(), serde_json::Value::String(value.to_string()));
                }
                
                results.push(row);
            }
        }
        
        Ok(results)
    }
}

/// InfluxDB 数据点
#[derive(Debug, Clone)]
pub struct InfluxPoint {
    pub measurement: String,
    pub tags: HashMap<String, String>,
    pub fields: HashMap<String, InfluxValue>,
    pub timestamp: Option<DateTime<Utc>>,
}

#[derive(Debug, Clone)]
pub enum InfluxValue {
    Float(f64),
    Integer(i64),
    String(String),
    Boolean(bool),
}

impl InfluxPoint {
    /// 转换为 Line Protocol
    pub fn to_line_protocol(&self) -> String {
        let mut result = self.measurement.clone();
        
        // 添加标签
        if !self.tags.is_empty() {
            result.push(',');
            let tags: Vec<String> = self.tags
                .iter()
                .map(|(k, v)| format!("{}={}", Self::escape_key(k), Self::escape_tag_value(v)))
                .collect();
            result.push_str(&tags.join(","));
        }
        
        // 添加字段
        result.push(' ');
        let fields: Vec<String> = self.fields
            .iter()
            .map(|(k, v)| format!("{}={}", Self::escape_key(k), v.to_string()))
            .collect();
        result.push_str(&fields.join(","));
        
        // 添加时间戳
        if let Some(ts) = self.timestamp {
            result.push(' ');
            result.push_str(&ts.timestamp_nanos_opt().unwrap_or(0).to_string());
        }
        
        result
    }
    
    fn escape_key(s: &str) -> String {
        s.replace(',', "\\,")
            .replace('=', "\\=")
            .replace(' ', "\\ ")
    }
    
    fn escape_tag_value(s: &str) -> String {
        s.replace(',', "\\,")
            .replace('=', "\\=")
            .replace(' ', "\\ ")
    }
}

impl InfluxValue {
    fn to_string(&self) -> String {
        match self {
            Self::Float(f) => f.to_string(),
            Self::Integer(i) => format!("{}i", i),
            Self::String(s) => format!("\"{}\"", s.replace('"', "\\\"")),
            Self::Boolean(b) => b.to_string(),
        }
    }
}
```

---

### 2. OTLP 到 InfluxDB 转换器

```rust
/// OTLP Metric 到 InfluxDB 转换器
pub struct OtlpToInfluxConverter {
    // 配置
}

impl OtlpToInfluxConverter {
    pub fn new() -> Self {
        Self {}
    }
    
    /// 转换 Metric 到 InfluxDB 数据点
    pub fn convert_metric(&self, metric: &crate::DistributedMetric) -> Vec<InfluxPoint> {
        let mut points = Vec::new();
        
        for data_point in &metric.data_points {
            let mut tags = HashMap::new();
            tags.insert("service_name".to_string(), metric.resource.service_name.clone());
            
            if let Some(ns) = &metric.resource.service_namespace {
                tags.insert("service_namespace".to_string(), ns.clone());
            }
            
            // 添加数据点的属性作为标签
            for (k, v) in &data_point.attributes {
                tags.insert(k.clone(), v.clone());
            }
            
            let mut fields = HashMap::new();
            
            match &data_point.value {
                crate::MetricValue::Int(i) => {
                    fields.insert("value".to_string(), InfluxValue::Integer(*i));
                }
                crate::MetricValue::Double(d) => {
                    fields.insert("value".to_string(), InfluxValue::Float(*d));
                }
                crate::MetricValue::Histogram { count, sum, buckets } => {
                    fields.insert("count".to_string(), InfluxValue::Integer(*count as i64));
                    fields.insert("sum".to_string(), InfluxValue::Float(*sum));
                    
                    // 为每个桶创建单独的字段
                    for (i, bucket) in buckets.iter().enumerate() {
                        fields.insert(
                            format!("bucket_{}", i),
                            InfluxValue::Integer(bucket.count as i64)
                        );
                    }
                }
                _ => {
                    // 其他类型...
                }
            }
            
            points.push(InfluxPoint {
                measurement: metric.name.clone(),
                tags,
                fields,
                timestamp: Some(data_point.timestamp),
            });
        }
        
        points
    }
    
    /// 转换 Trace 到 InfluxDB 数据点（用于追踪统计）
    pub fn convert_trace_stats(&self, trace: &crate::DistributedTrace) -> Vec<InfluxPoint> {
        let mut points = Vec::new();
        
        for span in &trace.spans {
            let mut tags = HashMap::new();
            tags.insert("service_name".to_string(), trace.resource.service_name.clone());
            tags.insert("span_name".to_string(), span.name.clone());
            
            let duration_ms = (span.end_time - span.start_time).num_milliseconds();
            
            let mut fields = HashMap::new();
            fields.insert("duration_ms".to_string(), InfluxValue::Integer(duration_ms));
            
            points.push(InfluxPoint {
                measurement: "span_duration".to_string(),
                tags,
                fields,
                timestamp: Some(span.start_time),
            });
        }
        
        points
    }
}
```

---

## 📊 TimescaleDB 集成

### 1. TimescaleDB 客户端

```rust
use tokio_postgres::{Client, NoTls, Error};

/// TimescaleDB 客户端
pub struct TimescaleDbClient {
    client: Client,
}

impl TimescaleDbClient {
    /// 连接 TimescaleDB
    pub async fn connect(connection_string: &str) -> Result<Self, Error> {
        let (client, connection) = tokio_postgres::connect(connection_string, NoTls).await?;
        
        // 在后台处理连接
        tokio::spawn(async move {
            if let Err(e) = connection.await {
                eprintln!("TimescaleDB connection error: {}", e);
            }
        });
        
        Ok(Self { client })
    }
    
    /// 初始化表结构
    pub async fn initialize_schema(&self) -> Result<(), Error> {
        // 创建 Metrics 表
        self.client.execute(
            "CREATE TABLE IF NOT EXISTS metrics (
                time TIMESTAMPTZ NOT NULL,
                metric_name TEXT NOT NULL,
                service_name TEXT NOT NULL,
                service_namespace TEXT,
                value DOUBLE PRECISION,
                tags JSONB,
                PRIMARY KEY (time, metric_name, service_name)
            )",
            &[],
        ).await?;
        
        // 创建 Hypertable
        self.client.execute(
            "SELECT create_hypertable('metrics', 'time', if_not_exists => TRUE)",
            &[],
        ).await?;
        
        // 创建索引
        self.client.execute(
            "CREATE INDEX IF NOT EXISTS idx_metrics_service ON metrics (service_name, time DESC)",
            &[],
        ).await?;
        
        self.client.execute(
            "CREATE INDEX IF NOT EXISTS idx_metrics_tags ON metrics USING GIN (tags)",
            &[],
        ).await?;
        
        tracing::info!("TimescaleDB schema initialized");
        
        Ok(())
    }
    
    /// 插入 Metric 数据
    pub async fn insert_metric(
        &self,
        timestamp: DateTime<Utc>,
        metric_name: &str,
        service_name: &str,
        service_namespace: Option<&str>,
        value: f64,
        tags: &HashMap<String, String>,
    ) -> Result<(), Error> {
        let tags_json = serde_json::to_value(tags).unwrap();
        
        self.client.execute(
            "INSERT INTO metrics (time, metric_name, service_name, service_namespace, value, tags)
             VALUES ($1, $2, $3, $4, $5, $6)",
            &[&timestamp, &metric_name, &service_name, &service_namespace, &value, &tags_json],
        ).await?;
        
        Ok(())
    }
    
    /// 批量插入
    pub async fn insert_batch(&self, points: Vec<TimescalePoint>) -> Result<(), Error> {
        let mut transaction = self.client.transaction().await?;
        
        let statement = transaction.prepare(
            "INSERT INTO metrics (time, metric_name, service_name, service_namespace, value, tags)
             VALUES ($1, $2, $3, $4, $5, $6)"
        ).await?;
        
        for point in points {
            let tags_json = serde_json::to_value(&point.tags).unwrap();
            
            transaction.execute(
                &statement,
                &[
                    &point.timestamp,
                    &point.metric_name,
                    &point.service_name,
                    &point.service_namespace,
                    &point.value,
                    &tags_json,
                ],
            ).await?;
        }
        
        transaction.commit().await?;
        
        Ok(())
    }
    
    /// 查询时间范围内的数据
    pub async fn query_range(
        &self,
        metric_name: &str,
        service_name: &str,
        start: DateTime<Utc>,
        end: DateTime<Utc>,
    ) -> Result<Vec<TimescalePoint>, Error> {
        let rows = self.client.query(
            "SELECT time, metric_name, service_name, service_namespace, value, tags
             FROM metrics
             WHERE metric_name = $1 AND service_name = $2 AND time >= $3 AND time <= $4
             ORDER BY time ASC",
            &[&metric_name, &service_name, &start, &end],
        ).await?;
        
        let mut results = Vec::new();
        
        for row in rows {
            let tags_json: serde_json::Value = row.get(5);
            let tags: HashMap<String, String> = serde_json::from_value(tags_json).unwrap_or_default();
            
            results.push(TimescalePoint {
                timestamp: row.get(0),
                metric_name: row.get(1),
                service_name: row.get(2),
                service_namespace: row.get(3),
                value: row.get(4),
                tags,
            });
        }
        
        Ok(results)
    }
}

#[derive(Debug, Clone)]
pub struct TimescalePoint {
    pub timestamp: DateTime<Utc>,
    pub metric_name: String,
    pub service_name: String,
    pub service_namespace: Option<String>,
    pub value: f64,
    pub tags: HashMap<String, String>,
}
```

---

### 2. Hypertable 管理

```rust
/// Hypertable 管理器
pub struct HypertableManager {
    client: TimescaleDbClient,
}

impl HypertableManager {
    pub fn new(client: TimescaleDbClient) -> Self {
        Self { client }
    }
    
    /// 设置数据保留策略
    pub async fn set_retention_policy(
        &self,
        table_name: &str,
        retention_days: i32,
    ) -> Result<(), Error> {
        self.client.client.execute(
            &format!(
                "SELECT add_retention_policy('{}', INTERVAL '{} days', if_not_exists => TRUE)",
                table_name, retention_days
            ),
            &[],
        ).await?;
        
        tracing::info!("Set retention policy: {} days for table {}", retention_days, table_name);
        
        Ok(())
    }
    
    /// 设置压缩策略
    pub async fn set_compression_policy(
        &self,
        table_name: &str,
        compress_after_days: i32,
    ) -> Result<(), Error> {
        // 启用压缩
        self.client.client.execute(
            &format!(
                "ALTER TABLE {} SET (timescaledb.compress, timescaledb.compress_segmentby = 'service_name')",
                table_name
            ),
            &[],
        ).await?;
        
        // 设置压缩策略
        self.client.client.execute(
            &format!(
                "SELECT add_compression_policy('{}', INTERVAL '{} days', if_not_exists => TRUE)",
                table_name, compress_after_days
            ),
            &[],
        ).await?;
        
        tracing::info!("Set compression policy: {} days for table {}", compress_after_days, table_name);
        
        Ok(())
    }
    
    /// 创建连续聚合（Continuous Aggregate）
    pub async fn create_continuous_aggregate(
        &self,
        aggregate_name: &str,
        source_table: &str,
        bucket_width: &str, // e.g., "1 hour"
    ) -> Result<(), Error> {
        self.client.client.execute(
            &format!(
                "CREATE MATERIALIZED VIEW {} WITH (timescaledb.continuous) AS
                 SELECT time_bucket('{}', time) AS bucket,
                        metric_name,
                        service_name,
                        AVG(value) as avg_value,
                        MAX(value) as max_value,
                        MIN(value) as min_value,
                        COUNT(*) as count
                 FROM {}
                 GROUP BY bucket, metric_name, service_name",
                aggregate_name, bucket_width, source_table
            ),
            &[],
        ).await?;
        
        // 设置刷新策略
        self.client.client.execute(
            &format!(
                "SELECT add_continuous_aggregate_policy('{}',
                    start_offset => INTERVAL '1 month',
                    end_offset => INTERVAL '1 hour',
                    schedule_interval => INTERVAL '1 hour')",
                aggregate_name
            ),
            &[],
        ).await?;
        
        tracing::info!("Created continuous aggregate: {}", aggregate_name);
        
        Ok(())
    }
}
```

---

## ⚡ Prometheus 集成

### 1. Prometheus 远程写入

```rust
use prost::Message;

/// Prometheus 远程写入客户端
pub struct PrometheusRemoteWriteClient {
    remote_write_url: String,
    http_client: Client,
}

impl PrometheusRemoteWriteClient {
    pub fn new(remote_write_url: String) -> Self {
        Self {
            remote_write_url,
            http_client: Client::new(),
        }
    }
    
    /// 写入时间序列
    pub async fn write_timeseries(
        &self,
        timeseries: Vec<PrometheusTimeSeries>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        // 构建 Prometheus Remote Write 请求
        let write_request = prometheus::WriteRequest {
            timeseries: timeseries.into_iter().map(|ts| ts.into()).collect(),
            metadata: vec![],
        };
        
        // 序列化为 Protobuf
        let mut buf = Vec::new();
        write_request.encode(&mut buf)?;
        
        // Snappy 压缩
        let compressed = snap::raw::Encoder::new().compress_vec(&buf)?;
        
        // 发送请求
        let response = self.http_client
            .post(&self.remote_write_url)
            .header("Content-Encoding", "snappy")
            .header("Content-Type", "application/x-protobuf")
            .header("X-Prometheus-Remote-Write-Version", "0.1.0")
            .body(compressed)
            .send()
            .await?;
        
        if !response.status().is_success() {
            let error_text = response.text().await?;
            return Err(format!("Prometheus write failed: {}", error_text).into());
        }
        
        Ok(())
    }
}

/// Prometheus 时间序列
#[derive(Debug, Clone)]
pub struct PrometheusTimeSeries {
    pub labels: Vec<(String, String)>,
    pub samples: Vec<PrometheusSample>,
}

#[derive(Debug, Clone)]
pub struct PrometheusSample {
    pub timestamp_ms: i64,
    pub value: f64,
}

// Protobuf 定义（简化）
mod prometheus {
    use prost::Message;
    
    #[derive(Clone, PartialEq, Message)]
    pub struct WriteRequest {
        #[prost(message, repeated, tag = "1")]
        pub timeseries: Vec<TimeSeries>,
        
        #[prost(message, repeated, tag = "3")]
        pub metadata: Vec<MetricMetadata>,
    }
    
    #[derive(Clone, PartialEq, Message)]
    pub struct TimeSeries {
        #[prost(message, repeated, tag = "1")]
        pub labels: Vec<Label>,
        
        #[prost(message, repeated, tag = "2")]
        pub samples: Vec<Sample>,
    }
    
    #[derive(Clone, PartialEq, Message)]
    pub struct Label {
        #[prost(string, tag = "1")]
        pub name: String,
        
        #[prost(string, tag = "2")]
        pub value: String,
    }
    
    #[derive(Clone, PartialEq, Message)]
    pub struct Sample {
        #[prost(double, tag = "1")]
        pub value: f64,
        
        #[prost(int64, tag = "2")]
        pub timestamp: i64,
    }
    
    #[derive(Clone, PartialEq, Message)]
    pub struct MetricMetadata {
        #[prost(enumeration = "MetricType", tag = "1")]
        pub r#type: i32,
        
        #[prost(string, tag = "2")]
        pub metric_family_name: String,
    }
    
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
    #[repr(i32)]
    pub enum MetricType {
        Counter = 0,
        Gauge = 1,
        Histogram = 2,
        Summary = 4,
    }
}

impl From<PrometheusTimeSeries> for prometheus::TimeSeries {
    fn from(ts: PrometheusTimeSeries) -> Self {
        prometheus::TimeSeries {
            labels: ts.labels
                .into_iter()
                .map(|(name, value)| prometheus::Label { name, value })
                .collect(),
            samples: ts.samples
                .into_iter()
                .map(|s| prometheus::Sample {
                    value: s.value,
                    timestamp: s.timestamp_ms,
                })
                .collect(),
        }
    }
}
```

---

## 🔍 VictoriaMetrics 集成

### 1. VictoriaMetrics 客户端

```rust
/// VictoriaMetrics 客户端（兼容 Prometheus API）
pub struct VictoriaMetricsClient {
    base_url: String,
    http_client: Client,
}

impl VictoriaMetricsClient {
    pub fn new(base_url: String) -> Self {
        Self {
            base_url,
            http_client: Client::new(),
        }
    }
    
    /// 写入数据（使用 Prometheus Remote Write 协议）
    pub async fn write(&self, timeseries: Vec<PrometheusTimeSeries>) -> Result<(), Box<dyn std::error::Error>> {
        let prometheus_client = PrometheusRemoteWriteClient::new(
            format!("{}/api/v1/write", self.base_url)
        );
        
        prometheus_client.write_timeseries(timeseries).await
    }
    
    /// 使用 InfluxDB Line Protocol 写入
    pub async fn write_influx_line_protocol(&self, lines: Vec<String>) -> Result<(), Box<dyn std::error::Error>> {
        let url = format!("{}/write", self.base_url);
        let body = lines.join("\n");
        
        let response = self.http_client
            .post(&url)
            .header("Content-Type", "text/plain")
            .body(body)
            .send()
            .await?;
        
        if !response.status().is_success() {
            let error_text = response.text().await?;
            return Err(format!("VictoriaMetrics write failed: {}", error_text).into());
        }
        
        Ok(())
    }
    
    /// 查询数据（PromQL）
    pub async fn query(
        &self,
        promql: &str,
        time: Option<DateTime<Utc>>,
    ) -> Result<serde_json::Value, Box<dyn std::error::Error>> {
        let mut url = format!("{}/api/v1/query?query={}", self.base_url, urlencoding::encode(promql));
        
        if let Some(t) = time {
            url.push_str(&format!("&time={}", t.timestamp()));
        }
        
        let response = self.http_client
            .get(&url)
            .send()
            .await?;
        
        let result = response.json::<serde_json::Value>().await?;
        
        Ok(result)
    }
    
    /// 范围查询（PromQL）
    pub async fn query_range(
        &self,
        promql: &str,
        start: DateTime<Utc>,
        end: DateTime<Utc>,
        step: &str, // e.g., "15s"
    ) -> Result<serde_json::Value, Box<dyn std::error::Error>> {
        let url = format!(
            "{}/api/v1/query_range?query={}&start={}&end={}&step={}",
            self.base_url,
            urlencoding::encode(promql),
            start.timestamp(),
            end.timestamp(),
            step
        );
        
        let response = self.http_client
            .get(&url)
            .send()
            .await?;
        
        let result = response.json::<serde_json::Value>().await?;
        
        Ok(result)
    }
}
```

---

## 💾 列式存储引擎

### 1. Apache Parquet 集成

```rust
use parquet::{
    file::{
        properties::WriterProperties,
        writer::SerializedFileWriter,
    },
    schema::parser::parse_message_type,
};
use arrow::{
    array::{ArrayRef, Float64Array, Int64Array, StringArray, TimestampMillisecondArray},
    datatypes::{DataType, Field, Schema, TimeUnit},
    record_batch::RecordBatch,
};
use std::sync::Arc;

/// Parquet 写入器
pub struct ParquetWriter {
    output_path: std::path::PathBuf,
}

impl ParquetWriter {
    pub fn new(output_path: std::path::PathBuf) -> Self {
        Self { output_path }
    }
    
    /// 写入 Metric 数据到 Parquet 文件
    pub async fn write_metrics(
        &self,
        metrics: Vec<MetricRecord>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        // 定义 Schema
        let schema = Arc::new(Schema::new(vec![
            Field::new("timestamp", DataType::Timestamp(TimeUnit::Millisecond, None), false),
            Field::new("metric_name", DataType::Utf8, false),
            Field::new("service_name", DataType::Utf8, false),
            Field::new("value", DataType::Float64, false),
        ]));
        
        // 构建列数组
        let timestamps: Vec<i64> = metrics.iter().map(|m| m.timestamp.timestamp_millis()).collect();
        let metric_names: Vec<String> = metrics.iter().map(|m| m.metric_name.clone()).collect();
        let service_names: Vec<String> = metrics.iter().map(|m| m.service_name.clone()).collect();
        let values: Vec<f64> = metrics.iter().map(|m| m.value).collect();
        
        let timestamp_array: ArrayRef = Arc::new(TimestampMillisecondArray::from(timestamps));
        let metric_name_array: ArrayRef = Arc::new(StringArray::from(metric_names));
        let service_name_array: ArrayRef = Arc::new(StringArray::from(service_names));
        let value_array: ArrayRef = Arc::new(Float64Array::from(values));
        
        // 创建 RecordBatch
        let batch = RecordBatch::try_new(
            schema.clone(),
            vec![timestamp_array, metric_name_array, service_name_array, value_array],
        )?;
        
        // 写入 Parquet 文件
        let file = std::fs::File::create(&self.output_path)?;
        let props = WriterProperties::builder()
            .set_compression(parquet::basic::Compression::SNAPPY)
            .build();
        
        let mut writer = SerializedFileWriter::new(file, schema, Arc::new(props))?;
        
        let mut arrow_writer = parquet::arrow::ArrowWriter::try_new(
            &mut writer,
            batch.schema(),
            None,
        )?;
        
        arrow_writer.write(&batch)?;
        arrow_writer.close()?;
        
        tracing::info!("Wrote {} metrics to Parquet file: {:?}", metrics.len(), self.output_path);
        
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct MetricRecord {
    pub timestamp: DateTime<Utc>,
    pub metric_name: String,
    pub service_name: String,
    pub value: f64,
}
```

---

### 2. 列式数据写入器

```rust
/// 列式批量写入器
pub struct ColumnarBatchWriter {
    buffer: Vec<MetricRecord>,
    batch_size: usize,
    parquet_writer: ParquetWriter,
}

impl ColumnarBatchWriter {
    pub fn new(output_path: std::path::PathBuf, batch_size: usize) -> Self {
        Self {
            buffer: Vec::with_capacity(batch_size),
            batch_size,
            parquet_writer: ParquetWriter::new(output_path),
        }
    }
    
    /// 添加记录到缓冲区
    pub async fn add(&mut self, record: MetricRecord) -> Result<(), Box<dyn std::error::Error>> {
        self.buffer.push(record);
        
        if self.buffer.len() >= self.batch_size {
            self.flush().await?;
        }
        
        Ok(())
    }
    
    /// 刷新缓冲区
    pub async fn flush(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        if self.buffer.is_empty() {
            return Ok(());
        }
        
        self.parquet_writer.write_metrics(self.buffer.clone()).await?;
        self.buffer.clear();
        
        Ok(())
    }
}
```

---

## 🗜️ 数据压缩

### 1. 时序压缩算法

```rust
/// 时序数据压缩器
pub struct TimeSeriesCompressor {
    // 配置
}

impl TimeSeriesCompressor {
    /// Delta Encoding（差分编码）
    pub fn delta_encode(values: &[i64]) -> Vec<i64> {
        if values.is_empty() {
            return Vec::new();
        }
        
        let mut result = Vec::with_capacity(values.len());
        result.push(values[0]); // 第一个值保持不变
        
        for i in 1..values.len() {
            result.push(values[i] - values[i - 1]);
        }
        
        result
    }
    
    /// Delta Decoding（差分解码）
    pub fn delta_decode(deltas: &[i64]) -> Vec<i64> {
        if deltas.is_empty() {
            return Vec::new();
        }
        
        let mut result = Vec::with_capacity(deltas.len());
        result.push(deltas[0]);
        
        for i in 1..deltas.len() {
            result.push(result[i - 1] + deltas[i]);
        }
        
        result
    }
    
    /// Delta-of-Delta Encoding
    pub fn delta_of_delta_encode(values: &[i64]) -> Vec<i64> {
        let deltas = Self::delta_encode(values);
        Self::delta_encode(&deltas)
    }
    
    /// Delta-of-Delta Decoding
    pub fn delta_of_delta_decode(dods: &[i64]) -> Vec<i64> {
        let deltas = Self::delta_decode(dods);
        Self::delta_decode(&deltas)
    }
}
```

---

### 2. Gorilla 压缩

```rust
/// Gorilla 时间戳压缩（Facebook 算法）
pub struct GorillaTimestampCompressor {
    // 状态
}

impl GorillaTimestampCompressor {
    /// 压缩时间戳序列
    pub fn compress(&self, timestamps: &[i64]) -> Vec<u8> {
        if timestamps.is_empty() {
            return Vec::new();
        }
        
        let mut compressed = Vec::new();
        
        // 第一个时间戳完整存储（64位）
        compressed.extend_from_slice(&timestamps[0].to_be_bytes());
        
        if timestamps.len() == 1 {
            return compressed;
        }
        
        // 第二个时间戳存储为差值（64位）
        let delta1 = timestamps[1] - timestamps[0];
        compressed.extend_from_slice(&delta1.to_be_bytes());
        
        // 后续时间戳使用 Delta-of-Delta
        let mut prev_delta = delta1;
        
        for i in 2..timestamps.len() {
            let delta = timestamps[i] - timestamps[i - 1];
            let dod = delta - prev_delta;
            
            // 根据 DoD 的大小选择编码方式
            if dod == 0 {
                // 0 位：'0'
                compressed.push(0);
            } else if dod >= -63 && dod <= 64 {
                // 7 位：'10' + 7位有符号整数
                compressed.push(0x80 | ((dod & 0x7F) as u8));
            } else if dod >= -255 && dod <= 256 {
                // 9 位：'110' + 9位有符号整数
                compressed.push(0xC0 | ((dod >> 8) & 0x3) as u8);
                compressed.push((dod & 0xFF) as u8);
            } else {
                // 12 位或更多...
                compressed.extend_from_slice(&dod.to_be_bytes());
            }
            
            prev_delta = delta;
        }
        
        compressed
    }
}
```

---

### 3. Delta-of-Delta 编码

```rust
/// XOR 浮点数压缩（Gorilla 算法）
pub struct GorillaFloatCompressor {
    // 状态
}

impl GorillaFloatCompressor {
    /// 压缩浮点数序列
    pub fn compress(&self, values: &[f64]) -> Vec<u8> {
        if values.is_empty() {
            return Vec::new();
        }
        
        let mut compressed = Vec::new();
        
        // 第一个值完整存储
        compressed.extend_from_slice(&values[0].to_bits().to_be_bytes());
        
        if values.len() == 1 {
            return compressed;
        }
        
        let mut prev_bits = values[0].to_bits();
        let mut prev_leading_zeros = 0;
        let mut prev_trailing_zeros = 0;
        
        for &value in values.iter().skip(1) {
            let current_bits = value.to_bits();
            let xor = prev_bits ^ current_bits;
            
            if xor == 0 {
                // 值相同，写入 '0' 位
                compressed.push(0);
            } else {
                let leading_zeros = xor.leading_zeros();
                let trailing_zeros = xor.trailing_zeros();
                
                if leading_zeros >= prev_leading_zeros && trailing_zeros >= prev_trailing_zeros {
                    // 使用控制位 '10' + 中间位
                    compressed.push(0x80);
                    let meaningful_bits = 64 - leading_zeros - trailing_zeros;
                    let value_to_store = (xor >> trailing_zeros) & ((1 << meaningful_bits) - 1);
                    compressed.extend_from_slice(&value_to_store.to_be_bytes());
                } else {
                    // 使用控制位 '11' + leading zeros + meaningful bits length + meaningful bits
                    compressed.push(0xC0);
                    compressed.push(leading_zeros as u8);
                    let meaningful_bits = 64 - leading_zeros - trailing_zeros;
                    compressed.push(meaningful_bits as u8);
                    let value_to_store = (xor >> trailing_zeros) & ((1 << meaningful_bits) - 1);
                    compressed.extend_from_slice(&value_to_store.to_be_bytes());
                    
                    prev_leading_zeros = leading_zeros;
                    prev_trailing_zeros = trailing_zeros;
                }
            }
            
            prev_bits = current_bits;
        }
        
        compressed
    }
}
```

---

## 📈 数据保留策略

### 1. TTL 管理器

```rust
/// TTL（Time-To-Live）管理器
pub struct TtlManager {
    retention_policies: HashMap<String, chrono::Duration>,
}

impl TtlManager {
    pub fn new() -> Self {
        Self {
            retention_policies: HashMap::new(),
        }
    }
    
    /// 设置数据保留策略
    pub fn set_policy(&mut self, table_name: String, retention: chrono::Duration) {
        self.retention_policies.insert(table_name, retention);
    }
    
    /// 清理过期数据
    pub async fn cleanup_expired_data(&self, storage: &dyn StorageBackend) -> Result<(), Box<dyn std::error::Error>> {
        let now = Utc::now();
        
        for (table_name, retention) in &self.retention_policies {
            let cutoff_time = now - *retention;
            
            tracing::info!("Cleaning up data older than {} in table {}", cutoff_time, table_name);
            
            storage.delete_before(table_name, cutoff_time).await?;
        }
        
        Ok(())
    }
    
    /// 定期清理任务
    pub async fn start_cleanup_task(&self, storage: std::sync::Arc<dyn StorageBackend>, interval: std::time::Duration) {
        let mut interval_timer = tokio::time::interval(interval);
        
        loop {
            interval_timer.tick().await;
            
            if let Err(e) = self.cleanup_expired_data(storage.as_ref()).await {
                tracing::error!("TTL cleanup failed: {}", e);
            }
        }
    }
}
```

---

### 2. 数据降采样

```rust
/// 数据降采样器
pub struct Downsampler {
    // 配置
}

impl Downsampler {
    /// 降采样到指定时间粒度
    pub fn downsample(
        &self,
        data: Vec<MetricRecord>,
        bucket_size: chrono::Duration,
    ) -> Vec<MetricRecord> {
        if data.is_empty() {
            return Vec::new();
        }
        
        // 按时间桶分组
        let mut buckets: HashMap<i64, Vec<MetricRecord>> = HashMap::new();
        
        for record in data {
            let bucket = record.timestamp.timestamp() / bucket_size.num_seconds();
            buckets.entry(bucket).or_insert_with(Vec::new).push(record);
        }
        
        // 对每个桶进行聚合
        let mut result = Vec::new();
        
        for (bucket, records) in buckets {
            if let Some(first) = records.first() {
                let avg_value = records.iter().map(|r| r.value).sum::<f64>() / records.len() as f64;
                
                result.push(MetricRecord {
                    timestamp: DateTime::from_timestamp(bucket * bucket_size.num_seconds(), 0).unwrap(),
                    metric_name: first.metric_name.clone(),
                    service_name: first.service_name.clone(),
                    value: avg_value,
                });
            }
        }
        
        result.sort_by_key(|r| r.timestamp);
        
        result
    }
}
```

---

## 🔄 统一存储抽象

### 1. 存储后端 Trait

```rust
use async_trait::async_trait;

/// 存储后端 Trait
#[async_trait]
pub trait StorageBackend: Send + Sync {
    /// 写入单个 Metric
    async fn write_metric(&self, metric: &crate::DistributedMetric) -> Result<(), Box<dyn std::error::Error>>;
    
    /// 批量写入
    async fn write_batch(&self, metrics: Vec<crate::DistributedMetric>) -> Result<(), Box<dyn std::error::Error>>;
    
    /// 查询时间范围内的数据
    async fn query_range(
        &self,
        metric_name: &str,
        service_name: &str,
        start: DateTime<Utc>,
        end: DateTime<Utc>,
    ) -> Result<Vec<MetricRecord>, Box<dyn std::error::Error>>;
    
    /// 删除指定时间之前的数据
    async fn delete_before(&self, table_name: &str, cutoff: DateTime<Utc>) -> Result<(), Box<dyn std::error::Error>>;
    
    /// 健康检查
    async fn health_check(&self) -> Result<bool, Box<dyn std::error::Error>>;
}

/// InfluxDB 后端实现
pub struct InfluxDbBackend {
    client: InfluxDbClient,
    converter: OtlpToInfluxConverter,
}

#[async_trait]
impl StorageBackend for InfluxDbBackend {
    async fn write_metric(&self, metric: &crate::DistributedMetric) -> Result<(), Box<dyn std::error::Error>> {
        let points = self.converter.convert_metric(metric);
        self.client.write_points(points).await
    }
    
    async fn write_batch(&self, metrics: Vec<crate::DistributedMetric>) -> Result<(), Box<dyn std::error::Error>> {
        let mut all_points = Vec::new();
        
        for metric in &metrics {
            all_points.extend(self.converter.convert_metric(metric));
        }
        
        self.client.write_batch(all_points, 5000).await
    }
    
    async fn query_range(
        &self,
        metric_name: &str,
        service_name: &str,
        start: DateTime<Utc>,
        end: DateTime<Utc>,
    ) -> Result<Vec<MetricRecord>, Box<dyn std::error::Error>> {
        let flux_query = format!(
            r#"from(bucket: "otlp")
               |> range(start: {}, stop: {})
               |> filter(fn: (r) => r._measurement == "{}" and r.service_name == "{}")"#,
            start.to_rfc3339(),
            end.to_rfc3339(),
            metric_name,
            service_name
        );
        
        let results = self.client.query(&flux_query).await?;
        
        // 转换为 MetricRecord
        let mut records = Vec::new();
        
        for row in results {
            if let (Some(time), Some(value)) = (row.get("_time"), row.get("_value")) {
                // 简化转换
                records.push(MetricRecord {
                    timestamp: Utc::now(), // TODO: 解析时间
                    metric_name: metric_name.to_string(),
                    service_name: service_name.to_string(),
                    value: 0.0, // TODO: 解析值
                });
            }
        }
        
        Ok(records)
    }
    
    async fn delete_before(&self, _table_name: &str, _cutoff: DateTime<Utc>) -> Result<(), Box<dyn std::error::Error>> {
        // InfluxDB 使用 Retention Policy 自动删除
        Ok(())
    }
    
    async fn health_check(&self) -> Result<bool, Box<dyn std::error::Error>> {
        // 简化实现
        Ok(true)
    }
}
```

---

## 📊 完整示例：多后端存储系统

```rust
/// 多后端存储系统
pub struct MultiBackendStorage {
    backends: Vec<Box<dyn StorageBackend>>,
    write_strategy: WriteStrategy,
}

#[derive(Debug, Clone, Copy)]
pub enum WriteStrategy {
    /// 写入所有后端
    All,
    
    /// 写入主后端，异步复制到其他后端
    PrimaryWithAsyncReplication,
    
    /// 仅写入主后端
    PrimaryOnly,
}

impl MultiBackendStorage {
    pub fn new(backends: Vec<Box<dyn StorageBackend>>, write_strategy: WriteStrategy) -> Self {
        Self {
            backends,
            write_strategy,
        }
    }
    
    /// 写入 Metric
    pub async fn write_metric(&self, metric: crate::DistributedMetric) -> Result<(), Box<dyn std::error::Error>> {
        match self.write_strategy {
            WriteStrategy::All => {
                let mut handles = Vec::new();
                
                for backend in &self.backends {
                    let backend_clone = backend as *const dyn StorageBackend;
                    let metric_clone = metric.clone();
                    
                    let handle = tokio::spawn(async move {
                        unsafe { (*backend_clone).write_metric(&metric_clone).await }
                    });
                    
                    handles.push(handle);
                }
                
                for handle in handles {
                    handle.await??;
                }
            }
            
            WriteStrategy::PrimaryWithAsyncReplication => {
                // 同步写入主后端
                if let Some(primary) = self.backends.first() {
                    primary.write_metric(&metric).await?;
                }
                
                // 异步复制到其他后端
                for backend in self.backends.iter().skip(1) {
                    let backend_clone = backend as *const dyn StorageBackend;
                    let metric_clone = metric.clone();
                    
                    tokio::spawn(async move {
                        if let Err(e) = unsafe { (*backend_clone).write_metric(&metric_clone).await } {
                            tracing::error!("Async replication failed: {}", e);
                        }
                    });
                }
            }
            
            WriteStrategy::PrimaryOnly => {
                if let Some(primary) = self.backends.first() {
                    primary.write_metric(&metric).await?;
                }
            }
        }
        
        Ok(())
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt::init();
    
    // 初始化多个存储后端
    let influxdb_backend = Box::new(InfluxDbBackend {
        client: InfluxDbClient::new(
            "http://localhost:8086".to_string(),
            "my-token".to_string(),
            "my-org".to_string(),
            "otlp".to_string(),
        ),
        converter: OtlpToInfluxConverter::new(),
    });
    
    let backends: Vec<Box<dyn StorageBackend>> = vec![influxdb_backend];
    
    let storage = MultiBackendStorage::new(backends, WriteStrategy::All);
    
    println!("Multi-backend storage system initialized!");
    
    Ok(())
}
```

---

## 🎯 最佳实践

### 数据建模

- 使用时间戳作为主分区键
- 高基数标签使用哈希
- 避免过多的标签组合

### 写入优化

- 批量写入（5K-10K 数据点）
- 使用异步写入
- 启用压缩

### 查询优化

- 使用时间范围过滤
- 使用连续聚合
- 缓存热点查询

---

## 📚 参考资源

- [InfluxDB Documentation](https://docs.influxdata.com/)
- [TimescaleDB Best Practices](https://docs.timescale.com/)
- [Prometheus Storage](https://prometheus.io/docs/prometheus/latest/storage/)
- [Gorilla: A Fast, Scalable, In-Memory Time Series Database](https://www.vldb.org/pvldb/vol8/p1816-teller.pdf)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-10  
**作者**: OTLP Rust 项目组
