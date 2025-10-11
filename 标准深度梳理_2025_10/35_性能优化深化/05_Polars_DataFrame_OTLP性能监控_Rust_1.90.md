# Polars DataFrame - OTLP 性能监控完整指南 (Rust 1.90)

> **文档版本**: v1.0  
> **创建日期**: 2025-10-11  
> **Rust 版本**: 1.90+  
> **Polars 版本**: 0.47.0  
> **OpenTelemetry**: 0.31.0  
> **GitHub Stars**: 30.8k+
> **对标**: Pandas, Apache Spark

---

## 📋 概述

**Polars** 是 Rust 实现的 DataFrame 库,性能超越 Pandas 5倍,内存占用降低 50%!

### 核心特性

- ✅ **列式存储**: Arrow 内存格式
- ✅ **并行执行**: Rayon 多线程
- ✅ **惰性求值**: 查询优化
- ✅ **零拷贝**: 高效数据处理

---

## 性能对比

| 操作 | Pandas | Spark | **Polars** | 改进 |
|------|--------|-------|-----------|------|
| **读取 1GB CSV** | 12 s | 8 s | **2.4 s** | **5x ↑** |
| **GroupBy 聚合** | 8 s | 6 s | **1.2 s** | **6.7x ↑** |
| **Join (1M rows)** | 5 s | 3.5 s | **0.9 s** | **5.6x ↑** |
| **内存占用** | 8 GB | 6 GB | **4 GB** | **50% ↓** |

---

## 完整示例

### 1. 基础 DataFrame 操作 + OTLP

```rust
use polars::prelude::*;
use std::time::Instant;
use tracing::{info, instrument};
use opentelemetry::{global, trace::Tracer, KeyValue};

/// 加载 CSV 文件
#[instrument]
pub fn load_csv(path: &str) -> Result<DataFrame, PolarsError> {
    let tracer = global::tracer("polars_pipeline");
    let mut span = tracer.span_builder("load_csv").start(&tracer);
    
    let start = Instant::now();
    
    let df = CsvReadOptions::default()
        .with_has_header(true)
        .try_into_reader_with_file_path(Some(path.into()))?
        .finish()?;
    
    let elapsed = start.elapsed();
    let row_count = df.height();
    
    span.set_attribute(KeyValue::new("df.rows", row_count as i64));
    span.set_attribute(KeyValue::new("df.columns", df.width() as i64));
    span.set_attribute(KeyValue::new("load.duration_ms", elapsed.as_millis() as i64));
    
    info!(
        path = path,
        rows = row_count,
        duration_ms = elapsed.as_millis(),
        "CSV loaded successfully"
    );
    
    Ok(df)
}

/// 数据清洗
#[instrument(skip(df))]
pub fn clean_data(df: DataFrame) -> Result<DataFrame, PolarsError> {
    let tracer = global::tracer("polars_pipeline");
    let mut span = tracer.span_builder("clean_data").start(&tracer);
    
    let start = Instant::now();
    let initial_rows = df.height();
    
    // 删除空值
    let df = df.drop_nulls::<String>(None)?;
    
    // 删除重复行
    let df = df.unique(None, UniqueKeepStrategy::First, None)?;
    
    let elapsed = start.elapsed();
    let final_rows = df.height();
    let removed_rows = initial_rows - final_rows;
    
    span.set_attribute(KeyValue::new("clean.initial_rows", initial_rows as i64));
    span.set_attribute(KeyValue::new("clean.final_rows", final_rows as i64));
    span.set_attribute(KeyValue::new("clean.removed_rows", removed_rows as i64));
    span.set_attribute(KeyValue::new("clean.duration_ms", elapsed.as_millis() as i64));
    
    info!(
        removed_rows = removed_rows,
        duration_ms = elapsed.as_millis(),
        "Data cleaned"
    );
    
    Ok(df)
}

/// GroupBy 聚合
#[instrument(skip(df))]
pub fn aggregate_by_category(df: DataFrame) -> Result<DataFrame, PolarsError> {
    let tracer = global::tracer("polars_pipeline");
    let mut span = tracer.span_builder("aggregate_by_category").start(&tracer);
    
    let start = Instant::now();
    
    let result = df
        .lazy()
        .group_by([col("category")])
        .agg([
            col("amount").sum().alias("total_amount"),
            col("amount").mean().alias("avg_amount"),
            col("amount").count().alias("count"),
        ])
        .sort(["total_amount"], Default::default())
        .collect()?;
    
    let elapsed = start.elapsed();
    
    span.set_attribute(KeyValue::new("agg.groups", result.height() as i64));
    span.set_attribute(KeyValue::new("agg.duration_ms", elapsed.as_millis() as i64));
    
    info!(
        groups = result.height(),
        duration_ms = elapsed.as_millis(),
        "Aggregation completed"
    );
    
    Ok(result)
}

/// Join 操作
#[instrument(skip(left, right))]
pub fn join_dataframes(left: DataFrame, right: DataFrame) -> Result<DataFrame, PolarsError> {
    let tracer = global::tracer("polars_pipeline");
    let mut span = tracer.span_builder("join_dataframes").start(&tracer);
    
    let start = Instant::now();
    let left_rows = left.height();
    let right_rows = right.height();
    
    let result = left.join(
        &right,
        ["user_id"],
        ["user_id"],
        JoinArgs::new(JoinType::Inner),
    )?;
    
    let elapsed = start.elapsed();
    let result_rows = result.height();
    
    span.set_attribute(KeyValue::new("join.left_rows", left_rows as i64));
    span.set_attribute(KeyValue::new("join.right_rows", right_rows as i64));
    span.set_attribute(KeyValue::new("join.result_rows", result_rows as i64));
    span.set_attribute(KeyValue::new("join.duration_ms", elapsed.as_millis() as i64));
    
    info!(
        left_rows = left_rows,
        right_rows = right_rows,
        result_rows = result_rows,
        duration_ms = elapsed.as_millis(),
        "Join completed"
    );
    
    Ok(result)
}
```

---

## 惰性求值 (Lazy Evaluation)

```rust
/// 复杂查询优化示例
#[instrument]
pub fn optimized_pipeline(path: &str) -> Result<DataFrame, PolarsError> {
    let tracer = global::tracer("polars_pipeline");
    let mut span = tracer.span_builder("optimized_pipeline").start(&tracer);
    
    let start = Instant::now();
    
    // 惰性读取 + 查询优化
    let result = LazyCsvReader::new(path)
        .has_header(true)
        .finish()?
        .filter(col("amount").gt(lit(100)))  // 过滤
        .with_columns([
            (col("amount") * lit(1.1)).alias("amount_with_tax"),  // 计算新列
        ])
        .group_by([col("category")])  // 分组
        .agg([
            col("amount_with_tax").sum().alias("total"),
            col("amount_with_tax").mean().alias("average"),
        ])
        .sort(["total"], SortMultipleOptions::default().with_order_descending(true))  // 排序
        .limit(10)  // 限制结果
        .collect()?;  // 执行查询
    
    let elapsed = start.elapsed();
    
    span.set_attribute(KeyValue::new("pipeline.duration_ms", elapsed.as_millis() as i64));
    span.set_attribute(KeyValue::new("pipeline.result_rows", result.height() as i64));
    
    info!(
        duration_ms = elapsed.as_millis(),
        result_rows = result.height(),
        "Optimized pipeline completed"
    );
    
    Ok(result)
}
```

---

## 并行处理

```rust
use rayon::prelude::*;

/// 并行处理多个文件
#[instrument(skip(file_paths))]
pub fn parallel_load_csv(file_paths: Vec<&str>) -> Result<Vec<DataFrame>, PolarsError> {
    let tracer = global::tracer("polars_pipeline");
    let mut span = tracer.span_builder("parallel_load_csv").start(&tracer);
    
    let start = Instant::now();
    
    let results: Vec<_> = file_paths
        .par_iter()
        .map(|path| {
            info!(path = path, "Loading file");
            load_csv(path)
        })
        .collect();
    
    let elapsed = start.elapsed();
    
    span.set_attribute(KeyValue::new("parallel.files", file_paths.len() as i64));
    span.set_attribute(KeyValue::new("parallel.duration_ms", elapsed.as_millis() as i64));
    
    info!(
        files = file_paths.len(),
        duration_ms = elapsed.as_millis(),
        "Parallel load completed"
    );
    
    results.into_iter().collect()
}
```

---

## 内存监控

```rust
use sysinfo::{System, SystemExt};

/// 监控内存使用
pub fn monitor_memory_usage(stage: &str) {
    let mut sys = System::new_all();
    sys.refresh_all();
    
    let used_memory = sys.used_memory();
    let total_memory = sys.total_memory();
    let memory_percent = (used_memory as f64 / total_memory as f64) * 100.0;
    
    info!(
        stage = stage,
        used_mb = used_memory / 1024 / 1024,
        total_mb = total_memory / 1024 / 1024,
        percent = format!("{:.2}%", memory_percent),
        "Memory usage"
    );
}

/// 完整数据管道 + 内存监控
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化 OpenTelemetry
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(opentelemetry_otlp::new_exporter().tonic())
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;

    let telemetry = tracing_opentelemetry::layer().with_tracer(tracer);
    tracing_subscriber::registry()
        .with(telemetry)
        .with(tracing_subscriber::fmt::layer())
        .init();

    monitor_memory_usage("start");
    
    // 加载数据
    let df = load_csv("data.csv")?;
    monitor_memory_usage("after_load");
    
    // 清洗数据
    let df = clean_data(df)?;
    monitor_memory_usage("after_clean");
    
    // 聚合数据
    let result = aggregate_by_category(df)?;
    monitor_memory_usage("after_aggregate");
    
    println!("{:?}", result);
    
    Ok(())
}
```

---

## Cargo.toml

```toml
[package]
name = "polars-otlp"
version = "1.0.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# Polars
polars = { version = "0.47", features = ["lazy", "csv", "parquet", "dtype-full"] }

# 并行处理
rayon = "1.10"

# 异步运行时
tokio = { version = "1.41", features = ["full"] }

# OpenTelemetry
opentelemetry = "0.31"
opentelemetry_sdk = "0.31"
opentelemetry-otlp = "0.16"
tracing = "0.1"
tracing-subscriber = "0.3.18"
tracing-opentelemetry = "0.30"

# 系统监控
sysinfo = "0.32"
```

---

**🚀 Polars: 5x Pandas 性能 + 完整 OTLP 追踪 🚀**-
