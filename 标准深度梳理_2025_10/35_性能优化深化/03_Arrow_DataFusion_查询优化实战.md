# Arrow DataFusion 查询优化实战 - OTLP 数据分析加速

> **Rust版本**: 1.90+  
> **DataFusion**: 43.0+  
> **Arrow**: 54.0+  
> **最后更新**: 2025年10月10日

---

## 📋 目录

- [1. DataFusion 简介](#1-datafusion-简介)
- [2. OTLP 数据查询场景](#2-otlp-数据查询场景)
- [3. 查询优化技术](#3-查询优化技术)
- [4. 实战案例](#4-实战案例)
- [5. 性能调优](#5-性能调优)
- [6. 生产部署](#6-生产部署)

---

## 1. DataFusion 简介

### 1.1 什么是 DataFusion

```text
DataFusion = Arrow + SQL + 查询优化器

┌─────────────────────────────────────────┐
│          SQL/DataFrame API              │
├─────────────────────────────────────────┤
│       逻辑计划 & 优化器                  │
│  - 谓词下推                              │
│  - 投影下推                              │
│  - 常量折叠                              │
│  - 公共子表达式消除                      │
├─────────────────────────────────────────┤
│       物理计划 & 执行                    │
│  - 向量化执行                            │
│  - 并行执行                              │
│  - 流式处理                              │
├─────────────────────────────────────────┤
│       Apache Arrow 内存格式              │
└─────────────────────────────────────────┘
```

### 1.2 核心特性

```rust
use datafusion::prelude::*;
use datafusion::arrow::array::*;

/// DataFusion 43.0 核心特性
pub struct DataFusionFeatures;

impl DataFusionFeatures {
    /// 特性列表
    pub fn features() -> Vec<&'static str> {
        vec![
            "✅ SQL 查询支持 (完整 SQL-92)",
            "✅ DataFrame API",
            "✅ 查询优化器 (谓词下推、投影下推等)",
            "✅ 向量化执行引擎",
            "✅ 并行查询执行",
            "✅ 流式处理",
            "✅ 自定义函数 (UDF/UDAF)",
            "✅ Parquet 原生支持",
            "✅ CSV, JSON, Avro 支持",
            "✅ 内存表和外部表",
            "✅ 分区表支持",
            "✅ 窗口函数",
            "✅ 复杂类型 (Array, Struct, Map)",
        ]
    }
}
```

---

## 2. OTLP 数据查询场景

### 2.1 典型查询场景

```rust
use datafusion::prelude::*;
use datafusion::arrow::datatypes::*;

/// OTLP Trace 数据查询场景
pub struct OtlpQueryScenarios;

impl OtlpQueryScenarios {
    /// 场景1: 按 TraceID 查询完整链路
    pub async fn query_full_trace(
        ctx: &SessionContext,
        trace_id: &str,
    ) -> Result<Vec<RecordBatch>, DataFusionError> {
        ctx.sql(&format!(
            "SELECT * FROM traces WHERE trace_id = '{}' ORDER BY start_time",
            trace_id
        ))
        .await?
        .collect()
        .await
    }
    
    /// 场景2: 慢查询分析
    pub async fn analyze_slow_queries(
        ctx: &SessionContext,
        threshold_ms: i64,
    ) -> Result<Vec<RecordBatch>, DataFusionError> {
        ctx.sql(&format!(
            "
            SELECT 
                service_name,
                operation_name,
                COUNT(*) as slow_count,
                AVG(duration_ms) as avg_duration,
                MAX(duration_ms) as max_duration,
                PERCENTILE_CONT(0.95) WITHIN GROUP (ORDER BY duration_ms) as p95_duration
            FROM traces
            WHERE duration_ms > {}
            GROUP BY service_name, operation_name
            ORDER BY slow_count DESC
            LIMIT 100
            ",
            threshold_ms
        ))
        .await?
        .collect()
        .await
    }
    
    /// 场景3: 错误率分析
    pub async fn error_rate_analysis(
        ctx: &SessionContext,
    ) -> Result<Vec<RecordBatch>, DataFusionError> {
        ctx.sql(
            "
            SELECT 
                service_name,
                DATE_TRUNC('hour', start_time) as hour,
                COUNT(*) as total_requests,
                SUM(CASE WHEN status_code = 2 THEN 1 ELSE 0 END) as error_count,
                SUM(CASE WHEN status_code = 2 THEN 1 ELSE 0 END) * 100.0 / COUNT(*) as error_rate
            FROM traces
            WHERE start_time > NOW() - INTERVAL '24 hours'
            GROUP BY service_name, hour
            ORDER BY error_rate DESC
            "
        )
        .await?
        .collect()
        .await
    }
    
    /// 场景4: 服务依赖图
    pub async fn service_dependency_graph(
        ctx: &SessionContext,
    ) -> Result<Vec<RecordBatch>, DataFusionError> {
        ctx.sql(
            "
            WITH parent_child AS (
                SELECT 
                    parent.service_name as parent_service,
                    child.service_name as child_service,
                    COUNT(*) as call_count,
                    AVG(child.duration_ms) as avg_duration
                FROM traces parent
                JOIN traces child ON parent.trace_id = child.trace_id 
                    AND parent.span_id = child.parent_span_id
                WHERE parent.start_time > NOW() - INTERVAL '1 hour'
                GROUP BY parent_service, child_service
            )
            SELECT * FROM parent_child
            WHERE call_count > 10
            ORDER BY call_count DESC
            "
        )
        .await?
        .collect()
        .await
    }
    
    /// 场景5: 时间序列聚合
    pub async fn timeseries_aggregation(
        ctx: &SessionContext,
        interval: &str,
    ) -> Result<Vec<RecordBatch>, DataFusionError> {
        ctx.sql(&format!(
            "
            SELECT 
                DATE_TRUNC('{}', start_time) as time_bucket,
                service_name,
                COUNT(*) as request_count,
                AVG(duration_ms) as avg_duration,
                PERCENTILE_CONT(0.50) WITHIN GROUP (ORDER BY duration_ms) as p50,
                PERCENTILE_CONT(0.95) WITHIN GROUP (ORDER BY duration_ms) as p95,
                PERCENTILE_CONT(0.99) WITHIN GROUP (ORDER BY duration_ms) as p99
            FROM traces
            WHERE start_time > NOW() - INTERVAL '24 hours'
            GROUP BY time_bucket, service_name
            ORDER BY time_bucket, service_name
            ",
            interval
        ))
        .await?
        .collect()
        .await
    }
}
```

---

## 3. 查询优化技术

### 3.1 谓词下推优化

```rust
use datafusion::logical_expr::*;
use datafusion::optimizer::*;

/// 谓词下推示例
pub async fn predicate_pushdown_example() -> Result<(), DataFusionError> {
    let ctx = SessionContext::new();
    
    // 注册表
    ctx.sql(
        "CREATE EXTERNAL TABLE traces (
            trace_id VARCHAR,
            span_id VARCHAR,
            service_name VARCHAR,
            duration_ms BIGINT,
            start_time TIMESTAMP
        ) STORED AS PARQUET LOCATION './traces.parquet'"
    ).await?;
    
    // 查询 (自动谓词下推)
    let df = ctx.sql(
        "
        SELECT service_name, AVG(duration_ms)
        FROM traces
        WHERE service_name = 'api-gateway'
          AND start_time > NOW() - INTERVAL '1 hour'
        GROUP BY service_name
        "
    ).await?;
    
    // 查看优化后的计划
    let logical_plan = df.logical_plan().clone();
    println!("Logical Plan:\n{}", logical_plan.display_indent());
    
    // 查看物理计划
    let physical_plan = df.create_physical_plan().await?;
    println!("\nPhysical Plan:\n{}", displayable(physical_plan.as_ref()).indent(true));
    
    Ok(())
}
```

### 3.2 投影下推优化

```rust
/// 投影下推示例
pub async fn projection_pushdown_example() -> Result<(), DataFusionError> {
    let ctx = SessionContext::new();
    
    // 只读取需要的列 (投影下推到 Parquet)
    let df = ctx.sql(
        "
        SELECT 
            service_name,
            duration_ms
        FROM traces
        WHERE start_time > NOW() - INTERVAL '1 hour'
        "
    ).await?;
    
    // DataFusion 会优化为只读取 service_name 和 duration_ms 列
    // 避免读取整行数据
    
    let results = df.collect().await?;
    println!("Projection pushdown saved {} columns from reading", 
        results[0].num_columns());
    
    Ok(())
}
```

### 3.3 分区剪枝

```rust
/// 分区剪枝示例
pub async fn partition_pruning_example() -> Result<(), DataFusionError> {
    let ctx = SessionContext::new();
    
    // 创建分区表 (按日期分区)
    ctx.sql(
        "
        CREATE EXTERNAL TABLE traces (
            trace_id VARCHAR,
            service_name VARCHAR,
            duration_ms BIGINT,
            start_time TIMESTAMP
        ) 
        STORED AS PARQUET 
        LOCATION './traces/'
        PARTITIONED BY (date DATE)
        "
    ).await?;
    
    // 查询特定分区 (自动剪枝)
    let df = ctx.sql(
        "
        SELECT service_name, COUNT(*)
        FROM traces
        WHERE date = '2025-10-10'
        GROUP BY service_name
        "
    ).await?;
    
    // DataFusion 只扫描 2025-10-10 分区
    // 跳过其他分区文件
    
    let results = df.collect().await?;
    println!("Partition pruning scanned only 1 partition");
    
    Ok(())
}
```

### 3.4 向量化执行

```rust
use datafusion::physical_plan::*;

/// 向量化执行示例
pub async fn vectorized_execution_example() -> Result<(), DataFusionError> {
    let ctx = SessionContext::new();
    
    // 创建测试数据
    let batch = create_test_batch()?;
    ctx.register_batch("traces", batch)?;
    
    // 向量化聚合
    let df = ctx.sql(
        "
        SELECT 
            service_name,
            COUNT(*) as count,
            AVG(duration_ms) as avg_duration,
            SUM(duration_ms) as total_duration,
            MIN(duration_ms) as min_duration,
            MAX(duration_ms) as max_duration
        FROM traces
        GROUP BY service_name
        "
    ).await?;
    
    // DataFusion 使用向量化执行:
    // - 一次处理多行 (batch)
    // - SIMD 加速
    // - 减少函数调用开销
    
    let start = Instant::now();
    let results = df.collect().await?;
    let duration = start.elapsed();
    
    println!("Vectorized execution completed in {:?}", duration);
    
    Ok(())
}

fn create_test_batch() -> Result<RecordBatch, ArrowError> {
    let schema = Arc::new(Schema::new(vec![
        Field::new("service_name", DataType::Utf8, false),
        Field::new("duration_ms", DataType::Int64, false),
    ]));
    
    let services: Vec<&str> = (0..100000)
        .map(|i| if i % 3 == 0 { "api-gateway" } 
                 else if i % 3 == 1 { "user-service" } 
                 else { "order-service" })
        .collect();
    
    let durations: Vec<i64> = (0..100000)
        .map(|_| rand::random::<i64>() % 1000)
        .collect();
    
    RecordBatch::try_new(
        schema,
        vec![
            Arc::new(StringArray::from(services)),
            Arc::new(Int64Array::from(durations)),
        ],
    )
}
```

---

## 4. 实战案例

### 4.1 完整的 OTLP 查询引擎

```rust
use datafusion::prelude::*;
use datafusion::arrow::datatypes::*;
use std::sync::Arc;
use tokio::sync::RwLock;

/// OTLP 查询引擎
pub struct OtlpQueryEngine {
    ctx: Arc<SessionContext>,
    config: QueryEngineConfig,
}

#[derive(Debug, Clone)]
pub struct QueryEngineConfig {
    /// 并行度
    pub parallelism: usize,
    
    /// 批处理大小
    pub batch_size: usize,
    
    /// 启用分区剪枝
    pub enable_partition_pruning: bool,
    
    /// 启用谓词下推
    pub enable_predicate_pushdown: bool,
}

impl OtlpQueryEngine {
    /// 创建查询引擎
    pub async fn new(config: QueryEngineConfig) -> Result<Self, DataFusionError> {
        // 创建 SessionContext 并配置
        let mut ctx_config = SessionConfig::new()
            .with_target_partitions(config.parallelism)
            .with_batch_size(config.batch_size);
        
        if config.enable_partition_pruning {
            ctx_config = ctx_config.set_bool("datafusion.execution.enable_partition_pruning", true);
        }
        
        let ctx = SessionContext::new_with_config(ctx_config);
        
        Ok(Self {
            ctx: Arc::new(ctx),
            config,
        })
    }
    
    /// 注册 Trace 数据源
    pub async fn register_trace_source(
        &self,
        name: &str,
        path: &str,
    ) -> Result<(), DataFusionError> {
        self.ctx.sql(&format!(
            "
            CREATE EXTERNAL TABLE {} (
                trace_id VARCHAR,
                span_id VARCHAR,
                parent_span_id VARCHAR,
                service_name VARCHAR,
                operation_name VARCHAR,
                kind INT,
                start_time TIMESTAMP,
                end_time TIMESTAMP,
                duration_ms BIGINT,
                status_code INT,
                status_message VARCHAR,
                attributes VARCHAR,
                resource_attributes VARCHAR
            )
            STORED AS PARQUET
            LOCATION '{}'
            ",
            name, path
        )).await?;
        
        Ok(())
    }
    
    /// 查询 Trace
    pub async fn query_traces(
        &self,
        sql: &str,
    ) -> Result<Vec<RecordBatch>, DataFusionError> {
        let start = Instant::now();
        
        let df = self.ctx.sql(sql).await?;
        let results = df.collect().await?;
        
        let duration = start.elapsed();
        tracing::info!(
            "Query executed in {:?}, returned {} batches",
            duration,
            results.len()
        );
        
        Ok(results)
    }
    
    /// 创建物化视图 (预聚合)
    pub async fn create_materialized_view(
        &self,
        view_name: &str,
        query: &str,
    ) -> Result<(), DataFusionError> {
        // 执行查询
        let df = self.ctx.sql(query).await?;
        let results = df.collect().await?;
        
        // 注册为内存表
        self.ctx.register_batch(view_name, results[0].clone())?;
        
        tracing::info!("Materialized view '{}' created", view_name);
        
        Ok(())
    }
    
    /// 注册自定义函数
    pub async fn register_custom_functions(&self) -> Result<(), DataFusionError> {
        use datafusion::logical_expr::{create_udf, Volatility};
        use datafusion::arrow::array::StringArray;
        
        // UDF: 提取 TraceID 的前8位
        let trace_id_prefix = create_udf(
            "trace_id_prefix",
            vec![DataType::Utf8],
            Arc::new(DataType::Utf8),
            Volatility::Immutable,
            Arc::new(move |args| {
                let trace_ids = args[0]
                    .as_any()
                    .downcast_ref::<StringArray>()
                    .unwrap();
                
                let result: StringArray = trace_ids
                    .iter()
                    .map(|trace_id| {
                        trace_id.map(|s| s.chars().take(8).collect::<String>())
                    })
                    .collect();
                
                Ok(Arc::new(result) as ArrayRef)
            }),
        );
        
        self.ctx.register_udf(trace_id_prefix);
        
        Ok(())
    }
}

/// 使用示例
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建查询引擎
    let config = QueryEngineConfig {
        parallelism: num_cpus::get(),
        batch_size: 8192,
        enable_partition_pruning: true,
        enable_predicate_pushdown: true,
    };
    
    let engine = OtlpQueryEngine::new(config).await?;
    
    // 注册数据源
    engine.register_trace_source("traces", "./data/traces.parquet").await?;
    
    // 注册自定义函数
    engine.register_custom_functions().await?;
    
    // 执行查询
    let results = engine.query_traces(
        "
        SELECT 
            service_name,
            COUNT(*) as request_count,
            AVG(duration_ms) as avg_duration
        FROM traces
        WHERE start_time > NOW() - INTERVAL '1 hour'
        GROUP BY service_name
        ORDER BY request_count DESC
        "
    ).await?;
    
    // 打印结果
    arrow::util::pretty::print_batches(&results)?;
    
    Ok(())
}
```

### 4.2 实时聚合引擎

```rust
use tokio::sync::mpsc;
use tokio_stream::StreamExt;

/// 实时聚合引擎
pub struct RealtimeAggregationEngine {
    engine: Arc<OtlpQueryEngine>,
    aggregator: Arc<RwLock<WindowAggregator>>,
}

/// 滑动窗口聚合器
struct WindowAggregator {
    window_size: Duration,
    batches: VecDeque<TimestampedBatch>,
}

struct TimestampedBatch {
    timestamp: Instant,
    batch: RecordBatch,
}

impl RealtimeAggregationEngine {
    pub fn new(
        engine: Arc<OtlpQueryEngine>,
        window_size: Duration,
    ) -> Self {
        Self {
            engine,
            aggregator: Arc::new(RwLock::new(WindowAggregator {
                window_size,
                batches: VecDeque::new(),
            })),
        }
    }
    
    /// 处理实时数据流
    pub async fn process_stream(
        &self,
        mut stream: mpsc::Receiver<RecordBatch>,
    ) -> Result<(), DataFusionError> {
        while let Some(batch) = stream.recv().await {
            // 添加到窗口
            self.add_batch(batch).await?;
            
            // 执行聚合
            let aggregated = self.aggregate_window().await?;
            
            // 输出结果
            self.emit_results(aggregated).await?;
        }
        
        Ok(())
    }
    
    async fn add_batch(&self, batch: RecordBatch) -> Result<(), DataFusionError> {
        let mut aggregator = self.aggregator.write().await;
        
        // 添加新批次
        aggregator.batches.push_back(TimestampedBatch {
            timestamp: Instant::now(),
            batch,
        });
        
        // 移除过期批次
        let cutoff = Instant::now() - aggregator.window_size;
        while let Some(oldest) = aggregator.batches.front() {
            if oldest.timestamp < cutoff {
                aggregator.batches.pop_front();
            } else {
                break;
            }
        }
        
        Ok(())
    }
    
    async fn aggregate_window(&self) -> Result<Vec<RecordBatch>, DataFusionError> {
        let aggregator = self.aggregator.read().await;
        
        if aggregator.batches.is_empty() {
            return Ok(vec![]);
        }
        
        // 合并所有批次
        let schema = aggregator.batches[0].batch.schema();
        let batches: Vec<RecordBatch> = aggregator.batches
            .iter()
            .map(|tb| tb.batch.clone())
            .collect();
        
        use arrow::compute::concat_batches;
        let combined = concat_batches(&schema, &batches)?;
        
        // 注册临时表
        self.engine.ctx.register_batch("window_data", combined)?;
        
        // 执行聚合查询
        let results = self.engine.query_traces(
            "
            SELECT 
                service_name,
                COUNT(*) as count,
                AVG(duration_ms) as avg_duration,
                PERCENTILE_CONT(0.95) WITHIN GROUP (ORDER BY duration_ms) as p95
            FROM window_data
            GROUP BY service_name
            "
        ).await?;
        
        Ok(results)
    }
    
    async fn emit_results(&self, results: Vec<RecordBatch>) -> Result<(), DataFusionError> {
        for batch in results {
            arrow::util::pretty::print_batches(&[batch])?;
        }
        Ok(())
    }
}
```

---

## 5. 性能调优

### 5.1 查询性能分析

```rust
use datafusion::physical_plan::display::DisplayableExecutionPlan;

/// 查询性能分析器
pub struct QueryProfiler {
    ctx: Arc<SessionContext>,
}

impl QueryProfiler {
    pub async fn analyze_query(
        &self,
        sql: &str,
    ) -> Result<QueryProfile, DataFusionError> {
        let start = Instant::now();
        
        // 1. 解析查询
        let df = self.ctx.sql(sql).await?;
        let parse_time = start.elapsed();
        
        // 2. 查看逻辑计划
        let logical_plan = df.logical_plan().clone();
        println!("=== Logical Plan ===");
        println!("{}", logical_plan.display_indent());
        
        // 3. 优化逻辑计划
        let optimized_plan = self.ctx.state().optimize(&logical_plan)?;
        println!("\n=== Optimized Logical Plan ===");
        println!("{}", optimized_plan.display_indent());
        
        // 4. 创建物理计划
        let physical_plan = df.create_physical_plan().await?;
        println!("\n=== Physical Plan ===");
        println!("{}", DisplayableExecutionPlan::new(physical_plan.as_ref()).indent(true));
        
        // 5. 执行查询
        let exec_start = Instant::now();
        let results = df.collect().await?;
        let exec_time = exec_start.elapsed();
        
        // 6. 收集统计信息
        let total_rows: usize = results.iter().map(|b| b.num_rows()).sum();
        let total_bytes: usize = results.iter()
            .map(|b| b.get_array_memory_size())
            .sum();
        
        Ok(QueryProfile {
            parse_time,
            execution_time: exec_time,
            total_rows,
            total_bytes,
            num_batches: results.len(),
        })
    }
}

#[derive(Debug)]
pub struct QueryProfile {
    pub parse_time: Duration,
    pub execution_time: Duration,
    pub total_rows: usize,
    pub total_bytes: usize,
    pub num_batches: usize,
}

impl QueryProfile {
    pub fn print_summary(&self) {
        println!("\n=== Query Profile ===");
        println!("Parse time: {:?}", self.parse_time);
        println!("Execution time: {:?}", self.execution_time);
        println!("Total rows: {}", self.total_rows);
        println!("Total bytes: {} MB", self.total_bytes / 1024 / 1024);
        println!("Num batches: {}", self.num_batches);
        println!("Throughput: {:.2} M rows/sec", 
            self.total_rows as f64 / self.execution_time.as_secs_f64() / 1_000_000.0);
    }
}
```

### 5.2 配置优化建议

```rust
/// 性能调优配置
pub struct PerformanceTuning;

impl PerformanceTuning {
    /// 推荐配置
    pub fn recommended_config() -> SessionConfig {
        SessionConfig::new()
            // 并行度: CPU核心数
            .with_target_partitions(num_cpus::get())
            
            // 批处理大小: 8192 (平衡内存和性能)
            .with_batch_size(8192)
            
            // 启用所有优化
            .set_bool("datafusion.optimizer.filter_null_join_keys", true)
            .set_bool("datafusion.optimizer.skip_failed_rules", false)
            .set_bool("datafusion.execution.coalesce_batches", true)
            
            // 内存限制 (防止 OOM)
            .set_u64("datafusion.execution.memory_pool_size", 8 * 1024 * 1024 * 1024) // 8GB
            
            // 排序内存限制
            .set_usize("datafusion.execution.sort_in_place_threshold_bytes", 256 * 1024 * 1024) // 256MB
            
            // 分区数限制
            .set_usize("datafusion.execution.max_partitions", 512)
            
            // 启用统计信息收集
            .set_bool("datafusion.execution.collect_statistics", true)
    }
    
    /// 大数据量配置
    pub fn large_dataset_config() -> SessionConfig {
        Self::recommended_config()
            .with_batch_size(16384)  // 更大的批次
            .set_u64("datafusion.execution.memory_pool_size", 32 * 1024 * 1024 * 1024) // 32GB
            .set_usize("datafusion.execution.max_partitions", 2048)
    }
    
    /// 低延迟配置
    pub fn low_latency_config() -> SessionConfig {
        Self::recommended_config()
            .with_batch_size(1024)   // 更小的批次
            .with_target_partitions(1)  // 减少并行度
    }
}
```

---

## 6. 生产部署

### 6.1 Kubernetes 部署

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otlp-query-engine
spec:
  replicas: 3
  selector:
    matchLabels:
      app: otlp-query-engine
  template:
    metadata:
      labels:
        app: otlp-query-engine
    spec:
      containers:
      - name: query-engine
        image: otlp-datafusion:latest
        resources:
          requests:
            memory: "8Gi"
            cpu: "4"
          limits:
            memory: "16Gi"
            cpu: "8"
        env:
        - name: RUST_LOG
          value: "info"
        - name: DATAFUSION_PARALLELISM
          value: "8"
        - name: DATAFUSION_BATCH_SIZE
          value: "8192"
        ports:
        - containerPort: 8080
          name: http
        volumeMounts:
        - name: data
          mountPath: /data
      volumes:
      - name: data
        persistentVolumeClaim:
          claimName: traces-data-pvc
```

### 6.2 监控指标

```rust
use metrics::{counter, histogram, gauge};

/// 查询引擎监控
pub struct QueryEngineMetrics;

impl QueryEngineMetrics {
    pub fn record_query_execution(
        duration: Duration,
        rows: usize,
        success: bool,
    ) {
        // 查询计数
        if success {
            counter!("query_total", "status" => "success").increment(1);
        } else {
            counter!("query_total", "status" => "error").increment(1);
        }
        
        // 查询延迟
        histogram!("query_duration_seconds").record(duration.as_secs_f64());
        
        // 处理行数
        histogram!("query_rows_processed").record(rows as f64);
        
        // 吞吐量
        let throughput = rows as f64 / duration.as_secs_f64();
        histogram!("query_throughput_rows_per_sec").record(throughput);
    }
    
    pub fn record_cache_stats(hits: u64, misses: u64) {
        gauge!("cache_hit_rate").set(
            hits as f64 / (hits + misses) as f64
        );
    }
}
```

---

## 总结

### 🎯 DataFusion 最佳实践

```text
✅ 查询优化
   - 启用谓词下推
   - 启用投影下推
   - 使用分区剪枝
   - 充分利用统计信息

✅ 性能调优
   - 合理设置并行度
   - 优化批处理大小
   - 使用向量化执行
   - 配置内存限制

✅ 数据建模
   - 使用 Parquet 格式
   - 合理分区策略
   - 创建物化视图
   - 收集统计信息

✅ 生产部署
   - 容器化部署
   - 资源限制
   - 监控指标
   - 故障恢复
```

---

**文档版本**: v1.0  
**创建日期**: 2025年10月10日  
**维护者**: OTLP Rust 团队  
**许可证**: MIT OR Apache-2.0

---

[🏠 返回主目录](../README.md) | [⬅️ Arrow 优化](./02_Arrow_Rust_1.90_最新优化实践.md)
