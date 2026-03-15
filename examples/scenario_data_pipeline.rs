//! # 数据管道场景示例
//!
//! 展示在数据处理管道中使用 OTLP Rust：
//! - 数据采集 (Data Collection)
//! - 数据转换 (Data Transformation)
//! - 数据验证 (Data Validation)
//! - 数据加载 (Data Loading)
//! - 错误处理和重试

use anyhow::Result;
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::{mpsc, Semaphore};
use tokio::time::{sleep, Duration, Instant};

/// ============================================
/// 遥测和监控基础设施
/// ============================================

/// 指标收集器
#[derive(Clone)]
pub struct MetricsCollector {
    sender: mpsc::UnboundedSender<MetricEvent>,
}

#[derive(Clone, Debug)]
pub enum MetricEvent {
    Counter { name: String, value: u64, tags: HashMap<String, String> },
    Gauge { name: String, value: f64, tags: HashMap<String, String> },
    Histogram { name: String, value: f64, tags: HashMap<String, String> },
    Timer { name: String, duration_ms: u64, tags: HashMap<String, String> },
}

impl MetricsCollector {
    pub fn new() -> (Self, mpsc::UnboundedReceiver<MetricEvent>) {
        let (sender, receiver) = mpsc::unbounded_channel();
        (Self { sender }, receiver)
    }

    pub fn counter(&self, name: &str, value: u64, tags: HashMap<String, String>) {
        let _ = self.sender.send(MetricEvent::Counter {
            name: name.to_string(),
            value,
            tags,
        });
    }

    pub fn gauge(&self, name: &str, value: f64, tags: HashMap<String, String>) {
        let _ = self.sender.send(MetricEvent::Gauge {
            name: name.to_string(),
            value,
            tags,
        });
    }

    pub fn timer(&self, name: &str, duration_ms: u64, tags: HashMap<String, String>) {
        let _ = self.sender.send(MetricEvent::Timer {
            name: name.to_string(),
            duration_ms,
            tags,
        });
    }
}

/// 追踪跨度
pub struct Span {
    pub name: String,
    pub start_time: Instant,
    pub tags: HashMap<String, String>,
}

impl Span {
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            start_time: Instant::now(),
            tags: HashMap::new(),
        }
    }

    pub fn tag(mut self, key: &str, value: &str) -> Self {
        self.tags.insert(key.to_string(), value.to_string());
        self
    }

    pub fn elapsed_ms(&self) -> u64 {
        self.start_time.elapsed().as_millis() as u64
    }
}

/// ============================================
/// 数据管道组件
/// ============================================

/// 数据记录
#[derive(Clone, Debug)]
pub struct DataRecord {
    pub id: String,
    pub payload: HashMap<String, serde_json::Value>,
    pub source: String,
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub metadata: HashMap<String, String>,
}

/// 处理结果
#[derive(Clone, Debug)]
pub enum ProcessingResult {
    Success(DataRecord),
    Filtered { reason: String, record: DataRecord },
    Error { error: String, record: DataRecord },
    Retryable { error: String, record: DataRecord, attempt: u32 },
}

/// 数据采集器
pub struct DataCollector {
    metrics: MetricsCollector,
    source_name: String,
}

impl DataCollector {
    pub fn new(metrics: MetricsCollector, source: &str) -> Self {
        Self {
            metrics,
            source_name: source.to_string(),
        }
    }

    pub async fn collect(&self, batch_size: usize) -> Vec<DataRecord> {
        let span = Span::new("data_collection").tag("source", &self.source_name);

        // 模拟数据采集
        sleep(Duration::from_millis(50)).await;

        let records: Vec<DataRecord> = (0..batch_size)
            .map(|i| DataRecord {
                id: format!("record_{}_{}", self.source_name, i),
                payload: {
                    let mut map = HashMap::new();
                    map.insert(
                        "value".to_string(),
                        serde_json::json!(rand::random::<f64>() * 100.0),
                    );
                    map.insert("index".to_string(), serde_json::json!(i));
                    map
                },
                source: self.source_name.clone(),
                timestamp: chrono::Utc::now(),
                metadata: {
                    let mut map = HashMap::new();
                    map.insert("collection_id".to_string(), format!("batch_{}", i));
                    map
                },
            })
            .collect();

        let mut tags = HashMap::new();
        tags.insert("source".to_string(), self.source_name.clone());
        self.metrics.counter("records.collected", records.len() as u64, tags.clone());
        self.metrics.timer("collection.duration", span.elapsed_ms(), tags);

        records
    }
}

/// 数据转换器
pub struct DataTransformer {
    metrics: MetricsCollector,
    transformations: Vec<Box<dyn Fn(&mut DataRecord) -> Result<()> + Send + Sync>>,
}

impl DataTransformer {
    pub fn new(metrics: MetricsCollector) -> Self {
        Self {
            metrics,
            transformations: Vec::new(),
        }
    }

    pub fn add_transformation<F>(&mut self, f: F)
    where
        F: Fn(&mut DataRecord) -> Result<()> + Send + Sync + 'static,
    {
        self.transformations.push(Box::new(f));
    }

    pub async fn transform(&self, mut record: DataRecord) -> ProcessingResult {
        let span = Span::new("data_transformation").tag("record_id", &record.id);

        for (idx, transform) in self.transformations.iter().enumerate() {
            if let Err(e) = transform(&mut record) {
                let mut tags = HashMap::new();
                tags.insert("stage".to_string(), format!("transform_{}", idx));
                tags.insert("error_type".to_string(), "transformation_failed".to_string());
                self.metrics.counter("records.transform_failed", 1, tags);

                return ProcessingResult::Error {
                    error: format!("Transformation {} failed: {}", idx, e),
                    record,
                };
            }
        }

        let mut tags = HashMap::new();
        tags.insert("record_id".to_string(), record.id.clone());
        self.metrics.timer("transformation.duration", span.elapsed_ms(), tags);

        ProcessingResult::Success(record)
    }
}

/// 数据验证器
pub struct DataValidator {
    metrics: MetricsCollector,
    rules: Vec<Box<dyn Fn(&DataRecord) -> Result<()> + Send + Sync>>,
}

impl DataValidator {
    pub fn new(metrics: MetricsCollector) -> Self {
        Self {
            metrics,
            rules: Vec::new(),
        }
    }

    pub fn add_rule<F>(&mut self, f: F)
    where
        F: Fn(&DataRecord) -> Result<()> + Send + Sync + 'static,
    {
        self.rules.push(Box::new(f));
    }

    pub async fn validate(&self, record: &DataRecord) -> ProcessingResult {
        let span = Span::new("data_validation").tag("record_id", &record.id);

        for (idx, rule) in self.rules.iter().enumerate() {
            if let Err(e) = rule(record) {
                let mut tags = HashMap::new();
                tags.insert("rule_index".to_string(), idx.to_string());
                tags.insert("validation_error".to_string(), e.to_string());
                self.metrics.counter("records.validation_failed", 1, tags);

                // 模拟某些错误是可重试的
                if e.to_string().contains("timeout") || e.to_string().contains("network") {
                    return ProcessingResult::Retryable {
                        error: e.to_string(),
                        record: record.clone(),
                        attempt: 1,
                    };
                }

                return ProcessingResult::Filtered {
                    reason: format!("Validation rule {} failed: {}", idx, e),
                    record: record.clone(),
                };
            }
        }

        let mut tags = HashMap::new();
        tags.insert("record_id".to_string(), record.id.clone());
        self.metrics.timer("validation.duration", span.elapsed_ms(), tags);

        ProcessingResult::Success(record.clone())
    }
}

/// 数据加载器
pub struct DataLoader {
    metrics: MetricsCollector,
    destination: String,
    semaphore: Arc<Semaphore>,
}

impl DataLoader {
    pub fn new(metrics: MetricsCollector, destination: &str, max_concurrent: usize) -> Self {
        Self {
            metrics,
            destination: destination.to_string(),
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
        }
    }

    pub async fn load(&self, record: DataRecord) -> ProcessingResult {
        let _permit = self.semaphore.acquire().await.unwrap();
        let span = Span::new("data_loading")
            .tag("record_id", &record.id)
            .tag("destination", &self.destination);

        // 模拟加载延迟（偶尔失败）
        sleep(Duration::from_millis(20)).await;

        // 模拟 5% 的失败率
        if rand::random::<f32>() < 0.05 {
            let mut tags = HashMap::new();
            tags.insert("destination".to_string(), self.destination.clone());
            self.metrics.counter("records.load_failed", 1, tags);

            return ProcessingResult::Retryable {
                error: "Network timeout during load".to_string(),
                record,
                attempt: 1,
            };
        }

        let mut tags = HashMap::new();
        tags.insert("destination".to_string(), self.destination.clone());
        self.metrics.counter("records.loaded", 1, tags.clone());
        self.metrics.timer("load.duration", span.elapsed_ms(), tags);

        ProcessingResult::Success(record)
    }
}

/// 重试处理器
pub struct RetryHandler {
    metrics: MetricsCollector,
    max_retries: u32,
    base_delay_ms: u64,
}

impl RetryHandler {
    pub fn new(metrics: MetricsCollector, max_retries: u32, base_delay_ms: u64) -> Self {
        Self {
            metrics,
            max_retries,
            base_delay_ms,
        }
    }

    pub async fn execute_with_retry<F, Fut>(
        &self,
        operation: F,
        record: DataRecord,
    ) -> ProcessingResult
    where
        F: Fn(DataRecord) -> Fut + Send + Sync,
        Fut: std::future::Future<Output = ProcessingResult> + Send,
    {
        let mut last_result = ProcessingResult::Error {
            error: "Not executed".to_string(),
            record: record.clone(),
        };

        for attempt in 0..=self.max_retries {
            let span = Span::new("retry_attempt")
                .tag("record_id", &record.id)
                .tag("attempt", &attempt.to_string());

            let result = operation(record.clone()).await;

            match &result {
                ProcessingResult::Success(_) => {
                    if attempt > 0 {
                        let mut tags = HashMap::new();
                        tags.insert("attempt".to_string(), attempt.to_string());
                        self.metrics.counter("records.retry_success", 1, tags);
                    }
                    return result;
                }
                ProcessingResult::Retryable { error, record: _, attempt: _ } => {
                    let mut tags = HashMap::new();
                    tags.insert("attempt".to_string(), attempt.to_string());
                    tags.insert("error".to_string(), error.clone());
                    self.metrics.counter("records.retry_attempt", 1, tags);

                    if attempt < self.max_retries {
                        // 指数退避
                        let delay = self.base_delay_ms * (2_u64.pow(attempt));
                        sleep(Duration::from_millis(delay)).await;
                        last_result = result;
                    } else {
                        let mut tags = HashMap::new();
                        tags.insert("max_attempts".to_string(), self.max_retries.to_string());
                        self.metrics.counter("records.retry_exhausted", 1, tags);
                        return ProcessingResult::Error {
                            error: format!("Max retries exceeded: {}", error),
                            record: record.clone(),
                        };
                    }
                }
                ProcessingResult::Error { .. } | ProcessingResult::Filtered { .. } => {
                    return result;
                }
            }

            let mut tags = HashMap::new();
            tags.insert("record_id".to_string(), record.id.clone());
            self.metrics.timer("retry_attempt.duration", span.elapsed_ms(), tags);
        }

        last_result
    }
}

/// ============================================
/// 完整数据管道
/// ============================================

pub struct DataPipeline {
    collector: DataCollector,
    transformer: DataTransformer,
    validator: DataValidator,
    loader: DataLoader,
    retry_handler: RetryHandler,
    metrics: MetricsCollector,
}

impl DataPipeline {
    pub fn new(metrics: MetricsCollector) -> Self {
        let collector = DataCollector::new(metrics.clone(), "api_server");
        let mut transformer = DataTransformer::new(metrics.clone());
        let mut validator = DataValidator::new(metrics.clone());
        let loader = DataLoader::new(metrics.clone(), "data_warehouse", 10);
        let retry_handler = RetryHandler::new(metrics.clone(), 3, 100);

        // 添加转换规则
        transformer.add_transformation(|record| {
            // 添加处理时间戳
            record.metadata.insert(
                "processed_at".to_string(),
                chrono::Utc::now().to_rfc3339(),
            );
            Ok(())
        });

        transformer.add_transformation(|record| {
            // 标准化字段名称
            if let Some(value) = record.payload.remove("VALUE") {
                record.payload.insert("value".to_string(), value);
            }
            Ok(())
        });

        // 添加验证规则
        validator.add_rule(|record| {
            // 验证必需字段
            if !record.payload.contains_key("value") {
                return Err(anyhow::anyhow!("Missing required field: value"));
            }
            Ok(())
        });

        validator.add_rule(|record| {
            // 验证数值范围
            if let Some(val) = record.payload.get("value") {
                if let Some(num) = val.as_f64() {
                    if num < 0.0 || num > 1000.0 {
                        return Err(anyhow::anyhow!("Value out of range: {}", num));
                    }
                }
            }
            Ok(())
        });

        validator.add_rule(|record| {
            // 模拟随机网络错误（可重试）
            if rand::random::<f32>() < 0.02 {
                return Err(anyhow::anyhow!("network timeout"));
            }
            Ok(())
        });

        Self {
            collector,
            transformer,
            validator,
            loader,
            retry_handler,
            metrics,
        }
    }

    pub async fn process_batch(&self, batch_size: usize) -> PipelineMetrics {
        let start = Instant::now();
        let mut stats = PipelineStats::new();

        // 1. 采集数据
        let records = self.collector.collect(batch_size).await;
        stats.collected = records.len();

        // 2. 处理每条记录
        for record in records {
            let result = self.process_record(record).await;
            match result {
                ProcessingResult::Success(_) => stats.succeeded += 1,
                ProcessingResult::Filtered { reason, .. } => {
                    stats.filtered += 1;
                    stats.filter_reasons.push(reason);
                }
                ProcessingResult::Error { error, .. } => {
                    stats.failed += 1;
                    stats.errors.push(error);
                }
                ProcessingResult::Retryable { .. } => {
                    // 不应该发生，重试应该在 process_record 内部处理
                    stats.failed += 1;
                }
            }
        }

        let duration_ms = start.elapsed().as_millis() as u64;

        // 记录整体指标
        let mut tags = HashMap::new();
        tags.insert("batch_size".to_string(), batch_size.to_string());
        self.metrics.timer("pipeline.batch_duration", duration_ms, tags.clone());
        self.metrics.gauge("pipeline.throughput", batch_size as f64 / (duration_ms as f64 / 1000.0), tags);

        PipelineMetrics {
            duration_ms,
            stats,
        }
    }

    async fn process_record(&self, record: DataRecord) -> ProcessingResult {
        // 转换 -> 验证 -> 加载（带重试）
        let transformed = self.transformer.transform(record).await;

        let validated = match transformed {
            ProcessingResult::Success(r) => self.validator.validate(&r).await,
            other => return other,
        };

        match validated {
            ProcessingResult::Success(r) => {
                self.retry_handler
                    .execute_with_retry(|rec| self.loader.load(rec), r)
                    .await
            }
            ProcessingResult::Retryable { record, .. } => {
                // 验证失败但可重试
                self.retry_handler
                    .execute_with_retry(|rec| self.validator.validate(&rec), record)
                    .await
            }
            other => other,
        }
    }
}

#[derive(Default)]
pub struct PipelineStats {
    pub collected: usize,
    pub succeeded: usize,
    pub filtered: usize,
    pub failed: usize,
    pub filter_reasons: Vec<String>,
    pub errors: Vec<String>,
}

impl PipelineStats {
    fn new() -> Self {
        Self::default()
    }
}

pub struct PipelineMetrics {
    pub duration_ms: u64,
    pub stats: PipelineStats,
}

/// ============================================
/// 演示主程序
/// ============================================

#[tokio::main]
async fn main() -> Result<()> {
    println!("=== 数据管道遥测示例 ===\n");

    // 创建指标收集器
    let (metrics, mut receiver) = MetricsCollector::new();

    // 启动指标处理任务
    let metrics_handle = tokio::spawn(async move {
        let mut counters: HashMap<String, u64> = HashMap::new();
        let mut timers: HashMap<String, Vec<u64>> = HashMap::new();

        while let Some(event) = receiver.recv().await {
            match event {
                MetricEvent::Counter { name, value, tags } => {
                    let key = format!("{}:{:?}", name, tags);
                    *counters.entry(key.clone()).or_insert(0) += value;
                    println!("[METRIC] Counter {} += {} (tags: {:?})", name, value, tags);
                }
                MetricEvent::Timer { name, duration_ms, tags } => {
                    timers.entry(name.clone()).or_default().push(duration_ms);
                    println!("[METRIC] Timer {} = {}ms (tags: {:?})", name, duration_ms, tags);
                }
                MetricEvent::Gauge { name, value, tags } => {
                    println!("[METRIC] Gauge {} = {} (tags: {:?})", name, value, tags);
                }
                MetricEvent::Histogram { name, value, tags } => {
                    println!("[METRIC] Histogram {} = {} (tags: {:?})", name, value, tags);
                }
            }
        }

        (counters, timers)
    });

    // 创建并运行管道
    let pipeline = DataPipeline::new(metrics.clone());

    println!("--- 执行批处理 #1 (100条记录) ---");
    let metrics1 = pipeline.process_batch(100).await;
    print_metrics(&metrics1);

    sleep(Duration::from_millis(500)).await;

    println!("\n--- 执行批处理 #2 (50条记录) ---");
    let metrics2 = pipeline.process_batch(50).await;
    print_metrics(&metrics2);

    sleep(Duration::from_millis(500)).await;

    println!("\n--- 执行批处理 #3 (200条记录) ---");
    let metrics3 = pipeline.process_batch(200).await;
    print_metrics(&metrics3);

    // 关闭管道并等待指标处理完成
    drop(pipeline);
    drop(metrics);

    println!("\n--- 最终指标统计 ---");
    match metrics_handle.await {
        Ok((counters, timers)) => {
            println!("\n计数器汇总:");
            for (key, value) in counters.iter().take(10) {
                println!("  {}: {}", key, value);
            }

            println!("\n计时器汇总:");
            for (name, values) in timers.iter().take(5) {
                let avg = if !values.is_empty() {
                    values.iter().sum::<u64>() / values.len() as u64
                } else {
                    0
                };
                println!("  {}: 平均 {}ms (样本数: {})", name, avg, values.len());
            }
        }
        Err(e) => println!("指标处理器错误: {}", e),
    }

    println!("\n=== 示例完成 ===");
    Ok(())
}

fn print_metrics(metrics: &PipelineMetrics) {
    let stats = &metrics.stats;
    println!("批处理完成:");
    println!("  耗时: {}ms", metrics.duration_ms);
    println!("  采集: {} 条", stats.collected);
    println!("  成功: {} 条", stats.succeeded);
    println!("  过滤: {} 条", stats.filtered);
    println!("  失败: {} 条", stats.failed);

    if !stats.filter_reasons.is_empty() {
        println!("  过滤原因 (前3条):");
        for reason in stats.filter_reasons.iter().take(3) {
            println!("    - {}", reason);
        }
    }

    if !stats.errors.is_empty() {
        println!("  错误 (前3条):");
        for error in stats.errors.iter().take(3) {
            println!("    - {}", error);
        }
    }
}
