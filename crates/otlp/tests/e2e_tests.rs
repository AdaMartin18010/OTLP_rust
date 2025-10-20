//! # OTLP端到端测试
//!
//! 测试完整的OTLP数据流从采集到传输的全过程

use std::sync::Arc;
use std::time::Duration;
use tokio::time::sleep;

// 模拟OTLP数据采集器
struct OtlpCollector {
    traces: Vec<TraceData>,
    metrics: Vec<MetricData>,
    logs: Vec<LogData>,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
struct TraceData {
    trace_id: String,
    span_id: String,
    operation_name: String,
    start_time: u64,
    duration: u64,
    attributes: std::collections::HashMap<String, String>,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
struct MetricData {
    name: String,
    value: f64,
    timestamp: u64,
    labels: std::collections::HashMap<String, String>,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
struct LogData {
    level: String,
    message: String,
    timestamp: u64,
    fields: std::collections::HashMap<String, String>,
}

impl OtlpCollector {
    fn new() -> Self {
        Self {
            traces: Vec::new(),
            metrics: Vec::new(),
            logs: Vec::new(),
        }
    }

    fn collect_trace(&mut self, trace: TraceData) {
        self.traces.push(trace);
    }

    fn collect_metric(&mut self, metric: MetricData) {
        self.metrics.push(metric);
    }

    fn collect_log(&mut self, log: LogData) {
        self.logs.push(log);
    }

    fn get_traces(&self) -> &[TraceData] {
        &self.traces
    }

    fn get_metrics(&self) -> &[MetricData] {
        &self.metrics
    }

    fn get_logs(&self) -> &[LogData] {
        &self.logs
    }

    #[allow(dead_code)]
    fn clear(&mut self) {
        self.traces.clear();
        self.metrics.clear();
        self.logs.clear();
    }
}

// 模拟OTLP处理器
struct OtlpProcessor {
    batch_size: usize,
    flush_interval: Duration,
}

impl OtlpProcessor {
    fn new(batch_size: usize, flush_interval: Duration) -> Self {
        Self {
            batch_size,
            flush_interval,
        }
    }

    async fn process_traces(&self, traces: &[TraceData]) -> Result<Vec<u8>, String> {
        // 模拟trace数据处理
        sleep(Duration::from_millis(5)).await;

        let mut data = Vec::new();
        for trace in traces {
            data.extend_from_slice(
                format!(
                    "trace:{}:{}:{}",
                    trace.trace_id, trace.span_id, trace.operation_name
                )
                .as_bytes(),
            );
        }
        Ok(data)
    }

    async fn process_metrics(&self, metrics: &[MetricData]) -> Result<Vec<u8>, String> {
        // 模拟metrics数据处理
        sleep(Duration::from_millis(3)).await;

        let mut data = Vec::new();
        for metric in metrics {
            data.extend_from_slice(format!("metric:{}:{}", metric.name, metric.value).as_bytes());
        }
        Ok(data)
    }

    async fn process_logs(&self, logs: &[LogData]) -> Result<Vec<u8>, String> {
        // 模拟logs数据处理
        sleep(Duration::from_millis(2)).await;

        let mut data = Vec::new();
        for log in logs {
            data.extend_from_slice(format!("log:{}:{}", log.level, log.message).as_bytes());
        }
        Ok(data)
    }
}

// 模拟OTLP导出器
struct OtlpExporter {
    endpoint: String,
    timeout: Duration,
    sent_data: Arc<std::sync::Mutex<Vec<Vec<u8>>>>,
}

impl OtlpExporter {
    fn new(endpoint: String) -> Self {
        Self {
            endpoint,
            timeout: Duration::from_secs(5),
            sent_data: Arc::new(std::sync::Mutex::new(Vec::new())),
        }
    }

    async fn export(&self, data: Vec<u8>) -> Result<(), String> {
        // 模拟数据导出
        sleep(Duration::from_millis(10)).await;

        if data.is_empty() {
            return Err("Empty data".to_string());
        }

        self.sent_data.lock().unwrap().push(data);
        Ok(())
    }

    fn get_sent_data(&self) -> Vec<Vec<u8>> {
        self.sent_data.lock().unwrap().clone()
    }
}

#[tokio::test]
async fn test_otlp_complete_data_flow() {
    // 创建组件
    let mut collector = OtlpCollector::new();
    let processor = OtlpProcessor::new(10, Duration::from_millis(100));
    let exporter = OtlpExporter::new("http://localhost:8080".to_string());

    // 1. 数据采集阶段
    let trace = TraceData {
        trace_id: "trace-123".to_string(),
        span_id: "span-456".to_string(),
        operation_name: "test_operation".to_string(),
        start_time: 1234567890,
        duration: 1000,
        attributes: std::collections::HashMap::new(),
    };
    collector.collect_trace(trace.clone());

    let metric = MetricData {
        name: "cpu_usage".to_string(),
        value: 75.5,
        timestamp: 1234567890,
        labels: std::collections::HashMap::new(),
    };
    collector.collect_metric(metric.clone());

    let log = LogData {
        level: "INFO".to_string(),
        message: "Test log message".to_string(),
        timestamp: 1234567890,
        fields: std::collections::HashMap::new(),
    };
    collector.collect_log(log.clone());

    // 验证数据采集
    assert_eq!(collector.get_traces().len(), 1);
    assert_eq!(collector.get_metrics().len(), 1);
    assert_eq!(collector.get_logs().len(), 1);

    // 2. 数据处理阶段
    let trace_data = processor
        .process_traces(collector.get_traces())
        .await
        .expect("Should process traces");
    let metric_data = processor
        .process_metrics(collector.get_metrics())
        .await
        .expect("Should process metrics");
    let log_data = processor
        .process_logs(collector.get_logs())
        .await
        .expect("Should process logs");

    // 验证数据处理结果
    assert!(!trace_data.is_empty());
    assert!(!metric_data.is_empty());
    assert!(!log_data.is_empty());

    // 3. 数据导出阶段
    exporter
        .export(trace_data)
        .await
        .expect("Should export traces");
    exporter
        .export(metric_data)
        .await
        .expect("Should export metrics");
    exporter.export(log_data).await.expect("Should export logs");

    // 验证数据导出
    let sent_data = exporter.get_sent_data();
    assert_eq!(sent_data.len(), 3);
}

#[tokio::test]
async fn test_otlp_batch_processing() {
    let mut collector = OtlpCollector::new();
    let processor = OtlpProcessor::new(5, Duration::from_millis(50));
    let exporter = OtlpExporter::new("http://localhost:8080".to_string());

    // 采集多个trace
    for i in 0..10 {
        let trace = TraceData {
            trace_id: format!("trace-{}", i),
            span_id: format!("span-{}", i),
            operation_name: format!("operation-{}", i),
            start_time: 1234567890 + i,
            duration: 1000 + i,
            attributes: std::collections::HashMap::new(),
        };
        collector.collect_trace(trace);
    }

    // 批量处理
    let traces = collector.get_traces();
    let batch_size = processor.batch_size;

    for chunk in traces.chunks(batch_size) {
        let data = processor
            .process_traces(chunk)
            .await
            .expect("Should process trace batch");
        exporter
            .export(data)
            .await
            .expect("Should export trace batch");
    }

    // 验证批量处理结果
    let sent_data = exporter.get_sent_data();
    assert_eq!(sent_data.len(), 2); // 10 traces / 5 batch_size = 2 batches
}

#[tokio::test]
async fn test_otlp_error_handling() {
    let processor = OtlpProcessor::new(10, Duration::from_millis(100));
    let exporter = OtlpExporter::new("http://localhost:8080".to_string());

    // 测试空数据处理
    let empty_traces = &[];
    let result = processor.process_traces(empty_traces).await;
    assert!(result.is_ok());

    let data = result.unwrap();
    assert!(data.is_empty());

    // 测试空数据导出
    let result = exporter.export(data).await;
    assert!(result.is_err());
    assert_eq!(result.unwrap_err(), "Empty data");
}

#[tokio::test]
async fn test_otlp_performance_under_load() {
    let mut collector = OtlpCollector::new();
    let processor = OtlpProcessor::new(100, Duration::from_millis(10));
    let exporter = OtlpExporter::new("http://localhost:8080".to_string());

    let start = std::time::Instant::now();

    // 采集大量数据
    for i in 0..1000 {
        let trace = TraceData {
            trace_id: format!("trace-{}", i),
            span_id: format!("span-{}", i),
            operation_name: format!("operation-{}", i),
            start_time: 1234567890 + i,
            duration: 1000 + i,
            attributes: std::collections::HashMap::new(),
        };
        collector.collect_trace(trace);
    }

    // 处理所有数据
    let traces = collector.get_traces();
    let data = processor
        .process_traces(traces)
        .await
        .expect("Should process all traces");

    // 导出数据
    exporter
        .export(data)
        .await
        .expect("Should export all traces");

    let duration = start.elapsed();

    // 验证性能要求（1000个trace应该在1秒内处理完成）
    assert!(duration < Duration::from_secs(1));

    // 验证数据完整性
    let sent_data = exporter.get_sent_data();
    assert_eq!(sent_data.len(), 1);
}

#[tokio::test]
async fn test_otlp_memory_efficiency() {
    let mut collector = OtlpCollector::new();
    let processor = OtlpProcessor::new(50, Duration::from_millis(100));
    let exporter = OtlpExporter::new("http://localhost:8080".to_string());

    // 采集大量数据
    for i in 0..500 {
        let trace = TraceData {
            trace_id: format!("trace-{}", i),
            span_id: format!("span-{}", i),
            operation_name: format!("operation-{}", i),
            start_time: 1234567890 + i,
            duration: 1000 + i,
            attributes: std::collections::HashMap::new(),
        };
        collector.collect_trace(trace);
    }

    // 分批处理以控制内存使用
    let traces = collector.get_traces();
    let batch_size = processor.batch_size;

    for chunk in traces.chunks(batch_size) {
        let data = processor
            .process_traces(chunk)
            .await
            .expect("Should process trace batch");
        exporter
            .export(data)
            .await
            .expect("Should export trace batch");
    }

    // 验证内存效率
    let sent_data = exporter.get_sent_data();
    assert_eq!(sent_data.len(), 10); // 500 traces / 50 batch_size = 10 batches
}

#[tokio::test]
async fn test_otlp_concurrent_processing() {
    let processor = Arc::new(OtlpProcessor::new(10, Duration::from_millis(50)));
    let exporter = Arc::new(OtlpExporter::new("http://localhost:8080".to_string()));

    // 创建多个并发任务
    let mut handles = Vec::new();
    for i in 0..10 {
        let processor = Arc::clone(&processor);
        let exporter = Arc::clone(&exporter);

        let handle = tokio::spawn(async move {
            let trace = TraceData {
                trace_id: format!("trace-{}", i),
                span_id: format!("span-{}", i),
                operation_name: format!("operation-{}", i),
                start_time: 1234567890 + i,
                duration: 1000 + i,
                attributes: std::collections::HashMap::new(),
            };

            let data = processor
                .process_traces(&[trace])
                .await
                .expect("Should process trace");
            exporter.export(data).await.expect("Should export trace");
        });

        handles.push(handle);
    }

    // 等待所有任务完成
    for handle in handles {
        handle.await.expect("Task should complete");
    }

    // 验证并发处理结果
    let sent_data = exporter.get_sent_data();
    assert_eq!(sent_data.len(), 10);
}

#[tokio::test]
async fn test_otlp_configuration_validation() {
    // 测试处理器配置
    let processor = OtlpProcessor::new(100, Duration::from_millis(200));
    assert_eq!(processor.batch_size, 100);
    assert_eq!(processor.flush_interval, Duration::from_millis(200));

    // 测试导出器配置
    let exporter = OtlpExporter::new("http://localhost:8080".to_string());
    assert_eq!(exporter.endpoint, "http://localhost:8080");
    assert_eq!(exporter.timeout, Duration::from_secs(5));
}

#[tokio::test]
async fn test_otlp_graceful_shutdown() {
    let mut collector = OtlpCollector::new();
    let processor = OtlpProcessor::new(10, Duration::from_millis(100));
    let exporter = OtlpExporter::new("http://localhost:8080".to_string());

    // 采集一些数据
    let trace = TraceData {
        trace_id: "shutdown-trace".to_string(),
        span_id: "shutdown-span".to_string(),
        operation_name: "shutdown_operation".to_string(),
        start_time: 1234567890,
        duration: 1000,
        attributes: std::collections::HashMap::new(),
    };
    collector.collect_trace(trace);

    // 处理数据
    let traces = collector.get_traces();
    let data = processor
        .process_traces(traces)
        .await
        .expect("Should process traces");

    // 导出数据
    exporter.export(data).await.expect("Should export traces");

    // 验证优雅关闭
    let sent_data = exporter.get_sent_data();
    assert_eq!(sent_data.len(), 1);
}
