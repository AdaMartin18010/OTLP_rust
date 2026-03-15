//! # 云提供商集成示例
//!
//! 展示与主流云平台的集成：
//! - AWS (CloudWatch, X-Ray)
//! - Azure (Application Insights, Monitor)
//! - GCP (Cloud Monitoring, Cloud Trace)
//! - 阿里云 (ARMS, 日志服务)

use anyhow::Result;
use std::collections::HashMap;

/// ============================================
/// 云提供商抽象接口
/// ============================================

#[async_trait::async_trait]
pub trait CloudTelemetryBackend: Send + Sync {
    async fn export_traces(&self, traces: &[TraceData]) -> Result<()>;
    async fn export_metrics(&self, metrics: &[MetricData]) -> Result<()>;
    async fn export_logs(&self, logs: &[LogData]) -> Result<()>;
    fn get_name(&self) -> &str;
}

#[derive(Clone, Debug)]
pub struct TraceData {
    pub trace_id: String,
    pub spans: Vec<SpanData>,
}

#[derive(Clone, Debug)]
pub struct SpanData {
    pub span_id: String,
    pub parent_id: Option<String>,
    pub name: String,
    pub start_time: u64,
    pub end_time: u64,
    pub attributes: HashMap<String, String>,
}

#[derive(Clone, Debug)]
pub struct MetricData {
    pub name: String,
    pub value: f64,
    pub timestamp: u64,
    pub dimensions: HashMap<String, String>,
}

#[derive(Clone, Debug)]
pub struct LogData {
    pub timestamp: u64,
    pub level: String,
    pub message: String,
    pub fields: HashMap<String, String>,
}

/// ============================================
/// AWS 集成 (CloudWatch & X-Ray)
/// ============================================

pub struct AWSIntegration {
    region: String,
    access_key_id: String,
    secret_access_key: String,
}

impl AWSIntegration {
    pub fn new(region: &str, access_key: &str, secret_key: &str) -> Self {
        Self {
            region: region.to_string(),
            access_key_id: access_key.to_string(),
            secret_access_key: secret_key.to_string(),
        }
    }

    /// 将 OTLP 格式转换为 X-Ray 格式
    fn convert_to_xray_format(&self, trace: &TraceData) -> serde_json::Value {
        let segments: Vec<_> = trace
            .spans
            .iter()
            .map(|span| {
                serde_json::json!({
                    "id": span.span_id,
                    "trace_id": format!("1-{}-{}", 
                        span.start_time / 1_000_000, 
                        trace.trace_id.replace("-", "")
                    ),
                    "parent_id": span.parent_id,
                    "name": span.name,
                    "start_time": span.start_time as f64 / 1_000_000.0,
                    "end_time": span.end_time as f64 / 1_000_000.0,
                    "annotations": span.attributes,
                })
            })
            .collect();

        serde_json::json!({ "trace_id": trace.trace_id, "segments": segments })
    }

    /// 将指标转换为 CloudWatch 格式
    fn convert_to_cloudwatch_format(&self, metric: &MetricData) -> serde_json::Value {
        let dimensions: Vec<_> = metric
            .dimensions
            .iter()
            .map(|(k, v)| {
                serde_json::json!({
                    "Name": k,
                    "Value": v
                })
            })
            .collect();

        serde_json::json!({
            "Namespace": "OTLP/Application",
            "MetricData": [{
                "MetricName": metric.name,
                "Value": metric.value,
                "Timestamp": metric.timestamp,
                "Unit": "Count",
                "Dimensions": dimensions
            }]
        })
    }
}

#[async_trait::async_trait]
impl CloudTelemetryBackend for AWSIntegration {
    async fn export_traces(&self, traces: &[TraceData]) -> Result<()> {
        println!("[AWS X-Ray] Exporting {} traces", traces.len());
        for trace in traces {
            let xray_data = self.convert_to_xray_format(trace);
            // 实际实现中调用 AWS X-Ray API
            println!("  Sending to X-Ray: {}", xray_data["trace_id"]);
        }
        Ok(())
    }

    async fn export_metrics(&self, metrics: &[MetricData]) -> Result<()> {
        println!("[AWS CloudWatch] Exporting {} metrics", metrics.len());
        for metric in metrics {
            let cw_data = self.convert_to_cloudwatch_format(metric);
            println!("  Sending to CloudWatch: {}", metric.name);
        }
        Ok(())
    }

    async fn export_logs(&self, logs: &[LogData]) -> Result<()> {
        println!("[AWS CloudWatch Logs] Exporting {} logs", logs.len());
        for log in logs {
            println!("  [{}/{}] {}", self.region, log.level, log.message);
        }
        Ok(())
    }

    fn get_name(&self) -> &str {
        "AWS"
    }
}

/// ============================================
/// Azure 集成 (Application Insights)
/// ============================================

pub struct AzureIntegration {
    instrumentation_key: String,
    endpoint: String,
}

impl AzureIntegration {
    pub fn new(instrumentation_key: &str) -> Self {
        Self {
            instrumentation_key: instrumentation_key.to_string(),
            endpoint: "https://dc.services.visualstudio.com/v2/track".to_string(),
        }
    }

    /// 转换为 Application Insights 格式
    fn convert_to_app_insights(&self, trace: &TraceData) -> Vec<serde_json::Value> {
        trace
            .spans
            .iter()
            .map(|span| {
                serde_json::json!({
                    "name": "Microsoft.ApplicationInsights.Request",
                    "time": chrono::DateTime::from_timestamp(
                        (span.start_time / 1_000_000) as i64,
                        0
                    ).map(|d| d.to_rfc3339()).unwrap_or_default(),
                    "iKey": self.instrumentation_key,
                    "data": {
                        "baseType": "RequestData",
                        "baseData": {
                            "id": span.span_id,
                            "name": span.name,
                            "duration": format!("{}.{:06}",
                                (span.end_time - span.start_time) / 1_000_000,
                                (span.end_time - span.start_time) % 1_000_000
                            ),
                            "success": true,
                            "properties": span.attributes
                        }
                    }
                })
            })
            .collect()
    }
}

#[async_trait::async_trait]
impl CloudTelemetryBackend for AzureIntegration {
    async fn export_traces(&self, traces: &[TraceData]) -> Result<()> {
        println!("[Azure Application Insights] Exporting {} traces", traces.len());
        for trace in traces {
            let app_insights_data = self.convert_to_app_insights(trace);
            println!("  Sending {} telemetry items", app_insights_data.len());
        }
        Ok(())
    }

    async fn export_metrics(&self, metrics: &[MetricData]) -> Result<()> {
        println!("[Azure Monitor] Exporting {} metrics", metrics.len());
        for metric in metrics {
            println!("  {} = {}", metric.name, metric.value);
        }
        Ok(())
    }

    async fn export_logs(&self, logs: &[LogData]) -> Result<()> {
        println!("[Azure Log Analytics] Exporting {} logs", logs.len());
        for log in logs {
            println!("  [AppInsights] {} - {}", log.level, log.message);
        }
        Ok(())
    }

    fn get_name(&self) -> &str {
        "Azure"
    }
}

/// ============================================
/// GCP 集成 (Cloud Monitoring & Cloud Trace)
/// ============================================

pub struct GCPIntegration {
    project_id: String,
    credentials: String,
}

impl GCPIntegration {
    pub fn new(project_id: &str, credentials: &str) -> Self {
        Self {
            project_id: project_id.to_string(),
            credentials: credentials.to_string(),
        }
    }

    /// 转换为 Cloud Trace 格式
    fn convert_to_cloud_trace(&self, trace: &TraceData) -> serde_json::Value {
        let spans: Vec<_> = trace
            .spans
            .iter()
            .map(|span| {
                serde_json::json!({
                    "name": format!("projects/{}/traces/{}/spans/{}",
                        self.project_id, trace.trace_id, span.span_id),
                    "spanId": span.span_id,
                    "parentSpanId": span.parent_id,
                    "displayName": { "value": span.name },
                    "startTime": format!("{}.{:09}Z",
                        span.start_time / 1_000_000_000,
                        span.start_time % 1_000_000_000),
                    "endTime": format!("{}.{:09}Z",
                        span.end_time / 1_000_000_000,
                        span.end_time % 1_000_000_000),
                    "attributes": {
                        "attributeMap": span.attributes.iter().map(|(k, v)| {
                            (k.clone(), serde_json::json!({ "stringValue": v }))
                        }).collect::<HashMap<_, _>>()
                    }
                })
            })
            .collect();

        serde_json::json!({
            "projectId": self.project_id,
            "traceId": trace.trace_id,
            "spans": spans
        })
    }

    /// 转换为 Cloud Monitoring 格式 (MonitoredResource + TimeSeries)
    fn convert_to_cloud_monitoring(&self, metric: &MetricData) -> serde_json::Value {
        serde_json::json!({
            "metric": {
                "type": format!("custom.googleapis.com/{}", metric.name),
                "labels": metric.dimensions
            },
            "resource": {
                "type": "global",
                "labels": {
                    "project_id": self.project_id.clone()
                }
            },
            "points": [{
                "interval": {
                    "endTime": format!("{}Z", 
                        chrono::DateTime::from_timestamp(
                            (metric.timestamp / 1_000_000) as i64, 0
                        ).map(|d| d.to_rfc3339()).unwrap_or_default()
                    )
                },
                "value": {
                    "doubleValue": metric.value
                }
            }]
        })
    }
}

#[async_trait::async_trait]
impl CloudTelemetryBackend for GCPIntegration {
    async fn export_traces(&self, traces: &[TraceData]) -> Result<()> {
        println!("[GCP Cloud Trace] Exporting {} traces", traces.len());
        for trace in traces {
            let cloud_trace_data = self.convert_to_cloud_trace(trace);
            println!("  Sending to projects/{}/traces", self.project_id);
        }
        Ok(())
    }

    async fn export_metrics(&self, metrics: &[MetricData]) -> Result<()> {
        println!("[GCP Cloud Monitoring] Exporting {} metrics", metrics.len());
        for metric in metrics {
            let monitoring_data = self.convert_to_cloud_monitoring(metric);
            println!("  {} = {}", metric.name, metric.value);
        }
        Ok(())
    }

    async fn export_logs(&self, logs: &[LogData]) -> Result<()> {
        println!("[GCP Cloud Logging] Exporting {} logs", logs.len());
        for log in logs {
            println!("  [projects/{}] {}: {}", self.project_id, log.level, log.message);
        }
        Ok(())
    }

    fn get_name(&self) -> &str {
        "GCP"
    }
}

/// ============================================
/// 阿里云集成 (ARMS & 日志服务)
/// ============================================

pub struct AlibabaCloudIntegration {
    access_key_id: String,
    access_key_secret: String,
    region: String,
}

impl AlibabaCloudIntegration {
    pub fn new(access_key: &str, secret: &str, region: &str) -> Self {
        Self {
            access_key_id: access_key.to_string(),
            access_key_secret: secret.to_string(),
            region: region.to_string(),
        }
    }

    /// 转换为 ARMS 调用链格式
    fn convert_to_arms_format(&self, trace: &TraceData) -> serde_json::Value {
        serde_json::json!({
            "traceId": trace.trace_id,
            "serviceName": "rust-service",
            "spans": trace.spans.iter().map(|span| {
                serde_json::json!({
                    "spanId": span.span_id,
                    "parentSpanId": span.parent_id,
                    "operationName": span.name,
                    "startTime": span.start_time,
                    "duration": span.end_time - span.start_time,
                    "tags": span.attributes
                })
            }).collect::<Vec<_>>()
        })
    }

    /// 转换为 SLS (日志服务) 格式
    fn convert_to_sls_format(&self, log: &LogData) -> serde_json::Value {
        serde_json::json!({
            "__source__": "rust-application",
            "__time__": log.timestamp / 1_000_000,
            "level": log.level,
            "message": log.message,
            "fields": log.fields
        })
    }
}

#[async_trait::async_trait]
impl CloudTelemetryBackend for AlibabaCloudIntegration {
    async fn export_traces(&self, traces: &[TraceData]) -> Result<()> {
        println!("[阿里云 ARMS] Exporting {} traces", traces.len());
        for trace in traces {
            let arms_data = self.convert_to_arms_format(trace);
            println!("  Sending to ARMS in region {}", self.region);
        }
        Ok(())
    }

    async fn export_metrics(&self, metrics: &[MetricData]) -> Result<()> {
        println!("[阿里云云监控] Exporting {} metrics", metrics.len());
        for metric in metrics {
            println!("  {} = {}", metric.name, metric.value);
        }
        Ok(())
    }

    async fn export_logs(&self, logs: &[LogData]) -> Result<()> {
        println!("[阿里云 SLS] Exporting {} logs", logs.len());
        for log in logs {
            let sls_data = self.convert_to_sls_format(log);
            println!("  [SLS] {} - {}", log.level, log.message);
        }
        Ok(())
    }

    fn get_name(&self) -> &str {
        "Alibaba Cloud"
    }
}

/// ============================================
/// 多云导出器 - 支持同时导出到多个云平台
/// ============================================

pub struct MultiCloudExporter {
    backends: Vec<Box<dyn CloudTelemetryBackend>>,
}

impl MultiCloudExporter {
    pub fn new() -> Self {
        Self { backends: Vec::new() }
    }

    pub fn add_backend(&mut self, backend: Box<dyn CloudTelemetryBackend>) {
        self.backends.push(backend);
    }

    pub async fn export_traces(&self, traces: &[TraceData]) -> Vec<Result<()>> {
        let mut results = Vec::new();
        for backend in &self.backends {
            let result = backend.export_traces(traces).await;
            results.push(result);
        }
        results
    }

    pub async fn export_metrics(&self, metrics: &[MetricData]) -> Vec<Result<()>> {
        let mut results = Vec::new();
        for backend in &self.backends {
            let result = backend.export_metrics(metrics).await;
            results.push(result);
        }
        results
    }

    pub fn list_backends(&self) -> Vec<&str> {
        self.backends.iter().map(|b| b.get_name()).collect()
    }
}

/// ============================================
/// 演示主程序
/// ============================================

#[tokio::main]
async fn main() -> Result<()> {
    println!("=== 云提供商集成示例 ===\n");

    // 创建多云导出器
    let mut exporter = MultiCloudExporter::new();

    // 添加 AWS 后端
    exporter.add_backend(Box::new(AWSIntegration::new(
        "us-west-2",
        "AKIAIOSFODNN7EXAMPLE",
        "wJalrXUtnFEMI/K7MDENG/bPxRfiCYEXAMPLEKEY",
    )));

    // 添加 Azure 后端
    exporter.add_backend(Box::new(AzureIntegration::new(
        "00000000-0000-0000-0000-000000000000",
    )));

    // 添加 GCP 后端
    exporter.add_backend(Box::new(GCPIntegration::new(
        "my-gcp-project",
        "{ \"type\": \"service_account\" }",
    )));

    // 添加阿里云后端
    exporter.add_backend(Box::new(AlibabaCloudIntegration::new(
        "LTAI5t8Z3y8Y7Z7Z7Z7Z7Z7Z",
        "your-access-key-secret",
        "cn-hangzhou",
    )));

    println!("配置的后端:");
    for backend in exporter.list_backends() {
        println!("  - {}", backend);
    }
    println!();

    // 准备示例数据
    let traces = vec![TraceData {
        trace_id: "abc123def456".to_string(),
        spans: vec![
            SpanData {
                span_id: "span001".to_string(),
                parent_id: None,
                name: "process_request".to_string(),
                start_time: 1_700_000_000_000_000,
                end_time: 1_700_000_000_500_000,
                attributes: {
                    let mut map = HashMap::new();
                    map.insert("http.method".to_string(), "GET".to_string());
                    map.insert("http.path".to_string(), "/api/users".to_string());
                    map
                },
            },
            SpanData {
                span_id: "span002".to_string(),
                parent_id: Some("span001".to_string()),
                name: "query_database".to_string(),
                start_time: 1_700_000_000_100_000,
                end_time: 1_700_000_000_300_000,
                attributes: {
                    let mut map = HashMap::new();
                    map.insert("db.system".to_string(), "postgresql".to_string());
                    map.insert("db.statement".to_string(), "SELECT * FROM users".to_string());
                    map
                },
            },
        ],
    }];

    let metrics = vec![
        MetricData {
            name: "request_duration".to_string(),
            value: 150.5,
            timestamp: 1_700_000_000_000_000,
            dimensions: {
                let mut map = HashMap::new();
                map.insert("endpoint".to_string(), "/api/users".to_string());
                map
            },
        },
        MetricData {
            name: "active_connections".to_string(),
            value: 42.0,
            timestamp: 1_700_000_000_000_000,
            dimensions: HashMap::new(),
        },
    ];

    let logs = vec![
        LogData {
            timestamp: 1_700_000_000_000_000,
            level: "INFO".to_string(),
            message: "Request processed successfully".to_string(),
            fields: {
                let mut map = HashMap::new();
                map.insert("request_id".to_string(), "req-123".to_string());
                map
            },
        },
        LogData {
            timestamp: 1_700_000_000_001_000,
            level: "WARN".to_string(),
            message: "High latency detected".to_string(),
            fields: {
                let mut map = HashMap::new();
                map.insert("latency_ms".to_string(), "500".to_string());
                map
            },
        },
    ];

    // 导出到所有云平台
    println!("--- 导出 Traces ---");
    let trace_results = exporter.export_traces(&traces).await;
    for (i, result) in trace_results.iter().enumerate() {
        match result {
            Ok(_) => println!("  ✅ Trace 导出成功"),
            Err(e) => println!("  ❌ Trace 导出失败: {}", e),
        }
    }
    println!();

    println!("--- 导出 Metrics ---");
    let metric_results = exporter.export_metrics(&metrics).await;
    for result in metric_results {
        match result {
            Ok(_) => println!("  ✅ Metric 导出成功"),
            Err(e) => println!("  ❌ Metric 导出失败: {}", e),
        }
    }
    println!();

    println!("--- 导出 Logs ---");
    for backend in &exporter.backends {
        backend.export_logs(&logs).await?;
    }

    println!("\n=== 示例完成 ===");
    Ok(())
}
