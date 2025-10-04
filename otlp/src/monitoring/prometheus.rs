//! # Prometheus监控集成
//!
//! 提供Prometheus指标收集和暴露功能

use crate::error::Result;
use prometheus::{
    Counter, CounterVec, Gauge, GaugeVec, Histogram, HistogramOpts, HistogramVec, Opts, Registry,
};
use std::sync::Arc;
use tokio::sync::RwLock;

/// Prometheus监控器
pub struct PrometheusMonitor {
    registry: Registry,
    metrics: Arc<RwLock<PrometheusMetrics>>,
}

/// Prometheus指标
pub struct PrometheusMetrics {
    // 请求指标
    pub requests_total: CounterVec,
    pub requests_duration: HistogramVec,
    pub requests_in_flight: GaugeVec,
    
    // 数据处理指标
    pub data_processed_total: CounterVec,
    pub data_processing_duration: HistogramVec,
    pub data_queue_size: GaugeVec,
    
    // 传输指标
    pub transport_requests_total: CounterVec,
    pub transport_duration: HistogramVec,
    pub transport_errors_total: CounterVec,
    
    // 系统指标
    pub memory_usage: Gauge,
    pub cpu_usage: Gauge,
    pub active_connections: Gauge,
}

impl PrometheusMonitor {
    /// 创建新的Prometheus监控器
    pub fn new() -> Result<Self> {
        let registry = Registry::new();
        let metrics = Self::create_metrics(&registry)?;
        
        Ok(Self {
            registry,
            metrics: Arc::new(RwLock::new(metrics)),
        })
    }
    
    /// 创建指标
    fn create_metrics(registry: &Registry) -> Result<PrometheusMetrics> {
        // 请求指标
        let requests_total = CounterVec::new(
            Opts::new("otlp_requests_total", "Total number of requests"),
            &["method", "endpoint", "status"]
        )?;
        
        let requests_duration = HistogramVec::new(
            HistogramOpts::new("otlp_requests_duration_seconds", "Request duration in seconds"),
            &["method", "endpoint"]
        )?;
        
        let requests_in_flight = GaugeVec::new(
            Opts::new("otlp_requests_in_flight", "Number of requests currently being processed"),
            &["method", "endpoint"]
        )?;
        
        // 数据处理指标
        let data_processed_total = CounterVec::new(
            Opts::new("otlp_data_processed_total", "Total amount of data processed"),
            &["type", "status"]
        )?;
        
        let data_processing_duration = HistogramVec::new(
            HistogramOpts::new("otlp_data_processing_duration_seconds", "Data processing duration in seconds"),
            &["type"]
        )?;
        
        let data_queue_size = GaugeVec::new(
            Opts::new("otlp_data_queue_size", "Size of data processing queue"),
            &["type"]
        )?;
        
        // 传输指标
        let transport_requests_total = CounterVec::new(
            Opts::new("otlp_transport_requests_total", "Total number of transport requests"),
            &["protocol", "endpoint", "status"]
        )?;
        
        let transport_duration = HistogramVec::new(
            HistogramOpts::new("otlp_transport_duration_seconds", "Transport duration in seconds"),
            &["protocol", "endpoint"]
        )?;
        
        let transport_errors_total = CounterVec::new(
            Opts::new("otlp_transport_errors_total", "Total number of transport errors"),
            &["protocol", "endpoint", "error_type"]
        )?;
        
        // 系统指标
        let memory_usage = Gauge::new("otlp_memory_usage_bytes", "Memory usage in bytes")?;
        let cpu_usage = Gauge::new("otlp_cpu_usage_percent", "CPU usage percentage")?;
        let active_connections = Gauge::new("otlp_active_connections", "Number of active connections")?;
        
        // 注册指标
        registry.register(Box::new(requests_total.clone()))?;
        registry.register(Box::new(requests_duration.clone()))?;
        registry.register(Box::new(requests_in_flight.clone()))?;
        registry.register(Box::new(data_processed_total.clone()))?;
        registry.register(Box::new(data_processing_duration.clone()))?;
        registry.register(Box::new(data_queue_size.clone()))?;
        registry.register(Box::new(transport_requests_total.clone()))?;
        registry.register(Box::new(transport_duration.clone()))?;
        registry.register(Box::new(transport_errors_total.clone()))?;
        registry.register(Box::new(memory_usage.clone()))?;
        registry.register(Box::new(cpu_usage.clone()))?;
        registry.register(Box::new(active_connections.clone()))?;
        
        Ok(PrometheusMetrics {
            requests_total,
            requests_duration,
            requests_in_flight,
            data_processed_total,
            data_processing_duration,
            data_queue_size,
            transport_requests_total,
            transport_duration,
            transport_errors_total,
            memory_usage,
            cpu_usage,
            active_connections,
        })
    }
    
    /// 获取指标注册表
    pub fn registry(&self) -> &Registry {
        &self.registry
    }
    
    /// 获取指标
    pub async fn metrics(&self) -> Arc<RwLock<PrometheusMetrics>> {
        self.metrics.clone()
    }
    
    /// 记录请求指标
    pub async fn record_request(&self, method: &str, endpoint: &str, status: &str, duration: f64) {
        let metrics = self.metrics.read().await;
        metrics.requests_total
            .with_label_values(&[method, endpoint, status])
            .inc();
        metrics.requests_duration
            .with_label_values(&[method, endpoint])
            .observe(duration);
    }
    
    /// 增加正在处理的请求数
    pub async fn increment_requests_in_flight(&self, method: &str, endpoint: &str) {
        let metrics = self.metrics.read().await;
        metrics.requests_in_flight
            .with_label_values(&[method, endpoint])
            .inc();
    }
    
    /// 减少正在处理的请求数
    pub async fn decrement_requests_in_flight(&self, method: &str, endpoint: &str) {
        let metrics = self.metrics.read().await;
        metrics.requests_in_flight
            .with_label_values(&[method, endpoint])
            .dec();
    }
    
    /// 记录数据处理指标
    pub async fn record_data_processed(&self, data_type: &str, status: &str, amount: u64, duration: f64) {
        let metrics = self.metrics.read().await;
        metrics.data_processed_total
            .with_label_values(&[data_type, status])
            .inc_by(amount as f64);
        metrics.data_processing_duration
            .with_label_values(&[data_type])
            .observe(duration);
    }
    
    /// 更新数据队列大小
    pub async fn update_data_queue_size(&self, data_type: &str, size: usize) {
        let metrics = self.metrics.read().await;
        metrics.data_queue_size
            .with_label_values(&[data_type])
            .set(size as f64);
    }
    
    /// 记录传输指标
    pub async fn record_transport_request(&self, protocol: &str, endpoint: &str, status: &str, duration: f64) {
        let metrics = self.metrics.read().await;
        metrics.transport_requests_total
            .with_label_values(&[protocol, endpoint, status])
            .inc();
        metrics.transport_duration
            .with_label_values(&[protocol, endpoint])
            .observe(duration);
    }
    
    /// 记录传输错误
    pub async fn record_transport_error(&self, protocol: &str, endpoint: &str, error_type: &str) {
        let metrics = self.metrics.read().await;
        metrics.transport_errors_total
            .with_label_values(&[protocol, endpoint, error_type])
            .inc();
    }
    
    /// 更新系统指标
    pub async fn update_system_metrics(&self, memory_usage: u64, cpu_usage: f64, active_connections: usize) {
        let metrics = self.metrics.read().await;
        metrics.memory_usage.set(memory_usage as f64);
        metrics.cpu_usage.set(cpu_usage);
        metrics.active_connections.set(active_connections as f64);
    }
}

impl Default for PrometheusMonitor {
    fn default() -> Self {
        Self::new().expect("Failed to create PrometheusMonitor")
    }
}

/// 监控中间件
pub struct MonitoringMiddleware {
    monitor: Arc<PrometheusMonitor>,
}

impl MonitoringMiddleware {
    pub fn new(monitor: Arc<PrometheusMonitor>) -> Self {
        Self { monitor }
    }
    
    /// 记录请求开始
    pub async fn on_request_start(&self, method: &str, endpoint: &str) {
        self.monitor.increment_requests_in_flight(method, endpoint).await;
    }
    
    /// 记录请求结束
    pub async fn on_request_end(&self, method: &str, endpoint: &str, status: &str, duration: f64) {
        self.monitor.decrement_requests_in_flight(method, endpoint).await;
        self.monitor.record_request(method, endpoint, status, duration).await;
    }
    
    /// 记录数据处理
    pub async fn on_data_processed(&self, data_type: &str, status: &str, amount: u64, duration: f64) {
        self.monitor.record_data_processed(data_type, status, amount, duration).await;
    }
    
    /// 记录传输请求
    pub async fn on_transport_request(&self, protocol: &str, endpoint: &str, status: &str, duration: f64) {
        self.monitor.record_transport_request(protocol, endpoint, status, duration).await;
    }
    
    /// 记录传输错误
    pub async fn on_transport_error(&self, protocol: &str, endpoint: &str, error_type: &str) {
        self.monitor.record_transport_error(protocol, endpoint, error_type).await;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_prometheus_monitor_creation() {
        let monitor = PrometheusMonitor::new().expect("Failed to create Prometheus monitor");
        assert!(monitor.registry().gather().is_empty());
    }
    
    #[tokio::test]
    async fn test_metrics_recording() {
        let monitor = PrometheusMonitor::new().expect("Failed to create Prometheus monitor");
        
        // 记录请求指标
        monitor.record_request("GET", "/health", "200", 0.1).await;
        
        // 记录数据处理指标
        monitor.record_data_processed("trace", "success", 100, 0.05).await;
        
        // 记录传输指标
        monitor.record_transport_request("grpc", "localhost:4317", "success", 0.2).await;
        
        // 更新系统指标
        monitor.update_system_metrics(1024 * 1024, 50.0, 10).await;
        
        // 验证指标已记录
        let metrics = monitor.metrics().read().await;
        assert_eq!(metrics.requests_total.get_metric_with_label_values(&["GET", "/health", "200"])
            .expect("Failed to get requests metric").get(), 1.0);
        assert_eq!(metrics.data_processed_total.get_metric_with_label_values(&["trace", "success"])
            .expect("Failed to get data processed metric").get(), 100.0);
        assert_eq!(metrics.transport_requests_total.get_metric_with_label_values(&["grpc", "localhost:4317", "success"])
            .expect("Failed to get transport requests metric").get(), 1.0);
        assert_eq!(metrics.memory_usage.get(), 1024.0 * 1024.0);
        assert_eq!(metrics.cpu_usage.get(), 50.0);
        assert_eq!(metrics.active_connections.get(), 10.0);
    }
}
