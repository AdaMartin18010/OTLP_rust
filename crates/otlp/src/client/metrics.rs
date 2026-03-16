//! # 客户端指标和审计
//!
//! 提供客户端性能指标收集和审计功能。

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

/// 客户端性能指标
#[derive(Debug, Default)]
pub struct ClientMetrics {
    pub total_requests: AtomicU64,
    pub successful_requests: AtomicU64,
    pub failed_requests: AtomicU64,
    pub total_bytes_sent: AtomicU64,
    pub total_bytes_received: AtomicU64,
    pub average_latency_ms: AtomicU64,
}

impl Clone for ClientMetrics {
    fn clone(&self) -> Self {
        Self {
            total_requests: AtomicU64::new(self.total_requests.load(Ordering::Relaxed)),
            successful_requests: AtomicU64::new(self.successful_requests.load(Ordering::Relaxed)),
            failed_requests: AtomicU64::new(self.failed_requests.load(Ordering::Relaxed)),
            total_bytes_sent: AtomicU64::new(self.total_bytes_sent.load(Ordering::Relaxed)),
            total_bytes_received: AtomicU64::new(self.total_bytes_received.load(Ordering::Relaxed)),
            average_latency_ms: AtomicU64::new(self.average_latency_ms.load(Ordering::Relaxed)),
        }
    }
}

impl ClientMetrics {
    /// 记录请求
    pub fn record_request(&self) {
        self.total_requests.fetch_add(1, Ordering::Relaxed);
    }

    /// 记录成功请求
    pub fn record_success(&self, latency: Duration) {
        self.successful_requests.fetch_add(1, Ordering::Relaxed);
        self.update_average_latency(latency);
    }

    /// 记录失败请求
    pub fn record_failure(&self) {
        self.failed_requests.fetch_add(1, Ordering::Relaxed);
    }

    /// 记录发送字节数
    pub fn record_bytes_sent(&self, bytes: u64) {
        self.total_bytes_sent.fetch_add(bytes, Ordering::Relaxed);
    }

    /// 记录接收字节数
    pub fn record_bytes_received(&self, bytes: u64) {
        self.total_bytes_received
            .fetch_add(bytes, Ordering::Relaxed);
    }

    /// 更新平均延迟
    fn update_average_latency(&self, latency: Duration) {
        let latency_ms = latency.as_millis() as u64;
        let current = self.average_latency_ms.load(Ordering::Relaxed);
        let total_requests = self.total_requests.load(Ordering::Relaxed);

        if total_requests > 0 {
            // 使用移动平均
            let new_avg = (current * (total_requests - 1) + latency_ms) / total_requests;
            self.average_latency_ms.store(new_avg, Ordering::Relaxed);
        }
    }

    /// 获取快照
    pub fn snapshot(&self) -> MetricsSnapshot {
        MetricsSnapshot {
            total_requests: self.total_requests.load(Ordering::Relaxed),
            successful_requests: self.successful_requests.load(Ordering::Relaxed),
            failed_requests: self.failed_requests.load(Ordering::Relaxed),
            total_bytes_sent: self.total_bytes_sent.load(Ordering::Relaxed),
            total_bytes_received: self.total_bytes_received.load(Ordering::Relaxed),
            average_latency_ms: self.average_latency_ms.load(Ordering::Relaxed),
        }
    }
}

/// 指标快照
#[derive(Debug, Clone, Copy)]
pub struct MetricsSnapshot {
    pub total_requests: u64,
    pub successful_requests: u64,
    pub failed_requests: u64,
    pub total_bytes_sent: u64,
    pub total_bytes_received: u64,
    pub average_latency_ms: u64,
}

impl MetricsSnapshot {
    /// 计算成功率
    pub fn success_rate(&self) -> f64 {
        if self.total_requests == 0 {
            return 0.0;
        }
        self.successful_requests as f64 / self.total_requests as f64
    }

    /// 计算失败率
    pub fn failure_rate(&self) -> f64 {
        if self.total_requests == 0 {
            return 0.0;
        }
        self.failed_requests as f64 / self.total_requests as f64
    }
}

/// 审计钩子 trait
///
/// 用于审计和记录客户端操作。
pub trait AuditHook: Send + Sync + std::fmt::Debug {
    /// 记录审计事件
    fn log_event(&self, event: AuditEvent);

    /// 刷新审计日志
    fn flush(&self);
}

/// 审计事件
#[derive(Debug, Clone)]
pub struct AuditEvent {
    pub timestamp: Instant,
    pub event_type: EventType,
    pub operation: String,
    pub details: HashMap<String, String>,
    pub success: bool,
}

impl AuditEvent {
    /// 创建新的审计事件
    pub fn new(event_type: EventType, operation: impl Into<String>, success: bool) -> Self {
        Self {
            timestamp: Instant::now(),
            event_type,
            operation: operation.into(),
            details: HashMap::new(),
            success,
        }
    }

    /// 添加详情
    pub fn with_detail(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.details.insert(key.into(), value.into());
        self
    }
}

/// 事件类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EventType {
    Request,
    Response,
    Error,
    Configuration,
    Shutdown,
}

/// 标准输出审计钩子
#[derive(Debug, Default)]
pub struct StdoutAuditHook;

impl AuditHook for StdoutAuditHook {
    fn log_event(&self, event: AuditEvent) {
        println!(
            "[AUDIT] {:?} | {} | Success: {} | Details: {:?}",
            event.event_type, event.operation, event.success, event.details
        );
    }

    fn flush(&self) {
        // 标准输出自动刷新
    }
}

/// 文件审计钩子
#[derive(Debug)]
pub struct FileAuditHook {
    file_path: String,
}

impl FileAuditHook {
    /// 创建新的文件审计钩子
    pub fn new(file_path: impl Into<String>) -> Self {
        Self {
            file_path: file_path.into(),
        }
    }
}

impl AuditHook for FileAuditHook {
    fn log_event(&self, event: AuditEvent) {
        use std::fs::OpenOptions;
        use std::io::Write;

        let line = format!(
            "[{}] {:?} | {} | Success: {} | Details: {:?}\n",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            event.event_type,
            event.operation,
            event.success,
            event.details
        );

        if let Ok(mut file) = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&self.file_path)
        {
            let _ = file.write_all(line.as_bytes());
        }
    }

    fn flush(&self) {
        // 文件操作通常会自动刷新
    }
}

/// HTTP 审计钩子
#[derive(Debug)]
pub struct HttpAuditHook {
    endpoint: String,
    headers: HashMap<String, String>,
}

impl HttpAuditHook {
    /// 创建新的 HTTP 审计钩子
    pub fn new(endpoint: impl Into<String>) -> Self {
        Self {
            endpoint: endpoint.into(),
            headers: HashMap::new(),
        }
    }

    /// 添加请求头
    pub fn with_header(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.headers.insert(key.into(), value.into());
        self
    }
}

impl AuditHook for HttpAuditHook {
    fn log_event(&self, event: AuditEvent) {
        // HTTP 审计钩子的实现
        // 这里可以发送 HTTP 请求到审计服务器
        tracing::debug!("Sending audit event to {}: {:?}", self.endpoint, event);
    }

    fn flush(&self) {
        // HTTP 批量发送逻辑
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_metrics_recording() {
        let metrics = ClientMetrics::default();

        metrics.record_request();
        metrics.record_request();
        metrics.record_success(Duration::from_millis(100));
        metrics.record_failure();

        let snapshot = metrics.snapshot();
        assert_eq!(snapshot.total_requests, 2);
        assert_eq!(snapshot.successful_requests, 1);
        assert_eq!(snapshot.failed_requests, 1);
    }

    #[test]
    fn test_metrics_snapshot_calculations() {
        let snapshot = MetricsSnapshot {
            total_requests: 100,
            successful_requests: 95,
            failed_requests: 5,
            total_bytes_sent: 1000,
            total_bytes_received: 2000,
            average_latency_ms: 50,
        };

        assert_eq!(snapshot.success_rate(), 0.95);
        assert_eq!(snapshot.failure_rate(), 0.05);
    }

    #[test]
    fn test_audit_event_creation() {
        let event = AuditEvent::new(EventType::Request, "test_operation", true)
            .with_detail("key1", "value1")
            .with_detail("key2", "value2");

        assert_eq!(event.operation, "test_operation");
        assert!(event.success);
        assert_eq!(event.details.len(), 2);
    }

    #[test]
    fn test_stdout_audit_hook() {
        let hook = StdoutAuditHook;
        let event = AuditEvent::new(EventType::Request, "test", true);
        hook.log_event(event);
        hook.flush();
    }

    #[test]
    fn test_bytes_recording() {
        let metrics = ClientMetrics::default();

        metrics.record_bytes_sent(1024);
        metrics.record_bytes_sent(2048);
        metrics.record_bytes_received(512);

        let snapshot = metrics.snapshot();
        assert_eq!(snapshot.total_bytes_sent, 3072);
        assert_eq!(snapshot.total_bytes_received, 512);
    }
}
