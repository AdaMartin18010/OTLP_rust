//! 简化的OTLP客户端
//!
//! 提供简化的API接口，降低使用复杂度

use std::time::{Duration, Instant};
use tokio::time::sleep;
use anyhow::Result;

/// 日志级别
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LogLevel {
    Debug,
    Info,
    Warn,
    Error,
}

/// 简单操作类型
#[derive(Debug, Clone)]
pub enum SimpleOperation {
    Trace {
        name: String,
        duration_ms: u64,
        success: bool,
        error: Option<String>,
    },
    Metric {
        name: String,
        value: f64,
        unit: Option<String>,
    },
    Log {
        message: String,
        level: LogLevel,
        source: Option<String>,
    },
}

/// 批量发送结果
#[derive(Debug, Clone)]
pub struct BatchSendResult {
    pub total_sent: usize,
    pub success_count: usize,
    pub failure_count: usize,
    pub duration: Duration,
}

/// 健康检查结果
#[derive(Debug, Clone)]
pub struct HealthStatus {
    pub is_healthy: bool,
    pub uptime: Duration,
    pub total_requests: u64,
    pub success_rate: f64,
}

/// 简化的OTLP客户端
#[derive(Debug)]
#[allow(dead_code)]
pub struct SimpleOtlpClient {
    endpoint: String,
    service_name: String,
    service_version: String,
    timeout: Duration,
    debug: bool,
    start_time: Instant,
    request_count: u64,
    success_count: u64,
}

impl SimpleOtlpClient {
    /// 创建新的简化客户端
    pub async fn new(endpoint: &str) -> Result<Self> {
        Ok(Self {
            endpoint: endpoint.to_string(),
            service_name: "default-service".to_string(),
            service_version: "1.0.0".to_string(),
            timeout: Duration::from_secs(10),
            debug: false,
            start_time: Instant::now(),
            request_count: 0,
            success_count: 0,
        })
    }

    /// 发送追踪数据
    pub async fn trace(
        &mut self,
        operation_name: &str,
        duration_ms: u64,
        success: bool,
        _error: Option<String>,
    ) -> Result<()> {
        self.request_count += 1;
        
        if self.debug {
            println!("发送追踪: {} ({}ms, {})", operation_name, duration_ms, if success { "成功" } else { "失败" });
        }
        
        // 模拟网络请求
        sleep(Duration::from_millis(1)).await;
        
        if success {
            self.success_count += 1;
        }
        
        Ok(())
    }

    /// 发送指标数据
    pub async fn metric(&mut self, name: &str, value: f64, unit: Option<&str>) -> Result<()> {
        self.request_count += 1;
        
        if self.debug {
            println!("发送指标: {} = {} {}", name, value, unit.unwrap_or(""));
        }
        
        // 模拟网络请求
        sleep(Duration::from_millis(1)).await;
        
        self.success_count += 1;
        Ok(())
    }

    /// 发送日志数据
    pub async fn log(&mut self, message: &str, level: LogLevel, source: Option<&str>) -> Result<()> {
        self.request_count += 1;
        
        if self.debug {
            println!("发送日志 [{}]: {} (来源: {})", 
                match level {
                    LogLevel::Debug => "DEBUG",
                    LogLevel::Info => "INFO",
                    LogLevel::Warn => "WARN",
                    LogLevel::Error => "ERROR",
                },
                message,
                source.unwrap_or("unknown")
            );
        }
        
        // 模拟网络请求
        sleep(Duration::from_millis(1)).await;
        
        self.success_count += 1;
        Ok(())
    }

    /// 批量发送操作
    pub async fn batch_send(&mut self, operations: Vec<SimpleOperation>) -> Result<BatchSendResult> {
        let start_time = Instant::now();
        let mut success_count = 0;
        let mut failure_count = 0;

        for operation in operations {
            match operation {
                SimpleOperation::Trace { name, duration_ms, success, error } => {
                    match self.trace(&name, duration_ms, success, error).await {
                        Ok(_) => success_count += 1,
                        Err(_) => failure_count += 1,
                    }
                },
                SimpleOperation::Metric { name, value, unit } => {
                    match self.metric(&name, value, unit.as_deref()).await {
                        Ok(_) => success_count += 1,
                        Err(_) => failure_count += 1,
                    }
                },
                SimpleOperation::Log { message, level, source } => {
                    match self.log(&message, level, source.as_deref()).await {
                        Ok(_) => success_count += 1,
                        Err(_) => failure_count += 1,
                    }
                },
            }
        }

        Ok(BatchSendResult {
            total_sent: success_count + failure_count,
            success_count,
            failure_count,
            duration: start_time.elapsed(),
        })
    }

    /// 健康检查
    pub async fn health_check(&self) -> HealthStatus {
        let uptime = self.start_time.elapsed();
        let success_rate = if self.request_count > 0 {
            self.success_count as f64 / self.request_count as f64
        } else {
            1.0
        };

        HealthStatus {
            is_healthy: success_rate > 0.8, // 80%以上成功率认为健康
            uptime,
            total_requests: self.request_count,
            success_rate,
        }
    }

    /// 关闭客户端
    pub async fn shutdown(&mut self) -> Result<()> {
        if self.debug {
            println!("关闭客户端");
        }
        Ok(())
    }
}

/// 简化客户端构建器
#[derive(Debug)]
pub struct SimpleClientBuilder {
    endpoint: Option<String>,
    service_name: Option<String>,
    service_version: Option<String>,
    timeout: Option<Duration>,
    debug: Option<bool>,
}

impl SimpleClientBuilder {
    /// 创建新的构建器
    pub fn new() -> Self {
        Self {
            endpoint: None,
            service_name: None,
            service_version: None,
            timeout: None,
            debug: None,
        }
    }

    /// 设置端点
    pub fn endpoint(mut self, endpoint: &str) -> Self {
        self.endpoint = Some(endpoint.to_string());
        self
    }

    /// 设置服务名称
    pub fn service(mut self, name: &str, version: &str) -> Self {
        self.service_name = Some(name.to_string());
        self.service_version = Some(version.to_string());
        self
    }

    /// 设置超时时间
    pub fn timeout(mut self, timeout: Duration) -> Self {
        self.timeout = Some(timeout);
        self
    }

    /// 设置调试模式
    pub fn debug(mut self, debug: bool) -> Self {
        self.debug = Some(debug);
        self
    }

    /// 构建客户端
    pub async fn build(self) -> Result<SimpleOtlpClient> {
        let endpoint = self.endpoint.unwrap_or_else(|| "http://localhost:4317".to_string());
        let mut client = SimpleOtlpClient::new(&endpoint).await?;
        
        if let Some(service_name) = self.service_name {
            client.service_name = service_name;
        }
        if let Some(service_version) = self.service_version {
            client.service_version = service_version;
        }
        if let Some(timeout) = self.timeout {
            client.timeout = timeout;
        }
        if let Some(debug) = self.debug {
            client.debug = debug;
        }

        Ok(client)
    }
}

impl Default for SimpleClientBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_simple_client_creation() {
        let client = SimpleOtlpClient::new("http://localhost:4317").await.unwrap();
        assert_eq!(client.endpoint, "http://localhost:4317");
    }

    #[tokio::test]
    async fn test_client_builder() {
        let client = SimpleClientBuilder::new()
            .endpoint("http://test:4317")
            .service("test-service", "2.0.0")
            .timeout(Duration::from_secs(5))
            .debug(true)
            .build()
            .await
            .unwrap();
        
        assert_eq!(client.endpoint, "http://test:4317");
        assert_eq!(client.service_name, "test-service");
        assert_eq!(client.service_version, "2.0.0");
        assert_eq!(client.timeout, Duration::from_secs(5));
        assert!(client.debug);
    }

    #[tokio::test]
    async fn test_health_check() {
        let mut client = SimpleOtlpClient::new("http://localhost:4317").await.unwrap();
        
        // 发送一些请求
        client.trace("test", 100, true, None).await.unwrap();
        client.metric("test_metric", 1.0, Some("count")).await.unwrap();
        
        let health = client.health_check().await;
        assert!(health.is_healthy);
        assert_eq!(health.total_requests, 2);
        assert_eq!(health.success_rate, 1.0);
    }
}