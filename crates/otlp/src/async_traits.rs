//! Async Fn in Trait (Rust 1.75+ 稳定特性)
//!
//! 使用原生 `async fn` in trait，无需 `async-trait` crate。
//! 这是 Rust 1.75 稳定的重要特性，Rust 2024 Edition 进一步改进。
//!
//! 参考: https://blog.rust-lang.org/2023/12/21/async-fn-rpit-in-traits.html

// 允许在 public trait 中使用 async fn
// 这是 Rust 1.75+ 的标准特性
#![allow(async_fn_in_trait)]

use std::future::Future;

/// OTLP 导出器 trait - 使用原生 async fn
///
/// 不再需要 #[async_trait] 宏！
///
/// # 示例
/// ```rust
/// use otlp::async_traits::OtlpExporter;
///
/// struct MyExporter;
///
/// impl OtlpExporter for MyExporter {
///     async fn export(&self, data: Vec<u8>) -> Result<(), ExportError> {
///         // 异步导出逻辑
///         Ok(())
///     }
/// }
/// ```
pub trait OtlpExporter {
    /// 异步导出数据
    async fn export(&self, data: Vec<u8>) -> Result<(), ExportError>;
    
    /// 异步关闭导出器
    async fn shutdown(&self) -> Result<(), ExportError>;
}

/// 导出错误
#[derive(Debug, thiserror::Error)]
pub enum ExportError {
    #[error("Network error: {0}")]
    Network(String),
    #[error("Serialization error: {0}")]
    Serialization(#[from] serde_json::Error),
    #[error("Timeout")]
    Timeout,
    #[error("Other: {0}")]
    Other(String),
}

/// 遥测数据处理器 trait
///
/// 展示如何使用 async fn in trait 进行复杂操作
pub trait TelemetryProcessor {
    /// 处理遥测数据
    async fn process(&self, data: TelemetryData) -> ProcessResult;
    
    /// 批量处理
    async fn process_batch(&self, batch: Vec<TelemetryData>) -> Vec<ProcessResult> {
        // 默认实现：顺序处理
        let mut results = Vec::new();
        for item in batch {
            results.push(self.process(item).await);
        }
        results
    }
}

/// 遥测数据
#[derive(Debug, Clone)]
pub struct TelemetryData {
    pub trace_id: String,
    pub span_id: String,
    pub payload: Vec<u8>,
    pub timestamp: std::time::SystemTime,
}

/// 处理结果
#[derive(Debug)]
pub struct ProcessResult {
    pub success: bool,
    pub processed_at: std::time::SystemTime,
    pub error: Option<String>,
}

/// 存储后端 trait
///
/// 展示如何在 trait 中使用 `-> impl Future`
pub trait StorageBackend {
    /// 使用 async fn 保存数据
    async fn save(&self, key: &str, value: &[u8]) -> Result<(), StorageError>;
    
    /// 使用 `-> impl Future` 语法（等效于 async fn）
    fn load(&self, key: &str) -> impl Future<Output = Result<Option<Vec<u8>>, StorageError>> + Send;
    
    /// 删除数据
    async fn delete(&self, key: &str) -> Result<(), StorageError>;
}

/// 存储错误
#[derive(Debug, thiserror::Error)]
pub enum StorageError {
    #[error("Not found")]
    NotFound,
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    #[error("Other: {0}")]
    Other(String),
}

/// HTTP 客户端 trait
///
/// 展示 async fn in trait 的实际应用
pub trait HttpClient {
    /// 发送 HTTP 请求
    async fn send(&self, request: HttpRequest) -> Result<HttpResponse, HttpError>;
    
    /// 发送 GET 请求（便捷方法）
    async fn get(&self, url: &str) -> Result<HttpResponse, HttpError> {
        let request = HttpRequest {
            method: "GET".to_string(),
            url: url.to_string(),
            headers: vec![],
            body: None,
        };
        self.send(request).await
    }
    
    /// 发送 POST 请求（便捷方法）
    async fn post(&self, url: &str, body: Vec<u8>) -> Result<HttpResponse, HttpError> {
        let request = HttpRequest {
            method: "POST".to_string(),
            url: url.to_string(),
            headers: vec![("Content-Type".to_string(), "application/json".to_string())],
            body: Some(body),
        };
        self.send(request).await
    }
}

/// HTTP 请求
#[derive(Debug, Clone)]
pub struct HttpRequest {
    pub method: String,
    pub url: String,
    pub headers: Vec<(String, String)>,
    pub body: Option<Vec<u8>>,
}

/// HTTP 响应
#[derive(Debug, Clone)]
pub struct HttpResponse {
    pub status: u16,
    pub headers: Vec<(String, String)>,
    pub body: Vec<u8>,
}

/// HTTP 错误
#[derive(Debug, thiserror::Error)]
pub enum HttpError {
    #[error("Network error: {0}")]
    Network(String),
    #[error("Timeout")]
    Timeout,
    #[error("Invalid URL: {0}")]
    InvalidUrl(String),
}

/// 批处理 trait
///
/// 展示 async fn in trait 的高级用法
pub trait BatchProcessor<T> {
    /// 处理单个项目
    async fn process_item(&self, item: T) -> ProcessResult;
    
    /// 并发处理多个项目（默认实现）
    async fn process_concurrent(
        &self,
        items: Vec<T>,
        concurrency: usize,
    ) -> Vec<ProcessResult>
    where
        T: Send + 'static,
    {
        use futures::stream::{self, StreamExt};
        
        stream::iter(items)
            .map(|item| async move { self.process_item(item).await })
            .buffer_unordered(concurrency)
            .collect()
            .await
    }
}

/// 采样器 trait
///
/// 用于性能分析和数据采样
pub trait Sampler {
    /// 判断是否采样
    async fn should_sample(&self, trace_id: &str) -> bool;
    
    /// 获取采样率
    async fn get_sampling_rate(&self) -> f64;
}

/// 资源管理器 trait
///
/// 展示生命周期管理
pub trait ResourceManager {
    type Resource;
    
    /// 获取资源
    async fn acquire(&self) -> Result<Self::Resource, ResourceError>;
    
    /// 释放资源
    async fn release(&self, resource: Self::Resource) -> Result<(), ResourceError>;
}

/// 资源错误
#[derive(Debug, thiserror::Error)]
pub enum ResourceError {
    #[error("Resource exhausted")]
    Exhausted,
    #[error("Timeout")]
    Timeout,
}

/// 实现示例：内存存储后端
pub struct InMemoryStorage {
    data: std::sync::Mutex<std::collections::HashMap<String, Vec<u8>>>,
}

impl InMemoryStorage {
    pub fn new() -> Self {
        Self {
            data: std::sync::Mutex::new(std::collections::HashMap::new()),
        }
    }
}

impl StorageBackend for InMemoryStorage {
    async fn save(&self, key: &str, value: &[u8]) -> Result<(), StorageError> {
        let mut data = self.data.lock().unwrap();
        data.insert(key.to_string(), value.to_vec());
        Ok(())
    }
    
    fn load(&self, key: &str) -> impl Future<Output = Result<Option<Vec<u8>>, StorageError>> + Send {
        let data = self.data.lock().unwrap().get(key).cloned();
        async move { Ok(data) }
    }
    
    async fn delete(&self, key: &str) -> Result<(), StorageError> {
        let mut data = self.data.lock().unwrap();
        data.remove(key);
        Ok(())
    }
}

/// 实现示例：简单导出器
pub struct SimpleExporter;

impl OtlpExporter for SimpleExporter {
    async fn export(&self, _data: Vec<u8>) -> Result<(), ExportError> {
        // 模拟导出
        tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
        Ok(())
    }
    
    async fn shutdown(&self) -> Result<(), ExportError> {
        Ok(())
    }
}

/// 实现示例：随机采样器
pub struct RandomSampler {
    rate: f64,
}

impl RandomSampler {
    pub fn new(rate: f64) -> Self {
        Self { rate }
    }
}

impl Sampler for RandomSampler {
    async fn should_sample(&self, _trace_id: &str) -> bool {
        rand::random::<f64>() < self.rate
    }
    
    async fn get_sampling_rate(&self) -> f64 {
        self.rate
    }
}

/// 使用 trait 的泛型函数
///
/// 展示如何在泛型代码中使用 async fn in trait
pub async fn export_with_retry<E>(
    exporter: &E,
    data: Vec<u8>,
    max_retries: u32,
) -> Result<(), ExportError>
where
    E: OtlpExporter,
{
    let mut last_error = None;
    
    for attempt in 0..max_retries {
        match exporter.export(data.clone()).await {
            Ok(()) => return Ok(()),
            Err(e) => {
                last_error = Some(e);
                if attempt < max_retries - 1 {
                    tokio::time::sleep(tokio::time::Duration::from_millis(100 * (attempt + 1) as u64)).await;
                }
            }
        }
    }
    
    Err(last_error.unwrap_or_else(|| ExportError::Other("Unknown error".to_string())))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_in_memory_storage() {
        let storage = InMemoryStorage::new();
        
        // 测试保存和加载
        storage.save("test", b"hello").await.unwrap();
        let value = storage.load("test").await.unwrap();
        assert_eq!(value, Some(b"hello".to_vec()));
        
        // 测试删除
        storage.delete("test").await.unwrap();
        let value = storage.load("test").await.unwrap();
        assert_eq!(value, None);
    }

    #[tokio::test]
    async fn test_simple_exporter() {
        let exporter = SimpleExporter;
        
        let result = exporter.export(vec![1, 2, 3]).await;
        assert!(result.is_ok());
        
        let result = exporter.shutdown().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_random_sampler() {
        let sampler = RandomSampler::new(1.0); // 100% 采样
        
        assert!(sampler.should_sample("test").await);
        assert_eq!(sampler.get_sampling_rate().await, 1.0);
        
        let sampler = RandomSampler::new(0.0); // 0% 采样
        assert!(!sampler.should_sample("test").await);
    }

    #[tokio::test]
    async fn test_export_with_retry() {
        let exporter = SimpleExporter;
        
        let result = export_with_retry(&exporter, vec![1, 2, 3], 3).await;
        assert!(result.is_ok());
    }
}
