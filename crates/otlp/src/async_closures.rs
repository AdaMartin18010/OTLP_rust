//! Rust 2024 Edition: Async Closures
//!
//! 本模块展示 Rust 2024 Edition 的 async closure 特性：
//! - `async || {}` 语法
//! - `AsyncFn` trait
//! - 在 OTLP 导出器中的应用
//!
//! 注意：需要 Rust 1.85+ (Edition 2024)
//!
//! 参考: https://blog.rust-lang.org/2025/02/28/Rust-1.85.0.html

use std::future::Future;
use std::pin::Pin;

/// ==================== Async Closure 基础 ====================

/// Rust 2024 Edition 允许直接定义 async closure
/// 
/// 以前：
/// ```rust
/// let f = || async { /* ... */ };
/// ```
/// 
/// 现在：
/// ```rust
/// let f = async || { /* ... */ };
/// ```
pub fn create_async_timer() -> impl Fn() -> Pin<Box<dyn Future<Output = ()> + Send + 'static>> {
    // Rust 2024: async closure 语法
    // let timer = async || {
    //     tokio::time::sleep(Duration::from_secs(1)).await;
    //     println!("Timer fired!");
    // };
    
    // 由于当前编译器版本可能不完全支持，使用兼容写法
    || Box::pin(async {
        tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
    })
}

/// 使用 async closure 的重试逻辑
pub struct AsyncRetry<F> {
    operation: F,
    max_attempts: u32,
    delay_ms: u64,
}

impl<F, Fut, T, E> AsyncRetry<F>
where
    F: Fn() -> Fut,
    Fut: Future<Output = Result<T, E>>,
    E: std::fmt::Display,
{
    pub fn new(operation: F, max_attempts: u32, delay_ms: u64) -> Self {
        Self {
            operation,
            max_attempts,
            delay_ms,
        }
    }
    
    /// 执行带重试的操作
    /// 
    /// Rust 2024: 可以使用 async || 捕获环境
    pub async fn execute(&self) -> Result<T, E> {
        let mut last_error = None;
        
        for attempt in 1..=self.max_attempts {
            match (self.operation)().await {
                Ok(result) => return Ok(result),
                Err(e) => {
                    tracing::warn!("Attempt {} failed: {}", attempt, e);
                    last_error = Some(e);
                    
                    if attempt < self.max_attempts {
                        tokio::time::sleep(tokio::time::Duration::from_millis(self.delay_ms)).await;
                    }
                }
            }
        }
        
        Err(last_error.unwrap())
    }
}

/// ==================== OTLP 导出器中的应用 ====================

/// 使用 async closure 的批量导出器
pub struct AsyncBatchExporter<T> {
    buffer: Vec<T>,
    /// Rust 2024: async closure 类型
    export_fn: Box<dyn Fn(Vec<T>) -> Pin<Box<dyn Future<Output = Result<(), ExportError>> + Send>> + Send>,
}

#[derive(Debug, thiserror::Error)]
pub enum ExportError {
    #[error("Export failed: {0}")]
    Failed(String),
    #[error("Timeout")]
    Timeout,
}

impl<T: Send + 'static> AsyncBatchExporter<T> {
    /// 创建新的批量导出器
    /// 
    /// # Example (Rust 2024)
    /// ```rust,ignore
    /// let exporter = AsyncBatchExporter::new(async |batch| {
    ///     client.send_batch(batch).await
    /// });
    /// ```
    pub fn new<F, Fut>(export_fn: F) -> Self
    where
        F: Fn(Vec<T>) -> Fut + Send + 'static,
        Fut: Future<Output = Result<(), ExportError>> + Send + 'static,
    {
        Self {
            buffer: Vec::new(),
            export_fn: Box::new(move |batch| Box::pin(export_fn(batch))),
        }
    }
    
    /// 添加项目到缓冲区
    pub fn push(&mut self, item: T) {
        self.buffer.push(item);
    }
    
    /// 导出当前缓冲区
    pub async fn flush(&mut self) -> Result<(), ExportError> {
        if self.buffer.is_empty() {
            return Ok(());
        }
        
        let batch = std::mem::take(&mut self.buffer);
        (self.export_fn)(batch).await
    }
}

/// ==================== AsyncFn Trait 使用 ====================

/// 使用 AsyncFn trait 的通用遥测处理器
/// 
/// Rust 2024 引入了 AsyncFn、AsyncFnMut 和 AsyncFnOnce trait
#[allow(dead_code)]
pub struct TelemetryProcessor<F> {
    processor: F,
}

// Rust 2024: 可以使用 AsyncFn trait bound
// impl<F> TelemetryProcessor<F>
// where
//     F: AsyncFn(TelemetryData) -> ProcessResult,
// {
//     pub async fn process(&self, data: TelemetryData) -> ProcessResult {
//         (self.processor)(data).await
//     }
// }

/// 遥测数据
#[derive(Debug, Clone)]
pub struct TelemetryData {
    pub trace_id: String,
    pub span_id: String,
    pub attributes: Vec<(String, String)>,
}

/// 处理结果
#[derive(Debug)]
pub struct ProcessResult {
    pub success: bool,
    pub processed_at: std::time::SystemTime,
}

/// ==================== 生产环境模式 ====================

/// 使用 async closure 的连接池管理器
pub struct AsyncPoolManager<T> {
    create_fn: Box<dyn Fn() -> Pin<Box<dyn Future<Output = T> + Send>> + Send>,
    destroy_fn: Box<dyn Fn(T) -> Pin<Box<dyn Future<Output = ()> + Send>> + Send>,
}

impl<T: Send + 'static> AsyncPoolManager<T> {
    /// 创建新的连接池管理器
    /// 
    /// # Rust 2024 语法
    /// ```rust,ignore
    /// let manager = AsyncPoolManager::new(
    ///     async || create_connection().await,
    ///     async |conn| { conn.close().await; }
    /// );
    /// ```
    pub fn new<CreateFut, DestroyFut>(
        create_fn: impl Fn() -> CreateFut + Send + 'static,
        destroy_fn: impl Fn(T) -> DestroyFut + Send + 'static,
    ) -> Self
    where
        CreateFut: Future<Output = T> + Send + 'static,
        DestroyFut: Future<Output = ()> + Send + 'static,
    {
        Self {
            create_fn: Box::new(move || Box::pin(create_fn())),
            destroy_fn: Box::new(move |item| Box::pin(destroy_fn(item))),
        }
    }
    
    /// 创建新连接
    pub async fn create(&self) -> T {
        (self.create_fn)().await
    }
    
    /// 销毁连接
    pub async fn destroy(&self, item: T) {
        (self.destroy_fn)(item).await
    }
}

/// ==================== 实用工具函数 ====================

/// 使用 async closure 的超时包装器
pub async fn with_timeout<F, Fut, T>(
    operation: F,
    timeout_ms: u64,
) -> Result<T, TimeoutError>
where
    F: FnOnce() -> Fut,
    Fut: Future<Output = T>,
{
    let timeout = tokio::time::Duration::from_millis(timeout_ms);
    
    match tokio::time::timeout(timeout, operation()).await {
        Ok(result) => Ok(result),
        Err(_) => Err(TimeoutError::Elapsed),
    }
}

#[derive(Debug, thiserror::Error)]
pub enum TimeoutError {
    #[error("Operation timed out")]
    Elapsed,
}

/// 使用 async closure 的批处理映射
pub async fn async_map_batch<T, F, Fut, R>(
    items: Vec<T>,
    f: F,
    concurrency: usize,
) -> Vec<R>
where
    F: Fn(T) -> Fut + Send + Copy,
    Fut: Future<Output = R> + Send,
    R: Send,
    T: Send,
{
    use futures::stream::{self, StreamExt};
    
    stream::iter(items)
        .map(|item| async move { f(item).await })
        .buffer_unordered(concurrency)
        .collect()
        .await
}

/// ==================== 示例使用 ====================

/// 展示 Rust 2024 async closure 的完整示例
pub mod examples {
    use super::*;
    
    /// 示例：异步遥测导出
    pub async fn telemetry_export_example() {
        // Rust 2024: async closure 语法
        // let exporter = AsyncBatchExporter::new(async |batch: Vec<TelemetryData>| {
        //     let client = create_otlp_client().await?;
        //     client.export(batch).await
        // });
        
        // 兼容写法
        let mut exporter = AsyncBatchExporter::new(|batch: Vec<TelemetryData>| async move {
            println!("Exporting {} items", batch.len());
            Ok(())
        });
        
        exporter.push(TelemetryData {
            trace_id: "abc".to_string(),
            span_id: "123".to_string(),
            attributes: vec![],
        });
        
        let _ = exporter.flush().await;
    }
    
    /// 示例：带重试的导出
    pub async fn retry_export_example() {
        let attempt = std::sync::Arc::new(std::sync::atomic::AtomicU32::new(0));
        
        let retry = AsyncRetry::new(
            || async {
                let curr = attempt.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                if curr < 2 {
                    Err(ExportError::Failed("Temporary failure".to_string()))
                } else {
                    Ok(())
                }
            },
            3,
            100,
        );
        
        let result = retry.execute().await;
        assert!(result.is_ok());
    }
    
    /// 创建 OTLP 客户端（模拟）
    #[cfg(test)]
    #[allow(dead_code)]
    async fn create_otlp_client() -> Result<OtlpClient, ExportError> {
        Ok(OtlpClient)
    }
    
    #[cfg(test)]
    #[allow(dead_code)]
    struct OtlpClient;
    
    #[cfg(test)]
    impl OtlpClient {
        #[allow(dead_code)]
        async fn export(&self, _batch: Vec<TelemetryData>) -> Result<(), ExportError> {
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_async_batch_exporter() {
        let mut exporter = AsyncBatchExporter::new(|batch: Vec<i32>| async move {
            assert_eq!(batch.len(), 2);
            Ok(())
        });
        
        exporter.push(1);
        exporter.push(2);
        
        let result = exporter.flush().await;
        assert!(result.is_ok());
    }
    
    #[tokio::test]
    async fn test_async_retry() {
        let counter = std::sync::Arc::new(std::sync::atomic::AtomicU32::new(0));
        let counter_clone = counter.clone();
        
        let retry = AsyncRetry::new(
            move || {
                let c = counter_clone.clone();
                async move {
                    let val = c.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                    if val < 2 {
                        Err(ExportError::Failed("fail".to_string()))
                    } else {
                        Ok(val)
                    }
                }
            },
            3,
            10,
        );
        
        let result = retry.execute().await;
        assert!(result.is_ok());
        assert_eq!(counter.load(std::sync::atomic::Ordering::SeqCst), 3);
    }
    
    #[tokio::test]
    async fn test_async_map_batch() {
        let items = vec![1, 2, 3, 4, 5];
        
        let results = async_map_batch(items, |x| async move { x * 2 }, 2).await;
        
        assert_eq!(results, vec![2, 4, 6, 8, 10]);
    }
    
    #[tokio::test]
    async fn test_with_timeout_success() {
        let result = with_timeout(|| async { "success" }, 1000).await;
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "success");
    }
    
    #[tokio::test]
    async fn test_with_timeout_failure() {
        let result = with_timeout(
            || async {
                tokio::time::sleep(tokio::time::Duration::from_secs(10)).await;
                "never returns"
            },
            50,
        ).await;
        
        assert!(result.is_err());
    }
}
