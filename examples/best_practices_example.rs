//! # OTLP Rust 最佳实践示例
//!
//! 展示使用 OTLP Rust 的推荐实践：
//! - 错误处理策略
//! - 资源管理
//! - 并发控制
//! - 性能优化
//! - 测试策略
//! - 配置管理

use anyhow::{Context, Result};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{mpsc, oneshot, Semaphore};
use tokio::time::timeout;

/// ============================================
/// 1. 错误处理策略
/// ============================================

/// 使用 thiserror 定义明确的错误类型
#[derive(thiserror::Error, Debug)]
pub enum TelemetryError {
    #[error("Export failed: {0}")]
    ExportFailed(String),
    
    #[error("Configuration error: {0}")]
    ConfigError(String),
    
    #[error("Resource exhausted: {0}")]
    ResourceExhausted(String),
    
    #[error("Timeout after {0}ms")]
    Timeout(u64),
    
    #[error(transparent)]
    Other(#[from] anyhow::Error),
}

/// 带上下文的错误处理
pub async fn export_with_context(data: &[u8], endpoint: &str) -> Result<(), TelemetryError> {
    // 使用 .context() 添加上下文信息
    let client = reqwest::Client::new()
        .post(endpoint)
        .body(data.to_vec())
        .build()
        .context("Failed to build HTTP request")
        .map_err(|e| TelemetryError::ExportFailed(e.to_string()))?;

    // 使用 anyhow 的 ? 操作符传播错误
    let response = reqwest::Client::new()
        .execute(client)
        .await
        .context("HTTP request failed")
        .map_err(|e| TelemetryError::ExportFailed(e.to_string()))?;

    if !response.status().is_success() {
        return Err(TelemetryError::ExportFailed(
            format!("HTTP {}", response.status())
        ));
    }

    Ok(())
}

/// 错误分类和恢复策略
pub enum RecoveryStrategy {
    Retry { max_attempts: u32, backoff: Duration },
    Drop,
    DeadLetterQueue,
}

pub async fn export_with_recovery<F, Fut>(
    operation: F,
    strategy: RecoveryStrategy,
) -> Result<()>
where
    F: Fn() -> Fut + Send + Sync,
    Fut: std::future::Future<Output = Result<()>> + Send,
{
    match strategy {
        RecoveryStrategy::Retry { max_attempts, backoff } => {
            for attempt in 0..max_attempts {
                match operation().await {
                    Ok(()) => return Ok(()),
                    Err(e) => {
                        if attempt < max_attempts - 1 {
                            println!("Retry attempt {} after {:?}: {}", attempt + 1, backoff, e);
                            tokio::time::sleep(backoff * (attempt + 1)).await;
                        } else {
                            return Err(e);
                        }
                    }
                }
            }
            Err(anyhow::anyhow!("Max retries exceeded"))
        }
        RecoveryStrategy::Drop => {
            // 静默丢弃错误
            let _ = operation().await;
            Ok(())
        }
        RecoveryStrategy::DeadLetterQueue => {
            if let Err(e) = operation().await {
                println!("Sending to DLQ: {}", e);
                // 实际实现中发送到死信队列
            }
            Ok(())
        }
    }
}

/// ============================================
/// 2. 资源管理
/// ============================================

/// 使用 RAII 模式管理资源
pub struct ManagedBuffer {
    data: Vec<u8>,
    max_size: usize,
    current_size: usize,
}

impl ManagedBuffer {
    pub fn new(max_size: usize) -> Self {
        Self {
            data: Vec::with_capacity(max_size),
            max_size,
            current_size: 0,
        }
    }

    pub fn try_push(&mut self, item: &[u8]) -> Result<bool> {
        if self.current_size + item.len() > self.max_size {
            Ok(false) // 缓冲区已满
        } else {
            self.data.extend_from_slice(item);
            self.current_size += item.len();
            Ok(true)
        }
    }

    pub fn clear(&mut self) {
        self.data.clear();
        self.current_size = 0;
    }

    pub fn is_full(&self) -> bool {
        self.current_size >= self.max_size * 9 / 10 // 90% 满
    }
}

/// 使用 Drop trait 确保资源释放
pub struct SpanGuard {
    name: String,
    start: Instant,
    exporter: mpsc::UnboundedSender<CompletedSpan>,
}

#[derive(Debug)]
pub struct CompletedSpan {
    pub name: String,
    pub duration_ms: u64,
}

impl SpanGuard {
    pub fn new(name: &str, exporter: mpsc::UnboundedSender<CompletedSpan>) -> Self {
        Self {
            name: name.to_string(),
            start: Instant::now(),
            exporter,
        }
    }
}

impl Drop for SpanGuard {
    fn drop(&mut self) {
        let duration = self.start.elapsed().as_millis() as u64;
        let _ = self.exporter.send(CompletedSpan {
            name: self.name.clone(),
            duration_ms: duration,
        });
    }
}

/// ============================================
/// 3. 并发控制
/// ============================================

/// 使用信号量限制并发
pub struct ConcurrencyLimitedExporter {
    semaphore: Arc<Semaphore>,
    client: reqwest::Client,
}

impl ConcurrencyLimitedExporter {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
            client: reqwest::Client::new(),
        }
    }

    pub async fn export(&self, data: Vec<u8>, endpoint: &str) -> Result<()> {
        // 获取许可，限制并发
        let _permit = self.semaphore.acquire().await?;
        
        let response = self.client
            .post(endpoint)
            .body(data)
            .send()
            .await?;

        if !response.status().is_success() {
            return Err(anyhow::anyhow!("Export failed: {}", response.status()));
        }

        Ok(())
    }
}

/// 使用通道进行消息传递
pub struct PipelineStage<T> {
    input: mpsc::Receiver<T>,
    output: mpsc::Sender<T>,
    buffer_size: usize,
}

impl<T: Send + 'static> PipelineStage<T> {
    pub fn new(buffer_size: usize) -> (Self, mpsc::Sender<T>, mpsc::Receiver<T>) {
        let (input_tx, input_rx) = mpsc::channel(buffer_size);
        let (output_tx, output_rx) = mpsc::channel(buffer_size);

        let stage = Self {
            input: input_rx,
            output: output_tx,
            buffer_size,
        };

        (stage, input_tx, output_rx)
    }

    pub async fn run<F>(mut self, processor: F)
    where
        F: Fn(T) -> T + Send + Sync + 'static,
    {
        while let Some(item) = self.input.recv().await {
            let processed = processor(item);
            if self.output.send(processed).await.is_err() {
                break;
            }
        }
    }
}

/// 批处理优化
pub struct BatchProcessor<T> {
    buffer: Vec<T>,
    max_batch_size: usize,
    max_wait_time: Duration,
    flush_sender: mpsc::Sender<Vec<T>>,
}

impl<T: Clone + Send + 'static> BatchProcessor<T> {
    pub fn new(max_batch_size: usize, max_wait_time: Duration) -> (Self, mpsc::Receiver<Vec<T>>) {
        let (flush_sender, flush_receiver) = mpsc::channel(100);

        let processor = Self {
            buffer: Vec::with_capacity(max_batch_size),
            max_batch_size,
            max_wait_time,
            flush_sender,
        };

        (processor, flush_receiver)
    }

    pub async fn push(&mut self, item: T) -> Result<()> {
        self.buffer.push(item);

        if self.buffer.len() >= self.max_batch_size {
            self.flush().await?;
        }

        Ok(())
    }

    pub async fn flush(&mut self) -> Result<()> {
        if !self.buffer.is_empty() {
            let batch = std::mem::replace(&mut self.buffer, Vec::with_capacity(self.max_batch_size));
            self.flush_sender.send(batch).await?;
        }
        Ok(())
    }

    pub async fn run_with_timeout(mut self, mut input: mpsc::Receiver<T>) {
        let mut interval = tokio::time::interval(self.max_wait_time);

        loop {
            tokio::select! {
                Some(item) = input.recv() => {
                    if let Err(_) = self.push(item).await {
                        break;
                    }
                }
                _ = interval.tick() => {
                    if let Err(_) = self.flush().await {
                        break;
                    }
                }
            }
        }
    }
}

/// ============================================
/// 4. 性能优化
/// ============================================

/// 对象池模式减少分配
pub struct ObjectPool<T> {
    objects: std::sync::Mutex<Vec<T>>,
    creator: Box<dyn Fn() -> T + Send + Sync>,
}

impl<T> ObjectPool<T> {
    pub fn new<F>(capacity: usize, creator: F) -> Self
    where
        F: Fn() -> T + Send + Sync + 'static,
    {
        let objects: Vec<T> = (0..capacity).map(|_| creator()).collect();
        
        Self {
            objects: std::sync::Mutex::new(objects),
            creator: Box::new(creator),
        }
    }

    pub fn acquire(&self) -> PooledObject<T> {
        let object = self.objects.lock().unwrap().pop();
        PooledObject {
            object: object.unwrap_or_else(|| (self.creator)()),
            pool: self,
        }
    }

    fn release(&self, object: T) {
        self.objects.lock().unwrap().push(object);
    }
}

pub struct PooledObject<'a, T> {
    object: T,
    pool: &'a ObjectPool<T>,
}

impl<'a, T> std::ops::Deref for PooledObject<'a, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.object
    }
}

impl<'a, T> std::ops::DerefMut for PooledObject<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.object
    }
}

impl<'a, T> Drop for PooledObject<'a, T> {
    fn drop(&mut self) {
        // 重置对象状态并归还到池中
        self.pool.release(unsafe { std::ptr::read(&self.object) });
    }
}

/// 零拷贝序列化
pub fn serialize_without_copy(data: &HashMap<String, String>) -> Vec<u8> {
    // 使用 Cap'n Proto 或 FlatBuffers 进行零拷贝序列化
    // 这里简化示例使用 bincode
    bincode::serialize(data).unwrap_or_default()
}

/// 内存预分配
pub fn preallocate_buffers(count: usize, size: usize) -> Vec<Vec<u8>> {
    (0..count)
        .map(|_| {
            let mut buf = Vec::with_capacity(size);
            buf.resize(size, 0);
            buf
        })
        .collect()
}

/// ============================================
/// 5. 测试策略
/// ============================================

#[cfg(test)]
mod tests {
    use super::*;

    /// 单元测试
    #[test]
    fn test_managed_buffer_push() {
        let mut buffer = ManagedBuffer::new(100);
        
        assert!(buffer.try_push(b"small data").unwrap());
        assert_eq!(buffer.current_size, 10);
    }

    /// 使用 mock 进行测试
    pub struct MockExporter {
        exported_data: std::sync::Mutex<Vec<Vec<u8>>>,
        should_fail: bool,
    }

    impl MockExporter {
        pub async fn export(&self, data: &[u8]) -> Result<()> {
            if self.should_fail {
                return Err(anyhow::anyhow!("Mock export failure"));
            }
            self.exported_data.lock().unwrap().push(data.to_vec());
            Ok(())
        }

        pub fn get_exported(&self) -> Vec<Vec<u8>> {
            self.exported_data.lock().unwrap().clone()
        }
    }

    #[tokio::test]
    async fn test_export_with_retry() {
        let exporter = Arc::new(MockExporter {
            exported_data: std::sync::Mutex::new(Vec::new()),
            should_fail: false,
        });

        let result = export_with_recovery(
            || async {
                let data = b"test data";
                exporter.export(data).await
            },
            RecoveryStrategy::Retry {
                max_attempts: 3,
                backoff: Duration::from_millis(10),
            },
        ).await;

        assert!(result.is_ok());
        assert_eq!(exporter.get_exported().len(), 1);
    }

    /// 集成测试
    #[tokio::test]
    async fn test_concurrent_export() {
        let exporter = ConcurrencyLimitedExporter::new(2);
        
        let mut handles = vec![];
        for i in 0..5 {
            let exporter = ConcurrencyLimitedExporter::new(2);
            handles.push(tokio::spawn(async move {
                // 模拟导出操作
                tokio::time::sleep(Duration::from_millis(10)).await;
                i
            }));
        }

        for handle in handles {
            let _ = handle.await.unwrap();
        }
    }
}

/// ============================================
/// 6. 配置管理
/// ============================================

/// 分层配置
#[derive(Debug, Clone)]
pub struct TelemetryConfig {
    pub endpoint: String,
    pub timeout_ms: u64,
    pub retry: RetryConfig,
    pub batch: BatchConfig,
    pub resource: ResourceConfig,
}

#[derive(Debug, Clone)]
pub struct RetryConfig {
    pub max_attempts: u32,
    pub initial_backoff_ms: u64,
    pub max_backoff_ms: u64,
}

#[derive(Debug, Clone)]
pub struct BatchConfig {
    pub max_size: usize,
    pub max_wait_ms: u64,
}

#[derive(Debug, Clone)]
pub struct ResourceConfig {
    pub service_name: String,
    pub service_version: String,
    pub attributes: HashMap<String, String>,
}

impl TelemetryConfig {
    /// 从环境变量加载配置
    pub fn from_env() -> Result<Self> {
        Ok(Self {
            endpoint: std::env::var("OTEL_EXPORTER_ENDPOINT")
                .unwrap_or_else(|_| "http://localhost:4317".to_string()),
            timeout_ms: std::env::var("OTEL_EXPORTER_TIMEOUT_MS")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(30000),
            retry: RetryConfig {
                max_attempts: std::env::var("OTEL_RETRY_MAX_ATTEMPTS")
                    .ok()
                    .and_then(|s| s.parse().ok())
                    .unwrap_or(3),
                initial_backoff_ms: 100,
                max_backoff_ms: 5000,
            },
            batch: BatchConfig {
                max_size: std::env::var("OTEL_BATCH_MAX_SIZE")
                    .ok()
                    .and_then(|s| s.parse().ok())
                    .unwrap_or(512),
                max_wait_ms: std::env::var("OTEL_BATCH_MAX_WAIT_MS")
                    .ok()
                    .and_then(|s| s.parse().ok())
                    .unwrap_or(1000),
            },
            resource: ResourceConfig {
                service_name: std::env::var("OTEL_SERVICE_NAME")
                    .unwrap_or_else(|_| "unknown-service".to_string()),
                service_version: std::env::var("OTEL_SERVICE_VERSION")
                    .unwrap_or_else(|_| "0.0.0".to_string()),
                attributes: Self::parse_attributes(),
            },
        })
    }

    /// 从文件加载配置
    pub fn from_file(path: &str) -> Result<Self> {
        let content = std::fs::read_to_string(path)
            .context("Failed to read config file")?;
        
        // 使用 serde 解析 YAML/JSON
        // let config: TelemetryConfig = serde_yaml::from_str(&content)?;
        
        // 简化为默认配置
        Ok(Self::default())
    }

    /// 配置验证
    pub fn validate(&self) -> Result<()> {
        if self.endpoint.is_empty() {
            return Err(anyhow::anyhow!("Endpoint cannot be empty"));
        }
        if self.timeout_ms == 0 {
            return Err(anyhow::anyhow!("Timeout must be greater than 0"));
        }
        if self.retry.max_attempts == 0 {
            return Err(anyhow::anyhow!("Max attempts must be greater than 0"));
        }
        Ok(())
    }

    fn parse_attributes() -> HashMap<String, String> {
        let mut attrs = HashMap::new();
        if let Ok(val) = std::env::var("OTEL_RESOURCE_ATTRIBUTES") {
            for pair in val.split(',') {
                let parts: Vec<&str> = pair.splitn(2, '=').collect();
                if parts.len() == 2 {
                    attrs.insert(parts[0].to_string(), parts[1].to_string());
                }
            }
        }
        attrs
    }
}

impl Default for TelemetryConfig {
    fn default() -> Self {
        Self {
            endpoint: "http://localhost:4317".to_string(),
            timeout_ms: 30000,
            retry: RetryConfig {
                max_attempts: 3,
                initial_backoff_ms: 100,
                max_backoff_ms: 5000,
            },
            batch: BatchConfig {
                max_size: 512,
                max_wait_ms: 1000,
            },
            resource: ResourceConfig {
                service_name: "default-service".to_string(),
                service_version: "0.0.0".to_string(),
                attributes: HashMap::new(),
            },
        }
    }
}

/// ============================================
/// 演示主程序
/// ============================================

#[tokio::main]
async fn main() -> Result<()> {
    println!("=== OTLP Rust 最佳实践示例 ===\n");

    // 1. 加载配置
    println!("1. 配置管理:");
    let config = TelemetryConfig::from_env().unwrap_or_default();
    println!("   Endpoint: {}", config.endpoint);
    println!("   Service: {}", config.resource.service_name);
    config.validate()?;
    println!("   ✅ 配置验证通过\n");

    // 2. 错误处理
    println!("2. 错误处理与恢复:");
    let result = export_with_recovery(
        || async {
            println!("   执行导出操作...");
            Ok(())
        },
        RecoveryStrategy::Retry {
            max_attempts: 3,
            backoff: Duration::from_millis(100),
        },
    ).await;
    println!("   ✅ 结果: {:?}\n", result.is_ok());

    // 3. 资源管理
    println!("3. 资源管理 (RAII):");
    let (tx, mut rx) = mpsc::unbounded_channel();
    {
        let _span = SpanGuard::new("example_operation", tx);
        println!("   执行操作...");
        tokio::time::sleep(Duration::from_millis(10)).await;
    } // SpanGuard 在这里自动 drop，发送完成事件
    
    if let Some(completed) = rx.recv().await {
        println!("   ✅ Span 完成: {} ({}ms)\n", completed.name, completed.duration_ms);
    }

    // 4. 并发控制
    println!("4. 并发控制 (信号量):");
    let exporter = ConcurrencyLimitedExporter::new(3);
    let start = Instant::now();
    
    let mut handles = vec![];
    for i in 0..5 {
        let exporter = ConcurrencyLimitedExporter::new(3);
        handles.push(tokio::spawn(async move {
            tokio::time::sleep(Duration::from_millis(50)).await;
            println!("   任务 {} 完成", i);
        }));
    }
    
    for h in handles {
        h.await?;
    }
    println!("   ✅ 所有任务完成，总耗时: {}ms\n", start.elapsed().as_millis());

    // 5. 性能优化
    println!("5. 性能优化 (对象池):");
    let pool = Arc::new(ObjectPool::new(5, || vec![0u8; 1024]));
    
    for i in 0..3 {
        let pool = pool.clone();
        let mut buffer = pool.acquire();
        buffer[0] = i as u8;
        println!("   使用缓冲区 {}, 首字节: {}", i, buffer[0]);
        // buffer 在这里自动归还到池中
    }
    println!("   ✅ 对象池使用完成\n");

    // 6. 批处理
    println!("6. 批处理优化:");
    let (mut processor, mut receiver) = BatchProcessor::<String>::new(3, Duration::from_millis(100));
    let (input_tx, input_rx) = mpsc::channel(10);
    
    tokio::spawn(async move {
        processor.run_with_timeout(input_rx).await;
    });
    
    for i in 0..7 {
        input_tx.send(format!("item_{}", i)).await?;
    }
    
    tokio::time::sleep(Duration::from_millis(200)).await;
    
    let mut batch_count = 0;
    while let Ok(batch) = receiver.try_recv() {
        println!("   批 {}: {:?}", batch_count, batch);
        batch_count += 1;
    }
    println!("   ✅ 处理了 {} 个批次\n", batch_count);

    println!("=== 示例完成 ===");
    Ok(())
}
