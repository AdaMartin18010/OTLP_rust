//! # OTLP Rust 设计模式示例
//!
//! 展示在OTLP Rust中使用的主要设计模式：
//! - 建造者模式 (Builder Pattern)
//! - 装饰器模式 (Decorator Pattern)  
//! - 工厂模式 (Factory Pattern)
//! - 策略模式 (Strategy Pattern)
//! - 观察者模式 (Observer Pattern)
//! - 单例模式 (Singleton Pattern)

use anyhow::Result;
use std::sync::Arc;
use tokio::sync::RwLock;

/// ============================================
/// 1. 建造者模式 (Builder Pattern)
/// ============================================
/// 用于构建复杂的 OTLP 客户端配置

pub struct TelemetryClientBuilder {
    endpoint: String,
    timeout_ms: u64,
    retry_policy: RetryPolicy,
    compression: CompressionType,
    headers: Vec<(String, String)>,
}

#[derive(Clone)]
pub struct RetryPolicy {
    max_retries: u32,
    backoff_ms: u64,
}

#[derive(Clone)]
pub enum CompressionType {
    None,
    Gzip,
    Zstd,
}

impl TelemetryClientBuilder {
    pub fn new() -> Self {
        Self {
            endpoint: "http://localhost:4317".to_string(),
            timeout_ms: 30000,
            retry_policy: RetryPolicy {
                max_retries: 3,
                backoff_ms: 1000,
            },
            compression: CompressionType::Gzip,
            headers: Vec::new(),
        }
    }

    pub fn endpoint(mut self, endpoint: &str) -> Self {
        self.endpoint = endpoint.to_string();
        self
    }

    pub fn timeout(mut self, ms: u64) -> Self {
        self.timeout_ms = ms;
        self
    }

    pub fn retry_policy(mut self, max_retries: u32, backoff_ms: u64) -> Self {
        self.retry_policy = RetryPolicy {
            max_retries,
            backoff_ms,
        };
        self
    }

    pub fn compression(mut self, compression: CompressionType) -> Self {
        self.compression = compression;
        self
    }

    pub fn with_header(mut self, key: &str, value: &str) -> Self {
        self.headers.push((key.to_string(), value.to_string()));
        self
    }

    pub fn build(self) -> TelemetryClient {
        TelemetryClient {
            endpoint: self.endpoint,
            timeout_ms: self.timeout_ms,
            retry_policy: self.retry_policy,
            compression: self.compression,
            headers: self.headers,
        }
    }
}

pub struct TelemetryClient {
    endpoint: String,
    timeout_ms: u64,
    retry_policy: RetryPolicy,
    compression: CompressionType,
    headers: Vec<(String, String)>,
}

impl TelemetryClient {
    pub async fn send_trace(&self, trace_data: &[u8]) -> Result<()> {
        println!(
            "Sending trace to {} with {:?} compression",
            self.endpoint, self.compression
        );
        Ok(())
    }
}

/// ============================================
/// 2. 装饰器模式 (Decorator Pattern)
/// ============================================
/// 用于添加额外功能（压缩、加密、重试等）而不修改核心导出器

#[async_trait::async_trait]
pub trait SpanExporter: Send + Sync {
    async fn export(&self, spans: Vec<Span>) -> Result<()>;
}

#[derive(Clone)]
pub struct Span {
    pub trace_id: String,
    pub span_id: String,
    pub name: String,
}

/// 基础导出器
pub struct BaseExporter {
    endpoint: String,
}

#[async_trait::async_trait]
impl SpanExporter for BaseExporter {
    async fn export(&self, spans: Vec<Span>) -> Result<()> {
        println!("BaseExporter: Exporting {} spans to {}", spans.len(), self.endpoint);
        Ok(())
    }
}

/// 压缩装饰器
pub struct CompressionExporter<E: SpanExporter> {
    inner: E,
    compression_level: u32,
}

impl<E: SpanExporter> CompressionExporter<E> {
    pub fn new(inner: E, level: u32) -> Self {
        Self {
            inner,
            compression_level: level,
        }
    }
}

#[async_trait::async_trait]
impl<E: SpanExporter> SpanExporter for CompressionExporter<E> {
    async fn export(&self, spans: Vec<Span>) -> Result<()> {
        println!(
            "CompressionExporter: Compressing with level {}",
            self.compression_level
        );
        self.inner.export(spans).await
    }
}

/// 重试装饰器
pub struct RetryExporter<E: SpanExporter> {
    inner: E,
    max_retries: u32,
}

impl<E: SpanExporter> RetryExporter<E> {
    pub fn new(inner: E, max_retries: u32) -> Self {
        Self { inner, max_retries }
    }
}

#[async_trait::async_trait]
impl<E: SpanExporter> SpanExporter for RetryExporter<E> {
    async fn export(&self, spans: Vec<Span>) -> Result<()> {
        let mut attempts = 0;
        loop {
            match self.inner.export(spans.clone()).await {
                Ok(()) => return Ok(()),
                Err(e) => {
                    attempts += 1;
                    if attempts >= self.max_retries {
                        return Err(e);
                    }
                    println!("RetryExporter: Retry attempt {}", attempts);
                    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
                }
            }
        }
    }
}

/// ============================================
/// 3. 工厂模式 (Factory Pattern)
/// ============================================
/// 用于根据不同场景创建不同类型的导出器

pub enum ExporterType {
    Grpc,
    Http,
    Kafka,
    File,
}

pub struct ExporterFactory;

impl ExporterFactory {
    pub fn create(exporter_type: ExporterType, config: &str) -> Box<dyn SpanExporter> {
        match exporter_type {
            ExporterType::Grpc => Box::new(BaseExporter {
                endpoint: format!("{}/grpc", config),
            }),
            ExporterType::Http => Box::new(BaseExporter {
                endpoint: format!("{}/http", config),
            }),
            ExporterType::Kafka => Box::new(BaseExporter {
                endpoint: format!("kafka://{}", config),
            }),
            ExporterType::File => Box::new(BaseExporter {
                endpoint: format!("file://{}", config),
            }),
        }
    }
}

/// ============================================
/// 4. 策略模式 (Strategy Pattern)
/// ============================================
/// 用于在运行时切换不同的批处理策略

#[async_trait::async_trait]
pub trait BatchingStrategy: Send + Sync {
    async fn should_flush(&self, batch_size: usize, last_flush: std::time::Instant) -> bool;
}

/// 大小触发策略
pub struct SizeBasedStrategy {
    max_size: usize,
}

#[async_trait::async_trait]
impl BatchingStrategy for SizeBasedStrategy {
    async fn should_flush(&self, batch_size: usize, _last_flush: std::time::Instant) -> bool {
        batch_size >= self.max_size
    }
}

/// 时间触发策略
pub struct TimeBasedStrategy {
    max_interval: std::time::Duration,
}

#[async_trait::async_trait]
impl BatchingStrategy for TimeBasedStrategy {
    async fn should_flush(&self, _batch_size: usize, last_flush: std::time::Instant) -> bool {
        last_flush.elapsed() >= self.max_interval
    }
}

/// 混合策略
pub struct HybridStrategy {
    size_strategy: SizeBasedStrategy,
    time_strategy: TimeBasedStrategy,
}

#[async_trait::async_trait]
impl BatchingStrategy for HybridStrategy {
    async fn should_flush(&self, batch_size: usize, last_flush: std::time::Instant) -> bool {
        self.size_strategy.should_flush(batch_size, last_flush).await
            || self.time_strategy.should_flush(batch_size, last_flush).await
    }
}

/// ============================================
/// 5. 观察者模式 (Observer Pattern)
/// ============================================
/// 用于监听和处理遥测数据事件

#[derive(Clone, Debug)]
pub enum TelemetryEvent {
    SpanCreated(Span),
    SpanExported { trace_id: String, success: bool },
    ExportError { error: String },
}

#[async_trait::async_trait]
pub trait TelemetryObserver: Send + Sync {
    async fn on_event(&self, event: &TelemetryEvent);
}

/// 日志观察者
pub struct LoggingObserver;

#[async_trait::async_trait]
impl TelemetryObserver for LoggingObserver {
    async fn on_event(&self, event: &TelemetryEvent) {
        println!("[LOG] Telemetry event: {:?}", event);
    }
}

/// 指标观察者
pub struct MetricsObserver {
    counter: Arc<RwLock<u64>>,
}

impl MetricsObserver {
    pub fn new() -> Self {
        Self {
            counter: Arc::new(RwLock::new(0)),
        }
    }
}

#[async_trait::async_trait]
impl TelemetryObserver for MetricsObserver {
    async fn on_event(&self, event: &TelemetryEvent) {
        if let TelemetryEvent::SpanExported { .. } = event {
            let mut counter = self.counter.write().await;
            *counter += 1;
            println!("[METRICS] Total exported spans: {}", *counter);
        }
    }
}

/// 事件总线
pub struct TelemetryEventBus {
    observers: Vec<Box<dyn TelemetryObserver>>,
}

impl TelemetryEventBus {
    pub fn new() -> Self {
        Self {
            observers: Vec::new(),
        }
    }

    pub fn subscribe(&mut self, observer: Box<dyn TelemetryObserver>) {
        self.observers.push(observer);
    }

    pub async fn publish(&self, event: TelemetryEvent) {
        for observer in &self.observers {
            observer.on_event(&event).await;
        }
    }
}

/// ============================================
/// 6. 单例模式 (Singleton Pattern)
/// ============================================
/// 用于全局配置和连接池管理

use std::sync::OnceLock;

pub struct GlobalConfig {
    pub service_name: String,
    pub service_version: String,
    pub environment: String,
}

impl GlobalConfig {
    fn default() -> Self {
        Self {
            service_name: "unknown".to_string(),
            service_version: "0.0.0".to_string(),
            environment: "development".to_string(),
        }
    }
}

static GLOBAL_CONFIG: OnceLock<GlobalConfig> = OnceLock::new();

pub fn init_global_config(config: GlobalConfig) -> Result<()> {
    GLOBAL_CONFIG
        .set(config)
        .map_err(|_| anyhow::anyhow!("Global config already initialized"))
}

pub fn global_config() -> &'static GlobalConfig {
    GLOBAL_CONFIG.get_or_init(GlobalConfig::default)
}

/// ============================================
/// 主程序：展示所有设计模式的使用
/// ============================================

#[tokio::main]
async fn main() -> Result<()> {
    println!("=== OTLP Rust 设计模式示例 ===\n");

    // 1. 建造者模式
    println!("1. 建造者模式示例:");
    let client = TelemetryClientBuilder::new()
        .endpoint("http://otel-collector:4317")
        .timeout(5000)
        .retry_policy(5, 500)
        .compression(CompressionType::Zstd)
        .with_header("X-API-Key", "secret123")
        .with_header("X-Service", "payment-service")
        .build();
    client.send_trace(b"test data").await?;
    println!();

    // 2. 装饰器模式
    println!("2. 装饰器模式示例:");
    let base = BaseExporter {
        endpoint: "http://localhost:4317".to_string(),
    };
    let with_compression = CompressionExporter::new(base, 6);
    let with_retry = RetryExporter::new(with_compression, 3);
    
    let spans = vec![
        Span {
            trace_id: "abc123".to_string(),
            span_id: "span1".to_string(),
            name: "process_payment".to_string(),
        },
    ];
    with_retry.export(spans).await?;
    println!();

    // 3. 工厂模式
    println!("3. 工厂模式示例:");
    let grpc_exporter = ExporterFactory::create(ExporterType::Grpc, "localhost:4317");
    let http_exporter = ExporterFactory::create(ExporterType::Http, "localhost:4318");
    
    grpc_exporter.export(vec![]).await?;
    http_exporter.export(vec![]).await?;
    println!();

    // 4. 策略模式
    println!("4. 策略模式示例:");
    let size_strategy: Box<dyn BatchingStrategy> = Box::new(SizeBasedStrategy { max_size: 100 });
    let time_strategy: Box<dyn BatchingStrategy> = Box::new(TimeBasedStrategy {
        max_interval: std::time::Duration::from_secs(5),
    });
    
    let now = std::time::Instant::now();
    println!("Size strategy (batch=50): {}", size_strategy.should_flush(50, now).await);
    println!("Size strategy (batch=150): {}", size_strategy.should_flush(150, now).await);
    println!();

    // 5. 观察者模式
    println!("5. 观察者模式示例:");
    let mut event_bus = TelemetryEventBus::new();
    event_bus.subscribe(Box::new(LoggingObserver));
    event_bus.subscribe(Box::new(MetricsObserver::new()));
    
    event_bus
        .publish(TelemetryEvent::SpanCreated(Span {
            trace_id: "trace1".to_string(),
            span_id: "span1".to_string(),
            name: "db_query".to_string(),
        }))
        .await;
    
    event_bus
        .publish(TelemetryEvent::SpanExported {
            trace_id: "trace1".to_string(),
            success: true,
        })
        .await;
    println!();

    // 6. 单例模式
    println!("6. 单例模式示例:");
    init_global_config(GlobalConfig {
        service_name: "payment-service".to_string(),
        service_version: "1.2.3".to_string(),
        environment: "production".to_string(),
    })?;
    
    let config = global_config();
    println!(
        "Global config: {} {} ({})",
        config.service_name, config.service_version, config.environment
    );

    println!("\n=== 所有设计模式示例完成 ===");
    Ok(())
}
