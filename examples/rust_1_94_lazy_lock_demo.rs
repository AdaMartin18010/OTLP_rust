//! Rust 1.94 LazyLock Demo - Global Configuration & Resource Management
//!
//! This example demonstrates the `LazyLock` feature (stabilized in Rust 1.94)
//! for efficient lazy initialization of global resources.
//!
//! Features demonstrated:
//! - Global configuration initialization
//! - Connection pool lazy setup
//! - Caching patterns for telemetry data
//! - OTLP exporter singleton pattern
//!
//! Run with: cargo run --example rust_1_94_lazy_lock_demo

use std::collections::HashMap;
use std::sync::{Arc, LazyLock, Mutex, RwLock};
use std::time::{Duration, Instant};
use tokio::sync::Semaphore;

/// ============================================
/// Global Configuration with LazyLock
/// ============================================
/// Global configuration singleton using LazyLock
///
/// LazyLock initializes the configuration only on first access,
/// ensuring thread-safe lazy initialization without external crates.
/// This is a Rust 1.94 feature that replaces the need for once_cell::sync::Lazy.
static GLOBAL_CONFIG: LazyLock<RwLock<OtlpConfig>> = LazyLock::new(|| {
    println!("🔄 Initializing global configuration...");
    RwLock::new(OtlpConfig::load_from_env())
});

/// OTLP Configuration structure
#[derive(Debug, Clone)]
pub struct OtlpConfig {
    pub endpoint: String,
    pub protocol: Protocol,
    pub timeout_seconds: u64,
    pub batch_size: usize,
    pub retry_policy: RetryPolicy,
    pub headers: HashMap<String, String>,
    pub compression: CompressionType,
    pub max_queue_size: usize,
    pub export_interval_ms: u64,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Protocol {
    Grpc,
    HttpProtobuf,
    HttpJson,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum CompressionType {
    None,
    Gzip,
    Zstd,
}

#[derive(Debug, Clone, Copy)]
pub struct RetryPolicy {
    pub max_retries: u32,
    pub initial_backoff_ms: u64,
    pub max_backoff_ms: u64,
    pub backoff_multiplier: f64,
}

impl OtlpConfig {
    /// Loads configuration from environment variables with sensible defaults
    fn load_from_env() -> Self {
        use std::env;

        let endpoint =
            env::var("OTLP_ENDPOINT").unwrap_or_else(|_| "http://localhost:4317".to_string());

        let protocol = match env::var("OTLP_PROTOCOL").unwrap_or_default().as_str() {
            "grpc" => Protocol::Grpc,
            "http/protobuf" => Protocol::HttpProtobuf,
            "http/json" => Protocol::HttpJson,
            _ => Protocol::Grpc,
        };

        let timeout_seconds = env::var("OTLP_TIMEOUT")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(30);

        let batch_size = env::var("OTLP_BATCH_SIZE")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(512);

        let compression = match env::var("OTLP_COMPRESSION").unwrap_or_default().as_str() {
            "gzip" => CompressionType::Gzip,
            "zstd" => CompressionType::Zstd,
            _ => CompressionType::Gzip,
        };

        let max_queue_size = env::var("OTLP_MAX_QUEUE_SIZE")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(2048);

        let export_interval_ms = env::var("OTLP_EXPORT_INTERVAL")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(1000);

        let mut headers = HashMap::new();
        if let Ok(api_key) = env::var("OTLP_API_KEY") {
            headers.insert("x-api-key".to_string(), api_key);
        }
        if let Ok(auth) = env::var("OTLP_AUTH_TOKEN") {
            headers.insert("authorization".to_string(), format!("Bearer {}", auth));
        }

        Self {
            endpoint,
            protocol,
            timeout_seconds,
            batch_size,
            retry_policy: RetryPolicy {
                max_retries: 3,
                initial_backoff_ms: 100,
                max_backoff_ms: 5000,
                backoff_multiplier: 2.0,
            },
            headers,
            compression,
            max_queue_size,
            export_interval_ms,
        }
    }

    /// Gets a read-only reference to the global configuration
    pub fn global() -> std::sync::RwLockReadGuard<'static, OtlpConfig> {
        GLOBAL_CONFIG.read().expect("Config lock poisoned")
    }

    /// Gets a mutable reference to the global configuration
    pub fn global_mut() -> std::sync::RwLockWriteGuard<'static, OtlpConfig> {
        GLOBAL_CONFIG.write().expect("Config lock poisoned")
    }
}

/// ============================================
/// Connection Pool with LazyLock
/// ============================================
/// Global connection pool singleton using LazyLock
///
/// This demonstrates lazy initialization of an expensive resource
/// that should only be created when first needed.
static CONNECTION_POOL: LazyLock<Arc<ConnectionPool>> = LazyLock::new(|| {
    println!("🔄 Initializing connection pool...");
    let config = OtlpConfig::global();
    Arc::new(ConnectionPool::new(&config))
});

/// Simulated connection pool for OTLP exporters
pub struct ConnectionPool {
    endpoints: RwLock<Vec<PoolConnection>>,
    semaphore: Semaphore,
    max_connections: usize,
    idle_timeout: Duration,
    stats: Mutex<PoolStats>,
}

#[derive(Debug, Clone)]
pub struct PoolConnection {
    pub id: usize,
    pub endpoint: String,
    pub created_at: Instant,
    pub last_used: Instant,
    pub requests_served: u64,
}

#[derive(Debug, Default)]
pub struct PoolStats {
    pub total_connections: usize,
    pub active_connections: usize,
    pub total_requests: u64,
    pub failed_requests: u64,
}

impl ConnectionPool {
    fn new(config: &OtlpConfig) -> Self {
        let max_connections = config.max_queue_size.min(100);

        Self {
            endpoints: RwLock::new(Vec::with_capacity(max_connections)),
            semaphore: Semaphore::new(max_connections),
            max_connections,
            idle_timeout: Duration::from_secs(300),
            stats: Mutex::new(PoolStats::default()),
        }
    }

    /// Gets a connection from the pool
    pub async fn acquire(&self) -> Result<PoolConnection, PoolError> {
        let _permit = self
            .semaphore
            .acquire()
            .await
            .map_err(|_| PoolError::Closed)?;

        // Try to reuse existing connection
        {
            let mut endpoints = self.endpoints.write().map_err(|_| PoolError::Poisoned)?;
            if let Some(conn) = endpoints.pop()
                && conn.last_used.elapsed() < self.idle_timeout
            {
                // Update stats
                if let Ok(mut stats) = self.stats.lock() {
                    stats.active_connections += 1;
                }
                return Ok(conn);
            }
        }

        // Create new connection
        let conn = self.create_connection().await?;

        if let Ok(mut stats) = self.stats.lock() {
            stats.total_connections += 1;
            stats.active_connections += 1;
        }

        Ok(conn)
    }

    /// Returns a connection to the pool
    pub fn release(&self, mut conn: PoolConnection) {
        conn.last_used = Instant::now();
        conn.requests_served += 1;

        if let Ok(mut endpoints) = self.endpoints.write()
            && endpoints.len() < self.max_connections
        {
            endpoints.push(conn);
        }

        if let Ok(mut stats) = self.stats.lock() {
            stats.active_connections = stats.active_connections.saturating_sub(1);
        }
    }

    async fn create_connection(&self) -> Result<PoolConnection, PoolError> {
        use rand::Rng;

        // Simulate connection establishment
        tokio::time::sleep(Duration::from_millis(10)).await;

        let config = OtlpConfig::global();

        Ok(PoolConnection {
            id: rand::rng().random::<u64>() as usize,
            endpoint: config.endpoint.clone(),
            created_at: Instant::now(),
            last_used: Instant::now(),
            requests_served: 0,
        })
    }

    /// Gets current pool statistics
    pub fn stats(&self) -> PoolStats {
        self.stats
            .lock()
            .map(|s| PoolStats {
                total_connections: s.total_connections,
                active_connections: s.active_connections,
                total_requests: s.total_requests,
                failed_requests: s.failed_requests,
            })
            .unwrap_or_default()
    }

    /// Global accessor for the connection pool
    pub fn global() -> Arc<ConnectionPool> {
        CONNECTION_POOL.clone()
    }
}

#[derive(Debug)]
pub enum PoolError {
    Closed,
    Poisoned,
    ConnectionFailed(String),
}

impl std::fmt::Display for PoolError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PoolError::Closed => write!(f, "Connection pool is closed"),
            PoolError::Poisoned => write!(f, "Connection pool lock poisoned"),
            PoolError::ConnectionFailed(e) => write!(f, "Connection failed: {}", e),
        }
    }
}

impl std::error::Error for PoolError {}

/// ============================================
/// Telemetry Cache with LazyLock
/// ============================================
/// Global telemetry cache singleton using LazyLock
///
/// Demonstrates a caching pattern for frequently accessed telemetry metadata.
static TELEMETRY_CACHE: LazyLock<Arc<TelemetryCache>> = LazyLock::new(|| {
    println!("🔄 Initializing telemetry cache...");
    Arc::new(TelemetryCache::new())
});

/// Cache for telemetry metadata to avoid repeated lookups
pub struct TelemetryCache {
    resource_attributes: RwLock<HashMap<String, String>>,
    instrument_metadata: RwLock<HashMap<String, InstrumentInfo>>,
    span_context_cache: RwLock<HashMap<String, SpanContext>>,
    cache_hits: Mutex<u64>,
    cache_misses: Mutex<u64>,
}

#[derive(Debug, Clone)]
pub struct InstrumentInfo {
    pub name: String,
    pub description: String,
    pub unit: String,
    pub instrument_kind: InstrumentKind,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum InstrumentKind {
    Counter,
    UpDownCounter,
    Histogram,
    Gauge,
    ObservableCounter,
    ObservableGauge,
}

#[derive(Debug, Clone)]
pub struct SpanContext {
    pub trace_id: String,
    pub span_id: String,
    pub trace_flags: u8,
    pub trace_state: String,
}

impl TelemetryCache {
    fn new() -> Self {
        Self {
            resource_attributes: RwLock::new(HashMap::new()),
            instrument_metadata: RwLock::new(HashMap::new()),
            span_context_cache: RwLock::new(HashMap::new()),
            cache_hits: Mutex::new(0),
            cache_misses: Mutex::new(0),
        }
    }

    /// Gets resource attributes with caching
    pub fn get_resource_attribute(&self, key: &str) -> Option<String> {
        if let Ok(attrs) = self.resource_attributes.read()
            && let Some(value) = attrs.get(key)
        {
            if let Ok(mut hits) = self.cache_hits.lock() {
                *hits += 1;
            }
            return Some(value.clone());
        }

        if let Ok(mut misses) = self.cache_misses.lock() {
            *misses += 1;
        }

        // Simulate lookup from external source
        let value = self.lookup_resource_attribute(key);

        if let Some(ref v) = value
            && let Ok(mut attrs) = self.resource_attributes.write()
        {
            attrs.insert(key.to_string(), v.clone());
        }

        value
    }

    /// Gets instrument metadata with caching
    pub fn get_instrument_info(&self, name: &str) -> Option<InstrumentInfo> {
        if let Ok(metadata) = self.instrument_metadata.read()
            && let Some(info) = metadata.get(name)
        {
            if let Ok(mut hits) = self.cache_hits.lock() {
                *hits += 1;
            }
            return Some(info.clone());
        }

        if let Ok(mut misses) = self.cache_misses.lock() {
            *misses += 1;
        }

        // Simulate lookup
        let info = self.lookup_instrument_info(name);

        if let Some(ref i) = info
            && let Ok(mut metadata) = self.instrument_metadata.write()
        {
            metadata.insert(name.to_string(), i.clone());
        }

        info
    }

    /// Caches span context for efficient propagation
    pub fn cache_span_context(&self, operation: &str, context: SpanContext) {
        if let Ok(mut cache) = self.span_context_cache.write() {
            cache.insert(operation.to_string(), context);
        }
    }

    /// Gets cached span context
    pub fn get_span_context(&self, operation: &str) -> Option<SpanContext> {
        if let Ok(cache) = self.span_context_cache.read()
            && let Some(ctx) = cache.get(operation)
        {
            if let Ok(mut hits) = self.cache_hits.lock() {
                *hits += 1;
            }
            return Some(ctx.clone());
        }

        if let Ok(mut misses) = self.cache_misses.lock() {
            *misses += 1;
        }

        None
    }

    /// Returns cache statistics
    pub fn stats(&self) -> CacheStats {
        let hits = self.cache_hits.lock().map(|h| *h).unwrap_or(0);
        let misses = self.cache_misses.lock().map(|m| *m).unwrap_or(0);
        let total = hits + misses;

        CacheStats {
            hits,
            misses,
            hit_rate: if total > 0 {
                hits as f64 / total as f64
            } else {
                0.0
            },
            resource_attributes_count: self
                .resource_attributes
                .read()
                .map(|m| m.len())
                .unwrap_or(0),
            instrument_count: self
                .instrument_metadata
                .read()
                .map(|m| m.len())
                .unwrap_or(0),
            span_context_count: self.span_context_cache.read().map(|m| m.len()).unwrap_or(0),
        }
    }

    fn lookup_resource_attribute(&self, key: &str) -> Option<String> {
        // Simulate external lookup
        match key {
            "service.name" => Some("otlp-demo-service".to_string()),
            "service.version" => Some("1.0.0".to_string()),
            "deployment.environment" => Some("production".to_string()),
            _ => None,
        }
    }

    fn lookup_instrument_info(&self, name: &str) -> Option<InstrumentInfo> {
        // Simulate external lookup
        match name {
            "http.server.duration" => Some(InstrumentInfo {
                name: name.to_string(),
                description: "HTTP server request duration".to_string(),
                unit: "ms".to_string(),
                instrument_kind: InstrumentKind::Histogram,
            }),
            "http.server.active_requests" => Some(InstrumentInfo {
                name: name.to_string(),
                description: "Number of active HTTP requests".to_string(),
                unit: "1".to_string(),
                instrument_kind: InstrumentKind::UpDownCounter,
            }),
            _ => None,
        }
    }

    /// Global accessor for the telemetry cache
    pub fn global() -> Arc<TelemetryCache> {
        TELEMETRY_CACHE.clone()
    }
}

#[derive(Debug)]
pub struct CacheStats {
    pub hits: u64,
    pub misses: u64,
    pub hit_rate: f64,
    pub resource_attributes_count: usize,
    pub instrument_count: usize,
    pub span_context_count: usize,
}

/// ============================================
/// OTLP Exporter Singleton
/// ============================================
/// Global OTLP exporter singleton using LazyLock
///
/// Demonstrates the singleton pattern for expensive resources
/// that should be shared across the application.
static OTLP_EXPORTER: LazyLock<Arc<OtlpExporter>> = LazyLock::new(|| {
    println!("🔄 Initializing OTLP exporter...");
    Arc::new(OtlpExporter::new())
});

/// OTLP exporter with lazy initialization
pub struct OtlpExporter {
    config: OtlpConfig,
    connection_pool: Arc<ConnectionPool>,
    cache: Arc<TelemetryCache>,
    shutdown_signal: Mutex<bool>,
}

impl OtlpExporter {
    fn new() -> Self {
        let config = OtlpConfig::global();
        let connection_pool = ConnectionPool::global();
        let cache = TelemetryCache::global();

        Self {
            config: config.clone(),
            connection_pool,
            cache,
            shutdown_signal: Mutex::new(false),
        }
    }

    /// Exports telemetry data
    pub async fn export(&self, data: TelemetryData) -> Result<ExportResult, ExportError> {
        // Check shutdown signal
        if *self
            .shutdown_signal
            .lock()
            .map_err(|_| ExportError::Internal)?
        {
            return Err(ExportError::Shutdown);
        }

        // Acquire connection from pool
        let conn = self
            .connection_pool
            .acquire()
            .await
            .map_err(|e| ExportError::Connection(e.to_string()))?;

        println!(
            "   📤 Exporting {} items using connection #{}",
            data.items.len(),
            conn.id
        );

        // Simulate export
        tokio::time::sleep(Duration::from_millis(5)).await;

        // Release connection back to pool
        self.connection_pool.release(conn);

        Ok(ExportResult {
            exported: data.items.len(),
            failed: 0,
            duration_ms: 5,
        })
    }

    /// Gets exporter statistics
    pub fn stats(&self) -> ExporterStats {
        ExporterStats {
            endpoint: self.config.endpoint.clone(),
            protocol: format!("{:?}", self.config.protocol),
            pool_stats: self.connection_pool.stats(),
            cache_stats: self.cache.stats(),
        }
    }

    /// Gracefully shuts down the exporter
    pub fn shutdown(&self) -> Result<(), ExportError> {
        if let Ok(mut signal) = self.shutdown_signal.lock() {
            *signal = true;
        }
        Ok(())
    }

    /// Global accessor for the OTLP exporter
    pub fn global() -> Arc<OtlpExporter> {
        OTLP_EXPORTER.clone()
    }
}

#[derive(Debug)]
pub struct TelemetryData {
    pub items: Vec<TelemetryItem>,
}

#[derive(Debug)]
pub enum TelemetryItem {
    Metric(MetricData),
    Trace(TraceData),
    Log(LogData),
}

#[derive(Debug)]
pub struct MetricData {
    pub name: String,
    pub value: f64,
    pub timestamp: u64,
}

#[derive(Debug)]
pub struct TraceData {
    pub trace_id: String,
    pub span_id: String,
    pub operation: String,
}

#[derive(Debug)]
pub struct LogData {
    pub level: String,
    pub message: String,
    pub timestamp: u64,
}

#[derive(Debug)]
pub struct ExportResult {
    pub exported: usize,
    pub failed: usize,
    pub duration_ms: u64,
}

#[derive(Debug)]
pub enum ExportError {
    Connection(String),
    Shutdown,
    Internal,
}

impl std::fmt::Display for ExportError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExportError::Connection(e) => write!(f, "Connection error: {}", e),
            ExportError::Shutdown => write!(f, "Exporter is shutting down"),
            ExportError::Internal => write!(f, "Internal error"),
        }
    }
}

impl std::error::Error for ExportError {}

#[derive(Debug)]
pub struct ExporterStats {
    pub endpoint: String,
    pub protocol: String,
    pub pool_stats: PoolStats,
    pub cache_stats: CacheStats,
}

/// ============================================
/// Main Demo
/// ============================================
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("╔══════════════════════════════════════════════════════════╗");
    println!("║      Rust 1.94 LazyLock Demo - OTLP Resource Mgmt        ║");
    println!("║        Lazy Initialization & Singleton Patterns          ║");
    println!("╚══════════════════════════════════════════════════════════╝");

    // Section 1: Configuration Access
    println!("\n📋 Section 1: Global Configuration Access");
    println!("   (Configuration will be lazily initialized on first access)");

    {
        let config = OtlpConfig::global();
        println!("   ✅ Configuration loaded:");
        println!("      - Endpoint: {}", config.endpoint);
        println!("      - Protocol: {:?}", config.protocol);
        println!("      - Timeout: {}s", config.timeout_seconds);
        println!("      - Batch size: {}", config.batch_size);
        println!("      - Compression: {:?}", config.compression);
    }

    // Section 2: Connection Pool
    println!("\n🔌 Section 2: Connection Pool");
    println!("   (Pool will be lazily initialized on first access)");

    // Simulate multiple concurrent requests
    let mut handles = vec![];

    for i in 0..5 {
        let handle = tokio::spawn(async move {
            let pool = ConnectionPool::global();
            match pool.acquire().await {
                Ok(conn) => {
                    println!("   ✅ Request {} acquired connection #{}", i + 1, conn.id);
                    tokio::time::sleep(Duration::from_millis(20)).await;
                    pool.release(conn);
                    println!("   🔄 Request {} released connection", i + 1);
                }
                Err(e) => {
                    println!("   ❌ Request {} failed: {}", i + 1, e);
                }
            }
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.await?;
    }

    let pool_stats = ConnectionPool::global().stats();
    println!("   📊 Pool stats: {:?}", pool_stats);

    // Section 3: Telemetry Cache
    println!("\n💾 Section 3: Telemetry Cache");
    println!("   (Cache will be lazily initialized on first access)");

    let cache = TelemetryCache::global();

    // First access - cache miss
    println!("   First access (cache miss expected):");
    let attr1 = cache.get_resource_attribute("service.name");
    println!("      service.name = {:?}", attr1);

    // Second access - cache hit
    println!("   Second access (cache hit expected):");
    let attr2 = cache.get_resource_attribute("service.name");
    println!("      service.name = {:?}", attr2);

    // Instrument metadata
    let instrument = cache.get_instrument_info("http.server.duration");
    println!("   Instrument info: {:?}", instrument);

    // Span context caching
    cache.cache_span_context(
        "process_order",
        SpanContext {
            trace_id: "abc123".to_string(),
            span_id: "def456".to_string(),
            trace_flags: 1,
            trace_state: "vendor=otlp".to_string(),
        },
    );

    let span_ctx = cache.get_span_context("process_order");
    println!("   Cached span context: {:?}", span_ctx);

    let cache_stats = cache.stats();
    println!("   📊 Cache stats: {:?}", cache_stats);

    // Section 4: OTLP Exporter
    println!("\n📤 Section 4: OTLP Exporter");
    println!("   (Exporter will be lazily initialized on first access)");

    let exporter = OtlpExporter::global();

    // Create sample telemetry data
    let telemetry = TelemetryData {
        items: vec![
            TelemetryItem::Metric(MetricData {
                name: "http.requests".to_string(),
                value: 100.0,
                timestamp: 1234567890,
            }),
            TelemetryItem::Metric(MetricData {
                name: "http.latency".to_string(),
                value: 45.5,
                timestamp: 1234567890,
            }),
            TelemetryItem::Trace(TraceData {
                trace_id: "trace-001".to_string(),
                span_id: "span-001".to_string(),
                operation: "GET /api/users".to_string(),
            }),
        ],
    };

    // Export data
    match exporter.export(telemetry).await {
        Ok(result) => {
            println!("   ✅ Export successful:");
            println!("      - Exported: {} items", result.exported);
            println!("      - Duration: {} ms", result.duration_ms);
        }
        Err(e) => {
            println!("   ❌ Export failed: {}", e);
        }
    }

    let exporter_stats = exporter.stats();
    println!("   📊 Exporter stats: {:?}", exporter_stats);

    // Section 5: Configuration Mutation
    println!("\n⚙️  Section 5: Dynamic Configuration Update");

    {
        let mut config = OtlpConfig::global_mut();
        config.batch_size = 1024;
        println!("   ✅ Updated batch_size to {}", config.batch_size);
    }

    {
        let config = OtlpConfig::global();
        println!("   ✅ Verified batch_size: {}", config.batch_size);
    }

    // Summary
    println!("\n╔══════════════════════════════════════════════════════════╗");
    println!("║                       Summary                            ║");
    println!("╚══════════════════════════════════════════════════════════╝");
    println!("  LazyLock provides:");
    println!("  - Thread-safe lazy initialization");
    println!("  - Zero-cost abstraction after initialization");
    println!("  - No external crate dependencies");
    println!("  - Drop-in replacement for once_cell::sync::Lazy");
    println!();
    println!("  Applications in OTLP:");
    println!("  - Global configuration management");
    println!("  - Connection pool singleton");
    println!("  - Telemetry metadata caching");
    println!("  - Exporter resource sharing");

    println!("\n✅ LazyLock demo completed successfully!");

    Ok(())
}

/// Unit tests
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_config_loading() {
        let config = OtlpConfig::load_from_env();
        assert!(!config.endpoint.is_empty());
        assert!(config.batch_size > 0);
        assert!(config.timeout_seconds > 0);
    }

    #[test]
    fn test_cache_operations() {
        let cache = TelemetryCache::new();

        // Test resource attribute caching
        let attr = cache.get_resource_attribute("service.name");
        assert!(attr.is_some());

        // Test cache hit
        let attr2 = cache.get_resource_attribute("service.name");
        assert_eq!(attr, attr2);

        let stats = cache.stats();
        assert!(stats.hits > 0);
        assert!(stats.misses > 0);
    }

    #[tokio::test]
    async fn test_connection_pool() {
        let config = OtlpConfig::load_from_env();
        let pool = ConnectionPool::new(&config);

        // Acquire and release connection
        let conn = pool.acquire().await.unwrap();
        let conn_id = conn.id;
        pool.release(conn);

        // Reacquire should potentially reuse
        let conn2 = pool.acquire().await.unwrap();
        pool.release(conn2);

        let stats = pool.stats();
        assert!(stats.total_connections > 0);
    }
}
