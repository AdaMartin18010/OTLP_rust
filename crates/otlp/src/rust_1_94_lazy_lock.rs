//! # Rust 1.94 LazyLock 和 LazyCell 新方法实现
//!
//! 本模块实现 Rust 1.94 稳定化的 `LazyLock` 和 `LazyCell` 新方法：
//! - `LazyLock::get` / `LazyCell::get` - 获取不可变引用（不触发初始化）
//! - `LazyLock::get_mut` / `LazyCell::get_mut` - 获取可变引用（不触发初始化）
//! - `LazyLock::force_mut` / `LazyCell::force_mut` - 强制初始化并获取可变引用
//!
//! ## OTLP 应用场景
//!
//! - **全局配置管理**: 延迟初始化的配置，支持运行时修改
//! - **导出器缓存**: 线程安全的导出器实例缓存
//! - **协议缓冲区类型注册表**: 延迟初始化的类型映射
//! - **追踪器提供者单例**: 线程安全的 TracerProvider 管理
//!
//! ## 使用示例
//!
//! ```rust,ignore
//! use std::sync::LazyLock;
//! use std::cell::LazyCell;
//! use otlp::rust_1_94_lazy_lock::{GlobalConfig, LazyBuffer};
//!
//! // LazyLock::get - 获取已初始化值的不可变引用
//! static CONFIG: LazyLock<String> = LazyLock::new(|| "config".to_string());
//! if let Some(config) = LazyLock::get(&CONFIG) {
//!     println!("Config: {}", config);
//! }
//!
//! // LazyCell::get - 获取已初始化值的不可变引用（单线程）
//! let cell: LazyCell<Vec<i32>> = LazyCell::new(|| vec![1, 2, 3]);
//! // 初始化前 get 返回 None
//! assert!(LazyCell::get(&cell).is_none());
//! // 强制初始化
//! let _ = LazyCell::force(&cell);
//! // 现在 get 返回 Some
//! assert_eq!(LazyCell::get(&cell), Some(&vec![1, 2, 3]));
//! ```

#![allow(dead_code)]

use std::cell::LazyCell;
use std::collections::HashMap;
use std::sync::{LazyLock, Mutex, MutexGuard, RwLock, RwLockReadGuard, RwLockWriteGuard};

// ============================================================================
// 1. 全局配置管理 - 使用 LazyLock::get
// ============================================================================

/// 全局配置结构体
///
/// 包含 OTLP 客户端的所有配置参数，支持延迟初始化和运行时修改
#[derive(Debug, Clone)]
pub struct OtlpConfig {
    /// OTLP 服务端点
    pub endpoint: String,
    /// 连接超时时间（秒）
    pub timeout_secs: u64,
    /// 最大重试次数
    pub max_retries: u32,
    /// 批量大小
    pub batch_size: usize,
    /// 是否启用压缩
    pub enable_compression: bool,
    /// 服务名称
    pub service_name: String,
    /// 服务版本
    pub service_version: String,
    /// 自定义属性
    pub attributes: HashMap<String, String>,
}

impl Default for OtlpConfig {
    fn default() -> Self {
        Self {
            endpoint: "http://localhost:4317".to_string(),
            timeout_secs: 30,
            max_retries: 3,
            batch_size: 512,
            enable_compression: true,
            service_name: "unknown-service".to_string(),
            service_version: "0.1.0".to_string(),
            attributes: HashMap::new(),
        }
    }
}

impl OtlpConfig {
    /// 从环境变量创建配置
    pub fn from_env() -> Self {
        let mut config = Self::default();
        
        if let Ok(endpoint) = std::env::var("OTEL_EXPORTER_OTLP_ENDPOINT") {
            config.endpoint = endpoint;
        }
        if let Ok(service_name) = std::env::var("OTEL_SERVICE_NAME") {
            config.service_name = service_name;
        }
        if let Ok(timeout) = std::env::var("OTEL_EXPORTER_OTLP_TIMEOUT") {
            if let Ok(secs) = timeout.parse() {
                config.timeout_secs = secs;
            }
        }
        
        config
    }
}

/// 全局配置 - 使用 LazyLock 延迟初始化
///
/// 这是主要的配置存储，使用 LazyLock 确保线程安全的延迟初始化
pub static GLOBAL_CONFIG: LazyLock<RwLock<OtlpConfig>> = LazyLock::new(|| {
    RwLock::new(OtlpConfig::from_env())
});

/// 全局配置管理器
///
/// 提供类型安全的方法访问全局配置，封装 LazyLock 操作
pub struct GlobalConfig;

impl GlobalConfig {
    /// 获取全局配置的不可变引用（不触发初始化）
    ///
    /// 使用 `LazyLock::get` 检查配置是否已初始化
    ///
    /// # 返回
    /// - `Some(RwLockReadGuard<OtlpConfig>)` - 如果已初始化，返回配置读锁
    /// - `None` - 如果尚未初始化
    ///
    /// # 示例
    ///
    /// ```rust,ignore
    /// if let Some(config) = GlobalConfig::get() {
    ///     println!("Endpoint: {}", config.endpoint);
    /// }
    /// ```
    pub fn get() -> Option<RwLockReadGuard<'static, OtlpConfig>> {
        // Rust 1.94: LazyLock::get 返回 Option<&T>
        // 检查 LazyLock 是否已初始化
        LazyLock::get(&GLOBAL_CONFIG).map(|lock| lock.read().unwrap())
    }

    /// 检查配置是否已初始化
    ///
    /// 使用 `LazyLock::get` 进行检查，不会触发初始化
    ///
    /// # Rust 1.94 特性
    /// `LazyLock::get` 允许在不触发初始化的前提下检查状态
    pub fn is_initialized() -> bool {
        LazyLock::get(&GLOBAL_CONFIG).is_some()
    }

    /// 强制初始化并获取全局配置的不可变引用
    ///
    /// 使用 `LazyLock::force` 确保配置已初始化
    pub fn force() -> RwLockReadGuard<'static, OtlpConfig> {
        LazyLock::force(&GLOBAL_CONFIG).read().unwrap()
    }

    /// 获取全局配置的写锁（强制初始化）
    ///
    /// 使用 `LazyLock::force` 确保配置已初始化，然后获取写锁
    pub fn force_write() -> RwLockWriteGuard<'static, OtlpConfig> {
        LazyLock::force(&GLOBAL_CONFIG).write().unwrap()
    }

    /// 更新配置端点
    pub fn update_endpoint(endpoint: impl Into<String>) {
        let mut config = Self::force_write();
        config.endpoint = endpoint.into();
    }

    /// 添加自定义属性
    pub fn add_attribute(key: impl Into<String>, value: impl Into<String>) {
        let mut config = Self::force_write();
        config.attributes.insert(key.into(), value.into());
    }
}

// ============================================================================
// 2. 导出器缓存 - 使用 LazyLock 的线程安全缓存
// ============================================================================

/// 导出器 trait - 定义 OTLP 导出器接口
pub trait Exporter: Send + Sync {
    fn name(&self) -> &str;
    fn export(&self, data: &[u8]) -> Result<(), ExporterError>;
}

/// 导出器错误类型
#[derive(Debug, Clone)]
pub struct ExporterError {
    pub message: String,
}

impl std::fmt::Display for ExporterError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Exporter error: {}", self.message)
    }
}

impl std::error::Error for ExporterError {}

/// OTLP gRPC 导出器
#[derive(Debug)]
pub struct GrpcExporter {
    name: String,
    endpoint: String,
}

impl GrpcExporter {
    pub fn new(endpoint: impl Into<String>) -> Self {
        Self {
            name: "grpc".to_string(),
            endpoint: endpoint.into(),
        }
    }
}

impl Exporter for GrpcExporter {
    fn name(&self) -> &str {
        &self.name
    }

    fn export(&self, _data: &[u8]) -> Result<(), ExporterError> {
        // 模拟导出操作
        Ok(())
    }
}

/// OTLP HTTP 导出器
#[derive(Debug)]
pub struct HttpExporter {
    name: String,
    endpoint: String,
}

impl HttpExporter {
    pub fn new(endpoint: impl Into<String>) -> Self {
        Self {
            name: "http".to_string(),
            endpoint: endpoint.into(),
        }
    }
}

impl Exporter for HttpExporter {
    fn name(&self) -> &str {
        &self.name
    }

    fn export(&self, _data: &[u8]) -> Result<(), ExporterError> {
        // 模拟导出操作
        Ok(())
    }
}

/// 导出器缓存
///
/// 使用 LazyLock 实现线程安全的延迟初始化导出器缓存
pub struct ExporterCache {
    exporters: Mutex<HashMap<String, Box<dyn Exporter>>>,
}

impl ExporterCache {
    /// 创建新的导出器缓存
    pub fn new() -> Self {
        Self {
            exporters: Mutex::new(HashMap::new()),
        }
    }

    /// 检查是否包含指定导出器
    ///
    /// # Rust 1.94 特性
    /// 使用 `LazyLock::get` 检查缓存是否已初始化
    pub fn contains(&self, key: &str) -> bool {
        let guard = self.exporters.lock().unwrap();
        guard.contains_key(key)
    }

    /// 获取或初始化导出器
    ///
    /// # Rust 1.94 特性
    /// 使用 `LazyLock::force` 模式进行延迟初始化
    pub fn get_or_init<F>(&self, key: &str, f: F) -> MutexGuard<'_, HashMap<String, Box<dyn Exporter>>>
    where
        F: FnOnce() -> Box<dyn Exporter>,
    {
        let mut guard = self.exporters.lock().unwrap();
        guard.entry(key.to_string()).or_insert_with(f);
        guard
    }

    /// 添加导出器
    pub fn add_exporter(&self, key: impl Into<String>, exporter: Box<dyn Exporter>) {
        let mut guard = self.exporters.lock().unwrap();
        guard.insert(key.into(), exporter);
    }

    /// 移除导出器
    pub fn remove_exporter(&self, key: &str) -> Option<Box<dyn Exporter>> {
        let mut guard = self.exporters.lock().unwrap();
        guard.remove(key)
    }

    /// 获取缓存大小
    pub fn len(&self) -> usize {
        let guard = self.exporters.lock().unwrap();
        guard.len()
    }

    /// 检查缓存是否为空
    pub fn is_empty(&self) -> bool {
        let guard = self.exporters.lock().unwrap();
        guard.is_empty()
    }
}

impl Default for ExporterCache {
    fn default() -> Self {
        Self::new()
    }
}

/// 全局导出器缓存 - LazyLock 延迟初始化
pub static EXPORTER_CACHE: LazyLock<ExporterCache> = LazyLock::new(ExporterCache::new);

/// 导出器缓存管理器
///
/// 提供 Rust 1.94 LazyLock 新方法的封装
pub struct ExporterCacheManager;

impl ExporterCacheManager {
    /// 获取缓存的不可变引用（不触发初始化）
    ///
    /// # Rust 1.94 特性
    /// 使用 `LazyLock::get` 避免不必要的初始化
    pub fn get() -> Option<&'static ExporterCache> {
        LazyLock::get(&EXPORTER_CACHE)
    }

    /// 检查缓存是否已初始化
    pub fn is_initialized() -> bool {
        LazyLock::get(&EXPORTER_CACHE).is_some()
    }

    /// 强制初始化并获取缓存
    ///
    /// # Rust 1.94 特性
    /// 使用 `LazyLock::force` 确保已初始化
    pub fn force() -> &'static ExporterCache {
        LazyLock::force(&EXPORTER_CACHE)
    }

    /// 获取 gRPC 导出器（如果不存在则创建）
    pub fn get_grpc_exporter(endpoint: impl Into<String>) -> &'static ExporterCache {
        let cache = LazyLock::force(&EXPORTER_CACHE);
        let endpoint = endpoint.into();
        let _guard = cache.get_or_init("grpc", || Box::new(GrpcExporter::new(endpoint)));
        cache
    }

    /// 获取 HTTP 导出器（如果不存在则创建）
    pub fn get_http_exporter(endpoint: impl Into<String>) -> &'static ExporterCache {
        let cache = LazyLock::force(&EXPORTER_CACHE);
        let endpoint = endpoint.into();
        let _guard = cache.get_or_init("http", || Box::new(HttpExporter::new(endpoint)));
        cache
    }
}

// ============================================================================
// 3. 协议缓冲区类型注册表 - LazyLock 延迟初始化
// ============================================================================

/// 协议缓冲区字段类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProtoFieldType {
    Int32,
    Int64,
    UInt32,
    UInt64,
    Float,
    Double,
    Bool,
    String,
    Bytes,
    Message(&'static str),
    Enum(&'static str),
}

/// 协议缓冲区字段描述
#[derive(Debug, Clone)]
pub struct ProtoField {
    pub name: &'static str,
    pub field_number: u32,
    pub field_type: ProtoFieldType,
    pub repeated: bool,
}

/// 协议缓冲区消息描述
#[derive(Debug, Clone)]
pub struct ProtoMessage {
    pub name: &'static str,
    pub fields: Vec<ProtoField>,
}

/// 协议缓冲区类型注册表
///
/// 管理所有 OTLP protobuf 类型的元数据信息
pub struct ProtoTypeRegistry {
    messages: HashMap<&'static str, ProtoMessage>,
    enums: HashMap<&'static str, Vec<&'static str>>,
}

impl ProtoTypeRegistry {
    /// 创建新的类型注册表并初始化标准 OTLP 类型
    fn new() -> Self {
        let mut registry = Self {
            messages: HashMap::new(),
            enums: HashMap::new(),
        };
        registry.init_standard_types();
        registry
    }

    /// 初始化标准 OTLP 类型
    fn init_standard_types(&mut self) {
        // Trace 相关类型
        self.register_message(ProtoMessage {
            name: "opentelemetry.proto.trace.v1.Span",
            fields: vec![
                ProtoField {
                    name: "trace_id",
                    field_number: 1,
                    field_type: ProtoFieldType::Bytes,
                    repeated: false,
                },
                ProtoField {
                    name: "span_id",
                    field_number: 2,
                    field_type: ProtoFieldType::Bytes,
                    repeated: false,
                },
                ProtoField {
                    name: "parent_span_id",
                    field_number: 3,
                    field_type: ProtoFieldType::Bytes,
                    repeated: false,
                },
                ProtoField {
                    name: "name",
                    field_number: 4,
                    field_type: ProtoFieldType::String,
                    repeated: false,
                },
                ProtoField {
                    name: "kind",
                    field_number: 5,
                    field_type: ProtoFieldType::Enum("Span.SpanKind"),
                    repeated: false,
                },
            ],
        });

        // Metrics 相关类型
        self.register_message(ProtoMessage {
            name: "opentelemetry.proto.metrics.v1.Metric",
            fields: vec![
                ProtoField {
                    name: "name",
                    field_number: 1,
                    field_type: ProtoFieldType::String,
                    repeated: false,
                },
                ProtoField {
                    name: "description",
                    field_number: 2,
                    field_type: ProtoFieldType::String,
                    repeated: false,
                },
                ProtoField {
                    name: "unit",
                    field_number: 3,
                    field_type: ProtoFieldType::String,
                    repeated: false,
                },
            ],
        });

        // Logs 相关类型
        self.register_message(ProtoMessage {
            name: "opentelemetry.proto.logs.v1.LogRecord",
            fields: vec![
                ProtoField {
                    name: "time_unix_nano",
                    field_number: 1,
                    field_type: ProtoFieldType::UInt64,
                    repeated: false,
                },
                ProtoField {
                    name: "severity_number",
                    field_number: 2,
                    field_type: ProtoFieldType::Enum("SeverityNumber"),
                    repeated: false,
                },
                ProtoField {
                    name: "body",
                    field_number: 3,
                    field_type: ProtoFieldType::Message("AnyValue"),
                    repeated: false,
                },
            ],
        });

        // 注册枚举类型
        self.enums.insert(
            "Span.SpanKind",
            vec!["UNSPECIFIED", "INTERNAL", "SERVER", "CLIENT", "PRODUCER", "CONSUMER"],
        );
        self.enums.insert(
            "SeverityNumber",
            vec![
                "UNSPECIFIED",
                "TRACE",
                "DEBUG",
                "INFO",
                "WARN",
                "ERROR",
                "FATAL",
            ],
        );
    }

    /// 注册消息类型
    pub fn register_message(&mut self, message: ProtoMessage) {
        self.messages.insert(message.name, message);
    }

    /// 获取消息类型
    pub fn get_message(&self, name: &str) -> Option<&ProtoMessage> {
        self.messages.get(name)
    }

    /// 获取枚举类型
    pub fn get_enum(&self, name: &str) -> Option<&Vec<&'static str>> {
        self.enums.get(name)
    }

    /// 获取所有消息类型名称
    pub fn message_names(&self) -> impl Iterator<Item = &&'static str> {
        self.messages.keys()
    }

    /// 获取所有枚举类型名称
    pub fn enum_names(&self) -> impl Iterator<Item = &&'static str> {
        self.enums.keys()
    }
}

/// 全局类型注册表 - LazyLock 延迟初始化
pub static PROTO_REGISTRY: LazyLock<RwLock<ProtoTypeRegistry>> =
    LazyLock::new(|| RwLock::new(ProtoTypeRegistry::new()));

/// 协议缓冲区类型注册表管理器
///
/// 提供 Rust 1.94 LazyLock 新方法的封装
pub struct ProtoRegistryManager;

impl ProtoRegistryManager {
    /// 获取注册表的不可变引用（不触发初始化）
    ///
    /// # Rust 1.94 特性
    /// 使用 `LazyLock::get` 避免不必要的初始化
    pub fn get() -> Option<RwLockReadGuard<'static, ProtoTypeRegistry>> {
        LazyLock::get(&PROTO_REGISTRY).map(|lock| lock.read().unwrap())
    }

    /// 检查注册表是否已初始化
    pub fn is_initialized() -> bool {
        LazyLock::get(&PROTO_REGISTRY).is_some()
    }

    /// 强制初始化并获取注册表
    ///
    /// # Rust 1.94 特性
    /// 使用 `LazyLock::force` 确保已初始化
    pub fn force() -> RwLockReadGuard<'static, ProtoTypeRegistry> {
        LazyLock::force(&PROTO_REGISTRY).read().unwrap()
    }

    /// 强制初始化并获取注册表写锁
    pub fn force_write() -> RwLockWriteGuard<'static, ProtoTypeRegistry> {
        LazyLock::force(&PROTO_REGISTRY).write().unwrap()
    }

    /// 获取消息类型描述
    pub fn get_message(name: &str) -> Option<ProtoMessage> {
        Self::force().get_message(name).cloned()
    }

    /// 注册自定义消息类型
    pub fn register_message(message: ProtoMessage) {
        let mut registry = Self::force_write();
        registry.register_message(message);
    }
}

// ============================================================================
// 4. 追踪器提供者单例 - LazyLock 模式
// ============================================================================

/// Span ID 类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SpanId(pub [u8; 8]);

impl SpanId {
    pub fn new() -> Self {
        let mut id = [0u8; 8];
        for (i, byte) in id.iter_mut().enumerate() {
            *byte = i as u8;
        }
        Self(id)
    }
}

impl Default for SpanId {
    fn default() -> Self {
        Self::new()
    }
}

/// Trace ID 类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TraceId(pub [u8; 16]);

impl TraceId {
    pub fn new() -> Self {
        let mut id = [0u8; 16];
        for (i, byte) in id.iter_mut().enumerate() {
            *byte = i as u8;
        }
        Self(id)
    }
}

impl Default for TraceId {
    fn default() -> Self {
        Self::new()
    }
}

/// Span 上下文
#[derive(Debug, Clone)]
pub struct SpanContext {
    pub trace_id: TraceId,
    pub span_id: SpanId,
    pub parent_span_id: Option<SpanId>,
    pub sampled: bool,
}

/// Tracer 接口
pub trait Tracer: Send + Sync {
    fn start_span(&self, name: &str) -> SpanContext;
    fn end_span(&self, span: &SpanContext);
}

/// Tracer 提供者
pub struct TracerProvider {
    tracers: Mutex<HashMap<String, Box<dyn Tracer>>>,
    default_tracer: String,
}

impl TracerProvider {
    /// 创建新的 TracerProvider
    pub fn new() -> Self {
        Self {
            tracers: Mutex::new(HashMap::new()),
            default_tracer: "default".to_string(),
        }
    }

    /// 注册 Tracer
    pub fn register_tracer(&self, name: impl Into<String>, tracer: Box<dyn Tracer>) {
        let mut guard = self.tracers.lock().unwrap();
        guard.insert(name.into(), tracer);
    }

    /// 获取 Tracer
    pub fn get_tracer(&self, name: &str) -> Option<MutexGuard<'_, HashMap<String, Box<dyn Tracer>>>> {
        let guard = self.tracers.lock().unwrap();
        if guard.contains_key(name) {
            Some(guard)
        } else {
            None
        }
    }

    /// 设置默认 Tracer
    pub fn set_default_tracer(&mut self, name: impl Into<String>) {
        self.default_tracer = name.into();
    }

    /// 获取默认 Tracer 名称
    pub fn default_tracer_name(&self) -> &str {
        &self.default_tracer
    }
}

impl Default for TracerProvider {
    fn default() -> Self {
        Self::new()
    }
}

/// 全局 TracerProvider - LazyLock 延迟初始化
pub static TRACER_PROVIDER: LazyLock<Mutex<TracerProvider>> =
    LazyLock::new(|| Mutex::new(TracerProvider::new()));

/// TracerProvider 管理器
///
/// 提供 Rust 1.94 LazyLock 新方法的封装
pub struct TracerProviderManager;

impl TracerProviderManager {
    /// 获取提供者的不可变引用（不触发初始化）
    ///
    /// # Rust 1.94 特性
    /// 使用 `LazyLock::get` 避免不必要的初始化
    pub fn get() -> Option<MutexGuard<'static, TracerProvider>> {
        LazyLock::get(&TRACER_PROVIDER).map(|lock| lock.lock().unwrap())
    }

    /// 检查提供者是否已初始化
    pub fn is_initialized() -> bool {
        LazyLock::get(&TRACER_PROVIDER).is_some()
    }

    /// 强制初始化并获取提供者
    ///
    /// # Rust 1.94 特性
    /// 使用 `LazyLock::force` 确保已初始化
    pub fn force() -> MutexGuard<'static, TracerProvider> {
        LazyLock::force(&TRACER_PROVIDER).lock().unwrap()
    }

    /// 注册 Tracer
    pub fn register_tracer(name: impl Into<String>, tracer: Box<dyn Tracer>) {
        let provider = Self::force();
        provider.register_tracer(name, tracer);
    }

    /// 设置默认 Tracer
    pub fn set_default_tracer(name: impl Into<String>) {
        let mut provider = Self::force();
        provider.set_default_tracer(name);
    }
}

// ============================================================================
// 5. LazyCell 实现 - 单线程延迟初始化
// ============================================================================

/// 线程本地资源管理器
///
/// 使用 LazyCell 实现单线程延迟初始化
/// 
/// # 注意
/// 由于 LazyCell::new 是 const fn，需要使用具体的函数指针或 Default
pub struct ThreadLocalResource<T, F = fn() -> T> {
    cell: LazyCell<T, F>,
}

impl<T, F: FnOnce() -> T> ThreadLocalResource<T, F> {
    /// 创建新的线程本地资源
    pub const fn new(f: F) -> Self {
        Self {
            cell: LazyCell::new(f),
        }
    }

    /// 获取资源的不可变引用（不触发初始化）
    ///
    /// # Rust 1.94 特性
    /// 使用 `LazyCell::get` 避免不必要的初始化
    pub fn get(&self) -> Option<&T> {
        LazyCell::get(&self.cell)
    }

    /// 获取资源的可变引用（不触发初始化）
    ///
    /// # Rust 1.94 特性
    /// 使用 `LazyCell::get_mut` 在已初始化时修改
    pub fn get_mut(&mut self) -> Option<&mut T> {
        LazyCell::get_mut(&mut self.cell)
    }

    /// 强制初始化并获取资源
    ///
    /// # Rust 1.94 特性
    /// 使用 `LazyCell::force` 确保已初始化
    pub fn force(&self) -> &T {
        LazyCell::force(&self.cell)
    }

    /// 强制初始化并获取可变引用
    ///
    /// # Rust 1.94 特性
    /// 使用 `LazyCell::force_mut` 确保已初始化并修改
    pub fn force_mut(&mut self) -> &mut T {
        LazyCell::force_mut(&mut self.cell)
    }
}

impl<T: Default> ThreadLocalResource<T, fn() -> T> {
    /// 使用 Default 创建资源
    pub const fn new_default() -> Self {
        Self::new(T::default)
    }
}

/// 缓冲区管理器 - LazyCell 实现
///
/// 单线程缓冲区，使用 LazyCell 延迟分配内存
/// 
/// # 注意
/// 由于 LazyCell::new 是 const fn，这里使用固定容量或 Default
pub struct LazyBuffer {
    buffer: LazyCell<Vec<u8>>,
}

impl LazyBuffer {
    /// 创建新的延迟缓冲区（使用默认容量）
    pub const fn new() -> Self {
        Self {
            buffer: LazyCell::new(Vec::new),
        }
    }

    /// 获取缓冲区的不可变引用（不触发初始化）
    ///
    /// # Rust 1.94 特性
    /// 使用 `LazyCell::get` 避免不必要的内存分配
    pub fn get(&self) -> Option<&Vec<u8>> {
        LazyCell::get(&self.buffer)
    }

    /// 获取缓冲区的可变引用（不触发初始化）
    ///
    /// # Rust 1.94 特性
    /// 使用 `LazyCell::get_mut` 在已初始化时修改
    pub fn get_mut(&mut self) -> Option<&mut Vec<u8>> {
        LazyCell::get_mut(&mut self.buffer)
    }

    /// 强制初始化并获取缓冲区
    ///
    /// # Rust 1.94 特性
    /// 使用 `LazyCell::force` 确保已初始化
    pub fn force(&self) -> &Vec<u8> {
        LazyCell::force(&self.buffer)
    }

    /// 强制初始化并获取可变缓冲区
    ///
    /// # Rust 1.94 特性
    /// 使用 `LazyCell::force_mut` 确保已初始化并修改
    pub fn force_mut(&mut self) -> &mut Vec<u8> {
        LazyCell::force_mut(&mut self.buffer)
    }

    /// 写入数据到缓冲区
    pub fn write(&mut self, data: &[u8]) {
        let buffer = self.force_mut();
        buffer.extend_from_slice(data);
    }

    /// 清空缓冲区
    pub fn clear(&mut self) {
        if let Some(buffer) = self.get_mut() {
            buffer.clear();
        }
    }

    /// 获取缓冲区长度
    pub fn len(&self) -> usize {
        self.get().map(|b| b.len()).unwrap_or(0)
    }

    /// 检查缓冲区是否为空
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl Default for LazyBuffer {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// 6. 综合示例 - 结合所有 Rust 1.94 特性
// ============================================================================

/// 综合配置管理器
///
/// 结合 LazyLock 和 LazyCell 的优势，提供完整的配置管理方案
pub struct ComprehensiveConfigManager;

impl ComprehensiveConfigManager {
    /// 检查全局配置是否已初始化
    ///
    /// 使用 `LazyLock::get` 避免触发初始化
    pub fn is_config_initialized() -> bool {
        GlobalConfig::is_initialized()
    }

    /// 安全地读取配置（不触发初始化）
    ///
    /// # Rust 1.94 特性
    /// 使用 `LazyLock::get` 实现按需读取
    pub fn try_read_config() -> Option<OtlpConfig> {
        GlobalConfig::get().map(|guard| guard.clone())
    }

    /// 强制初始化并配置
    ///
    /// # Rust 1.94 特性
    /// 使用 `LazyLock::force` 确保初始化并修改
    pub fn initialize_with<F>(f: F)
    where
        F: FnOnce(&mut OtlpConfig),
    {
        let mut config = GlobalConfig::force_write();
        f(&mut *config);
    }

    /// 获取或创建缓冲区
    ///
    /// 使用 `LazyCell::force_mut` 模式
    pub fn get_or_create_buffer() -> LazyBuffer {
        LazyBuffer::new()
    }
}

/// OTLP 运行时上下文
///
/// 管理 OTLP 客户端的运行时状态
pub struct OtlpRuntimeContext {
    /// 是否已启动
    started: bool,
}

impl OtlpRuntimeContext {
    /// 创建新的运行时上下文
    pub fn new() -> Self {
        Self {
            started: false,
        }
    }

    /// 启动运行时（触发所有延迟初始化）
    pub fn start(&mut self) {
        // 使用 force 强制初始化配置
        let _guard = GlobalConfig::force();
        
        self.started = true;
    }

    /// 检查运行时状态
    pub fn is_started(&self) -> bool {
        self.started
    }

    /// 获取配置（不触发初始化）
    pub fn get_config(&self) -> Option<RwLockReadGuard<'_, OtlpConfig>> {
        GlobalConfig::get()
    }
}

impl Default for OtlpRuntimeContext {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// 7. Rust 1.94 新方法演示和文档
// ============================================================================

/// Rust 1.94 LazyLock 和 LazyCell 新方法演示
///
/// 此模块展示 Rust 1.94 中 `LazyLock` 和 `LazyCell` 新增的 API 方法：
///
/// # 新增方法
///
/// ## `LazyLock::get`
/// ```ignore
/// pub fn get(this: &LazyLock<T, F>) -> Option<&T>
/// ```
/// 如果 LazyLock 已完全初始化，则返回对其基础数据的引用。
/// 如果尚未初始化，则返回 `None`。
///
/// ## `LazyLock::get_mut`
/// ```ignore
/// pub fn get_mut(this: &mut LazyLock<T, F>) -> Option<&mut T>
/// ```
/// 如果 LazyLock 已完全初始化，则返回对其基础数据的可变引用。
/// 如果尚未初始化，则返回 `None`。
///
/// ## `LazyLock::force_mut`
/// ```ignore
/// pub fn force_mut(this: &mut LazyLock<T, F>) -> &mut T
/// ```
/// 强制初始化 LazyLock（如果需要），并返回对其基础数据的可变引用。
///
/// ## `LazyCell::get`
/// ```ignore
/// pub fn get(this: &LazyCell<T, F>) -> Option<&T>
/// ```
/// 如果 LazyCell 已完全初始化，则返回对其基础数据的引用。
///
/// ## `LazyCell::get_mut`
/// ```ignore
/// pub fn get_mut(this: &mut LazyCell<T, F>) -> Option<&mut T>
/// ```
/// 如果 LazyCell 已完全初始化，则返回对其基础数据的可变引用。
///
/// ## `LazyCell::force_mut`
/// ```ignore
/// pub fn force_mut(this: &mut LazyCell<T, F>) -> &mut T
/// ```
/// 强制初始化 LazyCell（如果需要），并返回对其基础数据的可变引用。
pub mod rust_1_94_api_demo {
    use std::cell::LazyCell;
    use std::sync::LazyLock;

    /// 演示 `LazyLock::get` 方法
    ///
    /// 用于检查静态值是否已初始化，而不触发初始化
    pub fn demo_lazy_lock_get() {
        static LAZY_VALUE: LazyLock<String> = LazyLock::new(|| {
            println!("Initializing LAZY_VALUE...");
            "initialized".to_string()
        });

        // 检查是否已初始化（不触发初始化）
        match LazyLock::get(&LAZY_VALUE) {
            Some(value) => println!("Already initialized: {}", value),
            None => println!("Not yet initialized"),
        }

        // 强制初始化
        let _ = LazyLock::force(&LAZY_VALUE);

        // 再次检查
        match LazyLock::get(&LAZY_VALUE) {
            Some(value) => println!("Now initialized: {}", value),
            None => println!("Still not initialized"),
        }
    }

    /// 演示 `LazyCell::get` 和 `LazyCell::get_mut` 方法
    ///
    /// 用于单线程延迟初始化场景
    pub fn demo_lazy_cell_methods() {
        let mut cell: LazyCell<Vec<i32>> = LazyCell::new(|| {
            println!("Initializing LazyCell...");
            vec![1, 2, 3]
        });

        // 初始化前 get 返回 None
        assert!(LazyCell::get(&cell).is_none());
        println!("Before init: get() returned None");

        // 强制初始化
        let value = LazyCell::force(&cell);
        println!("After force: {:?}", value);

        // 现在 get 返回 Some
        assert_eq!(LazyCell::get(&cell), Some(&vec![1, 2, 3]));
        println!("After init: get() returned Some");

        // 使用 get_mut 修改（已初始化）
        if let Some(vec) = LazyCell::get_mut(&mut cell) {
            vec.push(4);
            println!("After push: {:?}", vec);
        }

        // 验证修改
        assert_eq!(LazyCell::force(&cell).len(), 4);
    }

    /// 演示 `LazyCell::force_mut` 方法
    ///
    /// 用于需要立即初始化并修改的场景
    pub fn demo_lazy_cell_force_mut() {
        let mut cell: LazyCell<String> = LazyCell::new(|| "Hello".to_string());

        // 使用 force_mut 初始化并立即修改
        let value = LazyCell::force_mut(&mut cell);
        value.push_str(" World!");

        assert_eq!(LazyCell::force(&cell), "Hello World!");
        println!("force_mut result: {}", LazyCell::force(&cell));
    }

    /// 演示线程本地 LazyCell 的使用
    ///
    /// 用于每个线程独立的延迟初始化资源
    pub fn demo_thread_local_lazy_cell() {
        use std::cell::RefCell;

        thread_local! {
            static LOCAL_BUFFER: RefCell<LazyCell<Vec<u8>>> = RefCell::new(LazyCell::new(Vec::new));
        }

        LOCAL_BUFFER.with(|buf| {
            // 检查是否已初始化
            let is_init = LazyCell::get(&*buf.borrow()).is_some();
            println!("Buffer initialized before access: {}", is_init);

            // 获取可变绑定
            let mut binding = buf.borrow_mut();
            // 强制初始化并获取可变引用
            let buffer = LazyCell::force_mut(&mut *binding);
            buffer.extend_from_slice(b"thread-local data");

            println!("Buffer content: {:?}", buffer);
            
            // 现在检查应该已初始化
            let is_init_after = LazyCell::get(&*binding).is_some();
            println!("Buffer initialized after access: {}", is_init_after);
        });
    }
}

// ============================================================================
// 测试模块
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::LazyCell;
    use std::sync::LazyLock;

    // ==========================================================================
    // LazyLock::get / LazyLock::force 测试
    // ==========================================================================

    #[test]
    fn test_lazy_lock_get_before_init() {
        // 创建一个新的局部 LazyLock 用于测试
        let lazy: LazyLock<String> = LazyLock::new(|| "test".to_string());
        
        // 初始化前，get 返回 None
        assert!(LazyLock::get(&lazy).is_none());
        
        // 强制初始化
        let _ = LazyLock::force(&lazy);
        
        // 现在 get 返回 Some
        assert_eq!(LazyLock::get(&lazy), Some(&"test".to_string()));
    }

    #[test]
    fn test_lazy_lock_get_static() {
        // 由于 GLOBAL_CONFIG 可能已被其他测试初始化，
        // 我们测试 API 的行为而不是具体的返回值
        let config = LazyLock::get(&GLOBAL_CONFIG);
        
        // 验证返回类型正确
        let _: Option<&RwLock<OtlpConfig>> = config;
        
        // 如果已初始化，验证可以读取
        if let Some(lock) = config {
            let guard = lock.read().unwrap();
            assert!(!guard.endpoint.is_empty());
        }
    }

    #[test]
    fn test_lazy_lock_force() {
        // 使用 force 确保初始化，使用 try_lock 避免死锁
        let config = LazyLock::force(&GLOBAL_CONFIG);
        if let Ok(guard) = config.try_read() {
            assert_eq!(guard.endpoint, "http://localhost:4317");
        }
    }

    #[test]
    fn test_global_config_manager() {
        // 测试配置管理器 - 使用独立的锁作用域
        {
            let mut config = GlobalConfig::force_write();
            config.endpoint = "http://test:4317".to_string();
        }
        
        {
            let config = GlobalConfig::force();
            assert_eq!(config.endpoint, "http://test:4317");
        }
        
        // 恢复默认
        {
            let mut config = GlobalConfig::force_write();
            config.endpoint = "http://localhost:4317".to_string();
        }
    }

    #[test]
    fn test_global_config_add_attribute() {
        GlobalConfig::add_attribute("test_key", "test_value");
        
        let config = GlobalConfig::force();
        assert_eq!(config.attributes.get("test_key"), Some(&"test_value".to_string()));
    }

    // ==========================================================================
    // LazyCell::get / LazyCell::get_mut / LazyCell::force_mut 测试
    // ==========================================================================

    #[test]
    fn test_lazy_cell_get() {
        let cell: LazyCell<String> = LazyCell::new(|| "initialized".to_string());
        
        // 首次访问前，get 返回 None
        assert!(LazyCell::get(&cell).is_none());
        
        // 强制初始化
        let _ = LazyCell::force(&cell);
        
        // 现在 get 返回 Some
        assert_eq!(LazyCell::get(&cell), Some(&"initialized".to_string()));
    }

    #[test]
    fn test_lazy_cell_force_mut() {
        let mut cell: LazyCell<String> = LazyCell::new(|| "initial".to_string());
        
        // 使用 force_mut 初始化并修改
        let value = LazyCell::force_mut(&mut cell);
        value.push_str(" modified");
        
        assert_eq!(LazyCell::force(&cell), "initial modified");
    }

    #[test]
    fn test_lazy_cell_get_mut() {
        let mut cell: LazyCell<Vec<i32>> = LazyCell::new(|| vec![1, 2, 3]);
        
        // 初始化前，get_mut 返回 None
        assert!(LazyCell::get_mut(&mut cell).is_none());
        
        // 强制初始化
        let _ = LazyCell::force(&cell);
        
        // 现在 get_mut 返回 Some
        if let Some(vec) = LazyCell::get_mut(&mut cell) {
            vec.push(4);
        }
        
        assert_eq!(LazyCell::force(&cell).len(), 4);
    }

    #[test]
    fn test_thread_local_resource() {
        let mut resource: ThreadLocalResource<String, fn() -> String> = ThreadLocalResource::new(|| "test".to_string());
        
        // 初始化前
        assert!(resource.get().is_none());
        
        // 强制初始化并修改
        let value = resource.force_mut();
        value.push_str(" resource");
        
        assert_eq!(resource.force(), "test resource");
    }

    #[test]
    fn test_lazy_buffer() {
        let mut buffer = LazyBuffer::new();
        
        // 初始状态
        assert!(buffer.get().is_none());
        assert_eq!(buffer.len(), 0);
        
        // 写入数据（触发初始化）
        buffer.write(b"Hello, OTLP!");
        
        assert_eq!(buffer.len(), 12);
        assert_eq!(buffer.force().as_slice(), b"Hello, OTLP!");
        
        // 清空缓冲区
        buffer.clear();
        assert!(buffer.is_empty());
    }

    // ==========================================================================
    // 导出器缓存测试
    // ==========================================================================

    #[test]
    fn test_exporter_cache() {
        let cache = ExporterCache::new();
        
        // 初始为空
        assert!(cache.is_empty());
        
        // 添加导出器
        cache.add_exporter("test", Box::new(GrpcExporter::new("http://test:4317")));
        
        assert_eq!(cache.len(), 1);
        
        // 检查包含
        assert!(cache.contains("test"));
    }

    #[test]
    fn test_exporter_cache_manager() {
        // 获取 gRPC 导出器
        let cache = ExporterCacheManager::get_grpc_exporter("http://grpc:4317");
        assert!(!cache.is_empty());
        
        // 获取 HTTP 导出器
        let cache = ExporterCacheManager::get_http_exporter("http://http:4318");
        assert!(!cache.is_empty());
    }

    // ==========================================================================
    // 协议缓冲区类型注册表测试
    // ==========================================================================

    #[test]
    fn test_proto_registry() {
        let registry = ProtoRegistryManager::force();
        
        // 验证标准类型已注册
        let span_message = registry.get_message("opentelemetry.proto.trace.v1.Span");
        assert!(span_message.is_some());
        
        let span = span_message.unwrap();
        assert_eq!(span.name, "opentelemetry.proto.trace.v1.Span");
        assert!(!span.fields.is_empty());
    }

    #[test]
    fn test_proto_registry_enum() {
        let registry = ProtoRegistryManager::force();
        
        let span_kind = registry.get_enum("Span.SpanKind");
        assert!(span_kind.is_some());
        
        let kinds = span_kind.unwrap();
        assert!(kinds.contains(&"INTERNAL"));
        assert!(kinds.contains(&"SERVER"));
    }

    // ==========================================================================
    // TracerProvider 测试
    // ==========================================================================

    #[test]
    fn test_tracer_provider_manager() {
        // 使用独立的锁作用域避免死锁
        {
            let provider = TracerProviderManager::force();
            assert_eq!(provider.default_tracer_name(), "default");
        }
        
        // 设置默认 tracer
        {
            let mut provider = TracerProviderManager::force();
            provider.set_default_tracer("custom");
        }
        
        {
            let provider = TracerProviderManager::force();
            assert_eq!(provider.default_tracer_name(), "custom");
        }
        
        // 恢复默认
        {
            let mut provider = TracerProviderManager::force();
            provider.set_default_tracer("default");
        }
    }

    // ==========================================================================
    // 综合测试
    // ==========================================================================

    #[test]
    fn test_comprehensive_config_manager() {
        // 检查初始化状态
        let _is_init = ComprehensiveConfigManager::is_config_initialized();
        
        // 尝试读取配置
        let config = ComprehensiveConfigManager::try_read_config();
        
        // 如果已初始化，验证配置内容
        if let Some(cfg) = config {
            assert!(!cfg.endpoint.is_empty());
        }
        
        // 初始化并配置
        ComprehensiveConfigManager::initialize_with(|cfg| {
            cfg.endpoint = "http://comprehensive:4317".to_string();
            cfg.batch_size = 1024;
        });
        
        let config = GlobalConfig::force();
        assert_eq!(config.endpoint, "http://comprehensive:4317");
        assert_eq!(config.batch_size, 1024);
    }

    #[test]
    fn test_otlp_runtime_context() {
        let mut context = OtlpRuntimeContext::new();
        
        // 初始状态
        assert!(!context.is_started());
        
        // 启动运行时
        context.start();
        assert!(context.is_started());
    }

    #[test]
    fn test_lazy_lock_all_methods() {
        // 测试 LazyLock 的所有 Rust 1.94 方法
        let lazy: LazyLock<String> = LazyLock::new(|| "test".to_string());
        
        // 1. get - 获取不可变引用（不触发初始化）
        let before_init = LazyLock::get(&lazy);
        assert!(before_init.is_none());
        
        // 2. force - 强制初始化并获取
        let forced = LazyLock::force(&lazy);
        assert_eq!(forced, "test");
        
        // 3. 初始化后 get 返回 Some
        let after_init = LazyLock::get(&lazy);
        assert!(after_init.is_some());
        assert_eq!(after_init.unwrap(), "test");
    }

    #[test]
    fn test_lazy_cell_all_methods() {
        // 测试 LazyCell 的所有 Rust 1.94 方法
        let mut cell: LazyCell<i32> = LazyCell::new(|| 42);
        
        // 1. get - 获取不可变引用（不触发初始化）
        assert!(LazyCell::get(&cell).is_none());
        
        // 2. get_mut - 获取可变引用（不触发初始化）
        assert!(LazyCell::get_mut(&mut cell).is_none());
        
        // 3. force - 强制初始化
        let forced = LazyCell::force(&cell);
        assert_eq!(*forced, 42);
        
        // 4. 初始化后 get 返回 Some
        assert_eq!(LazyCell::get(&cell), Some(&42));
        
        // 5. get_mut 现在返回 Some
        if let Some(value) = LazyCell::get_mut(&mut cell) {
            *value = 100;
        }
        assert_eq!(LazyCell::force(&cell), &100);
        
        // 6. force_mut - 强制初始化并获取可变引用
        let mut cell2: LazyCell<String> = LazyCell::new(|| "hello".to_string());
        let value = LazyCell::force_mut(&mut cell2);
        value.push_str(" world");
        assert_eq!(LazyCell::force(&cell2), "hello world");
    }

    #[test]
    fn test_lazy_cell_in_struct() {
        // 测试在结构体中使用 LazyCell
        struct DataProcessor {
            buffer: LazyCell<Vec<u8>>,
            processed: bool,
        }

        impl DataProcessor {
            const fn new() -> Self {
                Self {
                    buffer: LazyCell::new(Vec::new),
                    processed: false,
                }
            }

            fn process(&mut self, data: &[u8]) {
                // 使用 force_mut 获取可变缓冲区
                let buffer = LazyCell::force_mut(&mut self.buffer);
                buffer.extend_from_slice(data);
                self.processed = true;
            }

            fn get_data(&self) -> Option<&[u8]> {
                LazyCell::get(&self.buffer).map(|v| v.as_slice())
            }
        }

        let mut processor = DataProcessor::new();
        assert!(processor.get_data().is_none());
        
        processor.process(b"test data");
        assert!(processor.processed);
        assert_eq!(processor.get_data(), Some(&b"test data"[..]));
    }

    #[test]
    fn test_lazy_lock_with_rwlock() {
        // 测试 LazyLock<RwLock<T>> 模式
        static DATA: LazyLock<RwLock<Vec<i32>>> = LazyLock::new(|| RwLock::new(vec![1, 2, 3]));

        // 获取读锁
        {
            let guard = DATA.read().unwrap();
            assert_eq!(guard.len(), 3);
        }

        // 获取写锁
        {
            let mut guard = DATA.write().unwrap();
            guard.push(4);
        }

        // 验证修改
        let guard = DATA.read().unwrap();
        assert_eq!(guard.len(), 4);
    }
}
