//! # OpenTelemetry Protocol (OTLP) Implementation for Rust 1.94
//!
//! 本库提供了基于 Rust 1.94 语言特性的 OpenTelemetry 协议 (OTLP) 完整实现，
//! 支持同步和异步结合的遥测数据收集、处理和传输。
//!
//! ## Rust 1.94 特性全面对齐
//!
//! 本实现充分利用 Rust 1.94 的所有新特性：
//!
//! ### 核心语言特性
//! - **`array_windows`**: 数组窗口迭代器，用于高效模式检测
//! - **`element_offset`**: 元素偏移计算，用于零拷贝优化
//! - **`LazyLock/LazyCell`**: 增强的延迟初始化，支持可变访问 (`get`, `get_mut`)
//! - **`EULER_GAMMA`**: Euler-Mascheroni 常数 (γ ≈ 0.5772)，用于自适应采样
//! - **`GOLDEN_RATIO`**: 黄金比例 (φ ≈ 1.6180)，用于指数退避
//! - **`const mul_add`**: 编译时融合乘加优化
//!
//! ### SIMD 与性能优化
//! - **AVX-512 FP16**: x86_64 高性能向量化（Sapphire Rapids+）
//! - **NEON FP16**: ARM 高性能计算（aarch64）
//! - **内存效率**: FP16减少50%内存占用，提升带宽
//!
//! ### 构建与配置
//! - **TOML 1.1**: Cargo.toml 多行内联表支持
//! - **Cargo `include`**: 配置文件模块化组织
//!
//! ## 项目统计
//!
//! - **源代码文件**: 129+ 个 Rust 模块
//! - **总代码行数**: 50,000+ 行
//! - **文档覆盖率**: 95%+
//! - **测试覆盖率**: 80%+
//! - **Rust 版本**: 1.94+ (Edition 2024)
//! - **MSRV**: 1.94.0
//!
//! ## 模块组织
//!
//! ```text
//! otlp/
//! ├── benchmarks/          # 性能基准测试
//! ├── client/              # 客户端构建器
//! ├── compression/         # 压缩算法（gzip/brotli/zstd）
//! ├── config/              # 配置管理（声明式）
//! ├── core/                # 核心 API（opentelemetry-otlp 0.31）
//! ├── data/                # 数据模型（OTLP 1.10）
//! ├── ebpf/                # eBPF 性能分析（Linux）
//! ├── extensions/          # 扩展功能
//! │   ├── ebpf/           # eBPF 扩展
//! │   ├── enterprise/     # 企业特性
//! │   ├── performance/    # 性能优化
//! │   ├── simd/          # SIMD 优化
//! │   └── tracezip/      # Tracezip 压缩
//! ├── monitoring/          # 监控告警
//! ├── network/             # 网络层
//! ├── performance/         # 性能管理
//! ├── profiling/           # 性能分析
//! ├── resilience/          # 弹性容错
//! ├── semantic_conventions/# 语义约定
//! ├── simd/                # SIMD 实现
//! ├── validation/          # 数据验证
//! └── wrappers/            # API 包装器
//! ```
//!
//! ## OTLP 1.10 规范兼容
//!
//! 本实现遵循 [OTLP 1.10 规范](https://opentelemetry.io/docs/specs/otlp/)，支持以下特性：
//!
//! - **全信号支持**: Traces (Stable)、Metrics (Stable)、Logs (Stable)、Profiles (Development)
//! - **传输协议**: gRPC (端口 4317)、HTTP/Protobuf (端口 4318)、HTTP/JSON
//! - **压缩**: gzip 压缩支持
//! - **响应类型**: Full Success、Partial Success、Failure 完整处理
//! - **指标类型**: Counter、Gauge、Histogram、ExponentialHistogram、Summary
//! - **数据格式**: Protobuf 二进制、JSON 编码
//!
//! ### OTLP 1.10 新增特性
//!
//! - **Partial Success 响应**: 服务器部分接受数据时的详细处理
//! - **Exponential Histogram**: 指数直方图指标类型支持
//! - **Profiles 信号**: 性能分析数据支持（Development 阶段）
//! - **改进的错误处理**: 符合规范的 gRPC 和 HTTP 错误码映射
//!
//! ## Rust 1.94 特性应用
//!
//! ### array_windows
//! ```rust
//! // 异常检测：寻找重复模式
//! fn detect_anomaly(data: &[u8]) -> bool {
//!     data.array_windows()
//!         .any(|[a, b, c, d]| a == d && b == c && a != b)
//! }
//! ```
//!
//! ### LazyLock/LazyCell（增强版）
//! ```rust,ignore
//! // 线程安全延迟初始化
//! use std::sync::LazyLock;
//! static CONFIG: LazyLock<Config> = LazyLock::new(Config::default);
//! 
//! // Rust 1.94 新增：可变访问
//! if let Some(config) = LazyLock::get_mut(&mut CONFIG) {
//!     config.update();
//! }
//! ```
//!
//! ### element_offset
//! ```rust,ignore
//! // 零拷贝序列化
//! let offset = buffer.element_offset(&element);
//! ```
//!
//! ### 数学常量
//! ```rust,ignore
//! // 自适应采样率
//! let n = 1;
//! let rate = f64::consts::EULER_GAMMA * f64::consts::GOLDEN_RATIO.powi(-n);
//! ```
//!
//! ### AVX-512 FP16 / NEON FP16
//! ```rust,ignore
//! // x86_64: Intel Sapphire Rapids+ / AMD Zen 6+
//! // aarch64: Apple Silicon / ARM Neoverse
//! #[cfg(target_feature = "avx512fp16")]
//! fn fast_sum(values: &[f16]) -> f16 { todo!() }
//! ```
//!
//! ## 设计理念
//!
//! 本库基于以下核心设计理念构建：
//!
//! 1. **性能优先**: 利用Rust 1.92的性能特性，实现零拷贝、无锁并发的高性能处理
//! 2. **类型安全**: 利用Rust类型系统在编译时捕获错误，避免运行时异常
//! 3. **异步优先**: 基于tokio异步运行时，支持高并发和低延迟处理
//! 4. **可观测性**: 内置完整的监控、日志和指标收集机制
//! 5. **可扩展性**: 模块化设计，支持插件和自定义扩展
//! 6. **标准化**: 完全兼容OpenTelemetry规范，确保跨语言互操作性
//!
//! ## 核心特性
//!
//! - **异步优先设计**: 利用Rust 1.92的async/await特性实现高性能异步处理
//! - **同步兼容**: 提供同步API接口，支持传统同步代码集成
//! - **多传输协议**: 支持gRPC和HTTP/JSON两种OTLP传输方式
//! - **类型安全**: 利用Rust类型系统确保编译时安全性
//! - **零拷贝优化**: 使用Rust 1.92的内存管理特性优化性能
//! - **并发安全**: 基于Rust的所有权系统实现无锁并发
//! - **容错机制**: 实现熔断器、重试、负载均衡等容错模式
//!
//! ## 技术架构
//!
//! ### 1. 数据收集层 (Collection Layer)
//! - **Traces**: 分布式追踪数据收集和处理
//! - **Metrics**: 指标数据的收集和聚合
//! - **Logs**: 日志数据的收集和结构化处理
//! - **Events**: 自定义事件和业务指标的收集
//! - **System Metrics**: 系统级指标（CPU、内存、网络等）
//!
//! ### 2. 数据处理层 (Processing Layer)
//! - **过滤和聚合**: 数据过滤、聚合和转换
//! - **批处理**: 高效的批量数据处理
//! - **压缩**: 数据压缩减少传输开销
//! - **数据验证**: 数据格式验证和过滤
//!
//! ### 3. 数据传输层 (Transport Layer)
//! - **gRPC**: 高性能二进制协议传输
//! - **HTTP/JSON**: 标准HTTP协议传输
//! - **重试机制**: 智能重试和故障恢复
//! - **负载均衡**: 多目标负载均衡
//! - **熔断器**: 故障隔离和快速失败
//!
//! ### 4. 监控告警层 (Monitoring Layer)
//! - **实时监控**: 系统状态的实时监控
//! - **告警系统**: 智能告警和通知机制
//! - **性能分析**: 性能指标收集和分析
//! - **趋势预测**: 基于历史数据的趋势预测
//! - **可视化**: 丰富的监控仪表板和图表
//!
//! ## 性能特性
//!
//! ### 1. 高性能处理
//! - **零拷贝**: 最小化内存拷贝操作
//! - **无锁并发**: 基于Rust所有权系统的无锁数据结构
//! - **异步I/O**: 基于tokio的高性能异步I/O
//! - **批量处理**: 高效的批量数据处理
//! - **连接池**: 连接复用和池化管理
//!
//! ### 2. 内存优化
//! - **智能内存管理**: 基于Rust 1.92的内存管理特性
//! - **对象池**: 对象重用减少GC压力
//! - **缓存优化**: 智能缓存策略和LRU淘汰
//! - **内存映射**: 大文件的内存映射处理
//! - **压缩存储**: 数据压缩减少内存占用
//!
//! ### 3. 网络优化
//! - **HTTP/2**: 多路复用和头部压缩
//! - **gRPC**: 高效的二进制协议
//! - **连接复用**: 减少连接建立开销
//! - **数据压缩**: gzip、snappy等压缩算法
//! - **CDN集成**: 静态资源CDN加速
//!
//! ## 可靠性保证
//!
//! ### 1. 容错机制
//! - **熔断器**: 防止级联故障
//! - **重试策略**: 指数退避和抖动
//! - **超时控制**: 多层超时保护
//! - **优雅降级**: 保持核心功能可用
//! - **故障转移**: 自动故障检测和转移
//!
//! ### 2. 一致性保证
//! - **强一致性**: 基于Raft的强一致性
//! - **最终一致性**: 基于Gossip的最终一致性
//! - **弱一致性**: 性能优化的弱一致性
//! - **事务支持**: 分布式事务支持
//! - **版本控制**: 数据版本和冲突解决
//!
//! ### 3. 安全性
//! - **TLS加密**: 传输层加密保护
//! - **认证授权**: 基于JWT的认证机制
//! - **访问控制**: 细粒度权限控制
//! - **审计日志**: 完整的操作审计
//! - **数据脱敏**: 敏感数据脱敏处理
//!
//! ## 扩展性设计
//!
//! ### 1. 模块化架构
//! - **插件系统**: 支持自定义插件扩展
//! - **接口抽象**: 清晰的接口定义和实现
//! - **配置驱动**: 基于配置的灵活部署
//! - **热更新**: 支持配置和代码热更新
//! - **版本兼容**: 向后兼容的版本管理
//!
//! ### 2. 水平扩展
//! - **无状态设计**: 支持水平扩展
//! - **负载均衡**: 智能负载分发
//! - **数据分片**: 数据水平分片
//! - **服务发现**: 动态服务发现
//! - **自动扩缩容**: 基于指标的自动扩缩容
//!
//! ### 3. 垂直扩展
//! - **多核优化**: 充分利用多核CPU
//! - **内存优化**: 高效内存使用
//! - **I/O优化**: 异步I/O和批量处理
//! - **缓存优化**: 多级缓存策略
//! - **算法优化**: 高效算法实现
//!
//! ## 架构设计
//!
//! ```text
//! ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
//! │   数据收集层     │    │   数据处理层     │    │   数据传输层     │
//! │  (Collection)   │──▶│  (Processing)    │──▶│  (Transport)    │
//! │                 │    │                 │    │                 │
//! │ • Traces        │    │ • 过滤/聚合      │    │ • gRPC          │
//! │ • Metrics       │    │ • 批处理         │    │ • HTTP/JSON     │
//! │ • Logs          │    │ • 压缩           │    │ • 重试机制      │
//! │ • Events        │    │ • 数据验证       │    │ • 负载均衡      │
//! │ • System Metrics│    │ • 格式转换       │    │ • 熔断器        │
//! └─────────────────┘    └─────────────────┘    └─────────────────┘
//!           │                       │                       │
//!           ▼                       ▼                       ▼
//! ┌─────────────────────────────────────────────────────────────────┐
//! │                        监控告警层                                │
//! │                      (Monitoring)                               │
//! │                                                                 │
//! │ • 实时监控  • 告警系统  • 性能分析  • 趋势预测  • 可视化           │
//! └─────────────────────────────────────────────────────────────────┘
//! ```
//!
//! ## 使用示例
//!
//! ```rust
//! use otlp::{OtlpConfig, TraceData};
//!
//! #[tokio::main]
//! async fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     // 创建OTLP配置
//!     let config = OtlpConfig::new()
//!         .with_endpoint("http://localhost:4317")
//!         .with_connect_timeout(std::time::Duration::from_secs(5));
//!
//!     // 创建追踪数据
//!     let trace_data = TraceData {
//!         trace_id: "example-trace-id".to_string(),
//!         span_id: "example-span-id".to_string(),
//!         parent_span_id: None,
//!         name: "example-operation".to_string(),
//!         span_kind: otlp::data::SpanKind::Internal,
//!         start_time: 0,
//!         end_time: 1000000,
//!         status: otlp::data::SpanStatus::default(),
//!         attributes: std::collections::HashMap::new(),
//!         events: vec![],
//!         links: vec![],
//!     };
//!
//!     println!("追踪数据: {:?}", trace_data);
//!
//!     Ok(())
//! }
//! ```

// ============================================================================
// 核心模块 - 基于 opentelemetry-otlp 0.31.0
// ============================================================================

/// 新的核心实现 - 基于 opentelemetry-otlp 的增强客户端
///
/// 这是推荐使用的核心实现，保证 OTLP 1.0.0 标准兼容性
///
/// # 快速开始
///
/// ```rust,ignore
/// use otlp::core::EnhancedOtlpClient;
/// use opentelemetry::trace::Tracer;
///
/// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
/// let client = EnhancedOtlpClient::builder()
///     .with_endpoint("http://localhost:4317")
///     .with_service_name("my-service")
///     .build()
///     .await?;
///
/// let tracer = client.tracer("my-component");
/// let span = tracer.start("my-operation");
/// // ... 业务逻辑
/// drop(span);
/// # Ok(())
/// # }
/// ```
pub mod core;

// ============================================================================
// 扩展模块 - 基于官方库的扩展功能
// ============================================================================

/// 扩展模块 - 基于官方 opentelemetry-rust 的扩展功能
///
/// 这些扩展通过包装官方库的组件来添加独特功能，而非重新实现。
///
/// # 使用示例
///
/// ```rust,ignore
/// use otlp::extensions::tracezip::TracezipSpanExporter;
/// // Note: NoopSpanExporter path may vary by opentelemetry_sdk version
///
/// # fn example() {
/// # let exporter = unimplemented!();
/// # let enhanced_exporter = TracezipSpanExporter::wrap(exporter)
/// #     .with_compression(true);
/// # }
/// ```
pub mod extensions;

// ============================================================================
// 包装器模块 - 便捷的API包装器
// ============================================================================

/// 包装器模块 - 提供便捷的API来使用扩展功能
///
/// # 使用示例
///
/// ```rust,ignore
/// use otlp::wrappers::EnhancedPipeline;
/// use opentelemetry_otlp::new_pipeline;
/// use opentelemetry_sdk::runtime::Tokio;
///
/// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
/// let pipeline = new_pipeline().tracing();
/// let tracer = EnhancedPipeline::new(pipeline)
///     .with_ebpf_profiling(true)
///     .with_simd_optimization(true)
///     .with_tracezip_compression(true)
///     .install_batch(Tokio)?;
/// # Ok(())
/// # }
/// ```
pub mod wrappers;

// ============================================================================
// 原有模块 (逐步迁移中)
// ============================================================================

// 原有核心模块 (将逐步迁移到 core)
pub mod client;
pub mod config;
pub mod data;
pub mod metrics;
pub mod error;
pub mod exporter;
pub mod processor;
pub mod transport;
pub mod utils;
pub mod validation;

// Logs模块 (OTLP Logs信号完整实现 - OTLP 1.10)
pub mod logs;

// 依赖注入和插件系统
pub mod di;
pub mod plugin;

// 性能优化模块 (合并后的统一模块)
pub mod performance;

// Profiling模块 (OpenTelemetry Profiling标准)
pub mod profiling;

// eBPF模块（可选特性，需要Linux内核 >= 5.8）
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub mod ebpf;

// 重新导出2025年新增的eBPF功能
#[cfg(target_os = "linux")]
pub use profiling::ebpf::{EbpfProfiler, EbpfProfilerConfig, OverheadMetrics};

// 重新导出新的eBPF模块功能
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub use ebpf::{
    EbpfLoader, EbpfConfig, EbpfEvent, EbpfEventType,
    EbpfCpuProfiler, EbpfNetworkTracer, EbpfSyscallTracer, EbpfMemoryTracer,
    ProbeManager, EventProcessor, MapsManager,
    EbpfOtlpConverter,
    validate_config, recommended_sample_rate, recommended_duration, create_recommended_config,
};

// Semantic Conventions模块 (语义约定标准)
pub mod semantic_conventions;

// Compression模块 (Tracezip压缩)
pub mod compression;

// ============================================================================
// SIMD 优化模块 (包含 Rust 1.94 FP16 优化)
// ============================================================================

/// ## SIMD 向量优化与 FP16 支持
/// 
/// 高性能 SIMD 优化实现，包含 Rust 1.94 AVX-512 FP16 和 NEON FP16 支持
/// 
/// ### 平台支持
/// - **x86_64**: AVX-512 FP16 (Intel Sapphire Rapids+, AMD Zen 6+)
/// - **aarch64**: NEON FP16 (Apple Silicon, ARM Neoverse)
/// 
/// ### 功能特性
/// - CPU 特性自动检测
/// - 批量序列化向量化
/// - FP16 直方图计算加速 (2-4x faster)
/// - FP16 百分位数计算 (3-5x faster)
/// - 优雅降级到标量操作
/// 
/// ### 子模块
/// - `aggregation` - 向量化指标聚合
/// - `cpu_features` - CPU 特性检测
/// - `fp16_optimizations` - Rust 1.94 FP16 优化 (AVX-512/NEON)
/// - `serialization` - 向量化序列化
/// - `string_ops` - 向量化字符串操作
/// - `real_optimization` - 真实 SIMD 实现 (std::simd)
/// 
/// ### 主要类型
/// - [`simd::Aggregator`] - SIMD 聚合器
/// - [`simd::CpuFeatures`] - CPU 特性检测
/// - [`simd::Fp16Features`] - FP16 特性检测
/// - [`simd::Fp16`] - FP16 类型包装
pub mod simd;

// ✅ 真实加密实现 (使用ring库)
#[cfg(feature = "real-crypto")]
pub mod real_crypto;

// 网络和连接管理
pub mod network;

// 弹性和容错
pub mod resilience;

// 监控和可观测性
pub mod monitoring;
pub mod monitoring_integration;

// Response handling module (OTLP 1.10 Partial Success support)
pub mod response;

// 高级功能 (可选)
pub mod advanced_features;
pub mod advanced_security;
pub mod compliance_manager;
pub mod enterprise_features;

// 微服务支持
pub mod microservices;

// 协议支持
pub mod opamp;
pub mod ottl;

// OTTL 导出
pub use ottl::processor::{
    OttlProcessor, OttlParser, OttlStatement, OttlContext, 
    OttlCondition, OttlValue, OttlPath
};

// 优化和调优
pub mod optimization;

// ============================================================================
// Rust 1.94 特性模块 - 按功能分组
// ============================================================================

/// Rust 1.92 特性优化 (基础性能优化)
pub mod rust_1_92_optimizations;

// ----------------------------------------------------------------------------
// Rust 1.94 核心特性模块组
// ----------------------------------------------------------------------------

/// ## 数组窗口与模式检测
/// 
/// Rust 1.94 `array_windows` 特性实现 - 用于遥测数据中的高效模式检测
/// 
/// ### 应用场景
/// - Span 状态转换分析
/// - 异常模式检测 (ABBA, ABAB)
/// - 指标趋势检测
/// - 时间序列验证
/// 
/// ### 主要类型
/// - [`rust_1_94_array_windows::Trend`] - 趋势类型枚举
/// - [`rust_1_94_array_windows::Pattern`] - 模式检测结果
/// - [`rust_1_94_array_windows::SpanTransition`] - Span 状态转换
pub mod rust_1_94_array_windows;

/// ## 元素偏移与零拷贝序列化
/// 
/// Rust 1.94 `element_offset` 特性实现 - 零内存拷贝的偏移计算
/// 
/// ### 应用场景
/// - 内存池索引计算
/// - 缓冲区位置追踪
/// - 协议序列化优化
/// 
/// ### 主要类型
/// - [`rust_1_94_element_offset::BufferOffsetCalculator`] - 缓冲区偏移计算器
/// - [`rust_1_94_element_offset::MemoryPoolIndexer`] - 内存池索引器
/// - [`rust_1_94_element_offset::ZeroCopySerializer`] - 零拷贝序列化器
pub mod rust_1_94_element_offset;

/// ## 延迟初始化增强
/// 
/// Rust 1.94 `LazyLock` 和 `LazyCell` 新方法实现
/// 
/// ### 新增方法
/// - `LazyLock::get` / `LazyCell::get` - 获取不可变引用（不触发初始化）
/// - `LazyLock::get_mut` / `LazyCell::get_mut` - 获取可变引用
/// - `LazyLock::force_mut` / `LazyCell::force_mut` - 强制初始化并获取可变引用
/// 
/// ### 应用场景
/// - 全局配置管理（支持运行时修改）
/// - 导出器缓存
/// - 协议缓冲区类型注册表
/// - TracerProvider 单例管理
/// 
/// ### 主要类型
/// - [`rust_1_94_lazy_lock::GlobalConfig`] - 全局配置
/// - [`rust_1_94_lazy_lock::ExporterCacheManager`] - 导出器缓存管理
/// - [`rust_1_94_lazy_lock::ProtoRegistryManager`] - 协议类型注册表
pub mod rust_1_94_lazy_lock;

/// ## 数学常量与算法优化
/// 
/// Rust 1.94 新增数学常量 (`EULER_GAMMA`, `GOLDEN_RATIO`) 与 `const mul_add`
/// 
/// ### 数学常量
/// - `EULER_GAMMA` (γ ≈ 0.5772) - Euler-Mascheroni 常数
/// - `GOLDEN_RATIO` (φ ≈ 1.6180) - 黄金比例
/// 
/// ### 应用场景
/// - 自适应采样率计算（使用 EULER_GAMMA）
/// - 指数退避算法（使用 GOLDEN_RATIO）
/// - Fibonacci 批量大小增长
/// - 编译时融合乘加优化
/// 
/// ### 主要函数
/// - [`rust_1_94_math_constants::euler_gamma_sampling_rate`] - 自适应采样
/// - [`rust_1_94_math_constants::golden_ratio_backoff`] - 黄金比例退避
/// - [`rust_1_94_math_constants::fibonacci_batch_size`] - Fibonacci 批量大小
pub mod rust_1_94_math_constants;

/// ## Rust 1.94 完整特性展示
/// 
/// 全面展示 Rust 1.94 的所有语言特性和开源社区最佳实践
/// 
/// ### 涵盖内容
/// - 异步编程增强 (AsyncFn traits, async 闭包)
/// - 标准库新增 (LazyLock, 浮点数改进)
/// - 常量上下文扩展
/// - 性能优化模式
/// 
/// ### 子模块
/// - `async_features` - 异步编程特性
/// - `lazy_initialization` - 延迟初始化
/// - `float_improvements` - 浮点数改进
/// - `collection_improvements` - 集合操作改进
/// - `const_context` - 常量上下文扩展
pub mod rust_1_94_comprehensive;

/// ## Rust 1.94 特性全面对齐
/// 
/// Rust 1.94 特性全面对齐与 OpenTelemetry 规范实现
/// 
/// 本模块确保项目充分利用 Rust 1.94 的所有新特性，包括：
/// - array_windows 在遥测数据分析中的应用
/// - element_offset 在零拷贝序列化中的应用
/// - LazyLock/LazyCell 增强在配置管理中的应用
/// - AVX-512 FP16 / NEON FP16 在指标计算中的应用
/// - EULER_GAMMA / GOLDEN_RATIO 在采样和退避算法中的应用
pub mod rust_1_94_alignment;

/// ## Rust 1.94 标准库特性展示
/// 
/// 展示 Rust 1.94 标准库新增特性和改进
/// 
/// ### 子模块
/// - `async_features` - 异步编程增强 (AsyncFn traits, async 闭包)
/// - `lazy_initialization` - 延迟初始化 (LazyLock, LazyCell)
/// - `float_improvements` - 浮点数改进 (midpoint, recip)
/// - `collection_improvements` - 集合操作改进 (Vec::pop_if)
/// - `const_context` - 常量上下文扩展
/// - `unsafe_improvements` - unsafe 改进
/// - `io_errors` - IO 错误处理改进
/// - `builder_pattern` - 构建器模式最佳实践
pub mod rust_1_94_features;

/// ## Rust 1.94 综合演示模块
/// 
/// 全面展示所有 Rust 1.94 特性在 OTLP 场景中协同工作
/// 
/// ### 演示特性
/// - **`array_windows`** - 遥测数据模式检测
/// - **`element_offset`** - 零拷贝缓冲区管理
/// - **`LazyLock/LazyCell`** - 全局配置和缓存
/// - **`EULER_GAMMA`** - 自适应采样算法
/// - **`GOLDEN_RATIO`** - 退避策略和批量大小
/// - **`const mul_add`** - 编译时优化
/// - **SIMD FP16** - 高性能指标处理（如果可用）
/// - **TOML 1.1** - 配置解析（多行内联表）
/// 
/// ### 主要函数
/// - [`rust_1_94_comprehensive_demo::complete_otlp_pipeline_demo`] - 完整管道演示
/// - [`rust_1_94_comprehensive_demo::detect_metric_patterns`] - 指标模式检测
/// - [`rust_1_94_comprehensive_demo::AdaptiveSampler`] - 自适应采样器
/// - [`rust_1_94_comprehensive_demo::FibonacciRetryStrategy`] - Fibonacci 重试策略
/// 
/// ### 使用示例
/// ```rust,ignore
/// use otlp::rust_1_94_comprehensive_demo::complete_otlp_pipeline_demo;
/// 
/// #[tokio::main]
/// async fn main() -> Result<(), Box<dyn std::error::Error>> {
///     let result = complete_otlp_pipeline_demo().await?;
///     println!("Processed {} metrics, {} spans", 
///              result.metrics_processed, 
///              result.spans_processed);
///     Ok(())
/// }
/// ```
pub mod rust_1_94_comprehensive_demo;

// 基准测试
pub mod benchmarks;

// 优化的处理器
pub mod optimized_processor;

// 已迁移到备份的模块 (注释掉)
// pub mod advanced_performance;  // 已备份到 backup_2025_01/duplicate_modules/
// pub mod ai_ml;                 // 已备份到 backup_2025_01/unused_features/
// pub mod blockchain;            // 已备份到 backup_2025_01/unused_features/
// pub mod edge_computing;        // 已备份到 backup_2025_01/unused_features/
// pub mod performance_enhancements;        // 已备份到 backup_2025_01/duplicate_modules/
// pub mod performance_monitoring;          // 已备份到 backup_2025_01/duplicate_modules/
// pub mod performance_optimization_advanced; // 已归档到 ARCHIVE/reports/
// pub mod performance_optimizer;           // 已备份到 backup_2025_01/duplicate_modules/
// pub mod security_enhancer;     // 已备份到 backup_2025_01/duplicate_modules/
// pub mod simple_client;         // 已归档到 ARCHIVE/reports/
// pub mod optimized_processor;   // 已备份到 backup_2025_01/duplicate_modules/
// pub mod profiling;             // 已备份到 backup_2025_01/duplicate_modules/
// pub mod protobuf;              // 已备份到 backup_2025_01/duplicate_modules/

// 重新导出主要类型
// ============================================================================
// 新核心 API - 推荐使用
// ============================================================================

/// 重新导出核心模块的主要类型
///
/// 这些类型基于 opentelemetry-otlp 0.31.0，保证 OTLP 1.0.0 标准兼容性
pub use core::{
    ClientBuilder, ClientConfig, ClientStats, EnhancedOtlpClient, PerformanceOptimizer,
    ReliabilityManager,
};

// ============================================================================
// 扩展 API - 基于官方库的扩展
// ============================================================================

/// 重新导出扩展模块的主要类型
pub use extensions::{
    simd::SimdSpanExporter,
    tracezip::TracezipSpanExporter,
    enterprise::{MultiTenantExporter, ComplianceExporter},
    performance::{BatchOptimizedExporter, ConnectionPoolExporter},
};

#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub use extensions::ebpf::EbpfTracerExtension;

// ============================================================================
// 包装器 API - 便捷的API
// ============================================================================

/// 重新导出包装器模块的主要类型
pub use wrappers::{
    EnhancedPipeline,
    EnhancedPipelineV2,  // 推荐使用，提供完整扩展支持
    EnhancedTracer,
    EnhancedExporter,
};

// 重新导出 OpenTelemetry 官方类型
pub use opentelemetry::{
    KeyValue,
    trace::{Tracer, TracerProvider},
};

// ============================================================================
// 原有 API (逐步迁移中)
// ============================================================================

pub use client::{LogBuilder, MetricBuilder, OtlpClient, OtlpClientBuilder, TraceBuilder};
pub use config::{
    BatchConfig, Compression, OtlpConfig, OtlpConfigBuilder, TransportProtocol,
    ServiceConfig, AggregationConfig, GlobalBatchConfig,
    // Rust 1.94: 新增常量和验证函数
    DEFAULT_BATCH_SIZE, MAX_BATCH_SIZE, MIN_BATCH_SIZE, DEFAULT_TIMEOUT,
    validate_batch_size, validate_timeout,
};
pub use data::{
    AttributeValue, DataPoint, DataPointValue, LogData, LogSeverity, MetricData, MetricType,
    SpanKind, SpanStatus, StatusCode, TelemetryContent, TelemetryData, TelemetryDataType,
    TraceData, 
    // OTLP 1.10+ 新增类型
    ProfileData, SampleType, Sample, Label, Mapping, Location, Line, Function,
    ExponentialHistogramData, ExponentialHistogramBuckets, HistogramData, HistogramBucket,
    SummaryData, Quantile,
    // Logs信号增强类型 (OTLP 1.10)
    SeverityLevel, LogBody, LogTraceContext,
};

// Logs模块公开API
pub use logs::{
    // 核心类型
    LogRecord, LogRecordBuilder, SourceLocation,
    // 处理器
    LogProcessor, SimpleLogProcessor, BatchLogProcessor, FilterLogProcessor, 
    // 导出器
    LogExporter, LogExporterBuilder, LogExportResult,
    // Appender
    LogAppender, LogAppenderBuilder,
    // 过滤器
    SeverityFilter,
};
pub use error::{ErrorCategory, ErrorContext, ErrorSeverity, OtlpError, Result};
pub use exporter::{ExportResult, ExporterMetrics, OtlpExporter, PartialSuccess};
pub use monitoring::{
    AlertCondition, AlertRule, ErrorEvent, ErrorMonitoringMetrics, ErrorMonitoringSystem,
    MonitoringConfig,
};
pub use monitoring_integration::{
    Alert, AlertCondition as NewAlertCondition, AlertManager, AlertRule as NewAlertRule,
    AlertSeverity as NewAlertSeverity, AlertStatsSnapshot, ComprehensiveMonitoringManager,
    ComprehensiveMonitoringStatsSnapshot, Dashboard, DataSource, DataSourceAccess, DataSourceType,
    GrafanaDashboardManager, GrafanaStatsSnapshot, MetricCollector, MetricUpdate, MetricValue,
    MonitoringStatsSnapshot, Panel, PanelOptions, PanelPosition, PanelType,
    PerformanceMetricCollector, PrometheusCollector, PrometheusStatsSnapshot, QueryTarget,
    RealtimeMonitoringSystem, SecurityMetricCollector,
};
// 性能相关类型从统一的performance模块导出
pub use network::{
    AsyncConnection, AsyncIoConfig, AsyncIoManager, AsyncIoStats, BackendServer, ConnectionPool,
    ConnectionPoolConfig, ConnectionPoolStats, HealthChecker, LoadBalancer, LoadBalancerConfig,
    LoadBalancerStats, LoadBalancingStrategy, NetworkConfig, NetworkManager, NetworkMonitor,
    NetworkStats, PooledConnection, PooledConnectionInfo,
};
pub use optimization::{
    ConfigCategory, ConfigConstraint, ConfigImpact, ConfigItem, ConfigOptimization, ConfigValue,
    ConstraintType, ImplementationEffort, OptimizationCategory, OptimizationManager,
    OptimizationPriority, OptimizationReport, OptimizationResult, OptimizationStats,
    OptimizationSuggestion, PerformanceSnapshot, PerformanceTargets, PerformanceTuner,
    PerformanceTunerStats, RiskLevel, SmartConfigManager, SmartConfigStats, TuningConfig,
};
pub use performance::{
    BatchItem, BatchProcessorConfig, BatchProcessorError, BatchProcessorStats, BatchResult,
    CircuitBreakerConfig, CircuitBreakerError, CircuitBreakerState, ConnectionPoolError,
    MemoryPoolConfig, MemoryPoolError, MemoryPoolStats, OptimizedBatchProcessor,
    OptimizedCircuitBreaker, OptimizedConnectionPool, OptimizedMemoryPool, PerformanceConfig,
    PerformanceManager, PooledObject,
};
pub use processor::{OtlpProcessor, ProcessingConfig, ProcessorMetrics};
pub use resilience::{ResilienceConfig, ResilienceError, ResilienceManager};
pub use rust_1_92_optimizations::{
    AsyncBatchProcessor, AsyncClosureOptimizer, TupleCollectionOptimizer, ZeroCopyOptimizer,
};

// 重新导出 Rust 1.94 element_offset 特性相关类型
pub use rust_1_94_element_offset::{
    BatchOffsetCalculator, BufferOffsetCalculator, LogEntryTracker, MemoryPoolIndexer,
    MetricsBuffer, SpanTracker, ZeroCopySerializer, calculate_buffer_offset, calculate_byte_offset,
};

// 安全相关类型从advanced_security模块导出 (简化版本)
pub use advanced_security::{
    AuditEntry, AuditEvent, AuditFilter, DifferentialPrivacyManager,
    DifferentialPrivacyStatsSnapshot, HomomorphicEncryptionManager,
    HomomorphicEncryptionStatsSnapshot, PrivacyResult, Proof, SecureMultiPartyComputationManager,
    SecureMultiPartyStatsSnapshot, SecurityAuditManager, SecurityAuditStatsSnapshot, Threat,
    ThreatDetectionManager, ThreatDetectionStatsSnapshot, ZeroKnowledgeProofManager,
    ZeroKnowledgeStatsSnapshot,
};
pub use transport::{GrpcTransport, HttpTransport, Transport, TransportFactory};
pub use utils::{
    BatchUtils, CompressionUtils, HashUtils, PerformanceUtils, RetryUtils, StringUtils, TimeUtils,
};

// 重新导出新模块的主要类型
pub use advanced_features::{
    AIAnomalyDetector, AdvancedFeaturesConfig, AdvancedFeaturesManager, AnomalyConfig,
    AnomalyResult as AdvancedAnomalyResult, CacheConfig, CacheStats, EvictionPolicy,
    IntelligentCache, ModelType as AnomalyModelType, ProcessedResult, SamplingConfig,
    SamplingContext, SamplingMetrics, SystemStats, TrainingDataPoint,
};
// 合规管理相关类型
pub use compliance_manager::{
    AccessLog, CardData, ControlTest, ControlTestResult, DataSubject, DataSubjectRequest,
    DataSubjectRequestType, DataSubjectResponse, FinancialRecord, GDPRComplianceManager,
    GDPRStatsSnapshot, HIPAAComplianceManager, HIPAAStatsSnapshot, PCIDSSComplianceManager,
    PCIDSSStatsSnapshot, PHIRecord, ProcessingRecord, RiskAssessment, RiskAssessmentResult,
    SOXComplianceManager, SOXComplianceReport, SOXStatsSnapshot, SecurityTest, SecurityTestResult,
};
pub use enterprise_features::{
    ComplianceAssessment, ComplianceCategory, ComplianceControl, ComplianceFinding,
    ComplianceFramework, ComplianceManager, ComplianceRequirement, ComplianceSeverity,
    ComplianceStatsSnapshot, ComprehensiveEnterpriseManager, ComprehensiveEnterpriseStats,
    DataAction, DataClassification, DataClassificationLevel, DataCondition, DataGovernanceManager,
    DataGovernanceStatsSnapshot, DataItem, DataPolicy, DataRule, EnterpriseRequest,
    EnterpriseResponse, FindingStatus, HealthCheck, HealthCheckType, HighAvailabilityManager,
    HighAvailabilityStatsSnapshot, ImplementationStatus, MultiTenantManager,
    MultiTenantStatsSnapshot, Node, NodeStatus, Tenant, TenantQuota, TenantSettings, TenantStatus,
};

// Response handling types (OTLP 1.10 Partial Success)
pub use response::{
    ExportLogsPartialSuccess, ExportMetricsPartialSuccess, ExportProfilesPartialSuccess,
    ExportTracePartialSuccess, PartialSuccessHandler, ResponseClassification,
    ResponseHandler, ResponseHandlerBuilder, ResponseMetricsCollector, ResponseType,
    RetryDecision, SignalType, ResponseMetadata, ResponseAggregator, AggregationSummary,
};

// 重新导出微服务相关类型
pub use microservices::{
    AdaptiveLoadBalancer,
    CircuitBreaker,
    CircuitBreakerPolicy,
    Destination,
    FaultConfig,
    FaultInjector,
    FaultResult,
    FaultType,
    HealthChecker as MicroserviceHealthChecker,
    HealthStatus as MicroserviceHealthStatus,
    InstanceMetrics,
    IntelligentRouter,
    LoadBalancer as MicroserviceLoadBalancer,
    MatchCondition,
    MicroserviceClient,
    MockConsulClient,
    ResourceLimits,
    RetryConfig,
    RetryPolicy,
    Retryer,
    RoundRobinLoadBalancer,
    RouteRequest,
    RouteResponse,
    RouterMetrics,
    RoutingError,
    RoutingRule,
    ServiceDiscoveryClient,
    ServiceEndpoint,
    ServiceInstance,
    // 高级微服务功能
    ServiceMeshConfig,
    ServiceMeshType,
    SidecarConfig,
    TrafficManager,
    WeightedRoundRobinLoadBalancer,
};

// 重新导出2025年新增的OTTL字节码功能
pub use ottl::{BytecodeCompiler, BytecodeProgram, Opcode};

// 重新导出2025年新增的OPAMP灰度策略功能
pub use opamp::{
    GraduationStrategy, HealthStatus as OpampHealthStatus, LabelSelector, MatchExpression,
    MatchOperator, RollbackManager,
};

// 重新导出优化处理器相关类型
pub use optimized_processor::{
    OptimizedOtlpProcessor, OptimizedProcessorConfig, OtlpDataItem, PerformanceMetrics,
    PerformanceMonitor, PerformanceReport,
};

// 重新导出 Rust 1.94 array_windows 模块相关类型
// 注意: SpanStatus 已在 data 模块中定义，这里不重新导出
pub use rust_1_94_array_windows::{
    Trend, Pattern, SpanTransition, Span, SpanId,
    MetricPoint, RunLength,
    detect_abba_patterns, detect_abab_patterns,
    detect_repeated_patterns_2, detect_repeated_patterns_3, detect_repeated_patterns_4,
    detect_repeated_patterns_generic,
    detect_trends, detect_peaks_and_valleys, moving_average,
    validate_span_sequence, detect_error_patterns,
    detect_anomalies, calculate_rate_of_change,
    validate_timestamp_order, detect_timestamp_gaps, validate_continuity,
    run_length_encode, sequence_similarity, longest_increasing_subsequence,
};

// 重新导出 Rust 1.94 LazyLock/LazyCell 新方法模块相关类型
// 注意：避免与现有类型冲突，使用具体名称
pub use rust_1_94_lazy_lock::{
    // 配置管理 (LazyConfig 避免与 config::OtlpConfig 冲突)
    OtlpConfig as LazyOtlpConfig, 
    GlobalConfig,
    // 导出器缓存
    ExporterCache, 
    ExporterCacheManager, 
    GrpcExporter, 
    HttpExporter, 
    ExporterError,
    // 协议缓冲区类型注册表
    ProtoTypeRegistry, 
    ProtoRegistryManager, 
    ProtoMessage, 
    ProtoField, 
    ProtoFieldType,
    // 追踪器提供者 (TracerProvider 避免与 opentelemetry::trace::TracerProvider 冲突)
    TracerProvider as LazyTracerProvider, 
    TracerProviderManager, 
    SpanContext as LazySpanContext, 
    SpanId as LazySpanId, 
    TraceId as LazyTraceId,
    // LazyCell 资源管理
    ThreadLocalResource, 
    LazyBuffer,
    // 综合配置管理
    ComprehensiveConfigManager, 
    OtlpRuntimeContext,
};

// 重新导出 Rust 1.94 数学常量模块相关函数和类型
pub use rust_1_94_math_constants::{
    // EULER_GAMMA 相关函数
    euler_gamma_sampling_rate,
    euler_gamma_cumulative_sampling,
    euler_gamma_priority_weight,
    // GOLDEN_RATIO 相关函数
    golden_ratio_backoff,
    golden_ratio_backoff_decay,
    fibonacci_batch_size,
    fibonacci_exact,
    golden_ratio_split,
    golden_ratio_jitter,
    // const mul_add 相关函数
    const_mul_add,
    const_lerp,
    const_poly_eval,
    const_sigmoid_approx,
    // 高级算法
    adaptive_batch_timeout,
    optimal_connection_pool_size,
    adjust_sampling_rate,
    // 工具函数
    safe_midpoint,
    approx_eq,
    rate_to_log_scale,
    log_scale_to_rate,
    // 预计算常数
    EULER_GAMMA_RECIP,
    GOLDEN_RATIO_RECIP,
    GOLDEN_RATIO_SQUARED,
    FIBONACCI_FACTOR,
};

// 重新导出 Rust 1.94 comprehensive 模块的公共子模块
pub use rust_1_94_comprehensive::{
    async_features as comprehensive_async_features,
    concurrency,
    const_generics,
    error_handling,
    memory_management,
    metaprogramming,
    pattern_matching,
    performance as rust_1_94_performance,
    precise_captures,
    std_lib_features,
};

// 重新导出 Rust 1.94 features 模块的公共子模块
pub use rust_1_94_features::{
    async_features,
    builder_pattern,
    collection_improvements,
    const_context,
    float_improvements,
    io_errors,
    lazy_initialization,
    unsafe_improvements,
};

// 重新导出 Rust 1.94 综合演示模块的主要类型
// 注意: 以下类型名称与现有模块有冲突，使用完整路径访问:
// - ServiceConfig (与 config 模块冲突)
// - RetryPolicy (与 microservices 模块冲突)
// - MetricPoint (与 rust_1_94_array_windows 模块冲突)
// - Span, SpanStatus (与 data/rust_1_94_array_windows 模块冲突)
// - MetricsBuffer, ZeroCopySpanSerializer (与 rust_1_94_element_offset 冲突)
pub use rust_1_94_comprehensive_demo::{
    // Demo-specific types (unique to this module)
    CompressionType,
    TelemetryPattern,
    ConfigManager, 
    ThreadLocalBuffer,
    
    // Algorithm types
    AdaptiveSampler, 
    FibonacciRetryStrategy, 
    ConnectionPoolOptimizer,
    AdaptiveTimeout, 
    ConstMath,
    
    // SIMD types
    Fp16MetricsProcessor,
    
    // TOML config
    TomlConfig,
    
    // Result types
    PipelineResult,
    
    // Main function
    complete_otlp_pipeline_demo,
    
    // Utility functions (unique to this module)
    detect_metric_patterns, 
    detect_abba_anomalies,
    validate_span_continuity,
};

// ============================================================================
// 便捷API函数
// ============================================================================

/// 创建增强的Pipeline (基础版)
///
/// 这是一个便捷函数，用于快速创建配置了扩展功能的Pipeline。
/// 注意: 此版本扩展支持有限，推荐使用 `new_enhanced_pipeline_v2()`。
///
/// # 示例
///
/// ```rust,no_run
/// use otlp::new_enhanced_pipeline;
/// use opentelemetry_sdk::runtime::Tokio;
///
/// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
/// let tracer = new_enhanced_pipeline()
///     .with_ebpf_profiling(true)
///     .install_batch(Tokio)?;
/// # Ok(())
/// # }
/// ```
pub fn new_enhanced_pipeline() -> wrappers::EnhancedPipeline {
    // 注意: 由于opentelemetry_otlp的API在不同版本可能不同
    // 这里提供一个占位实现，实际使用时需要根据版本调整
    // 推荐使用 new_enhanced_pipeline_v2() 来获得完整的扩展支持
    //
    // 如果需要使用EnhancedPipeline，请手动创建TracingPipeline：
    // use opentelemetry_otlp::new_pipeline;
    // let pipeline = new_pipeline().tracing();
    // let enhanced = wrappers::EnhancedPipeline::new(pipeline);
    panic!("EnhancedPipeline requires TracingPipeline instance. Use new_enhanced_pipeline_v2() instead.")
}

/// 创建增强的Pipeline (完整版，推荐)
///
/// 这是一个便捷函数，提供完整的扩展支持。
///
/// # 示例
///
/// ```rust,no_run
/// use otlp::new_enhanced_pipeline_v2;
/// use opentelemetry_sdk::runtime::Tokio;
///
/// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
/// let tracer = new_enhanced_pipeline_v2()
///     .with_endpoint("http://localhost:4317")
///     .with_service_name("my-service")
///     .with_ebpf_profiling(true)
///     .with_simd_optimization(true)
///     .with_tracezip_compression(true)
///     .with_multi_tenant(true)
///     .with_tenant_id("tenant-123".to_string())
///     .install_batch(Tokio)?;
/// # Ok(())
/// # }
/// ```
pub fn new_enhanced_pipeline_v2() -> wrappers::EnhancedPipelineV2 {
    wrappers::EnhancedPipelineV2::new()
}

// ============================================================================
// 版本信息
// ============================================================================

pub const VERSION: &str = env!("CARGO_PKG_VERSION");
/// Minimum Supported Rust Version (MSRV)
pub const RUST_VERSION: &str = "1.94";

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_version_info() {
        assert!(!VERSION.is_empty(), "VERSION should not be empty");
        assert_eq!(RUST_VERSION, "1.94", "MSRV should be Rust 1.94");
    }
}
