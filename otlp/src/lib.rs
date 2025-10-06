#![allow(clippy::excessive_nesting)]
//! # OpenTelemetry Protocol (OTLP) Implementation for Rust 1.90
//!
//! 本库提供了基于Rust 1.90语言特性的OpenTelemetry协议(OTLP)完整实现，
//! 支持同步和异步结合的遥测数据收集、处理和传输。
//!
//! ## 设计理念
//!
//! 本库基于以下核心设计理念构建：
//!
//! 1. **性能优先**: 利用Rust 1.90的性能特性，实现零拷贝、无锁并发的高性能处理
//! 2. **类型安全**: 利用Rust类型系统在编译时捕获错误，避免运行时异常
//! 3. **异步优先**: 基于tokio异步运行时，支持高并发和低延迟处理
//! 4. **可观测性**: 内置完整的监控、日志和指标收集机制
//! 5. **可扩展性**: 模块化设计，支持插件和自定义扩展
//! 6. **标准化**: 完全兼容OpenTelemetry规范，确保跨语言互操作性
//!
//! ## 核心特性
//!
//! - **异步优先设计**: 利用Rust 1.90的async/await特性实现高性能异步处理
//! - **同步兼容**: 提供同步API接口，支持传统同步代码集成
//! - **多传输协议**: 支持gRPC和HTTP/JSON两种OTLP传输方式
//! - **类型安全**: 利用Rust类型系统确保编译时安全性
//! - **零拷贝优化**: 使用Rust 1.90的内存管理特性优化性能
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
//! - **智能内存管理**: 基于Rust 1.90的内存管理特性
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
//! │ • 实时监控  • 告警系统  • 性能分析  • 趋势预测  • 可视化            │
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

pub mod advanced_features;
pub mod advanced_performance;
pub mod advanced_security;
pub mod ai_ml;
pub mod compliance_manager;
pub mod benchmarks;
pub mod blockchain;
pub mod client;
pub mod config;
pub mod data;
pub mod edge_computing;
pub mod enterprise_features;
pub mod error;
pub mod exporter;
pub mod microservices;
pub mod monitoring;
pub mod monitoring_integration;
pub mod opamp;
pub mod optimized_processor;
pub mod ottl;
pub mod performance;
pub mod performance_enhancements;
pub mod performance_monitoring;
pub mod performance_optimization_advanced;
pub mod performance_optimizer;
pub mod processor;
pub mod profiling;
pub mod protobuf;
pub mod resilience;
pub mod network;
pub mod optimization;
pub mod rust_1_90_optimizations;
pub mod security_enhancer;
pub mod simple_client;
pub mod transport;
pub mod utils;
pub mod validation;

// 重新导出主要类型
pub use client::{LogBuilder, MetricBuilder, OtlpClient, OtlpClientBuilder, TraceBuilder};
pub use config::{BatchConfig, Compression, OtlpConfig, OtlpConfigBuilder, TransportProtocol};
pub use data::{
    AttributeValue, DataPoint, DataPointValue, LogData, LogSeverity, MetricData, MetricType,
    SpanKind, SpanStatus, StatusCode, TelemetryContent, TelemetryData, TelemetryDataType,
    TraceData,
};
pub use error::{ErrorCategory, ErrorContext, ErrorSeverity, OtlpError, Result};
pub use exporter::{ExportResult, ExporterMetrics, OtlpExporter};
pub use monitoring::{
    AlertCondition, AlertRule, ErrorEvent, ErrorMonitoringMetrics, ErrorMonitoringSystem,
    MonitoringConfig,
};
pub use monitoring_integration::{
    Alert, AlertCondition as NewAlertCondition, AlertManager, AlertRule as NewAlertRule, AlertSeverity as NewAlertSeverity, AlertStatsSnapshot,
    ComprehensiveMonitoringManager, ComprehensiveMonitoringStatsSnapshot, Dashboard, DataSource,
    DataSourceAccess, DataSourceType, GrafanaDashboardManager, GrafanaStatsSnapshot,
    MetricCollector, MetricUpdate, MetricValue, MonitoringStatsSnapshot, Panel, PanelOptions,
    PanelPosition, PanelType, PerformanceMetricCollector, PrometheusCollector,
    PrometheusStatsSnapshot, QueryTarget, RealtimeMonitoringSystem, SecurityMetricCollector,
};
pub use optimized_processor::{
    OptimizedOtlpProcessor, OptimizedProcessorConfig, OtlpDataItem, PerformanceMetrics,
    PerformanceMonitor, PerformanceReport, ProcessedItem,
};
pub use performance::{
    BatchItem, BatchProcessorConfig, BatchProcessorError, BatchProcessorStats, BatchResult,
    CircuitBreakerConfig, CircuitBreakerError, CircuitBreakerState,
    ConnectionPoolError, MemoryPoolConfig, MemoryPoolError, MemoryPoolStats,
    OptimizedBatchProcessor, OptimizedCircuitBreaker, OptimizedConnectionPool, OptimizedMemoryPool,
    PerformanceConfig, PerformanceManager, PooledObject,
};
pub use performance_enhancements::{
    AsyncGenerator, BatchProcessorMetricsSnapshot, ExecutorMetricsSnapshot,
    HighPerformanceBatchProcessor, HighPerformanceExecutor, HighPerformanceMemoryPool as LegacyHighPerformanceMemoryPool,
    MemoryPoolMetricsSnapshot,
};
pub use performance_monitoring::{
    AlertSeverity, AlertType, PerformanceAlert, PerformanceDataPoint, PerformanceMonitoringConfig,
    PerformanceSummary, PerformanceThresholds, RealtimePerformanceMonitor,
};
pub use performance_optimization_advanced::{
    AdvancedMemoryPoolOptimizer, AdvancedSimdOptimizer, BenchmarkResults, CacheOptimizationManager,
    CachePerformanceMetrics, ComprehensivePerformanceOptimizer, SimdIntOperation, SimdOperation,
};
pub use performance_optimizer::{
    BenchmarkConfig, BenchmarkResult, ComprehensivePerformanceOptimizer as NewComprehensivePerformanceOptimizer,
    ComprehensivePerformanceStats, ConcurrencyOptimizer, ConcurrencyStatsSnapshot, HighPerformanceMemoryPool,
    MemoryPoolStatsSnapshot, PerformanceBenchmarker, PooledObject as NewPooledObject, SimdOptimizer, SimdStatsSnapshot,
};
pub use processor::{OtlpProcessor, ProcessingConfig, ProcessorMetrics};
pub use resilience::{ResilienceConfig, ResilienceError, ResilienceManager};
pub use network::{
    AsyncConnection, AsyncIoConfig, AsyncIoManager, AsyncIoStats, BackendServer,
    ConnectionPool, ConnectionPoolConfig, ConnectionPoolStats, HealthChecker,
    LoadBalancer, LoadBalancerConfig, LoadBalancerStats, LoadBalancingStrategy,
    NetworkConfig, NetworkManager, NetworkMonitor, NetworkStats, PooledConnection,
    PooledConnectionInfo,
};
pub use optimization::{
    ConfigCategory, ConfigConstraint, ConfigImpact, ConfigItem, ConfigOptimization, ConfigValue,
    ConstraintType, ImplementationEffort, OptimizationCategory, OptimizationManager,
    OptimizationPriority, OptimizationReport, OptimizationResult, OptimizationSuggestion,
    OptimizationStats, PerformanceSnapshot, PerformanceTargets,
    PerformanceTuner, PerformanceTunerStats, RiskLevel, SmartConfigManager, SmartConfigStats,
    TuningConfig,
};
pub use rust_1_90_optimizations::{
    AsyncBatchProcessor, AsyncClosureOptimizer, TupleCollectionOptimizer, ZeroCopyOptimizer,
};
pub use security_enhancer::{
    AuditLog, AuditLogFilter, AuditLogger, AuditResult, AuditStatsSnapshot, AuthCondition,
    AuthPolicy, AuthResult, AuthRule, AuthStatsSnapshot, AuthValidationResult, AuthenticationManager,
    ComprehensiveSecurityManager, ComprehensiveSecurityStats, EncryptionAlgorithm, EncryptionManager,
    EncryptionStatsSnapshot, EncryptedData, SecurityPolicy, SecurityRule, SecuritySeverity,
    SecureRequest, SecureResponse, Session, User,
};
pub use simple_client::{
    HealthStatus, LogLevel, SimpleClientBuilder, SimpleOperation, SimpleOtlpClient,
};
pub use transport::{GrpcTransport, HttpTransport, Transport, TransportFactory};
pub use utils::{
    BatchUtils, CompressionUtils, HashUtils, PerformanceUtils, RetryUtils, StringUtils, TimeUtils,
};

// 重新导出新模块的主要类型
pub use advanced_features::{
    AdvancedFeaturesConfig, AdvancedFeaturesManager, AIAnomalyDetector, AnomalyConfig,
    AnomalyResult as AdvancedAnomalyResult, CacheConfig, CacheStats, EvictionPolicy, IntelligentCache,
    ProcessedResult, SamplingConfig, SamplingContext, SamplingMetrics, SystemStats,
    TrainingDataPoint, ModelType as AnomalyModelType,
};
pub use advanced_performance::{
    BatchProcessor, BatchStatsSnapshot, BufferPool, BufferPoolStatsSnapshot, CacheOptimizer,
    CacheStatsSnapshot, Connection, LockFreeDataManager, LockFreeStatsSnapshot,
    NetworkOptimizer, NetworkStatsSnapshot, ProcessingStatsSnapshot, ZeroCopyProcessor,
};
pub use advanced_security::{
    AuditEntry, AuditEvent, AuditFilter, DifferentialPrivacyManager, DifferentialPrivacyStatsSnapshot,
    HomomorphicEncryptionManager, HomomorphicEncryptionStatsSnapshot, PrivacyResult,
    Proof, SecureMultiPartyComputationManager, SecureMultiPartyStatsSnapshot, SecurityAuditManager,
    SecurityAuditStatsSnapshot, Threat, ThreatDetectionManager, ThreatDetectionStatsSnapshot,
    ZeroKnowledgeProofManager, ZeroKnowledgeStatsSnapshot,
};
pub use compliance_manager::{
    AccessLog, CardData, ControlTest, ControlTestResult, DataSubject, DataSubjectRequest,
    DataSubjectRequestType, DataSubjectResponse, FinancialRecord, GDPRComplianceManager,
    GDPRStatsSnapshot, HIPAAComplianceManager, HIPAAStatsSnapshot, PCIDSSComplianceManager,
    PCIDSSStatsSnapshot, PHIRecord, ProcessingRecord, RiskAssessment, RiskAssessmentResult,
    SecurityTest, SecurityTestResult, SOXComplianceManager, SOXComplianceReport, SOXStatsSnapshot,
};
pub use ai_ml::{AiMlAnalyzer, AiMlConfig, AnomalyResult, MlModel, ModelType, PredictionResult};
pub use blockchain::{Block, BlockchainManager, ConsensusAlgorithm, SmartContract, Transaction};
pub use edge_computing::{EdgeComputingManager, EdgeNode, EdgeTask, TaskPriority, TaskType};
pub use enterprise_features::{
    ComplianceAssessment, ComplianceCategory, ComplianceControl, ComplianceFinding,
    ComplianceFramework, ComplianceManager, ComplianceRequirement, ComplianceSeverity,
    ComplianceStatsSnapshot, ComprehensiveEnterpriseManager, ComprehensiveEnterpriseStats,
    DataAction, DataClassification, DataClassificationLevel, DataCondition, DataGovernanceManager,
    DataGovernanceStatsSnapshot, DataItem, DataPolicy, DataRule, EnterpriseRequest,
    EnterpriseResponse, FindingStatus, HighAvailabilityManager, HighAvailabilityStatsSnapshot,
    HealthCheck, HealthCheckType, ImplementationStatus, MultiTenantManager,
    MultiTenantStatsSnapshot, Node, NodeStatus, Tenant, TenantQuota, TenantSettings,
    TenantStatus,
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

// 版本信息
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
pub const RUST_VERSION: &str = "1.90";

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_version_info() {
        assert!(!VERSION.is_empty());
        assert_eq!(RUST_VERSION, "1.90");
    }
}
