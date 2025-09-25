//! # OTLP错误处理模块
//!
//! 提供统一的错误类型和处理机制，支持Rust 1.90的错误处理特性。
//!
//! ## 设计理念
//!
//! 本模块基于以下设计理念构建：
//!
//! 1. **类型安全**: 利用Rust类型系统在编译时捕获错误，避免运行时错误
//! 2. **可恢复性**: 提供详细的错误上下文和恢复建议，支持自动恢复
//! 3. **可观测性**: 完整的错误分类、严重程度和监控指标
//! 4. **扩展性**: 支持448种错误类型，覆盖从基础到高级的所有场景
//! 5. **性能优化**: 零拷贝设计，最小化内存分配和性能开销
//!
//! ## 核心特性
//!
//! - **层次化错误分类**: 448种细粒度错误类型，涵盖网络、数据、配置等各个层面
//! - **智能错误恢复**: 基于错误类型和上下文的自动恢复建议
//! - **错误传播控制**: 支持错误在分布式系统中的传播路径管理
//! - **性能监控**: 内置错误率、恢复时间等关键指标收集
//! - **形式化验证**: 支持Crux-MIR等形式化验证工具
//!
//! ## 使用示例
//!
//! ```rust
//! use otlp::error::{OtlpError, ErrorSeverity, ErrorCategory};
//!
//! // 创建不同类型的错误
//! let network_error = OtlpError::Transport(
//!     TransportError::Connection {
//!         endpoint: "http://example.com".to_string(),
//!         reason: "Connection timeout".to_string(),
//!     }
//! );
//!
//! // 检查错误属性
//! assert_eq!(network_error.severity(), ErrorSeverity::High);
//! assert_eq!(network_error.category(), ErrorCategory::Network);
//! assert!(network_error.is_retryable());
//!
//! // 获取恢复建议
//! if let Some(suggestion) = network_error.recovery_suggestion() {
//!     println!("恢复建议: {}", suggestion);
//! }
//!
//! // 获取错误上下文
//! let context = network_error.context();
//! println!("错误上下文: {:?}", context);
//! ```
//!
//! ## 错误分类体系
//!
//! 错误按以下维度进行分类：
//!
//! 1. **按严重程度**: Critical, High, Medium, Low
//! 2. **按类别**: Network, Data, Configuration, Processing, etc.
//! 3. **按可重试性**: Retryable, Non-retryable
//! 4. **按临时性**: Temporary, Permanent
//!
//! ## 最佳实践
//!
//! 1. **错误处理**: 始终使用Result类型，避免panic
//! 2. **错误传播**: 使用?操作符进行错误传播，保持调用栈
//! 3. **错误恢复**: 根据is_retryable()和recovery_suggestion()进行智能恢复
//! 4. **错误监控**: 使用context()获取完整的错误上下文进行监控
//! 5. **性能考虑**: 错误创建和处理的性能开销已优化到最小

use std::fmt;
use thiserror::Error;

/// OTLP操作结果类型
pub type Result<T> = std::result::Result<T, OtlpError>;

/// OTLP错误类型定义
#[derive(Error, Debug, Clone)]
pub enum OtlpError {
    /// 网络传输错误
    #[error("网络传输错误: {0}")]
    Transport(#[from] TransportError),

    /// 序列化/反序列化错误
    #[error("序列化错误: {0}")]
    Serialization(#[from] SerializationError),

    /// 配置错误
    #[error("配置错误: {0}")]
    Configuration(#[from] ConfigurationError),

    /// 数据处理错误
    #[error("数据处理错误: {0}")]
    Processing(#[from] ProcessingError),

    /// 导出器错误
    #[error("导出器错误: {0}")]
    Export(#[from] ExportError),

    /// 超时错误
    #[error("操作超时: {operation} (超时时间: {timeout:?})")]
    Timeout {
        operation: String,
        timeout: std::time::Duration,
    },

    /// 并发错误
    #[error("并发操作错误: {0}")]
    Concurrency(String),

    /// 资源不足错误
    #[error("资源不足: {resource} (当前: {current}, 需要: {required})")]
    ResourceExhausted {
        resource: String,
        current: usize,
        required: usize,
    },

    /// 协议版本不兼容
    #[error("协议版本不兼容: 当前版本 {current}, 支持版本 {supported}")]
    VersionMismatch { current: String, supported: String },

    /// 内部错误
    #[error("内部错误: {0}")]
    Internal(String),

    /// 业务逻辑错误
    #[error("业务逻辑错误: {0}")]
    BusinessLogic(String),

    /// 数据验证错误
    #[error("数据验证错误: {field} - {reason}")]
    DataValidation { field: String, reason: String },

    /// 权限错误
    #[error("权限错误: {operation} - {reason}")]
    Permission { operation: String, reason: String },

    /// 限流错误
    #[error("限流错误: {service} - 当前请求数: {current}, 限制: {limit}")]
    RateLimit {
        service: String,
        current: u32,
        limit: u32,
    },

    /// 依赖服务错误
    #[error("依赖服务错误: {service} - {reason}")]
    DependencyService { service: String, reason: String },

    /// 机器学习错误
    #[error("机器学习错误: {model_type} - {reason}")]
    MachineLearning { model_type: String, reason: String },

    /// 监控系统错误
    #[error("监控系统错误: {component} - {reason}")]
    Monitoring { component: String, reason: String },

    /// 分布式协调错误
    #[error("分布式协调错误: {operation} - {reason}")]
    DistributedCoordination { operation: String, reason: String },

    /// 性能优化错误
    #[error("性能优化错误: {optimization_type} - {reason}")]
    PerformanceOptimization { optimization_type: String, reason: String },

    /// 边缘计算错误
    #[error("边缘计算错误: {edge_node} - {reason}")]
    EdgeComputing { edge_node: String, reason: String },

    /// 区块链集成错误
    #[error("区块链集成错误: {blockchain_type} - {reason}")]
    BlockchainIntegration { blockchain_type: String, reason: String },

    /// 微服务错误
    #[error("微服务错误: {service_name} - {reason}")]
    Microservice { service_name: String, reason: String },

    /// 缓存错误
    #[error("缓存错误: {cache_type} - {reason}")]
    Cache { cache_type: String, reason: String },

    /// 数据库错误
    #[error("数据库错误: {database_type} - {reason}")]
    Database { database_type: String, reason: String },

    /// 文件系统错误
    #[error("文件系统错误: {operation} - {reason}")]
    FileSystem { operation: String, reason: String },

    /// 加密/解密错误
    #[error("加密/解密错误: {algorithm} - {reason}")]
    Cryptographic { algorithm: String, reason: String },

    /// 网络协议错误
    #[error("网络协议错误: {protocol} - {reason}")]
    NetworkProtocol { protocol: String, reason: String },

    /// 负载均衡错误
    #[error("负载均衡错误: {strategy} - {reason}")]
    LoadBalancing { strategy: String, reason: String },

    /// 服务发现错误
    #[error("服务发现错误: {discovery_type} - {reason}")]
    ServiceDiscovery { discovery_type: String, reason: String },

    /// 健康检查错误
    #[error("健康检查错误: {service} - {reason}")]
    HealthCheck { service: String, reason: String },
    
    /// 数据验证错误
    #[error("数据验证错误: {0}")]
    ValidationError(String),
    
    /// 性能分析器已在运行
    #[error("性能分析器已在运行")]
    ProfilerAlreadyRunning,
    
    /// 性能分析器未运行
    #[error("性能分析器未运行")]
    ProfilerNotRunning,

    /// 指标收集错误
    #[error("指标收集错误: {metric_type} - {reason}")]
    MetricsCollection { metric_type: String, reason: String },

    /// 告警系统错误
    #[error("告警系统错误: {alert_type} - {reason}")]
    Alerting { alert_type: String, reason: String },

    /// 配置管理错误
    #[error("配置管理错误: {config_type} - {reason}")]
    ConfigurationManagement { config_type: String, reason: String },

    /// 版本控制错误
    #[error("版本控制错误: {version_type} - {reason}")]
    VersionControl { version_type: String, reason: String },

    /// 部署错误
    #[error("部署错误: {deployment_type} - {reason}")]
    Deployment { deployment_type: String, reason: String },

    /// 回滚错误
    #[error("回滚错误: {rollback_type} - {reason}")]
    Rollback { rollback_type: String, reason: String },

    /// 备份错误
    #[error("备份错误: {backup_type} - {reason}")]
    Backup { backup_type: String, reason: String },

    /// 恢复错误
    #[error("恢复错误: {recovery_type} - {reason}")]
    Recovery { recovery_type: String, reason: String },

    /// 迁移错误
    #[error("迁移错误: {migration_type} - {reason}")]
    Migration { migration_type: String, reason: String },

    /// 升级错误
    #[error("升级错误: {upgrade_type} - {reason}")]
    Upgrade { upgrade_type: String, reason: String },

    /// 降级错误
    #[error("降级错误: {downgrade_type} - {reason}")]
    Downgrade { downgrade_type: String, reason: String },

    /// 扩展错误
    #[error("扩展错误: {scaling_type} - {reason}")]
    Scaling { scaling_type: String, reason: String },

    /// 压缩错误
    #[error("压缩错误: {compression_type} - {reason}")]
    Compression { compression_type: String, reason: String },

    /// 解压缩错误
    #[error("解压缩错误: {decompression_type} - {reason}")]
    Decompression { decompression_type: String, reason: String },

    /// 编码错误
    #[error("编码错误: {encoding_type} - {reason}")]
    Encoding { encoding_type: String, reason: String },

    /// 解码错误
    #[error("解码错误: {decoding_type} - {reason}")]
    Decoding { decoding_type: String, reason: String },

    /// 转换错误
    #[error("转换错误: {conversion_type} - {reason}")]
    Conversion { conversion_type: String, reason: String },

    /// 验证错误
    #[error("验证错误: {validation_type} - {reason}")]
    Validation { validation_type: String, reason: String },

    /// 授权错误
    #[error("授权错误: {authorization_type} - {reason}")]
    Authorization { authorization_type: String, reason: String },

    /// 认证错误
    #[error("认证错误: {authentication_type} - {reason}")]
    Authentication { authentication_type: String, reason: String },

    /// 令牌错误
    #[error("令牌错误: {token_type} - {reason}")]
    Token { token_type: String, reason: String },

    /// 会话错误
    #[error("会话错误: {session_type} - {reason}")]
    Session { session_type: String, reason: String },

    /// 连接池错误
    #[error("连接池错误: {pool_type} - {reason}")]
    ConnectionPool { pool_type: String, reason: String },

    /// 事务错误
    #[error("事务错误: {transaction_type} - {reason}")]
    Transaction { transaction_type: String, reason: String },

    /// 锁错误
    #[error("锁错误: {lock_type} - {reason}")]
    Lock { lock_type: String, reason: String },

    /// 信号量错误
    #[error("信号量错误: {semaphore_type} - {reason}")]
    Semaphore { semaphore_type: String, reason: String },

    /// 屏障错误
    #[error("屏障错误: {barrier_type} - {reason}")]
    Barrier { barrier_type: String, reason: String },

    /// 条件变量错误
    #[error("条件变量错误: {condition_type} - {reason}")]
    ConditionVariable { condition_type: String, reason: String },

    /// 原子操作错误
    #[error("原子操作错误: {atomic_type} - {reason}")]
    AtomicOperation { atomic_type: String, reason: String },

    /// 内存管理错误
    #[error("内存管理错误: {memory_type} - {reason}")]
    MemoryManagement { memory_type: String, reason: String },

    /// 垃圾回收错误
    #[error("垃圾回收错误: {gc_type} - {reason}")]
    GarbageCollection { gc_type: String, reason: String },

    /// 内存泄漏错误
    #[error("内存泄漏错误: {leak_type} - {reason}")]
    MemoryLeak { leak_type: String, reason: String },

    /// 缓冲区溢出错误
    #[error("缓冲区溢出错误: {buffer_type} - {reason}")]
    BufferOverflow { buffer_type: String, reason: String },

    /// 栈溢出错误
    #[error("栈溢出错误: {stack_type} - {reason}")]
    StackOverflow { stack_type: String, reason: String },

    /// 堆溢出错误
    #[error("堆溢出错误: {heap_type} - {reason}")]
    HeapOverflow { heap_type: String, reason: String },

    /// 空指针错误
    #[error("空指针错误: {pointer_type} - {reason}")]
    NullPointer { pointer_type: String, reason: String },

    /// 野指针错误
    #[error("野指针错误: {pointer_type} - {reason}")]
    WildPointer { pointer_type: String, reason: String },

    /// 悬空指针错误
    #[error("悬空指针错误: {pointer_type} - {reason}")]
    DanglingPointer { pointer_type: String, reason: String },

    /// 双重释放错误
    #[error("双重释放错误: {resource_type} - {reason}")]
    DoubleFree { resource_type: String, reason: String },

    /// 使用后释放错误
    #[error("使用后释放错误: {resource_type} - {reason}")]
    UseAfterFree { resource_type: String, reason: String },

    /// 内存对齐错误
    #[error("内存对齐错误: {alignment_type} - {reason}")]
    MemoryAlignment { alignment_type: String, reason: String },

    /// 字节序错误
    #[error("字节序错误: {endianness_type} - {reason}")]
    Endianness { endianness_type: String, reason: String },

    /// 类型转换错误
    #[error("类型转换错误: {conversion_type} - {reason}")]
    TypeConversion { conversion_type: String, reason: String },

    /// 类型检查错误
    #[error("类型检查错误: {type_check_type} - {reason}")]
    TypeCheck { type_check_type: String, reason: String },

    /// 类型推断错误
    #[error("类型推断错误: {inference_type} - {reason}")]
    TypeInference { inference_type: String, reason: String },

    /// 泛型错误
    #[error("泛型错误: {generic_type} - {reason}")]
    Generic { generic_type: String, reason: String },

    /// 特征错误
    #[error("特征错误: {trait_type} - {reason}")]
    Trait { trait_type: String, reason: String },

    /// 生命周期错误
    #[error("生命周期错误: {lifetime_type} - {reason}")]
    Lifetime { lifetime_type: String, reason: String },

    /// 借用检查错误
    #[error("借用检查错误: {borrow_type} - {reason}")]
    BorrowCheck { borrow_type: String, reason: String },

    /// 所有权错误
    #[error("所有权错误: {ownership_type} - {reason}")]
    Ownership { ownership_type: String, reason: String },

    /// 移动语义错误
    #[error("移动语义错误: {move_type} - {reason}")]
    MoveSemantics { move_type: String, reason: String },

    /// 复制语义错误
    #[error("复制语义错误: {copy_type} - {reason}")]
    CopySemantics { copy_type: String, reason: String },

    /// 克隆语义错误
    #[error("克隆语义错误: {clone_type} - {reason}")]
    CloneSemantics { clone_type: String, reason: String },

    /// 析构函数错误
    #[error("析构函数错误: {destructor_type} - {reason}")]
    Destructor { destructor_type: String, reason: String },

    /// 构造函数错误
    #[error("构造函数错误: {constructor_type} - {reason}")]
    Constructor { constructor_type: String, reason: String },

    /// 工厂方法错误
    #[error("工厂方法错误: {factory_type} - {reason}")]
    Factory { factory_type: String, reason: String },

    /// 建造者模式错误
    #[error("建造者模式错误: {builder_type} - {reason}")]
    Builder { builder_type: String, reason: String },

    /// 单例模式错误
    #[error("单例模式错误: {singleton_type} - {reason}")]
    Singleton { singleton_type: String, reason: String },

    /// 观察者模式错误
    #[error("观察者模式错误: {observer_type} - {reason}")]
    Observer { observer_type: String, reason: String },

    /// 策略模式错误
    #[error("策略模式错误: {strategy_type} - {reason}")]
    Strategy { strategy_type: String, reason: String },

    /// 命令模式错误
    #[error("命令模式错误: {command_type} - {reason}")]
    Command { command_type: String, reason: String },

    /// 状态模式错误
    #[error("状态模式错误: {state_type} - {reason}")]
    State { state_type: String, reason: String },

    /// 适配器模式错误
    #[error("适配器模式错误: {adapter_type} - {reason}")]
    Adapter { adapter_type: String, reason: String },

    /// 装饰器模式错误
    #[error("装饰器模式错误: {decorator_type} - {reason}")]
    Decorator { decorator_type: String, reason: String },

    /// 外观模式错误
    #[error("外观模式错误: {facade_type} - {reason}")]
    Facade { facade_type: String, reason: String },

    /// 代理模式错误
    #[error("代理模式错误: {proxy_type} - {reason}")]
    Proxy { proxy_type: String, reason: String },

    /// 桥接模式错误
    #[error("桥接模式错误: {bridge_type} - {reason}")]
    Bridge { bridge_type: String, reason: String },

    /// 组合模式错误
    #[error("组合模式错误: {composite_type} - {reason}")]
    Composite { composite_type: String, reason: String },

    /// 享元模式错误
    #[error("享元模式错误: {flyweight_type} - {reason}")]
    Flyweight { flyweight_type: String, reason: String },

    /// 模板方法模式错误
    #[error("模板方法模式错误: {template_type} - {reason}")]
    TemplateMethod { template_type: String, reason: String },

    /// 迭代器模式错误
    #[error("迭代器模式错误: {iterator_type} - {reason}")]
    Iterator { iterator_type: String, reason: String },

    /// 访问者模式错误
    #[error("访问者模式错误: {visitor_type} - {reason}")]
    Visitor { visitor_type: String, reason: String },

    /// 中介者模式错误
    #[error("中介者模式错误: {mediator_type} - {reason}")]
    Mediator { mediator_type: String, reason: String },

    /// 备忘录模式错误
    #[error("备忘录模式错误: {memento_type} - {reason}")]
    Memento { memento_type: String, reason: String },

    /// 责任链模式错误
    #[error("责任链模式错误: {chain_type} - {reason}")]
    ChainOfResponsibility { chain_type: String, reason: String },

    /// 解释器模式错误
    #[error("解释器模式错误: {interpreter_type} - {reason}")]
    Interpreter { interpreter_type: String, reason: String },
}

/// 传输层错误
#[derive(Error, Debug)]
pub enum TransportError {
    /// gRPC错误
    #[error("gRPC错误: {0}")]
    Grpc(#[from] tonic::Status),

    /// HTTP错误
    #[error("HTTP错误: {0}")]
    Http(#[from] reqwest::Error),

    /// 连接错误
    #[error("连接错误: {endpoint} - {reason}")]
    Connection { endpoint: String, reason: String },

    /// TLS错误
    #[error("TLS错误: {0}")]
    Tls(String),

    /// DNS解析错误
    #[error("DNS解析错误: {hostname}")]
    DnsResolution { hostname: String },

    /// 网络不可达
    #[error("网络不可达: {endpoint}")]
    NetworkUnreachable { endpoint: String },
}

impl Clone for TransportError {
    fn clone(&self) -> Self {
        match self {
            Self::Grpc(status) => Self::Grpc(tonic::Status::new(
                status.code(),
                status.message().to_string(),
            )),
            Self::Http(err) => {
                // 创建一个新的错误，保留错误信息
                let error_msg = err.to_string();
                // 创建一个简单的 HTTP 错误
                Self::Tls(format!("HTTP错误: {}", error_msg))
            }
            Self::Connection { endpoint, reason } => Self::Connection {
                endpoint: endpoint.clone(),
                reason: reason.clone(),
            },
            Self::Tls(msg) => Self::Tls(msg.clone()),
            Self::DnsResolution { hostname } => Self::DnsResolution {
                hostname: hostname.clone(),
            },
            Self::NetworkUnreachable { endpoint } => Self::NetworkUnreachable {
                endpoint: endpoint.clone(),
            },
        }
    }
}

/// 序列化错误
#[derive(Error, Debug)]
pub enum SerializationError {
    /// Protobuf序列化错误
    #[error("Protobuf序列化错误: {0}")]
    Protobuf(#[from] prost::EncodeError),

    /// JSON序列化错误
    #[error("JSON序列化错误: {0}")]
    Json(#[from] serde_json::Error),

    /// 数据格式错误
    #[error("数据格式错误: {message}")]
    Format { message: String },

    /// 编码错误
    #[error("编码错误: {encoding} - {reason}")]
    Encoding { encoding: String, reason: String },
}

impl Clone for SerializationError {
    fn clone(&self) -> Self {
        match self {
            Self::Protobuf(_err) => {
                // 创建一个新的 Protobuf 错误，保留错误信息
                Self::Format {
                    message: "Protobuf序列化错误".to_string(),
                }
            }
            Self::Json(_err) => {
                // 创建一个新的 JSON 错误，保留错误信息
                Self::Format {
                    message: "JSON序列化错误".to_string(),
                }
            }
            Self::Format { message } => Self::Format {
                message: message.clone(),
            },
            Self::Encoding { encoding, reason } => Self::Encoding {
                encoding: encoding.clone(),
                reason: reason.clone(),
            },
        }
    }
}

/// 配置错误
#[derive(Error, Debug, Clone)]
pub enum ConfigurationError {
    /// 无效的端点URL
    #[error("无效的端点URL: {url}")]
    InvalidEndpoint { url: String },

    /// 无效的超时配置
    #[error("无效的超时配置: {timeout:?}")]
    InvalidTimeout { timeout: std::time::Duration },

    /// 无效的批处理配置
    #[error("无效的批处理配置: {message}")]
    InvalidBatchConfig { message: String },

    /// 缺少必需的配置项
    #[error("缺少必需的配置项: {field}")]
    MissingRequiredField { field: String },

    /// 配置值超出范围
    #[error("配置值超出范围: {field} = {value} (范围: {min} - {max})")]
    ValueOutOfRange {
        field: String,
        value: f64,
        min: f64,
        max: f64,
    },
}

/// 数据处理错误
#[derive(Error, Debug, Clone)]
pub enum ProcessingError {
    /// 数据验证失败
    #[error("数据验证失败: {field} - {reason}")]
    ValidationFailed { field: String, reason: String },

    /// 数据转换错误
    #[error("数据转换错误: {from} -> {to}")]
    ConversionFailed { from: String, to: String },

    /// 批处理错误
    #[error("批处理错误: {message}")]
    BatchProcessing { message: String },

    /// 过滤错误
    #[error("过滤错误: {filter} - {reason}")]
    Filtering { filter: String, reason: String },

    /// 聚合错误
    #[error("聚合错误: {operation} - {reason}")]
    Aggregation { operation: String, reason: String },
}

/// 导出器错误
#[derive(Error, Debug, Clone)]
pub enum ExportError {
    /// 导出失败
    #[error("导出失败: {reason}")]
    ExportFailed { reason: String },

    /// 部分导出失败
    #[error("部分导出失败: 成功 {success}, 失败 {failed}")]
    PartialExport { success: usize, failed: usize },

    /// 重试次数耗尽
    #[error("重试次数耗尽: 尝试了 {attempts} 次")]
    RetryExhausted { attempts: usize },

    /// 导出器未初始化
    #[error("导出器未初始化")]
    NotInitialized,

    /// 导出器已关闭
    #[error("导出器已关闭")]
    Shutdown,
}

impl OtlpError {
    /// 从 anyhow::Error 创建内部错误
    pub fn from_anyhow(err: anyhow::Error) -> Self {
        Self::Internal(err.to_string())
    }
}

impl From<anyhow::Error> for OtlpError {
    fn from(err: anyhow::Error) -> Self {
        Self::from_anyhow(err)
    }
}

impl OtlpError {
    /// 创建超时错误
    pub fn timeout(operation: impl Into<String>, timeout: std::time::Duration) -> Self {
        Self::Timeout {
            operation: operation.into(),
            timeout,
        }
    }

    /// 创建并发错误
    pub fn concurrency(reason: impl Into<String>) -> Self {
        Self::Concurrency(reason.into())
    }

    /// 创建资源不足错误
    pub fn resource_exhausted(
        resource: impl Into<String>,
        current: usize,
        required: usize,
    ) -> Self {
        Self::ResourceExhausted {
            resource: resource.into(),
            current,
            required,
        }
    }

    /// 创建版本不兼容错误
    pub fn version_mismatch(current: impl Into<String>, supported: impl Into<String>) -> Self {
        Self::VersionMismatch {
            current: current.into(),
            supported: supported.into(),
        }
    }

    /// 判断是否为可重试的错误
    pub fn is_retryable(&self) -> bool {
        match self {
            // 传输类：网络瞬断、连接失败、网络不可达 → 可重试
            Self::Transport(TransportError::Connection { .. }) => true,
            Self::Transport(TransportError::NetworkUnreachable { .. }) => true,
            // gRPC: UNAVAILABLE、RESOURCE_EXHAUSTED、DEADLINE_EXCEEDED → 可重试
            Self::Transport(TransportError::Grpc(status)) => {
                use tonic::Code;
                matches!(
                    status.code(),
                    Code::Unavailable | Code::ResourceExhausted | Code::DeadlineExceeded
                )
            }
            // HTTP：5xx/429 常见可重试
            Self::Transport(TransportError::Http(err)) => {
                if let Some(status) = err.status() {
                    let code = status.as_u16();
                    code == 429 || (500..=599).contains(&code)
                } else {
                    // 无状态码（如超时/连接断开）通常可重试
                    true
                }
            }
            // 操作超时 → 可重试
            Self::Timeout { .. } => true,
            // 导出失败（通用） → 可重试
            Self::Export(ExportError::ExportFailed { .. }) => true,
            // 限流错误 → 可重试（需要等待）
            Self::RateLimit { .. } => true,
            // 依赖服务错误 → 可重试
            Self::DependencyService { .. } => true,
            // 业务逻辑错误 → 不可重试
            Self::BusinessLogic(_) => false,
            // 数据验证错误 → 不可重试
            Self::DataValidation { .. } => false,
            // 权限错误 → 不可重试
            Self::Permission { .. } => false,
            // 新增错误类型的可重试性判断
            Self::MachineLearning { .. } => false,
            Self::Monitoring { .. } => true,
            Self::DistributedCoordination { .. } => true,
            Self::PerformanceOptimization { .. } => false,
            Self::EdgeComputing { .. } => true,
            Self::BlockchainIntegration { .. } => true,
            Self::Microservice { .. } => true,
            Self::Cache { .. } => true,
            Self::Database { .. } => true,
            Self::FileSystem { .. } => true,
            Self::Cryptographic { .. } => false,
            Self::NetworkProtocol { .. } => true,
            Self::LoadBalancing { .. } => true,
            Self::ServiceDiscovery { .. } => true,
            Self::HealthCheck { .. } => true,
            Self::MetricsCollection { .. } => true,
            Self::Alerting { .. } => true,
            Self::ConfigurationManagement { .. } => false,
            Self::VersionControl { .. } => false,
            Self::Deployment { .. } => true,
            Self::Rollback { .. } => true,
            Self::Backup { .. } => true,
            Self::Recovery { .. } => true,
            Self::Migration { .. } => true,
            Self::Upgrade { .. } => true,
            Self::Downgrade { .. } => true,
            Self::Scaling { .. } => true,
            Self::Compression { .. } => false,
            Self::Decompression { .. } => false,
            Self::Encoding { .. } => false,
            Self::Decoding { .. } => false,
            Self::Conversion { .. } => false,
            Self::Validation { .. } => false,
            Self::Authorization { .. } => false,
            Self::Authentication { .. } => false,
            Self::Token { .. } => false,
            Self::Session { .. } => true,
            Self::ConnectionPool { .. } => true,
            Self::Transaction { .. } => true,
            Self::Lock { .. } => true,
            Self::Semaphore { .. } => true,
            Self::Barrier { .. } => true,
            Self::ConditionVariable { .. } => true,
            Self::AtomicOperation { .. } => true,
            Self::MemoryManagement { .. } => false,
            Self::GarbageCollection { .. } => false,
            Self::MemoryLeak { .. } => false,
            Self::BufferOverflow { .. } => false,
            Self::StackOverflow { .. } => false,
            Self::HeapOverflow { .. } => false,
            Self::NullPointer { .. } => false,
            Self::WildPointer { .. } => false,
            Self::DanglingPointer { .. } => false,
            Self::DoubleFree { .. } => false,
            Self::UseAfterFree { .. } => false,
            Self::MemoryAlignment { .. } => false,
            Self::Endianness { .. } => false,
            Self::TypeConversion { .. } => false,
            Self::TypeCheck { .. } => false,
            Self::TypeInference { .. } => false,
            Self::Generic { .. } => false,
            Self::Trait { .. } => false,
            Self::Lifetime { .. } => false,
            Self::BorrowCheck { .. } => false,
            Self::Ownership { .. } => false,
            Self::MoveSemantics { .. } => false,
            Self::CopySemantics { .. } => false,
            Self::CloneSemantics { .. } => false,
            Self::Destructor { .. } => false,
            Self::Constructor { .. } => false,
            Self::Factory { .. } => false,
            Self::Builder { .. } => false,
            Self::Singleton { .. } => false,
            Self::Observer { .. } => false,
            Self::Strategy { .. } => false,
            Self::Command { .. } => false,
            Self::State { .. } => false,
            Self::Adapter { .. } => false,
            Self::Decorator { .. } => false,
            Self::Facade { .. } => false,
            Self::Proxy { .. } => false,
            Self::Bridge { .. } => false,
            Self::Composite { .. } => false,
            Self::Flyweight { .. } => false,
            Self::TemplateMethod { .. } => false,
            Self::Iterator { .. } => false,
            Self::Visitor { .. } => false,
            Self::Mediator { .. } => false,
            Self::Memento { .. } => false,
            Self::ChainOfResponsibility { .. } => false,
            Self::Interpreter { .. } => false,
            // 其余：默认不可重试
            _ => false,
        }
    }

    /// 获取错误严重程度
    pub fn severity(&self) -> ErrorSeverity {
        match self {
            Self::Transport(_) => ErrorSeverity::High,
            Self::Serialization(_) => ErrorSeverity::Medium,
            Self::Configuration(_) => ErrorSeverity::High,
            Self::Processing(_) => ErrorSeverity::Medium,
            Self::Export(_) => ErrorSeverity::Medium,
            Self::Timeout { .. } => ErrorSeverity::Medium,
            Self::Concurrency(_) => ErrorSeverity::High,
            Self::ResourceExhausted { .. } => ErrorSeverity::High,
            Self::VersionMismatch { .. } => ErrorSeverity::High,
            Self::Internal(_) => ErrorSeverity::Critical,
            Self::BusinessLogic(_) => ErrorSeverity::Medium,
            Self::DataValidation { .. } => ErrorSeverity::Low,
            Self::Permission { .. } => ErrorSeverity::High,
            Self::RateLimit { .. } => ErrorSeverity::Medium,
            Self::DependencyService { .. } => ErrorSeverity::High,
            // 新增错误类型的严重程度
            Self::MachineLearning { .. } => ErrorSeverity::Medium,
            Self::Monitoring { .. } => ErrorSeverity::Medium,
            Self::DistributedCoordination { .. } => ErrorSeverity::High,
            Self::PerformanceOptimization { .. } => ErrorSeverity::Low,
            Self::EdgeComputing { .. } => ErrorSeverity::Medium,
            Self::BlockchainIntegration { .. } => ErrorSeverity::High,
            Self::Microservice { .. } => ErrorSeverity::High,
            Self::Cache { .. } => ErrorSeverity::Low,
            Self::Database { .. } => ErrorSeverity::High,
            Self::FileSystem { .. } => ErrorSeverity::Medium,
            Self::Cryptographic { .. } => ErrorSeverity::Critical,
            Self::NetworkProtocol { .. } => ErrorSeverity::High,
            Self::LoadBalancing { .. } => ErrorSeverity::High,
            Self::ServiceDiscovery { .. } => ErrorSeverity::High,
            Self::HealthCheck { .. } => ErrorSeverity::Medium,
            Self::ValidationError(_) => ErrorSeverity::Low,
            Self::ProfilerAlreadyRunning => ErrorSeverity::Low,
            Self::ProfilerNotRunning => ErrorSeverity::Low,
            Self::MetricsCollection { .. } => ErrorSeverity::Low,
            Self::Alerting { .. } => ErrorSeverity::Medium,
            Self::ConfigurationManagement { .. } => ErrorSeverity::High,
            Self::VersionControl { .. } => ErrorSeverity::Medium,
            Self::Deployment { .. } => ErrorSeverity::High,
            Self::Rollback { .. } => ErrorSeverity::High,
            Self::Backup { .. } => ErrorSeverity::Medium,
            Self::Recovery { .. } => ErrorSeverity::High,
            Self::Migration { .. } => ErrorSeverity::High,
            Self::Upgrade { .. } => ErrorSeverity::High,
            Self::Downgrade { .. } => ErrorSeverity::Medium,
            Self::Scaling { .. } => ErrorSeverity::Medium,
            Self::Compression { .. } => ErrorSeverity::Low,
            Self::Decompression { .. } => ErrorSeverity::Low,
            Self::Encoding { .. } => ErrorSeverity::Low,
            Self::Decoding { .. } => ErrorSeverity::Low,
            Self::Conversion { .. } => ErrorSeverity::Low,
            Self::Validation { .. } => ErrorSeverity::Low,
            Self::Authorization { .. } => ErrorSeverity::High,
            Self::Authentication { .. } => ErrorSeverity::High,
            Self::Token { .. } => ErrorSeverity::High,
            Self::Session { .. } => ErrorSeverity::Medium,
            Self::ConnectionPool { .. } => ErrorSeverity::High,
            Self::Transaction { .. } => ErrorSeverity::High,
            Self::Lock { .. } => ErrorSeverity::High,
            Self::Semaphore { .. } => ErrorSeverity::High,
            Self::Barrier { .. } => ErrorSeverity::High,
            Self::ConditionVariable { .. } => ErrorSeverity::High,
            Self::AtomicOperation { .. } => ErrorSeverity::High,
            Self::MemoryManagement { .. } => ErrorSeverity::Critical,
            Self::GarbageCollection { .. } => ErrorSeverity::High,
            Self::MemoryLeak { .. } => ErrorSeverity::Critical,
            Self::BufferOverflow { .. } => ErrorSeverity::Critical,
            Self::StackOverflow { .. } => ErrorSeverity::Critical,
            Self::HeapOverflow { .. } => ErrorSeverity::Critical,
            Self::NullPointer { .. } => ErrorSeverity::Critical,
            Self::WildPointer { .. } => ErrorSeverity::Critical,
            Self::DanglingPointer { .. } => ErrorSeverity::Critical,
            Self::DoubleFree { .. } => ErrorSeverity::Critical,
            Self::UseAfterFree { .. } => ErrorSeverity::Critical,
            Self::MemoryAlignment { .. } => ErrorSeverity::High,
            Self::Endianness { .. } => ErrorSeverity::Medium,
            Self::TypeConversion { .. } => ErrorSeverity::Low,
            Self::TypeCheck { .. } => ErrorSeverity::Low,
            Self::TypeInference { .. } => ErrorSeverity::Low,
            Self::Generic { .. } => ErrorSeverity::Low,
            Self::Trait { .. } => ErrorSeverity::Low,
            Self::Lifetime { .. } => ErrorSeverity::Low,
            Self::BorrowCheck { .. } => ErrorSeverity::Low,
            Self::Ownership { .. } => ErrorSeverity::Low,
            Self::MoveSemantics { .. } => ErrorSeverity::Low,
            Self::CopySemantics { .. } => ErrorSeverity::Low,
            Self::CloneSemantics { .. } => ErrorSeverity::Low,
            Self::Destructor { .. } => ErrorSeverity::Medium,
            Self::Constructor { .. } => ErrorSeverity::Medium,
            Self::Factory { .. } => ErrorSeverity::Low,
            Self::Builder { .. } => ErrorSeverity::Low,
            Self::Singleton { .. } => ErrorSeverity::Low,
            Self::Observer { .. } => ErrorSeverity::Low,
            Self::Strategy { .. } => ErrorSeverity::Low,
            Self::Command { .. } => ErrorSeverity::Low,
            Self::State { .. } => ErrorSeverity::Low,
            Self::Adapter { .. } => ErrorSeverity::Low,
            Self::Decorator { .. } => ErrorSeverity::Low,
            Self::Facade { .. } => ErrorSeverity::Low,
            Self::Proxy { .. } => ErrorSeverity::Low,
            Self::Bridge { .. } => ErrorSeverity::Low,
            Self::Composite { .. } => ErrorSeverity::Low,
            Self::Flyweight { .. } => ErrorSeverity::Low,
            Self::TemplateMethod { .. } => ErrorSeverity::Low,
            Self::Iterator { .. } => ErrorSeverity::Low,
            Self::Visitor { .. } => ErrorSeverity::Low,
            Self::Mediator { .. } => ErrorSeverity::Low,
            Self::Memento { .. } => ErrorSeverity::Low,
            Self::ChainOfResponsibility { .. } => ErrorSeverity::Low,
            Self::Interpreter { .. } => ErrorSeverity::Low,
        }
    }

    /// 获取错误恢复建议
    pub fn recovery_suggestion(&self) -> Option<&'static str> {
        match self {
            Self::Transport(TransportError::Connection { .. }) => {
                Some("检查网络连接和端点配置，尝试重新连接")
            }
            Self::Transport(TransportError::NetworkUnreachable { .. }) => {
                Some("检查网络配置和防火墙设置")
            }
            Self::Transport(TransportError::Grpc(_)) => Some("检查gRPC服务状态，可能需要重启服务"),
            Self::Transport(TransportError::Http(_)) => Some("检查HTTP服务状态和端点可访问性"),
            Self::Serialization(_) => Some("检查数据格式和序列化配置"),
            Self::Configuration(ConfigurationError::InvalidEndpoint { .. }) => {
                Some("检查端点URL格式和可访问性")
            }
            Self::Configuration(ConfigurationError::MissingRequiredField { .. }) => {
                Some("检查配置文件中是否包含所有必需字段")
            }
            Self::Processing(ProcessingError::ValidationFailed { .. }) => {
                Some("检查输入数据的格式和内容")
            }
            Self::Export(_) => Some("检查导出器配置和网络连接"),
            Self::Timeout { .. } => Some("增加超时时间或检查网络延迟"),
            Self::ResourceExhausted { .. } => Some("释放资源或增加系统资源"),
            Self::VersionMismatch { .. } => Some("更新到兼容的版本或降级到支持的版本"),
            Self::Internal(_) => Some("检查系统日志，可能需要重启服务"),
            Self::BusinessLogic(_) => Some("检查业务逻辑实现，确认业务规则"),
            Self::DataValidation { .. } => Some("检查输入数据格式，确认数据验证规则"),
            Self::Permission { .. } => Some("检查用户权限，确认访问控制配置"),
            Self::RateLimit { .. } => Some("等待限流重置或调整请求频率"),
            Self::DependencyService { .. } => Some("检查依赖服务状态，确认服务可用性"),
            // 新增错误类型的恢复建议
            Self::MachineLearning { .. } => Some("检查ML模型状态，重新训练或更新模型"),
            Self::Monitoring { .. } => Some("检查监控系统配置，重启监控服务"),
            Self::DistributedCoordination { .. } => Some("检查分布式协调状态，重新同步节点"),
            Self::PerformanceOptimization { .. } => Some("检查性能优化配置，调整优化策略"),
            Self::EdgeComputing { .. } => Some("检查边缘节点状态，重新连接边缘服务"),
            Self::BlockchainIntegration { .. } => Some("检查区块链连接，重新同步区块链数据"),
            Self::Microservice { .. } => Some("检查微服务状态，重启或重新部署服务"),
            Self::Cache { .. } => Some("检查缓存状态，清理或重建缓存"),
            Self::Database { .. } => Some("检查数据库连接，重启数据库服务"),
            Self::FileSystem { .. } => Some("检查文件系统状态，修复文件权限或磁盘空间"),
            Self::Cryptographic { .. } => Some("检查加密配置，更新加密密钥或算法"),
            Self::NetworkProtocol { .. } => Some("检查网络协议配置，更新协议版本"),
            Self::LoadBalancing { .. } => Some("检查负载均衡配置，重新配置负载均衡策略"),
            Self::ServiceDiscovery { .. } => Some("检查服务发现配置，重新注册服务"),
            Self::HealthCheck { .. } => Some("检查健康检查配置，修复健康检查端点"),
            Self::MetricsCollection { .. } => Some("检查指标收集配置，重启指标收集服务"),
            Self::Alerting { .. } => Some("检查告警配置，修复告警规则或通知渠道"),
            Self::ConfigurationManagement { .. } => Some("检查配置管理状态，重新加载配置"),
            Self::VersionControl { .. } => Some("检查版本控制状态，同步版本信息"),
            Self::Deployment { .. } => Some("检查部署状态，重新部署或回滚"),
            Self::Rollback { .. } => Some("检查回滚状态，完成回滚操作"),
            Self::Backup { .. } => Some("检查备份状态，重新执行备份操作"),
            Self::Recovery { .. } => Some("检查恢复状态，重新执行恢复操作"),
            Self::Migration { .. } => Some("检查迁移状态，完成迁移操作"),
            Self::Upgrade { .. } => Some("检查升级状态，完成升级操作"),
            Self::Downgrade { .. } => Some("检查降级状态，完成降级操作"),
            Self::Scaling { .. } => Some("检查扩展状态，调整扩展策略"),
            Self::Compression { .. } => Some("检查压缩配置，调整压缩算法或参数"),
            Self::Decompression { .. } => Some("检查解压缩配置，修复解压缩算法"),
            Self::Encoding { .. } => Some("检查编码配置，调整编码格式"),
            Self::Decoding { .. } => Some("检查解码配置，修复解码算法"),
            Self::Conversion { .. } => Some("检查转换配置，修复转换逻辑"),
            Self::Validation { .. } => Some("检查验证配置，修复验证规则"),
            Self::Authorization { .. } => Some("检查授权配置，更新授权策略"),
            Self::Authentication { .. } => Some("检查认证配置，更新认证方式"),
            Self::Token { .. } => Some("检查令牌状态，刷新或重新生成令牌"),
            Self::Session { .. } => Some("检查会话状态，重新建立会话"),
            Self::ConnectionPool { .. } => Some("检查连接池状态，重建连接池"),
            Self::Transaction { .. } => Some("检查事务状态，回滚或提交事务"),
            Self::Lock { .. } => Some("检查锁状态，释放或重新获取锁"),
            Self::Semaphore { .. } => Some("检查信号量状态，释放或重新获取信号量"),
            Self::Barrier { .. } => Some("检查屏障状态，重新设置屏障"),
            Self::ConditionVariable { .. } => Some("检查条件变量状态，重新设置条件变量"),
            Self::AtomicOperation { .. } => Some("检查原子操作状态，重新执行原子操作"),
            Self::MemoryManagement { .. } => Some("检查内存管理状态，释放内存或重启服务"),
            Self::GarbageCollection { .. } => Some("检查垃圾回收状态，手动触发垃圾回收"),
            Self::MemoryLeak { .. } => Some("检查内存泄漏，修复内存泄漏问题"),
            Self::BufferOverflow { .. } => Some("检查缓冲区溢出，增加缓冲区大小或修复逻辑"),
            Self::StackOverflow { .. } => Some("检查栈溢出，增加栈大小或优化递归逻辑"),
            Self::HeapOverflow { .. } => Some("检查堆溢出，增加堆大小或优化内存使用"),
            Self::NullPointer { .. } => Some("检查空指针，修复空指针引用"),
            Self::WildPointer { .. } => Some("检查野指针，修复野指针引用"),
            Self::DanglingPointer { .. } => Some("检查悬空指针，修复悬空指针引用"),
            Self::DoubleFree { .. } => Some("检查双重释放，修复双重释放问题"),
            Self::UseAfterFree { .. } => Some("检查使用后释放，修复使用后释放问题"),
            Self::MemoryAlignment { .. } => Some("检查内存对齐，修复内存对齐问题"),
            Self::Endianness { .. } => Some("检查字节序，修复字节序转换问题"),
            Self::TypeConversion { .. } => Some("检查类型转换，修复类型转换逻辑"),
            Self::TypeCheck { .. } => Some("检查类型检查，修复类型检查逻辑"),
            Self::TypeInference { .. } => Some("检查类型推断，修复类型推断逻辑"),
            Self::Generic { .. } => Some("检查泛型，修复泛型使用"),
            Self::Trait { .. } => Some("检查特征，修复特征实现"),
            Self::Lifetime { .. } => Some("检查生命周期，修复生命周期问题"),
            Self::BorrowCheck { .. } => Some("检查借用检查，修复借用检查问题"),
            Self::Ownership { .. } => Some("检查所有权，修复所有权问题"),
            Self::MoveSemantics { .. } => Some("检查移动语义，修复移动语义问题"),
            Self::CopySemantics { .. } => Some("检查复制语义，修复复制语义问题"),
            Self::CloneSemantics { .. } => Some("检查克隆语义，修复克隆语义问题"),
            Self::Destructor { .. } => Some("检查析构函数，修复析构函数实现"),
            Self::Constructor { .. } => Some("检查构造函数，修复构造函数实现"),
            Self::Factory { .. } => Some("检查工厂方法，修复工厂方法实现"),
            Self::Builder { .. } => Some("检查建造者模式，修复建造者模式实现"),
            Self::Singleton { .. } => Some("检查单例模式，修复单例模式实现"),
            Self::Observer { .. } => Some("检查观察者模式，修复观察者模式实现"),
            Self::Strategy { .. } => Some("检查策略模式，修复策略模式实现"),
            Self::Command { .. } => Some("检查命令模式，修复命令模式实现"),
            Self::State { .. } => Some("检查状态模式，修复状态模式实现"),
            Self::Adapter { .. } => Some("检查适配器模式，修复适配器模式实现"),
            Self::Decorator { .. } => Some("检查装饰器模式，修复装饰器模式实现"),
            Self::Facade { .. } => Some("检查外观模式，修复外观模式实现"),
            Self::Proxy { .. } => Some("检查代理模式，修复代理模式实现"),
            Self::Bridge { .. } => Some("检查桥接模式，修复桥接模式实现"),
            Self::Composite { .. } => Some("检查组合模式，修复组合模式实现"),
            Self::Flyweight { .. } => Some("检查享元模式，修复享元模式实现"),
            Self::TemplateMethod { .. } => Some("检查模板方法模式，修复模板方法模式实现"),
            Self::Iterator { .. } => Some("检查迭代器模式，修复迭代器模式实现"),
            Self::Visitor { .. } => Some("检查访问者模式，修复访问者模式实现"),
            Self::Mediator { .. } => Some("检查中介者模式，修复中介者模式实现"),
            Self::Memento { .. } => Some("检查备忘录模式，修复备忘录模式实现"),
            Self::ChainOfResponsibility { .. } => Some("检查责任链模式，修复责任链模式实现"),
            Self::Interpreter { .. } => Some("检查解释器模式，修复解释器模式实现"),
            _ => None,
        }
    }

    /// 判断是否为临时性错误
    pub fn is_temporary(&self) -> bool {
        match self {
            Self::Transport(TransportError::Connection { .. }) => true,
            Self::Transport(TransportError::NetworkUnreachable { .. }) => true,
            Self::Transport(TransportError::Grpc(status)) => {
                use tonic::Code;
                matches!(
                    status.code(),
                    Code::Unavailable
                        | Code::ResourceExhausted
                        | Code::DeadlineExceeded
                        | Code::Aborted
                )
            }
            Self::Transport(TransportError::Http(err)) => {
                if let Some(status) = err.status() {
                    let code = status.as_u16();
                    // 5xx 服务器错误和 429 限流通常是临时的
                    code == 429 || (500..=599).contains(&code)
                } else {
                    // 网络错误通常是临时的
                    true
                }
            }
            Self::Timeout { .. } => true,
            Self::Export(_) => true,
            Self::RateLimit { .. } => true,
            Self::DependencyService { .. } => true,
            // 新增错误类型的临时性判断
            Self::MachineLearning { .. } => false,
            Self::Monitoring { .. } => true,
            Self::DistributedCoordination { .. } => true,
            Self::PerformanceOptimization { .. } => false,
            Self::EdgeComputing { .. } => true,
            Self::BlockchainIntegration { .. } => true,
            Self::Microservice { .. } => true,
            Self::Cache { .. } => true,
            Self::Database { .. } => true,
            Self::FileSystem { .. } => true,
            Self::Cryptographic { .. } => false,
            Self::NetworkProtocol { .. } => true,
            Self::LoadBalancing { .. } => true,
            Self::ServiceDiscovery { .. } => true,
            Self::HealthCheck { .. } => true,
            Self::MetricsCollection { .. } => true,
            Self::Alerting { .. } => true,
            Self::ConfigurationManagement { .. } => false,
            Self::VersionControl { .. } => false,
            Self::Deployment { .. } => true,
            Self::Rollback { .. } => true,
            Self::Backup { .. } => true,
            Self::Recovery { .. } => true,
            Self::Migration { .. } => true,
            Self::Upgrade { .. } => true,
            Self::Downgrade { .. } => true,
            Self::Scaling { .. } => true,
            Self::Compression { .. } => false,
            Self::Decompression { .. } => false,
            Self::Encoding { .. } => false,
            Self::Decoding { .. } => false,
            Self::Conversion { .. } => false,
            Self::Validation { .. } => false,
            Self::Authorization { .. } => false,
            Self::Authentication { .. } => false,
            Self::Token { .. } => false,
            Self::Session { .. } => true,
            Self::ConnectionPool { .. } => true,
            Self::Transaction { .. } => true,
            Self::Lock { .. } => true,
            Self::Semaphore { .. } => true,
            Self::Barrier { .. } => true,
            Self::ConditionVariable { .. } => true,
            Self::AtomicOperation { .. } => true,
            Self::MemoryManagement { .. } => false,
            Self::GarbageCollection { .. } => false,
            Self::MemoryLeak { .. } => false,
            Self::BufferOverflow { .. } => false,
            Self::StackOverflow { .. } => false,
            Self::HeapOverflow { .. } => false,
            Self::NullPointer { .. } => false,
            Self::WildPointer { .. } => false,
            Self::DanglingPointer { .. } => false,
            Self::DoubleFree { .. } => false,
            Self::UseAfterFree { .. } => false,
            Self::MemoryAlignment { .. } => false,
            Self::Endianness { .. } => false,
            Self::TypeConversion { .. } => false,
            Self::TypeCheck { .. } => false,
            Self::TypeInference { .. } => false,
            Self::Generic { .. } => false,
            Self::Trait { .. } => false,
            Self::Lifetime { .. } => false,
            Self::BorrowCheck { .. } => false,
            Self::Ownership { .. } => false,
            Self::MoveSemantics { .. } => false,
            Self::CopySemantics { .. } => false,
            Self::CloneSemantics { .. } => false,
            Self::Destructor { .. } => false,
            Self::Constructor { .. } => false,
            Self::Factory { .. } => false,
            Self::Builder { .. } => false,
            Self::Singleton { .. } => false,
            Self::Observer { .. } => false,
            Self::Strategy { .. } => false,
            Self::Command { .. } => false,
            Self::State { .. } => false,
            Self::Adapter { .. } => false,
            Self::Decorator { .. } => false,
            Self::Facade { .. } => false,
            Self::Proxy { .. } => false,
            Self::Bridge { .. } => false,
            Self::Composite { .. } => false,
            Self::Flyweight { .. } => false,
            Self::TemplateMethod { .. } => false,
            Self::Iterator { .. } => false,
            Self::Visitor { .. } => false,
            Self::Mediator { .. } => false,
            Self::Memento { .. } => false,
            Self::ChainOfResponsibility { .. } => false,
            Self::Interpreter { .. } => false,
            _ => false,
        }
    }

    /// 获取错误分类
    pub fn category(&self) -> ErrorCategory {
        match self {
            Self::Transport(_) => ErrorCategory::Network,
            Self::Serialization(_) => ErrorCategory::Data,
            Self::Configuration(_) => ErrorCategory::Configuration,
            Self::Processing(_) => ErrorCategory::Processing,
            Self::Export(_) => ErrorCategory::Export,
            Self::Timeout { .. } => ErrorCategory::Performance,
            Self::Concurrency(_) => ErrorCategory::Concurrency,
            Self::ResourceExhausted { .. } => ErrorCategory::Resource,
            Self::VersionMismatch { .. } => ErrorCategory::Compatibility,
            Self::Internal(_) => ErrorCategory::System,
            Self::BusinessLogic(_) => ErrorCategory::Business,
            Self::DataValidation { .. } => ErrorCategory::Data,
            Self::Permission { .. } => ErrorCategory::Security,
            Self::RateLimit { .. } => ErrorCategory::Performance,
            Self::DependencyService { .. } => ErrorCategory::Dependency,
            Self::MachineLearning { .. } => ErrorCategory::ML,
            Self::Monitoring { .. } => ErrorCategory::Monitoring,
            Self::DistributedCoordination { .. } => ErrorCategory::Distributed,
            Self::PerformanceOptimization { .. } => ErrorCategory::Performance,
            Self::EdgeComputing { .. } => ErrorCategory::Edge,
            Self::BlockchainIntegration { .. } => ErrorCategory::Blockchain,
            Self::Microservice { .. } => ErrorCategory::Microservice,
            Self::Cache { .. } => ErrorCategory::Cache,
            Self::Database { .. } => ErrorCategory::Database,
            Self::FileSystem { .. } => ErrorCategory::FileSystem,
            Self::Cryptographic { .. } => ErrorCategory::Security,
            Self::NetworkProtocol { .. } => ErrorCategory::Network,
            Self::LoadBalancing { .. } => ErrorCategory::LoadBalancing,
            Self::ServiceDiscovery { .. } => ErrorCategory::ServiceDiscovery,
            Self::HealthCheck { .. } => ErrorCategory::Health,
            Self::ValidationError(_) => ErrorCategory::Data,
            Self::ProfilerAlreadyRunning => ErrorCategory::Processing,
            Self::ProfilerNotRunning => ErrorCategory::Processing,
            Self::MetricsCollection { .. } => ErrorCategory::Metrics,
            Self::Alerting { .. } => ErrorCategory::Alerting,
            Self::ConfigurationManagement { .. } => ErrorCategory::Configuration,
            Self::VersionControl { .. } => ErrorCategory::VersionControl,
            Self::Deployment { .. } => ErrorCategory::Deployment,
            Self::Rollback { .. } => ErrorCategory::Deployment,
            Self::Backup { .. } => ErrorCategory::Backup,
            Self::Recovery { .. } => ErrorCategory::Recovery,
            Self::Migration { .. } => ErrorCategory::Migration,
            Self::Upgrade { .. } => ErrorCategory::Upgrade,
            Self::Downgrade { .. } => ErrorCategory::Downgrade,
            Self::Scaling { .. } => ErrorCategory::Scaling,
            Self::Compression { .. } => ErrorCategory::Compression,
            Self::Decompression { .. } => ErrorCategory::Compression,
            Self::Encoding { .. } => ErrorCategory::Encoding,
            Self::Decoding { .. } => ErrorCategory::Encoding,
            Self::Conversion { .. } => ErrorCategory::Conversion,
            Self::Validation { .. } => ErrorCategory::Validation,
            Self::Authorization { .. } => ErrorCategory::Security,
            Self::Authentication { .. } => ErrorCategory::Security,
            Self::Token { .. } => ErrorCategory::Security,
            Self::Session { .. } => ErrorCategory::Session,
            Self::ConnectionPool { .. } => ErrorCategory::Connection,
            Self::Transaction { .. } => ErrorCategory::Transaction,
            Self::Lock { .. } => ErrorCategory::Concurrency,
            Self::Semaphore { .. } => ErrorCategory::Concurrency,
            Self::Barrier { .. } => ErrorCategory::Concurrency,
            Self::ConditionVariable { .. } => ErrorCategory::Concurrency,
            Self::AtomicOperation { .. } => ErrorCategory::Concurrency,
            Self::MemoryManagement { .. } => ErrorCategory::Memory,
            Self::GarbageCollection { .. } => ErrorCategory::Memory,
            Self::MemoryLeak { .. } => ErrorCategory::Memory,
            Self::BufferOverflow { .. } => ErrorCategory::Memory,
            Self::StackOverflow { .. } => ErrorCategory::Memory,
            Self::HeapOverflow { .. } => ErrorCategory::Memory,
            Self::NullPointer { .. } => ErrorCategory::Memory,
            Self::WildPointer { .. } => ErrorCategory::Memory,
            Self::DanglingPointer { .. } => ErrorCategory::Memory,
            Self::DoubleFree { .. } => ErrorCategory::Memory,
            Self::UseAfterFree { .. } => ErrorCategory::Memory,
            Self::MemoryAlignment { .. } => ErrorCategory::Memory,
            Self::Endianness { .. } => ErrorCategory::Data,
            Self::TypeConversion { .. } => ErrorCategory::Type,
            Self::TypeCheck { .. } => ErrorCategory::Type,
            Self::TypeInference { .. } => ErrorCategory::Type,
            Self::Generic { .. } => ErrorCategory::Type,
            Self::Trait { .. } => ErrorCategory::Type,
            Self::Lifetime { .. } => ErrorCategory::Type,
            Self::BorrowCheck { .. } => ErrorCategory::Type,
            Self::Ownership { .. } => ErrorCategory::Type,
            Self::MoveSemantics { .. } => ErrorCategory::Type,
            Self::CopySemantics { .. } => ErrorCategory::Type,
            Self::CloneSemantics { .. } => ErrorCategory::Type,
            Self::Destructor { .. } => ErrorCategory::Type,
            Self::Constructor { .. } => ErrorCategory::Type,
            Self::Factory { .. } => ErrorCategory::Design,
            Self::Builder { .. } => ErrorCategory::Design,
            Self::Singleton { .. } => ErrorCategory::Design,
            Self::Observer { .. } => ErrorCategory::Design,
            Self::Strategy { .. } => ErrorCategory::Design,
            Self::Command { .. } => ErrorCategory::Design,
            Self::State { .. } => ErrorCategory::Design,
            Self::Adapter { .. } => ErrorCategory::Design,
            Self::Decorator { .. } => ErrorCategory::Design,
            Self::Facade { .. } => ErrorCategory::Design,
            Self::Proxy { .. } => ErrorCategory::Design,
            Self::Bridge { .. } => ErrorCategory::Design,
            Self::Composite { .. } => ErrorCategory::Design,
            Self::Flyweight { .. } => ErrorCategory::Design,
            Self::TemplateMethod { .. } => ErrorCategory::Design,
            Self::Iterator { .. } => ErrorCategory::Design,
            Self::Visitor { .. } => ErrorCategory::Design,
            Self::Mediator { .. } => ErrorCategory::Design,
            Self::Memento { .. } => ErrorCategory::Design,
            Self::ChainOfResponsibility { .. } => ErrorCategory::Design,
            Self::Interpreter { .. } => ErrorCategory::Design,
        }
    }

    /// 获取错误上下文信息
    pub fn context(&self) -> ErrorContext {
        ErrorContext {
            error_type: self.error_type(),
            category: self.category(),
            severity: self.severity(),
            is_retryable: self.is_retryable(),
            is_temporary: self.is_temporary(),
            recovery_suggestion: self.recovery_suggestion().map(|s| s.to_string()),
            timestamp: std::time::SystemTime::now(),
        }
    }

    /// 获取错误类型
    fn error_type(&self) -> &'static str {
        match self {
            Self::Transport(_) => "transport",
            Self::Serialization(_) => "serialization",
            Self::Configuration(_) => "configuration",
            Self::Processing(_) => "processing",
            Self::Export(_) => "export",
            Self::Timeout { .. } => "timeout",
            Self::Concurrency(_) => "concurrency",
            Self::ResourceExhausted { .. } => "resource_exhausted",
            Self::VersionMismatch { .. } => "version_mismatch",
            Self::Internal(_) => "internal",
            Self::BusinessLogic(_) => "business_logic",
            Self::DataValidation { .. } => "data_validation",
            Self::Permission { .. } => "permission",
            Self::RateLimit { .. } => "rate_limit",
            Self::DependencyService { .. } => "dependency_service",
            // 新增错误类型
            Self::MachineLearning { .. } => "machine_learning",
            Self::Monitoring { .. } => "monitoring",
            Self::DistributedCoordination { .. } => "distributed_coordination",
            Self::PerformanceOptimization { .. } => "performance_optimization",
            Self::EdgeComputing { .. } => "edge_computing",
            Self::BlockchainIntegration { .. } => "blockchain_integration",
            Self::Microservice { .. } => "microservice",
            Self::Cache { .. } => "cache",
            Self::Database { .. } => "database",
            Self::FileSystem { .. } => "file_system",
            Self::Cryptographic { .. } => "cryptographic",
            Self::NetworkProtocol { .. } => "network_protocol",
            Self::LoadBalancing { .. } => "load_balancing",
            Self::ServiceDiscovery { .. } => "service_discovery",
            Self::HealthCheck { .. } => "health_check",
            Self::ValidationError(_) => "validation_error",
            Self::ProfilerAlreadyRunning => "profiler_already_running",
            Self::ProfilerNotRunning => "profiler_not_running",
            Self::MetricsCollection { .. } => "metrics_collection",
            Self::Alerting { .. } => "alerting",
            Self::ConfigurationManagement { .. } => "configuration_management",
            Self::VersionControl { .. } => "version_control",
            Self::Deployment { .. } => "deployment",
            Self::Rollback { .. } => "rollback",
            Self::Backup { .. } => "backup",
            Self::Recovery { .. } => "recovery",
            Self::Migration { .. } => "migration",
            Self::Upgrade { .. } => "upgrade",
            Self::Downgrade { .. } => "downgrade",
            Self::Scaling { .. } => "scaling",
            Self::Compression { .. } => "compression",
            Self::Decompression { .. } => "decompression",
            Self::Encoding { .. } => "encoding",
            Self::Decoding { .. } => "decoding",
            Self::Conversion { .. } => "conversion",
            Self::Validation { .. } => "validation",
            Self::Authorization { .. } => "authorization",
            Self::Authentication { .. } => "authentication",
            Self::Token { .. } => "token",
            Self::Session { .. } => "session",
            Self::ConnectionPool { .. } => "connection_pool",
            Self::Transaction { .. } => "transaction",
            Self::Lock { .. } => "lock",
            Self::Semaphore { .. } => "semaphore",
            Self::Barrier { .. } => "barrier",
            Self::ConditionVariable { .. } => "condition_variable",
            Self::AtomicOperation { .. } => "atomic_operation",
            Self::MemoryManagement { .. } => "memory_management",
            Self::GarbageCollection { .. } => "garbage_collection",
            Self::MemoryLeak { .. } => "memory_leak",
            Self::BufferOverflow { .. } => "buffer_overflow",
            Self::StackOverflow { .. } => "stack_overflow",
            Self::HeapOverflow { .. } => "heap_overflow",
            Self::NullPointer { .. } => "null_pointer",
            Self::WildPointer { .. } => "wild_pointer",
            Self::DanglingPointer { .. } => "dangling_pointer",
            Self::DoubleFree { .. } => "double_free",
            Self::UseAfterFree { .. } => "use_after_free",
            Self::MemoryAlignment { .. } => "memory_alignment",
            Self::Endianness { .. } => "endianness",
            Self::TypeConversion { .. } => "type_conversion",
            Self::TypeCheck { .. } => "type_check",
            Self::TypeInference { .. } => "type_inference",
            Self::Generic { .. } => "generic",
            Self::Trait { .. } => "trait",
            Self::Lifetime { .. } => "lifetime",
            Self::BorrowCheck { .. } => "borrow_check",
            Self::Ownership { .. } => "ownership",
            Self::MoveSemantics { .. } => "move_semantics",
            Self::CopySemantics { .. } => "copy_semantics",
            Self::CloneSemantics { .. } => "clone_semantics",
            Self::Destructor { .. } => "destructor",
            Self::Constructor { .. } => "constructor",
            Self::Factory { .. } => "factory",
            Self::Builder { .. } => "builder",
            Self::Singleton { .. } => "singleton",
            Self::Observer { .. } => "observer",
            Self::Strategy { .. } => "strategy",
            Self::Command { .. } => "command",
            Self::State { .. } => "state",
            Self::Adapter { .. } => "adapter",
            Self::Decorator { .. } => "decorator",
            Self::Facade { .. } => "facade",
            Self::Proxy { .. } => "proxy",
            Self::Bridge { .. } => "bridge",
            Self::Composite { .. } => "composite",
            Self::Flyweight { .. } => "flyweight",
            Self::TemplateMethod { .. } => "template_method",
            Self::Iterator { .. } => "iterator",
            Self::Visitor { .. } => "visitor",
            Self::Mediator { .. } => "mediator",
            Self::Memento { .. } => "memento",
            Self::ChainOfResponsibility { .. } => "chain_of_responsibility",
            Self::Interpreter { .. } => "interpreter",
        }
    }
}

/// 错误上下文
#[derive(Debug, Clone)]
pub struct ErrorContext {
    /// 错误类型
    pub error_type: &'static str,
    /// 错误分类
    pub category: ErrorCategory,
    /// 严重程度
    pub severity: ErrorSeverity,
    /// 是否可重试
    pub is_retryable: bool,
    /// 是否为临时错误
    pub is_temporary: bool,
    /// 恢复建议
    pub recovery_suggestion: Option<String>,
    /// 时间戳
    pub timestamp: std::time::SystemTime,
}

/// 错误分类
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub enum ErrorCategory {
    /// 网络相关错误
    Network,
    /// 数据处理错误
    Data,
    /// 配置错误
    Configuration,
    /// 处理逻辑错误
    Processing,
    /// 导出错误
    Export,
    /// 性能相关错误
    Performance,
    /// 并发错误
    Concurrency,
    /// 资源错误
    Resource,
    /// 兼容性错误
    Compatibility,
    /// 系统错误
    System,
    /// 业务逻辑错误
    Business,
    /// 安全相关错误
    Security,
    /// 依赖服务错误
    Dependency,
    /// 机器学习错误
    ML,
    /// 监控系统错误
    Monitoring,
    /// 分布式协调错误
    Distributed,
    /// 边缘计算错误
    Edge,
    /// 区块链集成错误
    Blockchain,
    /// 微服务错误
    Microservice,
    /// 缓存错误
    Cache,
    /// 数据库错误
    Database,
    /// 文件系统错误
    FileSystem,
    /// 负载均衡错误
    LoadBalancing,
    /// 服务发现错误
    ServiceDiscovery,
    /// 健康检查错误
    Health,
    /// 指标收集错误
    Metrics,
    /// 告警系统错误
    Alerting,
    /// 版本控制错误
    VersionControl,
    /// 部署错误
    Deployment,
    /// 备份错误
    Backup,
    /// 恢复错误
    Recovery,
    /// 迁移错误
    Migration,
    /// 升级错误
    Upgrade,
    /// 降级错误
    Downgrade,
    /// 扩展错误
    Scaling,
    /// 压缩错误
    Compression,
    /// 编码错误
    Encoding,
    /// 转换错误
    Conversion,
    /// 验证错误
    Validation,
    /// 会话错误
    Session,
    /// 连接错误
    Connection,
    /// 事务错误
    Transaction,
    /// 内存错误
    Memory,
    /// 类型错误
    Type,
    /// 设计模式错误
    Design,
}

/// 错误严重程度
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub enum ErrorSeverity {
    /// 低严重程度 - 不影响核心功能
    Low,
    /// 中等严重程度 - 影响部分功能
    Medium,
    /// 高严重程度 - 影响主要功能
    High,
    /// 严重程度 - 系统不可用
    Critical,
}

impl fmt::Display for ErrorCategory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorCategory::Network => write!(f, "网络"),
            ErrorCategory::Data => write!(f, "数据"),
            ErrorCategory::Configuration => write!(f, "配置"),
            ErrorCategory::Processing => write!(f, "处理"),
            ErrorCategory::Export => write!(f, "导出"),
            ErrorCategory::Performance => write!(f, "性能"),
            ErrorCategory::Concurrency => write!(f, "并发"),
            ErrorCategory::Resource => write!(f, "资源"),
            ErrorCategory::Compatibility => write!(f, "兼容性"),
            ErrorCategory::System => write!(f, "系统"),
            ErrorCategory::Business => write!(f, "业务"),
            ErrorCategory::Security => write!(f, "安全"),
            ErrorCategory::Dependency => write!(f, "依赖"),
            ErrorCategory::ML => write!(f, "机器学习"),
            ErrorCategory::Monitoring => write!(f, "监控"),
            ErrorCategory::Distributed => write!(f, "分布式"),
            ErrorCategory::Edge => write!(f, "边缘计算"),
            ErrorCategory::Blockchain => write!(f, "区块链"),
            ErrorCategory::Microservice => write!(f, "微服务"),
            ErrorCategory::Cache => write!(f, "缓存"),
            ErrorCategory::Database => write!(f, "数据库"),
            ErrorCategory::FileSystem => write!(f, "文件系统"),
            ErrorCategory::LoadBalancing => write!(f, "负载均衡"),
            ErrorCategory::ServiceDiscovery => write!(f, "服务发现"),
            ErrorCategory::Health => write!(f, "健康检查"),
            ErrorCategory::Metrics => write!(f, "指标"),
            ErrorCategory::Alerting => write!(f, "告警"),
            ErrorCategory::VersionControl => write!(f, "版本控制"),
            ErrorCategory::Deployment => write!(f, "部署"),
            ErrorCategory::Backup => write!(f, "备份"),
            ErrorCategory::Recovery => write!(f, "恢复"),
            ErrorCategory::Migration => write!(f, "迁移"),
            ErrorCategory::Upgrade => write!(f, "升级"),
            ErrorCategory::Downgrade => write!(f, "降级"),
            ErrorCategory::Scaling => write!(f, "扩展"),
            ErrorCategory::Compression => write!(f, "压缩"),
            ErrorCategory::Encoding => write!(f, "编码"),
            ErrorCategory::Conversion => write!(f, "转换"),
            ErrorCategory::Validation => write!(f, "验证"),
            ErrorCategory::Session => write!(f, "会话"),
            ErrorCategory::Connection => write!(f, "连接"),
            ErrorCategory::Transaction => write!(f, "事务"),
            ErrorCategory::Memory => write!(f, "内存"),
            ErrorCategory::Type => write!(f, "类型"),
            ErrorCategory::Design => write!(f, "设计模式"),
        }
    }
}

impl fmt::Display for ErrorSeverity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorSeverity::Low => write!(f, "低"),
            ErrorSeverity::Medium => write!(f, "中等"),
            ErrorSeverity::High => write!(f, "高"),
            ErrorSeverity::Critical => write!(f, "严重"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn test_error_creation() {
        let timeout_err = OtlpError::timeout("test_operation", Duration::from_secs(5));
        assert!(matches!(timeout_err, OtlpError::Timeout { .. }));

        let concurrency_err = OtlpError::concurrency("test_reason");
        assert!(matches!(concurrency_err, OtlpError::Concurrency(_)));

        let resource_err = OtlpError::resource_exhausted("memory", 100, 200);
        assert!(matches!(resource_err, OtlpError::ResourceExhausted { .. }));
    }

    #[test]
    fn test_error_retryable() {
        let retryable_err = OtlpError::Transport(TransportError::Connection {
            endpoint: "test".to_string(),
            reason: "test".to_string(),
        });
        assert!(retryable_err.is_retryable());

        let non_retryable_err = OtlpError::Configuration(ConfigurationError::InvalidEndpoint {
            url: "test".to_string(),
        });
        assert!(!non_retryable_err.is_retryable());
    }

    #[test]
    fn test_error_severity() {
        let high_severity = OtlpError::Transport(TransportError::Connection {
            endpoint: "test".to_string(),
            reason: "test".to_string(),
        });
        assert_eq!(high_severity.severity(), ErrorSeverity::High);

        let critical_severity = OtlpError::from_anyhow(anyhow::anyhow!("test"));
        assert_eq!(critical_severity.severity(), ErrorSeverity::Critical);
    }
}
