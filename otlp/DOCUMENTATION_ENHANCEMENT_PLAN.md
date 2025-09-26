# 📚 OTLP Rust 文档体系完善计划

## 📋 文档概览

**完善目标**: 建立完整、清晰、易用的文档体系  
**文档范围**: 用户指南、API文档、开发文档、运维文档  
**实施周期**: 3-4周  
**预期收益**: 提升用户体验和开发效率

## 🎯 文档架构设计

### 文档层次结构

```text
docs/
├── README.md                    # 项目概览
├── QUICK_START.md              # 快速开始
├── USER_GUIDE/                 # 用户指南
│   ├── installation.md         # 安装指南
│   ├── configuration.md        # 配置说明
│   ├── basic_usage.md          # 基础使用
│   ├── advanced_usage.md       # 高级用法
│   └── troubleshooting.md      # 故障排除
├── API_REFERENCE/              # API参考
│   ├── client.md               # 客户端API
│   ├── config.md               # 配置API
│   ├── data_types.md           # 数据类型
│   └── error_handling.md       # 错误处理
├── DEVELOPER_GUIDE/            # 开发者指南
│   ├── architecture.md         # 架构设计
│   ├── contributing.md         # 贡献指南
│   ├── testing.md              # 测试指南
│   └── performance.md          # 性能优化
├── OPERATIONS/                 # 运维文档
│   ├── deployment.md           # 部署指南
│   ├── monitoring.md           # 监控配置
│   ├── troubleshooting.md      # 运维故障排除
│   └── security.md             # 安全配置
└── EXAMPLES/                   # 示例代码
    ├── basic_examples/         # 基础示例
    ├── advanced_examples/      # 高级示例
    └── integration_examples/   # 集成示例
```

## 📖 用户指南文档

### 1. 快速开始指南

```markdown
    # 🚀 OTLP Rust 快速开始

    ## 安装

    ### 使用 Cargo 安装

    ```toml
    [dependencies]
    otlp = "1.0.0"
    tokio = { version = "1.0", features = ["full"] }
    ```

    ### 使用 Docker 运行

    ```bash
    docker run -p 4317:4317 -p 4318:4318 docker.io/your-org/otlp-rust:latest
    ```

    ## 5分钟快速体验

    ### 1. 创建客户端

    ```rust
    use otlp::SimpleOtlpClient;

    #[tokio::main]
    async fn main() -> Result<(), Box<dyn std::error::Error>> {
        // 创建简单的OTLP客户端
        let client = SimpleOtlpClient::new("http://localhost:4317").await?;
        
        // 发送追踪数据
        client.trace("user-login", 150, true, None::<String>).await?;
        
        // 发送指标数据
        client.metric("login_count", 1.0, Some("count")).await?;
        
        // 发送日志数据
        client.log("User logged in successfully", LogLevel::Info, Some("auth")).await?;
        
        Ok(())
    }
    ```

    ### 2. 高级配置

    ```rust
    use otlp::{OtlpClient, OtlpConfig, TransportProtocol};
    use std::time::Duration;

    #[tokio::main]
    async fn main() -> Result<(), Box<dyn std::error::Error>> {
        // 创建配置
        let config = OtlpConfig::default()
            .with_endpoint("http://localhost:4317")
            .with_protocol(TransportProtocol::Grpc)
            .with_batch_size(100)
            .with_timeout(Duration::from_secs(5));
        
        // 创建客户端
        let client = OtlpClient::new(config).await?;
        client.initialize().await?;
        
        // 使用构建器模式发送数据
        let trace = client.send_trace("database-query").await?;
        trace
            .with_attribute("table", "users")
            .with_attribute("operation", "select")
            .with_duration(250)
            .finish()
            .await?;
        
        Ok(())
    }
    ```

    ## 下一步

    - 📖 阅读 [用户指南](USER_GUIDE/basic_usage.md) 了解更多功能
    - 🔧 查看 [配置说明](USER_GUIDE/configuration.md) 进行高级配置
    - 🚀 探索 [高级用法](USER_GUIDE/advanced_usage.md) 实现复杂场景

```

### 2. 安装指南

```markdown
    # 📦 安装指南

    ## 系统要求

    - Rust 1.90 或更高版本
    - 支持的操作系统：Linux、macOS、Windows
    - 内存：至少 128MB 可用内存
    - 网络：支持 HTTP/HTTPS 和 gRPC 连接

    ## 安装方法

    ### 方法一：Cargo 安装（推荐）

    1. 确保已安装 Rust 1.90+

    ```bash
    rustup update
    rustup default 1.90
    ```

    2. 在 Cargo.toml 中添加依赖

    ```toml
    [dependencies]
    otlp = "1.0.0"
    tokio = { version = "1.0", features = ["full"] }
    serde = { version = "1.0", features = ["derive"] }
    ```

    3. 运行项目

    ```bash
    cargo run
    ```

    ### 方法二：Docker 安装

    1. 拉取镜像

    ```bash
    docker pull docker.io/your-org/otlp-rust:latest
    ```

    2. 运行容器

    ```bash
    docker run -d \
    --name otlp-client \
    -p 4317:4317 \
    -p 4318:4318 \
    -p 8080:8080 \
    docker.io/your-org/otlp-rust:latest
    ```

    3. 验证安装

    ```bash
    curl http://localhost:8080/health
    ```

    ### 方法三：Kubernetes 部署

    1. 添加 Helm 仓库

    ```bash
    helm repo add otlp https://charts.your-org.com/otlp
    helm repo update
    ```

    2. 安装 Chart

    ```bash
    helm install otlp-client otlp/otlp-client \
    --namespace otlp-system \
    --create-namespace
    ```

    3. 验证部署

    ```bash
    kubectl get pods -n otlp-system
    kubectl port-forward svc/otlp-client 8080:8080 -n otlp-system
    ```

    ## 验证安装

    ### 健康检查

    ```bash
    # HTTP 健康检查
    curl http://localhost:8080/health

    # gRPC 健康检查
    grpcurl -plaintext localhost:4317 grpc.health.v1.Health/Check
    ```

    ### 功能测试

    ```rust
    #[tokio::test]
    async fn test_installation() {
        let client = SimpleOtlpClient::new("http://localhost:4317").await.unwrap();
        let result = client.trace("test", 100, true, None::<String>).await;
        assert!(result.is_ok());
    }
    ```

    ## 故障排除

    ### 常见问题

    1. **连接失败**
    - 检查端点 URL 是否正确
    - 确认网络连接是否正常
    - 验证防火墙设置

    2. **编译错误**
    - 确认 Rust 版本是否为 1.90+
    - 检查依赖版本是否兼容
    - 清理并重新构建：`cargo clean && cargo build`

    3. **运行时错误**
    - 检查配置文件格式
    - 验证权限设置
    - 查看日志输出

    ### 获取帮助

    - 📖 查看 [故障排除指南](USER_GUIDE/troubleshooting.md)
    - 💬 加入 [社区讨论](https://github.com/your-org/otlp-rust/discussions)
    - 🐛 报告 [问题](https://github.com/your-org/otlp-rust/issues)

```

### 3. 配置说明

```markdown
    # ⚙️ 配置说明

    ## 配置文件格式

    OTLP Rust 支持多种配置格式：TOML、YAML、JSON 和环境变量。

    ### TOML 配置示例

    ```toml
    [otlp]
    endpoint = "http://localhost:4317"
    protocol = "grpc"
    batch_size = 100
    timeout = "5s"

    [resilience]
    max_retries = 3
    retry_delay = "100ms"
    circuit_breaker_threshold = 5

    [monitoring]
    metrics_enabled = true
    health_check_interval = "30s"
    ```

    ### YAML 配置示例

    ```yaml
    otlp:
    endpoint: "http://localhost:4317"
    protocol: "grpc"
    batch_size: 100
    timeout: "5s"

    resilience:
    max_retries: 3
    retry_delay: "100ms"
    circuit_breaker_threshold: 5

    monitoring:
    metrics_enabled: true
    health_check_interval: "30s"
    ```

    ## 配置选项详解

    ### 基础配置

    | 选项 | 类型 | 默认值 | 说明 |
    |------|------|--------|------|
    | `endpoint` | String | `http://localhost:4317` | OTLP 端点地址 |
    | `protocol` | String | `grpc` | 传输协议 (grpc/http) |
    | `batch_size` | Integer | 100 | 批处理大小 |
    | `timeout` | Duration | `5s` | 请求超时时间 |

    ### 弹性配置

    | 选项 | 类型 | 默认值 | 说明 |
    |------|------|--------|------|
    | `max_retries` | Integer | 3 | 最大重试次数 |
    | `retry_delay` | Duration | `100ms` | 重试延迟时间 |
    | `circuit_breaker_threshold` | Integer | 5 | 熔断器阈值 |

    ### 监控配置

    | 选项 | 类型 | 默认值 | 说明 |
    |------|------|--------|------|
    | `metrics_enabled` | Boolean | true | 是否启用指标收集 |
    | `health_check_interval` | Duration | `30s` | 健康检查间隔 |

    ## 环境变量配置

    ```bash
    # 基础配置
    export OTLP_ENDPOINT="http://localhost:4317"
    export OTLP_PROTOCOL="grpc"
    export OTLP_BATCH_SIZE="100"
    export OTLP_TIMEOUT="5s"

    # 弹性配置
    export OTLP_MAX_RETRIES="3"
    export OTLP_RETRY_DELAY="100ms"
    export OTLP_CIRCUIT_BREAKER_THRESHOLD="5"

    # 监控配置
    export OTLP_METRICS_ENABLED="true"
    export OTLP_HEALTH_CHECK_INTERVAL="30s"
    ```

    ## 配置验证

    ### 程序化验证

    ```rust
    use otlp::OtlpConfig;

    #[tokio::main]
    async fn main() -> Result<(), Box<dyn std::error::Error>> {
        let config = OtlpConfig::from_file("config.toml")?;
        
        // 验证配置
        config.validate()?;
        
        println!("配置验证通过: {:?}", config);
        Ok(())
    }
    ```

    ### 命令行验证

    ```bash
    # 验证配置文件
    otlp-client --config config.toml --validate

    # 显示配置信息
    otlp-client --config config.toml --show-config
    ```

    ## 配置最佳实践

    ### 1. 生产环境配置

    ```toml
    [otlp]
    endpoint = "https://otlp-collector.company.com"
    protocol = "grpc"
    batch_size = 1000
    timeout = "10s"

    [resilience]
    max_retries = 5
    retry_delay = "200ms"
    circuit_breaker_threshold = 10

    [monitoring]
    metrics_enabled = true
    health_check_interval = "15s"
    ```

    ### 2. 开发环境配置

    ```toml
    [otlp]
    endpoint = "http://localhost:4317"
    protocol = "grpc"
    batch_size = 10
    timeout = "1s"

    [resilience]
    max_retries = 1
    retry_delay = "50ms"
    circuit_breaker_threshold = 3

    [monitoring]
    metrics_enabled = false
    health_check_interval = "60s"
    ```

    ### 3. 测试环境配置

    ```toml
    [otlp]
    endpoint = "http://test-otlp:4317"
    protocol = "grpc"
    batch_size = 100
    timeout = "5s"

    [resilience]
    max_retries = 2
    retry_delay = "100ms"
    circuit_breaker_threshold = 5

    [monitoring]
    metrics_enabled = true
    health_check_interval = "30s"
    ```

```

## 📚 API 参考文档

### 1. 客户端 API

```markdown
    # 🔧 客户端 API 参考

    ## SimpleOtlpClient

    简单易用的 OTLP 客户端，适合快速集成。

    ### 构造函数

    ```rust
    impl SimpleOtlpClient {
        /// 创建新的简单客户端
        /// 
        /// # 参数
        /// 
        /// * `endpoint` - OTLP 端点地址
        /// 
        /// # 示例
        /// 
        /// ```rust
        /// let client = SimpleOtlpClient::new("http://localhost:4317").await?;
        /// ```
        pub async fn new(endpoint: impl Into<String>) -> Result<Self>;
    }
    ```

    ### 方法

    #### trace

    发送追踪数据。

    ```rust
    /// 发送追踪数据
    /// 
    /// # 参数
    /// 
    /// * `name` - 操作名称
    /// * `duration_ms` - 持续时间（毫秒）
    /// * `success` - 是否成功
    /// * `error` - 错误信息（可选）
    /// 
    /// # 示例
    /// 
    /// ```rust
    /// client.trace("database-query", 150, true, None::<String>).await?;
    /// client.trace("api-call", 200, false, Some("timeout".to_string())).await?;
    /// ```
    pub async fn trace(
        &self,
        name: impl Into<String>,
        duration_ms: u64,
        success: bool,
        error: Option<String>
    ) -> Result<()>;
    ```

    #### metric

    发送指标数据。

    ```rust
    /// 发送指标数据
    /// 
    /// # 参数
    /// 
    /// * `name` - 指标名称
    /// * `value` - 指标值
    /// * `unit` - 单位（可选）
    /// 
    /// # 示例
    /// 
    /// ```rust
    /// client.metric("request_count", 1.0, Some("count")).await?;
    /// client.metric("response_time", 150.0, Some("ms")).await?;
    /// ```
    pub async fn metric(
        &self,
        name: impl Into<String>,
        value: f64,
        unit: Option<String>
    ) -> Result<()>;
    ```

    #### log

    发送日志数据。

    ```rust
    /// 发送日志数据
    /// 
    /// # 参数
    /// 
    /// * `message` - 日志消息
    /// * `level` - 日志级别
    /// * `source` - 日志来源（可选）
    /// 
    /// # 示例
    /// 
    /// ```rust
    /// client.log("User logged in", LogLevel::Info, Some("auth")).await?;
    /// client.log("Database error", LogLevel::Error, Some("db")).await?;
    /// ```
    pub async fn log(
        &self,
        message: impl Into<String>,
        level: LogLevel,
        source: Option<String>
    ) -> Result<()>;
    ```

    ## OtlpClient

    功能完整的高级 OTLP 客户端。

    ### 构造函数

    ```rust
    impl OtlpClient {
        /// 创建新的 OTLP 客户端
        /// 
        /// # 参数
        /// 
        /// * `config` - 客户端配置
        /// 
        /// # 示例
        /// 
        /// ```rust
        /// let config = OtlpConfig::default()
        ///     .with_endpoint("http://localhost:4317")
        ///     .with_batch_size(100);
        /// let client = OtlpClient::new(config).await?;
        /// client.initialize().await?;
        /// ```
        pub async fn new(config: OtlpConfig) -> Result<Self>;
        
        /// 初始化客户端
        /// 
        /// 必须在发送数据前调用此方法。
        /// 
        /// # 示例
        /// 
        /// ```rust
        /// client.initialize().await?;
        /// ```
        pub async fn initialize(&self) -> Result<()>;
    }
    ```

    ### 构建器方法

    #### send_trace

    创建追踪构建器。

    ```rust
    /// 创建追踪构建器
    /// 
    /// # 参数
    /// 
    /// * `name` - 操作名称
    /// 
    /// # 返回值
    /// 
    /// 返回 `TraceBuilder` 实例，支持链式调用。
    /// 
    /// # 示例
    /// 
    /// ```rust
    /// let trace = client.send_trace("database-query").await?;
    /// trace
    ///     .with_attribute("table", "users")
    ///     .with_attribute("operation", "select")
    ///     .with_duration(150)
    ///     .with_status(StatusCode::Ok, None)
    ///     .finish()
    ///     .await?;
    /// ```
    pub async fn send_trace(&self, name: impl Into<String>) -> Result<TraceBuilder>;
    ```

    #### send_metric

    创建指标构建器。

    ```rust
    /// 创建指标构建器
    /// 
    /// # 参数
    /// 
    /// * `name` - 指标名称
    /// * `value` - 指标值
    /// 
    /// # 返回值
    /// 
    /// 返回 `MetricBuilder` 实例，支持链式调用。
    /// 
    /// # 示例
    /// 
    /// ```rust
    /// let metric = client.send_metric("request_count", 1.0).await?;
    /// metric
    ///     .with_label("method", "GET")
    ///     .with_label("status", "200")
    ///     .with_description("HTTP request count")
    ///     .with_unit("count")
    ///     .send()
    ///     .await?;
    /// ```
    pub async fn send_metric(&self, name: impl Into<String>, value: f64) -> Result<MetricBuilder>;
    ```

    #### send_log

    创建日志构建器。

    ```rust
    /// 创建日志构建器
    /// 
    /// # 参数
    /// 
    /// * `message` - 日志消息
    /// * `severity` - 日志严重程度
    /// 
    /// # 返回值
    /// 
    /// 返回 `LogBuilder` 实例，支持链式调用。
    /// 
    /// # 示例
    /// 
    /// ```rust
    /// let log = client.send_log("User action", LogSeverity::Info).await?;
    /// log
    ///     .with_attribute("user_id", "12345")
    ///     .with_attribute("action", "login")
    ///     .with_trace_context("trace-id", "span-id")
    ///     .send()
    ///     .await?;
    /// ```
    pub async fn send_log(
        &self,
        message: impl Into<String>,
        severity: LogSeverity
    ) -> Result<LogBuilder>;
    ```

    ## 错误处理

    ### OtlpError

    主要的错误类型。

    ```rust
    #[derive(Debug, thiserror::Error)]
    pub enum OtlpError {
        #[error("网络错误: {context}")]
        Network { context: String, source: Box<dyn std::error::Error + Send + Sync> },
        
        #[error("配置错误: {field} = {value}")]
        Configuration { field: String, value: String },
        
        #[error("处理错误: {operation}")]
        Processing { operation: String, source: Box<dyn std::error::Error + Send + Sync> },
        
        #[error("内部错误: {message}")]
        Internal { message: String },
    }
    ```

    ### 错误处理示例

    ```rust
    use otlp::{OtlpClient, OtlpError};

    #[tokio::main]
    async fn main() -> Result<(), Box<dyn std::error::Error>> {
        let client = OtlpClient::new(config).await?;
        
        match client.initialize().await {
            Ok(_) => println!("客户端初始化成功"),
            Err(OtlpError::Configuration { field, value }) => {
                eprintln!("配置错误: {} = {}", field, value);
            }
            Err(OtlpError::Network { context, .. }) => {
                eprintln!("网络错误: {}", context);
            }
            Err(e) => {
                eprintln!("其他错误: {}", e);
            }
        }
        
        Ok(())
    }
    ```

```

## 🛠️ 开发者指南

### 1. 架构设计文档

```markdown
    # 🏗️ 架构设计

    ## 整体架构

    OTLP Rust 采用分层架构设计，确保模块化、可扩展性和高性能。

    ```text

    ┌─────────────────────────────────────────────────────────┐
    │                    OTLP Client Layer                    │
    │  ┌─────────────────┬─────────────────┬─────────────────┐ │
    │  │   Telemetry     │   Configuration │   Monitoring    │ │
    │  │   Operations    │   Management    │   & Metrics     │ │
    │  └─────────────────┴─────────────────┴─────────────────┘ │
    └─────────────────────────────────────────────────────────┘
                                │
                                ▼
    ┌─────────────────────────────────────────────────────────┐
    │                 Resilience Manager                      │
    │  ┌─────────────┬─────────────┬─────────────┬─────────────┐ │
    │  │    Retry    │   Circuit   │   Timeout   │   Health    │ │
    │  │  Mechanism  │   Breaker   │   Control   │   Check     │ │
    │  └─────────────┴─────────────┴─────────────┴─────────────┘ │
    └─────────────────────────────────────────────────────────┘
                                │
                                ▼
    ┌─────────────────────────────────────────────────────────┐
    │                Processing & Transport Layer             │
    │  ┌─────────────┬─────────────┬─────────────┬─────────────┐ │
    │  │  Exporter   │  Processor  │  Transport  │   Client    │ │
    │  │             │             │             │             │ │
    │  └─────────────┴─────────────┴─────────────┴─────────────┘ │
    └─────────────────────────────────────────────────────────┘

    ```

    ## 核心组件

    ### 1. 客户端层 (Client Layer)

    负责提供用户友好的 API 接口，处理遥测数据的创建和发送。

    **主要组件：**
    - `SimpleOtlpClient`: 简单易用的客户端
    - `OtlpClient`: 功能完整的高级客户端
    - `TraceBuilder`: 追踪数据构建器
    - `MetricBuilder`: 指标数据构建器
    - `LogBuilder`: 日志数据构建器

    ### 2. 弹性管理层 (Resilience Layer)

    提供容错和恢复机制，确保系统在各种异常情况下的稳定性。

    **主要组件：**
    - `ResilienceManager`: 弹性管理器
    - `CircuitBreaker`: 熔断器
    - `RetryMechanism`: 重试机制
    - `TimeoutControl`: 超时控制
    - `HealthChecker`: 健康检查

    ### 3. 处理传输层 (Processing & Transport Layer)

    负责数据的处理、批量和传输。

    **主要组件：**
    - `OtlpExporter`: 数据导出器
    - `OtlpProcessor`: 数据处理器
    - `GrpcTransport`: gRPC 传输
    - `HttpTransport`: HTTP 传输

    ## 设计原则

    ### 1. 单一职责原则

    每个模块都有明确的职责边界：
    - 客户端层：用户接口和数据创建
    - 弹性层：容错和恢复
    - 处理层：数据处理和传输

    ### 2. 开闭原则

    系统对扩展开放，对修改封闭：
    - 支持插件系统
    - 可配置的传输协议
    - 可扩展的处理器

    ### 3. 依赖倒置原则

    高层模块不依赖低层模块，都依赖于抽象：
    - 使用 trait 定义接口
    - 依赖注入容器
    - 配置驱动的实现

    ### 4. 接口隔离原则

    客户端不应该依赖它不需要的接口：
    - 细粒度的 trait 定义
    - 可选的功能模块
    - 最小化的依赖

    ## 性能优化

    ### 1. 异步优先

    充分利用 Rust 的异步特性：
    - 基于 tokio 运行时
    - 非阻塞 I/O 操作
    - 高并发处理能力

    ### 2. 零拷贝优化

    减少不必要的数据拷贝：
    - 使用 `Cow` 类型
    - 智能的数据处理
    - 内存池管理

    ### 3. 批处理优化

    提高数据传输效率：
    - 智能批处理策略
    - 异步批处理器
    - 背压控制

    ### 4. 并发优化

    提升并发处理能力：
    - 无锁数据结构
    - 原子操作
    - 读写锁优化

    ## 扩展性设计

    ### 1. 插件系统

    支持自定义扩展：
    ```rust
    pub trait Plugin: Send + Sync {
        fn name(&self) -> &str;
        fn process(&self, data: &mut TelemetryData) -> Result<()>;
    }
    ```

    ### 2. 配置驱动

    支持灵活的配置管理：

    ```rust
    pub struct OtlpConfig {
        pub endpoint: Endpoint,
        pub protocol: TransportProtocol,
        pub batch_size: BatchSize,
        // ... 更多配置选项
    }
    ```

    ### 3. 接口抽象

    清晰的接口定义：

    ```rust
    pub trait Exporter: Send + Sync {
        async fn export(&self, data: Vec<TelemetryData>) -> Result<ExportResult>;
    }

    pub trait Processor: Send + Sync {
        async fn process(&self, data: TelemetryData) -> Result<()>;
    }
    ```

    ## 安全考虑

    ### 1. 内存安全

    利用 Rust 的所有权系统：

    - 编译时内存安全
    - 无数据竞争
    - 自动内存管理

    ### 2. 类型安全

    强类型系统：

    - 编译时类型检查
    - 防止类型错误
    - 清晰的错误信息

    ### 3. 并发安全

    安全的并发编程：

    - 所有权和借用检查
    - 无锁数据结构
    - 原子操作

    ## 测试策略

    ### 1. 单元测试

    测试单个组件的功能：

    - 高覆盖率 (>95%)
    - 快速执行 (<1分钟)
    - 隔离测试

    ### 2. 集成测试

    测试组件间的交互：

    - 端到端测试
    - 真实环境测试
    - 性能测试

    ### 3. 压力测试

    验证系统在高负载下的表现：

    - 并发测试
    - 内存泄漏测试
    - 长时间运行测试

```

## 📝 示例代码文档

### 1. 基础示例

```markdown
    # 📝 基础示例

    ## 简单使用

    ### 发送追踪数据

    ```rust
    use otlp::SimpleOtlpClient;

    #[tokio::main]
    async fn main() -> Result<(), Box<dyn std::error::Error>> {
        let client = SimpleOtlpClient::new("http://localhost:4317").await?;
        
        // 发送成功的操作
        client.trace("user-login", 150, true, None::<String>).await?;
        
        // 发送失败的操作
        client.trace("database-query", 200, false, Some("timeout".to_string())).await?;
        
        Ok(())
    }
    ```

    ### 发送指标数据

    ```rust
    use otlp::SimpleOtlpClient;

    #[tokio::main]
    async fn main() -> Result<(), Box<dyn std::error::Error>> {
        let client = SimpleOtlpClient::new("http://localhost:4317").await?;
        
        // 发送计数器指标
        client.metric("request_count", 1.0, Some("count")).await?;
        
        // 发送响应时间指标
        client.metric("response_time", 150.0, Some("ms")).await?;
        
        // 发送内存使用指标
        client.metric("memory_usage", 512.0, Some("MB")).await?;
        
        Ok(())
    }
    ```

    ### 发送日志数据

    ```rust
    use otlp::{SimpleOtlpClient, LogLevel};

    #[tokio::main]
    async fn main() -> Result<(), Box<dyn std::error::Error>> {
        let client = SimpleOtlpClient::new("http://localhost:4317").await?;
        
        // 发送信息日志
        client.log("User logged in successfully", LogLevel::Info, Some("auth")).await?;
        
        // 发送警告日志
        client.log("High memory usage detected", LogLevel::Warn, Some("monitor")).await?;
        
        // 发送错误日志
        client.log("Database connection failed", LogLevel::Error, Some("db")).await?;
        
        Ok(())
    }
    ```

    ## 高级使用

    ### 使用构建器模式

    ```rust
    use otlp::{OtlpClient, OtlpConfig, TransportProtocol};
    use std::time::Duration;

    #[tokio::main]
    async fn main() -> Result<(), Box<dyn std::error::Error>> {
        let config = OtlpConfig::default()
            .with_endpoint("http://localhost:4317")
            .with_protocol(TransportProtocol::Grpc)
            .with_batch_size(100)
            .with_timeout(Duration::from_secs(5));
        
        let client = OtlpClient::new(config).await?;
        client.initialize().await?;
        
        // 创建详细的追踪数据
        let trace = client.send_trace("database-query").await?;
        trace
            .with_attribute("table", "users")
            .with_attribute("operation", "select")
            .with_attribute("user_id", "12345")
            .with_duration(250)
            .with_status(StatusCode::Ok, None)
            .finish()
            .await?;
        
        // 创建详细的指标数据
        let metric = client.send_metric("query_duration", 250.0).await?;
        metric
            .with_label("table", "users")
            .with_label("operation", "select")
            .with_description("Database query duration")
            .with_unit("ms")
            .send()
            .await?;
        
        Ok(())
    }
    ```

    ### 批量操作

    ```rust
    use otlp::{SimpleOtlpClient, SimpleOperation, LogLevel};

    #[tokio::main]
    async fn main() -> Result<(), Box<dyn std::error::Error>> {
        let client = SimpleOtlpClient::new("http://localhost:4317").await?;
        
        let operations = vec![
            SimpleOperation::Trace {
                name: "user-login".to_string(),
                duration_ms: 150,
                success: true,
                error: None,
            },
            SimpleOperation::Metric {
                name: "login_count".to_string(),
                value: 1.0,
                unit: Some("count".to_string()),
            },
            SimpleOperation::Log {
                message: "User logged in successfully".to_string(),
                level: LogLevel::Info,
                source: Some("auth".to_string()),
            },
        ];
        
        let result = client.batch_send(operations).await?;
        println!("批量发送结果: {:?}", result);
        
        Ok(())
    }
    ```

```

## 📊 文档质量指标

### 文档覆盖率

| 文档类型 | 当前覆盖率 | 目标覆盖率 | 优先级 |
|----------|------------|------------|--------|
| API 文档 | 70% | 95% | 高 |
| 用户指南 | 60% | 90% | 高 |
| 示例代码 | 50% | 85% | 中 |
| 开发者文档 | 40% | 80% | 中 |
| 运维文档 | 30% | 75% | 低 |

### 文档质量指标

| 指标 | 目标值 | 监控方式 |
|------|--------|----------|
| 文档完整性 | >90% | 自动检查 |
| 示例可运行性 | 100% | 自动化测试 |
| 链接有效性 | >95% | 定期检查 |
| 用户满意度 | >4.5/5 | 用户反馈 |

## 🛠️ 文档工具链

### 文档生成工具

```toml
[dev-dependencies]
# 文档生成
mdbook = "0.4"
mdbook-mermaid = "0.12"

# API 文档
cargo-doc = "0.1"

# 示例测试
doc-comment = "0.3"
```

### 自动化文档检查

```yaml
# .github/workflows/docs.yml
name: Documentation

on:
  push:
    branches: [ main ]
    paths: [ 'docs/**', 'src/**' ]

jobs:
  docs:
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v3
    
    - name: Install Rust
      uses: actions-rs/toolchain@v1
      with:
        toolchain: 1.90
    
    - name: Generate API docs
      run: cargo doc --no-deps --document-private-items
    
    - name: Build mdbook
      run: |
        cargo install mdbook
        mdbook build docs/
    
    - name: Check links
      run: |
        cargo install cargo-deadlinks
        cargo deadlinks
    
    - name: Deploy docs
      uses: peaceiris/actions-gh-pages@v3
      with:
        github_token: ${{ secrets.GITHUB_TOKEN }}
        publish_dir: ./docs/book
```

---

**文档负责人**: OTLP Rust 团队  
**预计完成时间**: 2025年3月  
**状态**: 🚀 进行中
