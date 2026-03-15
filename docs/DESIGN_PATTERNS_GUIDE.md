# OTLP Rust 设计模式指南

本文档详细介绍 OTLP Rust 项目中使用的设计模式及其应用场景。

## 目录

- [OTLP Rust 设计模式指南](#otlp-rust-设计模式指南)
  - [目录](#目录)
  - [1. 建造者模式 (Builder Pattern)](#1-建造者模式-builder-pattern)
    - [目的](#目的)
    - [应用场景](#应用场景)
    - [代码示例](#代码示例)
    - [优势](#优势)
  - [2. 装饰器模式 (Decorator Pattern)](#2-装饰器模式-decorator-pattern)
    - [目的](#目的-1)
    - [应用场景](#应用场景-1)
    - [代码示例](#代码示例-1)
    - [优势](#优势-1)
  - [3. 工厂模式 (Factory Pattern)](#3-工厂模式-factory-pattern)
    - [目的](#目的-2)
    - [应用场景](#应用场景-2)
    - [代码示例](#代码示例-2)
    - [优势](#优势-2)
  - [4. 策略模式 (Strategy Pattern)](#4-策略模式-strategy-pattern)
    - [目的](#目的-3)
    - [应用场景](#应用场景-3)
    - [代码示例](#代码示例-3)
    - [优势](#优势-3)
  - [5. 观察者模式 (Observer Pattern)](#5-观察者模式-observer-pattern)
    - [目的](#目的-4)
    - [应用场景](#应用场景-4)
    - [代码示例](#代码示例-4)
    - [优势](#优势-4)
  - [6. 单例模式 (Singleton Pattern)](#6-单例模式-singleton-pattern)
    - [目的](#目的-5)
    - [应用场景](#应用场景-5)
    - [代码示例](#代码示例-5)
    - [优势](#优势-5)
    - [注意事项](#注意事项)
  - [7. 其他模式](#7-其他模式)
    - [7.1 对象池模式 (Object Pool)](#71-对象池模式-object-pool)
    - [7.2 RAII 模式](#72-raii-模式)
    - [7.3 生产者-消费者模式](#73-生产者-消费者模式)
  - [模式选择指南](#模式选择指南)
  - [相关资源](#相关资源)

---

## 1. 建造者模式 (Builder Pattern)

### 目的

用于构建复杂的 OTLP 客户端配置，避免构造函数参数过多的问题。

### 应用场景

- 创建配置复杂的 `OtlpClient`
- 构建 `Exporter` 链
- 配置 `TracerProvider`

### 代码示例

```rust
pub struct TelemetryClientBuilder {
    endpoint: String,
    timeout_ms: u64,
    retry_policy: RetryPolicy,
    compression: CompressionType,
    headers: Vec<(String, String)>,
}

impl TelemetryClientBuilder {
    pub fn new() -> Self { /* ... */ }

    pub fn endpoint(mut self, endpoint: &str) -> Self {
        self.endpoint = endpoint.to_string();
        self
    }

    pub fn build(self) -> TelemetryClient {
        TelemetryClient { /* ... */ }
    }
}

// 使用
let client = TelemetryClientBuilder::new()
    .endpoint("http://otel-collector:4317")
    .timeout(5000)
    .compression(CompressionType::Zstd)
    .with_header("X-API-Key", "secret")
    .build();
```

### 优势

- 清晰的配置流程
- 可选参数支持
- 不可变配置对象

---

## 2. 装饰器模式 (Decorator Pattern)

### 目的

动态添加功能（压缩、加密、重试等）而不修改核心导出器。

### 应用场景

- 添加压缩功能
- 实现重试机制
- 添加日志记录
- 实现断路器

### 代码示例

```rust
#[async_trait::async_trait]
pub trait SpanExporter: Send + Sync {
    async fn export(&self, spans: Vec<Span>) -> Result<()>;
}

// 基础导出器
pub struct BaseExporter { /* ... */ }

// 压缩装饰器
pub struct CompressionExporter<E: SpanExporter> {
    inner: E,
    compression_level: u32,
}

impl<E: SpanExporter> SpanExporter for CompressionExporter<E> {
    async fn export(&self, spans: Vec<Span>) -> Result<()> {
        // 压缩逻辑
        self.inner.export(spans).await
    }
}

// 使用
let exporter = RetryExporter::new(
    CompressionExporter::new(
        BaseExporter::new(),
        6
    ),
    3  // 重试次数
);
```

### 优势

- 功能模块化
- 可组合
- 符合开闭原则

---

## 3. 工厂模式 (Factory Pattern)

### 目的

根据不同场景创建不同类型的导出器。

### 应用场景

- 支持多种协议（gRPC、HTTP、Kafka）
- 根据配置创建导出器
- 测试时的 mock 对象创建

### 代码示例

```rust
pub enum ExporterType {
    Grpc,
    Http,
    Kafka,
}

pub struct ExporterFactory;

impl ExporterFactory {
    pub fn create(
        exporter_type: ExporterType,
        config: &str
    ) -> Box<dyn SpanExporter> {
        match exporter_type {
            ExporterType::Grpc => Box::new(GrpcExporter::new(config)),
            ExporterType::Http => Box::new(HttpExporter::new(config)),
            ExporterType::Kafka => Box::new(KafkaExporter::new(config)),
        }
    }
}

// 使用
let exporter = ExporterFactory::create(
    ExporterType::Grpc,
    "localhost:4317"
);
```

### 优势

- 创建逻辑集中
- 易于扩展新类型
- 简化客户端代码

---

## 4. 策略模式 (Strategy Pattern)

### 目的

在运行时切换不同的算法实现。

### 应用场景

- 批处理策略（大小触发 vs 时间触发）
- 采样策略
- 负载均衡策略
- 压缩算法选择

### 代码示例

```rust
#[async_trait::async_trait]
pub trait BatchingStrategy: Send + Sync {
    async fn should_flush(
        &self,
        batch_size: usize,
        last_flush: Instant
    ) -> bool;
}

// 大小触发策略
pub struct SizeBasedStrategy { max_size: usize }

#[async_trait::async_trait]
impl BatchingStrategy for SizeBasedStrategy {
    async fn should_flush(&self, batch_size: usize, _: Instant) -> bool {
        batch_size >= self.max_size
    }
}

// 时间触发策略
pub struct TimeBasedStrategy { max_interval: Duration }

#[async_trait::async_trait]
impl BatchingStrategy for TimeBasedStrategy {
    async fn should_flush(&self, _: usize, last_flush: Instant) -> bool {
        last_flush.elapsed() >= self.max_interval
    }
}

// 使用
let strategy: Box<dyn BatchingStrategy> = if config.size_based {
    Box::new(SizeBasedStrategy { max_size: 100 })
} else {
    Box::new(TimeBasedStrategy { max_interval: Duration::from_secs(5) })
};
```

### 优势

- 算法独立变化
- 易于测试
- 运行时灵活性

---

## 5. 观察者模式 (Observer Pattern)

### 目的

建立对象间的一对多依赖关系，当一个对象状态改变时通知所有依赖者。

### 应用场景

- 遥测数据事件监听
- 配置变更通知
- 健康状态监控
- 指标收集

### 代码示例

```rust
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

// 日志观察者
pub struct LoggingObserver;

#[async_trait::async_trait]
impl TelemetryObserver for LoggingObserver {
    async fn on_event(&self, event: &TelemetryEvent) {
        println!("[LOG] {:?}", event);
    }
}

// 事件总线
pub struct TelemetryEventBus {
    observers: Vec<Box<dyn TelemetryObserver>>,
}

impl TelemetryEventBus {
    pub fn subscribe(&mut self, observer: Box<dyn TelemetryObserver>) {
        self.observers.push(observer);
    }

    pub async fn publish(&self, event: TelemetryEvent) {
        for observer in &self.observers {
            observer.on_event(&event).await;
        }
    }
}
```

### 优势

- 松耦合
- 支持广播通信
- 易于扩展新观察者

---

## 6. 单例模式 (Singleton Pattern)

### 目的

确保一个类只有一个实例，并提供全局访问点。

### 应用场景

- 全局配置管理
- 连接池
- 资源管理器
- 全局状态

### 代码示例

```rust
use std::sync::OnceLock;

pub struct GlobalConfig {
    pub service_name: String,
    pub environment: String,
}

static GLOBAL_CONFIG: OnceLock<GlobalConfig> = OnceLock::new();

pub fn init_global_config(config: GlobalConfig) -> Result<()> {
    GLOBAL_CONFIG
        .set(config)
        .map_err(|_| anyhow!("Already initialized"))
}

pub fn global_config() -> &'static GlobalConfig {
    GLOBAL_CONFIG.get_or_init(|| GlobalConfig {
        service_name: "unknown".to_string(),
        environment: "development".to_string(),
    })
}
```

### 优势

- 控制实例数量
- 全局访问点
- 延迟初始化

### 注意事项

- 谨慎使用，避免隐藏依赖
- 考虑线程安全
- 测试时可能需要重置

---

## 7. 其他模式

### 7.1 对象池模式 (Object Pool)

用于复用昂贵的对象，减少内存分配。

```rust
pub struct ObjectPool<T> {
    objects: std::sync::Mutex<Vec<T>>,
    creator: Box<dyn Fn() -> T + Send + Sync>,
}
```

### 7.2 RAII 模式

资源获取即初始化，确保资源正确释放。

```rust
pub struct SpanGuard {
    name: String,
    start: Instant,
}

impl Drop for SpanGuard {
    fn drop(&mut self) {
        // 自动发送完成事件
        self.exporter.send_completed(self.name.clone());
    }
}
```

### 7.3 生产者-消费者模式

用于异步数据处理。

```rust
let (tx, rx) = mpsc::channel(100);

// 生产者
tokio::spawn(async move {
    for item in data {
        tx.send(item).await?;
    }
});

// 消费者
tokio::spawn(async move {
    while let Some(item) = rx.recv().await {
        process(item).await;
    }
});
```

---

## 模式选择指南

| 问题 | 推荐模式 |
|------|---------|
| 复杂对象构造 | 建造者模式 |
| 动态添加功能 | 装饰器模式 |
| 多种实现切换 | 策略模式 |
| 创建相关对象 | 工厂模式 |
| 状态变更通知 | 观察者模式 |
| 全局唯一资源 | 单例模式 |
| 资源复用 | 对象池模式 |
| 资源生命周期 | RAII |
| 异步处理 | 生产者-消费者 |

---

## 相关资源

- [设计模式示例代码](../examples/design_patterns_example.rs)
- [Rust 设计模式](https://rust-unofficial.github.io/patterns/)
- [GoF 设计模式](https://refactoring.guru/design-patterns)
