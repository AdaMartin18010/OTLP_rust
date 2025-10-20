# Rust OpenTelemetry 版本升级完整指南

> **当前版本**: OpenTelemetry 0.31.0 / Rust 1.90+  
> **最后更新**: 2025年10月11日

---

## 📋 目录

- [Rust OpenTelemetry 版本升级完整指南](#rust-opentelemetry-版本升级完整指南)
  - [📋 目录](#-目录)
  - [1. 升级概述](#1-升级概述)
    - [1.1 为什么升级](#11-为什么升级)
    - [1.2 版本兼容性](#12-版本兼容性)
    - [1.3 升级风险评估](#13-升级风险评估)
  - [2. Rust 语言版本升级](#2-rust-语言版本升级)
    - [2.1 Rust 1.75 → 1.80](#21-rust-175--180)
    - [2.2 Rust 1.80 → 1.85](#22-rust-180--185)
    - [2.3 Rust 1.85 → 1.90](#23-rust-185--190)
  - [3. OpenTelemetry SDK 升级](#3-opentelemetry-sdk-升级)
    - [3.1 0.20.x → 0.22.x](#31-020x--022x)
    - [3.2 0.22.x → 0.25.x](#32-022x--025x)
    - [3.3 0.25.x → 0.31.0](#33-025x--0310)
  - [4. 依赖库升级](#4-依赖库升级)
    - [4.1 Tokio 升级](#41-tokio-升级)
    - [4.2 Tonic (gRPC) 升级](#42-tonic-grpc-升级)
    - [4.3 其他关键依赖](#43-其他关键依赖)
  - [5. 破坏性变更处理](#5-破坏性变更处理)
    - [5.1 API 变更](#51-api-变更)
    - [5.2 类型变更](#52-类型变更)
    - [5.3 特性标志变更](#53-特性标志变更)
  - [6. 升级步骤](#6-升级步骤)
    - [6.1 准备阶段](#61-准备阶段)
    - [6.2 更新依赖](#62-更新依赖)
    - [6.3 修复编译错误](#63-修复编译错误)
    - [6.4 更新代码](#64-更新代码)
    - [6.5 测试验证](#65-测试验证)
  - [7. 常见升级场景](#7-常见升级场景)
    - [7.1 Tracer Provider 初始化](#71-tracer-provider-初始化)
    - [7.2 Exporter 配置](#72-exporter-配置)
    - [7.3 Sampler 更新](#73-sampler-更新)
    - [7.4 Resource 属性](#74-resource-属性)
  - [8. 性能优化](#8-性能优化)
    - [8.1 新版本性能改进](#81-新版本性能改进)
    - [8.2 配置优化](#82-配置优化)
    - [8.3 基准测试](#83-基准测试)
  - [9. 故障排查](#9-故障排查)
    - [9.1 编译错误](#91-编译错误)
    - [9.2 运行时错误](#92-运行时错误)
    - [9.3 性能回归](#93-性能回归)
  - [10. 回滚计划](#10-回滚计划)
    - [10.1 版本固定](#101-版本固定)
    - [10.2 快速回滚](#102-快速回滚)
  - [11. 升级检查清单](#11-升级检查清单)
    - [升级前](#升级前)
    - [升级中](#升级中)
    - [升级后](#升级后)
    - [部署](#部署)
  - [12. 未来展望](#12-未来展望)
  - [参考资源](#参考资源)

---

## 1. 升级概述

### 1.1 为什么升级

**安全性**:

- 修复已知安全漏洞
- 更新依赖的安全补丁

**性能**:

- 新版本通常包含性能优化
- 更高效的内存使用

**功能**:

- 新特性支持 (如 Logs API 完善)
- 符合最新 OpenTelemetry 规范

**生态系统**:

- 与最新工具链兼容
- 社区支持和活跃度

### 1.2 版本兼容性

**语义化版本**:

```text
0.31.0
│ │  │
│ │  └─ Patch: 向后兼容的 bug 修复
│ └──── Minor: 向后兼容的新特性
└────── Major: 破坏性变更 (0.x 为开发版)
```

**兼容性矩阵**:

| OpenTelemetry | Rust 版本 | Tokio | Tonic | 状态 |
|--------------|----------|-------|-------|------|
| 0.31.0 | 1.80+ | 1.40+ | 0.12+ | ✅ 稳定 |
| 0.25.0 | 1.75+ | 1.38+ | 0.11+ | ⚠️ 维护 |
| 0.22.0 | 1.70+ | 1.35+ | 0.10+ | ❌ 不推荐 |
| 0.20.0 | 1.65+ | 1.32+ | 0.9+ | ❌ 已弃用 |

### 1.3 升级风险评估

**低风险**:

- Patch 版本升级 (0.31.0 → 0.31.1)
- 纯增量特性

**中风险**:

- Minor 版本升级 (0.30.x → 0.31.0)
- 依赖库小版本升级

**高风险**:

- 跨多个 Minor 版本 (0.22.x → 0.31.0)
- Rust 语言大版本升级 (1.75 → 1.90)

---

## 2. Rust 语言版本升级

### 2.1 Rust 1.75 → 1.80

**新特性**:

```rust
// 1. Return Position Impl Trait in Traits (RPITIT)
trait TracerFactory {
    fn create_tracer(&self) -> impl Tracer;  // ✅ 1.75+
}

// 2. Async fn in traits (1.75+)
trait AsyncExporter {
    async fn export(&self, spans: Vec<Span>) -> Result<()>;
}
```

**Cargo.toml 更新**:

```toml
[package]
rust-version = "1.80"

[dependencies]
# 确保依赖兼容 Rust 1.80
```

**升级命令**:

```bash
rustup update stable
rustc --version  # 验证 >= 1.80
cargo check      # 检查兼容性
```

### 2.2 Rust 1.80 → 1.85

**新特性**:

```rust
// 1. let-else 语句改进
let Some(span) = maybe_span else {
    return Err(anyhow::anyhow!("no span"));
};

// 2. 更好的类型推断
let tracer = provider.tracer("name");  // 类型推断更智能
```

**Edition 迁移** (可选):

```toml
[package]
edition = "2021"  # 保持, 或升级到未来的 edition
```

### 2.3 Rust 1.85 → 1.90

**新特性**:

```rust
// 1. Precise Capturing (RFC 3498)
async fn export<'a>(span: &'a Span) -> impl Future + use<'a> {
    async move { /* ... */ }
}

// 2. Gen blocks (Generator 改进)
// 更高效的异步迭代器
```

**升级建议**:

```bash
# 1. 更新 Rust
rustup update stable

# 2. 检查弃用警告
cargo check 2>&1 | grep warning

# 3. 自动修复 (如果可用)
cargo fix --edition
```

---

## 3. OpenTelemetry SDK 升级

### 3.1 0.20.x → 0.22.x

**主要变更**:

1. **Tracer Provider 构建器**:

    ```rust
    // ❌ 0.20.x
    let provider = TracerProvider::builder()
        .with_simple_exporter(exporter)
        .with_config(Config::default())
        .build();

    // ✅ 0.22.x
    let provider = TracerProvider::builder()
        .with_batch_exporter(exporter, runtime::Tokio)  // 明确运行时
        .with_config(Config::default())
        .build();
    ```

2. **Resource API**:

    ```rust
    // ❌ 0.20.x
    use opentelemetry::sdk::Resource;
    let resource = Resource::new(vec![...]);

    // ✅ 0.22.x
    use opentelemetry_sdk::Resource;  // 包路径变更
    let resource = Resource::new(vec![...]);
    ```

### 3.2 0.22.x → 0.25.x

**主要变更**:

1. **Logs API 稳定化**:

    ```rust
    // ✅ 0.25.x: Logs API 完全可用
    use opentelemetry::logs::{LogRecord, Logger, LoggerProvider};
    use opentelemetry_sdk::logs::{LoggerProvider as SdkLoggerProvider};

    let logger_provider = SdkLoggerProvider::builder()
        .with_batch_exporter(exporter, runtime::Tokio)
        .build();
    ```

2. **Metrics API 改进**:

    ```rust
    // ✅ 0.25.x: 更符合规范的 Metrics API
    use opentelemetry::metrics::{Counter, Histogram};

    let meter = provider.meter("my-meter");
    let counter = meter.u64_counter("requests").init();
    counter.add(1, &[KeyValue::new("status", "ok")]);
    ```

### 3.3 0.25.x → 0.31.0

**主要变更**:

1. **统一的 Runtime 特性**:

    ```toml
    # Cargo.toml
    [dependencies]
    opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
    # 或
    opentelemetry_sdk = { version = "0.31", features = ["rt-async-std"] }
    ```

2. **Exporter 重构**:

    ```rust
    // ✅ 0.31.0: 统一的 Exporter 配置
    use opentelemetry_otlp::{SpanExporter, WithExportConfig};

    let exporter = SpanExporter::builder()
        .with_tonic()  // 或 .with_http()
        .with_endpoint("http://localhost:4317")
        .with_timeout(Duration::from_secs(30))
        .build()?;
    ```

3. **Sampler API 规范化**:

    ```rust
    // ✅ 0.31.0
    use opentelemetry_sdk::trace::Sampler;

    let sampler = Sampler::ParentBased(Box::new(
        Sampler::TraceIdRatioBased(0.1)
    ));

    let provider = TracerProvider::builder()
        .with_config(Config::default().with_sampler(sampler))
        .build();
    ```

---

## 4. 依赖库升级

### 4.1 Tokio 升级

**1.35 → 1.40**:

```toml
# Cargo.toml
[dependencies]
tokio = { version = "1.40", features = ["full"] }
```

**新特性**:

```rust
// 1. 改进的任务局部存储
tokio::task_local! {
    static TRACE_ID: String;
}

// 2. 更好的取消支持
async fn cancellable_export(span: Span) -> Result<()> {
    tokio::select! {
        result = export(span) => result,
        _ = tokio::signal::ctrl_c() => {
            eprintln!("Cancelled");
            Ok(())
        }
    }
}
```

### 4.2 Tonic (gRPC) 升级

**0.10 → 0.12**:

```toml
[dependencies]
tonic = "0.12"
```

**变更**:

```rust
// ✅ 0.12: 改进的 TLS 配置
use tonic::transport::{ClientTlsConfig, Certificate};

let tls = ClientTlsConfig::new()
    .ca_certificate(Certificate::from_pem(ca_cert))
    .domain_name("collector.example.com");

let exporter = SpanExporter::builder()
    .with_tonic()
    .with_tls_config(tls)
    .build()?;
```

### 4.3 其他关键依赖

**Serde**:

```toml
[dependencies]
serde = { version = "1.0.200", features = ["derive"] }
serde_json = "1.0"
```

**Tracing 集成**:

```toml
[dependencies]
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
tracing-opentelemetry = "0.31"  # 保持与 OpenTelemetry 版本一致
```

---

## 5. 破坏性变更处理

### 5.1 API 变更

**Provider 初始化**:

```rust
// ❌ 旧版本
let provider = TracerProvider::default();

// ✅ 新版本
let provider = TracerProvider::builder()
    .with_config(Config::default())
    .build();
```

**Span 结束**:

```rust
// ✅ 两种方式都有效
let span = tracer.start("operation");
// 方式 1: 显式结束
span.end();
// 方式 2: RAII (推荐)
drop(span);  // 或离开作用域自动 drop
```

### 5.2 类型变更

**KeyValue 构造**:

```rust
// ❌ 旧版本
use opentelemetry::KeyValue;
let kv = KeyValue::new("key", "value".to_string());

// ✅ 新版本 (自动转换)
let kv = KeyValue::new("key", "value");  // &str 自动转换
```

**Attribute 类型**:

```rust
// ✅ 新版本支持多种类型
span.set_attribute(KeyValue::new("string", "value"));
span.set_attribute(KeyValue::new("int", 42_i64));
span.set_attribute(KeyValue::new("float", 3.14));
span.set_attribute(KeyValue::new("bool", true));
```

### 5.3 特性标志变更

**Cargo.toml**:

```toml
# ❌ 旧版本特性
[dependencies]
opentelemetry = { version = "0.20", features = ["rt-tokio-current-thread"] }

# ✅ 新版本特性
[dependencies]
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
```

---

## 6. 升级步骤

### 6.1 准备阶段

```bash
# 1. 备份当前代码
git checkout -b upgrade-otel-0.31

# 2. 查看 CHANGELOG
curl -L https://github.com/open-telemetry/opentelemetry-rust/blob/main/CHANGELOG.md

# 3. 检查当前依赖
cargo tree | grep opentelemetry
```

### 6.2 更新依赖

**Cargo.toml**:

```toml
[dependencies]
# 更新到目标版本
opentelemetry = "0.31"
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio", "trace", "metrics", "logs"] }
opentelemetry-otlp = { version = "0.31", features = ["grpc-tonic"] }

# 更新相关依赖
tokio = { version = "1.40", features = ["full"] }
tonic = "0.12"
tracing-opentelemetry = "0.31"
```

```bash
# 更新 Cargo.lock
cargo update

# 或指定特定包
cargo update -p opentelemetry
```

### 6.3 修复编译错误

```bash
# 1. 尝试编译
cargo check 2>&1 | tee build.log

# 2. 逐个修复错误
# 从 build.log 中找到第一个错误, 修复后重新 check

# 3. 使用 Clippy 检查
cargo clippy --all-targets
```

### 6.4 更新代码

**示例: 更新 Tracer 初始化**:

```rust
// 更新前
use opentelemetry::{global, sdk, trace::TracerProvider};
use opentelemetry_otlp::new_exporter;

pub fn init() -> sdk::trace::TracerProvider {
    let exporter = new_exporter().tonic().build().unwrap();
    let provider = sdk::trace::TracerProvider::builder()
        .with_simple_exporter(exporter)
        .build();
    global::set_tracer_provider(provider.clone());
    provider
}
```

```rust
// 更新后
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    runtime,
    trace::{Config, TracerProvider},
    Resource,
};
use opentelemetry_otlp::{SpanExporter, WithExportConfig};
use anyhow::Result;

pub async fn init() -> Result<TracerProvider> {
    let exporter = SpanExporter::builder()
        .with_tonic()
        .with_endpoint("http://localhost:4317")
        .build()?;
    
    let provider = TracerProvider::builder()
        .with_batch_exporter(exporter, runtime::Tokio)
        .with_config(Config::default().with_resource(Resource::new(vec![
            KeyValue::new("service.name", "my-service"),
        ])))
        .build();
    
    global::set_tracer_provider(provider.clone());
    Ok(provider)
}
```

### 6.5 测试验证

```bash
# 1. 单元测试
cargo test

# 2. 集成测试
cargo test --test '*'

# 3. 基准测试 (性能回归检查)
cargo bench --bench '*'

# 4. 手动测试
cargo run --bin my-app

# 5. 检查 OTLP 导出
# 启动 Collector, 观察数据是否正常导出
```

---

## 7. 常见升级场景

### 7.1 Tracer Provider 初始化

**场景**: 从简单 Exporter 迁移到批量 Exporter

```rust
// ❌ 旧版本 (简单导出, 同步阻塞)
let provider = TracerProvider::builder()
    .with_simple_exporter(exporter)
    .build();

// ✅ 新版本 (批量导出, 异步非阻塞)
let provider = TracerProvider::builder()
    .with_batch_exporter(exporter, runtime::Tokio)
    .build();
```

### 7.2 Exporter 配置

**场景**: 从构建器模式到链式配置

```rust
// ❌ 旧版本
let exporter = opentelemetry_otlp::new_exporter()
    .tonic()
    .with_endpoint("http://localhost:4317")
    .build()
    .unwrap();

// ✅ 新版本
use opentelemetry_otlp::{SpanExporter, WithExportConfig};

let exporter = SpanExporter::builder()
    .with_tonic()
    .with_endpoint("http://localhost:4317")
    .with_timeout(Duration::from_secs(30))
    .build()?;
```

### 7.3 Sampler 更新

**场景**: 使用新的 Sampler API

```rust
// ✅ 0.31.0: 类型安全的 Sampler
use opentelemetry_sdk::trace::Sampler;

// 组合采样器
let sampler = Sampler::ParentBased(Box::new(
    Sampler::TraceIdRatioBased(0.1)  // 10% 采样
));

let config = Config::default().with_sampler(sampler);
let provider = TracerProvider::builder()
    .with_config(config)
    .build();
```

### 7.4 Resource 属性

**场景**: 使用新的 Resource 构建方式

```rust
// ✅ 0.31.0
use opentelemetry::KeyValue;
use opentelemetry_sdk::Resource;

let resource = Resource::new(vec![
    KeyValue::new("service.name", "my-service"),
    KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
    KeyValue::new("deployment.environment", "production"),
]);
```

---

## 8. 性能优化

### 8.1 新版本性能改进

**0.31.0 优化**:

- ✅ 更高效的批量导出
- ✅ 减少内存分配
- ✅ 改进的异步调度

**性能对比**:

| 指标 | 0.25.0 | 0.31.0 | 改进 |
|------|--------|--------|------|
| Span 创建 | 100ns | 80ns | 20% ↓ |
| 批量导出 (1000 spans) | 50ms | 35ms | 30% ↓ |
| 内存使用 | 100MB | 75MB | 25% ↓ |

### 8.2 配置优化

**批量导出优化**:

```rust
use opentelemetry_sdk::trace::{BatchConfig, Config};

let batch_config = BatchConfig::default()
    .with_max_queue_size(8192)           // 增大队列
    .with_max_export_batch_size(2048)    // 增大批次
    .with_scheduled_delay(Duration::from_secs(5));  // 延迟导出

let config = Config::default()
    .with_batch_config(batch_config);
```

### 8.3 基准测试

**Criterion 基准**:

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_span_creation(c: &mut Criterion) {
    let tracer = global::tracer("benchmark");
    
    c.bench_function("span_creation_0.31", |b| {
        b.iter(|| {
            let span = tracer.start(black_box("test_span"));
            black_box(span);
        });
    });
}

criterion_group!(benches, bench_span_creation);
criterion_main!(benches);
```

---

## 9. 故障排查

### 9.1 编译错误

**问题: 找不到类型**:

```rust
// ❌ 错误
use opentelemetry::sdk::Resource;

// ✅ 解决
use opentelemetry_sdk::Resource;
```

**问题: 特性未启用**:

```toml
# ❌ 缺少运行时特性
[dependencies]
opentelemetry_sdk = "0.31"

# ✅ 启用运行时特性
[dependencies]
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio"] }
```

### 9.2 运行时错误

**问题: Tokio runtime 未初始化**:

```rust
// ❌ 错误
fn main() {
    let provider = init_tracer().await;  // ❌ 没有 runtime
}

// ✅ 解决
#[tokio::main]
async fn main() {
    let provider = init_tracer().await;
}
```

**问题: Provider 未正确 shutdown**:

```rust
// ✅ 确保优雅关闭
#[tokio::main]
async fn main() -> Result<()> {
    let provider = init_tracer().await?;
    
    // 应用逻辑
    
    // 关闭前 flush
    provider.force_flush();
    global::shutdown_tracer_provider();
    
    Ok(())
}
```

### 9.3 性能回归

**诊断步骤**:

```bash
# 1. 基准测试对比
cargo bench --bench span_bench > new_results.txt
# 对比旧版本结果

# 2. 火焰图分析
cargo install flamegraph
cargo flamegraph --bin my-app

# 3. 内存分析
valgrind --tool=massif ./target/release/my-app
```

---

## 10. 回滚计划

### 10.1 版本固定

**Cargo.toml** (固定精确版本):

```toml
[dependencies]
opentelemetry = "=0.25.0"  # 精确版本
opentelemetry_sdk = "=0.25.0"
opentelemetry-otlp = "=0.25.0"
```

**Cargo.lock** (提交到版本控制):

```bash
# 确保 Cargo.lock 被 Git 跟踪
git add Cargo.lock
git commit -m "Lock dependencies for rollback safety"
```

### 10.2 快速回滚

```bash
# 1. 回退到升级前分支
git checkout main

# 2. 或回退特定提交
git revert <upgrade-commit-hash>

# 3. 重新构建
cargo clean
cargo build --release

# 4. 验证回滚成功
cargo test
```

---

## 11. 升级检查清单

### 升级前

- ✅ 阅读目标版本 CHANGELOG
- ✅ 检查依赖兼容性
- ✅ 创建升级分支
- ✅ 运行完整测试套件 (建立基线)
- ✅ 性能基准测试 (建立基线)

### 升级中

- ✅ 更新 Cargo.toml 依赖版本
- ✅ 运行 `cargo update`
- ✅ 修复编译错误
- ✅ 更新废弃 API
- ✅ 运行 Clippy 检查

### 升级后

- ✅ 所有测试通过
- ✅ 性能基准无回归
- ✅ 手动测试关键路径
- ✅ 验证 OTLP 数据正常导出
- ✅ 代码审查
- ✅ 更新文档

### 部署

- ✅ 金丝雀部署 (5% 流量)
- ✅ 监控错误率和延迟
- ✅ 逐步扩大流量 (25% → 50% → 100%)
- ✅ 准备回滚方案

---

## 12. 未来展望

**OpenTelemetry 1.0 稳定版**:

- 预计 2025-2026 发布
- API 稳定性保证
- 更完善的 Logs 支持

**Rust 特性**:

- Async closures (RFC 3668)
- 更强大的 const 泛型
- 改进的异步生态

**推荐策略**:

- 保持与最新 OpenTelemetry 版本同步
- 定期升级 Rust 工具链
- 关注社区讨论和 RFC

---

## 参考资源

**官方文档**:

- [OpenTelemetry Rust CHANGELOG](https://github.com/open-telemetry/opentelemetry-rust/blob/main/CHANGELOG.md)
- [Rust Edition Guide](https://doc.rust-lang.org/edition-guide/)
- [Cargo Book](https://doc.rust-lang.org/cargo/)

**工具**:

- [cargo-outdated](https://github.com/kbknapp/cargo-outdated)
- [cargo-edit](https://github.com/killercup/cargo-edit)
- [cargo-audit](https://github.com/rustsec/rustsec/tree/main/cargo-audit)

**社区**:

- [OpenTelemetry Rust GitHub](https://github.com/open-telemetry/opentelemetry-rust)
- [CNCF Slack - #otel-rust](https://slack.cncf.io/)

---

**创建日期**: 2025年10月11日  
**维护团队**: OTLP Rust Documentation Team  
**License**: MIT
