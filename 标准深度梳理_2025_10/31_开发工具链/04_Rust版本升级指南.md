# 🔄 Rust OTLP 版本升级指南

> **适用版本**: OpenTelemetry Rust SDK 0.20+ → 0.31+  
> **Rust 版本**: 1.75+ → 1.90+  
> **最后更新**: 2025年10月10日

---

## 📋 目录

- [🔄 Rust OTLP 版本升级指南](#-rust-otlp-版本升级指南)
  - [📋 目录](#-目录)
  - [1. 升级概述](#1-升级概述)
    - [1.1 为什么要升级？](#11-为什么要升级)
    - [1.2 升级路径](#12-升级路径)
    - [1.3 升级风险评估](#13-升级风险评估)
  - [2. OpenTelemetry Rust SDK 版本升级](#2-opentelemetry-rust-sdk-版本升级)
    - [2.1 版本历史与重要变更](#21-版本历史与重要变更)
      - [0.20.x → 0.21.x (2023年底)](#020x--021x-2023年底)
      - [0.21.x → 0.22.x (2024年初)](#021x--022x-2024年初)
      - [0.22.x → 0.31.x (2024年中-2025年)](#022x--031x-2024年中-2025年)
    - [2.2 依赖版本对照表](#22-依赖版本对照表)
    - [2.3 Cargo.toml 升级示例](#23-cargotoml-升级示例)
  - [3. Rust 语言版本升级](#3-rust-语言版本升级)
    - [3.1 Rust 1.75 → 1.90 新特性应用](#31-rust-175--190-新特性应用)
      - [✨ 新特性 1: `async fn` in Traits (Rust 1.75+)](#-新特性-1-async-fn-in-traits-rust-175)
      - [✨ 新特性 2: `impl Trait` in return position (Rust 1.80+)](#-新特性-2-impl-trait-in-return-position-rust-180)
      - [✨ 新特性 3: Let-else statements (Rust 1.87+)](#-新特性-3-let-else-statements-rust-187)
      - [✨ 新特性 4: Generic Associated Types (GATs) (Rust 1.90+)](#-新特性-4-generic-associated-types-gats-rust-190)
    - [3.2 rust-toolchain.toml 配置](#32-rust-toolchaintoml-配置)
  - [4. 破坏性变更](#4-破坏性变更)
    - [4.1 API 变更清单](#41-api-变更清单)
      - [变更 1: TracerProvider 构建](#变更-1-tracerprovider-构建)
      - [变更 2: Context 传播](#变更-2-context-传播)
      - [变更 3: Resource 创建](#变更-3-resource-创建)
    - [4.2 导入路径变更](#42-导入路径变更)
  - [5. 迁移步骤](#5-迁移步骤)
    - [5.1 准备阶段](#51-准备阶段)
      - [Step 1: 备份与分支](#step-1-备份与分支)
      - [Step 2: 更新依赖](#step-2-更新依赖)
      - [Step 3: 检查依赖冲突](#step-3-检查依赖冲突)
    - [5.2 代码迁移](#52-代码迁移)
      - [Step 1: 批量更新导入路径](#step-1-批量更新导入路径)
      - [Step 2: 更新初始化代码](#step-2-更新初始化代码)
      - [Step 3: 更新测试代码](#step-3-更新测试代码)
    - [5.3 编译与修复](#53-编译与修复)
  - [6. 常见问题](#6-常见问题)
    - [6.1 编译错误](#61-编译错误)
      - [问题 1: 找不到 `TracerProvider`](#问题-1-找不到-tracerprovider)
      - [问题 2: 生命周期错误](#问题-2-生命周期错误)
    - [6.2 运行时错误](#62-运行时错误)
      - [问题 1: Panic on shutdown](#问题-1-panic-on-shutdown)
      - [问题 2: 数据未导出](#问题-2-数据未导出)
  - [7. 性能优化](#7-性能优化)
    - [7.1 编译性能](#71-编译性能)
    - [7.2 运行时性能](#72-运行时性能)
  - [8. 测试与验证](#8-测试与验证)
    - [8.1 单元测试](#81-单元测试)
    - [8.2 集成测试](#82-集成测试)
    - [8.3 性能测试](#83-性能测试)
  - [🔗 参考资源](#-参考资源)

---

## 1. 升级概述

### 1.1 为什么要升级？

| 升级理由 | 说明 |
|---------|------|
| **新特性** | 新的 API、改进的性能、更好的类型安全 |
| **Bug 修复** | 关键 Bug 修复、安全漏洞补丁 |
| **生态兼容** | 与最新 Tokio、Tonic 等库保持兼容 |
| **标准合规** | 遵循最新 OpenTelemetry 规范 |
| **性能提升** | 利用最新 Rust 编译器优化 |

### 1.2 升级路径

```text
OpenTelemetry Rust SDK:
0.20.x → 0.21.x → 0.22.x → 0.23.x → 0.31.x (当前)

Rust 语言:
1.75.x → 1.80.x → 1.85.x → 1.90.x (当前)

推荐策略:
- 小版本升级: 直接升级
- 大版本升级: 分步升级，逐步测试
```

### 1.3 升级风险评估

| 风险等级 | 升级类型 | 应对策略 |
|---------|---------|---------|
| 🟢 低 | 补丁版本 (0.31.0 → 0.31.1) | 直接升级 |
| 🟡 中 | 小版本 (0.30.x → 0.31.x) | 测试后升级 |
| 🔴 高 | 大版本 (0.20.x → 0.31.x) | 分步升级 + 完整测试 |

---

## 2. OpenTelemetry Rust SDK 版本升级

### 2.1 版本历史与重要变更

#### 0.20.x → 0.21.x (2023年底)

**主要变更**:

- Context API 重构
- `TracerProvider` 构建器模式改进

```rust
// ❌ 旧版本 (0.20.x)
let tracer_provider = TracerProvider::builder()
    .with_simple_exporter(exporter)
    .with_config(config)
    .build();

// ✅ 新版本 (0.21.x)
let tracer_provider = TracerProvider::builder()
    .with_batch_exporter(exporter, runtime::Tokio)
    .with_config(config)
    .build();
```

#### 0.21.x → 0.22.x (2024年初)

**主要变更**:

- Resource API 改进
- 导出器配置统一

```rust
// ❌ 旧版本 (0.21.x)
use opentelemetry_otlp::TonicExporterBuilder;

let exporter = TonicExporterBuilder::default()
    .with_endpoint("http://localhost:4317")
    .build_span_exporter()?;

// ✅ 新版本 (0.22.x)
let exporter = opentelemetry_otlp::new_exporter()
    .tonic()
    .with_endpoint("http://localhost:4317")
    .build_span_exporter()?;
```

#### 0.22.x → 0.31.x (2024年中-2025年)

**主要变更**:

- 完整的 Logs 支持
- Metrics SDK 稳定
- 异步运行时统一

```rust
// ✅ 0.31.x 完整示例
use opentelemetry::global;
use opentelemetry_sdk::{
    trace::{TracerProvider, Config},
    logs::LoggerProvider,
    metrics::MeterProvider,
    Resource,
};

fn init_telemetry() -> Result<(), Box<dyn std::error::Error>> {
    let resource = Resource::new(vec![
        KeyValue::new("service.name", "my-service"),
    ]);
    
    // Traces
    let tracer_provider = TracerProvider::builder()
        .with_config(Config::default().with_resource(resource.clone()))
        .with_batch_exporter(
            opentelemetry_otlp::new_exporter().tonic(),
            opentelemetry_sdk::runtime::Tokio,
        )
        .build();
    
    global::set_tracer_provider(tracer_provider);
    
    // Logs (新增)
    let logger_provider = LoggerProvider::builder()
        .with_resource(resource.clone())
        .with_batch_exporter(
            opentelemetry_otlp::new_exporter().tonic(),
            opentelemetry_sdk::runtime::Tokio,
        )
        .build();
    
    global::set_logger_provider(logger_provider);
    
    // Metrics
    let meter_provider = MeterProvider::builder()
        .with_resource(resource)
        .with_reader(
            opentelemetry_sdk::metrics::PeriodicReader::builder(
                opentelemetry_otlp::new_exporter().tonic(),
                opentelemetry_sdk::runtime::Tokio,
            )
            .build()
        )
        .build();
    
    global::set_meter_provider(meter_provider);
    
    Ok(())
}
```

### 2.2 依赖版本对照表

| SDK 版本 | Rust 最低版本 | Tokio 版本 | Tonic 版本 |
|---------|--------------|-----------|-----------|
| 0.20.x | 1.65+ | 1.28+ | 0.9+ |
| 0.21.x | 1.70+ | 1.32+ | 0.10+ |
| 0.22.x | 1.75+ | 1.35+ | 0.11+ |
| 0.31.x | 1.75+ | 1.38+ | 0.12+ |

### 2.3 Cargo.toml 升级示例

```toml
# ❌ 旧版本 (0.20.x)
[dependencies]
opentelemetry = "0.20"
opentelemetry-otlp = "0.13"
opentelemetry-jaeger = "0.19"
tokio = { version = "1.28", features = ["full"] }

# ✅ 新版本 (0.31.x)
[dependencies]
opentelemetry = "0.31.0"
opentelemetry-otlp = { version = "0.31.0", features = ["tonic", "metrics", "logs"] }
opentelemetry_sdk = "0.31.0"
tokio = { version = "1.38", features = ["full"] }
tracing = "0.1"
tracing-opentelemetry = "0.31.0"
```

---

## 3. Rust 语言版本升级

### 3.1 Rust 1.75 → 1.90 新特性应用

#### ✨ 新特性 1: `async fn` in Traits (Rust 1.75+)

```rust
// ✅ 1.75+ 可以直接在 trait 中使用 async fn
pub trait Exporter {
    async fn export(&self, spans: Vec<SpanData>) -> Result<(), Error>;
}

// 实现
pub struct MyExporter;

impl Exporter for MyExporter {
    async fn export(&self, spans: Vec<SpanData>) -> Result<(), Error> {
        // 异步导出逻辑
        Ok(())
    }
}
```

#### ✨ 新特性 2: `impl Trait` in return position (Rust 1.80+)

```rust
// ✅ 简化返回类型
pub fn create_tracer() -> impl Tracer {
    opentelemetry::global::tracer("my-service")
}

// ✅ 异步函数返回简化
pub async fn get_spans() -> impl Iterator<Item = SpanData> {
    // 返回 Span 迭代器
    std::iter::empty()
}
```

#### ✨ 新特性 3: Let-else statements (Rust 1.87+)

```rust
use opentelemetry::trace::{Span, SpanKind};

pub fn process_span(span_data: Option<SpanData>) -> Result<(), Error> {
    // ✅ 使用 let-else 简化错误处理
    let Some(span) = span_data else {
        return Err(Error::MissingSpan);
    };
    
    let SpanKind::Server = span.kind else {
        return Err(Error::InvalidSpanKind);
    };
    
    // 处理 Span
    Ok(())
}
```

#### ✨ 新特性 4: Generic Associated Types (GATs) (Rust 1.90+)

```rust
// ✅ 使用 GAT 提升类型安全
pub trait SpanProcessor {
    type Output<'a>: Iterator<Item = &'a SpanData>
    where
        Self: 'a;
    
    fn process<'a>(&'a self, spans: &'a [SpanData]) -> Self::Output<'a>;
}
```

### 3.2 rust-toolchain.toml 配置

```toml
# 项目根目录: rust-toolchain.toml

[toolchain]
channel = "1.90.0"
components = ["rustfmt", "clippy"]
targets = ["x86_64-unknown-linux-gnu", "wasm32-unknown-unknown"]
profile = "minimal"
```

---

## 4. 破坏性变更

### 4.1 API 变更清单

#### 变更 1: TracerProvider 构建

```rust
// ❌ 0.20.x
use opentelemetry::sdk::trace::TracerProvider;

let provider = TracerProvider::builder()
    .with_simple_exporter(exporter)
    .build();

// ✅ 0.31.x
use opentelemetry_sdk::trace::TracerProvider;

let provider = TracerProvider::builder()
    .with_batch_exporter(exporter, opentelemetry_sdk::runtime::Tokio)
    .build();
```

#### 变更 2: Context 传播

```rust
// ❌ 0.20.x
use opentelemetry::Context;

let cx = Context::current();
let span = tracer.start_with_context("operation", &cx);

// ✅ 0.31.x
use opentelemetry::Context;

let cx = Context::current();
let span = tracer.start_with_context("operation", cx);
```

#### 变更 3: Resource 创建

```rust
// ❌ 0.20.x
use opentelemetry::sdk::Resource;

let resource = Resource::new(vec![
    KeyValue::new("service.name", "my-service"),
]);

// ✅ 0.31.x
use opentelemetry_sdk::Resource;

let resource = Resource::new(vec![
    KeyValue::new("service.name", "my-service"),
]);
```

### 4.2 导入路径变更

```rust
// ❌ 旧导入路径
use opentelemetry::sdk::trace::TracerProvider;
use opentelemetry::sdk::Resource;
use opentelemetry::runtime::Tokio;

// ✅ 新导入路径
use opentelemetry_sdk::trace::TracerProvider;
use opentelemetry_sdk::Resource;
use opentelemetry_sdk::runtime::Tokio;
```

---

## 5. 迁移步骤

### 5.1 准备阶段

#### Step 1: 备份与分支

```bash
# 创建升级分支
git checkout -b upgrade/otlp-0.31

# 备份当前 Cargo.lock
cp Cargo.lock Cargo.lock.backup
```

#### Step 2: 更新依赖

```bash
# 更新到最新版本
cargo update

# 或指定版本
cargo update -p opentelemetry --precise 0.31.0
cargo update -p opentelemetry-otlp --precise 0.31.0
```

#### Step 3: 检查依赖冲突

```bash
# 检查依赖树
cargo tree | grep opentelemetry

# 检查重复依赖
cargo tree -d
```

### 5.2 代码迁移

#### Step 1: 批量更新导入路径

```bash
# 使用 sed 批量替换（Linux/macOS）
find src -name "*.rs" -exec sed -i 's/opentelemetry::sdk/opentelemetry_sdk/g' {} +

# 或使用 ripgrep + sed
rg "use opentelemetry::sdk" -l | xargs sed -i 's/opentelemetry::sdk/opentelemetry_sdk/g'
```

#### Step 2: 更新初始化代码

```rust
// 创建迁移辅助函数
pub mod migration {
    use opentelemetry_sdk::{
        trace::TracerProvider,
        Resource,
    };
    use opentelemetry::KeyValue;
    
    pub fn create_tracer_provider() -> TracerProvider {
        let resource = Resource::new(vec![
            KeyValue::new("service.name", env!("CARGO_PKG_NAME")),
            KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        ]);
        
        TracerProvider::builder()
            .with_config(
                opentelemetry_sdk::trace::Config::default()
                    .with_resource(resource)
            )
            .with_batch_exporter(
                opentelemetry_otlp::new_exporter().tonic(),
                opentelemetry_sdk::runtime::Tokio,
            )
            .build()
    }
}
```

#### Step 3: 更新测试代码

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use opentelemetry_sdk::testing::trace::NoopSpanExporter;
    
    #[tokio::test]
    async fn test_tracer_setup() {
        let provider = TracerProvider::builder()
            .with_simple_exporter(NoopSpanExporter::new())
            .build();
        
        let tracer = provider.tracer("test");
        let span = tracer.start("test-span");
        
        assert!(!span.span_context().is_valid());
    }
}
```

### 5.3 编译与修复

```bash
# 清理构建缓存
cargo clean

# 编译并查看错误
cargo build 2>&1 | tee build-errors.log

# 逐个修复错误
cargo fix --edition --allow-dirty

# 检查 Clippy 警告
cargo clippy --all-targets --all-features
```

---

## 6. 常见问题

### 6.1 编译错误

#### 问题 1: 找不到 `TracerProvider`

```rust
error[E0432]: unresolved import `opentelemetry::sdk::trace::TracerProvider`
```

**解决方案**:

```rust
// ❌ 错误
use opentelemetry::sdk::trace::TracerProvider;

// ✅ 正确
use opentelemetry_sdk::trace::TracerProvider;
```

#### 问题 2: 生命周期错误

```rust
error[E0597]: `exporter` does not live long enough
```

**解决方案**:

```rust
// ✅ 使用 'static 生命周期
let exporter: Box<dyn SpanExporter + Send + Sync + 'static> = 
    Box::new(opentelemetry_otlp::new_exporter().tonic());
```

### 6.2 运行时错误

#### 问题 1: Panic on shutdown

```text
thread 'main' panicked at 'failed to shutdown tracer provider'
```

**解决方案**:

```rust
// ✅ 正确的关闭顺序
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let tracer_provider = init_tracer()?;
    
    // 应用逻辑
    run_app().await?;
    
    // 显式关闭（使用 owned provider）
    tracer_provider.shutdown()?;
    
    // 或使用全局
    opentelemetry::global::shutdown_tracer_provider();
    
    Ok(())
}
```

#### 问题 2: 数据未导出

**排查步骤**:

```rust
// ✅ 添加日志调试
use tracing::{debug, info};

let provider = TracerProvider::builder()
    .with_batch_exporter(exporter, runtime::Tokio)
    .build();

info!("TracerProvider initialized");

// 创建 Span
let span = tracer.start("test");
debug!("Span created: {:?}", span.span_context());

// 确保 shutdown
provider.shutdown()?;
info!("TracerProvider shutdown");
```

---

## 7. 性能优化

### 7.1 编译性能

```toml
# Cargo.toml - 优化编译速度

[profile.dev]
opt-level = 1  # 轻度优化，加快运行速度

[profile.dev.package."*"]
opt-level = 2  # 依赖包优化

# 使用 mold/lld 链接器
[target.x86_64-unknown-linux-gnu]
linker = "clang"
rustflags = ["-C", "link-arg=-fuse-ld=mold"]
```

### 7.2 运行时性能

```rust
// ✅ 使用批量处理
use opentelemetry_sdk::trace::BatchConfig;
use std::time::Duration;

let batch_config = BatchConfig::default()
    .with_max_queue_size(2048)
    .with_max_export_batch_size(512)
    .with_scheduled_delay(Duration::from_secs(5))
    .with_max_export_timeout(Duration::from_secs(30));

let provider = TracerProvider::builder()
    .with_batch_exporter(exporter, runtime::Tokio)
    .with_config(
        Config::default()
            .with_max_events_per_span(128)
            .with_max_attributes_per_span(128)
    )
    .build();
```

---

## 8. 测试与验证

### 8.1 单元测试

```rust
#[cfg(test)]
mod upgrade_tests {
    use super::*;
    use opentelemetry_sdk::testing::trace::InMemorySpanExporter;
    
    #[tokio::test]
    async fn test_new_api() {
        let exporter = InMemorySpanExporter::default();
        let provider = TracerProvider::builder()
            .with_simple_exporter(exporter.clone())
            .build();
        
        let tracer = provider.tracer("test");
        let span = tracer.start("test-span");
        drop(span);
        
        provider.force_flush();
        
        let spans = exporter.get_finished_spans().unwrap();
        assert_eq!(spans.len(), 1);
        assert_eq!(spans[0].name, "test-span");
    }
}
```

### 8.2 集成测试

```rust
// tests/integration_test.rs
use opentelemetry::trace::{Tracer, TracerProvider as _};

#[tokio::test]
async fn test_full_stack() {
    // 初始化
    let provider = create_test_provider();
    let tracer = provider.tracer("integration-test");
    
    // 创建 Span
    let span = tracer.start("test-operation");
    
    // 模拟操作
    tokio::time::sleep(std::time::Duration::from_millis(10)).await;
    
    drop(span);
    provider.shutdown().unwrap();
}
```

### 8.3 性能测试

```rust
// benches/upgrade_benchmark.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_span_creation(c: &mut Criterion) {
    let provider = create_tracer_provider();
    let tracer = provider.tracer("bench");
    
    c.bench_function("span_creation_0.31", |b| {
        b.iter(|| {
            let span = tracer.start("bench-span");
            black_box(span);
        });
    });
}

criterion_group!(benches, bench_span_creation);
criterion_main!(benches);
```

---

## 🔗 参考资源

- [OpenTelemetry Rust Changelog](https://github.com/open-telemetry/opentelemetry-rust/blob/main/CHANGELOG.md)
- [Rust Release Notes](https://github.com/rust-lang/rust/blob/master/RELEASES.md)
- [Migration Guide (官方)](https://opentelemetry.io/docs/languages/rust/)
- [Rust OTLP 快速入门](../33_教程与示例/01_Rust_OTLP_30分钟快速入门.md)

---

**文档版本**: v1.0  
**创建日期**: 2025年10月10日  
**维护者**: OTLP Rust 文档团队

---

[🏠 返回主目录](../README.md) | [🔧 开发工具链](./README.md) | [📚 迁移指南](./03_从其他语言迁移到Rust_OTLP指南.md)
