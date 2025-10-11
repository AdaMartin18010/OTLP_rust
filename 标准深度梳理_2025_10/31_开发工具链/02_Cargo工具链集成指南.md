# 🔧 Cargo 工具链集成指南 - OTLP 专用

> **目标读者**: Rust OTLP 开发者  
> **Rust 版本**: 1.90+  
> **Cargo 版本**: 1.90+  
> **最后更新**: 2025年10月10日

---

## 📋 目录

- [🔧 Cargo 工具链集成指南 - OTLP 专用](#-cargo-工具链集成指南---otlp-专用)
  - [📋 目录](#-目录)
  - [1. 核心 Cargo 工具](#1-核心-cargo-工具)
    - [1.1 cargo-edit - 依赖管理](#11-cargo-edit---依赖管理)
      - [安装](#安装)
      - [使用](#使用)
      - [OTLP 项目常用命令](#otlp-项目常用命令)
    - [1.2 cargo-watch - 自动重编译](#12-cargo-watch---自动重编译)
      - [1.2.1 安装](#121-安装)
      - [1.2.2 使用](#122-使用)
      - [OTLP 开发工作流](#otlp-开发工作流)
    - [1.3 cargo-expand - 宏展开](#13-cargo-expand---宏展开)
      - [1.3.1 安装](#131-安装)
      - [1.3.2 使用](#132-使用)
      - [OTLP 宏调试](#otlp-宏调试)
  - [2. OTLP 性能分析工具](#2-otlp-性能分析工具)
    - [2.1 cargo-flamegraph - 火焰图](#21-cargo-flamegraph---火焰图)
      - [2.1.1 安装](#211-安装)
      - [2.1.2 使用](#212-使用)
      - [OTLP 性能分析示例](#otlp-性能分析示例)
    - [2.2 cargo-instruments (macOS) - Profiling](#22-cargo-instruments-macos---profiling)
      - [2.2.1 安装](#221-安装)
      - [2.2.2 使用](#222-使用)
      - [OTLP 示例](#otlp-示例)
    - [2.3 cargo-criterion - 基准测试](#23-cargo-criterion---基准测试)
      - [配置 Criterion](#配置-criterion)
      - [运行基准测试](#运行基准测试)
  - [3. 代码质量工具](#3-代码质量工具)
    - [3.1 cargo-clippy - Lint 检查](#31-cargo-clippy---lint-检查)
      - [3.1.1 使用](#311-使用)
      - [OTLP 专用 Clippy 配置](#otlp-专用-clippy-配置)
    - [3.2 cargo-fmt - 代码格式化](#32-cargo-fmt---代码格式化)
      - [3.2.1 使用](#321-使用)
      - [OTLP 项目 rustfmt 配置](#otlp-项目-rustfmt-配置)
    - [3.3 cargo-deny - 依赖审核](#33-cargo-deny---依赖审核)
      - [3.3.1 安装](#331-安装)
      - [3.3.2 配置](#332-配置)
      - [3.3.3 使用](#333-使用)
  - [4. 测试与覆盖率](#4-测试与覆盖率)
    - [4.1 cargo-nextest - 快速测试](#41-cargo-nextest---快速测试)
      - [4.1.1 安装](#411-安装)
      - [4.1.2 使用](#412-使用)
      - [4.1.3 OTLP 集成测试](#413-otlp-集成测试)
    - [4.2 cargo-llvm-cov - 代码覆盖率](#42-cargo-llvm-cov---代码覆盖率)
      - [4.2.1 安装](#421-安装)
      - [4.2.2 使用](#422-使用)
    - [4.3 cargo-tarpaulin - 覆盖率报告](#43-cargo-tarpaulin---覆盖率报告)
      - [4.3.1 安装](#431-安装)
      - [4.3.2 使用](#432-使用)
  - [5. 安全与审计](#5-安全与审计)
    - [5.1 cargo-audit - 漏洞扫描](#51-cargo-audit---漏洞扫描)
      - [5.1.1 安装](#511-安装)
      - [5.1.2 使用](#512-使用)
      - [5.1.3 CI 集成](#513-ci-集成)
    - [5.2 cargo-outdated - 依赖更新](#52-cargo-outdated---依赖更新)
      - [5.2.1 安装](#521-安装)
      - [5.2.2 使用](#522-使用)
    - [5.3 cargo-udeps - 未使用依赖](#53-cargo-udeps---未使用依赖)
      - [5.3.1 安装](#531-安装)
      - [5.3.2 使用](#532-使用)
  - [6. 构建与发布](#6-构建与发布)
    - [6.1 cargo-make - 任务自动化](#61-cargo-make---任务自动化)
      - [6.1.1 安装](#611-安装)
      - [6.1.2 配置](#612-配置)
      - [6.1.3 使用](#613-使用)
    - [6.2 cargo-release - 版本发布](#62-cargo-release---版本发布)
      - [6.2.1 安装](#621-安装)
      - [6.2.2 使用](#622-使用)
      - [配置](#配置)
    - [6.3 cross - 交叉编译](#63-cross---交叉编译)
      - [6.3.1 安装](#631-安装)
      - [6.3.2 使用](#632-使用)
  - [7. OTLP 专用集成](#7-otlp-专用集成)
    - [7.1 自定义 Cargo 命令 - otlp-trace](#71-自定义-cargo-命令---otlp-trace)
      - [7.2 使用](#72-使用)
    - [7.2 OTLP 基准测试模板](#72-otlp-基准测试模板)
    - [7.3 OTLP 构建脚本](#73-otlp-构建脚本)
  - [8. 完整 Makefile / Justfile](#8-完整-makefile--justfile)
    - [8.1 Makefile](#81-makefile)
    - [8.2 Justfile (推荐)](#82-justfile-推荐)
      - [使用 Just](#使用-just)
  - [9. CI/CD 集成](#9-cicd-集成)
    - [9.1 GitHub Actions](#91-github-actions)
    - [9.2 GitLab CI](#92-gitlab-ci)
  - [10. 最佳实践](#10-最佳实践)
    - [10.1 开发工作流](#101-开发工作流)
    - [10.2 性能优化工作流](#102-性能优化工作流)
    - [10.3 发布工作流](#103-发布工作流)
  - [🔗 参考资源](#-参考资源)

---

## 1. 核心 Cargo 工具

### 1.1 cargo-edit - 依赖管理

#### 安装

```bash
cargo install cargo-edit
```

#### 使用

```bash
# 添加依赖
cargo add opentelemetry
cargo add opentelemetry-otlp
cargo add tokio --features full

# 添加开发依赖
cargo add --dev criterion --features html_reports
cargo add --dev mockall

# 升级依赖到最新版本
cargo upgrade

# 指定版本
cargo add serde --vers "1.0.200"

# 添加 Git 依赖
cargo add my_crate --git https://github.com/user/repo

# 移除依赖
cargo rm some_crate
```

#### OTLP 项目常用命令

```bash
# 快速初始化 OTLP 项目依赖
cargo add opentelemetry@0.31.0
cargo add opentelemetry-otlp@0.31.0
cargo add opentelemetry-sdk@0.31.0
cargo add tokio --features full
cargo add tracing@0.1
cargo add tracing-opentelemetry
cargo add tracing-subscriber --features env-filter

# 添加测试依赖
cargo add --dev criterion --features html_reports
cargo add --dev wiremock
cargo add --dev testcontainers
```

---

### 1.2 cargo-watch - 自动重编译

#### 1.2.1 安装

```bash
cargo install cargo-watch
```

#### 1.2.2 使用

```bash
# 监视文件变化并运行
cargo watch -x run

# 监视并运行测试
cargo watch -x test

# 链式命令（先检查，再测试，最后运行）
cargo watch -x check -x test -x run

# 只监视特定文件
cargo watch -w src -x test

# 清屏后执行
cargo watch -c -x run

# 忽略特定文件
cargo watch -i docs/ -x test

# 监视并运行 clippy
cargo watch -x clippy
```

#### OTLP 开发工作流

```bash
# 完整的开发工作流
cargo watch -c -x check -x "test --lib" -x "run --example basic_trace"

# 监视并运行 OTLP 集成测试
cargo watch -x "test --test integration_test -- --nocapture"
```

---

### 1.3 cargo-expand - 宏展开

#### 1.3.1 安装

```bash
cargo install cargo-expand
```

#### 1.3.2 使用

```bash
# 展开所有宏
cargo expand

# 展开特定模块
cargo expand module::path

# 展开特定 item
cargo expand my_function

# 彩色输出
cargo expand --color=always | less -R
```

#### OTLP 宏调试

```rust
// src/lib.rs
use opentelemetry::trace::{Tracer, TracerProvider};

#[tracing::instrument]
async fn traced_function(user_id: u64) -> Result<(), Box<dyn std::error::Error>> {
    // 实现
    Ok(())
}
```

```bash
# 查看 #[tracing::instrument] 宏展开后的代码
cargo expand traced_function
```

---

## 2. OTLP 性能分析工具

### 2.1 cargo-flamegraph - 火焰图

#### 2.1.1 安装

```bash
cargo install flamegraph

# Linux 需要 perf
sudo apt-get install linux-tools-common linux-tools-generic linux-tools-`uname -r`

# macOS 使用 DTrace (无需额外安装)
```

#### 2.1.2 使用

```bash
# 生成火焰图
cargo flamegraph

# 指定二进制
cargo flamegraph --bin my_binary

# 指定测试
cargo flamegraph --test my_test

# 带参数运行
cargo flamegraph -- --some-arg value

# 生成反向火焰图（适合分析内存分配）
cargo flamegraph --reverse
```

#### OTLP 性能分析示例

```bash
# 分析 OTLP 导出性能
cargo flamegraph --example otlp_export -- --count 10000

# 分析 Span 创建性能
cargo flamegraph --bench span_creation

# 生成 SVG 并打开
cargo flamegraph && open flamegraph.svg
```

**分析 OTLP 热点**:

```rust
// examples/otlp_export.rs
use opentelemetry::trace::{Tracer, TracerProvider};
use opentelemetry_sdk::trace::TracerProvider as SdkTracerProvider;

fn main() {
    let provider = SdkTracerProvider::builder().build();
    let tracer = provider.tracer("benchmark");

    // 模拟高负载
    for i in 0..100_000 {
        let span = tracer.start(&format!("operation-{}", i));
        drop(span); // 立即结束
    }
}
```

```bash
cargo flamegraph --example otlp_export
```

---

### 2.2 cargo-instruments (macOS) - Profiling

#### 2.2.1 安装

```bash
cargo install cargo-instruments

# 需要 Xcode Command Line Tools
xcode-select --install
```

#### 2.2.2 使用

```bash
# 时间分析
cargo instruments -t time

# 内存分配分析
cargo instruments -t alloc

# 系统调用分析
cargo instruments -t sys

# 线程分析
cargo instruments -t threads

# 自定义模板
cargo instruments -t /path/to/template.tracetemplate
```

#### OTLP 示例

```bash
# 分析 OTLP 批处理性能
cargo instruments -t time --example batch_exporter

# 分析内存使用
cargo instruments -t alloc --bin otlp_server --release
```

---

### 2.3 cargo-criterion - 基准测试

#### 配置 Criterion

**Cargo.toml**:

```toml
[dev-dependencies]
criterion = { version = "0.5", features = ["html_reports"] }

[[bench]]
name = "otlp_benchmark"
harness = false
```

**benches/otlp_benchmark.rs**:

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use opentelemetry::trace::{Tracer, TracerProvider};
use opentelemetry_sdk::trace::TracerProvider as SdkTracerProvider;

fn span_creation_benchmark(c: &mut Criterion) {
    let provider = SdkTracerProvider::builder().build();
    let tracer = provider.tracer("benchmark");

    c.bench_function("span_creation", |b| {
        b.iter(|| {
            let span = tracer.start(black_box("test-operation"));
            drop(span);
        });
    });
}

fn batch_export_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("batch_export");
    
    for batch_size in [10, 100, 1000, 10000].iter() {
        group.bench_with_input(
            BenchmarkId::from_parameter(batch_size),
            batch_size,
            |b, &size| {
                b.iter(|| {
                    // 模拟批量导出
                    (0..size).for_each(|_| {
                        black_box(create_span());
                    });
                });
            },
        );
    }
    group.finish();
}

fn create_span() {
    // Span 创建逻辑
}

criterion_group!(benches, span_creation_benchmark, batch_export_benchmark);
criterion_main!(benches);
```

#### 运行基准测试

```bash
# 运行所有基准测试
cargo bench

# 运行特定基准测试
cargo bench span_creation

# 保存基线
cargo bench -- --save-baseline master

# 对比基线
cargo bench -- --baseline master

# 生成 HTML 报告
cargo bench
# 报告位于: target/criterion/report/index.html
```

---

## 3. 代码质量工具

### 3.1 cargo-clippy - Lint 检查

#### 3.1.1 使用

```bash
# 基本检查
cargo clippy

# 所有 targets 和 features
cargo clippy --all-targets --all-features

# 自动修复
cargo clippy --fix

# 严格模式（CI 推荐）
cargo clippy -- -D warnings

# 特定 Lint 规则
cargo clippy -- -W clippy::pedantic -W clippy::nursery
```

#### OTLP 专用 Clippy 配置

**.clippy.toml**:

```toml
# 认知复杂度阈值
cognitive-complexity-threshold = 30

# 类型复杂度阈值
type-complexity-threshold = 250

# 函数参数数量阈值
too-many-arguments-threshold = 7

# 函数行数阈值
too-many-lines-threshold = 300
```

**lib.rs 顶部配置**:

```rust
#![warn(
    missing_docs,
    missing_debug_implementations,
    rust_2018_idioms,
    unreachable_pub,
    clippy::all,
    clippy::pedantic,
)]
#![allow(clippy::module_name_repetitions)]
#![allow(clippy::too_many_arguments)] // OTLP API 常需要多参数
```

---

### 3.2 cargo-fmt - 代码格式化

#### 3.2.1 使用

```bash
# 格式化整个项目
cargo fmt

# 检查格式（CI 使用）
cargo fmt -- --check

# 格式化特定文件
cargo fmt -- src/main.rs
```

#### OTLP 项目 rustfmt 配置

**rustfmt.toml**:

```toml
edition = "2021"
max_width = 100
hard_tabs = false
tab_spaces = 4

# 导入整理
imports_granularity = "Crate"
group_imports = "StdExternalCrate"
reorder_imports = true

# 格式化选项
fn_single_line = false
where_single_line = true
force_explicit_abi = true
format_code_in_doc_comments = true
normalize_comments = true
wrap_comments = true
comment_width = 80

# 链式调用
chain_width = 80
```

---

### 3.3 cargo-deny - 依赖审核

#### 3.3.1 安装

```bash
cargo install cargo-deny
```

#### 3.3.2 配置

**deny.toml**:

```toml
[advisories]
db-path = "~/.cargo/advisory-db"
db-urls = ["https://github.com/rustsec/advisory-db"]
vulnerability = "deny"
unmaintained = "warn"
yanked = "deny"
notice = "warn"

[licenses]
unlicensed = "deny"
allow = [
    "MIT",
    "Apache-2.0",
    "BSD-3-Clause",
]
deny = [
    "GPL-3.0",
]

[bans]
multiple-versions = "warn"
wildcards = "allow"
highlight = "all"

[sources]
unknown-registry = "deny"
unknown-git = "deny"
allow-git = []
```

#### 3.3.3 使用

```bash
# 检查所有规则
cargo deny check

# 只检查许可证
cargo deny check licenses

# 只检查安全漏洞
cargo deny check advisories

# 只检查禁止的依赖
cargo deny check bans
```

---

## 4. 测试与覆盖率

### 4.1 cargo-nextest - 快速测试

#### 4.1.1 安装

```bash
cargo install cargo-nextest
```

#### 4.1.2 使用

```bash
# 运行所有测试
cargo nextest run

# 并行度控制
cargo nextest run -j 8

# 失败时立即停止
cargo nextest run --fail-fast

# 只运行失败的测试
cargo nextest run --failed

# 重试失败的测试
cargo nextest run --retries 3

# 显示详细输出
cargo nextest run --nocapture
```

#### 4.1.3 OTLP 集成测试

```bash
# 运行 OTLP 集成测试
cargo nextest run --test integration_test

# 运行特定测试
cargo nextest run test_span_export

# 显示测试时间
cargo nextest run --verbose
```

---

### 4.2 cargo-llvm-cov - 代码覆盖率

#### 4.2.1 安装

```bash
cargo install cargo-llvm-cov
rustup component add llvm-tools-preview
```

#### 4.2.2 使用

```bash
# 生成覆盖率报告
cargo llvm-cov

# HTML 报告
cargo llvm-cov --html
# 打开: target/llvm-cov/html/index.html

# Lcov 格式（适合 CI）
cargo llvm-cov --lcov --output-path lcov.info

# 只测试库
cargo llvm-cov --lib

# 包含集成测试
cargo llvm-cov --all-targets

# 排除特定文件
cargo llvm-cov --ignore-filename-regex "tests/"
```

---

### 4.3 cargo-tarpaulin - 覆盖率报告

#### 4.3.1 安装

```bash
cargo install cargo-tarpaulin
```

#### 4.3.2 使用

```bash
# 生成覆盖率
cargo tarpaulin

# 输出到 Codecov
cargo tarpaulin --out Xml

# HTML 报告
cargo tarpaulin --out Html

# 忽略测试文件
cargo tarpaulin --ignore-tests
```

---

## 5. 安全与审计

### 5.1 cargo-audit - 漏洞扫描

#### 5.1.1 安装

```bash
cargo install cargo-audit
```

#### 5.1.2 使用

```bash
# 扫描漏洞
cargo audit

# 更新漏洞数据库
cargo audit fetch

# JSON 输出
cargo audit --json

# 只显示高危漏洞
cargo audit --deny warnings
```

#### 5.1.3 CI 集成

```yaml
# .github/workflows/audit.yml
name: Security Audit
on:
  schedule:
    - cron: '0 0 * * *'
jobs:
  audit:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - uses: actions-rs/audit-check@v1
        with:
          token: ${{ secrets.GITHUB_TOKEN }}
```

---

### 5.2 cargo-outdated - 依赖更新

#### 5.2.1 安装

```bash
cargo install cargo-outdated
```

#### 5.2.2 使用

```bash
# 检查过期依赖
cargo outdated

# 显示详细信息
cargo outdated -v

# 只显示根依赖
cargo outdated --root-deps-only

# 检查特定依赖
cargo outdated opentelemetry
```

---

### 5.3 cargo-udeps - 未使用依赖

#### 5.3.1 安装

```bash
cargo install cargo-udeps --locked
```

#### 5.3.2 使用

```bash
# 检查未使用依赖（需要 nightly）
cargo +nightly udeps

# 检查所有 targets
cargo +nightly udeps --all-targets
```

---

## 6. 构建与发布

### 6.1 cargo-make - 任务自动化

#### 6.1.1 安装

```bash
cargo install cargo-make
```

#### 6.1.2 配置

**Makefile.toml**:

```toml
[tasks.dev]
description = "开发环境运行"
command = "cargo"
args = ["watch", "-x", "check", "-x", "test", "-x", "run"]

[tasks.lint]
description = "代码检查"
script = [
    "cargo fmt -- --check",
    "cargo clippy -- -D warnings",
]

[tasks.test-all]
description = "运行所有测试"
script = [
    "cargo test --lib",
    "cargo test --bins",
    "cargo test --tests",
]

[tasks.bench]
description = "运行基准测试"
command = "cargo"
args = ["bench", "--", "--save-baseline", "current"]

[tasks.security]
description = "安全检查"
script = [
    "cargo audit",
    "cargo deny check",
]

[tasks.coverage]
description = "生成覆盖率"
command = "cargo"
args = ["llvm-cov", "--html"]

[tasks.ci]
description = "CI 完整检查"
dependencies = ["lint", "test-all", "security"]

[tasks.release]
description = "发布流程"
script = [
    "cargo test --release",
    "cargo build --release",
    "cargo publish --dry-run",
]
```

#### 6.1.3 使用

```bash
# 运行任务
cargo make dev
cargo make lint
cargo make ci
cargo make release
```

---

### 6.2 cargo-release - 版本发布

#### 6.2.1 安装

```bash
cargo install cargo-release
```

#### 6.2.2 使用

```bash
# 发布 patch 版本
cargo release patch

# 发布 minor 版本
cargo release minor

# 发布 major 版本
cargo release major

# 预发布版本
cargo release --pre-release alpha

# 干运行（不实际发布）
cargo release --dry-run
```

#### 配置

**Cargo.toml**:

```toml
[package.metadata.release]
sign-commit = true
sign-tag = true
push = true
publish = true
pre-release-commit-message = "chore: Release {{version}}"
tag-message = "Release {{version}}"
```

---

### 6.3 cross - 交叉编译

#### 6.3.1 安装

```bash
cargo install cross
```

#### 6.3.2 使用

```bash
# Linux ARM64
cross build --target aarch64-unknown-linux-gnu

# Linux x86_64
cross build --target x86_64-unknown-linux-gnu

# macOS ARM64
cross build --target aarch64-apple-darwin

# Windows
cross build --target x86_64-pc-windows-gnu

# Release 构建
cross build --release --target aarch64-unknown-linux-gnu
```

---

## 7. OTLP 专用集成

### 7.1 自定义 Cargo 命令 - otlp-trace

创建自定义 Cargo 命令来快速启动 OTLP 追踪。

**~/.cargo/bin/cargo-otlp-trace**:

```bash
#!/bin/bash
# cargo-otlp-trace - 快速启动 OTLP 追踪示例

set -e

# 启动 Jaeger
docker run -d --name jaeger-temp \
  -e COLLECTOR_OTLP_ENABLED=true \
  -p 4317:4317 \
  -p 16686:16686 \
  jaegertracing/all-in-one:latest

echo "Jaeger started at http://localhost:16686"

# 运行应用
OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317 \
RUST_LOG=debug \
cargo run "$@"

# 清理
docker stop jaeger-temp
docker rm jaeger-temp
```

```bash
chmod +x ~/.cargo/bin/cargo-otlp-trace
```

#### 7.2 使用

```bash
# 快速运行 OTLP 追踪
cargo otlp-trace

# 运行特定示例
cargo otlp-trace --example http_server
```

---

### 7.2 OTLP 基准测试模板

**benches/otlp_template.rs**:

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};
use opentelemetry::trace::{Tracer, TracerProvider};
use opentelemetry_sdk::trace::TracerProvider as SdkTracerProvider;

fn benchmark_span_throughput(c: &mut Criterion) {
    let provider = SdkTracerProvider::builder().build();
    let tracer = provider.tracer("benchmark");

    let mut group = c.benchmark_group("span_throughput");
    group.throughput(Throughput::Elements(1));

    group.bench_function("create_span", |b| {
        b.iter(|| {
            let span = tracer.start(black_box("operation"));
            drop(span);
        });
    });

    group.bench_function("create_span_with_attributes", |b| {
        b.iter(|| {
            let mut span = tracer.start(black_box("operation"));
            span.set_attribute(black_box(opentelemetry::KeyValue::new("key", "value")));
            drop(span);
        });
    });

    group.finish();
}

criterion_group!(benches, benchmark_span_throughput);
criterion_main!(benches);
```

---

### 7.3 OTLP 构建脚本

**build.rs**:

```rust
use std::env;

fn main() {
    // 检测 OTLP 环境变量
    if let Ok(endpoint) = env::var("OTEL_EXPORTER_OTLP_ENDPOINT") {
        println!("cargo:rustc-env=OTEL_EXPORTER_OTLP_ENDPOINT={}", endpoint);
    }

    // 默认端点
    if env::var("OTEL_EXPORTER_OTLP_ENDPOINT").is_err() {
        println!("cargo:rustc-env=OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317");
    }

    // 检测 feature flags
    if cfg!(feature = "otlp-grpc") {
        println!("cargo:rustc-cfg=otlp_grpc_enabled");
    }

    if cfg!(feature = "otlp-http") {
        println!("cargo:rustc-cfg=otlp_http_enabled");
    }

    println!("cargo:rerun-if-env-changed=OTEL_EXPORTER_OTLP_ENDPOINT");
}
```

---

## 8. 完整 Makefile / Justfile

### 8.1 Makefile

**Makefile**:

```makefile
.PHONY: all build test lint fmt check clean dev bench coverage audit release

# 默认目标
all: build

# 构建
build:
 cargo build

build-release:
 cargo build --release

# 测试
test:
 cargo nextest run

test-all:
 cargo nextest run --all-targets --all-features

# 代码检查
lint:
 cargo clippy -- -D warnings

fmt:
 cargo fmt

fmt-check:
 cargo fmt -- --check

check: fmt-check lint test

# 开发
dev:
 cargo watch -c -x check -x test -x run

# 基准测试
bench:
 cargo bench --bench otlp_benchmark

# 覆盖率
coverage:
 cargo llvm-cov --html
 @echo "Coverage report: target/llvm-cov/html/index.html"

# 安全
audit:
 cargo audit
 cargo deny check

# 清理
clean:
 cargo clean

# 发布
release: check
 cargo build --release
 cargo publish --dry-run

# OTLP 专用
otlp-dev:
 docker-compose up -d jaeger
 OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317 cargo run
 docker-compose down

otlp-test:
 docker-compose up -d jaeger
 OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317 cargo test
 docker-compose down
```

---

### 8.2 Justfile (推荐)

**justfile**:

```just
# 列出所有命令
default:
    @just --list

# 构建项目
build:
    cargo build

# Release 构建
build-release:
    cargo build --release

# 运行测试
test:
    cargo nextest run

# 运行所有测试
test-all:
    cargo nextest run --all-targets --all-features

# 代码格式化
fmt:
    cargo fmt

# 检查格式
fmt-check:
    cargo fmt -- --check

# Lint 检查
lint:
    cargo clippy -- -D warnings

# 完整检查
check: fmt-check lint test

# 开发模式
dev:
    cargo watch -c -x check -x test -x run

# 基准测试
bench:
    cargo bench

# 覆盖率
coverage:
    cargo llvm-cov --html
    @echo "Coverage report: target/llvm-cov/html/index.html"

# 安全审计
audit:
    cargo audit
    cargo deny check

# 清理
clean:
    cargo clean

# 发布检查
release: check
    cargo build --release
    cargo publish --dry-run

# OTLP 开发环境
otlp-dev:
    docker-compose up -d jaeger
    OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317 cargo run
    docker-compose down

# OTLP 测试
otlp-test:
    docker-compose up -d jaeger
    OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317 cargo test
    docker-compose down

# 启动 Jaeger
jaeger-start:
    docker run -d --name jaeger \
      -e COLLECTOR_OTLP_ENABLED=true \
      -p 4317:4317 \
      -p 4318:4318 \
      -p 16686:16686 \
      jaegertracing/all-in-one:latest
    @echo "Jaeger UI: http://localhost:16686"

# 停止 Jaeger
jaeger-stop:
    docker stop jaeger
    docker rm jaeger

# 火焰图
flamegraph:
    cargo flamegraph --bin my_binary

# 依赖更新
update:
    cargo update
    cargo outdated

# CI 完整流程
ci: fmt-check lint test audit
    @echo "✅ All CI checks passed!"
```

#### 使用 Just

```bash
# 安装 just
cargo install just

# 列出所有命令
just

# 运行命令
just build
just dev
just otlp-dev
just ci
```

---

## 9. CI/CD 集成

### 9.1 GitHub Actions

**.github/workflows/ci.yml**:

```yaml
name: CI

on:
  push:
    branches: [main]
  pull_request:
    branches: [main]

env:
  CARGO_TERM_COLOR: always

jobs:
  check:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Install Rust
        uses: actions-rs/toolchain@v1
        with:
          toolchain: 1.90.0
          profile: minimal
          components: rustfmt, clippy
          override: true

      - name: Cache cargo registry
        uses: actions/cache@v3
        with:
          path: ~/.cargo/registry
          key: ${{ runner.os }}-cargo-registry-${{ hashFiles('**/Cargo.lock') }}

      - name: Cache cargo index
        uses: actions/cache@v3
        with:
          path: ~/.cargo/git
          key: ${{ runner.os }}-cargo-git-${{ hashFiles('**/Cargo.lock') }}

      - name: Cache cargo build
        uses: actions/cache@v3
        with:
          path: target
          key: ${{ runner.os }}-cargo-build-target-${{ hashFiles('**/Cargo.lock') }}

      - name: Check formatting
        run: cargo fmt -- --check

      - name: Run clippy
        run: cargo clippy --all-targets --all-features -- -D warnings

      - name: Run tests
        run: cargo test --all-features

      - name: Run security audit
        uses: actions-rs/audit-check@v1
        with:
          token: ${{ secrets.GITHUB_TOKEN }}

  coverage:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Install Rust
        uses: actions-rs/toolchain@v1
        with:
          toolchain: 1.90.0
          profile: minimal
          components: llvm-tools-preview
          override: true

      - name: Install cargo-llvm-cov
        run: cargo install cargo-llvm-cov

      - name: Generate coverage
        run: cargo llvm-cov --lcov --output-path lcov.info

      - name: Upload to Codecov
        uses: codecov/codecov-action@v3
        with:
          files: lcov.info

  benchmark:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Install Rust
        uses: actions-rs/toolchain@v1
        with:
          toolchain: 1.90.0
          profile: minimal
          override: true

      - name: Run benchmarks
        run: cargo bench --bench otlp_benchmark
```

---

### 9.2 GitLab CI

**.gitlab-ci.yml**:

```yaml
stages:
  - check
  - test
  - benchmark

variables:
  CARGO_HOME: $CI_PROJECT_DIR/.cargo

cache:
  paths:
    - .cargo/
    - target/

before_script:
  - rustc --version
  - cargo --version

check:
  stage: check
  script:
    - cargo fmt -- --check
    - cargo clippy -- -D warnings

test:
  stage: test
  script:
    - cargo test --all-features
  coverage: '/^\d+\.\d+% coverage/'

security:
  stage: check
  script:
    - cargo install cargo-audit
    - cargo audit

benchmark:
  stage: benchmark
  script:
    - cargo bench
  only:
    - main
```

---

## 10. 最佳实践

### 10.1 开发工作流

```bash
# 1. 启动开发环境
just jaeger-start

# 2. 启动 watch 模式
cargo watch -c -x check -x test -x "run --example basic_trace"

# 3. 在另一个终端查看 Jaeger UI
open http://localhost:16686

# 4. 完成后清理
just jaeger-stop
```

---

### 10.2 性能优化工作流

```bash
# 1. 运行基准测试
cargo bench --bench otlp_benchmark

# 2. 生成火焰图
cargo flamegraph --bench otlp_benchmark

# 3. 分析瓶颈
open flamegraph.svg

# 4. 优化代码后再次基准测试
cargo bench --bench otlp_benchmark -- --baseline previous
```

---

### 10.3 发布工作流

```bash
# 1. 完整检查
just ci

# 2. 更新版本号
cargo release patch --dry-run

# 3. 生成 changelog
git log --oneline > CHANGELOG_new.md

# 4. 发布
cargo release patch --execute

# 5. 推送 tag
git push origin v0.2.0
```

---

## 🔗 参考资源

- [Cargo Book](https://doc.rust-lang.org/cargo/)
- [Cargo Commands](https://doc.rust-lang.org/cargo/commands/)
- [Criterion.rs](https://bheisler.github.io/criterion.rs/book/)
- [cargo-flamegraph](https://github.com/flamegraph-rs/flamegraph)
- [cargo-nextest](https://nexte.st/)
- [just](https://github.com/casey/just)

---

**文档版本**: v1.0  
**创建日期**: 2025年10月10日  
**维护者**: OTLP Rust 团队

---

[🏠 返回主目录](../README.md) | [📚 快速入门](../33_教程与示例/01_Rust_OTLP_30分钟快速入门.md) | [⚙️ 开发环境配置](./01_Rust开发环境配置.md)
