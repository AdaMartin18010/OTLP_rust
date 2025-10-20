# Cargo 工具链完整集成指南 - OpenTelemetry Rust

> **Rust 版本**: 1.90+  
> **Cargo 版本**: 1.90+  
> **最后更新**: 2025年10月11日

---

## 📋 目录

- [Cargo 工具链完整集成指南 - OpenTelemetry Rust](#cargo-工具链完整集成指南---opentelemetry-rust)
  - [📋 目录](#-目录)
  - [1. Cargo 基础工具](#1-cargo-基础工具)
    - [1.1 核心命令](#11-核心命令)
    - [1.2 工作区 (Workspace) 管理](#12-工作区-workspace-管理)
    - [1.3 特性 (Features) 管理](#13-特性-features-管理)
  - [2. OpenTelemetry 专用工具](#2-opentelemetry-专用工具)
    - [2.1 cargo-otlp (自定义工具)](#21-cargo-otlp-自定义工具)
    - [2.2 cargo-trace (追踪集成)](#22-cargo-trace-追踪集成)
  - [3. 性能分析工具](#3-性能分析工具)
    - [3.1 cargo-flamegraph (火焰图)](#31-cargo-flamegraph-火焰图)
    - [3.2 cargo-instruments (macOS)](#32-cargo-instruments-macos)
    - [3.3 cargo-criterion (基准测试)](#33-cargo-criterion-基准测试)
    - [3.4 cargo-bench (内置基准测试)](#34-cargo-bench-内置基准测试)
  - [4. 代码质量工具](#4-代码质量工具)
    - [4.1 cargo-clippy (Linter)](#41-cargo-clippy-linter)
    - [4.2 cargo-fmt (格式化)](#42-cargo-fmt-格式化)
    - [4.3 cargo-fix (自动修复)](#43-cargo-fix-自动修复)
    - [4.4 cargo-expand (宏展开)](#44-cargo-expand-宏展开)
  - [5. 依赖管理工具](#5-依赖管理工具)
    - [5.1 cargo-tree (依赖树)](#51-cargo-tree-依赖树)
    - [5.2 cargo-outdated (过期检查)](#52-cargo-outdated-过期检查)
    - [5.3 cargo-udeps (未使用依赖)](#53-cargo-udeps-未使用依赖)
    - [5.4 cargo-edit (依赖编辑)](#54-cargo-edit-依赖编辑)
  - [6. 安全审计工具](#6-安全审计工具)
    - [6.1 cargo-audit (安全审计)](#61-cargo-audit-安全审计)
    - [6.2 cargo-deny (依赖策略)](#62-cargo-deny-依赖策略)
    - [6.3 cargo-geiger (不安全代码检测)](#63-cargo-geiger-不安全代码检测)
  - [7. 测试与覆盖率工具](#7-测试与覆盖率工具)
    - [7.1 cargo-test (内置测试)](#71-cargo-test-内置测试)
    - [7.2 cargo-tarpaulin (覆盖率)](#72-cargo-tarpaulin-覆盖率)
    - [7.3 cargo-llvm-cov (LLVM 覆盖率)](#73-cargo-llvm-cov-llvm-覆盖率)
    - [7.4 cargo-nextest (下一代测试运行器)](#74-cargo-nextest-下一代测试运行器)
  - [8. 构建与发布工具](#8-构建与发布工具)
    - [8.1 cargo-cross (交叉编译)](#81-cargo-cross-交叉编译)
    - [8.2 cargo-deb (Debian 包)](#82-cargo-deb-debian-包)
    - [8.3 cargo-rpm (RPM 包)](#83-cargo-rpm-rpm-包)
    - [8.4 cargo-release (发布自动化)](#84-cargo-release-发布自动化)
  - [9. 文档工具](#9-文档工具)
    - [9.1 cargo-doc (文档生成)](#91-cargo-doc-文档生成)
    - [9.2 cargo-readme (README 生成)](#92-cargo-readme-readme-生成)
  - [10. 监控与追踪集成](#10-监控与追踪集成)
    - [10.1 构建时追踪](#101-构建时追踪)
    - [10.2 测试时追踪](#102-测试时追踪)
    - [10.3 基准测试追踪](#103-基准测试追踪)
  - [11. CI/CD 工具链](#11-cicd-工具链)
    - [11.1 GitHub Actions](#111-github-actions)
    - [11.2 GitLab CI](#112-gitlab-ci)
    - [11.3 完整 Makefile](#113-完整-makefile)
  - [12. 自定义 Cargo 命令](#12-自定义-cargo-命令)
    - [12.1 创建自定义命令](#121-创建自定义命令)
    - [12.2 示例: cargo-otlp-verify](#122-示例-cargo-otlp-verify)
  - [13. 最佳实践清单](#13-最佳实践清单)
  - [参考资源](#参考资源)

---

## 1. Cargo 基础工具

### 1.1 核心命令

```bash
# 创建新项目
cargo new my-otlp-service --bin
cargo new my-otlp-lib --lib

# 构建
cargo build                    # Debug 模式
cargo build --release         # Release 模式
cargo build --all-features    # 启用所有特性

# 运行
cargo run
cargo run --release
cargo run --bin my-app -- --arg1 value1

# 测试
cargo test
cargo test --all-features
cargo test test_name

# 检查 (不生成二进制)
cargo check
cargo check --all-targets

# 清理
cargo clean

# 更新依赖
cargo update
cargo update -p opentelemetry
```

### 1.2 工作区 (Workspace) 管理

**Cargo.toml (根目录)**:

```toml
[workspace]
members = [
    "services/api",
    "services/worker",
    "libs/telemetry",
    "libs/common",
]

[workspace.package]
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[workspace.dependencies]
# 统一管理依赖版本
opentelemetry = "0.31"
opentelemetry_sdk = "0.31"
opentelemetry-otlp = "0.31"
tokio = { version = "1.41", features = ["full"] }
axum = "0.7"
anyhow = "1.0"
```

**成员项目使用工作区依赖**:

```toml
# services/api/Cargo.toml
[package]
name = "api-service"
version.workspace = true
edition.workspace = true

[dependencies]
opentelemetry.workspace = true
tokio.workspace = true
axum.workspace = true
```

**工作区命令**:

```bash
# 构建所有成员
cargo build --workspace

# 测试所有成员
cargo test --workspace

# 仅构建特定成员
cargo build -p api-service

# 运行特定成员
cargo run -p worker-service
```

### 1.3 特性 (Features) 管理

**Cargo.toml**:

```toml
[features]
default = ["grpc", "traces"]
grpc = ["opentelemetry-otlp/grpc-tonic"]
http = ["opentelemetry-otlp/http-proto"]
traces = ["opentelemetry/trace"]
metrics = ["opentelemetry/metrics"]
logs = ["opentelemetry/logs"]
full = ["grpc", "http", "traces", "metrics", "logs"]

[dependencies]
opentelemetry = { version = "0.31", optional = true }
opentelemetry-otlp = { version = "0.31", optional = true }
```

**使用特性**:

```bash
# 禁用默认特性
cargo build --no-default-features

# 启用特定特性
cargo build --features "grpc,traces"

# 启用所有特性
cargo build --all-features

# 检查特性组合
cargo check --features "http,metrics"
```

---

## 2. OpenTelemetry 专用工具

### 2.1 cargo-otlp (自定义工具)

**创建自定义 cargo-otlp 工具**:

```rust
// cargo-otlp/src/main.rs
use clap::{Parser, Subcommand};
use anyhow::Result;

#[derive(Parser)]
#[command(name = "cargo-otlp")]
#[command(about = "OpenTelemetry 工具链集成", long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// 验证 OTLP 配置
    Verify {
        #[arg(short, long)]
        config: Option<String>,
    },
    /// 测试 OTLP 连接
    TestConnection {
        #[arg(short, long, default_value = "http://localhost:4317")]
        endpoint: String,
    },
    /// 生成 OTLP 配置模板
    Init {
        #[arg(short, long, default_value = "collector-config.yaml")]
        output: String,
    },
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    
    match cli.command {
        Commands::Verify { config } => {
            println!("✅ 验证 OTLP 配置...");
            // 实现验证逻辑
        }
        Commands::TestConnection { endpoint } => {
            println!("🔌 测试连接: {}", endpoint);
            // 实现连接测试
        }
        Commands::Init { output } => {
            println!("📝 生成配置: {}", output);
            // 实现配置生成
        }
    }
    
    Ok(())
}
```

**安装**:

```bash
cargo install --path cargo-otlp

# 使用
cargo otlp verify
cargo otlp test-connection --endpoint http://localhost:4317
cargo otlp init
```

### 2.2 cargo-trace (追踪集成)

**概念**: 为 Cargo 命令添加 OTLP 追踪。

```rust
// cargo-trace/src/main.rs
use opentelemetry::{global, trace::{Tracer, Span}};
use std::process::Command;

fn main() -> anyhow::Result<()> {
    // 初始化 OTLP
    let tracer = global::tracer("cargo-trace");
    
    let mut span = tracer.start("cargo_command");
    
    // 运行实际 Cargo 命令
    let args: Vec<String> = std::env::args().skip(1).collect();
    let output = Command::new("cargo")
        .args(&args)
        .output()?;
    
    span.set_attribute(opentelemetry::KeyValue::new("exit_code", output.status.code().unwrap_or(-1) as i64));
    span.end();
    
    println!("{}", String::from_utf8_lossy(&output.stdout));
    
    Ok(())
}
```

---

## 3. 性能分析工具

### 3.1 cargo-flamegraph (火焰图)

**安装**:

```bash
cargo install flamegraph
```

**使用**:

```bash
# 生成火焰图
cargo flamegraph --bin my-app

# 指定输出
cargo flamegraph --bin my-app -o my-app-flamegraph.svg

# 采样频率
cargo flamegraph --freq 997 --bin my-app

# 仅 CPU
cargo flamegraph --bin my-app -- --release
```

**OTLP 应用集成**:

```bash
# 分析 OTLP 导出性能
cargo flamegraph --bin my-app -- --otlp-endpoint http://localhost:4317
```

### 3.2 cargo-instruments (macOS)

**安装**:

```bash
cargo install cargo-instruments
```

**使用**:

```bash
# 时间分析
cargo instruments -t time --bin my-app

# 内存分配
cargo instruments -t alloc --bin my-app

# 系统调用
cargo instruments -t syscall --bin my-app

# 自定义模板
cargo instruments --list-templates
```

### 3.3 cargo-criterion (基准测试)

**Cargo.toml**:

```toml
[dev-dependencies]
criterion = { version = "0.5", features = ["html_reports"] }

[[bench]]
name = "otlp_export_bench"
harness = false
```

**benches/otlp_export_bench.rs**:

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use opentelemetry::{global, trace::Tracer, KeyValue};

fn bench_span_creation(c: &mut Criterion) {
    let tracer = global::tracer("benchmark");
    
    c.bench_function("create_span", |b| {
        b.iter(|| {
            let span = tracer.start("test_span");
            black_box(span);
        });
    });
}

fn bench_span_with_attributes(c: &mut Criterion) {
    let tracer = global::tracer("benchmark");
    
    c.bench_function("span_with_attributes", |b| {
        b.iter(|| {
            let mut span = tracer.start("test_span");
            span.set_attribute(KeyValue::new("key1", "value1"));
            span.set_attribute(KeyValue::new("key2", 42));
            black_box(span);
        });
    });
}

criterion_group!(benches, bench_span_creation, bench_span_with_attributes);
criterion_main!(benches);
```

**运行**:

```bash
cargo bench
cargo bench --bench otlp_export_bench

# 保存基线
cargo bench -- --save-baseline before

# 对比基线
cargo bench -- --baseline before
```

### 3.4 cargo-bench (内置基准测试)

```bash
# 运行所有基准测试
cargo bench

# 运行特定基准
cargo bench bench_name

# 传递参数
cargo bench -- --nocapture
```

---

## 4. 代码质量工具

### 4.1 cargo-clippy (Linter)

```bash
# 安装
rustup component add clippy

# 运行
cargo clippy
cargo clippy --all-targets
cargo clippy -- -D warnings      # 将警告视为错误
cargo clippy --fix               # 自动修复

# 特定 lint 级别
cargo clippy -- -W clippy::pedantic
cargo clippy -- -A clippy::module_name_repetitions
```

**.clippy.toml**:

```toml
cognitive-complexity-threshold = 30
too-many-arguments-threshold = 8
type-complexity-threshold = 250
```

### 4.2 cargo-fmt (格式化)

```bash
# 安装
rustup component add rustfmt

# 格式化
cargo fmt
cargo fmt --all                  # 工作区所有成员
cargo fmt -- --check             # 仅检查, 不修改
```

**rustfmt.toml**:

```toml
edition = "2021"
max_width = 100
hard_tabs = false
tab_spaces = 4
newline_style = "Unix"
use_small_heuristics = "Default"
reorder_imports = true
reorder_modules = true
```

### 4.3 cargo-fix (自动修复)

```bash
# 自动修复编译警告
cargo fix

# 应用 Rust Edition 迁移
cargo fix --edition

# 允许修改 staged 文件
cargo fix --allow-staged
```

### 4.4 cargo-expand (宏展开)

**安装**:

```bash
cargo install cargo-expand
```

**使用**:

```bash
# 展开所有宏
cargo expand

# 展开特定模块
cargo expand module_name

# 展开测试
cargo expand --test test_name

# 彩色输出
cargo expand --color always
```

**OTLP 宏调试**:

```rust
#[opentelemetry::instrument]
fn my_function() {
    // ...
}

// 使用 cargo expand 查看展开后的代码
// cargo expand my_function
```

---

## 5. 依赖管理工具

### 5.1 cargo-tree (依赖树)

```bash
# 查看依赖树 (内置)
cargo tree

# 仅显示特定包
cargo tree -p opentelemetry

# 显示重复依赖
cargo tree -d

# 反向依赖
cargo tree -i opentelemetry

# 显示特性
cargo tree --features full
```

### 5.2 cargo-outdated (过期检查)

**安装**:

```bash
cargo install cargo-outdated
```

**使用**:

```bash
# 检查过期依赖
cargo outdated

# 仅显示根依赖
cargo outdated --root-deps-only

# 显示详细信息
cargo outdated -v

# 退出代码 (CI 集成)
cargo outdated --exit-code 1
```

### 5.3 cargo-udeps (未使用依赖)

**安装**:

```bash
cargo install cargo-udeps --locked
```

**使用**:

```bash
# 检查未使用依赖
cargo +nightly udeps

# 所有目标
cargo +nightly udeps --all-targets
```

### 5.4 cargo-edit (依赖编辑)

**安装**:

```bash
cargo install cargo-edit
```

**使用**:

```bash
# 添加依赖
cargo add opentelemetry
cargo add opentelemetry@0.31
cargo add opentelemetry --features trace,metrics

# 添加开发依赖
cargo add --dev criterion

# 移除依赖
cargo rm opentelemetry

# 升级依赖
cargo upgrade
cargo upgrade opentelemetry
```

---

## 6. 安全审计工具

### 6.1 cargo-audit (安全审计)

**安装**:

```bash
cargo install cargo-audit
```

**使用**:

```bash
# 运行审计
cargo audit

# 修复已知漏洞
cargo audit fix

# 忽略特定漏洞
cargo audit --ignore RUSTSEC-2021-0001

# JSON 输出
cargo audit --json
```

**.cargo/audit.toml**:

```toml
[advisories]
ignore = [
    # "RUSTSEC-2021-0001"  # 忽略特定漏洞
]

[output]
deny = ["unmaintained", "unsound", "yanked"]
```

### 6.2 cargo-deny (依赖策略)

**安装**:

```bash
cargo install cargo-deny
```

**deny.toml**:

```toml
[advisories]
vulnerability = "deny"
unmaintained = "warn"
yanked = "warn"

[licenses]
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
wildcards = "deny"
deny = [
    { name = "openssl-sys", wrappers = ["openssl"] }
]

[sources]
unknown-registry = "deny"
unknown-git = "warn"
```

**使用**:

```bash
# 检查所有策略
cargo deny check

# 仅检查许可证
cargo deny check licenses

# 仅检查安全问题
cargo deny check advisories

# 仅检查禁用依赖
cargo deny check bans
```

### 6.3 cargo-geiger (不安全代码检测)

**安装**:

```bash
cargo install cargo-geiger
```

**使用**:

```bash
# 检测不安全代码
cargo geiger

# 详细输出
cargo geiger --all-dependencies

# JSON 输出
cargo geiger --output-format json
```

---

## 7. 测试与覆盖率工具

### 7.1 cargo-test (内置测试)

```bash
# 运行所有测试
cargo test

# 运行特定测试
cargo test test_name

# 显示输出
cargo test -- --nocapture

# 并行度
cargo test -- --test-threads=1

# 忽略测试
cargo test -- --ignored

# 文档测试
cargo test --doc
```

### 7.2 cargo-tarpaulin (覆盖率)

**安装 (Linux)**:

```bash
cargo install cargo-tarpaulin
```

**使用**:

```bash
# 生成覆盖率报告
cargo tarpaulin --out Html

# 多种输出格式
cargo tarpaulin --out Html --out Xml --out Lcov

# 排除文件
cargo tarpaulin --exclude-files "tests/*"

# CI 模式
cargo tarpaulin --out Xml --output-dir coverage
```

### 7.3 cargo-llvm-cov (LLVM 覆盖率)

**安装**:

```bash
rustup component add llvm-tools-preview
cargo install cargo-llvm-cov
```

**使用**:

```bash
# HTML 报告
cargo llvm-cov --html

# LCOV 格式
cargo llvm-cov --lcov --output-path lcov.info

# 在浏览器中打开
cargo llvm-cov --open

# 包含所有依赖
cargo llvm-cov --all-targets
```

### 7.4 cargo-nextest (下一代测试运行器)

**安装**:

```bash
cargo install cargo-nextest
```

**使用**:

```bash
# 运行测试
cargo nextest run

# 并行测试
cargo nextest run --test-threads=16

# 失败时停止
cargo nextest run --fail-fast

# JUnit 输出 (CI)
cargo nextest run --message-format junit > test-results.xml
```

---

## 8. 构建与发布工具

### 8.1 cargo-cross (交叉编译)

**安装**:

```bash
cargo install cross
```

**使用**:

```bash
# 交叉编译到 Linux ARM64
cross build --target aarch64-unknown-linux-gnu

# 交叉编译到 Windows
cross build --target x86_64-pc-windows-gnu

# 构建 Docker 镜像
cross build --target x86_64-unknown-linux-musl --release
```

**Cross.toml**:

```toml
[build]
image = "my-custom-image:latest"

[target.aarch64-unknown-linux-gnu]
dockerfile = "./Dockerfile.arm64"
```

### 8.2 cargo-deb (Debian 包)

**安装**:

```bash
cargo install cargo-deb
```

**Cargo.toml**:

```toml
[package.metadata.deb]
maintainer = "Your Name <you@example.com>"
copyright = "2025, Your Name <you@example.com>"
extended-description = """\
My OTLP service with OpenTelemetry integration."""
depends = "$auto"
section = "utility"
priority = "optional"
assets = [
    ["target/release/my-app", "usr/bin/", "755"],
    ["README.md", "usr/share/doc/my-app/", "644"],
]
```

**使用**:

```bash
cargo deb
sudo dpkg -i target/debian/my-app_0.1.0_amd64.deb
```

### 8.3 cargo-rpm (RPM 包)

**安装**:

```bash
cargo install cargo-rpm
```

**使用**:

```bash
cargo rpm init
cargo rpm build
```

### 8.4 cargo-release (发布自动化)

**安装**:

```bash
cargo install cargo-release
```

**使用**:

```bash
# 发布 patch 版本
cargo release patch

# 发布 minor 版本
cargo release minor

# 发布 major 版本
cargo release major

# 试运行
cargo release --dry-run
```

---

## 9. 文档工具

### 9.1 cargo-doc (文档生成)

```bash
# 生成文档
cargo doc

# 打开文档
cargo doc --open

# 包含私有项
cargo doc --document-private-items

# 不包含依赖
cargo doc --no-deps
```

### 9.2 cargo-readme (README 生成)

**安装**:

```bash
cargo install cargo-readme
```

**使用**:

```bash
# 从 lib.rs 生成 README.md
cargo readme > README.md

# 自定义模板
cargo readme --template custom-template.md
```

---

## 10. 监控与追踪集成

### 10.1 构建时追踪

**build.rs**:

```rust
use opentelemetry::{global, trace::Tracer};

fn main() {
    // 初始化 OTLP (仅在 CI 环境)
    if std::env::var("CI").is_ok() {
        init_otlp();
    }
    
    let tracer = global::tracer("build-script");
    let span = tracer.start("cargo_build");
    
    // 执行构建任务
    println!("cargo:rerun-if-changed=build.rs");
    
    drop(span);  // 结束 span
}

fn init_otlp() {
    // 初始化 OTLP exporter
}
```

### 10.2 测试时追踪

```rust
#[cfg(test)]
mod tests {
    use opentelemetry::{global, trace::Tracer};

    #[test]
    fn test_with_tracing() {
        let tracer = global::tracer("tests");
        let span = tracer.start("test_function");
        
        // 测试逻辑
        assert_eq!(2 + 2, 4);
        
        drop(span);
    }
}
```

### 10.3 基准测试追踪

```rust
use criterion::{criterion_group, criterion_main, Criterion};
use opentelemetry::{global, trace::Tracer};

fn bench_with_tracing(c: &mut Criterion) {
    let tracer = global::tracer("benchmark");
    
    c.bench_function("my_function", |b| {
        b.iter(|| {
            let span = tracer.start("bench_iteration");
            // 基准测试逻辑
            drop(span);
        });
    });
}

criterion_group!(benches, bench_with_tracing);
criterion_main!(benches);
```

---

## 11. CI/CD 工具链

### 11.1 GitHub Actions

**.github/workflows/ci.yml**:

```yaml
name: CI

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - uses: dtolnay/rust-toolchain@stable
        with:
          components: rustfmt, clippy
      
      - uses: Swatinem/rust-cache@v2
      
      - name: Format
        run: cargo fmt -- --check
      
      - name: Clippy
        run: cargo clippy --all-targets -- -D warnings
      
      - name: Test
        run: cargo test
      
      - name: Coverage
        run: |
          cargo install cargo-tarpaulin
          cargo tarpaulin --out Xml
      
      - name: Upload Coverage
        uses: codecov/codecov-action@v4
        with:
          files: cobertura.xml
```

### 11.2 GitLab CI

**.gitlab-ci.yml**:

```yaml
image: rust:1.90

stages:
  - test
  - build
  - deploy

variables:
  CARGO_HOME: $CI_PROJECT_DIR/.cargo

cache:
  paths:
    - .cargo/
    - target/

test:
  stage: test
  script:
    - cargo fmt -- --check
    - cargo clippy -- -D warnings
    - cargo test
    - cargo audit

build:
  stage: build
  script:
    - cargo build --release
  artifacts:
    paths:
      - target/release/my-app
```

### 11.3 完整 Makefile

**Makefile**:

```makefile
.PHONY: all build test check fmt clippy audit doc clean

all: check test build

build:
 cargo build --release

test:
 cargo test --all-features

check:
 cargo check --all-targets

fmt:
 cargo fmt --all

fmt-check:
 cargo fmt --all -- --check

clippy:
 cargo clippy --all-targets -- -D warnings

audit:
 cargo audit

outdated:
 cargo outdated

doc:
 cargo doc --no-deps --open

bench:
 cargo bench

flamegraph:
 cargo flamegraph --bin my-app

coverage:
 cargo tarpaulin --out Html

clean:
 cargo clean

install-tools:
 cargo install cargo-audit cargo-outdated cargo-tarpaulin cargo-flamegraph

ci: fmt-check clippy test
 @echo "✅ CI checks passed"
```

---

## 12. 自定义 Cargo 命令

### 12.1 创建自定义命令

任何以 `cargo-` 为前缀的可执行文件都可以作为 Cargo 子命令。

**项目结构**:

```text
cargo-otlp-verify/
├── Cargo.toml
└── src/
    └── main.rs
```

**src/main.rs**:

```rust
use clap::Parser;
use anyhow::Result;

#[derive(Parser)]
#[command(name = "cargo-otlp-verify")]
struct Cli {
    #[arg(skip)]
    _cargo: Option<String>,  // 跳过第一个参数 "otlp-verify"
}

fn main() -> Result<()> {
    let _cli = Cli::parse();
    
    println!("🔍 Verifying OTLP configuration...");
    
    // 实现验证逻辑
    
    println!("✅ OTLP configuration is valid");
    Ok(())
}
```

**安装**:

```bash
cargo install --path .

# 使用
cargo otlp-verify
```

### 12.2 示例: cargo-otlp-verify

完整的 OTLP 配置验证工具:

```rust
use anyhow::{Context, Result};
use serde::Deserialize;
use std::path::PathBuf;

#[derive(Deserialize)]
struct OtlpConfig {
    endpoint: String,
    service_name: String,
}

fn main() -> Result<()> {
    let config_path = PathBuf::from("otlp-config.toml");
    
    // 读取配置
    let config_str = std::fs::read_to_string(&config_path)
        .context("Failed to read config file")?;
    
    let config: OtlpConfig = toml::from_str(&config_str)
        .context("Failed to parse config")?;
    
    // 验证 endpoint
    if !config.endpoint.starts_with("http://") && !config.endpoint.starts_with("https://") {
        anyhow::bail!("Invalid endpoint format");
    }
    
    // 验证 service_name
    if config.service_name.is_empty() {
        anyhow::bail!("Service name cannot be empty");
    }
    
    println!("✅ Configuration is valid");
    println!("   Endpoint: {}", config.endpoint);
    println!("   Service: {}", config.service_name);
    
    Ok(())
}
```

---

## 13. 最佳实践清单

- ✅ **使用工作区**: 多包项目使用 workspace 统一管理
- ✅ **固定版本**: 使用 `Cargo.lock` 固定依赖版本
- ✅ **代码质量**: CI 中强制执行 `fmt` 和 `clippy`
- ✅ **安全审计**: 定期运行 `cargo audit` 和 `cargo deny`
- ✅ **测试覆盖**: 保持 > 80% 测试覆盖率
- ✅ **性能基准**: 使用 `criterion` 持续监控性能
- ✅ **文档完整**: 为公开 API 编写完整文档
- ✅ **依赖更新**: 定期检查并更新依赖
- ✅ **交叉编译**: 使用 `cross` 支持多平台
- ✅ **自动化发布**: 使用 `cargo-release` 自动化版本管理

---

## 参考资源

**官方文档**:

- [Cargo Book](https://doc.rust-lang.org/cargo/)
- [Cargo Commands](https://doc.rust-lang.org/cargo/commands/)
- [Cargo Reference](https://doc.rust-lang.org/cargo/reference/)

**工具集**:

- [cargo-edit](https://github.com/killercup/cargo-edit)
- [cargo-audit](https://github.com/rustsec/rustsec/tree/main/cargo-audit)
- [cargo-deny](https://github.com/EmbarkStudios/cargo-deny)
- [cargo-nextest](https://nexte.st/)

**最佳实践**:

- [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)
- [Rust Performance Book](https://nnethercote.github.io/perf-book/)

---

**创建日期**: 2025年10月11日  
**维护团队**: OTLP Rust Documentation Team  
**License**: MIT
