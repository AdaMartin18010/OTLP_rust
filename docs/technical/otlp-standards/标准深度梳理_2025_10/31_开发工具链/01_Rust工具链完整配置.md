# Rust 工具链完整配置 - OTLP 开发环境

> **Rust版本**: 1.90+  
> **最后更新**: 2025年10月9日

---

## 目录

- [Rust 工具链完整配置 - OTLP 开发环境](#rust-工具链完整配置---otlp-开发环境)
  - [目录](#目录)
  - [1. Rust 安装与配置](#1-rust-安装与配置)
    - [1.1 Rustup 安装](#11-rustup-安装)
    - [1.2 Rust 1.90 配置](#12-rust-190-配置)
    - [1.3 Cargo 全局配置](#13-cargo-全局配置)
  - [2. Cargo 配置优化](#2-cargo-配置优化)
    - [2.1 依赖管理](#21-依赖管理)
    - [2.2 构建加速](#22-构建加速)
    - [2.3 Workspace 配置](#23-workspace-配置)
  - [3. 开发工具](#3-开发工具)
    - [3.1 rust-analyzer (LSP)](#31-rust-analyzer-lsp)
    - [3.2 cargo-expand](#32-cargo-expand)
    - [3.3 cargo-tree](#33-cargo-tree)
  - [4. 代码质量工具](#4-代码质量工具)
    - [4.1 Clippy (Linter)](#41-clippy-linter)
    - [4.2 Rustfmt (格式化)](#42-rustfmt-格式化)
    - [4.3 cargo-deny](#43-cargo-deny)
  - [5. 性能分析工具](#5-性能分析工具)
    - [5.1 cargo-flamegraph](#51-cargo-flamegraph)
    - [5.2 cargo-bench](#52-cargo-bench)
    - [5.3 Criterion (基准测试框架)](#53-criterion-基准测试框架)
  - [6. 调试工具](#6-调试工具)
    - [6.1 LLDB/GDB](#61-lldbgdb)
    - [6.2 cargo-llvm-cov (覆盖率)](#62-cargo-llvm-cov-覆盖率)
    - [6.3 tracing-subscriber (日志)](#63-tracing-subscriber-日志)
  - [7. CI/CD 工具](#7-cicd-工具)
    - [7.1 cargo-audit (安全审计)](#71-cargo-audit-安全审计)
    - [7.2 cargo-outdated](#72-cargo-outdated)
    - [7.3 cargo-nextest (快速测试)](#73-cargo-nextest-快速测试)
  - [8. 完整示例项目结构](#8-完整示例项目结构)
    - [Makefile (可选)](#makefile-可选)
    - [justfile (推荐)](#justfile-推荐)

---

## 1. Rust 安装与配置

### 1.1 Rustup 安装

```bash
# Linux/macOS
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Windows (PowerShell)
Invoke-WebRequest -Uri https://win.rustup.rs/x86_64 -OutFile rustup-init.exe
.\rustup-init.exe

# 验证安装
rustc --version
cargo --version
```

### 1.2 Rust 1.90 配置

**rust-toolchain.toml**:

```toml
[toolchain]
channel = "1.90"
components = [
    "rustfmt",
    "clippy",
    "rust-src",
    "rust-analyzer",
    "llvm-tools-preview",
]
profile = "default"
```

### 1.3 Cargo 全局配置

**.cargo/config.toml** (项目级):

```toml
[build]
# 使用本地 CPU 特性
rustflags = ["-C", "target-cpu=native"]

# 增量编译 (开发环境)
incremental = true

[term]
# 彩色输出
color = "always"

[cargo-new]
# 新项目默认使用 2021 edition
edition = "2021"

[profile.dev]
# 开发环境优化
opt-level = 0
debug = true
split-debuginfo = "unpacked"

[profile.release]
# 生产环境优化
opt-level = 3
lto = "fat"
codegen-units = 1
panic = "abort"
strip = true

[profile.bench]
# 基准测试优化
inherits = "release"

[profile.test]
# 测试优化
opt-level = 1

# 依赖加速 (使用国内镜像)
[source.crates-io]
replace-with = "ustc"

[source.ustc]
registry = "https://mirrors.ustc.edu.cn/crates.io-index"
```

---

## 2. Cargo 配置优化

### 2.1 依赖管理

```bash
# 安装 cargo-edit (添加/删除/升级依赖)
cargo install cargo-edit

# 添加依赖
cargo add opentelemetry@0.31.0
cargo add tokio --features full

# 升级依赖
cargo upgrade

# 移除依赖
cargo rm old-crate
```

### 2.2 构建加速

```bash
# 安装 sccache (编译缓存)
cargo install sccache

# 配置 sccache
export RUSTC_WRAPPER=sccache

# 或在 .cargo/config.toml 中配置
[build]
rustc-wrapper = "sccache"

# 安装 cargo-watch (自动重新编译)
cargo install cargo-watch

# 使用
cargo watch -x run
cargo watch -x test
```

### 2.3 Workspace 配置

**Cargo.toml** (workspace 根目录):

```toml
[workspace]
members = [
    "crates/otlp-core",
    "crates/otlp-http",
    "crates/otlp-grpc",
    "examples/*",
]

resolver = "2"

[workspace.package]
version = "0.1.0"
edition = "2021"
rust-version = "1.90"
authors = ["Your Name <your.email@example.com>"]
license = "MIT OR Apache-2.0"
repository = "https://github.com/yourorg/yourproject"

[workspace.dependencies]
# 统一依赖版本
opentelemetry = "0.31.0"
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio", "trace"] }
tokio = { version = "1.47", features = ["full"] }
tracing = "0.1"
tracing-subscriber = "0.3"

[profile.release]
opt-level = 3
lto = "fat"
codegen-units = 1
```

---

## 3. 开发工具

### 3.1 rust-analyzer (LSP)

**VS Code settings.json**:

```json
{
  "rust-analyzer.checkOnSave.command": "clippy",
  "rust-analyzer.cargo.features": "all",
  "rust-analyzer.inlayHints.enable": true,
  "rust-analyzer.lens.enable": true,
  "rust-analyzer.completion.autoimport.enable": true
}
```

### 3.2 cargo-expand

```bash
# 查看宏展开
cargo install cargo-expand

# 使用
cargo expand
cargo expand my_module
```

### 3.3 cargo-tree

```bash
# 查看依赖树
cargo tree

# 只显示特定包
cargo tree -p opentelemetry

# 查看重复依赖
cargo tree -d
```

---

## 4. 代码质量工具

### 4.1 Clippy (Linter)

```bash
# 安装 (通常已包含)
rustup component add clippy

# 运行 clippy
cargo clippy

# 严格模式
cargo clippy -- -D warnings

# 自动修复
cargo clippy --fix
```

**clippy.toml** (项目配置):

```toml
# 警告级别
warn-on-all-wildcard-imports = true
disallowed-methods = [
    { path = "std::env::set_var", reason = "使用配置文件" },
]

# 忽略特定 lint
allow = [
    "clippy::too_many_arguments",
]
```

### 4.2 Rustfmt (格式化)

**rustfmt.toml**:

```toml
edition = "2021"
max_width = 100
tab_spaces = 4
newline_style = "Unix"
use_small_heuristics = "Default"

# 导入排序
imports_granularity = "Crate"
group_imports = "StdExternalCrate"

# 格式化选项
format_strings = true
format_macro_bodies = true
normalize_comments = true
wrap_comments = true
```

```bash
# 运行 rustfmt
cargo fmt

# 检查格式
cargo fmt -- --check
```

### 4.3 cargo-deny

```bash
# 检查许可证和安全问题
cargo install cargo-deny

# 初始化配置
cargo deny init

# 运行检查
cargo deny check
```

**deny.toml**:

```toml
[advisories]
vulnerability = "deny"
unmaintained = "warn"

[licenses]
allow = [
    "MIT",
    "Apache-2.0",
    "BSD-3-Clause",
]

[bans]
multiple-versions = "warn"
wildcards = "deny"
```

---

## 5. 性能分析工具

### 5.1 cargo-flamegraph

```bash
# 安装
cargo install flamegraph

# 生成火焰图
cargo flamegraph

# 指定二进制
cargo flamegraph --bin my-app
```

### 5.2 cargo-bench

```bash
# 运行基准测试
cargo bench

# 保存结果
cargo bench -- --save-baseline my-baseline

# 比较基准
cargo bench -- --baseline my-baseline
```

### 5.3 Criterion (基准测试框架)

**Cargo.toml**:

```toml
[dev-dependencies]
criterion = { version = "0.5", features = ["html_reports"] }

[[bench]]
name = "my_benchmark"
harness = false
```

**benches/my_benchmark.rs**:

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn fibonacci(n: u64) -> u64 {
    match n {
        0 => 1,
        1 => 1,
        n => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("fib 20", |b| b.iter(|| fibonacci(black_box(20))));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
```

---

## 6. 调试工具

### 6.1 LLDB/GDB

**VS Code launch.json**:

```json
{
  "version": "0.2.0",
  "configurations": [
    {
      "type": "lldb",
      "request": "launch",
      "name": "Debug executable",
      "cargo": {
        "args": ["build", "--bin=my-app", "--package=my-package"]
      },
      "args": [],
      "cwd": "${workspaceFolder}",
      "env": {
        "RUST_LOG": "debug",
        "RUST_BACKTRACE": "1"
      }
    }
  ]
}
```

### 6.2 cargo-llvm-cov (覆盖率)

```bash
# 安装
cargo install cargo-llvm-cov

# 生成覆盖率报告
cargo llvm-cov

# HTML 报告
cargo llvm-cov --html

# 输出 lcov 格式 (Codecov)
cargo llvm-cov --lcov --output-path lcov.info
```

### 6.3 tracing-subscriber (日志)

```rust
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

fn init_logging() {
    tracing_subscriber::registry()
        .with(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| "info,my_crate=debug".into()),
        )
        .with(tracing_subscriber::fmt::layer())
        .init();
}
```

---

## 7. CI/CD 工具

### 7.1 cargo-audit (安全审计)

```bash
# 安装
cargo install cargo-audit

# 运行审计
cargo audit

# 自动修复
cargo audit fix
```

### 7.2 cargo-outdated

```bash
# 检查过期依赖
cargo install cargo-outdated

cargo outdated
```

### 7.3 cargo-nextest (快速测试)

```bash
# 安装
cargo install cargo-nextest

# 运行测试 (比 cargo test 更快)
cargo nextest run

# 并行测试
cargo nextest run --test-threads=8
```

---

## 8. 完整示例项目结构

```text
my-otlp-project/
├── .cargo/
│   └── config.toml          # Cargo 配置
├── .github/
│   └── workflows/
│       └── ci.yml           # CI/CD
├── .vscode/
│   ├── launch.json          # 调试配置
│   └── settings.json        # VS Code 配置
├── benches/
│   └── benchmarks.rs        # 基准测试
├── crates/
│   ├── otlp-core/           # 核心库
│   ├── otlp-http/           # HTTP 传输
│   └── otlp-grpc/           # gRPC 传输
├── examples/
│   ├── basic.rs             # 基础示例
│   └── advanced.rs          # 高级示例
├── src/
│   ├── main.rs              # 主程序
│   └── lib.rs               # 库
├── tests/
│   └── integration_test.rs  # 集成测试
├── .gitignore
├── Cargo.toml               # 项目配置
├── Cargo.lock
├── clippy.toml              # Clippy 配置
├── deny.toml                # cargo-deny 配置
├── rustfmt.toml             # Rustfmt 配置
└── rust-toolchain.toml      # Rust 工具链
```

### Makefile (可选)

```makefile
.PHONY: all build test clippy fmt check clean

all: check test build

build:
 cargo build --release

test:
 cargo nextest run

clippy:
 cargo clippy -- -D warnings

fmt:
 cargo fmt

check: fmt clippy
 cargo deny check

clean:
 cargo clean

bench:
 cargo bench

doc:
 cargo doc --no-deps --open

audit:
 cargo audit

outdated:
 cargo outdated
```

### justfile (推荐)

```just
# 显示帮助
help:
    @just --list

# 构建项目
build:
    cargo build --release

# 运行测试
test:
    cargo nextest run

# 代码检查
check:
    cargo fmt -- --check
    cargo clippy -- -D warnings
    cargo deny check

# 自动修复
fix:
    cargo fmt
    cargo clippy --fix --allow-dirty

# 基准测试
bench:
    cargo bench

# 运行应用
run *ARGS:
    cargo run --release -- {{ARGS}}

# 清理
clean:
    cargo clean
```

---

**相关文档**:

- [VS Code 配置](02_VS_Code_Rust_OTLP配置.md)
- [GitHub Actions 配置](../09_CI_CD集成/01_GitHub_Actions_Rust完整配置.md)

**文档状态**: ✅ 完成  
**最后更新**: 2025年10月9日
