# Rust OpenTelemetry 开发环境完整配置指南

> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月11日

---

## 📋 目录

- [Rust OpenTelemetry 开发环境完整配置指南](#rust-opentelemetry-开发环境完整配置指南)
  - [📋 目录](#-目录)
  - [1. Rust 环境安装与配置](#1-rust-环境安装与配置)
    - [1.1 Rustup 安装](#11-rustup-安装)
    - [1.2 工具链管理](#12-工具链管理)
    - [1.3 组件安装](#13-组件安装)
    - [1.4 Cargo 配置优化](#14-cargo-配置优化)
  - [2. IDE 与编辑器配置](#2-ide-与编辑器配置)
    - [2.1 Visual Studio Code](#21-visual-studio-code)
    - [2.2 JetBrains RustRover / IntelliJ IDEA](#22-jetbrains-rustrover--intellij-idea)
    - [2.3 Vim/Neovim](#23-vimneovim)
    - [2.4 Helix Editor](#24-helix-editor)
  - [3. OpenTelemetry 依赖配置](#3-opentelemetry-依赖配置)
    - [3.1 核心依赖](#31-核心依赖)
    - [3.2 可选特性说明](#32-可选特性说明)
    - [3.3 依赖版本锁定](#33-依赖版本锁定)
  - [4. 代码质量工具](#4-代码质量工具)
    - [4.1 Clippy (Linter)](#41-clippy-linter)
    - [4.2 Rustfmt (代码格式化)](#42-rustfmt-代码格式化)
    - [4.3 Cargo Audit (安全审计)](#43-cargo-audit-安全审计)
    - [4.4 Cargo Deny (依赖检查)](#44-cargo-deny-依赖检查)
  - [5. 调试与分析工具](#5-调试与分析工具)
    - [5.1 LLDB / GDB 调试器](#51-lldb--gdb-调试器)
    - [5.2 Tokio Console (异步调试)](#52-tokio-console-异步调试)
    - [5.3 Cargo Flamegraph (性能分析)](#53-cargo-flamegraph-性能分析)
    - [5.4 Valgrind / Heaptrack (内存分析)](#54-valgrind--heaptrack-内存分析)
  - [6. 测试环境配置](#6-测试环境配置)
    - [6.1 单元测试配置](#61-单元测试配置)
    - [6.2 集成测试环境](#62-集成测试环境)
    - [6.3 测试覆盖率](#63-测试覆盖率)
  - [7. 本地 OTLP 基础设施](#7-本地-otlp-基础设施)
    - [7.1 OpenTelemetry Collector](#71-opentelemetry-collector)
    - [7.2 Jaeger 后端](#72-jaeger-后端)
    - [7.3 Prometheus + Grafana](#73-prometheus--grafana)
    - [7.4 完整开发栈 (Docker Compose)](#74-完整开发栈-docker-compose)
  - [8. 环境变量配置](#8-环境变量配置)
    - [8.1 开发环境变量](#81-开发环境变量)
    - [8.2 使用 dotenv](#82-使用-dotenv)
  - [9. 项目模板与脚手架](#9-项目模板与脚手架)
    - [9.1 使用 Cargo Generate](#91-使用-cargo-generate)
    - [9.2 自定义项目模板](#92-自定义项目模板)
  - [10. 持续集成配置](#10-持续集成配置)
    - [10.1 GitHub Actions](#101-github-actions)
    - [10.2 GitLab CI](#102-gitlab-ci)
  - [11. 故障排查](#11-故障排查)
    - [11.1 Rustup 问题](#111-rustup-问题)
    - [11.2 编译问题](#112-编译问题)
    - [11.3 IDE 问题](#113-ide-问题)
    - [11.4 OTLP 连接问题](#114-otlp-连接问题)
  - [12. 最佳实践清单](#12-最佳实践清单)
  - [参考资源](#参考资源)

---

## 1. Rust 环境安装与配置

### 1.1 Rustup 安装

Rustup 是 Rust 官方的工具链管理器。

**Linux / macOS**:

```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

**Windows**:

下载并运行 [rustup-init.exe](https://rustup.rs/)

**验证安装**:

```bash
rustc --version  # 应显示 rustc 1.90.0 或更高版本
cargo --version  # 应显示 cargo 1.90.0 或更高版本
```

### 1.2 工具链管理

```bash
# 安装最新稳定版
rustup install stable

# 安装特定版本
rustup install 1.90.0

# 设置默认工具链
rustup default stable

# 查看已安装工具链
rustup show

# 更新工具链
rustup update
```

**项目特定工具链 (`rust-toolchain.toml`)**:

```toml
# rust-toolchain.toml
[toolchain]
channel = "1.90.0"
components = ["rustfmt", "clippy", "rust-analyzer"]
targets = ["x86_64-unknown-linux-gnu", "wasm32-unknown-unknown"]
```

### 1.3 组件安装

```bash
# 安装核心组件
rustup component add rustfmt      # 代码格式化
rustup component add clippy       # Linter
rustup component add rust-analyzer # IDE 支持
rustup component add llvm-tools-preview # Profiling 工具

# 安装目标平台
rustup target add x86_64-unknown-linux-musl  # 静态链接 Linux
rustup target add wasm32-unknown-unknown     # WebAssembly
rustup target add aarch64-unknown-linux-gnu  # ARM64 Linux
```

### 1.4 Cargo 配置优化

创建 `~/.cargo/config.toml`:

```toml
# ~/.cargo/config.toml

# 使用国内镜像加速 (可选)
[source.crates-io]
replace-with = 'ustc'

[source.ustc]
registry = "sparse+https://mirrors.ustc.edu.cn/crates.io-index/"

# 或使用清华镜像
# [source.tuna]
# registry = "https://mirrors.tuna.tsinghua.edu.cn/git/crates.io-index.git"

# 编译优化
[build]
jobs = 8                 # 并行编译任务数
incremental = true       # 增量编译
pipelining = true        # 流水线编译

# 目标特定配置
[target.x86_64-unknown-linux-gnu]
linker = "clang"
rustflags = ["-C", "link-arg=-fuse-ld=lld"]  # 使用 lld 链接器加速

# 开发环境优化
[profile.dev]
opt-level = 0            # 不优化, 快速编译
debug = true
split-debuginfo = "unpacked"

# 生产环境优化
[profile.release]
opt-level = 3            # 最高优化
lto = "thin"             # 链接时优化
codegen-units = 1        # 单一代码生成单元, 更好的优化
strip = true             # 移除调试符号
panic = "abort"          # Panic 时直接 abort

# 注册表配置
[registries.crates-io]
protocol = "sparse"      # 使用稀疏协议加速
```

---

## 2. IDE 与编辑器配置

### 2.1 Visual Studio Code

**必装扩展**:

```bash
# 安装 VS Code 扩展 (命令行)
code --install-extension rust-lang.rust-analyzer
code --install-extension tamasfe.even-better-toml
code --install-extension serayuzgur.crates
code --install-extension vadimcn.vscode-lldb
```

**VS Code 设置 (`.vscode/settings.json`)**:

```json
{
  "rust-analyzer.checkOnSave.command": "clippy",
  "rust-analyzer.checkOnSave.extraArgs": ["--all-targets"],
  "rust-analyzer.cargo.features": "all",
  "rust-analyzer.procMacro.enable": true,
  "rust-analyzer.inlayHints.typeHints.enable": true,
  "rust-analyzer.inlayHints.parameterHints.enable": true,
  "rust-analyzer.completion.autoimport.enable": true,
  "editor.formatOnSave": true,
  "editor.defaultFormatter": "rust-lang.rust-analyzer",
  "[rust]": {
    "editor.rulers": [100],
    "editor.tabSize": 4
  },
  "files.watcherExclude": {
    "**/target/**": true
  }
}
```

**调试配置 (`.vscode/launch.json`)**:

```json
{
  "version": "0.2.0",
  "configurations": [
    {
      "type": "lldb",
      "request": "launch",
      "name": "Debug Rust Binary",
      "cargo": {
        "args": ["build", "--bin=my-app", "--package=my-package"]
      },
      "args": [],
      "cwd": "${workspaceFolder}",
      "env": {
        "RUST_LOG": "debug",
        "OTEL_EXPORTER_OTLP_ENDPOINT": "http://localhost:4317"
      }
    }
  ]
}
```

### 2.2 JetBrains RustRover / IntelliJ IDEA

**安装**:

- 下载 [RustRover](https://www.jetbrains.com/rust/) 或
- 在 IntelliJ IDEA 中安装 Rust 插件

**推荐设置**:

- **Editor → Code Style → Rust**: 使用 `rustfmt` 格式
- **Tools → Rust → External Linters**: 启用 Clippy
- **Build, Execution, Deployment → Cargo**: 启用 "Use offline mode" (离线模式)

### 2.3 Vim/Neovim

**使用 coc.nvim**:

```vim
" ~/.config/nvim/init.vim 或 ~/.vimrc

" 安装 coc-rust-analyzer
:CocInstall coc-rust-analyzer

" 配置 coc-settings.json
{
  "rust-analyzer.checkOnSave.command": "clippy",
  "rust-analyzer.cargo.loadOutDirsFromCheck": true,
  "rust-analyzer.procMacro.enable": true
}
```

**或使用 rust.vim + ALE**:

```vim
Plug 'rust-lang/rust.vim'
Plug 'dense-analysis/ale'

let g:rustfmt_autosave = 1
let g:ale_linters = {'rust': ['analyzer', 'cargo']}
let g:ale_fixers = {'rust': ['rustfmt']}
let g:ale_rust_cargo_use_clippy = 1
```

### 2.4 Helix Editor

Helix 原生支持 Rust 和 rust-analyzer:

```bash
# 安装 Helix
brew install helix  # macOS
# 或从 https://helix-editor.com/ 下载

# 确保 rust-analyzer 在 PATH 中
rustup component add rust-analyzer
```

---

## 3. OpenTelemetry 依赖配置

### 3.1 核心依赖

**Cargo.toml**:

```toml
[package]
name = "my-otlp-app"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# OpenTelemetry 核心
opentelemetry = { version = "0.31", features = ["trace", "metrics", "logs"] }
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio", "trace", "metrics", "logs"] }
opentelemetry-otlp = { version = "0.31", features = ["grpc-tonic", "http-proto", "metrics", "logs", "trace"] }

# 异步运行时
tokio = { version = "1.41", features = ["full"] }
# 或使用 async-std
# async-std = { version = "1.13", features = ["attributes"] }

# HTTP 客户端/服务器
axum = "0.7"              # Web 框架
reqwest = { version = "0.12", features = ["json", "rustls-tls"] }
tonic = "0.12"            # gRPC

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 错误处理
anyhow = "1.0"
thiserror = "2.0"

# 日志集成
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.31"

# 配置管理
config = "0.14"
dotenvy = "0.15"

# 时间处理
chrono = { version = "0.4", features = ["serde"] }

[dev-dependencies]
criterion = "0.5"         # 基准测试
tokio-test = "0.4"
mockito = "1.5"

[profile.dev]
opt-level = 0

[profile.release]
opt-level = 3
lto = "thin"
codegen-units = 1
```

### 3.2 可选特性说明

**OpenTelemetry 特性**:

| 特性 | 说明 |
|------|------|
| `trace` | Tracing API |
| `metrics` | Metrics API |
| `logs` | Logs API |
| `rt-tokio` | Tokio 运行时 |
| `rt-async-std` | async-std 运行时 |
| `grpc-tonic` | gRPC 传输 (推荐) |
| `http-proto` | HTTP 传输 |
| `reqwest-blocking` | 同步 HTTP 客户端 |
| `reqwest-rustls` | 使用 rustls 的 TLS |

**推荐组合**:

```toml
# 生产环境 (gRPC + Tokio + 全特性)
opentelemetry = "0.31"
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio", "trace", "metrics", "logs"] }
opentelemetry-otlp = { version = "0.31", features = ["grpc-tonic", "metrics", "logs", "trace"] }

# 轻量级 (仅 Tracing + HTTP)
opentelemetry = { version = "0.31", features = ["trace"] }
opentelemetry_sdk = { version = "0.31", features = ["rt-tokio", "trace"] }
opentelemetry-otlp = { version = "0.31", features = ["http-proto", "trace"] }
```

### 3.3 依赖版本锁定

**生成 Cargo.lock**:

```bash
# 生成精确的依赖版本锁文件
cargo generate-lockfile

# 更新依赖到兼容的最新版本
cargo update

# 更新特定依赖
cargo update -p opentelemetry

# 检查过期依赖
cargo install cargo-outdated
cargo outdated
```

---

## 4. 代码质量工具

### 4.1 Clippy (Linter)

```bash
# 运行 Clippy
cargo clippy

# 所有目标 (包括测试、基准测试)
cargo clippy --all-targets

# 严格模式
cargo clippy -- -D warnings

# 修复自动修复的问题
cargo clippy --fix
```

**项目 Clippy 配置 (`.clippy.toml`)**:

```toml
# .clippy.toml
avoid-breaking-exported-api = false
cognitive-complexity-threshold = 30

# 禁用特定 lint
disallowed-names = ["foo", "bar", "baz"]
```

**CI 中使用**:

```yaml
# .github/workflows/ci.yml
- name: Clippy
  run: cargo clippy --all-targets -- -D warnings
```

### 4.2 Rustfmt (代码格式化)

```bash
# 格式化项目
cargo fmt

# 检查格式 (不修改)
cargo fmt -- --check
```

**项目格式化配置 (`rustfmt.toml`)**:

```toml
# rustfmt.toml
edition = "2021"
max_width = 100
hard_tabs = false
tab_spaces = 4
newline_style = "Unix"
use_small_heuristics = "Default"
reorder_imports = true
reorder_modules = true
remove_nested_parens = true
```

### 4.3 Cargo Audit (安全审计)

```bash
# 安装
cargo install cargo-audit

# 运行安全审计
cargo audit

# 修复已知漏洞
cargo audit fix
```

**CI 集成**:

```yaml
- name: Security Audit
  run: cargo audit
```

### 4.4 Cargo Deny (依赖检查)

```bash
# 安装
cargo install cargo-deny

# 检查许可证、安全、禁用依赖
cargo deny check
```

**配置 (`deny.toml`)**:

```toml
# deny.toml
[licenses]
allow = ["MIT", "Apache-2.0", "BSD-3-Clause"]

[bans]
multiple-versions = "warn"
deny = [
    { name = "openssl-sys" }  # 禁用 OpenSSL, 强制使用 rustls
]

[advisories]
vulnerability = "deny"
unmaintained = "warn"
```

---

## 5. 调试与分析工具

### 5.1 LLDB / GDB 调试器

**LLDB (推荐)**:

```bash
# macOS/Linux
rustup component add llvm-tools-preview

# 使用 rust-lldb
rust-lldb ./target/debug/my-app

# 设置断点
(lldb) breakpoint set --name main
(lldb) run
(lldb) print variable_name
```

**GDB**:

```bash
# Linux
rust-gdb ./target/debug/my-app

# 美化输出
(gdb) set print pretty on
```

### 5.2 Tokio Console (异步调试)

**安装**:

```bash
cargo install tokio-console
```

**应用配置**:

```toml
[dependencies]
tokio = { version = "1.41", features = ["full", "tracing"] }
console-subscriber = "0.4"
```

```rust
fn main() {
    console_subscriber::init();
    
    let rt = tokio::runtime::Runtime::new().unwrap();
    rt.block_on(async {
        // 你的异步代码
    });
}
```

**运行**:

```bash
# 启动应用
RUSTFLAGS="--cfg tokio_unstable" cargo run

# 另一个终端启动 Console
tokio-console
```

### 5.3 Cargo Flamegraph (性能分析)

```bash
# 安装
cargo install flamegraph

# 生成火焰图
cargo flamegraph --bin my-app

# 指定采样频率
cargo flamegraph --freq 999 --bin my-app
```

### 5.4 Valgrind / Heaptrack (内存分析)

**Valgrind (Linux)**:

```bash
# 内存泄漏检测
valgrind --leak-check=full ./target/debug/my-app

# Cachegrind (缓存分析)
valgrind --tool=cachegrind ./target/debug/my-app
```

**Heaptrack (Linux)**:

```bash
# 安装
sudo apt install heaptrack  # Ubuntu/Debian

# 运行
heaptrack ./target/debug/my-app
heaptrack_gui heaptrack.my-app.*.gz
```

---

## 6. 测试环境配置

### 6.1 单元测试配置

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use opentelemetry::global;
    use opentelemetry_sdk::testing::trace::InMemorySpanExporter;

    #[test]
    fn test_with_tracing() {
        // 测试专用 exporter
        let exporter = InMemorySpanExporter::default();
        let provider = opentelemetry_sdk::trace::TracerProvider::builder()
            .with_simple_exporter(exporter.clone())
            .build();
        
        global::set_tracer_provider(provider);
        
        // 你的测试逻辑
        
        // 验证 spans
        let spans = exporter.get_finished_spans().unwrap();
        assert_eq!(spans.len(), 1);
    }
}
```

### 6.2 集成测试环境

**Testcontainers for Rust**:

```toml
[dev-dependencies]
testcontainers = "0.23"
```

```rust
// tests/integration_test.rs
use testcontainers::{clients, images};

#[tokio::test]
async fn test_with_real_collector() {
    let docker = clients::Cli::default();
    let collector = docker.run(images::generic::GenericImage::new(
        "otel/opentelemetry-collector",
        "0.111.0"
    ).with_exposed_port(4317));
    
    let port = collector.get_host_port_ipv4(4317);
    let endpoint = format!("http://localhost:{}", port);
    
    // 使用真实 Collector 进行测试
}
```

### 6.3 测试覆盖率

**Tarpaulin**:

```bash
# 安装
cargo install cargo-tarpaulin

# 生成覆盖率报告
cargo tarpaulin --out Html

# CI 集成
cargo tarpaulin --out Xml
```

**LLVM Coverage (内置)**:

```bash
# 安装组件
rustup component add llvm-tools-preview
cargo install cargo-llvm-cov

# 生成覆盖率
cargo llvm-cov --html
```

---

## 7. 本地 OTLP 基础设施

### 7.1 OpenTelemetry Collector

**collector-config.yaml**:

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318

processors:
  batch:
    timeout: 10s
    send_batch_size: 1024
  
  memory_limiter:
    check_interval: 1s
    limit_mib: 512

exporters:
  logging:
    loglevel: debug
  
  jaeger:
    endpoint: jaeger:14250
    tls:
      insecure: true
  
  prometheus:
    endpoint: "0.0.0.0:8889"

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch, memory_limiter]
      exporters: [logging, jaeger]
    
    metrics:
      receivers: [otlp]
      processors: [batch]
      exporters: [logging, prometheus]
    
    logs:
      receivers: [otlp]
      processors: [batch]
      exporters: [logging]
```

### 7.2 Jaeger 后端

```bash
# 使用 Docker 启动
docker run -d --name jaeger \
  -p 16686:16686 \
  -p 14250:14250 \
  jaegertracing/all-in-one:1.62

# 访问 UI: http://localhost:16686
```

### 7.3 Prometheus + Grafana

**prometheus.yml**:

```yaml
global:
  scrape_interval: 15s

scrape_configs:
  - job_name: 'otel-collector'
    static_configs:
      - targets: ['collector:8889']
```

```bash
# 启动 Prometheus
docker run -d --name prometheus \
  -p 9090:9090 \
  -v $(pwd)/prometheus.yml:/etc/prometheus/prometheus.yml \
  prom/prometheus

# 启动 Grafana
docker run -d --name grafana \
  -p 3000:3000 \
  grafana/grafana
```

### 7.4 完整开发栈 (Docker Compose)

**docker-compose.yml**:

```yaml
version: '3.8'

services:
  # OpenTelemetry Collector
  collector:
    image: otel/opentelemetry-collector:0.111.0
    command: ["--config=/etc/otel-collector-config.yaml"]
    volumes:
      - ./collector-config.yaml:/etc/otel-collector-config.yaml
    ports:
      - "4317:4317"   # OTLP gRPC
      - "4318:4318"   # OTLP HTTP
      - "8889:8889"   # Prometheus metrics
    networks:
      - otel

  # Jaeger
  jaeger:
    image: jaegertracing/all-in-one:1.62
    ports:
      - "16686:16686"  # UI
      - "14250:14250"  # gRPC
    networks:
      - otel

  # Prometheus
  prometheus:
    image: prom/prometheus:latest
    command:
      - '--config.file=/etc/prometheus/prometheus.yml'
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml
    ports:
      - "9090:9090"
    networks:
      - otel

  # Grafana
  grafana:
    image: grafana/grafana:latest
    ports:
      - "3000:3000"
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=admin
    networks:
      - otel

networks:
  otel:
    driver: bridge
```

**启动**:

```bash
docker-compose up -d

# 查看日志
docker-compose logs -f collector
```

---

## 8. 环境变量配置

### 8.1 开发环境变量

```bash
# 设置 Rust 日志级别
export RUST_LOG=debug,opentelemetry=trace

# OTLP Endpoint
export OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317

# 服务名称
export OTEL_SERVICE_NAME=my-rust-service

# 资源属性
export OTEL_RESOURCE_ATTRIBUTES=service.version=0.1.0,deployment.environment=dev

# 禁用 TLS (开发环境)
export OTEL_EXPORTER_OTLP_INSECURE=true
```

### 8.2 使用 dotenv

**安装**:

```toml
[dependencies]
dotenvy = "0.15"
```

**.env**:

```env
RUST_LOG=debug
OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317
OTEL_SERVICE_NAME=my-rust-service
OTEL_RESOURCE_ATTRIBUTES=service.version=0.1.0,deployment.environment=dev
```

**加载**:

```rust
use dotenvy::dotenv;

fn main() {
    dotenv().ok();  // 加载 .env 文件
    
    let endpoint = std::env::var("OTEL_EXPORTER_OTLP_ENDPOINT")
        .unwrap_or_else(|_| "http://localhost:4317".to_string());
    
    println!("OTLP Endpoint: {}", endpoint);
}
```

---

## 9. 项目模板与脚手架

### 9.1 使用 Cargo Generate

```bash
# 安装 cargo-generate
cargo install cargo-generate

# 从模板创建项目
cargo generate --git https://github.com/rust-lang/cargo-generate-template
```

### 9.2 自定义项目模板

**创建模板仓库 `rust-otlp-template`**:

```text
rust-otlp-template/
├── Cargo.toml
├── src/
│   └── main.rs
├── .env.example
├── docker-compose.yml
├── collector-config.yaml
├── rustfmt.toml
├── .clippy.toml
└── README.md
```

**使用模板**:

```bash
cargo generate --git https://github.com/your-org/rust-otlp-template --name my-new-service
```

---

## 10. 持续集成配置

### 10.1 GitHub Actions

**.github/workflows/ci.yml**:

```yaml
name: CI

on:
  push:
    branches: [main]
  pull_request:

env:
  RUST_VERSION: "1.90"

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
        with:
          toolchain: ${{ env.RUST_VERSION }}
          components: rustfmt, clippy
      
      - name: Cache
        uses: actions/cache@v4
        with:
          path: |
            ~/.cargo/registry
            ~/.cargo/git
            target
          key: ${{ runner.os }}-cargo-${{ hashFiles('**/Cargo.lock') }}
      
      - name: Format
        run: cargo fmt -- --check
      
      - name: Clippy
        run: cargo clippy --all-targets -- -D warnings
      
      - name: Test
        run: cargo test --all-features
      
      - name: Build
        run: cargo build --release

  security:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Audit
        uses: actions-rs/audit-check@v1
        with:
          token: ${{ secrets.GITHUB_TOKEN }}
```

### 10.2 GitLab CI

**.gitlab-ci.yml**:

```yaml
image: rust:1.90

stages:
  - test
  - build

variables:
  CARGO_HOME: $CI_PROJECT_DIR/.cargo

cache:
  paths:
    - .cargo/
    - target/

test:
  stage: test
  script:
    - rustc --version
    - cargo --version
    - cargo fmt -- --check
    - cargo clippy -- -D warnings
    - cargo test --all-features

build:
  stage: build
  script:
    - cargo build --release
  artifacts:
    paths:
      - target/release/my-app
    expire_in: 1 week
```

---

## 11. 故障排查

### 11.1 Rustup 问题

**问题: `rustup` 命令未找到**

```bash
# 确保 PATH 包含 ~/.cargo/bin
echo 'export PATH="$HOME/.cargo/bin:$PATH"' >> ~/.bashrc
source ~/.bashrc
```

**问题: 工具链损坏**:

```bash
rustup self update
rustup update
```

### 11.2 编译问题

**问题: 链接错误 (Linux)**:

```bash
# 安装构建依赖
sudo apt install build-essential pkg-config libssl-dev  # Ubuntu/Debian
sudo yum install gcc openssl-devel  # CentOS/RHEL
```

**问题: OpenSSL 相关错误**:

```toml
# 使用 rustls 替代 openssl
reqwest = { version = "0.12", features = ["rustls-tls"], default-features = false }
```

**问题: 编译速度慢**:

```bash
# 使用 mold 链接器 (Linux)
sudo apt install mold
export RUSTFLAGS="-C link-arg=-fuse-ld=mold"

# 或使用 lld
sudo apt install lld
export RUSTFLAGS="-C link-arg=-fuse-ld=lld"
```

### 11.3 IDE 问题

**问题: rust-analyzer 无响应**:

```bash
# 清理缓存
rm -rf ~/.cache/rust-analyzer
rm -rf target/

# 重新构建
cargo clean
cargo build
```

**问题: VS Code 中类型提示不工作**:

```json
// settings.json
{
  "rust-analyzer.procMacro.enable": true,
  "rust-analyzer.cargo.loadOutDirsFromCheck": true
}
```

### 11.4 OTLP 连接问题

**问题: 连接被拒绝**:

```bash
# 检查 Collector 是否运行
docker ps | grep collector

# 检查端口
netstat -an | grep 4317

# 测试连接
telnet localhost 4317
```

**问题: TLS 握手失败**:

```rust
// 开发环境禁用 TLS 验证
let exporter = SpanExporter::builder()
    .with_tonic()
    .with_endpoint("http://localhost:4317")  // 注意: http 而非 https
    .build()?;
```

---

## 12. 最佳实践清单

- ✅ **版本控制**: 使用 `rust-toolchain.toml` 固定 Rust 版本
- ✅ **依赖管理**: 定期运行 `cargo update` 和 `cargo audit`
- ✅ **代码格式**: 强制执行 `cargo fmt` (CI 检查)
- ✅ **Linter**: 启用 `cargo clippy` 并修复所有警告
- ✅ **测试覆盖**: 保持 > 80% 测试覆盖率
- ✅ **安全审计**: CI 中运行 `cargo audit` 和 `cargo deny`
- ✅ **文档**: 为公开 API 编写 rustdoc 文档
- ✅ **性能分析**: 定期使用 flamegraph 和 criterion
- ✅ **异步调试**: 集成 tokio-console
- ✅ **本地环境**: 使用 Docker Compose 统一开发环境
- ✅ **环境变量**: 使用 `.env` 文件管理配置
- ✅ **错误处理**: 使用 `anyhow` (应用) 和 `thiserror` (库)
- ✅ **日志**: 集成 `tracing` 和 OpenTelemetry

---

## 参考资源

**官方文档**:

- [Rust 官方网站](https://www.rust-lang.org/)
- [Rust Book](https://doc.rust-lang.org/book/)
- [OpenTelemetry Rust](https://github.com/open-telemetry/opentelemetry-rust)

**工具**:

- [Rustup](https://rustup.rs/)
- [Cargo Book](https://doc.rust-lang.org/cargo/)
- [rust-analyzer](https://rust-analyzer.github.io/)

**社区**:

- [Rust Users Forum](https://users.rust-lang.org/)
- [r/rust](https://www.reddit.com/r/rust/)
- [Rust Discord](https://discord.gg/rust-lang)

---

**创建日期**: 2025年10月11日  
**维护团队**: OTLP Rust Documentation Team  
**License**: MIT
