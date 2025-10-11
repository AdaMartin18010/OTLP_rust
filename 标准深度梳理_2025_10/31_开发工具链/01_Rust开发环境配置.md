# 🛠️ Rust 开发环境配置完整指南 - OTLP 开发专用

> **目标读者**: Rust 初学者和中级开发者  
> **Rust 版本**: 1.90+  
> **系统支持**: Linux, macOS, Windows  
> **最后更新**: 2025年10月10日

---

## 📋 目录

- [🛠️ Rust 开发环境配置完整指南 - OTLP 开发专用](#️-rust-开发环境配置完整指南---otlp-开发专用)
  - [📋 目录](#-目录)
  - [1. Rust 工具链安装](#1-rust-工具链安装)
    - [1.1 安装 Rustup](#11-安装-rustup)
    - [1.2 验证安装](#12-验证安装)
    - [1.3 配置 Rust 工具链](#13-配置-rust-工具链)
      - [设置默认工具链](#设置默认工具链)
      - [安装必要组件](#安装必要组件)
    - [1.4 配置 Cargo](#14-配置-cargo)
  - [2. IDE 配置](#2-ide-配置)
    - [2.1 VS Code (推荐)](#21-vs-code-推荐)
      - [必装插件](#必装插件)
      - [VS Code 配置](#vs-code-配置)
      - [调试配置](#调试配置)
    - [2.2 IntelliJ IDEA / CLion](#22-intellij-idea--clion)
      - [安装插件](#安装插件)
      - [配置](#配置)
    - [2.3 其他 IDE](#23-其他-ide)
  - [3. 代码质量工具](#3-代码质量工具)
    - [3.1 Rustfmt (代码格式化)](#31-rustfmt-代码格式化)
      - [配置文件](#配置文件)
      - [使用](#使用)
    - [3.2 Clippy (代码检查)](#32-clippy-代码检查)
      - [3.2.1 配置](#321-配置)
      - [3.2.2 使用](#322-使用)
      - [自定义 Lint 级别](#自定义-lint-级别)
    - [3.3 Cargo Check](#33-cargo-check)
  - [4. OTLP 开发专用工具](#4-otlp-开发专用工具)
    - [4.1 本地测试环境](#41-本地测试环境)
      - [方法1: 使用 Jaeger (推荐)](#方法1-使用-jaeger-推荐)
      - [方法2: 使用 OpenTelemetry Collector](#方法2-使用-opentelemetry-collector)
    - [4.2 开发辅助工具](#42-开发辅助工具)
      - [cargo-watch (自动重新编译)](#cargo-watch-自动重新编译)
      - [cargo-expand (宏展开)](#cargo-expand-宏展开)
      - [cargo-edit (管理依赖)](#cargo-edit-管理依赖)
      - [cargo-udeps (查找未使用依赖)](#cargo-udeps-查找未使用依赖)
  - [5. 调试工具](#5-调试工具)
    - [5.1 GDB / LLDB](#51-gdb--lldb)
      - [LLDB 基本命令](#lldb-基本命令)
    - [5.2 使用 `dbg!` 宏](#52-使用-dbg-宏)
    - [5.3 日志调试](#53-日志调试)
  - [6. 性能分析工具](#6-性能分析工具)
    - [6.1 Criterion (基准测试)](#61-criterion-基准测试)
      - [安装和配置](#安装和配置)
      - [创建基准测试](#创建基准测试)
      - [运行](#运行)
    - [6.2 Flamegraph (火焰图)](#62-flamegraph-火焰图)
    - [6.3 Valgrind (内存检查)](#63-valgrind-内存检查)
    - [6.4 cargo-instruments (macOS)](#64-cargo-instruments-macos)
  - [7. 完整开发工作流](#7-完整开发工作流)
    - [7.1 项目初始化](#71-项目初始化)
    - [7.2 日常开发流程](#72-日常开发流程)
    - [7.3 性能优化流程](#73-性能优化流程)
    - [7.4 发布流程](#74-发布流程)
  - [📊 工具对比](#-工具对比)
  - [🔗 参考资源](#-参考资源)

---

## 1. Rust 工具链安装

### 1.1 安装 Rustup

**Linux / macOS**:

```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

**Windows**:

1. 下载: <https://rustup.rs/>
2. 运行 `rustup-init.exe`
3. 选择默认安装

### 1.2 验证安装

```bash
rustc --version
# 输出: rustc 1.90.0 (或更高)

cargo --version
# 输出: cargo 1.90.0 (或更高)
```

### 1.3 配置 Rust 工具链

#### 设置默认工具链

```bash
# 使用稳定版（推荐）
rustup default stable

# 更新到最新版本
rustup update
```

#### 安装必要组件

```bash
# Rust源码（用于跳转到标准库定义）
rustup component add rust-src

# Rust Analyzer（LSP支持）
rustup component add rust-analyzer

# 代码格式化工具
rustup component add rustfmt

# 代码检查工具
rustup component add clippy
```

### 1.4 配置 Cargo

创建 `~/.cargo/config.toml`：

```toml
# 使用国内镜像加速（可选，中国用户推荐）
[source.crates-io]
replace-with = 'ustc'

[source.ustc]
registry = "sparse+https://mirrors.ustc.edu.cn/crates.io-index/"

# 或使用清华镜像
[source.tuna]
registry = "https://mirrors.tuna.tsinghua.edu.cn/git/crates.io-index.git"

# 编译优化
[build]
# 使用所有CPU核心
jobs = 8  # 根据你的CPU核心数调整

# 增量编译（加快重新编译速度）
incremental = true

# 目标目录（可选，统一放置编译产物）
target-dir = "/path/to/global/target"

# Release 编译优化
[profile.release]
lto = true              # 链接时优化
codegen-units = 1       # 更好的优化，但编译更慢
opt-level = 3           # 最高优化级别
strip = true            # 移除调试符号

# Dev 编译优化（开发时更快）
[profile.dev]
opt-level = 0           # 不优化
debug = true            # 包含调试信息
split-debuginfo = "unpacked"  # 加快链接速度（macOS）
```

---

## 2. IDE 配置

### 2.1 VS Code (推荐)

#### 必装插件

1. **rust-analyzer** (matklad.rust-analyzer)
   - 智能补全
   - 代码跳转
   - 实时错误检查

2. **CodeLLDB** (vadimcn.vscode-lldb)
   - 调试支持
   - 断点、变量查看

3. **crates** (serayuzgur.crates)
   - 依赖版本管理
   - 自动更新提示

4. **Even Better TOML** (tamasfe.even-better-toml)
   - Cargo.toml 语法高亮
   - 自动补全

5. **Error Lens** (usernamehw.errorlens)
   - 内联显示错误
   - 更好的可见性

#### VS Code 配置

创建 `.vscode/settings.json`:

```json
{
  // Rust Analyzer 配置
  "rust-analyzer.checkOnSave.command": "clippy",
  "rust-analyzer.cargo.allFeatures": true,
  "rust-analyzer.procMacro.enable": true,
  "rust-analyzer.inlayHints.enable": true,
  "rust-analyzer.lens.enable": true,
  
  // 代码格式化
  "[rust]": {
    "editor.formatOnSave": true,
    "editor.defaultFormatter": "rust-lang.rust-analyzer"
  },
  
  // 文件关联
  "files.associations": {
    "*.rs": "rust",
    "Cargo.toml": "toml",
    "Cargo.lock": "toml"
  },
  
  // 终端配置
  "terminal.integrated.env.linux": {
    "RUST_BACKTRACE": "1"
  },
  "terminal.integrated.env.osx": {
    "RUST_BACKTRACE": "1"
  },
  "terminal.integrated.env.windows": {
    "RUST_BACKTRACE": "1"
  }
}
```

#### 调试配置

创建 `.vscode/launch.json`:

```json
{
  "version": "0.2.0",
  "configurations": [
    {
      "type": "lldb",
      "request": "launch",
      "name": "Debug executable",
      "cargo": {
        "args": [
          "build",
          "--bin=${workspaceFolderBasename}",
          "--package=${workspaceFolderBasename}"
        ],
        "filter": {
          "name": "${workspaceFolderBasename}",
          "kind": "bin"
        }
      },
      "args": [],
      "cwd": "${workspaceFolder}",
      "env": {
        "RUST_BACKTRACE": "1",
        "RUST_LOG": "debug"
      }
    },
    {
      "type": "lldb",
      "request": "launch",
      "name": "Debug unit tests",
      "cargo": {
        "args": [
          "test",
          "--no-run",
          "--lib",
          "--package=${workspaceFolderBasename}"
        ],
        "filter": {
          "name": "${workspaceFolderBasename}",
          "kind": "lib"
        }
      },
      "args": [],
      "cwd": "${workspaceFolder}",
      "env": {
        "RUST_BACKTRACE": "1"
      }
    }
  ]
}
```

### 2.2 IntelliJ IDEA / CLion

#### 安装插件

- **Rust Plugin** (官方)
- **TOML** 支持

#### 配置

1. Settings → Languages & Frameworks → Rust
2. 选择 Rust 工具链路径
3. 启用 Cargo 检查
4. 启用外部 linter (clippy)

### 2.3 其他 IDE

- **Vim/Neovim**: 使用 `coc-rust-analyzer` 或 `nvim-lspconfig`
- **Emacs**: 使用 `rust-mode` + `lsp-mode`
- **Sublime Text**: 使用 `rust-enhanced` + `LSP`

---

## 3. 代码质量工具

### 3.1 Rustfmt (代码格式化)

#### 配置文件

创建 `rustfmt.toml`:

```toml
# 基础设置
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
format_macro_matchers = true
format_strings = true
normalize_comments = true
normalize_doc_attributes = true
wrap_comments = true
comment_width = 80

# 链式调用
chain_width = 80
fn_call_width = 80
attr_fn_like_width = 80
struct_lit_width = 80
struct_variant_width = 80
array_width = 80
```

#### 使用

```bash
# 格式化整个项目
cargo fmt

# 检查格式（CI中使用）
cargo fmt -- --check

# 格式化单个文件
rustfmt src/main.rs
```

### 3.2 Clippy (代码检查)

#### 3.2.1 配置

创建 `.clippy.toml`:

```toml
# 最大复杂度
cognitive-complexity-threshold = 30
cyclomatic-complexity-threshold = 30

# 类型检查
type-complexity-threshold = 250

# 性能相关
too-many-arguments-threshold = 7
too-many-lines-threshold = 300

# 命名约定
enum-variant-name-threshold = 3
```

#### 3.2.2 使用

```bash
# 运行 clippy
cargo clippy

# 所有target和feature
cargo clippy --all-targets --all-features

# 自动修复
cargo clippy --fix

# 严格模式（CI中使用）
cargo clippy -- -D warnings

# 推荐的CI命令
cargo clippy --all-targets --all-features -- -D warnings -D clippy::all
```

#### 自定义 Lint 级别

在 `src/main.rs` 或 `lib.rs` 顶部：

```rust
// 禁止特定 lint
#![allow(clippy::too_many_arguments)]

// 警告级别
#![warn(clippy::pedantic)]

// 错误级别
#![deny(clippy::correctness)]

// 推荐的配置
#![warn(
    missing_docs,
    missing_debug_implementations,
    rust_2018_idioms,
    unreachable_pub,
    unused_qualifications
)]
```

### 3.3 Cargo Check

```bash
# 快速检查（不生成可执行文件）
cargo check

# 检查所有targets
cargo check --all-targets

# 检查所有features
cargo check --all-features
```

---

## 4. OTLP 开发专用工具

### 4.1 本地测试环境

#### 方法1: 使用 Jaeger (推荐)

```bash
# 启动 Jaeger All-in-One
docker run -d --name jaeger \
  -e COLLECTOR_OTLP_ENABLED=true \
  -p 4317:4317 \
  -p 4318:4318 \
  -p 16686:16686 \
  jaegertracing/all-in-one:latest

# 访问 UI: http://localhost:16686
```

#### 方法2: 使用 OpenTelemetry Collector

创建 `otel-collector-config.yaml`:

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

exporters:
  logging:
    loglevel: debug
  jaeger:
    endpoint: jaeger:14250
    tls:
      insecure: true

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [logging, jaeger]
```

启动:

```bash
docker run -d --name otel-collector \
  -p 4317:4317 \
  -p 4318:4318 \
  -v $(pwd)/otel-collector-config.yaml:/etc/otel-collector-config.yaml \
  otel/opentelemetry-collector:latest \
  --config=/etc/otel-collector-config.yaml
```

### 4.2 开发辅助工具

#### cargo-watch (自动重新编译)

```bash
# 安装
cargo install cargo-watch

# 使用
cargo watch -x run
cargo watch -x test
cargo watch -x clippy
```

#### cargo-expand (宏展开)

```bash
# 安装
cargo install cargo-expand

# 使用
cargo expand

# 展开特定模块
cargo expand module::path
```

#### cargo-edit (管理依赖)

```bash
# 安装
cargo install cargo-edit

# 添加依赖
cargo add opentelemetry
cargo add --dev criterion

# 升级依赖
cargo upgrade

# 删除依赖
cargo rm some_crate
```

#### cargo-udeps (查找未使用依赖)

```bash
# 安装（需要 nightly）
cargo install cargo-udeps --locked

# 使用
cargo +nightly udeps
```

---

## 5. 调试工具

### 5.1 GDB / LLDB

#### LLDB 基本命令

```bash
# 编译并启动调试器
cargo build
lldb ./target/debug/myapp

# 常用命令
(lldb) b main                # 设置断点
(lldb) r                     # 运行程序
(lldb) n                     # 下一行
(lldb) s                     # 步入
(lldb) c                     # 继续
(lldb) p variable            # 打印变量
(lldb) bt                    # 回溯栈
(lldb) q                     # 退出
```

### 5.2 使用 `dbg!` 宏

```rust
fn main() {
    let x = 5;
    let y = 10;
    
    // 打印表达式和值
    dbg!(x);
    dbg!(x + y);
    
    // 不影响所有权
    let result = dbg!(some_function());
}
```

### 5.3 日志调试

```rust
use tracing::{debug, info, warn, error};
use tracing_subscriber;

fn main() {
    // 初始化日志
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::DEBUG)
        .init();
    
    info!("应用启动");
    debug!(user_id = 123, "处理用户请求");
    warn!("配置缺失，使用默认值");
    error!(error = ?err, "操作失败");
}
```

---

## 6. 性能分析工具

### 6.1 Criterion (基准测试)

#### 安装和配置

`Cargo.toml`:

```toml
[dev-dependencies]
criterion = { version = "0.5", features = ["html_reports"] }

[[bench]]
name = "my_benchmark"
harness = false
```

#### 创建基准测试

`benches/my_benchmark.rs`:

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn fibonacci(n: u64) -> u64 {
    match n {
        0 => 1,
        1 => 1,
        n => fibonacci(n-1) + fibonacci(n-2),
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("fib 20", |b| b.iter(|| fibonacci(black_box(20))));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
```

#### 运行

```bash
cargo bench
```

### 6.2 Flamegraph (火焰图)

```bash
# 安装
cargo install flamegraph

# Linux 需要 perf
sudo apt-get install linux-tools-common linux-tools-generic

# 生成火焰图
cargo flamegraph

# 生成后查看 flamegraph.svg
```

### 6.3 Valgrind (内存检查)

```bash
# 安装 valgrind
sudo apt-get install valgrind  # Debian/Ubuntu
brew install valgrind           # macOS

# 使用
cargo build
valgrind --leak-check=full ./target/debug/myapp
```

### 6.4 cargo-instruments (macOS)

```bash
# 安装
cargo install cargo-instruments

# 使用 Xcode Instruments
cargo instruments -t time
cargo instruments -t alloc
cargo instruments -t sys
```

---

## 7. 完整开发工作流

### 7.1 项目初始化

```bash
# 创建新项目
cargo new my-otlp-service
cd my-otlp-service

# 初始化 git
git init
git add .
git commit -m "Initial commit"

# 创建配置文件
cat > rustfmt.toml << EOF
edition = "2021"
max_width = 100
EOF

cat > .clippy.toml << EOF
cognitive-complexity-threshold = 30
EOF

# 创建 .gitignore
cat > .gitignore << EOF
/target
Cargo.lock
*.swp
*.swo
.DS_Store
.vscode
.idea
EOF
```

### 7.2 日常开发流程

```bash
# 1. 开发时使用 cargo-watch
cargo watch -x check -x test -x run

# 2. 提交前检查
cargo fmt                # 格式化代码
cargo clippy --fix       # 修复 lint 问题
cargo test               # 运行测试
cargo doc --no-deps      # 生成文档

# 3. CI/CD 检查命令
cargo fmt -- --check
cargo clippy -- -D warnings
cargo test --all-features
cargo doc --no-deps --document-private-items
```

### 7.3 性能优化流程

```bash
# 1. 基准测试
cargo bench --bench my_benchmark

# 2. 生成火焰图
cargo flamegraph

# 3. 内存分析
valgrind --tool=massif ./target/debug/myapp
ms_print massif.out.*

# 4. 编译优化检查
cargo build --release
ls -lh target/release/myapp
```

### 7.4 发布流程

```bash
# 1. 更新版本号
# 编辑 Cargo.toml: version = "0.2.0"

# 2. 更新 CHANGELOG.md

# 3. 测试发布
cargo publish --dry-run

# 4. 发布到 crates.io
cargo login <token>
cargo publish

# 5. 打 git tag
git tag -a v0.2.0 -m "Release v0.2.0"
git push origin v0.2.0
```

---

## 📊 工具对比

| 工具 | 用途 | 必要性 | 替代方案 |
|------|------|--------|----------|
| rustup | Rust 版本管理 | 🔴 必须 | 无 |
| cargo | 包管理和构建 | 🔴 必须 | 无 |
| rustfmt | 代码格式化 | 🔴 必须 | 无 |
| clippy | 代码检查 | 🔴 必须 | 无 |
| rust-analyzer | LSP 支持 | 🟡 推荐 | RLS (已废弃) |
| cargo-watch | 自动重新编译 | 🟡 推荐 | 手动运行 |
| cargo-edit | 依赖管理 | 🟢 可选 | 手动编辑 |
| flamegraph | 性能分析 | 🟢 可选 | perf, valgrind |

---

## 🔗 参考资源

- [Rust 官方文档](https://doc.rust-lang.org/)
- [Rust Analyzer 手册](https://rust-analyzer.github.io/)
- [Clippy Lints 列表](https://rust-lang.github.io/rust-clippy/master/)
- [Cargo 文档](https://doc.rust-lang.org/cargo/)

---

**文档版本**: v1.0  
**创建日期**: 2025年10月10日  
**维护者**: OTLP Rust 团队

---

[🏠 返回主目录](../README.md) | [📚 快速入门](../33_教程与示例/01_Rust_OTLP_30分钟快速入门.md) | [✅ 最佳实践](../17_最佳实践清单/Rust_OTLP_最佳实践Checklist.md)
