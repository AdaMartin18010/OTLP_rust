# 📦 安装指南

**版本**: 1.0
**最后更新**: 2025年10月26日
**状态**: 🟢 活跃维护

> **简介**: 安装指南 - Rust环境、项目依赖和开发工具的完整安装说明。

---

## 📋 目录

- [📦 安装指南](#-安装指南)
  - [📋 目录](#-目录)
  - [🔧 系统要求](#-系统要求)
    - [最低要求](#最低要求)
    - [推荐配置](#推荐配置)
    - [支持的平台](#支持的平台)
  - [🦀 Rust 环境安装](#-rust-环境安装)
    - [方法 1: 使用 rustup（推荐）](#方法-1-使用-rustup推荐)
      - [Windows](#windows)
      - [macOS/Linux](#macoslinux)
    - [方法 2: 使用包管理器](#方法-2-使用包管理器)
      - [Ubuntu/Debian](#ubuntudebian)
      - [macOS](#macos)
      - [Windows1](#windows1)
    - [验证 Rust 安装](#验证-rust-安装)
  - [📥 项目安装](#-项目安装)
    - [方法 1: 从源码安装（推荐）](#方法-1-从源码安装推荐)
      - [1. 克隆仓库](#1-克隆仓库)
      - [2. 构建项目](#2-构建项目)
      - [3. 运行测试](#3-运行测试)
    - [方法 2: 使用 Cargo 安装](#方法-2-使用-cargo-安装)
    - [方法 3: 使用 crates.io（未来版本）](#方法-3-使用-cratesio未来版本)
  - [📚 依赖管理](#-依赖管理)
    - [核心依赖](#核心依赖)
    - [可选依赖](#可选依赖)
    - [特性标志](#特性标志)
    - [依赖更新](#依赖更新)
  - [✅ 验证安装](#-验证安装)
    - [1. 基础验证](#1-基础验证)
    - [2. 功能验证](#2-功能验证)
      - [运行示例](#运行示例)
      - [运行测试](#运行测试)
      - [运行基准测试](#运行基准测试)
    - [3. 集成验证](#3-集成验证)
      - [创建测试项目](#创建测试项目)
      - [测试代码](#测试代码)
      - [运行测试1](#运行测试1)
  - [❓ 常见问题](#-常见问题)
    - [Q1: Rust 版本不兼容](#q1-rust-版本不兼容)
    - [Q2: 依赖下载失败](#q2-依赖下载失败)
    - [Q3: 编译错误](#q3-编译错误)
      - [Windows2](#windows2)
      - [macOS1](#macos1)
      - [Linux](#linux)
    - [Q4: 内存不足](#q4-内存不足)
    - [Q5: 网络代理问题](#q5-网络代理问题)
    - [Q6: 权限问题](#q6-权限问题)
    - [Q7: 磁盘空间不足](#q7-磁盘空间不足)
  - [🗑️ 卸载](#️-卸载)
    - [卸载项目](#卸载项目)
    - [卸载 Rust（可选）](#卸载-rust可选)
    - [清理依赖](#清理依赖)
  - [📞 获取帮助](#-获取帮助)
    - [官方资源](#官方资源)
    - [社区支持](#社区支持)
    - [技术支持](#技术支持)
  - [📝 更新日志](#-更新日志)
    - [v0.1.0 (2025-10-20)](#v010-2025-10-20)

---

## 🔧 系统要求

### 最低要求

- **操作系统**: Windows 10+, macOS 10.15+, Linux (Ubuntu 18.04+, CentOS 7+)
- **Rust 版本**: 1.92.0 或更高版本
- **内存**: 至少 4GB RAM
- **磁盘空间**: 至少 2GB 可用空间
- **网络**: 用于下载依赖包

### 推荐配置

- **操作系统**: Windows 11, macOS 12+, Ubuntu 20.04+
- **Rust 版本**: 1.92.0+ (最新稳定版)
- **内存**: 8GB+ RAM
- **磁盘空间**: 5GB+ 可用空间
- **CPU**: 多核处理器（4核+）

### 支持的平台

| 平台 | 架构 | 支持状态 | 备注 |
|------|------|----------|------|
| Windows | x86_64 | ✅ 完全支持 | Windows 10+ |
| Windows | ARM64 | ✅ 支持 | Windows 11+ |
| macOS | x86_64 | ✅ 完全支持 | Intel Mac |
| macOS | ARM64 | ✅ 完全支持 | Apple Silicon |
| Linux | x86_64 | ✅ 完全支持 | Ubuntu, CentOS, Debian |
| Linux | ARM64 | ✅ 支持 | Raspberry Pi, ARM 服务器 |

---

## 🦀 Rust 环境安装

### 方法 1: 使用 rustup（推荐）

#### Windows

```powershell
# 下载并运行 rustup 安装程序
Invoke-WebRequest -Uri "https://win.rustup.rs" -OutFile "rustup-init.exe"
.\rustup-init.exe

# 或者使用 winget
winget install Rustlang.Rustup
```

#### macOS/Linux

```bash
# 下载并运行 rustup 安装脚本
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# 重新加载环境变量
source ~/.cargo/env
```

### 方法 2: 使用包管理器

#### Ubuntu/Debian

```bash
# 添加 Rust 官方源
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# 或者使用 snap
sudo snap install rustup --classic
```

#### macOS

```bash
# 使用 Homebrew
brew install rust

# 或者使用 MacPorts
sudo port install rust
```

#### Windows1

```powershell
# 使用 Chocolatey
choco install rust

# 或者使用 Scoop
scoop install rust
```

### 验证 Rust 安装

```bash
# 检查 Rust 版本
rustc --version

# 检查 Cargo 版本
cargo --version

# 检查工具链
rustup show
```

**预期输出**:

```text
rustc 1.90.0 (abc123def 2025-xx-xx)
cargo 1.90.0 (abc123def 2025-xx-xx)
```

---

## 📥 项目安装

### 方法 1: 从源码安装（推荐）

#### 1. 克隆仓库

```bash
# 克隆主仓库
git clone https://github.com/your-org/OTLP_rust.git
cd OTLP_rust

# 或者使用 SSH
git clone git@github.com:your-org/OTLP_rust.git
cd OTLP_rust
```

#### 2. 构建项目

```bash
# 构建所有 crates
cargo build

# 构建特定 crate
cargo build -p otlp
cargo build -p reliability

# 构建发布版本
cargo build --release
```

#### 3. 运行测试

```bash
# 运行所有测试
cargo test

# 运行特定 crate 的测试
cargo test -p otlp
cargo test -p reliability

# 运行基准测试
cargo bench
```

### 方法 2: 使用 Cargo 安装

```bash
# 从 Git 仓库安装
cargo install --git https://github.com/your-org/OTLP_rust.git

# 安装特定 crate
cargo install --git https://github.com/your-org/OTLP_rust.git --bin otlp-client
```

### 方法 3: 使用 crates.io（未来版本）

```bash
# 安装 OTLP crate
cargo install otlp

# 安装可靠性框架
cargo install reliability
```

---

## 📚 依赖管理

### 核心依赖

项目使用以下核心依赖：

```toml
[dependencies]
# 异步运行时
tokio = { version = "1.48", features = ["full"] }

# OpenTelemetry
opentelemetry = "0.31"
opentelemetry-semantic-conventions = "0.31"

# gRPC 支持
tonic = "0.12"
prost = "0.13"

# HTTP 支持
hyper = "1.0"
reqwest = "0.12"

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 错误处理
thiserror = "1.0"
anyhow = "1.0"

# 日志和追踪
tracing = "0.1"
tracing-subscriber = "0.3"

# 并发和同步
crossbeam = "0.8"
dashmap = "5.5"
```

### 可选依赖

```toml
[dependencies]
# 性能优化
rayon = { version = "1.8", optional = true }

# 压缩支持
flate2 = { version = "1.0", optional = true }
zstd = { version = "0.13", optional = true }

# 加密支持
ring = { version = "0.17", optional = true }

# 指标收集
prometheus = { version = "0.13", optional = true }
```

### 特性标志

```toml
[features]
default = ["std", "async"]
std = []
async = ["tokio"]
grpc = ["tonic", "prost"]
http = ["hyper", "reqwest"]
monitoring = ["prometheus"]
performance = ["rayon"]
compression = ["flate2", "zstd"]
security = ["ring"]
```

### 依赖更新

```bash
# 更新所有依赖
cargo update

# 更新特定依赖
cargo update -p tokio

# 检查过时的依赖
cargo outdated

# 审计依赖安全性
cargo audit
```

---

## ✅ 验证安装

### 1. 基础验证

```bash
# 检查项目结构
ls -la
# 应该看到: Cargo.toml, crates/, docs/, analysis/

# 检查 crates 目录
ls crates/
# 应该看到: otlp/, reliability/

# 验证构建
cargo check
# 应该显示: Finished dev [unoptimized + debuginfo] target(s)
```

### 2. 功能验证

#### 运行示例

```bash
# 运行 OTLP 示例
cargo run -p otlp --example quick_optimizations_demo

# 运行可靠性框架示例
cargo run -p reliability --example reliability_basic_usage
```

#### 运行测试

```bash
# 运行所有测试
cargo test --all

# 运行特定测试
cargo test -p otlp --lib
cargo test -p reliability --lib
```

#### 运行基准测试

```bash
# 运行所有基准测试
cargo bench

# 运行特定基准测试
cargo bench --bench otlp_performance
cargo bench --bench reliability_stress
```

### 3. 集成验证

#### 创建测试项目

```bash
# 创建新的测试项目
cargo new test_otlp_integration
cd test_otlp_integration

# 添加 OTLP 依赖
cargo add --path ../crates/otlp
cargo add tokio --features full
```

#### 测试代码

```rust
// src/main.rs
use otlp::core::EnhancedOtlpClient;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("测试 OTLP 客户端...");

    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("test-service")
        .build()
        .await?;

    println!("✅ OTLP 客户端创建成功！");
    Ok(())
}
```

#### 运行测试1

```bash
cargo run
# 预期输出: ✅ OTLP 客户端创建成功！
```

---

## ❓ 常见问题

### Q1: Rust 版本不兼容

**问题**: `error: failed to parse lock file at: Cargo.lock`

**解决方案**:

```bash
# 更新 Rust 工具链
rustup update

# 检查 Rust 版本
rustc --version

# 如果版本过低，重新安装
rustup install 1.90.0
rustup default 1.90.0
```

### Q2: 依赖下载失败

**问题**: `error: failed to download from https://crates.io/`

**解决方案**:

```bash
# 配置国内镜像源（中国用户）
# 创建或编辑 ~/.cargo/config.toml
[source.crates-io]
replace-with = 'ustc'

[source.ustc]
registry = "https://mirrors.ustc.edu.cn/crates.io-index"

# 或者使用其他镜像
[source.crates-io]
replace-with = 'tuna'

[source.tuna]
registry = "https://mirrors.tuna.tsinghua.edu.cn/git/crates.io-index.git"
```

### Q3: 编译错误

**问题**: `error: linking with`cc`failed`

**解决方案**:

#### Windows2

```powershell
# 安装 Visual Studio Build Tools
winget install Microsoft.VisualStudio.2022.BuildTools

# 或者安装 Visual Studio Community
winget install Microsoft.VisualStudio.2022.Community
```

#### macOS1

```bash
# 安装 Xcode Command Line Tools
xcode-select --install
```

#### Linux

```bash
# Ubuntu/Debian
sudo apt update
sudo apt install build-essential

# CentOS/RHEL
sudo yum groupinstall "Development Tools"
sudo yum install gcc gcc-c++
```

### Q4: 内存不足

**问题**: `error: process didn't exit successfully`

**解决方案**:

```bash
# 增加交换空间
sudo fallocate -l 2G /swapfile
sudo chmod 600 /swapfile
sudo mkswap /swapfile
sudo swapon /swapfile

# 或者减少并行编译
export CARGO_BUILD_JOBS=1
cargo build
```

### Q5: 网络代理问题

**问题**: `error: failed to fetch`

**解决方案**:

```bash
# 设置代理环境变量
export https_proxy=http://proxy.company.com:8080
export http_proxy=http://proxy.company.com:8080

# 或者配置 Cargo
# 编辑 ~/.cargo/config.toml
[http]
proxy = "http://proxy.company.com:8080"
```

### Q6: 权限问题

**问题**: `error: Permission denied`

**解决方案**:

```bash
# Linux/macOS: 修复权限
sudo chown -R $USER:$USER ~/.cargo
sudo chown -R $USER:$USER ~/.rustup

# Windows: 以管理员身份运行 PowerShell
```

### Q7: 磁盘空间不足

**问题**: `error: No space left on device`

**解决方案**:

```bash
# 清理 Cargo 缓存
cargo clean

# 清理全局缓存
cargo cache --autoclean

# 检查磁盘使用
du -sh ~/.cargo
du -sh target/
```

---

## 🗑️ 卸载

### 卸载项目

```bash
# 删除项目目录
rm -rf OTLP_rust

# 或者
rmdir /s OTLP_rust  # Windows
```

### 卸载 Rust（可选）

```bash
# 卸载 Rust 工具链
rustup self uninstall

# 删除 Cargo 目录
rm -rf ~/.cargo
rm -rf ~/.rustup
```

### 清理依赖

```bash
# 清理 Cargo 缓存
cargo clean

# 清理全局缓存
cargo cache --autoclean

# 删除 Cargo 注册表缓存
rm -rf ~/.cargo/registry
```

---

## 📞 获取帮助

### 官方资源

- **文档**: [项目文档](../README.md)
- **API 参考**: [OTLP API](../api/otlp.md) | [Reliability API](../api/reliability.md)
- **用户指南**: [OTLP 客户端使用](otlp-client.md) | [可靠性框架使用](reliability-framework.md)

### 社区支持

- **GitHub Issues**: [报告问题](https://github.com/your-org/OTLP_rust/issues)
- **讨论区**: [社区讨论](https://github.com/your-org/OTLP_rust/discussions)
- **邮件列表**: [订阅更新](mailto:otlp-rust-subscribe@example.com)

### 技术支持

- **Stack Overflow**: 使用标签 `otlp-rust`
- **Reddit**: r/rust 社区
- **Discord**: Rust 官方服务器

---

## 📝 更新日志

### v0.1.0 (2025-10-20)

- ✅ 初始安装指南发布
- ✅ 支持 Windows, macOS, Linux
- ✅ 完整的依赖管理说明
- ✅ 详细的故障排除指南

---

_最后更新: 2025年10月20日_
_文档版本: 1.0.0_
