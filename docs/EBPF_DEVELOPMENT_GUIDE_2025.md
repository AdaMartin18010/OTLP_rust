# eBPF 开发指南 2025

**创建日期**: 2025年1月
**状态**: 📚 开发指南
**Rust 版本**: 1.92+

---

## 📋 目录

- [概述](#概述)
- [开发环境设置](#开发环境设置)
- [项目结构](#项目结构)
- [代码规范](#代码规范)
- [开发流程](#开发流程)
- [调试技巧](#调试技巧)
- [贡献指南](#贡献指南)

---

## 概述

本文档提供 eBPF 模块的开发指南，帮助开发者快速上手和贡献代码。

---

## 开发环境设置

### 1. 系统要求

- **操作系统**: Linux (内核 >= 5.8)
- **Rust**: 1.92+
- **工具**:
  - `clang` (eBPF 程序编译)
  - `llvm` (eBPF 程序验证)
  - `bpftool` (可选，用于调试)

### 2. 安装依赖

```bash
# 安装 Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# 安装构建工具
sudo apt-get update
sudo apt-get install -y build-essential clang llvm libclang-dev

# 安装 bpftool (可选)
sudo apt-get install -y bpftool
```

### 3. 克隆项目

```bash
git clone <repository-url>
cd OTLP_rust
```

### 4. 编译项目

```bash
# 编译（启用 eBPF feature）
cargo build --features ebpf

# 运行测试
cargo test --features ebpf
```

---

## 项目结构

### eBPF 模块结构

```
crates/otlp/src/ebpf/
├── mod.rs              # 模块入口
├── types.rs            # 数据类型定义
├── error.rs            # 错误类型定义
├── loader.rs           # eBPF程序加载器
├── probes.rs           # 探针管理
├── events.rs           # 事件处理
├── maps.rs             # eBPF Maps管理
├── profiling.rs        # CPU性能分析
├── networking.rs       # 网络追踪
├── syscalls.rs         # 系统调用追踪
├── memory.rs           # 内存追踪
├── integration.rs      # OpenTelemetry集成
├── utils.rs            # 工具函数
└── tests.rs            # 单元测试
```

### 测试文件

```
tests/
├── ebpf_integration_test.rs  # 集成测试
├── ebpf_mock.rs              # Mock测试
└── common/
    └── mod.rs                # 测试公共模块

crates/otlp/tests/
└── ebpf_test_utils.rs        # eBPF测试工具库
```

### 示例文件

```
examples/
├── ebpf_complete_example.rs          # 完整功能示例
├── ebpf_profiling_example.rs         # CPU性能分析示例
├── ebpf_network_tracing_example.rs   # 网络追踪示例
└── ebpf_syscall_tracing_example.rs   # 系统调用追踪示例
```

### 基准测试

```
benches/
└── ebpf_performance.rs  # 性能基准测试
```

---

## 代码规范

### 1. 命名规范

- **结构体**: PascalCase (如 `EbpfConfig`)
- **函数**: snake_case (如 `create_recommended_config`)
- **常量**: UPPER_SNAKE_CASE (如 `DEFAULT_SAMPLE_RATE`)

### 2. 文档注释

```rust
/// 创建推荐的 eBPF 配置
///
/// # 参数
/// * `env` - 环境名称 ("production", "development", "debug")
///
/// # 返回值
/// 配置好的 `EbpfConfig` 实例
///
/// # 示例
/// ```
/// let config = create_recommended_config("production");
/// ```
pub fn create_recommended_config(env: &str) -> EbpfConfig {
    // ...
}
```

### 3. 错误处理

```rust
use crate::ebpf::error::EbpfError;

// 使用 Result 返回错误
pub fn load(&mut self, program_bytes: &[u8]) -> Result<()> {
    if program_bytes.is_empty() {
        return Err(EbpfError::LoadFailed("程序字节码为空".to_string()).into());
    }
    Ok(())
}
```

### 4. 条件编译

```rust
#[cfg(all(feature = "ebpf", target_os = "linux"))]
pub fn linux_specific_function() {
    // Linux 特定实现
}

#[cfg(not(all(feature = "ebpf", target_os = "linux")))]
pub fn linux_specific_function() {
    // 非 Linux 平台返回错误
    Err(EbpfError::UnsupportedPlatform.into())
}
```

---

## 开发流程

### 1. 创建功能分支

```bash
git checkout -b feature/ebpf-new-feature
```

### 2. 编写代码

- 遵循代码规范
- 添加文档注释
- 编写单元测试

### 3. 运行测试

```bash
# 运行所有测试
cargo test --features ebpf

# 运行特定测试
cargo test test_name

# 运行 Clippy
cargo clippy --features ebpf -- -D warnings
```

### 4. 格式化代码

```bash
cargo fmt --all
```

### 5. 提交代码

```bash
git add .
git commit -m "feat(ebpf): add new feature"
git push origin feature/ebpf-new-feature
```

### 6. 创建 Pull Request

- 填写 PR 描述
- 关联相关 Issue
- 等待代码审查

---

## 调试技巧

### 1. 使用 tracing

```rust
use tracing::{info, debug, error};

fn my_function() {
    debug!("进入函数");
    info!("处理数据: {:?}", data);
    if let Err(e) = result {
        error!("处理失败: {}", e);
    }
}
```

### 2. 使用 gdb

```bash
# 编译调试版本
cargo build --features ebpf

# 使用 gdb 调试
gdb target/debug/your_binary
```

### 3. 使用 bpftool

```bash
# 查看加载的 eBPF 程序
sudo bpftool prog list

# 查看 eBPF Maps
sudo bpftool map list

# 查看特定程序详情
sudo bpftool prog show id <prog_id>
```

---

## 贡献指南

### 1. 报告问题

- 使用 GitHub Issues
- 提供详细的错误信息
- 附上复现步骤

### 2. 提交代码

- 遵循代码规范
- 添加测试
- 更新文档

### 3. 代码审查

- 审查代码质量
- 检查测试覆盖
- 验证文档更新

---

## 参考资源

- [架构设计文档](./EBPF_ARCHITECTURE_2025.md)
- [API 参考](./EBPF_API_REFERENCE_2025.md)
- [测试指南](./EBPF_TESTING_GUIDE_2025.md)
- [最佳实践](./EBPF_BEST_PRACTICES_2025.md)

---

**状态**: 📚 开发指南
**最后更新**: 2025年1月
