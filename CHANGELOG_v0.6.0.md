# Changelog v0.6.0

## 概述

版本 v0.6.0 专注于技术栈升级和性能优化，为项目带来最新的 Rust 和 OpenTelemetry 生态支持。

## 主要变更

### 🔧 技术栈升级

#### Rust 1.94 支持

- **工具链升级**: 项目现在支持 Rust 1.94.0
- **新特性应用**: 开始应用 `array_windows` 优化（Rust 1.94 新特性）
- **TOML v1.1**: Cargo.toml 现在支持 TOML v1.1 格式特性

#### 依赖升级

| 依赖 | 旧版本 | 新版本 | 备注 |
|------|--------|--------|------|
| candle-core | 0.9.2 | 0.12.0 | ML 框架升级 |
| candle-nn | 0.9.2 | 0.12.0 | ML 框架升级 |
| candle-transformers | 0.9.2 | 0.12.0 | ML 框架升级 |
| aya | 0.13 | 0.13.1 | eBPF 框架升级 |

#### OpenTelemetry 生态

- **当前版本**: 保持 0.31.0（ crates.io 最新可用版本）
- **兼容性**: 已验证与 tracing-opentelemetry 0.32.1 兼容

### 🚀 性能优化

#### 代码优化

- **model/utils.rs**: 应用 `array_windows` 优化差分计算

  ```rust
  // 优化前
  data.windows(2).map(|w| w[1] - w[0]).collect()

  // 优化后（Rust 1.94）
  data.array_windows().map(|[a, b]| b - a).collect()
  ```

#### Clippy 修复

- 自动修复 114 个 Clippy 警告
- 剩余警告从 535 个减少到 402 个

### 📚 文档更新

- **README.md**: 更新 Rust 版本徽章和文档
- **rust-toolchain.toml**: 更新工具链配置

## 兼容性

### 支持的 Rust 版本

- **最低版本**: Rust 1.92.0
- **推荐版本**: Rust 1.94.0+

### 支持的 OpenTelemetry 版本

- **API 版本**: 0.31.0
- **SDK 版本**: 0.31.0
- **Protocol 版本**: 0.31.0

## 迁移指南

### 从 v0.5.0 迁移

1. **更新 Rust 工具链**

   ```bash
   rustup update stable
   ```

2. **更新依赖**

   ```bash
   cargo update
   ```

3. **重新构建项目**

   ```bash
   cargo build --release
   ```

### 破坏性变更

无破坏性变更。此版本保持与 v0.5.0 的 API 兼容性。

## 已知问题

1. **OpenTelemetry 0.32/0.33**: 等待上游 crates.io 发布
2. **Aya 0.14**: 等待上游 crates.io 发布

## 贡献者

感谢所有为本版本做出贡献的开发者！

## 相关链接

- [Rust 1.94 发布说明](https://blog.rust-lang.org/releases/)
- [OpenTelemetry Rust](https://github.com/open-telemetry/opentelemetry-rust)
- [Candle ML](https://github.com/huggingface/candle)

---

**发布日期**: 2026-03-14
**版本**: v0.6.0
**状态**: 稳定版
