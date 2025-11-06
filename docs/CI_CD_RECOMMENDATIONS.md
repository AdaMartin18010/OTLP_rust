# CI/CD配置建议 - 2025年技术趋势对齐

**最后更新**: 2025年10月29日

---

## 📋 概述

本文档提供CI/CD配置建议，确保2025年新增功能的持续集成和测试。

---

## 🔧 GitHub Actions配置

### 基础工作流

```yaml
name: 2025 Trend Alignment CI

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main, develop ]

jobs:
  test:
    name: 测试
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: 安装Rust
        uses: actions-rs/toolchain@v1
        with:
          toolchain: 1.91
          override: true

      - name: 运行测试
        run: |
          cargo test --workspace
          cargo test --test opamp_graduation_test
          cargo test --test integration_2025_trends

      - name: 运行性能测试
        run: |
          cargo bench --bench ottl_performance -- --test

  lint:
    name: 代码检查
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: 安装Rust
        uses: actions-rs/toolchain@v1
        with:
          toolchain: 1.91
          components: rustfmt, clippy

      - name: 格式化检查
        run: cargo fmt --all -- --check

      - name: Clippy检查
        run: cargo clippy --workspace --all-targets -- -D warnings

  linux-ebpf:
    name: Linux eBPF测试
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: 安装Rust
        uses: actions-rs/toolchain@v1
        with:
          toolchain: 1.91

      - name: 运行eBPF测试
        run: |
          cargo test --test integration_2025_trends --features ebpf
```

---

## 🚀 GitLab CI配置

### .gitlab-ci.yml

```yaml
stages:
  - test
  - lint
  - benchmark

variables:
  RUST_VERSION: "1.91"

test:
  stage: test
  image: rust:1.91
  script:
    - cargo test --workspace
    - cargo test --test opamp_graduation_test
    - cargo test --test integration_2025_trends

lint:
  stage: lint
  image: rust:1.91
  script:
    - rustup component add rustfmt clippy
    - cargo fmt --all -- --check
    - cargo clippy --workspace --all-targets -- -D warnings

benchmark:
  stage: benchmark
  image: rust:1.91
  script:
    - cargo bench --bench ottl_performance -- --test
  artifacts:
    paths:
      - target/criterion/
```

---

## 📊 性能监控

### 性能基准测试

```bash
# 运行性能基准测试
cargo bench --bench ottl_performance

# 生成性能报告
cargo bench --bench ottl_performance -- --output-format json > performance.json
```

### 性能阈值检查

```bash
# 检查OTTL性能 (目标: 300k span/s)
cargo bench --bench ottl_performance | grep "ottl_execute_bytecode"

# 检查eBPF开销 (目标: <1% CPU, <50MB内存)
cargo test --test integration_2025_trends -- --nocapture | grep "overhead"
```

---

## 🔍 代码质量检查

### Clippy配置

在 `Cargo.toml` 中添加:

```toml
[lints.clippy]
# 2025年技术趋势对齐相关检查
warn = ["clippy::all"]
deny = ["clippy::pedantic"]
```

### 格式化检查

```bash
# 检查格式
cargo fmt --all -- --check

# 自动格式化
cargo fmt --all
```

---

## 📈 持续监控

### 性能趋势跟踪

建议使用工具跟踪性能趋势:

1. **Criterion.rs**: 内置性能基准测试
2. **GitHub Actions Artifacts**: 保存性能报告
3. **自定义Dashboard**: 可视化性能趋势

### 测试覆盖率

```bash
# 安装cargo-tarpaulin
cargo install cargo-tarpaulin

# 生成覆盖率报告
cargo tarpaulin --workspace --out Html
```

---

## ✅ 检查清单

### 每次提交前

- [ ] 运行 `cargo test --workspace`
- [ ] 运行 `cargo fmt --all`
- [ ] 运行 `cargo clippy --workspace --all-targets`
- [ ] 运行集成测试

### 每次发布前

- [ ] 运行性能基准测试
- [ ] 验证性能目标 (OTTL: 300k span/s, eBPF: <1%开销)
- [ ] 更新文档
- [ ] 运行完整测试套件

---

## 🎯 最佳实践

1. **自动化测试**: 所有新功能都应包含测试
2. **性能监控**: 定期运行性能基准测试
3. **代码质量**: 使用Clippy和rustfmt保持代码质量
4. **文档更新**: 及时更新文档和示例

---

## 📚 更多资源

- [GitHub Actions文档](https://docs.github.com/en/actions)
- [GitLab CI文档](https://docs.gitlab.com/ee/ci/)
- [Criterion.rs文档](https://github.com/bheisler/criterion.rs)

---

**CI/CD支持**: 如有问题，请查看文档或提交Issue。
