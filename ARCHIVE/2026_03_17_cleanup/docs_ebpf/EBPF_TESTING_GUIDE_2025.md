# eBPF 测试指南 2025

**创建日期**: 2025年1月
**状态**: 📚 测试指南
**Rust 版本**: 1.92+

---

## 📋 目录

- [eBPF 测试指南 2025](#ebpf-测试指南-2025)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [测试类型](#测试类型)
    - [1. 单元测试](#1-单元测试)
    - [2. 集成测试](#2-集成测试)
    - [3. 模拟测试](#3-模拟测试)
    - [4. 基准测试](#4-基准测试)
  - [单元测试](#单元测试)
    - [运行单元测试](#运行单元测试)
    - [测试覆盖范围](#测试覆盖范围)
  - [集成测试](#集成测试)
    - [运行集成测试](#运行集成测试)
    - [系统要求](#系统要求)
  - [模拟测试](#模拟测试)
    - [运行模拟测试](#运行模拟测试)
    - [适用场景](#适用场景)
  - [基准测试](#基准测试)
    - [运行基准测试](#运行基准测试)
    - [性能目标](#性能目标)
  - [测试工具](#测试工具)
    - [测试工具库](#测试工具库)
  - [最佳实践](#最佳实践)
    - [1. 测试隔离](#1-测试隔离)
    - [2. 错误测试](#2-错误测试)
    - [3. 边界测试](#3-边界测试)
    - [4. 异步测试](#4-异步测试)
    - [5. Mock 使用](#5-mock-使用)
  - [测试覆盖率](#测试覆盖率)
    - [目标覆盖率](#目标覆盖率)
    - [生成覆盖率报告](#生成覆盖率报告)
  - [CI/CD 集成](#cicd-集成)
    - [GitHub Actions](#github-actions)
  - [参考资源](#参考资源)

---

## 概述

本文档提供 eBPF 模块的完整测试指南，包括单元测试、集成测试、模拟测试和基准测试。

---

## 测试类型

### 1. 单元测试

测试单个模块的功能，不依赖外部环境。

**位置**: `crates/otlp/src/ebpf/tests.rs`

**示例**:

```rust
#[test]
fn test_ebpf_config_default() {
    let config = EbpfConfig::default();
    assert_eq!(config.sample_rate, 99);
    assert!(config.enable_cpu_profiling);
}
```

### 2. 集成测试

测试多个模块的协作，可能需要特定环境。

**位置**: `tests/ebpf_integration_test.rs`

**示例**:

```rust
#[tokio::test]
async fn test_ebpf_cpu_profiler_lifecycle() {
    let config = create_test_ebpf_config();
    let mut profiler = EbpfCpuProfiler::new(config).unwrap();
    assert!(profiler.start().is_ok());
    let profile = profiler.stop().unwrap();
    assert!(!profile.data.is_empty());
}
```

### 3. 模拟测试

在非 Linux 环境或无权限环境下测试。

**位置**: `tests/ebpf_mock.rs`

**示例**:

```rust
#[tokio::test]
async fn test_mock_cpu_profiler() {
    let config = EbpfConfig::default();
    let mut profiler = MockEbpfCpuProfiler::new(config).unwrap();
    assert!(profiler.start().is_ok());
    let profile = profiler.stop().unwrap();
    assert!(!profile.data.is_empty());
}
```

### 4. 基准测试

测试性能，确保开销在可接受范围内。

**位置**: `benches/ebpf_performance.rs`

**示例**:

```rust
fn ebpf_config_benchmarks(c: &mut Criterion) {
    c.bench_function("create_recommended_config_dev", |b| {
        b.iter(|| create_recommended_config("development"))
    });
}
```

---

## 单元测试

### 运行单元测试

```bash
# 运行所有单元测试
cargo test --package otlp --lib ebpf

# 运行特定测试
cargo test test_ebpf_config_default

# 显示输出
cargo test --package otlp --lib ebpf -- --nocapture
```

### 测试覆盖范围

- ✅ 配置验证
- ✅ 类型定义
- ✅ 错误处理
- ✅ 工具函数

---

## 集成测试

### 运行集成测试

```bash
# 运行所有集成测试
cargo test --test ebpf_integration --features ebpf

# 运行特定测试
cargo test --test ebpf_integration test_ebpf_cpu_profiler_lifecycle
```

### 系统要求

- Linux 内核 >= 5.8
- CAP_BPF 权限或 root
- BTF 支持

---

## 模拟测试

### 运行模拟测试

```bash
# 运行模拟测试（无需 root 权限）
cargo test --test ebpf_mock
```

### 适用场景

- 非 Linux 环境
- 无 root 权限
- CI/CD 环境
- 快速验证逻辑

---

## 基准测试

### 运行基准测试

```bash
# 运行所有基准测试
cargo bench --bench ebpf_performance --features ebpf

# 运行特定基准测试
cargo bench --bench ebpf_performance ebpf_config_benchmarks
```

### 性能目标

- 配置创建: < 100ns
- 配置验证: < 1μs
- 事件转换: < 10μs/event

---

## 测试工具

### 测试工具库

**位置**: `crates/otlp/tests/ebpf_test_utils.rs`

**功能**:

- 创建测试配置
- 创建测试事件
- 验证配置
- 辅助函数

**使用示例**:

```rust
use crate::otlp::tests::ebpf_test_utils::*;

#[test]
fn test_with_test_config() {
    let config = create_test_ebpf_config();
    assert_valid_config(&config);
}
```

---

## 最佳实践

### 1. 测试隔离

每个测试应该独立运行，不依赖其他测试的状态。

```rust
#[test]
fn test_isolated() {
    let config = EbpfConfig::default(); // 每次创建新配置
    // 测试逻辑
}
```

### 2. 错误测试

测试错误情况，确保错误处理正确。

```rust
#[test]
fn test_invalid_config() {
    let config = EbpfConfig::default().with_sample_rate(0);
    assert!(validate_config(&config).is_err());
}
```

### 3. 边界测试

测试边界情况，确保稳定性。

```rust
#[test]
fn test_edge_cases() {
    // 测试最大值
    let config = EbpfConfig::default().with_max_samples(usize::MAX);
    // 测试最小值
    let config = EbpfConfig::default().with_max_samples(1);
}
```

### 4. 异步测试

对于异步代码，使用 `#[tokio::test]`。

```rust
#[tokio::test]
async fn test_async_operation() {
    let processor = EventProcessor::new(100);
    let event = create_test_ebpf_event(EbpfEventType::CpuSample);
    assert!(processor.send_mock_event(event).await.is_ok());
}
```

### 5. Mock 使用

在无法使用真实环境时，使用 Mock。

```rust
#[test]
fn test_with_mock() {
    let mut profiler = MockEbpfCpuProfiler::new(config).unwrap();
    // 测试逻辑
}
```

---

## 测试覆盖率

### 目标覆盖率

- 单元测试: 80%+
- 集成测试: 60%+
- 总体: 75%+

### 生成覆盖率报告

```bash
# 使用 cargo-llvm-cov
cargo llvm-cov --workspace --all-features --lcov --output-path lcov.info

# 使用 cargo-tarpaulin
cargo tarpaulin --workspace --all-features --out Html --output-dir coverage
```

---

## CI/CD 集成

### GitHub Actions

eBPF 测试已集成到 CI/CD 流程：

- `.github/workflows/ebpf-tests.yml` - eBPF 专用测试工作流

**功能**:

- 运行单元测试
- 运行集成测试
- 代码格式检查
- Clippy 检查
- 文档生成

---

## 参考资源

- [使用指南](./EBPF_USAGE_GUIDE_2025.md)
- [最佳实践](./EBPF_BEST_PRACTICES_2025.md)
- [故障排查](./EBPF_TROUBLESHOOTING_2025.md)

---

**状态**: 📚 测试指南
**最后更新**: 2025年1月
