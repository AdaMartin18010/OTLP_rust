# 2025年技术趋势对齐 - 迁移指南

**最后更新**: 2025年10月29日

---

## 📋 概述

本指南帮助您将现有代码迁移到使用2025年新增的技术趋势对齐功能。

---

## 🚀 迁移步骤

### 1. OTTL性能优化迁移

#### 之前 (标量解析)

```rust
use otlp::ottl::{OtlpTransform, TransformConfig, Statement};

let mut config = TransformConfig::new();
config = config.add_statement(statement);

let transform = OtlpTransform::new(config)?;
```

#### 之后 (字节码优化，默认启用)

```rust
use otlp::ottl::{OtlpTransform, TransformConfig};

let mut config = TransformConfig::new()
    .with_bytecode(true); // 默认启用，可显式指定

// 编译字节码以获得10×性能提升
config.compile_bytecode()?;

let transform = OtlpTransform::new(config)?;
```

**优势**:

- ✅ 10×性能提升 (30k → 300k span/s)
- ✅ 自动字符串去重
- ✅ 常量池优化

---

### 2. OPAMP灰度策略迁移

#### 之前 (无灰度策略)

```rust
use otlp::opamp::messages::ServerToAgent;

let message = ServerToAgent {
    remote_config: Some(config),
    // ... 其他字段
    graduation_strategy: None,
    rollback_window: None,
};
```

#### 之后 (启用灰度策略)

```rust
use otlp::opamp::messages::ServerToAgent;
use otlp::{GraduationStrategy, LabelSelector};
use std::time::Duration;

// 创建灰度策略
let selector = LabelSelector::new()
    .with_label("env".to_string(), "prod".to_string());

let strategy = GraduationStrategy::new(selector)
    .with_weight(0.1) // 10%灰度
    .with_rollback_window(Duration::from_secs(300));

let message = ServerToAgent {
    remote_config: Some(config),
    // ... 其他字段
    graduation_strategy: Some(strategy),
    rollback_window: Some(Duration::from_secs(300)),
};
```

**优势**:

- ✅ 企业级灰度发布
- ✅ 自动回滚机制
- ✅ 健康状态监控

---

### 3. Const API迁移

#### 之前 (硬编码值)

```rust
const BATCH_SIZE: usize = 1000;
const TIMEOUT_SECS: u64 = 5;

let config = Config {
    batch_size: BATCH_SIZE,
    timeout: Duration::from_secs(TIMEOUT_SECS),
};
```

#### 之后 (使用const API)

```rust
use otlp::config::{
    DEFAULT_BATCH_SIZE, DEFAULT_TIMEOUT, validate_batch_size
};

// 使用const常量
let config = Config {
    batch_size: DEFAULT_BATCH_SIZE,
    timeout: DEFAULT_TIMEOUT,
};

// 使用const函数验证
if !validate_batch_size(config.batch_size) {
    return Err("无效的批处理大小");
}
```

**优势**:

- ✅ 编译时优化
- ✅ 类型安全
- ✅ 统一配置管理

---

### 4. eBPF Profiling迁移

#### 之前 (无eBPF支持)

```rust
use otlp::profiling::CpuProfiler;

let profiler = CpuProfiler::new(config);
profiler.start().await?;
```

#### 之后 (启用eBPF，仅Linux)

```rust
#[cfg(target_os = "linux")]
use otlp::{EbpfProfiler, EbpfProfilerConfig};

#[cfg(target_os = "linux")]
{
    let config = EbpfProfilerConfig::new()
        .with_sample_rate(99); // 99Hz，符合2025年标准

    let mut profiler = EbpfProfiler::new(config)?;
    profiler.start()?;

    // ... 工作负载 ...

    let profile = profiler.stop()?;
    let overhead = profiler.get_overhead();

    // 验证性能开销
    assert!(overhead.cpu_percent < 1.0);
    assert!(overhead.memory_bytes < 50 * 1024 * 1024);
}
```

**优势**:

- ✅ <1% CPU开销
- ✅ <50MB内存开销
- ✅ 符合2025年标准

---

## 🔧 配置更新

### Cargo.toml

确保使用Rust 1.90+:

```toml
[package]
rust-version = "1.91"
```

### .cargo/config.toml

LLD链接器配置已自动添加，无需手动配置。

---

## ✅ 迁移检查清单

- [ ] 更新OTTL Transform配置，启用字节码优化
- [ ] 更新OPAMP消息，添加灰度策略字段
- [ ] 替换硬编码配置值为const常量
- [ ] (可选) 在Linux平台启用eBPF Profiling
- [ ] 运行性能测试验证效果
- [ ] 更新文档和注释

---

## 📊 性能验证

迁移后，运行性能测试验证效果:

```bash
# 运行所有性能测试
./scripts/run_performance_tests.sh

# 或单独运行
cargo bench --bench ottl_performance
cargo test --test opamp_graduation_test
cargo test --test integration_2025_trends
```

---

## 🐛 常见问题

### Q: 字节码优化是否向后兼容？

A: 是的，字节码优化默认启用，但可以禁用:

```rust
let config = TransformConfig::new()
    .with_bytecode(false); // 禁用字节码，使用标量解析
```

### Q: 灰度策略是否必需？

A: 不是，灰度策略是可选的。如果不提供，OPAMP消息将正常工作。

### Q: eBPF Profiling是否支持Windows/macOS？

A: 不支持，eBPF仅在Linux平台支持。非Linux平台会自动使用fallback实现。

---

## 📚 更多资源

- [快速开始指南](../QUICK_START_TREND_2025.md)
- [使用示例](../examples/README_TREND_2025.md)
- [技术总结](../analysis/2025_TREND_ALIGNMENT_SUMMARY.md)

---

**迁移支持**: 如有问题，请查看文档或提交Issue。
