# OTLP Rust 快速入门指南

**版本**: v0.5.0-rc1
**最后更新**: 2025年1月13日

---

## 🚀 5分钟快速开始

### 1. 安装依赖

```bash
# 确保使用 Rust 1.92+
rustup update stable
rustc --version  # 应显示 1.92.0 或更高版本
```

### 2. 添加依赖

在 `Cargo.toml` 中添加：

```toml
[dependencies]
otlp = { path = "../crates/otlp", features = ["full"] }
tokio = { version = "1.49", features = ["full"] }
tracing-subscriber = "0.3"
```

### 3. 基础使用

#### 3.1 CPU 性能分析

```rust
use otlp::profiling::{CpuProfiler, ProfilerConfig};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    // 创建配置
    let config = ProfilerConfig::default();

    // 创建 Profiler
    let mut profiler = CpuProfiler::new(config);

    // 启动性能分析
    profiler.start().await?;

    // 执行你的代码
    // ... your code ...

    // 停止并获取 Profile
    let profile = profiler.stop().await?;

    // 导出为 JSON
    let json = profile.encode_json()?;
    println!("Profile: {}", json);

    Ok(())
}
```

#### 3.2 eBPF 使用（Linux）

```rust
use otlp::ebpf::{EbpfConfig, EbpfLoader, EbpfCpuProfiler};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 检查系统支持
    EbpfLoader::check_system_support()?;

    // 创建配置
    let config = EbpfConfig::default()
        .with_sample_rate(99)
        .with_cpu_profiling(true);

    // 创建 CPU Profiler
    let mut profiler = EbpfCpuProfiler::new(config);

    // 启动
    profiler.start()?;

    // ... your code ...

    // 停止
    let profile = profiler.stop()?;

    Ok(())
}
```

#### 3.3 性能优化

```rust
use otlp::performance::{QuickOptimizationsManager, CompressionAlgorithm};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let manager = QuickOptimizationsManager::default();

    let data = b"your data here";

    // 压缩
    let compressed = manager.compress(data, CompressionAlgorithm::Gzip)?;

    // 解压
    let decompressed = manager.decompress(&compressed, CompressionAlgorithm::Gzip)?;

    assert_eq!(data, decompressed.as_slice());

    Ok(())
}
```

---

## 📚 更多示例

- [eBPF 基础示例](../examples/ebpf_basic_example.rs)
- [OTLP Profiling 示例](../examples/otlp_profiling_example.rs)
- [性能优化示例](../examples/performance_optimization_example.rs)

---

## 🔗 相关文档

- [完整API文档](../crates/otlp/docs/)
- [架构设计](../docs/04_ARCHITECTURE/)
- [最佳实践](../docs/12_GUIDES/)

---

**需要帮助？** 查看 [完整文档](../README.md) 或 [提交Issue](https://github.com/your-org/OTLP_rust/issues)
