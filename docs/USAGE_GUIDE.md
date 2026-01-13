# OTLP Rust 使用指南

**版本**: v0.5.0-rc1
**最后更新**: 2025年1月13日

---

## 📖 目录

1. [快速开始](#快速开始)
2. [核心功能](#核心功能)
3. [高级特性](#高级特性)
4. [最佳实践](#最佳实践)
5. [故障排查](#故障排查)

---

## 🚀 快速开始

### 安装

```bash
# 在 Cargo.toml 中添加
[dependencies]
otlp = { path = "../crates/otlp", features = ["full"] }
tokio = { version = "1.49", features = ["full"] }
```

### 第一个示例

```rust
use otlp::profiling::{CpuProfiler, ProfilerConfig};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut profiler = CpuProfiler::new(ProfilerConfig::default());
    profiler.start().await?;

    // 你的代码

    let profile = profiler.stop().await?;
    let json = profile.encode_json()?;
    println!("{}", json);

    Ok(())
}
```

---

## 🎯 核心功能

### CPU 性能分析

```rust
use otlp::profiling::{CpuProfiler, ProfilerConfig};

let mut profiler = CpuProfiler::new(ProfilerConfig::default());
profiler.start().await?;

// 执行代码

let profile = profiler.stop().await?;
```

### eBPF 追踪（Linux）

```rust
use otlp::ebpf::{EbpfConfig, EbpfCpuProfiler};

// 检查系统支持
EbpfLoader::check_system_support()?;

let config = EbpfConfig::default()
    .with_cpu_profiling(true);

let mut profiler = EbpfCpuProfiler::new(config);
profiler.start()?;

// 执行代码

let profile = profiler.stop()?;
```

### 性能优化

```rust
use otlp::performance::{QuickOptimizationsManager, CompressionAlgorithm};

let manager = QuickOptimizationsManager::default();
let compressed = manager.compress(&data, CompressionAlgorithm::Gzip)?;
```

---

## 🔥 高级特性

### 批量处理

```rust
use otlp::profiling::{CpuProfiler, ProfilerConfig};

let mut profiles = Vec::new();

for _ in 0..10 {
    let mut profiler = CpuProfiler::new(ProfilerConfig::default());
    profiler.start().await?;
    // ...
    let profile = profiler.stop().await?;
    profiles.push(profile);
}

// 批量导出
// exporter.export_batch(&profiles).await?;
```

### 自定义配置

```rust
use otlp::profiling::ProfilerConfig;
use std::time::Duration;

let config = ProfilerConfig {
    sample_rate: 100,  // 100Hz
    duration: Duration::from_secs(30),
    // ...
};
```

---

## 💡 最佳实践

### 1. 性能分析

- ✅ 在生产环境使用较低的采样频率（10-50Hz）
- ✅ 定期收集 Profile，避免持续运行
- ✅ 监控性能分析开销

### 2. eBPF 使用

- ✅ 确保系统支持（Linux 5.8+）
- ✅ 检查 CAP_BPF 权限
- ✅ 使用 BTF 支持的内核

### 3. 错误处理

```rust
use otlp::error::OtlpError;

match result {
    Ok(value) => { /* 处理成功 */ }
    Err(OtlpError::Processing(e)) => { /* 处理错误 */ }
    Err(e) => { /* 其他错误 */ }
}
```

---

## 🔧 故障排查

### 常见问题

#### 1. eBPF 不支持

**问题**: `UnsupportedPlatform` 错误

**解决**:

- 确保在 Linux 系统运行
- 检查内核版本 >= 5.8
- 验证 CAP_BPF 权限

#### 2. 性能分析启动失败

**问题**: Profiler 启动失败

**解决**:

- 检查系统资源
- 降低采样频率
- 查看日志输出

#### 3. 内存不足

**问题**: 内存分配失败

**解决**:

- 使用内存池
- 减少缓冲区大小
- 增加系统内存

---

## 📚 更多资源

- [API 参考](../docs/API_QUICK_REFERENCE.md)
- [示例代码](../examples/)
- [架构文档](../docs/04_ARCHITECTURE/)

---

**需要帮助？** 查看 [完整文档](../README.md)
