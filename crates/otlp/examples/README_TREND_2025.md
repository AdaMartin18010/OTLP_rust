# 2025年技术趋势对齐 - 使用示例

**最后更新**: 2025年10月29日

---

## 📚 示例列表

### 1. OTTL字节码解析器

**文件**: `examples/ottl_bytecode_example.rs`

**功能**: 演示如何使用字节码解析器实现10×性能提升

**运行**:

```bash
cargo run --example ottl_bytecode_example
```

**关键代码**:

```rust
use otlp::ottl::{BytecodeCompiler, OttlParser};

let mut parser = OttlParser::new(ottl_statement.to_string());
let statements = parser.parse()?;

let mut compiler = BytecodeCompiler::new();
let program = compiler.compile(&statement)?;
```

---

### 2. OPAMP灰度策略

**文件**: `examples/opamp_graduation_example.rs`

**功能**: 演示如何使用OPAMP灰度策略实现企业级灰度发布

**运行**:

```bash
cargo run --example opamp_graduation_example
```

**关键代码**:

```rust
use otlp::opamp::graduation::{GraduationStrategy, LabelSelector};

let selector = LabelSelector::new()
    .with_label("env".to_string(), "prod".to_string());

let strategy = GraduationStrategy::new(selector)
    .with_weight(0.1) // 10%灰度
    .with_rollback_window(Duration::from_secs(300));
```

---

### 3. eBPF Profiling

**文件**: `examples/ebpf_profiling_example.rs`

**功能**: 演示如何使用eBPF性能分析器进行持续性能分析

**运行** (仅Linux):

```bash
cargo run --example ebpf_profiling_example
```

**关键代码**:

```rust
use otlp::profiling::ebpf::{EbpfProfiler, EbpfProfilerConfig};

let config = EbpfProfilerConfig::new()
    .with_sample_rate(99); // 99Hz

let mut profiler = EbpfProfiler::new(config)?;
profiler.start()?;
let profile = profiler.stop()?;
```

---

### 4. Const API使用

**文件**: `examples/const_api_example.rs`

**功能**: 演示如何使用const API实现编译时优化

**运行**:

```bash
cargo run --example const_api_example
```

**关键代码**:

```rust
use otlp::config::{
    DEFAULT_BATCH_SIZE, DEFAULT_TIMEOUT, validate_batch_size, validate_timeout
};

// 使用const常量
let batch_size = DEFAULT_BATCH_SIZE;

// 使用const函数验证
if validate_batch_size(batch_size) {
    // ...
}
```

---

## 🚀 快速开始

### 运行所有示例

```bash
# OTTL字节码示例
cargo run --example ottl_bytecode_example

# OPAMP灰度策略示例
cargo run --example opamp_graduation_example

# eBPF Profiling示例 (仅Linux)
#[cfg(target_os = "linux")]
cargo run --example ebpf_profiling_example

# Const API示例
cargo run --example const_api_example
```

---

## 📖 更多信息

- [实施计划](../analysis/2025_TREND_ALIGNMENT_PLAN.md)
- [进度报告](../analysis/2025_TREND_ALIGNMENT_PROGRESS.md)
- [技术总结](../analysis/2025_TREND_ALIGNMENT_SUMMARY.md)
