# eBPF 模块文档

**最后更新**: 2025年1月
**Rust 版本**: 1.92+
**状态**: 🚀 开发中

---

## 📋 概述

eBPF 模块提供了基于内核的性能分析、网络追踪和系统调用追踪功能，无需修改应用代码即可收集详细的性能数据。

---

## 🏗️ 模块结构

```
ebpf/
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
└── tests.rs            # 单元测试
```

---

## 🚀 快速开始

### 基本使用

```rust
use otlp::ebpf::{EbpfConfig, EbpfCpuProfiler};

let config = EbpfConfig::default();
let mut profiler = EbpfCpuProfiler::new(config);
profiler.start()?;
// ... 执行代码 ...
let profile = profiler.stop()?;
```

---

## 📚 文档

- [完整使用指南](../../../docs/EBPF_USAGE_GUIDE_2025.md)
- [快速开始指南](../../../docs/QUICK_START_EBPF_2025.md)
- [集成指南](../../../docs/EBPF_INTEGRATION_GUIDE_2025.md)
- [最佳实践指南](../../../docs/EBPF_BEST_PRACTICES_2025.md)
- [故障排查指南](../../../docs/EBPF_TROUBLESHOOTING_2025.md)
- [性能优化指南](../../../docs/EBPF_PERFORMANCE_GUIDE_2025.md)
- [示例指南](../../../docs/EBPF_EXAMPLES_GUIDE_2025.md)
- [架构设计文档](../../../docs/EBPF_ARCHITECTURE_2025.md)
- [API 参考](../../../docs/EBPF_API_REFERENCE_2025.md)
- [更新日志](../../../docs/EBPF_CHANGELOG_2025.md)
- [部署指南](../../../docs/EBPF_DEPLOYMENT_GUIDE_2025.md)
- [安全指南](../../../docs/EBPF_SECURITY_GUIDE_2025.md)
- [迁移指南](../../../docs/EBPF_MIGRATION_GUIDE_2025.md)
- [实施计划](../../../EBPF_IMPLEMENTATION_PLAN_2025.md)

---

## 🔧 系统要求

- Linux 内核 >= 5.8 (推荐 5.15+)
- CAP_BPF 权限（或 root）
- BTF 支持

---

## 📝 示例

- `examples/ebpf_complete_example.rs` - 完整功能示例
- `examples/ebpf_profiling_example.rs` - CPU 性能分析示例
- `examples/ebpf_network_tracing_example.rs` - 网络追踪示例
- `examples/ebpf_syscall_tracing_example.rs` - 系统调用追踪示例

---

**状态**: 🚀 开发中
**进度**: Phase 1 完成，Phase 2 进行中
