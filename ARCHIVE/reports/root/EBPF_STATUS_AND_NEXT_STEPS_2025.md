# eBPF 功能状态与后续步骤

**创建日期**: 2025年1月
**状态**: 📊 分析完成，计划制定中

---

## 📋 当前状态

### ✅ 已有内容

1. **框架代码**
   - `crates/otlp/src/profiling/ebpf.rs` - 基础框架（占位实现）
   - `examples/ebpf_profiling_example.rs` - 示例代码框架

2. **文档**
   - `analysis/04_ebpf_profiling/` - 理论分析文档
   - `crates/otlp/semantics/EBPF_PRACTICE_GUIDE.md` - 实践指南

3. **模块声明**
   - `crates/otlp/src/lib.rs` 中已声明 eBPF 模块

### ❌ 缺失内容

1. **实际实现**
   - ❌ eBPF 程序加载和执行
   - ❌ 内核探针附加
   - ❌ 事件收集和处理
   - ❌ eBPF Maps 管理

2. **依赖库**
   - ❌ aya 或 libbpf-rs 依赖
   - ❌ eBPF 程序编译工具

3. **功能实现**
   - ❌ CPU 性能分析
   - ❌ 网络追踪
   - ❌ 系统调用追踪
   - ❌ 内存分配追踪

4. **集成**
   - ❌ OpenTelemetry 集成
   - ❌ OTLP 导出

---

## 🎯 实施建议

### 优先级排序

#### P0 - 立即实施（本周）
1. ✅ 添加 eBPF 库依赖（aya 或 libbpf-rs）
2. ✅ 创建完整的模块结构
3. ✅ 实现基础加载器

#### P1 - 短期实施（本月）
1. ✅ 实现 CPU 性能分析
2. ✅ 实现基础事件处理
3. ✅ 添加单元测试

#### P2 - 中期实施（下月）
1. ✅ 实现网络追踪
2. ✅ 实现系统调用追踪
3. ✅ OpenTelemetry 集成

#### P3 - 长期实施（季度）
1. ✅ 性能优化
2. ✅ 完整文档
3. ✅ 生产就绪

---

## 📦 技术选型

### 推荐方案

#### 方案 1: aya（推荐用于开发）
- **优势**: 纯 Rust，无需 C 依赖
- **劣势**: 生态系统较小
- **版本**: 0.13+
- **适用**: 快速开发，易于集成

#### 方案 2: libbpf-rs（推荐用于生产）
- **优势**: 成熟稳定，基于 libbpf
- **劣势**: 需要系统 libbpf 库
- **版本**: 0.23+
- **适用**: 生产环境，稳定性优先

#### 最终建议: 支持两种方案（可选特性）

```toml
[features]
ebpf-aya = ["dep:aya"]        # 使用 aya
ebpf-libbpf = ["dep:libbpf-rs"]  # 使用 libbpf-rs
```

---

## 🚀 实施步骤

### Step 1: 添加依赖（1天）

```toml
[dependencies]
aya = { version = "0.13", optional = true }
object = { version = "0.40", optional = true }
```

### Step 2: 创建模块结构（2天）

创建 `crates/otlp/src/ebpf/` 目录和基础模块。

### Step 3: 实现基础功能（1周）

实现加载器、探针管理、事件处理。

### Step 4: 实现核心功能（2-3周）

- CPU 性能分析
- 网络追踪
- 系统调用追踪

### Step 5: 集成和测试（1-2周）

- OpenTelemetry 集成
- 单元测试
- 集成测试
- 文档

---

## 📝 注意事项

### 系统要求
- Linux 内核 >= 5.8（推荐 5.15+）
- CAP_BPF 权限（或 root）
- BTF 支持

### 平台限制
- 仅在 Linux 平台支持
- 需要条件编译 `#[cfg(target_os = "linux")]`

### 安全性
- eBPF 程序需要验证器验证
- 使用可信的 eBPF 程序
- 遵循最小权限原则

---

## ✅ 成功标准

### 功能标准
- ✅ 能够加载和执行 eBPF 程序
- ✅ 能够附加到内核探针
- ✅ 能够收集和处理事件
- ✅ 性能开销 <1%

### 质量标准
- ✅ 测试覆盖率 >80%
- ✅ 文档完整
- ✅ 示例代码可用

---

**状态**: 📝 分析完成
**下一步**: 开始实施 Step 1
