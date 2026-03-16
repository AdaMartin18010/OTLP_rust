# 归档目录说明

**创建日期**: 2025-01-13  
**最后更新**: 2026-03-17  
**目的**: 归档非核心主题和过时内容，保持项目结构清晰

---

## 📂 归档结构

```
ARCHIVE/
├── 2026_03_17_cleanup/   # 2026-03-17 清理归档
│   ├── completion_reports/  # 过时的完成报告
│   ├── progress_reports/    # 过时的进度报告
│   ├── analysis_reports/    # 过时的分析报告
│   ├── clippy_outputs/      # 临时构建输出
│   ├── guides/              # 过时的指南
│   ├── docs_ebpf/           # 误导性的eBPF文档
│   └── ARCHIVE_SUMMARY.md   # 本次归档摘要
├── modules/              # 归档的代码模块
│   └── otlp/            # OTLP crate 中的非核心模块
│       ├── blockchain/  # 区块链模块（已归档）
│       ├── edge_computing/  # 边缘计算模块（已归档）
│       └── ai_ml/       # AI/ML 模块（已归档）
├── docs/                # 归档的文档
│   ├── blockchain/      # 区块链相关文档
│   ├── edge_computing/ # 边缘计算相关文档
│   └── ai_ml/          # AI/ML 相关文档
└── reports/             # 归档的报告和计划文档
    ├── root/           # 根目录下的报告
    └── docs/           # docs 目录下的报告
```

---

## 🎯 核心主题

本项目实际只包含 **2个核心 crate**：

1. **`crates/otlp`** - OpenTelemetry Protocol 实现
2. **`crates/reliability`** - 统一可靠性框架

注意：`model` 和 `libraries` 两个主题**不存在实际代码**，仅为文档中的概念。

---

## 📋 归档内容

### 2026-03-17 清理归档

详见 [`2026_03_17_cleanup/ARCHIVE_SUMMARY.md`](2026_03_17_cleanup/ARCHIVE_SUMMARY.md)

#### 归档原因

根据 [`PROJECT_STATUS.md`](../PROJECT_STATUS.md) 的真实状态评估，归档以下内容：

1. **重复的"100%完成"报告** - 内容夸大，与实际情况不符
2. **误导性eBPF文档** - eBPF功能为模拟实现，文档会误导用户
3. **过时的分析报告** - 2025年的趋势分析报告已过时
4. **临时构建输出** - Clippy输出文件不应提交到版本控制

#### 真实项目状态

- ✅ **可用**: OTLP导出、批量处理、重试/断路器/超时、语义约定、OTTL基础、Tracezip
- 🚧 **模拟/不可用**: eBPF、性能分析、高级加密、AI采样、SIMD优化（未实现指令优化）

### 历史归档 (2025-01-13)

#### 1. Blockchain (区块链)

- **位置**: `ARCHIVE/modules/otlp/blockchain/`
- **原因**: 不属于 OTLP 核心功能
- **状态**: 已从 `crates/otlp/src/lib.rs` 中移除

#### 2. Edge Computing (边缘计算)

- **位置**: `ARCHIVE/modules/otlp/edge_computing/`
- **原因**: 不属于 OTLP 核心功能
- **状态**: 已从 `crates/otlp/src/lib.rs` 中移除

#### 3. AI/ML (人工智能/机器学习)

- **位置**: `ARCHIVE/modules/otlp/ai_ml/`
- **原因**: 不属于 OTLP 核心功能
- **状态**: 已从 `crates/otlp/src/lib.rs` 中移除

### 已归档的文档

- `BLOCKCHAIN_GUIDE_2025.md` → `ARCHIVE/docs/blockchain/`
- `EDGE_COMPUTING_GUIDE_2025.md` → `ARCHIVE/docs/edge_computing/`
- `AI_ML_GUIDE_2025.md` → `ARCHIVE/docs/ai_ml/`

### 已归档的报告

根目录和 `docs/` 目录下的各种完成报告、进度报告、计划文档等已归档到 `ARCHIVE/reports/`。

---

## 🔍 如何查找归档内容

### 查找最新归档

```bash
# 查看2026-03-17归档摘要
cat ARCHIVE/2026_03_17_cleanup/ARCHIVE_SUMMARY.md

# 查看该次归档的所有内容
ls ARCHIVE/2026_03_17_cleanup/
```

### 查找历史归档的模块代码

```bash
# 查看区块链模块
ls ARCHIVE/modules/otlp/blockchain/

# 查看边缘计算模块
ls ARCHIVE/modules/otlp/edge_computing/

# 查看 AI/ML 模块
ls ARCHIVE/modules/otlp/ai_ml/
```

### 查找归档的文档

```bash
# 查看归档的文档
ls ARCHIVE/docs/

# 查看归档的报告
ls ARCHIVE/reports/
```

---

## ⚠️ 重要说明

1. **归档内容仍然可用**: 归档的内容仍然保留在项目中，只是不再作为核心功能维护
2. **不推荐使用**: 归档的模块和文档不再接受更新，不推荐在新项目中使用
3. **历史参考**: 归档内容仅作为历史参考和研究用途
4. **误导性内容**: 特别是eBPF相关文档，描述的功能实际上是模拟实现，**不应在生产环境使用**
5. **恢复方法**: 如需恢复归档内容，可以从 `ARCHIVE/` 目录中复制回原位置

---

## 📝 更新记录

- **2026-03-17**: 清理归档，移动过时的完成报告、误导性eBPF文档、临时构建输出等
  - 归档了12个重复的"100%完成"报告
  - 归档了21个eBPF相关文档（功能为模拟实现）
  - 归档了16个过时的分析报告
  - 归档了8个临时Clippy输出文件
  - 归档了2个过时的指南文件
- **2025-01-13**: 初始归档，移动 blockchain、edge_computing、ai_ml 模块及相关文档

---

## 🔗 相关链接

- [项目 README](../README.md)
- [项目状态](../PROJECT_STATUS.md) - 真实的项目状态
- [核心主题文档](../docs/INDEX.md)
- [OTLP 模块文档](../crates/otlp/README.md)
- [Reliability 模块文档](../crates/reliability/README.md)
