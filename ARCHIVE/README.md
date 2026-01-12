# 归档目录说明

**创建日期**: 2025-01-13
**目的**: 归档非核心主题，保持项目结构清晰

---

## 📂 归档结构

```
ARCHIVE/
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

本项目专注于以下 **4个核心主题**：

1. **`otlp`** - OpenTelemetry Protocol 实现
2. **`reliability`** - 统一可靠性框架
3. **`model`** - 理论模型实现库
4. **`libraries`** - Rust 生态成熟库集成

---

## 📋 归档内容

### 已归档的模块

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

### 查找归档的模块代码

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
4. **恢复方法**: 如需恢复归档内容，可以从 `ARCHIVE/` 目录中复制回原位置

---

## 📝 更新记录

- **2025-01-13**: 初始归档，移动 blockchain、edge_computing、ai_ml 模块及相关文档

---

## 🔗 相关链接

- [项目 README](../README.md)
- [核心主题文档](../docs/INDEX.md)
- [OTLP 模块文档](../crates/otlp/README.md)
- [Reliability 模块文档](../crates/reliability/README.md)
- [Model 模块文档](../crates/model/README.md)
- [Libraries 模块文档](../crates/libraries/README.md)
