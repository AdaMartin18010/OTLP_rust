# Deprecated Documentation Structure

**归档日期**: 2025年10月26日  
**原因**: 文档结构重组，统一为编号目录格式

---

## 📂 归档内容

本目录包含已被废弃的旧文档结构，主要是在文档重组过程中被替代的目录。

### 目录说明

#### `api/` (已废弃)
- **状态**: 已迁移到 `03_API_REFERENCE/`
- **文件数**: 3 个
- **内容**: OTLP API 参考文档
- **说明**: 该目录的 README.md 已包含迁移通知，指向新的 `03_API_REFERENCE/` 目录

#### `architecture/` (已废弃)
- **状态**: 已合并到 `04_ARCHITECTURE/`
- **文件数**: 3 个
- **内容**: 系统架构和模块设计文档
- **说明**: 该目录的完整内容已合并到 `04_ARCHITECTURE/`，包括：
  - `system-architecture.md` → `04_ARCHITECTURE/system_architecture.md`
  - `module-design.md` → `04_ARCHITECTURE/module_design.md`

---

## 🔄 迁移映射

| 旧位置 | 新位置 | 状态 |
|--------|--------|------|
| `api/otlp.md` | `03_API_REFERENCE/README.md` | ✅ 已迁移 |
| `api/README.md` | `03_API_REFERENCE/README.md` | ✅ 已迁移 |
| `api/reliability.md` | `03_API_REFERENCE/README.md` | ✅ 已迁移 |
| `architecture/system-architecture.md` | `04_ARCHITECTURE/system_architecture.md` | ✅ 已合并 |
| `architecture/module-design.md` | `04_ARCHITECTURE/module_design.md` | ✅ 已合并 |
| `architecture/README.md` | `04_ARCHITECTURE/README.md` | ✅ 已合并 |

---

## ⚠️ 重要说明

- **不要修改**: 这些文件仅用于归档和历史参考，不应再进行修改
- **使用新结构**: 请使用 `docs/` 下的新编号目录结构
- **链接失效**: 指向这些旧文件的链接可能已失效，请参考新文档结构

---

## 📖 新文档结构

新的文档结构采用统一的编号目录格式：

```
docs/
├── 00_INDEX/              # 文档索引和导航
├── 01_GETTING_STARTED/    # 快速开始
├── 02_THEORETICAL_FRAMEWORK/  # 理论框架
├── 03_API_REFERENCE/      # API 参考 (原 api/)
├── 04_ARCHITECTURE/       # 架构设计 (原 architecture/)
├── 05_IMPLEMENTATION/     # 实现指南
├── 06_DEPLOYMENT/         # 部署运维
├── 07_INTEGRATION/        # 集成指南
├── 08_REFERENCE/          # 参考资料
├── 09_CRATES/             # Crates 文档
├── 10_DEVELOPMENT/        # 开发指南
├── 11_EXAMPLES/           # 示例代码
├── 12_GUIDES/             # 详细指南
├── 13_PLANNING/           # 规划文档
└── 14_TECHNICAL/          # 技术文档
```

---

**如有问题，请参考**: [docs/README.md](../../README.md)

