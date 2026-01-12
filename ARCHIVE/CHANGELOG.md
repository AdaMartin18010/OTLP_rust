# 归档变更日志

## 2025-01-13

### 初始归档

#### 归档的模块

- **blockchain** - 区块链模块
  - 位置: `crates/otlp/src/blockchain/` → `ARCHIVE/modules/otlp/blockchain/`
  - 原因: 不属于 OTLP 核心功能
  - 状态: 已从 `crates/otlp/src/lib.rs` 中移除导出

- **edge_computing** - 边缘计算模块
  - 位置: `crates/otlp/src/edge_computing/` → `ARCHIVE/modules/otlp/edge_computing/`
  - 原因: 不属于 OTLP 核心功能
  - 状态: 已从 `crates/otlp/src/lib.rs` 中移除导出

- **ai_ml** - AI/ML 模块
  - 位置: `crates/otlp/src/ai_ml/` → `ARCHIVE/modules/otlp/ai_ml/`
  - 原因: 不属于 OTLP 核心功能
  - 状态: 已从 `crates/otlp/src/lib.rs` 中移除导出

#### 归档的文档

- `docs/BLOCKCHAIN_GUIDE_2025.md` → `ARCHIVE/docs/blockchain/`
- `docs/EDGE_COMPUTING_GUIDE_2025.md` → `ARCHIVE/docs/edge_computing/`
- `docs/AI_ML_GUIDE_2025.md` → `ARCHIVE/docs/ai_ml/`

#### 归档的报告

根目录和 `docs/` 目录下的各种完成报告、进度报告、计划文档等已归档到 `ARCHIVE/reports/`。

#### 更新的文件

- `docs/INDEX.md` - 更新索引，移除已归档文档链接，添加归档说明
- `docs/MODULE_DOCUMENTATION_STATUS_2025.md` - 标记已归档模块
- `README.md` - 添加归档说明
- `ARCHIVE/README.md` - 创建归档说明文档
- `ARCHIVE/ARCHIVE_SUMMARY.md` - 创建归档总结文档

---

## 归档原则

1. **核心主题优先**: 只保留与4个核心主题（otlp, reliability, model, libraries）直接相关的内容
2. **非核心功能归档**: 不属于核心功能的模块和文档归档但不删除
3. **历史保留**: 归档内容作为历史参考保留
4. **清晰标记**: 所有归档内容都有明确的标记和说明

---

## 恢复方法

如需恢复归档内容：

1. 从 `ARCHIVE/modules/` 复制模块代码回 `crates/otlp/src/`
2. 从 `ARCHIVE/docs/` 复制文档回 `docs/`
3. 在 `crates/otlp/src/lib.rs` 中取消注释相应的模块导出
4. 更新相关索引文件
