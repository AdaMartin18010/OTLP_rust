# 📋 文档清理决策记录 2025-10-26

**决策时间**: 2025年10月26日  
**状态**: ✅ 已确认

---

## 🎯 关键决策

### 1. Analysis 主题21和22处理 ✅

**决策**: **独立保留，移动到归档目录**

**理由**:

- 两个主题虽有重叠，但各有独特价值
- 主题21侧重语义模型和代码原型
- 主题22侧重综合分析和性能基准

**执行方案**:

```
analysis/
├── archives/
│   ├── 21_rust_otlp_semantic_models/  (保留原内容)
│   └── 22_rust_1.90_otlp_comprehensive_analysis/  (保留原内容)
└── [01-20, 23-27保持当前位置]
```

---

### 2. 前沿主题23-27处理 ✅

**决策**: **保留**

**理由**:

- 代表未来研究方向
- 为后续扩展保留空间
- 标记为实验性/研究性主题

**执行方案**:

```
analysis/
├── 23_quantum_inspired_observability/  (保留)
├── 24_neuromorphic_monitoring/  (保留)
├── 25_edge_ai_fusion/  (保留)
├── 26_semantic_interoperability/  (保留)
└── 27_resilience_engineering/  (保留)
```

在各主题README中添加状态标签：

```markdown
**状态**: 🧪 实验性/研究阶段
```

---

### 3. 命名规范 ✅

**决策**: **采用英文**

**理由**:

- 便于编程引用
- 国际化友好
- 避免编码问题

**执行方案**:

**目录命名**:

```
✅ 01_getting_started/
✅ tier_01_foundations/
✅ analysis/rust_otlp_models/
```

**文件命名**:

```
✅ quick-start.md
✅ installation-guide.md
✅ api-reference.md
```

**内容**: 保持中文（面向中文用户）

---

### 4. Legacy内容处理 ✅

**决策**: **评估价值，选择性压缩归档**

**执行方案**:

```
crates/model/docs/archives/
├── legacy_summary.md  (压缩所有legacy_*的总结)
└── legacy_backup/  (完整备份，可选)
```

---

## 🚀 清理执行计划

### 阶段1: 立即执行（今天）

**任务1.1**: 运行自动清理脚本

```bash
bash scripts/doc_cleanup_2025_10_26.sh
```

**任务1.2**: 移动analysis主题到归档

```bash
# 创建archives目录
mkdir -p analysis/archives/historical_analysis

# 移动主题21和22
mv analysis/21_rust_otlp_semantic_models analysis/archives/historical_analysis/
mv analysis/22_rust_1.90_otlp_comprehensive_analysis analysis/archives/historical_analysis/

# 更新INDEX.md
```

**任务1.3**: 标记前沿主题状态

```bash
# 在23-27各主题的README开头添加状态标签
```

---

### 阶段2: 明天执行

**任务2.1**: 合并otlp重复文档

- 合并API文档
- 合并用户指南
- 删除重复目录

**任务2.2**: 统一crates文档结构

- 删除libraries数字命名文档
- 合并guides到tier_02_guides
- 压缩model的legacy_*

**任务2.3**: 规范化命名

- 将中文目录/文件名改为英文
- 保持内容为中文

---

## ✅ 决策总结

| 决策项 | 决定 | 状态 |
|--------|------|------|
| analysis主题21和22 | 独立保留，归档 | ✅ 已确认 |
| 前沿主题23-27 | 保留 | ✅ 已确认 |
| 命名规范 | 英文 | ✅ 已确认 |
| legacy内容 | 压缩归档 | ✅ 已确认 |

---

## 📊 预期成果

执行完成后：

- ✅ ~100个临时报告已归档
- ✅ analysis主题21和22已归档保存
- ✅ 前沿主题已标记状态
- ✅ 所有命名统一为英文
- ✅ 结构清晰，便于维护

---

**决策人**: 用户  
**记录人**: AI Assistant  
**执行开始**: 2025年10月26日  
**预计完成**: 2025年10月27日

