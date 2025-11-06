# 文档质量检查清单

**版本**: 1.0
**日期**: 2025年10月28日
**用途**: 确保文档符合标准

---

## 📋 快速检查清单

### ✅ 基本结构

- [ ] 文档有标准头部（版本、日期、状态）
- [ ] 文档有完整目录（使用`## 📋 目录`）
- [ ] 文档有标准尾部（相关资源、版本信息）
- [ ] 所有标题使用数字编号（1. 2. 3.）
- [ ] 文档结构符合模板要求

### ✅ 内容质量

- [ ] 有明确的概述/简介
- [ ] 有实质性内容（非空模板）
- [ ] 代码示例可运行
- [ ] 有量化数据（性能、对比等）
- [ ] 有实际案例
- [ ] 链接全部有效

### ✅ 格式规范

- [ ] Markdown格式正确
- [ ] 代码块有语言标识
- [ ] 表格格式正确
- [ ] 无拼写错误
- [ ] 无明显语法错误

---

## 📊 详细检查项

### 1. 文件夹级别检查

每个docs/子文件夹必须包含：

```bash
folder_name/
├── README.md               ✅ 必需
├── KNOWLEDGE_GRAPH.md     ✅ 必需
├── COMPARISON_MATRIX.md   ✅ 必需
└── CONCEPTS.md            ✅ 必需
```

**检查命令**:

```bash
ls docs/*/KNOWLEDGE_GRAPH.md | wc -l  # 应为14
ls docs/*/COMPARISON_MATRIX.md | wc -l  # 应为14
ls docs/*/CONCEPTS.md | wc -l  # 应为14
```

---

### 2. KNOWLEDGE_GRAPH.md 检查

#### 必须包含

- [ ] 概念网络图（Mermaid）
- [ ] 概念关系矩阵（表格）
- [ ] 层次结构（树形图或Mermaid）
- [ ] 属性维度分析
- [ ] 至少5个核心概念

#### 内容质量

- [ ] Mermaid图表能正确渲染
- [ ] 概念关系清晰
- [ ] 层次结构合理
- [ ] 有具体示例

#### 示例检查

```markdown
✅ 好的Mermaid图表：
\`\`\`mermaid
graph TB
    A[概念A] --> B[概念B]
    A --> C[概念C]
\`\`\`

❌ 坏的Mermaid图表：
\`\`\`mermaid
// 空的或语法错误
\`\`\`
```

---

### 3. COMPARISON_MATRIX.md 检查

#### 必须包含

- [ ] 至少3个维度的对比
- [ ] 量化数据（性能、复杂度等）
- [ ] 使用场景对比
- [ ] 推荐建议

#### 内容质量

- [ ] 对比维度合理
- [ ] 数据准确可靠
- [ ] 有实际测试结果
- [ ] 结论明确

#### 示例检查

```markdown
✅ 好的对比表格：
| 方案 | 性能 | 复杂度 | 适用场景 | 推荐度 |
|------|------|--------|----------|--------|
| A    | 100K/s | ⭐⭐ | 小型 | ⭐⭐⭐⭐⭐ |
| B    | 50K/s | ⭐⭐⭐⭐ | 大型 | ⭐⭐⭐ |

❌ 坏的对比表格：
| 方案 | 评价 |
|------|------|
| A    | 好   |
| B    | 一般 |
```

---

### 4. CONCEPTS.md 检查

#### 必须包含（每个概念）

- [ ] 形式化定义
- [ ] 通俗解释
- [ ] 内涵（本质特征）
- [ ] 外延（涵盖范围）
- [ ] 属性表格
- [ ] 关系说明
- [ ] 代码示例

#### 内容质量

- [ ] 定义准确清晰
- [ ] 示例可运行
- [ ] 概念间关系明确
- [ ] 属性完整

#### 示例检查

```markdown
✅ 好的概念定义：
### 1.1 Actor模型

#### 定义
**形式化定义**: Actor = (Identity, Behavior, Mailbox)

**通俗解释**: Actor是独立的计算实体...

#### 内涵
- 隔离性: 无共享状态
- 异步性: 消息传递

#### 外延
- 包含: 经典Actor, Typed Actor
- 不包含: 同步通信模型

#### 示例
\`\`\`rust
// 可运行的代码
\`\`\`

❌ 坏的概念定义：
### Actor
Actor是一种模型。
```

---

### 5. README.md 检查

#### 必须包含

- [ ] 文件夹概述
- [ ] 文档清单
- [ ] 快速导航链接
- [ ] 学习路径建议
- [ ] 链接到标准文档（KNOWLEDGE_GRAPH等）

#### 示例模板

```markdown
# [文件夹名称]

## 📋 概述
[2-3段说明]

## 📂 文档清单
- [KNOWLEDGE_GRAPH.md](./KNOWLEDGE_GRAPH.md)
- [COMPARISON_MATRIX.md](./COMPARISON_MATRIX.md)
- [CONCEPTS.md](./CONCEPTS.md)

## 🗺️ 快速导航
...
```

---

## 🔍 自动化检查脚本

### 检查脚本1: 结构完整性

```bash
#!/bin/bash

echo "检查文档结构完整性..."
ERRORS=0

for folder in docs/*/; do
    folder_name=$(basename "$folder")

    # 跳过archives和reports
    if [[ "$folder_name" == "archives" || "$folder_name" == "reports" ]]; then
        continue
    fi

    echo "检查: $folder_name"

    if [ ! -f "$folder/KNOWLEDGE_GRAPH.md" ]; then
        echo "  ❌ 缺少 KNOWLEDGE_GRAPH.md"
        ERRORS=$((ERRORS + 1))
    fi

    if [ ! -f "$folder/COMPARISON_MATRIX.md" ]; then
        echo "  ❌ 缺少 COMPARISON_MATRIX.md"
        ERRORS=$((ERRORS + 1))
    fi

    if [ ! -f "$folder/CONCEPTS.md" ]; then
        echo "  ❌ 缺少 CONCEPTS.md"
        ERRORS=$((ERRORS + 1))
    fi
done

if [ $ERRORS -eq 0 ]; then
    echo "✅ 所有文件夹结构完整！"
else
    echo "❌ 发现 $ERRORS 个问题"
    exit 1
fi
```

### 检查脚本2: 链接有效性

```bash
#!/bin/bash

echo "检查链接有效性..."

# 使用markdown-link-check
for file in docs/**/*.md; do
    echo "检查: $file"
    markdown-link-check "$file" || true
done
```

### 检查脚本3: 格式检查

```bash
#!/bin/bash

echo "检查Markdown格式..."

# 使用markdownlint
markdownlint docs/**/*.md --config .markdownlint.json
```

---

## 📈 质量评分

### 评分标准

```
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
维度             权重    评分方法
────────────────────────────────────────
结构完整性       25%     检查必需文件和章节
内容实质性       30%     检查示例、数据完整度
格式规范性       15%     Markdown格式检查
链接有效性       10%     链接检查工具
概念清晰度       20%     人工评审
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
总分 = Σ(维度得分 × 权重)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 等级划分

| 总分 | 等级 | 说明 |
|------|------|------|
| 9.0-10.0 | ⭐⭐⭐⭐⭐ | 优秀 - 可作为标杆 |
| 8.0-8.9 | ⭐⭐⭐⭐ | 良好 - 符合标准 |
| 7.0-7.9 | ⭐⭐⭐ | 合格 - 需要改进 |
| 6.0-6.9 | ⭐⭐ | 待改进 |
| < 6.0 | ⭐ | 不合格 |

---

## 🔧 常见问题修复

### 问题1: 编号不一致

**症状**: 使用A. B. C.或I. II. III.

**修复**:

```bash
# 全局替换
sed -i 's/^## A\. /## 1. /g' file.md
sed -i 's/^### A\.1 /### 1.1 /g' file.md
```

### 问题2: 缺少目录

**症状**: 没有`## 📋 目录`部分

**修复**: 使用VSCode的Markdown All in One插件自动生成

### 问题3: 代码块无语言标识

**症状**: \`\`\` 而非 \`\`\`rust

**修复**:

```bash
# 手动添加语言标识
```

### 问题4: 链接失效

**症状**: 点击链接404

**修复**:

1. 检查文件路径
2. 更新相对路径
3. 确认文件存在

---

## 📝 检查工作流

### 每次编辑后

1. 运行markdownlint
2. 检查代码示例能否编译
3. 预览Mermaid图表
4. 检查内部链接

### 每周

1. 运行完整性检查脚本
2. 运行链接检查
3. 更新过时内容
4. 检查新增文件

### 每月

1. 全面质量评估
2. 用户反馈收集
3. 改进计划制定
4. 版本号更新

---

## ✅ 最终检查

在提交PR前，确保：

- [ ] 运行所有自动化检查脚本，全部通过
- [ ] 至少一位同事评审
- [ ] 所有TODO/FIXME已处理或记录
- [ ] 更新了相关的索引文档
- [ ] Git commit message清晰

---

**检查清单版本**: 1.0
**最后更新**: 2025-10-28
**维护者**: OTLP_rust文档团队
