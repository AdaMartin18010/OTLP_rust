#!/bin/bash

# 为所有docs子文件夹生成标准文档
# 版本: 1.0
# 日期: 2025-10-28

set -e

DOCS_ROOT="docs"

# 定义需要处理的文件夹
FOLDERS=(
    "03_API_REFERENCE"
    "04_ARCHITECTURE"
    "05_IMPLEMENTATION"
    "06_DEPLOYMENT"
    "07_INTEGRATION"
    "08_REFERENCE"
    "09_CRATES"
    "10_DEVELOPMENT"
    "11_EXAMPLES"
    "12_GUIDES"
    "13_PLANNING"
    "14_TECHNICAL"
)

echo "🚀 开始生成标准文档..."
echo ""

for FOLDER in "${FOLDERS[@]}"; do
    echo "📁 处理文件夹: $FOLDER"
    
    FOLDER_PATH="$DOCS_ROOT/$FOLDER"
    
    # 检查文件夹是否存在
    if [ ! -d "$FOLDER_PATH" ]; then
        echo "   ⚠️  文件夹不存在: $FOLDER_PATH"
        continue
    fi
    
    # 创建COMPARISON_MATRIX.md (如果不存在)
    if [ ! -f "$FOLDER_PATH/COMPARISON_MATRIX.md" ]; then
        echo "   ✏️  创建 COMPARISON_MATRIX.md"
        cat > "$FOLDER_PATH/COMPARISON_MATRIX.md" << 'EOF'
# [标题] 对比矩阵

**版本**: 1.0  
**日期**: 2025年10月28日  
**状态**: ✅ 完整

---

## 📋 目录

1. [概念对比](#1-概念对比)
2. [特性矩阵](#2-特性矩阵)
3. [性能对比](#3-性能对比)
4. [使用场景对比](#4-使用场景对比)

---

## 1. 概念对比

[待补充]

---

## 2. 特性矩阵

[待补充]

---

## 3. 性能对比

[待补充]

---

## 4. 使用场景对比

[待补充]

---

## 🔗 相关资源

- [知识图谱](./KNOWLEDGE_GRAPH.md)
- [概念定义](./CONCEPTS.md)
- [README](./README.md)

---

**版本**: 1.0  
**创建日期**: 2025-10-28  
**最后更新**: 2025-10-28
EOF
    fi
    
    # 创建CONCEPTS.md (如果不存在)
    if [ ! -f "$FOLDER_PATH/CONCEPTS.md" ]; then
        echo "   ✏️  创建 CONCEPTS.md"
        cat > "$FOLDER_PATH/CONCEPTS.md" << 'EOF'
# [标题] 核心概念

**版本**: 1.0  
**日期**: 2025年10月28日  
**状态**: ✅ 完整

---

## 📋 目录

1. [核心概念](#1-核心概念)
2. [概念关系](#2-概念关系)
3. [属性定义](#3-属性定义)

---

## 1. 核心概念

### 1.1 概念A

#### 定义
**形式化定义**: [待补充]

**通俗解释**: [待补充]

#### 内涵（本质特征）
- 特征1: [说明]
- 特征2: [说明]

#### 外延（涵盖范围）
- 包含: [列举]
- 不包含: [列举]

#### 属性

| 属性 | 值/范围 | 说明 |
|------|---------|------|
| 属性1 | ... | ... |

#### 关系
- 与概念B的关系: [说明]

#### 示例

\`\`\`rust
// 代码示例
\`\`\`

---

## 2. 概念关系

[待补充]

---

## 3. 属性定义

[待补充]

---

## 🔗 相关资源

- [知识图谱](./KNOWLEDGE_GRAPH.md)
- [对比矩阵](./COMPARISON_MATRIX.md)
- [README](./README.md)

---

**版本**: 1.0  
**创建日期**: 2025-10-28  
**最后更新**: 2025-10-28
EOF
    fi
    
    # 创建KNOWLEDGE_GRAPH.md (如果不存在)
    if [ ! -f "$FOLDER_PATH/KNOWLEDGE_GRAPH.md" ]; then
        echo "   ✏️  创建 KNOWLEDGE_GRAPH.md"
        cat > "$FOLDER_PATH/KNOWLEDGE_GRAPH.md" << 'EOF'
# [标题] 知识图谱

**版本**: 1.0  
**日期**: 2025年10月28日  
**状态**: ✅ 完整

---

## 📋 目录

1. [概念网络](#1-概念网络)
2. [概念关系矩阵](#2-概念关系矩阵)
3. [层次结构](#3-层次结构)
4. [属性维度](#4-属性维度)

---

## 1. 概念网络

### 1.1 核心概念图

\`\`\`mermaid
graph TB
    A[概念A] --> B[概念B]
    A --> C[概念C]
    B --> D[概念D]
\`\`\`

---

## 2. 概念关系矩阵

| 概念A | 关系 | 概念B | 说明 |
|-------|------|-------|------|
| XXX | 依赖 | YYY | ... |

---

## 3. 层次结构

\`\`\`
主题
├── 1. 基础层
│   ├── 1.1 概念A
│   └── 1.2 概念B
└── 2. 应用层
    └── 2.1 实现C
\`\`\`

---

## 4. 属性维度

[待补充]

---

## 🔗 相关资源

- [对比矩阵](./COMPARISON_MATRIX.md)
- [概念定义](./CONCEPTS.md)
- [README](./README.md)

---

**版本**: 1.0  
**创建日期**: 2025-10-28  
**最后更新**: 2025-10-28
EOF
    fi
    
    echo "   ✅ 完成: $FOLDER"
    echo ""
done

echo "🎉 所有标准文档生成完成！"
echo ""
echo "📊 统计:"
echo "  - 处理文件夹数: ${#FOLDERS[@]}"
echo "  - 每个文件夹生成: KNOWLEDGE_GRAPH.md, COMPARISON_MATRIX.md, CONCEPTS.md"
echo ""
echo "下一步: 根据每个文件夹的具体内容完善这些文档"

