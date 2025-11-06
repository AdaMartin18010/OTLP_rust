#!/bin/bash
# 验证所有Markdown文件的目录格式

PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"

echo "========================================="
echo "验证Markdown文件目录格式"
echo "========================================="
echo ""

TOTAL=0
CORRECT=0
NO_TOC=0
DUPLICATE=0
WRONG_FORMAT=0

find "$PROJECT_ROOT" -name "*.md" -type f \
    ! -path "*/target/*" \
    ! -path "*/.git/*" \
    ! -path "*/node_modules/*" \
    ! -path "*/.vscode/*" \
    ! -path "*/.github/*" \
| while read -r file; do
    ((TOTAL++))
    rel_path="${file#$PROJECT_ROOT/}"

    # 查找目录数量
    toc_count=$(grep -c "^## 📋 目录$" "$file" 2>/dev/null || echo "0")

    if [ "$toc_count" -eq 0 ]; then
        # 检查是否有其他格式的目录
        alt_count=$(grep -c "^##.*📋.*目录$\|^##.*目录$" "$file" 2>/dev/null || echo "0")
        if [ "$alt_count" -eq 0 ]; then
            ((NO_TOC++))
        else
            echo "⚠️  非标准格式: $rel_path"
            ((WRONG_FORMAT++))
        fi
    elif [ "$toc_count" -eq 1 ]; then
        # 检查格式是否正确（标题后是否有空行）
        toc_line=$(grep -n "^## 📋 目录$" "$file" | head -1 | cut -d: -f1)
        next_line=$(sed -n "$((toc_line + 1))p" "$file")
        if [ -z "$next_line" ]; then
            ((CORRECT++))
        else
            echo "⚠️  格式问题: $rel_path (目录后缺少空行)"
            ((WRONG_FORMAT++))
        fi
    else
        echo "❌ 重复目录: $rel_path (发现 $toc_count 个)"
        ((DUPLICATE++))
    fi
done

echo ""
echo "========================================="
echo "验证完成"
echo "========================================="
echo "总文件数: $TOTAL"
echo "格式正确: $CORRECT"
echo "无目录: $NO_TOC"
echo "重复目录: $DUPLICATE"
echo "格式问题: $WRONG_FORMAT"
echo ""
