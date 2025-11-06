#!/bin/bash
# 统一所有Markdown文件的目录格式 - 改进版本

set -euo pipefail

PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
STANDARD_TOC="## 📋 目录"

# 统计
TOTAL=0
PROCESSED=0
NO_TOC=0
DUPLICATE_REMOVED=0
FORMAT_FIXED=0
ERRORS=0

echo "========================================="
echo "统一所有Markdown文件的目录格式"
echo "========================================="
echo ""

process_file() {
    local file="$1"
    local rel_path="${file#$PROJECT_ROOT/}"

    ((TOTAL++))

    # 读取文件
    local temp_file=$(mktemp)
    cp "$file" "$temp_file"

    local has_toc=false
    local modified=false

    # 查找所有目录行号
    local toc_lines=$(grep -n "^##.*📋.*目录$\|^##.*目录$" "$temp_file" 2>/dev/null | cut -d: -f1 || true)

    if [ -z "$toc_lines" ]; then
        # 没有目录，跳过（某些文件可能不需要目录）
        ((NO_TOC++))
        rm -f "$temp_file"
        return 0
    fi

    local toc_count=$(echo "$toc_lines" | wc -l | tr -d ' ')

    # 处理多个目录的情况
    if [ "$toc_count" -gt 1 ]; then
        echo "🔧 删除重复目录: $rel_path (发现 $toc_count 个)"
        ((DUPLICATE_REMOVED++))

        # 获取第一个目录的行号
        local first_toc=$(echo "$toc_lines" | head -1)
        local other_tocs=$(echo "$toc_lines" | tail -n +2)

        # 从后往前删除，避免行号变化
        echo "$other_tocs" | tac | while read -r line_num; do
            [ -z "$line_num" ] && continue

            # 找到这个目录部分的结束位置
            local end_line=$(sed -n "${line_num},\$p" "$temp_file" | grep -n "^##" | head -2 | tail -1 | cut -d: -f1)

            if [ -z "$end_line" ]; then
                # 删除到文件末尾
                sed -i "${line_num},\$d" "$temp_file"
            else
                end_line=$((line_num + end_line - 2))
                # 删除目录部分
                sed -i "${line_num},${end_line}d" "$temp_file"
            fi
        done

        modified=true
        has_toc=true
    else
        has_toc=true
    fi

    # 统一格式
    if [ "$has_toc" = true ]; then
        # 重新查找目录行号（可能在删除后变化）
        local toc_line=$(grep -n "^##.*📋.*目录$\|^##.*目录$" "$temp_file" 2>/dev/null | head -1 | cut -d: -f1 || true)

        if [ -n "$toc_line" ]; then
            # 检查格式
            local toc_content=$(sed -n "${toc_line}p" "$temp_file")
            local next_line=$(sed -n "$((toc_line + 1))p" "$temp_file" || echo "")

            local needs_fix=false

            # 检查标题格式
            if ! echo "$toc_content" | grep -q "^##.*📋.*目录$"; then
                needs_fix=true
            fi

            # 检查空行
            if [ -n "$next_line" ] && [ "$next_line" != "" ]; then
                needs_fix=true
            fi

            if [ "$needs_fix" = true ]; then
                echo "🔧 统一格式: $rel_path"
                ((FORMAT_FIXED++))

                # 修复标题
                sed -i "${toc_line}s/.*/$STANDARD_TOC/" "$temp_file"

                # 确保后面有空行
                if [ -n "$next_line" ] && [ "$next_line" != "" ]; then
                    sed -i "${toc_line}a\\" "$temp_file"
                fi

                modified=true
            fi
        fi
    fi

    # 保存修改
    if [ "$modified" = true ]; then
        mv "$temp_file" "$file"
        ((PROCESSED++))
    else
        rm -f "$temp_file"
    fi

    return 0
}

# 主循环
echo "开始处理文件..."
echo ""

# 查找所有Markdown文件
while IFS= read -r -d '' file; do
    # 排除某些路径
    if [[ "$file" == */target/* ]] || \
       [[ "$file" == */.git/* ]] || \
       [[ "$file" == */node_modules/* ]] || \
       [[ "$file" == */.vscode/* ]] || \
       [[ "$file" == */.github/* ]]; then
        continue
    fi

    if ! process_file "$file"; then
        ((ERRORS++))
        echo "❌ 处理失败: ${file#$PROJECT_ROOT/}"
    fi
done < <(find "$PROJECT_ROOT" -name "*.md" -type f -print0)

echo ""
echo "========================================="
echo "处理完成！"
echo "========================================="
echo "总文件数: $TOTAL"
echo "已有目录: $PROCESSED"
echo "无目录文件: $NO_TOC"
echo "删除重复目录: $DUPLICATE_REMOVED"
echo "统一格式: $FORMAT_FIXED"
[ $ERRORS -gt 0 ] && echo "错误: $ERRORS"
echo ""
