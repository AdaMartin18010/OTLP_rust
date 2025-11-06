#!/bin/bash
# 修复目录中使用编号格式的文件，转换为标准格式

PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"

echo "修复目录中的编号格式列表..."

find "$PROJECT_ROOT" -name "*.md" -type f \
    ! -path "*/target/*" \
    ! -path "*/.git/*" \
    ! -path "*/node_modules/*" \
| while read -r file; do
    # 检查是否有目录
    if ! grep -q "^## 📋 目录$" "$file" 2>/dev/null; then
        continue
    fi

    # 查找目录行号
    toc_line=$(grep -n "^## 📋 目录$" "$file" | head -1 | cut -d: -f1)

    # 检查目录部分是否有编号格式
    has_numbered=false
    for i in $(seq $((toc_line + 2)) $((toc_line + 50))); do
        line=$(sed -n "${i}p" "$file" 2>/dev/null)
        if [ -z "$line" ] || echo "$line" | grep -q "^##\|^---"; then
            break
        fi
        if echo "$line" | grep -q "^[0-9]\+\.\s\+\["; then
            has_numbered=true
            break
        fi
    done

    if [ "$has_numbered" = true ]; then
        echo "修复: $file"
        # 使用sed修复：将编号格式转换为标准格式
        # 在目录部分内，将 "数字. " 替换为 "- "
        sed -i "${toc_line},/^##/ {
            s/^\(\s*\)[0-9]\+\.\s\+\[/\1- [/g
        }" "$file"
    fi
done

echo "完成！"
