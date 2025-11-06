#!/bin/bash
# 查找包含多个目录的文件

PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
ANALYSIS_DIR="$PROJECT_ROOT/analysis"

echo "查找包含多个目录的文件..."

find "$ANALYSIS_DIR" -name "*.md" -type f | while read -r file; do
    # 查找所有 "## 📋 目录" 标题
    count=$(grep -c "^## 📋 目录$" "$file" 2>/dev/null || echo "0")
    if [ "$count" -gt 1 ]; then
        echo "发现 $count 个目录: $file"
        grep -n "^## 📋 目录$" "$file"
        echo "---"
    fi
done

echo "检查完成！"
