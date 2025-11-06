#!/bin/bash
# 检查并统一Markdown文件的目录格式

PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
ANALYSIS_DIR="$PROJECT_ROOT/analysis"

echo "检查Markdown文件的目录格式..."

# 查找所有包含目录的Markdown文件
find "$ANALYSIS_DIR" -name "*.md" -type f | while read -r file; do
    # 检查是否有目录标题
    if grep -q "^##[#]*\s*📋\s*目录\|^##[#]*\s*目录" "$file"; then
        # 检查格式是否正确
        if ! grep -q "^##\s*📋\s*目录" "$file"; then
            echo "需要修复: $file"
            # 这里可以添加修复逻辑
        fi
    fi
done

echo "检查完成！"
