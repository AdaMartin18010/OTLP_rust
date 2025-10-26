#!/bin/bash
# OTLP Rust 文档链接验证脚本
# 用于检查文档中的内部链接是否有效

set -e

echo "🔗 开始链接验证..."
echo ""

# 配置
DOCS_DIRS=("crates/otlp/docs" "crates/libraries/docs" "crates/model/docs" "crates/reliability/docs" "docs")
BROKEN_LINKS=0

# 验证内部链接
validate_internal_links() {
    echo "📝 验证内部链接..."
    
    for dir in "${DOCS_DIRS[@]}"; do
        if [ -d "$dir" ]; then
            echo "检查目录: $dir"
            
            # 查找所有Markdown文件中的内部链接
            find "$dir" -name "*.md" -type f | while read -r file; do
                # 提取相对路径链接（简化版）
                grep -o '\[.*\]([^h][^t][^t][^p].*\.md)' "$file" 2>/dev/null || true | while read -r link; do
                    # 提取文件路径
                    target=$(echo "$link" | sed 's/.*](\(.*\))/\1/')
                    target_file=$(dirname "$file")/"$target"
                    
                    # 检查文件是否存在
                    if [ ! -f "$target_file" ]; then
                        echo "❌ 断链: $file -> $target"
                        ((BROKEN_LINKS++))
                    fi
                done
            done
        fi
    done
    
    echo "✅ 内部链接验证完成"
    echo ""
}

# 主执行流程
main() {
    validate_internal_links
    
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    
    if [ $BROKEN_LINKS -eq 0 ]; then
        echo "✅ 所有链接有效！"
        echo ""
        exit 0
    else
        echo "❌ 发现 $BROKEN_LINKS 个断链"
        echo "请修复后再提交"
        echo ""
        exit 1
    fi
}

# 运行主函数
main

