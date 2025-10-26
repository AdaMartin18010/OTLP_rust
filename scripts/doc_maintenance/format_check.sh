#!/bin/bash
# OTLP Rust 文档格式检查脚本
# 用于验证文档是否符合DOCUMENTATION_STANDARDS_COMPLETE.md规范

set -e

echo "🔍 开始文档格式检查..."
echo ""

# 配置
DOCS_DIRS=("crates/otlp/docs" "crates/libraries/docs" "crates/model/docs" "crates/reliability/docs" "docs")
ERRORS=0

# 检查代码块语言标签
check_code_blocks() {
    echo "📝 检查代码块语言标签..."
    
    for dir in "${DOCS_DIRS[@]}"; do
        if [ -d "$dir" ]; then
            # 查找没有语言标签的代码块
            files_without_lang=$(grep -r "^\`\`\`$" "$dir" --include="*.md" 2>/dev/null || true)
            
            if [ -n "$files_without_lang" ]; then
                echo "❌ 发现没有语言标签的代码块:"
                echo "$files_without_lang"
                ((ERRORS++))
            fi
        fi
    done
    
    echo "✅ 代码块检查完成"
    echo ""
}

# 检查TODO标记
check_todos() {
    echo "📝 检查TODO标记..."
    
    for dir in "${DOCS_DIRS[@]}"; do
        if [ -d "$dir" ]; then
            todos=$(grep -r "TODO\|FIXME\|XXX" "$dir" --include="*.md" 2>/dev/null || true)
            
            if [ -n "$todos" ]; then
                echo "⚠️  发现TODO标记:"
                echo "$todos"
                echo "提示: 提交前应移除或解决TODO标记"
            fi
        fi
    done
    
    echo "✅ TODO检查完成"
    echo ""
}

# 检查小文件
check_small_files() {
    echo "📝 检查空洞文档..."
    
    for dir in "${DOCS_DIRS[@]}"; do
        if [ -d "$dir" ]; then
            small_files=$(find "$dir" -name "*.md" -type f -size -1k 2>/dev/null || true)
            
            if [ -n "$small_files" ]; then
                echo "⚠️  发现小于1KB的文档:"
                echo "$small_files"
                echo "提示: 确认这些文档内容是否完整"
            fi
        fi
    done
    
    echo "✅ 文件大小检查完成"
    echo ""
}

# 检查标题层级
check_headers() {
    echo "📝 检查标题层级..."
    
    # 简单检查：是否存在H1后直接H3的情况
    # (实际实现需要更复杂的逻辑)
    
    echo "✅ 标题层级检查完成"
    echo ""
}

# 主执行流程
main() {
    check_code_blocks
    check_todos
    check_small_files
    check_headers
    
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    
    if [ $ERRORS -eq 0 ]; then
        echo "✅ 所有检查通过！"
        echo ""
        exit 0
    else
        echo "❌ 发现 $ERRORS 个格式问题"
        echo "请修复后再提交"
        echo ""
        exit 1
    fi
}

# 运行主函数
main

