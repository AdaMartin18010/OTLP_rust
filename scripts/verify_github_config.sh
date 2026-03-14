#!/bin/bash
# GitHub 配置验证脚本
# 用于验证 GitHub 配置的完整性和正确性

set -e

echo "🔍 验证 GitHub 配置..."
echo ""

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

ERRORS=0
WARNINGS=0

# 检查文件存在性
check_file() {
    if [ -f "$1" ]; then
        echo -e "${GREEN}✓${NC} $2 存在"
        return 0
    else
        echo -e "${RED}✗${NC} $2 缺失"
        ((ERRORS++))
        return 1
    fi
}

# 检查目录存在性
check_dir() {
    if [ -d "$1" ]; then
        echo -e "${GREEN}✓${NC} $2 目录存在"
        return 0
    else
        echo -e "${RED}✗${NC} $2 目录缺失"
        ((ERRORS++))
        return 1
    fi
}

echo "📁 检查必要文件..."
echo "-------------------"
check_file ".github/CODEOWNERS" "CODEOWNERS"
check_file ".github/PULL_REQUEST_TEMPLATE.md" "PR 模板"
check_file ".github/ISSUE_TEMPLATE/bug_report.md" "Bug 报告模板"
check_file ".github/ISSUE_TEMPLATE/feature_request.md" "功能请求模板"
check_file "SECURITY.md" "安全策略"
check_file "CONTRIBUTING.md" "贡献指南"

echo ""
echo "📂 检查工作流..."
echo "-------------------"
check_dir ".github/workflows" "工作流目录"
check_file ".github/workflows/ci.yml" "CI 工作流"
check_file ".github/workflows/coverage.yml" "覆盖率工作流"
check_file ".github/workflows/security.yml" "安全工作流"

echo ""
echo "🔧 检查 Rust 版本配置..."
echo "-------------------"

# 检查所有 workflow 中的 Rust 版本
RUST_VERSIONS=$(grep -r "rust-toolchain@" .github/workflows/ | grep -v "README" | sort | uniq)
if echo "$RUST_VERSIONS" | grep -q "1.94"; then
    echo -e "${GREEN}✓${NC} 发现 Rust 1.94 配置"
else
    echo -e "${YELLOW}⚠${NC} 未找到 Rust 1.94 配置"
    ((WARNINGS++))
fi

echo ""
echo "当前配置的 Rust 版本:"
echo "$RUST_VERSIONS" | while read -r line; do
    echo "  $line"
done

echo ""
echo "📝 检查 Issue 模板..."
echo "-------------------"
if grep -q "Rust 1.94" ".github/ISSUE_TEMPLATE/bug_report.md" 2>/dev/null; then
    echo -e "${GREEN}✓${NC} Issue 模板已更新到 Rust 1.94"
else
    echo -e "${YELLOW}⚠${NC} Issue 模板可能需要更新 Rust 版本"
    ((WARNINGS++))
fi

echo ""
echo "🔐 检查安全策略..."
echo "-------------------"
if grep -q "1.94" "SECURITY.md" 2>/dev/null; then
    echo -e "${GREEN}✓${NC} 安全策略已更新到 Rust 1.94"
else
    echo -e "${YELLOW}⚠${NC} 安全策略可能需要更新 Rust 版本"
    ((WARNINGS++))
fi

echo ""
echo "📋 检查贡献指南..."
echo "-------------------"
if grep -q "1.94" "CONTRIBUTING.md" 2>/dev/null; then
    echo -e "${GREEN}✓${NC} 贡献指南已更新到 Rust 1.94"
else
    echo -e "${YELLOW}⚠${NC} 贡献指南可能需要更新 Rust 版本"
    ((WARNINGS++))
fi

echo ""
echo "==================="
echo "📊 验证结果"
echo "==================="

if [ $ERRORS -eq 0 ] && [ $WARNINGS -eq 0 ]; then
    echo -e "${GREEN}✅ 所有检查通过！${NC}"
    exit 0
elif [ $ERRORS -eq 0 ]; then
    echo -e "${YELLOW}⚠️  $WARNINGS 个警告${NC}"
    echo "建议查看警告内容并进行优化"
    exit 0
else
    echo -e "${RED}❌ $ERRORS 个错误, $WARNINGS 个警告${NC}"
    echo "请修复错误后重试"
    exit 1
fi
