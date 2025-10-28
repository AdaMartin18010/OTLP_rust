#!/bin/bash
# 项目健康度检查脚本
# 用途: 快速检查项目的整体健康状况
# 使用: ./scripts/check_project_health.sh

set -e

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "🏥 OTLP_rust 项目健康度检查"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# 计数器
PASS=0
WARN=0
FAIL=0

# 检查函数
check_pass() {
    echo -e "${GREEN}✅ PASS${NC} - $1"
    ((PASS++))
}

check_warn() {
    echo -e "${YELLOW}⚠️  WARN${NC} - $1"
    ((WARN++))
}

check_fail() {
    echo -e "${RED}❌ FAIL${NC} - $1"
    ((FAIL++))
}

echo "📦 1. Rust工具链检查"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# 检查Rust版本
if command -v rustc &> /dev/null; then
    RUST_VERSION=$(rustc --version | awk '{print $2}')
    if [[ "$RUST_VERSION" == "1.90.0" ]]; then
        check_pass "Rust版本: $RUST_VERSION (目标版本)"
    else
        check_warn "Rust版本: $RUST_VERSION (建议使用1.90.0)"
    fi
else
    check_fail "Rust未安装"
fi

# 检查Cargo版本
if command -v cargo &> /dev/null; then
    CARGO_VERSION=$(cargo --version | awk '{print $2}')
    check_pass "Cargo版本: $CARGO_VERSION"
else
    check_fail "Cargo未安装"
fi

echo ""
echo "🔍 2. 项目结构检查"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# 检查Cargo.toml
if [ -f "Cargo.toml" ]; then
    check_pass "Cargo.toml存在"
else
    check_fail "Cargo.toml不存在"
fi

# 检查crates目录
if [ -d "crates" ]; then
    CRATE_COUNT=$(find crates -maxdepth 1 -type d | wc -l)
    check_pass "crates目录存在 ($((CRATE_COUNT-1))个crate)"
else
    check_fail "crates目录不存在"
fi

# 检查源文件数量
if [ -d "crates" ]; then
    RS_COUNT=$(find crates -name "*.rs" -not -path "*/target/*" | wc -l)
    if [ $RS_COUNT -gt 300 ]; then
        check_pass "Rust源文件: $RS_COUNT个"
    else
        check_warn "Rust源文件: $RS_COUNT个 (偏少)"
    fi
fi

echo ""
echo "🧪 3. 测试相关检查"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# 检查测试文件
TEST_COUNT=$(find crates -name "*test*.rs" -o -path "*/tests/*" | wc -l)
if [ $TEST_COUNT -gt 30 ]; then
    check_pass "测试文件: $TEST_COUNT个"
else
    check_warn "测试文件: $TEST_COUNT个 (建议>30)"
fi

# 检查是否有覆盖率报告
if [ -d "coverage" ]; then
    if [ -f "coverage/index.html" ]; then
        check_pass "覆盖率报告存在"
    else
        check_warn "覆盖率目录存在但报告缺失"
    fi
else
    check_warn "未生成覆盖率报告"
fi

echo ""
echo "📚 4. 文档检查"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# 检查README
if [ -f "README.md" ]; then
    check_pass "README.md存在"
else
    check_fail "README.md不存在"
fi

# 检查docs目录
if [ -d "docs" ]; then
    DOC_COUNT=$(find docs -name "*.md" | wc -l)
    check_pass "docs目录存在 ($DOC_COUNT个文档)"
else
    check_warn "docs目录不存在"
fi

# 检查analysis目录
if [ -d "analysis" ]; then
    ANALYSIS_COUNT=$(find analysis -name "*.md" | wc -l)
    check_pass "analysis目录存在 ($ANALYSIS_COUNT个分析文档)"
else
    check_warn "analysis目录不存在"
fi

echo ""
echo "🔧 5. CI/CD检查"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# 检查GitHub Actions
if [ -d ".github/workflows" ]; then
    WORKFLOW_COUNT=$(find .github/workflows -name "*.yml" -o -name "*.yaml" | wc -l)
    if [ $WORKFLOW_COUNT -gt 0 ]; then
        check_pass "GitHub Actions配置: $WORKFLOW_COUNT个workflow"
    else
        check_warn "GitHub Actions目录存在但无workflow"
    fi
else
    check_warn "未配置GitHub Actions (建议配置)"
fi

echo ""
echo "🔐 6. 安全检查"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# 检查是否安装cargo-audit
if command -v cargo-audit &> /dev/null; then
    check_pass "cargo-audit已安装"
    echo "   运行安全审计..."
    if cargo audit --quiet 2>/dev/null; then
        check_pass "无已知安全漏洞"
    else
        check_warn "存在安全警告，请运行: cargo audit"
    fi
else
    check_warn "cargo-audit未安装 (建议安装: cargo install cargo-audit)"
fi

echo ""
echo "📊 7. 依赖检查"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# 检查OpenTelemetry版本
echo "   检查OpenTelemetry版本..."
OTEL_VERSIONS=$(cargo tree --workspace 2>/dev/null | grep "opentelemetry v" | sort -u | wc -l)
if [ $OTEL_VERSIONS -eq 1 ]; then
    check_pass "OpenTelemetry版本统一"
elif [ $OTEL_VERSIONS -gt 1 ]; then
    check_fail "OpenTelemetry存在版本冲突 (检测到${OTEL_VERSIONS}个版本)"
    echo "   详细信息: cargo tree -i opentelemetry"
else
    check_warn "无法检测OpenTelemetry版本"
fi

# 检查Cargo.lock
if [ -f "Cargo.lock" ]; then
    check_pass "Cargo.lock存在"
else
    check_warn "Cargo.lock不存在 (建议提交到版本控制)"
fi

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "📈 健康度总结"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

TOTAL=$((PASS + WARN + FAIL))
if [ $TOTAL -gt 0 ]; then
    PASS_PERCENT=$((PASS * 100 / TOTAL))
    echo -e "通过: ${GREEN}$PASS${NC} | 警告: ${YELLOW}$WARN${NC} | 失败: ${RED}$FAIL${NC}"
    echo ""
    
    if [ $PASS_PERCENT -ge 80 ]; then
        echo -e "${GREEN}✨ 健康度: 优秀 (${PASS_PERCENT}%)${NC}"
        echo "   项目状态良好，继续保持！"
    elif [ $PASS_PERCENT -ge 60 ]; then
        echo -e "${YELLOW}⚠️  健康度: 良好 (${PASS_PERCENT}%)${NC}"
        echo "   建议解决警告项以提升健康度。"
    else
        echo -e "${RED}❌ 健康度: 需要改进 (${PASS_PERCENT}%)${NC}"
        echo "   请优先解决失败项。"
    fi
fi

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "💡 建议的下一步行动"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

if [ $FAIL -gt 0 ]; then
    echo "1. 🔴 优先解决失败项"
fi

if [ $WARN -gt 0 ]; then
    echo "2. 🟡 解决警告项:"
    if [ ! -d "coverage" ]; then
        echo "   - 生成测试覆盖率报告: cargo install cargo-tarpaulin && cargo tarpaulin --workspace --out Html"
    fi
    if [ ! -d ".github/workflows" ]; then
        echo "   - 配置CI/CD: 参考 analysis/IMPROVEMENT_ACTION_PLAN_2025_10_29.md"
    fi
    if ! command -v cargo-audit &> /dev/null; then
        echo "   - 安装安全审计工具: cargo install cargo-audit"
    fi
fi

echo ""
echo "3. ✅ 查看详细改进计划:"
echo "   - 执行摘要: analysis/EXECUTIVE_SUMMARY_2025_10_29.md"
echo "   - 完整评估: analysis/CRITICAL_EVALUATION_REPORT_2025_10_29.md"
echo "   - 行动计划: analysis/IMPROVEMENT_ACTION_PLAN_2025_10_29.md"

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "检查完成! $(date '+%Y-%m-%d %H:%M:%S')"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

