#!/bin/bash
# 测试覆盖率设置脚本
# 用途: 安装工具并生成测试覆盖率报告
# 使用: ./scripts/setup_coverage.sh

set -e

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "📊 测试覆盖率设置和报告生成"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# 检查是否在项目根目录
if [ ! -f "Cargo.toml" ]; then
    echo -e "${RED}❌ 错误: 请在项目根目录运行此脚本${NC}"
    exit 1
fi

echo -e "${BLUE}📋 步骤1: 检查并安装工具${NC}"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# 检查cargo-tarpaulin
if command -v cargo-tarpaulin &> /dev/null; then
    echo -e "${GREEN}✅ cargo-tarpaulin 已安装${NC}"
    TARPAULIN_VERSION=$(cargo tarpaulin --version | head -1)
    echo "   版本: $TARPAULIN_VERSION"
else
    echo -e "${YELLOW}⚙️  安装 cargo-tarpaulin...${NC}"
    cargo install cargo-tarpaulin
    echo -e "${GREEN}✅ cargo-tarpaulin 安装完成${NC}"
fi

echo ""

# 检查cargo-nextest (可选，但推荐)
if command -v cargo-nextest &> /dev/null; then
    echo -e "${GREEN}✅ cargo-nextest 已安装${NC}"
else
    echo -e "${YELLOW}💡 建议安装 cargo-nextest 以加速测试${NC}"
    echo "   安装命令: cargo install cargo-nextest"
fi

echo ""
echo -e "${BLUE}📋 步骤2: 创建覆盖率输出目录${NC}"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

mkdir -p coverage
echo -e "${GREEN}✅ 创建目录: coverage/${NC}"

echo ""
echo -e "${BLUE}📋 步骤3: 运行测试覆盖率分析${NC}"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
echo "这可能需要几分钟时间..."
echo ""

# 运行tarpaulin
START_TIME=$(date +%s)

if cargo tarpaulin --workspace \
    --out Html \
    --out Lcov \
    --out Json \
    --output-dir coverage/ \
    --exclude-files "*/tests/*" "*/benches/*" "*/examples/*" \
    --timeout 300 \
    --verbose \
    2>&1 | tee coverage/tarpaulin.log; then
    
    END_TIME=$(date +%s)
    DURATION=$((END_TIME - START_TIME))
    
    echo ""
    echo -e "${GREEN}✅ 覆盖率分析完成 (耗时: ${DURATION}秒)${NC}"
else
    echo ""
    echo -e "${RED}❌ 覆盖率分析失败${NC}"
    echo "查看日志: coverage/tarpaulin.log"
    exit 1
fi

echo ""
echo -e "${BLUE}📋 步骤4: 生成覆盖率报告${NC}"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# 从JSON提取覆盖率数据
if [ -f "coverage/tarpaulin-report.json" ]; then
    echo "解析覆盖率数据..."
    
    # 提取总覆盖率
    TOTAL_COVERAGE=$(grep -oP '"coverage":\s*\K[0-9.]+' coverage/tarpaulin-report.json | head -1)
    
    if [ -n "$TOTAL_COVERAGE" ]; then
        echo ""
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        echo -e "${BLUE}📊 覆盖率结果${NC}"
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        echo ""
        
        # 计算覆盖率百分比
        COVERAGE_PERCENT=$(echo "$TOTAL_COVERAGE * 100" | bc | cut -d. -f1)
        
        if [ $COVERAGE_PERCENT -ge 80 ]; then
            echo -e "${GREEN}✨ 总体覆盖率: ${COVERAGE_PERCENT}% (优秀)${NC}"
        elif [ $COVERAGE_PERCENT -ge 70 ]; then
            echo -e "${GREEN}✅ 总体覆盖率: ${COVERAGE_PERCENT}% (良好)${NC}"
        elif [ $COVERAGE_PERCENT -ge 60 ]; then
            echo -e "${YELLOW}⚠️  总体覆盖率: ${COVERAGE_PERCENT}% (及格)${NC}"
        else
            echo -e "${RED}❌ 总体覆盖率: ${COVERAGE_PERCENT}% (需要改进)${NC}"
        fi
    fi
fi

echo ""
echo "生成的文件:"
echo "  - coverage/index.html         (HTML报告)"
echo "  - coverage/cobertura.xml      (Lcov格式)"
echo "  - coverage/tarpaulin-report.json (JSON数据)"
echo "  - coverage/tarpaulin.log      (详细日志)"

echo ""
echo -e "${BLUE}📋 步骤5: 创建覆盖率基准文档${NC}"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# 创建基准报告
REPORT_FILE="coverage/COVERAGE_BASELINE_$(date +%Y_%m_%d).md"

cat > "$REPORT_FILE" << EOF
# 测试覆盖率基准报告

**生成日期**: $(date '+%Y年%m月%d日 %H:%M:%S')  
**工具版本**: $(cargo tarpaulin --version | head -1)  
**项目版本**: v0.5.0-rc1

---

## 📊 整体覆盖率

EOF

if [ -n "$TOTAL_COVERAGE" ]; then
    cat >> "$REPORT_FILE" << EOF
- **总体覆盖率**: ${COVERAGE_PERCENT}%
- **目标覆盖率**: 70% (短期), 80% (长期)

### 评级

EOF

    if [ $COVERAGE_PERCENT -ge 80 ]; then
        echo "✅ **优秀** - 覆盖率达标，继续保持！" >> "$REPORT_FILE"
    elif [ $COVERAGE_PERCENT -ge 70 ]; then
        echo "✅ **良好** - 覆盖率良好，可以进一步提升。" >> "$REPORT_FILE"
    elif [ $COVERAGE_PERCENT -ge 60 ]; then
        echo "⚠️ **及格** - 覆盖率及格，建议增加测试。" >> "$REPORT_FILE"
    else
        echo "❌ **需要改进** - 覆盖率偏低，需要优先提升。" >> "$REPORT_FILE"
    fi
fi

cat >> "$REPORT_FILE" << EOF

---

## 📁 各Crate覆盖率

查看详细报告: [coverage/index.html](index.html)

---

## 🎯 改进目标

### 短期目标 (1个月)
- [ ] 核心模块覆盖率 >70%
- [ ] 整体覆盖率 >60%
- [ ] 所有公开API有基本测试

### 中期目标 (3个月)
- [ ] 核心模块覆盖率 >80%
- [ ] 整体覆盖率 >70%
- [ ] 关键路径100%覆盖

### 长期目标 (6个月)
- [ ] 核心模块覆盖率 >90%
- [ ] 整体覆盖率 >80%
- [ ] CI集成覆盖率检查

---

## 🔧 测试命令

\`\`\`bash
# 运行所有测试
cargo test --workspace

# 生成覆盖率报告
cargo tarpaulin --workspace --out Html

# 查看HTML报告
open coverage/index.html  # macOS
xdg-open coverage/index.html  # Linux
start coverage/index.html  # Windows
\`\`\`

---

## 📚 参考文档

- [完整评估报告](../CRITICAL_EVALUATION_REPORT_2025_10_29.md)
- [改进行动计划](../IMPROVEMENT_ACTION_PLAN_2025_10_29.md)
- [cargo-tarpaulin文档](https://github.com/xd009642/tarpaulin)

---

*报告由 setup_coverage.sh 自动生成*
EOF

echo -e "${GREEN}✅ 基准报告已创建: $REPORT_FILE${NC}"

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo -e "${GREEN}✨ 覆盖率设置完成!${NC}"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
echo "📊 查看覆盖率报告:"
echo ""
echo "   浏览器打开: coverage/index.html"
echo "   文本报告: $REPORT_FILE"
echo ""
echo "📝 下一步建议:"
echo ""
echo "   1. 查看覆盖率报告，识别低覆盖率模块"
echo "   2. 为低覆盖率模块添加测试"
echo "   3. 定期运行此脚本监控覆盖率变化"
echo "   4. 将覆盖率报告添加到.gitignore (如果还没有)"
echo ""
echo "   echo 'coverage/' >> .gitignore"
echo ""

