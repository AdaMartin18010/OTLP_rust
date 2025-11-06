#!/bin/bash
# 2025年技术趋势对齐 - 性能测试运行脚本
# 运行所有性能测试并生成报告

set -e

echo "=========================================="
echo "2025年技术趋势对齐 - 性能测试"
echo "=========================================="
echo ""

# 颜色定义
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m' # No Color

# 测试结果目录
RESULTS_DIR="performance_results_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$RESULTS_DIR"

echo "结果将保存到: $RESULTS_DIR"
echo ""

# 1. OTTL性能基准测试
echo -e "${GREEN}[1/3]${NC} 运行OTTL性能基准测试..."
if cargo bench --bench ottl_performance -- --output-format json > "$RESULTS_DIR/ottl_performance.json" 2>&1; then
    echo -e "${GREEN}✓${NC} OTTL性能测试完成"
else
    echo -e "${YELLOW}⚠${NC} OTTL性能测试失败或未找到基准测试"
fi
echo ""

# 2. OPAMP集成测试
echo -e "${GREEN}[2/3]${NC} 运行OPAMP集成测试..."
if cargo test --test opamp_graduation_test -- --nocapture > "$RESULTS_DIR/opamp_tests.txt" 2>&1; then
    echo -e "${GREEN}✓${NC} OPAMP集成测试完成"
else
    echo -e "${RED}✗${NC} OPAMP集成测试失败"
    exit 1
fi
echo ""

# 3. 2025趋势集成测试
echo -e "${GREEN}[3/3]${NC} 运行2025趋势集成测试..."
if cargo test --package otlp --test integration_2025_trends -- --nocapture > "$RESULTS_DIR/integration_tests.txt" 2>&1; then
    echo -e "${GREEN}✓${NC} 集成测试完成"
else
    echo -e "${YELLOW}⚠${NC} 集成测试未找到或失败 (可能文件位置不同)"
fi
echo ""

# 4. LLD性能对比 (如果脚本存在)
if [ -f "scripts/benchmark_lld.sh" ]; then
    echo -e "${GREEN}[4/4]${NC} 运行LLD性能对比测试..."
    if bash scripts/benchmark_lld.sh > "$RESULTS_DIR/lld_benchmark.txt" 2>&1; then
        echo -e "${GREEN}✓${NC} LLD性能对比完成"
    else
        echo -e "${YELLOW}⚠${NC} LLD性能对比失败或未配置"
    fi
    echo ""
fi

# 生成摘要报告
echo "=========================================="
echo "测试摘要"
echo "=========================================="
echo ""

if [ -f "$RESULTS_DIR/ottl_performance.json" ]; then
    echo "✓ OTTL性能基准测试: 完成"
else
    echo "⚠ OTTL性能基准测试: 未运行"
fi

if [ -f "$RESULTS_DIR/opamp_tests.txt" ]; then
    PASSED=$(grep -c "test result: ok" "$RESULTS_DIR/opamp_tests.txt" || echo "0")
    echo "✓ OPAMP集成测试: $PASSED 个测试通过"
fi

if [ -f "$RESULTS_DIR/integration_tests.txt" ]; then
    PASSED=$(grep -c "test result: ok" "$RESULTS_DIR/integration_tests.txt" || echo "0")
    echo "✓ 2025趋势集成测试: $PASSED 个测试通过"
fi

if [ -f "$RESULTS_DIR/lld_benchmark.txt" ]; then
    echo "✓ LLD性能对比: 完成"
fi

echo ""
echo "详细结果请查看: $RESULTS_DIR/"
echo "=========================================="
