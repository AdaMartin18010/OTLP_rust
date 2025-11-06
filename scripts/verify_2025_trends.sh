#!/bin/bash
# 2025年技术趋势对齐 - 功能验证脚本
# 验证所有2025年新增功能是否正常工作

set -e

echo "=========================================="
echo "2025年技术趋势对齐 - 功能验证"
echo "=========================================="
echo ""

# 颜色定义
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# 验证结果
PASSED=0
FAILED=0
SKIPPED=0

# 验证函数
verify_test() {
    local name=$1
    local command=$2

    echo -e "${BLUE}验证: ${name}${NC}"
    if eval "$command" > /dev/null 2>&1; then
        echo -e "${GREEN}✓ ${name} 通过${NC}"
        ((PASSED++))
        return 0
    else
        echo -e "${RED}✗ ${name} 失败${NC}"
        ((FAILED++))
        return 1
    fi
}

# 1. 编译检查
echo -e "${BLUE}[1/6]${NC} 编译检查..."
if cargo check --workspace > /dev/null 2>&1; then
    echo -e "${GREEN}✓ 编译检查通过${NC}"
    ((PASSED++))
else
    echo -e "${RED}✗ 编译检查失败${NC}"
    ((FAILED++))
    exit 1
fi
echo ""

# 2. OTTL字节码测试
echo -e "${BLUE}[2/6]${NC} OTTL字节码功能..."
verify_test "OTTL字节码解析器" "cargo test --package otlp --test integration_2025_trends test_ottl_bytecode_integration --lib"
verify_test "OTTL Transform字节码" "cargo test --package otlp --test integration_2025_trends test_ottl_transform_with_bytecode --lib"
echo ""

# 3. OPAMP灰度策略测试
echo -e "${BLUE}[3/6]${NC} OPAMP灰度策略功能..."
verify_test "OPAMP灰度策略" "cargo test --package otlp --test integration_2025_trends test_opamp_graduation_integration --lib"
verify_test "回滚管理器" "cargo test --package otlp --test integration_2025_trends test_rollback_manager_integration --lib"
verify_test "OPAMP消息集成" "cargo test --package otlp --test integration_2025_trends test_opamp_messages_with_graduation --lib"
echo ""

# 4. Const API测试
echo -e "${BLUE}[4/6]${NC} Const API功能..."
verify_test "Const API" "cargo test --package otlp --test integration_2025_trends test_const_api_integration --lib"
echo ""

# 5. eBPF Profiling测试
echo -e "${BLUE}[5/6]${NC} eBPF Profiling功能..."
if [[ "$OSTYPE" == "linux-gnu"* ]]; then
    verify_test "eBPF配置" "cargo test --package otlp --test integration_2025_trends test_ebpf_profiling_config --lib"
else
    echo -e "${YELLOW}⚠ eBPF测试跳过 (仅Linux平台)${NC}"
    ((SKIPPED++))
fi
echo ""

# 6. 端到端测试
echo -e "${BLUE}[6/6]${NC} 端到端集成测试..."
verify_test "端到端工作流" "cargo test --package otlp --test integration_2025_trends test_end_to_end_workflow --lib"
echo ""

# 总结
echo "=========================================="
echo "验证总结"
echo "=========================================="
echo -e "${GREEN}通过: ${PASSED}${NC}"
echo -e "${RED}失败: ${FAILED}${NC}"
if [ $SKIPPED -gt 0 ]; then
    echo -e "${YELLOW}跳过: ${SKIPPED}${NC}"
fi
echo ""

if [ $FAILED -eq 0 ]; then
    echo -e "${GREEN}✅ 所有验证通过！${NC}"
    exit 0
else
    echo -e "${RED}❌ 部分验证失败，请检查上述错误${NC}"
    exit 1
fi
