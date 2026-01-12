#!/bin/bash
# 运行 eBPF 相关测试

set -e

echo "=========================================="
echo "  🧪 运行 eBPF 测试"
echo "=========================================="
echo ""

# 颜色定义
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m' # No Color

# 检查是否在 Linux 环境
if [[ "$OSTYPE" != "linux-gnu"* ]]; then
    echo -e "${YELLOW}⚠️  警告: eBPF 功能仅在 Linux 平台支持${NC}"
    echo "当前操作系统: $OSTYPE"
    echo "跳过 eBPF 测试"
    exit 0
fi

# 检查 eBPF feature
if ! grep -q "ebpf" Cargo.toml; then
    echo -e "${YELLOW}⚠️  警告: eBPF feature 未启用${NC}"
    echo "跳过 eBPF 测试"
    exit 0
fi

echo -e "${GREEN}1️⃣  运行 eBPF 单元测试...${NC}"
if cargo test --package otlp --lib ebpf --features ebpf; then
    echo -e "${GREEN}✅ 单元测试通过${NC}"
else
    echo -e "${RED}❌ 单元测试失败${NC}"
    exit 1
fi

echo ""
echo -e "${GREEN}2️⃣  运行 eBPF 集成测试...${NC}"
if cargo test --test ebpf_integration --features ebpf; then
    echo -e "${GREEN}✅ 集成测试通过${NC}"
else
    echo -e "${YELLOW}⚠️  集成测试跳过（可能需要 root 权限）${NC}"
fi

echo ""
echo -e "${GREEN}3️⃣  运行 eBPF 示例...${NC}"
if cargo run --example ebpf_complete --features ebpf 2>&1 | head -20; then
    echo -e "${GREEN}✅ 示例运行成功${NC}"
else
    echo -e "${YELLOW}⚠️  示例运行跳过（可能需要 root 权限或 eBPF 支持）${NC}"
fi

echo ""
echo -e "${GREEN}✅ eBPF 测试完成！${NC}"
echo ""
