#!/bin/bash
# 完整构建脚本
# 用于构建、测试和检查整个项目

set -e

echo "=========================================="
echo "  🏗️  完整构建和检查"
echo "=========================================="
echo ""

# 颜色定义
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m' # No Color

# 1. 格式化检查
echo -e "${GREEN}1️⃣  检查代码格式化...${NC}"
cargo fmt --all -- --check || {
    echo -e "${YELLOW}⚠️  代码格式化不一致，运行 cargo fmt --all 修复${NC}"
    exit 1
}

# 2. Clippy 检查
echo -e "${GREEN}2️⃣  运行 Clippy 检查...${NC}"
cargo clippy --workspace --all-targets --all-features -- -D warnings

# 3. 编译检查
echo -e "${GREEN}3️⃣  编译检查...${NC}"
cargo check --workspace --all-features

# 4. 运行测试
echo -e "${GREEN}4️⃣  运行测试...${NC}"
cargo test --workspace --all-features

# 5. 文档检查
echo -e "${GREEN}5️⃣  检查文档...${NC}"
cargo doc --workspace --all-features --no-deps

echo ""
echo -e "${GREEN}✅ 所有检查通过！${NC}"
