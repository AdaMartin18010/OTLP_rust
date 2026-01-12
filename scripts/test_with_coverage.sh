#!/bin/bash
# 测试覆盖率脚本
# 用于运行测试并生成覆盖率报告

set -e

echo "=========================================="
echo "  🧪 运行测试并生成覆盖率报告"
echo "=========================================="
echo ""

# 颜色定义
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m' # No Color

# 检查是否安装了 cargo-llvm-cov
if ! command -v cargo-llvm-cov &> /dev/null; then
    echo -e "${YELLOW}⚠️  cargo-llvm-cov 未安装${NC}"
    echo "安装命令: cargo install cargo-llvm-cov"
    echo ""
    echo "使用 cargo test 代替..."
    cargo test --workspace --all-features
    exit 0
fi

# 运行测试
echo -e "${GREEN}📋 运行测试...${NC}"
cargo test --workspace --all-features

# 生成覆盖率报告
echo ""
echo -e "${GREEN}📊 生成覆盖率报告...${NC}"
cargo llvm-cov --workspace --all-features --lcov --output-path lcov.info

# 生成 HTML 报告
echo -e "${GREEN}📄 生成 HTML 报告...${NC}"
cargo llvm-cov --workspace --all-features --html --output-dir coverage/

# 显示覆盖率摘要
echo ""
echo -e "${GREEN}✅ 覆盖率报告生成完成！${NC}"
echo ""
echo "📁 报告位置:"
echo "  - LCOV 格式: lcov.info"
echo "  - HTML 格式: coverage/index.html"
echo ""
echo "💡 查看 HTML 报告:"
echo "  open coverage/index.html  # macOS"
echo "  xdg-open coverage/index.html  # Linux"
echo "  start coverage/index.html  # Windows"
