#!/bin/bash
# OpenTelemetry版本冲突修复脚本
# 用途: 自动检测并修复OpenTelemetry版本冲突
# 使用: ./scripts/fix_opentelemetry_conflict.sh

set -e

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "🔧 OpenTelemetry 版本冲突修复工具"
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

echo -e "${BLUE}📋 步骤1: 检测当前OpenTelemetry版本${NC}"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# 创建临时文件
TEMP_FILE=$(mktemp)
trap "rm -f $TEMP_FILE" EXIT

# 检测OpenTelemetry版本
echo "运行: cargo tree -i opentelemetry"
cargo tree -i opentelemetry 2>/dev/null | grep "opentelemetry v" | sort -u > $TEMP_FILE

if [ ! -s "$TEMP_FILE" ]; then
    echo -e "${GREEN}✅ 未检测到OpenTelemetry依赖或无法分析${NC}"
    exit 0
fi

echo "检测到的OpenTelemetry版本:"
cat $TEMP_FILE

VERSION_COUNT=$(wc -l < $TEMP_FILE)

if [ $VERSION_COUNT -eq 1 ]; then
    echo ""
    echo -e "${GREEN}✅ OpenTelemetry版本统一，无需修复${NC}"
    VERSION=$(grep -oP 'v\K[0-9]+\.[0-9]+\.[0-9]+' $TEMP_FILE | head -1)
    echo "   当前版本: $VERSION"
    exit 0
fi

echo ""
echo -e "${RED}⚠️  检测到版本冲突: 存在 $VERSION_COUNT 个不同版本${NC}"
echo ""

# 提取版本号
VERSIONS=$(grep -oP 'v\K[0-9]+\.[0-9]+\.[0-9]+' $TEMP_FILE | sort -V | uniq)
echo "版本列表:"
echo "$VERSIONS" | while read v; do echo "  - $v"; done
echo ""

# 确定目标版本 (使用最新版本)
TARGET_VERSION=$(echo "$VERSIONS" | tail -1)
echo -e "${BLUE}🎯 目标统一版本: $TARGET_VERSION${NC}"
echo ""

# 询问用户确认
echo -e "${YELLOW}是否要将所有OpenTelemetry依赖统一到 v$TARGET_VERSION? (y/N)${NC}"
read -r CONFIRM

if [[ ! $CONFIRM =~ ^[Yy]$ ]]; then
    echo "操作已取消"
    exit 0
fi

echo ""
echo -e "${BLUE}📋 步骤2: 备份Cargo.toml${NC}"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

BACKUP_FILE="Cargo.toml.backup.$(date +%Y%m%d_%H%M%S)"
cp Cargo.toml "$BACKUP_FILE"
echo -e "${GREEN}✅ 备份已创建: $BACKUP_FILE${NC}"
echo ""

echo -e "${BLUE}📋 步骤3: 添加版本patch${NC}"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# 检查是否已存在patch.crates-io节
if grep -q "^\[patch\.crates-io\]" Cargo.toml; then
    echo "检测到现有的 [patch.crates-io] 节"
    
    # 更新现有的patch
    if grep -q "^opentelemetry = " Cargo.toml; then
        echo "更新现有的opentelemetry patch..."
        sed -i.tmp "s/^opentelemetry = .*/opentelemetry = { version = \"$TARGET_VERSION\" }/" Cargo.toml
    else
        echo "在现有的 [patch.crates-io] 节中添加opentelemetry..."
        sed -i.tmp "/^\[patch\.crates-io\]/a opentelemetry = { version = \"$TARGET_VERSION\" }" Cargo.toml
    fi
    
    # 添加其他OpenTelemetry相关的patch
    for pkg in opentelemetry_sdk opentelemetry-otlp opentelemetry-http opentelemetry-proto opentelemetry-stdout tracing-opentelemetry; do
        if ! grep -q "^$pkg = " Cargo.toml; then
            sed -i.tmp "/^opentelemetry = /a $pkg = { version = \"$TARGET_VERSION\" }" Cargo.toml 2>/dev/null || true
        fi
    done
    
    rm -f Cargo.toml.tmp
else
    echo "创建新的 [patch.crates-io] 节..."
    
    cat >> Cargo.toml << EOF

# ========== 版本冲突修复 ==========
# 自动添加于: $(date '+%Y-%m-%d %H:%M:%S')
# 统一OpenTelemetry版本到: $TARGET_VERSION
[patch.crates-io]
opentelemetry = { version = "$TARGET_VERSION" }
opentelemetry_sdk = { version = "$TARGET_VERSION" }
opentelemetry-otlp = { version = "$TARGET_VERSION" }
opentelemetry-http = { version = "$TARGET_VERSION" }
opentelemetry-proto = { version = "$TARGET_VERSION" }
opentelemetry-stdout = { version = "$TARGET_VERSION" }
tracing-opentelemetry = { version = "0.31" }
EOF
fi

echo -e "${GREEN}✅ Cargo.toml已更新${NC}"
echo ""

echo -e "${BLUE}📋 步骤4: 更新依赖${NC}"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

echo "运行: cargo update -p opentelemetry"
if cargo update -p opentelemetry 2>&1; then
    echo -e "${GREEN}✅ 依赖更新成功${NC}"
else
    echo -e "${YELLOW}⚠️  依赖更新遇到警告，但可能已部分成功${NC}"
fi
echo ""

echo -e "${BLUE}📋 步骤5: 验证修复${NC}"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

echo "运行: cargo check --workspace"
if cargo check --workspace 2>&1 | tee /tmp/cargo_check.log; then
    echo ""
    echo -e "${GREEN}✅ 编译检查通过${NC}"
else
    echo ""
    echo -e "${RED}❌ 编译检查失败${NC}"
    echo ""
    echo "可能需要手动解决一些兼容性问题。"
    echo "查看错误日志: /tmp/cargo_check.log"
    echo ""
    echo "如需回滚，运行:"
    echo "  mv $BACKUP_FILE Cargo.toml"
    echo "  cargo update"
    exit 1
fi

echo ""
echo "再次检查OpenTelemetry版本:"
cargo tree -i opentelemetry 2>/dev/null | grep "opentelemetry v" | sort -u

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo -e "${GREEN}✨ 修复完成!${NC}"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
echo "✅ 已完成的操作:"
echo "   1. 备份原始Cargo.toml -> $BACKUP_FILE"
echo "   2. 添加版本patch到Cargo.toml"
echo "   3. 更新依赖"
echo "   4. 验证编译"
echo ""
echo "📝 下一步建议:"
echo "   1. 运行测试: cargo test --workspace"
echo "   2. 提交更改: git add Cargo.toml Cargo.lock && git commit -m 'fix: resolve OpenTelemetry version conflict'"
echo "   3. 删除备份 (如果确认无误): rm $BACKUP_FILE"
echo ""

