#!/bin/bash
# LLD链接器性能对比测试脚本
# 用于验证LLD链接器的优化效果

set -e

echo "=== LLD链接器性能对比测试 ==="
echo ""

# 检查是否安装了LLD
if ! command -v lld &> /dev/null; then
    echo "警告: LLD未安装，跳过LLD测试"
    echo "安装方法:"
    echo "  Linux: sudo apt-get install lld"
    echo "  macOS: brew install llvm"
    exit 0
fi

# 清理之前的构建
echo "1. 清理之前的构建..."
cargo clean > /dev/null 2>&1 || true

# 使用默认链接器
echo "2. 使用默认链接器编译..."
unset RUSTFLAGS
START_TIME=$(date +%s.%N)
cargo build --release --no-default-features 2>&1 | grep -E "(Compiling|Finished)" || true
END_TIME=$(date +%s.%N)
DEFAULT_TIME=$(echo "$END_TIME - $START_TIME" | bc)

# 获取二进制大小
DEFAULT_SIZE=$(stat -f%z target/release/otlp 2>/dev/null || stat -c%s target/release/otlp 2>/dev/null || echo "0")

echo "3. 使用LLD链接器编译..."
export RUSTFLAGS="-C link-arg=-fuse-ld=lld"
cargo clean > /dev/null 2>&1 || true
START_TIME=$(date +%s.%N)
cargo build --release --no-default-features 2>&1 | grep -E "(Compiling|Finished)" || true
END_TIME=$(date +%s.%N)
LLD_TIME=$(echo "$END_TIME - $START_TIME" | bc)

# 获取二进制大小
LLD_SIZE=$(stat -f%z target/release/otlp 2>/dev/null || stat -c%s target/release/otlp 2>/dev/null || echo "0")

# 计算提升百分比
if [ "$DEFAULT_TIME" != "0" ] && [ "$LLD_TIME" != "0" ]; then
    TIME_IMPROVEMENT=$(echo "scale=2; (($DEFAULT_TIME - $LLD_TIME) / $DEFAULT_TIME) * 100" | bc)
else
    TIME_IMPROVEMENT="N/A"
fi

if [ "$DEFAULT_SIZE" != "0" ] && [ "$LLD_SIZE" != "0" ]; then
    SIZE_REDUCTION=$(echo "scale=2; (($DEFAULT_SIZE - $LLD_SIZE) / $DEFAULT_SIZE) * 100" | bc)
else
    SIZE_REDUCTION="N/A"
fi

echo ""
echo "=== 测试结果 ==="
echo "默认链接器编译时间: ${DEFAULT_TIME}s"
echo "LLD链接器编译时间: ${LLD_TIME}s"
echo "编译时间提升: ${TIME_IMPROVEMENT}%"
echo ""
echo "默认链接器二进制大小: ${DEFAULT_SIZE} bytes"
echo "LLD链接器二进制大小: ${LLD_SIZE} bytes"
echo "二进制体积减少: ${SIZE_REDUCTION}%"
echo ""

# 验证目标
if [ "$TIME_IMPROVEMENT" != "N/A" ]; then
    if (( $(echo "$TIME_IMPROVEMENT > 20" | bc -l) )); then
        echo "✅ 编译时间提升达到目标 (>=20%)"
    else
        echo "⚠️  编译时间提升未达目标 (<20%)"
    fi
fi

if [ "$SIZE_REDUCTION" != "N/A" ]; then
    if (( $(echo "$SIZE_REDUCTION > 10" | bc -l) )); then
        echo "✅ 二进制体积减少达到目标 (>=10%)"
    else
        echo "⚠️  二进制体积减少未达目标 (<10%)"
    fi
fi
