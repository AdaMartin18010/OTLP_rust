#!/bin/bash
# 代码质量追踪脚本
# 用于持续监控项目质量指标

OUTPUT_FILE="${1:-code_quality_report.txt}"

echo "🔍 开始代码质量分析..."
echo ""

# 开始生成报告
cat > "$OUTPUT_FILE" <<EOF
# 代码质量追踪报告
生成时间: $(date "+%Y-%m-%d %H:%M:%S")

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 📊 基本统计

EOF

# 1. Rust文件统计
echo "📁 统计Rust文件..."
RUST_FILES=$(find crates/otlp/src -name "*.rs" -type f | wc -l)
echo "Rust文件数: $RUST_FILES 个" >> "$OUTPUT_FILE"
echo "   Rust文件: $RUST_FILES 个"

# 2. 测试函数统计
echo "🧪 统计测试函数..."
TEST_FNS=$(rg "fn test_" crates/otlp/src -c --type rust 2>/dev/null | awk -F: '{sum+=$2} END {print sum+0}')
echo "测试函数数: $TEST_FNS 个" >> "$OUTPUT_FILE"
echo "   测试函数: $TEST_FNS 个"

# 3. Async测试统计
echo "⚡ 统计异步测试..."
ASYNC_TESTS=$(rg "#\[tokio::test\]" crates/otlp/src -c 2>/dev/null | awk -F: '{sum+=$2} END {print sum+0}')
echo "异步测试数: $ASYNC_TESTS 个" >> "$OUTPUT_FILE"
echo "   异步测试: $ASYNC_TESTS 个"

# 4. Unsafe代码统计
echo "⚠️  统计Unsafe代码..."
UNSAFE_COUNT=$(rg "\bunsafe\b" crates/otlp/src --type rust -c 2>/dev/null | awk -F: '{sum+=$2} END {print sum+0}')
echo "Unsafe块数: $UNSAFE_COUNT 个" >> "$OUTPUT_FILE"
echo "   Unsafe块: $UNSAFE_COUNT 个"

cat >> "$OUTPUT_FILE" <<EOF

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 🎯 性能指标

EOF

# 5. Clone操作统计
echo "📋 统计Clone操作..."
CLONE_COUNT=$(rg "clone\(\)" crates/otlp/src --type rust -c 2>/dev/null | awk -F: '{sum+=$2} END {print sum+0}')
echo "Clone操作: $CLONE_COUNT 次" >> "$OUTPUT_FILE"
echo "   Clone操作: $CLONE_COUNT 次"

# 6. Arc使用统计
echo "🔗 统计Arc使用..."
ARC_COUNT=$(rg "Arc::new" crates/otlp/src --type rust -c 2>/dev/null | awk -F: '{sum+=$2} END {print sum+0}')
echo "Arc::new: $ARC_COUNT 次" >> "$OUTPUT_FILE"
echo "   Arc::new: $ARC_COUNT 次"

# 7. Await点统计
echo "⏳ 统计Await点..."
AWAIT_COUNT=$(rg "\.await" crates/otlp/src --type rust -c 2>/dev/null | awk -F: '{sum+=$2} END {print sum+0}')
echo "Await点: $AWAIT_COUNT 个" >> "$OUTPUT_FILE"
echo "   Await点: $AWAIT_COUNT 个"

cat >> "$OUTPUT_FILE" <<EOF

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 🏗️  架构指标

EOF

# 8. 公共结构体统计
echo "📦 统计公共结构体..."
STRUCT_COUNT=$(rg "pub struct" crates/otlp/src --type rust -c 2>/dev/null | awk -F: '{sum+=$2} END {print sum+0}')
echo "公共结构体: $STRUCT_COUNT 个" >> "$OUTPUT_FILE"
echo "   公共结构体: $STRUCT_COUNT 个"

# 9. 公共枚举统计
echo "🔢 统计公共枚举..."
ENUM_COUNT=$(rg "pub enum" crates/otlp/src --type rust -c 2>/dev/null | awk -F: '{sum+=$2} END {print sum+0}')
echo "公共枚举: $ENUM_COUNT 个" >> "$OUTPUT_FILE"
echo "   公共枚举: $ENUM_COUNT 个"

# 10. 公共Trait统计
echo "🎭 统计公共Trait..."
TRAIT_COUNT=$(rg "pub trait" crates/otlp/src --type rust -c 2>/dev/null | awk -F: '{sum+=$2} END {print sum+0}')
echo "公共Trait: $TRAIT_COUNT 个" >> "$OUTPUT_FILE"
echo "   公共Trait: $TRAIT_COUNT 个"

cat >> "$OUTPUT_FILE" <<EOF

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 📈 质量趋势

EOF

# 计算质量指标
if [ $RUST_FILES -gt 0 ]; then
    TEST_COVERAGE=$(echo "scale=2; $TEST_FNS / $RUST_FILES" | bc)
else
    TEST_COVERAGE=0
fi

if [ $TEST_FNS -gt 0 ]; then
    ASYNC_RATIO=$(echo "scale=1; $ASYNC_TESTS * 100 / $TEST_FNS" | bc)
else
    ASYNC_RATIO=0
fi

CLONE_PER_FILE=$(echo "scale=2; $CLONE_COUNT / $RUST_FILES" | bc)
UNSAFE_PER_FILE=$(echo "scale=2; $UNSAFE_COUNT / $RUST_FILES" | bc)

cat >> "$OUTPUT_FILE" <<EOF

每文件测试数: $TEST_COVERAGE 个/文件
异步测试占比: $ASYNC_RATIO%
Clone/文件比: $CLONE_PER_FILE
Unsafe/文件比: $UNSAFE_PER_FILE

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 🎯 改进目标对比

当前 vs 目标:

EOF

# 生成目标对比
[ $TEST_FNS -ge 400 ] && TEST_STATUS="✅" || TEST_STATUS="⏳"
[ $CLONE_COUNT -le 340 ] && CLONE_STATUS="✅" || CLONE_STATUS="⏳"
[ $RUST_FILES -le 60 ] && FILE_STATUS="✅" || FILE_STATUS="⏳"
[ $STRUCT_COUNT -le 300 ] && STRUCT_STATUS="✅" || STRUCT_STATUS="⏳"

cat >> "$OUTPUT_FILE" <<EOF
测试函数:     $TEST_FNS → 400+ $TEST_STATUS
Clone操作:    $CLONE_COUNT → 340 $CLONE_STATUS
Unsafe文档:   估计0% → 100% ⏳
Rust文件:     $RUST_FILES → <60 $FILE_STATUS
公共结构体:   $STRUCT_COUNT → 300 $STRUCT_STATUS

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 💡 建议

EOF

# 生成建议
SUGGESTIONS=0

if [ $TEST_FNS -lt 400 ]; then
    NEEDED=$((400 - TEST_FNS))
    echo "- 需要增加 $NEEDED 个测试函数" >> "$OUTPUT_FILE"
    ((SUGGESTIONS++))
fi

if [ $CLONE_COUNT -gt 340 ]; then
    REDUCE=$((CLONE_COUNT - 340))
    echo "- 需要减少 $REDUCE 次clone操作" >> "$OUTPUT_FILE"
    ((SUGGESTIONS++))
fi

if [ $UNSAFE_COUNT -gt 0 ]; then
    echo "- 需要为 $UNSAFE_COUNT 个unsafe块添加safety文档" >> "$OUTPUT_FILE"
    ((SUGGESTIONS++))
fi

if [ $RUST_FILES -gt 60 ]; then
    REDUCE=$((RUST_FILES - 60))
    echo "- 需要减少 $REDUCE 个Rust文件（合并模块）" >> "$OUTPUT_FILE"
    ((SUGGESTIONS++))
fi

if [ $STRUCT_COUNT -gt 300 ]; then
    REDUCE=$((STRUCT_COUNT - 300))
    echo "- 需要减少 $REDUCE 个公共结构体（隐藏内部实现）" >> "$OUTPUT_FILE"
    ((SUGGESTIONS++))
fi

if [ $SUGGESTIONS -eq 0 ]; then
    echo -e "\n所有目标已达成! 🎉\n" >> "$OUTPUT_FILE"
else
    echo "" >> "$OUTPUT_FILE"
fi

cat >> "$OUTPUT_FILE" <<EOF

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

报告生成完成！

可以使用以下命令定期运行此脚本追踪进度：
    bash scripts/track_code_quality.sh

EOF

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "✅ 报告已生成: $OUTPUT_FILE"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# 显示报告摘要
echo "📄 报告摘要:"
echo ""
echo "   Rust文件:    $RUST_FILES"
echo "   测试函数:    $TEST_FNS"
echo "   Clone操作:   $CLONE_COUNT"
echo "   Unsafe块:    $UNSAFE_COUNT"
echo "   公共结构体:  $STRUCT_COUNT"
echo ""

if [ $SUGGESTIONS -gt 0 ]; then
    echo "⚠️  待改进项目: $SUGGESTIONS 个"
else
    echo "🎉 所有目标已达成!"
fi

echo ""
echo "详细报告请查看: $OUTPUT_FILE"

