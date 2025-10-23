#!/bin/bash

# OTLP Rust Project - Phase 1 Cleanup Script
# Date: 2025-10-23
# Description: Removes unrelated modules and theoretical documents

set -e  # Exit on error

echo "🚀 OTLP Rust Project - Phase 1 Cleanup"
echo "======================================"
echo ""

# Color codes
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Check if we're in the right directory
if [ ! -f "Cargo.toml" ]; then
    echo -e "${RED}Error: Cargo.toml not found. Please run this script from the project root.${NC}"
    exit 1
fi

# Check if on main branch (prevent accidental execution)
CURRENT_BRANCH=$(git branch --show-current)
if [ "$CURRENT_BRANCH" = "main" ] || [ "$CURRENT_BRANCH" = "master" ]; then
    echo -e "${RED}Warning: You are on the main/master branch!${NC}"
    echo "Please create a cleanup branch first:"
    echo "  git checkout -b cleanup/phase1-major-refactor"
    exit 1
fi

echo -e "${YELLOW}⚠️  WARNING: This script will delete files!${NC}"
echo "Current branch: $CURRENT_BRANCH"
echo ""
echo "This script will:"
echo "  1. Remove AI/ML modules"
echo "  2. Remove blockchain modules"
echo "  3. Remove edge computing modules"
echo "  4. Remove backup directory"
echo "  5. Remove theoretical research documents"
echo "  6. Remove Chinese progress reports"
echo "  7. Remove duplicate progress reports"
echo ""
read -p "Do you want to continue? (yes/no): " CONFIRM

if [ "$CONFIRM" != "yes" ]; then
    echo "Aborted."
    exit 0
fi

echo ""
echo "Starting cleanup..."
echo ""

# Function to safely remove directory
safe_remove_dir() {
    local dir=$1
    if [ -d "$dir" ]; then
        echo -e "${GREEN}✓${NC} Removing directory: $dir"
        rm -rf "$dir"
    else
        echo -e "${YELLOW}⊘${NC} Directory not found (skip): $dir"
    fi
}

# Function to safely remove file
safe_remove_file() {
    local file=$1
    if [ -f "$file" ]; then
        echo -e "${GREEN}✓${NC} Removing file: $file"
        rm -f "$file"
    else
        echo -e "${YELLOW}⊘${NC} File not found (skip): $file"
    fi
}

# 1. Remove unrelated feature modules
echo "📦 Step 1: Removing unrelated modules..."
safe_remove_dir "crates/otlp/src/ai_ml"
safe_remove_dir "crates/otlp/src/blockchain"
safe_remove_dir "crates/otlp/src/edge_computing"
echo ""

# 2. Remove backup directory
echo "🗑️  Step 2: Removing backup directory..."
safe_remove_dir "backup_2025_01"
echo ""

# 3. Remove theoretical research documents
echo "📚 Step 3: Removing theoretical research documents..."
safe_remove_dir "analysis/23_quantum_inspired_observability"
safe_remove_dir "analysis/24_neuromorphic_monitoring"
safe_remove_dir "analysis/25_edge_ai_fusion"
echo ""

# 4. Remove Chinese progress reports
echo "📝 Step 4: Removing Chinese progress reports..."
safe_remove_file "完整交付清单_2025_10_20.md"
safe_remove_file "对外发布准备清单_2025_10_20.md"
safe_remove_file "工作完成确认_2025_10_20.md"
safe_remove_file "持续推进最终总结_2025_10_20.md"
safe_remove_file "持续推进工作完成报告_简版_2025_10_20.md"
safe_remove_file "持续推进总结_2025_10_20.md"
safe_remove_file "文档体系建设完成报告_2025_10_20.md"
safe_remove_file "文档可视化分析完成报告_2025_10_20.md"
safe_remove_file "文档清理完善完成报告_2025_10_20.md"
safe_remove_file "文档清理整合计划_2025_10_20.md"
safe_remove_file "架构规划交付清单_2025_10_20.md"
safe_remove_file "项目一页纸总结_2025_10_20.md"
safe_remove_file "项目成就与里程碑_2025_10_20.md"
safe_remove_file "项目持续推进总结_2025_10_20_更新.md"
safe_remove_file "项目持续推进总结_2025_10_20.md"
safe_remove_file "项目文档体系全面完成报告_2025_10_20.md"
echo ""

# 5. Remove duplicate progress reports
echo "📄 Step 5: Removing duplicate progress reports..."
if [ -d "analysis/22_rust_1.90_otlp_comprehensive_analysis" ]; then
    cd analysis/22_rust_1.90_otlp_comprehensive_analysis
    rm -f PROGRESS_*.md SESSION_*.md PART*_*.md 2>/dev/null || true
    cd ../..
    echo -e "${GREEN}✓${NC} Removed duplicate progress reports"
else
    echo -e "${YELLOW}⊘${NC} Directory not found (skip)"
fi
echo ""

# 6. Generate statistics
echo "📊 Step 6: Generating cleanup statistics..."

STATS_FILE="cleanup_after_stats.txt"

echo "=== Cleanup Statistics ===" > "$STATS_FILE"
echo "Date: $(date)" >> "$STATS_FILE"
echo "" >> "$STATS_FILE"

echo "Rust files:" >> "$STATS_FILE"
RUST_COUNT=$(find . -name "*.rs" -not -path "./target/*" | wc -l)
echo "  Count: $RUST_COUNT" >> "$STATS_FILE"

echo "" >> "$STATS_FILE"
echo "Markdown files:" >> "$STATS_FILE"
MD_COUNT=$(find . -name "*.md" | wc -l)
echo "  Count: $MD_COUNT" >> "$STATS_FILE"

echo "" >> "$STATS_FILE"
echo "Total lines of Rust code:" >> "$STATS_FILE"
find . -name "*.rs" -not -path "./target/*" -exec wc -l {} + | tail -1 >> "$STATS_FILE"

echo -e "${GREEN}✓${NC} Statistics saved to: $STATS_FILE"
cat "$STATS_FILE"
echo ""

# 7. Verify compilation
echo "🔧 Step 7: Verifying compilation..."
if cargo check --workspace 2>&1 | tee cleanup_compile_log.txt; then
    echo -e "${GREEN}✅ Compilation successful!${NC}"
else
    echo -e "${RED}❌ Compilation failed!${NC}"
    echo "Please check cleanup_compile_log.txt for errors"
    echo "You may need to update lib.rs to remove references to deleted modules"
    exit 1
fi
echo ""

# 8. Summary
echo "======================================"
echo -e "${GREEN}✅ Phase 1 Cleanup Complete!${NC}"
echo "======================================"
echo ""
echo "Summary:"
echo "  - Removed unrelated modules (AI/ML, blockchain, edge computing)"
echo "  - Removed backup directory"
echo "  - Removed theoretical research documents"
echo "  - Removed Chinese progress reports"
echo "  - Removed duplicate progress reports"
echo "  - Project compiled successfully"
echo ""
echo "Statistics:"
echo "  - Rust files: $RUST_COUNT"
echo "  - Markdown files: $MD_COUNT"
echo ""
echo "Next steps:"
echo "  1. Review the changes: git status"
echo "  2. Update lib.rs to remove deleted module exports"
echo "  3. Run tests: cargo test --workspace"
echo "  4. Commit changes: git add . && git commit"
echo ""
echo "Files created:"
echo "  - $STATS_FILE (cleanup statistics)"
echo "  - cleanup_compile_log.txt (compilation log)"
echo ""
echo -e "${YELLOW}⚠️  Don't forget to update lib.rs!${NC}"
echo ""

