#!/bin/bash
# 文档清理脚本 2025-10-26
# 用法: ./scripts/doc_cleanup_2025_10_26.sh

set -e

echo "================================"
echo "OTLP_rust 文档清理脚本"
echo "================================"
echo ""

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# 创建归档目录
create_archive_dirs() {
    echo -e "${YELLOW}[1/6] 创建归档目录...${NC}"
    mkdir -p crates/otlp/docs/archives/reports/2025-10
    mkdir -p crates/libraries/docs/reports/phases/2025-10
    mkdir -p crates/model/docs/archives/reports/2025-10
    mkdir -p crates/reliability/docs/archives/reports/2025-10
    echo -e "${GREEN}✓ 归档目录创建完成${NC}"
    echo ""
}

# 清理 otlp 文档
cleanup_otlp() {
    echo -e "${YELLOW}[2/6] 清理 crates/otlp/docs/...${NC}"
    
    cd crates/otlp/docs
    
    # 移动完成报告
    echo "  移动完成报告..."
    find . -maxdepth 1 -name "*完成报告*.md" -exec mv {} archives/reports/2025-10/ \; 2>/dev/null || true
    find . -maxdepth 1 -name "*COMPLETION*.md" -exec mv {} archives/reports/2025-10/ \; 2>/dev/null || true
    
    # 移动推进报告
    echo "  移动推进报告..."
    find . -maxdepth 1 -name "*推进报告*.md" -exec mv {} archives/reports/2025-10/ \; 2>/dev/null || true
    find . -maxdepth 1 -name "*PROGRESS*.md" -exec mv {} archives/reports/2025-10/ \; 2>/dev/null || true
    
    # 移动总结报告
    echo "  移动总结报告..."
    find . -maxdepth 1 -name "*总结报告*.md" -exec mv {} archives/reports/2025-10/ \; 2>/dev/null || true
    find . -maxdepth 1 -name "*SUMMARY*.md" -exec mv {} archives/reports/2025-10/ \; 2>/dev/null || true
    
    # 移动状态报告
    echo "  移动状态报告..."
    find . -maxdepth 1 -name "*STATUS*.md" -exec mv {} archives/reports/2025-10/ \; 2>/dev/null || true
    
    # 移动多任务报告
    echo "  移动多任务报告..."
    find . -maxdepth 1 -name "*多任务*.md" -exec mv {} archives/reports/2025-10/ \; 2>/dev/null || true
    find . -maxdepth 1 -name "*MULTI_TASK*.md" -exec mv {} archives/reports/2025-10/ \; 2>/dev/null || true
    
    cd ../../..
    echo -e "${GREEN}✓ otlp 文档清理完成${NC}"
    echo ""
}

# 清理 libraries 文档
cleanup_libraries() {
    echo -e "${YELLOW}[3/6] 清理 crates/libraries/docs/...${NC}"
    
    cd crates/libraries/docs
    
    # 移动 Phase 报告
    echo "  移动 Phase 报告..."
    find . -maxdepth 1 -name "PHASE*.md" -exec mv {} reports/phases/2025-10/ \; 2>/dev/null || true
    
    # 移动其他报告
    echo "  移动其他报告..."
    find . -maxdepth 1 -name "*COMPLETION*.md" -exec mv {} reports/phases/2025-10/ \; 2>/dev/null || true
    find . -maxdepth 1 -name "*PROGRESS*.md" -exec mv {} reports/phases/2025-10/ \; 2>/dev/null || true
    find . -maxdepth 1 -name "*ROADMAP*.md" -exec mv {} reports/phases/2025-10/ \; 2>/dev/null || true
    
    cd ../../..
    echo -e "${GREEN}✓ libraries 文档清理完成${NC}"
    echo ""
}

# 清理 model 文档
cleanup_model() {
    echo -e "${YELLOW}[4/6] 清理 crates/model/docs/...${NC}"
    
    cd crates/model/docs
    
    # 移动中文报告
    echo "  移动中文报告..."
    find . -maxdepth 1 -name "文档*.md" -exec mv {} archives/reports/2025-10/ \; 2>/dev/null || true
    find . -maxdepth 1 -name "*梳理*.md" -exec mv {} archives/reports/2025-10/ \; 2>/dev/null || true
    find . -maxdepth 1 -name "*目录*.md" -exec mv {} archives/reports/2025-10/ \; 2>/dev/null || true
    
    cd ../../..
    echo -e "${GREEN}✓ model 文档清理完成${NC}"
    echo ""
}

# 清理 reliability 文档
cleanup_reliability() {
    echo -e "${YELLOW}[5/6] 清理 crates/reliability/docs/...${NC}"
    
    cd crates/reliability/docs
    
    # 移动中文报告
    echo "  移动中文报告..."
    find . -maxdepth 1 -name "*完成*.md" -exec mv {} archives/reports/2025-10/ \; 2>/dev/null || true
    find . -maxdepth 1 -name "*推进*.md" -exec mv {} archives/reports/2025-10/ \; 2>/dev/null || true
    find . -maxdepth 1 -name "文档*.md" -exec mv {} archives/reports/2025-10/ \; 2>/dev/null || true
    find . -maxdepth 1 -name "*梳理*.md" -exec mv {} archives/reports/2025-10/ \; 2>/dev/null || true
    
    cd ../../..
    echo -e "${GREEN}✓ reliability 文档清理完成${NC}"
    echo ""
}

# 生成清理报告
generate_report() {
    echo -e "${YELLOW}[6/6] 生成清理报告...${NC}"
    
    REPORT_FILE="DOC_CLEANUP_RESULT_$(date +%Y_%m_%d_%H%M%S).txt"
    
    cat > "$REPORT_FILE" << EOF
# 文档清理结果报告

**执行时间**: $(date)
**清理脚本**: doc_cleanup_2025_10_26.sh

## 清理统计

### crates/otlp/docs
归档文件数: $(ls -1 crates/otlp/docs/archives/reports/2025-10/ 2>/dev/null | wc -l)
归档位置: crates/otlp/docs/archives/reports/2025-10/

### crates/libraries/docs
归档文件数: $(ls -1 crates/libraries/docs/reports/phases/2025-10/ 2>/dev/null | wc -l)
归档位置: crates/libraries/docs/reports/phases/2025-10/

### crates/model/docs
归档文件数: $(ls -1 crates/model/docs/archives/reports/2025-10/ 2>/dev/null | wc -l)
归档位置: crates/model/docs/archives/reports/2025-10/

### crates/reliability/docs
归档文件数: $(ls -1 crates/reliability/docs/archives/reports/2025-10/ 2>/dev/null | wc -l)
归档位置: crates/reliability/docs/archives/reports/2025-10/

## 归档文件列表

### otlp
$(ls -1 crates/otlp/docs/archives/reports/2025-10/ 2>/dev/null)

### libraries
$(ls -1 crates/libraries/docs/reports/phases/2025-10/ 2>/dev/null)

### model
$(ls -1 crates/model/docs/archives/reports/2025-10/ 2>/dev/null)

### reliability
$(ls -1 crates/reliability/docs/archives/reports/2025-10/ 2>/dev/null)

---

## 下一步建议

1. 查看归档文件，确认没有误操作
2. 如有问题，可以从archives恢复
3. 继续执行阶段2的结构统一工作
4. 参考: COMPREHENSIVE_DOCUMENTATION_AUDIT_REPORT_2025_10_26.md

EOF

    echo -e "${GREEN}✓ 清理报告已生成: $REPORT_FILE${NC}"
    echo ""
}

# 主流程
main() {
    echo "开始执行文档清理..."
    echo ""
    
    # 确认操作
    echo -e "${RED}警告: 此脚本将移动大量文档文件到归档目录${NC}"
    echo -e "${YELLOW}建议先备份项目或确保Git状态干净${NC}"
    echo ""
    read -p "确认继续? (y/N): " -n 1 -r
    echo
    if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        echo "操作已取消"
        exit 1
    fi
    
    # 执行清理
    create_archive_dirs
    cleanup_otlp
    cleanup_libraries
    cleanup_model
    cleanup_reliability
    generate_report
    
    echo ""
    echo -e "${GREEN}================================${NC}"
    echo -e "${GREEN}文档清理完成！${NC}"
    echo -e "${GREEN}================================${NC}"
    echo ""
    echo "清理报告已保存，请查看详细结果"
    echo ""
    echo "下一步:"
    echo "1. 查看归档文件确认无误"
    echo "2. 提交Git更改"
    echo "3. 继续阶段2的结构统一工作"
    echo ""
}

# 执行主流程
main

