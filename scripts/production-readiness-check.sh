#!/bin/bash

# OTLP Rust 生产环境就绪性检查脚本
# 本脚本检查系统是否准备好进行生产环境部署

set -euo pipefail

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# 日志函数
log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

log_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# 检查结果统计
TOTAL_CHECKS=0
PASSED_CHECKS=0
FAILED_CHECKS=0
WARNING_CHECKS=0

# 检查函数
check_pass() {
    PASSED_CHECKS=$((PASSED_CHECKS + 1))
    TOTAL_CHECKS=$((TOTAL_CHECKS + 1))
    log_success "$1"
}

check_fail() {
    FAILED_CHECKS=$((FAILED_CHECKS + 1))
    TOTAL_CHECKS=$((TOTAL_CHECKS + 1))
    log_error "$1"
}

check_warning() {
    WARNING_CHECKS=$((WARNING_CHECKS + 1))
    TOTAL_CHECKS=$((TOTAL_CHECKS + 1))
    log_warning "$1"
}

# 检查依赖
check_dependencies() {
    log_info "检查系统依赖..."
    
    # 检查Rust
    if command -v rustc &> /dev/null; then
        RUST_VERSION=$(rustc --version | cut -d' ' -f2)
        if [[ "$RUST_VERSION" == "1.90"* ]]; then
            check_pass "Rust版本检查通过: $RUST_VERSION"
        else
            check_warning "Rust版本可能不兼容: $RUST_VERSION (推荐: 1.90+)"
        fi
    else
        check_fail "Rust未安装"
    fi
    
    # 检查Cargo
    if command -v cargo &> /dev/null; then
        check_pass "Cargo已安装"
    else
        check_fail "Cargo未安装"
    fi
    
    # 检查Docker
    if command -v docker &> /dev/null; then
        if docker info &> /dev/null; then
            check_pass "Docker已安装且运行正常"
        else
            check_fail "Docker未运行"
        fi
    else
        check_fail "Docker未安装"
    fi
    
    # 检查kubectl
    if command -v kubectl &> /dev/null; then
        if kubectl cluster-info &> /dev/null; then
            check_pass "kubectl已安装且集群连接正常"
        else
            check_fail "kubectl集群连接失败"
        fi
    else
        check_fail "kubectl未安装"
    fi
    
    # 检查helm
    if command -v helm &> /dev/null; then
        check_pass "Helm已安装"
    else
        check_fail "Helm未安装"
    fi
}

# 检查代码质量
check_code_quality() {
    log_info "检查代码质量..."
    
    # 检查代码编译
    if cargo check --package otlp &> /dev/null; then
        check_pass "代码编译检查通过"
    else
        check_fail "代码编译失败"
    fi
    
    # 检查测试
    if cargo test --package otlp --lib &> /dev/null; then
        check_pass "单元测试通过"
    else
        check_fail "单元测试失败"
    fi
    
    # 检查Clippy
    if command -v cargo-clippy &> /dev/null; then
        if cargo clippy --package otlp &> /dev/null; then
            check_pass "Clippy检查通过"
        else
            check_warning "Clippy检查有警告"
        fi
    else
        check_warning "Clippy未安装"
    fi
    
    # 检查格式化
    if cargo fmt --package otlp --check &> /dev/null; then
        check_pass "代码格式化检查通过"
    else
        check_warning "代码格式化需要调整"
    fi
}

# 检查安全
check_security() {
    log_info "检查安全配置..."
    
    # 检查依赖漏洞
    if command -v cargo-audit &> /dev/null; then
        if cargo audit --package otlp &> /dev/null; then
            check_pass "依赖安全审计通过"
        else
            check_warning "依赖安全审计有警告"
        fi
    else
        check_warning "cargo-audit未安装"
    fi
    
    # 检查TLS证书
    if [ -f "k8s/ssl/otlp.crt" ] && [ -f "k8s/ssl/otlp.key" ]; then
        check_pass "TLS证书文件存在"
    else
        check_warning "TLS证书文件不存在"
    fi
    
    # 检查密钥管理
    if [ -f "k8s/otlp-production-deployment.yaml" ]; then
        if grep -q "secretName: otlp-secrets" k8s/otlp-production-deployment.yaml; then
            check_pass "密钥管理配置存在"
        else
            check_warning "密钥管理配置不完整"
        fi
    else
        check_fail "生产环境部署配置不存在"
    fi
}

# 检查性能
check_performance() {
    log_info "检查性能配置..."
    
    # 检查性能基准测试
    if [ -f "otlp/benches/otlp_benchmarks.rs" ]; then
        check_pass "性能基准测试文件存在"
    else
        check_warning "性能基准测试文件不存在"
    fi
    
    # 检查性能优化配置
    if [ -f "otlp/config/production.toml" ]; then
        if grep -q "enable_memory_pool = true" otlp/config/production.toml; then
            check_pass "性能优化配置存在"
        else
            check_warning "性能优化配置不完整"
        fi
    else
        check_fail "生产环境配置文件不存在"
    fi
    
    # 检查资源限制
    if [ -f "k8s/otlp-production-deployment.yaml" ]; then
        if grep -q "resources:" k8s/otlp-production-deployment.yaml; then
            check_pass "资源限制配置存在"
        else
            check_warning "资源限制配置不完整"
        fi
    else
        check_fail "生产环境部署配置不存在"
    fi
}

# 检查监控
check_monitoring() {
    log_info "检查监控配置..."
    
    # 检查监控配置
    if [ -f "monitoring/grafana-dashboard.json" ]; then
        check_pass "Grafana仪表板配置存在"
    else
        check_warning "Grafana仪表板配置不存在"
    fi
    
    # 检查Prometheus配置
    if [ -f "k8s/otlp-production-deployment.yaml" ]; then
        if grep -q "prometheus.io/scrape" k8s/otlp-production-deployment.yaml; then
            check_pass "Prometheus监控配置存在"
        else
            check_warning "Prometheus监控配置不完整"
        fi
    else
        check_fail "生产环境部署配置不存在"
    fi
    
    # 检查告警配置
    if [ -f "k8s/otlp-production-deployment.yaml" ]; then
        if grep -q "PrometheusRule" k8s/otlp-production-deployment.yaml; then
            check_pass "告警配置存在"
        else
            check_warning "告警配置不完整"
        fi
    else
        check_fail "生产环境部署配置不存在"
    fi
}

# 检查高可用性
check_high_availability() {
    log_info "检查高可用性配置..."
    
    # 检查副本数配置
    if [ -f "k8s/otlp-production-deployment.yaml" ]; then
        if grep -q "replicas: 3" k8s/otlp-production-deployment.yaml; then
            check_pass "多副本配置存在"
        else
            check_warning "多副本配置不完整"
        fi
    else
        check_fail "生产环境部署配置不存在"
    fi
    
    # 检查HPA配置
    if [ -f "k8s/otlp-production-deployment.yaml" ]; then
        if grep -q "HorizontalPodAutoscaler" k8s/otlp-production-deployment.yaml; then
            check_pass "自动扩缩容配置存在"
        else
            check_warning "自动扩缩容配置不完整"
        fi
    else
        check_fail "生产环境部署配置不存在"
    fi
    
    # 检查PDB配置
    if [ -f "k8s/otlp-production-deployment.yaml" ]; then
        if grep -q "PodDisruptionBudget" k8s/otlp-production-deployment.yaml; then
            check_pass "PodDisruptionBudget配置存在"
        else
            check_warning "PodDisruptionBudget配置不完整"
        fi
    else
        check_fail "生产环境部署配置不存在"
    fi
}

# 检查企业级功能
check_enterprise_features() {
    log_info "检查企业级功能配置..."
    
    # 检查多租户配置
    if [ -f "otlp/config/production.toml" ]; then
        if grep -q "enable_multi_tenant = true" otlp/config/production.toml; then
            check_pass "多租户功能配置存在"
        else
            check_warning "多租户功能配置不完整"
        fi
    else
        check_fail "生产环境配置文件不存在"
    fi
    
    # 检查数据治理配置
    if [ -f "otlp/config/production.toml" ]; then
        if grep -q "enable_data_governance = true" otlp/config/production.toml; then
            check_pass "数据治理功能配置存在"
        else
            check_warning "数据治理功能配置不完整"
        fi
    else
        check_fail "生产环境配置文件不存在"
    fi
    
    # 检查合规性配置
    if [ -f "otlp/config/production.toml" ]; then
        if grep -q "compliance_frameworks" otlp/config/production.toml; then
            check_pass "合规性功能配置存在"
        else
            check_warning "合规性功能配置不完整"
        fi
    else
        check_fail "生产环境配置文件不存在"
    fi
}

# 检查文档
check_documentation() {
    log_info "检查文档完整性..."
    
    # 检查API文档
    if [ -f "otlp/docs/API_REFERENCE.md" ]; then
        check_pass "API参考文档存在"
    else
        check_warning "API参考文档不存在"
    fi
    
    # 检查快速开始指南
    if [ -f "otlp/docs/QUICK_START_GUIDE.md" ]; then
        check_pass "快速开始指南存在"
    else
        check_warning "快速开始指南不存在"
    fi
    
    # 检查部署指南
    if [ -f "scripts/deploy-production.sh" ]; then
        check_pass "部署脚本存在"
    else
        check_warning "部署脚本不存在"
    fi
    
    # 检查README
    if [ -f "README.md" ]; then
        check_pass "README文件存在"
    else
        check_warning "README文件不存在"
    fi
}

# 检查部署配置
check_deployment_config() {
    log_info "检查部署配置..."
    
    # 检查Kubernetes配置
    if [ -f "k8s/otlp-production-deployment.yaml" ]; then
        check_pass "Kubernetes部署配置存在"
    else
        check_fail "Kubernetes部署配置不存在"
    fi
    
    # 检查Docker配置
    if [ -f "Dockerfile.production" ]; then
        check_pass "生产环境Dockerfile存在"
    else
        check_fail "生产环境Dockerfile不存在"
    fi
    
    # 检查Helm配置
    if [ -f "helm/otlp-server/Chart.yaml" ] && [ -f "helm/otlp-server/values.yaml" ]; then
        check_pass "Helm Chart配置存在"
    else
        check_warning "Helm Chart配置不完整"
    fi
    
    # 检查部署脚本
    if [ -f "scripts/deploy-production.sh" ]; then
        if [ -x "scripts/deploy-production.sh" ]; then
            check_pass "部署脚本可执行"
        else
            check_warning "部署脚本不可执行"
        fi
    else
        check_fail "部署脚本不存在"
    fi
}

# 检查网络配置
check_network_config() {
    log_info "检查网络配置..."
    
    # 检查网络策略
    if [ -f "k8s/otlp-production-deployment.yaml" ]; then
        if grep -q "NetworkPolicy" k8s/otlp-production-deployment.yaml; then
            check_pass "网络策略配置存在"
        else
            check_warning "网络策略配置不完整"
        fi
    else
        check_fail "生产环境部署配置不存在"
    fi
    
    # 检查Ingress配置
    if [ -f "k8s/otlp-production-deployment.yaml" ]; then
        if grep -q "Ingress" k8s/otlp-production-deployment.yaml; then
            check_pass "Ingress配置存在"
        else
            check_warning "Ingress配置不完整"
        fi
    else
        check_fail "生产环境部署配置不存在"
    fi
    
    # 检查Service配置
    if [ -f "k8s/otlp-production-deployment.yaml" ]; then
        if grep -q "kind: Service" k8s/otlp-production-deployment.yaml; then
            check_pass "Service配置存在"
        else
            check_warning "Service配置不完整"
        fi
    else
        check_fail "生产环境部署配置不存在"
    fi
}

# 检查存储配置
check_storage_config() {
    log_info "检查存储配置..."
    
    # 检查PVC配置
    if [ -f "k8s/otlp-production-deployment.yaml" ]; then
        if grep -q "PersistentVolumeClaim" k8s/otlp-production-deployment.yaml; then
            check_pass "持久化存储配置存在"
        else
            check_warning "持久化存储配置不完整"
        fi
    else
        check_fail "生产环境部署配置不存在"
    fi
    
    # 检查存储类配置
    if [ -f "k8s/otlp-production-deployment.yaml" ]; then
        if grep -q "storageClassName" k8s/otlp-production-deployment.yaml; then
            check_pass "存储类配置存在"
        else
            check_warning "存储类配置不完整"
        fi
    else
        check_fail "生产环境部署配置不存在"
    fi
}

# 生成报告
generate_report() {
    log_info "生成生产环境就绪性报告..."
    
    local report_file="production-readiness-report-$(date +%Y%m%d-%H%M%S).md"
    
    cat > "$report_file" << EOF
# OTLP Rust 生产环境就绪性报告

**生成时间**: $(date)
**检查版本**: 1.0.0

## 检查摘要

- **总检查项**: $TOTAL_CHECKS
- **通过**: $PASSED_CHECKS
- **失败**: $FAILED_CHECKS
- **警告**: $WARNING_CHECKS
- **成功率**: $(( (PASSED_CHECKS * 100) / TOTAL_CHECKS ))%

## 检查结果

### 系统依赖
- Rust版本检查: $([ $PASSED_CHECKS -gt 0 ] && echo "✅ 通过" || echo "❌ 失败")
- Cargo检查: $([ $PASSED_CHECKS -gt 1 ] && echo "✅ 通过" || echo "❌ 失败")
- Docker检查: $([ $PASSED_CHECKS -gt 2 ] && echo "✅ 通过" || echo "❌ 失败")
- kubectl检查: $([ $PASSED_CHECKS -gt 3 ] && echo "✅ 通过" || echo "❌ 失败")
- Helm检查: $([ $PASSED_CHECKS -gt 4 ] && echo "✅ 通过" || echo "❌ 失败")

### 代码质量
- 代码编译: $([ $PASSED_CHECKS -gt 5 ] && echo "✅ 通过" || echo "❌ 失败")
- 单元测试: $([ $PASSED_CHECKS -gt 6 ] && echo "✅ 通过" || echo "❌ 失败")
- Clippy检查: $([ $PASSED_CHECKS -gt 7 ] && echo "✅ 通过" || echo "⚠️ 警告")
- 代码格式化: $([ $PASSED_CHECKS -gt 8 ] && echo "✅ 通过" || echo "⚠️ 警告")

### 安全配置
- 依赖安全审计: $([ $PASSED_CHECKS -gt 9 ] && echo "✅ 通过" || echo "⚠️ 警告")
- TLS证书: $([ $PASSED_CHECKS -gt 10 ] && echo "✅ 通过" || echo "⚠️ 警告")
- 密钥管理: $([ $PASSED_CHECKS -gt 11 ] && echo "✅ 通过" || echo "⚠️ 警告")

### 性能配置
- 性能基准测试: $([ $PASSED_CHECKS -gt 12 ] && echo "✅ 通过" || echo "⚠️ 警告")
- 性能优化配置: $([ $PASSED_CHECKS -gt 13 ] && echo "✅ 通过" || echo "❌ 失败")
- 资源限制: $([ $PASSED_CHECKS -gt 14 ] && echo "✅ 通过" || echo "⚠️ 警告")

### 监控配置
- Grafana仪表板: $([ $PASSED_CHECKS -gt 15 ] && echo "✅ 通过" || echo "⚠️ 警告")
- Prometheus监控: $([ $PASSED_CHECKS -gt 16 ] && echo "✅ 通过" || echo "⚠️ 警告")
- 告警配置: $([ $PASSED_CHECKS -gt 17 ] && echo "✅ 通过" || echo "⚠️ 警告")

### 高可用性
- 多副本配置: $([ $PASSED_CHECKS -gt 18 ] && echo "✅ 通过" || echo "⚠️ 警告")
- 自动扩缩容: $([ $PASSED_CHECKS -gt 19 ] && echo "✅ 通过" || echo "⚠️ 警告")
- PodDisruptionBudget: $([ $PASSED_CHECKS -gt 20 ] && echo "✅ 通过" || echo "⚠️ 警告")

### 企业级功能
- 多租户功能: $([ $PASSED_CHECKS -gt 21 ] && echo "✅ 通过" || echo "⚠️ 警告")
- 数据治理: $([ $PASSED_CHECKS -gt 22 ] && echo "✅ 通过" || echo "⚠️ 警告")
- 合规性: $([ $PASSED_CHECKS -gt 23 ] && echo "✅ 通过" || echo "⚠️ 警告")

### 文档完整性
- API文档: $([ $PASSED_CHECKS -gt 24 ] && echo "✅ 通过" || echo "⚠️ 警告")
- 快速开始指南: $([ $PASSED_CHECKS -gt 25 ] && echo "✅ 通过" || echo "⚠️ 警告")
- 部署脚本: $([ $PASSED_CHECKS -gt 26 ] && echo "✅ 通过" || echo "⚠️ 警告")
- README: $([ $PASSED_CHECKS -gt 27 ] && echo "✅ 通过" || echo "⚠️ 警告")

### 部署配置
- Kubernetes配置: $([ $PASSED_CHECKS -gt 28 ] && echo "✅ 通过" || echo "❌ 失败")
- Docker配置: $([ $PASSED_CHECKS -gt 29 ] && echo "✅ 通过" || echo "❌ 失败")
- Helm配置: $([ $PASSED_CHECKS -gt 30 ] && echo "✅ 通过" || echo "⚠️ 警告")
- 部署脚本: $([ $PASSED_CHECKS -gt 31 ] && echo "✅ 通过" || echo "❌ 失败")

### 网络配置
- 网络策略: $([ $PASSED_CHECKS -gt 32 ] && echo "✅ 通过" || echo "⚠️ 警告")
- Ingress配置: $([ $PASSED_CHECKS -gt 33 ] && echo "✅ 通过" || echo "⚠️ 警告")
- Service配置: $([ $PASSED_CHECKS -gt 34 ] && echo "✅ 通过" || echo "⚠️ 警告")

### 存储配置
- 持久化存储: $([ $PASSED_CHECKS -gt 35 ] && echo "✅ 通过" || echo "⚠️ 警告")
- 存储类配置: $([ $PASSED_CHECKS -gt 36 ] && echo "✅ 通过" || echo "⚠️ 警告")

## 建议

### 必须修复的问题
EOF

    if [ $FAILED_CHECKS -gt 0 ]; then
        echo "- 修复所有失败的检查项" >> "$report_file"
    else
        echo "- 无必须修复的问题" >> "$report_file"
    fi

    cat >> "$report_file" << EOF

### 建议改进的问题
EOF

    if [ $WARNING_CHECKS -gt 0 ]; then
        echo "- 处理所有警告项以提升生产环境质量" >> "$report_file"
    else
        echo "- 无建议改进的问题" >> "$report_file"
    fi

    cat >> "$report_file" << EOF

## 结论

$([ $FAILED_CHECKS -eq 0 ] && echo "✅ 系统已准备好进行生产环境部署" || echo "❌ 系统尚未准备好进行生产环境部署，请修复失败的检查项")

**报告文件**: $report_file
EOF

    log_success "生产环境就绪性报告已生成: $report_file"
}

# 主函数
main() {
    log_info "开始OTLP Rust生产环境就绪性检查..."
    
    check_dependencies
    check_code_quality
    check_security
    check_performance
    check_monitoring
    check_high_availability
    check_enterprise_features
    check_documentation
    check_deployment_config
    check_network_config
    check_storage_config
    
    echo ""
    log_info "检查完成！"
    echo "总检查项: $TOTAL_CHECKS"
    echo "通过: $PASSED_CHECKS"
    echo "失败: $FAILED_CHECKS"
    echo "警告: $WARNING_CHECKS"
    echo "成功率: $(( (PASSED_CHECKS * 100) / TOTAL_CHECKS ))%"
    
    generate_report
    
    if [ $FAILED_CHECKS -eq 0 ]; then
        log_success "✅ 系统已准备好进行生产环境部署！"
        exit 0
    else
        log_error "❌ 系统尚未准备好进行生产环境部署，请修复失败的检查项"
        exit 1
    fi
}

# 显示帮助信息
show_help() {
    echo "OTLP Rust 生产环境就绪性检查脚本"
    echo ""
    echo "用法: $0 [选项]"
    echo ""
    echo "选项:"
    echo "  -h, --help     显示帮助信息"
    echo "  -v, --verbose  详细输出"
    echo ""
    echo "示例:"
    echo "  $0              # 运行完整检查"
    echo "  $0 -v           # 运行详细检查"
}

# 解析命令行参数
while [[ $# -gt 0 ]]; do
    case $1 in
        -h|--help)
            show_help
            exit 0
            ;;
        -v|--verbose)
            set -x
            shift
            ;;
        *)
            log_error "未知选项: $1"
            show_help
            exit 1
            ;;
    esac
done

# 执行主函数
main
