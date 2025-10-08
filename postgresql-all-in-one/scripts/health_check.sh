#!/bin/bash
# PostgreSQL All-in-One 健康检查脚本
# 版本: 1.0.0
# 日期: 2025-10-08

set -e

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
NC='\033[0m' # No Color

# 日志函数
log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[✓]${NC} $1"
}

log_warning() {
    echo -e "${YELLOW}[!]${NC} $1"
}

log_error() {
    echo -e "${RED}[✗]${NC} $1"
}

log_section() {
    echo ""
    echo -e "${CYAN}═══════════════════════════════════════════════════════════════${NC}"
    echo -e "${CYAN}  $1${NC}"
    echo -e "${CYAN}═══════════════════════════════════════════════════════════════${NC}"
    echo ""
}

# 打印横幅
print_banner() {
    cat << "EOF"
╔══════════════════════════════════════════════════════════════╗
║                                                              ║
║     PostgreSQL All-in-One 健康检查工具                      ║
║                                                              ║
╚══════════════════════════════════════════════════════════════╝
EOF
    echo ""
}

# 初始化统计
init_stats() {
    TOTAL_CHECKS=0
    PASSED_CHECKS=0
    FAILED_CHECKS=0
    WARNING_CHECKS=0
}

# 记录检查结果
record_check() {
    TOTAL_CHECKS=$((TOTAL_CHECKS + 1))
    case $1 in
        "pass")
            PASSED_CHECKS=$((PASSED_CHECKS + 1))
            ;;
        "fail")
            FAILED_CHECKS=$((FAILED_CHECKS + 1))
            ;;
        "warn")
            WARNING_CHECKS=$((WARNING_CHECKS + 1))
            ;;
    esac
}

# 检查命名空间
check_namespace() {
    log_section "1. 检查命名空间"
    
    if kubectl get namespace postgresql-all-in-one &> /dev/null; then
        log_success "命名空间 'postgresql-all-in-one' 存在"
        record_check "pass"
        
        # 显示命名空间标签
        local labels=$(kubectl get namespace postgresql-all-in-one -o jsonpath='{.metadata.labels}' | jq -r 'to_entries | map("\(.key)=\(.value)") | join(", ")' 2>/dev/null || echo "")
        if [ -n "$labels" ]; then
            echo "  标签: $labels"
        fi
    else
        log_error "命名空间 'postgresql-all-in-one' 不存在"
        record_check "fail"
        return 1
    fi
}

# 检查PostgreSQL
check_postgresql() {
    log_section "2. 检查 PostgreSQL"
    
    # 检查StatefulSet
    if kubectl get statefulset postgresql-all-in-one -n postgresql-all-in-one &> /dev/null; then
        local ready=$(kubectl get statefulset postgresql-all-in-one -n postgresql-all-in-one -o jsonpath='{.status.readyReplicas}')
        local desired=$(kubectl get statefulset postgresql-all-in-one -n postgresql-all-in-one -o jsonpath='{.status.replicas}')
        
        if [ "$ready" = "$desired" ] && [ "$ready" != "" ]; then
            log_success "PostgreSQL StatefulSet 运行正常 ($ready/$desired)"
            record_check "pass"
        else
            log_warning "PostgreSQL StatefulSet 不完全就绪 ($ready/$desired)"
            record_check "warn"
        fi
    else
        log_error "PostgreSQL StatefulSet 不存在"
        record_check "fail"
        return 1
    fi
    
    # 检查Pod状态
    log_info "检查 PostgreSQL Pod 状态..."
    local pod_status=$(kubectl get pods -n postgresql-all-in-one -l app=postgresql -o jsonpath='{.items[0].status.phase}' 2>/dev/null || echo "NotFound")
    
    case $pod_status in
        "Running")
            log_success "Pod 状态: Running"
            record_check "pass"
            ;;
        "Pending")
            log_warning "Pod 状态: Pending"
            record_check "warn"
            kubectl get pods -n postgresql-all-in-one -l app=postgresql
            ;;
        "Failed"|"CrashLoopBackOff")
            log_error "Pod 状态: $pod_status"
            record_check "fail"
            kubectl get pods -n postgresql-all-in-one -l app=postgresql
            ;;
        *)
            log_error "无法获取 Pod 状态"
            record_check "fail"
            ;;
    esac
    
    # 检查Service
    if kubectl get service postgresql-service -n postgresql-all-in-one &> /dev/null; then
        log_success "PostgreSQL Service 存在"
        record_check "pass"
        
        local service_ip=$(kubectl get service postgresql-service -n postgresql-all-in-one -o jsonpath='{.spec.clusterIP}')
        local service_port=$(kubectl get service postgresql-service -n postgresql-all-in-one -o jsonpath='{.spec.ports[0].port}')
        echo "  访问地址: $service_ip:$service_port"
    else
        log_error "PostgreSQL Service 不存在"
        record_check "fail"
    fi
    
    # 测试数据库连接
    if [ "$DETAILED_CHECK" = "true" ]; then
        log_info "测试数据库连接..."
        if kubectl exec -n postgresql-all-in-one statefulset/postgresql-all-in-one -- \
            psql -U postgres -c "SELECT version();" &> /dev/null; then
            log_success "数据库连接测试成功"
            record_check "pass"
        else
            log_error "数据库连接测试失败"
            record_check "fail"
        fi
    fi
}

# 检查Redis
check_redis() {
    log_section "3. 检查 Redis"
    
    # 检查Deployment
    if kubectl get deployment redis -n postgresql-all-in-one &> /dev/null; then
        local ready=$(kubectl get deployment redis -n postgresql-all-in-one -o jsonpath='{.status.readyReplicas}')
        local desired=$(kubectl get deployment redis -n postgresql-all-in-one -o jsonpath='{.status.replicas}')
        
        if [ "$ready" = "$desired" ] && [ "$ready" != "" ]; then
            log_success "Redis Deployment 运行正常 ($ready/$desired)"
            record_check "pass"
        else
            log_warning "Redis Deployment 不完全就绪 ($ready/$desired)"
            record_check "warn"
        fi
    else
        log_warning "Redis Deployment 不存在"
        record_check "warn"
        return 1
    fi
    
    # 检查Pod状态
    local pod_status=$(kubectl get pods -n postgresql-all-in-one -l app=redis -o jsonpath='{.items[0].status.phase}' 2>/dev/null || echo "NotFound")
    
    if [ "$pod_status" = "Running" ]; then
        log_success "Redis Pod 状态: Running"
        record_check "pass"
    else
        log_warning "Redis Pod 状态: $pod_status"
        record_check "warn"
    fi
    
    # 测试Redis连接
    if [ "$DETAILED_CHECK" = "true" ]; then
        log_info "测试 Redis 连接..."
        if kubectl exec -n postgresql-all-in-one deployment/redis -- redis-cli ping &> /dev/null; then
            log_success "Redis 连接测试成功"
            record_check "pass"
        else
            log_error "Redis 连接测试失败"
            record_check "fail"
        fi
    fi
}

# 检查Vector
check_vector() {
    log_section "4. 检查 Vector 数据管道"
    
    # 检查StatefulSet或Deployment
    if kubectl get statefulset vector -n postgresql-all-in-one &> /dev/null; then
        local ready=$(kubectl get statefulset vector -n postgresql-all-in-one -o jsonpath='{.status.readyReplicas}')
        local desired=$(kubectl get statefulset vector -n postgresql-all-in-one -o jsonpath='{.status.replicas}')
        
        if [ "$ready" = "$desired" ] && [ "$ready" != "" ]; then
            log_success "Vector StatefulSet 运行正常 ($ready/$desired)"
            record_check "pass"
        else
            log_warning "Vector StatefulSet 不完全就绪 ($ready/$desired)"
            record_check "warn"
        fi
    elif kubectl get deployment vector -n postgresql-all-in-one &> /dev/null; then
        local ready=$(kubectl get deployment vector -n postgresql-all-in-one -o jsonpath='{.status.readyReplicas}')
        local desired=$(kubectl get deployment vector -n postgresql-all-in-one -o jsonpath='{.status.replicas}')
        
        if [ "$ready" = "$desired" ] && [ "$ready" != "" ]; then
            log_success "Vector Deployment 运行正常 ($ready/$desired)"
            record_check "pass"
        else
            log_warning "Vector Deployment 不完全就绪 ($ready/$desired)"
            record_check "warn"
        fi
    else
        log_warning "Vector 未部署（可选组件）"
        record_check "warn"
    fi
}

# 检查监控系统
check_monitoring() {
    log_section "5. 检查监控系统"
    
    # 检查Prometheus
    log_info "检查 Prometheus..."
    if kubectl get deployment prometheus -n postgresql-all-in-one &> /dev/null; then
        local ready=$(kubectl get deployment prometheus -n postgresql-all-in-one -o jsonpath='{.status.readyReplicas}')
        local desired=$(kubectl get deployment prometheus -n postgresql-all-in-one -o jsonpath='{.status.replicas}')
        
        if [ "$ready" = "$desired" ] && [ "$ready" != "" ]; then
            log_success "Prometheus 运行正常 ($ready/$desired)"
            record_check "pass"
        else
            log_warning "Prometheus 不完全就绪 ($ready/$desired)"
            record_check "warn"
        fi
    else
        log_warning "Prometheus 未部署"
        record_check "warn"
    fi
    
    # 检查Grafana
    log_info "检查 Grafana..."
    if kubectl get deployment grafana -n postgresql-all-in-one &> /dev/null; then
        local ready=$(kubectl get deployment grafana -n postgresql-all-in-one -o jsonpath='{.status.readyReplicas}')
        local desired=$(kubectl get deployment grafana -n postgresql-all-in-one -o jsonpath='{.status.replicas}')
        
        if [ "$ready" = "$desired" ] && [ "$ready" != "" ]; then
            log_success "Grafana 运行正常 ($ready/$desired)"
            record_check "pass"
            
            # 获取访问地址
            local grafana_port=$(kubectl get svc grafana -n postgresql-all-in-one -o jsonpath='{.spec.ports[0].nodePort}' 2>/dev/null || echo "3000")
            echo "  访问地址: http://localhost:$grafana_port"
        else
            log_warning "Grafana 不完全就绪 ($ready/$desired)"
            record_check "warn"
        fi
    else
        log_warning "Grafana 未部署"
        record_check "warn"
    fi
}

# 检查资源使用
check_resources() {
    log_section "6. 检查资源使用情况"
    
    log_info "Pod 资源使用:"
    if command -v kubectl &> /dev/null && kubectl top pods -n postgresql-all-in-one &> /dev/null; then
        kubectl top pods -n postgresql-all-in-one
        log_success "资源使用信息获取成功"
        record_check "pass"
    else
        log_warning "无法获取资源使用信息（需要安装 metrics-server）"
        record_check "warn"
    fi
    
    echo ""
    log_info "存储使用情况:"
    kubectl get pvc -n postgresql-all-in-one 2>/dev/null || log_warning "未找到 PVC"
}

# 检查网络连接
check_networking() {
    log_section "7. 检查网络连接"
    
    log_info "Services:"
    kubectl get svc -n postgresql-all-in-one
    
    echo ""
    log_info "Ingress:"
    if kubectl get ingress -n postgresql-all-in-one &> /dev/null; then
        kubectl get ingress -n postgresql-all-in-one
        log_success "Ingress 配置存在"
        record_check "pass"
    else
        log_warning "Ingress 未配置"
        record_check "warn"
    fi
}

# 检查最近事件
check_events() {
    log_section "8. 检查最近事件"
    
    log_info "最近的事件 (最新10条):"
    kubectl get events -n postgresql-all-in-one \
        --sort-by='.lastTimestamp' \
        --field-selector type!=Normal \
        2>/dev/null | tail -10 || log_info "没有异常事件"
}

# 显示汇总
show_summary() {
    log_section "健康检查汇总"
    
    echo ""
    echo "  总检查项: $TOTAL_CHECKS"
    echo -e "  ${GREEN}通过: $PASSED_CHECKS${NC}"
    echo -e "  ${YELLOW}警告: $WARNING_CHECKS${NC}"
    echo -e "  ${RED}失败: $FAILED_CHECKS${NC}"
    echo ""
    
    # 计算健康分数
    local health_score=0
    if [ $TOTAL_CHECKS -gt 0 ]; then
        health_score=$((PASSED_CHECKS * 100 / TOTAL_CHECKS))
    fi
    
    echo -n "  整体健康度: "
    if [ $health_score -ge 90 ]; then
        echo -e "${GREEN}$health_score% - 优秀${NC}"
    elif [ $health_score -ge 70 ]; then
        echo -e "${YELLOW}$health_score% - 良好${NC}"
    elif [ $health_score -ge 50 ]; then
        echo -e "${YELLOW}$health_score% - 一般${NC}"
    else
        echo -e "${RED}$health_score% - 需要关注${NC}"
    fi
    echo ""
    
    if [ $FAILED_CHECKS -gt 0 ]; then
        log_error "发现 $FAILED_CHECKS 个失败项，请检查上述详细信息"
        return 1
    elif [ $WARNING_CHECKS -gt 0 ]; then
        log_warning "发现 $WARNING_CHECKS 个警告项，建议检查"
        return 0
    else
        log_success "所有检查项通过！系统运行正常 ✓"
        return 0
    fi
}

# 快速检查模式
quick_check() {
    print_banner
    init_stats
    
    log_info "快速健康检查..."
    echo ""
    
    # 只检查关键组件
    check_namespace
    
    # 检查关键Pod
    local critical_pods="postgresql redis"
    for pod_label in $critical_pods; do
        if kubectl get pods -n postgresql-all-in-one -l app=$pod_label -o jsonpath='{.items[0].status.phase}' 2>/dev/null | grep -q "Running"; then
            log_success "$pod_label 运行正常"
            record_check "pass"
        else
            log_error "$pod_label 运行异常"
            record_check "fail"
        fi
    done
    
    echo ""
    show_summary
}

# 完整检查模式
full_check() {
    print_banner
    init_stats
    
    check_namespace
    check_postgresql
    check_redis
    check_vector
    check_monitoring
    check_resources
    check_networking
    
    if [ "$SHOW_EVENTS" = "true" ]; then
        check_events
    fi
    
    show_summary
}

# 主函数
main() {
    # 解析命令行参数
    while [[ $# -gt 0 ]]; do
        case $1 in
            --quick)
                QUICK_MODE=true
                shift
                ;;
            --detailed)
                DETAILED_CHECK=true
                shift
                ;;
            --events)
                SHOW_EVENTS=true
                shift
                ;;
            --help)
                cat << EOF
使用方法: $0 [选项]

选项:
  --quick      快速检查模式（只检查关键组件）
  --detailed   详细检查模式（包含连接测试）
  --events     显示最近事件
  --help       显示此帮助信息

示例:
  $0                      # 标准健康检查
  $0 --quick              # 快速检查
  $0 --detailed --events  # 详细检查并显示事件

EOF
                exit 0
                ;;
            *)
                log_error "未知选项: $1"
                log_info "使用 --help 查看帮助信息"
                exit 1
                ;;
        esac
    done
    
    # 检查kubectl是否可用
    if ! command -v kubectl &> /dev/null; then
        log_error "kubectl 未安装或不在 PATH 中"
        exit 1
    fi
    
    # 检查集群连接
    if ! kubectl cluster-info &> /dev/null; then
        log_error "无法连接到 Kubernetes 集群"
        exit 1
    fi
    
    # 执行检查
    if [ "$QUICK_MODE" = "true" ]; then
        quick_check
    else
        full_check
    fi
}

# 执行主函数
main "$@"

