#!/bin/bash
# PostgreSQL All-in-One 性能监控脚本
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
║     PostgreSQL All-in-One 性能监控工具                        ║
║                                                              ║
╚══════════════════════════════════════════════════════════════╝
EOF
    echo ""
    echo "  监控时间: $(date '+%Y-%m-%d %H:%M:%S')"
    echo ""
}

# 检查Pod状态
check_pod_status() {
    log_section "1. Pod 状态"
    
    kubectl get pods -n postgresql-all-in-one -o wide
}

# 检查资源使用
check_resource_usage() {
    log_section "2. 资源使用情况"
    
    if kubectl top pods -n postgresql-all-in-one &> /dev/null; then
        kubectl top pods -n postgresql-all-in-one
        
        echo ""
        log_info "节点资源使用:"
        kubectl top nodes
    else
        log_warning "无法获取资源使用信息（需要安装 metrics-server）"
        log_info "安装 metrics-server: kubectl apply -f https://github.com/kubernetes-sigs/metrics-server/releases/latest/download/components.yaml"
    fi
}

# 检查服务状态
check_service_status() {
    log_section "3. 服务状态"
    
    kubectl get svc -n postgresql-all-in-one
    
    echo ""
    log_info "端点状态:"
    kubectl get endpoints -n postgresql-all-in-one
}

# 检查存储使用
check_storage_usage() {
    log_section "4. 存储使用情况"
    
    log_info "PersistentVolumeClaims:"
    kubectl get pvc -n postgresql-all-in-one
    
    echo ""
    log_info "PersistentVolumes:"
    kubectl get pv | grep postgresql-all-in-one || log_info "未找到相关 PV"
}

# 检查PostgreSQL性能
check_postgresql_performance() {
    log_section "5. PostgreSQL 性能指标"
    
    local pod=$(kubectl get pods -n postgresql-all-in-one -l app=postgresql -o jsonpath='{.items[0].metadata.name}' 2>/dev/null)
    
    if [ -z "$pod" ]; then
        log_warning "未找到 PostgreSQL Pod"
        return 1
    fi
    
    log_info "数据库连接数:"
    kubectl exec -n postgresql-all-in-one "$pod" -- \
        psql -U postgres -t -c "SELECT count(*) as connections FROM pg_stat_activity;" 2>/dev/null || \
        log_warning "无法获取连接数"
    
    echo ""
    log_info "数据库大小:"
    kubectl exec -n postgresql-all-in-one "$pod" -- \
        psql -U postgres -c "SELECT datname, pg_size_pretty(pg_database_size(datname)) as size FROM pg_database ORDER BY pg_database_size(datname) DESC;" 2>/dev/null || \
        log_warning "无法获取数据库大小"
    
    echo ""
    log_info "表大小 (Top 10):"
    kubectl exec -n postgresql-all-in-one "$pod" -- \
        psql -U postgres -d allinone -c "SELECT schemaname, tablename, pg_size_pretty(pg_total_relation_size(schemaname||'.'||tablename)) AS size FROM pg_tables WHERE schemaname NOT IN ('pg_catalog', 'information_schema') ORDER BY pg_total_relation_size(schemaname||'.'||tablename) DESC LIMIT 10;" 2>/dev/null || \
        log_warning "无法获取表大小"
    
    echo ""
    log_info "缓存命中率:"
    kubectl exec -n postgresql-all-in-one "$pod" -- \
        psql -U postgres -t -c "SELECT round(sum(blks_hit)*100/sum(blks_hit+blks_read), 2) as cache_hit_ratio FROM pg_stat_database WHERE datname='allinone';" 2>/dev/null || \
        log_warning "无法获取缓存命中率"
    
    echo ""
    log_info "慢查询 (Top 5):"
    kubectl exec -n postgresql-all-in-one "$pod" -- \
        psql -U postgres -d allinone -c "SELECT query, calls, total_time, mean_time FROM pg_stat_statements ORDER BY mean_time DESC LIMIT 5;" 2>/dev/null || \
        log_warning "pg_stat_statements 未启用"
    
    echo ""
    log_info "索引使用情况:"
    kubectl exec -n postgresql-all-in-one "$pod" -- \
        psql -U postgres -d allinone -c "SELECT schemaname, tablename, indexname, idx_scan, idx_tup_read, idx_tup_fetch FROM pg_stat_user_indexes ORDER BY idx_scan DESC LIMIT 10;" 2>/dev/null || \
        log_warning "无法获取索引使用情况"
}

# 检查Redis性能
check_redis_performance() {
    log_section "6. Redis 性能指标"
    
    local pod=$(kubectl get pods -n postgresql-all-in-one -l app=redis -o jsonpath='{.items[0].metadata.name}' 2>/dev/null)
    
    if [ -z "$pod" ]; then
        log_warning "未找到 Redis Pod"
        return 1
    fi
    
    log_info "Redis 信息:"
    kubectl exec -n postgresql-all-in-one "$pod" -- redis-cli INFO stats 2>/dev/null | grep -E "^(total_commands_processed|instantaneous_ops_per_sec|total_connections_received|connected_clients|used_memory_human|keyspace)" || \
        log_warning "无法获取 Redis 信息"
    
    echo ""
    log_info "Redis 命中率:"
    local hits=$(kubectl exec -n postgresql-all-in-one "$pod" -- redis-cli INFO stats 2>/dev/null | grep keyspace_hits | cut -d: -f2 | tr -d '\r')
    local misses=$(kubectl exec -n postgresql-all-in-one "$pod" -- redis-cli INFO stats 2>/dev/null | grep keyspace_misses | cut -d: -f2 | tr -d '\r')
    
    if [ -n "$hits" ] && [ -n "$misses" ]; then
        local total=$((hits + misses))
        if [ $total -gt 0 ]; then
            local hit_rate=$((hits * 100 / total))
            echo "  命中率: ${hit_rate}%"
            
            if [ $hit_rate -ge 95 ]; then
                log_success "缓存命中率优秀 (>= 95%)"
            elif [ $hit_rate -ge 80 ]; then
                log_info "缓存命中率良好 (>= 80%)"
            else
                log_warning "缓存命中率偏低 (< 80%)，建议优化缓存策略"
            fi
        fi
    fi
}

# 检查网络性能
check_network_performance() {
    log_section "7. 网络性能"
    
    log_info "Service 端点:"
    kubectl get endpoints -n postgresql-all-in-one
    
    echo ""
    log_info "网络策略:"
    if kubectl get networkpolicy -n postgresql-all-in-one &> /dev/null; then
        kubectl get networkpolicy -n postgresql-all-in-one
    else
        log_info "未配置网络策略"
    fi
}

# 检查最近日志
check_recent_logs() {
    log_section "8. 最近日志 (最后20行)"
    
    local components="postgresql redis prometheus grafana"
    
    for component in $components; do
        local pod=$(kubectl get pods -n postgresql-all-in-one -l app=$component -o jsonpath='{.items[0].metadata.name}' 2>/dev/null)
        
        if [ -n "$pod" ]; then
            echo ""
            log_info "$component 日志:"
            kubectl logs -n postgresql-all-in-one "$pod" --tail=20 2>/dev/null || log_warning "无法获取日志"
        fi
    done
}

# 检查最近事件
check_recent_events() {
    log_section "9. 最近事件"
    
    log_info "Warning 和 Error 事件 (最近15条):"
    kubectl get events -n postgresql-all-in-one \
        --sort-by='.lastTimestamp' \
        --field-selector type!=Normal \
        2>/dev/null | tail -15 || log_info "没有异常事件"
}

# 生成性能报告
generate_performance_report() {
    log_section "10. 性能报告摘要"
    
    local report_file="/tmp/postgresql-all-in-one-performance-$(date +%Y%m%d_%H%M%S).txt"
    
    {
        echo "PostgreSQL All-in-One 性能报告"
        echo "生成时间: $(date '+%Y-%m-%d %H:%M:%S')"
        echo "================================================"
        echo ""
        
        echo "系统概况:"
        kubectl get pods -n postgresql-all-in-one -o wide
        echo ""
        
        echo "资源使用:"
        kubectl top pods -n postgresql-all-in-one 2>/dev/null || echo "metrics-server 未安装"
        echo ""
        
        echo "存储使用:"
        kubectl get pvc -n postgresql-all-in-one
        echo ""
        
        echo "服务状态:"
        kubectl get svc -n postgresql-all-in-one
        echo ""
        
    } > "$report_file"
    
    log_success "性能报告已生成: $report_file"
    
    if [ "$SHOW_REPORT" = "true" ]; then
        cat "$report_file"
    fi
}

# 持续监控模式
continuous_monitor() {
    log_info "持续监控模式 (按 Ctrl+C 退出)"
    log_info "刷新间隔: ${INTERVAL}秒"
    echo ""
    
    while true; do
        clear
        print_banner
        check_resource_usage
        check_postgresql_performance
        check_redis_performance
        
        echo ""
        log_info "下次刷新: ${INTERVAL}秒后..."
        sleep "$INTERVAL"
    done
}

# 主函数
main() {
    # 默认参数
    INTERVAL=30
    SHOW_LOGS=false
    SHOW_EVENTS=false
    CONTINUOUS=false
    SHOW_REPORT=false
    
    # 解析命令行参数
    while [[ $# -gt 0 ]]; do
        case $1 in
            --continuous)
                CONTINUOUS=true
                shift
                ;;
            --interval)
                INTERVAL="$2"
                shift 2
                ;;
            --logs)
                SHOW_LOGS=true
                shift
                ;;
            --events)
                SHOW_EVENTS=true
                shift
                ;;
            --report)
                SHOW_REPORT=true
                shift
                ;;
            --help)
                cat << EOF
使用方法: $0 [选项]

选项:
  --continuous         持续监控模式
  --interval <秒>      持续监控刷新间隔（默认: 30秒）
  --logs              显示最近日志
  --events            显示最近事件
  --report            生成并显示性能报告
  --help              显示此帮助信息

示例:
  $0                           # 标准性能监控
  $0 --continuous              # 持续监控模式
  $0 --interval 10             # 10秒刷新间隔
  $0 --logs --events           # 包含日志和事件
  $0 --report                  # 生成性能报告

EOF
                exit 0
                ;;
            *)
                echo "未知选项: $1"
                echo "使用 --help 查看帮助信息"
                exit 1
                ;;
        esac
    done
    
    # 检查kubectl是否可用
    if ! command -v kubectl &> /dev/null; then
        echo "错误: kubectl 未安装或不在 PATH 中"
        exit 1
    fi
    
    # 检查集群连接
    if ! kubectl cluster-info &> /dev/null; then
        echo "错误: 无法连接到 Kubernetes 集群"
        exit 1
    fi
    
    # 执行监控
    if [ "$CONTINUOUS" = "true" ]; then
        continuous_monitor
    else
        print_banner
        check_pod_status
        check_resource_usage
        check_service_status
        check_storage_usage
        check_postgresql_performance
        check_redis_performance
        check_network_performance
        
        if [ "$SHOW_LOGS" = "true" ]; then
            check_recent_logs
        fi
        
        if [ "$SHOW_EVENTS" = "true" ]; then
            check_recent_events
        fi
        
        generate_performance_report
    fi
}

# 信号处理
trap 'echo ""; log_info "监控已停止"; exit 0' INT TERM

# 执行主函数
main "$@"

