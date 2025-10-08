#!/bin/bash
# PostgreSQL All-in-One 恢复脚本
# 版本: 1.0.0
# 日期: 2025-10-08

set -e

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

# 打印横幅
print_banner() {
    cat << "EOF"
╔══════════════════════════════════════════════════════════════╗
║                                                              ║
║     PostgreSQL All-in-One 恢复工具                            ║
║                                                              ║
╚══════════════════════════════════════════════════════════════╝
EOF
    echo ""
    echo "  恢复时间: $(date '+%Y-%m-%d %H:%M:%S')"
    echo ""
}

# 确认恢复操作
confirm_restore() {
    log_warning "⚠️  警告: 恢复操作将覆盖现有数据！"
    echo ""
    
    if [ "$FORCE_RESTORE" = "true" ]; then
        log_warning "强制恢复模式已启用，跳过确认"
        return 0
    fi
    
    read -p "是否继续？(yes/no): " -r
    echo ""
    
    if [[ ! $REPLY =~ ^[Yy][Ee][Ss]$ ]]; then
        log_info "恢复已取消"
        exit 0
    fi
}

# 检查环境
check_environment() {
    log_info "检查恢复环境..."
    
    # 检查kubectl
    if ! command -v kubectl &> /dev/null; then
        log_error "kubectl 未安装"
        exit 1
    fi
    
    # 检查集群连接
    if ! kubectl cluster-info &> /dev/null; then
        log_error "无法连接到 Kubernetes 集群"
        exit 1
    fi
    
    # 检查命名空间
    if ! kubectl get namespace postgresql-all-in-one &> /dev/null; then
        log_error "命名空间 'postgresql-all-in-one' 不存在"
        exit 1
    fi
    
    # 检查备份目录
    if [ ! -d "$BACKUP_DIR" ]; then
        log_error "备份目录不存在: $BACKUP_DIR"
        exit 1
    fi
    
    log_success "环境检查通过"
    echo ""
}

# 列出可用备份
list_backups() {
    log_info "可用的备份:"
    echo ""
    
    log_info "PostgreSQL 备份:"
    find "$BACKUP_DIR" -type f \( -name "postgresql_backup_*.sql" -o -name "postgresql_backup_*.sql.gz" \) \
        -exec ls -lh {} \; | awk '{print "  " $9 " (" $5 ", " $6 " " $7 ")"}' 2>/dev/null || \
        echo "  未找到备份"
    
    echo ""
    log_info "Redis 备份:"
    find "$BACKUP_DIR" -type f -name "redis_backup_*.rdb" \
        -exec ls -lh {} \; | awk '{print "  " $9 " (" $5 ", " $6 " " $7 ")"}' 2>/dev/null || \
        echo "  未找到备份"
    
    echo ""
    log_info "配置备份:"
    find "$BACKUP_DIR" -type f -name "configs_*.tar.gz" \
        -exec ls -lh {} \; | awk '{print "  " $9 " (" $5 ", " $6 " " $7 ")"}' 2>/dev/null || \
        echo "  未找到备份"
    
    echo ""
}

# 恢复PostgreSQL
restore_postgresql() {
    log_info "恢复 PostgreSQL 数据库..."
    
    local pod=$(kubectl get pods -n postgresql-all-in-one -l app=postgresql -o jsonpath='{.items[0].metadata.name}' 2>/dev/null)
    
    if [ -z "$pod" ]; then
        log_error "未找到 PostgreSQL Pod"
        return 1
    fi
    
    # 查找最新的备份文件
    if [ -z "$POSTGRESQL_BACKUP_FILE" ]; then
        POSTGRESQL_BACKUP_FILE=$(find "$BACKUP_DIR" -type f \( -name "postgresql_backup_*.sql" -o -name "postgresql_backup_*.sql.gz" \) | sort -r | head -1)
    fi
    
    if [ -z "$POSTGRESQL_BACKUP_FILE" ]; then
        log_error "未找到 PostgreSQL 备份文件"
        return 1
    fi
    
    log_info "  使用备份: $(basename $POSTGRESQL_BACKUP_FILE)"
    
    # 解压缩（如果需要）
    local sql_file="$POSTGRESQL_BACKUP_FILE"
    if [[ "$POSTGRESQL_BACKUP_FILE" == *.gz ]]; then
        log_info "  解压缩备份文件..."
        sql_file="${POSTGRESQL_BACKUP_FILE%.gz}"
        gunzip -c "$POSTGRESQL_BACKUP_FILE" > "$sql_file"
    fi
    
    # 恢复数据库
    log_info "  执行恢复..."
    kubectl exec -i -n postgresql-all-in-one "$pod" -- \
        psql -U postgres < "$sql_file"
    
    # 清理临时文件
    if [[ "$POSTGRESQL_BACKUP_FILE" == *.gz ]]; then
        rm -f "$sql_file"
    fi
    
    log_success "PostgreSQL 恢复完成"
    echo ""
}

# 恢复Redis
restore_redis() {
    log_info "恢复 Redis 数据..."
    
    local pod=$(kubectl get pods -n postgresql-all-in-one -l app=redis -o jsonpath='{.items[0].metadata.name}' 2>/dev/null)
    
    if [ -z "$pod" ]; then
        log_warning "未找到 Redis Pod，跳过恢复"
        return 0
    fi
    
    # 查找最新的备份文件
    if [ -z "$REDIS_BACKUP_FILE" ]; then
        REDIS_BACKUP_FILE=$(find "$BACKUP_DIR" -type f -name "redis_backup_*.rdb" | sort -r | head -1)
    fi
    
    if [ -z "$REDIS_BACKUP_FILE" ]; then
        log_warning "未找到 Redis 备份文件，跳过恢复"
        return 0
    fi
    
    log_info "  使用备份: $(basename $REDIS_BACKUP_FILE)"
    
    # 停止Redis写入
    log_info "  停止 Redis..."
    kubectl exec -n postgresql-all-in-one "$pod" -- redis-cli SHUTDOWN NOSAVE || true
    sleep 3
    
    # 复制备份文件
    log_info "  复制备份文件..."
    kubectl cp "$REDIS_BACKUP_FILE" "postgresql-all-in-one/$pod:/data/dump.rdb"
    
    # 重启Pod以加载数据
    log_info "  重启 Redis Pod..."
    kubectl delete pod "$pod" -n postgresql-all-in-one
    
    # 等待Pod重启
    log_info "  等待 Redis 就绪..."
    kubectl wait --for=condition=ready pod -l app=redis \
        --timeout=120s -n postgresql-all-in-one
    
    log_success "Redis 恢复完成"
    echo ""
}

# 恢复配置文件
restore_configs() {
    log_info "恢复配置文件..."
    
    # 查找最新的配置备份
    if [ -z "$CONFIG_BACKUP_FILE" ]; then
        CONFIG_BACKUP_FILE=$(find "$BACKUP_DIR" -type f -name "configs_*.tar.gz" | sort -r | head -1)
    fi
    
    if [ -z "$CONFIG_BACKUP_FILE" ]; then
        log_warning "未找到配置备份文件，跳过恢复"
        return 0
    fi
    
    log_info "  使用备份: $(basename $CONFIG_BACKUP_FILE)"
    
    # 解压配置备份
    local temp_dir=$(mktemp -d)
    tar -xzf "$CONFIG_BACKUP_FILE" -C "$temp_dir"
    
    local config_dir=$(find "$temp_dir" -type d -name "configs_*" | head -1)
    
    if [ -z "$config_dir" ]; then
        log_error "无效的配置备份文件"
        rm -rf "$temp_dir"
        return 1
    fi
    
    # 恢复ConfigMaps
    if [ -f "$config_dir/configmaps.yaml" ]; then
        log_info "  恢复 ConfigMaps..."
        kubectl apply -f "$config_dir/configmaps.yaml" 2>/dev/null || true
    fi
    
    # 恢复Secrets
    if [ -f "$config_dir/secrets.yaml" ]; then
        log_info "  恢复 Secrets..."
        kubectl apply -f "$config_dir/secrets.yaml" 2>/dev/null || true
    fi
    
    # 恢复Services
    if [ -f "$config_dir/services.yaml" ]; then
        log_info "  恢复 Services..."
        kubectl apply -f "$config_dir/services.yaml" 2>/dev/null || true
    fi
    
    # 清理临时目录
    rm -rf "$temp_dir"
    
    log_success "配置文件恢复完成"
    echo ""
}

# 恢复监控数据
restore_monitoring() {
    log_info "恢复监控数据..."
    
    # 恢复Prometheus数据
    local prom_backup=$(find "$BACKUP_DIR" -type f -name "prometheus_data_*.tar.gz" | sort -r | head -1)
    
    if [ -n "$prom_backup" ]; then
        local prom_pod=$(kubectl get pods -n postgresql-all-in-one -l app=prometheus -o jsonpath='{.items[0].metadata.name}' 2>/dev/null)
        
        if [ -n "$prom_pod" ]; then
            log_info "  恢复 Prometheus 数据..."
            log_info "    使用备份: $(basename $prom_backup)"
            
            kubectl cp "$prom_backup" "postgresql-all-in-one/$prom_pod:/tmp/prometheus_backup.tar.gz"
            kubectl exec -n postgresql-all-in-one "$prom_pod" -- \
                tar -xzf /tmp/prometheus_backup.tar.gz -C /prometheus 2>/dev/null || true
            
            log_success "  Prometheus 数据恢复完成"
        fi
    else
        log_warning "未找到 Prometheus 备份，跳过恢复"
    fi
    
    # 恢复Grafana数据
    local grafana_backup=$(find "$BACKUP_DIR" -type f -name "grafana_data_*.tar.gz" | sort -r | head -1)
    
    if [ -n "$grafana_backup" ]; then
        local grafana_pod=$(kubectl get pods -n postgresql-all-in-one -l app=grafana -o jsonpath='{.items[0].metadata.name}' 2>/dev/null)
        
        if [ -n "$grafana_pod" ]; then
            log_info "  恢复 Grafana 数据..."
            log_info "    使用备份: $(basename $grafana_backup)"
            
            kubectl cp "$grafana_backup" "postgresql-all-in-one/$grafana_pod:/tmp/grafana_backup.tar.gz"
            kubectl exec -n postgresql-all-in-one "$grafana_pod" -- \
                tar -xzf /tmp/grafana_backup.tar.gz -C /var/lib/grafana 2>/dev/null || true
            
            # 重启Grafana以加载数据
            kubectl delete pod "$grafana_pod" -n postgresql-all-in-one
            
            log_success "  Grafana 数据恢复完成"
        fi
    else
        log_warning "未找到 Grafana 备份，跳过恢复"
    fi
    
    echo ""
}

# 验证恢复
verify_restore() {
    log_info "验证恢复结果..."
    
    # 检查PostgreSQL
    local pg_pod=$(kubectl get pods -n postgresql-all-in-one -l app=postgresql -o jsonpath='{.items[0].metadata.name}' 2>/dev/null)
    if [ -n "$pg_pod" ]; then
        if kubectl exec -n postgresql-all-in-one "$pg_pod" -- \
            psql -U postgres -c "SELECT version();" &> /dev/null; then
            log_success "PostgreSQL 连接正常"
        else
            log_error "PostgreSQL 连接失败"
        fi
    fi
    
    # 检查Redis
    local redis_pod=$(kubectl get pods -n postgresql-all-in-one -l app=redis -o jsonpath='{.items[0].metadata.name}' 2>/dev/null)
    if [ -n "$redis_pod" ]; then
        if kubectl exec -n postgresql-all-in-one "$redis_pod" -- \
            redis-cli ping &> /dev/null; then
            log_success "Redis 连接正常"
        else
            log_warning "Redis 连接失败"
        fi
    fi
    
    echo ""
}

# 显示恢复摘要
show_summary() {
    echo ""
    cat << "EOF"
╔══════════════════════════════════════════════════════════════╗
║                    ✅ 恢复完成！                             ║
╚══════════════════════════════════════════════════════════════╝
EOF
    echo ""
    
    log_success "数据恢复成功完成"
    echo ""
    
    log_info "恢复统计:"
    echo "  备份目录: $BACKUP_DIR"
    
    if [ -n "$POSTGRESQL_BACKUP_FILE" ]; then
        echo "  PostgreSQL: $(basename $POSTGRESQL_BACKUP_FILE)"
    fi
    
    if [ -n "$REDIS_BACKUP_FILE" ]; then
        echo "  Redis: $(basename $REDIS_BACKUP_FILE)"
    fi
    
    if [ -n "$CONFIG_BACKUP_FILE" ]; then
        echo "  配置文件: $(basename $CONFIG_BACKUP_FILE)"
    fi
    
    echo ""
    
    log_info "后续步骤:"
    echo "  1. 验证数据完整性"
    echo "  2. 检查应用程序连接"
    echo "  3. 运行健康检查: ./health_check.sh"
    echo "  4. 检查日志: kubectl logs -n postgresql-all-in-one <pod-name>"
    echo ""
}

# 主函数
main() {
    # 默认参数
    BACKUP_DIR="./backups"
    FORCE_RESTORE=false
    RESTORE_ALL=true
    RESTORE_POSTGRESQL=false
    RESTORE_REDIS=false
    RESTORE_CONFIGS=false
    RESTORE_MONITORING=false
    LIST_ONLY=false
    
    # 解析命令行参数
    while [[ $# -gt 0 ]]; do
        case $1 in
            --backup-dir)
                BACKUP_DIR="$2"
                shift 2
                ;;
            --postgresql-backup)
                POSTGRESQL_BACKUP_FILE="$2"
                RESTORE_ALL=false
                RESTORE_POSTGRESQL=true
                shift 2
                ;;
            --redis-backup)
                REDIS_BACKUP_FILE="$2"
                RESTORE_ALL=false
                RESTORE_REDIS=true
                shift 2
                ;;
            --config-backup)
                CONFIG_BACKUP_FILE="$2"
                RESTORE_ALL=false
                RESTORE_CONFIGS=true
                shift 2
                ;;
            --postgresql)
                RESTORE_ALL=false
                RESTORE_POSTGRESQL=true
                shift
                ;;
            --redis)
                RESTORE_ALL=false
                RESTORE_REDIS=true
                shift
                ;;
            --configs)
                RESTORE_ALL=false
                RESTORE_CONFIGS=true
                shift
                ;;
            --monitoring)
                RESTORE_ALL=false
                RESTORE_MONITORING=true
                shift
                ;;
            --list)
                LIST_ONLY=true
                shift
                ;;
            --force)
                FORCE_RESTORE=true
                shift
                ;;
            --help)
                cat << EOF
使用方法: $0 [选项]

选项:
  --backup-dir <目录>              备份目录（默认: ./backups）
  --postgresql-backup <文件>       指定 PostgreSQL 备份文件
  --redis-backup <文件>            指定 Redis 备份文件
  --config-backup <文件>           指定配置备份文件
  --postgresql                     只恢复 PostgreSQL
  --redis                          只恢复 Redis
  --configs                        只恢复配置文件
  --monitoring                     只恢复监控数据
  --list                           列出可用备份
  --force                          跳过确认直接恢复
  --help                           显示此帮助信息

示例:
  $0 --list                                # 列出可用备份
  $0 --backup-dir /mnt/backups             # 指定备份目录
  $0 --postgresql                          # 只恢复 PostgreSQL
  $0 --postgresql-backup backup.sql        # 指定备份文件
  $0 --force                               # 强制恢复（跳过确认）

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
    
    # 转换为绝对路径
    BACKUP_DIR=$(realpath "$BACKUP_DIR")
    
    print_banner
    check_environment
    
    # 列表模式
    if [ "$LIST_ONLY" = "true" ]; then
        list_backups
        exit 0
    fi
    
    # 确认恢复
    confirm_restore
    
    # 执行恢复
    if [ "$RESTORE_ALL" = "true" ] || [ "$RESTORE_POSTGRESQL" = "true" ]; then
        restore_postgresql
    fi
    
    if [ "$RESTORE_ALL" = "true" ] || [ "$RESTORE_REDIS" = "true" ]; then
        restore_redis
    fi
    
    if [ "$RESTORE_ALL" = "true" ] || [ "$RESTORE_CONFIGS" = "true" ]; then
        restore_configs
    fi
    
    if [ "$RESTORE_ALL" = "true" ] || [ "$RESTORE_MONITORING" = "true" ]; then
        restore_monitoring
    fi
    
    verify_restore
    show_summary
}

# 错误处理
trap 'log_error "恢复过程中发生错误，退出代码: $?"; exit 1' ERR

# 执行主函数
main "$@"

