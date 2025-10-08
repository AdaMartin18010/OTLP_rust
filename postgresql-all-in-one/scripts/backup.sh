#!/bin/bash
# PostgreSQL All-in-One 备份脚本
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
║     PostgreSQL All-in-One 备份工具                            ║
║                                                              ║
╚══════════════════════════════════════════════════════════════╝
EOF
    echo ""
    echo "  备份时间: $(date '+%Y-%m-%d %H:%M:%S')"
    echo ""
}

# 检查环境
check_environment() {
    log_info "检查备份环境..."
    
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
        log_info "创建备份目录: $BACKUP_DIR"
        mkdir -p "$BACKUP_DIR"
    fi
    
    log_success "环境检查通过"
    echo ""
}

# 备份PostgreSQL
backup_postgresql() {
    log_info "备份 PostgreSQL 数据库..."
    
    local pod=$(kubectl get pods -n postgresql-all-in-one -l app=postgresql -o jsonpath='{.items[0].metadata.name}' 2>/dev/null)
    
    if [ -z "$pod" ]; then
        log_error "未找到 PostgreSQL Pod"
        return 1
    fi
    
    local backup_file="$BACKUP_DIR/postgresql_backup_$(date +%Y%m%d_%H%M%S).sql"
    
    # 执行pg_dump
    log_info "  执行 pg_dump..."
    kubectl exec -n postgresql-all-in-one "$pod" -- \
        pg_dumpall -U postgres > "$backup_file" 2>/dev/null
    
    if [ $? -eq 0 ]; then
        local file_size=$(du -h "$backup_file" | cut -f1)
        log_success "PostgreSQL 备份完成: $backup_file ($file_size)"
        
        # 压缩备份文件
        if [ "$COMPRESS" = "true" ]; then
            log_info "  压缩备份文件..."
            gzip "$backup_file"
            backup_file="${backup_file}.gz"
            local compressed_size=$(du -h "$backup_file" | cut -f1)
            log_success "  压缩完成: $compressed_size"
        fi
        
        echo "$backup_file" >> "$BACKUP_DIR/.postgresql_backups"
    else
        log_error "PostgreSQL 备份失败"
        return 1
    fi
    
    echo ""
}

# 备份Redis
backup_redis() {
    log_info "备份 Redis 数据..."
    
    local pod=$(kubectl get pods -n postgresql-all-in-one -l app=redis -o jsonpath='{.items[0].metadata.name}' 2>/dev/null)
    
    if [ -z "$pod" ]; then
        log_warning "未找到 Redis Pod，跳过备份"
        return 0
    fi
    
    # 触发Redis保存
    log_info "  触发 Redis BGSAVE..."
    kubectl exec -n postgresql-all-in-one "$pod" -- redis-cli BGSAVE &> /dev/null
    
    # 等待保存完成
    local max_wait=60
    local waited=0
    while [ $waited -lt $max_wait ]; do
        if kubectl exec -n postgresql-all-in-one "$pod" -- redis-cli LASTSAVE &> /dev/null; then
            break
        fi
        sleep 1
        waited=$((waited + 1))
    done
    
    # 复制dump.rdb文件
    local backup_file="$BACKUP_DIR/redis_backup_$(date +%Y%m%d_%H%M%S).rdb"
    log_info "  复制 Redis 数据文件..."
    kubectl cp "postgresql-all-in-one/$pod:/data/dump.rdb" "$backup_file" 2>/dev/null
    
    if [ -f "$backup_file" ]; then
        local file_size=$(du -h "$backup_file" | cut -f1)
        log_success "Redis 备份完成: $backup_file ($file_size)"
        echo "$backup_file" >> "$BACKUP_DIR/.redis_backups"
    else
        log_warning "Redis 备份文件不存在，可能 Redis 为空"
    fi
    
    echo ""
}

# 备份配置文件
backup_configs() {
    log_info "备份配置文件..."
    
    local config_dir="$BACKUP_DIR/configs_$(date +%Y%m%d_%H%M%S)"
    mkdir -p "$config_dir"
    
    # 备份ConfigMaps
    log_info "  备份 ConfigMaps..."
    kubectl get configmap -n postgresql-all-in-one -o yaml > "$config_dir/configmaps.yaml"
    
    # 备份Secrets (注意: 这包含敏感信息)
    log_info "  备份 Secrets..."
    kubectl get secret -n postgresql-all-in-one -o yaml > "$config_dir/secrets.yaml"
    
    # 备份Services
    log_info "  备份 Services..."
    kubectl get svc -n postgresql-all-in-one -o yaml > "$config_dir/services.yaml"
    
    # 备份Deployments
    log_info "  备份 Deployments..."
    kubectl get deployment -n postgresql-all-in-one -o yaml > "$config_dir/deployments.yaml" 2>/dev/null || true
    
    # 备份StatefulSets
    log_info "  备份 StatefulSets..."
    kubectl get statefulset -n postgresql-all-in-one -o yaml > "$config_dir/statefulsets.yaml" 2>/dev/null || true
    
    # 备份PVCs
    log_info "  备份 PVCs..."
    kubectl get pvc -n postgresql-all-in-one -o yaml > "$config_dir/pvcs.yaml" 2>/dev/null || true
    
    # 压缩配置目录
    log_info "  压缩配置文件..."
    tar -czf "${config_dir}.tar.gz" -C "$BACKUP_DIR" "$(basename $config_dir)"
    rm -rf "$config_dir"
    
    local file_size=$(du -h "${config_dir}.tar.gz" | cut -f1)
    log_success "配置文件备份完成: ${config_dir}.tar.gz ($file_size)"
    
    echo ""
}

# 备份监控数据
backup_monitoring() {
    log_info "备份监控数据..."
    
    # 备份Prometheus数据
    local prom_pod=$(kubectl get pods -n postgresql-all-in-one -l app=prometheus -o jsonpath='{.items[0].metadata.name}' 2>/dev/null)
    
    if [ -n "$prom_pod" ]; then
        local prom_backup="$BACKUP_DIR/prometheus_data_$(date +%Y%m%d_%H%M%S).tar.gz"
        log_info "  备份 Prometheus 数据..."
        
        kubectl exec -n postgresql-all-in-one "$prom_pod" -- \
            tar -czf /tmp/prometheus_backup.tar.gz -C /prometheus . 2>/dev/null || true
        
        kubectl cp "postgresql-all-in-one/$prom_pod:/tmp/prometheus_backup.tar.gz" "$prom_backup" 2>/dev/null
        
        if [ -f "$prom_backup" ]; then
            local file_size=$(du -h "$prom_backup" | cut -f1)
            log_success "Prometheus 数据备份完成: $prom_backup ($file_size)"
        fi
    else
        log_warning "未找到 Prometheus Pod，跳过监控数据备份"
    fi
    
    # 备份Grafana仪表板
    local grafana_pod=$(kubectl get pods -n postgresql-all-in-one -l app=grafana -o jsonpath='{.items[0].metadata.name}' 2>/dev/null)
    
    if [ -n "$grafana_pod" ]; then
        local grafana_backup="$BACKUP_DIR/grafana_data_$(date +%Y%m%d_%H%M%S).tar.gz"
        log_info "  备份 Grafana 数据..."
        
        kubectl exec -n postgresql-all-in-one "$grafana_pod" -- \
            tar -czf /tmp/grafana_backup.tar.gz -C /var/lib/grafana . 2>/dev/null || true
        
        kubectl cp "postgresql-all-in-one/$grafana_pod:/tmp/grafana_backup.tar.gz" "$grafana_backup" 2>/dev/null
        
        if [ -f "$grafana_backup" ]; then
            local file_size=$(du -h "$grafana_backup" | cut -f1)
            log_success "Grafana 数据备份完成: $grafana_backup ($file_size)"
        fi
    else
        log_warning "未找到 Grafana Pod，跳过仪表板备份"
    fi
    
    echo ""
}

# 创建备份清单
create_manifest() {
    log_info "创建备份清单..."
    
    local manifest_file="$BACKUP_DIR/backup_manifest_$(date +%Y%m%d_%H%M%S).txt"
    
    {
        echo "PostgreSQL All-in-One 备份清单"
        echo "备份时间: $(date '+%Y-%m-%d %H:%M:%S')"
        echo "备份目录: $BACKUP_DIR"
        echo "================================================"
        echo ""
        
        echo "备份文件列表:"
        find "$BACKUP_DIR" -type f -name "*$(date +%Y%m%d)*" -exec ls -lh {} \;
        echo ""
        
        echo "系统信息:"
        kubectl version --short
        echo ""
        
        echo "Pod 状态:"
        kubectl get pods -n postgresql-all-in-one -o wide
        echo ""
        
        echo "存储使用:"
        kubectl get pvc -n postgresql-all-in-one
        echo ""
        
    } > "$manifest_file"
    
    log_success "备份清单已创建: $manifest_file"
    
    if [ "$SHOW_MANIFEST" = "true" ]; then
        cat "$manifest_file"
    fi
    
    echo ""
}

# 清理旧备份
cleanup_old_backups() {
    if [ "$RETENTION_DAYS" -le 0 ]; then
        return 0
    fi
    
    log_info "清理旧备份 (保留 $RETENTION_DAYS 天)..."
    
    local deleted_count=0
    
    # 删除旧的备份文件
    while IFS= read -r file; do
        if [ -f "$file" ]; then
            local file_age=$((($(date +%s) - $(stat -c %Y "$file")) / 86400))
            if [ $file_age -gt $RETENTION_DAYS ]; then
                rm -f "$file"
                log_info "  已删除: $(basename $file) (${file_age}天前)"
                deleted_count=$((deleted_count + 1))
            fi
        fi
    done < <(find "$BACKUP_DIR" -type f -name "*.sql*" -o -name "*.rdb" -o -name "*.tar.gz")
    
    if [ $deleted_count -gt 0 ]; then
        log_success "已清理 $deleted_count 个旧备份文件"
    else
        log_info "没有需要清理的旧备份"
    fi
    
    echo ""
}

# 显示备份摘要
show_summary() {
    echo ""
    cat << "EOF"
╔══════════════════════════════════════════════════════════════╗
║                    ✅ 备份完成！                             ║
╚══════════════════════════════════════════════════════════════╝
EOF
    echo ""
    
    log_success "备份成功完成"
    echo ""
    
    log_info "备份统计:"
    echo "  备份目录: $BACKUP_DIR"
    echo "  备份文件数: $(find "$BACKUP_DIR" -type f -name "*$(date +%Y%m%d)*" | wc -l)"
    echo "  总大小: $(du -sh "$BACKUP_DIR" | cut -f1)"
    echo ""
    
    log_info "最新备份文件:"
    find "$BACKUP_DIR" -type f -name "*$(date +%Y%m%d)*" -exec ls -lh {} \; | \
        awk '{print "  " $9 " (" $5 ")"}'
    echo ""
    
    log_info "恢复备份:"
    echo "  使用 restore.sh 脚本恢复备份"
    echo "  示例: ./restore.sh --backup-dir $BACKUP_DIR"
    echo ""
}

# 主函数
main() {
    # 默认参数
    BACKUP_DIR="./backups"
    RETENTION_DAYS=7
    COMPRESS=true
    SHOW_MANIFEST=false
    BACKUP_ALL=true
    BACKUP_POSTGRESQL=false
    BACKUP_REDIS=false
    BACKUP_CONFIGS=false
    BACKUP_MONITORING=false
    
    # 解析命令行参数
    while [[ $# -gt 0 ]]; do
        case $1 in
            --backup-dir)
                BACKUP_DIR="$2"
                shift 2
                ;;
            --retention-days)
                RETENTION_DAYS="$2"
                shift 2
                ;;
            --no-compress)
                COMPRESS=false
                shift
                ;;
            --show-manifest)
                SHOW_MANIFEST=true
                shift
                ;;
            --postgresql)
                BACKUP_ALL=false
                BACKUP_POSTGRESQL=true
                shift
                ;;
            --redis)
                BACKUP_ALL=false
                BACKUP_REDIS=true
                shift
                ;;
            --configs)
                BACKUP_ALL=false
                BACKUP_CONFIGS=true
                shift
                ;;
            --monitoring)
                BACKUP_ALL=false
                BACKUP_MONITORING=true
                shift
                ;;
            --help)
                cat << EOF
使用方法: $0 [选项]

选项:
  --backup-dir <目录>      备份目录（默认: ./backups）
  --retention-days <天数>  保留天数（默认: 7天）
  --no-compress           不压缩备份文件
  --show-manifest         显示备份清单
  --postgresql            只备份 PostgreSQL
  --redis                 只备份 Redis
  --configs               只备份配置文件
  --monitoring            只备份监控数据
  --help                  显示此帮助信息

示例:
  $0                                    # 完整备份
  $0 --backup-dir /mnt/backups          # 指定备份目录
  $0 --retention-days 30                # 保留30天
  $0 --postgresql --redis               # 只备份数据库
  $0 --no-compress --show-manifest      # 不压缩并显示清单

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
    
    # 执行备份
    if [ "$BACKUP_ALL" = "true" ] || [ "$BACKUP_POSTGRESQL" = "true" ]; then
        backup_postgresql
    fi
    
    if [ "$BACKUP_ALL" = "true" ] || [ "$BACKUP_REDIS" = "true" ]; then
        backup_redis
    fi
    
    if [ "$BACKUP_ALL" = "true" ] || [ "$BACKUP_CONFIGS" = "true" ]; then
        backup_configs
    fi
    
    if [ "$BACKUP_ALL" = "true" ] || [ "$BACKUP_MONITORING" = "true" ]; then
        backup_monitoring
    fi
    
    create_manifest
    cleanup_old_backups
    show_summary
}

# 错误处理
trap 'log_error "备份过程中发生错误，退出代码: $?"; exit 1' ERR

# 执行主函数
main "$@"

