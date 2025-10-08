#!/bin/bash
# PostgreSQL All-in-One 卸载脚本
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
║     PostgreSQL All-in-One 卸载工具                            ║
║                                                              ║
╚══════════════════════════════════════════════════════════════╝
EOF
    echo ""
}

# 确认卸载
confirm_uninstall() {
    log_warning "⚠️  警告: 此操作将删除所有 PostgreSQL All-in-One 组件和数据！"
    echo ""
    
    if [ "$FORCE_UNINSTALL" = "true" ]; then
        log_warning "强制卸载模式已启用，跳过确认"
        return 0
    fi
    
    read -p "是否继续？(yes/no): " -r
    echo ""
    
    if [[ ! $REPLY =~ ^[Yy][Ee][Ss]$ ]]; then
        log_info "卸载已取消"
        exit 0
    fi
}

# 删除Helm发布
uninstall_helm_releases() {
    log_info "删除 Helm 发布..."
    
    # 删除PostgreSQL Helm发布
    if helm list -n postgresql-all-in-one 2>/dev/null | grep -q postgresql-all-in-one; then
        helm uninstall postgresql-all-in-one -n postgresql-all-in-one
        log_success "PostgreSQL Helm 发布已删除"
    else
        log_warning "PostgreSQL Helm 发布不存在"
    fi
    
    # 删除Vector Helm发布
    if helm list -n postgresql-all-in-one 2>/dev/null | grep -q vector; then
        helm uninstall vector -n postgresql-all-in-one
        log_success "Vector Helm 发布已删除"
    else
        log_warning "Vector Helm 发布不存在"
    fi
    
    echo ""
}

# 删除Kubernetes资源
delete_kubernetes_resources() {
    log_info "删除 Kubernetes 资源..."
    
    # 删除Deployments
    log_info "  删除 Deployments..."
    kubectl delete deployment redis prometheus grafana \
        -n postgresql-all-in-one --ignore-not-found=true
    
    # 删除StatefulSets
    log_info "  删除 StatefulSets..."
    kubectl delete statefulset postgresql-all-in-one vector \
        -n postgresql-all-in-one --ignore-not-found=true
    
    # 删除Services
    log_info "  删除 Services..."
    kubectl delete service postgresql-service redis-service \
        prometheus-service grafana-service vector \
        -n postgresql-all-in-one --ignore-not-found=true
    
    # 删除ConfigMaps
    log_info "  删除 ConfigMaps..."
    kubectl delete configmap --all -n postgresql-all-in-one --ignore-not-found=true
    
    # 删除Secrets
    log_info "  删除 Secrets..."
    kubectl delete secret --all -n postgresql-all-in-one --ignore-not-found=true
    
    # 删除PVCs
    log_info "  删除 PersistentVolumeClaims..."
    kubectl delete pvc --all -n postgresql-all-in-one --ignore-not-found=true
    
    # 删除Ingress
    log_info "  删除 Ingress..."
    kubectl delete ingress --all -n postgresql-all-in-one --ignore-not-found=true
    
    log_success "Kubernetes 资源已删除"
    echo ""
}

# 删除命名空间
delete_namespace() {
    log_info "删除命名空间..."
    
    if kubectl get namespace postgresql-all-in-one &> /dev/null; then
        kubectl delete namespace postgresql-all-in-one
        log_success "命名空间已删除"
        
        # 等待命名空间完全删除
        log_info "等待命名空间完全删除..."
        timeout=60
        elapsed=0
        while kubectl get namespace postgresql-all-in-one &> /dev/null; do
            if [ $elapsed -ge $timeout ]; then
                log_warning "命名空间删除超时，可能需要手动清理"
                break
            fi
            sleep 2
            elapsed=$((elapsed + 2))
            echo -n "."
        done
        echo ""
        
        if ! kubectl get namespace postgresql-all-in-one &> /dev/null; then
            log_success "命名空间完全删除"
        fi
    else
        log_warning "命名空间不存在"
    fi
    
    echo ""
}

# 清理孤立资源
cleanup_orphaned_resources() {
    log_info "清理孤立资源..."
    
    # 清理未绑定的PVs
    log_info "  检查未绑定的 PersistentVolumes..."
    local unbound_pvs=$(kubectl get pv -o json | jq -r '.items[] | select(.spec.claimRef.namespace=="postgresql-all-in-one") | .metadata.name' 2>/dev/null || echo "")
    
    if [ -n "$unbound_pvs" ]; then
        log_warning "  发现未绑定的 PersistentVolumes:"
        echo "$unbound_pvs"
        
        if [ "$FORCE_CLEANUP" = "true" ]; then
            for pv in $unbound_pvs; do
                kubectl delete pv "$pv" --ignore-not-found=true
                log_success "  已删除 PV: $pv"
            done
        else
            log_info "  使用 --force-cleanup 选项可自动删除这些资源"
        fi
    else
        log_success "  没有发现孤立的 PersistentVolumes"
    fi
    
    echo ""
}

# 显示清理摘要
show_summary() {
    echo ""
    cat << "EOF"
╔══════════════════════════════════════════════════════════════╗
║                    ✅ 卸载完成！                             ║
╚══════════════════════════════════════════════════════════════╝
EOF
    echo ""
    
    log_success "PostgreSQL All-in-One 已成功卸载"
    echo ""
    
    log_info "已删除的资源:"
    echo "  ✓ Helm 发布"
    echo "  ✓ Kubernetes 资源 (Deployments, StatefulSets, Services, etc.)"
    echo "  ✓ ConfigMaps 和 Secrets"
    echo "  ✓ PersistentVolumeClaims"
    echo "  ✓ Namespace"
    echo ""
    
    log_info "验证清理:"
    echo "  # 检查命名空间是否已删除"
    echo "  kubectl get namespace postgresql-all-in-one"
    echo ""
    echo "  # 检查是否有残留的PV"
    echo "  kubectl get pv | grep postgresql-all-in-one"
    echo ""
    
    if [ -n "$unbound_pvs" ] && [ "$FORCE_CLEANUP" != "true" ]; then
        log_warning "提示: 发现一些孤立的资源，使用以下命令重新运行以清理:"
        echo "  $0 --force-cleanup"
        echo ""
    fi
}

# 主函数
main() {
    print_banner
    
    # 解析命令行参数
    while [[ $# -gt 0 ]]; do
        case $1 in
            --force)
                FORCE_UNINSTALL=true
                shift
                ;;
            --force-cleanup)
                FORCE_CLEANUP=true
                shift
                ;;
            --help)
                cat << EOF
使用方法: $0 [选项]

选项:
  --force          跳过确认直接卸载
  --force-cleanup  强制清理所有孤立资源
  --help          显示此帮助信息

示例:
  $0                     # 标准卸载（需要确认）
  $0 --force             # 强制卸载（跳过确认）
  $0 --force-cleanup     # 卸载并清理所有孤立资源

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
    
    # 确认卸载
    confirm_uninstall
    
    # 执行卸载流程
    uninstall_helm_releases
    delete_kubernetes_resources
    delete_namespace
    cleanup_orphaned_resources
    show_summary
}

# 错误处理
trap 'log_error "卸载过程中发生错误，退出代码: $?"; exit 1' ERR

# 执行主函数
main "$@"

