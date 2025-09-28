#!/bin/bash

# OTLP Rust 生产环境部署脚本
# 本脚本提供了完整的生产环境部署流程

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

# 配置变量
NAMESPACE="otlp-production"
RELEASE_NAME="otlp-server"
CHART_PATH="./helm/otlp-server"
VALUES_FILE="./helm/otlp-server/values.yaml"
DOCKER_IMAGE="otlp-rust:latest"
DOCKER_REGISTRY="your-registry.com"
KUBECONFIG_PATH="${KUBECONFIG:-~/.kube/config}"

# 检查依赖
check_dependencies() {
    log_info "检查部署依赖..."
    
    # 检查kubectl
    if ! command -v kubectl &> /dev/null; then
        log_error "kubectl 未安装，请先安装 kubectl"
        exit 1
    fi
    
    # 检查helm
    if ! command -v helm &> /dev/null; then
        log_error "helm 未安装，请先安装 helm"
        exit 1
    fi
    
    # 检查docker
    if ! command -v docker &> /dev/null; then
        log_error "docker 未安装，请先安装 docker"
        exit 1
    fi
    
    # 检查kubeconfig
    if [ ! -f "$KUBECONFIG_PATH" ]; then
        log_error "kubeconfig 文件不存在: $KUBECONFIG_PATH"
        exit 1
    fi
    
    log_success "所有依赖检查通过"
}

# 构建Docker镜像
build_docker_image() {
    log_info "构建Docker镜像..."
    
    # 构建生产环境镜像
    docker build -f Dockerfile.production -t "$DOCKER_IMAGE" .
    
    if [ $? -eq 0 ]; then
        log_success "Docker镜像构建成功: $DOCKER_IMAGE"
    else
        log_error "Docker镜像构建失败"
        exit 1
    fi
    
    # 标记镜像
    docker tag "$DOCKER_IMAGE" "$DOCKER_REGISTRY/$DOCKER_IMAGE"
    
    # 推送镜像
    log_info "推送Docker镜像到注册表..."
    docker push "$DOCKER_REGISTRY/$DOCKER_IMAGE"
    
    if [ $? -eq 0 ]; then
        log_success "Docker镜像推送成功"
    else
        log_error "Docker镜像推送失败"
        exit 1
    fi
}

# 创建命名空间
create_namespace() {
    log_info "创建Kubernetes命名空间: $NAMESPACE"
    
    kubectl create namespace "$NAMESPACE" --dry-run=client -o yaml | kubectl apply -f -
    
    # 添加标签
    kubectl label namespace "$NAMESPACE" \
        name="$NAMESPACE" \
        environment=production \
        app=otlp-rust \
        --overwrite
    
    log_success "命名空间创建成功"
}

# 创建TLS证书
create_tls_certificates() {
    log_info "创建TLS证书..."
    
    # 创建证书目录
    mkdir -p k8s/ssl
    
    # 生成CA证书
    openssl genrsa -out k8s/ssl/ca.key 4096
    openssl req -new -x509 -days 365 -key k8s/ssl/ca.key -out k8s/ssl/ca.crt \
        -subj "/C=CN/ST=Beijing/L=Beijing/O=OTLP/OU=IT/CN=otlp-ca"
    
    # 生成服务器证书
    openssl genrsa -out k8s/ssl/otlp.key 4096
    openssl req -new -key k8s/ssl/otlp.key -out k8s/ssl/otlp.csr \
        -subj "/C=CN/ST=Beijing/L=Beijing/O=OTLP/OU=IT/CN=otlp-server"
    
    # 签名服务器证书
    openssl x509 -req -days 365 -in k8s/ssl/otlp.csr -CA k8s/ssl/ca.crt -CAkey k8s/ssl/ca.key \
        -CAcreateserial -out k8s/ssl/otlp.crt
    
    # 创建Kubernetes Secret
    kubectl create secret tls otlp-tls-secret \
        --cert=k8s/ssl/otlp.crt \
        --key=k8s/ssl/otlp.key \
        --namespace="$NAMESPACE" \
        --dry-run=client -o yaml | kubectl apply -f -
    
    # 创建证书Secret
    kubectl create secret generic otlp-tls-certs \
        --from-file=otlp.crt=k8s/ssl/otlp.crt \
        --from-file=ca.crt=k8s/ssl/ca.crt \
        --namespace="$NAMESPACE" \
        --dry-run=client -o yaml | kubectl apply -f -
    
    # 创建密钥Secret
    kubectl create secret generic otlp-tls-keys \
        --from-file=otlp.key=k8s/ssl/otlp.key \
        --namespace="$NAMESPACE" \
        --dry-run=client -o yaml | kubectl apply -f -
    
    log_success "TLS证书创建成功"
}

# 部署应用
deploy_application() {
    log_info "部署OTLP应用..."
    
    # 更新Helm仓库
    helm repo update
    
    # 部署应用
    helm upgrade --install "$RELEASE_NAME" "$CHART_PATH" \
        --namespace "$NAMESPACE" \
        --values "$VALUES_FILE" \
        --set image.repository="$DOCKER_REGISTRY/otlp-rust" \
        --set image.tag="latest" \
        --set image.pullPolicy="Always" \
        --wait \
        --timeout=10m
    
    if [ $? -eq 0 ]; then
        log_success "应用部署成功"
    else
        log_error "应用部署失败"
        exit 1
    fi
}

# 验证部署
verify_deployment() {
    log_info "验证部署状态..."
    
    # 检查Pod状态
    kubectl wait --for=condition=Ready pod \
        -l app=otlp-rust \
        -n "$NAMESPACE" \
        --timeout=300s
    
    # 检查Service状态
    kubectl get svc -n "$NAMESPACE"
    
    # 检查Ingress状态
    kubectl get ingress -n "$NAMESPACE"
    
    # 检查HPA状态
    kubectl get hpa -n "$NAMESPACE"
    
    # 检查PDB状态
    kubectl get pdb -n "$NAMESPACE"
    
    log_success "部署验证完成"
}

# 运行健康检查
run_health_check() {
    log_info "运行健康检查..."
    
    # 获取Pod IP
    POD_IP=$(kubectl get pods -n "$NAMESPACE" -l app=otlp-rust -o jsonpath='{.items[0].status.podIP}')
    
    if [ -z "$POD_IP" ]; then
        log_error "无法获取Pod IP"
        return 1
    fi
    
    # 检查健康端点
    kubectl run health-check --image=curlimages/curl --rm -i --restart=Never \
        -- curl -f "http://$POD_IP:9090/health"
    
    if [ $? -eq 0 ]; then
        log_success "健康检查通过"
    else
        log_warning "健康检查失败"
    fi
}

# 显示部署信息
show_deployment_info() {
    log_info "部署信息:"
    echo "命名空间: $NAMESPACE"
    echo "发布名称: $RELEASE_NAME"
    echo "Docker镜像: $DOCKER_REGISTRY/$DOCKER_IMAGE"
    echo ""
    
    log_info "访问信息:"
    echo "GRPC端点: otlp.example.com:4317"
    echo "HTTP端点: otlp.example.com:4318"
    echo "监控端点: otlp.example.com:9090/metrics"
    echo ""
    
    log_info "有用的命令:"
    echo "查看Pod状态: kubectl get pods -n $NAMESPACE"
    echo "查看日志: kubectl logs -f -l app=otlp-rust -n $NAMESPACE"
    echo "查看服务: kubectl get svc -n $NAMESPACE"
    echo "查看Ingress: kubectl get ingress -n $NAMESPACE"
    echo "扩展副本: kubectl scale deployment otlp-server -n $NAMESPACE --replicas=5"
    echo "删除部署: helm uninstall $RELEASE_NAME -n $NAMESPACE"
}

# 清理函数
cleanup() {
    log_info "清理临时文件..."
    rm -rf k8s/ssl
}

# 主函数
main() {
    log_info "开始OTLP Rust生产环境部署..."
    
    # 设置错误时退出
    trap cleanup EXIT
    
    # 执行部署步骤
    check_dependencies
    build_docker_image
    create_namespace
    create_tls_certificates
    deploy_application
    verify_deployment
    run_health_check
    show_deployment_info
    
    log_success "OTLP Rust生产环境部署完成！"
}

# 显示帮助信息
show_help() {
    echo "OTLP Rust 生产环境部署脚本"
    echo ""
    echo "用法: $0 [选项]"
    echo ""
    echo "选项:"
    echo "  -h, --help     显示帮助信息"
    echo "  -n, --namespace 指定命名空间 (默认: otlp-production)"
    echo "  -r, --release   指定发布名称 (默认: otlp-server)"
    echo "  -i, --image     指定Docker镜像 (默认: otlp-rust:latest)"
    echo "  --registry      指定Docker注册表"
    echo "  --skip-build    跳过Docker镜像构建"
    echo "  --skip-certs    跳过TLS证书创建"
    echo ""
    echo "示例:"
    echo "  $0                                    # 使用默认配置部署"
    echo "  $0 -n my-namespace -r my-release     # 指定命名空间和发布名称"
    echo "  $0 --skip-build --skip-certs         # 跳过构建和证书创建"
}

# 解析命令行参数
while [[ $# -gt 0 ]]; do
    case $1 in
        -h|--help)
            show_help
            exit 0
            ;;
        -n|--namespace)
            NAMESPACE="$2"
            shift 2
            ;;
        -r|--release)
            RELEASE_NAME="$2"
            shift 2
            ;;
        -i|--image)
            DOCKER_IMAGE="$2"
            shift 2
            ;;
        --registry)
            DOCKER_REGISTRY="$2"
            shift 2
            ;;
        --skip-build)
            SKIP_BUILD=true
            shift
            ;;
        --skip-certs)
            SKIP_CERTS=true
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
