#!/bin/bash
# PostgreSQL All-in-One 一键部署脚本
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
║     PostgreSQL All-in-One 部署工具                          ║
║     为中小型团队打造的经济高效数据处理平台                   ║
║                                                              ║
║     版本: 1.0.0                                             ║
║     日期: 2025-10-08                                        ║
║                                                              ║
╚══════════════════════════════════════════════════════════════╝
EOF
    echo ""
}

# 检查命令是否存在
check_command() {
    if ! command -v "$1" &> /dev/null; then
        return 1
    fi
    return 0
}

# 检查环境
check_environment() {
    log_info "检查部署环境..."
    
    local errors=0
    
    # 检查Docker
    if ! check_command docker; then
        log_error "Docker 未安装，请先安装 Docker"
        log_info "安装指南: https://docs.docker.com/get-docker/"
        errors=$((errors + 1))
    else
        local docker_version=$(docker --version | awk '{print $3}' | sed 's/,//')
        log_success "Docker 已安装 (版本: $docker_version)"
    fi
    
    # 检查kubectl
    if ! check_command kubectl; then
        log_error "kubectl 未安装，请先安装 kubectl"
        log_info "安装指南: https://kubernetes.io/docs/tasks/tools/"
        errors=$((errors + 1))
    else
        local kubectl_version=$(kubectl version --client --short 2>/dev/null | awk '{print $3}')
        log_success "kubectl 已安装 (版本: $kubectl_version)"
    fi
    
    # 检查Helm
    if ! check_command helm; then
        log_error "Helm 未安装，请先安装 Helm"
        log_info "安装指南: https://helm.sh/docs/intro/install/"
        errors=$((errors + 1))
    else
        local helm_version=$(helm version --short | awk '{print $1}')
        log_success "Helm 已安装 (版本: $helm_version)"
    fi
    
    # 检查Kubernetes集群连接
    if check_command kubectl; then
        if kubectl cluster-info &> /dev/null; then
            local cluster_version=$(kubectl version --short 2>/dev/null | grep "Server Version" | awk '{print $3}')
            log_success "Kubernetes 集群连接正常 (版本: $cluster_version)"
        else
            log_error "无法连接到 Kubernetes 集群"
            log_info "请检查 kubeconfig 配置"
            errors=$((errors + 1))
        fi
    fi
    
    if [ $errors -gt 0 ]; then
        log_error "环境检查失败，请解决上述问题后重试"
        exit 1
    fi
    
    log_success "环境检查通过 ✓"
    echo ""
}

# 创建命名空间
create_namespace() {
    log_info "创建命名空间..."
    
    if kubectl get namespace postgresql-all-in-one &> /dev/null; then
        log_warning "命名空间 'postgresql-all-in-one' 已存在"
    else
        kubectl create namespace postgresql-all-in-one
        log_success "命名空间创建完成"
    fi
    
    # 添加标签
    kubectl label namespace postgresql-all-in-one \
        name=postgresql-all-in-one \
        app=postgresql-all-in-one \
        --overwrite
    
    echo ""
}

# 部署PostgreSQL
deploy_postgresql() {
    log_info "部署 PostgreSQL..."
    
    # 使用Helm部署
    if [ -f "../helm/postgresql-all-in-one/Chart.yaml" ]; then
        helm upgrade --install postgresql-all-in-one \
            ../helm/postgresql-all-in-one \
            --namespace postgresql-all-in-one \
            --set postgresql.username=postgres \
            --set postgresql.password=postgres123 \
            --set postgresql.database=allinone \
            --set persistence.size=100Gi \
            --set resources.requests.memory=4Gi \
            --set resources.requests.cpu=2 \
            --set resources.limits.memory=8Gi \
            --set resources.limits.cpu=4 \
            --wait --timeout=10m
        
        log_success "PostgreSQL Helm 部署完成"
    else
        # 使用原始 YAML 部署
        log_warning "Helm Chart 未找到，使用 kubectl 部署"
        if [ -f "../k8s/postgresql-all-in-one-deployment.yaml" ]; then
            kubectl apply -f ../k8s/postgresql-all-in-one-deployment.yaml
            log_success "PostgreSQL kubectl 部署完成"
        else
            log_error "找不到部署配置文件"
            exit 1
        fi
    fi
    
    echo ""
}

# 部署Vector
deploy_vector() {
    log_info "部署 Vector 数据管道..."
    
    # 使用Helm部署
    if [ -f "../helm/vector/Chart.yaml" ]; then
        helm upgrade --install vector \
            ../helm/vector \
            --namespace postgresql-all-in-one \
            --wait --timeout=10m
        
        log_success "Vector Helm 部署完成"
    else
        # 使用原始 YAML 部署
        log_warning "Vector Helm Chart 未找到，使用 kubectl 部署"
        if [ -f "../k8s/vector-deployment.yaml" ]; then
            kubectl apply -f ../k8s/vector-deployment.yaml
            log_success "Vector kubectl 部署完成"
        else
            log_warning "Vector 配置文件未找到，跳过部署"
        fi
    fi
    
    echo ""
}

# 部署监控系统
deploy_monitoring() {
    log_info "部署监控系统..."
    
    # Prometheus
    log_info "  部署 Prometheus..."
    if kubectl get deployment prometheus -n postgresql-all-in-one &> /dev/null; then
        log_warning "  Prometheus 已存在"
    else
        kubectl apply -f - <<EOF
apiVersion: v1
kind: ConfigMap
metadata:
  name: prometheus-config
  namespace: postgresql-all-in-one
data:
  prometheus.yml: |
    global:
      scrape_interval: 15s
      evaluation_interval: 15s
    
    scrape_configs:
      - job_name: 'postgresql'
        static_configs:
          - targets: ['postgresql-service:5432']
      
      - job_name: 'redis'
        static_configs:
          - targets: ['redis-service:6379']
      
      - job_name: 'prometheus'
        static_configs:
          - targets: ['localhost:9090']
---
apiVersion: apps/v1
kind: Deployment
metadata:
  name: prometheus
  namespace: postgresql-all-in-one
spec:
  replicas: 1
  selector:
    matchLabels:
      app: prometheus
  template:
    metadata:
      labels:
        app: prometheus
    spec:
      containers:
      - name: prometheus
        image: prom/prometheus:latest
        ports:
        - containerPort: 9090
        volumeMounts:
        - name: prometheus-config
          mountPath: /etc/prometheus
        - name: prometheus-data
          mountPath: /prometheus
        resources:
          requests:
            memory: "1Gi"
            cpu: "500m"
          limits:
            memory: "2Gi"
            cpu: "1"
      volumes:
      - name: prometheus-config
        configMap:
          name: prometheus-config
      - name: prometheus-data
        emptyDir: {}
---
apiVersion: v1
kind: Service
metadata:
  name: prometheus
  namespace: postgresql-all-in-one
spec:
  selector:
    app: prometheus
  ports:
  - port: 9090
    targetPort: 9090
  type: NodePort
EOF
        log_success "  Prometheus 部署完成"
    fi
    
    # Grafana
    log_info "  部署 Grafana..."
    if kubectl get deployment grafana -n postgresql-all-in-one &> /dev/null; then
        log_warning "  Grafana 已存在"
    else
        kubectl apply -f - <<EOF
apiVersion: apps/v1
kind: Deployment
metadata:
  name: grafana
  namespace: postgresql-all-in-one
spec:
  replicas: 1
  selector:
    matchLabels:
      app: grafana
  template:
    metadata:
      labels:
        app: grafana
    spec:
      containers:
      - name: grafana
        image: grafana/grafana:latest
        ports:
        - containerPort: 3000
        env:
        - name: GF_SECURITY_ADMIN_PASSWORD
          value: "admin123"
        volumeMounts:
        - name: grafana-data
          mountPath: /var/lib/grafana
        resources:
          requests:
            memory: "512Mi"
            cpu: "250m"
          limits:
            memory: "1Gi"
            cpu: "500m"
      volumes:
      - name: grafana-data
        emptyDir: {}
---
apiVersion: v1
kind: Service
metadata:
  name: grafana
  namespace: postgresql-all-in-one
spec:
  selector:
    app: grafana
  ports:
  - port: 3000
    targetPort: 3000
  type: NodePort
EOF
        log_success "  Grafana 部署完成"
    fi
    
    echo ""
}

# 等待服务就绪
wait_for_services() {
    log_info "等待服务就绪..."
    
    # 等待PostgreSQL
    log_info "  等待 PostgreSQL..."
    if kubectl get statefulset postgresql-all-in-one -n postgresql-all-in-one &> /dev/null; then
        kubectl wait --for=condition=ready pod -l app=postgresql \
            --timeout=300s -n postgresql-all-in-one
        log_success "  PostgreSQL 已就绪"
    fi
    
    # 等待Redis
    log_info "  等待 Redis..."
    if kubectl get deployment redis -n postgresql-all-in-one &> /dev/null; then
        kubectl wait --for=condition=available deployment/redis \
            --timeout=300s -n postgresql-all-in-one
        log_success "  Redis 已就绪"
    fi
    
    # 等待Prometheus
    log_info "  等待 Prometheus..."
    if kubectl get deployment prometheus -n postgresql-all-in-one &> /dev/null; then
        kubectl wait --for=condition=available deployment/prometheus \
            --timeout=300s -n postgresql-all-in-one
        log_success "  Prometheus 已就绪"
    fi
    
    # 等待Grafana
    log_info "  等待 Grafana..."
    if kubectl get deployment grafana -n postgresql-all-in-one &> /dev/null; then
        kubectl wait --for=condition=available deployment/grafana \
            --timeout=300s -n postgresql-all-in-one
        log_success "  Grafana 已就绪"
    fi
    
    log_success "所有服务已就绪 ✓"
    echo ""
}

# 显示访问信息
show_access_info() {
    echo ""
    cat << "EOF"
╔══════════════════════════════════════════════════════════════╗
║                    🎉 部署完成！                             ║
╚══════════════════════════════════════════════════════════════╝
EOF
    echo ""
    
    log_info "📊 服务访问信息:"
    echo ""
    
    # 获取PostgreSQL信息
    if kubectl get service postgresql-service -n postgresql-all-in-one &> /dev/null; then
        local pg_port=$(kubectl get svc postgresql-service -n postgresql-all-in-one -o jsonpath='{.spec.ports[0].port}')
        echo "  🗄️  PostgreSQL:"
        echo "      内部地址: postgresql-service.postgresql-all-in-one.svc.cluster.local:$pg_port"
        echo "      用户名: postgres"
        echo "      密码: postgres123"
        echo "      数据库: allinone"
        echo ""
    fi
    
    # 获取Grafana信息
    if kubectl get service grafana -n postgresql-all-in-one &> /dev/null; then
        local grafana_port=$(kubectl get svc grafana -n postgresql-all-in-one -o jsonpath='{.spec.ports[0].nodePort}' 2>/dev/null || echo "3000")
        echo "  📊 Grafana:"
        echo "      访问地址: http://localhost:$grafana_port"
        echo "      用户名: admin"
        echo "      密码: admin123"
        echo ""
    fi
    
    # 获取Prometheus信息
    if kubectl get service prometheus -n postgresql-all-in-one &> /dev/null; then
        local prom_port=$(kubectl get svc prometheus -n postgresql-all-in-one -o jsonpath='{.spec.ports[0].nodePort}' 2>/dev/null || echo "9090")
        echo "  📈 Prometheus:"
        echo "      访问地址: http://localhost:$prom_port"
        echo ""
    fi
    
    log_info "🔧 常用命令:"
    echo ""
    echo "  # 查看所有Pod状态"
    echo "  kubectl get pods -n postgresql-all-in-one"
    echo ""
    echo "  # 查看服务状态"
    echo "  kubectl get svc -n postgresql-all-in-one"
    echo ""
    echo "  # 连接到PostgreSQL"
    echo "  kubectl exec -it -n postgresql-all-in-one statefulset/postgresql-all-in-one -- psql -U postgres -d allinone"
    echo ""
    echo "  # 查看日志"
    echo "  kubectl logs -f -n postgresql-all-in-one statefulset/postgresql-all-in-one"
    echo ""
    echo "  # 端口转发到本地"
    echo "  kubectl port-forward -n postgresql-all-in-one svc/postgresql-service 5432:5432"
    echo "  kubectl port-forward -n postgresql-all-in-one svc/grafana 3000:3000"
    echo ""
    
    log_info "📚 更多信息:"
    echo "  - 项目文档: ../docs/"
    echo "  - 架构设计: PostgreSQL_All_in_One_架构设计方案_2025.md"
    echo "  - 部署指南: PostgreSQL_All_in_One_项目交付清单与部署指南_2025.md"
    echo ""
    
    log_success "部署完成！祝使用愉快 🚀"
    echo ""
}

# 主函数
main() {
    print_banner
    
    # 解析命令行参数
    while [[ $# -gt 0 ]]; do
        case $1 in
            --skip-checks)
                SKIP_CHECKS=true
                shift
                ;;
            --help)
                cat << EOF
使用方法: $0 [选项]

选项:
  --skip-checks    跳过环境检查
  --help          显示此帮助信息

示例:
  $0                     # 标准部署
  $0 --skip-checks       # 跳过环境检查

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
    
    # 执行部署流程
    if [ "$SKIP_CHECKS" != "true" ]; then
        check_environment
    fi
    
    create_namespace
    deploy_postgresql
    deploy_vector
    deploy_monitoring
    wait_for_services
    show_access_info
}

# 错误处理
trap 'log_error "部署过程中发生错误，退出代码: $?"; exit 1' ERR

# 执行主函数
main "$@"

