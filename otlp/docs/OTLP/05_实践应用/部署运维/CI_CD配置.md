# CI/CD 配置与自动化部署

## 目录

- [CI/CD 配置与自动化部署](#cicd-配置与自动化部署)
  - [目录](#目录)
  - [📚 概述](#-概述)
  - [🚀 GitHub Actions 配置](#-github-actions-配置)
    - [1. 基础工作流配置](#1-基础工作流配置)
    - [2. 多环境部署配置](#2-多环境部署配置)
  - [🔧 GitLab CI 配置](#-gitlab-ci-配置)
  - [🏗️ Jenkins 配置](#️-jenkins-配置)
  - [🚀 自动化部署脚本](#-自动化部署脚本)
    - [1. 部署脚本](#1-部署脚本)
    - [2. 回滚脚本](#2-回滚脚本)
    - [3. 监控脚本](#3-监控脚本)
  - [📊 部署状态监控](#-部署状态监控)
    - [1. 部署状态检查](#1-部署状态检查)
  - [🎯 最佳实践](#-最佳实践)
    - [1. CI/CD最佳实践](#1-cicd最佳实践)
    - [2. 部署最佳实践](#2-部署最佳实践)
    - [3. 安全最佳实践](#3-安全最佳实践)
  - [🚀 下一步](#-下一步)
    - [深入学习](#深入学习)
    - [运维实践](#运维实践)

## 📚 概述

本文档详细介绍了OTLP Rust项目的CI/CD配置，包括GitHub Actions、GitLab CI、Jenkins等主流CI/CD平台的配置，以及自动化部署流程。

## 🚀 GitHub Actions 配置

### 1. 基础工作流配置

创建 `.github/workflows/ci.yml`：

```yaml
name: CI/CD Pipeline

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main ]

env:
  CARGO_TERM_COLOR: always
  RUST_BACKTRACE: 1

jobs:
  # 代码质量检查
  lint:
    name: Code Quality
    runs-on: ubuntu-latest
    steps:
    - name: Checkout code
      uses: actions/checkout@v4
      
    - name: Install Rust
      uses: dtolnay/rust-toolchain@stable
      with:
        components: rustfmt, clippy
        
    - name: Cache cargo dependencies
      uses: actions/cache@v3
      with:
        path: |
          ~/.cargo/registry
          ~/.cargo/git
          target
        key: ${{ runner.os }}-cargo-${{ hashFiles('**/Cargo.lock') }}
        
    - name: Check formatting
      run: cargo fmt --all -- --check
      
    - name: Run clippy
      run: cargo clippy --all-targets --all-features -- -D warnings
      
    - name: Check documentation
      run: cargo doc --no-deps --document-private-items

  # 单元测试
  test:
    name: Unit Tests
    runs-on: ubuntu-latest
    strategy:
      matrix:
        rust: [stable, beta, nightly]
        target: [x86_64-unknown-linux-gnu, x86_64-unknown-linux-musl]
    steps:
    - name: Checkout code
      uses: actions/checkout@v4
      
    - name: Install Rust
      uses: dtolnay/rust-toolchain@master
      with:
        toolchain: ${{ matrix.rust }}
        target: ${{ matrix.target }}
        
    - name: Cache cargo dependencies
      uses: actions/cache@v3
      with:
        path: |
          ~/.cargo/registry
          ~/.cargo/git
          target
        key: ${{ runner.os }}-${{ matrix.rust }}-${{ matrix.target }}-cargo-${{ hashFiles('**/Cargo.lock') }}
        
    - name: Run tests
      run: cargo test --target ${{ matrix.target }} --verbose
      
    - name: Run integration tests
      run: cargo test --target ${{ matrix.target }} --test '*' --verbose
      
    - name: Generate test coverage
      run: |
        cargo install cargo-tarpaulin
        cargo tarpaulin --target ${{ matrix.target }} --out Xml

  # 性能基准测试
  benchmark:
    name: Performance Benchmarks
    runs-on: ubuntu-latest
    steps:
    - name: Checkout code
      uses: actions/checkout@v4
      
    - name: Install Rust
      uses: dtolnay/rust-toolchain@stable
      
    - name: Install dependencies
      run: |
        sudo apt-get update
        sudo apt-get install -y libssl-dev pkg-config
        
    - name: Run benchmarks
      run: cargo bench
      
    - name: Upload benchmark results
      uses: actions/upload-artifact@v3
      with:
        name: benchmark-results
        path: target/criterion/

  # 安全审计
  security:
    name: Security Audit
    runs-on: ubuntu-latest
    steps:
    - name: Checkout code
      uses: actions/checkout@v4
      
    - name: Install Rust
      uses: dtolnay/rust-toolchain@stable
      
    - name: Install cargo-audit
      run: cargo install cargo-audit
      
    - name: Run security audit
      run: cargo audit
      
    - name: Check for known vulnerabilities
      run: cargo audit --deny warnings

  # 构建和发布
  build:
    name: Build and Release
    runs-on: ubuntu-latest
    needs: [lint, test, security]
    if: github.ref == 'refs/heads/main'
    strategy:
      matrix:
        target: [x86_64-unknown-linux-gnu, x86_64-pc-windows-gnu, x86_64-apple-darwin]
    steps:
    - name: Checkout code
      uses: actions/checkout@v4
      
    - name: Install Rust
      uses: dtolnay/rust-toolchain@stable
      with:
        target: ${{ matrix.target }}
        
    - name: Cache cargo dependencies
      uses: actions/cache@v3
      with:
        path: |
          ~/.cargo/registry
          ~/.cargo/git
          target
        key: ${{ runner.os }}-${{ matrix.target }}-cargo-${{ hashFiles('**/Cargo.lock') }}
        
    - name: Build release
      run: cargo build --release --target ${{ matrix.target }}
      
    - name: Upload artifacts
      uses: actions/upload-artifact@v3
      with:
        name: ${{ matrix.target }}
        path: target/${{ matrix.target }}/release/
        
    - name: Create release
      if: matrix.target == 'x86_64-unknown-linux-gnu'
      uses: softprops/action-gh-release@v1
      with:
        tag_name: ${{ github.ref_name }}
        name: Release ${{ github.ref_name }}
        body: |
          ## Changes in this Release
          - Bug fixes and improvements
          - Performance optimizations
          - New features
        files: |
          target/x86_64-unknown-linux-gnu/release/otlp
          target/x86_64-pc-windows-gnu/release/otlp.exe
          target/x86_64-apple-darwin/release/otlp
      env:
        GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}

  # 容器构建和推送
  docker:
    name: Docker Build and Push
    runs-on: ubuntu-latest
    needs: [build]
    if: github.ref == 'refs/heads/main'
    steps:
    - name: Checkout code
      uses: actions/checkout@v4
      
    - name: Set up Docker Buildx
      uses: docker/setup-buildx-action@v3
      
    - name: Login to Docker Hub
      uses: docker/login-action@v3
      with:
        username: ${{ secrets.DOCKER_USERNAME }}
        password: ${{ secrets.DOCKER_PASSWORD }}
        
    - name: Extract metadata
      id: meta
      uses: docker/metadata-action@v5
      with:
        images: my-registry/otlp-rust
        tags: |
          type=ref,event=branch
          type=ref,event=pr
          type=semver,pattern={{version}}
          type=semver,pattern={{major}}.{{minor}}
          type=raw,value=latest,enable={{is_default_branch}}
          
    - name: Build and push Docker image
      uses: docker/build-push-action@v5
      with:
        context: .
        platforms: linux/amd64,linux/arm64
        push: true
        tags: ${{ steps.meta.outputs.tags }}
        labels: ${{ steps.meta.outputs.labels }}
        cache-from: type=gha
        cache-to: type=gha,mode=max

  # Kubernetes部署
  deploy:
    name: Deploy to Kubernetes
    runs-on: ubuntu-latest
    needs: [docker]
    if: github.ref == 'refs/heads/main'
    environment: production
    steps:
    - name: Checkout code
      uses: actions/checkout@v4
      
    - name: Configure kubectl
      uses: azure/setup-kubectl@v3
      with:
        version: 'latest'
        
    - name: Setup Helm
      uses: azure/setup-helm@v3
      with:
        version: 'latest'
        
    - name: Deploy to Kubernetes
      run: |
        echo "${{ secrets.KUBE_CONFIG }}" | base64 -d > kubeconfig
        export KUBECONFIG=kubeconfig
        
        # Update image tag
        sed -i "s|image: my-registry/otlp-rust:.*|image: my-registry/otlp-rust:${{ github.sha }}|g" k8s/deployment.yaml
        
        # Apply manifests
        kubectl apply -f k8s/namespace.yaml
        kubectl apply -f k8s/configmap.yaml
        kubectl apply -f k8s/secret.yaml
        kubectl apply -f k8s/deployment.yaml
        kubectl apply -f k8s/service.yaml
        
        # Wait for rollout
        kubectl rollout status deployment/otlp-app -n otlp-system --timeout=300s
        
    - name: Run health checks
      run: |
        export KUBECONFIG=kubeconfig
        kubectl wait --for=condition=ready pod -l app=otlp-app -n otlp-system --timeout=300s
        kubectl get pods -n otlp-system
        
    - name: Notify deployment
      uses: 8398a7/action-slack@v3
      with:
        status: ${{ job.status }}
        channel: '#deployments'
        text: 'OTLP Rust deployment completed: ${{ job.status }}'
      env:
        SLACK_WEBHOOK_URL: ${{ secrets.SLACK_WEBHOOK_URL }}
      if: always()
```

### 2. 多环境部署配置

创建 `.github/workflows/deploy-staging.yml`：

```yaml
name: Deploy to Staging

on:
  push:
    branches: [ develop ]
  workflow_dispatch:

env:
  ENVIRONMENT: staging
  NAMESPACE: otlp-staging

jobs:
  deploy-staging:
    name: Deploy to Staging
    runs-on: ubuntu-latest
    environment: staging
    steps:
    - name: Checkout code
      uses: actions/checkout@v4
      
    - name: Configure kubectl
      uses: azure/setup-kubectl@v3
      
    - name: Deploy to Staging
      run: |
        echo "${{ secrets.KUBE_CONFIG_STAGING }}" | base64 -d > kubeconfig
        export KUBECONFIG=kubeconfig
        
        # Deploy with staging configuration
        helm upgrade --install otlp-app ./helm/otlp-app \
          --namespace ${{ env.NAMESPACE }} \
          --create-namespace \
          --set image.tag=${{ github.sha }} \
          --set environment=${{ env.ENVIRONMENT }} \
          --set ingress.host=staging.otlp.example.com \
          --set resources.requests.memory=128Mi \
          --set resources.requests.cpu=100m \
          --set resources.limits.memory=256Mi \
          --set resources.limits.cpu=200m
        
        # Wait for deployment
        kubectl rollout status deployment/otlp-app -n ${{ env.NAMESPACE }} --timeout=300s
        
    - name: Run smoke tests
      run: |
        export KUBECONFIG=kubeconfig
        # Port forward for testing
        kubectl port-forward -n ${{ env.NAMESPACE }} svc/otlp-app-service 8080:80 &
        PORT_FORWARD_PID=$!
        
        sleep 10
        
        # Run smoke tests
        curl -f http://localhost:8080/health
        curl -f http://localhost:8080/ready
        curl -f http://localhost:8080/metrics
        
        kill $PORT_FORWARD_PID
        
    - name: Notify staging deployment
      uses: 8398a7/action-slack@v3
      with:
        status: ${{ job.status }}
        channel: '#staging-deployments'
        text: 'OTLP Rust staging deployment: ${{ job.status }}'
      env:
        SLACK_WEBHOOK_URL: ${{ secrets.SLACK_WEBHOOK_URL }}
      if: always()
```

## 🔧 GitLab CI 配置

创建 `.gitlab-ci.yml`：

```yaml
stages:
  - lint
  - test
  - security
  - build
  - deploy

variables:
  CARGO_TERM_COLOR: always
  RUST_BACKTRACE: 1
  DOCKER_DRIVER: overlay2
  DOCKER_TLS_CERTDIR: "/certs"

# 代码质量检查
lint:
  stage: lint
  image: rust:1.90-slim
  before_script:
    - rustup component add rustfmt clippy
    - cargo --version
    - rustc --version
  script:
    - cargo fmt --all -- --check
    - cargo clippy --all-targets --all-features -- -D warnings
    - cargo doc --no-deps --document-private-items
  cache:
    key: ${CI_COMMIT_REF_SLUG}
    paths:
      - target/
      - .cargo/

# 单元测试
test:
  stage: test
  image: rust:1.90-slim
  script:
    - cargo test --verbose
    - cargo test --test '*' --verbose
  coverage: '/TOTAL.*\s+(\d+%)$/'
  artifacts:
    reports:
      coverage_report:
        coverage_format: cobertura
        path: coverage/cobertura-coverage.xml
    paths:
      - target/coverage/
    expire_in: 1 week
  cache:
    key: ${CI_COMMIT_REF_SLUG}
    paths:
      - target/
      - .cargo/

# 安全审计
security_audit:
  stage: security
  image: rust:1.90-slim
  script:
    - cargo install cargo-audit
    - cargo audit
    - cargo audit --deny warnings
  allow_failure: true

# 构建
build:
  stage: build
  image: rust:1.90-slim
  script:
    - cargo build --release
  artifacts:
    paths:
      - target/release/
    expire_in: 1 hour
  only:
    - main
    - develop

# Docker构建
docker_build:
  stage: build
  image: docker:latest
  services:
    - docker:dind
  before_script:
    - docker login -u $CI_REGISTRY_USER -p $CI_REGISTRY_PASSWORD $CI_REGISTRY
  script:
    - docker build -t $CI_REGISTRY_IMAGE:$CI_COMMIT_SHA .
    - docker build -t $CI_REGISTRY_IMAGE:latest .
    - docker push $CI_REGISTRY_IMAGE:$CI_COMMIT_SHA
    - docker push $CI_REGISTRY_IMAGE:latest
  only:
    - main
    - develop

# 部署到开发环境
deploy_dev:
  stage: deploy
  image: bitnami/kubectl:latest
  script:
    - kubectl config use-context $KUBE_CONTEXT_DEV
    - kubectl set image deployment/otlp-app otlp-app=$CI_REGISTRY_IMAGE:$CI_COMMIT_SHA -n otlp-dev
    - kubectl rollout status deployment/otlp-app -n otlp-dev --timeout=300s
  environment:
    name: development
    url: https://dev.otlp.example.com
  only:
    - develop

# 部署到生产环境
deploy_prod:
  stage: deploy
  image: bitnami/kubectl:latest
  script:
    - kubectl config use-context $KUBE_CONTEXT_PROD
    - kubectl set image deployment/otlp-app otlp-app=$CI_REGISTRY_IMAGE:$CI_COMMIT_SHA -n otlp-prod
    - kubectl rollout status deployment/otlp-app -n otlp-prod --timeout=300s
    - kubectl get pods -n otlp-prod
  environment:
    name: production
    url: https://otlp.example.com
  only:
    - main
  when: manual
```

## 🏗️ Jenkins 配置

创建 `Jenkinsfile`：

```groovy
pipeline {
    agent any
    
    environment {
        DOCKER_REGISTRY = 'my-registry'
        KUBE_NAMESPACE = 'otlp-system'
        RUST_VERSION = '1.90'
    }
    
    stages {
        stage('Checkout') {
            steps {
                checkout scm
            }
        }
        
        stage('Setup') {
            steps {
                sh '''
                    rustup update
                    rustup default ${RUST_VERSION}
                    rustup component add rustfmt clippy
                '''
            }
        }
        
        stage('Lint') {
            steps {
                sh '''
                    cargo fmt --all -- --check
                    cargo clippy --all-targets --all-features -- -D warnings
                '''
            }
        }
        
        stage('Test') {
            parallel {
                stage('Unit Tests') {
                    steps {
                        sh 'cargo test --verbose'
                    }
                }
                stage('Integration Tests') {
                    steps {
                        sh 'cargo test --test "*" --verbose'
                    }
                }
                stage('Security Audit') {
                    steps {
                        sh '''
                            cargo install cargo-audit
                            cargo audit
                        '''
                    }
                }
            }
            post {
                always {
                    publishTestResults testResultsPattern: 'target/test-results/*.xml'
                    publishCoverage adapters: [
                        coberturaAdapter('target/cobertura.xml')
                    ], sourceFileResolver: sourceFiles('STORE_LAST_BUILD')
                }
            }
        }
        
        stage('Build') {
            steps {
                sh 'cargo build --release'
                archiveArtifacts artifacts: 'target/release/*', fingerprint: true
            }
        }
        
        stage('Docker Build') {
            when {
                branch 'main'
            }
            steps {
                script {
                    def image = docker.build("${DOCKER_REGISTRY}/otlp-rust:${env.BUILD_NUMBER}")
                    docker.withRegistry("https://${DOCKER_REGISTRY}", 'docker-registry-credentials') {
                        image.push()
                        image.push('latest')
                    }
                }
            }
        }
        
        stage('Deploy to Staging') {
            when {
                branch 'develop'
            }
            steps {
                script {
                    kubernetesDeploy(
                        configs: 'k8s/*.yaml',
                        kubeconfigId: 'kubeconfig-staging',
                        namespace: 'otlp-staging'
                    )
                }
            }
        }
        
        stage('Deploy to Production') {
            when {
                branch 'main'
            }
            steps {
                input message: 'Deploy to production?', ok: 'Deploy'
                script {
                    kubernetesDeploy(
                        configs: 'k8s/*.yaml',
                        kubeconfigId: 'kubeconfig-prod',
                        namespace: 'otlp-prod'
                    )
                }
            }
        }
    }
    
    post {
        always {
            cleanWs()
        }
        success {
            emailext (
                subject: "Build Successful: ${env.JOB_NAME} - ${env.BUILD_NUMBER}",
                body: "Build was successful. Check the build log for details.",
                to: "${env.CHANGE_AUTHOR_EMAIL}"
            )
        }
        failure {
            emailext (
                subject: "Build Failed: ${env.JOB_NAME} - ${env.BUILD_NUMBER}",
                body: "Build failed. Check the build log for details.",
                to: "${env.CHANGE_AUTHOR_EMAIL}"
            )
        }
    }
}
```

## 🚀 自动化部署脚本

### 1. 部署脚本

创建 `scripts/deploy.sh`：

```bash
#!/bin/bash
set -euo pipefail

# 配置变量
NAMESPACE=${1:-otlp-system}
ENVIRONMENT=${2:-development}
IMAGE_TAG=${3:-latest}
REGISTRY=${4:-my-registry}

# 颜色输出
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# 日志函数
log_info() {
    echo -e "${GREEN}[INFO]${NC} $1"
}

log_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# 检查依赖
check_dependencies() {
    log_info "Checking dependencies..."
    
    if ! command -v kubectl &> /dev/null; then
        log_error "kubectl is not installed"
        exit 1
    fi
    
    if ! command -v helm &> /dev/null; then
        log_error "helm is not installed"
        exit 1
    fi
    
    log_info "All dependencies are available"
}

# 验证Kubernetes连接
verify_k8s_connection() {
    log_info "Verifying Kubernetes connection..."
    
    if ! kubectl cluster-info &> /dev/null; then
        log_error "Cannot connect to Kubernetes cluster"
        exit 1
    fi
    
    log_info "Kubernetes connection verified"
}

# 创建命名空间
create_namespace() {
    log_info "Creating namespace: $NAMESPACE"
    
    kubectl create namespace "$NAMESPACE" --dry-run=client -o yaml | kubectl apply -f -
    
    log_info "Namespace created/updated"
}

# 部署配置
deploy_config() {
    log_info "Deploying configuration..."
    
    # 应用ConfigMap
    if [ -f "k8s/configmap.yaml" ]; then
        envsubst < k8s/configmap.yaml | kubectl apply -f -
        log_info "ConfigMap deployed"
    fi
    
    # 应用Secret
    if [ -f "k8s/secret.yaml" ]; then
        kubectl apply -f k8s/secret.yaml
        log_info "Secret deployed"
    fi
    
    # 应用RBAC
    if [ -f "k8s/rbac.yaml" ]; then
        kubectl apply -f k8s/rbac.yaml
        log_info "RBAC deployed"
    fi
}

# 部署应用
deploy_app() {
    log_info "Deploying application..."
    
    # 更新镜像标签
    sed -i.bak "s|image: ${REGISTRY}/otlp-rust:.*|image: ${REGISTRY}/otlp-rust:${IMAGE_TAG}|g" k8s/deployment.yaml
    
    # 应用部署
    kubectl apply -f k8s/deployment.yaml
    log_info "Deployment applied"
    
    # 应用服务
    kubectl apply -f k8s/service.yaml
    log_info "Service applied"
    
    # 应用Ingress
    if [ -f "k8s/ingress.yaml" ]; then
        kubectl apply -f k8s/ingress.yaml
        log_info "Ingress applied"
    fi
}

# 等待部署完成
wait_for_deployment() {
    log_info "Waiting for deployment to complete..."
    
    kubectl rollout status deployment/otlp-app -n "$NAMESPACE" --timeout=300s
    
    log_info "Deployment completed"
}

# 健康检查
health_check() {
    log_info "Running health checks..."
    
    # 等待Pod就绪
    kubectl wait --for=condition=ready pod -l app=otlp-app -n "$NAMESPACE" --timeout=300s
    
    # 获取Pod名称
    POD_NAME=$(kubectl get pods -n "$NAMESPACE" -l app=otlp-app -o jsonpath='{.items[0].metadata.name}')
    
    if [ -z "$POD_NAME" ]; then
        log_error "No pods found"
        exit 1
    fi
    
    # 端口转发
    kubectl port-forward -n "$NAMESPACE" svc/otlp-app-service 8080:80 &
    PORT_FORWARD_PID=$!
    
    sleep 10
    
    # 健康检查
    if curl -f http://localhost:8080/health; then
        log_info "Health check passed"
    else
        log_error "Health check failed"
        kill $PORT_FORWARD_PID
        exit 1
    fi
    
    # 就绪检查
    if curl -f http://localhost:8080/ready; then
        log_info "Readiness check passed"
    else
        log_error "Readiness check failed"
        kill $PORT_FORWARD_PID
        exit 1
    fi
    
    kill $PORT_FORWARD_PID
    log_info "All health checks passed"
}

# 清理旧镜像
cleanup_old_images() {
    log_info "Cleaning up old images..."
    
    # 保留最近的3个版本
    kubectl get replicasets -n "$NAMESPACE" -l app=otlp-app --sort-by=.metadata.creationTimestamp -o jsonpath='{.items[:-3].metadata.name}' | \
    xargs -r kubectl delete replicaset -n "$NAMESPACE"
    
    log_info "Cleanup completed"
}

# 发送通知
send_notification() {
    local status=$1
    local message=$2
    
    if [ -n "${SLACK_WEBHOOK_URL:-}" ]; then
        curl -X POST -H 'Content-type: application/json' \
            --data "{\"text\":\"OTLP Rust Deployment: $status - $message\"}" \
            "$SLACK_WEBHOOK_URL"
    fi
}

# 主函数
main() {
    log_info "Starting deployment..."
    log_info "Namespace: $NAMESPACE"
    log_info "Environment: $ENVIRONMENT"
    log_info "Image Tag: $IMAGE_TAG"
    log_info "Registry: $REGISTRY"
    
    check_dependencies
    verify_k8s_connection
    create_namespace
    deploy_config
    deploy_app
    wait_for_deployment
    health_check
    cleanup_old_images
    
    log_info "Deployment completed successfully!"
    send_notification "SUCCESS" "Deployment to $ENVIRONMENT completed"
}

# 错误处理
trap 'log_error "Deployment failed"; send_notification "FAILED" "Deployment to $ENVIRONMENT failed"; exit 1' ERR

# 执行主函数
main "$@"
```

### 2. 回滚脚本

创建 `scripts/rollback.sh`：

```bash
#!/bin/bash
set -euo pipefail

NAMESPACE=${1:-otlp-system}
REVISION=${2:-}

# 颜色输出
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

log_info() {
    echo -e "${GREEN}[INFO]${NC} $1"
}

log_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# 显示可用版本
show_revisions() {
    log_info "Available revisions:"
    kubectl rollout history deployment/otlp-app -n "$NAMESPACE"
}

# 回滚到指定版本
rollback_to_revision() {
    local revision=$1
    
    log_info "Rolling back to revision $revision in namespace $NAMESPACE"
    
    kubectl rollout undo deployment/otlp-app --to-revision="$revision" -n "$NAMESPACE"
    
    kubectl rollout status deployment/otlp-app -n "$NAMESPACE" --timeout=300s
    
    log_info "Rollback completed successfully!"
}

# 主函数
main() {
    if [ -z "$REVISION" ]; then
        log_error "Usage: $0 <namespace> <revision>"
        show_revisions
        exit 1
    fi
    
    rollback_to_revision "$REVISION"
}

main "$@"
```

### 3. 监控脚本

创建 `scripts/monitor.sh`：

```bash
#!/bin/bash
set -euo pipefail

NAMESPACE=${1:-otlp-system}
DURATION=${2:-300}

# 颜色输出
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

log_info() {
    echo -e "${GREEN}[INFO]${NC} $1"
}

log_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# 监控Pod状态
monitor_pods() {
    log_info "Monitoring pods in namespace: $NAMESPACE"
    
    while true; do
        echo -e "\n${BLUE}=== Pod Status ===${NC}"
        kubectl get pods -n "$NAMESPACE" -l app=otlp-app
        
        echo -e "\n${BLUE}=== Pod Events ===${NC}"
        kubectl get events -n "$NAMESPACE" --sort-by='.lastTimestamp' | tail -5
        
        sleep 10
    done
}

# 监控资源使用
monitor_resources() {
    log_info "Monitoring resource usage..."
    
    while true; do
        echo -e "\n${BLUE}=== Resource Usage ===${NC}"
        kubectl top pods -n "$NAMESPACE" -l app=otlp-app
        
        echo -e "\n${BLUE}=== Node Resources ===${NC}"
        kubectl top nodes
        
        sleep 30
    done
}

# 监控日志
monitor_logs() {
    log_info "Monitoring application logs..."
    
    kubectl logs -f -n "$NAMESPACE" -l app=otlp-app --tail=100
}

# 性能测试
performance_test() {
    log_info "Running performance tests..."
    
    # 端口转发
    kubectl port-forward -n "$NAMESPACE" svc/otlp-app-service 8080:80 &
    PORT_FORWARD_PID=$!
    
    sleep 5
    
    # 并发测试
    for i in {1..10}; do
        curl -w "@curl-format.txt" -o /dev/null -s http://localhost:8080/health &
    done
    
    wait
    kill $PORT_FORWARD_PID
}

# 主函数
main() {
    case "${3:-pods}" in
        "pods")
            monitor_pods
            ;;
        "resources")
            monitor_resources
            ;;
        "logs")
            monitor_logs
            ;;
        "performance")
            performance_test
            ;;
        *)
            log_error "Unknown monitoring type: ${3:-pods}"
            log_info "Available types: pods, resources, logs, performance"
            exit 1
            ;;
    esac
}

main "$@"
```

## 📊 部署状态监控

### 1. 部署状态检查

创建 `scripts/check-deployment.sh`：

```bash
#!/bin/bash
set -euo pipefail

NAMESPACE=${1:-otlp-system}

# 检查部署状态
check_deployment_status() {
    echo "=== Deployment Status ==="
    kubectl get deployment otlp-app -n "$NAMESPACE" -o wide
    
    echo -e "\n=== Pod Status ==="
    kubectl get pods -n "$NAMESPACE" -l app=otlp-app
    
    echo -e "\n=== Service Status ==="
    kubectl get svc -n "$NAMESPACE" -l app=otlp-app
    
    echo -e "\n=== Ingress Status ==="
    kubectl get ingress -n "$NAMESPACE" -l app=otlp-app
}

# 检查健康状态
check_health() {
    echo -e "\n=== Health Check ==="
    
    # 端口转发
    kubectl port-forward -n "$NAMESPACE" svc/otlp-app-service 8080:80 &
    PORT_FORWARD_PID=$!
    
    sleep 5
    
    # 健康检查
    if curl -f http://localhost:8080/health; then
        echo "✓ Health check passed"
    else
        echo "✗ Health check failed"
    fi
    
    # 就绪检查
    if curl -f http://localhost:8080/ready; then
        echo "✓ Readiness check passed"
    else
        echo "✗ Readiness check failed"
    fi
    
    # 指标检查
    if curl -f http://localhost:8080/metrics > /dev/null; then
        echo "✓ Metrics endpoint accessible"
    else
        echo "✗ Metrics endpoint not accessible"
    fi
    
    kill $PORT_FORWARD_PID
}

# 检查资源使用
check_resources() {
    echo -e "\n=== Resource Usage ==="
    kubectl top pods -n "$NAMESPACE" -l app=otlp-app
}

# 检查事件
check_events() {
    echo -e "\n=== Recent Events ==="
    kubectl get events -n "$NAMESPACE" --sort-by='.lastTimestamp' | tail -10
}

# 主函数
main() {
    check_deployment_status
    check_health
    check_resources
    check_events
}

main "$@"
```

## 🎯 最佳实践

### 1. CI/CD最佳实践

- **自动化测试**: 在每次提交时运行完整的测试套件
- **安全扫描**: 集成安全审计工具，检查依赖漏洞
- **代码质量**: 使用clippy和rustfmt确保代码质量
- **渐进式部署**: 使用蓝绿部署或金丝雀部署策略
- **回滚机制**: 确保能够快速回滚到之前的版本

### 2. 部署最佳实践

- **环境隔离**: 使用不同的命名空间隔离环境
- **配置管理**: 使用ConfigMap和Secret管理配置
- **资源限制**: 设置合理的资源请求和限制
- **健康检查**: 实现完整的健康检查机制
- **监控告警**: 设置监控和告警系统

### 3. 安全最佳实践

- **镜像安全**: 使用安全的基础镜像
- **密钥管理**: 使用Kubernetes Secret管理敏感信息
- **网络策略**: 实施网络隔离策略
- **RBAC**: 使用基于角色的访问控制
- **审计日志**: 启用审计日志记录

## 🚀 下一步

### 深入学习

1. **[监控告警设置](监控告警.md)** - 建立完整的监控体系
2. **[故障排查指南](故障排查.md)** - 快速定位和解决问题
3. **[性能优化策略](../性能调优/优化策略.md)** - 提升应用性能

### 运维实践

1. **[自动化运维](自动化运维.md)** - 实现运维自动化
2. **[灾难恢复](灾难恢复.md)** - 建立灾难恢复机制
3. **[容量规划](容量规划.md)** - 进行容量规划和扩展

---

**CI/CD配置与自动化部署版本**: v1.0  
**最后更新**: 2025年1月27日  
**维护者**: OTLP 2025 文档团队
