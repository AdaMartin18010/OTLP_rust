# Jenkins CI - Rust 完整配置

## 目录

- [Jenkins CI - Rust 完整配置](#jenkins-ci---rust-完整配置)
  - [目录](#目录)
  - [1. Jenkins 环境配置](#1-jenkins-环境配置)
    - [1.1 安装 Jenkins](#11-安装-jenkins)
    - [1.2 安装必要插件](#12-安装必要插件)
    - [1.3 全局工具配置](#13-全局工具配置)
  - [2. Rust 构建环境](#2-rust-构建环境)
    - [2.1 Docker Agent](#21-docker-agent)
    - [2.2 Shell Agent](#22-shell-agent)
  - [3. 基础 Pipeline](#3-基础-pipeline)
    - [3.1 Jenkinsfile](#31-jenkinsfile)
    - [3.2 多阶段构建](#32-多阶段构建)
  - [4. 代码质量检查](#4-代码质量检查)
    - [4.1 格式检查](#41-格式检查)
    - [4.2 Clippy 静态分析](#42-clippy-静态分析)
    - [4.3 安全审计](#43-安全审计)
  - [5. 测试执行](#5-测试执行)
    - [5.1 单元测试](#51-单元测试)
    - [5.2 集成测试](#52-集成测试)
    - [5.3 测试覆盖率](#53-测试覆盖率)
  - [6. OTLP 集成测试](#6-otlp-集成测试)
    - [6.1 启动 Jaeger](#61-启动-jaeger)
    - [6.2 运行集成测试](#62-运行集成测试)
  - [7. 性能测试](#7-性能测试)
    - [7.1 Criterion 基准测试](#71-criterion-基准测试)
    - [7.2 结果发布](#72-结果发布)
  - [8. Docker 构建与发布](#8-docker-构建与发布)
    - [8.1 多阶段 Dockerfile](#81-多阶段-dockerfile)
    - [8.2 镜像推送](#82-镜像推送)
  - [9. 自动化部署](#9-自动化部署)
    - [9.1 部署到 Kubernetes](#91-部署到-kubernetes)
    - [9.2 部署到 Docker Swarm](#92-部署到-docker-swarm)
  - [10. 通知与报告](#10-通知与报告)
    - [10.1 Slack 通知](#101-slack-通知)
    - [10.2 Email 通知](#102-email-通知)
    - [10.3 测试报告](#103-测试报告)
  - [11. 缓存优化](#11-缓存优化)
    - [11.1 Cargo 缓存](#111-cargo-缓存)
    - [11.2 sccache 配置](#112-sccache-配置)
  - [12. 完整示例](#12-完整示例)
    - [12.1 生产级 Jenkinsfile](#121-生产级-jenkinsfile)
    - [12.2 多分支 Pipeline](#122-多分支-pipeline)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [性能优化](#性能优化)
    - [最佳实践清单](#最佳实践清单)

---

## 1. Jenkins 环境配置

### 1.1 安装 Jenkins

````yaml
# docker-compose.yml
version: '3.8'
services:
  jenkins:
    image: jenkins/jenkins:lts
    container_name: jenkins
    privileged: true
    user: root
    ports:
      - "8080:8080"
      - "50000:50000"
    volumes:
      - jenkins_home:/var/jenkins_home
      - /var/run/docker.sock:/var/run/docker.sock
    environment:
      - JAVA_OPTS=-Djenkins.install.runSetupWizard=false

volumes:
  jenkins_home:
````

````bash
# 启动 Jenkins
docker-compose up -d

# 获取初始密码
docker exec jenkins cat /var/jenkins_home/secrets/initialAdminPassword
````

### 1.2 安装必要插件

````text
必要插件列表:
- Pipeline
- Docker Pipeline
- Git
- GitHub
- Slack Notification
- HTML Publisher
- JUnit
- Cobertura
- Blue Ocean (可选)
````

**通过 Jenkins UI 安装**:

1. Manage Jenkins → Manage Plugins
2. 搜索并安装以上插件
3. 重启 Jenkins

### 1.3 全局工具配置

**Manage Jenkins → Global Tool Configuration**:

````text
Rust:
- Name: rust-stable
- Installation: Install from rustup.rs

Docker:
- Name: docker
- Installation: Install automatically

Git:
- Name: git
- Installation: Default
````

---

## 2. Rust 构建环境

### 2.1 Docker Agent

**Dockerfile**:

````dockerfile
FROM rust:1.90-slim

# 安装依赖
RUN apt-get update && apt-get install -y \
    build-essential \
    pkg-config \
    libssl-dev \
    git \
    curl \
    && rm -rf /var/lib/apt/lists/*

# 安装额外工具
RUN rustup component add rustfmt clippy
RUN cargo install cargo-audit cargo-deny sccache cargo-llvm-cov

# 配置 sccache
ENV RUSTC_WRAPPER=sccache
ENV SCCACHE_DIR=/cache/sccache

WORKDIR /workspace
````

````bash
# 构建镜像
docker build -t rust-ci:latest .
````

### 2.2 Shell Agent

````bash
# 在 Jenkins Agent 上安装 Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y

# 安装工具
cargo install cargo-audit cargo-deny sccache cargo-llvm-cov
rustup component add rustfmt clippy
````

---

## 3. 基础 Pipeline

### 3.1 Jenkinsfile

````groovy
pipeline {
    agent {
        docker {
            image 'rust:1.90-slim'
            args '-v cargo-cache:/usr/local/cargo/registry'
        }
    }

    environment {
        CARGO_HOME = '/usr/local/cargo'
        RUSTFLAGS = '-D warnings'
    }

    stages {
        stage('Checkout') {
            steps {
                checkout scm
            }
        }

        stage('Build') {
            steps {
                sh 'cargo build --release'
            }
        }

        stage('Test') {
            steps {
                sh 'cargo test --all-features'
            }
        }

        stage('Lint') {
            steps {
                sh 'cargo fmt -- --check'
                sh 'cargo clippy -- -D warnings'
            }
        }
    }

    post {
        always {
            cleanWs()
        }
    }
}
````

### 3.2 多阶段构建

````groovy
pipeline {
    agent {
        docker {
            image 'rust-ci:latest'
        }
    }

    stages {
        stage('Setup') {
            steps {
                echo 'Setting up Rust environment...'
                sh 'rustc --version'
                sh 'cargo --version'
            }
        }

        stage('Check') {
            parallel {
                stage('Format') {
                    steps {
                        sh 'cargo fmt -- --check'
                    }
                }
                stage('Clippy') {
                    steps {
                        sh 'cargo clippy --all-targets --all-features -- -D warnings'
                    }
                }
            }
        }

        stage('Build') {
            parallel {
                stage('Debug Build') {
                    steps {
                        sh 'cargo build --all-features'
                    }
                }
                stage('Release Build') {
                    steps {
                        sh 'cargo build --release --all-features'
                    }
                }
            }
        }

        stage('Test') {
            parallel {
                stage('Unit Tests') {
                    steps {
                        sh 'cargo test --lib --all-features'
                    }
                }
                stage('Integration Tests') {
                    steps {
                        sh 'cargo test --test "*" --all-features'
                    }
                }
            }
        }
    }
}
````

---

## 4. 代码质量检查

### 4.1 格式检查

````groovy
stage('Format Check') {
    steps {
        script {
            def formatResult = sh(
                script: 'cargo fmt -- --check',
                returnStatus: true
            )
            if (formatResult != 0) {
                error "Code formatting check failed. Run 'cargo fmt' to fix."
            }
        }
    }
}
````

### 4.2 Clippy 静态分析

````groovy
stage('Clippy') {
    steps {
        script {
            sh '''
                cargo clippy --all-targets --all-features \
                    --message-format=json -- -D warnings \
                    | tee clippy-output.json
            '''
        }
        
        // 发布 Clippy 报告
        publishHTML([
            reportDir: '.',
            reportFiles: 'clippy-output.json',
            reportName: 'Clippy Report'
        ])
    }
}
````

### 4.3 安全审计

````groovy
stage('Security Audit') {
    steps {
        script {
            // cargo-audit: 检查已知漏洞
            sh 'cargo audit --json > audit-report.json || true'
            
            // cargo-deny: 检查许可证和依赖
            sh 'cargo deny check --config .cargo-deny.toml || true'
        }
        
        publishHTML([
            reportDir: '.',
            reportFiles: 'audit-report.json',
            reportName: 'Security Audit Report'
        ])
    }
}
````

**.cargo-deny.toml**:

````toml
[advisories]
vulnerability = "deny"
unmaintained = "warn"
yanked = "deny"

[licenses]
unlicensed = "deny"
allow = ["MIT", "Apache-2.0", "BSD-3-Clause"]
deny = ["GPL-3.0"]

[bans]
multiple-versions = "warn"
````

---

## 5. 测试执行

### 5.1 单元测试

````groovy
stage('Unit Tests') {
    steps {
        sh '''
            cargo test --lib --all-features \
                --no-fail-fast \
                -- --test-threads=1 --nocapture \
                | tee test-output.txt
        '''
    }
    post {
        always {
            junit 'target/test-results/*.xml'
        }
    }
}
````

### 5.2 集成测试

````groovy
stage('Integration Tests') {
    steps {
        sh '''
            # 启动测试依赖
            docker-compose -f docker-compose.test.yml up -d
            
            # 等待服务就绪
            sleep 10
            
            # 运行集成测试
            cargo test --test "*" --all-features -- --nocapture
            
            # 清理
            docker-compose -f docker-compose.test.yml down -v
        '''
    }
}
````

**docker-compose.test.yml**:

````yaml
version: '3.8'
services:
  postgres:
    image: postgres:16
    environment:
      POSTGRES_PASSWORD: password
      POSTGRES_DB: testdb
    ports:
      - "5432:5432"

  redis:
    image: redis:7
    ports:
      - "6379:6379"

  jaeger:
    image: jaegertracing/all-in-one:latest
    environment:
      COLLECTOR_OTLP_ENABLED: "true"
    ports:
      - "4317:4317"
      - "16686:16686"
````

### 5.3 测试覆盖率

````groovy
stage('Test Coverage') {
    steps {
        sh '''
            # 安装 cargo-llvm-cov (如果未安装)
            cargo install cargo-llvm-cov || true
            
            # 生成覆盖率报告
            cargo llvm-cov --all-features --lcov --output-path lcov.info
            cargo llvm-cov report --html --output-dir coverage
        '''
    }
    post {
        always {
            // 发布覆盖率报告
            publishHTML([
                reportDir: 'coverage',
                reportFiles: 'index.html',
                reportName: 'Code Coverage Report'
            ])
            
            // 发布到 Codecov (可选)
            sh '''
                curl -s https://codecov.io/bash | bash -s -- \
                    -f lcov.info \
                    -t ${CODECOV_TOKEN}
            '''
        }
    }
}
````

---

## 6. OTLP 集成测试

### 6.1 启动 Jaeger

````groovy
stage('Start OTLP Stack') {
    steps {
        sh '''
            docker run -d --name jaeger \
                -e COLLECTOR_OTLP_ENABLED=true \
                -p 4317:4317 \
                -p 16686:16686 \
                jaegertracing/all-in-one:latest
            
            # 等待 Jaeger 就绪
            sleep 5
        '''
    }
}
````

### 6.2 运行集成测试

````groovy
stage('OTLP Integration Tests') {
    environment {
        OTEL_EXPORTER_OTLP_ENDPOINT = 'http://localhost:4317'
        RUST_LOG = 'debug'
    }
    steps {
        sh '''
            cargo test --test otlp_integration -- --nocapture
            
            # 验证 Trace 数据
            curl -s http://localhost:16686/api/services | jq .
        '''
    }
    post {
        always {
            sh 'docker stop jaeger && docker rm jaeger || true'
        }
    }
}
````

---

## 7. 性能测试

### 7.1 Criterion 基准测试

````groovy
stage('Benchmark') {
    steps {
        sh '''
            cargo bench --bench "*" -- --output-format bencher \
                | tee bench-output.txt
        '''
    }
    post {
        always {
            // 发布基准测试结果
            publishHTML([
                reportDir: 'target/criterion',
                reportFiles: 'report/index.html',
                reportName: 'Criterion Benchmark Report'
            ])
        }
    }
}
````

### 7.2 结果发布

````groovy
stage('Publish Benchmark Results') {
    steps {
        script {
            // 解析 Criterion 输出
            def benchResults = readFile('bench-output.txt')
            
            // 发送到性能监控系统
            sh """
                curl -X POST http://performance-tracker/api/results \
                    -H 'Content-Type: application/json' \
                    -d '${benchResults}'
            """
        }
    }
}
````

---

## 8. Docker 构建与发布

### 8.1 多阶段 Dockerfile

````dockerfile
# Stage 1: Build
FROM rust:1.90-slim AS builder

WORKDIR /app
COPY . .

RUN cargo build --release

# Stage 2: Runtime
FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

COPY --from=builder /app/target/release/my-app /usr/local/bin/

EXPOSE 8080

ENTRYPOINT ["my-app"]
````

### 8.2 镜像推送

````groovy
stage('Build Docker Image') {
    steps {
        script {
            def app = docker.build("my-registry/my-app:${env.BUILD_ID}")
            
            docker.withRegistry('https://my-registry', 'docker-credentials') {
                app.push("${env.BUILD_ID}")
                app.push("latest")
            }
        }
    }
}
````

---

## 9. 自动化部署

### 9.1 部署到 Kubernetes

````groovy
stage('Deploy to Kubernetes') {
    when {
        branch 'main'
    }
    steps {
        script {
            sh """
                kubectl set image deployment/my-app \
                    my-app=my-registry/my-app:${env.BUILD_ID} \
                    --namespace=production
                
                kubectl rollout status deployment/my-app \
                    --namespace=production \
                    --timeout=5m
            """
        }
    }
}
````

### 9.2 部署到 Docker Swarm

````groovy
stage('Deploy to Swarm') {
    steps {
        sh """
            docker stack deploy -c docker-stack.yml my-app \
                --with-registry-auth
        """
    }
}
````

---

## 10. 通知与报告

### 10.1 Slack 通知

````groovy
post {
    success {
        slackSend(
            color: 'good',
            message: "Build Successful: ${env.JOB_NAME} #${env.BUILD_NUMBER}\n${env.BUILD_URL}"
        )
    }
    failure {
        slackSend(
            color: 'danger',
            message: "Build Failed: ${env.JOB_NAME} #${env.BUILD_NUMBER}\n${env.BUILD_URL}"
        )
    }
}
````

### 10.2 Email 通知

````groovy
post {
    failure {
        emailext(
            subject: "Build Failed: ${env.JOB_NAME} #${env.BUILD_NUMBER}",
            body: """
                <p>Build Status: <b>FAILED</b></p>
                <p>Job: ${env.JOB_NAME}</p>
                <p>Build Number: ${env.BUILD_NUMBER}</p>
                <p>Build URL: <a href="${env.BUILD_URL}">${env.BUILD_URL}</a></p>
            """,
            to: '${DEFAULT_RECIPIENTS}',
            mimeType: 'text/html'
        )
    }
}
````

### 10.3 测试报告

````groovy
post {
    always {
        junit 'target/test-results/**/*.xml'
        
        publishHTML([
            reportDir: 'target/coverage',
            reportFiles: 'index.html',
            reportName: 'Coverage Report',
            allowMissing: true
        ])
        
        archiveArtifacts artifacts: 'target/release/my-app', fingerprint: true
    }
}
````

---

## 11. 缓存优化

### 11.1 Cargo 缓存

````groovy
pipeline {
    agent {
        docker {
            image 'rust:1.90-slim'
            args '''
                -v cargo-cache:/usr/local/cargo/registry
                -v cargo-git:/usr/local/cargo/git
            '''
        }
    }
    
    environment {
        CARGO_HOME = '/usr/local/cargo'
    }
    
    // ...
}
````

### 11.2 sccache 配置

````groovy
environment {
    RUSTC_WRAPPER = 'sccache'
    SCCACHE_DIR = '/cache/sccache'
    SCCACHE_CACHE_SIZE = '10G'
}

stages {
    stage('Build with sccache') {
        steps {
            sh '''
                sccache --start-server || true
                cargo build --release
                sccache --show-stats
            '''
        }
    }
}
````

---

## 12. 完整示例

### 12.1 生产级 Jenkinsfile

````groovy
pipeline {
    agent {
        docker {
            image 'rust-ci:latest'
            args '''
                -v cargo-cache:/usr/local/cargo/registry
                -v sccache:/cache/sccache
                -v /var/run/docker.sock:/var/run/docker.sock
            '''
        }
    }

    environment {
        CARGO_HOME = '/usr/local/cargo'
        RUSTC_WRAPPER = 'sccache'
        SCCACHE_DIR = '/cache/sccache'
        RUSTFLAGS = '-D warnings'
        OTEL_EXPORTER_OTLP_ENDPOINT = 'http://jaeger:4317'
    }

    options {
        timestamps()
        timeout(time: 1, unit: 'HOURS')
        buildDiscarder(logRotator(numToKeepStr: '30'))
    }

    stages {
        stage('Checkout') {
            steps {
                checkout scm
                sh 'git submodule update --init --recursive'
            }
        }

        stage('Setup') {
            steps {
                sh '''
                    rustc --version
                    cargo --version
                    sccache --start-server || true
                '''
            }
        }

        stage('Check') {
            parallel {
                stage('Format') {
                    steps {
                        sh 'cargo fmt -- --check'
                    }
                }
                stage('Clippy') {
                    steps {
                        sh 'cargo clippy --all-targets --all-features -- -D warnings'
                    }
                }
                stage('Audit') {
                    steps {
                        sh 'cargo audit || true'
                        sh 'cargo deny check || true'
                    }
                }
            }
        }

        stage('Build') {
            steps {
                sh 'cargo build --release --all-features'
            }
        }

        stage('Test') {
            parallel {
                stage('Unit Tests') {
                    steps {
                        sh 'cargo test --lib --all-features -- --nocapture'
                    }
                }
                stage('Integration Tests') {
                    steps {
                        sh '''
                            docker-compose -f docker-compose.test.yml up -d
                            sleep 10
                            cargo test --test "*" --all-features -- --nocapture
                            docker-compose -f docker-compose.test.yml down -v
                        '''
                    }
                }
                stage('Coverage') {
                    steps {
                        sh '''
                            cargo llvm-cov --all-features --lcov --output-path lcov.info
                            cargo llvm-cov report --html --output-dir coverage
                        '''
                    }
                }
            }
        }

        stage('Benchmark') {
            when {
                branch 'main'
            }
            steps {
                sh 'cargo bench --bench "*" -- --output-format bencher'
            }
        }

        stage('Docker Build') {
            when {
                branch 'main'
            }
            steps {
                script {
                    def app = docker.build("my-registry/my-app:${env.BUILD_ID}")
                    docker.withRegistry('https://my-registry', 'docker-credentials') {
                        app.push("${env.BUILD_ID}")
                        app.push("latest")
                    }
                }
            }
        }

        stage('Deploy') {
            when {
                branch 'main'
            }
            steps {
                sh """
                    kubectl set image deployment/my-app \
                        my-app=my-registry/my-app:${env.BUILD_ID} \
                        --namespace=production
                    kubectl rollout status deployment/my-app \
                        --namespace=production
                """
            }
        }
    }

    post {
        always {
            sh 'sccache --show-stats'
            
            junit 'target/test-results/**/*.xml'
            
            publishHTML([
                reportDir: 'coverage',
                reportFiles: 'index.html',
                reportName: 'Coverage Report'
            ])
            
            publishHTML([
                reportDir: 'target/criterion',
                reportFiles: 'report/index.html',
                reportName: 'Benchmark Report'
            ])
            
            archiveArtifacts artifacts: 'target/release/my-app', fingerprint: true
            
            cleanWs()
        }
        success {
            slackSend(
                color: 'good',
                message: "✅ Build Successful: ${env.JOB_NAME} #${env.BUILD_NUMBER}"
            )
        }
        failure {
            slackSend(
                color: 'danger',
                message: "❌ Build Failed: ${env.JOB_NAME} #${env.BUILD_NUMBER}\n${env.BUILD_URL}"
            )
        }
    }
}
````

### 12.2 多分支 Pipeline

````groovy
// Multibranch Pipeline - Jenkinsfile
pipeline {
    agent none

    stages {
        stage('Build') {
            agent {
                docker {
                    image 'rust-ci:latest'
                }
            }
            steps {
                sh 'cargo build --all-features'
            }
        }

        stage('Test') {
            agent {
                docker {
                    image 'rust-ci:latest'
                }
            }
            steps {
                sh 'cargo test --all-features'
            }
        }

        stage('Deploy to Staging') {
            when {
                branch 'develop'
            }
            agent any
            steps {
                sh 'kubectl apply -f k8s/staging/'
            }
        }

        stage('Deploy to Production') {
            when {
                branch 'main'
            }
            agent any
            steps {
                input message: 'Deploy to Production?', ok: 'Deploy'
                sh 'kubectl apply -f k8s/production/'
            }
        }
    }
}
````

---

## 总结

### 核心要点

1. **Docker Agent**: 使用 Docker 提供一致的构建环境
2. **并行执行**: 利用 `parallel` 加速构建流程
3. **缓存优化**: 使用 Cargo 缓存和 sccache 加速编译
4. **质量检查**: 集成 rustfmt、clippy、cargo-audit
5. **测试覆盖率**: 使用 cargo-llvm-cov 生成覆盖率报告
6. **OTLP 测试**: 集成 Jaeger 测试 OTLP 功能
7. **自动部署**: 支持 Kubernetes/Docker Swarm 部署
8. **通知机制**: Slack/Email 通知构建状态

### 性能优化

| 优化项 | 加速效果 | 说明 |
|--------|---------|------|
| Cargo 缓存 | 3-5x | 缓存依赖下载 |
| sccache | 2-3x | 缓存编译结果 |
| 并行执行 | 2x | 同时运行多个 stage |
| Docker 层缓存 | 2x | 复用 Docker 镜像层 |

### 最佳实践清单

- ✅ 使用 Docker Agent 保证环境一致性
- ✅ 配置 Cargo 和 sccache 缓存
- ✅ 并行执行测试和检查
- ✅ 集成代码质量工具 (fmt, clippy, audit)
- ✅ 生成测试覆盖率报告
- ✅ 运行 OTLP 集成测试
- ✅ 自动化 Docker 构建和推送
- ✅ 实现 Kubernetes 自动部署
- ✅ 配置 Slack/Email 通知
- ✅ 保留构建产物和报告
- ✅ 设置构建超时和清理
- ✅ 多分支 Pipeline 支持

---

**相关文档**:

- [GitHub Actions 完整配置](./01_GitHub_Actions_Rust完整配置.md)
- [GitLab CI 完整配置](./02_GitLab_CI_Rust完整配置.md)
- [Docker 部署完整指南](./03_Docker_部署_Rust完整指南.md)
- [Rust工具链完整配置](../31_开发工具链/01_Rust工具链完整配置.md)
