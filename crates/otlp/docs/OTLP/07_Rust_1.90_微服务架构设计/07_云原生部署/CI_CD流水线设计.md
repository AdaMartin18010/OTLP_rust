# CI/CD 流水线设计

## 目录

- [CI/CD 流水线设计](#cicd-流水线设计)
  - [目录](#目录)
  - [📋 概述](#-概述)
  - [🎯 CI/CD 流水线架构](#-cicd-流水线架构)
  - [🔨 持续集成 (CI)](#-持续集成-ci)
  - [🚀 持续部署 (CD)](#-持续部署-cd)
  - [🔒 安全扫描](#-安全扫描)
  - [📊 流水线监控](#-流水线监控)
  - [🎯 最佳实践](#-最佳实践)

## 📋 概述

CI/CD 流水线是现代软件交付的核心,通过自动化构建、测试、部署流程,实现快速、可靠的软件发布。

## 🎯 CI/CD 流水线架构

```yaml
# GitHub Actions CI/CD 流水线
name: Rust Microservice CI/CD

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main ]

env:
  CARGO_TERM_COLOR: always
  RUST_VERSION: "1.90"

jobs:
  # 阶段 1: 代码检查
  lint:
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v3
    - uses: actions-rs/toolchain@v1
      with:
        toolchain: ${{ env.RUST_VERSION }}
        components: rustfmt, clippy
    - name: Format check
      run: cargo fmt -- --check
    - name: Clippy check
      run: cargo clippy -- -D warnings

  # 阶段 2: 单元测试
  test:
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v3
    - uses: actions-rs/toolchain@v1
      with:
        toolchain: ${{ env.RUST_VERSION }}
    - name: Run tests
      run: cargo test --all-features
    - name: Generate coverage
      run: |
        cargo install cargo-tarpaulin
        cargo tarpaulin --out Xml
    - name: Upload coverage
      uses: codecov/codecov-action@v3

  # 阶段 3: 构建
  build:
    needs: [lint, test]
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v3
    - uses: actions-rs/toolchain@v1
      with:
        toolchain: ${{ env.RUST_VERSION }}
    - name: Build release
      run: cargo build --release
    - name: Upload artifact
      uses: actions/upload-artifact@v3
      with:
        name: binary
        path: target/release/my-service

  # 阶段 4: Docker 镜像构建
  docker:
    needs: build
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v3
    - name: Set up Docker Buildx
      uses: docker/setup-buildx-action@v2
    - name: Login to Registry
      uses: docker/login-action@v2
      with:
        registry: ghcr.io
        username: ${{ github.actor }}
        password: ${{ secrets.GITHUB_TOKEN }}
    - name: Build and push
      uses: docker/build-push-action@v4
      with:
        context: .
        push: true
        tags: |
          ghcr.io/${{ github.repository }}:${{ github.sha }}
          ghcr.io/${{ github.repository }}:latest
        cache-from: type=gha
        cache-to: type=gha,mode=max

  # 阶段 5: 安全扫描
  security:
    needs: docker
    runs-on: ubuntu-latest
    steps:
    - name: Run Trivy scanner
      uses: aquasecurity/trivy-action@master
      with:
        image-ref: ghcr.io/${{ github.repository }}:${{ github.sha }}
        format: 'sarif'
        output: 'trivy-results.sarif'
    - name: Upload results
      uses: github/codeql-action/upload-sarif@v2
      with:
        sarif_file: 'trivy-results.sarif'

  # 阶段 6: 部署到开发环境
  deploy-dev:
    needs: [docker, security]
    runs-on: ubuntu-latest
    if: github.ref == 'refs/heads/develop'
    steps:
    - uses: actions/checkout@v3
    - name: Deploy to Dev
      run: |
        kubectl set image deployment/my-service \
          my-service=ghcr.io/${{ github.repository }}:${{ github.sha }} \
          --namespace=dev

  # 阶段 7: 部署到生产环境
  deploy-prod:
    needs: [docker, security]
    runs-on: ubuntu-latest
    if: github.ref == 'refs/heads/main'
    environment: production
    steps:
    - uses: actions/checkout@v3
    - name: Deploy to Production
      run: |
        kubectl set image deployment/my-service \
          my-service=ghcr.io/${{ github.repository }}:${{ github.sha }} \
          --namespace=prod
```

## 🔨 持续集成 (CI)

```rust
/// CI 流水线配置
pub struct CiPipeline {
    pub stages: Vec<CiStage>,
}

#[derive(Debug, Clone)]
pub enum CiStage {
    Lint {
        tools: Vec<LintTool>,
    },
    Test {
        test_types: Vec<TestType>,
        coverage_threshold: f64,
    },
    Build {
        target: BuildTarget,
        optimization: OptimizationLevel,
    },
    Audit {
        checks: Vec<AuditCheck>,
    },
}

#[derive(Debug, Clone)]
pub enum LintTool {
    Rustfmt,
    Clippy,
    CargoCheck,
}

#[derive(Debug, Clone)]
pub enum TestType {
    Unit,
    Integration,
    E2E,
    Performance,
}

impl CiPipeline {
    /// 创建标准 CI 流水线
    pub fn standard() -> Self {
        Self {
            stages: vec![
                CiStage::Lint {
                    tools: vec![
                        LintTool::Rustfmt,
                        LintTool::Clippy,
                        LintTool::CargoCheck,
                    ],
                },
                CiStage::Test {
                    test_types: vec![
                        TestType::Unit,
                        TestType::Integration,
                    ],
                    coverage_threshold: 80.0,
                },
                CiStage::Build {
                    target: BuildTarget::Release,
                    optimization: OptimizationLevel::Level3,
                },
                CiStage::Audit {
                    checks: vec![
                        AuditCheck::Dependencies,
                        AuditCheck::Security,
                        AuditCheck::License,
                    ],
                },
            ],
        }
    }
}
```

## 🚀 持续部署 (CD)

```rust
/// CD 流水线配置
pub struct CdPipeline {
    pub environments: Vec<DeploymentEnvironment>,
    pub strategy: DeploymentStrategy,
}

#[derive(Debug, Clone)]
pub struct DeploymentEnvironment {
    pub name: String,
    pub namespace: String,
    pub replicas: u32,
    pub auto_approve: bool,
}

#[derive(Debug, Clone)]
pub enum DeploymentStrategy {
    RollingUpdate {
        max_surge: u32,
        max_unavailable: u32,
    },
    BlueGreen,
    Canary {
        steps: Vec<CanaryStep>,
    },
}

#[derive(Debug, Clone)]
pub struct CanaryStep {
    pub weight: u32,
    pub duration: Duration,
}

impl CdPipeline {
    /// 创建生产环境 CD 流水线
    pub fn production() -> Self {
        Self {
            environments: vec![
                DeploymentEnvironment {
                    name: "dev".to_string(),
                    namespace: "dev".to_string(),
                    replicas: 2,
                    auto_approve: true,
                },
                DeploymentEnvironment {
                    name: "staging".to_string(),
                    namespace: "staging".to_string(),
                    replicas: 3,
                    auto_approve: true,
                },
                DeploymentEnvironment {
                    name: "production".to_string(),
                    namespace: "prod".to_string(),
                    replicas: 10,
                    auto_approve: false,
                },
            ],
            strategy: DeploymentStrategy::Canary {
                steps: vec![
                    CanaryStep {
                        weight: 10,
                        duration: Duration::from_secs(300),
                    },
                    CanaryStep {
                        weight: 50,
                        duration: Duration::from_secs(600),
                    },
                    CanaryStep {
                        weight: 100,
                        duration: Duration::from_secs(0),
                    },
                ],
            },
        }
    }
}
```

## 🔒 安全扫描

```bash
# 依赖安全审计
cargo audit

# 容器镜像扫描
trivy image my-service:latest

# 代码静态分析
cargo clippy -- -D warnings
```

## 📊 流水线监控

```rust
/// 流水线指标收集
pub struct PipelineMetrics {
    pub build_duration: Histogram,
    pub test_duration: Histogram,
    pub deploy_duration: Histogram,
    pub success_rate: Counter,
    pub failure_rate: Counter,
}

impl PipelineMetrics {
    /// 记录流水线执行
    pub fn record_pipeline_run(&self, result: PipelineResult) {
        match result.status {
            PipelineStatus::Success => {
                self.success_rate.inc();
                self.build_duration.observe(result.build_duration.as_secs_f64());
                self.test_duration.observe(result.test_duration.as_secs_f64());
                self.deploy_duration.observe(result.deploy_duration.as_secs_f64());
            }
            PipelineStatus::Failed => {
                self.failure_rate.inc();
            }
        }
    }
}
```

## 🎯 最佳实践

1. **快速反馈**: CI 流水线应在 10 分钟内完成
2. **并行执行**: 尽可能并行化测试和构建
3. **缓存优化**: 使用缓存加速构建
4. **渐进式部署**: 使用金丝雀或蓝绿部署
5. **自动回滚**: 检测到问题时自动回滚

---

**总结**: 完善的 CI/CD 流水线是实现快速、可靠软件交付的基础。
