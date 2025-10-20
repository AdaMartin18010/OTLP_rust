# GitLab CI Rust 完整配置指南

## 目录

- [GitLab CI Rust 完整配置指南](#gitlab-ci-rust-完整配置指南)
  - [目录](#目录)
  - [一、GitLab CI 架构与概述](#一gitlab-ci-架构与概述)
    - [1.1 GitLab CI/CD 流程](#11-gitlab-cicd-流程)
    - [1.2 关键概念](#12-关键概念)
  - [二、基础 CI 配置](#二基础-ci-配置)
    - [2.1 基本结构](#21-基本结构)
  - [三、多平台测试](#三多平台测试)
    - [3.1 多操作系统](#31-多操作系统)
    - [3.2 多 Rust 版本](#32-多-rust-版本)
  - [四、代码质量检查](#四代码质量检查)
    - [4.1 Clippy + Rustfmt](#41-clippy--rustfmt)
    - [4.2 依赖审计](#42-依赖审计)
  - [五、测试覆盖率](#五测试覆盖率)
    - [5.1 cargo-llvm-cov](#51-cargo-llvm-cov)
    - [5.2 Codecov 集成](#52-codecov-集成)
  - [六、OTLP 集成测试](#六otlp-集成测试)
    - [6.1 Jaeger + OTLP](#61-jaeger--otlp)
  - [七、性能基准测试](#七性能基准测试)
    - [7.1 Criterion 基准](#71-criterion-基准)
    - [7.2 性能对比](#72-性能对比)
  - [八、安全审计](#八安全审计)
    - [8.1 cargo-audit](#81-cargo-audit)
    - [8.2 cargo-deny](#82-cargo-deny)
  - [九、Docker 构建与发布](#九docker-构建与发布)
    - [9.1 多阶段构建](#91-多阶段构建)
    - [9.2 Dockerfile 优化](#92-dockerfile-优化)
  - [十、自动化发布](#十自动化发布)
    - [10.1 语义化版本](#101-语义化版本)
    - [10.2 Crates.io 发布](#102-cratesio-发布)
  - [十一、缓存优化](#十一缓存优化)
    - [11.1 Cargo 缓存](#111-cargo-缓存)
    - [11.2 sccache 加速](#112-sccache-加速)
  - [十二、完整 .gitlab-ci.yml 示例](#十二完整-gitlab-ciyml-示例)
    - [12.1 生产级配置](#121-生产级配置)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [最佳实践](#最佳实践)
    - [性能优化](#性能优化)
    - [常见问题](#常见问题)

---

## 一、GitLab CI 架构与概述

### 1.1 GitLab CI/CD 流程

````text
┌─────────────────────────────────────────┐
│          GitLab CI/CD Pipeline          │
├─────────────────────────────────────────┤
│  Stages:                                │
│    1. build    (编译检查)               │
│    2. test     (单元测试)               │
│    3. lint     (代码质量)               │
│    4. coverage (测试覆盖)               │
│    5. deploy   (部署发布)               │
└─────────────────────────────────────────┘
````

### 1.2 关键概念

- **Stages**：阶段（顺序执行）
- **Jobs**：任务（同一阶段并行执行）
- **Runners**：执行器（Docker、Shell、Kubernetes）
- **Cache**：缓存（加速构建）
- **Artifacts**：制品（跨任务传递）

---

## 二、基础 CI 配置

### 2.1 基本结构

````yaml
# .gitlab-ci.yml

# Docker 镜像
image: rust:1.90

# 定义阶段
stages:
  - check
  - test
  - deploy

# 全局变量
variables:
  CARGO_HOME: $CI_PROJECT_DIR/.cargo
  RUST_BACKTRACE: "1"

# 缓存配置
cache:
  key:
    files:
      - Cargo.lock
  paths:
    - .cargo/
    - target/

# 前置脚本
before_script:
  - rustc --version
  - cargo --version
  - apt-get update && apt-get install -y protobuf-compiler

# 格式检查
fmt:
  stage: check
  script:
    - rustup component add rustfmt
    - cargo fmt -- --check
  allow_failure: false

# Clippy 检查
clippy:
  stage: check
  script:
    - rustup component add clippy
    - cargo clippy --all-targets --all-features -- -D warnings
  allow_failure: false

# 编译检查
build:
  stage: check
  script:
    - cargo build --verbose
  artifacts:
    paths:
      - target/debug/
    expire_in: 1 hour

# 单元测试
test:
  stage: test
  script:
    - cargo test --verbose
  dependencies:
    - build
````

---

## 三、多平台测试

### 3.1 多操作系统

````yaml
# 测试矩阵
.test_template: &test_template
  stage: test
  script:
    - cargo test --verbose --all-features

test:linux:
  <<: *test_template
  image: rust:1.90
  tags:
    - linux

test:macos:
  <<: *test_template
  tags:
    - macos
  before_script:
    - curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
    - source $HOME/.cargo/env

test:windows:
  <<: *test_template
  tags:
    - windows
  before_script:
    - choco install rust
````

### 3.2 多 Rust 版本

````yaml
# Rust 版本矩阵
.test_rust_version: &test_rust_version
  stage: test
  script:
    - cargo test --verbose

test:rust-1.90:
  <<: *test_rust_version
  image: rust:1.90

test:rust-stable:
  <<: *test_rust_version
  image: rust:latest

test:rust-nightly:
  <<: *test_rust_version
  image: rustlang/rust:nightly
  allow_failure: true
````

---

## 四、代码质量检查

### 4.1 Clippy + Rustfmt

````yaml
# 代码质量阶段
lint:
  stage: lint
  script:
    - rustup component add clippy rustfmt
    - cargo fmt -- --check
    - cargo clippy --all-targets --all-features -- -D warnings
    - cargo doc --no-deps --document-private-items
  artifacts:
    paths:
      - target/doc/
    expire_in: 7 days
````

### 4.2 依赖审计

````yaml
# 安全审计
audit:
  stage: lint
  script:
    - cargo install cargo-audit
    - cargo audit
  allow_failure: true
````

---

## 五、测试覆盖率

### 5.1 cargo-llvm-cov

````yaml
# 代码覆盖率
coverage:
  stage: test
  image: rust:1.90
  before_script:
    - apt-get update && apt-get install -y protobuf-compiler
    - cargo install cargo-llvm-cov
  script:
    - cargo llvm-cov --all-features --lcov --output-path lcov.info
    - cargo llvm-cov report --html
  coverage: '/\d+\.\d+% coverage/'
  artifacts:
    paths:
      - lcov.info
      - target/llvm-cov/html/
    reports:
      coverage_report:
        coverage_format: cobertura
        path: lcov.info
    expire_in: 30 days
````

### 5.2 Codecov 集成

````yaml
# 上传到 Codecov
coverage:upload:
  stage: test
  needs:
    - coverage
  script:
    - curl -Os https://uploader.codecov.io/latest/linux/codecov
    - chmod +x codecov
    - ./codecov -t $CODECOV_TOKEN -f lcov.info
  only:
    - main
    - develop
````

---

## 六、OTLP 集成测试

### 6.1 Jaeger + OTLP

````yaml
# OTLP 集成测试
test:otlp:
  stage: test
  image: rust:1.90
  services:
    - name: jaegertracing/all-in-one:1.66
      alias: jaeger
  variables:
    OTLP_ENDPOINT: "http://jaeger:4317"
    COLLECTOR_OTLP_ENABLED: "true"
  before_script:
    - apt-get update && apt-get install -y protobuf-compiler
  script:
    - cargo test --test integration_tests -- --test-threads=1
    - cargo run --example otlp_example
  after_script:
    # 验证追踪数据
    - curl http://jaeger:16686/api/traces?service=rust-otlp-test
````

---

## 七、性能基准测试

### 7.1 Criterion 基准

````yaml
# 性能基准测试
benchmark:
  stage: test
  image: rust:1.90
  script:
    - cargo bench --bench otlp_benchmark -- --output-format bencher | tee output.txt
  artifacts:
    paths:
      - target/criterion/
      - output.txt
    expire_in: 30 days
  only:
    - main
    - develop
````

### 7.2 性能对比

````yaml
# 性能回归检测
benchmark:compare:
  stage: test
  script:
    - cargo install cargo-criterion
    - cargo criterion --message-format=json > new.json
    - wget $CI_API_V4_URL/projects/$CI_PROJECT_ID/jobs/artifacts/main/raw/old.json?job=benchmark -O old.json
    - cargo criterion --compare old.json new.json
  artifacts:
    paths:
      - new.json
    expire_in: 30 days
  only:
    - main
````

---

## 八、安全审计

### 8.1 cargo-audit

````yaml
# 依赖安全扫描
security:audit:
  stage: lint
  script:
    - cargo install cargo-audit
    - cargo audit --json > audit.json
  artifacts:
    paths:
      - audit.json
    expire_in: 7 days
  allow_failure: true
````

### 8.2 cargo-deny

````yaml
# 依赖许可证检查
security:deny:
  stage: lint
  script:
    - cargo install cargo-deny
    - cargo deny check licenses
    - cargo deny check bans
    - cargo deny check sources
  allow_failure: true
````

---

## 九、Docker 构建与发布

### 9.1 多阶段构建

````yaml
# Docker 镜像构建
docker:build:
  stage: deploy
  image: docker:27
  services:
    - docker:27-dind
  variables:
    DOCKER_DRIVER: overlay2
    DOCKER_TLS_CERTDIR: "/certs"
  before_script:
    - docker login -u $CI_REGISTRY_USER -p $CI_REGISTRY_PASSWORD $CI_REGISTRY
  script:
    - docker build -t $CI_REGISTRY_IMAGE:$CI_COMMIT_SHORT_SHA .
    - docker build -t $CI_REGISTRY_IMAGE:latest .
    - docker push $CI_REGISTRY_IMAGE:$CI_COMMIT_SHORT_SHA
    - docker push $CI_REGISTRY_IMAGE:latest
  only:
    - main
    - tags
````

### 9.2 Dockerfile 优化

````dockerfile
# 多阶段构建
FROM rust:1.90 as builder

WORKDIR /app
COPY Cargo.toml Cargo.lock ./
RUN mkdir src && echo "fn main() {}" > src/main.rs
RUN cargo build --release
RUN rm -rf src

COPY src ./src
RUN touch src/main.rs
RUN cargo build --release

# 最小化镜像
FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

COPY --from=builder /app/target/release/myapp /usr/local/bin/

EXPOSE 8000
CMD ["myapp"]
````

---

## 十、自动化发布

### 10.1 语义化版本

````yaml
# 自动发布
release:
  stage: deploy
  image: rust:1.90
  script:
    - cargo install cargo-release
    - cargo release --execute --no-confirm
  only:
    - tags
  when: manual
````

### 10.2 Crates.io 发布

````yaml
# 发布到 crates.io
publish:crates:
  stage: deploy
  script:
    - cargo login $CRATES_IO_TOKEN
    - cargo publish
  only:
    - tags
  when: manual
````

---

## 十一、缓存优化

### 11.1 Cargo 缓存

````yaml
# 优化缓存策略
.cargo_cache: &cargo_cache
  cache:
    key:
      files:
        - Cargo.lock
      prefix: $CI_COMMIT_REF_SLUG
    paths:
      - .cargo/bin/
      - .cargo/registry/index/
      - .cargo/registry/cache/
      - .cargo/git/db/
      - target/

# 构建任务
build:optimized:
  <<: *cargo_cache
  stage: check
  script:
    - cargo build --release
````

### 11.2 sccache 加速

````yaml
# 使用 sccache
.sccache: &sccache
  variables:
    RUSTC_WRAPPER: sccache
    SCCACHE_DIR: $CI_PROJECT_DIR/.sccache
  before_script:
    - apt-get update && apt-get install -y wget
    - wget https://github.com/mozilla/sccache/releases/download/v0.9.4/sccache-v0.9.4-x86_64-unknown-linux-musl.tar.gz
    - tar xzf sccache-v0.9.4-x86_64-unknown-linux-musl.tar.gz
    - mv sccache-v0.9.4-x86_64-unknown-linux-musl/sccache /usr/local/bin/
  cache:
    key: sccache-$CI_COMMIT_REF_SLUG
    paths:
      - .sccache/

build:sccache:
  <<: *sccache
  stage: check
  script:
    - cargo build --release
    - sccache --show-stats
````

---

## 十二、完整 .gitlab-ci.yml 示例

### 12.1 生产级配置

````yaml
# .gitlab-ci.yml - 完整配置

image: rust:1.90

stages:
  - check
  - test
  - lint
  - coverage
  - deploy

variables:
  CARGO_HOME: $CI_PROJECT_DIR/.cargo
  RUST_BACKTRACE: "1"

# 全局缓存
cache: &global_cache
  key:
    files:
      - Cargo.lock
  paths:
    - .cargo/
    - target/

# 前置脚本
before_script:
  - rustc --version
  - cargo --version
  - apt-get update && apt-get install -y protobuf-compiler

# === CHECK 阶段 ===

fmt:
  stage: check
  script:
    - rustup component add rustfmt
    - cargo fmt -- --check

clippy:
  stage: check
  script:
    - rustup component add clippy
    - cargo clippy --all-targets --all-features -- -D warnings

build:
  stage: check
  script:
    - cargo build --release
  artifacts:
    paths:
      - target/release/
    expire_in: 1 hour

# === TEST 阶段 ===

test:unit:
  stage: test
  script:
    - cargo test --lib --bins
  coverage: '/\d+\.\d+% coverage/'

test:integration:
  stage: test
  services:
    - name: jaegertracing/all-in-one:1.66
      alias: jaeger
  variables:
    OTLP_ENDPOINT: "http://jaeger:4317"
  script:
    - cargo test --test '*'

test:doc:
  stage: test
  script:
    - cargo test --doc

# === LINT 阶段 ===

audit:
  stage: lint
  script:
    - cargo install cargo-audit
    - cargo audit
  allow_failure: true

deny:
  stage: lint
  script:
    - cargo install cargo-deny
    - cargo deny check
  allow_failure: true

# === COVERAGE 阶段 ===

coverage:
  stage: coverage
  before_script:
    - apt-get update && apt-get install -y protobuf-compiler
    - cargo install cargo-llvm-cov
  script:
    - cargo llvm-cov --all-features --lcov --output-path lcov.info
  coverage: '/\d+\.\d+% coverage/'
  artifacts:
    paths:
      - lcov.info
    reports:
      coverage_report:
        coverage_format: cobertura
        path: lcov.info

# === DEPLOY 阶段 ===

docker:build:
  stage: deploy
  image: docker:27
  services:
    - docker:27-dind
  before_script:
    - docker login -u $CI_REGISTRY_USER -p $CI_REGISTRY_PASSWORD $CI_REGISTRY
  script:
    - docker build -t $CI_REGISTRY_IMAGE:$CI_COMMIT_SHORT_SHA .
    - docker build -t $CI_REGISTRY_IMAGE:latest .
    - docker push $CI_REGISTRY_IMAGE:$CI_COMMIT_SHORT_SHA
    - docker push $CI_REGISTRY_IMAGE:latest
  only:
    - main
    - tags

release:
  stage: deploy
  script:
    - cargo install cargo-release
    - cargo release --execute --no-confirm
  only:
    - tags
  when: manual
````

---

## 总结

### 核心要点

1. **完整流水线**：检查、测试、部署全覆盖
2. **多平台支持**：Linux、macOS、Windows
3. **质量保障**：格式、Clippy、测试覆盖、安全审计
4. **OTLP 集成**：Jaeger 集成测试
5. **自动化发布**：Docker、Crates.io

### 最佳实践

- 使用 Docker 镜像统一环境
- 合理配置缓存加速构建
- 并行执行独立任务
- 使用 `artifacts` 传递制品
- 敏感信息使用 CI/CD 变量

### 性能优化

- **sccache**：编译缓存，减少重复编译
- **增量缓存**：保存 `target/` 和 `.cargo/`
- **并行测试**：`--jobs` 参数控制
- **条件执行**：`only`/`except` 限制触发
- **最小化镜像**：多阶段构建减少镜像体积

### 常见问题

1. **缓存失效**：检查 `Cargo.lock` 是否变更
2. **编译超时**：增加 Runner 资源或使用 sccache
3. **Docker 权限**：确保 Runner 有 Docker 权限
4. **依赖冲突**：使用 `cargo update` 更新依赖

---

**文档版本**: v1.0  
**最后更新**: 2025-10-09  
**Rust 版本**: 1.90+  
**GitLab CI**: 15.0+  
**OpenTelemetry 版本**: 0.31.0+
