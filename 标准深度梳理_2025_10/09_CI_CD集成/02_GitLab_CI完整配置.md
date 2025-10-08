# GitLab CI 完整配置 - Rust OTLP CI/CD

> **版本信息**
>
> - Rust: 1.90 (2024 Edition)
> - opentelemetry: 0.31.0
> - 更新日期: 2025-10-08
> - 适用场景: GitLab CI/CD Pipeline

## 目录

- [GitLab CI 完整配置 - Rust OTLP CI/CD](#gitlab-ci-完整配置---rust-otlp-cicd)
  - [目录](#目录)
  - [概述](#概述)
  - [1. 基础配置](#1-基础配置)
    - [1.1 完整 Pipeline](#11-完整-pipeline)
    - [1.2 多阶段构建](#12-多阶段构建)
  - [2. Docker-in-Docker 构建](#2-docker-in-docker-构建)
  - [3. 缓存优化](#3-缓存优化)
  - [4. 并行测试](#4-并行测试)
  - [5. 制品管理](#5-制品管理)
  - [6. 环境部署](#6-环境部署)
  - [7. 完整生产配置](#7-完整生产配置)
  - [总结](#总结)

---

## 概述

本文档提供 Rust OTLP 项目在 GitLab CI 的完整配置，包括：

- ✅ 多阶段 Pipeline（测试、构建、部署）
- ✅ Docker-in-Docker 构建
- ✅ 缓存优化
- ✅ 并行测试
- ✅ 制品管理
- ✅ 多环境部署

---

## 1. 基础配置

### 1.1 完整 Pipeline

`.gitlab-ci.yml`:

```yaml
# Rust OTLP CI/CD Pipeline

variables:
  RUST_VERSION: "1.90"
  CARGO_HOME: $CI_PROJECT_DIR/.cargo
  CARGO_TERM_COLOR: always

# 定义阶段
stages:
  - check
  - test
  - build
  - package
  - deploy

# 缓存配置
cache:
  key: ${CI_COMMIT_REF_SLUG}
  paths:
    - .cargo/
    - target/

# 默认配置
default:
  image: rust:${RUST_VERSION}
  before_script:
    - rustc --version
    - cargo --version

# ==================== 检查阶段 ====================

format:check:
  stage: check
  script:
    - rustup component add rustfmt
    - cargo fmt --all -- --check
  only:
    - merge_requests
    - main

clippy:check:
  stage: check
  script:
    - rustup component add clippy
    - cargo clippy --all-targets --all-features -- -D warnings
  only:
    - merge_requests
    - main

audit:check:
  stage: check
  script:
    - cargo install cargo-audit
    - cargo audit
  only:
    - merge_requests
    - main
  allow_failure: true

# ==================== 测试阶段 ====================

test:unit:
  stage: test
  services:
    - name: otel/opentelemetry-collector:latest
      alias: otel-collector
    - name: postgres:16
      alias: postgres
    - name: redis:7
      alias: redis
  variables:
    POSTGRES_DB: test
    POSTGRES_USER: postgres
    POSTGRES_PASSWORD: postgres
    OTEL_EXPORTER_OTLP_ENDPOINT: http://otel-collector:4317
    DATABASE_URL: postgres://postgres:postgres@postgres:5432/test
    REDIS_URL: redis://redis:6379
  script:
    - cargo test --lib --all-features --verbose
  coverage: '/^TOTAL.*\s+(\d+\.\d+)%/'
  artifacts:
    reports:
      junit: target/test-results.xml
      cobertura: cobertura.xml

test:integration:
  stage: test
  services:
    - name: otel/opentelemetry-collector:latest
      alias: otel-collector
    - name: postgres:16
      alias: postgres
  script:
    - cargo test --test '*' --all-features
  only:
    - merge_requests
    - main

test:doc:
  stage: test
  script:
    - cargo test --doc
  only:
    - merge_requests
    - main

# ==================== 构建阶段 ====================

build:debug:
  stage: build
  script:
    - cargo build --all-features
  artifacts:
    paths:
      - target/debug/my-app
    expire_in: 1 day
  only:
    - merge_requests

build:release:
  stage: build
  script:
    - cargo build --release --all-features
  artifacts:
    paths:
      - target/release/my-app
    expire_in: 1 week
  only:
    - main
    - tags

# ==================== 打包阶段 ====================

package:docker:
  stage: package
  image: docker:latest
  services:
    - docker:dind
  variables:
    DOCKER_DRIVER: overlay2
    DOCKER_TLS_CERTDIR: "/certs"
  before_script:
    - docker login -u $CI_REGISTRY_USER -p $CI_REGISTRY_PASSWORD $CI_REGISTRY
  script:
    - docker build -t $CI_REGISTRY_IMAGE:$CI_COMMIT_SHORT_SHA .
    - docker push $CI_REGISTRY_IMAGE:$CI_COMMIT_SHORT_SHA
    - |
      if [ "$CI_COMMIT_BRANCH" == "main" ]; then
        docker tag $CI_REGISTRY_IMAGE:$CI_COMMIT_SHORT_SHA $CI_REGISTRY_IMAGE:latest
        docker push $CI_REGISTRY_IMAGE:latest
      fi
  only:
    - main
    - tags

# ==================== 部署阶段 ====================

deploy:staging:
  stage: deploy
  image: alpine:latest
  before_script:
    - apk add --no-cache curl
  script:
    - echo "Deploying to staging environment"
    - curl -X POST $STAGING_WEBHOOK_URL
  environment:
    name: staging
    url: https://staging.example.com
  only:
    - main

deploy:production:
  stage: deploy
  image: alpine:latest
  before_script:
    - apk add --no-cache curl
  script:
    - echo "Deploying to production environment"
    - curl -X POST $PRODUCTION_WEBHOOK_URL
  environment:
    name: production
    url: https://example.com
  when: manual
  only:
    - tags
```

---

### 1.2 多阶段构建

```yaml
# 定义可复用的模板
.build_template: &build_template
  stage: build
  image: rust:${RUST_VERSION}
  cache:
    key: ${CI_COMMIT_REF_SLUG}
    paths:
      - .cargo/
      - target/
  script:
    - cargo build ${BUILD_FLAGS}

# 使用模板
build:debug:
  <<: *build_template
  variables:
    BUILD_FLAGS: "--all-features"

build:release:
  <<: *build_template
  variables:
    BUILD_FLAGS: "--release --all-features"
  only:
    - main
    - tags
```

---

## 2. Docker-in-Docker 构建

```yaml
docker:build:
  stage: package
  image: docker:latest
  services:
    - name: docker:dind
      command: ["--tls=false"]
  variables:
    DOCKER_HOST: tcp://docker:2375
    DOCKER_TLS_CERTDIR: ""
    DOCKER_DRIVER: overlay2
  before_script:
    - docker info
    - echo $CI_REGISTRY_PASSWORD | docker login -u $CI_REGISTRY_USER --password-stdin $CI_REGISTRY
  script:
    # 构建多架构镜像
    - docker buildx create --use
    - docker buildx build 
        --platform linux/amd64,linux/arm64 
        --tag $CI_REGISTRY_IMAGE:$CI_COMMIT_SHORT_SHA 
        --tag $CI_REGISTRY_IMAGE:latest 
        --push 
        .
  only:
    - main
    - tags

# 使用 Kaniko 构建（无需特权模式）
docker:kaniko:
  stage: package
  image:
    name: gcr.io/kaniko-project/executor:latest
    entrypoint: [""]
  script:
    - echo "{\"auths\":{\"$CI_REGISTRY\":{\"username\":\"$CI_REGISTRY_USER\",\"password\":\"$CI_REGISTRY_PASSWORD\"}}}" > /kaniko/.docker/config.json
    - /kaniko/executor
        --context $CI_PROJECT_DIR
        --dockerfile $CI_PROJECT_DIR/Dockerfile
        --destination $CI_REGISTRY_IMAGE:$CI_COMMIT_SHORT_SHA
  only:
    - main
```

---

## 3. 缓存优化

```yaml
# 全局缓存配置
cache:
  key: ${CI_COMMIT_REF_SLUG}
  paths:
    - .cargo/
    - target/
  policy: pull-push

# 特定作业缓存策略
test:
  cache:
    key: ${CI_COMMIT_REF_SLUG}-test
    paths:
      - .cargo/
      - target/debug/
    policy: pull

build:
  cache:
    key: ${CI_COMMIT_REF_SLUG}-build
    paths:
      - .cargo/
      - target/release/
    policy: pull-push

# 使用分布式缓存
.rust_cache: &rust_cache
  cache:
    key:
      files:
        - Cargo.lock
      prefix: ${CI_JOB_NAME}
    paths:
      - .cargo/registry/
      - .cargo/git/
      - target/
```

---

## 4. 并行测试

```yaml
# 并行测试配置
test:parallel:
  stage: test
  parallel:
    matrix:
      - TEST_SUITE: [unit, integration, doc]
  script:
    - |
      case $TEST_SUITE in
        unit)
          cargo test --lib --all-features
          ;;
        integration)
          cargo test --test '*' --all-features
          ;;
        doc)
          cargo test --doc
          ;;
      esac
  artifacts:
    reports:
      junit: target/test-results-${TEST_SUITE}.xml

# 按模块并行测试
test:by-module:
  stage: test
  parallel: 5
  script:
    - |
      MODULES=$(cargo test --list | grep -E '^    ' | cut -d' ' -f5 | sort -u)
      TOTAL=$(echo "$MODULES" | wc -l)
      MODULE=$(echo "$MODULES" | sed -n "$((CI_NODE_INDEX + 1))p")
      cargo test --test $MODULE
```

---

## 5. 制品管理

```yaml
# 构建制品
build:artifacts:
  stage: build
  script:
    - cargo build --release
  artifacts:
    name: "${CI_PROJECT_NAME}-${CI_COMMIT_SHORT_SHA}"
    paths:
      - target/release/my-app
    expire_in: 30 days
    reports:
      dotenv: build.env

# 生成制品报告
artifacts:report:
  stage: build
  script:
    - cargo build --release
    - echo "BUILD_VERSION=${CI_COMMIT_SHORT_SHA}" > build.env
    - echo "BUILD_DATE=$(date -u +'%Y-%m-%dT%H:%M:%SZ')" >> build.env
  artifacts:
    reports:
      dotenv: build.env

# 发布到 GitLab Package Registry
publish:cargo:
  stage: package
  script:
    - cargo publish --token ${CARGO_REGISTRY_TOKEN}
  only:
    - tags
  when: manual
```

---

## 6. 环境部署

```yaml
# 定义环境
.deploy_template: &deploy_template
  stage: deploy
  image: alpine:latest
  before_script:
    - apk add --no-cache openssh-client
    - eval $(ssh-agent -s)
    - echo "$SSH_PRIVATE_KEY" | tr -d '\r' | ssh-add -
    - mkdir -p ~/.ssh
    - chmod 700 ~/.ssh

# 开发环境
deploy:development:
  <<: *deploy_template
  script:
    - echo "Deploying to development"
    - ssh $DEV_USER@$DEV_HOST "docker pull $CI_REGISTRY_IMAGE:$CI_COMMIT_SHORT_SHA"
    - ssh $DEV_USER@$DEV_HOST "docker-compose up -d"
  environment:
    name: development
    url: https://dev.example.com
  only:
    - develop

# 预生产环境
deploy:staging:
  <<: *deploy_template
  script:
    - echo "Deploying to staging"
    - ssh $STAGING_USER@$STAGING_HOST "docker pull $CI_REGISTRY_IMAGE:$CI_COMMIT_SHORT_SHA"
    - ssh $STAGING_USER@$STAGING_HOST "docker-compose up -d"
  environment:
    name: staging
    url: https://staging.example.com
  only:
    - main

# 生产环境
deploy:production:
  <<: *deploy_template
  script:
    - echo "Deploying to production"
    - ssh $PROD_USER@$PROD_HOST "docker pull $CI_REGISTRY_IMAGE:$CI_COMMIT_TAG"
    - ssh $PROD_USER@$PROD_HOST "docker-compose up -d"
  environment:
    name: production
    url: https://example.com
    on_stop: stop:production
  when: manual
  only:
    - tags

# 停止生产环境
stop:production:
  <<: *deploy_template
  script:
    - echo "Stopping production"
    - ssh $PROD_USER@$PROD_HOST "docker-compose down"
  environment:
    name: production
    action: stop
  when: manual
  only:
    - tags
```

---

## 7. 完整生产配置

完整的生产级 `.gitlab-ci.yml`:

```yaml
# Rust OTLP 生产级 CI/CD Pipeline

include:
  - template: Security/SAST.gitlab-ci.yml
  - template: Security/Dependency-Scanning.gitlab-ci.yml
  - template: Security/Container-Scanning.gitlab-ci.yml

variables:
  RUST_VERSION: "1.90"
  CARGO_HOME: $CI_PROJECT_DIR/.cargo
  CARGO_TERM_COLOR: always
  DOCKER_DRIVER: overlay2
  DOCKER_TLS_CERTDIR: "/certs"

stages:
  - check
  - test
  - build
  - security
  - package
  - deploy

# ==================== 默认配置 ====================

default:
  image: rust:${RUST_VERSION}
  before_script:
    - rustc --version
    - cargo --version
  cache:
    key:
      files:
        - Cargo.lock
    paths:
      - .cargo/
      - target/
    policy: pull-push

# ==================== 检查阶段 ====================

format:
  stage: check
  script:
    - rustup component add rustfmt
    - cargo fmt --all -- --check
  rules:
    - if: $CI_PIPELINE_SOURCE == "merge_request_event"
    - if: $CI_COMMIT_BRANCH == $CI_DEFAULT_BRANCH

clippy:
  stage: check
  script:
    - rustup component add clippy
    - cargo clippy --all-targets --all-features -- -D warnings
  rules:
    - if: $CI_PIPELINE_SOURCE == "merge_request_event"
    - if: $CI_COMMIT_BRANCH == $CI_DEFAULT_BRANCH

audit:
  stage: check
  script:
    - cargo install cargo-audit
    - cargo audit --deny warnings
  allow_failure: true
  rules:
    - if: $CI_PIPELINE_SOURCE == "merge_request_event"
    - if: $CI_COMMIT_BRANCH == $CI_DEFAULT_BRANCH

# ==================== 测试阶段 ====================

test:unit:
  stage: test
  parallel: 3
  services:
    - name: otel/opentelemetry-collector:latest
      alias: otel
    - name: postgres:16
      alias: postgres
    - name: redis:7
      alias: redis
  variables:
    POSTGRES_DB: test
    POSTGRES_USER: postgres
    POSTGRES_PASSWORD: postgres
    OTEL_EXPORTER_OTLP_ENDPOINT: http://otel:4317
    DATABASE_URL: postgres://postgres:postgres@postgres:5432/test
    REDIS_URL: redis://redis:6379
  script:
    - cargo test --lib --all-features --verbose -- --test-threads=1
  coverage: '/^\s*lines:\s*\d+\.\d+\%/'
  artifacts:
    when: always
    reports:
      junit: target/junit.xml
      cobertura: target/coverage/cobertura.xml
    paths:
      - target/coverage/
    expire_in: 30 days

test:integration:
  stage: test
  services:
    - name: otel/opentelemetry-collector:latest
      alias: otel
    - name: postgres:16
      alias: postgres
  script:
    - cargo test --test '*' --all-features
  rules:
    - if: $CI_PIPELINE_SOURCE == "merge_request_event"
    - if: $CI_COMMIT_BRANCH == $CI_DEFAULT_BRANCH

test:doc:
  stage: test
  script:
    - cargo test --doc
  rules:
    - if: $CI_PIPELINE_SOURCE == "merge_request_event"
    - if: $CI_COMMIT_BRANCH == $CI_DEFAULT_BRANCH

benchmark:
  stage: test
  script:
    - cargo bench --all-features
  artifacts:
    paths:
      - target/criterion/
    expire_in: 7 days
  rules:
    - if: $CI_COMMIT_BRANCH == $CI_DEFAULT_BRANCH

# ==================== 构建阶段 ====================

build:debug:
  stage: build
  script:
    - cargo build --all-features
  artifacts:
    paths:
      - target/debug/my-app
    expire_in: 1 day
  rules:
    - if: $CI_PIPELINE_SOURCE == "merge_request_event"

build:release:
  stage: build
  script:
    - cargo build --release --all-features
    - strip target/release/my-app
  artifacts:
    name: "${CI_PROJECT_NAME}-${CI_COMMIT_SHORT_SHA}"
    paths:
      - target/release/my-app
    expire_in: 30 days
  rules:
    - if: $CI_COMMIT_BRANCH == $CI_DEFAULT_BRANCH
    - if: $CI_COMMIT_TAG

# ==================== 安全阶段 ====================

sast:
  stage: security
  variables:
    SAST_EXCLUDED_PATHS: "spec, test, tests, tmp, target"

dependency_scanning:
  stage: security

container_scanning:
  stage: security
  dependencies:
    - package:docker

# ==================== 打包阶段 ====================

package:docker:
  stage: package
  image: docker:latest
  services:
    - docker:dind
  before_script:
    - echo $CI_REGISTRY_PASSWORD | docker login -u $CI_REGISTRY_USER --password-stdin $CI_REGISTRY
  script:
    - |
      docker build \
        --tag $CI_REGISTRY_IMAGE:$CI_COMMIT_SHORT_SHA \
        --tag $CI_REGISTRY_IMAGE:latest \
        --build-arg RUST_VERSION=${RUST_VERSION} \
        .
    - docker push $CI_REGISTRY_IMAGE:$CI_COMMIT_SHORT_SHA
    - |
      if [ "$CI_COMMIT_BRANCH" == "$CI_DEFAULT_BRANCH" ]; then
        docker push $CI_REGISTRY_IMAGE:latest
      fi
    - |
      if [ -n "$CI_COMMIT_TAG" ]; then
        docker tag $CI_REGISTRY_IMAGE:$CI_COMMIT_SHORT_SHA $CI_REGISTRY_IMAGE:$CI_COMMIT_TAG
        docker push $CI_REGISTRY_IMAGE:$CI_COMMIT_TAG
      fi
  rules:
    - if: $CI_COMMIT_BRANCH == $CI_DEFAULT_BRANCH
    - if: $CI_COMMIT_TAG

# ==================== 部署阶段 ====================

deploy:staging:
  stage: deploy
  image: alpine:latest
  before_script:
    - apk add --no-cache curl
  script:
    - echo "Deploying to staging"
    - |
      curl -X POST \
        -H "Content-Type: application/json" \
        -d "{\"image\":\"$CI_REGISTRY_IMAGE:$CI_COMMIT_SHORT_SHA\"}" \
        $STAGING_WEBHOOK_URL
  environment:
    name: staging
    url: https://staging.example.com
  rules:
    - if: $CI_COMMIT_BRANCH == $CI_DEFAULT_BRANCH

deploy:production:
  stage: deploy
  image: alpine:latest
  before_script:
    - apk add --no-cache curl
  script:
    - echo "Deploying to production"
    - |
      curl -X POST \
        -H "Content-Type: application/json" \
        -d "{\"image\":\"$CI_REGISTRY_IMAGE:$CI_COMMIT_TAG\"}" \
        $PRODUCTION_WEBHOOK_URL
  environment:
    name: production
    url: https://example.com
    on_stop: rollback:production
  when: manual
  rules:
    - if: $CI_COMMIT_TAG

rollback:production:
  stage: deploy
  image: alpine:latest
  script:
    - echo "Rolling back production"
    - curl -X POST $PRODUCTION_ROLLBACK_URL
  environment:
    name: production
    action: stop
  when: manual
  rules:
    - if: $CI_COMMIT_TAG
```

---

## 总结

本文档提供了 Rust OTLP 项目在 GitLab CI 的完整配置：

1. ✅ **完整 Pipeline**
   - 检查、测试、构建、打包、部署

2. ✅ **Docker 构建**
   - Docker-in-Docker
   - Kaniko 无特权构建

3. ✅ **缓存优化**
   - Cargo 缓存
   - 分布式缓存

4. ✅ **并行测试**
   - 按测试套件并行
   - 按模块并行

5. ✅ **多环境部署**
   - 开发、预生产、生产环境
   - 自动和手动部署

6. ✅ **安全扫描**
   - SAST
   - 依赖扫描
   - 容器扫描

通过这些配置，您可以构建一个完整的 GitLab CI/CD 流水线。

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-08  
**维护者**: OTLP Rust Team  
**许可证**: MIT OR Apache-2.0
