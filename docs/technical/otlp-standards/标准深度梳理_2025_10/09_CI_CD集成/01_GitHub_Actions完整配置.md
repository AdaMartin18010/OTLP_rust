# GitHub Actions 完整配置 - Rust OTLP CI/CD

> **版本信息**
>
> - Rust: 1.90 (2024 Edition)
> - opentelemetry: 0.31.0
> - 更新日期: 2025-10-08
> - 适用场景: GitHub Actions CI/CD Pipeline

## 目录

- [GitHub Actions 完整配置 - Rust OTLP CI/CD](#github-actions-完整配置---rust-otlp-cicd)
  - [目录](#目录)
  - [概述](#概述)
  - [1. 基础配置](#1-基础配置)
    - [1.1 完整 CI 工作流](#11-完整-ci-工作流)
    - [1.2 多平台构建](#12-多平台构建)
  - [2. 代码质量检查](#2-代码质量检查)
    - [2.1 格式化检查](#21-格式化检查)
    - [2.2 Clippy 静态分析](#22-clippy-静态分析)
    - [2.3 审计依赖](#23-审计依赖)
  - [3. 测试自动化](#3-测试自动化)
    - [3.1 单元测试](#31-单元测试)
    - [3.2 集成测试](#32-集成测试)
    - [3.3 测试覆盖率](#33-测试覆盖率)
  - [4. 性能回归检测](#4-性能回归检测)
    - [4.1 基准测试](#41-基准测试)
    - [4.2 性能对比](#42-性能对比)
  - [5. 容器化构建](#5-容器化构建)
    - [5.1 Docker 镜像构建](#51-docker-镜像构建)
    - [5.2 多阶段构建优化](#52-多阶段构建优化)
  - [6. 发布自动化](#6-发布自动化)
    - [6.1 自动发布](#61-自动发布)
    - [6.2 Cargo 发布](#62-cargo-发布)
  - [7. 依赖更新](#7-依赖更新)
    - [7.1 Dependabot 配置](#71-dependabot-配置)
    - [7.2 自动更新 PR](#72-自动更新-pr)
  - [8. 缓存优化](#8-缓存优化)
    - [8.1 Cargo 缓存](#81-cargo-缓存)
    - [8.2 Docker Layer 缓存](#82-docker-layer-缓存)
  - [9. 安全扫描](#9-安全扫描)
    - [9.1 漏洞扫描](#91-漏洞扫描)
    - [9.2 SAST 分析](#92-sast-分析)
  - [10. 完整示例](#10-完整示例)
  - [总结](#总结)

---

## 概述

本文档提供 Rust OTLP 项目在 GitHub Actions 的完整 CI/CD 配置，包括：

- ✅ 自动化测试（单元测试、集成测试）
- ✅ 代码质量检查（格式化、Clippy、审计）
- ✅ 性能回归检测（基准测试、性能对比）
- ✅ 多平台构建（Linux、macOS、Windows）
- ✅ 容器化部署（Docker 镜像）
- ✅ 自动发布（GitHub Release、Cargo）
- ✅ 安全扫描（依赖审计、漏洞扫描）

---

## 1. 基础配置

### 1.1 完整 CI 工作流

`.github/workflows/ci.yml`:

```yaml
name: CI

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main ]

env:
  RUST_VERSION: "1.90"
  CARGO_TERM_COLOR: always

jobs:
  # 代码检查
  check:
    name: Code Quality
    runs-on: ubuntu-latest
    steps:
      - name: Checkout code
        uses: actions/checkout@v4

      - name: Install Rust toolchain
        uses: dtolnay/rust-toolchain@master
        with:
          toolchain: ${{ env.RUST_VERSION }}
          components: rustfmt, clippy

      - name: Cache dependencies
        uses: Swatinem/rust-cache@v2
        with:
          cache-on-failure: true

      - name: Check formatting
        run: cargo fmt --all -- --check

      - name: Run Clippy
        run: cargo clippy --all-targets --all-features -- -D warnings

      - name: Check documentation
        run: cargo doc --no-deps --all-features
        env:
          RUSTDOCFLAGS: -D warnings

  # 构建
  build:
    name: Build
    runs-on: ${{ matrix.os }}
    strategy:
      matrix:
        os: [ubuntu-latest, macos-latest, windows-latest]
        rust: ["1.90", stable]
    steps:
      - name: Checkout code
        uses: actions/checkout@v4

      - name: Install Rust
        uses: dtolnay/rust-toolchain@master
        with:
          toolchain: ${{ matrix.rust }}

      - name: Cache dependencies
        uses: Swatinem/rust-cache@v2

      - name: Build
        run: cargo build --release --all-features

      - name: Upload artifacts
        if: matrix.os == 'ubuntu-latest' && matrix.rust == '1.90'
        uses: actions/upload-artifact@v4
        with:
          name: binary-linux
          path: target/release/my-app

  # 测试
  test:
    name: Test
    runs-on: ubuntu-latest
    services:
      # OTLP Collector
      otel-collector:
        image: otel/opentelemetry-collector:latest
        ports:
          - 4317:4317
          - 4318:4318
      
      # PostgreSQL
      postgres:
        image: postgres:16
        env:
          POSTGRES_PASSWORD: postgres
        ports:
          - 5432:5432
        options: >-
          --health-cmd pg_isready
          --health-interval 10s
          --health-timeout 5s
          --health-retries 5
      
      # Redis
      redis:
        image: redis:7
        ports:
          - 6379:6379
        options: >-
          --health-cmd "redis-cli ping"
          --health-interval 10s
          --health-timeout 5s
          --health-retries 5

    steps:
      - name: Checkout code
        uses: actions/checkout@v4

      - name: Install Rust
        uses: dtolnay/rust-toolchain@master
        with:
          toolchain: ${{ env.RUST_VERSION }}

      - name: Cache dependencies
        uses: Swatinem/rust-cache@v2

      - name: Run tests
        run: cargo test --all-features --verbose
        env:
          OTEL_EXPORTER_OTLP_ENDPOINT: http://localhost:4317
          DATABASE_URL: postgres://postgres:postgres@localhost:5432/test
          REDIS_URL: redis://localhost:6379

      - name: Run doc tests
        run: cargo test --doc

  # 覆盖率
  coverage:
    name: Code Coverage
    runs-on: ubuntu-latest
    steps:
      - name: Checkout code
        uses: actions/checkout@v4

      - name: Install Rust
        uses: dtolnay/rust-toolchain@master
        with:
          toolchain: ${{ env.RUST_VERSION }}
          components: llvm-tools-preview

      - name: Install cargo-llvm-cov
        uses: taiki-e/install-action@cargo-llvm-cov

      - name: Generate coverage
        run: cargo llvm-cov --all-features --workspace --lcov --output-path lcov.info

      - name: Upload to codecov
        uses: codecov/codecov-action@v4
        with:
          files: lcov.info
          fail_ci_if_error: true
```

---

### 1.2 多平台构建

```yaml
name: Multi-Platform Build

on:
  push:
    tags:
      - 'v*'

jobs:
  build-matrix:
    name: Build ${{ matrix.target }}
    runs-on: ${{ matrix.os }}
    strategy:
      matrix:
        include:
          - os: ubuntu-latest
            target: x86_64-unknown-linux-gnu
          - os: ubuntu-latest
            target: x86_64-unknown-linux-musl
          - os: macos-latest
            target: x86_64-apple-darwin
          - os: macos-latest
            target: aarch64-apple-darwin
          - os: windows-latest
            target: x86_64-pc-windows-msvc

    steps:
      - uses: actions/checkout@v4

      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
        with:
          targets: ${{ matrix.target }}

      - name: Install cross (Linux musl)
        if: matrix.target == 'x86_64-unknown-linux-musl'
        run: cargo install cross

      - name: Build
        run: |
          if [[ "${{ matrix.target }}" == "x86_64-unknown-linux-musl" ]]; then
            cross build --release --target ${{ matrix.target }}
          else
            cargo build --release --target ${{ matrix.target }}
          fi

      - name: Package
        run: |
          cd target/${{ matrix.target }}/release
          tar czf ../../../my-app-${{ matrix.target }}.tar.gz my-app
        shell: bash

      - name: Upload artifact
        uses: actions/upload-artifact@v4
        with:
          name: my-app-${{ matrix.target }}
          path: my-app-${{ matrix.target }}.tar.gz
```

---

## 2. 代码质量检查

### 2.1 格式化检查

```yaml
name: Format Check

on: [push, pull_request]

jobs:
  rustfmt:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
        with:
          components: rustfmt

      - name: Check formatting
        run: cargo fmt --all -- --check
```

---

### 2.2 Clippy 静态分析

```yaml
name: Clippy

on: [push, pull_request]

jobs:
  clippy:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
        with:
          components: clippy

      - name: Run Clippy
        run: |
          cargo clippy --all-targets --all-features -- \
            -D warnings \
            -D clippy::all \
            -D clippy::pedantic \
            -A clippy::module_name_repetitions
```

---

### 2.3 审计依赖

```yaml
name: Security Audit

on:
  schedule:
    - cron: '0 0 * * *' # 每天运行
  push:
    paths:
      - '**/Cargo.toml'
      - '**/Cargo.lock'

jobs:
  audit:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Install cargo-audit
        run: cargo install cargo-audit

      - name: Run audit
        run: cargo audit

      - name: Check advisories
        run: cargo audit --deny warnings
```

---

## 3. 测试自动化

### 3.1 单元测试

```yaml
name: Unit Tests

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable

      - name: Run unit tests
        run: cargo test --lib --all-features

      - name: Run doc tests
        run: cargo test --doc
```

---

### 3.2 集成测试

```yaml
name: Integration Tests

on: [push, pull_request]

jobs:
  integration:
    runs-on: ubuntu-latest
    services:
      otel-collector:
        image: otel/opentelemetry-collector:latest
        ports:
          - 4317:4317
      postgres:
        image: postgres:16
        env:
          POSTGRES_PASSWORD: postgres
        ports:
          - 5432:5432

    steps:
      - uses: actions/checkout@v4
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable

      - name: Setup database
        run: |
          cargo install sqlx-cli
          sqlx database create
          sqlx migrate run

      - name: Run integration tests
        run: cargo test --test '*' --all-features
        env:
          OTEL_EXPORTER_OTLP_ENDPOINT: http://localhost:4317
          DATABASE_URL: postgres://postgres:postgres@localhost:5432/test
```

---

### 3.3 测试覆盖率

```yaml
name: Code Coverage

on: [push, pull_request]

jobs:
  coverage:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
        with:
          components: llvm-tools-preview

      - name: Install cargo-llvm-cov
        uses: taiki-e/install-action@cargo-llvm-cov

      - name: Generate coverage
        run: cargo llvm-cov --all-features --workspace --lcov --output-path lcov.info

      - name: Upload to Codecov
        uses: codecov/codecov-action@v4
        with:
          token: ${{ secrets.CODECOV_TOKEN }}
          files: lcov.info
          fail_ci_if_error: true

      - name: Coverage report
        run: cargo llvm-cov report --html
      
      - name: Upload HTML report
        uses: actions/upload-artifact@v4
        with:
          name: coverage-report
          path: target/llvm-cov/html/
```

---

## 4. 性能回归检测

### 4.1 基准测试

```yaml
name: Benchmark

on:
  push:
    branches: [ main ]
  pull_request:
    branches: [ main ]

jobs:
  benchmark:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable

      - name: Run benchmarks
        run: cargo bench --bench '*' -- --output-format bencher | tee output.txt

      - name: Store benchmark result
        uses: benchmark-action/github-action-benchmark@v1
        with:
          tool: 'cargo'
          output-file-path: output.txt
          github-token: ${{ secrets.GITHUB_TOKEN }}
          auto-push: true
          alert-threshold: '200%'
          comment-on-alert: true
          fail-on-alert: true
```

---

### 4.2 性能对比

```yaml
name: Performance Comparison

on:
  pull_request:
    branches: [ main ]

jobs:
  compare:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
        with:
          fetch-depth: 0

      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable

      - name: Install critcmp
        run: cargo install critcmp

      - name: Benchmark base branch
        run: |
          git checkout ${{ github.base_ref }}
          cargo bench --bench '*' -- --save-baseline base

      - name: Benchmark PR branch
        run: |
          git checkout ${{ github.head_ref }}
          cargo bench --bench '*' -- --save-baseline pr

      - name: Compare results
        run: critcmp base pr

      - name: Comment PR
        uses: actions/github-script@v7
        with:
          script: |
            const fs = require('fs');
            const output = fs.readFileSync('criterion/comparison.txt', 'utf8');
            github.rest.issues.createComment({
              issue_number: context.issue.number,
              owner: context.repo.owner,
              repo: context.repo.repo,
              body: `## Performance Comparison\n\n\`\`\`\n${output}\n\`\`\``
            });
```

---

## 5. 容器化构建

### 5.1 Docker 镜像构建

```yaml
name: Docker Build

on:
  push:
    branches: [ main ]
    tags:
      - 'v*'

jobs:
  docker:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Set up Docker Buildx
        uses: docker/setup-buildx-action@v3

      - name: Log in to Docker Hub
        uses: docker/login-action@v3
        with:
          username: ${{ secrets.DOCKER_USERNAME }}
          password: ${{ secrets.DOCKER_PASSWORD }}

      - name: Extract metadata
        id: meta
        uses: docker/metadata-action@v5
        with:
          images: myorg/my-app
          tags: |
            type=ref,event=branch
            type=semver,pattern={{version}}
            type=semver,pattern={{major}}.{{minor}}
            type=sha

      - name: Build and push
        uses: docker/build-push-action@v5
        with:
          context: .
          platforms: linux/amd64,linux/arm64
          push: true
          tags: ${{ steps.meta.outputs.tags }}
          labels: ${{ steps.meta.outputs.labels }}
          cache-from: type=gha
          cache-to: type=gha,mode=max
```

---

### 5.2 多阶段构建优化

`Dockerfile`:

```dockerfile
# 构建阶段
FROM rust:1.90-slim as builder

WORKDIR /app

# 缓存依赖
COPY Cargo.toml Cargo.lock ./
RUN mkdir src && \
    echo "fn main() {}" > src/main.rs && \
    cargo build --release && \
    rm -rf src

# 构建应用
COPY . .
RUN touch src/main.rs && \
    cargo build --release

# 运行阶段
FROM debian:bookworm-slim

RUN apt-get update && \
    apt-get install -y ca-certificates && \
    rm -rf /var/lib/apt/lists/*

COPY --from=builder /app/target/release/my-app /usr/local/bin/

EXPOSE 8080

CMD ["my-app"]
```

---

## 6. 发布自动化

### 6.1 自动发布

```yaml
name: Release

on:
  push:
    tags:
      - 'v*'

jobs:
  create-release:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Create Release
        uses: softprops/action-gh-release@v1
        with:
          generate_release_notes: true
          draft: false
          prerelease: false

  build-and-upload:
    needs: create-release
    runs-on: ${{ matrix.os }}
    strategy:
      matrix:
        include:
          - os: ubuntu-latest
            target: x86_64-unknown-linux-gnu
          - os: macos-latest
            target: x86_64-apple-darwin
          - os: windows-latest
            target: x86_64-pc-windows-msvc

    steps:
      - uses: actions/checkout@v4

      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
        with:
          targets: ${{ matrix.target }}

      - name: Build
        run: cargo build --release --target ${{ matrix.target }}

      - name: Package
        run: |
          cd target/${{ matrix.target }}/release
          if [ "${{ matrix.os }}" == "windows-latest" ]; then
            7z a ../../../my-app-${{ matrix.target }}.zip my-app.exe
          else
            tar czf ../../../my-app-${{ matrix.target }}.tar.gz my-app
          fi
        shell: bash

      - name: Upload Release Asset
        uses: softprops/action-gh-release@v1
        with:
          files: my-app-${{ matrix.target }}.*
```

---

### 6.2 Cargo 发布

```yaml
name: Cargo Publish

on:
  push:
    tags:
      - 'v*'

jobs:
  publish:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable

      - name: Publish to crates.io
        run: cargo publish --token ${{ secrets.CARGO_TOKEN }}
```

---

## 7. 依赖更新

### 7.1 Dependabot 配置

`.github/dependabot.yml`:

```yaml
version: 2
updates:
  # Cargo dependencies
  - package-ecosystem: "cargo"
    directory: "/"
    schedule:
      interval: "weekly"
    open-pull-requests-limit: 10
    reviewers:
      - "maintainer-team"
    commit-message:
      prefix: "chore"
      include: "scope"

  # GitHub Actions
  - package-ecosystem: "github-actions"
    directory: "/"
    schedule:
      interval: "weekly"
    open-pull-requests-limit: 5
```

---

### 7.2 自动更新 PR

```yaml
name: Auto Merge Dependabot

on:
  pull_request:
    types: [opened, synchronize]

jobs:
  auto-merge:
    runs-on: ubuntu-latest
    if: github.actor == 'dependabot[bot]'
    steps:
      - name: Dependabot metadata
        id: metadata
        uses: dependabot/fetch-metadata@v1

      - name: Enable auto-merge for minor/patch updates
        if: steps.metadata.outputs.update-type != 'version-update:semver-major'
        run: gh pr merge --auto --squash "$PR_URL"
        env:
          PR_URL: ${{github.event.pull_request.html_url}}
          GITHUB_TOKEN: ${{secrets.GITHUB_TOKEN}}
```

---

## 8. 缓存优化

### 8.1 Cargo 缓存

```yaml
name: Optimized Build

on: [push, pull_request]

jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable

      - name: Cache Cargo registry
        uses: actions/cache@v4
        with:
          path: ~/.cargo/registry
          key: ${{ runner.os }}-cargo-registry-${{ hashFiles('**/Cargo.lock') }}

      - name: Cache Cargo index
        uses: actions/cache@v4
        with:
          path: ~/.cargo/git
          key: ${{ runner.os }}-cargo-index-${{ hashFiles('**/Cargo.lock') }}

      - name: Cache build artifacts
        uses: actions/cache@v4
        with:
          path: target
          key: ${{ runner.os }}-cargo-build-${{ hashFiles('**/Cargo.lock') }}

      - name: Build
        run: cargo build --release
```

---

### 8.2 Docker Layer 缓存

```yaml
name: Docker with Cache

on: [push]

jobs:
  docker:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Set up Docker Buildx
        uses: docker/setup-buildx-action@v3

      - name: Build with cache
        uses: docker/build-push-action@v5
        with:
          context: .
          push: false
          cache-from: type=gha
          cache-to: type=gha,mode=max
```

---

## 9. 安全扫描

### 9.1 漏洞扫描

```yaml
name: Security Scan

on:
  schedule:
    - cron: '0 0 * * 0' # 每周日运行
  push:
    branches: [ main ]

jobs:
  security:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Run Trivy vulnerability scanner
        uses: aquasecurity/trivy-action@master
        with:
          scan-type: 'fs'
          scan-ref: '.'
          format: 'sarif'
          output: 'trivy-results.sarif'

      - name: Upload Trivy results to GitHub Security
        uses: github/codeql-action/upload-sarif@v3
        with:
          sarif_file: 'trivy-results.sarif'
```

---

### 9.2 SAST 分析

```yaml
name: CodeQL

on:
  push:
    branches: [ main ]
  pull_request:
    branches: [ main ]
  schedule:
    - cron: '0 0 * * 1'

jobs:
  analyze:
    runs-on: ubuntu-latest
    permissions:
      security-events: write

    steps:
      - uses: actions/checkout@v4

      - name: Initialize CodeQL
        uses: github/codeql-action/init@v3
        with:
          languages: rust

      - name: Build
        run: cargo build --release

      - name: Perform CodeQL Analysis
        uses: github/codeql-action/analyze@v3
```

---

## 10. 完整示例

完整的生产级 CI/CD 配置：

`.github/workflows/production.yml`:

```yaml
name: Production CI/CD

on:
  push:
    branches: [ main ]
    tags:
      - 'v*'
  pull_request:
    branches: [ main ]

env:
  RUST_VERSION: "1.90"
  CARGO_TERM_COLOR: always

jobs:
  # 1. 代码质量
  quality:
    name: Code Quality
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - uses: dtolnay/rust-toolchain@master
        with:
          toolchain: ${{ env.RUST_VERSION }}
          components: rustfmt, clippy
      
      - uses: Swatinem/rust-cache@v2
      
      - name: Format check
        run: cargo fmt --all -- --check
      
      - name: Clippy
        run: cargo clippy --all-targets --all-features -- -D warnings
      
      - name: Audit
        run: |
          cargo install cargo-audit
          cargo audit

  # 2. 测试
  test:
    name: Test Suite
    runs-on: ${{ matrix.os }}
    strategy:
      matrix:
        os: [ubuntu-latest, macos-latest, windows-latest]
    services:
      otel-collector:
        image: otel/opentelemetry-collector:latest
        ports:
          - 4317:4317
    steps:
      - uses: actions/checkout@v4
      
      - uses: dtolnay/rust-toolchain@stable
      
      - uses: Swatinem/rust-cache@v2
      
      - name: Run tests
        run: cargo test --all-features --verbose

  # 3. 覆盖率
  coverage:
    name: Coverage
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - uses: dtolnay/rust-toolchain@stable
        with:
          components: llvm-tools-preview
      
      - uses: taiki-e/install-action@cargo-llvm-cov
      
      - name: Generate coverage
        run: cargo llvm-cov --all-features --workspace --lcov --output-path lcov.info
      
      - uses: codecov/codecov-action@v4
        with:
          files: lcov.info

  # 4. 基准测试
  benchmark:
    name: Benchmark
    if: github.event_name == 'push' && github.ref == 'refs/heads/main'
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - uses: dtolnay/rust-toolchain@stable
      
      - name: Run benchmarks
        run: cargo bench

  # 5. Docker 构建
  docker:
    name: Docker Build
    if: github.event_name == 'push' && (github.ref == 'refs/heads/main' || startsWith(github.ref, 'refs/tags/v'))
    runs-on: ubuntu-latest
    needs: [quality, test]
    steps:
      - uses: actions/checkout@v4
      
      - uses: docker/setup-buildx-action@v3
      
      - uses: docker/login-action@v3
        with:
          username: ${{ secrets.DOCKER_USERNAME }}
          password: ${{ secrets.DOCKER_PASSWORD }}
      
      - uses: docker/metadata-action@v5
        id: meta
        with:
          images: myorg/my-app
      
      - uses: docker/build-push-action@v5
        with:
          context: .
          push: true
          tags: ${{ steps.meta.outputs.tags }}
          cache-from: type=gha
          cache-to: type=gha,mode=max

  # 6. 发布
  release:
    name: Release
    if: startsWith(github.ref, 'refs/tags/v')
    runs-on: ubuntu-latest
    needs: [quality, test, docker]
    steps:
      - uses: actions/checkout@v4
      
      - uses: dtolnay/rust-toolchain@stable
      
      - name: Build release
        run: cargo build --release
      
      - uses: softprops/action-gh-release@v1
        with:
          files: target/release/my-app
          generate_release_notes: true
```

---

## 总结

本文档提供了 Rust OTLP 项目的完整 GitHub Actions CI/CD 配置：

1. ✅ **代码质量检查**
   - 格式化检查
   - Clippy 静态分析
   - 依赖审计

2. ✅ **自动化测试**
   - 单元测试
   - 集成测试
   - 测试覆盖率

3. ✅ **性能监控**
   - 基准测试
   - 性能回归检测

4. ✅ **容器化**
   - Docker 镜像构建
   - 多架构支持

5. ✅ **自动发布**
   - GitHub Release
   - Cargo 发布

6. ✅ **安全扫描**
   - 漏洞扫描
   - SAST 分析

通过这些配置，您可以构建一个完整的生产级 CI/CD 流水线。

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-08  
**维护者**: OTLP Rust Team  
**许可证**: MIT OR Apache-2.0
