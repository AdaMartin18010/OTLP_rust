# GitHub Actions - Rust OTLP 完整配置

> **Rust版本**: 1.90+  
> **GitHub Actions**: 最新版  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月9日

---

## 目录

- [GitHub Actions - Rust OTLP 完整配置](#github-actions---rust-otlp-完整配置)
  - [目录](#目录)
  - [1. 基础工作流](#1-基础工作流)
  - [2. 测试工作流](#2-测试工作流)
  - [3. 性能基准测试](#3-性能基准测试)
  - [4. 发布工作流](#4-发布工作流)
  - [5. 完整生产配置](#5-完整生产配置)

---

## 1. 基础工作流

**基础 CI 配置** (`.github/workflows/ci.yml`):

```yaml
name: Rust CI

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main ]

env:
  CARGO_TERM_COLOR: always
  RUST_BACKTRACE: 1

jobs:
  check:
    name: Check
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
        with:
          toolchain: 1.90
          components: rustfmt, clippy
      
      - name: Cache cargo registry
        uses: actions/cache@v4
        with:
          path: ~/.cargo/registry
          key: ${{ runner.os }}-cargo-registry-${{ hashFiles('**/Cargo.lock') }}
      
      - name: Cache cargo index
        uses: actions/cache@v4
        with:
          path: ~/.cargo/git
          key: ${{ runner.os }}-cargo-git-${{ hashFiles('**/Cargo.lock') }}
      
      - name: Cache cargo build
        uses: actions/cache@v4
        with:
          path: target
          key: ${{ runner.os }}-cargo-build-${{ hashFiles('**/Cargo.lock') }}
      
      - name: Check format
        run: cargo fmt -- --check
      
      - name: Run clippy
        run: cargo clippy -- -D warnings
      
      - name: Build
        run: cargo build --verbose
      
      - name: Run tests
        run: cargo test --verbose

  security-audit:
    name: Security Audit
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: rustsec/audit-check@v1
        with:
          token: ${{ secrets.GITHUB_TOKEN }}
```

---

## 2. 测试工作流

**完整测试配置** (`.github/workflows/test.yml`):

```yaml
name: Rust Tests

on:
  push:
    branches: [ main ]
  pull_request:
    branches: [ main ]

jobs:
  test:
    name: Test Suite
    runs-on: ${{ matrix.os }}
    strategy:
      matrix:
        os: [ubuntu-latest, windows-latest, macos-latest]
        rust: [stable, 1.90, nightly]
    
    steps:
      - uses: actions/checkout@v4
      
      - name: Install Rust ${{ matrix.rust }}
        uses: dtolnay/rust-toolchain@master
        with:
          toolchain: ${{ matrix.rust }}
      
      - name: Run tests
        run: cargo test --all-features --verbose
      
      - name: Run doc tests
        run: cargo test --doc --verbose

  coverage:
    name: Code Coverage
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
      
      - name: Upload to codecov.io
        uses: codecov/codecov-action@v4
        with:
          files: lcov.info
          fail_ci_if_error: true
          token: ${{ secrets.CODECOV_TOKEN }}

  integration-test:
    name: Integration Tests with OTLP
    runs-on: ubuntu-latest
    services:
      jaeger:
        image: jaegertracing/all-in-one:latest
        ports:
          - 4317:4317
          - 4318:4318
          - 16686:16686
    
    steps:
      - uses: actions/checkout@v4
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
      
      - name: Run integration tests
        run: cargo test --test '*' --verbose
        env:
          OTLP_ENDPOINT: http://localhost:4317
          JAEGER_UI: http://localhost:16686
      
      - name: Check traces
        run: |
          sleep 5
          curl http://localhost:16686/api/traces?service=test-service
```

---

## 3. 性能基准测试

**Criterion 基准测试** (`.github/workflows/bench.yml`):

```yaml
name: Performance Benchmarks

on:
  push:
    branches: [ main ]
  pull_request:
    branches: [ main ]

jobs:
  benchmark:
    name: Run Benchmarks
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
      
      - name: Upload benchmark results
        uses: actions/upload-artifact@v4
        with:
          name: benchmark-results
          path: target/criterion/

  performance-regression:
    name: Performance Regression Check
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
        with:
          fetch-depth: 0
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
      
      - name: Run current benchmarks
        run: cargo bench --bench '*' > current.txt
      
      - name: Checkout main branch
        run: git checkout main
      
      - name: Run baseline benchmarks
        run: cargo bench --bench '*' > baseline.txt
      
      - name: Compare results
        run: |
          # 简单的性能回归检查
          echo "Comparing performance..."
          # 实际项目中应使用更复杂的比较逻辑
```

---

## 4. 发布工作流

**自动发布配置** (`.github/workflows/release.yml`):

```yaml
name: Release

on:
  push:
    tags:
      - 'v*'

env:
  CARGO_TERM_COLOR: always

jobs:
  create-release:
    name: Create Release
    runs-on: ubuntu-latest
    outputs:
      upload_url: ${{ steps.create_release.outputs.upload_url }}
    steps:
      - name: Create Release
        id: create_release
        uses: actions/create-release@v1
        env:
          GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
        with:
          tag_name: ${{ github.ref }}
          release_name: Release ${{ github.ref }}
          draft: false
          prerelease: false

  build-release:
    name: Build Release
    needs: create-release
    runs-on: ${{ matrix.os }}
    strategy:
      matrix:
        include:
          - os: ubuntu-latest
            target: x86_64-unknown-linux-gnu
            artifact_name: myapp
            asset_name: myapp-linux-amd64
          
          - os: ubuntu-latest
            target: x86_64-unknown-linux-musl
            artifact_name: myapp
            asset_name: myapp-linux-musl-amd64
          
          - os: windows-latest
            target: x86_64-pc-windows-msvc
            artifact_name: myapp.exe
            asset_name: myapp-windows-amd64.exe
          
          - os: macos-latest
            target: x86_64-apple-darwin
            artifact_name: myapp
            asset_name: myapp-macos-amd64
          
          - os: macos-latest
            target: aarch64-apple-darwin
            artifact_name: myapp
            asset_name: myapp-macos-arm64
    
    steps:
      - uses: actions/checkout@v4
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
        with:
          targets: ${{ matrix.target }}
      
      - name: Build release binary
        run: cargo build --release --target ${{ matrix.target }}
      
      - name: Strip binary (Linux/macOS)
        if: matrix.os != 'windows-latest'
        run: strip target/${{ matrix.target }}/release/${{ matrix.artifact_name }}
      
      - name: Upload Release Asset
        uses: actions/upload-release-asset@v1
        env:
          GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
        with:
          upload_url: ${{ needs.create-release.outputs.upload_url }}
          asset_path: ./target/${{ matrix.target }}/release/${{ matrix.artifact_name }}
          asset_name: ${{ matrix.asset_name }}
          asset_content_type: application/octet-stream

  publish-crate:
    name: Publish to crates.io
    needs: build-release
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
      
      - name: Publish
        run: cargo publish --token ${{ secrets.CRATES_IO_TOKEN }}
```

---

## 5. 完整生产配置

**完整的 CI/CD Pipeline** (`.github/workflows/production.yml`):

```yaml
name: Production Pipeline

on:
  push:
    branches: [ main ]
  pull_request:
    branches: [ main ]

env:
  CARGO_TERM_COLOR: always
  RUST_BACKTRACE: 1
  RUSTFLAGS: -D warnings

jobs:
  # 代码质量检查
  quality:
    name: Code Quality
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
        with:
          components: rustfmt, clippy
      
      - name: Format check
        run: cargo fmt -- --check
      
      - name: Clippy
        run: cargo clippy --all-targets --all-features -- -D warnings
      
      - name: Check documentation
        run: cargo doc --no-deps --all-features
        env:
          RUSTDOCFLAGS: -D warnings

  # 测试
  test:
    name: Test
    runs-on: ubuntu-latest
    services:
      postgres:
        image: postgres:16
        env:
          POSTGRES_PASSWORD: postgres
        options: >-
          --health-cmd pg_isready
          --health-interval 10s
          --health-timeout 5s
          --health-retries 5
        ports:
          - 5432:5432
      
      redis:
        image: redis:7
        options: >-
          --health-cmd "redis-cli ping"
          --health-interval 10s
          --health-timeout 5s
          --health-retries 5
        ports:
          - 6379:6379
      
      jaeger:
        image: jaegertracing/all-in-one:latest
        ports:
          - 4317:4317
          - 16686:16686
    
    steps:
      - uses: actions/checkout@v4
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
      
      - name: Cache
        uses: Swatinem/rust-cache@v2
      
      - name: Run unit tests
        run: cargo test --lib
      
      - name: Run integration tests
        run: cargo test --test '*'
        env:
          DATABASE_URL: postgres://postgres:postgres@localhost:5432/test
          REDIS_URL: redis://localhost:6379
          OTLP_ENDPOINT: http://localhost:4317
      
      - name: Run doc tests
        run: cargo test --doc

  # 安全审计
  security:
    name: Security
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Security audit
        uses: rustsec/audit-check@v1
      
      - name: Dependency review
        uses: actions/dependency-review-action@v4
        if: github.event_name == 'pull_request'

  # Docker 构建
  docker:
    name: Docker Build
    runs-on: ubuntu-latest
    if: github.event_name == 'push' && github.ref == 'refs/heads/main'
    needs: [quality, test, security]
    steps:
      - uses: actions/checkout@v4
      
      - name: Set up Docker Buildx
        uses: docker/setup-buildx-action@v3
      
      - name: Login to Docker Hub
        uses: docker/login-action@v3
        with:
          username: ${{ secrets.DOCKER_USERNAME }}
          password: ${{ secrets.DOCKER_PASSWORD }}
      
      - name: Build and push
        uses: docker/build-push-action@v5
        with:
          context: .
          push: true
          tags: |
            myorg/myapp:latest
            myorg/myapp:${{ github.sha }}
          cache-from: type=gha
          cache-to: type=gha,mode=max

  # 部署到 staging
  deploy-staging:
    name: Deploy to Staging
    runs-on: ubuntu-latest
    needs: docker
    if: github.event_name == 'push' && github.ref == 'refs/heads/main'
    environment:
      name: staging
      url: https://staging.example.com
    steps:
      - name: Deploy to Kubernetes
        run: |
          echo "Deploying to staging..."
          # kubectl apply -f k8s/staging/
```

**Dockerfile 优化**:

```dockerfile
# 多阶段构建
FROM rust:1.90-slim as builder

WORKDIR /app

# 复制依赖文件
COPY Cargo.toml Cargo.lock ./

# 缓存依赖
RUN mkdir src && \
    echo "fn main() {}" > src/main.rs && \
    cargo build --release && \
    rm -rf src

# 复制源代码
COPY src ./src

# 构建应用
RUN cargo build --release

# 运行时镜像
FROM debian:bookworm-slim

# 安装运行时依赖
RUN apt-get update && \
    apt-get install -y ca-certificates && \
    rm -rf /var/lib/apt/lists/*

# 复制二进制文件
COPY --from=builder /app/target/release/myapp /usr/local/bin/

# 设置环境变量
ENV RUST_LOG=info
ENV OTLP_ENDPOINT=http://localhost:4317

EXPOSE 8080

CMD ["myapp"]
```

---

**相关文档**:

- [GitLab CI Rust完整配置](02_GitLab_CI_Rust完整配置.md)
- [性能基准测试完整框架](../14_性能与基准测试/02_Rust_OTLP性能基准测试完整框架.md)

**文档状态**: ✅ 完成  
**最后更新**: 2025年10月9日
