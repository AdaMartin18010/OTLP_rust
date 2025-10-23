# ⚙️ CI/CD最佳实践

**创建日期**: 2025年10月23日  
**目标**: 建立高效、可靠的CI/CD流程  
**状态**: 持续推进中

---

## 🎯 CI/CD目标

### 当前状况

```text
┌─────────────────────────────────────────────┐
│          CI/CD现状                           │
├─────────────────────────────────────────────┤
│ 自动化测试:   部分配置                      │
│ 构建流程:     需优化                        │
│ 部署流程:     需建立                        │
│ 质量检查:     需加强                        │
│ 发布流程:     需自动化                      │
└─────────────────────────────────────────────┘
```

### 目标状态

```text
✅ 完整的自动化测试流程
✅ 快速的构建管道（<5分钟）
✅ 自动化质量检查
✅ 多平台构建和测试
✅ 自动化发布到crates.io
✅ 完整的监控和告警
```

---

## 🔧 核心CI工作流

### 1. 主CI流程

**文件**: `.github/workflows/ci.yml`

```yaml
name: CI

on:
  push:
    branches: [main, develop]
  pull_request:
    branches: [main, develop]

env:
  RUST_VERSION: 1.90
  CARGO_TERM_COLOR: always

jobs:
  # 快速检查（最快完成，快速反馈）
  quick-check:
    name: Quick Check
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Setup Rust
        uses: actions-rs/toolchain@v1
        with:
          profile: minimal
          toolchain: ${{ env.RUST_VERSION }}
          override: true
          components: rustfmt, clippy
      
      - name: Cache
        uses: Swatinem/rust-cache@v2
      
      - name: Format Check
        run: cargo fmt --all -- --check
      
      - name: Clippy
        run: cargo clippy --all-targets --all-features -- -D warnings
  
  # 测试（中等时间）
  test:
    name: Test
    needs: quick-check
    strategy:
      matrix:
        os: [ubuntu-latest, windows-latest, macos-latest]
        rust: [1.90, stable]
    runs-on: ${{ matrix.os }}
    steps:
      - uses: actions/checkout@v4
      
      - name: Setup Rust ${{ matrix.rust }}
        uses: actions-rs/toolchain@v1
        with:
          profile: minimal
          toolchain: ${{ matrix.rust }}
          override: true
      
      - name: Cache
        uses: Swatinem/rust-cache@v2
      
      - name: Build
        run: cargo build --workspace --all-features
      
      - name: Test
        run: cargo test --workspace --all-features -- --nocapture
      
      - name: Doc Test
        run: cargo test --doc --workspace --all-features
  
  # 覆盖率（较慢）
  coverage:
    name: Code Coverage
    needs: test
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Setup Rust
        uses: actions-rs/toolchain@v1
        with:
          profile: minimal
          toolchain: ${{ env.RUST_VERSION }}
          override: true
      
      - name: Install tarpaulin
        run: cargo install cargo-tarpaulin
      
      - name: Generate coverage
        run: cargo tarpaulin --out Xml --all-features
      
      - name: Upload to codecov
        uses: codecov/codecov-action@v3
        with:
          files: ./cobertura.xml
          fail_ci_if_error: true
```

### 2. 安全审计工作流

**文件**: `.github/workflows/security.yml`

```yaml
name: Security Audit

on:
  schedule:
    - cron: '0 0 * * *'  # 每天UTC 0点
  push:
    paths:
      - 'Cargo.toml'
      - 'Cargo.lock'
  pull_request:
    paths:
      - 'Cargo.toml'
      - 'Cargo.lock'

jobs:
  audit:
    name: Security Audit
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Cargo Audit
        uses: rustsec/audit-check@v1.4.1
        with:
          token: ${{ secrets.GITHUB_TOKEN }}
  
  deny:
    name: Cargo Deny
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Cargo Deny
        uses: EmbarkStudios/cargo-deny-action@v1
```

### 3. 性能基准工作流

**文件**: `.github/workflows/benchmark.yml`

```yaml
name: Benchmark

on:
  push:
    branches: [main]
  pull_request:
    branches: [main]

jobs:
  benchmark:
    name: Run Benchmarks
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Setup Rust
        uses: actions-rs/toolchain@v1
        with:
          profile: minimal
          toolchain: stable
          override: true
      
      - name: Cache
        uses: Swatinem/rust-cache@v2
      
      - name: Run benchmarks
        run: cargo bench --workspace -- --output-format bencher | tee output.txt
      
      - name: Store benchmark result
        uses: benchmark-action/github-action-benchmark@v1
        with:
          tool: 'cargo'
          output-file-path: output.txt
          github-token: ${{ secrets.GITHUB_TOKEN }}
          auto-push: true
```

---

## 🚀 发布工作流

### 自动化发布

**文件**: `.github/workflows/release.yml`

```yaml
name: Release

on:
  push:
    tags:
      - 'v*.*.*'

env:
  RUST_VERSION: 1.90

jobs:
  # 创建GitHub Release
  create-release:
    name: Create Release
    runs-on: ubuntu-latest
    outputs:
      upload_url: ${{ steps.create_release.outputs.upload_url }}
    steps:
      - uses: actions/checkout@v4
      
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
  
  # 构建二进制文件
  build:
    name: Build ${{ matrix.target }}
    needs: create-release
    strategy:
      matrix:
        include:
          - os: ubuntu-latest
            target: x86_64-unknown-linux-gnu
          - os: windows-latest
            target: x86_64-pc-windows-msvc
          - os: macos-latest
            target: x86_64-apple-darwin
    runs-on: ${{ matrix.os }}
    steps:
      - uses: actions/checkout@v4
      
      - name: Setup Rust
        uses: actions-rs/toolchain@v1
        with:
          profile: minimal
          toolchain: ${{ env.RUST_VERSION }}
          override: true
          target: ${{ matrix.target }}
      
      - name: Build
        run: cargo build --release --target ${{ matrix.target }}
      
      - name: Package (Unix)
        if: matrix.os != 'windows-latest'
        run: |
          cd target/${{ matrix.target }}/release
          tar czf otlp-rust-${{ matrix.target }}.tar.gz otlp-rust
          echo "ASSET=otlp-rust-${{ matrix.target }}.tar.gz" >> $GITHUB_ENV
      
      - name: Package (Windows)
        if: matrix.os == 'windows-latest'
        run: |
          cd target/${{ matrix.target }}/release
          7z a otlp-rust-${{ matrix.target }}.zip otlp-rust.exe
          echo "ASSET=otlp-rust-${{ matrix.target }}.zip" >> $env:GITHUB_ENV
      
      - name: Upload Release Asset
        uses: actions/upload-release-asset@v1
        env:
          GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
        with:
          upload_url: ${{ needs.create-release.outputs.upload_url }}
          asset_path: ./target/${{ matrix.target }}/release/${{ env.ASSET }}
          asset_name: ${{ env.ASSET }}
          asset_content_type: application/octet-stream
  
  # 发布到crates.io
  publish:
    name: Publish to crates.io
    needs: build
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Setup Rust
        uses: actions-rs/toolchain@v1
        with:
          profile: minimal
          toolchain: ${{ env.RUST_VERSION }}
          override: true
      
      - name: Publish
        run: cargo publish --token ${{ secrets.CARGO_TOKEN }}
```

---

## 📊 质量门禁

### 质量标准

**必须通过的检查**:

```yaml
# .github/workflows/quality-gate.yml
name: Quality Gate

on:
  pull_request:
    branches: [main]

jobs:
  quality-gate:
    name: Quality Gate
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Setup Rust
        uses: actions-rs/toolchain@v1
        with:
          profile: minimal
          toolchain: 1.90
          override: true
          components: rustfmt, clippy
      
      - name: Cache
        uses: Swatinem/rust-cache@v2
      
      # 1. 代码格式
      - name: Check Formatting
        run: cargo fmt --all -- --check
      
      # 2. Clippy警告
      - name: Clippy (no warnings)
        run: cargo clippy --all-targets --all-features -- -D warnings
      
      # 3. 测试覆盖率
      - name: Test Coverage
        run: |
          cargo install cargo-tarpaulin
          cargo tarpaulin --out Xml
          
          # 检查覆盖率 >= 80%
          coverage=$(cargo tarpaulin --out Json | jq '.files | map(.covered_percent) | add / length')
          echo "Coverage: $coverage%"
          if (( $(echo "$coverage < 80" | bc -l) )); then
            echo "Coverage below 80%!"
            exit 1
          fi
      
      # 4. 文档完整性
      - name: Check Docs
        run: |
          cargo doc --no-deps --all-features
          
          # 检查是否有missing docs警告
          cargo rustdoc --all-features -- -D missing-docs
      
      # 5. 依赖安全
      - name: Security Audit
        run: |
          cargo install cargo-audit
          cargo audit
```

---

## ⚡ 性能优化

### 缓存策略

**1. Rust编译缓存**:

```yaml
- name: Cache Cargo Registry
  uses: actions/cache@v3
  with:
    path: ~/.cargo/registry
    key: ${{ runner.os }}-cargo-registry-${{ hashFiles('**/Cargo.lock') }}

- name: Cache Cargo Index
  uses: actions/cache@v3
  with:
    path: ~/.cargo/git
    key: ${{ runner.os }}-cargo-index-${{ hashFiles('**/Cargo.lock') }}

- name: Cache Target Directory
  uses: actions/cache@v3
  with:
    path: target
    key: ${{ runner.os }}-target-${{ hashFiles('**/Cargo.lock') }}
```

**2. 使用rust-cache action**（推荐）:

```yaml
- name: Cache
  uses: Swatinem/rust-cache@v2
  with:
    shared-key: "build"
    cache-on-failure: true
```

### 并行化构建

**策略矩阵**:

```yaml
strategy:
  matrix:
    os: [ubuntu-latest, windows-latest, macos-latest]
    rust: [1.90, stable, beta]
  fail-fast: false  # 一个失败不影响其他
```

### 增量编译

```yaml
env:
  CARGO_INCREMENTAL: 1  # 启用增量编译
  CARGO_NET_RETRY: 10   # 网络重试
  RUST_BACKTRACE: short # 简短的回溯
```

---

## 📈 监控和通知

### 失败通知

**Slack通知**:

```yaml
- name: Notify Slack on Failure
  if: failure()
  uses: 8398a7/action-slack@v3
  with:
    status: ${{ job.status }}
    text: 'CI build failed!'
    webhook_url: ${{ secrets.SLACK_WEBHOOK }}
```

### 性能趋势

**存储基准结果**:

```yaml
- name: Store benchmark result
  uses: benchmark-action/github-action-benchmark@v1
  with:
    tool: 'cargo'
    output-file-path: output.txt
    github-token: ${{ secrets.GITHUB_TOKEN }}
    auto-push: true
    alert-threshold: '150%'  # 性能下降超过50%时告警
    comment-on-alert: true
    fail-on-alert: true
```

---

## 🔄 分支策略

### Git Flow

**分支模型**:

```text
main (production)
  ↓ release branch
develop (development)
  ↓ feature branches
  ↓ hotfix branches
```

**CI触发规则**:

```yaml
on:
  push:
    branches:
      - main
      - develop
      - 'release/**'
  pull_request:
    branches:
      - main
      - develop
```

---

## 📋 最佳实践清单

### CI配置

- [ ] 快速反馈（<10分钟）
- [ ] 并行化测试
- [ ] 缓存依赖
- [ ] 多平台测试
- [ ] 增量构建
- [ ] 失败快速（fail-fast）

### 测试策略

- [ ] 单元测试（快）
- [ ] 集成测试（中）
- [ ] E2E测试（慢）
- [ ] 性能测试
- [ ] 安全扫描

### 发布流程

- [ ] 自动版本管理
- [ ] 生成CHANGELOG
- [ ] 多平台构建
- [ ] 自动发布到crates.io
- [ ] 创建GitHub Release
- [ ] 发布通知

---

## 🎯 CI/CD成熟度

### 当前级别

```text
Level 1: 基础CI ✅
- 自动化构建
- 基本测试

Level 2: 自动化测试 ✅
- 完整测试套件
- 代码覆盖率

Level 3: 持续部署 ⏳
- 自动化发布
- 环境管理

Level 4: 监控和反馈 ⏳
- 性能监控
- 自动告警

Level 5: 优化和创新 🎯
- AI辅助测试
- 自动优化
```

---

## 📞 故障排查

### 常见问题

**1. 构建超时**:

```yaml
# 增加超时时间
jobs:
  build:
    timeout-minutes: 60
```

**2. 缓存失效**:

```bash
# 清理缓存
gh cache delete <cache-id>
```

**3. 依赖下载失败**:

```yaml
env:
  CARGO_NET_RETRY: 10
  CARGO_NET_TIMEOUT: 300
```

---

**创建者**: AI Assistant  
**创建日期**: 2025年10月23日  
**版本**: 1.0
