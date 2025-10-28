# GitHub Actions Workflows

本目录包含项目的所有CI/CD自动化workflow。

**最后更新**: 2025年10月29日

---

## 📋 Workflow列表

### 1. 🔄 基础CI (ci.yml)

**触发条件**:
- Push到main或develop分支
- Pull Request到main或develop分支

**检查项**:
- ✅ 代码格式检查 (cargo fmt)
- ✅ 编译检查 (cargo check)
- ✅ 测试 (多平台: Ubuntu/Windows/macOS)
- ✅ Clippy静态分析
- ✅ 文档构建验证
- ✅ OpenTelemetry版本冲突检查
- ✅ MSRV验证 (Rust 1.90.0)

**运行时间**: 约10-15分钟

**查看结果**: 
```
Actions → CI → 查看最新运行
```

---

### 2. 📊 测试覆盖率 (coverage.yml)

**触发条件**:
- Push到main分支
- Pull Request到main分支
- 每周一早上8点 (定时)

**功能**:
- 📊 生成测试覆盖率报告
- 📤 上传到Codecov
- 💬 在PR中自动评论覆盖率
- 📦 保存HTML报告为artifact

**输出**:
- `coverage/index.html` - 可视化报告
- `coverage/cobertura.xml` - Lcov格式
- `coverage/tarpaulin-report.json` - JSON数据

**查看覆盖率**:
1. 访问Actions → Coverage
2. 下载`coverage-report` artifact
3. 打开`index.html`

---

### 3. 🔐 安全审计 (security.yml)

**触发条件**:
- Push到main分支 (Cargo.toml/Cargo.lock变更)
- 每天凌晨2点 (定时)
- 手动触发

**检查项**:
- 🔍 cargo-audit - 已知安全漏洞
- ⚖️ cargo-deny - 许可证和依赖策略
- 📋 dependency-review - 依赖变更审查 (仅PR)

**处理流程**:
1. 检测到漏洞 → CI失败
2. 查看audit报告 → 识别问题
3. 更新依赖 → 修复漏洞
4. 重新运行 → 验证修复

**查看报告**:
```
Actions → Security Audit → 查看最新运行 → 下载artifact
```

---

### 4. 📦 依赖管理 (dependencies.yml)

**触发条件**:
- 每周一早上9点 (定时)
- 手动触发

**检查项**:
- 📤 过时依赖检查 (cargo-outdated)
- 🗑️ 未使用依赖检查 (cargo-udeps)
- 🌳 依赖树生成

**输出**:
- `outdated-dependencies-report.json`
- `unused-dependencies-report.json`
- `dependency-tree.md`

**如何使用**:
1. 每周查看报告
2. 评估是否需要更新
3. 创建Issue跟踪更新任务
4. 测试后更新依赖

---

## 🔧 配置说明

### 通用环境变量

```yaml
env:
  CARGO_TERM_COLOR: always  # 彩色输出
  RUST_BACKTRACE: 1         # 错误堆栈
  RUSTFLAGS: -D warnings    # 警告视为错误
```

### 缓存策略

所有workflow使用 `Swatinem/rust-cache@v2` 缓存依赖:
- 自动缓存 `~/.cargo` 和 `target/`
- 基于Cargo.lock哈希
- 大幅提升构建速度

### Secrets配置

需要配置的secrets:
- `CODECOV_TOKEN` - Codecov上传token (可选)

---

## 📊 状态徽章

在README.md中添加徽章:

```markdown
![CI](https://github.com/<owner>/<repo>/workflows/CI/badge.svg)
![Coverage](https://github.com/<owner>/<repo>/workflows/Coverage/badge.svg)
![Security](https://github.com/<owner>/<repo>/workflows/Security%20Audit/badge.svg)
```

---

## 🔍 故障排查

### CI失败常见原因

#### 1. 编译错误

**症状**: `cargo check` 失败

**解决**:
```bash
# 本地验证
cargo check --workspace
```

#### 2. 测试失败

**症状**: `cargo test` 失败

**解决**:
```bash
# 本地运行测试
cargo test --workspace --verbose
```

#### 3. Clippy警告

**症状**: `cargo clippy` 有警告

**解决**:
```bash
# 查看警告
cargo clippy --workspace --all-targets

# 自动修复部分问题
cargo clippy --workspace --all-targets --fix
```

#### 4. 格式问题

**症状**: `cargo fmt` 检查失败

**解决**:
```bash
# 格式化代码
cargo fmt --all
```

#### 5. 依赖冲突

**症状**: 依赖检查失败

**解决**:
```bash
# 使用自动化脚本
./scripts/fix_opentelemetry_conflict.sh
```

---

## 🚀 最佳实践

### 1. 本地验证

提交前在本地运行:
```bash
# 完整检查
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
```

或使用健康度检查脚本:
```bash
./scripts/check_project_health.sh
```

### 2. PR要求

合并到main分支的PR必须:
- ✅ 所有CI检查通过
- ✅ 至少1个approving review
- ✅ 覆盖率不下降
- ✅ 无新的安全漏洞

### 3. 定期审查

- **每周**: 查看依赖管理报告
- **每月**: 审查安全审计趋势
- **每季度**: 评估CI/CD效率

---

## 📝 添加新的Workflow

### 步骤

1. 创建新的YAML文件
```bash
touch .github/workflows/new-workflow.yml
```

2. 定义workflow
```yaml
name: New Workflow

on:
  push:
    branches: [ main ]

jobs:
  job-name:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      # ... 其他步骤
```

3. 测试workflow
```bash
git add .github/workflows/new-workflow.yml
git commit -m "ci: add new workflow"
git push
```

4. 验证运行
- 访问Actions页面
- 查看运行结果
- 调整配置

---

## 📚 参考资料

- [GitHub Actions文档](https://docs.github.com/en/actions)
- [Rust CI/CD最佳实践](https://doc.rust-lang.org/cargo/guide/continuous-integration.html)
- [项目改进行动计划](../../analysis/IMPROVEMENT_ACTION_PLAN_2025_10_29.md)

---

## 🤝 贡献

改进workflow? 欢迎提交PR:
1. 修改workflow文件
2. 本地验证（如可能）
3. 提交PR并说明改进点
4. 等待审查和合并

---

*CI/CD是项目质量保证的基石。保持workflow简洁、快速、可靠！*

