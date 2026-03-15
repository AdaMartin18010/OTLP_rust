# GitHub 配置项和规范指南

**项目**: OTLP Rust
**版本**: 适配 Rust 1.94.0
**更新日期**: 2026-03-15

---

## 📁 GitHub 配置结构

```text
.github/
├── workflows/                    # CI/CD 工作流
│   ├── ci.yml                    # 基础 CI
│   ├── ci-cd.yml                 # 完整 CI/CD 管道
│   ├── coverage.yml              # 测试覆盖率
│   ├── security.yml              # 安全审计
│   ├── security-audit.yml        # 详细安全扫描
│   ├── dependencies.yml          # 依赖管理
│   ├── docs-quality.yml          # 文档质量检查
│   ├── e2e.yml                   # 端到端测试
│   ├── ebpf-tests.yml            # eBPF 测试
│   ├── performance.yml           # 性能基准
│   ├── reliability-ci.yml        # 可靠性 CI
│   └── README.md                 # 工作流文档
│
├── ISSUE_TEMPLATE/               # Issue 模板
│   ├── bug_report.md             # Bug 报告模板
│   └── feature_request.md        # 功能请求模板
│
├── PULL_REQUEST_TEMPLATE.md      # PR 模板
├── CODEOWNERS                    # 代码所有者
├── actionlint.yml                # Actionlint 配置
└── FUNDING.yml                   # 赞助配置

SECURITY.md                       # 安全策略
CONTRIBUTING.md                   # 贡献指南
```

---

## 🔧 配置项详解

### 1. CODEOWNERS

**文件**: `.github/CODEOWNERS`

**作用**: 定义代码审查责任人和自动分配规则

```text
# 格式: 路径模式 @用户名或团队

# 全局所有者
* @luyan

# 特定模块
/crates/otlp/src/ebpf/ @ebpf-maintainer
/crates/otlp/src/simd/ @performance-maintainer
```

**更新指南**:

- 添加新模块时，指定对应的维护者
- 团队扩展时，更新代码所有者
- 模块移交时，同步更新此文件

---

### 2. CI/CD Workflows

#### 2.1 基础 CI (ci.yml)

| 配置项 | 值 | 说明 |
|--------|-----|------|
| Rust版本 | 1.94 | 固定版本确保一致性 |
| 触发条件 | push到main/develop, PR | 标准触发 |
| 平台 | Ubuntu/Windows/macOS | 跨平台测试 |
| 检查项 | fmt, check, clippy, test | 完整质量检查 |

**关键配置**:

```yaml
- uses: dtolnay/rust-toolchain@1.94  # Rust 版本
- uses: Swatinem/rust-cache@v2       # 缓存加速
```

#### 2.2 安全审计 (security.yml)

| 配置项 | 值 | 说明 |
|--------|-----|------|
| 工具 | cargo-audit, cargo-deny | 安全检查 |
| 频率 | 每天 + 依赖变更时 | 持续监控 |
| 报告 | 自动上传 | 可追溯 |

#### 2.3 测试覆盖率 (coverage.yml)

| 配置项 | 值 | 说明 |
|--------|-----|------|
| 工具 | cargo-tarpaulin | Rust 覆盖率 |
| 输出 | XML, HTML, Lcov | 多格式支持 |
| 上传 | Codecov | 可视化报告 |

#### 2.4 依赖管理 (dependencies.yml)

| 配置项 | 值 | 说明 |
|--------|-----|------|
| 工具 | cargo-outdated | 过时检查 |
| 频率 | 每周一 | 定期维护 |
| 报告 | JSON格式 | 自动化处理 |

---

### 3. Issue/PR 模板

#### 3.1 Bug 报告模板

**文件**: `.github/ISSUE_TEMPLATE/bug_report.md`

**必填项**:

- Bug 描述
- 复现步骤
- 预期/实际行为
- 环境信息（Rust 版本等）

**更新指南**:

- Rust 版本要求变化时更新模板
- 新增诊断脚本时添加提示

#### 3.2 功能请求模板

**文件**: `.github/ISSUE_TEMPLATE/feature_request.md`

**必填项**:

- 功能描述
- 用例场景
- API 设计（如适用）
- 验收标准

#### 3.3 PR 模板

**文件**: `.github/PULL_REQUEST_TEMPLATE.md`

**必填项**:

- PR 类型
- 变更描述
- 测试覆盖
- 代码质量检查清单

---

### 4. 安全策略 (SECURITY.md)

**文件**: `SECURITY.md`

**内容**:

- 支持的版本
- 漏洞报告流程
- 响应时间表
- 安全最佳实践

**更新指南**:

- 新版本发布时更新支持版本表
- 安全联系人变化时更新
- 新增安全功能时补充

---

### 5. 贡献指南 (CONTRIBUTING.md)

**文件**: `CONTRIBUTING.md`

**关键章节**:

- 开发环境设置
- 代码规范
- 测试要求
- PR 流程
- Commit 规范

**更新指南**:

- Rust 版本要求变化时更新
- 新工具引入时补充
- 流程变化时同步

---

## 🔄 配置更新清单

### Rust 版本升级时

当升级 Rust 版本（如 1.94 → 1.95）:

- [ ] 更新 `ci.yml` - `dtolnay/rust-toolchain@1.94`
- [ ] 更新 `coverage.yml`
- [ ] 更新 `security.yml`
- [ ] 更新 `dependencies.yml`
- [ ] 更新 `performance.yml`
- [ ] 更新 `e2e.yml`
- [ ] 更新 `workflows/README.md`
- [ ] 更新 `CONTRIBUTING.md` 中的版本要求
- [ ] 更新 Issue 模板中的版本提示
- [ ] 测试所有 workflows

### 新增 crate 时

当添加新 crate:

- [ ] 在 `CODEOWNERS` 中添加所有者
- [ ] 更新 `ci.yml` 测试范围
- [ ] 更新 `ci-cd.yml` 构建范围
- [ ] 添加特定的 workflow（如需要）

### 依赖工具变更时

当更换 CI 工具:

- [ ] 更新对应的 workflow
- [ ] 更新 `workflows/README.md` 文档
- [ ] 更新 secrets 配置说明
- [ ] 测试新工具

---

## 🛡️ Secrets 配置

需要在 GitHub Settings > Secrets 中配置:

| Secret | 用途 | 必需 |
|--------|------|------|
| `CODECOV_TOKEN` | 覆盖率上传 | 可选 |
| `DOCKER_USERNAME` | Docker 构建 | 仅部署 |
| `DOCKER_PASSWORD` | Docker 构建 | 仅部署 |
| `KUBE_CONFIG_STAGING` | K8s 部署 | 仅部署 |
| `KUBE_CONFIG_PRODUCTION` | K8s 部署 | 仅部署 |
| `SLACK_WEBHOOK` | 通知 | 可选 |
| `GITHUB_TOKEN` | 自动提供 | 必需 |

---

## 📝 最佳实践

### Workflow 编写

1. **使用最新稳定 Action 版本**

   ```yaml
   - uses: actions/checkout@v4  # 不是 v3
   ```

2. **启用缓存加速**

   ```yaml
   - uses: Swatinem/rust-cache@v2
   ```

3. **固定 Rust 版本**

   ```yaml
   - uses: dtolnay/rust-toolchain@1.94
   ```

4. **并行执行**

   ```yaml
   strategy:
     matrix:
       os: [ubuntu-latest, windows-latest, macos-latest]
   ```

5. **错误处理**

   ```yaml
   continue-on-error: true  # 非关键步骤
   ```

### Issue/PR 管理

1. **标签系统**
   - `bug`: Bug 报告
   - `enhancement`: 功能请求
   - `documentation`: 文档
   - `good first issue`: 新手友好
   - `help wanted`: 需要帮助

2. **里程碑管理**
   - 为每个版本创建里程碑
   - 将 Issue/PR 关联到里程碑

3. **项目看板**
   - 使用 GitHub Projects 跟踪进度
   - 列: To Do, In Progress, Review, Done

---

## 🚀 快速参考

### 手动触发 Workflow

```bash
# 使用 gh CLI
gh workflow run ci.yml

# 在网页上
Actions > 选择 Workflow > Run workflow
```

### 调试失败的 CI

1. 下载日志:

   ```bash
   gh run download <run-id>
   ```

2. 本地复现:

   ```bash
   cargo check --workspace
   cargo test --workspace
   cargo clippy --workspace -- -D warnings
   ```

### 更新 Workflow

```bash
# 1. 修改 workflow 文件
vim .github/workflows/ci.yml

# 2. 提交更改
git add .github/workflows/ci.yml
git commit -m "ci: update Rust version to 1.95"
git push

# 3. 验证运行
gh run watch
```

---

## 📊 状态徽章

在 README.md 中添加:

```markdown
![CI](https://github.com/luyan/OTLP_rust/workflows/CI/badge.svg)
![Coverage](https://github.com/luyan/OTLP_rust/workflows/Coverage/badge.svg)
![Security](https://github.com/luyan/OTLP_rust/workflows/Security%20Audit/badge.svg)
```

---

## 🔗 相关链接

- [GitHub Actions 文档](https://docs.github.com/en/actions)
- [Rust CI/CD 最佳实践](https://doc.rust-lang.org/cargo/guide/continuous-integration.html)
- [actionlint 配置](https://github.com/rhysd/actionlint)

---

**维护**: @luyan
**更新频率**: 每次 Rust 版本升级或 CI 工具变更
