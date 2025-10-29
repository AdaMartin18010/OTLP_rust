# 📖 项目改进术语表 (Glossary)

**最后更新**: 2025年10月29日

> 💡 快速理解项目改进中的专业术语

---

## 🎯 如何使用

- 🔤 **按字母顺序排列**
- 🔗 **相关术语交叉引用**
- 📚 **包含示例和链接**
- 🌐 **中英文对照**

---

## A

### Artifact (构建产物)

**定义**: CI/CD流程中产生的文件或数据，如编译后的二进制、测试报告、覆盖率报告等。

**示例**: 
```yaml
# GitHub Actions中保存artifact
- uses: actions/upload-artifact@v3
  with:
    name: coverage-report
    path: coverage/
```

**相关**: [CI/CD](#cicd-持续集成持续部署)

---

## C

### CI/CD (持续集成/持续部署)

**英文**: Continuous Integration / Continuous Deployment

**定义**: 自动化的软件开发实践，代码每次提交都会自动构建、测试和部署。

**本项目中**:
- **CI**: 自动运行测试、Clippy、格式检查
- **CD**: (未来) 自动部署到生产环境

**工具**: GitHub Actions

**相关文档**: [CI/CD说明](.github/workflows/README.md)

**相关**: [Workflow](#workflow-工作流)

---

### Clippy (Rust代码检查工具)

**定义**: Rust的官方linter，检查代码中的常见错误和不良实践。

**用法**:
```bash
cargo clippy --workspace --all-targets -- -D warnings
```

**检查类型**:
- 🐛 潜在bug
- 🎨 代码风格
- ⚡ 性能问题
- 📖 文档缺失

**相关**: [Linter](#linter-代码检查工具)

---

### Code Coverage (代码覆盖率)

**定义**: 测试执行时覆盖的代码比例，通常以百分比表示。

**类型**:
- **行覆盖率**: 执行的代码行比例
- **分支覆盖率**: 执行的条件分支比例
- **函数覆盖率**: 执行的函数比例

**目标**:
- 核心API: 80-90%
- 工具函数: 70-80%
- 示例代码: 50-70%

**工具**: cargo-tarpaulin

**相关**: [Tarpaulin](#tarpaulin-覆盖率工具)

---

## D

### Dependency (依赖)

**定义**: 项目需要的外部库或crate。

**类型**:
- **直接依赖**: 项目直接使用的
- **间接依赖**: 依赖的依赖

**问题**:
- **版本冲突**: 同一库有多个版本
- **僵尸依赖**: 不再使用但未删除
- **安全漏洞**: 依赖有已知漏洞

**管理工具**:
- `cargo tree` - 查看依赖树
- `cargo-audit` - 安全审计
- `cargo-outdated` - 过时检查
- `cargo-udeps` - 未使用检查

**相关文档**: [完整评估](analysis/CRITICAL_EVALUATION_REPORT_2025_10_29.md)

---

## G

### GitHub Actions

**定义**: GitHub提供的CI/CD自动化平台。

**本项目中的workflows**:
1. `ci.yml` - 基础CI
2. `coverage.yml` - 覆盖率
3. `security.yml` - 安全审计
4. `dependencies.yml` - 依赖管理

**优势**:
- ✅ 与GitHub深度集成
- ✅ 免费额度充足
- ✅ 配置简单

**相关文档**: [CI/CD说明](.github/workflows/README.md)

---

## H

### Health Score (健康度评分)

**定义**: 项目整体质量的量化评分，0-100分。

**评分维度**:
1. 技术前瞻性 (15%)
2. 架构设计 (15%)
3. 代码质量 (20%)
4. 测试覆盖 (15%)
5. 文档完整性 (10%)
6. 依赖管理 (15%)
7. 工程成熟度 (10%)

**当前评分**: 82/100

**计算方法**: 加权平均

**查看方式**:
```bash
./scripts/check_project_health.sh
```

**相关文档**: [执行摘要](analysis/EXECUTIVE_SUMMARY_2025_10_29.md)

---

## L

### Linter (代码检查工具)

**定义**: 静态分析工具，检查代码风格和潜在问题。

**Rust生态中**:
- **rustfmt**: 代码格式化
- **clippy**: 代码检查
- **cargo-deny**: 依赖策略检查

**使用**:
```bash
cargo clippy --workspace
cargo fmt --all --check
```

**相关**: [Clippy](#clippy-rust代码检查工具)

---

## M

### MSRV (Minimum Supported Rust Version)

**英文**: Minimum Supported Rust Version

**定义**: 项目支持的最低Rust版本。

**本项目**: Rust 1.90.0

**配置位置**:
- `Cargo.toml`: `rust-version = "1.90"`
- `rust-toolchain.toml`: `channel = "stable"`

**验证**:
```bash
cargo check --workspace
```

---

## O

### OTLP (OpenTelemetry Protocol)

**英文**: OpenTelemetry Protocol

**定义**: OpenTelemetry的标准协议，用于传输遥测数据。

**支持的信号**:
- Traces (追踪)
- Metrics (指标)
- Logs (日志)
- Profiles (性能分析)

**本项目**: OTLP的Rust实现

**相关**: [OpenTelemetry](#opentelemetry-开放遥测)

---

### OpenTelemetry (开放遥测)

**定义**: 云原生可观测性的开放标准和工具集。

**核心概念**:
- **Traces**: 分布式追踪
- **Metrics**: 指标收集
- **Logs**: 结构化日志
- **Context Propagation**: 上下文传播

**本项目角色**: 实现OTLP协议

**官网**: https://opentelemetry.io/

---

## P

### Phase (阶段)

**定义**: 项目改进计划的时间阶段。

**本项目的4个阶段**:

| 阶段 | 时间 | 目标 | 评分目标 |
|------|------|------|----------|
| **Phase 1** | 2周 | 紧急修复 | 85/100 |
| **Phase 2** | 2月 | 质量提升 | 88/100 |
| **Phase 3** | 6月 | 功能完善 | 92/100 |
| **Phase 4** | 12月 | 生产就绪 | 95+/100 |

**当前阶段**: Phase 1 准备中

**相关文档**: [行动计划](analysis/IMPROVEMENT_ACTION_PLAN_2025_10_29.md)

---

### Priority (优先级)

**定义**: 任务的重要程度和紧急程度。

**分级**:
- **🔴 P0 - 紧急**: 1-2周内必须解决
- **🟡 P1 - 重要**: 1-2月内应该解决
- **🟢 P2 - 优化**: 3-6月内可以解决

**决策依据**:
- 影响范围
- 阻塞程度
- 资源可用性

**相关**: [任务](#task-任务)

---

## R

### Rustfmt (Rust格式化工具)

**定义**: Rust官方的代码格式化工具。

**用法**:
```bash
# 格式化所有代码
cargo fmt --all

# 仅检查，不修改
cargo fmt --all -- --check
```

**配置文件**: `rustfmt.toml`

**CI中**: 自动检查格式

---

## S

### Semantic Convention (语义约定)

**定义**: OpenTelemetry定义的标准属性和命名规范。

**类别**:
- HTTP语义约定
- Database语义约定
- Messaging语义约定
- Kubernetes语义约定

**目的**: 统一不同系统的遥测数据格式

**示例**:
```rust
span.set_attribute("http.method", "GET");
span.set_attribute("http.status_code", 200);
```

---

## T

### Tarpaulin (覆盖率工具)

**定义**: Rust的代码覆盖率测试工具。

**安装**:
```bash
cargo install cargo-tarpaulin
```

**使用**:
```bash
cargo tarpaulin --workspace \
    --out Html \
    --out Lcov \
    --output-dir coverage/
```

**输出格式**:
- HTML - 可视化报告
- Lcov - 标准格式
- JSON - 机器可读

**相关**: [Code Coverage](#code-coverage-代码覆盖率)

---

### Task (任务)

**定义**: 改进计划中的具体工作项。

**本项目**: 14个任务

**任务结构**:
- **ID**: 唯一标识符 (如P0-1)
- **名称**: 任务描述
- **优先级**: P0/P1/P2
- **工作量**: 估算时间
- **验收标准**: 完成定义
- **负责人**: 谁来做
- **状态**: 待开始/进行中/已完成

**追踪**: [进度追踪](IMPROVEMENT_PROGRESS_TRACKER_2025_10_29.md)

---

## W

### Workflow (工作流)

**定义**: GitHub Actions中的自动化流程定义。

**组成**:
- **触发器** (on): 什么时候运行
- **作业** (jobs): 要做什么
- **步骤** (steps): 具体操作

**示例**:
```yaml
name: CI
on:
  push:
    branches: [main]
jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - run: cargo test
```

**本项目**: 4个workflows

**相关**: [GitHub Actions](#github-actions)

---

## 缩写词表

| 缩写 | 全称 | 中文 |
|------|------|------|
| **CI** | Continuous Integration | 持续集成 |
| **CD** | Continuous Deployment | 持续部署 |
| **PR** | Pull Request | 拉取请求 |
| **OTLP** | OpenTelemetry Protocol | 开放遥测协议 |
| **MSRV** | Minimum Supported Rust Version | 最低支持Rust版本 |
| **API** | Application Programming Interface | 应用程序接口 |
| **SDK** | Software Development Kit | 软件开发工具包 |
| **YAML** | YAML Ain't Markup Language | YAML不是标记语言 |
| **JSON** | JavaScript Object Notation | JavaScript对象表示法 |
| **HTTP** | Hypertext Transfer Protocol | 超文本传输协议 |
| **gRPC** | Google Remote Procedure Call | 谷歌远程过程调用 |

---

## 常用命令速查

### 健康检查
```bash
./scripts/check_project_health.sh
```

### 版本修复
```bash
./scripts/fix_opentelemetry_conflict.sh
```

### 覆盖率
```bash
./scripts/setup_coverage.sh
```

### 代码质量
```bash
cargo fmt --all
cargo clippy --workspace
cargo test --workspace
```

### 依赖管理
```bash
cargo tree
cargo update
cargo audit
```

---

## 相关资源

### 核心文档
- 📊 [执行摘要](analysis/EXECUTIVE_SUMMARY_2025_10_29.md)
- 📋 [完整评估](analysis/CRITICAL_EVALUATION_REPORT_2025_10_29.md)
- 🗓️ [行动计划](analysis/IMPROVEMENT_ACTION_PLAN_2025_10_29.md)
- ❓ [常见问题](IMPROVEMENT_FAQ.md)
- 📚 [资源索引](IMPROVEMENT_RESOURCES_INDEX.md)

### 官方文档
- [Rust官方文档](https://doc.rust-lang.org/)
- [Cargo指南](https://doc.rust-lang.org/cargo/)
- [OpenTelemetry文档](https://opentelemetry.io/docs/)
- [GitHub Actions文档](https://docs.github.com/en/actions)

---

## 贡献术语表

发现遗漏或错误？欢迎贡献！

**提交方式**:
1. Fork项目
2. 添加或修改术语
3. 提交PR
4. 标题: `docs: update glossary - add/fix XXX term`

**术语格式**:
```markdown
### 术语名称 (中文)

**英文**: English Name (如适用)

**定义**: 清晰的定义

**示例**: 代码或使用示例

**相关**: [其他术语](#链接)
```

---

**维护者**: 项目改进小组  
**最后更新**: 2025年10月29日  
**版本**: v1.0

---

*有疑问？查看 [FAQ](IMPROVEMENT_FAQ.md) 或在Discussions中提问！*

