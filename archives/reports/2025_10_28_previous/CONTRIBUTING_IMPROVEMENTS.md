# 🤝 贡献项目改进指南

欢迎为OTLP_rust项目的改进工作做出贡献！

**最后更新**: 2025年10月29日

---

## 📋 目录

- [快速开始](#-快速开始)
- [改进优先级](#-改进优先级)
- [贡献流程](#-贡献流程)
- [开发规范](#-开发规范)
- [测试要求](#-测试要求)
- [文档要求](#-文档要求)
- [代码审查](#-代码审查)

---

## 🚀 快速开始

### 1. 环境准备

```bash
# 1. Fork并克隆仓库
git clone https://github.com/<your-username>/OTLP_rust.git
cd OTLP_rust

# 2. 安装Rust 1.90.0
rustup update
rustup default 1.90

# 3. 检查项目健康度
./scripts/check_project_health.sh

# 4. 运行测试
cargo test --workspace
```

### 2. 选择任务

查看 [改进行动计划](analysis/IMPROVEMENT_ACTION_PLAN_2025_10_29.md) 或 [进度追踪](IMPROVEMENT_PROGRESS_TRACKER_2025_10_29.md)，选择一个未被认领的任务。

### 3. 认领任务

在对应的Issue中评论：
```
我想认领这个任务，预计X天完成。
```

---

## 🎯 改进优先级

### 🔴 P0 - 紧急优先级 (当前Phase 1)

**时间范围**: Week 1-2

| 任务ID | 任务名称 | 工作量 | 状态 | 认领人 |
|--------|----------|--------|------|--------|
| P0-1 | OpenTelemetry版本冲突修复 | 4h | ⏳ | 待认领 |
| P0-2 | 建立测试覆盖率基准 | 8h | ⏳ | 待认领 |
| P0-3 | CI/CD验证和调试 | 4h | ⏳ | 待认领 |
| P0-4 | 代码质量修复 | 4h | ⏳ | 待认领 |

**如何贡献**:
1. 查看 [快速开始指南](QUICK_START_IMPROVEMENT.md)
2. 选择一个P0任务
3. 按照任务说明执行
4. 提交PR

### 🟡 P1 - 重要优先级 (Phase 2)

**时间范围**: Month 1-2

| 任务ID | 任务名称 | 工作量 | 状态 | 认领人 |
|--------|----------|--------|------|--------|
| P1-1 | 依赖审查和清理 | 3天 | ⏳ | 待认领 |
| P1-2 | 代码组织重构 | 1周 | ⏳ | 待认领 |
| P1-3 | 测试覆盖率提升 | 2周 | ⏳ | 待认领 |
| P1-4 | 添加实战示例 | 1周 | ⏳ | 待认领 |

### 🟢 P2 - 优化优先级 (Phase 3-4)

**时间范围**: Month 3-12

查看完整列表: [改进行动计划](analysis/IMPROVEMENT_ACTION_PLAN_2025_10_29.md)

---

## 🔄 贡献流程

### 1. 创建分支

```bash
# 从最新的main分支创建
git checkout main
git pull origin main

# 创建功能分支，命名规范：
# - fix/<issue-id>-<short-description>  # bug修复
# - feat/<issue-id>-<short-description> # 新功能
# - docs/<short-description>            # 文档更新
# - refactor/<short-description>        # 代码重构
# - test/<short-description>            # 测试相关

git checkout -b fix/123-opentelemetry-conflict
```

### 2. 进行修改

```bash
# 2.1 进行你的修改
# ...

# 2.2 运行质量检查
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace

# 2.3 生成覆盖率（可选，但推荐）
./scripts/setup_coverage.sh
```

### 3. 提交变更

```bash
# 提交规范（遵循Conventional Commits）:
# - feat: 新功能
# - fix: Bug修复
# - docs: 文档更新
# - style: 格式化（不影响代码运行）
# - refactor: 重构
# - test: 测试相关
# - chore: 构建/工具相关

git add .
git commit -m "fix: resolve OpenTelemetry version conflict

- Add patch.crates-io section to unify version
- Update to opentelemetry 0.31.0
- Run cargo update
- Verify all tests pass

Closes #123"
```

### 4. 推送并创建PR

```bash
# 推送到你的fork
git push origin fix/123-opentelemetry-conflict

# 然后在GitHub上创建Pull Request
```

### 5. PR模板

PR会自动加载模板，请完整填写所有必要信息：
- PR类型
- 变更描述
- 测试说明
- 影响范围
- 质量检查清单

---

## 📝 开发规范

### 代码风格

#### Rust代码规范

```rust
// 1. 使用rustfmt默认配置
cargo fmt --all

// 2. 遵循Clippy建议
cargo clippy --workspace --all-targets -- -D warnings

// 3. 命名规范
// - 类型: PascalCase
// - 函数/变量: snake_case
// - 常量: SCREAMING_SNAKE_CASE
// - 生命周期: 'short_lowercase

// 4. 文档注释
/// 公开API必须有文档注释
///
/// # Examples
///
/// ```
/// use otlp::client::OtlpClient;
/// let client = OtlpClient::new("http://localhost:4317");
/// ```
pub fn public_api() {}

// 5. 错误处理
// - 使用Result类型
// - 错误类型使用thiserror
// - 提供有意义的错误信息

use thiserror::Error;

#[derive(Error, Debug)]
pub enum MyError {
    #[error("connection failed: {0}")]
    ConnectionFailed(String),
}
```

#### 项目结构规范

```
crates/
├── otlp/           # OTLP核心实现
│   ├── src/
│   │   ├── client/     # 按功能模块组织
│   │   ├── transport/
│   │   └── ...
│   ├── tests/      # 集成测试
│   ├── examples/   # 示例代码
│   └── benches/    # 性能测试
```

### Commit规范

遵循 [Conventional Commits](https://www.conventionalcommits.org/):

```
<type>(<scope>): <subject>

<body>

<footer>
```

**示例**:
```
feat(client): add retry mechanism

Implement exponential backoff retry for failed requests.

- Add RetryPolicy struct
- Implement retry logic in HttpTransport
- Add tests for retry scenarios

Closes #123
```

**类型**:
- `feat`: 新功能
- `fix`: Bug修复
- `docs`: 文档更新
- `style`: 代码格式化
- `refactor`: 重构
- `perf`: 性能优化
- `test`: 测试相关
- `chore`: 构建/工具

---

## ✅ 测试要求

### 测试金字塔

```
     /\
    /  \  E2E Tests (10%)
   /────\
  /      \  Integration Tests (20%)
 /────────\
/          \  Unit Tests (70%)
```

### 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_functionality() {
        // Arrange
        let input = setup_test_data();
        
        // Act
        let result = function_under_test(input);
        
        // Assert
        assert_eq!(result, expected_value);
    }

    #[tokio::test]
    async fn test_async_functionality() {
        let client = TestClient::new().await;
        let result = client.send_data().await;
        assert!(result.is_ok());
    }
}
```

### 集成测试

```rust
// tests/integration_test.rs
use otlp::client::OtlpClient;

#[tokio::test]
async fn test_full_workflow() {
    // Setup
    let client = OtlpClient::builder()
        .endpoint("http://localhost:4317")
        .build()
        .await
        .unwrap();
    
    // Execute
    let result = client.send_trace(test_data()).await;
    
    // Verify
    assert!(result.is_ok());
}
```

### 覆盖率要求

| 模块类型 | 最低覆盖率 | 目标覆盖率 |
|----------|-----------|-----------|
| **核心API** | 80% | 90% |
| **工具函数** | 70% | 80% |
| **示例代码** | 50% | 70% |

### 运行测试

```bash
# 所有测试
cargo test --workspace

# 特定crate
cargo test -p otlp

# 特定测试
cargo test test_name

# 覆盖率
./scripts/setup_coverage.sh
```

---

## 📚 文档要求

### 代码文档

#### 1. 公开API必须有文档

```rust
/// 创建新的OTLP客户端
///
/// # Arguments
///
/// * `endpoint` - OTLP收集器的endpoint URL
///
/// # Returns
///
/// 返回配置好的`OtlpClient`实例
///
/// # Errors
///
/// 如果endpoint URL格式不正确，返回`ConfigError`
///
/// # Examples
///
/// ```
/// use otlp::client::OtlpClient;
///
/// let client = OtlpClient::new("http://localhost:4317")?;
/// ```
pub fn new(endpoint: &str) -> Result<OtlpClient, ConfigError> {
    // ...
}
```

#### 2. 复杂算法需要解释

```rust
/// 使用指数退避策略计算下次重试延迟
///
/// 算法: delay = base_delay * (factor ^ attempt) + jitter
///
/// 其中:
/// - base_delay: 基础延迟时间
/// - factor: 退避因子（通常为2）
/// - attempt: 当前重试次数
/// - jitter: 随机抖动，避免同时重试
fn calculate_backoff(attempt: u32) -> Duration {
    // ...
}
```

### Markdown文档

#### 文档结构

```markdown
# 标题

**简介**: 一句话说明这个文档的内容

**最后更新**: 2025-10-29

---

## 目录

- [章节1](#章节1)
- [章节2](#章节2)

---

## 章节1

内容...

### 子章节

内容...

## 示例代码

\`\`\`rust
// 示例
\`\`\`

## 参考链接

- [相关文档](link)
```

### 更新文档

修改代码时，同时更新：
- API文档 (`///` 注释)
- README (如果影响用法)
- CHANGELOG (如果是用户可见的变更)
- 相关的markdown文档

---

## 🔍 代码审查

### 审查清单

#### 对于提交者

提交PR前自查:

- [ ] 代码遵循项目规范
- [ ] 所有测试通过
- [ ] 添加了必要的测试
- [ ] 更新了文档
- [ ] 运行了 `cargo fmt --all`
- [ ] 运行了 `cargo clippy`
- [ ] 填写了完整的PR描述

#### 对于审查者

审查PR时检查:

- [ ] 代码逻辑正确
- [ ] 测试覆盖充分
- [ ] 错误处理适当
- [ ] 性能影响可接受
- [ ] 文档清晰完整
- [ ] 符合项目改进方向

### 审查流程

1. **自动检查** - CI自动运行测试和检查
2. **代码审查** - 至少1个maintainer审查
3. **修改反馈** - 根据反馈修改代码
4. **批准合并** - 通过后合并到main

### 审查时间

- 🔴 P0任务: 24小时内
- 🟡 P1任务: 48小时内
- 🟢 P2任务: 1周内

---

## 🎯 特殊贡献类型

### 1. Bug修复

1. 创建Bug Issue (如果还没有)
2. 在Issue中描述复现步骤
3. 创建fix分支
4. 修复bug并添加回归测试
5. 提交PR并关联Issue

### 2. 新功能

1. 先在Discussions讨论设计
2. 创建Feature Issue
3. 等待maintainer批准
4. 实现功能
5. 提交PR

### 3. 性能优化

1. 提供性能基准数据
2. 说明优化思路
3. 实现优化
4. 提供优化后的性能数据
5. 提交PR

### 4. 文档改进

1. 识别文档问题
2. 创建docs分支
3. 改进文档
4. 提交PR

---

## 📞 获取帮助

### 遇到问题？

1. 查看 [完整评估报告](analysis/CRITICAL_EVALUATION_REPORT_2025_10_29.md)
2. 运行 `./scripts/check_project_health.sh`
3. 搜索已有的Issues
4. 在Discussions提问

### 联系方式

- 💬 GitHub Discussions - 设计和想法
- 🐛 GitHub Issues - Bug和功能请求
- 📧 邮件 - (待填写)

---

## 🏆 贡献者荣誉

感谢所有为项目改进做出贡献的开发者！

<!-- 贡献者列表将自动更新 -->

---

## 📄 许可证

本项目采用 MIT OR Apache-2.0 双许可证。

贡献代码即表示你同意将你的贡献以相同许可证发布。

---

*感谢你的贡献！让我们一起让OTLP_rust变得更好！🚀*

