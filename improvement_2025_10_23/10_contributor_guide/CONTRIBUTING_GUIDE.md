# 🤝 贡献者指南

**欢迎贡献！**  
**创建日期**: 2025年10月23日

---

## 🎯 如何贡献

我们欢迎各种形式的贡献：

- 🐛 报告Bug
- ✨ 提出新功能
- 📝 改进文档
- 🔧 提交代码修复
- 🧪 添加测试
- 📊 性能优化

---

## 🚀 快速开始

### 1. Fork和Clone

```bash
# Fork项目到您的GitHub账户
# 然后克隆

git clone https://github.com/YOUR_USERNAME/otlp-rust.git
cd otlp-rust
```

### 2. 设置开发环境

```bash
# 确保Rust 1.90+
rustc --version

# 安装开发工具
cargo install cargo-watch
cargo install cargo-tarpaulin
cargo install cargo-clippy

# 运行测试确保一切正常
cargo test --workspace
```

### 3. 创建分支

```bash
# 从main创建新分支
git checkout -b feature/your-feature-name

# 或者修复bug
git checkout -b fix/issue-123
```

---

## 📝 代码规范

### Rust代码风格

**使用rustfmt**:

```bash
# 格式化所有代码
cargo fmt --all

# 检查格式
cargo fmt --all -- --check
```

**配置**（`rustfmt.toml`）:

```toml
edition = "2024"
max_width = 100
tab_spaces = 4
newline_style = "Unix"
use_small_heuristics = "Default"
```

### Clippy Lints

**运行Clippy**:

```bash
# 检查所有警告
cargo clippy --all-targets --all-features -- -D warnings
```

**禁止的模式**:

```rust
// ❌ 不要使用unwrap()在库代码中
let value = option.unwrap();

// ✅ 正确的错误处理
let value = option.ok_or(Error::MissingValue)?;

// ❌ 不要使用panic!
panic!("Something went wrong");

// ✅ 返回Result
return Err(Error::OperationFailed);
```

---

## 🧪 测试要求

### 最低要求

**每个新功能必须包含**:

1. 单元测试
2. 文档测试（doctest）
3. 如果是公共API，需要集成测试

### 测试示例

```rust
/// 创建新的OTLP客户端
///
/// # Examples
///
/// ```
/// use otlp_rust::Client;
///
/// let client = Client::new("http://localhost:4317");
/// assert!(client.is_connected());
/// ```
pub fn new(endpoint: &str) -> Self {
    // 实现
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_new_client() {
        let client = Client::new("http://localhost:4317");
        assert_eq!(client.endpoint(), "http://localhost:4317");
    }
    
    #[tokio::test]
    async fn test_client_connection() {
        let client = Client::new("http://localhost:4317");
        assert!(client.connect().await.is_ok());
    }
}
```

### 运行测试

```bash
# 所有测试
cargo test --workspace

# 特定模块
cargo test client::tests

# 集成测试
cargo test --test integration_test

# 文档测试
cargo test --doc

# 带覆盖率
cargo tarpaulin --out Html
```

---

## 📚 文档要求

### API文档

**所有公共项必须有文档**:

```rust
/// 表示OTLP客户端配置
///
/// # Examples
///
/// ```
/// use otlp_rust::ClientConfig;
///
/// let config = ClientConfig::builder()
///     .endpoint("http://localhost:4317")
///     .timeout(Duration::from_secs(30))
///     .build();
/// ```
pub struct ClientConfig {
    /// 服务端点URL
    pub endpoint: String,
    /// 连接超时时间
    pub timeout: Duration,
}

impl ClientConfig {
    /// 创建配置构建器
    ///
    /// # Returns
    ///
    /// 返回新的`ClientConfigBuilder`实例
    ///
    /// # Examples
    ///
    /// ```
    /// use otlp_rust::ClientConfig;
    ///
    /// let builder = ClientConfig::builder();
    /// ```
    pub fn builder() -> ClientConfigBuilder {
        // 实现
    }
}
```

### 文档检查

```bash
# 生成文档
cargo doc --no-deps --all-features

# 检查文档链接
cargo install cargo-deadlinks
cargo deadlinks

# 在浏览器中查看
cargo doc --no-deps --open
```

---

## 🔄 提交规范

### Commit Message格式

遵循[Conventional Commits](https://www.conventionalcommits.org/):

```text
<type>(<scope>): <subject>

<body>

<footer>
```

**类型（type）**:

- `feat`: 新功能
- `fix`: Bug修复
- `docs`: 文档更新
- `style`: 代码格式（不影响功能）
- `refactor`: 重构
- `perf`: 性能优化
- `test`: 添加测试
- `chore`: 构建/工具更改

**示例**:

```text
feat(client): add retry mechanism for failed requests

Implement exponential backoff retry logic for network failures.
This improves reliability when the backend is temporarily unavailable.

Closes #123
```

```text
fix(transport): handle connection timeout correctly

Previously, timeouts were not properly handled, causing the client
to hang indefinitely.

Fixes #456
```

---

## 📤 提交Pull Request

### PR检查清单

提交前确保：

- [ ] 代码已格式化（`cargo fmt`）
- [ ] Clippy检查通过
- [ ] 所有测试通过
- [ ] 添加了必要的测试
- [ ] 更新了文档
- [ ] 更新了CHANGELOG.md
- [ ] Commit message符合规范

### PR模板

创建PR时，请填写以下信息：

```markdown
## 描述
简要描述这个PR做了什么。

## 动机和背景
为什么需要这个改动？解决了什么问题？

## 类型
- [ ] Bug修复
- [ ] 新功能
- [ ] 重构
- [ ] 文档更新
- [ ] 性能优化

## 测试
描述你如何测试这些更改。

## 检查清单
- [ ] 代码已格式化
- [ ] Clippy检查通过
- [ ] 测试通过
- [ ] 文档已更新
- [ ] CHANGELOG已更新

## 相关Issue
Closes #xxx
```

---

## 🐛 报告Bug

### Bug报告模板

```markdown
## Bug描述
清晰简洁地描述bug。

## 复现步骤
1. 执行 '...'
2. 调用 '....'
3. 查看错误

## 预期行为
描述你期望发生什么。

## 实际行为
描述实际发生了什么。

## 环境
- OS: [e.g. Ubuntu 22.04]
- Rust版本: [e.g. 1.90]
- 库版本: [e.g. 0.1.0]

## 额外信息
任何其他相关信息。
```

---

## ✨ 提议新功能

### 功能提议模板

```markdown
## 功能描述
清晰简洁地描述你想要的功能。

## 动机
为什么需要这个功能？它解决了什么问题？

## 建议的实现
如果有想法，描述你认为应该如何实现。

## 替代方案
你考虑过哪些替代方案？

## 额外信息
任何其他相关信息、截图等。
```

---

## 🏗️ 架构决策

### 做出更改前

对于重大架构更改：

1. 先创建Issue讨论
2. 等待维护者反馈
3. 如需要，创建RFC文档
4. 获得批准后再实现

### RFC流程

对于重大更改，请创建RFC：

```markdown
# RFC: <标题>

## 摘要
一段话摘要。

## 动机
为什么需要这个更改？

## 详细设计
详细描述设计。包括：
- API设计
- 实现细节
- 示例代码

## 缺点
这个设计有什么缺点？

## 替代方案
考虑过哪些其他设计？

## 未解决的问题
还有哪些问题需要解决？
```

---

## 🎯 代码审查指南

### 作为审查者

**关注点**:

1. 功能正确性
2. 测试覆盖
3. 文档完整性
4. 性能影响
5. API设计
6. 错误处理

**反馈原则**:

- 建设性和友好
- 具体和可操作
- 区分问题和建议

**示例反馈**:

```text
# ❌ 不好的反馈
这个代码很糟糕。

# ✅ 好的反馈
这个函数可以通过使用迭代器链来简化：
建议：`items.iter().filter(|x| x.is_valid()).collect()`
```

### 作为提交者

**响应审查**:

- 及时响应
- 解释你的决策
- 保持开放心态
- 感谢审查者

---

## 🚀 发布流程

### 版本号

遵循语义版本：

- `0.1.x`: Bug修复
- `0.x.0`: 新功能
- `x.0.0`: 破坏性更改

### 发布检查清单

- [ ] 更新CHANGELOG.md
- [ ] 更新版本号
- [ ] 更新文档
- [ ] 运行完整测试套件
- [ ] 创建Git标签
- [ ] 发布到crates.io
- [ ] 发布公告

---

## 🤝 社区准则

### 行为准则

我们致力于提供友好、安全和欢迎的环境。

**期望行为**:

- 尊重不同观点
- 接受建设性批评
- 关注对社区最有利的事情
- 对其他成员表示同理心

**不可接受行为**:

- 骚扰或歧视
- 侮辱或贬损评论
- 公开或私人骚扰
- 未经许可发布他人信息

---

## 📞 获取帮助

### 资源

- **文档**: [docs.rs/otlp-rust](https://docs.rs/otlp-rust)
- **Issues**: [GitHub Issues](https://github.com/username/otlp-rust/issues)
- **讨论**: [GitHub Discussions](https://github.com/username/otlp-rust/discussions)

### 联系方式

- 报告安全问题: <security@example.com>
- 一般问题: GitHub Discussions
- Bug报告: GitHub Issues

---

## 🎉 感谢贡献者

感谢所有为这个项目做出贡献的人！

您的贡献使这个项目变得更好。 ❤️

---

**维护者**: AI Assistant  
**创建日期**: 2025年10月23日  
**版本**: 1.0
