# 贡献指南

欢迎为OTLP Rust项目做出贡献！本指南将帮助您了解如何参与项目开发。

## 📋 目录

## 🤝 行为准则

本项目遵循[贡献者公约](CODE_OF_CONDUCT.md)。请确保您的行为符合该准则。

## 🚀 如何贡献

### 报告问题

如果您发现了bug或有功能请求，请：

1. 检查[现有问题](https://github.com/your-org/otlp-rust/issues)是否已存在
2. 创建新的issue，包含：
   - 清晰的问题描述
   - 复现步骤
   - 预期行为
   - 实际行为
   - 环境信息

### 提交代码

1. Fork项目
2. 创建功能分支：`git checkout -b feature/amazing-feature`
3. 提交更改：`git commit -m 'Add amazing feature'`
4. 推送分支：`git push origin feature/amazing-feature`
5. 创建Pull Request

## 🛠️ 开发环境设置

### 系统要求

- Rust 1.90+
- Cargo
- Git

### 安装步骤

```bash
# 克隆项目
git clone https://github.com/your-org/otlp-rust.git
cd otlp-rust

# 安装依赖
cargo build

# 运行测试
cargo test

# 运行示例
cargo run --example basic_usage
```

### 开发工具

推荐安装以下开发工具：

```bash
# 代码格式化
cargo install rustfmt

# 代码检查
cargo install clippy

# 文档生成
cargo install cargo-doc

# 测试覆盖率
cargo install cargo-tarpaulin

# 安全审计
cargo install cargo-audit
```

## 📝 代码规范

### Rust代码规范

我们遵循Rust官方代码规范：

```bash
# 格式化代码
cargo fmt

# 检查代码质量
cargo clippy --all-targets --all-features -- -D warnings
```

### 文档规范

- 所有公共API必须有文档注释
- 使用`cargo doc`生成文档
- 示例代码必须能够编译运行

### 测试规范

- 单元测试覆盖率目标：90%+
- 所有新功能必须包含测试
- 集成测试覆盖主要使用场景

## 🔄 提交流程

### 分支命名规范

- `feature/功能名称` - 新功能开发
- `bugfix/问题描述` - Bug修复
- `docs/文档更新` - 文档更新
- `refactor/重构描述` - 代码重构
- `test/测试相关` - 测试相关

### 提交信息规范

使用[约定式提交](https://www.conventionalcommits.org/)格式：

```text
<类型>[可选范围]: <描述>

[可选正文]

[可选脚注]
```

类型包括：

- `feat`: 新功能
- `fix`: Bug修复
- `docs`: 文档更新
- `style`: 代码格式调整
- `refactor`: 代码重构
- `test`: 测试相关
- `chore`: 构建过程或辅助工具的变动

示例：

```text
feat(client): add batch processing support

Add support for batch processing of telemetry data to improve
performance when sending large amounts of data.

Closes #123
```

### Pull Request规范

PR必须包含：

1. **清晰的标题和描述**
2. **相关issue链接**
3. **测试覆盖**
4. **文档更新**（如需要）
5. **性能影响说明**（如适用）

PR模板：

```markdown
## 变更描述
简要描述此PR的变更内容

## 变更类型
- [ ] Bug修复
- [ ] 新功能
- [ ] 破坏性变更
- [ ] 文档更新
- [ ] 性能优化

## 测试
- [ ] 单元测试
- [ ] 集成测试
- [ ] 手动测试

## 检查清单
- [ ] 代码遵循项目规范
- [ ] 自测通过
- [ ] 添加了必要的测试
- [ ] 更新了相关文档
- [ ] 所有CI检查通过

## 相关Issue
Closes #123
```

## 🚀 发布流程

### 版本号规范

使用[语义化版本](https://semver.org/)：

- `MAJOR`: 不兼容的API修改
- `MINOR`: 向下兼容的功能性新增
- `PATCH`: 向下兼容的问题修正

### 发布步骤

1. **更新版本号**

   ```bash
   # 更新Cargo.toml中的版本号
   cargo set-version 1.2.3
   ```

2. **更新CHANGELOG**
   - 记录所有变更
   - 按类型分组（新增、修复、变更、移除）

3. **创建发布标签**

   ```bash
   git tag -a v1.2.3 -m "Release version 1.2.3"
   git push origin v1.2.3
   ```

4. **发布到crates.io**

   ```bash
   cargo publish
   ```

## 🏆 贡献者认可

我们感谢所有贡献者！贡献者将被列在：

- [CONTRIBUTORS.md](CONTRIBUTORS.md)
- 项目README
- 发布说明

## 📞 获取帮助

如果您需要帮助，可以通过以下方式联系：

- [GitHub Issues](https://github.com/your-org/otlp-rust/issues)
- [GitHub Discussions](https://github.com/your-org/otlp-rust/discussions)
- [Discord社区](https://discord.gg/your-discord)

## 📚 相关资源

- [Rust官方文档](https://doc.rust-lang.org/)
- [OpenTelemetry规范](https://opentelemetry.io/docs/)
- [项目文档](https://your-org.github.io/otlp-rust/)

---

感谢您的贡献！🎉
