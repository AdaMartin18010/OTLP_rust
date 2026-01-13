# 🤝 OTLP Rust 贡献指南

**版本**: 1.0
**最后更新**: 2025年10月26日
**状态**: 🟢 活跃维护

> **简介**: 贡献指南 - 如何向 OTLP Rust 项目贡献代码、文档和测试的完整指南。

---

## 📋 贡献类型

### 🐛 Bug修复

- 修复已知问题
- 改进错误处理
- 提升稳定性

### ✨ 新功能

- 添加新特性
- 扩展API
- 增强功能

### 📚 文档改进

- 完善文档
- 添加示例
- 改进说明

### 🧪 测试

- 增加测试覆盖
- 添加集成测试
- 性能测试

### ⚡ 性能优化

- 算法优化
- 内存优化
- 并发优化

---

## 🚀 开发流程

### 1. 环境准备

```bash
# 安装Rust 1.92+
rustup install 1.90.0
rustup default 1.90.0

# 克隆项目
git clone https://github.com/your-repo/otlp-rust.git
cd otlp-rust

# 安装依赖
cargo build
```

### 2. 创建分支

```bash
# 创建特性分支
git checkout -b feature/your-feature-name

# 或修复分支
git checkout -b fix/your-bug-fix
```

### 3. 开发规范

#### 代码风格

```bash
# 格式化代码
cargo fmt

# 检查代码质量
cargo clippy --all-targets --all-features -- -D warnings
```

#### 测试要求

```bash
# 运行所有测试
cargo test --all-features

# 运行基准测试
cargo bench

# 检查测试覆盖率
cargo tarpaulin --out Html
```

#### 提交规范

```bash
# 提交信息格式
git commit -m "type(scope): description"

# 示例
git commit -m "feat(client): add batch processing support"
git commit -m "fix(network): resolve connection timeout issue"
git commit -m "docs(api): update client documentation"
```

### 4. 提交PR

1. **推送分支**

   ```bash
   git push origin feature/your-feature-name
   ```

2. **创建Pull Request**
   - 填写PR标题和描述
   - 关联相关Issue
   - 添加测试结果

3. **代码审查**
   - 等待维护者审查
   - 根据反馈修改
   - 确保CI通过

---

## 📝 代码规范

### Rust代码风格

```rust
// 使用snake_case命名
fn process_telemetry_data() -> Result<(), Error> {
    // 使用有意义的变量名
    let telemetry_items = vec![];

    // 使用Result进行错误处理
    let result = process_items(telemetry_items)?;

    Ok(result)
}

// 使用文档注释
/// 处理遥测数据
///
/// # Arguments
///
/// * `data` - 遥测数据向量
///
/// # Returns
///
/// 处理结果或错误
pub async fn process_telemetry_data(
    data: Vec<TelemetryData>
) -> Result<ProcessResult, ProcessError> {
    // 实现
}
```

### 错误处理

```rust
// 使用Result而不是unwrap()
let config = load_config()
    .context("Failed to load configuration")?;

// 使用anyhow进行错误链
use anyhow::{Context, Result};

fn process_data() -> Result<()> {
    let data = read_file("data.json")
        .context("Failed to read data file")?;

    let parsed = serde_json::from_str(&data)
        .context("Failed to parse JSON data")?;

    Ok(parsed)
}
```

### 测试规范

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_functionality() {
        // 准备测试数据
        let test_data = create_test_data();

        // 执行测试
        let result = process_data(test_data).await;

        // 验证结果
        assert!(result.is_ok());
        assert_eq!(result.unwrap().count, 10);
    }

    #[test]
    fn test_edge_cases() {
        // 测试边界情况
        let empty_data = vec![];
        let result = process_data(empty_data);
        assert!(result.is_err());
    }
}
```

---

## 🧪 测试指南

### 测试类型

1. **单元测试**

   ```bash
   cargo test --lib
   ```

2. **集成测试**

   ```bash
   cargo test --test integration
   ```

3. **基准测试**

   ```bash
   cargo bench
   ```

4. **性能测试**

   ```bash
   cargo bench --bench simple_benchmarks
   ```

### 测试覆盖率

```bash
# 安装tarpaulin
cargo install cargo-tarpaulin

# 生成覆盖率报告
cargo tarpaulin --out Html --output-dir coverage/

# 查看覆盖率
open coverage/tarpaulin-report.html
```

**目标覆盖率**: 80%+

---

## 📚 文档规范

### 代码文档

```rust
/// 处理遥测数据的核心函数
///
/// 这个函数负责将输入的遥测数据转换为OTLP格式，
/// 并进行必要的验证和处理。
///
/// # 参数
///
/// * `data` - 输入的遥测数据
/// * `config` - 处理配置
///
/// # 返回值
///
/// 返回处理后的数据或错误信息
///
/// # 示例
///
/// ```rust
/// use otlp::{process_telemetry_data, TelemetryData};
///
/// let data = vec![TelemetryData::trace("test")];
/// let result = process_telemetry_data(data).await?;
/// ```
pub async fn process_telemetry_data(
    data: Vec<TelemetryData>,
    config: ProcessConfig,
) -> Result<ProcessResult, ProcessError> {
    // 实现
}
```

### README更新

- 更新功能列表
- 添加使用示例
- 更新性能数据
- 维护版本信息

---

## 🔍 代码审查

### 审查清单

- [ ] 代码风格符合规范
- [ ] 测试覆盖率达标
- [ ] 文档完整准确
- [ ] 性能无回归
- [ ] 安全性检查通过

### 审查流程

1. **自动检查**
   - CI/CD流水线
   - 代码格式检查
   - 静态分析

2. **人工审查**
   - 代码逻辑检查
   - 架构设计审查
   - 性能影响评估

3. **测试验证**
   - 单元测试通过
   - 集成测试通过
   - 性能测试通过

---

## 🎯 贡献奖励

### 贡献者认可

- 添加到贡献者列表
- 特殊贡献者徽章
- 项目维护者邀请

### 贡献类型奖励

- **Bug修复**: 问题解决者徽章
- **新功能**: 功能贡献者徽章
- **文档**: 文档贡献者徽章
- **测试**: 质量保证徽章
- **性能**: 性能优化徽章

---

## 📞 获取帮助

### 联系方式

- **GitHub Issues**: 报告问题和功能请求
- **GitHub Discussions**: 技术讨论和建议
- **邮件**: 联系项目维护者
- **社区**: 参与社区活动

### 常见问题

1. **如何开始贡献？**
   - 查看Good First Issues
   - 阅读开发文档
   - 加入社区讨论

2. **代码审查需要多长时间？**
   - 通常1-3个工作日
   - 复杂功能可能需要更长时间
   - 节假日可能延迟

3. **如何成为维护者？**
   - 持续贡献高质量代码
   - 积极参与社区讨论
   - 帮助其他贡献者

---

## 📄 许可证

贡献的代码将采用与项目相同的许可证：

- MIT License
- Apache-2.0 License

---

**感谢您的贡献！** 🙏

**最后更新**: 2025年1月
**维护者**: OTLP Rust Team
