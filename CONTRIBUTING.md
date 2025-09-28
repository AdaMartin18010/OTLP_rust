# 贡献指南

感谢您对OTLP Rust项目的关注和贡献！本指南将帮助您了解如何参与项目开发、提交代码、报告问题以及参与社区讨论。

## 🤝 如何贡献

### 贡献方式

#### 1. 代码贡献
- **Bug修复**: 修复项目中的bug
- **功能开发**: 实现新功能或改进现有功能
- **性能优化**: 优化代码性能和内存使用
- **测试完善**: 添加或改进测试用例

#### 2. 文档贡献
- **文档编写**: 编写或改进项目文档
- **示例代码**: 提供使用示例和教程
- **翻译工作**: 翻译文档到其他语言
- **文档审查**: 审查和改进现有文档

#### 3. 社区贡献
- **问题报告**: 报告bug或提出改进建议
- **讨论参与**: 参与技术讨论和设计决策
- **用户支持**: 帮助其他用户解决问题
- **社区建设**: 参与社区活动和推广

## 🚀 快速开始

### 1. Fork和克隆项目

```bash
# Fork项目到你的GitHub账户
# 克隆你的fork
git clone https://github.com/your-username/otlp-rust.git
cd otlp-rust

# 添加上游仓库
git remote add upstream https://github.com/otlp-rust/otlp-rust.git

# 获取最新代码
git fetch upstream
git checkout main
git merge upstream/main
```

### 2. 设置开发环境

```bash
# 安装Rust工具链
rustup install stable
rustup component add clippy rustfmt

# 安装开发工具
cargo install cargo-audit cargo-tarpaulin cargo-nextest

# 验证安装
cargo --version
rustc --version
```

### 3. 运行测试

```bash
# 运行所有测试
cargo test --all

# 运行特定测试
cargo test --package otlp

# 运行基准测试
cargo bench

# 运行代码检查
cargo clippy --all
cargo fmt --all
```

## 🔧 开发工作流

### 1. 创建功能分支

```bash
# 创建新分支
git checkout -b feature/your-feature-name

# 或者创建bug修复分支
git checkout -b fix/issue-number
```

### 2. 开发代码

```bash
# 编写代码
# 运行测试确保代码正确
cargo test

# 运行代码检查
cargo clippy
cargo fmt

# 运行安全检查
cargo audit
```

### 3. 提交代码

```bash
# 添加更改
git add .

# 提交更改
git commit -m "feat: 添加新功能描述"

# 推送到你的fork
git push origin feature/your-feature-name
```

### 4. 创建Pull Request

- 在GitHub上创建Pull Request
- 填写详细的描述和说明
- 等待代码审查和反馈
- 根据反馈进行修改

## 📝 代码规范

### 1. Rust代码规范

#### 代码格式化
```bash
# 使用cargo fmt格式化代码
cargo fmt

# 检查代码格式
cargo fmt --check
```

#### 代码检查
```bash
# 使用cargo clippy检查代码
cargo clippy --all

# 允许特定警告
#[allow(clippy::unnecessary_unwrap)]
```

#### 安全检查
```bash
# 使用cargo audit进行安全检查
cargo audit

# 更新依赖
cargo update
```

### 2. 提交信息规范

使用以下格式编写提交信息：

```
<type>: <description>

[optional body]

[optional footer]
```

#### 类型说明
- `feat`: 新功能
- `fix`: 修复bug
- `docs`: 文档更新
- `style`: 代码格式调整
- `refactor`: 代码重构
- `test`: 测试相关
- `chore`: 构建过程或辅助工具的变动

#### 示例
```
feat: 添加零拷贝数据处理功能

- 实现ZeroCopyProcessor
- 添加性能基准测试
- 更新相关文档

Closes #123
```

### 3. 代码注释规范

```rust
/// 计算两个数的和
/// 
/// # 参数
/// 
/// * `a` - 第一个数
/// * `b` - 第二个数
/// 
/// # 返回值
/// 
/// 返回两个数的和
/// 
/// # 示例
/// 
/// ```rust
/// let result = add(2, 3);
/// assert_eq!(result, 5);
/// ```
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

## 🧪 测试规范

### 1. 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_functionality() {
        let result = add(2, 3);
        assert_eq!(result, 5);
    }

    #[tokio::test]
    async fn test_async_functionality() {
        let result = async_add(2, 3).await;
        assert_eq!(result, 5);
    }
}
```

### 2. 集成测试

```rust
// tests/integration_tests.rs
use otlp::{OtlpClient, TelemetryData};

#[tokio::test]
async fn test_end_to_end_flow() {
    let client = OtlpClient::new()
        .with_endpoint("http://localhost:4317")
        .build()
        .unwrap();
    
    let data = TelemetryData {
        // 测试数据
    };
    
    let result = client.send_telemetry_data(data).await;
    assert!(result.is_ok());
}
```

### 3. 性能测试

```rust
// benches/performance_benchmarks.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use otlp::OtlpClient;

fn benchmark_client_creation(c: &mut Criterion) {
    c.bench_function("client_creation", |b| {
        b.iter(|| {
            let client = OtlpClient::new()
                .with_endpoint("http://localhost:4317")
                .build()
                .unwrap();
            black_box(client);
        })
    });
}

criterion_group!(benches, benchmark_client_creation);
criterion_main!(benches);
```

## 📚 文档规范

### 1. 代码文档

```rust
/// 高性能数据处理器
/// 
/// 这个结构体提供了高性能的数据处理功能，包括：
/// - 零拷贝数据处理
/// - 无锁并发处理
/// - 智能缓存管理
/// 
/// # 示例
/// 
/// ```rust
/// use otlp::HighPerformanceProcessor;
/// 
/// let processor = HighPerformanceProcessor::new();
/// let result = processor.process(&data).await?;
/// ```
pub struct HighPerformanceProcessor {
    // 实现细节
}
```

### 2. 用户文档

```markdown
## 功能使用指南

### 基本使用

```rust
use otlp::OtlpClient;

let client = OtlpClient::new()
    .with_endpoint("http://localhost:4317")
    .build()?;
```

### 配置选项

| 选项 | 类型 | 默认值 | 描述 |
|------|------|--------|------|
| endpoint | String | - | OTLP端点地址 |
| timeout | Duration | 30s | 请求超时时间 |
```

### 3. API文档

```rust
/// 发送遥测数据
/// 
/// # 参数
/// 
/// * `data` - 要发送的遥测数据
/// 
/// # 返回值
/// 
/// 返回发送结果，成功时返回`Ok(())`，失败时返回错误。
/// 
/// # 错误
/// 
/// 可能返回以下错误：
/// - `NetworkError` - 网络错误
/// - `SerializationError` - 序列化错误
/// - `TimeoutError` - 超时错误
/// 
/// # 示例
/// 
/// ```rust
/// let result = client.send_telemetry_data(data).await?;
/// ```
pub async fn send_telemetry_data(&self, data: TelemetryData) -> Result<()> {
    // 实现
}
```

## 🐛 问题报告

### 1. Bug报告

在报告bug时，请包含以下信息：

- **问题描述**: 详细描述遇到的问题
- **重现步骤**: 提供重现问题的步骤
- **预期行为**: 描述预期的行为
- **实际行为**: 描述实际发生的行为
- **环境信息**: 操作系统、Rust版本、依赖版本等
- **代码示例**: 提供相关的代码示例

### 2. 功能请求

在提出功能请求时，请包含以下信息：

- **功能描述**: 详细描述请求的功能
- **使用场景**: 说明功能的使用场景
- **实现建议**: 如果有的话，提供实现建议
- **相关链接**: 相关的文档或讨论链接

### 3. 问题模板

```markdown
## 问题描述
[详细描述遇到的问题]

## 重现步骤
1. 步骤1
2. 步骤2
3. 步骤3

## 预期行为
[描述预期的行为]

## 实际行为
[描述实际发生的行为]

## 环境信息
- 操作系统: [例如: Ubuntu 20.04]
- Rust版本: [例如: 1.90.0]
- 项目版本: [例如: 1.0.0]

## 代码示例
```rust
// 相关的代码示例
```

## 附加信息
[任何其他相关信息]
```

## 🔍 代码审查

### 1. 审查流程

1. **自动检查**: 代码提交后自动运行测试和检查
2. **人工审查**: 维护者进行代码审查
3. **反馈修改**: 根据反馈进行修改
4. **合并代码**: 审查通过后合并代码

### 2. 审查标准

- **代码质量**: 代码是否清晰、可读、可维护
- **功能正确性**: 功能是否按预期工作
- **测试覆盖**: 是否有足够的测试覆盖
- **文档更新**: 是否更新了相关文档
- **性能影响**: 是否对性能有负面影响

### 3. 审查反馈

- **建设性反馈**: 提供建设性的改进建议
- **具体建议**: 提供具体的修改建议
- **学习机会**: 将审查作为学习机会
- **尊重他人**: 保持尊重和礼貌的态度

## 🎯 贡献奖励

### 1. 贡献者认可

- **贡献者列表**: 在项目README中列出贡献者
- **贡献统计**: 显示贡献统计信息
- **特殊贡献**: 对特殊贡献者给予特别认可

### 2. 社区参与

- **技术分享**: 邀请贡献者进行技术分享
- **社区活动**: 参与社区活动和聚会
- **导师计划**: 为新手提供导师支持

### 3. 职业发展

- **技能提升**: 通过贡献提升技术技能
- **网络建设**: 建立专业网络
- **职业机会**: 获得职业发展机会

## 📞 获取帮助

### 1. 技术支持

- **GitHub Issues**: 在GitHub上报告问题
- **Discord频道**: 加入Discord频道获取实时帮助
- **邮件支持**: 发送邮件获取支持
- **文档支持**: 查看项目文档

### 2. 社区支持

- **社区指南**: 查看社区指南了解社区规范
- **行为准则**: 了解社区行为准则
- **治理结构**: 了解社区治理结构
- **决策流程**: 了解社区决策流程

### 3. 学习资源

- **官方文档**: 查看官方文档
- **教程资源**: 查看教程和示例
- **技术博客**: 阅读技术博客
- **视频教程**: 观看视频教程

## 🎉 感谢

感谢所有为OTLP Rust项目做出贡献的社区成员！您的贡献让项目变得更好。

### 贡献者类型

- **代码贡献者**: 编写代码和修复bug
- **文档贡献者**: 编写和改进文档
- **测试贡献者**: 编写测试和验证功能
- **社区贡献者**: 参与社区讨论和推广

### 特别感谢

- 项目创始人和核心维护者
- 主要功能开发者和维护者
- 文档编写者和社区管理者
- 所有参与项目的社区成员

---

**版本**: 1.0.0  
**最后更新**: 2025年9月18日  
**维护者**: OTLP Rust Team

让我们一起构建更好的OTLP Rust项目！🚀