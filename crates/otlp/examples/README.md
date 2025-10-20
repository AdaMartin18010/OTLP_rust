# OTLP Rust Examples

本目录包含 OTLP Rust 的使用示例，从简单到复杂，展示各种使用场景。

## 📚 示例列表

### 基础示例

#### 1. `hello_world.rs` - Hello World

最简单的示例，展示如何创建客户端并导出一个 span。

```bash
cargo run --example hello_world
```

**学习内容**:

- 创建 `EnhancedOtlpClient`
- 获取 `Tracer`
- 创建和结束 `Span`
- 添加属性
- 查看统计信息

---

#### 2. `enhanced_client_demo.rs` - 完整功能演示

展示 `EnhancedOtlpClient` 的完整功能。

```bash
cargo run --example enhanced_client_demo
```

**学习内容**:

- 客户端配置
- 批处理和压缩
- 重试和熔断
- 性能优化
- 可靠性保证

---

### 中级示例

#### 3. `nested_spans.rs` - 嵌套 Spans

展示如何创建嵌套的 spans 来追踪复杂的操作流程。

```bash
cargo run --example nested_spans
```

**学习内容**:

- 创建父子 span 关系
- 多层嵌套结构
- 追踪复杂业务流程
- 在 Jaeger 中可视化追踪树

---

#### 4. `async_tracing.rs` - 异步追踪

展示如何在异步场景中使用 OTLP 进行分布式追踪。

```bash
cargo run --example async_tracing
```

**学习内容**:

- 异步函数中的追踪
- 并发请求追踪
- 超时处理
- 异步任务间的追踪关系

---

### 高级示例

#### 5. `attributes_and_events.rs` - 属性和事件 (待实现)

展示如何使用 span 属性和事件。

```bash
cargo run --example attributes_and_events
```

**学习内容**:

- 添加各种类型的属性
- 记录 span 事件
- 结构化日志
- 最佳实践

---

#### 6. `error_handling.rs` - 错误处理 (待实现)

展示如何在追踪中处理和记录错误。

```bash
cargo run --example error_handling
```

**学习内容**:

- 记录错误信息
- 设置 span 状态
- 错误传播
- 错误分析

---

#### 7. `custom_config.rs` - 自定义配置 (待实现)

展示如何自定义客户端配置。

```bash
cargo run --example custom_config
```

**学习内容**:

- 批处理配置
- 压缩配置
- 重试策略
- 超时设置
- 熔断器配置

---

### 性能示例

#### 8. `batching.rs` - 批处理 (待实现)

展示批处理功能如何提升性能。

```bash
cargo run --example batching
```

**学习内容**:

- 批处理配置
- 性能对比
- 最佳批大小
- 内存管理

---

#### 9. `compression.rs` - 压缩 (待实现)

展示数据压缩如何减少网络传输。

```bash
cargo run --example compression
```

**学习内容**:

- Gzip vs Snappy
- 压缩比对比
- 性能影响
- 何时使用压缩

---

### 集成示例

#### 10. `jaeger_integration.rs` - Jaeger 集成 (待实现)

展示如何将追踪数据发送到 Jaeger。

```bash
cargo run --example jaeger_integration
```

**学习内容**:

- Jaeger 配置
- 查看追踪数据
- 分析性能
- 故障排查

---

## 🚀 快速开始

### 前置条件

#### 基础示例（无需外部服务）

以下示例可以直接运行，无需启动 Docker 或其他服务：

- `hello_world.rs`
- `nested_spans.rs`
- `async_tracing.rs`
- `enhanced_client_demo.rs`

```bash
# 直接运行
cargo run --example hello_world
```

#### 集成示例（需要 Docker）

以下示例需要启动 OpenTelemetry Collector 和 Jaeger：

- `jaeger_integration.rs`
- 任何需要查看追踪数据的示例

```bash
# 1. 启动 Docker 环境
cd tests/integration
docker-compose up -d

# 2. 运行示例
cd ../..
cargo run --example hello_world

# 3. 查看 Jaeger UI
# 浏览器打开: http://localhost:16686
```

---

## 📖 示例结构

每个示例都遵循相同的结构：

```rust
//! 示例标题
//!
//! 示例描述
//!
//! # 运行方式
//!
//! ```bash
//! cargo run --example example_name
//! ```
//!
//! # 前置条件
//!
//! 列出所需的前置条件

use otlp::core::EnhancedOtlpClient;
// ... 其他 imports ...

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 示例代码
    Ok(())
}

/* 预期输出或说明 */
```

---

## 🎯 学习路径

### 初学者

1. `hello_world.rs` - 了解基本概念
2. `nested_spans.rs` - 学习追踪结构
3. `enhanced_client_demo.rs` - 掌握完整功能

### 中级用户

1. `async_tracing.rs` - 异步场景
2. `attributes_and_events.rs` - 丰富追踪数据
3. `error_handling.rs` - 错误处理

### 高级用户

1. `custom_config.rs` - 性能调优
2. `batching.rs` + `compression.rs` - 优化策略
3. `jaeger_integration.rs` - 生产环境集成

---

## 🔧 运行所有示例

```bash
# 运行所有基础示例
cargo run --example hello_world
cargo run --example nested_spans
cargo run --example async_tracing
cargo run --example enhanced_client_demo

# 查看可用示例
cargo run --example --list
```

---

## 📊 性能对比

### 示例性能数据

| 示例 | Spans | 时间 | 内存 | 复杂度 |
|------|-------|------|------|--------|
| hello_world | 1 | <100ms | ~1MB | 简单 |
| nested_spans | 7 | ~500ms | ~2MB | 中等 |
| async_tracing | 15+ | ~1s | ~5MB | 复杂 |
| enhanced_client_demo | 3 | ~300ms | ~3MB | 中等 |

---

## 🐛 故障排查

### 常见问题

#### 1. 无法连接到 localhost:4317

**原因**: OpenTelemetry Collector 未运行

**解决方案**:

```bash
cd tests/integration
docker-compose up -d
```

#### 2. Jaeger UI 无追踪数据

**原因**:

- Collector 配置问题
- 客户端未正确导出

**解决方案**:

```bash
# 检查 Collector 日志
docker-compose logs otel-collector

# 验证健康状态
curl http://localhost:13133/
```

#### 3. 编译错误

**原因**: 依赖版本不匹配

**解决方案**:

```bash
cargo clean
cargo build
```

---

## 📝 贡献新示例

欢迎贡献新的示例！请确保：

1. **清晰的文档**: 说明示例目的和学习内容
2. **完整的注释**: 解释关键代码
3. **错误处理**: 展示正确的错误处理
4. **输出说明**: 包含预期输出示例
5. **README 更新**: 在本文件中添加示例说明

---

## 📚 相关文档

- [核心 API 使用指南](../docs/核心API使用指南.md)
- [集成测试指南](../docs/集成测试指南.md)
- [项目 README](../../README_核心重构_2025_10_18.md)
- [快速开始](../../QUICK_START_快速开始.md)

---

## 🎓 推荐资源

### OpenTelemetry

- [OpenTelemetry 官方文档](https://opentelemetry.io/docs/)
- [OTLP 规范](https://github.com/open-telemetry/opentelemetry-specification/blob/main/specification/protocol/otlp.md)
- [OpenTelemetry Rust](https://github.com/open-telemetry/opentelemetry-rust)

### Jaeger

- [Jaeger 文档](https://www.jaegertracing.io/docs/)
- [Jaeger UI 指南](https://www.jaegertracing.io/docs/latest/frontend-ui/)

### Rust

- [Tokio 异步编程](https://tokio.rs/tokio/tutorial)
- [Rust 异步书](https://rust-lang.github.io/async-book/)

---

**最后更新**: 2025-10-18  
**示例数量**: 4 个已实现, 6 个待实现  
**总示例目标**: 10+ 个

---
