# 🔧 API 参考文档

欢迎来到 OTLP Rust 的 API 参考文档中心。这里提供了完整的 API 文档和使用指南。

**最后更新**: 2025年10月24日

---

## 📚 API 文档

### 核心 API

#### [OTLP API 参考](otlp.md)

完整的 OTLP 客户端 API 文档，包括：

- **核心类型**
  - `EnhancedOtlpClient` - 主客户端
  - `Tracer` - 追踪器
  - `Meter` - 指标收集器
  - `Logger` - 日志记录器

- **配置类型**
  - `ClientBuilder` - 客户端构建器
  - `RetryConfig` - 重试配置
  - `BatchConfig` - 批处理配置
  - `TransportConfig` - 传输配置

- **数据类型**
  - `SpanData` - Span 数据
  - `MetricData` - 指标数据
  - `LogData` - 日志数据
  - `AttributeValue` - 属性值

- **导出器**
  - `Exporter` - 导出器 trait
  - `GrpcExporter` - gRPC 导出器
  - `HttpExporter` - HTTP 导出器

---

#### [Reliability API 参考](reliability.md)

可靠性框架的完整 API 文档，包括：

- **错误处理**
  - `UnifiedError` - 统一错误类型
  - `ErrorContext` - 错误上下文
  - `ErrorCategory` - 错误分类

- **容错机制**
  - `CircuitBreaker` - 断路器
  - `RetryPolicy` - 重试策略
  - `Timeout` - 超时控制
  - `Bulkhead` - 隔板模式

- **监控组件**
  - `HealthChecker` - 健康检查
  - `PerformanceMonitor` - 性能监控
  - `ResourceMonitor` - 资源监控

- **自动恢复**
  - `RecoveryManager` - 恢复管理器
  - `ConnectionPool` - 连接池
  - `MemoryManager` - 内存管理

---

## 🎯 快速导航

### 按使用场景查找

#### 我想创建客户端

→ [EnhancedOtlpClient](otlp.md#enhancedotlpclient) + [ClientBuilder](otlp.md#clientbuilder)

#### 我想记录追踪

→ [Tracer](otlp.md#tracer) + [SpanData](otlp.md#spandata)

#### 我想收集指标

→ [Meter](otlp.md#meter) + [MetricData](otlp.md#metricdata)

#### 我想导出日志

→ [Logger](otlp.md#logger) + [LogData](otlp.md#logdata)

#### 我想处理错误

→ [UnifiedError](reliability.md#unifiederror) + [ErrorContext](reliability.md#errorcontext)

#### 我想实现容错

→ [CircuitBreaker](reliability.md#circuitbreaker) + [RetryPolicy](reliability.md#retrypolicy)

#### 我想监控健康

→ [HealthChecker](reliability.md#healthchecker) + [PerformanceMonitor](reliability.md#performancemonitor)

---

## 📊 API 覆盖度

### OTLP API

| 模块 | 公开 API | 文档覆盖 | 示例代码 |
|------|---------|---------|---------|
| 客户端 | 15+ | ✅ 100% | ✅ 8个 |
| 追踪 | 20+ | ✅ 100% | ✅ 12个 |
| 指标 | 18+ | ✅ 100% | ✅ 10个 |
| 日志 | 12+ | ✅ 100% | ✅ 6个 |
| 配置 | 25+ | ✅ 100% | ✅ 15个 |
| 导出 | 10+ | ✅ 100% | ✅ 5个 |

### Reliability API

| 模块 | 公开 API | 文档覆盖 | 示例代码 |
|------|---------|---------|---------|
| 错误处理 | 12+ | ✅ 100% | ✅ 8个 |
| 容错机制 | 16+ | ✅ 100% | ✅ 13个 |
| 监控 | 14+ | ✅ 100% | ✅ 10个 |
| 自动恢复 | 10+ | ✅ 100% | ✅ 7个 |

---

## 🎓 学习路径

### 快速入门（30分钟）

```text
1. 阅读 EnhancedOtlpClient 文档
   ↓
2. 查看基础示例代码
   ↓
3. 创建第一个客户端
   ↓
4. 运行简单示例
```

### 深入学习（2-3小时）

```text
1. 完成快速入门
   ↓
2. 学习 Tracer/Meter/Logger
   ↓
3. 理解配置选项
   ↓
4. 掌握错误处理
   ↓
5. 实践容错机制
```

### 精通掌握（1-2天）

```text
1. 完成深入学习
   ↓
2. 研究所有 API
   ↓
3. 阅读源码实现
   ↓
4. 构建复杂应用
   ↓
5. 优化性能
```

---

## 💡 使用建议

### 如何阅读 API 文档

1. **先看概览** - 了解模块整体结构
2. **查看示例** - 看实际使用方法
3. **理解参数** - 掌握每个参数含义
4. **注意事项** - 关注使用注意事项
5. **相关 API** - 查看相关联的 API

### 最佳实践

- ✅ **使用类型系统** - 利用 Rust 的类型安全
- ✅ **处理错误** - 不要忽略错误
- ✅ **查看文档** - 不确定时查文档
- ✅ **运行示例** - 先运行再修改
- ✅ **阅读源码** - 源码是最好的文档

---

## 🔗 相关资源

### 项目文档

- [快速开始](../guides/quick-start.md) - 快速上手
- [OTLP 客户端指南](../guides/otlp-client.md) - 详细使用指南
- [可靠性框架指南](../guides/reliability-framework.md) - 可靠性使用
- [基础示例](../examples/basic-examples.md) - 入门示例
- [高级示例](../examples/advanced-examples.md) - 高级示例

### 在线文档

- [docs.rs/otlp](https://docs.rs/otlp) - 在线 API 文档
- [docs.rs/reliability](https://docs.rs/reliability) - 可靠性文档

### 源代码

- [crates/otlp/src](../../crates/otlp/src) - OTLP 源码
- [crates/reliability/src](../../crates/reliability/src) - Reliability 源码

---

## 📖 API 设计原则

### 核心原则

1. **类型安全** - 利用 Rust 类型系统防止错误
2. **零成本抽象** - 高层抽象不牺牲性能
3. **可组合性** - API 易于组合使用
4. **明确性** - API 语义清晰明确
5. **向后兼容** - 遵循语义化版本

### 命名约定

- **Builder 模式** - `with_*` 方法用于配置
- **创建方法** - `new()` 用于简单创建
- **构建方法** - `build()` 用于复杂构建
- **异步方法** - `async fn` 用于异步操作
- **错误处理** - 返回 `Result<T, E>`

### 生命周期

- **'static** - 全局资源
- **'a** - 引用生命周期
- **无生命周期** - 拥有所有权

---

## 🔍 查找技巧

### 按功能查找

使用 Ctrl+F (或 Cmd+F) 搜索关键词：

- 搜索 "Client" 查找客户端相关
- 搜索 "Tracer" 查找追踪相关
- 搜索 "Meter" 查找指标相关
- 搜索 "Error" 查找错误处理
- 搜索 "Config" 查找配置选项

### 按类型查找

- **struct** - 数据结构
- **enum** - 枚举类型
- **trait** - trait 定义
- **fn** - 函数
- **impl** - 实现

---

## 🤝 贡献 API 文档

想要改进 API 文档？

1. 查看 [贡献指南](../guides/CONTRIBUTING.md)
2. 选择需要改进的 API
3. 编写清晰的文档和示例
4. 提交 Pull Request

**我们欢迎**:

- 更清晰的描述
- 更多的示例代码
- 常见错误说明
- 性能提示

---

## 💬 反馈

### API 使用问题？

1. 查看 [故障排除](../guides/troubleshooting.md)
2. 搜索 [GitHub Issues](https://github.com/your-org/OTLP_rust/issues)
3. 提出新的 Issue

### API 设计建议？

我们欢迎 API 设计的建议和反馈：

- 📝 API 易用性改进
- 🐛 API 缺陷报告
- ✨ 新 API 需求
- 📚 文档改进

---

*祝你使用愉快！* 🔧
