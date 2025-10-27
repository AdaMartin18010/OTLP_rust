# 📝 示例和教程

**版本**: 1.0  
**最后更新**: 2025年10月26日  
**状态**: 🟢 活跃维护

> **简介**: OTLP Rust 示例中心 - 从基础到高级的完整示例代码和教程集合。

---

## 📚 示例文档

### 🎯 基础示例

**[基础示例文档](basic-examples.md)** - 适合初学者

包含 7 个循序渐进的示例：

1. **Hello World** - 最简单的 OTLP 客户端
2. **带配置的客户端** - 自定义配置
3. **完整追踪示例** - 创建和管理 Span
4. **指标收集示例** - 收集和记录指标
5. **日志记录示例** - 结构化日志
6. **错误处理示例** - 优雅的错误处理
7. **完整应用示例** - 综合应用

**预计学习时间**: 2-3小时  
**难度**: ⭐ 入门

---

### 🚀 高级示例

**[高级示例文档](advanced-examples.md)** - 适合进阶用户

包含 7 个高级主题：

1. **微服务架构** - 多服务追踪
2. **分布式追踪** - 跨服务上下文传播
3. **高级指标收集** - 自定义指标和聚合
4. **自定义导出器** - 实现自定义后端
5. **性能优化** - 高性能配置
6. **可靠性框架集成** - 容错和恢复
7. **生产环境配置** - 完整生产配置

**预计学习时间**: 4-6小时  
**难度**: ⭐⭐⭐⭐ 进阶

---

## 💻 可运行代码示例

### OTLP 核心示例

项目包含 **25+ 个可运行的示例程序**，位于：

```
crates/otlp/examples/
├── 01_quick_start.rs              # 快速开始
├── 02_custom_config.rs            # 自定义配置
├── 03_distributed_tracing.rs      # 分布式追踪
├── 04_metrics_collection.rs       # 指标收集
├── 05_log_export.rs               # 日志导出
├── 06_error_handling.rs           # 错误处理
├── 07_performance_tuning.rs       # 性能调优
├── 08_batch_processing.rs         # 批处理
├── 09_compression.rs              # 数据压缩
├── 10_retry_strategy.rs           # 重试策略
└── ... 更多示例
```

**运行示例**:

```bash
# 运行快速开始示例
cargo run -p otlp --example 01_quick_start

# 运行分布式追踪示例
cargo run -p otlp --example 03_distributed_tracing

# 列出所有示例
cargo run -p otlp --example
```

---

### 可靠性框架示例

**13+ 个可靠性框架示例**，位于：

```
crates/reliability/examples/
├── 01_basic_error_handling.rs     # 基础错误处理
├── 02_circuit_breaker.rs          # 断路器
├── 03_retry_pattern.rs            # 重试模式
├── 04_timeout_handling.rs         # 超时处理
├── 05_bulkhead_pattern.rs         # 隔板模式
├── 06_health_checks.rs            # 健康检查
├── 07_fallback_strategy.rs       # 降级策略
├── 08_chaos_testing.rs            # 混沌测试
└── ... 更多示例
```

**运行示例**:

```bash
# 运行断路器示例
cargo run -p reliability --example 02_circuit_breaker

# 运行健康检查示例
cargo run -p reliability --example 06_health_checks
```

---

## 🎓 学习路径

### 初学者路径

```text
1. 阅读基础示例文档
   ↓
2. 运行 Hello World (01_quick_start.rs)
   ↓
3. 逐个运行基础示例 (02-07)
   ↓
4. 完成一个简单项目
```

**预计时间**: 1天

---

### 进阶路径

```text
1. 完成初学者路径
   ↓
2. 阅读高级示例文档
   ↓
3. 运行高级示例 (08-15)
   ↓
4. 研究可靠性框架示例
   ↓
5. 构建微服务应用
```

**预计时间**: 3-5天

---

### 专家路径

```text
1. 完成进阶路径
   ↓
2. 阅读所有示例源码
   ↓
3. 实现自定义导出器
   ↓
4. 性能压力测试
   ↓
5. 贡献新示例
```

**预计时间**: 1-2周

---

## 📊 示例索引

### 按难度分类

| 难度 | 示例数量 | 文档 |
|------|---------|------|
| ⭐ 入门 | 7 | [基础示例](basic-examples.md) |
| ⭐⭐⭐ 中级 | 15 | crates/otlp/examples/ |
| ⭐⭐⭐⭐ 高级 | 7 | [高级示例](advanced-examples.md) |
| ⭐⭐⭐⭐⭐ 专家 | 13 | crates/reliability/examples/ |

---

### 按主题分类

| 主题 | 示例 | 位置 |
|------|------|------|
| **追踪 (Tracing)** | 8个 | 基础示例 + 高级示例 |
| **指标 (Metrics)** | 6个 | 基础示例 + 高级示例 |
| **日志 (Logging)** | 4个 | 基础示例 + OTLP 示例 |
| **性能优化** | 8个 | 高级示例 + OTLP 示例 |
| **可靠性** | 13个 | Reliability 示例 |
| **微服务** | 3个 | 高级示例 |
| **生产部署** | 2个 | 高级示例 |

---

## 💡 使用建议

### 如何学习示例

1. **先读文档** - 了解示例的目的和概念
2. **运行代码** - 看实际效果
3. **修改参数** - 尝试不同配置
4. **阅读源码** - 理解实现细节
5. **编写测试** - 验证理解

### 最佳实践

- ✅ **按顺序学习** - 从简单到复杂
- ✅ **动手实践** - 不要只看不做
- ✅ **做笔记** - 记录关键点
- ✅ **提问题** - 不懂就问
- ✅ **写总结** - 巩固知识

---

## 🔗 相关资源

### 项目文档

- [快速开始](../guides/quick-start.md) - 5分钟快速上手
- [安装指南](../guides/installation.md) - 环境配置
- [OTLP 客户端](../guides/otlp-client.md) - 详细使用指南
- [示例索引](../EXAMPLES_INDEX.md) - 完整示例列表

### API 参考

- [OTLP API](../api/otlp.md) - OTLP API 文档
- [Reliability API](../api/reliability.md) - 可靠性 API 文档

### 外部资源

- [OpenTelemetry 示例](https://opentelemetry.io/docs/instrumentation/)
- [Rust 异步编程](https://rust-lang.github.io/async-book/)
- [Tokio 教程](https://tokio.rs/tokio/tutorial)

---

## 🎯 实践项目建议

### 初级项目（1-2天）

1. **HTTP API 追踪** - 为简单 HTTP 服务添加追踪
2. **数据库监控** - 监控数据库查询性能
3. **定时任务** - 监控定时任务执行

### 中级项目（3-5天）

1. **微服务追踪** - 实现跨服务追踪
2. **自定义指标** - 实现业务指标收集
3. **告警系统** - 实现基于指标的告警

### 高级项目（1-2周）

1. **分布式监控** - 构建完整监控系统
2. **性能分析工具** - 开发性能分析工具
3. **可观测性平台** - 构建企业级可观测性平台

---

## 🤝 贡献示例

想要贡献新的示例？太好了！

1. 查看 [贡献指南](../guides/CONTRIBUTING.md)
2. 选择一个有趣的主题
3. 编写清晰的代码和注释
4. 添加到示例文档中
5. 提交 Pull Request

**我们欢迎**:
- 新的使用场景示例
- 常见问题的解决方案
- 性能优化技巧
- 最佳实践分享

---

## 💬 反馈和问题

### 遇到问题？

1. 查看 [故障排除指南](../guides/troubleshooting.md)
2. 搜索 [GitHub Issues](https://github.com/your-org/OTLP_rust/issues)
3. 提出新的 Issue
4. 在 [Discussions](https://github.com/your-org/OTLP_rust/discussions) 讨论

### 改进建议？

我们随时欢迎对示例的改进建议：

- 📝 更清晰的说明
- 🐛 Bug 修复
- ✨ 新功能示例
- 📚 更好的文档

---

*祝你学习愉快！* 🚀

