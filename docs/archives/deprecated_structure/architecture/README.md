# 🏗️ 架构设计文档

欢迎来到 OTLP Rust 的架构设计文档中心。这里详细介绍了项目的架构设计和实现细节。

> 📢 **文档迁移通知**  
> 为了提供更完整、更系统化的架构文档，我们已将详细内容迁移到 **[04_ARCHITECTURE](../04_ARCHITECTURE/README.md)** 目录。  
> 新目录包含：
>
> - ✅ 更详细的架构说明（653+ 行）
> - ✅ 完整的微服务架构设计
> - ✅ 性能优化、安全架构、部署架构
> - ✅ OTLP 2024-2025 新特性架构支持
>
> 📖 **建议阅读顺序**:
>
> 1. 快速参考：继续阅读本页面
> 2. 深入学习：访问 [04_ARCHITECTURE](../04_ARCHITECTURE/README.md)
> 3. 理论基础：查看 [02_THEORETICAL_FRAMEWORK](../02_THEORETICAL_FRAMEWORK/README.md)

**最后更新**: 2025年10月24日  
**版本**: 2.0 (新增 OTLP 2024-2025 特性支持)

---

## 📚 架构文档

### [系统架构](system-architecture.md)

整体系统架构设计，包括：

- **架构概览** - 系统整体架构
- **核心组件** - 主要组件说明
- **数据流** - 数据流转过程
- **交互模式** - 组件交互方式
- **部署架构** - 部署拓扑结构

**适合读者**: 所有开发者和架构师

---

### [模块设计](module-design.md)

详细的模块设计文档，包括：

- **模块划分** - 模块组织结构
- **职责边界** - 模块职责定义
- **接口设计** - 模块间接口
- **依赖关系** - 模块依赖图
- **扩展点** - 可扩展设计

**适合读者**: 核心贡献者和深度用户

---

## 🎯 架构特点

### 核心设计原则

1. **模块化** - 清晰的模块划分
2. **可扩展** - 易于扩展新功能
3. **高性能** - 优化的执行路径
4. **类型安全** - 利用 Rust 类型系统
5. **异步优先** - 基于 Tokio 的异步设计

### 关键技术决策

- ✅ **Crate 拆分** - 多 crate 组织
- ✅ **异步运行时** - 使用 Tokio
- ✅ **错误处理** - 统一的错误类型
- ✅ **零拷贝** - 最小化内存拷贝
- ✅ **批处理** - 高效的批处理机制

### 🚀 OTLP 2024-2025 新特性支持

- 🆕 **Profile 信号类型** - CPU/内存性能分析（pprof 格式）
- 🆕 **Event 信号类型** - 独立事件模型，超越日志的结构化事件
- 🆕 **增强的 Log 模型** - 结构化日志，支持复杂嵌套数据
- 🆕 **OTLP/Arrow** - 基于 Apache Arrow 的高性能传输协议
- 🆕 **Semantic Conventions v1.25+** - GenAI、云原生、消息系统新属性

---

## 🏛️ 架构层次

```text
┌─────────────────────────────────────────────────┐
│          应用层 (Application)                    │
│  ┌───────────────────────────────────────────┐  │
│  │   OTLP 客户端 API                         │  │
│  │   可靠性框架 API                          │  │
│  └───────────────────────────────────────────┘  │
├─────────────────────────────────────────────────┤
│          信号层 (Signals) - OTLP 2025           │
│  ┌─────────┬─────────┬─────────┬─────────────┐ │
│  │ 追踪    │ 指标    │ 日志    │ Profile🆕  │ │
│  │ Trace   │ Metrics │ Logs    │ (pprof)     │ │
│  ├─────────┴─────────┴─────────┼─────────────┤ │
│  │      数据导出               │  Event🆕   │ │
│  │      Export                 │  (独立事件) │ │
│  └─────────────────────────────┴─────────────┘ │
├─────────────────────────────────────────────────┤
│          传输层 (Transport) - OTLP 2025         │
│  ┌─────────┬───────────┬──────────────────┐    │
│  │ gRPC    │ HTTP/JSON │ OTLP/Arrow🆕    │    │
│  │ 传输    │ 传输      │ (高性能传输)     │    │
│  └─────────┴───────────┴──────────────────┘    │
├─────────────────────────────────────────────────┤
│          基础层 (Foundation)                    │
│  ┌───────────────────────────────────────────┐ │
│  │ 错误处理 │ 配置管理 │ Semantic Conventions│ │
│  │ 批处理   │ 连接池   │ v1.25+🆕          │ │
│  │ 监控     │ 安全     │ (GenAI/云原生)    │ │
│  └───────────────────────────────────────────┘ │
└─────────────────────────────────────────────────┘
```

---

## 📊 Crate 组织

### 主要 Crates

```text
OTLP_rust/
├── crates/
│   ├── otlp/                  # OTLP 核心实现
│   │   ├── src/
│   │   │   ├── client/        # 客户端
│   │   │   ├── signals/       # 信号处理 (2025)
│   │   │   │   ├── trace/     # 追踪信号
│   │   │   │   ├── metrics/   # 指标信号
│   │   │   │   ├── logs/      # 日志信号 (增强)
│   │   │   │   ├── profile/   # Profile 信号 🆕
│   │   │   │   └── event/     # Event 信号 🆕
│   │   │   ├── export/        # 数据导出
│   │   │   ├── transport/     # 传输层
│   │   │   │   ├── grpc/      # gRPC 传输
│   │   │   │   ├── http/      # HTTP 传输
│   │   │   │   └── arrow/     # OTLP/Arrow 🆕
│   │   │   ├── semconv/       # Semantic Conventions v1.25+ 🆕
│   │   │   └── config/        # 配置管理
│   │   └── examples/          # 示例代码
│   │
│   └── reliability/           # 可靠性框架
│       ├── src/
│       │   ├── error/         # 错误处理
│       │   ├── fault/         # 容错机制
│       │   ├── monitor/       # 运行时监控
│       │   └── recovery/      # 自动恢复
│       └── examples/          # 示例代码
```

### Crate 依赖

```text
应用程序
    ↓
  otlp  ←────┐
    ↓        │
reliability  │
    ↓        │
  tokio ─────┘
```

---

## 🔄 数据流

### 追踪数据流

```text
应用代码
    ↓
  Tracer.start()
    ↓
  Span (收集属性和事件)
    ↓
  Span.end()
    ↓
  SpanProcessor (批处理)
    ↓
  Exporter (导出)
    ↓
  传输层 (gRPC/HTTP)
    ↓
  OTLP Collector
```

### 指标数据流

```text
应用代码
    ↓
  Meter.counter/histogram/gauge
    ↓
  MetricData (聚合)
    ↓
  MetricProcessor (批处理)
    ↓
  Exporter (导出)
    ↓
  传输层 (gRPC/HTTP)
    ↓
  OTLP Collector
```

### 🆕 Profile 数据流 (2025)

```text
应用代码
    ↓
  Profiler.start() (CPU/Memory)
    ↓
  ProfileData (pprof 格式)
    ↓
  ProfileProcessor (批处理)
    ↓
  Exporter (导出)
    ↓
  传输层 (gRPC/HTTP/Arrow)
    ↓
  OTLP Collector → Profiling Backend
```

### 🆕 Event 数据流 (2025)

```text
应用代码
    ↓
  EventEmitter.emit() (结构化事件)
    ↓
  EventData (独立于日志)
    ↓
  EventProcessor (批处理)
    ↓
  Exporter (导出)
    ↓
  传输层 (gRPC/HTTP/Arrow)
    ↓
  OTLP Collector → Event Processing
```

---

## 🎓 学习路径

### 快速了解（30分钟）

1. 阅读系统架构概览
2. 查看架构图
3. 理解核心组件

### 深入学习（2-3小时）

1. 详细阅读系统架构
2. 理解模块设计
3. 查看源码结构
4. 运行架构示例

### 精通掌握（1-2天）

1. 研究所有架构文档
2. 阅读核心源码
3. 理解设计决策
4. 参与架构讨论

---

## 🔗 相关资源

### 项目文档

- [快速开始](../guides/quick-start.md) - 快速上手
- [OTLP 客户端](../guides/otlp-client.md) - 客户端使用
- [API 参考](../api/otlp.md) - API 文档
- [示例代码](../examples/basic-examples.md) - 示例教程

### 理论框架

- [理论框架总览](../02_THEORETICAL_FRAMEWORK/README.md)
- [语义模型与流分析](../02_THEORETICAL_FRAMEWORK/SEMANTIC_MODELS_AND_FLOW_ANALYSIS.md)
- [自我修复架构](../02_THEORETICAL_FRAMEWORK/SELF_HEALING_AUTO_ADJUSTMENT_ARCHITECTURE.md)
- [分布式系统理论](../02_THEORETICAL_FRAMEWORK/DISTRIBUTED_SYSTEMS_THEORY.md)

### 🚀 OTLP 2024-2025 参考

- [🌟 OTLP 标准对齐](../08_REFERENCE/otlp_standards_alignment.md) - 完整 OTLP 标准参考
- [🚀 OTLP 2024-2025 特性](../08_REFERENCE/otlp_2024_2025_features.md) - Profile/Event/Arrow 等新特性

### 外部资源

- [OpenTelemetry 架构](https://opentelemetry.io/docs/reference/specification/)
- [OTLP 协议规范](https://github.com/open-telemetry/opentelemetry-specification/blob/main/specification/protocol/otlp.md)
- [Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/)
- [Rust 异步编程](https://rust-lang.github.io/async-book/)
- [Tokio 架构](https://tokio.rs/tokio/tutorial)

---

## 💡 架构决策记录 (ADR)

### 重要决策

1. **ADR-001: Crate 拆分** - 为什么采用多 crate 架构
2. **ADR-002: 异步运行时** - 为什么选择 Tokio
3. **ADR-003: 错误处理** - 统一错误处理的设计
4. **ADR-004: 批处理策略** - 批处理的实现方案
5. **ADR-005: 传输协议** - gRPC vs HTTP 的选择

### 🆕 2025 新架构决策

1. **ADR-006: Profile 信号集成** - pprof 格式性能分析数据支持
2. **ADR-007: Event 信号设计** - 独立事件模型 vs 日志模型
3. **ADR-008: OTLP/Arrow 传输** - Apache Arrow 格式高性能传输
4. **ADR-009: Semantic Conventions v1.25+** - GenAI/云原生属性集成
5. **ADR-010: 增强日志模型** - 结构化日志复杂数据支持

> 详细的 ADR 文档即将推出

---

## 🤝 参与架构讨论

### 提出架构建议

1. 查看 [贡献指南](../guides/CONTRIBUTING.md)
2. 在 [Discussions](https://github.com/your-org/OTLP_rust/discussions) 发起讨论
3. 提交架构改进提案
4. 参与架构评审

### 我们欢迎

- 📝 架构改进建议
- 🐛 架构问题报告
- ✨ 新功能架构设计
- 📚 架构文档改进

---

## 💬 反馈

### 架构相关问题？

1. 查看 [FAQ](../guides/troubleshooting.md)
2. 搜索 [GitHub Issues](https://github.com/your-org/OTLP_rust/issues)
3. 提出新的 Issue
4. 参与社区讨论

---

*祝你学习愉快！* 🏗️
