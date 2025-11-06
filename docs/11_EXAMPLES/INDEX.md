# 📦 可运行示例代码索引

**版本**: 1.0
**最后更新**: 2025年10月26日
**状态**: 🟢 活跃维护

> **简介**: 可运行示例代码索引 - 38+ 个 Rust 示例的完整目录和快速运行指南。

---

## 🎯 概览

本项目包含 **38+ 个可运行的 Rust 示例**，覆盖从基础到高级的各种使用场景。

### 📊 示例统计

| 类型 | 数量 | 位置 |
|------|------|------|
| OTLP 示例 | 25 | `crates/otlp/examples/` |
| 可靠性框架示例 | 13 | `crates/reliability/examples/` |
| **总计** | **38** | - |

---

## 🚀 快速开始

### 运行示例的基本命令

```bash
# 进入项目根目录
cd OTLP_rust

# 运行 OTLP 示例
cargo run --example <example_name> --package otlp

# 运行可靠性框架示例
cargo run --example <example_name> --package reliability

# 查看所有可用示例
cargo run --example 2>&1 | grep "    "
```

---

## 📚 OTLP 示例 (25个)

### ⭐ 入门级示例

#### 1. Hello World

**文件**: `crates/otlp/examples/hello_world.rs`

最简单的入门示例，创建第一个 OTLP 客户端。

```bash
cargo run --example hello_world --package otlp
```

**适合**: 第一次使用 OTLP 的开发者

---

#### 2. 简单使用

**文件**: `crates/otlp/examples/simple_usage.rs`

展示基本的追踪、指标和日志功能。

```bash
cargo run --example simple_usage --package otlp
```

**适合**: 了解基本概念

---

#### 3. 简单演示

**文件**: `crates/otlp/examples/simple_demo.rs`

快速演示 OTLP 的核心功能。

```bash
cargo run --example simple_demo --package otlp
```

**适合**: 快速预览

---

### ⭐⭐ 中级示例

#### 4. 异步追踪

**文件**: `crates/otlp/examples/async_tracing.rs`

展示如何在异步环境中使用 OTLP 追踪。

```bash
cargo run --example async_tracing --package otlp
```

**学习内容**:

- 异步函数追踪
- 上下文传播
- 并发 Span 管理

---

#### 5. 嵌套 Span

**文件**: `crates/otlp/examples/nested_spans.rs`

演示父子 Span 关系和嵌套追踪。

```bash
cargo run --example nested_spans --package otlp
```

**学习内容**:

- Span 层次结构
- 上下文传递
- 分布式追踪链

---

#### 6. 监控演示

**文件**: `crates/otlp/examples/monitoring_demo.rs`

展示监控指标收集和导出。

```bash
cargo run --example monitoring_demo --package otlp
```

**学习内容**:

- Counter、Gauge、Histogram
- 指标聚合
- 自定义指标

---

#### 7. 可靠性使用

**文件**: `crates/otlp/examples/resilience_usage.rs`

集成可靠性框架的示例。

```bash
cargo run --example resilience_usage --package otlp
```

**学习内容**:

- 错误处理
- 重试机制
- 断路器模式

---

### ⭐⭐⭐ 高级示例

#### 8. 微服务演示

**文件**: `crates/otlp/examples/microservices_demo.rs`

模拟微服务架构中的分布式追踪。

```bash
cargo run --example microservices_demo --package otlp
```

**学习内容**:

- 服务间追踪
- 上下文传播
- 调用链分析

---

#### 9. 高级微服务

**文件**: `crates/otlp/examples/advanced_microservices_demo.rs`

更复杂的微服务追踪场景。

```bash
cargo run --example advanced_microservices_demo --package otlp
```

**学习内容**:

- 复杂服务拓扑
- 异步调用追踪
- 错误传播

---

#### 10. 分布式协调

**文件**: `crates/otlp/examples/distributed_coordination_demo.rs`

展示分布式系统中的协调和追踪。

```bash
cargo run --example distributed_coordination_demo --package otlp
```

**学习内容**:

- 分布式事务追踪
- 协调服务监控
- 一致性检查

---

#### 11. 机器学习预测

**文件**: `crates/otlp/examples/ml_prediction_demo.rs`

在 ML 管道中使用 OTLP 追踪。

```bash
cargo run --example ml_prediction_demo --package otlp
```

**学习内容**:

- ML 模型监控
- 预测追踪
- 性能分析

---

### ⭐⭐⭐⭐ 性能优化示例

#### 12. 性能演示

**文件**: `crates/otlp/examples/performance_demo.rs`

展示性能优化技巧。

```bash
cargo run --example performance_demo --package otlp
```

**学习内容**:

- 批处理优化
- 连接池使用
- 内存优化

---

#### 13. 性能基准

**文件**: `crates/otlp/examples/performance_benchmarks.rs`

性能基准测试工具。

```bash
cargo run --example performance_benchmarks --package otlp
```

**学习内容**:

- 性能测试
- 吞吐量分析
- 延迟优化

---

#### 14-20. 优化系列

多个专注于不同优化方向的示例：

```bash
# 核心优化
cargo run --example core_optimization_demo --package otlp

# 简单优化
cargo run --example simple_optimization_demo --package otlp

# 快速优化
cargo run --example quick_optimizations_demo --package otlp

# 性能优化
cargo run --example performance_optimization_demo --package otlp

# 集成优化
cargo run --example integrated_optimizations_demo --package otlp

# 最终优化
cargo run --example final_optimization_demo --package otlp

# 增强监控
cargo run --example enhanced_monitoring_demo --package otlp
```

---

### ⭐⭐⭐⭐⭐ 综合示例

#### 21. 综合演示

**文件**: `crates/otlp/examples/comprehensive_demo.rs`

最全面的功能展示。

```bash
cargo run --example comprehensive_demo --package otlp
```

**学习内容**:

- 所有核心功能
- 集成使用
- 最佳实践

---

#### 22. 综合使用

**文件**: `crates/otlp/examples/comprehensive_usage.rs`

完整的使用场景演示。

```bash
cargo run --example comprehensive_usage --package otlp
```

---

#### 23. 增强客户端

**文件**: `crates/otlp/examples/enhanced_client_demo.rs`

展示增强功能的客户端。

```bash
cargo run --example enhanced_client_demo --package otlp
```

---

#### 24-25. 高级模式

```bash
# 高级模式
cargo run --example advanced_patterns --package otlp
```

---

## 🛡️ 可靠性框架示例 (13个)

### ⭐ 入门级示例1

#### 1. 基础使用

**文件**: `crates/reliability/examples/reliability_basic_usage.rs`
**行数**: 474

完整的可靠性框架入门教程。

```bash
cargo run --example reliability_basic_usage --package reliability
```

**学习内容**:

- UnifiedError 使用
- 错误上下文
- 基础监控

---

#### 2. 简单 Rust 1.90 演示

**文件**: `crates/reliability/examples/simple_rust_190_demo.rs`
**行数**: 109

展示 Rust 1.90 新特性在可靠性框架中的应用。

```bash
cargo run --example simple_rust_190_demo --package reliability
```

**学习内容**:

- Rust 1.90 特性
- 现代 Rust 实践
- 简化代码

---

### ⭐⭐ 中级示例1

#### 3. Rust 1.90 特性演示

**文件**: `crates/reliability/examples/rust_190_features_demo.rs`
**行数**: 220

深入展示 Rust 1.90 特性。

```bash
cargo run --example rust_190_features_demo --package reliability
```

**学习内容**:

- 高级特性
- 性能优化
- 新语法

---

#### 4. 运行时环境

**文件**: `crates/reliability/examples/runtime_environment_example.rs`
**行数**: 456

运行时环境检测和适配。

```bash
cargo run --example runtime_environment_example --package reliability
```

**学习内容**:

- 环境检测
- 自动适配
- 配置管理

---

#### 5. 增强环境检测

**文件**: `crates/reliability/examples/enhanced_environment_detection.rs`

高级环境检测功能。

```bash
cargo run --example enhanced_environment_detection --package reliability
```

**学习内容**:

- 多平台检测
- 容器环境
- 云平台识别

---

#### 6. 综合环境演示

**文件**: `crates/reliability/examples/comprehensive_environment_demo.rs`

完整的环境管理演示。

```bash
cargo run --example comprehensive_environment_demo --package reliability
```

---

### ⭐⭐⭐ 高级示例1

#### 7. 高级使用

**文件**: `crates/reliability/examples/advanced_usage.rs`

可靠性框架的高级功能。

```bash
cargo run --example advanced_usage --package reliability
```

**学习内容**:

- 高级错误处理
- 自定义监控
- 复杂场景

---

#### 8. 集成示例

**文件**: `crates/reliability/examples/integration_example.rs`

与其他系统的集成。

```bash
cargo run --example integration_example --package reliability
```

**学习内容**:

- 系统集成
- 接口适配
- 数据转换

---

#### 9. 监控仪表板

**文件**: `crates/reliability/examples/monitoring_dashboard.rs`

可视化监控示例。

```bash
cargo run --example monitoring_dashboard --package reliability
```

**学习内容**:

- 实时监控
- 指标可视化
- 告警配置

---

#### 10. 增强异常检测

**文件**: `crates/reliability/examples/enhanced_anomaly_detection.rs`

智能异常检测功能。

```bash
cargo run --example enhanced_anomaly_detection --package reliability
```

**学习内容**:

- 异常检测算法
- 智能告警
- 自动处理

---

### ⭐⭐⭐⭐ 架构模式示例

#### 11. 编排器（最小版）

**文件**: `crates/reliability/examples/orchestrator_minimal.rs`
**行数**: 57

服务编排器的最小实现。

```bash
cargo run --example orchestrator_minimal --package reliability
```

**学习内容**:

- 服务编排
- 工作流管理
- 状态机

---

#### 12. 监督器（最小版）

**文件**: `crates/reliability/examples/supervisor_minimal.rs`
**行数**: 44

监督器模式的最小实现。

```bash
cargo run --example supervisor_minimal --package reliability
```

**学习内容**:

- 监督器模式
- 故障恢复
- 进程管理

---

#### 13. 容器（最小版）

**文件**: `crates/reliability/examples/container_minimal.rs`

容器模式的最小实现。

```bash
cargo run --example container_minimal --package reliability
```

**学习内容**:

- 容器模式
- 依赖注入
- 生命周期管理

---

## 🎯 按场景选择

### 场景 1: 我想学习基础用法

**推荐顺序**:

```bash
# 1. OTLP 入门
cargo run --example hello_world --package otlp
cargo run --example simple_usage --package otlp

# 2. 可靠性框架入门
cargo run --example reliability_basic_usage --package reliability
```

**预计时间**: 30分钟

---

### 场景 2: 我要实现微服务追踪

**推荐顺序**:

```bash
# 1. 基础追踪
cargo run --example nested_spans --package otlp

# 2. 微服务追踪
cargo run --example microservices_demo --package otlp

# 3. 高级微服务
cargo run --example advanced_microservices_demo --package otlp

# 4. 分布式协调
cargo run --example distributed_coordination_demo --package otlp
```

**预计时间**: 2小时

---

### 场景 3: 我需要优化性能

**推荐顺序**:

```bash
# 1. 性能基准
cargo run --example performance_benchmarks --package otlp

# 2. 核心优化
cargo run --example core_optimization_demo --package otlp

# 3. 性能优化
cargo run --example performance_optimization_demo --package otlp

# 4. 最终优化
cargo run --example final_optimization_demo --package otlp
```

**预计时间**: 3小时

---

### 场景 4: 我要实现可靠性

**推荐顺序**:

```bash
# 1. 基础可靠性
cargo run --example reliability_basic_usage --package reliability

# 2. 高级使用
cargo run --example advanced_usage --package reliability

# 3. 监控仪表板
cargo run --example monitoring_dashboard --package reliability

# 4. 异常检测
cargo run --example enhanced_anomaly_detection --package reliability
```

**预计时间**: 3小时

---

### 场景 5: 我要学习 Rust 1.90 新特性

**推荐顺序**:

```bash
# 1. 简单演示
cargo run --example simple_rust_190_demo --package reliability

# 2. 特性演示
cargo run --example rust_190_features_demo --package reliability

# 3. 运行时环境
cargo run --example runtime_environment_example --package reliability
```

**预计时间**: 2小时

---

## 🔧 示例开发指南

### 创建新示例

1. **选择位置**:
   - OTLP 功能 → `crates/otlp/examples/`
   - 可靠性功能 → `crates/reliability/examples/`

2. **文件命名**: 使用描述性名称，如 `my_feature_demo.rs`

3. **基本结构**:

    ```rust
    //! # 示例标题
    //!
    //! 简短描述示例的目的和功能。
    //!
    //! ## 运行方式
    //!
    //! ```bash
    //! cargo run --example my_feature_demo --package <package_name>
    //! ```
    //!
    //! ## 学习内容
    //!
    //! - 功能点 1
    //! - 功能点 2
    //! - 功能点 3

    use otlp::*; // 或 use reliability::*;

    #[tokio::main]
    async fn main() -> Result<(), Box<dyn std::error::Error>> {
        println!("=== 示例标题 ===\n");

        // 示例代码

        println!("\n✅ 示例完成！");
        Ok(())
    }
    ```

4. **添加文档**: 在本文件中更新示例索引

---

## 📊 示例质量标准

### 优秀示例的特征

✅ **清晰的目的**: 每个示例专注一个主题
✅ **完整的文档**: 包含用途、运行方式、学习内容
✅ **可运行性**: 无需额外配置即可运行
✅ **详细注释**: 关键代码有清晰注释
✅ **错误处理**: 正确处理错误情况
✅ **输出友好**: 有清晰的输出信息

### 示例分类标准

| 级别 | 代码行数 | 复杂度 | 适合对象 |
|------|---------|--------|---------|
| ⭐ 入门 | < 50 | 低 | 新手 |
| ⭐⭐ 初级 | 50-150 | 中低 | 初学者 |
| ⭐⭐⭐ 中级 | 150-300 | 中 | 开发者 |
| ⭐⭐⭐⭐ 高级 | 300-500 | 中高 | 高级开发者 |
| ⭐⭐⭐⭐⭐ 专家 | > 500 | 高 | 架构师 |

---

## 🤝 贡献示例

### 欢迎贡献

我们欢迎社区贡献新的示例！

**贡献流程**:

1. Fork 项目
2. 创建示例文件
3. 添加文档注释
4. 本地测试
5. 更新本索引文档
6. 提交 PR

**示例主题建议**:

- 实际业务场景
- 与第三方库集成
- 性能优化技巧
- 错误处理模式
- 测试策略

---

## 📞 获取帮助

### 示例相关问题

- **示例无法运行** → 检查依赖版本，查看 [故障排除](../docs/guides/troubleshooting.md)
- **理解示例代码** → 查看代码注释和相关文档
- **需要新示例** → 提交 Issue 或贡献代码

---

## 🎊 统计信息

### 代码统计

- **总示例数**: 38+
- **OTLP 示例**: 25
- **可靠性示例**: 13
- **总代码行数**: 估计 5,000+
- **覆盖场景**: 入门到专家级全覆盖

### 维护状态

- ✅ 所有示例可运行
- ✅ 文档保持更新
- ✅ 定期优化和改进
- ✅ 社区贡献活跃

---

_最后更新: 2025年10月20日_
_维护者: OTLP Rust Team_
_版本: 1.0.0_

**Happy Coding! 🚀**-
