# C13 可靠性框架: 主索引 (Master Index)

**版本**: 2.1.0  
**最后更新**: 2025年10月28日  
**Rust 版本**: 1.90.0 (LLD链接器、const API、workspace发布)  
**状态**: 🟢 活跃维护

> **简介**: C13可靠性框架学习路径总导航，涵盖容错、分布式系统、微服务架构等核心模式，帮助您快速找到所需资源。

---

## 📋 目录

- [1. 快速导航](#1-快速导航)
- [2. 文档结构](#2-文档结构)
- [3. 按主题导航](#3-按主题导航)
- [4. 学习路径](#4-学习路径)
- [5. 按场景导航](#5-按场景导航)
- [6. 项目统计](#6-项目统计)
- [7. 外部资源](#7-外部资源)
- [8. 最近更新](#8-最近更新)
- [9. 获取帮助](#9-获取帮助)

---

## 🚀 快速导航

### 1.1 按角色导航

| 角色 | 推荐路径 | 关键文档 |
|------|---------|---------|
| **初学者** | [README](../README.md) → [快速开始](../QUICK_START.md) → 熔断器 | 基础模式 |
| **中级开发者** | 分布式系统 → 微服务 → 可观测性 | 生产实践 |
| **架构师** | 架构设计 → 性能优化 → 容量规划 | 架构决策 |
| **研究者** | 形式化验证 → 算法分类 → 理论分析 | 学术研究 |

---

---

## 📝 文档结构

### 2.1 用户指南 (guides/)

完整的使用指南和最佳实践：

- **[指南总览](guides/README.md)** - 用户指南索引
- **[快速开始](../QUICK_START.md)** - 5分钟快速上手
- **[使用指南](guides/usage-guide.md)** - 详细使用说明
- **[最佳实践](guides/best-practices.md)** - 生产环境最佳实践
- **[综合指南](guides/comprehensive-guide.md)** - 完整功能介绍

**适用人群**: 初学者、中级开发者  
**推荐起点**: 快速开始 → 使用指南 → 最佳实践

---

### 2.2 架构设计 (architecture/)

框架架构设计与决策文档：

- **[架构总览](architecture/README.md)** - 架构文档索引
- **[整体架构](../ARCHITECTURE.md)** - 分层架构、核心模块、运行时环境
- **[架构概览](architecture/overview.md)** - 详细的架构说明
- **[架构决策](architecture/decisions.md)** - 12个ADR文档
- **[实施路线图](architecture/implementation-roadmap.md)** - 实施计划

**适用人群**: 架构师、高级开发者  
**核心亮点**: 支持13种运行时环境、模块化设计、统一抽象

---

### 2.3 API 文档 (api/)

完整的 API 参考文档：

- **[API总览](api/README.md)** - API文档索引
- **[API参考手册](api/reference.md)** - 所有公共接口、函数签名、使用示例

**适用人群**: 所有开发者  
**主要模块**: 容错机制、分布式系统、并发模型、微服务、可观测性

---

### 2.4 功能文档 (features/)

各功能模块的详细文档：

- **[功能总览](features/README.md)** - 功能模块索引
- **[容错机制](features/fault-tolerance.md)** - 熔断器、限流器、重试等
- **[分布式系统](features/distributed-systems.md)** - Raft、分布式事务、一致性哈希
- **[并发模型](features/concurrency-models.md)** - Actor、CSP、STM、Fork-Join
- **[微服务架构](features/microservices.md)** - 服务发现、API网关、负载均衡

**适用人群**: 所有开发者  
**完成度**: 容错(100%)、分布式(100%)、并发(100%)、微服务(80%)

---

### 2.5 高级主题 (advanced/)

深入的高级主题与研究：

- **[高级主题总览](advanced/README.md)** - 高级文档索引
- **[运行时环境](advanced/runtime-environments/)** - 13种运行时环境支持
  - [环境总览](advanced/runtime-environments/overview.md)
  - [环境分类](advanced/runtime-environments/taxonomy.md)
  - [实现细节](advanced/runtime-environments/implementation.md)
  - [能力矩阵](advanced/runtime-environments/capabilities-matrix.md)
- **[算法分类](advanced/algorithm-taxonomy.md)** - 完整的算法分类体系
- **[Rust 1.90 特性](advanced/rust-190-features.md)** - 最新Rust特性应用
- **[高级特性总结](advanced/features-summary.md)** - 高级功能概览

**适用人群**: 高级开发者、架构师、研究者  
**核心主题**: 运行时环境适配、算法分类、形式化验证

---

### 2.6 参考资料 (reference/)

常见问题、术语表和统计信息：

- **[参考资料总览](reference/README.md)** - 参考资料索引
- **[FAQ](reference/FAQ.md)** - 常见问题解答
- **[术语表](reference/Glossary.md)** - 专业术语词汇表
- **[代码统计](reference/code-statistics.md)** - 项目代码统计

**适用人群**: 所有用户  
**使用场景**: 快速查找、概念理解、问题解答

---

### 2.7 历史归档 (archives/)

项目历史文档归档：

- **[归档总览](archives/README.md)** - 历史文档索引
- **进度报告** - `archives/progress-reports/`
  - 2025-10-03 进度报告
  - 2025-10-04 进度报告
  - 2025-10-12 进度报告
- **完成报告** - `archives/completion-reports/`
- **里程碑记录** - `archives/milestones-*.md`

**适用人群**: 项目维护者  
**用途**: 历史追溯、学习项目演进

---

---

## 🔍 核心功能

### 3.1 容错与弹性

**主文档**: [容错机制详解](features/fault-tolerance.md)

**核心模式**: 熔断器 | 重试策略 | 超时控制 | 降级策略 | 限流器 | 舱壁模式

**最佳实践**: 合理设置阈值 | 选择合适策略 | 避免重试风暴 | 监控状态

**深入阅读**: [容错增强报告](FAULT_TOLERANCE_ENHANCEMENT_REPORT.md)

---

### 3.2 分布式系统

**主文档**: [分布式系统详解](features/distributed-systems.md) | [架构概览](architecture/overview.md)

**核心算法**: Raft共识 | 分布式事务 | 一致性哈希 | 分布式锁 | 向量时钟

**应用场景**: 分布式数据库 | 分布式缓存 | 消息队列 | 配置中心

---

### 3.3 并发与并行

**主文档**: [并发模型详解](features/concurrency-models.md)

**并发抽象**: Actor模型 | CSP模型 | STM | Fork-Join

**同步原语**: Mutex/RwLock | Channel | Barrier | Atomic操作

**深入阅读**: [并发工程报告](archives/PARALLEL_CONCURRENT_ENHANCEMENT_REPORT.md)

---

### 3.4 微服务与云原生

**主文档**: [微服务详解](features/microservices.md)

**核心组件**: 服务发现 | API网关 | 负载均衡 | 配置中心 | 分布式追踪

**治理功能**: 服务注册 | 健康检查 | 路由策略 | 熔断降级 | 灰度发布

**深入阅读**: [微服务增强](archives/MICROSERVICE_ENHANCEMENT_REPORT.md)

---

## 🔧 高级主题

### 4.1 可观测性

**主文档**: [API参考 - 可观测性](api/reference.md#可观测性)

**三大支柱**: Metrics(指标) | Tracing(追踪) | Logging(日志)

**工具集成**: OpenTelemetry | Prometheus | Jaeger/Zipkin | ELK

---

### 4.2 形式化验证

**主文档**: [形式化验证工具指南](FORMAL_VERIFICATION_TOOLS_GUIDE.md) | [验证示例](FORMAL_VERIFICATION_EXAMPLES_FIXES.md)

**验证工具**: Kani(模型检查) | Creusot(演绎验证) | Prusti(Viper) | MIRI(UB检测)

**应用场景**: 安全关键系统 | 金融交易 | 医疗设备 | 航空航天

---

### 4.3 运行时环境适配

**主文档**: [环境总览](archives/legacy_advanced/runtime-environments/overview.md) | [环境分类](archives/legacy_advanced/runtime-environments/taxonomy.md)

**支持环境**: OS(Linux/Windows/macOS) | 容器(Docker/Podman) | 编排(K8s) | 无服务器(Lambda/Functions) | 嵌入式(bare-metal/RTOS) | 边缘计算

---

## 📊 学习路径

### 5.1 初学者（1周）

**路径**: README → 快速开始 → 容错机制 → 使用指南

**文档**: [README](../README.md) | [快速开始](../QUICK_START.md) | [容错机制](features/fault-tolerance.md) | [使用指南](guides/usage-guide.md)

**目标**: 使用基础容错功能

---

### 5.2 中级（2-3周)

**路径**: 分布式系统 → 微服务架构 → 最佳实践

**文档**: [分布式系统](features/distributed-systems.md) | [微服务](features/microservices.md) | [最佳实践](guides/best-practices.md)

**目标**: 构建分布式微服务应用

---

### 5.3 高级（4周+）

**路径**: 架构设计 → 运行时环境 → 算法理论 → 架构决策

**文档**: [架构设计](architecture/) | [运行时环境](advanced/runtime-environments/) | [算法分类](advanced/algorithm-taxonomy.md) | [架构决策](architecture/decisions.md)

**目标**: 架构设计和扩展开发

---

## 🌟 应用场景

### 6.1 高可用系统

**方案**: [熔断器](features/fault-tolerance.md#熔断器) | [限流器](features/fault-tolerance.md#限流器) | [重试策略](features/fault-tolerance.md#重试策略)

**文档**: [容错最佳实践](guides/best-practices.md#容错机制) | [熔断器示例](../examples/circuit_breaker_example.rs)

---

### 6.2 分布式系统

**方案**: [Raft共识](features/distributed-systems.md#raft) | [分布式事务](features/distributed-systems.md#分布式事务) | [一致性哈希](features/distributed-systems.md#一致性哈希) | [分布式锁](features/distributed-systems.md#分布式锁)

**文档**: [分布式最佳实践](guides/best-practices.md#分布式系统) | [分布式示例](../examples/distributed_systems_example.rs)

---

### 6.3 微服务架构

**方案**: [服务发现](features/microservices.md#服务发现) | [API网关](features/microservices.md#api网关) | [负载均衡](features/microservices.md#负载均衡) | [配置中心](features/microservices.md#配置中心) | [分布式追踪](features/microservices.md#分布式追踪)

**文档**: [微服务最佳实践](guides/best-practices.md#微服务) | [微服务示例](../examples/microservices_example.rs)

---

### 6.4 高并发系统

**方案**: [Actor模型](features/concurrency-models.md#actor模型) | [CSP模型](features/concurrency-models.md#csp模型) | [限流器](features/fault-tolerance.md#限流器) | [负载均衡](features/microservices.md#负载均衡)

**文档**: [并发最佳实践](guides/best-practices.md#并发控制) | [并发示例](../examples/concurrency_example.rs)

---

---

## 🔬 项目统计

| 指标 | 数值 |
|------|------|
| 代码量 | ~23,650 行 |
| 模块数 | 9 个 |
| 测试用例 | 80+ |
| 运行时环境 | 13 种 |
| 完成度 | 91% |
| Rust版本 | 1.90+ |

详见：[代码统计](reference/code-statistics.md)

---

---

## 🔬 外部资源

### 7.1 代码仓库

- [GitHub](https://github.com/yourusername/c13_reliability)
- [示例代码](../examples/)
- [测试用例](../tests/)
- [基准测试](../benches/)

### 7.2 相关项目

- [Tokio](https://tokio.rs/) - 异步运行时
- [Rust](https://www.rust-lang.org/) - Rust 语言
- [Cargo](https://doc.rust-lang.org/cargo/) - Rust 包管理器

---

---

## 🔬 最近更新

### 7.1 2025-10-27

- ✅ 完成文档标准化
- ✅ 更新Rust 1.90特性
- ✅ 统一目录结构

### 8.2 2025-10-19

- ✅ 完成文档结构重组
- ✅ 创建目录化文档体系
- ✅ 新增各目录 README
- ✅ 归档历史文档
- ✅ 更新主索引

### 8.3 2025-10-12

- ✅ 文档完善
- ✅ 功能优化

### 8.4 2025-10-04

- ✅ 测试完善
- ✅ Bug修复
- ✅ 编译成功

### 8.5 2025-10-03

- ✅ 分布式系统完成
- ✅ 并发模型实现

---

---

## 📚 获取帮助

### 9.1 文档资源

- **文档问题** → [FAQ](reference/FAQ.md)
- **概念理解** → [术语表](reference/Glossary.md)
- **使用问题** → [使用指南](USAGE_GUIDE.md)
- **代码问题** → [示例代码](../examples/)

### 9.2 社区支持

- **Bug报告** → [GitHub Issues](https://github.com/yourusername/c13_reliability/issues)
- **功能建议** → 提交 Issue
- **贡献代码** → 查看 CONTRIBUTING.md

---

**版本**: 2.1.0  
**Rust 版本**: 1.90.0 (LLD链接器、const API、workspace发布)  
**最后更新**: 2025年10月27日  
**维护者**: C13 Reliability Team  
**反馈**: [提交 Issue](https://github.com/yourusername/c13_reliability/issues)

---

> **提示**: 从快速导航开始，根据您的角色和场景选择合适的学习路径！🦀✨
