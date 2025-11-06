# C12 模型与架构：主索引

**版本**: 1.2.0
**最后更新**: 2025年10月28日
**Rust 版本**: 1.90.0 (const API稳定、LLD链接器优化)
**状态**: 🟢 活跃维护

> **简介**: 软件建模与形式方法学习路径总导航，作为学习起点，根据需求选择合适的模型和方法。

---

## 📋 目录

- [C12 模型与架构：主索引](#c12-模型与架构主索引)
  - [📋 目录](#-目录)
  - [🚀 快速导航](#-快速导航)
    - [1.1 按角色导航](#11-按角色导航)
    - [1.2 按主题导航](#12-按主题导航)
  - [📝 文档结构](#-文档结构)
  - [🔍 核心模型文档](#-核心模型文档)
    - [3.1 并发模型](#31-并发模型)
    - [3.2 分布式系统](#32-分布式系统)
    - [3.3 架构设计](#33-架构设计)
    - [3.4 形式化方法](#34-形式化方法)
  - [🔧 实践文档](#-实践文档)
    - [4.1 使用指南](#41-使用指南)
    - [4.2 教程](#42-教程)
    - [4.3 API 参考](#43-api-参考)
    - [4.4 示例与模式](#44-示例与模式)
  - [📊 高级主题](#-高级主题)
  - [🌟 学习路径](#-学习路径)
    - [6.1 初学者路径（1-2周）](#61-初学者路径1-2周)
    - [6.2 中级路径（3-6周）](#62-中级路径3-6周)
    - [6.3 高级路径（7-12周）](#63-高级路径7-12周)
  - [🔬 使用场景](#-使用场景)
    - [7.1 高并发系统开发](#71-高并发系统开发)
    - [7.2 分布式系统设计](#72-分布式系统设计)
    - [7.3 微服务架构](#73-微服务架构)
    - [7.4 形式化验证](#74-形式化验证)
  - [💻 项目资源](#-项目资源)
  - [📚 项目统计](#-项目统计)
  - [✅ 使用建议](#-使用建议)
  - [🌈 支持与贡献](#-支持与贡献)
  - [附录: 更新历史](#附录-更新历史)
    - [2025-10-27](#2025-10-27)
    - [2025-10-19](#2025-10-19)
    - [历史更新](#历史更新)


## 🚀 快速导航

### 1.1 按角色导航

| 角色 | 推荐路径 | 关键文档 |
|------|---------|---------|
| **初学者** | README → 教程 → 核心概念 | [快速开始](./tutorials/quick-start.md) |
| **中级开发者** | 并发模型 → 分布式系统 → 架构设计 | [使用指南](./guides/) |
| **架构师** | 架构设计 → 模型分类 → 高级主题 | [架构设计](./architecture/) |
| **研究者** | 形式化方法 → 语义模型 → 算法理论 | [形式化方法](./formal/) |

### 1.2 按主题导航

| 主题 | 文档入口 | 说明 |
|------|---------|------|
| **概览** | [OVERVIEW.md](./OVERVIEW.md) | 项目整体概述 |
| **核心概念** | [core/](./core/) | 建模基础理论 |
| **并发模型** | [concurrency/](./concurrency/) | 并发与异步模型 |
| **分布式系统** | [distributed/](./distributed/) | 分布式共识与算法 |
| **架构设计** | [architecture/](./architecture/) | 软件架构模式 |
| **形式化方法** | [formal/](./formal/) | 语义与验证 |

---

---

## 📝 文档结构

```text
docs/
├── 00_MASTER_INDEX.md          # 主导航索引
├── README.md                    # 文档中心
├── OVERVIEW.md                  # 项目概述
├── FAQ.md / Glossary.md         # 参考资料
│
├── core/                        # 核心概念
├── concurrency/                 # 并发模型
├── distributed/                 # 分布式系统
├── architecture/                # 架构设计
├── formal/                      # 形式化方法
│
├── guides/                      # 使用指南
├── tutorials/                   # 教程
├── api/                        # API参考
├── examples/                   # 示例
│
└── advanced/                   # 高级主题
```

---

## 🔍 核心模型文档

### 3.1 并发模型

**目录**: [concurrency/](./concurrency/)

**核心文档**:

- [并发模型总览](./concurrency/README.md) - 入门必读
- [并发模型分类](./concurrency/models.md) - 完整分类
- [深度分析](./concurrency/concurrency-models-deep-dive.md) - 深入理解

**专题文档**:

- 异步同步分类 | 异步递归模型 | 背压控制 | 工程实践

**适合**: 中高级开发者、并发系统设计者

---

### 3.2 分布式系统

**目录**: [distributed/](./distributed/)

**核心文档**:

- [Raft共识算法](./distributed/raft-consensus-comprehensive.md) - 完整实现
- [分布式快照](./distributed/distributed-snapshot-comprehensive.md) - Chandy-Lamport

**适合**: 分布式系统开发者、架构师

---

### 3.3 架构设计

**目录**: [architecture/](./architecture/)

**核心文档**:

- [架构设计总览](./architecture/README.md)
- [设计模型](./architecture/design-models.md)
- [分布式架构设计](./architecture/distributed-design.md)
- [软件设计模型综合](./architecture/software-design-models-comprehensive.md)
- [微服务机制](./architecture/microservices-mechanisms.md)

**适合**: 架构师、系统设计者

---

### 3.4 形式化方法

**目录**: [formal/](./formal/)

**核心文档**:

- [形式化方法总览](./formal/README.md)
- [语言语义学](./formal/language-semantics.md)
- [语义模型综合](./formal/semantic-models-comprehensive.md)

**适合**: 研究者、编译器开发者、形式化验证工程师

---

## 🔧 实践文档

### 4.1 使用指南

**目录**: [guides/](./guides/)

**综合指南**:

- [综合使用指南](./guides/comprehensive-usage-guide.md) - 完整指南
- [系统建模指南](./guides/system-modeling.md) - 系统建模
- [机器学习集成](./guides/machine-learning.md) - ML模型
- [状态机到协议](./guides/fsm-to-protocol.md) - FSM设计

**适合**: 所有开发者

---

### 4.2 教程

**目录**: [tutorials/](./tutorials/)

**入门教程**:

- [安装配置](./tutorials/installation.md)
- [快速开始](./tutorials/quick-start.md)

**适合**: 初学者

---

### 4.3 API 参考

**目录**: [api/](./api/)

**API 文档**:

- [形式化模型 API](./api/formal-models.md)
- [机器学习模型 API](./api/ml-models.md)
- [排队论模型 API](./api/queueing-models.md)

**适合**: API 使用者

---

### 4.4 示例与模式

- **示例代码**: [examples/](./examples/)
- **设计模式**: [patterns/](./patterns/)
- **领域应用**: [domain/](./domain/)

---

## 📊 高级主题

**目录**: [advanced/](./advanced/)

**深度分析**:

- [模型分类体系](./advanced/MODEL_COMPREHENSIVE_TAXONOMY.md) - 完整分类
- [模型关系分析](./advanced/MODEL_RELATIONSHIPS_COMPREHENSIVE.md) - 关系网络
- [模型架构设计](./advanced/MODEL_ARCHITECTURE_DESIGN.md) - 架构模式

**适合**: 高级开发者、研究者

---

## 🌟 学习路径

### 6.1 初学者路径（1-2周）

理解基本概念，使用基础模型

**路径**: README → 快速开始 → 建模概述 → 示例代码

**推荐文档**: [OVERVIEW](./OVERVIEW.md) | [快速开始](./tutorials/quick-start.md) | [建模概述](./core/modeling-overview.md)

---

### 6.2 中级路径（3-6周）

掌握核心模型，设计并发和分布式系统

**路径**: 并发模型 → 分布式系统 → 架构设计 → 使用指南

**推荐文档**: [并发](./concurrency/) | [分布式](./distributed/) | [架构](./architecture/)

---

### 6.3 高级路径（7-12周）

精通形式化方法，理论研究和高级设计

**路径**: 形式化方法 → 高级主题 → 设计模式 → 领域应用

**推荐文档**: [形式化](./formal/) | [高级主题](./advanced/) | [模式](./patterns/)

---

## 🔬 使用场景

### 7.1 高并发系统开发

**推荐**: [并发模型分类](./concurrency/models.md) | [背压控制](./concurrency/backpressure-models.md) | [异步编程](./concurrency/async-sync-classification.md)

---

### 7.2 分布式系统设计

**推荐**: [Raft共识](./distributed/raft-consensus-comprehensive.md) | [分布式快照](./distributed/distributed-snapshot-comprehensive.md) | [分布式架构](./architecture/distributed-design.md)

---

### 7.3 微服务架构

**推荐**: [架构设计](./architecture/design-models.md) | [微服务机制](./architecture/microservices-mechanisms.md) | [系统建模](./guides/system-modeling.md)

---

### 7.4 形式化验证

**推荐**: [语义模型](./formal/semantic-models-comprehensive.md) | [语言语义学](./formal/language-semantics.md) | [状态机到协议](./guides/fsm-to-protocol.md)

---

---

## 💻 项目资源

**项目文档**: [README](../README.md) | [路线图](../ROADMAP.md) | [更新日志](../CHANGELOG.md)

**代码资源**: [源码](../src/) | [示例](../examples/) | [测试](../tests/) | [基准](../benches/)

**配置文件**: [Cargo.toml](../Cargo.toml) | [book.toml](./book.toml)

---

## 📚 项目统计

| 指标 | 数值 | 说明 |
|------|------|------|
| 文档总数 | 50+ | 包含所有.md文件 |
| 核心模型 | 4类 | 并发/分布式/架构/形式化 |
| API文档 | 3篇 | 完整API参考 |
| 示例代码 | 15+ | 实践示例 |
| 更新频率 | 月度 | 持续维护 |

---

## ✅ 使用建议

**首次使用**: [README](./README.md) + [OVERVIEW](./OVERVIEW.md) → 了解全貌

**快速入门**: [快速开始](./tutorials/quick-start.md) → 10分钟上手

**深入学习**: 按学习路径(6.1-6.3) → 系统掌握

**问题解决**: [FAQ](./FAQ.md) | [术语表](./Glossary.md) → 快速查询

---

## 🌈 支持与贡献

**问题反馈**: [GitHub Issues](https://github.com/rust-lang/rust-lang/issues) | [Discussions](https://github.com/rust-lang/rust-lang/discussions)

**参与贡献**: [贡献指南](./development/contributing.md) | [开发文档](./development/)

---

## 附录: 更新历史

### 2025-10-27

- ✅ **标准化格式**: 添加完整目录和统一序号
- ✅ **更新元数据**: 更新为 Rust 1.90.0 版本
- ✅ **优化结构**: 重组文档结构和导航

### 2025-10-19

- ✅ 重组文档结构
- ✅ 合并重复目录 (concurrent → concurrency)
- ✅ 创建清晰的分类体系
- ✅ 添加学习路径指引
- ✅ 完善导航索引

### 历史更新

详见 [归档文档](./archives/) 和 [更新日志](../CHANGELOG.md)

---

**文档版本**: 1.2
**Rust 版本**: 1.90.0 (const API稳定、LLD链接器优化)
**最后更新**: 2025年10月27日
**维护者**: C12 Model Team
**反馈**: [提交 Issue](https://github.com/rust-lang/rust-lang/issues)

---

> **提示**: 本文档是学习路径总导航，建议配合 [README.md](./README.md) 和各专题目录使用。
