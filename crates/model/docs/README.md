# C12 模型与架构：文档中心

**版本**: 2.1  
**最后更新**: 2025年10月27日  
**Rust 版本**: 1.90.0 (const API 稳定、LLD链接器优化)  
**状态**: 🟢 活跃维护

> **简介**: 基于 Rust 1.90+ 的现代化建模与形式方法库，涵盖并发模型、分布式系统、形式化方法、架构设计等核心建模技术。

---

## 📋 目录

- [C12 模型与架构：文档中心](#c12-模型与架构文档中心)
  - [📋 目录](#-目录)
  - [1. 文档导航](#1-文档导航)
    - [1.1 快速入口](#11-快速入口)
    - [1.2 核心主题](#12-核心主题)
  - [2. 层级化文档结构](#2-层级化文档结构)
    - [2.1 Tier 1: 基础层](#21-tier-1-基础层)
    - [2.2 Tier 2: 指南层](#22-tier-2-指南层)
    - [2.3 Tier 3: 参考层](#23-tier-3-参考层)
    - [2.4 Tier 4: 高级层](#24-tier-4-高级层)
  - [3. Rust 1.90 新特性](#3-rust-190-新特性)
  - [4. 快速开始](#4-快速开始)
  - [5. 项目亮点](#5-项目亮点)
  - [6. 贡献指南](#6-贡献指南)
  - [7. 相关资源](#7-相关资源)

---

## 🎯 文档导航

### 1.1 快速入口

| 入口 | 说明 | 适合人群 |
|------|------|---------|
| [**主索引**](./00_MASTER_INDEX.md) | 完整文档导航，按角色/主题/场景分类 | 所有用户 |
| [**项目概览**](./OVERVIEW.md) | 项目整体介绍和特性概览 | 初次了解 |
| [**快速开始**](./tutorials/quick-start.md) | 10分钟快速入门教程 | 新手 |
| [**常见问题**](./FAQ.md) | 常见问题解答 | 遇到问题 |
| [**术语表**](./Glossary.md) | 专业术语解释 | 查询概念 |

### 1.2 核心主题

```text
┌─────────────────────────────────────────────────────────────┐
│                      C12 建模与架构体系                      │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐          │
│  │ 并发模型     │  │ 分布式系统   │  │ 架构设计     │         │
│  │ Concurrency │  │ Distributed │  │ Architecture│          │
│  └─────────────┘  └─────────────┘  └─────────────┘          │
│                                                             │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐          │
│  │ 形式化方法   │  │ 核心概念     │  │ 使用指南     │         │
│  │ Formal      │  │ Core        │  │ Guides      │          │
│  └─────────────┘  └─────────────┘  └─────────────┘          │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

#### 1.2.1 并发模型

并发编程、异步模型、背压控制

- **Actor模型** - 消息传递并发
- **CSP模型** - 通信顺序进程  
- **异步递归** - 递归异步函数
- **背压控制** - 流量控制机制

**推荐起点**: [并发模型总览](./concurrency/README.md)

#### 1.2.2 分布式系统

分布式共识、一致性、快照算法

- **Raft共识** - 分布式共识算法
- **分布式快照** - Chandy-Lamport算法
- **向量时钟** - 因果关系追踪

**推荐起点**: [Raft共识算法](./distributed/raft-consensus-comprehensive.md)

#### 1.2.3 架构设计

软件架构模式、微服务设计

- **分层架构** - 经典分层模式
- **事件驱动** - Event-Driven Architecture
- **微服务** - Microservices patterns
- **CQRS** - 命令查询职责分离

**推荐起点**: [架构设计总览](./architecture/README.md)

#### 1.2.4 形式化方法

语义模型、形式化验证

- **操作语义** - 小步/大步语义
- **指称语义** - 数学函数映射
- **公理语义** - Hoare逻辑
- **模型检查** - 自动化验证

**推荐起点**: [形式化方法总览](./formal/README.md)

#### 1.2.5 核心概念

建模基础理论

- **建模概述** - 建模方法论
- **算法模型** - 算法理论基础

**推荐起点**: [建模概述](./core/modeling-overview.md)

#### 1.2.6 使用指南

实践指南和最佳实践

- **综合指南** - 完整使用指南
- **系统建模** - 系统建模方法
- **机器学习** - ML模型集成
- **状态机** - FSM到协议设计

**推荐起点**: [综合使用指南](./guides/comprehensive-usage-guide.md)

---

## 🚀 快速开始

### 第一步：安装配置

参考 [安装指南](./tutorials/installation.md) 配置开发环境。

```bash
# 确保 Rust 1.90+ 已安装
rustc --version  # 应显示 1.90.0

# 验证 LLD 链接器（Linux x86_64 默认启用）
rustc -C help | grep lld

# 克隆项目
git clone <repository-url>
cd rust-lang/crates/c12_model

# 编译检查（受益于 LLD 链接器提速）
cargo check -p c12_model

# 构建优化（使用 Rust 1.90 新特性）
cargo build --release
```

### 第二步：运行示例

```bash
# 并发模型示例
cargo run -p c12_model --example concurrency_models

# 分布式系统示例
cargo run -p c12_model --example distributed_consensus

# 形式化方法示例
cargo run -p c12_model --example formal_methods_examples
```

### 第三步：深入学习

根据你的兴趣和需求，选择学习路径：

- **并发开发者** → [并发模型](./concurrency/)
- **分布式系统** → [分布式文档](./distributed/)
- **架构设计** → [架构设计](./architecture/)
- **研究学习** → [形式化方法](./formal/)

---

## 📚 学习路径

### 🌟 初学者路径

**目标**: 理解基本概念，能够使用基础模型

1. **入门** (1-2天)
   - [项目概览](./OVERVIEW.md)
   - [快速开始](./tutorials/quick-start.md)
   - [建模概述](./core/modeling-overview.md)

2. **基础** (3-5天)
   - [并发模型入门](./concurrency/README.md)
   - [架构基础](./architecture/README.md)
   - [运行示例](./examples/)

3. **实践** (1周)
   - [系统建模指南](./guides/system-modeling.md)
   - [使用指南](./guides/comprehensive-usage-guide.md)
   - 完成小项目

**时间**: 2-3周

### 🎓 中级路径

**目标**: 掌握核心模型，能够设计并发和分布式系统

1. **并发深入** (1-2周)
   - [并发模型深度分析](./concurrency/concurrency-models-deep-dive.md)
   - [异步递归](./concurrency/async-recursion.md)
   - [背压控制](./concurrency/backpressure-models.md)

2. **分布式系统** (2-3周)
   - [Raft共识算法](./distributed/raft-consensus-comprehensive.md)
   - [分布式快照](./distributed/distributed-snapshot-comprehensive.md)
   - [分布式架构设计](./architecture/distributed-design.md)

3. **架构设计** (1-2周)
   - [软件设计模型](./architecture/software-design-models-comprehensive.md)
   - [微服务机制](./architecture/microservices-mechanisms.md)
   - [设计模式](./patterns/)

**时间**: 4-7周

### 🔬 高级路径

**目标**: 精通形式化方法，能够进行理论研究和高级系统设计

1. **形式化方法** (2-3周)
   - [语言语义学](./formal/language-semantics.md)
   - [语义模型](./formal/semantic-models-comprehensive.md)
   - [状态机到协议](./guides/fsm-to-protocol.md)

2. **高级主题** (2-4周)
   - [模型分类体系](./advanced/MODEL_COMPREHENSIVE_TAXONOMY.md)
   - [模型关系分析](./advanced/MODEL_RELATIONSHIPS_COMPREHENSIVE.md)
   - [架构设计理论](./advanced/MODEL_ARCHITECTURE_DESIGN.md)

3. **研究方向** (持续)
   - [领域应用](./domain/)
   - [贡献开发](./development/contributing.md)
   - 学术研究

**时间**: 8-12周及以后

---

## 📖 文档结构

### 文档组织

```text
docs/
├── 00_MASTER_INDEX.md          # 主导航索引 ⭐
├── README.md                    # 本文档 - 文档中心首页
├── OVERVIEW.md                  # 项目概览
├── FAQ.md                       # 常见问题
├── Glossary.md                  # 术语表
├── SUMMARY.md                   # 文档结构总览
│
├── core/                        # 核心概念
│   ├── modeling-overview.md    # 建模概述
│   └── algorithm-models.md     # 算法模型
│
├── concurrency/                 # 并发模型 ⭐
│   ├── README.md               # 并发总览
│   ├── models.md               # 模型分类
│   ├── async-sync-classification.md
│   ├── async-recursion.md
│   ├── backpressure-models.md
│   └── ...
│
├── distributed/                 # 分布式系统 ⭐
│   ├── raft-consensus-comprehensive.md
│   └── distributed-snapshot-comprehensive.md
│
├── architecture/                # 架构设计 ⭐
│   ├── README.md
│   ├── design-models.md
│   ├── distributed-design.md
│   ├── software-design-models-comprehensive.md
│   └── microservices-mechanisms.md
│
├── formal/                      # 形式化方法 ⭐
│   ├── README.md
│   ├── language-semantics.md
│   └── semantic-models-comprehensive.md
│
├── guides/                      # 使用指南
│   ├── README.md
│   ├── comprehensive-usage-guide.md
│   ├── system-modeling.md
│   ├── machine-learning.md
│   └── ...
│
├── tutorials/                   # 教程
│   ├── README.md
│   ├── installation.md
│   └── quick-start.md
│
├── api/                        # API 参考
│   ├── README.md
│   ├── formal-models.md
│   ├── ml-models.md
│   └── queueing-models.md
│
├── examples/                    # 示例
│   └── README.md
│
├── patterns/                    # 设计模式
│   └── README.md
│
├── domain/                      # 领域应用
│   └── README.md
│
├── development/                 # 开发指南
│   ├── README.md
│   └── contributing.md
│
├── advanced/                    # 高级主题
│   ├── MODEL_COMPREHENSIVE_TAXONOMY.md
│   ├── MODEL_RELATIONSHIPS_COMPREHENSIVE.md
│   ├── MODEL_RELATIONSHIPS_AND_SEMANTICS.md
│   └── MODEL_ARCHITECTURE_DESIGN.md
│
└── archives/                    # 归档文档
    └── (历史文档和报告)
```

### 文档类型说明

| 标记 | 说明 |
|-----|------|
| ⭐ | 核心文档，重点推荐 |
| 📚 | 理论文档，深入学习 |
| 🔧 | 实践文档，动手操作 |
| 📖 | 参考文档，查阅使用 |

---

## 🎯 按场景查找

### 我想学习并发编程

1. [并发模型总览](./concurrency/README.md)
2. [并发模型分类](./concurrency/models.md)
3. [异步递归模型](./concurrency/async-recursion.md)
4. [背压控制](./concurrency/backpressure-models.md)

### 我想设计分布式系统

1. [Raft共识算法](./distributed/raft-consensus-comprehensive.md)
2. [分布式快照](./distributed/distributed-snapshot-comprehensive.md)
3. [分布式架构设计](./architecture/distributed-design.md)
4. [微服务机制](./architecture/microservices-mechanisms.md)

### 我想进行形式化验证

1. [形式化方法总览](./formal/README.md)
2. [语言语义学](./formal/language-semantics.md)
3. [语义模型](./formal/semantic-models-comprehensive.md)
4. [状态机到协议](./guides/fsm-to-protocol.md)

### 我想学习架构设计

1. [架构设计总览](./architecture/README.md)
2. [设计模型](./architecture/design-models.md)
3. [软件设计模型](./architecture/software-design-models-comprehensive.md)
4. [分布式架构](./architecture/distributed-design.md)

---

## 🔗 相关资源

### 项目文档

- [项目 README](../README.md) - 项目总体介绍
- [路线图](../ROADMAP.md) - 开发路线图
- [里程碑](../MILESTONES.md) - 项目里程碑
- [更新日志](../CHANGELOG.md) - 版本历史

### 代码资源

- [源码](../src/) - 实现代码
- [示例](../examples/) - 示例程序
- [测试](../tests/) - 测试用例
- [基准](../benches/) - 性能测试

### 外部链接

- [Rust 官方文档](https://doc.rust-lang.org/)
- [Rust 标准库](https://doc.rust-lang.org/std/)
- [Tokio 文档](https://tokio.rs/)

---

## 💡 使用建议

### 如何阅读文档

1. **首次访问**: 先阅读 [项目概览](./OVERVIEW.md) 了解全貌
2. **查找内容**: 使用 [主索引](./00_MASTER_INDEX.md) 定位所需文档
3. **循序渐进**: 按照推荐的学习路径逐步学习
4. **动手实践**: 结合 [示例代码](./examples/) 和 [教程](./tutorials/) 实践
5. **问题求助**: 查看 [FAQ](./FAQ.md) 或提交 Issue

### 文档反馈

我们欢迎任何形式的反馈：

- **问题报告**: 发现文档错误或不清晰的地方
- **改进建议**: 对文档结构和内容的建议
- **贡献文档**: 补充缺失的文档或改进现有文档

参考 [贡献指南](./development/contributing.md) 了解如何贡献。

---

## 📊 文档统计

- **文档总数**: 50+ 篇
- **代码示例**: 15+ 个
- **API 文档**: 4 篇
- **教程文档**: 3 篇
- **覆盖主题**: 6 大类

**文档更新频率**: 定期更新  
**文档质量**: ⭐⭐⭐⭐⭐

---

## 📞 获取帮助

### 文档问题

- 查看 [FAQ](./FAQ.md)
- 搜索 [主索引](./00_MASTER_INDEX.md)
- 查询 [术语表](./Glossary.md)

### 技术问题

- [GitHub Issues](https://github.com/rust-lang/rust-lang/issues)
- [GitHub Discussions](https://github.com/rust-lang/rust-lang/discussions)

### 参与贡献

- [贡献指南](./development/contributing.md)
- [开发文档](./development/README.md)

---

**文档维护**: Rust 学习社区  
**最后更新**: 2025-10-27  
**文档版本**: v2.1  
**适用版本**: Rust 1.90.0 (1159e78c4 2025-09-14)

## 🆕 Rust 1.90 建模特性更新

### Const 上下文稳定化
C12 建模库已全面支持 Rust 1.90 稳定的 const API，包括：

- ✅ **常量浮点运算**: `f32/f64::floor`, `ceil`, `trunc`, `round` 等可在编译期计算
- ✅ **常量切片操作**: `<[T]>::reverse` 可用于编译期数组反转
- ✅ **整数运算增强**: `checked_sub_signed`, `wrapping_sub_signed` 支持有符号/无符号混合运算

### 编译性能优化
- **LLD 链接器**: 在 Linux x86_64 上，模型库编译速度提升 30-50%
- **增量编译**: 模型重编译时间显著减少

### 工作区管理
```bash
# 一键发布整个工作区（Rust 1.90 新特性）
cargo publish --workspace

# 检查工作区依赖
cargo tree --workspace
```

### 使用建议
```rust
// 利用 Rust 1.90 的 const 特性进行编译期计算
const MODEL_SCALE: f64 = 1.5_f64.floor();  // 编译期常量
const ARRAY_SIZE: usize = [1, 2, 3].len(); // 编译期数组长度
```

---

**开始你的学习之旅**: [主索引](./00_MASTER_INDEX.md) | [快速开始](./tutorials/quick-start.md) | [项目概览](./OVERVIEW.md)
