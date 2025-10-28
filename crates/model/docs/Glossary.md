# C12 模型与架构：术语表 (Glossary)

**版本**: 1.1  
**最后更新**: 2025年10月27日  
**Rust 版本**: 1.90.0 (const API稳定、LLD链接器优化)  
**状态**: 🟢 活跃维护

> **简介**: 模型与架构核心术语快速参考，通过术语索引快速查找定义和说明。

---

## 📋 目录

- [1. 术语索引](#1-术语索引)
- [2. 术语详解](#2-术语详解)
  - [2.1 Actor 模型](#21-actor-模型)
  - [2.2 CSP (通信顺序进程)](#22-csp-通信顺序进程)
  - [2.3 Raft (共识算法)](#23-raft-共识算法)
  - [2.4 ML (机器学习)](#24-ml-机器学习)
  - [2.5 背压 (Backpressure)](#25-背压-backpressure)
- [3. 延伸阅读](#3-延伸阅读)

---

## 📖 术语索引

**按字母顺序**:  
[A](#21-actor-模型) | [B](#25-背压-backpressure) | [C](#22-csp-通信顺序进程) | [M](#24-ml-机器学习) | [R](#23-raft-共识算法)

**按类别**:
- **并发模型**: [Actor模型](#21-actor-模型), [CSP](#22-csp-通信顺序进程), [背压](#25-背压-backpressure)
- **分布式系统**: [Raft](#23-raft-共识算法)
- **机器学习**: [ML](#24-ml-机器学习)

---

## 📝 术语详解

### 2.1 Actor 模型

**定义**: 消息传递并发模型，每个Actor是独立的计算单元。

**核心概念**:
- 独立状态：每个Actor维护自己的状态
- 异步通信：通过消息传递进行通信
- 并发执行：多个Actor可以并发运行

**应用场景**:
- 高并发系统
- 分布式计算
- 实时处理

**相关文档**: [并发模型](./concurrency/)  
**代码实现**: `src/parallel_concurrent_models.rs`

---

### 2.2 CSP (通信顺序进程)

**定义**: Communicating Sequential Processes，通信顺序进程模型。

**核心概念**:
- Channel通信：通过channel进行数据传递
- 进程同步：支持同步和异步模式
- Golang风格：类似于Go语言的并发模型

**特点**:
- 简单易用
- 类型安全
- 高性能

**相关文档**: [并发模型](./concurrency/)  
**Rust实现**: `tokio::sync::mpsc`

---

### 2.3 Raft (共识算法)

**定义**: 分布式共识算法，用于实现分布式系统的一致性。

**核心概念**:
- Leader选举：选举一个Leader节点
- 日志复制：Leader将日志复制到Follower
- 安全性保证：确保数据一致性

**优势**:
- 易于理解和实现
- 强一致性保证
- 高可用性

**应用场景**:
- 分布式数据库
- 配置中心
- 分布式锁

**相关文档**: [Raft共识算法](./distributed/raft-consensus-comprehensive.md)  
**代码实现**: `src/distributed_models.rs`

---

### 2.4 ML (机器学习)

**定义**: Machine Learning，机器学习，通过数据训练模型以实现预测和决策。

**相关技术**:
- 深度学习 (Deep Learning)
- 自然语言处理 (NLP)
- 计算机视觉 (CV)
- 强化学习 (RL)

**Rust集成**:
- **tch-rs**: PyTorch绑定
- **tract**: ONNX推理引擎
- **burn**: 纯Rust深度学习框架

**应用场景**:
- 图像识别
- 文本分析
- 推荐系统
- 异常检测

**相关文档**: [机器学习集成](./guides/machine-learning.md)  
**代码实现**: `src/ml_models.rs`

---

### 2.5 背压 (Backpressure)

**定义**: 流量控制机制，防止生产者速度超过消费者处理能力。

**核心概念**:
- 流量控制：限制数据流速
- 缓冲管理：合理使用缓冲区
- 反馈机制：消费者向生产者反馈压力

**实现方式**:
- 有界channel：`tokio::sync::mpsc::channel(capacity)`
- 信号量：`tokio::sync::Semaphore`
- 自适应策略：动态调整缓冲区大小

**应用场景**:
- 异步数据流
- 网络服务
- 消息队列
- 实时处理

**相关文档**: [背压控制模型](./concurrency/backpressure-models.md)  
**示例代码**: `examples/async_backpressure_demo.rs`

---

## 🔍 延伸阅读

### 文档资源

- [主索引](./00_MASTER_INDEX.md) - 完整文档导航
- [README](./README.md) - 文档中心首页
- [FAQ](./FAQ.md) - 常见问题解答
- [项目概览](./OVERVIEW.md) - 项目全貌

### 技术主题

- [并发模型](./concurrency/) - 并发编程深度解析
- [分布式系统](./distributed/) - 分布式算法实现
- [架构设计](./architecture/) - 软件架构模式
- [形式化方法](./formal/) - 形式化验证技术

---

**文档版本**: 1.1  
**Rust 版本**: 1.90.0 (const API稳定、LLD链接器优化)  
**最后更新**: 2025年10月27日  
**维护者**: C12 Model Team  
**反馈**: [提交 Issue](https://github.com/rust-lang/rust-lang/issues)

---

> **提示**: 本术语表持续更新中，如需添加新术语，请 [提交 Issue](https://github.com/rust-lang/rust-lang/issues)。
