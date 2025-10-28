# Crates知识图谱

**版本**: 2.0  
**日期**: 2025年10月28日  
**状态**: ✅ 完整

---

## 📋 目录

- [Crates知识图谱](#crates知识图谱)
  - [📋 目录](#-目录)
  - [🌐 Crate依赖全景](#-crate依赖全景)
    - [完整依赖关系](#完整依赖关系)
    - [层次结构](#层次结构)
  - [🔗 功能关系图](#-功能关系图)
    - [核心功能连接](#核心功能连接)
  - [📊 数据流图](#-数据流图)
    - [请求处理流程](#请求处理流程)

---

## 🌐 Crate依赖全景

### 1.1 完整依赖关系

```mermaid
graph TB
    subgraph "应用层"
        APP[Your Application]
    end
    
    subgraph "协议层"
        OTLP[otlp crate<br/>OTLP协议实现]
    end
    
    subgraph "可靠性层"
        REL[reliability crate<br/>熔断/重试/限流]
    end
    
    subgraph "模型层"
        MODEL[model crate<br/>数据模型/状态机]
    end
    
    subgraph "基础层"
        LIB[libraries crate<br/>对象池/缓存/工具]
    end
    
    subgraph "外部依赖"
        TOKIO[tokio<br/>异步运行时]
        OT[opentelemetry<br/>OTel标准]
        TONIC[tonic<br/>gRPC]
    end
    
    APP --> OTLP
    OTLP --> REL
    OTLP --> OT
    OTLP --> TONIC
    REL --> MODEL
    REL --> TOKIO
    MODEL --> LIB
    LIB --> TOKIO
    
    style APP fill:#f9f,stroke:#333,stroke-width:3px
    style OTLP fill:#bbf,stroke:#333,stroke-width:2px
    style REL fill:#bfb,stroke:#333,stroke-width:2px
    style MODEL fill:#fbf,stroke:#333,stroke-width:2px
    style LIB fill:#ffb,stroke:#333,stroke-width:2px
```

### 1.2 依赖层次

```
Layer 4: 应用层
  └─ Your Application

Layer 3: 协议层
  └─ otlp (OTLP实现)

Layer 2: 可靠性层
  └─ reliability (容错机制)

Layer 1: 模型层
  └─ model (数据模型)

Layer 0: 基础层
  └─ libraries (基础工具)

External: 外部依赖
  ├─ tokio (异步运行时)
  ├─ opentelemetry (OTel标准)
  └─ tonic (gRPC框架)
```

---

## 🔗 功能关系图

### 2.1 核心功能映射

```mermaid
graph LR
    subgraph "otlp功能"
        T[Trace追踪]
        M[Metrics指标]
        L[Logs日志]
        E[Export导出]
    end
    
    subgraph "reliability功能"
        CB[CircuitBreaker<br/>熔断器]
        RT[Retry<br/>重试]
        RL[RateLimit<br/>限流]
        BH[Bulkhead<br/>隔离]
    end
    
    subgraph "model功能"
        SM[StateMachine<br/>状态机]
        AC[Actor<br/>并发模型]
        FM[Formal<br/>形式化]
    end
    
    subgraph "libraries功能"
        POOL[ObjectPool<br/>对象池]
        CACHE[Cache<br/>缓存]
        UTIL[Utils<br/>工具]
    end
    
    T --> CB
    M --> RL
    E --> RT
    
    CB --> SM
    RT --> SM
    RL --> AC
    
    SM --> POOL
    AC --> POOL
    CACHE --> UTIL
    
    style T fill:#bbf
    style CB fill:#bfb
    style SM fill:#fbf
    style POOL fill:#ffb
```

### 2.2 功能组合推荐

```
组合1: 分布式追踪
otlp.Trace + reliability.CircuitBreaker + libraries.ObjectPool
效果: 可靠的分布式追踪

组合2: 高可用服务
reliability.* + model.StateMachine + otlp.Metrics
效果: 高可用微服务

组合3: 高性能系统
libraries.ObjectPool + libraries.Cache + otlp.Metrics
效果: 高性能监控
```

---

## 📊 数据流图

### 3.1 请求处理流程

```mermaid
sequenceDiagram
    participant App as Application
    participant OTLP as otlp
    participant REL as reliability
    participant MODEL as model
    participant LIB as libraries
    participant Collector as OTLP Collector
    
    App->>OTLP: 1. 创建Span
    OTLP->>LIB: 2. 从对象池获取
    LIB-->>OTLP: 3. 返回Span对象
    
    App->>REL: 4. 执行业务逻辑(with熔断)
    REL->>MODEL: 5. 检查状态机
    MODEL-->>REL: 6. 允许执行
    
    REL-->>App: 7. 执行成功
    
    App->>OTLP: 8. 结束Span
    OTLP->>REL: 9. 批量导出(with重试)
    REL->>Collector: 10. 发送数据
    Collector-->>REL: 11. 确认接收
    
    OTLP->>LIB: 12. 归还对象到池
```

### 3.2 错误处理流程

```mermaid
graph TD
    START[请求开始]
    
    START --> OTLP_START[otlp: 创建Span]
    OTLP_START --> REL_CHECK{reliability: 熔断检查}
    
    REL_CHECK -->|开路| RETURN_ERROR[快速失败]
    REL_CHECK -->|闭路| MODEL_CHECK{model: 状态检查}
    
    MODEL_CHECK -->|无效| RETURN_ERROR
    MODEL_CHECK -->|有效| EXEC[执行业务]
    
    EXEC -->|成功| OTLP_END[otlp: 结束Span]
    EXEC -->|失败| REL_RETRY{reliability: 重试?}
    
    REL_RETRY -->|是| EXEC
    REL_RETRY -->|否| OTLP_ERROR[otlp: 记录错误]
    
    OTLP_END --> LIB_RETURN[libraries: 归还资源]
    OTLP_ERROR --> LIB_RETURN
    RETURN_ERROR --> LIB_RETURN
    
    LIB_RETURN --> END[请求结束]
    
    style OTLP_START fill:#bbf
    style REL_CHECK fill:#bfb
    style MODEL_CHECK fill:#fbf
    style LIB_RETURN fill:#ffb
```

---

## 🔧 核心概念

### 4.1 Crate核心概念列表

```
otlp (10个核心概念):
├─ Tracer - 追踪器
├─ Span - 跨度
├─ SpanContext - 上下文
├─ Exporter - 导出器
├─ BatchProcessor - 批处理器
├─ Resource - 资源
├─ Attributes - 属性
├─ Events - 事件
├─ Links - 链接
└─ Status - 状态

reliability (8个核心概念):
├─ CircuitBreaker - 熔断器
├─ RetryPolicy - 重试策略
├─ RateLimiter - 限流器
├─ Bulkhead - 隔离舱
├─ Timeout - 超时
├─ Fallback - 降级
├─ HealthCheck - 健康检查
└─ Backpressure - 背压

model (6个核心概念):
├─ StateMachine - 状态机
├─ Actor - Actor模型
├─ CSP - CSP模型
├─ STM - STM模型
├─ RateLimitAlgorithm - 限流算法
└─ FormalModel - 形式化模型

libraries (5个核心概念):
├─ ObjectPool - 对象池
├─ Cache - 缓存
├─ MetricsCollector - 指标采集
├─ Lock - 锁
└─ Utils - 工具函数
```

### 4.2 概念关系网络

```
追踪链路:
Tracer → Span → SpanContext → Exporter → Collector

可靠性链:
Request → CircuitBreaker → RateLimiter → Retry → Response

状态管理链:
Event → StateMachine → State → Transition → NewState

资源管理链:
Request → ObjectPool → Resource → Process → Return
```

---

## 📊 使用决策树

```mermaid
graph TD
    START{需要什么?}
    
    START -->|追踪| USE_OTLP[使用 otlp]
    START -->|容错| USE_REL[使用 reliability]
    START -->|状态管理| USE_MODEL[使用 model]
    START -->|性能优化| USE_LIB[使用 libraries]
    
    USE_OTLP --> Q1{需要可靠性?}
    Q1 -->|是| ADD_REL[+ reliability]
    Q1 -->|否| DONE1[完成]
    ADD_REL --> DONE1
    
    USE_REL --> Q2{需要追踪?}
    Q2 -->|是| ADD_OTLP[+ otlp]
    Q2 -->|否| DONE2[完成]
    ADD_OTLP --> DONE2
    
    USE_MODEL --> Q3{需要容错?}
    Q3 -->|是| ADD_REL2[+ reliability]
    Q3 -->|否| DONE3[完成]
    ADD_REL2 --> DONE3
    
    USE_LIB --> Q4{需要追踪?}
    Q4 -->|是| ADD_OTLP2[+ otlp]
    Q4 -->|否| DONE4[完成]
    ADD_OTLP2 --> DONE4
    
    style START fill:#f9f
    style USE_OTLP fill:#bbf
    style USE_REL fill:#bfb
    style USE_MODEL fill:#fbf
    style USE_LIB fill:#ffb
```

---

## 🚀 学习路径

```
新手路径 (推荐):
Step 1: libraries (1天)
  └─ 学习对象池和缓存

Step 2: otlp (1周)
  └─ 学习OTLP基础

Step 3: reliability (3天)
  └─ 学习容错机制

Step 4: model (1周)
  └─ 学习状态管理

进阶路径:
Step 1: otlp + reliability (2周)
  └─ 直接学习核心组合

Step 2: model + libraries (1周)
  └─ 深入理解底层

专家路径:
└─ 同时学习全部 (1月)
    └─ 深入源码和原理
```

---

## 🔗 相关资源

- [核心概念](./CONCEPTS.md) - Crate详细说明
- [对比矩阵](./COMPARISON_MATRIX.md) - Crate对比
- [快速入门](../01_GETTING_STARTED/) - 开始使用

---

**版本**: 2.0  
**创建日期**: 2025-10-28  
**最后更新**: 2025-10-28

---

> **💡 学习提示**: 按照Layer 0 → Layer 3的顺序学习，从基础到高级，循序渐进。新手建议从libraries开始。
