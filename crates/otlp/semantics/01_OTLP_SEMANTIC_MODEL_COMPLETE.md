# OTLP语义模型完整定义

> **版本**: 1.0  
> **日期**: 2025年10月17日  
> **基于**: OpenTelemetry 1.x 规范  
> **状态**: ✅ 完整版

---

## 目录

- [OTLP语义模型完整定义](#otlp语义模型完整定义)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 OTLP四支柱架构](#11-otlp四支柱架构)
      - [1.1.1 四支柱的定义](#111-四支柱的定义)
      - [1.1.2 四支柱的协同](#112-四支柱的协同)
    - [1.2 语义模型的重要性](#12-语义模型的重要性)
      - [1.2.1 为什么需要语义模型](#121-为什么需要语义模型)
      - [1.2.2 语义模型的层次](#122-语义模型的层次)
    - [1.3 本文档的组织结构](#13-本文档的组织结构)
  - [2. Resource语义模型](#2-resource语义模型)
    - [2.1 Resource定义与作用](#21-resource定义与作用)
      - [2.1.1 Resource的概念](#211-resource的概念)
      - [2.1.2 Resource的作用](#212-resource的作用)
    - [2.2 标准Resource属性](#22-标准resource属性)
      - [2.2.1 Service属性](#221-service属性)
      - [2.2.2 Deployment属性](#222-deployment属性)
      - [2.2.3 K8s属性](#223-k8s属性)
      - [2.2.4 Cloud属性](#224-cloud属性)
      - [2.2.5 Host属性](#225-host属性)
      - [2.2.6 Process属性](#226-process属性)
    - [2.3 Resource最佳实践](#23-resource最佳实践)
      - [2.3.1 Resource设计原则](#231-resource设计原则)
      - [2.3.2 跨信号一致性](#232-跨信号一致性)
  - [3. Context语义模型](#3-context语义模型)
    - [3.1 TraceContext](#31-tracecontext)
      - [3.1.1 TraceContext组成](#311-tracecontext组成)
      - [3.1.2 TraceContext传播](#312-tracecontext传播)
    - [3.2 Baggage](#32-baggage)
      - [3.2.1 Baggage特性](#321-baggage特性)
    - [3.3 TraceState](#33-tracestate)
      - [3.3.1 TraceState格式](#331-tracestate格式)
  - [4. Traces语义模型](#4-traces语义模型)
    - [4.1 Span完整定义](#41-span完整定义)
      - [4.1.1 Span数据结构](#411-span数据结构)
      - [4.1.2 Span生命周期](#412-span生命周期)
    - [4.2 SpanKind语义](#42-spankind语义)
      - [4.2.1 五种SpanKind](#421-五种spankind)
      - [4.2.2 SpanKind使用示例](#422-spankind使用示例)
    - [4.3 Span属性与事件](#43-span属性与事件)
      - [4.3.1 Span属性](#431-span属性)
      - [4.3.2 Span事件](#432-span事件)
    - [4.4 Span状态与链接](#44-span状态与链接)
      - [4.4.1 Span状态](#441-span状态)
      - [4.4.2 Span链接](#442-span链接)
  - [5. Metrics语义模型](#5-metrics语义模型)
    - [5.1 Metric类型详解](#51-metric类型详解)
      - [5.1.1 Counter（计数器）](#511-counter计数器)
      - [5.1.2 UpDownCounter（可增减计数器）](#512-updowncounter可增减计数器)
      - [5.1.3 Histogram（直方图）](#513-histogram直方图)
      - [5.1.4 Gauge（仪表）](#514-gauge仪表)
      - [5.1.5 ExponentialHistogram（指数直方图）](#515-exponentialhistogram指数直方图)
    - [5.2 聚合语义](#52-聚合语义)
      - [5.2.1 聚合时间性](#521-聚合时间性)
      - [5.2.2 聚合维度](#522-聚合维度)
    - [5.3 Exemplar机制](#53-exemplar机制)
      - [5.3.1 Exemplar结构](#531-exemplar结构)
      - [5.3.2 Exemplar使用](#532-exemplar使用)
  - [6. Logs语义模型](#6-logs语义模型)
    - [6.1 LogRecord结构](#61-logrecord结构)
    - [6.2 Severity语义](#62-severity语义)
    - [6.3 跨信号关联](#63-跨信号关联)
  - [7. Profiles语义模型](#7-profiles语义模型)
    - [7.1 Profile数据结构](#71-profile数据结构)
    - [7.2 采样策略](#72-采样策略)
    - [7.3 与Trace关联](#73-与trace关联)
  - [8. 语义一致性保证](#8-语义一致性保证)
    - [8.1 命名规范](#81-命名规范)
    - [8.2 单位规范](#82-单位规范)
    - [8.3 属性一致性](#83-属性一致性)
  - [9. 参考文献](#9-参考文献)

---

## 🎯 概述

### 1.1 OTLP四支柱架构

OpenTelemetry定义了可观测性的四个支柱：

```text
┌─────────────────────────────────────────────────┐
│           OTLP 四支柱完整架构                    │
├─────────────────────────────────────────────────┤
│                                                 │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐     │
│  │  Traces  │  │ Metrics  │  │   Logs   │     │
│  │          │  │          │  │          │     │
│  │ • Span   │  │ • Counter│  │ • Record │     │
│  │ • Event  │  │ • Gauge  │  │ • Severity│    │
│  │ • Link   │  │ • Histo  │  │ • Body   │     │
│  └──────────┘  └──────────┘  └──────────┘     │
│                                                 │
│              ┌──────────────┐                  │
│              │   Profiles   │                  │
│              │              │                  │
│              │ • CPU        │                  │
│              │ • Memory     │                  │
│              │ • Goroutine  │                  │
│              └──────────────┘                  │
│                                                 │
│  ─────────────  共享基础  ─────────────        │
│                                                 │
│  ┌──────────────┐    ┌──────────────┐         │
│  │   Resource   │    │   Context    │         │
│  │              │    │              │         │
│  │ • service.*  │    │ • TraceId    │         │
│  │ • host.*     │    │ • SpanId     │         │
│  │ • k8s.*      │    │ • Baggage    │         │
│  └──────────────┘    └──────────────┘         │
│                                                 │
└─────────────────────────────────────────────────┘
```

#### 1.1.1 四支柱的定义

**Traces（追踪）**:

- **定义**: 记录请求在分布式系统中的完整路径
- **核心**: Span（操作片段）、因果关系、延迟分析
- **典型场景**: 微服务调用链追踪、性能瓶颈定位

**Metrics（指标）**:

- **定义**: 数值化的性能和业务指标
- **核心**: 时间序列、聚合计算、告警阈值
- **典型场景**: CPU/内存监控、QPS统计、业务KPI

**Logs（日志）**:

- **定义**: 系统运行时的事件记录
- **核心**: 结构化、上下文关联、等级分类
- **典型场景**: 错误排查、审计、调试

**Profiles（性能剖析）**:

- **定义**: 程序运行时的资源消耗详情
- **核心**: 调用栈、采样频率、热点分析
- **典型场景**: CPU/内存性能优化、资源泄漏排查

#### 1.1.2 四支柱的协同

```text
场景：用户请求延迟异常

┌─ Metrics ─┐
│ P99 > 1s  │ ──→ 触发告警
└───────────┘
     ↓
┌─ Traces ──┐
│ 找到慢请求 │ ──→ 定位具体Span
└───────────┘
     ↓
┌─ Logs ────┐
│ 查看错误日志│ ──→ 发现异常堆栈
└───────────┘
     ↓
┌─ Profiles ┐
│ 分析CPU热点│ ──→ 找到性能瓶颈代码
└───────────┘
```

### 1.2 语义模型的重要性

#### 1.2.1 为什么需要语义模型

**统一理解**:

- 不同团队、不同系统对数据的理解一致
- 避免"同名不同义"、"同义不同名"

**跨系统互操作**:

- 数据可以在不同后端（Jaeger、Prometheus、Elastic等）之间迁移
- 避免供应商锁定

**自动化分析**:

- 语义明确的数据可以被自动化工具理解和处理
- 支持智能告警、根因分析等高级功能

**成本优化**:

- 标准化的语义减少数据冗余
- 降低存储和传输成本

#### 1.2.2 语义模型的层次

```text
┌───────────────────────────────────────┐
│       L3: 领域语义约定                 │
│   (HTTP, DB, Messaging, CI/CD等)      │
├───────────────────────────────────────┤
│       L2: 通用属性语义                 │
│   (net.*, host.*, cloud.* 等)        │
├───────────────────────────────────────┤
│       L1: 基础数据结构                 │
│   (Resource, Span, Metric等)         │
└───────────────────────────────────────┘
```

### 1.3 本文档的组织结构

本文档按照以下顺序组织：

1. **共享基础** (Resource、Context) - 所有信号共用
2. **四个支柱** (Traces、Metrics、Logs、Profiles) - 按重要性排序
3. **语义一致性** - 跨信号关联和验证

每个部分包含：

- 完整的语义定义
- 实际代码示例
- 最佳实践建议
- 常见陷阱和解决方案

---

## 📝 Resource语义模型

### 2.1 Resource定义与作用

#### 2.1.1 Resource的概念

**定义**: Resource描述了生成遥测数据的实体（Entity）。

**关键特性**:

- **不可变**: Resource在应用生命周期内通常不变
- **层次性**: 可以包含多层资源信息（进程→容器→Pod→节点→集群）
- **共享性**: 同一Resource可以被多种信号共享

**举例说明**:

```yaml
# 一个在Kubernetes上运行的Node.js服务
service.name: "payment-api"
service.version: "1.2.3"
deployment.environment: "production"
k8s.namespace.name: "backend"
k8s.pod.name: "payment-api-7d9f8c-xyz"
k8s.container.name: "app"
host.name: "node-12"
cloud.provider: "aws"
cloud.region: "us-west-2"
```

#### 2.1.2 Resource的作用

**1. 唯一标识**:

```text
Resource能够唯一标识遥测数据的来源

service.name + service.instance.id + deployment.environment
  ↓
payment-api@pod-xyz@production
```

**2. 多维度分析**:

```text
按不同维度聚合和分析数据：
- 按服务: service.name
- 按环境: deployment.environment
- 按K8s: k8s.namespace.name, k8s.pod.name
- 按云: cloud.provider, cloud.region
```

**3. 成本归因**:

```text
根据Resource属性进行成本分配：
- 团队: team.name
- 项目: project.name
- 成本中心: cost.center
```

### 2.2 标准Resource属性

#### 2.2.1 Service属性

**service.* 命名空间**:

| 属性 | 类型 | 必需 | 说明 | 示例 |
|------|------|------|------|------|
| `service.name` | string | ✅ | 服务名称，逻辑标识符 | `payment-api` |
| `service.namespace` | string | ❌ | 服务命名空间，区分不同团队 | `ecommerce` |
| `service.instance.id` | string | ❌ | 服务实例ID，物理标识符 | `pod-abc-123` |
| `service.version` | string | ❌ | 服务版本 | `1.2.3` |

**最佳实践**:

```yaml
# ✅ 推荐：清晰的服务标识
service.name: "payment-api"
service.namespace: "ecommerce.backend"
service.instance.id: "payment-api-7d9f8c-xyz"
service.version: "1.2.3"

# ❌ 避免：含糊不清的命名
service.name: "api"  # 太泛化
service.name: "payment-api-prod-us-west-2-1"  # 包含了环境信息
```

#### 2.2.2 Deployment属性

**deployment.* 命名空间**:

| 属性 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `deployment.environment` | string | 部署环境 | `production`, `staging`, `dev` |
| `deployment.name` | string | 部署名称 | `payment-api-prod` |

#### 2.2.3 K8s属性

**k8s.* 命名空间**:

| 属性 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `k8s.namespace.name` | string | K8s命名空间 | `backend` |
| `k8s.pod.name` | string | Pod名称 | `payment-api-7d9f8c-xyz` |
| `k8s.pod.uid` | string | Pod UID | `a1b2c3d4-...` |
| `k8s.container.name` | string | 容器名称 | `app` |
| `k8s.replicaset.name` | string | ReplicaSet名称 | `payment-api-7d9f8c` |
| `k8s.deployment.name` | string | Deployment名称 | `payment-api` |
| `k8s.statefulset.name` | string | StatefulSet名称 | `redis-cluster` |
| `k8s.daemonset.name` | string | DaemonSet名称 | `log-agent` |
| `k8s.job.name` | string | Job名称 | `data-migration` |
| `k8s.cronjob.name` | string | CronJob名称 | `daily-backup` |
| `k8s.node.name` | string | 节点名称 | `node-12` |
| `k8s.node.uid` | string | 节点UID | `x1y2z3...` |
| `k8s.cluster.name` | string | 集群名称 | `prod-us-west-2` |

#### 2.2.4 Cloud属性

**cloud.* 命名空间**:

| 属性 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `cloud.provider` | string | 云提供商 | `aws`, `azure`, `gcp` |
| `cloud.account.id` | string | 账号ID | `123456789012` |
| `cloud.region` | string | 区域 | `us-west-2` |
| `cloud.availability_zone` | string | 可用区 | `us-west-2a` |
| `cloud.platform` | string | 云平台 | `aws_eks`, `azure_aks` |

#### 2.2.5 Host属性

**host.* 命名空间**:

| 属性 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `host.name` | string | 主机名 | `node-12` |
| `host.id` | string | 主机ID | `i-1234567890abcdef0` |
| `host.type` | string | 主机类型 | `m5.xlarge` |
| `host.image.name` | string | 镜像名称 | `ubuntu-20.04` |
| `host.image.id` | string | 镜像ID | `ami-12345678` |

#### 2.2.6 Process属性

**process.* 命名空间**:

| 属性 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `process.pid` | int | 进程ID | `1234` |
| `process.executable.name` | string | 可执行文件名 | `node` |
| `process.executable.path` | string | 可执行文件路径 | `/usr/bin/node` |
| `process.command` | string | 命令 | `node app.js` |
| `process.command_line` | string | 完整命令行 | `node app.js --port 3000` |
| `process.owner` | string | 进程所有者 | `appuser` |
| `process.runtime.name` | string | 运行时名称 | `nodejs` |
| `process.runtime.version` | string | 运行时版本 | `18.12.0` |

### 2.3 Resource最佳实践

#### 2.3.1 Resource设计原则

**1. 最小必需原则**:

```yaml
# ✅ 推荐：只包含必需的Resource属性
service.name: "payment-api"
deployment.environment: "production"
k8s.pod.name: "payment-api-xyz"

# ❌ 避免：包含过多冗余信息
service.name: "payment-api"
service.full_name: "payment-api-production"  # 冗余
deployment.environment: "production"
deployment.env: "prod"  # 冗余
```

**2. 层次一致性**:

```yaml
# ✅ 推荐：层次关系明确
service.name: "payment-api"
k8s.deployment.name: "payment-api"
k8s.replicaset.name: "payment-api-7d9f8c"
k8s.pod.name: "payment-api-7d9f8c-xyz"

# ❌ 避免：层次关系混乱
service.name: "payment-api"
k8s.deployment.name: "payments"  # 不一致
```

**3. 命名规范**:

```yaml
# ✅ 推荐：使用标准命名
service.name: "payment-api"
deployment.environment: "production"

# ❌ 避免：自定义命名
app.name: "payment-api"  # 应使用 service.name
env: "production"  # 应使用 deployment.environment
```

#### 2.3.2 跨信号一致性

**确保所有信号使用相同的Resource**:

```rust
// ✅ 推荐：统一Resource定义
let resource = Resource::new(vec![
    KeyValue::new("service.name", "payment-api"),
    KeyValue::new("service.version", "1.2.3"),
    KeyValue::new("deployment.environment", "production"),
]);

// Tracer使用相同Resource
let tracer = TracerProvider::builder()
    .with_resource(resource.clone())
    .build();

// Meter使用相同Resource
let meter = MeterProvider::builder()
    .with_resource(resource.clone())
    .build();

// Logger使用相同Resource
let logger = LoggerProvider::builder()
    .with_resource(resource)
    .build();
```

---

## 💡 Context语义模型

### 3.1 TraceContext

**TraceContext**是分布式追踪的核心，用于在服务之间传递追踪信息。

#### 3.1.1 TraceContext组成

```text
┌─────────────────────────────────┐
│        TraceContext             │
├─────────────────────────────────┤
│ • TraceId    (16 bytes)         │
│ • SpanId     (8 bytes)          │
│ • TraceFlags (1 byte)           │
└─────────────────────────────────┘
```

**TraceId**:

- **长度**: 16字节（128位）
- **格式**: 十六进制字符串
- **示例**: `4bf92f3577b34da6a3ce929d0e0e4736`
- **作用**: 唯一标识一条完整的追踪链

**SpanId**:

- **长度**: 8字节（64位）
- **格式**: 十六进制字符串
- **示例**: `00f067aa0ba902b7`
- **作用**: 唯一标识追踪链中的一个Span

**TraceFlags**:

- **长度**: 1字节
- **格式**: 位掩码
- **采样标志**: `0x01` = 已采样, `0x00` = 未采样
- **作用**: 控制采样行为

#### 3.1.2 TraceContext传播

**HTTP Header传播**:

```http
traceparent: 00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01
             └┬┘ └──────────────────────────────┘ └──────────────┘ └┬┘
              │                │                          │          │
           版本            TraceId                    SpanId      Flags
```

**gRPC Metadata传播**:

```protobuf
metadata {
  key: "traceparent"
  value: "00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01"
}
```

### 3.2 Baggage

**Baggage**用于在追踪链中传递业务上下文信息。

#### 3.2.1 Baggage特性

**键值对存储**:

```text
user_id=12345,tenant_id=abc,feature_flag=new_checkout
```

**跨服务传播**:

```text
Service A → Service B → Service C
    ↓           ↓           ↓
Baggage    Baggage    Baggage
自动传播    自动传播    自动传播
```

**注意事项**:

- ⚠️ Baggage会增加网络开销
- ⚠️ 敏感信息不应放入Baggage
- ⚠️ 建议总大小 < 8KB

### 3.3 TraceState

**TraceState**用于供应商特定的追踪信息传递。

#### 3.3.1 TraceState格式

```http
tracestate: vendor1=value1,vendor2=value2
```

**示例**:

```http
tracestate: congo=t61rcWkgMzE,rojo=00f067aa0ba902b7
```

---

## 🔧 Traces语义模型

### 4.1 Span完整定义

**Span**是Traces的基本单元，表示一个操作或工作单元。

#### 4.1.1 Span数据结构

```proto
message Span {
  // 追踪上下文
  bytes trace_id = 1;           // 16 bytes
  bytes span_id = 2;            // 8 bytes
  string trace_state = 3;
  bytes parent_span_id = 4;     // 8 bytes
  
  // 基本信息
  string name = 5;
  SpanKind kind = 6;
  uint64 start_time_unix_nano = 7;
  uint64 end_time_unix_nano = 8;
  
  // 属性
  repeated KeyValue attributes = 9;
  uint32 dropped_attributes_count = 10;
  
  // 事件
  repeated Event events = 11;
  uint32 dropped_events_count = 12;
  
  // 链接
  repeated Link links = 13;
  uint32 dropped_links_count = 14;
  
  // 状态
  Status status = 15;
}
```

#### 4.1.2 Span生命周期

```text
创建 → 激活 → 记录事件 → 结束 → 导出

┌──────┐  ┌──────┐  ┌──────┐  ┌──────┐  ┌──────┐
│Create│→ │Start │→ │Events│→ │ End  │→ │Export│
└──────┘  └──────┘  └──────┘  └──────┘  └──────┘
   ↓         ↓         ↓         ↓         ↓
 设置名称   记录开始   添加属性   记录结束   发送到后端
 设置Kind   时间戳    添加事件   时间戳
```

### 4.2 SpanKind语义

**SpanKind**定义了Span在追踪链中的角色。

#### 4.2.1 五种SpanKind

| Kind | 说明 | 场景 | 示例 |
|------|------|------|------|
| `INTERNAL` | 内部操作 | 函数调用、本地计算 | `processPayment()` |
| `SERVER` | 服务端接收请求 | HTTP服务器、gRPC服务器 | `POST /api/payment` |
| `CLIENT` | 客户端发起请求 | HTTP客户端、gRPC客户端 | `GET https://api.bank.com` |
| `PRODUCER` | 消息生产者 | Kafka Producer、RabbitMQ发送 | `publish to topic` |
| `CONSUMER` | 消息消费者 | Kafka Consumer、RabbitMQ接收 | `consume from queue` |

#### 4.2.2 SpanKind使用示例

**场景1: HTTP调用链**:

```text
Service A (CLIENT) → Service B (SERVER)
    ↓                      ↓
Client Span           Server Span
span.kind=CLIENT      span.kind=SERVER
```

**场景2: 消息队列**:

```text
Producer (PRODUCER) → Queue → Consumer (CONSUMER)
    ↓                             ↓
Producer Span                Consumer Span
span.kind=PRODUCER           span.kind=CONSUMER
```

### 4.3 Span属性与事件

#### 4.3.1 Span属性

**属性类型**:

- `string`: 字符串值
- `int64`: 64位整数
- `double`: 双精度浮点数
- `bool`: 布尔值
- `array`: 数组（同类型元素）

**常用属性**:

```yaml
# HTTP属性
http.method: "POST"
http.url: "https://api.example.com/payment"
http.status_code: 200
http.request_content_length: 1024
http.response_content_length: 2048

# Database属性
db.system: "postgresql"
db.name: "orders"
db.statement: "SELECT * FROM orders WHERE id = $1"
db.operation: "SELECT"

# Messaging属性
messaging.system: "kafka"
messaging.destination: "orders-topic"
messaging.operation: "publish"
```

#### 4.3.2 Span事件

**Event结构**:

```proto
message Event {
  uint64 time_unix_nano = 1;
  string name = 2;
  repeated KeyValue attributes = 3;
  uint32 dropped_attributes_count = 4;
}
```

**事件示例**:

```rust
span.add_event(
    "cache_miss",
    vec![
        KeyValue::new("cache.key", "user:12345"),
        KeyValue::new("cache.ttl", 300),
    ],
);
```

### 4.4 Span状态与链接

#### 4.4.1 Span状态

```proto
enum StatusCode {
  UNSET = 0;  // 未设置（默认）
  OK = 1;     // 成功
  ERROR = 2;  // 错误
}

message Status {
  string message = 2;
  StatusCode code = 3;
}
```

**状态语义**:

- `UNSET`: 默认状态，表示未明确设置
- `OK`: 明确表示成功
- `ERROR`: 表示发生错误

#### 4.4.2 Span链接

**Link用于关联多个Span**:

```proto
message Link {
  bytes trace_id = 1;
  bytes span_id = 2;
  string trace_state = 3;
  repeated KeyValue attributes = 4;
  uint32 dropped_attributes_count = 5;
}
```

**链接场景**:

```text
异步批处理：
Request Span ──link──> Batch Process Span
                       ↓
                   Process Item 1 Span
                   Process Item 2 Span
                   Process Item 3 Span
```

---

## 📊 Metrics语义模型

### 5.1 Metric类型详解

#### 5.1.1 Counter（计数器）

**定义**: 单调递增的累积值

**特性**:

- 只能增加，不能减少
- 通常从0开始
- 查询时需要计算增量（rate）

**示例**:

```rust
let counter = meter.u64_counter("http.server.requests")
    .with_description("HTTP请求总数")
    .with_unit("{request}")
    .init();

counter.add(1, &[
    KeyValue::new("http.method", "GET"),
    KeyValue::new("http.status_code", 200),
]);
```

**查询示例**:

```promql
# 计算每秒请求数
rate(http_server_requests_total[5m])

# 按状态码分组
sum by (http_status_code) (rate(http_server_requests_total[5m]))
```

#### 5.1.2 UpDownCounter（可增减计数器）

**定义**: 可以增加或减少的累积值

**特性**:

- 可以增加或减少
- 当前值有意义

**示例**:

```rust
let active_requests = meter.i64_up_down_counter("http.server.active_requests")
    .with_description("活跃HTTP请求数")
    .with_unit("{request}")
    .init();

// 请求开始时+1
active_requests.add(1, &[]);

// 请求结束时-1
active_requests.add(-1, &[]);
```

#### 5.1.3 Histogram（直方图）

**定义**: 记录值的分布情况

**特性**:

- 自动计算分位数
- 桶边界可配置
- 适合延迟、大小等指标

**示例**:

```rust
let histogram = meter.f64_histogram("http.server.duration")
    .with_description("HTTP请求延迟")
    .with_unit("ms")
    .init();

histogram.record(123.45, &[
    KeyValue::new("http.method", "GET"),
    KeyValue::new("http.route", "/api/users"),
]);
```

**默认桶边界**:

```text
[0, 5, 10, 25, 50, 75, 100, 250, 500, 750, 1000, 2500, 5000, 7500, 10000]
```

#### 5.1.4 Gauge（仪表）

**定义**: 当前时刻的瞬时值

**特性**:

- 表示当前状态
- 可增可减
- 不保留历史

**示例**:

```rust
let gauge = meter.f64_observable_gauge("system.cpu.utilization")
    .with_description("CPU使用率")
    .with_unit("1")  // 单位1表示比例
    .with_callback(|observer| {
        let cpu_usage = get_cpu_usage();
        observer.observe(cpu_usage, &[]);
    })
    .init();
```

#### 5.1.5 ExponentialHistogram（指数直方图）

**定义**: 使用指数桶的直方图

**特性**:

- 自动调整桶边界
- 节省存储空间
- 适合大范围值

### 5.2 聚合语义

#### 5.2.1 聚合时间性

**Delta聚合**:

- 报告时间段内的增量
- 适合Counter
- 示例：过去1分钟新增请求数

**Cumulative聚合**:

- 报告从开始到现在的累积值
- 适合Counter
- 示例：进程启动以来的总请求数

#### 5.2.2 聚合维度

**时间聚合**:

```text
原始数据（1s）→ 聚合到1m → 聚合到1h → 聚合到1d
```

**空间聚合**:

```text
实例级别 → 服务级别 → 集群级别
```

### 5.3 Exemplar机制

**Exemplar**将Metrics和Traces关联起来。

#### 5.3.1 Exemplar结构

```proto
message Exemplar {
  repeated KeyValue filtered_attributes = 1;
  uint64 time_unix_nano = 2;
  oneof value {
    double as_double = 3;
    int64 as_int = 6;
  }
  bytes span_id = 4;
  bytes trace_id = 5;
}
```

#### 5.3.2 Exemplar使用

```rust
// 在记录Metric时关联Trace
histogram.record(
    duration_ms,
    &[KeyValue::new("http.route", "/api/payment")],
);
// Exemplar自动捕获当前的TraceId和SpanId
```

**查询示例**:

```text
看到P99延迟异常 → 点击Exemplar → 跳转到具体Trace
```

---

## 🚀 Logs语义模型

### 6.1 LogRecord结构

```proto
message LogRecord {
  uint64 time_unix_nano = 1;
  uint64 observed_time_unix_nano = 11;
  SeverityNumber severity_number = 2;
  string severity_text = 3;
  AnyValue body = 5;
  repeated KeyValue attributes = 6;
  uint32 dropped_attributes_count = 7;
  uint32 flags = 8;
  bytes trace_id = 9;
  bytes span_id = 10;
}
```

### 6.2 Severity语义

**Severity级别**:

| Number | Name | 说明 |
|--------|------|------|
| 1-4 | TRACE | 最详细的跟踪信息 |
| 5-8 | DEBUG | 调试信息 |
| 9-12 | INFO | 一般信息 |
| 13-16 | WARN | 警告信息 |
| 17-20 | ERROR | 错误信息 |
| 21-24 | FATAL | 致命错误 |

### 6.3 跨信号关联

**通过TraceId和SpanId关联**:

```text
Log → trace_id/span_id → Span → Trace → Metrics (via Exemplar)
```

**示例**:

```rust
log::error!(
    "Payment failed: {}",
    error,
    {
        trace_id = %current_span.trace_id(),
        span_id = %current_span.span_id(),
        user_id = user.id,
    }
);
```

---

## 🔍 Profiles语义模型

### 7.1 Profile数据结构

**Profile基于pprof格式**:

```proto
message Profile {
  repeated ValueType sample_type = 1;
  repeated Sample sample = 2;
  repeated Mapping mapping = 3;
  repeated Location location = 4;
  repeated Function function = 5;
  repeated string string_table = 6;
  int64 drop_frames = 7;
  int64 keep_frames = 8;
  int64 time_nanos = 9;
  int64 duration_nanos = 10;
  ValueType period_type = 11;
  int64 period = 12;
  repeated int64 comment = 13;
  int64 default_sample_type = 14;
}
```

### 7.2 采样策略

**CPU采样**:

- **频率**: 9-49 Hz（推荐19Hz）
- **开销**: < 5% CPU
- **适用**: 性能热点分析

**Memory采样**:

- **频率**: 按分配次数（如每128KB一次）
- **开销**: < 2% CPU
- **适用**: 内存泄漏排查

### 7.3 与Trace关联

**通过Resource和Attributes关联**:

```yaml
# Profile中的属性
profile.type: "cpu"
trace.id: "4bf92f3577b34da6a3ce929d0e0e4736"
span.id: "00f067aa0ba902b7"
```

---

## 💻 语义一致性保证

### 8.1 命名规范

**命名空间**:

```text
<namespace>.<component>.<attribute>

示例:
http.server.duration
db.client.connections
messaging.kafka.consumer.lag
```

### 8.2 单位规范

**标准单位**:

- 时间: `ms`, `s`, `min`, `h`
- 字节: `By`, `KiBy`, `MiBy`, `GiBy`
- 比例: `1` (0.0-1.0)
- 百分比: `%` (0-100)
- 计数: `{count}`, `{request}`, `{error}`

### 8.3 属性一致性

**跨信号使用相同的属性名**:

```yaml
# ✅ 在Span、Metric、Log中都使用相同的属性名
http.method: "GET"
http.route: "/api/users"
http.status_code: 200
```

---

## 📚 参考文献

1. [OpenTelemetry Specification](https://opentelemetry.io/docs/specs/)
2. [Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/)
3. [OTLP Protocol Specification](https://opentelemetry.io/docs/specs/otlp/)
4. [Profiles Specification](https://github.com/open-telemetry/opentelemetry-proto/tree/main/opentelemetry/proto/profiles)

---

**文档版本**: 1.0  
**最后更新**: 2025年10月17日  
**维护者**: OTLP Rust Team
