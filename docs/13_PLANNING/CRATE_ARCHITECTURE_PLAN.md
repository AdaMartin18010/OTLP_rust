# OTLP Rust 项目 - Crate 架构规划

**版本**: 1.0  
**规划日期**: 2025年10月26日  
**Rust 版本**: 1.90+  
**OpenTelemetry 版本**: 0.31.0  
**状态**: 🟢 活跃维护

> **简介**: Crate 架构规划 - 完整的 crate 分层设计、职责划分和实施计划。

---

## 📋 目录

- [OTLP Rust 项目 - Crate 架构规划](#otlp-rust-项目---crate-架构规划)
  - [📋 目录](#-目录)
  - [🏗️ 架构概览](#️-架构概览)
    - [设计原则](#设计原则)
    - [架构分层](#架构分层)
  - [📦 Crate 规划](#-crate-规划)
    - [1. 核心 Crates](#1-核心-crates)
      - [1.1 `otlp-core` (新建)](#11-otlp-core-新建)
      - [1.2 `otlp-proto` (新建)](#12-otlp-proto-新建)
      - [1.3 `otlp-transport` (新建)](#13-otlp-transport-新建)
    - [2. 功能 Crates](#2-功能-crates)
      - [2.1 `otlp` (重构)](#21-otlp-重构)
      - [2.2 `reliability` (增强)](#22-reliability-增强)
      - [2.3 `otlp-microservices` (新建，从 otlp 提取)](#23-otlp-microservices-新建从-otlp-提取)
    - [3. 整合与扩展 Crates](#3-整合与扩展-crates)
      - [3.1 `otlp-reliability-bridge` (新建)](#31-otlp-reliability-bridge-新建)
      - [3.2 `otlp-integrations` (新建)](#32-otlp-integrations-新建)
      - [3.3 `otlp-cli` (新建)](#33-otlp-cli-新建)
    - [4. 开发辅助 Crates](#4-开发辅助-crates)
      - [4.1 `otlp-examples` (新建，可选)](#41-otlp-examples-新建可选)
      - [4.2 `otlp-benchmarks` (新建，可选)](#42-otlp-benchmarks-新建可选)
  - [📊 依赖关系图](#-依赖关系图)
  - [📚 文档目录规划](#-文档目录规划)
    - [新的文档结构](#新的文档结构)
    - [文档迁移映射](#文档迁移映射)
    - [文档生成工具](#文档生成工具)
  - [🛣️ 迁移路线图](#️-迁移路线图)
    - [阶段 1: 核心拆分（第 1-2 周）](#阶段-1-核心拆分第-1-2-周)
    - [阶段 2: 主 Crate 重构（第 3-4 周）](#阶段-2-主-crate-重构第-3-4-周)
    - [阶段 3: 提取专项 Crates（第 5-6 周）](#阶段-3-提取专项-crates第-5-6-周)
    - [阶段 4: 整合层（第 7-8 周）](#阶段-4-整合层第-7-8-周)
    - [阶段 5: 工具和文档（第 9-10 周）](#阶段-5-工具和文档第-9-10-周)
    - [阶段 6: 发布准备（第 11-12 周）](#阶段-6-发布准备第-11-12-周)
  - [🎯 最佳实践](#-最佳实践)
    - [Crate 设计原则](#crate-设计原则)
    - [依赖管理](#依赖管理)
    - [特性标志策略](#特性标志策略)
    - [测试策略](#测试策略)
    - [文档规范](#文档规范)
    - [错误处理](#错误处理)
  - [📝 更新的工作区 Cargo.toml](#-更新的工作区-cargotoml)
  - [🚀 快速开始（新架构）](#-快速开始新架构)
    - [安装](#安装)
    - [基础使用](#基础使用)
    - [高级用法](#高级用法)
  - [📊 预期收益](#-预期收益)
    - [代码组织](#代码组织)
    - [依赖管理1](#依赖管理1)
    - [用户体验](#用户体验)
    - [维护性](#维护性)
  - [🤝 参与贡献](#-参与贡献)
  - [📄 许可证](#-许可证)

---

## 🏗️ 架构概览

### 设计原则

1. **关注点分离**: 每个 crate 有明确的职责边界
2. **最小依赖**: 核心 crate 保持轻量级
3. **OTLP 语义优先**: 以 OpenTelemetry 标准为核心语义
4. **渐进式增强**: 高级功能通过特性门控（feature flags）可选启用
5. **向后兼容**: 保持 API 稳定性，平滑迁移路径

### 架构分层

```text
┌─────────────────────────────────────────────────────────────┐
│                    应用层 (Applications)                     │
│           用户服务、监控系统、数据分析平台等                   │
└─────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────┐
│                整合层 (Integration Layer)                    │
│  ┌──────────────────┐  ┌─────────────────────────────────┐  │
│  │ otlp-integrations│  │  otlp-reliability-bridge        │  │
│  │ • K8s/Prometheus │  │  • 统一可观测性 + 可靠性          │  │
│  │ • Grafana/Jaeger │  │  • 错误与追踪关联                │  │
│  └──────────────────┘  └─────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────┐
│                   功能层 (Feature Layer)                     │
│  ┌─────────────┐  ┌──────────────┐  ┌──────────────────┐    │
│  │   otlp      │  │ reliability  │  │ otlp-microservices│   │
│  │ • 完整实现   │  │ • 容错机制    │  │ • 服务发现        │   │
│  │ • 性能优化   │  │ • 错误处理    │  │ • 负载均衡        │   │
│  │ • 监控集成   │  │ • 自愈能力    │  │ • 熔断重试        │   │
│  └─────────────┘  └──────────────┘  └──────────────────┘    │
└─────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────┐
│                   核心层 (Core Layer)                        │
│  ┌─────────────┐  ┌──────────────┐  ┌──────────────────┐    │
│  │ otlp-core   │  │ otlp-proto   │  │ otlp-transport   │    │
│  │ • 数据模型   │  │ • Protobuf   │  │ • gRPC/HTTP      │    │
│  │ • 类型定义   │  │ • 编解码     │  │ • 连接管理        │    │
│  │ • 验证逻辑   │  │ • 序列化     │  │ • TLS/压缩        │    │
│  └─────────────┘  └──────────────┘  └──────────────────┘    │
└─────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────┐
│                   基础层 (Foundation)                        │
│            opentelemetry 0.31.0 + Rust Std                  │
└─────────────────────────────────────────────────────────────┘
```

---

## 📦 Crate 规划

### 1. 核心 Crates

#### 1.1 `otlp-core` (新建)

**职责**: OTLP 核心数据模型和类型定义

```toml
[package]
name = "otlp-core"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"
description = "OpenTelemetry Protocol core data models and types"

[dependencies]
# 最小依赖
serde = { workspace = true }
chrono = { workspace = true }
uuid = { workspace = true }

[features]
default = ["std"]
std = []
validation = []  # 数据验证
```

**模块结构**:

```text
otlp-core/
├── src/
│   ├── lib.rs
│   ├── types/           # 核心类型
│   │   ├── trace.rs     # 追踪数据类型
│   │   ├── metric.rs    # 指标数据类型
│   │   ├── log.rs       # 日志数据类型
│   │   └── common.rs    # 通用类型
│   ├── validation/      # 数据验证
│   │   ├── trace.rs
│   │   ├── metric.rs
│   │   └── log.rs
│   └── error.rs         # 核心错误类型
└── tests/
```

**从 otlp 迁移**:

- `src/data.rs` → `otlp-core/src/types/`
- `src/validation/` → `otlp-core/src/validation/`
- `src/error.rs` (部分) → `otlp-core/src/error.rs`

---

#### 1.2 `otlp-proto` (新建)

**职责**: Protocol Buffers 编解码和序列化

```toml
[package]
name = "otlp-proto"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"
description = "OpenTelemetry Protocol protobuf definitions and codecs"

[dependencies]
otlp-core = { path = "../otlp-core" }
prost = { workspace = true }
prost-types = { workspace = true }
opentelemetry-proto = { workspace = true }

[build-dependencies]
prost-build = { workspace = true }
```

**模块结构**:

```text
otlp-proto/
├── src/
│   ├── lib.rs
│   ├── codec/           # 编解码器
│   │   ├── trace.rs
│   │   ├── metric.rs
│   │   └── log.rs
│   └── convert.rs       # otlp-core ↔ protobuf 转换
├── proto/               # .proto 文件
└── build.rs             # 构建脚本
```

**从 otlp 迁移**:

- `src/protobuf.rs` → `otlp-proto/src/codec/`

---

#### 1.3 `otlp-transport` (新建)

**职责**: 网络传输层（gRPC/HTTP）

```toml
[package]
name = "otlp-transport"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"
description = "OpenTelemetry Protocol transport implementations"

[dependencies]
otlp-core = { path = "../otlp-core" }
otlp-proto = { path = "../otlp-proto" }
tokio = { workspace = true }
tonic = { workspace = true, optional = true }
hyper = { workspace = true, optional = true }
reqwest = { workspace = true, optional = true }

[features]
default = ["grpc", "http"]
grpc = ["tonic"]
http = ["hyper", "reqwest"]
tls = ["rustls"]
compression = ["flate2", "brotli", "zstd"]
```

**模块结构**:

```text
otlp-transport/
├── src/
│   ├── lib.rs
│   ├── grpc/            # gRPC 传输
│   │   ├── client.rs
│   │   └── config.rs
│   ├── http/            # HTTP 传输
│   │   ├── client.rs
│   │   └── config.rs
│   ├── tls.rs           # TLS 配置
│   ├── compression.rs   # 压缩算法
│   └── connection_pool.rs
└── tests/
```

**从 otlp 迁移**:

- `src/transport.rs` → `otlp-transport/src/`
- `src/network/` → `otlp-transport/src/`

---

### 2. 功能 Crates

#### 2.1 `otlp` (重构)

**职责**: 完整的 OTLP 客户端实现（保持主 crate 地位）

```toml
[package]
name = "otlp"
version = "0.2.0"  # 主版本升级
edition = "2024"
rust-version = "1.90"
description = "Full-featured OpenTelemetry Protocol implementation"

[dependencies]
# 核心依赖
otlp-core = { path = "../otlp-core" }
otlp-proto = { path = "../otlp-proto" }
otlp-transport = { path = "../otlp-transport" }

# OpenTelemetry
opentelemetry = { workspace = true }
opentelemetry_sdk = { workspace = true }
opentelemetry-otlp = { workspace = true }

# 异步和网络
tokio = { workspace = true }
futures = { workspace = true }

# 性能和监控
dashmap = { workspace = true }
parking_lot = { workspace = true }
metrics = { workspace = true, optional = true }

[features]
default = ["client", "async", "monitoring"]
full = ["client", "async", "monitoring", "performance", "microservices"]

# 核心功能
client = ["otlp-transport/default"]
async = ["tokio/full"]
monitoring = ["metrics"]

# 高级功能
performance = ["simd", "zero-copy"]
simd = []
zero-copy = []
microservices = ["service-discovery", "load-balancing"]
service-discovery = []
load-balancing = []

# 协议扩展
opamp = []
ottl = []
```

**新的模块结构**:

```text
otlp/
├── src/
│   ├── lib.rs           # 简化，主要做导出
│   ├── client/          # 客户端实现
│   │   ├── mod.rs
│   │   ├── builder.rs
│   │   ├── enhanced.rs  # EnhancedOtlpClient
│   │   └── simple.rs    # SimpleOtlpClient
│   ├── exporter/        # 导出器
│   │   ├── mod.rs
│   │   ├── trace.rs
│   │   ├── metric.rs
│   │   └── log.rs
│   ├── processor/       # 处理器
│   │   ├── mod.rs
│   │   ├── batch.rs
│   │   └── optimized.rs
│   ├── performance/     # 性能优化（保留）
│   │   ├── mod.rs
│   │   ├── simd.rs
│   │   ├── zero_copy.rs
│   │   └── memory_pool.rs
│   ├── monitoring/      # 监控集成（保留）
│   │   ├── mod.rs
│   │   ├── metrics.rs
│   │   └── alerts.rs
│   ├── microservices/   # 微服务支持（保留）
│   │   ├── mod.rs
│   │   └── advanced.rs
│   ├── opamp/           # OpAMP 协议（可选）
│   └── ottl/            # OTTL 转换（可选）
├── examples/            # 保持丰富的示例
└── tests/              # 保持完整的测试
```

**清理计划**:

- 移除 `ai_ml/`, `blockchain/`, `edge_computing/`（已备份）
- 简化 `advanced_features.rs`, `enterprise_features.rs`（保留核心，其他迁移到扩展 crate）
- 合并重复的性能模块

---

#### 2.2 `reliability` (增强)

**职责**: 统一可靠性框架

```toml
[package]
name = "reliability"
version = "0.2.0"
edition = "2024"
rust-version = "1.90"
description = "Unified reliability framework with fault tolerance and monitoring"

[dependencies]
# 核心依赖
otlp-core = { path = "../otlp-core" }  # 只依赖核心类型
thiserror = { workspace = true }
anyhow = { workspace = true }
tracing = { workspace = true }

# 可选：完整 OTLP 集成
otlp = { path = "../otlp", optional = true }

# 异步支持
tokio = { workspace = true, optional = true }
async-trait = { workspace = true, optional = true }

# 并发和监控
parking_lot = { workspace = true, optional = true }
dashmap = { workspace = true, optional = true }
metrics = { workspace = true, optional = true }

[features]
default = ["std", "async", "fault-tolerance"]
full = ["default", "otlp-integration", "monitoring", "chaos-engineering"]

std = []
async = ["tokio", "async-trait"]
fault-tolerance = ["parking_lot", "dashmap"]
monitoring = ["metrics"]
chaos-engineering = ["proptest"]
otlp-integration = ["otlp"]  # 可选依赖完整 otlp
```

**模块结构保持**:

```text
reliability/
├── src/
│   ├── lib.rs
│   ├── error_handling/      # 错误处理
│   ├── fault_tolerance/     # 容错机制
│   ├── runtime_monitoring/  # 运行时监控
│   ├── runtime_environments/# 运行环境
│   ├── chaos_engineering/   # 混沌工程
│   └── otlp_integration.rs  # OTLP 集成（可选）
├── examples/
└── benches/
```

**增强点**:

- 明确对 `otlp-core` 的依赖（轻量级）
- 通过 feature flag 控制完整 `otlp` 集成
- 增加更多容错模式（Saga、补偿事务等）

---

#### 2.3 `otlp-microservices` (新建，从 otlp 提取)

**职责**: 微服务架构支持

```toml
[package]
name = "otlp-microservices"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"
description = "Microservices support for OTLP with service discovery and load balancing"

[dependencies]
otlp-core = { path = "../otlp-core" }
otlp = { path = "../otlp" }
reliability = { path = "../reliability" }

tokio = { workspace = true }
consul = { workspace = true, optional = true }
tower = { workspace = true }

[features]
default = ["service-discovery", "load-balancing"]
service-discovery = ["consul"]
load-balancing = []
circuit-breaker = ["reliability/fault-tolerance"]
```

**模块结构**:

```text
otlp-microservices/
├── src/
│   ├── lib.rs
│   ├── discovery/       # 服务发现
│   │   ├── consul.rs
│   │   └── dns.rs
│   ├── load_balancing/  # 负载均衡
│   │   ├── round_robin.rs
│   │   └── weighted.rs
│   ├── circuit_breaker.rs
│   └── health_check.rs
└── examples/
    ├── consul_integration.rs
    └── microservice_demo.rs
```

**从 otlp 迁移**:

- `src/microservices/` → `otlp-microservices/src/`

---

### 3. 整合与扩展 Crates

#### 3.1 `otlp-reliability-bridge` (新建)

**职责**: OTLP 与 Reliability 的深度整合

```toml
[package]
name = "otlp-reliability-bridge"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"
description = "Deep integration between OTLP observability and reliability framework"

[dependencies]
otlp = { path = "../otlp" }
reliability = { path = "../reliability" }
opentelemetry = { workspace = true }
tracing = { workspace = true }
```

**模块结构**:

```text
otlp-reliability-bridge/
├── src/
│   ├── lib.rs
│   ├── unified_observability.rs  # 统一可观测性
│   ├── error_trace_correlation.rs # 错误与追踪关联
│   ├── reliability_metrics.rs    # 可靠性指标
│   └── auto_recovery_with_trace.rs # 带追踪的自动恢复
└── examples/
    └── unified_monitoring.rs
```

**功能**:

- 自动将 reliability 的错误转换为 OTLP spans
- 在追踪中记录容错决策（重试、熔断等）
- 统一的健康检查和监控仪表板
- 基于可观测性数据的智能恢复

---

#### 3.2 `otlp-integrations` (新建)

**职责**: 与外部系统的集成

```toml
[package]
name = "otlp-integrations"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"
description = "Integrations with Kubernetes, Prometheus, Grafana, Jaeger, etc."

[dependencies]
otlp = { path = "../otlp" }

[features]
default = []
kubernetes = ["kube"]
prometheus = ["prometheus"]
grafana = []
jaeger = []
```

**模块结构**:

```text
otlp-integrations/
├── src/
│   ├── lib.rs
│   ├── kubernetes/      # K8s 集成
│   │   ├── operator.rs
│   │   └── configmap.rs
│   ├── prometheus/      # Prometheus 导出器
│   ├── grafana/         # Grafana 仪表板
│   └── jaeger/          # Jaeger 追踪
└── examples/
```

**从 otlp 迁移**:

- `src/monitoring_integration.rs` (部分) → `otlp-integrations/src/`

---

#### 3.3 `otlp-cli` (新建)

**职责**: 命令行工具

```toml
[package]
name = "otlp-cli"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

[[bin]]
name = "otlp"
path = "src/main.rs"

[dependencies]
otlp = { path = "../otlp" }
clap = "4.5"
```

**功能**:

- 发送测试数据到 OTLP 端点
- 验证 OTLP 配置
- 性能基准测试
- 监控数据查看

---

### 4. 开发辅助 Crates

#### 4.1 `otlp-examples` (新建，可选)

将所有示例整合到独立 crate：

```text
otlp-examples/
├── Cargo.toml
└── examples/
    ├── 01-basic/
    ├── 02-advanced/
    ├── 03-microservices/
    └── 04-production/
```

#### 4.2 `otlp-benchmarks` (新建，可选)

整合所有基准测试：

```text
otlp-benchmarks/
├── Cargo.toml
├── benches/
└── results/
```

---

## 📊 依赖关系图

```text
┌──────────────────────────────────────────────────────────┐
│                    应用 / 用户代码                        │
└──────────────────────────────────────────────────────────┘
         │                  │                   │
         ▼                  ▼                   ▼
┌────────────────┐  ┌──────────────┐  ┌──────────────────┐
│  otlp-cli      │  │    otlp      │  │  reliability     │
└────────────────┘  └──────────────┘  └──────────────────┘
         │                  │                   │
         └──────────────────┼───────────────────┘
                            ▼
              ┌─────────────────────────┐
              │ otlp-reliability-bridge │
              └─────────────────────────┘
                       │         │
         ┌─────────────┘         └─────────────┐
         ▼                                      ▼
┌──────────────────┐                   ┌──────────────────┐
│ otlp-microservices│                  │ otlp-integrations│
└──────────────────┘                   └──────────────────┘
         │                                      │
         └──────────────┬───────────────────────┘
                        ▼
            ┌───────────────────────┐
            │    otlp-transport     │
            └───────────────────────┘
                        │
         ┌──────────────┼──────────────┐
         ▼              ▼              ▼
┌─────────────┐  ┌─────────────┐  ┌─────────────┐
│ otlp-core   │  │ otlp-proto  │  │ opentelemetry│
└─────────────┘  └─────────────┘  └─────────────┘
```

**依赖层级**:

1. **L0 (Foundation)**: `opentelemetry`, Rust std
2. **L1 (Core)**: `otlp-core`, `otlp-proto`, `otlp-transport`
3. **L2 (Features)**: `otlp`, `reliability`, `otlp-microservices`
4. **L3 (Integration)**: `otlp-reliability-bridge`, `otlp-integrations`
5. **L4 (Applications)**: `otlp-cli`, `otlp-examples`

---

## 📚 文档目录规划

### 新的文档结构

```text
docs/
├── README.md                      # 文档导航
├── architecture/                  # 架构文档
│   ├── overview.md               # 架构概览
│   ├── crate-design.md           # Crate 设计
│   ├── dependency-graph.md       # 依赖关系图
│   └── module-organization.md    # 模块组织
│
├── guides/                        # 用户指南
│   ├── getting-started/          # 快速开始
│   │   ├── installation.md
│   │   ├── first-trace.md
│   │   └── configuration.md
│   ├── tutorials/                # 教程
│   │   ├── 01-basic-usage.md
│   │   ├── 02-advanced-features.md
│   │   ├── 03-microservices.md
│   │   └── 04-production-deployment.md
│   ├── howto/                    # 操作指南
│   │   ├── custom-exporter.md
│   │   ├── performance-tuning.md
│   │   └── troubleshooting.md
│   └── best-practices/           # 最佳实践
│       ├── error-handling.md
│       ├── monitoring.md
│       └── security.md
│
├── api/                          # API 文档
│   ├── otlp-core/
│   ├── otlp-proto/
│   ├── otlp-transport/
│   ├── otlp/
│   ├── reliability/
│   └── integrations/
│
├── design/                       # 设计文档
│   ├── rfcs/                    # RFC (Request for Comments)
│   │   ├── 0001-core-refactor.md
│   │   └── 0002-reliability-integration.md
│   ├── decisions/               # 架构决策记录 (ADR)
│   │   ├── 0001-crate-split.md
│   │   ├── 0002-async-runtime.md
│   │   └── 0003-error-handling.md
│   └── specifications/          # 规范文档
│       ├── otlp-extensions.md
│       └── performance-requirements.md
│
├── implementation/               # 实现细节
│   ├── semantic-models/         # 语义模型
│   │   └── [从 analysis/ 迁移]
│   ├── algorithms/              # 算法实现
│   │   ├── compression.md
│   │   ├── batching.md
│   │   └── load-balancing.md
│   └── optimizations/           # 优化技术
│       ├── simd.md
│       ├── zero-copy.md
│       └── memory-pool.md
│
├── operations/                  # 运维文档
│   ├── deployment/             # 部署指南
│   │   ├── kubernetes.md
│   │   ├── docker.md
│   │   └── bare-metal.md
│   ├── monitoring/             # 监控配置
│   │   ├── prometheus.md
│   │   ├── grafana.md
│   │   └── alerts.md
│   └── maintenance/            # 维护指南
│       ├── upgrades.md
│       ├── backup-recovery.md
│       └── capacity-planning.md
│
├── reports/                    # 报告和分析
│   ├── benchmarks/            # 基准测试报告
│   │   └── [从 benchmarks/results 迁移]
│   ├── security/              # 安全审计报告
│   ├── performance/           # 性能分析报告
│   └── progress/              # 进度报告
│       └── [从 docs/reports 整理]
│
├── research/                  # 研究文档
│   ├── quantum-observability/ # 量子可观测性
│   ├── neuromorphic-monitoring/# 神经形态监控
│   └── ai-automation/        # AI 自动化
│
├── contributing/              # 贡献指南
│   ├── CONTRIBUTING.md
│   ├── code-style.md
│   ├── testing.md
│   └── release-process.md
│
└── reference/                 # 参考资料
    ├── glossary.md           # 术语表
    ├── faq.md                # 常见问题
    └── resources.md          # 外部资源
```

### 文档迁移映射

| 旧位置 | 新位置 | 说明 |
|--------|--------|------|
| `analysis/` | `docs/implementation/semantic-models/` | 语义模型和深度分析 |
| `benchmarks/results/` | `docs/reports/benchmarks/` | 基准测试报告 |
| `docs/reports/` | `docs/reports/progress/` | 进度报告整理 |
| `otlp/docs/` | `docs/api/otlp/` | API 文档 |
| `otlp/semantics/` | `docs/implementation/semantic-models/` | 语义定义 |
| 散落的 README | `docs/guides/` | 统一到指南中 |

### 文档生成工具

```toml
# 在 workspace Cargo.toml 添加
[workspace.metadata.docs.rs]
all-features = true
rustdoc-args = ["--cfg", "docsrs"]
```

使用 `mdBook` 生成文档站点：

```text
docs/book/
├── book.toml
└── src/
    ├── SUMMARY.md
    └── [自动从 docs/ 生成]
```

---

## 🛣️ 迁移路线图

### 阶段 1: 核心拆分（第 1-2 周）

**目标**: 创建基础核心 crates

- [ ] 创建 `otlp-core` crate
  - [ ] 迁移 `data.rs` 到 `types/`
  - [ ] 迁移 `validation/` 模块
  - [ ] 创建核心错误类型
  - [ ] 编写单元测试
  
- [ ] 创建 `otlp-proto` crate
  - [ ] 设置 protobuf 构建
  - [ ] 实现编解码器
  - [ ] 类型转换函数
  
- [ ] 创建 `otlp-transport` crate
  - [ ] 迁移 gRPC 传输
  - [ ] 迁移 HTTP 传输
  - [ ] 连接池实现

**验证**: 所有现有测试通过

### 阶段 2: 主 Crate 重构（第 3-4 周）

**目标**: 重构 `otlp` 和 `reliability`

- [ ] 重构 `otlp` crate
  - [ ] 更新依赖为核心 crates
  - [ ] 简化模块结构
  - [ ] 清理冗余代码
  - [ ] 更新示例
  
- [ ] 增强 `reliability` crate
  - [ ] 添加对 `otlp-core` 的依赖
  - [ ] 可选的完整 `otlp` 集成
  - [ ] 增加新的容错模式

**验证**: 所有示例运行正常

### 阶段 3: 提取专项 Crates（第 5-6 周）

**目标**: 创建专项功能 crates

- [ ] 创建 `otlp-microservices`
  - [ ] 从 `otlp/src/microservices/` 迁移
  - [ ] 集成 `reliability` 容错
  
- [ ] 创建 `otlp-integrations`
  - [ ] Kubernetes 集成
  - [ ] Prometheus 导出器
  - [ ] Grafana 仪表板

**验证**: 集成测试通过

### 阶段 4: 整合层（第 7-8 周）

**目标**: 创建深度整合

- [ ] 创建 `otlp-reliability-bridge`
  - [ ] 统一可观测性
  - [ ] 错误追踪关联
  - [ ] 智能恢复

**验证**: 端到端测试

### 阶段 5: 工具和文档（第 9-10 周）

**目标**: 完善工具链和文档

- [ ] 创建 `otlp-cli`
- [ ] 整理 `otlp-examples`
- [ ] 整理 `otlp-benchmarks`
- [ ] 文档迁移和重组
- [ ] 生成 API 文档
- [ ] 创建 mdBook 站点

**验证**: 文档完整，所有示例可运行

### 阶段 6: 发布准备（第 11-12 周）

- [ ] 性能基准测试
- [ ] 安全审计
- [ ] API 稳定性评审
- [ ] 版本标记
- [ ] 发布到 crates.io

---

## 🎯 最佳实践

### Crate 设计原则

1. **单一职责**: 每个 crate 有明确的边界
2. **最小 API 表面**: 只导出必要的公共接口
3. **特性门控**: 使用 feature flags 控制可选功能
4. **版本兼容**: 遵循语义化版本
5. **文档完整**: 每个公共 API 都有文档

### 依赖管理

```toml
# 工作区统一依赖
[workspace.dependencies]
otlp-core = { path = "otlp-core", version = "0.1.0" }
otlp-proto = { path = "otlp-proto", version = "0.1.0" }
otlp-transport = { path = "otlp-transport", version = "0.1.0" }
otlp = { path = "otlp", version = "0.2.0" }
reliability = { path = "reliability", version = "0.2.0" }
```

### 特性标志策略

```toml
[features]
# 默认特性：最常用的功能组合
default = ["std", "async"]

# 核心特性
std = []
async = ["tokio"]

# 可选特性：按需启用
full = ["std", "async", "monitoring", "performance"]
monitoring = ["metrics"]
performance = ["simd", "zero-copy"]
```

### 测试策略

```rust
// 单元测试：在各 crate 内部
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_core_functionality() {
        // ...
    }
}

// 集成测试：在 tests/ 目录
#[tokio::test]
async fn test_integration() {
    // 跨 crate 测试
}

// 基准测试：在 benches/
use criterion::{criterion_group, criterion_main, Criterion};

fn benchmark(c: &mut Criterion) {
    c.bench_function("operation", |b| {
        b.iter(|| {
            // ...
        });
    });
}
```

### 文档规范

```rust
//! # Crate 级别文档
//! 
//! 概述、快速开始、架构说明
//!
//! ## 示例
//!
//! ```rust
//! use crate_name::Type;
//! let instance = Type::new();
//! ```

/// 函数级别文档
///
/// # 参数
/// 
/// * `param` - 参数说明
///
/// # 返回
///
/// 返回值说明
///
/// # 示例
///
/// ```
/// let result = function(42);
/// ```
///
/// # 错误
///
/// 可能的错误情况
pub fn function(param: i32) -> Result<(), Error> {
    // ...
}
```

### 错误处理

```rust
// 使用 thiserror 定义错误
use thiserror::Error;

#[derive(Error, Debug)]
pub enum CrateError {
    #[error("配置错误: {0}")]
    Config(String),
    
    #[error("网络错误")]
    Network(#[from] std::io::Error),
    
    #[error("OTLP 错误")]
    Otlp(#[from] otlp_core::Error),
}

pub type Result<T> = std::result::Result<T, CrateError>;
```

---

## 📝 更新的工作区 Cargo.toml

```toml
[workspace]
resolver = "3"

members = [
    # 核心 crates
    "otlp-core",
    "otlp-proto",
    "otlp-transport",
    
    # 功能 crates
    "otlp",
    "reliability",
    "otlp-microservices",
    
    # 整合 crates
    "otlp-reliability-bridge",
    "otlp-integrations",
    
    # 工具 crates
    "otlp-cli",
]

[workspace.package]
edition = "2024"
rust-version = "1.90"
license = "MIT OR Apache-2.0"
repository = "https://github.com/your-org/otlp-rust"

[workspace.dependencies]
# 内部 crates
otlp-core = { path = "otlp-core", version = "0.1" }
otlp-proto = { path = "otlp-proto", version = "0.1" }
otlp-transport = { path = "otlp-transport", version = "0.1" }
otlp = { path = "otlp", version = "0.2" }
reliability = { path = "reliability", version = "0.2" }
otlp-microservices = { path = "otlp-microservices", version = "0.1" }

# 外部依赖（从原 Cargo.toml 保留）
# ... [已有的 workspace.dependencies]

# 新增 Crate 构建工具
cargo-workspaces = "0.3"  # 工作区版本管理
cargo-release = "0.25"    # 发布自动化

[profile.release]
# ... [保持原配置]

[profile.dev]
# ... [保持原配置]
```

---

## 🚀 快速开始（新架构）

### 安装

```bash
# 从 crates.io（未来）
cargo add otlp
cargo add reliability

# 从源码（当前）
git clone https://github.com/your-org/otlp-rust
cd otlp-rust
cargo build --all
```

### 基础使用

```rust
use otlp::prelude::*;
use reliability::prelude::*;

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化 OTLP 客户端
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("my-service")
        .build()
        .await?;
    
    // 创建带容错的追踪器
    let tracer = client.tracer("my-component");
    let circuit_breaker = CircuitBreaker::new(5, Duration::from_secs(60));
    
    // 执行带监控的操作
    circuit_breaker.execute(|| async {
        let span = tracer.start("operation");
        // 业务逻辑
        drop(span);
        Ok(())
    }).await?;
    
    Ok(())
}
```

### 高级用法

```rust
use otlp_reliability_bridge::UnifiedObservability;

#[tokio::main]
async fn main() -> Result<()> {
    // 统一的可观测性和可靠性
    let unified = UnifiedObservability::builder()
        .with_otlp_endpoint("http://localhost:4317")
        .with_auto_recovery()
        .with_error_trace_correlation()
        .build()
        .await?;
    
    // 自动记录追踪、错误和恢复
    unified.execute_with_full_observability(|| async {
        // 业务逻辑
        Ok(())
    }).await?;
    
    Ok(())
}
```

---

## 📊 预期收益

### 代码组织

- ✅ 清晰的模块边界
- ✅ 减少编译时间（增量编译优化）
- ✅ 更容易的并行开发
- ✅ 更好的代码复用

### 依赖管理1

- ✅ 最小化核心依赖
- ✅ 可选功能通过 feature flags
- ✅ 减少冲突风险
- ✅ 更快的依赖解析

### 用户体验

- ✅ 渐进式功能采用
- ✅ 明确的升级路径
- ✅ 更好的文档结构
- ✅ 更快的学习曲线

### 维护性

- ✅ 独立的版本发布
- ✅ 局部修改影响小
- ✅ 更容易的测试
- ✅ 清晰的责任划分

---

## 🤝 参与贡献

欢迎参与 Crate 架构的设计和实现！

- 提出建议：[GitHub Issues](https://github.com/your-org/otlp-rust/issues)
- 讨论设计：[GitHub Discussions](https://github.com/your-org/otlp-rust/discussions)
- 提交代码：[Pull Requests](https://github.com/your-org/otlp-rust/pulls)

---

## 📄 许可证

MIT OR Apache-2.0

---

**文档版本**: 1.0  
**最后更新**: 2025-10-20  
**维护者**: OTLP Rust Team
