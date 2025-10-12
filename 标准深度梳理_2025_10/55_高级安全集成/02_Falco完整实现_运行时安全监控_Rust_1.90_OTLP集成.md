# Falco 完整实现：运行时安全监控 - Rust 1.90 + OTLP 集成

## 目录

- [Falco 完整实现：运行时安全监控 - Rust 1.90 + OTLP 集成](#falco-完整实现运行时安全监控---rust-190--otlp-集成)
  - [目录](#目录)
  - [1. 核心概念与架构](#1-核心概念与架构)
    - [1.1 Falco 核心特性](#11-falco-核心特性)
    - [1.2 架构模型](#12-架构模型)
    - [1.3 国际标准对齐](#13-国际标准对齐)
  - [2. Rust 生态集成](#2-rust-生态集成)
    - [2.1 核心依赖](#21-核心依赖)
    - [2.2 项目结构](#22-项目结构)
  - [3. Falco Rules 规则引擎](#3-falco-rules-规则引擎)
    - [3.1 规则定义](#31-规则定义)
    - [3.2 规则解析](#32-规则解析)
    - [3.3 内置规则集](#33-内置规则集)
  - [4. gRPC API 集成](#4-grpc-api-集成)
    - [4.1 gRPC 客户端](#41-grpc-客户端)
    - [4.2 事件订阅](#42-事件订阅)
    - [4.3 输出格式](#43-输出格式)
  - [5. 事件处理与分析](#5-事件处理与分析)
    - [5.1 事件解析](#51-事件解析)
    - [5.2 事件过滤](#52-事件过滤)
    - [5.3 事件聚合](#53-事件聚合)
  - [6. 告警集成](#6-告警集成)
    - [6.1 Slack 集成](#61-slack-集成)
    - [6.2 PagerDuty 集成](#62-pagerduty-集成)
    - [6.3 Webhook 集成](#63-webhook-集成)
  - [7. Kubernetes 审计集成](#7-kubernetes-审计集成)
    - [7.1 Audit Webhook](#71-audit-webhook)
    - [7.2 审计策略](#72-审计策略)
    - [7.3 审计事件处理](#73-审计事件处理)
  - [8. OTLP 可观测性集成](#8-otlp-可观测性集成)
    - [8.1 分布式追踪](#81-分布式追踪)
    - [8.2 指标监控](#82-指标监控)
    - [8.3 安全事件日志](#83-安全事件日志)
  - [9. 生产部署实践](#9-生产部署实践)
    - [9.1 Kubernetes 部署](#91-kubernetes-部署)
    - [9.2 eBPF Driver 配置](#92-ebpf-driver-配置)
    - [9.3 性能优化](#93-性能优化)
  - [10. 测试策略](#10-测试策略)
  - [11. 参考资源](#11-参考资源)
    - [官方文档](#官方文档)
    - [Rust 生态](#rust-生态)
    - [标准与协议](#标准与协议)
    - [云原生](#云原生)

---

## 1. 核心概念与架构

### 1.1 Falco 核心特性

Falco 是云原生运行时安全监控工具，核心特性包括：

| 特性 | 描述 | 应用场景 |
|------|------|----------|
| **内核事件采集** | eBPF/Kernel Module | 系统调用监控 |
| **规则引擎** | YAML规则语言 | 威胁检测 |
| **实时告警** | 多种输出格式 | 事件响应 |
| **Container Runtime** | Docker, containerd, CRI-O | 容器安全 |
| **Kubernetes Audit** | K8s审计日志分析 | 集群安全 |
| **低开销** | eBPF高性能采集 | 生产环境部署 |
| **自定义规则** | 灵活的规则语法 | 定制化安全策略 |

### 1.2 架构模型

```text
┌─────────────────────────────────────────────────────────────────┐
│                      Falco Architecture                         │
│                                                                 │
│  ┌────────────────────────────────────────────────────────────┐ │
│  │                   User Space                               │ │
│  │  ┌──────────────────────────────────────────────────────┐  │ │
│  │  │              Falco Engine                            │  │ │
│  │  │  ┌───────────────────────────────────────────────┐   │  │ │
│  │  │  │          Rules Engine                         │   │  │ │
│  │  │  │  - Rule Parsing                               │   │  │ │
│  │  │  │  - Condition Evaluation                       │   │  │ │
│  │  │  │  - Priority Filtering                         │   │  │ │
│  │  │  └───────────────────────────────────────────────┘   │  │ │
│  │  │                                                      │  │ │
│  │  │  ┌───────────────────────────────────────────────┐   │  │ │
│  │  │  │          Output Channels                      │   │  │ │
│  │  │  │  - STDOUT                                     │   │  │ │
│  │  │  │  - gRPC API                                   │   │  │ │
│  │  │  │  - HTTP (Webhook)                             │   │  │ │
│  │  │  │  - File                                       │   │  │ │
│  │  │  └───────────────────────────────────────────────┘   │  │ │
│  │  └──────────────────────────────────────────────────────┘  │ │
│  │                          ▲                                 │ │
│  │                          │ Events                          │ │
│  │                          │                                 │ │
│  │  ┌──────────────────────────────────────────────────────┐  │ │
│  │  │              libsinsp/libscap                        │  │ │
│  │  │  - Event Parsing                                     │  │ │
│  │  │  - Syscall Decoding                                  │  │ │
│  │  │  - Container Metadata                                │  │ │
│  │  └──────────────────────────────────────────────────────┘  │ │
│  └────────────────────────────────────────────────────────────┘ │
│                          ▲                                      │
│                          │ Raw Events                           │
│  ┌────────────────────────────────────────────────────────────┐ │
│  │                   Kernel Space                             │ │
│  │  ┌──────────────────────────────────────────────────────┐  │ │
│  │  │          eBPF Probe / Kernel Module                  │  │ │
│  │  │  - Syscall Tracing                                   │  │ │
│  │  │  - Kprobe Hooks                                      │  │ │
│  │  │  - Tracepoints                                       │  │ │
│  │  └──────────────────────────────────────────────────────┘  │ │
│  └────────────────────────────────────────────────────────────┘ │
│                          ▲                                      │
│                          │ System Calls                         │
│  ┌────────────────────────────────────────────────────────────┐ │
│  │              Container Runtimes                            │ │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐                  │ │
│  │  │  Docker  │  │containerd│  │  CRI-O   │                  │ │
│  │  └──────────┘  └──────────┘  └──────────┘                  │ │
│  └────────────────────────────────────────────────────────────┘ │
│                                                                 │
│  ┌────────────────────────────────────────────────────────────┐ │
│  │              External Integrations                         │ │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐    │ │
│  │  │  Slack   │  │PagerDuty │  │Webhook   │  │   SIEM   │    │ │
│  │  └──────────┘  └──────────┘  └──────────┘  └──────────┘    │ │
│  └────────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────────┘
```

**核心组件说明**：

- **eBPF Probe**: 基于 eBPF 的内核事件采集
- **libscap/libsinsp**: 系统调用捕获与解析库
- **Rules Engine**: 规则引擎，评估事件是否匹配规则
- **Output Channels**: 多种输出渠道（gRPC, HTTP, File）

### 1.3 国际标准对齐

| 标准/协议 | 应用场景 | Falco 实现 |
|-----------|----------|------------|
| **eBPF (Extended Berkeley Packet Filter)** | 内核编程 | 事件采集 |
| **CRI (Container Runtime Interface)** | 容器运行时 | 容器元数据 |
| **Kubernetes Audit** | 审计日志 | K8s事件分析 |
| **MITRE ATT&CK** | 威胁模型 | 规则映射 |
| **NIST CSF** | 网络安全框架 | 检测与响应 |
| **PCI DSS** | 支付卡安全 | 合规监控 |
| **GDPR** | 数据保护 | 访问监控 |
| **gRPC** | API协议 | 事件流 |
| **OpenTelemetry** | 可观测性 | 追踪与指标 |

---

## 2. Rust 生态集成

### 2.1 核心依赖

```toml
[package]
name = "falco-integration"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# gRPC & Protobuf
tonic = { version = "0.12", features = ["tls"] }
prost = "0.13"
prost-types = "0.13"

# 异步运行时
tokio = { version = "1.42", features = ["full"] }
tokio-stream = "0.1"

# HTTP 客户端
reqwest = { version = "0.12", features = ["json"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
serde_yaml = "0.9"

# 错误处理
anyhow = "1.0"
thiserror = "2.0"

# OpenTelemetry (OTLP)
opentelemetry = "0.27"
opentelemetry-otlp = { version = "0.27", features = ["grpc-tonic", "metrics", "trace"] }
opentelemetry_sdk = { version = "0.27", features = ["rt-tokio"] }
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.28"

# 时间处理
chrono = "0.4"

# 配置管理
config = "0.14"

# 正则表达式
regex = "1.11"

[build-dependencies]
tonic-build = "0.12"
```

### 2.2 项目结构

```text
falco-integration/
├── src/
│   ├── main.rs                    # 入口
│   ├── grpc/
│   │   ├── mod.rs
│   │   ├── client.rs              # Falco gRPC Client
│   │   └── events.rs              # 事件订阅
│   ├── rules/
│   │   ├── mod.rs
│   │   ├── parser.rs              # 规则解析
│   │   ├── engine.rs              # 规则引擎
│   │   └── builtin.rs             # 内置规则
│   ├── events/
│   │   ├── mod.rs
│   │   ├── processor.rs           # 事件处理
│   │   ├── filter.rs              # 事件过滤
│   │   └── aggregator.rs          # 事件聚合
│   ├── alerts/
│   │   ├── mod.rs
│   │   ├── slack.rs               # Slack 集成
│   │   ├── pagerduty.rs           # PagerDuty 集成
│   │   └── webhook.rs             # Webhook 集成
│   ├── k8s/
│   │   ├── mod.rs
│   │   ├── audit.rs               # Kubernetes Audit
│   │   └── events.rs              # K8s 事件处理
│   ├── observability/
│   │   ├── mod.rs
│   │   ├── tracing.rs             # 分布式追踪
│   │   └── metrics.rs             # 指标收集
│   └── error.rs                   # 错误定义
├── proto/
│   ├── falco.proto                # Falco gRPC API
│   └── schema.proto               # Event Schema
├── examples/
│   ├── basic_client.rs
│   └── custom_rules.rs
├── tests/
│   └── integration_test.rs
├── build.rs                        # Protobuf 构建
└── Cargo.toml
```

---

## 3. Falco Rules 规则引擎

### 3.1 规则定义

Falco 使用 YAML 格式定义规则：

```yaml
# rules/suspicious_activity.yaml
- rule: Terminal Shell in Container
  desc: Detect shell execution in container
  condition: >
    spawned_process and
    container and
    shell_procs and
    proc.tty != 0 and
    container_entrypoint
  output: >
    Shell spawned in container (user=%user.name %container.info
    shell=%proc.name parent=%proc.pname cmdline=%proc.cmdline
    terminal=%proc.tty container_id=%container.id image=%container.image.repository)
  priority: WARNING
  tags: [shell, container, mitre_execution]

- rule: Write Below Binary Dir
  desc: Detect suspicious write to system binary directory
  condition: >
    open_write and
    bin_dir and
    not package_mgmt_procs and
    not exe_running_docker_save
  output: >
    File below a known binary directory opened for writing
    (user=%user.name file=%fd.name command=%proc.cmdline
    container_id=%container.id image=%container.image.repository)
  priority: ERROR
  tags: [filesystem, mitre_persistence]

- rule: Contact K8S API Server From Container
  desc: Detect attempts to contact K8s API from container
  condition: >
    evt.type=connect and
    evt.dir=< and
    (fd.typechar=4 or fd.typechar=6) and
    container and
    not k8s_containers and
    k8s_api_server
  output: >
    Unexpected connection to K8s API Server from container
    (user=%user.name command=%proc.cmdline
    connection=%fd.name container_id=%container.id
    image=%container.image.repository)
  priority: NOTICE
  tags: [network, k8s, mitre_discovery]
```

### 3.2 规则解析

```rust
// src/rules/parser.rs
use anyhow::Result;
use serde::{Deserialize, Serialize};
use tracing::{info, instrument};

/// Falco 规则
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FalcoRule {
    pub rule: String,
    pub desc: String,
    pub condition: String,
    pub output: String,
    pub priority: Priority,
    #[serde(default)]
    pub tags: Vec<String>,
    #[serde(default)]
    pub enabled: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "UPPERCASE")]
pub enum Priority {
    Emergency,
    Alert,
    Critical,
    Error,
    Warning,
    Notice,
    Informational,
    Debug,
}

/// 规则解析器
pub struct RuleParser;

impl RuleParser {
    /// 从 YAML 加载规则
    #[instrument(skip(yaml_content))]
    pub fn parse_yaml(yaml_content: &str) -> Result<Vec<FalcoRule>> {
        info!("Parsing Falco rules from YAML");

        let rules: Vec<FalcoRule> = serde_yaml::from_str(yaml_content)?;

        // 验证规则
        for rule in &rules {
            Self::validate_rule(rule)?;
        }

        info!(rule_count = %rules.len(), "Falco rules parsed");

        Ok(rules)
    }

    /// 验证规则
    fn validate_rule(rule: &FalcoRule) -> Result<()> {
        if rule.rule.is_empty() {
            anyhow::bail!("Rule name cannot be empty");
        }

        if rule.condition.is_empty() {
            anyhow::bail!("Rule condition cannot be empty");
        }

        if rule.output.is_empty() {
            anyhow::bail!("Rule output cannot be empty");
        }

        Ok(())
    }

    /// 加载规则文件
    #[instrument]
    pub async fn load_rules_file(path: &str) -> Result<Vec<FalcoRule>> {
        info!(path = %path, "Loading rules file");

        let content = tokio::fs::read_to_string(path).await?;
        Self::parse_yaml(&content)
    }

    /// 加载规则目录
    #[instrument]
    pub async fn load_rules_directory(dir: &str) -> Result<Vec<FalcoRule>> {
        info!(dir = %dir, "Loading rules directory");

        let mut all_rules = Vec::new();
        let mut entries = tokio::fs::read_dir(dir).await?;

        while let Some(entry) = entries.next_entry().await? {
            let path = entry.path();

            if path.extension().and_then(|s| s.to_str()) == Some("yaml")
                || path.extension().and_then(|s| s.to_str()) == Some("yml")
            {
                let rules = Self::load_rules_file(path.to_str().unwrap()).await?;
                all_rules.extend(rules);
            }
        }

        info!(rule_count = %all_rules.len(), "Rules loaded from directory");

        Ok(all_rules)
    }
}
```

### 3.3 内置规则集

```rust
// src/rules/builtin.rs
use super::parser::{FalcoRule, Priority};

/// 内置规则集
pub struct BuiltinRules;

impl BuiltinRules {
    /// 容器逃逸检测规则
    pub fn container_escape_rules() -> Vec<FalcoRule> {
        vec![
            FalcoRule {
                rule: "Launch Privileged Container".to_string(),
                desc: "Detect launch of privileged container".to_string(),
                condition: "container.privileged=true".to_string(),
                output: "Privileged container started (user=%user.name container_id=%container.id image=%container.image.repository)".to_string(),
                priority: Priority::Warning,
                tags: vec!["container".to_string(), "privilege_escalation".to_string()],
                enabled: true,
            },
            FalcoRule {
                rule: "Mount Sensitive Paths".to_string(),
                desc: "Detect sensitive host path mounts in container".to_string(),
                condition: "container and fd.name in (/proc, /sys, /dev)".to_string(),
                output: "Sensitive host path mounted in container (path=%fd.name container_id=%container.id)".to_string(),
                priority: Priority::Error,
                tags: vec!["container".to_string(), "mount".to_string()],
                enabled: true,
            },
        ]
    }

    /// 加密货币挖矿检测规则
    pub fn crypto_mining_rules() -> Vec<FalcoRule> {
        vec![
            FalcoRule {
                rule: "Detect Crypto Miners".to_string(),
                desc: "Detect cryptocurrency mining processes".to_string(),
                condition: "proc.name in (xmrig, ethminer, cgminer)".to_string(),
                output: "Crypto miner detected (process=%proc.name cmdline=%proc.cmdline user=%user.name)".to_string(),
                priority: Priority::Critical,
                tags: vec!["malware".to_string(), "crypto".to_string()],
                enabled: true,
            },
        ]
    }

    /// 网络异常检测规则
    pub fn network_anomaly_rules() -> Vec<FalcoRule> {
        vec![
            FalcoRule {
                rule: "Unexpected Outbound Connection".to_string(),
                desc: "Detect unexpected outbound network connections".to_string(),
                condition: "evt.type=connect and fd.sip not in (internal_networks)".to_string(),
                output: "Unexpected outbound connection (dest=%fd.sip:%fd.sport process=%proc.name user=%user.name)".to_string(),
                priority: Priority::Notice,
                tags: vec!["network".to_string(), "anomaly".to_string()],
                enabled: true,
            },
        ]
    }

    /// 获取所有内置规则
    pub fn all() -> Vec<FalcoRule> {
        let mut rules = Vec::new();
        rules.extend(Self::container_escape_rules());
        rules.extend(Self::crypto_mining_rules());
        rules.extend(Self::network_anomaly_rules());
        rules
    }
}
```

---

## 4. gRPC API 集成

### 4.1 gRPC 客户端

```rust
// build.rs
fn main() -> Result<(), Box<dyn std::error::Error>> {
    tonic_build::configure()
        .build_server(false)
        .compile(
            &["proto/falco.proto", "proto/schema.proto"],
            &["proto/"],
        )?;
    Ok(())
}
```

```rust
// src/grpc/client.rs
use anyhow::Result;
use tonic::transport::Channel;
use tracing::{info, instrument};

// 生成的 gRPC 代码
pub mod falco_api {
    tonic::include_proto!("falco.service");
}

pub mod falco_schema {
    tonic::include_proto!("falco.schema");
}

use falco_api::service_client::ServiceClient;

/// Falco gRPC Client
pub struct FalcoClient {
    client: ServiceClient<Channel>,
}

impl FalcoClient {
    /// 连接到 Falco
    #[instrument]
    pub async fn connect(endpoint: &str) -> Result<Self> {
        info!(endpoint = %endpoint, "Connecting to Falco gRPC server");

        let channel = Channel::from_shared(endpoint.to_string())?
            .connect()
            .await?;

        let client = ServiceClient::new(channel);

        Ok(Self { client })
    }

    /// 获取 Falco 版本
    #[instrument(skip(self))]
    pub async fn get_version(&mut self) -> Result<String> {
        info!("Getting Falco version");

        let request = falco_api::VersionRequest {};
        let response = self.client.version(request).await?;
        let version_response = response.into_inner();

        info!(version = %version_response.version, "Falco version retrieved");

        Ok(version_response.version)
    }

    /// 订阅事件流
    #[instrument(skip(self))]
    pub async fn subscribe_events(&mut self) -> Result<tonic::Streaming<falco_schema::Response>> {
        info!("Subscribing to Falco event stream");

        let request = falco_api::Request {
            // 可选：设置过滤器
            ..Default::default()
        };

        let response = self.client.sub(request).await?;
        let stream = response.into_inner();

        info!("Subscribed to Falco event stream");

        Ok(stream)
    }
}
```

### 4.2 事件订阅

```rust
// src/grpc/events.rs
use anyhow::Result;
use tokio_stream::StreamExt;
use tracing::{info, warn, instrument};

use super::client::{FalcoClient, falco_schema};

/// 事件订阅器
pub struct EventSubscriber {
    client: FalcoClient,
}

impl EventSubscriber {
    pub fn new(client: FalcoClient) -> Self {
        Self { client }
    }

    /// 启动事件订阅
    #[instrument(skip(self, handler))]
    pub async fn start<F>(&mut self, mut handler: F) -> Result<()>
    where
        F: FnMut(FalcoEvent) -> Result<()>,
    {
        info!("Starting Falco event subscription");

        let mut stream = self.client.subscribe_events().await?;

        while let Some(response) = stream.next().await {
            match response {
                Ok(event_response) => {
                    // 解析事件
                    let event = FalcoEvent::from_response(event_response)?;

                    info!(
                        rule = %event.rule,
                        priority = ?event.priority,
                        "Falco event received"
                    );

                    // 调用处理器
                    if let Err(e) = handler(event) {
                        warn!(error = %e, "Event handler failed");
                    }
                }
                Err(e) => {
                    warn!(error = %e, "Error receiving event");
                    break;
                }
            }
        }

        info!("Falco event subscription ended");

        Ok(())
    }
}

/// Falco 事件
#[derive(Debug, Clone)]
pub struct FalcoEvent {
    pub time: chrono::DateTime<chrono::Utc>,
    pub priority: Priority,
    pub rule: String,
    pub output: String,
    pub output_fields: std::collections::HashMap<String, String>,
    pub hostname: String,
    pub tags: Vec<String>,
}

impl FalcoEvent {
    /// 从 gRPC Response 转换
    pub fn from_response(response: falco_schema::Response) -> Result<Self> {
        use chrono::TimeZone;

        let time = chrono::Utc.timestamp_opt(
            response.time.unwrap().seconds,
            response.time.unwrap().nanos as u32,
        ).single().ok_or_else(|| anyhow::anyhow!("Invalid timestamp"))?;

        let priority = match response.priority {
            0 => Priority::Emergency,
            1 => Priority::Alert,
            2 => Priority::Critical,
            3 => Priority::Error,
            4 => Priority::Warning,
            5 => Priority::Notice,
            6 => Priority::Informational,
            7 => Priority::Debug,
            _ => Priority::Informational,
        };

        Ok(Self {
            time,
            priority,
            rule: response.rule,
            output: response.output,
            output_fields: response.output_fields,
            hostname: response.hostname,
            tags: response.tags,
        })
    }

    /// 检查是否匹配标签
    pub fn has_tag(&self, tag: &str) -> bool {
        self.tags.iter().any(|t| t == tag)
    }

    /// 检查优先级
    pub fn is_high_priority(&self) -> bool {
        matches!(
            self.priority,
            Priority::Emergency | Priority::Alert | Priority::Critical | Priority::Error
        )
    }
}
```

### 4.3 输出格式

```rust
// src/grpc/events.rs (续)
use serde::{Deserialize, Serialize};

impl FalcoEvent {
    /// 转换为 JSON
    pub fn to_json(&self) -> Result<String> {
        #[derive(Serialize)]
        struct JsonOutput {
            time: String,
            priority: String,
            rule: String,
            output: String,
            output_fields: std::collections::HashMap<String, String>,
            hostname: String,
            tags: Vec<String>,
        }

        let json_output = JsonOutput {
            time: self.time.to_rfc3339(),
            priority: format!("{:?}", self.priority),
            rule: self.rule.clone(),
            output: self.output.clone(),
            output_fields: self.output_fields.clone(),
            hostname: self.hostname.clone(),
            tags: self.tags.clone(),
        };

        Ok(serde_json::to_string(&json_output)?)
    }

    /// 格式化为日志行
    pub fn to_log_line(&self) -> String {
        format!(
            "{} {} {} {}",
            self.time.to_rfc3339(),
            self.priority,
            self.rule,
            self.output
        )
    }
}
```

---

## 5. 事件处理与分析

### 5.1 事件解析

```rust
// src/events/processor.rs
use anyhow::Result;
use std::collections::HashMap;
use tracing::{info, instrument};

/// 事件处理器
pub struct EventProcessor {
    parsers: HashMap<String, Box<dyn EventParser>>,
}

impl EventProcessor {
    pub fn new() -> Self {
        Self {
            parsers: HashMap::new(),
        }
    }

    /// 注册解析器
    pub fn register_parser(&mut self, rule_name: String, parser: Box<dyn EventParser>) {
        self.parsers.insert(rule_name, parser);
    }

    /// 处理事件
    #[instrument(skip(self, event))]
    pub fn process(&self, event: &FalcoEvent) -> Result<ProcessedEvent> {
        info!(rule = %event.rule, "Processing event");

        // 查找特定规则的解析器
        if let Some(parser) = self.parsers.get(&event.rule) {
            return parser.parse(event);
        }

        // 默认解析
        Ok(ProcessedEvent {
            original_event: event.clone(),
            severity: Self::map_priority_to_severity(&event.priority),
            category: Self::infer_category(event),
            indicators: Self::extract_indicators(event),
            recommendations: Self::generate_recommendations(event),
        })
    }

    /// 映射优先级到严重程度
    fn map_priority_to_severity(priority: &Priority) -> Severity {
        match priority {
            Priority::Emergency | Priority::Alert => Severity::Critical,
            Priority::Critical | Priority::Error => Severity::High,
            Priority::Warning => Severity::Medium,
            _ => Severity::Low,
        }
    }

    /// 推断类别
    fn infer_category(event: &FalcoEvent) -> EventCategory {
        if event.has_tag("shell") || event.has_tag("execution") {
            EventCategory::Execution
        } else if event.has_tag("network") {
            EventCategory::Network
        } else if event.has_tag("filesystem") {
            EventCategory::FileSystem
        } else if event.has_tag("privilege_escalation") {
            EventCategory::PrivilegeEscalation
        } else {
            EventCategory::Other
        }
    }

    /// 提取威胁指标
    fn extract_indicators(event: &FalcoEvent) -> Vec<String> {
        let mut indicators = Vec::new();

        // 提取进程名
        if let Some(proc_name) = event.output_fields.get("proc.name") {
            indicators.push(format!("Process: {}", proc_name));
        }

        // 提取用户名
        if let Some(user_name) = event.output_fields.get("user.name") {
            indicators.push(format!("User: {}", user_name));
        }

        // 提取容器 ID
        if let Some(container_id) = event.output_fields.get("container.id") {
            indicators.push(format!("Container: {}", container_id));
        }

        indicators
    }

    /// 生成建议
    fn generate_recommendations(event: &FalcoEvent) -> Vec<String> {
        let mut recommendations = Vec::new();

        if event.has_tag("privilege_escalation") {
            recommendations.push("Review container security policies".to_string());
            recommendations.push("Consider using Pod Security Standards".to_string());
        }

        if event.has_tag("shell") {
            recommendations.push("Investigate unexpected shell access".to_string());
            recommendations.push("Review container RBAC permissions".to_string());
        }

        recommendations
    }
}

/// 事件解析器 Trait
pub trait EventParser: Send + Sync {
    fn parse(&self, event: &FalcoEvent) -> Result<ProcessedEvent>;
}

/// 处理后的事件
#[derive(Debug, Clone)]
pub struct ProcessedEvent {
    pub original_event: FalcoEvent,
    pub severity: Severity,
    pub category: EventCategory,
    pub indicators: Vec<String>,
    pub recommendations: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Severity {
    Critical,
    High,
    Medium,
    Low,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EventCategory {
    Execution,
    Network,
    FileSystem,
    PrivilegeEscalation,
    Other,
}
```

### 5.2 事件过滤

```rust
// src/events/filter.rs
use anyhow::Result;
use regex::Regex;
use tracing::{info, instrument};

/// 事件过滤器
pub struct EventFilter {
    rules: Vec<FilterRule>,
}

impl EventFilter {
    pub fn new() -> Self {
        Self { rules: Vec::new() }
    }

    /// 添加过滤规则
    pub fn add_rule(&mut self, rule: FilterRule) {
        self.rules.push(rule);
    }

    /// 检查事件是否应该被处理
    #[instrument(skip(self, event))]
    pub fn should_process(&self, event: &FalcoEvent) -> bool {
        // 如果没有规则，默认处理所有事件
        if self.rules.is_empty() {
            return true;
        }

        // 检查所有规则
        for rule in &self.rules {
            if !rule.matches(event) {
                return false;
            }
        }

        true
    }
}

/// 过滤规则
pub enum FilterRule {
    /// 最小优先级
    MinPriority(Priority),
    /// 必须包含标签
    RequireTags(Vec<String>),
    /// 排除标签
    ExcludeTags(Vec<String>),
    /// 规则名称匹配
    RuleNameMatch(Regex),
    /// 输出匹配
    OutputMatch(Regex),
    /// 自定义过滤器
    Custom(Box<dyn Fn(&FalcoEvent) -> bool + Send + Sync>),
}

impl FilterRule {
    /// 检查事件是否匹配规则
    pub fn matches(&self, event: &FalcoEvent) -> bool {
        match self {
            FilterRule::MinPriority(min_priority) => &event.priority <= min_priority,
            FilterRule::RequireTags(tags) => {
                tags.iter().all(|tag| event.has_tag(tag))
            }
            FilterRule::ExcludeTags(tags) => {
                !tags.iter().any(|tag| event.has_tag(tag))
            }
            FilterRule::RuleNameMatch(regex) => {
                regex.is_match(&event.rule)
            }
            FilterRule::OutputMatch(regex) => {
                regex.is_match(&event.output)
            }
            FilterRule::Custom(func) => func(event),
        }
    }
}
```

### 5.3 事件聚合

```rust
// src/events/aggregator.rs
use anyhow::Result;
use std::collections::HashMap;
use tokio::time::{interval, Duration};
use tracing::{info, instrument};

/// 事件聚合器
pub struct EventAggregator {
    window_size: Duration,
    event_counts: HashMap<String, u64>,
    threshold: u64,
}

impl EventAggregator {
    pub fn new(window_size: Duration, threshold: u64) -> Self {
        Self {
            window_size,
            event_counts: HashMap::new(),
            threshold,
        }
    }

    /// 添加事件
    #[instrument(skip(self, event))]
    pub fn add_event(&mut self, event: &FalcoEvent) -> Option<AggregatedAlert> {
        let key = self.generate_key(event);

        let count = self.event_counts.entry(key.clone()).or_insert(0);
        *count += 1;

        info!(
            rule = %event.rule,
            count = %count,
            threshold = %self.threshold,
            "Event aggregated"
        );

        // 检查是否达到阈值
        if *count >= self.threshold {
            return Some(AggregatedAlert {
                key: key.clone(),
                rule: event.rule.clone(),
                count: *count,
                time: chrono::Utc::now(),
            });
        }

        None
    }

    /// 生成聚合键
    fn generate_key(&self, event: &FalcoEvent) -> String {
        format!("{}_{}_{}", event.rule, event.hostname, event.priority)
    }

    /// 重置计数器
    pub fn reset(&mut self) {
        info!("Resetting event aggregator");
        self.event_counts.clear();
    }

    /// 启动自动重置
    pub async fn start_auto_reset(&mut self) {
        let mut reset_interval = interval(self.window_size);

        loop {
            reset_interval.tick().await;
            self.reset();
        }
    }
}

/// 聚合告警
#[derive(Debug, Clone)]
pub struct AggregatedAlert {
    pub key: String,
    pub rule: String,
    pub count: u64,
    pub time: chrono::DateTime<chrono::Utc>,
}
```

---

## 6. 告警集成

### 6.1 Slack 集成

```rust
// src/alerts/slack.rs
use anyhow::Result;
use reqwest::Client;
use serde::{Deserialize, Serialize};
use tracing::{info, warn, instrument};

/// Slack 告警发送器
pub struct SlackAlerter {
    webhook_url: String,
    client: Client,
}

impl SlackAlerter {
    pub fn new(webhook_url: String) -> Self {
        Self {
            webhook_url,
            client: Client::new(),
        }
    }

    /// 发送告警
    #[instrument(skip(self, event))]
    pub async fn send_alert(&self, event: &FalcoEvent) -> Result<()> {
        info!(rule = %event.rule, "Sending Slack alert");

        let color = Self::get_color_for_priority(&event.priority);

        let message = SlackMessage {
            attachments: vec![SlackAttachment {
                color,
                title: format!("🚨 Falco Alert: {}", event.rule),
                text: event.output.clone(),
                fields: vec![
                    SlackField {
                        title: "Priority".to_string(),
                        value: format!("{:?}", event.priority),
                        short: true,
                    },
                    SlackField {
                        title: "Hostname".to_string(),
                        value: event.hostname.clone(),
                        short: true,
                    },
                    SlackField {
                        title: "Time".to_string(),
                        value: event.time.to_rfc3339(),
                        short: false,
                    },
                ],
            }],
        };

        let response = self
            .client
            .post(&self.webhook_url)
            .json(&message)
            .send()
            .await?;

        if response.status().is_success() {
            info!("Slack alert sent successfully");
        } else {
            warn!(status = %response.status(), "Failed to send Slack alert");
        }

        Ok(())
    }

    fn get_color_for_priority(priority: &Priority) -> String {
        match priority {
            Priority::Emergency | Priority::Alert | Priority::Critical => "#FF0000".to_string(),
            Priority::Error => "#FF6600".to_string(),
            Priority::Warning => "#FFCC00".to_string(),
            _ => "#808080".to_string(),
        }
    }
}

#[derive(Serialize)]
struct SlackMessage {
    attachments: Vec<SlackAttachment>,
}

#[derive(Serialize)]
struct SlackAttachment {
    color: String,
    title: String,
    text: String,
    fields: Vec<SlackField>,
}

#[derive(Serialize)]
struct SlackField {
    title: String,
    value: String,
    short: bool,
}
```

### 6.2 PagerDuty 集成

```rust
// src/alerts/pagerduty.rs
use anyhow::Result;
use reqwest::Client;
use serde::{Deserialize, Serialize};
use tracing::{info, instrument};

/// PagerDuty 告警发送器
pub struct PagerDutyAlerter {
    routing_key: String,
    client: Client,
}

impl PagerDutyAlerter {
    pub fn new(routing_key: String) -> Self {
        Self {
            routing_key,
            client: Client::new(),
        }
    }

    /// 发送告警
    #[instrument(skip(self, event))]
    pub async fn send_alert(&self, event: &FalcoEvent) -> Result<()> {
        info!(rule = %event.rule, "Sending PagerDuty alert");

        let severity = Self::get_severity_for_priority(&event.priority);

        let payload = PagerDutyEvent {
            routing_key: self.routing_key.clone(),
            event_action: "trigger".to_string(),
            payload: PagerDutyPayload {
                summary: format!("Falco Alert: {}", event.rule),
                severity,
                source: event.hostname.clone(),
                timestamp: event.time.to_rfc3339(),
                custom_details: serde_json::to_value(&event.output_fields)?,
            },
        };

        let response = self
            .client
            .post("https://events.pagerduty.com/v2/enqueue")
            .json(&payload)
            .send()
            .await?;

        response.error_for_status()?;

        info!("PagerDuty alert sent successfully");

        Ok(())
    }

    fn get_severity_for_priority(priority: &Priority) -> String {
        match priority {
            Priority::Emergency | Priority::Alert => "critical".to_string(),
            Priority::Critical | Priority::Error => "error".to_string(),
            Priority::Warning => "warning".to_string(),
            _ => "info".to_string(),
        }
    }
}

#[derive(Serialize)]
struct PagerDutyEvent {
    routing_key: String,
    event_action: String,
    payload: PagerDutyPayload,
}

#[derive(Serialize)]
struct PagerDutyPayload {
    summary: String,
    severity: String,
    source: String,
    timestamp: String,
    custom_details: serde_json::Value,
}
```

### 6.3 Webhook 集成

```rust
// src/alerts/webhook.rs
use anyhow::Result;
use reqwest::Client;
use tracing::{info, instrument};

/// Webhook 告警发送器
pub struct WebhookAlerter {
    url: String,
    client: Client,
}

impl WebhookAlerter {
    pub fn new(url: String) -> Self {
        Self {
            url,
            client: Client::new(),
        }
    }

    /// 发送告警
    #[instrument(skip(self, event))]
    pub async fn send_alert(&self, event: &FalcoEvent) -> Result<()> {
        info!(rule = %event.rule, url = %self.url, "Sending webhook alert");

        let response = self
            .client
            .post(&self.url)
            .header("Content-Type", "application/json")
            .json(&event)
            .send()
            .await?;

        response.error_for_status()?;

        info!("Webhook alert sent successfully");

        Ok(())
    }
}
```

---

## 7. Kubernetes 审计集成

### 7.1 Audit Webhook

```yaml
# config/audit-webhook.yaml
apiVersion: v1
kind: Config
clusters:
  - name: falco
    cluster:
      server: http://falco-k8s-audit:8765/k8s-audit
users:
  - name: falco
    user: {}
contexts:
  - context:
      cluster: falco
      user: falco
    name: falco
current-context: falco
```

### 7.2 审计策略

```yaml
# config/audit-policy.yaml
apiVersion: audit.k8s.io/v1
kind: Policy
rules:
  # 记录 Secret 访问
  - level: Metadata
    resources:
      - group: ""
        resources: ["secrets"]

  # 记录 ConfigMap 修改
  - level: RequestResponse
    verbs: ["create", "update", "patch", "delete"]
    resources:
      - group: ""
        resources: ["configmaps"]

  # 记录 Pod 执行
  - level: Request
    verbs: ["create"]
    resources:
      - group: ""
        resources: ["pods/exec"]

  # 记录 RBAC 变更
  - level: RequestResponse
    verbs: ["create", "update", "patch", "delete"]
    resources:
      - group: "rbac.authorization.k8s.io"
        resources: ["roles", "rolebindings", "clusterroles", "clusterrolebindings"]

  # 默认不记录
  - level: None
```

### 7.3 审计事件处理

```rust
// src/k8s/audit.rs
use anyhow::Result;
use serde::{Deserialize, Serialize};
use tracing::{info, warn, instrument};

/// Kubernetes 审计事件
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct K8sAuditEvent {
    pub kind: String,
    pub api_version: String,
    pub audit_id: String,
    pub stage: String,
    pub verb: String,
    pub user: K8sUser,
    pub object_ref: Option<K8sObjectRef>,
    pub response_status: Option<K8sResponseStatus>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct K8sUser {
    pub username: String,
    #[serde(default)]
    pub groups: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct K8sObjectRef {
    pub resource: String,
    pub namespace: Option<String>,
    pub name: Option<String>,
    pub api_version: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct K8sResponseStatus {
    pub code: i32,
}

/// Kubernetes 审计处理器
pub struct K8sAuditProcessor;

impl K8sAuditProcessor {
    /// 分析审计事件
    #[instrument(skip(event))]
    pub fn analyze(event: &K8sAuditEvent) -> Option<SecurityAlert> {
        // 检测可疑的 pod/exec 操作
        if event.verb == "create"
            && event.object_ref.as_ref()
                .map(|obj| obj.resource == "pods/exec")
                .unwrap_or(false)
        {
            return Some(SecurityAlert {
                severity: Severity::High,
                title: "Pod Exec Detected".to_string(),
                description: format!(
                    "User {} executed command in pod",
                    event.user.username
                ),
                recommendations: vec![
                    "Review exec permissions".to_string(),
                    "Audit command execution".to_string(),
                ],
            });
        }

        // 检测 Secret 访问
        if event.object_ref.as_ref()
            .map(|obj| obj.resource == "secrets")
            .unwrap_or(false)
        {
            return Some(SecurityAlert {
                severity: Severity::Medium,
                title: "Secret Access Detected".to_string(),
                description: format!(
                    "User {} accessed secret in namespace {}",
                    event.user.username,
                    event.object_ref.as_ref().unwrap().namespace.as_deref().unwrap_or("default")
                ),
                recommendations: vec![
                    "Review secret access patterns".to_string(),
                    "Consider using sealed secrets".to_string(),
                ],
            });
        }

        None
    }
}

#[derive(Debug, Clone)]
pub struct SecurityAlert {
    pub severity: Severity,
    pub title: String,
    pub description: String,
    pub recommendations: Vec<String>,
}
```

---

## 8. OTLP 可观测性集成

### 8.1 分布式追踪

```rust
// src/observability/tracing.rs
use anyhow::Result;
use opentelemetry::{
    global,
    trace::{SpanKind, Tracer},
    KeyValue,
};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{
    runtime,
    trace::{Config, TracerProvider},
    Resource,
};
use tracing::{info, instrument};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

/// 初始化 OTLP 追踪
#[instrument]
pub fn init_otlp_tracing(service_name: &str, otlp_endpoint: &str) -> Result<()> {
    info!(
        service_name = %service_name,
        otlp_endpoint = %otlp_endpoint,
        "Initializing OTLP tracing"
    );

    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint(otlp_endpoint),
        )
        .with_trace_config(
            Config::default()
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", service_name.to_string()),
                    KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
                ])),
        )
        .install_batch(runtime::Tokio)?;

    global::set_tracer_provider(tracer);

    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    info!("OTLP tracing initialized");

    Ok(())
}

/// 追踪 Falco 事件处理
#[instrument(skip(event), fields(rule = %event.rule, priority = ?event.priority))]
pub fn trace_event_processing(event: &FalcoEvent) {
    let tracer = global::tracer("falco");
    
    let mut span = tracer
        .span_builder("falco.event.process")
        .with_kind(SpanKind::Internal)
        .start(&tracer);

    span.set_attribute(KeyValue::new("falco.rule", event.rule.clone()));
    span.set_attribute(KeyValue::new("falco.priority", format!("{:?}", event.priority)));
    span.set_attribute(KeyValue::new("falco.hostname", event.hostname.clone()));
}
```

### 8.2 指标监控

```rust
// src/observability/metrics.rs
use anyhow::Result;
use opentelemetry::{
    global,
    metrics::{Counter, Histogram, Meter},
    KeyValue,
};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{
    metrics::{PeriodicReader, SdkMeterProvider},
    runtime,
    Resource,
};
use tracing::{info, instrument};

/// Falco 指标
pub struct FalcoMetrics {
    meter: Meter,
    event_counter: Counter<u64>,
    event_processing_duration: Histogram<f64>,
    alert_counter: Counter<u64>,
    rule_evaluation_counter: Counter<u64>,
}

impl FalcoMetrics {
    /// 初始化指标
    #[instrument]
    pub fn new(service_name: &str, otlp_endpoint: &str) -> Result<Self> {
        info!(
            service_name = %service_name,
            otlp_endpoint = %otlp_endpoint,
            "Initializing Falco metrics"
        );

        let exporter = opentelemetry_otlp::new_exporter()
            .tonic()
            .with_endpoint(otlp_endpoint)
            .build_metrics_exporter(
                Box::new(opentelemetry_sdk::metrics::aggregation::default_temporality_selector()),
                Box::new(opentelemetry_sdk::metrics::data::default_resource_detector()),
            )?;

        let reader = PeriodicReader::builder(exporter, runtime::Tokio).build();

        let provider = SdkMeterProvider::builder()
            .with_reader(reader)
            .with_resource(Resource::new(vec![
                KeyValue::new("service.name", service_name.to_string()),
            ]))
            .build();

        global::set_meter_provider(provider.clone());

        let meter = provider.meter("falco");

        let event_counter = meter
            .u64_counter("falco.events")
            .with_description("Number of Falco events")
            .build();

        let event_processing_duration = meter
            .f64_histogram("falco.event.processing.duration")
            .with_description("Duration of event processing")
            .with_unit("s")
            .build();

        let alert_counter = meter
            .u64_counter("falco.alerts")
            .with_description("Number of alerts sent")
            .build();

        let rule_evaluation_counter = meter
            .u64_counter("falco.rules.evaluation")
            .with_description("Number of rule evaluations")
            .build();

        info!("Falco metrics initialized");

        Ok(Self {
            meter,
            event_counter,
            event_processing_duration,
            alert_counter,
            rule_evaluation_counter,
        })
    }

    /// 记录事件
    pub fn record_event(&self, rule: &str, priority: &Priority) {
        let attributes = vec![
            KeyValue::new("rule", rule.to_string()),
            KeyValue::new("priority", format!("{:?}", priority)),
        ];
        self.event_counter.add(1, &attributes);
    }

    /// 记录处理时间
    pub fn record_processing_duration(&self, duration: f64) {
        self.event_processing_duration.record(duration, &[]);
    }

    /// 记录告警
    pub fn record_alert(&self, alert_type: &str, success: bool) {
        let attributes = vec![
            KeyValue::new("type", alert_type.to_string()),
            KeyValue::new("success", success.to_string()),
        ];
        self.alert_counter.add(1, &attributes);
    }
}
```

### 8.3 安全事件日志

```rust
// src/observability/security_log.rs
use serde::{Deserialize, Serialize};
use tracing::{info, warn, instrument};

/// 安全事件日志记录器
pub struct SecurityEventLogger;

impl SecurityEventLogger {
    /// 记录安全事件
    #[instrument(skip(event))]
    pub fn log(event: &FalcoEvent) {
        let security_event = SecurityEvent {
            timestamp: event.time,
            event_type: "falco_alert".to_string(),
            severity: format!("{:?}", event.priority),
            rule: event.rule.clone(),
            description: event.output.clone(),
            source: event.hostname.clone(),
            tags: event.tags.clone(),
            metadata: event.output_fields.clone(),
        };

        let event_json = serde_json::to_string(&security_event).unwrap_or_default();

        if event.is_high_priority() {
            warn!(
                security_event = %event_json,
                "High priority security event"
            );
        } else {
            info!(
                security_event = %event_json,
                "Security event"
            );
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct SecurityEvent {
    timestamp: chrono::DateTime<chrono::Utc>,
    event_type: String,
    severity: String,
    rule: String,
    description: String,
    source: String,
    tags: Vec<String>,
    metadata: std::collections::HashMap<String, String>,
}
```

---

## 9. 生产部署实践

### 9.1 Kubernetes 部署

```yaml
# deploy/falco-daemonset.yaml
apiVersion: v1
kind: ServiceAccount
metadata:
  name: falco
  namespace: falco-system

---
apiVersion: rbac.authorization.k8s.io/v1
kind: ClusterRole
metadata:
  name: falco
rules:
  - apiGroups: [""]
    resources: ["nodes", "namespaces", "pods", "events"]
    verbs: ["get", "list", "watch"]

---
apiVersion: rbac.authorization.k8s.io/v1
kind: ClusterRoleBinding
metadata:
  name: falco
roleRef:
  apiGroup: rbac.authorization.k8s.io
  kind: ClusterRole
  name: falco
subjects:
  - kind: ServiceAccount
    name: falco
    namespace: falco-system

---
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: falco
  namespace: falco-system
spec:
  selector:
    matchLabels:
      app: falco
  template:
    metadata:
      labels:
        app: falco
    spec:
      serviceAccountName: falco
      hostNetwork: true
      hostPID: true
      tolerations:
        - effect: NoSchedule
          key: node-role.kubernetes.io/master
      containers:
        - name: falco
          image: falcosecurity/falco:0.38.2
          args:
            - /usr/bin/falco
            - --cri
            - /run/containerd/containerd.sock
            - -K
            - /var/run/secrets/kubernetes.io/serviceaccount/token
            - -k
            - https://$(KUBERNETES_SERVICE_HOST)
            - -pk
          securityContext:
            privileged: true
          env:
            - name: FALCO_BPF_PROBE
              value: ""
          volumeMounts:
            - name: dev
              mountPath: /host/dev
            - name: proc
              mountPath: /host/proc
              readOnly: true
            - name: boot
              mountPath: /host/boot
              readOnly: true
            - name: lib-modules
              mountPath: /host/lib/modules
              readOnly: true
            - name: usr
              mountPath: /host/usr
              readOnly: true
            - name: etc
              mountPath: /host/etc
              readOnly: true
            - name: config
              mountPath: /etc/falco
          resources:
            requests:
              memory: "512Mi"
              cpu: "500m"
            limits:
              memory: "1Gi"
              cpu: "1000m"
      volumes:
        - name: dev
          hostPath:
            path: /dev
        - name: proc
          hostPath:
            path: /proc
        - name: boot
          hostPath:
            path: /boot
        - name: lib-modules
          hostPath:
            path: /lib/modules
        - name: usr
          hostPath:
            path: /usr
        - name: etc
          hostPath:
            path: /etc
        - name: config
          configMap:
            name: falco
```

### 9.2 eBPF Driver 配置

**eBPF优势**:

- ✅ 无需内核模块
- ✅ 更高的安全性
- ✅ 更容易部署
- ✅ 更好的兼容性

**配置示例**:

```yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: falco
  namespace: falco-system
data:
  falco.yaml: |
    engine:
      kind: ebpf
      ebpf:
        probe: /usr/lib/falco/bpf/probe.o
        
    output_timeout: 2000
    outputs:
      rate: 1
      max_burst: 1000
      
    grpc:
      enabled: true
      bind_address: "0.0.0.0:5060"
      threadiness: 0
      
    grpc_output:
      enabled: true
```

### 9.3 性能优化

| 优化项 | 说明 | 建议配置 |
|--------|------|----------|
| **事件过滤** | 减少不必要的事件 | 使用 `drop_event_type` |
| **输出限流** | 防止日志风暴 | `output_timeout: 2000` |
| **eBPF vs Module** | 选择合适的 driver | 优先使用 eBPF |
| **规则优化** | 精简规则集 | 禁用不需要的规则 |
| **资源限制** | 防止资源耗尽 | CPU: 1 core, Memory: 1GB |

---

## 10. 测试策略

```rust
// tests/integration_test.rs
#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_rule_parsing() {
        let yaml = r#"
- rule: Test Rule
  desc: Test description
  condition: evt.type=open
  output: File opened (name=%fd.name)
  priority: WARNING
  tags: [test]
"#;

        let rules = RuleParser::parse_yaml(yaml).unwrap();
        assert_eq!(rules.len(), 1);
        assert_eq!(rules[0].rule, "Test Rule");
    }

    #[tokio::test]
    async fn test_event_filter() {
        let mut filter = EventFilter::new();
        filter.add_rule(FilterRule::MinPriority(Priority::Warning));

        let event = FalcoEvent {
            time: chrono::Utc::now(),
            priority: Priority::Error,
            rule: "Test".to_string(),
            output: "Test output".to_string(),
            output_fields: Default::default(),
            hostname: "localhost".to_string(),
            tags: vec![],
        };

        assert!(filter.should_process(&event));
    }

    #[tokio::test]
    async fn test_slack_alert() {
        // 使用 mockito 模拟 Slack webhook
        // let mock_server = mockito::Server::new();
        // let alerter = SlackAlerter::new(mock_server.url());
        // alerter.send_alert(&event).await.unwrap();
    }
}
```

---

## 11. 参考资源

### 官方文档

- **Falco**: <https://falco.org/>
- **Falco Rules**: <https://github.com/falcosecurity/rules>
- **Falco Helm Chart**: <https://github.com/falcosecurity/charts>

### Rust 生态

- **tonic**: <https://docs.rs/tonic/>
- **tokio**: <https://tokio.rs/>
- **reqwest**: <https://docs.rs/reqwest/>

### 标准与协议

- **eBPF**: <https://ebpf.io/>
- **MITRE ATT&CK**: <https://attack.mitre.org/>
- **NIST CSF**: <https://www.nist.gov/cyberframework>
- **Kubernetes Audit**: <https://kubernetes.io/docs/tasks/debug/debug-cluster/audit/>

### 云原生

- **Falco Sidekick**: <https://github.com/falcosecurity/falcosidekick>
- **Falco Exporter**: <https://github.com/falcosecurity/falco-exporter>
- **Falco Talon**: <https://github.com/falcosecurity/falco-talon>

---

**本文档提供了 Falco 运行时安全监控在 Rust 生态中的完整实现指南，涵盖事件采集、规则引擎、告警集成、Kubernetes审计、OTLP可观测性，以及生产部署实践。所有代码基于 Rust 1.90 和 OpenTelemetry 0.27，完全对齐国际标准。** 🎉
