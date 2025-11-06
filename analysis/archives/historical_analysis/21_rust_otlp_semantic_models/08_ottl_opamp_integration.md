# OTTL 与 OPAMP 集成机制

> **版本**: OTLP 1.3.0 & Rust 1.90
> **日期**: 2025年10月2日
> **主题**: 数据转换语言、远程配置管理、动态更新

---

## 📋 目录

- [OTTL 与 OPAMP 集成机制](#ottl-与-opamp-集成机制)
  - [📋 目录](#-目录)
  - [OTTL 概述](#ottl-概述)
    - [什么是 OTTL](#什么是-ottl)
  - [OTTL 语法与实现](#ottl-语法与实现)
    - [基础语法](#基础语法)
    - [Rust 实现示例](#rust-实现示例)
  - [OPAMP 协议](#opamp-协议)
    - [什么是 OPAMP](#什么是-opamp)
    - [OPAMP 消息格式](#opamp-消息格式)
  - [动态配置管理](#动态配置管理)
    - [实现远程配置客户端](#实现远程配置客户端)
  - [实战案例](#实战案例)
    - [案例 1: 动态采样率调整](#案例-1-动态采样率调整)
    - [案例 2: OTTL 驱动的敏感数据脱敏](#案例-2-ottl-驱动的敏感数据脱敏)

---

## OTTL 概述

### 什么是 OTTL

**OpenTelemetry Transformation Language (OTTL)** 是一种声明式、类型安全的数据转换语言。

**核心特性**:

- ✅ 统一处理 Trace/Metric/Log
- ✅ 路径表达式 (`resource.attributes["service.name"]`)
- ✅ 可插拔函数库
- ✅ 上下文隔离
- ✅ 热更新支持

**应用场景**:

```text
1. 数据清洗: 删除敏感字段
2. 数据丰富: 添加元数据
3. 数据路由: 根据条件分流
4. 数据采样: 自定义采样策略
```

---

## OTTL 语法与实现

### 基础语法

```ottl
# 删除敏感属性
delete_key(attributes, "password")

# 添加环境标签
set(resource.attributes["environment"], "production")

# 条件处理
where attributes["http.status_code"] >= 500
```

### Rust 实现示例

```rust
/// OTTL 表达式解析器
enum OttlExpression {
    DeleteKey { path: String, key: String },
    Set { path: String, value: String },
    Where { condition: Condition },
}

struct Condition {
    left: String,
    operator: Operator,
    right: String,
}

enum Operator {
    Eq,
    Gt,
    Lt,
}

/// 应用 OTTL 转换
fn apply_ottl(span: &mut Span, expr: &OttlExpression) {
    match expr {
        OttlExpression::DeleteKey { key, .. } => {
            span.attributes.retain(|kv| kv.key != *key);
        }
        OttlExpression::Set { path, value } => {
            if path == "attributes" {
                span.attributes.push(KeyValue {
                    key: "custom_key".to_string(),
                    value: Value::String(value.clone()),
                });
            }
        }
        OttlExpression::Where { .. } => {
            // 条件过滤
        }
    }
}

struct Span {
    attributes: Vec<KeyValue>,
}

struct KeyValue {
    key: String,
    value: Value,
}

enum Value {
    String(String),
}
```

---

## OPAMP 协议

### 什么是 OPAMP

**Open Agent Management Protocol (OPAMP)** 是远程管理 OpenTelemetry Agent 的标准协议。

**核心功能**:

- ✅ 远程配置推送
- ✅ 证书管理
- ✅ 二进制更新
- ✅ 健康状态上报
- ✅ 灰度发布

### OPAMP 消息格式

```rust
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize)]
struct OpampMessage {
    /// 消息类型
    message_type: MessageType,
    /// Agent 状态
    agent_status: Option<AgentStatus>,
    /// 配置更新
    config_update: Option<ConfigUpdate>,
}

#[derive(Serialize, Deserialize)]
enum MessageType {
    AgentToServer,
    ServerToAgent,
}

#[derive(Serialize, Deserialize)]
struct AgentStatus {
    agent_id: String,
    health: HealthStatus,
    effective_config: String,
}

#[derive(Serialize, Deserialize)]
enum HealthStatus {
    Healthy,
    Degraded,
    Unhealthy,
}

#[derive(Serialize, Deserialize)]
struct ConfigUpdate {
    config_hash: String,
    config_body: String,
}
```

---

## 动态配置管理

### 实现远程配置客户端

```rust
use tokio_tungstenite::{connect_async, tungstenite::Message};
use futures::{StreamExt, SinkExt};

/// OPAMP 客户端
struct OpampClient {
    agent_id: String,
    server_url: String,
}

impl OpampClient {
    async fn connect(&self) -> Result<(), Box<dyn std::error::Error>> {
        let (mut ws_stream, _) = connect_async(&self.server_url).await?;

        // 发送初始状态
        let status = OpampMessage {
            message_type: MessageType::AgentToServer,
            agent_status: Some(AgentStatus {
                agent_id: self.agent_id.clone(),
                health: HealthStatus::Healthy,
                effective_config: "{}".to_string(),
            }),
            config_update: None,
        };

        ws_stream.send(Message::Text(serde_json::to_string(&status)?)).await?;

        // 接收配置更新
        while let Some(msg) = ws_stream.next().await {
            if let Ok(Message::Text(text)) = msg {
                let update: OpampMessage = serde_json::from_str(&text)?;
                if let Some(config) = update.config_update {
                    self.apply_config(&config.config_body).await?;
                }
            }
        }

        Ok(())
    }

    async fn apply_config(&self, _config: &str) -> Result<(), Box<dyn std::error::Error>> {
        println!("Applying new configuration");
        Ok(())
    }
}
```

---

## 实战案例

### 案例 1: 动态采样率调整

```rust
/// 根据 OPAMP 配置动态调整采样率
struct DynamicSampler {
    sample_rate: std::sync::Arc<std::sync::RwLock<f64>>,
}

impl DynamicSampler {
    async fn update_from_opamp(&self, new_rate: f64) {
        let mut rate = self.sample_rate.write().unwrap();
        *rate = new_rate;
        println!("Sample rate updated to: {}", new_rate);
    }

    fn should_sample(&self) -> bool {
        let rate = self.sample_rate.read().unwrap();
        rand::random::<f64>() < *rate
    }
}
```

### 案例 2: OTTL 驱动的敏感数据脱敏

```rust
/// 使用 OTTL 自动脱敏
fn redact_sensitive_data(span: &mut Span) {
    let ottl_rules = vec![
        OttlExpression::DeleteKey {
            path: "attributes".to_string(),
            key: "password".to_string(),
        },
        OttlExpression::DeleteKey {
            path: "attributes".to_string(),
            key: "credit_card".to_string(),
        },
    ];

    for rule in ottl_rules {
        apply_ottl(span, &rule);
    }
}
```

---

**最后更新**: 2025年10月2日
**作者**: OTLP Rust 项目组
