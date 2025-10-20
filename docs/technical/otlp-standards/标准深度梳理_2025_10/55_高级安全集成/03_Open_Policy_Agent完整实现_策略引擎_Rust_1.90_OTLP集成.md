# Open Policy Agent 完整实现：策略引擎 - Rust 1.90 + OTLP 集成

## 目录

- [Open Policy Agent 完整实现：策略引擎 - Rust 1.90 + OTLP 集成](#open-policy-agent-完整实现策略引擎---rust-190--otlp-集成)
  - [目录](#目录)
  - [1. 核心概念与架构](#1-核心概念与架构)
    - [1.1 OPA 核心特性](#11-opa-核心特性)
    - [1.2 架构模型](#12-架构模型)
    - [1.3 国际标准对齐](#13-国际标准对齐)
  - [2. Rust 生态集成](#2-rust-生态集成)
    - [2.1 核心依赖](#21-核心依赖)
    - [2.2 项目结构](#22-项目结构)
  - [3. Rego 策略语言](#3-rego-策略语言)
    - [3.1 Rego 基础](#31-rego-基础)
    - [3.2 策略示例](#32-策略示例)
    - [3.3 策略管理](#33-策略管理)
  - [4. REST API 集成](#4-rest-api-集成)
    - [4.1 策略评估API](#41-策略评估api)
    - [4.2 数据API](#42-数据api)
    - [4.3 批量决策](#43-批量决策)
  - [5. Kubernetes Admission Controller](#5-kubernetes-admission-controller)
    - [5.1 Webhook 配置](#51-webhook-配置)
    - [5.2 Pod 安全策略](#52-pod-安全策略)
    - [5.3 RBAC 策略](#53-rbac-策略)
  - [6. 数据过滤与转换](#6-数据过滤与转换)
    - [6.1 JSON 数据过滤](#61-json-数据过滤)
    - [6.2 GraphQL 授权](#62-graphql-授权)
    - [6.3 微服务授权](#63-微服务授权)
  - [7. Bundle 分发](#7-bundle-分发)
    - [7.1 Bundle 格式](#71-bundle-格式)
    - [7.2 Bundle 服务器](#72-bundle-服务器)
    - [7.3 Bundle 签名](#73-bundle-签名)
  - [8. 决策日志](#8-决策日志)
    - [8.1 日志收集](#81-日志收集)
    - [8.2 审计跟踪](#82-审计跟踪)
    - [8.3 合规报告](#83-合规报告)
  - [9. OTLP 可观测性集成](#9-otlp-可观测性集成)
    - [9.1 分布式追踪](#91-分布式追踪)
    - [9.2 指标监控](#92-指标监控)
    - [9.3 性能分析](#93-性能分析)
  - [10. 生产部署实践](#10-生产部署实践)
    - [10.1 Kubernetes 部署](#101-kubernetes-部署)
    - [10.2 高可用配置](#102-高可用配置)
    - [10.3 性能优化](#103-性能优化)
  - [11. 测试策略](#11-测试策略)
  - [12. 参考资源](#12-参考资源)
    - [官方文档](#官方文档)
    - [Rust 生态](#rust-生态)
    - [标准与协议](#标准与协议)
    - [云原生](#云原生)

---

## 1. 核心概念与架构

### 1.1 OPA 核心特性

Open Policy Agent (OPA) 是云原生通用策略引擎，核心特性包括：

| 特性 | 描述 | 应用场景 |
|------|------|----------|
| **通用策略引擎** | 统一策略框架 | 微服务、K8s、API网关 |
| **Rego 语言** | 声明式策略语言 | 复杂授权逻辑 |
| **决策即服务** | RESTful API | 策略评估 |
| **数据过滤** | Partial Evaluation | 大数据集过滤 |
| **Admission Control** | K8s准入控制 | Pod安全策略 |
| **Bundle分发** | 策略打包与分发 | 多环境部署 |
| **决策日志** | 审计与合规 | 安全追踪 |

### 1.2 架构模型

```text
┌─────────────────────────────────────────────────────────────────┐
│                     OPA Architecture                            │
│                                                                 │
│  ┌────────────────────────────────────────────────────────────┐ │
│  │               Applications & Services                      │ │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐    │ │
│  │  │   API    │  │   K8s    │  │  Service │  │  Gateway │    │ │
│  │  │ Gateway  │  │Admission │  │   Mesh   │  │          │    │ │
│  │  └────┬─────┘  └────┬─────┘  └────┬─────┘  └────┬─────┘    │ │
│  └───────┼──────────────┼──────────────┼──────────────┼───────┘ │
│          │              │              │              │         │
│          │ Policy       │ Policy       │ Policy       │ Policy  │
│          │ Query        │ Query        │ Query        │ Query   │
│          ▼              ▼              ▼              ▼         │
│  ┌────────────────────────────────────────────────────────────┐ │
│  │                    OPA Core Engine                         │ │
│  │  ┌──────────────────────────────────────────────────────┐  │ │
│  │  │              Policy Evaluation                       │  │ │
│  │  │  ┌───────────────────────────────────────────────┐   │  │ │
│  │  │  │          Rego Interpreter                     │   │  │ │
│  │  │  │  - Policy Compilation                         │   │  │ │
│  │  │  │  - Query Execution                            │   │  │ │
│  │  │  │  - Partial Evaluation                         │   │  │ │
│  │  │  └───────────────────────────────────────────────┘   │  │ │
│  │  │                                                      │  │ │
│  │  │  ┌───────────────────────────────────────────────┐   │  │ │
│  │  │  │          Data Store                           │   │  │ │
│  │  │  │  - In-Memory Cache                            │   │  │ │
│  │  │  │  - External Data                              │   │  │ │
│  │  │  │  - Base Documents                             │   │  │ │
│  │  │  └───────────────────────────────────────────────┘   │  │ │
│  │  └──────────────────────────────────────────────────────┘  │ │
│  │                                                            │ │
│  │  ┌──────────────────────────────────────────────────────┐  │ │
│  │  │              Decision Logging                        │  │ │
│  │  │  - Query Logs                                        │  │ │
│  │  │  - Audit Trail                                       │  │ │
│  │  │  - Compliance Reports                                │  │ │
│  │  └──────────────────────────────────────────────────────┘  │ │
│  └────────────────────────────────────────────────────────────┘ │
│                          ▲                  ▲                   │
│                          │ Bundles          │ Data              │
│                          │                  │                   │
│  ┌────────────────────────────────────────────────────────────┐ │
│  │              Management & Distribution                     │ │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐    │ │
│  │  │  Bundle  │  │  Bundle  │  │External  │  │ Decision │    │ │
│  │  │  Server  │  │  Signing │  │   Data   │  │   Logs   │    │ │
│  │  └──────────┘  └──────────┘  └──────────┘  └──────────┘    │ │
│  └────────────────────────────────────────────────────────────┘ │
│                                                                 │
│  ┌────────────────────────────────────────────────────────────┐ │
│  │              Observability & Monitoring                    │ │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐                  │ │
│  │  │  Traces  │  │ Metrics  │  │   Logs   │                  │ │
│  │  │  (OTLP)  │  │  (OTLP)  │  │  (JSON)  │                  │ │
│  │  └──────────┘  └──────────┘  └──────────┘                  │ │
│  └────────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────────┘
```

**核心组件说明**：

- **Rego Interpreter**: 策略语言解释器
- **Data Store**: 内存数据存储
- **Decision Logging**: 决策日志记录
- **Bundle Management**: 策略包管理

### 1.3 国际标准对齐

| 标准/协议 | 应用场景 | OPA 实现 |
|-----------|----------|----------|
| **JSON (RFC 8259)** | 数据格式 | 输入/输出 |
| **JWT (RFC 7519)** | 令牌验证 | 授权决策 |
| **OAuth 2.0 (RFC 6749)** | 授权框架 | 访问控制 |
| **RBAC (RFC 6749)** | 角色权限 | 策略模型 |
| **ABAC** | 属性授权 | 策略评估 |
| **Kubernetes API** | K8s集成 | Admission Control |
| **HTTP/REST** | API协议 | 策略评估API |
| **gRPC** | RPC协议 | 可选API |
| **OpenTelemetry** | 可观测性 | 追踪与指标 |

---

## 2. Rust 生态集成

### 2.1 核心依赖

```toml
[package]
name = "opa-integration"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# HTTP 客户端/服务器
reqwest = { version = "0.12", features = ["json"] }
axum = { version = "0.7", features = ["macros"] }
tower = "0.5"
tower-http = { version = "0.6", features = ["trace"] }

# 异步运行时
tokio = { version = "1.42", features = ["full"] }

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

# JSON Web Token
jsonwebtoken = "9.3"

# Base64
base64 = "0.22"

# 配置管理
config = "0.14"
```

### 2.2 项目结构

```text
opa-integration/
├── src/
│   ├── main.rs                    # 入口
│   ├── client/
│   │   ├── mod.rs
│   │   ├── rest.rs                # REST API Client
│   │   └── policy.rs              # 策略评估
│   ├── rego/
│   │   ├── mod.rs
│   │   ├── policy.rs              # Rego策略
│   │   └── parser.rs              # 策略解析
│   ├── admission/
│   │   ├── mod.rs
│   │   ├── webhook.rs             # K8s Webhook
│   │   └── validator.rs           # 准入验证
│   ├── bundle/
│   │   ├── mod.rs
│   │   ├── server.rs              # Bundle服务器
│   │   └── signer.rs              # Bundle签名
│   ├── decision/
│   │   ├── mod.rs
│   │   ├── logger.rs              # 决策日志
│   │   └── audit.rs               # 审计追踪
│   ├── observability/
│   │   ├── mod.rs
│   │   ├── tracing.rs             # 分布式追踪
│   │   └── metrics.rs             # 指标收集
│   └── error.rs                   # 错误定义
├── policies/
│   ├── kubernetes/
│   │   ├── pod_security.rego
│   │   └── rbac.rego
│   ├── api/
│   │   └── authorization.rego
│   └── data_filter/
│       └── graphql.rego
├── examples/
│   ├── basic_policy.rs
│   └── k8s_admission.rs
├── tests/
│   └── integration_test.rs
└── Cargo.toml
```

---

## 3. Rego 策略语言

### 3.1 Rego 基础

Rego 是声明式策略语言，核心概念：

```rego
# 包声明
package example.authz

# 导入
import rego.v1

# 默认决策
default allow := false

# 规则定义
allow if {
    # 条件1: 用户已认证
    input.user.authenticated == true
    
    # 条件2: 用户有admin角色
    "admin" in input.user.roles
}

# 带参数的规则
allow if {
    input.method == "GET"
    is_public_resource(input.path)
}

# 辅助函数
is_public_resource(path) if {
    startswith(path, "/public")
}

# 集合操作
admin_users := {"alice", "bob", "charlie"}

is_admin(user) if {
    user in admin_users
}

# 部分规则
violations[msg] {
    input.kind == "Pod"
    not input.spec.securityContext.runAsNonRoot
    msg := "Pod must run as non-root"
}
```

### 3.2 策略示例

**Kubernetes Pod 安全策略**:

```rego
# policies/kubernetes/pod_security.rego
package kubernetes.admission

import rego.v1

# 默认拒绝
deny[msg] {
    input.request.kind.kind == "Pod"
    not input.request.object.spec.securityContext.runAsNonRoot
    msg := "Pods must run as non-root"
}

# 拒绝特权容器
deny[msg] {
    input.request.kind.kind == "Pod"
    container := input.request.object.spec.containers[_]
    container.securityContext.privileged == true
    msg := sprintf("Container %s cannot run in privileged mode", [container.name])
}

# 拒绝主机网络
deny[msg] {
    input.request.kind.kind == "Pod"
    input.request.object.spec.hostNetwork == true
    msg := "Pods cannot use host network"
}

# 强制资源限制
deny[msg] {
    input.request.kind.kind == "Pod"
    container := input.request.object.spec.containers[_]
    not container.resources.limits.memory
    msg := sprintf("Container %s must have memory limit", [container.name])
}

# 允许的镜像注册表
allowed_registries := [
    "gcr.io/my-project",
    "docker.io/myorg",
]

deny[msg] {
    input.request.kind.kind == "Pod"
    container := input.request.object.spec.containers[_]
    image := container.image
    not image_from_allowed_registry(image)
    msg := sprintf("Image %s from disallowed registry", [image])
}

image_from_allowed_registry(image) if {
    registry := allowed_registries[_]
    startswith(image, registry)
}
```

**API 授权策略**:

```rego
# policies/api/authorization.rego
package api.authz

import rego.v1

# 默认拒绝
default allow := false

# 公共端点
allow if {
    input.method == "GET"
    input.path == "/health"
}

# 认证用户可以访问自己的资源
allow if {
    input.method == "GET"
    input.path == ["users", user_id]
    input.user.id == user_id
}

# Admin可以访问所有资源
allow if {
    "admin" in input.user.roles
}

# 基于JWT的授权
allow if {
    token := input.token
    [valid, _, payload] := io.jwt.decode_verify(token, {"secret": data.jwt_secret})
    valid == true
    payload.sub == input.user.id
}

# 速率限制
deny[msg] {
    count_requests(input.user.id) > 100
    msg := "Rate limit exceeded"
}

count_requests(user_id) := count {
    count := count([req | req := data.requests[_]; req.user == user_id])
}
```

### 3.3 策略管理

```rust
// src/rego/policy.rs
use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use tracing::{info, instrument};

/// Rego 策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RegoPolicy {
    pub id: String,
    pub package_path: String,
    pub content: String,
    pub version: String,
    pub metadata: PolicyMetadata,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PolicyMetadata {
    pub title: String,
    pub description: String,
    pub severity: String,
    #[serde(default)]
    pub tags: Vec<String>,
}

/// 策略管理器
pub struct PolicyManager {
    policies: HashMap<String, RegoPolicy>,
}

impl PolicyManager {
    pub fn new() -> Self {
        Self {
            policies: HashMap::new(),
        }
    }

    /// 加载策略
    #[instrument(skip(self, policy))]
    pub fn load_policy(&mut self, policy: RegoPolicy) -> Result<()> {
        info!(
            policy_id = %policy.id,
            package = %policy.package_path,
            "Loading policy"
        );

        // 验证策略
        self.validate_policy(&policy)?;

        self.policies.insert(policy.id.clone(), policy);

        Ok(())
    }

    /// 从文件加载策略
    #[instrument(skip(self))]
    pub async fn load_from_file(&mut self, path: &str) -> Result<()> {
        info!(path = %path, "Loading policy from file");

        let content = tokio::fs::read_to_string(path).await?;

        // 解析策略元数据（从注释中提取）
        let metadata = Self::parse_metadata(&content)?;

        let policy = RegoPolicy {
            id: Self::generate_policy_id(path),
            package_path: Self::extract_package_path(&content)?,
            content,
            version: "1.0.0".to_string(),
            metadata,
        };

        self.load_policy(policy)?;

        Ok(())
    }

    /// 验证策略
    fn validate_policy(&self, policy: &RegoPolicy) -> Result<()> {
        // 基本验证
        if policy.content.is_empty() {
            anyhow::bail!("Policy content cannot be empty");
        }

        if !policy.content.contains("package") {
            anyhow::bail!("Policy must declare a package");
        }

        Ok(())
    }

    /// 生成策略ID
    fn generate_policy_id(path: &str) -> String {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut hasher = DefaultHasher::new();
        path.hash(&mut hasher);
        format!("policy_{:x}", hasher.finish())
    }

    /// 提取package路径
    fn extract_package_path(content: &str) -> Result<String> {
        for line in content.lines() {
            if line.trim().starts_with("package") {
                let parts: Vec<&str> = line.split_whitespace().collect();
                if parts.len() >= 2 {
                    return Ok(parts[1].to_string());
                }
            }
        }

        anyhow::bail!("No package declaration found")
    }

    /// 解析元数据
    fn parse_metadata(content: &str) -> Result<PolicyMetadata> {
        // 从注释中提取元数据（简化示例）
        Ok(PolicyMetadata {
            title: "Policy".to_string(),
            description: "Policy description".to_string(),
            severity: "medium".to_string(),
            tags: Vec::new(),
        })
    }

    /// 获取策略
    pub fn get_policy(&self, id: &str) -> Option<&RegoPolicy> {
        self.policies.get(id)
    }

    /// 列出所有策略
    pub fn list_policies(&self) -> Vec<&RegoPolicy> {
        self.policies.values().collect()
    }
}
```

---

## 4. REST API 集成

### 4.1 策略评估API

```rust
// src/client/rest.rs
use anyhow::Result;
use reqwest::Client;
use serde::{Deserialize, Serialize};
use tracing::{info, warn, instrument};

/// OPA REST Client
pub struct OpaClient {
    base_url: String,
    client: Client,
}

impl OpaClient {
    pub fn new(base_url: String) -> Self {
        Self {
            base_url,
            client: Client::new(),
        }
    }

    /// 评估策略
    #[instrument(skip(self, input))]
    pub async fn evaluate_policy(
        &self,
        policy_path: &str,
        input: serde_json::Value,
    ) -> Result<PolicyDecision> {
        info!(policy = %policy_path, "Evaluating policy");

        let url = format!("{}/v1/data/{}", self.base_url, policy_path);

        let request_body = PolicyRequest { input };

        let response = self
            .client
            .post(&url)
            .json(&request_body)
            .send()
            .await?;

        if response.status().is_success() {
            let decision: PolicyResponse = response.json().await?;

            info!(
                policy = %policy_path,
                allow = ?decision.result,
                "Policy evaluated"
            );

            Ok(PolicyDecision {
                allow: decision.result.as_bool().unwrap_or(false),
                result: decision.result,
                decision_id: decision.decision_id,
            })
        } else {
            warn!(
                status = %response.status(),
                "Policy evaluation failed"
            );
            anyhow::bail!("OPA API error: {}", response.status())
        }
    }

    /// 上传策略
    #[instrument(skip(self, policy_content))]
    pub async fn upload_policy(&self, policy_id: &str, policy_content: &str) -> Result<()> {
        info!(policy_id = %policy_id, "Uploading policy");

        let url = format!("{}/v1/policies/{}", self.base_url, policy_id);

        let response = self
            .client
            .put(&url)
            .header("Content-Type", "text/plain")
            .body(policy_content.to_string())
            .send()
            .await?;

        if response.status().is_success() {
            info!(policy_id = %policy_id, "Policy uploaded");
            Ok(())
        } else {
            warn!(status = %response.status(), "Policy upload failed");
            anyhow::bail!("Failed to upload policy")
        }
    }

    /// 上传数据
    #[instrument(skip(self, data))]
    pub async fn upload_data(&self, path: &str, data: serde_json::Value) -> Result<()> {
        info!(path = %path, "Uploading data");

        let url = format!("{}/v1/data/{}", self.base_url, path);

        let response = self.client.put(&url).json(&data).send().await?;

        if response.status().is_success() {
            info!(path = %path, "Data uploaded");
            Ok(())
        } else {
            warn!(status = %response.status(), "Data upload failed");
            anyhow::bail!("Failed to upload data")
        }
    }

    /// 查询数据
    #[instrument(skip(self))]
    pub async fn query_data(&self, path: &str) -> Result<serde_json::Value> {
        info!(path = %path, "Querying data");

        let url = format!("{}/v1/data/{}", self.base_url, path);

        let response = self.client.get(&url).send().await?;

        if response.status().is_success() {
            let data_response: DataResponse = response.json().await?;
            Ok(data_response.result)
        } else {
            warn!(status = %response.status(), "Data query failed");
            anyhow::bail!("Failed to query data")
        }
    }
}

/// 策略请求
#[derive(Debug, Serialize, Deserialize)]
struct PolicyRequest {
    input: serde_json::Value,
}

/// 策略响应
#[derive(Debug, Serialize, Deserialize)]
struct PolicyResponse {
    result: serde_json::Value,
    #[serde(skip_serializing_if = "Option::is_none")]
    decision_id: Option<String>,
}

/// 数据响应
#[derive(Debug, Serialize, Deserialize)]
struct DataResponse {
    result: serde_json::Value,
}

/// 策略决策
#[derive(Debug, Clone)]
pub struct PolicyDecision {
    pub allow: bool,
    pub result: serde_json::Value,
    pub decision_id: Option<String>,
}
```

### 4.2 数据API

```rust
// src/client/policy.rs
use anyhow::Result;
use serde_json::json;
use tracing::{info, instrument};

/// 策略评估器
pub struct PolicyEvaluator {
    client: OpaClient,
}

impl PolicyEvaluator {
    pub fn new(client: OpaClient) -> Self {
        Self { client }
    }

    /// 评估Kubernetes准入
    #[instrument(skip(self, request))]
    pub async fn evaluate_admission(
        &self,
        request: &serde_json::Value,
    ) -> Result<AdmissionDecision> {
        info!("Evaluating admission request");

        let input = json!({
            "request": request
        });

        let decision = self
            .client
            .evaluate_policy("kubernetes/admission", input)
            .await?;

        // 解析拒绝原因
        let deny_messages = decision.result
            .get("deny")
            .and_then(|v| v.as_array())
            .map(|arr| {
                arr.iter()
                    .filter_map(|v| v.as_str().map(String::from))
                    .collect()
            })
            .unwrap_or_default();

        Ok(AdmissionDecision {
            allowed: deny_messages.is_empty(),
            deny_messages,
        })
    }

    /// 评估API授权
    #[instrument(skip(self))]
    pub async fn evaluate_api_auth(
        &self,
        user_id: &str,
        method: &str,
        path: &str,
    ) -> Result<bool> {
        info!(user_id = %user_id, method = %method, path = %path, "Evaluating API authorization");

        let input = json!({
            "user": {
                "id": user_id
            },
            "method": method,
            "path": path
        });

        let decision = self
            .client
            .evaluate_policy("api/authz/allow", input)
            .await?;

        Ok(decision.allow)
    }

    /// 评估数据过滤
    #[instrument(skip(self, query))]
    pub async fn evaluate_data_filter(
        &self,
        user_id: &str,
        query: &str,
    ) -> Result<serde_json::Value> {
        info!(user_id = %user_id, "Evaluating data filter");

        let input = json!({
            "user": {
                "id": user_id
            },
            "query": query
        });

        let decision = self
            .client
            .evaluate_policy("data/filter", input)
            .await?;

        Ok(decision.result)
    }
}

/// 准入决策
#[derive(Debug, Clone)]
pub struct AdmissionDecision {
    pub allowed: bool,
    pub deny_messages: Vec<String>,
}
```

### 4.3 批量决策

```rust
// src/client/policy.rs (续)
use futures::future::join_all;

impl PolicyEvaluator {
    /// 批量评估
    #[instrument(skip(self, requests))]
    pub async fn evaluate_batch(
        &self,
        policy_path: &str,
        requests: Vec<serde_json::Value>,
    ) -> Result<Vec<PolicyDecision>> {
        info!(
            policy = %policy_path,
            count = %requests.len(),
            "Evaluating batch requests"
        );

        // 并发评估
        let futures: Vec<_> = requests
            .into_iter()
            .map(|input| self.client.evaluate_policy(policy_path, input))
            .collect();

        let results = join_all(futures).await;

        // 收集成功的结果
        let decisions: Vec<PolicyDecision> = results
            .into_iter()
            .filter_map(|r| r.ok())
            .collect();

        info!(success_count = %decisions.len(), "Batch evaluation complete");

        Ok(decisions)
    }
}
```

---

## 5. Kubernetes Admission Controller

### 5.1 Webhook 配置

```yaml
# config/webhook-configuration.yaml
apiVersion: admissionregistration.k8s.io/v1
kind: ValidatingWebhookConfiguration
metadata:
  name: opa-validating-webhook
webhooks:
  - name: validating-webhook.openpolicyagent.org
    clientConfig:
      service:
        name: opa
        namespace: opa
        path: "/v1/admit"
      caBundle: LS0tLS1CRUdJTi... # Base64 encoded CA cert
    rules:
      - operations: ["CREATE", "UPDATE"]
        apiGroups: ["*"]
        apiVersions: ["*"]
        resources: ["pods", "deployments", "services"]
    admissionReviewVersions: ["v1", "v1beta1"]
    sideEffects: None
    failurePolicy: Fail
    timeoutSeconds: 5
```

### 5.2 Pod 安全策略

```rust
// src/admission/webhook.rs
use anyhow::Result;
use axum::{
    extract::Json,
    http::StatusCode,
    routing::post,
    Router,
};
use serde::{Deserialize, Serialize};
use tracing::{info, warn, instrument};

/// Admission Webhook 服务器
pub struct AdmissionWebhook {
    opa_client: OpaClient,
}

impl AdmissionWebhook {
    pub fn new(opa_client: OpaClient) -> Self {
        Self { opa_client }
    }

    /// 启动 Webhook 服务器
    pub async fn start(self, addr: &str) -> Result<()> {
        let app = Router::new()
            .route("/v1/admit", post(handle_admission))
            .with_state(self);

        let listener = tokio::net::TcpListener::bind(addr).await?;
        
        info!(addr = %addr, "Starting admission webhook server");

        axum::serve(listener, app).await?;

        Ok(())
    }

    /// 处理准入请求
    #[instrument(skip(self, request))]
    async fn validate_admission(&self, request: AdmissionRequest) -> Result<AdmissionResponse> {
        info!(
            kind = %request.request.kind.kind,
            namespace = ?request.request.namespace,
            name = ?request.request.name,
            operation = %request.request.operation,
            "Validating admission request"
        );

        // 构造 OPA 输入
        let input = serde_json::json!({
            "request": request.request
        });

        // 评估策略
        let decision = self.opa_client
            .evaluate_policy("kubernetes/admission", input)
            .await?;

        // 解析拒绝原因
        let deny_messages: Vec<String> = decision.result
            .get("deny")
            .and_then(|v| v.as_array())
            .map(|arr| {
                arr.iter()
                    .filter_map(|v| v.as_str().map(String::from))
                    .collect()
            })
            .unwrap_or_default();

        let allowed = deny_messages.is_empty();

        info!(
            allowed = %allowed,
            deny_count = %deny_messages.len(),
            "Admission decision made"
        );

        Ok(AdmissionResponse {
            uid: request.request.uid,
            allowed,
            status: if allowed {
                None
            } else {
                Some(AdmissionStatus {
                    code: 403,
                    message: deny_messages.join("; "),
                })
            },
        })
    }
}

async fn handle_admission(
    axum::extract::State(webhook): axum::extract::State<AdmissionWebhook>,
    Json(review): Json<AdmissionReview>,
) -> Result<Json<AdmissionReview>, StatusCode> {
    match webhook.validate_admission(review.request).await {
        Ok(response) => {
            Ok(Json(AdmissionReview {
                api_version: "admission.k8s.io/v1".to_string(),
                kind: "AdmissionReview".to_string(),
                response,
            }))
        }
        Err(e) => {
            warn!(error = %e, "Admission validation failed");
            Err(StatusCode::INTERNAL_SERVER_ERROR)
        }
    }
}

/// Admission Review
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AdmissionReview {
    pub api_version: String,
    pub kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub request: Option<AdmissionRequest>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub response: Option<AdmissionResponse>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AdmissionRequest {
    pub uid: String,
    pub kind: GroupVersionKind,
    pub resource: GroupVersionResource,
    pub sub_resource: Option<String>,
    pub request_kind: Option<GroupVersionKind>,
    pub request_resource: Option<GroupVersionResource>,
    pub name: Option<String>,
    pub namespace: Option<String>,
    pub operation: String,
    pub user_info: UserInfo,
    pub object: Option<serde_json::Value>,
    pub old_object: Option<serde_json::Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GroupVersionKind {
    pub group: String,
    pub version: String,
    pub kind: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GroupVersionResource {
    pub group: String,
    pub version: String,
    pub resource: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct UserInfo {
    pub username: String,
    pub uid: String,
    #[serde(default)]
    pub groups: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AdmissionResponse {
    pub uid: String,
    pub allowed: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub status: Option<AdmissionStatus>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AdmissionStatus {
    pub code: u16,
    pub message: String,
}
```

### 5.3 RBAC 策略

**Rego 策略示例**:

```rego
# policies/kubernetes/rbac.rego
package kubernetes.rbac

import rego.v1

# 默认拒绝
default allow := false

# 允许读取自己namespace的资源
allow if {
    input.request.operation == "GET"
    input.request.namespace == user_namespace
}

# 允许admin角色
allow if {
    "system:masters" in input.request.user_info.groups
}

# 允许特定ServiceAccount
allow if {
    input.request.user_info.username == "system:serviceaccount:kube-system:deployment-controller"
}

# 获取用户namespace
user_namespace := ns {
    username := input.request.user_info.username
    startswith(username, "system:serviceaccount:")
    parts := split(username, ":")
    ns := parts[2]
}

# 拒绝跨namespace访问
deny[msg] {
    input.request.operation in ["CREATE", "UPDATE", "DELETE"]
    input.request.namespace != user_namespace
    not is_admin
    msg := "Cross-namespace access denied"
}

is_admin if {
    "system:masters" in input.request.user_info.groups
}
```

---

## 6. 数据过滤与转换

### 6.1 JSON 数据过滤

```rego
# policies/data_filter/json_filter.rego
package data.filter

import rego.v1

# 根据用户角色过滤数据
filtered_data[item] {
    item := input.data[_]
    allowed_for_user(item, input.user)
}

allowed_for_user(item, user) if {
    user.role == "admin"
}

allowed_for_user(item, user) if {
    item.owner == user.id
}

allowed_for_user(item, user) if {
    item.visibility == "public"
}

# 过滤敏感字段
sanitized_item[key] = value {
    item := input.data[_]
    [key, value] := walk(item)[_]
    not is_sensitive_field(key)
}

is_sensitive_field(field) if {
    field in ["password", "ssn", "credit_card"]
}
```

**Rust 实现**:

```rust
// src/client/policy.rs (续)
impl PolicyEvaluator {
    /// 数据过滤
    #[instrument(skip(self, data))]
    pub async fn filter_data(
        &self,
        user_id: &str,
        role: &str,
        data: Vec<serde_json::Value>,
    ) -> Result<Vec<serde_json::Value>> {
        info!(user_id = %user_id, role = %role, "Filtering data");

        let input = json!({
            "user": {
                "id": user_id,
                "role": role
            },
            "data": data
        });

        let decision = self
            .client
            .evaluate_policy("data/filter/filtered_data", input)
            .await?;

        // 提取过滤后的数据
        let filtered = decision.result
            .as_array()
            .cloned()
            .unwrap_or_default();

        info!(
            original_count = %data.len(),
            filtered_count = %filtered.len(),
            "Data filtered"
        );

        Ok(filtered)
    }
}
```

### 6.2 GraphQL 授权

```rego
# policies/data_filter/graphql.rego
package graphql.authz

import rego.v1

# 允许的字段
allowed_fields[field] {
    input.query.field := field
    field_allowed_for_user(field, input.user)
}

field_allowed_for_user(field, user) if {
    user.role == "admin"
}

field_allowed_for_user(field, user) if {
    field in public_fields
}

public_fields := ["id", "name", "description"]

# 行级安全
allowed_rows[row] {
    row := data.database.users[_]
    row_allowed_for_user(row, input.user)
}

row_allowed_for_user(row, user) if {
    row.owner == user.id
}

row_allowed_for_user(row, user) if {
    user.role == "admin"
}
```

### 6.3 微服务授权

```rust
// src/admission/validator.rs
use anyhow::Result;
use tracing::{info, instrument};

/// 微服务授权验证器
pub struct MicroserviceAuthorizer {
    evaluator: PolicyEvaluator,
}

impl MicroserviceAuthorizer {
    pub fn new(evaluator: PolicyEvaluator) -> Self {
        Self { evaluator }
    }

    /// 验证API访问
    #[instrument(skip(self))]
    pub async fn authorize_api_call(
        &self,
        user_id: &str,
        service: &str,
        method: &str,
        path: &str,
    ) -> Result<AuthorizationDecision> {
        info!(
            user_id = %user_id,
            service = %service,
            method = %method,
            path = %path,
            "Authorizing API call"
        );

        let input = json!({
            "user": {
                "id": user_id
            },
            "service": service,
            "method": method,
            "path": path
        });

        let decision = self.evaluator
            .client
            .evaluate_policy("microservices/authz/allow", input)
            .await?;

        Ok(AuthorizationDecision {
            allowed: decision.allow,
            reason: if !decision.allow {
                Some("Access denied by policy".to_string())
            } else {
                None
            },
        })
    }

    /// 验证服务间通信
    #[instrument(skip(self))]
    pub async fn authorize_service_to_service(
        &self,
        source_service: &str,
        target_service: &str,
        operation: &str,
    ) -> Result<bool> {
        info!(
            source = %source_service,
            target = %target_service,
            operation = %operation,
            "Authorizing service-to-service call"
        );

        let input = json!({
            "source": source_service,
            "target": target_service,
            "operation": operation
        });

        let decision = self.evaluator
            .client
            .evaluate_policy("microservices/service_mesh/allow", input)
            .await?;

        Ok(decision.allow)
    }
}

#[derive(Debug, Clone)]
pub struct AuthorizationDecision {
    pub allowed: bool,
    pub reason: Option<String>,
}
```

---

## 7. Bundle 分发

### 7.1 Bundle 格式

OPA Bundle 是包含策略和数据的压缩包：

```text
bundle.tar.gz
├── .manifest
├── policies/
│   ├── kubernetes/
│   │   ├── admission.rego
│   │   └── rbac.rego
│   └── api/
│       └── authz.rego
└── data/
    └── config.json
```

**Manifest 文件**:

```json
{
  "revision": "v1.2.3",
  "roots": ["kubernetes", "api"],
  "metadata": {
    "authors": ["security-team"],
    "description": "Production policies",
    "organization": "my-org"
  }
}
```

### 7.2 Bundle 服务器

```rust
// src/bundle/server.rs
use anyhow::Result;
use axum::{
    extract::{Path, State},
    http::StatusCode,
    response::IntoResponse,
    routing::get,
    Router,
};
use std::sync::Arc;
use tokio::sync::RwLock;
use tracing::{info, instrument};

/// Bundle 服务器
pub struct BundleServer {
    bundles: Arc<RwLock<BundleStore>>,
}

impl BundleServer {
    pub fn new() -> Self {
        Self {
            bundles: Arc::new(RwLock::new(BundleStore::new())),
        }
    }

    /// 启动服务器
    pub async fn start(self, addr: &str) -> Result<()> {
        let app = Router::new()
            .route("/bundles/:name", get(get_bundle))
            .route("/bundles/:name/manifest", get(get_manifest))
            .with_state(self);

        let listener = tokio::net::TcpListener::bind(addr).await?;
        
        info!(addr = %addr, "Starting bundle server");

        axum::serve(listener, app).await?;

        Ok(())
    }

    /// 上传 Bundle
    #[instrument(skip(self, bundle_data))]
    pub async fn upload_bundle(&self, name: String, bundle_data: Vec<u8>) -> Result<()> {
        info!(bundle_name = %name, size = %bundle_data.len(), "Uploading bundle");

        let bundle = Bundle {
            name: name.clone(),
            data: bundle_data,
            revision: chrono::Utc::now().timestamp().to_string(),
            uploaded_at: chrono::Utc::now(),
        };

        let mut store = self.bundles.write().await;
        store.save(name, bundle)?;

        Ok(())
    }
}

async fn get_bundle(
    State(server): State<BundleServer>,
    Path(name): Path<String>,
) -> impl IntoResponse {
    let store = server.bundles.read().await;

    match store.get(&name) {
        Some(bundle) => {
            info!(bundle_name = %name, "Serving bundle");
            (StatusCode::OK, bundle.data.clone())
        }
        None => {
            (StatusCode::NOT_FOUND, Vec::new())
        }
    }
}

async fn get_manifest(
    State(server): State<BundleServer>,
    Path(name): Path<String>,
) -> impl IntoResponse {
    let store = server.bundles.read().await;

    match store.get(&name) {
        Some(bundle) => {
            let manifest = json!({
                "revision": bundle.revision,
                "uploaded_at": bundle.uploaded_at.to_rfc3339()
            });

            (StatusCode::OK, serde_json::to_string(&manifest).unwrap())
        }
        None => {
            (StatusCode::NOT_FOUND, String::new())
        }
    }
}

/// Bundle 存储
struct BundleStore {
    bundles: std::collections::HashMap<String, Bundle>,
}

impl BundleStore {
    fn new() -> Self {
        Self {
            bundles: std::collections::HashMap::new(),
        }
    }

    fn save(&mut self, name: String, bundle: Bundle) -> Result<()> {
        self.bundles.insert(name, bundle);
        Ok(())
    }

    fn get(&self, name: &str) -> Option<&Bundle> {
        self.bundles.get(name)
    }
}

#[derive(Debug, Clone)]
struct Bundle {
    name: String,
    data: Vec<u8>,
    revision: String,
    uploaded_at: chrono::DateTime<chrono::Utc>,
}
```

### 7.3 Bundle 签名

```rust
// src/bundle/signer.rs
use anyhow::Result;
use base64::{Engine as _, engine::general_purpose};
use sha2::{Digest, Sha256};
use tracing::{info, instrument};

/// Bundle 签名器
pub struct BundleSigner {
    private_key: Vec<u8>,
}

impl BundleSigner {
    pub fn new(private_key: Vec<u8>) -> Self {
        Self { private_key }
    }

    /// 签名 Bundle
    #[instrument(skip(self, bundle_data))]
    pub fn sign_bundle(&self, bundle_data: &[u8]) -> Result<String> {
        info!(size = %bundle_data.len(), "Signing bundle");

        // 计算哈希
        let mut hasher = Sha256::new();
        hasher.update(bundle_data);
        let hash = hasher.finalize();

        // 签名（简化示例，实际应使用 RSA/ECDSA）
        let signature = self.sign_hash(&hash)?;

        // Base64 编码
        let signature_b64 = general_purpose::STANDARD.encode(signature);

        info!("Bundle signed successfully");

        Ok(signature_b64)
    }

    /// 验证签名
    #[instrument(skip(self, bundle_data, signature))]
    pub fn verify_signature(&self, bundle_data: &[u8], signature: &str) -> Result<bool> {
        info!("Verifying bundle signature");

        // 计算哈希
        let mut hasher = Sha256::new();
        hasher.update(bundle_data);
        let hash = hasher.finalize();

        // 解码签名
        let signature_bytes = general_purpose::STANDARD.decode(signature)?;

        // 验证（简化示例）
        let expected_signature = self.sign_hash(&hash)?;

        Ok(signature_bytes == expected_signature)
    }

    fn sign_hash(&self, hash: &[u8]) -> Result<Vec<u8>> {
        // 简化示例：实际应使用密码学库
        // 例如: ring, rsa, ed25519-dalek
        Ok(hash.to_vec())
    }
}
```

---

## 8. 决策日志

### 8.1 日志收集

```rust
// src/decision/logger.rs
use anyhow::Result;
use serde::{Deserialize, Serialize};
use tracing::{info, instrument};

/// 决策日志记录器
pub struct DecisionLogger {
    log_file: Option<std::path::PathBuf>,
}

impl DecisionLogger {
    pub fn new(log_file: Option<std::path::PathBuf>) -> Self {
        Self { log_file }
    }

    /// 记录决策
    #[instrument(skip(self, decision))]
    pub async fn log_decision(&self, decision: &Decision) -> Result<()> {
        info!(
            policy = %decision.policy_path,
            allowed = %decision.allowed,
            "Logging decision"
        );

        let log_entry = DecisionLog {
            timestamp: chrono::Utc::now().to_rfc3339(),
            decision_id: decision.decision_id.clone(),
            policy_path: decision.policy_path.clone(),
            input: decision.input.clone(),
            result: decision.result.clone(),
            allowed: decision.allowed,
            metrics: DecisionMetrics {
                evaluation_time_ms: decision.evaluation_time.as_millis() as u64,
            },
        };

        // 写入文件
        if let Some(path) = &self.log_file {
            let json = serde_json::to_string(&log_entry)?;
            tokio::fs::write(path, json.as_bytes()).await?;
        }

        // 或发送到远程服务
        // self.send_to_collector(&log_entry).await?;

        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct Decision {
    pub decision_id: Option<String>,
    pub policy_path: String,
    pub input: serde_json::Value,
    pub result: serde_json::Value,
    pub allowed: bool,
    pub evaluation_time: std::time::Duration,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DecisionLog {
    pub timestamp: String,
    pub decision_id: Option<String>,
    pub policy_path: String,
    pub input: serde_json::Value,
    pub result: serde_json::Value,
    pub allowed: bool,
    pub metrics: DecisionMetrics,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DecisionMetrics {
    pub evaluation_time_ms: u64,
}
```

### 8.2 审计跟踪

```rust
// src/decision/audit.rs
use anyhow::Result;
use serde::{Deserialize, Serialize};
use tracing::{info, warn, instrument};

/// 审计追踪
pub struct AuditTrail {
    storage: AuditStorage,
}

impl AuditTrail {
    pub fn new(storage: AuditStorage) -> Self {
        Self { storage }
    }

    /// 记录审计事件
    #[instrument(skip(self))]
    pub async fn record_audit_event(&self, event: AuditEvent) -> Result<()> {
        info!(
            event_type = ?event.event_type,
            actor = %event.actor,
            "Recording audit event"
        );

        self.storage.save(event).await?;

        Ok(())
    }

    /// 查询审计日志
    #[instrument(skip(self))]
    pub async fn query_audit_logs(
        &self,
        start_time: chrono::DateTime<chrono::Utc>,
        end_time: chrono::DateTime<chrono::Utc>,
        filters: Option<AuditFilters>,
    ) -> Result<Vec<AuditEvent>> {
        info!(
            start = %start_time,
            end = %end_time,
            "Querying audit logs"
        );

        self.storage.query(start_time, end_time, filters).await
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuditEvent {
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub event_type: AuditEventType,
    pub actor: String,
    pub resource: String,
    pub action: String,
    pub result: AuditResult,
    pub metadata: serde_json::Value,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AuditEventType {
    PolicyEvaluation,
    PolicyUpdate,
    DataUpdate,
    BundleDownload,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum AuditResult {
    Success,
    Failure,
    Denied,
}

#[derive(Debug, Clone)]
pub struct AuditFilters {
    pub event_type: Option<AuditEventType>,
    pub actor: Option<String>,
    pub result: Option<AuditResult>,
}

/// 审计存储
pub struct AuditStorage;

impl AuditStorage {
    pub async fn save(&self, _event: AuditEvent) -> Result<()> {
        // 实际实现：保存到数据库或对象存储
        Ok(())
    }

    pub async fn query(
        &self,
        _start: chrono::DateTime<chrono::Utc>,
        _end: chrono::DateTime<chrono::Utc>,
        _filters: Option<AuditFilters>,
    ) -> Result<Vec<AuditEvent>> {
        // 实际实现：从数据库查询
        Ok(Vec::new())
    }
}
```

### 8.3 合规报告

```rust
// src/decision/audit.rs (续)
use std::collections::HashMap;

impl AuditTrail {
    /// 生成合规报告
    #[instrument(skip(self))]
    pub async fn generate_compliance_report(
        &self,
        start_time: chrono::DateTime<chrono::Utc>,
        end_time: chrono::DateTime<chrono::Utc>,
    ) -> Result<ComplianceReport> {
        info!("Generating compliance report");

        let events = self.query_audit_logs(start_time, end_time, None).await?;

        let mut report = ComplianceReport {
            period_start: start_time,
            period_end: end_time,
            total_evaluations: 0,
            denied_count: 0,
            policy_violations: HashMap::new(),
            top_actors: Vec::new(),
        };

        for event in &events {
            if matches!(event.event_type, AuditEventType::PolicyEvaluation) {
                report.total_evaluations += 1;

                if matches!(event.result, AuditResult::Denied) {
                    report.denied_count += 1;

                    let counter = report.policy_violations
                        .entry(event.resource.clone())
                        .or_insert(0);
                    *counter += 1;
                }
            }
        }

        // 统计最活跃的用户
        let mut actor_counts: HashMap<String, u32> = HashMap::new();
        for event in &events {
            *actor_counts.entry(event.actor.clone()).or_insert(0) += 1;
        }

        let mut sorted_actors: Vec<_> = actor_counts.into_iter().collect();
        sorted_actors.sort_by(|a, b| b.1.cmp(&a.1));
        report.top_actors = sorted_actors.into_iter().take(10).collect();

        info!(
            total_evaluations = %report.total_evaluations,
            denied_count = %report.denied_count,
            "Compliance report generated"
        );

        Ok(report)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComplianceReport {
    pub period_start: chrono::DateTime<chrono::Utc>,
    pub period_end: chrono::DateTime<chrono::Utc>,
    pub total_evaluations: u64,
    pub denied_count: u64,
    pub policy_violations: HashMap<String, u32>,
    pub top_actors: Vec<(String, u32)>,
}
```

---

## 9. OTLP 可观测性集成

### 9.1 分布式追踪

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

/// 追踪策略评估
#[instrument(skip(policy_path, input), fields(policy = %policy_path))]
pub async fn trace_policy_evaluation(
    policy_path: &str,
    input: &serde_json::Value,
) -> Result<()> {
    let tracer = global::tracer("opa");
    
    let mut span = tracer
        .span_builder("opa.policy.evaluate")
        .with_kind(SpanKind::Internal)
        .start(&tracer);

    span.set_attribute(KeyValue::new("opa.policy.path", policy_path.to_string()));
    span.set_attribute(KeyValue::new("opa.input.size", input.to_string().len() as i64));

    Ok(())
}
```

### 9.2 指标监控

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

/// OPA 指标
pub struct OpaMetrics {
    meter: Meter,
    evaluations_counter: Counter<u64>,
    evaluation_duration: Histogram<f64>,
    policy_loads: Counter<u64>,
    bundle_downloads: Counter<u64>,
}

impl OpaMetrics {
    /// 初始化指标
    #[instrument]
    pub fn new(service_name: &str, otlp_endpoint: &str) -> Result<Self> {
        info!(
            service_name = %service_name,
            otlp_endpoint = %otlp_endpoint,
            "Initializing OPA metrics"
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

        let meter = provider.meter("opa");

        let evaluations_counter = meter
            .u64_counter("opa.evaluations.total")
            .with_description("Total number of policy evaluations")
            .build();

        let evaluation_duration = meter
            .f64_histogram("opa.evaluation.duration")
            .with_description("Policy evaluation duration")
            .with_unit("s")
            .build();

        let policy_loads = meter
            .u64_counter("opa.policy.loads")
            .with_description("Number of policy loads")
            .build();

        let bundle_downloads = meter
            .u64_counter("opa.bundle.downloads")
            .with_description("Number of bundle downloads")
            .build();

        info!("OPA metrics initialized");

        Ok(Self {
            meter,
            evaluations_counter,
            evaluation_duration,
            policy_loads,
            bundle_downloads,
        })
    }

    /// 记录评估
    pub fn record_evaluation(&self, policy_path: &str, allowed: bool, duration: f64) {
        let attributes = vec![
            KeyValue::new("policy", policy_path.to_string()),
            KeyValue::new("allowed", allowed.to_string()),
        ];

        self.evaluations_counter.add(1, &attributes);
        self.evaluation_duration.record(duration, &attributes);
    }

    /// 记录策略加载
    pub fn record_policy_load(&self, policy_id: &str, success: bool) {
        let attributes = vec![
            KeyValue::new("policy_id", policy_id.to_string()),
            KeyValue::new("success", success.to_string()),
        ];
        self.policy_loads.add(1, &attributes);
    }

    /// 记录Bundle下载
    pub fn record_bundle_download(&self, bundle_name: &str, success: bool) {
        let attributes = vec![
            KeyValue::new("bundle", bundle_name.to_string()),
            KeyValue::new("success", success.to_string()),
        ];
        self.bundle_downloads.add(1, &attributes);
    }
}
```

### 9.3 性能分析

```rust
// src/observability/metrics.rs (续)
use std::time::Instant;

/// 性能分析器
pub struct PerformanceAnalyzer {
    metrics: OpaMetrics,
}

impl PerformanceAnalyzer {
    pub fn new(metrics: OpaMetrics) -> Self {
        Self { metrics }
    }

    /// 测量评估性能
    #[instrument(skip(self, f))]
    pub async fn measure_evaluation<F, T>(&self, policy_path: &str, f: F) -> Result<T>
    where
        F: std::future::Future<Output = Result<T>>,
    {
        let start = Instant::now();

        let result = f.await;

        let duration = start.elapsed().as_secs_f64();

        let success = result.is_ok();
        self.metrics.record_evaluation(policy_path, success, duration);

        result
    }
}
```

---

## 10. 生产部署实践

### 10.1 Kubernetes 部署

```yaml
# deploy/opa.yaml
apiVersion: v1
kind: Namespace
metadata:
  name: opa

---
apiVersion: v1
kind: ConfigMap
metadata:
  name: opa-config
  namespace: opa
data:
  config.yaml: |
    services:
      - name: bundle
        url: https://bundle-server/bundles
    bundles:
      authz:
        service: bundle
        resource: /production/authz
        polling:
          min_delay_seconds: 60
          max_delay_seconds: 120
    decision_logs:
      service: bundle
      reporting:
        min_delay_seconds: 300
        max_delay_seconds: 600

---
apiVersion: apps/v1
kind: Deployment
metadata:
  name: opa
  namespace: opa
spec:
  replicas: 3
  selector:
    matchLabels:
      app: opa
  template:
    metadata:
      labels:
        app: opa
    spec:
      affinity:
        podAntiAffinity:
          preferredDuringSchedulingIgnoredDuringExecution:
            - weight: 100
              podAffinityTerm:
                labelSelector:
                  matchExpressions:
                    - key: app
                      operator: In
                      values: [opa]
                topologyKey: kubernetes.io/hostname
      containers:
        - name: opa
          image: openpolicyagent/opa:0.60.0
          args:
            - "run"
            - "--server"
            - "--addr=0.0.0.0:8181"
            - "--config-file=/config/config.yaml"
            - "--log-level=info"
          ports:
            - containerPort: 8181
              name: http
          volumeMounts:
            - name: config
              mountPath: /config
          livenessProbe:
            httpGet:
              path: /health
              port: 8181
            initialDelaySeconds: 10
            periodSeconds: 10
          readinessProbe:
            httpGet:
              path: /health?bundle=true
              port: 8181
            initialDelaySeconds: 10
            periodSeconds: 5
          resources:
            requests:
              memory: "256Mi"
              cpu: "250m"
            limits:
              memory: "512Mi"
              cpu: "500m"
      volumes:
        - name: config
          configMap:
            name: opa-config

---
apiVersion: v1
kind: Service
metadata:
  name: opa
  namespace: opa
spec:
  type: ClusterIP
  selector:
    app: opa
  ports:
    - port: 8181
      targetPort: 8181
      protocol: TCP
      name: http
```

### 10.2 高可用配置

**负载均衡**:

```yaml
apiVersion: v1
kind: Service
metadata:
  name: opa-lb
  namespace: opa
spec:
  type: LoadBalancer
  selector:
    app: opa
  ports:
    - port: 80
      targetPort: 8181
      protocol: TCP
  sessionAffinity: ClientIP
  sessionAffinityConfig:
    clientIP:
      timeoutSeconds: 10800
```

**HPA 自动扩缩容**:

```yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: opa-hpa
  namespace: opa
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: opa
  minReplicas: 3
  maxReplicas: 10
  metrics:
    - type: Resource
      resource:
        name: cpu
        target:
          type: Utilization
          averageUtilization: 70
    - type: Resource
      resource:
        name: memory
        target:
          type: Utilization
          averageUtilization: 80
```

### 10.3 性能优化

**缓存配置**:

```yaml
services:
  - name: bundle
    url: https://bundle-server
    credentials:
      bearer:
        token: ${BUNDLE_TOKEN}
bundles:
  authz:
    service: bundle
    resource: /bundles/production
    persist: true  # 启用持久化缓存
    polling:
      min_delay_seconds: 60
      max_delay_seconds: 120
    caching:
      max_age_seconds: 300  # 缓存有效期
```

**性能调优参数**:

```yaml
# OPA 配置优化
decision_logs:
  plugin: decision_logs_plugin
  reporting:
    min_delay_seconds: 300
    max_delay_seconds: 600
    max_decisions_per_second: 1000  # 限制日志速率
    
caching:
  inter_query_builtin_cache:
    max_size_bytes: 104857600  # 100MB缓存

plugins:
  envoy_ext_authz_grpc:
    addr: :9191
    query: data.authz.allow
    dry-run: false
```

---

## 11. 测试策略

```rust
// tests/integration_test.rs
#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_policy_evaluation() {
        let client = OpaClient::new("http://localhost:8181".to_string());

        let input = json!({
            "user": {
                "role": "admin"
            },
            "method": "GET",
            "path": "/api/users"
        });

        let decision = client
            .evaluate_policy("api/authz/allow", input)
            .await
            .unwrap();

        assert!(decision.allow);
    }

    #[tokio::test]
    async fn test_admission_webhook() {
        let opa_client = OpaClient::new("http://localhost:8181".to_string());
        let webhook = AdmissionWebhook::new(opa_client);

        let request = AdmissionRequest {
            uid: "test-123".to_string(),
            kind: GroupVersionKind {
                group: "".to_string(),
                version: "v1".to_string(),
                kind: "Pod".to_string(),
            },
            operation: "CREATE".to_string(),
            object: Some(json!({
                "spec": {
                    "containers": [{
                        "name": "nginx",
                        "image": "nginx:latest",
                        "securityContext": {
                            "privileged": true
                        }
                    }]
                }
            })),
            // ... other fields
        };

        let response = webhook.validate_admission(request).await.unwrap();

        assert!(!response.allowed);
    }

    #[tokio::test]
    async fn test_data_filtering() {
        let evaluator = PolicyEvaluator::new(
            OpaClient::new("http://localhost:8181".to_string())
        );

        let data = vec![
            json!({"id": 1, "owner": "user1"}),
            json!({"id": 2, "owner": "user2"}),
            json!({"id": 3, "visibility": "public"}),
        ];

        let filtered = evaluator
            .filter_data("user1", "user", data)
            .await
            .unwrap();

        assert_eq!(filtered.len(), 2);
    }
}
```

---

## 12. 参考资源

### 官方文档

- **Open Policy Agent**: <https://www.openpolicyagent.org/>
- **Rego Language**: <https://www.openpolicyagent.org/docs/latest/policy-language/>
- **Kubernetes Admission Control**: <https://www.openpolicyagent.org/docs/latest/kubernetes-admission-control/>

### Rust 生态

- **reqwest**: <https://docs.rs/reqwest/>
- **axum**: <https://docs.rs/axum/>
- **serde_json**: <https://docs.rs/serde_json/>

### 标准与协议

- **JSON (RFC 8259)**: <https://datatracker.ietf.org/doc/html/rfc8259>
- **JWT (RFC 7519)**: <https://datatracker.ietf.org/doc/html/rfc7519>
- **OAuth 2.0 (RFC 6749)**: <https://datatracker.ietf.org/doc/html/rfc6749>

### 云原生

- **OPA Gatekeeper**: <https://open-policy-agent.github.io/gatekeeper/>
- **Styra DAS**: <https://www.styra.com/>
- **CNCF Policy WG**: <https://github.com/cncf/tag-security>

---

**本文档提供了 Open Policy Agent 在 Rust 生态中的完整实现指南，涵盖Rego策略语言、REST API集成、Kubernetes准入控制、数据过滤、Bundle分发、决策日志、OTLP可观测性，以及生产部署实践。所有代码基于 Rust 1.90 和 OpenTelemetry 0.27，完全对齐国际标准。** 🎉
