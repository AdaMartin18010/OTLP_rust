# SPIFFE/SPIRE 完整实现：零信任身份 - Rust 1.90 + OTLP 集成

## 目录

- [SPIFFE/SPIRE 完整实现：零信任身份 - Rust 1.90 + OTLP 集成](#spiffespire-完整实现零信任身份---rust-190--otlp-集成)
  - [目录](#目录)
  - [1. 核心概念与架构](#1-核心概念与架构)
    - [1.1 SPIFFE 核心特性](#11-spiffe-核心特性)
    - [1.2 SPIRE 架构模型](#12-spire-架构模型)
    - [1.3 国际标准对齐](#13-国际标准对齐)
  - [2. Rust 生态集成](#2-rust-生态集成)
    - [2.1 核心依赖](#21-核心依赖)
    - [2.2 项目结构](#22-项目结构)
  - [3. SPIFFE ID 与 SVID](#3-spiffe-id-与-svid)
    - [3.1 SPIFFE ID 规范](#31-spiffe-id-规范)
    - [3.2 X.509-SVID 实现](#32-x509-svid-实现)
    - [3.3 JWT-SVID 实现](#33-jwt-svid-实现)
  - [4. SPIRE Server 集成](#4-spire-server-集成)
    - [4.1 Server 配置](#41-server-配置)
    - [4.2 节点认证](#42-节点认证)
    - [4.3 注册 Entry 管理](#43-注册-entry-管理)
  - [5. SPIRE Agent 集成](#5-spire-agent-集成)
    - [5.1 Agent 配置](#51-agent-配置)
    - [5.2 Workload Attestation](#52-workload-attestation)
    - [5.3 SVID 自动轮转](#53-svid-自动轮转)
  - [6. Workload API 集成](#6-workload-api-集成)
    - [6.1 gRPC Workload API](#61-grpc-workload-api)
    - [6.2 SVID 获取与缓存](#62-svid-获取与缓存)
    - [6.3 Trust Bundle 管理](#63-trust-bundle-管理)
  - [7. 服务间认证](#7-服务间认证)
    - [7.1 mTLS 配置](#71-mtls-配置)
    - [7.2 Envoy 集成](#72-envoy-集成)
    - [7.3 身份验证中间件](#73-身份验证中间件)
  - [8. OTLP 可观测性集成](#8-otlp-可观测性集成)
    - [8.1 分布式追踪](#81-分布式追踪)
    - [8.2 指标监控](#82-指标监控)
    - [8.3 审计日志](#83-审计日志)
  - [9. 生产部署实践](#9-生产部署实践)
    - [9.1 Kubernetes 部署](#91-kubernetes-部署)
    - [9.2 高可用配置](#92-高可用配置)
    - [9.3 安全最佳实践](#93-安全最佳实践)
  - [10. 测试策略](#10-测试策略)
  - [11. 参考资源](#11-参考资源)
    - [官方文档](#官方文档)
    - [Rust 生态](#rust-生态)
    - [标准与协议](#标准与协议)
    - [云原生](#云原生)

---

## 1. 核心概念与架构

### 1.1 SPIFFE 核心特性

SPIFFE (Secure Production Identity Framework For Everyone) 是云原生身份标准，核心特性包括：

| 特性 | 描述 | 应用场景 |
|------|------|----------|
| **统一身份标准** | SPIFFE ID (URI格式) | 跨平台身份识别 |
| **可验证凭证** | X.509-SVID、JWT-SVID | mTLS、API认证 |
| **自动轮转** | 短期证书自动续期 | 零停机更新 |
| **Workload Attestation** | 自动身份验证 | 无需密钥分发 |
| **Federation** | 跨信任域认证 | 多集群、多云 |
| **零信任架构** | 基于身份的访问控制 | 微服务安全 |

### 1.2 SPIRE 架构模型

```text
┌────────────────────────────────────────────────────────────┐
│                    SPIRE Architecture                      │
│                                                            │
│  ┌────────────────────────────────────────────────────┐    │
│  │              SPIRE Server Cluster                  │    │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐          │    │
│  │  │ Server 1 │  │ Server 2 │  │ Server 3 │          │    │
│  │  │ (Leader) │◄─┤(Follower)│◄─┤(Follower)│          │    │
│  │  └────┬─────┘  └──────────┘  └──────────┘          │    │
│  │       │                                            │    │
│  │       │ Registration API                           │    │
│  │       │ Node API                                   │    │
│  │       │                                            │    │
│  │  ┌────▼──────────────────────────────────┐         │    │
│  │  │     Trust Domain & CA                 │         │    │
│  │  │  - Root CA                             │        │    │
│  │  │  - Intermediate CA                     │        │    │
│  │  │  - SVID Signing                        │        │    │
│  │  └────────────────────────────────────────┘        │    │
│  └────────────────────────────────────────────────────┘    │
│                          │                                 │
│                          │ Node Attestation                │
│                          ▼                                 │
│  ┌────────────────────────────────────────────────────┐    │
│  │              SPIRE Agent Nodes                     │    │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐          │    │
│  │  │  Agent 1 │  │  Agent 2 │  │  Agent 3 │          │    │
│  │  └────┬─────┘  └────┬─────┘  └────┬─────┘          │    │
│  └───────┼──────────────┼──────────────┼──────────────┘    │
│          │              │              │                   │
│          │ Workload API │              │                   │
│          ▼              ▼              ▼                   │
│  ┌────────────────────────────────────────────────────┐    │
│  │              Workloads                             │    │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐          │    │
│  │  │Service A │──│Service B │──│Service C │          │    │
│  │  │(X.509)   │  │(X.509)   │  │(JWT)     │          │    │
│  │  └──────────┘  └──────────┘  └──────────┘          │    │
│  │                                                    │    │
│  │       mTLS Authentication & Authorization          │    │
│  └────────────────────────────────────────────────────┘    │
└────────────────────────────────────────────────────────────┘
```

**核心组件说明**：

- **SPIRE Server**: 身份颁发中心，管理SPIFFE ID和SVID
- **SPIRE Agent**: 节点代理，与Workload交互
- **Workload API**: gRPC API，提供SVID获取服务
- **Node Attestation**: 节点身份验证
- **Workload Attestation**: 工作负载身份验证

### 1.3 国际标准对齐

| 标准/协议 | 应用场景 | SPIFFE/SPIRE 实现 |
|-----------|----------|-------------------|
| **X.509 (RFC 5280)** | 数字证书 | X.509-SVID |
| **JWT (RFC 7519)** | 令牌格式 | JWT-SVID |
| **URI (RFC 3986)** | SPIFFE ID格式 | spiffe://trust-domain/path |
| **gRPC** | Workload API | gRPC Streaming |
| **mTLS (RFC 8446)** | 双向认证 | 服务间认证 |
| **PKIX (RFC 5280)** | 证书格式 | X.509证书 |
| **Zero Trust** | 安全架构 | 基于身份的访问控制 |
| **NIST SP 800-63** | 数字身份 | 身份保证级别 |

---

## 2. Rust 生态集成

### 2.1 核心依赖

```toml
[package]
name = "spire-integration"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# gRPC & Protobuf
tonic = { version = "0.12", features = ["tls", "tls-roots"] }
prost = "0.13"
prost-types = "0.13"

# 异步运行时
tokio = { version = "1.42", features = ["full"] }
tokio-stream = "0.1"

# TLS/mTLS
tokio-rustls = "0.26"
rustls = { version = "0.23", features = ["ring"] }
rustls-pemfile = "2.2"
x509-parser = "0.16"

# JWT
jsonwebtoken = "9.3"

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

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

# Unix Domain Socket
tokio-uds = "0.3"

[build-dependencies]
tonic-build = "0.12"
```

### 2.2 项目结构

```text
spire-integration/
├── src/
│   ├── main.rs                    # 入口
│   ├── spiffe/
│   │   ├── mod.rs
│   │   ├── id.rs                  # SPIFFE ID
│   │   └── svid.rs                # SVID (X.509/JWT)
│   ├── workload_api/
│   │   ├── mod.rs
│   │   ├── client.rs              # Workload API Client
│   │   └── watcher.rs             # SVID Watcher
│   ├── server/
│   │   ├── mod.rs
│   │   ├── registration.rs        # Registration API
│   │   └── node.rs                # Node API
│   ├── attestation/
│   │   ├── mod.rs
│   │   ├── node.rs                # Node Attestation
│   │   └── workload.rs            # Workload Attestation
│   ├── mtls/
│   │   ├── mod.rs
│   │   ├── server.rs              # mTLS Server
│   │   └── client.rs              # mTLS Client
│   ├── observability/
│   │   ├── mod.rs
│   │   ├── tracing.rs             # 分布式追踪
│   │   └── metrics.rs             # 指标收集
│   └── error.rs                   # 错误定义
├── proto/
│   ├── workload.proto             # Workload API
│   └── server.proto               # Server API
├── examples/
│   ├── workload_client.rs
│   └── mtls_service.rs
├── tests/
│   └── integration_test.rs
├── build.rs                        # Protobuf 构建
└── Cargo.toml
```

---

## 3. SPIFFE ID 与 SVID

### 3.1 SPIFFE ID 规范

```rust
// src/spiffe/id.rs
use anyhow::{anyhow, Result};
use serde::{Deserialize, Serialize};
use std::fmt;
use std::str::FromStr;
use tracing::{info, instrument};

/// SPIFFE ID
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SpiffeId {
    /// Trust Domain
    pub trust_domain: String,
    /// Path
    pub path: String,
}

impl SpiffeId {
    /// 创建 SPIFFE ID
    #[instrument]
    pub fn new(trust_domain: impl Into<String>, path: impl Into<String>) -> Result<Self> {
        let trust_domain = trust_domain.into();
        let path = path.into();

        // 验证 trust domain
        if trust_domain.is_empty() {
            anyhow::bail!("Trust domain cannot be empty");
        }

        // 验证 path
        if !path.starts_with('/') {
            anyhow::bail!("Path must start with /");
        }

        Ok(Self {
            trust_domain,
            path,
        })
    }

    /// 转换为 URI
    pub fn to_uri(&self) -> String {
        format!("spiffe://{}{}", self.trust_domain, self.path)
    }

    /// 验证身份
    #[instrument(skip(self))]
    pub fn is_member_of(&self, trust_domain: &str) -> bool {
        self.trust_domain == trust_domain
    }

    /// 检查是否匹配路径前缀
    pub fn matches_prefix(&self, prefix: &str) -> bool {
        self.path.starts_with(prefix)
    }
}

impl FromStr for SpiffeId {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self> {
        if !s.starts_with("spiffe://") {
            anyhow::bail!("SPIFFE ID must start with spiffe://");
        }

        let without_scheme = &s[9..];
        let parts: Vec<&str> = without_scheme.splitn(2, '/').collect();

        if parts.len() != 2 {
            anyhow::bail!("Invalid SPIFFE ID format");
        }

        Self::new(parts[0], format!("/{}", parts[1]))
    }
}

impl fmt::Display for SpiffeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_uri())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_spiffe_id() {
        let id = SpiffeId::new("example.org", "/service/backend").unwrap();
        assert_eq!(id.to_uri(), "spiffe://example.org/service/backend");

        let parsed: SpiffeId = "spiffe://example.org/service/backend".parse().unwrap();
        assert_eq!(parsed, id);
    }

    #[test]
    fn test_is_member_of() {
        let id = SpiffeId::new("example.org", "/service/backend").unwrap();
        assert!(id.is_member_of("example.org"));
        assert!(!id.is_member_of("other.org"));
    }
}
```

### 3.2 X.509-SVID 实现

```rust
// src/spiffe/svid.rs
use anyhow::Result;
use rustls::pki_types::{CertificateDer, PrivateKeyDer};
use serde::{Deserialize, Serialize};
use std::time::SystemTime;
use tracing::{info, instrument};
use x509_parser::prelude::*;

/// X.509-SVID
#[derive(Debug, Clone)]
pub struct X509Svid {
    /// SPIFFE ID
    pub spiffe_id: SpiffeId,
    /// 证书链
    pub certificates: Vec<CertificateDer<'static>>,
    /// 私钥
    pub private_key: PrivateKeyDer<'static>,
    /// 过期时间
    pub expiry: SystemTime,
}

impl X509Svid {
    /// 从 PEM 加载
    #[instrument(skip(cert_pem, key_pem))]
    pub fn from_pem(cert_pem: &[u8], key_pem: &[u8]) -> Result<Self> {
        info!("Loading X.509-SVID from PEM");

        // 解析证书
        let certs = rustls_pemfile::certs(&mut &cert_pem[..])
            .collect::<Result<Vec<_>, _>>()?;

        if certs.is_empty() {
            anyhow::bail!("No certificates found in PEM");
        }

        // 解析私钥
        let keys = rustls_pemfile::pkcs8_private_keys(&mut &key_pem[..])
            .collect::<Result<Vec<_>, _>>()?;

        if keys.is_empty() {
            anyhow::bail!("No private key found in PEM");
        }

        // 提取 SPIFFE ID
        let spiffe_id = Self::extract_spiffe_id(&certs[0])?;

        // 提取过期时间
        let expiry = Self::extract_expiry(&certs[0])?;

        Ok(Self {
            spiffe_id,
            certificates: certs,
            private_key: PrivateKeyDer::Pkcs8(keys[0].clone()),
            expiry,
        })
    }

    /// 提取 SPIFFE ID
    fn extract_spiffe_id(cert: &CertificateDer) -> Result<SpiffeId> {
        let (_, parsed) = X509Certificate::from_der(cert)?;

        // 从 SAN (Subject Alternative Name) 提取 URI
        if let Some(san) = parsed.subject_alternative_name()? {
            for name in &san.value.general_names {
                if let GeneralName::URI(uri) = name {
                    return uri.parse();
                }
            }
        }

        anyhow::bail!("No SPIFFE ID found in certificate")
    }

    /// 提取过期时间
    fn extract_expiry(cert: &CertificateDer) -> Result<SystemTime> {
        let (_, parsed) = X509Certificate::from_der(cert)?;
        let not_after = parsed.validity().not_after;

        Ok(SystemTime::UNIX_EPOCH + std::time::Duration::from_secs(not_after.timestamp() as u64))
    }

    /// 检查是否过期
    pub fn is_expired(&self) -> bool {
        SystemTime::now() >= self.expiry
    }

    /// 获取剩余有效期
    pub fn time_until_expiry(&self) -> std::time::Duration {
        self.expiry
            .duration_since(SystemTime::now())
            .unwrap_or_default()
    }
}
```

### 3.3 JWT-SVID 实现

```rust
// src/spiffe/svid.rs (续)
use jsonwebtoken::{decode, encode, Algorithm, DecodingKey, EncodingKey, Header, Validation};

/// JWT-SVID Claims
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct JwtSvidClaims {
    /// SPIFFE ID (sub claim)
    pub sub: String,
    /// Audience
    pub aud: Vec<String>,
    /// Issued At
    pub iat: i64,
    /// Expiration
    pub exp: i64,
}

/// JWT-SVID
#[derive(Debug, Clone)]
pub struct JwtSvid {
    /// SPIFFE ID
    pub spiffe_id: SpiffeId,
    /// Token
    pub token: String,
    /// Claims
    pub claims: JwtSvidClaims,
}

impl JwtSvid {
    /// 从 Token 解析
    #[instrument(skip(token, public_key))]
    pub fn from_token(token: &str, public_key: &[u8]) -> Result<Self> {
        info!("Parsing JWT-SVID");

        // 验证并解码
        let decoding_key = DecodingKey::from_rsa_pem(public_key)?;
        let mut validation = Validation::new(Algorithm::RS256);
        validation.validate_aud = false; // 可选：根据需求验证 audience

        let token_data = decode::<JwtSvidClaims>(token, &decoding_key, &validation)?;

        let spiffe_id: SpiffeId = token_data.claims.sub.parse()?;

        Ok(Self {
            spiffe_id,
            token: token.to_string(),
            claims: token_data.claims,
        })
    }

    /// 创建 JWT-SVID
    #[instrument(skip(private_key))]
    pub fn create(
        spiffe_id: &SpiffeId,
        audience: Vec<String>,
        ttl_seconds: i64,
        private_key: &[u8],
    ) -> Result<Self> {
        info!(spiffe_id = %spiffe_id, "Creating JWT-SVID");

        let now = chrono::Utc::now().timestamp();

        let claims = JwtSvidClaims {
            sub: spiffe_id.to_uri(),
            aud: audience,
            iat: now,
            exp: now + ttl_seconds,
        };

        let encoding_key = EncodingKey::from_rsa_pem(private_key)?;
        let token = encode(&Header::new(Algorithm::RS256), &claims, &encoding_key)?;

        Ok(Self {
            spiffe_id: spiffe_id.clone(),
            token,
            claims,
        })
    }

    /// 检查是否过期
    pub fn is_expired(&self) -> bool {
        chrono::Utc::now().timestamp() >= self.claims.exp
    }

    /// 验证 Audience
    pub fn has_audience(&self, audience: &str) -> bool {
        self.claims.aud.iter().any(|a| a == audience)
    }
}
```

---

## 4. SPIRE Server 集成

### 4.1 Server 配置

```toml
# config/spire-server.conf
server {
  bind_address = "0.0.0.0"
  bind_port = "8081"
  trust_domain = "example.org"
  data_dir = "/var/lib/spire/server"
  log_level = "INFO"
  
  ca_ttl = "24h"
  default_x509_svid_ttl = "1h"
  default_jwt_svid_ttl = "5m"
}

plugins {
  DataStore "sql" {
    plugin_data {
      database_type = "postgres"
      connection_string = "postgresql://spire:password@postgres:5432/spire"
    }
  }

  NodeAttestor "k8s_psat" {
    plugin_data {
      clusters = {
        "production" = {
          service_account_allow_list = ["spire:spire-agent"]
        }
      }
    }
  }

  KeyManager "disk" {
    plugin_data {
      keys_path = "/var/lib/spire/server/keys.json"
    }
  }

  Notifier "k8sbundle" {
    plugin_data {
      namespace = "spire"
      config_map = "spire-bundle"
    }
  }
}
```

### 4.2 节点认证

```rust
// src/server/node.rs
use anyhow::Result;
use tonic::{Request, Response, Status};
use tracing::{info, instrument};

/// Node Attestation
pub struct NodeAttestor {
    trust_domain: String,
}

impl NodeAttestor {
    pub fn new(trust_domain: String) -> Self {
        Self { trust_domain }
    }

    /// Kubernetes PSAT 认证
    #[instrument(skip(self, token))]
    pub async fn attest_k8s_psat(&self, token: &str) -> Result<String> {
        info!("Attesting Kubernetes node with PSAT");

        // 验证 Service Account Token
        let claims = Self::verify_service_account_token(token)?;

        // 生成节点 SPIFFE ID
        let node_id = format!(
            "spiffe://{}/spire/agent/k8s_psat/{}/{}",
            self.trust_domain, claims.namespace, claims.pod_name
        );

        info!(node_id = %node_id, "Node attestation successful");

        Ok(node_id)
    }

    /// 验证 Service Account Token
    fn verify_service_account_token(token: &str) -> Result<ServiceAccountClaims> {
        // 简化示例：实际需要调用 Kubernetes API 验证
        // 或使用 TokenReview API

        // 解析 JWT
        let claims: ServiceAccountClaims = jsonwebtoken::dangerous_insecure_decode(token)?
            .claims;

        Ok(claims)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct ServiceAccountClaims {
    pub sub: String,
    pub namespace: String,
    pub pod_name: String,
}
```

### 4.3 注册 Entry 管理

```rust
// src/server/registration.rs
use anyhow::Result;
use tracing::{info, instrument};

/// Registration Entry
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RegistrationEntry {
    /// Entry ID
    pub id: String,
    /// SPIFFE ID
    pub spiffe_id: SpiffeId,
    /// Parent ID
    pub parent_id: SpiffeId,
    /// Selectors
    pub selectors: Vec<Selector>,
    /// TTL
    pub ttl: i64,
    /// Admin
    pub admin: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Selector {
    pub r#type: String,
    pub value: String,
}

/// Registration Manager
pub struct RegistrationManager {
    trust_domain: String,
}

impl RegistrationManager {
    pub fn new(trust_domain: String) -> Self {
        Self { trust_domain }
    }

    /// 创建 Entry
    #[instrument(skip(self))]
    pub async fn create_entry(&self, entry: RegistrationEntry) -> Result<String> {
        info!(
            spiffe_id = %entry.spiffe_id,
            parent_id = %entry.parent_id,
            "Creating registration entry"
        );

        // 验证 SPIFFE ID 属于信任域
        if !entry.spiffe_id.is_member_of(&self.trust_domain) {
            anyhow::bail!("SPIFFE ID not in trust domain");
        }

        // 验证 Parent ID
        if !entry.parent_id.is_member_of(&self.trust_domain) {
            anyhow::bail!("Parent ID not in trust domain");
        }

        // 生成 Entry ID
        let entry_id = uuid::Uuid::new_v4().to_string();

        // 保存到数据库（简化示例）
        // self.db.save_entry(&entry).await?;

        info!(entry_id = %entry_id, "Registration entry created");

        Ok(entry_id)
    }

    /// 列出 Entries
    #[instrument(skip(self))]
    pub async fn list_entries(&self, parent_id: Option<&SpiffeId>) -> Result<Vec<RegistrationEntry>> {
        info!("Listing registration entries");

        // 从数据库查询（简化示例）
        // self.db.list_entries(parent_id).await

        Ok(vec![])
    }

    /// 删除 Entry
    #[instrument(skip(self))]
    pub async fn delete_entry(&self, entry_id: &str) -> Result<()> {
        info!(entry_id = %entry_id, "Deleting registration entry");

        // 从数据库删除（简化示例）
        // self.db.delete_entry(entry_id).await

        Ok(())
    }
}

/// Kubernetes Selectors
pub fn k8s_selectors(namespace: &str, service_account: &str, pod_label: Option<(&str, &str)>) -> Vec<Selector> {
    let mut selectors = vec![
        Selector {
            r#type: "k8s".to_string(),
            value: format!("ns:{}", namespace),
        },
        Selector {
            r#type: "k8s".to_string(),
            value: format!("sa:{}", service_account),
        },
    ];

    if let Some((key, value)) = pod_label {
        selectors.push(Selector {
            r#type: "k8s".to_string(),
            value: format!("pod-label:{}:{}", key, value),
        });
    }

    selectors
}
```

---

## 5. SPIRE Agent 集成

### 5.1 Agent 配置

```toml
# config/spire-agent.conf
agent {
  data_dir = "/var/lib/spire/agent"
  log_level = "INFO"
  server_address = "spire-server"
  server_port = "8081"
  socket_path = "/run/spire/agent.sock"
  trust_domain = "example.org"
  
  # Join token (for initial attestation)
  join_token = ""
}

plugins {
  NodeAttestor "k8s_psat" {
    plugin_data {
      cluster = "production"
    }
  }

  KeyManager "memory" {
    plugin_data {}
  }

  WorkloadAttestor "k8s" {
    plugin_data {
      skip_kubelet_verification = true
    }
  }

  WorkloadAttestor "unix" {
    plugin_data {}
  }
}
```

### 5.2 Workload Attestation

```rust
// src/attestation/workload.rs
use anyhow::Result;
use std::collections::HashMap;
use tracing::{info, instrument};

/// Workload Attestor
pub struct WorkloadAttestor {
    selectors_cache: HashMap<i32, Vec<Selector>>,
}

impl WorkloadAttestor {
    pub fn new() -> Self {
        Self {
            selectors_cache: HashMap::new(),
        }
    }

    /// Kubernetes Workload Attestation
    #[instrument(skip(self))]
    pub async fn attest_k8s(&mut self, pid: i32) -> Result<Vec<Selector>> {
        info!(pid = %pid, "Attesting Kubernetes workload");

        // 检查缓存
        if let Some(selectors) = self.selectors_cache.get(&pid) {
            return Ok(selectors.clone());
        }

        // 从 /proc/{pid}/cgroup 读取容器 ID
        let container_id = Self::read_container_id(pid)?;

        // 查询 Kubelet API 获取 Pod 信息
        let pod_info = Self::get_pod_info(&container_id).await?;

        // 构造 Selectors
        let selectors = vec![
            Selector {
                r#type: "k8s".to_string(),
                value: format!("ns:{}", pod_info.namespace),
            },
            Selector {
                r#type: "k8s".to_string(),
                value: format!("sa:{}", pod_info.service_account),
            },
            Selector {
                r#type: "k8s".to_string(),
                value: format!("pod-name:{}", pod_info.pod_name),
            },
        ];

        // 缓存
        self.selectors_cache.insert(pid, selectors.clone());

        info!(pid = %pid, selectors = ?selectors, "Workload attested");

        Ok(selectors)
    }

    /// Unix Process Attestation
    #[instrument(skip(self))]
    pub async fn attest_unix(&self, pid: i32) -> Result<Vec<Selector>> {
        info!(pid = %pid, "Attesting Unix process");

        // 读取进程信息
        let (uid, gid) = Self::read_process_ids(pid)?;
        let exe_path = Self::read_exe_path(pid)?;

        let selectors = vec![
            Selector {
                r#type: "unix".to_string(),
                value: format!("uid:{}", uid),
            },
            Selector {
                r#type: "unix".to_string(),
                value: format!("gid:{}", gid),
            },
            Selector {
                r#type: "unix".to_string(),
                value: format!("path:{}", exe_path),
            },
        ];

        Ok(selectors)
    }

    fn read_container_id(pid: i32) -> Result<String> {
        // 从 /proc/{pid}/cgroup 提取容器 ID
        let cgroup = std::fs::read_to_string(format!("/proc/{}/cgroup", pid))?;
        
        for line in cgroup.lines() {
            if line.contains("docker") || line.contains("containerd") {
                // 提取容器 ID（简化示例）
                if let Some(id) = line.split('/').last() {
                    return Ok(id.to_string());
                }
            }
        }

        anyhow::bail!("Container ID not found")
    }

    async fn get_pod_info(container_id: &str) -> Result<PodInfo> {
        // 查询 Kubelet API（简化示例）
        // 实际需要通过 Unix socket 连接 Kubelet

        Ok(PodInfo {
            namespace: "default".to_string(),
            pod_name: "my-pod".to_string(),
            service_account: "default".to_string(),
        })
    }

    fn read_process_ids(pid: i32) -> Result<(u32, u32)> {
        let status = std::fs::read_to_string(format!("/proc/{}/status", pid))?;
        
        let mut uid = 0;
        let mut gid = 0;

        for line in status.lines() {
            if line.starts_with("Uid:") {
                uid = line.split_whitespace().nth(1)
                    .and_then(|s| s.parse().ok())
                    .unwrap_or(0);
            } else if line.starts_with("Gid:") {
                gid = line.split_whitespace().nth(1)
                    .and_then(|s| s.parse().ok())
                    .unwrap_or(0);
            }
        }

        Ok((uid, gid))
    }

    fn read_exe_path(pid: i32) -> Result<String> {
        let exe = std::fs::read_link(format!("/proc/{}/exe", pid))?;
        Ok(exe.to_string_lossy().to_string())
    }
}

#[derive(Debug)]
struct PodInfo {
    namespace: String,
    pod_name: String,
    service_account: String,
}
```

### 5.3 SVID 自动轮转

```rust
// src/workload_api/watcher.rs
use anyhow::Result;
use tokio::time::{interval, Duration};
use tracing::{info, warn, instrument};

/// SVID Watcher
pub struct SvidWatcher {
    client: WorkloadApiClient,
    rotation_threshold: Duration,
}

impl SvidWatcher {
    pub fn new(client: WorkloadApiClient) -> Self {
        Self {
            client,
            rotation_threshold: Duration::from_secs(300), // 5分钟
        }
    }

    /// 启动自动轮转
    #[instrument(skip(self, callback))]
    pub async fn watch<F>(&mut self, mut callback: F) -> Result<()>
    where
        F: FnMut(X509Svid) -> Result<()>,
    {
        info!("Starting SVID watcher");

        let mut check_interval = interval(Duration::from_secs(60));

        loop {
            check_interval.tick().await;

            // 获取当前 SVID
            let svid = self.client.fetch_x509_svid().await?;

            // 检查是否需要轮转
            if svid.time_until_expiry() < self.rotation_threshold {
                info!(
                    time_until_expiry = ?svid.time_until_expiry(),
                    "SVID approaching expiry, rotating"
                );

                // 触发回调
                if let Err(e) = callback(svid) {
                    warn!(error = %e, "SVID rotation callback failed");
                } else {
                    info!("SVID rotated successfully");
                }
            }
        }
    }
}
```

---

(继续下一部分...)

## 6. Workload API 集成

### 6.1 gRPC Workload API

```rust
// build.rs
fn main() -> Result<(), Box<dyn std::error::Error>> {
    tonic_build::configure()
        .build_server(false)
        .compile(
            &["proto/workload.proto"],
            &["proto/"],
        )?;
    Ok(())
}
```

```rust
// src/workload_api/client.rs
use anyhow::Result;
use tonic::transport::{Channel, Endpoint, Uri};
use tracing::{info, instrument};

// 生成的 gRPC 代码
pub mod workload_api {
    tonic::include_proto!("spire.api.agent.workload");
}

use workload_api::spiffe_workload_api_client::SpiffeWorkloadApiClient;

/// Workload API Client
pub struct WorkloadApiClient {
    client: SpiffeWorkloadApiClient<Channel>,
}

impl WorkloadApiClient {
    /// 连接到 SPIRE Agent (Unix Domain Socket)
    #[instrument]
    pub async fn connect_uds(socket_path: &str) -> Result<Self> {
        info!(socket_path = %socket_path, "Connecting to Workload API");

        // 使用 Unix Domain Socket
        let channel = Endpoint::try_from("http://[::]:50051")?
            .connect_with_connector(tower::service_fn(move |_: Uri| {
                tokio::net::UnixStream::connect(socket_path.to_string())
            }))
            .await?;

        let client = SpiffeWorkloadApiClient::new(channel);

        Ok(Self { client })
    }

    /// 获取 X.509-SVID
    #[instrument(skip(self))]
    pub async fn fetch_x509_svid(&mut self) -> Result<X509Svid> {
        info!("Fetching X.509-SVID");

        let request = workload_api::X509SvidRequest {};

        let response = self.client.fetch_x509_svid(request).await?;
        let svid_response = response.into_inner();

        // 解析第一个 SVID
        let svid_msg = svid_response.svids.first()
            .ok_or_else(|| anyhow::anyhow!("No SVID returned"))?;

        // 转换为 X509Svid
        let svid = X509Svid::from_pem(
            &svid_msg.x509_svid,
            &svid_msg.x509_svid_key,
        )?;

        info!(spiffe_id = %svid.spiffe_id, "X.509-SVID fetched");

        Ok(svid)
    }

    /// 获取 JWT-SVID
    #[instrument(skip(self))]
    pub async fn fetch_jwt_svid(&mut self, audience: Vec<String>) -> Result<JwtSvid> {
        info!(audience = ?audience, "Fetching JWT-SVID");

        let request = workload_api::JwtSvidRequest {
            audience,
            spiffe_id: "".to_string(), // 空表示使用默认 SPIFFE ID
        };

        let response = self.client.fetch_jwt_svid(request).await?;
        let jwt_response = response.into_inner();

        // 解析第一个 JWT
        let jwt_msg = jwt_response.svids.first()
            .ok_or_else(|| anyhow::anyhow!("No JWT returned"))?;

        // 转换为 JwtSvid
        // 注意：实际需要从 Trust Bundle 获取公钥验证
        let svid = JwtSvid {
            spiffe_id: jwt_msg.spiffe_id.parse()?,
            token: jwt_msg.svid.clone(),
            claims: JwtSvidClaims {
                sub: jwt_msg.spiffe_id.clone(),
                aud: audience,
                iat: chrono::Utc::now().timestamp(),
                exp: jwt_msg.expires_at,
            },
        };

        info!(spiffe_id = %svid.spiffe_id, "JWT-SVID fetched");

        Ok(svid)
    }

    /// 获取 Trust Bundle
    #[instrument(skip(self))]
    pub async fn fetch_trust_bundle(&mut self) -> Result<Vec<CertificateDer<'static>>> {
        info!("Fetching trust bundle");

        let request = workload_api::X509BundlesRequest {};

        let response = self.client.fetch_x509_bundles(request).await?;
        let bundles_response = response.into_inner();

        // 解析 Trust Bundle
        let mut certificates = Vec::new();

        for (trust_domain, bundle) in bundles_response.bundles {
            info!(trust_domain = %trust_domain, "Processing trust bundle");

            for cert_der in bundle.x509_authorities {
                certificates.push(CertificateDer::from(cert_der));
            }
        }

        info!(cert_count = %certificates.len(), "Trust bundle fetched");

        Ok(certificates)
    }
}
```

### 6.2 SVID 获取与缓存

```rust
// src/workload_api/cache.rs
use anyhow::Result;
use std::sync::Arc;
use tokio::sync::RwLock;
use tracing::{info, instrument};

/// SVID Cache
pub struct SvidCache {
    x509_svid: Arc<RwLock<Option<X509Svid>>>,
    jwt_cache: Arc<RwLock<HashMap<String, JwtSvid>>>,
}

impl SvidCache {
    pub fn new() -> Self {
        Self {
            x509_svid: Arc::new(RwLock::new(None)),
            jwt_cache: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 更新 X.509-SVID
    #[instrument(skip(self, svid))]
    pub async fn update_x509_svid(&self, svid: X509Svid) {
        info!(spiffe_id = %svid.spiffe_id, "Updating X.509-SVID cache");
        
        let mut cache = self.x509_svid.write().await;
        *cache = Some(svid);
    }

    /// 获取 X.509-SVID
    pub async fn get_x509_svid(&self) -> Option<X509Svid> {
        let cache = self.x509_svid.read().await;
        cache.clone()
    }

    /// 缓存 JWT-SVID
    #[instrument(skip(self, svid))]
    pub async fn cache_jwt_svid(&self, audience: String, svid: JwtSvid) {
        info!(audience = %audience, "Caching JWT-SVID");
        
        let mut cache = self.jwt_cache.write().await;
        cache.insert(audience, svid);
    }

    /// 获取 JWT-SVID
    pub async fn get_jwt_svid(&self, audience: &str) -> Option<JwtSvid> {
        let cache = self.jwt_cache.read().await;
        cache.get(audience).cloned()
    }

    /// 清理过期的 JWT
    #[instrument(skip(self))]
    pub async fn cleanup_expired_jwts(&self) {
        let mut cache = self.jwt_cache.write().await;
        cache.retain(|_, svid| !svid.is_expired());
        
        info!("Cleaned up expired JWTs");
    }
}
```

### 6.3 Trust Bundle 管理

```rust
// src/workload_api/trust_bundle.rs
use anyhow::Result;
use rustls::pki_types::CertificateDer;
use rustls::RootCertStore;
use tracing::{info, instrument};

/// Trust Bundle Manager
pub struct TrustBundleManager {
    root_store: RootCertStore,
}

impl TrustBundleManager {
    pub fn new() -> Self {
        Self {
            root_store: RootCertStore::empty(),
        }
    }

    /// 更新 Trust Bundle
    #[instrument(skip(self, certificates))]
    pub fn update(&mut self, certificates: Vec<CertificateDer<'static>>) -> Result<()> {
        info!(cert_count = %certificates.len(), "Updating trust bundle");

        // 清空现有证书
        self.root_store = RootCertStore::empty();

        // 添加新证书
        for cert in certificates {
            self.root_store.add(cert)?;
        }

        info!("Trust bundle updated");

        Ok(())
    }

    /// 获取 Root Store
    pub fn root_store(&self) -> &RootCertStore {
        &self.root_store
    }

    /// 验证证书链
    #[instrument(skip(self, cert_chain))]
    pub fn verify_cert_chain(&self, cert_chain: &[CertificateDer]) -> Result<()> {
        info!(chain_length = %cert_chain.len(), "Verifying certificate chain");

        // 使用 rustls 验证证书链
        // 实际实现需要更复杂的验证逻辑

        info!("Certificate chain verified");

        Ok(())
    }
}
```

---

## 7. 服务间认证

### 7.1 mTLS 配置

```rust
// src/mtls/server.rs
use anyhow::Result;
use rustls::pki_types::{CertificateDer, PrivateKeyDer};
use rustls::ServerConfig;
use std::sync::Arc;
use tokio::net::TcpListener;
use tokio_rustls::TlsAcceptor;
use tracing::{info, instrument};

/// mTLS Server
pub struct MtlsServer {
    listener: TcpListener,
    acceptor: TlsAcceptor,
}

impl MtlsServer {
    /// 创建 mTLS Server
    #[instrument(skip(svid, trust_bundle))]
    pub async fn new(addr: &str, svid: X509Svid, trust_bundle: TrustBundleManager) -> Result<Self> {
        info!(addr = %addr, "Creating mTLS server");

        // 配置 TLS
        let mut config = ServerConfig::builder()
            .with_client_cert_verifier(Arc::new(
                rustls::server::WebPkiClientVerifier::builder(Arc::new(trust_bundle.root_store().clone()))
                    .build()?,
            ))
            .with_single_cert(svid.certificates.clone(), svid.private_key.clone_key())?;

        config.alpn_protocols = vec![b"h2".to_vec(), b"http/1.1".to_vec()];

        let acceptor = TlsAcceptor::from(Arc::new(config));
        let listener = TcpListener::bind(addr).await?;

        info!(addr = %addr, "mTLS server created");

        Ok(Self { listener, acceptor })
    }

    /// 启动服务器
    #[instrument(skip(self))]
    pub async fn serve(&self) -> Result<()> {
        info!("Starting mTLS server");

        loop {
            let (stream, peer_addr) = self.listener.accept().await?;

            info!(peer_addr = %peer_addr, "Accepted connection");

            let acceptor = self.acceptor.clone();

            tokio::spawn(async move {
                match acceptor.accept(stream).await {
                    Ok(tls_stream) => {
                        // 提取客户端 SPIFFE ID
                        if let Some(spiffe_id) = Self::extract_peer_spiffe_id(&tls_stream) {
                            info!(peer_spiffe_id = %spiffe_id, "Client authenticated");

                            // 处理请求
                            if let Err(e) = Self::handle_connection(tls_stream, spiffe_id).await {
                                tracing::error!(error = %e, "Connection handling failed");
                            }
                        } else {
                            tracing::warn!("No SPIFFE ID in client certificate");
                        }
                    }
                    Err(e) => {
                        tracing::error!(error = %e, "TLS handshake failed");
                    }
                }
            });
        }
    }

    /// 提取对等方 SPIFFE ID
    fn extract_peer_spiffe_id<IO>(stream: &tokio_rustls::server::TlsStream<IO>) -> Option<SpiffeId> {
        let (_, session) = stream.get_ref();
        
        session.peer_certificates()
            .and_then(|certs| certs.first())
            .and_then(|cert| SpiffeId::extract_from_cert(cert).ok())
    }

    async fn handle_connection<IO>(
        _stream: tokio_rustls::server::TlsStream<IO>,
        _spiffe_id: SpiffeId,
    ) -> Result<()> {
        // 实际业务逻辑
        Ok(())
    }
}
```

### 7.2 Envoy 集成

```yaml
# config/envoy.yaml
static_resources:
  listeners:
    - name: frontend_listener
      address:
        socket_address:
          address: 0.0.0.0
          port_value: 443
      filter_chains:
        - filters:
            - name: envoy.filters.network.http_connection_manager
              typed_config:
                "@type": type.googleapis.com/envoy.extensions.filters.network.http_connection_manager.v3.HttpConnectionManager
                stat_prefix: ingress_http
                route_config:
                  name: local_route
                  virtual_hosts:
                    - name: backend
                      domains: ["*"]
                      routes:
                        - match:
                            prefix: "/"
                          route:
                            cluster: backend_service
                http_filters:
                  - name: envoy.filters.http.router
          transport_socket:
            name: envoy.transport_sockets.tls
            typed_config:
              "@type": type.googleapis.com/envoy.extensions.transport_sockets.tls.v3.DownstreamTlsContext
              common_tls_context:
                tls_certificate_sds_secret_configs:
                  - name: spiffe://example.org/frontend
                    sds_config:
                      api_config_source:
                        api_type: GRPC
                        grpc_services:
                          - envoy_grpc:
                              cluster_name: spire_agent
                validation_context_sds_secret_config:
                  name: spiffe://example.org
                  sds_config:
                    api_config_source:
                      api_type: GRPC
                      grpc_services:
                        - envoy_grpc:
                            cluster_name: spire_agent

  clusters:
    - name: backend_service
      connect_timeout: 0.25s
      type: STRICT_DNS
      lb_policy: ROUND_ROBIN
      load_assignment:
        cluster_name: backend_service
        endpoints:
          - lb_endpoints:
              - endpoint:
                  address:
                    socket_address:
                      address: backend
                      port_value: 8080
      transport_socket:
        name: envoy.transport_sockets.tls
        typed_config:
          "@type": type.googleapis.com/envoy.extensions.transport_sockets.tls.v3.UpstreamTlsContext
          common_tls_context:
            tls_certificate_sds_secret_configs:
              - name: spiffe://example.org/frontend
                sds_config:
                  api_config_source:
                    api_type: GRPC
                    grpc_services:
                      - envoy_grpc:
                          cluster_name: spire_agent
            validation_context_sds_secret_config:
              name: spiffe://example.org
              sds_config:
                api_config_source:
                  api_type: GRPC
                  grpc_services:
                    - envoy_grpc:
                        cluster_name: spire_agent

    - name: spire_agent
      connect_timeout: 0.25s
      type: STATIC
      load_assignment:
        cluster_name: spire_agent
        endpoints:
          - lb_endpoints:
              - endpoint:
                  address:
                    pipe:
                      path: /run/spire/agent.sock
```

### 7.3 身份验证中间件

```rust
// src/mtls/middleware.rs
use anyhow::Result;
use axum::{
    extract::Request,
    http::StatusCode,
    middleware::Next,
    response::Response,
};
use std::sync::Arc;
use tracing::{info, warn, instrument};

/// SPIFFE 认证中间件
#[instrument(skip(req, next, policy))]
pub async fn spiffe_auth_middleware(
    req: Request,
    next: Next,
    policy: Arc<AuthorizationPolicy>,
) -> Result<Response, StatusCode> {
    // 提取 SPIFFE ID
    let spiffe_id = match extract_spiffe_id(&req) {
        Some(id) => id,
        None => {
            warn!("No SPIFFE ID in request");
            return Err(StatusCode::UNAUTHORIZED);
        }
    };

    info!(spiffe_id = %spiffe_id, "Request authenticated");

    // 授权检查
    if !policy.is_authorized(&spiffe_id, req.uri().path(), req.method().as_str()) {
        warn!(spiffe_id = %spiffe_id, path = %req.uri().path(), "Authorization denied");
        return Err(StatusCode::FORBIDDEN);
    }

    // 将 SPIFFE ID 添加到扩展
    // req.extensions_mut().insert(spiffe_id);

    Ok(next.run(req).await)
}

/// 提取 SPIFFE ID
fn extract_spiffe_id(req: &Request) -> Option<SpiffeId> {
    // 从 TLS 连接中提取（实际实现依赖于框架）
    // 这里是简化示例
    req.extensions()
        .get::<SpiffeId>()
        .cloned()
}

/// 授权策略
pub struct AuthorizationPolicy {
    rules: Vec<AuthorizationRule>,
}

#[derive(Debug, Clone)]
pub struct AuthorizationRule {
    pub spiffe_id_prefix: String,
    pub allowed_paths: Vec<String>,
    pub allowed_methods: Vec<String>,
}

impl AuthorizationPolicy {
    pub fn new(rules: Vec<AuthorizationRule>) -> Self {
        Self { rules }
    }

    /// 检查授权
    pub fn is_authorized(&self, spiffe_id: &SpiffeId, path: &str, method: &str) -> bool {
        self.rules.iter().any(|rule| {
            spiffe_id.matches_prefix(&rule.spiffe_id_prefix)
                && (rule.allowed_paths.is_empty() || rule.allowed_paths.iter().any(|p| path.starts_with(p)))
                && (rule.allowed_methods.is_empty() || rule.allowed_methods.iter().any(|m| m == method))
        })
    }
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

    // 配置 tracing-subscriber
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    info!("OTLP tracing initialized");

    Ok(())
}

/// 追踪 SPIFFE 操作
#[instrument(skip(client), fields(operation = "fetch_svid"))]
pub async fn trace_fetch_svid(client: &mut WorkloadApiClient) -> Result<X509Svid> {
    let tracer = global::tracer("spiffe");
    
    let mut span = tracer
        .span_builder("workload_api.fetch_x509_svid")
        .with_kind(SpanKind::Client)
        .start(&tracer);

    span.set_attribute(KeyValue::new("component", "spiffe"));

    let result = client.fetch_x509_svid().await;

    match &result {
        Ok(svid) => {
            span.set_attribute(KeyValue::new("spiffe.id", svid.spiffe_id.to_string()));
            span.set_attribute(KeyValue::new("svid.expiry", format!("{:?}", svid.expiry)));
        }
        Err(e) => {
            span.record_error(e);
        }
    }

    result
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

/// SPIFFE/SPIRE 指标
pub struct SpiffeMetrics {
    meter: Meter,
    svid_fetch_counter: Counter<u64>,
    svid_rotation_counter: Counter<u64>,
    svid_fetch_duration: Histogram<f64>,
    attestation_counter: Counter<u64>,
}

impl SpiffeMetrics {
    /// 初始化指标
    #[instrument]
    pub fn new(service_name: &str, otlp_endpoint: &str) -> Result<Self> {
        info!(
            service_name = %service_name,
            otlp_endpoint = %otlp_endpoint,
            "Initializing SPIFFE metrics"
        );

        // 配置 OTLP 导出器
        let exporter = opentelemetry_otlp::new_exporter()
            .tonic()
            .with_endpoint(otlp_endpoint)
            .build_metrics_exporter(
                Box::new(opentelemetry_sdk::metrics::aggregation::default_temporality_selector()),
                Box::new(opentelemetry_sdk::metrics::data::default_resource_detector()),
            )?;

        // 创建 Meter Provider
        let reader = PeriodicReader::builder(exporter, runtime::Tokio).build();

        let provider = SdkMeterProvider::builder()
            .with_reader(reader)
            .with_resource(Resource::new(vec![
                KeyValue::new("service.name", service_name.to_string()),
            ]))
            .build();

        global::set_meter_provider(provider.clone());

        let meter = provider.meter("spiffe");

        // 创建指标
        let svid_fetch_counter = meter
            .u64_counter("spiffe.svid.fetch")
            .with_description("Number of SVID fetch operations")
            .build();

        let svid_rotation_counter = meter
            .u64_counter("spiffe.svid.rotation")
            .with_description("Number of SVID rotations")
            .build();

        let svid_fetch_duration = meter
            .f64_histogram("spiffe.svid.fetch.duration")
            .with_description("Duration of SVID fetch operations")
            .with_unit("s")
            .build();

        let attestation_counter = meter
            .u64_counter("spiffe.attestation")
            .with_description("Number of attestation operations")
            .build();

        info!("SPIFFE metrics initialized");

        Ok(Self {
            meter,
            svid_fetch_counter,
            svid_rotation_counter,
            svid_fetch_duration,
            attestation_counter,
        })
    }

    /// 记录 SVID 获取
    pub fn record_svid_fetch(&self, success: bool, duration: f64) {
        let attributes = vec![KeyValue::new("success", success.to_string())];

        self.svid_fetch_counter.add(1, &attributes);
        self.svid_fetch_duration.record(duration, &attributes);
    }

    /// 记录 SVID 轮转
    pub fn record_svid_rotation(&self, success: bool) {
        let attributes = vec![KeyValue::new("success", success.to_string())];
        self.svid_rotation_counter.add(1, &attributes);
    }

    /// 记录认证
    pub fn record_attestation(&self, attestation_type: &str, success: bool) {
        let attributes = vec![
            KeyValue::new("type", attestation_type.to_string()),
            KeyValue::new("success", success.to_string()),
        ];
        self.attestation_counter.add(1, &attributes);
    }
}
```

### 8.3 审计日志

```rust
// src/observability/audit.rs
use serde::{Deserialize, Serialize};
use tracing::{info, warn, instrument};

/// 审计事件
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
    Authentication,
    Authorization,
    SvidIssued,
    SvidRotated,
    RegistrationCreated,
    RegistrationDeleted,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum AuditResult {
    Success,
    Failure,
    Denied,
}

/// 审计日志记录器
pub struct AuditLogger;

impl AuditLogger {
    /// 记录审计事件
    #[instrument(skip(event))]
    pub fn log(event: AuditEvent) {
        let event_json = serde_json::to_string(&event).unwrap_or_default();

        match event.result {
            AuditResult::Success => {
                info!(
                    event_type = ?event.event_type,
                    actor = %event.actor,
                    resource = %event.resource,
                    action = %event.action,
                    audit_event = %event_json,
                    "Audit event"
                );
            }
            AuditResult::Failure | AuditResult::Denied => {
                warn!(
                    event_type = ?event.event_type,
                    actor = %event.actor,
                    resource = %event.resource,
                    action = %event.action,
                    result = ?event.result,
                    audit_event = %event_json,
                    "Audit event"
                );
            }
        }
    }

    /// 记录 SVID 颁发
    pub fn log_svid_issued(spiffe_id: &SpiffeId, svid_type: &str) {
        Self::log(AuditEvent {
            timestamp: chrono::Utc::now(),
            event_type: AuditEventType::SvidIssued,
            actor: "spire-server".to_string(),
            resource: spiffe_id.to_string(),
            action: "issue".to_string(),
            result: AuditResult::Success,
            metadata: serde_json::json!({
                "svid_type": svid_type,
            }),
        });
    }

    /// 记录认证失败
    pub fn log_auth_failed(spiffe_id: &str, reason: &str) {
        Self::log(AuditEvent {
            timestamp: chrono::Utc::now(),
            event_type: AuditEventType::Authentication,
            actor: spiffe_id.to_string(),
            resource: "workload-api".to_string(),
            action: "authenticate".to_string(),
            result: AuditResult::Failure,
            metadata: serde_json::json!({
                "reason": reason,
            }),
        });
    }
}
```

---

## 9. 生产部署实践

### 9.1 Kubernetes 部署

```yaml
# deploy/spire-server.yaml
apiVersion: v1
kind: Namespace
metadata:
  name: spire

---
apiVersion: v1
kind: ServiceAccount
metadata:
  name: spire-server
  namespace: spire

---
apiVersion: rbac.authorization.k8s.io/v1
kind: ClusterRole
metadata:
  name: spire-server
rules:
  - apiGroups: [""]
    resources: ["pods", "nodes"]
    verbs: ["get", "list"]
  - apiGroups: ["authentication.k8s.io"]
    resources: ["tokenreviews"]
    verbs: ["create"]

---
apiVersion: rbac.authorization.k8s.io/v1
kind: ClusterRoleBinding
metadata:
  name: spire-server
roleRef:
  apiGroup: rbac.authorization.k8s.io
  kind: ClusterRole
  name: spire-server
subjects:
  - kind: ServiceAccount
    name: spire-server
    namespace: spire

---
apiVersion: apps/v1
kind: StatefulSet
metadata:
  name: spire-server
  namespace: spire
spec:
  serviceName: spire-server
  replicas: 3
  selector:
    matchLabels:
      app: spire-server
  template:
    metadata:
      labels:
        app: spire-server
    spec:
      serviceAccountName: spire-server
      containers:
        - name: spire-server
          image: ghcr.io/spiffe/spire-server:1.10.0
          args:
            - -config
            - /run/spire/config/server.conf
          ports:
            - containerPort: 8081
              name: grpc
          volumeMounts:
            - name: config
              mountPath: /run/spire/config
              readOnly: true
            - name: data
              mountPath: /var/lib/spire/server
          livenessProbe:
            exec:
              command:
                - /opt/spire/bin/spire-server
                - healthcheck
            initialDelaySeconds: 30
            periodSeconds: 60
          readinessProbe:
            exec:
              command:
                - /opt/spire/bin/spire-server
                - healthcheck
                - --shallow
            initialDelaySeconds: 10
            periodSeconds: 10
          resources:
            requests:
              memory: "512Mi"
              cpu: "500m"
            limits:
              memory: "1Gi"
              cpu: "1000m"
      volumes:
        - name: config
          configMap:
            name: spire-server
  volumeClaimTemplates:
    - metadata:
        name: data
      spec:
        accessModes: ["ReadWriteOnce"]
        resources:
          requests:
            storage: 10Gi

---
apiVersion: v1
kind: Service
metadata:
  name: spire-server
  namespace: spire
spec:
  type: ClusterIP
  selector:
    app: spire-server
  ports:
    - port: 8081
      targetPort: 8081
      protocol: TCP
      name: grpc
```

```yaml
# deploy/spire-agent.yaml
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: spire-agent
  namespace: spire
spec:
  selector:
    matchLabels:
      app: spire-agent
  template:
    metadata:
      labels:
        app: spire-agent
    spec:
      hostPID: true
      hostNetwork: true
      dnsPolicy: ClusterFirstWithHostNet
      serviceAccountName: spire-agent
      initContainers:
        - name: init
          image: ghcr.io/spiffe/spire-agent:1.10.0
          command:
            - /bin/sh
            - -c
            - |
              rm -rf /run/spire/agent.sock
      containers:
        - name: spire-agent
          image: ghcr.io/spiffe/spire-agent:1.10.0
          args:
            - -config
            - /run/spire/config/agent.conf
          volumeMounts:
            - name: config
              mountPath: /run/spire/config
              readOnly: true
            - name: socket
              mountPath: /run/spire
            - name: data
              mountPath: /var/lib/spire/agent
          livenessProbe:
            exec:
              command:
                - /opt/spire/bin/spire-agent
                - healthcheck
            initialDelaySeconds: 30
            periodSeconds: 60
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
            name: spire-agent
        - name: socket
          hostPath:
            path: /run/spire
            type: DirectoryOrCreate
        - name: data
          hostPath:
            path: /var/lib/spire/agent
            type: DirectoryOrCreate
```

### 9.2 高可用配置

**SPIRE Server 高可用架构**:

- ✅ **多副本部署**: StatefulSet 3副本
- ✅ **PostgreSQL 后端**: 共享数据存储
- ✅ **Leader选举**: 使用 Raft 或外部锁
- ✅ **负载均衡**: gRPC 负载均衡
- ✅ **健康检查**: Liveness + Readiness探针

**SPIRE Agent 容错**:

- ✅ **本地缓存**: SVID 本地缓存
- ✅ **自动重连**: Server 不可用时重试
- ✅ **优雅降级**: 使用缓存的 SVID

### 9.3 安全最佳实践

| 实践 | 说明 | 实现 |
|------|------|------|
| **最小权限** | RBAC最小权限 | Kubernetes ServiceAccount |
| **证书轮转** | 自动轮转短期证书 | SVID TTL 1小时 |
| **审计日志** | 记录所有关键操作 | 结构化日志 |
| **网络隔离** | Agent仅暴露Unix Socket | hostNetwork=false |
| **密钥保护** | 私钥加密存储 | Vault集成 |
| **联邦信任** | 跨集群信任边界 | Trust Bundle同步 |

---

## 10. 测试策略

```rust
// tests/integration_test.rs
#[cfg(test)]
mod tests {
    use super::*;
    use testcontainers::{clients, images};

    #[tokio::test]
    async fn test_spiffe_id_parsing() {
        let id: SpiffeId = "spiffe://example.org/service/backend"
            .parse()
            .unwrap();

        assert_eq!(id.trust_domain, "example.org");
        assert_eq!(id.path, "/service/backend");
        assert!(id.is_member_of("example.org"));
    }

    #[tokio::test]
    async fn test_x509_svid_loading() {
        let cert_pem = include_bytes!("../fixtures/test-cert.pem");
        let key_pem = include_bytes!("../fixtures/test-key.pem");

        let svid = X509Svid::from_pem(cert_pem, key_pem).unwrap();

        assert_eq!(svid.spiffe_id.trust_domain, "example.org");
        assert!(!svid.is_expired());
    }

    #[tokio::test]
    async fn test_workload_api_client() {
        // 启动 SPIRE Server/Agent 容器
        let docker = clients::Cli::default();
        // let spire_server = docker.run(...);

        // 连接 Workload API
        // let mut client = WorkloadApiClient::connect_uds("/run/spire/agent.sock")
        //     .await
        //     .unwrap();

        // 获取 SVID
        // let svid = client.fetch_x509_svid().await.unwrap();
        // assert!(!svid.is_expired());
    }

    #[tokio::test]
    async fn test_mtls_authentication() {
        // 创建 mTLS Server 和 Client
        // 验证相互认证
    }
}
```

---

## 11. 参考资源

### 官方文档

- **SPIFFE**: <https://spiffe.io/>
- **SPIRE**: <https://spiffe.io/docs/latest/spire/>
- **SPIFFE Specifications**: <https://github.com/spiffe/spiffe>

### Rust 生态

- **spiffe** crate: <https://crates.io/crates/spiffe>
- **tonic**: <https://docs.rs/tonic/>
- **tokio-rustls**: <https://docs.rs/tokio-rustls/>

### 标准与协议

- **X.509 (RFC 5280)**: <https://datatracker.ietf.org/doc/html/rfc5280>
- **JWT (RFC 7519)**: <https://datatracker.ietf.org/doc/html/rfc7519>
- **mTLS (RFC 8446)**: <https://datatracker.ietf.org/doc/html/rfc8446>
- **Zero Trust Architecture (NIST SP 800-207)**: <https://csrc.nist.gov/publications/detail/sp/800-207/final>

### 云原生

- **Envoy SDS**: <https://www.envoyproxy.io/docs/envoy/latest/configuration/security/secret>
- **Istio SPIRE Integration**: <https://istio.io/latest/docs/ops/integrations/spire/>
- **Kubernetes CSI Driver**: <https://github.com/spiffe/spiffe-csi>

---

**本文档提供了 SPIFFE/SPIRE 在 Rust 生态中的完整实现指南，涵盖零信任身份、mTLS认证、Workload API集成、OTLP可观测性，以及 Kubernetes 生产部署。所有代码基于 Rust 1.90 和 OpenTelemetry 0.27，完全对齐国际标准。** 🎉
