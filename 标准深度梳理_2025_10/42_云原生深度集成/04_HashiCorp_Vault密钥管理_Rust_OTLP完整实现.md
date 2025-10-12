# HashiCorp Vault密钥管理：Rust OTLP完整实现

## 目录

- [HashiCorp Vault密钥管理：Rust OTLP完整实现](#hashicorp-vault密钥管理rust-otlp完整实现)
  - [目录](#目录)
  - [1. HashiCorp Vault核心概念](#1-hashicorp-vault核心概念)
    - [1.1 架构组件](#11-架构组件)
    - [1.2 核心功能](#12-核心功能)
    - [1.3 应用场景](#13-应用场景)
  - [2. Vault Rust客户端集成](#2-vault-rust客户端集成)
    - [2.1 依赖配置](#21-依赖配置)
    - [2.2 客户端初始化](#22-客户端初始化)
  - [3. 认证方法实现](#3-认证方法实现)
    - [3.1 Token认证](#31-token认证)
    - [3.2 AppRole认证](#32-approle认证)
    - [3.3 Kubernetes认证](#33-kubernetes认证)
  - [4. KV Secrets Engine操作](#4-kv-secrets-engine操作)
    - [4.1 读写秘密](#41-读写秘密)
    - [4.2 版本控制](#42-版本控制)
  - [5. 动态秘密生成](#5-动态秘密生成)
    - [5.1 数据库动态凭证](#51-数据库动态凭证)
    - [5.2 自动续租](#52-自动续租)
  - [6. 加密即服务(Transit)](#6-加密即服务transit)
    - [6.1 数据加密解密](#61-数据加密解密)
    - [6.2 密钥轮换](#62-密钥轮换)
  - [7. PKI证书管理](#7-pki证书管理)
    - [7.1 证书签发](#71-证书签发)
    - [7.2 自动更新](#72-自动更新)
  - [8. 策略与权限控制](#8-策略与权限控制)
    - [8.1 策略定义](#81-策略定义)
    - [8.2 策略绑定](#82-策略绑定)
  - [9. OTLP分布式追踪集成](#9-otlp分布式追踪集成)
    - [9.1 追踪配置](#91-追踪配置)
    - [9.2 操作追踪](#92-操作追踪)
  - [10. Kubernetes集成](#10-kubernetes集成)
    - [10.1 Vault Agent Injector](#101-vault-agent-injector)
    - [10.2 CSI Secret Store Driver](#102-csi-secret-store-driver)
  - [11. 高可用与灾难恢复](#11-高可用与灾难恢复)
    - [11.1 HA架构](#111-ha架构)
    - [11.2 自动Unseal](#112-自动unseal)
  - [12. 监控与审计](#12-监控与审计)
    - [12.1 Prometheus指标](#121-prometheus指标)
    - [12.2 审计日志](#122-审计日志)
  - [13. 生产环境最佳实践](#13-生产环境最佳实践)
    - [13.1 安全加固](#131-安全加固)
    - [13.2 性能优化](#132-性能优化)
  - [14. 国际标准对齐](#14-国际标准对齐)
    - [14.1 NIST密码学标准](#141-nist密码学标准)
    - [14.2 OWASP密钥管理](#142-owasp密钥管理)
  - [15. 完整实战案例](#15-完整实战案例)
    - [15.1 微服务密钥管理](#151-微服务密钥管理)
  - [16. 故障排查](#16-故障排查)
    - [16.1 常见问题](#161-常见问题)
    - [16.2 调试技巧](#162-调试技巧)
  - [17. 总结](#17-总结)
    - [核心特性](#核心特性)
    - [国际标准对齐](#国际标准对齐)
    - [技术栈](#技术栈)
    - [生产就绪](#生产就绪)

---

## 1. HashiCorp Vault核心概念

### 1.1 架构组件

```text
┌─────────────────────────────────────────────────┐
│              Client Applications                │
│   ┌────────┐  ┌────────┐  ┌────────────────┐    │
│   │  CLI   │  │  UI    │  │  HTTP API      │    │
│   └────────┘  └────────┘  └────────────────┘    │
└──────────────────────┬──────────────────────────┘
                       │
┌──────────────────────▼──────────────────────────┐
│                 Vault Server                    │
│  ┌──────────────────────────────────────────┐  │
│  │         Authentication Backend           │  │
│  │  Token │ AppRole │ K8s │ LDAP │ AWS │...│  │
│  └──────────────────────────────────────────┘  │
│  ┌──────────────────────────────────────────┐  │
│  │            Secrets Engines               │  │
│  │   KV │ Database │ PKI │ Transit │ SSH │  │  │
│  └──────────────────────────────────────────┘  │
│  ┌──────────────────────────────────────────┐  │
│  │              Storage Backend             │  │
│  │      Consul │ Raft │ Etcd │ File │...   │  │
│  └──────────────────────────────────────────┘  │
└─────────────────────────────────────────────────┘
```

### 1.2 核心功能

| 功能 | 说明 |
|------|------|
| **秘密存储** | 加密存储API密钥、密码、证书 |
| **动态秘密** | 按需生成短期凭证 |
| **数据加密** | 提供加密即服务（Transit） |
| **身份认证** | 多种认证方法集成 |
| **密钥轮换** | 自动密钥轮换和更新 |
| **审计日志** | 详细的访问审计 |

### 1.3 应用场景

- **数据库凭证管理**：动态生成PostgreSQL、MySQL凭证
- **API密钥保护**：安全存储第三方服务API密钥
- **证书管理**：自动签发和更新TLS证书
- **敏感数据加密**：PII数据加密存储
- **云平台凭证**：AWS/Azure临时访问密钥

---

## 2. Vault Rust客户端集成

### 2.1 依赖配置

```toml
[dependencies]
# Vault客户端
vaultrs = "0.7"
vaultrs-login = "0.2"

# 异步运行时
tokio = { version = "1.40", features = ["full"] }

# HTTP客户端
reqwest = { version = "0.12", features = ["json", "rustls-tls"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# OpenTelemetry
opentelemetry = "0.31"
opentelemetry-otlp = "0.31"
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
tracing-opentelemetry = "0.31"

# 错误处理
thiserror = "2.0"
anyhow = "1.0"

# 时间处理
chrono = "0.4"

# 缓存
moka = { version = "0.12", features = ["future"] }
```

### 2.2 客户端初始化

```rust
use vaultrs::client::{VaultClient, VaultClientSettingsBuilder};
use vaultrs::error::ClientError;
use std::time::Duration;
use tracing::{info, instrument};

/// Vault客户端配置
#[derive(Debug, Clone)]
pub struct VaultConfig {
    /// Vault地址
    pub address: String,
    
    /// 认证Token（可选）
    pub token: Option<String>,
    
    /// Namespace（Vault Enterprise）
    pub namespace: Option<String>,
    
    /// 超时时间
    pub timeout: Duration,
    
    /// 是否跳过TLS验证（仅开发环境）
    pub skip_tls_verify: bool,
}

impl Default for VaultConfig {
    fn default() -> Self {
        Self {
            address: std::env::var("VAULT_ADDR")
                .unwrap_or_else(|_| "http://127.0.0.1:8200".to_string()),
            token: std::env::var("VAULT_TOKEN").ok(),
            namespace: std::env::var("VAULT_NAMESPACE").ok(),
            timeout: Duration::from_secs(30),
            skip_tls_verify: false,
        }
    }
}

/// 创建Vault客户端
#[instrument]
pub async fn create_vault_client(config: &VaultConfig) -> Result<VaultClient, ClientError> {
    info!("初始化Vault客户端: {}", config.address);
    
    let mut settings_builder = VaultClientSettingsBuilder::default()
        .address(&config.address)
        .timeout(Some(config.timeout));
    
    if let Some(ref namespace) = config.namespace {
        settings_builder = settings_builder.namespace(namespace);
    }
    
    if config.skip_tls_verify {
        settings_builder = settings_builder.verify(false);
    }
    
    if let Some(ref token) = config.token {
        settings_builder = settings_builder.token(token);
    }
    
    let client = VaultClient::new(settings_builder.build()?)?;
    
    info!("Vault客户端初始化成功");
    Ok(client)
}
```

---

## 3. 认证方法实现

### 3.1 Token认证

```rust
use vaultrs::auth::token;

/// Token认证
#[instrument(skip(client))]
pub async fn authenticate_with_token(
    client: &VaultClient,
    token: &str,
) -> Result<(), ClientError> {
    info!("使用Token认证");
    
    // 验证Token有效性
    let token_info = token::lookup(client, token).await?;
    
    info!(
        "Token认证成功, policies={:?}, renewable={}",
        token_info.policies,
        token_info.renewable
    );
    
    Ok(())
}

/// 创建Token
#[instrument(skip(client))]
pub async fn create_token(
    client: &VaultClient,
    policies: Vec<String>,
    ttl: Duration,
) -> Result<String, ClientError> {
    let request = token::requests::CreateTokenRequest::builder()
        .policies(policies.clone())
        .ttl(ttl.as_secs() as u64)
        .renewable(true)
        .build()?;
    
    let response = token::create(client, None, Some(&request)).await?;
    
    info!("创建Token成功, policies={:?}", policies);
    
    Ok(response.client_token)
}
```

### 3.2 AppRole认证

```rust
use vaultrs::auth::approle;

/// AppRole认证
#[instrument(skip(client))]
pub async fn authenticate_with_approle(
    client: &VaultClient,
    role_id: &str,
    secret_id: &str,
) -> Result<String, ClientError> {
    info!("使用AppRole认证");
    
    let response = approle::login(client, "approle", role_id, secret_id).await?;
    
    info!(
        "AppRole认证成功, lease_duration={}s",
        response.lease_duration
    );
    
    Ok(response.client_token)
}

/// 创建AppRole
#[instrument(skip(client))]
pub async fn create_approle(
    client: &VaultClient,
    role_name: &str,
    policies: Vec<String>,
) -> Result<(String, String), ClientError> {
    use vaultrs::auth::approle::requests::SetAppRoleRequest;
    
    // 创建角色
    let request = SetAppRoleRequest::builder()
        .token_policies(policies.clone())
        .token_ttl("1h")
        .token_max_ttl("24h")
        .build()?;
    
    approle::role::set(client, "approle", role_name, Some(&request)).await?;
    
    // 获取RoleID
    let role_id_resp = approle::role::read_id(client, "approle", role_name).await?;
    let role_id = role_id_resp.role_id;
    
    // 生成SecretID
    let secret_id_resp = approle::role::secret::generate(
        client,
        "approle",
        role_name,
        None,
    )
    .await?;
    let secret_id = secret_id_resp.secret_id;
    
    info!("创建AppRole成功: {}", role_name);
    
    Ok((role_id, secret_id))
}
```

### 3.3 Kubernetes认证

```rust
use vaultrs::auth::kubernetes;

/// Kubernetes认证
#[instrument(skip(client))]
pub async fn authenticate_with_kubernetes(
    client: &VaultClient,
    role: &str,
    jwt: &str,
) -> Result<String, ClientError> {
    info!("使用Kubernetes认证, role={}", role);
    
    let response = kubernetes::login(client, "kubernetes", role, jwt).await?;
    
    info!(
        "Kubernetes认证成功, lease_duration={}s",
        response.lease_duration
    );
    
    Ok(response.client_token)
}

/// 从ServiceAccount读取JWT
pub fn read_kubernetes_jwt() -> Result<String, std::io::Error> {
    use std::fs;
    
    let jwt_path = "/var/run/secrets/kubernetes.io/serviceaccount/token";
    fs::read_to_string(jwt_path)
}

/// 配置Kubernetes认证
#[instrument(skip(client))]
pub async fn configure_kubernetes_auth(
    client: &VaultClient,
    kubernetes_host: &str,
    kubernetes_ca_cert: &str,
) -> Result<(), ClientError> {
    use vaultrs::auth::kubernetes::requests::SetConfigurationRequest;
    
    let request = SetConfigurationRequest::builder()
        .kubernetes_host(kubernetes_host)
        .kubernetes_ca_cert(kubernetes_ca_cert)
        .build()?;
    
    kubernetes::config::set(client, "kubernetes", Some(&request)).await?;
    
    info!("Kubernetes认证配置成功");
    Ok(())
}
```

---

## 4. KV Secrets Engine操作

### 4.1 读写秘密

```rust
use vaultrs::kv2;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// 秘密数据结构
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DatabaseCredentials {
    pub username: String,
    pub password: String,
    pub host: String,
    pub port: u16,
    pub database: String,
}

impl DatabaseCredentials {
    pub fn connection_string(&self) -> String {
        format!(
            "postgresql://{}:{}@{}:{}/{}",
            self.username, self.password, self.host, self.port, self.database
        )
    }
}

/// 写入秘密
#[instrument(skip(client, data))]
pub async fn write_secret<T: Serialize>(
    client: &VaultClient,
    mount: &str,
    path: &str,
    data: &T,
) -> Result<(), ClientError> {
    info!("写入秘密: {}/{}", mount, path);
    
    kv2::set(client, mount, path, data).await?;
    
    info!("秘密写入成功");
    Ok(())
}

/// 读取秘密
#[instrument(skip(client))]
pub async fn read_secret<T: for<'de> Deserialize<'de>>(
    client: &VaultClient,
    mount: &str,
    path: &str,
) -> Result<T, ClientError> {
    info!("读取秘密: {}/{}", mount, path);
    
    let secret = kv2::read::<T>(client, mount, path).await?;
    
    info!("秘密读取成功");
    Ok(secret)
}

/// 删除秘密
#[instrument(skip(client))]
pub async fn delete_secret(
    client: &VaultClient,
    mount: &str,
    path: &str,
) -> Result<(), ClientError> {
    info!("删除秘密: {}/{}", mount, path);
    
    kv2::delete_latest(client, mount, path).await?;
    
    info!("秘密删除成功");
    Ok(())
}
```

### 4.2 版本控制

```rust
/// 读取特定版本
#[instrument(skip(client))]
pub async fn read_secret_version<T: for<'de> Deserialize<'de>>(
    client: &VaultClient,
    mount: &str,
    path: &str,
    version: u64,
) -> Result<T, ClientError> {
    info!("读取秘密版本: {}/{} (v{})", mount, path, version);
    
    let secret = kv2::read_version::<T>(client, mount, path, version).await?;
    
    Ok(secret)
}

/// 列出所有版本
#[instrument(skip(client))]
pub async fn list_secret_versions(
    client: &VaultClient,
    mount: &str,
    path: &str,
) -> Result<HashMap<String, serde_json::Value>, ClientError> {
    info!("列出秘密版本: {}/{}", mount, path);
    
    let metadata = kv2::read_metadata(client, mount, path).await?;
    
    Ok(metadata.versions)
}

/// 恢复已删除版本
#[instrument(skip(client))]
pub async fn undelete_secret_version(
    client: &VaultClient,
    mount: &str,
    path: &str,
    versions: Vec<u64>,
) -> Result<(), ClientError> {
    info!("恢复秘密版本: {}/{}, versions={:?}", mount, path, versions);
    
    kv2::undelete(client, mount, path, versions).await?;
    
    Ok(())
}
```

---

## 5. 动态秘密生成

### 5.1 数据库动态凭证

```rust
use vaultrs::database;
use vaultrs::database::requests::GenerateCredentialsRequest;

/// 生成数据库凭证
#[instrument(skip(client))]
pub async fn generate_database_credentials(
    client: &VaultClient,
    role_name: &str,
) -> Result<DatabaseCredentials, ClientError> {
    info!("生成数据库动态凭证, role={}", role_name);
    
    let response = database::roles::generate_credentials(
        client,
        "database",
        role_name,
    )
    .await?;
    
    let creds = DatabaseCredentials {
        username: response.username,
        password: response.password,
        host: "postgres.default.svc.cluster.local".to_string(),
        port: 5432,
        database: "appdb".to_string(),
    };
    
    info!(
        "数据库凭证生成成功, username={}, lease_duration={}s",
        creds.username, response.lease_duration
    );
    
    Ok(creds)
}

/// 配置数据库连接
#[instrument(skip(client))]
pub async fn configure_database_connection(
    client: &VaultClient,
    connection_url: &str,
) -> Result<(), ClientError> {
    use vaultrs::database::requests::SetConnectionRequest;
    
    info!("配置数据库连接");
    
    let mut plugin_config = HashMap::new();
    plugin_config.insert("connection_url".to_string(), connection_url.to_string());
    plugin_config.insert("max_open_connections".to_string(), "10".to_string());
    
    let request = SetConnectionRequest::builder()
        .plugin_name("postgresql-database-plugin")
        .connection_url(connection_url)
        .allowed_roles(vec!["readonly".to_string(), "readwrite".to_string()])
        .build()?;
    
    database::config::set(client, "database", "postgresql", &request).await?;
    
    info!("数据库连接配置成功");
    Ok(())
}

/// 创建数据库角色
#[instrument(skip(client))]
pub async fn create_database_role(
    client: &VaultClient,
    role_name: &str,
    creation_statements: Vec<String>,
    default_ttl: Duration,
    max_ttl: Duration,
) -> Result<(), ClientError> {
    use vaultrs::database::requests::SetRoleRequest;
    
    info!("创建数据库角色: {}", role_name);
    
    let request = SetRoleRequest::builder()
        .db_name("postgresql")
        .creation_statements(creation_statements)
        .default_ttl(default_ttl.as_secs())
        .max_ttl(max_ttl.as_secs())
        .build()?;
    
    database::roles::set(client, "database", role_name, &request).await?;
    
    info!("数据库角色创建成功");
    Ok(())
}
```

### 5.2 自动续租

```rust
use vaultrs::sys;
use tokio::time::{sleep, interval};

/// 租约管理器
pub struct LeaseManager {
    client: VaultClient,
    lease_id: String,
    ttl: Duration,
}

impl LeaseManager {
    pub fn new(client: VaultClient, lease_id: String, ttl: Duration) -> Self {
        Self {
            client,
            lease_id,
            ttl,
        }
    }
    
    /// 启动自动续租
    #[instrument(skip(self))]
    pub async fn start_auto_renew(&self) -> Result<(), ClientError> {
        info!("启动自动续租, lease_id={}", self.lease_id);
        
        // 在TTL的一半时续租
        let renew_interval = self.ttl / 2;
        let mut interval = interval(renew_interval);
        
        loop {
            interval.tick().await;
            
            match self.renew_lease().await {
                Ok(new_ttl) => {
                    info!("租约续租成功, new_ttl={}s", new_ttl);
                }
                Err(e) => {
                    tracing::error!("租约续租失败: {:?}", e);
                    break;
                }
            }
        }
        
        Ok(())
    }
    
    /// 续租
    async fn renew_lease(&self) -> Result<u64, ClientError> {
        use vaultrs::sys::requests::RenewLeaseRequest;
        
        let request = RenewLeaseRequest::builder()
            .lease_id(&self.lease_id)
            .increment(self.ttl.as_secs())
            .build()?;
        
        let response = sys::renew_lease(&self.client, &request).await?;
        
        Ok(response.lease_duration)
    }
    
    /// 撤销租约
    #[instrument(skip(self))]
    pub async fn revoke(&self) -> Result<(), ClientError> {
        info!("撤销租约, lease_id={}", self.lease_id);
        
        sys::revoke_lease(&self.client, &self.lease_id).await?;
        
        info!("租约撤销成功");
        Ok(())
    }
}
```

---

## 6. 加密即服务(Transit)

### 6.1 数据加密解密

```rust
use vaultrs::transit;
use base64::{Engine as _, engine::general_purpose};

/// 加密数据
#[instrument(skip(client, plaintext))]
pub async fn encrypt_data(
    client: &VaultClient,
    key_name: &str,
    plaintext: &str,
) -> Result<String, ClientError> {
    info!("加密数据, key={}", key_name);
    
    let encoded = general_purpose::STANDARD.encode(plaintext);
    
    let response = transit::data::encrypt(
        client,
        "transit",
        key_name,
        &encoded,
        None,
    )
    .await?;
    
    info!("数据加密成功");
    Ok(response.ciphertext)
}

/// 解密数据
#[instrument(skip(client, ciphertext))]
pub async fn decrypt_data(
    client: &VaultClient,
    key_name: &str,
    ciphertext: &str,
) -> Result<String, ClientError> {
    info!("解密数据, key={}", key_name);
    
    let response = transit::data::decrypt(
        client,
        "transit",
        key_name,
        ciphertext,
        None,
    )
    .await?;
    
    let decoded = general_purpose::STANDARD
        .decode(&response.plaintext)
        .map_err(|e| ClientError::APIError {
            code: 500,
            errors: vec![e.to_string()],
        })?;
    
    let plaintext = String::from_utf8(decoded).map_err(|e| ClientError::APIError {
        code: 500,
        errors: vec![e.to_string()],
    })?;
    
    info!("数据解密成功");
    Ok(plaintext)
}

/// 批量加密
#[instrument(skip(client, plaintexts))]
pub async fn encrypt_batch(
    client: &VaultClient,
    key_name: &str,
    plaintexts: Vec<String>,
) -> Result<Vec<String>, ClientError> {
    use vaultrs::transit::requests::EncryptDataBatchRequest;
    
    info!("批量加密数据, key={}, count={}", key_name, plaintexts.len());
    
    let batch_items: Vec<_> = plaintexts
        .iter()
        .map(|p| {
            let encoded = general_purpose::STANDARD.encode(p);
            EncryptDataBatchRequest {
                plaintext: encoded,
                ..Default::default()
            }
        })
        .collect();
    
    let response = transit::data::encrypt_batch(
        client,
        "transit",
        key_name,
        &batch_items,
    )
    .await?;
    
    let ciphertexts: Vec<String> = response
        .batch_results
        .into_iter()
        .map(|r| r.ciphertext)
        .collect();
    
    info!("批量加密成功");
    Ok(ciphertexts)
}
```

### 6.2 密钥轮换

```rust
/// 创建加密密钥
#[instrument(skip(client))]
pub async fn create_encryption_key(
    client: &VaultClient,
    key_name: &str,
) -> Result<(), ClientError> {
    use vaultrs::transit::requests::CreateKeyRequest;
    
    info!("创建加密密钥: {}", key_name);
    
    let request = CreateKeyRequest::builder()
        .convergent_encryption(false)
        .derived(false)
        .exportable(false)
        .allow_plaintext_backup(false)
        .key_type("aes256-gcm96")
        .build()?;
    
    transit::key::create(client, "transit", key_name, Some(&request)).await?;
    
    info!("加密密钥创建成功");
    Ok(())
}

/// 轮换密钥
#[instrument(skip(client))]
pub async fn rotate_key(
    client: &VaultClient,
    key_name: &str,
) -> Result<(), ClientError> {
    info!("轮换加密密钥: {}", key_name);
    
    transit::key::rotate(client, "transit", key_name).await?;
    
    info!("密钥轮换成功");
    Ok(())
}

/// 重新加密数据（使用最新密钥版本）
#[instrument(skip(client, ciphertext))]
pub async fn rewrap_data(
    client: &VaultClient,
    key_name: &str,
    ciphertext: &str,
) -> Result<String, ClientError> {
    info!("重新加密数据, key={}", key_name);
    
    let response = transit::data::rewrap(
        client,
        "transit",
        key_name,
        ciphertext,
        None,
    )
    .await?;
    
    info!("数据重新加密成功");
    Ok(response.ciphertext)
}
```

---

## 7. PKI证书管理

### 7.1 证书签发

```rust
use vaultrs::pki;

/// 生成证书
#[instrument(skip(client))]
pub async fn generate_certificate(
    client: &VaultClient,
    role_name: &str,
    common_name: &str,
    alt_names: Vec<String>,
    ttl: Duration,
) -> Result<(String, String, String), ClientError> {
    use vaultrs::pki::requests::GenerateCertificateRequest;
    
    info!("生成证书, cn={}, ttl={}s", common_name, ttl.as_secs());
    
    let request = GenerateCertificateRequest::builder()
        .common_name(common_name)
        .alt_names(alt_names)
        .ttl(format!("{}s", ttl.as_secs()))
        .build()?;
    
    let response = pki::roles::generate_certificate(
        client,
        "pki",
        role_name,
        &request,
    )
    .await?;
    
    info!("证书生成成功, serial_number={}", response.serial_number);
    
    Ok((
        response.certificate,
        response.private_key,
        response.ca_chain.join("\n"),
    ))
}

/// 配置PKI根证书
#[instrument(skip(client))]
pub async fn configure_pki_root(
    client: &VaultClient,
    common_name: &str,
    ttl: Duration,
) -> Result<String, ClientError> {
    use vaultrs::pki::requests::GenerateRootRequest;
    
    info!("配置PKI根证书, cn={}", common_name);
    
    let request = GenerateRootRequest::builder()
        .common_name(common_name)
        .ttl(format!("{}h", ttl.as_secs() / 3600))
        .build()?;
    
    let response = pki::ca::generate_root(
        client,
        "pki",
        "internal",
        &request,
    )
    .await?;
    
    info!("PKI根证书配置成功");
    Ok(response.certificate)
}

/// 创建PKI角色
#[instrument(skip(client))]
pub async fn create_pki_role(
    client: &VaultClient,
    role_name: &str,
    allowed_domains: Vec<String>,
    max_ttl: Duration,
) -> Result<(), ClientError> {
    use vaultrs::pki::requests::SetRoleRequest;
    
    info!("创建PKI角色: {}", role_name);
    
    let request = SetRoleRequest::builder()
        .allowed_domains(allowed_domains)
        .allow_subdomains(true)
        .max_ttl(format!("{}h", max_ttl.as_secs() / 3600))
        .build()?;
    
    pki::roles::set(client, "pki", role_name, &request).await?;
    
    info!("PKI角色创建成功");
    Ok(())
}
```

### 7.2 自动更新

```rust
use tokio::fs;

/// 证书管理器
pub struct CertificateManager {
    client: VaultClient,
    role_name: String,
    common_name: String,
    alt_names: Vec<String>,
    cert_path: String,
    key_path: String,
    ttl: Duration,
}

impl CertificateManager {
    pub fn new(
        client: VaultClient,
        role_name: String,
        common_name: String,
        alt_names: Vec<String>,
        cert_path: String,
        key_path: String,
        ttl: Duration,
    ) -> Self {
        Self {
            client,
            role_name,
            common_name,
            alt_names,
            cert_path,
            key_path,
            ttl,
        }
    }
    
    /// 启动自动更新
    #[instrument(skip(self))]
    pub async fn start_auto_renewal(&self) -> Result<(), Box<dyn std::error::Error>> {
        info!("启动证书自动更新");
        
        // 立即生成初始证书
        self.renew_certificate().await?;
        
        // 在TTL的80%时更新
        let renew_interval = self.ttl * 80 / 100;
        let mut interval = interval(renew_interval);
        
        loop {
            interval.tick().await;
            
            match self.renew_certificate().await {
                Ok(_) => {
                    info!("证书自动更新成功");
                }
                Err(e) => {
                    tracing::error!("证书自动更新失败: {:?}", e);
                }
            }
        }
    }
    
    /// 更新证书
    async fn renew_certificate(&self) -> Result<(), Box<dyn std::error::Error>> {
        let (cert, key, _ca_chain) = generate_certificate(
            &self.client,
            &self.role_name,
            &self.common_name,
            self.alt_names.clone(),
            self.ttl,
        )
        .await?;
        
        // 写入文件
        fs::write(&self.cert_path, cert).await?;
        fs::write(&self.key_path, key).await?;
        
        info!("证书已更新到磁盘");
        Ok(())
    }
}
```

---

## 8. 策略与权限控制

### 8.1 策略定义

```hcl
# policies/readonly-policy.hcl
# KV只读权限
path "secret/data/app/*" {
  capabilities = ["read", "list"]
}

# 数据库动态凭证读取
path "database/creds/readonly" {
  capabilities = ["read"]
}

# Transit加密权限
path "transit/encrypt/app-key" {
  capabilities = ["update"]
}

path "transit/decrypt/app-key" {
  capabilities = ["update"]
}

# Token自查权限
path "auth/token/lookup-self" {
  capabilities = ["read"]
}
```

```hcl
# policies/readwrite-policy.hcl
path "secret/data/app/*" {
  capabilities = ["create", "read", "update", "delete", "list"]
}

path "database/creds/readwrite" {
  capabilities = ["read"]
}

path "pki/issue/server" {
  capabilities = ["create", "update"]
}
```

### 8.2 策略绑定

```rust
use vaultrs::sys::policy;

/// 创建策略
#[instrument(skip(client, policy_content))]
pub async fn create_policy(
    client: &VaultClient,
    policy_name: &str,
    policy_content: &str,
) -> Result<(), ClientError> {
    info!("创建策略: {}", policy_name);
    
    policy::set(client, policy_name, policy_content).await?;
    
    info!("策略创建成功");
    Ok(())
}

/// 读取策略
#[instrument(skip(client))]
pub async fn read_policy(
    client: &VaultClient,
    policy_name: &str,
) -> Result<String, ClientError> {
    info!("读取策略: {}", policy_name);
    
    let policy = policy::read(client, policy_name).await?;
    
    Ok(policy.rules)
}

/// 列出所有策略
#[instrument(skip(client))]
pub async fn list_policies(client: &VaultClient) -> Result<Vec<String>, ClientError> {
    info!("列出所有策略");
    
    let policies = policy::list(client).await?;
    
    Ok(policies)
}

/// 删除策略
#[instrument(skip(client))]
pub async fn delete_policy(
    client: &VaultClient,
    policy_name: &str,
) -> Result<(), ClientError> {
    info!("删除策略: {}", policy_name);
    
    policy::delete(client, policy_name).await?;
    
    info!("策略删除成功");
    Ok(())
}
```

---

## 9. OTLP分布式追踪集成

### 9.1 追踪配置

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{runtime, trace as sdktrace, Resource};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

/// 初始化OpenTelemetry追踪
pub fn init_tracing() -> Result<(), Box<dyn std::error::Error>> {
    let otlp_endpoint = std::env::var("OTEL_EXPORTER_OTLP_ENDPOINT")
        .unwrap_or_else(|_| "http://localhost:4317".to_string());
    
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint(&otlp_endpoint),
        )
        .with_trace_config(
            sdktrace::config()
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", "vault-client"),
                    KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
                ]))
        )
        .install_batch(runtime::Tokio)?;
    
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new(
            std::env::var("RUST_LOG").unwrap_or_else(|_| "info".into()),
        ))
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();
    
    Ok(())
}
```

### 9.2 操作追踪

```rust
/// 带追踪的秘密读取
#[instrument(
    name = "vault.read_secret",
    skip(client),
    fields(
        vault.mount = %mount,
        vault.path = %path,
        vault.operation = "read"
    )
)]
pub async fn read_secret_traced<T: for<'de> Deserialize<'de>>(
    client: &VaultClient,
    mount: &str,
    path: &str,
) -> Result<T, ClientError> {
    let span = tracing::Span::current();
    
    match read_secret(client, mount, path).await {
        Ok(secret) => {
            span.record("vault.status", "success");
            Ok(secret)
        }
        Err(e) => {
            span.record("vault.status", "error");
            span.record("error.message", &e.to_string().as_str());
            Err(e)
        }
    }
}

/// 带追踪的数据加密
#[instrument(
    name = "vault.encrypt",
    skip(client, plaintext),
    fields(
        vault.key = %key_name,
        vault.operation = "encrypt",
        data.size = plaintext.len()
    )
)]
pub async fn encrypt_data_traced(
    client: &VaultClient,
    key_name: &str,
    plaintext: &str,
) -> Result<String, ClientError> {
    let span = tracing::Span::current();
    
    match encrypt_data(client, key_name, plaintext).await {
        Ok(ciphertext) => {
            span.record("vault.status", "success");
            span.record("cipher.size", ciphertext.len());
            Ok(ciphertext)
        }
        Err(e) => {
            span.record("vault.status", "error");
            span.record("error.message", &e.to_string().as_str());
            Err(e)
        }
    }
}
```

---

## 10. Kubernetes集成

### 10.1 Vault Agent Injector

```yaml
# deployment-with-vault-agent.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: myapp
spec:
  template:
    metadata:
      annotations:
        # 启用Vault Agent注入
        vault.hashicorp.com/agent-inject: "true"
        
        # 认证角色
        vault.hashicorp.com/role: "myapp"
        
        # 注入数据库凭证
        vault.hashicorp.com/agent-inject-secret-database: "database/creds/readwrite"
        vault.hashicorp.com/agent-inject-template-database: |
          {{- with secret "database/creds/readwrite" -}}
          export DATABASE_URL="postgresql://{{ .Data.username }}:{{ .Data.password }}@postgres:5432/appdb"
          {{- end }}
        
        # 注入API密钥
        vault.hashicorp.com/agent-inject-secret-apikey: "secret/data/app/config"
        vault.hashicorp.com/agent-inject-template-apikey: |
          {{- with secret "secret/data/app/config" -}}
          export API_KEY="{{ .Data.data.api_key }}"
          {{- end }}
    spec:
      serviceAccountName: myapp
      containers:
      - name: app
        image: myapp:latest
        command:
        - /bin/sh
        - -c
        - |
          source /vault/secrets/database
          source /vault/secrets/apikey
          exec /app/myapp
```

### 10.2 CSI Secret Store Driver

```yaml
# secretproviderclass.yaml
apiVersion: secrets-store.csi.x-k8s.io/v1
kind: SecretProviderClass
metadata:
  name: vault-database
spec:
  provider: vault
  parameters:
    vaultAddress: "http://vault.vault:8200"
    roleName: "myapp"
    objects: |
      - objectName: "database-creds"
        secretPath: "database/creds/readwrite"
        secretKey: "username"
      - objectName: "database-password"
        secretPath: "database/creds/readwrite"
        secretKey: "password"
  secretObjects:
  - secretName: database-secret
    type: Opaque
    data:
    - objectName: database-creds
      key: username
    - objectName: database-password
      key: password

---
apiVersion: apps/v1
kind: Deployment
metadata:
  name: myapp
spec:
  template:
    spec:
      serviceAccountName: myapp
      containers:
      - name: app
        image: myapp:latest
        env:
        - name: DATABASE_USERNAME
          valueFrom:
            secretKeyRef:
              name: database-secret
              key: username
        - name: DATABASE_PASSWORD
          valueFrom:
            secretKeyRef:
              name: database-secret
              key: password
        volumeMounts:
        - name: secrets-store
          mountPath: "/mnt/secrets-store"
          readOnly: true
      volumes:
      - name: secrets-store
        csi:
          driver: secrets-store.csi.k8s.io
          readOnly: true
          volumeAttributes:
            secretProviderClass: "vault-database"
```

---

## 11. 高可用与灾难恢复

### 11.1 HA架构

```yaml
# vault-ha-values.yaml (Helm Chart)
global:
  enabled: true
  tlsDisable: false

server:
  # 高可用模式
  ha:
    enabled: true
    replicas: 3
    
    # Raft存储后端
    raft:
      enabled: true
      setNodeId: true
      config: |
        ui = true
        
        listener "tcp" {
          tls_disable = 0
          address = "[::]:8200"
          cluster_address = "[::]:8201"
          tls_cert_file = "/vault/userconfig/vault-server-tls/tls.crt"
          tls_key_file  = "/vault/userconfig/vault-server-tls/tls.key"
        }
        
        storage "raft" {
          path = "/vault/data"
        }
        
        service_registration "kubernetes" {}
  
  # 资源配置
  resources:
    requests:
      memory: 256Mi
      cpu: 250m
    limits:
      memory: 1Gi
      cpu: 1000m
  
  # 数据持久化
  dataStorage:
    enabled: true
    size: 10Gi
    storageClass: "fast-ssd"

# UI访问
ui:
  enabled: true
  serviceType: "LoadBalancer"
```

### 11.2 自动Unseal

```yaml
# vault-config.hcl (AWS KMS Auto-Unseal)
seal "awskms" {
  region     = "us-west-2"
  kms_key_id = "arn:aws:kms:us-west-2:123456789012:key/12345678-1234-1234-1234-123456789012"
}

storage "raft" {
  path = "/vault/data"
}

listener "tcp" {
  address     = "0.0.0.0:8200"
  tls_disable = 0
}
```

```rust
/// 初始化Vault
#[instrument(skip(client))]
pub async fn initialize_vault(
    client: &VaultClient,
    secret_shares: u64,
    secret_threshold: u64,
) -> Result<(Vec<String>, String), ClientError> {
    use vaultrs::sys::requests::InitRequest;
    
    info!("初始化Vault, shares={}, threshold={}", secret_shares, secret_threshold);
    
    let request = InitRequest::builder()
        .secret_shares(secret_shares)
        .secret_threshold(secret_threshold)
        .build()?;
    
    let response = vaultrs::sys::init(client, &request).await?;
    
    info!("Vault初始化成功");
    
    Ok((response.keys, response.root_token))
}
```

---

## 12. 监控与审计

### 12.1 Prometheus指标

```yaml
# servicemonitor.yaml
apiVersion: monitoring.coreos.com/v1
kind: ServiceMonitor
metadata:
  name: vault
  labels:
    app: vault
spec:
  selector:
    matchLabels:
      app: vault
  endpoints:
  - port: http
    path: /v1/sys/metrics
    params:
      format: ['prometheus']
    interval: 30s
    bearerTokenSecret:
      name: vault-metrics-token
      key: token
```

**关键指标**:

| 指标 | 说明 |
|------|------|
| `vault_core_unsealed` | Vault unseal状态 |
| `vault_core_active` | 是否为active节点 |
| `vault_runtime_alloc_bytes` | 内存分配 |
| `vault_token_count` | Token总数 |
| `vault_secret_kv_count` | KV秘密数量 |
| `vault_audit_log_request` | 审计日志请求数 |

### 12.2 审计日志

```rust
/// 配置审计日志
#[instrument(skip(client))]
pub async fn enable_audit_log(
    client: &VaultClient,
    path: String,
) -> Result<(), ClientError> {
    use vaultrs::sys::audit;
    use vaultrs::sys::requests::EnableAuditDeviceRequest;
    
    info!("启用审计日志, path={}", path);
    
    let mut options = HashMap::new();
    options.insert("file_path".to_string(), path);
    
    let request = EnableAuditDeviceRequest::builder()
        .type_("file")
        .options(options)
        .build()?;
    
    audit::enable(client, "file", &request).await?;
    
    info!("审计日志已启用");
    Ok(())
}
```

---

## 13. 生产环境最佳实践

### 13.1 安全加固

```hcl
# 1. TLS加密
listener "tcp" {
  address       = "0.0.0.0:8200"
  tls_cert_file = "/vault/tls/tls.crt"
  tls_key_file  = "/vault/tls/tls.key"
  tls_min_version = "tls12"
}

# 2. 限制API速率
api_rate_limit {
  rate_limit_exempt_paths = [
    "/v1/sys/health"
  ]
}

# 3. 启用审计
audit {
  enabled = true
}

# 4. UI禁用（生产环境）
ui = false
```

### 13.2 性能优化

```rust
use moka::future::Cache;

/// 秘密缓存层
pub struct CachedVaultClient {
    client: VaultClient,
    cache: Cache<String, serde_json::Value>,
}

impl CachedVaultClient {
    pub fn new(client: VaultClient, max_capacity: u64, ttl: Duration) -> Self {
        let cache = Cache::builder()
            .max_capacity(max_capacity)
            .time_to_live(ttl)
            .build();
        
        Self { client, cache }
    }
    
    #[instrument(skip(self))]
    pub async fn read_secret_cached(
        &self,
        mount: &str,
        path: &str,
    ) -> Result<serde_json::Value, ClientError> {
        let cache_key = format!("{}/{}", mount, path);
        
        // 尝试从缓存读取
        if let Some(cached) = self.cache.get(&cache_key).await {
            info!("缓存命中: {}", cache_key);
            return Ok(cached);
        }
        
        // 缓存未命中，从Vault读取
        info!("缓存未命中，从Vault读取: {}", cache_key);
        let secret: serde_json::Value = kv2::read(&self.client, mount, path).await?;
        
        // 存入缓存
        self.cache.insert(cache_key, secret.clone()).await;
        
        Ok(secret)
    }
}
```

---

## 14. 国际标准对齐

### 14.1 NIST密码学标准

| 标准 | Vault实现 |
|------|----------|
| **NIST SP 800-57** | ✅ 密钥生命周期管理 |
| **NIST SP 800-131A** | ✅ AES-256-GCM96加密 |
| **FIPS 140-2** | ✅ Enterprise版支持 |

### 14.2 OWASP密钥管理

- ✅ **密钥轮换**：Transit自动轮换
- ✅ **最小权限**：细粒度策略控制
- ✅ **审计日志**：所有操作可追溯
- ✅ **加密传输**：TLS 1.2+
- ✅ **动态秘密**：短期凭证降低风险

---

## 15. 完整实战案例

### 15.1 微服务密钥管理

```rust
// src/main.rs
use anyhow::Result;
use tracing::info;

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化追踪
    init_tracing()?;
    
    info!("启动应用，初始化Vault客户端");
    
    // 1. 创建Vault客户端
    let config = VaultConfig::default();
    let mut client = create_vault_client(&config).await?;
    
    // 2. Kubernetes认证
    let jwt = read_kubernetes_jwt()?;
    let token = authenticate_with_kubernetes(&client, "myapp", &jwt).await?;
    client = client.set_token(&token);
    
    // 3. 读取配置
    let api_config: HashMap<String, String> = read_secret(
        &client,
        "secret",
        "app/config",
    )
    .await?;
    
    info!("配置加载成功: {:?}", api_config.keys());
    
    // 4. 获取数据库凭证
    let db_creds = generate_database_credentials(&client, "readwrite").await?;
    
    info!("数据库凭证生成: {}", db_creds.username);
    
    // 5. 加密敏感数据
    let plaintext = "user@example.com";
    let ciphertext = encrypt_data(&client, "app-key", plaintext).await?;
    
    info!("数据加密成功: {}", &ciphertext[..20]);
    
    // 6. 生成TLS证书
    let (cert, key, _ca) = generate_certificate(
        &client,
        "server",
        "api.example.com",
        vec!["*.example.com".to_string()],
        Duration::from_secs(86400 * 30), // 30天
    )
    .await?;
    
    info!("TLS证书生成成功");
    
    // 7. 启动应用服务器
    start_server(db_creds, cert, key).await?;
    
    Ok(())
}

async fn start_server(
    db_creds: DatabaseCredentials,
    cert: String,
    key: String,
) -> Result<()> {
    // 应用服务器逻辑
    info!("应用服务器已启动");
    Ok(())
}
```

---

## 16. 故障排查

### 16.1 常见问题

| 问题 | 原因 | 解决方案 |
|------|------|----------|
| **Permission denied** | 策略权限不足 | 检查Token绑定的策略 |
| **Lease expired** | 租约过期未续租 | 实现自动续租逻辑 |
| **Connection refused** | Vault未启动/网络问题 | 检查Vault状态和网络 |
| **Sealed** | Vault已sealed | 执行unseal操作 |
| **Invalid token** | Token过期/撤销 | 重新认证获取新Token |

### 16.2 调试技巧

```bash
# 查看Vault状态
vault status

# 查看认证方法
vault auth list

# 查看Secrets Engines
vault secrets list

# 查看策略
vault policy list
vault policy read myapp-policy

# 查看Token信息
vault token lookup

# 查看审计日志
tail -f /var/log/vault/audit.log | jq

# 查看租约
vault list sys/leases/lookup/database/creds/readwrite
```

---

## 17. 总结

本文档提供了 **HashiCorp Vault** 在 Rust 1.90 中的生产级密钥管理完整实现，涵盖：

### 核心特性

| 特性 | 实现 |
|------|------|
| **多种认证方法** | ✅ Token、AppRole、Kubernetes |
| **KV Secrets** | ✅ 版本控制、批量操作 |
| **动态秘密** | ✅ 数据库凭证自动生成 |
| **加密即服务** | ✅ Transit加密/解密、密钥轮换 |
| **PKI证书** | ✅ 自动签发和更新 |
| **策略控制** | ✅ 细粒度权限管理 |
| **OTLP追踪** | ✅ 分布式追踪集成 |
| **Kubernetes集成** | ✅ Agent Injector、CSI Driver |
| **高可用** | ✅ Raft存储、Auto-Unseal |
| **监控审计** | ✅ Prometheus指标、审计日志 |

### 国际标准对齐

| 标准 | 对齐内容 |
|------|----------|
| **NIST SP 800-57** | 密钥生命周期管理 |
| **FIPS 140-2** | 密码学模块标准 |
| **OWASP** | 密钥管理最佳实践 |
| **OpenTelemetry** | OTLP分布式追踪 |

### 技术栈

- **HashiCorp Vault 1.15+**：密钥管理服务
- **vaultrs 0.7**：Rust客户端库
- **Rust 1.90**：类型安全、零成本抽象
- **Tokio 1.40**：异步运行时
- **OpenTelemetry 0.31**：分布式追踪

### 生产就绪

✅ TLS加密传输  
✅ 高可用Raft集群  
✅ 自动Unseal（AWS KMS）  
✅ 细粒度RBAC控制  
✅ 完整审计日志  
✅ Prometheus监控  
✅ Kubernetes原生集成  
✅ 自动密钥轮换  

---

**参考资源**:

- [HashiCorp Vault官方文档](https://www.vaultproject.io/docs)
- [vaultrs文档](https://docs.rs/vaultrs/)
- [Vault Best Practices](https://www.vaultproject.io/docs/internals/security)
- [NIST密码学标准](https://csrc.nist.gov/publications)
- [OWASP密钥管理备忘单](https://cheatsheetseries.owasp.org/cheatsheets/Key_Management_Cheat_Sheet.html)

---

*文档版本：v1.0*  
*最后更新：2025-10-11*  
*Vault版本：1.15+*  
*Rust版本：1.90+*  
*OpenTelemetry版本：0.31.0*
