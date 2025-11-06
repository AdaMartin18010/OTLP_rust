# 安全最佳实践完整指南

**Crate:** c11_libraries
**主题:** Security Best Practices
**Rust 版本:** 1.90.0
**最后更新:** 2025年10月28日

---

## 📋 目录

- [安全最佳实践完整指南](#安全最佳实践完整指南)
  - [📋 目录](#-目录)
  - [安全概述](#安全概述)
    - [OWASP Top 10 (2023)](#owasp-top-10-2023)
    - [纵深防御](#纵深防御)
  - [输入验证和清理](#输入验证和清理)
    - [1. 输入验证](#1-输入验证)
      - [白名单验证](#白名单验证)
      - [类型安全的验证](#类型安全的验证)
    - [2. 输入清理](#2-输入清理)
      - [HTML/XSS 防护](#htmlxss-防护)
      - [SQL 注入防护](#sql-注入防护)
  - [认证和授权](#认证和授权)
    - [1. 密码管理](#1-密码管理)
      - [密码哈希](#密码哈希)
    - [2. JWT 认证](#2-jwt-认证)
      - [JWT 实现](#jwt-实现)
    - [3. RBAC (基于角色的访问控制)](#3-rbac-基于角色的访问控制)
      - [实现](#实现)
  - [密码学实践](#密码学实践)
    - [1. 加密和解密](#1-加密和解密)
      - [AES-GCM 加密](#aes-gcm-加密)
    - [2. 数字签名](#2-数字签名)
      - [Ed25519 签名](#ed25519-签名)
    - [3. 密钥管理](#3-密钥管理)
      - [密钥派生](#密钥派生)
  - [安全通信](#安全通信)
    - [1. TLS/HTTPS](#1-tlshttps)
      - [Axum with TLS](#axum-with-tls)
    - [2. mTLS (双向 TLS)](#2-mtls-双向-tls)
      - [配置](#配置)
  - [注入攻击防护](#注入攻击防护)
    - [1. SQL 注入防护](#1-sql-注入防护)
    - [2. Command 注入防护](#2-command-注入防护)
    - [3. LDAP 注入防护](#3-ldap-注入防护)
  - [依赖安全](#依赖安全)
    - [1. 依赖审计](#1-依赖审计)
      - [cargo-audit](#cargo-audit)
      - [cargo-deny](#cargo-deny)
    - [2. 最小权限原则](#2-最小权限原则)
    - [3. 依赖版本锁定](#3-依赖版本锁定)
  - [安全审计](#安全审计)
    - [1. 安全日志](#1-安全日志)
      - [实现](#实现-1)
    - [2. 入侵检测](#2-入侵检测)
      - [暴力破解检测](#暴力破解检测)
    - [3. 安全扫描](#3-安全扫描)
      - [静态分析](#静态分析)
      - [模糊测试](#模糊测试)
  - [总结](#总结)
    - [安全清单](#安全清单)
    - [最佳实践](#最佳实践)

---

## 安全概述

### OWASP Top 10 (2023)

```text
1. Broken Access Control (访问控制失效)
2. Cryptographic Failures (加密失败)
3. Injection (注入)
4. Insecure Design (不安全的设计)
5. Security Misconfiguration (安全配置错误)
6. Vulnerable Components (易受攻击的组件)
7. Authentication Failures (认证失败)
8. Software and Data Integrity Failures (软件和数据完整性失败)
9. Security Logging and Monitoring Failures (日志和监控失败)
10. Server-Side Request Forgery (SSRF)
```

### 纵深防御

```text
┌────────────────────────────────────────┐
│         纵深防御层次                     │
├────────────────────────────────────────┤
│ 1. 物理安全 (Physical Security)         │
│ 2. 网络安全 (Network Security)          │
│ 3. 主机安全 (Host Security)             │
│ 4. 应用安全 (Application Security)      │
│ 5. 数据安全 (Data Security)             │
└────────────────────────────────────────┘
```

---

## 输入验证和清理

### 1. 输入验证

#### 白名单验证

```rust
use regex::Regex;
use validator::Validate;

#[derive(Debug, Validate)]
pub struct UserInput {
    #[validate(email)]
    pub email: String,

    #[validate(length(min = 8, max = 128))]
    pub password: String,

    #[validate(regex = "USERNAME_REGEX")]
    pub username: String,

    #[validate(range(min = 18, max = 120))]
    pub age: u8,
}

lazy_static! {
    static ref USERNAME_REGEX: Regex = Regex::new(r"^[a-zA-Z0-9_]{3,20}$").unwrap();
}

pub fn validate_user_input(input: &UserInput) -> Result<()> {
    input.validate()
        .map_err(|e| anyhow::anyhow!("Validation failed: {}", e))
}

// 使用示例
async fn register_handler(
    Json(input): Json<UserInput>,
) -> Result<Json<RegisterResponse>> {
    // 1. 验证输入
    validate_user_input(&input)?;

    // 2. 进一步业务逻辑
    let user = create_user(input).await?;

    Ok(Json(RegisterResponse { user }))
}
```

---

#### 类型安全的验证

```rust
use std::str::FromStr;

// ❌ 不好：使用字符串
fn bad_validate(email: String) -> Result<()> {
    if !email.contains('@') {
        return Err(anyhow::anyhow!("Invalid email"));
    }
    Ok(())
}

// ✅ 好：使用新类型模式
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Email(String);

impl FromStr for Email {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self> {
        // 使用专业的 email 验证库
        if validator::validate_email(s) {
            Ok(Email(s.to_string()))
        } else {
            Err(anyhow::anyhow!("Invalid email format"))
        }
    }
}

// 使用
fn process_email(email: Email) {
    // 类型系统保证 email 是有效的
}
```

---

### 2. 输入清理

#### HTML/XSS 防护

```rust
use ammonia::clean;

pub fn sanitize_html(input: &str) -> String {
    // 清理 HTML，防止 XSS
    clean(input)
}

pub fn sanitize_user_content(content: &str) -> String {
    ammonia::Builder::default()
        .tags(hashset!["p", "br", "strong", "em", "a"])
        .link_rel(Some("nofollow noopener"))
        .url_schemes(hashset!["http", "https", "mailto"])
        .clean(content)
        .to_string()
}

// 使用示例
async fn create_post_handler(
    Json(input): Json<CreatePostRequest>,
) -> Result<Json<Post>> {
    // 清理用户输入的 HTML
    let safe_content = sanitize_user_content(&input.content);

    let post = Post {
        title: input.title,
        content: safe_content,
        ..Default::default()
    };

    save_post(&post).await?;

    Ok(Json(post))
}
```

---

#### SQL 注入防护

```rust
use sqlx::{PgPool, query, query_as};

// ❌ 不好：字符串拼接（SQL 注入风险）
async fn bad_find_user(pool: &PgPool, username: &str) -> Result<User> {
    let sql = format!("SELECT * FROM users WHERE username = '{}'", username);
    // 如果 username = "admin' OR '1'='1"，会导致 SQL 注入
    query_as::<_, User>(&sql)
        .fetch_one(pool)
        .await
        .map_err(Into::into)
}

// ✅ 好：参数化查询
async fn good_find_user(pool: &PgPool, username: &str) -> Result<User> {
    query_as::<_, User>("SELECT * FROM users WHERE username = $1")
        .bind(username)  // 参数化，自动转义
        .fetch_one(pool)
        .await
        .map_err(Into::into)
}

// ✅ 更好：使用 sqlx 宏
async fn best_find_user(pool: &PgPool, username: &str) -> Result<User> {
    let user = sqlx::query_as!(
        User,
        "SELECT * FROM users WHERE username = $1",
        username
    )
    .fetch_one(pool)
    .await?;

    Ok(user)
}
```

---

## 认证和授权

### 1. 密码管理

#### 密码哈希

```rust
use argon2::{
    password_hash::{PasswordHash, PasswordHasher, PasswordVerifier, SaltString},
    Argon2,
};
use rand::rngs::OsRng;

pub struct PasswordHasher {
    argon2: Argon2<'static>,
}

impl PasswordHasher {
    pub fn new() -> Self {
        Self {
            argon2: Argon2::default(),
        }
    }

    /// 哈希密码
    pub fn hash_password(&self, password: &str) -> Result<String> {
        let salt = SaltString::generate(&mut OsRng);

        let password_hash = self.argon2
            .hash_password(password.as_bytes(), &salt)
            .map_err(|e| anyhow::anyhow!("Password hashing failed: {}", e))?
            .to_string();

        Ok(password_hash)
    }

    /// 验证密码
    pub fn verify_password(&self, password: &str, hash: &str) -> Result<bool> {
        let parsed_hash = PasswordHash::new(hash)
            .map_err(|e| anyhow::anyhow!("Invalid password hash: {}", e))?;

        Ok(self.argon2
            .verify_password(password.as_bytes(), &parsed_hash)
            .is_ok())
    }
}

// 使用示例
async fn register_user(
    pool: &PgPool,
    email: Email,
    password: String,
) -> Result<User> {
    // 1. 验证密码强度
    validate_password_strength(&password)?;

    // 2. 哈希密码
    let hasher = PasswordHasher::new();
    let password_hash = hasher.hash_password(&password)?;

    // 3. 存储
    let user = sqlx::query_as!(
        User,
        "INSERT INTO users (email, password_hash) VALUES ($1, $2) RETURNING *",
        email.as_str(),
        password_hash
    )
    .fetch_one(pool)
    .await?;

    Ok(user)
}

fn validate_password_strength(password: &str) -> Result<()> {
    if password.len() < 8 {
        return Err(anyhow::anyhow!("Password too short"));
    }

    if !password.chars().any(|c| c.is_uppercase()) {
        return Err(anyhow::anyhow!("Password must contain uppercase"));
    }

    if !password.chars().any(|c| c.is_lowercase()) {
        return Err(anyhow::anyhow!("Password must contain lowercase"));
    }

    if !password.chars().any(|c| c.is_numeric()) {
        return Err(anyhow::anyhow!("Password must contain number"));
    }

    Ok(())
}
```

---

### 2. JWT 认证

#### JWT 实现

```rust
use jsonwebtoken::{encode, decode, Header, Validation, EncodingKey, DecodingKey};
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct Claims {
    pub sub: String,  // 用户 ID
    pub exp: usize,   // 过期时间
    pub iat: usize,   // 签发时间
    pub roles: Vec<String>,
}

pub struct JwtManager {
    encoding_key: EncodingKey,
    decoding_key: DecodingKey,
}

impl JwtManager {
    pub fn new(secret: &str) -> Self {
        Self {
            encoding_key: EncodingKey::from_secret(secret.as_bytes()),
            decoding_key: DecodingKey::from_secret(secret.as_bytes()),
        }
    }

    /// 生成 JWT
    pub fn generate_token(&self, user_id: &str, roles: Vec<String>) -> Result<String> {
        let now = chrono::Utc::now();
        let exp = (now + chrono::Duration::hours(24)).timestamp() as usize;

        let claims = Claims {
            sub: user_id.to_string(),
            exp,
            iat: now.timestamp() as usize,
            roles,
        };

        encode(&Header::default(), &claims, &self.encoding_key)
            .map_err(|e| anyhow::anyhow!("Token generation failed: {}", e))
    }

    /// 验证 JWT
    pub fn verify_token(&self, token: &str) -> Result<Claims> {
        let token_data = decode::<Claims>(
            token,
            &self.decoding_key,
            &Validation::default(),
        )
        .map_err(|e| anyhow::anyhow!("Token verification failed: {}", e))?;

        Ok(token_data.claims)
    }
}

// 中间件
pub async fn auth_middleware(
    State(jwt_manager): State<Arc<JwtManager>>,
    mut request: Request,
    next: Next,
) -> Result<Response, StatusCode> {
    // 1. 提取 token
    let auth_header = request
        .headers()
        .get("Authorization")
        .and_then(|h| h.to_str().ok())
        .ok_or(StatusCode::UNAUTHORIZED)?;

    let token = auth_header
        .strip_prefix("Bearer ")
        .ok_or(StatusCode::UNAUTHORIZED)?;

    // 2. 验证 token
    let claims = jwt_manager
        .verify_token(token)
        .map_err(|_| StatusCode::UNAUTHORIZED)?;

    // 3. 将 claims 添加到请求扩展
    request.extensions_mut().insert(claims);

    Ok(next.run(request).await)
}
```

---

### 3. RBAC (基于角色的访问控制)

#### 实现

```rust
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Permission {
    ReadUsers,
    WriteUsers,
    DeleteUsers,
    ReadPosts,
    WritePosts,
    DeletePosts,
    Admin,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Role {
    Admin,
    Editor,
    User,
    Guest,
}

pub struct RbacManager {
    role_permissions: HashMap<Role, Vec<Permission>>,
}

impl RbacManager {
    pub fn new() -> Self {
        let mut role_permissions = HashMap::new();

        // Admin: 所有权限
        role_permissions.insert(Role::Admin, vec![
            Permission::Admin,
            Permission::ReadUsers,
            Permission::WriteUsers,
            Permission::DeleteUsers,
            Permission::ReadPosts,
            Permission::WritePosts,
            Permission::DeletePosts,
        ]);

        // Editor: 内容管理
        role_permissions.insert(Role::Editor, vec![
            Permission::ReadUsers,
            Permission::ReadPosts,
            Permission::WritePosts,
        ]);

        // User: 基本权限
        role_permissions.insert(Role::User, vec![
            Permission::ReadPosts,
            Permission::WritePosts,
        ]);

        // Guest: 只读
        role_permissions.insert(Role::Guest, vec![
            Permission::ReadPosts,
        ]);

        Self { role_permissions }
    }

    pub fn has_permission(&self, role: &Role, permission: &Permission) -> bool {
        self.role_permissions
            .get(role)
            .map(|perms| perms.contains(permission))
            .unwrap_or(false)
    }
}

// 权限检查中间件
pub async fn require_permission(
    State(rbac): State<Arc<RbacManager>>,
    Extension(claims): Extension<Claims>,
    permission: Permission,
    next: Next,
) -> Result<Response, StatusCode> {
    // 检查用户是否有权限
    let has_permission = claims.roles.iter().any(|role_str| {
        if let Ok(role) = role_str.parse::<Role>() {
            rbac.has_permission(&role, &permission)
        } else {
            false
        }
    });

    if !has_permission {
        return Err(StatusCode::FORBIDDEN);
    }

    Ok(next.run(request).await)
}

// 使用示例
async fn delete_user_handler(
    Extension(claims): Extension<Claims>,
    Path(user_id): Path<i64>,
) -> Result<StatusCode> {
    // 权限已在中间件中检查
    delete_user(user_id).await?;
    Ok(StatusCode::NO_CONTENT)
}
```

---

## 密码学实践

### 1. 加密和解密

#### AES-GCM 加密

```rust
use aes_gcm::{
    aead::{Aead, KeyInit, OsRng},
    Aes256Gcm, Nonce,
};

pub struct Encryptor {
    cipher: Aes256Gcm,
}

impl Encryptor {
    pub fn new(key: &[u8; 32]) -> Self {
        let cipher = Aes256Gcm::new(key.into());
        Self { cipher }
    }

    /// 加密数据
    pub fn encrypt(&self, plaintext: &[u8]) -> Result<Vec<u8>> {
        // 生成随机 nonce
        let nonce = Aes256Gcm::generate_nonce(&mut OsRng);

        // 加密
        let ciphertext = self.cipher
            .encrypt(&nonce, plaintext)
            .map_err(|e| anyhow::anyhow!("Encryption failed: {}", e))?;

        // 组合 nonce + ciphertext
        let mut result = nonce.to_vec();
        result.extend_from_slice(&ciphertext);

        Ok(result)
    }

    /// 解密数据
    pub fn decrypt(&self, encrypted: &[u8]) -> Result<Vec<u8>> {
        if encrypted.len() < 12 {
            return Err(anyhow::anyhow!("Invalid encrypted data"));
        }

        // 分离 nonce 和 ciphertext
        let (nonce_bytes, ciphertext) = encrypted.split_at(12);
        let nonce = Nonce::from_slice(nonce_bytes);

        // 解密
        self.cipher
            .decrypt(nonce, ciphertext)
            .map_err(|e| anyhow::anyhow!("Decryption failed: {}", e))
    }
}

// 使用示例：加密敏感数据
async fn store_sensitive_data(
    encryptor: &Encryptor,
    user_id: i64,
    ssn: &str,
) -> Result<()> {
    // 加密 SSN
    let encrypted_ssn = encryptor.encrypt(ssn.as_bytes())?;

    // 存储加密数据
    sqlx::query!(
        "INSERT INTO sensitive_data (user_id, encrypted_ssn) VALUES ($1, $2)",
        user_id,
        encrypted_ssn
    )
    .execute(pool)
    .await?;

    Ok(())
}
```

---

### 2. 数字签名

#### Ed25519 签名

```rust
use ed25519_dalek::{Keypair, PublicKey, Signature, Signer, Verifier};
use rand::rngs::OsRng;

pub struct SignatureManager {
    keypair: Keypair,
}

impl SignatureManager {
    pub fn new() -> Self {
        let mut csprng = OsRng;
        let keypair = Keypair::generate(&mut csprng);

        Self { keypair }
    }

    pub fn from_keypair(keypair: Keypair) -> Self {
        Self { keypair }
    }

    /// 签名数据
    pub fn sign(&self, data: &[u8]) -> Signature {
        self.keypair.sign(data)
    }

    /// 验证签名
    pub fn verify(&self, data: &[u8], signature: &Signature) -> bool {
        self.keypair.public.verify(data, signature).is_ok()
    }

    pub fn public_key(&self) -> &PublicKey {
        &self.keypair.public
    }
}

// 使用示例：API 请求签名
async fn sign_api_request(
    signer: &SignatureManager,
    request_body: &[u8],
) -> Result<SignedRequest> {
    let signature = signer.sign(request_body);

    Ok(SignedRequest {
        body: request_body.to_vec(),
        signature: signature.to_bytes().to_vec(),
        public_key: signer.public_key().to_bytes().to_vec(),
    })
}

async fn verify_api_request(request: &SignedRequest) -> Result<bool> {
    let public_key = PublicKey::from_bytes(&request.public_key)?;
    let signature = Signature::from_bytes(&request.signature)?;

    Ok(public_key.verify(&request.body, &signature).is_ok())
}
```

---

### 3. 密钥管理

#### 密钥派生

```rust
use argon2::Argon2;
use sha2::{Sha256, Digest};

pub struct KeyDerivation;

impl KeyDerivation {
    /// 从密码派生密钥
    pub fn derive_key_from_password(
        password: &str,
        salt: &[u8],
    ) -> Result<[u8; 32]> {
        let argon2 = Argon2::default();
        let mut output_key = [0u8; 32];

        argon2
            .hash_password_into(password.as_bytes(), salt, &mut output_key)
            .map_err(|e| anyhow::anyhow!("Key derivation failed: {}", e))?;

        Ok(output_key)
    }

    /// HKDF 密钥派生
    pub fn hkdf(
        master_key: &[u8],
        salt: &[u8],
        info: &[u8],
    ) -> [u8; 32] {
        use hkdf::Hkdf;

        let hk = Hkdf::<Sha256>::new(Some(salt), master_key);
        let mut okm = [0u8; 32];
        hk.expand(info, &mut okm).unwrap();

        okm
    }
}

// 使用示例
pub struct MasterKeyManager {
    master_key: [u8; 32],
}

impl MasterKeyManager {
    pub fn derive_encryption_key(&self, context: &str) -> [u8; 32] {
        KeyDerivation::hkdf(
            &self.master_key,
            b"encryption",
            context.as_bytes(),
        )
    }

    pub fn derive_signing_key(&self, context: &str) -> [u8; 32] {
        KeyDerivation::hkdf(
            &self.master_key,
            b"signing",
            context.as_bytes(),
        )
    }
}
```

---

## 安全通信

### 1. TLS/HTTPS

#### Axum with TLS

```rust
use axum::Router;
use axum_server::tls_rustls::RustlsConfig;

pub async fn run_https_server(app: Router) -> Result<()> {
    // 加载 TLS 证书
    let config = RustlsConfig::from_pem_file(
        "/path/to/cert.pem",
        "/path/to/key.pem",
    )
    .await?;

    let addr = SocketAddr::from(([0, 0, 0, 0], 443));

    println!("HTTPS server listening on {}", addr);

    axum_server::bind_rustls(addr, config)
        .serve(app.into_make_service())
        .await?;

    Ok(())
}

// TLS 配置最佳实践
pub fn create_secure_tls_config() -> Result<RustlsConfig> {
    let config = rustls::ServerConfig::builder()
        .with_safe_default_cipher_suites()
        .with_safe_default_kx_groups()
        .with_protocol_versions(&[&rustls::version::TLS13])?  // 只用 TLS 1.3
        .with_no_client_auth()
        .with_cert_resolver(Arc::new(cert_resolver));

    Ok(config)
}
```

---

### 2. mTLS (双向 TLS)

#### 配置

```rust
use rustls::{ServerConfig, ClientConfig};
use rustls_pemfile::{certs, pkcs8_private_keys};

pub fn create_mtls_server_config() -> Result<ServerConfig> {
    // 加载服务器证书
    let cert_file = &mut BufReader::new(File::open("server-cert.pem")?);
    let key_file = &mut BufReader::new(File::open("server-key.pem")?);
    let ca_file = &mut BufReader::new(File::open("ca-cert.pem")?);

    let cert_chain = certs(cert_file)?
        .into_iter()
        .map(Certificate)
        .collect();

    let mut keys = pkcs8_private_keys(key_file)?;
    let key = PrivateKey(keys.remove(0));

    // 加载 CA 证书（用于验证客户端）
    let ca_certs = certs(ca_file)?
        .into_iter()
        .map(Certificate)
        .collect::<Vec<_>>();

    let mut client_auth_roots = RootCertStore::empty();
    for cert in ca_certs {
        client_auth_roots.add(&cert)?;
    }

    let client_auth = AllowAnyAuthenticatedClient::new(client_auth_roots);

    let config = ServerConfig::builder()
        .with_safe_defaults()
        .with_client_cert_verifier(client_auth)
        .with_single_cert(cert_chain, key)?;

    Ok(config)
}
```

---

## 注入攻击防护

### 1. SQL 注入防护

已在前面的"输入验证和清理"部分介绍。

### 2. Command 注入防护

```rust
use std::process::Command;

// ❌ 不好：直接使用用户输入
fn bad_execute_command(filename: &str) -> Result<String> {
    let output = Command::new("sh")
        .arg("-c")
        .arg(format!("cat {}", filename))  // 注入风险
        .output()?;

    Ok(String::from_utf8(output.stdout)?)
}

// ✅ 好：验证输入
fn good_execute_command(filename: &str) -> Result<String> {
    // 1. 验证文件名
    if !filename.chars().all(|c| c.is_alphanumeric() || c == '.' || c == '_') {
        return Err(anyhow::anyhow!("Invalid filename"));
    }

    // 2. 使用白名单路径
    let safe_path = Path::new("/safe/directory").join(filename);

    if !safe_path.starts_with("/safe/directory") {
        return Err(anyhow::anyhow!("Path traversal detected"));
    }

    // 3. 直接使用文件系统 API，不用 shell
    let content = std::fs::read_to_string(safe_path)?;

    Ok(content)
}
```

---

### 3. LDAP 注入防护

```rust
pub fn sanitize_ldap_input(input: &str) -> String {
    // 转义 LDAP 特殊字符
    input
        .replace('\\', "\\5c")
        .replace('*', "\\2a")
        .replace('(', "\\28")
        .replace(')', "\\29")
        .replace('\0', "\\00")
}

pub fn search_user_safe(ldap: &mut LdapConn, username: &str) -> Result<Vec<SearchEntry>> {
    let safe_username = sanitize_ldap_input(username);
    let filter = format!("(uid={})", safe_username);

    let result = ldap.search(
        "ou=users,dc=example,dc=com",
        Scope::Subtree,
        &filter,
        vec!["cn", "mail"],
    )?;

    Ok(result.success()?.0)
}
```

---

## 依赖安全

### 1. 依赖审计

#### cargo-audit

```bash
# 安装 cargo-audit
cargo install cargo-audit

# 审计依赖
cargo audit

# 修复已知漏洞
cargo audit fix
```

#### cargo-deny

```toml
# deny.toml
[advisories]
db-path = "~/.cargo/advisory-db"
db-urls = ["https://github.com/rustsec/advisory-db"]
vulnerability = "deny"
unmaintained = "warn"
yanked = "warn"
notice = "warn"

[licenses]
unlicensed = "deny"
allow = [
    "MIT",
    "Apache-2.0",
    "BSD-3-Clause",
]
deny = [
    "GPL-3.0",
]

[bans]
multiple-versions = "warn"
wildcards = "deny"
```

```bash
# 安装
cargo install cargo-deny

# 检查
cargo deny check
```

---

### 2. 最小权限原则

```toml
# Cargo.toml - 只启用需要的 features
[dependencies]
tokio = { version = "1.35", features = ["rt-multi-thread", "net"] }
# 不要使用 features = ["full"]

sqlx = { version = "0.7", features = ["postgres", "runtime-tokio"] }
# 只启用需要的数据库驱动
```

---

### 3. 依赖版本锁定

```toml
# 使用精确版本
[dependencies]
critical-dep = "=1.2.3"  # 精确版本

# 或使用 Cargo.lock
# 确保 Cargo.lock 提交到版本控制
```

---

## 安全审计

### 1. 安全日志

#### 实现

```rust
use tracing::{info, warn, error};

pub struct SecurityLogger;

impl SecurityLogger {
    /// 记录登录尝试
    pub fn log_login_attempt(
        username: &str,
        ip: &str,
        success: bool,
    ) {
        if success {
            info!(
                event = "login_success",
                username = %username,
                ip = %ip,
                "User login successful"
            );
        } else {
            warn!(
                event = "login_failure",
                username = %username,
                ip = %ip,
                "User login failed"
            );
        }
    }

    /// 记录权限拒绝
    pub fn log_access_denied(
        user_id: i64,
        resource: &str,
        action: &str,
    ) {
        warn!(
            event = "access_denied",
            user_id = %user_id,
            resource = %resource,
            action = %action,
            "Access denied"
        );
    }

    /// 记录敏感操作
    pub fn log_sensitive_operation(
        user_id: i64,
        operation: &str,
        details: &str,
    ) {
        info!(
            event = "sensitive_operation",
            user_id = %user_id,
            operation = %operation,
            details = %details,
            "Sensitive operation performed"
        );
    }

    /// 记录异常活动
    pub fn log_suspicious_activity(
        description: &str,
        severity: &str,
    ) {
        error!(
            event = "suspicious_activity",
            description = %description,
            severity = %severity,
            "Suspicious activity detected"
        );
    }
}
```

---

### 2. 入侵检测

#### 暴力破解检测

```rust
use std::collections::HashMap;
use tokio::sync::RwLock;

pub struct BruteForceDetector {
    attempts: Arc<RwLock<HashMap<String, Vec<Instant>>>>,
    max_attempts: usize,
    window: Duration,
}

impl BruteForceDetector {
    pub fn new(max_attempts: usize, window: Duration) -> Self {
        Self {
            attempts: Arc::new(RwLock::new(HashMap::new())),
            max_attempts,
            window,
        }
    }

    /// 记录登录尝试
    pub async fn record_attempt(&self, identifier: &str) -> bool {
        let now = Instant::now();
        let mut attempts = self.attempts.write().await;

        let user_attempts = attempts.entry(identifier.to_string())
            .or_insert_with(Vec::new);

        // 清理过期的尝试
        user_attempts.retain(|&t| now.duration_since(t) < self.window);

        // 添加新尝试
        user_attempts.push(now);

        // 检查是否超过阈值
        if user_attempts.len() > self.max_attempts {
            SecurityLogger::log_suspicious_activity(
                &format!("Brute force detected for {}", identifier),
                "high",
            );
            return false;  // 阻止
        }

        true  // 允许
    }

    /// 清除尝试记录（登录成功后）
    pub async fn clear_attempts(&self, identifier: &str) {
        let mut attempts = self.attempts.write().await;
        attempts.remove(identifier);
    }
}

// 使用示例
async fn login_with_protection(
    detector: &BruteForceDetector,
    username: &str,
    password: &str,
) -> Result<String> {
    // 1. 检查暴力破解
    if !detector.record_attempt(username).await {
        return Err(anyhow::anyhow!("Too many login attempts"));
    }

    // 2. 验证密码
    let user = verify_credentials(username, password).await?;

    // 3. 清除尝试记录
    detector.clear_attempts(username).await;

    // 4. 生成 token
    let token = generate_token(&user)?;

    Ok(token)
}
```

---

### 3. 安全扫描

#### 静态分析

```bash
# Clippy 安全检查
cargo clippy -- -W clippy::all -W clippy::pedantic -W clippy::security

# Miri (检测 unsafe 代码)
cargo +nightly miri test
```

#### 模糊测试

```rust
#[cfg(test)]
mod fuzz_tests {
    use super::*;

    #[test]
    fn fuzz_input_validation() {
        use quickcheck::{quickcheck, TestResult};

        fn prop(input: String) -> TestResult {
            match validate_input(&input) {
                Ok(_) => TestResult::passed(),
                Err(_) => TestResult::passed(),  // 错误处理正确
            }
        }

        quickcheck(prop as fn(String) -> TestResult);
    }
}
```

---

## 总结

### 安全清单

- ✅ **输入验证**: 白名单验证、类型安全
- ✅ **认证授权**: JWT、RBAC、密码哈希
- ✅ **密码学**: AES-GCM、Ed25519、密钥管理
- ✅ **安全通信**: TLS 1.3、mTLS
- ✅ **注入防护**: SQL、XSS、命令注入
- ✅ **依赖安全**: cargo-audit、cargo-deny
- ✅ **安全审计**: 日志、入侵检测

### 最佳实践

1. **纵深防御**: 多层安全措施
2. **最小权限**: 只授予必要权限
3. **默认安全**: 安全的默认配置
4. **持续监控**: 实时安全监控
5. **定期审计**: 代码审计和渗透测试

---

**文档贡献者:** AI Assistant
**审核状态:** ✅ 已完成
**最后更新:** 2025年10月28日
