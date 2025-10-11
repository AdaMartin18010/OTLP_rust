# 🦀 OpenTelemetry 数据隐私与合规 - Rust 1.90版

> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月11日

---

## 📋 目录

- [🦀 OpenTelemetry 数据隐私与合规 - Rust 1.90版](#-opentelemetry-数据隐私与合规---rust-190版)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [为什么需要关注隐私合规](#为什么需要关注隐私合规)
  - [🇪🇺 GDPR合规](#-gdpr合规)
    - [核心要求](#核心要求)
    - [数据最小化](#数据最小化)
    - [IP地址匿名化](#ip地址匿名化)
    - [用户数据删除 (被遗忘权)](#用户数据删除-被遗忘权)
  - [💳 PCI-DSS合规](#-pci-dss合规)
    - [信用卡数据保护](#信用卡数据保护)
    - [Token化](#token化)
  - [🏥 HIPAA合规](#-hipaa合规)
    - [PHI (Protected Health Information) 处理](#phi-protected-health-information-处理)
  - [🔒 数据匿名化](#-数据匿名化)
    - [K-匿名性](#k-匿名性)
    - [差分隐私](#差分隐私)
  - [📅 数据保留策略](#-数据保留策略)
    - [自动过期](#自动过期)
  - [📋 审计日志](#-审计日志)
    - [审计日志系统](#审计日志系统)
  - [✅ 合规检查清单](#-合规检查清单)
    - [实现检查](#实现检查)
  - [🔧 完整实现示例](#-完整实现示例)
  - [📚 参考资源](#-参考资源)

---

## 🎯 概述

### 为什么需要关注隐私合规

遥测数据可能包含:

1. **个人可识别信息 (PII)**
   - 邮箱地址
   - IP地址
   - 用户ID
   - 电话号码

2. **敏感业务数据**
   - 交易金额
   - 账户余额
   - 信用卡信息

3. **健康信息 (PHI)**
   - 医疗记录ID
   - 诊断代码

**风险**:

- 法律责任 (罚款高达€20M或4%营收)
- 声誉损失
- 客户信任流失
- 数据泄露

---

## 🇪🇺 GDPR合规

### 核心要求

```rust
/// GDPR合规处理器
pub struct GdprProcessor {
    /// PII字段列表
    pii_fields: HashSet<String>,
    /// 哈希盐值
    salt: String,
}

impl GdprProcessor {
    pub fn new(salt: String) -> Self {
        let pii_fields = [
            "user.email",
            "user.phone",
            "user.name",
            "user.address",
            "http.client.ip",
            "user.ssn",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect();
        
        Self { pii_fields, salt }
    }
}
```

### 数据最小化

```rust
use opentelemetry::KeyValue;
use std::collections::HashSet;

impl GdprProcessor {
    /// 删除PII字段
    pub fn remove_pii(&self, attributes: Vec<KeyValue>) -> Vec<KeyValue> {
        attributes
            .into_iter()
            .filter(|kv| !self.pii_fields.contains(kv.key.as_str()))
            .collect()
    }
    
    /// 哈希敏感字段
    pub fn hash_sensitive_fields(&self, attributes: Vec<KeyValue>) -> Vec<KeyValue> {
        attributes
            .into_iter()
            .map(|mut kv| {
                if self.pii_fields.contains(kv.key.as_str()) {
                    if let Some(value) = kv.value.as_str() {
                        kv.value = self.hash_value(value).into();
                    }
                }
                kv
            })
            .collect()
    }
    
    fn hash_value(&self, value: &str) -> String {
        use sha2::{Sha256, Digest};
        
        let mut hasher = Sha256::new();
        hasher.update(format!("{}{}", self.salt, value));
        format!("{:x}", hasher.finalize())
    }
}
```

### IP地址匿名化

```rust
use std::net::IpAddr;

pub struct IpAnonymizer;

impl IpAnonymizer {
    /// IPv4: 保留前3个八位组
    /// IPv6: 保留前48位
    pub fn anonymize(ip: &str) -> anyhow::Result<String> {
        let addr: IpAddr = ip.parse()?;
        
        match addr {
            IpAddr::V4(v4) => {
                let octets = v4.octets();
                Ok(format!("{}.{}.{}.0", octets[0], octets[1], octets[2]))
            }
            IpAddr::V6(v6) => {
                let segments = v6.segments();
                Ok(format!("{}:{}:{}::", segments[0], segments[1], segments[2]))
            }
        }
    }
}

// 使用示例
let anonymized = IpAnonymizer::anonymize("192.168.1.100")?;
// 结果: "192.168.1.0"
```

### 用户数据删除 (被遗忘权)

```rust
use async_trait::async_trait;

#[async_trait]
pub trait DataDeletionService {
    async fn delete_user_data(&self, user_id: &str) -> anyhow::Result<()>;
}

pub struct OtlpDataDeletionService {
    // 后端存储连接
    storage_client: Arc<dyn StorageClient>,
}

#[async_trait]
impl DataDeletionService for OtlpDataDeletionService {
    async fn delete_user_data(&self, user_id: &str) -> anyhow::Result<()> {
        // 1. 哈希user_id (与追踪时使用相同的哈希)
        let hashed_user_id = self.hash_user_id(user_id);
        
        // 2. 删除所有包含该user_id的traces
        self.storage_client
            .delete_traces_by_attribute("user.id", &hashed_user_id)
            .await?;
        
        // 3. 删除metrics
        self.storage_client
            .delete_metrics_by_attribute("user.id", &hashed_user_id)
            .await?;
        
        // 4. 删除logs
        self.storage_client
            .delete_logs_by_attribute("user.id", &hashed_user_id)
            .await?;
        
        // 5. 记录审计日志
        self.log_deletion_audit(user_id).await?;
        
        Ok(())
    }
}
```

---

## 💳 PCI-DSS合规

### 信用卡数据保护

```rust
use regex::Regex;

pub struct PciDssFilter {
    card_pattern: Regex,
    cvv_pattern: Regex,
}

impl PciDssFilter {
    pub fn new() -> Self {
        Self {
            // 匹配信用卡号 (Luhn算法验证)
            card_pattern: Regex::new(
                r"\b\d{4}[\s-]?\d{4}[\s-]?\d{4}[\s-]?\d{4}\b"
            ).unwrap(),
            
            // 匹配CVV
            cvv_pattern: Regex::new(r"\b\d{3,4}\b").unwrap(),
        }
    }
    
    /// 脱敏信用卡号
    pub fn mask_card_number(&self, input: &str) -> String {
        self.card_pattern.replace_all(input, "****-****-****-****").to_string()
    }
    
    /// 删除CVV
    pub fn remove_cvv(&self, input: &str) -> String {
        self.cvv_pattern.replace_all(input, "***").to_string()
    }
    
    /// 处理attributes
    pub fn sanitize_attributes(&self, attributes: Vec<KeyValue>) -> Vec<KeyValue> {
        attributes
            .into_iter()
            .map(|mut kv| {
                if let Some(s) = kv.value.as_str() {
                    let sanitized = self.mask_card_number(s);
                    let sanitized = self.remove_cvv(&sanitized);
                    kv.value = sanitized.into();
                }
                kv
            })
            .collect()
    }
}
```

### Token化

```rust
use uuid::Uuid;
use std::collections::HashMap;

pub struct TokenizationService {
    // 实际环境中应使用安全的密钥管理服务
    token_map: Arc<RwLock<HashMap<String, String>>>,
}

impl TokenizationService {
    pub fn new() -> Self {
        Self {
            token_map: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    /// 将敏感值替换为token
    pub async fn tokenize(&self, sensitive_value: &str) -> String {
        let token = Uuid::new_v4().to_string();
        
        let mut map = self.token_map.write().await;
        map.insert(token.clone(), sensitive_value.to_string());
        
        token
    }
    
    /// 解token化 (仅用于授权服务)
    pub async fn detokenize(&self, token: &str) -> Option<String> {
        let map = self.token_map.read().await;
        map.get(token).cloned()
    }
}

// 使用示例
let service = TokenizationService::new();

// 创建span时token化
let card_token = service.tokenize("4532-1234-5678-9010").await;
span.set_attribute(KeyValue::new("payment.card_token", card_token));
// 不保存实际卡号
```

---

## 🏥 HIPAA合规

### PHI (Protected Health Information) 处理

```rust
pub struct HipaaProcessor {
    phi_fields: HashSet<String>,
}

impl HipaaProcessor {
    pub fn new() -> Self {
        let phi_fields = [
            "patient.id",
            "patient.name",
            "patient.ssn",
            "patient.dob",
            "patient.medical_record_number",
            "diagnosis.code",
            "prescription.details",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect();
        
        Self { phi_fields }
    }
    
    /// 删除所有PHI
    pub fn remove_phi(&self, attributes: Vec<KeyValue>) -> Vec<KeyValue> {
        attributes
            .into_iter()
            .filter(|kv| !self.phi_fields.contains(kv.key.as_str()))
            .collect()
    }
    
    /// 加密PHI (使用AES-256)
    pub fn encrypt_phi(&self, attributes: Vec<KeyValue>) -> anyhow::Result<Vec<KeyValue>> {
        use aes_gcm::{
            aead::{Aead, KeyInit},
            Aes256Gcm, Nonce,
        };
        
        let key = self.load_encryption_key()?;
        let cipher = Aes256Gcm::new(&key);
        
        let result: Result<Vec<_>, _> = attributes
            .into_iter()
            .map(|mut kv| {
                if self.phi_fields.contains(kv.key.as_str()) {
                    if let Some(value) = kv.value.as_str() {
                        let nonce = Nonce::from_slice(b"unique nonce"); // 实际使用随机nonce
                        let encrypted = cipher.encrypt(nonce, value.as_bytes())?;
                        kv.value = base64::encode(&encrypted).into();
                    }
                }
                Ok(kv)
            })
            .collect();
        
        result
    }
    
    fn load_encryption_key(&self) -> anyhow::Result<aes_gcm::Key<Aes256Gcm>> {
        // 从密钥管理服务加载
        todo!("Load from key management service")
    }
}
```

---

## 🔒 数据匿名化

### K-匿名性

```rust
pub struct KAnonymizer {
    k: usize, // 至少k个记录共享相同的准标识符
}

impl KAnonymizer {
    pub fn new(k: usize) -> Self {
        Self { k }
    }
    
    /// 泛化年龄
    pub fn generalize_age(&self, age: u32) -> String {
        match age {
            0..=17 => "0-17".to_string(),
            18..=30 => "18-30".to_string(),
            31..=45 => "31-45".to_string(),
            46..=60 => "46-60".to_string(),
            _ => "60+".to_string(),
        }
    }
    
    /// 泛化邮编
    pub fn generalize_zipcode(&self, zipcode: &str) -> String {
        if zipcode.len() >= 3 {
            format!("{}***", &zipcode[..3])
        } else {
            "***".to_string()
        }
    }
}
```

### 差分隐私

```rust
use rand::Rng;

pub struct DifferentialPrivacy {
    epsilon: f64, // 隐私预算
}

impl DifferentialPrivacy {
    pub fn new(epsilon: f64) -> Self {
        Self { epsilon }
    }
    
    /// 添加拉普拉斯噪声
    pub fn add_laplace_noise(&self, value: f64, sensitivity: f64) -> f64 {
        let mut rng = rand::thread_rng();
        
        // 拉普拉斯分布参数
        let lambda = sensitivity / self.epsilon;
        
        // 生成拉普拉斯噪声
        let u: f64 = rng.gen_range(-0.5..0.5);
        let noise = -lambda * u.signum() * (1.0 - 2.0 * u.abs()).ln();
        
        value + noise
    }
    
    /// 为计数添加噪声
    pub fn noisy_count(&self, true_count: u64) -> u64 {
        let noisy = self.add_laplace_noise(true_count as f64, 1.0);
        noisy.max(0.0) as u64
    }
}

// 使用示例
let dp = DifferentialPrivacy::new(0.1);
let true_count = 1000u64;
let noisy_count = dp.noisy_count(true_count);
// 结果: 约1000 ± 噪声
```

---

## 📅 数据保留策略

### 自动过期

```rust
use chrono::{DateTime, Duration, Utc};

#[derive(Clone)]
pub struct RetentionPolicy {
    /// traces保留期
    pub traces_retention: Duration,
    /// metrics保留期
    pub metrics_retention: Duration,
    /// logs保留期
    pub logs_retention: Duration,
}

impl RetentionPolicy {
    /// GDPR建议: 最多6个月
    pub fn gdpr_compliant() -> Self {
        Self {
            traces_retention: Duration::days(90),  // 3个月
            metrics_retention: Duration::days(180), // 6个月
            logs_retention: Duration::days(30),    // 1个月
        }
    }
    
    /// 检查数据是否应删除
    pub fn should_delete_trace(&self, timestamp: DateTime<Utc>) -> bool {
        Utc::now() - timestamp > self.traces_retention
    }
}

pub struct DataRetentionService {
    policy: RetentionPolicy,
    storage: Arc<dyn StorageClient>,
}

impl DataRetentionService {
    /// 启动自动清理任务
    pub async fn start_cleanup_job(self: Arc<Self>) {
        let mut interval = tokio::time::interval(Duration::hours(24).to_std().unwrap());
        
        loop {
            interval.tick().await;
            
            if let Err(e) = self.cleanup_expired_data().await {
                eprintln!("❌ Cleanup failed: {}", e);
            } else {
                println!("✅ Cleanup completed");
            }
        }
    }
    
    async fn cleanup_expired_data(&self) -> anyhow::Result<()> {
        let cutoff_traces = Utc::now() - self.policy.traces_retention;
        let cutoff_metrics = Utc::now() - self.policy.metrics_retention;
        let cutoff_logs = Utc::now() - self.policy.logs_retention;
        
        // 删除过期数据
        self.storage.delete_traces_before(cutoff_traces).await?;
        self.storage.delete_metrics_before(cutoff_metrics).await?;
        self.storage.delete_logs_before(cutoff_logs).await?;
        
        Ok(())
    }
}
```

---

## 📋 审计日志

### 审计日志系统

```rust
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub struct AuditLog {
    timestamp: DateTime<Utc>,
    action: AuditAction,
    actor: String,
    resource: String,
    result: AuditResult,
    metadata: HashMap<String, String>,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AuditAction {
    DataAccess,
    DataDeletion,
    DataExport,
    ConfigChange,
    UserAuthentication,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AuditResult {
    Success,
    Failure { reason: String },
}

impl AuditLog {
    pub fn new(
        action: AuditAction,
        actor: String,
        resource: String,
        result: AuditResult,
    ) -> Self {
        Self {
            timestamp: Utc::now(),
            action,
            actor,
            resource,
            result,
            metadata: HashMap::new(),
        }
    }
    
    pub fn with_metadata(mut self, key: String, value: String) -> Self {
        self.metadata.insert(key, value);
        self
    }
    
    /// 写入审计日志
    pub async fn write(&self) -> anyhow::Result<()> {
        let log_entry = serde_json::to_string(self)?;
        
        // 1. 写入文件
        tokio::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open("/var/log/otlp/audit.log")
            .await?
            .write_all(format!("{}\n", log_entry).as_bytes())
            .await?;
        
        // 2. 发送到SIEM
        // self.send_to_siem(&log_entry).await?;
        
        Ok(())
    }
}

// 使用示例
AuditLog::new(
    AuditAction::DataDeletion,
    "user@example.com".to_string(),
    "user_data:12345".to_string(),
    AuditResult::Success,
)
.with_metadata("reason".to_string(), "GDPR request".to_string())
.write()
.await?;
```

---

## ✅ 合规检查清单

### 实现检查

```rust
#[derive(Debug)]
pub struct ComplianceChecklist {
    items: Vec<ComplianceItem>,
}

#[derive(Debug)]
pub struct ComplianceItem {
    name: String,
    required: bool,
    implemented: bool,
    framework: ComplianceFramework,
}

#[derive(Debug, PartialEq)]
pub enum ComplianceFramework {
    GDPR,
    PCIDSS,
    HIPAA,
    SOC2,
}

impl ComplianceChecklist {
    pub fn new() -> Self {
        let items = vec![
            ComplianceItem {
                name: "PII数据脱敏".to_string(),
                required: true,
                implemented: false,
                framework: ComplianceFramework::GDPR,
            },
            ComplianceItem {
                name: "数据加密传输(TLS)".to_string(),
                required: true,
                implemented: false,
                framework: ComplianceFramework::PCIDSS,
            },
            ComplianceItem {
                name: "访问审计日志".to_string(),
                required: true,
                implemented: false,
                framework: ComplianceFramework::HIPAA,
            },
            ComplianceItem {
                name: "数据保留策略".to_string(),
                required: true,
                implemented: false,
                framework: ComplianceFramework::GDPR,
            },
            ComplianceItem {
                name: "用户数据删除机制".to_string(),
                required: true,
                implemented: false,
                framework: ComplianceFramework::GDPR,
            },
        ];
        
        Self { items }
    }
    
    pub fn print_report(&self) {
        println!("\n📋 合规检查报告\n");
        
        for framework in [
            ComplianceFramework::GDPR,
            ComplianceFramework::PCIDSS,
            ComplianceFramework::HIPAA,
            ComplianceFramework::SOC2,
        ] {
            self.print_framework_status(&framework);
        }
    }
    
    fn print_framework_status(&self, framework: &ComplianceFramework) {
        let items: Vec<_> = self.items
            .iter()
            .filter(|item| &item.framework == framework)
            .collect();
        
        if items.is_empty() {
            return;
        }
        
        println!("═══ {:?} ═══", framework);
        
        for item in items {
            let icon = if item.implemented { "✅" } else { "❌" };
            println!("  {} {}", icon, item.name);
        }
        
        println!();
    }
}
```

---

## 🔧 完整实现示例

```rust
use opentelemetry::{global, trace::Tracer, KeyValue};

/// 创建合规的Tracer
pub async fn create_compliant_tracer() -> anyhow::Result<()> {
    // 1. 初始化处理器
    let gdpr_processor = Arc::new(GdprProcessor::new(
        std::env::var("GDPR_SALT").unwrap_or_default()
    ));
    let pci_filter = Arc::new(PciDssFilter::new());
    
    // 2. 创建Tracer
    let tracer_provider = init_tracer()?;
    let tracer = global::tracer("compliant-app");
    
    // 3. 创建Span并应用合规处理
    let mut span = tracer.start("sensitive-operation");
    
    // 原始attributes
    let attributes = vec![
        KeyValue::new("user.email", "user@example.com"),
        KeyValue::new("payment.card", "4532-1234-5678-9010"),
        KeyValue::new("http.client.ip", "192.168.1.100"),
    ];
    
    // 应用GDPR处理
    let attributes = gdpr_processor.hash_sensitive_fields(attributes);
    
    // 应用PCI-DSS处理
    let attributes = pci_filter.sanitize_attributes(attributes);
    
    // 设置attributes
    for kv in attributes {
        span.set_attribute(kv);
    }
    
    span.end();
    
    // 4. 确保优雅关闭
    tracer_provider.shutdown()?;
    
    Ok(())
}
```

---

## 📚 参考资源

| 框架 | 官方文档 |
|------|---------|
| **GDPR** | <https://gdpr.eu/> |
| **PCI-DSS** | <https://www.pcisecuritystandards.org/> |
| **HIPAA** | <https://www.hhs.gov/hipaa/> |
| **SOC2** | <https://www.aicpa.org/soc> |
| **OWASP** | <https://owasp.org/www-project-top-ten/> |

---

**最后更新**: 2025年10月11日  
**Rust版本**: 1.90+  
**OpenTelemetry**: 0.31.0  
**系列**: 安全与合规 - Rust完整版 🎉
