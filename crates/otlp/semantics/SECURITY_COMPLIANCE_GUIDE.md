# 安全与合规完整指南

> **版本**: 1.0
> **日期**: 2025年10月17日
> **状态**: ✅ 完整版

---

## 📋 目录

- [安全与合规完整指南](#安全与合规完整指南)
  - [📋 目录](#-目录)
  - [第一部分: 安全威胁模型](#第一部分-安全威胁模型)
    - [1.1 威胁分类](#11-威胁分类)
    - [1.2 风险评估矩阵](#12-风险评估矩阵)
    - [1.3 安全设计原则](#13-安全设计原则)
  - [第二部分: 数据加密](#第二部分-数据加密)
    - [2.1 传输加密(TLS)](#21-传输加密tls)
      - [2.1.1 生成证书](#211-生成证书)
      - [2.1.2 Collector TLS配置](#212-collector-tls配置)
      - [2.1.3 应用SDK TLS配置](#213-应用sdk-tls配置)
    - [2.2 存储加密](#22-存储加密)
      - [2.2.1 静态数据加密](#221-静态数据加密)
      - [2.2.2 云存储加密](#222-云存储加密)
  - [第三部分: 认证与授权](#第三部分-认证与授权)
    - [3.1 认证机制](#31-认证机制)
      - [3.1.1 mTLS认证](#311-mtls认证)
      - [3.1.2 Bearer Token认证](#312-bearer-token认证)
      - [3.1.3 OIDC认证](#313-oidc认证)
    - [3.2 授权(RBAC)](#32-授权rbac)
      - [3.2.1 Kubernetes RBAC](#321-kubernetes-rbac)
      - [3.2.2 Jaeger授权](#322-jaeger授权)
  - [第四部分: PII与数据脱敏](#第四部分-pii与数据脱敏)
    - [4.1 PII识别](#41-pii识别)
    - [4.2 数据脱敏策略](#42-数据脱敏策略)
      - [4.2.1 Collector脱敏](#421-collector脱敏)
      - [4.2.2 SDK脱敏](#422-sdk脱敏)
    - [4.3 数据最小化](#43-数据最小化)
  - [第五部分: 审计与日志](#第五部分-审计与日志)
    - [5.1 审计日志](#51-审计日志)
      - [5.1.1 记录内容](#511-记录内容)
      - [5.1.2 审计日志格式](#512-审计日志格式)
      - [5.1.3 审计日志实现](#513-审计日志实现)
    - [5.2 告警规则](#52-告警规则)
  - [第六部分: 合规性](#第六部分-合规性)
    - [6.1 GDPR合规](#61-gdpr合规)
      - [6.1.1 数据保留策略实现](#611-数据保留策略实现)
      - [6.1.2 数据删除请求处理](#612-数据删除请求处理)
    - [6.2 HIPAA合规(医疗行业)](#62-hipaa合规医疗行业)
    - [6.3 SOC 2合规](#63-soc-2合规)
  - [第七部分: 安全加固](#第七部分-安全加固)
    - [7.1 网络隔离](#71-网络隔离)
    - [7.2 容器安全](#72-容器安全)
    - [7.3 镜像安全](#73-镜像安全)
    - [7.4 漏洞管理](#74-漏洞管理)
  - [第八部分: 应急响应](#第八部分-应急响应)
    - [8.1 事件分类](#81-事件分类)
    - [8.2 应急响应流程](#82-应急响应流程)
    - [8.3 数据泄露响应](#83-数据泄露响应)
    - [8.4 应急演练](#84-应急演练)
  - [📚 参考资源](#-参考资源)

---

## 第一部分: 安全威胁模型

### 1.1 威胁分类

```text
可观测性系统威胁:
├── 数据泄露
│   ├── PII泄露(姓名、邮箱、手机号)
│   ├── 密钥泄露(API Key、密码、Token)
│   ├── 业务数据泄露(订单、交易)
│   └── 基础设施信息泄露(IP、拓扑)
│
├── 未授权访问
│   ├── 绕过认证
│   ├── 权限提升
│   ├── 跨租户访问
│   └── API滥用
│
├── 数据篡改
│   ├── Span注入/篡改
│   ├── 日志伪造
│   ├── 指标污染
│   └── 配置篡改
│
├── 拒绝服务(DoS)
│   ├── Span洪水
│   ├── 存储耗尽
│   ├── 查询轰炸
│   └── 资源耗尽
│
└── 供应链攻击
    ├── 恶意SDK
    ├── Collector漏洞
    ├── 依赖劫持
    └── 镜像投毒
```

### 1.2 风险评估矩阵

| 威胁 | 可能性 | 影响 | 风险等级 | 优先级 |
|------|--------|------|---------|--------|
| **PII泄露** | 高 | 严重 | 🔴 Critical | P0 |
| **密钥泄露** | 中 | 严重 | 🔴 Critical | P0 |
| **未授权访问** | 中 | 高 | 🟠 High | P1 |
| **数据篡改** | 低 | 高 | 🟠 High | P1 |
| **DoS攻击** | 中 | 中 | 🟡 Medium | P2 |
| **供应链攻击** | 低 | 严重 | 🟠 High | P1 |

### 1.3 安全设计原则

```yaml
security_principles:
  1_defense_in_depth:
    description: "多层防御,单点失效不导致系统失陷"
    examples:
      - 传输加密 + 存储加密
      - 认证 + 授权 + 审计
      - 网络隔离 + 应用隔离

  2_least_privilege:
    description: "最小权限,只授予必要的权限"
    examples:
      - Collector只读配置
      - 应用只能写入Traces
      - 查询用户只读后端

  3_zero_trust:
    description: "零信任,不信任任何来源"
    examples:
      - 内部流量也加密
      - 每次请求都认证
      - 持续验证

  4_secure_by_default:
    description: "默认安全,安全配置为默认"
    examples:
      - 默认启用TLS
      - 默认脱敏PII
      - 默认最小权限

  5_privacy_by_design:
    description: "隐私设计,从设计开始保护隐私"
    examples:
      - 数据最小化
      - 本地脱敏
      - 定期清理
```

---

## 第二部分: 数据加密

### 2.1 传输加密(TLS)

#### 2.1.1 生成证书

```bash
# 生成CA
cfssl gencert -initca ca-csr.json | cfssljson -bare ca

# ca-csr.json
{
  "CN": "OTel CA",
  "key": {
    "algo": "rsa",
    "size": 4096
  },
  "names": [{
    "C": "US",
    "ST": "California",
    "L": "San Francisco",
    "O": "MyOrg",
    "OU": "Security"
  }],
  "ca": {
    "expiry": "87600h"
  }
}

# 生成Collector服务器证书
cfssl gencert \
  -ca=ca.pem \
  -ca-key=ca-key.pem \
  -config=ca-config.json \
  -profile=server \
  collector-csr.json | cfssljson -bare collector-server

# collector-csr.json
{
  "CN": "otel-collector.observability.svc.cluster.local",
  "key": {
    "algo": "rsa",
    "size": 2048
  },
  "names": [{
    "C": "US",
    "ST": "California",
    "L": "San Francisco",
    "O": "MyOrg",
    "OU": "Observability"
  }],
  "hosts": [
    "otel-collector",
    "otel-collector.observability",
    "otel-collector.observability.svc",
    "otel-collector.observability.svc.cluster.local",
    "localhost",
    "127.0.0.1"
  ]
}

# 生成客户端证书
cfssl gencert \
  -ca=ca.pem \
  -ca-key=ca-key.pem \
  -config=ca-config.json \
  -profile=client \
  client-csr.json | cfssljson -bare client
```

#### 2.1.2 Collector TLS配置

```yaml
# otel-collector-config.yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        tls:
          cert_file: /certs/server.crt
          key_file: /certs/server.key
          client_ca_file: /certs/ca.crt  # mTLS

          # TLS版本
          min_version: "1.3"
          max_version: "1.3"

          # 加密套件
          cipher_suites:
            - TLS_AES_128_GCM_SHA256
            - TLS_AES_256_GCM_SHA384
            - TLS_CHACHA20_POLY1305_SHA256

          # 客户端认证
          client_auth_type: RequireAndVerifyClientCert

exporters:
  otlp:
    endpoint: backend:4317
    tls:
      insecure: false
      ca_file: /certs/ca.crt
      cert_file: /certs/client.crt
      key_file: /certs/client.key
      server_name_override: backend.example.com
```

#### 2.1.3 应用SDK TLS配置

```rust
use opentelemetry_otlp::WithExportConfig;
use tonic::transport::ClientTlsConfig;

// 配置TLS
let tls_config = ClientTlsConfig::new()
    .ca_certificate(Certificate::from_pem(ca_cert))
    .identity(Identity::from_pem(client_cert, client_key))
    .domain_name("otel-collector.example.com");

// 创建exporter
let exporter = opentelemetry_otlp::new_exporter()
    .tonic()
    .with_endpoint("https://otel-collector:4317")
    .with_tls_config(tls_config)
    .with_timeout(Duration::from_secs(10));

let tracer = opentelemetry_otlp::new_pipeline()
    .tracing()
    .with_exporter(exporter)
    .install_batch(opentelemetry_sdk::runtime::Tokio)?;
```

### 2.2 存储加密

#### 2.2.1 静态数据加密

```yaml
# Elasticsearch加密
elasticsearch:
  # 节点间通信加密
  xpack.security.transport.ssl.enabled: true
  xpack.security.transport.ssl.verification_mode: certificate
  xpack.security.transport.ssl.key: /certs/node.key
  xpack.security.transport.ssl.certificate: /certs/node.crt
  xpack.security.transport.ssl.certificate_authorities: ["/certs/ca.crt"]

  # HTTP加密
  xpack.security.http.ssl.enabled: true
  xpack.security.http.ssl.key: /certs/node.key
  xpack.security.http.ssl.certificate: /certs/node.crt

  # 索引加密(需要企业版)
  xpack.security.encryption.enabled: true
  xpack.security.encryption.key: "your-encryption-key"

# Kubernetes Secret加密(etcd)
apiVersion: apiserver.config.k8s.io/v1
kind: EncryptionConfiguration
resources:
  - resources:
      - secrets
    providers:
      - aescbc:
          keys:
            - name: key1
              secret: <base64-encoded-key>
      - identity: {}
```

#### 2.2.2 云存储加密

```yaml
# AWS S3加密(用于长期存储)
s3_storage:
  # 服务端加密
  server_side_encryption:
    type: AES256  # 或 aws:kms
    kms_key_id: arn:aws:kms:region:account:key/key-id

  # Bucket策略强制加密
  bucket_policy:
    effect: Deny
    condition:
      StringNotEquals:
        s3:x-amz-server-side-encryption: aws:kms

# GCS加密
gcs_storage:
  # 客户端加密密钥
  encryption:
    type: CUSTOMER_SUPPLIED_ENCRYPTION_KEY
    key: <base64-encoded-key>
```

---

## 第三部分: 认证与授权

### 3.1 认证机制

#### 3.1.1 mTLS认证

```yaml
# Collector mTLS配置(已在2.1.2展示)

# 验证客户端证书
receivers:
  otlp:
    protocols:
      grpc:
        tls:
          client_auth_type: RequireAndVerifyClientCert
          client_ca_file: /certs/ca.crt
```

#### 3.1.2 Bearer Token认证

```yaml
# Collector配置
extensions:
  bearertokenauth:
    scheme: "Bearer"
    # Token验证(可选)
    token_file: /secrets/valid-tokens.txt

receivers:
  otlp:
    protocols:
      grpc:
        auth:
          authenticator: bearertokenauth

service:
  extensions: [bearertokenauth]
```

```rust
// SDK配置
use tonic::metadata::MetadataValue;
use opentelemetry_otlp::WithExportConfig;

let token = "your-secret-token";
let mut metadata = tonic::metadata::MetadataMap::new();
metadata.insert(
    "authorization",
    MetadataValue::from_str(&format!("Bearer {}", token)).unwrap(),
);

let exporter = opentelemetry_otlp::new_exporter()
    .tonic()
    .with_endpoint("https://otel-collector:4317")
    .with_metadata(metadata);
```

#### 3.1.3 OIDC认证

```yaml
# Collector配置
extensions:
  oidc:
    issuer_url: https://idp.example.com
    audience: otel-collector

    # JWT验证
    jwks_url: https://idp.example.com/.well-known/jwks.json

    # Claim映射
    username_claim: email
    groups_claim: groups

receivers:
  otlp:
    protocols:
      grpc:
        auth:
          authenticator: oidc
```

### 3.2 授权(RBAC)

#### 3.2.1 Kubernetes RBAC

```yaml
# ServiceAccount
apiVersion: v1
kind: ServiceAccount
metadata:
  name: app-traces
  namespace: default

---
# Role(只能写入Traces)
apiVersion: rbac.authorization.k8s.io/v1
kind: Role
metadata:
  name: traces-writer
  namespace: observability
rules:
  - apiGroups: [""]
    resources: ["services"]
    resourceNames: ["otel-collector"]
    verbs: ["create"]  # 只能创建(写入)

---
# RoleBinding
apiVersion: rbac.authorization.k8s.io/v1
kind: RoleBinding
metadata:
  name: app-traces-binding
  namespace: observability
subjects:
  - kind: ServiceAccount
    name: app-traces
    namespace: default
roleRef:
  kind: Role
  name: traces-writer
  apiGroup: rbac.authorization.k8s.io
```

#### 3.2.2 Jaeger授权

```yaml
# Jaeger with OAuth2 Proxy
apiVersion: apps/v1
kind: Deployment
metadata:
  name: jaeger-query
spec:
  template:
    spec:
      containers:
        # OAuth2 Proxy sidecar
        - name: oauth2-proxy
          image: quay.io/oauth2-proxy/oauth2-proxy:latest
          args:
            - --provider=oidc
            - --client-id=jaeger-query
            - --client-secret=$(CLIENT_SECRET)
            - --oidc-issuer-url=https://idp.example.com
            - --email-domain=*
            - --upstream=http://localhost:16686
            - --http-address=0.0.0.0:4180
          ports:
            - containerPort: 4180

        # Jaeger Query
        - name: jaeger-query
          image: jaegertracing/jaeger-query:latest
          ports:
            - containerPort: 16686

---
# Service(暴露OAuth2 Proxy)
apiVersion: v1
kind: Service
metadata:
  name: jaeger-query
spec:
  ports:
    - port: 80
      targetPort: 4180  # OAuth2 Proxy端口
  selector:
    app: jaeger-query
```

---

## 第四部分: PII与数据脱敏

### 4.1 PII识别

```yaml
# 常见PII类型
pii_types:
  identifiers:
    - 姓名
    - 邮箱
    - 手机号
    - 身份证号
    - 护照号
    - 驾照号
    - 社保号

  financial:
    - 信用卡号
    - 银行账号
    - 交易记录

  health:
    - 病历号
    - 诊断信息
    - 药物信息

  location:
    - 精确GPS坐标
    - 家庭地址
    - IP地址(某些场景)

  biometric:
    - 指纹
    - 面部识别数据
    - 声纹
```

### 4.2 数据脱敏策略

#### 4.2.1 Collector脱敏

```yaml
# OTTL脱敏示例
processors:
  transform:
    trace_statements:
      - context: span
        statements:
          # 1. 删除敏感字段
          - delete_key(attributes, "user.email")
          - delete_key(attributes, "user.phone")
          - delete_key(attributes, "credit_card")

          # 2. 正则匹配删除
          - delete_matching_keys(attributes, ".*password.*")
          - delete_matching_keys(attributes, ".*token.*")
          - delete_matching_keys(attributes, ".*secret.*")

          # 3. 哈希化
          - set(attributes["user.id"], SHA256(attributes["user.id"]))
            where attributes["user.id"] != nil

          # 4. 掩码(保留部分)
          - set(attributes["phone"],
                Concat("***-****-", Substring(attributes["phone"], -4, 4)))
            where attributes["phone"] != nil

          # 5. 泛化(降低精度)
          - set(attributes["age_group"],
                Int(attributes["age"]) / 10 * 10)
            where attributes["age"] != nil
          - delete_key(attributes, "age")

          # 6. SQL脱敏(截断)
          - set(attributes["db.statement"],
                Substring(attributes["db.statement"], 0, 1000))
            where Len(attributes["db.statement"]) > 1000

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [transform, batch]
      exporters: [otlp]
```

#### 4.2.2 SDK脱敏

```rust
use opentelemetry::trace::{Span, Tracer};
use regex::Regex;

// 敏感数据过滤器
pub struct SensitiveDataFilter {
    email_regex: Regex,
    phone_regex: Regex,
    credit_card_regex: Regex,
}

impl SensitiveDataFilter {
    pub fn new() -> Self {
        Self {
            email_regex: Regex::new(r"\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Z|a-z]{2,}\b").unwrap(),
            phone_regex: Regex::new(r"\b\d{3}[-.]?\d{3}[-.]?\d{4}\b").unwrap(),
            credit_card_regex: Regex::new(r"\b\d{4}[-\s]?\d{4}[-\s]?\d{4}[-\s]?\d{4}\b").unwrap(),
        }
    }

    // 脱敏字符串
    pub fn sanitize(&self, input: &str) -> String {
        let mut output = input.to_string();

        // 脱敏邮箱
        output = self.email_regex.replace_all(&output, "[EMAIL]").to_string();

        // 脱敏电话
        output = self.phone_regex.replace_all(&output, "[PHONE]").to_string();

        // 脱敏信用卡
        output = self.credit_card_regex.replace_all(&output, "[CARD]").to_string();

        output
    }
}

// Span处理器
pub struct SanitizingSpanProcessor {
    filter: SensitiveDataFilter,
    inner: Box<dyn opentelemetry::sdk::trace::SpanProcessor>,
}

impl opentelemetry::sdk::trace::SpanProcessor for SanitizingSpanProcessor {
    fn on_start(&self, span: &mut opentelemetry::sdk::trace::Span, cx: &opentelemetry::Context) {
        // 脱敏Span名称
        let sanitized_name = self.filter.sanitize(span.name());
        span.update_name(sanitized_name);

        // 脱敏属性
        for (key, value) in span.attributes_mut() {
            if let Some(string_value) = value.as_str() {
                let sanitized = self.filter.sanitize(string_value);
                *value = opentelemetry::Value::String(sanitized.into());
            }
        }

        self.inner.on_start(span, cx);
    }

    fn on_end(&self, span: opentelemetry::sdk::trace::SpanData) {
        self.inner.on_end(span);
    }

    fn force_flush(&self) -> opentelemetry::trace::TraceResult<()> {
        self.inner.force_flush()
    }

    fn shutdown(&mut self) -> opentelemetry::trace::TraceResult<()> {
        self.inner.shutdown()
    }
}
```

### 4.3 数据最小化

```yaml
# 属性白名单
attribute_whitelist:
  # 只保留必要属性
  allowed_attributes:
    - service.name
    - service.version
    - deployment.environment
    - http.method
    - http.status_code
    - http.route  # 已参数化
    - db.system
    - db.operation
    - error.type

  # 禁止的属性
  denied_attributes:
    - user.email
    - user.phone
    - user.address
    - credit_card.*
    - password
    - token
    - api_key

# Collector配置
processors:
  attributes:
    actions:
      # 只保留白名单
      - action: keep
        keys: [
          "service.name",
          "http.method",
          "http.status_code",
          # ...
        ]
```

---

## 第五部分: 审计与日志

### 5.1 审计日志

#### 5.1.1 记录内容

```yaml
audit_log_contents:
  authentication:
    - 登录成功/失败
    - Token颁发/撤销
    - 证书验证结果

  authorization:
    - 权限检查结果
    - 访问拒绝事件
    - 权限变更

  data_access:
    - Traces查询(who, when, what)
    - 配置读取/修改
    - 敏感数据访问

  configuration:
    - Collector配置变更
    - 采样率调整
    - 路由规则修改

  security_events:
    - 异常访问模式
    - 暴力破解尝试
    - 数据泄露迹象
```

#### 5.1.2 审计日志格式

```json
// 审计日志示例
{
  "timestamp": "2025-10-17T10:30:00Z",
  "event_type": "TRACE_QUERY",
  "severity": "INFO",
  "user": {
    "id": "user-123",
    "email": "alice@example.com",
    "roles": ["developer"]
  },
  "action": {
    "type": "query",
    "resource": "traces",
    "query": "service.name=payment AND error=true",
    "time_range": "2025-10-17T09:00:00Z to 2025-10-17T10:00:00Z"
  },
  "result": {
    "status": "success",
    "traces_returned": 42,
    "duration_ms": 123
  },
  "metadata": {
    "ip_address": "10.0.1.100",
    "user_agent": "Mozilla/5.0...",
    "session_id": "sess-abc123"
  }
}
```

#### 5.1.3 审计日志实现

```rust
// 审计日志系统
use serde::{Serialize, Deserialize};
use tracing::{info, warn};

#[derive(Serialize, Deserialize)]
pub struct AuditLog {
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub event_type: String,
    pub severity: String,
    pub user: UserInfo,
    pub action: ActionInfo,
    pub result: ResultInfo,
    pub metadata: Metadata,
}

pub struct AuditLogger {
    // 可以发送到专门的审计日志系统
}

impl AuditLogger {
    pub fn log_trace_query(&self, user: &UserInfo, query: &str, result: &QueryResult) {
        let audit_log = AuditLog {
            timestamp: chrono::Utc::now(),
            event_type: "TRACE_QUERY".to_string(),
            severity: "INFO".to_string(),
            user: user.clone(),
            action: ActionInfo {
                action_type: "query".to_string(),
                resource: "traces".to_string(),
                details: query.to_string(),
            },
            result: ResultInfo {
                status: if result.success { "success" } else { "failure" }.to_string(),
                traces_returned: result.count,
            },
            metadata: Metadata {
                ip_address: user.ip.clone(),
                user_agent: user.user_agent.clone(),
            },
        };

        info!("AUDIT: {}", serde_json::to_string(&audit_log).unwrap());

        // 发送到审计日志系统(如Elasticsearch)
        self.send_to_audit_system(&audit_log);
    }

    pub fn log_security_event(&self, event_type: &str, details: &str) {
        warn!("SECURITY_EVENT: type={} details={}", event_type, details);
        // 触发告警
    }
}
```

### 5.2 告警规则

```yaml
# 安全告警
security_alerts:
  - name: FailedAuthenticationSpike
    condition: |
      rate(audit_log_authentication_failures[5m]) > 10
    severity: warning
    description: "认证失败次数激增"

  - name: UnauthorizedAccessAttempt
    condition: |
      audit_log_authorization_denied > 0
    severity: critical
    description: "未授权访问尝试"

  - name: SensitiveDataAccess
    condition: |
      audit_log_sensitive_data_access{user_role!="admin"} > 0
    severity: high
    description: "非管理员访问敏感数据"

  - name: ConfigurationChanged
    condition: |
      audit_log_configuration_changes > 0
    severity: warning
    description: "配置被修改"
```

---

## 第六部分: 合规性

### 6.1 GDPR合规

```yaml
gdpr_requirements:
  data_minimization:
    - 只采集必要的遥测数据
    - 避免采集不必要的PII
    - 定期审查数据采集范围

  purpose_limitation:
    - 明确数据使用目的(可观测性)
    - 不得用于其他目的
    - 文档化数据处理流程

  storage_limitation:
    - 定义数据保留期(如30天)
    - 自动删除过期数据
    - 例外情况(如审计)需文档化

  data_subject_rights:
    - 访问权: 提供数据导出功能
    - 删除权: 支持数据删除请求
    - 更正权: 支持数据更正(如果适用)

  security:
    - 传输加密(TLS 1.3)
    - 存储加密(AES-256)
    - 访问控制(RBAC)
    - 审计日志

  data_breach:
    - 72小时内报告
    - 事件响应计划
    - 通知受影响用户
```

#### 6.1.1 数据保留策略实现

```yaml
# Elasticsearch ILM策略
PUT _ilm/policy/traces_policy
{
  "policy": {
    "phases": {
      "hot": {
        "min_age": "0ms",
        "actions": {
          "rollover": {
            "max_age": "1d",
            "max_size": "50GB"
          }
        }
      },
      "delete": {
        "min_age": "30d",  # 30天后删除(符合GDPR)
        "actions": {
          "delete": {}
        }
      }
    }
  }
}
```

#### 6.1.2 数据删除请求处理

```rust
// 处理数据删除请求
pub async fn handle_deletion_request(
    user_id: &str,
    es_client: &elasticsearch::Elasticsearch,
) -> Result<(), Box<dyn std::error::Error>> {
    // 1. 验证请求
    verify_deletion_request(user_id).await?;

    // 2. 查询相关数据
    let query = json!({
        "query": {
            "match": {
                "user.id": user_id
            }
        }
    });

    // 3. 删除Traces
    es_client
        .delete_by_query(DeleteByQueryParts::Index(&["jaeger-span-*"]))
        .body(query.clone())
        .send()
        .await?;

    // 4. 删除Logs
    es_client
        .delete_by_query(DeleteByQueryParts::Index(&["logs-*"]))
        .body(query)
        .send()
        .await?;

    // 5. 记录审计日志
    audit_logger.log_deletion(user_id);

    // 6. 通知用户
    notify_user_deletion_complete(user_id).await?;

    Ok(())
}
```

### 6.2 HIPAA合规(医疗行业)

```yaml
hipaa_requirements:
  access_control:
    - 唯一用户ID
    - 自动登出
    - 加密和解密控制

  audit_controls:
    - 记录所有PHI访问
    - 审计日志不可篡改
    - 定期审查

  integrity:
    - 数据完整性验证
    - 防篡改机制

  transmission_security:
    - 传输加密(TLS 1.3)
    - 完整性检查

  phi_minimization:
    - 脱敏PHI数据
    - 最小化PHI采集
```

### 6.3 SOC 2合规

```yaml
soc2_requirements:
  security:
    - 访问控制
    - 加密
    - 漏洞管理
    - 事件响应

  availability:
    - 高可用架构
    - 备份和恢复
    - 监控和告警

  processing_integrity:
    - 数据验证
    - 错误处理
    - 质量保证

  confidentiality:
    - 数据分类
    - 加密
    - 访问限制

  privacy:
    - PII保护
    - 同意管理
    - 数据最小化
```

---

## 第七部分: 安全加固

### 7.1 网络隔离

```yaml
# Kubernetes NetworkPolicy
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: otel-collector-policy
  namespace: observability
spec:
  podSelector:
    matchLabels:
      app: otel-collector

  policyTypes:
    - Ingress
    - Egress

  ingress:
    # 只允许应用命名空间访问
    - from:
        - namespaceSelector:
            matchLabels:
              purpose: application
      ports:
        - protocol: TCP
          port: 4317
        - protocol: TCP
          port: 4318

    # 允许Prometheus监控
    - from:
        - namespaceSelector:
            matchLabels:
              name: monitoring
      ports:
        - protocol: TCP
          port: 8888

  egress:
    # 只允许访问后端存储
    - to:
        - namespaceSelector:
            matchLabels:
              name: observability
        - podSelector:
            matchLabels:
              app: jaeger
      ports:
        - protocol: TCP
          port: 4317

    # 允许DNS
    - to:
        - namespaceSelector:
            matchLabels:
              name: kube-system
        - podSelector:
            matchLabels:
              k8s-app: kube-dns
      ports:
        - protocol: UDP
          port: 53
```

### 7.2 容器安全

```yaml
# Secur容器配置
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otel-collector
spec:
  template:
    spec:
      # 不使用root用户
      securityContext:
        runAsNonRoot: true
        runAsUser: 65534  # nobody
        fsGroup: 65534

      containers:
        - name: collector
          image: otel/opentelemetry-collector-contrib:0.89.0

          # 安全上下文
          securityContext:
            allowPrivilegeEscalation: false
            readOnlyRootFilesystem: true
            runAsNonRoot: true
            runAsUser: 65534
            capabilities:
              drop:
                - ALL
            seccompProfile:
              type: RuntimeDefault

          # 只读根文件系统,需要挂载可写目录
          volumeMounts:
            - name: config
              mountPath: /etc/otelcol
              readOnly: true
            - name: tmp
              mountPath: /tmp
            - name: cache
              mountPath: /var/cache

      volumes:
        - name: config
          configMap:
            name: otel-collector-config
        - name: tmp
          emptyDir: {}
        - name: cache
          emptyDir: {}
```

### 7.3 镜像安全

```dockerfile
# 安全的Dockerfile
FROM alpine:3.18 AS builder
RUN apk add --no-cache ca-certificates
COPY otel-collector /

FROM scratch
COPY --from=builder /etc/ssl/certs/ca-certificates.crt /etc/ssl/certs/
COPY --from=builder /otel-collector /
USER 65534:65534
ENTRYPOINT ["/otel-collector"]
```

```yaml
# 镜像扫描(CI/CD)
image_scanning:
  tools:
    - Trivy
    - Clair
    - Snyk

  policy:
    - 阻止CRITICAL漏洞
    - 警告HIGH漏洞
    - 定期重新扫描
```

### 7.4 漏洞管理

```yaml
vulnerability_management:
  scanning:
    frequency: daily
    tools: [Trivy, Dependabot]
    scope: [images, dependencies]

  patching:
    critical: 24h
    high: 7d
    medium: 30d
    low: 90d

  exceptions:
    - 需要批准
    - 有缓解措施
    - 定期审查
```

---

## 第八部分: 应急响应

### 8.1 事件分类

| 级别 | 说明 | 响应时间 | 示例 |
|------|------|---------|------|
| **P0** | 严重安全事件 | 立即 | 数据泄露、RCE |
| **P1** | 高危事件 | 1小时 | 未授权访问成功 |
| **P2** | 中危事件 | 4小时 | 配置错误、异常访问 |
| **P3** | 低危事件 | 24小时 | 失败的攻击尝试 |

### 8.2 应急响应流程

```text
1. 检测(Detection)
   - 自动告警触发
   - 人工发现
         │
         ▼
2. 分类(Triage)
   - 确定严重性
   - 分配负责人
         │
         ▼
3. 遏制(Containment)
   - 隔离受影响系统
   - 阻断攻击路径
         │
         ▼
4. 调查(Investigation)
   - 收集证据
   - 确定根因
   - 评估影响范围
         │
         ▼
5. 根除(Eradication)
   - 删除恶意内容
   - 修复漏洞
         │
         ▼
6. 恢复(Recovery)
   - 恢复服务
   - 验证正常
         │
         ▼
7. 总结(Lessons Learned)
   - 事后分析
   - 改进措施
   - 更新预案
```

### 8.3 数据泄露响应

```yaml
data_breach_response:
  immediate_actions:
    - 隔离受影响系统
    - 禁用泄露的凭证
    - 收集证据
    - 通知安全团队

  short_term_24h:
    - 评估泄露范围
    - 确定根因
    - 通知受影响用户
    - 监管机构报告(GDPR: 72h)

  medium_term_1week:
    - 修复漏洞
    - 强化安全措施
    - 公开声明(如需要)
    - 法律咨询

  long_term:
    - 事后分析
    - 流程改进
    - 培训和演练
    - 监控和验证
```

### 8.4 应急演练

```yaml
# 定期演练计划
drill_schedule:
  tabletop_exercise:
    frequency: quarterly
    participants: [security, ops, management]
    scenarios:
      - 数据泄露
      - 勒索软件
      - 内部威胁

  red_team_exercise:
    frequency: annually
    scope: 模拟真实攻击
    follow_up: 修复发现的问题

  disaster_recovery:
    frequency: semi-annually
    scenarios:
      - 数据中心故障
      - 全量数据丢失
      - 关键服务不可用
```

---

## 📚 参考资源

- [OWASP Top 10](https://owasp.org/www-project-top-ten/)
- [CIS Benchmarks](https://www.cisecurity.org/cis-benchmarks/)
- [NIST Cybersecurity Framework](https://www.nist.gov/cyberframework)
- [GDPR官方网站](https://gdpr.eu/)

---

**完整的安全与合规指南!** 🎓
