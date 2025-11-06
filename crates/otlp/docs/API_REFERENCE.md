# OTLP Rust API 参考文档

**版本**: 2.1
**最后更新**: 2025年10月27日
**Rust 版本**: 1.90.0 (LLD链接器、const API)
**状态**: 🟢 活跃维护

> **简介**: OTLP Rust 库的完整 API 参考文档，涵盖所有核心模块、类型、函数和使用示例。

---

## 📋 目录

- [OTLP Rust API 参考文档](#otlp-rust-api-参考文档)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
  - [📝 核心模块](#-核心模块)
    - [2.1 客户端模块](#21-客户端模块)
      - [OtlpClient](#otlpclient)
      - [配置选项](#配置选项)
    - [2.2 数据模型模块](#22-数据模型模块)
      - [2.2.1 TelemetryData](#221-telemetrydata)
      - [属性管理](#属性管理)
    - [2.3 性能优化器模块](#23-性能优化器模块)
      - [2.3.1 ComprehensivePerformanceOptimizer](#231-comprehensiveperformanceoptimizer)
      - [内存池管理](#内存池管理)
      - [SIMD优化](#simd优化)
    - [2.4 安全增强器模块](#24-安全增强器模块)
      - [2.4.1 ComprehensiveSecurityManager](#241-comprehensivesecuritymanager)
      - [加密管理](#加密管理)
      - [认证管理](#认证管理)
    - [2.5 监控集成模块](#25-监控集成模块)
      - [2.5.1 ComprehensiveMonitoringManager](#251-comprehensivemonitoringmanager)
      - [Grafana仪表板](#grafana仪表板)
    - [2.6 企业级功能模块](#26-企业级功能模块)
      - [2.6.1 ComprehensiveEnterpriseManager](#261-comprehensiveenterprisemanager)
      - [多租户管理](#多租户管理)
      - [数据治理](#数据治理)
  - [🔍 高级功能](#-高级功能)
    - [3.1 高级特性](#31-高级特性)
      - [智能缓存](#智能缓存)
      - [自适应采样](#自适应采样)
      - [AI异常检测](#ai异常检测)
    - [3.2 错误处理](#32-错误处理)
      - [3.2.1 错误类型](#321-错误类型)
      - [错误上下文](#错误上下文)
  - [🔧 性能优化](#-性能优化)
    - [4.1 内存优化](#41-内存优化)
    - [4.2 并发优化](#42-并发优化)
    - [4.3 缓存优化](#43-缓存优化)
  - [📊 安全最佳实践](#-安全最佳实践)
    - [5.1 数据加密](#51-数据加密)
    - [5.2 访问控制](#52-访问控制)
    - [5.3 审计日志](#53-审计日志)
  - [🚀 部署和运维](#-部署和运维)
    - [6.1 配置管理](#61-配置管理)
    - [6.2 健康检查](#62-健康检查)
    - [6.3 监控和告警](#63-监控和告警)
  - [🔬 示例项目](#-示例项目)
    - [7.1 完整的微服务示例](#71-完整的微服务示例)
  - [💻 相关资源](#-相关资源)
    - [8.1 官方文档](#81-官方文档)
    - [8.2 项目文档](#82-项目文档)
    - [8.3 社区资源](#83-社区资源)

---

## 🎯 概述

本文档提供了OTLP Rust库的完整API参考，包括所有模块、结构体、枚举和函数的详细说明。

---

## 📝 核心模块

### 2.1 客户端模块

#### OtlpClient

主要的OTLP客户端，用于发送遥测数据。

```rust
use otlp::{OtlpClient, OtlpClientBuilder, OtlpConfig};

// 创建客户端
let client = OtlpClientBuilder::new()
    .with_endpoint("http://localhost:4317")
    .with_config(OtlpConfig::default())
    .build()
    .await?;

// 发送追踪数据
let trace_builder = client.trace_builder();
trace_builder
    .with_trace_id("1234567890abcdef")
    .with_span_id("abcdef1234567890")
    .with_operation_name("user_login")
    .with_status_code(StatusCode::Ok)
    .send()
    .await?;
```

#### 配置选项

```rust
use otlp::{OtlpConfig, OtlpConfigBuilder, TransportProtocol, Compression};

let config = OtlpConfigBuilder::new()
    .with_endpoint("http://localhost:4317")
    .with_transport_protocol(TransportProtocol::Grpc)
    .with_compression(Compression::Gzip)
    .with_batch_config(BatchConfig {
        max_export_batch_size: 512,
        export_timeout: Duration::from_secs(30),
        max_queue_size: 2048,
    })
    .build();
```

### 2.2 数据模型模块

#### 2.2.1 TelemetryData

遥测数据的基础结构。

```rust
use otlp::{TelemetryData, TelemetryDataType, TelemetryContent, TraceData};

let telemetry_data = TelemetryData {
    data_type: TelemetryDataType::Trace,
    timestamp: SystemTime::now().duration_since(UNIX_EPOCH)?.as_secs(),
    resource_attributes: HashMap::new(),
    scope_attributes: HashMap::new(),
    content: TelemetryContent::Trace(TraceData {
        trace_id: "1234567890abcdef".to_string(),
        span_id: "abcdef1234567890".to_string(),
        parent_span_id: None,
        operation_name: "user_login".to_string(),
        start_time: SystemTime::now(),
        end_time: SystemTime::now(),
        status_code: StatusCode::Ok,
        attributes: HashMap::new(),
    }),
};
```

#### 属性管理

```rust
use otlp::{AttributeValue, TelemetryData};

let mut data = TelemetryData::default();
data.add_attribute("user.id", AttributeValue::String("user123".to_string()));
data.add_attribute("request.duration", AttributeValue::Int64(150));
data.add_attribute("error.occurred", AttributeValue::Bool(false));
```

### 2.3 性能优化器模块

#### 2.3.1 ComprehensivePerformanceOptimizer

综合性能优化器，提供内存池、SIMD优化、并发优化等功能。

```rust
use otlp::{ComprehensivePerformanceOptimizer, TelemetryData};

// 创建性能优化器
let mut optimizer = ComprehensivePerformanceOptimizer::new();

// 优化处理遥测数据
let test_data = vec![
    TelemetryData::default(),
    TelemetryData::default(),
];

let optimized_data = optimizer.optimize_processing(test_data).await?;

// 运行性能基准测试
let benchmark_results = optimizer.run_performance_benchmarks().await?;

// 获取综合统计信息
let stats = optimizer.get_comprehensive_stats();
println!("总操作数: {}", stats.total_operations);
println!("优化操作数: {}", stats.optimized_operations);
```

#### 内存池管理

```rust
use otlp::{HighPerformanceMemoryPool, PooledObject};

// 创建内存池
let pool = HighPerformanceMemoryPool::<String>::new(1000, 10);

// 获取池化对象
let pooled_obj = pool.acquire().await?;
let data = pooled_obj.get();
// 使用数据...

// 对象会在作用域结束时自动返回到池中
```

#### SIMD优化

```rust
use otlp::{SimdOptimizer, TelemetryData};

let optimizer = SimdOptimizer::new(100);

let test_data = vec![TelemetryData::default(); 1000];

// 批量处理数据
let results = optimizer.process_batch(test_data, |data| {
    // 自定义处理逻辑
    data.timestamp * 2
}).await?;
```

### 2.4 安全增强器模块

#### 2.4.1 ComprehensiveSecurityManager

综合安全管理器，提供加密、认证、审计等功能。

```rust
use otlp::{ComprehensiveSecurityManager, SecureRequest};

// 创建安全管理器
let security_manager = ComprehensiveSecurityManager::new();

// 处理安全请求
let request = SecureRequest {
    token: "valid_token".to_string(),
    resource: "user_data".to_string(),
    action: "read".to_string(),
    data: b"sensitive_data".to_vec(),
    encrypt: true,
    ip_address: Some("192.168.1.100".to_string()),
    user_agent: Some("Mozilla/5.0".to_string()),
};

let response = security_manager.process_secure_request(request).await?;

if response.success {
    println!("请求处理成功: {}", response.message);
} else {
    println!("请求被拒绝: {}", response.message);
}
```

#### 加密管理

```rust
use otlp::{EncryptionManager, EncryptionAlgorithm};

let encryption_manager = EncryptionManager::new();

// 加密数据
let plaintext = b"Hello, World!";
let encrypted_data = encryption_manager.encrypt(plaintext, "aes256gcm").await?;

// 解密数据
let decrypted_data = encryption_manager.decrypt(&encrypted_data).await?;
assert_eq!(plaintext, decrypted_data.as_slice());
```

#### 认证管理

```rust
use otlp::{AuthenticationManager, AuthResult};

let auth_manager = AuthenticationManager::new();

// 用户登录
let login_result = auth_manager.login("username", "password").await?;

if login_result.success {
    let session = login_result.session.unwrap();
    println!("登录成功，会话ID: {}", session.id);

    // 验证令牌
    let validation_result = auth_manager.validate_token(&session.token).await?;
    if validation_result.valid {
        println!("令牌有效，用户ID: {}", validation_result.user_id.unwrap());
    }
}
```

### 2.5 监控集成模块

#### 2.5.1 ComprehensiveMonitoringManager

综合监控管理器，提供Prometheus集成、Grafana仪表板、实时监控等功能。

```rust
use otlp::{ComprehensiveMonitoringManager, ComprehensivePerformanceStats};

// 创建监控管理器
let monitoring_manager = ComprehensiveMonitoringManager::new();

// 初始化监控系统
monitoring_manager.initialize().await?;

// 更新性能指标
let performance_stats = ComprehensivePerformanceStats {
    // ... 性能统计数据
};
monitoring_manager.update_performance_metrics(performance_stats).await?;

// 获取Prometheus格式指标
let prometheus_metrics = monitoring_manager.get_prometheus_metrics().await;
println!("Prometheus指标:\n{}", prometheus_metrics);

// 获取活跃告警
let active_alerts = monitoring_manager.get_active_alerts().await;
for alert in active_alerts {
    println!("告警: {} - {}", alert.name, alert.message);
}
```

#### Grafana仪表板

```rust
use otlp::{GrafanaDashboardManager, Dashboard, Panel, PanelType};

let grafana_manager = GrafanaDashboardManager::new();

// 创建性能监控仪表板
let dashboard_id = grafana_manager.create_performance_dashboard().await?;
println!("创建仪表板: {}", dashboard_id);

// 创建安全监控仪表板
let security_dashboard_id = grafana_manager.create_security_dashboard().await?;
println!("创建安全仪表板: {}", security_dashboard_id);
```

### 2.6 企业级功能模块

#### 2.6.1 ComprehensiveEnterpriseManager

综合企业功能管理器，提供多租户、数据治理、合规性、高可用性等功能。

```rust
use otlp::{ComprehensiveEnterpriseManager, EnterpriseRequest, Tenant, TenantStatus};

// 创建企业功能管理器
let enterprise_manager = ComprehensiveEnterpriseManager::new();

// 初始化企业功能
enterprise_manager.initialize().await?;

// 创建租户
let tenant = Tenant {
    id: "tenant_001".to_string(),
    name: "Acme Corporation".to_string(),
    domain: "acme.com".to_string(),
    status: TenantStatus::Active,
    created_at: SystemTime::now(),
    updated_at: SystemTime::now(),
    settings: TenantSettings {
        max_data_retention: Duration::from_secs(86400 * 30), // 30天
        max_requests_per_second: 1000,
        max_storage_gb: 100,
        features: vec!["basic".to_string(), "monitoring".to_string()],
        custom_attributes: HashMap::new(),
    },
};

enterprise_manager.multi_tenant_manager.create_tenant(tenant).await?;

// 处理企业级请求
let request = EnterpriseRequest {
    id: "req_001".to_string(),
    tenant_id: "tenant_001".to_string(),
    data: "business_data".to_string(),
    data_type: "transaction".to_string(),
    user_id: Some("user_123".to_string()),
};

let response = enterprise_manager.process_enterprise_request(request).await?;
println!("企业请求处理结果: {}", response.message);
```

#### 多租户管理

```rust
use otlp::{MultiTenantManager, TenantQuota};

let multi_tenant_manager = MultiTenantManager::new();

// 检查租户配额
let quota_ok = multi_tenant_manager.check_quota("tenant_001", "requests_per_second", 1).await?;
if quota_ok {
    // 更新配额使用量
    multi_tenant_manager.update_quota_usage("tenant_001", "requests_per_second", 1).await?;
}

// 获取租户统计信息
let stats = multi_tenant_manager.get_stats();
println!("总租户数: {}", stats.total_tenants);
println!("活跃租户数: {}", stats.active_tenants);
```

#### 数据治理

```rust
use otlp::{DataGovernanceManager, DataPolicy, DataRule, DataCondition, DataAction};

let governance_manager = DataGovernanceManager::new();

// 创建数据策略
let policy = DataPolicy {
    id: "pii_policy".to_string(),
    name: "PII数据保护策略".to_string(),
    description: "保护个人身份信息".to_string(),
    rules: vec![
        DataRule {
            id: "pii_encryption".to_string(),
            name: "PII加密规则".to_string(),
            condition: DataCondition::ContainsPII,
            action: DataAction::Encrypt,
            priority: 1,
        },
    ],
    is_active: true,
    created_at: SystemTime::now(),
    updated_at: SystemTime::now(),
};

governance_manager.add_policy(policy).await?;

// 评估数据策略
let data_item = DataItem {
    id: "data_001".to_string(),
    content: "user email: john@example.com".to_string(),
    data_type: "user_profile".to_string(),
    created_at: SystemTime::now(),
    classification: None,
};

let actions = governance_manager.evaluate_policies(&data_item).await?;
for action in actions {
    println!("需要执行的操作: {:?}", action);
}
```

---

## 🔍 高级功能

### 3.1 高级特性

#### 智能缓存

```rust
use otlp::{IntelligentCache, CacheConfig, EvictionPolicy};

let cache_config = CacheConfig {
    capacity: 1000,
    eviction_policy: EvictionPolicy::Lru,
    ttl: Some(Duration::from_secs(300)),
};

let cache = IntelligentCache::new(cache_config);

// 缓存数据
cache.put("key1", "value1").await?;

// 获取数据
if let Some(value) = cache.get("key1").await? {
    println!("缓存命中: {}", value);
}

// 获取缓存统计
let stats = cache.get_stats();
println!("缓存命中率: {:.2}%", stats.hit_rate * 100.0);
```

#### 自适应采样

```rust
use otlp::{AdaptiveSampler, SamplingConfig, SamplingContext};

let sampling_config = SamplingConfig {
    initial_rate: 0.1, // 10%初始采样率
    adjustment_factor: 0.05, // 5%调整因子
    min_rate: 0.01, // 最小1%采样率
    max_rate: 1.0, // 最大100%采样率
    adjustment_interval: Duration::from_secs(60),
};

let sampler = AdaptiveSampler::new(sampling_config);

// 决定是否采样
let context = SamplingContext {
    service_name: "user_service".to_string(),
    operation_name: "login".to_string(),
    current_load: 0.8, // 80%负载
    error_rate: 0.02, // 2%错误率
    latency_p99: 100.0, // 99分位延迟100ms
    attributes: HashMap::new(),
};

let should_sample = sampler.should_sample(&context).await?;
if should_sample {
    println!("应该采样此请求");
}
```

#### AI异常检测

```rust
use otlp::{AIAnomalyDetector, AnomalyConfig, TrainingDataPoint, ModelType};

let anomaly_config = AnomalyConfig {
    training_interval: Duration::from_secs(300), // 5分钟训练间隔
    min_training_samples: 100,
    anomaly_threshold: 0.7, // 0.7以上为异常
    model_types: vec![ModelType::Statistical, ModelType::TimeSeries],
};

let detector = AIAnomalyDetector::new(anomaly_config);

// 训练模型
let training_data = vec![
    TrainingDataPoint {
        timestamp: SystemTime::now(),
        features: vec![1.0, 2.0, 3.0],
        label: Some(false), // 正常数据
        metadata: HashMap::new(),
    },
    // ... 更多训练数据
];

detector.train_model("service_metrics", training_data).await?;

// 检测异常
let test_features = vec![10.0, 20.0, 30.0]; // 异常特征
let anomaly_result = detector.detect_anomaly("service_metrics", test_features).await?;

if anomaly_result.is_anomaly {
    println!("检测到异常! 异常分数: {:.2}", anomaly_result.anomaly_score);
}
```

### 3.2 错误处理

#### 3.2.1 错误类型

```rust
use otlp::{OtlpError, ErrorCategory, ErrorSeverity};

// 处理OTLP错误
match result {
    Ok(data) => {
        // 处理成功结果
        println!("操作成功: {:?}", data);
    },
    Err(OtlpError::NetworkError { message, .. }) => {
        // 处理网络错误
        eprintln!("网络错误: {}", message);
    },
    Err(OtlpError::ValidationError { message, .. }) => {
        // 处理验证错误
        eprintln!("验证错误: {}", message);
    },
    Err(OtlpError::ConfigurationError { message, .. }) => {
        // 处理配置错误
        eprintln!("配置错误: {}", message);
    },
    Err(e) => {
        // 处理其他错误
        eprintln!("未知错误: {}", e);
    }
}
```

#### 错误上下文

```rust
use otlp::{ErrorContext, ErrorSeverity};

let error_context = ErrorContext {
    operation: "send_trace".to_string(),
    component: "otlp_client".to_string(),
    severity: ErrorSeverity::Error,
    timestamp: SystemTime::now(),
    additional_info: HashMap::new(),
};

let error = OtlpError::NetworkError {
    message: "Connection timeout".to_string(),
    context: Some(error_context),
};
```

---

## 🔧 性能优化

### 4.1 内存优化

```rust
// 使用内存池减少分配
let pool = HighPerformanceMemoryPool::<TelemetryData>::new(1000, 10);

// 批量处理数据
let batch_size = 100;
for chunk in data.chunks(batch_size) {
    let optimized_chunk = optimizer.optimize_processing(chunk.to_vec()).await?;
    // 处理优化后的数据
}
```

### 4.2 并发优化

```rust
// 使用并发优化器
let concurrency_optimizer = ConcurrencyOptimizer::new(10); // 最大10个并发任务

// 并发处理多个任务
let tasks = vec![
    || async { process_data_1().await },
    || async { process_data_2().await },
    || async { process_data_3().await },
];

let handles = concurrency_optimizer.submit_batch(tasks).await?;
for handle in handles {
    let result = handle.await?;
    // 处理结果
}
```

### 4.3 缓存优化

```rust
// 配置智能缓存
let cache_config = CacheConfig {
    capacity: 10000,
    eviction_policy: EvictionPolicy::Lfu, // 最少使用频率
    ttl: Some(Duration::from_secs(600)), // 10分钟TTL
};

let cache = IntelligentCache::new(cache_config);

// 使用缓存减少重复计算
if let Some(cached_result) = cache.get(&cache_key).await? {
    return Ok(cached_result);
}

let result = expensive_computation().await?;
cache.put(cache_key, result.clone()).await?;
Ok(result)
```

---

## 📊 安全最佳实践

### 5.1 数据加密

```rust
// 使用强加密算法
let encryption_manager = EncryptionManager::new();

// 加密敏感数据
let sensitive_data = b"credit_card_number";
let encrypted = encryption_manager.encrypt(sensitive_data, "aes256gcm").await?;

// 安全存储加密数据
store_encrypted_data(&encrypted).await?;
```

### 5.2 访问控制

```rust
// 实施基于角色的访问控制
let auth_manager = AuthenticationManager::new();

// 检查用户权限
let has_permission = auth_manager.check_permission(
    &user_id,
    "sensitive_data",
    "read"
).await?;

if !has_permission {
    return Err(OtlpError::AuthorizationError {
        message: "Insufficient permissions".to_string(),
        context: None,
    });
}
```

### 5.3 审计日志

```rust
// 记录所有敏感操作
let audit_logger = AuditLogger::new(10000);

let audit_log = AuditLog {
    id: generate_audit_id(),
    timestamp: SystemTime::now(),
    user_id: Some(user_id.clone()),
    action: "data_access".to_string(),
    resource: "user_profile".to_string(),
    result: AuditResult::Success,
    details: HashMap::new(),
    ip_address: Some(request_ip),
    user_agent: Some(user_agent),
};

audit_logger.log(audit_log).await?;
```

---

## 🚀 部署和运维

### 6.1 配置管理

```rust
// 环境特定配置
let config = match env::var("ENVIRONMENT") {
    Ok(env) if env == "production" => {
        OtlpConfigBuilder::new()
            .with_endpoint("https://otlp.production.com")
            .with_batch_config(BatchConfig {
                max_export_batch_size: 1024,
                export_timeout: Duration::from_secs(60),
                max_queue_size: 4096,
            })
            .build()
    },
    _ => {
        OtlpConfigBuilder::new()
            .with_endpoint("http://localhost:4317")
            .with_batch_config(BatchConfig::default())
            .build()
    }
};
```

### 6.2 健康检查

```rust
// 实现健康检查端点
async fn health_check() -> Result<HealthStatus> {
    let client = get_otlp_client().await?;

    // 检查客户端连接
    let is_healthy = client.is_healthy().await?;

    Ok(HealthStatus {
        status: if is_healthy { "healthy" } else { "unhealthy" },
        timestamp: SystemTime::now(),
        details: HashMap::new(),
    })
}
```

### 6.3 监控和告警

```rust
// 设置监控和告警
let monitoring_manager = ComprehensiveMonitoringManager::new();
monitoring_manager.initialize().await?;

// 添加告警规则
let alert_rule = AlertRule {
    id: "high_error_rate".to_string(),
    name: "高错误率告警".to_string(),
    condition: AlertCondition::GreaterThan {
        metric: "error_rate".to_string(),
        threshold: 0.05, // 5%错误率阈值
    },
    severity: AlertSeverity::Warning,
    duration: Duration::from_secs(300), // 5分钟持续时间
    is_enabled: true,
};

monitoring_manager.get_alert_manager().add_rule(alert_rule).await?;
```

---

## 🔬 示例项目

### 7.1 完整的微服务示例

```rust
use otlp::{
    OtlpClient, OtlpClientBuilder, OtlpConfig,
    ComprehensivePerformanceOptimizer,
    ComprehensiveSecurityManager,
    ComprehensiveMonitoringManager,
    ComprehensiveEnterpriseManager,
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化所有组件
    let client = OtlpClientBuilder::new()
        .with_endpoint("http://localhost:4317")
        .with_config(OtlpConfig::default())
        .build()
        .await?;

    let performance_optimizer = ComprehensivePerformanceOptimizer::new();
    let security_manager = ComprehensiveSecurityManager::new();
    let monitoring_manager = ComprehensiveMonitoringManager::new();
    let enterprise_manager = ComprehensiveEnterpriseManager::new();

    // 初始化企业功能
    enterprise_manager.initialize().await?;
    monitoring_manager.initialize().await?;

    // 处理业务请求
    loop {
        let request = receive_request().await?;

        // 安全检查
        let secure_request = SecureRequest {
            token: request.token,
            resource: "business_data".to_string(),
            action: "process".to_string(),
            data: request.data,
            encrypt: true,
            ip_address: request.ip_address,
            user_agent: request.user_agent,
        };

        let security_response = security_manager.process_secure_request(secure_request).await?;

        if !security_response.success {
            send_error_response("Security check failed").await?;
            continue;
        }

        // 性能优化处理
        let telemetry_data = vec![create_telemetry_data(&request)?];
        let optimized_data = performance_optimizer.optimize_processing(telemetry_data).await?;

        // 发送遥测数据
        for data in optimized_data {
            client.send_telemetry_data(data).await?;
        }

        // 更新监控指标
        let stats = performance_optimizer.get_comprehensive_stats();
        monitoring_manager.update_performance_metrics(stats).await?;

        send_success_response("Request processed successfully").await?;
    }
}
```

---

## 💻 相关资源

### 8.1 官方文档

- **[OTLP规范](https://opentelemetry.io/docs/specs/otlp/)** - OpenTelemetry协议规范
- **[OpenTelemetry文档](https://opentelemetry.io/docs/)** - 完整的OpenTelemetry文档
- **[Rust OpenTelemetry](https://github.com/open-telemetry/opentelemetry-rust)** - Rust实现

### 8.2 项目文档

- **[快速开始](QUICK_START_GUIDE.md)** - 5分钟快速入门
- **[用户指南](USER_GUIDE.md)** - 完整用户指南
- **[架构设计](ARCHITECTURE_DESIGN.md)** - 系统架构
- **[主索引](00_MASTER_INDEX.md)** - 文档导航

### 8.3 社区资源

- **[GitHub仓库](https://github.com/your-org/otlp-rust)** - 源代码和Issues
- **[示例项目](https://github.com/your-org/otlp-rust/tree/main/examples)** - 完整示例
- **[贡献指南](../../CONTRIBUTING.md)** - 如何贡献

---

**文档版本**: 2.1
**Rust 版本**: 1.90.0 (LLD链接器、const API)
**最后更新**: 2025年10月27日
**维护者**: OTLP Rust Team
**反馈**: [提交 Issue](https://github.com/your-org/otlp-rust/issues)

---

> **提示**: 本文档提供了完整的API参考。开发者可以根据这个文档快速上手并构建高性能、安全、可观测的OTLP应用程序。更多信息请参考 [用户指南](USER_GUIDE.md) 和 [快速开始](QUICK_START_GUIDE.md)。

**📚 感谢使用 OTLP Rust API！** 🚀
