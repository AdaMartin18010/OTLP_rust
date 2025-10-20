# OTLP Rust 综合用户指南

## 📖 概述

本指南提供了OTLP Rust项目的完整使用说明，包括安装、配置、使用和最佳实践。

## 🚀 快速开始

### 安装

```bash
# 克隆项目
git clone https://github.com/your-org/otlp-rust.git
cd otlp-rust

# 构建项目
cargo build --release

# 运行测试
cargo test

# 运行基准测试
cargo bench
```

### 基本使用

```rust
use otlp::{OtlpClient, TelemetryData, TelemetryDataType};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建OTLP客户端
    let client = OtlpClient::new()
        .with_endpoint("http://localhost:4317")
        .build()?;
    
    // 创建遥测数据
    let data = TelemetryData {
        data_type: TelemetryDataType::Trace,
        timestamp: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)?
            .as_secs(),
        resource_attributes: std::collections::HashMap::new(),
        scope_attributes: std::collections::HashMap::new(),
        content: otlp::TelemetryContent::Trace(otlp::TraceData {
            name: "example_span".to_string(),
            span_kind: "internal".to_string(),
            status: "ok".to_string(),
            events: Vec::new(),
            links: Vec::new(),
        }),
    };
    
    // 发送数据
    client.send_telemetry_data(data).await?;
    
    Ok(())
}
```

## 🔧 配置

### 基本配置

```rust
use otlp::{OtlpConfig, TransportProtocol, Compression};

let config = OtlpConfig::new()
    .with_endpoint("http://localhost:4317")
    .with_transport_protocol(TransportProtocol::Grpc)
    .with_compression(Compression::Gzip)
    .with_batch_size(512)
    .with_export_timeout(std::time::Duration::from_secs(30))
    .build()?;
```

### 高级配置

```rust
use otlp::{OtlpConfig, BatchConfig};

let config = OtlpConfig::new()
    .with_endpoint("http://localhost:4317")
    .with_batch_config(BatchConfig {
        max_export_batch_size: 512,
        export_timeout: std::time::Duration::from_secs(30),
        max_queue_size: 2048,
        scheduled_delay: std::time::Duration::from_secs(5),
    })
    .with_retry_config(RetryConfig {
        max_retries: 3,
        initial_retry_delay: std::time::Duration::from_millis(100),
        max_retry_delay: std::time::Duration::from_secs(30),
        exponential_backoff: true,
    })
    .build()?;
```

## 📊 数据收集

### 追踪数据

```rust
use otlp::{TraceData, SpanKind, SpanStatus};

let trace_data = TraceData {
    name: "user_operation".to_string(),
    span_kind: SpanKind::Internal.to_string(),
    status: SpanStatus::Ok.to_string(),
    events: vec![
        otlp::SpanEvent {
            name: "user_clicked".to_string(),
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)?
                .as_secs(),
            attributes: std::collections::HashMap::new(),
        }
    ],
    links: Vec::new(),
};
```

### 指标数据

```rust
use otlp::{MetricData, MetricType, DataPoint};

let metric_data = MetricData {
    name: "request_count".to_string(),
    description: "Total number of requests".to_string(),
    unit: "count".to_string(),
    metric_type: MetricType::Counter,
    data_points: vec![
        DataPoint {
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)?
                .as_secs(),
            value: DataPointValue::Int64(100),
            attributes: std::collections::HashMap::new(),
        }
    ],
};
```

### 日志数据

```rust
use otlp::{LogData, LogSeverity};

let log_data = LogData {
    timestamp: std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)?
        .as_secs(),
    severity: LogSeverity::Info,
    body: "User logged in successfully".to_string(),
    attributes: std::collections::HashMap::new(),
};
```

## 🚀 高级功能

### 性能优化

```rust
use otlp::{ZeroCopyProcessor, LockFreeDataManager, CacheOptimizer};

// 零拷贝处理
let processor = ZeroCopyProcessor::new(1024, 10);
let processed_data = processor.process_zero_copy(&data).await?;

// 无锁数据管理
let manager = LockFreeDataManager::new();
manager.insert("key".to_string(), telemetry_data).await?;

// 缓存优化
let optimizer = CacheOptimizer::new(1000, 10000);
optimizer.insert("key".to_string(), telemetry_data).await?;
```

### 安全功能

```rust
use otlp::{ZeroKnowledgeProofManager, HomomorphicEncryptionManager, SecurityAuditManager};

// 零知识证明
let zk_manager = ZeroKnowledgeProofManager::new();
let proof = zk_manager.generate_proof("statement", "witness").await?;
let is_valid = zk_manager.verify_proof(&proof).await?;

// 同态加密
let he_manager = HomomorphicEncryptionManager::new();
let encrypted = he_manager.encrypt(&data, "key").await?;

// 安全审计
let audit_manager = SecurityAuditManager::new();
audit_manager.log_event(&audit_event).await?;
```

### 企业级功能

```rust
use otlp::{GDPRComplianceManager, MultiTenantManager, DataGovernanceManager};

// GDPR合规性
let gdpr_manager = GDPRComplianceManager::new();
let subject = DataSubject {
    id: "user1".to_string(),
    name: "John Doe".to_string(),
    email: "john@example.com".to_string(),
    consent_given: true,
    consent_timestamp: std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)?
        .as_secs(),
};
gdpr_manager.register_data_subject(subject).await?;

// 多租户管理
let tenant_manager = MultiTenantManager::new();
let tenant = Tenant {
    id: "tenant1".to_string(),
    name: "Company A".to_string(),
    domain: "company-a.com".to_string(),
    status: TenantStatus::Active,
    created_at: std::time::SystemTime::now(),
    updated_at: std::time::SystemTime::now(),
    settings: TenantSettings {
        max_data_retention: std::time::Duration::from_secs(86400),
        max_requests_per_second: 100,
        max_storage_gb: 10,
        features: vec!["basic".to_string()],
        custom_attributes: std::collections::HashMap::new(),
    },
};
tenant_manager.create_tenant(tenant).await?;
```

## 🔍 监控和可观测性

### 性能监控

```rust
use otlp::{ComprehensiveMonitoringManager, PrometheusCollector};

let monitoring_manager = ComprehensiveMonitoringManager::new();
monitoring_manager.initialize().await?;

// 获取性能指标
let metrics = monitoring_manager.get_prometheus_metrics().await;
println!("Metrics: {}", metrics);

// 获取告警
let alerts = monitoring_manager.get_active_alerts().await;
for alert in alerts {
    println!("Alert: {:?}", alert);
}
```

### 健康检查

```rust
use otlp::{HealthCheck, HealthCheckType};

let health_check = HealthCheck {
    id: "service_health".to_string(),
    name: "Service Health Check".to_string(),
    check_type: HealthCheckType::Http,
    endpoint: "http://localhost:8080/health".to_string(),
    timeout: std::time::Duration::from_secs(5),
    interval: std::time::Duration::from_secs(30),
    retries: 3,
    is_enabled: true,
};

let result = health_check.execute().await?;
println!("Health check result: {:?}", result);
```

## 🛡️ 安全最佳实践

### 数据加密

```rust
use otlp::{EncryptionManager, EncryptionAlgorithm};

let encryption_manager = EncryptionManager::new();
let encrypted_data = encryption_manager.encrypt(&data, EncryptionAlgorithm::Aes256Gcm).await?;
let decrypted_data = encryption_manager.decrypt(&encrypted_data).await?;
```

### 认证和授权

```rust
use otlp::{AuthenticationManager, AuthResult};

let auth_manager = AuthenticationManager::new();
let auth_result = auth_manager.login("username", "password").await?;

if auth_result.is_success {
    println!("Authentication successful");
    println!("User ID: {:?}", auth_result.user_id);
    println!("Roles: {:?}", auth_result.roles);
}
```

### 审计日志

```rust
use otlp::{AuditLogger, AuditLog};

let audit_logger = AuditLogger::new();
let audit_log = AuditLog {
    event_type: "user_login".to_string(),
    user_id: "user1".to_string(),
    resource: "api".to_string(),
    action: "login".to_string(),
    result: "success".to_string(),
    timestamp: std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)?
        .as_secs(),
    ip_address: Some("192.168.1.100".to_string()),
    user_agent: Some("Mozilla/5.0".to_string()),
};

audit_logger.log(audit_log).await?;
```

## 📈 性能优化

### 批量处理

```rust
use otlp::{BatchProcessor, BatchConfig};

let batch_processor = BatchProcessor::new(
    100,  // 批量大小
    std::time::Duration::from_secs(5),  // 批量超时
    10    // 最大并发数
);

let data_batch = vec![telemetry_data1, telemetry_data2, telemetry_data3];
let processed_batch = batch_processor.process_batch(data_batch).await?;
```

### 缓存优化

```rust
use otlp::{IntelligentCache, CacheConfig, EvictionPolicy};

let cache_config = CacheConfig {
    max_size: 10000,
    ttl: std::time::Duration::from_secs(300),
    eviction_policy: EvictionPolicy::Lru,
};

let cache = IntelligentCache::new(cache_config);
cache.put("key", "value").await?;
let value = cache.get("key").await?;
```

### 自适应采样

```rust
use otlp::{AdaptiveSampler, SamplingConfig};

let sampling_config = SamplingConfig {
    base_rate: 0.1,
    min_rate: 0.01,
    max_rate: 1.0,
    adjustment_interval: std::time::Duration::from_secs(60),
};

let sampler = AdaptiveSampler::new(sampling_config);
let should_sample = sampler.should_sample(&sampling_context).await?;
```

## 🔧 故障排除

### 常见问题

1. **连接超时**
   ```rust
   let config = OtlpConfig::new()
       .with_endpoint("http://localhost:4317")
       .with_connect_timeout(std::time::Duration::from_secs(10))
       .build()?;
   ```

2. **内存使用过高**
   ```rust
   let config = OtlpConfig::new()
       .with_batch_config(BatchConfig {
           max_queue_size: 1024,  // 减少队列大小
           max_export_batch_size: 256,  // 减少批量大小
           ..Default::default()
       })
       .build()?;
   ```

3. **性能问题**
   ```rust
   // 启用性能优化
   let processor = ZeroCopyProcessor::new(1024, 10);
   let manager = LockFreeDataManager::new();
   let optimizer = CacheOptimizer::new(1000, 10000);
   ```

### 调试模式

```rust
use std::env;

// 启用调试日志
env::set_var("RUST_LOG", "debug");
env::set_var("RUST_BACKTRACE", "1");

// 启用详细日志
let config = OtlpConfig::new()
    .with_endpoint("http://localhost:4317")
    .with_debug(true)
    .build()?;
```

## 📚 API参考

### 主要类型

- `OtlpClient`: OTLP客户端
- `TelemetryData`: 遥测数据
- `TraceData`: 追踪数据
- `MetricData`: 指标数据
- `LogData`: 日志数据
- `OtlpConfig`: 配置
- `BatchConfig`: 批量配置

### 高级类型

- `ZeroCopyProcessor`: 零拷贝处理器
- `LockFreeDataManager`: 无锁数据管理器
- `CacheOptimizer`: 缓存优化器
- `ZeroKnowledgeProofManager`: 零知识证明管理器
- `HomomorphicEncryptionManager`: 同态加密管理器
- `GDPRComplianceManager`: GDPR合规性管理器

## 🎯 最佳实践

### 1. 数据收集
- 使用适当的采样率
- 设置合理的批量大小
- 配置适当的超时时间

### 2. 性能优化
- 启用零拷贝处理
- 使用无锁数据结构
- 配置智能缓存

### 3. 安全
- 启用数据加密
- 配置认证和授权
- 记录审计日志

### 4. 监控
- 设置性能监控
- 配置健康检查
- 设置告警规则

### 5. 合规性
- 配置GDPR合规性
- 设置数据保留策略
- 实现数据主体权利

## 🔗 相关资源

- [OpenTelemetry规范](https://opentelemetry.io/docs/)
- [Rust文档](https://doc.rust-lang.org/)
- [Tokio文档](https://tokio.rs/)
- [项目GitHub](https://github.com/your-org/otlp-rust)

## 📞 支持

如果您在使用过程中遇到问题，请：

1. 查看本指南的故障排除部分
2. 检查项目的GitHub Issues
3. 提交新的Issue
4. 联系项目维护者

---

**版本**: 1.0.0  
**最后更新**: 2025年9月18日  
**维护者**: OTLP Rust Team
