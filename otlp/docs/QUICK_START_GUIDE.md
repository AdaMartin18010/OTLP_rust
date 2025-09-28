# OTLP Rust 快速开始指南

## 🚀 快速开始

本指南将帮助您在几分钟内开始使用OTLP Rust库。

## 📋 前置要求

- Rust 1.90 或更高版本
- 基本的Rust编程知识
- 运行中的OTLP收集器（如Jaeger、OpenTelemetry Collector等）

## 🛠️ 安装

### 1. 添加依赖

在您的 `Cargo.toml` 文件中添加OTLP依赖：

```toml
[dependencies]
otlp = "0.1.0"
tokio = { version = "1.47", features = ["full"] }
anyhow = "1.0"
```

### 2. 创建项目

```bash
cargo new my-otlp-app
cd my-otlp-app
```

## 📝 基础使用

### 1. 最简单的示例

创建一个 `src/main.rs` 文件：

```rust
use anyhow::Result;
use otlp::{OtlpClient, OtlpClientBuilder, OtlpConfig, StatusCode, AttributeValue};

#[tokio::main]
async fn main() -> Result<()> {
    // 创建OTLP客户端
    let client = OtlpClientBuilder::new()
        .with_endpoint("http://localhost:4317")
        .with_config(OtlpConfig::default())
        .build()
        .await?;

    // 发送追踪数据
    client.trace_builder()
        .with_trace_id("1234567890abcdef")
        .with_span_id("abcdef1234567890")
        .with_operation_name("hello_world")
        .with_status_code(StatusCode::Ok)
        .with_attribute("message", AttributeValue::String("Hello, OTLP!".to_string()))
        .send()
        .await?;

    println!("✅ 追踪数据发送成功！");
    Ok(())
}
```

### 2. 运行示例

```bash
cargo run
```

## 📊 发送不同类型的数据

### 1. 发送追踪数据

```rust
use otlp::{TraceBuilder, StatusCode, AttributeValue};

async fn send_trace_data(client: &OtlpClient) -> Result<()> {
    client.trace_builder()
        .with_trace_id("trace_123")
        .with_span_id("span_456")
        .with_operation_name("user_login")
        .with_status_code(StatusCode::Ok)
        .with_attribute("user.id", AttributeValue::String("user123".to_string()))
        .with_attribute("request.duration", AttributeValue::Int64(150))
        .send()
        .await?;
    
    Ok(())
}
```

### 2. 发送指标数据

```rust
use otlp::{MetricBuilder, AttributeValue};

async fn send_metric_data(client: &OtlpClient) -> Result<()> {
    client.metric_builder()
        .with_name("request_count")
        .with_description("Total number of requests")
        .with_value(AttributeValue::Int64(1000))
        .with_attribute("service", AttributeValue::String("my_service".to_string()))
        .send()
        .await?;
    
    Ok(())
}
```

### 3. 发送日志数据

```rust
use otlp::{LogBuilder, AttributeValue};

async fn send_log_data(client: &OtlpClient) -> Result<()> {
    client.log_builder()
        .with_message("User login successful")
        .with_level("INFO")
        .with_attribute("user.id", AttributeValue::String("user123".to_string()))
        .with_attribute("ip_address", AttributeValue::String("192.168.1.100".to_string()))
        .send()
        .await?;
    
    Ok(())
}
```

## ⚙️ 配置选项

### 1. 基本配置

```rust
use otlp::{OtlpConfig, OtlpConfigBuilder, TransportProtocol, Compression};

let config = OtlpConfigBuilder::new()
    .with_endpoint("http://localhost:4317")
    .with_transport_protocol(TransportProtocol::Grpc)
    .with_compression(Compression::Gzip)
    .build();
```

### 2. 批量配置

```rust
use otlp::{BatchConfig, Duration};

let batch_config = BatchConfig {
    max_export_batch_size: 512,
    export_timeout: Duration::from_secs(30),
    max_queue_size: 2048,
};

let config = OtlpConfigBuilder::new()
    .with_batch_config(batch_config)
    .build();
```

## 🚀 高级功能

### 1. 性能优化

```rust
use otlp::{ComprehensivePerformanceOptimizer, TelemetryData};

async fn use_performance_optimizer() -> Result<()> {
    let optimizer = ComprehensivePerformanceOptimizer::new();
    
    // 创建测试数据
    let test_data = vec![TelemetryData::default(); 1000];
    
    // 优化处理
    let optimized_data = optimizer.optimize_processing(test_data).await?;
    
    println!("优化处理了 {} 条数据", optimized_data.len());
    Ok(())
}
```

### 2. 安全增强

```rust
use otlp::{ComprehensiveSecurityManager, SecureRequest};

async fn use_security_manager() -> Result<()> {
    let security_manager = ComprehensiveSecurityManager::new();
    
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
        println!("安全请求处理成功");
    } else {
        println!("安全请求被拒绝: {}", response.message);
    }
    
    Ok(())
}
```

### 3. 监控集成

```rust
use otlp::ComprehensiveMonitoringManager;

async fn use_monitoring_manager() -> Result<()> {
    let monitoring_manager = ComprehensiveMonitoringManager::new();
    
    // 初始化监控系统
    monitoring_manager.initialize().await?;
    
    // 获取Prometheus指标
    let metrics = monitoring_manager.get_prometheus_metrics().await;
    println!("Prometheus指标:\n{}", metrics);
    
    Ok(())
}
```

## 🏢 企业级功能

### 1. 多租户支持

```rust
use otlp::{ComprehensiveEnterpriseManager, Tenant, TenantStatus, TenantSettings};
use std::time::Duration;
use std::collections::HashMap;

async fn use_enterprise_manager() -> Result<()> {
    let enterprise_manager = ComprehensiveEnterpriseManager::new();
    enterprise_manager.initialize().await?;
    
    // 创建租户
    let tenant = Tenant {
        id: "tenant_001".to_string(),
        name: "My Company".to_string(),
        domain: "mycompany.com".to_string(),
        status: TenantStatus::Active,
        created_at: std::time::SystemTime::now(),
        updated_at: std::time::SystemTime::now(),
        settings: TenantSettings {
            max_data_retention: Duration::from_secs(86400 * 30), // 30天
            max_requests_per_second: 1000,
            max_storage_gb: 100,
            features: vec!["basic".to_string(), "monitoring".to_string()],
            custom_attributes: HashMap::new(),
        },
    };
    
    enterprise_manager.multi_tenant_manager.create_tenant(tenant).await?;
    println!("租户创建成功");
    
    Ok(())
}
```

## 🔧 错误处理

### 1. 基本错误处理

```rust
use otlp::OtlpError;

async fn handle_errors() -> Result<()> {
    match client.trace_builder().send().await {
        Ok(_) => println!("数据发送成功"),
        Err(OtlpError::NetworkError { message, .. }) => {
            eprintln!("网络错误: {}", message);
        },
        Err(OtlpError::ValidationError { message, .. }) => {
            eprintln!("验证错误: {}", message);
        },
        Err(e) => {
            eprintln!("其他错误: {}", e);
        }
    }
    
    Ok(())
}
```

### 2. 重试机制

```rust
use tokio::time::{sleep, Duration};

async fn send_with_retry(client: &OtlpClient, max_retries: u32) -> Result<()> {
    for attempt in 0..max_retries {
        match client.trace_builder().send().await {
            Ok(_) => return Ok(()),
            Err(e) if attempt < max_retries - 1 => {
                println!("发送失败，第 {} 次重试: {}", attempt + 1, e);
                sleep(Duration::from_secs(2_u64.pow(attempt))).await; // 指数退避
            },
            Err(e) => return Err(e.into()),
        }
    }
    
    Ok(())
}
```

## 📊 性能优化建议

### 1. 批量发送

```rust
async fn batch_send_data(client: &OtlpClient) -> Result<()> {
    let mut batch = Vec::new();
    
    // 收集数据
    for i in 0..100 {
        let trace_data = create_trace_data(i);
        batch.push(trace_data);
    }
    
    // 批量发送
    for data in batch {
        client.trace_builder()
            .with_trace_id(&data.trace_id)
            .with_span_id(&data.span_id)
            .with_operation_name(&data.operation_name)
            .send()
            .await?;
    }
    
    Ok(())
}
```

### 2. 异步处理

```rust
use tokio::task;

async fn async_send_data(client: &OtlpClient) -> Result<()> {
    let client = Arc::new(client);
    let mut handles = Vec::new();
    
    // 创建多个异步任务
    for i in 0..10 {
        let client_clone = client.clone();
        let handle = task::spawn(async move {
            client_clone.trace_builder()
                .with_trace_id(&format!("trace_{}", i))
                .with_span_id(&format!("span_{}", i))
                .with_operation_name("async_operation")
                .send()
                .await
        });
        handles.push(handle);
    }
    
    // 等待所有任务完成
    for handle in handles {
        handle.await??;
    }
    
    Ok(())
}
```

## 🔒 安全最佳实践

### 1. 敏感数据加密

```rust
use otlp::{EncryptionManager, EncryptionAlgorithm};

async fn encrypt_sensitive_data() -> Result<()> {
    let encryption_manager = EncryptionManager::new();
    
    let sensitive_data = b"credit_card_number: 1234-5678-9012-3456";
    let encrypted_data = encryption_manager.encrypt(sensitive_data, "aes256gcm").await?;
    
    // 安全存储加密数据
    store_encrypted_data(&encrypted_data).await?;
    
    Ok(())
}
```

### 2. 访问控制

```rust
use otlp::{AuthenticationManager, AuthResult};

async fn authenticate_user() -> Result<()> {
    let auth_manager = AuthenticationManager::new();
    
    let login_result = auth_manager.login("username", "password").await?;
    
    if login_result.success {
        let session = login_result.session.unwrap();
        println!("登录成功，会话ID: {}", session.id);
        
        // 验证令牌
        let validation_result = auth_manager.validate_token(&session.token).await?;
        if validation_result.valid {
            println!("令牌有效");
        }
    } else {
        println!("登录失败: {}", login_result.message);
    }
    
    Ok(())
}
```

## 📈 监控和可观测性

### 1. 设置监控

```rust
use otlp::{ComprehensiveMonitoringManager, AlertRule, AlertCondition, AlertSeverity};
use std::time::Duration;

async fn setup_monitoring() -> Result<()> {
    let monitoring_manager = ComprehensiveMonitoringManager::new();
    monitoring_manager.initialize().await?;
    
    // 设置告警规则
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
    
    Ok(())
}
```

### 2. 获取指标

```rust
async fn get_metrics(monitoring_manager: &ComprehensiveMonitoringManager) -> Result<()> {
    // 获取Prometheus格式指标
    let prometheus_metrics = monitoring_manager.get_prometheus_metrics().await;
    println!("Prometheus指标:\n{}", prometheus_metrics);
    
    // 获取活跃告警
    let active_alerts = monitoring_manager.get_active_alerts().await;
    for alert in active_alerts {
        println!("活跃告警: {} - {}", alert.name, alert.message);
    }
    
    Ok(())
}
```

## 🚀 部署到生产环境

### 1. 环境配置

```rust
use std::env;

fn get_config() -> OtlpConfig {
    match env::var("ENVIRONMENT") {
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
    }
}
```

### 2. 健康检查

```rust
async fn health_check(client: &OtlpClient) -> Result<bool> {
    let is_healthy = client.is_healthy().await?;
    
    if is_healthy {
        println!("✅ 服务健康");
    } else {
        println!("❌ 服务不健康");
    }
    
    Ok(is_healthy)
}
```

### 3. 优雅关闭

```rust
use tokio::signal;

async fn graceful_shutdown() -> Result<()> {
    println!("等待关闭信号...");
    
    match signal::ctrl_c().await {
        Ok(()) => {
            println!("收到关闭信号，开始优雅关闭...");
            
            // 停止接收新请求
            println!("停止接收新请求");
            
            // 等待现有请求完成
            println!("等待现有请求完成");
            sleep(Duration::from_secs(5)).await;
            
            // 清理资源
            println!("清理资源");
            
            println!("优雅关闭完成");
        },
        Err(err) => {
            eprintln!("无法监听关闭信号: {}", err);
        }
    }
    
    Ok(())
}
```

## 📚 下一步

现在您已经掌握了OTLP Rust库的基础用法，可以：

1. **阅读完整API文档**: 查看 `API_REFERENCE.md` 了解所有可用功能
2. **运行综合示例**: 查看 `examples/comprehensive_usage_example.rs` 了解高级用法
3. **探索企业级功能**: 了解多租户、数据治理、合规性等企业级特性
4. **性能优化**: 使用性能优化器提升应用性能
5. **安全加固**: 实施安全增强功能保护敏感数据

## 🆘 获取帮助

如果您在使用过程中遇到问题：

1. **查看文档**: 阅读完整的API参考文档
2. **运行示例**: 参考提供的示例代码
3. **检查配置**: 确保OTLP收集器正在运行
4. **查看日志**: 检查错误日志获取详细信息

祝您使用愉快！🎉
