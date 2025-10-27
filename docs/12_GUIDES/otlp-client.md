# OTLP 客户端使用指南

**版本**: 1.0  
**最后更新**: 2025年10月26日  
**状态**: 🟢 活跃维护

> **简介**: OTLP Rust 客户端完整使用指南 - 从基础使用到高级功能和最佳实践。

---

## 📋 目录

- [OTLP 客户端使用指南](#otlp-客户端使用指南)
  - [📋 目录](#-目录)
  - [📖 概述](#-概述)
  - [🚀 快速开始](#-快速开始)
    - [1. 安装依赖](#1-安装依赖)
    - [2. 基础使用](#2-基础使用)
    - [3. 发送遥测数据](#3-发送遥测数据)
  - [📊 数据类型](#-数据类型)
  - [🔧 配置选项](#-配置选项)
  - [⚡ 高级功能](#-高级功能)
  - [💡 使用示例](#-使用示例)
  - [🛡️ 错误处理](#️-错误处理)
  - [📈 性能优化](#-性能优化)
  - [🔍 故障排查](#-故障排查)
  - [💡 最佳实践](#-最佳实践)
  - [📚 参考资源](#-参考资源)

---

## 📖 概述

本指南详细介绍如何使用 OTLP Rust 客户端进行遥测数据收集、处理和传输。
我们将从基础使用开始，逐步深入到高级功能和最佳实践。

## 🚀 快速开始

### 1. 安装依赖

首先确保你的项目使用 Rust 1.90+ 版本：

```bash
rustup update
rustup default 1.90
```

在你的 `Cargo.toml` 中添加依赖：

```toml
[dependencies]
otlp = { path = "../crates/otlp" }
tokio = { version = "1.48", features = ["full"] }
```

### 2. 基础使用

创建一个简单的 OTLP 客户端：

```rust
use otlp::core::EnhancedOtlpClient;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建客户端
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("my-service")
        .with_service_version("1.0.0")
        .with_http_transport()
        .build()
        .await?;
    
    // 创建追踪器
    let tracer = client.tracer("my-component");
    let span = tracer.start("my-operation");
    
    // 添加属性
    span.set_attribute("user.id", "12345");
    span.set_attribute("operation.type", "database");
    
    // 执行业务逻辑
    // ...
    
    // 结束 span
    drop(span);
    
    Ok(())
}
```

## 配置选项

### 基本配置

```rust
use otlp::{core::EnhancedOtlpClient, config::*};
use std::time::Duration;

let client = EnhancedOtlpClient::builder()
    // 端点配置
    .with_endpoint("http://localhost:4317")
    .with_service_name("my-service")
    .with_service_version("1.0.0")
    
    // 超时配置
    .with_connect_timeout(Duration::from_secs(5))
    .with_request_timeout(Duration::from_secs(30))
    
    // 传输协议
    .with_http_transport()  // 或 .with_grpc_transport()
    
    .build()
    .await?;
```

### 高级配置

```rust
use otlp::{core::EnhancedOtlpClient, config::*};

// 重试配置
let retry_config = RetryConfig {
    max_attempts: 3,
    initial_interval: Duration::from_millis(100),
    max_interval: Duration::from_secs(5),
    multiplier: 2.0,
    randomization_factor: 0.1,
    retryable_errors: vec![ErrorType::Network, ErrorType::Timeout],
};

// 批处理配置
let batch_config = BatchConfig {
    max_batch_size: 1000,
    batch_timeout: Duration::from_secs(5),
    max_queue_size: 10000,
    strategy: BatchStrategy::Hybrid,
};

let client = EnhancedOtlpClient::builder()
    .with_endpoint("http://localhost:4317")
    .with_service_name("my-service")
    .with_retry_config(retry_config)
    .with_batch_config(batch_config)
    .with_compression(Compression::Gzip)
    .with_grpc_transport()
    .build()
    .await?;
```

## 数据收集

### 追踪数据 (Traces)

追踪数据用于分布式追踪，记录请求在系统中的完整路径。

```rust
use otlp::{core::EnhancedOtlpClient, data::*};
use std::collections::HashMap;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .build()
        .await?;
    
    // 创建追踪数据
    let trace_data = TraceData {
        trace_id: "trace-123".to_string(),
        span_id: "span-456".to_string(),
        parent_span_id: None,
        name: "user-authentication".to_string(),
        span_kind: SpanKind::Server,
        start_time: 0,
        end_time: 1000000,
        status: SpanStatus {
            code: StatusCode::Ok,
            message: None,
        },
        attributes: {
            let mut attrs = HashMap::new();
            attrs.insert("user.id".to_string(), AttributeValue::String("12345".to_string()));
            attrs.insert("service.name".to_string(), AttributeValue::String("auth-service".to_string()));
            attrs
        },
        events: vec![],
        links: vec![],
    };
    
    // 导出追踪数据
    client.export_traces(vec![trace_data]).await?;
    
    Ok(())
}
```

### 指标数据 (Metrics)

指标数据用于监控系统性能和业务指标。

```rust
use otlp::{core::EnhancedOtlpClient, data::*};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .build()
        .await?;
    
    // 创建指标数据
    let metric_data = MetricData {
        name: "request_count".to_string(),
        description: "Total number of requests".to_string(),
        unit: "count".to_string(),
        metric_type: MetricType::Counter,
        data_points: vec![
            DataPoint {
                timestamp: SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos() as u64,
                value: DataPointValue::Int64(100),
                attributes: HashMap::new(),
            }
        ],
    };
    
    // 导出指标数据
    client.export_metrics(vec![metric_data]).await?;
    
    Ok(())
}
```

### 日志数据 (Logs)

日志数据用于结构化日志记录。

```rust
use otlp::{core::EnhancedOtlpClient, data::*};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .build()
        .await?;
    
    // 创建日志数据
    let log_data = LogData {
        timestamp: SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos() as u64,
        severity: LogSeverity::Info,
        body: "User login successful".to_string(),
        attributes: {
            let mut attrs = HashMap::new();
            attrs.insert("user.id".to_string(), AttributeValue::String("12345".to_string()));
            attrs.insert("ip.address".to_string(), AttributeValue::String("192.168.1.1".to_string()));
            attrs
        },
        resource: None,
    };
    
    // 导出日志数据
    client.export_logs(vec![log_data]).await?;
    
    Ok(())
}
```

## 性能优化

### 批量处理

批量处理可以显著提高性能，减少网络开销：

```rust
use otlp::{core::EnhancedOtlpClient, config::*};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 配置批量处理
    let batch_config = BatchConfig {
        max_batch_size: 1000,        // 最大批处理大小
        batch_timeout: Duration::from_secs(5),  // 批处理超时
        max_queue_size: 10000,      // 最大队列大小
        strategy: BatchStrategy::Hybrid,  // 混合策略
    };
    
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_batch_config(batch_config)
        .build()
        .await?;
    
    // 批量发送数据
    let mut traces = Vec::new();
    for i in 0..1000 {
        traces.push(create_trace_data(i));
    }
    
    client.export_traces(traces).await?;
    
    Ok(())
}
```

### 连接池优化

连接池可以复用连接，减少连接建立开销：

```rust
use otlp::core::EnhancedOtlpClient;

let client = EnhancedOtlpClient::builder()
    .with_endpoint("http://localhost:4317")
    .with_connect_timeout(Duration::from_secs(5))
    .with_request_timeout(Duration::from_secs(30))
    .build()
    .await?;
```

### 压缩优化

使用压缩可以减少网络传输开销：

```rust
use otlp::{core::EnhancedOtlpClient, config::Compression};

let client = EnhancedOtlpClient::builder()
    .with_endpoint("http://localhost:4317")
    .with_compression(Compression::Gzip)  // 使用 gzip 压缩
    .build()
    .await?;
```

## 错误处理

### 基本错误处理

```rust
use otlp::{core::EnhancedOtlpClient, error::OtlpError};

#[tokio::main]
async fn main() -> Result<(), OtlpError> {
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .build()
        .await?;
    
    match client.export_traces(vec![]).await {
        Ok(_) => println!("数据导出成功"),
        Err(e) => {
            match e {
                OtlpError::Network(err) => println!("网络错误: {}", err),
                OtlpError::Timeout(msg) => println!("超时错误: {}", msg),
                _ => println!("其他错误: {}", e),
            }
        }
    }
    
    Ok(())
}
```

### 重试机制

```rust
use otlp::{core::EnhancedOtlpClient, config::*};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 配置重试策略
    let retry_config = RetryConfig {
        max_attempts: 3,
        initial_interval: Duration::from_millis(100),
        max_interval: Duration::from_secs(5),
        multiplier: 2.0,
        randomization_factor: 0.1,
        retryable_errors: vec![ErrorType::Network, ErrorType::Timeout],
    };
    
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_retry_config(retry_config)
        .build()
        .await?;
    
    // 客户端会自动重试失败的操作
    client.export_traces(vec![]).await?;
    
    Ok(())
}
```

## 监控和统计

### 获取客户端统计信息

```rust
use otlp::core::EnhancedOtlpClient;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .build()
        .await?;
    
    // 获取统计信息
    let stats = client.stats();
    println!("发送的追踪数量: {}", stats.traces_sent);
    println!("发送的指标数量: {}", stats.metrics_sent);
    println!("发送的日志数量: {}", stats.logs_sent);
    println!("发送失败数量: {}", stats.send_failures);
    println!("平均响应时间: {:?}", stats.avg_response_time);
    println!("当前连接数: {}", stats.active_connections);
    println!("队列大小: {}", stats.queue_size);
    
    Ok(())
}
```

### 健康检查

```rust
use otlp::core::EnhancedOtlpClient;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .build()
        .await?;
    
    // 执行健康检查
    let health = client.health_check().await?;
    println!("整体健康状态: {:?}", health.status);
    
    for check in health.checks {
        println!("检查项目: {}, 状态: {:?}, 消息: {:?}", 
                check.name, check.status, check.message);
    }
    
    Ok(())
}
```

## 最佳实践

### 1. 合理设置批处理大小

```rust
// 根据网络条件和数据量调整批处理大小
let batch_config = BatchConfig {
    max_batch_size: if is_high_bandwidth { 2000 } else { 500 },
    batch_timeout: Duration::from_secs(5),
    max_queue_size: 10000,
    strategy: BatchStrategy::Hybrid,
};
```

### 2. 使用适当的压缩算法

```rust
// 根据数据特点选择压缩算法
let compression = if data_size > 1024 {
    Compression::Gzip  // 大文件使用 gzip
} else {
    Compression::None  // 小文件不使用压缩
};
```

### 3. 设置合理的超时时间

```rust
// 根据网络环境设置超时时间
let timeout = if is_local_network {
    Duration::from_secs(5)   // 本地网络
} else {
    Duration::from_secs(30)  // 远程网络
};
```

### 4. 监控客户端状态

```rust
// 定期检查客户端状态
tokio::spawn(async move {
    let mut interval = tokio::time::interval(Duration::from_secs(60));
    loop {
        interval.tick().await;
        let stats = client.stats();
        if stats.send_failures > 100 {
            eprintln!("警告: 发送失败次数过多: {}", stats.send_failures);
        }
    }
});
```

### 5. 优雅关闭

```rust
use tokio::signal;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .build()
        .await?;
    
    // 监听关闭信号
    tokio::select! {
        _ = signal::ctrl_c() => {
            println!("收到关闭信号，正在优雅关闭...");
            // 等待所有数据发送完成
            tokio::time::sleep(Duration::from_secs(2)).await;
        }
        _ = async {
            // 你的业务逻辑
            loop {
                tokio::time::sleep(Duration::from_secs(1)).await;
            }
        } => {}
    }
    
    Ok(())
}
```

## 故障排除

### 常见问题

1. **连接超时**
   - 检查网络连接
   - 增加超时时间
   - 检查防火墙设置

2. **数据发送失败**
   - 检查端点 URL
   - 验证认证信息
   - 检查数据格式

3. **性能问题**
   - 调整批处理大小
   - 启用压缩
   - 优化网络配置

### 调试技巧

```rust
// 启用详细日志
env_logger::Builder::from_default_env()
    .filter_level(log::LevelFilter::Debug)
    .init();

// 使用 tracing 进行结构化日志
use tracing::{info, error, debug};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt::init();
    
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .build()
        .await?;
    
    info!("OTLP 客户端初始化完成");
    
    match client.export_traces(vec![]).await {
        Ok(_) => info!("数据导出成功"),
        Err(e) => error!("数据导出失败: {}", e),
    }
    
    Ok(())
}
```

---

*本文档最后更新: 2025年10月20日*-
