# 可靠性框架使用指南

## 概述

可靠性框架 (`crates/reliability`) 提供了统一的错误处理、容错机制、运行时监控和环境适配功能。
本指南将详细介绍如何使用这些功能来构建高可靠性的应用程序。

## 快速开始

### 1. 安装依赖

在你的 `Cargo.toml` 中添加依赖：

```toml
[dependencies]
reliability = { path = "../crates/reliability" }
otlp = { path = "../crates/otlp" }
tokio = { version = "1.48", features = ["full"] }
```

### 2. 初始化框架

```rust
use reliability::prelude::*;

#[tokio::main]
async fn main() -> Result<(), UnifiedError> {
    // 初始化可靠性框架
    reliability::init().await?;
    
    // 你的业务逻辑
    // ...
    
    // 优雅关闭
    reliability::shutdown().await?;
    
    Ok(())
}
```

## 错误处理

### 统一错误类型

可靠性框架提供了统一的错误类型 `UnifiedError`，支持多种错误场景：

```rust
use reliability::prelude::*;

async fn example_operation() -> Result<String, UnifiedError> {
    // 系统错误
    if some_condition {
        return Err(UnifiedError::System("Something went wrong".to_string()));
    }
    
    // 网络错误
    let response = reqwest::get("https://api.example.com").await?;
    
    // 配置错误
    let config = load_config().map_err(|e| {
        UnifiedError::Configuration(format!("Failed to load config: {}", e))
    })?;
    
    // 超时错误
    let result = tokio::time::timeout(
        Duration::from_secs(5),
        async_operation()
    ).await
    .map_err(|_| UnifiedError::Timeout("Operation timed out".to_string()))?;
    
    Ok(result)
}
```

### 错误上下文

为错误添加上下文信息，便于调试和监控：

```rust
use reliability::prelude::*;
use std::collections::HashMap;

async fn operation_with_context() -> Result<(), UnifiedError> {
    let context = ErrorContext {
        error_id: "OP-001".to_string(),
        timestamp: SystemTime::now(),
        source: "user-service".to_string(),
        severity: ErrorSeverity::Medium,
        tags: {
            let mut tags = HashMap::new();
            tags.insert("operation".to_string(), "user_login".to_string());
            tags.insert("version".to_string(), "1.0.0".to_string());
            tags
        },
        stack_trace: None,
        metrics: HashMap::new(),
    };
    
    match risky_operation().await {
        Ok(result) => Ok(result),
        Err(error) => {
            // 记录错误上下文
            GlobalErrorMonitor::record_error(error, context).await?;
            Err(error)
        }
    }
}
```

### 错误监控

使用全局错误监控器跟踪和分析错误：

```rust
use reliability::prelude::*;

#[tokio::main]
async fn main() -> Result<(), UnifiedError> {
    // 初始化错误监控
    GlobalErrorMonitor::init().await?;
    
    // 执行业务操作
    for i in 0..100 {
        match operation().await {
            Ok(_) => println!("操作 {} 成功", i),
            Err(e) => {
                let context = ErrorContext {
                    error_id: format!("OP-{}", i),
                    timestamp: SystemTime::now(),
                    source: "main".to_string(),
                    severity: ErrorSeverity::Low,
                    tags: HashMap::new(),
                    stack_trace: None,
                    metrics: HashMap::new(),
                };
                
                GlobalErrorMonitor::record_error(e, context).await?;
            }
        }
    }
    
    // 获取错误统计
    let stats = GlobalErrorMonitor::get_error_stats();
    println!("错误统计: {:?}", stats);
    
    Ok(())
}
```

## 容错机制

### 断路器模式

断路器模式可以防止级联故障：

```rust
use reliability::prelude::*;

#[tokio::main]
async fn main() -> Result<(), UnifiedError> {
    // 创建断路器：失败阈值 5，恢复超时 60 秒
    let circuit_breaker = CircuitBreaker::new(5, Duration::from_secs(60));
    
    // 使用断路器执行操作
    let result = circuit_breaker.execute(|| async {
        // 可能失败的操作
        external_api_call().await
    }).await?;
    
    println!("操作结果: {}", result);
    Ok(())
}

async fn external_api_call() -> Result<String, UnifiedError> {
    // 模拟外部 API 调用
    tokio::time::sleep(Duration::from_millis(100)).await;
    
    // 随机失败
    if rand::random::<f64>() < 0.3 {
        Err(UnifiedError::System("API call failed".to_string()))
    } else {
        Ok("API response".to_string())
    }
}
```

### 重试策略

使用重试策略处理临时性故障：

```rust
use reliability::prelude::*;

#[tokio::main]
async fn main() -> Result<(), UnifiedError> {
    // 创建指数退避重试策略
    let retry_policy = RetryPolicy::exponential_backoff(
        3,                                    // 最大重试次数
        Duration::from_millis(100),          // 初始延迟
        Duration::from_secs(5),              // 最大延迟
        2.0,                                  // 乘数
    );
    
    // 使用重试策略执行操作
    let result = retry_policy.execute(|| async {
        unreliable_operation().await
    }).await?;
    
    println!("最终结果: {}", result);
    Ok(())
}

async fn unreliable_operation() -> Result<String, UnifiedError> {
    // 模拟不可靠的操作
    tokio::time::sleep(Duration::from_millis(50)).await;
    
    if rand::random::<f64>() < 0.7 {
        Err(UnifiedError::System("Temporary failure".to_string()))
    } else {
        Ok("Success".to_string())
    }
}
```

### 超时控制

使用超时控制防止操作无限等待：

```rust
use reliability::prelude::*;

#[tokio::main]
async fn main() -> Result<(), UnifiedError> {
    // 创建超时控制器
    let timeout = Timeout::new(
        Duration::from_secs(30),
        TimeoutStrategy::FailFast
    );
    
    // 使用超时控制执行操作
    let result = timeout.execute(|| async {
        slow_operation().await
    }).await?;
    
    println!("操作结果: {}", result);
    Ok(())
}

async fn slow_operation() -> String {
    // 模拟慢操作
    tokio::time::sleep(Duration::from_secs(rand::random::<u64>() % 60)).await;
    "Operation completed".to_string()
}
```

### 舱壁模式

使用舱壁模式隔离资源，防止故障传播：

```rust
use reliability::prelude::*;

#[tokio::main]
async fn main() -> Result<(), UnifiedError> {
    // 创建舱壁：最大并发数 10
    let bulkhead = Bulkhead::new(10);
    
    // 并发执行多个操作
    let mut handles = Vec::new();
    for i in 0..20 {
        let bulkhead = bulkhead.clone();
        let handle = tokio::spawn(async move {
            bulkhead.execute(|| async {
                println!("执行操作 {}", i);
                tokio::time::sleep(Duration::from_secs(1)).await;
                format!("操作 {} 完成", i)
            }).await
        });
        handles.push(handle);
    }
    
    // 等待所有操作完成
    for handle in handles {
        let result = handle.await??;
        println!("{}", result);
    }
    
    Ok(())
}
```

## 运行时监控

### 健康检查

实现系统健康检查：

```rust
use reliability::prelude::*;

// 自定义健康检查
struct DatabaseHealthCheck {
    connection_string: String,
}

impl HealthCheckTrait for DatabaseHealthCheck {
    async fn check(&self) -> HealthCheckResult {
        let start = Instant::now();
        
        // 检查数据库连接
        match check_database_connection(&self.connection_string).await {
            Ok(_) => HealthCheckResult {
                status: HealthStatus::Healthy,
                message: Some("Database connection OK".to_string()),
                duration: start.elapsed(),
                details: HashMap::new(),
            },
            Err(e) => HealthCheckResult {
                status: HealthStatus::Unhealthy,
                message: Some(format!("Database connection failed: {}", e)),
                duration: start.elapsed(),
                details: HashMap::new(),
            },
        }
    }
    
    fn name(&self) -> &str {
        "database"
    }
}

#[tokio::main]
async fn main() -> Result<(), UnifiedError> {
    // 创建健康检查配置
    let config = HealthCheckConfig {
        check_interval: Duration::from_secs(30),
        timeout: Duration::from_secs(5),
        failure_threshold: 3,
    };
    
    // 创建健康检查器
    let mut health_checker = HealthChecker::new(config);
    
    // 注册健康检查
    health_checker.register_checker(
        "database".to_string(),
        Box::new(DatabaseHealthCheck {
            connection_string: "postgresql://localhost/mydb".to_string(),
        }),
    );
    
    // 执行健康检查
    let results = health_checker.check_all().await;
    
    for (name, result) in results {
        println!("{}: {:?} - {}", name, result.status, 
                result.message.unwrap_or_default());
    }
    
    Ok(())
}
```

### 性能监控

实现性能指标监控：

```rust
use reliability::prelude::*;

// 自定义指标收集器
struct RequestMetricsCollector {
    request_count: AtomicU64,
    response_time_sum: AtomicU64,
}

impl MetricCollector for RequestMetricsCollector {
    async fn collect(&self) -> Vec<Metric> {
        let count = self.request_count.load(Ordering::Relaxed);
        let sum = self.response_time_sum.load(Ordering::Relaxed);
        let avg = if count > 0 { sum as f64 / count as f64 } else { 0.0 };
        
        vec![
            Metric {
                name: "request_count".to_string(),
                value: count as f64,
                labels: HashMap::new(),
                timestamp: SystemTime::now(),
            },
            Metric {
                name: "avg_response_time".to_string(),
                value: avg,
                labels: HashMap::new(),
                timestamp: SystemTime::now(),
            },
        ]
    }
    
    fn name(&self) -> &str {
        "request_metrics"
    }
}

#[tokio::main]
async fn main() -> Result<(), UnifiedError> {
    // 创建监控配置
    let config = MonitoringConfig {
        collection_interval: Duration::from_secs(10),
        retention_period: Duration::from_secs(3600),
        alert_thresholds: {
            let mut thresholds = HashMap::new();
            thresholds.insert("avg_response_time".to_string(), 1000.0);
            thresholds
        },
    };
    
    // 创建性能监控器
    let mut monitor = PerformanceMonitor::new(config);
    
    // 注册指标收集器
    let collector = Arc::new(RequestMetricsCollector {
        request_count: AtomicU64::new(0),
        response_time_sum: AtomicU64::new(0),
    });
    
    monitor.register_collector(
        "request_metrics".to_string(),
        Box::new(collector.clone()),
    );
    
    // 模拟请求处理
    for i in 0..100 {
        let start = Instant::now();
        
        // 处理请求
        tokio::time::sleep(Duration::from_millis(rand::random::<u64>() % 100)).await;
        
        let duration = start.elapsed();
        collector.request_count.fetch_add(1, Ordering::Relaxed);
        collector.response_time_sum.fetch_add(
            duration.as_millis() as u64, 
            Ordering::Relaxed
        );
    }
    
    // 收集指标
    let metrics = monitor.collect_all().await;
    for (name, metric_list) in metrics {
        println!("{}: {:?}", name, metric_list);
    }
    
    Ok(())
}
```

### 资源监控

监控系统资源使用情况：

```rust
use reliability::prelude::*;

#[tokio::main]
async fn main() -> Result<(), UnifiedError> {
    // 创建资源监控配置
    let config = ResourceMonitoringConfig {
        monitoring_interval: Duration::from_secs(5),
        history_size: 100,
        alert_thresholds: ResourceThresholds {
            cpu_threshold: 80.0,
            memory_threshold: 85.0,
            disk_threshold: 90.0,
            network_threshold: 70.0,
        },
    };
    
    // 创建资源监控器
    let mut monitor = ResourceMonitor::new(config);
    
    // 开始监控
    monitor.start_monitoring().await;
    
    // 模拟高负载
    for i in 0..10 {
        tokio::spawn(async move {
            loop {
                // 模拟 CPU 密集型任务
                let _ = (0..1000000).sum::<i64>();
                tokio::time::sleep(Duration::from_millis(1)).await;
            }
        });
    }
    
    // 监控一段时间
    tokio::time::sleep(Duration::from_secs(30)).await;
    
    // 检查告警
    let alerts = monitor.check_alerts();
    for alert in alerts {
        println!("资源告警: {:?}", alert);
    }
    
    // 获取资源使用历史
    let history = monitor.get_usage_history();
    for usage in history.iter().rev().take(5) {
        println!("CPU: {:.1}%, Memory: {:.1}%", 
                usage.cpu_usage, usage.memory_usage);
    }
    
    Ok(())
}
```

## 环境适配

### 自动环境检测

```rust
use reliability::prelude::*;

#[tokio::main]
async fn main() -> Result<(), UnifiedError> {
    // 创建环境管理器
    let mut env_manager = RuntimeEnvironmentManager::new();
    
    // 自动检测环境
    let environment = env_manager.auto_detect().await;
    println!("检测到环境: {:?}", environment);
    
    // 获取环境信息
    let info = env_manager.get_environment_info().await;
    println!("环境信息: {:?}", info);
    
    // 获取环境能力
    let capabilities = env_manager.get_environment_capabilities();
    println!("环境能力: {:?}", capabilities);
    
    // 根据环境调整配置
    match environment {
        RuntimeEnvironment::Container => {
            println!("在容器环境中运行，启用容器优化");
            // 容器特定配置
        },
        RuntimeEnvironment::Kubernetes => {
            println!("在 Kubernetes 环境中运行，启用 K8s 集成");
            // Kubernetes 特定配置
        },
        RuntimeEnvironment::Edge => {
            println!("在边缘环境中运行，启用边缘优化");
            // 边缘计算特定配置
        },
        _ => {
            println!("在标准环境中运行");
            // 标准配置
        }
    }
    
    Ok(())
}
```

## 混沌工程

### 故障注入

使用故障注入测试系统韧性：

```rust
use reliability::prelude::*;

#[tokio::main]
async fn main() -> Result<(), UnifiedError> {
    // 创建故障配置
    let config = FaultConfig {
        fault_type: FaultType::NetworkLatency(Duration::from_millis(100)),
        probability: 0.1,  // 10% 概率
        duration: Duration::from_secs(60),
        scope: FaultScope::Global,
    };
    
    // 创建故障注入器
    let mut fault_injector = FaultInjector::new(config);
    
    // 注入故障
    let result = fault_injector.inject_fault().await?;
    println!("故障注入结果: {:?}", result);
    
    // 在故障期间执行业务逻辑
    for i in 0..100 {
        match business_operation().await {
            Ok(_) => println!("操作 {} 成功", i),
            Err(e) => println!("操作 {} 失败: {}", i, e),
        }
        tokio::time::sleep(Duration::from_millis(100)).await;
    }
    
    // 停止故障注入
    fault_injector.stop_fault_injection().await;
    
    // 分析故障影响
    let analysis = fault_injector.analyze_fault_impact().await;
    println!("故障影响分析: {:?}", analysis);
    
    Ok(())
}

async fn business_operation() -> Result<String, UnifiedError> {
    // 模拟业务操作
    tokio::time::sleep(Duration::from_millis(50)).await;
    
    if rand::random::<f64>() < 0.05 {
        Err(UnifiedError::System("Business operation failed".to_string()))
    } else {
        Ok("Business operation succeeded".to_string())
    }
}
```

## 最佳实践

### 1. 组合使用容错机制

```rust
use reliability::prelude::*;

async fn robust_operation() -> Result<String, UnifiedError> {
    // 创建容错组件
    let circuit_breaker = CircuitBreaker::new(5, Duration::from_secs(60));
    let retry_policy = RetryPolicy::exponential_backoff(3, Duration::from_millis(100), Duration::from_secs(5), 2.0);
    let timeout = Timeout::new(Duration::from_secs(30), TimeoutStrategy::FailFast);
    
    // 组合使用
    circuit_breaker.execute(|| async {
        timeout.execute(|| async {
            retry_policy.execute(|| async {
                external_service_call().await
            }).await
        }).await
    }).await
}
```

### 2. 监控和告警

```rust
use reliability::prelude::*;

#[tokio::main]
async fn main() -> Result<(), UnifiedError> {
    // 初始化监控
    let mut health_checker = HealthChecker::new(HealthCheckConfig {
        check_interval: Duration::from_secs(30),
        timeout: Duration::from_secs(5),
        failure_threshold: 3,
    });
    
    let mut performance_monitor = PerformanceMonitor::new(MonitoringConfig {
        collection_interval: Duration::from_secs(10),
        retention_period: Duration::from_secs(3600),
        alert_thresholds: HashMap::new(),
    });
    
    // 启动监控任务
    tokio::spawn(async move {
        let mut interval = tokio::time::interval(Duration::from_secs(30));
        loop {
            interval.tick().await;
            
            // 健康检查
            let health_results = health_checker.check_all().await;
            for (name, result) in health_results {
                if result.status != HealthStatus::Healthy {
                    eprintln!("健康检查失败: {} - {}", name, result.message.unwrap_or_default());
                }
            }
            
            // 性能监控
            let metrics = performance_monitor.collect_all().await;
            for (name, metric_list) in metrics {
                for metric in metric_list {
                    if metric.value > 1000.0 {
                        eprintln!("性能告警: {} = {}", name, metric.value);
                    }
                }
            }
        }
    });
    
    // 业务逻辑
    // ...
    
    Ok(())
}
```

### 3. 配置管理

```toml
# reliability.toml
[error_handling]
monitoring_enabled = true
error_retention_days = 30
alert_threshold = 10

[fault_tolerance]
circuit_breaker_enabled = true
failure_threshold = 5
recovery_timeout = "60s"

retry_enabled = true
max_attempts = 3
initial_delay = "100ms"
max_delay = "5s"

timeout_enabled = true
default_timeout = "30s"

[monitoring]
health_check_enabled = true
check_interval = "30s"
timeout = "5s"

performance_monitoring_enabled = true
collection_interval = "10s"
retention_period = "24h"

resource_monitoring_enabled = true
monitoring_interval = "5s"
cpu_threshold = 80.0
memory_threshold = 85.0
```

---

*本文档最后更新: 2025年10月20日*-
