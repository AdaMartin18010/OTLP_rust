//! # 微服务架构演示程序
//! 
//! 本示例展示了如何使用OTLP Rust库构建完整的微服务架构，
//! 包括服务发现、负载均衡、熔断器、重试机制等核心功能。

use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;
use tokio::time::sleep;
use tracing::{info, warn, error};
// use opentelemetry::global; // 当前库未提供 create_tracer，取消直接集成

use otlp::{
    microservices::{
        LoadBalancer, RoundRobinLoadBalancer, WeightedRoundRobinLoadBalancer,
        CircuitBreaker, CircuitBreakerConfig,
        Retryer, RetryConfig, ServiceEndpoint, HealthStatus,
        MicroserviceClient, MockConsulClient,
        ServiceDiscoveryClient,
    },
    OtlpConfig, TransportProtocol,
};

/// 初始化OTLP追踪
async fn init_otlp() -> Result<(), Box<dyn std::error::Error>> {
    // 配置OTLP导出器
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc);

    // 验证配置（当前示例不直接创建 Tracer）
    config.validate()?;

    info!("OTLP tracing initialized");
    Ok(())
}

/// 演示负载均衡器功能
async fn demo_load_balancer() -> Result<(), Box<dyn std::error::Error>> {
    info!("🚀 演示负载均衡器功能");
    
    // 创建服务端点
    let endpoints = vec![
        ServiceEndpoint {
            id: "service-1".to_string(),
            address: "localhost".to_string(),
            port: 8080,
            weight: 100,
            metadata: {
                let mut meta = HashMap::new();
                meta.insert("version".to_string(), "1.0.0".to_string());
                meta.insert("environment".to_string(), "production".to_string());
                meta
            },
            health_status: HealthStatus::Healthy,
            last_health_check: std::time::Instant::now(),
        },
        ServiceEndpoint {
            id: "service-2".to_string(),
            address: "localhost".to_string(),
            port: 8081,
            weight: 200,
            metadata: {
                let mut meta = HashMap::new();
                meta.insert("version".to_string(), "2.0.0".to_string());
                meta.insert("environment".to_string(), "production".to_string());
                meta
            },
            health_status: HealthStatus::Healthy,
            last_health_check: std::time::Instant::now(),
        },
        ServiceEndpoint {
            id: "service-3".to_string(),
            address: "localhost".to_string(),
            port: 8082,
            weight: 150,
            metadata: {
                let mut meta = HashMap::new();
                meta.insert("version".to_string(), "1.5.0".to_string());
                meta.insert("environment".to_string(), "staging".to_string());
                meta
            },
            health_status: HealthStatus::Healthy,
            last_health_check: std::time::Instant::now(),
        },
    ];

    // 测试轮询负载均衡器
    info!("📊 测试轮询负载均衡器");
    let mut round_robin_lb = RoundRobinLoadBalancer::new();
    round_robin_lb.update_endpoints(endpoints.clone()).await;

    for i in 0..6 {
        if let Some(endpoint) = round_robin_lb.select_endpoint(&endpoints).await {
            info!("轮询选择 #{}: {}:{} (权重: {})", 
                  i + 1, endpoint.address, endpoint.port, endpoint.weight);
        }
    }

    // 测试加权轮询负载均衡器
    info!("⚖️ 测试加权轮询负载均衡器");
    let mut weighted_lb = WeightedRoundRobinLoadBalancer::new();
    weighted_lb.update_endpoints(endpoints.clone()).await;

    for i in 0..6 {
        if let Some(endpoint) = weighted_lb.select_endpoint(&endpoints).await {
            info!("加权选择 #{}: {}:{} (权重: {})", 
                  i + 1, endpoint.address, endpoint.port, endpoint.weight);
        }
    }

    Ok(())
}

/// 演示熔断器功能
async fn demo_circuit_breaker() -> Result<(), Box<dyn std::error::Error>> {
    info!("🔌 演示熔断器功能");
    
    // 创建熔断器配置
    let config = CircuitBreakerConfig {
        failure_threshold: 3,
        recovery_timeout: Duration::from_millis(500),
        half_open_max_calls: 2,
    };

    let circuit_breaker = Arc::new(CircuitBreaker::new(config));

    // 模拟成功的操作
    info!("✅ 测试成功操作");
    for i in 0..2 {
        let result = circuit_breaker.call(|| {
            Box::pin(async move {
                info!("执行成功操作 #{}", i + 1);
                Ok::<String, anyhow::Error>("操作成功".to_string())
            })
        }).await;

        match result {
            Ok(msg) => info!("操作结果: {}", msg),
            Err(e) => error!("操作失败: {}", e),
        }
    }

    // 模拟失败的操作，触发熔断
    info!("❌ 模拟失败操作，触发熔断");
    for i in 0..5 {
        let result = circuit_breaker.call(|| {
            Box::pin(async move {
                info!("执行失败操作 #{}", i + 1);
                Err::<String, anyhow::Error>(anyhow::anyhow!("模拟错误"))
            })
        }).await;

        match result {
            Ok(msg) => info!("操作结果: {}", msg),
            Err(e) => {
                warn!("操作失败: {}", e);
                let state = circuit_breaker.get_state().await;
                info!("熔断器状态: {:?}", state);
            }
        }
    }

    // 等待恢复时间
    info!("⏳ 等待熔断器恢复...");
    sleep(Duration::from_millis(600)).await;

    // 测试恢复后的操作
    info!("🔄 测试恢复后的操作");
    let result = circuit_breaker.call(|| {
        Box::pin(async move {
            info!("执行恢复后的操作");
            Ok::<String, anyhow::Error>("恢复成功".to_string())
        })
    }).await;

    match result {
        Ok(msg) => {
            info!("操作结果: {}", msg);
            let state = circuit_breaker.get_state().await;
            info!("熔断器状态: {:?}", state);
        }
        Err(e) => error!("操作失败: {}", e),
    }

    Ok(())
}

/// 演示重试机制
async fn demo_retry_mechanism() -> Result<(), Box<dyn std::error::Error>> {
    info!("🔄 演示重试机制");
    
    // 创建重试配置
    let config = RetryConfig {
        max_attempts: 5,
        base_delay: Duration::from_millis(100),
        max_delay: Duration::from_millis(1000),
        backoff_multiplier: 2.0,
        jitter: false,
    };

    let retryer = Arc::new(Retryer::new(config));
    let mut attempt_count = 0;

    // 模拟需要重试的操作
    info!("🎯 测试需要重试的操作");
    let result = retryer.execute(|| {
        Box::pin(async move {
            attempt_count += 1;
            info!("尝试 #{}", attempt_count);
            
            if attempt_count < 3 {
                Err::<String, anyhow::Error>(anyhow::anyhow!("模拟失败"))
            } else {
                Ok("重试成功".to_string())
            }
        })
    }).await;

    match result {
        Ok(msg) => info!("最终结果: {} (总尝试次数: {})", msg, attempt_count),
        Err(e) => error!("重试失败: {}", e),
    }

    // 重置计数器
    attempt_count = 0;

    // 模拟始终失败的操作
    info!("💥 测试始终失败的操作");
    let result = retryer.execute(|| {
        Box::pin(async move {
            attempt_count += 1;
            info!("尝试 #{}", attempt_count);
            Err::<String, anyhow::Error>(anyhow::anyhow!("持续失败"))
        })
    }).await;

    match result {
        Ok(msg) => info!("意外成功: {}", msg),
        Err(e) => error!("最终失败: {} (总尝试次数: {})", e, attempt_count),
    }

    Ok(())
}

/// 演示服务发现功能
async fn demo_service_discovery() -> Result<(), Box<dyn std::error::Error>> {
    info!("🔍 演示服务发现功能");
    
    // 创建负载均衡器
    let load_balancer = Arc::new(RoundRobinLoadBalancer::new());
    
    // 创建配置
    let circuit_breaker_config = CircuitBreakerConfig {
        failure_threshold: 5,
        recovery_timeout: Duration::from_millis(1000),
        half_open_max_calls: 3,
    };
    let retry_config = RetryConfig {
        max_attempts: 3,
        base_delay: Duration::from_millis(50),
        max_delay: Duration::from_millis(500),
        backoff_multiplier: 2.0,
        jitter: true,
    };

    // 使用 MockConsulClient 作为服务发现实现，并预注册服务
    let service_discovery = Arc::new(MockConsulClient::new());
    service_discovery.add_service(
        "user-service".to_string(),
        vec![
            ServiceEndpoint {
                id: "user-1".to_string(),
                address: "localhost".to_string(),
                port: 8001,
                weight: 100,
                metadata: {
                    let mut m = HashMap::new();
                    m.insert("service_name".to_string(), "user-service".to_string());
                    m
                },
                health_status: HealthStatus::Healthy,
                last_health_check: std::time::Instant::now(),
            },
        ],
    ).await;

    // 创建微服务客户端
    let microservice_client = MicroserviceClient::new(
        service_discovery.clone(),
        load_balancer.clone(),
        circuit_breaker_config,
        retry_config,
    );
    
    // 模拟服务发现
    info!("🔍 发现用户服务");
    match ServiceDiscoveryClient::discover_services(&*service_discovery, "user-service").await {
        Ok(endpoints) => {
            if let Some(endpoint) = endpoints.first() {
                info!("找到服务端点: {}:{}", endpoint.address, endpoint.port);
                info!("服务元数据: {:?}", endpoint.metadata);
            } else {
                warn!("未找到用户服务");
            }
        }
        Err(e) => error!("服务发现失败: {}", e),
    }
    
    // 模拟调用微服务
    info!("📞 调用微服务API");
    let res = microservice_client.call_service("user-service", |endpoint| {
        let url = format!("http://{}:{}/api/users/123", endpoint.address, endpoint.port);
        Box::pin(async move {
            // 这里可替换为真实HTTP调用；演示返回拼接好的URL
            Ok::<String, anyhow::Error>(url)
        })
    }).await;

    match res {
        Ok(msg) => info!("API调用成功: {}", msg),
        Err(e) => warn!("API调用失败: {}", e),
    }
    
    Ok(())
}

/// 演示完整的微服务架构
async fn demo_complete_microservice_architecture() -> Result<(), Box<dyn std::error::Error>> {
    info!("🏗️ 演示完整的微服务架构");
    
    // 创建模拟的服务端点
    let user_service_endpoints = vec![
        ServiceEndpoint {
            id: "user-service-1".to_string(),
            address: "localhost".to_string(),
            port: 8001,
            weight: 100,
            metadata: {
                let mut meta = HashMap::new();
                meta.insert("version".to_string(), "1.0.0".to_string());
                meta.insert("region".to_string(), "us-west-1".to_string());
                meta
            },
            health_status: HealthStatus::Healthy,
            last_health_check: std::time::Instant::now(),
        },
        ServiceEndpoint {
            id: "user-service-2".to_string(),
            address: "localhost".to_string(),
            port: 8002,
            weight: 150,
            metadata: {
                let mut meta = HashMap::new();
                meta.insert("version".to_string(), "1.1.0".to_string());
                meta.insert("region".to_string(), "us-east-1".to_string());
                meta
            },
            health_status: HealthStatus::Healthy,
            last_health_check: std::time::Instant::now(),
        },
    ];
    
    let order_service_endpoints = vec![
        ServiceEndpoint {
            id: "order-service-1".to_string(),
            address: "localhost".to_string(),
            port: 8003,
            weight: 200,
            metadata: {
                let mut meta = HashMap::new();
                meta.insert("version".to_string(), "2.0.0".to_string());
                meta.insert("region".to_string(), "us-west-1".to_string());
                meta
            },
            health_status: HealthStatus::Healthy,
            last_health_check: std::time::Instant::now(),
        },
    ];
    
    // 创建负载均衡器
    let mut user_service_lb = WeightedRoundRobinLoadBalancer::new();
    let mut order_service_lb = RoundRobinLoadBalancer::new();
    
    // 创建熔断器配置
    let _circuit_breaker_config = CircuitBreakerConfig {
        failure_threshold: 3,
        recovery_timeout: Duration::from_millis(500),
        half_open_max_calls: 2,
    };
    
    // 创建重试配置
    let _retry_config = RetryConfig {
        max_attempts: 3,
        base_delay: Duration::from_millis(100),
        max_delay: Duration::from_millis(1000),
        backoff_multiplier: 2.0,
        jitter: true,
    };
    
    // 模拟微服务调用链
    info!("🔗 模拟微服务调用链: API Gateway -> User Service -> Order Service");
    
    // 1. API Gateway 调用 User Service
    info!("📞 API Gateway 调用 User Service");
    user_service_lb.update_endpoints(user_service_endpoints.clone()).await;
    
    for i in 0..3 {
        if let Some(endpoint) = user_service_lb.select_endpoint(&user_service_endpoints).await {
            info!("调用用户服务 #{}: {}:{}", i + 1, endpoint.address, endpoint.port);
            
            // 模拟处理时间
            sleep(Duration::from_millis(50)).await;
            
            // 2. User Service 调用 Order Service
            info!("📞 User Service 调用 Order Service");
            order_service_lb.update_endpoints(order_service_endpoints.clone()).await;
            
            if let Some(order_endpoint) = order_service_lb.select_endpoint(&order_service_endpoints).await {
                info!("调用订单服务: {}:{}", order_endpoint.address, order_endpoint.port);
                
                // 模拟处理时间
                sleep(Duration::from_millis(30)).await;
                
                info!("✅ 调用链完成");
            }
        }
    }
    
    Ok(())
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt::init();
    
    // 初始化OTLP追踪
    init_otlp().await?;
    
    info!("🚀 OTLP Rust 1.90 微服务架构演示程序");
    info!("======================================");
    
    // 演示各个组件
    demo_load_balancer().await?;
    println!();
    
    demo_circuit_breaker().await?;
    println!();
    
    demo_retry_mechanism().await?;
    println!();
    
    demo_service_discovery().await?;
    println!();
    
    demo_complete_microservice_architecture().await?;
    
    info!("🎉 微服务架构演示完成！");
    
    Ok(())
}
