//! # 高级微服务架构演示程序
//!
//! 本示例展示了如何使用OTLP Rust库的高级微服务功能，
//! 包括智能路由、自适应负载均衡、故障注入等企业级特性。

use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;
use tokio::time::sleep;
use tracing::{debug, info, warn};

use otlp::{
    AdaptiveLoadBalancer, CircuitBreakerPolicy, Destination, FaultConfig, FaultInjector,
    FaultResult, FaultType, MicroserviceHealthStatus, IntelligentRouter, MatchCondition, OtlpConfig,
    ResourceLimits, RetryPolicy, RoundRobinLoadBalancer, RouteRequest, RoutingRule,
    ServiceEndpoint, ServiceMeshConfig, ServiceMeshType, SidecarConfig, TrafficManager,
    TransportProtocol,
};

/// 初始化OTLP追踪
async fn init_otlp() -> Result<(), Box<dyn std::error::Error>> {
    // 配置OTLP导出器
    let _config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc);

    // 注意：实际的OTLP初始化需要完整的tracer provider设置
    // 这里为了演示目的，我们跳过实际的tracer创建
    info!("OTLP tracing configuration prepared for advanced microservices demo");
    Ok(())
}

/// 演示智能路由功能
async fn demo_intelligent_routing() -> Result<(), Box<dyn std::error::Error>> {
    info!("🧭 演示智能路由功能");

    // 创建服务网格配置
    let mesh_config = ServiceMeshConfig {
        mesh_type: ServiceMeshType::Istio,
        control_plane_endpoint: "istiod.istio-system.svc.cluster.local:15012".to_string(),
        data_plane_endpoint: "localhost:15000".to_string(),
        service_account: "user-service".to_string(),
        namespace: "default".to_string(),
        sidecar_config: SidecarConfig {
            enabled: true,
            image: "istio/proxyv2:1.19.0".to_string(),
            resources: ResourceLimits {
                cpu_limit: "500m".to_string(),
                memory_limit: "512Mi".to_string(),
                cpu_request: "100m".to_string(),
                memory_request: "128Mi".to_string(),
            },
            env_vars: {
                let mut vars = HashMap::new();
                vars.insert(
                    "PILOT_ENABLE_WORKLOAD_ENTRY_AUTOREGISTRATION".to_string(),
                    "true".to_string(),
                );
                vars
            },
        },
    };

    info!("服务网格配置: {:?}", mesh_config);

    // 创建智能路由器
    let traffic_manager = Arc::new(TrafficManager::new());
    let load_balancer = Arc::new(RoundRobinLoadBalancer::new());
    let router = IntelligentRouter::new(traffic_manager, load_balancer);

    // 添加路由规则
    let api_rule = RoutingRule {
        name: "api-routing".to_string(),
        match_conditions: vec![
            MatchCondition::Path {
                pattern: "/api/*".to_string(),
            },
            MatchCondition::Method {
                methods: vec!["GET".to_string(), "POST".to_string()],
            },
        ],
        destination: Destination {
            service: "user-service".to_string(),
            namespace: "default".to_string(),
            subset: Some("v1".to_string()),
            port: 8080,
        },
        weight: 80,
        timeout: Duration::from_secs(30),
        retry_policy: RetryPolicy {
            attempts: 3,
            per_try_timeout: Duration::from_secs(5),
            retry_on: vec!["5xx".to_string(), "reset".to_string()],
            retry_remote_localities: false,
        },
        circuit_breaker: CircuitBreakerPolicy {
            consecutive_errors: 5,
            interval: Duration::from_secs(10),
            base_ejection_time: Duration::from_secs(30),
            max_ejection_percent: 50,
        },
    };

    let admin_rule = RoutingRule {
        name: "admin-routing".to_string(),
        match_conditions: vec![
            MatchCondition::Path {
                pattern: "/admin/*".to_string(),
            },
            MatchCondition::Header {
                name: "X-Admin-Token".to_string(),
                value: "admin-secret".to_string(),
            },
        ],
        destination: Destination {
            service: "admin-service".to_string(),
            namespace: "default".to_string(),
            subset: None,
            port: 8081,
        },
        weight: 20,
        timeout: Duration::from_secs(60),
        retry_policy: RetryPolicy {
            attempts: 1,
            per_try_timeout: Duration::from_secs(10),
            retry_on: vec!["5xx".to_string()],
            retry_remote_localities: false,
        },
        circuit_breaker: CircuitBreakerPolicy {
            consecutive_errors: 3,
            interval: Duration::from_secs(5),
            base_ejection_time: Duration::from_secs(60),
            max_ejection_percent: 30,
        },
    };

    router.add_rule(api_rule).await?;
    router.add_rule(admin_rule).await?;

    info!("✅ 路由规则添加成功");

    // 模拟路由请求
    let test_requests = vec![
        RouteRequest {
            method: "GET".to_string(),
            path: "/api/users".to_string(),
            headers: HashMap::new(),
            query_params: HashMap::new(),
            source_service: "gateway".to_string(),
            source_namespace: "default".to_string(),
            body: None,
        },
        RouteRequest {
            method: "GET".to_string(),
            path: "/admin/dashboard".to_string(),
            headers: {
                let mut headers = HashMap::new();
                headers.insert("X-Admin-Token".to_string(), "admin-secret".to_string());
                headers
            },
            query_params: HashMap::new(),
            source_service: "gateway".to_string(),
            source_namespace: "default".to_string(),
            body: None,
        },
    ];

    for (i, request) in test_requests.iter().enumerate() {
        info!(
            "📝 处理请求 #{}: {} {}",
            i + 1,
            request.method,
            request.path
        );

        match router.route_request(request).await {
            Ok(response) => {
                info!(
                    "✅ 路由成功: {} -> {}:{}",
                    request.path, response.destination.address, response.destination.port
                );
                info!("   路由规则: {}", response.rule.name);
                info!("   路由时间: {:?}", response.routing_time);
            }
            Err(e) => {
                warn!("❌ 路由失败: {}", e);
            }
        }
    }

    Ok(())
}

/// 演示自适应负载均衡
async fn demo_adaptive_load_balancing() -> Result<(), Box<dyn std::error::Error>> {
    info!("⚖️ 演示自适应负载均衡");

    // 创建自适应负载均衡器
    let adaptive_lb = AdaptiveLoadBalancer::new();

    // 创建测试端点
    let endpoints = vec![
        ServiceEndpoint {
            id: "instance-1".to_string(),
            address: "10.0.1.10".to_string(),
            port: 8080,
            weight: 100,
            metadata: {
                let mut meta = HashMap::new();
                meta.insert("zone".to_string(), "us-west-1a".to_string());
                meta.insert("version".to_string(), "v1.2.0".to_string());
                meta
            },
            health_status: MicroserviceHealthStatus::Healthy,
            last_health_check: std::time::Instant::now(),
        },
        ServiceEndpoint {
            id: "instance-2".to_string(),
            address: "10.0.1.11".to_string(),
            port: 8080,
            weight: 150,
            metadata: {
                let mut meta = HashMap::new();
                meta.insert("zone".to_string(), "us-west-1b".to_string());
                meta.insert("version".to_string(), "v1.2.1".to_string());
                meta
            },
            health_status: MicroserviceHealthStatus::Healthy,
            last_health_check: std::time::Instant::now(),
        },
        ServiceEndpoint {
            id: "instance-3".to_string(),
            address: "10.0.1.12".to_string(),
            port: 8080,
            weight: 200,
            metadata: {
                let mut meta = HashMap::new();
                meta.insert("zone".to_string(), "us-west-1c".to_string());
                meta.insert("version".to_string(), "v1.2.1".to_string());
                meta
            },
            health_status: MicroserviceHealthStatus::Healthy,
            last_health_check: std::time::Instant::now(),
        },
    ];

    info!("🎯 开始负载均衡测试，共 {} 个端点", endpoints.len());

    // 模拟请求处理
    for i in 0..20 {
        let _start_time = std::time::Instant::now();

        // 选择端点
        if let Some(selected) = adaptive_lb.select_endpoint(&endpoints).await {
            info!(
                "请求 #{}: 选择端点 {} ({})",
                i + 1,
                selected.id,
                selected.address
            );

            // 模拟请求处理时间
            let response_time = if i % 10 == 0 {
                // 模拟慢响应
                Duration::from_millis(500)
            } else if i % 15 == 0 {
                // 模拟错误
                Duration::from_millis(100)
            } else {
                Duration::from_millis(50 + (i % 50))
            };

            sleep(response_time).await;

            // 记录性能结果
            let success = i % 15 != 0; // 模拟偶尔的失败
            adaptive_lb
                .record_request_result("round_robin", success, response_time)
                .await;

            info!("   响应时间: {:?}, 成功: {}", response_time, success);
        }

        // 每5个请求评估一次算法性能
        if i % 5 == 0 {
            adaptive_lb.evaluate_and_switch_algorithm().await;
        }
    }

    info!("✅ 自适应负载均衡测试完成");

    Ok(())
}

/// 演示故障注入功能
async fn demo_fault_injection() -> Result<(), Box<dyn std::error::Error>> {
    info!("💥 演示故障注入功能");

    // 创建故障注入器
    let fault_injector = FaultInjector::new();

    // 添加不同类型的故障配置
    let fault_configs = vec![
        FaultConfig {
            name: "delay-fault".to_string(),
            fault_type: FaultType::Delay {
                delay: Duration::from_millis(100),
            },
            probability: 0.3, // 30%概率
            duration: Duration::from_secs(60),
            enabled: true,
        },
        FaultConfig {
            name: "error-fault".to_string(),
            fault_type: FaultType::Error {
                status_code: 500,
                message: "Internal Server Error".to_string(),
            },
            probability: 0.1, // 10%概率
            duration: Duration::from_secs(30),
            enabled: true,
        },
        FaultConfig {
            name: "abort-fault".to_string(),
            fault_type: FaultType::Abort { status_code: 503 },
            probability: 0.05, // 5%概率
            duration: Duration::from_secs(15),
            enabled: true,
        },
        FaultConfig {
            name: "throttle-fault".to_string(),
            fault_type: FaultType::Throttle { rate: 10 }, // 10 req/s
            probability: 0.2,                             // 20%概率
            duration: Duration::from_secs(45),
            enabled: true,
        },
    ];

    // 添加故障配置
    for config in fault_configs {
        fault_injector.add_fault_config(config).await;
    }

    info!("✅ 故障配置添加完成");

    // 模拟服务请求
    let services = vec!["user-service", "order-service", "payment-service"];
    let request_ids: Vec<String> = (1..=20).map(|i| format!("req-{:03}", i)).collect();

    for (i, (service, request_id)) in services.iter().cycle().zip(request_ids).enumerate() {
        info!("📞 处理请求 #{}: {} -> {}", i + 1, request_id, service);

        // 注入故障
        match fault_injector.inject_fault(service, &request_id).await? {
            Some(fault_result) => match fault_result {
                FaultResult::Delay(duration) => {
                    warn!("⏰ 注入延迟故障: {:?}", duration);
                    sleep(duration).await;
                }
                FaultResult::Error {
                    status_code,
                    message,
                } => {
                    warn!("❌ 注入错误故障: {} {}", status_code, message);
                }
                FaultResult::Abort(status_code) => {
                    warn!("🛑 注入中止故障: {}", status_code);
                }
                FaultResult::Throttle(rate) => {
                    warn!("🚦 注入限流故障: {} req/s", rate);
                }
            },
            None => {
                debug!("✅ 无故障注入，正常处理");
            }
        }

        // 模拟正常处理时间
        sleep(Duration::from_millis(50)).await;
    }

    info!("✅ 故障注入测试完成");

    Ok(())
}

/// 演示服务网格集成
async fn demo_service_mesh_integration() -> Result<(), Box<dyn std::error::Error>> {
    info!("🕸️ 演示服务网格集成");

    // 创建不同服务网格的配置
    let mesh_configs = vec![
        ("Istio", ServiceMeshType::Istio),
        ("Linkerd2", ServiceMeshType::Linkerd2),
        ("Consul Connect", ServiceMeshType::ConsulConnect),
        ("Envoy", ServiceMeshType::Envoy),
    ];

    for (name, mesh_type) in mesh_configs {
        info!("🔧 配置 {} 服务网格", name);

        let config = ServiceMeshConfig {
            mesh_type: mesh_type.clone(),
            control_plane_endpoint: match mesh_type {
                ServiceMeshType::Istio => "istiod.istio-system.svc.cluster.local:15012".to_string(),
                ServiceMeshType::Linkerd2 => {
                    "linkerd-dst.linkerd.svc.cluster.local:8086".to_string()
                }
                ServiceMeshType::ConsulConnect => {
                    "consul-server.consul.svc.cluster.local:8500".to_string()
                }
                ServiceMeshType::Envoy => "envoy-admin.localhost:9901".to_string(),
            },
            data_plane_endpoint: "localhost:15000".to_string(),
            service_account: format!("{}-service", name.to_lowercase()),
            namespace: "default".to_string(),
            sidecar_config: SidecarConfig {
                enabled: true,
                image: match mesh_type {
                    ServiceMeshType::Istio => "istio/proxyv2:1.19.0".to_string(),
                    ServiceMeshType::Linkerd2 => {
                        "cr.l5d.io/linkerd/proxy:stable-2.14.0".to_string()
                    }
                    ServiceMeshType::ConsulConnect => "consul:1.16.0".to_string(),
                    ServiceMeshType::Envoy => "envoyproxy/envoy:v1.29.0".to_string(),
                },
                resources: ResourceLimits {
                    cpu_limit: "500m".to_string(),
                    memory_limit: "512Mi".to_string(),
                    cpu_request: "100m".to_string(),
                    memory_request: "128Mi".to_string(),
                },
                env_vars: {
                    let mut vars = HashMap::new();
                    match mesh_type {
                        ServiceMeshType::Istio => {
                            vars.insert(
                                "PILOT_ENABLE_WORKLOAD_ENTRY_AUTOREGISTRATION".to_string(),
                                "true".to_string(),
                            );
                        }
                        ServiceMeshType::Linkerd2 => {
                            vars.insert(
                                "LINKERD2_PROXY_LOG".to_string(),
                                "warn,linkerd=info".to_string(),
                            );
                        }
                        ServiceMeshType::ConsulConnect => {
                            vars.insert(
                                "CONSUL_HTTP_ADDR".to_string(),
                                "consul-server.consul.svc.cluster.local:8500".to_string(),
                            );
                        }
                        ServiceMeshType::Envoy => {
                            vars.insert("ENVOY_LOG_LEVEL".to_string(), "info".to_string());
                        }
                    }
                    vars
                },
            },
        };

        info!("  控制平面端点: {}", config.control_plane_endpoint);
        info!("  数据平面端点: {}", config.data_plane_endpoint);
        info!("  服务账户: {}", config.service_account);
        info!("  Sidecar镜像: {}", config.sidecar_config.image);
        info!(
            "  资源配置: CPU {} / 内存 {}",
            config.sidecar_config.resources.cpu_limit, config.sidecar_config.resources.memory_limit
        );

        // 模拟服务网格功能
        info!("  🔐 启用mTLS加密通信");
        info!("  📊 启用流量指标收集");
        info!("  🛡️ 启用安全策略");
        info!("  🔄 启用服务发现");

        sleep(Duration::from_millis(100)).await;
    }

    info!("✅ 服务网格集成演示完成");

    Ok(())
}

/// 演示完整的微服务架构
async fn demo_complete_enterprise_architecture() -> Result<(), Box<dyn std::error::Error>> {
    info!("🏢 演示完整的企业级微服务架构");

    // 创建服务网格配置
    let _mesh_config = ServiceMeshConfig {
        mesh_type: ServiceMeshType::Istio,
        control_plane_endpoint: "istiod.istio-system.svc.cluster.local:15012".to_string(),
        data_plane_endpoint: "localhost:15000".to_string(),
        service_account: "enterprise-service".to_string(),
        namespace: "production".to_string(),
        sidecar_config: SidecarConfig {
            enabled: true,
            image: "istio/proxyv2:1.19.0".to_string(),
            resources: ResourceLimits {
                cpu_limit: "1000m".to_string(),
                memory_limit: "1Gi".to_string(),
                cpu_request: "200m".to_string(),
                memory_request: "256Mi".to_string(),
            },
            env_vars: HashMap::new(),
        },
    };

    // 创建智能路由器
    let traffic_manager = Arc::new(TrafficManager::new());
    let adaptive_lb = Arc::new(AdaptiveLoadBalancer::new());
    let router = IntelligentRouter::new(traffic_manager, adaptive_lb);

    // 创建故障注入器
    let fault_injector = FaultInjector::new();

    // 添加企业级路由规则
    let enterprise_rules = vec![
        // API路由规则
        RoutingRule {
            name: "api-v1-routing".to_string(),
            match_conditions: vec![
                MatchCondition::Path {
                    pattern: "/api/v1/*".to_string(),
                },
                MatchCondition::Method {
                    methods: vec!["GET".to_string(), "POST".to_string(), "PUT".to_string()],
                },
            ],
            destination: Destination {
                service: "api-gateway".to_string(),
                namespace: "production".to_string(),
                subset: Some("v1".to_string()),
                port: 8080,
            },
            weight: 70,
            timeout: Duration::from_secs(30),
            retry_policy: RetryPolicy {
                attempts: 3,
                per_try_timeout: Duration::from_secs(5),
                retry_on: vec!["5xx".to_string(), "reset".to_string()],
                retry_remote_localities: false,
            },
            circuit_breaker: CircuitBreakerPolicy {
                consecutive_errors: 5,
                interval: Duration::from_secs(10),
                base_ejection_time: Duration::from_secs(30),
                max_ejection_percent: 50,
            },
        },
        // 管理路由规则
        RoutingRule {
            name: "admin-routing".to_string(),
            match_conditions: vec![
                MatchCondition::Path {
                    pattern: "/admin/*".to_string(),
                },
                MatchCondition::Header {
                    name: "X-Admin-Token".to_string(),
                    value: "admin-secret".to_string(),
                },
            ],
            destination: Destination {
                service: "admin-service".to_string(),
                namespace: "production".to_string(),
                subset: None,
                port: 8081,
            },
            weight: 20,
            timeout: Duration::from_secs(60),
            retry_policy: RetryPolicy {
                attempts: 1,
                per_try_timeout: Duration::from_secs(10),
                retry_on: vec!["5xx".to_string()],
                retry_remote_localities: false,
            },
            circuit_breaker: CircuitBreakerPolicy {
                consecutive_errors: 3,
                interval: Duration::from_secs(5),
                base_ejection_time: Duration::from_secs(60),
                max_ejection_percent: 30,
            },
        },
        // 监控路由规则
        RoutingRule {
            name: "metrics-routing".to_string(),
            match_conditions: vec![
                MatchCondition::Path {
                    pattern: "/metrics".to_string(),
                },
                MatchCondition::Method {
                    methods: vec!["GET".to_string()],
                },
            ],
            destination: Destination {
                service: "metrics-service".to_string(),
                namespace: "monitoring".to_string(),
                subset: None,
                port: 9090,
            },
            weight: 10,
            timeout: Duration::from_secs(10),
            retry_policy: RetryPolicy {
                attempts: 2,
                per_try_timeout: Duration::from_secs(3),
                retry_on: vec!["5xx".to_string()],
                retry_remote_localities: false,
            },
            circuit_breaker: CircuitBreakerPolicy {
                consecutive_errors: 10,
                interval: Duration::from_secs(30),
                base_ejection_time: Duration::from_secs(120),
                max_ejection_percent: 20,
            },
        },
    ];

    // 添加路由规则
    for rule in enterprise_rules {
        router.add_rule(rule).await?;
    }

    // 添加故障注入配置
    let chaos_config = FaultConfig {
        name: "chaos-engineering".to_string(),
        fault_type: FaultType::Delay {
            delay: Duration::from_millis(50),
        },
        probability: 0.05, // 5%概率进行混沌工程测试
        duration: Duration::from_secs(300),
        enabled: true,
    };
    fault_injector.add_fault_config(chaos_config).await;

    info!("✅ 企业级架构配置完成");

    // 模拟企业级请求处理
    let enterprise_requests = vec![
        ("GET", "/api/v1/users", "user-service"),
        ("POST", "/api/v1/orders", "order-service"),
        ("GET", "/admin/dashboard", "admin-service"),
        ("GET", "/metrics", "metrics-service"),
        ("GET", "/api/v1/products", "product-service"),
    ];

    info!("🚀 开始企业级请求处理模拟");

    for (i, (method, path, service)) in enterprise_requests.iter().enumerate() {
        info!(
            "📋 处理企业请求 #{}: {} {} -> {}",
            i + 1,
            method,
            path,
            service
        );

        // 创建路由请求
        let route_request = RouteRequest {
            method: method.to_string(),
            path: path.to_string(),
            headers: {
                let mut headers = HashMap::new();
                if path.starts_with("/admin/") {
                    headers.insert("X-Admin-Token".to_string(), "admin-secret".to_string());
                }
                headers.insert(
                    "User-Agent".to_string(),
                    "Enterprise-Client/1.0".to_string(),
                );
                headers.insert("X-Request-ID".to_string(), format!("req-{:06}", i + 1));
                headers
            },
            query_params: HashMap::new(),
            source_service: "enterprise-gateway".to_string(),
            source_namespace: "production".to_string(),
            body: None,
        };

        // 执行路由
        match router.route_request(&route_request).await {
            Ok(response) => {
                info!(
                    "✅ 路由成功: {} -> {}:{}",
                    path, response.destination.address, response.destination.port
                );
                info!(
                    "   规则: {}, 权重: {}, 超时: {:?}",
                    response.rule.name, response.rule.weight, response.rule.timeout
                );

                // 注入故障（混沌工程）
                match fault_injector
                    .inject_fault(service, &format!("req-{:06}", i + 1))
                    .await?
                {
                    Some(fault_result) => match fault_result {
                        FaultResult::Delay(duration) => {
                            warn!("⏰ 混沌工程延迟: {:?}", duration);
                            sleep(duration).await;
                        }
                        _ => {
                            warn!("💥 混沌工程故障注入");
                        }
                    },
                    None => {
                        debug!("✅ 正常处理，无故障注入");
                    }
                }
            }
            Err(e) => {
                warn!("❌ 路由失败: {}", e);
            }
        }

        sleep(Duration::from_millis(100)).await;
    }

    info!("🎉 企业级微服务架构演示完成！");
    info!("📊 架构特性总结:");
    info!("   ✅ 智能路由和流量管理");
    info!("   ✅ 自适应负载均衡");
    info!("   ✅ 服务网格集成");
    info!("   ✅ 混沌工程和故障注入");
    info!("   ✅ 熔断器和重试机制");
    info!("   ✅ 分布式追踪和监控");

    Ok(())
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    // 初始化OTLP追踪
    init_otlp().await?;

    info!("🚀 OTLP Rust 1.90 高级微服务架构演示程序");
    info!("=============================================");

    // 演示各个高级功能
    demo_intelligent_routing().await?;
    println!();

    demo_adaptive_load_balancing().await?;
    println!();

    demo_fault_injection().await?;
    println!();

    demo_service_mesh_integration().await?;
    println!();

    demo_complete_enterprise_architecture().await?;

    info!("🎉 高级微服务架构演示完成！");

    Ok(())
}
