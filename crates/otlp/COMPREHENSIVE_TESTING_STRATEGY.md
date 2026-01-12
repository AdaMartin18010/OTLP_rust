# 🧪 OTLP Rust 完整测试策略

## 📋 测试概览

**测试目标**: 确保代码质量、功能正确性、性能稳定性和生产就绪性
**测试范围**: 单元测试、集成测试、性能测试、端到端测试
**测试覆盖率**: >95%
**实施周期**: 4-6周

## 🎯 测试金字塔架构

```text
        ┌─────────────────┐
        │   端到端测试     │  ← 少量，高价值
        │   (E2E Tests)   │
        └─────────────────┘
       ┌─────────────────────┐
       │    集成测试          │  ← 中等数量，中等价值
       │ (Integration Tests) │
       └─────────────────────┘
    ┌─────────────────────────────┐
    │        单元测试              │  ← 大量，基础价值
    │    (Unit Tests)             │
    └─────────────────────────────┘
```

## 🔧 测试类型详细设计

### 1. 单元测试 (Unit Tests)

#### 1.1 核心模块测试

```rust
#[cfg(test)]
mod unit_tests {
    use super::*;
    use mockall::mock;
    use tokio_test;

    // 熔断器测试
    mod circuit_breaker_tests {
        use super::*;

        #[tokio::test]
        async fn test_circuit_breaker_closed_to_open() {
            let config = CircuitBreakerConfig {
                failure_threshold: 3,
                recovery_timeout: Duration::from_secs(10),
                ..Default::default()
            };

            let cb = CircuitBreaker::new(config);

            // 连续失败3次，应该触发熔断
            for _ in 0..3 {
                let result = cb.call(|| async {
                    Err::<(), anyhow::Error>(anyhow::anyhow!("test error"))
                }).await;
                assert!(result.is_err());
            }

            // 第4次调用应该被熔断器拦截
            let result = cb.call(|| async { Ok::<(), anyhow::Error>(()) }).await;
            assert!(matches!(result, Err(CircuitBreakerError::CircuitBreakerOpen)));
        }

        #[tokio::test]
        async fn test_circuit_breaker_recovery() {
            let config = CircuitBreakerConfig {
                failure_threshold: 2,
                recovery_timeout: Duration::from_millis(100),
                ..Default::default()
            };

            let cb = CircuitBreaker::new(config);

            // 触发熔断
            for _ in 0..2 {
                let _ = cb.call(|| async {
                    Err::<(), anyhow::Error>(anyhow::anyhow!("test error"))
                }).await;
            }

            // 等待恢复时间
            tokio::time::sleep(Duration::from_millis(150)).await;

            // 应该能够恢复
            let result = cb.call(|| async { Ok::<(), anyhow::Error>(()) }).await;
            assert!(result.is_ok());
        }
    }

    // 错误处理测试
    mod error_handling_tests {
        use super::*;

        #[test]
        fn test_error_severity_classification() {
            let network_error = OtlpError::network("Connection failed", std::io::Error::new(std::io::ErrorKind::ConnectionRefused, "Connection refused"));
            assert_eq!(network_error.severity(), ErrorSeverity::High);

            let config_error = OtlpError::configuration("endpoint", "invalid-url");
            assert_eq!(config_error.severity(), ErrorSeverity::Medium);
        }

        #[test]
        fn test_error_retryable_logic() {
            let retryable_error = OtlpError::network("Timeout", std::io::Error::new(std::io::ErrorKind::TimedOut, "Request timeout"));
            assert!(retryable_error.is_retryable());

            let non_retryable_error = OtlpError::configuration("endpoint", "invalid-url");
            assert!(!non_retryable_error.is_retryable());
        }
    }

    // 配置验证测试
    mod config_validation_tests {
        use super::*;

        #[test]
        fn test_valid_endpoint() {
            let endpoint = Endpoint::new("http://localhost:4317").unwrap();
            assert_eq!(endpoint.as_str(), "http://localhost:4317");
        }

        #[test]
        fn test_invalid_endpoint() {
            let result = Endpoint::new("invalid-url");
            assert!(result.is_err());
        }

        #[test]
        fn test_batch_size_validation() {
            let valid_size = BatchSize::new(100).unwrap();
            assert_eq!(valid_size.value(), 100);

            let invalid_size = BatchSize::new(0);
            assert!(invalid_size.is_err());

            let too_large = BatchSize::new(10001);
            assert!(too_large.is_err());
        }
    }
}
```

#### 1.2 性能组件测试

```rust
#[cfg(test)]
mod performance_tests {
    use super::*;

    // 内存池测试
    mod memory_pool_tests {
        use super::*;

        #[tokio::test]
        async fn test_object_pool_reuse() {
            let pool = OptimizedObjectPool::new(|| String::with_capacity(1024), 10);

            let obj1 = pool.acquire().await;
            let capacity1 = obj1.get().capacity();
            drop(obj1);

            // 等待异步回收
            tokio::time::sleep(Duration::from_millis(10)).await;

            let obj2 = pool.acquire().await;
            let capacity2 = obj2.get().capacity();

            // 应该重用同一个对象
            assert_eq!(capacity1, capacity2);
        }

        #[tokio::test]
        async fn test_pool_size_limit() {
            let pool = OptimizedObjectPool::new(|| String::new(), 2);

            let obj1 = pool.acquire().await;
            let obj2 = pool.acquire().await;
            let obj3 = pool.acquire().await;

            drop(obj1);
            drop(obj2);
            drop(obj3);

            tokio::time::sleep(Duration::from_millis(10)).await;

            let stats = pool.get_stats().await;
            assert_eq!(stats.total_created, 3);
            assert_eq!(stats.total_reused, 0); // 池已满，无法重用
        }
    }

    // 批处理器测试
    mod batch_processor_tests {
        use super::*;

        #[tokio::test]
        async fn test_batch_size_trigger() {
            let processor = AsyncBatchProcessor::new(3, Duration::from_secs(1), 10);

            // 添加3个项目，应该触发批处理
            for i in 0..3 {
                processor.add_item(i).await.unwrap();
            }

            let batch = processor.get_next_batch().await;
            assert!(batch.is_some());
            assert_eq!(batch.unwrap().len(), 3);
        }

        #[tokio::test]
        async fn test_batch_timeout_trigger() {
            let processor = AsyncBatchProcessor::new(10, Duration::from_millis(100), 10);

            // 添加1个项目
            processor.add_item(1).await.unwrap();

            // 等待超时
            tokio::time::sleep(Duration::from_millis(150)).await;

            // 强制刷新
            let batch = processor.flush().await.unwrap();
            assert!(batch.is_some());
            assert_eq!(batch.unwrap().len(), 1);
        }
    }
}
```

### 2. 集成测试 (Integration Tests)

#### 2.1 组件集成测试

```rust
#[cfg(test)]
mod integration_tests {
    use super::*;
    use testcontainers::*;
    use testcontainers::images::generic::GenericImage;

    // OTLP端点集成测试
    mod otlp_endpoint_tests {
        use super::*;

        #[tokio::test]
        async fn test_grpc_export_integration() {
            let docker = clients::Cli::default();
            let jaeger = docker.run(GenericImage::new("jaegertracing/all-in-one", "latest"));

            let config = OtlpConfig::default()
                .with_endpoint(&format!("http://localhost:{}", jaeger.get_host_port_ipv4(14268)))
                .with_protocol(TransportProtocol::Grpc);

            let client = OtlpClient::new(config).await.unwrap();
            client.initialize().await.unwrap();

            // 发送追踪数据
            let trace = client.send_trace("integration-test").await.unwrap();
            let result = trace
                .with_attribute("test", "integration")
                .with_duration(100)
                .finish()
                .await
                .unwrap();

            assert!(result.is_success());
            assert_eq!(result.success_count, 1);
        }

        #[tokio::test]
        async fn test_http_export_integration() {
            let docker = clients::Cli::default();
            let jaeger = docker.run(GenericImage::new("jaegertracing/all-in-one", "latest"));

            let config = OtlpConfig::default()
                .with_endpoint(&format!("http://localhost:{}", jaeger.get_host_port_ipv4(14268)))
                .with_protocol(TransportProtocol::Http);

            let client = OtlpClient::new(config).await.unwrap();
            client.initialize().await.unwrap();

            // 发送指标数据
            let metric = client.send_metric("integration-metric", 42.0).await.unwrap();
            let result = metric
                .with_label("test", "integration")
                .with_description("Integration test metric")
                .send()
                .await
                .unwrap();

            assert!(result.is_success());
        }
    }

    // 弹性机制集成测试
    mod resilience_integration_tests {
        use super::*;

        #[tokio::test]
        async fn test_circuit_breaker_with_retry() {
            let config = OtlpConfig::default()
                .with_endpoint("http://unreachable-host:4317")
                .with_retry_config(RetryConfig {
                    max_retries: 3,
                    initial_retry_delay: Duration::from_millis(10),
                    ..Default::default()
                });

            let client = OtlpClient::new(config).await.unwrap();
            client.initialize().await.unwrap();

            let trace = client.send_trace("resilience-test").await.unwrap();
            let result = trace.finish().await;

            // 应该失败，但经过重试和熔断器处理
            assert!(result.is_err());
        }
    }
}
```

#### 2.2 微服务集成测试

```rust
#[cfg(test)]
mod microservice_integration_tests {
    use super::*;

    #[tokio::test]
    async fn test_intelligent_routing_integration() {
        let traffic_manager = Arc::new(TrafficManager::new());
        let load_balancer = Arc::new(RoundRobinLoadBalancer::new());
        let router = IntelligentRouter::new(traffic_manager, load_balancer);

        // 添加路由规则
        let rule = RoutingRule {
            name: "test-routing".to_string(),
            match_conditions: vec![
                MatchCondition::Path {
                    pattern: "/api/*".to_string(),
                },
            ],
            destination: Destination {
                service: "test-service".to_string(),
                namespace: "default".to_string(),
                subset: None,
                port: 8080,
            },
            weight: 100,
            timeout: Duration::from_secs(30),
            retry_policy: RetryPolicy::default(),
            circuit_breaker: CircuitBreakerPolicy::default(),
        };

        router.add_rule(rule).await.unwrap();

        // 测试路由
        let request = RouteRequest {
            method: "GET".to_string(),
            path: "/api/test".to_string(),
            headers: HashMap::new(),
            query_params: HashMap::new(),
            source_service: "test-client".to_string(),
            source_namespace: "default".to_string(),
            body: None,
        };

        let result = router.route_request(&request).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_adaptive_load_balancing_integration() {
        let adaptive_lb = AdaptiveLoadBalancer::new();

        let endpoints = vec![
            ServiceEndpoint {
                id: "instance-1".to_string(),
                address: "10.0.1.10".to_string(),
                port: 8080,
                weight: 100,
                metadata: HashMap::new(),
                health_status: MicroserviceHealthStatus::Healthy,
                last_health_check: std::time::Instant::now(),
            },
            ServiceEndpoint {
                id: "instance-2".to_string(),
                address: "10.0.1.11".to_string(),
                port: 8080,
                weight: 150,
                metadata: HashMap::new(),
                health_status: MicroserviceHealthStatus::Healthy,
                last_health_check: std::time::Instant::now(),
            },
        ];

        // 测试负载均衡
        for _ in 0..10 {
            let selected = adaptive_lb.select_endpoint(&endpoints).await;
            assert!(selected.is_some());

            // 记录结果
            adaptive_lb
                .record_request_result("test", true, Duration::from_millis(50))
                .await;
        }
    }
}
```

### 3. 性能测试 (Performance Tests)

#### 3.1 基准测试

```rust
#[cfg(test)]
mod benchmark_tests {
    use super::*;
    use criterion::{black_box, criterion_group, criterion_main, Criterion};

    fn benchmark_circuit_breaker_call(c: &mut Criterion) {
        let rt = tokio::runtime::Runtime::new().unwrap();

        c.bench_function("circuit_breaker_call", |b| {
            b.to_async(&rt).iter(|| async {
                let config = CircuitBreakerConfig::default();
                let cb = CircuitBreaker::new(config);

                cb.call(|| async { Ok::<(), anyhow::Error>(()) }).await
            })
        });
    }

    fn benchmark_batch_processing(c: &mut Criterion) {
        let rt = tokio::runtime::Runtime::new().unwrap();

        c.bench_function("batch_processing", |b| {
            b.to_async(&rt).iter(|| async {
                let processor = AsyncBatchProcessor::new(100, Duration::from_millis(100), 10);

                for i in 0..1000 {
                    processor.add_item(black_box(i)).await.unwrap();
                }

                while processor.get_next_batch().await.is_some() {
                    // 处理批次
                }
            })
        });
    }

    fn benchmark_memory_pool(c: &mut Criterion) {
        let rt = tokio::runtime::Runtime::new().unwrap();

        c.bench_function("memory_pool_acquire", |b| {
            b.to_async(&rt).iter(|| async {
                let pool = OptimizedObjectPool::new(|| String::with_capacity(1024), 100);
                let _obj = pool.acquire().await;
            })
        });
    }

    criterion_group!(benches, benchmark_circuit_breaker_call, benchmark_batch_processing, benchmark_memory_pool);
    criterion_main!(benches);
}
```

#### 3.2 压力测试

```rust
#[cfg(test)]
mod stress_tests {
    use super::*;

    #[tokio::test]
    async fn test_high_concurrency_circuit_breaker() {
        let config = CircuitBreakerConfig {
            failure_threshold: 10,
            recovery_timeout: Duration::from_millis(100),
            ..Default::default()
        };

        let cb = Arc::new(CircuitBreaker::new(config));

        // 并发执行1000个请求
        let handles: Vec<_> = (0..1000)
            .map(|i| {
                let cb = Arc::clone(&cb);
                tokio::spawn(async move {
                    cb.call(|| async {
                        if i % 10 == 0 {
                            Err::<(), anyhow::Error>(anyhow::anyhow!("test error"))
                        } else {
                            Ok(())
                        }
                    }).await
                })
            })
            .collect();

        let results = futures::future::join_all(handles).await;

        // 验证结果
        let success_count = results.iter().filter(|r| r.is_ok()).count();
        let failure_count = results.iter().filter(|r| r.is_err()).count();

        assert!(success_count > 0);
        assert!(failure_count > 0);
    }

    #[tokio::test]
    async fn test_memory_pool_under_load() {
        let pool = Arc::new(OptimizedObjectPool::new(|| String::with_capacity(1024), 100));

        // 并发获取和释放对象
        let handles: Vec<_> = (0..1000)
            .map(|_| {
                let pool = Arc::clone(&pool);
                tokio::spawn(async move {
                    let obj = pool.acquire().await;
                    // 模拟使用对象
                    tokio::time::sleep(Duration::from_millis(1)).await;
                    drop(obj);
                })
            })
            .collect();

        futures::future::join_all(handles).await;

        // 验证池状态
        let stats = pool.get_stats().await;
        assert!(stats.total_created <= 1000);
        assert!(stats.total_reused > 0);
    }
}
```

### 4. 端到端测试 (E2E Tests)

#### 4.1 完整流程测试

```rust
#[cfg(test)]
mod e2e_tests {
    use super::*;
    use testcontainers::*;
    use testcontainers::images::generic::GenericImage;

    #[tokio::test]
    async fn test_complete_telemetry_pipeline() {
        let docker = clients::Cli::default();
        let jaeger = docker.run(GenericImage::new("jaegertracing/all-in-one", "latest"));

        // 配置OTLP客户端
        let config = OtlpConfig::default()
            .with_endpoint(&format!("http://localhost:{}", jaeger.get_host_port_ipv4(14268)))
            .with_protocol(TransportProtocol::Grpc)
            .with_batch_size(10)
            .with_retry_config(RetryConfig {
                max_retries: 3,
                initial_retry_delay: Duration::from_millis(100),
                ..Default::default()
            });

        let client = OtlpClient::new(config).await.unwrap();
        client.initialize().await.unwrap();

        // 发送多种类型的遥测数据
        let mut handles = Vec::new();

        // 发送追踪数据
        for i in 0..10 {
            let client = client.clone();
            let handle = tokio::spawn(async move {
                let trace = client.send_trace(&format!("operation-{}", i)).await.unwrap();
                trace
                    .with_attribute("iteration", i.to_string())
                    .with_duration(100 + i * 10)
                    .finish()
                    .await
            });
            handles.push(handle);
        }

        // 发送指标数据
        for i in 0..5 {
            let client = client.clone();
            let handle = tokio::spawn(async move {
                let metric = client.send_metric(&format!("metric-{}", i), i as f64).await.unwrap();
                metric
                    .with_label("type", "counter")
                    .with_description(&format!("Test metric {}", i))
                    .send()
                    .await
            });
            handles.push(handle);
        }

        // 发送日志数据
        for i in 0..5 {
            let client = client.clone();
            let handle = tokio::spawn(async move {
                let log = client.send_log(&format!("Log message {}", i), LogSeverity::Info).await.unwrap();
                log
                    .with_attribute("source", "e2e-test")
                    .with_attribute("iteration", i.to_string())
                    .send()
                    .await
            });
            handles.push(handle);
        }

        // 等待所有操作完成
        let results = futures::future::join_all(handles).await;

        // 验证结果
        let mut success_count = 0;
        let mut failure_count = 0;

        for result in results {
            match result {
                Ok(Ok(export_result)) => {
                    success_count += export_result.success_count;
                }
                Ok(Err(e)) => {
                    eprintln!("Export failed: {}", e);
                    failure_count += 1;
                }
                Err(e) => {
                    eprintln!("Task failed: {}", e);
                    failure_count += 1;
                }
            }
        }

        // 验证大部分操作成功
        assert!(success_count > 0);
        assert!(failure_count < 5); // 允许少量失败

        // 关闭客户端
        client.shutdown().await.unwrap();
    }
}
```

## 📊 测试覆盖率目标

### 覆盖率指标

| 模块 | 当前覆盖率 | 目标覆盖率 | 优先级 |
|------|------------|------------|--------|
| 核心客户端 | 85% | 95% | 高 |
| 错误处理 | 90% | 98% | 高 |
| 配置管理 | 80% | 95% | 高 |
| 传输层 | 75% | 90% | 中 |
| 处理器 | 70% | 85% | 中 |
| 工具模块 | 60% | 80% | 低 |

### 测试类型分布

| 测试类型 | 数量 | 占比 | 执行时间 |
|----------|------|------|----------|
| 单元测试 | 200+ | 70% | <1分钟 |
| 集成测试 | 50+ | 20% | 5-10分钟 |
| 性能测试 | 20+ | 5% | 10-15分钟 |
| 端到端测试 | 10+ | 5% | 15-30分钟 |

## 🛠️ 测试工具和框架

### 测试框架

```toml
[dev-dependencies]
# 基础测试框架
tokio-test = "0.4"
tokio = { version = "1.0", features = ["full"] }

# 模拟和测试工具
mockall = "0.12"
testcontainers = "0.15"
criterion = "0.5"

# 断言和测试工具
proptest = "1.0"
quickcheck = "1.0"
rstest = "0.18"

# 测试覆盖率
cargo-tarpaulin = "0.27"
```

### 测试配置

```rust
// 测试配置
#[cfg(test)]
mod test_config {
    use super::*;

    pub fn test_otlp_config() -> OtlpConfig {
        OtlpConfig::default()
            .with_endpoint("http://localhost:4317")
            .with_protocol(TransportProtocol::Grpc)
            .with_batch_size(10)
            .with_timeout(Duration::from_secs(5))
    }

    pub fn test_resilience_config() -> ResilienceConfig {
        ResilienceConfig {
            retry: RetryConfig {
                max_attempts: 3,
                base_delay: Duration::from_millis(10),
                max_delay: Duration::from_millis(100),
                backoff_multiplier: 2.0,
                jitter: true,
                retryable_errors: vec!["timeout".to_string(), "connection_failed".to_string()],
            },
            circuit_breaker: CircuitBreakerConfig {
                failure_threshold: 5,
                recovery_timeout: Duration::from_millis(100),
                half_open_max_calls: 3,
                sliding_window_size: Duration::from_secs(60),
                minimum_calls: 10,
            },
            timeout: TimeoutConfig {
                connect_timeout: Duration::from_millis(100),
                read_timeout: Duration::from_millis(100),
                write_timeout: Duration::from_millis(100),
                operation_timeout: Duration::from_millis(100),
            },
            graceful_degradation: GracefulDegradationConfig::default(),
            health_check: HealthCheckConfig::default(),
        }
    }
}
```

## 🚀 持续集成配置

### GitHub Actions

```yaml
name: OTLP Rust Tests

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main ]

jobs:
  test:
    runs-on: ubuntu-latest

    steps:
    - uses: actions/checkout@v3

    - name: Install Rust
      uses: actions-rs/toolchain@v1
      with:
        toolchain: 1.90
        components: rustfmt, clippy

    - name: Cache dependencies
      uses: actions/cache@v3
      with:
        path: |
          ~/.cargo/registry
          ~/.cargo/git
          target
        key: ${{ runner.os }}-cargo-${{ hashFiles('**/Cargo.lock') }}

    - name: Run unit tests
      run: cargo test --lib

    - name: Run integration tests
      run: cargo test --test integration_tests

    - name: Run performance tests
      run: cargo bench

    - name: Generate coverage report
      run: |
        cargo install cargo-tarpaulin
        cargo tarpaulin --out Html --output-dir coverage

    - name: Upload coverage
      uses: codecov/codecov-action@v3
      with:
        file: coverage/tarpaulin-report.html
```

## 📈 测试质量监控

### 质量指标

| 指标 | 目标值 | 监控方式 |
|------|--------|----------|
| 测试覆盖率 | >95% | cargo-tarpaulin |
| 测试通过率 | 100% | CI/CD |
| 测试执行时间 | <30分钟 | CI/CD |
| 性能回归 | <5% | 基准测试 |
| 内存泄漏 | 0 | Valgrind/AddressSanitizer |

### 测试报告

```rust
// 测试报告生成
#[cfg(test)]
mod test_reporting {
    use super::*;

    #[tokio::test]
    async fn generate_test_report() {
        let report = TestReport::new()
            .with_coverage(95.5)
            .with_unit_tests(200)
            .with_integration_tests(50)
            .with_performance_tests(20)
            .with_e2e_tests(10)
            .with_execution_time(Duration::from_secs(1200))
            .generate();

        println!("{}", report);
    }
}
```

---

**测试负责人**: OTLP Rust 团队
**预计完成时间**: 2025年3月
**状态**: 🚀 进行中
