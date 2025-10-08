//! # 综合性能基准测试
//!
//! 本模块提供全面的性能基准测试，涵盖各种实际应用场景和压力测试。

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main, Throughput};
use otlp::{
    OtlpClient, OtlpConfig, TelemetryData,
    config::TransportProtocol,
    data::{LogSeverity, StatusCode},
};
use std::hint::black_box;
use std::sync::Arc;
use std::time::Duration;
use tokio::runtime::Runtime;

/// 创建测试运行时
fn create_runtime() -> Runtime {
    tokio::runtime::Builder::new_multi_thread()
        .worker_threads(4)
        .enable_all()
        .build()
        .unwrap()
}

/// 创建测试客户端
fn create_test_client(protocol: TransportProtocol) -> OtlpClient {
    let rt = Runtime::new().unwrap();
    let endpoint = match protocol {
        TransportProtocol::Grpc => "http://localhost:4317",
        TransportProtocol::Http => "http://localhost:4318",
        TransportProtocol::HttpProtobuf => "http://localhost:4318",
    };

    let config = OtlpConfig::default()
        .with_endpoint(endpoint)
        .with_protocol(protocol)
        .with_service("benchmark-service", "1.0.0")
        .with_request_timeout(Duration::from_secs(30));

    rt.block_on(async {
        let client = OtlpClient::new(config).await.unwrap();
        let _ = client.initialize().await;
        client
    })
}

/// 创建不同大小的测试数据
fn create_variable_size_trace_data(size: usize, attributes_count: usize) -> Vec<TelemetryData> {
    (0..size)
        .map(|i| {
            let mut data = TelemetryData::trace(format!("benchmark-operation-{}", i))
                .with_attribute("service.name", "benchmark-service")
                .with_status(StatusCode::Ok, Some("success".to_string()));

            // 添加可变数量的属性以模拟不同大小的数据
            for j in 0..attributes_count {
                data = data
                    .with_attribute(format!("attr-{}", j), format!("value-{}", j))
                    .with_numeric_attribute(format!("metric-{}", j), (i * j) as f64);
            }

            data
        })
        .collect()
}

/// 基准测试：端到端 Web 应用场景
fn benchmark_e2e_web_application(c: &mut Criterion) {
    let mut group = c.benchmark_group("e2e_web_application");
    let client = create_test_client(TransportProtocol::Http);
    let rt = create_runtime();

    // 模拟 Web 应用请求处理流程
    group.bench_function("http_request_processing", |b| {
        b.iter(|| {
            rt.block_on(async {
                // 1. 接收 HTTP 请求
                let request_span = client
                    .send_trace("http_request")
                    .await
                    .unwrap()
                    .with_attribute("http.method", "GET")
                    .with_attribute("http.url", "/api/users")
                    .with_attribute("http.status_code", "200")
                    .with_numeric_attribute("http.request_size", 1024.0)
                    .with_numeric_attribute("http.response_size", 2048.0);

                // 2. 数据库查询
                let db_span = client
                    .send_trace("database_query")
                    .await
                    .unwrap()
                    .with_attribute("db.system", "postgresql")
                    .with_attribute("db.statement", "SELECT * FROM users")
                    .with_numeric_attribute("db.rows", 10.0);

                // 3. 缓存访问
                let cache_span = client
                    .send_trace("cache_access")
                    .await
                    .unwrap()
                    .with_attribute("cache.system", "redis")
                    .with_attribute("cache.operation", "GET")
                    .with_bool_attribute("cache.hit", true);

                // 4. 发送指标
                let latency_metric = client
                    .send_metric("http_request_duration", 45.0)
                    .await
                    .unwrap()
                    .with_label("endpoint", "/api/users");

                // 完成所有 span
                let _ = request_span.finish().await;
                let _ = db_span.finish().await;
                let _ = cache_span.finish().await;
                let _ = latency_metric.send().await;

                black_box(())
            })
        })
    });

    group.finish();
}

/// 基准测试：微服务通信场景
fn benchmark_microservices_communication(c: &mut Criterion) {
    let mut group = c.benchmark_group("microservices_communication");
    let client = Arc::new(create_test_client(TransportProtocol::Grpc));
    let rt = create_runtime();

    group.bench_function("service_to_service_call", |b| {
        b.iter(|| {
            rt.block_on(async {
                // 服务 A 调用服务 B
                let service_a_span = client
                    .send_trace("service_a_processing")
                    .await
                    .unwrap()
                    .with_attribute("service.name", "service-a")
                    .with_attribute("service.version", "1.0.0");

                let service_b_span = client
                    .send_trace("service_b_processing")
                    .await
                    .unwrap()
                    .with_attribute("service.name", "service-b")
                    .with_attribute("service.version", "1.0.0")
                    .with_attribute("parent.service", "service-a");

                // 服务 B 调用服务 C
                let service_c_span = client
                    .send_trace("service_c_processing")
                    .await
                    .unwrap()
                    .with_attribute("service.name", "service-c")
                    .with_attribute("service.version", "1.0.0")
                    .with_attribute("parent.service", "service-b");

                // 完成所有 span
                let _ = service_c_span.finish().await;
                let _ = service_b_span.finish().await;
                let _ = service_a_span.finish().await;

                black_box(())
            })
        })
    });

    group.finish();
}

/// 基准测试：批处理任务场景
fn benchmark_batch_processing(c: &mut Criterion) {
    let mut group = c.benchmark_group("batch_processing");
    let client = create_test_client(TransportProtocol::Http);
    let rt = create_runtime();

    for batch_size in [100, 500, 1000, 5000].iter() {
        group.throughput(Throughput::Elements(*batch_size as u64));
        
        group.bench_with_input(
            BenchmarkId::new("batch_job", batch_size),
            batch_size,
            |b, &batch_size| {
                let data = create_variable_size_trace_data(batch_size, 5);
                
                b.iter(|| {
                    rt.block_on(async {
                        let result = client.send_batch(black_box(data.clone())).await;
                        black_box(result)
                    })
                })
            },
        );
    }

    group.finish();
}

/// 基准测试：高并发场景
fn benchmark_high_concurrency(c: &mut Criterion) {
    let mut group = c.benchmark_group("high_concurrency");
    let client = Arc::new(create_test_client(TransportProtocol::Http));
    let rt = create_runtime();

    for concurrency in [10, 50, 100, 200, 500].iter() {
        group.bench_with_input(
            BenchmarkId::new("concurrent_requests", concurrency),
            concurrency,
            |b, &concurrency| {
                b.iter(|| {
                    rt.block_on(async {
                        let handles: Vec<_> = (0..concurrency)
                            .map(|i| {
                                let client = client.clone();
                                tokio::spawn(async move {
                                    client
                                        .send_trace(format!("concurrent-operation-{}", i))
                                        .await
                                        .unwrap()
                                        .with_attribute("worker.id", i.to_string())
                                        .with_numeric_attribute("worker.index", i as f64)
                                        .finish()
                                        .await
                                })
                            })
                            .collect();

                        for handle in handles {
                            let _ = handle.await;
                        }

                        black_box(())
                    })
                })
            },
        );
    }

    group.finish();
}

/// 基准测试：压力测试 - 持续负载
fn benchmark_sustained_load(c: &mut Criterion) {
    let mut group = c.benchmark_group("sustained_load");
    group.sample_size(20); // 减少采样以缩短测试时间
    group.measurement_time(Duration::from_secs(10));

    let client = Arc::new(create_test_client(TransportProtocol::Http));
    let rt = create_runtime();

    group.bench_function("continuous_load_1min", |b| {
        b.iter(|| {
            rt.block_on(async {
                let start = std::time::Instant::now();
                let mut count = 0;

                // 持续发送 10 秒
                while start.elapsed() < Duration::from_secs(10) {
                    let _ = client
                        .send_trace(format!("sustained-{}", count))
                        .await
                        .unwrap()
                        .with_numeric_attribute("iteration", count as f64)
                        .finish()
                        .await;
                    
                    count += 1;
                }

                black_box(count)
            })
        })
    });

    group.finish();
}

/// 基准测试：不同数据大小性能
fn benchmark_data_size_variations(c: &mut Criterion) {
    let mut group = c.benchmark_group("data_size_variations");
    let client = create_test_client(TransportProtocol::Http);
    let rt = create_runtime();

    // 测试不同属性数量（模拟不同数据大小）
    for attr_count in [1, 5, 10, 20, 50].iter() {
        let data = create_variable_size_trace_data(100, *attr_count);
        
        group.bench_with_input(
            BenchmarkId::new("attributes", attr_count),
            attr_count,
            |b, _| {
                b.iter(|| {
                    rt.block_on(async {
                        let result = client.send_batch(black_box(data.clone())).await;
                        black_box(result)
                    })
                })
            },
        );
    }

    group.finish();
}

/// 基准测试：混合遥测数据类型
fn benchmark_mixed_telemetry_types(c: &mut Criterion) {
    let mut group = c.benchmark_group("mixed_telemetry_types");
    let client = create_test_client(TransportProtocol::Http);
    let rt = create_runtime();

    group.bench_function("mixed_traces_metrics_logs", |b| {
        b.iter(|| {
            rt.block_on(async {
                // 发送追踪
                let trace = client
                    .send_trace("mixed-operation")
                    .await
                    .unwrap()
                    .with_attribute("operation.type", "mixed")
                    .finish()
                    .await;

                // 发送指标
                let metric = client
                    .send_metric("operation_count", 1.0)
                    .await
                    .unwrap()
                    .with_label("operation.type", "mixed")
                    .send()
                    .await;

                // 发送日志
                let log = client
                    .send_log("Mixed operation completed", LogSeverity::Info)
                    .await
                    .unwrap()
                    .with_attribute("operation.type", "mixed")
                    .send()
                    .await;

                black_box((trace, metric, log))
            })
        })
    });

    group.finish();
}

/// 基准测试：错误处理和重试场景
fn benchmark_error_handling(c: &mut Criterion) {
    let mut group = c.benchmark_group("error_handling");
    let rt = create_runtime();

    group.bench_function("invalid_config_handling", |b| {
        b.iter(|| {
            rt.block_on(async {
                // 测试无效配置的错误处理性能
                let invalid_config = OtlpConfig::default()
                    .with_endpoint("") // 无效端点
                    .with_protocol(TransportProtocol::Http);

                let result = invalid_config.validate();
                black_box(result)
            })
        })
    });

    group.bench_function("network_timeout_handling", |b| {
        b.iter(|| {
            rt.block_on(async {
                // 测试超时配置的性能开销
                let config = OtlpConfig::default()
                    .with_endpoint("http://localhost:4318")
                    .with_protocol(TransportProtocol::Http)
                    .with_request_timeout(Duration::from_millis(100)); // 短超时

                let client = OtlpClient::new(config).await;
                black_box(client)
            })
        })
    });

    group.finish();
}

/// 基准测试：内存使用模式
fn benchmark_memory_patterns(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_patterns");
    let client = create_test_client(TransportProtocol::Http);
    let rt = create_runtime();

    // 测试内存分配和释放模式
    for count in [10, 100, 1000].iter() {
        group.bench_with_input(
            BenchmarkId::new("memory_allocation", count),
            count,
            |b, &count| {
                b.iter(|| {
                    // 创建大量临时对象测试内存性能
                    let data = create_variable_size_trace_data(count, 10);
                    
                    rt.block_on(async {
                        let result = client.send_batch(black_box(data)).await;
                        black_box(result)
                    })
                    
                    // 数据在此处被释放
                })
            },
        );
    }

    group.finish();
}

/// 基准测试：CPU 密集型场景
fn benchmark_cpu_intensive(c: &mut Criterion) {
    let mut group = c.benchmark_group("cpu_intensive");

    group.bench_function("data_serialization_cpu", |b| {
        let data = create_variable_size_trace_data(1000, 20);
        
        b.iter(|| {
            // JSON 序列化（CPU 密集型）
            let serialized = serde_json::to_vec(&data).unwrap();
            
            // JSON 反序列化（CPU 密集型）
            let deserialized: Vec<TelemetryData> = 
                serde_json::from_slice(&serialized).unwrap();
            
            black_box(deserialized)
        })
    });

    group.bench_function("data_compression_cpu", |b| {
        let data = vec![0u8; 10000]; // 10KB 数据
        
        b.iter(|| {
            use std::io::Write;
            
            // Gzip 压缩（CPU 密集型）
            let mut encoder = flate2::write::GzEncoder::new(
                Vec::new(),
                flate2::Compression::default()
            );
            encoder.write_all(&data).unwrap();
            let compressed = encoder.finish().unwrap();
            
            black_box(compressed)
        })
    });

    group.finish();
}

/// 基准测试：网络 I/O 场景
fn benchmark_network_io(c: &mut Criterion) {
    let mut group = c.benchmark_group("network_io");
    let rt = create_runtime();

    // HTTP 协议性能
    group.bench_function("http_protocol_overhead", |b| {
        let client = create_test_client(TransportProtocol::Http);
        let data = create_variable_size_trace_data(10, 5);
        
        b.iter(|| {
            rt.block_on(async {
                let result = client.send_batch(black_box(data.clone())).await;
                black_box(result)
            })
        })
    });

    // gRPC 协议性能
    group.bench_function("grpc_protocol_overhead", |b| {
        let client = create_test_client(TransportProtocol::Grpc);
        let data = create_variable_size_trace_data(10, 5);
        
        b.iter(|| {
            rt.block_on(async {
                let result = client.send_batch(black_box(data.clone())).await;
                black_box(result)
            })
        })
    });

    group.finish();
}

/// 基准测试：实际生产负载模拟
fn benchmark_production_workload(c: &mut Criterion) {
    let mut group = c.benchmark_group("production_workload");
    group.sample_size(20);
    group.measurement_time(Duration::from_secs(10));

    let client = Arc::new(create_test_client(TransportProtocol::Http));
    let rt = create_runtime();

    group.bench_function("realistic_production_load", |b| {
        b.iter(|| {
            rt.block_on(async {
                // 模拟真实生产环境的混合负载
                let handles: Vec<_> = (0..50)
                    .map(|i| {
                        let client = client.clone();
                        tokio::spawn(async move {
                            // 70% 追踪
                            if i % 10 < 7 {
                                let _ = client
                                    .send_trace(format!("prod-trace-{}", i))
                                    .await
                                    .unwrap()
                                    .with_attribute("environment", "production")
                                    .with_numeric_attribute("worker", i as f64)
                                    .finish()
                                    .await;
                            }
                            // 20% 指标
                            else if i % 10 < 9 {
                                let _ = client
                                    .send_metric("prod_metric", i as f64)
                                    .await
                                    .unwrap()
                                    .with_label("environment", "production")
                                    .send()
                                    .await;
                            }
                            // 10% 日志
                            else {
                                let _ = client
                                    .send_log("Production log message", LogSeverity::Info)
                                    .await
                                    .unwrap()
                                    .with_attribute("environment", "production")
                                    .send()
                                    .await;
                            }
                        })
                    })
                    .collect();

                for handle in handles {
                    let _ = handle.await;
                }

                black_box(())
            })
        })
    });

    group.finish();
}

criterion_group!(
    comprehensive_benches,
    benchmark_e2e_web_application,
    benchmark_microservices_communication,
    benchmark_batch_processing,
    benchmark_high_concurrency,
    benchmark_sustained_load,
    benchmark_data_size_variations,
    benchmark_mixed_telemetry_types,
    benchmark_error_handling,
    benchmark_memory_patterns,
    benchmark_cpu_intensive,
    benchmark_network_io,
    benchmark_production_workload
);

criterion_main!(comprehensive_benches);

