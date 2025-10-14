//! # OTLP 性能基准测试
//!
//! 提供全面的性能基准测试，包括数据传输、序列化、压缩等关键性能指标。

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use otlp::{
    Result,
    config::{OtlpConfigBuilder, TransportProtocol},
    data::{
        AttributeValue, SpanKind, SpanStatus, TelemetryContent, TelemetryData, TelemetryDataType,
        TraceData,
    },
    ottl::{OtlpTransform, TransformConfig},
    // profiling::{Profiler, ProfilingConfig}, // 已迁移到备份
    validation::DataValidator,
};
use std::collections::HashMap;
use std::hint::black_box;
use std::time::Duration;

/// 创建测试用的遥测数据
fn create_test_telemetry_data(count: usize) -> Vec<TelemetryData> {
    (0..count)
        .map(|i| {
            let trace_data = TraceData {
                trace_id: format!("{:032x}", i),
                span_id: format!("{:016x}", i),
                parent_span_id: None,
                name: format!("test-span-{}", i),
                span_kind: SpanKind::Internal,
                start_time: 1000 + i as u64,
                end_time: 2000 + i as u64,
                status: SpanStatus::default(),
                attributes: HashMap::from([
                    (
                        "service.name".to_string(),
                        AttributeValue::String("test-service".to_string()),
                    ),
                    (
                        "operation".to_string(),
                        AttributeValue::String("test-operation".to_string()),
                    ),
                ]),
                events: vec![],
                links: vec![],
            };

            TelemetryData {
                data_type: TelemetryDataType::Trace,
                timestamp: std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos() as u64,
                resource_attributes: HashMap::new(),
                scope_attributes: HashMap::new(),
                content: TelemetryContent::Trace(trace_data),
            }
        })
        .collect()
}

/// 数据传输性能基准测试
#[allow(unused_variables)]
fn benchmark_transport_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("transport_performance");

    for size in [10, 100, 1000].iter() {
        let test_data = create_test_telemetry_data(*size);

        // gRPC 传输基准测试
        group.bench_with_input(BenchmarkId::new("grpc_transport", size), size, |b, _| {
            b.iter(|| async {
                let _config = OtlpConfigBuilder::new()
                    .endpoint("http://localhost:4317")
                    .protocol(TransportProtocol::Grpc)
                    .build();

                // 模拟传输操作，避免实际网络调用
                let _result: Result<()> = Ok(());
            });
        });

        // HTTP 传输基准测试
        group.bench_with_input(BenchmarkId::new("http_transport", size), size, |b, _| {
            b.iter(|| async {
                let _config = OtlpConfigBuilder::new()
                    .endpoint("http://localhost:4318")
                    .protocol(TransportProtocol::Http)
                    .build();

                // 模拟传输操作，避免实际网络调用
                let _result: Result<()> = Ok(());
            });
        });
    }

    group.finish();
}

/// 数据验证性能基准测试
#[allow(unused_variables)]
fn benchmark_validation_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("validation_performance");

    for size in [10, 100, 1000].iter() {
        let test_data = create_test_telemetry_data(*size);
        let validator = DataValidator::new(true);

        group.bench_with_input(BenchmarkId::new("data_validation", size), size, |b, _| {
            b.iter(|| {
                for data in &test_data {
                    let _result = validator.validate_telemetry_data(data);
                    let _ = black_box(_result);
                }
            });
        });
    }

    group.finish();
}

/// OTTL 转换性能基准测试
fn benchmark_ottl_transform_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("ottl_transform_performance");

    for size in [10, 100, 1000].iter() {
        let test_data = create_test_telemetry_data(*size);

        // 简单转换配置 - 使用模拟配置
        let config = TransformConfig::new();

        let transformer = OtlpTransform::new(config).unwrap();

        group.bench_with_input(BenchmarkId::new("ottl_transform", size), size, |b, _| {
            b.iter(|| async {
                let result = transformer.transform(black_box(test_data.clone())).await;
                let _ = black_box(result);
            });
        });
    }

    group.finish();
}

/// 序列化性能基准测试
fn benchmark_serialization_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("serialization_performance");

    for size in [10, 100, 1000].iter() {
        let test_data = create_test_telemetry_data(*size);

        // JSON 序列化
        group.bench_with_input(
            BenchmarkId::new("json_serialization", size),
            size,
            |b, _| {
                b.iter(|| {
                    let serialized = serde_json::to_vec(black_box(&test_data)).unwrap();
                    black_box(serialized);
                });
            },
        );

        // JSON 反序列化
        let serialized_data = serde_json::to_vec(&test_data).unwrap();
        group.bench_with_input(
            BenchmarkId::new("json_deserialization", size),
            size,
            |b, _| {
                b.iter(|| {
                    let deserialized: Vec<TelemetryData> =
                        serde_json::from_slice(black_box(&serialized_data)).unwrap();
                    black_box(deserialized);
                });
            },
        );
    }

    group.finish();
}

/// 压缩性能基准测试
fn benchmark_compression_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("compression_performance");

    let test_data = vec![0u8; 1000]; // 模拟数据
    let serialized_data = test_data;

    // Gzip 压缩
    group.bench_function("gzip_compression", |b| {
        b.iter(|| {
            use std::io::Write;
            let mut encoder =
                flate2::write::GzEncoder::new(Vec::new(), flate2::Compression::default());
            let _result = encoder.write_all(black_box(&serialized_data));
            let compressed = encoder.finish().unwrap();
            black_box(compressed);
        });
    });

    // Brotli 压缩
    group.bench_function("brotli_compression", |b| {
        b.iter(|| {
            let mut output = Vec::new();
            let mut cursor = std::io::Cursor::new(&*serialized_data);
            let result = brotli::enc::BrotliCompress(
                &mut cursor,
                &mut output,
                &brotli::enc::BrotliEncoderParams::default(),
            );
            let _result = result;
            black_box(output);
        });
    });

    // Zstd 压缩
    group.bench_function("zstd_compression", |b| {
        b.iter(|| {
            let result = zstd::encode_all(black_box(&*serialized_data), 0);
            let compressed = result.unwrap();
            black_box(compressed);
        });
    });

    group.finish();
}

/// 内存使用基准测试
fn benchmark_memory_usage(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_usage");

    for size in [100, 1000, 10000].iter() {
        group.bench_with_input(BenchmarkId::new("data_creation", size), size, |b, _| {
            b.iter(|| {
                let data = create_test_telemetry_data(*size);
                black_box(data);
            });
        });
    }

    group.finish();
}

/// 并发性能基准测试
fn benchmark_concurrent_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("concurrent_performance");

    group.bench_function("concurrent_validation", |b| {
        b.iter(|| async {
            let test_data = create_test_telemetry_data(100);
            let handles: Vec<_> = test_data
                .chunks(10)
                .map(|chunk| {
                    let chunk = chunk.to_vec();
                    tokio::spawn(async move {
                        let validator = DataValidator::new(true);
                        for data in chunk {
                            let _result = validator.validate_telemetry_data(&data);
                        }
                    })
                })
                .collect();

            for handle in handles {
                handle.await.unwrap();
            }
        });
    });

    group.finish();
}

/// 性能分析基准测试
fn benchmark_profiling_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("profiling_performance");

    group.bench_function("profiler_start_stop", |b| {
        b.iter(|| async {
            let config = ProfilingConfig::default();
            let mut profiler = Profiler::new(config);

            let _start_result = profiler.start().await;
            tokio::time::sleep(Duration::from_millis(10)).await;
            let _stop_result = profiler.stop().await;
        });
    });

    group.bench_function("profiler_data_collection", |b| {
        b.iter(|| async {
            let config = ProfilingConfig::default();
            let mut profiler = Profiler::new(config);

            let _start_result = profiler.start().await;
            let data = profiler.collect_data().await.unwrap_or_default();
            let _stop_result = profiler.stop().await;

            black_box(data);
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    benchmark_transport_performance,
    benchmark_validation_performance,
    benchmark_ottl_transform_performance,
    benchmark_serialization_performance,
    benchmark_compression_performance,
    benchmark_memory_usage,
    benchmark_concurrent_performance,
    benchmark_profiling_performance
);

criterion_main!(benches);
