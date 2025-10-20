//! 简化的基准测试
//!
//! 测试核心OTLP功能的性能

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use otlp::{
    client::OtlpClientBuilder,
    config::{OtlpConfig, TransportProtocol},
    data::{AttributeValue, SpanKind, SpanStatus, TelemetryData, TraceData},
};
use std::collections::HashMap;
use std::hint::black_box;

/// 创建测试用的遥测数据
#[allow(unused_variables)]
fn create_test_telemetry_data(count: usize) -> Vec<TelemetryData> {
    (0..count)
        .map(|i| {
            let trace_data = TraceData {
                trace_id: format!("{:032x}", i),
                span_id: format!("{:016x}", i),
                parent_span_id: None,
                name: format!("test-span-{}", i),
                span_kind: SpanKind::Internal,
                start_time: 0,
                end_time: 1000000,
                status: SpanStatus::default(),
                attributes: {
                    let mut attrs = HashMap::new();
                    attrs.insert(
                        "service.name".to_string(),
                        AttributeValue::String("test-service".to_string()),
                    );
                    attrs.insert(
                        "operation".to_string(),
                        AttributeValue::String(format!("operation-{}", i)),
                    );
                    attrs
                },
                events: vec![],
                links: vec![],
            };

            TelemetryData::trace(format!("test-span-{}", i))
        })
        .collect()
}

/// 基准测试：客户端创建性能
#[allow(unused_variables)]
fn bench_client_creation(c: &mut Criterion) {
    let mut group = c.benchmark_group("client_creation");

    group.bench_function("create_client", |b| {
        b.iter(|| {
            let config = OtlpConfig::default()
                .with_endpoint("http://localhost:4317")
                .with_protocol(TransportProtocol::Http);

            black_box(OtlpClientBuilder::new())
        });
    });

    group.finish();
}

/// 基准测试：数据序列化性能
#[allow(unused_variables)]
fn bench_data_serialization(c: &mut Criterion) {
    let mut group = c.benchmark_group("data_serialization");

    let test_data = create_test_telemetry_data(1000);

    group.bench_with_input(
        BenchmarkId::new("serialize", 1000),
        &test_data,
        |b, data| {
            b.iter(|| {
                for item in data {
                    black_box(serde_json::to_string(item).unwrap());
                }
            });
        },
    );

    group.finish();
}

/// 基准测试：数据处理性能
fn bench_data_processing(c: &mut Criterion) {
    let mut group = c.benchmark_group("data_processing");

    let test_data = create_test_telemetry_data(10000);

    group.bench_with_input(BenchmarkId::new("process", 10000), &test_data, |b, data| {
        b.iter(|| {
            let mut processed = 0;
            for item in data {
                match item {
                    _ => {
                        processed += 1;
                    }
                }
            }
            black_box(processed);
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_client_creation,
    bench_data_serialization,
    bench_data_processing
);
criterion_main!(benches);
