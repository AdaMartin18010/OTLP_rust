//! eBPF 性能基准测试
//!
//! 测试 eBPF 模块的性能特征

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use otlp::ebpf::{EbpfConfig, EbpfLoader, validate_config, recommended_sample_rate};
use std::time::Duration;

fn bench_ebpf_config_creation(c: &mut Criterion) {
    c.bench_function("ebpf_config_creation", |b| {
        b.iter(|| {
            black_box(EbpfConfig::default());
        });
    });
}

fn bench_ebpf_config_validation(c: &mut Criterion) {
    let config = EbpfConfig::default();
    c.bench_function("ebpf_config_validation", |b| {
        b.iter(|| {
            black_box(validate_config(black_box(&config))).unwrap();
        });
    });
}

fn bench_ebpf_config_builder(c: &mut Criterion) {
    c.bench_function("ebpf_config_builder", |b| {
        b.iter(|| {
            black_box(
                EbpfConfig::default()
                    .with_sample_rate(99)
                    .with_cpu_profiling(true)
                    .with_network_tracing(true)
            );
        });
    });
}

fn bench_recommended_sample_rate(c: &mut Criterion) {
    let envs = ["production", "staging", "development", "debug"];
    c.bench_function("recommended_sample_rate", |b| {
        b.iter(|| {
            for env in &envs {
                black_box(recommended_sample_rate(black_box(env)));
            }
        });
    });
}

fn bench_ebpf_loader_new(c: &mut Criterion) {
    let config = EbpfConfig::default();
    c.bench_function("ebpf_loader_new", |b| {
        b.iter(|| {
            black_box(EbpfLoader::new(black_box(config.clone())));
        });
    });
}

criterion_group!(
    benches,
    bench_ebpf_config_creation,
    bench_ebpf_config_validation,
    bench_ebpf_config_builder,
    bench_recommended_sample_rate,
    bench_ebpf_loader_new
);
criterion_main!(benches);
