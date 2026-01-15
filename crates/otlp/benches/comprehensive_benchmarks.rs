//! 综合性能基准测试
//!
//! 测试 OTLP 模块的整体性能特征

use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;

// 性能模块基准测试
mod performance_benchmarks {
    use super::*;
    use otlp::performance::{QuickOptimizationsConfig, QuickOptimizationsManager};

    pub fn compression_benchmark(c: &mut Criterion) {
        // 注意: 压缩是异步的，基准测试中无法使用异步操作
        // 这里仅创建管理器作为占位符
        c.bench_function("compression_manager_creation", |b| {
            b.iter(|| {
                let config = QuickOptimizationsConfig::default();
                black_box(QuickOptimizationsManager::new(config));
            });
        });
    }

    pub fn decompression_benchmark(c: &mut Criterion) {
        // 注意: 解压缩是异步的，基准测试中无法使用异步操作
        // 这里仅创建管理器作为占位符
        c.bench_function("decompression_manager_creation", |b| {
            b.iter(|| {
                let config = QuickOptimizationsConfig::default();
                black_box(QuickOptimizationsManager::new(config));
            });
        });
    }
}

// Profiling模块基准测试
mod profiling_benchmarks {
    use super::*;
    use otlp::profiling::{PprofProfile, Sample, PprofEncoder};

    pub fn profile_creation_benchmark(c: &mut Criterion) {
        c.bench_function("profile_creation", |b| {
            b.iter(|| {
                black_box(PprofProfile::new());
            });
        });
    }

    pub fn profile_add_sample_benchmark(c: &mut Criterion) {
        c.bench_function("profile_add_sample", |b| {
            b.iter(|| {
                let mut profile = PprofProfile::new();
                let sample = Sample {
                    location_id: vec![1u64, 2, 3],
                    value: vec![100i64, 200, 300],
                    label: vec![],
                };
                profile.sample.push(sample);
                black_box(&profile);
            });
        });
    }

    pub fn profile_encode_json_benchmark(c: &mut Criterion) {
        let mut profile = PprofProfile::new();

        // 添加一些样本
        for i in 0..100 {
            let sample = Sample {
                location_id: vec![i as u64, (i + 1) as u64],
                value: vec![(i * 10) as i64, ((i + 1) * 10) as i64],
                label: vec![],
            };
            profile.sample.push(sample);
        }

        c.bench_function("profile_encode_json", |b| {
            b.iter(|| {
                let _ = black_box(PprofEncoder::encode_json(&profile));
            });
        });
    }
}

// eBPF模块基准测试
#[cfg(all(feature = "ebpf", target_os = "linux"))]
mod ebpf_benchmarks {
    use super::*;
    use otlp::ebpf::{EbpfConfig, EbpfLoader, ProbeManager, MapsManager, EventProcessor, EbpfEvent, EbpfEventType, MapType};

    pub fn probe_attach_detach_benchmark(c: &mut Criterion) {
        let mut group = c.benchmark_group("probe_operations");

        group.bench_function("attach_kprobe", |b| {
            b.iter(|| {
                let mut manager = ProbeManager::new();
                let _ = black_box(manager.attach_kprobe("test", "func", None));
            });
        });

        group.bench_function("detach_kprobe", |b| {
            b.iter(|| {
                let mut manager = ProbeManager::new();
                let _ = manager.attach_kprobe("test", "func", None);
                let _ = black_box(manager.detach("test"));
            });
        });

        group.finish();
    }

    pub fn map_operations_benchmark(c: &mut Criterion) {
        let mut manager = MapsManager::new();
        let _ = manager.register_map("test_map".to_string(), MapType::Hash, 4, 8);
        let key = vec![1, 2, 3, 4];
        let value = vec![5, 6, 7, 8, 9, 10, 11, 12];

        let mut group = c.benchmark_group("map_operations");

        group.bench_function("write", |b| {
            b.iter(|| {
                let _ = black_box(manager.write_map("test_map", &key, &value));
            });
        });

        group.bench_function("read", |b| {
            b.iter(|| {
                let _ = black_box(manager.read_map("test_map", &key));
            });
        });

        group.finish();
    }

    pub fn event_processing_benchmark(c: &mut Criterion) {
        let mut processor = EventProcessor::new(10000);
        let event = EbpfEvent {
            event_type: EbpfEventType::CpuSample,
            pid: 1234,
            tid: 5678,
            timestamp: std::time::SystemTime::now(),
            data: vec![0; 100],
        };

        c.bench_function("event_process", |b| {
            b.iter(|| {
                let mut test_processor = EventProcessor::new(10000);
                let test_event = EbpfEvent {
                    event_type: EbpfEventType::CpuSample,
                    pid: 1234,
                    tid: 5678,
                    timestamp: std::time::SystemTime::now(),
                    data: vec![0; 100],
                };
                let _ = black_box(test_processor.process_event(test_event));
            });
        });
    }
}

// 组合基准测试
#[cfg(all(feature = "ebpf", target_os = "linux"))]
criterion_group!(
    benches,
    performance_benchmarks::compression_benchmark,
    performance_benchmarks::decompression_benchmark,
    profiling_benchmarks::profile_creation_benchmark,
    profiling_benchmarks::profile_add_sample_benchmark,
    profiling_benchmarks::profile_encode_json_benchmark,
    ebpf_benchmarks::probe_attach_detach_benchmark,
    ebpf_benchmarks::map_operations_benchmark,
    ebpf_benchmarks::event_processing_benchmark,
);

#[cfg(not(all(feature = "ebpf", target_os = "linux")))]
criterion_group!(
    benches,
    performance_benchmarks::compression_benchmark,
    performance_benchmarks::decompression_benchmark,
    profiling_benchmarks::profile_creation_benchmark,
    profiling_benchmarks::profile_add_sample_benchmark,
    profiling_benchmarks::profile_encode_json_benchmark,
);

criterion_main!(benches);
