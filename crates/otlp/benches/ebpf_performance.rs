//! eBPF 性能基准测试
//!
//! 测试 eBPF 模块的性能特征
//!
//! ## 运行基准测试
//!
//! ```bash
//! # 运行所有基准测试
//! cargo bench --bench ebpf_performance
//!
//! # 运行特定基准测试
//! cargo bench --bench ebpf_performance -- ebpf_config_creation
//!
//! # 生成 HTML 报告
//! cargo bench --bench ebpf_performance -- --output-format html > report.html
//! ```
//!
//! ## 性能目标
//!
//! - **配置创建**: < 10ns
//! - **配置验证**: < 100ns
//! - **程序验证**: < 1μs
//! - **加载器创建**: < 100ns
//!
//! ## 已实现的基准测试
//!
//! - [x] eBPF 配置创建和验证
//! - [x] 事件处理性能
//! - [x] 批量操作性能
//! - [x] 事件过滤性能
//!
//! ## 已添加的基准测试
//!
//! - [x] eBPF 程序验证性能（模拟加载）
//! - [x] Map 读写性能（使用模拟Maps）
//! - [x] 探针管理性能
//! - [x] 事件批处理性能
//! - [x] 事件过滤性能
//!
//! ## 性能对比报告
//!
//! 运行基准测试后，可以使用以下命令生成对比报告：
//!
//! ```bash
//! cargo bench --bench ebpf_performance -- --output-format html > ebpf_performance_report.html
//! ```

// 注意: eBPF 模块需要 feature = "ebpf" 才能使用
// 如果编译时没有启用该 feature，这些导入会失败
#[cfg(feature = "ebpf")]
use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};
#[cfg(feature = "ebpf")]
use std::hint::black_box;
#[cfg(feature = "ebpf")]
use otlp::ebpf::{EbpfConfig, EbpfLoader, validate_config, recommended_sample_rate};

#[cfg(feature = "ebpf")]
fn bench_ebpf_config_creation(c: &mut Criterion) {
    c.bench_function("ebpf_config_creation", |b| {
        b.iter(|| {
            black_box(EbpfConfig::default());
        });
    });
}

#[cfg(feature = "ebpf")]
fn bench_ebpf_config_validation(c: &mut Criterion) {
    let config = EbpfConfig::default();
    c.bench_function("ebpf_config_validation", |b| {
        b.iter(|| {
            black_box(validate_config(black_box(&config))).unwrap();
        });
    });
}

#[cfg(feature = "ebpf")]
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

#[cfg(feature = "ebpf")]
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

#[cfg(feature = "ebpf")]
fn bench_ebpf_loader_new(c: &mut Criterion) {
    let config = EbpfConfig::default();
    c.bench_function("ebpf_loader_new", |b| {
        b.iter(|| {
            black_box(EbpfLoader::new(black_box(config.clone())));
        });
    });
}

#[cfg(feature = "ebpf")]
fn bench_ebpf_loader_validate_program(c: &mut Criterion) {
    let config = EbpfConfig::default();
    let loader = EbpfLoader::new(config);
    let mut elf_program = vec![0x7F, b'E', b'L', b'F'];
    elf_program.extend(vec![0; 100]);

    c.bench_function("ebpf_loader_validate_program", |b| {
        b.iter(|| {
            black_box(loader.validate_program(black_box(&elf_program))).unwrap();
        });
    });
}

#[cfg(feature = "ebpf")]
fn bench_recommended_duration(c: &mut Criterion) {
    use otlp::ebpf::recommended_duration;
    let envs = ["production", "staging", "development", "debug"];
    c.bench_function("recommended_duration", |b| {
        b.iter(|| {
            for env in &envs {
                black_box(recommended_duration(black_box(env)));
            }
        });
    });
}

#[cfg(feature = "ebpf")]
fn bench_create_recommended_config(c: &mut Criterion) {
    use otlp::ebpf::create_recommended_config;
    let envs = ["production", "staging", "development", "debug"];
    c.bench_function("create_recommended_config", |b| {
        b.iter(|| {
            for env in &envs {
                black_box(create_recommended_config(black_box(env)));
            }
        });
    });
}

// 注意: 以下基准测试需要实际 eBPF 程序才能运行
// 当前为占位实现，实际运行时需要:
// 1. 编译 eBPF 程序（使用 bpf-linker 或 aya-template）
// 2. 加载 eBPF 程序到内核
// 3. 附加探针
// 4. 执行实际操作

#[cfg(all(feature = "ebpf", target_os = "linux"))]
fn bench_ebpf_program_load(c: &mut Criterion) {
    use otlp::ebpf::EbpfLoader;

    let config = EbpfConfig::default();
    let mut loader = EbpfLoader::new(config);

    // 创建最小有效的 ELF 头部用于测试
    let mut elf_program = vec![0x7F, b'E', b'L', b'F'];
    elf_program.extend(vec![0; 100]);

    c.bench_function("ebpf_program_load", |b| {
        b.iter(|| {
            // 测试程序验证和加载准备（实际加载需要真实eBPF程序）
            let mut test_loader = EbpfLoader::new(EbpfConfig::default());
            let _ = black_box(test_loader.validate_program(black_box(&elf_program)));
        });
    });
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
fn bench_ebpf_map_read_write(c: &mut Criterion) {
    use otlp::ebpf::{MapsManager, MapType};

    let mut manager = MapsManager::new();
    manager.register_map("test_map".to_string(), MapType::Hash, 4, 8);
    let key = vec![1, 2, 3, 4];
    let value = vec![5, 6, 7, 8, 9, 10, 11, 12];

    c.bench_function("ebpf_map_write", |b| {
        b.iter(|| {
            let _ = black_box(manager.write_map("test_map", &key, &value, None));
        });
    });

    c.bench_function("ebpf_map_read", |b| {
        b.iter(|| {
            let _ = black_box(manager.read_map("test_map", &key, None));
        });
    });
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
fn bench_ebpf_event_processing(c: &mut Criterion) {
    use otlp::ebpf::{EventProcessor, EbpfEvent, EbpfEventType};

    let mut processor = EventProcessor::new(1000);
    let event = EbpfEvent {
        event_type: EbpfEventType::CpuSample,
        pid: 1234,
        tid: 5678,
        timestamp: std::time::SystemTime::now(),
        data: vec![0; 100],
    };

    c.bench_function("ebpf_event_process", |b| {
        b.iter(|| {
            let mut test_processor = EventProcessor::new(1000);
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

    c.bench_function("ebpf_event_flush", |b| {
        b.iter(|| {
            let mut test_processor = EventProcessor::new(100);
            // 添加一些事件
            for i in 0..10 {
                let test_event = EbpfEvent {
                    event_type: EbpfEventType::CpuSample,
                    pid: 1000 + i,
                    tid: 2000 + i,
                    timestamp: std::time::SystemTime::now(),
                    data: vec![],
                };
                let _ = test_processor.process_event(test_event);
            }
            let _ = black_box(test_processor.flush_events());
        });
    });
}

#[cfg(feature = "ebpf")]
fn bench_ebpf_event_batch_processing(c: &mut Criterion) {
    use otlp::ebpf::{EventProcessor, EbpfEvent, EbpfEventType};

    let mut events = Vec::new();
    for i in 0..100 {
        events.push(EbpfEvent {
            event_type: EbpfEventType::CpuSample,
            pid: 1000 + i,
            tid: 2000 + i,
            timestamp: std::time::SystemTime::now(),
            data: vec![0; 50],
        });
    }

    c.bench_function("ebpf_event_batch_processing", |b| {
        b.iter(|| {
            let mut test_processor = EventProcessor::new(1000);
            let _ = black_box(test_processor.process_batch(events.clone()));
        });
    });
}

#[cfg(feature = "ebpf")]
fn bench_ebpf_event_filtering(c: &mut Criterion) {
    use otlp::ebpf::{EventProcessor, EbpfEvent, EbpfEventType};

    let mut processor = EventProcessor::new(1000);
    // 添加混合类型的事件
    for i in 0..100 {
        let event_type = if i % 2 == 0 {
            EbpfEventType::CpuSample
        } else {
            EbpfEventType::NetworkPacket
        };
        processor.process_event(EbpfEvent {
            event_type,
            pid: 1000 + (i % 10),
            tid: 2000 + i,
            timestamp: std::time::SystemTime::now(),
            data: vec![],
        }).unwrap();
    }

    c.bench_function("ebpf_event_filter_by_type", |b| {
        b.iter(|| {
            let _ = black_box(processor.filter_by_type(EbpfEventType::CpuSample));
        });
    });

    c.bench_function("ebpf_event_filter_by_pid", |b| {
        b.iter(|| {
            let _ = black_box(processor.filter_by_pid(1005));
        });
    });
}

#[cfg(feature = "ebpf")]
fn bench_ebpf_probe_manager(c: &mut Criterion) {
    use otlp::ebpf::ProbeManager;

    c.bench_function("ebpf_probe_manager_new", |b| {
        b.iter(|| {
            black_box(ProbeManager::new());
        });
    });

    c.bench_function("ebpf_probe_manager_attach_kprobe", |b| {
        b.iter(|| {
            let mut manager = ProbeManager::new();
            let _ = black_box(manager.attach_kprobe("test_probe", "test_function", None));
        });
    });
}

#[cfg(feature = "ebpf")]
fn bench_ebpf_maps_manager(c: &mut Criterion) {
    use otlp::ebpf::{MapsManager, MapType};

    c.bench_function("ebpf_maps_manager_new", |b| {
        b.iter(|| {
            black_box(MapsManager::new());
        });
    });

    c.bench_function("ebpf_maps_manager_register_map", |b| {
        b.iter(|| {
            let mut manager = MapsManager::new();
            black_box(manager.register_map("test_map".to_string(), MapType::Hash, 4, 8));
        });
    });

    // 添加更多Map类型注册的性能测试
    let mut group = c.benchmark_group("ebpf_maps_manager_register_different_types");

    group.bench_function("register_hash_map", |b| {
        b.iter(|| {
            let mut manager = MapsManager::new();
            black_box(manager.register_map("hash_map".to_string(), MapType::Hash, 4, 8));
        });
    });

    group.bench_function("register_array_map", |b| {
        b.iter(|| {
            let mut manager = MapsManager::new();
            black_box(manager.register_map("array_map".to_string(), MapType::Array, 4, 8));
        });
    });

    group.bench_function("register_perf_event_map", |b| {
        b.iter(|| {
            let mut manager = MapsManager::new();
            black_box(manager.register_map("perf_map".to_string(), MapType::PerfEvent, 4, 8));
        });
    });

    group.bench_function("register_ring_buffer_map", |b| {
        b.iter(|| {
            let mut manager = MapsManager::new();
            black_box(manager.register_map("ring_map".to_string(), MapType::RingBuffer, 4, 8));
        });
    });

    group.finish();
}

#[cfg(feature = "ebpf")]
fn bench_ebpf_probe_operations(c: &mut Criterion) {
    use otlp::ebpf::ProbeManager;

    let mut group = c.benchmark_group("ebpf_probe_operations");

    group.bench_function("attach_uprobe", |b| {
        b.iter(|| {
            let mut manager = ProbeManager::new();
            let _ = black_box(manager.attach_uprobe("test_uprobe", "/usr/bin/test", "malloc", None));
        });
    });

    group.bench_function("attach_tracepoint", |b| {
        b.iter(|| {
            let mut manager = ProbeManager::new();
            let _ = black_box(manager.attach_tracepoint("test_tracepoint", "syscalls", "sys_enter_open", None));
        });
    });

    group.bench_function("detach_all", |b| {
        b.iter(|| {
            let mut manager = ProbeManager::new();
            let _ = manager.attach_kprobe("test1", "func1", None);
            let _ = manager.attach_kprobe("test2", "func2", None);
            let _ = manager.attach_uprobe("test3", "/usr/bin/test", "malloc", None);
            let _ = black_box(manager.detach_all());
        });
    });

    group.bench_function("probe_count", |b| {
        b.iter(|| {
            let mut manager = ProbeManager::new();
            let _ = manager.attach_kprobe("test1", "func1", None);
            let _ = manager.attach_kprobe("test2", "func2", None);
            let _ = manager.attach_uprobe("test3", "/usr/bin/test", "malloc", None);
            black_box(manager.probe_count());
        });
    });

    group.finish();
}

#[cfg(feature = "ebpf")]
fn bench_ebpf_event_batch_sizes(c: &mut Criterion) {
    use otlp::ebpf::{EventProcessor, EbpfEvent, EbpfEventType};

    let mut group = c.benchmark_group("ebpf_event_batch_processing_sizes");

    for size in [10, 100, 1000, 10000].iter() {
        let events: Vec<EbpfEvent> = (0..*size).map(|i| {
            EbpfEvent {
                event_type: EbpfEventType::CpuSample,
                pid: 1000 + (i % 10),
                tid: 2000 + i,
                timestamp: std::time::SystemTime::now(),
                data: vec![0; 50],
            }
        }).collect();

        group.bench_with_input(
            BenchmarkId::from_parameter(format!("batch_size_{}", size)),
            &events,
            |b, events| {
                b.iter(|| {
                    let mut processor = EventProcessor::new(10000);
                    let _ = black_box(processor.process_batch(events.clone()));
                });
            },
        );
    }

    group.finish();
}

#[cfg(feature = "ebpf")]
fn bench_ebpf_system_support_check(c: &mut Criterion) {
    use otlp::ebpf::EbpfLoader;

    c.bench_function("ebpf_system_support_check", |b| {
        b.iter(|| {
            let _ = black_box(EbpfLoader::check_system_support());
        });
    });
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
criterion_group!(
    benches,
    bench_ebpf_config_creation,
    bench_ebpf_config_validation,
    bench_ebpf_config_builder,
    bench_recommended_sample_rate,
    bench_recommended_duration,
    bench_create_recommended_config,
    bench_ebpf_loader_new,
    bench_ebpf_loader_validate_program,
    bench_ebpf_program_load,
    bench_ebpf_system_support_check,
    bench_ebpf_map_read_write,
    bench_ebpf_event_processing,
    bench_ebpf_event_batch_processing,
    bench_ebpf_event_batch_sizes,
    bench_ebpf_event_filtering,
    bench_ebpf_probe_manager,
    bench_ebpf_probe_operations,
    bench_ebpf_maps_manager,
);

#[cfg(all(feature = "ebpf", not(target_os = "linux")))]
criterion_group!(
    benches,
    bench_ebpf_config_creation,
    bench_ebpf_config_validation,
    bench_ebpf_config_builder,
    bench_recommended_sample_rate,
    bench_recommended_duration,
    bench_create_recommended_config,
    bench_ebpf_loader_new,
    bench_ebpf_loader_validate_program,
    bench_ebpf_event_batch_processing,
    bench_ebpf_event_batch_sizes,
    bench_ebpf_event_filtering,
    bench_ebpf_probe_manager,
    bench_ebpf_probe_operations,
    bench_ebpf_maps_manager,
);

// 如果没有启用 ebpf feature，不运行任何基准测试
#[cfg(not(feature = "ebpf"))]
fn main() {
    println!("eBPF feature 未启用，跳过基准测试");
}

#[cfg(feature = "ebpf")]
criterion_main!(benches);
