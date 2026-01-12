//! Integration tests for the profiling module

use otlp::profiling::pprof::StackFrame;
use otlp::profiling::*;
use std::time::Duration;

#[tokio::test]
async fn test_cpu_profiler_lifecycle() {
    let config = CpuProfilerConfig {
        sampling_frequency: 100,
        max_duration: Duration::from_secs(1),
        include_system_calls: false,
    };

    let mut profiler = CpuProfiler::new(config);

    // Test initial state
    assert!(!profiler.is_running());
    assert_eq!(profiler.sample_count(), 0);

    // Start profiling
    assert!(profiler.start().await.is_ok());
    assert!(profiler.is_running());

    // Run some work
    tokio::time::sleep(Duration::from_millis(100)).await;

    // Stop profiling
    assert!(profiler.stop().await.is_ok());
    assert!(!profiler.is_running());

    // Wait for samples
    tokio::time::sleep(Duration::from_millis(50)).await;

    // Check stats
    let stats = profiler.get_stats().await;
    assert!(stats.sample_count > 0, "Should have collected some samples");
    assert!(stats.duration.as_millis() >= 100);
}

#[tokio::test]
async fn test_cpu_profiler_double_start() {
    let config = CpuProfilerConfig::default();
    let mut profiler = CpuProfiler::new(config);

    // First start should succeed
    assert!(profiler.start().await.is_ok());

    // Second start should fail
    assert!(profiler.start().await.is_err());

    profiler.stop().await.unwrap();
}

#[tokio::test]
async fn test_cpu_profiler_generate_profile() {
    let config = CpuProfilerConfig {
        sampling_frequency: 100,
        max_duration: Duration::from_secs(1),
        include_system_calls: false,
    };

    let mut profiler = CpuProfiler::new(config);

    profiler.start().await.unwrap();
    tokio::time::sleep(Duration::from_millis(100)).await;
    profiler.stop().await.unwrap();

    // Wait for samples
    tokio::time::sleep(Duration::from_millis(50)).await;

    // Generate profile
    let profile = profiler.generate_profile().await;
    assert!(profile.is_ok(), "Should generate profile successfully");

    let profile = profile.unwrap();
    assert!(!profile.sample.is_empty(), "Profile should have samples");
    assert!(
        !profile.string_table.is_empty(),
        "String table should not be empty"
    );
    assert!(!profile.sample_type.is_empty(), "Should have sample types");
}

#[tokio::test]
async fn test_memory_profiler_lifecycle() {
    let config = MemoryProfilerConfig {
        sampling_rate: 1, // Sample every allocation
        min_allocation_size: 0,
        max_duration: Duration::from_secs(1),
        track_deallocations: true,
    };

    let mut profiler = MemoryProfiler::new(config);

    assert!(!profiler.is_running());

    // Start profiling
    profiler.start().await.unwrap();
    assert!(profiler.is_running());

    // Record allocations
    profiler.record_allocation(1024).await;
    profiler.record_allocation(2048).await;
    profiler.record_deallocation(512).await;

    // Stop profiling
    profiler.stop().await.unwrap();
    assert!(!profiler.is_running());

    // Check stats
    let stats = profiler.get_stats().await;
    assert_eq!(stats.total_allocated, 3072);
    assert_eq!(stats.total_deallocated, 512);
    assert_eq!(stats.current_usage, 2560);
}

#[tokio::test]
async fn test_memory_profiler_sampling() {
    let config = MemoryProfilerConfig {
        sampling_rate: 2, // Sample every 2nd allocation
        min_allocation_size: 0,
        max_duration: Duration::from_secs(1),
        track_deallocations: false,
    };

    let mut profiler = MemoryProfiler::new(config);

    profiler.start().await.unwrap();

    // Record 10 allocations
    for _ in 0..10 {
        profiler.record_allocation(1024).await;
    }

    profiler.stop().await.unwrap();

    let stats = profiler.get_stats().await;
    assert_eq!(stats.allocation_count, 10);
    // With sampling_rate=2, we should sample ~5 times (0, 2, 4, 6, 8)
    assert!(stats.sample_count >= 4 && stats.sample_count <= 6);
}

#[tokio::test]
async fn test_profile_builder() {
    let profile_id = generate_profile_id();
    let pprof = PprofProfile::new();

    let profile = ProfileBuilder::new(profile_id.clone())
        .attribute(
            "service.name",
            AttributeValue::String("test-service".to_string()),
        )
        .attribute("environment", AttributeValue::String("test".to_string()))
        .link_to_span(
            vec![1, 2, 3, 4, 5, 6, 7, 8],
            vec![9, 10, 11, 12, 13, 14, 15, 16],
        )
        .build(pprof);

    assert_eq!(profile.profile_id, profile_id);
    assert_eq!(profile.attributes.len(), 2);
    assert!(profile.trace_id.is_some());
    assert!(profile.span_id.is_some());
}

#[tokio::test]
async fn test_pprof_builder() {
    let mut builder = PprofBuilder::new(ProfileType::Cpu);

    // Test string interning
    let idx1 = builder.intern_string("test");
    let idx2 = builder.intern_string("test");
    assert_eq!(idx1, idx2, "Same strings should have same index");

    // Create a sample
    let frames = vec![
        StackFrame::new("main", "main.rs", 10, 0x1000),
        StackFrame::new("foo", "lib.rs", 20, 0x2000),
    ];
    let sample = builder.create_sample_from_stack(&frames, 100);

    assert_eq!(sample.location_id.len(), 2);
    assert_eq!(sample.value, vec![100]);

    // Build profile
    let profile = builder.build();
    assert_eq!(profile.location.len(), 2);
    assert_eq!(profile.function.len(), 2);
}

#[tokio::test]
async fn test_sampling_strategies() {
    // Test AlwaysSample
    let always = AlwaysSample::new();
    for _ in 0..100 {
        assert!(always.should_sample());
    }
    let stats = always.stats();
    assert_eq!(stats.sampled_events, 100);
    assert_eq!(stats.sampling_rate, 1.0);

    // Test NeverSample
    let never = NeverSample::new();
    for _ in 0..100 {
        assert!(!never.should_sample());
    }
    let stats = never.stats();
    assert_eq!(stats.sampled_events, 0);
    assert_eq!(stats.sampling_rate, 0.0);

    // Test RateSampler
    let rate = RateSampler::new(10);
    let mut count = 0;
    for _ in 0..100 {
        if rate.should_sample() {
            count += 1;
        }
    }
    assert_eq!(count, 10, "Should sample exactly 1 in 10");

    // Test ProbabilisticSampler
    let prob = ProbabilisticSampler::new(0.5);
    let mut count = 0;
    for _ in 0..1000 {
        if prob.should_sample() {
            count += 1;
        }
    }
    // Should be approximately 500 (with some tolerance)
    assert!(count > 400 && count < 600, "Count was {}", count);
}

#[tokio::test]
async fn test_profile_async_helper() {
    let config = CpuProfilerConfig {
        sampling_frequency: 100,
        max_duration: Duration::from_secs(1),
        include_system_calls: false,
    };

    let (result, profile) = profile_async(
        async {
            tokio::time::sleep(Duration::from_millis(100)).await;
            42
        },
        config,
    )
    .await
    .unwrap();

    assert_eq!(result, 42);
    assert!(!profile.sample.is_empty());
}

#[test]
fn test_profile_type() {
    assert_eq!(ProfileType::Cpu.name(), "cpu");
    assert_eq!(ProfileType::Heap.name(), "heap");
    assert_eq!(ProfileType::Cpu.unit(), "nanoseconds");
    assert_eq!(ProfileType::Heap.unit(), "bytes");
}

#[test]
fn test_profile_id_generation() {
    let id1 = generate_profile_id();
    let id2 = generate_profile_id();

    assert_eq!(id1.len(), 16);
    assert_eq!(id2.len(), 16);
    assert_ne!(id1, id2, "Profile IDs should be unique");
}

#[test]
fn test_profile_id_from_hex() {
    let hex = "0102030405060708090a0b0c0d0e0f10";
    let id = profile_id_from_hex(hex).unwrap();

    assert_eq!(id.len(), 16);
    assert_eq!(id[0], 0x01);
    assert_eq!(id[15], 0x10);

    // Test roundtrip
    let hex2 = hex::encode(&id);
    assert_eq!(hex, hex2);
}

#[test]
fn test_stack_frame() {
    let frame = StackFrame::new("test_fn", "test.rs", 42, 0x12345678);

    assert_eq!(frame.function_name, "test_fn");
    assert_eq!(frame.file_name, "test.rs");
    assert_eq!(frame.line_number, 42);
    assert_eq!(frame.address, 0x12345678);
}

#[tokio::test]
async fn test_profiler_stats() {
    let config = CpuProfilerConfig {
        sampling_frequency: 100,
        max_duration: Duration::from_secs(1),
        include_system_calls: false,
    };

    let mut profiler = CpuProfiler::new(config);

    profiler.start().await.unwrap();
    tokio::time::sleep(Duration::from_millis(200)).await;
    profiler.stop().await.unwrap();

    tokio::time::sleep(Duration::from_millis(50)).await;

    let stats = profiler.get_stats().await;
    assert!(!stats.is_running);
    assert!(stats.sample_count > 0);
    assert!(stats.duration.as_millis() >= 200);
    assert_eq!(stats.sampling_frequency, 100);

    let actual_rate = stats.actual_sampling_rate();
    assert!(actual_rate > 0.0, "Actual sampling rate should be positive");
}

#[tokio::test]
async fn test_memory_profiler_stats_calculations() {
    let config = MemoryProfilerConfig {
        sampling_rate: 1,
        min_allocation_size: 0,
        max_duration: Duration::from_secs(1),
        track_deallocations: true,
    };

    let mut profiler = MemoryProfiler::new(config);

    profiler.start().await.unwrap();

    // Record various allocations
    for i in 0..10 {
        profiler.record_allocation((i + 1) * 1024).await;
    }

    tokio::time::sleep(Duration::from_millis(100)).await;
    profiler.stop().await.unwrap();

    let stats = profiler.get_stats().await;

    // Check calculations
    assert_eq!(stats.allocation_count, 10);
    assert_eq!(
        stats.total_allocated,
        (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10) * 1024
    );

    let avg_size = stats.average_allocation_size();
    assert!(
        (avg_size - 5632.0).abs() < 1.0,
        "Average should be ~5632 bytes"
    );

    let rate = stats.allocation_rate();
    assert!(rate > 0.0, "Allocation rate should be positive");
}

#[tokio::test]
async fn test_concurrent_profilers() {
    // Test running multiple profilers concurrently
    let cpu_config = CpuProfilerConfig {
        sampling_frequency: 100,
        max_duration: Duration::from_secs(1),
        include_system_calls: false,
    };

    let mem_config = MemoryProfilerConfig {
        sampling_rate: 1,
        min_allocation_size: 0,
        max_duration: Duration::from_secs(1),
        track_deallocations: false,
    };

    let mut cpu_profiler = CpuProfiler::new(cpu_config);
    let mut mem_profiler = MemoryProfiler::new(mem_config);

    // Start both
    cpu_profiler.start().await.unwrap();
    mem_profiler.start().await.unwrap();

    // Do some work
    tokio::time::sleep(Duration::from_millis(100)).await;
    mem_profiler.record_allocation(1024).await;

    // Stop both
    cpu_profiler.stop().await.unwrap();
    mem_profiler.stop().await.unwrap();

    tokio::time::sleep(Duration::from_millis(50)).await;

    // Both should have collected data
    let cpu_stats = cpu_profiler.get_stats().await;
    let mem_stats = mem_profiler.get_stats().await;

    assert!(cpu_stats.sample_count > 0);
    assert_eq!(mem_stats.allocation_count, 1);
}
