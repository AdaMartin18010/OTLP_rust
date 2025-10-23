//! # Profiling Demo
//!
//! This example demonstrates how to use the OTLP profiling features.
//!
//! Run with: `cargo run --example profiling_demo --features=async`

use otlp::profiling::{
    CpuProfiler, CpuProfilerConfig, MemoryProfiler, MemoryProfilerConfig,
    ProfileBuilder, ProfileExporter, ProfileExporterConfig, ProfileType,
    generate_profile_id, AttributeValue,
};
use std::collections::HashMap;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 OTLP Profiling Demo\n");

    // Demo 1: CPU Profiling
    println!("📊 Demo 1: CPU Profiling");
    demo_cpu_profiling().await?;

    println!("\n{}", "=".repeat(60));

    // Demo 2: Memory Profiling
    println!("\n📊 Demo 2: Memory Profiling");
    demo_memory_profiling().await?;

    println!("\n{}", "=".repeat(60));

    // Demo 3: Export to OTLP
    println!("\n📊 Demo 3: Export Profile to OTLP");
    demo_profile_export().await?;

    println!("\n✅ All demos completed successfully!");

    Ok(())
}

/// Demonstrate CPU profiling
async fn demo_cpu_profiling() -> Result<(), Box<dyn std::error::Error>> {
    // Configure the CPU profiler
    let config = CpuProfilerConfig {
        sampling_frequency: 100, // 100 Hz
        max_duration: Duration::from_secs(2),
        include_system_calls: false,
    };

    let mut profiler = CpuProfiler::new(config);

    println!("  ⏱️  Starting CPU profiler...");
    profiler.start().await?;

    // Simulate some CPU-intensive work
    println!("  🔄 Running CPU-intensive workload...");
    simulate_cpu_work().await;

    println!("  ⏹️  Stopping profiler...");
    profiler.stop().await?;

    // Wait a moment for samples to be processed
    tokio::time::sleep(Duration::from_millis(100)).await;

    // Get statistics
    let stats = profiler.get_stats().await;
    println!("  📈 Profile Statistics:");
    println!("     - Samples collected: {}", stats.sample_count);
    println!("     - Duration: {:.2}s", stats.duration.as_secs_f64());
    println!("     - Sampling frequency: {} Hz", stats.sampling_frequency);
    println!("     - Actual sampling rate: {:.2} samples/sec", stats.actual_sampling_rate());

    // Generate profile
    if stats.sample_count > 0 {
        let profile = profiler.generate_profile().await?;
        println!("  ✅ Generated pprof profile:");
        println!("     - Samples: {}", profile.sample.len());
        println!("     - Locations: {}", profile.location.len());
        println!("     - Functions: {}", profile.function.len());
        println!("     - String table size: {}", profile.string_table.len());
    } else {
        println!("  ⚠️  No samples collected");
    }

    Ok(())
}

/// Demonstrate memory profiling
async fn demo_memory_profiling() -> Result<(), Box<dyn std::error::Error>> {
    // Configure the memory profiler
    let config = MemoryProfilerConfig {
        sampling_rate: 1, // Sample every allocation for demo
        min_allocation_size: 0,
        max_duration: Duration::from_secs(2),
        track_deallocations: true,
    };

    let mut profiler = MemoryProfiler::new(config);

    println!("  ⏱️  Starting memory profiler...");
    profiler.start().await?;

    // Simulate some allocations
    println!("  🔄 Running memory-intensive workload...");
    for _ in 0..10 {
        profiler.record_allocation(1024).await;
        profiler.record_allocation(2048).await;
        profiler.record_deallocation(512).await;
    }

    println!("  ⏹️  Stopping profiler...");
    profiler.stop().await?;

    // Get statistics
    let stats = profiler.get_stats().await;
    println!("  📈 Profile Statistics:");
    println!("     - Samples collected: {}", stats.sample_count);
    println!("     - Total allocated: {} bytes", stats.total_allocated);
    println!("     - Total deallocated: {} bytes", stats.total_deallocated);
    println!("     - Current usage: {} bytes", stats.current_usage);
    println!("     - Allocation count: {}", stats.allocation_count);
    println!("     - Allocation rate: {:.2} bytes/sec", stats.allocation_rate());
    println!("     - Average allocation: {:.2} bytes", stats.average_allocation_size());

    // Generate profile
    if stats.sample_count > 0 {
        let profile = profiler.generate_profile().await?;
        println!("  ✅ Generated heap profile:");
        println!("     - Samples: {}", profile.sample.len());
        println!("     - Locations: {}", profile.location.len());
        println!("     - Functions: {}", profile.function.len());
    } else {
        println!("  ⚠️  No samples collected");
    }

    Ok(())
}

/// Demonstrate profile export
async fn demo_profile_export() -> Result<(), Box<dyn std::error::Error>> {
    // Create a simple profile
    let mut config = CpuProfilerConfig::default();
    config.max_duration = Duration::from_millis(500);
    
    let mut profiler = CpuProfiler::new(config);
    
    println!("  🔄 Collecting profile data...");
    profiler.start().await?;
    simulate_cpu_work().await;
    profiler.stop().await?;
    
    tokio::time::sleep(Duration::from_millis(100)).await;
    
    let pprof_profile = profiler.generate_profile().await?;

    // Build a complete OTLP profile
    let profile_id = generate_profile_id();
    println!("  🆔 Profile ID: {}", hex::encode(&profile_id));

    let mut attributes = HashMap::new();
    attributes.insert(
        "service.name".to_string(),
        AttributeValue::String("profiling-demo".to_string()),
    );
    attributes.insert(
        "profile.type".to_string(),
        AttributeValue::String(ProfileType::Cpu.name().to_string()),
    );

    let profile = ProfileBuilder::new(profile_id.clone())
        .attribute("service.name", AttributeValue::String("profiling-demo".to_string()))
        .attribute("profile.type", AttributeValue::String("cpu".to_string()))
        .attribute("environment", AttributeValue::String("development".to_string()))
        .build(pprof_profile);

    println!("  ✅ Built OTLP profile:");
    println!("     - Profile ID: {}", hex::encode(&profile.profile_id));
    println!("     - Attributes: {}", profile.attributes.len());
    println!("     - Start time: {}", profile.start_time_unix_nano);
    println!("     - End time: {}", profile.end_time_unix_nano);

    // Configure exporter (would send to real collector in production)
    let exporter_config = ProfileExporterConfig {
        endpoint: "http://localhost:4318/v1/profiles".to_string(),
        api_key: None,
        batch_size: 100,
        timeout_secs: 30,
        resource_attributes: attributes,
    };

    let _exporter = ProfileExporter::new(exporter_config);

    println!("  📤 Exporter configured (not sending to avoid network dependency in demo)");
    println!("     - Endpoint: http://localhost:4318/v1/profiles");
    println!("     - Ready to export profiles to OTLP collector");

    Ok(())
}

/// Simulate CPU-intensive work
async fn simulate_cpu_work() {
    for _ in 0..5 {
        // Simulate some computation
        let mut sum = 0u64;
        for i in 0..1_000_000 {
            sum = sum.wrapping_add(i);
        }
        
        // Small async delay
        tokio::time::sleep(Duration::from_millis(10)).await;
        
        // Prevent optimization
        std::hint::black_box(sum);
    }
}

