# OTLP Profiling User Guide

## Overview

The OTLP Profiling module provides comprehensive profiling support for Rust applications, enabling you to collect and export performance data in OpenTelemetry-compatible formats.

## Features

- **CPU Profiling**: Sample call stacks to identify CPU hotspots
- **Memory Profiling**: Track heap allocations and memory usage patterns
- **pprof Format**: Industry-standard profile format support
- **OTLP Export**: Export profiles to OTLP collectors (Jaeger, Grafana, etc.)
- **Sampling Strategies**: Multiple sampling strategies to control overhead
- **Trace Correlation**: Link profiles to distributed traces

## Quick Start

### CPU Profiling

```rust
use otlp::profiling::{CpuProfiler, CpuProfilerConfig};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Configure the profiler
    let config = CpuProfilerConfig {
        sampling_frequency: 99, // 99 Hz (recommended)
        max_duration: Duration::from_secs(30),
        include_system_calls: false,
    };

    let mut profiler = CpuProfiler::new(config);

    // Start profiling
    profiler.start().await?;

    // Run your application code
    do_work().await;

    // Stop profiling
    profiler.stop().await?;

    // Generate profile
    let profile = profiler.generate_profile().await?;

    println!("Collected {} samples", profile.sample.len());

    Ok(())
}
```

### Memory Profiling

```rust
use otlp::profiling::{MemoryProfiler, MemoryProfilerConfig};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = MemoryProfilerConfig {
        sampling_rate: 524_288, // Sample 1 in 512KB
        min_allocation_size: 1024,
        max_duration: Duration::from_secs(30),
        track_deallocations: true,
    };

    let mut profiler = MemoryProfiler::new(config);

    profiler.start().await?;

    // Your code with allocations
    // Note: You need to manually record allocations
    // In a real scenario, this would be done through a global allocator

    profiler.stop().await?;
    let profile = profiler.generate_profile().await?;

    Ok(())
}
```

### Profile a Specific Function

```rust
use otlp::profiling::{profile_async, CpuProfilerConfig};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let (result, profile) = profile_async(
        async {
            // Your async work here
            expensive_computation().await
        },
        CpuProfilerConfig::default(),
    ).await?;

    println!("Result: {}", result);
    println!("Profile samples: {}", profile.sample.len());

    Ok(())
}
```

## Exporting to OTLP

### Basic Export

```rust
use otlp::profiling::{
    ProfileExporter, ProfileExporterConfig, ProfileBuilder,
    generate_profile_id, AttributeValue,
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Create exporter
    let config = ProfileExporterConfig {
        endpoint: "http://localhost:4318/v1/profiles".to_string(),
        api_key: Some("your-api-key".to_string()),
        ..Default::default()
    };

    let exporter = ProfileExporter::new(config);

    // Build profile
    let profile = ProfileBuilder::new(generate_profile_id())
        .attribute("service.name", AttributeValue::String("my-service".to_string()))
        .attribute("environment", AttributeValue::String("production".to_string()))
        .build(pprof_profile);

    // Export
    exporter.export_profile(profile).await?;

    Ok(())
}
```

### Batch Export

```rust
// Export multiple profiles at once
let profiles = vec![profile1, profile2, profile3];
exporter.export_profiles(profiles).await?;
```

## Sampling Strategies

### Always Sample

Sample every event (100% sampling):

```rust
use otlp::profiling::sampling::{AlwaysSample, SamplingStrategy};

let sampler = AlwaysSample::new();
if sampler.should_sample() {
    // Collect sample
}
```

### Probabilistic Sampling

Random sampling with fixed probability:

```rust
use otlp::profiling::sampling::ProbabilisticSampler;

let sampler = ProbabilisticSampler::new(0.1); // 10% sampling rate
if sampler.should_sample() {
    // Collect sample
}
```

### Rate-Based Sampling

Sample 1 in N events:

```rust
use otlp::profiling::sampling::RateSampler;

let sampler = RateSampler::new(100); // Sample 1 in 100
if sampler.should_sample() {
    // Collect sample
}
```

### Adaptive Sampling

Automatically adjust sampling rate based on volume:

```rust
use otlp::profiling::sampling::AdaptiveSampler;
use std::time::Duration;

let sampler = AdaptiveSampler::new(
    1000, // Target 1000 samples per second
    Duration::from_secs(10), // Adjust every 10 seconds
);

if sampler.should_sample() {
    // Collect sample
}
```

## Linking Profiles to Traces

Correlate profiling data with distributed traces:

```rust
use otlp::profiling::ProfileBuilder;

let mut profile = ProfileBuilder::new(profile_id)
    .link_to_span(trace_id, span_id)
    .build(pprof_profile);
```

## Configuration Best Practices

### CPU Profiling1

- **Sampling Frequency**:
  - Development: 100-1000 Hz
  - Production: 10-99 Hz (99 Hz recommended)
  - Lower frequencies reduce overhead

- **Duration**:
  - Short profiling: 10-30 seconds
  - Continuous profiling: Use adaptive sampling

### Memory Profiling1

- **Sampling Rate**:
  - Development: Sample every allocation (rate=1)
  - Production: Sample 1 in 512KB (rate=524288)
  - Higher rates reduce overhead

- **Minimum Allocation Size**:
  - Focus on large allocations: 1024+ bytes
  - Reduces noise from small allocations

## Performance Overhead

| Profiling Type | Sampling Rate | Overhead |
|----------------|---------------|----------|
| CPU | 99 Hz | ~1-3% |
| CPU | 1000 Hz | ~5-10% |
| Memory | 1 in 512KB | ~2-5% |
| Memory | Every allocation | ~20-50% |

## Integration with OTLP Collectors

### Jaeger

```yaml
# docker-compose.yml
services:
  jaeger:
    image: jaegertracing/all-in-one:latest
    ports:
      - "4318:4318" # OTLP HTTP
```

```rust
let config = ProfileExporterConfig {
    endpoint: "http://localhost:4318/v1/profiles".to_string(),
    ..Default::default()
};
```

### Grafana Cloud

```rust
let config = ProfileExporterConfig {
    endpoint: "https://profiles-prod-us-central-0.grafana.net/profiles".to_string(),
    api_key: Some(std::env::var("GRAFANA_API_KEY")?),
    ..Default::default()
};
```

### Custom Collector

```rust
let config = ProfileExporterConfig {
    endpoint: "https://your-collector.example.com/v1/profiles".to_string(),
    api_key: Some("your-auth-token".to_string()),
    timeout_secs: 30,
    ..Default::default()
};
```

## Troubleshooting

### No Samples Collected

**Problem**: Profiler returns 0 samples

**Solutions**:

- Ensure profiler is running long enough
- Check if your workload is CPU/memory intensive enough
- Verify sampling configuration isn't too restrictive
- Increase sampling frequency or rate

### High Overhead

**Problem**: Application slows down significantly when profiling

**Solutions**:

- Reduce sampling frequency (CPU profiling)
- Increase sampling rate (memory profiling)
- Use adaptive sampling
- Profile shorter time periods

### Export Failures

**Problem**: Cannot export profiles to collector

**Solutions**:

- Verify collector endpoint is correct and accessible
- Check authentication credentials
- Ensure network connectivity
- Review collector logs

## Advanced Topics

### Custom Sampling Strategies

Implement the `SamplingStrategy` trait:

```rust
use otlp::profiling::sampling::{SamplingStrategy, SamplingStats};

struct CustomSampler {
    // Your fields
}

impl SamplingStrategy for CustomSampler {
    fn should_sample(&self) -> bool {
        // Your logic
    }

    fn reset(&self) {
        // Reset state
    }

    fn stats(&self) -> SamplingStats {
        // Return statistics
    }
}
```

### Profile Analysis

```rust
let stats = profiler.get_stats().await;
println!("Samples: {}", stats.sample_count);
println!("Duration: {:?}", stats.duration);
println!("Rate: {:.2}", stats.actual_sampling_rate());
```

## Examples

See the `examples/` directory for complete examples:

- `profiling_demo.rs` - Comprehensive profiling demo
- Run with: `cargo run --example profiling_demo`

## API Reference

For detailed API documentation, see the module documentation:

```bash
cargo doc --package otlp --open
```

## Support

- GitHub Issues: <https://github.com/your-org/otlp-rust>
- Documentation: <https://docs.rs/otlp>
- Discussions: <https://github.com/your-org/otlp-rust/discussions>
