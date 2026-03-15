# OTLP Rust Examples

This directory contains comprehensive examples demonstrating the usage of the OTLP (OpenTelemetry Protocol) Rust implementation.

## Quick Start

Run any example with:

```bash
cargo run --example <example_name>
```

For example:
```bash
cargo run --example logs_basic
cargo run --example otlp_complete_walkthrough
```

## Example Categories

### 1. Complete Walkthroughs

| Example | Description | Run Command |
|---------|-------------|-------------|
| `otlp_complete_walkthrough` | Comprehensive demonstration of all OTLP signals (Traces, Metrics, Logs, Profiles) | `cargo run --example otlp_complete_walkthrough` |

**Covers:**
- Configuration setup
- Trace data creation and management
- Metric collection (Counter, Gauge, Histogram, ExponentialHistogram)
- Log generation with severity levels
- Profile data for continuous profiling
- Response handling (OTLP 1.10 Partial Success)
- Error handling patterns
- Graceful shutdown procedures

### 2. Signal-Specific Examples

#### Logs
| Example | Description |
|---------|-------------|
| `logs_basic` | Basic log creation and export |
| `logs_structured` | Structured logging with attributes |
| `logs_correlation` | Log-trace correlation |
| `logs_severity_filter` | Filtering by severity level |
| `logs_complete_example` | Complete logging demonstration |

#### Metrics
| Example | Description |
|---------|-------------|
| `exponential_histogram_example` | ExponentialHistogram usage (OTLP 1.10) |

### 3. Semantic Conventions

| Example | Description |
|---------|-------------|
| `semantic_conventions_demo` | All semantic conventions (HTTP, Database, FaaS, Cloud, Container, K8s, Exception) |

**Demonstrates:**
- HTTP client/server attributes
- Database conventions (PostgreSQL, Redis, MongoDB)
- FaaS conventions (AWS Lambda triggers)
- Cloud provider attributes (AWS, GCP, Azure)
- Container and Kubernetes conventions
- Exception handling conventions

### 4. Best Practices and Anti-Patterns

| Example | Description |
|---------|-------------|
| `best_practices_demo` | Recommended patterns and configurations |
| `otlp_anti_patterns` | Common mistakes and how to avoid them |
| `partial_success_handling` | OTLP 1.10 Partial Success handling |

### 5. Advanced Features

| Example | Description |
|---------|-------------|
| `otlp_profiling_example` | Continuous profiling with pprof export |
| `high_throughput_example` | High-throughput scenarios |
| `performance_optimization_example` | Performance tuning |
| `microservice_tracing_example` | Distributed tracing in microservices |
| `kubernetes_deployment_example` | Kubernetes-specific examples |

### 6. Rust 1.94 Features

| Example | Description |
|---------|-------------|
| `rust_1_94_array_windows_demo` | Pattern detection with array_windows |
| `rust_1_94_lazy_lock_demo` | Enhanced LazyLock/LazyCell usage |
| `rust_1_94_math_constants_demo` | EULER_GAMMA and GOLDEN_RATIO applications |
| `rust_1_94_simd_fp16_demo` | FP16 SIMD optimizations |

### 7. Scenario-Based Examples

| Example | Description |
|---------|-------------|
| `scenario_ecommerce_microservices` | E-commerce microservices tracing |
| `scenario_data_pipeline` | Data pipeline observability |
| `scenario_kubernetes_observability` | K8s cluster observability |
| `integration_cloud_providers` | Multi-cloud provider integration |

### 8. eBPF Examples (Linux only)

| Example | Description | Feature Required |
|---------|-------------|------------------|
| `ebpf_basic_example` | Basic eBPF usage | `ebpf` |
| `ebpf_async_example` | Async eBPF operations | `ebpf` |
| `ebpf_complete_example` | Complete eBPF demonstration | `ebpf` |

## Example Structure

Each example follows this structure:

```rust
//! Example Name
//!
//! Brief description of what this example demonstrates.
//!
//! Run with: cargo run --example <name>

use otlp::...;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Example code with detailed comments
}
```

## Common Patterns

### Basic Setup

```rust
use otlp::config::{OtlpConfigBuilder, TransportProtocol, Compression};
use std::time::Duration;

let config = OtlpConfigBuilder::new()
    .with_endpoint("http://localhost:4317")
    .with_protocol(TransportProtocol::Grpc)
    .with_compression(Compression::Gzip)
    .with_timeout(Duration::from_secs(30))
    .build()?;
```

### Creating Logs

```rust
use otlp::logs::{LogRecord, SeverityLevel, LogRecordBuilder};
use otlp::data::AttributeValue;

// Simple log
let log = LogRecord::info("Application started");

// Structured log
let log = LogRecordBuilder::new()
    .with_severity(SeverityLevel::Info)
    .with_message("User login")
    .with_attribute("user.id", AttributeValue::Int(123))
    .with_attribute("user.name", AttributeValue::String("alice".to_string()))
    .build();
```

### Creating Traces

```rust
use otlp::data::{TraceData, SpanKind, SpanStatus, StatusCode};
use std::collections::HashMap;

let trace = TraceData {
    trace_id: "abc123...".to_string(),
    span_id: "span001".to_string(),
    parent_span_id: None,
    name: "HTTP GET /api/users".to_string(),
    span_kind: SpanKind::Server,
    start_time: timestamp_nanos(),
    end_time: timestamp_nanos() + duration,
    status: SpanStatus {
        code: StatusCode::Ok,
        message: None,
    },
    attributes: HashMap::new(),
    events: vec![],
    links: vec![],
};
```

### Handling Partial Success

```rust
use otlp::response::{PartialSuccessHandler, ExportTracePartialSuccess};

let mut handler = PartialSuccessHandler::<ExportTracePartialSuccess>::new(1000);

// Handle partial success response
let partial = ExportTracePartialSuccess {
    rejected_spans: 50,
    error_message: "rate limit exceeded".to_string(),
};
handler.handle_trace_partial_success(&partial);

// Check if acceptable
let threshold = 0.05; // 5%
if !handler.is_acceptable(threshold) {
    eprintln!("Warning: High rejection rate: {:.1}%", 
        (1.0 - handler.success_rate()) * 100.0);
}
```

## Prerequisites

### Running Examples

1. **Basic examples**: No external dependencies
   ```bash
   cargo run --example logs_basic
   ```

2. **With OTLP collector**: Some examples assume a collector running at `localhost:4317`
   ```bash
   # Start a local collector
   docker run -p 4317:4317 otel/opentelemetry-collector
   
   cargo run --example otlp_complete_walkthrough
   ```

3. **eBPF examples** (Linux only):
   ```bash
   cargo run --example ebpf_basic_example --features ebpf
   ```

### Required Permissions

- **eBPF examples**: Require `CAP_BPF` capability and Linux kernel >= 5.8
- **High throughput examples**: May require increased file descriptor limits

## Configuration

Examples use default configurations. Override with environment variables:

```bash
export OTLP_ENDPOINT=http://my-collector:4317
export OTLP_PROTOCOL=grpc
export OTLP_TIMEOUT=30
cargo run --example <example_name>
```

## Troubleshooting

### Connection Refused

If you see connection errors:
```
Error: Failed to connect to OTLP endpoint
```

Either:
1. Start a local collector: `docker run -p 4317:4317 otel/opentelemetry-collector`
2. Or set the correct endpoint: `export OTLP_ENDPOINT=http://your-collector:4317`

### Missing Features

If you get compilation errors about missing modules:
```bash
# For eBPF examples
cargo run --example ebpf_basic_example --features ebpf

# For full feature set
cargo run --example <name> --features full
```

### Windows-specific Issues

eBPF examples don't work on Windows (Linux only).

## Contributing

When adding new examples:

1. Follow the existing code structure
2. Include detailed comments explaining WHY, not just WHAT
3. Add the example to this README
4. Include a `Run with:` comment in the file header
5. Test with both `cargo run` and `cargo test`

## Additional Resources

- [OpenTelemetry Documentation](https://opentelemetry.io/docs/)
- [OTLP Specification](https://opentelemetry.io/docs/specs/otlp/)
- [Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/)
- [Rust Docs](https://docs.rs/otlp)

## License

These examples are provided under the same license as the OTLP Rust project (MIT OR Apache-2.0).
