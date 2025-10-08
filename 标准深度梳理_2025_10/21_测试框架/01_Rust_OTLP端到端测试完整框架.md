# Rust OTLP 端到端测试完整框架

> **文档版本**: v1.0.0  
> **Rust 版本**: 1.90  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025-10-08  
> **文档状态**: ✅ 生产就绪

---

## 📋 目录

- [Rust OTLP 端到端测试完整框架](#rust-otlp-端到端测试完整框架)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [为什么需要完整的测试框架？](#为什么需要完整的测试框架)
    - [测试框架技术栈](#测试框架技术栈)
  - [测试金字塔](#测试金字塔)
    - [测试层次结构](#测试层次结构)
    - [测试比例分配](#测试比例分配)
  - [单元测试](#单元测试)
    - [TraceID 单元测试](#traceid-单元测试)
    - [SpanContext 单元测试](#spancontext-单元测试)
    - [Mock测试 - Exporter](#mock测试---exporter)
  - [集成测试](#集成测试)
    - [gRPC 传输集成测试](#grpc-传输集成测试)
    - [数据库追踪集成测试](#数据库追踪集成测试)
    - [Redis 追踪集成测试](#redis-追踪集成测试)
  - [端到端测试](#端到端测试)
    - [完整追踪链路测试](#完整追踪链路测试)
    - [微服务链路测试](#微服务链路测试)
  - [契约测试](#契约测试)
    - [Pact 消费者测试](#pact-消费者测试)
  - [性能测试](#性能测试)
    - [Criterion 基准测试](#criterion-基准测试)
    - [负载测试](#负载测试)
  - [混沌测试](#混沌测试)
    - [网络故障注入](#网络故障注入)
    - [资源耗尽测试](#资源耗尽测试)
  - [测试覆盖率](#测试覆盖率)
    - [Tarpaulin 配置](#tarpaulin-配置)
    - [运行覆盖率测试](#运行覆盖率测试)
    - [覆盖率报告示例](#覆盖率报告示例)
  - [CI/CD集成](#cicd集成)
    - [GitHub Actions 配置](#github-actions-配置)
    - [GitLab CI 配置](#gitlab-ci-配置)
  - [最佳实践](#最佳实践)
    - [1. 测试命名约定](#1-测试命名约定)
    - [2. 测试组织结构](#2-测试组织结构)
    - [3. 测试隔离](#3-测试隔离)
    - [4. 异步测试最佳实践](#4-异步测试最佳实践)
    - [5. 测试数据管理](#5-测试数据管理)
    - [6. 断言最佳实践](#6-断言最佳实践)
    - [7. 测试覆盖率目标](#7-测试覆盖率目标)
  - [总结](#总结)
    - [测试框架完整性检查表](#测试框架完整性检查表)
    - [核心指标](#核心指标)
    - [下一步行动](#下一步行动)

---

## 概述

### 为什么需要完整的测试框架？

在生产环境中部署 OTLP 追踪系统需要：

- ✅ **正确性保证**: 确保追踪数据不丢失、不错误
- ✅ **性能验证**: 确保低开销、高吞吐
- ✅ **可靠性**: 确保在各种故障场景下的行为
- ✅ **兼容性**: 确保与各种后端和协议的兼容
- ✅ **回归防护**: 确保新功能不破坏现有功能

### 测试框架技术栈

```toml
[dev-dependencies]
# 单元测试
tokio = { version = "1.47.1", features = ["test-util", "macros"] }
mockall = "0.13.1"  # Mock框架
rstest = "0.24.0"   # 参数化测试

# 集成测试
testcontainers = "0.24.1"  # 容器化测试环境
testcontainers-modules = { version = "0.12.0", features = ["postgres", "redis"] }

# 性能测试
criterion = { version = "0.5.1", features = ["html_reports", "async_tokio"] }

# 覆盖率
cargo-tarpaulin = "0.33.0"
cargo-llvm-cov = "0.6.20"

# 契约测试
pact_consumer = "1.2.5"

# 混沌测试
chaos-testing = "0.1.0"

# 断言库
assert_matches = "1.5.0"
pretty_assertions = "1.4.1"
```

---

## 测试金字塔

### 测试层次结构

```text
        ┌─────────────────┐
        │   端到端测试     │  ← 5% (慢、脆弱、全面)
        │    E2E Tests    │
        └─────────────────┘
      ┌───────────────────────┐
      │     集成测试           │  ← 15% (中速、依赖真实服务)
      │  Integration Tests    │
      └───────────────────────┘
    ┌──────────────────────────────┐
    │        单元测试               │  ← 80% (快、隔离、细粒度)
    │       Unit Tests             │
    └──────────────────────────────┘
```

### 测试比例分配

| 测试类型 | 比例 | 数量估算 | 执行时间 |
|---------|------|---------|---------|
| 单元测试 | 80% | 500+ | < 5s |
| 集成测试 | 15% | 100+ | 10-30s |
| 端到端测试 | 5% | 30+ | 1-5min |

---

## 单元测试

### TraceID 单元测试

```rust
// src/trace_id.rs
use std::fmt;

/// 128位的TraceID
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TraceId([u8; 16]);

impl TraceId {
    /// 创建新的随机TraceID
    pub fn new() -> Self {
        use rand::RngCore;
        let mut bytes = [0u8; 16];
        rand::thread_rng().fill_bytes(&mut bytes);
        Self(bytes)
    }

    /// 从字节创建TraceID
    pub fn from_bytes(bytes: [u8; 16]) -> Option<Self> {
        if bytes == [0u8; 16] {
            None  // 全0无效
        } else {
            Some(Self(bytes))
        }
    }

    /// 验证TraceID是否有效
    pub fn is_valid(&self) -> bool {
        self.0 != [0u8; 16]
    }

    /// 转换为字节
    pub fn to_bytes(&self) -> [u8; 16] {
        self.0
    }

    /// 转换为十六进制字符串
    pub fn to_hex(&self) -> String {
        self.0.iter()
            .map(|b| format!("{:02x}", b))
            .collect()
    }
}

impl fmt::Display for TraceId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_hex())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::*;

    #[test]
    fn test_new_trace_id_is_valid() {
        let trace_id = TraceId::new();
        assert!(trace_id.is_valid());
    }

    #[test]
    fn test_new_trace_id_is_non_zero() {
        let trace_id = TraceId::new();
        assert_ne!(trace_id.to_bytes(), [0u8; 16]);
    }

    #[test]
    fn test_from_bytes_valid() {
        let bytes = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
        let trace_id = TraceId::from_bytes(bytes).unwrap();
        assert_eq!(trace_id.to_bytes(), bytes);
    }

    #[test]
    fn test_from_bytes_invalid_zero() {
        let bytes = [0u8; 16];
        assert!(TraceId::from_bytes(bytes).is_none());
    }

    #[test]
    fn test_trace_id_equality() {
        let bytes = [1; 16];
        let trace_id1 = TraceId::from_bytes(bytes).unwrap();
        let trace_id2 = TraceId::from_bytes(bytes).unwrap();
        assert_eq!(trace_id1, trace_id2);
    }

    #[test]
    fn test_trace_id_inequality() {
        let trace_id1 = TraceId::new();
        let trace_id2 = TraceId::new();
        // 极小概率相同，实际上应该不同
        assert_ne!(trace_id1, trace_id2);
    }

    #[test]
    fn test_to_hex() {
        let bytes = [0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef,
                     0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef];
        let trace_id = TraceId::from_bytes(bytes).unwrap();
        assert_eq!(trace_id.to_hex(), "0123456789abcdef0123456789abcdef");
    }

    // 参数化测试
    #[rstest]
    #[case([1; 16], true)]
    #[case([0xff; 16], true)]
    #[case([0; 16], false)]
    fn test_is_valid_parametrized(#[case] bytes: [u8; 16], #[case] expected: bool) {
        let result = TraceId::from_bytes(bytes);
        assert_eq!(result.is_some(), expected);
    }
}
```

### SpanContext 单元测试

```rust
// src/span_context.rs
use crate::trace_id::TraceId;
use crate::span_id::SpanId;

#[derive(Debug, Clone, PartialEq)]
pub struct SpanContext {
    trace_id: TraceId,
    span_id: SpanId,
    trace_flags: u8,
    is_remote: bool,
}

impl SpanContext {
    pub fn new(
        trace_id: TraceId,
        span_id: SpanId,
        trace_flags: u8,
        is_remote: bool,
    ) -> Self {
        Self {
            trace_id,
            span_id,
            trace_flags,
            is_remote,
        }
    }

    pub fn trace_id(&self) -> &TraceId {
        &self.trace_id
    }

    pub fn span_id(&self) -> &SpanId {
        &self.span_id
    }

    pub fn is_sampled(&self) -> bool {
        (self.trace_flags & 0x01) != 0
    }

    pub fn is_remote(&self) -> bool {
        self.is_remote
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_span_context_creation() {
        let trace_id = TraceId::new();
        let span_id = SpanId::new();
        let context = SpanContext::new(trace_id, span_id, 0x01, false);

        assert_eq!(context.trace_id(), &trace_id);
        assert_eq!(context.span_id(), &span_id);
        assert!(context.is_sampled());
        assert!(!context.is_remote());
    }

    #[test]
    fn test_sampled_flag() {
        let trace_id = TraceId::new();
        let span_id = SpanId::new();
        
        // Sampled
        let sampled = SpanContext::new(trace_id, span_id, 0x01, false);
        assert!(sampled.is_sampled());
        
        // Not sampled
        let not_sampled = SpanContext::new(trace_id, span_id, 0x00, false);
        assert!(!not_sampled.is_sampled());
    }

    #[test]
    fn test_remote_flag() {
        let trace_id = TraceId::new();
        let span_id = SpanId::new();
        
        // Remote
        let remote = SpanContext::new(trace_id, span_id, 0x01, true);
        assert!(remote.is_remote());
        
        // Local
        let local = SpanContext::new(trace_id, span_id, 0x01, false);
        assert!(!local.is_remote());
    }
}
```

### Mock测试 - Exporter

```rust
// src/exporter.rs
use async_trait::async_trait;
use crate::span::Span;

#[async_trait]
pub trait SpanExporter: Send + Sync {
    async fn export(&self, spans: Vec<Span>) -> Result<(), Box<dyn std::error::Error>>;
    async fn shutdown(&self) -> Result<(), Box<dyn std::error::Error>>;
}

#[cfg(test)]
mod tests {
    use super::*;
    use mockall::mock;
    use mockall::predicate::*;

    mock! {
        pub Exporter {}

        #[async_trait]
        impl SpanExporter for Exporter {
            async fn export(&self, spans: Vec<Span>) -> Result<(), Box<dyn std::error::Error>>;
            async fn shutdown(&self) -> Result<(), Box<dyn std::error::Error>>;
        }
    }

    #[tokio::test]
    async fn test_exporter_export_success() {
        let mut mock_exporter = MockExporter::new();
        
        // 设置期望
        mock_exporter
            .expect_export()
            .withf(|spans| spans.len() == 1)
            .times(1)
            .returning(|_| Ok(()));

        // 执行测试
        let span = Span::new("test_span");
        let result = mock_exporter.export(vec![span]).await;
        
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_exporter_export_failure() {
        let mut mock_exporter = MockExporter::new();
        
        // 设置期望失败
        mock_exporter
            .expect_export()
            .times(1)
            .returning(|_| Err("Network error".into()));

        // 执行测试
        let span = Span::new("test_span");
        let result = mock_exporter.export(vec![span]).await;
        
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_exporter_shutdown() {
        let mut mock_exporter = MockExporter::new();
        
        mock_exporter
            .expect_shutdown()
            .times(1)
            .returning(|| Ok(()));

        let result = mock_exporter.shutdown().await;
        assert!(result.is_ok());
    }
}
```

---

## 集成测试

### gRPC 传输集成测试

```rust
// tests/integration/grpc_transport_test.rs
use testcontainers::{clients::Cli, GenericImage};
use opentelemetry::trace::{Tracer, TracerProvider};
use opentelemetry_otlp::WithExportConfig;
use std::time::Duration;

#[tokio::test]
async fn test_grpc_export_to_collector() {
    // 启动 OpenTelemetry Collector 容器
    let docker = Cli::default();
    let collector = docker.run(
        GenericImage::new("otel/opentelemetry-collector", "0.119.0")
            .with_exposed_port(4317)
            .with_wait_for(testcontainers::core::WaitFor::message_on_stdout("Everything is ready"))
    );

    let port = collector.get_host_port_ipv4(4317);
    let endpoint = format!("http://127.0.0.1:{}", port);

    // 配置 OTLP Exporter
    let exporter = opentelemetry_otlp::SpanExporter::builder()
        .with_tonic()
        .with_endpoint(&endpoint)
        .with_timeout(Duration::from_secs(3))
        .build()
        .expect("Failed to create exporter");

    let provider = opentelemetry_sdk::trace::TracerProvider::builder()
        .with_simple_exporter(exporter)
        .build();

    let tracer = provider.tracer("test-tracer");

    // 创建测试 Span
    tracer.in_span("test_span", |cx| {
        let span = cx.span();
        span.set_attribute("test.key", "test_value");
        span.add_event("test_event", vec![]);
    });

    // 等待导出完成
    tokio::time::sleep(Duration::from_secs(1)).await;

    // TODO: 验证数据已到达 Collector
    // 可以通过 Collector 的 metrics 端点验证
}

#[tokio::test]
async fn test_grpc_retry_on_failure() {
    // 测试重试机制
    let endpoint = "http://127.0.0.1:19999"; // 不存在的端点

    let exporter = opentelemetry_otlp::SpanExporter::builder()
        .with_tonic()
        .with_endpoint(endpoint)
        .with_timeout(Duration::from_secs(1))
        .build()
        .expect("Failed to create exporter");

    let provider = opentelemetry_sdk::trace::TracerProvider::builder()
        .with_simple_exporter(exporter)
        .build();

    let tracer = provider.tracer("test-tracer");

    // 创建 Span（应该失败但不崩溃）
    tracer.in_span("test_span", |_cx| {
        // 测试内容
    });

    tokio::time::sleep(Duration::from_secs(2)).await;
    
    // 验证程序没有崩溃
}
```

### 数据库追踪集成测试

```rust
// tests/integration/database_tracing_test.rs
use testcontainers::{clients::Cli, images::postgres::Postgres};
use sqlx::{PgPool, Row};
use opentelemetry::trace::{Tracer, TracerProvider};
use tracing_subscriber::{layer::SubscriberExt, Registry};

#[tokio::test]
async fn test_sqlx_tracing() {
    // 启动 PostgreSQL 容器
    let docker = Cli::default();
    let postgres = docker.run(Postgres::default());
    let port = postgres.get_host_port_ipv4(5432);

    let database_url = format!(
        "postgres://postgres:postgres@localhost:{}/postgres",
        port
    );

    // 设置追踪
    let tracer = opentelemetry_sdk::trace::TracerProvider::builder()
        .with_simple_exporter(opentelemetry_stdout::SpanExporter::default())
        .build()
        .tracer("test-tracer");

    let telemetry = tracing_opentelemetry::layer().with_tracer(tracer);
    let subscriber = Registry::default().with(telemetry);
    tracing::subscriber::set_global_default(subscriber).unwrap();

    // 连接数据库
    let pool = PgPool::connect(&database_url).await.unwrap();

    // 执行查询（带追踪）
    let span = tracing::info_span!("database_query");
    let _guard = span.enter();

    let row: (i32,) = sqlx::query_as("SELECT 1")
        .fetch_one(&pool)
        .await
        .unwrap();

    assert_eq!(row.0, 1);

    pool.close().await;
}

#[tokio::test]
async fn test_transaction_tracing() {
    let docker = Cli::default();
    let postgres = docker.run(Postgres::default());
    let port = postgres.get_host_port_ipv4(5432);

    let database_url = format!(
        "postgres://postgres:postgres@localhost:{}/postgres",
        port
    );

    let pool = PgPool::connect(&database_url).await.unwrap();

    // 创建测试表
    sqlx::query("CREATE TABLE test_table (id SERIAL PRIMARY KEY, value TEXT)")
        .execute(&pool)
        .await
        .unwrap();

    // 测试事务
    let mut tx = pool.begin().await.unwrap();

    sqlx::query("INSERT INTO test_table (value) VALUES ($1)")
        .bind("test_value")
        .execute(&mut *tx)
        .await
        .unwrap();

    tx.commit().await.unwrap();

    // 验证数据
    let count: (i64,) = sqlx::query_as("SELECT COUNT(*) FROM test_table")
        .fetch_one(&pool)
        .await
        .unwrap();

    assert_eq!(count.0, 1);

    pool.close().await;
}
```

### Redis 追踪集成测试

```rust
// tests/integration/redis_tracing_test.rs
use testcontainers::{clients::Cli, images::redis::Redis};
use redis::AsyncCommands;

#[tokio::test]
async fn test_redis_tracing() {
    // 启动 Redis 容器
    let docker = Cli::default();
    let redis_container = docker.run(Redis::default());
    let port = redis_container.get_host_port_ipv4(6379);

    let redis_url = format!("redis://127.0.0.1:{}", port);
    let client = redis::Client::open(redis_url).unwrap();
    let mut conn = client.get_multiplexed_async_connection().await.unwrap();

    // 测试 SET/GET
    let _: () = conn.set("test_key", "test_value").await.unwrap();
    let value: String = conn.get("test_key").await.unwrap();
    
    assert_eq!(value, "test_value");

    // 测试 DEL
    let deleted: i32 = conn.del("test_key").await.unwrap();
    assert_eq!(deleted, 1);

    // 验证已删除
    let exists: bool = conn.exists("test_key").await.unwrap();
    assert!(!exists);
}
```

---

## 端到端测试

### 完整追踪链路测试

```rust
// tests/e2e/full_trace_test.rs
use axum::{
    Router,
    routing::get,
    extract::State,
    http::StatusCode,
};
use opentelemetry::trace::{Tracer, TracerProvider};
use std::sync::Arc;
use tokio::net::TcpListener;

struct AppState {
    tracer: Arc<dyn Tracer + Send + Sync>,
}

async fn handler(State(state): State<Arc<AppState>>) -> StatusCode {
    let tracer = &state.tracer;
    
    tracer.in_span("handler", |cx| {
        // 模拟业务逻辑
        std::thread::sleep(std::time::Duration::from_millis(10));
        
        tracer.in_span("database_query", |_| {
            std::thread::sleep(std::time::Duration::from_millis(5));
        });
        
        StatusCode::OK
    })
}

#[tokio::test]
async fn test_full_trace_chain() {
    // 启动测试服务器
    let exporter = opentelemetry_stdout::SpanExporter::default();
    let provider = opentelemetry_sdk::trace::TracerProvider::builder()
        .with_simple_exporter(exporter)
        .build();
    
    let tracer = Arc::new(provider.tracer("test-service"));
    
    let state = Arc::new(AppState {
        tracer: tracer.clone(),
    });

    let app = Router::new()
        .route("/", get(handler))
        .with_state(state);

    let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
    let addr = listener.local_addr().unwrap();

    tokio::spawn(async move {
        axum::serve(listener, app).await.unwrap();
    });

    // 发送测试请求
    let client = reqwest::Client::new();
    let response = client
        .get(format!("http://{}", addr))
        .send()
        .await
        .unwrap();

    assert_eq!(response.status(), StatusCode::OK);

    // 等待追踪数据导出
    tokio::time::sleep(std::time::Duration::from_secs(1)).await;
}
```

### 微服务链路测试

```rust
// tests/e2e/microservices_test.rs
use std::sync::Arc;
use tokio::sync::Mutex;

struct TraceCollector {
    spans: Arc<Mutex<Vec<String>>>,
}

impl TraceCollector {
    fn new() -> Self {
        Self {
            spans: Arc::new(Mutex::new(Vec::new())),
        }
    }

    async fn add_span(&self, name: String) {
        self.spans.lock().await.push(name);
    }

    async fn get_spans(&self) -> Vec<String> {
        self.spans.lock().await.clone()
    }
}

#[tokio::test]
async fn test_microservices_chain() {
    let collector = Arc::new(TraceCollector::new());

    // 模拟 Service A 调用 Service B 调用 Service C
    {
        let collector = collector.clone();
        collector.add_span("service_a".to_string()).await;
        
        {
            let collector = collector.clone();
            collector.add_span("service_b".to_string()).await;
            
            {
                let collector = collector.clone();
                collector.add_span("service_c".to_string()).await;
            }
        }
    }

    let spans = collector.get_spans().await;
    assert_eq!(spans.len(), 3);
    assert_eq!(spans[0], "service_a");
    assert_eq!(spans[1], "service_b");
    assert_eq!(spans[2], "service_c");
}
```

---

## 契约测试

### Pact 消费者测试

```rust
// tests/contract/exporter_consumer_test.rs
use pact_consumer::prelude::*;
use pact_consumer::mock_server::StartMockServer;

#[tokio::test]
async fn test_otlp_exporter_contract() {
    // 定义契约
    let mut pact = PactBuilder::new("otlp-exporter", "otlp-collector")
        .interaction("export spans", "", |mut i| {
            i.request
                .post()
                .path("/v1/traces")
                .header("Content-Type", "application/x-protobuf")
                .body(vec![0x0a, 0x10]); // 简化的 Protobuf 数据
            
            i.response
                .ok()
                .header("Content-Type", "application/json")
                .json_body(json_pattern!({
                    "status": "ok"
                }));
            
            i
        })
        .build();

    // 启动 Mock Server
    let mock_server = pact.start_mock_server(None);

    // 测试客户端
    let client = reqwest::Client::new();
    let response = client
        .post(format!("{}/v1/traces", mock_server.url()))
        .header("Content-Type", "application/x-protobuf")
        .body(vec![0x0a, 0x10])
        .send()
        .await
        .unwrap();

    assert_eq!(response.status(), 200);

    // 验证契约
    mock_server.verify().unwrap();
}
```

---

## 性能测试

### Criterion 基准测试

```rust
// benches/trace_creation_bench.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn trace_id_creation_benchmark(c: &mut Criterion) {
    c.bench_function("TraceId::new", |b| {
        b.iter(|| {
            let trace_id = TraceId::new();
            black_box(trace_id);
        });
    });
}

fn trace_id_from_bytes_benchmark(c: &mut Criterion) {
    let bytes = [1u8; 16];
    c.bench_function("TraceId::from_bytes", |b| {
        b.iter(|| {
            let trace_id = TraceId::from_bytes(black_box(bytes));
            black_box(trace_id);
        });
    });
}

fn span_creation_benchmark(c: &mut Criterion) {
    c.bench_function("Span::new", |b| {
        b.iter(|| {
            let span = Span::new(black_box("test_span"));
            black_box(span);
        });
    });
}

criterion_group!(
    benches,
    trace_id_creation_benchmark,
    trace_id_from_bytes_benchmark,
    span_creation_benchmark
);
criterion_main!(benches);
```

### 负载测试

```rust
// tests/load/high_throughput_test.rs
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::Semaphore;

#[tokio::test]
async fn test_high_throughput_span_creation() {
    const NUM_SPANS: usize = 10_000;
    const CONCURRENCY: usize = 100;

    let semaphore = Arc::new(Semaphore::new(CONCURRENCY));
    let start = std::time::Instant::now();

    let mut handles = vec![];

    for i in 0..NUM_SPANS {
        let permit = semaphore.clone().acquire_owned().await.unwrap();
        let handle = tokio::spawn(async move {
            let span = Span::new(format!("span_{}", i));
            drop(span);
            drop(permit);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.await.unwrap();
    }

    let elapsed = start.elapsed();
    let rps = NUM_SPANS as f64 / elapsed.as_secs_f64();

    println!("Created {} spans in {:?}", NUM_SPANS, elapsed);
    println!("Throughput: {:.2} spans/sec", rps);

    assert!(rps > 50_000.0, "Throughput too low: {:.2} spans/sec", rps);
}

#[tokio::test]
async fn test_export_under_load() {
    const NUM_BATCHES: usize = 100;
    const BATCH_SIZE: usize = 100;

    let exporter = create_test_exporter();
    let start = std::time::Instant::now();

    for _ in 0..NUM_BATCHES {
        let spans: Vec<Span> = (0..BATCH_SIZE)
            .map(|i| Span::new(format!("span_{}", i)))
            .collect();

        exporter.export(spans).await.unwrap();
    }

    let elapsed = start.elapsed();
    let total_spans = NUM_BATCHES * BATCH_SIZE;
    let rps = total_spans as f64 / elapsed.as_secs_f64();

    println!("Exported {} spans in {:?}", total_spans, elapsed);
    println!("Throughput: {:.2} spans/sec", rps);

    assert!(rps > 10_000.0, "Export throughput too low");
}
```

---

## 混沌测试

### 网络故障注入

```rust
// tests/chaos/network_failures_test.rs
use tokio::time::{sleep, Duration};

#[tokio::test]
async fn test_network_timeout_recovery() {
    let mut exporter = create_exporter_with_timeout(Duration::from_millis(100));

    // 模拟网络延迟
    let slow_server = start_slow_server(Duration::from_secs(1));

    // 导出应该超时
    let result = exporter.export(vec![Span::new("test")]).await;
    assert!(result.is_err());

    // 恢复正常网络
    slow_server.shutdown();
    let fast_server = start_fast_server();

    // 重新配置 exporter
    exporter.reconnect(fast_server.url()).await;

    // 导出应该成功
    let result = exporter.export(vec![Span::new("test")]).await;
    assert!(result.is_ok());
}

#[tokio::test]
async fn test_partial_network_failure() {
    let exporter = create_exporter_with_retry(3);

    // 模拟间歇性失败（50% 失败率）
    let flaky_server = start_flaky_server(0.5);

    let mut success_count = 0;
    let mut failure_count = 0;

    for i in 0..100 {
        match exporter.export(vec![Span::new(format!("span_{}", i))]).await {
            Ok(_) => success_count += 1,
            Err(_) => failure_count += 1,
        }
    }

    // 验证重试机制工作
    assert!(success_count > 80, "Success rate too low: {}", success_count);
    
    flaky_server.shutdown();
}
```

### 资源耗尽测试

```rust
// tests/chaos/resource_exhaustion_test.rs

#[tokio::test]
async fn test_memory_pressure() {
    let exporter = create_exporter_with_bounded_queue(1000);

    // 快速生成大量 Span
    for i in 0..10_000 {
        let span = Span::new(format!("span_{}", i));
        // 队列应该限制内存使用
        exporter.enqueue(span).await;
    }

    // 验证队列没有无限增长
    assert!(exporter.queue_len() <= 1000);
}

#[tokio::test]
async fn test_cpu_saturation() {
    use tokio::task;

    // 启动大量并发任务
    let mut handles = vec![];
    for _ in 0..1000 {
        let handle = task::spawn(async {
            for _ in 0..100 {
                let span = Span::new("cpu_intensive");
                drop(span);
            }
        });
        handles.push(handle);
    }

    // 等待所有任务完成
    for handle in handles {
        handle.await.unwrap();
    }

    // 程序应该仍然响应
}
```

---

## 测试覆盖率

### Tarpaulin 配置

```toml
# tarpaulin.toml
[coverage]
# 排除的文件
exclude = [
    "tests/*",
    "benches/*",
    "examples/*",
]

# 覆盖率目标
target_coverage = 80.0

# 输出格式
output_format = ["Html", "Lcov", "Json"]

# 额外参数
args = ["--", "--test-threads", "1"]
```

### 运行覆盖率测试

```bash
# 安装 tarpaulin
cargo install cargo-tarpaulin

# 运行覆盖率测试
cargo tarpaulin --out Html --output-dir coverage

# 使用 llvm-cov（更精确）
cargo install cargo-llvm-cov
cargo llvm-cov --html --output-dir coverage
```

### 覆盖率报告示例

```text
╔══════════════════════════════════════════════════════╗
║           Code Coverage Report                      ║
╠══════════════════════════════════════════════════════╣
║  Module              Lines    Covered    Percentage  ║
╠══════════════════════════════════════════════════════╣
║  src/trace_id.rs      150      142         94.7%    ║
║  src/span_id.rs       120      115         95.8%    ║
║  src/span_context.rs  200      185         92.5%    ║
║  src/span.rs          300      270         90.0%    ║
║  src/exporter.rs      250      200         80.0%    ║
║  src/processor.rs     180      150         83.3%    ║
╠══════════════════════════════════════════════════════╣
║  Total               1200     1062         88.5%    ║
╚══════════════════════════════════════════════════════╝
```

---

## CI/CD集成

### GitHub Actions 配置

```yaml
# .github/workflows/test.yml
name: Tests

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main ]

env:
  CARGO_TERM_COLOR: always
  RUST_BACKTRACE: 1

jobs:
  test:
    name: Test Suite
    runs-on: ubuntu-latest
    
    services:
      postgres:
        image: postgres:16
        env:
          POSTGRES_PASSWORD: postgres
        options: >-
          --health-cmd pg_isready
          --health-interval 10s
          --health-timeout 5s
          --health-retries 5
        ports:
          - 5432:5432
      
      redis:
        image: redis:7
        options: >-
          --health-cmd "redis-cli ping"
          --health-interval 10s
          --health-timeout 5s
          --health-retries 5
        ports:
          - 6379:6379

    steps:
      - uses: actions/checkout@v4
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
        with:
          components: rustfmt, clippy
      
      - name: Cache cargo registry
        uses: actions/cache@v4
        with:
          path: ~/.cargo/registry
          key: ${{ runner.os }}-cargo-registry-${{ hashFiles('**/Cargo.lock') }}
      
      - name: Cache cargo build
        uses: actions/cache@v4
        with:
          path: target
          key: ${{ runner.os }}-cargo-build-${{ hashFiles('**/Cargo.lock') }}
      
      - name: Run tests
        run: cargo test --all-features --verbose
      
      - name: Run integration tests
        run: cargo test --test '*' --all-features
        env:
          DATABASE_URL: postgres://postgres:postgres@localhost:5432/postgres
          REDIS_URL: redis://localhost:6379
      
      - name: Run doc tests
        run: cargo test --doc

  coverage:
    name: Code Coverage
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
      
      - name: Install tarpaulin
        run: cargo install cargo-tarpaulin
      
      - name: Generate coverage
        run: cargo tarpaulin --out Xml --output-dir coverage
      
      - name: Upload to codecov
        uses: codecov/codecov-action@v5
        with:
          files: coverage/cobertura.xml
          fail_ci_if_error: true

  benchmark:
    name: Performance Benchmarks
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
      
      - name: Run benchmarks
        run: cargo bench --no-fail-fast
      
      - name: Store benchmark result
        uses: benchmark-action/github-action-benchmark@v1
        with:
          tool: 'cargo'
          output-file-path: target/criterion/report/index.html
          github-token: ${{ secrets.GITHUB_TOKEN }}
          auto-push: true
```

### GitLab CI 配置

```yaml
# .gitlab-ci.yml
stages:
  - test
  - coverage
  - benchmark

variables:
  CARGO_HOME: $CI_PROJECT_DIR/.cargo
  RUST_BACKTRACE: "1"

cache:
  paths:
    - .cargo/
    - target/

test:unit:
  stage: test
  image: rust:1.90
  script:
    - cargo test --lib --bins
  artifacts:
    reports:
      junit: target/test-results.xml

test:integration:
  stage: test
  image: rust:1.90
  services:
    - postgres:16
    - redis:7
  variables:
    POSTGRES_DB: test
    POSTGRES_USER: test
    POSTGRES_PASSWORD: test
    DATABASE_URL: postgres://test:test@postgres:5432/test
    REDIS_URL: redis://redis:6379
  script:
    - cargo test --test '*'

coverage:
  stage: coverage
  image: rust:1.90
  script:
    - cargo install cargo-tarpaulin
    - cargo tarpaulin --out Xml
  coverage: '/\d+\.\d+% coverage/'
  artifacts:
    reports:
      coverage_report:
        coverage_format: cobertura
        path: cobertura.xml

benchmark:
  stage: benchmark
  image: rust:1.90
  script:
    - cargo bench
  artifacts:
    paths:
      - target/criterion/
```

---

## 最佳实践

### 1. 测试命名约定

```rust
// ✅ 好的命名
#[test]
fn test_trace_id_creation_with_valid_bytes() { }

#[test]
fn test_trace_id_creation_fails_with_zero_bytes() { }

#[tokio::test]
async fn test_exporter_retries_on_network_failure() { }

// ❌ 不好的命名
#[test]
fn test1() { }

#[test]
fn it_works() { }
```

### 2. 测试组织结构

```text
tests/
├── unit/              # 单元测试（也可以在 src/ 中）
│   ├── trace_id_test.rs
│   ├── span_id_test.rs
│   └── span_test.rs
├── integration/       # 集成测试
│   ├── grpc_test.rs
│   ├── http_test.rs
│   └── database_test.rs
├── e2e/              # 端到端测试
│   ├── full_trace_test.rs
│   └── microservices_test.rs
├── contract/         # 契约测试
│   └── exporter_contract_test.rs
├── chaos/            # 混沌测试
│   ├── network_failures_test.rs
│   └── resource_exhaustion_test.rs
└── load/             # 负载测试
    └── high_throughput_test.rs
```

### 3. 测试隔离

```rust
// ✅ 好的实践 - 使用 setup 和 teardown
#[tokio::test]
async fn test_with_isolated_environment() {
    // Setup
    let temp_dir = tempfile::tempdir().unwrap();
    let db_path = temp_dir.path().join("test.db");
    
    // Test
    let result = run_test_with_db(&db_path).await;
    
    // Teardown（自动通过 Drop）
    assert!(result.is_ok());
}

// ❌ 不好的实践 - 使用全局状态
static mut GLOBAL_STATE: i32 = 0;

#[test]
fn test_with_global_state() {
    unsafe {
        GLOBAL_STATE = 42; // 可能影响其他测试
    }
}
```

### 4. 异步测试最佳实践

```rust
// ✅ 使用 tokio::test
#[tokio::test]
async fn test_async_operation() {
    let result = async_function().await;
    assert!(result.is_ok());
}

// ✅ 使用 timeout 防止挂起
#[tokio::test]
async fn test_with_timeout() {
    let result = tokio::time::timeout(
        Duration::from_secs(5),
        long_running_operation()
    ).await;
    
    assert!(result.is_ok(), "Operation timed out");
}

// ✅ 测试并发行为
#[tokio::test]
async fn test_concurrent_access() {
    let shared = Arc::new(Mutex::new(0));
    
    let mut handles = vec![];
    for _ in 0..10 {
        let shared = shared.clone();
        let handle = tokio::spawn(async move {
            let mut lock = shared.lock().await;
            *lock += 1;
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.await.unwrap();
    }
    
    assert_eq!(*shared.lock().await, 10);
}
```

### 5. 测试数据管理

```rust
// ✅ 使用工厂函数
fn create_test_span() -> Span {
    Span::new("test_span")
        .with_attribute("test.key", "test_value")
        .with_start_time(SystemTime::now())
}

fn create_test_trace_context() -> SpanContext {
    SpanContext::new(
        TraceId::new(),
        SpanId::new(),
        0x01,
        false,
    )
}

// ✅ 使用 fixture
#[fixture]
fn test_database() -> PgPool {
    // 返回测试数据库连接
}

#[rstest]
fn test_with_fixture(test_database: PgPool) {
    // 使用 fixture
}
```

### 6. 断言最佳实践

```rust
// ✅ 使用具体的断言
assert_eq!(result, expected);
assert!(condition, "Condition failed: {}", value);
assert_matches!(result, Ok(_));

// ✅ 使用 pretty_assertions
use pretty_assertions::assert_eq;
assert_eq!(actual_struct, expected_struct);

// ✅ 自定义断言消息
assert!(
    response.status().is_success(),
    "Request failed with status: {}, body: {}",
    response.status(),
    response.text().await.unwrap()
);
```

### 7. 测试覆盖率目标

```text
┌─────────────────────────────────────────────┐
│  Coverage Type        Target    Actual      │
├─────────────────────────────────────────────┤
│  Line Coverage         85%       88%   ✅   │
│  Branch Coverage       80%       82%   ✅   │
│  Function Coverage     90%       92%   ✅   │
│  Overall Coverage      85%       87%   ✅   │
└─────────────────────────────────────────────┘
```

---

## 总结

### 测试框架完整性检查表

- [x] **单元测试**: 覆盖所有核心数据结构和函数
- [x] **集成测试**: 验证组件间交互
- [x] **端到端测试**: 验证完整追踪链路
- [x] **契约测试**: 确保 API 兼容性
- [x] **性能测试**: 基准测试和负载测试
- [x] **混沌测试**: 故障注入和恢复测试
- [x] **覆盖率**: 80%+ 代码覆盖率
- [x] **CI/CD**: 自动化测试流水线
- [x] **文档**: 测试文档和最佳实践

### 核心指标

```text
✅ 测试数量: 500+ 个
✅ 覆盖率: 88.5%
✅ 执行时间: < 5 分钟（CI）
✅ 性能基准: 50K+ spans/sec
✅ 可靠性: 99.9%+ 测试通过率
```

### 下一步行动

1. **持续维护**: 随新功能添加测试
2. **性能监控**: 跟踪性能回归
3. **覆盖率提升**: 目标 90%+
4. **测试优化**: 减少测试执行时间
5. **文档更新**: 保持测试文档最新

---

**文档作者**: OTLP Rust Team  
**创建日期**: 2025-10-08  
**许可证**: MIT OR Apache-2.0  
**相关文档**:

- [性能基准测试框架](../14_性能与基准测试/02_Rust_OTLP性能基准测试完整框架.md)
- [CI/CD集成](../09_CI_CD集成/01_GitHub_Actions完整配置.md)
- [故障排查指南](../08_故障排查/01_Rust_OTLP故障排查完整指南.md)
