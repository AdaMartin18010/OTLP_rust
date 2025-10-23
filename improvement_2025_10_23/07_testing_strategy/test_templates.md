# 📝 测试模板和示例

**用途**: 提供可直接使用的测试模板  
**覆盖**: 各种测试类型和场景

---

## 🧪 单元测试模板

### 基础功能测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_creation() {
        let instance = MyStruct::new();
        assert!(instance.is_valid());
    }
    
    #[test]
    fn test_basic_operation() {
        let mut instance = MyStruct::new();
        let result = instance.process(input);
        assert_eq!(result, expected_output);
    }
}
```

### 错误处理测试

```rust
#[test]
fn test_invalid_input_returns_error() {
    let result = function_under_test(invalid_input);
    
    assert!(result.is_err());
    
    let error = result.unwrap_err();
    assert_eq!(error.kind(), ErrorKind::InvalidInput);
    assert!(error.to_string().contains("expected message"));
}

#[test]
fn test_error_chain() {
    let result = complex_operation();
    
    if let Err(e) = result {
        assert_eq!(e.kind(), ErrorKind::ProcessingError);
        
        // 检查error chain
        let source = e.source().unwrap();
        assert_eq!(source.kind(), ErrorKind::NetworkError);
    }
}
```

### 边界条件测试

```rust
#[test]
fn test_empty_input() {
    let result = process(vec![]);
    assert_eq!(result, ProcessResult::Empty);
}

#[test]
fn test_single_item() {
    let result = process(vec![item]);
    assert_eq!(result.len(), 1);
}

#[test]
fn test_max_capacity() {
    let large_input = vec![item; MAX_SIZE];
    let result = process(large_input);
    assert!(result.is_ok());
}

#[test]
fn test_over_capacity() {
    let too_large = vec![item; MAX_SIZE + 1];
    let result = process(too_large);
    assert!(matches!(result, Err(Error::CapacityExceeded)));
}

#[test]
fn test_zero_value() {
    let result = calculate(0);
    assert_eq!(result, 0);
}

#[test]
fn test_negative_value() {
    let result = calculate(-1);
    assert!(result.is_err());
}
```

---

## ⚡ 异步测试模板

### 基础异步测试

```rust
#[tokio::test]
async fn test_async_operation() {
    let result = async_function().await;
    assert!(result.is_ok());
}

#[tokio::test]
async fn test_async_with_timeout() {
    let result = tokio::time::timeout(
        Duration::from_secs(5),
        slow_operation()
    ).await;
    
    assert!(result.is_ok(), "Operation timed out");
}
```

### 并发测试

```rust
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn test_concurrent_access() {
    let shared = Arc::new(SharedResource::new());
    let mut tasks = vec![];
    
    for i in 0..100 {
        let shared = Arc::clone(&shared);
        tasks.push(tokio::spawn(async move {
            shared.process(i).await
        }));
    }
    
    let results = futures::future::join_all(tasks).await;
    
    assert_eq!(results.len(), 100);
    assert!(results.iter().all(|r| r.is_ok()));
}

#[tokio::test]
async fn test_race_condition() {
    let counter = Arc::new(AtomicUsize::new(0));
    let mut tasks = vec![];
    
    for _ in 0..1000 {
        let counter = Arc::clone(&counter);
        tasks.push(tokio::spawn(async move {
            counter.fetch_add(1, Ordering::SeqCst);
        }));
    }
    
    futures::future::join_all(tasks).await;
    
    assert_eq!(counter.load(Ordering::SeqCst), 1000);
}
```

### 取消和清理测试

```rust
#[tokio::test]
async fn test_cancellation() {
    let task = tokio::spawn(async {
        loop {
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    });
    
    tokio::time::sleep(Duration::from_millis(500)).await;
    task.abort();
    
    assert!(task.await.is_err());
}

#[tokio::test]
async fn test_cleanup_on_drop() {
    let resource = Resource::new().await;
    let id = resource.id();
    
    drop(resource);
    
    // 验证资源已清理
    assert!(!is_resource_active(id).await);
}
```

---

## 🔗 集成测试模板

### HTTP端点测试

```rust
// tests/integration_http.rs
use otlp::*;
use wiremock::{MockServer, Mock, ResponseTemplate};
use wiremock::matchers::{method, path};

#[tokio::test]
async fn test_http_trace_export_success() {
    // 1. 启动mock服务器
    let mock_server = MockServer::start().await;
    
    // 2. 配置mock响应
    Mock::given(method("POST"))
        .and(path("/v1/traces"))
        .respond_with(ResponseTemplate::new(200))
        .mount(&mock_server)
        .await;
    
    // 3. 创建客户端
    let client = EnhancedOtlpClient::builder()
        .with_endpoint(&mock_server.uri())
        .with_http_transport()
        .build()
        .await
        .unwrap();
    
    // 4. 发送数据
    let trace = create_test_trace();
    let result = client.export_traces(trace).await;
    
    // 5. 验证
    assert!(result.is_ok());
}

#[tokio::test]
async fn test_http_export_handles_server_error() {
    let mock_server = MockServer::start().await;
    
    Mock::given(method("POST"))
        .and(path("/v1/traces"))
        .respond_with(ResponseTemplate::new(500))
        .mount(&mock_server)
        .await;
    
    let client = EnhancedOtlpClient::builder()
        .with_endpoint(&mock_server.uri())
        .with_http_transport()
        .build()
        .await
        .unwrap();
    
    let trace = create_test_trace();
    let result = client.export_traces(trace).await;
    
    assert!(result.is_err());
    assert!(matches!(result.unwrap_err(), OtlpError::ServerError(_)));
}
```

### 端到端测试

```rust
#[tokio::test]
async fn test_end_to_end_trace_flow() {
    // 1. 启动测试基础设施
    let backend = start_test_backend().await;
    
    // 2. 创建OTLP客户端
    let client = EnhancedOtlpClient::builder()
        .with_endpoint(&backend.url())
        .with_service_name("test-service")
        .build()
        .await
        .unwrap();
    
    // 3. 创建trace
    let trace_id = TraceId::random();
    let span = Span::builder()
        .with_trace_id(trace_id)
        .with_name("test-operation")
        .with_start_time(SystemTime::now())
        .build();
    
    // 4. 导出
    client.export_traces(vec![span]).await.unwrap();
    
    // 5. 验证后端收到
    let received = backend.wait_for_traces(Duration::from_secs(5)).await;
    assert_eq!(received.len(), 1);
    assert_eq!(received[0].trace_id(), trace_id);
}
```

---

## 🎯 性能基准测试模板

### 吞吐量测试

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};

fn benchmark_throughput(c: &mut Criterion) {
    let mut group = c.benchmark_group("throughput");
    
    for size in [100, 1000, 10000].iter() {
        group.throughput(Throughput::Elements(*size as u64));
        
        group.bench_with_input(
            BenchmarkId::from_parameter(size),
            size,
            |b, &size| {
                b.iter(|| {
                    let data = create_test_data(size);
                    process_batch(black_box(data))
                });
            },
        );
    }
    
    group.finish();
}

criterion_group!(benches, benchmark_throughput);
criterion_main!(benches);
```

### 延迟测试

```rust
fn benchmark_latency(c: &mut Criterion) {
    c.bench_function("single_operation_latency", |b| {
        b.iter(|| {
            let data = create_single_item();
            process_single(black_box(data))
        });
    });
}

fn benchmark_p99_latency(c: &mut Criterion) {
    let mut group = c.benchmark_group("latency_percentiles");
    group.measurement_time(Duration::from_secs(10));
    
    group.bench_function("operation", |b| {
        b.iter(|| async_operation().await);
    });
    
    group.finish();
}
```

### 内存分配测试

```rust
fn benchmark_allocations(c: &mut Criterion) {
    let mut group = c.benchmark_group("allocations");
    
    group.bench_function("with_clone", |b| {
        let data = create_large_data();
        b.iter(|| {
            let cloned = black_box(data.clone());
            process(cloned)
        });
    });
    
    group.bench_function("zero_copy", |b| {
        let data = Arc::new(create_large_data());
        b.iter(|| {
            let reference = black_box(Arc::clone(&data));
            process_ref(&reference)
        });
    });
    
    group.finish();
}
```

---

## 🔍 属性测试模板

### 基础属性测试

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_doesnt_panic(input in any::<Input>()) {
        // 任何输入都不应该panic
        let _ = function_under_test(input);
    }
    
    #[test]
    fn test_idempotent(input in any::<Input>()) {
        // 操作应该是幂等的
        let result1 = function(input.clone());
        let result2 = function(input);
        prop_assert_eq!(result1, result2);
    }
    
    #[test]
    fn test_roundtrip(data in any::<MyData>()) {
        // 序列化往返
        let bytes = serialize(&data)?;
        let recovered = deserialize(&bytes)?;
        prop_assert_eq!(data, recovered);
    }
}
```

### 复杂属性测试

```rust
proptest! {
    #[test]
    fn test_invariants(
        data in prop::collection::vec(any::<Item>(), 0..100)
    ) {
        let processed = process_collection(data);
        
        // 验证不变量
        prop_assert!(processed.is_sorted());
        prop_assert!(processed.iter().all(|x| x.is_valid()));
    }
    
    #[test]
    fn test_bounded_output(
        input in 0..1000i32
    ) {
        let output = compute(input);
        
        // 输出应该在合理范围内
        prop_assert!(output >= 0);
        prop_assert!(output <= input * 2);
    }
}
```

---

## 🎭 Mock和Stub模板

### 使用mockall

```rust
use mockall::*;

#[automock]
pub trait DataStore {
    fn get(&self, key: &str) -> Result<Vec<u8>, Error>;
    fn set(&mut self, key: &str, value: Vec<u8>) -> Result<(), Error>;
    async fn async_get(&self, key: &str) -> Result<Vec<u8>, Error>;
}

#[test]
fn test_with_mock_store() {
    let mut mock = MockDataStore::new();
    
    mock.expect_get()
        .with(eq("test_key"))
        .times(1)
        .returning(|_| Ok(vec![1, 2, 3]));
    
    mock.expect_set()
        .with(eq("test_key"), eq(vec![4, 5, 6]))
        .times(1)
        .returning(|_, _| Ok(()));
    
    let service = Service::new(Box::new(mock));
    
    let value = service.fetch("test_key").unwrap();
    assert_eq!(value, vec![1, 2, 3]);
    
    service.store("test_key", vec![4, 5, 6]).unwrap();
}
```

### 手动Mock

```rust
struct MockTransport {
    sent_data: Arc<Mutex<Vec<Vec<u8>>>>,
    should_fail: bool,
}

impl MockTransport {
    fn new() -> Self {
        Self {
            sent_data: Arc::new(Mutex::new(Vec::new())),
            should_fail: false,
        }
    }
    
    fn with_failure(mut self) -> Self {
        self.should_fail = true;
        self
    }
    
    fn sent_data(&self) -> Vec<Vec<u8>> {
        self.sent_data.lock().unwrap().clone()
    }
}

#[async_trait]
impl Transport for MockTransport {
    async fn send(&self, data: &[u8]) -> Result<(), Error> {
        if self.should_fail {
            return Err(Error::SendFailed);
        }
        
        self.sent_data.lock().unwrap().push(data.to_vec());
        Ok(())
    }
}

#[tokio::test]
async fn test_with_mock_transport() {
    let mock = MockTransport::new();
    let client = Client::with_transport(mock.clone());
    
    client.send(b"test data").await.unwrap();
    
    let sent = mock.sent_data();
    assert_eq!(sent.len(), 1);
    assert_eq!(sent[0], b"test data");
}
```

---

## 🧰 测试辅助函数

### Builder模式

```rust
pub struct TestClientBuilder {
    endpoint: Option<String>,
    timeout: Duration,
    retry_count: usize,
}

impl TestClientBuilder {
    pub fn new() -> Self {
        Self {
            endpoint: None,
            timeout: Duration::from_secs(5),
            retry_count: 3,
        }
    }
    
    pub fn with_endpoint(mut self, endpoint: &str) -> Self {
        self.endpoint = Some(endpoint.to_string());
        self
    }
    
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }
    
    pub fn build(self) -> EnhancedOtlpClient {
        EnhancedOtlpClient::builder()
            .with_endpoint(&self.endpoint.unwrap_or_else(|| "http://localhost:4317".to_string()))
            .with_timeout(self.timeout)
            .build_sync()
            .unwrap()
    }
}
```

### 测试夹具

```rust
pub struct TestFixture {
    pub client: EnhancedOtlpClient,
    pub server: TestServer,
    _cleanup: CleanupGuard,
}

impl TestFixture {
    pub async fn new() -> Self {
        let server = TestServer::start().await;
        let client = EnhancedOtlpClient::builder()
            .with_endpoint(&server.url())
            .build()
            .await
            .unwrap();
        
        Self {
            client,
            server,
            _cleanup: CleanupGuard::new(),
        }
    }
}

#[tokio::test]
async fn test_with_fixture() {
    let fixture = TestFixture::new().await;
    
    let result = fixture.client.send_data(b"test").await;
    assert!(result.is_ok());
    
    let received = fixture.server.received_data().await;
    assert_eq!(received, b"test");
}
```

---

## 📊 测试数据生成

### 随机数据生成

```rust
use fake::{Fake, Faker};
use fake::faker::internet::en::*;

pub fn generate_random_trace() -> Trace {
    let trace_id = TraceId::random();
    let span_count: usize = (1..10).fake();
    
    let spans: Vec<_> = (0..span_count)
        .map(|_| generate_random_span(trace_id))
        .collect();
    
    Trace { trace_id, spans }
}

pub fn generate_random_span(trace_id: TraceId) -> Span {
    Span {
        trace_id,
        span_id: SpanId::random(),
        name: Username().fake(),
        start_time: SystemTime::now(),
        end_time: SystemTime::now() + Duration::from_millis((100..1000).fake()),
    }
}
```

---

## 📝 总结

### 可用模板

- ✅ 单元测试（基础、错误、边界）
- ✅ 异步测试（基础、并发、取消）
- ✅ 集成测试（HTTP、E2E）
- ✅ 性能测试（吞吐、延迟、内存）
- ✅ 属性测试（基础、复杂）
- ✅ Mock测试（mockall、手动）

### 使用指南

1. 复制相应模板
2. 替换占位符
3. 调整断言逻辑
4. 运行并验证

---

**创建者**: AI Assistant  
**创建日期**: 2025年10月23日  
**用途**: 加速测试开发
