# 📋 第27批补充完成 - SDK规范 Context Propagation

**完成时间**: 2025年10月10日  
**模块**: 04_SDK规范/04_Context_Propagation  
**文档数量**: 4个

---

## ✅ 已完成文档

### 1. **Context**

**文件**: `01_Context_Rust完整版.md`

**核心功能**:

- 进程内传播（线程/异步任务）
- 跨服务传播（HTTP Header/gRPC Metadata）
- 不可变存储机制

**关键实现**:

```rust
// 显式传递
async fn handle_request(cx: Context) {
    fetch_data(cx.clone()).await;
}

// 隐式传递（Task-local）
cx.attach(|| async {
    fetch_data().await;  // 自动获取 Context
}).await;

// 异步任务传播
tokio::spawn(async_task().instrument(cx.span().clone()));
```

**技术要点**:

- Context 不可变性（修改创建新实例）
- `Context::current()` 获取当前上下文
- `cx.attach()` 设置 Task-local 作用域
- 跨线程传播（`cx.clone()`）
- 与 tracing 的 `#[instrument]` 集成

---

### 2. **Propagator**

**文件**: `02_Propagator_Rust完整版.md`

**核心功能**:

- TextMapPropagator 接口
- HTTP/gRPC/Kafka 集成
- inject（Context → Carrier）
- extract（Carrier → Context）

**关键实现**:

```rust
// HTTP 客户端 inject
let propagator = global::get_text_map_propagator(|prop| prop.clone());
let mut headers = HeaderMap::new();
propagator.inject_context(&cx, &mut HeaderInjector(&mut headers));

// HTTP 服务端 extract
let parent_cx = propagator.extract(&HeaderExtractor(&headers));
let span = tracer
    .span_builder("incoming-request")
    .with_parent_context(parent_cx)
    .start(&tracer);

// gRPC Metadata inject
propagator.inject_context(&cx, &mut MetadataInjector(request.metadata_mut()));

// Kafka Headers inject
propagator.inject_context(&cx, &mut KafkaHeaderInjector(&mut headers));
```

**技术要点**:

- Injector/Extractor trait 实现
- HTTP Header 映射（reqwest、axum）
- gRPC Metadata 映射（tonic）
- Kafka Message Headers 映射（rdkafka）
- 复合 Propagator（TraceContext + Baggage）

---

### 3. **W3C Trace Context**

**文件**: `03_W3C_TraceContext_Rust完整版.md`

**核心功能**:

- traceparent 规范（version-traceid-spanid-flags）
- tracestate 规范（厂商数据）
- W3C 标准兼容

**关键实现**:

```rust
// traceparent 格式
// 00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01

// 生成 traceparent
let traceparent = format!(
    "00-{:032x}-{:016x}-{:02x}",
    trace_id.to_u128(),
    span_id.to_u64(),
    trace_flags.to_u8()
);

// 解析 traceparent
let parts: Vec<&str> = traceparent.split('-').collect();
let trace_id = TraceId::from_hex(parts[1])?;
let span_id = SpanId::from_hex(parts[2])?;
let flags = u8::from_str_radix(parts[3], 16)?;

// tracestate
let tracestate = TraceState::from_key_value([
    ("vendor1", "value1"),
    ("vendor2", "opaque-data"),
])?;
```

**技术要点**:

- traceparent 字段（version、trace-id、parent-id、trace-flags）
- trace-flags 的 sampled 位（01=采样）
- tracestate 键值对（最多 32 个，每个 512 字节）
- 版本兼容性（仅支持 version 00）
- 无效 traceparent 处理（创建新 root span）

---

### 4. **Baggage**

**文件**: `04_Baggage_Rust完整版.md`

**核心功能**:

- W3C Baggage 规范
- 业务上下文传播
- 与 Trace 集成

**关键实现**:

```rust
// 创建 Baggage
let cx = Context::current()
    .with_baggage_value("user_id", "123")
    .with_baggage_value("region", "us-west-2")
    .with_baggage_value("tenant_id", "acme-corp");

// 读取 Baggage
let baggage = cx.baggage();
if let Some(user_id) = baggage.get("user_id") {
    println!("User ID: {}", user_id);
}

// HTTP Header 格式
// baggage: user_id=123,region=us-west-2,tenant_id=acme-corp

// 附加到 Span
let span = cx.span();
for (key, (value, _)) in baggage.iter() {
    span.set_attribute(KeyValue::new(
        format!("baggage.{}", key),
        value.clone()
    ));
}

// 安全过滤
const ALLOWED_KEYS: &[&str] = &["user_id", "tenant_id", "region"];
let filtered = filter_baggage(&baggage, ALLOWED_KEYS);
```

**技术要点**:

- Baggage vs Trace Context 区别
- 格式：`key1=value1,key2=value2;prop1=val1`
- 大小限制（最大 8192 字节）
- 安全性（白名单过滤、敏感数据检查）
- 使用场景（user_id、tenant_id、experiment）

---

## 🔧 技术栈

### 核心依赖

```toml
[dependencies]
opentelemetry = "0.24"
opentelemetry-sdk = "0.24"
tokio = { version = "1", features = ["full"] }
```

### HTTP 集成

```toml
reqwest = "0.12"
axum = "0.7"
hyper = "1.0"
```

### gRPC 集成

```toml
tonic = "0.12"
```

### 消息队列

```toml
rdkafka = "0.36"        # Kafka
lapin = "2.5"           # RabbitMQ
```

### tracing 集成

```toml
tracing = "0.1"
tracing-subscriber = "0.3"
tracing-opentelemetry = "0.25"
```

---

## 📊 完整数据流

```text
┌─────────────────────────────────────────────────────────┐
│              Service A (HTTP Client)                    │
│  ┌───────────────────────────────────────────────────┐ │
│  │ Context (Trace + Baggage)                         │ │
│  │   - trace_id: 4bf92f3577b34da6a3ce929d0e0e4736    │ │
│  │   - span_id: 00f067aa0ba902b7                     │ │
│  │   - baggage: user_id=123, region=us-west-2        │ │
│  └───────────────────────────────────────────────────┘ │
│                           ↓                             │
│  ┌───────────────────────────────────────────────────┐ │
│  │ Propagator.inject()                               │ │
│  │   → HTTP Headers:                                 │ │
│  │      traceparent: 00-4bf9...-00f0...-01           │ │
│  │      baggage: user_id=123,region=us-west-2        │ │
│  └───────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────┘
                          ↓ (网络传输)
┌─────────────────────────────────────────────────────────┐
│              Service B (HTTP Server)                    │
│  ┌───────────────────────────────────────────────────┐ │
│  │ HTTP Headers:                                     │ │
│  │   traceparent: 00-4bf9...-00f0...-01              │ │
│  │   baggage: user_id=123,region=us-west-2           │ │
│  └───────────────────────────────────────────────────┘ │
│                           ↓                             │
│  ┌───────────────────────────────────────────────────┐ │
│  │ Propagator.extract()                              │ │
│  │   → Context (parent_cx):                          │ │
│  │      - parent_trace_id: 4bf9...                   │ │
│  │      - parent_span_id: 00f0...                    │ │
│  │      - baggage: user_id=123, region=us-west-2     │ │
│  └───────────────────────────────────────────────────┘ │
│                           ↓                             │
│  ┌───────────────────────────────────────────────────┐ │
│  │ Tracer.start_with_parent(parent_cx)               │ │
│  │   → 新 Span (继承 trace_id，新 span_id)           │ │
│  └───────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────┘
```

---

## 🎯 最佳实践总结

### ✅ 推荐

1. **使用 tracing 宏**: `#[instrument]` 自动管理 Context
2. **W3C 标准**: 优先使用 TraceContextPropagator
3. **复合 Propagator**: 同时支持 TraceContext + Baggage
4. **中间件集成**:
   - HTTP: Axum/Actix middleware
   - gRPC: Interceptor
   - Kafka: 自定义 wrapper
5. **Baggage 安全**:
   - 白名单过滤
   - 大小限制 < 4KB
   - 不传播敏感信息
6. **错误处理**: extract 失败时创建新 root span
7. **异步任务**: 使用 `.instrument(span)` 传播 Context
8. **跨线程**: `cx.clone()` 克隆 Context

### ❌ 避免

1. **忘记 inject/extract**: 导致 Trace 断链
2. **修改 trace-id**: trace-id 应保持不变
3. **丢弃 tracestate**: 即使不理解，也应传递
4. **Baggage 过大**: > 8KB 会被截断
5. **敏感数据**: 不在 Baggage 中传播密码/令牌
6. **高基数数据**: Baggage 不应包含 UUID/时间戳
7. **忽略采样标志**: 应根据 `is_sampled()` 决定记录级别

---

## 🚀 下一步

**SDK 规范的 4 个子模块全部完成！** 接下来进入：

### 05_Collector规范

- `01_Collector架构_Rust完整版.md`
- `02_Receivers_Rust完整版.md`
- `03_Processors_Rust完整版.md`
- `04_Exporters_Rust完整版.md`
- `05_Pipeline配置_Rust完整版.md`
- `06_扩展开发_Rust完整版.md`
- `07_性能优化_Rust完整版.md`
- `08_生产部署_Rust完整版.md`

---

## 📈 进度统计

| 模块 | 状态 | 文档数 |
|------|------|--------|
| 01_Tracing_SDK | ✅ 完成 | 6 |
| 02_Metrics_SDK | ✅ 完成 | 5 |
| 03_Logs_SDK | ✅ 完成 | 4 |
| **04_Context_Propagation** | **✅ 完成** | **4** |

**当前总计**: 19/19 完成 (100%)

**04_SDK规范 模块全部完成！** 🎉🎉🎉

---

## 🎊 里程碑达成

### SDK 规范完整实现

OpenTelemetry SDK 规范的所有核心组件已全部完成：

1. **Tracing SDK** (6 篇)
   - TracerProvider、Tracer、Span
   - SpanProcessor、SpanExporter、Sampler

2. **Metrics SDK** (5 篇)
   - MeterProvider、Meter、Instrument
   - MetricReader、MetricExporter

3. **Logs SDK** (4 篇)
   - LoggerProvider、Logger
   - LogRecordProcessor、LogRecordExporter

4. **Context Propagation** (4 篇)
   - Context、Propagator
   - W3C TraceContext、Baggage

**总计**: 19 篇完整的 Rust 实现文档 ✨

---

**恭喜！Context Propagation 模块全部完成！** 🎉  
**恭喜！SDK 规范全部模块完成！** 🎊
