# W3C Trace Context - Rust 完整实现指南

## 📋 目录

- [W3C Trace Context - Rust 完整实现指南](#w3c-trace-context---rust-完整实现指南)
  - [📋 目录](#-目录)
  - [核心概念](#核心概念)
  - [TraceContext 规范](#tracecontext-规范)
    - [**traceparent 格式**](#traceparent-格式)
    - [**trace-flags 详解**](#trace-flags-详解)
    - [**tracestate 格式**](#tracestate-格式)
  - [Rust 实现](#rust-实现)
    - [traceparent 详解](#traceparent-详解)
      - [**生成 traceparent**](#生成-traceparent)
      - [**解析 traceparent**](#解析-traceparent)
    - [tracestate 详解](#tracestate-详解)
      - [**创建 tracestate**](#创建-tracestate)
      - [**解析 tracestate**](#解析-tracestate)
      - [**更新 tracestate**](#更新-tracestate)
    - [完整示例](#完整示例)
      - [**HTTP 服务端完整流程**](#http-服务端完整流程)
      - [**HTTP 客户端完整流程**](#http-客户端完整流程)
  - [兼容性](#兼容性)
    - [**与其他格式共存**](#与其他格式共存)
    - [**处理无效 traceparent**](#处理无效-traceparent)
  - [最佳实践](#最佳实践)
    - [✅ **推荐**](#-推荐)
    - [❌ **避免**](#-避免)
  - [依赖库](#依赖库)
    - [**核心依赖**](#核心依赖)
    - [**HTTP 集成**](#http-集成)
  - [总结](#总结)

---

## 核心概念

**W3C Trace Context** 是分布式追踪的国际标准（[W3C Recommendation](https://www.w3.org/TR/trace-context/)），定义了两个 HTTP Header：

```text
traceparent: 00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01
             ││  │                                │                  ││
             ││  └─ trace-id (32 hex digits)      │                  ││
             ││                                   │                  ││
             ││                                   └─ parent-id       ││
             ││                                      (16 hex digits) ││
             ││                                                      ││
             │└─ version (00)                                        │
             └─ trace-flags (01=sampled)                             ─┘

tracestate: vendor1=value1,vendor2=value2
```

**关键组成**：

- **traceparent**：必需，包含 trace-id、parent-id、flags
- **tracestate**：可选，厂商特定数据

---

## TraceContext 规范

### **traceparent 格式**

```text
version-format = trace-id "-" parent-id "-" trace-flags
```

| 字段 | 长度 | 示例 | 说明 |
|------|------|------|------|
| **version** | 2 hex | `00` | 当前版本为 00 |
| **trace-id** | 32 hex | `4bf92f3577b34da6a3ce929d0e0e4736` | 全局唯一追踪 ID |
| **parent-id** | 16 hex | `00f067aa0ba902b7` | 当前 Span ID |
| **trace-flags** | 2 hex | `01` | 标志位（01=采样） |

---

### **trace-flags 详解**

```text
00000001 (binary)
       │
       └─ sampled (1=采样, 0=不采样)
```

**标志位**：

- **bit 0 (sampled)**：1 表示采样，0 表示不采样
- **bit 1-7**：保留未来使用

---

### **tracestate 格式**

```text
tracestate: vendor1=value1,vendor2=value2
```

**规则**：

- 最多 32 个键值对
- 每个键值对最多 512 字符
- 键：小写字母、数字、`_`、`-`、`*`、`/`
- 值：可打印 ASCII 字符（除 `,` 和 `=`）

---

## Rust 实现

### traceparent 详解

#### **生成 traceparent**

```rust
use opentelemetry::{
    trace::{TraceId, SpanId, TraceFlags, SpanContext},
    Context,
};

fn generate_traceparent() -> String {
    // 1. 生成 Trace ID (128-bit)
    let trace_id = TraceId::from_hex("4bf92f3577b34da6a3ce929d0e0e4736").unwrap();
    
    // 2. 生成 Span ID (64-bit)
    let span_id = SpanId::from_hex("00f067aa0ba902b7").unwrap();
    
    // 3. 设置 Trace Flags (sampled)
    let trace_flags = TraceFlags::SAMPLED;
    
    // 4. 创建 SpanContext
    let span_context = SpanContext::new(
        trace_id,
        span_id,
        trace_flags,
        false,  // is_remote
        Default::default(),  // tracestate
    );
    
    // 5. 生成 traceparent
    format!(
        "00-{:032x}-{:016x}-{:02x}",
        trace_id.to_u128(),
        span_id.to_u64(),
        trace_flags.to_u8()
    )
}

// 输出: 00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01
```

---

#### **解析 traceparent**

```rust
use opentelemetry::trace::{TraceId, SpanId, TraceFlags, SpanContext};

fn parse_traceparent(traceparent: &str) -> Result<SpanContext, String> {
    let parts: Vec<&str> = traceparent.split('-').collect();
    
    if parts.len() != 4 {
        return Err("Invalid traceparent format".to_string());
    }
    
    // 1. 解析 version
    let version = parts[0];
    if version != "00" {
        return Err(format!("Unsupported version: {}", version));
    }
    
    // 2. 解析 trace-id
    let trace_id = TraceId::from_hex(parts[1])
        .map_err(|e| format!("Invalid trace-id: {}", e))?;
    
    // 3. 解析 parent-id
    let span_id = SpanId::from_hex(parts[2])
        .map_err(|e| format!("Invalid span-id: {}", e))?;
    
    // 4. 解析 trace-flags
    let flags = u8::from_str_radix(parts[3], 16)
        .map_err(|e| format!("Invalid trace-flags: {}", e))?;
    let trace_flags = TraceFlags::new(flags);
    
    // 5. 创建 SpanContext
    Ok(SpanContext::new(
        trace_id,
        span_id,
        trace_flags,
        true,  // is_remote (从外部接收)
        Default::default(),
    ))
}

// 使用
let span_context = parse_traceparent(
    "00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01"
).unwrap();

println!("Trace ID: {:?}", span_context.trace_id());
println!("Span ID: {:?}", span_context.span_id());
println!("Sampled: {}", span_context.is_sampled());
```

---

### tracestate 详解

#### **创建 tracestate**

```rust
use opentelemetry::trace::TraceState;

fn create_tracestate() -> TraceState {
    TraceState::from_key_value([
        ("vendor1", "value1"),
        ("vendor2", "opaque-data"),
        ("myvendor", "priority=5,sampled=true"),
    ]).unwrap()
}

// 序列化为字符串
let tracestate = create_tracestate();
let header = tracestate.header();
// 输出: "vendor1=value1,vendor2=opaque-data,myvendor=priority=5,sampled=true"
```

---

#### **解析 tracestate**

```rust
fn parse_tracestate(header: &str) -> Result<TraceState, String> {
    TraceState::from_str(header)
        .map_err(|e| format!("Invalid tracestate: {:?}", e))
}

// 使用
let tracestate = parse_tracestate("vendor1=value1,vendor2=value2").unwrap();

// 获取特定厂商的值
if let Some(value) = tracestate.get("vendor1") {
    println!("vendor1 value: {}", value);
}
```

---

#### **更新 tracestate**

```rust
// 插入新键值对（会放到最前面）
let tracestate = TraceState::from_str("vendor1=value1,vendor2=value2").unwrap();
let updated = tracestate.insert("myvendor", "new-value").unwrap();

// 结果: "myvendor=new-value,vendor1=value1,vendor2=value2"
```

---

### 完整示例

#### **HTTP 服务端完整流程**

```rust
use axum::{
    extract::Request,
    http::HeaderMap,
    middleware::{self, Next},
    response::Response,
    Router,
};
use opentelemetry::{
    trace::{TraceContextExt, Tracer, SpanContext},
    Context,
};

async fn trace_context_middleware(
    headers: HeaderMap,
    request: Request,
    next: Next,
) -> Response {
    // 1. 提取 traceparent
    let traceparent = headers
        .get("traceparent")
        .and_then(|v| v.to_str().ok());
    
    // 2. 提取 tracestate
    let tracestate = headers
        .get("tracestate")
        .and_then(|v| v.to_str().ok());
    
    // 3. 创建 parent SpanContext
    let parent_cx = if let Some(traceparent_str) = traceparent {
        match parse_traceparent(traceparent_str) {
            Ok(span_context) => {
                // 添加 tracestate
                let span_context = if let Some(tracestate_str) = tracestate {
                    if let Ok(ts) = TraceState::from_str(tracestate_str) {
                        span_context.with_trace_state(ts)
                    } else {
                        span_context
                    }
                } else {
                    span_context
                };
                
                Context::current().with_remote_span_context(span_context)
            }
            Err(e) => {
                eprintln!("Failed to parse traceparent: {}", e);
                Context::current()
            }
        }
    } else {
        Context::current()
    };
    
    // 4. 创建子 Span
    let tracer = global::tracer("http-server");
    let span = tracer
        .span_builder("incoming-request")
        .with_parent_context(parent_cx)
        .start(&tracer);
    
    let cx = Context::current_with_span(span);
    
    // 5. 处理请求
    let response = cx.attach(|| async {
        next.run(request).await
    }).await;
    
    response
}

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/api", axum::routing::get(|| async { "OK" }))
        .layer(middleware::from_fn(trace_context_middleware));
    
    axum::Server::bind(&"0.0.0.0:3000".parse().unwrap())
        .serve(app.into_make_service())
        .await
        .unwrap();
}
```

---

#### **HTTP 客户端完整流程**

```rust
use reqwest::Client;

async fn make_traced_request() -> Result<(), Box<dyn std::error::Error>> {
    let client = Client::new();
    
    // 1. 创建 Span
    let tracer = global::tracer("http-client");
    let span = tracer.start("outgoing-request");
    let cx = Context::current_with_span(span);
    
    // 2. 获取 SpanContext
    let span_context = cx.span().span_context();
    
    // 3. 生成 traceparent
    let traceparent = format!(
        "00-{:032x}-{:016x}-{:02x}",
        span_context.trace_id().to_u128(),
        span_context.span_id().to_u64(),
        span_context.trace_flags().to_u8()
    );
    
    // 4. 生成 tracestate（如果存在）
    let tracestate = if !span_context.trace_state().is_empty() {
        Some(span_context.trace_state().header())
    } else {
        None
    };
    
    // 5. 设置 Header
    let mut request_builder = client
        .get("http://example.com/api")
        .header("traceparent", traceparent);
    
    if let Some(ts) = tracestate {
        request_builder = request_builder.header("tracestate", ts);
    }
    
    // 6. 发送请求
    let response = request_builder.send().await?;
    
    println!("Response: {:?}", response.status());
    Ok(())
}
```

---

## 兼容性

### **与其他格式共存**

```rust
use opentelemetry_sdk::propagation::{
    TraceContextPropagator,
    TextMapCompositePropagator,
};

// 同时支持 W3C Trace Context 和 Baggage
let propagator = TextMapCompositePropagator::new(vec![
    Box::new(TraceContextPropagator::new()),
    Box::new(BaggagePropagator::new()),
]);

global::set_text_map_propagator(propagator);
```

---

### **处理无效 traceparent**

```rust
fn safe_parse_traceparent(traceparent: &str) -> Context {
    match parse_traceparent(traceparent) {
        Ok(span_context) => {
            Context::current().with_remote_span_context(span_context)
        }
        Err(e) => {
            eprintln!("Invalid traceparent, creating new root span: {}", e);
            Context::current()
        }
    }
}
```

---

## 最佳实践

### ✅ **推荐**

1. **使用 TraceContextPropagator**：自动处理 W3C 格式
2. **验证 traceparent**：解析失败时创建新 root span
3. **保留 tracestate**：即使不理解，也应传递
4. **采样标志**：检查 `is_sampled()` 决定是否记录详细信息
5. **版本兼容**：仅支持 version `00`，其他版本应忽略

### ❌ **避免**

1. **手动拼接字符串**：使用 Propagator API
2. **修改 trace-id**：trace-id 应保持不变
3. **丢弃 tracestate**：即使不理解，也应传递给下游
4. **忽略采样标志**：应根据标志决定是否记录

---

## 依赖库

### **核心依赖**

```toml
[dependencies]
opentelemetry = "0.24"
opentelemetry-sdk = "0.24"
```

### **HTTP 集成**

```toml
reqwest = "0.12"
axum = "0.7"
```

---

## 总结

| 组件 | 格式 | 示例 |
|------|------|------|
| **traceparent** | `version-traceid-spanid-flags` | `00-4bf9...-00f0...-01` |
| **tracestate** | `key1=value1,key2=value2` | `vendor1=abc,vendor2=xyz` |
| **trace-flags** | 8-bit | `01` (sampled) |

**下一步**：[04_Baggage_Rust完整版.md](./04_Baggage_Rust完整版.md) - 学习如何传播业务数据
