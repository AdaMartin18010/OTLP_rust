# Baggage - Rust 完整实现指南

## 📋 目录

- [Baggage - Rust 完整实现指南](#baggage---rust-完整实现指南)
  - [📋 目录](#-目录)
  - [核心概念](#核心概念)
  - [Baggage 规范](#baggage-规范)
    - [**格式**](#格式)
  - [Rust 实现](#rust-实现)
    - [基础用法](#基础用法)
      - [**创建和读取 Baggage**](#创建和读取-baggage)
      - [**Builder 模式**](#builder-模式)
      - [**遍历 Baggage**](#遍历-baggage)
    - [跨服务传播](#跨服务传播)
      - [**HTTP 客户端（inject）**](#http-客户端inject)
      - [**HTTP 服务端（extract）**](#http-服务端extract)
    - [与 Trace 集成](#与-trace-集成)
      - [**将 Baggage 附加到 Span**](#将-baggage-附加到-span)
      - [**动态日志字段**](#动态日志字段)
  - [安全性](#安全性)
    - [**大小限制**](#大小限制)
    - [**敏感数据过滤**](#敏感数据过滤)
    - [**白名单模式**](#白名单模式)
  - [最佳实践](#最佳实践)
    - [✅ **推荐**](#-推荐)
    - [❌ **避免**](#-避免)
  - [依赖库](#依赖库)
    - [**核心依赖**](#核心依赖)
    - [**HTTP 集成**](#http-集成)
  - [总结](#总结)

---

## 核心概念

**Baggage** 是 W3C 标准（[W3C Baggage](https://www.w3.org/TR/baggage/)），用于在分布式系统中传播业务上下文数据：

```text
HTTP Header:
baggage: user_id=123,region=us-west-2,experiment=feature-a
```

**与 Trace 的区别**：

| 维度 | Trace Context | Baggage |
|------|--------------|---------|
| **用途** | 追踪调用链 | 传播业务数据 |
| **数据** | trace-id、span-id | 任意键值对 |
| **大小** | 固定（64 字节） | 可变（最大 8192 字节） |
| **可见性** | 后端可见 | 应用和后端都可见 |

---

## Baggage 规范

### **格式**

```text
baggage: key1=value1,key2=value2;prop1=val1;prop2=val2
         │     │      │     │     │                   │
         │     │      │     │     └─ properties      ─┘
         │     │      │     └─ value
         │     │      └─ key
         │     └─ value
         └─ key
```

**规则**：

- 键：ASCII 字母、数字、`-`、`_`、`*`、`/`
- 值：可打印 ASCII 字符（除 `,`、`;`、`=`）
- 属性：可选元数据（如 `metadata=opaque`）
- 最大大小：8192 字节（整个 Header）

---

## Rust 实现

### 基础用法

#### **创建和读取 Baggage**

```rust
use opentelemetry::baggage::Baggage;
use opentelemetry::{Context, KeyValue};

fn basic_baggage() {
    // 1. 创建 Baggage
    let mut baggage = Baggage::new();
    baggage.insert("user_id".to_string(), "123".to_string());
    baggage.insert("region".to_string(), "us-west-2".to_string());
    baggage.insert("experiment".to_string(), "feature-a".to_string());
    
    // 2. 关联到 Context
    let cx = Context::current().with_baggage(baggage);
    
    // 3. 从 Context 读取 Baggage
    let baggage = cx.baggage();
    if let Some(user_id) = baggage.get("user_id") {
        println!("User ID: {}", user_id);
    }
}
```

---

#### **Builder 模式**

```rust
use opentelemetry::baggage::BaggageExt;

fn builder_baggage() {
    let cx = Context::current()
        .with_baggage_value("user_id", "123")
        .with_baggage_value("region", "us-west-2")
        .with_baggage_value("experiment", "feature-a");
    
    // 读取
    let user_id = cx.baggage().get("user_id").unwrap();
    println!("User ID: {}", user_id);
}
```

---

#### **遍历 Baggage**

```rust
fn iterate_baggage(cx: &Context) {
    let baggage = cx.baggage();
    
    for (key, (value, _metadata)) in baggage.iter() {
        println!("{} = {}", key, value);
    }
}

// 输出:
// user_id = 123
// region = us-west-2
// experiment = feature-a
```

---

### 跨服务传播

#### **HTTP 客户端（inject）**

```rust
use reqwest::Client;
use opentelemetry::global;
use opentelemetry::propagation::TextMapPropagator;

async fn http_client_with_baggage() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 设置 Baggage
    let cx = Context::current()
        .with_baggage_value("user_id", "123")
        .with_baggage_value("region", "us-west-2")
        .with_baggage_value("tenant_id", "acme-corp");
    
    // 2. 注入到 HTTP Header
    let propagator = global::get_text_map_propagator(|prop| prop.clone());
    let mut headers = reqwest::header::HeaderMap::new();
    propagator.inject_context(&cx, &mut HeaderInjector(&mut headers));
    
    // 3. 发送请求
    let client = Client::new();
    let response = client
        .get("http://example.com/api")
        .headers(headers)
        .send()
        .await?;
    
    println!("Response: {:?}", response.status());
    Ok(())
}

struct HeaderInjector<'a>(&'a mut reqwest::header::HeaderMap);

impl<'a> opentelemetry::propagation::Injector for HeaderInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        if let Ok(name) = reqwest::header::HeaderName::from_bytes(key.as_bytes()) {
            if let Ok(val) = reqwest::header::HeaderValue::from_str(&value) {
                self.0.insert(name, val);
            }
        }
    }
}
```

**发送的 HTTP Header**：

```text
baggage: user_id=123,region=us-west-2,tenant_id=acme-corp
```

---

#### **HTTP 服务端（extract）**

```rust
use axum::{
    extract::Request,
    http::HeaderMap,
    middleware::{self, Next},
    response::Response,
};

async fn baggage_middleware(
    headers: HeaderMap,
    request: Request,
    next: Next,
) -> Response {
    // 1. 从 HTTP Header 提取 Baggage
    let propagator = global::get_text_map_propagator(|prop| prop.clone());
    let cx = propagator.extract(&HeaderExtractor(&headers));
    
    // 2. 读取 Baggage
    let baggage = cx.baggage();
    if let Some(user_id) = baggage.get("user_id") {
        tracing::info!(user_id = %user_id, "Processing request");
    }
    
    // 3. 在 Context 作用域内处理请求
    let response = cx.attach(|| async {
        next.run(request).await
    }).await;
    
    response
}

struct HeaderExtractor<'a>(&'a HeaderMap);

impl<'a> opentelemetry::propagation::Extractor for HeaderExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.0.get(key).and_then(|v| v.to_str().ok())
    }

    fn keys(&self) -> Vec<&str> {
        self.0.keys().map(|k| k.as_str()).collect()
    }
}
```

---

### 与 Trace 集成

#### **将 Baggage 附加到 Span**

```rust
use opentelemetry::trace::{Tracer, TracerProvider};

async fn trace_with_baggage() {
    // 1. 设置 Baggage
    let cx = Context::current()
        .with_baggage_value("user_id", "123")
        .with_baggage_value("tenant_id", "acme-corp");
    
    // 2. 创建 Span
    let tracer = global::tracer("service");
    let span = tracer.start("operation");
    let cx = cx.with_span(span);
    
    // 3. 将 Baggage 作为 Span 属性
    let span = cx.span();
    let baggage = cx.baggage();
    
    for (key, (value, _)) in baggage.iter() {
        span.set_attribute(KeyValue::new(
            format!("baggage.{}", key),
            value.clone()
        ));
    }
    
    // Span 现在包含:
    // baggage.user_id = "123"
    // baggage.tenant_id = "acme-corp"
}
```

---

#### **动态日志字段**

```rust
#[tracing::instrument(fields(
    user_id = %cx.baggage().get("user_id").unwrap_or(&"unknown".to_string()),
    tenant_id = %cx.baggage().get("tenant_id").unwrap_or(&"unknown".to_string()),
))]
async fn process_request(cx: Context) {
    // 日志会自动包含 Baggage 数据
    tracing::info!("Processing request");
}
```

---

## 安全性

### **大小限制**

```rust
fn check_baggage_size(baggage: &Baggage) -> Result<(), String> {
    // W3C 规范：最大 8192 字节
    let serialized = format!("{:?}", baggage);  // 简化示例
    
    if serialized.len() > 8192 {
        return Err(format!(
            "Baggage too large: {} bytes (max 8192)",
            serialized.len()
        ));
    }
    
    Ok(())
}
```

---

### **敏感数据过滤**

```rust
const SENSITIVE_KEYS: &[&str] = &["password", "token", "secret", "api_key"];

fn sanitize_baggage(baggage: &mut Baggage) {
    for key in SENSITIVE_KEYS {
        if baggage.get(key).is_some() {
            baggage.remove(key);
            eprintln!("Warning: Removed sensitive key from baggage: {}", key);
        }
    }
}

// 使用
let mut baggage = Baggage::new();
baggage.insert("user_id".to_string(), "123".to_string());
baggage.insert("password".to_string(), "secret123".to_string());

sanitize_baggage(&mut baggage);

// 结果：password 被移除
```

---

### **白名单模式**

```rust
const ALLOWED_KEYS: &[&str] = &["user_id", "tenant_id", "region", "experiment"];

fn filter_baggage(baggage: &Baggage) -> Baggage {
    let mut filtered = Baggage::new();
    
    for (key, (value, metadata)) in baggage.iter() {
        if ALLOWED_KEYS.contains(&key.as_str()) {
            filtered.insert_with_metadata(key.clone(), value.clone(), metadata.clone());
        }
    }
    
    filtered
}
```

---

## 最佳实践

### ✅ **推荐**

1. **使用场景**：
   - 用户身份（user_id、tenant_id）
   - 功能开关（experiment=feature-a）
   - 地域信息（region、datacenter）
   - 请求上下文（request_id、session_id）

2. **大小控制**：
   - 总大小 < 4KB（避免接近 8KB 限制）
   - 单个值 < 256 字节
   - 键数量 < 10 个

3. **命名规范**：
   - 使用小写字母 + 下划线：`user_id`
   - 避免特殊字符：`,`、`;`、`=`

4. **安全性**：
   - 不传播敏感信息（密码、令牌）
   - 使用白名单过滤
   - 验证大小限制

5. **与 Trace 集成**：
   - 将关键 Baggage 附加到 Span 属性
   - 使用 `tracing::instrument` 字段

### ❌ **避免**

1. **大数据**：不传播 JSON、base64 编码的大对象
2. **敏感信息**：密码、API 密钥、信用卡号
3. **高基数数据**：UUID、时间戳（除非必需）
4. **过多键**：> 10 个键会增加开销
5. **动态键**：键名应固定，不应动态生成

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

| 功能 | 实现方式 |
|------|---------|
| 创建 Baggage | `Baggage::new()` + `insert()` |
| Builder 模式 | `Context::with_baggage_value()` |
| 读取 Baggage | `cx.baggage().get(key)` |
| 跨服务传播 | `BaggagePropagator` |
| 与 Trace 集成 | 附加为 Span 属性 |
| 安全过滤 | 白名单 + 大小限制 |

**完成**：Context Propagation 模块全部文档已创建！
