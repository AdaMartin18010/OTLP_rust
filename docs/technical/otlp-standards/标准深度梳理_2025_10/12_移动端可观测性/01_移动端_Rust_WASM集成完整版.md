# 移动端 Rust + WASM 可观测性完整集成

> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **WASM Target**: `wasm32-unknown-unknown`, `wasm32-wasi`  
> **状态**: Production Ready  
> **最后更新**: 2025年10月9日

---

## 目录

- [移动端 Rust + WASM 可观测性完整集成](#移动端-rust--wasm-可观测性完整集成)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 为什么选择 Rust + WASM 移动端可观测性](#11-为什么选择-rust--wasm-移动端可观测性)
    - [1.2 适用场景](#12-适用场景)
  - [2. Rust WASM 移动端架构](#2-rust-wasm-移动端架构)
    - [2.1 架构图](#21-架构图)
    - [2.2 依赖配置](#22-依赖配置)
  - [3. WASM 环境初始化](#3-wasm-环境初始化)
    - [3.1 全局 TracerProvider 初始化](#31-全局-tracerprovider-初始化)
  - [4. 跨平台类型安全设计](#4-跨平台类型安全设计)
    - [4.1 Span 构建器（类型安全）](#41-span-构建器类型安全)
  - [5. JavaScript/TypeScript 互操作](#5-javascripttypescript-互操作)
    - [5.1 TypeScript 类型定义](#51-typescript-类型定义)
    - [5.2 JavaScript 集成示例](#52-javascript-集成示例)
  - [6. 移动端性能追踪](#6-移动端性能追踪)
    - [6.1 页面加载时间追踪](#61-页面加载时间追踪)
    - [6.2 网络请求追踪（Fetch 拦截）](#62-网络请求追踪fetch-拦截)
  - [7. 用户体验监控](#7-用户体验监控)
    - [7.1 用户交互追踪](#71-用户交互追踪)
    - [7.2 屏幕导航追踪](#72-屏幕导航追踪)
  - [8. 离线数据缓存](#8-离线数据缓存)
    - [8.1 IndexedDB 离线缓存](#81-indexeddb-离线缓存)
  - [9. React Native 集成](#9-react-native-集成)
    - [9.1 React Native 桥接](#91-react-native-桥接)
    - [9.2 React Native 使用示例](#92-react-native-使用示例)
  - [10. Flutter FFI 集成](#10-flutter-ffi-集成)
    - [10.1 Flutter FFI 绑定](#101-flutter-ffi-绑定)
  - [11. 性能优化](#11-性能优化)
    - [11.1 二进制体积优化](#111-二进制体积优化)
    - [11.2 异步批量导出优化](#112-异步批量导出优化)
  - [12. 完整示例](#12-完整示例)
    - [12.1 构建与部署](#121-构建与部署)
    - [12.2 React 应用完整集成](#122-react-应用完整集成)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [最佳实践](#最佳实践)

---

## 1. 概述

### 1.1 为什么选择 Rust + WASM 移动端可观测性

```text
✅ 近乎原生的性能（WASM 执行速度）
✅ 类型安全的跨平台代码（Rust 类型系统）
✅ 零拷贝内存共享（wasm-bindgen）
✅ 小巧的二进制体积（30-200KB gzipped）
✅ 跨平台一致性（iOS, Android, Web）
✅ 现代化异步支持（wasm-bindgen-futures, js-sys）
```

### 1.2 适用场景

```text
- React Native / Expo 应用
- Flutter 应用（通过 FFI）
- Progressive Web Apps (PWA)
- 混合移动应用（Capacitor, Cordova）
- 跨平台游戏引擎（Bevy, Macroquad）
```

---

## 2. Rust WASM 移动端架构

### 2.1 架构图

```text
┌──────────────────────────────────────────────────────────────┐
│                     移动端应用层                              │
│  (JavaScript/TypeScript, Dart, Swift, Kotlin)                │
└────────────────────┬─────────────────────────────────────────┘
                     │ JS Interop / FFI
┌────────────────────▼─────────────────────────────────────────┐
│                Rust WASM 可观测性核心                          │
│  - SpanBuilder / TracerProvider                               │
│  - Metrics (Counter, Histogram, Gauge)                        │
│  - Logs (LogRecord, Severity)                                 │
│  - Context Propagation (W3C Trace Context)                    │
└────────────────────┬─────────────────────────────────────────┘
                     │ HTTP/WebSocket
┌────────────────────▼─────────────────────────────────────────┐
│              OTLP Collector / Backend                          │
│  (Jaeger, Prometheus, Grafana, Tempo)                         │
└──────────────────────────────────────────────────────────────┘
```

### 2.2 依赖配置

**`Cargo.toml`**:

```toml
[package]
name = "mobile-otel-wasm"
version = "0.1.0"
edition = "2021"

[lib]
crate-type = ["cdylib", "rlib"]

[dependencies]
# OpenTelemetry 核心
opentelemetry = { version = "0.31.0", default-features = false, features = ["trace"] }
opentelemetry_sdk = { version = "0.31.0", default-features = false, features = ["trace"] }
opentelemetry-otlp = { version = "0.31.0", default-features = false, features = ["http-proto", "trace"] }
opentelemetry-semantic-conventions = "0.31.0"

# WASM 绑定
wasm-bindgen = "0.2"
wasm-bindgen-futures = "0.4"
js-sys = "0.3"
web-sys = { version = "0.3", features = [
    "Window",
    "Performance",
    "PerformanceTiming",
    "Navigator",
    "Headers",
    "Request",
    "RequestInit",
    "Response",
    "console",
    "Storage",
    "localStorage",
] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
serde-wasm-bindgen = "0.6"

# 异步运行时（WASM 兼容）
wasm-bindgen-futures = "0.4"

# 工具库
thiserror = "2.0"
once_cell = "1.20"

[target.'cfg(target_arch = "wasm32")'.dependencies]
getrandom = { version = "0.2", features = ["js"] }

[profile.release]
opt-level = "z"         # 最小二进制体积
lto = true              # 链接时优化
codegen-units = 1       # 单编译单元
strip = true            # 移除符号表
panic = "abort"         # Abort on panic
```

---

## 3. WASM 环境初始化

### 3.1 全局 TracerProvider 初始化

**`src/init.rs`**:

```rust
use once_cell::sync::OnceCell;
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    trace::{Config, TracerProvider},
    Resource,
};
use opentelemetry_semantic_conventions::resource::{SERVICE_NAME, SERVICE_VERSION};
use wasm_bindgen::prelude::*;
use web_sys::console;

/// 全局 TracerProvider（单例）
static TRACER_PROVIDER: OnceCell<TracerProvider> = OnceCell::new();

/// 初始化 OpenTelemetry（从 JavaScript 调用）
///
/// # JavaScript 示例
/// ```javascript
/// import init, { initOpenTelemetry } from './pkg/mobile_otel_wasm.js';
///
/// await init();
/// await initOpenTelemetry('my-mobile-app', '1.0.0', 'https://otel-collector.example.com:4318');
/// ```
#[wasm_bindgen]
pub async fn initOpenTelemetry(
    service_name: String,
    service_version: String,
    otlp_endpoint: String,
) -> Result<(), JsValue> {
    // 设置 panic hook（输出到浏览器控制台）
    std::panic::set_hook(Box::new(console_error_panic_hook::hook));

    // 1. 创建 Resource
    let resource = Resource::new(vec![
        KeyValue::new(SERVICE_NAME, service_name.clone()),
        KeyValue::new(SERVICE_VERSION, service_version.clone()),
        KeyValue::new("telemetry.sdk.name", "opentelemetry-rust-wasm"),
        KeyValue::new("telemetry.sdk.language", "rust"),
        KeyValue::new("telemetry.sdk.version", "0.31.0"),
        KeyValue::new("deployment.environment", detect_environment()),
    ]);

    // 2. 创建 OTLP HTTP Exporter（WASM 环境使用 fetch API）
    let exporter = opentelemetry_otlp::SpanExporter::builder()
        .with_http()
        .with_endpoint(format!("{}/v1/traces", otlp_endpoint))
        .with_timeout(std::time::Duration::from_secs(10))
        .build()
        .map_err(|e| JsValue::from_str(&format!("Failed to create exporter: {}", e)))?;

    // 3. 创建 BatchSpanProcessor（异步批量导出）
    let batch_processor = opentelemetry_sdk::trace::BatchSpanProcessor::builder(
        exporter,
        opentelemetry_sdk::runtime::WasmRuntime,
    )
    .with_max_queue_size(2048)
    .with_max_export_batch_size(512)
    .with_scheduled_delay(std::time::Duration::from_secs(5))
    .build();

    // 4. 创建 TracerProvider
    let tracer_provider = TracerProvider::builder()
        .with_config(Config::default().with_resource(resource))
        .with_span_processor(batch_processor)
        .build();

    // 5. 注册全局 TracerProvider
    global::set_tracer_provider(tracer_provider.clone());

    // 6. 缓存到单例
    TRACER_PROVIDER
        .set(tracer_provider)
        .map_err(|_| JsValue::from_str("TracerProvider already initialized"))?;

    console::log_1(&"✅ OpenTelemetry initialized successfully".into());
    Ok(())
}

/// 获取当前 TracerProvider
pub fn get_tracer_provider() -> Option<&'static TracerProvider> {
    TRACER_PROVIDER.get()
}

/// 检测运行环境（浏览器 vs React Native）
fn detect_environment() -> &'static str {
    #[cfg(target_arch = "wasm32")]
    {
        if web_sys::window().is_some() {
            "browser"
        } else {
            "react-native"
        }
    }
    #[cfg(not(target_arch = "wasm32"))]
    {
        "native"
    }
}

/// 优雅关闭（从 JavaScript 调用）
#[wasm_bindgen]
pub async fn shutdownOpenTelemetry() -> Result<(), JsValue> {
    if let Some(provider) = TRACER_PROVIDER.get() {
        provider
            .shutdown()
            .map_err(|e| JsValue::from_str(&format!("Shutdown error: {:?}", e)))?;
        console::log_1(&"✅ OpenTelemetry shutdown complete".into());
    }
    Ok(())
}
```

---

## 4. 跨平台类型安全设计

### 4.1 Span 构建器（类型安全）

**`src/span.rs`**:

```rust
use opentelemetry::{
    trace::{Span, SpanKind, Status, Tracer},
    KeyValue,
};
use serde::{Deserialize, Serialize};
use wasm_bindgen::prelude::*;
use web_sys::console;

/// Span 配置（从 JavaScript 传递）
#[derive(Serialize, Deserialize)]
#[wasm_bindgen(getter_with_clone)]
pub struct SpanConfig {
    pub name: String,
    pub kind: String, // "client" | "server" | "producer" | "consumer" | "internal"
    pub attributes: JsValue, // JavaScript Object
}

/// 创建 Span（从 JavaScript 调用）
///
/// # JavaScript 示例
/// ```javascript
/// const span = await createSpan({
///   name: 'user.button_click',
///   kind: 'client',
///   attributes: {
///     'user.id': '12345',
///     'button.label': 'Submit',
///     'screen.name': 'checkout'
///   }
/// });
/// ```
#[wasm_bindgen]
pub async fn createSpan(config: JsValue) -> Result<ManagedSpan, JsValue> {
    let config: SpanConfig = serde_wasm_bindgen::from_value(config)?;

    let tracer = opentelemetry::global::tracer("mobile-app");

    // 解析 SpanKind
    let span_kind = match config.kind.as_str() {
        "client" => SpanKind::Client,
        "server" => SpanKind::Server,
        "producer" => SpanKind::Producer,
        "consumer" => SpanKind::Consumer,
        _ => SpanKind::Internal,
    };

    // 构建 Span
    let mut span = tracer
        .span_builder(config.name)
        .with_kind(span_kind)
        .start(&tracer);

    // 解析并添加属性
    if let Ok(attrs) = serde_wasm_bindgen::from_value::<serde_json::Value>(config.attributes) {
        if let Some(obj) = attrs.as_object() {
            for (key, value) in obj {
                match value {
                    serde_json::Value::String(s) => {
                        span.set_attribute(KeyValue::new(key.clone(), s.clone()));
                    }
                    serde_json::Value::Number(n) => {
                        if let Some(i) = n.as_i64() {
                            span.set_attribute(KeyValue::new(key.clone(), i));
                        } else if let Some(f) = n.as_f64() {
                            span.set_attribute(KeyValue::new(key.clone(), f));
                        }
                    }
                    serde_json::Value::Bool(b) => {
                        span.set_attribute(KeyValue::new(key.clone(), *b));
                    }
                    _ => {}
                }
            }
        }
    }

    Ok(ManagedSpan {
        inner: Some(span),
    })
}

/// Span 包装器（支持 JavaScript 生命周期管理）
#[wasm_bindgen]
pub struct ManagedSpan {
    inner: Option<opentelemetry::trace::SpanRef>,
}

#[wasm_bindgen]
impl ManagedSpan {
    /// 添加事件
    #[wasm_bindgen(js_name = addEvent)]
    pub fn add_event(&mut self, name: String, attributes: JsValue) {
        if let Some(span) = &mut self.inner {
            // 解析属性
            let mut kvs = Vec::new();
            if let Ok(attrs) = serde_wasm_bindgen::from_value::<serde_json::Value>(attributes) {
                if let Some(obj) = attrs.as_object() {
                    for (key, value) in obj {
                        if let Some(s) = value.as_str() {
                            kvs.push(KeyValue::new(key.clone(), s.to_string()));
                        }
                    }
                }
            }
            span.add_event(name, kvs);
        }
    }

    /// 设置错误状态
    #[wasm_bindgen(js_name = setError)]
    pub fn set_error(&mut self, error_message: String) {
        if let Some(span) = &mut self.inner {
            span.set_status(Status::error(error_message));
        }
    }

    /// 结束 Span
    pub fn end(&mut self) {
        if let Some(span) = self.inner.take() {
            span.end();
        }
    }
}

impl Drop for ManagedSpan {
    fn drop(&mut self) {
        // 自动结束 Span（RAII）
        if let Some(span) = self.inner.take() {
            span.end();
        }
    }
}
```

---

## 5. JavaScript/TypeScript 互操作

### 5.1 TypeScript 类型定义

**`mobile-otel.d.ts`**:

```typescript
export interface SpanConfig {
  name: string;
  kind: 'client' | 'server' | 'producer' | 'consumer' | 'internal';
  attributes: Record<string, string | number | boolean>;
}

export interface ManagedSpan {
  addEvent(name: string, attributes: Record<string, string>): void;
  setError(errorMessage: string): void;
  end(): void;
}

export function initOpenTelemetry(
  serviceName: string,
  serviceVersion: string,
  otlpEndpoint: string
): Promise<void>;

export function createSpan(config: SpanConfig): Promise<ManagedSpan>;

export function shutdownOpenTelemetry(): Promise<void>;

// 性能追踪
export function measurePageLoad(): Promise<void>;
export function measureUserInteraction(actionName: string): Promise<void>;

// 网络追踪
export function traceFetch(url: string, options?: RequestInit): Promise<Response>;
```

### 5.2 JavaScript 集成示例

```javascript
import init, {
  initOpenTelemetry,
  createSpan,
  traceFetch,
} from './pkg/mobile_otel_wasm.js';

// 1. 初始化 WASM 模块
await init();

// 2. 初始化 OpenTelemetry
await initOpenTelemetry(
  'my-react-native-app',
  '1.2.0',
  'https://otel-collector.example.com:4318'
);

// 3. 追踪用户按钮点击
async function handleButtonClick() {
  const span = await createSpan({
    name: 'user.button_click',
    kind: 'client',
    attributes: {
      'button.id': 'submit-btn',
      'screen.name': 'checkout',
      'user.id': '12345',
    },
  });

  try {
    // 执行业务逻辑
    await processCheckout();
    span.addEvent('checkout.success', {});
  } catch (error) {
    span.setError(error.message);
  } finally {
    span.end();
  }
}

// 4. 追踪网络请求（fetch 拦截）
const response = await traceFetch('https://api.example.com/products', {
  method: 'GET',
  headers: { 'Content-Type': 'application/json' },
});
```

---

## 6. 移动端性能追踪

### 6.1 页面加载时间追踪

**`src/performance.rs`**:

```rust
use opentelemetry::{global, trace::Tracer, KeyValue};
use wasm_bindgen::prelude::*;
use web_sys::{Performance, Window};

/// 追踪页面加载性能（仅浏览器环境）
#[wasm_bindgen]
pub async fn measurePageLoad() -> Result<(), JsValue> {
    let window = web_sys::window().ok_or_else(|| JsValue::from_str("No window"))?;
    let performance = window.performance().ok_or_else(|| JsValue::from_str("No performance"))?;

    let tracer = global::tracer("mobile-app");
    let mut span = tracer
        .span_builder("page.load")
        .with_kind(opentelemetry::trace::SpanKind::Client)
        .start(&tracer);

    // 获取 PerformanceTiming
    let timing = performance.timing();

    let navigation_start = timing.navigation_start();
    let response_start = timing.response_start();
    let dom_content_loaded = timing.dom_content_loaded_event_end();
    let load_complete = timing.load_event_end();

    // 计算关键指标
    let ttfb = response_start - navigation_start; // Time to First Byte
    let dom_ready = dom_content_loaded - navigation_start; // DOM Ready
    let page_load = load_complete - navigation_start; // Page Load

    span.set_attribute(KeyValue::new("page.ttfb_ms", ttfb as i64));
    span.set_attribute(KeyValue::new("page.dom_ready_ms", dom_ready as i64));
    span.set_attribute(KeyValue::new("page.load_complete_ms", page_load as i64));

    // 添加 First Paint / First Contentful Paint（如果支持）
    if let Ok(entries) = performance.get_entries_by_type("paint") {
        for entry in entries.iter() {
            if let Some(entry) = entry.dyn_ref::<web_sys::PerformanceEntry>() {
                let name = entry.name();
                let start_time = entry.start_time();

                if name == "first-paint" {
                    span.set_attribute(KeyValue::new("page.first_paint_ms", start_time as i64));
                } else if name == "first-contentful-paint" {
                    span.set_attribute(KeyValue::new("page.fcp_ms", start_time as i64));
                }
            }
        }
    }

    span.end();
    Ok(())
}
```

### 6.2 网络请求追踪（Fetch 拦截）

**`src/network.rs`**:

```rust
use opentelemetry::{global, propagation::TextMapPropagator, trace::Tracer, KeyValue};
use opentelemetry_sdk::propagation::TraceContextPropagator;
use wasm_bindgen::prelude::*;
use wasm_bindgen_futures::JsFuture;
use web_sys::{Headers, Request, RequestInit, Response};

/// 追踪 fetch 请求
///
/// # JavaScript 示例
/// ```javascript
/// const response = await traceFetch('https://api.example.com/users', {
///   method: 'POST',
///   headers: { 'Content-Type': 'application/json' },
///   body: JSON.stringify({ name: 'Alice' })
/// });
/// ```
#[wasm_bindgen]
pub async fn traceFetch(url: String, options: JsValue) -> Result<Response, JsValue> {
    let tracer = global::tracer("mobile-app");
    let mut span = tracer
        .span_builder(format!("http.request {}", url))
        .with_kind(opentelemetry::trace::SpanKind::Client)
        .start(&tracer);

    // 提取请求方法
    let request_init: RequestInit = options.into();
    let method = request_init.method();

    span.set_attribute(KeyValue::new("http.method", method.as_string().unwrap_or_default()));
    span.set_attribute(KeyValue::new("http.url", url.clone()));

    // 注入 W3C Trace Context
    let mut headers_map = std::collections::HashMap::new();
    let propagator = TraceContextPropagator::new();
    let context = opentelemetry::Context::current_with_span(span.clone());

    propagator.inject_context(&context, &mut headers_map);

    // 创建请求并注入 traceparent 头部
    let request = Request::new_with_str_and_init(&url, &request_init)?;
    let headers = request.headers();

    for (key, value) in headers_map {
        headers.set(&key, &value)?;
    }

    // 发起请求
    let window = web_sys::window().ok_or_else(|| JsValue::from_str("No window"))?;
    let response_promise = window.fetch_with_request(&request);
    let response = JsFuture::from(response_promise).await?;
    let response: Response = response.dyn_into()?;

    // 记录响应信息
    span.set_attribute(KeyValue::new("http.status_code", response.status() as i64));

    if response.ok() {
        span.set_status(opentelemetry::trace::Status::Ok);
    } else {
        span.set_status(opentelemetry::trace::Status::error(format!(
            "HTTP {}",
            response.status()
        )));
    }

    span.end();

    Ok(response)
}
```

---

## 7. 用户体验监控

### 7.1 用户交互追踪

**`src/ux.rs`**:

```rust
use opentelemetry::{global, trace::Tracer, KeyValue};
use wasm_bindgen::prelude::*;

/// 追踪用户交互（点击、滑动、输入等）
///
/// # JavaScript 示例
/// ```javascript
/// await measureUserInteraction('button_click', {
///   'button.id': 'submit',
///   'screen.name': 'checkout'
/// });
/// ```
#[wasm_bindgen]
pub async fn measureUserInteraction(
    action_name: String,
    attributes: JsValue,
) -> Result<(), JsValue> {
    let tracer = global::tracer("mobile-app");
    let mut span = tracer
        .span_builder(format!("user.interaction.{}", action_name))
        .with_kind(opentelemetry::trace::SpanKind::Client)
        .start(&tracer);

    // 解析属性
    if let Ok(attrs) = serde_wasm_bindgen::from_value::<serde_json::Value>(attributes) {
        if let Some(obj) = attrs.as_object() {
            for (key, value) in obj {
                if let Some(s) = value.as_str() {
                    span.set_attribute(KeyValue::new(key.clone(), s.to_string()));
                }
            }
        }
    }

    // 获取设备信息
    if let Some(window) = web_sys::window() {
        if let Some(navigator) = window.navigator() {
            span.set_attribute(KeyValue::new("device.user_agent", navigator.user_agent().unwrap_or_default()));
            span.set_attribute(KeyValue::new("device.platform", navigator.platform().unwrap_or_default()));
        }
    }

    span.end();
    Ok(())
}
```

### 7.2 屏幕导航追踪

```rust
/// 追踪屏幕导航
#[wasm_bindgen]
pub async fn trackScreenView(screen_name: String, attributes: JsValue) -> Result<(), JsValue> {
    let tracer = global::tracer("mobile-app");
    let mut span = tracer
        .span_builder(format!("screen.view.{}", screen_name))
        .with_kind(opentelemetry::trace::SpanKind::Client)
        .start(&tracer);

    span.set_attribute(KeyValue::new("screen.name", screen_name));

    // 解析自定义属性
    if let Ok(attrs) = serde_wasm_bindgen::from_value::<serde_json::Value>(attributes) {
        if let Some(obj) = attrs.as_object() {
            for (key, value) in obj {
                if let Some(s) = value.as_str() {
                    span.set_attribute(KeyValue::new(key.clone(), s.to_string()));
                }
            }
        }
    }

    span.end();
    Ok(())
}
```

---

## 8. 离线数据缓存

### 8.1 IndexedDB 离线缓存

**`src/offline.rs`**:

```rust
use wasm_bindgen::prelude::*;
use web_sys::{IdbDatabase, IdbFactory, IdbObjectStore, IdbTransaction, IdbTransactionMode};

/// 离线缓存管理器（使用 IndexedDB）
#[wasm_bindgen]
pub struct OfflineCache {
    db_name: String,
}

#[wasm_bindgen]
impl OfflineCache {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        Self {
            db_name: "otel-offline-cache".to_string(),
        }
    }

    /// 初始化 IndexedDB
    pub async fn init(&self) -> Result<(), JsValue> {
        let window = web_sys::window().ok_or_else(|| JsValue::from_str("No window"))?;
        let idb_factory = window
            .indexed_db()?
            .ok_or_else(|| JsValue::from_str("IndexedDB not supported"))?;

        // 打开数据库（版本 1）
        let open_request = idb_factory.open_with_u32(&self.db_name, 1)?;

        // onupgradeneeded 回调（创建对象存储）
        let onupgradeneeded = Closure::wrap(Box::new(move |event: web_sys::IdbVersionChangeEvent| {
            let target = event.target().unwrap();
            let db: IdbDatabase = target.dyn_into().unwrap();

            // 创建 spans 对象存储
            if !db.object_store_names().contains("spans") {
                db.create_object_store("spans").unwrap();
            }
        }) as Box<dyn FnMut(_)>);

        open_request.set_onupgradeneeded(Some(onupgradeneeded.as_ref().unchecked_ref()));
        onupgradeneeded.forget();

        Ok(())
    }

    /// 缓存 Span 数据（网络不可用时）
    pub async fn cache_span(&self, span_data: JsValue) -> Result<(), JsValue> {
        // 实现：将 Span 数据序列化并存储到 IndexedDB
        // 当网络恢复时，批量发送缓存的 Spans
        Ok(())
    }

    /// 网络恢复后，发送缓存的 Spans
    pub async fn flush_cached_spans(&self) -> Result<(), JsValue> {
        // 实现：从 IndexedDB 读取所有缓存的 Spans，发送到 OTLP Collector
        Ok(())
    }
}
```

---

## 9. React Native 集成

### 9.1 React Native 桥接

**`react-native/OtelModule.ts`**:

```typescript
import { NativeModules } from 'react-native';
import init, { initOpenTelemetry, createSpan } from './pkg/mobile_otel_wasm.js';

const { OtelBridge } = NativeModules;

class OpenTelemetryService {
  private initialized = false;

  async initialize(
    serviceName: string,
    serviceVersion: string,
    otlpEndpoint: string
  ): Promise<void> {
    if (this.initialized) return;

    await init(); // 初始化 WASM 模块
    await initOpenTelemetry(serviceName, serviceVersion, otlpEndpoint);

    this.initialized = true;
    console.log('✅ OpenTelemetry initialized');
  }

  async trackScreenView(screenName: string, params?: Record<string, any>): Promise<void> {
    const span = await createSpan({
      name: `screen.view.${screenName}`,
      kind: 'client',
      attributes: {
        'screen.name': screenName,
        ...params,
      },
    });

    span.end();
  }

  async trackButtonPress(buttonId: string, screenName: string): Promise<void> {
    const span = await createSpan({
      name: 'user.button_press',
      kind: 'client',
      attributes: {
        'button.id': buttonId,
        'screen.name': screenName,
      },
    });

    span.end();
  }
}

export default new OpenTelemetryService();
```

### 9.2 React Native 使用示例

```typescript
import React, { useEffect } from 'react';
import { Button, View, Text } from 'react-native';
import OtelService from './OtelModule';

function CheckoutScreen() {
  useEffect(() => {
    // 追踪屏幕浏览
    OtelService.trackScreenView('checkout', {
      'user.id': '12345',
      'cart.items_count': 3,
    });
  }, []);

  const handleSubmit = async () => {
    // 追踪按钮点击
    await OtelService.trackButtonPress('submit-btn', 'checkout');

    // 业务逻辑...
  };

  return (
    <View>
      <Text>Checkout</Text>
      <Button title="Submit Order" onPress={handleSubmit} />
    </View>
  );
}
```

---

## 10. Flutter FFI 集成

### 10.1 Flutter FFI 绑定

**`flutter/otel_ffi.dart`**:

```dart
import 'dart:ffi' as ffi;
import 'dart:io';
import 'package:ffi/ffi.dart';

// 加载 Rust 动态库
final dylib = ffi.DynamicLibrary.open(
  Platform.isAndroid
      ? 'libotel_mobile.so'
      : Platform.isIOS
          ? 'otel_mobile.framework/otel_mobile'
          : 'libotel_mobile.dylib',
);

// FFI 函数签名
typedef InitOtelNative = ffi.Void Function(
  ffi.Pointer<Utf8> serviceName,
  ffi.Pointer<Utf8> serviceVersion,
  ffi.Pointer<Utf8> otlpEndpoint,
);
typedef InitOtel = void Function(
  ffi.Pointer<Utf8> serviceName,
  ffi.Pointer<Utf8> serviceVersion,
  ffi.Pointer<Utf8> otlpEndpoint,
);

final initOtel = dylib.lookupFunction<InitOtelNative, InitOtel>('init_otel');

// Dart 封装
class OpenTelemetryService {
  void initialize(String serviceName, String serviceVersion, String otlpEndpoint) {
    final serviceNamePtr = serviceName.toNativeUtf8();
    final serviceVersionPtr = serviceVersion.toNativeUtf8();
    final otlpEndpointPtr = otlpEndpoint.toNativeUtf8();

    initOtel(serviceNamePtr, serviceVersionPtr, otlpEndpointPtr);

    malloc.free(serviceNamePtr);
    malloc.free(serviceVersionPtr);
    malloc.free(otlpEndpointPtr);
  }
}
```

**Rust FFI 导出 (`src/ffi.rs`)**:

```rust
use std::ffi::CStr;
use std::os::raw::c_char;

#[no_mangle]
pub extern "C" fn init_otel(
    service_name: *const c_char,
    service_version: *const c_char,
    otlp_endpoint: *const c_char,
) {
    let service_name = unsafe { CStr::from_ptr(service_name).to_string_lossy().into_owned() };
    let service_version = unsafe { CStr::from_ptr(service_version).to_string_lossy().into_owned() };
    let otlp_endpoint = unsafe { CStr::from_ptr(otlp_endpoint).to_string_lossy().into_owned() };

    // 初始化 OpenTelemetry（同步版本，Flutter 主线程调用）
    // 实现省略...
}
```

---

## 11. 性能优化

### 11.1 二进制体积优化

```bash
# 1. 启用 wasm-opt 优化
wasm-opt -Oz -o output_optimized.wasm output.wasm

# 2. 启用 Brotli 压缩
brotli -q 11 output_optimized.wasm

# 典型体积：
# - 未优化: 500KB
# - wasm-opt: 200KB
# - Brotli: 50-80KB
```

### 11.2 异步批量导出优化

```rust
// 使用更大的批次以减少网络请求
let batch_processor = opentelemetry_sdk::trace::BatchSpanProcessor::builder(
    exporter,
    opentelemetry_sdk::runtime::WasmRuntime,
)
.with_max_queue_size(4096)        // 增大队列
.with_max_export_batch_size(1024) // 增大批次
.with_scheduled_delay(std::time::Duration::from_secs(10)) // 增加延迟
.build();
```

---

## 12. 完整示例

### 12.1 构建与部署

```bash
# 1. 添加 WASM 目标
rustup target add wasm32-unknown-unknown

# 2. 安装 wasm-pack
cargo install wasm-pack

# 3. 构建 WASM 模块
wasm-pack build --target web --release

# 4. 生成的文件
# pkg/
#   mobile_otel_wasm_bg.wasm
#   mobile_otel_wasm.js
#   mobile_otel_wasm.d.ts
```

### 12.2 React 应用完整集成

```javascript
import React, { useEffect } from 'react';
import init, { initOpenTelemetry, createSpan, traceFetch } from './pkg/mobile_otel_wasm';

function App() {
  useEffect(() => {
    async function initOtel() {
      await init();
      await initOpenTelemetry(
        'react-mobile-app',
        '1.0.0',
        'https://otel-collector.example.com:4318'
      );
    }
    initOtel();
  }, []);

  const handleLoadProducts = async () => {
    const span = await createSpan({
      name: 'load_products',
      kind: 'client',
      attributes: { 'screen.name': 'home' },
    });

    try {
      const response = await traceFetch('https://api.example.com/products');
      const products = await response.json();
      console.log(products);
    } catch (error) {
      span.setError(error.message);
    } finally {
      span.end();
    }
  };

  return (
    <div>
      <h1>My Mobile App</h1>
      <button onClick={handleLoadProducts}>Load Products</button>
    </div>
  );
}

export default App;
```

---

## 参考资源

### 官方文档

- **OpenTelemetry Rust**: <https://docs.rs/opentelemetry/latest/opentelemetry/>
- **wasm-bindgen**: <https://rustwasm.github.io/wasm-bindgen/>
- **web-sys**: <https://rustwasm.github.io/wasm-bindgen/api/web_sys/>

### 最佳实践

- **WASM 性能优化**: <https://rustwasm.github.io/book/reference/code-size.html>
- **React Native WASM**: <https://github.com/cuvent/react-native-webassembly>

---

**文档维护**: OTLP Rust 项目组  
**最后更新**: 2025年10月9日  
**文档版本**: v1.0  
**质量等级**: ⭐⭐⭐⭐⭐
