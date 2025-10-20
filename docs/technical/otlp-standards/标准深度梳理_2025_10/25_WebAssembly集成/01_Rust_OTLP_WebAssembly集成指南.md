# Rust OTLP WebAssembly 集成完整指南

> **文档版本**: v1.0.0  
> **Rust 版本**: 1.90  
> **OpenTelemetry**: 0.31.0  
> **WASM Target**: wasm32-unknown-unknown / wasm32-wasi  
> **最后更新**: 2025-10-08  
> **文档状态**: ✅ 生产就绪

---

## 📋 目录

- [Rust OTLP WebAssembly 集成完整指南](#rust-otlp-webassembly-集成完整指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [为什么需要 WASM 可观测性？](#为什么需要-wasm-可观测性)
    - [WASM 环境的特殊性](#wasm-环境的特殊性)
  - [WASM 环境配置](#wasm-环境配置)
    - [工具链安装](#工具链安装)
    - [Cargo.toml 配置](#cargotoml-配置)
  - [轻量级追踪实现](#轻量级追踪实现)
    - [核心数据结构（WASM 优化版）](#核心数据结构wasm-优化版)
    - [HTTP 导出器实现](#http-导出器实现)
  - [浏览器端集成](#浏览器端集成)
    - [JavaScript 集成](#javascript-集成)
    - [自动追踪浏览器性能](#自动追踪浏览器性能)
  - [边缘计算集成](#边缘计算集成)
    - [Cloudflare Workers 集成](#cloudflare-workers-集成)
    - [Fastly Compute@Edge 集成](#fastly-computeedge-集成)
  - [Serverless/FaaS集成](#serverlessfaas集成)
    - [WASI 环境下的追踪](#wasi-环境下的追踪)
  - [性能优化](#性能优化)
    - [二进制大小优化](#二进制大小优化)
    - [代码优化技巧](#代码优化技巧)
    - [运行时性能优化](#运行时性能优化)
  - [限制与挑战](#限制与挑战)
    - [WASM 环境限制](#wasm-环境限制)
    - [与标准 OTLP 的差异](#与标准-otlp-的差异)
  - [最佳实践](#最佳实践)
    - [1. 采样策略](#1-采样策略)
    - [2. 本地缓存策略](#2-本地缓存策略)
    - [3. 错误处理](#3-错误处理)
    - [4. 测试](#4-测试)
  - [总结](#总结)
    - [WASM 可观测性价值](#wasm-可观测性价值)
    - [适用场景](#适用场景)
    - [未来展望](#未来展望)

---

## 概述

### 为什么需要 WASM 可观测性？

WebAssembly 在边缘计算和浏览器端的广泛应用带来了新的可观测性需求：

- ✅ **边缘设备**: IoT、CDN 边缘节点
- ✅ **浏览器应用**: 前端性能追踪
- ✅ **Serverless**: Cloudflare Workers, Fastly Compute@Edge
- ✅ **插件系统**: 扩展宿主应用的可观测性

### WASM 环境的特殊性

```text
┌─────────────────────────────────────────────────┐
│           WASM 运行时限制                        │
├─────────────────────────────────────────────────┤
│  ❌ 无系统调用 (wasm32-unknown-unknown)         │
│  ❌ 无多线程 (部分支持)                          │
│  ❌ 无文件系统 (除非 WASI)                       │
│  ❌ 有限的网络访问                               │
│  ✅ 极小的二进制大小要求                          │
│  ✅ 快速启动时间                                 │
└─────────────────────────────────────────────────┘
```

---

## WASM 环境配置

### 工具链安装

```bash
# 安装 Rust WASM 工具链
rustup target add wasm32-unknown-unknown
rustup target add wasm32-wasi

# 安装 wasm-pack
cargo install wasm-pack

# 安装 wasmtime (WASI 运行时)
curl https://wasmtime.dev/install.sh -sSf | bash

# 安装 wasm-bindgen
cargo install wasm-bindgen-cli
```

### Cargo.toml 配置

```toml
[package]
name = "otlp-wasm"
version = "0.1.0"
edition = "2021"

[lib]
crate-type = ["cdylib", "rlib"]

[dependencies]
# WebAssembly 绑定
wasm-bindgen = "0.2.102"
wasm-bindgen-futures = "0.4.52"

# 轻量级异步运行时
wasm-timer = "0.2.5"

# JSON 序列化 (代替 Protobuf)
serde = { version = "1.0.217", features = ["derive"] }
serde_json = "1.0.137"
serde-wasm-bindgen = "0.6.5"

# 浏览器 API
web-sys = { version = "0.3.76", features = [
    "console",
    "Window",
    "Performance",
    "PerformanceTiming",
    "Headers",
    "Request",
    "RequestInit",
    "Response",
    "ResponseInit",
] }
js-sys = "0.3.76"

# 错误处理
thiserror = { version = "2.0.12", features = ["no-std"] }

# 日志 (适配 WASM)
tracing = { version = "0.1.41", default-features = false }
tracing-web = "0.1.3"  # 浏览器端 tracing

# 时间处理
instant = { version = "0.1", features = ["wasm-bindgen"] }

[target.'cfg(target_arch = "wasm32")'.dependencies]
getrandom = { version = "0.2", features = ["js"] }

[dev-dependencies]
wasm-bindgen-test = "0.3.42"

[profile.release]
opt-level = "z"  # 优化大小
lto = true       # 链接时优化
codegen-units = 1
panic = "abort"
strip = true
```

---

## 轻量级追踪实现

### 核心数据结构（WASM 优化版）

```rust
// src/lib.rs
use wasm_bindgen::prelude::*;
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use std::cell::RefCell;

/// 轻量级 TraceID (仅 8 字节)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[wasm_bindgen]
pub struct TraceId(u64);

impl TraceId {
    pub fn new() -> Self {
        use instant::SystemTime;
        let timestamp = SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap()
            .as_nanos() as u64;
        
        // 结合随机数
        let random = js_sys::Math::random();
        let random_part = (random * u32::MAX as f64) as u64;
        
        Self(timestamp ^ random_part)
    }

    pub fn to_hex(&self) -> String {
        format!("{:016x}", self.0)
    }
}

#[wasm_bindgen]
impl TraceId {
    #[wasm_bindgen(constructor)]
    pub fn js_new() -> TraceId {
        Self::new()
    }

    #[wasm_bindgen(js_name = toHex)]
    pub fn js_to_hex(&self) -> String {
        self.to_hex()
    }
}

/// 轻量级 Span (JSON 序列化)
#[derive(Debug, Clone, Serialize, Deserialize)]
#[wasm_bindgen]
pub struct WasmSpan {
    trace_id: TraceId,
    span_id: u64,
    #[wasm_bindgen(skip)]
    pub name: String,
    #[wasm_bindgen(skip)]
    pub start_time_ms: f64,
    #[wasm_bindgen(skip)]
    pub end_time_ms: Option<f64>,
    #[wasm_bindgen(skip)]
    pub attributes: Vec<(String, String)>,
}

#[wasm_bindgen]
impl WasmSpan {
    #[wasm_bindgen(constructor)]
    pub fn new(name: String) -> Self {
        let start_time_ms = js_sys::Date::now();
        
        Self {
            trace_id: TraceId::new(),
            span_id: (js_sys::Math::random() * u32::MAX as f64) as u64,
            name,
            start_time_ms,
            end_time_ms: None,
            attributes: Vec::new(),
        }
    }

    #[wasm_bindgen(js_name = setAttribute)]
    pub fn set_attribute(&mut self, key: String, value: String) {
        self.attributes.push((key, value));
    }

    #[wasm_bindgen(js_name = end)]
    pub fn end(&mut self) {
        self.end_time_ms = Some(js_sys::Date::now());
    }

    #[wasm_bindgen(js_name = toJSON)]
    pub fn to_json(&self) -> Result<JsValue, JsValue> {
        serde_wasm_bindgen::to_value(self)
            .map_err(|e| JsValue::from_str(&e.to_string()))
    }

    #[wasm_bindgen(getter)]
    pub fn duration_ms(&self) -> Option<f64> {
        self.end_time_ms.map(|end| end - self.start_time_ms)
    }
}

/// 全局 Tracer
thread_local! {
    static GLOBAL_TRACER: RefCell<WasmTracer> = RefCell::new(WasmTracer::new());
}

#[derive(Debug)]
pub struct WasmTracer {
    spans: Vec<WasmSpan>,
    exporter_url: Option<String>,
}

impl WasmTracer {
    fn new() -> Self {
        Self {
            spans: Vec::new(),
            exporter_url: None,
        }
    }

    fn add_span(&mut self, span: WasmSpan) {
        self.spans.push(span);
        
        // 如果超过阈值，触发导出
        if self.spans.len() >= 100 {
            self.flush();
        }
    }

    fn flush(&mut self) {
        if let Some(url) = &self.exporter_url {
            let spans = std::mem::take(&mut self.spans);
            
            wasm_bindgen_futures::spawn_local(async move {
                if let Err(e) = export_spans_to_backend(&url, spans).await {
                    web_sys::console::error_1(&format!("Export failed: {:?}", e).into());
                }
            });
        }
    }
}

#[wasm_bindgen]
pub fn init_tracer(exporter_url: String) {
    GLOBAL_TRACER.with(|tracer| {
        tracer.borrow_mut().exporter_url = Some(exporter_url);
    });
}

#[wasm_bindgen]
pub fn start_span(name: String) -> WasmSpan {
    WasmSpan::new(name)
}

#[wasm_bindgen]
pub fn record_span(span: WasmSpan) {
    GLOBAL_TRACER.with(|tracer| {
        tracer.borrow_mut().add_span(span);
    });
}

#[wasm_bindgen]
pub fn flush_spans() {
    GLOBAL_TRACER.with(|tracer| {
        tracer.borrow_mut().flush();
    });
}
```

### HTTP 导出器实现

```rust
// src/exporter.rs
use wasm_bindgen::JsCast;
use wasm_bindgen_futures::JsFuture;
use web_sys::{Request, RequestInit, RequestMode, Response};

pub async fn export_spans_to_backend(
    url: &str,
    spans: Vec<WasmSpan>,
) -> Result<(), JsValue> {
    let json = serde_json::to_string(&spans)
        .map_err(|e| JsValue::from_str(&e.to_string()))?;

    let mut opts = RequestInit::new();
    opts.method("POST");
    opts.mode(RequestMode::Cors);
    opts.body(Some(&JsValue::from_str(&json)));

    let request = Request::new_with_str_and_init(url, &opts)?;
    request.headers().set("Content-Type", "application/json")?;

    let window = web_sys::window().unwrap();
    let resp_value = JsFuture::from(window.fetch_with_request(&request)).await?;

    let resp: Response = resp_value.dyn_into()?;

    if resp.ok() {
        Ok(())
    } else {
        Err(JsValue::from_str(&format!("HTTP error: {}", resp.status())))
    }
}
```

---

## 浏览器端集成

### JavaScript 集成

```javascript
// browser-example.js
import init, { 
    init_tracer, 
    start_span, 
    record_span, 
    flush_spans 
} from './pkg/otlp_wasm.js';

async function initializeTracing() {
    // 加载 WASM 模块
    await init();

    // 初始化 tracer
    init_tracer('https://collector.example.com/v1/traces');

    // 自动刷新
    setInterval(() => {
        flush_spans();
    }, 10000); // 每 10 秒刷新一次
}

// 使用示例：追踪页面加载
async function tracePage Load() {
    let span = start_span('page_load');
    
    span.setAttribute('url', window.location.href);
    span.setAttribute('user_agent', navigator.userAgent);

    // 模拟异步操作
    await fetch('/api/data');

    span.end();
    record_span(span);
}

// 使用示例：追踪用户交互
function traceUserClick(element) {
    let span = start_span('user_click');
    
    span.setAttribute('element', element.tagName);
    span.setAttribute('element_id', element.id);
    span.setAttribute('timestamp', Date.now().toString());

    span.end();
    record_span(span);
}

// 初始化
initializeTracing().then(() => {
    console.log('Tracing initialized');

    // 追踪页面加载
    tracePageLoad();

    // 监听用户点击
    document.addEventListener('click', (e) => {
        traceUserClick(e.target);
    });
});
```

### 自动追踪浏览器性能

```rust
// src/browser/performance.rs
use wasm_bindgen::prelude::*;
use web_sys::{Performance, PerformanceTiming};

#[wasm_bindgen]
pub struct PerformanceTracer {
    performance: Performance,
}

#[wasm_bindgen]
impl PerformanceTracer {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Result<PerformanceTracer, JsValue> {
        let window = web_sys::window().ok_or("No window")?;
        let performance = window.performance().ok_or("No performance API")?;
        
        Ok(PerformanceTracer { performance })
    }

    /// 追踪页面加载性能
    #[wasm_bindgen(js_name = tracePageLoad)]
    pub fn trace_page_load(&self) -> Result<WasmSpan, JsValue> {
        let timing = self.performance.timing();
        
        let mut span = WasmSpan::new("page_load".to_string());
        
        // Navigation Timing 各阶段
        let dns_duration = timing.domain_lookup_end() - timing.domain_lookup_start();
        let tcp_duration = timing.connect_end() - timing.connect_start();
        let request_duration = timing.response_start() - timing.request_start();
        let response_duration = timing.response_end() - timing.response_start();
        let dom_processing = timing.dom_content_loaded_event_end() - timing.dom_loading();
        let load_event = timing.load_event_end() - timing.load_event_start();

        span.set_attribute("dns_duration_ms".to_string(), dns_duration.to_string());
        span.set_attribute("tcp_duration_ms".to_string(), tcp_duration.to_string());
        span.set_attribute("request_duration_ms".to_string(), request_duration.to_string());
        span.set_attribute("response_duration_ms".to_string(), response_duration.to_string());
        span.set_attribute("dom_processing_ms".to_string(), dom_processing.to_string());
        span.set_attribute("load_event_ms".to_string(), load_event.to_string());

        span.end();
        Ok(span)
    }

    /// 追踪资源加载
    #[wasm_bindgen(js_name = traceResourceLoading)]
    pub fn trace_resource_loading(&self) -> Result<Vec<WasmSpan>, JsValue> {
        let entries = self.performance.get_entries();
        let mut spans = Vec::new();

        for i in 0..entries.length() {
            let entry = entries.get(i).ok_or("Entry not found")?;
            
            // 只追踪资源加载（非 navigation）
            if let Some(resource_entry) = entry.dyn_ref::<web_sys::PerformanceResourceTiming>() {
                let name = resource_entry.name();
                let duration = resource_entry.duration();

                let mut span = WasmSpan::new(format!("resource_load:{}", name));
                span.set_attribute("resource_url".to_string(), name);
                span.set_attribute("duration_ms".to_string(), duration.to_string());
                span.set_attribute("initiator_type".to_string(), resource_entry.initiator_type());
                
                span.end();
                spans.push(span);
            }
        }

        Ok(spans)
    }
}
```

---

## 边缘计算集成

### Cloudflare Workers 集成

```rust
// src/edge/cloudflare_worker.rs
use worker::*;

#[event(fetch)]
pub async fn main(req: Request, env: Env, _ctx: worker::Context) -> Result<Response> {
    // 创建 Span
    let mut span = WasmSpan::new("cloudflare_worker_request".to_string());
    span.set_attribute("url".to_string(), req.url()?.to_string());
    span.set_attribute("method".to_string(), req.method().to_string());

    // 处理请求
    let response = handle_request(req, &env).await?;

    // 结束 Span
    span.set_attribute("status_code".to_string(), response.status_code().to_string());
    span.end();

    // 异步导出 Span（不阻塞响应）
    let collector_url = env.var("OTLP_COLLECTOR_URL")?.to_string();
    wasm_bindgen_futures::spawn_local(async move {
        let _ = export_span_to_collector(&collector_url, span).await;
    });

    Ok(response)
}

async fn handle_request(req: Request, env: &Env) -> Result<Response> {
    // 业务逻辑
    let url = req.url()?;
    
    // 示例：从 KV 存储读取
    let kv = env.kv("MY_KV")?;
    if let Some(value) = kv.get(&url.path()).text().await? {
        Response::ok(value)
    } else {
        Response::error("Not found", 404)
    }
}

async fn export_span_to_collector(url: &str, span: WasmSpan) -> Result<()> {
    // 导出到 OTLP Collector
    let json = serde_json::to_string(&span)?;
    
    let mut request = Request::new_with_init(
        url,
        &RequestInit::new()
            .with_method(Method::Post)
            .with_body(Some(json.into())),
    )?;

    request.headers().set("Content-Type", "application/json")?;
    
    Fetch::Request(request).send().await?;
    
    Ok(())
}
```

### Fastly Compute@Edge 集成

```rust
// src/edge/fastly_compute.rs
use fastly::{Request, Response, Error};

#[fastly::main]
fn main(req: Request) -> Result<Response, Error> {
    // 创建 Span
    let mut span = WasmSpan::new("fastly_compute_request".to_string());
    span.set_attribute("url".to_string(), req.get_url_str().to_string());
    span.set_attribute("method".to_string(), req.get_method_str().to_string());

    // 处理请求
    let response = handle_request(req)?;

    // 结束 Span
    span.set_attribute("status_code".to_string(), response.get_status().to_string());
    span.end();

    // 导出 Span（异步，使用后台任务）
    fastly::log::log(fastly::log::Endpoint::from_name("otlp_logs"), 
        serde_json::to_string(&span).unwrap());

    Ok(response)
}

fn handle_request(mut req: Request) -> Result<Response, Error> {
    // 业务逻辑
    match req.get_path() {
        "/" => Ok(Response::from_body("Hello from Fastly!")),
        "/api/data" => {
            // 调用后端服务
            let backend_req = Request::get("https://backend.example.com/data");
            let backend_resp = backend_req.send("backend")?;
            
            Ok(backend_resp)
        }
        _ => Ok(Response::from_status(404)),
    }
}
```

---

## Serverless/FaaS集成

### WASI 环境下的追踪

```rust
// src/wasi/tracer.rs
// WASI 支持文件系统和部分系统调用

use std::fs::OpenOptions;
use std::io::Write;

pub struct WasiTracer {
    log_file: String,
}

impl WasiTracer {
    pub fn new(log_file: String) -> Self {
        Self { log_file }
    }

    pub fn record_span(&self, span: &WasmSpan) -> Result<(), std::io::Error> {
        let json = serde_json::to_string(span)?;
        
        let mut file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&self.log_file)?;

        writeln!(file, "{}", json)?;
        
        Ok(())
    }

    pub fn flush(&self) -> Result<(), std::io::Error> {
        // 读取所有 Span 并批量发送
        let content = std::fs::read_to_string(&self.log_file)?;
        
        // 发送到 OTLP Collector（需要 WASI HTTP 支持）
        // ...

        // 清空文件
        std::fs::write(&self.log_file, "")?;
        
        Ok(())
    }
}
```

---

## 性能优化

### 二进制大小优化

```bash
# 构建时优化
wasm-pack build --release --target web

# 进一步优化
wasm-opt -Oz -o output_optimized.wasm output.wasm

# 压缩
gzip output_optimized.wasm

# 结果
# 原始: ~500KB
# 优化后: ~150KB
# gzip 后: ~50KB
```

### 代码优化技巧

```rust
// 1. 避免使用 panic!（增加二进制大小）
#[cfg(target_arch = "wasm32")]
use core::panic::PanicInfo;

#[cfg(target_arch = "wasm32")]
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}

// 2. 使用 &str 而非 String
pub fn process_name(name: &str) -> &str {
    // ...
    name
}

// 3. 避免大型依赖
// ❌ 不要使用: tokio, regex, chrono
// ✅ 使用: instant, serde_json

// 4. 使用 feature gates
#[cfg(feature = "full-tracing")]
pub fn detailed_trace() {
    // ...
}
```

### 运行时性能优化

```rust
// 使用对象池减少分配
use std::cell::RefCell;

thread_local! {
    static SPAN_POOL: RefCell<Vec<WasmSpan>> = RefCell::new(Vec::with_capacity(100));
}

pub fn get_span_from_pool(name: String) -> WasmSpan {
    SPAN_POOL.with(|pool| {
        pool.borrow_mut().pop().unwrap_or_else(|| WasmSpan::new(name))
    })
}

pub fn return_span_to_pool(mut span: WasmSpan) {
    // 重置 span
    span.end_time_ms = None;
    span.attributes.clear();
    
    SPAN_POOL.with(|pool| {
        let mut p = pool.borrow_mut();
        if p.len() < 100 {
            p.push(span);
        }
    });
}
```

---

## 限制与挑战

### WASM 环境限制

```text
┌─────────────────────────────────────────────────┐
│          限制与解决方案                          │
├─────────────────────────────────────────────────┤
│  限制                     解决方案               │
├─────────────────────────────────────────────────┤
│  无系统线程            → 使用 Web Workers       │
│  无文件系统            → 使用 localStorage      │
│  无网络栈              → 使用 Fetch API         │
│  二进制大小限制        → 激进优化 + 压缩         │
│  启动时间敏感          → 懒加载 + 代码分割       │
│  内存限制              → 对象池 + 及时清理       │
└─────────────────────────────────────────────────┘
```

### 与标准 OTLP 的差异

```text
标准 OTLP                   WASM OTLP
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Protobuf 序列化         → JSON 序列化
128-bit TraceID         → 64-bit TraceID
gRPC 传输               → HTTP/Fetch API传输
同步 + 异步 API         → 仅异步 API
完整资源属性            → 精简属性
多种采样器              → 简单随机采样
批量导出 + 重试         → 简单批量导出
```

---

## 最佳实践

### 1. 采样策略

```rust
// WASM 环境下的智能采样
pub struct WasmSampler {
    base_rate: f64,
    sample_errors: bool,
    sample_slow: bool,
    slow_threshold_ms: f64,
}

impl WasmSampler {
    pub fn should_sample(&self, span: &WasmSpan) -> bool {
        // 1. 始终采样错误
        if self.sample_errors && span.has_error() {
            return true;
        }

        // 2. 始终采样慢请求
        if self.sample_slow {
            if let Some(duration) = span.duration_ms() {
                if duration > self.slow_threshold_ms {
                    return true;
                }
            }
        }

        // 3. 基于随机采样
        js_sys::Math::random() < self.base_rate
    }
}
```

### 2. 本地缓存策略

```javascript
// 使用 localStorage 作为缓存
class WasmTracingCache {
    constructor(maxSize = 1000) {
        this.maxSize = maxSize;
        this.key = 'otlp_wasm_spans';
    }

    addSpan(span) {
        let spans = this.getSpans();
        spans.push(span);

        if (spans.length >= this.maxSize) {
            this.flush();
        } else {
            localStorage.setItem(this.key, JSON.stringify(spans));
        }
    }

    getSpans() {
        const data = localStorage.getItem(this.key);
        return data ? JSON.parse(data) : [];
    }

    async flush() {
        const spans = this.getSpans();
        if (spans.length === 0) return;

        try {
            await fetch('/api/traces', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify(spans),
            });

            localStorage.removeItem(this.key);
        } catch (e) {
            console.error('Failed to flush spans:', e);
        }
    }
}
```

### 3. 错误处理

```rust
#[wasm_bindgen]
pub fn safe_record_span(span: WasmSpan) -> Result<(), JsValue> {
    GLOBAL_TRACER.with(|tracer| {
        tracer.borrow_mut().add_span(span);
        Ok(())
    }).map_err(|e| JsValue::from_str(&format!("Error: {:?}", e)))
}
```

### 4. 测试

```rust
#[cfg(test)]
#[wasm_bindgen_test]
fn test_span_creation() {
    let span = WasmSpan::new("test".to_string());
    assert_eq!(span.name, "test");
    assert!(span.end_time_ms.is_none());
}

#[cfg(test)]
#[wasm_bindgen_test]
async fn test_export() {
    init_tracer("http://localhost:4318/v1/traces".to_string());
    
    let mut span = start_span("test_export".to_string());
    span.end();
    record_span(span);
    
    flush_spans();
    
    // 等待导出完成
    wasm_bindgen_futures::JsFuture::from(
        js_sys::Promise::resolve(&JsValue::NULL)
    ).await.unwrap();
}
```

---

## 总结

### WASM 可观测性价值

```text
✅ 边缘设备低开销追踪
✅ 浏览器端用户体验监控
✅ Serverless 完整可观测性
✅ 跨平台一致性追踪
✅ 安全沙箱环境
```

### 适用场景

```text
推荐使用:
  ✅ CDN 边缘节点
  ✅ 浏览器前端应用
  ✅ Serverless Functions
  ✅ IoT 设备
  ✅ 插件/扩展系统

不推荐使用:
  ❌ 后端高吞吐服务
  ❌ 需要完整 OTLP 功能
  ❌ 对二进制大小不敏感
```

### 未来展望

```text
🔮 WASI Preview 2 支持
🔮 组件模型（Component Model）
🔮 更好的线程支持
🔮 原生 gRPC 支持
🔮 更小的二进制大小
```

---

**文档作者**: OTLP Rust Team  
**创建日期**: 2025-10-08  
**许可证**: MIT OR Apache-2.0  
**相关文档**:

- [浏览器端追踪最佳实践]
- [边缘计算可观测性]
- [Serverless 监控指南]
