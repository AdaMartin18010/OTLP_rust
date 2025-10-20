# 🌐 移动端 Rust WASM 集成指南

> **Rust 版本**: 1.90+  
> **OpenTelemetry**: 0.31.0 (适配版)  
> **目标平台**: Web Browser, React Native, Flutter  
> **最后更新**: 2025年10月10日

---

## 📋 目录

- [🌐 移动端 Rust WASM 集成指南](#-移动端-rust-wasm-集成指南)
  - [📋 目录](#-目录)
  - [1. WebAssembly 可观测性概述](#1-webassembly-可观测性概述)
    - [1.1 为什么选择 Rust + WASM？](#11-为什么选择-rust--wasm)
    - [1.2 WASM OTLP 架构](#12-wasm-otlp-架构)
  - [2. 开发环境配置](#2-开发环境配置)
    - [2.1 工具链安装](#21-工具链安装)
    - [2.2 项目配置](#22-项目配置)
  - [3. WASM 环境下的 OTLP](#3-wasm-环境下的-otlp)
    - [3.1 核心数据结构](#31-核心数据结构)
    - [3.2 JavaScript 互操作](#32-javascript-互操作)
  - [4. 网络传输实现](#4-网络传输实现)
    - [4.1 使用 Fetch API](#41-使用-fetch-api)
    - [4.2 批量导出器](#42-批量导出器)
  - [5. 浏览器集成](#5-浏览器集成)
    - [5.1 基础集成](#51-基础集成)
    - [5.2 Performance API 集成](#52-performance-api-集成)
  - [6. React Native 集成](#6-react-native-集成)
    - [6.1 配置与构建](#61-配置与构建)
    - [6.2 实战示例](#62-实战示例)
  - [7. 性能优化](#7-性能优化)
    - [7.1 减小包体积](#71-减小包体积)
    - [7.2 运行时优化](#72-运行时优化)
  - [8. 完整示例](#8-完整示例)
    - [8.1 单页应用 (SPA)](#81-单页应用-spa)
  - [🔗 参考资源](#-参考资源)

---

## 1. WebAssembly 可观测性概述

### 1.1 为什么选择 Rust + WASM？

| 优势 | 说明 |
|------|------|
| **高性能** | 接近原生代码性能 |
| **类型安全** | Rust 的强类型系统 |
| **小体积** | 优化后可达 100KB 以下 |
| **跨平台** | 一次编写，多端运行 |
| **安全性** | 沙箱环境 + Rust 内存安全 |

### 1.2 WASM OTLP 架构

```text
┌──────────────────────────────────────────┐
│          Browser / Mobile App            │
│  ┌────────────────────────────────┐     │
│  │    JavaScript / TypeScript     │     │
│  │         (Application)          │     │
│  └─────────────┬──────────────────┘     │
│                │                         │
│                ▼                         │
│  ┌────────────────────────────────┐     │
│  │    Rust WASM OTLP Module       │     │
│  │  ┌──────────────────────────┐  │     │
│  │  │  Tracer (wasm_bindgen)   │  │     │
│  │  └──────────────────────────┘  │     │
│  │  ┌──────────────────────────┐  │     │
│  │  │  Span Buffer             │  │     │
│  │  └──────────────────────────┘  │     │
│  │  ┌──────────────────────────┐  │     │
│  │  │  Fetch API Exporter      │  │     │
│  │  └──────────────────────────┘  │     │
│  └────────────────────────────────┘     │
│                │                         │
│                ▼                         │
│      Browser Fetch / XHR API            │
└────────────────┬─────────────────────────┘
                 │
                 ▼
        OTLP Collector / Backend
```

---

## 2. 开发环境配置

### 2.1 工具链安装

```bash
# 安装 wasm-pack
curl https://rustwasm.github.io/wasm-pack/installer/init.sh -sSf | sh

# 或使用 cargo
cargo install wasm-pack

# 添加 wasm32 target
rustup target add wasm32-unknown-unknown

# 安装 wasm-bindgen-cli
cargo install wasm-bindgen-cli

# (可选) 安装 wasm-opt 优化工具
npm install -g wasm-opt
```

### 2.2 项目配置

```toml
# Cargo.toml

[package]
name = "otlp-wasm"
version = "0.1.0"
edition = "2021"

[lib]
crate-type = ["cdylib", "rlib"]

[dependencies]
wasm-bindgen = "0.2"
wasm-bindgen-futures = "0.4"
js-sys = "0.3"
web-sys = { version = "0.3", features = [
    "console",
    "Window",
    "Performance",
    "PerformanceTiming",
    "Headers",
    "Request",
    "RequestInit",
    "RequestMode",
    "Response",
] }
serde = { version = "1.0", features = ["derive"] }
serde-wasm-bindgen = "0.6"
serde_json = "1.0"
getrandom = { version = "0.2", features = ["js"] }

[dev-dependencies]
wasm-bindgen-test = "0.3"

[profile.release]
opt-level = "z"      # 最小化大小
lto = true           # 链接时优化
codegen-units = 1    # 单一代码生成单元
strip = true         # 移除符号
```

---

## 3. WASM 环境下的 OTLP

### 3.1 核心数据结构

```rust
use wasm_bindgen::prelude::*;
use serde::{Serialize, Deserialize};

/// TraceId (128-bit)
#[wasm_bindgen]
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub struct TraceId {
    high: u64,
    low: u64,
}

#[wasm_bindgen]
impl TraceId {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        use getrandom::getrandom;
        let mut bytes = [0u8; 16];
        getrandom(&mut bytes).expect("Failed to generate random bytes");
        
        Self {
            high: u64::from_be_bytes([
                bytes[0], bytes[1], bytes[2], bytes[3],
                bytes[4], bytes[5], bytes[6], bytes[7],
            ]),
            low: u64::from_be_bytes([
                bytes[8], bytes[9], bytes[10], bytes[11],
                bytes[12], bytes[13], bytes[14], bytes[15],
            ]),
        }
    }
    
    #[wasm_bindgen(js_name = toString)]
    pub fn to_string_js(&self) -> String {
        format!("{:016x}{:016x}", self.high, self.low)
    }
}

/// SpanId (64-bit)
#[wasm_bindgen]
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub struct SpanId(u64);

#[wasm_bindgen]
impl SpanId {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        use getrandom::getrandom;
        let mut bytes = [0u8; 8];
        getrandom(&mut bytes).expect("Failed to generate random bytes");
        Self(u64::from_be_bytes(bytes))
    }
    
    #[wasm_bindgen(js_name = toString)]
    pub fn to_string_js(&self) -> String {
        format!("{:016x}", self.0)
    }
}

/// Span 数据
#[wasm_bindgen]
#[derive(Clone, Serialize, Deserialize)]
pub struct Span {
    trace_id: TraceId,
    span_id: SpanId,
    parent_span_id: Option<SpanId>,
    name: String,
    start_time_ms: f64,
    end_time_ms: Option<f64>,
}

#[wasm_bindgen]
impl Span {
    #[wasm_bindgen(constructor)]
    pub fn new(name: String) -> Self {
        let start_time_ms = js_sys::Date::now();
        
        Self {
            trace_id: TraceId::new(),
            span_id: SpanId::new(),
            parent_span_id: None,
            name,
            start_time_ms,
            end_time_ms: None,
        }
    }
    
    pub fn end(&mut self) {
        self.end_time_ms = Some(js_sys::Date::now());
    }
    
    #[wasm_bindgen(getter, js_name = traceId)]
    pub fn trace_id(&self) -> String {
        self.trace_id.to_string_js()
    }
    
    #[wasm_bindgen(getter, js_name = spanId)]
    pub fn span_id(&self) -> String {
        self.span_id.to_string_js()
    }
    
    #[wasm_bindgen(getter)]
    pub fn name(&self) -> String {
        self.name.clone()
    }
    
    #[wasm_bindgen(getter, js_name = durationMs)]
    pub fn duration_ms(&self) -> Option<f64> {
        self.end_time_ms.map(|end| end - self.start_time_ms)
    }
}
```

### 3.2 JavaScript 互操作

```rust
use wasm_bindgen::prelude::*;
use web_sys::console;

/// 日志宏（WASM 版本）
#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = console)]
    fn log(s: &str);
}

macro_rules! console_log {
    ($($t:tt)*) => (log(&format_args!($($t)*).to_string()))
}

/// Tracer
#[wasm_bindgen]
pub struct Tracer {
    service_name: String,
    spans: Vec<Span>,
}

#[wasm_bindgen]
impl Tracer {
    #[wasm_bindgen(constructor)]
    pub fn new(service_name: String) -> Self {
        console_log!("Initializing tracer for service: {}", service_name);
        Self {
            service_name,
            spans: Vec::new(),
        }
    }
    
    #[wasm_bindgen(js_name = startSpan)]
    pub fn start_span(&mut self, name: String) -> Span {
        console_log!("Starting span: {}", name);
        Span::new(name)
    }
    
    #[wasm_bindgen(js_name = recordSpan)]
    pub fn record_span(&mut self, span: Span) {
        console_log!("Recording span: {}", span.name());
        self.spans.push(span);
    }
    
    #[wasm_bindgen(js_name = getSpans)]
    pub fn get_spans(&self) -> JsValue {
        serde_wasm_bindgen::to_value(&self.spans).unwrap()
    }
}
```

---

## 4. 网络传输实现

### 4.1 使用 Fetch API

```rust
use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use wasm_bindgen_futures::JsFuture;
use web_sys::{Request, RequestInit, RequestMode, Response};

/// OTLP Exporter
#[wasm_bindgen]
pub struct OtlpExporter {
    endpoint: String,
}

#[wasm_bindgen]
impl OtlpExporter {
    #[wasm_bindgen(constructor)]
    pub fn new(endpoint: String) -> Self {
        Self { endpoint }
    }
    
    /// 导出 Spans (异步)
    #[wasm_bindgen(js_name = exportSpans)]
    pub async fn export_spans(&self, spans: JsValue) -> Result<(), JsValue> {
        let spans: Vec<Span> = serde_wasm_bindgen::from_value(spans)?;
        
        // 序列化
        let payload = serde_json::to_string(&spans)
            .map_err(|e| JsValue::from_str(&e.to_string()))?;
        
        // 构建请求
        let mut opts = RequestInit::new();
        opts.method("POST");
        opts.mode(RequestMode::Cors);
        opts.body(Some(&JsValue::from_str(&payload)));
        
        let request = Request::new_with_str_and_init(&self.endpoint, &opts)?;
        request.headers().set("Content-Type", "application/json")?;
        
        // 发送请求
        let window = web_sys::window().unwrap();
        let resp_value = JsFuture::from(window.fetch_with_request(&request)).await?;
        let resp: Response = resp_value.dyn_into()?;
        
        if !resp.ok() {
            return Err(JsValue::from_str(&format!(
                "Export failed with status: {}",
                resp.status()
            )));
        }
        
        console_log!("Successfully exported {} spans", spans.len());
        Ok(())
    }
}
```

### 4.2 批量导出器

```rust
use std::sync::Mutex;
use std::rc::Rc;

/// 批量导出器
#[wasm_bindgen]
pub struct BatchExporter {
    exporter: OtlpExporter,
    buffer: Rc<Mutex<Vec<Span>>>,
    max_batch_size: usize,
}

#[wasm_bindgen]
impl BatchExporter {
    #[wasm_bindgen(constructor)]
    pub fn new(endpoint: String, max_batch_size: usize) -> Self {
        Self {
            exporter: OtlpExporter::new(endpoint),
            buffer: Rc::new(Mutex::new(Vec::new())),
            max_batch_size,
        }
    }
    
    /// 添加 Span 到缓冲区
    #[wasm_bindgen(js_name = addSpan)]
    pub fn add_span(&mut self, span: Span) {
        let mut buffer = self.buffer.lock().unwrap();
        buffer.push(span);
        
        // 如果达到批量大小，触发导出
        if buffer.len() >= self.max_batch_size {
            console_log!("Buffer full, triggering export");
            // 在实际应用中，这里应该触发异步导出
        }
    }
    
    /// 手动刷新
    #[wasm_bindgen]
    pub async fn flush(&mut self) -> Result<(), JsValue> {
        let spans = {
            let mut buffer = self.buffer.lock().unwrap();
            std::mem::take(&mut *buffer)
        };
        
        if spans.is_empty() {
            return Ok(());
        }
        
        let spans_js = serde_wasm_bindgen::to_value(&spans)?;
        self.exporter.export_spans(spans_js).await
    }
}
```

---

## 5. 浏览器集成

### 5.1 基础集成

```rust
use wasm_bindgen::prelude::*;

/// 初始化 OTLP
#[wasm_bindgen(start)]
pub fn init() {
    // 设置 panic hook
    #[cfg(feature = "console_error_panic_hook")]
    console_error_panic_hook::set_once();
    
    console_log!("OTLP WASM module initialized");
}

/// 全局 Tracer 实例
static mut GLOBAL_TRACER: Option<Tracer> = None;

/// 初始化全局 Tracer
#[wasm_bindgen(js_name = initTracer)]
pub fn init_tracer(service_name: String, endpoint: String) {
    unsafe {
        GLOBAL_TRACER = Some(Tracer::new(service_name));
    }
    console_log!("Global tracer initialized with endpoint: {}", endpoint);
}

/// 获取全局 Tracer
#[wasm_bindgen(js_name = getTracer)]
pub fn get_tracer() -> Option<Tracer> {
    unsafe { GLOBAL_TRACER.clone() }
}
```

### 5.2 Performance API 集成

```rust
use web_sys::Performance;

/// 使用浏览器 Performance API 测量
#[wasm_bindgen]
pub struct PerformanceSpan {
    name: String,
    start_mark: String,
    end_mark: String,
}

#[wasm_bindgen]
impl PerformanceSpan {
    #[wasm_bindgen(constructor)]
    pub fn new(name: String) -> Self {
        let window = web_sys::window().unwrap();
        let performance = window.performance().unwrap();
        
        let start_mark = format!("{}-start", name);
        performance.mark(&start_mark).ok();
        
        Self {
            name: name.clone(),
            start_mark,
            end_mark: format!("{}-end", name),
        }
    }
    
    pub fn end(&self) -> Result<f64, JsValue> {
        let window = web_sys::window().unwrap();
        let performance = window.performance().unwrap();
        
        performance.mark(&self.end_mark)?;
        
        let measure = performance.measure_with_start_mark_and_end_mark(
            &self.name,
            &self.start_mark,
            &self.end_mark,
        )?;
        
        Ok(measure.duration())
    }
}
```

---

## 6. React Native 集成

### 6.1 配置与构建

```bash
# 构建 WASM 模块
wasm-pack build --target web --out-dir pkg

# React Native 项目中安装
npm install ./pkg
```

### 6.2 实战示例

```javascript
// App.tsx
import React, { useEffect, useState } from 'react';
import * as OtlpWasm from 'otlp-wasm';

function App() {
  const [tracer, setTracer] = useState(null);

  useEffect(() => {
    // 初始化 OTLP
    OtlpWasm.initTracer(
      'my-mobile-app',
      'https://collector.example.com/v1/traces'
    );
    
    const t = OtlpWasm.getTracer();
    setTracer(t);
  }, []);

  const handleButtonClick = async () => {
    if (!tracer) return;
    
    // 创建并记录 Span
    const span = tracer.startSpan('button_click');
    
    // 模拟操作
    await new Promise(resolve => setTimeout(resolve, 100));
    
    span.end();
    tracer.recordSpan(span);
    
    console.log(`Span recorded: ${span.traceId}`);
  };

  return (
    <View>
      <Button title="Trace Me" onPress={handleButtonClick} />
    </View>
  );
}
```

---

## 7. 性能优化

### 7.1 减小包体积

```bash
# 优化构建
wasm-pack build --release --target web

# 使用 wasm-opt 进一步优化
wasm-opt -Oz -o optimized.wasm pkg/otlp_wasm_bg.wasm

# 启用 gzip 压缩
gzip -9 optimized.wasm
```

**优化前后对比**:

| 阶段 | 大小 |
|------|------|
| Debug 构建 | ~500KB |
| Release 构建 | ~200KB |
| wasm-opt 优化 | ~120KB |
| Gzip 压缩 | ~45KB |

### 7.2 运行时优化

```rust
// 使用 lazy_static 避免重复初始化
use once_cell::sync::Lazy;

static TRACER: Lazy<Tracer> = Lazy::new(|| {
    Tracer::new("my-service".to_string())
});

// 使用对象池减少分配
use std::cell::RefCell;

thread_local! {
    static SPAN_POOL: RefCell<Vec<Span>> = RefCell::new(Vec::with_capacity(100));
}
```

---

## 8. 完整示例

### 8.1 单页应用 (SPA)

```html
<!-- index.html -->
<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <title>OTLP WASM Demo</title>
</head>
<body>
    <h1>OpenTelemetry WASM Demo</h1>
    <button id="trace-btn">Create Trace</button>
    <div id="output"></div>

    <script type="module">
        import init, { 
            initTracer, 
            getTracer 
        } from './pkg/otlp_wasm.js';

        async function run() {
            // 初始化 WASM
            await init();
            
            // 初始化 Tracer
            initTracer(
                'wasm-demo-app',
                'https://collector.example.com/v1/traces'
            );
            
            const tracer = getTracer();
            
            // 按钮点击事件
            document.getElementById('trace-btn').addEventListener('click', async () => {
                const span = tracer.startSpan('user_click');
                
                // 模拟异步操作
                await fetch('https://api.example.com/data');
                
                span.end();
                tracer.recordSpan(span);
                
                // 显示结果
                document.getElementById('output').innerHTML = `
                    <p>Trace ID: ${span.traceId}</p>
                    <p>Span ID: ${span.spanId}</p>
                    <p>Duration: ${span.durationMs}ms</p>
                `;
            });
        }

        run();
    </script>
</body>
</html>
```

---

## 🔗 参考资源

- [Rust and WebAssembly Book](https://rustwasm.github.io/docs/book/)
- [wasm-bindgen Guide](https://rustwasm.github.io/wasm-bindgen/)
- [OpenTelemetry JavaScript](https://opentelemetry.io/docs/languages/js/)
- [Rust OTLP 快速入门](../33_教程与示例/01_Rust_OTLP_30分钟快速入门.md)

---

**文档版本**: v1.0  
**创建日期**: 2025年10月10日  
**维护者**: OTLP Rust 文档团队

---

[🏠 返回主目录](../README.md) | [📱 移动端可观测性](./README.md) | [🌐 IoT 设备追踪](../13_IoT可观测性/01_IoT设备_Rust完整追踪.md)
