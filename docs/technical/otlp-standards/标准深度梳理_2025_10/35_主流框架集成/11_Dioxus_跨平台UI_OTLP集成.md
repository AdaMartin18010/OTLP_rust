# Dioxus 跨平台 UI - Rust + OTLP 集成完整指南

## 📋 目录

- [概述](#概述)
- [核心概念](#核心概念)
- [Rust 1.90 实现](#rust-190-实现)
- [OTLP 集成策略](#otlp-集成策略)
- [跨平台部署](#跨平台部署)
- [性能监控](#性能监控)
- [最佳实践](#最佳实践)
- [完整示例](#完整示例)

---

## 概述

### 什么是 Dioxus?

**Dioxus** 是一个用 Rust 编写的跨平台 UI 框架,支持:

- **Web**(WASM + SSR)
- **Desktop**(Tauri)
- **Mobile**(iOS/Android)
- **TUI**(终端 UI)

语法类似 React,使用 Virtual DOM 和组件化架构。

### 为什么选择 Dioxus?

| 特性 | Dioxus | React | Flutter |
|-----|--------|-------|---------|
| **语言** | Rust | JavaScript/TypeScript | Dart |
| **类型安全** | ✅ 编译期 | ⚠️ TypeScript 运行时 | ✅ 编译期 |
| **性能** | 🚀 WASM 原生 | ⚡ V8 JIT | ⚡ AOT |
| **跨平台** | Web/Desktop/Mobile/TUI | Web/Native | Mobile/Web/Desktop |
| **包大小** | ~200KB(WASM) | ~500KB(压缩) | ~4MB(APK) |

### OTLP 集成价值

| 可观测性维度 | OTLP 能力 |
|------------|----------|
| **组件渲染时间** | Tracing Span |
| **虚拟 DOM Diff** | Metrics(histogram) |
| **事件处理延迟** | Histogram(p50/p99) |
| **API 调用** | 分布式 Trace |
| **错误追踪** | Span Events + Logs |

---

## 核心概念

### 1. Dioxus 组件模型

```rust
use dioxus::prelude::*;

#[component]
fn App(cx: Scope) -> Element {
    let count = use_state(cx, || 0);

    cx.render(rsx! {
        div {
            h1 { "计数器: {count}" }
            button {
                onclick: move |_| count.set(count.get() + 1),
                "增加"
            }
        }
    })
}
```

### 2. OTLP 追踪上下文

为 Dioxus 组件添加 OTLP 追踪:

```rust
use tracing::{instrument, info};
use opentelemetry::metrics::{Histogram, Meter};

pub struct DioxusMetrics {
    render_duration: Histogram<f64>,
    component_count: Histogram<u64>,
}

impl DioxusMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            render_duration: meter
                .f64_histogram("dioxus.render_duration")
                .with_description("组件渲染时间(ms)")
                .with_unit("ms")
                .init(),
            component_count: meter
                .u64_histogram("dioxus.component_count")
                .with_description("渲染的组件数量")
                .init(),
        }
    }
}
```

---

## Rust 1.90 实现

### 1. 项目设置

```toml
# Cargo.toml
[package]
name = "dioxus-otlp-app"
version = "0.1.0"
edition = "2021"

[dependencies]
dioxus = { version = "0.6", features = ["web", "desktop", "router"] }
dioxus-web = "0.6"
dioxus-desktop = "0.6"

# OTLP
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
tracing-opentelemetry = "0.28"
opentelemetry = "0.30"
opentelemetry_sdk = { version = "0.30", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.30", features = ["trace", "metrics"] }

# 异步运行时
tokio = { version = "1.40", features = ["full"] }

# HTTP 客户端
reqwest = { version = "0.12", features = ["json"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

[features]
default = ["web"]
web = []
desktop = []
```

### 2. OTLP 初始化

```rust
use opentelemetry::global;
use opentelemetry_sdk::trace::TracerProvider;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

pub fn init_telemetry() -> Result<(), Box<dyn std::error::Error>> {
    // 配置 OTLP 导出器
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;

    // 配置 Metrics
    let meter = opentelemetry_otlp::new_pipeline()
        .metrics(opentelemetry_sdk::runtime::Tokio)
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .build()?;

    global::set_meter_provider(meter);

    // 配置 Tracing Subscriber
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new(
            std::env::var("RUST_LOG").unwrap_or_else(|_| "info".into()),
        ))
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    Ok(())
}
```

### 3. 带追踪的 Dioxus 组件

```rust
use dioxus::prelude::*;
use tracing::{info, instrument, span, Level};
use std::sync::Arc;

#[derive(Clone)]
pub struct AppState {
    metrics: Arc<DioxusMetrics>,
}

#[component]
fn TracedApp(cx: Scope) -> Element {
    let _span = span!(Level::INFO, "App::render").entered();
    
    let state = use_shared_state::<AppState>(cx).unwrap();
    let count = use_state(cx, || 0);

    // 记录渲染开始
    let start = std::time::Instant::now();

    let result = cx.render(rsx! {
        div {
            class: "container",
            Header { title: "Dioxus + OTLP" }
            Counter { count: *count.get() }
            button {
                onclick: move |_| {
                    info!(old_count = count.get(), new_count = count.get() + 1, "增加计数");
                    count.set(count.get() + 1);
                },
                "增加"
            }
        }
    });

    // 记录渲染时间
    let elapsed = start.elapsed().as_secs_f64() * 1000.0;
    state.read().metrics.render_duration.record(elapsed, &[]);

    result
}

#[component]
fn Header(cx: Scope, title: &'static str) -> Element {
    let _span = span!(Level::INFO, "Header::render", title = title).entered();

    cx.render(rsx! {
        header {
            h1 { "{title}" }
        }
    })
}

#[component]
fn Counter(cx: Scope, count: i32) -> Element {
    let _span = span!(Level::INFO, "Counter::render", count = count).entered();

    cx.render(rsx! {
        div {
            class: "counter",
            p { "当前计数: {count}" }
        }
    })
}
```

---

## OTLP 集成策略

### 1. API 调用追踪

```rust
use reqwest::Client;
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct User {
    pub id: i64,
    pub name: String,
    pub email: String,
}

#[instrument(skip(client))]
pub async fn fetch_users(client: &Client) -> Result<Vec<User>, reqwest::Error> {
    info!("开始获取用户列表");

    let response = client
        .get("https://api.example.com/users")
        .timeout(std::time::Duration::from_secs(10))
        .send()
        .await?;

    let users = response.json::<Vec<User>>().await?;

    info!(user_count = users.len(), "用户列表获取成功");

    Ok(users)
}

#[component]
fn UserList(cx: Scope) -> Element {
    let users = use_future(cx, (), |_| async move {
        let client = Client::new();
        fetch_users(&client).await
    });

    match users.value() {
        Some(Ok(user_list)) => {
            cx.render(rsx! {
                ul {
                    for user in user_list {
                        li { key: "{user.id}",
                            "{user.name} ({user.email})"
                        }
                    }
                }
            })
        }
        Some(Err(err)) => {
            tracing::error!(error = %err, "获取用户失败");
            cx.render(rsx! {
                div { class: "error",
                    "加载失败: {err}"
                }
            })
        }
        None => {
            cx.render(rsx! {
                div { "加载中..." }
            })
        }
    }
}
```

### 2. 事件处理追踪

```rust
#[component]
fn LoginForm(cx: Scope) -> Element {
    let username = use_state(cx, String::new);
    let password = use_state(cx, String::new);
    let is_loading = use_state(cx, || false);

    let onsubmit = move |evt: FormEvent| {
        evt.prevent_default();
        
        let _span = span!(
            Level::INFO,
            "LoginForm::submit",
            username = %username.get()
        )
        .entered();

        is_loading.set(true);

        let username = username.get().clone();
        let password = password.get().clone();

        cx.spawn(async move {
            info!("开始登录");

            match login(&username, &password).await {
                Ok(_) => {
                    info!(username = %username, "登录成功");
                }
                Err(err) => {
                    tracing::error!(username = %username, error = %err, "登录失败");
                }
            }

            is_loading.set(false);
        });
    };

    cx.render(rsx! {
        form {
            onsubmit: onsubmit,
            input {
                r#type: "text",
                placeholder: "用户名",
                value: "{username}",
                oninput: move |evt| username.set(evt.value.clone())
            }
            input {
                r#type: "password",
                placeholder: "密码",
                value: "{password}",
                oninput: move |evt| password.set(evt.value.clone())
            }
            button {
                r#type: "submit",
                disabled: *is_loading.get(),
                if *is_loading.get() { "登录中..." } else { "登录" }
            }
        }
    })
}

#[instrument]
async fn login(username: &str, password: &str) -> Result<(), Box<dyn std::error::Error>> {
    let client = Client::new();
    
    let response = client
        .post("https://api.example.com/login")
        .json(&serde_json::json!({
            "username": username,
            "password": password
        }))
        .send()
        .await?;

    if response.status().is_success() {
        Ok(())
    } else {
        Err(format!("登录失败: {}", response.status()).into())
    }
}
```

---

## 跨平台部署

### 1. Web(WASM)

```rust
// src/main.rs
#![allow(non_snake_case)]

use dioxus::prelude::*;

fn main() {
    // Web 平台使用浏览器 console
    #[cfg(target_arch = "wasm32")]
    {
        console_error_panic_hook::set_once();
        tracing_wasm::set_as_global_default();
    }

    // 桌面平台使用标准 tracing
    #[cfg(not(target_arch = "wasm32"))]
    {
        init_telemetry().expect("初始化 OTLP 失败");
    }

    dioxus_web::launch(TracedApp);
}
```

**编译 WASM**:

```bash
# 安装 trunk
cargo install trunk

# 构建并运行
trunk serve --open

# 生产构建
trunk build --release
```

### 2. Desktop(Tauri)

```rust
// src/main.rs
#![cfg_attr(
    all(not(debug_assertions), target_os = "windows"),
    windows_subsystem = "windows"
)]

use dioxus::prelude::*;
use dioxus_desktop::{Config, WindowBuilder};

fn main() {
    init_telemetry().expect("初始化 OTLP 失败");

    dioxus_desktop::launch_cfg(
        TracedApp,
        Config::new()
            .with_window(
                WindowBuilder::new()
                    .with_title("Dioxus + OTLP")
                    .with_resizable(true)
                    .with_inner_size(dioxus_desktop::wry::application::dpi::LogicalSize::new(
                        1200.0, 800.0,
                    )),
            ),
    );
}
```

**运行桌面应用**:

```bash
cargo run --features desktop
```

### 3. SSR(服务端渲染)

```rust
use dioxus::prelude::*;
use axum::{
    extract::State,
    response::Html,
    routing::get,
    Router,
};

async fn render_app() -> Html<String> {
    let html = dioxus_ssr::render_lazy(rsx! {
        TracedApp {}
    });

    Html(html)
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    init_telemetry()?;

    let app = Router::new()
        .route("/", get(render_app))
        .route("/static/*path", axum_static::static_handler());

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
    tracing::info!("SSR 服务运行在 http://localhost:3000");

    axum::serve(listener, app).await?;

    Ok(())
}
```

---

## 性能监控

### 1. 虚拟 DOM Diff 追踪

```rust
use std::sync::atomic::{AtomicU64, Ordering};

static VDOM_DIFF_COUNT: AtomicU64 = AtomicU64::new(0);

pub fn track_vdom_diff() {
    let count = VDOM_DIFF_COUNT.fetch_add(1, Ordering::Relaxed);
    
    if count % 100 == 0 {
        info!(vdom.diff_count = count, "虚拟 DOM Diff 执行次数");
    }
}

#[component]
fn OptimizedList(cx: Scope, items: Vec<String>) -> Element {
    // 使用 use_memo 避免不必要的重新渲染
    let sorted_items = use_memo(cx, (items,), |(items,)| {
        track_vdom_diff();
        
        let mut sorted = items.clone();
        sorted.sort();
        sorted
    });

    cx.render(rsx! {
        ul {
            for item in sorted_items.iter() {
                li { key: "{item}", "{item}" }
            }
        }
    })
}
```

### 2. 组件渲染性能分析

```rust
use std::collections::HashMap;
use std::sync::Mutex;

lazy_static::lazy_static! {
    static ref RENDER_STATS: Mutex<HashMap<String, Vec<f64>>> = Mutex::new(HashMap::new());
}

pub fn record_render_time(component_name: &str, duration_ms: f64) {
    let mut stats = RENDER_STATS.lock().unwrap();
    stats
        .entry(component_name.to_string())
        .or_insert_with(Vec::new)
        .push(duration_ms);
}

pub fn report_render_stats() {
    let stats = RENDER_STATS.lock().unwrap();
    
    for (component, times) in stats.iter() {
        if times.is_empty() {
            continue;
        }
        
        let sum: f64 = times.iter().sum();
        let avg = sum / times.len() as f64;
        let max = times.iter().cloned().fold(f64::MIN, f64::max);
        
        info!(
            component = component,
            avg_ms = avg,
            max_ms = max,
            count = times.len(),
            "组件渲染统计"
        );
    }
}

#[component]
fn MonitoredComponent(cx: Scope) -> Element {
    let start = std::time::Instant::now();
    
    let result = cx.render(rsx! {
        div { "内容" }
    });
    
    let elapsed = start.elapsed().as_secs_f64() * 1000.0;
    record_render_time("MonitoredComponent", elapsed);
    
    result
}
```

---

## 最佳实践

### 1. 组件性能优化

```rust
// ❌ 不好: 每次都重新创建
#[component]
fn BadExample(cx: Scope, items: Vec<String>) -> Element {
    let filtered: Vec<_> = items
        .iter()
        .filter(|s| s.len() > 5)
        .collect();

    cx.render(rsx! {
        ul {
            for item in filtered {
                li { "{item}" }
            }
        }
    })
}

// ✅ 好: 使用 use_memo 缓存计算结果
#[component]
fn GoodExample(cx: Scope, items: Vec<String>) -> Element {
    let filtered = use_memo(cx, (items,), |(items,)| {
        items
            .iter()
            .filter(|s| s.len() > 5)
            .cloned()
            .collect::<Vec<_>>()
    });

    cx.render(rsx! {
        ul {
            for item in filtered.iter() {
                li { key: "{item}", "{item}" }
            }
        }
    })
}
```

### 2. 错误边界

```rust
#[component]
fn ErrorBoundary<'a>(cx: Scope<'a>, children: Element<'a>) -> Element {
    let error = use_state(cx, || None::<String>);

    if let Some(err) = error.get() {
        tracing::error!(error = %err, "组件错误");
        
        return cx.render(rsx! {
            div {
                class: "error-boundary",
                h2 { "出错了!" }
                p { "{err}" }
                button {
                    onclick: move |_| error.set(None),
                    "重试"
                }
            }
        });
    }

    cx.render(rsx! {
        children
    })
}
```

### 3. 路由追踪

```rust
use dioxus_router::prelude::*;

#[derive(Routable, Clone)]
#[rustfmt::skip]
enum Route {
    #[layout(Layout)]
        #[route("/")]
        Home {},
        #[route("/users")]
        Users {},
        #[route("/users/:id")]
        User { id: i64 },
}

#[component]
fn Layout(cx: Scope) -> Element {
    cx.render(rsx! {
        div {
            nav {
                Link { to: Route::Home {}, "首页" }
                Link { to: Route::Users {}, "用户" }
            }
            Outlet::<Route> {}
        }
    })
}

#[component]
fn Home(cx: Scope) -> Element {
    let _span = span!(Level::INFO, "route", path = "/").entered();
    
    cx.render(rsx! {
        h1 { "首页" }
    })
}

#[component]
fn User(cx: Scope, id: i64) -> Element {
    let _span = span!(Level::INFO, "route", path = "/users/:id", user_id = id).entered();
    
    cx.render(rsx! {
        h1 { "用户 {id}" }
    })
}
```

---

## 完整示例

### 1. 待办事项应用

```rust
use dioxus::prelude::*;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
struct Todo {
    id: u32,
    text: String,
    completed: bool,
}

#[component]
fn TodoApp(cx: Scope) -> Element {
    let todos = use_state(cx, Vec::<Todo>::new);
    let next_id = use_state(cx, || 1u32);
    let input = use_state(cx, String::new);

    let add_todo = move |_| {
        let _span = span!(Level::INFO, "TodoApp::add_todo").entered();
        
        if !input.get().is_empty() {
            let todo = Todo {
                id: *next_id.get(),
                text: input.get().clone(),
                completed: false,
            };

            info!(todo.id = todo.id, todo.text = %todo.text, "添加待办");

            todos.modify(|list| {
                let mut new_list = list.clone();
                new_list.push(todo);
                new_list
            });

            next_id.set(next_id.get() + 1);
            input.set(String::new());
        }
    };

    let toggle_todo = move |id: u32| {
        let _span = span!(Level::INFO, "TodoApp::toggle_todo", todo_id = id).entered();
        
        todos.modify(|list| {
            let mut new_list = list.clone();
            if let Some(todo) = new_list.iter_mut().find(|t| t.id == id) {
                todo.completed = !todo.completed;
                info!(todo.id = id, todo.completed = todo.completed, "切换待办状态");
            }
            new_list
        });
    };

    let delete_todo = move |id: u32| {
        let _span = span!(Level::INFO, "TodoApp::delete_todo", todo_id = id).entered();
        
        todos.modify(|list| {
            let new_list = list.iter().filter(|t| t.id != id).cloned().collect();
            info!(todo.id = id, "删除待办");
            new_list
        });
    };

    cx.render(rsx! {
        div {
            class: "todo-app",
            h1 { "待办事项" }
            
            div {
                class: "input-group",
                input {
                    value: "{input}",
                    placeholder: "添加新待办...",
                    oninput: move |evt| input.set(evt.value.clone()),
                    onkeypress: move |evt| {
                        if evt.key() == keyboard_types::Key::Enter {
                            add_todo(());
                        }
                    }
                }
                button {
                    onclick: add_todo,
                    "添加"
                }
            }

            ul {
                class: "todo-list",
                for todo in todos.iter() {
                    li {
                        key: "{todo.id}",
                        class: if todo.completed { "completed" } else { "" },
                        
                        input {
                            r#type: "checkbox",
                            checked: todo.completed,
                            onchange: move |_| toggle_todo(todo.id)
                        }
                        
                        span { "{todo.text}" }
                        
                        button {
                            onclick: move |_| delete_todo(todo.id),
                            "删除"
                        }
                    }
                }
            }

            div {
                class: "stats",
                "共 {todos.len()} 项, 已完成 {todos.iter().filter(|t| t.completed).count()} 项"
            }
        }
    })
}

fn main() {
    init_telemetry().expect("初始化 OTLP 失败");
    dioxus_web::launch(TodoApp);
}
```

### 2. Docker 部署

```dockerfile
# Dockerfile
FROM rust:1.90-alpine AS builder

WORKDIR /app

RUN apk add --no-cache musl-dev openssl-dev

COPY Cargo.toml Cargo.lock ./
COPY src ./src

RUN cargo build --release --bin dioxus-otlp-app

# 运行时镜像
FROM alpine:latest

RUN apk add --no-cache ca-certificates

COPY --from=builder /app/target/release/dioxus-otlp-app /usr/local/bin/

EXPOSE 3000

ENV RUST_LOG=info
ENV OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4317

CMD ["dioxus-otlp-app"]
```

```yaml
# docker-compose.yml
version: '3.8'

services:
  app:
    build: .
    ports:
      - "3000:3000"
    environment:
      OTEL_EXPORTER_OTLP_ENDPOINT: http://otel-collector:4317
      RUST_LOG: info
    depends_on:
      - otel-collector

  otel-collector:
    image: otel/opentelemetry-collector-contrib:0.98.0
    volumes:
      - ./otel-collector-config.yaml:/etc/otel-collector-config.yaml
    command: ["--config=/etc/otel-collector-config.yaml"]
    ports:
      - "4317:4317"
      - "4318:4318"

  jaeger:
    image: jaegertracing/all-in-one:latest
    ports:
      - "16686:16686"
```

---

## 总结

### 核心要点

1. **Dioxus 跨平台能力**: 一套代码,支持 Web/Desktop/Mobile/TUI
2. **OTLP 全面集成**: 组件渲染、API 调用、事件处理全追踪
3. **性能优化**: `use_memo` 缓存、Virtual DOM 优化
4. **类型安全**: Rust 编译期保证组件 Props 正确性
5. **开发体验**: 类 React 语法,支持热重载

### 性能对比

| 指标 | Dioxus(WASM) | React | Svelte |
|-----|--------------|-------|--------|
| **初始加载** | 200KB | 500KB | 150KB |
| **渲染时间(10k 项)** | 28ms | 45ms | 22ms |
| **内存占用** | 8MB | 15MB | 6MB |
| **首次渲染** | 120ms | 180ms | 100ms |

### 下一步

- **状态管理**: 集成 Fermi(类 Recoil)
- **持久化**: LocalStorage/IndexedDB
- **PWA**: Service Worker + Manifest
- **原生集成**: 调用平台 API(相机/定位等)

---

## 参考资料

- [Dioxus 官方文档](https://dioxuslabs.com/)
- [Dioxus Router](https://dioxuslabs.com/learn/0.5/router)
- [OpenTelemetry Rust SDK](https://docs.rs/opentelemetry)
- [WASM Tracing](https://docs.rs/tracing-wasm)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-11  
**Rust 版本**: 1.90+  
**Dioxus 版本**: 0.6+  
**OpenTelemetry**: 0.30+

