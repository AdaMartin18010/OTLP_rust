# Leptos 全栈响应式框架 - 完整实现指南

## 目录

- [Leptos 全栈响应式框架 - 完整实现指南](#leptos-全栈响应式框架---完整实现指南)
  - [目录](#目录)
  - [1. Leptos 概述](#1-leptos-概述)
    - [1.1 什么是 Leptos?](#11-什么是-leptos)
    - [1.2 Leptos vs 其他前端框架](#12-leptos-vs-其他前端框架)
    - [1.3 典型应用场景](#13-典型应用场景)
  - [2. 核心架构](#2-核心架构)
  - [3. 项目设置](#3-项目设置)
    - [3.1 Cargo.toml](#31-cargotoml)
    - [3.2 Trunk 配置](#32-trunk-配置)
  - [4. 核心概念](#4-核心概念)
    - [4.1 响应式信号 (Signals)](#41-响应式信号-signals)
    - [4.2 组件 (Components)](#42-组件-components)
    - [4.3 路由 (Router)](#43-路由-router)
  - [5. 服务器端渲染 (SSR)](#5-服务器端渲染-ssr)
    - [5.1 SSR 设置](#51-ssr-设置)
    - [5.2 Server Functions](#52-server-functions)
    - [5.3 Hydration](#53-hydration)
  - [6. 状态管理](#6-状态管理)
    - [6.1 全局状态](#61-全局状态)
    - [6.2 异步数据获取](#62-异步数据获取)
  - [7. OTLP 可观测性集成](#7-otlp-可观测性集成)
    - [7.1 前端追踪](#71-前端追踪)
    - [7.2 服务端追踪](#72-服务端追踪)
  - [8. 生产实践](#8-生产实践)
    - [8.1 构建优化](#81-构建优化)
    - [8.2 Docker 部署](#82-docker-部署)
  - [9. 测试策略](#9-测试策略)
    - [9.1 单元测试](#91-单元测试)
    - [9.2 端到端测试](#92-端到端测试)
  - [10. 国际标准对齐](#10-国际标准对齐)
    - [10.1 Web 标准](#101-web-标准)
    - [10.2 OpenTelemetry 语义约定](#102-opentelemetry-语义约定)
  - [总结](#总结)
    - [Leptos 优势](#leptos-优势)
    - [适用场景](#适用场景)

---

## 1. Leptos 概述

### 1.1 什么是 Leptos?

**Leptos** 是一个现代化的 Rust 全栈 Web 框架，提供:

- **细粒度响应式**: 类似 Solid.js 的响应式系统
- **服务器端渲染**: 首屏快速加载 + SEO 友好
- **无虚拟 DOM**: 直接操作真实 DOM，性能优越
- **全栈开发**: 前后端共享代码
- **WebAssembly**: 前端编译为 WASM，极致性能
- **类型安全**: Rust 编译期保证

### 1.2 Leptos vs 其他前端框架

| 特性 | Leptos | Yew | Dioxus | React | Vue |
|------|--------|-----|--------|-------|-----|
| **渲染方式** | 细粒度响应式 | 虚拟 DOM | 虚拟 DOM | 虚拟 DOM | 虚拟 DOM |
| **SSR** | ✅ 原生支持 | ⚠️ 有限 | ✅ 支持 | ✅ 支持 | ✅ 支持 |
| **类型安全** | ✅ Rust 编译期 | ✅ Rust 编译期 | ✅ Rust 编译期 | ⚠️ TypeScript | ⚠️ TypeScript |
| **性能** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ |
| **包体积** | 50-100 KB | 200-300 KB | 150-250 KB | 150-200 KB | 100-150 KB |
| **学习曲线** | ⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐ | ⭐⭐ |

### 1.3 典型应用场景

- ✅ **全栈 Web 应用**: 管理后台、Dashboard
- ✅ **高性能 SPA**: 数据密集型应用
- ✅ **SEO 友好网站**: 博客、文档站
- ✅ **实时应用**: WebSocket + 响应式

---

## 2. 核心架构

```text
┌─────────────────────────────────────────────────────────────┐
│                      Leptos 全栈架构                         │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌──────────────────────────────────────────────┐           │
│  │              客户端 (WebAssembly)             │           │
│  │  • 响应式信号 (Signals)                       │           │
│  │  • 组件树 (Component Tree)                    │           │
│  │  • 路由 (Router)                              │           │
│  │  • 事件处理 (Event Handlers)                  │           │
│  └────────────────┬─────────────────────────────┘           │
│                   │ HTTP/WebSocket                          │
│  ┌────────────────▼─────────────────────────────┐           │
│  │              服务端 (Axum)                    │           │
│  │  • Server Functions                          │           │
│  │  • SSR 渲染                                  │           │
│  │  • API 路由                                  │           │
│  │  • 数据库访问                                 │           │
│  └──────────────────────────────────────────────┘           │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 3. 项目设置

### 3.1 Cargo.toml

```toml
[package]
name = "leptos-app"
version = "0.1.0"
edition = "2021"

[dependencies]
# Leptos 核心
leptos = { version = "0.6", features = ["csr"] }
leptos_meta = "0.6"
leptos_router = "0.6"
leptos_axum = { version = "0.6", optional = true }

# 服务端
axum = { version = "0.7", optional = true }
tokio = { version = "1", features = ["full"], optional = true }
tower = { version = "0.4", optional = true }
tower-http = { version = "0.5", features = ["fs"], optional = true }

# 序列化
serde = { version = "1", features = ["derive"] }
serde_json = "1"

# WASM
wasm-bindgen = "0.2"
console_error_panic_hook = "0.1"
web-sys = { version = "0.3", features = [
    "Window",
    "Document",
    "HtmlElement",
    "Performance",
    "PerformanceNavigationTiming",
] }

# 日志
log = "0.4"
wasm-logger = "0.2"

# OpenTelemetry (服务端)
opentelemetry = { version = "0.25", optional = true }
opentelemetry-otlp = { version = "0.25", features = ["grpc-tonic"], optional = true }
opentelemetry_sdk = { version = "0.25", features = ["rt-tokio"], optional = true }
tracing = "0.1"
tracing-subscriber = { version = "0.3", optional = true }
tracing-opentelemetry = { version = "0.25", optional = true }

[features]
default = ["csr"]
csr = ["leptos/csr"]
ssr = [
    "leptos/ssr",
    "leptos_axum",
    "axum",
    "tokio",
    "tower",
    "tower-http",
    "opentelemetry",
    "opentelemetry-otlp",
    "opentelemetry_sdk",
    "tracing-subscriber",
    "tracing-opentelemetry",
]

[lib]
crate-type = ["cdylib", "rlib"]

[[bin]]
name = "server"
required-features = ["ssr"]
```

### 3.2 Trunk 配置

```toml
# Trunk.toml
[build]
target = "index.html"
dist = "dist"

[watch]
ignore = ["./dist"]

[serve]
address = "127.0.0.1"
port = 8080
```

---

## 4. 核心概念

### 4.1 响应式信号 (Signals)

```rust
use leptos::*;

/// 基础信号
#[component]
pub fn Counter() -> impl IntoView {
    // 创建响应式信号
    let (count, set_count) = create_signal(0);

    view! {
        <div>
            <p>"Count: " {count}</p>
            <button on:click=move |_| set_count.update(|n| *n += 1)>
                "Increment"
            </button>
        </div>
    }
}

/// 派生信号 (Memo)
#[component]
pub fn DoubleCounter() -> impl IntoView {
    let (count, set_count) = create_signal(0);
    
    // 派生信号（自动更新）
    let double_count = create_memo(move |_| count.get() * 2);

    view! {
        <div>
            <p>"Count: " {count}</p>
            <p>"Double: " {double_count}</p>
            <button on:click=move |_| set_count.update(|n| *n += 1)>
                "Increment"
            </button>
        </div>
    }
}

/// Effect (副作用)
#[component]
pub fn Logger() -> impl IntoView {
    let (count, set_count) = create_signal(0);

    // 监听信号变化
    create_effect(move |_| {
        log::info!("Count changed to: {}", count.get());
    });

    view! {
        <button on:click=move |_| set_count.update(|n| *n += 1)>
            "Increment"
        </button>
    }
}
```

### 4.2 组件 (Components)

```rust
use leptos::*;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct User {
    pub id: u32,
    pub name: String,
    pub email: String,
}

/// Props 组件
#[component]
pub fn UserCard(
    user: User,
) -> impl IntoView {
    view! {
        <div class="user-card">
            <h3>{&user.name}</h3>
            <p>{&user.email}</p>
        </div>
    }
}

/// 子组件 (Children)
#[component]
pub fn Card(
    children: Children,
) -> impl IntoView {
    view! {
        <div class="card">
            {children()}
        </div>
    }
}

// 使用示例
#[component]
pub fn App() -> impl IntoView {
    let user = User {
        id: 1,
        name: "Alice".to_string(),
        email: "alice@example.com".to_string(),
    };

    view! {
        <Card>
            <UserCard user=user/>
        </Card>
    }
}
```

### 4.3 路由 (Router)

```rust
use leptos::*;
use leptos_router::*;

#[component]
pub fn AppRouter() -> impl IntoView {
    view! {
        <Router>
            <nav>
                <A href="/">"Home"</A>
                <A href="/about">"About"</A>
                <A href="/users">"Users"</A>
            </nav>
            <main>
                <Routes>
                    <Route path="/" view=Home/>
                    <Route path="/about" view=About/>
                    <Route path="/users" view=UserList/>
                    <Route path="/users/:id" view=UserDetail/>
                    <Route path="/*any" view=NotFound/>
                </Routes>
            </main>
        </Router>
    }
}

#[component]
fn Home() -> impl IntoView {
    view! {
        <h1>"Home Page"</h1>
    }
}

#[component]
fn About() -> impl IntoView {
    view! {
        <h1>"About Page"</h1>
    }
}

#[component]
fn UserList() -> impl IntoView {
    view! {
        <h1>"User List"</h1>
        <ul>
            <li><A href="/users/1">"User 1"</A></li>
            <li><A href="/users/2">"User 2"</A></li>
        </ul>
    }
}

#[component]
fn UserDetail() -> impl IntoView {
    let params = use_params_map();
    let id = move || params.with(|p| p.get("id").cloned().unwrap_or_default());

    view! {
        <h1>"User Detail: " {id}</h1>
    }
}

#[component]
fn NotFound() -> impl IntoView {
    view! {
        <h1>"404 - Not Found"</h1>
    }
}
```

---

## 5. 服务器端渲染 (SSR)

### 5.1 SSR 设置

```rust
// src/main.rs (服务端)
#[cfg(feature = "ssr")]
use axum::{
    Router,
    routing::get,
    extract::State,
    response::IntoResponse,
};
use leptos::*;
use leptos_axum::{generate_route_list, LeptosRoutes};

#[cfg(feature = "ssr")]
#[tokio::main]
async fn main() {
    // 配置 Leptos
    let conf = get_configuration(None).await.unwrap();
    let leptos_options = conf.leptos_options;
    let addr = leptos_options.site_addr;
    let routes = generate_route_list(App);

    // 创建 Axum 路由
    let app = Router::new()
        .leptos_routes(&leptos_options, routes, App)
        .fallback(file_and_error_handler)
        .with_state(leptos_options);

    // 启动服务器
    let listener = tokio::net::TcpListener::bind(&addr).await.unwrap();
    tracing::info!("Server listening on http://{}", addr);
    axum::serve(listener, app.into_make_service())
        .await
        .unwrap();
}

#[cfg(feature = "ssr")]
async fn file_and_error_handler(
    uri: axum::http::Uri,
    State(options): State<LeptosOptions>,
) -> impl IntoResponse {
    let root = options.site_root.clone();
    let res = get_static_file(uri.clone(), &root).await;

    if res.is_err() {
        (
            axum::http::StatusCode::NOT_FOUND,
            "File not found".to_string(),
        )
    } else {
        res.unwrap()
    }
}
```

### 5.2 Server Functions

```rust
use leptos::*;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct User {
    pub id: u32,
    pub name: String,
    pub email: String,
}

/// Server Function (仅在服务端运行)
#[server(GetUsers, "/api")]
pub async fn get_users() -> Result<Vec<User>, ServerFnError> {
    // 模拟数据库查询
    Ok(vec![
        User {
            id: 1,
            name: "Alice".to_string(),
            email: "alice@example.com".to_string(),
        },
        User {
            id: 2,
            name: "Bob".to_string(),
            email: "bob@example.com".to_string(),
        },
    ])
}

#[server(CreateUser, "/api")]
pub async fn create_user(name: String, email: String) -> Result<User, ServerFnError> {
    // 模拟数据库插入
    Ok(User {
        id: 3,
        name,
        email,
    })
}

/// 客户端调用
#[component]
pub fn UserList() -> impl IntoView {
    // 异步加载数据
    let users = create_resource(
        || (),
        |_| async move { get_users().await },
    );

    view! {
        <div>
            <h1>"Users"</h1>
            <Suspense fallback=move || view! { <p>"Loading..."</p> }>
                {move || users.get().map(|users| match users {
                    Ok(users) => view! {
                        <ul>
                            {users.into_iter()
                                .map(|user| view! {
                                    <li>{user.name} " - " {user.email}</li>
                                })
                                .collect_view()}
                        </ul>
                    }.into_view(),
                    Err(e) => view! {
                        <p>"Error: " {e.to_string()}</p>
                    }.into_view(),
                })}
            </Suspense>
        </div>
    }
}
```

### 5.3 Hydration

```rust
// src/lib.rs
use leptos::*;

#[component]
pub fn App() -> impl IntoView {
    view! {
        <div id="app">
            <h1>"Hello, Leptos!"</h1>
            <Counter/>
        </div>
    }
}

// src/main.rs (WASM 入口)
#[cfg(not(feature = "ssr"))]
use leptos::*;

#[cfg(not(feature = "ssr"))]
pub fn main() {
    console_error_panic_hook::set_once();
    wasm_logger::init(wasm_logger::Config::default());

    // Hydrate (激活服务端渲染的 HTML)
    leptos::mount_to_body(App);
}
```

---

## 6. 状态管理

### 6.1 全局状态

```rust
use leptos::*;
use std::sync::Arc;

#[derive(Debug, Clone)]
pub struct AppState {
    pub user: Arc<RwSignal<Option<User>>>,
    pub theme: Arc<RwSignal<String>>,
}

impl AppState {
    pub fn new() -> Self {
        Self {
            user: Arc::new(create_rw_signal(None)),
            theme: Arc::new(create_rw_signal("light".to_string())),
        }
    }
}

/// 全局状态 Provider
#[component]
pub fn AppStateProvider(
    children: Children,
) -> impl IntoView {
    let state = AppState::new();

    view! {
        <Provider value=state>
            {children()}
        </Provider>
    }
}

/// 使用全局状态
#[component]
pub fn UserProfile() -> impl IntoView {
    let state = use_context::<AppState>().expect("AppState not found");
    let user = state.user.clone();

    view! {
        <div>
            {move || user.get().map(|u| view! {
                <p>"Welcome, " {u.name}</p>
            })}
        </div>
    }
}
```

### 6.2 异步数据获取

```rust
use leptos::*;

/// Resource (异步数据加载)
#[component]
pub fn AsyncUserList() -> impl IntoView {
    let (page, set_page) = create_signal(1);

    // 自动重新加载（当 page 变化时）
    let users = create_resource(
        page,
        |page| async move {
            fetch_users(page).await
        },
    );

    view! {
        <div>
            <h1>"Users"</h1>
            <Suspense fallback=move || view! { <p>"Loading..."</p> }>
                {move || users.get().map(|result| match result {
                    Ok(users) => view! {
                        <ul>
                            {users.into_iter()
                                .map(|user| view! { <li>{user.name}</li> })
                                .collect_view()}
                        </ul>
                    }.into_view(),
                    Err(e) => view! {
                        <p>"Error: " {e.to_string()}</p>
                    }.into_view(),
                })}
            </Suspense>
            <button on:click=move |_| set_page.update(|p| *p += 1)>
                "Next Page"
            </button>
        </div>
    }
}

async fn fetch_users(page: i32) -> Result<Vec<User>, String> {
    // 模拟 HTTP 请求
    Ok(vec![])
}
```

---

## 7. OTLP 可观测性集成

### 7.1 前端追踪

```rust
use wasm_bindgen::prelude::*;
use web_sys::{Window, Performance};

/// 前端性能追踪
#[wasm_bindgen]
pub fn track_page_load() {
    let window: Window = web_sys::window().expect("no global `window` exists");
    let performance = window.performance().expect("performance not available");
    
    if let Some(timing) = performance.get_entries_by_type("navigation").get(0) {
        let timing = timing.dyn_into::<web_sys::PerformanceNavigationTiming>().unwrap();
        
        let dns_time = timing.domain_lookup_end() - timing.domain_lookup_start();
        let tcp_time = timing.connect_end() - timing.connect_start();
        let request_time = timing.response_start() - timing.request_start();
        let response_time = timing.response_end() - timing.response_start();
        let dom_time = timing.dom_content_loaded_event_end() - timing.dom_content_loaded_event_start();
        let load_time = timing.load_event_end() - timing.load_event_start();

        log::info!("DNS Lookup: {:.2}ms", dns_time);
        log::info!("TCP Connection: {:.2}ms", tcp_time);
        log::info!("Request Time: {:.2}ms", request_time);
        log::info!("Response Time: {:.2}ms", response_time);
        log::info!("DOM Processing: {:.2}ms", dom_time);
        log::info!("Page Load: {:.2}ms", load_time);
    }
}

/// 用户交互追踪
#[component]
pub fn TrackedButton(
    on_click: Box<dyn Fn()>,
    children: Children,
) -> impl IntoView {
    let click_handler = move |_| {
        let start = web_sys::window()
            .unwrap()
            .performance()
            .unwrap()
            .now();

        on_click();

        let end = web_sys::window()
            .unwrap()
            .performance()
            .unwrap()
            .now();

        log::info!("Button click handled in {:.2}ms", end - start);
    };

    view! {
        <button on:click=click_handler>
            {children()}
        </button>
    }
}
```

### 7.2 服务端追踪

```rust
#[cfg(feature = "ssr")]
use opentelemetry::{global, trace::{SpanKind, Tracer, Status}, KeyValue};

#[cfg(feature = "ssr")]
pub fn init_telemetry() -> anyhow::Result<()> {
    use opentelemetry_otlp::WithExportConfig;
    use opentelemetry_sdk::{runtime, trace as sdktrace, Resource};

    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .with_trace_config(
            sdktrace::Config::default().with_resource(Resource::new(vec![
                KeyValue::new("service.name", "leptos-app"),
                KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
            ]))
        )
        .install_batch(runtime::Tokio)?;

    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new("info"))
        .with(tracing_subscriber::fmt::layer().json())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    Ok(())
}

#[cfg(feature = "ssr")]
#[server(TracedGetUsers, "/api")]
pub async fn traced_get_users() -> Result<Vec<User>, ServerFnError> {
    let tracer = global::tracer("leptos-server");
    
    let mut span = tracer
        .span_builder("Server Function: get_users")
        .with_kind(SpanKind::Server)
        .start(&tracer);
    
    let start = std::time::Instant::now();
    
    let result = get_users().await;
    
    let duration = start.elapsed();
    
    match &result {
        Ok(users) => {
            span.set_attribute(KeyValue::new("users.count", users.len() as i64));
            span.set_attribute(KeyValue::new("duration_ms", duration.as_millis() as i64));
        }
        Err(e) => {
            span.set_status(Status::error(e.to_string()));
            span.set_attribute(KeyValue::new("error", true));
        }
    }
    
    span.end();
    
    result
}
```

---

## 8. 生产实践

### 8.1 构建优化

```toml
# Cargo.toml
[profile.release]
opt-level = 'z'        # 优化体积
lto = true             # Link Time Optimization
codegen-units = 1      # 单一代码生成单元
panic = 'abort'        # 移除展开代码
strip = true           # 移除符号
```

```bash
# 构建客户端 (WASM)
trunk build --release

# 构建服务端
cargo build --release --features ssr --bin server
```

### 8.2 Docker 部署

```dockerfile
# Dockerfile
FROM rust:1.90 AS builder

WORKDIR /app

# 安装 Trunk
RUN cargo install trunk

# 复制源代码
COPY . .

# 构建 WASM (客户端)
RUN trunk build --release

# 构建服务端
RUN cargo build --release --features ssr --bin server

# 运行时镜像
FROM debian:bookworm-slim

COPY --from=builder /app/target/release/server /usr/local/bin/
COPY --from=builder /app/dist /usr/local/share/dist

ENV LEPTOS_SITE_ROOT=/usr/local/share/dist

EXPOSE 3000

CMD ["server"]
```

---

## 9. 测试策略

### 9.1 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_counter() {
        let runtime = create_runtime();
        
        let (count, set_count) = create_signal(0);
        
        assert_eq!(count.get(), 0);
        
        set_count.set(10);
        assert_eq!(count.get(), 10);
        
        runtime.dispose();
    }
}
```

### 9.2 端到端测试

```rust
// 使用 WebDriver
#[cfg(test)]
mod e2e_tests {
    use fantoccini::{ClientBuilder, Locator};

    #[tokio::test]
    async fn test_counter_increment() {
        let client = ClientBuilder::native()
            .connect("http://localhost:4444")
            .await
            .expect("failed to connect to WebDriver");

        client.goto("http://localhost:8080").await.unwrap();

        let button = client.find(Locator::Css("button")).await.unwrap();
        button.click().await.unwrap();

        let count = client.find(Locator::Css("p")).await.unwrap();
        let text = count.text().await.unwrap();

        assert!(text.contains("1"));

        client.close().await.unwrap();
    }
}
```

---

## 10. 国际标准对齐

### 10.1 Web 标准

- ✅ **HTML5**: 语义化标签
- ✅ **CSS3**: 现代样式
- ✅ **ES2020**: JavaScript 互操作
- ✅ **WebAssembly**: WASM 标准
- ✅ **Web Components**: 自定义元素

### 10.2 OpenTelemetry 语义约定

```rust
// HTTP Semantic Conventions (v1.21.0)
span.set_attribute(KeyValue::new("http.method", "GET"));
span.set_attribute(KeyValue::new("http.url", "https://example.com/api/users"));
span.set_attribute(KeyValue::new("http.status_code", 200));

// Server Function Conventions
span.set_attribute(KeyValue::new("leptos.server_fn", "get_users"));
span.set_attribute(KeyValue::new("leptos.render_mode", "ssr"));
```

---

## 总结

### Leptos 优势

1. **极致性能**: 细粒度响应式 + 无虚拟 DOM
2. **全栈类型安全**: Rust 编译期保证
3. **优秀的 SSR**: 首屏快速加载 + SEO 友好
4. **小包体积**: WASM 体积 < 100 KB
5. **现代开发体验**: 响应式编程范式

### 适用场景

- ✅ **高性能 Web 应用**: Dashboard, Admin Panel
- ✅ **SEO 友好网站**: 博客、文档站
- ✅ **实时应用**: WebSocket + 响应式
- ✅ **全栈 Rust 项目**: 前后端共享代码

---

**版权**: MIT License  
**作者**: OTLP Rust 项目组  
**最后更新**: 2025-10-11
