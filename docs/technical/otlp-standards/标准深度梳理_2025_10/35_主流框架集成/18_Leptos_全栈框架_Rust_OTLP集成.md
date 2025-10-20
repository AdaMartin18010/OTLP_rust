# Leptos 全栈框架 - Rust + OTLP 完整集成指南

## 📋 目录

- [Leptos 全栈框架 - Rust + OTLP 完整集成指南](#leptos-全栈框架---rust--otlp-完整集成指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [什么是 Leptos?](#什么是-leptos)
    - [为什么选择 Leptos?](#为什么选择-leptos)
    - [OTLP 集成价值](#otlp-集成价值)
  - [核心概念](#核心概念)
    - [1. Leptos 架构](#1-leptos-架构)
    - [2. 响应式系统](#2-响应式系统)
  - [环境准备](#环境准备)
    - [1. 安装工具链](#1-安装工具链)
    - [2. 项目配置](#2-项目配置)
  - [基础集成](#基础集成)
    - [1. 创建组件](#1-创建组件)
    - [2. 路由配置](#2-路由配置)
    - [3. 服务端函数](#3-服务端函数)
  - [服务端渲染 (SSR)](#服务端渲染-ssr)
    - [1. SSR 配置](#1-ssr-配置)
    - [2. Hydration](#2-hydration)
  - [OTLP 后端追踪](#otlp-后端追踪)
    - [1. 服务端追踪](#1-服务端追踪)
    - [2. Server Function 追踪](#2-server-function-追踪)
  - [前端监控](#前端监控)
    - [1. WASM 性能追踪](#1-wasm-性能追踪)
    - [2. 用户交互追踪](#2-用户交互追踪)
  - [数据获取](#数据获取)
    - [1. Resources](#1-resources)
    - [2. Actions](#2-actions)
  - [状态管理](#状态管理)
    - [1. 全局状态](#1-全局状态)
    - [2. Context API](#2-context-api)
  - [性能优化](#性能优化)
    - [1. 代码分割](#1-代码分割)
    - [2. 懒加载](#2-懒加载)
  - [完整示例](#完整示例)
    - [1. 全栈待办应用](#1-全栈待办应用)
    - [2. 实时聊天应用](#2-实时聊天应用)
  - [部署](#部署)
    - [1. Docker 部署](#1-docker-部署)
    - [2. Vercel/Netlify 部署](#2-vercelnetlify-部署)
  - [最佳实践](#最佳实践)
    - [1. 组件设计](#1-组件设计)
    - [2. 错误处理](#2-错误处理)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [Leptos vs 其他框架](#leptos-vs-其他框架)
    - [下一步](#下一步)
  - [参考资料](#参考资料)

---

## 概述

### 什么是 Leptos?

**Leptos** 是用 Rust 编写的全栈 Web 框架:

```text
┌─────────────────────────────────────┐
│         Leptos Framework            │
│  ┌──────────────────────────────┐   │
│  │  前端 (WASM)                  │  │
│  │  响应式 UI                    │  │
│  │  虚拟 DOM                     │  │
│  ├──────────────────────────────┤   │
│  │  后端 (Axum/Actix)            │  │
│  │  Server Functions            │   │
│  │  SSR                         │   │
│  └──────────────────────────────┘   │
└─────────────────────────────────────┘
```

**核心特性**:

- **全栈Rust**: 前端 + 后端同一语言
- **响应式**: 细粒度响应式系统
- **SSR**: 服务端渲染 + Hydration
- **零JS**: 编译为 WebAssembly
- **类型安全**: 端到端类型安全

### 为什么选择 Leptos?

| 优势 | 说明 |
|------|------|
| **性能卓越** | WASM + 细粒度更新 |
| **类型安全** | Rust 类型系统 |
| **全栈统一** | 前后端共享代码 |
| **现代化** | 类似 React/SolidJS |
| **SEO友好** | SSR 支持 |

### OTLP 集成价值

```text
Browser (WASM) → Server Functions → Backend
    ↓                 ↓                ↓
  RUM追踪          SSR追踪         APM追踪
    ↓                 ↓                ↓
    └──────────→ OTLP ←──────────┘
```

**追踪能力**:

- SSR 渲染时间
- Server Function 调用延迟
- 前端交互性能
- 端到端用户体验

---

## 核心概念

### 1. Leptos 架构

```text
┌─────────────────────────────────────────┐
│         Browser (WebAssembly)           │
│  ┌─────────────────────────────────┐   │
│  │  Leptos Components (WASM)       │   │
│  │  • 响应式 Signals                │   │
│  │  • 虚拟 DOM                      │   │
│  └──────────────┬──────────────────┘   │
└─────────────────┼────────────────────────┘
                  │ Server Functions
┌─────────────────▼────────────────────────┐
│         Server (Axum/Actix)              │
│  ┌─────────────────────────────────┐    │
│  │  SSR Renderer                   │    │
│  │  Server Function Handlers       │    │
│  │  API Routes                     │    │
│  └─────────────────────────────────┘    │
└──────────────────────────────────────────┘
```

### 2. 响应式系统

**Signals**:

```rust
// 创建响应式状态
let (count, set_count) = create_signal(0);

// 读取
let value = count.get();

// 更新
set_count.set(value + 1);

// 派生状态
let doubled = move || count.get() * 2;
```

**Effects**:

```rust
// 自动追踪依赖
create_effect(move |_| {
    // 当 count 变化时自动运行
    log!("Count is: {}", count.get());
});
```

---

## 环境准备

### 1. 安装工具链

```bash
# 安装 Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# 安装 WASM 目标
rustup target add wasm32-unknown-unknown

# 安装 trunk (WASM 打包工具)
cargo install trunk

# 安装 cargo-leptos (Leptos CLI)
cargo install cargo-leptos

# 安装 wasm-bindgen-cli
cargo install wasm-bindgen-cli
```

### 2. 项目配置

```toml
# Cargo.toml
[package]
name = "leptos-otlp-app"
version = "0.1.0"
edition = "2021"

[lib]
crate-type = ["cdylib", "rlib"]

[dependencies]
# Leptos 核心
leptos = { version = "0.6", features = ["csr", "ssr"] }
leptos_axum = { version = "0.6", optional = true }
leptos_router = "0.6"
leptos_meta = "0.6"

# 服务端
axum = { version = "0.7", optional = true }
tokio = { version = "1.37", features = ["full"], optional = true }
tower = { version = "0.4", optional = true }
tower-http = { version = "0.5", features = ["fs"], optional = true }

# WASM
wasm-bindgen = "0.2"
web-sys = { version = "0.3", features = ["Window", "Document", "Element"] }
console_log = "1.0"

# OTLP (服务端)
opentelemetry = { version = "0.30", optional = true }
opentelemetry-otlp = { version = "0.30", optional = true }
opentelemetry_sdk = { version = "0.30", features = ["rt-tokio"], optional = true }
tracing = "0.1"
tracing-subscriber = { version = "0.3", optional = true }
tracing-opentelemetry = { version = "0.31", optional = true }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 错误处理
thiserror = "1.0"

[features]
default = ["csr"]
csr = []  # Client-Side Rendering
ssr = [
    "dep:axum",
    "dep:tokio",
    "dep:tower",
    "dep:tower-http",
    "dep:leptos_axum",
    "dep:opentelemetry",
    "dep:opentelemetry-otlp",
    "dep:opentelemetry_sdk",
    "dep:tracing-subscriber",
    "dep:tracing-opentelemetry",
]

[profile.wasm-release]
inherits = "release"
opt-level = "z"  # 优化大小
lto = true
codegen-units = 1
```

---

## 基础集成

### 1. 创建组件

```rust
// src/components/counter.rs
use leptos::*;

#[component]
pub fn Counter(
    /// 初始值
    #[prop(default = 0)]
    initial_value: i32,
) -> impl IntoView {
    // 创建响应式状态
    let (count, set_count) = create_signal(initial_value);
    
    view! {
        <div class="counter">
            <h2>"Counter: " {count}</h2>
            <button on:click=move |_| {
                set_count.update(|n| *n += 1);
            }>
                "Increment"
            </button>
            <button on:click=move |_| {
                set_count.update(|n| *n -= 1);
            }>
                "Decrement"
            </button>
        </div>
    }
}
```

### 2. 路由配置

```rust
// src/app.rs
use leptos::*;
use leptos_router::*;

#[component]
pub fn App() -> impl IntoView {
    view! {
        <Router>
            <nav>
                <A href="/">"Home"</A>
                <A href="/about">"About"</A>
                <A href="/todos">"Todos"</A>
            </nav>
            
            <main>
                <Routes>
                    <Route path="/" view=Home/>
                    <Route path="/about" view=About/>
                    <Route path="/todos" view=Todos/>
                </Routes>
            </main>
        </Router>
    }
}

#[component]
fn Home() -> impl IntoView {
    view! {
        <div>
            <h1>"Welcome to Leptos!"</h1>
            <Counter initial_value=0/>
        </div>
    }
}

#[component]
fn About() -> impl IntoView {
    view! {
        <div>
            <h1>"About"</h1>
            <p>"Full-stack Rust web framework"</p>
        </div>
    }
}
```

### 3. 服务端函数

```rust
// src/api.rs
use leptos::*;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Todo {
    pub id: u32,
    pub title: String,
    pub completed: bool,
}

/// Server Function - 在服务端运行
#[server(GetTodos, "/api")]
pub async fn get_todos() -> Result<Vec<Todo>, ServerFnError> {
    // 这段代码只在服务端运行
    use sqlx::PgPool;
    
    let pool = use_context::<PgPool>()
        .expect("database pool not found");
    
    let todos = sqlx::query_as!(
        Todo,
        "SELECT id, title, completed FROM todos"
    )
    .fetch_all(&pool)
    .await
    .map_err(|e| ServerFnError::ServerError(e.to_string()))?;
    
    Ok(todos)
}

#[server(CreateTodo, "/api")]
pub async fn create_todo(title: String) -> Result<Todo, ServerFnError> {
    let pool = use_context::<PgPool>()
        .expect("database pool not found");
    
    let todo = sqlx::query_as!(
        Todo,
        "INSERT INTO todos (title, completed) VALUES ($1, false) RETURNING id, title, completed",
        title
    )
    .fetch_one(&pool)
    .await
    .map_err(|e| ServerFnError::ServerError(e.to_string()))?;
    
    Ok(todo)
}

/// 客户端调用 Server Function
#[component]
pub fn Todos() -> impl IntoView {
    // 创建 Resource (自动加载数据)
    let todos = create_resource(
        || (),
        |_| async move { get_todos().await },
    );
    
    // 创建 Action (手动触发)
    let create_todo_action = create_server_action::<CreateTodo>();
    
    view! {
        <div>
            <h1>"Todos"</h1>
            
            // 加载状态
            <Suspense fallback=move || view! { <p>"Loading..."</p> }>
                {move || {
                    todos.get().map(|todos| match todos {
                        Ok(todos) => view! {
                            <ul>
                                {todos.into_iter().map(|todo| {
                                    view! {
                                        <li>{todo.title}</li>
                                    }
                                }).collect_view()}
                            </ul>
                        }.into_view(),
                        Err(e) => view! { <p>"Error: " {e.to_string()}</p> }.into_view(),
                    })
                }}
            </Suspense>
            
            // 创建表单
            <ActionForm action=create_todo_action>
                <input type="text" name="title" placeholder="New todo..."/>
                <button type="submit">"Add"</button>
            </ActionForm>
        </div>
    }
}
```

---

## 服务端渲染 (SSR)

### 1. SSR 配置

```rust
// src/main.rs
#[cfg(feature = "ssr")]
#[tokio::main]
async fn main() {
    use axum::Router;
    use leptos::*;
    use leptos_axum::{generate_route_list, LeptosRoutes};
    
    // 初始化 OTLP
    init_otlp_tracing("leptos-app", "1.0.0", "production").unwrap();
    
    // Leptos 配置
    let conf = get_configuration(None).await.unwrap();
    let leptos_options = conf.leptos_options;
    let routes = generate_route_list(App);
    
    // 创建 Axum 路由
    let app = Router::new()
        .leptos_routes(&leptos_options, routes, App)
        .fallback(leptos_axum::file_and_error_handler(App))
        .with_state(leptos_options);
    
    // 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();
    axum::serve(listener, app).await.unwrap();
}

// 客户端入口
#[cfg(not(feature = "ssr"))]
pub fn main() {
    use leptos::*;
    
    console_error_panic_hook::set_once();
    
    mount_to_body(App);
}
```

### 2. Hydration

```rust
// Leptos 自动处理 Hydration
// 服务端渲染的 HTML 会在客户端自动"激活"

#[component]
pub fn App() -> impl IntoView {
    view! {
        // 这个组件会在服务端渲染
        // 然后在客户端 hydrate
        <div>
            <h1>"Server-Side Rendered!"</h1>
            <Counter/>  // 交互组件会在客户端激活
        </div>
    }
}
```

---

## OTLP 后端追踪

### 1. 服务端追踪

```rust
// src/tracing.rs
#[cfg(feature = "ssr")]
use opentelemetry::{global, trace::TracerProvider, KeyValue};
#[cfg(feature = "ssr")]
use opentelemetry_sdk::{
    trace::{self, RandomIdGenerator, Sampler},
    Resource,
};
#[cfg(feature = "ssr")]
use opentelemetry_otlp::WithExportConfig;

#[cfg(feature = "ssr")]
pub fn init_otlp_tracing(
    service_name: &str,
    version: &str,
    environment: &str,
) -> anyhow::Result<()> {
    let tracer_provider = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317"),
        )
        .with_trace_config(
            trace::config()
                .with_sampler(Sampler::AlwaysOn)
                .with_id_generator(RandomIdGenerator::default())
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", service_name.to_string()),
                    KeyValue::new("service.version", version.to_string()),
                    KeyValue::new("deployment.environment", environment.to_string()),
                ])),
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    global::set_tracer_provider(tracer_provider);
    
    let telemetry = tracing_opentelemetry::layer()
        .with_tracer(global::tracer(service_name));
    
    tracing_subscriber::registry()
        .with(telemetry)
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .init();
    
    Ok(())
}
```

### 2. Server Function 追踪

```rust
use tracing::{info, instrument};

#[server(GetUser, "/api")]
#[instrument(
    name = "server_fn.get_user",
    fields(
        function.name = "GetUser",
        user.id = %user_id,
    )
)]
pub async fn get_user(user_id: String) -> Result<User, ServerFnError> {
    info!("Fetching user: {}", user_id);
    
    let start = std::time::Instant::now();
    
    // 查询数据库
    let user = fetch_user_from_db(&user_id).await?;
    
    let duration = start.elapsed();
    tracing::Span::current().record("db.query.duration_ms", duration.as_millis() as i64);
    
    Ok(user)
}
```

---

## 前端监控

### 1. WASM 性能追踪

```rust
// src/frontend_monitoring.rs
use wasm_bindgen::prelude::*;
use web_sys::Performance;

pub struct FrontendMonitoring {
    performance: Performance,
}

impl FrontendMonitoring {
    pub fn new() -> Self {
        let window = web_sys::window().expect("no window");
        let performance = window.performance().expect("no performance");
        
        Self { performance }
    }
    
    pub fn measure_render(&self, component_name: &str) -> RenderMeasure {
        let start = self.performance.now();
        
        RenderMeasure {
            component_name: component_name.to_string(),
            start,
            performance: self.performance.clone(),
        }
    }
}

pub struct RenderMeasure {
    component_name: String,
    start: f64,
    performance: Performance,
}

impl Drop for RenderMeasure {
    fn drop(&mut self) {
        let duration = self.performance.now() - self.start;
        
        // 发送到后端
        wasm_bindgen_futures::spawn_local({
            let component_name = self.component_name.clone();
            async move {
                let _ = send_metric(&component_name, duration).await;
            }
        });
    }
}

#[server(SendMetric, "/api")]
async fn send_metric(component: String, duration: f64) -> Result<(), ServerFnError> {
    // 记录到 OTLP
    tracing::info!(
        component = %component,
        duration_ms = %duration,
        "Component render time"
    );
    Ok(())
}
```

### 2. 用户交互追踪

```rust
#[component]
pub fn TrackedButton() -> impl IntoView {
    let on_click = move |_| {
        // 追踪点击事件
        wasm_bindgen_futures::spawn_local(async {
            let _ = track_interaction("button_click", "checkout").await;
        });
        
        // 业务逻辑...
    };
    
    view! {
        <button on:click=on_click>
            "Checkout"
        </button>
    }
}

#[server(TrackInteraction, "/api")]
async fn track_interaction(
    event_type: String,
    element_id: String,
) -> Result<(), ServerFnError> {
    tracing::info!(
        event.type = %event_type,
        element.id = %element_id,
        "User interaction"
    );
    Ok(())
}
```

---

## 数据获取

### 1. Resources

```rust
// Resources 用于异步数据加载
#[component]
pub fn UserProfile(user_id: String) -> impl IntoView {
    // 创建 Resource
    let user = create_resource(
        move || user_id.clone(),
        |id| async move {
            get_user(id).await
        },
    );
    
    view! {
        <Suspense fallback=move || view! { <p>"Loading..."</p> }>
            {move || {
                user.get().map(|user| match user {
                    Ok(user) => view! {
                        <div>
                            <h2>{&user.name}</h2>
                            <p>{&user.email}</p>
                        </div>
                    }.into_view(),
                    Err(e) => view! { <p>"Error: " {e.to_string()}</p> }.into_view(),
                })
            }}
        </Suspense>
    }
}
```

### 2. Actions

```rust
// Actions 用于变更数据
#[component]
pub fn CreateUserForm() -> impl IntoView {
    let create_user = create_server_action::<CreateUser>();
    let value = create_user.value();
    
    view! {
        <div>
            <ActionForm action=create_user>
                <input type="text" name="name" placeholder="Name"/>
                <input type="email" name="email" placeholder="Email"/>
                <button type="submit">"Create"</button>
            </ActionForm>
            
            {move || {
                value.get().map(|result| match result {
                    Ok(user) => view! { <p>"Created: " {user.name}</p> }.into_view(),
                    Err(e) => view! { <p>"Error: " {e.to_string()}</p> }.into_view(),
                })
            }}
        </div>
    }
}

#[server(CreateUser, "/api")]
async fn create_user(name: String, email: String) -> Result<User, ServerFnError> {
    // 创建用户...
    Ok(User { name, email })
}
```

---

## 状态管理

### 1. 全局状态

```rust
use leptos::*;

// 创建全局状态
#[derive(Clone)]
pub struct AppState {
    pub user: RwSignal<Option<User>>,
    pub theme: RwSignal<Theme>,
}

#[component]
pub fn App() -> impl IntoView {
    // 初始化全局状态
    let app_state = AppState {
        user: create_rw_signal(None),
        theme: create_rw_signal(Theme::Light),
    };
    
    // 提供到所有子组件
    provide_context(app_state.clone());
    
    view! {
        <Router>
            <Routes>
                <Route path="/" view=Home/>
            </Routes>
        </Router>
    }
}

#[component]
pub fn UserDisplay() -> impl IntoView {
    // 使用全局状态
    let app_state = use_context::<AppState>()
        .expect("AppState not found");
    
    view! {
        <div>
            {move || {
                app_state.user.get().map(|user| {
                    view! { <p>"User: " {user.name}</p> }
                }).unwrap_or_else(|| {
                    view! { <p>"Not logged in"</p> }
                })
            }}
        </div>
    }
}
```

### 2. Context API

```rust
#[component]
pub fn ThemeProvider(children: Children) -> impl IntoView {
    let theme = create_rw_signal(Theme::Light);
    
    provide_context(theme);
    
    view! {
        <div class=move || theme.get().class_name()>
            {children()}
        </div>
    }
}

#[component]
pub fn ThemeToggle() -> impl IntoView {
    let theme = use_context::<RwSignal<Theme>>()
        .expect("Theme not found");
    
    view! {
        <button on:click=move |_| {
            theme.update(|t| *t = t.toggle());
        }>
            "Toggle Theme"
        </button>
    }
}
```

---

## 性能优化

### 1. 代码分割

```rust
// 使用动态导入
#[component]
pub fn LazyComponent() -> impl IntoView {
    view! {
        <Suspense fallback=|| view! { <p>"Loading component..."</p> }>
            <LazyInner/>
        </Suspense>
    }
}

// 这个组件会单独打包
#[component]
fn LazyInner() -> impl IntoView {
    view! {
        <div>"Heavy component loaded!"</div>
    }
}
```

### 2. 懒加载

```rust
#[component]
pub fn ImageGallery(images: Vec<String>) -> impl IntoView {
    view! {
        <div class="gallery">
            {images.into_iter().map(|src| {
                view! {
                    <img
                        src=src
                        loading="lazy"  // 浏览器原生懒加载
                    />
                }
            }).collect_view()}
        </div>
    }
}
```

---

## 完整示例

### 1. 全栈待办应用

见上文 Server Functions 部分。

### 2. 实时聊天应用

```rust
// src/chat.rs
use leptos::*;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Message {
    pub id: u32,
    pub user: String,
    pub content: String,
    pub timestamp: String,
}

#[server(GetMessages, "/api")]
async fn get_messages() -> Result<Vec<Message>, ServerFnError> {
    // 从数据库获取消息
    Ok(vec![])
}

#[server(SendMessage, "/api")]
async fn send_message(content: String) -> Result<Message, ServerFnError> {
    // 保存消息到数据库
    Ok(Message {
        id: 1,
        user: "user".to_string(),
        content,
        timestamp: chrono::Utc::now().to_rfc3339(),
    })
}

#[component]
pub fn Chat() -> impl IntoView {
    let messages = create_resource(|| (), |_| get_messages());
    let send_message_action = create_server_action::<SendMessage>();
    
    view! {
        <div class="chat">
            <div class="messages">
                <Suspense>
                    {move || {
                        messages.get().map(|msgs| match msgs {
                            Ok(msgs) => msgs.into_iter().map(|msg| {
                                view! {
                                    <div class="message">
                                        <strong>{msg.user}</strong>
                                        <p>{msg.content}</p>
                                    </div>
                                }
                            }).collect_view(),
                            Err(_) => view! { <p>"Error loading messages"</p> }.into_view(),
                        })
                    }}
                </Suspense>
            </div>
            
            <ActionForm action=send_message_action>
                <input type="text" name="content" placeholder="Type a message..."/>
                <button type="submit">"Send"</button>
            </ActionForm>
        </div>
    }
}
```

---

## 部署

### 1. Docker 部署

```dockerfile
# Dockerfile
FROM rust:1.90 as builder

WORKDIR /app

# 安装依赖
RUN rustup target add wasm32-unknown-unknown
RUN cargo install cargo-leptos

# 复制项目
COPY . .

# 构建
RUN cargo leptos build --release

# 运行镜像
FROM debian:bookworm-slim

COPY --from=builder /app/target/release/leptos-app /usr/local/bin/
COPY --from=builder /app/target/site /usr/local/share/leptos-app/

EXPOSE 3000

CMD ["leptos-app"]
```

### 2. Vercel/Netlify 部署

```toml
# netlify.toml
[build]
  command = "cargo leptos build --release"
  publish = "target/site"

[[redirects]]
  from = "/*"
  to = "/index.html"
  status = 200
```

---

## 最佳实践

### 1. 组件设计

```rust
// ✅ 好的实践: 小而可复用的组件
#[component]
pub fn Button(
    #[prop(into)] on_click: Callback<MouseEvent>,
    children: Children,
) -> impl IntoView {
    view! {
        <button on:click=on_click>
            {children()}
        </button>
    }
}

// ❌ 避免: 过大的组件
#[component]
pub fn EntireApp() -> impl IntoView {
    // 太多逻辑...
}
```

### 2. 错误处理

```rust
#[server(GetData, "/api")]
async fn get_data() -> Result<Data, ServerFnError> {
    fetch_data()
        .await
        .map_err(|e| ServerFnError::ServerError(e.to_string()))
}
```

---

## 总结

### 核心要点

1. **Leptos**: 全栈Rust Web框架
2. **响应式**: 细粒度响应式系统
3. **SSR**: 服务端渲染 + Hydration
4. **WASM**: 编译为 WebAssembly
5. **类型安全**: 端到端类型安全

### Leptos vs 其他框架

| 特性 | Leptos | Yew | Dioxus | React |
|------|--------|-----|--------|-------|
| **全栈** | ✅ SSR | ⚠️ CSR | ✅ SSR | ✅ SSR |
| **性能** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ |
| **响应式** | ✅ 细粒度 | ❌ VDOM | ✅ 细粒度 | ❌ VDOM |
| **DX** | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| **生态** | 🔄 发展中 | ⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ |

### 下一步

- **Islands Architecture**: 部分hydration
- **Streaming SSR**: 流式服务端渲染
- **WebSocket**: 实时通信

---

## 参考资料

- [Leptos 官方文档](https://leptos.dev/)
- [Leptos Book](https://book.leptos.dev/)
- [Leptos GitHub](https://github.com/leptos-rs/leptos)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-11  
**Rust 版本**: 1.90+  
**Leptos**: 0.6+  
**OpenTelemetry**: 0.30+
