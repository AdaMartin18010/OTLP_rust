# Dioxus 完整实现：跨平台 UI 框架（Rust 1.90 + OTLP 集成）

## 目录

- [Dioxus 完整实现：跨平台 UI 框架（Rust 1.90 + OTLP 集成）](#dioxus-完整实现跨平台-ui-框架rust-190--otlp-集成)
  - [目录](#目录)
  - [1. Dioxus 概述](#1-dioxus-概述)
    - [1.1 核心特性](#11-核心特性)
    - [1.2 跨平台支持](#12-跨平台支持)
    - [1.3 技术架构](#13-技术架构)
  - [2. 国际标准对齐](#2-国际标准对齐)
    - [2.1 Web 标准](#21-web-标准)
    - [2.2 移动端标准](#22-移动端标准)
    - [2.3 桌面端标准](#23-桌面端标准)
  - [3. 项目初始化](#3-项目初始化)
    - [3.1 依赖配置](#31-依赖配置)
    - [3.2 CLI 工具](#32-cli-工具)
    - [3.3 项目结构](#33-项目结构)
  - [4. 组件系统](#4-组件系统)
    - [4.1 函数式组件](#41-函数式组件)
    - [4.2 Props 传递](#42-props-传递)
    - [4.3 RSX 宏](#43-rsx-宏)
  - [5. 状态管理](#5-状态管理)
    - [5.1 use\_signal Hook](#51-use_signal-hook)
    - [5.2 use\_context 全局状态](#52-use_context-全局状态)
    - [5.3 Fermi 状态管理](#53-fermi-状态管理)
  - [6. 路由系统](#6-路由系统)
    - [6.1 声明式路由](#61-声明式路由)
    - [6.2 导航守卫](#62-导航守卫)
    - [6.3 嵌套路由](#63-嵌套路由)
  - [7. 异步处理](#7-异步处理)
    - [7.1 use\_future Hook](#71-use_future-hook)
    - [7.2 use\_resource Hook](#72-use_resource-hook)
    - [7.3 Suspense 边界](#73-suspense-边界)
  - [8. 跨平台渲染](#8-跨平台渲染)
    - [8.1 Web 渲染](#81-web-渲染)
    - [8.2 桌面应用](#82-桌面应用)
    - [8.3 移动应用](#83-移动应用)
    - [8.4 服务端渲染](#84-服务端渲染)
  - [9. 性能优化](#9-性能优化)
    - [9.1 虚拟 DOM Diff](#91-虚拟-dom-diff)
    - [9.2 记忆化组件](#92-记忆化组件)
    - [9.3 懒加载](#93-懒加载)
  - [10. OTLP 集成](#10-otlp-集成)
    - [10.1 前端性能追踪](#101-前端性能追踪)
    - [10.2 用户行为分析](#102-用户行为分析)
    - [10.3 错误追踪](#103-错误追踪)
  - [11. 测试策略](#11-测试策略)
    - [11.1 单元测试](#111-单元测试)
    - [11.2 集成测试](#112-集成测试)
    - [11.3 端到端测试](#113-端到端测试)
  - [12. 生产部署](#12-生产部署)
    - [12.1 构建优化](#121-构建优化)
    - [12.2 Docker 部署](#122-docker-部署)
    - [12.3 桌面应用打包](#123-桌面应用打包)
  - [总结](#总结)
    - [核心优势](#核心优势)
    - [国际标准对齐](#国际标准对齐)
    - [适用场景](#适用场景)

---

## 1. Dioxus 概述

**Dioxus** 是一个现代化的 Rust UI 框架，提供跨平台的 UI 开发能力，支持 **Web、Desktop、Mobile、Server-Side Rendering (SSR)**，核心设计理念是 "Write once, run everywhere"。

### 1.1 核心特性

| 特性 | 说明 | 对标标准 |
|------|------|----------|
| **RSX 宏** | React-like 的 JSX 语法，声明式 UI | JSX (React) |
| **虚拟 DOM** | 高效的 Diff 算法，减少实际 DOM 更新 | Virtual DOM (React, Vue) |
| **跨平台** | 单一代码库支持 Web/Desktop/Mobile | Flutter, React Native |
| **类型安全** | Rust 强类型系统，编译期错误检测 | TypeScript, Elm |
| **异步支持** | 原生支持 `async`/`await`，无 Promise 封装 | Rust Async Runtime |
| **Hooks API** | 函数式组件 + Hooks，状态管理更简洁 | React Hooks |

### 1.2 跨平台支持

```rust
// Web: wasm32-unknown-unknown
dioxus-web = "0.5"

// Desktop: Tauri/Wry (WebView)
dioxus-desktop = "0.5"

// Mobile: iOS/Android (通过 Tauri Mobile)
dioxus-mobile = "0.5"

// SSR: 服务端渲染
dioxus-ssr = "0.5"

// Terminal: 终端 UI
dioxus-tui = "0.5"
```

### 1.3 技术架构

```text
┌─────────────────────────────────────────────┐
│            Dioxus Application               │
│  (RSX Macros + Components + Hooks)          │
└─────────────┬───────────────────────────────┘
              │
              ├───► Web (WASM) ──────► Browser
              │      └─ dioxus-web
              │
              ├───► Desktop ──────► Wry/WebView
              │      └─ dioxus-desktop
              │
              ├───► Mobile ──────► iOS/Android
              │      └─ dioxus-mobile
              │
              ├───► SSR ──────► HTML String
              │      └─ dioxus-ssr
              │
              └───► TUI ──────► Terminal
                     └─ dioxus-tui
```

---

## 2. 国际标准对齐

### 2.1 Web 标准

| 标准 | 版本 | 说明 |
|------|------|------|
| **WebAssembly** | WASM 1.0 | Dioxus Web 编译为 WASM 字节码 |
| **HTML5** | 5.3 | 标准 DOM 元素和事件 |
| **CSS3** | CSS3 | 样式支持（通过 Tailwind/inline CSS） |
| **ES6 Modules** | ECMAScript 2015 | JavaScript 互操作 (wasm-bindgen) |
| **Web Workers** | W3C | 后台线程支持 |

### 2.2 移动端标准

| 标准 | 说明 |
|------|------|
| **iOS SDK** | UIKit/SwiftUI 互操作 |
| **Android SDK** | JNI 绑定 |
| **Mobile Web Standards** | Responsive Design, Touch Events |

### 2.3 桌面端标准

| 标准 | 说明 |
|------|------|
| **Wry** | Tauri 提供的跨平台 WebView |
| **Window Management** | 窗口大小、位置、多窗口 |
| **Native Dialogs** | 文件选择器、通知 |

---

## 3. 项目初始化

### 3.1 依赖配置

**Cargo.toml**:

```toml
[package]
name = "dioxus-app"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# Dioxus 核心
dioxus = "0.5"

# Web 渲染 (WASM)
dioxus-web = { version = "0.5", optional = true }

# 桌面应用
dioxus-desktop = { version = "0.5", optional = true }

# 服务端渲染
dioxus-ssr = { version = "0.5", optional = true }

# 路由
dioxus-router = "0.5"

# 状态管理
fermi = "0.5"

# HTTP 客户端 (WASM 兼容)
reqwest = { version = "0.12", features = ["json"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 日志
tracing = "0.1"
tracing-subscriber = "0.3"

# OpenTelemetry (可选)
opentelemetry = { version = "0.25", optional = true }
opentelemetry-otlp = { version = "0.25", optional = true }
tracing-opentelemetry = { version = "0.26", optional = true }

# 时间处理
chrono = { version = "0.4", features = ["serde"] }

[features]
default = ["web"]
web = ["dioxus-web"]
desktop = ["dioxus-desktop"]
ssr = ["dioxus-ssr"]
telemetry = ["opentelemetry", "opentelemetry-otlp", "tracing-opentelemetry"]

[profile.release]
opt-level = 'z'          # 优化大小
lto = true               # 链接时优化
codegen-units = 1        # 单个代码生成单元
strip = true             # 移除符号
panic = 'abort'          # 减小二进制大小
```

### 3.2 CLI 工具

```bash
# 安装 Dioxus CLI
cargo install dioxus-cli

# 创建新项目
dx new dioxus-app
cd dioxus-app

# Web 开发服务器 (热重载)
dx serve --platform web

# 桌面应用开发
dx serve --platform desktop

# 构建 Web 生产版本
dx build --release --platform web

# 构建桌面应用
dx build --release --platform desktop
```

### 3.3 项目结构

```text
dioxus-app/
├── Cargo.toml
├── Dioxus.toml              # Dioxus CLI 配置
├── assets/                  # 静态资源
│   ├── images/
│   └── styles/
│       └── tailwind.css
├── src/
│   ├── main.rs              # 入口文件
│   ├── components/          # 可复用组件
│   │   ├── mod.rs
│   │   ├── header.rs
│   │   └── footer.rs
│   ├── pages/               # 页面组件
│   │   ├── mod.rs
│   │   ├── home.rs
│   │   └── about.rs
│   ├── hooks/               # 自定义 Hooks
│   │   ├── mod.rs
│   │   └── use_fetch.rs
│   ├── services/            # 业务逻辑
│   │   ├── mod.rs
│   │   └── api.rs
│   └── utils/               # 工具函数
│       └── mod.rs
├── tests/
│   └── integration_test.rs
└── README.md
```

**Dioxus.toml**:

```toml
[application]
name = "dioxus-app"
default_platform = "web"

[web.app]
title = "Dioxus Application"
base_path = "/"

[web.watcher]
reload_html = true
watch_path = ["src", "assets"]

[web.resource]
style = ["assets/styles/tailwind.css"]

[web.proxy]
backend = "http://localhost:8080"
```

---

## 4. 组件系统

### 4.1 函数式组件

**src/main.rs**:

```rust
use dioxus::prelude::*;

fn main() {
    // Web 启动
    #[cfg(feature = "web")]
    dioxus_web::launch(App);
    
    // 桌面启动
    #[cfg(feature = "desktop")]
    dioxus_desktop::launch(App);
}

/// 根组件
fn App() -> Element {
    rsx! {
        div {
            class: "app",
            Header {}
            Counter {}
            Footer {}
        }
    }
}

/// Header 组件
fn Header() -> Element {
    rsx! {
        header {
            class: "bg-blue-600 text-white p-4",
            h1 { "Dioxus Application" }
            nav {
                ul {
                    class: "flex space-x-4",
                    li { Link { to: "/", "Home" } }
                    li { Link { to: "/about", "About" } }
                }
            }
        }
    }
}

/// 计数器组件
fn Counter() -> Element {
    // use_signal: 创建响应式状态
    let mut count = use_signal(|| 0);
    
    rsx! {
        div {
            class: "counter p-8",
            h2 { "Counter" }
            p { "Count: {count}" }
            div {
                class: "space-x-2",
                button {
                    class: "bg-green-500 text-white px-4 py-2 rounded",
                    onclick: move |_| count += 1,
                    "Increment"
                }
                button {
                    class: "bg-red-500 text-white px-4 py-2 rounded",
                    onclick: move |_| count -= 1,
                    "Decrement"
                }
                button {
                    class: "bg-gray-500 text-white px-4 py-2 rounded",
                    onclick: move |_| count.set(0),
                    "Reset"
                }
            }
        }
    }
}

/// Footer 组件
fn Footer() -> Element {
    rsx! {
        footer {
            class: "bg-gray-800 text-white p-4 text-center",
            p { "© 2025 Dioxus Application" }
        }
    }
}
```

### 4.2 Props 传递

**src/components/user_card.rs**:

```rust
use dioxus::prelude::*;
use serde::{Deserialize, Serialize};

/// 用户数据结构
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct User {
    pub id: u64,
    pub name: String,
    pub email: String,
    pub avatar: String,
}

/// UserCard Props
#[derive(Props, Clone, PartialEq)]
pub struct UserCardProps {
    pub user: User,
    pub on_delete: EventHandler<u64>,
}

/// UserCard 组件
pub fn UserCard(props: UserCardProps) -> Element {
    let user = &props.user;
    
    rsx! {
        div {
            class: "user-card border rounded-lg p-4 shadow-md",
            img {
                src: "{user.avatar}",
                alt: "{user.name}",
                class: "w-16 h-16 rounded-full"
            }
            h3 { class: "text-xl font-bold", "{user.name}" }
            p { class: "text-gray-600", "{user.email}" }
            button {
                class: "bg-red-500 text-white px-4 py-2 rounded mt-2",
                onclick: move |_| props.on_delete.call(user.id),
                "Delete"
            }
        }
    }
}
```

### 4.3 RSX 宏

RSX (Rust Syntax Extension) 提供类似 JSX 的声明式语法：

```rust
// 条件渲染
rsx! {
    if is_logged_in {
        p { "Welcome back!" }
    } else {
        p { "Please log in." }
    }
}

// 列表渲染
rsx! {
    ul {
        for user in users {
            li { key: "{user.id}", "{user.name}" }
        }
    }
}

// 动态属性
rsx! {
    button {
        class: if is_active { "active" } else { "inactive" },
        disabled: is_loading,
        "Submit"
    }
}

// 事件处理
rsx! {
    input {
        r#type: "text",
        value: "{input_value}",
        oninput: move |evt| input_value.set(evt.value()),
    }
}
```

---

## 5. 状态管理

### 5.1 use_signal Hook

**局部状态管理**：

```rust
use dioxus::prelude::*;

fn TodoApp() -> Element {
    let mut todos = use_signal(Vec::<String>::new);
    let mut input = use_signal(String::new);
    
    rsx! {
        div {
            class: "todo-app",
            h1 { "Todo List" }
            
            // 输入框
            div {
                input {
                    r#type: "text",
                    value: "{input}",
                    oninput: move |evt| input.set(evt.value()),
                    placeholder: "Enter a task..."
                }
                button {
                    onclick: move |_| {
                        if !input().is_empty() {
                            todos.write().push(input().clone());
                            input.set(String::new());
                        }
                    },
                    "Add"
                }
            }
            
            // Todo 列表
            ul {
                for (idx, todo) in todos.read().iter().enumerate() {
                    li {
                        key: "{idx}",
                        span { "{todo}" }
                        button {
                            onclick: move |_| { todos.write().remove(idx); },
                            "Delete"
                        }
                    }
                }
            }
        }
    }
}
```

### 5.2 use_context 全局状态

**src/state/theme.rs**:

```rust
use dioxus::prelude::*;

#[derive(Clone, Copy, PartialEq)]
pub enum Theme {
    Light,
    Dark,
}

/// 全局主题状态
pub fn use_theme() -> Signal<Theme> {
    use_context()
}

/// 提供主题上下文
pub fn ThemeProvider(children: Element) -> Element {
    let mut theme = use_signal(|| Theme::Light);
    
    use_context_provider(|| theme);
    
    rsx! {
        div {
            class: if theme() == Theme::Light { "light" } else { "dark" },
            {children}
        }
    }
}

/// 主题切换组件
pub fn ThemeToggle() -> Element {
    let mut theme = use_theme();
    
    rsx! {
        button {
            onclick: move |_| {
                theme.set(if theme() == Theme::Light {
                    Theme::Dark
                } else {
                    Theme::Light
                });
            },
            "Toggle Theme"
        }
    }
}
```

**使用示例**：

```rust
fn App() -> Element {
    rsx! {
        ThemeProvider {
            Header {}
            ThemeToggle {}
            Content {}
        }
    }
}
```

### 5.3 Fermi 状态管理

**全局原子状态**（类似 Recoil/Jotai）：

```rust
use fermi::*;
use dioxus::prelude::*;

// 定义全局 Atom
static USER: Atom<Option<User>> = Atom(|_| None);
static IS_LOADING: Atom<bool> = Atom(|_| false);

/// 登录组件
fn LoginForm() -> Element {
    let mut user = use_atom_state(&USER);
    let mut is_loading = use_atom_state(&IS_LOADING);
    
    let on_login = move |_| async move {
        is_loading.set(true);
        
        // 模拟 API 请求
        let result = fetch_user().await;
        
        if let Ok(u) = result {
            user.set(Some(u));
        }
        
        is_loading.set(false);
    };
    
    rsx! {
        button {
            onclick: on_login,
            disabled: *is_loading.current(),
            "Login"
        }
    }
}

/// 用户信息组件
fn UserProfile() -> Element {
    let user = use_atom_state(&USER);
    
    match user.current().as_ref() {
        Some(u) => rsx! {
            div {
                h2 { "Welcome, {u.name}!" }
                p { "Email: {u.email}" }
            }
        },
        None => rsx! {
            p { "Not logged in" }
        }
    }
}
```

---

## 6. 路由系统

### 6.1 声明式路由

**src/main.rs**:

```rust
use dioxus::prelude::*;
use dioxus_router::prelude::*;

#[derive(Clone, Routable, PartialEq)]
#[rustfmt::skip]
enum Route {
    #[route("/")]
    Home {},
    
    #[route("/about")]
    About {},
    
    #[route("/users")]
    UserList {},
    
    #[route("/users/:id")]
    UserDetail { id: u64 },
    
    #[route("/blog/:slug")]
    BlogPost { slug: String },
    
    #[route("/:..route")]
    NotFound { route: Vec<String> },
}

fn App() -> Element {
    rsx! {
        Router::<Route> {}
    }
}

#[component]
fn Home() -> Element {
    rsx! {
        div {
            h1 { "Home Page" }
            Link { to: Route::About {}, "Go to About" }
        }
    }
}

#[component]
fn About() -> Element {
    rsx! {
        div {
            h1 { "About Page" }
            Link { to: Route::Home {}, "Back to Home" }
        }
    }
}

#[component]
fn UserDetail(id: u64) -> Element {
    let user = use_resource(move || async move {
        fetch_user_by_id(id).await
    });
    
    match user.read().as_ref() {
        Some(Ok(u)) => rsx! {
            div {
                h1 { "User: {u.name}" }
                p { "Email: {u.email}" }
            }
        },
        Some(Err(e)) => rsx! { p { "Error: {e}" } },
        None => rsx! { p { "Loading..." } },
    }
}

#[component]
fn NotFound(route: Vec<String>) -> Element {
    rsx! {
        div {
            h1 { "404 - Page Not Found" }
            p { "Requested path: /{route.join("/")}" }
            Link { to: Route::Home {}, "Go Home" }
        }
    }
}
```

### 6.2 导航守卫

**权限检查**：

```rust
use dioxus::prelude::*;
use dioxus_router::prelude::*;

#[component]
fn ProtectedRoute(children: Element) -> Element {
    let user = use_atom_state(&USER);
    let nav = navigator();
    
    use_effect(move || {
        if user.current().is_none() {
            nav.push(Route::Login {});
        }
    });
    
    match user.current().as_ref() {
        Some(_) => rsx! { {children} },
        None => rsx! { p { "Redirecting..." } },
    }
}

// 使用示例
#[route("/dashboard")]
Dashboard {},

#[component]
fn Dashboard() -> Element {
    rsx! {
        ProtectedRoute {
            div {
                h1 { "Dashboard" }
                // ... 受保护的内容
            }
        }
    }
}
```

### 6.3 嵌套路由

```rust
#[derive(Clone, Routable, PartialEq)]
enum Route {
    #[route("/")]
    Home {},
    
    #[nest("/admin")]
        #[route("/")]
        AdminDashboard {},
        
        #[route("/users")]
        AdminUsers {},
        
        #[route("/settings")]
        AdminSettings {},
    #[end_nest]
    
    #[route("/:..route")]
    NotFound { route: Vec<String> },
}

#[component]
fn AdminLayout() -> Element {
    rsx! {
        div {
            class: "admin-layout",
            nav {
                Link { to: Route::AdminDashboard {}, "Dashboard" }
                Link { to: Route::AdminUsers {}, "Users" }
                Link { to: Route::AdminSettings {}, "Settings" }
            }
            Outlet::<Route> {}
        }
    }
}
```

---

## 7. 异步处理

### 7.1 use_future Hook

**一次性异步任务**：

```rust
use dioxus::prelude::*;

fn DataFetcher() -> Element {
    let data = use_future(|| async {
        fetch_data_from_api().await
    });
    
    match data.value() {
        Some(Ok(result)) => rsx! {
            div { "Data: {result}" }
        },
        Some(Err(e)) => rsx! {
            div { "Error: {e}" }
        },
        None => rsx! {
            div { "Loading..." }
        },
    }
}
```

### 7.2 use_resource Hook

**响应式异步任务**（依赖变化时重新执行）：

```rust
use dioxus::prelude::*;

fn UserProfile() -> Element {
    let user_id = use_signal(|| 1u64);
    
    // 当 user_id 变化时自动重新获取
    let user = use_resource(move || async move {
        fetch_user_by_id(user_id()).await
    });
    
    rsx! {
        div {
            // 用户选择器
            select {
                onchange: move |evt| {
                    if let Ok(id) = evt.value().parse::<u64>() {
                        user_id.set(id);
                    }
                },
                option { value: "1", "User 1" }
                option { value: "2", "User 2" }
                option { value: "3", "User 3" }
            }
            
            // 用户信息
            match user.read().as_ref() {
                Some(Ok(u)) => rsx! {
                    div {
                        h2 { "{u.name}" }
                        p { "{u.email}" }
                    }
                },
                Some(Err(e)) => rsx! { p { "Error: {e}" } },
                None => rsx! { p { "Loading..." } },
            }
        }
    }
}
```

### 7.3 Suspense 边界

**统一处理多个异步组件的加载状态**：

```rust
fn App() -> Element {
    rsx! {
        Suspense {
            fallback: |_| rsx! {
                div { class: "loading-spinner", "Loading..." }
            },
            UserProfile {}
            PostList {}
            CommentSection {}
        }
    }
}
```

---

## 8. 跨平台渲染

### 8.1 Web 渲染

**编译为 WASM**：

```bash
# 安装 wasm-pack
cargo install wasm-pack

# 构建 Web 版本
dx build --release --platform web

# 输出目录: dist/
# - index.html
# - assets/
#   - dioxus/
#     - dioxus-app_bg.wasm
#     - dioxus-app.js
```

**index.html**:

```html
<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Dioxus App</title>
    <link rel="stylesheet" href="/assets/styles/tailwind.css">
</head>
<body>
    <div id="main"></div>
    <script type="module" src="/assets/dioxus/dioxus-app.js"></script>
</body>
</html>
```

### 8.2 桌面应用

**基于 Tauri/Wry 的桌面应用**：

```rust
// src/main.rs
#[cfg(feature = "desktop")]
fn main() {
    use dioxus_desktop::{Config, WindowBuilder};
    
    dioxus_desktop::launch_cfg(
        App,
        Config::new()
            .with_window(
                WindowBuilder::new()
                    .with_title("Dioxus Desktop App")
                    .with_inner_size(dioxus_desktop::LogicalSize::new(1200, 800))
                    .with_resizable(true)
            )
            .with_custom_head("<style>body { margin: 0; }</style>".into())
    );
}
```

**窗口管理**：

```rust
use dioxus::prelude::*;
use dioxus_desktop::use_window;

fn WindowControls() -> Element {
    let window = use_window();
    
    rsx! {
        div {
            class: "window-controls",
            button {
                onclick: move |_| window.toggle_fullscreen(),
                "Toggle Fullscreen"
            }
            button {
                onclick: move |_| window.minimize(),
                "Minimize"
            }
            button {
                onclick: move |_| window.close(),
                "Close"
            }
        }
    }
}
```

### 8.3 移动应用

**iOS/Android 支持**（通过 Tauri Mobile）：

```bash
# 安装 Tauri Mobile CLI
cargo install tauri-mobile

# 初始化移动项目
tauri mobile init

# iOS 开发
tauri mobile ios dev

# Android 开发
tauri mobile android dev

# 构建
tauri mobile ios build --release
tauri mobile android build --release
```

**移动端适配**：

```rust
fn ResponsiveLayout() -> Element {
    let is_mobile = use_signal(|| {
        #[cfg(target_os = "ios")]
        return true;
        #[cfg(target_os = "android")]
        return true;
        false
    });
    
    rsx! {
        div {
            class: if is_mobile() { "mobile-layout" } else { "desktop-layout" },
            // 内容
        }
    }
}
```

### 8.4 服务端渲染

**SSR 渲染为 HTML 字符串**：

```rust
use dioxus::prelude::*;
use dioxus_ssr::render;

fn render_app_to_html() -> String {
    render! {
        App {}
    }
}

#[tokio::main]
async fn main() {
    let html = render_app_to_html();
    println!("{}", html);
}
```

**与 Axum 集成**：

```rust
use axum::{response::Html, routing::get, Router};
use dioxus::prelude::*;

async fn render_page() -> Html<String> {
    let html = dioxus_ssr::render! {
        App {}
    };
    
    Html(format!(
        r#"
        <!DOCTYPE html>
        <html>
        <head>
            <title>Dioxus SSR</title>
        </head>
        <body>
            <div id="main">{}</div>
        </body>
        </html>
        "#,
        html
    ))
}

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/", get(render_page));
    
    axum::Server::bind(&"0.0.0.0:3000".parse().unwrap())
        .serve(app.into_make_service())
        .await
        .unwrap();
}
```

---

## 9. 性能优化

### 9.1 虚拟 DOM Diff

Dioxus 使用高效的 Diff 算法，仅更新变化的 DOM 节点：

```rust
// 使用 key 优化列表渲染
rsx! {
    ul {
        for item in items {
            li {
                key: "{item.id}",  // 稳定的唯一标识
                "{item.name}"
            }
        }
    }
}
```

### 9.2 记忆化组件

**use_memo Hook**：

```rust
fn ExpensiveComponent() -> Element {
    let data = use_signal(|| vec![1, 2, 3, 4, 5]);
    
    // 仅当 data 变化时重新计算
    let sum = use_memo(move || {
        data().iter().sum::<i32>()
    });
    
    rsx! {
        div {
            p { "Sum: {sum}" }
        }
    }
}
```

### 9.3 懒加载

**代码分割**：

```rust
// 懒加载组件
async fn load_admin_panel() -> Element {
    // 动态加载大型组件
    rsx! {
        AdminPanel {}
    }
}

fn App() -> Element {
    let show_admin = use_signal(|| false);
    
    rsx! {
        div {
            button {
                onclick: move |_| show_admin.set(true),
                "Load Admin Panel"
            }
            
            if show_admin() {
                Suspense {
                    fallback: |_| rsx! { p { "Loading admin panel..." } },
                    load_admin_panel().await
                }
            }
        }
    }
}
```

---

## 10. OTLP 集成

### 10.1 前端性能追踪

**src/telemetry.rs**:

```rust
use opentelemetry::{global, trace::Tracer, KeyValue};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{runtime, trace::Config, Resource};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

/// 初始化 OTLP 遥测 (Web 环境)
pub fn init_telemetry() -> anyhow::Result<()> {
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .http()
                .with_endpoint("http://localhost:4318/v1/traces")
        )
        .with_trace_config(
            Config::default()
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", "dioxus-app"),
                    KeyValue::new("deployment.environment", "production"),
                ]))
        )
        .install_batch(runtime::Tokio)?;
    
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();
    
    Ok(())
}

/// 追踪组件渲染
#[tracing::instrument(skip(component_name))]
pub fn trace_component_render(component_name: &str) {
    tracing::info!(
        component = component_name,
        "Component rendered"
    );
}
```

**使用示例**：

```rust
fn TrackedComponent() -> Element {
    use_effect(|| {
        trace_component_render("TrackedComponent");
    });
    
    rsx! {
        div { "Tracked Component" }
    }
}
```

### 10.2 用户行为分析

**追踪用户交互**：

```rust
use tracing::info_span;

fn AnalyticsButton() -> Element {
    rsx! {
        button {
            onclick: move |_| {
                let span = info_span!(
                    "button_click",
                    button_id = "submit_form",
                    user_id = "user_123"
                );
                let _guard = span.enter();
                
                tracing::info!("Button clicked");
                
                // 业务逻辑
                handle_submit();
            },
            "Submit"
        }
    }
}
```

### 10.3 错误追踪

**捕获组件错误**：

```rust
use dioxus::prelude::*;
use tracing::error;

fn ErrorBoundary(children: Element) -> Element {
    let error = use_signal(|| None::<String>);
    
    use_effect(move || {
        // 监听全局错误
        if let Some(err) = error() {
            error!(
                error = %err,
                "Component error occurred"
            );
        }
    });
    
    rsx! {
        div {
            if let Some(err) = error() {
                div {
                    class: "error-message",
                    "Error: {err}"
                }
            } else {
                {children}
            }
        }
    }
}
```

---

## 11. 测试策略

### 11.1 单元测试

**tests/unit_test.rs**:

```rust
use dioxus::prelude::*;

#[test]
fn test_counter_increment() {
    let mut vdom = VirtualDom::new(Counter);
    vdom.rebuild();
    
    // 模拟点击
    vdom.handle_event(
        "click",
        Event::new(EventData::Click, false),
        ElementId(0),
        false,
    );
    
    vdom.wait_for_work();
    
    // 验证状态
    // ...
}
```

### 11.2 集成测试

**tests/integration_test.rs**:

```rust
#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
#[cfg_attr(not(target_arch = "wasm32"), test)]
async fn test_user_login_flow() {
    // 渲染应用
    let mut vdom = VirtualDom::new(App);
    vdom.rebuild();
    
    // 模拟用户登录流程
    // 1. 输入用户名
    // 2. 输入密码
    // 3. 点击登录按钮
    // 4. 验证成功跳转
    
    // 断言
    assert!(/* 验证登录成功 */);
}
```

### 11.3 端到端测试

**使用 Playwright (Rust)**：

```rust
use chromiumoxide::Browser;

#[tokio::test]
async fn e2e_test_homepage() -> anyhow::Result<()> {
    let (browser, mut handler) = Browser::launch(
        chromiumoxide::BrowserConfig::builder()
            .build()?
    ).await?;
    
    let page = browser.new_page("http://localhost:8080").await?;
    
    // 等待页面加载
    page.wait_for_navigation().await?;
    
    // 验证标题
    let title = page.get_title().await?;
    assert_eq!(title, Some("Dioxus Application".to_string()));
    
    // 点击按钮
    page.click("button.submit").await?;
    
    // 验证跳转
    let url = page.url().await?;
    assert!(url.as_str().contains("/success"));
    
    browser.close().await?;
    Ok(())
}
```

---

## 12. 生产部署

### 12.1 构建优化

**Cargo.toml**:

```toml
[profile.release]
opt-level = 'z'          # 优化大小
lto = true               # 链接时优化
codegen-units = 1        # 单个代码生成单元
strip = true             # 移除符号
panic = 'abort'          # 减小二进制大小

[profile.release.package."*"]
opt-level = 'z'
```

**构建命令**：

```bash
# Web 构建
dx build --release --platform web

# 压缩 WASM (使用 wasm-opt)
wasm-opt -Oz -o dist/assets/dioxus/app_bg.wasm \
    dist/assets/dioxus/app_bg.wasm

# 桌面构建
dx build --release --platform desktop
```

### 12.2 Docker 部署

**Dockerfile** (Web):

```dockerfile
# 构建阶段
FROM rust:1.90 AS builder

WORKDIR /app
COPY . .

# 安装 Dioxus CLI
RUN cargo install dioxus-cli

# 构建 Web 应用
RUN dx build --release --platform web

# 运行阶段
FROM nginx:alpine

# 复制构建产物
COPY --from=builder /app/dist /usr/share/nginx/html

# Nginx 配置 (SPA 路由)
COPY <<EOF /etc/nginx/conf.d/default.conf
server {
    listen 80;
    server_name localhost;
    root /usr/share/nginx/html;
    index index.html;
    
    location / {
        try_files \$uri \$uri/ /index.html;
    }
}
EOF

EXPOSE 80
CMD ["nginx", "-g", "daemon off;"]
```

**docker-compose.yml**:

```yaml
version: '3.9'

services:
  dioxus-app:
    build:
      context: .
      dockerfile: Dockerfile
    ports:
      - "8080:80"
    environment:
      - RUST_LOG=info
    restart: unless-stopped
    
  # OpenTelemetry Collector
  otel-collector:
    image: otel/opentelemetry-collector-contrib:0.110.0
    command: ["--config=/etc/otel-collector-config.yaml"]
    volumes:
      - ./otel-collector-config.yaml:/etc/otel-collector-config.yaml
    ports:
      - "4318:4318"   # OTLP HTTP
      - "4317:4317"   # OTLP gRPC
    
  # Jaeger (后端)
  jaeger:
    image: jaegertracing/all-in-one:latest
    ports:
      - "16686:16686"  # Jaeger UI
    environment:
      - COLLECTOR_OTLP_ENABLED=true
```

### 12.3 桌面应用打包

**Windows**:

```bash
# 构建 Windows 可执行文件
dx build --release --platform desktop

# 输出: target/release/dioxus-app.exe

# 使用 Inno Setup 创建安装程序
iscc installer_script.iss
```

**macOS**:

```bash
# 构建 macOS 应用
dx build --release --platform desktop

# 创建 .app bundle
dx bundle --release

# 输出: target/release/bundle/macos/DioxusApp.app

# 代码签名 (需要 Apple Developer 证书)
codesign --force --deep --sign "Developer ID Application: Your Name" \
    target/release/bundle/macos/DioxusApp.app

# 创建 DMG
hdiutil create -volname "Dioxus App" -srcfolder \
    target/release/bundle/macos/DioxusApp.app \
    -ov -format UDZO DioxusApp.dmg
```

**Linux**:

```bash
# 构建 Linux 可执行文件
dx build --release --platform desktop

# 创建 AppImage
dx bundle --release --format appimage

# 输出: target/release/bundle/appimage/dioxus-app.AppImage
```

---

## 总结

Dioxus 提供了 **真正的跨平台 UI 开发体验**，通过统一的 Rust 代码库支持 Web、Desktop、Mobile、SSR 和 TUI：

### 核心优势

1. **单一代码库**: 一次编写，多平台运行
2. **类型安全**: Rust 强类型系统，编译期错误检测
3. **高性能**: 虚拟 DOM + 零成本抽象
4. **现代化 API**: React-like Hooks + RSX 宏
5. **OTLP 集成**: 全面的可观测性支持

### 国际标准对齐

- **Web**: WebAssembly, HTML5, CSS3, ES6 Modules
- **Desktop**: Wry/WebView, Native Dialogs
- **Mobile**: iOS SDK, Android SDK
- **Observability**: OpenTelemetry Protocol, W3C Trace Context

### 适用场景

- 跨平台桌面应用（Electron 替代方案）
- 高性能 Web 应用（React/Vue 替代方案）
- 原生移动应用（React Native/Flutter 替代方案）
- 服务端渲染（Next.js 替代方案）

Dioxus 是 Rust 生态中最接近 **"Write Once, Run Everywhere"** 理念的 UI 框架，适合需要 **高性能、类型安全、跨平台** 的现代应用开发。
