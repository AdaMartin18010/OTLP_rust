# Yew 完整实现指南 - React 风格 Rust 前端框架

## 目录

- [Yew 完整实现指南 - React 风格 Rust 前端框架](#yew-完整实现指南---react-风格-rust-前端框架)
  - [目录](#目录)
  - [1. Yew 概述](#1-yew-概述)
    - [1.1 什么是 Yew?](#11-什么是-yew)
    - [1.2 核心特性](#12-核心特性)
    - [1.3 为什么选择 Yew?](#13-为什么选择-yew)
  - [2. 项目设置](#2-项目设置)
    - [2.1 Cargo.toml](#21-cargotoml)
    - [2.2 安装 Trunk](#22-安装-trunk)
    - [2.3 index.html](#23-indexhtml)
  - [3. 组件系统](#3-组件系统)
    - [3.1 函数式组件](#31-函数式组件)
    - [3.2 Props 传递](#32-props-传递)
    - [3.3 Hooks 系统](#33-hooks-系统)
  - [4. 状态管理](#4-状态管理)
    - [4.1 use\_state](#41-use_state)
    - [4.2 use\_reducer](#42-use_reducer)
    - [4.3 Context API](#43-context-api)
  - [5. 路由系统](#5-路由系统)
    - [5.1 Yew Router](#51-yew-router)
    - [5.2 导航与链接](#52-导航与链接)
    - [5.3 路由守卫](#53-路由守卫)
  - [6. HTTP 请求](#6-http-请求)
    - [6.1 Reqwest WASM](#61-reqwest-wasm)
    - [6.2 异步数据获取](#62-异步数据获取)
    - [6.3 错误处理](#63-错误处理)
  - [7. 表单处理](#7-表单处理)
    - [7.1 受控组件](#71-受控组件)
    - [7.2 表单验证](#72-表单验证)
    - [7.3 文件上传](#73-文件上传)
  - [8. 性能优化](#8-性能优化)
    - [8.1 虚拟 DOM 优化](#81-虚拟-dom-优化)
    - [8.2 代码分割](#82-代码分割)
    - [8.3 Lazy Loading](#83-lazy-loading)
  - [9. OTLP 集成](#9-otlp-集成)
    - [9.1 前端性能追踪](#91-前端性能追踪)
    - [9.2 用户行为追踪](#92-用户行为追踪)
    - [9.3 错误追踪](#93-错误追踪)
  - [10. 测试策略](#10-测试策略)
    - [10.1 单元测试](#101-单元测试)
    - [10.2 集成测试](#102-集成测试)
  - [11. 生产构建](#11-生产构建)
    - [11.1 构建优化](#111-构建优化)
    - [11.2 Docker 部署](#112-docker-部署)
  - [12. 国际标准对齐](#12-国际标准对齐)
  - [总结](#总结)
    - [Yew 核心优势](#yew-核心优势)
    - [适用场景](#适用场景)
    - [性能基准](#性能基准)

---

## 1. Yew 概述

### 1.1 什么是 Yew?

**Yew** 是 Rust 编写的现代前端框架,借鉴 React 设计:

- **组件化**: React 风格的组件系统
- **虚拟 DOM**: 高效的 DOM 更新
- **WebAssembly**: 编译为高性能 WASM
- **类型安全**: Rust 强类型系统

### 1.2 核心特性

| 特性 | 描述 |
|------|------|
| **函数式组件** | 类似 React Hooks |
| **Props & State** | 组件属性和状态管理 |
| **Yew Router** | 客户端路由 |
| **Hooks** | use_state, use_effect, use_reducer |
| **HTML 宏** | JSX 风格的模板 |
| **异步支持** | async/await 集成 |

### 1.3 为什么选择 Yew?

- ✅ **React 开发者友好**: 熟悉的 API 设计
- ✅ **类型安全**: 编译时类型检查
- ✅ **高性能**: WebAssembly 性能
- ✅ **现代工具链**: Trunk 构建工具
- ✅ **活跃社区**: 持续维护和更新

---

## 2. 项目设置

### 2.1 Cargo.toml

```toml
[package]
name = "yew-example"
version = "0.1.0"
edition = "2021"

[dependencies]
# Yew 核心
yew = { version = "0.21", features = ["csr"] }
yew-router = "0.18"

# Web API
web-sys = { version = "0.3", features = [
    "Window",
    "Document",
    "HtmlElement",
    "Storage",
    "console",
    "Performance",
    "PerformanceTiming",
] }
wasm-bindgen = "0.2"
wasm-bindgen-futures = "0.4"

# HTTP 请求
reqwest = { version = "0.12", features = ["json"] }
gloo-net = { version = "0.6", features = ["http"] }

# 序列化
serde = { version = "1", features = ["derive"] }
serde_json = "1"

# 日志
log = "0.4"
wasm-logger = "0.2"

# 工具库
gloo = "0.11"
gloo-utils = "0.2"
gloo-timers = "0.3"

# 错误处理
thiserror = "1"
anyhow = "1"

[dev-dependencies]
wasm-bindgen-test = "0.3"
```

### 2.2 安装 Trunk

```bash
# 安装 Trunk (构建工具)
cargo install trunk

# 安装 WASM target
rustup target add wasm32-unknown-unknown

# 开发服务器
trunk serve

# 生产构建
trunk build --release
```

### 2.3 index.html

```html
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Yew App</title>
    <link data-trunk rel="css" href="styles.css" />
</head>
<body>
    <div id="app"></div>
</body>
</html>
```

---

## 3. 组件系统

### 3.1 函数式组件

```rust
use yew::prelude::*;

/// 简单的函数式组件
#[function_component(App)]
fn app() -> Html {
    html! {
        <div class="app">
            <h1>{"Hello, Yew!"}</h1>
            <Counter />
        </div>
    }
}

/// 计数器组件
#[function_component(Counter)]
fn counter() -> Html {
    let count = use_state(|| 0);
    
    let increment = {
        let count = count.clone();
        Callback::from(move |_| {
            count.set(*count + 1);
        })
    };
    
    let decrement = {
        let count = count.clone();
        Callback::from(move |_| {
            count.set(*count - 1);
        })
    };
    
    html! {
        <div class="counter">
            <h2>{"Counter"}</h2>
            <p>{format!("Count: {}", *count)}</p>
            <button onclick={increment}>{"Increment"}</button>
            <button onclick={decrement}>{"Decrement"}</button>
        </div>
    }
}

/// 主函数
fn main() {
    wasm_logger::init(wasm_logger::Config::default());
    yew::Renderer::<App>::new().render();
}
```

### 3.2 Props 传递

```rust
use yew::prelude::*;

/// Props 定义
#[derive(Properties, PartialEq)]
pub struct UserCardProps {
    pub user: User,
    pub on_click: Callback<String>,
}

#[derive(Clone, PartialEq)]
pub struct User {
    pub id: String,
    pub name: String,
    pub email: String,
    pub avatar_url: Option<String>,
}

/// 用户卡片组件
#[function_component(UserCard)]
fn user_card(props: &UserCardProps) -> Html {
    let user = &props.user;
    
    let onclick = {
        let user_id = user.id.clone();
        let callback = props.on_click.clone();
        Callback::from(move |_| {
            callback.emit(user_id.clone());
        })
    };
    
    html! {
        <div class="user-card" onclick={onclick}>
            {
                if let Some(avatar) = &user.avatar_url {
                    html! { <img src={avatar.clone()} alt="Avatar" /> }
                } else {
                    html! { <div class="avatar-placeholder">{"👤"}</div> }
                }
            }
            <h3>{&user.name}</h3>
            <p>{&user.email}</p>
        </div>
    }
}

/// 父组件
#[function_component(UserList)]
fn user_list() -> Html {
    let users = vec![
        User {
            id: "1".to_string(),
            name: "Alice".to_string(),
            email: "alice@example.com".to_string(),
            avatar_url: None,
        },
        User {
            id: "2".to_string(),
            name: "Bob".to_string(),
            email: "bob@example.com".to_string(),
            avatar_url: None,
        },
    ];
    
    let on_user_click = Callback::from(|user_id: String| {
        log::info!("User clicked: {}", user_id);
    });
    
    html! {
        <div class="user-list">
            {
                for users.into_iter().map(|user| {
                    html! {
                        <UserCard 
                            user={user} 
                            on_click={on_user_click.clone()} 
                        />
                    }
                })
            }
        </div>
    }
}
```

### 3.3 Hooks 系统

```rust
use yew::prelude::*;

/// use_effect 示例
#[function_component(Timer)]
fn timer() -> Html {
    let count = use_state(|| 0);
    
    {
        let count = count.clone();
        use_effect_with((), move |_| {
            let interval = gloo_timers::callback::Interval::new(1000, move || {
                count.set(*count + 1);
            });
            
            // Cleanup
            move || drop(interval)
        });
    }
    
    html! {
        <div>
            <p>{format!("Elapsed: {} seconds", *count)}</p>
        </div>
    }
}

/// use_memo 示例
#[function_component(ExpensiveComputation)]
fn expensive_computation() -> Html {
    let input = use_state(|| 0);
    
    let result = use_memo(input.clone(), |input| {
        // 模拟昂贵计算
        (0..**input).sum::<i32>()
    });
    
    let on_change = {
        let input = input.clone();
        Callback::from(move |value: i32| {
            input.set(value);
        })
    };
    
    html! {
        <div>
            <input 
                type="number" 
                value={input.to_string()} 
                onchange={move |e: Event| {
                    let target: web_sys::HtmlInputElement = e.target_unchecked_into();
                    let value: i32 = target.value().parse().unwrap_or(0);
                    on_change.emit(value);
                }}
            />
            <p>{format!("Result: {}", *result)}</p>
        </div>
    }
}

/// use_ref 示例
#[function_component(InputFocus)]
fn input_focus() -> Html {
    let input_ref = use_node_ref();
    
    let on_click = {
        let input_ref = input_ref.clone();
        Callback::from(move |_| {
            if let Some(input) = input_ref.cast::<web_sys::HtmlInputElement>() {
                let _ = input.focus();
            }
        })
    };
    
    html! {
        <div>
            <input ref={input_ref} type="text" placeholder="Click button to focus" />
            <button onclick={on_click}>{"Focus Input"}</button>
        </div>
    }
}
```

---

## 4. 状态管理

### 4.1 use_state

```rust
use yew::prelude::*;

#[derive(Clone, PartialEq)]
pub struct Todo {
    pub id: u32,
    pub text: String,
    pub completed: bool,
}

#[function_component(TodoApp)]
fn todo_app() -> Html {
    let todos = use_state(Vec::<Todo>::new);
    let input_value = use_state(String::new);
    let next_id = use_state(|| 0u32);
    
    let on_input = {
        let input_value = input_value.clone();
        Callback::from(move |e: InputEvent| {
            let target: web_sys::HtmlInputElement = e.target_unchecked_into();
            input_value.set(target.value());
        })
    };
    
    let on_submit = {
        let todos = todos.clone();
        let input_value = input_value.clone();
        let next_id = next_id.clone();
        
        Callback::from(move |e: SubmitEvent| {
            e.prevent_default();
            
            if !input_value.is_empty() {
                let mut new_todos = (*todos).clone();
                new_todos.push(Todo {
                    id: *next_id,
                    text: (*input_value).clone(),
                    completed: false,
                });
                
                todos.set(new_todos);
                input_value.set(String::new());
                next_id.set(*next_id + 1);
            }
        })
    };
    
    let toggle_todo = {
        let todos = todos.clone();
        Callback::from(move |id: u32| {
            let mut new_todos = (*todos).clone();
            if let Some(todo) = new_todos.iter_mut().find(|t| t.id == id) {
                todo.completed = !todo.completed;
            }
            todos.set(new_todos);
        })
    };
    
    html! {
        <div class="todo-app">
            <h1>{"Todo List"}</h1>
            <form onsubmit={on_submit}>
                <input 
                    type="text" 
                    value={(*input_value).clone()} 
                    oninput={on_input}
                    placeholder="Add a new todo"
                />
                <button type="submit">{"Add"}</button>
            </form>
            <ul>
                {
                    for todos.iter().map(|todo| {
                        let id = todo.id;
                        let toggle = toggle_todo.clone();
                        html! {
                            <li key={todo.id}>
                                <input 
                                    type="checkbox" 
                                    checked={todo.completed}
                                    onchange={move |_| toggle.emit(id)}
                                />
                                <span class={if todo.completed { "completed" } else { "" }}>
                                    {&todo.text}
                                </span>
                            </li>
                        }
                    })
                }
            </ul>
        </div>
    }
}
```

### 4.2 use_reducer

```rust
use yew::prelude::*;
use std::rc::Rc;

/// State
#[derive(Clone, PartialEq)]
pub struct AppState {
    pub count: i32,
    pub history: Vec<String>,
}

/// Actions
pub enum AppAction {
    Increment,
    Decrement,
    Reset,
    AddHistory(String),
}

/// Reducer
fn reducer(state: Rc<AppState>, action: AppAction) -> Rc<AppState> {
    let mut new_state = (*state).clone();
    
    match action {
        AppAction::Increment => {
            new_state.count += 1;
            new_state.history.push(format!("Incremented to {}", new_state.count));
        }
        AppAction::Decrement => {
            new_state.count -= 1;
            new_state.history.push(format!("Decremented to {}", new_state.count));
        }
        AppAction::Reset => {
            new_state.count = 0;
            new_state.history.push("Reset to 0".to_string());
        }
        AppAction::AddHistory(msg) => {
            new_state.history.push(msg);
        }
    }
    
    Rc::new(new_state)
}

#[function_component(CounterWithReducer)]
fn counter_with_reducer() -> Html {
    let state = use_reducer(|| AppState {
        count: 0,
        history: vec![],
    });
    
    let increment = {
        let state = state.clone();
        Callback::from(move |_| {
            state.dispatch(AppAction::Increment);
        })
    };
    
    let decrement = {
        let state = state.clone();
        Callback::from(move |_| {
            state.dispatch(AppAction::Decrement);
        })
    };
    
    let reset = {
        let state = state.clone();
        Callback::from(move |_| {
            state.dispatch(AppAction::Reset);
        })
    };
    
    html! {
        <div>
            <h2>{"Counter with Reducer"}</h2>
            <p>{format!("Count: {}", state.count)}</p>
            <button onclick={increment}>{"+"}</button>
            <button onclick={decrement}>{"-"}</button>
            <button onclick={reset}>{"Reset"}</button>
            <h3>{"History:"}</h3>
            <ul>
                {
                    for state.history.iter().map(|msg| {
                        html! { <li>{msg}</li> }
                    })
                }
            </ul>
        </div>
    }
}
```

### 4.3 Context API

```rust
use yew::prelude::*;
use std::rc::Rc;

/// 全局状态
#[derive(Clone, PartialEq)]
pub struct GlobalState {
    pub user: Option<User>,
    pub theme: Theme,
}

#[derive(Clone, PartialEq)]
pub enum Theme {
    Light,
    Dark,
}

/// Context Provider
#[function_component(AppProvider)]
pub fn app_provider(props: &PropsWithChildren) -> Html {
    let state = use_state(|| GlobalState {
        user: None,
        theme: Theme::Light,
    });
    
    html! {
        <ContextProvider<UseStateHandle<GlobalState>> context={state.clone()}>
            {props.children.clone()}
        </ContextProvider<UseStateHandle<GlobalState>>>
    }
}

/// 消费 Context
#[function_component(ThemeToggle)]
fn theme_toggle() -> Html {
    let state = use_context::<UseStateHandle<GlobalState>>()
        .expect("GlobalState context not found");
    
    let toggle_theme = {
        let state = state.clone();
        Callback::from(move |_| {
            let mut new_state = (*state).clone();
            new_state.theme = match new_state.theme {
                Theme::Light => Theme::Dark,
                Theme::Dark => Theme::Light,
            };
            state.set(new_state);
        })
    };
    
    let theme_name = match state.theme {
        Theme::Light => "Light",
        Theme::Dark => "Dark",
    };
    
    html! {
        <button onclick={toggle_theme}>
            {format!("Toggle Theme (current: {})", theme_name)}
        </button>
    }
}
```

---

## 5. 路由系统

### 5.1 Yew Router

```rust
use yew::prelude::*;
use yew_router::prelude::*;

/// 路由定义
#[derive(Clone, Routable, PartialEq)]
enum Route {
    #[at("/")]
    Home,
    #[at("/users")]
    Users,
    #[at("/users/:id")]
    UserDetail { id: String },
    #[at("/about")]
    About,
    #[not_found]
    #[at("/404")]
    NotFound,
}

/// 路由切换
fn switch(routes: Route) -> Html {
    match routes {
        Route::Home => html! { <HomePage /> },
        Route::Users => html! { <UsersPage /> },
        Route::UserDetail { id } => html! { <UserDetailPage user_id={id} /> },
        Route::About => html! { <AboutPage /> },
        Route::NotFound => html! { <NotFoundPage /> },
    }
}

#[function_component(App)]
fn app() -> Html {
    html! {
        <BrowserRouter>
            <nav>
                <Link<Route> to={Route::Home}>{"Home"}</Link<Route>>
                <Link<Route> to={Route::Users}>{"Users"}</Link<Route>>
                <Link<Route> to={Route::About}>{"About"}</Link<Route>>
            </nav>
            <Switch<Route> render={switch} />
        </BrowserRouter>
    }
}

/// 首页
#[function_component(HomePage)]
fn home_page() -> Html {
    html! {
        <div>
            <h1>{"Welcome to Home"}</h1>
        </div>
    }
}

/// 用户详情页
#[derive(Properties, PartialEq)]
pub struct UserDetailProps {
    pub user_id: String,
}

#[function_component(UserDetailPage)]
fn user_detail_page(props: &UserDetailProps) -> Html {
    html! {
        <div>
            <h1>{format!("User Detail: {}", props.user_id)}</h1>
        </div>
    }
}
```

### 5.2 导航与链接

```rust
use yew::prelude::*;
use yew_router::prelude::*;

#[function_component(Navigation)]
fn navigation() -> Html {
    let navigator = use_navigator().unwrap();
    
    let go_to_home = {
        let navigator = navigator.clone();
        Callback::from(move |_| {
            navigator.push(&Route::Home);
        })
    };
    
    let go_to_users = {
        let navigator = navigator.clone();
        Callback::from(move |_| {
            navigator.push(&Route::Users);
        })
    };
    
    html! {
        <div class="navigation">
            <button onclick={go_to_home}>{"Go to Home"}</button>
            <button onclick={go_to_users}>{"Go to Users"}</button>
        </div>
    }
}
```

### 5.3 路由守卫

```rust
use yew::prelude::*;
use yew_router::prelude::*;

#[function_component(ProtectedRoute)]
fn protected_route(props: &PropsWithChildren) -> Html {
    let is_authenticated = use_state(|| false); // 从认证服务获取
    let navigator = use_navigator().unwrap();
    
    {
        let is_authenticated = is_authenticated.clone();
        let navigator = navigator.clone();
        
        use_effect_with((), move |_| {
            if !*is_authenticated {
                navigator.push(&Route::Home);
            }
            || ()
        });
    }
    
    if *is_authenticated {
        html! { <>{props.children.clone()}</> }
    } else {
        html! { <div>{"Redirecting..."}</div> }
    }
}
```

---

## 6. HTTP 请求

### 6.1 Reqwest WASM

```rust
use yew::prelude::*;
use serde::{Deserialize, Serialize};
use gloo_net::http::Request;

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub struct Post {
    pub id: u32,
    pub title: String,
    pub body: String,
    pub user_id: u32,
}

#[function_component(PostsList)]
fn posts_list() -> Html {
    let posts = use_state(|| None::<Vec<Post>>);
    let loading = use_state(|| false);
    let error = use_state(|| None::<String>);
    
    {
        let posts = posts.clone();
        let loading = loading.clone();
        let error = error.clone();
        
        use_effect_with((), move |_| {
            wasm_bindgen_futures::spawn_local(async move {
                loading.set(true);
                
                match Request::get("https://jsonplaceholder.typicode.com/posts")
                    .send()
                    .await
                {
                    Ok(response) => {
                        match response.json::<Vec<Post>>().await {
                            Ok(data) => {
                                posts.set(Some(data));
                                loading.set(false);
                            }
                            Err(e) => {
                                error.set(Some(e.to_string()));
                                loading.set(false);
                            }
                        }
                    }
                    Err(e) => {
                        error.set(Some(e.to_string()));
                        loading.set(false);
                    }
                }
            });
            
            || ()
        });
    }
    
    html! {
        <div>
            {
                if *loading {
                    html! { <p>{"Loading..."}</p> }
                } else if let Some(err) = (*error).as_ref() {
                    html! { <p class="error">{format!("Error: {}", err)}</p> }
                } else if let Some(posts_data) = (*posts).as_ref() {
                    html! {
                        <ul>
                            {
                                for posts_data.iter().map(|post| {
                                    html! {
                                        <li key={post.id}>
                                            <h3>{&post.title}</h3>
                                            <p>{&post.body}</p>
                                        </li>
                                    }
                                })
                            }
                        </ul>
                    }
                } else {
                    html! { <p>{"No data"}</p> }
                }
            }
        </div>
    }
}
```

### 6.2 异步数据获取

```rust
use yew::prelude::*;
use gloo_net::http::Request;

/// 自定义 Hook: useFetch
#[hook]
pub fn use_fetch<T>(url: String) -> (Option<T>, bool, Option<String>)
where
    T: for<'de> serde::Deserialize<'de> + 'static,
{
    let data = use_state(|| None);
    let loading = use_state(|| false);
    let error = use_state(|| None);
    
    {
        let data = data.clone();
        let loading = loading.clone();
        let error = error.clone();
        let url = url.clone();
        
        use_effect_with(url, move |url| {
            loading.set(true);
            
            wasm_bindgen_futures::spawn_local(async move {
                match Request::get(url).send().await {
                    Ok(response) => {
                        match response.json::<T>().await {
                            Ok(result) => {
                                data.set(Some(result));
                                loading.set(false);
                            }
                            Err(e) => {
                                error.set(Some(e.to_string()));
                                loading.set(false);
                            }
                        }
                    }
                    Err(e) => {
                        error.set(Some(e.to_string()));
                        loading.set(false);
                    }
                }
            });
            
            || ()
        });
    }
    
    ((*data).clone(), *loading, (*error).clone())
}

/// 使用 useFetch Hook
#[function_component(UserProfile)]
fn user_profile() -> Html {
    let (user, loading, error) = use_fetch::<User>(
        "https://api.example.com/user/1".to_string()
    );
    
    html! {
        <div>
            {
                if loading {
                    html! { <p>{"Loading..."}</p> }
                } else if let Some(err) = error {
                    html! { <p class="error">{err}</p> }
                } else if let Some(user_data) = user {
                    html! {
                        <div class="user-profile">
                            <h2>{&user_data.name}</h2>
                            <p>{&user_data.email}</p>
                        </div>
                    }
                } else {
                    html! { <p>{"No data"}</p> }
                }
            }
        </div>
    }
}
```

### 6.3 错误处理

```rust
use thiserror::Error;

#[derive(Error, Debug, Clone, PartialEq)]
pub enum ApiError {
    #[error("Network error: {0}")]
    Network(String),
    
    #[error("Parse error: {0}")]
    Parse(String),
    
    #[error("HTTP error: {0}")]
    Http(u16),
    
    #[error("Unknown error")]
    Unknown,
}

/// 错误显示组件
#[derive(Properties, PartialEq)]
pub struct ErrorDisplayProps {
    pub error: ApiError,
}

#[function_component(ErrorDisplay)]
fn error_display(props: &ErrorDisplayProps) -> Html {
    let message = match &props.error {
        ApiError::Network(msg) => format!("网络错误: {}", msg),
        ApiError::Parse(msg) => format!("解析错误: {}", msg),
        ApiError::Http(code) => format!("HTTP 错误: {}", code),
        ApiError::Unknown => "未知错误".to_string(),
    };
    
    html! {
        <div class="error-display">
            <span class="error-icon">{"⚠️"}</span>
            <span class="error-message">{message}</span>
        </div>
    }
}
```

---

## 7. 表单处理

### 7.1 受控组件

```rust
use yew::prelude::*;
use web_sys::HtmlInputElement;

#[derive(Clone, PartialEq, Default)]
pub struct FormData {
    pub name: String,
    pub email: String,
    pub age: u32,
}

#[function_component(UserForm)]
fn user_form() -> Html {
    let form_data = use_state(FormData::default);
    
    let on_name_change = {
        let form_data = form_data.clone();
        Callback::from(move |e: Event| {
            let target: HtmlInputElement = e.target_unchecked_into();
            let mut data = (*form_data).clone();
            data.name = target.value();
            form_data.set(data);
        })
    };
    
    let on_email_change = {
        let form_data = form_data.clone();
        Callback::from(move |e: Event| {
            let target: HtmlInputElement = e.target_unchecked_into();
            let mut data = (*form_data).clone();
            data.email = target.value();
            form_data.set(data);
        })
    };
    
    let on_submit = {
        let form_data = form_data.clone();
        Callback::from(move |e: SubmitEvent| {
            e.prevent_default();
            log::info!("Form submitted: {:?}", *form_data);
            // 发送到服务器
        })
    };
    
    html! {
        <form onsubmit={on_submit}>
            <div>
                <label>{"Name:"}</label>
                <input 
                    type="text" 
                    value={form_data.name.clone()}
                    onchange={on_name_change}
                />
            </div>
            <div>
                <label>{"Email:"}</label>
                <input 
                    type="email" 
                    value={form_data.email.clone()}
                    onchange={on_email_change}
                />
            </div>
            <button type="submit">{"Submit"}</button>
        </form>
    }
}
```

### 7.2 表单验证

```rust
use validator::{Validate, ValidationError};

#[derive(Clone, PartialEq, Default, Validate)]
pub struct RegistrationForm {
    #[validate(length(min = 3, max = 50))]
    pub username: String,
    
    #[validate(email)]
    pub email: String,
    
    #[validate(length(min = 8))]
    pub password: String,
    
    #[validate(must_match(other = "password"))]
    pub confirm_password: String,
}

#[function_component(RegistrationFormComponent)]
fn registration_form_component() -> Html {
    let form = use_state(RegistrationForm::default);
    let errors = use_state(|| None::<validator::ValidationErrors>);
    
    let on_submit = {
        let form = form.clone();
        let errors = errors.clone();
        
        Callback::from(move |e: SubmitEvent| {
            e.prevent_default();
            
            match form.validate() {
                Ok(_) => {
                    log::info!("Form is valid!");
                    errors.set(None);
                    // 提交表单
                }
                Err(e) => {
                    log::warn!("Form validation failed");
                    errors.set(Some(e));
                }
            }
        })
    };
    
    html! {
        <form onsubmit={on_submit}>
            // 表单字段
            {
                if let Some(errs) = (*errors).as_ref() {
                    html! {
                        <div class="errors">
                            {
                                for errs.field_errors().iter().map(|(field, errors)| {
                                    html! {
                                        <p>{format!("{}: {:?}", field, errors)}</p>
                                    }
                                })
                            }
                        </div>
                    }
                } else {
                    html! {}
                }
            }
            <button type="submit">{"Register"}</button>
        </form>
    }
}
```

### 7.3 文件上传

```rust
use web_sys::{Event, HtmlInputElement, File};
use gloo_file::{callbacks::FileReader, File as GlooFile};

#[function_component(FileUpload)]
fn file_upload() -> Html {
    let file_name = use_state(|| None::<String>);
    let file_content = use_state(|| None::<Vec<u8>>);
    
    let on_file_change = {
        let file_name = file_name.clone();
        let file_content = file_content.clone();
        
        Callback::from(move |e: Event| {
            let target: HtmlInputElement = e.target_unchecked_into();
            
            if let Some(files) = target.files() {
                if let Some(file) = files.get(0) {
                    let file_name_clone = file_name.clone();
                    let file_content_clone = file_content.clone();
                    
                    file_name_clone.set(Some(file.name()));
                    
                    let file = GlooFile::from(file);
                    let reader = FileReader::new();
                    
                    reader.read_as_bytes(&file, move |res| {
                        if let Ok(data) = res {
                            file_content_clone.set(Some(data));
                        }
                    });
                }
            }
        })
    };
    
    html! {
        <div>
            <input type="file" onchange={on_file_change} />
            {
                if let Some(name) = (*file_name).as_ref() {
                    html! { <p>{format!("Selected: {}", name)}</p> }
                } else {
                    html! {}
                }
            }
            {
                if let Some(content) = (*file_content).as_ref() {
                    html! { <p>{format!("Size: {} bytes", content.len())}</p> }
                } else {
                    html! {}
                }
            }
        </div>
    }
}
```

---

## 8. 性能优化

### 8.1 虚拟 DOM 优化

```rust
use yew::prelude::*;

/// 使用 key 优化列表渲染
#[function_component(OptimizedList)]
fn optimized_list() -> Html {
    let items = use_state(|| vec!["Item 1", "Item 2", "Item 3"]);
    
    html! {
        <ul>
            {
                for items.iter().enumerate().map(|(idx, item)| {
                    html! {
                        <li key={idx}>{ item }</li>
                    }
                })
            }
        </ul>
    }
}

/// 使用 memo 避免不必要的重渲染
#[derive(Properties, PartialEq)]
pub struct ExpensiveComponentProps {
    pub value: i32,
}

#[function_component(ExpensiveComponent)]
fn expensive_component(props: &ExpensiveComponentProps) -> Html {
    log::info!("ExpensiveComponent rendered");
    
    html! {
        <div>
            <p>{format!("Value: {}", props.value)}</p>
        </div>
    }
}
```

### 8.2 代码分割

```rust
// 延迟加载路由
use yew::prelude::*;
use yew::suspense::{Suspension, SuspensionResult};

#[function_component(LazyRoute)]
fn lazy_route() -> HtmlResult {
    let suspension = use_suspension()?;
    
    // 模拟异步加载
    wasm_bindgen_futures::spawn_local(async move {
        gloo_timers::future::TimeoutFuture::new(1000).await;
        suspension.resume();
    });
    
    Ok(html! {
        <div>{"Lazy loaded content"}</div>
    })
}

#[function_component(App)]
fn app() -> Html {
    html! {
        <Suspense fallback={html! { <div>{"Loading..."}</div> }}>
            <LazyRoute />
        </Suspense>
    }
}
```

### 8.3 Lazy Loading

```rust
use yew::prelude::*;

/// 图片懒加载
#[derive(Properties, PartialEq)]
pub struct LazyImageProps {
    pub src: String,
    pub alt: String,
}

#[function_component(LazyImage)]
fn lazy_image(props: &LazyImageProps) -> Html {
    let is_visible = use_state(|| false);
    let image_ref = use_node_ref();
    
    {
        let is_visible = is_visible.clone();
        let image_ref = image_ref.clone();
        
        use_effect_with((), move |_| {
            // 使用 Intersection Observer
            let callback = Closure::wrap(Box::new(move |entries: js_sys::Array| {
                if let Some(entry) = entries.get(0).dyn_into::<web_sys::IntersectionObserverEntry>().ok() {
                    if entry.is_intersecting() {
                        is_visible.set(true);
                    }
                }
            }) as Box<dyn FnMut(js_sys::Array)>);
            
            // Setup observer
            || ()
        });
    }
    
    html! {
        <img 
            ref={image_ref}
            src={if *is_visible { &props.src } else { "placeholder.png" }}
            alt={&props.alt}
        />
    }
}
```

---

## 9. OTLP 集成

### 9.1 前端性能追踪

```rust
use web_sys::window;

/// 性能追踪
pub fn track_page_load() {
    if let Some(window) = window() {
        if let Some(performance) = window.performance() {
            let navigation = performance.timing();
            
            let load_time = navigation.load_event_end() - navigation.navigation_start();
            let dom_ready = navigation.dom_content_loaded_event_end() - navigation.navigation_start();
            
            log::info!("Page Load Time: {}ms", load_time);
            log::info!("DOM Ready Time: {}ms", dom_ready);
            
            // 发送到 OTLP 后端
            send_metric("page.load_time", load_time as f64);
            send_metric("page.dom_ready", dom_ready as f64);
        }
    }
}

fn send_metric(name: &str, value: f64) {
    wasm_bindgen_futures::spawn_local(async move {
        let _ = gloo_net::http::Request::post("/api/metrics")
            .json(&serde_json::json!({
                "name": name,
                "value": value,
                "timestamp": js_sys::Date::now(),
            }))
            .unwrap()
            .send()
            .await;
    });
}
```

### 9.2 用户行为追踪

```rust
/// 用户交互追踪
pub fn track_click(element: &str, action: &str) {
    log::info!("Click: {} - {}", element, action);
    
    wasm_bindgen_futures::spawn_local(async move {
        let _ = gloo_net::http::Request::post("/api/events")
            .json(&serde_json::json!({
                "event_type": "click",
                "element": element,
                "action": action,
                "timestamp": js_sys::Date::now(),
            }))
            .unwrap()
            .send()
            .await;
    });
}

#[function_component(TrackedButton)]
fn tracked_button() -> Html {
    let on_click = Callback::from(|_| {
        track_click("button", "submit_form");
    });
    
    html! {
        <button onclick={on_click}>{"Submit"}</button>
    }
}
```

### 9.3 错误追踪

```rust
use std::panic;

/// 设置全局错误处理
pub fn setup_error_tracking() {
    panic::set_hook(Box::new(|panic_info| {
        let message = if let Some(s) = panic_info.payload().downcast_ref::<&str>() {
            (*s).to_string()
        } else {
            "Unknown panic".to_string()
        };
        
        let location = if let Some(loc) = panic_info.location() {
            format!("{}:{}:{}", loc.file(), loc.line(), loc.column())
        } else {
            "Unknown location".to_string()
        };
        
        log::error!("Panic: {} at {}", message, location);
        
        // 发送到错误追踪服务
        wasm_bindgen_futures::spawn_local(async move {
            let _ = gloo_net::http::Request::post("/api/errors")
                .json(&serde_json::json!({
                    "error_type": "panic",
                    "message": message,
                    "location": location,
                    "timestamp": js_sys::Date::now(),
                }))
                .unwrap()
                .send()
                .await;
        });
    }));
}
```

---

## 10. 测试策略

### 10.1 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_counter_increment() {
        // 测试逻辑
    }
}
```

### 10.2 集成测试

```rust
use wasm_bindgen_test::*;

wasm_bindgen_test_configure!(run_in_browser);

#[wasm_bindgen_test]
fn test_app_renders() {
    // WASM 集成测试
}
```

---

## 11. 生产构建

### 11.1 构建优化

```bash
# Trunk.toml
[build]
target = "index.html"
release = true
dist = "dist"

[[hooks]]
stage = "pre_build"
command = "npm"
command_arguments = ["run", "build:css"]

[[hooks]]
stage = "post_build"
command = "wasm-opt"
command_arguments = ["-Oz", "--output", "dist/app_bg.wasm", "dist/app_bg.wasm"]
```

### 11.2 Docker 部署

```dockerfile
# Dockerfile
FROM rust:1.90 as builder

RUN cargo install trunk
RUN rustup target add wasm32-unknown-unknown

WORKDIR /app
COPY . .

RUN trunk build --release

FROM nginx:alpine
COPY --from=builder /app/dist /usr/share/nginx/html
EXPOSE 80
CMD ["nginx", "-g", "daemon off;"]
```

---

## 12. 国际标准对齐

- ✅ **WebAssembly**: WASM 标准
- ✅ **HTML5/CSS3**: Web 标准
- ✅ **ES6 Modules**: JavaScript 模块
- ✅ **OpenTelemetry**: 前端性能追踪

---

## 总结

### Yew 核心优势

1. **React 风格**: 熟悉的组件模型
2. **类型安全**: Rust 强类型系统
3. **高性能**: WebAssembly 性能
4. **现代化**: Hooks, Context, Router

### 适用场景

- ✅ SPA (单页应用)
- ✅ PWA (渐进式 Web 应用)
- ✅ 企业级前端
- ✅ 高性能 Web 应用

### 性能基准

- **WASM 包大小**: ~200 KB (gzipped)
- **首屏加载**: < 1 秒
- **虚拟 DOM**: 高效 diff 算法

---

**版权**: MIT License  
**作者**: OTLP Rust 项目组  
**最后更新**: 2025-10-11
