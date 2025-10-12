# Tauri 完整实现：原生桌面应用框架（Rust 1.90 + OTLP 集成）

## 目录

- [Tauri 完整实现：原生桌面应用框架（Rust 1.90 + OTLP 集成）](#tauri-完整实现原生桌面应用框架rust-190--otlp-集成)
  - [目录](#目录)
  - [1. Tauri 概述](#1-tauri-概述)
    - [1.1 核心特性](#11-核心特性)
    - [1.2 与 Electron 对比](#12-与-electron-对比)
    - [1.3 技术架构](#13-技术架构)
  - [2. 国际标准对齐](#2-国际标准对齐)
    - [2.1 Web 标准](#21-web-标准)
    - [2.2 桌面端标准](#22-桌面端标准)
    - [2.3 安全标准](#23-安全标准)
  - [3. 项目初始化](#3-项目初始化)
    - [3.1 环境准备](#31-环境准备)
    - [3.2 创建项目](#32-创建项目)
    - [3.3 项目结构](#33-项目结构)
  - [4. 核心概念](#4-核心概念)
    - [4.1 Frontend + Backend 架构](#41-frontend--backend-架构)
    - [4.2 Command 系统](#42-command-系统)
    - [4.3 Event 系统](#43-event-系统)
    - [4.4 Plugin 系统](#44-plugin-系统)
  - [5. 窗口管理](#5-窗口管理)
    - [5.1 窗口创建与配置](#51-窗口创建与配置)
    - [5.2 多窗口管理](#52-多窗口管理)
    - [5.3 自定义标题栏](#53-自定义标题栏)
  - [6. 文件系统](#6-文件系统)
    - [6.1 安全的文件访问](#61-安全的文件访问)
    - [6.2 文件对话框](#62-文件对话框)
    - [6.3 拖放文件](#63-拖放文件)
  - [7. 系统集成](#7-系统集成)
    - [7.1 系统托盘](#71-系统托盘)
    - [7.2 原生菜单](#72-原生菜单)
    - [7.3 通知](#73-通知)
    - [7.4 剪贴板](#74-剪贴板)
    - [7.5 全局快捷键](#75-全局快捷键)
  - [8. 数据存储](#8-数据存储)
    - [8.1 嵌入式数据库](#81-嵌入式数据库)
    - [8.2 应用配置](#82-应用配置)
    - [8.3 安全存储](#83-安全存储)
  - [9. 自动更新](#9-自动更新)
    - [9.1 Updater 配置](#91-updater-配置)
    - [9.2 更新流程](#92-更新流程)
    - [9.3 版本管理](#93-版本管理)
  - [10. OTLP 集成](#10-otlp-集成)
    - [10.1 后端遥测](#101-后端遥测)
    - [10.2 前端性能追踪](#102-前端性能追踪)
    - [10.3 崩溃报告](#103-崩溃报告)
  - [11. 安全最佳实践](#11-安全最佳实践)
    - [11.1 CSP 配置](#111-csp-配置)
    - [11.2 IPC 安全](#112-ipc-安全)
    - [11.3 代码签名](#113-代码签名)
  - [12. 生产部署](#12-生产部署)
    - [12.1 跨平台构建](#121-跨平台构建)
    - [12.2 应用打包](#122-应用打包)
    - [12.3 发布流程](#123-发布流程)
  - [总结](#总结)
    - [核心优势](#核心优势)
    - [国际标准对齐](#国际标准对齐)
    - [适用场景](#适用场景)

---

## 1. Tauri 概述

**Tauri** 是一个用 Rust 构建的轻量级、安全的桌面应用框架，使用系统原生 WebView 渲染前端界面，后端由 Rust 驱动。

### 1.1 核心特性

| 特性 | 说明 | 优势 |
|------|------|------|
| **轻量级** | 使用系统 WebView (Windows: WebView2, macOS: WKWebView, Linux: WebKitGTK) | 应用体积小（~3-5MB），无需打包 Chromium |
| **安全性** | Rust 内存安全 + 细粒度权限控制 | 防止内存漏洞，沙箱隔离 |
| **性能** | 零成本抽象，原生速度 | 启动快，内存占用低 |
| **跨平台** | Windows, macOS, Linux, iOS, Android | 单一代码库 |
| **灵活前端** | 支持任意前端框架 (React, Vue, Svelte, Leptos) | 技术栈自由 |
| **原生能力** | 文件系统、系统托盘、通知、全局快捷键 | 完整的桌面应用体验 |

### 1.2 与 Electron 对比

| 维度 | Tauri | Electron |
|------|-------|----------|
| **应用体积** | 3-5 MB | 50-100 MB |
| **内存占用** | ~20-40 MB | ~100-200 MB |
| **后端语言** | Rust | Node.js |
| **安全性** | 内存安全 + 权限系统 | 依赖 Node.js 生态 |
| **启动速度** | 快 (~500ms) | 较慢 (~1-2s) |
| **WebView** | 系统原生 | Chromium (打包) |
| **生态成熟度** | 新兴 (2019+) | 成熟 (2013+) |

### 1.3 技术架构

```text
┌────────────────────────────────────────────┐
│           Frontend (WebView)               │
│  ┌──────────────────────────────────────┐  │
│  │   HTML + CSS + JavaScript            │  │
│  │   (React/Vue/Svelte/Leptos/etc.)     │  │
│  └────────────┬─────────────────────────┘  │
│               │ IPC (invoke/emit)          │
└───────────────┼────────────────────────────┘
                │
┌───────────────▼─────────────────────────────┐
│           Rust Backend (Core)               │
│  ┌──────────────────────────────────────┐   │
│  │   Tauri Commands (Async Functions)   │   │
│  │   - File System                      │   │
│  │   - Database                         │   │
│  │   - HTTP Requests                    │   │
│  │   - System APIs                      │   │
│  └──────────────────────────────────────┘   │
│                                             │
│  ┌──────────────────────────────────────┐   │
│  │   Tauri Plugins                      │   │
│  │   - Window, Dialog, Notification     │   │
│  │   - Updater, Store, HTTP             │   │
│  └──────────────────────────────────────┘   │
└─────────────────────────────────────────────┘
                │
┌───────────────▼─────────────────────────────┐
│         Operating System                    │
│   (Windows, macOS, Linux, iOS, Android)     │
└─────────────────────────────────────────────┘
```

---

## 2. 国际标准对齐

### 2.1 Web 标准

| 标准 | 版本 | 说明 |
|------|------|------|
| **HTML5** | 5.3 | 前端渲染 |
| **CSS3** | CSS3 | 样式支持 |
| **ECMAScript** | ES2022+ | JavaScript 支持 |
| **WebAssembly** | WASM 1.0 | Rust 前端库可编译为 WASM |
| **Web Workers** | W3C | 后台线程支持 |

### 2.2 桌面端标准

| 平台 | WebView | 版本 |
|------|---------|------|
| **Windows** | WebView2 | Edge Chromium |
| **macOS** | WKWebView | Safari WebKit |
| **Linux** | WebKitGTK | WebKit 2.0 |

### 2.3 安全标准

| 标准 | 说明 |
|------|------|
| **CSP (Content Security Policy)** | W3C 标准，防止 XSS 攻击 |
| **IPC 权限控制** | 细粒度 API 访问控制 |
| **代码签名** | Apple Notarization, Windows Authenticode |

---

## 3. 项目初始化

### 3.1 环境准备

**系统依赖**：

```bash
# Windows
# - Microsoft Edge WebView2 Runtime (通常已预装)
# - Visual Studio Build Tools

# macOS
# - Xcode Command Line Tools
xcode-select --install

# Linux (Ubuntu/Debian)
sudo apt update
sudo apt install libwebkit2gtk-4.1-dev \
    build-essential \
    curl \
    wget \
    file \
    libssl-dev \
    libayatana-appindicator3-dev \
    librsvg2-dev
```

**Rust 工具链**：

```bash
# 安装 Rust 1.90+
rustup update

# 安装 Tauri CLI
cargo install tauri-cli --version "^2.0"
```

### 3.2 创建项目

```bash
# 使用 create-tauri-app (推荐)
cargo install create-tauri-app
cargo create-tauri-app

# 或手动创建
cargo tauri init

# 项目选项
# - App name: my-tauri-app
# - Window title: My Tauri App
# - Frontend: Vanilla / React / Vue / Svelte / etc.
# - Dev server: http://localhost:5173 (Vite)
```

### 3.3 项目结构

```text
my-tauri-app/
├── src-tauri/                    # Rust 后端
│   ├── Cargo.toml                # Rust 依赖
│   ├── tauri.conf.json           # Tauri 配置
│   ├── build.rs                  # 构建脚本
│   ├── icons/                    # 应用图标
│   │   ├── icon.icns             # macOS
│   │   ├── icon.ico              # Windows
│   │   └── icon.png              # Linux
│   └── src/
│       ├── main.rs               # Rust 入口
│       ├── commands.rs           # Tauri Commands
│       └── lib.rs                # 库模块
├── src/                          # 前端代码
│   ├── main.tsx                  # 前端入口 (React 示例)
│   ├── App.tsx
│   └── ...
├── package.json                  # 前端依赖 (npm)
├── vite.config.ts                # Vite 配置
└── README.md
```

**src-tauri/Cargo.toml**:

```toml
[package]
name = "my-tauri-app"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[build-dependencies]
tauri-build = { version = "2.0", features = [] }

[dependencies]
# Tauri 核心
tauri = { version = "2.0", features = ["devtools"] }
tauri-plugin-shell = "2.0"

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 异步运行时
tokio = { version = "1", features = ["full"] }

# 日志
tracing = "0.1"
tracing-subscriber = "0.3"

# OpenTelemetry (可选)
opentelemetry = { version = "0.25", optional = true }
opentelemetry-otlp = { version = "0.25", optional = true }
tracing-opentelemetry = { version = "0.26", optional = true }

# 数据库 (可选)
sqlx = { version = "0.8", features = ["sqlite", "runtime-tokio"], optional = true }

[features]
default = ["custom-protocol"]
custom-protocol = ["tauri/custom-protocol"]
telemetry = ["opentelemetry", "opentelemetry-otlp", "tracing-opentelemetry"]
database = ["sqlx"]
```

**src-tauri/tauri.conf.json**:

```json
{
  "$schema": "https://schema.tauri.app/config/2.0",
  "productName": "My Tauri App",
  "version": "0.1.0",
  "identifier": "com.example.myapp",
  "build": {
    "beforeDevCommand": "npm run dev",
    "beforeBuildCommand": "npm run build",
    "devUrl": "http://localhost:5173",
    "frontendDist": "../dist"
  },
  "app": {
    "windows": [
      {
        "title": "My Tauri App",
        "width": 1200,
        "height": 800,
        "resizable": true,
        "fullscreen": false,
        "decorations": true,
        "transparent": false,
        "alwaysOnTop": false
      }
    ],
    "security": {
      "csp": "default-src 'self'; script-src 'self' 'unsafe-inline'; style-src 'self' 'unsafe-inline';"
    }
  },
  "bundle": {
    "active": true,
    "targets": "all",
    "icon": [
      "icons/32x32.png",
      "icons/128x128.png",
      "icons/icon.icns",
      "icons/icon.ico"
    ]
  }
}
```

---

## 4. 核心概念

### 4.1 Frontend + Backend 架构

**前端 (TypeScript/JavaScript)**:

```typescript
// src/App.tsx
import { invoke } from '@tauri-apps/api/core';
import { useState } from 'react';

function App() {
  const [message, setMessage] = useState('');
  
  async function greet(name: string) {
    // 调用 Rust 后端 Command
    const result = await invoke<string>('greet', { name });
    setMessage(result);
  }
  
  return (
    <div>
      <button onClick={() => greet('World')}>
        Greet
      </button>
      <p>{message}</p>
    </div>
  );
}

export default App;
```

**后端 (Rust)**:

```rust
// src-tauri/src/main.rs
#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")]

use tauri::Manager;

#[tauri::command]
fn greet(name: &str) -> String {
    format!("Hello, {}! You've been greeted from Rust!", name)
}

fn main() {
    tauri::Builder::default()
        .setup(|app| {
            tracing_subscriber::fmt::init();
            tracing::info!("Application started");
            Ok(())
        })
        .invoke_handler(tauri::generate_handler![greet])
        .run(tauri::generate_context!())
        .expect("error while running tauri application");
}
```

### 4.2 Command 系统

**异步 Command**：

```rust
// src-tauri/src/commands.rs
use serde::{Deserialize, Serialize};
use tauri::State;

#[derive(Debug, Serialize, Deserialize)]
pub struct User {
    pub id: u64,
    pub name: String,
    pub email: String,
}

/// 获取用户信息 (异步)
#[tauri::command]
pub async fn get_user(user_id: u64) -> Result<User, String> {
    tracing::info!(user_id = %user_id, "Fetching user");
    
    // 模拟数据库查询
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    
    Ok(User {
        id: user_id,
        name: "John Doe".to_string(),
        email: "john@example.com".to_string(),
    })
}

/// 保存用户信息
#[tauri::command]
pub async fn save_user(user: User) -> Result<(), String> {
    tracing::info!(user = ?user, "Saving user");
    
    // 数据库操作
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    
    Ok(())
}

/// 使用状态管理
pub struct AppState {
    pub database_url: String,
}

#[tauri::command]
pub async fn get_database_url(state: State<'_, AppState>) -> Result<String, String> {
    Ok(state.database_url.clone())
}
```

**注册 Commands**：

```rust
// src-tauri/src/main.rs
mod commands;

fn main() {
    tauri::Builder::default()
        .manage(commands::AppState {
            database_url: "sqlite://app.db".to_string(),
        })
        .invoke_handler(tauri::generate_handler![
            commands::greet,
            commands::get_user,
            commands::save_user,
            commands::get_database_url,
        ])
        .run(tauri::generate_context!())
        .expect("error while running tauri application");
}
```

**前端调用**：

```typescript
// src/api/user.ts
import { invoke } from '@tauri-apps/api/core';

export interface User {
  id: number;
  name: string;
  email: string;
}

export async function getUser(userId: number): Promise<User> {
  return await invoke<User>('get_user', { userId });
}

export async function saveUser(user: User): Promise<void> {
  await invoke('save_user', { user });
}
```

### 4.3 Event 系统

**后端发送事件**：

```rust
use tauri::{AppHandle, Emitter};

#[tauri::command]
pub async fn start_download(app: AppHandle, url: String) -> Result<(), String> {
    // 发送下载开始事件
    app.emit("download-started", &url).map_err(|e| e.to_string())?;
    
    // 模拟下载进度
    for progress in 0..=100 {
        tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
        
        app.emit("download-progress", progress)
            .map_err(|e| e.to_string())?;
    }
    
    // 发送完成事件
    app.emit("download-finished", &url).map_err(|e| e.to_string())?;
    
    Ok(())
}
```

**前端监听事件**：

```typescript
import { listen } from '@tauri-apps/api/event';

// 监听下载进度
const unlisten = await listen<number>('download-progress', (event) => {
  console.log(`Download progress: ${event.payload}%`);
  setProgress(event.payload);
});

// 清理监听器
unlisten();
```

**前端向后端发送事件**：

```typescript
import { emit } from '@tauri-apps/api/event';

await emit('user-action', { action: 'click', target: 'button' });
```

```rust
use tauri::Listener;

fn main() {
    tauri::Builder::default()
        .setup(|app| {
            app.listen("user-action", |event| {
                if let Some(payload) = event.payload() {
                    tracing::info!("User action: {}", payload);
                }
            });
            Ok(())
        })
        .run(tauri::generate_context!())
        .expect("error while running tauri application");
}
```

### 4.4 Plugin 系统

**使用官方插件**：

```toml
# Cargo.toml
[dependencies]
tauri-plugin-dialog = "2.0"
tauri-plugin-fs = "2.0"
tauri-plugin-http = "2.0"
tauri-plugin-notification = "2.0"
tauri-plugin-store = "2.0"
tauri-plugin-updater = "2.0"
```

```rust
fn main() {
    tauri::Builder::default()
        .plugin(tauri_plugin_dialog::init())
        .plugin(tauri_plugin_fs::init())
        .plugin(tauri_plugin_http::init())
        .plugin(tauri_plugin_notification::init())
        .plugin(tauri_plugin_store::Builder::default().build())
        .plugin(tauri_plugin_updater::Builder::new().build())
        .run(tauri::generate_context!())
        .expect("error while running tauri application");
}
```

---

## 5. 窗口管理

### 5.1 窗口创建与配置

```rust
use tauri::{Manager, WindowBuilder, WindowUrl};

#[tauri::command]
pub fn create_settings_window(app: AppHandle) -> Result<(), String> {
    let window = WindowBuilder::new(
        &app,
        "settings",
        WindowUrl::App("settings.html".into())
    )
    .title("Settings")
    .inner_size(800.0, 600.0)
    .center()
    .resizable(false)
    .build()
    .map_err(|e| e.to_string())?;
    
    tracing::info!("Settings window created");
    Ok(())
}
```

### 5.2 多窗口管理

**前端**：

```typescript
import { WebviewWindow } from '@tauri-apps/api/webviewWindow';

// 创建新窗口
const settingsWindow = new WebviewWindow('settings', {
  url: '/settings',
  title: 'Settings',
  width: 800,
  height: 600,
  center: true,
  resizable: false,
});

// 监听窗口事件
settingsWindow.once('tauri://created', () => {
  console.log('Settings window created');
});

settingsWindow.once('tauri://error', (error) => {
  console.error('Failed to create settings window:', error);
});

// 获取当前窗口
import { getCurrentWindow } from '@tauri-apps/api/window';
const currentWindow = getCurrentWindow();

// 窗口操作
await currentWindow.setTitle('New Title');
await currentWindow.setSize(new PhysicalSize(1024, 768));
await currentWindow.center();
await currentWindow.hide();
await currentWindow.show();
await currentWindow.close();
```

### 5.3 自定义标题栏

**tauri.conf.json**:

```json
{
  "app": {
    "windows": [
      {
        "decorations": false,
        "transparent": true
      }
    ]
  }
}
```

**前端 CSS**:

```css
/* src/styles/titlebar.css */
.titlebar {
  height: 30px;
  background: #1e1e1e;
  user-select: none;
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 0 10px;
}

.titlebar-drag {
  position: absolute;
  top: 0;
  left: 0;
  width: 100%;
  height: 30px;
  -webkit-app-region: drag;
}

.titlebar-buttons {
  display: flex;
  gap: 10px;
  -webkit-app-region: no-drag;
}
```

**前端组件**:

```typescript
import { getCurrentWindow } from '@tauri-apps/api/window';

function CustomTitleBar() {
  const window = getCurrentWindow();
  
  return (
    <div className="titlebar">
      <div className="titlebar-drag"></div>
      <div className="titlebar-title">My Tauri App</div>
      <div className="titlebar-buttons">
        <button onClick={() => window.minimize()}>−</button>
        <button onClick={() => window.toggleMaximize()}>□</button>
        <button onClick={() => window.close()}>×</button>
      </div>
    </div>
  );
}
```

---

## 6. 文件系统

### 6.1 安全的文件访问

**tauri.conf.json** (权限配置):

```json
{
  "plugins": {
    "fs": {
      "scope": [
        "$APPDATA/*",
        "$DOCUMENT/*"
      ]
    }
  }
}
```

**前端读写文件**:

```typescript
import { readTextFile, writeTextFile, BaseDirectory } from '@tauri-apps/plugin-fs';

// 读取文件
const content = await readTextFile('config.json', {
  baseDir: BaseDirectory.AppData
});

// 写入文件
await writeTextFile('config.json', JSON.stringify(config), {
  baseDir: BaseDirectory.AppData
});

// 追加内容
await writeTextFile('log.txt', `${new Date().toISOString()}: Log entry\n`, {
  baseDir: BaseDirectory.AppData,
  append: true
});
```

### 6.2 文件对话框

```typescript
import { open, save } from '@tauri-apps/plugin-dialog';

// 打开文件选择对话框
const selectedFile = await open({
  multiple: false,
  filters: [
    { name: 'JSON', extensions: ['json'] },
    { name: 'All Files', extensions: ['*'] }
  ]
});

if (selectedFile) {
  console.log('Selected file:', selectedFile);
}

// 保存文件对话框
const savePath = await save({
  defaultPath: 'export.json',
  filters: [
    { name: 'JSON', extensions: ['json'] }
  ]
});

if (savePath) {
  await writeTextFile(savePath, JSON.stringify(data));
}
```

### 6.3 拖放文件

```typescript
import { listen } from '@tauri-apps/api/event';

// 监听文件拖放
const unlisten = await listen<string[]>('tauri://file-drop', (event) => {
  console.log('Files dropped:', event.payload);
  event.payload.forEach(async (filePath) => {
    const content = await readTextFile(filePath);
    console.log('File content:', content);
  });
});
```

**前端 HTML**:

```html
<div
  id="drop-zone"
  ondragover="event.preventDefault()"
  ondrop="handleDrop(event)"
>
  Drop files here
</div>
```

---

## 7. 系统集成

### 7.1 系统托盘

```rust
use tauri::{
    menu::{Menu, MenuItem},
    tray::{TrayIconBuilder, TrayIconEvent},
    Manager,
};

fn main() {
    tauri::Builder::default()
        .setup(|app| {
            // 创建托盘菜单
            let quit = MenuItem::with_id(app, "quit", "Quit", true, None::<&str>)?;
            let show = MenuItem::with_id(app, "show", "Show", true, None::<&str>)?;
            let menu = Menu::with_items(app, &[&show, &quit])?;
            
            // 创建系统托盘
            let _tray = TrayIconBuilder::new()
                .menu(&menu)
                .icon(app.default_window_icon().unwrap().clone())
                .on_menu_event(|app, event| match event.id().as_ref() {
                    "quit" => {
                        app.exit(0);
                    }
                    "show" => {
                        if let Some(window) = app.get_webview_window("main") {
                            window.show().unwrap();
                            window.set_focus().unwrap();
                        }
                    }
                    _ => {}
                })
                .build(app)?;
            
            Ok(())
        })
        .run(tauri::generate_context!())
        .expect("error while running tauri application");
}
```

### 7.2 原生菜单

```rust
use tauri::menu::{Menu, MenuBuilder, MenuItem, Submenu, SubmenuBuilder};

fn main() {
    tauri::Builder::default()
        .setup(|app| {
            // File 菜单
            let new_file = MenuItem::with_id(app, "new", "New", true, Some("Ctrl+N"))?;
            let open_file = MenuItem::with_id(app, "open", "Open", true, Some("Ctrl+O"))?;
            let file_menu = SubmenuBuilder::new(app, "File")
                .items(&[&new_file, &open_file])
                .build()?;
            
            // Edit 菜单
            let copy = MenuItem::with_id(app, "copy", "Copy", true, Some("Ctrl+C"))?;
            let paste = MenuItem::with_id(app, "paste", "Paste", true, Some("Ctrl+V"))?;
            let edit_menu = SubmenuBuilder::new(app, "Edit")
                .items(&[&copy, &paste])
                .build()?;
            
            // 主菜单
            let menu = MenuBuilder::new(app)
                .items(&[&file_menu, &edit_menu])
                .build()?;
            
            app.set_menu(menu)?;
            
            // 菜单事件处理
            app.on_menu_event(|app, event| {
                match event.id().as_ref() {
                    "new" => {
                        tracing::info!("New file clicked");
                    }
                    "open" => {
                        tracing::info!("Open file clicked");
                    }
                    _ => {}
                }
            });
            
            Ok(())
        })
        .run(tauri::generate_context!())
        .expect("error while running tauri application");
}
```

### 7.3 通知

```typescript
import { sendNotification } from '@tauri-apps/plugin-notification';

await sendNotification({
  title: 'Download Complete',
  body: 'Your file has been downloaded successfully.',
  icon: 'icon.png',
});
```

### 7.4 剪贴板

```typescript
import { writeText, readText } from '@tauri-apps/plugin-clipboard-manager';

// 写入剪贴板
await writeText('Hello from Tauri!');

// 读取剪贴板
const clipboardContent = await readText();
console.log('Clipboard:', clipboardContent);
```

### 7.5 全局快捷键

```rust
use tauri::Manager;
use tauri_plugin_global_shortcut::{GlobalShortcutExt, Shortcut};

fn main() {
    tauri::Builder::default()
        .setup(|app| {
            // 注册全局快捷键
            let shortcut = Shortcut::new("Ctrl+Shift+A")?;
            app.global_shortcut().on_shortcut(shortcut, |app, _event| {
                tracing::info!("Global shortcut triggered");
                if let Some(window) = app.get_webview_window("main") {
                    window.show().unwrap();
                    window.set_focus().unwrap();
                }
            })?;
            
            Ok(())
        })
        .run(tauri::generate_context!())
        .expect("error while running tauri application");
}
```

---

## 8. 数据存储

### 8.1 嵌入式数据库

**使用 SQLx (SQLite)**:

```rust
// src-tauri/src/database.rs
use sqlx::{SqlitePool, sqlite::SqlitePoolOptions};

pub struct Database {
    pool: SqlitePool,
}

impl Database {
    pub async fn new(database_url: &str) -> anyhow::Result<Self> {
        let pool = SqlitePoolOptions::new()
            .max_connections(5)
            .connect(database_url)
            .await?;
        
        // 初始化表
        sqlx::query(
            r#"
            CREATE TABLE IF NOT EXISTS users (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                name TEXT NOT NULL,
                email TEXT NOT NULL UNIQUE
            )
            "#
        )
        .execute(&pool)
        .await?;
        
        Ok(Self { pool })
    }
    
    pub async fn create_user(&self, name: &str, email: &str) -> anyhow::Result<i64> {
        let result = sqlx::query!(
            "INSERT INTO users (name, email) VALUES (?, ?)",
            name,
            email
        )
        .execute(&self.pool)
        .await?;
        
        Ok(result.last_insert_rowid())
    }
    
    pub async fn get_user(&self, id: i64) -> anyhow::Result<Option<User>> {
        let user = sqlx::query_as!(
            User,
            "SELECT id, name, email FROM users WHERE id = ?",
            id
        )
        .fetch_optional(&self.pool)
        .await?;
        
        Ok(user)
    }
}

#[derive(Debug, serde::Serialize, serde::Deserialize)]
pub struct User {
    pub id: i64,
    pub name: String,
    pub email: String,
}
```

**Tauri Command**:

```rust
#[tauri::command]
pub async fn create_user(
    name: String,
    email: String,
    state: State<'_, Database>,
) -> Result<i64, String> {
    state.create_user(&name, &email)
        .await
        .map_err(|e| e.to_string())
}

#[tauri::command]
pub async fn get_user(
    id: i64,
    state: State<'_, Database>,
) -> Result<Option<User>, String> {
    state.get_user(id)
        .await
        .map_err(|e| e.to_string())
}
```

### 8.2 应用配置

**使用 tauri-plugin-store**:

```typescript
import { Store } from '@tauri-apps/plugin-store';

const store = await Store.load('config.json');

// 读取配置
const theme = await store.get<string>('theme');
console.log('Current theme:', theme ?? 'light');

// 写入配置
await store.set('theme', 'dark');

// 保存到磁盘
await store.save();

// 监听变化
const unlisten = await store.onChange((key, value) => {
  console.log(`Config changed: ${key} = ${value}`);
});
```

### 8.3 安全存储

**加密敏感数据 (使用 keyring)**:

```toml
[dependencies]
keyring = "2.0"
```

```rust
use keyring::Entry;

#[tauri::command]
pub async fn save_password(service: String, username: String, password: String) -> Result<(), String> {
    let entry = Entry::new(&service, &username)
        .map_err(|e| e.to_string())?;
    
    entry.set_password(&password)
        .map_err(|e| e.to_string())?;
    
    Ok(())
}

#[tauri::command]
pub async fn get_password(service: String, username: String) -> Result<String, String> {
    let entry = Entry::new(&service, &username)
        .map_err(|e| e.to_string())?;
    
    entry.get_password()
        .map_err(|e| e.to_string())
}
```

---

## 9. 自动更新

### 9.1 Updater 配置

**tauri.conf.json**:

```json
{
  "plugins": {
    "updater": {
      "active": true,
      "endpoints": [
        "https://releases.myapp.com/{{target}}/{{current_version}}"
      ],
      "dialog": true,
      "pubkey": "YOUR_PUBLIC_KEY_HERE"
    }
  }
}
```

### 9.2 更新流程

**后端**:

```rust
use tauri_plugin_updater::UpdaterExt;

#[tauri::command]
pub async fn check_for_updates(app: AppHandle) -> Result<(), String> {
    let updater = app.updater_builder().build()
        .map_err(|e| e.to_string())?;
    
    if let Some(update) = updater.check().await.map_err(|e| e.to_string())? {
        tracing::info!(
            current_version = %update.current_version,
            latest_version = %update.version,
            "Update available"
        );
        
        // 下载并安装更新
        update.download_and_install(|progress| {
            tracing::debug!("Download progress: {}%", progress);
        }).await.map_err(|e| e.to_string())?;
        
        // 重启应用
        app.restart();
    } else {
        tracing::info!("No update available");
    }
    
    Ok(())
}
```

**前端**:

```typescript
import { check } from '@tauri-apps/plugin-updater';
import { ask, message } from '@tauri-apps/plugin-dialog';

async function checkForUpdates() {
  const update = await check();
  
  if (update?.available) {
    const yes = await ask(
      `Update to v${update.version} is available!\n\nRelease notes: ${update.body}`,
      { title: 'Update Available', kind: 'info' }
    );
    
    if (yes) {
      await update.downloadAndInstall((progress) => {
        console.log(`Download progress: ${progress}%`);
      });
      
      await message('Update installed! App will restart.', { title: 'Update Complete' });
    }
  } else {
    await message('You are on the latest version!', { title: 'No Updates' });
  }
}
```

### 9.3 版本管理

**生成更新清单 (使用 Tauri CLI)**:

```bash
# 构建新版本
cargo tauri build

# 生成签名密钥对 (首次)
cargo tauri signer generate -w ~/.tauri/myapp.key

# 签名更新文件
cargo tauri signer sign target/release/bundle/msi/MyApp_0.1.0_x64_en-US.msi \
    -k ~/.tauri/myapp.key \
    -p "your_password"

# 部署到服务器
# - MyApp_0.1.0_x64_en-US.msi
# - MyApp_0.1.0_x64_en-US.msi.sig
# - latest.json (更新清单)
```

**latest.json** (示例):

```json
{
  "version": "0.2.0",
  "notes": "Bug fixes and performance improvements",
  "pub_date": "2025-10-11T12:00:00Z",
  "platforms": {
    "windows-x86_64": {
      "signature": "dW50cnVzdGVkIGNvbW1lbnQ6IHNpZ25hdHVyZQ==",
      "url": "https://releases.myapp.com/windows/MyApp_0.2.0_x64_en-US.msi"
    },
    "darwin-x86_64": {
      "signature": "dW50cnVzdGVkIGNvbW1lbnQ6IHNpZ25hdHVyZQ==",
      "url": "https://releases.myapp.com/macos/MyApp_0.2.0_x64.dmg"
    }
  }
}
```

---

## 10. OTLP 集成

### 10.1 后端遥测

**src-tauri/src/telemetry.rs**:

```rust
use opentelemetry::{global, trace::TracerProvider, KeyValue};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{runtime, trace::Config, Resource};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};

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
                    KeyValue::new("service.name", "tauri-app"),
                    KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
                    KeyValue::new("deployment.environment", "production"),
                ]))
        )
        .install_batch(runtime::Tokio)?;
    
    tracing_subscriber::registry()
        .with(EnvFilter::from_default_env())
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();
    
    Ok(())
}
```

**使用示例**:

```rust
use tracing::{info, info_span};

#[tauri::command]
#[tracing::instrument]
pub async fn process_data(data: String) -> Result<String, String> {
    info!(data_length = %data.len(), "Processing data");
    
    let span = info_span!("expensive_operation");
    let _guard = span.enter();
    
    // 模拟耗时操作
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    
    info!("Data processed successfully");
    Ok(format!("Processed: {}", data))
}
```

### 10.2 前端性能追踪

**使用 Web Performance API**:

```typescript
import { invoke } from '@tauri-apps/api/core';

async function trackedApiCall() {
  const startMark = `api-call-start-${Date.now()}`;
  const endMark = `api-call-end-${Date.now()}`;
  const measureName = 'api-call-duration';
  
  performance.mark(startMark);
  
  try {
    const result = await invoke('process_data', { data: 'example' });
    
    performance.mark(endMark);
    performance.measure(measureName, startMark, endMark);
    
    const measure = performance.getEntriesByName(measureName)[0];
    console.log(`API call took ${measure.duration}ms`);
    
    // 发送遥测
    await invoke('record_frontend_metric', {
      name: 'api_call_duration',
      value: measure.duration,
      unit: 'ms'
    });
    
    return result;
  } finally {
    performance.clearMarks(startMark);
    performance.clearMarks(endMark);
    performance.clearMeasures(measureName);
  }
}
```

### 10.3 崩溃报告

**使用 sentry (可选)**:

```toml
[dependencies]
sentry = { version = "0.32", features = ["tracing"] }
```

```rust
fn main() {
    let _guard = sentry::init((
        "https://your_dsn@sentry.io/project_id",
        sentry::ClientOptions {
            release: sentry::release_name!(),
            traces_sample_rate: 1.0,
            ..Default::default()
        },
    ));
    
    tauri::Builder::default()
        .setup(|app| {
            sentry::configure_scope(|scope| {
                scope.set_tag("app.version", env!("CARGO_PKG_VERSION"));
                scope.set_user(Some(sentry::User {
                    id: Some("user_id".to_string()),
                    ..Default::default()
                }));
            });
            Ok(())
        })
        .run(tauri::generate_context!())
        .expect("error while running tauri application");
}
```

---

## 11. 安全最佳实践

### 11.1 CSP 配置

**tauri.conf.json**:

```json
{
  "app": {
    "security": {
      "csp": "default-src 'self'; connect-src https://api.example.com; img-src 'self' data: https:; script-src 'self' 'wasm-unsafe-eval'; style-src 'self' 'unsafe-inline';"
    }
  }
}
```

### 11.2 IPC 安全

**限制 Command 访问**:

```rust
use tauri::ipc::InvokeError;

#[tauri::command]
pub async fn admin_action(
    window: tauri::Window,
    action: String,
) -> Result<(), InvokeError> {
    // 验证调用来源
    if window.label() != "main" {
        return Err(InvokeError::from("Unauthorized"));
    }
    
    // 验证用户权限 (从状态管理中获取)
    // ...
    
    Ok(())
}
```

### 11.3 代码签名

**Windows (Authenticode)**:

```bash
# 使用 SignTool
signtool sign /f certificate.pfx /p password /tr http://timestamp.digicert.com /td sha256 /fd sha256 MyApp.exe
```

**macOS (Notarization)**:

```bash
# 签名
codesign --force --deep --sign "Developer ID Application: Your Name" MyApp.app

# 公证
xcrun notarytool submit MyApp.dmg --keychain-profile "AC_PASSWORD" --wait

# 验证
spctl -a -v MyApp.app
```

---

## 12. 生产部署

### 12.1 跨平台构建

**GitHub Actions** (.github/workflows/release.yml):

```yaml
name: Release

on:
  push:
    tags:
      - 'v*'

jobs:
  release:
    strategy:
      fail-fast: false
      matrix:
        platform: [macos-latest, ubuntu-22.04, windows-latest]
    
    runs-on: ${{ matrix.platform }}
    
    steps:
      - uses: actions/checkout@v4
      
      - name: Setup Node.js
        uses: actions/setup-node@v4
        with:
          node-version: 20
      
      - name: Setup Rust
        uses: actions-rs/toolchain@v1
        with:
          toolchain: 1.90.0
      
      - name: Install dependencies (Ubuntu)
        if: matrix.platform == 'ubuntu-22.04'
        run: |
          sudo apt-get update
          sudo apt-get install -y libwebkit2gtk-4.1-dev libayatana-appindicator3-dev librsvg2-dev
      
      - name: Install frontend dependencies
        run: npm install
      
      - name: Build Tauri app
        uses: tauri-apps/tauri-action@v0
        env:
          GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
          TAURI_SIGNING_PRIVATE_KEY: ${{ secrets.TAURI_PRIVATE_KEY }}
          TAURI_SIGNING_PRIVATE_KEY_PASSWORD: ${{ secrets.TAURI_KEY_PASSWORD }}
        with:
          tagName: ${{ github.ref_name }}
          releaseName: 'MyApp ${{ github.ref_name }}'
          releaseBody: 'See CHANGELOG.md for details.'
          releaseDraft: true
          prerelease: false
```

### 12.2 应用打包

**构建命令**:

```bash
# Windows
cargo tauri build --target x86_64-pc-windows-msvc

# macOS
cargo tauri build --target x86_64-apple-darwin
cargo tauri build --target aarch64-apple-darwin

# Linux
cargo tauri build --target x86_64-unknown-linux-gnu

# 构建产物
# - Windows: target/release/bundle/msi/*.msi
# - macOS: target/release/bundle/macos/*.app, *.dmg
# - Linux: target/release/bundle/deb/*.deb, appimage/*.AppImage
```

### 12.3 发布流程

1. **更新版本号**: `Cargo.toml`, `package.json`, `tauri.conf.json`
2. **生成 CHANGELOG**: 记录版本变更
3. **构建应用**: `cargo tauri build`
4. **签名**: Windows Authenticode, macOS Notarization
5. **生成更新清单**: `latest.json`
6. **上传到服务器**: GitHub Releases, S3, CDN
7. **通知用户**: 应用内更新检查

---

## 总结

Tauri 是 **Electron 的最佳替代方案**，为桌面应用开发提供了 **轻量、安全、高性能** 的解决方案：

### 核心优势

1. **应用体积小**: 3-5 MB vs Electron 50-100 MB
2. **内存占用低**: 20-40 MB vs Electron 100-200 MB
3. **Rust 后端**: 内存安全 + 高性能 + 零成本抽象
4. **系统 WebView**: 无需打包 Chromium，使用原生渲染引擎
5. **细粒度权限**: 白名单机制，沙箱隔离
6. **自动更新**: 内置更新器，支持签名验证

### 国际标准对齐

- **Web**: HTML5, CSS3, WebAssembly, ES2022+
- **Desktop**: Windows WebView2, macOS WKWebView, Linux WebKitGTK
- **Security**: CSP, IPC Permissions, Code Signing
- **Observability**: OpenTelemetry Protocol, Distributed Tracing

### 适用场景

- 跨平台桌面应用（macOS, Windows, Linux）
- 系统工具（文件管理器、编辑器、监控工具）
- 企业内部应用（CRM, ERP, Admin Panel）
- 游戏启动器/管理工具

Tauri 是 Rust 生态中 **最成熟的桌面应用框架**，适合需要 **原生性能、小体积、高安全性** 的现代桌面应用开发。
