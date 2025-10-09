# VS Code Rust + OTLP 完整开发配置指南

## 目录

- [VS Code Rust + OTLP 完整开发配置指南](#vs-code-rust--otlp-完整开发配置指南)
  - [目录](#目录)
  - [1. 环境概述](#1-环境概述)
  - [2. 必装扩展](#2-必装扩展)
    - [2.1 Rust 核心扩展](#21-rust-核心扩展)
    - [2.2 调试扩展](#22-调试扩展)
    - [2.3 效率工具](#23-效率工具)
  - [3. Workspace 配置](#3-workspace-配置)
    - [3.1 settings.json](#31-settingsjson)
    - [3.2 extensions.json](#32-extensionsjson)
  - [4. 调试配置](#4-调试配置)
    - [4.1 launch.json](#41-launchjson)
    - [4.2 tasks.json](#42-tasksjson)
  - [5. Rust-analyzer 配置](#5-rust-analyzer-配置)
    - [5.1 基础配置](#51-基础配置)
    - [5.2 Cargo 配置](#52-cargo-配置)
    - [5.3 性能优化](#53-性能优化)
  - [6. 代码片段](#6-代码片段)
  - [7. 快捷键配置](#7-快捷键配置)
  - [8. Docker 集成](#8-docker-集成)
    - [8.1 docker-compose.yml](#81-docker-composeyml)
    - [8.2 Dev Container](#82-dev-container)
  - [9. Git 集成](#9-git-集成)
  - [10. 性能分析工具](#10-性能分析工具)
  - [11. 完整示例项目配置](#11-完整示例项目配置)
  - [总结](#总结)

---

## 1. 环境概述

VS Code 是 Rust 开发的主流 IDE，结合 rust-analyzer 和 OpenTelemetry 相关扩展，可以提供强大的开发体验。

**推荐环境**：

- VS Code 1.85+
- Rust 1.90+
- rust-analyzer 0.3.2264+

---

## 2. 必装扩展

### 2.1 Rust 核心扩展

```jsonc
{
  // Rust Language Server
  "rust-lang.rust-analyzer": "最新版本",
  
  // CodeLLDB - 调试器
  "vadimcn.vscode-lldb": "最新版本",
  
  // Cargo - 项目管理
  "swellaby.vscode-rust-pack": "最新版本",
  
  // Crates - 依赖管理
  "serayuzgur.crates": "最新版本",
  
  // Better TOML - Cargo.toml 支持
  "bungcip.better-toml": "最新版本"
}
```

### 2.2 调试扩展

```jsonc
{
  // CodeLLDB - Rust 调试
  "vadimcn.vscode-lldb": "最新版本",
  
  // GitLens - Git 增强
  "eamodio.gitlens": "最新版本",
  
  // Error Lens - 行内错误显示
  "usernamehw.errorlens": "最新版本"
}
```

### 2.3 效率工具

```jsonc
{
  // Tabnine - AI 代码补全
  "tabnine.tabnine-vscode": "最新版本",
  
  // GitHub Copilot - AI 编程助手
  "github.copilot": "最新版本",
  
  // REST Client - API 测试
  "humao.rest-client": "最新版本",
  
  // Thunder Client - API 测试
  "rangav.vscode-thunder-client": "最新版本",
  
  // Docker - 容器管理
  "ms-azuretools.vscode-docker": "最新版本",
  
  // YAML - YAML 支持
  "redhat.vscode-yaml": "最新版本"
}
```

---

## 3. Workspace 配置

### 3.1 settings.json

在项目根目录创建 `.vscode/settings.json`：

```json
{
  // ===== Rust-Analyzer 配置 =====
  "rust-analyzer.check.command": "clippy",
  "rust-analyzer.check.allTargets": true,
  "rust-analyzer.cargo.allFeatures": true,
  "rust-analyzer.cargo.loadOutDirsFromCheck": true,
  "rust-analyzer.procMacro.enable": true,
  "rust-analyzer.inlayHints.enable": true,
  "rust-analyzer.inlayHints.chainingHints.enable": true,
  "rust-analyzer.inlayHints.parameterHints.enable": true,
  "rust-analyzer.lens.enable": true,
  "rust-analyzer.lens.references.adt.enable": true,
  "rust-analyzer.lens.references.enumVariant.enable": true,
  "rust-analyzer.lens.references.method.enable": true,
  "rust-analyzer.lens.references.trait.enable": true,
  
  // ===== 编辑器配置 =====
  "editor.formatOnSave": true,
  "editor.defaultFormatter": "rust-lang.rust-analyzer",
  "[rust]": {
    "editor.defaultFormatter": "rust-lang.rust-analyzer",
    "editor.formatOnSave": true,
    "editor.tabSize": 4,
    "editor.insertSpaces": true
  },
  "editor.rulers": [100],
  "editor.codeActionsOnSave": {
    "source.fixAll": "always",
    "source.organizeImports": "always"
  },
  
  // ===== Files 配置 =====
  "files.associations": {
    "*.rs": "rust",
    "Cargo.toml": "toml",
    "Cargo.lock": "toml"
  },
  "files.exclude": {
    "**/target": true,
    "**/.git": true
  },
  "files.watcherExclude": {
    "**/target/**": true
  },
  
  // ===== Terminal 配置 =====
  "terminal.integrated.env.linux": {
    "RUST_BACKTRACE": "1",
    "RUST_LOG": "debug"
  },
  "terminal.integrated.env.osx": {
    "RUST_BACKTRACE": "1",
    "RUST_LOG": "debug"
  },
  "terminal.integrated.env.windows": {
    "RUST_BACKTRACE": "1",
    "RUST_LOG": "debug"
  },
  
  // ===== Search 配置 =====
  "search.exclude": {
    "**/target": true,
    "**/Cargo.lock": true
  },
  
  // ===== Crates 扩展配置 =====
  "crates.listPreReleases": false,
  "crates.useLocalCargoIndex": true,
  
  // ===== Git 配置 =====
  "git.autofetch": true,
  "git.confirmSync": false,
  
  // ===== Error Lens 配置 =====
  "errorLens.enabledDiagnosticLevels": [
    "error",
    "warning",
    "info"
  ],
  
  // ===== OpenTelemetry 相关 =====
  "rest-client.environmentVariables": {
    "$shared": {
      "otlpEndpoint": "http://localhost:4317",
      "jaegerEndpoint": "http://localhost:16686"
    }
  }
}
```

### 3.2 extensions.json

在项目根目录创建 `.vscode/extensions.json`：

```json
{
  "recommendations": [
    "rust-lang.rust-analyzer",
    "vadimcn.vscode-lldb",
    "serayuzgur.crates",
    "bungcip.better-toml",
    "usernamehw.errorlens",
    "eamodio.gitlens",
    "ms-azuretools.vscode-docker",
    "humao.rest-client",
    "redhat.vscode-yaml"
  ]
}
```

---

## 4. 调试配置

### 4.1 launch.json

在项目根目录创建 `.vscode/launch.json`：

```json
{
  "version": "0.2.0",
  "configurations": [
    {
      "type": "lldb",
      "request": "launch",
      "name": "Debug executable 'your-project'",
      "cargo": {
        "args": [
          "build",
          "--bin=your-project",
          "--package=your-project"
        ],
        "filter": {
          "name": "your-project",
          "kind": "bin"
        }
      },
      "args": [],
      "cwd": "${workspaceFolder}",
      "env": {
        "RUST_BACKTRACE": "1",
        "RUST_LOG": "debug",
        "OTEL_EXPORTER_OTLP_ENDPOINT": "http://localhost:4317"
      }
    },
    {
      "type": "lldb",
      "request": "launch",
      "name": "Debug unit tests",
      "cargo": {
        "args": [
          "test",
          "--no-run",
          "--lib",
          "--package=your-project"
        ],
        "filter": {
          "name": "your-project",
          "kind": "lib"
        }
      },
      "args": [],
      "cwd": "${workspaceFolder}",
      "env": {
        "RUST_BACKTRACE": "1"
      }
    },
    {
      "type": "lldb",
      "request": "launch",
      "name": "Debug integration tests",
      "cargo": {
        "args": [
          "test",
          "--no-run",
          "--test=*",
          "--package=your-project"
        ]
      },
      "args": [],
      "cwd": "${workspaceFolder}"
    },
    {
      "type": "lldb",
      "request": "launch",
      "name": "Debug with Jaeger",
      "cargo": {
        "args": [
          "build",
          "--bin=your-project"
        ]
      },
      "args": [],
      "cwd": "${workspaceFolder}",
      "env": {
        "RUST_BACKTRACE": "1",
        "RUST_LOG": "info,your_project=debug",
        "OTEL_EXPORTER_OTLP_ENDPOINT": "http://localhost:4317",
        "OTEL_SERVICE_NAME": "your-project-dev"
      },
      "preLaunchTask": "start-jaeger"
    }
  ]
}
```

### 4.2 tasks.json

在项目根目录创建 `.vscode/tasks.json`：

```json
{
  "version": "2.0.0",
  "tasks": [
    {
      "label": "cargo build",
      "type": "shell",
      "command": "cargo",
      "args": ["build"],
      "group": {
        "kind": "build",
        "isDefault": true
      },
      "presentation": {
        "reveal": "always",
        "panel": "new"
      },
      "problemMatcher": ["$rustc"]
    },
    {
      "label": "cargo test",
      "type": "shell",
      "command": "cargo",
      "args": ["test"],
      "group": {
        "kind": "test",
        "isDefault": true
      },
      "presentation": {
        "reveal": "always",
        "panel": "new"
      },
      "problemMatcher": ["$rustc"]
    },
    {
      "label": "cargo clippy",
      "type": "shell",
      "command": "cargo",
      "args": ["clippy", "--all-targets", "--all-features", "--", "-D", "warnings"],
      "group": "build",
      "presentation": {
        "reveal": "always",
        "panel": "new"
      },
      "problemMatcher": ["$rustc"]
    },
    {
      "label": "cargo fmt",
      "type": "shell",
      "command": "cargo",
      "args": ["fmt", "--all"],
      "group": "build",
      "presentation": {
        "reveal": "silent"
      }
    },
    {
      "label": "start-jaeger",
      "type": "shell",
      "command": "docker",
      "args": [
        "run",
        "-d",
        "--name", "jaeger-dev",
        "-p", "6831:6831/udp",
        "-p", "6832:6832/udp",
        "-p", "5778:5778",
        "-p", "16686:16686",
        "-p", "4317:4317",
        "-p", "4318:4318",
        "-p", "14250:14250",
        "-p", "14268:14268",
        "-p", "14269:14269",
        "-p", "9411:9411",
        "jaegertracing/all-in-one:1.67.0"
      ],
      "presentation": {
        "reveal": "always",
        "panel": "new"
      },
      "problemMatcher": []
    },
    {
      "label": "stop-jaeger",
      "type": "shell",
      "command": "docker",
      "args": ["stop", "jaeger-dev", "&&", "docker", "rm", "jaeger-dev"],
      "presentation": {
        "reveal": "always",
        "panel": "new"
      },
      "problemMatcher": []
    },
    {
      "label": "cargo run",
      "type": "shell",
      "command": "cargo",
      "args": ["run"],
      "group": "build",
      "presentation": {
        "reveal": "always",
        "panel": "new"
      },
      "problemMatcher": ["$rustc"]
    },
    {
      "label": "cargo watch",
      "type": "shell",
      "command": "cargo",
      "args": ["watch", "-x", "run"],
      "isBackground": true,
      "presentation": {
        "reveal": "always",
        "panel": "new"
      },
      "problemMatcher": ["$rustc"]
    }
  ]
}
```

---

## 5. Rust-analyzer 配置

### 5.1 基础配置

在 `settings.json` 中添加：

```json
{
  "rust-analyzer.server.extraEnv": {
    "RUST_LOG": "rust_analyzer=info"
  },
  "rust-analyzer.updates.channel": "stable",
  "rust-analyzer.imports.granularity.group": "module",
  "rust-analyzer.imports.prefix": "self",
  "rust-analyzer.assist.importPrefix": "self",
  "rust-analyzer.completion.autoimport.enable": true,
  "rust-analyzer.completion.autoself.enable": true
}
```

### 5.2 Cargo 配置

```json
{
  "rust-analyzer.cargo.features": "all",
  "rust-analyzer.cargo.noDefaultFeatures": false,
  "rust-analyzer.cargo.target": null,
  "rust-analyzer.cargo.runBuildScripts": true,
  "rust-analyzer.cargo.useRustcWrapperForBuildScripts": true
}
```

### 5.3 性能优化

```json
{
  "rust-analyzer.checkOnSave.enable": true,
  "rust-analyzer.checkOnSave.command": "clippy",
  "rust-analyzer.checkOnSave.extraArgs": [
    "--all-targets",
    "--all-features"
  ],
  "rust-analyzer.files.watcher": "client",
  "rust-analyzer.files.excludeDirs": [
    "target",
    ".git"
  ]
}
```

---

## 6. 代码片段

在项目根目录创建 `.vscode/rust.code-snippets`：

```json
{
  "OpenTelemetry Initialize": {
    "prefix": "otlp-init",
    "body": [
      "use opentelemetry::global;",
      "use opentelemetry_sdk::trace::TracerProvider;",
      "use opentelemetry_otlp::WithExportConfig;",
      "",
      "pub fn init_telemetry() -> Result<TracerProvider, Box<dyn std::error::Error>> {",
      "    let tracer_provider = opentelemetry_otlp::new_pipeline()",
      "        .tracing()",
      "        .with_exporter(",
      "            opentelemetry_otlp::new_exporter()",
      "                .tonic()",
      "                .with_endpoint(\"${1:http://localhost:4317}\"),",
      "        )",
      "        .install_batch(opentelemetry_sdk::runtime::Tokio)?;",
      "",
      "    global::set_tracer_provider(tracer_provider.clone());",
      "    Ok(tracer_provider)",
      "}"
    ],
    "description": "Initialize OpenTelemetry OTLP exporter"
  },
  "Create Traced Function": {
    "prefix": "trace-fn",
    "body": [
      "#[tracing::instrument(skip(${1:params}))]",
      "pub async fn ${2:function_name}(${3:params}) -> Result<${4:ReturnType}, Box<dyn std::error::Error>> {",
      "    ${0:// Implementation}",
      "}"
    ],
    "description": "Create a traced async function"
  },
  "Create Span": {
    "prefix": "span-create",
    "body": [
      "let tracer = global::tracer(\"${1:component-name}\");",
      "let mut span = tracer",
      "    .span_builder(\"${2:operation-name}\")",
      "    .with_kind(SpanKind::${3|Internal,Client,Server,Producer,Consumer|})",
      "    .with_attributes(vec![",
      "        KeyValue::new(\"${4:key}\", \"${5:value}\"),",
      "    ])",
      "    .start(&tracer);",
      "",
      "let cx = Context::current_with_span(span);",
      "let _guard = cx.attach();",
      "",
      "${0:// Your code here}"
    ],
    "description": "Create a manual OpenTelemetry span"
  },
  "Tracing Subscriber Init": {
    "prefix": "tracing-init",
    "body": [
      "use tracing_subscriber::layer::SubscriberExt;",
      "use tracing_subscriber::util::SubscriberInitExt;",
      "",
      "tracing_subscriber::registry()",
      "    .with(tracing_subscriber::EnvFilter::from_default_env())",
      "    .with(tracing_subscriber::fmt::layer())",
      "    .with(tracing_opentelemetry::layer().with_tracer(",
      "        global::tracer(\"${1:service-name}\"),",
      "    ))",
      "    .init();"
    ],
    "description": "Initialize tracing subscriber with OpenTelemetry"
  },
  "Tokio Main with OTLP": {
    "prefix": "tokio-main-otlp",
    "body": [
      "#[tokio::main]",
      "async fn main() -> Result<(), Box<dyn std::error::Error>> {",
      "    // Initialize telemetry",
      "    let _tracer_provider = init_telemetry()?;",
      "",
      "    // Initialize tracing",
      "    tracing_subscriber::registry()",
      "        .with(tracing_subscriber::EnvFilter::from_default_env())",
      "        .with(tracing_subscriber::fmt::layer())",
      "        .with(tracing_opentelemetry::layer().with_tracer(",
      "            global::tracer(\"${1:service-name}\"),",
      "        ))",
      "        .init();",
      "",
      "    ${0:// Your code here}",
      "",
      "    // Cleanup",
      "    global::shutdown_tracer_provider();",
      "    Ok(())",
      "}"
    ],
    "description": "Tokio main function with OpenTelemetry initialization"
  },
  "HTTP Client with Trace": {
    "prefix": "http-client-trace",
    "body": [
      "use reqwest::Client;",
      "use opentelemetry::trace::{Tracer, TraceContextExt, SpanKind};",
      "use opentelemetry::{global, Context, KeyValue};",
      "",
      "pub async fn ${1:http_request}(url: &str) -> Result<String, Box<dyn std::error::Error>> {",
      "    let tracer = global::tracer(\"http-client\");",
      "    let mut span = tracer",
      "        .span_builder(\"HTTP GET\")",
      "        .with_kind(SpanKind::Client)",
      "        .with_attributes(vec![",
      "            KeyValue::new(\"http.url\", url.to_string()),",
      "        ])",
      "        .start(&tracer);",
      "",
      "    let cx = Context::current_with_span(span);",
      "    let _guard = cx.attach();",
      "",
      "    let client = Client::new();",
      "    let response = client.get(url).send().await?;",
      "    let body = response.text().await?;",
      "",
      "    Ok(body)",
      "}"
    ],
    "description": "HTTP client request with tracing"
  }
}
```

---

## 7. 快捷键配置

在项目根目录创建 `.vscode/keybindings.json`：

```json
[
  {
    "key": "ctrl+shift+b",
    "command": "workbench.action.tasks.runTask",
    "args": "cargo build"
  },
  {
    "key": "ctrl+shift+t",
    "command": "workbench.action.tasks.runTask",
    "args": "cargo test"
  },
  {
    "key": "ctrl+shift+c",
    "command": "workbench.action.tasks.runTask",
    "args": "cargo clippy"
  },
  {
    "key": "ctrl+shift+f",
    "command": "workbench.action.tasks.runTask",
    "args": "cargo fmt"
  },
  {
    "key": "ctrl+shift+r",
    "command": "workbench.action.tasks.runTask",
    "args": "cargo run"
  }
]
```

---

## 8. Docker 集成

### 8.1 docker-compose.yml

在项目根目录创建 `docker-compose.yml`：

```yaml
version: '3.9'

services:
  jaeger:
    image: jaegertracing/all-in-one:1.67.0
    container_name: jaeger-dev
    ports:
      - "6831:6831/udp"
      - "6832:6832/udp"
      - "5778:5778"
      - "16686:16686"
      - "4317:4317"
      - "4318:4318"
      - "14250:14250"
      - "14268:14268"
      - "14269:14269"
      - "9411:9411"
    environment:
      - COLLECTOR_OTLP_ENABLED=true
    networks:
      - otlp-network

  redis:
    image: redis:7-alpine
    container_name: redis-dev
    ports:
      - "6379:6379"
    networks:
      - otlp-network

  postgres:
    image: postgres:16-alpine
    container_name: postgres-dev
    ports:
      - "5432:5432"
    environment:
      - POSTGRES_USER=dev
      - POSTGRES_PASSWORD=dev
      - POSTGRES_DB=myapp
    networks:
      - otlp-network

networks:
  otlp-network:
    driver: bridge
```

### 8.2 Dev Container

在项目根目录创建 `.devcontainer/devcontainer.json`：

```json
{
  "name": "Rust + OTLP Development",
  "dockerComposeFile": "../docker-compose.yml",
  "service": "app",
  "workspaceFolder": "/workspace",
  "customizations": {
    "vscode": {
      "extensions": [
        "rust-lang.rust-analyzer",
        "vadimcn.vscode-lldb",
        "serayuzgur.crates",
        "bungcip.better-toml"
      ],
      "settings": {
        "rust-analyzer.check.command": "clippy"
      }
    }
  },
  "forwardPorts": [3000, 4317, 16686],
  "postCreateCommand": "rustup update && cargo build"
}
```

---

## 9. Git 集成

在项目根目录创建 `.gitignore`：

```text
# Rust
/target/
Cargo.lock

# IDE
.vscode/
.idea/
*.swp
*.swo
*~

# OS
.DS_Store
Thumbs.db

# OpenTelemetry
*.trace
*.log
```

---

## 10. 性能分析工具

在 `tasks.json` 中添加性能分析任务：

```json
{
  "label": "cargo flamegraph",
  "type": "shell",
  "command": "cargo",
  "args": ["flamegraph", "--bin=your-project"],
  "group": "build",
  "presentation": {
    "reveal": "always",
    "panel": "new"
  },
  "problemMatcher": []
},
{
  "label": "cargo bench",
  "type": "shell",
  "command": "cargo",
  "args": ["bench"],
  "group": "test",
  "presentation": {
    "reveal": "always",
    "panel": "new"
  },
  "problemMatcher": ["$rustc"]
}
```

---

## 11. 完整示例项目配置

项目结构：

```text
my-rust-otlp-project/
├── .vscode/
│   ├── settings.json
│   ├── launch.json
│   ├── tasks.json
│   ├── extensions.json
│   └── rust.code-snippets
├── .devcontainer/
│   └── devcontainer.json
├── src/
│   ├── main.rs
│   ├── telemetry.rs
│   └── lib.rs
├── tests/
│   └── integration_test.rs
├── Cargo.toml
├── docker-compose.yml
├── .gitignore
└── README.md
```

**Cargo.toml**：

```toml
[package]
name = "my-rust-otlp-project"
version = "0.1.0"
edition = "2021"

[dependencies]
opentelemetry = { version = "0.31.0", features = ["trace", "metrics"] }
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.24.0", features = ["grpc-tonic"] }
tokio = { version = "1.47.1", features = ["full"] }
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
tracing-opentelemetry = "0.31.0"

[dev-dependencies]
criterion = "0.5"

[[bench]]
name = "my_benchmark"
harness = false
```

---

## 总结

本指南提供了 VS Code 中 Rust + OTLP 开发的完整配置：

1. **扩展安装**：rust-analyzer、CodeLLDB、Crates 等
2. **Workspace 配置**：settings.json、extensions.json
3. **调试配置**：launch.json、tasks.json
4. **代码片段**：OTLP 初始化、Span 创建、Tracing 集成
5. **Docker 集成**：Jaeger、Redis、PostgreSQL
6. **性能工具**：Flamegraph、Benchmark

通过这些配置，您可以获得高效的 Rust + OpenTelemetry 开发体验。
