# 调试工具 - Rust 完整版

## 目录

- [调试工具 - Rust 完整版](#调试工具---rust-完整版)
  - [目录](#目录)
  - [1. 调试工具概览](#1-调试工具概览)
    - [1.1 工具分类](#11-工具分类)
    - [1.2 调试流程](#12-调试流程)
  - [2. LLDB 调试](#2-lldb-调试)
    - [2.1 安装配置](#21-安装配置)
    - [2.2 基础命令](#22-基础命令)
    - [2.3 断点调试](#23-断点调试)
    - [2.4 Span 数据检查](#24-span-数据检查)
  - [3. GDB 调试](#3-gdb-调试)
    - [3.1 安装配置](#31-安装配置)
    - [3.2 基础命令](#32-基础命令)
    - [3.3 调试异步代码](#33-调试异步代码)
  - [4. VS Code 调试](#4-vs-code-调试)
    - [4.1 launch.json 配置](#41-launchjson-配置)
    - [4.2 调试会话](#42-调试会话)
    - [4.3 条件断点](#43-条件断点)
  - [5. tracing-subscriber 调试](#5-tracing-subscriber-调试)
    - [5.1 控制台输出](#51-控制台输出)
    - [5.2 文件日志](#52-文件日志)
    - [5.3 过滤器配置](#53-过滤器配置)
  - [6. Jaeger UI 调试](#6-jaeger-ui-调试)
    - [6.1 查询 Trace](#61-查询-trace)
    - [6.2 分析调用链](#62-分析调用链)
    - [6.3 性能分析](#63-性能分析)
  - [7. cargo-expand 宏展开](#7-cargo-expand-宏展开)
    - [7.1 安装使用](#71-安装使用)
    - [7.2 展开 #\[instrument\]](#72-展开-instrument)
  - [8. cargo-flamegraph 性能分析](#8-cargo-flamegraph-性能分析)
    - [8.1 安装配置](#81-安装配置)
    - [8.2 生成火焰图](#82-生成火焰图)
  - [9. tokio-console 异步调试](#9-tokio-console-异步调试)
    - [9.1 安装配置](#91-安装配置)
    - [9.2 监控 Task](#92-监控-task)
  - [10. 网络调试工具](#10-网络调试工具)
    - [10.1 tcpdump 抓包](#101-tcpdump-抓包)
    - [10.2 Wireshark 分析](#102-wireshark-分析)
  - [11. 内存调试](#11-内存调试)
    - [11.1 valgrind](#111-valgrind)
    - [11.2 heaptrack](#112-heaptrack)
  - [12. 生产环境调试](#12-生产环境调试)
    - [12.1 远程调试](#121-远程调试)
    - [12.2 coredump 分析](#122-coredump-分析)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [工具对比](#工具对比)
    - [最佳实践清单](#最佳实践清单)

---

## 1. 调试工具概览

### 1.1 工具分类

````text
调试工具分类:

1. 交互式调试器
   - LLDB (推荐 macOS/Linux)
   - GDB (Linux)
   - VS Code Debugger

2. 日志调试
   - tracing-subscriber
   - env_logger
   - log4rs

3. 追踪可视化
   - Jaeger UI
   - Zipkin UI
   - Grafana Tempo

4. 性能分析
   - cargo-flamegraph
   - perf (Linux)
   - Instruments (macOS)

5. 异步调试
   - tokio-console
   - async-backtrace

6. 网络调试
   - tcpdump
   - Wireshark
   - mitmproxy

7. 内存调试
   - valgrind
   - heaptrack
   - cargo-bloat
````

### 1.2 调试流程

````text
1. 复现问题
   ├─ 本地环境复现
   ├─ 收集日志/Trace
   └─ 记录复现步骤

2. 定位问题
   ├─ 查看 Jaeger Trace
   ├─ 分析日志
   └─ 使用调试器定位代码位置

3. 分析原因
   ├─ 检查变量值
   ├─ 查看调用栈
   └─ 分析 Span 属性

4. 修复验证
   ├─ 编写测试用例
   ├─ 本地验证
   └─ 提交 PR
````

---

## 2. LLDB 调试

### 2.1 安装配置

````bash
# macOS (已预装)
xcode-select --install

# Linux
sudo apt-get install lldb

# Rust 支持
rustup component add rust-src
rustup component add lldb-preview
````

**Cargo.toml 调试配置**:

````toml
[profile.dev]
opt-level = 0
debug = true
debug-assertions = true
overflow-checks = true
````

### 2.2 基础命令

````bash
# 启动调试
lldb target/debug/my-app

# 常用命令
(lldb) breakpoint set --name main          # 在 main 函数设置断点
(lldb) breakpoint set --file main.rs --line 10  # 在指定行设置断点
(lldb) run                                  # 运行程序
(lldb) continue (c)                         # 继续执行
(lldb) next (n)                             # 单步执行 (跳过函数)
(lldb) step (s)                             # 单步执行 (进入函数)
(lldb) finish                               # 执行到函数返回
(lldb) print variable_name (p)              # 打印变量
(lldb) frame variable                       # 打印所有局部变量
(lldb) backtrace (bt)                       # 打印调用栈
(lldb) thread list                          # 列出所有线程
(lldb) quit                                 # 退出调试器
````

### 2.3 断点调试

````bash
# 设置条件断点
(lldb) breakpoint set --name process_order --condition 'order_id == "ORD-001"'

# 查看断点
(lldb) breakpoint list

# 删除断点
(lldb) breakpoint delete 1

# 禁用/启用断点
(lldb) breakpoint disable 1
(lldb) breakpoint enable 1

# 设置观察点 (变量改变时中断)
(lldb) watchpoint set variable my_var
````

### 2.4 Span 数据检查

````rust
// src/main.rs
use tracing::{info, instrument, Span};
use opentelemetry::trace::TraceContextExt;

#[instrument(name = "process_order")]
pub async fn process_order(order_id: &str) -> Result<(), anyhow::Error> {
    let span = Span::current();
    
    // 设置断点这里，检查 Span 数据
    let context = span.context();
    let span_context = context.span().span_context();
    
    info!(
        trace_id = %span_context.trace_id(),
        span_id = %span_context.span_id(),
        is_sampled = span_context.is_sampled(),
        "Processing order"
    );
    
    Ok(())
}
````

**LLDB 调试会话**:

````bash
$ lldb target/debug/my-app
(lldb) breakpoint set --file main.rs --line 12
(lldb) run

# 程序在断点处停止
(lldb) frame variable span
# (tracing::Span) span = { ... }

(lldb) frame variable context
# (opentelemetry::Context) context = { ... }

(lldb) print span_context.trace_id()
# (opentelemetry::trace::TraceId) $0 = { ... }
````

---

## 3. GDB 调试

### 3.1 安装配置

````bash
# Linux
sudo apt-get install gdb

# 安装 Rust 支持
rustup component add rust-src
````

**~/.gdbinit**:

````text
set print pretty on
set print array on
set print array-indexes on
set pagination off
````

### 3.2 基础命令

````bash
# 启动调试
gdb target/debug/my-app

# 常用命令
(gdb) break main                    # 在 main 函数设置断点
(gdb) break main.rs:10              # 在指定行设置断点
(gdb) run                           # 运行程序
(gdb) continue (c)                  # 继续执行
(gdb) next (n)                      # 单步执行 (跳过函数)
(gdb) step (s)                      # 单步执行 (进入函数)
(gdb) finish                        # 执行到函数返回
(gdb) print variable_name (p)       # 打印变量
(gdb) backtrace (bt)                # 打印调用栈
(gdb) info threads                  # 列出所有线程
(gdb) thread 2                      # 切换到线程 2
(gdb) quit                          # 退出调试器
````

### 3.3 调试异步代码

````rust
use tokio::runtime::Runtime;
use tracing::{info, instrument};

#[instrument]
async fn async_function() {
    info!("Step 1");
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    info!("Step 2");  // 设置断点
}

fn main() {
    let rt = Runtime::new().unwrap();
    rt.block_on(async_function());
}
````

**GDB 调试**:

````bash
(gdb) break main.rs:8  # Step 2 行
(gdb) run

# 查看异步上下文
(gdb) info threads
(gdb) thread apply all bt  # 打印所有线程的调用栈
````

---

## 4. VS Code 调试

### 4.1 launch.json 配置

````json
{
  "version": "0.2.0",
  "configurations": [
    {
      "type": "lldb",
      "request": "launch",
      "name": "Debug Rust Application",
      "cargo": {
        "args": [
          "build",
          "--bin=my-app",
          "--package=my-app"
        ],
        "filter": {
          "name": "my-app",
          "kind": "bin"
        }
      },
      "args": [],
      "cwd": "${workspaceFolder}",
      "env": {
        "RUST_LOG": "debug",
        "RUST_BACKTRACE": "1"
      }
    },
    {
      "type": "lldb",
      "request": "launch",
      "name": "Debug Tests",
      "cargo": {
        "args": [
          "test",
          "--no-run",
          "--lib"
        ]
      },
      "args": ["--nocapture"],
      "cwd": "${workspaceFolder}"
    },
    {
      "type": "lldb",
      "request": "attach",
      "name": "Attach to Process",
      "pid": "${command:pickProcess}"
    }
  ]
}
````

### 4.2 调试会话

````rust
use tracing::{info, instrument};

#[instrument(name = "calculate_total")]
pub fn calculate_total(items: &[f64]) -> f64 {
    let mut total = 0.0;
    
    for item in items {
        total += item;  // ← 点击行号设置断点
        info!(item, total, "Adding item");
    }
    
    total
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_calculate_total() {
        let items = vec![10.0, 20.0, 30.0];
        let total = calculate_total(&items);
        assert_eq!(total, 60.0);
    }
}
````

**调试步骤**:

1. 在 `total += item` 行设置断点（点击行号）
2. 按 `F5` 启动调试
3. 使用 `F10` (Step Over) 单步执行
4. 鼠标悬停在变量上查看值
5. 在 "Debug Console" 中输入表达式

### 4.3 条件断点

1. 右键点击断点
2. 选择 "Edit Breakpoint"
3. 输入条件：`item > 20.0`
4. 断点只在条件满足时触发

---

## 5. tracing-subscriber 调试

### 5.1 控制台输出

````rust
use tracing_subscriber::{fmt, EnvFilter};

pub fn init_console_logging() {
    fmt()
        .with_env_filter(EnvFilter::from_default_env())
        .with_target(true)
        .with_thread_ids(true)
        .with_line_number(true)
        .with_file(true)
        .with_level(true)
        .with_ansi(true)
        .pretty()
        .init();
}
````

**输出示例**:

````text
2025-10-09T12:34:56.123Z  INFO ThreadId(01) my_app::api::orders:45: Processing order
  at src/api/orders.rs:45 on ThreadId(01)
  in my_app::api::orders::process_order with order_id: "ORD-001"

  with:
    order_id: "ORD-001"
    user_id: 12345
    amount: 99.99
````

### 5.2 文件日志

````rust
use tracing_subscriber::fmt;
use tracing_appender::rolling;

pub fn init_file_logging() {
    let file_appender = rolling::daily("./logs", "app.log");

    fmt()
        .with_writer(file_appender)
        .with_ansi(false)
        .json()
        .init();
}
````

### 5.3 过滤器配置

````bash
# 环境变量
export RUST_LOG=info,my_app=debug,sqlx=warn,hyper=error

# 代码配置
RUST_LOG="info,my_app::api=trace,my_app::db=debug" cargo run
````

````rust
use tracing_subscriber::EnvFilter;

pub fn init_filtered_logging() {
    let filter = EnvFilter::new("info")
        .add_directive("my_app::api=trace".parse().unwrap())
        .add_directive("my_app::db=debug".parse().unwrap())
        .add_directive("sqlx=warn".parse().unwrap());

    tracing_subscriber::fmt()
        .with_env_filter(filter)
        .init();
}
````

---

## 6. Jaeger UI 调试

### 6.1 查询 Trace

````bash
# 启动 Jaeger All-in-One
docker run -d --name jaeger \
  -e COLLECTOR_OTLP_ENABLED=true \
  -p 16686:16686 \
  -p 4317:4317 \
  jaegertracing/all-in-one:latest

# 访问 UI
open http://localhost:16686
````

**查询操作**:

1. **按服务名查询**:
   - Service: `my-rust-service`
   - Lookback: `1h`
   - Limit: `20`

2. **按标签查询**:
   - Tags: `http.status_code=500`
   - Tags: `error=true`

3. **按 Trace ID 查询**:
   - Trace ID: `4bf92f3577b34da6a3ce929d0e0e4736`

### 6.2 分析调用链

**Trace 视图**:

````text
Trace: order-processing (500ms)
├─ API Gateway (450ms)
│  ├─ User Service (50ms)
│  │  └─ PostgreSQL Query (30ms)
│  └─ Order Service (380ms)  ← 慢操作
│     ├─ Kafka Publish (300ms)  ← 瓶颈！
│     └─ Payment Service (50ms)
└─ Notification Service (20ms)
````

**分析步骤**:

1. 点击慢 Span 查看详情
2. 检查 Tags/Logs 找到错误信息
3. 查看 Span Duration 分布
4. 对比正常/异常 Trace

### 6.3 性能分析

````bash
# Jaeger UI 功能
1. Compare Traces: 对比两个 Trace
2. Deep Dependency Graph: 服务依赖关系图
3. System Architecture: 系统架构视图
4. Trace Search: 高级搜索
````

---

## 7. cargo-expand 宏展开

### 7.1 安装使用

````bash
cargo install cargo-expand

# 展开整个文件
cargo expand --lib

# 展开指定模块
cargo expand --lib api::orders

# 展开指定函数
cargo expand --lib api::orders::process_order
````

### 7.2 展开 #[instrument]

**原始代码**:

````rust
use tracing::instrument;

#[instrument(name = "process_order", skip(order))]
pub async fn process_order(order: Order) -> Result<(), anyhow::Error> {
    tracing::info!(order_id = %order.id, "Processing order");
    Ok(())
}
````

**展开后**:

````bash
cargo expand --lib api::orders::process_order
````

````rust
pub async fn process_order(order: Order) -> Result<(), anyhow::Error> {
    use tracing::__macro_support::Callsite as _;
    static CALLSITE: tracing::callsite::DefaultCallsite = {
        static META: tracing::Metadata<'static> = {
            tracing_core::metadata::Metadata::new(
                "process_order",
                "my_app::api::orders",
                tracing::Level::INFO,
                Some("src/api/orders.rs"),
                Some(10u32),
                Some("my_app::api::orders"),
                tracing_core::field::FieldSet::new(
                    &["message", "order_id"],
                    tracing_core::callsite::Identifier(&CALLSITE),
                ),
                tracing::metadata::Kind::SPAN,
            )
        };
        tracing::callsite::DefaultCallsite::new(&META)
    };
    
    let enabled = tracing::Level::INFO <= tracing::level_filters::STATIC_MAX_LEVEL
        && tracing::Level::INFO <= tracing::level_filters::LevelFilter::current()
        && {
            let interest = CALLSITE.interest();
            !interest.is_never() && CALLSITE.is_enabled(interest)
        };
    
    let __tracing_guard = if enabled {
        let meta = CALLSITE.metadata();
        Some(tracing::span::Span::new(meta, &{
            let mut valueset = tracing::field::ValueSet::new(
                meta.fields(),
                &[(&tracing::field::display(&order.id), Some("order_id"))],
            );
            valueset
        }).entered())
    } else {
        None
    };
    
    async move {
        tracing::info!(order_id = %order.id, "Processing order");
        Ok(())
    }
    .await
}
````

**用途**: 理解 `#[instrument]` 宏的实现，调试宏展开问题。

---

## 8. cargo-flamegraph 性能分析

### 8.1 安装配置

````bash
# 安装
cargo install flamegraph

# Linux 依赖
sudo apt-get install linux-tools-common linux-tools-generic

# macOS 依赖
brew install dtrace
````

### 8.2 生成火焰图

````bash
# 分析二进制
cargo flamegraph --bin my-app

# 分析测试
cargo flamegraph --test my_test

# 分析 Bench
cargo flamegraph --bench my_bench

# 输出文件: flamegraph.svg
open flamegraph.svg
````

**火焰图分析**:

````text
┌─────────────────────────────────────────┐ 100%
│         main                             │
├─────────────────────────────────────────┤
│  tokio::runtime::Runtime::block_on      │ 98%
├─────────────────────────────────────────┤
│    process_order                         │ 95%
├─────────────────────────────────────────┤
│      kafka::publish  ← 70% (瓶颈！)     │
│      payment::charge ← 20%               │
│      db::query       ← 5%                │
└─────────────────────────────────────────┘
````

---

## 9. tokio-console 异步调试

### 9.1 安装配置

````bash
# 安装 tokio-console
cargo install --locked tokio-console
````

**Cargo.toml**:

````toml
[dependencies]
tokio = { version = "1.47", features = ["full", "tracing"] }
console-subscriber = "0.4"

[profile.dev]
debug = true
````

**src/main.rs**:

````rust
fn main() {
    // 启动 console-subscriber
    console_subscriber::init();

    let rt = tokio::runtime::Runtime::new().unwrap();
    rt.block_on(async {
        tokio::spawn(async {
            loop {
                tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
                tracing::info!("Task 1");
            }
        });

        tokio::spawn(async {
            loop {
                tokio::time::sleep(tokio::time::Duration::from_secs(2)).await;
                tracing::info!("Task 2");
            }
        });

        tokio::time::sleep(tokio::time::Duration::from_secs(60)).await;
    });
}
````

### 9.2 监控 Task

````bash
# 终端 1: 运行应用
cargo run

# 终端 2: 启动 tokio-console
tokio-console
````

**tokio-console UI**:

````text
Tasks (2)
┌─────────────────────────────────────────────────────┐
│ ID   │ State   │ Name      │ Total Time │ Busy Time │
├──────┼─────────┼───────────┼────────────┼───────────┤
│ 1    │ Idle    │ task_1    │ 10.5s      │ 0.5ms     │
│ 2    │ Running │ task_2    │ 5.2s       │ 1.2ms     │
└─────────────────────────────────────────────────────┘

Resources (3)
┌─────────────────────────────────────────────────────┐
│ Type      │ Total │ Created │ Dropped │             │
├───────────┼───────┼─────────┼─────────┼─────────────┤
│ Timer     │ 2     │ 2       │ 0       │             │
│ TcpStream │ 5     │ 10      │ 5       │             │
└─────────────────────────────────────────────────────┘
````

---

## 10. 网络调试工具

### 10.1 tcpdump 抓包

````bash
# 抓取 OTLP gRPC 流量 (端口 4317)
sudo tcpdump -i any -n port 4317 -w otlp.pcap

# 抓取 HTTP 流量 (端口 8080)
sudo tcpdump -i any -n port 8080 -A

# 过滤特定 IP
sudo tcpdump -i any host 192.168.1.100

# 实时查看
sudo tcpdump -i any -n port 4317 -X
````

### 10.2 Wireshark 分析

````bash
# 打开抓包文件
wireshark otlp.pcap

# 过滤器
http.request.method == "POST"
grpc
tcp.port == 4317
````

**分析 OTLP 请求**:

1. 找到 gRPC 请求
2. 右键 → Follow → TCP Stream
3. 查看 Protobuf 数据

---

## 11. 内存调试

### 11.1 valgrind

````bash
# 安装 (Linux)
sudo apt-get install valgrind

# 内存泄漏检测
valgrind --leak-check=full --show-leak-kinds=all ./target/debug/my-app

# 输出示例
==12345== LEAK SUMMARY:
==12345==    definitely lost: 0 bytes in 0 blocks
==12345==    indirectly lost: 0 bytes in 0 blocks
==12345==      possibly lost: 0 bytes in 0 blocks
````

### 11.2 heaptrack

````bash
# 安装
sudo apt-get install heaptrack

# 运行分析
heaptrack ./target/debug/my-app

# 查看报告
heaptrack_gui heaptrack.my-app.12345.gz
````

---

## 12. 生产环境调试

### 12.1 远程调试

````bash
# 在生产服务器上启动 gdbserver
gdbserver :2345 ./my-app

# 本地连接
gdb
(gdb) target remote production-server:2345
(gdb) continue
````

### 12.2 coredump 分析

````bash
# 启用 coredump
ulimit -c unlimited

# 运行程序 (崩溃时生成 core 文件)
./my-app

# 分析 coredump
gdb ./my-app core
(gdb) backtrace
(gdb) info threads
(gdb) thread apply all bt
````

**生产环境配置**:

````toml
# Cargo.toml
[profile.release]
debug = true  # 保留调试符号
````

---

## 总结

### 核心要点

1. **交互式调试**: LLDB/GDB 适合深入调试，VS Code 提供图形化界面
2. **日志调试**: `tracing-subscriber` 是最常用的调试方式
3. **追踪可视化**: Jaeger UI 快速定位分布式系统问题
4. **性能分析**: `cargo-flamegraph` 生成火焰图找到瓶颈
5. **异步调试**: `tokio-console` 监控 Task 状态
6. **网络调试**: tcpdump + Wireshark 分析网络流量
7. **宏展开**: `cargo-expand` 理解 `#[instrument]` 实现

### 工具对比

| 工具 | 适用场景 | 优势 | 劣势 |
|------|---------|------|------|
| LLDB/GDB | 深入调试、Crash 分析 | 功能强大、精确 | 学习曲线陡峭 |
| VS Code Debugger | 日常开发调试 | 图形化、易用 | 功能有限 |
| tracing-subscriber | 生产环境、快速定位 | 非侵入、实时 | 信息有限 |
| Jaeger UI | 分布式追踪 | 可视化、全局视角 | 需要集成 |
| cargo-flamegraph | 性能优化 | 直观、准确 | 需要 root 权限 |
| tokio-console | 异步调试 | 实时监控 Task | 开销较大 |

### 最佳实践清单

- ✅ 开发环境启用调试符号 (`debug = true`)
- ✅ 使用 `RUST_LOG=debug` 查看详细日志
- ✅ 生产环境保留调试符号便于 coredump 分析
- ✅ 集成 Jaeger 快速定位分布式问题
- ✅ 使用 `cargo-expand` 理解宏展开
- ✅ 定期生成火焰图分析性能瓶颈
- ✅ 使用 `tokio-console` 监控异步 Task
- ✅ 使用条件断点减少调试时间
- ✅ tcpdump 抓包分析网络问题
- ✅ 启用 coredump 便于崩溃分析

---

**相关文档**:

- [故障排查完整指南](./01_Rust_OTLP故障排查完整指南.md)
- [Rust工具链完整配置](../31_开发工具链/01_Rust工具链完整配置.md)
- [VS Code Rust OTLP配置](../31_开发工具链/02_VS_Code_Rust_OTLP配置.md)
- [性能优化完整指南](../05_采样与性能/01_Rust_1.90_性能优化完整指南.md)
