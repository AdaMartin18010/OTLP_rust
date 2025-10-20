# Cilium eBPF - Rust + OTLP 网络可观测性完整指南

## 📋 目录

- [Cilium eBPF - Rust + OTLP 网络可观测性完整指南](#cilium-ebpf---rust--otlp-网络可观测性完整指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [什么是 eBPF?](#什么是-ebpf)
    - [什么是 Cilium?](#什么是-cilium)
    - [为什么使用 Rust + eBPF?](#为什么使用-rust--ebpf)
    - [OTLP 集成价值](#otlp-集成价值)
  - [核心概念](#核心概念)
    - [1. eBPF 架构](#1-ebpf-架构)
    - [2. Cilium 架构](#2-cilium-架构)
  - [环境准备](#环境准备)
    - [1. 安装依赖](#1-安装依赖)
    - [2. 安装 Cilium](#2-安装-cilium)
    - [3. 验证安装](#3-验证安装)
  - [Rust eBPF 开发](#rust-ebpf-开发)
    - [1. 项目初始化](#1-项目初始化)
    - [2. eBPF 程序 (Kernel Space)](#2-ebpf-程序-kernel-space)
    - [3. 用户空间程序 (User Space)](#3-用户空间程序-user-space)
  - [网络追踪](#网络追踪)
    - [1. TCP 连接追踪](#1-tcp-连接追踪)
    - [2. HTTP 请求追踪](#2-http-请求追踪)
    - [3. DNS 查询追踪](#3-dns-查询追踪)
  - [OTLP 集成](#otlp-集成)
    - [1. eBPF 数据导出到 OTLP](#1-ebpf-数据导出到-otlp)
    - [2. 网络指标聚合](#2-网络指标聚合)
  - [Cilium Hubble 集成](#cilium-hubble-集成)
    - [1. 启用 Hubble](#1-启用-hubble)
    - [2. Hubble Metrics 导出](#2-hubble-metrics-导出)
    - [3. Hubble Relay + OTLP](#3-hubble-relay--otlp)
  - [高级特性](#高级特性)
    - [1. 网络策略追踪](#1-网络策略追踪)
    - [2. Service Mesh 加速](#2-service-mesh-加速)
    - [3. L7 可观测性](#3-l7-可观测性)
  - [性能优化](#性能优化)
    - [1. eBPF Map 优化](#1-ebpf-map-优化)
    - [2. 批量处理](#2-批量处理)
    - [3. 性能对比](#3-性能对比)
  - [监控与告警](#监控与告警)
    - [1. Cilium Metrics](#1-cilium-metrics)
    - [2. eBPF 程序监控](#2-ebpf-程序监控)
  - [完整示例](#完整示例)
    - [1. 端到端网络追踪](#1-端到端网络追踪)
    - [2. Kubernetes 集成](#2-kubernetes-集成)
  - [故障排查](#故障排查)
    - [1. 常见问题](#1-常见问题)
    - [2. 调试工具](#2-调试工具)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [技术对比](#技术对比)
    - [下一步](#下一步)
  - [参考资料](#参考资料)

---

## 概述

### 什么是 eBPF?

**eBPF** (extended Berkeley Packet Filter) 是 Linux 内核的革命性技术:

```text
User Space
    ↕ syscall
Kernel Space
    ├─ eBPF Programs (Sandboxed)
    ├─ eBPF Maps (Data Exchange)
    └─ eBPF Verifier (Safety Check)
```

**特性**:

- **安全**: 内核验证器确保程序安全
- **高性能**: 内核态执行,零拷贝
- **可观测性**: 无侵入式监控
- **动态加载**: 无需重启内核

### 什么是 Cilium?

**Cilium** 是基于 eBPF 的云原生网络和安全解决方案:

```text
┌─────────────────────────────────┐
│      Cilium Agent (DaemonSet)   │
├─────────────────────────────────┤
│ Network Policy │ Load Balancing │
│ Service Mesh   │ Observability  │
└──────────┬──────────────────────┘
           │ eBPF
┌──────────▼──────────────────────┐
│      Linux Kernel (eBPF)        │
└─────────────────────────────────┘
```

### 为什么使用 Rust + eBPF?

| 优势 | 说明 |
|------|------|
| **内存安全** | Rust 编译期检查,避免内核崩溃 |
| **性能** | 零成本抽象,与 C 性能相当 |
| **Aya 框架** | 纯 Rust eBPF,无需 LLVM |
| **生态** | 与 Rust 生态无缝集成 |

### OTLP 集成价值

```text
eBPF (Kernel) → User Space (Rust) → OTLP → Observability Backend
    ↓               ↓                  ↓
 网络事件        结构化追踪          可视化分析
```

---

## 核心概念

### 1. eBPF 架构

```text
┌─────────────────────────────────────────┐
│           User Space                     │
│  ┌─────────────┐      ┌──────────────┐ │
│  │ eBPF Loader │ ←──→ │ eBPF Maps    │ │
│  └─────────────┘      └──────────────┘ │
└───────────┬─────────────────────────────┘
            │ bpf() syscall
┌───────────▼─────────────────────────────┐
│         Kernel Space                     │
│  ┌─────────────┐      ┌──────────────┐ │
│  │  Verifier   │ ───→ │ eBPF Program │ │
│  └─────────────┘      └──────┬───────┘ │
│                               ↓          │
│                        ┌──────────────┐ │
│                        │  Hook Point  │ │
│                        └──────────────┘ │
└─────────────────────────────────────────┘
```

**Hook Points**:

- `kprobe`: 内核函数入口
- `kretprobe`: 内核函数返回
- `tracepoint`: 静态跟踪点
- `XDP`: 网卡驱动层
- `TC`: 流量控制层
- `socket`: Socket 层

### 2. Cilium 架构

```text
┌─────────────────────────────────────────┐
│          Kubernetes Cluster             │
│  ┌─────────┐  ┌─────────┐  ┌─────────┐ │
│  │  Pod A  │  │  Pod B  │  │  Pod C  │ │
│  └────┬────┘  └────┬────┘  └────┬────┘ │
└───────┼────────────┼─────────────┼──────┘
        │            │             │
┌───────▼────────────▼─────────────▼──────┐
│          Cilium eBPF Datapath           │
│  ┌─────────────────────────────────┐   │
│  │  Network Policy  │  Service LB  │   │
│  │  Encryption      │  Observability│  │
│  └─────────────────────────────────┘   │
└─────────────────────────────────────────┘
```

---

## 环境准备

### 1. 安装依赖

```bash
# Ubuntu/Debian
sudo apt-get update
sudo apt-get install -y \
    clang llvm libelf-dev libssl-dev \
    linux-headers-$(uname -r) \
    libbpf-dev bpftool

# 安装 Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# 安装 bpf-linker (Aya 需要)
cargo install bpf-linker
```

### 2. 安装 Cilium

```bash
# 使用 Cilium CLI
CILIUM_CLI_VERSION=$(curl -s https://raw.githubusercontent.com/cilium/cilium-cli/main/stable.txt)
curl -L --fail --remote-name-all https://github.com/cilium/cilium-cli/releases/download/${CILIUM_CLI_VERSION}/cilium-linux-amd64.tar.gz
sudo tar xzvfC cilium-linux-amd64.tar.gz /usr/local/bin
rm cilium-linux-amd64.tar.gz

# 安装 Cilium 到 Kubernetes
cilium install \
  --version 1.15.3 \
  --set prometheus.enabled=true \
  --set operator.prometheus.enabled=true \
  --set hubble.enabled=true \
  --set hubble.metrics.enabled="{dns,drop,tcp,flow,port-distribution,icmp,httpV2:exemplars=true;labelsContext=source_ip\,source_namespace\,source_workload\,destination_ip\,destination_namespace\,destination_workload\,traffic_direction}"
```

### 3. 验证安装

```bash
# 检查 Cilium 状态
cilium status --wait

# 检查 eBPF 程序
sudo bpftool prog list

# 检查 eBPF Maps
sudo bpftool map list
```

---

## Rust eBPF 开发

### 1. 项目初始化

```toml
# Cargo.toml
[package]
name = "cilium-otlp-tracer"
version = "0.1.0"
edition = "2021"

[dependencies]
aya = "0.12"
aya-log = "0.2"
tokio = { version = "1.37", features = ["full"] }
anyhow = "1.0"
log = "0.4"
env_logger = "0.11"

# OTLP
opentelemetry = "0.30"
opentelemetry-otlp = "0.30"
opentelemetry_sdk = { version = "0.30", features = ["rt-tokio"] }
tracing = "0.1"
tracing-subscriber = "0.3"
tracing-opentelemetry = "0.31"

# 网络
bytes = "1.5"
pnet = "0.34"

[build-dependencies]
aya-gen = "0.12"

[[bin]]
name = "cilium-otlp-tracer"
path = "src/main.rs"

# eBPF 程序
[workspace]
members = ["cilium-otlp-tracer-ebpf"]

[profile.release]
opt-level = 3
lto = true
codegen-units = 1
```

```toml
# cilium-otlp-tracer-ebpf/Cargo.toml
[package]
name = "cilium-otlp-tracer-ebpf"
version = "0.1.0"
edition = "2021"

[dependencies]
aya-ebpf = "0.1"
aya-log-ebpf = "0.1"

[lib]
crate-type = ["cdylib"]

[profile.release]
opt-level = 3
```

### 2. eBPF 程序 (Kernel Space)

```rust
// cilium-otlp-tracer-ebpf/src/lib.rs
#![no_std]
#![no_main]

use aya_ebpf::{
    bindings::xdp_action,
    macros::{xdp, map, kprobe},
    maps::{HashMap, PerfEventArray},
    programs::{XdpContext, ProbeContext},
};
use aya_log_ebpf::info;

// 数据结构
#[repr(C)]
#[derive(Clone, Copy)]
pub struct NetworkEvent {
    pub src_ip: u32,
    pub dst_ip: u32,
    pub src_port: u16,
    pub dst_port: u16,
    pub protocol: u8,
    pub bytes: u64,
    pub timestamp_ns: u64,
}

#[map]
static EVENTS: PerfEventArray<NetworkEvent> = PerfEventArray::with_max_entries(1024, 0);

#[map]
static CONNECTION_MAP: HashMap<u64, NetworkEvent> = HashMap::with_max_entries(10240, 0);

/// XDP 程序 - 网络包捕获
#[xdp]
pub fn xdp_network_tracer(ctx: XdpContext) -> u32 {
    match try_xdp_network_tracer(ctx) {
        Ok(ret) => ret,
        Err(_) => xdp_action::XDP_PASS,
    }
}

fn try_xdp_network_tracer(ctx: XdpContext) -> Result<u32, ()> {
    let ethhdr_size = core::mem::size_of::<ethhdr>();
    let iphdr_size = core::mem::size_of::<iphdr>();
    
    // 解析以太网头
    let eth = ptr_at(&ctx, 0)?;
    if unsafe { (*eth).h_proto } != (ETH_P_IP as u16).to_be() {
        return Ok(xdp_action::XDP_PASS);
    }
    
    // 解析 IP 头
    let ip = ptr_at::<iphdr>(&ctx, ethhdr_size)?;
    let src_ip = unsafe { (*ip).saddr };
    let dst_ip = unsafe { (*ip).daddr };
    let protocol = unsafe { (*ip).protocol };
    
    // 只处理 TCP
    if protocol != IPPROTO_TCP {
        return Ok(xdp_action::XDP_PASS);
    }
    
    // 解析 TCP 头
    let tcp = ptr_at::<tcphdr>(&ctx, ethhdr_size + iphdr_size)?;
    let src_port = unsafe { u16::from_be((*tcp).source) };
    let dst_port = unsafe { u16::from_be((*tcp).dest) };
    
    // 创建事件
    let event = NetworkEvent {
        src_ip,
        dst_ip,
        src_port,
        dst_port,
        protocol,
        bytes: (ctx.data_end() - ctx.data()) as u64,
        timestamp_ns: unsafe { bpf_ktime_get_ns() },
    };
    
    // 发送到用户空间
    EVENTS.output(&ctx, &event, 0);
    
    info!(&ctx, "Captured packet: {}:{} -> {}:{}", 
          src_ip, src_port, dst_ip, dst_port);
    
    Ok(xdp_action::XDP_PASS)
}

/// Kprobe - TCP 连接追踪
#[kprobe]
pub fn tcp_connect(ctx: ProbeContext) -> u32 {
    match try_tcp_connect(ctx) {
        Ok(ret) => ret,
        Err(_) => 0,
    }
}

fn try_tcp_connect(ctx: ProbeContext) -> Result<u32, ()> {
    let sock: *const sock = ctx.arg(0).ok_or(())?;
    
    // 提取连接信息
    let src_port = unsafe { (*sock).sk_num };
    let dst_port = unsafe { (*sock).sk_dport };
    
    info!(&ctx, "TCP connect: src_port={}, dst_port={}", src_port, dst_port);
    
    Ok(0)
}

// 辅助函数
#[inline(always)]
fn ptr_at<T>(ctx: &XdpContext, offset: usize) -> Result<*const T, ()> {
    let start = ctx.data();
    let end = ctx.data_end();
    let len = core::mem::size_of::<T>();

    if start + offset + len > end {
        return Err(());
    }

    Ok((start + offset) as *const T)
}

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    unsafe { core::hint::unreachable_unchecked() }
}

// Linux 内核类型定义
const ETH_P_IP: u32 = 0x0800;
const IPPROTO_TCP: u8 = 6;

#[repr(C)]
struct ethhdr {
    h_dest: [u8; 6],
    h_source: [u8; 6],
    h_proto: u16,
}

#[repr(C)]
struct iphdr {
    _bitfield_1: u8,
    tos: u8,
    tot_len: u16,
    id: u16,
    frag_off: u16,
    ttl: u8,
    protocol: u8,
    check: u16,
    saddr: u32,
    daddr: u32,
}

#[repr(C)]
struct tcphdr {
    source: u16,
    dest: u16,
    seq: u32,
    ack_seq: u32,
    _bitfield_1: u16,
    window: u16,
    check: u16,
    urg_ptr: u16,
}

#[repr(C)]
struct sock {
    sk_num: u16,
    sk_dport: u16,
    // ... 简化版
}

extern "C" {
    fn bpf_ktime_get_ns() -> u64;
}
```

### 3. 用户空间程序 (User Space)

```rust
// src/main.rs
use aya::{
    maps::perf::AsyncPerfEventArray,
    programs::{Xdp, XdpFlags, KProbe},
    util::online_cpus,
    Ebpf,
};
use aya_log::EbpfLogger;
use bytes::BytesMut;
use log::{info, warn};
use tokio::task;
use anyhow::Result;

use opentelemetry::{
    global,
    trace::{Tracer, TracerProvider as _},
    KeyValue,
};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{
    trace::{self, RandomIdGenerator, Sampler},
    Resource,
};
use tracing::{info_span, Instrument};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

#[repr(C)]
#[derive(Debug, Clone, Copy)]
struct NetworkEvent {
    src_ip: u32,
    dst_ip: u32,
    src_port: u16,
    dst_port: u16,
    protocol: u8,
    bytes: u64,
    timestamp_ns: u64,
}

#[tokio::main]
async fn main() -> Result<()> {
    env_logger::init();
    
    // 初始化 OTLP
    init_otlp()?;
    
    info!("Loading eBPF program...");
    
    // 加载 eBPF 程序
    let mut ebpf = Ebpf::load(include_bytes_aligned!(
        "../../target/bpfel-unknown-none/release/cilium-otlp-tracer-ebpf"
    ))?;
    
    // 加载日志
    if let Err(e) = EbpfLogger::init(&mut ebpf) {
        warn!("Failed to initialize eBPF logger: {}", e);
    }
    
    // 附加 XDP 程序
    let program: &mut Xdp = ebpf.program_mut("xdp_network_tracer").unwrap().try_into()?;
    program.load()?;
    program.attach("eth0", XdpFlags::default())?;
    
    info!("XDP program attached to eth0");
    
    // 附加 Kprobe
    let program: &mut KProbe = ebpf.program_mut("tcp_connect").unwrap().try_into()?;
    program.load()?;
    program.attach("tcp_connect", 0)?;
    
    info!("Kprobe attached to tcp_connect");
    
    // 处理事件
    let mut perf_array = AsyncPerfEventArray::try_from(ebpf.take_map("EVENTS").unwrap())?;
    
    for cpu_id in online_cpus()? {
        let mut buf = perf_array.open(cpu_id, None)?;
        
        task::spawn(async move {
            let mut buffers = (0..10)
                .map(|_| BytesMut::with_capacity(1024))
                .collect::<Vec<_>>();
            
            loop {
                let events = buf.read_events(&mut buffers).await.unwrap();
                
                for buf in buffers.iter_mut().take(events.read) {
                    let event = unsafe { &*(buf.as_ptr() as *const NetworkEvent) };
                    process_network_event(event).await;
                }
            }
        });
    }
    
    info!("Listening for events... Press Ctrl-C to exit");
    tokio::signal::ctrl_c().await?;
    
    Ok(())
}

async fn process_network_event(event: &NetworkEvent) {
    let tracer = global::tracer("network-tracer");
    
    let span = tracer
        .span_builder("network.packet")
        .with_attributes(vec![
            KeyValue::new("net.src.ip", format!("{}", ipv4_to_string(event.src_ip))),
            KeyValue::new("net.src.port", event.src_port as i64),
            KeyValue::new("net.dst.ip", format!("{}", ipv4_to_string(event.dst_ip))),
            KeyValue::new("net.dst.port", event.dst_port as i64),
            KeyValue::new("net.protocol", event.protocol as i64),
            KeyValue::new("net.bytes", event.bytes as i64),
        ])
        .start(&tracer);
    
    let _guard = span.end();
}

fn ipv4_to_string(ip: u32) -> String {
    format!("{}.{}.{}.{}",
        ip & 0xFF,
        (ip >> 8) & 0xFF,
        (ip >> 16) & 0xFF,
        (ip >> 24) & 0xFF,
    )
}

fn init_otlp() -> Result<()> {
    let tracer = opentelemetry_otlp::new_pipeline()
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
                    KeyValue::new("service.name", "cilium-otlp-tracer"),
                ])),
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    let telemetry = tracing_opentelemetry::layer().with_tracer(tracer);
    
    tracing_subscriber::registry()
        .with(telemetry)
        .with(tracing_subscriber::fmt::layer())
        .init();
    
    Ok(())
}
```

---

## 网络追踪

### 1. TCP 连接追踪

```rust
// src/tcp_tracer.rs
use aya::maps::HashMap as AyaHashMap;
use std::net::Ipv4Addr;

#[derive(Debug, Clone)]
pub struct TcpConnection {
    pub src_addr: Ipv4Addr,
    pub dst_addr: Ipv4Addr,
    pub src_port: u16,
    pub dst_port: u16,
    pub state: TcpState,
    pub bytes_sent: u64,
    pub bytes_received: u64,
}

#[derive(Debug, Clone, Copy)]
pub enum TcpState {
    Established,
    SynSent,
    SynReceived,
    FinWait1,
    FinWait2,
    TimeWait,
    Close,
    CloseWait,
    LastAck,
    Listen,
    Closing,
}

pub async fn track_tcp_connections(
    map: &mut AyaHashMap<&mut aya::maps::MapData, u64, TcpConnection>,
) -> Result<()> {
    let tracer = global::tracer("tcp-tracer");
    
    for item in map.iter() {
        let (key, conn) = item?;
        
        let span = tracer
            .span_builder("tcp.connection")
            .with_attributes(vec![
                KeyValue::new("net.peer.ip", conn.dst_addr.to_string()),
                KeyValue::new("net.peer.port", conn.dst_port as i64),
                KeyValue::new("net.host.ip", conn.src_addr.to_string()),
                KeyValue::new("net.host.port", conn.src_port as i64),
                KeyValue::new("net.transport", "tcp"),
                KeyValue::new("tcp.state", format!("{:?}", conn.state)),
            ])
            .start(&tracer);
        
        // 记录指标
        global::meter("tcp-tracer")
            .u64_counter("tcp.bytes.sent")
            .init()
            .add(conn.bytes_sent, &[]);
        
        global::meter("tcp-tracer")
            .u64_counter("tcp.bytes.received")
            .init()
            .add(conn.bytes_received, &[]);
        
        span.end();
    }
    
    Ok(())
}
```

### 2. HTTP 请求追踪

```rust
// cilium-otlp-tracer-ebpf/src/http_tracer.rs (eBPF 部分)
use aya_ebpf::{
    macros::uprobe,
    programs::ProbeContext,
};

#[repr(C)]
pub struct HttpRequest {
    pub method: [u8; 16],
    pub path: [u8; 256],
    pub status_code: u16,
    pub duration_ns: u64,
}

#[uprobe]
pub fn http_request_start(ctx: ProbeContext) -> u32 {
    // 捕获 HTTP 请求开始
    0
}

#[uretprobe]
pub fn http_request_end(ctx: ProbeContext) -> u32 {
    // 捕获 HTTP 请求结束
    0
}
```

```rust
// src/http_tracer.rs (用户空间)
pub async fn trace_http_request(req: &HttpRequest) {
    let tracer = global::tracer("http-tracer");
    
    let method = std::str::from_utf8(&req.method)
        .unwrap_or("UNKNOWN")
        .trim_matches('\0');
    let path = std::str::from_utf8(&req.path)
        .unwrap_or("/")
        .trim_matches('\0');
    
    let span = tracer
        .span_builder(format!("HTTP {}", method))
        .with_kind(opentelemetry::trace::SpanKind::Server)
        .with_attributes(vec![
            KeyValue::new("http.method", method.to_string()),
            KeyValue::new("http.target", path.to_string()),
            KeyValue::new("http.status_code", req.status_code as i64),
            KeyValue::new("http.duration_ns", req.duration_ns as i64),
        ])
        .start(&tracer);
    
    span.end();
}
```

### 3. DNS 查询追踪

```rust
// src/dns_tracer.rs
#[repr(C)]
pub struct DnsQuery {
    pub query_name: [u8; 256],
    pub query_type: u16,
    pub response_code: u8,
    pub latency_ns: u64,
}

pub async fn trace_dns_query(query: &DnsQuery) {
    let tracer = global::tracer("dns-tracer");
    
    let query_name = std::str::from_utf8(&query.query_name)
        .unwrap_or("unknown")
        .trim_matches('\0');
    
    let span = tracer
        .span_builder("dns.query")
        .with_attributes(vec![
            KeyValue::new("dns.question.name", query_name.to_string()),
            KeyValue::new("dns.question.type", query.query_type as i64),
            KeyValue::new("dns.response_code", query.response_code as i64),
            KeyValue::new("dns.latency_ns", query.latency_ns as i64),
        ])
        .start(&tracer);
    
    span.end();
}
```

---

## OTLP 集成

### 1. eBPF 数据导出到 OTLP

```rust
// src/otlp_exporter.rs
use opentelemetry::trace::{Span, Tracer};
use tokio::sync::mpsc;

pub struct OtlpExporter {
    tx: mpsc::Sender<NetworkEvent>,
}

impl OtlpExporter {
    pub fn new() -> (Self, mpsc::Receiver<NetworkEvent>) {
        let (tx, rx) = mpsc::channel(1024);
        (Self { tx }, rx)
    }
    
    pub async fn export(&self, event: NetworkEvent) -> Result<()> {
        self.tx.send(event).await?;
        Ok(())
    }
}

pub async fn otlp_export_worker(mut rx: mpsc::Receiver<NetworkEvent>) {
    let tracer = global::tracer("network-exporter");
    
    while let Some(event) = rx.recv().await {
        let span = tracer
            .span_builder("network.flow")
            .with_start_time(
                std::time::UNIX_EPOCH + std::time::Duration::from_nanos(event.timestamp_ns)
            )
            .with_attributes(vec![
                KeyValue::new("net.src.ip", ipv4_to_string(event.src_ip)),
                KeyValue::new("net.src.port", event.src_port as i64),
                KeyValue::new("net.dst.ip", ipv4_to_string(event.dst_ip)),
                KeyValue::new("net.dst.port", event.dst_port as i64),
                KeyValue::new("net.protocol", protocol_name(event.protocol)),
                KeyValue::new("net.bytes", event.bytes as i64),
            ])
            .start(&tracer);
        
        span.end();
    }
}

fn protocol_name(proto: u8) -> &'static str {
    match proto {
        1 => "icmp",
        6 => "tcp",
        17 => "udp",
        _ => "unknown",
    }
}
```

### 2. 网络指标聚合

```rust
// src/metrics.rs
use opentelemetry::metrics::{Counter, Histogram};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

pub struct NetworkMetrics {
    packets_total: Counter<u64>,
    bytes_total: Counter<u64>,
    latency_histogram: Histogram<f64>,
    connections_active: Arc<Mutex<HashMap<u64, TcpConnection>>>,
}

impl NetworkMetrics {
    pub fn new() -> Self {
        let meter = global::meter("network-metrics");
        
        Self {
            packets_total: meter
                .u64_counter("network.packets.total")
                .with_description("Total number of network packets")
                .init(),
            bytes_total: meter
                .u64_counter("network.bytes.total")
                .with_description("Total number of bytes transferred")
                .init(),
            latency_histogram: meter
                .f64_histogram("network.latency")
                .with_description("Network latency distribution")
                .with_unit("ms")
                .init(),
            connections_active: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    pub fn record_packet(&self, event: &NetworkEvent) {
        let attributes = vec![
            KeyValue::new("protocol", protocol_name(event.protocol)),
            KeyValue::new("direction", if event.src_port < 1024 { "inbound" } else { "outbound" }),
        ];
        
        self.packets_total.add(1, &attributes);
        self.bytes_total.add(event.bytes, &attributes);
    }
    
    pub fn record_latency(&self, latency_ms: f64, protocol: &str) {
        self.latency_histogram.record(
            latency_ms,
            &[KeyValue::new("protocol", protocol.to_string())],
        );
    }
}
```

---

## Cilium Hubble 集成

### 1. 启用 Hubble

```bash
# 启用 Hubble UI
cilium hubble enable --ui

# 端口转发 Hubble UI
cilium hubble ui

# 或使用 kubectl
kubectl port-forward -n kube-system svc/hubble-ui 12000:80
```

### 2. Hubble Metrics 导出

```yaml
# hubble-metrics-configmap.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: hubble-metrics-config
  namespace: kube-system
data:
  metrics.yaml: |
    metrics:
      - drop
      - tcp
      - flow
      - port-distribution
      - icmp
      - httpV2:exemplars=true;labelsContext=source_ip,source_namespace,source_workload,destination_ip,destination_namespace,destination_workload,traffic_direction
    
    # 导出到 Prometheus
    enablePrometheus: true
    prometheusServeAddr: ":9965"
    
    # 导出到 OpenTelemetry
    enableOpenTelemetry: true
    openTelemetryEndpoint: "otel-collector:4317"
```

### 3. Hubble Relay + OTLP

```rust
// src/hubble_relay.rs
use hubble_relay::observer::Observer;
use opentelemetry::trace::{Span, Tracer};

pub struct HubbleOtlpBridge {
    observer: Observer,
    tracer: global::BoxedTracer,
}

impl HubbleOtlpBridge {
    pub async fn new(hubble_endpoint: &str) -> Result<Self> {
        let observer = Observer::connect(hubble_endpoint).await?;
        let tracer = global::tracer("hubble-bridge");
        
        Ok(Self { observer, tracer })
    }
    
    pub async fn stream_flows(&mut self) -> Result<()> {
        let mut stream = self.observer.get_flows().await?;
        
        while let Some(flow) = stream.next().await {
            let flow = flow?;
            self.export_flow_to_otlp(&flow).await?;
        }
        
        Ok(())
    }
    
    async fn export_flow_to_otlp(&self, flow: &Flow) -> Result<()> {
        let span = self.tracer
            .span_builder("hubble.flow")
            .with_attributes(vec![
                KeyValue::new("k8s.namespace", flow.source.namespace.clone()),
                KeyValue::new("k8s.pod", flow.source.pod_name.clone()),
                KeyValue::new("k8s.service", flow.destination.service_name.clone()),
                KeyValue::new("network.protocol.name", flow.l4.protocol.to_string()),
                KeyValue::new("network.verdict", flow.verdict.to_string()),
            ])
            .start(&self.tracer);
        
        span.end();
        Ok(())
    }
}
```

---

## 高级特性

### 1. 网络策略追踪

```yaml
# network-policy-traced.yaml
apiVersion: cilium.io/v2
kind: CiliumNetworkPolicy
metadata:
  name: traced-policy
  namespace: default
spec:
  endpointSelector:
    matchLabels:
      app: backend
  
  ingress:
    - fromEndpoints:
      - matchLabels:
          app: frontend
      toPorts:
      - ports:
        - port: "8080"
          protocol: TCP
      # 启用追踪
      metadata:
        trace: enabled
```

### 2. Service Mesh 加速

```yaml
# cilium-service-mesh.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: cilium-config
  namespace: kube-system
data:
  enable-envoy-config: "true"
  kube-proxy-replacement: "true"
  enable-l7-proxy: "true"
  
  # eBPF-based Service Mesh
  enable-bpf-masquerade: "true"
  enable-host-reachable-services: "true"
  
  # OTLP 配置
  enable-hubble: "true"
  hubble-export-file-max-backups: "10"
  hubble-export-file-compress: "true"
  hubble-metrics-server: ":9965"
```

### 3. L7 可观测性

```rust
// L7 (HTTP/gRPC) 追踪
pub async fn trace_l7_traffic() -> Result<()> {
    let tracer = global::tracer("l7-tracer");
    
    // 解析 HTTP/gRPC 协议
    let span = tracer
        .span_builder("http.request")
        .with_kind(opentelemetry::trace::SpanKind::Server)
        .with_attributes(vec![
            KeyValue::new("http.method", "GET"),
            KeyValue::new("http.url", "/api/users"),
            KeyValue::new("http.status_code", 200),
            KeyValue::new("http.user_agent", "curl/7.68.0"),
        ])
        .start(&tracer);
    
    span.end();
    Ok(())
}
```

---

## 性能优化

### 1. eBPF Map 优化

```rust
// 使用 LRU Map
#[map]
static LRU_CACHE: LruHashMap<u64, NetworkEvent> = 
    LruHashMap::with_max_entries(65536, 0);

// 使用 Per-CPU Array (零锁)
#[map]
static PER_CPU_STATS: PerCpuArray<NetworkStats> = 
    PerCpuArray::with_max_entries(1, 0);
```

### 2. 批量处理

```rust
pub async fn batch_export_events(
    events: Vec<NetworkEvent>,
) -> Result<()> {
    let tracer = global::tracer("batch-exporter");
    
    let batch_span = tracer
        .span_builder("batch.export")
        .with_attributes(vec![
            KeyValue::new("batch.size", events.len() as i64),
        ])
        .start(&tracer);
    
    for chunk in events.chunks(100) {
        // 批量导出
        for event in chunk {
            export_event(event).await?;
        }
    }
    
    batch_span.end();
    Ok(())
}
```

### 3. 性能对比

| 方案 | CPU 开销 | 延迟 | 吞吐量 |
|------|---------|------|-------|
| **eBPF (Cilium)** | ~1% | <1μs | 10M pps |
| **iptables** | ~5-10% | ~10μs | 1M pps |
| **User Space (BPF)** | ~15% | ~50μs | 500K pps |
| **Sidecar Proxy** | ~20% | ~100μs | 200K pps |

---

## 监控与告警

### 1. Cilium Metrics

```promql
# 数据包丢弃率
rate(cilium_drop_count_total[5m])

# 网络策略丢弃
rate(cilium_policy_verdict_total{verdict="denied"}[5m])

# eBPF 程序执行时间
histogram_quantile(0.99, 
  rate(cilium_bpf_map_ops_duration_seconds_bucket[5m])
)

# Hubble 流量速率
rate(hubble_flows_processed_total[5m])
```

### 2. eBPF 程序监控

```bash
# 查看 eBPF 程序统计
sudo bpftool prog show

# 查看 Map 使用情况
sudo bpftool map show

# Perf 分析
sudo perf record -a -g -F 99 sleep 10
sudo perf script | flamegraph.pl > flame.svg
```

---

## 完整示例

### 1. 端到端网络追踪

(见上文完整代码)

### 2. Kubernetes 集成

```yaml
# daemonset.yaml
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: cilium-otlp-tracer
  namespace: kube-system
spec:
  selector:
    matchLabels:
      app: cilium-otlp-tracer
  template:
    metadata:
      labels:
        app: cilium-otlp-tracer
    spec:
      hostNetwork: true
      hostPID: true
      containers:
      - name: tracer
        image: myregistry/cilium-otlp-tracer:latest
        securityContext:
          privileged: true
          capabilities:
            add:
              - SYS_ADMIN
              - SYS_RESOURCE
              - NET_ADMIN
        volumeMounts:
        - name: sys
          mountPath: /sys
        - name: bpf
          mountPath: /sys/fs/bpf
        env:
        - name: OTEL_EXPORTER_OTLP_ENDPOINT
          value: "http://otel-collector:4317"
        - name: RUST_LOG
          value: "info"
      volumes:
      - name: sys
        hostPath:
          path: /sys
      - name: bpf
        hostPath:
          path: /sys/fs/bpf
```

---

## 故障排查

### 1. 常见问题

```bash
# eBPF 程序加载失败
sudo dmesg | grep bpf
sudo bpftool prog load --debug

# Verifier 错误
# 解决: 简化 eBPF 程序逻辑,减少指令数

# Map 满
sudo bpftool map dump id <map_id>
# 解决: 增大 max_entries 或使用 LRU Map
```

### 2. 调试工具

```bash
# bpftrace - 动态追踪
sudo bpftrace -e 'tracepoint:net:netif_rx { @[comm] = count(); }'

# tcpdump + eBPF
sudo tcpdump -i any -w trace.pcap

# Cilium Monitor
cilium monitor --type trace

# Hubble Observe
hubble observe --protocol tcp --port 80
```

---

## 总结

### 核心要点

1. **eBPF**: 内核态高性能网络监控
2. **Cilium**: 云原生网络和安全平台
3. **Rust**: 安全高效的 eBPF 开发语言
4. **OTLP**: 统一可观测性数据格式
5. **Hubble**: Cilium 的可观测性层

### 技术对比

| 技术 | 优势 | 劣势 |
|------|------|------|
| **eBPF** | 极高性能,内核态 | 学习曲线陡峭 |
| **Sidecar** | 易于部署 | 性能开销大 |
| **Agent** | 灵活性高 | 需要额外部署 |

### 下一步

- **Cilium Service Mesh**: 无 Sidecar 的服务网格
- **Tetragon**: Cilium 的运行时安全
- **Pixie**: eBPF-based 自动化可观测性

---

## 参考资料

- [Cilium 官方文档](https://docs.cilium.io/)
- [eBPF 官方网站](https://ebpf.io/)
- [Aya Book](https://aya-rs.dev/book/)
- [Hubble 文档](https://docs.cilium.io/en/stable/gettingstarted/hubble/)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-11  
**Rust 版本**: 1.90+  
**Cilium 版本**: 1.15+  
**Aya 版本**: 0.12+  
**OpenTelemetry**: 0.30+
