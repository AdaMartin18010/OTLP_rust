# 🌐 IoT 设备 Rust 完整追踪

> **Rust 版本**: 1.90+ (stable/nightly)  
> **OpenTelemetry**: 0.31.0 (标准) / 自定义实现 (no_std)  
> **目标平台**: ARM Cortex-M, RISC-V, ESP32  
> **最后更新**: 2025年10月10日

---

## 📋 目录

- [🌐 IoT 设备 Rust 完整追踪](#-iot-设备-rust-完整追踪)
  - [📋 目录](#-目录)
  - [1. IoT 可观测性概述](#1-iot-可观测性概述)
    - [1.1 IoT 设备面临的挑战](#11-iot-设备面临的挑战)
    - [1.2 IoT OTLP 架构](#12-iot-otlp-架构)
  - [2. 嵌入式 Rust 生态](#2-嵌入式-rust-生态)
    - [2.1 核心库](#21-核心库)
    - [2.2 目标平台配置](#22-目标平台配置)
  - [3. no\_std 环境下的 OTLP](#3-no_std-环境下的-otlp)
    - [3.1 最小化 Span 数据结构](#31-最小化-span-数据结构)
    - [3.2 环形缓冲区 Span 存储](#32-环形缓冲区-span-存储)
    - [3.3 序列化与压缩](#33-序列化与压缩)
  - [4. 轻量级追踪实现](#4-轻量级追踪实现)
    - [4.1 基础 Tracer](#41-基础-tracer)
    - [4.2 RAII Span Guard](#42-raii-span-guard)
  - [5. 网络传输优化](#5-网络传输优化)
    - [5.1 CoAP 传输 (轻量级)](#51-coap-传输-轻量级)
    - [5.2 MQTT 传输](#52-mqtt-传输)
  - [6. 电源与资源管理](#6-电源与资源管理)
    - [6.1 动态采样](#61-动态采样)
    - [6.2 批量上报策略](#62-批量上报策略)
  - [7. 实战案例](#7-实战案例)
    - [7.1 温度传感器监控](#71-温度传感器监控)
  - [🔗 参考资源](#-参考资源)

---

## 1. IoT 可观测性概述

### 1.1 IoT 设备面临的挑战

| 挑战 | 说明 | 解决方案 |
|------|------|---------|
| **资源受限** | RAM < 256KB, Flash < 1MB | 最小化数据结构、零拷贝 |
| **低功耗** | 电池供电，需长期运行 | 批量处理、按需采样 |
| **网络不稳定** | 间歇性连接、低带宽 | 本地缓存、压缩传输 |
| **实时性要求** | 快速响应、低延迟 | 轻量级处理、优先级队列 |
| **安全要求** | 数据加密、安全传输 | TLS/DTLS、轻量级加密 |

### 1.2 IoT OTLP 架构

```text
┌─────────────────────────────────────────────┐
│            IoT Device (Rust)                │
│  ┌────────────┐  ┌──────────────────┐       │
│  │ Sensors    │→ │ Tracing Layer    │       │
│  └────────────┘  │ (Lightweight)    │       │
│                  └──────────────────┘       │
│                          ↓                  │
│  ┌────────────────────────────────────┐     │
│  │  Local Buffer (Ring Buffer)        │     │
│  │  - Span Queue (固定大小)            │     │
│  │  - Compression (可选)              │     │
│  └────────────────────────────────────┘     │
│                          ↓                  │
│  ┌────────────────────────────────────┐     │
│  │  Network Layer                     │     │
│  │  - CoAP / MQTT / HTTP              │     │
│  │  - TLS (可选)                      │     │
│  └────────────────────────────────────┘     │
└─────────────────────────────────────────────┘
                    ↓
┌─────────────────────────────────────────────┐
│        Edge Gateway / Cloud Collector       │
└─────────────────────────────────────────────┘
```

---

## 2. 嵌入式 Rust 生态

### 2.1 核心库

```toml
[dependencies]
# 核心库 (no_std)
embedded-hal = "1.0"
cortex-m = "0.7"
cortex-m-rt = "0.7"

# 异步运行时
embassy-executor = { version = "0.5", features = ["nightly"] }
embassy-time = "0.3"
embassy-net = { version = "0.4", features = ["tcp", "udp"] }

# 序列化 (no_std 兼容)
heapless = "0.8"
serde = { version = "1.0", default-features = false, features = ["derive"] }
postcard = "1.0"  # 轻量级序列化

# 网络协议
coap-lite = { version = "0.11", default-features = false }
embedded-mqtt = "0.9"

# 可选: 标准库功能 (如果平台支持)
# std 需要根据目标平台决定
```

### 2.2 目标平台配置

```toml
# .cargo/config.toml

# ARM Cortex-M4F (例如: STM32F4)
[target.thumbv7em-none-eabihf]
runner = "probe-rs run --chip STM32F407VGTx"
rustflags = [
  "-C", "link-arg=-Tlink.x",
  "-C", "link-arg=--nmagic",
]

# ESP32 (RISC-V)
[target.riscv32imc-esp-espidf]
linker = "ldproxy"
rustflags = ["-C", "default-linker-libraries"]

# 优化配置
[profile.release]
opt-level = "z"      # 最小化代码大小
lto = "fat"          # 链接时优化
codegen-units = 1    # 单一代码生成单元
debug = false
strip = true
```

---

## 3. no_std 环境下的 OTLP

### 3.1 最小化 Span 数据结构

```rust
#![no_std]

use heapless::{String, Vec};
use core::fmt;

/// 轻量级 TraceId (16 字节)
#[derive(Copy, Clone, Debug)]
pub struct TraceId([u8; 16]);

impl TraceId {
    pub fn new() -> Self {
        // 使用硬件 RNG 生成
        let mut bytes = [0u8; 16];
        // 假设有 RNG 硬件
        // rng.fill_bytes(&mut bytes);
        Self(bytes)
    }
    
    pub fn to_hex(&self) -> String<32> {
        let mut s = String::new();
        for byte in &self.0 {
            let _ = write!(&mut s, "{:02x}", byte);
        }
        s
    }
}

/// 轻量级 SpanId (8 字节)
#[derive(Copy, Clone, Debug)]
pub struct SpanId([u8; 8]);

impl SpanId {
    pub fn new() -> Self {
        let mut bytes = [0u8; 8];
        // rng.fill_bytes(&mut bytes);
        Self(bytes)
    }
}

/// 最小化 Span 数据 (固定大小)
#[derive(Debug)]
pub struct MicroSpan {
    pub trace_id: TraceId,
    pub span_id: SpanId,
    pub parent_span_id: Option<SpanId>,
    pub name: String<32>,  // 最大 32 字符
    pub start_time_us: u64,  // 微秒时间戳
    pub duration_us: u32,    // 持续时间 (微秒)
    pub attributes: Vec<(String<16>, i32), 4>,  // 最多 4 个属性
}

impl MicroSpan {
    pub fn new(name: &str) -> Self {
        Self {
            trace_id: TraceId::new(),
            span_id: SpanId::new(),
            parent_span_id: None,
            name: String::from(name),
            start_time_us: get_timestamp_us(),
            duration_us: 0,
            attributes: Vec::new(),
        }
    }
    
    pub fn end(&mut self) {
        self.duration_us = (get_timestamp_us() - self.start_time_us) as u32;
    }
    
    pub fn set_attribute(&mut self, key: &str, value: i32) {
        if self.attributes.len() < 4 {
            let _ = self.attributes.push((String::from(key), value));
        }
    }
}

// 获取时间戳（需要根据平台实现）
fn get_timestamp_us() -> u64 {
    // 使用硬件计时器
    // timer::get_microseconds()
    0
}
```

### 3.2 环形缓冲区 Span 存储

```rust
use heapless::spsc::{Queue, Producer, Consumer};

/// Span 缓冲区 (固定大小，零分配)
pub struct SpanBuffer {
    queue: Queue<MicroSpan, 32>,  // 最多存储 32 个 Span
}

impl SpanBuffer {
    pub const fn new() -> Self {
        Self {
            queue: Queue::new(),
        }
    }
    
    pub fn push(&mut self, span: MicroSpan) -> Result<(), MicroSpan> {
        self.queue.enqueue(span)
    }
    
    pub fn pop(&mut self) -> Option<MicroSpan> {
        self.queue.dequeue()
    }
    
    pub fn is_full(&self) -> bool {
        self.queue.is_full()
    }
    
    pub fn len(&self) -> usize {
        self.queue.len()
    }
}

/// 全局 Span 缓冲区（使用静态变量）
static mut SPAN_BUFFER: SpanBuffer = SpanBuffer::new();

pub fn record_span(span: MicroSpan) {
    unsafe {
        if let Err(_) = SPAN_BUFFER.push(span) {
            // 缓冲区满，丢弃最旧的 Span
            let _ = SPAN_BUFFER.pop();
            let _ = SPAN_BUFFER.push(span);
        }
    }
}
```

### 3.3 序列化与压缩

```rust
use postcard::{to_slice, from_bytes};
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize, Debug)]
pub struct CompactSpan {
    pub tid: [u8; 16],      // TraceId
    pub sid: [u8; 8],       // SpanId
    pub name: String<32>,
    pub start: u64,         // 开始时间
    pub dur: u32,           // 持续时间
    pub attrs: Vec<(String<16>, i32), 4>,
}

impl From<MicroSpan> for CompactSpan {
    fn from(span: MicroSpan) -> Self {
        Self {
            tid: span.trace_id.0,
            sid: span.span_id.0,
            name: span.name,
            start: span.start_time_us,
            dur: span.duration_us,
            attrs: span.attributes,
        }
    }
}

/// 序列化 Span 到字节数组
pub fn serialize_span(span: &MicroSpan) -> Result<Vec<u8, 128>, postcard::Error> {
    let compact: CompactSpan = span.clone().into();
    let mut buf = [0u8; 128];
    to_slice(&compact, &mut buf).map(|slice| {
        let mut vec = Vec::new();
        vec.extend_from_slice(slice).unwrap();
        vec
    })
}
```

---

## 4. 轻量级追踪实现

### 4.1 基础 Tracer

```rust
#![no_std]

use core::cell::RefCell;
use critical_section::Mutex;

/// 轻量级 Tracer
pub struct MicroTracer {
    buffer: Mutex<RefCell<SpanBuffer>>,
}

impl MicroTracer {
    pub const fn new() -> Self {
        Self {
            buffer: Mutex::new(RefCell::new(SpanBuffer::new())),
        }
    }
    
    /// 开始一个 Span
    pub fn start_span(&self, name: &str) -> MicroSpan {
        MicroSpan::new(name)
    }
    
    /// 结束并记录 Span
    pub fn end_span(&self, mut span: MicroSpan) {
        span.end();
        
        critical_section::with(|cs| {
            let mut buffer = self.buffer.borrow_ref_mut(cs);
            let _ = buffer.push(span);
        });
    }
    
    /// 导出所有 Span
    pub fn export_spans<F>(&self, mut callback: F) -> usize
    where
        F: FnMut(MicroSpan),
    {
        let mut count = 0;
        
        critical_section::with(|cs| {
            let mut buffer = self.buffer.borrow_ref_mut(cs);
            while let Some(span) = buffer.pop() {
                callback(span);
                count += 1;
            }
        });
        
        count
    }
}

/// 全局 Tracer 实例
static TRACER: MicroTracer = MicroTracer::new();

pub fn global_tracer() -> &'static MicroTracer {
    &TRACER
}
```

### 4.2 RAII Span Guard

```rust
/// RAII Span Guard - 自动结束 Span
pub struct SpanGuard {
    span: Option<MicroSpan>,
}

impl SpanGuard {
    pub fn new(name: &str) -> Self {
        let span = global_tracer().start_span(name);
        Self { span: Some(span) }
    }
    
    pub fn set_attribute(&mut self, key: &str, value: i32) {
        if let Some(span) = &mut self.span {
            span.set_attribute(key, value);
        }
    }
}

impl Drop for SpanGuard {
    fn drop(&mut self) {
        if let Some(span) = self.span.take() {
            global_tracer().end_span(span);
        }
    }
}

// 使用示例
fn sensor_read() -> i32 {
    let _span = SpanGuard::new("sensor_read");
    
    // 读取传感器
    let value = 42;
    
    value  // Span 在函数结束时自动记录
}
```

---

## 5. 网络传输优化

### 5.1 CoAP 传输 (轻量级)

```rust
use coap_lite::{CoapRequest, RequestType, Packet};
use embassy_net::udp::UdpSocket;

/// CoAP Exporter
pub struct CoapExporter<'a> {
    socket: UdpSocket<'a>,
    server_addr: SocketAddr,
}

impl<'a> CoapExporter<'a> {
    pub fn new(socket: UdpSocket<'a>, server_addr: SocketAddr) -> Self {
        Self { socket, server_addr }
    }
    
    /// 导出 Span
    pub async fn export(&mut self, span: &MicroSpan) -> Result<(), Error> {
        // 序列化 Span
        let payload = serialize_span(span)?;
        
        // 构建 CoAP 请求
        let mut request = CoapRequest::new(RequestType::Post);
        request.set_path("/v1/traces");
        request.message.payload = payload.to_vec();
        
        // 发送
        let packet = request.message.to_bytes()?;
        self.socket.send_to(&packet, self.server_addr).await?;
        
        Ok(())
    }
    
    /// 批量导出
    pub async fn export_batch(&mut self, spans: &[MicroSpan]) -> Result<(), Error> {
        // 批量序列化
        let mut batch_buf = Vec::<u8, 512>::new();
        
        for span in spans {
            let span_bytes = serialize_span(span)?;
            batch_buf.extend_from_slice(&span_bytes)?;
        }
        
        // 发送
        let mut request = CoapRequest::new(RequestType::Post);
        request.set_path("/v1/traces/batch");
        request.message.payload = batch_buf.to_vec();
        
        let packet = request.message.to_bytes()?;
        self.socket.send_to(&packet, self.server_addr).await?;
        
        Ok(())
    }
}
```

### 5.2 MQTT 传输

```rust
use embedded_mqtt::{Client, QoS};

/// MQTT Exporter
pub struct MqttExporter<'a, T> {
    client: Client<'a, T>,
    topic: &'static str,
}

impl<'a, T> MqttExporter<'a, T>
where
    T: embedded_io_async::Read + embedded_io_async::Write,
{
    pub fn new(client: Client<'a, T>, topic: &'static str) -> Self {
        Self { client, topic }
    }
    
    pub async fn export(&mut self, span: &MicroSpan) -> Result<(), Error> {
        let payload = serialize_span(span)?;
        
        self.client
            .publish(self.topic, &payload, QoS::AtLeastOnce)
            .await?;
        
        Ok(())
    }
}
```

---

## 6. 电源与资源管理

### 6.1 动态采样

```rust
/// 智能采样器 - 根据电池电量调整
pub struct AdaptiveSampler {
    battery_level: u8,  // 0-100%
}

impl AdaptiveSampler {
    pub fn new() -> Self {
        Self { battery_level: 100 }
    }
    
    pub fn update_battery(&mut self, level: u8) {
        self.battery_level = level;
    }
    
    /// 应该采样吗？
    pub fn should_sample(&self) -> bool {
        match self.battery_level {
            80..=100 => true,           // 100% 采样
            50..=79 => self.sample_50(),  // 50% 采样
            20..=49 => self.sample_20(),  // 20% 采样
            _ => self.sample_5(),         // 5% 采样
        }
    }
    
    fn sample_50(&self) -> bool {
        get_random_u8() % 2 == 0
    }
    
    fn sample_20(&self) -> bool {
        get_random_u8() % 5 == 0
    }
    
    fn sample_5(&self) -> bool {
        get_random_u8() % 20 == 0
    }
}

fn get_random_u8() -> u8 {
    // 使用硬件 RNG
    42
}
```

### 6.2 批量上报策略

```rust
use embassy_time::{Duration, Timer};

/// 批量上报任务
#[embassy_executor::task]
pub async fn batch_export_task(mut exporter: CoapExporter<'static>) {
    let mut interval = Timer::after(Duration::from_secs(60));
    
    loop {
        interval.await;
        
        // 收集所有 Span
        let mut spans = Vec::<MicroSpan, 32>::new();
        
        global_tracer().export_spans(|span| {
            let _ = spans.push(span);
        });
        
        // 批量发送
        if !spans.is_empty() {
            let _ = exporter.export_batch(&spans).await;
        }
    }
}
```

---

## 7. 实战案例

### 7.1 温度传感器监控

```rust
#![no_std]
#![no_main]

use embassy_executor::Spawner;
use embassy_time::{Duration, Timer};

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    // 初始化硬件
    let p = embassy_stm32::init(Default::default());
    
    // 启动批量导出任务
    spawner.spawn(batch_export_task()).unwrap();
    
    // 主循环
    loop {
        read_and_report_temperature().await;
        Timer::after(Duration::from_secs(10)).await;
    }
}

async fn read_and_report_temperature() {
    let mut span = SpanGuard::new("read_temp");
    
    // 读取温度
    let temp = read_temperature_sensor();
    span.set_attribute("temp", temp);
    
    // Span 自动结束
}

fn read_temperature_sensor() -> i32 {
    // 模拟读取
    25
}
```

---

## 🔗 参考资源

- [Embedded Rust Book](https://doc.rust-lang.org/embedded-book/)
- [Embassy Documentation](https://embassy.dev/)
- [Rust OTLP 快速入门](../33_教程与示例/01_Rust_OTLP_30分钟快速入门.md)

---

**文档版本**: v1.0  
**创建日期**: 2025年10月10日  
**维护者**: OTLP Rust 文档团队

---

[🏠 返回主目录](../README.md) | [📱 IoT 可观测性](./README.md)
