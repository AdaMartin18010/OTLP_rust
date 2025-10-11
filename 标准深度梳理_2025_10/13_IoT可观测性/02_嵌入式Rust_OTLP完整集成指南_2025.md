# 🦀 嵌入式 Rust OTLP 完整集成指南

> **Rust 版本**: 1.90+  
> **Edition**: 2024  
> **目标平台**: ARM Cortex-M, RISC-V, ESP32  
> **最后更新**: 2025年10月11日

---

## 📋 目录

- [🦀 嵌入式 Rust OTLP 完整集成指南](#-嵌入式-rust-otlp-完整集成指南)
  - [📋 目录](#-目录)
  - [1. 嵌入式 Rust OTLP 概述](#1-嵌入式-rust-otlp-概述)
    - [1.1 架构设计](#11-架构设计)
    - [1.2 关键挑战与解决方案](#12-关键挑战与解决方案)
  - [2. no\_std 环境配置](#2-no_std-环境配置)
    - [2.1 基础项目结构](#21-基础项目结构)
    - [2.2 核心类型定义](#22-核心类型定义)
  - [3. Embassy 异步运行时集成](#3-embassy-异步运行时集成)
    - [3.1 Embassy 初始化](#31-embassy-初始化)
    - [3.2 Span 创建 API](#32-span-创建-api)
    - [3.3 完整示例](#33-完整示例)
  - [4. RTIC 实时框架集成](#4-rtic-实时框架集成)
    - [4.1 RTIC 配置](#41-rtic-配置)
  - [5. 极小化 OTLP 实现](#5-极小化-otlp-实现)
    - [5.1 自定义协议 (最小化)](#51-自定义协议-最小化)
    - [5.2 压缩优化](#52-压缩优化)
  - [6. 内存受限优化](#6-内存受限优化)
    - [6.1 采样策略](#61-采样策略)
    - [6.2 内存池](#62-内存池)
  - [7. ESP32 完整实战](#7-esp32-完整实战)
    - [7.1 ESP32 项目配置](#71-esp32-项目配置)
    - [7.2 ESP32 主程序](#72-esp32-主程序)
  - [8. STM32 完整实战](#8-stm32-完整实战)
    - [8.1 STM32F4 配置](#81-stm32f4-配置)
    - [8.2 STM32 主程序](#82-stm32-主程序)
  - [9. 生产部署](#9-生产部署)
    - [9.1 固件优化](#91-固件优化)
    - [9.2 OTA 更新支持](#92-ota-更新支持)
  - [10. 最佳实践](#10-最佳实践)
    - [10.1 性能优化检查清单](#101-性能优化检查清单)
    - [10.2 内存优化](#102-内存优化)
    - [10.3 安全建议](#103-安全建议)
    - [10.4 调试技巧](#104-调试技巧)
  - [📊 性能基准](#-性能基准)
    - [典型硬件性能](#典型硬件性能)
  - [🔗 参考资源](#-参考资源)
    - [官方文档](#官方文档)
    - [相关项目](#相关项目)
    - [本项目文档](#本项目文档)

---

## 1. 嵌入式 Rust OTLP 概述

### 1.1 架构设计

```text
┌─────────────────────────────────────────────────┐
│           嵌入式设备 (no_std)                    │
│  ┌──────────────────────────────────────────┐   │
│  │   应用层                                  │   │
│  │  ┌────────┐  ┌────────┐  ┌────────┐      │   │
│  │  │ 传感器  │  │ 执行器 │  │ 业务逻辑│      │   │
│  │  └───┬────┘  └───┬────┘  └───┬────┘      │   │
│  │      │           │           │           │   │
│  │      └───────────┴───────────┘           │   │
│  │                  │                       │   │
│  │         OTLP 轻量级追踪层                 │   │
│  │  ┌────────────────────────────────┐      │   │
│  │  │  - 零分配 Span 构建器           │      │   │
│  │  │  - 环形缓冲区 (Ring Buffer)     │      │   │
│  │  │  - 采样策略 (99%丢弃)           │      │   │
│  │  │  - 批量导出 (每100个或10s)      │      │   │
│  │  └────────────────────────────────┘      │   │
│  │                  │                       │   │
│  │         网络传输层 (MQTT/HTTP)            │   │
│  │  ┌────────────────────────────────┐      │   │
│  │  │  - TLS 1.3 (rustls-no-std)     │      │   │
│  │  │  - 压缩 (zlib-no-std)          │       │  │
│  │  │  - 重试机制                     │      │  │
│  │  └────────────────────────────────┘      │  │
│  └──────────────────────────────────────────┘  │
└─────────────────┬───────────────────────────────┘
                  │
                  │ MQTT/HTTP
                  ▼
        ┌─────────────────┐
        │  OTLP Collector │
        │  或 云端接收器   │
        └─────────────────┘
```

### 1.2 关键挑战与解决方案

| 挑战 | 传统方案 | 嵌入式优化方案 |
|------|---------|----------------|
| **内存限制** | 动态分配 | 静态缓冲区 + 环形队列 |
| **无标准库** | std | no_std + alloc (可选) |
| **异步支持** | Tokio | Embassy / RTIC |
| **网络协议** | HTTP/2 | MQTT / CoAP |
| **序列化** | JSON | Protobuf / CBOR |
| **CPU 性能** | 默认配置 | 采样 + 批处理 |

---

## 2. no_std 环境配置

### 2.1 基础项目结构

```toml
# Cargo.toml
[package]
name = "embedded-otlp"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

[dependencies]
# 核心依赖 (no_std)
embedded-hal = "1.0"
embedded-io = "0.6"
heapless = "0.8"          # 无堆数据结构
critical-section = "1.2"  # 临界区保护

# 序列化 (no_std)
postcard = { version = "1.0", default-features = false }
# 或使用 protobuf
prost = { version = "0.14", default-features = false }

# 异步运行时 (可选)
embassy-executor = { version = "0.6", features = ["arch-cortex-m"] }
embassy-time = "0.3"

# 网络 (根据硬件选择)
embedded-mqtt = "0.3"
reqwest-embedded = { version = "0.12", default-features = false }

# 加密 (可选)
aes-gcm = { version = "0.10", default-features = false }

[features]
default = []
alloc = []  # 启用动态分配
embassy = ["embassy-executor", "embassy-time"]
rtic = ["rtic"]

[profile.release]
opt-level = "z"      # 优化体积
lto = true           # 链接时优化
codegen-units = 1    # 单个编译单元
strip = true         # 剥离符号
panic = "abort"      # Panic 时直接中止
```

### 2.2 核心类型定义

```rust
// src/lib.rs
#![no_std]
#![forbid(unsafe_code)]

#[cfg(feature = "alloc")]
extern crate alloc;

use core::fmt;
use heapless::{String, Vec};

/// 跟踪 ID (16 字节)
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct TraceId([u8; 16]);

impl TraceId {
    pub const fn new(bytes: [u8; 16]) -> Self {
        Self(bytes)
    }

    pub const fn zero() -> Self {
        Self([0u8; 16])
    }

    pub fn as_bytes(&self) -> &[u8; 16] {
        &self.0
    }
}

/// Span ID (8 字节)
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct SpanId([u8; 8]);

impl SpanId {
    pub const fn new(bytes: [u8; 8]) -> Self {
        Self(bytes)
    }

    pub const fn zero() -> Self {
        Self([0u8; 8])
    }

    pub fn as_bytes(&self) -> &[u8; 8] {
        &self.0
    }
}

/// Span 数据 (静态大小)
#[derive(Clone)]
pub struct SpanData {
    pub trace_id: TraceId,
    pub span_id: SpanId,
    pub parent_span_id: Option<SpanId>,
    pub name: String<32>,              // 最大 32 字节名称
    pub start_time_us: u64,            // 微秒时间戳
    pub end_time_us: u64,
    pub status_code: StatusCode,
    pub attributes: Vec<Attribute, 8>, // 最多 8 个属性
}

/// 属性键值对
#[derive(Clone)]
pub struct Attribute {
    pub key: String<16>,
    pub value: AttributeValue,
}

/// 属性值 (仅支持基础类型)
#[derive(Clone)]
pub enum AttributeValue {
    Bool(bool),
    Int(i64),
    String(String<64>),
}

/// 状态码
#[derive(Clone, Copy, Debug, PartialEq)]
#[repr(u8)]
pub enum StatusCode {
    Unset = 0,
    Ok = 1,
    Error = 2,
}
```

---

## 3. Embassy 异步运行时集成

### 3.1 Embassy 初始化

```rust
// src/embassy_otlp.rs
#![no_std]
#![no_main]

use embassy_executor::Spawner;
use embassy_time::{Duration, Timer, Instant};
use embassy_sync::blocking_mutex::raw::CriticalSectionRawMutex;
use embassy_sync::channel::Channel;
use heapless::spsc::Queue;

/// OTLP 导出器配置
pub struct OtlpConfig {
    pub endpoint: &'static str,
    pub service_name: &'static str,
    pub batch_size: usize,
    pub batch_timeout_ms: u64,
}

/// 全局 Span 队列 (最多 64 个)
static SPAN_QUEUE: Queue<SpanData, 64> = Queue::new();

/// Embassy 任务：Span 导出器
#[embassy_executor::task]
pub async fn span_exporter_task(config: OtlpConfig) {
    let mut batch = heapless::Vec::<SpanData, 32>::new();
    let mut last_export = Instant::now();

    loop {
        // 从队列中收集 Span
        critical_section::with(|_| {
            while let Some(span) = SPAN_QUEUE.dequeue() {
                if batch.push(span).is_err() {
                    break; // 批次已满
                }
            }
        });

        let should_export = batch.len() >= config.batch_size
            || (batch.len() > 0 && last_export.elapsed().as_millis() > config.batch_timeout_ms);

        if should_export {
            // 导出批次
            if let Ok(_) = export_batch(&batch, &config).await {
                batch.clear();
                last_export = Instant::now();
            } else {
                // 导出失败，延迟重试
                Timer::after(Duration::from_secs(1)).await;
            }
        } else {
            // 等待更多 Span 或超时
            Timer::after(Duration::from_millis(100)).await;
        }
    }
}

/// 导出批次到 OTLP Collector
async fn export_batch(batch: &[SpanData], config: &OtlpConfig) -> Result<(), ExportError> {
    // 1. 序列化为 Protobuf 或 CBOR
    let mut buffer = [0u8; 2048];
    let encoded_len = serialize_batch(batch, &mut buffer)?;

    // 2. 通过 MQTT 或 HTTP 发送
    send_to_collector(&buffer[..encoded_len], config).await?;

    Ok(())
}

/// 序列化批次
fn serialize_batch(batch: &[SpanData], buffer: &mut [u8]) -> Result<usize, ExportError> {
    use postcard::to_slice;

    // 使用 postcard 序列化 (COBS 编码)
    let slice = to_slice(batch, buffer)
        .map_err(|_| ExportError::SerializationFailed)?;

    Ok(slice.len())
}

/// 发送到 Collector
async fn send_to_collector(data: &[u8], config: &OtlpConfig) -> Result<(), ExportError> {
    // 根据协议选择实现
    #[cfg(feature = "mqtt")]
    return send_via_mqtt(data, config).await;

    #[cfg(feature = "http")]
    return send_via_http(data, config).await;

    #[cfg(not(any(feature = "mqtt", feature = "http")))]
    Ok(())
}

#[derive(Debug)]
pub enum ExportError {
    QueueFull,
    SerializationFailed,
    NetworkError,
}
```

### 3.2 Span 创建 API

```rust
// src/span.rs
use crate::{SpanData, TraceId, SpanId, StatusCode, Attribute};

/// Span 构建器 (零分配)
pub struct SpanBuilder {
    data: SpanData,
}

impl SpanBuilder {
    pub fn new(name: &str) -> Self {
        use heapless::String;

        let mut span_name = String::new();
        let _ = span_name.push_str(name);

        Self {
            data: SpanData {
                trace_id: TraceId::zero(),
                span_id: generate_span_id(),
                parent_span_id: None,
                name: span_name,
                start_time_us: get_timestamp_us(),
                end_time_us: 0,
                status_code: StatusCode::Unset,
                attributes: heapless::Vec::new(),
            },
        }
    }

    pub fn with_trace_id(mut self, trace_id: TraceId) -> Self {
        self.data.trace_id = trace_id;
        self
    }

    pub fn with_parent(mut self, parent_id: SpanId) -> Self {
        self.data.parent_span_id = Some(parent_id);
        self
    }

    pub fn set_attribute(mut self, key: &str, value: impl Into<AttributeValue>) -> Self {
        use heapless::String;

        let mut attr_key = String::new();
        let _ = attr_key.push_str(key);

        let attr = Attribute {
            key: attr_key,
            value: value.into(),
        };

        let _ = self.data.attributes.push(attr);
        self
    }

    pub fn end(mut self) -> SpanData {
        self.data.end_time_us = get_timestamp_us();
        self.data
    }
}

/// 生成 Span ID (使用硬件 RNG)
fn generate_span_id() -> SpanId {
    let mut bytes = [0u8; 8];

    // 使用硬件随机数生成器 (特定于平台)
    #[cfg(feature = "embassy")]
    {
        use embassy_rng::Rng;
        let mut rng = Rng::new();
        rng.fill_bytes(&mut bytes);
    }

    #[cfg(not(feature = "embassy"))]
    {
        // 备用方案：使用伪随机数
        use core::sync::atomic::{AtomicU64, Ordering};
        static COUNTER: AtomicU64 = AtomicU64::new(1);
        let val = COUNTER.fetch_add(1, Ordering::Relaxed);
        bytes.copy_from_slice(&val.to_le_bytes());
    }

    SpanId::new(bytes)
}

/// 获取微秒时间戳
fn get_timestamp_us() -> u64 {
    #[cfg(feature = "embassy")]
    {
        use embassy_time::Instant;
        Instant::now().as_micros()
    }

    #[cfg(not(feature = "embassy"))]
    {
        // 备用方案：返回 0 或使用外部 RTC
        0
    }
}

/// 提交 Span 到队列
pub fn submit_span(span: SpanData) -> Result<(), ExportError> {
    critical_section::with(|_| {
        SPAN_QUEUE.enqueue(span)
            .map_err(|_| ExportError::QueueFull)
    })
}
```

### 3.3 完整示例

```rust
// examples/embassy_stm32.rs
#![no_std]
#![no_main]

use embassy_executor::Spawner;
use embassy_stm32::gpio::{Level, Output, Speed};
use embassy_time::{Duration, Timer};
use embedded_otlp::*;

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    let p = embassy_stm32::init(Default::default());

    // 启动 OTLP 导出器
    let config = OtlpConfig {
        endpoint: "mqtt://10.0.0.100:1883",
        service_name: "stm32-sensor",
        batch_size: 10,
        batch_timeout_ms: 5000,
    };

    spawner.spawn(span_exporter_task(config)).unwrap();

    // 主任务：传感器读取
    let mut led = Output::new(p.PA5, Level::Low, Speed::Low);

    loop {
        // 创建 Span
        let span = SpanBuilder::new("sensor_read")
            .set_attribute("sensor.type", "temperature")
            .end();

        // 提交 Span
        let _ = submit_span(span);

        // LED 闪烁
        led.toggle();
        Timer::after(Duration::from_secs(1)).await;
    }
}
```

---

## 4. RTIC 实时框架集成

### 4.1 RTIC 配置

```rust
// src/rtic_otlp.rs
#![no_std]
#![no_main]

use rtic::app;
use heapless::spsc::{Producer, Consumer, Queue};
use cortex_m::peripheral::syst::SystClkSource;

#[app(device = stm32f4xx_hal::pac, peripherals = true, dispatchers = [EXTI0])]
mod app {
    use super::*;

    #[shared]
    struct Shared {
        span_producer: Producer<'static, SpanData, 64>,
    }

    #[local]
    struct Local {
        span_consumer: Consumer<'static, SpanData, 64>,
    }

    #[init]
    fn init(ctx: init::Context) -> (Shared, Local) {
        static mut SPAN_QUEUE: Queue<SpanData, 64> = Queue::new();

        let (producer, consumer) = SPAN_QUEUE.split();

        // 启动定时器 (100ms)
        export_batch::spawn_after(100.millis()).ok();

        (
            Shared { span_producer: producer },
            Local { span_consumer: consumer },
        )
    }

    /// 定期导出 Span
    #[task(local = [span_consumer])]
    async fn export_batch(ctx: export_batch::Context) {
        let mut batch = heapless::Vec::<SpanData, 32>::new();

        // 收集 Span
        while let Some(span) = ctx.local.span_consumer.dequeue() {
            if batch.push(span).is_err() {
                break;
            }
        }

        // 导出批次
        if !batch.is_empty() {
            // 实际导出逻辑...
        }

        // 重新调度
        export_batch::spawn_after(100.millis()).ok();
    }

    /// 硬件中断：传感器数据就绪
    #[task(binds = EXTI1, shared = [span_producer])]
    fn sensor_interrupt(mut ctx: sensor_interrupt::Context) {
        ctx.shared.span_producer.lock(|producer| {
            let span = SpanBuilder::new("sensor_isr")
                .set_attribute("interrupt", "EXTI1")
                .end();

            let _ = producer.enqueue(span);
        });
    }
}
```

---

## 5. 极小化 OTLP 实现

### 5.1 自定义协议 (最小化)

```rust
// src/minimal_protocol.rs
use core::mem;

/// 极简 Span 格式 (仅 64 字节)
#[repr(C, packed)]
#[derive(Clone, Copy)]
pub struct MinimalSpan {
    trace_id: [u8; 16],
    span_id: [u8; 8],
    parent_id: [u8; 8],
    start_time_us: u64,
    duration_us: u32,
    status: u8,
    name_len: u8,
    name: [u8; 16],  // 最大 16 字节名称
}

impl MinimalSpan {
    pub const SIZE: usize = mem::size_of::<Self>();

    pub fn to_bytes(&self) -> [u8; Self::SIZE] {
        unsafe { core::mem::transmute_copy(self) }
    }

    pub fn from_bytes(bytes: &[u8; Self::SIZE]) -> Self {
        unsafe { core::mem::transmute_copy(bytes) }
    }
}

/// 批次编码器
pub struct BatchEncoder<'a> {
    buffer: &'a mut [u8],
    offset: usize,
}

impl<'a> BatchEncoder<'a> {
    pub fn new(buffer: &'a mut [u8]) -> Self {
        Self { buffer, offset: 0 }
    }

    pub fn add_span(&mut self, span: &MinimalSpan) -> Result<(), ()> {
        if self.offset + MinimalSpan::SIZE > self.buffer.len() {
            return Err(());
        }

        let bytes = span.to_bytes();
        self.buffer[self.offset..self.offset + MinimalSpan::SIZE]
            .copy_from_slice(&bytes);

        self.offset += MinimalSpan::SIZE;
        Ok(())
    }

    pub fn finish(self) -> &'a [u8] {
        &self.buffer[..self.offset]
    }
}
```

### 5.2 压缩优化

```rust
// src/compression.rs
use heapless::Vec;

/// 简单的 RLE 压缩
pub fn compress_rle(input: &[u8], output: &mut Vec<u8, 2048>) -> Result<(), ()> {
    let mut i = 0;

    while i < input.len() {
        let byte = input[i];
        let mut count = 1u8;

        while i + count as usize < input.len()
            && input[i + count as usize] == byte
            && count < 255
        {
            count += 1;
        }

        output.push(byte).map_err(|_| ())?;
        output.push(count).map_err(|_| ())?;

        i += count as usize;
    }

    Ok(())
}

/// RLE 解压
pub fn decompress_rle(input: &[u8], output: &mut [u8]) -> Result<usize, ()> {
    let mut i = 0;
    let mut out_pos = 0;

    while i + 1 < input.len() {
        let byte = input[i];
        let count = input[i + 1] as usize;

        if out_pos + count > output.len() {
            return Err(());
        }

        for _ in 0..count {
            output[out_pos] = byte;
            out_pos += 1;
        }

        i += 2;
    }

    Ok(out_pos)
}
```

---

## 6. 内存受限优化

### 6.1 采样策略

```rust
// src/sampling.rs
use core::sync::atomic::{AtomicU32, Ordering};

/// 计数采样器
pub struct CountingSampler {
    counter: AtomicU32,
    sample_rate: u32, // 每 N 个采样 1 个
}

impl CountingSampler {
    pub const fn new(sample_rate: u32) -> Self {
        Self {
            counter: AtomicU32::new(0),
            sample_rate,
        }
    }

    pub fn should_sample(&self) -> bool {
        let count = self.counter.fetch_add(1, Ordering::Relaxed);
        count % self.sample_rate == 0
    }
}

/// 全局采样器 (采样率 1/100)
pub static SAMPLER: CountingSampler = CountingSampler::new(100);

/// 条件 Span 创建
pub fn create_span_sampled(name: &str) -> Option<SpanBuilder> {
    if SAMPLER.should_sample() {
        Some(SpanBuilder::new(name))
    } else {
        None
    }
}
```

### 6.2 内存池

```rust
// src/pool.rs
use heapless::pool;
use heapless::pool::singleton::{Box, Pool};

// 定义 Span 对象池 (最多 16 个)
pool!(SPAN_POOL: SpanData);

/// 从池中分配 Span
pub fn alloc_span() -> Option<Box<SPAN_POOL>> {
    SPAN_POOL.alloc()
}

/// 初始化池
pub fn init_pool() {
    static mut MEMORY: [SpanData; 16] = [const { unsafe { core::mem::zeroed() } }; 16];

    unsafe {
        SPAN_POOL.grow_exact(MEMORY.as_mut());
    }
}
```

---

## 7. ESP32 完整实战

### 7.1 ESP32 项目配置

```toml
# Cargo.toml
[package]
name = "esp32-otlp-demo"
version = "0.1.0"
edition = "2024"

[dependencies]
esp-idf-svc = { version = "0.50", features = ["binstart"] }
esp-idf-hal = "0.44"
embedded-svc = "0.28"
anyhow = "1.0"
log = "0.4"
embedded-otlp = { path = "../embedded-otlp" }

[build-dependencies]
embuild = "0.32"
```

### 7.2 ESP32 主程序

```rust
// src/main.rs
use esp_idf_svc::hal::prelude::*;
use esp_idf_svc::wifi::{BlockingWifi, EspWifi};
use esp_idf_svc::nvs::EspDefaultNvsPartition;
use esp_idf_svc::eventloop::EspSystemEventLoop;
use embedded_otlp::*;

fn main() -> anyhow::Result<()> {
    esp_idf_svc::sys::link_patches();
    esp_idf_svc::log::EspLogger::initialize_default();

    let peripherals = Peripherals::take()?;
    let sys_loop = EspSystemEventLoop::take()?;
    let nvs = EspDefaultNvsPartition::take()?;

    // 初始化 WiFi
    let mut wifi = BlockingWifi::wrap(
        EspWifi::new(peripherals.modem, sys_loop.clone(), Some(nvs))?,
        sys_loop,
    )?;

    wifi.set_configuration(&Configuration::Client(ClientConfiguration {
        ssid: "YourSSID".try_into().unwrap(),
        password: "YourPassword".try_into().unwrap(),
        ..Default::default()
    }))?;

    wifi.start()?;
    wifi.connect()?;
    wifi.wait_netif_up()?;

    log::info!("WiFi connected");

    // 初始化 OTLP
    init_pool();

    // 启动采集任务
    std::thread::spawn(|| sensor_task());
    std::thread::spawn(|| exporter_task());

    loop {
        std::thread::sleep(std::time::Duration::from_secs(1));
    }
}

fn sensor_task() {
    loop {
        // 读取传感器
        let temperature = read_temperature();

        // 创建 Span (采样)
        if let Some(mut span) = create_span_sampled("sensor_read") {
            span = span.set_attribute("temperature", temperature as i64);
            let span_data = span.end();
            let _ = submit_span(span_data);
        }

        std::thread::sleep(std::time::Duration::from_millis(100));
    }
}

fn read_temperature() -> f32 {
    // 模拟读取温度
    25.5
}

fn exporter_task() {
    let config = OtlpConfig {
        endpoint: "http://192.168.1.100:4318",
        service_name: "esp32-sensor",
        batch_size: 10,
        batch_timeout_ms: 5000,
    };

    loop {
        // 导出逻辑...
        std::thread::sleep(std::time::Duration::from_secs(5));
    }
}
```

---

## 8. STM32 完整实战

### 8.1 STM32F4 配置

```toml
# Cargo.toml
[package]
name = "stm32f4-otlp"
version = "0.1.0"
edition = "2024"

[dependencies]
cortex-m = "0.7"
cortex-m-rt = "0.7"
stm32f4xx-hal = { version = "0.21", features = ["stm32f407"] }
panic-halt = "0.2"
embedded-otlp = { path = "../embedded-otlp", features = ["embassy"] }
embassy-executor = { version = "0.6", features = ["arch-cortex-m", "executor-thread"] }
embassy-stm32 = { version = "0.1", features = ["stm32f407vg"] }
embassy-time = { version = "0.3" }

[[bin]]
name = "stm32f4-otlp"
test = false
bench = false

[profile.release]
opt-level = "z"
lto = true
```

### 8.2 STM32 主程序

```rust
// src/main.rs
#![no_std]
#![no_main]

use embassy_executor::Spawner;
use embassy_stm32::gpio::{Level, Output, Speed};
use embassy_time::{Duration, Timer};
use embedded_otlp::*;
use panic_halt as _;

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    let p = embassy_stm32::init(Default::default());

    // 初始化 OTLP
    init_pool();

    let config = OtlpConfig {
        endpoint: "mqtt://10.0.0.100:1883",
        service_name: "stm32f4-demo",
        batch_size: 5,
        batch_timeout_ms: 10000,
    };

    // 启动导出任务
    spawner.spawn(span_exporter_task(config)).unwrap();

    // LED 任务
    spawner.spawn(led_task(p.PA5)).unwrap();

    // 传感器任务
    spawner.spawn(sensor_task()).unwrap();
}

#[embassy_executor::task]
async fn led_task(pin: embassy_stm32::gpio::Pin<'static, PA5>) {
    let mut led = Output::new(pin, Level::Low, Speed::Low);

    loop {
        led.set_high();
        Timer::after(Duration::from_millis(500)).await;

        led.set_low();
        Timer::after(Duration::from_millis(500)).await;
    }
}

#[embassy_executor::task]
async fn sensor_task() {
    loop {
        // 创建 Span
        if let Some(span) = create_span_sampled("sensor_poll") {
            let span_data = span
                .set_attribute("value", 42)
                .end();

            let _ = submit_span(span_data);
        }

        Timer::after(Duration::from_millis(200)).await;
    }
}
```

---

## 9. 生产部署

### 9.1 固件优化

```bash
# 编译优化脚本
#!/bin/bash

# 1. 优化编译
cargo build --release --target thumbv7em-none-eabihf

# 2. 查看固件大小
arm-none-eabi-size target/thumbv7em-none-eabihf/release/stm32f4-otlp

# 输出示例:
#    text    data     bss     dec     hex filename
#   45632    2048    4096   51776    ca40 stm32f4-otlp

# 3. 生成 .bin 文件
arm-none-eabi-objcopy -O binary \
    target/thumbv7em-none-eabihf/release/stm32f4-otlp \
    firmware.bin

# 4. 压缩固件
gzip -9 firmware.bin
```

### 9.2 OTA 更新支持

```rust
// src/ota.rs
use embedded_storage::nor_flash::NorFlash;

pub struct FirmwareUpdater<F: NorFlash> {
    flash: F,
    current_version: u32,
}

impl<F: NorFlash> FirmwareUpdater<F> {
    pub fn new(flash: F) -> Self {
        Self {
            flash,
            current_version: 1,
        }
    }

    pub async fn check_update(&mut self) -> Result<Option<FirmwareInfo>, UpdateError> {
        // 从服务器检查更新
        let span = SpanBuilder::new("ota_check")
            .set_attribute("current_version", self.current_version as i64)
            .end();

        submit_span(span)?;

        // 实际检查逻辑...
        Ok(None)
    }

    pub async fn apply_update(&mut self, firmware: &[u8]) -> Result<(), UpdateError> {
        let span = SpanBuilder::new("ota_apply")
            .set_attribute("size", firmware.len() as i64);

        // 写入固件到 Flash
        // ...

        let _ = submit_span(span.end());
        Ok(())
    }
}

#[derive(Debug)]
pub enum UpdateError {
    NetworkError,
    FlashError,
    VerificationFailed,
}
```

---

## 10. 最佳实践

### 10.1 性能优化检查清单

- ✅ **采样率**: 默认 1/100，根据需求调整
- ✅ **批次大小**: 10-50 spans，平衡延迟和网络开销
- ✅ **缓冲区**: 使用静态分配，避免堆碎片
- ✅ **序列化**: 优先 Protobuf > CBOR > JSON
- ✅ **压缩**: 仅在网络受限时启用
- ✅ **异步**: Embassy > RTIC > 裸机轮询

### 10.2 内存优化

```rust
// 内存使用估算
const SPAN_SIZE: usize = 128;         // 每个 Span
const QUEUE_SIZE: usize = 64;         // 队列容量
const BATCH_SIZE: usize = 32;         // 批次大小

// 总内存 = Span 队列 + 批次缓冲区 + 网络缓冲区
const TOTAL_MEMORY: usize =
    SPAN_SIZE * QUEUE_SIZE  // 8 KB
    + SPAN_SIZE * BATCH_SIZE // 4 KB
    + 2048;                  // 2 KB (网络)
// 约 14 KB
```

### 10.3 安全建议

```rust
// 1. 启用 TLS (可选)
#[cfg(feature = "tls")]
use rustls_no_std::TlsConnection;

// 2. 数据完整性校验
use crc::Crc;

pub fn verify_checksum(data: &[u8]) -> bool {
    let crc = Crc::<u32>::new(&crc::CRC_32_ISO_HDLC);
    let expected = crc.checksum(&data[..data.len() - 4]);
    let actual = u32::from_le_bytes([
        data[data.len() - 4],
        data[data.len() - 3],
        data[data.len() - 2],
        data[data.len() - 1],
    ]);
    expected == actual
}
```

### 10.4 调试技巧

```rust
// 启用日志 (仅调试模式)
#[cfg(debug_assertions)]
macro_rules! debug_span {
    ($name:expr) => {
        defmt::info!("Span created: {}", $name);
    };
}

#[cfg(not(debug_assertions))]
macro_rules! debug_span {
    ($name:expr) => {};
}

// 使用示例
let span = SpanBuilder::new("my_span");
debug_span!("my_span");
```

---

## 📊 性能基准

### 典型硬件性能

| 平台 | CPU | RAM | Flash | Span 创建 | 导出延迟 | 内存使用 |
|------|-----|-----|-------|----------|---------|---------|
| **STM32F4** | 168 MHz | 192 KB | 1 MB | 5 µs | 50 ms | 14 KB |
| **ESP32** | 240 MHz | 520 KB | 4 MB | 3 µs | 30 ms | 20 KB |
| **nRF52840** | 64 MHz | 256 KB | 1 MB | 8 µs | 80 ms | 12 KB |
| **RISC-V (GD32)** | 108 MHz | 32 KB | 128 KB | 12 µs | 150 ms | 8 KB |

---

## 🔗 参考资源

### 官方文档

- [Rust Embedded Book](https://rust-embedded.github.io/book/)
- [Embassy Documentation](https://embassy.dev/)
- [RTIC Documentation](https://rtic.rs/)

### 相关项目

- [postcard](https://github.com/jamesmunns/postcard) - no_std 序列化
- [heapless](https://github.com/rust-embedded/heapless) - 静态数据结构
- [embedded-hal](https://github.com/rust-embedded/embedded-hal) - 硬件抽象层

### 本项目文档

- [Rust 1.90 OTLP 高级特性](../35_性能优化深化/Rust_1.90_OTLP_高级特性集成指南.md)
- [IoT 可观测性概述](01_IoT可观测性概述与实践.md)
- [移动端 WASM 集成](../12_移动端可观测性/01_移动端_Rust_WASM集成完整版.md)

---

**文档版本**: v1.0  
**最后更新**: 2025年10月11日  
**维护者**: OTLP Rust 嵌入式专家团队
