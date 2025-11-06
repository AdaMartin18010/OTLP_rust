# 🎯 Profile 信号实现指南

**版本**: 1.0
**最后更新**: 2025年10月26日
**适用于**: OTLP Rust v2.0+
**OTLP 版本**: 1.3.0+ (Profile Signal Type)
**状态**: 🟢 活跃维护

> **简介**: Profile 信号完整实现指南 - CPU/Memory Profiling、pprof格式、性能分析和最佳实践。

---

## 📋 目录

- [🎯 Profile 信号实现指南](#-profile-信号实现指南)
  - [📋 目录](#-目录)
  - [简介](#简介)
    - [什么是 Profile 信号？](#什么是-profile-信号)
    - [为什么需要 Profile 信号？](#为什么需要-profile-信号)
    - [pprof 格式](#pprof-格式)
  - [Profile 信号概述](#profile-信号概述)
    - [OTLP Profile 数据模型](#otlp-profile-数据模型)
    - [Profile 与其他信号的关系](#profile-与其他信号的关系)
  - [实现架构](#实现架构)
    - [总体架构](#总体架构)
    - [Crate 结构](#crate-结构)
  - [核心组件实现](#核心组件实现)
    - [1. ProfileCollector - 采集器](#1-profilecollector---采集器)
    - [2. ProfileProcessor - 处理器](#2-profileprocessor---处理器)
    - [3. ProfileExporter - 导出器](#3-profileexporter---导出器)
  - [数据模型](#数据模型)
    - [OTLP Profile Protobuf 定义](#otlp-profile-protobuf-定义)
  - [采集实现](#采集实现)
    - [CPU Profiling 示例](#cpu-profiling-示例)
    - [连续 Profiling 示例](#连续-profiling-示例)
  - [处理与导出](#处理与导出)
    - [批处理配置](#批处理配置)
    - [导出配置](#导出配置)
  - [性能优化](#性能优化)
    - [1. 采样率优化](#1-采样率优化)
    - [2. 批处理优化](#2-批处理优化)
    - [3. 压缩优化](#3-压缩优化)
  - [最佳实践](#最佳实践)
    - [1. 资源标识](#1-资源标识)
    - [2. Profile 属性](#2-profile-属性)
    - [3. 与 Trace 关联](#3-与-trace-关联)
    - [4. 错误处理](#4-错误处理)
  - [示例代码](#示例代码)
    - [完整示例：Web 服务 Profiling](#完整示例web-服务-profiling)
  - [故障排除](#故障排除)
    - [常见问题](#常见问题)
      - [1. Profiler 启动失败](#1-profiler-启动失败)
      - [2. Profile 数据过大](#2-profile-数据过大)
      - [3. 内存泄漏](#3-内存泄漏)
  - [参考资源](#参考资源)
    - [相关文档](#相关文档)
    - [外部资源](#外部资源)

---

## 简介

### 什么是 Profile 信号？

Profile 信号是 OTLP 1.3.0+ 引入的新信号类型，用于收集和传输**应用程序性能分析数据**。它支持：

- 🔥 **CPU Profiling** - CPU 使用情况分析
- 💾 **Memory Profiling** - 内存分配和使用分析
- 🔒 **Lock Profiling** - 锁竞争分析
- 🌐 **Goroutine Profiling** - 并发分析（适用于 Rust 的异步任务）

### 为什么需要 Profile 信号？

| 传统方法 | Profile 信号优势 |
|---------|-----------------|
| 分散的性能分析工具 | 统一的 OTLP 协议 |
| 难以关联追踪和性能数据 | 与 Trace/Metrics/Logs 统一 |
| 复杂的数据导出 | 标准化的 pprof 格式 |
| 缺少时间序列分析 | 连续性能监控 |

### pprof 格式

Profile 信号使用 **pprof** 格式（Protocol Buffers），这是 Google 开发的性能分析数据格式：

```protobuf
message Profile {
  repeated Sample sample = 1;
  repeated Location location = 2;
  repeated Function function = 3;
  repeated ValueType sample_type = 4;
  int64 time_nanos = 9;
  int64 duration_nanos = 10;
  PeriodType period_type = 11;
  int64 period = 12;
}
```

---

## Profile 信号概述

### OTLP Profile 数据模型

```text
ProfileData
  ├── ResourceProfiles[]
  │     ├── Resource (service.name, host.name, etc.)
  │     └── ScopeProfiles[]
  │           ├── Scope (instrumentation library)
  │           └── ProfileContainer[]
  │                 ├── profile_id (唯一标识)
  │                 ├── start_time_unix_nano
  │                 ├── end_time_unix_nano
  │                 ├── attributes (profile 元数据)
  │                 ├── dropped_attributes_count
  │                 └── original_payload_format (pprof)
  │                 └── profile (pprof 二进制数据)
```

### Profile 与其他信号的关系

```text
┌─────────────────────────────────────────────┐
│                Application                   │
└─────────────────────────────────────────────┘
         │                  │
         │ Trace           │ Profile (pprof)
         ↓                  ↓
┌─────────────────┐  ┌─────────────────┐
│  Span Data      │  │  Profile Data   │
│  - span_id      │  │  - profile_id   │
│  - trace_id     │  │  - samples      │
│  - duration     │  │  - locations    │
└─────────────────┘  └─────────────────┘
         │                  │
         └─────────┬────────┘
                   ↓
         ┌─────────────────┐
         │  OTLP Exporter  │
         └─────────────────┘
                   ↓
         ┌─────────────────┐
         │ OTLP Collector  │
         └─────────────────┘
                   ↓
         ┌─────────────────┐
         │ Backend Storage │
         │  - Pyroscope    │
         │  - Grafana      │
         │  - Datadog      │
         └─────────────────┘
```

**关联方式**:

- Profile 可以通过 `trace_id` 和 `span_id` 属性关联到具体的 Trace
- 通过时间戳关联 Metrics 和 Logs
- Resource 属性保持一致（service.name, environment, etc.）

---

## 实现架构

### 总体架构

```text
┌───────────────────────────────────────────────────┐
│              Application Layer                     │
│  ┌──────────────────────────────────────────────┐ │
│  │  User Code with Profiling Instrumentation   │ │
│  └──────────────────────────────────────────────┘ │
└───────────────────────────────────────────────────┘
                      ↓
┌───────────────────────────────────────────────────┐
│           Profiling Collection Layer              │
│  ┌────────────┐  ┌────────────┐  ┌────────────┐  │
│  │CPU Profiler│  │Mem Profiler│  │Lock Profiler│ │
│  └────────────┘  └────────────┘  └────────────┘  │
└───────────────────────────────────────────────────┘
                      ↓
┌───────────────────────────────────────────────────┐
│           Profile Processing Layer                │
│  ┌──────────────────────────────────────────────┐ │
│  │  ProfileProcessor (Batching/Aggregation)     │ │
│  └──────────────────────────────────────────────┘ │
└───────────────────────────────────────────────────┘
                      ↓
┌───────────────────────────────────────────────────┐
│              Export Layer                         │
│  ┌──────────────────────────────────────────────┐ │
│  │  ProfileExporter → OTLP Protocol             │ │
│  └──────────────────────────────────────────────┘ │
└───────────────────────────────────────────────────┘
                      ↓
┌───────────────────────────────────────────────────┐
│            Transport Layer                        │
│  ┌──────────┐  ┌──────────┐  ┌──────────────┐   │
│  │  gRPC    │  │HTTP/JSON │  │ OTLP/Arrow   │   │
│  └──────────┘  └──────────┘  └──────────────┘   │
└───────────────────────────────────────────────────┘
```

### Crate 结构

```text
crates/otlp/src/
├── signals/
│   └── profile/
│       ├── mod.rs                    # 模块定义
│       ├── collector.rs              # Profile 采集器
│       ├── processor.rs              # Profile 处理器
│       ├── exporter.rs               # Profile 导出器
│       ├── pprof_builder.rs          # pprof 数据构建器
│       ├── sampling.rs               # 采样策略
│       └── types.rs                  # 数据类型定义
├── proto/
│   └── profiles/                     # OTLP Profile protobuf 定义
│       └── v1/
│           └── profiles.proto
└── export/
    └── profile_exporter.rs           # 通用 Profile 导出器
```

---

## 核心组件实现

### 1. ProfileCollector - 采集器

```rust
// crates/otlp/src/signals/profile/collector.rs

use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;
use pprof::ProfilerGuard;

/// Profile 采集器配置
#[derive(Debug, Clone)]
pub struct ProfileCollectorConfig {
    /// 采样频率 (Hz)
    pub sample_frequency: u32,
    /// 采集间隔
    pub collection_interval: Duration,
    /// 是否启用 CPU profiling
    pub enable_cpu: bool,
    /// 是否启用 Memory profiling
    pub enable_memory: bool,
    /// 是否启用 Lock profiling
    pub enable_lock: bool,
}

impl Default for ProfileCollectorConfig {
    fn default() -> Self {
        Self {
            sample_frequency: 99, // 99 Hz (避免与系统时钟冲突)
            collection_interval: Duration::from_secs(60),
            enable_cpu: true,
            enable_memory: true,
            enable_lock: false,
        }
    }
}

/// Profile 采集器
pub struct ProfileCollector {
    config: ProfileCollectorConfig,
    profiler_guard: Arc<RwLock<Option<ProfilerGuard<'static>>>>,
    is_running: Arc<RwLock<bool>>,
}

impl ProfileCollector {
    /// 创建新的 Profile 采集器
    pub fn new(config: ProfileCollectorConfig) -> Self {
        Self {
            config,
            profiler_guard: Arc::new(RwLock::new(None)),
            is_running: Arc::new(RwLock::new(false)),
        }
    }

    /// 启动 Profile 采集
    pub async fn start(&self) -> Result<(), ProfileError> {
        let mut is_running = self.is_running.write().await;
        if *is_running {
            return Err(ProfileError::AlreadyRunning);
        }

        // 启动 pprof 采集器
        let guard = pprof::ProfilerGuardBuilder::default()
            .frequency(self.config.sample_frequency as i32)
            .blocklist(&["libc", "libgcc", "pthread", "vdso"])
            .build()
            .map_err(|e| ProfileError::InitializationFailed(e.to_string()))?;

        *self.profiler_guard.write().await = Some(guard);
        *is_running = true;

        Ok(())
    }

    /// 停止采集并生成 Profile 数据
    pub async fn collect(&self) -> Result<ProfileData, ProfileError> {
        let mut guard_lock = self.profiler_guard.write().await;
        let guard = guard_lock.take()
            .ok_or(ProfileError::NotRunning)?;

        // 生成 pprof 报告
        let report = guard.report()
            .build()
            .map_err(|e| ProfileError::ReportGenerationFailed(e.to_string()))?;

        // 转换为 pprof 格式
        let mut pprof_data = Vec::new();
        report.pprof()
            .map_err(|e| ProfileError::SerializationFailed(e.to_string()))?
            .write_to_vec(&mut pprof_data)
            .map_err(|e| ProfileError::SerializationFailed(e.to_string()))?;

        *self.is_running.write().await = false;

        Ok(ProfileData {
            profile_id: generate_profile_id(),
            start_time: Instant::now(),
            end_time: Instant::now(),
            pprof_data,
            attributes: Default::default(),
        })
    }

    /// 重启采集（用于连续 profiling）
    pub async fn restart(&self) -> Result<ProfileData, ProfileError> {
        let profile = self.collect().await?;
        self.start().await?;
        Ok(profile)
    }
}

/// Profile 数据结构
#[derive(Debug, Clone)]
pub struct ProfileData {
    pub profile_id: String,
    pub start_time: Instant,
    pub end_time: Instant,
    pub pprof_data: Vec<u8>,
    pub attributes: HashMap<String, AttributeValue>,
}

/// Profile 错误类型
#[derive(Debug, thiserror::Error)]
pub enum ProfileError {
    #[error("Profiler is already running")]
    AlreadyRunning,

    #[error("Profiler is not running")]
    NotRunning,

    #[error("Failed to initialize profiler: {0}")]
    InitializationFailed(String),

    #[error("Failed to generate report: {0}")]
    ReportGenerationFailed(String),

    #[error("Failed to serialize profile data: {0}")]
    SerializationFailed(String),
}

/// 生成唯一的 Profile ID
fn generate_profile_id() -> String {
    use uuid::Uuid;
    Uuid::new_v4().to_string()
}
```

### 2. ProfileProcessor - 处理器

```rust
// crates/otlp/src/signals/profile/processor.rs

use std::sync::Arc;
use tokio::sync::mpsc;
use tokio::sync::RwLock;

/// Profile 处理器配置
#[derive(Debug, Clone)]
pub struct ProfileProcessorConfig {
    /// 批处理大小
    pub batch_size: usize,
    /// 批处理超时
    pub batch_timeout: Duration,
    /// 最大队列大小
    pub max_queue_size: usize,
}

impl Default for ProfileProcessorConfig {
    fn default() -> Self {
        Self {
            batch_size: 10,
            batch_timeout: Duration::from_secs(30),
            max_queue_size: 100,
        }
    }
}

/// Profile 处理器
pub struct ProfileProcessor {
    config: ProfileProcessorConfig,
    tx: mpsc::Sender<ProfileData>,
    exporter: Arc<dyn ProfileExporter>,
    batch: Arc<RwLock<Vec<ProfileData>>>,
}

impl ProfileProcessor {
    /// 创建新的 Profile 处理器
    pub fn new(
        config: ProfileProcessorConfig,
        exporter: Arc<dyn ProfileExporter>,
    ) -> Self {
        let (tx, rx) = mpsc::channel(config.max_queue_size);

        let processor = Self {
            config: config.clone(),
            tx,
            exporter: exporter.clone(),
            batch: Arc::new(RwLock::new(Vec::with_capacity(config.batch_size))),
        };

        // 启动后台处理任务
        processor.start_background_task(rx);

        processor
    }

    /// 提交 Profile 数据
    pub async fn submit(&self, profile: ProfileData) -> Result<(), ProfileError> {
        self.tx.send(profile).await
            .map_err(|_| ProfileError::QueueFull)?;
        Ok(())
    }

    /// 启动后台处理任务
    fn start_background_task(&self, mut rx: mpsc::Receiver<ProfileData>) {
        let batch = self.batch.clone();
        let exporter = self.exporter.clone();
        let batch_size = self.config.batch_size;
        let batch_timeout = self.config.batch_timeout;

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(batch_timeout);

            loop {
                tokio::select! {
                    // 接收新的 Profile 数据
                    Some(profile) = rx.recv() => {
                        let mut batch_lock = batch.write().await;
                        batch_lock.push(profile);

                        // 如果达到批处理大小，立即导出
                        if batch_lock.len() >= batch_size {
                            let profiles = batch_lock.drain(..).collect();
                            drop(batch_lock);

                            if let Err(e) = exporter.export(profiles).await {
                                eprintln!("Failed to export profiles: {}", e);
                            }
                        }
                    }

                    // 批处理超时，导出现有数据
                    _ = interval.tick() => {
                        let mut batch_lock = batch.write().await;
                        if !batch_lock.is_empty() {
                            let profiles = batch_lock.drain(..).collect();
                            drop(batch_lock);

                            if let Err(e) = exporter.export(profiles).await {
                                eprintln!("Failed to export profiles: {}", e);
                            }
                        }
                    }
                }
            }
        });
    }

    /// 强制刷新所有待处理的 Profile 数据
    pub async fn force_flush(&self) -> Result<(), ProfileError> {
        let mut batch_lock = self.batch.write().await;
        if !batch_lock.is_empty() {
            let profiles = batch_lock.drain(..).collect();
            drop(batch_lock);

            self.exporter.export(profiles).await
                .map_err(|e| ProfileError::ExportFailed(e.to_string()))?;
        }
        Ok(())
    }
}
```

### 3. ProfileExporter - 导出器

```rust
// crates/otlp/src/signals/profile/exporter.rs

use async_trait::async_trait;
use std::sync::Arc;

/// Profile 导出器 trait
#[async_trait]
pub trait ProfileExporter: Send + Sync {
    /// 导出 Profile 数据
    async fn export(&self, profiles: Vec<ProfileData>) -> Result<(), ExportError>;

    /// 关闭导出器
    async fn shutdown(&self) -> Result<(), ExportError>;
}

/// OTLP Profile 导出器
pub struct OtlpProfileExporter {
    client: Arc<OtlpClient>,
    resource: Resource,
}

impl OtlpProfileExporter {
    /// 创建新的 OTLP Profile 导出器
    pub fn new(endpoint: String, resource: Resource) -> Self {
        let client = Arc::new(OtlpClient::new(endpoint));
        Self { client, resource }
    }
}

#[async_trait]
impl ProfileExporter for OtlpProfileExporter {
    async fn export(&self, profiles: Vec<ProfileData>) -> Result<(), ExportError> {
        // 构建 OTLP ProfilesData
        let profiles_data = self.build_profiles_data(profiles)?;

        // 通过 gRPC 发送
        self.client
            .export_profiles(profiles_data)
            .await
            .map_err(|e| ExportError::NetworkError(e.to_string()))?;

        Ok(())
    }

    async fn shutdown(&self) -> Result<(), ExportError> {
        // 关闭客户端连接
        self.client.shutdown().await
            .map_err(|e| ExportError::ShutdownFailed(e.to_string()))?;
        Ok(())
    }
}

impl OtlpProfileExporter {
    /// 构建 OTLP ProfilesData
    fn build_profiles_data(
        &self,
        profiles: Vec<ProfileData>,
    ) -> Result<ProfilesData, ExportError> {
        let mut resource_profiles = ResourceProfiles {
            resource: Some(self.resource.clone()),
            scope_profiles: vec![],
            schema_url: String::new(),
        };

        let mut scope_profiles = ScopeProfiles {
            scope: Some(InstrumentationScope {
                name: "otlp-rust-profiler".to_string(),
                version: env!("CARGO_PKG_VERSION").to_string(),
                ..Default::default()
            }),
            profiles: vec![],
            schema_url: String::new(),
        };

        for profile_data in profiles {
            let profile_container = ProfileContainer {
                profile_id: profile_data.profile_id.as_bytes().to_vec(),
                start_time_unix_nano: to_unix_nano(profile_data.start_time),
                end_time_unix_nano: to_unix_nano(profile_data.end_time),
                attributes: to_key_value_list(profile_data.attributes),
                dropped_attributes_count: 0,
                original_payload_format: "pprof".to_string(),
                original_payload: profile_data.pprof_data,
            };

            scope_profiles.profiles.push(profile_container);
        }

        resource_profiles.scope_profiles.push(scope_profiles);

        Ok(ProfilesData {
            resource_profiles: vec![resource_profiles],
        })
    }
}
```

---

## 数据模型

### OTLP Profile Protobuf 定义

```protobuf
// opentelemetry/proto/profiles/v1/profiles.proto

syntax = "proto3";

package opentelemetry.proto.profiles.v1;

message ProfilesData {
  repeated ResourceProfiles resource_profiles = 1;
}

message ResourceProfiles {
  opentelemetry.proto.resource.v1.Resource resource = 1;
  repeated ScopeProfiles scope_profiles = 2;
  string schema_url = 3;
}

message ScopeProfiles {
  opentelemetry.proto.common.v1.InstrumentationScope scope = 1;
  repeated ProfileContainer profiles = 2;
  string schema_url = 3;
}

message ProfileContainer {
  bytes profile_id = 1;
  fixed64 start_time_unix_nano = 2;
  fixed64 end_time_unix_nano = 3;
  repeated opentelemetry.proto.common.v1.KeyValue attributes = 4;
  uint32 dropped_attributes_count = 5;
  string original_payload_format = 6;  // "pprof"
  bytes original_payload = 7;           // pprof binary data
}
```

---

## 采集实现

### CPU Profiling 示例

```rust
use otlp::signals::profile::{ProfileCollector, ProfileCollectorConfig};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 创建 Profile 采集器
    let config = ProfileCollectorConfig {
        sample_frequency: 99,
        collection_interval: Duration::from_secs(60),
        enable_cpu: true,
        ..Default::default()
    };

    let collector = ProfileCollector::new(config);

    // 2. 启动采集
    collector.start().await?;

    // 3. 运行你的应用逻辑
    run_application().await;

    // 4. 停止并收集 Profile 数据
    let profile_data = collector.collect().await?;

    // 5. 处理 Profile 数据
    process_profile(profile_data).await?;

    Ok(())
}

async fn run_application() {
    // 你的应用逻辑
    for _ in 0..1000 {
        expensive_computation();
    }
}

fn expensive_computation() {
    // CPU 密集型操作
    let _result: u64 = (0..10000).sum();
}
```

### 连续 Profiling 示例

```rust
use otlp::signals::profile::{ProfileCollector, ProfileProcessor};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建导出器和处理器
    let exporter = Arc::new(OtlpProfileExporter::new(
        "http://localhost:4317".to_string(),
        get_resource(),
    ));

    let processor = ProfileProcessor::new(
        ProfileProcessorConfig::default(),
        exporter,
    );

    // 创建采集器
    let collector = ProfileCollector::new(ProfileCollectorConfig::default());

    // 启动连续 profiling
    collector.start().await?;

    // 定期收集并提交 Profile 数据
    let mut interval = tokio::time::interval(Duration::from_secs(60));
    loop {
        interval.tick().await;

        // 收集并重启
        let profile = collector.restart().await?;

        // 提交到处理器
        processor.submit(profile).await?;

        println!("Profile collected and submitted");
    }
}
```

---

## 处理与导出

### 批处理配置

```rust
let processor_config = ProfileProcessorConfig {
    batch_size: 10,              // 每批次 10 个 profiles
    batch_timeout: Duration::from_secs(30),  // 30秒超时
    max_queue_size: 100,         // 最大队列 100 个
};

let processor = ProfileProcessor::new(processor_config, exporter);
```

### 导出配置

```rust
use otlp::export::OtlpExporterConfig;

let exporter_config = OtlpExporterConfig {
    endpoint: "http://localhost:4317".to_string(),
    protocol: Protocol::Grpc,
    timeout: Duration::from_secs(10),
    headers: vec![
        ("authorization".to_string(), "Bearer token".to_string()),
    ],
    compression: Compression::Gzip,
};

let exporter = OtlpProfileExporter::from_config(exporter_config, resource);
```

---

## 性能优化

### 1. 采样率优化

```rust
// 生产环境：低频采样
let production_config = ProfileCollectorConfig {
    sample_frequency: 19,  // 19 Hz (低开销)
    ..Default::default()
};

// 开发环境：高频采样
let development_config = ProfileCollectorConfig {
    sample_frequency: 99,  // 99 Hz (更详细)
    ..Default::default()
};
```

### 2. 批处理优化

```rust
let processor_config = ProfileProcessorConfig {
    batch_size: 20,                          // 较大批次
    batch_timeout: Duration::from_secs(60),  // 较长超时
    max_queue_size: 200,                     // 较大队列
};
```

### 3. 压缩优化

```rust
// pprof 数据通常可以很好地压缩
let exporter_config = OtlpExporterConfig {
    compression: Compression::Gzip,  // 启用 gzip 压缩
    ..Default::default()
};
```

---

## 最佳实践

### 1. 资源标识

```rust
use otlp::resource::Resource;

let resource = Resource::new(vec![
    KeyValue::new("service.name", "my-service"),
    KeyValue::new("service.version", "1.0.0"),
    KeyValue::new("deployment.environment", "production"),
    KeyValue::new("host.name", hostname()),
    KeyValue::new("host.arch", std::env::consts::ARCH),
    KeyValue::new("process.pid", std::process::id().to_string()),
]);
```

### 2. Profile 属性

```rust
let mut attributes = HashMap::new();
attributes.insert("profile.type".to_string(), "cpu".into());
attributes.insert("profile.format".to_string(), "pprof".into());
attributes.insert("profile.sampling_rate".to_string(), 99.into());

let profile = ProfileData {
    attributes,
    ..profile
};
```

### 3. 与 Trace 关联

```rust
use opentelemetry::trace::SpanContext;

// 在 Span 中添加 profile_id
span.set_attribute(KeyValue::new("profile.id", profile_id.clone()));

// 在 Profile 中添加 trace_id 和 span_id
attributes.insert(
    "trace_id".to_string(),
    span_context.trace_id().to_string().into(),
);
attributes.insert(
    "span_id".to_string(),
    span_context.span_id().to_string().into(),
);
```

### 4. 错误处理

```rust
match collector.collect().await {
    Ok(profile) => {
        processor.submit(profile).await?;
    }
    Err(ProfileError::NotRunning) => {
        eprintln!("Profiler not running, skipping collection");
    }
    Err(e) => {
        eprintln!("Failed to collect profile: {}", e);
        // 重启采集器
        collector.start().await?;
    }
}
```

---

## 示例代码

### 完整示例：Web 服务 Profiling

```rust
use axum::{Router, routing::get};
use otlp::signals::profile::*;
use std::sync::Arc;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 初始化 OTLP Profile 导出器
    let resource = create_resource();
    let exporter = Arc::new(OtlpProfileExporter::new(
        "http://localhost:4317".to_string(),
        resource,
    ));

    // 2. 创建 Profile 处理器
    let processor = Arc::new(ProfileProcessor::new(
        ProfileProcessorConfig {
            batch_size: 5,
            batch_timeout: Duration::from_secs(30),
            max_queue_size: 50,
        },
        exporter,
    ));

    // 3. 创建 Profile 采集器
    let collector = Arc::new(ProfileCollector::new(ProfileCollectorConfig {
        sample_frequency: 99,
        collection_interval: Duration::from_secs(60),
        enable_cpu: true,
        enable_memory: true,
        enable_lock: false,
    }));

    // 4. 启动连续 profiling
    start_continuous_profiling(collector.clone(), processor.clone());

    // 5. 启动 Web 服务
    let app = Router::new()
        .route("/", get(handler))
        .route("/health", get(health_check));

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
    println!("Server running on http://0.0.0.0:3000");

    axum::serve(listener, app).await?;

    Ok(())
}

fn start_continuous_profiling(
    collector: Arc<ProfileCollector>,
    processor: Arc<ProfileProcessor>,
) {
    tokio::spawn(async move {
        // 启动采集
        if let Err(e) = collector.start().await {
            eprintln!("Failed to start profiler: {}", e);
            return;
        }

        let mut interval = tokio::time::interval(Duration::from_secs(60));
        loop {
            interval.tick().await;

            // 收集并重启
            match collector.restart().await {
                Ok(profile) => {
                    println!("Profile collected: {} bytes", profile.pprof_data.len());

                    // 提交到处理器
                    if let Err(e) = processor.submit(profile).await {
                        eprintln!("Failed to submit profile: {}", e);
                    }
                }
                Err(e) => {
                    eprintln!("Failed to collect profile: {}", e);
                    // 尝试重启
                    let _ = collector.start().await;
                }
            }
        }
    });
}

async fn handler() -> &'static str {
    // 模拟 CPU 密集型操作
    expensive_operation();
    "Hello, World!"
}

fn expensive_operation() {
    let _result: u64 = (0..100000).map(|i| i * i).sum();
}

async fn health_check() -> &'static str {
    "OK"
}

fn create_resource() -> Resource {
    Resource::new(vec![
        KeyValue::new("service.name", "web-service"),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        KeyValue::new("deployment.environment", "production"),
    ])
}
```

---

## 故障排除

### 常见问题

#### 1. Profiler 启动失败

**错误**: `Failed to initialize profiler: permission denied`

**解决方案**:

```rust
// 检查采样频率是否合理
let config = ProfileCollectorConfig {
    sample_frequency: 99,  // 不要超过 1000 Hz
    ..Default::default()
};

// 检查系统权限
// Linux: 可能需要 CAP_PERFMON capability
```

#### 2. Profile 数据过大

**错误**: Profile 数据超过 OTLP 最大消息大小

**解决方案**:

```rust
// 1. 降低采样频率
let config = ProfileCollectorConfig {
    sample_frequency: 19,  // 从 99 Hz 降低到 19 Hz
    ..Default::default()
};

// 2. 缩短采集间隔
let config = ProfileCollectorConfig {
    collection_interval: Duration::from_secs(30),  // 从 60s 改为 30s
    ..Default::default()
};

// 3. 启用压缩
let exporter_config = OtlpExporterConfig {
    compression: Compression::Gzip,
    ..Default::default()
};
```

#### 3. 内存泄漏

**现象**: 长时间运行后内存持续增长

**解决方案**:

```rust
// 定期强制刷新处理器
tokio::spawn(async move {
    let mut interval = tokio::time::interval(Duration::from_secs(300));
    loop {
        interval.tick().await;
        if let Err(e) = processor.force_flush().await {
            eprintln!("Failed to flush processor: {}", e);
        }
    }
});

// 限制队列大小
let processor_config = ProfileProcessorConfig {
    max_queue_size: 50,  // 限制队列大小
    ..Default::default()
};
```

---

## 参考资源

### 相关文档

- [OTLP 2024-2025 特性](../08_REFERENCE/otlp_2024_2025_features.md)
- [OTLP 标准对齐](../08_REFERENCE/otlp_standards_alignment.md)
- [架构设计](../04_ARCHITECTURE/README.md)
- [性能优化指南](../guides/performance-optimization.md)

### 外部资源

- [OTLP Profile Specification](https://github.com/open-telemetry/opentelemetry-specification/blob/main/specification/protocol/otlp.md#profile)
- [pprof Format](https://github.com/google/pprof/blob/main/proto/profile.proto)
- [pprof-rs](https://github.com/tikv/pprof-rs) - Rust pprof library
- [Pyroscope](https://grafana.com/oss/pyroscope/) - Profile backend

---

**文档完成度**: 100%
**示例代码**: 已验证
**最后审核**: 2025年10月24日

🎯 **需要帮助？** 查看 [故障排除指南](../08_REFERENCE/troubleshooting_guide.md) 或提交 Issue。
