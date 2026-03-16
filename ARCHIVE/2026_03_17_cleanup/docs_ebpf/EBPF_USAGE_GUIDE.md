# eBPF 使用指南

**版本**: 1.0
**更新日期**: 2025年1月13日

---

## 📋 目录

- [简介](#简介)
- [快速开始](#快速开始)
- [核心功能](#核心功能)
  - [程序加载](#程序加载)
  - [探针管理](#探针管理)
  - [Maps 操作](#maps-操作)
  - [事件处理](#事件处理)
- [高级功能](#高级功能)
  - [异步事件处理](#异步事件处理)
  - [批量操作](#批量操作)
- [最佳实践](#最佳实践)
- [故障排除](#故障排除)

---

## 简介

eBPF 模块提供了基于 eBPF 的性能分析、网络追踪和系统调用追踪功能。本指南将帮助您快速上手并充分利用这些功能。

### 系统要求

- Linux 内核 >= 5.8 (推荐 5.15+)
- CAP_BPF 权限（或 root）
- BTF (BPF Type Format) 支持（推荐）

---

## 快速开始

### 1. 添加依赖

在 `Cargo.toml` 中启用 eBPF 功能：

```toml
[dependencies]
otlp = { path = "../crates/otlp", features = ["ebpf"] }
```

### 2. 基本使用

```rust
use otlp::ebpf::{EbpfConfig, EbpfLoader};

let config = EbpfConfig::default()
    .with_sample_rate(99)
    .with_cpu_profiling(true);

let mut loader = EbpfLoader::new(config);

// 检查系统支持
loader.check_system_support()?;

// 加载 eBPF 程序
let program_bytes = include_bytes!("program.bpf.o");
loader.load(program_bytes)?;
```

---

## 核心功能

### 程序加载

#### 创建加载器

```rust
use otlp::ebpf::{EbpfConfig, EbpfLoader};

let config = EbpfConfig::default()
    .with_sample_rate(99)
    .with_cpu_profiling(true)
    .with_network_tracing(true);

let mut loader = EbpfLoader::new(config);
```

#### 检查系统支持

```rust
match loader.check_system_support() {
    Ok(()) => println!("系统支持 eBPF"),
    Err(e) => eprintln!("系统不支持: {}", e),
}
```

#### 验证程序

```rust
let program_bytes = include_bytes!("program.bpf.o");
match loader.validate_program(program_bytes) {
    Ok(()) => println!("程序验证通过"),
    Err(e) => eprintln!("程序验证失败: {}", e),
}
```

#### 加载程序

```rust
let program_bytes = include_bytes!("program.bpf.o");
loader.load(program_bytes)?;

// 检查是否已加载
if loader.is_loaded() {
    println!("程序已加载");
}
```

### 探针管理

#### 创建探针管理器

```rust
use otlp::ebpf::ProbeManager;

let mut probe_manager = ProbeManager::new();
```

#### 附加 KProbe（内核函数探针）

```rust
// 不提供 Bpf 实例，仅注册（用于测试或延迟附加）
probe_manager.attach_kprobe("tcp_connect", "tcp_v4_connect", None)?;

// 提供 Bpf 实例，进行实际附加
if let Some(bpf) = loader.bpf_mut() {
    probe_manager.attach_kprobe("tcp_connect", "tcp_v4_connect", Some(bpf))?;
}
```

#### 附加 UProbe（用户空间函数探针）

```rust
probe_manager.attach_uprobe(
    "malloc_trace",
    "/usr/lib/libc.so.6",
    "malloc",
    None
)?;
```

#### 附加 Tracepoint（跟踪点）

```rust
probe_manager.attach_tracepoint(
    "open_trace",
    "syscalls",
    "sys_enter_openat",
    None
)?;
```

#### 列出和管理探针

```rust
// 列出所有探针
let probes = probe_manager.list_probes();
for (name, probe_type, target, attached) in probes {
    println!("{}: {} -> {} [{}]", name, probe_type, target, attached);
}

// 分离单个探针
probe_manager.detach("tcp_connect")?;

// 分离所有探针
probe_manager.detach_all()?;
```

### Maps 操作

#### 创建 Maps 管理器

```rust
use otlp::ebpf::{MapsManager, MapType};

let mut maps_manager = MapsManager::new();
```

#### 注册 Map

```rust
maps_manager.register_map(
    "event_map".to_string(),
    MapType::Hash,
    4,  // key_size
    8   // value_size
);
```

#### 读写 Map

```rust
let key = vec![1, 2, 3, 4];
let value = vec![10, 20, 30, 40, 50, 60, 70, 80];

// 写入（不提供 Bpf 实例，仅验证）
maps_manager.write_map("event_map", &key, &value, None)?;

// 写入（提供 Bpf 实例，实际写入）
if let Some(bpf) = loader.bpf_mut() {
    maps_manager.write_map("event_map", &key, &value, Some(bpf))?;
}

// 读取
let read_value = maps_manager.read_map("event_map", &key, None)?;
```

#### 删除键值对

```rust
maps_manager.delete_map("event_map", &key)?;
```

### 事件处理

#### 创建事件处理器

```rust
use otlp::ebpf::{EventProcessor, EbpfEvent, EbpfEventType};

let mut processor = EventProcessor::new(1000); // 缓冲区大小

// 或指定批处理大小
let mut processor = EventProcessor::with_batch_size(1000, 50);
```

#### 处理单个事件

```rust
let event = EbpfEvent {
    event_type: EbpfEventType::CpuSample,
    pid: 1234,
    tid: 5678,
    timestamp: std::time::SystemTime::now(),
    data: vec![1, 2, 3, 4, 5],
};

processor.process_event(event)?;
```

#### 批量处理事件

```rust
let mut events = Vec::new();
for i in 0..100 {
    events.push(EbpfEvent {
        event_type: EbpfEventType::CpuSample,
        pid: 1000 + i,
        tid: 2000 + i,
        timestamp: std::time::SystemTime::now(),
        data: vec![],
    });
}

processor.process_batch(events)?;
```

#### 事件过滤

```rust
// 按类型过滤
let cpu_events = processor.filter_by_type(EbpfEventType::CpuSample);

// 按 PID 过滤
let pid_events = processor.filter_by_pid(1234);

// 自定义过滤
let filtered = processor.filter_events(|e| e.pid > 1000 && e.pid < 2000);
```

#### 刷新事件

```rust
let events = processor.flush_events()?;
// 处理 events...
```

---

## 高级功能

### 异步事件处理

对于高并发场景，可以使用 `AsyncEventProcessor`：

```rust
use otlp::ebpf::AsyncEventProcessor;

let processor = AsyncEventProcessor::with_batch_size(5000, 100);

// 异步处理事件
processor.process_event(event).await?;

// 批量异步处理
processor.process_batch_async(events).await?;

// 异步刷新
let events = processor.flush_events_async().await?;
```

### 批量操作

批量操作可以显著提升性能：

```rust
// 批量处理事件
processor.process_batch(events)?;

// 批量异步处理
processor.process_batch_async(events).await?;
```

---

## 最佳实践

### 1. 错误处理

始终检查系统支持和程序验证：

```rust
loader.check_system_support()?;
loader.validate_program(program_bytes)?;
```

### 2. 资源清理

使用完毕后清理资源：

```rust
probe_manager.detach_all()?;
loader.unload()?;
processor.clear();
```

### 3. 性能优化

- 使用批量处理而不是逐个处理
- 在高并发场景使用 `AsyncEventProcessor`
- 合理设置缓冲区大小

### 4. 权限管理

确保有足够的权限：

```rust
// 检查权限
if loader.check_system_support().is_err() {
    eprintln!("需要 CAP_BPF 权限或 root");
    return;
}
```

---

## 故障排除

### 常见问题

#### 1. 程序加载失败

**问题**: `LoadFailed` 错误

**解决方案**:
- 检查内核版本 >= 5.8
- 确认有 CAP_BPF 权限
- 验证程序字节码格式正确

#### 2. 探针附加失败

**问题**: `AttachFailed` 错误

**解决方案**:
- 确认函数名或符号名正确
- 检查二进制文件路径存在
- 确认有足够的权限

#### 3. Map 操作失败

**问题**: `MapOperationFailed` 错误

**解决方案**:
- 确认 Map 已注册
- 检查键值大小匹配
- 验证 Map 类型支持该操作

---

## 示例代码

完整的示例代码请参考：

- `examples/ebpf_complete_example.rs` - 完整功能示例
- `examples/ebpf_async_example.rs` - 异步处理示例
- `examples/ebpf_probe_management_example.rs` - 探针管理示例
- `examples/ebpf_maps_operations_example.rs` - Maps 操作示例

---

**最后更新**: 2025年1月13日
