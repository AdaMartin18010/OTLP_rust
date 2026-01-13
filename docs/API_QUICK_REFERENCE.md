# API 快速参考

**版本**: v0.5.0-rc1
**最后更新**: 2025年1月13日

---

## 📚 核心模块

### Profiling 模块

#### CpuProfiler

```rust
use otlp::profiling::{CpuProfiler, ProfilerConfig};

// 创建
let mut profiler = CpuProfiler::new(ProfilerConfig::default());

// 启动
profiler.start().await?;

// 停止并获取 Profile
let profile = profiler.stop().await?;

// 导出
let json = profile.encode_json()?;
```

#### PprofProfile

```rust
use otlp::profiling::types::PprofProfile;

let mut profile = PprofProfile::new();

// 添加样本
profile.add_sample(sample);

// 添加位置
profile.add_location(location);

// 添加函数
profile.add_function(function);

// 编码/解码
let json = profile.encode_json()?;
let profile = PprofProfile::decode_json(&json)?;
```

### eBPF 模块

#### EbpfLoader

```rust
use otlp::ebpf::{EbpfLoader, EbpfConfig};

// 检查系统支持
EbpfLoader::check_system_support()?;

// 创建加载器
let mut loader = EbpfLoader::new(EbpfConfig::default());

// 验证程序
loader.validate_program(&program_bytes)?;

// 加载程序
loader.load(&program_bytes)?;

// 卸载
loader.unload()?;
```

#### ProbeManager

```rust
use otlp::ebpf::ProbeManager;

let mut manager = ProbeManager::new();

// 附加 KProbe
manager.attach_kprobe("name", "function")?;

// 附加 UProbe
manager.attach_uprobe("name", "/path/to/binary", "symbol")?;

// 附加 Tracepoint
manager.attach_tracepoint("name", "category", "event")?;

// 分离
manager.detach("name")?;
manager.detach_all()?;
```

#### MapsManager

```rust
use otlp::ebpf::{MapsManager, MapType};

let mut manager = MapsManager::new();

// 注册 Map
manager.register_map("name".to_string(), MapType::Hash, 4, 8)?;

// 读写
manager.write_map("name", &key, &value)?;
let value = manager.read_map("name", &key)?;

// 删除
manager.delete_map("name")?;
```

#### EventProcessor

```rust
use otlp::ebpf::{EventProcessor, EbpfEvent, EbpfEventType};

let mut processor = EventProcessor::new(1000);

// 处理事件
processor.process_event(event)?;

// 刷新
let events = processor.flush_events()?;

// 过滤
let cpu_events = processor.filter_events_by_type(EbpfEventType::CpuSample);
```

### 性能优化模块

#### QuickOptimizationsManager

```rust
use otlp::performance::{QuickOptimizationsManager, CompressionAlgorithm};

let manager = QuickOptimizationsManager::default();

// 压缩
let compressed = manager.compress(&data, CompressionAlgorithm::Gzip)?;

// 解压
let decompressed = manager.decompress(&compressed, CompressionAlgorithm::Gzip)?;
```

#### OptimizedMemoryPool

```rust
use otlp::performance::{OptimizedMemoryPool, MemoryPoolConfig};

let mut pool = OptimizedMemoryPool::new(MemoryPoolConfig::default());

// 分配
let block = pool.allocate(1024)?;

// 释放
pool.deallocate(block)?;

// 统计
let stats = pool.stats();
```

---

## 🔧 配置

### ProfilerConfig

```rust
use otlp::profiling::ProfilerConfig;

let config = ProfilerConfig {
    sample_rate: 100,  // Hz
    duration: Duration::from_secs(10),
    // ...
};
```

### EbpfConfig

```rust
use otlp::ebpf::EbpfConfig;

let config = EbpfConfig::default()
    .with_sample_rate(99)
    .with_cpu_profiling(true)
    .with_network_tracing(true)
    .with_syscall_tracing(true)
    .with_memory_tracing(true);
```

---

## 📝 错误处理

```rust
use otlp::error::OtlpError;

match result {
    Ok(value) => println!("成功: {:?}", value),
    Err(OtlpError::Processing(e)) => println!("处理错误: {}", e),
    Err(OtlpError::System(e)) => println!("系统错误: {}", e),
    Err(e) => println!("其他错误: {}", e),
}
```

---

## 🔗 更多信息

- [完整API文档](../crates/otlp/docs/)
- [使用示例](../examples/)
- [最佳实践](../docs/12_GUIDES/)
