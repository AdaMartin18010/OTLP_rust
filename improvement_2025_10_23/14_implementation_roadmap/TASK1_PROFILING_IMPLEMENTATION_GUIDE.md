# 任务1详细指南：Profiling标准实现

**📅 开始日期**: 2025年10月23日  
**⏱️ 预计工期**: 2-3周  
**🎯 目标**: 完整实现OpenTelemetry Profiling标准v0.1  
**📊 优先级**: P0（最高）

---

## 🎯 任务目标

实现符合OpenTelemetry Profiling Specification v0.1的完整性能分析功能，支持CPU和Memory profiling，并能够通过OTLP协议导出，与Trace数据无缝关联。

---

## 📋 功能需求

### 核心功能

```yaml
CPU Profiling:
  ✅ 基于采样的CPU profiling
  ✅ 可配置采样频率（默认100Hz）
  ✅ 调用栈捕获
  ✅ 符号解析
  ✅ 时间统计

Memory Profiling:
  ✅ 堆分配追踪
  ✅ 内存使用统计
  ✅ 分配点识别
  ✅ 内存泄漏检测

数据导出:
  ✅ pprof格式兼容
  ✅ OTLP协议导出
  ✅ Trace关联（trace_id, span_id）
  ✅ 批量处理

配置管理:
  ✅ 采样策略配置
  ✅ 导出配置
  ✅ 性能阈值配置
```

---

## 🏗️ 架构设计

### 模块结构

```text
src/profiling/
├── mod.rs              # 公共API和模块导出
├── types.rs            # 核心数据结构
├── cpu.rs              # CPU profiling
├── memory.rs           # Memory profiling
├── pprof.rs            # pprof格式编码
├── exporter.rs         # OTLP导出器
├── sampling.rs         # 采样策略
├── config.rs           # 配置管理
└── utils.rs            # 工具函数

tests/profiling/
├── cpu_tests.rs
├── memory_tests.rs
├── integration_tests.rs
└── performance_tests.rs

examples/
├── cpu_profiling_demo.rs
├── memory_profiling_demo.rs
└── trace_correlation_demo.rs

docs/profiling/
├── README.md
├── API_REFERENCE.md
├── USER_GUIDE.md
└── PERFORMANCE.md
```

### 数据流

```text
┌─────────────┐
│ Application │
└──────┬──────┘
       │
       ▼
┌─────────────┐
│  Profiler   │ ◄── 采样触发
│  (CPU/Mem)  │
└──────┬──────┘
       │ 采样数据
       ▼
┌─────────────┐
│  Profile    │
│  Builder    │
└──────┬──────┘
       │ Profile对象
       ▼
┌─────────────┐
│   pprof     │
│  Encoder    │
└──────┬──────┘
       │ pprof格式
       ▼
┌─────────────┐
│    OTLP     │
│  Exporter   │
└──────┬──────┘
       │
       ▼
┌─────────────┐
│   Backend   │
│ (Jaeger等)  │
└─────────────┘
```

---

## 💻 详细实现

### 1. 核心数据结构 (`types.rs`)

```rust
use std::collections::HashMap;
use std::time::{Duration, SystemTime};

/// Profile 表示一个性能分析快照
#[derive(Debug, Clone)]
pub struct Profile {
    /// 采样值类型（例如：cpu samples, alloc_space）
    pub sample_type: Vec<ValueType>,
    /// 采样数据
    pub sample: Vec<Sample>,
    /// 内存映射信息
    pub mapping: Vec<Mapping>,
    /// 代码位置
    pub location: Vec<Location>,
    /// 函数信息
    pub function: Vec<Function>,
    /// 字符串表（去重存储）
    pub string_table: Vec<String>,
    /// 采样时间（纳秒）
    pub time_nanos: i64,
    /// 采样持续时间（纳秒）
    pub duration_nanos: i64,
    /// 采样周期类型
    pub period_type: Option<ValueType>,
    /// 采样周期
    pub period: i64,
    /// 注释
    pub comment: Vec<i64>,
    /// 默认采样类型索引
    pub default_sample_type: i64,
}

/// 值类型定义
#[derive(Debug, Clone, PartialEq)]
pub struct ValueType {
    /// 类型（例如：cpu, memory）
    pub type_: i64,  // string table index
    /// 单位（例如：nanoseconds, bytes）
    pub unit: i64,   // string table index
}

/// 采样点
#[derive(Debug, Clone)]
pub struct Sample {
    /// 位置ID列表（调用栈）
    pub location_id: Vec<u64>,
    /// 采样值（可能有多个类型的值）
    pub value: Vec<i64>,
    /// 标签
    pub label: Vec<Label>,
}

/// 标签
#[derive(Debug, Clone)]
pub struct Label {
    pub key: i64,    // string table index
    pub str: i64,    // string table index (for string values)
    pub num: i64,    // for numeric values
    pub num_unit: i64, // string table index
}

/// 内存映射
#[derive(Debug, Clone)]
pub struct Mapping {
    pub id: u64,
    pub memory_start: u64,
    pub memory_limit: u64,
    pub file_offset: u64,
    pub filename: i64,  // string table index
    pub build_id: i64,  // string table index
    pub has_functions: bool,
    pub has_filenames: bool,
    pub has_line_numbers: bool,
    pub has_inline_frames: bool,
}

/// 代码位置
#[derive(Debug, Clone)]
pub struct Location {
    pub id: u64,
    pub mapping_id: u64,
    pub address: u64,
    pub line: Vec<Line>,
    pub is_folded: bool,
}

/// 代码行
##[derive(Debug, Clone)]
pub struct Line {
    pub function_id: u64,
    pub line: i64,
}

/// 函数信息
#[derive(Debug, Clone)]
pub struct Function {
    pub id: u64,
    pub name: i64,         // string table index
    pub system_name: i64,  // string table index
    pub filename: i64,     // string table index
    pub start_line: i64,
}

/// Profile构建器
pub struct ProfileBuilder {
    sample_type: Vec<ValueType>,
    samples: Vec<Sample>,
    mappings: HashMap<u64, Mapping>,
    locations: HashMap<u64, Location>,
    functions: HashMap<u64, Function>,
    string_table: HashMap<String, i64>,
    string_list: Vec<String>,
    time_nanos: i64,
    duration_nanos: i64,
    period_type: Option<ValueType>,
    period: i64,
}

impl ProfileBuilder {
    pub fn new() -> Self {
        let mut builder = Self {
            sample_type: Vec::new(),
            samples: Vec::new(),
            mappings: HashMap::new(),
            locations: HashMap::new(),
            functions: HashMap::new(),
            string_table: HashMap::new(),
            string_list: vec![String::new()], // index 0 is always empty string
            time_nanos: SystemTime::now()
                .duration_since(SystemTime::UNIX_EPOCH)
                .unwrap()
                .as_nanos() as i64,
            duration_nanos: 0,
            period_type: None,
            period: 0,
        };
        builder.string_table.insert(String::new(), 0);
        builder
    }

    /// 添加字符串到字符串表，返回索引
    pub fn add_string(&mut self, s: impl Into<String>) -> i64 {
        let s = s.into();
        if let Some(&idx) = self.string_table.get(&s) {
            return idx;
        }
        let idx = self.string_list.len() as i64;
        self.string_table.insert(s.clone(), idx);
        self.string_list.push(s);
        idx
    }

    /// 添加采样
    pub fn add_sample(&mut self, sample: Sample) {
        self.samples.push(sample);
    }

    /// 添加位置
    pub fn add_location(&mut self, location: Location) -> u64 {
        let id = location.id;
        self.locations.insert(id, location);
        id
    }

    /// 添加函数
    pub fn add_function(&mut self, function: Function) -> u64 {
        let id = function.id;
        self.functions.insert(id, function);
        id
    }

    /// 构建Profile
    pub fn build(mut self) -> Profile {
        Profile {
            sample_type: self.sample_type,
            sample: self.samples,
            mapping: self.mappings.into_values().collect(),
            location: self.locations.into_values().collect(),
            function: self.functions.into_values().collect(),
            string_table: self.string_list,
            time_nanos: self.time_nanos,
            duration_nanos: self.duration_nanos,
            period_type: self.period_type,
            period: self.period,
            comment: Vec::new(),
            default_sample_type: 0,
        }
    }
}
```

### 2. CPU Profiling (`cpu.rs`)

```rust
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;
use tokio::sync::RwLock;
use crate::profiling::types::*;
use crate::profiling::config::CpuProfilerConfig;

/// CPU Profiler
pub struct CpuProfiler {
    config: CpuProfilerConfig,
    running: Arc<AtomicBool>,
    profile_builder: Arc<RwLock<ProfileBuilder>>,
}

impl CpuProfiler {
    pub fn new(config: CpuProfilerConfig) -> Result<Self, ProfileError> {
        Ok(Self {
            config,
            running: Arc::new(AtomicBool::new(false)),
            profile_builder: Arc::new(RwLock::new(ProfileBuilder::new())),
        })
    }

    /// 启动CPU profiling
    pub async fn start(&self) -> Result<(), ProfileError> {
        if self.running.load(Ordering::SeqCst) {
            return Err(ProfileError::AlreadyRunning);
        }

        self.running.store(true, Ordering::SeqCst);

        // 启动采样线程
        let running = self.running.clone();
        let profile_builder = self.profile_builder.clone();
        let sample_frequency = self.config.sample_frequency;

        tokio::spawn(async move {
            let interval = Duration::from_secs_f64(1.0 / sample_frequency as f64);
            let mut ticker = tokio::time::interval(interval);

            while running.load(Ordering::SeqCst) {
                ticker.tick().await;
                
                // 捕获当前调用栈
                if let Ok(stacktrace) = capture_stacktrace() {
                    let mut builder = profile_builder.write().await;
                    add_stacktrace_to_profile(&mut builder, stacktrace);
                }
            }
        });

        Ok(())
    }

    /// 停止CPU profiling并返回profile
    pub async fn stop(&self) -> Result<Profile, ProfileError> {
        if !self.running.load(Ordering::SeqCst) {
            return Err(ProfileError::NotRunning);
        }

        self.running.store(false, Ordering::SeqCst);
        
        // 等待采样线程结束
        tokio::time::sleep(Duration::from_millis(100)).await;

        // 构建profile
        let builder = self.profile_builder.write().await;
        let profile = builder.clone().build();
        
        Ok(profile)
    }
}

/// 捕获当前调用栈
fn capture_stacktrace() -> Result<Vec<usize>, ProfileError> {
    // 使用backtrace库捕获调用栈
    let bt = backtrace::Backtrace::new();
    let frames: Vec<usize> = bt
        .frames()
        .iter()
        .filter_map(|frame| frame.ip() as usize)
        .collect();
    
    Ok(frames)
}

/// 将调用栈添加到profile
fn add_stacktrace_to_profile(builder: &mut ProfileBuilder, stacktrace: Vec<usize>) {
    let mut location_ids = Vec::new();

    for (idx, &addr) in stacktrace.iter().enumerate() {
        let location_id = (addr as u64) | ((idx as u64) << 48);
        
        // 符号解析
        if let Some((func_name, file, line)) = resolve_symbol(addr) {
            // 添加函数
            let func_name_idx = builder.add_string(func_name);
            let file_idx = builder.add_string(file);
            
            let function = Function {
                id: location_id,
                name: func_name_idx,
                system_name: func_name_idx,
                filename: file_idx,
                start_line: line as i64,
            };
            builder.add_function(function);

            // 添加位置
            let location = Location {
                id: location_id,
                mapping_id: 0,
                address: addr as u64,
                line: vec![Line {
                    function_id: location_id,
                    line: line as i64,
                }],
                is_folded: false,
            };
            builder.add_location(location);
            
            location_ids.push(location_id);
        }
    }

    // 添加采样
    let sample = Sample {
        location_id: location_ids,
        value: vec![1], // 采样次数
        label: Vec::new(),
    };
    builder.add_sample(sample);
}

/// 符号解析
fn resolve_symbol(addr: usize) -> Option<(String, String, u32)> {
    // 使用backtrace库进行符号解析
    backtrace::resolve(addr as *mut _, |symbol| {
        if let Some(name) = symbol.name() {
            let func_name = format!("{}", name);
            let (file, line) = symbol
                .filename()
                .and_then(|f| Some((f.display().to_string(), symbol.lineno()?)))
                .unwrap_or((String::from("unknown"), 0));
            
            return Some((func_name, file, line));
        }
        None
    });
    
    None
}

#[derive(Debug, thiserror::Error)]
pub enum ProfileError {
    #[error("Profiler is already running")]
    AlreadyRunning,
    
    #[error("Profiler is not running")]
    NotRunning,
    
    #[error("Failed to capture stacktrace: {0}")]
    StacktraceError(String),
    
    #[error("Failed to export profile: {0}")]
    ExportError(String),
}
```

### 3. 配置管理 (`config.rs`)

```rust
use std::time::Duration;

/// CPU Profiler配置
#[derive(Debug, Clone)]
pub struct CpuProfilerConfig {
    /// 采样频率（Hz）
    pub sample_frequency: u32,
    /// 最大调用栈深度
    pub max_stack_depth: usize,
    /// 是否解析符号
    pub resolve_symbols: bool,
    /// 是否包含系统调用
    pub include_syscalls: bool,
}

impl Default for CpuProfilerConfig {
    fn default() -> Self {
        Self {
            sample_frequency: 100, // 100Hz
            max_stack_depth: 128,
            resolve_symbols: true,
            include_syscalls: false,
        }
    }
}

/// Memory Profiler配置
#[derive(Debug, Clone)]
pub struct MemoryProfilerConfig {
    /// 采样率（每N次分配采样一次）
    pub sample_rate: usize,
    /// 最小追踪大小（bytes）
    pub min_size: usize,
    /// 是否追踪释放
    pub track_deallocations: bool,
}

impl Default for MemoryProfilerConfig {
    fn default() -> Self {
        Self {
            sample_rate: 524288, // 512KB
            min_size: 0,
            track_deallocations: true,
        }
    }
}

/// Profile导出配置
#[derive(Debug, Clone)]
pub struct ExporterConfig {
    /// OTLP端点
    pub endpoint: String,
    /// 导出间隔
    pub export_interval: Duration,
    /// 批大小
    pub batch_size: usize,
    /// 是否压缩
    pub compress: bool,
}

impl Default for ExporterConfig {
    fn default() -> Self {
        Self {
            endpoint: "http://localhost:4317".to_string(),
            export_interval: Duration::from_secs(60),
            batch_size: 100,
            compress: true,
        }
    }
}
```

---

## 🧪 测试策略

### 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_profile_builder() {
        let mut builder = ProfileBuilder::new();
        
        // 测试字符串表
        let idx1 = builder.add_string("test");
        let idx2 = builder.add_string("test");
        assert_eq!(idx1, idx2); // 去重

        // 测试添加采样
        let sample = Sample {
            location_id: vec![1, 2, 3],
            value: vec![10],
            label: Vec::new(),
        };
        builder.add_sample(sample);

        let profile = builder.build();
        assert_eq!(profile.sample.len(), 1);
    }

    #[tokio::test]
    async fn test_cpu_profiler_start_stop() {
        let config = CpuProfilerConfig::default();
        let profiler = CpuProfiler::new(config).unwrap();

        // 启动
        profiler.start().await.unwrap();
        assert!(profiler.running.load(Ordering::SeqCst));

        // 运行一段时间
        tokio::time::sleep(Duration::from_millis(100)).await();

        // 停止
        let profile = profiler.stop().await.unwrap();
        assert!(!profiler.running.load(Ordering::SeqCst));
        assert!(profile.sample.len() > 0);
    }
}
```

### 集成测试

```rust
// tests/profiling/integration_tests.rs

#[tokio::test]
async fn test_cpu_profiling_with_trace() {
    // 创建OTLP客户端
    let client = OtlpClient::new(OtlpConfig::default()).await.unwrap();

    // 创建CPU profiler
    let profiler_config = CpuProfilerConfig::default();
    let profiler = CpuProfiler::new(profiler_config).unwrap();

    // 启动trace
    let trace_id = client.start_trace("test_operation").await.unwrap();

    // 启动profiling
    profiler.start().await.unwrap();

    // 执行一些CPU密集操作
    perform_cpu_intensive_work();

    // 停止profiling
    let profile = profiler.stop().await.unwrap();

    // 将profile与trace关联并导出
    export_profile_with_trace(profile, trace_id).await.unwrap();
}

fn perform_cpu_intensive_work() {
    let mut sum = 0u64;
    for i in 0..10_000_000 {
        sum = sum.wrapping_add(i);
    }
}
```

### 性能测试

```rust
// benches/profiling_benchmarks.rs

use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn benchmark_cpu_profiler(c: &mut Criterion) {
    let rt = tokio::runtime::Runtime::new().unwrap();

    c.bench_function("cpu_profiler_overhead", |b| {
        b.iter(|| {
            rt.block_on(async {
                let config = CpuProfilerConfig::default();
                let profiler = CpuProfiler::new(config).unwrap();
                
                profiler.start().await.unwrap();
                perform_work();
                profiler.stop().await.unwrap();
            });
        });
    });
}

fn perform_work() {
    black_box((0..1000).sum::<i32>());
}

criterion_group!(benches, benchmark_cpu_profiler);
criterion_main!(benches);
```

---

## 📚 文档要求

### 用户文档

```markdown
    # Profiling用户指南

    ## 快速开始

    ### CPU Profiling

    ```rust
    use otlp::profiling::{CpuProfiler, CpuProfilerConfig};

    #[tokio::main]
    async fn main() -> Result<(), Box<dyn std::error::Error>> {
        // 创建配置
        let config = CpuProfilerConfig {
            sample_frequency: 100, // 100Hz
            max_stack_depth: 128,
            ..Default::default()
        };

        // 创建profiler
        let profiler = CpuProfiler::new(config)?;

        // 启动profiling
        profiler.start().await?;

        // 运行你的应用
        run_application().await?;

        // 停止并获取profile
        let profile = profiler.stop().await?;

        // 导出profile
        export_profile(profile).await?;

        Ok(())
    }
    ```

    ## 配置选项

    ### 采样频率

    ...（详细说明）

    ```

    ### API文档

    使用`cargo doc`生成，确保所有公共API都有文档注释。

    ```rust
    /// CPU性能分析器
    ///
    /// # Examples
    ///
    /// ```
    /// use otlp::profiling::CpuProfiler;
    ///
    /// # #[tokio::main]
    /// # async fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let profiler = CpuProfiler::new(Default::default())?;
    /// profiler.start().await?;
    /// // ... 运行代码 ...
    /// let profile = profiler.stop().await?;
    /// # Ok(())
    /// # }
    /// ```
    pub struct CpuProfiler {
        // ...
    }
```

---

## ✅ 验收标准

### 功能验收

- [ ] **CPU Profiling**
  - [ ] 采样功能正常
  - [ ] 符号解析准确
  - [ ] 调用栈完整

- [ ] **Memory Profiling**
  - [ ] 分配追踪正常
  - [ ] 统计数据准确

- [ ] **数据导出**
  - [ ] pprof格式兼容
  - [ ] OTLP导出正常
  - [ ] Trace关联正确

### 性能验收

- [ ] CPU开销 <5%
- [ ] 内存开销 <20MB
- [ ] 采样延迟 <1ms

### 质量验收

- [ ] 测试覆盖率 >80%
- [ ] 所有测试通过
- [ ] 无Clippy警告
- [ ] 文档完整

---

## 📞 支持和帮助

**问题反馈**: GitHub Issues  
**技术讨论**: GitHub Discussions  
**文档**: docs/profiling/  

---

**创建日期**: 2025年10月23日  
**最后更新**: 2025年10月23日  
**状态**: 📝 规划中
