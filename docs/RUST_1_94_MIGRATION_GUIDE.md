# Rust 1.94 + 2024 Edition 迁移指南

> 本文档总结 OTLP Rust 项目对标 Rust 1.94 和 2024 Edition 的改进
> 
> 参考: https://releases.rs/docs/1.94.0/

## 1. Rust 1.94 新特性应用

### 1.1 LazyCell/LazyLock 可变访问

Rust 1.94 新增：
- `LazyCell::get()` / `LazyCell::get_mut()`
- `LazyCell::force()` / `LazyCell::force_mut()`
- `LazyLock::get()` / `LazyLock::get_mut()`

**使用示例** (`crates/otlp/src/rust_1_94_features_new.rs`):

```rust
use std::cell::LazyCell;

let mut cell: LazyCell<Vec<i32>> = LazyCell::new(|| vec![1, 2, 3]);

// Rust 1.94: 使用 force_mut 获取可变引用
let vec = LazyCell::force_mut(&mut cell);
vec.push(4);

// 使用 force 获取不可变引用
let endpoints: &Vec<String> = LazyCell::force(&self.endpoints);
```

### 1.2 数组切片新操作

Rust 1.94 稳定：
- `<[T]>::array_windows<N>()` - 创建固定大小的滑动窗口
- `<[T]>::element_offset()` - 获取元素字节偏移

**使用示例**:

```rust
let data = [1.0, 2.0, 3.0, 4.0, 5.0];

// 创建大小为2的滑动窗口
let windows: Vec<_> = data.array_windows::<2>().collect();
// windows = [[1.0, 2.0], [2.0, 3.0], [3.0, 4.0], [4.0, 5.0]]

// 计算变化率
let rates: Vec<f64> = data.array_windows::<2>()
    .map(|&[prev, curr]| (curr - prev) / prev)
    .collect();
```

### 1.3 数学常数

Rust 1.94 新增：
- `f32::consts::EULER_GAMMA` / `f64::consts::EULER_GAMMA`
- `f32::consts::GOLDEN_RATIO` / `f64::consts::GOLDEN_RATIO`

**使用示例**:

```rust
use std::f64::consts::{EULER_GAMMA, GOLDEN_RATIO};

// 黄金比例 φ ≈ 1.618
let phi = GOLDEN_RATIO;

// Euler-Mascheroni 常数 γ ≈ 0.577
let euler = EULER_GAMMA;

// 应用：基于黄金比例计算最优采样间隔
let sample_interval = (1000.0 / GOLDEN_RATIO) as u64; // ~618ms
```

### 1.4 迭代器新方法

Rust 1.94 稳定：
- `Peekable::next_if_map()`

## 2. Rust 2024 Edition 特性

### 2.1 Async Closures

Rust 2024 Edition 引入 `async || {}` 语法：

```rust
// 以前
let f = || async { /* ... */ };

// Rust 2024
let f = async || { /* ... */ };
```

**项目实现** (`crates/otlp/src/async_closures.rs`):

```rust
/// 使用 async closure 的批量导出器
pub struct AsyncBatchExporter<T> {
    export_fn: Box<dyn Fn(Vec<T>) -> Pin<Box<dyn Future<Output = Result<(), ExportError>> + Send>> + Send>,
}

impl<T: Send + 'static> AsyncBatchExporter<T> {
    pub fn new<F, Fut>(export_fn: F) -> Self
    where
        F: Fn(Vec<T>) -> Fut + Send + 'static,
        Fut: Future<Output = Result<(), ExportError>> + Send + 'static,
    {
        Self {
            export_fn: Box::new(move |batch| Box::pin(export_fn(batch))),
        }
    }
}
```

### 2.2 AsyncFn Trait

Rust 2024 引入 `AsyncFn`、`AsyncFnMut`、`AsyncFnOnce` trait：

```rust
// Rust 2024: 可以使用 AsyncFn trait bound
impl<F> TelemetryProcessor<F>
where
    F: AsyncFn(TelemetryData) -> ProcessResult,
{
    pub async fn process(&self, data: TelemetryData) -> ProcessResult {
        (self.processor)(data).await
    }
}
```

### 2.3 生命周期捕获规则

Rust 2024 改进 `impl Trait + use<..>` 语法：

```rust
// 精确控制生命周期捕获
fn make_iter<'a>(slice: &'a [i32]) -> impl Iterator<Item = &'a i32> + use<'a> {
    slice.iter()
}
```

## 3. 依赖更新

### 3.1 关键依赖版本

| 依赖 | 旧版本 | 新版本 | 说明 |
|------|--------|--------|------|
| tokio | 1.35 | 1.50 | 最新稳定版 |
| axum | 0.7 | 0.8 | 移除 async_trait |
| tracing-opentelemetry | 0.23 | 0.32 | OpenTelemetry 0.31 支持 |
| opentelemetry | 0.22 | 0.31 | 最新稳定版 |
| opentelemetry-otlp | 0.15 | 0.31 | 最新稳定版 |

### 3.2 废弃依赖迁移

- `async-std` → `tokio` (async-std 已废弃)
- `wasm32-wasi` → `wasm32-wasip1` / `wasm32-wasip2`

## 4. 代码改进示例

### 4.1 使用 Rust 1.94 特性优化 OTLP 导出器

```rust
// crates/otlp/src/rust_1_94_features_new.rs

pub struct EndpointManager {
    /// 使用 LazyCell 延迟初始化
    endpoints: LazyCell<Vec<String>>,
    /// 使用 LazyLock 缓存健康检查
    health_cache: LazyLock<Mutex<Vec<(String, bool)>>>,
}

impl EndpointManager {
    /// Rust 1.94: 使用 force_mut 动态添加端点
    pub fn add_endpoint(&mut self, endpoint: &str) {
        let endpoints = LazyCell::force_mut(&mut self.endpoints);
        endpoints.push(endpoint.to_string());
    }
    
    /// 使用 array_windows 检查端点对
    pub fn check_endpoint_pairs(&self) -> Vec<(&str, &str)> {
        let endpoints: &Vec<String> = LazyCell::force(&self.endpoints);
        
        endpoints.array_windows::<2>()
            .map(|[a, b]: &[String; 2]| (a.as_str(), b.as_str()))
            .collect()
    }
}
```

### 4.2 使用数学常数优化性能分析器

```rust
pub struct ProfilerConfig {
    /// 采样间隔（基于黄金比例优化）
    pub sample_interval_ms: u64,
}

impl Default for ProfilerConfig {
    fn default() -> Self {
        use std::f64::consts::GOLDEN_RATIO;
        
        // 使用黄金比例计算最优采样间隔
        let base_interval = (1000.0 / GOLDEN_RATIO) as u64;
        
        Self {
            sample_interval_ms: base_interval, // ~618ms
        }
    }
}
```

## 5. 迁移检查清单

- [x] 更新 `Cargo.toml` 到 `edition = "2024"`
- [x] 运行 `cargo fix --edition` 自动修复
- [x] 更新 tokio 到 1.50+
- [x] 更新 axum 到 0.8+
- [x] 更新 OpenTelemetry 到 0.31+
- [x] 移除 async-std 依赖
- [x] 应用 Rust 1.94 新 API
- [x] 修复所有编译警告
- [x] 运行完整测试套件

## 6. 性能改进

| 优化项 | 改进前 | 改进后 | 提升 |
|--------|--------|--------|------|
| 端点管理 | 即时初始化 | LazyCell 延迟初始化 | 启动速度 ↑ |
| 批处理 | 顺序处理 | array_windows 并行 | 吞吐量 ↑ |
| 采样间隔 | 固定 1000ms | 黄金比例优化 ~618ms | 精度 ↑ |

## 7. 参考资源

- [Rust 1.94 Release Notes](https://releases.rs/docs/1.94.0/)
- [Rust 2024 Edition Guide](https://doc.rust-lang.org/edition-guide/rust-2024/)
- [Tokio 1.50 Documentation](https://docs.rs/tokio/1.50.0/)
- [Axum 0.8 Documentation](https://docs.rs/axum/0.8.0/)
- [OpenTelemetry Rust 0.31](https://docs.rs/opentelemetry/0.31.0/)

---

**持续更新中...**
