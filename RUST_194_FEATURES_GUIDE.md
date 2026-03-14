# Rust 1.94 特性全面应用指南

## Rust 1.94 新特性概览

### 1. 语言特性

- `array_windows` - 数组窗口迭代
- Impl 继承 dead_code lint 级别
- 29个 RISC-V target features
- `unused_visibilities` lint
- Unicode 17 支持

### 2. 标准库新增 API

- `LazyCell::get/get_mut/force_mut`
- `LazyLock::get/get_mut/force_mut`
- `TryFrom<char> for usize`
- `Peekable::next_if_map/next_if_map_mut`
- `f32/f64::consts::EULER_GAMMA`
- `f32/f64::consts::GOLDEN_RATIO`
- `f32/f64::mul_add` (const 上下文)
- `[T]::element_offset`
- x86 AVX-512 FP16 intrinsics
- AArch64 NEON FP16 intrinsics

### 3. Cargo 特性

- Config `include` key
- TOML v1.1 支持

---

## 应用示例

### array_windows

```rust
// 旧代码
data.windows(2).map(|w| w[1] - w[0])

// Rust 1.94
data.array_windows().map(|[a, b]| b - a)
```

### LazyLock

```rust
use std::sync::LazyLock;

static CONFIG: LazyLock<Config> = LazyLock::new(|| {
    Config::load()
});

// 可变访问
if let Some(config) = LazyLock::get_mut(&mut CONFIG) {
    config.update();
}
```

### element_offset

```rust
let arr = [10, 20, 30];
let offset = arr.element_offset(&arr[1]); // 4 或 8 (取决于元素大小)
```

### 数学常量

```rust
use std::f64::consts::{EULER_GAMMA, GOLDEN_RATIO};

let gamma = EULER_GAMMA; // 0.5772156649015329
let phi = GOLDEN_RATIO;  // 1.618033988749895
```

### AVX-512 FP16

```rust
#[cfg(all(target_arch = "x86_64", target_feature = "avx512fp16"))]
use std::arch::x86_64::*;
```
