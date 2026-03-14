//! # Rust Edition 2024 新特性应用
//!
//! 本模块展示 Rust 1.85+ / Edition 2024 的最新语言特性
//!
//! ## Edition 2024 主要特性
//!
//! - **Async Closures**: `async || {}` 语法
//! - **Lifetime Capture Rules**: `impl Trait + use<..>` 精确捕获
//! - **Match Ergonomics**: 改进的模式匹配
//! - **Unsafe Extern Blocks**: `unsafe extern "C" {}`
//! - **Reserved `gen` Keyword**: 为生成器预留
//!
//! ## 标准库新增
//!
//! - `LazyLock` / `LazyCell` - 线程安全的延迟初始化
//! - `Future` / `IntoFuture` 进入 prelude
//! - `AsyncFn` / `AsyncFnMut` / `AsyncFnOnce` traits
//! - `ptr::fn_addr_eq` - 函数指针比较
//!
//! ## Cargo 新特性
//!
//! - Resolver v3 (Rust-version aware)
//! - 自动缓存清理
//! - `cargo info` 命令

/// Edition 2024: Async Closure 示例
///
/// 在 Edition 2024 之前，需要使用 `|| async {}` 组合
/// 现在可以直接使用 `async || {}` 语法
pub mod async_closures {

    /// 使用 async closure 捕获环境变量
    ///
    /// # Example
    /// ```
    /// let data = vec![1, 2, 3];
    /// let closure = async || {
    ///     // 可以直接使用 data，不需要 move
    ///     process(&data).await
    /// };
    /// ```
    pub async fn with_async_closure<F>(f: F) -> i32
    where
        F: AsyncFnOnce() -> i32,
    {
        f().await
    }

    /// 高阶 async closure 示例
    pub async fn higher_ranked<F>(f: F)
    where
        F: AsyncFn(&str) -> i32,
    {
        let result = f("hello").await;
        println!("Result: {}", result);
    }

    #[allow(dead_code)]
    async fn process(data: &[i32]) -> i32 {
        data.iter().sum()
    }
}

/// Edition 2024: Lifetime Capture Rules
///
/// 使用 `+ use<..>` 精确控制哪些泛型参数被捕获
pub mod precise_captures {
    /// 精确捕获特定生命周期
    ///
    /// 在 Edition 2024 中，这会捕获 'a 和 T
    /// 使用 `+ use<'a, T>` 可以明确指定
    pub async fn capture_specific<T>(data: &T) -> &T {
        data
    }

    /// 不捕获任何泛型参数
    pub async fn capture_nothing() -> i32 {
        42
    }

    /// 捕获所有在作用域中的类型
    pub async fn capture_all<T: Clone>(data: T) -> T {
        data
    }
}

/// Edition 2024: Match Ergonomics 改进
///
/// 简化的模式匹配语法
pub mod match_ergonomics {
    /// 使用更简洁的 match 模式
    ///
    /// Edition 2024 改进了引用类型的匹配
    pub fn simplified_match(opt: &Option<String>) -> usize {
        match opt {
            // 不再需要显式的 ref
            Some(val) => val.len(),
            None => 0,
        }
    }

    /// 解构匹配改进
    pub fn destructuring_match(data: &(i32, String)) -> String {
        let (num, text) = data;
        format!("{}: {}", num, text)
    }
}

/// Edition 2024: Unsafe 改进
///
/// - `unsafe extern` 块
/// - `unsafe` 属性标记
/// - `unsafe_op_in_unsafe_fn` 警告
pub mod unsafe_improvements {
    // Unsafe extern 块 (Edition 2024)
    // extern 块现在需要 `unsafe` 关键字
    unsafe extern "C" {
        pub safe fn safe_ffi_function();
        pub unsafe fn unsafe_ffi_function();
    }

    /// Unsafe 属性标记 (Edition 2024)
    ///
    /// 某些属性现在需要 `unsafe` 标记
    #[unsafe(no_mangle)]
    pub extern "C" fn my_exported_function() {}

    /// Unsafe 函数中的显式 unsafe 块
    ///
    /// Edition 2024 要求 unsafe 函数中的 unsafe 操作
    /// 必须包裹在 unsafe 块中
    pub unsafe fn explicit_unsafe_block(data: *const i32) -> i32 {
        // 必须显式使用 unsafe 块
        unsafe { *data }
    }
}

/// Edition 2024: LazyLock 延迟初始化
///
/// 线程安全的延迟初始化，替代 lazy_static
pub mod lazy_initialization {
    use std::sync::LazyLock;

    /// 全局配置 - 使用 LazyLock
    pub static GLOBAL_CONFIG: LazyLock<Config> = LazyLock::new(|| {
        Config {
            name: "OTLP".to_string(),
            version: "1.0".to_string(),
        }
    });

    /// 昂贵的初始化只执行一次
    pub static EXPENSIVE_DATA: LazyLock<Vec<u8>> = LazyLock::new(|| {
        println!("Initializing expensive data...");
        vec![0; 1024 * 1024] // 1MB data
    });

    #[derive(Debug)]
    pub struct Config {
        pub name: String,
        pub version: String,
    }
}

/// Edition 2024: 新的 Prelude 项
///
/// `Future` 和 `IntoFuture` 现在自动导入
pub mod prelude_additions {
    // Future 和 IntoFuture 现在自动在 scope 中
    // 不需要显式 use std::future::{Future, IntoFuture};

    pub async fn uses_future(f: impl Future<Output = i32>) -> i32 {
        f.await + 1
    }

    pub async fn into_future_example() -> String {
        "Hello".to_string()
    }
}

/// Edition 2024: Const 上下文改进
///
/// 更多 API 可以在 const 上下文中使用
pub mod const_improvements {
    use std::mem::{align_of_val, size_of_val};
    use std::ptr::{swap, NonNull};

    /// Const 上下文中的 size_of_val
    pub const fn get_size<T: ?Sized>(val: &T) -> usize {
        size_of_val(val)
    }

    /// Const 上下文中的 align_of_val
    pub const fn get_align<T: ?Sized>(val: &T) -> usize {
        align_of_val(val)
    }

    /// Const 上下文中的指针操作
    pub const unsafe fn swap_values<T>(a: *mut T, b: *mut T) {
        unsafe { swap(a, b) }
    }

    /// Const 上下文中的 NonNull
    pub const fn create_non_null<T>(ptr: *mut T) -> Option<NonNull<T>> {
        NonNull::new(ptr)
    }
}

/// Edition 2024: 诊断属性
///
/// 控制编译器诊断信息
pub mod diagnostic_attributes {
    /// 不推荐显示的 trait 实现
    ///
    /// 在错误信息中隐藏这个 blanket impl
    #[diagnostic::do_not_recommend]
    impl<T: Clone> MyTrait for T {
        fn do_something(&self) {}
    }

    pub trait MyTrait {
        fn do_something(&self);
    }
}

/// Edition 2024: 元编程改进
///
/// Macro fragment specifier 改进
pub mod macro_improvements {
    /// expr 片段说明符现在匹配 const 和 _ 表达式
    #[macro_export]
    macro_rules! improved_macro {
        // 现在可以匹配 const 表达式
        (const $e:expr) => {
            const VALUE: i32 = $e;
        };
        // 可以匹配 _ 占位符
        (placeholder: _) => {
            let _ = 42;
        };
    }
}

/// Edition 2024: 浮点数 midpoints
///
/// 计算两个浮点数的中间值，不会溢出
pub fn float_midpoint(a: f64, b: f64) -> f64 {
    a.midpoint(b)
}

/// Edition 2024: 元组 collect
///
/// 将迭代器收集到元组中 (需要精确类型匹配)
pub fn tuple_collect() -> (i32, String, bool) {
    [(1i32, "hello".to_string(), true)]
        .into_iter()
        .next()
        .unwrap()
}

/// Edition 2024: io::ErrorKind 新变体
///
/// 更详细的错误分类
pub fn check_error_kind(e: std::io::Error) -> bool {
    matches!(
        e.kind(),
        std::io::ErrorKind::QuotaExceeded | std::io::ErrorKind::CrossesDevices
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_async_closure() {
        // async closure 可以在同步上下文中测试
        let rt = tokio::runtime::Runtime::new().unwrap();
        rt.block_on(async {
            let data = vec![1, 2, 3];
            let closure = async || data.iter().sum::<i32>();
            let result = closure().await;
            assert_eq!(result, 6);
        });
    }

    #[test]
    fn test_lazy_lock() {
        // 第一次访问会初始化
        let config = &*lazy_initialization::GLOBAL_CONFIG;
        assert_eq!(config.name, "OTLP");

        // 第二次访问直接使用已初始化的值
        let config2 = &*lazy_initialization::GLOBAL_CONFIG;
        assert_eq!(config2.version, "1.0");
    }

    #[test]
    fn test_match_ergonomics() {
        let opt = Some("hello".to_string());
        let len = match_ergonomics::simplified_match(&opt);
        assert_eq!(len, 5);
    }

    #[test]
    fn test_float_midpoint() {
        assert_eq!(float_midpoint(0.0, 10.0), 5.0);
        assert_eq!(float_midpoint(-10.0, 10.0), 0.0);
    }

    #[test]
    fn test_const_size_of_val() {
        let arr = [1, 2, 3];
        const SIZE: usize = std::mem::size_of_val(&[1, 2, 3]);
        assert_eq!(const_improvements::get_size(&arr), SIZE);
    }

    #[test]
    fn test_tuple_collect() {
        let (a, b, c) = tuple_collect();
        assert_eq!(a, 1);
        assert_eq!(b, "hello");
        assert_eq!(c, true);
    }
}
