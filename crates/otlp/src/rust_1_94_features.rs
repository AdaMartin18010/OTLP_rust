//! # Rust 1.94 完整特性展示
//!
//! 本模块全面展示 Rust 1.94 的所有新特性和改进

// ============================================================================
// 1. 异步编程增强 (Async Programming Enhancements)
// ============================================================================

/// Rust 1.94 异步闭包和 AsyncFn traits
pub mod async_features {
    /// 使用 AsyncFn trait 的泛型函数
    pub async fn call_async<F>(f: F) -> i32
    where
        F: std::ops::AsyncFnOnce() -> i32,
    {
        f().await
    }

    /// 异步闭包示例
    #[allow(clippy::useless_vec)]
    pub async fn async_closure_example() -> i32 {
        let data = vec![1, 2, 3, 4, 5];

        // Rust 1.94: 异步闭包语法
        let sum_closure = async || -> i32 {
            data.iter().sum()
        };

        sum_closure().await
    }
}

// ============================================================================
// 2. 标准库新增 (Standard Library Additions)
// ============================================================================

/// LazyLock 和 LazyCell - 线程安全的延迟初始化
pub mod lazy_initialization {
    use std::sync::LazyLock;

    /// 全局配置 - 使用 LazyLock (线程安全)
    pub static GLOBAL_CONFIG: LazyLock<Config> = LazyLock::new(|| {
        Config {
            name: "OTLP".to_string(),
            version: env!("CARGO_PKG_VERSION").to_string(),
            max_connections: 100,
        }
    });

    #[derive(Debug, Clone)]
    pub struct Config {
        pub name: String,
        pub version: String,
        pub max_connections: usize,
    }
}

/// 浮点数改进
pub mod float_improvements {
    /// 计算中点 - 不会溢出
    pub fn safe_midpoint(a: f64, b: f64) -> f64 {
        a.midpoint(b)
    }

    /// 角度转换
    pub fn angle_conversions(radians: f64) -> (f64, f64) {
        (radians.to_degrees(), radians.to_radians())
    }

    /// 倒数
    pub fn reciprocal(x: f32) -> f32 {
        x.recip()
    }
}

/// 集合操作改进
pub mod collection_improvements {
    /// Vec::pop_if - 条件弹出
    pub fn pop_if_example(vec: &mut Vec<i32>) -> Option<i32> {
        vec.pop_if(|x| *x % 2 == 0)
    }
}

// ============================================================================
// 3. Const 上下文扩展 (Const Context Extensions)
// ============================================================================

/// Rust 1.94 中更多 API 可在 const 上下文中使用
pub mod const_context {
    use std::mem::{align_of_val, size_of_val};
    use std::ptr::NonNull;

    /// Const 上下文中的 size_of_val
    pub const fn get_size<T: ?Sized>(val: &T) -> usize {
        size_of_val(val)
    }

    /// Const 上下文中的 align_of_val
    pub const fn get_align<T: ?Sized>(val: &T) -> usize {
        align_of_val(val)
    }

    /// Const 上下文中的 NonNull
    pub const fn create_non_null<T>(ptr: *mut T) -> Option<NonNull<T>> {
        NonNull::new(ptr)
    }
}

// ============================================================================
// 4. Unsafe 代码改进 (Unsafe Code Improvements)
// ============================================================================

/// Rust 1.94 的 Unsafe 代码改进
pub mod unsafe_improvements {
    // Unsafe extern 块 - extern 块现在需要 unsafe 关键字
    unsafe extern "C" {
        // Safe FFI 函数
        pub safe fn safe_ffi_function();
        // Unsafe FFI 函数
        pub unsafe fn unsafe_ffi_function();
    }

    /// Unsafe 属性标记
    #[unsafe(no_mangle)]
    pub extern "C" fn exported_function() {
        println!("Exported function");
    }

    /// Unsafe 函数中的显式 unsafe 块
    /// # Safety
    /// 调用者必须确保指针有效且指向有效的i32值
    pub unsafe fn read_pointer(p: *const i32) -> i32 {
        unsafe { *p }
    }
}

// ============================================================================
// 5. I/O 错误处理改进
// ============================================================================

/// Rust 1.94 新增的错误类型
pub mod io_errors {
    use std::io;

    /// 处理新的 ErrorKind 变体
    pub fn handle_io_error(e: &io::Error) -> &'static str {
        match e.kind() {
            io::ErrorKind::QuotaExceeded => {
                "Disk quota exceeded - clean up space or increase quota"
            }
            io::ErrorKind::CrossesDevices => {
                "Operation would cross device boundaries"
            }
            _ => "Unknown I/O error",
        }
    }
}

// ============================================================================
// 6. 构建器和配置模式
// ============================================================================

/// 使用 Rust 1.94 特性的构建器模式
pub mod builder_pattern {
    use std::sync::LazyLock;

    /// 全局默认配置
    static DEFAULT_CONFIG: LazyLock<ClientConfig> = LazyLock::new(ClientConfig::default);

    #[derive(Debug, Clone)]
    pub struct ClientConfig {
        pub endpoint: String,
        pub timeout: std::time::Duration,
        pub max_retries: u32,
        pub enable_compression: bool,
    }

    impl Default for ClientConfig {
        fn default() -> Self {
            Self {
                endpoint: "http://localhost:4317".to_string(),
                timeout: std::time::Duration::from_secs(30),
                max_retries: 3,
                enable_compression: true,
            }
        }
    }

    pub struct ClientConfigBuilder {
        config: ClientConfig,
    }

    impl Default for ClientConfigBuilder {
        fn default() -> Self {
            Self::new()
        }
    }

    impl ClientConfigBuilder {
        pub fn new() -> Self {
            Self {
                config: DEFAULT_CONFIG.clone(),
            }
        }

        pub fn endpoint(mut self, endpoint: impl Into<String>) -> Self {
            self.config.endpoint = endpoint.into();
            self
        }

        pub fn build(self) -> ClientConfig {
            self.config
        }
    }
}

// ============================================================================
// 7. 测试和验证
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lazy_lock() {
        let config = &*lazy_initialization::GLOBAL_CONFIG;
        assert_eq!(config.name, "OTLP");
    }

    #[test]
    fn test_float_midpoint() {
        assert_eq!(float_improvements::safe_midpoint(0.0, 10.0), 5.0);
    }

    #[test]
    fn test_collection_pop_if() {
        // pop_if pops from the END, so it checks 5 first (odd), returns None
        let mut vec = vec![1, 2, 3, 4, 5];
        let result = collection_improvements::pop_if_example(&mut vec);
        assert_eq!(result, None); // 5 is odd
        
        // Now pop from vec with even at the end
        let mut vec2 = vec![1, 2, 3, 4];
        let even = collection_improvements::pop_if_example(&mut vec2);
        assert_eq!(even, Some(4)); // 4 is even
    }

    #[test]
    fn test_const_context() {
        let arr = [1, 2, 3];
        let size = const_context::get_size(&arr);
        assert_eq!(size, 12);
    }

    #[tokio::test]
    async fn test_async_closure() {
        let result = async_features::async_closure_example().await;
        assert_eq!(result, 15);
    }
}
