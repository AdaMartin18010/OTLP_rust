//! Const API使用示例
//!
//! 演示如何使用const API实现编译时优化

use otlp::config::{
    validate_batch_size, validate_timeout, DEFAULT_BATCH_SIZE, DEFAULT_TIMEOUT, MAX_BATCH_SIZE,
    MIN_BATCH_SIZE,
};

fn main() {
    // 1. 使用const常量
    println!("默认批处理大小: {}", DEFAULT_BATCH_SIZE);
    println!("最大批处理大小: {}", MAX_BATCH_SIZE);
    println!("最小批处理大小: {}", MIN_BATCH_SIZE);
    println!("默认超时: {:?}", DEFAULT_TIMEOUT);

    // 2. 使用const函数进行编译时验证
    // 注意: 这些函数在编译时无法完全验证，但在运行时可以快速检查

    // 验证批处理大小
    let batch_size = 5000;
    if validate_batch_size(batch_size) {
        println!("批处理大小 {} 有效", batch_size);
    } else {
        println!("批处理大小 {} 无效", batch_size);
    }

    // 验证超时值
    let timeout = DEFAULT_TIMEOUT;
    if validate_timeout(timeout) {
        println!("超时值 {:?} 有效", timeout);
    } else {
        println!("超时值 {:?} 无效", timeout);
    }

    // 3. 使用const常量进行配置
    println!("\n配置已使用const常量，实现编译时优化");
    println!("可以使用这些const常量在编译时进行配置验证");
}

// 示例配置构建器 (简化版)
struct OtlpConfigBuilder {
    batch_size: usize,
    timeout: std::time::Duration,
}

impl OtlpConfigBuilder {
    fn new() -> Self {
        Self {
            batch_size: DEFAULT_BATCH_SIZE,
            timeout: DEFAULT_TIMEOUT,
        }
    }

    fn batch_size(mut self, size: usize) -> Self {
        self.batch_size = size;
        self
    }

    fn timeout(mut self, timeout: std::time::Duration) -> Self {
        self.timeout = timeout;
        self
    }

    fn build(self) -> Self {
        self
    }
}
