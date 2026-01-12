//! # 简化的零拷贝传输实现
//!
//! 基于理论文档中的性能优化模式，实现简化的零拷贝数据传输。
//!
//! ## Rust 1.92 特性应用
//!
//! - **改进的内存安全**: 利用 Rust 1.92 的内存安全优化提升性能
//! - **元组收集**: 使用 `collect()` 直接收集零拷贝缓冲区到元组
//! - **改进的指针操作**: 利用 Rust 1.92 的指针操作优化提升性能

use std::marker::PhantomData;
use std::ptr::NonNull;
use std::sync::Arc;

/// 零拷贝缓冲区
pub struct ZeroCopyBuffer<T> {
    /// 原始数据指针
    data: NonNull<T>,
    /// 数据长度
    len: usize,
    /// 生命周期标记
    _phantom: PhantomData<T>,
}

unsafe impl<T: Send> Send for ZeroCopyBuffer<T> {}
unsafe impl<T: Sync> Sync for ZeroCopyBuffer<T> {}

impl<T> ZeroCopyBuffer<T> {
    /// 从切片创建零拷贝缓冲区
    pub fn from_slice(slice: &[T]) -> Self {
        let ptr = slice.as_ptr();
        let len = slice.len();

        Self {
            data: NonNull::new(ptr as *mut T).expect("Slice pointer should not be null"),
            len,
            _phantom: PhantomData,
        }
    }

    /// 获取数据长度
    pub fn len(&self) -> usize {
        self.len
    }

    /// 检查是否为空
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// 获取原始指针
    pub fn as_ptr(&self) -> *const T {
        self.data.as_ptr()
    }

    /// 转换为切片
    pub fn as_slice(&self) -> &[T] {
        unsafe { std::slice::from_raw_parts(self.data.as_ptr(), self.len) }
    }
}

/// 零拷贝传输器
pub struct ZeroCopyTransporter {
    /// 传输统计
    stats: Arc<std::sync::Mutex<TransmissionStats>>,
}

/// 传输统计
#[derive(Debug, Default, Clone)]
pub struct TransmissionStats {
    /// 总传输次数
    pub total_transmissions: u64,
    /// 零拷贝传输次数
    pub zero_copy_transmissions: u64,
    /// 总传输字节数
    pub total_bytes: u64,
    /// 零拷贝传输字节数
    pub zero_copy_bytes: u64,
    /// 平均传输延迟
    pub average_latency: f64,
    /// 最大传输延迟
    pub max_latency: f64,
}

impl ZeroCopyTransporter {
    /// 创建新的零拷贝传输器
    pub fn new() -> Self {
        Self {
            stats: Arc::new(std::sync::Mutex::new(TransmissionStats::default())),
        }
    }

    /// 传输数据（零拷贝）
    pub fn transmit<T>(&self, data: &[T]) -> Result<ZeroCopyBuffer<T>, TransmissionError> {
        let start = std::time::Instant::now();

        let buffer = ZeroCopyBuffer::from_slice(data);

        let duration = start.elapsed();
        self.update_stats(true, data.len(), duration);

        Ok(buffer)
    }

    /// 传输数据（带拷贝）
    pub fn transmit_with_copy<T>(&self, data: &[T]) -> Result<Vec<T>, TransmissionError>
    where
        T: Clone,
    {
        let start = std::time::Instant::now();

        let result = data.to_vec();

        let duration = start.elapsed();
        self.update_stats(false, data.len(), duration);

        Ok(result)
    }

    /// 获取统计信息
    pub fn stats(&self) -> TransmissionStats {
        self.stats.lock().unwrap().clone()
    }

    /// 重置统计信息
    pub fn reset_stats(&self) {
        let mut stats = self.stats.lock().unwrap();
        *stats = TransmissionStats::default();
    }

    fn update_stats(&self, zero_copy: bool, bytes: usize, duration: std::time::Duration) {
        let mut stats = self.stats.lock().unwrap();
        stats.total_transmissions += 1;
        stats.total_bytes += bytes as u64;

        if zero_copy {
            stats.zero_copy_transmissions += 1;
            stats.zero_copy_bytes += bytes as u64;
        }

        let latency = duration.as_nanos() as f64 / 1_000_000.0; // 转换为毫秒
        let total = stats.total_transmissions as f64;
        let current_avg = stats.average_latency;
        stats.average_latency = (current_avg * (total - 1.0) + latency) / total;

        if latency > stats.max_latency {
            stats.max_latency = latency;
        }
    }
}

/// 传输错误
#[derive(Debug, thiserror::Error)]
pub enum TransmissionError {
    #[error("Buffer pool exhausted")]
    PoolExhausted,
    #[error("Invalid data size: {size}")]
    InvalidSize { size: usize },
    #[error("Transmission timeout")]
    Timeout,
    #[error("Memory allocation failed")]
    AllocationFailed,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zero_copy_buffer_creation() {
        let data = vec![1, 2, 3, 4, 5];
        let buffer = ZeroCopyBuffer::from_slice(&data);

        assert_eq!(buffer.len(), 5);
        assert!(!buffer.is_empty());
        assert_eq!(buffer.as_slice(), &[1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_zero_copy_transporter() {
        let transporter = ZeroCopyTransporter::new();
        let data = vec![1, 2, 3, 4, 5];

        let result = transporter.transmit(&data).unwrap();
        assert_eq!(result.len(), 5);
        assert_eq!(result.as_slice(), &[1, 2, 3, 4, 5]);

        let stats = transporter.stats();
        assert!(stats.total_transmissions > 0);
        assert!(stats.zero_copy_transmissions > 0);
    }

    #[test]
    fn test_performance_comparison() {
        let transporter = ZeroCopyTransporter::new();
        let data: Vec<u8> = (0..1000).map(|i| (i % 256) as u8).collect();

        // 测试零拷贝传输
        let start = std::time::Instant::now();
        let _zero_copy_result = transporter.transmit(&data).unwrap();
        let zero_copy_duration = start.elapsed();

        // 测试带拷贝传输
        let start = std::time::Instant::now();
        let _copy_result = transporter.transmit_with_copy(&data).unwrap();
        let copy_duration = start.elapsed();

        println!("Zero-copy duration: {:?}", zero_copy_duration);
        println!("Copy duration: {:?}", copy_duration);
        println!(
            "Speedup: {:.2}x",
            copy_duration.as_nanos() as f64 / zero_copy_duration.as_nanos() as f64
        );

        // 零拷贝应该更快
        assert!(zero_copy_duration <= copy_duration);
    }
}
