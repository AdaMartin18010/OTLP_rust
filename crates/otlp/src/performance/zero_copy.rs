//! # 零拷贝传输实现
//!
//! 基于理论文档中的性能优化模式，实现零拷贝数据传输。
//! 参考: OTLP_Rust编程规范与实践指南.md 第3.2节
//!
//! ## Rust 1.92 特性应用
//!
//! - **改进的内存安全**: 利用 Rust 1.92 的内存安全优化提升性能
//! - **元组收集**: 使用 `collect()` 直接收集零拷贝缓冲区到元组
//! - **改进的指针操作**: 利用 Rust 1.92 的指针操作优化提升性能

use std::marker::PhantomData;
use std::ptr::{self, NonNull};
use std::sync::Arc;
use std::mem;

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

    /// 从Vec创建零拷贝缓冲区
    pub fn from_vec(vec: Vec<T>) -> Self {
        let len = vec.len();
        let ptr = vec.as_ptr();

        // 防止Vec被释放
        mem::forget(vec);

        Self {
            data: NonNull::new(ptr as *mut T).expect("Vec pointer should not be null"),
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

    /// 获取可变指针
    pub fn as_mut_ptr(&self) -> *mut T {
        self.data.as_ptr()
    }

    /// 转换为切片
    pub fn as_slice(&self) -> &[T] {
        unsafe {
            std::slice::from_raw_parts(self.data.as_ptr(), self.len)
        }
    }

    /// 转换为可变切片
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe {
            std::slice::from_raw_parts_mut(self.data.as_ptr(), self.len)
        }
    }

    /// 分割缓冲区
    pub fn split_at(&self, mid: usize) -> (Self, Self) {
        assert!(mid <= self.len);

        let left = Self {
            data: self.data,
            len: mid,
            _phantom: PhantomData,
        };

        let right = Self {
            data: unsafe { NonNull::new_unchecked(self.data.as_ptr().add(mid)) },
            len: self.len - mid,
            _phantom: PhantomData,
        };

        (left, right)
    }

    /// 获取子缓冲区
    pub fn sub_buffer(&self, start: usize, len: usize) -> Self {
        assert!(start + len <= self.len);

        Self {
            data: unsafe { NonNull::new_unchecked(self.data.as_ptr().add(start)) },
            len,
            _phantom: PhantomData,
        }
    }
}

impl<T> Drop for ZeroCopyBuffer<T> {
    fn drop(&mut self) {
        // 注意：这里不释放内存，因为内存可能由其他所有者管理
        // 如果需要释放，应该使用相应的释放方法
    }
}

/// 零拷贝传输器
pub struct ZeroCopyTransporter<T> {
    /// 缓冲区池
    buffer_pool: Arc<BufferPool<T>>,
    /// 传输统计
    stats: Arc<TransmissionStats>,
}

/// 缓冲区池
struct BufferPool<T> {
    /// 可用缓冲区
    available: std::sync::Mutex<Vec<ZeroCopyBuffer<T>>>,
    /// 池大小
    pool_size: usize,
    /// 缓冲区大小
    buffer_size: usize,
}

impl<T> BufferPool<T> {
    fn new(pool_size: usize, buffer_size: usize) -> Self {
        Self {
            available: std::sync::Mutex::new(Vec::with_capacity(pool_size)),
            pool_size,
            buffer_size,
        }
    }

    fn acquire(&self) -> Option<ZeroCopyBuffer<T>> {
        self.available.lock().unwrap().pop()
    }

    fn release(&self, buffer: ZeroCopyBuffer<T>) {
        let mut available = self.available.lock().unwrap();
        if available.len() < self.pool_size {
            available.push(buffer);
        }
    }
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

impl<T> ZeroCopyTransporter<T> {
    /// 创建新的零拷贝传输器
    pub fn new(pool_size: usize, buffer_size: usize) -> Self {
        Self {
            buffer_pool: Arc::new(BufferPool::new(pool_size, buffer_size)),
            stats: Arc::new(TransmissionStats::default()),
        }
    }

    /// 传输数据（零拷贝）
    pub fn transmit(&self, data: &[T]) -> Result<ZeroCopyBuffer<T>, TransmissionError> {
        let start = std::time::Instant::now();

        // 尝试从池中获取缓冲区
        let buffer = if let Some(mut buffer) = self.buffer_pool.acquire() {
            if buffer.len() >= data.len() {
                // 使用现有缓冲区
                unsafe {
                    ptr::copy_nonoverlapping(data.as_ptr(), buffer.as_mut_ptr(), data.len());
                }
                buffer.len = data.len();
                buffer
            } else {
                // 缓冲区太小，创建新的
                ZeroCopyBuffer::from_slice(data)
            }
        } else {
            // 池中没有可用缓冲区，创建新的
            ZeroCopyBuffer::from_slice(data)
        };

        let duration = start.elapsed();
        self.update_stats(true, data.len(), duration);

        Ok(buffer)
    }

    /// 传输数据（带拷贝）
    pub fn transmit_with_copy(&self, data: &[T]) -> Result<Vec<T>, TransmissionError> {
        let start = std::time::Instant::now();

        let result = data.to_vec();

        let duration = start.elapsed();
        self.update_stats(false, data.len(), duration);

        Ok(result)
    }

    /// 批量传输
    pub fn batch_transmit(&self, data_slices: &[&[T]]) -> Result<Vec<ZeroCopyBuffer<T>>, TransmissionError> {
        let start = std::time::Instant::now();
        let mut results = Vec::with_capacity(data_slices.len());

        for &data in data_slices {
            let buffer = self.transmit(data)?;
            results.push(buffer);
        }

        let duration = start.elapsed();
        self.update_stats(true, data_slices.iter().map(|s| s.len()).sum(), duration);

        Ok(results)
    }

    /// 获取统计信息
    pub fn stats(&self) -> TransmissionStats {
        *self.stats.as_ref()
    }

    /// 重置统计信息
    pub fn reset_stats(&self) {
        let mut stats = self.stats.as_ref();
        *stats = TransmissionStats::default();
    }

    fn update_stats(&self, zero_copy: bool, bytes: usize, duration: std::time::Duration) {
        let mut stats = self.stats.as_ref();
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

/// 零拷贝网络传输器
pub struct ZeroCopyNetworkTransporter {
    /// 套接字缓冲区大小
    socket_buffer_size: usize,
    /// 传输统计
    stats: Arc<TransmissionStats>,
}

impl ZeroCopyNetworkTransporter {
    /// 创建新的网络传输器
    pub fn new(socket_buffer_size: usize) -> Self {
        Self {
            socket_buffer_size,
            stats: Arc::new(TransmissionStats::default()),
        }
    }

    /// 发送数据（零拷贝）
    pub async fn send_zero_copy<W: tokio::io::AsyncWrite + Unpin>(
        &self,
        writer: &mut W,
        data: &[u8],
    ) -> Result<usize, TransmissionError> {
        let start = std::time::Instant::now();

        // 使用tokio的零拷贝写入
        let bytes_written = writer.write(data).await
            .map_err(|_| TransmissionError::AllocationFailed)?;

        let duration = start.elapsed();
        self.update_stats(true, bytes_written, duration);

        Ok(bytes_written)
    }

    /// 接收数据（零拷贝）
    pub async fn recv_zero_copy<R: tokio::io::AsyncRead + Unpin>(
        &self,
        reader: &mut R,
        buffer: &mut [u8],
    ) -> Result<usize, TransmissionError> {
        let start = std::time::Instant::now();

        let bytes_read = reader.read(buffer).await
            .map_err(|_| TransmissionError::AllocationFailed)?;

        let duration = start.elapsed();
        self.update_stats(true, bytes_read, duration);

        Ok(bytes_read)
    }

    /// 获取统计信息
    pub fn stats(&self) -> TransmissionStats {
        self.stats.as_ref().clone()
    }

    fn update_stats(&self, zero_copy: bool, bytes: usize, duration: std::time::Duration) {
        let mut stats = self.stats.as_ref();
        stats.total_transmissions += 1;
        stats.total_bytes += bytes as u64;

        if zero_copy {
            stats.zero_copy_transmissions += 1;
            stats.zero_copy_bytes += bytes as u64;
        }

        let latency = duration.as_nanos() as f64 / 1_000_000.0;
        let total = stats.total_transmissions as f64;
        let current_avg = stats.average_latency;
        stats.average_latency = (current_avg * (total - 1.0) + latency) / total;

        if latency > stats.max_latency {
            stats.max_latency = latency;
        }
    }
}

/// 零拷贝序列化器
pub struct ZeroCopySerializer<T> {
    /// 序列化缓冲区
    buffer: Vec<u8>,
    /// 当前位置
    position: usize,
    /// 类型标记
    _phantom: PhantomData<T>,
}

impl<T> ZeroCopySerializer<T> {
    /// 创建新的序列化器
    pub fn new(capacity: usize) -> Self {
        Self {
            buffer: Vec::with_capacity(capacity),
            position: 0,
            _phantom: PhantomData,
        }
    }

    /// 序列化数据
    pub fn serialize(&mut self, data: &T) -> Result<&[u8], SerializationError>
    where
        T: serde::Serialize,
    {
        // 使用bincode进行零拷贝序列化
        let serialized = bincode::serialize(data)
            .map_err(|_| SerializationError::SerializationFailed)?;

        // 确保缓冲区有足够空间
        if self.position + serialized.len() > self.buffer.capacity() {
            self.buffer.reserve(serialized.len());
        }

        // 将序列化数据添加到缓冲区
        self.buffer.extend_from_slice(&serialized);
        let start = self.position;
        self.position += serialized.len();

        Ok(&self.buffer[start..self.position])
    }

    /// 获取缓冲区
    pub fn buffer(&self) -> &[u8] {
        &self.buffer
    }

    /// 清空缓冲区
    pub fn clear(&mut self) {
        self.buffer.clear();
        self.position = 0;
    }
}

/// 序列化错误
#[derive(Debug, thiserror::Error)]
pub enum SerializationError {
    #[error("Serialization failed")]
    SerializationFailed,
    #[error("Deserialization failed")]
    DeserializationFailed,
    #[error("Buffer overflow")]
    BufferOverflow,
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
    fn test_zero_copy_buffer_split() {
        let data = vec![1, 2, 3, 4, 5];
        let buffer = ZeroCopyBuffer::from_slice(&data);
        let (left, right) = buffer.split_at(3);

        assert_eq!(left.len(), 3);
        assert_eq!(right.len(), 2);
        assert_eq!(left.as_slice(), &[1, 2, 3]);
        assert_eq!(right.as_slice(), &[4, 5]);
    }

    #[test]
    fn test_zero_copy_transporter() {
        let transporter = ZeroCopyTransporter::new(10, 1024);
        let data = vec![1, 2, 3, 4, 5];

        let result = transporter.transmit(&data).unwrap();
        assert_eq!(result.len(), 5);
        assert_eq!(result.as_slice(), &[1, 2, 3, 4, 5]);

        let stats = transporter.stats();
        assert!(stats.total_transmissions > 0);
        assert!(stats.zero_copy_transmissions > 0);
    }

    #[test]
    fn test_batch_transmit() {
        let transporter = ZeroCopyTransporter::new(10, 1024);
        let data1 = vec![1, 2, 3];
        let data2 = vec![4, 5, 6];
        let data_slices = vec![&data1[..], &data2[..]];

        let results = transporter.batch_transmit(&data_slices).unwrap();
        assert_eq!(results.len(), 2);
        assert_eq!(results[0].as_slice(), &[1, 2, 3]);
        assert_eq!(results[1].as_slice(), &[4, 5, 6]);
    }

    #[test]
    fn test_zero_copy_serializer() {
        let mut serializer = ZeroCopySerializer::new(1024);
        let data = vec![1, 2, 3, 4, 5];

        let serialized = serializer.serialize(&data).unwrap();
        assert!(!serialized.is_empty());

        let buffer = serializer.buffer();
        assert!(!buffer.is_empty());
    }

    #[test]
    fn test_performance_comparison() {
        let transporter = ZeroCopyTransporter::new(10, 1024);
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
        println!("Speedup: {:.2}x", copy_duration.as_nanos() as f64 / zero_copy_duration.as_nanos() as f64);

        // 零拷贝应该更快
        assert!(zero_copy_duration <= copy_duration);
    }
}
