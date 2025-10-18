//! 异步I/O优化模块
//!
//! 提供高性能的异步网络I/O操作

use anyhow::{Result, anyhow};
use std::collections::VecDeque;
use std::net::{SocketAddr, ToSocketAddrs};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::time::{Duration, Instant};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::{RwLock, Semaphore};
use tokio::time::timeout;

/// 异步I/O统计信息
#[derive(Debug, Default)]
pub struct AsyncIoStats {
    pub total_connections: AtomicUsize,
    pub active_connections: AtomicUsize,
    pub bytes_read: AtomicU64,
    pub bytes_written: AtomicU64,
    pub read_operations: AtomicUsize,
    pub write_operations: AtomicUsize,
    pub connection_errors: AtomicUsize,
    pub timeout_errors: AtomicUsize,
    pub average_latency: AtomicU64, // 微秒
    pub peak_throughput: AtomicU64, // 字节/秒
}

impl Clone for AsyncIoStats {
    fn clone(&self) -> Self {
        Self {
            total_connections: AtomicUsize::new(self.total_connections.load(Ordering::Relaxed)),
            active_connections: AtomicUsize::new(self.active_connections.load(Ordering::Relaxed)),
            bytes_read: AtomicU64::new(self.bytes_read.load(Ordering::Relaxed)),
            bytes_written: AtomicU64::new(self.bytes_written.load(Ordering::Relaxed)),
            read_operations: AtomicUsize::new(self.read_operations.load(Ordering::Relaxed)),
            write_operations: AtomicUsize::new(self.write_operations.load(Ordering::Relaxed)),
            connection_errors: AtomicUsize::new(self.connection_errors.load(Ordering::Relaxed)),
            timeout_errors: AtomicUsize::new(self.timeout_errors.load(Ordering::Relaxed)),
            average_latency: AtomicU64::new(self.average_latency.load(Ordering::Relaxed)),
            peak_throughput: AtomicU64::new(self.peak_throughput.load(Ordering::Relaxed)),
        }
    }
}

/// 异步I/O配置
#[derive(Debug, Clone)]
pub struct AsyncIoConfig {
    pub max_connections: usize,
    pub read_timeout: Duration,
    pub write_timeout: Duration,
    pub connect_timeout: Duration,
    pub keep_alive: bool,
    pub tcp_nodelay: bool,
    pub buffer_size: usize,
    pub max_pending_operations: usize,
}

impl Default for AsyncIoConfig {
    fn default() -> Self {
        Self {
            max_connections: 1000,
            read_timeout: Duration::from_secs(30),
            write_timeout: Duration::from_secs(30),
            connect_timeout: Duration::from_secs(10),
            keep_alive: true,
            tcp_nodelay: true,
            buffer_size: 8192,
            max_pending_operations: 10000,
        }
    }
}

/// 连接信息
#[derive(Debug)]
pub struct ConnectionInfo {
    pub id: usize,
    pub addr: SocketAddr,
    pub connected_at: Instant,
    pub last_activity: std::sync::Mutex<Instant>,
    pub bytes_read: std::sync::Mutex<u64>,
    pub bytes_written: std::sync::Mutex<u64>,
}

impl Clone for ConnectionInfo {
    fn clone(&self) -> Self {
        Self {
            id: self.id,
            addr: self.addr,
            connected_at: self.connected_at,
            last_activity: std::sync::Mutex::new(*self.last_activity.lock().unwrap()),
            bytes_read: std::sync::Mutex::new(*self.bytes_read.lock().unwrap()),
            bytes_written: std::sync::Mutex::new(*self.bytes_written.lock().unwrap()),
        }
    }
}

/// 异步I/O管理器
pub struct AsyncIoManager {
    config: AsyncIoConfig,
    stats: Arc<AsyncIoStats>,
    connections: Arc<RwLock<std::collections::HashMap<usize, Arc<ConnectionInfo>>>>,
    connection_semaphore: Arc<Semaphore>,
    pending_operations: Arc<Semaphore>,
    next_connection_id: AtomicUsize,
}

impl AsyncIoManager {
    /// 创建新的异步I/O管理器
    pub fn new(config: AsyncIoConfig) -> Self {
        let connection_semaphore = Arc::new(Semaphore::new(config.max_connections));
        let pending_operations = Arc::new(Semaphore::new(config.max_pending_operations));

        Self {
            stats: Arc::new(AsyncIoStats::default()),
            connections: Arc::new(RwLock::new(std::collections::HashMap::new())),
            connection_semaphore,
            pending_operations,
            next_connection_id: AtomicUsize::new(1),
            config,
        }
    }

    /// 建立连接
    pub async fn connect<A: ToSocketAddrs + tokio::net::ToSocketAddrs>(
        &self,
        addr: A,
    ) -> Result<AsyncConnection> {
        let _permit = self
            .connection_semaphore
            .acquire()
            .await
            .map_err(|_| anyhow!("Failed to acquire connection permit"))?;

        let stream = timeout(self.config.connect_timeout, TcpStream::connect(addr))
            .await
            .map_err(|_| anyhow!("Connection timeout"))?
            .map_err(|e| anyhow!("Connection failed: {}", e))?;

        // 配置TCP选项
        if self.config.tcp_nodelay {
            stream.set_nodelay(true)?;
        }

        let connection_id = self.next_connection_id.fetch_add(1, Ordering::Relaxed);
        let connection_info = Arc::new(ConnectionInfo {
            id: connection_id,
            addr: stream.peer_addr()?,
            connected_at: Instant::now(),
            last_activity: std::sync::Mutex::new(Instant::now()),
            bytes_read: std::sync::Mutex::new(0),
            bytes_written: std::sync::Mutex::new(0),
        });

        // 注册连接
        {
            let mut connections = self.connections.write().await;
            connections.insert(connection_id, connection_info.clone());
        }

        self.stats.total_connections.fetch_add(1, Ordering::Relaxed);
        self.stats
            .active_connections
            .fetch_add(1, Ordering::Relaxed);

        Ok(AsyncConnection {
            stream,
            info: connection_info,
            stats: self.stats.clone(),
            config: self.config.clone(),
        })
    }

    /// 监听连接
    pub async fn listen<A: ToSocketAddrs + tokio::net::ToSocketAddrs>(
        &self,
        addr: A,
    ) -> Result<AsyncListener> {
        let listener = TcpListener::bind(addr).await?;
        Ok(AsyncListener {
            listener,
            manager: self.clone(),
        })
    }

    /// 获取统计信息
    pub async fn stats(&self) -> AsyncIoStats {
        (*self.stats).clone()
    }

    /// 获取连接信息
    pub async fn get_connections(&self) -> Vec<ConnectionInfo> {
        let connections = self.connections.read().await;
        connections
            .values()
            .map(|info| info.as_ref().clone())
            .collect()
    }

    /// 关闭连接
    pub async fn close_connection(&self, connection_id: usize) {
        let mut connections = self.connections.write().await;
        if connections.remove(&connection_id).is_some() {
            self.stats
                .active_connections
                .fetch_sub(1, Ordering::Relaxed);
        }
    }

    /// 清理过期连接
    pub async fn cleanup_expired_connections(&self, max_age: Duration) {
        let now = Instant::now();
        let mut connections = self.connections.write().await;
        let mut to_remove = Vec::new();

        for (id, info) in connections.iter() {
            if now.duration_since(*info.last_activity.lock().unwrap()) > max_age {
                to_remove.push(*id);
            }
        }

        for id in to_remove {
            connections.remove(&id);
            self.stats
                .active_connections
                .fetch_sub(1, Ordering::Relaxed);
        }
    }
}

impl Clone for AsyncIoManager {
    fn clone(&self) -> Self {
        Self {
            config: self.config.clone(),
            stats: self.stats.clone(),
            connections: self.connections.clone(),
            connection_semaphore: self.connection_semaphore.clone(),
            pending_operations: self.pending_operations.clone(),
            next_connection_id: AtomicUsize::new(0), // 不克隆计数器
        }
    }
}

/// 异步连接
pub struct AsyncConnection {
    stream: TcpStream,
    info: Arc<ConnectionInfo>,
    stats: Arc<AsyncIoStats>,
    config: AsyncIoConfig,
}

impl AsyncConnection {
    /// 异步读取数据
    pub async fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        let _permit = self.stats.read_operations.fetch_add(1, Ordering::Relaxed);

        let start = Instant::now();
        let result = timeout(self.config.read_timeout, self.stream.read(buf)).await;
        let duration = start.elapsed();

        match result {
            Ok(Ok(n)) => {
                self.stats.bytes_read.fetch_add(n as u64, Ordering::Relaxed);
                *self.info.bytes_read.lock().unwrap() += n as u64;
                *self.info.last_activity.lock().unwrap() = Instant::now();

                // 更新平均延迟
                let current_avg = self.stats.average_latency.load(Ordering::Relaxed);
                let new_avg = (current_avg + duration.as_micros() as u64) / 2;
                self.stats.average_latency.store(new_avg, Ordering::Relaxed);

                Ok(n)
            }
            Ok(Err(e)) => {
                self.stats.connection_errors.fetch_add(1, Ordering::Relaxed);
                Err(anyhow!("Read error: {}", e))
            }
            Err(_) => {
                self.stats.timeout_errors.fetch_add(1, Ordering::Relaxed);
                Err(anyhow!("Read timeout"))
            }
        }
    }

    /// 异步写入数据
    pub async fn write(&mut self, buf: &[u8]) -> Result<usize> {
        let _permit = self.stats.write_operations.fetch_add(1, Ordering::Relaxed);

        let start = Instant::now();
        let result = timeout(self.config.write_timeout, self.stream.write_all(buf)).await;
        let duration = start.elapsed();

        match result {
            Ok(Ok(())) => {
                let n = buf.len();
                self.stats
                    .bytes_written
                    .fetch_add(n as u64, Ordering::Relaxed);
                *self.info.bytes_written.lock().unwrap() += n as u64;
                *self.info.last_activity.lock().unwrap() = Instant::now();

                // 更新峰值吞吐量
                let throughput = (n as u64 * 1_000_000) / duration.as_micros() as u64;
                let current_peak = self.stats.peak_throughput.load(Ordering::Relaxed);
                if throughput > current_peak {
                    self.stats
                        .peak_throughput
                        .store(throughput, Ordering::Relaxed);
                }

                Ok(n)
            }
            Ok(Err(e)) => {
                self.stats.connection_errors.fetch_add(1, Ordering::Relaxed);
                Err(anyhow!("Write error: {}", e))
            }
            Err(_) => {
                self.stats.timeout_errors.fetch_add(1, Ordering::Relaxed);
                Err(anyhow!("Write timeout"))
            }
        }
    }

    /// 获取连接信息
    pub fn info(&self) -> &ConnectionInfo {
        &self.info
    }

    /// 关闭连接
    pub async fn close(self) {
        // 连接会在drop时自动关闭
    }
}

/// 异步监听器
pub struct AsyncListener {
    listener: TcpListener,
    manager: AsyncIoManager,
}

impl AsyncListener {
    /// 接受连接
    pub async fn accept(&self) -> Result<AsyncConnection> {
        let (stream, addr) = self.listener.accept().await?;

        // 配置TCP选项
        if self.manager.config.tcp_nodelay {
            stream.set_nodelay(true)?;
        }

        let connection_id = self
            .manager
            .next_connection_id
            .fetch_add(1, Ordering::Relaxed);
        let connection_info = Arc::new(ConnectionInfo {
            id: connection_id,
            addr,
            connected_at: Instant::now(),
            last_activity: std::sync::Mutex::new(Instant::now()),
            bytes_read: std::sync::Mutex::new(0),
            bytes_written: std::sync::Mutex::new(0),
        });

        // 注册连接
        {
            let mut connections = self.manager.connections.write().await;
            connections.insert(connection_id, connection_info.clone());
        }

        self.manager
            .stats
            .total_connections
            .fetch_add(1, Ordering::Relaxed);
        self.manager
            .stats
            .active_connections
            .fetch_add(1, Ordering::Relaxed);

        Ok(AsyncConnection {
            stream,
            info: connection_info,
            stats: self.manager.stats.clone(),
            config: self.manager.config.clone(),
        })
    }

    /// 获取管理器
    pub fn manager(&self) -> &AsyncIoManager {
        &self.manager
    }
}

/// 批量I/O操作
pub struct BatchIo {
    operations: VecDeque<
        Box<
            dyn Fn() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<usize>> + Send>>
                + Send
                + Sync,
        >,
    >,
    max_batch_size: usize,
}

impl BatchIo {
    /// 创建批量I/O操作器
    pub fn new(max_batch_size: usize) -> Self {
        Self {
            operations: VecDeque::new(),
            max_batch_size,
        }
    }

    /// 添加读取操作
    pub fn add_read<F>(&mut self, operation: F)
    where
        F: Fn() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<usize>> + Send>>
            + Send
            + Sync
            + 'static,
    {
        if self.operations.len() < self.max_batch_size {
            self.operations.push_back(Box::new(operation));
        }
    }

    /// 执行批量操作
    pub async fn execute_batch(&mut self) -> Vec<Result<usize>> {
        let mut results = Vec::new();
        let operations: Vec<_> = self.operations.drain(..).collect();

        for operation in operations {
            let result = operation().await;
            results.push(result);
        }

        results
    }

    /// 获取待处理操作数量
    pub fn pending_operations(&self) -> usize {
        self.operations.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_async_io_manager_creation() {
        let config = AsyncIoConfig::default();
        let manager = AsyncIoManager::new(config);
        let stats = manager.stats().await;
        assert_eq!(stats.total_connections.load(Ordering::Relaxed), 0);
    }

    #[tokio::test]
    async fn test_connection_info() {
        let config = AsyncIoConfig::default();
        let manager = AsyncIoManager::new(config);
        let connections = manager.get_connections().await;
        assert!(connections.is_empty());
    }

    #[tokio::test]
    async fn test_batch_io() {
        let mut batch_io = BatchIo::new(10);
        assert_eq!(batch_io.pending_operations(), 0);

        batch_io.add_read(|| Box::pin(async { Ok(42) }));
        assert_eq!(batch_io.pending_operations(), 1);

        let results = batch_io.execute_batch().await;
        assert_eq!(results.len(), 1);
        assert!(results[0].is_ok());
        assert_eq!(results[0].as_ref().unwrap(), &42);
    }
}
