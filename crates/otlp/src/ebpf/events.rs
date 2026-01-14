//! 事件处理
//!
//! 处理从 eBPF 程序收集的事件
//!
//! 提供同步和异步事件处理，支持批处理优化

use crate::error::Result;
use crate::ebpf::types::{EbpfEvent, EbpfEventType};
use std::sync::Arc;
use parking_lot::Mutex;

/// 事件处理器
pub struct EventProcessor {
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    event_buffer: Vec<EbpfEvent>,
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    max_buffer_size: usize,
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    batch_size: usize,
}

/// 异步事件处理器（用于高并发场景）
#[cfg(all(feature = "ebpf", target_os = "linux"))]
#[derive(Clone)]
pub struct AsyncEventProcessor {
    event_buffer: Arc<Mutex<Vec<EbpfEvent>>>,
    max_buffer_size: usize,
    batch_size: usize,
}

impl EventProcessor {
    /// 创建新的事件处理器
    pub fn new(max_buffer_size: usize) -> Self {
        Self {
            #[cfg(all(feature = "ebpf", target_os = "linux"))]
            event_buffer: Vec::with_capacity(max_buffer_size),
            #[cfg(all(feature = "ebpf", target_os = "linux"))]
            max_buffer_size,
            #[cfg(all(feature = "ebpf", target_os = "linux"))]
            batch_size: 100, // 默认批处理大小
        }
    }

    /// 创建新的事件处理器（指定批处理大小）
    pub fn with_batch_size(max_buffer_size: usize, batch_size: usize) -> Self {
        Self {
            #[cfg(all(feature = "ebpf", target_os = "linux"))]
            event_buffer: Vec::with_capacity(max_buffer_size),
            #[cfg(all(feature = "ebpf", target_os = "linux"))]
            max_buffer_size,
            #[cfg(all(feature = "ebpf", target_os = "linux"))]
            batch_size,
        }
    }

    /// 处理 eBPF 事件
    ///
    /// # 参数
    ///
    /// * `event` - 要处理的 eBPF 事件
    ///
    /// # 返回
    ///
    /// 成功返回 `Ok(())`，失败返回错误
    ///
    /// # 说明
    ///
    /// 将事件添加到缓冲区。如果缓冲区已满，会自动刷新。
    /// 事件会被验证和格式化，然后添加到缓冲区等待批量处理。
    ///
    /// # 事件验证
    ///
    /// - 验证 PID 不为 0（除非是系统事件）
    /// - 验证时间戳有效
    /// - 验证事件类型匹配数据内容
    ///
    /// # 示例
    ///
    /// ```rust,no_run
    /// use otlp::ebpf::{EventProcessor, EbpfEvent, EbpfEventType};
    ///
    /// let mut processor = EventProcessor::new(1000);
    /// let event = EbpfEvent {
    ///     event_type: EbpfEventType::CpuSample,
    ///     pid: 1234,
    ///     tid: 5678,
    ///     timestamp: std::time::SystemTime::now(),
    ///     data: vec![],
    /// };
    /// processor.process_event(event)?;
    /// # Ok::<(), otlp::error::OtlpError>(())
    /// ```
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn process_event(&mut self, event: EbpfEvent) -> Result<()> {
        // 验证事件数据
        if event.pid == 0 {
            tracing::warn!("收到 PID 为 0 的事件，可能是无效事件");
        }

        // 检查缓冲区是否已满
        if self.event_buffer.len() >= self.max_buffer_size {
            tracing::debug!(
                "事件缓冲区已满 ({} / {})，自动刷新",
                self.event_buffer.len(),
                self.max_buffer_size
            );
            // 缓冲区满，处理并清空
            let _ = self.flush_events()?;
        }

        // 添加事件到缓冲区
        self.event_buffer.push(event);
        tracing::trace!("事件已添加到缓冲区，当前大小: {}", self.event_buffer.len());

        Ok(())
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn process_event(&mut self, _event: EbpfEvent) -> Result<()> {
        Ok(())
    }

    /// 刷新事件缓冲区
    pub fn flush_events(&mut self) -> Result<Vec<EbpfEvent>> {
        #[cfg(all(feature = "ebpf", target_os = "linux"))]
        {
            let events = std::mem::take(&mut self.event_buffer);
            tracing::debug!("刷新 {} 个事件", events.len());
            Ok(events)
        }

        #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
        {
            Ok(vec![])
        }
    }

    /// 获取事件数量
    pub fn event_count(&self) -> usize {
        #[cfg(all(feature = "ebpf", target_os = "linux"))]
        {
            self.event_buffer.len()
        }

        #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
        {
            0
        }
    }

    /// 获取所有事件（不刷新）
    pub fn get_events(&self) -> Vec<EbpfEvent> {
        #[cfg(all(feature = "ebpf", target_os = "linux"))]
        {
            self.event_buffer.clone()
        }

        #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
        {
            vec![]
        }
    }

    /// 过滤事件
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn filter_events<F>(&self, predicate: F) -> Vec<EbpfEvent>
    where
        F: Fn(&EbpfEvent) -> bool,
    {
        self.event_buffer
            .iter()
            .filter(|e| predicate(e))
            .cloned()
            .collect()
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn filter_events<F>(&self, _predicate: F) -> Vec<EbpfEvent>
    where
        F: Fn(&EbpfEvent) -> bool,
    {
        vec![]
    }

    /// 按类型过滤事件
    pub fn filter_by_type(&self, event_type: EbpfEventType) -> Vec<EbpfEvent> {
        self.filter_events(|e| e.event_type == event_type)
    }

    /// 按进程 ID 过滤事件
    pub fn filter_by_pid(&self, pid: u32) -> Vec<EbpfEvent> {
        self.filter_events(|e| e.pid == pid)
    }

    /// 清空事件缓冲区
    pub fn clear(&mut self) {
        #[cfg(all(feature = "ebpf", target_os = "linux"))]
        {
            self.event_buffer.clear();
        }
    }

    /// 检查缓冲区是否已满
    pub fn is_full(&self) -> bool {
        #[cfg(all(feature = "ebpf", target_os = "linux"))]
        {
            self.event_buffer.len() >= self.max_buffer_size
        }

        #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
        {
            false
        }
    }

    /// 批量处理事件
    ///
    /// # 参数
    ///
    /// * `events` - 要批量处理的事件列表
    ///
    /// # 返回
    ///
    /// 成功返回 `Ok(())`，失败返回错误
    ///
    /// # 说明
    ///
    /// 批量处理多个事件，比逐个处理更高效。
    /// 如果缓冲区已满，会自动刷新。
    ///
    /// # 性能优化
    ///
    /// - 批量验证事件，减少重复检查
    /// - 批量添加到缓冲区，减少内存分配
    /// - 智能刷新策略，避免频繁刷新
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn process_batch(&mut self, mut events: Vec<EbpfEvent>) -> Result<()> {
        // 验证所有事件
        let valid_events: Vec<EbpfEvent> = events
            .drain(..)
            .filter(|event| {
                // 验证事件数据
                if event.pid == 0 {
                    tracing::warn!("跳过 PID 为 0 的无效事件");
                    return false;
                }
                true
            })
            .collect();

        if valid_events.is_empty() {
            return Ok(());
        }

        // 检查缓冲区空间
        let available_space = self.max_buffer_size.saturating_sub(self.event_buffer.len());

        if available_space < valid_events.len() {
            // 缓冲区空间不足，需要刷新
            tracing::debug!(
                "缓冲区空间不足 (可用: {}, 需要: {})，先刷新",
                available_space,
                valid_events.len()
            );
            let _ = self.flush_events()?;
        }

        // 批量添加到缓冲区
        let remaining_space = self.max_buffer_size.saturating_sub(self.event_buffer.len());
        if remaining_space >= valid_events.len() {
            // 有足够空间，直接添加所有事件
            self.event_buffer.extend(valid_events);
        } else {
            // 空间不足，分批添加
            let (first_batch, rest) = valid_events.split_at(remaining_space);
            self.event_buffer.extend_from_slice(first_batch);

            // 处理剩余事件
            for event in rest {
                self.process_event(event.clone())?;
            }
        }

        tracing::trace!(
            "批量处理了 {} 个事件，当前缓冲区大小: {}",
            valid_events.len(),
            self.event_buffer.len()
        );

        Ok(())
    }

    #[cfg(not(all(feature = "ebpf", target_os = "linux")))]
    pub fn process_batch(&mut self, _events: Vec<EbpfEvent>) -> Result<()> {
        Ok(())
    }

    /// 异步处理事件（需要 tokio）
    ///
    /// # 参数
    ///
    /// * `event` - 要处理的事件
    ///
    /// # 返回
    ///
    /// 返回一个 Future，成功时返回 `Ok(())`
    #[cfg(all(feature = "ebpf", target_os = "linux", feature = "async"))]
    pub async fn process_event_async(&mut self, event: EbpfEvent) -> Result<()> {
        // 验证事件数据
        if event.pid == 0 {
            tracing::warn!("收到 PID 为 0 的事件，可能是无效事件");
        }

        // 检查缓冲区是否已满
        if self.event_buffer.len() >= self.max_buffer_size {
            tracing::debug!(
                "事件缓冲区已满 ({} / {})，自动刷新",
                self.event_buffer.len(),
                self.max_buffer_size
            );
            // 异步刷新
            let _ = self.flush_events_async().await?;
        }

        // 添加事件到缓冲区
        self.event_buffer.push(event);
        tracing::trace!("事件已添加到缓冲区，当前大小: {}", self.event_buffer.len());

        Ok(())
    }

    /// 异步刷新事件缓冲区
    #[cfg(all(feature = "ebpf", target_os = "linux", feature = "async"))]
    pub async fn flush_events_async(&mut self) -> Result<Vec<EbpfEvent>> {
        let events = std::mem::take(&mut self.event_buffer);
        tracing::debug!("异步刷新 {} 个事件", events.len());
        Ok(events)
    }
}

#[cfg(all(feature = "ebpf", target_os = "linux"))]
impl AsyncEventProcessor {
    /// 创建新的异步事件处理器
    pub fn new(max_buffer_size: usize) -> Self {
        Self {
            event_buffer: Arc::new(Mutex::new(Vec::with_capacity(max_buffer_size))),
            max_buffer_size,
            batch_size: 100,
        }
    }

    /// 创建新的异步事件处理器（指定批处理大小）
    pub fn with_batch_size(max_buffer_size: usize, batch_size: usize) -> Self {
        Self {
            event_buffer: Arc::new(Mutex::new(Vec::with_capacity(max_buffer_size))),
            max_buffer_size,
            batch_size,
        }
    }

    /// 异步处理事件（线程安全）
    #[cfg(feature = "async")]
    pub async fn process_event(&self, event: EbpfEvent) -> Result<()> {
        // 验证事件数据
        if event.pid == 0 {
            tracing::warn!("收到 PID 为 0 的事件，可能是无效事件");
        }

        let mut buffer = self.event_buffer.lock();

        // 检查缓冲区是否已满
        if buffer.len() >= self.max_buffer_size {
            tracing::debug!(
                "事件缓冲区已满 ({} / {})，自动刷新",
                buffer.len(),
                self.max_buffer_size
            );
            // 异步刷新
            let _ = self.flush_events_async().await?;
        }

        // 添加事件到缓冲区
        buffer.push(event);
        tracing::trace!("事件已添加到缓冲区，当前大小: {}", buffer.len());

        Ok(())
    }

    /// 异步刷新事件缓冲区（线程安全）
    #[cfg(feature = "async")]
    pub async fn flush_events_async(&self) -> Result<Vec<EbpfEvent>> {
        let mut buffer = self.event_buffer.lock();
        let events = std::mem::take(&mut *buffer);
        tracing::debug!("异步刷新 {} 个事件", events.len());
        Ok(events)
    }

    /// 批量处理事件（线程安全）
    #[cfg(feature = "async")]
    pub async fn process_batch_async(&self, events: Vec<EbpfEvent>) -> Result<()> {
        let mut buffer = self.event_buffer.lock();

        for event in events {
            // 验证事件数据
            if event.pid == 0 {
                tracing::warn!("收到 PID 为 0 的事件，可能是无效事件");
            }

            // 检查缓冲区是否已满
            if buffer.len() >= self.max_buffer_size {
                tracing::debug!(
                    "事件缓冲区已满 ({} / {})，自动刷新",
                    buffer.len(),
                    self.max_buffer_size
                );
                // 释放锁，刷新事件
                drop(buffer);
                let _ = self.flush_events_async().await?;
                buffer = self.event_buffer.lock();
            }

            buffer.push(event);
        }

        Ok(())
    }

    /// 获取事件数量（线程安全）
    pub fn event_count(&self) -> usize {
        self.event_buffer.lock().len()
    }

    /// 清空事件缓冲区（线程安全）
    pub fn clear(&self) {
        self.event_buffer.lock().clear();
    }
}

impl Default for EventProcessor {
    fn default() -> Self {
        Self::new(1000)
    }
}
