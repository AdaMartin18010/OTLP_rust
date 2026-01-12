//! 事件处理
//!
//! 处理从 eBPF 程序收集的事件

use crate::error::Result;
use crate::ebpf::types::{EbpfEvent, EbpfEventType};

/// 事件处理器
pub struct EventProcessor {
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    event_buffer: Vec<EbpfEvent>,
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    max_buffer_size: usize,
}

impl EventProcessor {
    /// 创建新的事件处理器
    pub fn new(max_buffer_size: usize) -> Self {
        Self {
            #[cfg(all(feature = "ebpf", target_os = "linux"))]
            event_buffer: Vec::with_capacity(max_buffer_size),
            #[cfg(all(feature = "ebpf", target_os = "linux"))]
            max_buffer_size,
        }
    }

    /// 处理事件
    #[cfg(all(feature = "ebpf", target_os = "linux"))]
    pub fn process_event(&mut self, event: EbpfEvent) -> Result<()> {
        // TODO: 实际实现需要:
        // 1. 验证事件数据
        // 2. 转换事件格式
        // 3. 缓冲或立即处理

        if self.event_buffer.len() >= self.max_buffer_size {
            // 缓冲区满，处理并清空
            self.flush_events()?;
        }

        self.event_buffer.push(event);
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
}

impl Default for EventProcessor {
    fn default() -> Self {
        Self::new(1000)
    }
}
