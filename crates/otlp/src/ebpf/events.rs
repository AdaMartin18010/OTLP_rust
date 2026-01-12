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
}

impl Default for EventProcessor {
    fn default() -> Self {
        Self::new(1000)
    }
}
