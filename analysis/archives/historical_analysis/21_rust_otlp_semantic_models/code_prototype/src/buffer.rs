//! 无锁缓冲区

use crossbeam::queue::ArrayQueue;
use std::sync::Arc;
use crate::span::Span;

/// 无锁环形缓冲区
pub struct LockFreeBuffer {
    queue: Arc<ArrayQueue<Span>>,
}

impl LockFreeBuffer {
    /// 创建新缓冲区
    pub fn new(capacity: usize) -> Self {
        Self {
            queue: Arc::new(ArrayQueue::new(capacity)),
        }
    }
    
    /// 推送 Span
    pub fn push(&self, span: Span) -> Result<(), Span> {
        self.queue.push(span)
    }
    
    /// 弹出 Span
    pub fn pop(&self) -> Option<Span> {
        self.queue.pop()
    }
    
    /// 批量弹出
    pub fn pop_batch(&self, max_size: usize) -> Vec<Span> {
        let mut batch = Vec::with_capacity(max_size);
        
        for _ in 0..max_size {
            if let Some(span) = self.queue.pop() {
                batch.push(span);
            } else {
                break;
            }
        }
        
        batch
    }
    
    /// 当前大小
    pub fn len(&self) -> usize {
        self.queue.len()
    }
    
    /// 是否为空
    pub fn is_empty(&self) -> bool {
        self.queue.is_empty()
    }
    
    /// 容量
    pub fn capacity(&self) -> usize {
        self.queue.capacity()
    }
    
    /// 克隆队列引用
    pub fn clone_queue(&self) -> Arc<ArrayQueue<Span>> {
        Arc::clone(&self.queue)
    }
}

impl Clone for LockFreeBuffer {
    fn clone(&self) -> Self {
        Self {
            queue: Arc::clone(&self.queue),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_buffer_basic() {
        let buffer = LockFreeBuffer::new(100);
        
        let span = Span::new("test".to_string());
        assert!(buffer.push(span.clone()).is_ok());
        
        assert_eq!(buffer.len(), 1);
        
        let popped = buffer.pop().unwrap();
        assert_eq!(popped.name, "test");
        
        assert_eq!(buffer.len(), 0);
    }
    
    #[test]
    fn test_buffer_full() {
        let buffer = LockFreeBuffer::new(2);
        
        let span1 = Span::new("span1".to_string());
        let span2 = Span::new("span2".to_string());
        let span3 = Span::new("span3".to_string());
        
        assert!(buffer.push(span1).is_ok());
        assert!(buffer.push(span2).is_ok());
        assert!(buffer.push(span3).is_err()); // 缓冲区已满
    }
    
    #[test]
    fn test_pop_batch() {
        let buffer = LockFreeBuffer::new(100);
        
        for i in 0..10 {
            let span = Span::new(format!("span-{}", i));
            buffer.push(span).unwrap();
        }
        
        let batch = buffer.pop_batch(5);
        assert_eq!(batch.len(), 5);
        assert_eq!(buffer.len(), 5);
    }
}

