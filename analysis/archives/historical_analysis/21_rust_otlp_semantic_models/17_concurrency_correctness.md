# 并发正确性验证

> **版本**: Rust 1.90  
> **日期**: 2025年10月2日  
> **主题**: 并发安全、数据竞争、死锁预防

---

## 📋 目录

- [并发正确性验证](#并发正确性验证)
  - [📋 目录](#-目录)
  - [并发安全基础](#并发安全基础)
    - [Send 与 Sync](#send-与-sync)
  - [数据竞争自由性](#数据竞争自由性)
    - [Happens-Before 关系](#happens-before-关系)
  - [死锁预防](#死锁预防)
    - [偏序锁获取](#偏序锁获取)
  - [无锁并发](#无锁并发)
    - [CAS (Compare-And-Swap)](#cas-compare-and-swap)
  - [OTLP 并发设计](#otlp-并发设计)
    - [无锁 Span 收集器](#无锁-span-收集器)
    - [并发批处理器](#并发批处理器)

---

## 并发安全基础

### Send 与 Sync

**定理**: Rust 的 Send + Sync 保证线程安全

**形式化定义**:

```text
T: Send ⇔ T 的所有权可安全地在线程间转移
T: Sync ⇔ &T 可安全地在线程间共享

推论:
  T: Sync ⇒ &T: Send
  T: Send + Sync ⇒ Arc<T>: Send + Sync
```

**代码验证**:

```rust
use std::sync::Arc;
use std::thread;

/// 证明: Arc<T> where T: Send + Sync 是线程安全的
fn prove_arc_safety<T: Send + Sync + 'static>(data: T) {
    let arc = Arc::new(data);
    
    let handles: Vec<_> = (0..10)
        .map(|_| {
            let arc_clone = Arc::clone(&arc);
            thread::spawn(move || {
                // 多线程安全访问
                drop(arc_clone);
            })
        })
        .collect();
    
    for h in handles {
        h.join().unwrap();
    }
}
```

---

## 数据竞争自由性

### Happens-Before 关系

**定义 (Lamport, 1978)**:

```text
e₁ → e₂ (e₁ happens-before e₂) ⇔

1. e₁, e₂ 在同一线程且 e₁ 先于 e₂，或
2. e₁ 是发送，e₂ 是接收同一消息，或  
3. ∃ e₃, e₁ → e₃ ∧ e₃ → e₂ (传递性)

数据竞争自由 ⇔
  ∀ 内存位置 x, ∀ 写 w, ∀ 访问 a,
    (a ≠ w) ⇒ (w → a ∨ a → w)
```

**Rust 保证**:

```rust
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

/// Atomic + Release/Acquire 建立 happens-before
fn release_acquire_example() {
    let flag = Arc::new(AtomicBool::new(false));
    let data = Arc::new(std::sync::Mutex::new(0));
    
    // 线程 1: 写入者
    {
        let flag = Arc::clone(&flag);
        let data = Arc::clone(&data);
        thread::spawn(move || {
            *data.lock().unwrap() = 42;
            flag.store(true, Ordering::Release); // Release 写
        });
    }
    
    // 线程 2: 读取者
    {
        let flag = Arc::clone(&flag);
        let data = Arc::clone(&data);
        thread::spawn(move || {
            while !flag.load(Ordering::Acquire) { // Acquire 读
                thread::yield_now();
            }
            // 保证能看到线程 1 的所有写入
            assert_eq!(*data.lock().unwrap(), 42);
        });
    }
}
```

---

## 死锁预防

### 偏序锁获取

**定理**: 按固定偏序获取锁可避免死锁

**证明 (反证法)**:

```text
假设存在死锁 ⇒ 存在循环等待

设: T₁ 持有 L₁ 等待 L₂
    T₂ 持有 L₂ 等待 L₃
    ...
    Tₙ 持有 Lₙ 等待 L₁

由锁获取规则: L₁ < L₂ < L₃ < ... < Lₙ < L₁
⇒ L₁ < L₁ (矛盾: < 是严格偏序，反自反)

∴ 不存在死锁
```

**Rust 实现**:

```rust
use std::sync::Mutex;

struct Account {
    id: u64,
    balance: Mutex<f64>,
}

impl Account {
    /// 按 ID 顺序获取锁，避免死锁
    fn transfer(from: &Account, to: &Account, amount: f64) {
        let (first, second) = if from.id < to.id {
            (&from.balance, &to.balance)
        } else {
            (&to.balance, &from.balance)
        };
        
        let mut first_lock = first.lock().unwrap();
        let mut second_lock = second.lock().unwrap();
        
        *first_lock -= amount;
        *second_lock += amount;
    }
}
```

---

## 无锁并发

### CAS (Compare-And-Swap)

```rust
use std::sync::atomic::{AtomicU64, Ordering};

/// 无锁计数器
struct LockFreeCounter {
    count: AtomicU64,
}

impl LockFreeCounter {
    fn new() -> Self {
        Self {
            count: AtomicU64::new(0),
        }
    }
    
    /// 原子递增
    fn increment(&self) -> u64 {
        self.count.fetch_add(1, Ordering::SeqCst)
    }
    
    /// CAS 循环
    fn add_if_below_max(&self, value: u64, max: u64) -> Result<u64, u64> {
        let mut current = self.count.load(Ordering::SeqCst);
        
        loop {
            if current >= max {
                return Err(current);
            }
            
            let new = current + value;
            
            match self.count.compare_exchange(
                current,
                new,
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                Ok(_) => return Ok(new),
                Err(actual) => current = actual, // 重试
            }
        }
    }
}
```

---

## OTLP 并发设计

### 无锁 Span 收集器

```rust
use crossbeam::queue::ArrayQueue;

/// 无锁 Span 队列
pub struct LockFreeSpanCollector {
    queue: ArrayQueue<Span>,
}

impl LockFreeSpanCollector {
    pub fn new(capacity: usize) -> Self {
        Self {
            queue: ArrayQueue::new(capacity),
        }
    }
    
    /// 无锁添加 Span
    pub fn add_span(&self, span: Span) -> Result<(), Span> {
        self.queue.push(span)
    }
    
    /// 批量取出
    pub fn drain(&self) -> Vec<Span> {
        let mut spans = Vec::new();
        while let Some(span) = self.queue.pop() {
            spans.push(span);
        }
        spans
    }
}

struct Span;
```

### 并发批处理器

```rust
use tokio::sync::Notify;
use std::sync::Arc;

/// 并发安全的批处理器
pub struct ConcurrentBatchProcessor {
    buffer: Arc<Mutex<Vec<Span>>>,
    batch_size: usize,
    notify: Arc<Notify>,
}

impl ConcurrentBatchProcessor {
    pub fn new(batch_size: usize) -> Self {
        let processor = Self {
            buffer: Arc::new(Mutex::new(Vec::new())),
            batch_size,
            notify: Arc::new(Notify::new()),
        };
        
        // 后台批处理任务
        let buffer = Arc::clone(&processor.buffer);
        let notify = Arc::clone(&processor.notify);
        tokio::spawn(async move {
            loop {
                notify.notified().await;
                
                let batch = {
                    let mut buf = buffer.lock().unwrap();
                    std::mem::take(&mut *buf)
                };
                
                if !batch.is_empty() {
                    Self::export_batch(batch).await;
                }
            }
        });
        
        processor
    }
    
    pub fn add_span(&self, span: Span) {
        let should_notify = {
            let mut buffer = self.buffer.lock().unwrap();
            buffer.push(span);
            buffer.len() >= self.batch_size
        };
        
        if should_notify {
            self.notify.notify_one();
        }
    }
    
    async fn export_batch(_batch: Vec<Span>) {
        // 导出逻辑
    }
}
```

---

**最后更新**: 2025年10月2日  
**作者**: OTLP Rust 项目组
