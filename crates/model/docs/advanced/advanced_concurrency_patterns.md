# 高级并发模式完整指南

**Crate:** c12_model  
**主题:** Advanced Concurrency Patterns  
**Rust 版本:** 1.90.0  
**最后更新:** 2025年10月28日

---

## 📋 目录

- [高级并发模式完整指南](#高级并发模式完整指南)
  - [📋 目录](#-目录)
  - [🎯 高级并发概述](#-高级并发概述)
    - [并发 vs 并行](#并发-vs-并行)
    - [Rust 的并发安全](#rust-的并发安全)
  - [软件事务内存](#软件事务内存)
    - [概念](#概念)
    - [实现](#实现)
  - [Lock-Free 数据结构](#lock-free-数据结构)
    - [1. Lock-Free Stack](#1-lock-free-stack)
      - [实现](#实现-1)
    - [2. Lock-Free Queue](#2-lock-free-queue)
      - [Michael-Scott Queue](#michael-scott-queue)
  - [Work-Stealing 调度器](#work-stealing-调度器)
    - [概念](#概念-1)
    - [实现](#实现-2)
  - [协程和绿色线程](#协程和绿色线程)
    - [1. 协程基础](#1-协程基础)
      - [手动实现简单协程](#手动实现简单协程)
    - [2. 绿色线程](#2-绿色线程)
      - [使用 may (绿色线程库)](#使用-may-绿色线程库)
  - [并发数据结构](#并发数据结构)
    - [1. Concurrent HashMap](#1-concurrent-hashmap)
      - [使用 dashmap](#使用-dashmap)
    - [2. Concurrent Skip List](#2-concurrent-skip-list)
      - [实现](#实现-3)
  - [内存模型和原子操作](#内存模型和原子操作)
    - [1. 内存序 (Memory Ordering)](#1-内存序-memory-ordering)
    - [2. 原子操作模式](#2-原子操作模式)
      - [Compare-And-Swap (CAS)](#compare-and-swap-cas)
      - [Fetch-And-Add](#fetch-and-add)
  - [死锁检测和预防](#死锁检测和预防)
    - [1. 死锁检测](#1-死锁检测)
      - [资源分配图](#资源分配图)
    - [2. 死锁预防](#2-死锁预防)
      - [锁顺序](#锁顺序)
      - [超时机制](#超时机制)
  - [总结](#总结)
    - [并发模式清单](#并发模式清单)
    - [最佳实践](#最佳实践)

---

## 🎯 高级并发概述

### 并发 vs 并行

```
并发 (Concurrency):
┌─────┐ ┌─────┐ ┌─────┐
│ T1  │ │ T2  │ │ T3  │  多个任务交替执行
└──┬──┘ └──┬──┘ └──┬──┘
   │       │       │
   └───────┴───────┘
       单核 CPU

并行 (Parallelism):
┌─────┐ ┌─────┐ ┌─────┐
│ T1  │ │ T2  │ │ T3  │  多个任务同时执行
└──┬──┘ └──┬──┘ └──┬──┘
   │       │       │
  Core1   Core2   Core3
      多核 CPU
```

### Rust 的并发安全

```rust
// Rust 通过类型系统保证并发安全

// Send: 可以安全地在线程间转移所有权
// Sync: 可以安全地在线程间共享引用

use std::marker::{Send, Sync};

// ✅ 安全：实现了 Send + Sync
fn process_data<T: Send + Sync>(data: T) {
    std::thread::spawn(move || {
        // 可以安全地使用 data
    });
}

// ❌ 不安全：Rc 没有实现 Send
use std::rc::Rc;

fn unsafe_example() {
    let data = Rc::new(5);
    
    // 编译错误！Rc<T> 不能跨线程发送
    // std::thread::spawn(move || {
    //     println!("{}", data);
    // });
}

// ✅ 使用 Arc 替代
use std::sync::Arc;

fn safe_example() {
    let data = Arc::new(5);
    
    std::thread::spawn(move || {
        println!("{}", data);
    });
}
```

---

## 软件事务内存

### 概念

STM 允许多个线程原子地修改共享内存，类似于数据库事务。

### 实现

```rust
use std::sync::{Arc, Mutex};
use std::collections::HashMap;

pub struct STM {
    global_state: Arc<Mutex<HashMap<String, i64>>>,
    version: Arc<Mutex<u64>>,
}

pub struct Transaction {
    reads: HashMap<String, (i64, u64)>,  // (value, version)
    writes: HashMap<String, i64>,
    version: u64,
}

impl STM {
    pub fn new() -> Self {
        Self {
            global_state: Arc::new(Mutex::new(HashMap::new())),
            version: Arc::new(Mutex::new(0)),
        }
    }
    
    pub fn begin(&self) -> Transaction {
        let version = *self.version.lock().unwrap();
        Transaction {
            reads: HashMap::new(),
            writes: HashMap::new(),
            version,
        }
    }
    
    pub fn commit(&self, tx: &Transaction) -> Result<()> {
        // 1. 验证阶段：检查读集是否被修改
        let state = self.global_state.lock().unwrap();
        let current_version = *self.version.lock().unwrap();
        
        for (key, (_, read_version)) in &tx.reads {
            // 如果版本号变化，说明有其他事务修改了数据
            if *read_version < current_version {
                return Err(anyhow::anyhow!("Conflict detected"));
            }
        }
        
        // 2. 写入阶段：应用所有写操作
        drop(state);  // 释放锁
        let mut state = self.global_state.lock().unwrap();
        
        for (key, value) in &tx.writes {
            state.insert(key.clone(), *value);
        }
        
        // 3. 提交：增加版本号
        let mut version = self.version.lock().unwrap();
        *version += 1;
        
        Ok(())
    }
    
    pub fn read(&self, tx: &mut Transaction, key: &str) -> Option<i64> {
        // 先检查写集
        if let Some(&value) = tx.writes.get(key) {
            return Some(value);
        }
        
        // 再检查读集
        if let Some(&(value, _)) = tx.reads.get(key) {
            return Some(value);
        }
        
        // 从全局状态读取
        let state = self.global_state.lock().unwrap();
        let value = state.get(key).copied();
        
        if let Some(v) = value {
            tx.reads.insert(key.to_string(), (v, tx.version));
        }
        
        value
    }
    
    pub fn write(&self, tx: &mut Transaction, key: String, value: i64) {
        tx.writes.insert(key, value);
    }
}

// 使用示例：银行转账
async fn transfer_with_stm(stm: &STM, from: &str, to: &str, amount: i64) -> Result<()> {
    loop {
        let mut tx = stm.begin();
        
        // 读取账户余额
        let from_balance = stm.read(&mut tx, from).unwrap_or(0);
        let to_balance = stm.read(&mut tx, to).unwrap_or(0);
        
        // 检查余额
        if from_balance < amount {
            return Err(anyhow::anyhow!("Insufficient balance"));
        }
        
        // 执行转账
        stm.write(&mut tx, from.to_string(), from_balance - amount);
        stm.write(&mut tx, to.to_string(), to_balance + amount);
        
        // 尝试提交
        match stm.commit(&tx) {
            Ok(_) => return Ok(()),
            Err(_) => {
                // 冲突，重试
                continue;
            }
        }
    }
}
```

---

## Lock-Free 数据结构

### 1. Lock-Free Stack

#### 实现

```rust
use std::sync::atomic::{AtomicPtr, Ordering};
use std::ptr;

pub struct Node<T> {
    data: T,
    next: *mut Node<T>,
}

pub struct LockFreeStack<T> {
    head: AtomicPtr<Node<T>>,
}

impl<T> LockFreeStack<T> {
    pub fn new() -> Self {
        Self {
            head: AtomicPtr::new(ptr::null_mut()),
        }
    }
    
    pub fn push(&self, data: T) {
        let new_node = Box::into_raw(Box::new(Node {
            data,
            next: ptr::null_mut(),
        }));
        
        loop {
            // 读取当前 head
            let old_head = self.head.load(Ordering::Acquire);
            
            // 设置新节点的 next
            unsafe {
                (*new_node).next = old_head;
            }
            
            // CAS: 如果 head 没变，更新为新节点
            match self.head.compare_exchange(
                old_head,
                new_node,
                Ordering::Release,
                Ordering::Acquire,
            ) {
                Ok(_) => return,  // 成功
                Err(_) => continue,  // 失败，重试
            }
        }
    }
    
    pub fn pop(&self) -> Option<T> {
        loop {
            let old_head = self.head.load(Ordering::Acquire);
            
            if old_head.is_null() {
                return None;
            }
            
            unsafe {
                let next = (*old_head).next;
                
                // CAS: 尝试将 head 更新为 next
                match self.head.compare_exchange(
                    old_head,
                    next,
                    Ordering::Release,
                    Ordering::Acquire,
                ) {
                    Ok(_) => {
                        // 成功，读取数据并释放节点
                        let data = ptr::read(&(*old_head).data);
                        drop(Box::from_raw(old_head));
                        return Some(data);
                    }
                    Err(_) => continue,  // 失败，重试
                }
            }
        }
    }
}

unsafe impl<T: Send> Send for LockFreeStack<T> {}
unsafe impl<T: Send> Sync for LockFreeStack<T> {}
```

---

### 2. Lock-Free Queue

#### Michael-Scott Queue

```rust
use std::sync::atomic::{AtomicPtr, Ordering};
use std::ptr;

struct QueueNode<T> {
    data: Option<T>,
    next: AtomicPtr<QueueNode<T>>,
}

pub struct LockFreeQueue<T> {
    head: AtomicPtr<QueueNode<T>>,
    tail: AtomicPtr<QueueNode<T>>,
}

impl<T> LockFreeQueue<T> {
    pub fn new() -> Self {
        // 创建哨兵节点
        let sentinel = Box::into_raw(Box::new(QueueNode {
            data: None,
            next: AtomicPtr::new(ptr::null_mut()),
        }));
        
        Self {
            head: AtomicPtr::new(sentinel),
            tail: AtomicPtr::new(sentinel),
        }
    }
    
    pub fn enqueue(&self, data: T) {
        let new_node = Box::into_raw(Box::new(QueueNode {
            data: Some(data),
            next: AtomicPtr::new(ptr::null_mut()),
        }));
        
        loop {
            let tail = self.tail.load(Ordering::Acquire);
            let next = unsafe { (*tail).next.load(Ordering::Acquire) };
            
            if tail == self.tail.load(Ordering::Acquire) {
                if next.is_null() {
                    // tail 是最后一个节点，尝试插入
                    match unsafe {
                        (*tail).next.compare_exchange(
                            next,
                            new_node,
                            Ordering::Release,
                            Ordering::Acquire,
                        )
                    } {
                        Ok(_) => {
                            // 成功插入，尝试移动 tail
                            self.tail.compare_exchange(
                                tail,
                                new_node,
                                Ordering::Release,
                                Ordering::Acquire,
                            ).ok();
                            return;
                        }
                        Err(_) => continue,
                    }
                } else {
                    // tail 不是最后一个节点，帮助移动 tail
                    self.tail.compare_exchange(
                        tail,
                        next,
                        Ordering::Release,
                        Ordering::Acquire,
                    ).ok();
                }
            }
        }
    }
    
    pub fn dequeue(&self) -> Option<T> {
        loop {
            let head = self.head.load(Ordering::Acquire);
            let tail = self.tail.load(Ordering::Acquire);
            let next = unsafe { (*head).next.load(Ordering::Acquire) };
            
            if head == self.head.load(Ordering::Acquire) {
                if head == tail {
                    if next.is_null() {
                        return None;  // 队列为空
                    }
                    
                    // 帮助移动 tail
                    self.tail.compare_exchange(
                        tail,
                        next,
                        Ordering::Release,
                        Ordering::Acquire,
                    ).ok();
                } else {
                    // 读取数据
                    let data = unsafe { (*next).data.take() };
                    
                    // 尝试移动 head
                    match self.head.compare_exchange(
                        head,
                        next,
                        Ordering::Release,
                        Ordering::Acquire,
                    ) {
                        Ok(_) => {
                            unsafe { drop(Box::from_raw(head)) };
                            return data;
                        }
                        Err(_) => continue,
                    }
                }
            }
        }
    }
}
```

---

## Work-Stealing 调度器

### 概念

Work-Stealing 是一种负载均衡策略，空闲的线程会"偷取"其他线程的任务。

### 实现

```rust
use crossbeam::deque::{Worker, Stealer};
use std::sync::Arc;

pub struct WorkStealingScheduler {
    workers: Vec<Worker<Task>>,
    stealers: Vec<Stealer<Task>>,
    threads: Vec<std::thread::JoinHandle<()>>,
}

type Task = Box<dyn FnOnce() + Send>;

impl WorkStealingScheduler {
    pub fn new(num_threads: usize) -> Self {
        let mut workers = Vec::new();
        let mut stealers = Vec::new();
        
        // 为每个线程创建工作队列
        for _ in 0..num_threads {
            let worker = Worker::new_fifo();
            let stealer = worker.stealer();
            workers.push(worker);
            stealers.push(stealer);
        }
        
        let stealers = Arc::new(stealers);
        let mut threads = Vec::new();
        
        // 启动工作线程
        for (id, worker) in workers.iter().enumerate() {
            let worker = worker.clone();
            let stealers = Arc::clone(&stealers);
            
            let handle = std::thread::spawn(move || {
                Self::worker_loop(id, worker, stealers);
            });
            
            threads.push(handle);
        }
        
        Self {
            workers,
            stealers: Arc::try_unwrap(stealers).unwrap(),
            threads,
        }
    }
    
    pub fn submit<F>(&self, task: F)
    where
        F: FnOnce() + Send + 'static,
    {
        // 轮询分配任务
        let worker_id = rand::random::<usize>() % self.workers.len();
        self.workers[worker_id].push(Box::new(task));
    }
    
    fn worker_loop(
        id: usize,
        worker: Worker<Task>,
        stealers: Arc<Vec<Stealer<Task>>>,
    ) {
        loop {
            // 1. 从自己的队列中取任务
            if let Some(task) = worker.pop() {
                task();
                continue;
            }
            
            // 2. 从其他线程偷取任务
            let mut found = false;
            for (i, stealer) in stealers.iter().enumerate() {
                if i == id {
                    continue;  // 跳过自己
                }
                
                if let crossbeam::deque::Steal::Success(task) = stealer.steal() {
                    task();
                    found = true;
                    break;
                }
            }
            
            if !found {
                // 3. 没有任务，休眠一会儿
                std::thread::sleep(Duration::from_millis(1));
            }
        }
    }
}

// 使用示例
async fn work_stealing_example() {
    let scheduler = WorkStealingScheduler::new(4);
    
    // 提交 1000 个任务
    for i in 0..1000 {
        scheduler.submit(move || {
            println!("Task {} executing", i);
            std::thread::sleep(Duration::from_millis(10));
        });
    }
    
    // 等待所有任务完成
    std::thread::sleep(Duration::from_secs(5));
}
```

---

## 协程和绿色线程

### 1. 协程基础

#### 手动实现简单协程

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, Waker};

pub struct SimpleCoroutine {
    state: CoroutineState,
}

enum CoroutineState {
    Created,
    Running,
    Suspended(usize),  // 挂起点
    Completed,
}

impl Future for SimpleCoroutine {
    type Output = ();
    
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        match self.state {
            CoroutineState::Created => {
                println!("Coroutine started");
                self.state = CoroutineState::Running;
                cx.waker().wake_by_ref();
                Poll::Pending
            }
            CoroutineState::Running => {
                println!("Coroutine running");
                self.state = CoroutineState::Suspended(0);
                cx.waker().wake_by_ref();
                Poll::Pending
            }
            CoroutineState::Suspended(n) if n < 5 => {
                println!("Coroutine suspended at step {}", n);
                self.state = CoroutineState::Suspended(n + 1);
                cx.waker().wake_by_ref();
                Poll::Pending
            }
            CoroutineState::Suspended(_) => {
                println!("Coroutine completed");
                self.state = CoroutineState::Completed;
                Poll::Ready(())
            }
            CoroutineState::Completed => Poll::Ready(()),
        }
    }
}
```

---

### 2. 绿色线程

#### 使用 may (绿色线程库)

```rust
// Cargo.toml: may = "0.3"

use may::go;
use may::coroutine;

fn green_thread_example() {
    // 启动 10000 个绿色线程
    let handles: Vec<_> = (0..10000).map(|i| {
        go!(move || {
            println!("Green thread {} started", i);
            coroutine::sleep(Duration::from_millis(100));
            println!("Green thread {} finished", i);
        })
    }).collect();
    
    // 等待所有绿色线程完成
    for handle in handles {
        handle.join().ok();
    }
}

// 绿色线程池
fn green_thread_pool_example() {
    use may::sync::mpsc;
    
    let (tx, rx) = mpsc::channel();
    
    // Worker 绿色线程
    for id in 0..10 {
        let rx = rx.clone();
        go!(move || {
            while let Ok(task) = rx.recv() {
                println!("Worker {} processing task", id);
                process_task(task);
            }
        });
    }
    
    // 发送任务
    for i in 0..100 {
        tx.send(i).ok();
    }
}
```

---

## 并发数据结构

### 1. Concurrent HashMap

#### 使用 dashmap

```rust
use dashmap::DashMap;

let map = Arc::new(DashMap::new());

// 并发插入
let handles: Vec<_> = (0..10).map(|i| {
    let map = Arc::clone(&map);
    std::thread::spawn(move || {
        for j in 0..1000 {
            map.insert(i * 1000 + j, j);
        }
    })
}).collect();

for handle in handles {
    handle.join().unwrap();
}

// 并发读取
let count = map.iter().count();
println!("Total entries: {}", count);
```

---

### 2. Concurrent Skip List

#### 实现

```rust
use std::sync::Arc;
use crossbeam::epoch::{self, Atomic, Owned, Shared};
use std::sync::atomic::Ordering;

const MAX_LEVEL: usize = 16;

struct Node<K, V> {
    key: K,
    value: V,
    next: [Atomic<Node<K, V>>; MAX_LEVEL],
}

pub struct ConcurrentSkipList<K, V> {
    head: Atomic<Node<K, V>>,
    max_level: AtomicUsize,
}

impl<K: Ord, V> ConcurrentSkipList<K, V> {
    pub fn new() -> Self {
        // 实现省略...
        todo!()
    }
    
    pub fn insert(&self, key: K, value: V) {
        let guard = epoch::pin();
        
        // 1. 找到插入位置
        let (preds, succs) = self.find(&key, &guard);
        
        // 2. 创建新节点
        let level = self.random_level();
        let new_node = Owned::new(Node {
            key,
            value,
            next: Default::default(),
        });
        
        // 3. 插入节点
        // 实现 lock-free 插入逻辑...
    }
    
    pub fn get(&self, key: &K) -> Option<&V> {
        let guard = epoch::pin();
        
        let mut curr = self.head.load(Ordering::Acquire, &guard);
        
        for level in (0..MAX_LEVEL).rev() {
            loop {
                let next = unsafe { curr.deref() }.next[level].load(Ordering::Acquire, &guard);
                
                if next.is_null() {
                    break;
                }
                
                let next_node = unsafe { next.deref() };
                
                match next_node.key.cmp(key) {
                    Ordering::Less => curr = next,
                    Ordering::Equal => return Some(&next_node.value),
                    Ordering::Greater => break,
                }
            }
        }
        
        None
    }
    
    fn random_level(&self) -> usize {
        let mut level = 1;
        while rand::random::<bool>() && level < MAX_LEVEL {
            level += 1;
        }
        level
    }
}
```

---

## 内存模型和原子操作

### 1. 内存序 (Memory Ordering)

```rust
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

// Relaxed: 最弱的序，只保证原子性
let counter = AtomicUsize::new(0);
counter.fetch_add(1, Ordering::Relaxed);

// Acquire-Release: 保证同步
let flag = AtomicBool::new(false);
let data = AtomicUsize::new(0);

// Writer
data.store(42, Ordering::Relaxed);
flag.store(true, Ordering::Release);  // Release

// Reader
while !flag.load(Ordering::Acquire) {  // Acquire
    std::hint::spin_loop();
}
let value = data.load(Ordering::Relaxed);
assert_eq!(value, 42);

// SeqCst: 最强的序，全局顺序一致
let x = AtomicBool::new(false);
let y = AtomicBool::new(false);

x.store(true, Ordering::SeqCst);
y.store(true, Ordering::SeqCst);
```

---

### 2. 原子操作模式

#### Compare-And-Swap (CAS)

```rust
use std::sync::atomic::{AtomicU64, Ordering};

let atomic = AtomicU64::new(0);

loop {
    let current = atomic.load(Ordering::Acquire);
    let new_value = current + 1;
    
    match atomic.compare_exchange(
        current,
        new_value,
        Ordering::Release,
        Ordering::Acquire,
    ) {
        Ok(_) => break,  // 成功
        Err(_) => continue,  // 失败，重试
    }
}
```

#### Fetch-And-Add

```rust
let counter = AtomicU64::new(0);

// 原子地加 1 并返回旧值
let old_value = counter.fetch_add(1, Ordering::SeqCst);
```

---

## 死锁检测和预防

### 1. 死锁检测

#### 资源分配图

```rust
use std::collections::{HashMap, HashSet};

pub struct DeadlockDetector {
    /// 线程 -> 持有的锁
    held_locks: HashMap<ThreadId, HashSet<LockId>>,
    /// 线程 -> 等待的锁
    waiting_for: HashMap<ThreadId, LockId>,
    /// 锁 -> 持有者
    lock_holders: HashMap<LockId, ThreadId>,
}

type ThreadId = usize;
type LockId = usize;

impl DeadlockDetector {
    pub fn new() -> Self {
        Self {
            held_locks: HashMap::new(),
            waiting_for: HashMap::new(),
            lock_holders: HashMap::new(),
        }
    }
    
    pub fn acquire_lock(&mut self, thread_id: ThreadId, lock_id: LockId) -> Result<()> {
        // 1. 检查是否会导致死锁
        if self.would_deadlock(thread_id, lock_id) {
            return Err(anyhow::anyhow!("Deadlock detected!"));
        }
        
        // 2. 记录锁的获取
        self.held_locks.entry(thread_id)
            .or_insert_with(HashSet::new)
            .insert(lock_id);
        
        self.lock_holders.insert(lock_id, thread_id);
        self.waiting_for.remove(&thread_id);
        
        Ok(())
    }
    
    pub fn wait_for_lock(&mut self, thread_id: ThreadId, lock_id: LockId) {
        self.waiting_for.insert(thread_id, lock_id);
    }
    
    pub fn release_lock(&mut self, thread_id: ThreadId, lock_id: LockId) {
        if let Some(locks) = self.held_locks.get_mut(&thread_id) {
            locks.remove(&lock_id);
        }
        self.lock_holders.remove(&lock_id);
    }
    
    fn would_deadlock(&self, thread_id: ThreadId, lock_id: LockId) -> bool {
        // 使用 DFS 检测环
        let mut visited = HashSet::new();
        self.has_cycle(thread_id, lock_id, &mut visited)
    }
    
    fn has_cycle(
        &self,
        thread_id: ThreadId,
        lock_id: LockId,
        visited: &mut HashSet<ThreadId>,
    ) -> bool {
        if visited.contains(&thread_id) {
            return true;  // 发现环
        }
        
        visited.insert(thread_id);
        
        // 检查持有目标锁的线程
        if let Some(&holder) = self.lock_holders.get(&lock_id) {
            // 检查持有者是否在等待当前线程持有的锁
            if let Some(&waiting_lock) = self.waiting_for.get(&holder) {
                if let Some(locks) = self.held_locks.get(&thread_id) {
                    if locks.contains(&waiting_lock) {
                        return true;  // 死锁
                    }
                }
                
                // 递归检查
                return self.has_cycle(holder, waiting_lock, visited);
            }
        }
        
        false
    }
}
```

---

### 2. 死锁预防

#### 锁顺序

```rust
// ❌ 可能死锁
fn bad_transfer(account1: &Mutex<Account>, account2: &Mutex<Account>) {
    let a1 = account1.lock().unwrap();
    let a2 = account2.lock().unwrap();
    // ... 转账操作
}

// ✅ 按固定顺序加锁，避免死锁
fn good_transfer(account1: &Mutex<Account>, account2: &Mutex<Account>) {
    let (first, second) = if account1 as *const _ < account2 as *const _ {
        (account1, account2)
    } else {
        (account2, account1)
    };
    
    let a1 = first.lock().unwrap();
    let a2 = second.lock().unwrap();
    // ... 转账操作
}
```

#### 超时机制

```rust
use std::time::Duration;

fn try_lock_with_timeout<T>(
    lock: &Mutex<T>,
    timeout: Duration,
) -> Option<MutexGuard<T>> {
    let start = Instant::now();
    
    loop {
        if let Ok(guard) = lock.try_lock() {
            return Some(guard);
        }
        
        if start.elapsed() > timeout {
            return None;  // 超时
        }
        
        std::thread::sleep(Duration::from_millis(10));
    }
}
```

---

## 总结

### 并发模式清单

- ✅ **STM**: 软件事务内存
- ✅ **Lock-Free**: 无锁数据结构
- ✅ **Work-Stealing**: 工作窃取调度
- ✅ **Green Threads**: 绿色线程/协程
- ✅ **Concurrent DS**: 并发数据结构
- ✅ **Memory Model**: 内存模型和原子操作
- ✅ **Deadlock**: 死锁检测和预防

### 最佳实践

1. **优先使用高级抽象**: 如 `Arc`, `Mutex`, `Channel`
2. **避免过早优化**: 先用简单的锁，需要时再优化
3. **测试并发代码**: 使用工具如 Loom
4. **理解内存模型**: 正确使用 Ordering
5. **预防死锁**: 按顺序加锁，使用超时

---

**文档贡献者:** AI Assistant  
**审核状态:** ✅ 已完成  
**最后更新:** 2025年10月28日

