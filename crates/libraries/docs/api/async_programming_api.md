# 异步编程最佳实践 - API参考文档

**示例文件**: `crates/libraries/examples/async_programming_best_practices.rs`  
**版本**: 1.0.0  
**Rust版本**: 1.90.0+  
**最后更新**: 2025年10月28日

---

## 目录

- [任务管理](#任务管理)
- [超时和取消](#超时和取消)
- [并发数据结构](#并发数据结构)
- [Channel模式](#channel模式)
- [Stream处理](#stream处理)
- [异步递归](#异步递归)
- [错误处理](#错误处理)
- [高级模式](#高级模式)
- [性能优化](#性能优化)

---

## 任务管理

### `basic_task_spawning()`

**签名**:
```rust
pub async fn basic_task_spawning()
```

**功能**: 演示基本的异步任务生成和等待模式。

**涵盖内容**:
- 使用`tokio::spawn`创建任务
- 使用`JoinHandle`等待任务完成
- 处理任务返回值
- 错误处理

**使用示例**:
```rust
#[tokio::main]
async fn main() {
    // 生成单个任务
    let handle = tokio::spawn(async {
        sleep(Duration::from_millis(100)).await;
        "Task completed"
    });
    
    // 等待任务完成
    match handle.await {
        Ok(result) => println!("Result: {}", result),
        Err(e) => eprintln!("Task panicked: {}", e),
    }
}
```

**最佳实践**:
- ✅ 总是处理`JoinHandle::await`的`Result`
- ✅ 使用`tokio::spawn`而非`std::thread::spawn`
- ⚠️ 注意任务panic会被捕获在`JoinError`中

---

### `joinset_usage()`

**签名**:
```rust
pub async fn joinset_usage()
```

**功能**: 演示使用JoinSet管理多个任务。

**优势**:
- 自动管理多个任务的生命周期
- 按完成顺序获取结果
- 更好的资源管理

**使用示例**:
```rust
use tokio::task::JoinSet;

let mut set = JoinSet::new();

// 添加任务
for i in 0..10 {
    set.spawn(async move {
        process_item(i).await
    });
}

// 按完成顺序获取结果
while let Some(result) = set.join_next().await {
    match result {
        Ok(value) => println!("Task completed: {:?}", value),
        Err(e) => eprintln!("Task failed: {}", e),
    }
}
```

**适用场景**:
- 需要管理多个并发任务
- 任务数量动态变化
- 需要按完成顺序处理结果

**性能**: O(1) 添加任务，O(1) 获取完成的任务

---

### `limited_concurrency_example()`

**签名**:
```rust
pub async fn limited_concurrency_example()
```

**功能**: 使用Semaphore限制并发任务数量。

**核心技术**: `tokio::sync::Semaphore`

**使用示例**:
```rust
use tokio::sync::Semaphore;
use std::sync::Arc;

let semaphore = Arc::new(Semaphore::new(3)); // 最多3个并发

let mut handles = Vec::new();
for i in 0..10 {
    let permit = semaphore.clone();
    handles.push(tokio::spawn(async move {
        let _permit = permit.acquire().await.unwrap();
        // 持有permit期间，最多3个任务同时运行
        expensive_operation(i).await
    }));
}

let results = futures::future::join_all(handles).await;
```

**适用场景**:
- 限制资源使用（CPU、内存、网络）
- 防止系统过载
- 公平调度

**配置建议**:
- CPU密集型: `num_cpus::get()`
- I/O密集型: `num_cpus::get() * 2-4`
- 外部API: 根据API限流配置

---

## 超时和取消

### `timeout_patterns()`

**签名**:
```rust
pub async fn timeout_patterns()
```

**功能**: 演示各种超时处理模式。

**核心API**: `tokio::time::timeout`

**使用示例**:
```rust
use tokio::time::{timeout, Duration};

// 基本超时
match timeout(Duration::from_secs(5), async_operation()).await {
    Ok(result) => println!("Completed: {:?}", result),
    Err(_) => println!("Timeout!"),
}

// 组合多个操作的超时
let results = tokio::try_join!(
    timeout(Duration::from_secs(1), operation1()),
    timeout(Duration::from_secs(2), operation2()),
    timeout(Duration::from_secs(3), operation3()),
)?;
```

**最佳实践**:
- ✅ 为所有外部调用设置超时
- ✅ 使用合理的超时时间（不要太短或太长）
- ✅ 记录超时事件用于监控
- ⚠️ 超时会取消Future但不会取消底层操作

**推荐超时时间**:
- 数据库查询: 5-30秒
- HTTP请求: 10-60秒
- RPC调用: 5-15秒
- 缓存操作: 1-5秒

---

### `cancellation_patterns()`

**签名**:
```rust
pub async fn cancellation_patterns()
```

**功能**: 演示优雅的任务取消模式。

**核心技术**: `tokio::select!` + `oneshot::channel`

**使用示例**:
```rust
use tokio::sync::oneshot;
use tokio::select;

let (cancel_tx, mut cancel_rx) = oneshot::channel::<()>();

let task = tokio::spawn(async move {
    let mut interval = tokio::time::interval(Duration::from_secs(1));
    loop {
        select! {
            _ = interval.tick() => {
                println!("Working...");
            }
            _ = &mut cancel_rx => {
                println!("Cancelled");
                break;
            }
        }
    }
});

// 发送取消信号
cancel_tx.send(()).unwrap();
task.await.unwrap();
```

**最佳实践**:
- ✅ 使用`select!`监听取消信号
- ✅ 清理资源后再退出
- ✅ 记录取消原因
- ⚠️ 避免在关键section中检查取消

---

## 并发数据结构

### `rwlock_patterns()`

**签名**:
```rust
pub async fn rwlock_patterns()
```

**功能**: 演示异步读写锁的使用模式。

**核心API**: `tokio::sync::RwLock`

**使用示例**:
```rust
use tokio::sync::RwLock;
use std::sync::Arc;

let data = Arc::new(RwLock::new(vec![1, 2, 3]));

// 多个读者可以并发
let read_handles: Vec<_> = (0..5).map(|i| {
    let data = data.clone();
    tokio::spawn(async move {
        let guard = data.read().await;
        println!("Reader {}: {:?}", i, *guard);
    })
}).collect();

futures::future::join_all(read_handles).await;

// 写入者独占
{
    let mut guard = data.write().await;
    guard.push(4);
}
```

**性能特点**:
- 读操作: 多个并发，无等待
- 写操作: 独占访问，阻塞所有读写
- 读多写少场景最优

**vs Mutex**:
| 特性 | RwLock | Mutex |
|------|--------|-------|
| 读并发 | ✅ 支持 | ❌ 不支持 |
| 写并发 | ❌ 独占 | ❌ 独占 |
| 性能(读多) | ⚡ 优秀 | 👍 良好 |
| 性能(写多) | 👍 良好 | ⚡ 优秀 |
| 复杂度 | 中等 | 简单 |

---

### `mutex_patterns()`

**签名**:
```rust
pub async fn mutex_patterns()
```

**功能**: 演示异步Mutex的使用模式。

**核心API**: `tokio::sync::Mutex`

**使用示例**:
```rust
use tokio::sync::Mutex;
use std::sync::Arc;

let counter = Arc::new(Mutex::new(0));

let handles: Vec<_> = (0..10).map(|_| {
    let counter = counter.clone();
    tokio::spawn(async move {
        let mut num = counter.lock().await;
        *num += 1;
    })
}).collect();

futures::future::join_all(handles).await;

println!("Final count: {}", *counter.lock().await);
```

**最佳实践**:
- ✅ 持有锁的时间越短越好
- ✅ 不要在持有锁时await
- ✅ 使用`Arc`共享Mutex
- ⚠️ 避免嵌套锁（可能死锁）

**性能优化**:
```rust
// ❌ 不好：在持有锁时await
let mut guard = mutex.lock().await;
let data = fetch_data().await; // 持有锁时间过长
*guard = data;

// ✅ 好：最小化锁持有时间
let data = fetch_data().await;
let mut guard = mutex.lock().await;
*guard = data;
```

---

## Channel模式

### `mpsc_patterns()`

**签名**:
```rust
pub async fn mpsc_patterns()
```

**功能**: 多生产者单消费者Channel模式。

**核心API**: `tokio::sync::mpsc`

**使用示例**:
```rust
use tokio::sync::mpsc;

let (tx, mut rx) = mpsc::channel::<String>(100);

// 多个生产者
for i in 0..5 {
    let tx = tx.clone();
    tokio::spawn(async move {
        tx.send(format!("Message from {}", i)).await.unwrap();
    });
}

drop(tx); // 关闭channel

// 单个消费者
while let Some(msg) = rx.recv().await {
    println!("Received: {}", msg);
}
```

**容量选择**:
- 无界: `mpsc::unbounded_channel()` - 可能内存溢出
- 有界: `mpsc::channel(n)` - 提供背压
- 推荐: 根据处理速度选择合适大小（通常100-1000）

---

### `bounded_channel_backpressure()`

**签名**:
```rust
pub async fn bounded_channel_backpressure()
```

**功能**: 演示有界Channel的背压机制。

**背压原理**:
- Channel满时，`send()`会等待
- 自动限制生产速度
- 防止内存溢出

**使用示例**:
```rust
let (tx, mut rx) = mpsc::channel::<i32>(3); // 容量为3

// 快速生产者
tokio::spawn(async move {
    for i in 0..10 {
        println!("Sending {}", i);
        tx.send(i).await.unwrap(); // 可能阻塞
        println!("Sent {}", i);
    }
});

// 慢速消费者
while let Some(value) = rx.recv().await {
    println!("Processing {}", value);
    sleep(Duration::from_millis(200)).await;
}
```

**适用场景**:
- 生产者快于消费者
- 需要限制内存使用
- 需要流量控制

---

### `broadcast_patterns()`

**签名**:
```rust
pub async fn broadcast_patterns()
```

**功能**: 广播Channel模式（一对多）。

**核心API**: `tokio::sync::broadcast`

**使用示例**:
```rust
use tokio::sync::broadcast;

let (tx, _) = broadcast::channel::<String>(16);

// 多个订阅者
let mut subscribers = vec![];
for i in 0..3 {
    let mut rx = tx.subscribe();
    subscribers.push(tokio::spawn(async move {
        while let Ok(msg) = rx.recv().await {
            println!("Subscriber {} got: {}", i, msg);
        }
    }));
}

// 发布消息
for i in 0..5 {
    tx.send(format!("Broadcast {}", i)).unwrap();
}

drop(tx); // 关闭channel
```

**特点**:
- 所有订阅者都收到相同消息
- 支持动态订阅
- 自动跳过慢订阅者

**适用场景**:
- 事件通知
- 配置更新
- 实时数据分发

---

## Stream处理

### `stream_processing()`

**签名**:
```rust
pub async fn stream_processing()
```

**功能**: 演示Stream的各种处理操作。

**核心API**: `futures::stream::StreamExt`

**使用示例**:
```rust
use futures::stream::{self, StreamExt};

let stream = stream::iter(0..10)
    .map(|x| x * 2)
    .filter(|x| x % 3 == 0)
    .take(5);

let results: Vec<_> = stream.collect().await;
println!("Results: {:?}", results);
```

**常用操作**:
- `map`: 转换元素
- `filter`: 过滤元素
- `take`: 取前N个
- `skip`: 跳过前N个
- `fold`: 累积操作
- `buffer_unordered`: 并发处理

**并发处理**:
```rust
// 并发获取URLs
let results = stream::iter(urls)
    .map(|url| async move { fetch(url).await })
    .buffer_unordered(10) // 最多10个并发
    .collect::<Vec<_>>()
    .await;
```

---

### `stream_batching()`

**签名**:
```rust
pub async fn stream_batching()
```

**功能**: 演示Stream的批处理模式。

**使用示例**:
```rust
use futures::stream::{self, StreamExt};

let stream = stream::iter(0..100)
    .chunks(10); // 每批10个

tokio::pin!(stream);

while let Some(batch) = stream.next().await {
    println!("Processing batch of {}", batch.len());
    process_batch(batch).await;
}
```

**适用场景**:
- 批量数据库插入
- 批量API调用
- 降低开销

**批大小建议**:
- 数据库: 100-1000
- API调用: 10-100
- 消息队列: 10-1000

---

## 异步递归

### `async_recursion_example()`

**签名**:
```rust
pub fn async_recursion_example() -> BoxFuture<'static, u64>
```

**功能**: 演示异步递归的实现方式。

**问题**: Rust不支持直接的异步递归

**解决方案**: 使用`BoxFuture`

**使用示例**:
```rust
use futures::future::{BoxFuture, FutureExt};

fn async_fibonacci(n: u64) -> BoxFuture<'static, u64> {
    async move {
        if n <= 1 {
            return n;
        }
        
        let (a, b) = tokio::join!(
            async_fibonacci(n - 1),
            async_fibonacci(n - 2)
        );
        
        a + b
    }.boxed()
}

// 使用
let result = async_fibonacci(10).await;
```

**性能考虑**:
- `Box`分配有开销
- 深度递归可能栈溢出
- 考虑改用迭代

**替代方案**:
```rust
// 使用async-recursion crate
#[async_recursion]
async fn fibonacci(n: u64) -> u64 {
    if n <= 1 {
        return n;
    }
    fibonacci(n - 1).await + fibonacci(n - 2).await
}
```

---

## 错误处理

### `error_handling_patterns()`

**签名**:
```rust
pub async fn error_handling_patterns() -> Result<(), AsyncError>
```

**功能**: 演示异步错误处理的最佳实践。

**使用示例**:
```rust
// 使用?操作符
async fn fetch_user(id: i64) -> Result<User, Error> {
    let conn = pool.get().await?;
    let user = conn.query_one("SELECT * FROM users WHERE id = $1", &[&id]).await?;
    Ok(user.into())
}

// try_join! - 并发执行，任一失败则全部取消
let (user, profile, settings) = tokio::try_join!(
    fetch_user(id),
    fetch_profile(id),
    fetch_settings(id),
)?;

// join_all - 等待所有完成，收集结果
let results = futures::future::join_all(tasks).await;
for result in results {
    match result {
        Ok(value) => process(value),
        Err(e) => log_error(e),
    }
}
```

**错误类型设计**:
```rust
#[derive(Debug, thiserror::Error)]
pub enum AsyncError {
    #[error("Timeout")]
    Timeout,
    
    #[error("Task panicked")]
    Panic,
    
    #[error("Operation failed: {0}")]
    Failed(String),
}
```

---

## 高级模式

### `worker_pool_pattern()`

**签名**:
```rust
pub async fn worker_pool_pattern()
```

**功能**: 实现高效的Worker Pool模式。

**架构**:
```
生产者 → [工作队列] → Worker 1
                    → Worker 2
                    → Worker 3
                    → Worker N
                    ↓
                [结果队列] → 消费者
```

**使用示例**:
```rust
let (work_tx, work_rx) = mpsc::channel(100);
let (result_tx, mut result_rx) = mpsc::channel(100);

let work_rx = Arc::new(Mutex::new(work_rx));

// 启动Worker Pool
for worker_id in 0..4 {
    let work_rx = work_rx.clone();
    let result_tx = result_tx.clone();
    
    tokio::spawn(async move {
        loop {
            let task = work_rx.lock().await.recv().await;
            match task {
                Some(work) => {
                    let result = process(work).await;
                    result_tx.send(result).await.unwrap();
                }
                None => break,
            }
        }
    });
}
```

**适用场景**:
- CPU密集型任务
- 限制并发数
- 任务调度

---

### `request_coalescing()`

**签名**:
```rust
pub async fn request_coalescing()
```

**功能**: 请求合并/批处理模式。

**使用示例**:
```rust
// 收集一段时间内的请求，批量处理
let mut batch = Vec::new();
let mut interval = tokio::time::interval(Duration::from_millis(50));

loop {
    select! {
        _ = interval.tick() => {
            if !batch.is_empty() {
                process_batch(&batch).await;
                batch.clear();
            }
        }
        Some(req) = rx.recv() => {
            batch.push(req);
            if batch.len() >= 100 {
                process_batch(&batch).await;
                batch.clear();
            }
        }
    }
}
```

**优势**:
- 减少系统调用
- 提高吞吐量
- 降低延迟抖动

---

## 性能优化

### `performance_optimization()`

**签名**:
```rust
pub async fn performance_optimization()
```

**功能**: 异步编程性能优化技巧集合。

**优化技巧**:

#### 1. 避免不必要的Clone
```rust
// ❌ 不好：每次都clone
for i in 0..1000 {
    let data = expensive_data.clone();
    tokio::spawn(async move { process(data).await });
}

// ✅ 好：使用Arc
let data = Arc::new(expensive_data);
for i in 0..1000 {
    let data = data.clone(); // 只clone指针
    tokio::spawn(async move { process(&data).await });
}
```

#### 2. 使用try_join!提前失败
```rust
// ❌ join! - 等待所有任务完成
let (r1, r2, r3) = tokio::join!(task1(), task2(), task3());

// ✅ try_join! - 任一失败立即返回
let (r1, r2, r3) = tokio::try_join!(task1(), task2(), task3())?;
```

#### 3. 无序处理更快
```rust
// buffer_unordered 比 buffered 快（不保证顺序）
stream.map(|x| process(x))
    .buffer_unordered(10) // 快
    .collect().await;
```

#### 4. 选择合适的数据结构
- 读多写少: `RwLock`
- 读写均衡: `Mutex`
- 无竞争: `RefCell` + `thread_local!`

---

## 最佳实践总结

### 任务生成
- ✅ 使用`JoinSet`管理多任务
- ✅ 限制并发数量
- ⚠️ 处理任务panic

### 超时处理
- ✅ 所有外部调用都设置超时
- ✅ 使用合理的超时值
- ⚠️ 记录超时事件

### 锁使用
- ✅ 最小化锁持有时间
- ✅ 不在持有锁时await
- ⚠️ 避免死锁

### Channel选择
- MPSC: 多对一通信
- Broadcast: 一对多广播
- Oneshot: 一次性响应
- Watch: 状态同步

### 性能优化
- ✅ 使用Arc而非Clone
- ✅ 使用try_join!提前失败
- ✅ buffer_unordered无序并发
- ✅ 选择合适的数据结构

---

## 相关文档

- [Web框架API](./web_framework_api.md)
- [Tokio官方文档](https://docs.rs/tokio)
- [Futures文档](https://docs.rs/futures)
- [示例代码](../../examples/async_programming_best_practices.rs)

---

**版本**: 1.0.0  
**维护者**: OTLP Rust Team  
**最后更新**: 2025年10月28日

