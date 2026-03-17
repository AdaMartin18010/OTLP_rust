//! # WebAssembly Async Runtime
//!
//! WebAssembly-native async runtime for OTLP operations without requiring
//! a full host-side async executor. Implements cooperative scheduling
//! optimized for WASM's single-threaded environment.
//!
//! ## WASM Async Landscape 2025-2026
//!
//! | Runtime | WASM Support | Approach | Status |
//! |---------|--------------|----------|--------|
//! | wasm-bindgen-futures | ✅ Full | JS Promise bridge | Stable |
//! | WASI Preview 2 | ✅ Full | wasi:io/poll | Stable |
//! | WASI Preview 3 | 🔄 Async | Native async/await | 2025 H1 |
//! | wasmtime | ✅ Good | Async via host | Stable |
//! | wasmCloud | ✅ Full | Actor async model | Stable |
//!
//! ## Design Principles
//!
//! 1. **Cooperative Scheduling**: Yield control periodically to prevent blocking
//! 2. **Memory Efficiency**: Minimize allocations in hot paths
//! 3. **Host Agnostic**: Works in browser, WASI, and embedded environments
//! 4. **Zero-cost Abstractions**: No overhead when not needed
//!
//! ## Usage Examples
//!
//! ### Basic Async Export
//!
//! ```rust,ignore
//! use otlp::wasm_async::{WasmAsyncRuntime, Task};
//!
//! let runtime = WasmAsyncRuntime::new();
//!
//! runtime.spawn(async {
//!     let exporter = WasmExporter::new(config).await?;
//!     exporter.export_traces(traces).await?;
//!     Ok(())
//! });
//!
//! runtime.run_until_complete().await?;
//! ```
//!
//! ### Concurrent Export with Backpressure
//!
//! ```rust,ignore
//! use otlp::wasm_async::{JoinSet, BackpressureController};
//!
//! let mut join_set = JoinSet::new();
//! let backpressure = BackpressureController::new(10); // Max 10 concurrent
//!
//! for batch in trace_batches {
//!     backpressure.acquire().await?;
//!     join_set.spawn(async move {
//!         exporter.export_traces(batch).await?;
//!         backpressure.release();
//!         Ok(())
//!     });
//! }
//!
//! while let Some(result) = join_set.join_next().await {
//!     result??;
//! }
//! ```
//!
//! ### Timer-based Operations
//!
//! ```rust,ignore
//! use otlp::wasm_async::{interval, timeout};
//!
//! // Periodic export
//! let mut ticker = interval(Duration::from_secs(5));
//! loop {
//!     ticker.tick().await;
//!     exporter.export_traces(collect_traces()).await?;
//! }
//!
//! // With timeout
//! let result = timeout(
//!     Duration::from_secs(10),
//!     exporter.export_traces(traces)
//! ).await?;
//! ```

use std::cell::RefCell;
use std::collections::VecDeque;
use std::future::Future;
use std::pin::Pin;
use std::rc::Rc;
use std::task::{Context, Poll, Waker};
use std::time::{Duration, Instant};

use crate::error::{OtlpError, ProcessingError, Result};

/// WASM-compatible async runtime
///
/// A lightweight async executor designed for WebAssembly's constrained environment.
/// Uses cooperative scheduling to prevent blocking the main thread.
#[allow(dead_code)]
pub struct WasmAsyncRuntime {
    task_queue: Rc<RefCell<VecDeque<TaskHandle>>>,
    timer_queue: Rc<RefCell<BinaryHeap<TimerEntry>>>,
    max_concurrent: usize,
    current_tasks: Rc<RefCell<usize>>,
}

impl WasmAsyncRuntime {
    /// Create a new WASM async runtime
    pub fn new() -> Self {
        Self {
            task_queue: Rc::new(RefCell::new(VecDeque::new())),
            timer_queue: Rc::new(RefCell::new(BinaryHeap::new())),
            max_concurrent: 10,
            current_tasks: Rc::new(RefCell::new(0)),
        }
    }

    /// Create with custom concurrency limit
    pub fn with_max_concurrent(max: usize) -> Self {
        Self {
            task_queue: Rc::new(RefCell::new(VecDeque::new())),
            timer_queue: Rc::new(RefCell::new(BinaryHeap::new())),
            max_concurrent: max,
            current_tasks: Rc::new(RefCell::new(0)),
        }
    }

    /// Spawn a new async task
    pub fn spawn<F>(&self, future: F)
    where
        F: Future<Output = Result<()>> + 'static,
    {
        let task = TaskHandle {
            future: Box::pin(future),
            waker: self.create_waker(),
        };
        self.task_queue.borrow_mut().push_back(task);
    }

    /// Run until all tasks complete
    pub async fn run_until_complete(&self) -> Result<()> {
        loop {
            let has_work = self.tick().await?;
            if !has_work && *self.current_tasks.borrow() == 0 {
                break;
            }
            // Yield to host environment
            self.yield_to_host().await;
        }
        Ok(())
    }

    /// Run for a maximum duration
    pub async fn run_for(&self, duration: Duration) -> Result<()> {
        let deadline = Instant::now() + duration;
        while Instant::now() < deadline {
            self.tick().await?;
            self.yield_to_host().await;
        }
        Ok(())
    }

    /// Single tick of the event loop
    async fn tick(&self) -> Result<bool> {
        // Process timers
        self.process_timers();

        // Process tasks
        let mut has_work = false;
        if let Some(mut task) = self.task_queue.borrow_mut().pop_front() {
            has_work = true;
            let waker = task.waker.clone();
            let mut context = Context::from_waker(&waker);

            match task.future.as_mut().poll(&mut context) {
                Poll::Ready(result) => {
                    result?;
                    *self.current_tasks.borrow_mut() -= 1;
                }
                Poll::Pending => {
                    self.task_queue.borrow_mut().push_back(task);
                }
            }
        }

        Ok(has_work || !self.timer_queue.borrow().is_empty())
    }

    /// Process expired timers
    fn process_timers(&self) {
        let now = Instant::now();
        let mut timers = self.timer_queue.borrow_mut();

        while let Some(timer) = timers.peek() {
            if timer.deadline > now {
                break;
            }
            let timer = timers.pop().unwrap();
            if let Some(waker) = timer.waker {
                waker.wake();
            }
        }
    }

    /// Yield control to host environment
    async fn yield_to_host(&self) {
        // Platform-specific yield implementation
        #[cfg(target_arch = "wasm32")]
        {
            // Use setTimeout(0) equivalent in browser/WASI
            YieldFuture::new().await;
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            tokio::task::yield_now().await;
        }
    }

    /// Create a waker for tasks (simplified for WASM)
    fn create_waker(&self) -> Waker {
        // Use a simple counter-based waker for WASM
        // In production, this would use proper async wake mechanisms
        use std::task::{RawWaker, RawWakerVTable, Waker};

        // Create a dummy waker that does nothing
        fn dummy_clone(_: *const ()) -> RawWaker {
            RawWaker::new(std::ptr::null(), &DUMMY_VTABLE)
        }
        fn dummy_wake(_: *const ()) {}
        fn dummy_wake_by_ref(_: *const ()) {}
        fn dummy_drop(_: *const ()) {}

        static DUMMY_VTABLE: RawWakerVTable = RawWakerVTable::new(
            dummy_clone,
            dummy_wake,
            dummy_wake_by_ref,
            dummy_drop,
        );

        unsafe { Waker::from_raw(RawWaker::new(std::ptr::null(), &DUMMY_VTABLE)) }
    }

    /// Sleep for a duration
    pub fn sleep(&self, duration: Duration) -> SleepFuture {
        SleepFuture {
            deadline: Instant::now() + duration,
            timer_queue: self.timer_queue.clone(),
            registered: false,
        }
    }

    /// Create an interval
    pub fn interval(&self, period: Duration) -> Interval {
        Interval {
            period,
            next_tick: Instant::now() + period,
            timer_queue: self.timer_queue.clone(),
        }
    }
}

impl Default for WasmAsyncRuntime {
    fn default() -> Self {
        Self::new()
    }
}

/// Task handle for the runtime
struct TaskHandle {
    future: Pin<Box<dyn Future<Output = Result<()>>>>,
    waker: Waker,
}

/// Timer entry for scheduling
#[derive(Debug)]
struct TimerEntry {
    deadline: Instant,
    waker: Option<Waker>,
}

impl PartialEq for TimerEntry {
    fn eq(&self, other: &Self) -> bool {
        self.deadline == other.deadline
    }
}

impl Eq for TimerEntry {}

impl PartialOrd for TimerEntry {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TimerEntry {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Reverse ordering for min-heap behavior
        other.deadline.cmp(&self.deadline)
    }
}

/// Future that yields to host
pub struct YieldFuture {
    yielded: bool,
}

impl YieldFuture {
    #[allow(dead_code)]
    fn new() -> Self {
        Self { yielded: false }
    }
}

impl Future for YieldFuture {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        if self.yielded {
            Poll::Ready(())
        } else {
            self.yielded = true;
            Poll::Pending
        }
    }
}

/// Sleep future
pub struct SleepFuture {
    deadline: Instant,
    timer_queue: Rc<RefCell<BinaryHeap<TimerEntry>>>,
    registered: bool,
}

impl Future for SleepFuture {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.get_mut();

        if Instant::now() >= this.deadline {
            return Poll::Ready(());
        }

        if !this.registered {
            this.timer_queue.borrow_mut().push(TimerEntry {
                deadline: this.deadline,
                waker: Some(cx.waker().clone()),
            });
            this.registered = true;
        }

        Poll::Pending
    }
}

/// Interval for periodic operations
pub struct Interval {
    period: Duration,
    next_tick: Instant,
    timer_queue: Rc<RefCell<BinaryHeap<TimerEntry>>>,
}

impl Interval {
    /// Wait for the next tick
    pub async fn tick(&mut self) {
        SleepFuture {
            deadline: self.next_tick,
            timer_queue: self.timer_queue.clone(),
            registered: false,
        }
        .await;
        self.next_tick += self.period;
    }

    /// Reset the interval
    pub fn reset(&mut self) {
        self.next_tick = Instant::now() + self.period;
    }
}

/// Timeout wrapper for futures
pub async fn timeout<F, T>(duration: Duration, future: F) -> Result<T>
where
    F: Future<Output = Result<T>>,
{
    // In WASM, we use a simple deadline check
    let deadline = Instant::now() + duration;

    // This is a simplified implementation
    // Real implementation would use select! macro or similar
    let result = future.await;

    if Instant::now() > deadline {
        return Err(OtlpError::Processing(ProcessingError::InvalidState {
            message: "Operation timed out".to_string(),
        }));
    }

    result
}

/// JoinSet for managing multiple concurrent tasks
pub struct JoinSet<T> {
    tasks: Vec<Pin<Box<dyn Future<Output = T>>>>,
    #[allow(dead_code)]
    results: Vec<T>,
}

impl<T> JoinSet<T> {
    /// Create a new JoinSet
    pub fn new() -> Self {
        Self {
            tasks: Vec::new(),
            results: Vec::new(),
        }
    }

    /// Spawn a task into the set
    pub fn spawn<F>(&mut self, future: F)
    where
        F: Future<Output = T> + 'static,
    {
        self.tasks.push(Box::pin(future));
    }

    /// Join the next completed task
    pub async fn join_next(&mut self) -> Option<T> {
        if self.tasks.is_empty() {
            return None;
        }

        // Simplified: just poll the first task
        // Real implementation would use a proper select mechanism
        let task = self.tasks.remove(0);
        let result = task.await;
        Some(result)
    }

    /// Check if all tasks are complete
    pub fn is_empty(&self) -> bool {
        self.tasks.is_empty()
    }

    /// Get number of pending tasks
    pub fn len(&self) -> usize {
        self.tasks.len()
    }
}

impl<T> Default for JoinSet<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// Backpressure controller for limiting concurrency
pub struct BackpressureController {
    max: usize,
    current: Rc<RefCell<usize>>,
    waiters: Rc<RefCell<Vec<Waker>>>,
}

impl BackpressureController {
    /// Create a new controller with max concurrency
    pub fn new(max: usize) -> Self {
        Self {
            max,
            current: Rc::new(RefCell::new(0)),
            waiters: Rc::new(RefCell::new(Vec::new())),
        }
    }

    /// Acquire a slot
    pub async fn acquire(&self) -> Result<()> {
        AcquireFuture {
            controller: self,
            registered: false,
        }
        .await
    }

    /// Release a slot
    pub fn release(&self) {
        *self.current.borrow_mut() -= 1;
        // Wake up a waiter
        if let Some(waker) = self.waiters.borrow_mut().pop() {
            waker.wake();
        }
    }

    /// Get current count
    pub fn current(&self) -> usize {
        *self.current.borrow()
    }

    /// Get available slots
    pub fn available(&self) -> usize {
        self.max.saturating_sub(*self.current.borrow())
    }
}

/// Future for acquiring a backpressure slot
struct AcquireFuture<'a> {
    controller: &'a BackpressureController,
    registered: bool,
}

impl<'a> Future for AcquireFuture<'a> {
    type Output = Result<()>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.get_mut();

        let mut current = this.controller.current.borrow_mut();
        if *current < this.controller.max {
            *current += 1;
            return Poll::Ready(Ok(()));
        }

        if !this.registered {
            this.controller.waiters.borrow_mut().push(cx.waker().clone());
            this.registered = true;
        }

        Poll::Pending
    }
}

/// Simple binary heap implementation for timers
/// (Using std::collections::BinaryHeap in real implementation)
use std::collections::BinaryHeap;

/// WASM-compatible async mutex
/// Uses cell-based interior mutability for single-threaded WASM
pub struct WasmMutex<T> {
    inner: RefCell<T>,
    waiters: RefCell<Vec<Waker>>,
}

impl<T> WasmMutex<T> {
    /// Create a new mutex
    pub fn new(value: T) -> Self {
        Self {
            inner: RefCell::new(value),
            waiters: RefCell::new(Vec::new()),
        }
    }

    /// Try to lock the mutex
    pub fn try_lock(&self) -> Option<WasmMutexGuard<'_, T>> {
        self.inner.try_borrow_mut().ok().map(|guard| WasmMutexGuard {
            mutex: self,
            guard: Some(guard),
        })
    }

    /// Lock the mutex (async)
    pub async fn lock(&self) -> WasmMutexGuard<'_, T> {
        LockFuture { mutex: self }.await
    }
}

/// Future for locking a mutex
struct LockFuture<'a, T> {
    mutex: &'a WasmMutex<T>,
}

impl<'a, T> Future for LockFuture<'a, T> {
    type Output = WasmMutexGuard<'a, T>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        match self.mutex.try_lock() {
            Some(guard) => Poll::Ready(guard),
            None => {
                self.mutex.waiters.borrow_mut().push(cx.waker().clone());
                Poll::Pending
            }
        }
    }
}

/// Mutex guard
pub struct WasmMutexGuard<'a, T> {
    mutex: &'a WasmMutex<T>,
    guard: Option<std::cell::RefMut<'a, T>>,
}

impl<'a, T> std::ops::Deref for WasmMutexGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.guard.as_ref().unwrap()
    }
}

impl<'a, T> std::ops::DerefMut for WasmMutexGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.guard.as_mut().unwrap()
    }
}

impl<'a, T> Drop for WasmMutexGuard<'a, T> {
    fn drop(&mut self) {
        drop(self.guard.take());
        // Wake up a waiter
        if let Some(waker) = self.mutex.waiters.borrow_mut().pop() {
            waker.wake();
        }
    }
}

/// WASM-compatible async channel (single-producer, single-consumer)
pub fn channel<T>() -> (Sender<T>, Receiver<T>) {
    let shared = Rc::new(RefCell::new(ChannelShared {
        queue: VecDeque::new(),
        sender_waker: None,
        receiver_waker: None,
        closed: false,
    }));

    (
        Sender {
            shared: shared.clone(),
        },
        Receiver { shared },
    )
}

/// Channel shared state
struct ChannelShared<T> {
    queue: VecDeque<T>,
    sender_waker: Option<Waker>,
    receiver_waker: Option<Waker>,
    closed: bool,
}

/// Sender half of channel
pub struct Sender<T> {
    shared: Rc<RefCell<ChannelShared<T>>>,
}

impl<T> Sender<T> {
    /// Send a value
    pub fn send(&self, value: T) -> Result<()> {
        let mut shared = self.shared.borrow_mut();
        if shared.closed {
            return Err(OtlpError::Processing(ProcessingError::InvalidState {
                message: "Channel closed".to_string(),
            }));
        }
        shared.queue.push_back(value);
        if let Some(waker) = shared.receiver_waker.take() {
            waker.wake();
        }
        Ok(())
    }

    /// Close the channel
    pub fn close(&self) {
        let mut shared = self.shared.borrow_mut();
        shared.closed = true;
        if let Some(waker) = shared.receiver_waker.take() {
            waker.wake();
        }
    }
}

impl<T> Clone for Sender<T> {
    fn clone(&self) -> Self {
        Self {
            shared: self.shared.clone(),
        }
    }
}

/// Receiver half of channel
pub struct Receiver<T> {
    shared: Rc<RefCell<ChannelShared<T>>>,
}

impl<T> Receiver<T> {
    /// Receive a value (async)
    pub async fn recv(&self) -> Option<T> {
        RecvFuture { receiver: self }.await
    }

    /// Try to receive a value
    pub fn try_recv(&self) -> Option<T> {
        let mut shared = self.shared.borrow_mut();
        shared.queue.pop_front()
    }

    /// Close the channel
    pub fn close(&self) {
        let mut shared = self.shared.borrow_mut();
        shared.closed = true;
        if let Some(waker) = shared.sender_waker.take() {
            waker.wake();
        }
    }
}

/// Future for receiving from channel
struct RecvFuture<'a, T> {
    receiver: &'a Receiver<T>,
}

impl<'a, T> Future for RecvFuture<'a, T> {
    type Output = Option<T>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let mut shared = self.receiver.shared.borrow_mut();

        if let Some(value) = shared.queue.pop_front() {
            return Poll::Ready(Some(value));
        }

        if shared.closed {
            return Poll::Ready(None);
        }

        shared.receiver_waker = Some(cx.waker().clone());
        Poll::Pending
    }
}



#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wasm_async_runtime_creation() {
        let runtime = WasmAsyncRuntime::new();
        assert_eq!(runtime.max_concurrent, 10);

        let runtime = WasmAsyncRuntime::with_max_concurrent(20);
        assert_eq!(runtime.max_concurrent, 20);
    }

    #[test]
    fn test_backpressure_controller() {
        let controller = BackpressureController::new(2);
        assert_eq!(controller.available(), 2);
        assert_eq!(controller.current(), 0);
    }

    #[test]
    fn test_wasm_mutex() {
        let mutex = WasmMutex::new(42);
        if let Some(guard) = mutex.try_lock() {
            assert_eq!(*guard, 42);
        }
    }

    #[test]
    fn test_channel() {
        let (tx, rx) = channel::<i32>();

        tx.send(1).unwrap();
        tx.send(2).unwrap();

        assert_eq!(rx.try_recv(), Some(1));
        assert_eq!(rx.try_recv(), Some(2));
        assert_eq!(rx.try_recv(), None);
    }

    #[test]
    fn test_join_set() {
        let join_set: JoinSet<i32> = JoinSet::new();
        assert!(join_set.is_empty());

        // Note: Actual async testing would require the runtime
    }

    #[test]
    fn test_timer_entry_ordering() {
        let now = Instant::now();
        let t1 = TimerEntry {
            deadline: now + Duration::from_secs(1),
            waker: None,
        };
        let t2 = TimerEntry {
            deadline: now + Duration::from_secs(2),
            waker: None,
        };

        // TimerEntry uses reverse ordering for min-heap behavior
        // Earlier deadline = higher priority = "greater" in ordering
        assert!(t1 > t2, "Earlier deadline should have higher priority");
    }
}
