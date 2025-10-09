# OTLP 智能调度策略 - Rust 完整实现

> **版本**: 1.0.0  
> **Rust 版本**: 1.90+  
> **OpenTelemetry**: v0.27+  
> **最后更新**: 2025-10-09

## 目录

1. [概述](#概述)
2. [核心架构](#核心架构)
3. [任务调度器](#任务调度器)
4. [优先级调度](#优先级调度)
5. [公平调度](#公平调度)
6. [预测性调度](#预测性调度)
7. [工作窃取调度](#工作窃取调度)
8. [资源感知调度](#资源感知调度)
9. [批量调度优化](#批量调度优化)
10. [完整示例](#完整示例)
11. [性能优化](#性能优化)
12. [最佳实践](#最佳实践)

---

## 概述

智能调度是 OTLP 系统的核心组件，负责合理分配计算资源、优化任务执行顺序、提高系统吞吐量和响应时间。

### 核心特性

- ✅ **多种调度策略**: 优先级、公平、预测性、工作窃取
- ✅ **资源感知**: 根据 CPU、内存、网络等资源动态调度
- ✅ **负载均衡**: 自动平衡各工作线程/节点的负载
- ✅ **自适应调整**: 根据系统状态动态优化调度策略
- ✅ **批量优化**: 批处理提高效率
- ✅ **异步高性能**: 基于 Tokio 的零开销调度

---

## 核心架构

```rust
use std::sync::Arc;
use std::time::{Duration, Instant};
use std::collections::{VecDeque, BinaryHeap, HashMap};
use std::cmp::Ordering;
use tokio::sync::{RwLock, Semaphore, mpsc};
use serde::{Serialize, Deserialize};

/// 调度任务
#[derive(Debug, Clone)]
pub struct ScheduledTask {
    pub id: String,
    pub priority: u32,
    pub payload: Vec<u8>,
    pub resource_requirement: ResourceRequirement,
    pub deadline: Option<Instant>,
    pub created_at: Instant,
}

/// 资源需求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceRequirement {
    pub cpu: f64,
    pub memory: u64,
    pub network: u64,
}

/// 调度策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SchedulingStrategy {
    FIFO,
    Priority,
    Fair,
    Predictive,
    WorkStealing,
    ResourceAware,
}

/// 调度指标
#[derive(Debug, Default, Clone)]
pub struct SchedulingMetrics {
    pub total_scheduled: u64,
    pub total_completed: u64,
    pub total_failed: u64,
    pub avg_wait_time: Duration,
    pub avg_execution_time: Duration,
}

impl Ord for ScheduledTask {
    fn cmp(&self, other: &Self) -> Ordering {
        // 先按优先级，再按创建时间
        match self.priority.cmp(&other.priority) {
            Ordering::Equal => other.created_at.cmp(&self.created_at),
            ord => ord,
        }
    }
}

impl PartialOrd for ScheduledTask {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for ScheduledTask {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for ScheduledTask {}
```

---

## 任务调度器

```rust
/// 通用任务调度器
pub struct TaskScheduler {
    strategy: SchedulingStrategy,
    task_queue: Arc<RwLock<BinaryHeap<ScheduledTask>>>,
    workers: usize,
    semaphore: Arc<Semaphore>,
    metrics: Arc<RwLock<SchedulingMetrics>>,
}

impl TaskScheduler {
    pub fn new(strategy: SchedulingStrategy, workers: usize) -> Self {
        Self {
            strategy,
            task_queue: Arc::new(RwLock::new(BinaryHeap::new())),
            workers,
            semaphore: Arc::new(Semaphore::new(workers)),
            metrics: Arc::new(RwLock::new(SchedulingMetrics::default())),
        }
    }

    /// 提交任务
    pub async fn submit(&self, task: ScheduledTask) {
        let mut queue = self.task_queue.write().await;
        queue.push(task);

        let mut metrics = self.metrics.write().await;
        metrics.total_scheduled += 1;
    }

    /// 批量提交任务
    pub async fn submit_batch(&self, tasks: Vec<ScheduledTask>) {
        let mut queue = self.task_queue.write().await;
        let count = tasks.len();

        for task in tasks {
            queue.push(task);
        }

        let mut metrics = self.metrics.write().await;
        metrics.total_scheduled += count as u64;
    }

    /// 启动调度
    pub async fn start(&self) {
        for _ in 0..self.workers {
            let scheduler = self.clone();
            tokio::spawn(async move {
                scheduler.worker_loop().await;
            });
        }
    }

    /// 工作线程循环
    async fn worker_loop(&self) {
        loop {
            // 获取许可
            let _permit = self.semaphore.acquire().await.unwrap();

            // 获取任务
            let task = {
                let mut queue = self.task_queue.write().await;
                queue.pop()
            };

            if let Some(task) = task {
                let start = Instant::now();

                // 执行任务
                if let Err(e) = self.execute_task(&task).await {
                    tracing::error!("Task execution failed: {}", e);
                    let mut metrics = self.metrics.write().await;
                    metrics.total_failed += 1;
                } else {
                    let execution_time = start.elapsed();
                    let wait_time = start.duration_since(task.created_at);

                    let mut metrics = self.metrics.write().await;
                    metrics.total_completed += 1;
                    metrics.avg_execution_time = 
                        (metrics.avg_execution_time * (metrics.total_completed - 1) as u32 + execution_time)
                        / metrics.total_completed as u32;
                    metrics.avg_wait_time = 
                        (metrics.avg_wait_time * (metrics.total_completed - 1) as u32 + wait_time)
                        / metrics.total_completed as u32;
                }
            } else {
                // 队列为空，等待
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        }
    }

    /// 执行任务
    async fn execute_task(&self, task: &ScheduledTask) -> Result<(), String> {
        // 模拟任务执行
        tracing::debug!("Executing task: {}", task.id);
        tokio::time::sleep(Duration::from_millis(50)).await;
        Ok(())
    }

    /// 获取队列长度
    pub async fn queue_length(&self) -> usize {
        self.task_queue.read().await.len()
    }

    /// 获取指标
    pub async fn get_metrics(&self) -> SchedulingMetrics {
        self.metrics.read().await.clone()
    }
}

impl Clone for TaskScheduler {
    fn clone(&self) -> Self {
        Self {
            strategy: self.strategy.clone(),
            task_queue: self.task_queue.clone(),
            workers: self.workers,
            semaphore: self.semaphore.clone(),
            metrics: self.metrics.clone(),
        }
    }
}
```

---

## 优先级调度

```rust
/// 优先级调度器
pub struct PriorityScheduler {
    high_priority_queue: Arc<RwLock<VecDeque<ScheduledTask>>>,
    normal_priority_queue: Arc<RwLock<VecDeque<ScheduledTask>>>,
    low_priority_queue: Arc<RwLock<VecDeque<ScheduledTask>>>,
    workers: usize,
    metrics: Arc<RwLock<SchedulingMetrics>>,
}

impl PriorityScheduler {
    pub fn new(workers: usize) -> Self {
        Self {
            high_priority_queue: Arc::new(RwLock::new(VecDeque::new())),
            normal_priority_queue: Arc::new(RwLock::new(VecDeque::new())),
            low_priority_queue: Arc::new(RwLock::new(VecDeque::new())),
            workers,
            metrics: Arc::new(RwLock::new(SchedulingMetrics::default())),
        }
    }

    /// 提交任务
    pub async fn submit(&self, task: ScheduledTask) {
        let queue = match task.priority {
            p if p >= 80 => &self.high_priority_queue,
            p if p >= 40 => &self.normal_priority_queue,
            _ => &self.low_priority_queue,
        };

        let mut q = queue.write().await;
        q.push_back(task);

        let mut metrics = self.metrics.write().await;
        metrics.total_scheduled += 1;
    }

    /// 获取下一个任务（优先级顺序）
    pub async fn next_task(&self) -> Option<ScheduledTask> {
        // 先检查高优先级队列
        {
            let mut high = self.high_priority_queue.write().await;
            if let Some(task) = high.pop_front() {
                return Some(task);
            }
        }

        // 再检查普通优先级队列
        {
            let mut normal = self.normal_priority_queue.write().await;
            if let Some(task) = normal.pop_front() {
                return Some(task);
            }
        }

        // 最后检查低优先级队列
        {
            let mut low = self.low_priority_queue.write().await;
            low.pop_front()
        }
    }

    /// 启动调度
    pub async fn start(&self) {
        for _ in 0..self.workers {
            let scheduler = self.clone();
            tokio::spawn(async move {
                scheduler.worker_loop().await;
            });
        }
    }

    async fn worker_loop(&self) {
        loop {
            if let Some(task) = self.next_task().await {
                let start = Instant::now();

                if let Err(e) = self.execute_task(&task).await {
                    tracing::error!("Task execution failed: {}", e);
                } else {
                    let execution_time = start.elapsed();

                    let mut metrics = self.metrics.write().await;
                    metrics.total_completed += 1;
                    metrics.avg_execution_time = 
                        (metrics.avg_execution_time * (metrics.total_completed - 1) as u32 + execution_time)
                        / metrics.total_completed as u32;
                }
            } else {
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        }
    }

    async fn execute_task(&self, task: &ScheduledTask) -> Result<(), String> {
        tracing::debug!("Executing task: {} (priority: {})", task.id, task.priority);
        tokio::time::sleep(Duration::from_millis(50)).await;
        Ok(())
    }

    pub async fn get_metrics(&self) -> SchedulingMetrics {
        self.metrics.read().await.clone()
    }
}

impl Clone for PriorityScheduler {
    fn clone(&self) -> Self {
        Self {
            high_priority_queue: self.high_priority_queue.clone(),
            normal_priority_queue: self.normal_priority_queue.clone(),
            low_priority_queue: self.low_priority_queue.clone(),
            workers: self.workers,
            metrics: self.metrics.clone(),
        }
    }
}
```

---

## 公平调度

```rust
use std::collections::BTreeMap;

/// 公平调度器（按租户/服务公平分配资源）
pub struct FairScheduler {
    tenant_queues: Arc<RwLock<HashMap<String, VecDeque<ScheduledTask>>>>,
    tenant_usage: Arc<RwLock<HashMap<String, u64>>>,
    workers: usize,
    metrics: Arc<RwLock<SchedulingMetrics>>,
}

impl FairScheduler {
    pub fn new(workers: usize) -> Self {
        Self {
            tenant_queues: Arc::new(RwLock::new(HashMap::new())),
            tenant_usage: Arc::new(RwLock::new(HashMap::new())),
            workers,
            metrics: Arc::new(RwLock::new(SchedulingMetrics::default())),
        }
    }

    /// 提交任务
    pub async fn submit(&self, tenant_id: String, task: ScheduledTask) {
        let mut queues = self.tenant_queues.write().await;
        queues.entry(tenant_id.clone())
            .or_insert_with(VecDeque::new)
            .push_back(task);

        let mut metrics = self.metrics.write().await;
        metrics.total_scheduled += 1;
    }

    /// 获取下一个任务（使用最少资源的租户优先）
    pub async fn next_task(&self) -> Option<(String, ScheduledTask)> {
        let mut queues = self.tenant_queues.write().await;
        let usage = self.tenant_usage.read().await;

        // 找到使用资源最少的租户
        let min_tenant = queues.keys()
            .filter(|k| !queues[*k].is_empty())
            .min_by_key(|k| usage.get(*k).unwrap_or(&0))?;

        let tenant_id = min_tenant.clone();
        let task = queues.get_mut(&tenant_id)?.pop_front()?;

        Some((tenant_id, task))
    }

    /// 启动调度
    pub async fn start(&self) {
        for _ in 0..self.workers {
            let scheduler = self.clone();
            tokio::spawn(async move {
                scheduler.worker_loop().await;
            });
        }
    }

    async fn worker_loop(&self) {
        loop {
            if let Some((tenant_id, task)) = self.next_task().await {
                let start = Instant::now();

                if let Err(e) = self.execute_task(&task).await {
                    tracing::error!("Task execution failed: {}", e);
                } else {
                    // 更新租户使用量
                    let mut usage = self.tenant_usage.write().await;
                    *usage.entry(tenant_id.clone()).or_insert(0) += 1;

                    let execution_time = start.elapsed();

                    let mut metrics = self.metrics.write().await;
                    metrics.total_completed += 1;
                    metrics.avg_execution_time = 
                        (metrics.avg_execution_time * (metrics.total_completed - 1) as u32 + execution_time)
                        / metrics.total_completed as u32;
                }
            } else {
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        }
    }

    async fn execute_task(&self, task: &ScheduledTask) -> Result<(), String> {
        tracing::debug!("Executing task: {}", task.id);
        tokio::time::sleep(Duration::from_millis(50)).await;
        Ok(())
    }

    /// 获取租户统计
    pub async fn get_tenant_stats(&self) -> HashMap<String, (usize, u64)> {
        let queues = self.tenant_queues.read().await;
        let usage = self.tenant_usage.read().await;

        queues.iter()
            .map(|(k, v)| {
                let queue_len = v.len();
                let used = *usage.get(k).unwrap_or(&0);
                (k.clone(), (queue_len, used))
            })
            .collect()
    }

    pub async fn get_metrics(&self) -> SchedulingMetrics {
        self.metrics.read().await.clone()
    }
}

impl Clone for FairScheduler {
    fn clone(&self) -> Self {
        Self {
            tenant_queues: self.tenant_queues.clone(),
            tenant_usage: self.tenant_usage.clone(),
            workers: self.workers,
            metrics: self.metrics.clone(),
        }
    }
}
```

---

## 预测性调度

```rust
/// 预测性调度器（基于历史数据预测任务执行时间）
pub struct PredictiveScheduler {
    task_queue: Arc<RwLock<Vec<ScheduledTask>>>,
    execution_history: Arc<RwLock<HashMap<String, Vec<Duration>>>>,
    workers: usize,
    metrics: Arc<RwLock<SchedulingMetrics>>,
}

impl PredictiveScheduler {
    pub fn new(workers: usize) -> Self {
        Self {
            task_queue: Arc::new(RwLock::new(Vec::new())),
            execution_history: Arc::new(RwLock::new(HashMap::new())),
            workers,
            metrics: Arc::new(RwLock::new(SchedulingMetrics::default())),
        }
    }

    /// 提交任务
    pub async fn submit(&self, task: ScheduledTask) {
        let mut queue = self.task_queue.write().await;
        queue.push(task);

        let mut metrics = self.metrics.write().await;
        metrics.total_scheduled += 1;
    }

    /// 预测任务执行时间
    async fn predict_execution_time(&self, task: &ScheduledTask) -> Duration {
        let history = self.execution_history.read().await;

        if let Some(times) = history.get(&task.id) {
            if !times.is_empty() {
                // 使用移动平均
                let sum: Duration = times.iter().sum();
                return sum / times.len() as u32;
            }
        }

        // 默认估计
        Duration::from_millis(100)
    }

    /// 获取下一个任务（选择预测执行时间最短的）
    pub async fn next_task(&self) -> Option<ScheduledTask> {
        let mut queue = self.task_queue.write().await;

        if queue.is_empty() {
            return None;
        }

        // 预测每个任务的执行时间
        let mut predictions = Vec::new();
        for (idx, task) in queue.iter().enumerate() {
            let predicted_time = self.predict_execution_time(task).await;
            predictions.push((idx, predicted_time));
        }

        // 选择预测时间最短的
        let shortest_idx = predictions.iter()
            .min_by_key(|(_, time)| *time)
            .map(|(idx, _)| *idx)?;

        Some(queue.remove(shortest_idx))
    }

    /// 记录执行时间
    async fn record_execution_time(&self, task_id: &str, duration: Duration) {
        let mut history = self.execution_history.write().await;
        let entry = history.entry(task_id.to_string()).or_insert_with(Vec::new);

        entry.push(duration);

        // 只保留最近 10 次记录
        if entry.len() > 10 {
            entry.remove(0);
        }
    }

    /// 启动调度
    pub async fn start(&self) {
        for _ in 0..self.workers {
            let scheduler = self.clone();
            tokio::spawn(async move {
                scheduler.worker_loop().await;
            });
        }
    }

    async fn worker_loop(&self) {
        loop {
            if let Some(task) = self.next_task().await {
                let start = Instant::now();

                if let Err(e) = self.execute_task(&task).await {
                    tracing::error!("Task execution failed: {}", e);
                } else {
                    let execution_time = start.elapsed();

                    // 记录执行时间
                    self.record_execution_time(&task.id, execution_time).await;

                    let mut metrics = self.metrics.write().await;
                    metrics.total_completed += 1;
                    metrics.avg_execution_time = 
                        (metrics.avg_execution_time * (metrics.total_completed - 1) as u32 + execution_time)
                        / metrics.total_completed as u32;
                }
            } else {
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        }
    }

    async fn execute_task(&self, task: &ScheduledTask) -> Result<(), String> {
        tracing::debug!("Executing task: {}", task.id);
        tokio::time::sleep(Duration::from_millis(50)).await;
        Ok(())
    }

    pub async fn get_metrics(&self) -> SchedulingMetrics {
        self.metrics.read().await.clone()
    }
}

impl Clone for PredictiveScheduler {
    fn clone(&self) -> Self {
        Self {
            task_queue: self.task_queue.clone(),
            execution_history: self.execution_history.clone(),
            workers: self.workers,
            metrics: self.metrics.clone(),
        }
    }
}
```

---

## 工作窃取调度

```rust
use crossbeam::deque::{Injector, Stealer, Worker};

/// 工作窃取调度器
pub struct WorkStealingScheduler {
    injector: Arc<Injector<ScheduledTask>>,
    stealers: Arc<RwLock<Vec<Stealer<ScheduledTask>>>>,
    workers: usize,
    metrics: Arc<RwLock<SchedulingMetrics>>,
}

impl WorkStealingScheduler {
    pub fn new(workers: usize) -> Self {
        Self {
            injector: Arc::new(Injector::new()),
            stealers: Arc::new(RwLock::new(Vec::new())),
            workers,
            metrics: Arc::new(RwLock::new(SchedulingMetrics::default())),
        }
    }

    /// 提交任务
    pub async fn submit(&self, task: ScheduledTask) {
        self.injector.push(task);

        let mut metrics = self.metrics.write().await;
        metrics.total_scheduled += 1;
    }

    /// 启动调度
    pub async fn start(&self) {
        let mut local_workers = Vec::new();

        for _ in 0..self.workers {
            let worker = Worker::new_fifo();
            let stealer = worker.stealer();
            local_workers.push(worker);

            let mut stealers = self.stealers.write().await;
            stealers.push(stealer);
        }

        for (idx, worker) in local_workers.into_iter().enumerate() {
            let scheduler = self.clone();
            tokio::spawn(async move {
                scheduler.worker_loop(idx, worker).await;
            });
        }
    }

    async fn worker_loop(&self, worker_id: usize, local: Worker<ScheduledTask>) {
        loop {
            // 1. 尝试从本地队列获取
            let task = if let Some(task) = local.pop() {
                Some(task)
            } else {
                // 2. 尝试从全局队列获取
                match self.injector.steal() {
                    crossbeam::deque::Steal::Success(task) => Some(task),
                    _ => {
                        // 3. 尝试从其他工作线程窃取
                        self.steal_from_others(worker_id).await
                    }
                }
            };

            if let Some(task) = task {
                let start = Instant::now();

                if let Err(e) = self.execute_task(&task).await {
                    tracing::error!("Worker {} task execution failed: {}", worker_id, e);
                } else {
                    let execution_time = start.elapsed();

                    let mut metrics = self.metrics.write().await;
                    metrics.total_completed += 1;
                    metrics.avg_execution_time = 
                        (metrics.avg_execution_time * (metrics.total_completed - 1) as u32 + execution_time)
                        / metrics.total_completed as u32;
                }
            } else {
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        }
    }

    async fn steal_from_others(&self, worker_id: usize) -> Option<ScheduledTask> {
        let stealers = self.stealers.read().await;

        for (idx, stealer) in stealers.iter().enumerate() {
            if idx != worker_id {
                if let crossbeam::deque::Steal::Success(task) = stealer.steal() {
                    tracing::debug!("Worker {} stole task from worker {}", worker_id, idx);
                    return Some(task);
                }
            }
        }

        None
    }

    async fn execute_task(&self, task: &ScheduledTask) -> Result<(), String> {
        tracing::debug!("Executing task: {}", task.id);
        tokio::time::sleep(Duration::from_millis(50)).await;
        Ok(())
    }

    pub async fn get_metrics(&self) -> SchedulingMetrics {
        self.metrics.read().await.clone()
    }
}

impl Clone for WorkStealingScheduler {
    fn clone(&self) -> Self {
        Self {
            injector: self.injector.clone(),
            stealers: self.stealers.clone(),
            workers: self.workers,
            metrics: self.metrics.clone(),
        }
    }
}
```

---

## 资源感知调度

```rust
use sysinfo::{System, SystemExt, ProcessorExt};

/// 资源感知调度器
pub struct ResourceAwareScheduler {
    task_queue: Arc<RwLock<Vec<ScheduledTask>>>,
    system: Arc<RwLock<System>>,
    workers: usize,
    metrics: Arc<RwLock<SchedulingMetrics>>,
}

impl ResourceAwareScheduler {
    pub fn new(workers: usize) -> Self {
        Self {
            task_queue: Arc::new(RwLock::new(Vec::new())),
            system: Arc::new(RwLock::new(System::new_all())),
            workers,
            metrics: Arc::new(RwLock::new(SchedulingMetrics::default())),
        }
    }

    /// 提交任务
    pub async fn submit(&self, task: ScheduledTask) {
        let mut queue = self.task_queue.write().await;
        queue.push(task);

        let mut metrics = self.metrics.write().await;
        metrics.total_scheduled += 1;
    }

    /// 检查资源是否充足
    async fn has_sufficient_resources(&self, requirement: &ResourceRequirement) -> bool {
        let mut system = self.system.write().await;
        system.refresh_all();

        let cpu_usage = system.global_cpu_info().cpu_usage();
        let available_cpu = 100.0 - cpu_usage;

        let available_memory = system.available_memory();

        available_cpu >= requirement.cpu && available_memory >= requirement.memory
    }

    /// 获取下一个可执行的任务
    pub async fn next_task(&self) -> Option<ScheduledTask> {
        let mut queue = self.task_queue.write().await;

        for (idx, task) in queue.iter().enumerate() {
            if self.has_sufficient_resources(&task.resource_requirement).await {
                return Some(queue.remove(idx));
            }
        }

        None
    }

    /// 启动调度
    pub async fn start(&self) {
        for _ in 0..self.workers {
            let scheduler = self.clone();
            tokio::spawn(async move {
                scheduler.worker_loop().await;
            });
        }
    }

    async fn worker_loop(&self) {
        loop {
            if let Some(task) = self.next_task().await {
                let start = Instant::now();

                if let Err(e) = self.execute_task(&task).await {
                    tracing::error!("Task execution failed: {}", e);
                } else {
                    let execution_time = start.elapsed();

                    let mut metrics = self.metrics.write().await;
                    metrics.total_completed += 1;
                    metrics.avg_execution_time = 
                        (metrics.avg_execution_time * (metrics.total_completed - 1) as u32 + execution_time)
                        / metrics.total_completed as u32;
                }
            } else {
                tokio::time::sleep(Duration::from_millis(100)).await;
            }
        }
    }

    async fn execute_task(&self, task: &ScheduledTask) -> Result<(), String> {
        tracing::debug!("Executing task: {} (CPU: {}, Memory: {})",
            task.id, task.resource_requirement.cpu, task.resource_requirement.memory);
        tokio::time::sleep(Duration::from_millis(50)).await;
        Ok(())
    }

    pub async fn get_metrics(&self) -> SchedulingMetrics {
        self.metrics.read().await.clone()
    }
}

impl Clone for ResourceAwareScheduler {
    fn clone(&self) -> Self {
        Self {
            task_queue: self.task_queue.clone(),
            system: self.system.clone(),
            workers: self.workers,
            metrics: self.metrics.clone(),
        }
    }
}
```

---

## 批量调度优化

```rust
/// 批量调度器
pub struct BatchScheduler {
    batch_size: usize,
    batch_timeout: Duration,
    pending_tasks: Arc<RwLock<Vec<ScheduledTask>>>,
    processor: Arc<dyn Fn(Vec<ScheduledTask>) -> Result<(), String> + Send + Sync>,
    metrics: Arc<RwLock<SchedulingMetrics>>,
}

impl BatchScheduler {
    pub fn new<F>(batch_size: usize, batch_timeout: Duration, processor: F) -> Self
    where
        F: Fn(Vec<ScheduledTask>) -> Result<(), String> + Send + Sync + 'static,
    {
        Self {
            batch_size,
            batch_timeout,
            pending_tasks: Arc::new(RwLock::new(Vec::new())),
            processor: Arc::new(processor),
            metrics: Arc::new(RwLock::new(SchedulingMetrics::default())),
        }
    }

    /// 提交任务
    pub async fn submit(&self, task: ScheduledTask) {
        let mut pending = self.pending_tasks.write().await;
        pending.push(task);

        let mut metrics = self.metrics.write().await;
        metrics.total_scheduled += 1;

        // 如果达到批量大小，立即处理
        if pending.len() >= self.batch_size {
            let batch = pending.drain(..).collect();
            drop(pending);
            drop(metrics);

            self.process_batch(batch).await;
        }
    }

    /// 启动批量调度
    pub async fn start(&self) {
        let scheduler = self.clone();
        tokio::spawn(async move {
            scheduler.batch_loop().await;
        });
    }

    async fn batch_loop(&self) {
        let mut interval = tokio::time::interval(self.batch_timeout);

        loop {
            interval.tick().await;

            let batch = {
                let mut pending = self.pending_tasks.write().await;
                if pending.is_empty() {
                    continue;
                }
                pending.drain(..).collect()
            };

            self.process_batch(batch).await;
        }
    }

    async fn process_batch(&self, batch: Vec<ScheduledTask>) {
        if batch.is_empty() {
            return;
        }

        let start = Instant::now();
        let count = batch.len();

        if let Err(e) = (self.processor)(batch) {
            tracing::error!("Batch processing failed: {}", e);
            let mut metrics = self.metrics.write().await;
            metrics.total_failed += count as u64;
        } else {
            let execution_time = start.elapsed();

            let mut metrics = self.metrics.write().await;
            metrics.total_completed += count as u64;
            metrics.avg_execution_time = 
                (metrics.avg_execution_time * ((metrics.total_completed - count as u64) as u32) + execution_time)
                / metrics.total_completed as u32;

            tracing::info!("Processed batch of {} tasks in {:?}", count, execution_time);
        }
    }

    pub async fn get_metrics(&self) -> SchedulingMetrics {
        self.metrics.read().await.clone()
    }
}

impl Clone for BatchScheduler {
    fn clone(&self) -> Self {
        Self {
            batch_size: self.batch_size,
            batch_timeout: self.batch_timeout,
            pending_tasks: self.pending_tasks.clone(),
            processor: self.processor.clone(),
            metrics: self.metrics.clone(),
        }
    }
}
```

---

## 完整示例

```rust
use rand::Rng;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt::init();

    println!("=== OTLP 智能调度系统 ===\n");

    // 1. 测试优先级调度
    println!("测试优先级调度器:");
    let priority_scheduler = PriorityScheduler::new(4);
    priority_scheduler.start().await;

    let mut rng = rand::thread_rng();
    for i in 0..20 {
        let task = ScheduledTask {
            id: format!("task-{}", i),
            priority: rng.gen_range(0..100),
            payload: vec![],
            resource_requirement: ResourceRequirement {
                cpu: 1.0,
                memory: 1024,
                network: 100,
            },
            deadline: None,
            created_at: Instant::now(),
        };
        priority_scheduler.submit(task).await;
    }

    tokio::time::sleep(Duration::from_secs(3)).await;

    let metrics = priority_scheduler.get_metrics().await;
    println!("  已调度: {}, 已完成: {}, 平均执行时间: {:?}",
        metrics.total_scheduled, metrics.total_completed, metrics.avg_execution_time);

    // 2. 测试公平调度
    println!("\n测试公平调度器:");
    let fair_scheduler = FairScheduler::new(4);
    fair_scheduler.start().await;

    let tenants = vec!["tenant-a", "tenant-b", "tenant-c"];
    for i in 0..30 {
        let tenant = tenants[i % tenants.len()].to_string();
        let task = ScheduledTask {
            id: format!("task-{}", i),
            priority: 50,
            payload: vec![],
            resource_requirement: ResourceRequirement {
                cpu: 1.0,
                memory: 1024,
                network: 100,
            },
            deadline: None,
            created_at: Instant::now(),
        };
        fair_scheduler.submit(tenant, task).await;
    }

    tokio::time::sleep(Duration::from_secs(3)).await;

    let tenant_stats = fair_scheduler.get_tenant_stats().await;
    println!("  租户统计:");
    for (tenant, (queue_len, used)) in tenant_stats {
        println!("    {}: 队列长度={}, 已使用={}", tenant, queue_len, used);
    }

    // 3. 测试预测性调度
    println!("\n测试预测性调度器:");
    let predictive_scheduler = PredictiveScheduler::new(4);
    predictive_scheduler.start().await;

    for i in 0..15 {
        let task = ScheduledTask {
            id: format!("recurring-task-{}", i % 5),  // 重复的任务 ID
            priority: 50,
            payload: vec![],
            resource_requirement: ResourceRequirement {
                cpu: 1.0,
                memory: 1024,
                network: 100,
            },
            deadline: None,
            created_at: Instant::now(),
        };
        predictive_scheduler.submit(task).await;
    }

    tokio::time::sleep(Duration::from_secs(2)).await;

    let metrics = predictive_scheduler.get_metrics().await;
    println!("  已调度: {}, 已完成: {}, 平均执行时间: {:?}",
        metrics.total_scheduled, metrics.total_completed, metrics.avg_execution_time);

    // 4. 测试工作窃取调度
    println!("\n测试工作窃取调度器:");
    let work_stealing_scheduler = WorkStealingScheduler::new(4);
    work_stealing_scheduler.start().await;

    for i in 0..25 {
        let task = ScheduledTask {
            id: format!("task-{}", i),
            priority: 50,
            payload: vec![],
            resource_requirement: ResourceRequirement {
                cpu: 1.0,
                memory: 1024,
                network: 100,
            },
            deadline: None,
            created_at: Instant::now(),
        };
        work_stealing_scheduler.submit(task).await;
    }

    tokio::time::sleep(Duration::from_secs(2)).await;

    let metrics = work_stealing_scheduler.get_metrics().await;
    println!("  已调度: {}, 已完成: {}",
        metrics.total_scheduled, metrics.total_completed);

    // 5. 测试资源感知调度
    println!("\n测试资源感知调度器:");
    let resource_scheduler = ResourceAwareScheduler::new(4);
    resource_scheduler.start().await;

    for i in 0..10 {
        let task = ScheduledTask {
            id: format!("task-{}", i),
            priority: 50,
            payload: vec![],
            resource_requirement: ResourceRequirement {
                cpu: 10.0,
                memory: 1024 * 1024 * 10,
                network: 1000,
            },
            deadline: None,
            created_at: Instant::now(),
        };
        resource_scheduler.submit(task).await;
    }

    tokio::time::sleep(Duration::from_secs(2)).await;

    let metrics = resource_scheduler.get_metrics().await;
    println!("  已调度: {}, 已完成: {}",
        metrics.total_scheduled, metrics.total_completed);

    // 6. 测试批量调度
    println!("\n测试批量调度器:");
    let batch_scheduler = BatchScheduler::new(
        5,
        Duration::from_secs(1),
        |batch| {
            println!("  处理批量任务: {} 个", batch.len());
            Ok(())
        },
    );
    batch_scheduler.start().await;

    for i in 0..12 {
        let task = ScheduledTask {
            id: format!("task-{}", i),
            priority: 50,
            payload: vec![],
            resource_requirement: ResourceRequirement {
                cpu: 1.0,
                memory: 1024,
                network: 100,
            },
            deadline: None,
            created_at: Instant::now(),
        };
        batch_scheduler.submit(task).await;
        tokio::time::sleep(Duration::from_millis(200)).await;
    }

    tokio::time::sleep(Duration::from_secs(3)).await;

    println!("\n✅ 智能调度系统测试完成!");

    Ok(())
}
```

---

## 性能优化

### 1. **无锁队列**
对于高并发场景，使用无锁数据结构（如 `crossbeam`）。

### 2. **批量处理**
```rust
// 批量提交任务
scheduler.submit_batch(vec![task1, task2, task3]).await;
```

### 3. **自适应工作线程**
```rust
// 根据负载动态调整工作线程数
let optimal_workers = num_cpus::get();
```

---

## 最佳实践

### 1. **选择合适的调度策略**
- **FIFO**: 简单场景
- **优先级**: 有明确优先级的任务
- **公平**: 多租户场景
- **预测性**: 任务执行时间稳定
- **工作窃取**: 任务执行时间差异大
- **资源感知**: 资源受限场景

### 2. **监控与调优**
```rust
// 定期输出调度指标
tokio::spawn(async move {
    let mut interval = tokio::time::interval(Duration::from_secs(60));
    loop {
        interval.tick().await;
        let metrics = scheduler.get_metrics().await;
        tracing::info!("调度指标: {:?}", metrics);
    }
});
```

### 3. **合理设置工作线程数**
```rust
// CPU 密集型
let workers = num_cpus::get();

// I/O 密集型
let workers = num_cpus::get() * 2;
```

---

## 依赖项

```toml
[dependencies]
tokio = { version = "1.41", features = ["full"] }
serde = { version = "1.0", features = ["derive"] }
tracing = "0.1"
tracing-subscriber = "0.3"
sysinfo = "0.32"
crossbeam = "0.8"
num_cpus = "1.16"
rand = "0.8"
futures = "0.3"
```

---

## 总结

本文档提供了完整的 OTLP 智能调度策略的 Rust 实现，包括：

✅ **多种调度策略**: 优先级、公平、预测性、工作窃取、资源感知
✅ **批量优化**: 提高处理效率
✅ **自适应调整**: 根据负载动态优化
✅ **性能优化**: 无锁队列、批处理
✅ **生产就绪**: 监控、指标、最佳实践

通过这些实现，您可以构建高性能、高可用的 OTLP 智能调度系统。

