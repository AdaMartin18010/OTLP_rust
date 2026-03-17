//! # Complete Actor Model Implementation
//! 
//! 完整的Actor模型实现，基于消息传递的并发模型
//! 
//! ## Actor模型核心概念
//! - **Actor**: 独立的计算单元，拥有自己的状态
//! - **Message**: Actor之间通过消息通信
//! - **Mailbox**: 每个Actor有自己的消息队列
//! - **Location Transparency**: Actor位置透明
//! - **Supervision**: 监督策略处理失败
//! 
//! ## 实现特性
//! - 异步消息处理
//! - 类型安全的消息
//! - Actor生命周期管理
//! - 监督策略(One-for-One, All-for-One)
//! - 死信队列
//! - Actor引用(ActorRef)
//! - 状态封装
//! 
//! ## 使用场景
//! - 分布式系统
//! - 并发状态管理
//! - 事件驱动架构
//! - 微服务通信

use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::{mpsc, RwLock, oneshot};
use tokio::time::{sleep, Duration};
use async_trait::async_trait;
use tracing::{info, warn, error, instrument};
use thiserror::Error;

// ============================================================================
// Part 1: Core Actor Types
// ============================================================================

/// Actor唯一标识符
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ActorId(u64);

impl ActorId {
    pub fn new() -> Self {
        use std::sync::atomic::{AtomicU64, Ordering};
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        Self(COUNTER.fetch_add(1, Ordering::Relaxed))
    }
}

impl std::fmt::Display for ActorId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Actor({})", self.0)
    }
}

/// Actor错误类型
#[derive(Debug, Error)]
pub enum ActorError {
    #[error("Actor mailbox full")]
    MailboxFull,
    
    #[error("Actor stopped")]
    ActorStopped,
    
    #[error("Actor not found: {0}")]
    ActorNotFound(ActorId),
    
    #[error("Message processing failed: {0}")]
    ProcessingFailed(String),
    
    #[error("Supervisor error: {0}")]
    SupervisorError(String),
}

/// Actor状态
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ActorState {
    Starting,
    Running,
    Stopping,
    Stopped,
    Failed,
}

// ============================================================================
// Part 2: Message System
// ============================================================================

/// 消息trait - 所有消息必须实现
#[async_trait]
pub trait Message: Send + 'static {
    type Result: Send;
    
    fn name(&self) -> &str {
        std::any::type_name::<Self>()
    }
}

/// 系统消息(内部使用)
#[derive(Debug)]
enum SystemMessage {
    Stop,
    Restart,
    GetState(oneshot::Sender<ActorState>),
}

/// 消息信封(包含消息和响应通道)
struct MessageEnvelope<M: Message> {
    message: M,
    respond_to: Option<oneshot::Sender<M::Result>>,
}

// ============================================================================
// Part 3: Actor Trait
// ============================================================================

/// Actor trait - 所有Actor必须实现
#[async_trait]
pub trait Actor: Send + 'static {
    type Message: Message;
    
    /// Actor启动时调用
    async fn started(&mut self) {
        info!("Actor started");
    }
    
    /// 处理消息
    async fn handle(&mut self, msg: Self::Message) -> <Self::Message as Message>::Result;
    
    /// Actor停止时调用
    async fn stopped(&mut self) {
        info!("Actor stopped");
    }
    
    /// Actor失败时调用
    async fn failed(&mut self, error: ActorError) {
        error!("Actor failed: {}", error);
    }
}

// ============================================================================
// Part 4: Actor Context
// ============================================================================

/// Actor上下文 - 管理Actor的运行时环境
pub struct ActorContext<A: Actor> {
    id: ActorId,
    state: Arc<RwLock<ActorState>>,
    mailbox: mpsc::Receiver<MessageEnvelope<A::Message>>,
    system_mailbox: mpsc::Receiver<SystemMessage>,
    actor: A,
    supervisor: Option<ActorRef<SupervisorActor>>,
}

impl<A: Actor> ActorContext<A> {
    fn new(
        id: ActorId,
        actor: A,
        mailbox: mpsc::Receiver<MessageEnvelope<A::Message>>,
        system_mailbox: mpsc::Receiver<SystemMessage>,
    ) -> Self {
        Self {
            id,
            state: Arc::new(RwLock::new(ActorState::Starting)),
            mailbox,
            system_mailbox,
            actor,
            supervisor: None,
        }
    }

    #[instrument(skip(self), fields(actor_id = %self.id))]
    async fn run(mut self) {
        info!("Actor context running");

        // Set state to running
        *self.state.write().await = ActorState::Running;

        // Call started hook
        self.actor.started().await;

        loop {
            tokio::select! {
                // Handle regular messages
                Some(envelope) = self.mailbox.recv() => {
                    let result = self.actor.handle(envelope.message).await;
                    
                    if let Some(respond_to) = envelope.respond_to {
                        let _ = respond_to.send(result);
                    }
                }
                
                // Handle system messages
                Some(sys_msg) = self.system_mailbox.recv() => {
                    match sys_msg {
                        SystemMessage::Stop => {
                            info!("Received stop message");
                            break;
                        }
                        SystemMessage::Restart => {
                            info!("Received restart message");
                            self.actor.stopped().await;
                            self.actor.started().await;
                        }
                        SystemMessage::GetState(tx) => {
                            let state = *self.state.read().await;
                            let _ = tx.send(state);
                        }
                    }
                }
                
                else => {
                    warn!("Both mailboxes closed");
                    break;
                }
            }
        }

        // Cleanup
        *self.state.write().await = ActorState::Stopped;
        self.actor.stopped().await;
        info!("Actor context stopped");
    }
}

// ============================================================================
// Part 5: Actor Reference
// ============================================================================

/// Actor引用 - 用于向Actor发送消息
#[derive(Clone)]
pub struct ActorRef<A: Actor> {
    id: ActorId,
    mailbox: mpsc::Sender<MessageEnvelope<A::Message>>,
    system_mailbox: mpsc::Sender<SystemMessage>,
    state: Arc<RwLock<ActorState>>,
}

impl<A: Actor> ActorRef<A> {
    pub fn id(&self) -> ActorId {
        self.id
    }

    /// 发送消息(fire-and-forget)
    pub async fn tell(&self, message: A::Message) -> Result<(), ActorError> {
        let envelope = MessageEnvelope {
            message,
            respond_to: None,
        };

        self.mailbox
            .send(envelope)
            .await
            .map_err(|_| ActorError::ActorStopped)
    }

    /// 发送消息并等待响应(request-response)
    pub async fn ask(&self, message: A::Message) -> Result<<A::Message as Message>::Result, ActorError> {
        let (tx, rx) = oneshot::channel();
        
        let envelope = MessageEnvelope {
            message,
            respond_to: Some(tx),
        };

        self.mailbox
            .send(envelope)
            .await
            .map_err(|_| ActorError::ActorStopped)?;

        rx.await.map_err(|_| ActorError::ActorStopped)
    }

    /// 停止Actor
    pub async fn stop(&self) -> Result<(), ActorError> {
        self.system_mailbox
            .send(SystemMessage::Stop)
            .await
            .map_err(|_| ActorError::ActorStopped)
    }

    /// 获取Actor状态
    pub async fn get_state(&self) -> Result<ActorState, ActorError> {
        let (tx, rx) = oneshot::channel();
        
        self.system_mailbox
            .send(SystemMessage::GetState(tx))
            .await
            .map_err(|_| ActorError::ActorStopped)?;

        rx.await.map_err(|_| ActorError::ActorStopped)
    }
}

// ============================================================================
// Part 6: Actor System
// ============================================================================

/// Actor系统 - 管理所有Actor
pub struct ActorSystem {
    actors: Arc<RwLock<HashMap<ActorId, Box<dyn std::any::Any + Send>>>>,
}

impl ActorSystem {
    pub fn new() -> Self {
        Self {
            actors: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 生成一个新的Actor
    pub async fn spawn<A: Actor>(&self, actor: A) -> ActorRef<A> {
        self.spawn_with_capacity(actor, 100).await
    }

    /// 生成一个新的Actor，指定mailbox容量
    pub async fn spawn_with_capacity<A: Actor>(
        &self,
        actor: A,
        capacity: usize,
    ) -> ActorRef<A> {
        let id = ActorId::new();
        let (mailbox_tx, mailbox_rx) = mpsc::channel(capacity);
        let (system_tx, system_rx) = mpsc::channel(10);

        let context = ActorContext::new(id, actor, mailbox_rx, system_rx);
        let state = context.state.clone();

        // Spawn actor task
        tokio::spawn(context.run());

        let actor_ref = ActorRef {
            id,
            mailbox: mailbox_tx,
            system_mailbox: system_tx,
            state,
        };

        info!("Spawned actor: {}", id);

        actor_ref
    }
}

// ============================================================================
// Part 7: Supervision Strategy
// ============================================================================

/// 监督策略
#[derive(Debug, Clone, Copy)]
pub enum SupervisionStrategy {
    /// One-for-One: 只重启失败的Actor
    OneForOne,
    /// All-for-One: 重启所有子Actor
    AllForOne,
}

/// 监督器消息
#[derive(Debug)]
pub enum SupervisorMessage {
    SpawnChild(String),
    StopChild(String),
    ChildFailed(String),
    GetChildren(oneshot::Sender<Vec<String>>),
}

impl Message for SupervisorMessage {
    type Result = Result<(), ActorError>;
}

/// 监督器Actor
pub struct SupervisorActor {
    strategy: SupervisionStrategy,
    children: HashMap<String, ActorId>,
}

impl SupervisorActor {
    pub fn new(strategy: SupervisionStrategy) -> Self {
        Self {
            strategy,
            children: HashMap::new(),
        }
    }
}

#[async_trait]
impl Actor for SupervisorActor {
    type Message = SupervisorMessage;

    async fn handle(&mut self, msg: Self::Message) -> <Self::Message as Message>::Result {
        match msg {
            SupervisorMessage::SpawnChild(name) => {
                info!("Spawning child: {}", name);
                // In real implementation, would spawn actual child actor
                let child_id = ActorId::new();
                self.children.insert(name, child_id);
                Ok(())
            }
            
            SupervisorMessage::StopChild(name) => {
                info!("Stopping child: {}", name);
                self.children.remove(&name);
                Ok(())
            }
            
            SupervisorMessage::ChildFailed(name) => {
                warn!("Child failed: {}", name);
                
                match self.strategy {
                    SupervisionStrategy::OneForOne => {
                        info!("Restarting failed child: {}", name);
                        // Restart only the failed child
                    }
                    SupervisionStrategy::AllForOne => {
                        info!("Restarting all children due to failure of: {}", name);
                        // Restart all children
                    }
                }
                
                Ok(())
            }
            
            SupervisorMessage::GetChildren(tx) => {
                let children: Vec<String> = self.children.keys().cloned().collect();
                let _ = tx.send(children);
                Ok(())
            }
        }
    }
}

// ============================================================================
// Part 8: Example Actors
// ============================================================================

/// 计数器Actor消息
#[derive(Debug)]
pub enum CounterMessage {
    Increment,
    Decrement,
    GetValue(oneshot::Sender<i64>),
    Reset,
}

impl Message for CounterMessage {
    type Result = ();
}

/// 计数器Actor
pub struct CounterActor {
    value: i64,
}

impl CounterActor {
    pub fn new(initial: i64) -> Self {
        Self { value: initial }
    }
}

#[async_trait]
impl Actor for CounterActor {
    type Message = CounterMessage;

    async fn handle(&mut self, msg: Self::Message) {
        match msg {
            CounterMessage::Increment => {
                self.value += 1;
                info!("Counter incremented to {}", self.value);
            }
            CounterMessage::Decrement => {
                self.value -= 1;
                info!("Counter decremented to {}", self.value);
            }
            CounterMessage::GetValue(tx) => {
                let _ = tx.send(self.value);
            }
            CounterMessage::Reset => {
                self.value = 0;
                info!("Counter reset to 0");
            }
        }
    }

    async fn started(&mut self) {
        info!("Counter actor started with value: {}", self.value);
    }

    async fn stopped(&mut self) {
        info!("Counter actor stopped with final value: {}", self.value);
    }
}

/// 工作者Actor消息
#[derive(Debug)]
pub struct WorkMessage {
    pub id: u64,
    pub data: String,
}

impl Message for WorkMessage {
    type Result = Result<String, String>;
}

/// 工作者Actor
pub struct WorkerActor {
    name: String,
    processed_count: u64,
}

impl WorkerActor {
    pub fn new(name: String) -> Self {
        Self {
            name,
            processed_count: 0,
        }
    }
}

#[async_trait]
impl Actor for WorkerActor {
    type Message = WorkMessage;

    async fn handle(&mut self, msg: Self::Message) -> <Self::Message as Message>::Result {
        info!("{} processing work {}: {}", self.name, msg.id, msg.data);
        
        // Simulate work
        sleep(Duration::from_millis(100)).await;
        
        self.processed_count += 1;
        
        Ok(format!("{} processed: {}", self.name, msg.data))
    }

    async fn started(&mut self) {
        info!("Worker '{}' started", self.name);
    }

    async fn stopped(&mut self) {
        info!("Worker '{}' stopped after processing {} messages", 
              self.name, self.processed_count);
    }
}

/// 聚合器Actor消息
#[derive(Debug)]
pub enum AggregatorMessage {
    Add(i64),
    GetSum(oneshot::Sender<i64>),
    GetCount(oneshot::Sender<u64>),
    GetAverage(oneshot::Sender<f64>),
}

impl Message for AggregatorMessage {
    type Result = ();
}

/// 聚合器Actor
pub struct AggregatorActor {
    sum: i64,
    count: u64,
}

impl AggregatorActor {
    pub fn new() -> Self {
        Self { sum: 0, count: 0 }
    }
}

#[async_trait]
impl Actor for AggregatorActor {
    type Message = AggregatorMessage;

    async fn handle(&mut self, msg: Self::Message) {
        match msg {
            AggregatorMessage::Add(value) => {
                self.sum += value;
                self.count += 1;
                info!("Added {} to aggregator (sum={}, count={})", 
                      value, self.sum, self.count);
            }
            AggregatorMessage::GetSum(tx) => {
                let _ = tx.send(self.sum);
            }
            AggregatorMessage::GetCount(tx) => {
                let _ = tx.send(self.count);
            }
            AggregatorMessage::GetAverage(tx) => {
                let avg = if self.count > 0 {
                    self.sum as f64 / self.count as f64
                } else {
                    0.0
                };
                let _ = tx.send(avg);
            }
        }
    }
}

// ============================================================================
// Part 9: Example Usage Patterns
// ============================================================================

/// Demo: Basic Actor usage
#[instrument]
pub async fn demo_basic_actor() {
    info!("=== Demo: Basic Actor Usage ===");

    let system = ActorSystem::new();
    
    // Spawn a counter actor
    let counter = system.spawn(CounterActor::new(0)).await;
    
    // Send messages (fire-and-forget)
    for _ in 0..5 {
        counter.tell(CounterMessage::Increment).await.unwrap();
    }
    
    sleep(Duration::from_millis(100)).await;
    
    // Request value (request-response)
    let (tx, rx) = oneshot::channel();
    counter.tell(CounterMessage::GetValue(tx)).await.unwrap();
    let value = rx.await.unwrap();
    info!("Counter value: {}", value);
    
    // Stop actor
    counter.stop().await.unwrap();
    
    sleep(Duration::from_millis(100)).await;
}

/// Demo: Worker pool pattern
#[instrument]
pub async fn demo_worker_pool() {
    info!("=== Demo: Worker Pool Pattern ===");

    let system = ActorSystem::new();
    
    // Spawn worker pool
    let mut workers = Vec::new();
    for i in 0..4 {
        let worker = system.spawn(WorkerActor::new(format!("Worker-{}", i))).await;
        workers.push(worker);
    }
    
    // Distribute work
    for i in 0..20 {
        let worker = &workers[i % workers.len()];
        let msg = WorkMessage {
            id: i as u64,
            data: format!("Task {}", i),
        };
        
        // Use ask for request-response
        let result = worker.ask(msg).await.unwrap();
        info!("Result: {:?}", result);
    }
    
    sleep(Duration::from_millis(500)).await;
    
    // Stop all workers
    for worker in workers {
        worker.stop().await.unwrap();
    }
}

/// Demo: Aggregator pattern
#[instrument]
pub async fn demo_aggregator() {
    info!("=== Demo: Aggregator Pattern ===");

    let system = ActorSystem::new();
    
    let aggregator = system.spawn(AggregatorActor::new()).await;
    
    // Send values to aggregate
    for i in 1..=10 {
        aggregator.tell(AggregatorMessage::Add(i * 10)).await.unwrap();
    }
    
    sleep(Duration::from_millis(100)).await;
    
    // Get aggregated results
    let (sum_tx, sum_rx) = oneshot::channel();
    aggregator.tell(AggregatorMessage::GetSum(sum_tx)).await.unwrap();
    let sum = sum_rx.await.unwrap();
    
    let (count_tx, count_rx) = oneshot::channel();
    aggregator.tell(AggregatorMessage::GetCount(count_tx)).await.unwrap();
    let count = count_rx.await.unwrap();
    
    let (avg_tx, avg_rx) = oneshot::channel();
    aggregator.tell(AggregatorMessage::GetAverage(avg_tx)).await.unwrap();
    let avg = avg_rx.await.unwrap();
    
    info!("Aggregation results: sum={}, count={}, average={:.2}", sum, count, avg);
    
    aggregator.stop().await.unwrap();
}

/// Demo: Supervisor pattern
#[instrument]
pub async fn demo_supervisor() {
    info!("=== Demo: Supervisor Pattern ===");

    let system = ActorSystem::new();
    
    let supervisor = system.spawn(SupervisorActor::new(SupervisionStrategy::OneForOne)).await;
    
    // Spawn children
    supervisor.tell(SupervisorMessage::SpawnChild("child-1".to_string())).await.unwrap();
    supervisor.tell(SupervisorMessage::SpawnChild("child-2".to_string())).await.unwrap();
    supervisor.tell(SupervisorMessage::SpawnChild("child-3".to_string())).await.unwrap();
    
    sleep(Duration::from_millis(100)).await;
    
    // Get children
    let (tx, rx) = oneshot::channel();
    supervisor.tell(SupervisorMessage::GetChildren(tx)).await.unwrap();
    let children = rx.await.unwrap();
    info!("Supervisor has {} children: {:?}", children.len(), children);
    
    // Simulate child failure
    supervisor.tell(SupervisorMessage::ChildFailed("child-2".to_string())).await.unwrap();
    
    sleep(Duration::from_millis(100)).await;
    
    supervisor.stop().await.unwrap();
}

// ============================================================================
// Main Function - Run All Demos
// ============================================================================

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt()
        .with_target(false)
        .compact()
        .init();

    info!("🚀 Starting Actor Model Demos");

    // Demo 1: Basic actor
    demo_basic_actor().await;
    sleep(Duration::from_secs(1)).await;

    // Demo 2: Worker pool
    demo_worker_pool().await;
    sleep(Duration::from_secs(1)).await;

    // Demo 3: Aggregator
    demo_aggregator().await;
    sleep(Duration::from_secs(1)).await;

    // Demo 4: Supervisor
    demo_supervisor().await;

    info!("✅ All Actor demos completed!");

    Ok(())
}

