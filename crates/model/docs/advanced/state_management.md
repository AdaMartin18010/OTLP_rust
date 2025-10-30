# 状态管理和状态机完整指南

**Crate:** c12_model  
**主题:** State Management & State Machines  
**Rust 版本:** 1.90.0  
**最后更新:** 2025年10月28日

---

## 📋 目录

- [状态管理和状态机完整指南](#状态管理和状态机完整指南)
  - [📋 目录](#-目录)
  - [状态管理概述](#状态管理概述)
    - [状态机的重要性](#状态机的重要性)
    - [状态机类型](#状态机类型)
  - [有限状态机(FSM)](#有限状态机fsm)
    - [1. 基本 FSM 实现](#1-基本-fsm-实现)
      - [订单状态机](#订单状态机)
    - [2. 类型安全的状态机](#2-类型安全的状态机)
      - [使用类型系统强制正确的状态转换](#使用类型系统强制正确的状态转换)
  - [层次状态机(HSM)](#层次状态机hsm)
    - [实现](#实现)
  - [状态模式实现](#状态模式实现)
    - [使用 Trait Objects](#使用-trait-objects)
  - [事件驱动状态机](#事件驱动状态机)
    - [实现](#实现-1)
  - [状态持久化](#状态持久化)
    - [实现](#实现-2)
  - [状态迁移和验证](#状态迁移和验证)
    - [实现](#实现-3)
  - [状态机可视化](#状态机可视化)
    - [生成 Graphviz DOT 格式](#生成-graphviz-dot-格式)
  - [总结](#总结)
    - [状态机清单](#状态机清单)
    - [最佳实践](#最佳实践)

---

## 状态管理概述

### 状态机的重要性

```
┌────────────────────────────────────────┐
│        状态机的应用场景                  │
├────────────────────────────────────────┤
│ 1. 订单处理流程                         │
│ 2. 工作流引擎                           │
│ 3. 网络协议                             │
│ 4. 游戏逻辑                             │
│ 5. UI 状态管理                          │
│ 6. 设备状态控制                         │
└────────────────────────────────────────┘
```

### 状态机类型

```
有限状态机 (FSM)
    ├─ Mealy Machine (输出依赖输入)
    └─ Moore Machine (输出只依赖状态)

层次状态机 (HSM)
    └─ 状态可以包含子状态

并发状态机
    └─ 多个状态机并行运行
```

---

## 有限状态机(FSM)

### 1. 基本 FSM 实现

#### 订单状态机

```rust
use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OrderState {
    Created,
    Paid,
    Processing,
    Shipped,
    Delivered,
    Cancelled,
}

#[derive(Debug, Clone, Copy)]
pub enum OrderEvent {
    Pay,
    Process,
    Ship,
    Deliver,
    Cancel,
}

pub struct OrderStateMachine {
    current_state: OrderState,
    history: Vec<(OrderState, OrderEvent)>,
}

impl OrderStateMachine {
    pub fn new() -> Self {
        Self {
            current_state: OrderState::Created,
            history: Vec::new(),
        }
    }
    
    pub fn current_state(&self) -> OrderState {
        self.current_state
    }
    
    /// 处理事件，返回新状态
    pub fn handle_event(&mut self, event: OrderEvent) -> Result<OrderState> {
        let old_state = self.current_state;
        
        let new_state = match (self.current_state, event) {
            // Created -> Paid
            (OrderState::Created, OrderEvent::Pay) => OrderState::Paid,
            
            // Paid -> Processing
            (OrderState::Paid, OrderEvent::Process) => OrderState::Processing,
            
            // Processing -> Shipped
            (OrderState::Processing, OrderEvent::Ship) => OrderState::Shipped,
            
            // Shipped -> Delivered
            (OrderState::Shipped, OrderEvent::Deliver) => OrderState::Delivered,
            
            // 任何状态都可以取消（除了已交付）
            (OrderState::Delivered, OrderEvent::Cancel) => {
                return Err(anyhow::anyhow!("Cannot cancel delivered order"));
            }
            (_, OrderEvent::Cancel) => OrderState::Cancelled,
            
            // 无效的状态转换
            (state, event) => {
                return Err(anyhow::anyhow!(
                    "Invalid transition: {:?} -> {:?}",
                    state, event
                ));
            }
        };
        
        // 记录历史
        self.history.push((old_state, event));
        
        // 更新状态
        self.current_state = new_state;
        
        // 触发状态进入回调
        self.on_enter_state(new_state);
        
        Ok(new_state)
    }
    
    fn on_enter_state(&self, state: OrderState) {
        match state {
            OrderState::Paid => {
                println!("Order paid, sending confirmation email");
            }
            OrderState::Shipped => {
                println!("Order shipped, notifying customer");
            }
            OrderState::Delivered => {
                println!("Order delivered, requesting feedback");
            }
            _ => {}
        }
    }
    
    /// 获取允许的事件
    pub fn allowed_events(&self) -> Vec<OrderEvent> {
        match self.current_state {
            OrderState::Created => vec![OrderEvent::Pay, OrderEvent::Cancel],
            OrderState::Paid => vec![OrderEvent::Process, OrderEvent::Cancel],
            OrderState::Processing => vec![OrderEvent::Ship, OrderEvent::Cancel],
            OrderState::Shipped => vec![OrderEvent::Deliver, OrderEvent::Cancel],
            OrderState::Delivered => vec![],
            OrderState::Cancelled => vec![],
        }
    }
}

// 使用示例
#[tokio::main]
async fn main() -> Result<()> {
    let mut order = OrderStateMachine::new();
    
    // 创建 -> 支付
    order.handle_event(OrderEvent::Pay)?;
    assert_eq!(order.current_state(), OrderState::Paid);
    
    // 支付 -> 处理
    order.handle_event(OrderEvent::Process)?;
    assert_eq!(order.current_state(), OrderState::Processing);
    
    // 处理 -> 发货
    order.handle_event(OrderEvent::Ship)?;
    assert_eq!(order.current_state(), OrderState::Shipped);
    
    // 发货 -> 送达
    order.handle_event(OrderEvent::Deliver)?;
    assert_eq!(order.current_state(), OrderState::Delivered);
    
    // 尝试取消已送达订单（失败）
    assert!(order.handle_event(OrderEvent::Cancel).is_err());
    
    Ok(())
}
```

---

### 2. 类型安全的状态机

#### 使用类型系统强制正确的状态转换

```rust
// 状态类型
pub struct Created;
pub struct Paid;
pub struct Processing;
pub struct Shipped;
pub struct Delivered;
pub struct Cancelled;

// Order 类型，泛型参数表示当前状态
pub struct Order<State> {
    id: u64,
    amount: f64,
    _state: std::marker::PhantomData<State>,
}

impl Order<Created> {
    pub fn new(id: u64, amount: f64) -> Self {
        Self {
            id,
            amount,
            _state: std::marker::PhantomData,
        }
    }
    
    /// Created -> Paid
    pub fn pay(self) -> Order<Paid> {
        println!("Order {} paid", self.id);
        Order {
            id: self.id,
            amount: self.amount,
            _state: std::marker::PhantomData,
        }
    }
    
    /// Created -> Cancelled
    pub fn cancel(self) -> Order<Cancelled> {
        println!("Order {} cancelled", self.id);
        Order {
            id: self.id,
            amount: self.amount,
            _state: std::marker::PhantomData,
        }
    }
}

impl Order<Paid> {
    /// Paid -> Processing
    pub fn process(self) -> Order<Processing> {
        println!("Order {} processing", self.id);
        Order {
            id: self.id,
            amount: self.amount,
            _state: std::marker::PhantomData,
        }
    }
    
    pub fn cancel(self) -> Order<Cancelled> {
        println!("Order {} cancelled, refunding", self.id);
        Order {
            id: self.id,
            amount: self.amount,
            _state: std::marker::PhantomData,
        }
    }
}

impl Order<Processing> {
    /// Processing -> Shipped
    pub fn ship(self) -> Order<Shipped> {
        println!("Order {} shipped", self.id);
        Order {
            id: self.id,
            amount: self.amount,
            _state: std::marker::PhantomData,
        }
    }
}

impl Order<Shipped> {
    /// Shipped -> Delivered
    pub fn deliver(self) -> Order<Delivered> {
        println!("Order {} delivered", self.id);
        Order {
            id: self.id,
            amount: self.amount,
            _state: std::marker::PhantomData,
        }
    }
}

// 使用示例
fn type_safe_order_flow() {
    let order = Order::<Created>::new(1, 99.99);
    
    // ✅ 合法的状态转换
    let order = order.pay();
    let order = order.process();
    let order = order.ship();
    let order = order.deliver();
    
    // ❌ 编译错误：Delivered 状态没有 cancel 方法
    // order.cancel();
    
    // ❌ 编译错误：不能从 Created 直接到 Shipped
    // let order = Order::<Created>::new(2, 50.0);
    // order.ship();  // 编译失败
}
```

---

## 层次状态机(HSM)

### 实现

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum DeviceState {
    Off,
    On(OnState),
}

#[derive(Debug, Clone, PartialEq)]
pub enum OnState {
    Idle,
    Working(WorkingState),
}

#[derive(Debug, Clone, PartialEq)]
pub enum WorkingState {
    Processing,
    Paused,
}

#[derive(Debug, Clone)]
pub enum DeviceEvent {
    PowerOn,
    PowerOff,
    StartWork,
    Pause,
    Resume,
    FinishWork,
}

pub struct DeviceStateMachine {
    state: DeviceState,
}

impl DeviceStateMachine {
    pub fn new() -> Self {
        Self {
            state: DeviceState::Off,
        }
    }
    
    pub fn handle_event(&mut self, event: DeviceEvent) -> Result<()> {
        match (&self.state, event) {
            // Off -> On(Idle)
            (DeviceState::Off, DeviceEvent::PowerOn) => {
                self.state = DeviceState::On(OnState::Idle);
                self.on_power_on();
            }
            
            // On -> Off (从任何 On 子状态)
            (DeviceState::On(_), DeviceEvent::PowerOff) => {
                self.on_power_off();
                self.state = DeviceState::Off;
            }
            
            // On(Idle) -> On(Working(Processing))
            (DeviceState::On(OnState::Idle), DeviceEvent::StartWork) => {
                self.state = DeviceState::On(OnState::Working(WorkingState::Processing));
                self.on_start_work();
            }
            
            // On(Working(Processing)) -> On(Working(Paused))
            (DeviceState::On(OnState::Working(WorkingState::Processing)), DeviceEvent::Pause) => {
                self.state = DeviceState::On(OnState::Working(WorkingState::Paused));
                self.on_pause();
            }
            
            // On(Working(Paused)) -> On(Working(Processing))
            (DeviceState::On(OnState::Working(WorkingState::Paused)), DeviceEvent::Resume) => {
                self.state = DeviceState::On(OnState::Working(WorkingState::Processing));
                self.on_resume();
            }
            
            // On(Working(_)) -> On(Idle)
            (DeviceState::On(OnState::Working(_)), DeviceEvent::FinishWork) => {
                self.state = DeviceState::On(OnState::Idle);
                self.on_finish_work();
            }
            
            (state, event) => {
                return Err(anyhow::anyhow!(
                    "Invalid transition: {:?} with event {:?}",
                    state, event
                ));
            }
        }
        
        Ok(())
    }
    
    fn on_power_on(&self) {
        println!("Device powered on, initializing...");
    }
    
    fn on_power_off(&self) {
        println!("Device powering off, saving state...");
    }
    
    fn on_start_work(&self) {
        println!("Starting work...");
    }
    
    fn on_pause(&self) {
        println!("Work paused");
    }
    
    fn on_resume(&self) {
        println!("Work resumed");
    }
    
    fn on_finish_work(&self) {
        println!("Work finished");
    }
}
```

---

## 状态模式实现

### 使用 Trait Objects

```rust
use async_trait::async_trait;

#[async_trait]
pub trait ConnectionState: Send + Sync {
    async fn connect(&self, ctx: &mut Connection) -> Result<Box<dyn ConnectionState>>;
    async fn disconnect(&self, ctx: &mut Connection) -> Result<Box<dyn ConnectionState>>;
    async fn send_data(&self, ctx: &mut Connection, data: &[u8]) -> Result<()>;
    fn state_name(&self) -> &'static str;
}

pub struct Connection {
    state: Box<dyn ConnectionState>,
    socket: Option<TcpStream>,
}

impl Connection {
    pub fn new() -> Self {
        Self {
            state: Box::new(DisconnectedState),
            socket: None,
        }
    }
    
    pub async fn connect(&mut self) -> Result<()> {
        let new_state = self.state.connect(self).await?;
        self.state = new_state;
        Ok(())
    }
    
    pub async fn disconnect(&mut self) -> Result<()> {
        let new_state = self.state.disconnect(self).await?;
        self.state = new_state;
        Ok(())
    }
    
    pub async fn send(&mut self, data: &[u8]) -> Result<()> {
        self.state.send_data(self, data).await
    }
    
    pub fn current_state(&self) -> &str {
        self.state.state_name()
    }
}

// Disconnected State
pub struct DisconnectedState;

#[async_trait]
impl ConnectionState for DisconnectedState {
    async fn connect(&self, ctx: &mut Connection) -> Result<Box<dyn ConnectionState>> {
        println!("Connecting...");
        
        // 建立连接
        let socket = TcpStream::connect("127.0.0.1:8080").await?;
        ctx.socket = Some(socket);
        
        Ok(Box::new(ConnectingState))
    }
    
    async fn disconnect(&self, _ctx: &mut Connection) -> Result<Box<dyn ConnectionState>> {
        Err(anyhow::anyhow!("Already disconnected"))
    }
    
    async fn send_data(&self, _ctx: &mut Connection, _data: &[u8]) -> Result<()> {
        Err(anyhow::anyhow!("Not connected"))
    }
    
    fn state_name(&self) -> &'static str {
        "Disconnected"
    }
}

// Connecting State
pub struct ConnectingState;

#[async_trait]
impl ConnectionState for ConnectingState {
    async fn connect(&self, _ctx: &mut Connection) -> Result<Box<dyn ConnectionState>> {
        Err(anyhow::anyhow!("Already connecting"))
    }
    
    async fn disconnect(&self, ctx: &mut Connection) -> Result<Box<dyn ConnectionState>> {
        // 取消连接
        ctx.socket = None;
        Ok(Box::new(DisconnectedState))
    }
    
    async fn send_data(&self, _ctx: &mut Connection, _data: &[u8]) -> Result<()> {
        Err(anyhow::anyhow!("Still connecting"))
    }
    
    fn state_name(&self) -> &'static str {
        "Connecting"
    }
}

// Connected State
pub struct ConnectedState;

#[async_trait]
impl ConnectionState for ConnectedState {
    async fn connect(&self, _ctx: &mut Connection) -> Result<Box<dyn ConnectionState>> {
        Err(anyhow::anyhow!("Already connected"))
    }
    
    async fn disconnect(&self, ctx: &mut Connection) -> Result<Box<dyn ConnectionState>> {
        println!("Disconnecting...");
        ctx.socket = None;
        Ok(Box::new(DisconnectedState))
    }
    
    async fn send_data(&self, ctx: &mut Connection, data: &[u8]) -> Result<()> {
        if let Some(socket) = &mut ctx.socket {
            socket.write_all(data).await?;
            Ok(())
        } else {
            Err(anyhow::anyhow!("Socket not available"))
        }
    }
    
    fn state_name(&self) -> &'static str {
        "Connected"
    }
}
```

---

## 事件驱动状态机

### 实现

```rust
use tokio::sync::mpsc;

pub struct EventDrivenStateMachine {
    state: OrderState,
    event_tx: mpsc::UnboundedSender<OrderEvent>,
    event_rx: mpsc::UnboundedReceiver<OrderEvent>,
}

impl EventDrivenStateMachine {
    pub fn new() -> Self {
        let (event_tx, event_rx) = mpsc::unbounded_channel();
        
        Self {
            state: OrderState::Created,
            event_tx,
            event_rx,
        }
    }
    
    /// 发送事件
    pub fn send_event(&self, event: OrderEvent) -> Result<()> {
        self.event_tx.send(event)
            .map_err(|e| anyhow::anyhow!("Failed to send event: {}", e))
    }
    
    /// 运行事件循环
    pub async fn run(mut self) {
        while let Some(event) = self.event_rx.recv().await {
            match self.handle_event(event) {
                Ok(new_state) => {
                    println!("Transitioned: {:?} -> {:?}", self.state, new_state);
                    self.state = new_state;
                }
                Err(e) => {
                    eprintln!("Error handling event: {}", e);
                }
            }
        }
    }
    
    fn handle_event(&self, event: OrderEvent) -> Result<OrderState> {
        // 状态转换逻辑（与之前相同）
        match (self.state, event) {
            (OrderState::Created, OrderEvent::Pay) => Ok(OrderState::Paid),
            (OrderState::Paid, OrderEvent::Process) => Ok(OrderState::Processing),
            // ... 其他转换
            (state, event) => Err(anyhow::anyhow!(
                "Invalid transition: {:?} with event {:?}",
                state, event
            )),
        }
    }
}

// 使用示例
#[tokio::main]
async fn main() {
    let sm = EventDrivenStateMachine::new();
    let sm_handle = sm.event_tx.clone();
    
    // 启动状态机
    tokio::spawn(async move {
        sm.run().await;
    });
    
    // 发送事件
    sm_handle.send(OrderEvent::Pay).unwrap();
    sm_handle.send(OrderEvent::Process).unwrap();
    sm_handle.send(OrderEvent::Ship).unwrap();
    sm_handle.send(OrderEvent::Deliver).unwrap();
    
    // 等待处理
    tokio::time::sleep(Duration::from_secs(1)).await;
}
```

---

## 状态持久化

### 实现

```rust
use serde::{Serialize, Deserialize};
use sqlx::PgPool;

#[derive(Debug, Serialize, Deserialize)]
pub struct StateMachineSnapshot {
    pub id: String,
    pub current_state: OrderState,
    pub history: Vec<StateTransition>,
    pub created_at: chrono::DateTime<chrono::Utc>,
    pub updated_at: chrono::DateTime<chrono::Utc>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct StateTransition {
    pub from_state: OrderState,
    pub to_state: OrderState,
    pub event: OrderEvent,
    pub timestamp: chrono::DateTime<chrono::Utc>,
}

pub struct PersistentStateMachine {
    id: String,
    state_machine: OrderStateMachine,
    pool: PgPool,
}

impl PersistentStateMachine {
    pub async fn new(id: String, pool: PgPool) -> Result<Self> {
        // 尝试从数据库加载
        let snapshot = Self::load_snapshot(&id, &pool).await?;
        
        let state_machine = if let Some(snap) = snapshot {
            // 恢复状态
            OrderStateMachine {
                current_state: snap.current_state,
                history: snap.history.into_iter()
                    .map(|t| (t.from_state, t.event))
                    .collect(),
            }
        } else {
            // 新建状态机
            OrderStateMachine::new()
        };
        
        Ok(Self {
            id,
            state_machine,
            pool,
        })
    }
    
    pub async fn handle_event(&mut self, event: OrderEvent) -> Result<OrderState> {
        let old_state = self.state_machine.current_state();
        
        // 处理事件
        let new_state = self.state_machine.handle_event(event)?;
        
        // 持久化状态
        self.save_transition(old_state, new_state, event).await?;
        
        Ok(new_state)
    }
    
    async fn save_transition(
        &self,
        from_state: OrderState,
        to_state: OrderState,
        event: OrderEvent,
    ) -> Result<()> {
        sqlx::query!(
            r#"
            INSERT INTO state_transitions 
            (machine_id, from_state, to_state, event, timestamp)
            VALUES ($1, $2, $3, $4, $5)
            "#,
            self.id,
            serde_json::to_value(&from_state)?,
            serde_json::to_value(&to_state)?,
            serde_json::to_value(&event)?,
            chrono::Utc::now()
        )
        .execute(&self.pool)
        .await?;
        
        // 更新当前状态
        sqlx::query!(
            r#"
            INSERT INTO state_machines (id, current_state, updated_at)
            VALUES ($1, $2, $3)
            ON CONFLICT (id) DO UPDATE
            SET current_state = $2, updated_at = $3
            "#,
            self.id,
            serde_json::to_value(&to_state)?,
            chrono::Utc::now()
        )
        .execute(&self.pool)
        .await?;
        
        Ok(())
    }
    
    async fn load_snapshot(id: &str, pool: &PgPool) -> Result<Option<StateMachineSnapshot>> {
        let row = sqlx::query!(
            r#"
            SELECT current_state, created_at, updated_at
            FROM state_machines
            WHERE id = $1
            "#,
            id
        )
        .fetch_optional(pool)
        .await?;
        
        if let Some(row) = row {
            // 加载历史
            let transitions = sqlx::query!(
                r#"
                SELECT from_state, to_state, event, timestamp
                FROM state_transitions
                WHERE machine_id = $1
                ORDER BY timestamp
                "#,
                id
            )
            .fetch_all(pool)
            .await?;
            
            let history = transitions.into_iter()
                .map(|t| StateTransition {
                    from_state: serde_json::from_value(t.from_state).unwrap(),
                    to_state: serde_json::from_value(t.to_state).unwrap(),
                    event: serde_json::from_value(t.event).unwrap(),
                    timestamp: t.timestamp,
                })
                .collect();
            
            Ok(Some(StateMachineSnapshot {
                id: id.to_string(),
                current_state: serde_json::from_value(row.current_state)?,
                history,
                created_at: row.created_at,
                updated_at: row.updated_at,
            }))
        } else {
            Ok(None)
        }
    }
}
```

---

## 状态迁移和验证

### 实现

```rust
pub struct StateMachineValidator {
    valid_transitions: HashMap<(OrderState, OrderEvent), OrderState>,
    guards: HashMap<(OrderState, OrderEvent), Box<dyn Fn(&Order) -> bool + Send + Sync>>,
}

impl StateMachineValidator {
    pub fn new() -> Self {
        let mut valid_transitions = HashMap::new();
        
        // 定义所有有效的转换
        valid_transitions.insert(
            (OrderState::Created, OrderEvent::Pay),
            OrderState::Paid
        );
        valid_transitions.insert(
            (OrderState::Paid, OrderEvent::Process),
            OrderState::Processing
        );
        // ... 其他转换
        
        Self {
            valid_transitions,
            guards: HashMap::new(),
        }
    }
    
    /// 添加守卫条件
    pub fn add_guard<F>(&mut self, state: OrderState, event: OrderEvent, guard: F)
    where
        F: Fn(&Order) -> bool + Send + Sync + 'static,
    {
        self.guards.insert((state, event), Box::new(guard));
    }
    
    /// 验证状态转换
    pub fn validate_transition(
        &self,
        order: &Order,
        from_state: OrderState,
        event: OrderEvent,
    ) -> Result<OrderState> {
        // 1. 检查转换是否存在
        let to_state = self.valid_transitions
            .get(&(from_state, event))
            .ok_or_else(|| anyhow::anyhow!("Invalid transition"))?;
        
        // 2. 检查守卫条件
        if let Some(guard) = self.guards.get(&(from_state, event)) {
            if !guard(order) {
                return Err(anyhow::anyhow!("Guard condition failed"));
            }
        }
        
        Ok(*to_state)
    }
}

// 使用示例
fn setup_validator() -> StateMachineValidator {
    let mut validator = StateMachineValidator::new();
    
    // 添加守卫：只有金额 > 0 才能支付
    validator.add_guard(
        OrderState::Created,
        OrderEvent::Pay,
        |order| order.amount > 0.0
    );
    
    // 添加守卫：只有库存充足才能处理
    validator.add_guard(
        OrderState::Paid,
        OrderEvent::Process,
        |order| check_inventory(order.items)
    );
    
    validator
}
```

---

## 状态机可视化

### 生成 Graphviz DOT 格式

```rust
pub struct StateMachineVisualizer {
    transitions: Vec<(OrderState, OrderEvent, OrderState)>,
}

impl StateMachineVisualizer {
    pub fn new() -> Self {
        Self {
            transitions: vec![
                (OrderState::Created, OrderEvent::Pay, OrderState::Paid),
                (OrderState::Paid, OrderEvent::Process, OrderState::Processing),
                (OrderState::Processing, OrderEvent::Ship, OrderState::Shipped),
                (OrderState::Shipped, OrderEvent::Deliver, OrderState::Delivered),
                // 取消转换
                (OrderState::Created, OrderEvent::Cancel, OrderState::Cancelled),
                (OrderState::Paid, OrderEvent::Cancel, OrderState::Cancelled),
                (OrderState::Processing, OrderEvent::Cancel, OrderState::Cancelled),
            ],
        }
    }
    
    pub fn generate_dot(&self) -> String {
        let mut dot = String::from("digraph OrderStateMachine {\n");
        dot.push_str("    rankdir=LR;\n");
        dot.push_str("    node [shape=circle];\n\n");
        
        // 起始状态
        dot.push_str("    Created [shape=doublecircle];\n");
        
        // 终止状态
        dot.push_str("    Delivered [shape=doublecircle];\n");
        dot.push_str("    Cancelled [shape=doublecircle];\n\n");
        
        // 转换
        for (from, event, to) in &self.transitions {
            dot.push_str(&format!(
                "    {:?} -> {:?} [label=\"{:?}\"];\n",
                from, to, event
            ));
        }
        
        dot.push_str("}\n");
        dot
    }
    
    pub fn save_to_file(&self, path: &str) -> Result<()> {
        let dot = self.generate_dot();
        std::fs::write(path, dot)?;
        Ok(())
    }
}

// 使用示例
fn visualize_state_machine() {
    let visualizer = StateMachineVisualizer::new();
    visualizer.save_to_file("order_state_machine.dot").unwrap();
    
    // 使用 Graphviz 生成图片:
    // dot -Tpng order_state_machine.dot -o order_state_machine.png
}
```

---

## 总结

### 状态机清单

- ✅ **FSM**: 有限状态机基本实现
- ✅ **HSM**: 层次状态机
- ✅ **状态模式**: Trait Objects 实现
- ✅ **事件驱动**: 异步事件处理
- ✅ **持久化**: 数据库状态存储
- ✅ **验证**: 转换验证和守卫
- ✅ **可视化**: Graphviz 图表生成

### 最佳实践

1. **类型安全**: 使用类型系统保证正确性
2. **事件驱动**: 解耦状态机和业务逻辑
3. **持久化**: 关键状态需要持久化
4. **验证**: 添加守卫条件验证转换
5. **可视化**: 生成状态图辅助理解

---

**文档贡献者:** AI Assistant  
**审核状态:** ✅ 已完成  
**最后更新:** 2025年10月28日

