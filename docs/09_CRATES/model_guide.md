# 🎨 Model Crate 使用指南

**版本**: 1.0  
**定位**: Rust各领域的设计模型、形式模型、架构模型、软件模型  
**最后更新**: 2025年10月26日  
**状态**: 🟢 活跃维护

> **简介**: Model Crate 使用指南 - 设计模型、形式模型和架构模型的完整指南。

---

## 📋 目录

- [🎨 Model Crate 使用指南](#-model-crate-使用指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [核心功能](#核心功能)
    - [📦 模型分类](#-模型分类)
  - [快速开始](#快速开始)
    - [安装依赖](#安装依赖)
    - [基础示例](#基础示例)
  - [形式化模型](#形式化模型)
    - [操作语义](#操作语义)
      - [小步语义 (Small-Step Semantics)](#小步语义-small-step-semantics)
      - [大步语义 (Big-Step Semantics)](#大步语义-big-step-semantics)
    - [指称语义](#指称语义)
    - [时序逻辑](#时序逻辑)
  - [架构模型](#架构模型)
    - [分层架构](#分层架构)
    - [六边形架构 (端口与适配器)](#六边形架构-端口与适配器)
    - [微服务架构](#微服务架构)
  - [设计模式](#设计模式)
    - [Builder 模式](#builder-模式)
    - [Observer 模式](#observer-模式)
    - [Strategy 模式](#strategy-模式)
  - [并发模型](#并发模型)
    - [Actor 模型](#actor-模型)
    - [CSP (Communicating Sequential Processes)](#csp-communicating-sequential-processes)
    - [Work-Stealing 调度](#work-stealing-调度)
  - [分布式模型](#分布式模型)
    - [Raft 共识算法](#raft-共识算法)
    - [Paxos 协议](#paxos-协议)
    - [分布式快照 (Chandy-Lamport)](#分布式快照-chandy-lamport)
  - [最佳实践](#最佳实践)
    - [形式化验证](#形式化验证)
    - [架构验证](#架构验证)
    - [分布式系统测试](#分布式系统测试)
  - [完整文档](#完整文档)
    - [📚 详细文档](#-详细文档)
    - [📖 主要文档索引](#-主要文档索引)
    - [🎯 示例代码](#-示例代码)
  - [🔗 相关资源](#-相关资源)
    - [项目文档](#项目文档)
    - [架构文档](#架构文档)
    - [主文档](#主文档)
  - [🤝 贡献](#-贡献)

---

## 概述

`model` crate 提供了 Rust 中各领域的设计模型、形式化方法、架构模式的完整实现。它专注于:

- ✅ **形式化模型**: 操作语义、指称语义、时序逻辑等理论基础
- ✅ **架构模型**: 分层架构、六边形架构、微服务架构等
- ✅ **设计模式**: Builder、Factory、Observer等经典模式
- ✅ **并发模型**: Actor、CSP、STM、Fork-Join等并发范式
- ✅ **分布式模型**: Raft、Paxos、一致性哈希、分布式事务

---

## 核心功能

### 📦 模型分类

```text
model/
├── 🔬 形式化模型 (formal_models/)
│   ├── 操作语义 (小步/大步语义)
│   ├── 指称语义 (数学函数映射)
│   ├── 公理语义 (Hoare逻辑)
│   └── 时序逻辑 (LTL/CTL)
│
├── 🏛️ 架构模型 (architecture_design_models/)
│   ├── 分层架构 (Layered Architecture)
│   ├── 六边形架构 (Hexagonal/Ports & Adapters)
│   ├── 事件驱动架构 (Event-Driven)
│   ├── CQRS (命令查询职责分离)
│   ├── 微服务架构 (Microservices)
│   └── P2P架构 (Peer-to-Peer)
│
├── 🎨 设计模式 (patterns/)
│   ├── 创建型: Builder, Factory, Singleton
│   ├── 结构型: Adapter, Decorator, Proxy
│   └── 行为型: Observer, Strategy, Command
│
├── 🔄 并发模型 (parallel_concurrent_models/)
│   ├── Actor模型
│   ├── CSP (Communicating Sequential Processes)
│   ├── STM (Software Transactional Memory)
│   ├── Fork-Join
│   └── Work-Stealing调度
│
└── 🌐 分布式模型 (distributed_models/)
    ├── Raft共识算法
    ├── Paxos协议
    ├── 2PC/3PC (两阶段/三阶段提交)
    ├── 分布式快照 (Chandy-Lamport)
    └── 向量时钟 (Vector Clock)
```

---

## 快速开始

### 安装依赖

在 `Cargo.toml` 中添加:

```toml
[dependencies]
c12_model = { path = "crates/model" }

# 或使用特性标志
c12_model = { path = "crates/model", features = ["formal", "distributed", "concurrent"] }
```

### 基础示例

```rust
use c12_model::*;

#[tokio::main]
async fn main() -> Result<()> {
    // 1. 形式化语义分析
    let semantics = SmallStepSemantics::new();
    let expr = Expression::Add(Box::new(Value(1)), Box::new(Value(2)));
    let result = semantics.evaluate(expr)?;
    println!("Result: {}", result);
    
    // 2. Raft共识算法
    let raft = RaftProtocol::new(
        "node1".to_string(),
        Duration::from_millis(150),
        Duration::from_millis(50),
    );
    raft.start_election()?;
    raft.append_entry("SET x = 10".to_string())?;
    
    // 3. CSP并发模型
    let mut csp = CSPModel::new();
    csp.send("producer", "channel", "data")?;
    let msg = csp.receive("consumer", "channel")?;
    
    // 4. 架构模式 - 六边形架构
    let hex_arch = HexagonalArchitecture::new();
    hex_arch.add_port("HTTP", PortType::Input);
    hex_arch.add_adapter("HTTPAdapter", "HTTP", AdapterType::Input);
    
    Ok(())
}
```

---

## 形式化模型

### 操作语义

**操作语义**描述程序如何一步步执行。

#### 小步语义 (Small-Step Semantics)

每次执行一小步,描述程序的状态转换:

```rust
use c12_model::formal_models::*;

// 定义表达式
enum Expression {
    Value(i32),
    Add(Box<Expression>, Box<Expression>),
    Mul(Box<Expression>, Box<Expression>),
}

// 小步语义求值器
struct SmallStepSemantics;

impl SmallStepSemantics {
    fn step(&self, expr: Expression) -> Option<Expression> {
        match expr {
            Expression::Add(box Expression::Value(n1), box Expression::Value(n2)) => {
                Some(Expression::Value(n1 + n2))
            }
            Expression::Add(box e1, box e2) => {
                if let Some(e1_next) = self.step(e1) {
                    Some(Expression::Add(Box::new(e1_next), Box::new(e2)))
                } else if let Some(e2_next) = self.step(e2) {
                    Some(Expression::Add(Box::new(Expression::Value(n1)), Box::new(e2_next)))
                } else {
                    None
                }
            }
            Expression::Value(_) => None,
            _ => todo!(),
        }
    }
    
    fn evaluate(&self, mut expr: Expression) -> i32 {
        while let Some(next) = self.step(expr) {
            expr = next;
        }
        match expr {
            Expression::Value(n) => n,
            _ => panic!("Invalid expression"),
        }
    }
}

// 使用示例
fn main() {
    let sem = SmallStepSemantics;
    let expr = Expression::Add(
        Box::new(Expression::Value(1)),
        Box::new(Expression::Add(
            Box::new(Expression::Value(2)),
            Box::new(Expression::Value(3)),
        ))
    );
    let result = sem.evaluate(expr);
    println!("Result: {}", result); // 6
}
```

#### 大步语义 (Big-Step Semantics)

一次性求值到最终结果:

```rust
impl BigStepSemantics {
    fn evaluate(&self, expr: Expression) -> i32 {
        match expr {
            Expression::Value(n) => n,
            Expression::Add(box e1, box e2) => {
                self.evaluate(e1) + self.evaluate(e2)
            }
            Expression::Mul(box e1, box e2) => {
                self.evaluate(e1) * self.evaluate(e2)
            }
        }
    }
}
```

### 指称语义

**指称语义**将程序映射到数学对象:

```rust
use c12_model::formal_models::denotational::*;

// 程序的数学语义
type State = HashMap<String, i32>;
type Denotation = Box<dyn Fn(&State) -> i32>;

struct DenotationalSemantics;

impl DenotationalSemantics {
    // 表达式语义
    fn expr_semantics(&self, expr: &Expression) -> Denotation {
        match expr {
            Expression::Var(name) => {
                let name = name.clone();
                Box::new(move |state: &State| *state.get(&name).unwrap_or(&0))
            }
            Expression::Add(e1, e2) => {
                let sem1 = self.expr_semantics(e1);
                let sem2 = self.expr_semantics(e2);
                Box::new(move |state: &State| sem1(state) + sem2(state))
            }
            _ => todo!(),
        }
    }
    
    // 语句语义
    fn stmt_semantics(&self, stmt: &Statement) -> Box<dyn Fn(&State) -> State> {
        match stmt {
            Statement::Assign(var, expr) => {
                let var = var.clone();
                let expr_sem = self.expr_semantics(expr);
                Box::new(move |state: &State| {
                    let mut new_state = state.clone();
                    new_state.insert(var.clone(), expr_sem(state));
                    new_state
                })
            }
            _ => todo!(),
        }
    }
}
```

### 时序逻辑

**时序逻辑**描述系统随时间的性质:

```rust
use c12_model::formal_models::temporal::*;

// LTL (线性时序逻辑) 公式
enum LTLFormula {
    Atom(String),              // 原子命题
    Not(Box<LTLFormula>),      // 非
    And(Box<LTLFormula>, Box<LTLFormula>),  // 与
    Next(Box<LTLFormula>),     // 下一个状态 (X)
    Eventually(Box<LTLFormula>), // 最终 (F)
    Always(Box<LTLFormula>),   // 总是 (G)
    Until(Box<LTLFormula>, Box<LTLFormula>), // 直到 (U)
}

// 模型检查器
struct LTLModelChecker {
    states: Vec<State>,
    transitions: Vec<(usize, usize)>,
}

impl LTLModelChecker {
    fn check(&self, formula: &LTLFormula, initial_state: usize) -> bool {
        match formula {
            LTLFormula::Atom(prop) => self.states[initial_state].satisfies(prop),
            LTLFormula::Always(f) => {
                // G φ: φ 在所有状态都成立
                self.all_paths_satisfy(initial_state, f)
            }
            LTLFormula::Eventually(f) => {
                // F φ: φ 最终在某个状态成立
                self.some_path_eventually_satisfies(initial_state, f)
            }
            _ => todo!(),
        }
    }
}

// 示例: 验证安全性质
fn main() {
    let checker = LTLModelChecker::new(/* ... */);
    
    // 验证: "系统总是在安全状态"
    let safety = LTLFormula::Always(Box::new(LTLFormula::Atom("safe".to_string())));
    assert!(checker.check(&safety, 0));
    
    // 验证: "请求最终会被响应"
    let liveness = LTLFormula::Always(Box::new(
        LTLFormula::Implies(
            Box::new(LTLFormula::Atom("request".to_string())),
            Box::new(LTLFormula::Eventually(Box::new(LTLFormula::Atom("response".to_string()))))
        )
    ));
    assert!(checker.check(&liveness, 0));
}
```

---

## 架构模型

### 分层架构

**分层架构**将系统分为多个层次:

```rust
use c12_model::architecture_design_models::*;

struct LayeredArchitecture {
    layers: Vec<Layer>,
}

struct Layer {
    name: String,
    level: usize,
    dependencies: Vec<String>, // 只能依赖下层
}

impl LayeredArchitecture {
    fn new() -> Self {
        let mut arch = LayeredArchitecture { layers: Vec::new() };
        
        // 定义4层架构
        arch.add_layer("Presentation", 4, vec![]);           // 表示层
        arch.add_layer("Application", 3, vec!["Presentation"]); // 应用层
        arch.add_layer("Domain", 2, vec!["Application"]);    // 领域层
        arch.add_layer("Infrastructure", 1, vec!["Domain"]); // 基础设施层
        
        arch
    }
    
    fn validate_dependency(&self, from: &str, to: &str) -> Result<()> {
        let from_level = self.get_level(from)?;
        let to_level = self.get_level(to)?;
        
        if from_level <= to_level {
            return Err(anyhow!("Violation: {} cannot depend on {}", from, to));
        }
        
        Ok(())
    }
}

// 示例
fn main() -> Result<()> {
    let arch = LayeredArchitecture::new();
    
    // 合法依赖
    arch.validate_dependency("Presentation", "Application")?; // ✅
    
    // 非法依赖 (违反分层原则)
    arch.validate_dependency("Infrastructure", "Presentation")?; // ❌ 错误!
    
    Ok(())
}
```

### 六边形架构 (端口与适配器)

**六边形架构**将核心逻辑与外部系统隔离:

```rust
use c12_model::architecture_design_models::hexagonal::*;

// 核心领域
trait UserRepository {
    fn find_by_id(&self, id: u64) -> Option<User>;
    fn save(&self, user: &User) -> Result<()>;
}

struct UserService {
    repo: Box<dyn UserRepository>, // 端口
}

impl UserService {
    fn get_user(&self, id: u64) -> Result<User> {
        self.repo.find_by_id(id)
            .ok_or_else(|| anyhow!("User not found"))
    }
}

// 适配器1: PostgreSQL
struct PostgresUserRepository {
    pool: PgPool,
}

impl UserRepository for PostgresUserRepository {
    fn find_by_id(&self, id: u64) -> Option<User> {
        // PostgreSQL 实现
        sqlx::query_as("SELECT * FROM users WHERE id = $1")
            .bind(id)
            .fetch_one(&self.pool)
            .await
            .ok()
    }
    
    fn save(&self, user: &User) -> Result<()> {
        sqlx::query("INSERT INTO users (...) VALUES (...)")
            .execute(&self.pool)
            .await?;
        Ok(())
    }
}

// 适配器2: In-Memory (用于测试)
struct InMemoryUserRepository {
    users: HashMap<u64, User>,
}

impl UserRepository for InMemoryUserRepository {
    fn find_by_id(&self, id: u64) -> Option<User> {
        self.users.get(&id).cloned()
    }
    
    fn save(&self, user: &User) -> Result<()> {
        self.users.insert(user.id, user.clone());
        Ok(())
    }
}

// 使用示例
fn main() {
    // 生产环境: 使用 PostgreSQL
    let repo = Box::new(PostgresUserRepository { pool });
    let service = UserService { repo };
    
    // 测试环境: 使用 In-Memory
    let repo = Box::new(InMemoryUserRepository::new());
    let service = UserService { repo };
}
```

### 微服务架构

**微服务架构**将系统拆分为独立的服务:

```rust
use c12_model::microservice_models::*;

struct Microservice {
    name: String,
    port: u16,
    endpoints: Vec<Endpoint>,
    dependencies: Vec<String>,
}

struct ServiceMesh {
    services: HashMap<String, Microservice>,
    registry: ServiceRegistry,
}

impl ServiceMesh {
    fn register(&mut self, service: Microservice) {
        self.registry.register(&service);
        self.services.insert(service.name.clone(), service);
    }
    
    fn discover(&self, service_name: &str) -> Option<&Microservice> {
        self.services.get(service_name)
    }
    
    async fn call(&self, from: &str, to: &str, request: Request) -> Response {
        // 服务间调用,带有:
        // - 负载均衡
        // - 熔断器
        // - 重试
        // - 分布式追踪
        
        let target = self.discover(to)?;
        self.load_balancer.route(target, request).await
    }
}

// 示例: API Gateway -> User Service -> Auth Service
fn main() {
    let mut mesh = ServiceMesh::new();
    
    mesh.register(Microservice {
        name: "api-gateway".to_string(),
        port: 8080,
        endpoints: vec![Endpoint::new("/api/*")],
        dependencies: vec!["user-service".to_string()],
    });
    
    mesh.register(Microservice {
        name: "user-service".to_string(),
        port: 8081,
        endpoints: vec![Endpoint::new("/users/*")],
        dependencies: vec!["auth-service".to_string()],
    });
    
    mesh.register(Microservice {
        name: "auth-service".to_string(),
        port: 8082,
        endpoints: vec![Endpoint::new("/auth/*")],
        dependencies: vec![],
    });
}
```

---

## 设计模式

### Builder 模式

**Builder 模式**用于构建复杂对象:

```rust
use c12_model::patterns::*;

struct HttpRequest {
    method: String,
    url: String,
    headers: HashMap<String, String>,
    body: Option<String>,
    timeout: Duration,
}

struct HttpRequestBuilder {
    method: String,
    url: String,
    headers: HashMap<String, String>,
    body: Option<String>,
    timeout: Duration,
}

impl HttpRequestBuilder {
    fn new(url: impl Into<String>) -> Self {
        Self {
            method: "GET".to_string(),
            url: url.into(),
            headers: HashMap::new(),
            body: None,
            timeout: Duration::from_secs(30),
        }
    }
    
    fn method(mut self, method: impl Into<String>) -> Self {
        self.method = method.into();
        self
    }
    
    fn header(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.headers.insert(key.into(), value.into());
        self
    }
    
    fn body(mut self, body: impl Into<String>) -> Self {
        self.body = Some(body.into());
        self
    }
    
    fn timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }
    
    fn build(self) -> HttpRequest {
        HttpRequest {
            method: self.method,
            url: self.url,
            headers: self.headers,
            body: self.body,
            timeout: self.timeout,
        }
    }
}

// 使用示例
fn main() {
    let request = HttpRequestBuilder::new("https://api.example.com")
        .method("POST")
        .header("Authorization", "Bearer token")
        .header("Content-Type", "application/json")
        .body(r#"{"key": "value"}"#)
        .timeout(Duration::from_secs(10))
        .build();
}
```

### Observer 模式

**Observer 模式**实现事件通知:

```rust
use c12_model::patterns::observer::*;

trait Observer {
    fn update(&self, event: &Event);
}

struct Subject {
    observers: Vec<Box<dyn Observer>>,
}

impl Subject {
    fn attach(&mut self, observer: Box<dyn Observer>) {
        self.observers.push(observer);
    }
    
    fn notify(&self, event: &Event) {
        for observer in &self.observers {
            observer.update(event);
        }
    }
}

// 具体观察者
struct Logger;

impl Observer for Logger {
    fn update(&self, event: &Event) {
        println!("Logger: {:?}", event);
    }
}

struct Metrics;

impl Observer for Metrics {
    fn update(&self, event: &Event) {
        // 记录指标
    }
}

// 使用示例
fn main() {
    let mut subject = Subject::new();
    subject.attach(Box::new(Logger));
    subject.attach(Box::new(Metrics));
    
    subject.notify(&Event::UserCreated { id: 1 });
}
```

### Strategy 模式

**Strategy 模式**封装算法:

```rust
use c12_model::patterns::strategy::*;

trait CompressionStrategy {
    fn compress(&self, data: &[u8]) -> Vec<u8>;
    fn decompress(&self, data: &[u8]) -> Vec<u8>;
}

struct GzipCompression;
impl CompressionStrategy for GzipCompression {
    fn compress(&self, data: &[u8]) -> Vec<u8> {
        // gzip 压缩
        todo!()
    }
    fn decompress(&self, data: &[u8]) -> Vec<u8> {
        todo!()
    }
}

struct ZstdCompression;
impl CompressionStrategy for ZstdCompression {
    fn compress(&self, data: &[u8]) -> Vec<u8> {
        // zstd 压缩
        todo!()
    }
    fn decompress(&self, data: &[u8]) -> Vec<u8> {
        todo!()
    }
}

struct Compressor {
    strategy: Box<dyn CompressionStrategy>,
}

impl Compressor {
    fn new(strategy: Box<dyn CompressionStrategy>) -> Self {
        Self { strategy }
    }
    
    fn set_strategy(&mut self, strategy: Box<dyn CompressionStrategy>) {
        self.strategy = strategy;
    }
    
    fn compress(&self, data: &[u8]) -> Vec<u8> {
        self.strategy.compress(data)
    }
}

// 使用示例
fn main() {
    let mut compressor = Compressor::new(Box::new(GzipCompression));
    let compressed = compressor.compress(b"data");
    
    // 切换策略
    compressor.set_strategy(Box::new(ZstdCompression));
    let compressed = compressor.compress(b"data");
}
```

---

## 并发模型

### Actor 模型

**Actor 模型**通过消息传递实现并发:

```rust
use c12_model::parallel_concurrent_models::actor::*;
use tokio::sync::mpsc;

struct Actor {
    id: String,
    mailbox: mpsc::Receiver<Message>,
}

impl Actor {
    async fn run(mut self) {
        while let Some(msg) = self.mailbox.recv().await {
            self.handle_message(msg).await;
        }
    }
    
    async fn handle_message(&self, msg: Message) {
        match msg {
            Message::Request(data) => {
                // 处理请求
                println!("Actor {}: Processing {}", self.id, data);
            }
            Message::Stop => {
                // 停止 actor
            }
        }
    }
}

// 使用示例
#[tokio::main]
async fn main() {
    let (tx, rx) = mpsc::channel(32);
    
    let actor = Actor {
        id: "worker-1".to_string(),
        mailbox: rx,
    };
    
    tokio::spawn(async move {
        actor.run().await;
    });
    
    // 发送消息
    tx.send(Message::Request("task1".to_string())).await.unwrap();
    tx.send(Message::Request("task2".to_string())).await.unwrap();
}
```

### CSP (Communicating Sequential Processes)

**CSP 模型**通过通道通信:

```rust
use c12_model::parallel_concurrent_models::csp::*;
use tokio::sync::mpsc;

// 生产者进程
async fn producer(tx: mpsc::Sender<i32>) {
    for i in 0..10 {
        tx.send(i).await.unwrap();
        println!("Produced: {}", i);
    }
}

// 消费者进程
async fn consumer(mut rx: mpsc::Receiver<i32>) {
    while let Some(value) = rx.recv().await {
        println!("Consumed: {}", value);
        // 处理数据
    }
}

// 使用示例
#[tokio::main]
async fn main() {
    let (tx, rx) = mpsc::channel(10);
    
    // 并发执行两个进程
    tokio::join!(
        producer(tx),
        consumer(rx),
    );
}
```

### Work-Stealing 调度

**Work-Stealing** 实现负载均衡:

```rust
use c12_model::parallel_concurrent_models::work_stealing::*;
use crossbeam_deque::{Injector, Stealer, Worker};

struct WorkStealingScheduler {
    global_queue: Arc<Injector<Task>>,
    workers: Vec<Worker<Task>>,
    stealers: Vec<Stealer<Task>>,
}

impl WorkStealingScheduler {
    fn new(num_workers: usize) -> Self {
        let global_queue = Arc::new(Injector::new());
        let mut workers = Vec::new();
        let mut stealers = Vec::new();
        
        for _ in 0..num_workers {
            let worker = Worker::new_fifo();
            stealers.push(worker.stealer());
            workers.push(worker);
        }
        
        Self { global_queue, workers, stealers }
    }
    
    fn submit(&self, task: Task) {
        self.global_queue.push(task);
    }
    
    fn worker_loop(&self, worker_id: usize) {
        let worker = &self.workers[worker_id];
        
        loop {
            // 1. 从本地队列获取任务
            if let Some(task) = worker.pop() {
                task.execute();
                continue;
            }
            
            // 2. 从全局队列获取任务
            if let Ok(task) = self.global_queue.steal() {
                task.execute();
                continue;
            }
            
            // 3. 从其他 worker 窃取任务
            for stealer in &self.stealers {
                if let Ok(task) = stealer.steal() {
                    task.execute();
                    continue;
                }
            }
            
            // 4. 没有任务，休眠
            std::thread::sleep(Duration::from_millis(1));
        }
    }
}
```

---

## 分布式模型

### Raft 共识算法

**Raft** 实现分布式共识:

```rust
use c12_model::distributed_models::raft::*;

struct RaftNode {
    id: String,
    state: NodeState,
    current_term: u64,
    voted_for: Option<String>,
    log: Vec<LogEntry>,
    commit_index: u64,
    last_applied: u64,
}

enum NodeState {
    Follower,
    Candidate,
    Leader,
}

impl RaftNode {
    fn start_election(&mut self) {
        self.state = NodeState::Candidate;
        self.current_term += 1;
        self.voted_for = Some(self.id.clone());
        
        // 发送 RequestVote RPC
        for peer in &self.peers {
            self.send_vote_request(peer);
        }
    }
    
    fn append_entries(&mut self, entry: LogEntry) -> Result<()> {
        if !matches!(self.state, NodeState::Leader) {
            return Err(anyhow!("Not leader"));
        }
        
        self.log.push(entry);
        
        // 复制到其他节点
        for peer in &self.peers {
            self.send_append_entries(peer);
        }
        
        Ok(())
    }
    
    fn commit(&mut self, index: u64) {
        if self.commit_index >= index {
            return;
        }
        
        self.commit_index = index;
        
        // 应用已提交的日志
        while self.last_applied < self.commit_index {
            self.last_applied += 1;
            let entry = &self.log[self.last_applied as usize];
            self.apply(entry);
        }
    }
}

// 使用示例
fn main() {
    let mut node = RaftNode::new("node1".to_string());
    
    // 启动选举
    node.start_election();
    
    // 追加日志
    node.append_entries(LogEntry {
        term: 1,
        command: "SET x = 10".to_string(),
    })?;
    
    // 提交
    node.commit(1);
}
```

### Paxos 协议

**Paxos** 实现分布式共识:

```rust
use c12_model::distributed_models::paxos::*;

struct PaxosNode {
    id: String,
    promised_proposal: Option<u64>,
    accepted_proposal: Option<(u64, String)>,
}

impl PaxosNode {
    // Phase 1a: Proposer 发送 Prepare
    fn prepare(&self, proposal_num: u64) -> PrepareRequest {
        PrepareRequest { proposal_num }
    }
    
    // Phase 1b: Acceptor 响应 Promise
    fn handle_prepare(&mut self, req: PrepareRequest) -> Option<PromiseResponse> {
        if Some(req.proposal_num) > self.promised_proposal {
            self.promised_proposal = Some(req.proposal_num);
            Some(PromiseResponse {
                proposal_num: req.proposal_num,
                accepted_value: self.accepted_proposal.clone(),
            })
        } else {
            None
        }
    }
    
    // Phase 2a: Proposer 发送 Accept
    fn accept(&self, proposal_num: u64, value: String) -> AcceptRequest {
        AcceptRequest { proposal_num, value }
    }
    
    // Phase 2b: Acceptor 响应 Accepted
    fn handle_accept(&mut self, req: AcceptRequest) -> Option<AcceptedResponse> {
        if Some(req.proposal_num) >= self.promised_proposal {
            self.promised_proposal = Some(req.proposal_num);
            self.accepted_proposal = Some((req.proposal_num, req.value.clone()));
            Some(AcceptedResponse {
                proposal_num: req.proposal_num,
            })
        } else {
            None
        }
    }
}
```

### 分布式快照 (Chandy-Lamport)

**分布式快照**捕获全局状态:

```rust
use c12_model::distributed_models::snapshot::*;

struct DistributedSnapshot {
    snapshot_id: String,
    initiator: String,
    local_states: HashMap<String, State>,
    channel_states: HashMap<(String, String), Vec<Message>>,
}

impl DistributedSnapshot {
    fn initiate(&mut self, node_id: String) {
        // 1. 记录本地状态
        self.local_states.insert(node_id.clone(), self.get_local_state(&node_id));
        
        // 2. 发送 marker 到所有出边
        for neighbor in self.get_neighbors(&node_id) {
            self.send_marker(&node_id, &neighbor);
        }
    }
    
    fn receive_marker(&mut self, from: String, to: String) {
        if !self.local_states.contains_key(&to) {
            // 第一次收到 marker
            // 1. 记录本地状态
            self.local_states.insert(to.clone(), self.get_local_state(&to));
            
            // 2. 标记该通道为空
            self.channel_states.insert((from.clone(), to.clone()), vec![]);
            
            // 3. 发送 marker 到其他出边
            for neighbor in self.get_neighbors(&to) {
                if neighbor != from {
                    self.send_marker(&to, &neighbor);
                }
            }
        } else {
            // 已经记录过本地状态
            // 停止记录该通道的消息
            self.stop_recording(&from, &to);
        }
    }
    
    fn get_global_snapshot(&self) -> GlobalSnapshot {
        GlobalSnapshot {
            local_states: self.local_states.clone(),
            channel_states: self.channel_states.clone(),
        }
    }
}
```

---

## 最佳实践

### 形式化验证

```rust
// 使用 Loom 进行并发测试
#[cfg(test)]
mod tests {
    use loom::sync::Arc;
    use loom::thread;

    #[test]
    fn test_concurrent_counter() {
        loom::model(|| {
            let counter = Arc::new(AtomicU32::new(0));
            
            let handles: Vec<_> = (0..2).map(|_| {
                let counter = Arc::clone(&counter);
                thread::spawn(move || {
                    counter.fetch_add(1, Ordering::SeqCst);
                })
            }).collect();
            
            for handle in handles {
                handle.join().unwrap();
            }
            
            assert_eq!(counter.load(Ordering::SeqCst), 2);
        });
    }
}
```

### 架构验证

```rust
// 使用类型系统保证架构约束
mod presentation {
    // 表示层只能依赖 application 层
    use super::application;
    
    pub struct Controller {
        service: application::UserService,
    }
}

mod application {
    // 应用层只能依赖 domain 层
    use super::domain;
    
    pub struct UserService {
        repo: Box<dyn domain::UserRepository>,
    }
}

mod domain {
    // 领域层不依赖任何层
    pub trait UserRepository {
        fn find(&self, id: u64) -> Option<User>;
    }
}

mod infrastructure {
    // 基础设施层实现 domain 接口
    use super::domain;
    
    pub struct PostgresUserRepository;
    impl domain::UserRepository for PostgresUserRepository {
        fn find(&self, id: u64) -> Option<User> {
            // 实现
        }
    }
}
```

### 分布式系统测试

```rust
// 使用 Chaos Engineering 测试
#[cfg(test)]
mod chaos_tests {
    use chaos::*;

    #[test]
    fn test_raft_with_network_partition() {
        let cluster = RaftCluster::new(5);
        
        // 网络分区: 隔离 leader
        chaos::network_partition(&cluster, vec![0], vec![1, 2, 3, 4]);
        
        // 验证: 剩余节点能选出新 leader
        assert!(cluster.wait_for_leader(Duration::from_secs(5)));
        
        // 恢复网络
        chaos::heal_network(&cluster);
        
        // 验证: 原 leader 同步到最新状态
        assert!(cluster.wait_for_convergence(Duration::from_secs(10)));
    }
}
```

---

## 完整文档

### 📚 详细文档

model crate 包含 **100+ 篇** 详细文档，覆盖:

- **形式化模型理论** (操作语义、指称语义、时序逻辑)
- **架构模式详解** (分层、六边形、微服务、事件驱动)
- **设计模式实现** (23+ 种经典模式)
- **并发模型分析** (Actor、CSP、STM、Fork-Join)
- **分布式算法** (Raft、Paxos、2PC/3PC、分布式快照)

访问: [crates/model/docs/](../../crates/model/docs/)

### 📖 主要文档索引

| 文档 | 说明 | 规模 |
|------|------|------|
| [完整索引](../../crates/model/docs/00_MASTER_INDEX.md) | 文档导航 | 完整 |
| [形式化建模实践](../../crates/model/docs/tier_02_guides/01_形式化建模实践.md) | 实践指南 | 详细 |
| [分布式系统建模](../../crates/model/docs/tier_02_guides/02_分布式系统建模.md) | 分布式模型 | 详细 |
| [并发模型实践](../../crates/model/docs/tier_02_guides/03_并发模型实践.md) | 并发编程 | 详细 |
| [软件设计模型](../../crates/model/docs/architecture/software-design-models-comprehensive.md) | 架构模式 | 完整 |
| [分布式设计](../../crates/model/docs/architecture/distributed-design.md) | 分布式架构 | 完整 |
| [知识图谱](../../crates/model/docs/theory_enhanced/KNOWLEDGE_GRAPH_AND_CONCEPT_RELATIONS.md) | 概念关系 | 详细 |
| [多维矩阵对比](../../crates/model/docs/theory_enhanced/MULTI_DIMENSIONAL_COMPARISON_MATRIX.md) | 模型对比 | 详细 |

### 🎯 示例代码

20个完整示例位于 `crates/model/examples/`:

```bash
# 运行示例
cd crates/model

# 形式化方法示例
cargo run --example formal_methods_examples

# 并发模型示例
cargo run --example concurrency_actor
cargo run --example concurrency_csp
cargo run --example concurrency_structured

# 分布式系统示例
cargo run --example comprehensive_model_showcase

# 机器学习示例
cargo run --example machine_learning_examples
cargo run --example rust_190_modern_ml_demo

# 系统建模示例
cargo run --example system_modeling_examples

# 更多示例
cargo run --example async_backpressure_demo
cargo run --example async_recursion_examples
cargo run --example tower_reliability
```

---

## 🔗 相关资源

### 项目文档

- [返回 Crates 总览](README.md)
- [libraries 使用指南](libraries_guide.md)
- [reliability 使用指南](reliability_guide.md)
- [otlp 使用指南](otlp_guide.md)

### 架构文档

- [架构重组计划](../CRATES_ARCHITECTURE_REORG_2025_10_26.md)
- [知识图谱](../CRATES_KNOWLEDGE_GRAPH_2025_10_26.md)
- [矩阵对比](../CRATES_MATRIX_COMPARISON_2025_10_26.md)

### 主文档

- [项目主文档](../README.md)
- [文档导航](../DOCUMENTATION_GUIDE.md)
- [快速开始](../01_GETTING_STARTED/README.md)

---

## 🤝 贡献

欢迎贡献！

1. **添加新模型**: 补充更多设计模型和架构模式
2. **改进文档**: 完善理论说明和实践指导
3. **提供示例**: 分享实际项目中的模型应用
4. **报告问题**: 反馈模型实现中的问题

详见: [贡献指南](../guides/CONTRIBUTING.md)

---

**最后更新**: 2025年10月26日  
**文档版本**: v1.0.0  
**维护状态**: 🔄 持续维护中
