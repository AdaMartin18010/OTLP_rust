# 分布式系统可靠性完整指南

**Crate:** c13_reliability
**主题:** Distributed System Reliability
**Rust 版本:** 1.90.0
**最后更新:** 2025年10月28日

---

## 📋 目录

- [分布式系统可靠性完整指南](#分布式系统可靠性完整指南)
  - [📋 目录](#-目录)
  - [📍 分布式系统概述](#-分布式系统概述)
    - [分布式系统的挑战](#分布式系统的挑战)
    - [可靠性保证](#可靠性保证)
  - [🤝 共识算法](#-共识算法)
    - [1. Raft 共识算法](#1-raft-共识算法)
      - [概念](#概念)
      - [核心组件](#核心组件)
    - [2. Paxos 共识算法](#2-paxos-共识算法)
      - [基本 Paxos](#基本-paxos)
  - [⏱️ 最终一致性](#️-最终一致性)
    - [1. CRDT (Conflict-free Replicated Data Types)](#1-crdt-conflict-free-replicated-data-types)
      - [G-Counter (增长型计数器)](#g-counter-增长型计数器)
      - [PN-Counter (正负计数器)](#pn-counter-正负计数器)
    - [2. 向量时钟 (Vector Clock)](#2-向量时钟-vector-clock)
      - [实现](#实现)
  - [💳 分布式事务](#-分布式事务)
    - [1. 两阶段提交 (2PC)](#1-两阶段提交-2pc)
      - [实现1](#实现1)
    - [2. Saga 模式](#2-saga-模式)
      - [实现3](#实现3)
  - [🔒 分布式锁](#-分布式锁)
    - [1. Redis 分布式锁](#1-redis-分布式锁)
      - [实现2](#实现2)
  - [🔍 故障检测和恢复](#-故障检测和恢复)
    - [1. 心跳机制](#1-心跳机制)
      - [实现4](#实现4)
    - [2. 故障恢复策略](#2-故障恢复策略)
      - [实现5](#实现5)
  - [🔄 数据复制](#-数据复制)
    - [1. 主从复制](#1-主从复制)
      - [实现6](#实现6)
    - [2. 多主复制](#2-多主复制)
      - [实现7](#实现7)
  - [⚖️ CAP 理论实践](#️-cap-理论实践)
    - [CAP 三角](#cap-三角)
    - [1. CP 系统 (一致性 + 分区容错)](#1-cp-系统-一致性--分区容错)
    - [2. AP 系统 (可用性 + 分区容错)](#2-ap-系统-可用性--分区容错)
  - [总结](#总结)
    - [分布式系统可靠性清单](#分布式系统可靠性清单)
    - [最佳实践](#最佳实践)

---

## 📍 分布式系统概述

### 分布式系统的挑战

```text
┌────────────────────────────────────────┐
│       分布式系统的八大谬误               │
├────────────────────────────────────────┤
│ 1. 网络是可靠的                         │
│ 2. 延迟为零                             │
│ 3. 带宽是无限的                         │
│ 4. 网络是安全的                         │
│ 5. 拓扑不会改变                         │
│ 6. 只有一个管理员                       │
│ 7. 传输成本为零                         │
│ 8. 网络是同构的                         │
└────────────────────────────────────────┘
```

### 可靠性保证

```rust
use serde::{Serialize, Deserialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ConsistencyLevel {
    /// 强一致性
    Strong,
    /// 最终一致性
    Eventual,
    /// 因果一致性
    Causal,
    /// 会话一致性
    Session,
}

#[derive(Debug, Clone)]
pub struct ReliabilityGuarantees {
    /// 一致性级别
    pub consistency: ConsistencyLevel,
    /// 是否保证 at-least-once
    pub at_least_once: bool,
    /// 是否保证 at-most-once
    pub at_most_once: bool,
    /// 是否保证 exactly-once
    pub exactly_once: bool,
    /// 超时时间
    pub timeout: Duration,
}
```

---

## 🤝 共识算法

### 1. Raft 共识算法

#### 概念

Raft 是一个易于理解的共识算法，用于在分布式系统中达成一致。

#### 核心组件

```rust
use tokio::sync::{RwLock, mpsc};
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum NodeState {
    Follower,
    Candidate,
    Leader,
}

pub struct RaftNode {
    /// 节点 ID
    id: u64,
    /// 当前状态
    state: RwLock<NodeState>,
    /// 当前任期
    current_term: RwLock<u64>,
    /// 投票给谁
    voted_for: RwLock<Option<u64>>,
    /// 日志条目
    log: RwLock<Vec<LogEntry>>,
    /// 已提交的索引
    commit_index: RwLock<u64>,
    /// 已应用的索引
    last_applied: RwLock<u64>,
    /// 集群节点
    peers: Vec<u64>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogEntry {
    pub term: u64,
    pub index: u64,
    pub command: Vec<u8>,
}

impl RaftNode {
    /// 启动选举
    async fn start_election(&self) -> Result<bool> {
        let mut current_term = self.current_term.write().await;
        *current_term += 1;

        *self.state.write().await = NodeState::Candidate;
        *self.voted_for.write().await = Some(self.id);

        // 向所有节点发送投票请求
        let votes = self.request_votes(*current_term).await?;

        // 需要过半数投票
        let majority = self.peers.len() / 2 + 1;
        Ok(votes >= majority)
    }

    /// 请求投票
    async fn request_votes(&self, term: u64) -> Result<usize> {
        let last_log_index = self.log.read().await.len() as u64;
        let last_log_term = self.log.read().await
            .last()
            .map(|e| e.term)
            .unwrap_or(0);

        let mut votes = 1;  // 自己投给自己

        for peer_id in &self.peers {
            if *peer_id == self.id {
                continue;
            }

            let request = RequestVoteRequest {
                term,
                candidate_id: self.id,
                last_log_index,
                last_log_term,
            };

            if self.send_vote_request(*peer_id, request).await? {
                votes += 1;
            }
        }

        Ok(votes)
    }

    /// 追加日志条目
    pub async fn append_entry(&self, command: Vec<u8>) -> Result<()> {
        // 只有 Leader 可以追加日志
        let state = self.state.read().await;
        if *state != NodeState::Leader {
            return Err(anyhow::anyhow!("Not a leader"));
        }

        let term = *self.current_term.read().await;
        let mut log = self.log.write().await;

        let entry = LogEntry {
            term,
            index: log.len() as u64 + 1,
            command,
        };

        log.push(entry.clone());

        // 复制到其他节点
        self.replicate_log(entry).await?;

        Ok(())
    }

    /// 复制日志到其他节点
    async fn replicate_log(&self, entry: LogEntry) -> Result<()> {
        let mut success_count = 1;  // 自己算一个

        for peer_id in &self.peers {
            if *peer_id == self.id {
                continue;
            }

            if self.send_append_entries(*peer_id, vec![entry.clone()]).await? {
                success_count += 1;
            }
        }

        // 过半数成功才提交
        let majority = self.peers.len() / 2 + 1;
        if success_count >= majority {
            let mut commit_index = self.commit_index.write().await;
            *commit_index = entry.index;
        }

        Ok(())
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct RequestVoteRequest {
    pub term: u64,
    pub candidate_id: u64,
    pub last_log_index: u64,
    pub last_log_term: u64,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct AppendEntriesRequest {
    pub term: u64,
    pub leader_id: u64,
    pub prev_log_index: u64,
    pub prev_log_term: u64,
    pub entries: Vec<LogEntry>,
    pub leader_commit: u64,
}
```

---

### 2. Paxos 共识算法

#### 基本 Paxos

```rust
pub struct PaxosNode {
    id: u64,
    /// Proposer 编号
    proposal_number: RwLock<u64>,
    /// 已承诺的最大编号
    promised: RwLock<u64>,
    /// 已接受的提案
    accepted: RwLock<Option<Proposal>>,
}

#[derive(Debug, Clone)]
pub struct Proposal {
    pub number: u64,
    pub value: Vec<u8>,
}

impl PaxosNode {
    /// Phase 1a: Prepare
    pub async fn prepare(&self) -> Result<Proposal> {
        let mut proposal_number = self.proposal_number.write().await;
        *proposal_number += 1;

        // 向所有 Acceptor 发送 Prepare 请求
        let promises = self.send_prepare_requests(*proposal_number).await?;

        // 选择已接受提案中编号最大的值
        let value = promises
            .into_iter()
            .filter_map(|p| p.accepted)
            .max_by_key(|p| p.number)
            .map(|p| p.value)
            .unwrap_or_else(|| self.generate_value());

        Ok(Proposal {
            number: *proposal_number,
            value,
        })
    }

    /// Phase 2a: Accept
    pub async fn accept(&self, proposal: Proposal) -> Result<bool> {
        // 向所有 Acceptor 发送 Accept 请求
        let accepts = self.send_accept_requests(proposal).await?;

        // 过半数接受才算成功
        let majority = self.get_quorum_size();
        Ok(accepts >= majority)
    }

    /// Phase 1b: Promise
    pub async fn handle_prepare(&self, n: u64) -> Result<PrepareResponse> {
        let mut promised = self.promised.write().await;

        if n > *promised {
            *promised = n;
            let accepted = self.accepted.read().await.clone();

            Ok(PrepareResponse {
                promised: true,
                accepted,
            })
        } else {
            Ok(PrepareResponse {
                promised: false,
                accepted: None,
            })
        }
    }

    /// Phase 2b: Accepted
    pub async fn handle_accept(&self, proposal: Proposal) -> Result<bool> {
        let promised = *self.promised.read().await;

        if proposal.number >= promised {
            *self.accepted.write().await = Some(proposal);
            Ok(true)
        } else {
            Ok(false)
        }
    }
}

#[derive(Debug)]
pub struct PrepareResponse {
    pub promised: bool,
    pub accepted: Option<Proposal>,
}
```

---

## ⏱️ 最终一致性

### 1. CRDT (Conflict-free Replicated Data Types)

#### G-Counter (增长型计数器)

```rust
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct GCounter {
    node_id: String,
    counters: HashMap<String, u64>,
}

impl GCounter {
    pub fn new(node_id: String) -> Self {
        let mut counters = HashMap::new();
        counters.insert(node_id.clone(), 0);

        Self { node_id, counters }
    }

    /// 增加计数
    pub fn increment(&mut self) {
        *self.counters.entry(self.node_id.clone()).or_insert(0) += 1;
    }

    /// 获取总计数
    pub fn value(&self) -> u64 {
        self.counters.values().sum()
    }

    /// 合并其他节点的状态
    pub fn merge(&mut self, other: &GCounter) {
        for (node_id, count) in &other.counters {
            let entry = self.counters.entry(node_id.clone()).or_insert(0);
            *entry = (*entry).max(*count);
        }
    }
}

// 使用示例
async fn crdt_counter_example() {
    let mut counter1 = GCounter::new("node1".to_string());
    let mut counter2 = GCounter::new("node2".to_string());

    // Node 1 增加
    counter1.increment();
    counter1.increment();

    // Node 2 增加
    counter2.increment();

    // 合并
    counter1.merge(&counter2);
    counter2.merge(&counter1);

    // 两个节点的值相同
    assert_eq!(counter1.value(), 3);
    assert_eq!(counter2.value(), 3);
}
```

---

#### PN-Counter (正负计数器)

```rust
#[derive(Debug, Clone)]
pub struct PNCounter {
    node_id: String,
    positive: HashMap<String, u64>,
    negative: HashMap<String, u64>,
}

impl PNCounter {
    pub fn new(node_id: String) -> Self {
        Self {
            node_id,
            positive: HashMap::new(),
            negative: HashMap::new(),
        }
    }

    pub fn increment(&mut self) {
        *self.positive.entry(self.node_id.clone()).or_insert(0) += 1;
    }

    pub fn decrement(&mut self) {
        *self.negative.entry(self.node_id.clone()).or_insert(0) += 1;
    }

    pub fn value(&self) -> i64 {
        let pos: u64 = self.positive.values().sum();
        let neg: u64 = self.negative.values().sum();
        pos as i64 - neg as i64
    }

    pub fn merge(&mut self, other: &PNCounter) {
        for (node_id, count) in &other.positive {
            let entry = self.positive.entry(node_id.clone()).or_insert(0);
            *entry = (*entry).max(*count);
        }

        for (node_id, count) in &other.negative {
            let entry = self.negative.entry(node_id.clone()).or_insert(0);
            *entry = (*entry).max(*count);
        }
    }
}
```

---

### 2. 向量时钟 (Vector Clock)

#### 实现

```rust
use std::cmp::Ordering;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VectorClock {
    clock: HashMap<String, u64>,
}

impl VectorClock {
    pub fn new() -> Self {
        Self {
            clock: HashMap::new(),
        }
    }

    /// 递增本地时钟
    pub fn increment(&mut self, node_id: &str) {
        *self.clock.entry(node_id.to_string()).or_insert(0) += 1;
    }

    /// 合并两个向量时钟
    pub fn merge(&mut self, other: &VectorClock) {
        for (node_id, timestamp) in &other.clock {
            let entry = self.clock.entry(node_id.clone()).or_insert(0);
            *entry = (*entry).max(*timestamp);
        }
    }

    /// 比较两个向量时钟
    pub fn partial_cmp(&self, other: &VectorClock) -> Option<Ordering> {
        let mut less = false;
        let mut greater = false;

        let all_nodes: HashSet<_> = self.clock.keys()
            .chain(other.clock.keys())
            .collect();

        for node_id in all_nodes {
            let self_ts = self.clock.get(node_id).copied().unwrap_or(0);
            let other_ts = other.clock.get(node_id).copied().unwrap_or(0);

            match self_ts.cmp(&other_ts) {
                Ordering::Less => less = true,
                Ordering::Greater => greater = true,
                Ordering::Equal => {}
            }
        }

        match (less, greater) {
            (true, false) => Some(Ordering::Less),      // self < other
            (false, true) => Some(Ordering::Greater),   // self > other
            (false, false) => Some(Ordering::Equal),    // self == other
            (true, true) => None,                        // 并发
        }
    }

    /// 判断是否并发
    pub fn concurrent_with(&self, other: &VectorClock) -> bool {
        self.partial_cmp(other).is_none()
    }
}

// 使用示例
async fn vector_clock_example() {
    let mut clock_a = VectorClock::new();
    let mut clock_b = VectorClock::new();

    // Node A 的操作
    clock_a.increment("A");
    clock_a.increment("A");

    // Node B 的操作
    clock_b.increment("B");

    // 检查并发性
    assert!(clock_a.concurrent_with(&clock_b));

    // B 同步 A 的状态
    clock_b.merge(&clock_a);
    clock_b.increment("B");

    // 现在 B 的时钟比 A 更新
    assert_eq!(clock_b.partial_cmp(&clock_a), Some(Ordering::Greater));
}
```

---

## 💳 分布式事务

### 1. 两阶段提交 (2PC)

#### 实现1

```rust
pub struct TwoPhaseCommitCoordinator {
    transaction_id: String,
    participants: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Vote {
    Commit,
    Abort,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Decision {
    Commit,
    Abort,
}

impl TwoPhaseCommitCoordinator {
    /// Phase 1: Prepare
    pub async fn prepare(&self) -> Result<Decision> {
        let mut votes = Vec::new();

        for participant in &self.participants {
            match self.send_prepare(participant).await {
                Ok(vote) => votes.push(vote),
                Err(_) => {
                    // 参与者失败，投票 Abort
                    votes.push(Vote::Abort);
                }
            }
        }

        // 所有参与者都投票 Commit 才能提交
        if votes.iter().all(|v| matches!(v, Vote::Commit)) {
            Ok(Decision::Commit)
        } else {
            Ok(Decision::Abort)
        }
    }

    /// Phase 2: Commit/Abort
    pub async fn finalize(&self, decision: Decision) -> Result<()> {
        for participant in &self.participants {
            self.send_decision(participant, decision.clone()).await?;
        }

        Ok(())
    }

    /// 完整的 2PC 流程
    pub async fn execute(&self) -> Result<()> {
        // Phase 1
        let decision = self.prepare().await?;

        // Phase 2
        self.finalize(decision).await?;

        Ok(())
    }

    async fn send_prepare(&self, participant: &str) -> Result<Vote> {
        // 发送 Prepare 请求
        todo!()
    }

    async fn send_decision(&self, participant: &str, decision: Decision) -> Result<()> {
        // 发送 Commit/Abort 决定
        todo!()
    }
}

// 参与者
pub struct TwoPhaseCommitParticipant {
    transaction_log: RwLock<HashMap<String, TransactionState>>,
}

#[derive(Debug, Clone)]
pub struct TransactionState {
    pub status: TransactionStatus,
    pub data: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TransactionStatus {
    Prepared,
    Committed,
    Aborted,
}

impl TwoPhaseCommitParticipant {
    pub async fn handle_prepare(&self, tx_id: &str) -> Result<Vote> {
        // 尝试准备事务
        match self.try_prepare(tx_id).await {
            Ok(_) => {
                // 记录状态
                let mut log = self.transaction_log.write().await;
                log.insert(tx_id.to_string(), TransactionState {
                    status: TransactionStatus::Prepared,
                    data: Vec::new(),
                });

                Ok(Vote::Commit)
            }
            Err(_) => Ok(Vote::Abort),
        }
    }

    pub async fn handle_commit(&self, tx_id: &str) -> Result<()> {
        // 提交事务
        self.commit_transaction(tx_id).await?;

        let mut log = self.transaction_log.write().await;
        if let Some(state) = log.get_mut(tx_id) {
            state.status = TransactionStatus::Committed;
        }

        Ok(())
    }

    pub async fn handle_abort(&self, tx_id: &str) -> Result<()> {
        // 回滚事务
        self.rollback_transaction(tx_id).await?;

        let mut log = self.transaction_log.write().await;
        if let Some(state) = log.get_mut(tx_id) {
            state.status = TransactionStatus::Aborted;
        }

        Ok(())
    }
}
```

---

### 2. Saga 模式

#### 实现3

```rust
use async_trait::async_trait;

#[async_trait]
pub trait SagaStep: Send + Sync {
    /// 执行步骤
    async fn execute(&self) -> Result<()>;

    /// 补偿操作（回滚）
    async fn compensate(&self) -> Result<()>;
}

pub struct Saga {
    steps: Vec<Box<dyn SagaStep>>,
}

impl Saga {
    pub fn new() -> Self {
        Self { steps: Vec::new() }
    }

    pub fn add_step(mut self, step: Box<dyn SagaStep>) -> Self {
        self.steps.push(step);
        self
    }

    /// 执行 Saga
    pub async fn execute(&self) -> Result<()> {
        let mut executed_steps = Vec::new();

        for (i, step) in self.steps.iter().enumerate() {
            match step.execute().await {
                Ok(_) => {
                    executed_steps.push(i);
                }
                Err(e) => {
                    // 执行失败，回滚已执行的步骤
                    eprintln!("Step {} failed: {}, starting compensation", i, e);
                    self.compensate(&executed_steps).await?;
                    return Err(e);
                }
            }
        }

        Ok(())
    }

    /// 补偿（回滚）已执行的步骤
    async fn compensate(&self, executed_steps: &[usize]) -> Result<()> {
        // 反向补偿
        for &index in executed_steps.iter().rev() {
            if let Err(e) = self.steps[index].compensate().await {
                eprintln!("Compensation failed for step {}: {}", index, e);
                // 补偿失败是严重错误，需要人工介入
            }
        }

        Ok(())
    }
}

// 使用示例：转账 Saga
pub struct DebitAccountStep {
    account_id: String,
    amount: f64,
}

#[async_trait]
impl SagaStep for DebitAccountStep {
    async fn execute(&self) -> Result<()> {
        println!("Debiting {} from account {}", self.amount, self.account_id);
        // 扣款操作
        Ok(())
    }

    async fn compensate(&self) -> Result<()> {
        println!("Crediting back {} to account {}", self.amount, self.account_id);
        // 补偿：退款
        Ok(())
    }
}

pub struct CreditAccountStep {
    account_id: String,
    amount: f64,
}

#[async_trait]
impl SagaStep for CreditAccountStep {
    async fn execute(&self) -> Result<()> {
        println!("Crediting {} to account {}", self.amount, self.account_id);
        // 入账操作
        Ok(())
    }

    async fn compensate(&self) -> Result<()> {
        println!("Debiting {} from account {}", self.amount, self.account_id);
        // 补偿：扣款
        Ok(())
    }
}

async fn transfer_money_saga(from: String, to: String, amount: f64) -> Result<()> {
    let saga = Saga::new()
        .add_step(Box::new(DebitAccountStep {
            account_id: from.clone(),
            amount,
        }))
        .add_step(Box::new(CreditAccountStep {
            account_id: to.clone(),
            amount,
        }));

    saga.execute().await
}
```

---

## 🔒 分布式锁

### 1. Redis 分布式锁

#### 实现2

```rust
use redis::AsyncCommands;

pub struct RedisDistributedLock {
    redis: redis::aio::Connection,
    key: String,
    value: String,
    ttl_seconds: usize,
}

impl RedisDistributedLock {
    pub async fn acquire(&mut self) -> Result<bool> {
        // 使用 SET NX EX 原子操作
        let result: bool = redis::cmd("SET")
            .arg(&self.key)
            .arg(&self.value)
            .arg("NX")  // 只在键不存在时设置
            .arg("EX")  // 设置过期时间
            .arg(self.ttl_seconds)
            .query_async(&mut self.redis)
            .await?;

        Ok(result)
    }

    pub async fn release(&mut self) -> Result<()> {
        // 使用 Lua 脚本确保原子性
        let script = r#"
            if redis.call("get", KEYS[1]) == ARGV[1] then
                return redis.call("del", KEYS[1])
            else
                return 0
            end
        "#;

        redis::cmd("EVAL")
            .arg(script)
            .arg(1)
            .arg(&self.key)
            .arg(&self.value)
            .query_async(&mut self.redis)
            .await?;

        Ok(())
    }

    pub async fn renew(&mut self) -> Result<bool> {
        // 续期锁
        let script = r#"
            if redis.call("get", KEYS[1]) == ARGV[1] then
                return redis.call("expire", KEYS[1], ARGV[2])
            else
                return 0
            end
        "#;

        let result: i32 = redis::cmd("EVAL")
            .arg(script)
            .arg(1)
            .arg(&self.key)
            .arg(&self.value)
            .arg(self.ttl_seconds)
            .query_async(&mut self.redis)
            .await?;

        Ok(result == 1)
    }
}

// 自动续期的锁守卫
pub struct LockGuard {
    lock: RedisDistributedLock,
    renew_handle: Option<tokio::task::JoinHandle<()>>,
}

impl LockGuard {
    pub async fn new(mut lock: RedisDistributedLock) -> Result<Self> {
        if !lock.acquire().await? {
            return Err(anyhow::anyhow!("Failed to acquire lock"));
        }

        // 启动自动续期任务
        let renew_interval = Duration::from_secs((lock.ttl_seconds / 2) as u64);
        let mut lock_clone = lock.clone();

        let handle = tokio::spawn(async move {
            let mut interval = tokio::time::interval(renew_interval);

            loop {
                interval.tick().await;

                match lock_clone.renew().await {
                    Ok(true) => {}
                    Ok(false) => {
                        eprintln!("Lock renewal failed");
                        break;
                    }
                    Err(e) => {
                        eprintln!("Lock renewal error: {}", e);
                        break;
                    }
                }
            }
        });

        Ok(Self {
            lock,
            renew_handle: Some(handle),
        })
    }
}

impl Drop for LockGuard {
    fn drop(&mut self) {
        // 停止续期任务
        if let Some(handle) = self.renew_handle.take() {
            handle.abort();
        }

        // 释放锁（异步操作在 Drop 中需要特殊处理）
        let mut lock = self.lock.clone();
        tokio::spawn(async move {
            lock.release().await.ok();
        });
    }
}

// 使用示例
async fn use_distributed_lock() -> Result<()> {
    let redis_client = redis::Client::open("redis://127.0.0.1/")?;
    let connection = redis_client.get_async_connection().await?;

    let lock = RedisDistributedLock {
        redis: connection,
        key: "my_resource_lock".to_string(),
        value: uuid::Uuid::new_v4().to_string(),
        ttl_seconds: 30,
    };

    let guard = LockGuard::new(lock).await?;

    // 在锁保护下执行操作
    critical_section().await?;

    // guard 离开作用域时自动释放锁
    Ok(())
}
```

---

## 🔍 故障检测和恢复

### 1. 心跳机制

#### 实现4

```rust
use tokio::time::{interval, Duration};

pub struct HeartbeatMonitor {
    node_id: String,
    peers: Vec<String>,
    last_heartbeat: Arc<RwLock<HashMap<String, Instant>>>,
    timeout: Duration,
}

impl HeartbeatMonitor {
    pub async fn start_monitoring(&self) {
        let mut interval = interval(Duration::from_secs(1));

        loop {
            interval.tick().await;

            // 检查每个节点的心跳
            let now = Instant::now();
            let last_hb = self.last_heartbeat.read().await;

            for peer in &self.peers {
                if let Some(&last_time) = last_hb.get(peer) {
                    if now.duration_since(last_time) > self.timeout {
                        // 节点超时，标记为失败
                        self.handle_node_failure(peer).await;
                    }
                }
            }
        }
    }

    pub async fn record_heartbeat(&self, node_id: &str) {
        let mut last_hb = self.last_heartbeat.write().await;
        last_hb.insert(node_id.to_string(), Instant::now());
    }

    async fn handle_node_failure(&self, node_id: &str) {
        println!("Node {} failed!", node_id);

        // 触发故障恢复流程
        self.initiate_failover(node_id).await;
    }

    async fn initiate_failover(&self, failed_node: &str) {
        // 1. 从集群中移除失败节点
        // 2. 重新分配失败节点的工作
        // 3. 选举新的 Leader（如果需要）
    }
}
```

---

### 2. 故障恢复策略

#### 实现5

```rust
pub struct FailoverManager {
    primary: Arc<RwLock<Option<String>>>,
    replicas: Arc<RwLock<Vec<String>>>,
}

impl FailoverManager {
    /// 主节点故障转移
    pub async fn failover_primary(&self) -> Result<String> {
        let replicas = self.replicas.read().await;

        if replicas.is_empty() {
            return Err(anyhow::anyhow!("No replicas available"));
        }

        // 选择最合适的副本升级为主节点
        let new_primary = self.select_best_replica(&replicas).await?;

        // 升级副本
        self.promote_replica(&new_primary).await?;

        // 更新主节点
        *self.primary.write().await = Some(new_primary.clone());

        // 通知其他节点
        self.notify_failover(&new_primary).await?;

        Ok(new_primary)
    }

    async fn select_best_replica(&self, replicas: &[String]) -> Result<String> {
        // 选择数据最新、延迟最低的副本
        // 简化版本：选择第一个
        Ok(replicas[0].clone())
    }

    async fn promote_replica(&self, replica: &str) -> Result<()> {
        // 将副本升级为主节点
        println!("Promoting replica {} to primary", replica);
        Ok(())
    }

    async fn notify_failover(&self, new_primary: &str) -> Result<()> {
        // 通知所有节点新的主节点
        println!("Notifying all nodes of new primary: {}", new_primary);
        Ok(())
    }
}
```

---

## 🔄 数据复制

### 1. 主从复制

#### 实现6

```rust
pub struct ReplicationMaster {
    replicas: Arc<RwLock<Vec<ReplicaInfo>>>,
    replication_log: Arc<RwLock<Vec<ReplicationEntry>>>,
}

#[derive(Debug, Clone)]
pub struct ReplicaInfo {
    pub id: String,
    pub last_synced_index: u64,
    pub lag: Duration,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReplicationEntry {
    pub index: u64,
    pub timestamp: u64,
    pub operation: Operation,
    pub data: Vec<u8>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Operation {
    Write,
    Delete,
    Update,
}

impl ReplicationMaster {
    /// 写入数据并复制到副本
    pub async fn write(&self, data: Vec<u8>) -> Result<()> {
        // 1. 写入主节点
        let entry = self.create_replication_entry(Operation::Write, data).await?;

        // 2. 添加到复制日志
        self.replication_log.write().await.push(entry.clone());

        // 3. 异步复制到副本
        self.replicate_to_replicas(entry).await?;

        Ok(())
    }

    async fn replicate_to_replicas(&self, entry: ReplicationEntry) -> Result<()> {
        let replicas = self.replicas.read().await.clone();

        // 并发复制到所有副本
        let tasks: Vec<_> = replicas.iter()
            .map(|replica| {
                let entry = entry.clone();
                let replica_id = replica.id.clone();
                tokio::spawn(async move {
                    self.replicate_to_replica(&replica_id, entry).await
                })
            })
            .collect();

        // 等待所有复制完成
        for task in tasks {
            task.await??;
        }

        Ok(())
    }

    async fn replicate_to_replica(&self, replica_id: &str, entry: ReplicationEntry) -> Result<()> {
        // 发送复制数据到副本
        println!("Replicating entry {} to replica {}", entry.index, replica_id);

        // 更新副本状态
        let mut replicas = self.replicas.write().await;
        if let Some(replica) = replicas.iter_mut().find(|r| r.id == replica_id) {
            replica.last_synced_index = entry.index;
        }

        Ok(())
    }
}
```

---

### 2. 多主复制

#### 实现7

```rust
pub struct MultiMasterNode {
    node_id: String,
    vector_clock: Arc<RwLock<VectorClock>>,
    data_store: Arc<RwLock<HashMap<String, VersionedValue>>>,
    peers: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct VersionedValue {
    pub value: Vec<u8>,
    pub version: VectorClock,
}

impl MultiMasterNode {
    /// 写入数据
    pub async fn write(&self, key: String, value: Vec<u8>) -> Result<()> {
        // 1. 递增本地向量时钟
        let mut clock = self.vector_clock.write().await;
        clock.increment(&self.node_id);

        // 2. 创建版本化值
        let versioned = VersionedValue {
            value: value.clone(),
            version: clock.clone(),
        };

        // 3. 写入本地存储
        self.data_store.write().await.insert(key.clone(), versioned.clone());

        // 4. 异步复制到其他主节点
        self.replicate_to_peers(key, versioned).await?;

        Ok(())
    }

    /// 读取数据
    pub async fn read(&self, key: &str) -> Result<Option<Vec<u8>>> {
        let store = self.data_store.read().await;
        Ok(store.get(key).map(|v| v.value.clone()))
    }

    /// 处理来自其他节点的更新
    pub async fn handle_remote_write(
        &self,
        key: String,
        value: VersionedValue,
    ) -> Result<()> {
        let mut store = self.data_store.write().await;

        match store.get(&key) {
            Some(local) => {
                // 比较版本
                match local.version.partial_cmp(&value.version) {
                    Some(Ordering::Less) => {
                        // 远程版本更新，接受更新
                        store.insert(key, value);
                    }
                    Some(Ordering::Greater) => {
                        // 本地版本更新，忽略
                    }
                    None => {
                        // 并发冲突，需要解决
                        self.resolve_conflict(key, local.clone(), value).await?;
                    }
                    _ => {}
                }
            }
            None => {
                // 本地没有，直接插入
                store.insert(key, value);
            }
        }

        Ok(())
    }

    async fn resolve_conflict(
        &self,
        key: String,
        local: VersionedValue,
        remote: VersionedValue,
    ) -> Result<()> {
        // 冲突解决策略：Last Write Wins (LWW)
        // 或者保存多个版本让应用层解决

        println!("Conflict detected for key: {}", key);

        // 简化：保存两个版本
        // 实际应用中可能需要更复杂的冲突解决策略

        Ok(())
    }
}
```

---

## ⚖️ CAP 理论实践

### CAP 三角

```text
        Consistency (一致性)
               /\
              /  \
             /    \
            /      \
           /   CA   \
          /          \
Partition-------------- Availability
 (分区容错)             (可用性)
    CP                    AP
```

### 1. CP 系统 (一致性 + 分区容错)

```rust
pub struct CPSystem {
    consensus: Arc<RaftNode>,
    data: Arc<RwLock<HashMap<String, String>>>,
}

impl CPSystem {
    /// 强一致性写入
    pub async fn write(&self, key: String, value: String) -> Result<()> {
        // 必须通过共识算法
        let command = serde_json::to_vec(&(key.clone(), value.clone()))?;

        self.consensus.append_entry(command).await?;

        // 等待提交
        self.wait_for_commit().await?;

        // 应用到本地状态机
        self.data.write().await.insert(key, value);

        Ok(())
    }

    /// 强一致性读取
    pub async fn read(&self, key: &str) -> Result<Option<String>> {
        // 必须从 Leader 读取
        if !self.consensus.is_leader().await {
            return Err(anyhow::anyhow!("Not a leader"));
        }

        Ok(self.data.read().await.get(key).cloned())
    }
}
```

---

### 2. AP 系统 (可用性 + 分区容错)

```rust
pub struct APSystem {
    local_data: Arc<RwLock<HashMap<String, VersionedValue>>>,
    vector_clock: Arc<RwLock<VectorClock>>,
}

impl APSystem {
    /// 最终一致性写入
    pub async fn write(&self, key: String, value: String) -> Result<()> {
        // 立即写入本地
        let mut clock = self.vector_clock.write().await;
        clock.increment(&self.node_id);

        let versioned = VersionedValue {
            value: value.into_bytes(),
            version: clock.clone(),
        };

        self.local_data.write().await.insert(key.clone(), versioned.clone());

        // 异步复制（不等待）
        tokio::spawn(async move {
            self.replicate_async(key, versioned).await.ok();
        });

        Ok(())  // 立即返回
    }

    /// 最终一致性读取
    pub async fn read(&self, key: &str) -> Result<Option<String>> {
        // 从本地读取（可能是旧数据）
        let data = self.local_data.read().await;
        Ok(data.get(key).map(|v| String::from_utf8_lossy(&v.value).to_string()))
    }
}
```

---

## 总结

### 分布式系统可靠性清单

- ✅ **共识算法**: Raft, Paxos
- ✅ **最终一致性**: CRDT, Vector Clock
- ✅ **分布式事务**: 2PC, Saga
- ✅ **分布式锁**: Redis, Zookeeper
- ✅ **故障检测**: Heartbeat, Failure Detector
- ✅ **数据复制**: Master-Slave, Multi-Master
- ✅ **CAP 理论**: CP vs AP 的权衡

### 最佳实践

1. **选择合适的一致性模型**: 根据业务需求权衡
2. **容忍网络分区**: 设计时假设分区会发生
3. **幂等性设计**: 确保操作可以安全重试
4. **监控和告警**: 及时发现和处理故障
5. **故障演练**: 定期进行故障注入测试

---

**文档贡献者:** AI Assistant
**审核状态:** ✅ 已完成
**最后更新:** 2025年10月28日
