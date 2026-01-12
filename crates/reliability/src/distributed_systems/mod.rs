//! # 分布式系统模型
//!
//! 本模块提供分布式系统的核心算法和模型实现：
//! - 分布式共识算法 (Raft, Paxos, etc.)
//! - 分布式事务 (2PC, 3PC, Saga, TCC)
//! - 分布式协调 (Gossip, Vector Clocks, HLC)
//! - 一致性哈希
//! - 分布式锁
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步分布式操作
//! - **元组收集**: 使用 `collect()` 直接收集分布式节点到元组
//! - **改进的共识算法**: 利用 Rust 1.92 的共识算法优化提升性能

pub mod consensus;
pub mod consistent_hashing;
pub mod coordination;
pub mod distributed_lock;
pub mod replication;
pub mod transaction;

// 重新导出核心类型（避免命名冲突）
pub use consensus::raft::RaftNode;
pub use consensus::types::*;
pub use transaction::saga::SagaCoordinator;
// pub use coordination::gossip::GossipProtocol;  // GossipProtocol类型不存在，使用Gossip
pub use consistent_hashing::{ConsistentHashRing, JumpConsistentHash, RendezvousHash};
pub use coordination::hybrid_logical_clock::HybridLogicalClock;
pub use coordination::vector_clock::VectorClock;
pub use distributed_lock::{DistributedLock, LocalDistributedLock, LockOptions, RedlockLock};
pub use replication::{ReplicationConfig, ReplicationCoordinator, ReplicationMode};
