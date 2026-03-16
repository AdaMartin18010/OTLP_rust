//! Raft 共识算法演示示例
//!
//! 本示例展示如何使用 Raft 共识算法实现分布式一致性
//!
//! # 运行示例
//!
//! ```bash
//! cargo run --example raft_consensus_demo
//! ```

use reliability::distributed_systems::consensus::{
    ClusterConfig, ConsensusAlgorithm, ConsensusState, NodeId, RaftNode,
};
use reliability::error_handling::UnifiedError;
use std::time::Duration;
use tokio::time::sleep;

#[tokio::main]
#[allow(clippy::result_large_err)]
async fn main() -> Result<(), UnifiedError> {
    println!("=== Raft 共识算法演示 ===\n");

    // 示例 1: 创建 Raft 集群节点
    demo_1_create_raft_nodes().await?;

    println!("\n{}", "=".repeat(60));

    // 示例 2: Leader 选举演示
    demo_2_leader_election().await?;

    println!("\n{}", "=".repeat(60));

    // 示例 3: 日志复制演示
    demo_3_log_replication().await?;

    println!("\n{}", "=".repeat(60));

    // 示例 4: 提案提交和等待
    demo_4_proposal_workflow().await?;

    Ok(())
}

/// 示例 1: 创建 Raft 集群节点
async fn demo_1_create_raft_nodes() -> Result<(), UnifiedError> {
    println!("📝 示例 1: 创建 Raft 集群节点\n");

    // 配置 3 节点集群
    let config = ClusterConfig {
        nodes: vec![
            NodeId::new("node1"),
            NodeId::new("node2"),
            NodeId::new("node3"),
        ],
        self_id: NodeId::new("node1"),
        heartbeat_interval_ms: 100,
        election_timeout_range_ms: (150, 300),
    };

    println!("集群配置:");
    println!("  节点数量: {}", config.nodes.len());
    println!("  当前节点: {:?}", config.self_id);
    println!("  心跳间隔: {}ms", config.heartbeat_interval_ms);
    println!(
        "  选举超时: {}-{}ms",
        config.election_timeout_range_ms.0, config.election_timeout_range_ms.1
    );

    // 创建 Raft 节点
    let node = RaftNode::new(config);

    println!("\n✅ Raft 节点创建成功");
    println!("  初始状态: {:?}", node.get_state());
    println!("  当前任期: {}", node.current_term());
    println!("  是否为 Leader: {}", node.is_leader());

    Ok(())
}

/// 示例 2: Leader 选举演示
async fn demo_2_leader_election() -> Result<(), UnifiedError> {
    println!("📝 示例 2: Leader 选举演示\n");

    let config = ClusterConfig {
        nodes: vec![
            NodeId::new("node1"),
            NodeId::new("node2"),
            NodeId::new("node3"),
        ],
        self_id: NodeId::new("node1"),
        heartbeat_interval_ms: 100,
        election_timeout_range_ms: (150, 300),
    };

    let node = RaftNode::new(config);

    println!("初始状态: {:?}", node.get_state());

    // 启动节点（模拟场景）
    println!("\n🚀 启动节点...");

    // 模拟选举过程
    println!("⏰ 等待选举超时...");
    sleep(Duration::from_millis(200)).await;

    println!("\n当前状态:");
    match node.get_state() {
        ConsensusState::Follower => println!("  状态: Follower (跟随者)"),
        ConsensusState::Candidate => println!("  状态: Candidate (候选者)"),
        ConsensusState::Leader => println!("  状态: Leader (领导者)"),
    }
    println!("  任期: {}", node.current_term());

    println!("\n💡 说明:");
    println!("  - 节点启动时为 Follower 状态");
    println!("  - 选举超时后变为 Candidate");
    println!("  - 获得多数票后成为 Leader");
    println!("  - Leader 定期发送心跳维持地位");

    Ok(())
}

/// 示例 3: 日志复制演示
async fn demo_3_log_replication() -> Result<(), UnifiedError> {
    println!("📝 示例 3: 日志复制演示\n");

    let config = ClusterConfig {
        nodes: vec![
            NodeId::new("node1"),
            NodeId::new("node2"),
            NodeId::new("node3"),
        ],
        self_id: NodeId::new("node1"),
        heartbeat_interval_ms: 50,
        election_timeout_range_ms: (150, 300),
    };

    let mut node = RaftNode::new(config);

    println!("📊 日志复制流程:\n");

    println!("1️⃣ Leader 接收客户端请求");
    let data1 = b"transaction_1: transfer $100".to_vec();
    println!("   数据: {:?}", String::from_utf8_lossy(&data1));

    // 在实际场景中，需要先确保节点是 Leader
    if node.is_leader() {
        println!("\n2️⃣ Leader 追加到本地日志");
        let proposal_id = node.propose(data1.clone()).await?;
        println!("   提案 ID: {:?}", proposal_id);

        println!("\n3️⃣ Leader 向 Followers 发送 AppendEntries RPC");
        println!(
            "   → node2: AppendEntries(term={}, entries=[...])",
            node.current_term()
        );
        println!(
            "   → node3: AppendEntries(term={}, entries=[...])",
            node.current_term()
        );

        println!("\n4️⃣ 等待多数节点确认");
        println!("   ← node2: Success");
        println!("   ← node3: Success");

        println!("\n5️⃣ 日志提交成功");
        println!("   ✅ 已复制到多数节点");
    } else {
        println!("\n⚠️  当前节点不是 Leader，无法提交提案");
        println!("   提示: 在实际场景中，需要将请求转发给 Leader");
    }

    println!("\n💡 日志复制保证:");
    println!("  ✅ 顺序性: 日志按顺序追加");
    println!("  ✅ 一致性: 多数节点相同才提交");
    println!("  ✅ 持久性: 提交后不会丢失");

    Ok(())
}

/// 示例 4: 提案提交和等待
async fn demo_4_proposal_workflow() -> Result<(), UnifiedError> {
    println!("📝 示例 4: 提案提交和等待完整流程\n");

    let config = ClusterConfig {
        nodes: vec![
            NodeId::new("node1"),
            NodeId::new("node2"),
            NodeId::new("node3"),
        ],
        self_id: NodeId::new("node1"),
        heartbeat_interval_ms: 50,
        election_timeout_range_ms: (150, 300),
    };

    let mut node = RaftNode::new(config);

    println!("🎯 场景: 分布式键值存储\n");

    // 模拟一系列操作
    let operations = [
        ("SET", "user:1001", "Alice"),
        ("SET", "user:1002", "Bob"),
        ("SET", "balance:1001", "1000"),
        ("SET", "balance:1002", "500"),
    ];

    println!("待提交的操作:");
    for (idx, (op, key, value)) in operations.iter().enumerate() {
        println!("  {}. {} {} = {}", idx + 1, op, key, value);
    }

    if node.is_leader() {
        println!("\n开始提交...\n");

        for (idx, (op, key, value)) in operations.iter().enumerate() {
            let data = format!("{} {} {}", op, key, value).into_bytes();

            println!("📤 提交操作 {}: {} {} = {}", idx + 1, op, key, value);

            // 提交提案
            let proposal_id = node.propose(data.clone()).await?;

            // 等待提交完成
            match node.wait_committed(proposal_id).await {
                Ok(committed_data) => {
                    println!("   ✅ 已提交: {}", String::from_utf8_lossy(&committed_data));
                }
                Err(e) => {
                    println!("   ❌ 提交失败: {}", e);
                }
            }

            // 模拟短暂延迟
            sleep(Duration::from_millis(10)).await;
        }

        println!("\n🎉 所有操作已成功提交到集群！");
    } else {
        println!("\n⚠️  当前节点不是 Leader");
        println!("   在实际应用中，客户端需要:");
        println!("   1. 发现当前的 Leader 节点");
        println!("   2. 将请求发送给 Leader");
        println!("   3. 如果 Leader 失败，重新发现新 Leader");
    }

    println!("\n📊 Raft 性能特点:");
    println!("  延迟: ~2-10ms (取决于网络和集群大小)");
    println!("  吞吐量: ~5K-50K ops/sec (取决于批处理)");
    println!("  一致性: 强一致性 (Linearizable)");

    Ok(())
}
