# Reinforcement Learning 完整实现 - Rust 1.90 + OTLP 集成

## 目录

- [Reinforcement Learning 完整实现 - Rust 1.90 + OTLP 集成](#reinforcement-learning-完整实现---rust-190--otlp-集成)
  - [目录](#目录)
  - [1. 核心概念与理论](#1-核心概念与理论)
    - [1.1 强化学习基础](#11-强化学习基础)
    - [1.2 RL vs 监督学习](#12-rl-vs-监督学习)
    - [1.3 国际标准对齐](#13-国际标准对齐)
  - [2. Q-Learning算法](#2-q-learning算法)
    - [2.1 Q-Table实现](#21-q-table实现)
    - [2.2 Deep Q-Network (DQN)](#22-deep-q-network-dqn)
    - [2.3 Experience Replay](#23-experience-replay)
  - [3. Policy Gradient方法](#3-policy-gradient方法)
    - [3.1 REINFORCE算法](#31-reinforce算法)
    - [3.2 Actor-Critic](#32-actor-critic)
    - [3.3 Advantage Actor-Critic (A2C)](#33-advantage-actor-critic-a2c)
  - [4. Proximal Policy Optimization (PPO)](#4-proximal-policy-optimization-ppo)
    - [4.1 PPO核心原理](#41-ppo核心原理)
    - [4.2 PPO完整实现](#42-ppo完整实现)
    - [4.3 PPO超参数调优](#43-ppo超参数调优)
  - [5. RLHF (Reinforcement Learning from Human Feedback)](#5-rlhf-reinforcement-learning-from-human-feedback)
    - [5.1 RLHF流程](#51-rlhf流程)
    - [5.2 Reward Model训练](#52-reward-model训练)
    - [5.3 PPO微调LLM](#53-ppo微调llm)
  - [6. 环境与仿真](#6-环境与仿真)
    - [6.1 Gym-like环境接口](#61-gym-like环境接口)
    - [6.2 自定义环境](#62-自定义环境)
  - [7. OTLP可观测性](#7-otlp可观测性)
    - [7.1 训练追踪](#71-训练追踪)
    - [7.2 性能指标](#72-性能指标)
  - [8. 生产实践](#8-生产实践)
    - [8.1 分布式训练](#81-分布式训练)
    - [8.2 模型部署](#82-模型部署)
  - [9. 参考资源](#9-参考资源)
    - [学术论文](#学术论文)
    - [Rust生态](#rust生态)
    - [经典书籍](#经典书籍)

---

## 1. 核心概念与理论

### 1.1 强化学习基础

**核心组件**:

```text
┌─────────────────────────────────────────────────────┐
│          Reinforcement Learning Loop                │
│                                                     │
│     Agent                        Environment        │
│       │                              │              │
│       │  1. Action (a_t)             │              │
│       │─────────────────────────────>│              │
│       │                              │              │
│       │  2. State (s_t+1)            │              │
│       │<─────────────────────────────│              │
│       │     Reward (r_t)             │              │
│       │                              │              │
│       ▼                              ▼              │
│   Policy π(a|s)                   Dynamics          │
│   Value V(s)                      P(s'|s,a)         │
│   Q-Value Q(s,a)                  Reward R(s,a)     │
│                                                     │
└─────────────────────────────────────────────────────┘
```

**马尔可夫决策过程 (MDP)**:

- **状态空间** S: 所有可能的状态
- **动作空间** A: 所有可能的动作
- **转移概率** P(s'|s,a): 状态转移
- **奖励函数** R(s,a): 即时奖励
- **折扣因子** γ: 未来奖励折扣 (0 ≤ γ ≤ 1)

**核心公式**:

```text
回报 (Return): G_t = r_t + γr_{t+1} + γ²r_{t+2} + ... = Σ γᵏr_{t+k}

状态价值函数: V^π(s) = E_π[G_t | s_t = s]

动作价值函数: Q^π(s,a) = E_π[G_t | s_t = s, a_t = a]

Bellman方程: V(s) = max_a [R(s,a) + γ Σ P(s'|s,a) V(s')]
```

### 1.2 RL vs 监督学习

| 维度 | 强化学习 (RL) | 监督学习 |
|------|---------------|----------|
| **数据来源** | Agent与环境交互 | 标注数据集 |
| **反馈** | 延迟奖励 | 即时标签 |
| **目标** | 最大化累计奖励 | 最小化预测误差 |
| **探索** | 需要平衡探索与利用 | 不需要探索 |
| **训练稳定性** | 不稳定 | 相对稳定 |
| **样本效率** | 低 | 高 |
| **适用场景** | 决策控制,游戏AI | 分类,回归 |

### 1.3 国际标准对齐

| 标准/框架 | 应用场景 | Rust实现 |
|-----------|----------|----------|
| **OpenAI Gym** | RL环境标准接口 | 自定义实现 |
| **IEEE 754** | 浮点运算 | Rust原生支持 |
| **OpenTelemetry** | 可观测性 | opentelemetry 0.27 |
| **Sutton & Barto RL Book** | 理论基础 | 算法参考 |

---

## 2. Q-Learning算法

### 2.1 Q-Table实现

```rust
// src/rl/q_learning.rs
use ndarray::Array2;
use rand::Rng;
use tracing::{info, instrument};
use std::collections::HashMap;

/// Q-Learning智能体
pub struct QLearningAgent {
    q_table: HashMap<(usize, usize), f32>, // (state, action) -> Q-value
    learning_rate: f32,  // α
    discount_factor: f32, // γ
    epsilon: f32,        // ε-greedy探索率
    epsilon_decay: f32,
    epsilon_min: f32,
}

impl QLearningAgent {
    pub fn new(
        learning_rate: f32,
        discount_factor: f32,
        epsilon: f32,
        epsilon_decay: f32,
    ) -> Self {
        Self {
            q_table: HashMap::new(),
            learning_rate,
            discount_factor,
            epsilon,
            epsilon_decay,
            epsilon_min: 0.01,
        }
    }

    /// ε-greedy策略选择动作
    #[instrument(skip(self))]
    pub fn select_action(&self, state: usize, num_actions: usize) -> usize {
        let mut rng = rand::thread_rng();

        if rng.gen::<f32>() < self.epsilon {
            // 探索: 随机选择
            rng.gen_range(0..num_actions)
        } else {
            // 利用: 选择最大Q值的动作
            self.get_best_action(state, num_actions)
        }
    }

    /// 获取最大Q值的动作
    fn get_best_action(&self, state: usize, num_actions: usize) -> usize {
        (0..num_actions)
            .max_by(|&a1, &a2| {
                let q1 = self.get_q_value(state, a1);
                let q2 = self.get_q_value(state, a2);
                q1.partial_cmp(&q2).unwrap()
            })
            .unwrap()
    }

    /// 获取Q值
    fn get_q_value(&self, state: usize, action: usize) -> f32 {
        *self.q_table.get(&(state, action)).unwrap_or(&0.0)
    }

    /// Q-Learning更新
    #[instrument(skip(self))]
    pub fn update(
        &mut self,
        state: usize,
        action: usize,
        reward: f32,
        next_state: usize,
        num_actions: usize,
        done: bool,
    ) {
        let current_q = self.get_q_value(state, action);

        let next_max_q = if done {
            0.0
        } else {
            (0..num_actions)
                .map(|a| self.get_q_value(next_state, a))
                .fold(f32::NEG_INFINITY, f32::max)
        };

        // Q-Learning更新公式
        // Q(s,a) ← Q(s,a) + α[r + γ max_a' Q(s',a') - Q(s,a)]
        let new_q = current_q + self.learning_rate * (
            reward + self.discount_factor * next_max_q - current_q
        );

        self.q_table.insert((state, action), new_q);

        info!(
            state = %state,
            action = %action,
            reward = %reward,
            current_q = %current_q,
            new_q = %new_q,
            "Q-value updated"
        );
    }

    /// 衰减探索率
    pub fn decay_epsilon(&mut self) {
        self.epsilon = (self.epsilon * self.epsilon_decay).max(self.epsilon_min);
    }

    /// 保存Q表
    pub fn save_q_table(&self, path: &str) -> std::io::Result<()> {
        let serialized = serde_json::to_string(&self.q_table)?;
        std::fs::write(path, serialized)?;
        Ok(())
    }
}
```

### 2.2 Deep Q-Network (DQN)

```rust
// src/rl/dqn.rs
use ndarray::{Array1, Array2};
use tracing::{info, instrument};

/// DQN神经网络 (简化实现概念)
pub struct DQNNetwork {
    input_dim: usize,
    hidden_dim: usize,
    output_dim: usize,
    // 实际应用中使用candle/burn等深度学习框架
}

impl DQNNetwork {
    pub fn new(input_dim: usize, hidden_dim: usize, output_dim: usize) -> Self {
        Self {
            input_dim,
            hidden_dim,
            output_dim,
        }
    }

    /// 前向传播
    pub fn forward(&self, state: &Array1<f32>) -> Array1<f32> {
        // 简化示例: 线性层
        // 实际需要使用深度学习框架
        Array1::zeros(self.output_dim)
    }

    /// 预测Q值
    pub fn predict_q_values(&self, state: &Array1<f32>) -> Array1<f32> {
        self.forward(state)
    }
}

/// DQN智能体
pub struct DQNAgent {
    network: DQNNetwork,
    target_network: DQNNetwork,
    learning_rate: f32,
    discount_factor: f32,
    epsilon: f32,
    epsilon_decay: f32,
    batch_size: usize,
    target_update_freq: usize,
    update_counter: usize,
}

impl DQNAgent {
    pub fn new(
        state_dim: usize,
        action_dim: usize,
        hidden_dim: usize,
        learning_rate: f32,
        discount_factor: f32,
    ) -> Self {
        Self {
            network: DQNNetwork::new(state_dim, hidden_dim, action_dim),
            target_network: DQNNetwork::new(state_dim, hidden_dim, action_dim),
            learning_rate,
            discount_factor,
            epsilon: 1.0,
            epsilon_decay: 0.995,
            batch_size: 32,
            target_update_freq: 100,
            update_counter: 0,
        }
    }

    /// 选择动作
    #[instrument(skip(self, state))]
    pub fn select_action(&self, state: &Array1<f32>) -> usize {
        let mut rng = rand::thread_rng();

        if rng.gen::<f32>() < self.epsilon {
            rng.gen_range(0..self.network.output_dim)
        } else {
            let q_values = self.network.predict_q_values(state);
            q_values
                .iter()
                .enumerate()
                .max_by(|(_, a), (_, b)| a.partial_cmp(b).unwrap())
                .map(|(idx, _)| idx)
                .unwrap()
        }
    }

    /// 训练 (简化概念)
    #[instrument(skip(self, replay_buffer))]
    pub fn train(&mut self, replay_buffer: &ExperienceReplay) -> f32 {
        if replay_buffer.size() < self.batch_size {
            return 0.0;
        }

        let batch = replay_buffer.sample(self.batch_size);

        // 计算损失并更新网络
        // 实际实现需要使用深度学习框架的反向传播

        self.update_counter += 1;

        // 定期更新目标网络
        if self.update_counter % self.target_update_freq == 0 {
            self.update_target_network();
        }

        // 衰减epsilon
        self.epsilon = (self.epsilon * self.epsilon_decay).max(0.01);

        0.0 // 返回损失
    }

    /// 更新目标网络
    fn update_target_network(&mut self) {
        info!("Updating target network");
        // 复制网络权重
        // self.target_network = self.network.clone();
    }
}
```

### 2.3 Experience Replay

```rust
// src/rl/replay_buffer.rs
use rand::seq::SliceRandom;
use std::collections::VecDeque;
use tracing::{info, instrument};

/// 经验回放样本
#[derive(Debug, Clone)]
pub struct Experience {
    pub state: Vec<f32>,
    pub action: usize,
    pub reward: f32,
    pub next_state: Vec<f32>,
    pub done: bool,
}

/// 经验回放缓冲区
pub struct ExperienceReplay {
    buffer: VecDeque<Experience>,
    capacity: usize,
}

impl ExperienceReplay {
    pub fn new(capacity: usize) -> Self {
        Self {
            buffer: VecDeque::with_capacity(capacity),
            capacity,
        }
    }

    /// 添加经验
    #[instrument(skip(self, experience))]
    pub fn add(&mut self, experience: Experience) {
        if self.buffer.len() >= self.capacity {
            self.buffer.pop_front();
        }
        self.buffer.push_back(experience);

        info!(
            buffer_size = %self.buffer.len(),
            capacity = %self.capacity,
            "Experience added"
        );
    }

    /// 随机采样批次
    #[instrument(skip(self))]
    pub fn sample(&self, batch_size: usize) -> Vec<Experience> {
        let mut rng = rand::thread_rng();

        self.buffer
            .iter()
            .collect::<Vec<_>>()
            .choose_multiple(&mut rng, batch_size)
            .map(|&exp| exp.clone())
            .collect()
    }

    /// 缓冲区大小
    pub fn size(&self) -> usize {
        self.buffer.len()
    }

    /// 清空缓冲区
    pub fn clear(&mut self) {
        self.buffer.clear();
    }
}
```

---

## 3. Policy Gradient方法

### 3.1 REINFORCE算法

```rust
// src/rl/reinforce.rs
use ndarray::Array1;
use tracing::{info, instrument};

/// REINFORCE算法智能体
pub struct ReinforceAgent {
    policy_network: PolicyNetwork,
    learning_rate: f32,
    discount_factor: f32,
}

/// 策略网络
pub struct PolicyNetwork {
    input_dim: usize,
    hidden_dim: usize,
    output_dim: usize,
}

impl PolicyNetwork {
    pub fn new(input_dim: usize, hidden_dim: usize, output_dim: usize) -> Self {
        Self {
            input_dim,
            hidden_dim,
            output_dim,
        }
    }

    /// 前向传播 -> 动作概率分布
    pub fn forward(&self, state: &Array1<f32>) -> Array1<f32> {
        // 简化: 返回均匀分布
        Array1::from_elem(self.output_dim, 1.0 / self.output_dim as f32)
    }

    /// 采样动作
    pub fn sample_action(&self, state: &Array1<f32>) -> usize {
        let probs = self.forward(state);
        // 按概率采样
        sample_from_distribution(&probs)
    }
}

impl ReinforceAgent {
    pub fn new(state_dim: usize, action_dim: usize, learning_rate: f32) -> Self {
        Self {
            policy_network: PolicyNetwork::new(state_dim, 128, action_dim),
            learning_rate,
            discount_factor: 0.99,
        }
    }

    /// 选择动作
    pub fn select_action(&self, state: &Array1<f32>) -> usize {
        self.policy_network.sample_action(state)
    }

    /// REINFORCE更新
    #[instrument(skip(self, trajectory))]
    pub fn update(&mut self, trajectory: &Trajectory) -> f32 {
        info!(trajectory_length = %trajectory.len(), "Updating policy with REINFORCE");

        // 计算回报
        let returns = self.compute_returns(&trajectory.rewards);

        // 策略梯度更新
        // ∇J(θ) = E[Σ_t ∇log π(a_t|s_t) G_t]
        let mut total_loss = 0.0;

        for (i, (state, action, g_t)) in trajectory.iter().zip(returns.iter()).enumerate() {
            // 计算log概率
            let log_prob = self.compute_log_prob(state, *action);

            // 策略梯度
            let loss = -log_prob * g_t;
            total_loss += loss;

            // 反向传播 (简化)
            // self.policy_network.backward(loss);
        }

        info!(total_loss = %total_loss, "Policy updated");

        total_loss
    }

    /// 计算折扣回报
    fn compute_returns(&self, rewards: &[f32]) -> Vec<f32> {
        let mut returns = Vec::with_capacity(rewards.len());
        let mut g_t = 0.0;

        for &reward in rewards.iter().rev() {
            g_t = reward + self.discount_factor * g_t;
            returns.push(g_t);
        }

        returns.reverse();
        returns
    }

    /// 计算log概率 (简化)
    fn compute_log_prob(&self, state: &[f32], action: usize) -> f32 {
        let state_arr = Array1::from(state.to_vec());
        let probs = self.policy_network.forward(&state_arr);
        probs[action].ln()
    }
}

/// 轨迹数据
#[derive(Debug)]
pub struct Trajectory {
    pub states: Vec<Vec<f32>>,
    pub actions: Vec<usize>,
    pub rewards: Vec<f32>,
}

impl Trajectory {
    pub fn new() -> Self {
        Self {
            states: Vec::new(),
            actions: Vec::new(),
            rewards: Vec::new(),
        }
    }

    pub fn add(&mut self, state: Vec<f32>, action: usize, reward: f32) {
        self.states.push(state);
        self.actions.push(action);
        self.rewards.push(reward);
    }

    pub fn len(&self) -> usize {
        self.states.len()
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Vec<f32>, &usize)> {
        self.states.iter().zip(self.actions.iter())
    }
}

/// 从概率分布采样
fn sample_from_distribution(probs: &Array1<f32>) -> usize {
    let mut rng = rand::thread_rng();
    let random_val: f32 = rng.gen();

    let mut cumulative = 0.0;
    for (i, &prob) in probs.iter().enumerate() {
        cumulative += prob;
        if random_val < cumulative {
            return i;
        }
    }

    probs.len() - 1
}
```

### 3.2 Actor-Critic

```rust
// src/rl/actor_critic.rs
use ndarray::Array1;
use tracing::{info, instrument};

/// Actor-Critic智能体
pub struct ActorCriticAgent {
    actor: PolicyNetwork,    // 策略网络
    critic: ValueNetwork,    // 价值网络
    actor_lr: f32,
    critic_lr: f32,
    discount_factor: f32,
}

/// 价值网络
pub struct ValueNetwork {
    input_dim: usize,
    hidden_dim: usize,
}

impl ValueNetwork {
    pub fn new(input_dim: usize, hidden_dim: usize) -> Self {
        Self {
            input_dim,
            hidden_dim,
        }
    }

    /// 预测状态价值
    pub fn predict(&self, state: &Array1<f32>) -> f32 {
        // 简化: 返回随机值
        0.0
    }
}

impl ActorCriticAgent {
    pub fn new(state_dim: usize, action_dim: usize) -> Self {
        Self {
            actor: PolicyNetwork::new(state_dim, 128, action_dim),
            critic: ValueNetwork::new(state_dim, 128),
            actor_lr: 0.001,
            critic_lr: 0.001,
            discount_factor: 0.99,
        }
    }

    /// 选择动作
    pub fn select_action(&self, state: &Array1<f32>) -> usize {
        self.actor.sample_action(state)
    }

    /// Actor-Critic更新
    #[instrument(skip(self, state, action, reward, next_state))]
    pub fn update(
        &mut self,
        state: &Array1<f32>,
        action: usize,
        reward: f32,
        next_state: &Array1<f32>,
        done: bool,
    ) -> (f32, f32) {
        // Critic更新: TD误差
        let value = self.critic.predict(state);
        let next_value = if done {
            0.0
        } else {
            self.critic.predict(next_state)
        };

        let td_error = reward + self.discount_factor * next_value - value;
        let critic_loss = td_error * td_error;

        // Actor更新: 策略梯度
        let log_prob = self.compute_log_prob(state, action);
        let actor_loss = -log_prob * td_error; // 使用TD误差作为优势函数

        info!(
            td_error = %td_error,
            actor_loss = %actor_loss,
            critic_loss = %critic_loss,
            "Actor-Critic updated"
        );

        // 反向传播 (简化)
        // self.actor.backward(actor_loss);
        // self.critic.backward(critic_loss);

        (actor_loss, critic_loss)
    }

    fn compute_log_prob(&self, state: &Array1<f32>, action: usize) -> f32 {
        let probs = self.actor.forward(state);
        probs[action].ln()
    }
}
```

### 3.3 Advantage Actor-Critic (A2C)

```rust
// src/rl/a2c.rs
use ndarray::Array1;
use tracing::{info, instrument};

/// A2C智能体
pub struct A2CAgent {
    actor: PolicyNetwork,
    critic: ValueNetwork,
    learning_rate: f32,
    discount_factor: f32,
    entropy_coef: f32, // 熵正则化系数
}

impl A2CAgent {
    pub fn new(state_dim: usize, action_dim: usize) -> Self {
        Self {
            actor: PolicyNetwork::new(state_dim, 128, action_dim),
            critic: ValueNetwork::new(state_dim, 128),
            learning_rate: 0.001,
            discount_factor: 0.99,
            entropy_coef: 0.01,
        }
    }

    /// A2C更新 (批量)
    #[instrument(skip(self, trajectory))]
    pub fn update(&mut self, trajectory: &Trajectory) -> (f32, f32, f32) {
        info!(trajectory_length = %trajectory.len(), "Updating with A2C");

        let mut actor_loss = 0.0;
        let mut critic_loss = 0.0;
        let mut entropy = 0.0;

        // 计算优势函数
        let advantages = self.compute_advantages(trajectory);

        for (i, ((state, action), advantage)) in trajectory.iter()
            .zip(advantages.iter())
            .enumerate()
        {
            let state_arr = Array1::from(state.clone());

            // Actor损失: 策略梯度 + 熵正则化
            let probs = self.actor.forward(&state_arr);
            let log_prob = probs[*action].ln();
            actor_loss += -log_prob * advantage;

            // 熵 = -Σ p(a) log p(a)
            let ent = -probs.iter().map(|&p| p * p.ln()).sum::<f32>();
            entropy += ent;

            // Critic损失: MSE
            let value = self.critic.predict(&state_arr);
            let target = advantage + value; // A(s,a) = Q(s,a) - V(s)
            critic_loss += (target - value).powi(2);
        }

        let n = trajectory.len() as f32;
        actor_loss /= n;
        critic_loss /= n;
        entropy /= n;

        // 总损失 = actor_loss + critic_loss - entropy_coef * entropy
        let total_loss = actor_loss + critic_loss - self.entropy_coef * entropy;

        info!(
            actor_loss = %actor_loss,
            critic_loss = %critic_loss,
            entropy = %entropy,
            total_loss = %total_loss,
            "A2C update completed"
        );

        (actor_loss, critic_loss, entropy)
    }

    /// 计算优势函数 A(s,a) = Q(s,a) - V(s)
    fn compute_advantages(&self, trajectory: &Trajectory) -> Vec<f32> {
        let mut advantages = Vec::with_capacity(trajectory.len());

        let mut returns = Vec::new();
        let mut g_t = 0.0;

        // 计算回报
        for &reward in trajectory.rewards.iter().rev() {
            g_t = reward + self.discount_factor * g_t;
            returns.push(g_t);
        }
        returns.reverse();

        // 计算优势
        for (state, g_t) in trajectory.states.iter().zip(returns.iter()) {
            let state_arr = Array1::from(state.clone());
            let value = self.critic.predict(&state_arr);
            advantages.push(g_t - value);
        }

        advantages
    }
}
```

---

## 4. Proximal Policy Optimization (PPO)

### 4.1 PPO核心原理

PPO是当前最流行的RL算法之一,用于LLM微调(RLHF)。

**核心思想**: 限制策略更新幅度,防止性能崩溃。

**目标函数**:

```text
L^CLIP(θ) = E_t[min(
    r_t(θ) Â_t,
    clip(r_t(θ), 1-ε, 1+ε) Â_t
)]

其中:
- r_t(θ) = π_θ(a_t|s_t) / π_θ_old(a_t|s_t)  (概率比)
- Â_t = 优势函数
- ε = 裁剪阈值 (通常0.1或0.2)
```

**优势**:

- ✅ 训练稳定
- ✅ 样本效率高
- ✅ 实现简单
- ✅ 适用范围广

### 4.2 PPO完整实现

```rust
// src/rl/ppo.rs
use ndarray::Array1;
use tracing::{info, instrument};

/// PPO智能体
pub struct PPOAgent {
    actor: PolicyNetwork,
    critic: ValueNetwork,
    old_actor: PolicyNetwork, // 旧策略(用于计算概率比)
    learning_rate: f32,
    discount_factor: f32,
    gae_lambda: f32,      // GAE λ参数
    clip_epsilon: f32,    // 裁剪阈值
    entropy_coef: f32,
    value_coef: f32,
    max_grad_norm: f32,
    ppo_epochs: usize,    // PPO更新轮数
    mini_batch_size: usize,
}

impl PPOAgent {
    pub fn new(state_dim: usize, action_dim: usize) -> Self {
        let actor = PolicyNetwork::new(state_dim, 256, action_dim);
        let old_actor = PolicyNetwork::new(state_dim, 256, action_dim);

        Self {
            actor,
            critic: ValueNetwork::new(state_dim, 256),
            old_actor,
            learning_rate: 3e-4,
            discount_factor: 0.99,
            gae_lambda: 0.95,
            clip_epsilon: 0.2,
            entropy_coef: 0.01,
            value_coef: 0.5,
            max_grad_norm: 0.5,
            ppo_epochs: 4,
            mini_batch_size: 64,
        }
    }

    /// PPO更新
    #[instrument(skip(self, rollout_buffer))]
    pub fn update(&mut self, rollout_buffer: &RolloutBuffer) -> PPOMetrics {
        info!(
            buffer_size = %rollout_buffer.size(),
            ppo_epochs = %self.ppo_epochs,
            "Starting PPO update"
        );

        // 复制当前策略到旧策略
        self.update_old_policy();

        let mut total_policy_loss = 0.0;
        let mut total_value_loss = 0.0;
        let mut total_entropy = 0.0;
        let mut update_count = 0;

        // 多轮PPO更新
        for epoch in 0..self.ppo_epochs {
            // 随机打乱数据
            let batches = rollout_buffer.shuffle_and_batch(self.mini_batch_size);

            for batch in batches {
                let (policy_loss, value_loss, entropy) = self.ppo_step(&batch);

                total_policy_loss += policy_loss;
                total_value_loss += value_loss;
                total_entropy += entropy;
                update_count += 1;
            }
        }

        let metrics = PPOMetrics {
            policy_loss: total_policy_loss / update_count as f32,
            value_loss: total_value_loss / update_count as f32,
            entropy: total_entropy / update_count as f32,
            update_count,
        };

        info!(
            policy_loss = %metrics.policy_loss,
            value_loss = %metrics.value_loss,
            entropy = %metrics.entropy,
            "PPO update completed"
        );

        metrics
    }

    /// 单步PPO更新
    fn ppo_step(&mut self, batch: &Batch) -> (f32, f32, f32) {
        let mut policy_loss = 0.0;
        let mut value_loss = 0.0;
        let mut entropy = 0.0;

        for sample in &batch.samples {
            let state_arr = Array1::from(sample.state.clone());

            // 计算当前策略概率
            let probs = self.actor.forward(&state_arr);
            let log_prob = probs[sample.action].ln();

            // 计算旧策略概率
            let old_probs = self.old_actor.forward(&state_arr);
            let old_log_prob = old_probs[sample.action].ln();

            // 概率比 r_t(θ)
            let ratio = (log_prob - old_log_prob).exp();

            // PPO裁剪目标
            let surr1 = ratio * sample.advantage;
            let surr2 = ratio.clamp(
                1.0 - self.clip_epsilon,
                1.0 + self.clip_epsilon
            ) * sample.advantage;

            policy_loss += -surr1.min(surr2);

            // 价值函数损失
            let value = self.critic.predict(&state_arr);
            value_loss += (sample.return_ - value).powi(2);

            // 熵
            let ent = -probs.iter().map(|&p| p * p.ln()).sum::<f32>();
            entropy += ent;
        }

        let n = batch.samples.len() as f32;

        (
            policy_loss / n,
            value_loss / n,
            entropy / n,
        )
    }

    /// 更新旧策略
    fn update_old_policy(&mut self) {
        // self.old_actor = self.actor.clone();
    }

    /// 计算GAE (Generalized Advantage Estimation)
    #[instrument(skip(self, rollout_buffer))]
    pub fn compute_gae(&self, rollout_buffer: &mut RolloutBuffer) {
        let mut gae = 0.0;

        for i in (0..rollout_buffer.size()).rev() {
            let sample = &rollout_buffer.samples[i];
            let state_arr = Array1::from(sample.state.clone());

            let value = self.critic.predict(&state_arr);

            let next_value = if i == rollout_buffer.size() - 1 {
                0.0
            } else {
                let next_state_arr = Array1::from(rollout_buffer.samples[i + 1].state.clone());
                self.critic.predict(&next_state_arr)
            };

            let delta = sample.reward + self.discount_factor * next_value - value;
            gae = delta + self.discount_factor * self.gae_lambda * gae;

            rollout_buffer.samples[i].advantage = gae;
            rollout_buffer.samples[i].return_ = gae + value;
        }

        info!("GAE computation completed");
    }
}

/// PPO训练指标
#[derive(Debug, Clone)]
pub struct PPOMetrics {
    pub policy_loss: f32,
    pub value_loss: f32,
    pub entropy: f32,
    pub update_count: usize,
}

/// Rollout缓冲区
pub struct RolloutBuffer {
    pub samples: Vec<RolloutSample>,
}

#[derive(Debug, Clone)]
pub struct RolloutSample {
    pub state: Vec<f32>,
    pub action: usize,
    pub reward: f32,
    pub advantage: f32,
    pub return_: f32,
}

impl RolloutBuffer {
    pub fn new() -> Self {
        Self {
            samples: Vec::new(),
        }
    }

    pub fn add(&mut self, state: Vec<f32>, action: usize, reward: f32) {
        self.samples.push(RolloutSample {
            state,
            action,
            reward,
            advantage: 0.0,
            return_: 0.0,
        });
    }

    pub fn size(&self) -> usize {
        self.samples.len()
    }

    pub fn clear(&mut self) {
        self.samples.clear();
    }

    /// 打乱并分批
    pub fn shuffle_and_batch(&self, batch_size: usize) -> Vec<Batch> {
        use rand::seq::SliceRandom;

        let mut indices: Vec<usize> = (0..self.samples.len()).collect();
        indices.shuffle(&mut rand::thread_rng());

        indices
            .chunks(batch_size)
            .map(|chunk| Batch {
                samples: chunk.iter().map(|&i| self.samples[i].clone()).collect(),
            })
            .collect()
    }
}

/// 训练批次
pub struct Batch {
    pub samples: Vec<RolloutSample>,
}
```

### 4.3 PPO超参数调优

| 超参数 | 典型值 | 说明 |
|--------|--------|------|
| **learning_rate** | 3e-4 | 学习率 |
| **discount_factor (γ)** | 0.99 | 折扣因子 |
| **gae_lambda (λ)** | 0.95 | GAE平滑参数 |
| **clip_epsilon (ε)** | 0.1~0.2 | PPO裁剪阈值 |
| **entropy_coef** | 0.01 | 熵正则化系数 |
| **value_coef** | 0.5 | 价值损失系数 |
| **ppo_epochs** | 3~10 | PPO更新轮数 |
| **mini_batch_size** | 32~256 | Mini-batch大小 |
| **n_steps** | 128~2048 | Rollout步数 |

---

## 5. RLHF (Reinforcement Learning from Human Feedback)

### 5.1 RLHF流程

```text
┌────────────────────────────────────────────────────────────┐
│                RLHF Pipeline (3 Stages)                    │
│                                                            │
│  Stage 1: Supervised Fine-Tuning (SFT)                     │
│  ┌──────────────────────────────────────────────────────┐  │
│  │  Base LLM  →  SFT Data  →  SFT Model                 │  │
│  │  (GPT/LLaMA)   (高质量示例)   (初始对齐)               │  │
│  └──────────────────────────────────────────────────────┘  │
│                          │                                 │
│                          ▼                                 │
│  Stage 2: Reward Model Training                            │
│  ┌──────────────────────────────────────────────────────┐  │
│  │  SFT Model  →  Human Preferences  →  Reward Model    │  │
│  │  (生成对比)    (人类偏好排序)       (评分器)            │  │
│  └──────────────────────────────────────────────────────┘  │
│                          │                                 │
│                          ▼                                 │
│  Stage 3: PPO Fine-Tuning                                  │
│  ┌──────────────────────────────────────────────────────┐  │
│  │  SFT Model  +  Reward Model  →  PPO  →  RLHF Model   │  │
│  │  (策略)        (奖励信号)      (优化)   (最终模型)     │  │
│  └──────────────────────────────────────────────────────┘  │
└────────────────────────────────────────────────────────────┘
```

### 5.2 Reward Model训练

```rust
// src/rlhf/reward_model.rs
use ndarray::Array1;
use tracing::{info, instrument};

/// 奖励模型 (简化概念)
pub struct RewardModel {
    model: ValueNetwork, // 实际使用Transformer
}

impl RewardModel {
    pub fn new(input_dim: usize) -> Self {
        Self {
            model: ValueNetwork::new(input_dim, 512),
        }
    }

    /// 预测奖励分数
    #[instrument(skip(self, text_embedding))]
    pub fn predict_reward(&self, text_embedding: &Array1<f32>) -> f32 {
        let reward = self.model.predict(text_embedding);

        info!(reward = %reward, "Reward predicted");

        reward
    }

    /// 训练奖励模型
    #[instrument(skip(self, preferences))]
    pub fn train(&mut self, preferences: &[Preference]) -> f32 {
        info!(num_preferences = %preferences.len(), "Training reward model");

        let mut total_loss = 0.0;

        for pref in preferences {
            // 预测两个响应的奖励
            let reward_chosen = self.predict_reward(&pref.chosen_embedding);
            let reward_rejected = self.predict_reward(&pref.rejected_embedding);

            // Bradley-Terry模型损失
            // Loss = -log(σ(r_chosen - r_rejected))
            let diff = reward_chosen - reward_rejected;
            let loss = -(1.0 / (1.0 + (-diff).exp())).ln();

            total_loss += loss;

            // 反向传播 (简化)
            // self.model.backward(loss);
        }

        let avg_loss = total_loss / preferences.len() as f32;

        info!(avg_loss = %avg_loss, "Reward model training completed");

        avg_loss
    }
}

/// 人类偏好数据
#[derive(Debug, Clone)]
pub struct Preference {
    pub prompt_embedding: Array1<f32>,
    pub chosen_embedding: Array1<f32>,    // 更好的响应
    pub rejected_embedding: Array1<f32>,  // 较差的响应
}
```

### 5.3 PPO微调LLM

```rust
// src/rlhf/ppo_trainer.rs
use tracing::{info, instrument};

/// RLHF PPO训练器
pub struct RLHFTrainer {
    policy_model: PolicyLLM,      // 策略LLM (要优化的)
    ref_model: PolicyLLM,         // 参考LLM (用于KL散度)
    reward_model: RewardModel,
    ppo_agent: PPOAgent,
    kl_coef: f32,                 // KL散度系数
}

/// 策略LLM (简化接口)
pub struct PolicyLLM {
    // 实际使用transformer模型
}

impl PolicyLLM {
    pub fn generate(&self, prompt: &str) -> String {
        // 生成响应
        String::from("Generated response")
    }

    pub fn log_prob(&self, prompt: &str, response: &str) -> f32 {
        // 计算log概率
        0.0
    }
}

impl RLHFTrainer {
    pub fn new(
        policy_model: PolicyLLM,
        ref_model: PolicyLLM,
        reward_model: RewardModel,
    ) -> Self {
        Self {
            policy_model,
            ref_model,
            reward_model,
            ppo_agent: PPOAgent::new(768, 50257), // 示例维度
            kl_coef: 0.1,
        }
    }

    /// RLHF训练步骤
    #[instrument(skip(self, prompts))]
    pub fn train_step(&mut self, prompts: &[String]) -> RLHFMetrics {
        info!(num_prompts = %prompts.len(), "Starting RLHF training step");

        let mut total_reward = 0.0;
        let mut total_kl = 0.0;
        let mut rollout_buffer = RolloutBuffer::new();

        // 1. 收集Rollout数据
        for prompt in prompts {
            // 策略模型生成响应
            let response = self.policy_model.generate(prompt);

            // 计算奖励 = reward_model(response) - kl_penalty
            let rm_reward = self.compute_reward(&response);
            let kl_penalty = self.compute_kl_penalty(prompt, &response);
            let reward = rm_reward - self.kl_coef * kl_penalty;

            total_reward += reward;
            total_kl += kl_penalty;

            // 添加到buffer (简化: state=prompt_embedding)
            let state_embedding = self.encode_prompt(prompt);
            rollout_buffer.add(state_embedding, 0, reward);
        }

        // 2. 计算GAE
        self.ppo_agent.compute_gae(&mut rollout_buffer);

        // 3. PPO更新
        let ppo_metrics = self.ppo_agent.update(&rollout_buffer);

        let metrics = RLHFMetrics {
            avg_reward: total_reward / prompts.len() as f32,
            avg_kl: total_kl / prompts.len() as f32,
            policy_loss: ppo_metrics.policy_loss,
            value_loss: ppo_metrics.value_loss,
        };

        info!(
            avg_reward = %metrics.avg_reward,
            avg_kl = %metrics.avg_kl,
            policy_loss = %metrics.policy_loss,
            "RLHF training step completed"
        );

        metrics
    }

    /// 计算奖励模型分数
    fn compute_reward(&self, response: &str) -> f32 {
        let embedding = self.encode_response(response);
        self.reward_model.predict_reward(&embedding)
    }

    /// 计算KL散度惩罚
    fn compute_kl_penalty(&self, prompt: &str, response: &str) -> f32 {
        let log_prob_policy = self.policy_model.log_prob(prompt, response);
        let log_prob_ref = self.ref_model.log_prob(prompt, response);

        // KL(π || π_ref) ≈ log π(a|s) - log π_ref(a|s)
        log_prob_policy - log_prob_ref
    }

    fn encode_prompt(&self, prompt: &str) -> Vec<f32> {
        // 编码prompt为向量
        vec![0.0; 768]
    }

    fn encode_response(&self, response: &str) -> Array1<f32> {
        // 编码response为向量
        Array1::zeros(768)
    }
}

/// RLHF训练指标
#[derive(Debug, Clone)]
pub struct RLHFMetrics {
    pub avg_reward: f32,
    pub avg_kl: f32,
    pub policy_loss: f32,
    pub value_loss: f32,
}
```

---

## 6. 环境与仿真

### 6.1 Gym-like环境接口

```rust
// src/env/gym.rs
use anyhow::Result;
use ndarray::Array1;
use tracing::{info, instrument};

/// Gym风格环境接口
pub trait Environment {
    type State;
    type Action;

    /// 重置环境
    fn reset(&mut self) -> Self::State;

    /// 执行动作
    fn step(&mut self, action: &Self::Action) -> StepResult<Self::State>;

    /// 渲染环境 (可选)
    fn render(&self) {}

    /// 环境是否结束
    fn is_done(&self) -> bool;

    /// 动作空间大小
    fn action_space_size(&self) -> usize;

    /// 状态空间维度
    fn observation_space_dim(&self) -> usize;
}

/// Step结果
#[derive(Debug, Clone)]
pub struct StepResult<S> {
    pub next_state: S,
    pub reward: f32,
    pub done: bool,
    pub info: StepInfo,
}

#[derive(Debug, Clone, Default)]
pub struct StepInfo {
    pub episode_reward: Option<f32>,
    pub episode_length: Option<usize>,
}
```

### 6.2 自定义环境

```rust
// src/env/cartpole.rs
use super::{Environment, StepResult, StepInfo};
use ndarray::Array1;
use tracing::{info, instrument};

/// CartPole环境 (简化)
pub struct CartPoleEnv {
    state: [f32; 4], // [x, x_dot, theta, theta_dot]
    steps: usize,
    max_steps: usize,
    done: bool,
}

impl CartPoleEnv {
    pub fn new() -> Self {
        Self {
            state: [0.0; 4],
            steps: 0,
            max_steps: 500,
            done: false,
        }
    }

    fn update_physics(&mut self, force: f32) {
        // 简化的物理模拟
        let dt = 0.02; // 时间步长
        let gravity = 9.8;
        let cart_mass = 1.0;
        let pole_mass = 0.1;

        let x = self.state[0];
        let x_dot = self.state[1];
        let theta = self.state[2];
        let theta_dot = self.state[3];

        // 简化物理更新
        let theta_acc = gravity * theta.sin();
        let x_acc = force;

        self.state[1] += x_acc * dt;
        self.state[0] += x_dot * dt;
        self.state[3] += theta_acc * dt;
        self.state[2] += theta_dot * dt;
    }
}

impl Environment for CartPoleEnv {
    type State = Array1<f32>;
    type Action = usize; // 0: 左, 1: 右

    #[instrument(skip(self))]
    fn reset(&mut self) -> Self::State {
        self.state = [
            rand::random::<f32>() * 0.1 - 0.05,
            0.0,
            rand::random::<f32>() * 0.1 - 0.05,
            0.0,
        ];
        self.steps = 0;
        self.done = false;

        info!("CartPole environment reset");

        Array1::from(self.state.to_vec())
    }

    #[instrument(skip(self))]
    fn step(&mut self, action: &Self::Action) -> StepResult<Self::State> {
        let force = if *action == 0 { -10.0 } else { 10.0 };

        self.update_physics(force);
        self.steps += 1;

        // 检查终止条件
        let x = self.state[0];
        let theta = self.state[2];

        self.done = x.abs() > 2.4
            || theta.abs() > 0.209 // ~12度
            || self.steps >= self.max_steps;

        let reward = if self.done { 0.0 } else { 1.0 };

        info!(
            step = %self.steps,
            action = %action,
            reward = %reward,
            done = %self.done,
            "CartPole step"
        );

        StepResult {
            next_state: Array1::from(self.state.to_vec()),
            reward,
            done: self.done,
            info: StepInfo::default(),
        }
    }

    fn is_done(&self) -> bool {
        self.done
    }

    fn action_space_size(&self) -> usize {
        2
    }

    fn observation_space_dim(&self) -> usize {
        4
    }
}
```

---

## 7. OTLP可观测性

### 7.1 训练追踪

```rust
// src/observability/tracing.rs
use opentelemetry::trace::Span;
use tracing::{info, instrument};

#[instrument(
    skip(agent, env),
    fields(
        otel.kind = "internal",
        rl.algorithm = "ppo",
        rl.episode,
        rl.total_reward,
        rl.episode_length,
    )
)]
pub async fn train_episode<E, A>(
    agent: &mut A,
    env: &mut E,
    episode: usize,
) -> Result<EpisodeMetrics>
where
    E: Environment,
    A: RLAgent,
{
    let span = tracing::Span::current();
    span.record("rl.episode", episode);

    let mut state = env.reset();
    let mut total_reward = 0.0;
    let mut steps = 0;

    while !env.is_done() {
        let action = agent.select_action(&state);
        let result = env.step(&action);

        agent.update(&state, &action, result.reward, &result.next_state, result.done);

        state = result.next_state;
        total_reward += result.reward;
        steps += 1;
    }

    span.record("rl.total_reward", total_reward);
    span.record("rl.episode_length", steps);

    info!(
        episode = %episode,
        total_reward = %total_reward,
        steps = %steps,
        "Episode completed"
    );

    Ok(EpisodeMetrics {
        episode,
        total_reward,
        episode_length: steps,
    })
}

pub struct EpisodeMetrics {
    pub episode: usize,
    pub total_reward: f32,
    pub episode_length: usize,
}
```

### 7.2 性能指标

```rust
// RL训练指标
rl_episode_reward{algorithm="ppo",env="cartpole"} 195.5
rl_episode_length{algorithm="ppo",env="cartpole"} 195
rl_policy_loss{algorithm="ppo"} 0.023
rl_value_loss{algorithm="ppo"} 0.156
rl_entropy{algorithm="ppo"} 0.693
rl_learning_rate{algorithm="ppo"} 0.0003
rl_epsilon{algorithm="q_learning"} 0.15

# RLHF指标
rlhf_reward_model_score{model="llama2-7b"} 0.78
rlhf_kl_divergence{model="llama2-7b"} 0.012
rlhf_ppo_objective{model="llama2-7b"} 0.045
```

---

## 8. 生产实践

### 8.1 分布式训练

```rust
// src/distributed/parallel_env.rs
use tokio::task::JoinHandle;
use tracing::{info, instrument};

/// 并行环境管理器
pub struct ParallelEnvRunner<E> {
    envs: Vec<E>,
    num_workers: usize,
}

impl<E: Environment + Send + 'static> ParallelEnvRunner<E> {
    pub fn new(envs: Vec<E>) -> Self {
        let num_workers = envs.len();
        Self { envs, num_workers }
    }

    /// 并行收集rollout
    #[instrument(skip(self, agent))]
    pub async fn collect_rollouts<A>(
        &mut self,
        agent: &A,
        steps_per_env: usize,
    ) -> Vec<RolloutBuffer>
    where
        A: RLAgent + Clone + Send + 'static,
    {
        info!(
            num_workers = %self.num_workers,
            steps_per_env = %steps_per_env,
            "Collecting parallel rollouts"
        );

        let mut handles: Vec<JoinHandle<RolloutBuffer>> = Vec::new();

        for mut env in self.envs.drain(..) {
            let agent_clone = agent.clone();

            let handle = tokio::spawn(async move {
                let mut buffer = RolloutBuffer::new();
                let mut state = env.reset();

                for _ in 0..steps_per_env {
                    let action = agent_clone.select_action(&state);
                    let result = env.step(&action);

                    buffer.add(
                        state.to_vec(),
                        action,
                        result.reward,
                    );

                    state = result.next_state;

                    if result.done {
                        state = env.reset();
                    }
                }

                buffer
            });

            handles.push(handle);
        }

        // 等待所有worker完成
        let mut buffers = Vec::new();
        for handle in handles {
            buffers.push(handle.await.unwrap());
        }

        info!(total_samples = %buffers.iter().map(|b| b.size()).sum::<usize>(), "Rollouts collected");

        buffers
    }
}
```

### 8.2 模型部署

```yaml
# k8s/rl-deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: rl-agent
spec:
  replicas: 1
  selector:
    matchLabels:
      app: rl-agent
  template:
    metadata:
      labels:
        app: rl-agent
    spec:
      containers:
      - name: agent
        image: rl-agent:latest
        resources:
          limits:
            memory: 8Gi
            cpu: 4
          requests:
            memory: 4Gi
            cpu: 2
        env:
        - name: RUST_LOG
          value: info
        - name: OTEL_EXPORTER_OTLP_ENDPOINT
          value: http://otel-collector:4317
```

---

## 9. 参考资源

### 学术论文

- **Q-Learning**: "Learning from Delayed Rewards" (Watkins, 1989)
- **DQN**: "Human-level control through deep RL" (Mnih et al., 2015)
- **PPO**: "Proximal Policy Optimization" (Schulman et al., 2017)
- **RLHF**: "Training language models to follow instructions" (Ouyang et al., 2022)

### Rust生态

- **ndarray**: [https://docs.rs/ndarray](https://docs.rs/ndarray)
- **candle-core**: [https://github.com/huggingface/candle](https://github.com/huggingface/candle)
- **burn**: [https://github.com/tracel-ai/burn](https://github.com/tracel-ai/burn)

### 经典书籍

- **Sutton & Barto**: "Reinforcement Learning: An Introduction" (2nd Edition, 2018)
- **Spinning Up in Deep RL**: OpenAI教程

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-13  
**Rust版本**: 1.90+  
**OpenTelemetry**: 0.27+  
**作者**: OTLP Rust 项目组
