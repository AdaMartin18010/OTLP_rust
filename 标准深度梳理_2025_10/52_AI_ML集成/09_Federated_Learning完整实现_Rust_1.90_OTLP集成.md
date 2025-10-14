# Federated Learning 完整实现 - Rust 1.90 + OTLP 集成

## 目录

- [Federated Learning 完整实现 - Rust 1.90 + OTLP 集成](#federated-learning-完整实现---rust-190--otlp-集成)
  - [目录](#目录)
  - [1. 核心概念与理论](#1-核心概念与理论)
    - [1.1 联邦学习基础](#11-联邦学习基础)
    - [1.2 联邦学习 vs 集中式学习](#12-联邦学习-vs-集中式学习)
    - [1.3 挑战与解决方案](#13-挑战与解决方案)
  - [2. FedAvg算法](#2-fedavg算法)
    - [2.1 基础FedAvg实现](#21-基础fedavg实现)
    - [2.2 异步FedAvg](#22-异步fedavg)
  - [3. 差分隐私](#3-差分隐私)
    - [3.1 高斯噪声机制](#31-高斯噪声机制)
  - [4. 安全聚合](#4-安全聚合)
    - [4.1 安全多方计算](#41-安全多方计算)
  - [5. 联邦优化](#5-联邦优化)
    - [5.1 FedProx算法](#51-fedprox算法)
  - [6. 系统架构](#6-系统架构)
    - [6.1 联邦学习框架](#61-联邦学习框架)
  - [7. OTLP可观测性](#7-otlp可观测性)
    - [7.1 联邦学习追踪](#71-联邦学习追踪)
    - [7.2 性能指标](#72-性能指标)
  - [8. 生产实践](#8-生产实践)
    - [8.1 分布式部署](#81-分布式部署)
  - [9. 参考资源](#9-参考资源)
    - [学术论文](#学术论文)
    - [Rust生态](#rust生态)

---

## 1. 核心概念与理论

### 1.1 联邦学习基础

**核心思想**: 在保护数据隐私的前提下,让多个客户端协作训练机器学习模型。

```text
┌────────────────────────────────────────────────────────────┐
│                Federated Learning Architecture             │
│                                                            │
│  ┌─────────────┐    ┌─────────────┐    ┌─────────────┐     │
│  │   Client 1  │    │   Client 2  │    │   Client N  │     │
│  │             │    │             │    │             │     │
│  │ Local Data  │    │ Local Data  │    │ Local Data  │     │
│  │ Local Train │    │ Local Train │    │ Local Train │    │
│  │             │    │             │    │             │    │
│  └──────┬──────┘    └──────┬──────┘    └──────┬──────┘    │
│         │                  │                  │           │
│         │ Gradients        │ Gradients        │ Gradients │
│         │                  │                  │           │
│         └──────────────────┼──────────────────┘           │
│                            │                              │
│                            ▼                              │
│                    ┌─────────────┐                        │
│                    │   Server    │                        │
│                    │             │                        │
│                    │ Aggregation │                        │
│                    │             │                        │
│                    └──────┬──────┘                        │
│                           │                               │
│                           │ Global Model                  │
│                           │                               │
│                    ┌──────▼──────┐                        │
│                    │ Broadcast   │                        │
│                    └─────────────┘                        │
└────────────────────────────────────────────────────────────┘
```

### 1.2 联邦学习 vs 集中式学习

| 维度 | 联邦学习 | 集中式学习 |
|------|----------|------------|
| **数据隐私** | ✅ 数据不出本地 | ❌ 数据集中存储 |
| **通信开销** | ⚠️ 需要网络传输 | ✅ 无网络开销 |
| **计算分布** | ✅ 分布式计算 | ❌ 集中式计算 |
| **数据异构性** | ⚠️ 需要处理Non-IID | ✅ 数据同质 |
| **系统复杂性** | ⚠️ 复杂协调 | ✅ 简单直接 |
| **适用场景** | 跨组织协作 | 单一组织 |

### 1.3 挑战与解决方案

| 挑战 | 解决方案 |
|------|----------|
| **数据异构性 (Non-IID)** | FedProx, SCAFFOLD |
| **通信效率** | 梯度压缩, 异步更新 |
| **隐私保护** | 差分隐私, 安全聚合 |
| **系统异构性** | 异步联邦学习 |
| **恶意攻击** | 拜占庭容错, 安全聚合 |

---

## 2. FedAvg算法

### 2.1 基础FedAvg实现

```rust
// src/fl/fedavg.rs
use ndarray::Array2;
use tracing::{info, instrument};
use std::collections::HashMap;

/// FedAvg服务器
pub struct FedAvgServer {
    global_model: Array2<f32>,
    client_weights: HashMap<String, Array2<f32>>,
    learning_rate: f32,
    num_rounds: usize,
}

impl FedAvgServer {
    pub fn new(global_model: Array2<f32>, learning_rate: f32) -> Self {
        Self {
            global_model,
            client_weights: HashMap::new(),
            learning_rate,
            num_rounds: 0,
        }
    }

    /// 联邦平均聚合
    #[instrument(skip(self, client_updates))]
    pub fn aggregate(&mut self, client_updates: Vec<ClientUpdate>) -> Array2<f32> {
        info!(
            num_clients = %client_updates.len(),
            round = %self.num_rounds,
            "Starting FedAvg aggregation"
        );

        let mut aggregated_weights = Array2::zeros(self.global_model.raw_dim());
        let mut total_samples = 0;

        // 计算总样本数
        for update in &client_updates {
            total_samples += update.num_samples;
        }

        // 加权平均
        for update in client_updates {
            let weight = update.num_samples as f32 / total_samples as f32;
            let weighted_update = &update.model_weights * weight;
            aggregated_weights = &aggregated_weights + &weighted_update;

            info!(
                client_id = %update.client_id,
                num_samples = %update.num_samples,
                weight = %weight,
                "Client update processed"
            );
        }

        // 更新全局模型
        self.global_model = &self.global_model + &aggregated_weights;
        self.num_rounds += 1;

        info!(
            round = %self.num_rounds,
            total_samples = %total_samples,
            "FedAvg aggregation completed"
        );

        self.global_model.clone()
    }

    /// 获取全局模型
    pub fn get_global_model(&self) -> &Array2<f32> {
        &self.global_model
    }
}

/// 客户端更新
#[derive(Debug, Clone)]
pub struct ClientUpdate {
    pub client_id: String,
    pub model_weights: Array2<f32>,
    pub num_samples: usize,
    pub loss: f32,
}

/// FedAvg客户端
pub struct FedAvgClient {
    client_id: String,
    local_model: Array2<f32>,
    local_data: Vec<Array2<f32>>,
    learning_rate: f32,
    epochs: usize,
}

impl FedAvgClient {
    pub fn new(
        client_id: String,
        initial_model: Array2<f32>,
        local_data: Vec<Array2<f32>>,
        learning_rate: f32,
    ) -> Self {
        Self {
            client_id,
            local_model: initial_model,
            local_data,
            learning_rate,
            epochs: 5,
        }
    }

    /// 本地训练
    #[instrument(skip(self))]
    pub fn local_train(&mut self, global_model: &Array2<f32>) -> ClientUpdate {
        info!(
            client_id = %self.client_id,
            data_size = %self.local_data.len(),
            epochs = %self.epochs,
            "Starting local training"
        );

        // 初始化本地模型为全局模型
        self.local_model = global_model.clone();

        let mut total_loss = 0.0;

        // 本地训练循环
        for epoch in 0..self.epochs {
            let epoch_loss = self.train_epoch();
            total_loss += epoch_loss;

            info!(
                client_id = %self.client_id,
                epoch = %epoch,
                loss = %epoch_loss,
                "Local training epoch completed"
            );
        }

        let avg_loss = total_loss / self.epochs as f32;

        // 计算模型更新 (梯度)
        let model_update = &self.local_model - global_model;

        info!(
            client_id = %self.client_id,
            avg_loss = %avg_loss,
            "Local training completed"
        );

        ClientUpdate {
            client_id: self.client_id.clone(),
            model_weights: model_update,
            num_samples: self.local_data.len(),
            loss: avg_loss,
        }
    }

    /// 单轮训练
    fn train_epoch(&mut self) -> f32 {
        let mut epoch_loss = 0.0;

        for batch in &self.local_data {
            // 简化: 随机梯度下降
            let loss = self.compute_loss(batch);
            epoch_loss += loss;

            // 更新模型参数
            self.update_parameters(batch);
        }

        epoch_loss / self.local_data.len() as f32
    }

    /// 计算损失 (简化)
    fn compute_loss(&self, batch: &Array2<f32>) -> f32 {
        // 简化损失计算
        0.5
    }

    /// 更新参数 (简化)
    fn update_parameters(&mut self, batch: &Array2<f32>) {
        // 简化参数更新
    }
}
```

### 2.2 异步FedAvg

```rust
// src/fl/async_fedavg.rs
use tokio::sync::mpsc;
use tracing::{info, instrument};

/// 异步FedAvg服务器
pub struct AsyncFedAvgServer {
    global_model: Array2<f32>,
    update_channel: mpsc::UnboundedReceiver<ClientUpdate>,
    broadcast_channel: mpsc::UnboundedSender<Array2<f32>>,
    staleness_threshold: usize,
}

impl AsyncFedAvgServer {
    pub fn new(
        global_model: Array2<f32>,
        staleness_threshold: usize,
    ) -> (
        Self,
        mpsc::UnboundedSender<ClientUpdate>,
        mpsc::UnboundedReceiver<Array2<f32>>,
    ) {
        let (update_tx, update_rx) = mpsc::unbounded_channel();
        let (broadcast_tx, broadcast_rx) = mpsc::unbounded_channel();

        let server = Self {
            global_model,
            update_channel: update_rx,
            broadcast_channel: broadcast_tx,
            staleness_threshold,
        };

        (server, update_tx, broadcast_rx)
    }

    /// 异步聚合循环
    #[instrument(skip(self))]
    pub async fn run_async_aggregation(&mut self) {
        info!("Starting async FedAvg server");

        while let Some(update) = self.update_channel.recv().await {
            // 检查更新延迟
            if update.round_age > self.staleness_threshold {
                info!(
                    client_id = %update.client_id,
                    round_age = %update.round_age,
                    "Skipping stale update"
                );
                continue;
            }

            // 异步更新全局模型
            self.async_update_global_model(update).await;
        }
    }

    /// 异步更新全局模型
    async fn async_update_global_model(&mut self, update: ClientUpdate) {
        info!(
            client_id = %update.client_id,
            round_age = %update.round_age,
            "Processing async update"
        );

        // 简化的异步聚合
        let weight = 1.0 / (update.round_age + 1) as f32;
        let weighted_update = &update.model_weights * weight;
        self.global_model = &self.global_model + &weighted_update;

        // 广播更新后的模型
        if let Err(e) = self.broadcast_channel.send(self.global_model.clone()) {
            info!(error = %e, "Failed to broadcast model update");
        }
    }
}

/// 带延迟信息的客户端更新
#[derive(Debug, Clone)]
pub struct AsyncClientUpdate {
    pub client_id: String,
    pub model_weights: Array2<f32>,
    pub num_samples: usize,
    pub loss: f32,
    pub round_age: usize, // 更新延迟
}
```

---

## 3. 差分隐私

### 3.1 高斯噪声机制

```rust
// src/fl/differential_privacy.rs
use rand::distributions::{Distribution, Normal};
use tracing::{info, instrument};

/// 差分隐私参数
#[derive(Debug, Clone)]
pub struct DPParams {
    pub epsilon: f64,    // 隐私预算
    pub delta: f64,      // 失败概率
    pub sensitivity: f64, // 敏感度
}

/// 高斯噪声机制
pub struct GaussianMechanism {
    params: DPParams,
    normal_dist: Normal<f64>,
}

impl GaussianMechanism {
    pub fn new(params: DPParams) -> Self {
        // 计算噪声标准差
        let sigma = Self::compute_sigma(params.epsilon, params.delta, params.sensitivity);
        let normal_dist = Normal::new(0.0, sigma);

        Self {
            params,
            normal_dist,
        }
    }

    /// 计算噪声标准差
    fn compute_sigma(epsilon: f64, delta: f64, sensitivity: f64) -> f64 {
        // σ = sensitivity * sqrt(2 * ln(1.25/δ)) / ε
        let c = (1.25 / delta).ln() * 2.0;
        sensitivity * c.sqrt() / epsilon
    }

    /// 添加噪声到梯度
    #[instrument(skip(self, gradients))]
    pub fn add_noise(&self, gradients: &mut Array2<f32>) {
        let mut rng = rand::thread_rng();

        info!(
            epsilon = %self.params.epsilon,
            delta = %self.params.delta,
            sensitivity = %self.params.sensitivity,
            "Adding Gaussian noise to gradients"
        );

        // 为每个梯度参数添加噪声
        for elem in gradients.iter_mut() {
            let noise = self.normal_dist.sample(&mut rng) as f32;
            *elem += noise;
        }
    }

    /// 计算隐私预算消耗
    pub fn compute_privacy_cost(&self, num_rounds: usize) -> f64 {
        // 组合定理: 多轮训练的隐私预算
        self.params.epsilon * (num_rounds as f64).sqrt()
    }
}

/// 差分隐私FedAvg
pub struct DPFedAvg {
    fedavg_server: FedAvgServer,
    dp_mechanism: GaussianMechanism,
    privacy_budget: f64,
    consumed_budget: f64,
}

impl DPFedAvg {
    pub fn new(
        global_model: Array2<f32>,
        learning_rate: f32,
        dp_params: DPParams,
    ) -> Self {
        let fedavg_server = FedAvgServer::new(global_model, learning_rate);
        let dp_mechanism = GaussianMechanism::new(dp_params.clone());

        Self {
            fedavg_server,
            dp_mechanism,
            privacy_budget: dp_params.epsilon,
            consumed_budget: 0.0,
        }
    }

    /// 差分隐私聚合
    #[instrument(skip(self, client_updates))]
    pub fn dp_aggregate(&mut self, client_updates: Vec<ClientUpdate>) -> Array2<f32> {
        info!(
            privacy_budget = %self.privacy_budget,
            consumed_budget = %self.consumed_budget,
            "Starting DP-FedAvg aggregation"
        );

        // 检查隐私预算
        if self.consumed_budget >= self.privacy_budget {
            info!("Privacy budget exhausted");
            return self.fedavg_server.get_global_model().clone();
        }

        // 为每个客户端更新添加噪声
        let mut noisy_updates = Vec::new();
        for mut update in client_updates {
            self.dp_mechanism.add_noise(&mut update.model_weights);
            noisy_updates.push(update);
        }

        // 执行FedAvg聚合
        let global_model = self.fedavg_server.aggregate(noisy_updates);

        // 更新隐私预算消耗
        self.consumed_budget += self.dp_mechanism.params.epsilon;

        info!(
            consumed_budget = %self.consumed_budget,
            remaining_budget = %(self.privacy_budget - self.consumed_budget),
            "DP-FedAvg aggregation completed"
        );

        global_model
    }
}
```

---

## 4. 安全聚合

### 4.1 安全多方计算

```rust
// src/fl/secure_aggregation.rs
use tracing::{info, instrument};

/// 安全聚合服务器
pub struct SecureAggregationServer {
    global_model: Array2<f32>,
    client_secrets: HashMap<String, SecretShare>,
    threshold: usize,
}

/// 秘密分享
#[derive(Debug, Clone)]
pub struct SecretShare {
    pub client_id: String,
    pub share: Array2<f32>,
    pub commitment: Vec<u8>, // 承诺值
}

impl SecureAggregationServer {
    pub fn new(global_model: Array2<f32>, threshold: usize) -> Self {
        Self {
            global_model,
            client_secrets: HashMap::new(),
            threshold,
        }
    }

    /// 安全聚合
    #[instrument(skip(self, client_shares))]
    pub fn secure_aggregate(&mut self, client_shares: Vec<SecretShare>) -> Array2<f32> {
        info!(
            num_clients = %client_shares.len(),
            threshold = %self.threshold,
            "Starting secure aggregation"
        );

        // 验证承诺
        for share in &client_shares {
            if !self.verify_commitment(share) {
                info!(
                    client_id = %share.client_id,
                    "Invalid commitment, skipping client"
                );
                continue;
            }
        }

        // 秘密重构
        let aggregated_share = self.reconstruct_secret(client_shares);

        // 更新全局模型
        self.global_model = &self.global_model + &aggregated_share;

        info!("Secure aggregation completed");

        self.global_model.clone()
    }

    /// 验证承诺
    fn verify_commitment(&self, share: &SecretShare) -> bool {
        // 简化: 总是返回true
        true
    }

    /// 秘密重构
    fn reconstruct_secret(&self, shares: Vec<SecretShare>) -> Array2<f32> {
        // 简化: 直接求和
        let mut result = Array2::zeros(self.global_model.raw_dim());
        for share in shares {
            result = &result + &share.share;
        }
        result
    }
}
```

---

## 5. 联邦优化

### 5.1 FedProx算法

```rust
// src/fl/fedprox.rs
use tracing::{info, instrument};

/// FedProx客户端
pub struct FedProxClient {
    client_id: String,
    local_model: Array2<f32>,
    local_data: Vec<Array2<f32>>,
    learning_rate: f32,
    mu: f32, // 近端项系数
    epochs: usize,
}

impl FedProxClient {
    pub fn new(
        client_id: String,
        initial_model: Array2<f32>,
        local_data: Vec<Array2<f32>>,
        learning_rate: f32,
        mu: f32,
    ) -> Self {
        Self {
            client_id,
            local_model: initial_model,
            local_data,
            learning_rate,
            mu,
            epochs: 5,
        }
    }

    /// FedProx本地训练
    #[instrument(skip(self))]
    pub fn fedprox_train(&mut self, global_model: &Array2<f32>) -> ClientUpdate {
        info!(
            client_id = %self.client_id,
            mu = %self.mu,
            "Starting FedProx local training"
        );

        // 初始化本地模型
        self.local_model = global_model.clone();

        let mut total_loss = 0.0;

        for epoch in 0..self.epochs {
            let epoch_loss = self.fedprox_epoch(global_model);
            total_loss += epoch_loss;

            info!(
                client_id = %self.client_id,
                epoch = %epoch,
                loss = %epoch_loss,
                "FedProx epoch completed"
            );
        }

        let avg_loss = total_loss / self.epochs as f32;
        let model_update = &self.local_model - global_model;

        ClientUpdate {
            client_id: self.client_id.clone(),
            model_weights: model_update,
            num_samples: self.local_data.len(),
            loss: avg_loss,
        }
    }

    /// FedProx单轮训练
    fn fedprox_epoch(&mut self, global_model: &Array2<f32>) -> f32 {
        let mut epoch_loss = 0.0;

        for batch in &self.local_data {
            // 计算FedProx损失
            let loss = self.compute_fedprox_loss(batch, global_model);
            epoch_loss += loss;

            // 更新参数
            self.fedprox_update(batch, global_model);
        }

        epoch_loss / self.local_data.len() as f32
    }

    /// 计算FedProx损失
    fn compute_fedprox_loss(&self, batch: &Array2<f32>, global_model: &Array2<f32>) -> f32 {
        // 标准损失 + 近端项
        let standard_loss = self.compute_standard_loss(batch);
        let proximal_term = self.mu * self.compute_proximal_term(global_model);
        standard_loss + proximal_term
    }

    /// 计算近端项
    fn compute_proximal_term(&self, global_model: &Array2<f32>) -> f32 {
        let diff = &self.local_model - global_model;
        diff.mapv(|x| x * x).sum() * 0.5
    }

    /// 计算标准损失
    fn compute_standard_loss(&self, batch: &Array2<f32>) -> f32 {
        0.5 // 简化
    }

    /// FedProx参数更新
    fn fedprox_update(&mut self, batch: &Array2<f32>, global_model: &Array2<f32>) {
        // 简化更新
    }
}
```

---

## 6. 系统架构

### 6.1 联邦学习框架

```rust
// src/fl/framework.rs
use tokio::sync::mpsc;
use tracing::{info, instrument};

/// 联邦学习框架
pub struct FLFramework {
    server: Box<dyn FLServer>,
    clients: Vec<Box<dyn FLClient>>,
    config: FLConfig,
}

/// 联邦学习配置
#[derive(Debug, Clone)]
pub struct FLConfig {
    pub num_rounds: usize,
    pub clients_per_round: usize,
    pub local_epochs: usize,
    pub learning_rate: f32,
    pub dp_params: Option<DPParams>,
    pub secure_aggregation: bool,
}

/// 联邦学习服务器trait
pub trait FLServer: Send + Sync {
    fn aggregate(&mut self, updates: Vec<ClientUpdate>) -> Array2<f32>;
    fn get_global_model(&self) -> &Array2<f32>;
    fn broadcast_model(&self, model: Array2<f32>);
}

/// 联邦学习客户端trait
pub trait FLClient: Send + Sync {
    fn get_client_id(&self) -> &str;
    fn local_train(&mut self, global_model: &Array2<f32>) -> ClientUpdate;
    fn receive_model(&mut self, model: Array2<f32>);
}

impl FLFramework {
    pub fn new(
        server: Box<dyn FLServer>,
        clients: Vec<Box<dyn FLClient>>,
        config: FLConfig,
    ) -> Self {
        Self {
            server,
            clients,
            config,
        }
    }

    /// 运行联邦学习
    #[instrument(skip(self))]
    pub async fn run(&mut self) -> Array2<f32> {
        info!(
            num_rounds = %self.config.num_rounds,
            clients_per_round = %self.config.clients_per_round,
            "Starting federated learning"
        );

        for round in 0..self.config.num_rounds {
            info!(round = %round, "Starting FL round");

            // 选择参与客户端
            let selected_clients = self.select_clients();

            // 广播全局模型
            let global_model = self.server.get_global_model().clone();
            for client in &mut selected_clients {
                client.receive_model(global_model.clone());
            }

            // 本地训练
            let mut updates = Vec::new();
            for client in &mut selected_clients {
                let update = client.local_train(&global_model);
                updates.push(update);
            }

            // 聚合更新
            let new_global_model = self.server.aggregate(updates);
            self.server.broadcast_model(new_global_model);

            info!(round = %round, "FL round completed");
        }

        info!("Federated learning completed");
        self.server.get_global_model().clone()
    }

    /// 选择参与客户端
    fn select_clients(&self) -> Vec<&mut Box<dyn FLClient>> {
        // 简化: 返回前N个客户端
        self.clients.iter_mut().take(self.config.clients_per_round).collect()
    }
}
```

---

## 7. OTLP可观测性

### 7.1 联邦学习追踪

```rust
// src/fl/observability.rs
use opentelemetry::trace::Span;
use tracing::{info, instrument};

#[instrument(
    skip(framework),
    fields(
        otel.kind = "internal",
        fl.num_rounds,
        fl.clients_per_round,
        fl.convergence_metric,
    )
)]
pub async fn run_fl_with_observability(
    framework: &mut FLFramework,
) -> Result<Array2<f32>> {
    let span = tracing::Span::current();
    span.record("fl.num_rounds", framework.config.num_rounds as i64);
    span.record("fl.clients_per_round", framework.config.clients_per_round as i64);

    let global_model = framework.run().await;

    // 记录收敛指标
    let convergence_metric = compute_convergence_metric(&global_model);
    span.record("fl.convergence_metric", convergence_metric);

    info!(
        convergence_metric = %convergence_metric,
        "FL training completed with observability"
    );

    Ok(global_model)
}

fn compute_convergence_metric(model: &Array2<f32>) -> f64 {
    // 简化: 计算模型参数的L2范数
    model.mapv(|x| x as f64 * x as f64).sum().sqrt()
}
```

### 7.2 性能指标

```text
# 联邦学习指标
fl_round_duration{round="1"} 45.2
fl_clients_selected{round="1"} 10
fl_aggregation_time{round="1"} 2.1
fl_communication_overhead{round="1"} 15.6
fl_model_accuracy{round="1"} 0.85
fl_privacy_budget_consumed{epsilon="1.0"} 0.15
fl_secure_aggregation_success_rate 0.98
```

---

## 8. 生产实践

### 8.1 分布式部署

```yaml
# k8s/fl-deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: fl-server
spec:
  replicas: 1
  selector:
    matchLabels:
      app: fl-server
  template:
    metadata:
      labels:
        app: fl-server
    spec:
      containers:
      - name: server
        image: fl-server:latest
        resources:
          limits:
            memory: 4Gi
            cpu: 2
        env:
        - name: RUST_LOG
          value: info
        - name: OTEL_EXPORTER_OTLP_ENDPOINT
          value: http://otel-collector:4317
---
apiVersion: apps/v1
kind: Deployment
metadata:
  name: fl-client
spec:
  replicas: 10
  selector:
    matchLabels:
      app: fl-client
  template:
    metadata:
      labels:
        app: fl-client
    spec:
      containers:
      - name: client
        image: fl-client:latest
        resources:
          limits:
            memory: 2Gi
            cpu: 1
```

---

## 9. 参考资源

### 学术论文

- **FedAvg**: "Communication-Efficient Learning of Deep Networks" (McMahan et al., 2017)
- **FedProx**: "Federated Optimization in Heterogeneous Networks" (Li et al., 2020)
- **差分隐私**: "The Algorithmic Foundations of Differential Privacy" (Dwork & Roth, 2014)

### Rust生态

- **ndarray**: [https://docs.rs/ndarray](https://docs.rs/ndarray)
- **tokio**: [https://docs.rs/tokio](https://docs.rs/tokio)
- **opentelemetry**: [https://docs.rs/opentelemetry](https://docs.rs/opentelemetry)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-13  
**Rust版本**: 1.90+  
**OpenTelemetry**: 0.27+  
**作者**: OTLP Rust 项目组
