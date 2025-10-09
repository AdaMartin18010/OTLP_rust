# 负载均衡与路由算法 - Rust完整实现

> **Rust版本**: 1.90+  
> **核心依赖**: tokio 1.47.1, dashmap 6.1  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月9日

---

## 📋 目录

- [1. 负载均衡概述](#1-负载均衡概述)
- [2. 基础负载均衡算法](#2-基础负载均衡算法)
- [3. 动态负载均衡](#3-动态负载均衡)
- [4. 一致性哈希](#4-一致性哈希)
- [5. 智能路由](#5-智能路由)
- [6. 故障转移](#6-故障转移)
- [7. 完整实现](#7-完整实现)

---

## 1. 负载均衡概述

### 1.1 算法对比

```text
┌──────────────┬────────┬────────┬────────┬──────────┬────────┐
│ 算法          │ 复杂度 │ 公平性 │ 粘性   │ 故障感知 │ 扩展性 │
├──────────────┼────────┼────────┼────────┼──────────┼────────┤
│ 轮询          │ O(1)   │ 高     │ 无     │ 中       │ 优秀   │
│ 加权轮询      │ O(1)   │ 中     │ 无     │ 中       │ 优秀   │
│ 最少连接      │ O(n)   │ 高     │ 无     │ 高       │ 良好   │
│ 随机          │ O(1)   │ 中     │ 无     │ 低       │ 优秀   │
│ 一致性哈希    │ O(logn)│ 中     │ 高     │ 中       │ 优秀   │
│ 最小延迟      │ O(n)   │ 中     │ 无     │ 很高     │ 良好   │
│ P2C          │ O(1)   │ 高     │ 无     │ 高       │ 优秀   │
└──────────────┴────────┴────────┴────────┴──────────┴────────┘
```

### 1.2 负载均衡器trait

```rust
use std::sync::Arc;
use tokio::sync::RwLock;
use std::collections::HashMap;
use dashmap::DashMap;

/// 后端服务器
#[derive(Debug, Clone)]
pub struct Backend {
    pub id: String,
    pub address: String,
    pub weight: u32,
    pub active_connections: Arc<AtomicUsize>,
    pub total_requests: Arc<AtomicU64>,
    pub failed_requests: Arc<AtomicU64>,
    pub avg_latency_ms: Arc<AtomicU64>,
    pub health: Arc<RwLock<HealthState>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HealthState {
    Healthy,
    Degraded,
    Unhealthy,
}

impl Backend {
    pub fn new(id: String, address: String, weight: u32) -> Self {
        Self {
            id,
            address,
            weight,
            active_connections: Arc::new(AtomicUsize::new(0)),
            total_requests: Arc::new(AtomicU64::new(0)),
            failed_requests: Arc::new(AtomicU64::new(0)),
            avg_latency_ms: Arc::new(AtomicU64::new(0)),
            health: Arc::new(RwLock::new(HealthState::Healthy)),
        }
    }
    
    pub async fn is_healthy(&self) -> bool {
        matches!(*self.health.read().await, HealthState::Healthy)
    }
    
    pub fn connection_count(&self) -> usize {
        self.active_connections.load(Ordering::Relaxed)
    }
    
    pub fn error_rate(&self) -> f64 {
        let total = self.total_requests.load(Ordering::Relaxed);
        if total == 0 {
            return 0.0;
        }
        let failed = self.failed_requests.load(Ordering::Relaxed);
        failed as f64 / total as f64
    }
}

/// 负载均衡器trait
#[async_trait::async_trait]
pub trait LoadBalancer: Send + Sync {
    /// 选择后端
    async fn select(&self, request: &Request) -> Option<Backend>;
    
    /// 更新后端列表
    async fn update_backends(&self, backends: Vec<Backend>);
    
    /// 记录请求结果
    async fn record_result(&self, backend_id: &str, success: bool, latency_ms: u64);
    
    /// 算法名称
    fn name(&self) -> &str;
}

/// 请求上下文
#[derive(Debug, Clone)]
pub struct Request {
    pub id: String,
    pub client_id: Option<String>,
    pub route_key: Option<String>,
    pub priority: Priority,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Priority {
    High = 2,
    Normal = 1,
    Low = 0,
}

use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use serde::{Serialize, Deserialize};
```

---

## 2. 基础负载均衡算法

### 2.1 轮询(Round Robin)

```rust
/// 轮询负载均衡器
pub struct RoundRobinBalancer {
    backends: Arc<RwLock<Vec<Backend>>>,
    counter: Arc<AtomicUsize>,
}

impl RoundRobinBalancer {
    pub fn new(backends: Vec<Backend>) -> Self {
        Self {
            backends: Arc::new(RwLock::new(backends)),
            counter: Arc::new(AtomicUsize::new(0)),
        }
    }
}

#[async_trait::async_trait]
impl LoadBalancer for RoundRobinBalancer {
    async fn select(&self, _request: &Request) -> Option<Backend> {
        let backends = self.backends.read().await;
        
        if backends.is_empty() {
            return None;
        }
        
        // 只选择健康的后端
        let healthy: Vec<&Backend> = backends.iter()
            .filter(|b| matches!(*b.health.blocking_read(), HealthState::Healthy))
            .collect();
        
        if healthy.is_empty() {
            return None;
        }
        
        let idx = self.counter.fetch_add(1, Ordering::Relaxed) % healthy.len();
        Some(healthy[idx].clone())
    }
    
    async fn update_backends(&self, backends: Vec<Backend>) {
        let mut b = self.backends.write().await;
        *b = backends;
    }
    
    async fn record_result(&self, backend_id: &str, success: bool, latency_ms: u64) {
        let backends = self.backends.read().await;
        
        if let Some(backend) = backends.iter().find(|b| b.id == backend_id) {
            backend.total_requests.fetch_add(1, Ordering::Relaxed);
            
            if !success {
                backend.failed_requests.fetch_add(1, Ordering::Relaxed);
            }
            
            // 更新平均延迟 (简化的EMA)
            let current_avg = backend.avg_latency_ms.load(Ordering::Relaxed);
            let new_avg = if current_avg == 0 {
                latency_ms
            } else {
                (current_avg * 9 + latency_ms) / 10
            };
            backend.avg_latency_ms.store(new_avg, Ordering::Relaxed);
        }
    }
    
    fn name(&self) -> &str {
        "RoundRobin"
    }
}
```

### 2.2 加权轮询(Weighted Round Robin)

```rust
/// 加权轮询负载均衡器
pub struct WeightedRoundRobinBalancer {
    backends: Arc<RwLock<Vec<Backend>>>,
    current_weights: Arc<RwLock<Vec<i64>>>,
}

impl WeightedRoundRobinBalancer {
    pub fn new(backends: Vec<Backend>) -> Self {
        let weights = vec![0i64; backends.len()];
        
        Self {
            backends: Arc::new(RwLock::new(backends)),
            current_weights: Arc::new(RwLock::new(weights)),
        }
    }
    
    /// Smooth Weighted Round Robin算法
    async fn select_smooth(&self) -> Option<Backend> {
        let backends = self.backends.read().await;
        let mut weights = self.current_weights.write().await;
        
        if backends.is_empty() {
            return None;
        }
        
        // 确保weights和backends长度一致
        if weights.len() != backends.len() {
            *weights = vec![0i64; backends.len()];
        }
        
        // 计算总权重
        let total_weight: i64 = backends.iter()
            .filter(|b| matches!(*b.health.blocking_read(), HealthState::Healthy))
            .map(|b| b.weight as i64)
            .sum();
        
        if total_weight == 0 {
            return None;
        }
        
        // 更新当前权重并选择最大权重的后端
        let mut max_idx = 0;
        let mut max_weight = i64::MIN;
        
        for (idx, backend) in backends.iter().enumerate() {
            if !matches!(*backend.health.blocking_read(), HealthState::Healthy) {
                continue;
            }
            
            weights[idx] += backend.weight as i64;
            
            if weights[idx] > max_weight {
                max_weight = weights[idx];
                max_idx = idx;
            }
        }
        
        // 减少选中后端的当前权重
        weights[max_idx] -= total_weight;
        
        Some(backends[max_idx].clone())
    }
}

#[async_trait::async_trait]
impl LoadBalancer for WeightedRoundRobinBalancer {
    async fn select(&self, _request: &Request) -> Option<Backend> {
        self.select_smooth().await
    }
    
    async fn update_backends(&self, backends: Vec<Backend>) {
        let mut b = self.backends.write().await;
        let mut w = self.current_weights.write().await;
        
        *w = vec![0i64; backends.len()];
        *b = backends;
    }
    
    async fn record_result(&self, backend_id: &str, success: bool, latency_ms: u64) {
        let backends = self.backends.read().await;
        
        if let Some(backend) = backends.iter().find(|b| b.id == backend_id) {
            backend.total_requests.fetch_add(1, Ordering::Relaxed);
            
            if !success {
                backend.failed_requests.fetch_add(1, Ordering::Relaxed);
            }
            
            let current_avg = backend.avg_latency_ms.load(Ordering::Relaxed);
            let new_avg = if current_avg == 0 {
                latency_ms
            } else {
                (current_avg * 9 + latency_ms) / 10
            };
            backend.avg_latency_ms.store(new_avg, Ordering::Relaxed);
        }
    }
    
    fn name(&self) -> &str {
        "WeightedRoundRobin"
    }
}
```

### 2.3 最少连接(Least Connections)

```rust
/// 最少连接负载均衡器
pub struct LeastConnectionsBalancer {
    backends: Arc<RwLock<Vec<Backend>>>,
}

impl LeastConnectionsBalancer {
    pub fn new(backends: Vec<Backend>) -> Self {
        Self {
            backends: Arc::new(RwLock::new(backends)),
        }
    }
}

#[async_trait::async_trait]
impl LoadBalancer for LeastConnectionsBalancer {
    async fn select(&self, _request: &Request) -> Option<Backend> {
        let backends = self.backends.read().await;
        
        backends.iter()
            .filter(|b| matches!(*b.health.blocking_read(), HealthState::Healthy))
            .min_by_key(|b| b.connection_count())
            .cloned()
    }
    
    async fn update_backends(&self, backends: Vec<Backend>) {
        let mut b = self.backends.write().await;
        *b = backends;
    }
    
    async fn record_result(&self, backend_id: &str, success: bool, latency_ms: u64) {
        let backends = self.backends.read().await;
        
        if let Some(backend) = backends.iter().find(|b| b.id == backend_id) {
            backend.total_requests.fetch_add(1, Ordering::Relaxed);
            
            if !success {
                backend.failed_requests.fetch_add(1, Ordering::Relaxed);
            }
            
            let current_avg = backend.avg_latency_ms.load(Ordering::Relaxed);
            let new_avg = if current_avg == 0 {
                latency_ms
            } else {
                (current_avg * 9 + latency_ms) / 10
            };
            backend.avg_latency_ms.store(new_avg, Ordering::Relaxed);
        }
    }
    
    fn name(&self) -> &str {
        "LeastConnections"
    }
}

/// 连接守卫(自动递增/递减连接数)
pub struct ConnectionGuard {
    backend: Backend,
}

impl ConnectionGuard {
    pub fn new(backend: Backend) -> Self {
        backend.active_connections.fetch_add(1, Ordering::Relaxed);
        Self { backend }
    }
}

impl Drop for ConnectionGuard {
    fn drop(&mut self) {
        self.backend.active_connections.fetch_sub(1, Ordering::Relaxed);
    }
}
```

---

## 3. 动态负载均衡

### 3.1 Power of Two Choices (P2C)

```rust
use rand::Rng;

/// P2C负载均衡器
pub struct P2CBalancer {
    backends: Arc<RwLock<Vec<Backend>>>,
    rng: Arc<Mutex<rand::rngs::ThreadRng>>,
}

impl P2CBalancer {
    pub fn new(backends: Vec<Backend>) -> Self {
        Self {
            backends: Arc::new(RwLock::new(backends)),
            rng: Arc::new(Mutex::new(rand::thread_rng())),
        }
    }
    
    /// 计算后端负载分数(越低越好)
    fn calculate_load(&self, backend: &Backend) -> f64 {
        let connections = backend.connection_count() as f64;
        let latency = backend.avg_latency_ms.load(Ordering::Relaxed) as f64;
        let error_rate = backend.error_rate();
        
        // 综合评分
        connections * 0.4 + latency * 0.4 + error_rate * 1000.0 * 0.2
    }
}

#[async_trait::async_trait]
impl LoadBalancer for P2CBalancer {
    async fn select(&self, _request: &Request) -> Option<Backend> {
        let backends = self.backends.read().await;
        
        let healthy: Vec<&Backend> = backends.iter()
            .filter(|b| matches!(*b.health.blocking_read(), HealthState::Healthy))
            .collect();
        
        if healthy.is_empty() {
            return None;
        }
        
        if healthy.len() == 1 {
            return Some(healthy[0].clone());
        }
        
        // 随机选择两个后端
        let mut rng = self.rng.lock().await;
        let idx1 = rng.gen_range(0..healthy.len());
        let mut idx2 = rng.gen_range(0..healthy.len());
        
        while idx1 == idx2 && healthy.len() > 1 {
            idx2 = rng.gen_range(0..healthy.len());
        }
        
        let load1 = self.calculate_load(healthy[idx1]);
        let load2 = self.calculate_load(healthy[idx2]);
        
        // 选择负载较低的后端
        if load1 <= load2 {
            Some(healthy[idx1].clone())
        } else {
            Some(healthy[idx2].clone())
        }
    }
    
    async fn update_backends(&self, backends: Vec<Backend>) {
        let mut b = self.backends.write().await;
        *b = backends;
    }
    
    async fn record_result(&self, backend_id: &str, success: bool, latency_ms: u64) {
        let backends = self.backends.read().await;
        
        if let Some(backend) = backends.iter().find(|b| b.id == backend_id) {
            backend.total_requests.fetch_add(1, Ordering::Relaxed);
            
            if !success {
                backend.failed_requests.fetch_add(1, Ordering::Relaxed);
            }
            
            let current_avg = backend.avg_latency_ms.load(Ordering::Relaxed);
            let new_avg = if current_avg == 0 {
                latency_ms
            } else {
                (current_avg * 9 + latency_ms) / 10
            };
            backend.avg_latency_ms.store(new_avg, Ordering::Relaxed);
        }
    }
    
    fn name(&self) -> &str {
        "P2C"
    }
}
```

### 3.2 最小延迟(Least Latency)

```rust
/// 最小延迟负载均衡器
pub struct LeastLatencyBalancer {
    backends: Arc<RwLock<Vec<Backend>>>,
}

impl LeastLatencyBalancer {
    pub fn new(backends: Vec<Backend>) -> Self {
        Self {
            backends: Arc::new(RwLock::new(backends)),
        }
    }
}

#[async_trait::async_trait]
impl LoadBalancer for LeastLatencyBalancer {
    async fn select(&self, _request: &Request) -> Option<Backend> {
        let backends = self.backends.read().await;
        
        backends.iter()
            .filter(|b| matches!(*b.health.blocking_read(), HealthState::Healthy))
            .min_by_key(|b| b.avg_latency_ms.load(Ordering::Relaxed))
            .cloned()
    }
    
    async fn update_backends(&self, backends: Vec<Backend>) {
        let mut b = self.backends.write().await;
        *b = backends;
    }
    
    async fn record_result(&self, backend_id: &str, success: bool, latency_ms: u64) {
        let backends = self.backends.read().await;
        
        if let Some(backend) = backends.iter().find(|b| b.id == backend_id) {
            backend.total_requests.fetch_add(1, Ordering::Relaxed);
            
            if !success {
                backend.failed_requests.fetch_add(1, Ordering::Relaxed);
            }
            
            // 指数移动平均(EMA)
            let alpha = 0.1;
            let current_avg = backend.avg_latency_ms.load(Ordering::Relaxed);
            let new_avg = if current_avg == 0 {
                latency_ms
            } else {
                ((1.0 - alpha) * current_avg as f64 + alpha * latency_ms as f64) as u64
            };
            backend.avg_latency_ms.store(new_avg, Ordering::Relaxed);
        }
    }
    
    fn name(&self) -> &str {
        "LeastLatency"
    }
}
```

---

## 4. 一致性哈希

### 4.1 一致性哈希实现

```rust
use std::collections::BTreeMap;
use std::hash::{Hash, Hasher};
use std::collections::hash_map::DefaultHasher;

/// 一致性哈希负载均衡器
pub struct ConsistentHashBalancer {
    backends: Arc<RwLock<Vec<Backend>>>,
    hash_ring: Arc<RwLock<BTreeMap<u64, String>>>,
    virtual_nodes: usize,
}

impl ConsistentHashBalancer {
    pub fn new(backends: Vec<Backend>, virtual_nodes: usize) -> Self {
        let balancer = Self {
            backends: Arc::new(RwLock::new(backends.clone())),
            hash_ring: Arc::new(RwLock::new(BTreeMap::new())),
            virtual_nodes,
        };
        
        // 初始化哈希环
        tokio::spawn({
            let balancer_clone = balancer.clone();
            async move {
                balancer_clone.rebuild_ring().await;
            }
        });
        
        balancer
    }
    
    /// 重建哈希环
    async fn rebuild_ring(&self) {
        let backends = self.backends.read().await;
        let mut ring = self.hash_ring.write().await;
        
        ring.clear();
        
        for backend in backends.iter() {
            if !matches!(*backend.health.read().await, HealthState::Healthy) {
                continue;
            }
            
            // 为每个后端创建虚拟节点
            for i in 0..self.virtual_nodes {
                let key = format!("{}:{}", backend.id, i);
                let hash = Self::hash_key(&key);
                ring.insert(hash, backend.id.clone());
            }
        }
    }
    
    /// 哈希函数
    fn hash_key(key: &str) -> u64 {
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        hasher.finish()
    }
    
    /// 根据key查找后端
    async fn find_backend(&self, key: &str) -> Option<Backend> {
        let ring = self.hash_ring.read().await;
        let backends = self.backends.read().await;
        
        if ring.is_empty() {
            return None;
        }
        
        let hash = Self::hash_key(key);
        
        // 查找第一个大于等于hash的节点
        let backend_id = ring.range(hash..)
            .next()
            .or_else(|| ring.iter().next())
            .map(|(_, id)| id)?;
        
        backends.iter()
            .find(|b| &b.id == backend_id)
            .cloned()
    }
}

impl Clone for ConsistentHashBalancer {
    fn clone(&self) -> Self {
        Self {
            backends: Arc::clone(&self.backends),
            hash_ring: Arc::clone(&self.hash_ring),
            virtual_nodes: self.virtual_nodes,
        }
    }
}

#[async_trait::async_trait]
impl LoadBalancer for ConsistentHashBalancer {
    async fn select(&self, request: &Request) -> Option<Backend> {
        let key = request.route_key.as_ref()
            .or(request.client_id.as_ref())
            .unwrap_or(&request.id);
        
        self.find_backend(key).await
    }
    
    async fn update_backends(&self, backends: Vec<Backend>) {
        let mut b = self.backends.write().await;
        *b = backends;
        drop(b);
        
        // 重建哈希环
        self.rebuild_ring().await;
    }
    
    async fn record_result(&self, backend_id: &str, success: bool, latency_ms: u64) {
        let backends = self.backends.read().await;
        
        if let Some(backend) = backends.iter().find(|b| b.id == backend_id) {
            backend.total_requests.fetch_add(1, Ordering::Relaxed);
            
            if !success {
                backend.failed_requests.fetch_add(1, Ordering::Relaxed);
            }
            
            let current_avg = backend.avg_latency_ms.load(Ordering::Relaxed);
            let new_avg = if current_avg == 0 {
                latency_ms
            } else {
                (current_avg * 9 + latency_ms) / 10
            };
            backend.avg_latency_ms.store(new_avg, Ordering::Relaxed);
        }
    }
    
    fn name(&self) -> &str {
        "ConsistentHash"
    }
}
```

---

## 5. 智能路由

### 5.1 基于优先级的路由

```rust
/// 优先级路由器
pub struct PriorityRouter {
    high_priority_balancer: Arc<dyn LoadBalancer>,
    normal_priority_balancer: Arc<dyn LoadBalancer>,
    low_priority_balancer: Arc<dyn LoadBalancer>,
}

impl PriorityRouter {
    pub fn new(
        high_priority_balancer: Arc<dyn LoadBalancer>,
        normal_priority_balancer: Arc<dyn LoadBalancer>,
        low_priority_balancer: Arc<dyn LoadBalancer>,
    ) -> Self {
        Self {
            high_priority_balancer,
            normal_priority_balancer,
            low_priority_balancer,
        }
    }
}

#[async_trait::async_trait]
impl LoadBalancer for PriorityRouter {
    async fn select(&self, request: &Request) -> Option<Backend> {
        match request.priority {
            Priority::High => self.high_priority_balancer.select(request).await,
            Priority::Normal => self.normal_priority_balancer.select(request).await,
            Priority::Low => self.low_priority_balancer.select(request).await,
        }
    }
    
    async fn update_backends(&self, backends: Vec<Backend>) {
        // 根据权重分配到不同的balancer
        // 简化实现：所有balancer使用相同的backends
        self.high_priority_balancer.update_backends(backends.clone()).await;
        self.normal_priority_balancer.update_backends(backends.clone()).await;
        self.low_priority_balancer.update_backends(backends).await;
    }
    
    async fn record_result(&self, backend_id: &str, success: bool, latency_ms: u64) {
        // 所有balancer都记录结果
        self.high_priority_balancer.record_result(backend_id, success, latency_ms).await;
        self.normal_priority_balancer.record_result(backend_id, success, latency_ms).await;
        self.low_priority_balancer.record_result(backend_id, success, latency_ms).await;
    }
    
    fn name(&self) -> &str {
        "PriorityRouter"
    }
}
```

---

## 6. 故障转移

### 6.1 重试机制

```rust
/// 重试负载均衡器
pub struct RetryBalancer {
    inner: Arc<dyn LoadBalancer>,
    max_retries: usize,
    backoff: Duration,
}

impl RetryBalancer {
    pub fn new(inner: Arc<dyn LoadBalancer>, max_retries: usize, backoff: Duration) -> Self {
        Self {
            inner,
            max_retries,
            backoff,
        }
    }
    
    /// 带重试的请求执行
    pub async fn execute_with_retry<F, Fut, T, E>(
        &self,
        request: &Request,
        f: F,
    ) -> Result<T, E>
    where
        F: Fn(Backend) -> Fut,
        Fut: std::future::Future<Output = Result<T, E>>,
        E: std::fmt::Display,
    {
        let mut attempts = 0;
        let mut last_error = None;
        
        while attempts < self.max_retries {
            let backend = match self.inner.select(request).await {
                Some(b) => b,
                None => {
                    tokio::time::sleep(self.backoff).await;
                    attempts += 1;
                    continue;
                }
            };
            
            let start = Instant::now();
            
            match f(backend.clone()).await {
                Ok(result) => {
                    let latency = start.elapsed().as_millis() as u64;
                    self.inner.record_result(&backend.id, true, latency).await;
                    return Ok(result);
                }
                Err(e) => {
                    let latency = start.elapsed().as_millis() as u64;
                    self.inner.record_result(&backend.id, false, latency).await;
                    
                    tracing::warn!(
                        "Request failed on backend {}: {}, attempt {}/{}",
                        backend.id,
                        e,
                        attempts + 1,
                        self.max_retries
                    );
                    
                    last_error = Some(e);
                    attempts += 1;
                    
                    if attempts < self.max_retries {
                        tokio::time::sleep(self.backoff).await;
                    }
                }
            }
        }
        
        Err(last_error.unwrap())
    }
}

#[async_trait::async_trait]
impl LoadBalancer for RetryBalancer {
    async fn select(&self, request: &Request) -> Option<Backend> {
        self.inner.select(request).await
    }
    
    async fn update_backends(&self, backends: Vec<Backend>) {
        self.inner.update_backends(backends).await;
    }
    
    async fn record_result(&self, backend_id: &str, success: bool, latency_ms: u64) {
        self.inner.record_result(backend_id, success, latency_ms).await;
    }
    
    fn name(&self) -> &str {
        "RetryBalancer"
    }
}
```

---

## 7. 完整实现

### 7.1 综合示例

```rust
use tracing_subscriber;
use std::time::Instant;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt::init();
    
    // 创建后端
    let backends = vec![
        Backend::new("backend-1".to_string(), "localhost:8001".to_string(), 10),
        Backend::new("backend-2".to_string(), "localhost:8002".to_string(), 20),
        Backend::new("backend-3".to_string(), "localhost:8003".to_string(), 30),
    ];
    
    // 测试各种负载均衡算法
    println!("=== Round Robin ===");
    test_balancer(Arc::new(RoundRobinBalancer::new(backends.clone()))).await;
    
    println!("\n=== Weighted Round Robin ===");
    test_balancer(Arc::new(WeightedRoundRobinBalancer::new(backends.clone()))).await;
    
    println!("\n=== Least Connections ===");
    test_balancer(Arc::new(LeastConnectionsBalancer::new(backends.clone()))).await;
    
    println!("\n=== P2C ===");
    test_balancer(Arc::new(P2CBalancer::new(backends.clone()))).await;
    
    println!("\n=== Consistent Hash ===");
    test_balancer(Arc::new(ConsistentHashBalancer::new(backends.clone(), 100))).await;
    
    Ok(())
}

async fn test_balancer(balancer: Arc<dyn LoadBalancer>) {
    let mut distribution: HashMap<String, usize> = HashMap::new();
    
    for i in 0..100 {
        let request = Request {
            id: format!("req-{}", i),
            client_id: Some(format!("client-{}", i % 10)),
            route_key: Some(format!("key-{}", i % 10)),
            priority: Priority::Normal,
        };
        
        if let Some(backend) = balancer.select(&request).await {
            *distribution.entry(backend.id.clone()).or_insert(0) += 1;
            
            // 模拟请求处理
            let latency = rand::random::<u64>() % 100 + 10;
            let success = rand::random::<f64>() > 0.1; // 10% 失败率
            
            balancer.record_result(&backend.id, success, latency).await;
        }
    }
    
    println!("Distribution:");
    for (backend_id, count) in distribution {
        println!("  {}: {} requests ({}%)", backend_id, count, count);
    }
}
```

---

## 总结

本文档提供了负载均衡与路由算法的完整Rust实现，包括:

✅ **基础算法**:
- 轮询(Round Robin)
- 加权轮询(Weighted RR)
- 最少连接(Least Connections)

✅ **动态算法**:
- Power of Two Choices (P2C)
- 最小延迟(Least Latency)

✅ **一致性哈希**:
- 虚拟节点
- 动态扩缩容

✅ **智能路由**:
- 优先级路由
- 故障转移
- 重试机制

✅ **生产特性**:
- 健康检查
- 指标收集
- 自动恢复

---

**参考资源**:
- [Load Balancing Algorithms](https://en.wikipedia.org/wiki/Load_balancing_(computing))
- [Consistent Hashing](https://en.wikipedia.org/wiki/Consistent_hashing)
- [The Power of Two Random Choices](https://www.eecs.harvard.edu/~michaelm/postscripts/handbook2001.pdf)

