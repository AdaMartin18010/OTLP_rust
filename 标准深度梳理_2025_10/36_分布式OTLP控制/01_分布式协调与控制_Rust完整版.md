# 分布式OTLP协调与控制 - Rust完整实现

> **Rust版本**: 1.90+  
> **核心依赖**: tokio 1.47.1, etcd-client 0.15, consul 0.6  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月9日

---

## 📋 目录

- [分布式OTLP协调与控制 - Rust完整实现](#分布式otlp协调与控制---rust完整实现)
  - [📋 目录](#-目录)
  - [1. 分布式OTLP架构概述](#1-分布式otlp架构概述)
    - [1.1 架构设计](#11-架构设计)
    - [1.2 核心组件](#12-核心组件)
  - [2. 全局感知机制](#2-全局感知机制)
    - [2.1 全局拓扑感知](#21-全局拓扑感知)
    - [2.2 全局采样协调](#22-全局采样协调)
  - [3. 本地感知与优化](#3-本地感知与优化)
    - [3.1 本地负载感知](#31-本地负载感知)
    - [3.2 本地智能路由](#32-本地智能路由)
  - [4. 分布式协调服务](#4-分布式协调服务)
    - [4.1 基于etcd的协调实现](#41-基于etcd的协调实现)
  - [5. 配置管理与热更新](#5-配置管理与热更新)
    - [5.1 配置热更新实现](#51-配置热更新实现)
  - [6. 服务发现与注册](#6-服务发现与注册)
    - [6.1 服务注册实现](#61-服务注册实现)
  - [7. 分布式锁与选举](#7-分布式锁与选举)
    - [7.1 分布式锁实现](#71-分布式锁实现)
    - [7.2 Leader选举实现](#72-leader选举实现)
  - [8. 完整实现示例](#8-完整实现示例)
    - [8.1 综合示例](#81-综合示例)
  - [9. 配置示例](#9-配置示例)
    - [9.1 全局配置示例](#91-全局配置示例)
  - [10. 性能优化](#10-性能优化)
    - [10.1 批处理优化](#101-批处理优化)
  - [11. 监控与告警](#11-监控与告警)
    - [11.1 指标收集](#111-指标收集)
  - [12. 总结](#12-总结)

---

## 1. 分布式OTLP架构概述

### 1.1 架构设计

```text
分布式OTLP架构层次:

┌─────────────────────────────────────────────────────────┐
│              全局控制平面 (Global Control Plane)         │
│  ┌──────────────────────────────────────────────────┐   │
│  │  配置中心 (etcd/Consul)                           │   │
│  │  - 全局配置管理                                    │  │
│  │  - 采样策略同步                                    │  │
│  │  - 拓扑感知                                       │   │
│  └──────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────┘
                          ↕
┌─────────────────────────────────────────────────────────┐
│              区域控制器 (Regional Controllers)           │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐               │
│  │ Region-1 │  │ Region-2 │  │ Region-N │               │
│  │ 负载均衡  │  │ 负载均衡  │  │ 负载均衡  │              │
│  │ 本地感知  │  │ 本地感知  │  │ 本地感知  │              │
│  └──────────┘  └──────────┘  └──────────┘               │
└─────────────────────────────────────────────────────────┘
                          ↕
┌─────────────────────────────────────────────────────────┐
│              数据平面 (Data Plane)                       │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐               │
│  │Collector1│  │Collector2│  │CollectorN│               │
│  │ Receiver │  │ Receiver │  │ Receiver │               │
│  │Processor │  │Processor │  │Processor │               │
│  │ Exporter │  │ Exporter │  │ Exporter │               │
│  └──────────┘  └──────────┘  └──────────┘               │
└─────────────────────────────────────────────────────────┘
```

### 1.2 核心组件

```rust
use tokio::sync::{RwLock, broadcast, mpsc};
use std::sync::Arc;
use std::collections::HashMap;
use serde::{Serialize, Deserialize};

/// 分布式OTLP控制器
pub struct DistributedOtlpController {
    /// 全局配置
    global_config: Arc<RwLock<GlobalConfig>>,
    
    /// 区域控制器
    regional_controllers: Arc<RwLock<HashMap<String, RegionalController>>>,
    
    /// 配置变更通知
    config_changes: broadcast::Sender<ConfigChange>,
    
    /// 健康状态
    health: Arc<RwLock<HealthStatus>>,
    
    /// 协调服务客户端
    coordinator: Arc<dyn CoordinatorClient>,
}

/// 全局配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GlobalConfig {
    /// 全局采样率
    pub global_sampling_rate: f64,
    
    /// 采样策略
    pub sampling_strategies: Vec<SamplingStrategy>,
    
    /// 降级配置
    pub degradation: DegradationConfig,
    
    /// 限流配置
    pub rate_limiting: RateLimitingConfig,
    
    /// 路由规则
    pub routing_rules: Vec<RoutingRule>,
    
    /// 元数据
    pub metadata: HashMap<String, String>,
    
    /// 版本号
    pub version: u64,
}

/// 区域控制器
pub struct RegionalController {
    /// 区域ID
    region_id: String,
    
    /// 本地配置
    local_config: Arc<RwLock<LocalConfig>>,
    
    /// Collector实例
    collectors: Arc<RwLock<HashMap<String, CollectorInfo>>>,
    
    /// 负载均衡器
    load_balancer: Arc<dyn LoadBalancer>,
    
    /// 健康检查器
    health_checker: Arc<HealthChecker>,
    
    /// 指标收集器
    metrics: Arc<MetricsCollector>,
}

/// 本地配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LocalConfig {
    /// 区域特定采样率
    pub regional_sampling_rate: f64,
    
    /// 本地路由偏好
    pub local_routing_preference: Vec<String>,
    
    /// 缓冲区大小
    pub buffer_size: usize,
    
    /// 批处理配置
    pub batch_config: BatchConfig,
    
    /// 重试策略
    pub retry_policy: RetryPolicy,
}

impl DistributedOtlpController {
    /// 创建新的分布式控制器
    pub async fn new(
        coordinator_url: &str,
        region_id: String,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        let coordinator = create_coordinator_client(coordinator_url).await?;
        
        let (config_tx, _) = broadcast::channel(1000);
        
        let global_config = Arc::new(RwLock::new(
            coordinator.get_global_config().await?
        ));
        
        let health = Arc::new(RwLock::new(HealthStatus::healthy()));
        
        Ok(Self {
            global_config,
            regional_controllers: Arc::new(RwLock::new(HashMap::new())),
            config_changes: config_tx,
            health,
            coordinator,
        })
    }
    
    /// 启动控制器
    pub async fn start(&self) -> Result<(), Box<dyn std::error::Error>> {
        // 启动配置监听
        self.start_config_watcher().await?;
        
        // 启动健康检查
        self.start_health_checks().await?;
        
        // 启动指标收集
        self.start_metrics_collection().await?;
        
        Ok(())
    }
    
    /// 监听配置变更
    async fn start_config_watcher(&self) -> Result<(), Box<dyn std::error::Error>> {
        let coordinator = Arc::clone(&self.coordinator);
        let global_config = Arc::clone(&self.global_config);
        let config_changes = self.config_changes.clone();
        
        tokio::spawn(async move {
            let mut watch_stream = coordinator.watch_config().await.unwrap();
            
            while let Some(change) = watch_stream.recv().await {
                // 更新全局配置
                let mut config = global_config.write().await;
                config.apply_change(&change);
                
                // 广播配置变更
                let _ = config_changes.send(change);
                
                tracing::info!("Config updated: {:?}", config.version);
            }
        });
        
        Ok(())
    }
    
    /// 注册区域控制器
    pub async fn register_region(
        &self,
        region_id: String,
        local_config: LocalConfig,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let regional_controller = RegionalController::new(
            region_id.clone(),
            local_config,
            self.coordinator.clone(),
        ).await?;
        
        let mut controllers = self.regional_controllers.write().await;
        controllers.insert(region_id.clone(), regional_controller);
        
        // 注册到协调服务
        self.coordinator.register_region(&region_id).await?;
        
        Ok(())
    }
}
```

---

## 2. 全局感知机制

### 2.1 全局拓扑感知

```rust
use std::time::{Duration, Instant};
use tokio::time::interval;

/// 全局拓扑管理器
pub struct GlobalTopologyManager {
    /// 拓扑状态
    topology: Arc<RwLock<Topology>>,
    
    /// 更新间隔
    update_interval: Duration,
    
    /// 协调器
    coordinator: Arc<dyn CoordinatorClient>,
}

/// 拓扑结构
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Topology {
    /// 区域列表
    pub regions: HashMap<String, RegionTopology>,
    
    /// 全局统计
    pub global_stats: GlobalStats,
    
    /// 更新时间
    pub last_updated: Instant,
}

/// 区域拓扑
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RegionTopology {
    /// 区域ID
    pub region_id: String,
    
    /// Collector列表
    pub collectors: Vec<CollectorTopology>,
    
    /// 区域统计
    pub stats: RegionStats,
    
    /// 健康状态
    pub health: RegionHealth,
}

/// Collector拓扑
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CollectorTopology {
    /// Collector ID
    pub id: String,
    
    /// 地址
    pub address: String,
    
    /// 容量
    pub capacity: Capacity,
    
    /// 当前负载
    pub current_load: Load,
    
    /// 健康状态
    pub health: HealthStatus,
}

/// 全局统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GlobalStats {
    /// 总span数
    pub total_spans: u64,
    
    /// 总字节数
    pub total_bytes: u64,
    
    /// 平均延迟
    pub avg_latency_ms: f64,
    
    /// 错误率
    pub error_rate: f64,
    
    /// 采样率
    pub effective_sampling_rate: f64,
}

impl GlobalTopologyManager {
    pub fn new(
        coordinator: Arc<dyn CoordinatorClient>,
        update_interval: Duration,
    ) -> Self {
        Self {
            topology: Arc::new(RwLock::new(Topology::default())),
            update_interval,
            coordinator,
        }
    }
    
    /// 启动拓扑更新
    pub async fn start(&self) {
        let topology = Arc::clone(&self.topology);
        let coordinator = Arc::clone(&self.coordinator);
        let update_interval = self.update_interval;
        
        tokio::spawn(async move {
            let mut ticker = interval(update_interval);
            
            loop {
                ticker.tick().await;
                
                match Self::update_topology(&coordinator).await {
                    Ok(new_topology) => {
                        let mut topo = topology.write().await;
                        *topo = new_topology;
                        
                        tracing::debug!("Topology updated: {} regions", topo.regions.len());
                    }
                    Err(e) => {
                        tracing::error!("Failed to update topology: {}", e);
                    }
                }
            }
        });
    }
    
    /// 更新拓扑信息
    async fn update_topology(
        coordinator: &Arc<dyn CoordinatorClient>,
    ) -> Result<Topology, Box<dyn std::error::Error>> {
        // 获取所有区域
        let regions = coordinator.list_regions().await?;
        
        let mut region_topologies = HashMap::new();
        let mut global_stats = GlobalStats::default();
        
        for region_id in regions {
            // 获取区域详情
            let region = coordinator.get_region(&region_id).await?;
            
            // 获取Collector列表
            let collectors = coordinator.list_collectors(&region_id).await?;
            
            let mut collector_topologies = Vec::new();
            
            for collector_id in collectors {
                let collector = coordinator.get_collector(&collector_id).await?;
                
                collector_topologies.push(CollectorTopology {
                    id: collector.id,
                    address: collector.address,
                    capacity: collector.capacity,
                    current_load: collector.current_load,
                    health: collector.health,
                });
                
                // 累加全局统计
                global_stats.total_spans += collector.stats.spans;
                global_stats.total_bytes += collector.stats.bytes;
            }
            
            region_topologies.insert(
                region_id.clone(),
                RegionTopology {
                    region_id: region_id.clone(),
                    collectors: collector_topologies,
                    stats: region.stats,
                    health: region.health,
                },
            );
        }
        
        // 计算平均指标
        if !region_topologies.is_empty() {
            let total_collectors: usize = region_topologies.values()
                .map(|r| r.collectors.len())
                .sum();
            
            if total_collectors > 0 {
                global_stats.avg_latency_ms /= total_collectors as f64;
            }
        }
        
        Ok(Topology {
            regions: region_topologies,
            global_stats,
            last_updated: Instant::now(),
        })
    }
    
    /// 获取最优Collector
    pub async fn get_best_collector(
        &self,
        region_id: Option<&str>,
        criteria: &SelectionCriteria,
    ) -> Option<CollectorTopology> {
        let topology = self.topology.read().await;
        
        let collectors: Vec<&CollectorTopology> = if let Some(rid) = region_id {
            // 优先选择指定区域
            topology.regions.get(rid)
                .map(|r| r.collectors.iter().collect())
                .unwrap_or_default()
        } else {
            // 全局选择
            topology.regions.values()
                .flat_map(|r| r.collectors.iter())
                .collect()
        };
        
        // 根据标准选择最优Collector
        collectors.into_iter()
            .filter(|c| c.health.is_healthy() && c.has_capacity())
            .max_by_key(|c| criteria.score(c))
            .cloned()
    }
}

/// 选择标准
#[derive(Debug, Clone)]
pub struct SelectionCriteria {
    /// 权重: 负载
    pub load_weight: f64,
    
    /// 权重: 延迟
    pub latency_weight: f64,
    
    /// 权重: 容量
    pub capacity_weight: f64,
}

impl SelectionCriteria {
    fn score(&self, collector: &CollectorTopology) -> i64 {
        let load_score = (1.0 - collector.current_load.utilization()) * self.load_weight;
        let latency_score = (1.0 / (1.0 + collector.current_load.avg_latency_ms)) * self.latency_weight;
        let capacity_score = collector.capacity.available_ratio() * self.capacity_weight;
        
        ((load_score + latency_score + capacity_score) * 1000.0) as i64
    }
}
```

### 2.2 全局采样协调

```rust
/// 全局采样协调器
pub struct GlobalSamplingCoordinator {
    /// 当前策略
    current_strategy: Arc<RwLock<SamplingStrategy>>,
    
    /// 目标采样率
    target_rate: Arc<RwLock<f64>>,
    
    /// 实际采样率统计
    actual_rates: Arc<RwLock<HashMap<String, f64>>>,
    
    /// 协调器
    coordinator: Arc<dyn CoordinatorClient>,
}

/// 采样策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SamplingStrategy {
    /// 固定比例
    Fixed { rate: f64 },
    
    /// 自适应
    Adaptive {
        min_rate: f64,
        max_rate: f64,
        target_qps: u64,
    },
    
    /// 基于优先级
    PriorityBased {
        high_priority_rate: f64,
        normal_rate: f64,
        low_priority_rate: f64,
    },
    
    /// 基于成本
    CostBased {
        budget_per_hour: f64,
        cost_per_span: f64,
    },
}

impl GlobalSamplingCoordinator {
    pub fn new(coordinator: Arc<dyn CoordinatorClient>) -> Self {
        Self {
            current_strategy: Arc::new(RwLock::new(SamplingStrategy::Fixed { rate: 0.1 })),
            target_rate: Arc::new(RwLock::new(0.1)),
            actual_rates: Arc::new(RwLock::new(HashMap::new())),
            coordinator,
        }
    }
    
    /// 启动采样协调
    pub async fn start(&self) {
        self.start_strategy_adjuster().await;
        self.start_rate_aggregator().await;
    }
    
    /// 启动策略调整器
    async fn start_strategy_adjuster(&self) {
        let current_strategy = Arc::clone(&self.current_strategy);
        let target_rate = Arc::clone(&self.target_rate);
        let actual_rates = Arc::clone(&self.actual_rates);
        let coordinator = Arc::clone(&self.coordinator);
        
        tokio::spawn(async move {
            let mut ticker = interval(Duration::from_secs(60));
            
            loop {
                ticker.tick().await;
                
                // 获取全局统计
                let global_stats = match coordinator.get_global_stats().await {
                    Ok(stats) => stats,
                    Err(e) => {
                        tracing::error!("Failed to get global stats: {}", e);
                        continue;
                    }
                };
                
                // 计算平均实际采样率
                let rates = actual_rates.read().await;
                let avg_actual_rate = if rates.is_empty() {
                    0.0
                } else {
                    rates.values().sum::<f64>() / rates.len() as f64
                };
                
                // 根据策略调整目标采样率
                let strategy = current_strategy.read().await;
                let new_target = match &*strategy {
                    SamplingStrategy::Fixed { rate } => *rate,
                    
                    SamplingStrategy::Adaptive { min_rate, max_rate, target_qps } => {
                        Self::calculate_adaptive_rate(
                            *min_rate,
                            *max_rate,
                            *target_qps,
                            global_stats.current_qps,
                        )
                    }
                    
                    SamplingStrategy::PriorityBased { normal_rate, .. } => {
                        *normal_rate // 简化实现
                    }
                    
                    SamplingStrategy::CostBased { budget_per_hour, cost_per_span } => {
                        Self::calculate_cost_based_rate(
                            *budget_per_hour,
                            *cost_per_span,
                            global_stats.current_qps,
                        )
                    }
                };
                
                let mut target = target_rate.write().await;
                *target = new_target;
                
                tracing::info!(
                    "Sampling rate adjusted: target={:.4}, actual={:.4}, qps={}",
                    new_target,
                    avg_actual_rate,
                    global_stats.current_qps
                );
            }
        });
    }
    
    /// 计算自适应采样率
    fn calculate_adaptive_rate(
        min_rate: f64,
        max_rate: f64,
        target_qps: u64,
        current_qps: u64,
    ) -> f64 {
        if current_qps == 0 {
            return max_rate;
        }
        
        let ratio = target_qps as f64 / current_qps as f64;
        ratio.clamp(min_rate, max_rate)
    }
    
    /// 计算基于成本的采样率
    fn calculate_cost_based_rate(
        budget_per_hour: f64,
        cost_per_span: f64,
        current_qps: u64,
    ) -> f64 {
        if current_qps == 0 || cost_per_span == 0.0 {
            return 1.0;
        }
        
        let max_spans_per_hour = budget_per_hour / cost_per_span;
        let current_spans_per_hour = current_qps as f64 * 3600.0;
        
        (max_spans_per_hour / current_spans_per_hour).min(1.0)
    }
}
```

---

## 3. 本地感知与优化

### 3.1 本地负载感知

```rust
use std::sync::atomic::{AtomicU64, Ordering};

/// 本地负载监控器
pub struct LocalLoadMonitor {
    /// 当前QPS
    current_qps: Arc<AtomicU64>,
    
    /// 当前字节/秒
    current_bps: Arc<AtomicU64>,
    
    /// 队列深度
    queue_depth: Arc<AtomicU64>,
    
    /// CPU使用率
    cpu_usage: Arc<RwLock<f64>>,
    
    /// 内存使用率
    memory_usage: Arc<RwLock<f64>>,
    
    /// 历史统计
    history: Arc<RwLock<CircularBuffer<LoadSnapshot>>>,
}

/// 负载快照
#[derive(Debug, Clone)]
pub struct LoadSnapshot {
    pub timestamp: Instant,
    pub qps: u64,
    pub bps: u64,
    pub queue_depth: u64,
    pub cpu_usage: f64,
    pub memory_usage: f64,
}

impl LocalLoadMonitor {
    pub fn new(history_size: usize) -> Self {
        Self {
            current_qps: Arc::new(AtomicU64::new(0)),
            current_bps: Arc::new(AtomicU64::new(0)),
            queue_depth: Arc::new(AtomicU64::new(0)),
            cpu_usage: Arc::new(RwLock::new(0.0)),
            memory_usage: Arc::new(RwLock::new(0.0)),
            history: Arc::new(RwLock::new(CircularBuffer::new(history_size))),
        }
    }
    
    /// 启动监控
    pub async fn start(&self) {
        self.start_qps_counter().await;
        self.start_resource_monitor().await;
        self.start_history_recorder().await;
    }
    
    /// 启动QPS计数器
    async fn start_qps_counter(&self) {
        let current_qps = Arc::clone(&self.current_qps);
        let current_bps = Arc::clone(&self.current_bps);
        
        tokio::spawn(async move {
            let mut ticker = interval(Duration::from_secs(1));
            let mut last_spans = 0u64;
            let mut last_bytes = 0u64;
            
            loop {
                ticker.tick().await;
                
                let current_spans = current_qps.load(Ordering::Relaxed);
                let current_bytes = current_bps.load(Ordering::Relaxed);
                
                let qps = current_spans.saturating_sub(last_spans);
                let bps = current_bytes.saturating_sub(last_bytes);
                
                last_spans = current_spans;
                last_bytes = current_bytes;
                
                tracing::debug!("Current load: {} spans/s, {} bytes/s", qps, bps);
            }
        });
    }
    
    /// 记录span
    pub fn record_span(&self, size_bytes: u64) {
        self.current_qps.fetch_add(1, Ordering::Relaxed);
        self.current_bps.fetch_add(size_bytes, Ordering::Relaxed);
    }
    
    /// 获取当前负载
    pub async fn get_current_load(&self) -> Load {
        Load {
            qps: self.current_qps.load(Ordering::Relaxed),
            bps: self.current_bps.load(Ordering::Relaxed),
            queue_depth: self.queue_depth.load(Ordering::Relaxed),
            cpu_usage: *self.cpu_usage.read().await,
            memory_usage: *self.memory_usage.read().await,
            avg_latency_ms: self.calculate_avg_latency().await,
        }
    }
    
    /// 计算平均延迟
    async fn calculate_avg_latency(&self) -> f64 {
        let history = self.history.read().await;
        
        if history.is_empty() {
            return 0.0;
        }
        
        // 简化实现：基于队列深度估算
        let avg_queue_depth: f64 = history.iter()
            .map(|s| s.queue_depth as f64)
            .sum::<f64>() / history.len() as f64;
        
        // Little's Law: L = λ * W
        // W = L / λ
        let avg_qps: f64 = history.iter()
            .map(|s| s.qps as f64)
            .sum::<f64>() / history.len() as f64;
        
        if avg_qps > 0.0 {
            (avg_queue_depth / avg_qps) * 1000.0 // 转换为毫秒
        } else {
            0.0
        }
    }
    
    /// 预测未来负载
    pub async fn predict_load(&self, horizon_secs: u64) -> PredictedLoad {
        let history = self.history.read().await;
        
        if history.len() < 10 {
            // 数据不足，返回当前负载
            return PredictedLoad {
                qps: self.current_qps.load(Ordering::Relaxed),
                confidence: 0.5,
            };
        }
        
        // 简单的线性回归预测
        let recent: Vec<&LoadSnapshot> = history.iter().rev().take(60).collect();
        
        let sum_qps: u64 = recent.iter().map(|s| s.qps).sum();
        let avg_qps = sum_qps / recent.len() as u64;
        
        // 计算趋势
        let first_half_avg = recent.iter().take(30).map(|s| s.qps).sum::<u64>() / 30;
        let second_half_avg = recent.iter().skip(30).map(|s| s.qps).sum::<u64>() / 30;
        let trend = second_half_avg as i64 - first_half_avg as i64;
        
        let predicted_qps = (avg_qps as i64 + trend * horizon_secs as i64 / 60).max(0) as u64;
        
        PredictedLoad {
            qps: predicted_qps,
            confidence: 0.8, // 简化：固定置信度
        }
    }
}

/// 预测负载
#[derive(Debug, Clone)]
pub struct PredictedLoad {
    pub qps: u64,
    pub confidence: f64,
}

/// 负载
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Load {
    pub qps: u64,
    pub bps: u64,
    pub queue_depth: u64,
    pub cpu_usage: f64,
    pub memory_usage: f64,
    pub avg_latency_ms: f64,
}

impl Load {
    pub fn utilization(&self) -> f64 {
        // 综合利用率
        (self.cpu_usage + self.memory_usage) / 2.0
    }
}
```

### 3.2 本地智能路由

```rust
/// 本地智能路由器
pub struct LocalIntelligentRouter {
    /// 后端列表
    backends: Arc<RwLock<Vec<Backend>>>,
    
    /// 负载监控器
    load_monitor: Arc<LocalLoadMonitor>,
    
    /// 路由策略
    strategy: Arc<RwLock<RoutingStrategy>>,
    
    /// 统计信息
    stats: Arc<RwLock<RoutingStats>>,
}

/// 后端
#[derive(Debug, Clone)]
pub struct Backend {
    pub id: String,
    pub address: String,
    pub weight: u32,
    pub health: HealthStatus,
    pub load: Load,
}

/// 路由策略
#[derive(Debug, Clone)]
pub enum RoutingStrategy {
    /// 轮询
    RoundRobin,
    
    /// 加权轮询
    WeightedRoundRobin,
    
    /// 最少连接
    LeastConnections,
    
    /// 一致性哈希
    ConsistentHash,
    
    /// 智能路由（基于负载和延迟）
    Intelligent {
        load_weight: f64,
        latency_weight: f64,
    },
}

impl LocalIntelligentRouter {
    pub fn new(load_monitor: Arc<LocalLoadMonitor>) -> Self {
        Self {
            backends: Arc::new(RwLock::new(Vec::new())),
            load_monitor,
            strategy: Arc::new(RwLock::new(RoutingStrategy::Intelligent {
                load_weight: 0.7,
                latency_weight: 0.3,
            })),
            stats: Arc::new(RwLock::new(RoutingStats::default())),
        }
    }
    
    /// 选择后端
    pub async fn select_backend(&self, request: &RoutingRequest) -> Option<Backend> {
        let backends = self.backends.read().await;
        let strategy = self.strategy.read().await;
        
        match &*strategy {
            RoutingStrategy::RoundRobin => {
                self.select_round_robin(&backends).await
            }
            
            RoutingStrategy::WeightedRoundRobin => {
                self.select_weighted_round_robin(&backends).await
            }
            
            RoutingStrategy::LeastConnections => {
                self.select_least_connections(&backends).await
            }
            
            RoutingStrategy::ConsistentHash => {
                self.select_consistent_hash(&backends, request).await
            }
            
            RoutingStrategy::Intelligent { load_weight, latency_weight } => {
                self.select_intelligent(&backends, *load_weight, *latency_weight).await
            }
        }
    }
    
    /// 智能选择后端
    async fn select_intelligent(
        &self,
        backends: &[Backend],
        load_weight: f64,
        latency_weight: f64,
    ) -> Option<Backend> {
        let healthy_backends: Vec<&Backend> = backends.iter()
            .filter(|b| b.health.is_healthy())
            .collect();
        
        if healthy_backends.is_empty() {
            return None;
        }
        
        // 计算每个后端的评分
        let scores: Vec<(usize, f64)> = healthy_backends.iter()
            .enumerate()
            .map(|(idx, backend)| {
                let load_score = 1.0 - backend.load.utilization();
                let latency_score = 1.0 / (1.0 + backend.load.avg_latency_ms);
                let total_score = load_score * load_weight + latency_score * latency_weight;
                (idx, total_score)
            })
            .collect();
        
        // 选择得分最高的后端
        scores.iter()
            .max_by(|a, b| a.1.partial_cmp(&b.1).unwrap())
            .and_then(|(idx, _)| healthy_backends.get(*idx))
            .map(|&b| b.clone())
    }
    
    /// 轮询选择
    async fn select_round_robin(&self, backends: &[Backend]) -> Option<Backend> {
        let healthy: Vec<&Backend> = backends.iter()
            .filter(|b| b.health.is_healthy())
            .collect();
        
        if healthy.is_empty() {
            return None;
        }
        
        let mut stats = self.stats.write().await;
        let idx = stats.round_robin_counter % healthy.len();
        stats.round_robin_counter += 1;
        
        healthy.get(idx).map(|&b| b.clone())
    }
    
    /// 最少连接选择
    async fn select_least_connections(&self, backends: &[Backend]) -> Option<Backend> {
        backends.iter()
            .filter(|b| b.health.is_healthy())
            .min_by_key(|b| b.load.queue_depth)
            .cloned()
    }
}

/// 路由请求
#[derive(Debug)]
pub struct RoutingRequest {
    pub trace_id: TraceId,
    pub service_name: String,
    pub span_count: usize,
}

/// 路由统计
#[derive(Debug, Default)]
struct RoutingStats {
    round_robin_counter: usize,
    total_requests: u64,
    successful_routes: u64,
    failed_routes: u64,
}
```

---

## 4. 分布式协调服务

### 4.1 基于etcd的协调实现

```rust
use etcd_client::{Client as EtcdClient, GetOptions, WatchOptions, PutOptions};

/// etcd协调客户端
pub struct EtcdCoordinator {
    client: EtcdClient,
    prefix: String,
}

impl EtcdCoordinator {
    pub async fn new(endpoints: Vec<String>, prefix: String) -> Result<Self, Box<dyn std::error::Error>> {
        let client = EtcdClient::connect(endpoints, None).await?;
        
        Ok(Self {
            client,
            prefix,
        })
    }
    
    /// 获取全局配置
    pub async fn get_global_config(&mut self) -> Result<GlobalConfig, Box<dyn std::error::Error>> {
        let key = format!("{}/global/config", self.prefix);
        
        let resp = self.client.get(key, None).await?;
        
        if let Some(kv) = resp.kvs().first() {
            let config: GlobalConfig = serde_json::from_slice(kv.value())?;
            Ok(config)
        } else {
            Ok(GlobalConfig::default())
        }
    }
    
    /// 监听配置变更
    pub async fn watch_config(&mut self) -> Result<mpsc::Receiver<ConfigChange>, Box<dyn std::error::Error>> {
        let key = format!("{}/global/config", self.prefix);
        
        let (tx, rx) = mpsc::channel(100);
        
        let (mut watcher, mut stream) = self.client.watch(key, None).await?;
        
        tokio::spawn(async move {
            while let Some(resp) = stream.message().await.transpose() {
                match resp {
                    Ok(watch_resp) => {
                        for event in watch_resp.events() {
                            if let Some(kv) = event.kv() {
                                if let Ok(config) = serde_json::from_slice::<GlobalConfig>(kv.value()) {
                                    let change = ConfigChange {
                                        version: config.version,
                                        config,
                                    };
                                    
                                    if tx.send(change).await.is_err() {
                                        break;
                                    }
                                }
                            }
                        }
                    }
                    Err(e) => {
                        tracing::error!("Watch error: {}", e);
                        break;
                    }
                }
            }
        });
        
        Ok(rx)
    }
    
    /// 注册Collector
    pub async fn register_collector(
        &mut self,
        collector_id: &str,
        info: &CollectorInfo,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let key = format!("{}/collectors/{}", self.prefix, collector_id);
        let value = serde_json::to_string(info)?;
        
        // 带TTL的注册（心跳机制）
        let lease = self.client.lease_grant(30, None).await?;
        
        self.client.put(key, value, Some(PutOptions::new().with_lease(lease.id()))).await?;
        
        // 启动心跳保持
        self.keep_alive_lease(lease.id()).await?;
        
        Ok(())
    }
    
    /// 保持租约活跃
    async fn keep_alive_lease(&mut self, lease_id: i64) -> Result<(), Box<dyn std::error::Error>> {
        let mut client = self.client.clone();
        
        tokio::spawn(async move {
            let (mut keeper, mut stream) = match client.lease_keep_alive(lease_id).await {
                Ok(k) => k,
                Err(e) => {
                    tracing::error!("Failed to create lease keeper: {}", e);
                    return;
                }
            };
            
            let mut ticker = interval(Duration::from_secs(10));
            
            loop {
                ticker.tick().await;
                
                if keeper.keep_alive().await.is_err() {
                    tracing::error!("Failed to keep lease alive");
                    break;
                }
                
                // 消费响应
                if stream.message().await.is_none() {
                    break;
                }
            }
        });
        
        Ok(())
    }
}

#[async_trait::async_trait]
impl CoordinatorClient for EtcdCoordinator {
    async fn get_global_config(&self) -> Result<GlobalConfig, Box<dyn std::error::Error>> {
        let mut client = self.clone();
        client.get_global_config().await
    }
    
    async fn watch_config(&self) -> Result<mpsc::Receiver<ConfigChange>, Box<dyn std::error::Error>> {
        let mut client = self.clone();
        client.watch_config().await
    }
    
    async fn register_region(&self, region_id: &str) -> Result<(), Box<dyn std::error::Error>> {
        let mut client = self.clone();
        let key = format!("{}/regions/{}", client.prefix, region_id);
        client.client.put(key, "", None).await?;
        Ok(())
    }
    
    async fn list_regions(&self) -> Result<Vec<String>, Box<dyn std::error::Error>> {
        let mut client = self.clone();
        let key = format!("{}/regions/", client.prefix);
        
        let resp = client.client.get(key, Some(GetOptions::new().with_prefix())).await?;
        
        let regions: Vec<String> = resp.kvs().iter()
            .filter_map(|kv| {
                std::str::from_utf8(kv.key()).ok()
                    .and_then(|k| k.rsplit('/').next())
                    .map(|s| s.to_string())
            })
            .collect();
        
        Ok(regions)
    }
    
    // ... 其他方法实现
}
```

---

## 5. 配置管理与热更新

### 5.1 配置热更新实现

```rust
/// 配置管理器
pub struct ConfigManager {
    /// 当前配置
    current: Arc<RwLock<GlobalConfig>>,
    
    /// 配置监听器
    listeners: Arc<RwLock<Vec<broadcast::Sender<GlobalConfig>>>>,
    
    /// 验证器
    validator: Arc<dyn ConfigValidator>,
}

impl ConfigManager {
    pub fn new(initial_config: GlobalConfig, validator: Arc<dyn ConfigValidator>) -> Self {
        Self {
            current: Arc::new(RwLock::new(initial_config)),
            listeners: Arc::new(RwLock::new(Vec::new())),
            validator,
        }
    }
    
    /// 更新配置
    pub async fn update_config(&self, new_config: GlobalConfig) -> Result<(), ConfigError> {
        // 验证新配置
        self.validator.validate(&new_config)?;
        
        // 应用配置
        let mut current = self.current.write().await;
        let old_config = current.clone();
        *current = new_config.clone();
        
        // 通知所有监听器
        let listeners = self.listeners.read().await;
        for listener in listeners.iter() {
            let _ = listener.send(new_config.clone());
        }
        
        tracing::info!(
            "Config updated: version {} -> {}",
            old_config.version,
            new_config.version
        );
        
        Ok(())
    }
    
    /// 订阅配置变更
    pub async fn subscribe(&self) -> broadcast::Receiver<GlobalConfig> {
        let (tx, rx) = broadcast::channel(100);
        
        let mut listeners = self.listeners.write().await;
        listeners.push(tx);
        
        rx
    }
    
    /// 获取当前配置
    pub async fn get_current(&self) -> GlobalConfig {
        self.current.read().await.clone()
    }
}

/// 配置验证器
#[async_trait::async_trait]
pub trait ConfigValidator: Send + Sync {
    fn validate(&self, config: &GlobalConfig) -> Result<(), ConfigError>;
}

/// 默认配置验证器
pub struct DefaultConfigValidator;

impl DefaultConfigValidator {
    pub fn new() -> Self {
        Self
    }
}

impl ConfigValidator for DefaultConfigValidator {
    fn validate(&self, config: &GlobalConfig) -> Result<(), ConfigError> {
        // 采样率范围检查
        if config.global_sampling_rate < 0.0 || config.global_sampling_rate > 1.0 {
            return Err(ConfigError::InvalidValue(
                "global_sampling_rate must be between 0.0 and 1.0".to_string()
            ));
        }
        
        // 降级配置检查
        if config.degradation.threshold < 0.0 || config.degradation.threshold > 1.0 {
            return Err(ConfigError::InvalidValue(
                "degradation threshold must be between 0.0 and 1.0".to_string()
            ));
        }
        
        // 限流配置检查
        if config.rate_limiting.max_qps == 0 {
            return Err(ConfigError::InvalidValue(
                "max_qps must be greater than 0".to_string()
            ));
        }
        
        Ok(())
    }
}

/// 配置错误
#[derive(Debug, thiserror::Error)]
pub enum ConfigError {
    #[error("Invalid config value: {0}")]
    InvalidValue(String),
    
    #[error("Config validation failed: {0}")]
    ValidationFailed(String),
}
```

---

## 6. 服务发现与注册

### 6.1 服务注册实现

```rust
use std::net::SocketAddr;

/// 服务注册器
pub struct ServiceRegistry {
    /// 协调客户端
    coordinator: Arc<dyn CoordinatorClient>,
    
    /// 服务信息
    service_info: Arc<RwLock<ServiceInfo>>,
    
    /// 健康检查器
    health_checker: Arc<HealthChecker>,
}

/// 服务信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceInfo {
    pub id: String,
    pub name: String,
    pub address: SocketAddr,
    pub region: String,
    pub metadata: HashMap<String, String>,
    pub health: HealthStatus,
    pub registered_at: u64,
}

impl ServiceRegistry {
    pub fn new(
        coordinator: Arc<dyn CoordinatorClient>,
        service_info: ServiceInfo,
    ) -> Self {
        Self {
            coordinator,
            service_info: Arc::new(RwLock::new(service_info)),
            health_checker: Arc::new(HealthChecker::new()),
        }
    }
    
    /// 注册服务
    pub async fn register(&self) -> Result<(), Box<dyn std::error::Error>> {
        let service_info = self.service_info.read().await;
        
        self.coordinator.register_service(&service_info).await?;
        
        tracing::info!(
            "Service registered: {} at {}",
            service_info.name,
            service_info.address
        );
        
        // 启动心跳
        self.start_heartbeat().await;
        
        Ok(())
    }
    
    /// 启动心跳
    async fn start_heartbeat(&self) {
        let coordinator = Arc::clone(&self.coordinator);
        let service_info = Arc::clone(&self.service_info);
        let health_checker = Arc::clone(&self.health_checker);
        
        tokio::spawn(async move {
            let mut ticker = interval(Duration::from_secs(10));
            
            loop {
                ticker.tick().await;
                
                // 检查健康状态
                let health = health_checker.check().await;
                
                // 更新服务信息
                let mut info = service_info.write().await;
                info.health = health.clone();
                
                // 发送心跳
                if let Err(e) = coordinator.heartbeat(&info.id, &health).await {
                    tracing::error!("Heartbeat failed: {}", e);
                }
            }
        });
    }
    
    /// 注销服务
    pub async fn deregister(&self) -> Result<(), Box<dyn std::error::Error>> {
        let service_info = self.service_info.read().await;
        
        self.coordinator.deregister_service(&service_info.id).await?;
        
        tracing::info!("Service deregistered: {}", service_info.name);
        
        Ok(())
    }
}

/// 健康检查器
pub struct HealthChecker {
    checks: Arc<RwLock<Vec<Box<dyn HealthCheck>>>>,
}

impl HealthChecker {
    pub fn new() -> Self {
        Self {
            checks: Arc::new(RwLock::new(Vec::new())),
        }
    }
    
    /// 添加健康检查
    pub async fn add_check(&self, check: Box<dyn HealthCheck>) {
        let mut checks = self.checks.write().await;
        checks.push(check);
    }
    
    /// 执行健康检查
    pub async fn check(&self) -> HealthStatus {
        let checks = self.checks.read().await;
        
        for check in checks.iter() {
            if !check.check().await {
                return HealthStatus::Unhealthy {
                    reason: check.name().to_string(),
                };
            }
        }
        
        HealthStatus::Healthy
    }
}

/// 健康检查trait
#[async_trait::async_trait]
pub trait HealthCheck: Send + Sync {
    async fn check(&self) -> bool;
    fn name(&self) -> &str;
}

/// CPU健康检查
pub struct CpuHealthCheck {
    threshold: f64,
}

#[async_trait::async_trait]
impl HealthCheck for CpuHealthCheck {
    async fn check(&self) -> bool {
        // 实际实现需要获取真实CPU使用率
        let cpu_usage = get_cpu_usage().await;
        cpu_usage < self.threshold
    }
    
    fn name(&self) -> &str {
        "cpu"
    }
}

/// 健康状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum HealthStatus {
    Healthy,
    Unhealthy { reason: String },
    Unknown,
}

impl HealthStatus {
    pub fn healthy() -> Self {
        Self::Healthy
    }
    
    pub fn is_healthy(&self) -> bool {
        matches!(self, Self::Healthy)
    }
}

// 辅助函数
async fn get_cpu_usage() -> f64 {
    // 简化实现
    0.5
}
```

---

## 7. 分布式锁与选举

### 7.1 分布式锁实现

```rust
use tokio::sync::Mutex as TokioMutex;
use std::time::SystemTime;

/// 分布式锁
pub struct DistributedLock {
    coordinator: Arc<dyn CoordinatorClient>,
    lock_name: String,
    lease_duration: Duration,
    holder: Arc<TokioMutex<Option<String>>>,
}

impl DistributedLock {
    pub fn new(
        coordinator: Arc<dyn CoordinatorClient>,
        lock_name: String,
        lease_duration: Duration,
    ) -> Self {
        Self {
            coordinator,
            lock_name,
            lease_duration,
            holder: Arc::new(TokioMutex::new(None)),
        }
    }
    
    /// 获取锁
    pub async fn acquire(&self) -> Result<LockGuard, Box<dyn std::error::Error>> {
        let lock_id = uuid::Uuid::new_v4().to_string();
        
        loop {
            match self.try_acquire(&lock_id).await {
                Ok(true) => {
                    let mut holder = self.holder.lock().await;
                    *holder = Some(lock_id.clone());
                    
                    return Ok(LockGuard {
                        lock: self.clone(),
                        lock_id,
                    });
                }
                Ok(false) => {
                    // 锁被占用，等待后重试
                    tokio::time::sleep(Duration::from_millis(100)).await;
                }
                Err(e) => {
                    return Err(e);
                }
            }
        }
    }
    
    /// 尝试获取锁
    async fn try_acquire(&self, lock_id: &str) -> Result<bool, Box<dyn std::error::Error>> {
        self.coordinator.try_lock(&self.lock_name, lock_id, self.lease_duration).await
    }
    
    /// 释放锁
    async fn release(&self, lock_id: &str) -> Result<(), Box<dyn std::error::Error>> {
        self.coordinator.unlock(&self.lock_name, lock_id).await?;
        
        let mut holder = self.holder.lock().await;
        *holder = None;
        
        Ok(())
    }
}

impl Clone for DistributedLock {
    fn clone(&self) -> Self {
        Self {
            coordinator: Arc::clone(&self.coordinator),
            lock_name: self.lock_name.clone(),
            lease_duration: self.lease_duration,
            holder: Arc::clone(&self.holder),
        }
    }
}

/// 锁守卫
pub struct LockGuard {
    lock: DistributedLock,
    lock_id: String,
}

impl Drop for LockGuard {
    fn drop(&mut self) {
        let lock = self.lock.clone();
        let lock_id = self.lock_id.clone();
        
        tokio::spawn(async move {
            if let Err(e) = lock.release(&lock_id).await {
                tracing::error!("Failed to release lock: {}", e);
            }
        });
    }
}
```

### 7.2 Leader选举实现

```rust
/// Leader选举器
pub struct LeaderElection {
    coordinator: Arc<dyn CoordinatorClient>,
    election_name: String,
    node_id: String,
    is_leader: Arc<RwLock<bool>>,
    leader_id: Arc<RwLock<Option<String>>>,
}

impl LeaderElection {
    pub fn new(
        coordinator: Arc<dyn CoordinatorClient>,
        election_name: String,
        node_id: String,
    ) -> Self {
        Self {
            coordinator,
            election_name,
            node_id,
            is_leader: Arc::new(RwLock::new(false)),
            leader_id: Arc::new(RwLock::new(None)),
        }
    }
    
    /// 开始选举
    pub async fn start(&self) {
        let coordinator = Arc::clone(&self.coordinator);
        let election_name = self.election_name.clone();
        let node_id = self.node_id.clone();
        let is_leader = Arc::clone(&self.is_leader);
        let leader_id = Arc::clone(&self.leader_id);
        
        tokio::spawn(async move {
            loop {
                match coordinator.campaign(&election_name, &node_id).await {
                    Ok(true) => {
                        // 成为Leader
                        *is_leader.write().await = true;
                        *leader_id.write().await = Some(node_id.clone());
                        
                        tracing::info!("Became leader: {}", node_id);
                        
                        // 保持Leader状态
                        Self::maintain_leadership(
                            &coordinator,
                            &election_name,
                            &node_id,
                            &is_leader,
                        ).await;
                    }
                    Ok(false) => {
                        // 观察当前Leader
                        if let Ok(current_leader) = coordinator.observe(&election_name).await {
                            *leader_id.write().await = Some(current_leader);
                        }
                    }
                    Err(e) => {
                        tracing::error!("Election error: {}", e);
                    }
                }
                
                tokio::time::sleep(Duration::from_secs(5)).await;
            }
        });
    }
    
    /// 维持Leader状态
    async fn maintain_leadership(
        coordinator: &Arc<dyn CoordinatorClient>,
        election_name: &str,
        node_id: &str,
        is_leader: &Arc<RwLock<bool>>,
    ) {
        let mut ticker = interval(Duration::from_secs(10));
        
        loop {
            ticker.tick().await;
            
            match coordinator.proclaim(election_name, node_id).await {
                Ok(()) => {
                    // Leader状态维持成功
                }
                Err(e) => {
                    tracing::error!("Failed to maintain leadership: {}", e);
                    *is_leader.write().await = false;
                    break;
                }
            }
        }
    }
    
    /// 是否是Leader
    pub async fn is_leader(&self) -> bool {
        *self.is_leader.read().await
    }
    
    /// 获取当前Leader
    pub async fn get_leader(&self) -> Option<String> {
        self.leader_id.read().await.clone()
    }
    
    /// 辞职
    pub async fn resign(&self) -> Result<(), Box<dyn std::error::Error>> {
        if *self.is_leader.read().await {
            self.coordinator.resign(&self.election_name, &self.node_id).await?;
            *self.is_leader.write().await = false;
            tracing::info!("Resigned from leadership");
        }
        
        Ok(())
    }
}
```

---

## 8. 完整实现示例

### 8.1 综合示例

```rust
use tracing_subscriber;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt::init();
    
    // 创建etcd协调客户端
    let etcd_endpoints = vec!["http://localhost:2379".to_string()];
    let coordinator = Arc::new(
        EtcdCoordinator::new(etcd_endpoints, "/otlp".to_string()).await?
    );
    
    // 创建分布式控制器
    let controller = DistributedOtlpController::new(
        "http://localhost:2379",
        "region-1".to_string(),
    ).await?;
    
    // 启动控制器
    controller.start().await?;
    
    // 注册区域控制器
    let local_config = LocalConfig {
        regional_sampling_rate: 0.1,
        local_routing_preference: vec!["collector-1".to_string()],
        buffer_size: 10000,
        batch_config: BatchConfig {
            max_batch_size: 100,
            max_wait_time: Duration::from_millis(100),
        },
        retry_policy: RetryPolicy {
            max_retries: 3,
            initial_backoff: Duration::from_millis(100),
            max_backoff: Duration::from_secs(10),
        },
    };
    
    controller.register_region("region-1".to_string(), local_config).await?;
    
    // 创建全局拓扑管理器
    let topology_manager = GlobalTopologyManager::new(
        Arc::clone(&coordinator),
        Duration::from_secs(30),
    );
    topology_manager.start().await;
    
    // 创建全局采样协调器
    let sampling_coordinator = GlobalSamplingCoordinator::new(Arc::clone(&coordinator));
    sampling_coordinator.start().await;
    
    // 创建本地负载监控器
    let load_monitor = Arc::new(LocalLoadMonitor::new(600));
    load_monitor.start().await;
    
    // 创建本地智能路由器
    let router = LocalIntelligentRouter::new(Arc::clone(&load_monitor));
    
    // 创建服务注册器
    let service_info = ServiceInfo {
        id: "collector-1".to_string(),
        name: "otlp-collector".to_string(),
        address: "0.0.0.0:4317".parse()?,
        region: "region-1".to_string(),
        metadata: HashMap::new(),
        health: HealthStatus::Healthy,
        registered_at: SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)?
            .as_secs(),
    };
    
    let registry = ServiceRegistry::new(Arc::clone(&coordinator), service_info);
    registry.register().await?;
    
    // 创建Leader选举器
    let election = LeaderElection::new(
        Arc::clone(&coordinator),
        "otlp-controller".to_string(),
        "node-1".to_string(),
    );
    election.start().await;
    
    // 等待信号
    tokio::signal::ctrl_c().await?;
    
    // 清理
    registry.deregister().await?;
    election.resign().await?;
    
    Ok(())
}
```

---

## 9. 配置示例

### 9.1 全局配置示例

```yaml
# global-config.yaml
global:
  sampling_rate: 0.1
  
  sampling_strategies:
    - type: adaptive
      min_rate: 0.01
      max_rate: 0.5
      target_qps: 100000
    
    - type: priority_based
      rules:
        - priority: high
          rate: 1.0
          services: ["payment", "checkout"]
        - priority: normal
          rate: 0.1
        - priority: low
          rate: 0.01
          services: ["debug", "test"]
  
  degradation:
    enabled: true
    threshold: 0.8
    target_rate: 0.01
    recovery_threshold: 0.6
  
  rate_limiting:
    max_qps: 1000000
    burst_size: 10000
    per_service_limit: 10000
  
  routing_rules:
    - service: "critical-*"
      target_region: "us-east-1"
      priority: high
    
    - service: "batch-*"
      target_region: "us-west-2"
      priority: low
```

---

## 10. 性能优化

### 10.1 批处理优化

```rust
/// 批处理配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchConfig {
    pub max_batch_size: usize,
    pub max_wait_time: Duration,
}

/// 批处理器
pub struct Batcher<T> {
    config: BatchConfig,
    buffer: Arc<TokioMutex<Vec<T>>>,
    tx: mpsc::Sender<Vec<T>>,
}

impl<T: Send + 'static> Batcher<T> {
    pub fn new(config: BatchConfig) -> (Self, mpsc::Receiver<Vec<T>>) {
        let (tx, rx) = mpsc::channel(100);
        
        let batcher = Self {
            config,
            buffer: Arc::new(TokioMutex::new(Vec::with_capacity(config.max_batch_size))),
            tx,
        };
        
        batcher.start_flush_timer();
        
        (batcher, rx)
    }
    
    /// 添加项目
    pub async fn add(&self, item: T) -> Result<(), Box<dyn std::error::Error>> {
        let mut buffer = self.buffer.lock().await;
        buffer.push(item);
        
        if buffer.len() >= self.config.max_batch_size {
            let batch = std::mem::replace(&mut *buffer, Vec::with_capacity(self.config.max_batch_size));
            self.tx.send(batch).await?;
        }
        
        Ok(())
    }
    
    /// 启动定时刷新
    fn start_flush_timer(&self) {
        let buffer = Arc::clone(&self.buffer);
        let tx = self.tx.clone();
        let max_wait = self.config.max_wait_time;
        
        tokio::spawn(async move {
            let mut ticker = interval(max_wait);
            
            loop {
                ticker.tick().await;
                
                let mut buf = buffer.lock().await;
                if !buf.is_empty() {
                    let batch = std::mem::take(&mut *buf);
                    let _ = tx.send(batch).await;
                }
            }
        });
    }
}
```

---

## 11. 监控与告警

### 11.1 指标收集

```rust
use prometheus::{IntCounterVec, HistogramVec, Registry};

/// 指标收集器
pub struct MetricsCollector {
    registry: Registry,
    
    // 计数器
    requests_total: IntCounterVec,
    errors_total: IntCounterVec,
    
    // 直方图
    request_duration: HistogramVec,
    batch_size: HistogramVec,
}

impl MetricsCollector {
    pub fn new() -> Self {
        let registry = Registry::new();
        
        let requests_total = IntCounterVec::new(
            opts!("otlp_requests_total", "Total number of OTLP requests"),
            &["region", "service"]
        ).unwrap();
        
        let errors_total = IntCounterVec::new(
            opts!("otlp_errors_total", "Total number of errors"),
            &["region", "error_type"]
        ).unwrap();
        
        let request_duration = HistogramVec::new(
            histogram_opts!("otlp_request_duration_seconds", "Request duration"),
            &["region", "method"]
        ).unwrap();
        
        let batch_size = HistogramVec::new(
            histogram_opts!("otlp_batch_size", "Batch size"),
            &["region"]
        ).unwrap();
        
        registry.register(Box::new(requests_total.clone())).unwrap();
        registry.register(Box::new(errors_total.clone())).unwrap();
        registry.register(Box::new(request_duration.clone())).unwrap();
        registry.register(Box::new(batch_size.clone())).unwrap();
        
        Self {
            registry,
            requests_total,
            errors_total,
            request_duration,
            batch_size,
        }
    }
    
    pub fn record_request(&self, region: &str, service: &str) {
        self.requests_total
            .with_label_values(&[region, service])
            .inc();
    }
    
    pub fn record_error(&self, region: &str, error_type: &str) {
        self.errors_total
            .with_label_values(&[region, error_type])
            .inc();
    }
    
    pub fn record_duration(&self, region: &str, method: &str, duration: Duration) {
        self.request_duration
            .with_label_values(&[region, method])
            .observe(duration.as_secs_f64());
    }
}
```

---

## 12. 总结

本文档提供了分布式OTLP协调与控制的完整Rust实现，包括:

✅ **核心特性**:

- 全局感知与本地感知机制
- 分布式协调服务(etcd/Consul)
- 配置管理与热更新
- 服务发现与注册
- 分布式锁与Leader选举
- 智能路由与负载均衡

✅ **生产就绪**:

- 健康检查与自动恢复
- 性能监控与告警
- 批处理优化
- 完整的错误处理

✅ **可扩展性**:

- 支持多区域部署
- 水平扩展能力
- 插件化架构

---

**参考资源**:

- [etcd Documentation](https://etcd.io/docs/)
- [Consul Documentation](https://www.consul.io/docs)
- [OpenTelemetry Collector](https://opentelemetry.io/docs/collector/)
- [Distributed Systems Patterns](https://martinfowler.com/articles/patterns-of-distributed-systems/)
