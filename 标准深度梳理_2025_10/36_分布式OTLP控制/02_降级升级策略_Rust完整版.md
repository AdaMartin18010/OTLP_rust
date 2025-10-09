# OTLP降级与升级策略 - Rust完整实现

> **Rust版本**: 1.90+  
> **核心依赖**: tokio 1.47.1, governor 0.7  
> **OpenTelemetry**: 0.31.0  
> **最后更新**: 2025年10月9日

---

## 📋 目录

- [OTLP降级与升级策略 - Rust完整实现](#otlp降级与升级策略---rust完整实现)
  - [📋 目录](#-目录)
  - [1. 降级策略概述](#1-降级策略概述)
    - [1.1 降级场景](#11-降级场景)
    - [1.2 降级策略](#12-降级策略)
  - [2. 自适应降级](#2-自适应降级)
    - [2.1 CPU触发器](#21-cpu触发器)
    - [2.2 内存触发器](#22-内存触发器)
    - [2.3 延迟触发器](#23-延迟触发器)
  - [3. 限流与熔断](#3-限流与熔断)
    - [3.1 令牌桶限流器](#31-令牌桶限流器)
    - [3.2 熔断器](#32-熔断器)
  - [4. 平滑升级策略](#4-平滑升级策略)
    - [4.1 滚动升级](#41-滚动升级)
  - [5. 灰度发布](#5-灰度发布)
    - [5.1 金丝雀发布](#51-金丝雀发布)
  - [6. 完整实现](#6-完整实现)
    - [6.1 综合示例](#61-综合示例)
  - [总结](#总结)

---

## 1. 降级策略概述

### 1.1 降级场景

```text
降级触发条件:

1. 过载保护
   - CPU使用率 > 80%
   - 内存使用率 > 85%
   - 队列深度 > 阈值

2. 服务质量下降
   - 延迟 > SLA
   - 错误率 > 阈值
   - 超时率 > 阈值

3. 成本控制
   - 超出预算
   - 配额不足

4. 故障恢复
   - 部分节点故障
   - 网络分区
```

### 1.2 降级策略

```rust
use std::sync::Arc;
use tokio::sync::RwLock;
use std::time::{Duration, Instant};

/// 降级控制器
pub struct DegradationController {
    /// 当前降级级别
    current_level: Arc<RwLock<DegradationLevel>>,
    
    /// 降级配置
    config: Arc<RwLock<DegradationConfig>>,
    
    /// 指标收集器
    metrics: Arc<MetricsCollector>,
    
    /// 触发器
    triggers: Arc<RwLock<Vec<Box<dyn DegradationTrigger>>>>,
    
    /// 状态历史
    history: Arc<RwLock<CircularBuffer<DegradationEvent>>>,
}

/// 降级级别
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum DegradationLevel {
    /// 正常
    Normal = 0,
    
    /// 轻度降级 (采样率 50%)
    Light = 1,
    
    /// 中度降级 (采样率 10%)
    Moderate = 2,
    
    /// 重度降级 (采样率 1%)
    Heavy = 3,
    
    /// 紧急降级 (仅错误追踪)
    Emergency = 4,
}

/// 降级配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DegradationConfig {
    /// 启用降级
    pub enabled: bool,
    
    /// CPU阈值
    pub cpu_threshold: f64,
    
    /// 内存阈值
    pub memory_threshold: f64,
    
    /// 延迟阈值(毫秒)
    pub latency_threshold_ms: f64,
    
    /// 错误率阈值
    pub error_rate_threshold: f64,
    
    /// 队列深度阈值
    pub queue_depth_threshold: usize,
    
    /// 恢复阈值
    pub recovery_threshold: f64,
    
    /// 评估间隔
    pub evaluation_interval: Duration,
    
    /// 降级策略
    pub strategies: Vec<DegradationStrategy>,
}

/// 降级策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DegradationStrategy {
    /// 降低采样率
    ReduceSamplingRate {
        target_rate: f64,
    },
    
    /// 禁用非关键追踪
    DisableNonCritical {
        critical_services: Vec<String>,
    },
    
    /// 增加批处理大小
    IncreaseBatchSize {
        target_size: usize,
    },
    
    /// 延长批处理等待时间
    IncreaseBatchWait {
        target_wait: Duration,
    },
    
    /// 禁用详细属性
    DisableVerboseAttributes,
    
    /// 仅追踪错误
    ErrorsOnly,
}

impl DegradationController {
    pub fn new(
        config: DegradationConfig,
        metrics: Arc<MetricsCollector>,
    ) -> Self {
        Self {
            current_level: Arc::new(RwLock::new(DegradationLevel::Normal)),
            config: Arc::new(RwLock::new(config)),
            metrics,
            triggers: Arc::new(RwLock::new(Vec::new())),
            history: Arc::new(RwLock::new(CircularBuffer::new(1000))),
        }
    }
    
    /// 启动降级控制器
    pub async fn start(&self) {
        self.start_evaluator().await;
        self.start_recovery_monitor().await;
    }
    
    /// 启动评估器
    async fn start_evaluator(&self) {
        let current_level = Arc::clone(&self.current_level);
        let config = Arc::clone(&self.config);
        let metrics = Arc::clone(&self.metrics);
        let triggers = Arc::clone(&self.triggers);
        let history = Arc::clone(&self.history);
        
        tokio::spawn(async move {
            loop {
                let cfg = config.read().await;
                let interval = cfg.evaluation_interval;
                drop(cfg);
                
                tokio::time::sleep(interval).await;
                
                // 评估当前状态
                let triggers_list = triggers.read().await;
                let mut max_level = DegradationLevel::Normal;
                
                for trigger in triggers_list.iter() {
                    if let Some(level) = trigger.evaluate().await {
                        max_level = max_level.max(level);
                    }
                }
                
                // 更新降级级别
                let mut current = current_level.write().await;
                if *current != max_level {
                    let event = DegradationEvent {
                        timestamp: Instant::now(),
                        from_level: *current,
                        to_level: max_level,
                        reason: "Automatic evaluation".to_string(),
                    };
                    
                    *current = max_level;
                    
                    let mut hist = history.write().await;
                    hist.push(event);
                    
                    tracing::warn!(
                        "Degradation level changed: {:?} -> {:?}",
                        event.from_level,
                        event.to_level
                    );
                    
                    // 记录指标
                    metrics.record_degradation_change(event.to_level as i64);
                }
            }
        });
    }
    
    /// 启动恢复监控
    async fn start_recovery_monitor(&self) {
        let current_level = Arc::clone(&self.current_level);
        let config = Arc::clone(&self.config);
        let metrics = Arc::clone(&self.metrics);
        let history = Arc::clone(&self.history);
        
        tokio::spawn(async move {
            let mut ticker = tokio::time::interval(Duration::from_secs(30));
            
            loop {
                ticker.tick().await;
                
                let level = *current_level.read().await;
                
                if level == DegradationLevel::Normal {
                    continue;
                }
                
                // 检查是否可以恢复
                let cfg = config.read().await;
                let can_recover = Self::check_recovery_conditions(&metrics, cfg.recovery_threshold).await;
                
                if can_recover {
                    let new_level = match level {
                        DegradationLevel::Emergency => DegradationLevel::Heavy,
                        DegradationLevel::Heavy => DegradationLevel::Moderate,
                        DegradationLevel::Moderate => DegradationLevel::Light,
                        DegradationLevel::Light => DegradationLevel::Normal,
                        DegradationLevel::Normal => DegradationLevel::Normal,
                    };
                    
                    let mut current = current_level.write().await;
                    
                    let event = DegradationEvent {
                        timestamp: Instant::now(),
                        from_level: *current,
                        to_level: new_level,
                        reason: "Automatic recovery".to_string(),
                    };
                    
                    *current = new_level;
                    
                    let mut hist = history.write().await;
                    hist.push(event);
                    
                    tracing::info!(
                        "Degradation level recovered: {:?} -> {:?}",
                        event.from_level,
                        event.to_level
                    );
                    
                    metrics.record_degradation_change(new_level as i64);
                }
            }
        });
    }
    
    /// 检查恢复条件
    async fn check_recovery_conditions(
        metrics: &Arc<MetricsCollector>,
        threshold: f64,
    ) -> bool {
        let load = metrics.get_current_load().await;
        
        load.cpu_usage < threshold &&
        load.memory_usage < threshold &&
        load.error_rate < 0.01 &&
        load.avg_latency_ms < 100.0
    }
    
    /// 获取当前降级级别
    pub async fn get_current_level(&self) -> DegradationLevel {
        *self.current_level.read().await
    }
    
    /// 获取推荐采样率
    pub async fn get_recommended_sampling_rate(&self) -> f64 {
        match *self.current_level.read().await {
            DegradationLevel::Normal => 1.0,
            DegradationLevel::Light => 0.5,
            DegradationLevel::Moderate => 0.1,
            DegradationLevel::Heavy => 0.01,
            DegradationLevel::Emergency => 0.001,
        }
    }
    
    /// 是否应该追踪
    pub async fn should_trace(&self, service_name: &str, is_error: bool) -> bool {
        let level = *self.current_level.read().await;
        
        match level {
            DegradationLevel::Normal => true,
            DegradationLevel::Light | DegradationLevel::Moderate => {
                is_error || self.is_critical_service(service_name).await
            }
            DegradationLevel::Heavy | DegradationLevel::Emergency => is_error,
        }
    }
    
    async fn is_critical_service(&self, service_name: &str) -> bool {
        let config = self.config.read().await;
        
        for strategy in &config.strategies {
            if let DegradationStrategy::DisableNonCritical { critical_services } = strategy {
                return critical_services.contains(&service_name.to_string());
            }
        }
        
        false
    }
}

/// 降级事件
#[derive(Debug, Clone)]
pub struct DegradationEvent {
    pub timestamp: Instant,
    pub from_level: DegradationLevel,
    pub to_level: DegradationLevel,
    pub reason: String,
}

/// 降级触发器trait
#[async_trait::async_trait]
pub trait DegradationTrigger: Send + Sync {
    async fn evaluate(&self) -> Option<DegradationLevel>;
    fn name(&self) -> &str;
}
```

---

## 2. 自适应降级

### 2.1 CPU触发器

```rust
use sysinfo::{System, SystemExt};

/// CPU触发器
pub struct CpuTrigger {
    system: Arc<RwLock<System>>,
    thresholds: CpuThresholds,
}

#[derive(Debug, Clone)]
pub struct CpuThresholds {
    pub light: f64,
    pub moderate: f64,
    pub heavy: f64,
    pub emergency: f64,
}

impl CpuTrigger {
    pub fn new(thresholds: CpuThresholds) -> Self {
        Self {
            system: Arc::new(RwLock::new(System::new_all())),
            thresholds,
        }
    }
}

#[async_trait::async_trait]
impl DegradationTrigger for CpuTrigger {
    async fn evaluate(&self) -> Option<DegradationLevel> {
        let mut sys = self.system.write().await;
        sys.refresh_cpu();
        
        // 等待一小段时间以获取准确的CPU使用率
        tokio::time::sleep(Duration::from_millis(200)).await;
        sys.refresh_cpu();
        
        let cpu_usage = sys.global_cpu_info().cpu_usage() as f64;
        
        let level = if cpu_usage >= self.thresholds.emergency {
            DegradationLevel::Emergency
        } else if cpu_usage >= self.thresholds.heavy {
            DegradationLevel::Heavy
        } else if cpu_usage >= self.thresholds.moderate {
            DegradationLevel::Moderate
        } else if cpu_usage >= self.thresholds.light {
            DegradationLevel::Light
        } else {
            DegradationLevel::Normal
        };
        
        if level > DegradationLevel::Normal {
            tracing::warn!("CPU trigger activated: usage={:.2}%, level={:?}", cpu_usage, level);
            Some(level)
        } else {
            None
        }
    }
    
    fn name(&self) -> &str {
        "cpu"
    }
}
```

### 2.2 内存触发器

```rust
/// 内存触发器
pub struct MemoryTrigger {
    system: Arc<RwLock<System>>,
    thresholds: MemoryThresholds,
}

#[derive(Debug, Clone)]
pub struct MemoryThresholds {
    pub light: f64,
    pub moderate: f64,
    pub heavy: f64,
    pub emergency: f64,
}

impl MemoryTrigger {
    pub fn new(thresholds: MemoryThresholds) -> Self {
        Self {
            system: Arc::new(RwLock::new(System::new_all())),
            thresholds,
        }
    }
}

#[async_trait::async_trait]
impl DegradationTrigger for MemoryTrigger {
    async fn evaluate(&self) -> Option<DegradationLevel> {
        let mut sys = self.system.write().await;
        sys.refresh_memory();
        
        let total_memory = sys.total_memory();
        let used_memory = sys.used_memory();
        let memory_usage = (used_memory as f64 / total_memory as f64) * 100.0;
        
        let level = if memory_usage >= self.thresholds.emergency {
            DegradationLevel::Emergency
        } else if memory_usage >= self.thresholds.heavy {
            DegradationLevel::Heavy
        } else if memory_usage >= self.thresholds.moderate {
            DegradationLevel::Moderate
        } else if memory_usage >= self.thresholds.light {
            DegradationLevel::Light
        } else {
            DegradationLevel::Normal
        };
        
        if level > DegradationLevel::Normal {
            tracing::warn!("Memory trigger activated: usage={:.2}%, level={:?}", memory_usage, level);
            Some(level)
        } else {
            None
        }
    }
    
    fn name(&self) -> &str {
        "memory"
    }
}
```

### 2.3 延迟触发器

```rust
/// 延迟触发器
pub struct LatencyTrigger {
    metrics: Arc<MetricsCollector>,
    thresholds: LatencyThresholds,
}

#[derive(Debug, Clone)]
pub struct LatencyThresholds {
    pub light_ms: f64,
    pub moderate_ms: f64,
    pub heavy_ms: f64,
    pub emergency_ms: f64,
}

impl LatencyTrigger {
    pub fn new(metrics: Arc<MetricsCollector>, thresholds: LatencyThresholds) -> Self {
        Self {
            metrics,
            thresholds,
        }
    }
}

#[async_trait::async_trait]
impl DegradationTrigger for LatencyTrigger {
    async fn evaluate(&self) -> Option<DegradationLevel> {
        let load = self.metrics.get_current_load().await;
        let latency_ms = load.avg_latency_ms;
        
        let level = if latency_ms >= self.thresholds.emergency_ms {
            DegradationLevel::Emergency
        } else if latency_ms >= self.thresholds.heavy_ms {
            DegradationLevel::Heavy
        } else if latency_ms >= self.thresholds.moderate_ms {
            DegradationLevel::Moderate
        } else if latency_ms >= self.thresholds.light_ms {
            DegradationLevel::Light
        } else {
            DegradationLevel::Normal
        };
        
        if level > DegradationLevel::Normal {
            tracing::warn!("Latency trigger activated: latency={:.2}ms, level={:?}", latency_ms, level);
            Some(level)
        } else {
            None
        }
    }
    
    fn name(&self) -> &str {
        "latency"
    }
}
```

---

## 3. 限流与熔断

### 3.1 令牌桶限流器

```rust
use governor::{Quota, RateLimiter as GovernorRateLimiter};
use governor::state::{InMemoryState, NotKeyed};
use governor::clock::DefaultClock;
use nonzero_ext::*;

/// 限流器
pub struct RateLimiter {
    limiter: Arc<GovernorRateLimiter<NotKeyed, InMemoryState, DefaultClock>>,
    max_qps: u64,
    burst_size: u32,
}

impl RateLimiter {
    pub fn new(max_qps: u64, burst_size: u32) -> Self {
        let quota = Quota::per_second(nonzero!(max_qps as u32))
            .allow_burst(nonzero!(burst_size));
        
        let limiter = Arc::new(GovernorRateLimiter::direct(quota));
        
        Self {
            limiter,
            max_qps,
            burst_size,
        }
    }
    
    /// 检查是否允许通过
    pub fn check(&self) -> bool {
        self.limiter.check().is_ok()
    }
    
    /// 异步等待直到允许通过
    pub async fn wait(&self) {
        self.limiter.until_ready().await;
    }
    
    /// 更新限流配置
    pub fn update(&mut self, max_qps: u64, burst_size: u32) {
        let quota = Quota::per_second(nonzero!(max_qps as u32))
            .allow_burst(nonzero!(burst_size));
        
        self.limiter = Arc::new(GovernorRateLimiter::direct(quota));
        self.max_qps = max_qps;
        self.burst_size = burst_size;
        
        tracing::info!("Rate limiter updated: max_qps={}, burst={}", max_qps, burst_size);
    }
}
```

### 3.2 熔断器

```rust
use std::sync::atomic::{AtomicU64, AtomicBool, Ordering};

/// 熔断器
pub struct CircuitBreaker {
    /// 熔断器状态
    state: Arc<RwLock<CircuitState>>,
    
    /// 配置
    config: CircuitBreakerConfig,
    
    /// 统计
    stats: Arc<CircuitStats>,
}

/// 熔断器状态
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CircuitState {
    /// 关闭(正常)
    Closed,
    
    /// 打开(熔断)
    Open,
    
    /// 半开(试探)
    HalfOpen,
}

/// 熔断器配置
#[derive(Debug, Clone)]
pub struct CircuitBreakerConfig {
    /// 失败阈值
    pub failure_threshold: u64,
    
    /// 成功阈值(半开状态)
    pub success_threshold: u64,
    
    /// 超时时间
    pub timeout: Duration,
    
    /// 半开超时
    pub half_open_timeout: Duration,
}

/// 熔断器统计
#[derive(Debug)]
struct CircuitStats {
    total_requests: AtomicU64,
    failed_requests: AtomicU64,
    successful_requests: AtomicU64,
    last_failure_time: RwLock<Option<Instant>>,
}

impl CircuitBreaker {
    pub fn new(config: CircuitBreakerConfig) -> Self {
        Self {
            state: Arc::new(RwLock::new(CircuitState::Closed)),
            config,
            stats: Arc::new(CircuitStats {
                total_requests: AtomicU64::new(0),
                failed_requests: AtomicU64::new(0),
                successful_requests: AtomicU64::new(0),
                last_failure_time: RwLock::new(None),
            }),
        }
    }
    
    /// 检查是否允许请求
    pub async fn allow_request(&self) -> bool {
        let state = *self.state.read().await;
        
        match state {
            CircuitState::Closed => true,
            
            CircuitState::Open => {
                // 检查是否可以进入半开状态
                let last_failure = self.stats.last_failure_time.read().await;
                if let Some(last_time) = *last_failure {
                    if last_time.elapsed() >= self.config.timeout {
                        drop(last_failure);
                        let mut state_mut = self.state.write().await;
                        *state_mut = CircuitState::HalfOpen;
                        
                        tracing::info!("Circuit breaker transitioning to HalfOpen");
                        return true;
                    }
                }
                false
            }
            
            CircuitState::HalfOpen => {
                // 半开状态允许少量请求
                true
            }
        }
    }
    
    /// 记录成功
    pub async fn record_success(&self) {
        self.stats.total_requests.fetch_add(1, Ordering::Relaxed);
        self.stats.successful_requests.fetch_add(1, Ordering::Relaxed);
        
        let state = *self.state.read().await;
        
        if state == CircuitState::HalfOpen {
            let success_count = self.stats.successful_requests.load(Ordering::Relaxed);
            
            if success_count >= self.config.success_threshold {
                drop(state);
                let mut state_mut = self.state.write().await;
                *state_mut = CircuitState::Closed;
                
                // 重置统计
                self.stats.failed_requests.store(0, Ordering::Relaxed);
                self.stats.successful_requests.store(0, Ordering::Relaxed);
                
                tracing::info!("Circuit breaker closed");
            }
        }
    }
    
    /// 记录失败
    pub async fn record_failure(&self) {
        self.stats.total_requests.fetch_add(1, Ordering::Relaxed);
        self.stats.failed_requests.fetch_add(1, Ordering::Relaxed);
        
        let mut last_failure = self.stats.last_failure_time.write().await;
        *last_failure = Some(Instant::now());
        drop(last_failure);
        
        let state = *self.state.read().await;
        
        match state {
            CircuitState::Closed => {
                let failed_count = self.stats.failed_requests.load(Ordering::Relaxed);
                
                if failed_count >= self.config.failure_threshold {
                    drop(state);
                    let mut state_mut = self.state.write().await;
                    *state_mut = CircuitState::Open;
                    
                    tracing::warn!("Circuit breaker opened due to failures: {}", failed_count);
                }
            }
            
            CircuitState::HalfOpen => {
                // 半开状态下失败，直接打开
                drop(state);
                let mut state_mut = self.state.write().await;
                *state_mut = CircuitState::Open;
                
                tracing::warn!("Circuit breaker reopened from HalfOpen");
            }
            
            CircuitState::Open => {
                // 已经打开，无需操作
            }
        }
    }
    
    /// 获取当前状态
    pub async fn get_state(&self) -> CircuitState {
        *self.state.read().await
    }
}
```

---

## 4. 平滑升级策略

### 4.1 滚动升级

```rust
/// 滚动升级控制器
pub struct RollingUpgradeController {
    /// 实例列表
    instances: Arc<RwLock<Vec<Instance>>>,
    
    /// 升级配置
    config: RollingUpgradeConfig,
    
    /// 健康检查器
    health_checker: Arc<HealthChecker>,
}

/// 升级配置
#[derive(Debug, Clone)]
pub struct RollingUpgradeConfig {
    /// 批次大小
    pub batch_size: usize,
    
    /// 批次间等待时间
    pub batch_wait: Duration,
    
    /// 健康检查间隔
    pub health_check_interval: Duration,
    
    /// 最大并发升级数
    pub max_concurrent: usize,
    
    /// 回滚阈值
    pub rollback_threshold: f64,
}

/// 实例
#[derive(Debug, Clone)]
pub struct Instance {
    pub id: String,
    pub address: String,
    pub version: String,
    pub status: InstanceStatus,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InstanceStatus {
    Running,
    Upgrading,
    Draining,
    Stopped,
    Failed,
}

impl RollingUpgradeController {
    pub fn new(
        instances: Vec<Instance>,
        config: RollingUpgradeConfig,
        health_checker: Arc<HealthChecker>,
    ) -> Self {
        Self {
            instances: Arc::new(RwLock::new(instances)),
            config,
            health_checker,
        }
    }
    
    /// 执行滚动升级
    pub async fn execute_upgrade(&self, target_version: String) -> Result<(), Box<dyn std::error::Error>> {
        let instances = self.instances.read().await;
        let total = instances.len();
        let batches = (total + self.config.batch_size - 1) / self.config.batch_size;
        
        tracing::info!(
            "Starting rolling upgrade to version {}: {} instances in {} batches",
            target_version,
            total,
            batches
        );
        
        for batch_idx in 0..batches {
            let start_idx = batch_idx * self.config.batch_size;
            let end_idx = ((batch_idx + 1) * self.config.batch_size).min(total);
            
            tracing::info!("Upgrading batch {}/{}: instances {}-{}", batch_idx + 1, batches, start_idx, end_idx);
            
            // 升级当前批次
            self.upgrade_batch(start_idx, end_idx, &target_version).await?;
            
            // 健康检查
            if !self.check_batch_health(start_idx, end_idx).await? {
                tracing::error!("Health check failed for batch {}, initiating rollback", batch_idx + 1);
                self.rollback(batch_idx, &target_version).await?;
                return Err("Upgrade failed, rolled back".into());
            }
            
            // 等待下一批次
            if batch_idx < batches - 1 {
                tokio::time::sleep(self.config.batch_wait).await;
            }
        }
        
        tracing::info!("Rolling upgrade completed successfully");
        Ok(())
    }
    
    /// 升级批次
    async fn upgrade_batch(
        &self,
        start: usize,
        end: usize,
        target_version: &str,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut instances = self.instances.write().await;
        let batch: Vec<_> = instances[start..end].iter_mut().collect();
        
        // 并发升级
        let mut tasks = Vec::new();
        
        for instance in batch {
            instance.status = InstanceStatus::Draining;
            
            let id = instance.id.clone();
            let version = target_version.to_string();
            
            let task = tokio::spawn(async move {
                // 1. 排空流量
                Self::drain_traffic(&id).await?;
                
                // 2. 停止实例
                Self::stop_instance(&id).await?;
                
                // 3. 升级
                Self::upgrade_instance(&id, &version).await?;
                
                // 4. 启动实例
                Self::start_instance(&id).await?;
                
                Ok::<_, Box<dyn std::error::Error + Send + Sync>>(())
            });
            
            tasks.push(task);
            
            // 控制并发数
            if tasks.len() >= self.config.max_concurrent {
                futures::future::try_join_all(tasks).await?;
                tasks = Vec::new();
            }
        }
        
        // 等待剩余任务
        if !tasks.is_empty() {
            futures::future::try_join_all(tasks).await?;
        }
        
        // 更新状态
        for instance in &mut instances[start..end] {
            instance.version = target_version.to_string();
            instance.status = InstanceStatus::Running;
        }
        
        Ok(())
    }
    
    /// 检查批次健康状态
    async fn check_batch_health(
        &self,
        start: usize,
        end: usize,
    ) -> Result<bool, Box<dyn std::error::Error>> {
        let instances = self.instances.read().await;
        let batch = &instances[start..end];
        
        // 多次健康检查
        for _ in 0..3 {
            tokio::time::sleep(self.config.health_check_interval).await;
            
            let mut healthy_count = 0;
            
            for instance in batch {
                if self.health_checker.check_instance(&instance.id).await {
                    healthy_count += 1;
                }
            }
            
            let health_ratio = healthy_count as f64 / batch.len() as f64;
            
            if health_ratio < self.config.rollback_threshold {
                return Ok(false);
            }
        }
        
        Ok(true)
    }
    
    /// 回滚
    async fn rollback(
        &self,
        failed_batch: usize,
        _target_version: &str,
    ) -> Result<(), Box<dyn std::error::Error>> {
        tracing::warn!("Initiating rollback from batch {}", failed_batch);
        
        // 简化实现：回滚到之前的版本
        let mut instances = self.instances.write().await;
        
        for (idx, instance) in instances.iter_mut().enumerate() {
            if idx / self.config.batch_size <= failed_batch {
                instance.status = InstanceStatus::Failed;
                // 实际应该回滚到previous_version
            }
        }
        
        Ok(())
    }
    
    // 辅助方法
    async fn drain_traffic(_instance_id: &str) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        tokio::time::sleep(Duration::from_secs(5)).await;
        Ok(())
    }
    
    async fn stop_instance(_instance_id: &str) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        tokio::time::sleep(Duration::from_secs(2)).await;
        Ok(())
    }
    
    async fn upgrade_instance(_instance_id: &str, _version: &str) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        tokio::time::sleep(Duration::from_secs(10)).await;
        Ok(())
    }
    
    async fn start_instance(_instance_id: &str) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        tokio::time::sleep(Duration::from_secs(3)).await;
        Ok(())
    }
}
```

---

## 5. 灰度发布

### 5.1 金丝雀发布

```rust
/// 金丝雀发布控制器
pub struct CanaryController {
    /// 流量分配
    traffic_split: Arc<RwLock<TrafficSplit>>,
    
    /// 指标比较器
    metrics_comparator: Arc<MetricsComparator>,
    
    /// 配置
    config: CanaryConfig,
}

/// 流量分配
#[derive(Debug, Clone)]
pub struct TrafficSplit {
    /// 稳定版本权重
    pub stable_weight: u32,
    
    /// 金丝雀版本权重
    pub canary_weight: u32,
}

/// 金丝雀配置
#[derive(Debug, Clone)]
pub struct CanaryConfig {
    /// 初始金丝雀流量百分比
    pub initial_traffic: f64,
    
    /// 流量递增步长
    pub traffic_increment: f64,
    
    /// 递增间隔
    pub increment_interval: Duration,
    
    /// 指标阈值
    pub metrics_threshold: MetricsThreshold,
}

#[derive(Debug, Clone)]
pub struct MetricsThreshold {
    pub max_error_rate_increase: f64,
    pub max_latency_increase: f64,
}

impl CanaryController {
    pub fn new(
        config: CanaryConfig,
        metrics_comparator: Arc<MetricsComparator>,
    ) -> Self {
        let initial_canary_weight = (config.initial_traffic * 100.0) as u32;
        let stable_weight = 100 - initial_canary_weight;
        
        Self {
            traffic_split: Arc::new(RwLock::new(TrafficSplit {
                stable_weight,
                canary_weight: initial_canary_weight,
            })),
            metrics_comparator,
            config,
        }
    }
    
    /// 开始金丝雀发布
    pub async fn start_canary(&self) -> Result<(), Box<dyn std::error::Error>> {
        tracing::info!("Starting canary deployment with {}% traffic", self.config.initial_traffic * 100.0);
        
        loop {
            // 等待观察间隔
            tokio::time::sleep(self.config.increment_interval).await;
            
            // 比较指标
            let comparison = self.metrics_comparator.compare().await?;
            
            if !comparison.is_healthy(&self.config.metrics_threshold) {
                tracing::error!("Canary metrics unhealthy, rolling back");
                self.rollback_canary().await?;
                return Err("Canary deployment failed".into());
            }
            
            // 增加金丝雀流量
            let current_split = self.traffic_split.read().await.clone();
            let new_canary_weight = current_split.canary_weight + (self.config.traffic_increment * 100.0) as u32;
            
            if new_canary_weight >= 100 {
                // 金丝雀成为稳定版本
                self.promote_canary().await?;
                tracing::info!("Canary promoted to stable");
                break;
            }
            
            let mut split = self.traffic_split.write().await;
            split.canary_weight = new_canary_weight;
            split.stable_weight = 100 - new_canary_weight;
            
            tracing::info!("Canary traffic increased to {}%", new_canary_weight);
        }
        
        Ok(())
    }
    
    /// 回滚金丝雀
    async fn rollback_canary(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut split = self.traffic_split.write().await;
        split.canary_weight = 0;
        split.stable_weight = 100;
        
        tracing::info!("Canary rolled back, 100% traffic to stable");
        Ok(())
    }
    
    /// 提升金丝雀为稳定版本
    async fn promote_canary(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut split = self.traffic_split.write().await;
        split.stable_weight = 0;
        split.canary_weight = 100;
        
        // 实际应该交换版本标签
        Ok(())
    }
    
    /// 获取当前流量分配
    pub async fn get_traffic_split(&self) -> TrafficSplit {
        self.traffic_split.read().await.clone()
    }
}

/// 指标比较器
pub struct MetricsComparator {
    stable_metrics: Arc<RwLock<VersionMetrics>>,
    canary_metrics: Arc<RwLock<VersionMetrics>>,
}

#[derive(Debug, Clone, Default)]
pub struct VersionMetrics {
    pub error_rate: f64,
    pub avg_latency_ms: f64,
    pub p99_latency_ms: f64,
    pub request_count: u64,
}

#[derive(Debug)]
pub struct MetricsComparison {
    pub error_rate_diff: f64,
    pub latency_diff: f64,
}

impl MetricsComparison {
    fn is_healthy(&self, threshold: &MetricsThreshold) -> bool {
        self.error_rate_diff <= threshold.max_error_rate_increase &&
        self.latency_diff <= threshold.max_latency_increase
    }
}

impl MetricsComparator {
    pub fn new() -> Self {
        Self {
            stable_metrics: Arc::new(RwLock::new(VersionMetrics::default())),
            canary_metrics: Arc::new(RwLock::new(VersionMetrics::default())),
        }
    }
    
    /// 比较指标
    pub async fn compare(&self) -> Result<MetricsComparison, Box<dyn std::error::Error>> {
        let stable = self.stable_metrics.read().await;
        let canary = self.canary_metrics.read().await;
        
        Ok(MetricsComparison {
            error_rate_diff: canary.error_rate - stable.error_rate,
            latency_diff: canary.avg_latency_ms - stable.avg_latency_ms,
        })
    }
}
```

---

## 6. 完整实现

### 6.1 综合示例

```rust
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt::init();
    
    // 创建指标收集器
    let metrics = Arc::new(MetricsCollector::new());
    
    // 创建降级控制器
    let degradation_config = DegradationConfig {
        enabled: true,
        cpu_threshold: 80.0,
        memory_threshold: 85.0,
        latency_threshold_ms: 100.0,
        error_rate_threshold: 0.05,
        queue_depth_threshold: 10000,
        recovery_threshold: 0.6,
        evaluation_interval: Duration::from_secs(30),
        strategies: vec![
            DegradationStrategy::ReduceSamplingRate { target_rate: 0.1 },
            DegradationStrategy::DisableNonCritical {
                critical_services: vec!["payment".to_string(), "checkout".to_string()],
            },
        ],
    };
    
    let degradation_controller = DegradationController::new(
        degradation_config,
        Arc::clone(&metrics),
    );
    
    // 添加触发器
    {
        let mut triggers = degradation_controller.triggers.write().await;
        triggers.push(Box::new(CpuTrigger::new(CpuThresholds {
            light: 70.0,
            moderate: 80.0,
            heavy: 90.0,
            emergency: 95.0,
        })));
        
        triggers.push(Box::new(MemoryTrigger::new(MemoryThresholds {
            light: 75.0,
            moderate: 85.0,
            heavy: 92.0,
            emergency: 97.0,
        })));
    }
    
    degradation_controller.start().await;
    
    // 创建限流器
    let mut rate_limiter = RateLimiter::new(10000, 1000);
    
    // 创建熔断器
    let circuit_breaker = CircuitBreaker::new(CircuitBreakerConfig {
        failure_threshold: 10,
        success_threshold: 5,
        timeout: Duration::from_secs(30),
        half_open_timeout: Duration::from_secs(10),
    });
    
    tracing::info!("Degradation and protection systems started");
    
    // 模拟请求处理
    for i in 0..100 {
        // 检查是否允许请求
        if !rate_limiter.check() {
            tracing::warn!("Request {} rate limited", i);
            continue;
        }
        
        if !circuit_breaker.allow_request().await {
            tracing::warn!("Request {} blocked by circuit breaker", i);
            continue;
        }
        
        // 检查降级级别
        let level = degradation_controller.get_current_level().await;
        let sampling_rate = degradation_controller.get_recommended_sampling_rate().await;
        
        tracing::info!(
            "Request {}: degradation_level={:?}, sampling_rate={:.4}",
            i,
            level,
            sampling_rate
        );
        
        // 模拟处理
        let success = (i % 10) != 0; // 10% 失败率
        
        if success {
            circuit_breaker.record_success().await;
        } else {
            circuit_breaker.record_failure().await;
        }
        
        tokio::time::sleep(Duration::from_millis(100)).await;
    }
    
    Ok(())
}
```

---

## 总结

本文档提供了OTLP降级与升级策略的完整Rust实现，包括:

✅ **降级策略**:

- 自适应降级(CPU/内存/延迟触发)
- 分级降级(Normal/Light/Moderate/Heavy/Emergency)
- 自动恢复机制

✅ **保护机制**:

- 令牌桶限流
- 熔断器(Circuit Breaker)
- 过载保护

✅ **升级策略**:

- 滚动升级(批次升级)
- 金丝雀发布(灰度发布)
- 自动回滚

✅ **生产就绪**:

- 完整的监控指标
- 健康检查机制
- 详细的日志记录

---

**参考资源**:

- [Site Reliability Engineering](https://sre.google/books/)
- [Release Engineering](https://en.wikipedia.org/wiki/Release_engineering)
- [Chaos Engineering](https://principlesofchaos.org/)
