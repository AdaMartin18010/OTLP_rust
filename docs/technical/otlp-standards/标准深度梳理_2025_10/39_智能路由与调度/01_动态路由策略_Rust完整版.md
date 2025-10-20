# OTLP 动态路由策略 - Rust 完整实现

> **版本**: 1.0.0  
> **Rust 版本**: 1.90+  
> **OpenTelemetry**: v0.27+  
> **最后更新**: 2025-10-09

## 目录

- [OTLP 动态路由策略 - Rust 完整实现](#otlp-动态路由策略---rust-完整实现)
  - [目录](#目录)
  - [概述](#概述)
    - [核心特性](#核心特性)
  - [核心架构](#核心架构)
  - [动态路由管理器](#动态路由管理器)
  - [路由策略](#路由策略)
    - [4.1 基于权重的路由](#41-基于权重的路由)
    - [4.2 基于延迟的路由](#42-基于延迟的路由)
    - [4.3 基于地理位置的路由](#43-基于地理位置的路由)
    - [4.4 基于内容的路由](#44-基于内容的路由)
  - [流量分发器](#流量分发器)
  - [健康检查与故障转移](#健康检查与故障转移)
  - [路由表管理](#路由表管理)
  - [完整示例](#完整示例)
  - [性能优化](#性能优化)
    - [1. **缓存路由决策**](#1-缓存路由决策)
    - [2. **预编译正则表达式**](#2-预编译正则表达式)
    - [3. **批量健康检查**](#3-批量健康检查)
  - [最佳实践](#最佳实践)
    - [1. **规则优先级设计**](#1-规则优先级设计)
    - [2. **健康检查配置**](#2-健康检查配置)
    - [3. **故障转移策略**](#3-故障转移策略)
    - [4. **监控与告警**](#4-监控与告警)
    - [5. **配置管理**](#5-配置管理)
  - [依赖项](#依赖项)
  - [总结](#总结)

---

## 概述

动态路由是分布式 OTLP 系统的核心组件，负责根据各种条件（负载、延迟、地理位置、内容等）智能地将遥测数据路由到最佳的后端服务。

### 核心特性

- ✅ **多策略路由**: 支持权重、延迟、地理位置、内容等多种路由策略
- ✅ **动态更新**: 支持运行时动态更新路由规则
- ✅ **健康检查**: 自动检测后端健康状态并进行故障转移
- ✅ **负载感知**: 根据后端负载动态调整路由权重
- ✅ **零停机**: 支持平滑切换路由策略
- ✅ **异步优化**: 基于 Tokio 的高性能异步实现

---

## 核心架构

```rust
use std::sync::Arc;
use std::time::{Duration, Instant};
use std::collections::HashMap;
use tokio::sync::RwLock;
use serde::{Serialize, Deserialize};

/// 路由目标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RouteTarget {
    pub id: String,
    pub endpoint: String,
    pub weight: u32,
    pub region: String,
    pub tags: HashMap<String, String>,
}

/// 路由规则
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RouteRule {
    pub id: String,
    pub priority: u32,
    pub conditions: Vec<RouteCondition>,
    pub targets: Vec<RouteTarget>,
    pub strategy: RouteStrategy,
}

/// 路由条件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RouteCondition {
    ServiceName(String),
    SpanKind(String),
    AttributeMatch { key: String, value: String },
    Region(String),
    SampleRate(f64),
}

/// 路由策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RouteStrategy {
    WeightedRoundRobin,
    LatencyBased,
    GeographyBased,
    ContentBased,
    Failover,
}

/// 后端健康状态
#[derive(Debug, Clone)]
pub struct BackendHealth {
    pub target_id: String,
    pub is_healthy: bool,
    pub last_check: Instant,
    pub latency: Duration,
    pub error_rate: f64,
}
```

---

## 动态路由管理器

```rust
use opentelemetry::trace::{SpanContext, SpanKind};
use opentelemetry::KeyValue;

/// 动态路由管理器
pub struct DynamicRouter {
    rules: Arc<RwLock<Vec<RouteRule>>>,
    health_status: Arc<RwLock<HashMap<String, BackendHealth>>>,
    metrics: Arc<RwLock<RouterMetrics>>,
}

#[derive(Debug, Default)]
struct RouterMetrics {
    total_routed: u64,
    route_failures: u64,
    latency_sum: Duration,
}

impl DynamicRouter {
    pub fn new() -> Self {
        Self {
            rules: Arc::new(RwLock::new(Vec::new())),
            health_status: Arc::new(RwLock::new(HashMap::new())),
            metrics: Arc::new(RwLock::new(RouterMetrics::default())),
        }
    }

    /// 添加路由规则
    pub async fn add_rule(&self, rule: RouteRule) {
        let mut rules = self.rules.write().await;
        rules.push(rule);
        // 按优先级排序
        rules.sort_by(|a, b| b.priority.cmp(&a.priority));
    }

    /// 更新路由规则
    pub async fn update_rule(&self, rule_id: &str, new_rule: RouteRule) {
        let mut rules = self.rules.write().await;
        if let Some(pos) = rules.iter().position(|r| r.id == rule_id) {
            rules[pos] = new_rule;
            rules.sort_by(|a, b| b.priority.cmp(&a.priority));
        }
    }

    /// 删除路由规则
    pub async fn remove_rule(&self, rule_id: &str) {
        let mut rules = self.rules.write().await;
        rules.retain(|r| r.id != rule_id);
    }

    /// 路由 Span
    pub async fn route_span(
        &self,
        span_context: &SpanContext,
        attributes: &[KeyValue],
    ) -> Result<Vec<RouteTarget>, String> {
        let start = Instant::now();
        let rules = self.rules.read().await;
        let health = self.health_status.read().await;

        // 遍历规则，找到第一个匹配的
        for rule in rules.iter() {
            if self.matches_conditions(&rule.conditions, span_context, attributes) {
                // 过滤健康的目标
                let healthy_targets: Vec<RouteTarget> = rule
                    .targets
                    .iter()
                    .filter(|t| {
                        health
                            .get(&t.id)
                            .map(|h| h.is_healthy)
                            .unwrap_or(true)
                    })
                    .cloned()
                    .collect();

                if !healthy_targets.is_empty() {
                    // 更新指标
                    let mut metrics = self.metrics.write().await;
                    metrics.total_routed += 1;
                    metrics.latency_sum += start.elapsed();

                    return Ok(healthy_targets);
                }
            }
        }

        // 记录失败
        let mut metrics = self.metrics.write().await;
        metrics.route_failures += 1;

        Err("No matching route found".to_string())
    }

    /// 检查条件是否匹配
    fn matches_conditions(
        &self,
        conditions: &[RouteCondition],
        _span_context: &SpanContext,
        attributes: &[KeyValue],
    ) -> bool {
        for condition in conditions {
            match condition {
                RouteCondition::ServiceName(name) => {
                    let matches = attributes.iter().any(|kv| {
                        kv.key.as_str() == "service.name" && kv.value.to_string() == *name
                    });
                    if !matches {
                        return false;
                    }
                }
                RouteCondition::AttributeMatch { key, value } => {
                    let matches = attributes.iter().any(|kv| {
                        kv.key.as_str() == key && kv.value.to_string() == *value
                    });
                    if !matches {
                        return false;
                    }
                }
                RouteCondition::Region(region) => {
                    let matches = attributes.iter().any(|kv| {
                        kv.key.as_str() == "region" && kv.value.to_string() == *region
                    });
                    if !matches {
                        return false;
                    }
                }
                RouteCondition::SpanKind(kind) => {
                    let matches = attributes.iter().any(|kv| {
                        kv.key.as_str() == "span.kind" && kv.value.to_string() == *kind
                    });
                    if !matches {
                        return false;
                    }
                }
                RouteCondition::SampleRate(_rate) => {
                    // 采样率逻辑已在采样器中处理
                    continue;
                }
            }
        }
        true
    }

    /// 获取路由指标
    pub async fn get_metrics(&self) -> RouterMetrics {
        let metrics = self.metrics.read().await;
        RouterMetrics {
            total_routed: metrics.total_routed,
            route_failures: metrics.route_failures,
            latency_sum: metrics.latency_sum,
        }
    }
}
```

---

## 路由策略

### 4.1 基于权重的路由

```rust
use rand::Rng;

/// 加权轮询路由器
pub struct WeightedRoundRobinRouter {
    targets: Vec<RouteTarget>,
    current_weights: Vec<i32>,
    effective_weights: Vec<i32>,
}

impl WeightedRoundRobinRouter {
    pub fn new(targets: Vec<RouteTarget>) -> Self {
        let effective_weights: Vec<i32> = targets.iter().map(|t| t.weight as i32).collect();
        let current_weights = vec![0; targets.len()];

        Self {
            targets,
            current_weights,
            effective_weights,
        }
    }

    /// 选择下一个目标（平滑加权轮询算法）
    pub fn next(&mut self) -> Option<&RouteTarget> {
        if self.targets.is_empty() {
            return None;
        }

        let total_weight: i32 = self.effective_weights.iter().sum();
        
        // 更新当前权重
        for i in 0..self.current_weights.len() {
            self.current_weights[i] += self.effective_weights[i];
        }

        // 找到当前权重最大的
        let max_index = self
            .current_weights
            .iter()
            .enumerate()
            .max_by_key(|(_, &w)| w)
            .map(|(i, _)| i)?;

        // 减去总权重
        self.current_weights[max_index] -= total_weight;

        Some(&self.targets[max_index])
    }

    /// 随机选择（按权重）
    pub fn random_weighted(&self) -> Option<&RouteTarget> {
        if self.targets.is_empty() {
            return None;
        }

        let total_weight: u32 = self.targets.iter().map(|t| t.weight).sum();
        let mut rng = rand::thread_rng();
        let mut random_weight = rng.gen_range(0..total_weight);

        for target in &self.targets {
            if random_weight < target.weight {
                return Some(target);
            }
            random_weight -= target.weight;
        }

        None
    }
}
```

### 4.2 基于延迟的路由

```rust
use std::collections::BTreeMap;

/// 基于延迟的路由器
pub struct LatencyBasedRouter {
    latency_map: Arc<RwLock<BTreeMap<String, Duration>>>,
    targets: Vec<RouteTarget>,
}

impl LatencyBasedRouter {
    pub fn new(targets: Vec<RouteTarget>) -> Self {
        Self {
            latency_map: Arc::new(RwLock::new(BTreeMap::new())),
            targets,
        }
    }

    /// 更新延迟信息
    pub async fn update_latency(&self, target_id: &str, latency: Duration) {
        let mut map = self.latency_map.write().await;
        map.insert(target_id.to_string(), latency);
    }

    /// 选择延迟最低的目标
    pub async fn select_lowest_latency(&self) -> Option<RouteTarget> {
        let map = self.latency_map.read().await;

        self.targets
            .iter()
            .min_by_key(|t| map.get(&t.id).unwrap_or(&Duration::from_secs(9999)))
            .cloned()
    }

    /// 选择延迟在阈值内的随机目标
    pub async fn select_within_threshold(&self, threshold: Duration) -> Option<RouteTarget> {
        let map = self.latency_map.read().await;

        let candidates: Vec<&RouteTarget> = self
            .targets
            .iter()
            .filter(|t| {
                map.get(&t.id)
                    .map(|lat| *lat <= threshold)
                    .unwrap_or(false)
            })
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let mut rng = rand::thread_rng();
        let index = rng.gen_range(0..candidates.len());
        Some(candidates[index].clone())
    }
}
```

### 4.3 基于地理位置的路由

```rust
/// 地理位置路由器
pub struct GeographyBasedRouter {
    targets: Vec<RouteTarget>,
    region_map: HashMap<String, Vec<RouteTarget>>,
}

impl GeographyBasedRouter {
    pub fn new(targets: Vec<RouteTarget>) -> Self {
        let mut region_map: HashMap<String, Vec<RouteTarget>> = HashMap::new();

        for target in &targets {
            region_map
                .entry(target.region.clone())
                .or_insert_with(Vec::new)
                .push(target.clone());
        }

        Self {
            targets,
            region_map,
        }
    }

    /// 选择同区域的目标
    pub fn select_by_region(&self, region: &str) -> Vec<RouteTarget> {
        self.region_map
            .get(region)
            .cloned()
            .unwrap_or_default()
    }

    /// 选择最近的区域
    pub fn select_nearest(&self, client_region: &str) -> Vec<RouteTarget> {
        // 首先尝试同区域
        if let Some(targets) = self.region_map.get(client_region) {
            if !targets.is_empty() {
                return targets.clone();
            }
        }

        // 回退到默认区域或所有目标
        self.region_map
            .get("default")
            .cloned()
            .unwrap_or_else(|| self.targets.clone())
    }

    /// 多区域故障转移
    pub fn select_with_fallback(&self, preferred_regions: &[String]) -> Vec<RouteTarget> {
        for region in preferred_regions {
            if let Some(targets) = self.region_map.get(region) {
                if !targets.is_empty() {
                    return targets.clone();
                }
            }
        }

        // 最后回退到所有目标
        self.targets.clone()
    }
}
```

### 4.4 基于内容的路由

```rust
use regex::Regex;

/// 基于内容的路由器
pub struct ContentBasedRouter {
    rules: Vec<ContentRule>,
}

#[derive(Debug, Clone)]
pub struct ContentRule {
    pub matcher: ContentMatcher,
    pub targets: Vec<RouteTarget>,
}

#[derive(Debug, Clone)]
pub enum ContentMatcher {
    ServiceNamePattern(Regex),
    AttributeEquals { key: String, value: String },
    AttributeContains { key: String, pattern: Regex },
    SpanNamePattern(Regex),
    ResourcePattern(Regex),
}

impl ContentBasedRouter {
    pub fn new(rules: Vec<ContentRule>) -> Self {
        Self { rules }
    }

    /// 根据内容选择目标
    pub fn select(&self, attributes: &[KeyValue]) -> Option<Vec<RouteTarget>> {
        for rule in &self.rules {
            if self.matches(&rule.matcher, attributes) {
                return Some(rule.targets.clone());
            }
        }
        None
    }

    fn matches(&self, matcher: &ContentMatcher, attributes: &[KeyValue]) -> bool {
        match matcher {
            ContentMatcher::ServiceNamePattern(regex) => {
                attributes.iter().any(|kv| {
                    kv.key.as_str() == "service.name"
                        && regex.is_match(&kv.value.to_string())
                })
            }
            ContentMatcher::AttributeEquals { key, value } => {
                attributes.iter().any(|kv| {
                    kv.key.as_str() == key && kv.value.to_string() == *value
                })
            }
            ContentMatcher::AttributeContains { key, pattern } => {
                attributes.iter().any(|kv| {
                    kv.key.as_str() == key && pattern.is_match(&kv.value.to_string())
                })
            }
            ContentMatcher::SpanNamePattern(regex) => {
                attributes.iter().any(|kv| {
                    kv.key.as_str() == "span.name"
                        && regex.is_match(&kv.value.to_string())
                })
            }
            ContentMatcher::ResourcePattern(regex) => {
                attributes.iter().any(|kv| {
                    kv.key.as_str() == "resource"
                        && regex.is_match(&kv.value.to_string())
                })
            }
        }
    }
}
```

---

## 流量分发器

```rust
use tokio::sync::mpsc;

/// 流量分发器
pub struct TrafficDistributor {
    router: Arc<DynamicRouter>,
    senders: Arc<RwLock<HashMap<String, mpsc::Sender<Vec<u8>>>>>,
}

impl TrafficDistributor {
    pub fn new(router: Arc<DynamicRouter>) -> Self {
        Self {
            router,
            senders: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 注册后端发送器
    pub async fn register_backend(&self, target_id: String, sender: mpsc::Sender<Vec<u8>>) {
        let mut senders = self.senders.write().await;
        senders.insert(target_id, sender);
    }

    /// 分发数据
    pub async fn distribute(
        &self,
        span_context: &SpanContext,
        attributes: &[KeyValue],
        data: Vec<u8>,
    ) -> Result<(), String> {
        // 路由到目标
        let targets = self.router.route_span(span_context, attributes).await?;

        let senders = self.senders.read().await;

        // 并发发送到所有目标
        let mut send_futures = Vec::new();

        for target in targets {
            if let Some(sender) = senders.get(&target.id) {
                let sender = sender.clone();
                let data = data.clone();
                send_futures.push(async move {
                    sender.send(data).await.map_err(|e| e.to_string())
                });
            }
        }

        // 等待所有发送完成
        let results = futures::future::join_all(send_futures).await;

        // 检查是否有失败
        let failures: Vec<_> = results.into_iter().filter(|r| r.is_err()).collect();

        if failures.is_empty() {
            Ok(())
        } else {
            Err(format!("Failed to send to {} targets", failures.len()))
        }
    }
}
```

---

## 健康检查与故障转移

```rust
use tokio::time::interval;
use reqwest::Client;

/// 健康检查器
pub struct HealthChecker {
    router: Arc<DynamicRouter>,
    check_interval: Duration,
    timeout: Duration,
    http_client: Client,
}

impl HealthChecker {
    pub fn new(router: Arc<DynamicRouter>, check_interval: Duration) -> Self {
        Self {
            router,
            check_interval,
            timeout: Duration::from_secs(5),
            http_client: Client::new(),
        }
    }

    /// 启动健康检查
    pub async fn start(&self) {
        let mut interval = interval(self.check_interval);

        loop {
            interval.tick().await;
            self.check_all_backends().await;
        }
    }

    async fn check_all_backends(&self) {
        let rules = self.router.rules.read().await;
        let mut health_status = self.router.health_status.write().await;

        for rule in rules.iter() {
            for target in &rule.targets {
                let health = self.check_backend(target).await;
                health_status.insert(target.id.clone(), health);
            }
        }
    }

    async fn check_backend(&self, target: &RouteTarget) -> BackendHealth {
        let start = Instant::now();
        let health_url = format!("{}/health", target.endpoint);

        match tokio::time::timeout(self.timeout, self.http_client.get(&health_url).send()).await {
            Ok(Ok(response)) => {
                let latency = start.elapsed();
                let is_healthy = response.status().is_success();

                BackendHealth {
                    target_id: target.id.clone(),
                    is_healthy,
                    last_check: Instant::now(),
                    latency,
                    error_rate: 0.0,
                }
            }
            _ => BackendHealth {
                target_id: target.id.clone(),
                is_healthy: false,
                last_check: Instant::now(),
                latency: Duration::from_secs(0),
                error_rate: 1.0,
            },
        }
    }
}
```

---

## 路由表管理

```rust
/// 路由表管理器
pub struct RouteTableManager {
    router: Arc<DynamicRouter>,
    config_path: String,
}

impl RouteTableManager {
    pub fn new(router: Arc<DynamicRouter>, config_path: String) -> Self {
        Self {
            router,
            config_path,
        }
    }

    /// 从配置文件加载路由表
    pub async fn load_from_file(&self) -> Result<(), Box<dyn std::error::Error>> {
        let content = tokio::fs::read_to_string(&self.config_path).await?;
        let rules: Vec<RouteRule> = serde_json::from_str(&content)?;

        for rule in rules {
            self.router.add_rule(rule).await;
        }

        Ok(())
    }

    /// 保存路由表到文件
    pub async fn save_to_file(&self) -> Result<(), Box<dyn std::error::Error>> {
        let rules = self.router.rules.read().await;
        let content = serde_json::to_string_pretty(&*rules)?;
        tokio::fs::write(&self.config_path, content).await?;

        Ok(())
    }

    /// 热重载路由表
    pub async fn reload(&self) -> Result<(), Box<dyn std::error::Error>> {
        let content = tokio::fs::read_to_string(&self.config_path).await?;
        let new_rules: Vec<RouteRule> = serde_json::from_str(&content)?;

        let mut rules = self.router.rules.write().await;
        *rules = new_rules;
        rules.sort_by(|a, b| b.priority.cmp(&a.priority));

        println!("路由表已重载: {} 条规则", rules.len());

        Ok(())
    }

    /// 监听配置文件变化
    pub async fn watch_config(&self) {
        use notify::{Watcher, RecursiveMode, watcher};
        use std::sync::mpsc::channel;

        let (tx, rx) = channel();
        let mut watcher = watcher(tx, Duration::from_secs(2)).unwrap();
        watcher.watch(&self.config_path, RecursiveMode::NonRecursive).unwrap();

        loop {
            match rx.recv() {
                Ok(_event) => {
                    println!("检测到配置文件变化，重新加载路由表...");
                    if let Err(e) = self.reload().await {
                        eprintln!("重载路由表失败: {}", e);
                    }
                }
                Err(e) => {
                    eprintln!("监听配置文件失败: {}", e);
                    break;
                }
            }
        }
    }
}
```

---

## 完整示例

```rust
use opentelemetry::trace::{TraceId, SpanId, TraceFlags, TraceState};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== OTLP 动态路由系统 ===\n");

    // 1. 创建路由目标
    let targets = vec![
        RouteTarget {
            id: "backend-1".to_string(),
            endpoint: "http://localhost:4317".to_string(),
            weight: 50,
            region: "us-east-1".to_string(),
            tags: HashMap::from([("tier".to_string(), "premium".to_string())]),
        },
        RouteTarget {
            id: "backend-2".to_string(),
            endpoint: "http://localhost:4318".to_string(),
            weight: 30,
            region: "us-west-2".to_string(),
            tags: HashMap::from([("tier".to_string(), "standard".to_string())]),
        },
        RouteTarget {
            id: "backend-3".to_string(),
            endpoint: "http://localhost:4319".to_string(),
            weight: 20,
            region: "eu-west-1".to_string(),
            tags: HashMap::from([("tier".to_string(), "basic".to_string())]),
        },
    ];

    // 2. 创建动态路由器
    let router = Arc::new(DynamicRouter::new());

    // 3. 添加路由规则
    let rule = RouteRule {
        id: "rule-1".to_string(),
        priority: 100,
        conditions: vec![
            RouteCondition::ServiceName("my-service".to_string()),
            RouteCondition::Region("us-east-1".to_string()),
        ],
        targets: targets.clone(),
        strategy: RouteStrategy::WeightedRoundRobin,
    };

    router.add_rule(rule).await;

    // 4. 启动健康检查器
    let health_checker = HealthChecker::new(
        router.clone(),
        Duration::from_secs(10),
    );

    tokio::spawn(async move {
        health_checker.start().await;
    });

    // 5. 测试加权轮询路由
    println!("测试加权轮询路由:");
    let mut wrr = WeightedRoundRobinRouter::new(targets.clone());
    for i in 0..10 {
        if let Some(target) = wrr.next() {
            println!("  请求 {}: 路由到 {} (权重: {})", i + 1, target.id, target.weight);
        }
    }

    // 6. 测试基于延迟的路由
    println!("\n测试基于延迟的路由:");
    let latency_router = LatencyBasedRouter::new(targets.clone());
    latency_router.update_latency("backend-1", Duration::from_millis(50)).await;
    latency_router.update_latency("backend-2", Duration::from_millis(30)).await;
    latency_router.update_latency("backend-3", Duration::from_millis(100)).await;

    if let Some(target) = latency_router.select_lowest_latency().await {
        println!("  最低延迟目标: {}", target.id);
    }

    // 7. 测试地理位置路由
    println!("\n测试地理位置路由:");
    let geo_router = GeographyBasedRouter::new(targets.clone());
    let us_targets = geo_router.select_by_region("us-east-1");
    println!("  US-East-1 区域目标数: {}", us_targets.len());

    // 8. 测试基于内容的路由
    println!("\n测试基于内容的路由:");
    let content_rule = ContentRule {
        matcher: ContentMatcher::ServiceNamePattern(
            Regex::new(r"^my-.*").unwrap(),
        ),
        targets: vec![targets[0].clone()],
    };

    let content_router = ContentBasedRouter::new(vec![content_rule]);

    let attributes = vec![
        KeyValue::new("service.name", "my-service"),
        KeyValue::new("region", "us-east-1"),
    ];

    if let Some(matched_targets) = content_router.select(&attributes) {
        println!("  内容匹配到 {} 个目标", matched_targets.len());
    }

    // 9. 测试实际路由
    println!("\n测试完整路由:");
    let span_context = SpanContext::new(
        TraceId::from_u128(12345),
        SpanId::from_u64(67890),
        TraceFlags::default(),
        false,
        TraceState::default(),
    );

    let routed_targets = router.route_span(&span_context, &attributes).await?;
    println!("  路由到 {} 个目标:", routed_targets.len());
    for target in routed_targets {
        println!("    - {} ({})", target.id, target.endpoint);
    }

    // 10. 显示路由指标
    println!("\n路由指标:");
    let metrics = router.get_metrics().await;
    println!("  总路由数: {}", metrics.total_routed);
    println!("  失败数: {}", metrics.route_failures);
    println!("  平均延迟: {:?}", metrics.latency_sum / metrics.total_routed.max(1) as u32);

    println!("\n✅ 动态路由系统运行成功!");

    Ok(())
}
```

---

## 性能优化

### 1. **缓存路由决策**

```rust
use lru::LruCache;

pub struct CachedRouter {
    router: Arc<DynamicRouter>,
    cache: Arc<RwLock<LruCache<String, Vec<RouteTarget>>>>,
}

impl CachedRouter {
    pub fn new(router: Arc<DynamicRouter>, cache_size: usize) -> Self {
        Self {
            router,
            cache: Arc::new(RwLock::new(LruCache::new(cache_size))),
        }
    }

    pub async fn route_with_cache(
        &self,
        span_context: &SpanContext,
        attributes: &[KeyValue],
    ) -> Result<Vec<RouteTarget>, String> {
        let cache_key = self.build_cache_key(span_context, attributes);

        // 尝试从缓存获取
        {
            let mut cache = self.cache.write().await;
            if let Some(targets) = cache.get(&cache_key) {
                return Ok(targets.clone());
            }
        }

        // 缓存未命中，执行路由
        let targets = self.router.route_span(span_context, attributes).await?;

        // 更新缓存
        {
            let mut cache = self.cache.write().await;
            cache.put(cache_key, targets.clone());
        }

        Ok(targets)
    }

    fn build_cache_key(&self, span_context: &SpanContext, attributes: &[KeyValue]) -> String {
        format!("{:?}:{:?}", span_context, attributes)
    }
}
```

### 2. **预编译正则表达式**

在 `ContentMatcher` 中预编译所有正则表达式，避免运行时编译开销。

### 3. **批量健康检查**

```rust
impl HealthChecker {
    async fn check_all_backends_parallel(&self) {
        let rules = self.router.rules.read().await;
        let mut handles = Vec::new();

        for rule in rules.iter() {
            for target in &rule.targets {
                let target = target.clone();
                let checker = self.clone();
                handles.push(tokio::spawn(async move {
                    checker.check_backend(&target).await
                }));
            }
        }

        let results = futures::future::join_all(handles).await;

        let mut health_status = self.router.health_status.write().await;
        for result in results {
            if let Ok(health) = result {
                health_status.insert(health.target_id.clone(), health);
            }
        }
    }
}
```

---

## 最佳实践

### 1. **规则优先级设计**

- 高优先级规则用于特殊流量（VIP、调试）
- 中优先级规则用于常规业务路由
- 低优先级规则作为默认兜底

### 2. **健康检查配置**

```rust
// 推荐配置
let health_config = HealthCheckConfig {
    interval: Duration::from_secs(10),     // 检查间隔
    timeout: Duration::from_secs(5),       // 超时时间
    unhealthy_threshold: 3,                // 不健康阈值
    healthy_threshold: 2,                  // 健康阈值
};
```

### 3. **故障转移策略**

- 自动检测并移除不健康的后端
- 支持手动禁用/启用后端
- 实现主备切换逻辑

### 4. **监控与告警**

```rust
// 记录关键指标
tracing::info!(
    target: "otlp_router",
    route_latency_ms = latency.as_millis(),
    target_id = target.id,
    rule_id = rule.id,
    "Routed span"
);
```

### 5. **配置管理**

- 使用 JSON/YAML 格式存储路由规则
- 支持热重载，避免重启服务
- 版本控制路由配置

---

## 依赖项

```toml
[dependencies]
tokio = { version = "1.41", features = ["full"] }
opentelemetry = "0.27"
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
rand = "0.8"
regex = "1.11"
futures = "0.3"
reqwest = { version = "0.12", features = ["json"] }
notify = "6.1"
lru = "0.12"
tracing = "0.1"
```

---

## 总结

本文档提供了完整的 OTLP 动态路由策略的 Rust 实现，包括：

✅ **多种路由策略**: 权重、延迟、地理位置、内容
✅ **动态管理**: 运行时更新路由规则
✅ **健康检查**: 自动故障检测与转移
✅ **性能优化**: 缓存、批量处理、异步并发
✅ **生产就绪**: 监控、日志、配置管理

通过这些实现，您可以构建高性能、高可用的 OTLP 路由系统。
