//! # 微服务架构设计模式实现
//!
//! 本模块提供了基于Rust 1.90的微服务架构设计模式实现，
//! 包括服务发现、负载均衡、熔断器、重试机制等核心模式。

pub mod advanced;

use anyhow::{anyhow, Result};
use async_trait::async_trait;
use futures::future::BoxFuture;
use opentelemetry::global;
use opentelemetry::metrics::{Counter, Histogram};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{Mutex, RwLock};
use tokio::time::sleep;
use tracing::debug;

/// 服务端点信息
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct ServiceEndpoint {
    pub id: String,
    pub address: String,
    pub port: u16,
    pub weight: u32,
    pub metadata: HashMap<String, String>,
    pub health_status: HealthStatus,
    pub last_health_check: Instant,
}

/// 健康状态
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[allow(dead_code)]
pub enum HealthStatus {
    Healthy,
    Unhealthy,
    Unknown,
}

/// 负载均衡器trait
#[async_trait]
pub trait LoadBalancer: Send + Sync {
    async fn select_endpoint<'a>(
        &self,
        endpoints: &'a [ServiceEndpoint],
    ) -> Option<&'a ServiceEndpoint>;
    async fn update_endpoints(&mut self, endpoints: Vec<ServiceEndpoint>);
}

/// 轮询负载均衡器
#[allow(dead_code)]
pub struct RoundRobinLoadBalancer {
    current: Arc<Mutex<usize>>,
    endpoints: Arc<RwLock<Vec<ServiceEndpoint>>>,
}

impl RoundRobinLoadBalancer {
    pub fn new() -> Self {
        Self {
            current: Arc::new(Mutex::new(0)),
            endpoints: Arc::new(RwLock::new(Vec::new())),
        }
    }
}

#[async_trait]
impl LoadBalancer for RoundRobinLoadBalancer {
    async fn select_endpoint<'a>(
        &self,
        endpoints: &'a [ServiceEndpoint],
    ) -> Option<&'a ServiceEndpoint> {
        if endpoints.is_empty() {
            return None;
        }

        let mut current = self.current.lock().await;
        let selected = &endpoints[*current % endpoints.len()];
        *current += 1;
        Some(selected)
    }

    async fn update_endpoints(&mut self, endpoints: Vec<ServiceEndpoint>) {
        let mut current_endpoints = self.endpoints.write().await;
        *current_endpoints = endpoints;
    }
}

/// 加权轮询负载均衡器
#[allow(dead_code)]
pub struct WeightedRoundRobinLoadBalancer {
    current_weights: Arc<Mutex<HashMap<String, u32>>>,
    endpoints: Arc<RwLock<Vec<ServiceEndpoint>>>,
}

impl WeightedRoundRobinLoadBalancer {
    pub fn new() -> Self {
        Self {
            current_weights: Arc::new(Mutex::new(HashMap::new())),
            endpoints: Arc::new(RwLock::new(Vec::new())),
        }
    }
}

#[async_trait]
impl LoadBalancer for WeightedRoundRobinLoadBalancer {
    async fn select_endpoint<'a>(
        &self,
        endpoints: &'a [ServiceEndpoint],
    ) -> Option<&'a ServiceEndpoint> {
        if endpoints.is_empty() {
            return None;
        }

        let mut current_weights = self.current_weights.lock().await;

        // 找到权重最高的端点
        let mut max_weight = 0;
        let mut selected_endpoint = None;

        for endpoint in endpoints {
            let current_weight = current_weights
                .get(&endpoint.id)
                .unwrap_or(&endpoint.weight);
            if *current_weight > max_weight {
                max_weight = *current_weight;
                selected_endpoint = Some(endpoint);
            }
        }

        if let Some(endpoint) = selected_endpoint {
            // 减少选中端点的当前权重
            let total_weight: u32 = endpoints.iter().map(|e| e.weight).sum();
            let current_weight = *current_weights
                .get(&endpoint.id)
                .unwrap_or(&endpoint.weight);
            let new_weight = current_weight.saturating_sub(total_weight);
            current_weights.insert(endpoint.id.clone(), new_weight);

            // 为所有端点增加权重
            for endpoint in endpoints {
                let current_weight = *current_weights.get(&endpoint.id).unwrap_or(&0);
                current_weights.insert(endpoint.id.clone(), current_weight + endpoint.weight);
            }
        }

        selected_endpoint
    }

    async fn update_endpoints(&mut self, endpoints: Vec<ServiceEndpoint>) {
        let mut current_endpoints = self.endpoints.write().await;
        *current_endpoints = endpoints;
    }
}

/// 熔断器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct CircuitBreakerConfig {
    pub failure_threshold: u32,
    pub recovery_timeout: Duration,
    pub half_open_max_calls: u32,
}

impl Default for CircuitBreakerConfig {
    fn default() -> Self {
        Self {
            failure_threshold: 5,
            recovery_timeout: Duration::from_secs(60),
            half_open_max_calls: 3,
        }
    }
}

/// 熔断器状态
#[derive(Debug, Clone, PartialEq)]
#[allow(dead_code)]
pub enum CircuitBreakerState {
    Closed,
    Open,
    HalfOpen,
}

/// 熔断器
#[allow(dead_code)]
pub struct CircuitBreaker {
    config: CircuitBreakerConfig,
    state: Arc<Mutex<CircuitBreakerState>>,
    failure_count: Arc<Mutex<u32>>,
    last_failure_time: Arc<Mutex<Option<Instant>>>,
    half_open_calls: Arc<Mutex<u32>>,
}

impl CircuitBreaker {
    pub fn new(config: CircuitBreakerConfig) -> Self {
        Self {
            config,
            state: Arc::new(Mutex::new(CircuitBreakerState::Closed)),
            failure_count: Arc::new(Mutex::new(0)),
            last_failure_time: Arc::new(Mutex::new(None)),
            half_open_calls: Arc::new(Mutex::new(0)),
        }
    }

    pub async fn call<F, R>(&self, f: F) -> Result<R, CircuitBreakerError>
    where
        F: FnOnce() -> BoxFuture<'static, Result<R, anyhow::Error>>,
    {
        let state = self.state.lock().await;

        match *state {
            CircuitBreakerState::Closed => {
                drop(state);
                self.execute_call(f).await
            }
            CircuitBreakerState::Open => {
                drop(state);
                self.check_recovery_time().await.map(|_| unreachable!())
            }
            CircuitBreakerState::HalfOpen => {
                drop(state);
                self.execute_half_open_call(f).await
            }
        }
    }

    async fn execute_call<F, R>(&self, f: F) -> Result<R, CircuitBreakerError>
    where
        F: FnOnce() -> BoxFuture<'static, Result<R, anyhow::Error>>,
    {
        match f().await {
            Ok(result) => {
                self.on_success().await;
                Ok(result)
            }
            Err(e) => {
                self.on_failure().await;
                Err(CircuitBreakerError::ExecutionError(e))
            }
        }
    }

    async fn execute_half_open_call<F, R>(&self, f: F) -> Result<R, CircuitBreakerError>
    where
        F: FnOnce() -> BoxFuture<'static, Result<R, anyhow::Error>>,
    {
        let mut half_open_calls = self.half_open_calls.lock().await;
        if *half_open_calls >= self.config.half_open_max_calls {
            return Err(CircuitBreakerError::HalfOpenMaxCallsReached);
        }

        *half_open_calls += 1;
        drop(half_open_calls);

        match f().await {
            Ok(result) => {
                self.on_half_open_success().await;
                Ok(result)
            }
            Err(e) => {
                self.on_half_open_failure().await;
                Err(CircuitBreakerError::ExecutionError(e))
            }
        }
    }

    async fn check_recovery_time(&self) -> Result<(), CircuitBreakerError> {
        let last_failure_time = self.last_failure_time.lock().await;
        if let Some(last_failure) = *last_failure_time {
            if last_failure.elapsed() >= self.config.recovery_timeout {
                drop(last_failure_time);
                self.transition_to_half_open().await;
                return Ok(());
            }
        }
        Err(CircuitBreakerError::CircuitBreakerOpen)
    }

    async fn on_success(&self) {
        let mut failure_count = self.failure_count.lock().await;
        *failure_count = 0;
    }

    async fn on_failure(&self) {
        let mut failure_count = self.failure_count.lock().await;
        *failure_count += 1;

        if *failure_count >= self.config.failure_threshold {
            self.transition_to_open().await;
        }
    }

    async fn on_half_open_success(&self) {
        self.transition_to_closed().await;
    }

    async fn on_half_open_failure(&self) {
        self.transition_to_open().await;
    }

    async fn transition_to_open(&self) {
        let mut state = self.state.lock().await;
        *state = CircuitBreakerState::Open;

        let mut last_failure_time = self.last_failure_time.lock().await;
        *last_failure_time = Some(Instant::now());
    }

    async fn transition_to_half_open(&self) {
        let mut state = self.state.lock().await;
        *state = CircuitBreakerState::HalfOpen;

        let mut half_open_calls = self.half_open_calls.lock().await;
        *half_open_calls = 0;
    }

    async fn transition_to_closed(&self) {
        let mut state = self.state.lock().await;
        *state = CircuitBreakerState::Closed;

        let mut failure_count = self.failure_count.lock().await;
        *failure_count = 0;

        let mut half_open_calls = self.half_open_calls.lock().await;
        *half_open_calls = 0;
    }

    pub async fn get_state(&self) -> CircuitBreakerState {
        let state = self.state.lock().await;
        state.clone()
    }
}

/// 熔断器错误
#[derive(Debug)]
pub enum CircuitBreakerError {
    CircuitBreakerOpen,
    HalfOpenMaxCallsReached,
    ExecutionError(anyhow::Error),
}

impl std::fmt::Display for CircuitBreakerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CircuitBreakerError::CircuitBreakerOpen => {
                write!(f, "Circuit breaker is open")
            }
            CircuitBreakerError::HalfOpenMaxCallsReached => {
                write!(f, "Half-open max calls reached")
            }
            CircuitBreakerError::ExecutionError(e) => {
                write!(f, "Execution error: {}", e)
            }
        }
    }
}

impl std::error::Error for CircuitBreakerError {}

/// 重试配置
#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct RetryConfig {
    pub max_attempts: u32,
    pub base_delay: Duration,
    pub max_delay: Duration,
    pub backoff_multiplier: f64,
    pub jitter: bool,
}

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            max_attempts: 3,
            base_delay: Duration::from_millis(100),
            max_delay: Duration::from_secs(5),
            backoff_multiplier: 2.0,
            jitter: true,
        }
    }
}

/// 重试器
pub struct Retryer {
    config: RetryConfig,
}

impl Retryer {
    pub fn new(config: RetryConfig) -> Self {
        Self { config }
    }

    pub async fn execute<F, R>(&self, mut f: F) -> Result<R, anyhow::Error>
    where
        F: FnMut() -> BoxFuture<'static, Result<R, anyhow::Error>>,
    {
        let mut last_error = None;
        let mut delay = self.config.base_delay;

        for attempt in 1..=self.config.max_attempts {
            match f().await {
                Ok(result) => return Ok(result),
                Err(e) => {
                    last_error = Some(e);

                    if attempt == self.config.max_attempts {
                        break;
                    }

                    // 计算延迟时间
                    let mut current_delay = delay;
                    if self.config.jitter {
                        use rand::Rng;
                        let jitter_factor = 0.1;
                        let jitter = current_delay.as_millis() as f64 * jitter_factor;
                        let jitter_amount = rand::rng().random_range(-jitter..=jitter);
                        current_delay = Duration::from_millis(
                            (current_delay.as_millis() as f64 + jitter_amount).max(0.0) as u64,
                        );
                    }

                    current_delay = current_delay.min(self.config.max_delay);

                    debug!("Retry attempt {} after {:?}", attempt + 1, current_delay);
                    sleep(current_delay).await;

                    delay = Duration::from_millis(
                        (delay.as_millis() as f64 * self.config.backoff_multiplier) as u64,
                    );
                    delay = delay.min(self.config.max_delay);
                }
            }
        }

        Err(last_error.unwrap())
    }
}

/// 服务发现客户端trait
#[async_trait]
pub trait ServiceDiscoveryClient: Send + Sync {
    async fn discover_services(
        &self,
        service_name: &str,
    ) -> Result<Vec<ServiceEndpoint>, anyhow::Error>;
    async fn register_service(&self, endpoint: ServiceEndpoint) -> Result<(), anyhow::Error>;
    async fn deregister_service(&self, service_id: &str) -> Result<(), anyhow::Error>;
    async fn health_check(&self, endpoint: &ServiceEndpoint)
        -> Result<HealthStatus, anyhow::Error>;
}

/// 微服务客户端
#[allow(dead_code)]
pub struct MicroserviceClient {
    service_discovery: Arc<dyn ServiceDiscoveryClient>,
    load_balancer: Arc<dyn LoadBalancer + Send + Sync>,
    circuit_breaker: Arc<CircuitBreaker>,
    retryer: Arc<Retryer>,
    metrics: ClientMetrics,
}

/// 客户端指标
#[allow(dead_code)]
pub struct ClientMetrics {
    pub total_requests: Counter<u64>,
    pub successful_requests: Counter<u64>,
    pub failed_requests: Counter<u64>,
    pub circuit_breaker_opens: Counter<u64>,
    pub retry_attempts: Counter<u64>,
    pub request_latency: Histogram<f64>,
}

impl MicroserviceClient {
    pub fn new(
        service_discovery: Arc<dyn ServiceDiscoveryClient>,
        load_balancer: Arc<dyn LoadBalancer + Send + Sync>,
        circuit_breaker_config: CircuitBreakerConfig,
        retry_config: RetryConfig,
    ) -> Self {
        let meter = global::meter("microservice_client");
        let metrics = ClientMetrics {
            total_requests: meter
                .u64_counter("total_requests")
                .with_description("Total number of requests made")
                .build(),
            successful_requests: meter
                .u64_counter("successful_requests")
                .with_description("Number of successful requests")
                .build(),
            failed_requests: meter
                .u64_counter("failed_requests")
                .with_description("Number of failed requests")
                .build(),
            circuit_breaker_opens: meter
                .u64_counter("circuit_breaker_opens")
                .with_description("Number of circuit breaker opens")
                .build(),
            retry_attempts: meter
                .u64_counter("retry_attempts")
                .with_description("Number of retry attempts")
                .build(),
            request_latency: meter
                .f64_histogram("request_latency")
                .with_description("Request latency in milliseconds")
                .build(),
        };

        Self {
            service_discovery,
            load_balancer,
            circuit_breaker: Arc::new(CircuitBreaker::new(circuit_breaker_config)),
            retryer: Arc::new(Retryer::new(retry_config)),
            metrics,
        }
    }

    pub async fn call_service<F, R>(&self, service_name: &str, f: F) -> Result<R, anyhow::Error>
    where
        F: Fn(&ServiceEndpoint) -> BoxFuture<'static, Result<R, anyhow::Error>>
            + Send
            + Sync
            + 'static,
        R: Send,
    {
        self.metrics.total_requests.add(1, &[]);
        let start_time = Instant::now();

        // 发现服务端点
        let endpoints = self
            .service_discovery
            .discover_services(service_name)
            .await?;
        if endpoints.is_empty() {
            return Err(anyhow!(
                "No available endpoints for service: {}",
                service_name
            ));
        }

        // 选择端点
        let endpoint = self
            .load_balancer
            .select_endpoint(&endpoints)
            .await
            .ok_or_else(|| anyhow!("Failed to select endpoint"))?;

        // 通过熔断器执行调用
        let result = self
            .circuit_breaker
            .call(|| {
                let endpoint = endpoint.clone();
                Box::pin(async move { f(&endpoint).await })
            })
            .await;

        let final_result = match result {
            Ok(response) => {
                self.metrics.successful_requests.add(1, &[]);
                Ok(response)
            }
            Err(CircuitBreakerError::CircuitBreakerOpen) => {
                self.metrics.circuit_breaker_opens.add(1, &[]);
                Err(anyhow!("Circuit breaker is open"))
            }
            Err(CircuitBreakerError::ExecutionError(e)) => {
                self.metrics.failed_requests.add(1, &[]);
                Err(e)
            }
            Err(e) => {
                self.metrics.failed_requests.add(1, &[]);
                Err(anyhow!("Circuit breaker error: {}", e))
            }
        };

        let duration = start_time.elapsed();
        self.metrics
            .request_latency
            .record(duration.as_millis() as f64, &[]);

        final_result
    }
}

/// Mock Consul客户端实现
#[allow(dead_code)]
pub struct MockConsulClient {
    services: Arc<RwLock<HashMap<String, Vec<ServiceEndpoint>>>>,
}

impl MockConsulClient {
    pub fn new() -> Self {
        Self {
            services: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    pub async fn add_service(&self, service_name: String, endpoints: Vec<ServiceEndpoint>) {
        let mut services = self.services.write().await;
        services.insert(service_name, endpoints);
    }
}

#[async_trait]
impl ServiceDiscoveryClient for MockConsulClient {
    async fn discover_services(
        &self,
        service_name: &str,
    ) -> Result<Vec<ServiceEndpoint>, anyhow::Error> {
        let services = self.services.read().await;
        Ok(services.get(service_name).cloned().unwrap_or_default())
    }

    async fn register_service(&self, endpoint: ServiceEndpoint) -> Result<(), anyhow::Error> {
        let mut services = self.services.write().await;
        let service_name = endpoint
            .metadata
            .get("service_name")
            .ok_or_else(|| anyhow!("Missing service_name in metadata"))?;

        services
            .entry(service_name.clone())
            .or_insert_with(Vec::new)
            .push(endpoint);
        Ok(())
    }

    async fn deregister_service(&self, service_id: &str) -> Result<(), anyhow::Error> {
        let mut services = self.services.write().await;
        for (_, endpoints) in services.iter_mut() {
            endpoints.retain(|e| e.id != service_id);
        }
        Ok(())
    }

    async fn health_check(
        &self,
        endpoint: &ServiceEndpoint,
    ) -> Result<HealthStatus, anyhow::Error> {
        // 模拟健康检查
        Ok(endpoint.health_status.clone())
    }
}

// 重新导出advanced模块的类型
pub use advanced::{
    AdaptiveLoadBalancer, CircuitBreakerPolicy, Destination, FaultConfig, FaultInjector,
    FaultResult, FaultType, HealthChecker, InstanceMetrics, IntelligentRouter, MatchCondition,
    ResourceLimits, RetryPolicy, RouteRequest, RouteResponse, RouterMetrics, RoutingError,
    RoutingRule, ServiceInstance, ServiceMeshConfig, ServiceMeshType, SidecarConfig,
    TrafficManager,
};
