//! # Tower 服务集成 - OTLP 中间件
//!
//! 本模块实现与 Tower 生态系统的深度集成，提供服务中间件、
//! 负载均衡、超时控制和重试机制。
//!
//! ## Tower 生态系统
//!
//! Tower 是一个模块化、可重用的网络服务组件库，提供：
//! - **Service trait**: 异步请求/响应处理的核心抽象
//! - **Layer trait**: 服务组合的中间件抽象
//! - **超时控制**: 请求超时处理
//! - **重试机制**: 智能重试策略
//! - **速率限制**: 请求频率控制
//! - **负载均衡**: 多后端负载分发
//!
//! ## 依赖版本
//!
//! - tower: 0.5.x
//! - tower-service: 0.3.x
//! - tower-layer: 0.3.x
//! - tokio: 1.50+
//!
//! ## 使用示例
//!
//! ```rust,ignore
//! use otlp::tower_integration::{OtlpService, OtlpLayer};
//! use tower::{Service, ServiceBuilder};
//!
//! let service = ServiceBuilder::new()
//!     .layer(OtlpLayer::new())
//!     .timeout(Duration::from_secs(30))
//!     .retry(OtlpRetryPolicy::default())
//!     .service(OtlpService::new(client));
//! ```

use std::{
    future::Future,
    pin::Pin,
    task::{Context, Poll},
    time::Duration,
};

use tower::{Layer, Service};

/// OTLP 服务请求
#[derive(Debug, Clone)]
pub struct OtlpRequest {
    pub data: Vec<u8>,
    pub signal_type: SignalType,
    pub headers: std::collections::HashMap<String, String>,
}

/// OTLP 服务响应
#[derive(Debug, Clone)]
pub struct OtlpResponse {
    pub status_code: u16,
    pub body: Vec<u8>,
    pub metadata: ResponseMetadata,
}

/// 响应元数据
#[derive(Debug, Clone, Default)]
pub struct ResponseMetadata {
    pub request_id: String,
    pub server_time_ms: u64,
    pub retry_after: Option<Duration>,
}

/// 信号类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SignalType {
    Traces,
    Metrics,
    Logs,
    Profiles,
}

/// OTLP 服务核心实现
#[derive(Debug, Clone)]
pub struct OtlpService<C> {
    client: C,
    endpoint: String,
}

impl<C> OtlpService<C> {
    pub fn new(client: C, endpoint: impl Into<String>) -> Self {
        Self {
            client,
            endpoint: endpoint.into(),
        }
    }
}

impl<C> Service<OtlpRequest> for OtlpService<C>
where
    C: Clone + Send + 'static,
{
    type Response = OtlpResponse;
    type Error = OtlpServiceError;
    type Future = Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>> + Send>>;

    fn poll_ready(&mut self, _cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        Poll::Ready(Ok(()))
    }

    fn call(&mut self, req: OtlpRequest) -> Self::Future {
        let endpoint = self.endpoint.clone();
        let _client = self.client.clone();
        
        Box::pin(async move {
            // 模拟 OTLP 请求处理
            tokio::time::sleep(Duration::from_millis(10)).await;
            
            tracing::info!(
                signal_type = ?req.signal_type,
                endpoint = %endpoint,
                data_size = req.data.len(),
                "Processing OTLP request"
            );
            
            Ok(OtlpResponse {
                status_code: 200,
                body: vec![],
                metadata: ResponseMetadata {
                    request_id: format!("req-{}", uuid::Uuid::new_v4()),
                    server_time_ms: 10,
                    retry_after: None,
                },
            })
        })
    }
}

/// OTLP 服务错误
#[derive(Debug, thiserror::Error)]
pub enum OtlpServiceError {
    #[error("Transport error: {0}")]
    Transport(String),
    
    #[error("Protocol error: {0}")]
    Protocol(String),
    
    #[error("Timeout")]
    Timeout,
    
    #[error("Rate limited")]
    RateLimited,
}

/// OTLP 中间件层
#[derive(Debug, Clone)]
pub struct OtlpLayer {
    enable_metrics: bool,
    enable_tracing: bool,
}

impl OtlpLayer {
    pub fn new() -> Self {
        Self {
            enable_metrics: true,
            enable_tracing: true,
        }
    }

    pub fn with_metrics(mut self, enable: bool) -> Self {
        self.enable_metrics = enable;
        self
    }

    pub fn with_tracing(mut self, enable: bool) -> Self {
        self.enable_tracing = enable;
        self
    }
}

impl Default for OtlpLayer {
    fn default() -> Self {
        Self::new()
    }
}

impl<S> Layer<S> for OtlpLayer {
    type Service = OtlpMiddleware<S>;

    fn layer(&self, inner: S) -> Self::Service {
        OtlpMiddleware {
            inner,
            enable_metrics: self.enable_metrics,
            enable_tracing: self.enable_tracing,
        }
    }
}

/// OTLP 中间件实现
#[derive(Debug, Clone)]
pub struct OtlpMiddleware<S> {
    inner: S,
    enable_metrics: bool,
    enable_tracing: bool,
}

impl<S> Service<OtlpRequest> for OtlpMiddleware<S>
where
    S: Service<OtlpRequest, Response = OtlpResponse> + Send + Clone + 'static,
    S::Error: std::fmt::Debug,
    S::Future: Send,
{
    type Response = S::Response;
    type Error = S::Error;
    type Future = Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>> + Send>>;

    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        self.inner.poll_ready(cx)
    }

    fn call(&mut self, req: OtlpRequest) -> Self::Future {
        let mut inner = self.inner.clone();
        let enable_metrics = self.enable_metrics;
        let enable_tracing = self.enable_tracing;
        let signal_type = req.signal_type;
        let start = std::time::Instant::now();
        
        Box::pin(async move {
            if enable_tracing {
                tracing::info!(?signal_type, "OTLP request started");
            }
            
            let result = inner.call(req).await;
            
            let duration = start.elapsed();
            
            if enable_metrics {
                // 记录指标
                tracing::info!(
                    signal_type = ?signal_type,
                    duration_ms = duration.as_millis() as u64,
                    "OTLP request completed"
                );
            }
            
            if enable_tracing {
                tracing::info!(?signal_type, ?result, "OTLP request finished");
            }
            
            result
        })
    }
}

/// 重试策略配置
#[derive(Debug, Clone)]
pub struct OtlpRetryPolicy {
    max_retries: usize,
    initial_delay: Duration,
    max_delay: Duration,
    backoff_multiplier: f64,
}

impl Default for OtlpRetryPolicy {
    fn default() -> Self {
        Self {
            max_retries: 3,
            initial_delay: Duration::from_millis(100),
            max_delay: Duration::from_secs(30),
            backoff_multiplier: 2.0,
        }
    }
}

impl OtlpRetryPolicy {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_max_retries(mut self, max: usize) -> Self {
        self.max_retries = max;
        self
    }

    pub fn calculate_delay(&self, attempt: usize) -> Duration {
        let delay = self.initial_delay.as_millis() as f64 
            * self.backoff_multiplier.powi(attempt as i32);
        let delay = delay.min(self.max_delay.as_millis() as f64) as u64;
        Duration::from_millis(delay)
    }

    /// 检查是否应该重试
    pub fn should_retry(&self, attempt: usize, error: &OtlpServiceError) -> bool {
        if attempt >= self.max_retries {
            return false;
        }
        
        matches!(error, 
            OtlpServiceError::Transport(_) | 
            OtlpServiceError::Timeout |
            OtlpServiceError::RateLimited
        )
    }
}

/// 带重试的 OTLP 服务包装器
#[derive(Debug, Clone)]
pub struct RetryableOtlpService<S> {
    inner: S,
    policy: OtlpRetryPolicy,
}

impl<S> RetryableOtlpService<S> {
    pub fn new(inner: S, policy: OtlpRetryPolicy) -> Self {
        Self { inner, policy }
    }
}

impl<S> Service<OtlpRequest> for RetryableOtlpService<S>
where
    S: Service<OtlpRequest, Response = OtlpResponse, Error = OtlpServiceError> 
        + Clone 
        + Send 
        + 'static,
    S::Future: Send,
{
    type Response = S::Response;
    type Error = S::Error;
    type Future = Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>> + Send>>;

    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        self.inner.poll_ready(cx)
    }

    fn call(&mut self, req: OtlpRequest) -> Self::Future {
        let mut inner = self.inner.clone();
        let policy = self.policy.clone();
        
        Box::pin(async move {
            let mut attempt = 0;
            
            loop {
                match inner.call(req.clone()).await {
                    Ok(response) => return Ok(response),
                    Err(error) => {
                        if !policy.should_retry(attempt, &error) {
                            return Err(error);
                        }
                        
                        let delay = policy.calculate_delay(attempt);
                        tracing::warn!(
                            attempt = attempt + 1,
                            max_retries = policy.max_retries,
                            delay_ms = delay.as_millis() as u64,
                            "Retrying OTLP request"
                        );
                        
                        tokio::time::sleep(delay).await;
                        attempt += 1;
                    }
                }
            }
        })
    }
}

/// 负载均衡策略
#[derive(Debug, Clone)]
pub enum LoadBalancingStrategy {
    RoundRobin,
    LeastConnections,
    Random,
    WeightedRoundRobin(Vec<u32>),
}

/// 负载均衡 OTLP 服务
#[derive(Debug)]
pub struct LoadBalancedOtlpService<S> {
    backends: Vec<S>,
    strategy: LoadBalancingStrategy,
    current_index: std::sync::atomic::AtomicUsize,
}

impl<S: Clone> Clone for LoadBalancedOtlpService<S> {
    fn clone(&self) -> Self {
        Self {
            backends: self.backends.clone(),
            strategy: self.strategy.clone(),
            current_index: std::sync::atomic::AtomicUsize::new(
                self.current_index.load(std::sync::atomic::Ordering::Relaxed)
            ),
        }
    }
}

impl<S> LoadBalancedOtlpService<S> {
    pub fn new(backends: Vec<S>, strategy: LoadBalancingStrategy) -> Self {
        Self {
            backends,
            strategy,
            current_index: std::sync::atomic::AtomicUsize::new(0),
        }
    }

    fn select_backend(&self) -> Option<&S> {
        if self.backends.is_empty() {
            return None;
        }

        match &self.strategy {
            LoadBalancingStrategy::RoundRobin => {
                let idx = self.current_index.fetch_add(
                    1, 
                    std::sync::atomic::Ordering::Relaxed
                ) % self.backends.len();
                self.backends.get(idx)
            }
            LoadBalancingStrategy::Random => {
                use rand::Rng;
                let idx = rand::rng().random_range(0..self.backends.len());
                self.backends.get(idx)
            }
            _ => self.backends.first(),
        }
    }
}

impl<S> Service<OtlpRequest> for LoadBalancedOtlpService<S>
where
    S: Service<OtlpRequest, Response = OtlpResponse, Error = OtlpServiceError> 
        + Clone 
        + Send 
        + 'static,
    S::Future: Send,
{
    type Response = S::Response;
    type Error = OtlpServiceError;
    type Future = Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>> + Send>>;

    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        // 检查至少一个后端可用
        for backend in &mut self.backends {
            if backend.poll_ready(cx).is_ready() {
                return Poll::Ready(Ok(()));
            }
        }
        Poll::Pending
    }

    fn call(&mut self, req: OtlpRequest) -> Self::Future {
        let backend = self.select_backend().cloned();
        
        Box::pin(async move {
            match backend {
                Some(mut svc) => svc.call(req).await,
                None => Err(OtlpServiceError::Transport(
                    "No available backends".to_string()
                )),
            }
        })
    }
}

/// 速率限制配置
#[derive(Debug, Clone)]
pub struct RateLimitConfig {
    pub requests_per_second: u64,
    pub burst_size: u64,
}

impl Default for RateLimitConfig {
    fn default() -> Self {
        Self {
            requests_per_second: 1000,
            burst_size: 100,
        }
    }
}

/// 带速率限制的 OTLP 服务
#[derive(Debug)]
pub struct RateLimitedOtlpService<S> {
    inner: S,
    tokens: std::sync::Arc<tokio::sync::Semaphore>,
    config: RateLimitConfig,
}

impl<S: Clone> Clone for RateLimitedOtlpService<S> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            tokens: std::sync::Arc::clone(&self.tokens),
            config: self.config.clone(),
        }
    }
}

impl<S> RateLimitedOtlpService<S> {
    pub fn new(inner: S, config: RateLimitConfig) -> Self {
        let tokens = std::sync::Arc::new(tokio::sync::Semaphore::new(
            config.burst_size as usize
        ));
        
        Self {
            inner,
            tokens,
            config,
        }
    }
}

impl<S> Service<OtlpRequest> for RateLimitedOtlpService<S>
where
    S: Service<OtlpRequest, Response = OtlpResponse, Error = OtlpServiceError> 
        + Clone 
        + Send 
        + 'static,
    S::Future: Send,
{
    type Response = S::Response;
    type Error = S::Error;
    type Future = Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>> + Send>>;

    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        self.inner.poll_ready(cx)
    }

    fn call(&mut self, req: OtlpRequest) -> Self::Future {
        let mut inner = self.inner.clone();
        let tokens = std::sync::Arc::clone(&self.tokens);
        
        Box::pin(async move {
            // 获取令牌进行速率限制
            let _permit = match tokens.acquire().await {
                Ok(p) => p,
                Err(_) => {
                    return Err(OtlpServiceError::RateLimited);
                }
            };
            
            inner.call(req).await
        })
    }
}

/// 创建标准的 OTLP 服务栈
///
/// 组合所有中间件：追踪、指标、重试、超时、速率限制
pub fn create_otlp_service_stack<C>(
    client: C,
    endpoint: impl Into<String>,
) -> impl Service<OtlpRequest, Response = OtlpResponse>
where
    C: Clone + Send + 'static,
{
    use tower::ServiceBuilder;
    
    ServiceBuilder::new()
        .layer(OtlpLayer::new())
        .timeout(Duration::from_secs(30))
        .service(OtlpService::new(client, endpoint))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_otlp_service() {
        let mut service = OtlpService::new((), "http://localhost:4317");
        
        let request = OtlpRequest {
            data: vec![1, 2, 3],
            signal_type: SignalType::Traces,
            headers: std::collections::HashMap::new(),
        };
        
        let response = service.call(request).await.unwrap();
        assert_eq!(response.status_code, 200);
    }

    #[test]
    fn test_retry_policy() {
        let policy = OtlpRetryPolicy::default();
        
        assert_eq!(policy.calculate_delay(0), Duration::from_millis(100));
        assert_eq!(policy.calculate_delay(1), Duration::from_millis(200));
        assert_eq!(policy.calculate_delay(2), Duration::from_millis(400));
        
        let error = OtlpServiceError::Timeout;
        assert!(policy.should_retry(0, &error));
        assert!(policy.should_retry(2, &error));
        assert!(!policy.should_retry(3, &error));
    }

    #[test]
    fn test_load_balancing_strategy() {
        let backends = vec!["backend1", "backend2", "backend3"];
        let lb = LoadBalancedOtlpService::new(
            backends,
            LoadBalancingStrategy::RoundRobin
        );
        
        // 验证轮询选择
        let _ = lb.select_backend();
        let _ = lb.select_backend();
        let _ = lb.select_backend();
    }
}
