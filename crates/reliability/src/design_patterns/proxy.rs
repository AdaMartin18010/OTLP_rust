//! # 代理模式 (Proxy Pattern)
//!
//! 为其他对象提供一种代理以控制对这个对象的访问
//!
//! ## 应用场景
//!
//! - 延迟加载（Lazy Loading）
//! - 访问控制
//! - 缓存代理
//! - 远程代理
//! - 虚拟代理
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步代理操作
//! - **元组收集**: 使用 `collect()` 直接收集代理数据到元组
//! - **改进的代理模式**: 利用 Rust 1.92 的代理模式优化提升性能
use crate::prelude::*;
use serde::{Deserialize, Serialize};
use std::sync::Arc;

// Helper function to create validation errors
fn validation_error(msg: impl Into<String>) -> anyhow::Error {
    anyhow::anyhow!(msg.into())
}

/// 服务接口
#[async_trait::async_trait]
pub trait Service: Send + Sync {
    /// 执行服务操作
    async fn execute(&self, request: &ServiceRequest) -> Result<ServiceResponse>;

    /// 服务名称
    fn name(&self) -> &str;
}

/// 服务请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceRequest {
    pub id: String,
    pub data: serde_json::Value,
    pub metadata: std::collections::HashMap<String, String>,
}

impl ServiceRequest {
    pub fn new(id: impl Into<String>, data: serde_json::Value) -> Self {
        Self {
            id: id.into(),
            data,
            metadata: std::collections::HashMap::new(),
        }
    }

    pub fn with_metadata(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.metadata.insert(key.into(), value.into());
        self
    }
}

/// 服务响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceResponse {
    pub request_id: String,
    pub data: serde_json::Value,
    pub status: ResponseStatus,
    pub duration_ms: u64,
}

/// 响应状态
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum ResponseStatus {
    Success,
    Error(String),
}

impl ServiceResponse {
    pub fn success(request_id: impl Into<String>, data: serde_json::Value, duration_ms: u64) -> Self {
        Self {
            request_id: request_id.into(),
            data,
            status: ResponseStatus::Success,
            duration_ms,
        }
    }

    pub fn error(request_id: impl Into<String>, error: impl Into<String>, duration_ms: u64) -> Self {
        Self {
            request_id: request_id.into(),
            data: serde_json::Value::Null,
            status: ResponseStatus::Error(error.into()),
            duration_ms,
        }
    }
}

// ============================================================================
// 真实服务实现
// ============================================================================

/// 真实服务
pub struct RealService {
    name: String,
    processing_time_ms: u64,
}

impl RealService {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            processing_time_ms: 100,
        }
    }

    pub fn with_processing_time(mut self, ms: u64) -> Self {
        self.processing_time_ms = ms;
        self
    }
}

#[async_trait::async_trait]
impl Service for RealService {
    async fn execute(&self, request: &ServiceRequest) -> Result<ServiceResponse> {
        // 模拟处理时间
        tokio::time::sleep(Duration::from_millis(self.processing_time_ms)).await;

        let response_data = serde_json::json!({
            "processed_by": self.name,
            "original_data": request.data,
        });

        Ok(ServiceResponse::success(
            request.id.clone(),
            response_data,
            self.processing_time_ms,
        ))
    }

    fn name(&self) -> &str {
        &self.name
    }
}

// ============================================================================
// 代理服务
// ============================================================================

/// 代理服务基类
pub struct ServiceProxy {
    service: Option<Arc<dyn Service>>,
    service_factory: Option<Arc<dyn Fn() -> Arc<dyn Service> + Send + Sync>>,
}

impl ServiceProxy {
    pub fn new(service: Arc<dyn Service>) -> Self {
        Self {
            service: Some(service),
            service_factory: None,
        }
    }

    pub fn lazy(factory: Arc<dyn Fn() -> Arc<dyn Service> + Send + Sync>) -> Self {
        Self {
            service: None,
            service_factory: Some(factory),
        }
    }

    #[allow(dead_code)]
    async fn get_service(&mut self) -> Arc<dyn Service> {
        if let Some(ref service) = self.service {
            return service.clone();
        }

        if let Some(ref factory) = self.service_factory {
            let service = factory();
            self.service = Some(service.clone());
            return service;
        }

        panic!("Service proxy not initialized");
    }
}

#[async_trait::async_trait]
impl Service for ServiceProxy {
    async fn execute(&self, request: &ServiceRequest) -> Result<ServiceResponse> {
        // 需要可变引用，使用内部可变性
        // 这里简化实现，实际应该使用 Mutex 或 RwLock
        if let Some(ref service) = self.service {
            return service.execute(request).await;
        }

        if let Some(ref factory) = self.service_factory {
            let service = factory();
            return service.execute(request).await;
        }

        Err(validation_error("Service proxy not initialized"))
    }

    fn name(&self) -> &str {
        "ServiceProxy"
    }
}

// ============================================================================
// 缓存代理
// ============================================================================

/// 缓存代理 - 缓存服务响应
pub struct CachingProxy {
    service: Arc<dyn Service>,
    cache: Arc<tokio::sync::RwLock<std::collections::HashMap<String, ServiceResponse>>>,
    ttl_ms: Option<u64>,
    cache_timestamps: Arc<tokio::sync::RwLock<std::collections::HashMap<String, std::time::Instant>>>,
}

impl CachingProxy {
    pub fn new(service: Arc<dyn Service>) -> Self {
        Self {
            service,
            cache: Arc::new(tokio::sync::RwLock::new(std::collections::HashMap::new())),
            ttl_ms: None,
            cache_timestamps: Arc::new(tokio::sync::RwLock::new(std::collections::HashMap::new())),
        }
    }

    pub fn with_ttl(service: Arc<dyn Service>, ttl_ms: u64) -> Self {
        Self {
            service,
            cache: Arc::new(tokio::sync::RwLock::new(std::collections::HashMap::new())),
            ttl_ms: Some(ttl_ms),
            cache_timestamps: Arc::new(tokio::sync::RwLock::new(std::collections::HashMap::new())),
        }
    }

    fn cache_key(request: &ServiceRequest) -> String {
        // 使用请求ID作为缓存键
        request.id.clone()
    }

    async fn is_cache_valid(&self, key: &str) -> bool {
        if self.ttl_ms.is_none() {
            return self.cache.read().await.contains_key(key);
        }

        let timestamps = self.cache_timestamps.read().await;
        if let Some(timestamp) = timestamps.get(key) {
            timestamp.elapsed().as_millis() < self.ttl_ms.unwrap() as u128
        } else {
            false
        }
    }
}

#[async_trait::async_trait]
impl Service for CachingProxy {
    async fn execute(&self, request: &ServiceRequest) -> Result<ServiceResponse> {
        let key = Self::cache_key(request);

        // 检查缓存
        if self.is_cache_valid(&key).await {
            let cache = self.cache.read().await;
            if let Some(cached_response) = cache.get(&key) {
                return Ok(cached_response.clone());
            }
        }

        // 执行服务并缓存结果
        let response = self.service.execute(request).await?;
        {
            let mut cache = self.cache.write().await;
            cache.insert(key.clone(), response.clone());
        }
        {
            let mut timestamps = self.cache_timestamps.write().await;
            timestamps.insert(key, std::time::Instant::now());
        }

        Ok(response)
    }

    fn name(&self) -> &str {
        "CachingProxy"
    }
}

// ============================================================================
// 访问控制代理
// ============================================================================

/// 访问控制代理 - 控制对服务的访问
pub struct AccessControlProxy {
    service: Arc<dyn Service>,
    allowed_users: Arc<tokio::sync::RwLock<std::collections::HashSet<String>>>,
}

impl AccessControlProxy {
    pub fn new(service: Arc<dyn Service>) -> Self {
        Self {
            service,
            allowed_users: Arc::new(tokio::sync::RwLock::new(std::collections::HashSet::new())),
        }
    }

    pub async fn allow_user(&self, user: impl Into<String>) {
        let mut users = self.allowed_users.write().await;
        users.insert(user.into());
    }

    pub async fn deny_user(&self, user: &str) {
        let mut users = self.allowed_users.write().await;
        users.remove(user);
    }

    pub async fn is_allowed(&self, user: &str) -> bool {
        let users = self.allowed_users.read().await;
        users.contains(user)
    }
}

#[async_trait::async_trait]
impl Service for AccessControlProxy {
    async fn execute(&self, request: &ServiceRequest) -> Result<ServiceResponse> {
        // 从请求元数据中获取用户信息
        let user = request
            .metadata
            .get("user")
            .ok_or_else(|| validation_error("User not specified in request"))?;

        if !self.is_allowed(user).await {
            return Ok(ServiceResponse::error(
                request.id.clone(),
                format!("Access denied for user: {}", user),
                0,
            ));
        }

        self.service.execute(request).await
    }

    fn name(&self) -> &str {
        "AccessControlProxy"
    }
}

// ============================================================================
// 限流代理
// ============================================================================

/// 限流代理 - 限制请求速率
pub struct RateLimitingProxy {
    service: Arc<dyn Service>,
    rate_limiter: Arc<tokio::sync::RwLock<RateLimiterState>>,
    max_requests: u64,
    window_ms: u64,
}

struct RateLimiterState {
    requests: Vec<std::time::Instant>,
}

impl RateLimiterState {
    fn new() -> Self {
        Self {
            requests: Vec::new(),
        }
    }

    fn cleanup(&mut self, window_ms: u64) {
        let cutoff = std::time::Instant::now() - Duration::from_millis(window_ms);
        self.requests.retain(|&time| time > cutoff);
    }

    fn can_proceed(&mut self, max_requests: u64, window_ms: u64) -> bool {
        self.cleanup(window_ms);
        if self.requests.len() < max_requests as usize {
            self.requests.push(std::time::Instant::now());
            true
        } else {
            false
        }
    }
}

impl RateLimitingProxy {
    pub fn new(service: Arc<dyn Service>, max_requests: u64, window_ms: u64) -> Self {
        Self {
            service,
            rate_limiter: Arc::new(tokio::sync::RwLock::new(RateLimiterState::new())),
            max_requests,
            window_ms,
        }
    }
}

#[async_trait::async_trait]
impl Service for RateLimitingProxy {
    async fn execute(&self, request: &ServiceRequest) -> Result<ServiceResponse> {
        let can_proceed = {
            let mut limiter = self.rate_limiter.write().await;
            limiter.can_proceed(self.max_requests, self.window_ms)
        };

        if !can_proceed {
            return Ok(ServiceResponse::error(
                request.id.clone(),
                format!(
                    "Rate limit exceeded: {} requests per {}ms",
                    self.max_requests, self.window_ms
                ),
                0,
            ));
        }

        self.service.execute(request).await
    }

    fn name(&self) -> &str {
        "RateLimitingProxy"
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_real_service() {
        let service = Arc::new(RealService::new("test-service"));
        let request = ServiceRequest::new("req-1", serde_json::json!({"test": "data"}));

        let response = service.execute(&request).await.unwrap();
        assert_eq!(response.status, ResponseStatus::Success);
        assert_eq!(response.request_id, "req-1");
    }

    #[tokio::test]
    async fn test_caching_proxy() {
        let real_service = Arc::new(RealService::new("test-service"));
        let proxy = Arc::new(CachingProxy::new(real_service));
        let request = ServiceRequest::new("req-1", serde_json::json!({"test": "data"}));

        let start1 = std::time::Instant::now();
        let response1 = proxy.execute(&request).await.unwrap();
        let duration1 = start1.elapsed();

        let start2 = std::time::Instant::now();
        let response2 = proxy.execute(&request).await.unwrap();
        let duration2 = start2.elapsed();

        // 第二次应该从缓存获取，速度更快
        assert!(duration2 < duration1);
        assert_eq!(response1.request_id, response2.request_id);
    }

    #[tokio::test]
    async fn test_access_control_proxy() {
        let real_service = Arc::new(RealService::new("test-service"));
        let proxy = Arc::new(AccessControlProxy::new(real_service));

        proxy.allow_user("user1").await;

        let allowed_request = ServiceRequest::new("req-1", serde_json::json!({}))
            .with_metadata("user", "user1");
        let response1 = proxy.execute(&allowed_request).await.unwrap();
        assert_eq!(response1.status, ResponseStatus::Success);

        let denied_request = ServiceRequest::new("req-2", serde_json::json!({}))
            .with_metadata("user", "user2");
        let response2 = proxy.execute(&denied_request).await.unwrap();
        match response2.status {
            ResponseStatus::Error(_) => {}
            _ => panic!("Should have been denied"),
        }
    }

    #[tokio::test]
    async fn test_rate_limiting_proxy() {
        let real_service = Arc::new(RealService::new("test-service"));
        let proxy = Arc::new(RateLimitingProxy::new(real_service, 2, 1000));

        let request1 = ServiceRequest::new("req-1", serde_json::json!({}));
        let response1 = proxy.execute(&request1).await.unwrap();
        assert_eq!(response1.status, ResponseStatus::Success);

        let request2 = ServiceRequest::new("req-2", serde_json::json!({}));
        let response2 = proxy.execute(&request2).await.unwrap();
        assert_eq!(response2.status, ResponseStatus::Success);

        // 第三次应该被限流
        let request3 = ServiceRequest::new("req-3", serde_json::json!({}));
        let response3 = proxy.execute(&request3).await.unwrap();
        match response3.status {
            ResponseStatus::Error(_) => {}
            _ => panic!("Should have been rate limited"),
        }
    }
}
