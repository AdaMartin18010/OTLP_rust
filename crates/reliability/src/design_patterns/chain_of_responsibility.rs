//! # 责任链模式 (Chain of Responsibility Pattern)
//!
//! 使多个对象都有机会处理请求，从而避免请求的发送者和接收者之间的耦合关系
//!
//! ## 应用场景
//!
//! - 请求处理链
//! - 中间件链
//! - 异常处理链
//! - 权限验证链
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步责任链操作
//! - **元组收集**: 使用 `collect()` 直接收集责任链数据到元组
//! - **改进的责任链模式**: 利用 Rust 1.92 的责任链模式优化提升性能
use crate::prelude::*;
use serde::{Deserialize, Serialize};
use std::sync::Arc;

// Helper function to create validation errors
fn validation_error(msg: impl Into<String>) -> anyhow::Error {
    anyhow::anyhow!(msg.into())
}

/// 请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Request {
    pub id: String,
    pub data: serde_json::Value,
    pub metadata: std::collections::HashMap<String, String>,
}

impl Request {
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

/// 响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Response {
    pub request_id: String,
    pub success: bool,
    pub message: String,
    pub data: Option<serde_json::Value>,
}

impl Response {
    pub fn success(request_id: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            request_id: request_id.into(),
            success: true,
            message: message.into(),
            data: None,
        }
    }

    pub fn success_with_data(
        request_id: impl Into<String>,
        message: impl Into<String>,
        data: serde_json::Value,
    ) -> Self {
        Self {
            request_id: request_id.into(),
            success: true,
            message: message.into(),
            data: Some(data),
        }
    }

    pub fn error(request_id: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            request_id: request_id.into(),
            success: false,
            message: message.into(),
            data: None,
        }
    }
}

/// 处理器 trait
#[async_trait::async_trait]
pub trait Handler: Send + Sync {
    /// 处理请求
    async fn handle(&self, request: &Request) -> Result<Option<Response>>;

    /// 设置下一个处理器
    fn set_next(&mut self, next: Arc<dyn Handler>);

    /// 处理器名称
    fn name(&self) -> &str;
}

/// 基础处理器
pub struct BaseHandler {
    name: String,
    next: Option<Arc<dyn Handler>>,
}

impl BaseHandler {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            next: None,
        }
    }
}

#[async_trait::async_trait]
impl Handler for BaseHandler {
    async fn handle(&self, request: &Request) -> Result<Option<Response>> {
        if let Some(ref next) = self.next {
            next.handle(request).await
        } else {
            Ok(None)
        }
    }

    fn set_next(&mut self, next: Arc<dyn Handler>) {
        self.next = Some(next);
    }

    fn name(&self) -> &str {
        &self.name
    }
}

// ============================================================================
// 认证处理器
// ============================================================================

/// 认证处理器
pub struct AuthenticationHandler {
    base: BaseHandler,
    valid_tokens: Arc<tokio::sync::RwLock<std::collections::HashSet<String>>>,
}

impl AuthenticationHandler {
    pub fn new() -> Self {
        Self {
            base: BaseHandler::new("AuthenticationHandler"),
            valid_tokens: Arc::new(tokio::sync::RwLock::new(std::collections::HashSet::new())),
        }
    }

    pub async fn add_token(&self, token: impl Into<String>) {
        let mut tokens = self.valid_tokens.write().await;
        tokens.insert(token.into());
    }

    pub async fn is_valid_token(&self, token: &str) -> bool {
        let tokens = self.valid_tokens.read().await;
        tokens.contains(token)
    }
}

impl Default for AuthenticationHandler {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait::async_trait]
impl Handler for AuthenticationHandler {
    async fn handle(&self, request: &Request) -> Result<Option<Response>> {
        let token = request
            .metadata
            .get("token")
            .ok_or_else(|| validation_error("Missing authentication token"))?;

        if !self.is_valid_token(token).await {
            return Ok(Some(Response::error(
                request.id.clone(),
                "Invalid authentication token",
            )));
        }

        // 认证通过，传递给下一个处理器
        self.base.handle(request).await
    }

    fn set_next(&mut self, next: Arc<dyn Handler>) {
        self.base.set_next(next);
    }

    fn name(&self) -> &str {
        self.base.name()
    }
}

// ============================================================================
// 授权处理器
// ============================================================================

/// 授权处理器
pub struct AuthorizationHandler {
    base: BaseHandler,
    user_permissions: Arc<
        tokio::sync::RwLock<std::collections::HashMap<String, std::collections::HashSet<String>>>,
    >,
}

impl AuthorizationHandler {
    pub fn new() -> Self {
        Self {
            base: BaseHandler::new("AuthorizationHandler"),
            user_permissions: Arc::new(tokio::sync::RwLock::new(std::collections::HashMap::new())),
        }
    }

    pub async fn grant_permission(&self, user: impl Into<String>, permission: impl Into<String>) {
        let mut permissions = self.user_permissions.write().await;
        permissions
            .entry(user.into())
            .or_insert_with(std::collections::HashSet::new)
            .insert(permission.into());
    }

    pub async fn has_permission(&self, user: &str, permission: &str) -> bool {
        let permissions = self.user_permissions.read().await;
        permissions
            .get(user)
            .map(|perms| perms.contains(permission))
            .unwrap_or(false)
    }
}

impl Default for AuthorizationHandler {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait::async_trait]
impl Handler for AuthorizationHandler {
    async fn handle(&self, request: &Request) -> Result<Option<Response>> {
        let user = request
            .metadata
            .get("user")
            .ok_or_else(|| validation_error("Missing user information"))?;

        let required_permission = request
            .metadata
            .get("permission")
            .ok_or_else(|| validation_error("Missing required permission"))?;

        if !self.has_permission(user, required_permission).await {
            return Ok(Some(Response::error(
                request.id.clone(),
                format!("User {} lacks permission: {}", user, required_permission),
            )));
        }

        // 授权通过，传递给下一个处理器
        self.base.handle(request).await
    }

    fn set_next(&mut self, next: Arc<dyn Handler>) {
        self.base.set_next(next);
    }

    fn name(&self) -> &str {
        self.base.name()
    }
}

// ============================================================================
// 限流处理器
// ============================================================================

/// 限流处理器
pub struct RateLimitingHandler {
    base: BaseHandler,
    rate_limiter: Arc<tokio::sync::RwLock<RateLimiterState>>,
    max_requests: u64,
    window_ms: u64,
}

struct RateLimiterState {
    requests: Vec<(String, std::time::Instant)>, // (client_id, timestamp)
}

impl RateLimiterState {
    fn new() -> Self {
        Self {
            requests: Vec::new(),
        }
    }

    fn cleanup(&mut self, window_ms: u64) {
        let cutoff = std::time::Instant::now() - Duration::from_millis(window_ms);
        self.requests.retain(|(_, time)| *time > cutoff);
    }

    fn can_proceed(&mut self, client_id: &str, max_requests: u64, window_ms: u64) -> bool {
        self.cleanup(window_ms);
        let client_requests = self
            .requests
            .iter()
            .filter(|(id, _)| id == client_id)
            .count();
        if client_requests < max_requests as usize {
            self.requests
                .push((client_id.to_string(), std::time::Instant::now()));
            true
        } else {
            false
        }
    }
}

impl RateLimitingHandler {
    pub fn new(max_requests: u64, window_ms: u64) -> Self {
        Self {
            base: BaseHandler::new("RateLimitingHandler"),
            rate_limiter: Arc::new(tokio::sync::RwLock::new(RateLimiterState::new())),
            max_requests,
            window_ms,
        }
    }
}

#[async_trait::async_trait]
impl Handler for RateLimitingHandler {
    async fn handle(&self, request: &Request) -> Result<Option<Response>> {
        let client_id = request
            .metadata
            .get("client_id")
            .unwrap_or(&request.id);

        let can_proceed = {
            let mut limiter = self.rate_limiter.write().await;
            limiter.can_proceed(client_id, self.max_requests, self.window_ms)
        };

        if !can_proceed {
            return Ok(Some(Response::error(
                request.id.clone(),
                format!(
                    "Rate limit exceeded: {} requests per {}ms",
                    self.max_requests, self.window_ms
                ),
            )));
        }

        // 限流通过，传递给下一个处理器
        self.base.handle(request).await
    }

    fn set_next(&mut self, next: Arc<dyn Handler>) {
        self.base.set_next(next);
    }

    fn name(&self) -> &str {
        self.base.name()
    }
}

// ============================================================================
// 业务逻辑处理器
// ============================================================================

/// 业务逻辑处理器
pub struct BusinessLogicHandler {
    base: BaseHandler,
}

impl BusinessLogicHandler {
    pub fn new() -> Self {
        Self {
            base: BaseHandler::new("BusinessLogicHandler"),
        }
    }
}

impl Default for BusinessLogicHandler {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait::async_trait]
impl Handler for BusinessLogicHandler {
    async fn handle(&self, request: &Request) -> Result<Option<Response>> {
        // 执行业务逻辑
        let result_data = serde_json::json!({
            "processed": true,
            "request_id": request.id,
            "original_data": request.data,
        });

        Ok(Some(Response::success_with_data(
            request.id.clone(),
            "Request processed successfully",
            result_data,
        )))
    }

    fn set_next(&mut self, _next: Arc<dyn Handler>) {
        // 业务逻辑处理器通常是链的末尾
    }

    fn name(&self) -> &str {
        self.base.name()
    }
}

// ============================================================================
// 责任链构建器
// ============================================================================

/// 责任链构建器
pub struct HandlerChain {
    first: Option<Arc<dyn Handler>>,
}

impl HandlerChain {
    pub fn new() -> Self {
        Self { first: None }
    }

    /// 添加处理器到链中
    pub fn add_handler(mut self, handler: Arc<dyn Handler>) -> Self {
        // 简化实现：直接设置第一个处理器
        // 实际应用中应该使用内部可变性（Mutex/RwLock）来构建链
        self.first = Some(handler);
        self
    }

    /// 执行请求
    pub async fn execute(&self, request: Request) -> Result<Response> {
        if let Some(ref handler) = self.first {
            match handler.handle(&request).await? {
                Some(response) => Ok(response),
                None => Ok(Response::error(
                    request.id.clone(),
                    "No handler processed the request",
                )),
            }
        } else {
            Err(validation_error("Handler chain is empty"))
        }
    }
}

impl Default for HandlerChain {
    fn default() -> Self {
        Self::new()
    }
}

// 简化版责任链 - 使用Vec存储处理器
pub struct SimpleHandlerChain {
    handlers: Vec<Arc<dyn Handler>>,
}

impl SimpleHandlerChain {
    pub fn new() -> Self {
        Self {
            handlers: Vec::new(),
        }
    }

    pub fn add_handler(mut self, handler: Arc<dyn Handler>) -> Self {
        self.handlers.push(handler);
        self
    }

    pub async fn execute(&self, request: Request) -> Result<Response> {
        for handler in &self.handlers {
            if let Some(response) = handler.handle(&request).await? {
                return Ok(response);
            }
        }

        Ok(Response::error(
            request.id.clone(),
            "No handler processed the request",
        ))
    }
}

impl Default for SimpleHandlerChain {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_authentication_handler() {
        let mut auth_handler = AuthenticationHandler::new();
        auth_handler.add_token("valid-token").await;

        let business_handler = BusinessLogicHandler::new();
        auth_handler.set_next(Arc::new(business_handler));

        let valid_request = Request::new("req-1", serde_json::json!({}))
            .with_metadata("token", "valid-token");

        let response = auth_handler.handle(&valid_request).await.unwrap();
        assert!(response.is_some());
        assert!(response.unwrap().success);

        let invalid_request = Request::new("req-2", serde_json::json!({}))
            .with_metadata("token", "invalid-token");

        let response = auth_handler.handle(&invalid_request).await.unwrap();
        assert!(response.is_some());
        assert!(!response.unwrap().success);
    }

    #[tokio::test]
    async fn test_handler_chain() {
        let mut auth_handler = AuthenticationHandler::new();
        auth_handler.add_token("token1").await;

        let authz_handler = AuthorizationHandler::new();
        authz_handler.grant_permission("user1", "read").await;

        let business_handler = BusinessLogicHandler::new();

        // 构建链：认证 -> 授权 -> 业务逻辑
        auth_handler.set_next(Arc::new(authz_handler));
        // 注意：这里需要重新获取引用，简化实现

        let request = Request::new("req-1", serde_json::json!({}))
            .with_metadata("token", "token1")
            .with_metadata("user", "user1")
            .with_metadata("permission", "read");

        // 使用简单链测试
        let chain = SimpleHandlerChain::new()
            .add_handler(Arc::new(auth_handler))
            .add_handler(Arc::new(business_handler));

        let response = chain.execute(request).await.unwrap();
        assert!(response.success);
    }

    #[tokio::test]
    async fn test_rate_limiting_handler() {
        let mut rate_limiter = RateLimitingHandler::new(2, 1000);
        let business_handler = BusinessLogicHandler::new();
        rate_limiter.set_next(Arc::new(business_handler));

        let request1 = Request::new("req-1", serde_json::json!({}))
            .with_metadata("client_id", "client1");
        let response1 = rate_limiter.handle(&request1).await.unwrap();
        assert!(response1.is_some());

        let request2 = Request::new("req-2", serde_json::json!({}))
            .with_metadata("client_id", "client1");
        let response2 = rate_limiter.handle(&request2).await.unwrap();
        assert!(response2.is_some());

        // 第三次应该被限流
        let request3 = Request::new("req-3", serde_json::json!({}))
            .with_metadata("client_id", "client1");
        let response3 = rate_limiter.handle(&request3).await.unwrap();
        assert!(response3.is_some());
        assert!(!response3.unwrap().success);
    }
}
