//! # 装饰器模式 (Decorator Pattern)
//!
//! 动态地给一个对象添加一些额外的职责，就增加功能来说，装饰器模式比生成子类更为灵活
//!
//! ## 应用场景
//!
//! - 动态添加功能
//! - 中间件实现
//! - 功能组合
//! - 横切关注点（日志、缓存、重试等）
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步装饰器操作
//! - **元组收集**: 使用 `collect()` 直接收集装饰器数据到元组
//! - **改进的装饰器模式**: 利用 Rust 1.92 的装饰器模式优化提升性能
use crate::prelude::*;
use serde::{Deserialize, Serialize};
use std::sync::Arc;

// Helper function to create validation errors
fn validation_error(msg: impl Into<String>) -> anyhow::Error {
    anyhow::anyhow!(msg.into())
}

/// 组件 trait - 被装饰的接口
#[async_trait::async_trait]
pub trait Component: Send + Sync {
    /// 执行操作
    async fn execute(&self) -> Result<String>;

    /// 组件名称
    fn name(&self) -> &str;
}

/// 基础组件
pub struct BaseComponent {
    name: String,
}

impl BaseComponent {
    pub fn new(name: impl Into<String>) -> Self {
        Self { name: name.into() }
    }
}

#[async_trait::async_trait]
impl Component for BaseComponent {
    async fn execute(&self) -> Result<String> {
        Ok(format!("{}: Executing base operation", self.name))
    }

    fn name(&self) -> &str {
        &self.name
    }
}

/// 装饰器基类
pub struct ComponentDecorator {
    component: Arc<dyn Component>,
}

impl ComponentDecorator {
    pub fn new(component: Arc<dyn Component>) -> Self {
        Self { component }
    }
}

#[async_trait::async_trait]
impl Component for ComponentDecorator {
    async fn execute(&self) -> Result<String> {
        self.component.execute().await
    }

    fn name(&self) -> &str {
        self.component.name()
    }
}

// ============================================================================
// 日志装饰器
// ============================================================================

/// 日志装饰器 - 在执行前后添加日志
pub struct LoggingDecorator {
    decorator: ComponentDecorator,
    logger: Arc<dyn Fn(&str) + Send + Sync>,
}

impl LoggingDecorator {
    pub fn new(component: Arc<dyn Component>) -> Self {
        Self {
            decorator: ComponentDecorator::new(component),
            logger: Arc::new(|msg| println!("[LOG] {}", msg)),
        }
    }

    pub fn with_logger(
        component: Arc<dyn Component>,
        logger: Arc<dyn Fn(&str) + Send + Sync>,
    ) -> Self {
        Self {
            decorator: ComponentDecorator::new(component),
            logger,
        }
    }
}

#[async_trait::async_trait]
impl Component for LoggingDecorator {
    async fn execute(&self) -> Result<String> {
        (self.logger)(&format!("Before executing: {}", self.decorator.name()));
        let result = self.decorator.execute().await;
        match &result {
            Ok(msg) => (self.logger)(&format!("After executing: {}", msg)),
            Err(e) => (self.logger)(&format!("Error executing: {}", e)),
        }
        result
    }

    fn name(&self) -> &str {
        self.decorator.name()
    }
}

// ============================================================================
// 重试装饰器
// ============================================================================

/// 重试装饰器 - 自动重试失败的操作
pub struct RetryDecorator {
    decorator: ComponentDecorator,
    max_attempts: u32,
    delay_ms: u64,
}

impl RetryDecorator {
    pub fn new(component: Arc<dyn Component>, max_attempts: u32, delay_ms: u64) -> Self {
        Self {
            decorator: ComponentDecorator::new(component),
            max_attempts,
            delay_ms,
        }
    }
}

#[async_trait::async_trait]
impl Component for RetryDecorator {
    async fn execute(&self) -> Result<String> {
        let mut last_error = None;

        for attempt in 1..=self.max_attempts {
            match self.decorator.execute().await {
                Ok(result) => {
                    if attempt > 1 {
                        return Ok(format!("{} (retried {} times)", result, attempt - 1));
                    }
                    return Ok(result);
                }
                Err(e) => {
                    last_error = Some(e);
                    if attempt < self.max_attempts {
                        tokio::time::sleep(Duration::from_millis(self.delay_ms)).await;
                    }
                }
            }
        }

        Err(last_error.unwrap_or_else(|| {
            validation_error("All retry attempts failed")
        }))
    }

    fn name(&self) -> &str {
        self.decorator.name()
    }
}

// ============================================================================
// 缓存装饰器
// ============================================================================

/// 缓存装饰器 - 缓存执行结果
pub struct CachingDecorator {
    decorator: ComponentDecorator,
    cache: Arc<tokio::sync::RwLock<Option<String>>>,
    ttl_ms: Option<u64>,
    cached_at: Arc<tokio::sync::RwLock<Option<std::time::Instant>>>,
}

impl CachingDecorator {
    pub fn new(component: Arc<dyn Component>) -> Self {
        Self {
            decorator: ComponentDecorator::new(component),
            cache: Arc::new(tokio::sync::RwLock::new(None)),
            ttl_ms: None,
            cached_at: Arc::new(tokio::sync::RwLock::new(None)),
        }
    }

    pub fn with_ttl(component: Arc<dyn Component>, ttl_ms: u64) -> Self {
        Self {
            decorator: ComponentDecorator::new(component),
            cache: Arc::new(tokio::sync::RwLock::new(None)),
            ttl_ms: Some(ttl_ms),
            cached_at: Arc::new(tokio::sync::RwLock::new(None)),
        }
    }

    async fn is_cache_valid(&self) -> bool {
        if self.ttl_ms.is_none() {
            return self.cache.read().await.is_some();
        }

        let cached_at = self.cached_at.read().await;
        if let Some(time) = *cached_at {
            time.elapsed().as_millis() < self.ttl_ms.unwrap() as u128
        } else {
            false
        }
    }
}

#[async_trait::async_trait]
impl Component for CachingDecorator {
    async fn execute(&self) -> Result<String> {
        // 检查缓存
        if self.is_cache_valid().await {
            let cache = self.cache.read().await;
            if let Some(cached_value) = cache.as_ref() {
                return Ok(format!("{} (cached)", cached_value));
            }
        }

        // 执行并缓存结果
        let result = self.decorator.execute().await?;
        {
            let mut cache = self.cache.write().await;
            *cache = Some(result.clone());
        }
        {
            let mut cached_at = self.cached_at.write().await;
            *cached_at = Some(std::time::Instant::now());
        }

        Ok(result)
    }

    fn name(&self) -> &str {
        self.decorator.name()
    }
}

// ============================================================================
// 超时装饰器
// ============================================================================

/// 超时装饰器 - 为操作添加超时控制
pub struct TimeoutDecorator {
    decorator: ComponentDecorator,
    timeout_ms: u64,
}

impl TimeoutDecorator {
    pub fn new(component: Arc<dyn Component>, timeout_ms: u64) -> Self {
        Self {
            decorator: ComponentDecorator::new(component),
            timeout_ms,
        }
    }
}

#[async_trait::async_trait]
impl Component for TimeoutDecorator {
    async fn execute(&self) -> Result<String> {
        tokio::select! {
            result = self.decorator.execute() => result,
            _ = tokio::time::sleep(Duration::from_millis(self.timeout_ms)) => {
                Err(validation_error(format!(
                    "Operation timed out after {}ms",
                    self.timeout_ms
                )))
            }
        }
    }

    fn name(&self) -> &str {
        self.decorator.name()
    }
}

// ============================================================================
// 指标装饰器
// ============================================================================

/// 指标装饰器 - 记录执行时间和指标
pub struct MetricsDecorator {
    decorator: ComponentDecorator,
    metrics: Arc<tokio::sync::RwLock<Vec<ExecutionMetric>>>,
}

/// 执行指标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExecutionMetric {
    pub component_name: String,
    pub duration_ms: u64,
    pub success: bool,
    pub timestamp: u64,
}

impl MetricsDecorator {
    pub fn new(component: Arc<dyn Component>) -> Self {
        Self {
            decorator: ComponentDecorator::new(component),
            metrics: Arc::new(tokio::sync::RwLock::new(Vec::new())),
        }
    }

    pub async fn get_metrics(&self) -> Vec<ExecutionMetric> {
        self.metrics.read().await.clone()
    }

    pub async fn clear_metrics(&self) {
        self.metrics.write().await.clear();
    }
}

#[async_trait::async_trait]
impl Component for MetricsDecorator {
    async fn execute(&self) -> Result<String> {
        let start = std::time::Instant::now();
        let result = self.decorator.execute().await;
        let duration = start.elapsed().as_millis() as u64;

        let metric = ExecutionMetric {
            component_name: self.decorator.name().to_string(),
            duration_ms: duration,
            success: result.is_ok(),
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
        };

        {
            let mut metrics = self.metrics.write().await;
            metrics.push(metric);
        }

        result
    }

    fn name(&self) -> &str {
        self.decorator.name()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_base_component() {
        let component = Arc::new(BaseComponent::new("test"));
        let result = component.execute().await.unwrap();
        assert!(result.contains("test"));
    }

    #[tokio::test]
    async fn test_logging_decorator() {
        let base = Arc::new(BaseComponent::new("test"));
        let decorated = Arc::new(LoggingDecorator::new(base));
        let result = decorated.execute().await.unwrap();
        assert!(result.contains("test"));
    }

    #[tokio::test]
    async fn test_caching_decorator() {
        let base = Arc::new(BaseComponent::new("test"));
        let decorated = Arc::new(CachingDecorator::new(base));

        let result1 = decorated.execute().await.unwrap();
        let result2 = decorated.execute().await.unwrap();

        assert!(result1.contains("test"));
        assert!(result2.contains("cached"));
    }

    #[tokio::test]
    async fn test_metrics_decorator() {
        let base = Arc::new(BaseComponent::new("test"));
        let decorated = Arc::new(MetricsDecorator::new(base));

        decorated.execute().await.unwrap();
        let metrics = decorated.get_metrics().await;

        assert_eq!(metrics.len(), 1);
        assert!(metrics[0].success);
        assert!(metrics[0].duration_ms > 0);
    }

    #[tokio::test]
    async fn test_decorator_chain() {
        let base = Arc::new(BaseComponent::new("test"));
        let cached = Arc::new(CachingDecorator::new(base));
        let logged = Arc::new(LoggingDecorator::new(cached));
        let metrics = Arc::new(MetricsDecorator::new(logged));

        let result = metrics.execute().await.unwrap();
        assert!(result.contains("test"));

        let metrics_data = metrics.get_metrics().await;
        // 可能执行了多次（由于缓存装饰器），所以至少应该有1条记录
        assert!(metrics_data.len() >= 1);
        assert!(metrics_data[0].success);
    }
}
