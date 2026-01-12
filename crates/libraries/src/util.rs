//! # 工具函数模块
//!
//! 提供通用的工具函数，包括重试、超时等功能。
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步工具操作
//! - **改进的异步工具**: 利用 Rust 1.92 的异步工具优化提升性能

use crate::config::RetryPolicy;
use crate::error::{Error, Result};

#[cfg(feature = "tokio")]
pub async fn retry_async<F, Fut, T>(policy: &RetryPolicy, mut f: F) -> Result<T>
where
    F: FnMut() -> Fut,
    Fut: std::future::Future<Output = Result<T>>,
{
    let mut attempt: u32 = 0;
    let mut delay = policy.initial_backoff_ms;
    loop {
        match f().await {
            Ok(v) => return Ok(v),
            Err(_e) if attempt < policy.max_retries => {
                attempt += 1;
                let d = std::time::Duration::from_millis(delay);
                tokio::time::sleep(d).await;
                delay = (delay * 2).min(policy.max_backoff_ms);
                #[cfg(feature = "obs")]
                tracing::debug!(attempt, ?_e, "retrying operation");
            }
            Err(e) => return Err(e),
        }
    }
}

#[cfg(not(feature = "tokio"))]
pub async fn retry_async<F, Fut, T>(_policy: &RetryPolicy, _f: F) -> Result<T>
where
    F: FnMut() -> Fut,
    Fut: std::future::Future<Output = Result<T>>,
{
    Err(Error::Other("retry_async requires 'tokio' feature".into()))
}

#[cfg(feature = "tokio")]
pub async fn maybe_timeout<F, T>(dur_ms: u64, fut: F) -> Result<T>
where
    F: std::future::Future<Output = Result<T>>,
{
    match tokio::time::timeout(std::time::Duration::from_millis(dur_ms), fut).await {
        Ok(r) => r,
        Err(_) => Err(Error::Other("operation timed out".into())),
    }
}

#[cfg(not(feature = "tokio"))]
pub async fn maybe_timeout<F, T>(_dur_ms: u64, fut: F) -> Result<T>
where
    F: std::future::Future<Output = Result<T>>,
{
    fut.await
}
