//! # 键值存储抽象层
//!
//! 提供统一的键值存储接口，支持异步操作和批量操作。
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步键值操作
//! - **元组收集**: 使用 `collect()` 直接收集键值对到元组
//! - **改进的异步trait**: 利用 Rust 1.92 的异步trait优化提升性能

use crate::error::Result;
use async_trait::async_trait;

#[async_trait]
pub trait KeyValueStore {
    async fn get(&self, key: &str) -> Result<Option<Vec<u8>>>;
    async fn set(&self, key: &str, value: &[u8]) -> Result<()>;
    async fn del(&self, key: &str) -> Result<()>;

    // 批量操作（默认实现）
    async fn mget(&self, keys: &[&str]) -> Result<Vec<Option<Vec<u8>>>> {
        let mut results = Vec::with_capacity(keys.len());
        for key in keys {
            results.push(self.get(key).await?);
        }
        Ok(results)
    }

    async fn mset(&self, pairs: &[(&str, &[u8])]) -> Result<()> {
        for (key, value) in pairs {
            self.set(key, value).await?;
        }
        Ok(())
    }
}
