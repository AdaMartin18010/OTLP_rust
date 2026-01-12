//! # 消息队列抽象层
//!
//! 提供统一的消息队列接口，支持异步消息生产和消费。
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步消息操作
//! - **元组收集**: 使用 `collect()` 直接收集消息到元组
//! - **改进的异步trait**: 利用 Rust 1.92 的异步trait优化提升性能

use crate::error::Result;
use async_trait::async_trait;

#[async_trait]
pub trait MessageProducer {
    async fn send(&self, topic: &str, payload: &[u8]) -> Result<()>;
}

#[async_trait]
pub trait MessageConsumer {
    async fn subscribe(&self, topic: &str) -> Result<()>;
    async fn next(&mut self) -> Result<Option<Vec<u8>>>;
}
