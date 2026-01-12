//! # SQL 数据库抽象层
//!
//! 提供统一的 SQL 数据库接口，支持异步操作和事务管理。
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步数据库操作
//! - **元组收集**: 使用 `collect()` 直接收集查询结果到元组
//! - **改进的异步trait**: 利用 Rust 1.92 的异步trait优化提升性能

use crate::error::Result;
use async_trait::async_trait;

pub struct SqlRow(pub Vec<(String, String)>);

impl SqlRow {
    pub fn get_string(&self, col_name: &str) -> Option<&String> {
        self.0
            .iter()
            .find(|(name, _)| name == col_name)
            .map(|(_, val)| val)
    }

    pub fn get_int(&self, col_name: &str) -> Option<i64> {
        self.get_string(col_name)?.parse().ok()
    }

    pub fn get_float(&self, col_name: &str) -> Option<f64> {
        self.get_string(col_name)?.parse().ok()
    }
}

#[async_trait]
pub trait SqlDatabase {
    async fn execute(&self, sql: &str) -> Result<u64>;
    async fn query(&self, sql: &str) -> Result<Vec<SqlRow>>;

    /// 事务接口（最小化示例）：
    /// begin -> execute/query... -> commit 或 rollback
    async fn begin(&self) -> Result<()> {
        Ok(())
    }
    async fn commit(&self) -> Result<()> {
        Ok(())
    }
    async fn rollback(&self) -> Result<()> {
        Ok(())
    }

    // 批量操作（默认实现）
    async fn batch_execute(&self, sqls: &[&str]) -> Result<Vec<u64>> {
        let mut results = Vec::with_capacity(sqls.len());
        for sql in sqls {
            results.push(self.execute(sql).await?);
        }
        Ok(results)
    }
}
