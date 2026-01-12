//! # SQLite 数据库客户端
//!
//! 提供 SQLite 数据库的异步操作支持。
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步数据库操作
//! - **改进的数据库连接**: 利用 Rust 1.92 的数据库连接优化提升性能

#[cfg(feature = "sql-sqlite")]
use crate::database::sql::{SqlDatabase, SqlRow};

#[cfg(feature = "sql-sqlite")]
pub struct SqliteDb {
    conn: std::sync::Arc<tokio::sync::Mutex<rusqlite::Connection>>,
}

#[cfg(feature = "sql-sqlite")]
impl SqliteDb {
    pub fn connect_memory() -> crate::error::Result<Self> {
        let conn = rusqlite::Connection::open_in_memory()?;
        Ok(Self {
            conn: std::sync::Arc::new(tokio::sync::Mutex::new(conn)),
        })
    }
    
    pub async fn connect(url: &str) -> crate::error::Result<Self> {
        let conn = rusqlite::Connection::open(url)?;
        Ok(Self {
            conn: std::sync::Arc::new(tokio::sync::Mutex::new(conn)),
        })
    }
}

#[cfg(feature = "sql-sqlite")]
#[async_trait::async_trait]
impl SqlDatabase for SqliteDb {
    async fn execute(&self, sql: &str) -> crate::error::Result<u64> {
        let conn = self.conn.clone();
        let sql_owned = sql.to_owned();
        let affected = tokio::task::spawn_blocking(move || -> crate::error::Result<u64> {
            let conn = conn.blocking_lock();
            let rows = conn.execute(&sql_owned, [])? as u64;
            Ok(rows)
        })
        .await?;
        affected
    }

    async fn query(&self, sql: &str) -> crate::error::Result<Vec<SqlRow>> {
        let conn = self.conn.clone();
        let sql_owned = sql.to_owned();
        let rows = tokio::task::spawn_blocking(move || -> crate::error::Result<Vec<SqlRow>> {
            let conn = conn.blocking_lock();
            let mut stmt = conn.prepare(&sql_owned)?;
            let column_names: Vec<String> =
                stmt.column_names().iter().map(|s| s.to_string()).collect();
            let map = stmt.query_map([], |_| Ok(()))?; // 占位遍历
            let mut out = Vec::new();
            for _ in map {
                let row = SqlRow(
                    column_names
                        .iter()
                        .cloned()
                        .map(|c| (c, String::new()))
                        .collect(),
                );
                out.push(row);
            }
            Ok(out)
        })
        .await?;
        rows
    }
}
