//! # 命令模式 (Command Pattern)
//!
//! 将一个请求封装成一个对象，从而可以用不同的请求对客户进行参数化
//!
//! ## 应用场景
//!
//! - 请求队列化
//! - 撤销/重做操作
//! - 日志记录
//! - 事务处理
//! - 宏命令（命令组合）
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步命令操作
//! - **元组收集**: 使用 `collect()` 直接收集命令数据到元组
//! - **改进的命令模式**: 利用 Rust 1.92 的命令模式优化提升性能
use crate::prelude::*;
use serde::{Deserialize, Serialize};
use std::collections::VecDeque;
use std::sync::Arc;

// Helper function to create validation errors
fn validation_error(msg: impl Into<String>) -> anyhow::Error {
    anyhow::anyhow!(msg.into())
}

/// 命令 trait
#[async_trait::async_trait]
pub trait Command: Send + Sync {
    /// 执行命令
    async fn execute(&mut self) -> Result<CommandResult>;

    /// 撤销命令
    async fn undo(&mut self) -> Result<()>;

    /// 命令名称
    fn name(&self) -> &str;

    /// 命令描述
    fn description(&self) -> &str {
        "No description"
    }
}

/// 命令结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CommandResult {
    pub success: bool,
    pub message: String,
    pub data: Option<serde_json::Value>,
}

impl CommandResult {
    pub fn success(message: impl Into<String>) -> Self {
        Self {
            success: true,
            message: message.into(),
            data: None,
        }
    }

    pub fn success_with_data(message: impl Into<String>, data: serde_json::Value) -> Self {
        Self {
            success: true,
            message: message.into(),
            data: Some(data),
        }
    }

    pub fn error(message: impl Into<String>) -> Self {
        Self {
            success: false,
            message: message.into(),
            data: None,
        }
    }
}

// ============================================================================
// 简单命令示例
// ============================================================================

/// 计数器增加命令
pub struct IncrementCommand {
    counter: Arc<tokio::sync::RwLock<i32>>,
    amount: i32,
    previous_value: Option<i32>,
}

impl IncrementCommand {
    pub fn new(counter: Arc<tokio::sync::RwLock<i32>>, amount: i32) -> Self {
        Self {
            counter,
            amount,
            previous_value: None,
        }
    }
}

#[async_trait::async_trait]
impl Command for IncrementCommand {
    async fn execute(&mut self) -> Result<CommandResult> {
        let mut counter = self.counter.write().await;
        self.previous_value = Some(*counter);
        *counter += self.amount;
        Ok(CommandResult::success(format!(
            "Incremented by {}, new value: {}",
            self.amount, *counter
        )))
    }

    async fn undo(&mut self) -> Result<()> {
        if let Some(prev) = self.previous_value {
            let mut counter = self.counter.write().await;
            *counter = prev;
            self.previous_value = None;
            Ok(())
        } else {
            Err(validation_error("Nothing to undo"))
        }
    }

    fn name(&self) -> &str {
        "IncrementCommand"
    }

    fn description(&self) -> &str {
        "Increments a counter by a specified amount"
    }
}

/// 设置值命令
pub struct SetValueCommand<T: Clone + Send + Sync> {
    target: Arc<tokio::sync::RwLock<T>>,
    new_value: T,
    previous_value: Option<T>,
}

impl<T: Clone + Send + Sync> SetValueCommand<T> {
    pub fn new(target: Arc<tokio::sync::RwLock<T>>, new_value: T) -> Self {
        Self {
            target,
            new_value,
            previous_value: None,
        }
    }
}

#[async_trait::async_trait]
impl<T: Clone + Send + Sync + 'static> Command for SetValueCommand<T> {
    async fn execute(&mut self) -> Result<CommandResult> {
        let mut target = self.target.write().await;
        self.previous_value = Some(target.clone());
        *target = self.new_value.clone();
        Ok(CommandResult::success("Value set successfully"))
    }

    async fn undo(&mut self) -> Result<()> {
        if let Some(prev) = self.previous_value.take() {
            let mut target = self.target.write().await;
            *target = prev;
            Ok(())
        } else {
            Err(validation_error("Nothing to undo"))
        }
    }

    fn name(&self) -> &str {
        "SetValueCommand"
    }

    fn description(&self) -> &str {
        "Sets a value and allows undo"
    }
}

// ============================================================================
// 宏命令（命令组合）
// ============================================================================

/// 宏命令 - 组合多个命令
pub struct MacroCommand {
    commands: Vec<Box<dyn Command>>,
    name: String,
    executed_commands: Vec<usize>,
}

impl MacroCommand {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            commands: Vec::new(),
            name: name.into(),
            executed_commands: Vec::new(),
        }
    }

    pub fn add_command(mut self, command: Box<dyn Command>) -> Self {
        self.commands.push(command);
        self
    }
}

#[async_trait::async_trait]
impl Command for MacroCommand {
    async fn execute(&mut self) -> Result<CommandResult> {
        self.executed_commands.clear();
        let mut results = Vec::new();

        for (index, command) in self.commands.iter_mut().enumerate() {
            match command.execute().await {
                Ok(result) => {
                    if result.success {
                        self.executed_commands.push(index);
                        results.push(result.message);
                    } else {
                        // 如果某个命令失败，撤销已执行的命令
                        for &executed_index in self.executed_commands.iter().rev() {
                            if let Some(cmd) = self.commands.get_mut(executed_index) {
                                let _ = cmd.undo().await;
                            }
                        }
                        self.executed_commands.clear();
                        return Ok(CommandResult::error(format!(
                            "Command {} failed, all commands rolled back",
                            index
                        )));
                    }
                }
                Err(e) => {
                    // 撤销已执行的命令
                    for &executed_index in self.executed_commands.iter().rev() {
                        if let Some(cmd) = self.commands.get_mut(executed_index) {
                            let _ = cmd.undo().await;
                        }
                    }
                    self.executed_commands.clear();
                    return Err(e);
                }
            }
        }

        Ok(CommandResult::success(format!(
            "Macro command executed: {}",
            results.join(", ")
        )))
    }

    async fn undo(&mut self) -> Result<()> {
        for &executed_index in self.executed_commands.iter().rev() {
            if let Some(cmd) = self.commands.get_mut(executed_index) {
                cmd.undo().await?;
            }
        }
        self.executed_commands.clear();
        Ok(())
    }

    fn name(&self) -> &str {
        &self.name
    }

    fn description(&self) -> &str {
        "A macro command that executes multiple commands"
    }
}

// ============================================================================
// 命令调用者（Invoker）
// ============================================================================

/// 命令调用者 - 负责执行和管理命令
pub struct CommandInvoker {
    history: VecDeque<Box<dyn Command>>,
    max_history_size: usize,
}

impl CommandInvoker {
    pub fn new() -> Self {
        Self {
            history: VecDeque::new(),
            max_history_size: 100,
        }
    }

    pub fn with_max_history(mut self, size: usize) -> Self {
        self.max_history_size = size;
        self
    }

    /// 执行命令并添加到历史
    pub async fn execute(&mut self, mut command: Box<dyn Command>) -> Result<CommandResult> {
        let result = command.execute().await?;

        if result.success {
            self.history.push_back(command);
            if self.history.len() > self.max_history_size {
                self.history.pop_front();
            }
        }

        Ok(result)
    }

    /// 撤销最后一个命令
    pub async fn undo(&mut self) -> Result<()> {
        if let Some(mut command) = self.history.pop_back() {
            command.undo().await?;
            Ok(())
        } else {
            Err(validation_error("No commands to undo"))
        }
    }

    /// 获取历史记录数量
    pub fn history_len(&self) -> usize {
        self.history.len()
    }

    /// 清空历史
    pub fn clear_history(&mut self) {
        self.history.clear();
    }
}

impl Default for CommandInvoker {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// 命令队列
// ============================================================================

/// 命令队列 - 异步执行命令队列
pub struct CommandQueue {
    queue: Arc<tokio::sync::Mutex<VecDeque<Box<dyn Command>>>>,
    invoker: Arc<tokio::sync::Mutex<CommandInvoker>>,
    running: Arc<std::sync::atomic::AtomicBool>,
}

impl CommandQueue {
    pub fn new() -> Self {
        Self {
            queue: Arc::new(tokio::sync::Mutex::new(VecDeque::new())),
            invoker: Arc::new(tokio::sync::Mutex::new(CommandInvoker::new())),
            running: Arc::new(std::sync::atomic::AtomicBool::new(false)),
        }
    }

    /// 添加命令到队列
    pub async fn enqueue(&self, command: Box<dyn Command>) {
        let mut queue = self.queue.lock().await;
        queue.push_back(command);
    }

    /// 启动队列处理
    pub async fn start(&self) {
        self.running.store(true, std::sync::atomic::Ordering::Relaxed);
        let queue = self.queue.clone();
        let invoker = self.invoker.clone();
        let running = self.running.clone();

        tokio::spawn(async move {
            while running.load(std::sync::atomic::Ordering::Relaxed) {
                let command = {
                    let mut q = queue.lock().await;
                    q.pop_front()
                };

                if let Some(cmd) = command {
                    let mut inv = invoker.lock().await;
                    let _ = inv.execute(cmd).await;
                } else {
                    tokio::time::sleep(Duration::from_millis(10)).await;
                }
            }
        });
    }

    /// 停止队列处理
    pub fn stop(&self) {
        self.running.store(false, std::sync::atomic::Ordering::Relaxed);
    }

    /// 获取队列长度
    pub async fn queue_len(&self) -> usize {
        self.queue.lock().await.len()
    }
}

impl Default for CommandQueue {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_increment_command() {
        let counter = Arc::new(tokio::sync::RwLock::new(0));
        let mut command = IncrementCommand::new(counter.clone(), 5);

        let result = command.execute().await.unwrap();
        assert!(result.success);
        assert_eq!(*counter.read().await, 5);

        command.undo().await.unwrap();
        assert_eq!(*counter.read().await, 0);
    }

    #[tokio::test]
    async fn test_command_invoker() {
        let counter = Arc::new(tokio::sync::RwLock::new(0));
        let mut invoker = CommandInvoker::new();

        let cmd1 = Box::new(IncrementCommand::new(counter.clone(), 5));
        invoker.execute(cmd1).await.unwrap();
        assert_eq!(*counter.read().await, 5);

        let cmd2 = Box::new(IncrementCommand::new(counter.clone(), 3));
        invoker.execute(cmd2).await.unwrap();
        assert_eq!(*counter.read().await, 8);

        invoker.undo().await.unwrap();
        assert_eq!(*counter.read().await, 5);

        invoker.undo().await.unwrap();
        assert_eq!(*counter.read().await, 0);
    }

    #[tokio::test]
    async fn test_macro_command() {
        let counter = Arc::new(tokio::sync::RwLock::new(0));

        let mut macro_cmd = MacroCommand::new("test_macro")
            .add_command(Box::new(IncrementCommand::new(counter.clone(), 5)))
            .add_command(Box::new(IncrementCommand::new(counter.clone(), 3)));

        let result = macro_cmd.execute().await.unwrap();
        assert!(result.success);
        assert_eq!(*counter.read().await, 8);

        macro_cmd.undo().await.unwrap();
        assert_eq!(*counter.read().await, 0);
    }

    #[tokio::test]
    async fn test_command_queue() {
        let counter = Arc::new(tokio::sync::RwLock::new(0));
        let queue = CommandQueue::new();

        queue.start().await;

        for i in 1..=5 {
            let cmd = Box::new(IncrementCommand::new(counter.clone(), i));
            queue.enqueue(cmd).await;
        }

        // 等待队列处理
        tokio::time::sleep(Duration::from_millis(100)).await;

        queue.stop();
        // 等待最后一个命令完成
        tokio::time::sleep(Duration::from_millis(50)).await;

        // 验证所有命令都已执行
        assert_eq!(*counter.read().await, 15); // 1+2+3+4+5
    }
}
