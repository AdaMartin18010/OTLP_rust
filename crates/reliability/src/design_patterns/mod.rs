//! # 设计模式库
//!
//! 提供在可靠性场景中常用的设计模式实现
//!
//! ## 模块结构
//!
//! - `observer` - 观察者模式：用于事件通知和状态变更
//! - `strategy` - 策略模式：用于算法选择和动态策略
//! - `factory` - 工厂模式：用于对象创建和依赖注入
//! - `builder` - 建造者模式：用于复杂对象构建
//! - `adapter` - 适配器模式：用于接口适配和兼容性
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步设计模式操作
//! - **元组收集**: 使用 `collect()` 直接收集设计模式数据到元组
//! - **改进的设计模式**: 利用 Rust 1.92 的设计模式优化提升性能

pub mod adapter;
pub mod builder;
pub mod factory;
pub mod observer;
pub mod strategy;

// 重新导出常用类型
pub use adapter::Adapter;
pub use builder::Builder;
pub use factory::{AbstractFactory, Factory};
pub use observer::{Event, EventBus, Observer, Subject};
pub use strategy::{Context as StrategyContext, Strategy};
