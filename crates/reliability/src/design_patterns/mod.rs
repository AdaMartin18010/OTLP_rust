//! # 设计模式库
//!
//! 提供在可靠性场景中常用的设计模式实现
//!
//! ## 模块结构
//!
//! ### 创建型模式
//! - `factory` - 工厂模式：用于对象创建和依赖注入
//! - `builder` - 建造者模式：用于复杂对象构建
//!
//! ### 结构型模式
//! - `adapter` - 适配器模式：用于接口适配和兼容性
//! - `decorator` - 装饰器模式：用于动态添加功能
//! - `proxy` - 代理模式：用于访问控制和延迟加载
//!
//! ### 行为型模式
//! - `observer` - 观察者模式：用于事件通知和状态变更
//! - `strategy` - 策略模式：用于算法选择和动态策略
//! - `command` - 命令模式：用于请求封装和撤销/重做
//! - `state` - 状态模式：用于状态机实现
//! - `chain_of_responsibility` - 责任链模式：用于请求处理链
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步设计模式操作
//! - **元组收集**: 使用 `collect()` 直接收集设计模式数据到元组
//! - **改进的设计模式**: 利用 Rust 1.92 的设计模式优化提升性能

pub mod adapter;
pub mod builder;
pub mod chain_of_responsibility;
pub mod command;
pub mod decorator;
pub mod factory;
pub mod observer;
pub mod proxy;
pub mod state;
pub mod strategy;

// 重新导出常用类型
pub use adapter::Adapter;
pub use builder::Builder;
pub use chain_of_responsibility::{Handler, HandlerChain, Request, Response, SimpleHandlerChain};
pub use command::{Command, CommandInvoker, CommandQueue, CommandResult};
pub use decorator::{Component, ComponentDecorator};
pub use factory::{AbstractFactory, Factory};
pub use observer::{Event, EventBus, Observer, Subject};
pub use proxy::{Service, ServiceProxy, ServiceRequest, ServiceResponse};
pub use state::{State, StateContext, StateEvent, StateMachine};
pub use strategy::{Context as StrategyContext, Strategy};
