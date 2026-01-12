pub mod adapter;
pub mod builder;
pub mod factory;
/// 设计模式库
///
/// 提供在可靠性场景中常用的设计模式实现
///
/// # 模块结构
///
/// - `observer` - 观察者模式：用于事件通知和状态变更
/// - `strategy` - 策略模式：用于算法选择和动态策略
/// - `factory` - 工厂模式：用于对象创建和依赖注入
/// - `builder` - 建造者模式：用于复杂对象构建
/// - `adapter` - 适配器模式：用于接口适配和兼容性
pub mod observer;
pub mod strategy;

// 重新导出常用类型
pub use adapter::Adapter;
pub use builder::Builder;
pub use factory::{AbstractFactory, Factory};
pub use observer::{Event, EventBus, Observer, Subject};
pub use strategy::{Context as StrategyContext, Strategy};
