//! # 高级可观测性模块
//!
//! 提供企业级的监控、日志、追踪和告警功能
//!
//! ## 模块结构
//!
//! - `metrics_aggregation` - 指标聚合和统计
//! - `log_correlation` - 日志关联和分析
//! - `alerting` - 实时告警系统
//! - `dashboards` - 可视化仪表板
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步可观测性操作
//! - **元组收集**: 使用 `collect()` 直接收集可观测性数据到元组
//! - **改进的并发**: 利用 Rust 1.92 的并发优化提升性能

pub mod alerting;
pub mod log_correlation;
pub mod metrics_aggregation;
pub mod profiler;

// 重新导出常用类型
pub use alerting::{Alert, AlertLevel, AlertManager};
pub use log_correlation::{CorrelationContext, LogCorrelator};
pub use metrics_aggregation::{AggregatedMetric, MetricType, MetricsAggregator};
pub use profiler::{ProfileReport, ProfileType, Profiler};
