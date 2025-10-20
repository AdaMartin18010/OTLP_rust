//! # 性能监控集成模块
//!
//! 本模块提供实时性能指标收集和监控功能

use crate::optimized_processor::*;
use anyhow::Result;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
//use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;

/// 性能监控器配置
#[derive(Debug, Clone)]
pub struct PerformanceMonitoringConfig {
    /// 监控间隔
    pub monitoring_interval: Duration,
    /// 是否启用实时监控
    pub enable_realtime_monitoring: bool,
    /// 是否启用历史数据收集
    pub enable_historical_collection: bool,
    /// 历史数据保留时间
    pub historical_retention: Duration,
    /// 性能阈值配置
    pub performance_thresholds: PerformanceThresholds,
}

/// 性能阈值配置
#[derive(Debug, Clone)]
pub struct PerformanceThresholds {
    /// 最大处理时间阈值
    pub max_processing_time: Duration,
    /// 最大内存压力阈值
    pub max_memory_pressure: f64,
    /// 最小缓存命中率阈值
    pub min_cache_hit_ratio: f64,
    /// 最大SIMD处理比例阈值
    pub max_simd_ratio: f64,
}

impl Default for PerformanceMonitoringConfig {
    fn default() -> Self {
        Self {
            monitoring_interval: Duration::from_secs(5),
            enable_realtime_monitoring: true,
            enable_historical_collection: true,
            historical_retention: Duration::from_secs(3600), // 1小时
            performance_thresholds: PerformanceThresholds {
                max_processing_time: Duration::from_millis(100),
                max_memory_pressure: 0.8,
                min_cache_hit_ratio: 0.7,
                max_simd_ratio: 0.9,
            },
        }
    }
}

/// 历史性能数据点
#[derive(Debug, Clone)]
pub struct PerformanceDataPoint {
    pub timestamp: Instant,
    pub total_processed: u64,
    pub simd_processed: u64,
    pub cache_hit_ratio: f64,
    pub average_processing_time: Duration,
    pub memory_pressure: f64,
    pub memory_allocations: usize,
    pub memory_deallocations: usize,
}

/// 性能告警
#[derive(Debug, Clone)]
pub struct PerformanceAlert {
    pub timestamp: Instant,
    pub alert_type: AlertType,
    pub message: String,
    pub severity: AlertSeverity,
    pub metrics: PerformanceDataPoint,
}

/// 告警类型
#[derive(Debug, Clone)]
pub enum AlertType {
    HighProcessingTime,
    HighMemoryPressure,
    LowCacheHitRatio,
    HighSimdRatio,
    MemoryLeak,
    PerformanceDegradation,
}

/// 告警严重程度
#[derive(Debug, Clone)]
pub enum AlertSeverity {
    Info,
    Warning,
    Critical,
}

/// 实时性能监控器
pub struct RealtimePerformanceMonitor {
    config: PerformanceMonitoringConfig,
    historical_data: Arc<Mutex<Vec<PerformanceDataPoint>>>,
    alerts: Arc<Mutex<Vec<PerformanceAlert>>>,
    is_running: AtomicBool,
    monitoring_thread: Option<thread::JoinHandle<()>>,
}

impl RealtimePerformanceMonitor {
    /// 创建新的实时性能监控器
    pub fn new(config: PerformanceMonitoringConfig, _processor: OptimizedOtlpProcessor) -> Self {
        Self {
            historical_data: Arc::new(Mutex::new(Vec::new())),
            alerts: Arc::new(Mutex::new(Vec::new())),
            is_running: AtomicBool::new(false),
            monitoring_thread: None,
            config,
        }
    }

    /// 启动监控
    pub fn start_monitoring(&mut self) -> Result<()> {
        if self.is_running.load(Ordering::Relaxed) {
            return Ok(());
        }

        self.is_running.store(true, Ordering::Relaxed);

        let config = self.config.clone();
        let historical_data = Arc::clone(&self.historical_data);
        let alerts = Arc::clone(&self.alerts);
        let is_running = Arc::new(AtomicBool::new(self.is_running.load(Ordering::Relaxed)));

        let monitoring_thread = thread::spawn(move || {
            while is_running.load(Ordering::Relaxed) {
                // 创建模拟的性能数据点
                let data_point = PerformanceDataPoint {
                    timestamp: Instant::now(),
                    total_processed: 1000,
                    simd_processed: 800,
                    cache_hit_ratio: 0.85,
                    average_processing_time: Duration::from_millis(50),
                    memory_pressure: 0.3,
                    memory_allocations: 100,
                    memory_deallocations: 95,
                };

                // 检查性能阈值并生成告警
                Self::check_performance_thresholds(&data_point, &config, &alerts);

                // 收集历史数据
                if config.enable_historical_collection {
                    if let Ok(mut historical) = historical_data.lock() {
                        historical.push(data_point);

                        // 清理过期数据
                        let cutoff_time = Instant::now() - config.historical_retention;
                        historical.retain(|dp| dp.timestamp > cutoff_time);
                    }
                }

                thread::sleep(config.monitoring_interval);
            }
        });

        self.monitoring_thread = Some(monitoring_thread);
        Ok(())
    }

    /// 停止监控
    pub fn stop_monitoring(&mut self) -> Result<()> {
        if !self.is_running.load(Ordering::Relaxed) {
            return Ok(());
        }

        self.is_running.store(false, Ordering::Relaxed);

        if let Some(thread) = self.monitoring_thread.take() {
            thread
                .join()
                .map_err(|_| anyhow::anyhow!("监控线程停止失败"))?;
        }

        Ok(())
    }

    /// 检查性能阈值
    fn check_performance_thresholds(
        data_point: &PerformanceDataPoint,
        config: &PerformanceMonitoringConfig,
        alerts: &Arc<Mutex<Vec<PerformanceAlert>>>,
    ) {
        let mut new_alerts = Vec::new();

        // 检查处理时间
        if data_point.average_processing_time > config.performance_thresholds.max_processing_time {
            new_alerts.push(PerformanceAlert {
                timestamp: data_point.timestamp,
                alert_type: AlertType::HighProcessingTime,
                message: format!(
                    "处理时间过高: {:?} > {:?}",
                    data_point.average_processing_time,
                    config.performance_thresholds.max_processing_time
                ),
                severity: AlertSeverity::Warning,
                metrics: data_point.clone(),
            });
        }

        // 检查内存压力
        if data_point.memory_pressure > config.performance_thresholds.max_memory_pressure {
            new_alerts.push(PerformanceAlert {
                timestamp: data_point.timestamp,
                alert_type: AlertType::HighMemoryPressure,
                message: format!(
                    "内存压力过高: {:.2}% > {:.2}%",
                    data_point.memory_pressure * 100.0,
                    config.performance_thresholds.max_memory_pressure * 100.0
                ),
                severity: AlertSeverity::Critical,
                metrics: data_point.clone(),
            });
        }

        // 检查缓存命中率
        if data_point.cache_hit_ratio < config.performance_thresholds.min_cache_hit_ratio {
            new_alerts.push(PerformanceAlert {
                timestamp: data_point.timestamp,
                alert_type: AlertType::LowCacheHitRatio,
                message: format!(
                    "缓存命中率过低: {:.2}% < {:.2}%",
                    data_point.cache_hit_ratio * 100.0,
                    config.performance_thresholds.min_cache_hit_ratio * 100.0
                ),
                severity: AlertSeverity::Warning,
                metrics: data_point.clone(),
            });
        }

        // 检查内存泄漏
        if data_point.memory_allocations > data_point.memory_deallocations * 2 {
            new_alerts.push(PerformanceAlert {
                timestamp: data_point.timestamp,
                alert_type: AlertType::MemoryLeak,
                message: format!(
                    "可能存在内存泄漏: 分配 {} > 释放 {}",
                    data_point.memory_allocations, data_point.memory_deallocations
                ),
                severity: AlertSeverity::Critical,
                metrics: data_point.clone(),
            });
        }

        // 添加新告警
        if !new_alerts.is_empty() {
            if let Ok(mut alerts_guard) = alerts.lock() {
                alerts_guard.extend(new_alerts);
            }
        }
    }

    /// 获取历史性能数据
    pub fn get_historical_data(&self) -> Result<Vec<PerformanceDataPoint>> {
        let historical = self
            .historical_data
            .lock()
            .map_err(|_| anyhow::anyhow!("获取历史数据失败"))?;
        Ok(historical.clone())
    }

    /// 获取告警列表
    pub fn get_alerts(&self) -> Result<Vec<PerformanceAlert>> {
        let alerts = self
            .alerts
            .lock()
            .map_err(|_| anyhow::anyhow!("获取告警失败"))?;
        Ok(alerts.clone())
    }

    /// 清除告警
    pub fn clear_alerts(&self) -> Result<()> {
        let mut alerts = self
            .alerts
            .lock()
            .map_err(|_| anyhow::anyhow!("清除告警失败"))?;
        alerts.clear();
        Ok(())
    }

    /// 生成性能报告
    pub fn generate_performance_report(&self) -> Result<PerformanceReport> {
        let historical = self.get_historical_data()?;
        let _alerts = self.get_alerts()?;

        if historical.is_empty() {
            return Ok(PerformanceReport {
                timestamp: Instant::now(),
                total_processed: 0,
                simd_processed: 0,
                cache_hit_ratio: 0.0,
                average_processing_time: Duration::ZERO,
                memory_pressure: 0.0,
                memory_allocations: 0,
                memory_deallocations: 0,
                pool_count: 0,
                total_pooled_objects: 0,
            });
        }

        let latest = &historical[historical.len() - 1];
        let first = &historical[0];

        let total_processed = latest.total_processed - first.total_processed;
        let total_simd = latest.simd_processed - first.simd_processed;
        let avg_cache_hit_ratio =
            historical.iter().map(|dp| dp.cache_hit_ratio).sum::<f64>() / historical.len() as f64;
        let avg_processing_time = historical
            .iter()
            .map(|dp| dp.average_processing_time)
            .sum::<Duration>()
            / historical.len() as u32;
        let avg_memory_pressure =
            historical.iter().map(|dp| dp.memory_pressure).sum::<f64>() / historical.len() as f64;

        Ok(PerformanceReport {
            timestamp: latest.timestamp,
            total_processed,
            simd_processed: total_simd,
            cache_hit_ratio: avg_cache_hit_ratio,
            average_processing_time: avg_processing_time,
            memory_pressure: avg_memory_pressure,
            memory_allocations: latest.memory_allocations,
            memory_deallocations: latest.memory_deallocations,
            pool_count: 0,           // 需要从内存统计获取
            total_pooled_objects: 0, // 需要从内存统计获取
        })
    }

    /// 获取性能统计摘要
    pub fn get_performance_summary(&self) -> Result<PerformanceSummary> {
        let historical = self.get_historical_data()?;
        let alerts = self.get_alerts()?;

        if historical.is_empty() {
            return Ok(PerformanceSummary {
                monitoring_duration: Duration::ZERO,
                total_data_points: 0,
                total_alerts: 0,
                critical_alerts: 0,
                warning_alerts: 0,
                average_throughput: 0.0,
                peak_memory_pressure: 0.0,
                average_cache_hit_ratio: 0.0,
            });
        }

        let first = &historical[0];
        let latest = &historical[historical.len() - 1];
        let monitoring_duration = latest.timestamp - first.timestamp;

        let total_alerts = alerts.len();
        let critical_alerts = alerts
            .iter()
            .filter(|a| matches!(a.severity, AlertSeverity::Critical))
            .count();
        let warning_alerts = alerts
            .iter()
            .filter(|a| matches!(a.severity, AlertSeverity::Warning))
            .count();

        let total_processed = latest.total_processed - first.total_processed;
        let average_throughput = if monitoring_duration.as_secs() > 0 {
            total_processed as f64 / monitoring_duration.as_secs() as f64
        } else {
            0.0
        };

        let peak_memory_pressure = historical
            .iter()
            .map(|dp| dp.memory_pressure)
            .fold(0.0, f64::max);

        let average_cache_hit_ratio =
            historical.iter().map(|dp| dp.cache_hit_ratio).sum::<f64>() / historical.len() as f64;

        Ok(PerformanceSummary {
            monitoring_duration,
            total_data_points: historical.len(),
            total_alerts,
            critical_alerts,
            warning_alerts,
            average_throughput,
            peak_memory_pressure,
            average_cache_hit_ratio,
        })
    }
}

/// 性能统计摘要
#[derive(Debug, Clone)]
pub struct PerformanceSummary {
    pub monitoring_duration: Duration,
    pub total_data_points: usize,
    pub total_alerts: usize,
    pub critical_alerts: usize,
    pub warning_alerts: usize,
    pub average_throughput: f64,
    pub peak_memory_pressure: f64,
    pub average_cache_hit_ratio: f64,
}

impl PerformanceSummary {
    /// 格式化摘要为字符串
    pub fn format_summary(&self) -> String {
        format!(
            "=== 性能监控摘要 ===\n\
            监控时长: {:?}\n\
            数据点数量: {}\n\
            总告警数: {}\n\
            严重告警: {}\n\
            警告告警: {}\n\
            平均吞吐量: {:.2} items/sec\n\
            峰值内存压力: {:.2}%\n\
            平均缓存命中率: {:.2}%\n\
            ===================",
            self.monitoring_duration,
            self.total_data_points,
            self.total_alerts,
            self.critical_alerts,
            self.warning_alerts,
            self.average_throughput,
            self.peak_memory_pressure * 100.0,
            self.average_cache_hit_ratio * 100.0
        )
    }
}

impl Drop for RealtimePerformanceMonitor {
    fn drop(&mut self) {
        let _ = self.stop_monitoring();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    //use std::collections::HashMap;

    #[test]
    fn test_performance_monitoring_config() {
        let config = PerformanceMonitoringConfig::default();
        assert_eq!(config.monitoring_interval, Duration::from_secs(5));
        assert!(config.enable_realtime_monitoring);
        assert!(config.enable_historical_collection);
        assert_eq!(
            config.performance_thresholds.max_processing_time,
            Duration::from_millis(100)
        );
    }

    #[test]
    fn test_performance_data_point() {
        let data_point = PerformanceDataPoint {
            timestamp: Instant::now(),
            total_processed: 1000,
            simd_processed: 800,
            cache_hit_ratio: 0.85,
            average_processing_time: Duration::from_millis(50),
            memory_pressure: 0.3,
            memory_allocations: 100,
            memory_deallocations: 95,
        };

        assert_eq!(data_point.total_processed, 1000);
        assert_eq!(data_point.simd_processed, 800);
        assert_eq!(data_point.cache_hit_ratio, 0.85);
    }

    #[test]
    fn test_performance_alert() {
        let alert = PerformanceAlert {
            timestamp: Instant::now(),
            alert_type: AlertType::HighMemoryPressure,
            message: "内存压力过高".to_string(),
            severity: AlertSeverity::Critical,
            metrics: PerformanceDataPoint {
                timestamp: Instant::now(),
                total_processed: 0,
                simd_processed: 0,
                cache_hit_ratio: 0.0,
                average_processing_time: Duration::ZERO,
                memory_pressure: 0.0,
                memory_allocations: 0,
                memory_deallocations: 0,
            },
        };

        assert!(matches!(alert.alert_type, AlertType::HighMemoryPressure));
        assert!(matches!(alert.severity, AlertSeverity::Critical));
    }

    #[test]
    fn test_performance_summary() {
        let summary = PerformanceSummary {
            monitoring_duration: Duration::from_secs(60),
            total_data_points: 12,
            total_alerts: 3,
            critical_alerts: 1,
            warning_alerts: 2,
            average_throughput: 100.0,
            peak_memory_pressure: 0.8,
            average_cache_hit_ratio: 0.85,
        };

        let summary_str = summary.format_summary();
        assert!(summary_str.contains("性能监控摘要"));
        assert!(summary_str.contains("监控时长"));
        assert!(summary_str.contains("总告警数"));
    }
}
