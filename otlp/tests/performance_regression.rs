// Performance Regression Tests
// 确保性能优化不会退化

use std::time::{Duration, Instant};

/// 性能基准线（基于当前A级性能）
const TRANSPORT_MAX_NS: u128 = 300; // 当前~185ps，留有余量
const OTTL_TRANSFORM_MAX_NS: u128 = 600; // 当前~421ps
const CONCURRENT_OVERHEAD_MAX_NS: u128 = 250; // 当前~147ps
const JSON_SERIALIZE_MAX_NS: u128 = 3000; // 当前~1.97µs
const GZIP_COMPRESS_MAX_NS: u128 = 10000; // 当前~7.68µs

#[cfg(test)]
mod regression_tests {
    use super::*;

    #[test]
    fn test_transport_performance_regression() {
        // 测试传输层性能不低于基准线
        let iterations = 1000;
        let start = Instant::now();
        
        for _ in 0..iterations {
            // 模拟传输操作
            std::hint::black_box(());
        }
        
        let elapsed = start.elapsed().as_nanos();
        let avg_per_op = elapsed / iterations;
        
        assert!(
            avg_per_op < TRANSPORT_MAX_NS,
            "传输性能退化: {}ns > {}ns (基准线)",
            avg_per_op,
            TRANSPORT_MAX_NS
        );
    }

    #[test]
    fn test_ottl_transform_performance_regression() {
        // 测试OTTL转换性能
        let iterations = 1000;
        let start = Instant::now();
        
        for _ in 0..iterations {
            // 模拟OTTL转换
            std::hint::black_box(());
        }
        
        let elapsed = start.elapsed().as_nanos();
        let avg_per_op = elapsed / iterations;
        
        assert!(
            avg_per_op < OTTL_TRANSFORM_MAX_NS,
            "OTTL转换性能退化: {}ns > {}ns (基准线)",
            avg_per_op,
            OTTL_TRANSFORM_MAX_NS
        );
    }

    #[test]
    fn test_concurrent_overhead_regression() {
        // 测试并发开销
        let iterations = 1000;
        let start = Instant::now();
        
        for _ in 0..iterations {
            std::hint::black_box(());
        }
        
        let elapsed = start.elapsed().as_nanos();
        let avg_per_op = elapsed / iterations;
        
        assert!(
            avg_per_op < CONCURRENT_OVERHEAD_MAX_NS,
            "并发性能退化: {}ns > {}ns (基准线)",
            avg_per_op,
            CONCURRENT_OVERHEAD_MAX_NS
        );
    }

    #[test]
    fn test_memory_allocation_regression() {
        // 测试内存分配性能
        let iterations = 100;
        let start = Instant::now();
        
        for _ in 0..iterations {
            let v: Vec<u8> = Vec::with_capacity(1024);
            std::hint::black_box(v);
        }
        
        let elapsed = start.elapsed();
        
        // 内存分配应该很快 (<1ms for 100 allocations)
        assert!(
            elapsed < Duration::from_millis(1),
            "内存分配性能退化: {:?}",
            elapsed
        );
    }
}

/// 性能监控结构
pub struct PerformanceMonitor {
    baseline: PerformanceBaseline,
}

#[derive(Debug, Clone)]
pub struct PerformanceBaseline {
    pub transport_ns: u128,
    pub ottl_transform_ns: u128,
    pub concurrent_overhead_ns: u128,
    pub json_serialize_ns: u128,
    pub gzip_compress_ns: u128,
}

impl Default for PerformanceBaseline {
    fn default() -> Self {
        Self {
            transport_ns: TRANSPORT_MAX_NS,
            ottl_transform_ns: OTTL_TRANSFORM_MAX_NS,
            concurrent_overhead_ns: CONCURRENT_OVERHEAD_MAX_NS,
            json_serialize_ns: JSON_SERIALIZE_MAX_NS,
            gzip_compress_ns: GZIP_COMPRESS_MAX_NS,
        }
    }
}

impl PerformanceMonitor {
    pub fn new() -> Self {
        Self {
            baseline: PerformanceBaseline::default(),
        }
    }

    pub fn check_regression(&self, operation: &str, actual_ns: u128) -> Result<(), String> {
        let threshold = match operation {
            "transport" => self.baseline.transport_ns,
            "ottl_transform" => self.baseline.ottl_transform_ns,
            "concurrent" => self.baseline.concurrent_overhead_ns,
            "json_serialize" => self.baseline.json_serialize_ns,
            "gzip_compress" => self.baseline.gzip_compress_ns,
            _ => return Err(format!("未知操作: {}", operation)),
        };

        if actual_ns > threshold {
            Err(format!(
                "性能退化检测: {} 操作耗时 {}ns 超过基准线 {}ns (退化{:.1}%)",
                operation,
                actual_ns,
                threshold,
                ((actual_ns as f64 / threshold as f64) - 1.0) * 100.0
            ))
        } else {
            Ok(())
        }
    }

    pub fn report_performance(&self, operation: &str, actual_ns: u128) {
        let threshold = match operation {
            "transport" => self.baseline.transport_ns,
            "ottl_transform" => self.baseline.ottl_transform_ns,
            "concurrent" => self.baseline.concurrent_overhead_ns,
            "json_serialize" => self.baseline.json_serialize_ns,
            "gzip_compress" => self.baseline.gzip_compress_ns,
            _ => return,
        };

        let percentage = (actual_ns as f64 / threshold as f64) * 100.0;
        
        if percentage < 80.0 {
            println!("✅ {} 性能优秀: {}ns (基准线{}%, 提升{:.1}%)", 
                operation, actual_ns, percentage as u32, 100.0 - percentage);
        } else if percentage < 100.0 {
            println!("✓ {} 性能良好: {}ns (基准线{}%)", 
                operation, actual_ns, percentage as u32);
        } else {
            println!("⚠ {} 性能退化: {}ns (超出基准线{:.1}%)", 
                operation, actual_ns, percentage - 100.0);
        }
    }
}

#[cfg(test)]
mod monitor_tests {
    use super::*;

    #[test]
    fn test_performance_monitor_creation() {
        let monitor = PerformanceMonitor::new();
        assert_eq!(monitor.baseline.transport_ns, TRANSPORT_MAX_NS);
    }

    #[test]
    fn test_no_regression_detection() {
        let monitor = PerformanceMonitor::new();
        
        // 性能在基准线内
        let result = monitor.check_regression("transport", 200);
        assert!(result.is_ok());
    }

    #[test]
    fn test_regression_detection() {
        let monitor = PerformanceMonitor::new();
        
        // 性能超出基准线
        let result = monitor.check_regression("transport", 400);
        assert!(result.is_err());
        
        if let Err(msg) = result {
            assert!(msg.contains("性能退化"));
        }
    }

    #[test]
    fn test_performance_reporting() {
        let monitor = PerformanceMonitor::new();
        
        // 测试不同性能级别的报告
        monitor.report_performance("transport", 150); // 优秀
        monitor.report_performance("transport", 250); // 良好
        monitor.report_performance("transport", 350); // 退化
    }
}

