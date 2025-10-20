//! # 测试报告生成器
//!
//! 生成详细的测试报告，包括测试结果、性能指标和覆盖率信息。
use std::time::{Duration, SystemTime};

/// 测试结果
#[derive(Debug, Clone, serde::Serialize)]
pub struct TestResult {
    pub name: String,
    pub status: TestStatus,
    pub duration: Duration,
    pub error_message: Option<String>,
    pub performance_metrics: Option<PerformanceMetrics>,
}

/// 测试状态
#[derive(Debug, Clone, PartialEq, serde::Serialize)]
pub enum TestStatus {
    Passed,
    Failed,
    Skipped,
    Timeout,
}

/// 性能指标
#[derive(Debug, Clone, serde::Serialize)]
pub struct PerformanceMetrics {
    pub throughput: f64,     // 每秒处理的数据量
    pub latency: Duration,   // 平均延迟
    pub memory_usage: usize, // 内存使用量（字节）
    pub cpu_usage: f64,      // CPU使用率（百分比）
}

/// 测试报告
#[derive(Debug, Clone, serde::Serialize)]
pub struct TestReport {
    pub test_suite: String,
    pub start_time: SystemTime,
    pub end_time: SystemTime,
    pub total_tests: usize,
    pub passed_tests: usize,
    pub failed_tests: usize,
    pub skipped_tests: usize,
    pub timeout_tests: usize,
    pub total_duration: Duration,
    pub results: Vec<TestResult>,
    pub summary: TestSummary,
}

/// 测试摘要
#[derive(Debug, Clone, serde::Serialize)]
pub struct TestSummary {
    pub success_rate: f64,
    pub average_duration: Duration,
    pub slowest_test: Option<String>,
    pub fastest_test: Option<String>,
    pub performance_summary: Option<PerformanceSummary>,
}

/// 性能摘要
#[derive(Debug, Clone, serde::Serialize)]
pub struct PerformanceSummary {
    pub average_throughput: f64,
    pub average_latency: Duration,
    pub peak_memory_usage: usize,
    pub average_cpu_usage: f64,
}

/// 测试报告生成器
pub struct TestReporter {
    results: Vec<TestResult>,
    start_time: SystemTime,
}

impl TestReporter {
    /// 创建新的测试报告生成器
    pub fn new() -> Self {
        Self {
            results: Vec::new(),
            start_time: SystemTime::now(),
        }
    }

    /// 添加测试结果
    pub fn add_result(&mut self, result: TestResult) {
        self.results.push(result);
    }

    /// 生成测试报告
    pub fn generate_report(&self, test_suite: &str) -> TestReport {
        let end_time = SystemTime::now();
        let total_duration = end_time.duration_since(self.start_time).unwrap_or_default();

        let total_tests = self.results.len();
        let passed_tests = self
            .results
            .iter()
            .filter(|r| r.status == TestStatus::Passed)
            .count();
        let failed_tests = self
            .results
            .iter()
            .filter(|r| r.status == TestStatus::Failed)
            .count();
        let skipped_tests = self
            .results
            .iter()
            .filter(|r| r.status == TestStatus::Skipped)
            .count();
        let timeout_tests = self
            .results
            .iter()
            .filter(|r| r.status == TestStatus::Timeout)
            .count();

        let success_rate = if total_tests > 0 {
            (passed_tests as f64 / total_tests as f64) * 100.0
        } else {
            0.0
        };

        let average_duration = if total_tests > 0 {
            let total_duration_ms: u64 = self
                .results
                .iter()
                .map(|r| r.duration.as_millis() as u64)
                .sum();
            Duration::from_millis(total_duration_ms / total_tests as u64)
        } else {
            Duration::default()
        };

        let slowest_test = self
            .results
            .iter()
            .max_by_key(|r| r.duration)
            .map(|r| r.name.clone());

        let fastest_test = self
            .results
            .iter()
            .min_by_key(|r| r.duration)
            .map(|r| r.name.clone());

        let performance_summary = self.generate_performance_summary();

        let summary = TestSummary {
            success_rate,
            average_duration,
            slowest_test,
            fastest_test,
            performance_summary,
        };

        TestReport {
            test_suite: test_suite.to_string(),
            start_time: self.start_time,
            end_time,
            total_tests,
            passed_tests,
            failed_tests,
            skipped_tests,
            timeout_tests,
            total_duration,
            results: self.results.clone(),
            summary,
        }
    }

    /// 生成性能摘要
    fn generate_performance_summary(&self) -> Option<PerformanceSummary> {
        let performance_results: Vec<&PerformanceMetrics> = self
            .results
            .iter()
            .filter_map(|r| r.performance_metrics.as_ref())
            .collect();

        if performance_results.is_empty() {
            return None;
        }

        let average_throughput = performance_results
            .iter()
            .map(|m| m.throughput)
            .sum::<f64>()
            / performance_results.len() as f64;

        let average_latency_ms = performance_results
            .iter()
            .map(|m| m.latency.as_millis() as u64)
            .sum::<u64>()
            / performance_results.len() as u64;
        let average_latency = Duration::from_millis(average_latency_ms);

        let peak_memory_usage = performance_results
            .iter()
            .map(|m| m.memory_usage)
            .max()
            .unwrap_or(0);

        let average_cpu_usage = performance_results.iter().map(|m| m.cpu_usage).sum::<f64>()
            / performance_results.len() as f64;

        Some(PerformanceSummary {
            average_throughput,
            average_latency,
            peak_memory_usage,
            average_cpu_usage,
        })
    }

    /// 生成HTML报告
    pub fn generate_html_report(&self, test_suite: &str) -> String {
        let report = self.generate_report(test_suite);

        format!(
            r#"
<!DOCTYPE html>
<html>
<head>
    <title>OTLP Rust 测试报告 - {}</title>
    <style>
        body {{ font-family: Arial, sans-serif; margin: 20px; }}
        .header {{ background-color: #f0f0f0; padding: 20px; border-radius: 5px; }}
        .summary {{ background-color: #e8f5e8; padding: 15px; border-radius: 5px; margin: 20px 0; }}
        .failed {{ background-color: #ffe8e8; padding: 15px; border-radius: 5px; margin: 20px 0; }}
        .performance {{ background-color: #e8f0ff; padding: 15px; border-radius: 5px; margin: 20px 0; }}
        table {{ border-collapse: collapse; width: 100%; }}
        th, td {{ border: 1px solid #ddd; padding: 8px; text-align: left; }}
        th {{ background-color: #f2f2f2; }}
        .status-passed {{ color: green; font-weight: bold; }}
        .status-failed {{ color: red; font-weight: bold; }}
        .status-skipped {{ color: orange; font-weight: bold; }}
        .status-timeout {{ color: purple; font-weight: bold; }}
    </style>
</head>
<body>
    <div class="header">
        <h1>OTLP Rust 测试报告</h1>
        <h2>{}</h2>
        <p>测试时间: {} - {}</p>
        <p>总耗时: {:?}</p>
    </div>
    
    <div class="summary">
        <h3>测试摘要</h3>
        <ul>
            <li>总测试数: {}</li>
            <li>通过: {} ({:.1}%)</li>
            <li>失败: {} ({:.1}%)</li>
            <li>跳过: {} ({:.1}%)</li>
            <li>超时: {} ({:.1}%)</li>
            <li>平均耗时: {:?}</li>
        </ul>
    </div>
    
    <div class="performance">
        <h3>性能摘要</h3>
        {}
    </div>
    
    <h3>详细结果</h3>
    <table>
        <tr>
            <th>测试名称</th>
            <th>状态</th>
            <th>耗时</th>
            <th>错误信息</th>
        </tr>
        {}
    </table>
</body>
</html>
        "#,
            test_suite,
            test_suite,
            format_time(report.start_time),
            format_time(report.end_time),
            report.total_duration,
            report.total_tests,
            report.passed_tests,
            (report.passed_tests as f64 / report.total_tests as f64) * 100.0,
            report.failed_tests,
            (report.failed_tests as f64 / report.total_tests as f64) * 100.0,
            report.skipped_tests,
            (report.skipped_tests as f64 / report.total_tests as f64) * 100.0,
            report.timeout_tests,
            (report.timeout_tests as f64 / report.total_tests as f64) * 100.0,
            report.summary.average_duration,
            generate_performance_html(&report.summary.performance_summary),
            generate_results_html(&report.results)
        )
    }

    /// 生成JSON报告
    pub fn generate_json_report(&self, test_suite: &str) -> String {
        let report = self.generate_report(test_suite);
        serde_json::to_string_pretty(&report).unwrap_or_else(|_| "{}".to_string())
    }
}

impl Default for TestReporter {
    fn default() -> Self {
        Self::new()
    }
}

/// 格式化时间
fn format_time(time: SystemTime) -> String {
    use std::time::UNIX_EPOCH;

    let duration = time.duration_since(UNIX_EPOCH).unwrap_or_default();
    let secs = duration.as_secs();
    let nanos = duration.subsec_nanos();

    format!("{}.{:09}", secs, nanos)
}

/// 生成性能HTML
fn generate_performance_html(performance: &Option<PerformanceSummary>) -> String {
    match performance {
        Some(perf) => format!(
            r#"
            <ul>
                <li>平均吞吐量: {:.2} 条/秒</li>
                <li>平均延迟: {:?}</li>
                <li>峰值内存使用: {} 字节</li>
                <li>平均CPU使用率: {:.1}%</li>
            </ul>
        "#,
            perf.average_throughput,
            perf.average_latency,
            perf.peak_memory_usage,
            perf.average_cpu_usage
        ),
        None => "<p>无性能数据</p>".to_string(),
    }
}

/// 生成结果HTML
fn generate_results_html(results: &[TestResult]) -> String {
    results
        .iter()
        .map(|result| {
            let status_class = match result.status {
                TestStatus::Passed => "status-passed",
                TestStatus::Failed => "status-failed",
                TestStatus::Skipped => "status-skipped",
                TestStatus::Timeout => "status-timeout",
            };

            let status_text = match result.status {
                TestStatus::Passed => "通过",
                TestStatus::Failed => "失败",
                TestStatus::Skipped => "跳过",
                TestStatus::Timeout => "超时",
            };

            let error_msg = result.error_message.as_deref().unwrap_or("");

            format!(
                r#"
            <tr>
                <td>{}</td>
                <td class="{}">{}</td>
                <td>{:?}</td>
                <td>{}</td>
            </tr>
        "#,
                result.name, status_class, status_text, result.duration, error_msg
            )
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_test_reporter() {
        let mut reporter = TestReporter::new();

        let result = TestResult {
            name: "test_example".to_string(),
            status: TestStatus::Passed,
            duration: Duration::from_millis(100),
            error_message: None,
            performance_metrics: Some(PerformanceMetrics {
                throughput: 1000.0,
                latency: Duration::from_millis(10),
                memory_usage: 1024,
                cpu_usage: 50.0,
            }),
        };

        reporter.add_result(result);

        let report = reporter.generate_report("test_suite");
        assert_eq!(report.total_tests, 1);
        assert_eq!(report.passed_tests, 1);
        assert_eq!(report.failed_tests, 0);
        assert!(report.summary.success_rate > 99.0);
    }
}
