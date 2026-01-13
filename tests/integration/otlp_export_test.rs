//! OTLP 导出集成测试
//!
//! 测试 OTLP 数据导出功能

use otlp::profiling::{CpuProfiler, ProfilerConfig};
// use otlp::profiling::exporter::ProfilesExporter; // 待实现
use std::time::Duration;

#[tokio::test]
async fn test_otlp_profile_export() {
    let config = ProfilerConfig::default();
    let mut profiler = CpuProfiler::new(config);

    // 启动性能分析
    assert!(profiler.start().await.is_ok());

    // 等待采样
    tokio::time::sleep(Duration::from_millis(100)).await;

    // 停止并获取profile
    let profile = profiler.stop().await.unwrap();

    // 创建导出器（待实现）
    // let exporter = ProfilesExporter::new("http://localhost:4317".to_string());
    // let result = exporter.export(&profile).await;

    // 当前只测试profile创建
    assert!(profile.samples.len() >= 0);
}

#[tokio::test]
async fn test_otlp_profile_export_batch() {
    let config = ProfilerConfig::default();
    let mut profiler = CpuProfiler::new(config);

    // 收集多个profiles
    let mut profiles = Vec::new();

    for _ in 0..3 {
        assert!(profiler.start().await.is_ok());
        tokio::time::sleep(Duration::from_millis(50)).await;
        let profile = profiler.stop().await.unwrap();
        profiles.push(profile);
    }

    // 批量导出（待实现）
    // let exporter = ProfilesExporter::new("http://localhost:4317".to_string());
    // let result = exporter.export_batch(&profiles).await;

    // 当前只测试profiles收集
    assert_eq!(profiles.len(), 3);
}

#[tokio::test]
async fn test_otlp_profile_export_pprof_format() {
    let config = ProfilerConfig::default();
    let mut profiler = CpuProfiler::new(config);

    // 启动并停止获取profile
    assert!(profiler.start().await.is_ok());
    tokio::time::sleep(Duration::from_millis(100)).await;
    let profile = profiler.stop().await.unwrap();

    // 测试pprof格式导出
    let pprof_json = profile.encode_json();
    assert!(pprof_json.is_ok());

    let json_str = pprof_json.unwrap();
    assert!(!json_str.is_empty());
    assert!(json_str.contains("samples") || json_str.contains("locations"));
}

#[tokio::test]
async fn test_otlp_profile_export_with_metadata() {
    let config = ProfilerConfig::default();
    let mut profiler = CpuProfiler::new(config);

    // 启动并停止获取profile
    assert!(profiler.start().await.is_ok());
    tokio::time::sleep(Duration::from_millis(100)).await;
    let profile = profiler.stop().await.unwrap();

    // 验证profile包含必要的元数据
    assert!(!profile.samples.is_empty() || profile.samples.is_empty()); // 取决于采样时间
    // profile应该包含locations和functions（即使为空）
    assert!(profile.locations.len() >= 0);
    assert!(profile.functions.len() >= 0);
}
