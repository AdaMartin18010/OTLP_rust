//! eBPF 与 OpenTelemetry 集成示例
//!
//! 本示例展示如何使用 eBPF 数据转换器将 eBPF 事件转换为 OpenTelemetry 格式

use otlp::ebpf::integration::EbpfOtlpConverter;
use otlp::ebpf::types::{EbpfEvent, EbpfEventType};
use otlp::profiling::types::PprofProfile;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建转换器
    let converter = EbpfOtlpConverter::new();

    // 创建示例 eBPF 事件
    let cpu_event = EbpfEvent::new(
        EbpfEventType::CpuSample,
        1234,
        5678,
        vec![1, 2, 3, 4],
    );

    let network_event = EbpfEvent::new(
        EbpfEventType::NetworkPacket,
        1234,
        5678,
        vec![5, 6, 7, 8],
    );

    // 转换单个事件到 Span
    println!("转换 CPU 事件到 Span...");
    match converter.convert_event_to_span(&cpu_event)? {
        Some(span) => {
            println!("✅ Span 创建成功: {}", span.name());
        }
        None => {
            println!("⚠️  未配置 Tracer，跳过 Span 创建");
        }
    }

    // 转换单个事件到 Metric
    println!("转换网络事件到 Metric...");
    converter.convert_event_to_metric(&network_event)?;
    println!("✅ Metric 记录成功");

    // 使用增强的转换方法
    println!("使用增强方法转换事件...");
    match converter.convert_event_to_span_enhanced(&cpu_event)? {
        Some(span) => {
            println!("✅ 增强 Span 创建成功: {}", span.name());
        }
        None => {
            println!("⚠️  未配置 Tracer，跳过 Span 创建");
        }
    }

    converter.convert_event_to_metric_enhanced(&network_event)?;
    println!("✅ 增强 Metric 记录成功");

    // 批量转换事件
    println!("批量转换事件...");
    let events = vec![cpu_event, network_event];
    let (spans, metric_count) = converter.convert_events_batch(&events)?;
    println!("✅ 批量转换完成: {} 个 Span, {} 个 Metric", spans.len(), metric_count);

    // 转换 Profile 到 OTLP
    println!("转换 Profile 到 OTLP...");
    let profile = PprofProfile::default();
    converter.convert_profile_to_otlp(&profile)?;
    println!("✅ Profile 转换完成");

    // 获取转换统计信息
    let stats = converter.get_conversion_stats();
    println!("转换统计:");
    println!("  - Span 数量: {}", stats.spans_converted);
    println!("  - Metric 数量: {}", stats.metrics_converted);
    println!("  - Profile 数量: {}", stats.profiles_converted);
    println!("  - 错误数量: {}", stats.conversion_errors);

    // 检查转换器配置
    if converter.is_configured() {
        println!("✅ 转换器已配置");
    } else {
        println!("⚠️  转换器未配置（需要设置 Tracer 或 Meter）");
    }

    Ok(())
}
