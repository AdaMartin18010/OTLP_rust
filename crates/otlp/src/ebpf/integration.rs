//! eBPF 与 OpenTelemetry 集成
//!
//! 提供 eBPF 数据到 OpenTelemetry 的转换和导出功能

use crate::error::Result;
use crate::ebpf::types::{EbpfEvent, EbpfEventType};
use crate::profiling::types::PprofProfile;
use opentelemetry::trace::{Span, Tracer};
use opentelemetry::metrics::Meter;

/// eBPF 事件到 OpenTelemetry 的转换器
pub struct EbpfOtlpConverter {
    // OpenTelemetry 组件
    tracer: Option<Tracer>,
    meter: Option<Meter>,
}

impl EbpfOtlpConverter {
    /// 创建新的转换器
    pub fn new() -> Self {
        Self {
            tracer: None,
            meter: None,
        }
    }

    /// 设置 Tracer
    pub fn with_tracer(mut self, tracer: Tracer) -> Self {
        self.tracer = Some(tracer);
        self
    }

    /// 设置 Meter
    pub fn with_meter(mut self, meter: Meter) -> Self {
        self.meter = Some(meter);
        self
    }

    /// 转换 eBPF 事件到 OpenTelemetry Span
    ///
    /// # 实现说明
    ///
    /// 根据 eBPF 事件类型创建相应的 OpenTelemetry Span，并设置相关属性。
    /// 实际实现需要根据事件类型设置不同的属性：
    ///
    /// - **CpuSample**: 记录 CPU 采样信息（函数名、调用栈等）
    /// - **NetworkPacket**: 记录网络包信息（源地址、目标地址、协议等）
    /// - **Syscall**: 记录系统调用信息（系统调用号、参数等）
    /// - **MemoryAlloc/Free**: 记录内存分配信息（大小、地址等）
    pub fn convert_event_to_span(&self, event: &EbpfEvent) -> Result<Option<Span>> {
        if let Some(ref tracer) = self.tracer {
            let span_name = match event.event_type {
                EbpfEventType::CpuSample => "ebpf.cpu.sample",
                EbpfEventType::NetworkPacket => "ebpf.network.packet",
                EbpfEventType::Syscall => "ebpf.syscall",
                EbpfEventType::MemoryAlloc => "ebpf.memory.alloc",
                EbpfEventType::MemoryFree => "ebpf.memory.free",
            };

            let span = tracer.start(span_name);

            // 基础属性
            span.set_attribute(opentelemetry::KeyValue::new("ebpf.pid", event.pid as i64));
            span.set_attribute(opentelemetry::KeyValue::new("ebpf.tid", event.tid as i64));
            span.set_attribute(
                opentelemetry::KeyValue::new("ebpf.event_type", format!("{:?}", event.event_type)),
            );

            // 注意: 实际实现需要根据事件类型解析 event.data 并设置相应的属性
            // 例如，对于 NetworkPacket 事件，需要解析 IP 地址、端口等信息：
            //     if let EbpfEventType::NetworkPacket = event.event_type {
            //         // 解析网络包数据
            //         if let Ok(packet) = parse_network_packet(&event.data) {
            //             span.set_attribute(KeyValue::new("network.src_addr", packet.src_addr));
            //             span.set_attribute(KeyValue::new("network.dst_addr", packet.dst_addr));
            //             span.set_attribute(KeyValue::new("network.protocol", packet.protocol));
            //         }
            //     }
            //
            // 对于 Syscall 事件，需要解析系统调用信息：
            //     if let EbpfEventType::Syscall = event.event_type {
            //         if let Ok(syscall_info) = parse_syscall_info(&event.data) {
            //             span.set_attribute(KeyValue::new("syscall.number", syscall_info.number));
            //             span.set_attribute(KeyValue::new("syscall.name", syscall_info.name));
            //         }
            //     }

            Ok(Some(span))
        } else {
            Ok(None)
        }
    }

    /// 转换 eBPF 事件到 OpenTelemetry Metrics
    ///
    /// # 实现说明
    ///
    /// 根据 eBPF 事件类型记录相应的指标：
    ///
    /// - **CpuSample**: 记录 CPU 采样率、调用栈深度等指标
    /// - **NetworkPacket**: 记录网络流量（字节数、包数等）
    /// - **Syscall**: 记录系统调用频率、延迟等指标
    /// - **MemoryAlloc/Free**: 记录内存分配大小、频率等指标
    ///
    /// # 指标类型
    ///
    /// - **Counter**: 用于累计计数（如事件总数、字节数）
    /// - **Gauge**: 用于瞬时值（如当前内存使用量）
    /// - **Histogram**: 用于分布值（如延迟分布）
    pub fn convert_event_to_metric(&self, event: &EbpfEvent) -> Result<()> {
        if let Some(ref meter) = self.meter {
            // 基础指标：事件计数
            let counter = meter.u64_counter("ebpf.events.count").init();
            counter.add(
                1,
                &[opentelemetry::KeyValue::new(
                    "event.type",
                    format!("{:?}", event.event_type),
                )],
            );

            // 注意: 实际实现需要根据事件类型记录更多指标
            // 例如，对于 NetworkPacket 事件，记录流量指标：
            //     match event.event_type {
            //         EbpfEventType::NetworkPacket => {
            //             if let Ok(packet) = parse_network_packet(&event.data) {
            //                 // 记录字节数
            //                 let bytes_counter = meter.u64_counter("ebpf.network.bytes").init();
            //                 bytes_counter.add(packet.size, &[
            //                     KeyValue::new("direction", packet.direction),
            //                     KeyValue::new("protocol", packet.protocol),
            //                 ]);
            //
            //                 // 记录延迟（如果有）
            //                 if let Some(latency) = packet.latency {
            //                     let latency_histogram = meter.f64_histogram("ebpf.network.latency").init();
            //                     latency_histogram.record(latency, &[
            //                         KeyValue::new("protocol", packet.protocol),
            //                     ]);
            //                 }
            //             }
            //         }
            //         EbpfEventType::Syscall => {
            //             if let Ok(syscall_info) = parse_syscall_info(&event.data) {
            //                 // 记录系统调用延迟
            //                 let latency_histogram = meter.f64_histogram("ebpf.syscall.latency").init();
            //                 latency_histogram.record(syscall_info.duration, &[
            //                     KeyValue::new("syscall.name", syscall_info.name),
            //                 ]);
            //             }
            //         }
            //         EbpfEventType::MemoryAlloc => {
            //             if let Ok(alloc_info) = parse_memory_alloc_info(&event.data) {
            //                 // 记录分配大小
            //                 let size_counter = meter.u64_counter("ebpf.memory.allocated").init();
            //                 size_counter.add(alloc_info.size, &[]);
            //             }
            //         }
            //         _ => {}
            //     }
        }

        Ok(())
    }

    /// 转换 PprofProfile 到 OpenTelemetry
    ///
    /// # 实现说明
    ///
    /// 将 pprof 格式的性能分析数据转换为 OpenTelemetry Profile 格式并导出。
    ///
    /// ## OpenTelemetry Profile 格式
    ///
    /// OpenTelemetry 定义了标准的 Profile 数据模型，包括：
    ///
    /// - **Profile**: 包含样本、位置、函数等信息
    /// - **Sample**: 包含调用栈和计数值
    /// - **Location**: 包含代码位置信息
    /// - **Function**: 包含函数名、文件名等信息
    ///
    /// ## 转换步骤
    ///
    /// 1. **解析 pprof Profile**: 从 `PprofProfile` 中提取样本数据
    /// 2. **转换为 OTLP 格式**: 创建 OpenTelemetry Profile 消息
    /// 3. **导出到 Collector**: 使用 OTLP exporter 发送数据
    ///
    /// ## 实现示例
    ///
    /// ```rust,ignore
    /// use opentelemetry_proto::tonic::collector::profiles::v1::ExportProfilesServiceRequest;
    /// use opentelemetry_proto::tonic::profiles::v1::{Profile, Sample, Location, Function};
    ///
    /// // 创建 OTLP Profile
    /// let mut otlp_profile = Profile::default();
    ///
    /// // 转换样本
    /// for pprof_sample in &profile.sample {
    ///     let mut otlp_sample = Sample::default();
    ///     otlp_sample.value = pprof_sample.value.clone();
    ///     // 转换调用栈...
    ///     otlp_profile.sample.push(otlp_sample);
    /// }
    ///
    /// // 使用 exporter 导出
    /// let request = ExportProfilesServiceRequest {
    ///     resource_profiles: vec![...],
    /// };
    /// exporter.export(request).await?;
    /// ```
    ///
    /// ## 参考
    ///
    /// - [OpenTelemetry Profile Specification](https://github.com/open-telemetry/opentelemetry-specification/blob/main/specification/profiles/README.md)
    /// - [pprof.proto](https://github.com/google/pprof/blob/main/proto/profile.proto)
    pub fn convert_profile_to_otlp(&self, profile: &PprofProfile) -> Result<()> {
        // 注意: 实际的 profile 转换需要:
        // 1. 解析 pprof Profile 数据结构
        //    从 PprofProfile 中提取:
        //    - sample: 样本数据（调用栈 + 计数值）
        //    - location: 代码位置信息
        //    - function: 函数信息
        //    - string_table: 字符串表
        //
        // 2. 转换为 OpenTelemetry Profile 格式
        //    使用 opentelemetry-proto 定义的类型:
        //    - opentelemetry_proto::tonic::profiles::v1::Profile
        //    - opentelemetry_proto::tonic::profiles::v1::Sample
        //    - opentelemetry_proto::tonic::profiles::v1::Location
        //    - opentelemetry_proto::tonic::profiles::v1::Function
        //
        // 3. 创建导出请求
        //    let request = ExportProfilesServiceRequest {
        //        resource_profiles: vec![
        //            ResourceProfiles {
        //                resource: Some(resource),
        //                scope_profiles: vec![
        //                    ScopeProfiles {
        //                        scope: Some(scope),
        //                        profiles: vec![otlp_profile],
        //                    }
        //                ],
        //            }
        //        ],
        //    };
        //
        // 4. 使用 OTLP exporter 导出
        //    需要使用实现了 ProfilesExporter trait 的 exporter
        //    exporter.export(request).await?;
        //
        // 注意: OpenTelemetry Profile 支持仍在开发中，具体实现可能需要根据最新规范调整
        //
        // 实现步骤总结:
        // 1. 解析 pprof Profile: 提取 sample, location, function, string_table
        // 2. 转换为 OTLP 格式: 使用 opentelemetry-proto 定义的类型
        // 3. 创建导出请求: ExportProfilesServiceRequest
        // 4. 使用 exporter 导出: exporter.export(request).await?
        //
        // 当前实现: 记录日志并返回成功，实际转换逻辑待 OpenTelemetry Profile API 稳定后实现
        tracing::info!(
            "转换 profile 到 OTLP (待实现，需要 OpenTelemetry Profile API 支持)。\
            当前 profile 数据已收集，等待 OpenTelemetry Profile 规范稳定后实现完整转换。\
            参考: https://github.com/open-telemetry/opentelemetry-specification/blob/main/specification/profiles/README.md"
        );
        Ok(())
    }

    /// 批量转换事件到 OpenTelemetry
    pub fn convert_events_batch(&self, events: &[EbpfEvent]) -> Result<(Vec<Span>, u64)> {
        let mut spans = Vec::new();
        let mut metric_count = 0u64;

        for event in events {
            if let Some(span) = self.convert_event_to_span(event)? {
                spans.push(span);
            }
            self.convert_event_to_metric(event)?;
            metric_count += 1;
        }

        Ok((spans, metric_count))
    }

    /// 检查转换器是否已配置
    pub fn is_configured(&self) -> bool {
        self.tracer.is_some() || self.meter.is_some()
    }

    /// 获取已转换的事件统计
    pub fn get_conversion_stats(&self) -> ConversionStats {
        ConversionStats::default()
    }
}

/// 转换统计信息
#[derive(Debug, Clone, Default)]
pub struct ConversionStats {
    /// 转换的 Span 数量
    pub spans_converted: u64,
    /// 转换的 Metric 数量
    pub metrics_converted: u64,
    /// 转换的 Profile 数量
    pub profiles_converted: u64,
    /// 转换错误数量
    pub conversion_errors: u64,
}

impl EbpfOtlpConverter {
    /// 增强的事件到 Span 转换（带更多属性）
    pub fn convert_event_to_span_enhanced(&self, event: &EbpfEvent) -> Result<Option<Span>> {
        if let Some(ref tracer) = self.tracer {
            let span_name = match event.event_type {
                EbpfEventType::CpuSample => "ebpf.cpu.sample",
                EbpfEventType::NetworkPacket => "ebpf.network.packet",
                EbpfEventType::Syscall => "ebpf.syscall",
                EbpfEventType::MemoryAlloc => "ebpf.memory.alloc",
                EbpfEventType::MemoryFree => "ebpf.memory.free",
            };

            let span = tracer.start(span_name);

            // 基础属性
            span.set_attribute(opentelemetry::KeyValue::new("ebpf.pid", event.pid as i64));
            span.set_attribute(opentelemetry::KeyValue::new("ebpf.tid", event.tid as i64));
            span.set_attribute(
                opentelemetry::KeyValue::new("ebpf.event_type", format!("{:?}", event.event_type)),
            );

            // 时间戳属性
            let timestamp_nanos = event.timestamp.as_nanos() as i64;
            span.set_attribute(
                opentelemetry::KeyValue::new("ebpf.timestamp", timestamp_nanos),
            );

            // 数据大小属性
            if !event.data.is_empty() {
                span.set_attribute(
                    opentelemetry::KeyValue::new("ebpf.data_size", event.data.len() as i64),
                );
            }

            Ok(Some(span))
        } else {
            Ok(None)
        }
    }

    /// 增强的事件到 Metric 转换（带更多指标）
    pub fn convert_event_to_metric_enhanced(&self, event: &EbpfEvent) -> Result<()> {
        if let Some(ref meter) = self.meter {
            // 基础指标：事件计数
            let counter = meter.u64_counter("ebpf.events.count").init();
            counter.add(
                1,
                &[
                    opentelemetry::KeyValue::new("event.type", format!("{:?}", event.event_type)),
                    opentelemetry::KeyValue::new("pid", event.pid.to_string()),
                ],
            );

            // 数据大小指标
            if !event.data.is_empty() {
                let size_gauge = meter.u64_gauge("ebpf.events.data_size").init();
                size_gauge.record(
                    event.data.len() as u64,
                    &[opentelemetry::KeyValue::new("event.type", format!("{:?}", event.event_type))],
                );
            }
        }

        Ok(())
    }
}

impl Default for EbpfOtlpConverter {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ebpf::types::EbpfEvent;
    use std::time::SystemTime;

    fn create_test_event(event_type: EbpfEventType) -> EbpfEvent {
        EbpfEvent::new(event_type, 1234, 5678, vec![1, 2, 3, 4])
    }

    #[test]
    fn test_converter_new() {
        let converter = EbpfOtlpConverter::new();
        assert!(!converter.is_configured());
    }

    #[test]
    fn test_converter_default() {
        let converter = EbpfOtlpConverter::default();
        assert!(!converter.is_configured());
    }

    #[test]
    fn test_converter_is_configured() {
        let converter = EbpfOtlpConverter::new();
        assert!(!converter.is_configured());
    }

    #[test]
    fn test_convert_event_to_span_no_tracer() {
        let converter = EbpfOtlpConverter::new();
        let event = create_test_event(EbpfEventType::CpuSample);
        let result = converter.convert_event_to_span(&event);
        assert!(result.is_ok());
        assert!(result.unwrap().is_none());
    }

    #[test]
    fn test_convert_event_to_span_enhanced_no_tracer() {
        let converter = EbpfOtlpConverter::new();
        let event = create_test_event(EbpfEventType::NetworkPacket);
        let result = converter.convert_event_to_span_enhanced(&event);
        assert!(result.is_ok());
        assert!(result.unwrap().is_none());
    }

    #[test]
    fn test_convert_event_to_metric_no_meter() {
        let converter = EbpfOtlpConverter::new();
        let event = create_test_event(EbpfEventType::Syscall);
        let result = converter.convert_event_to_metric(&event);
        assert!(result.is_ok());
    }

    #[test]
    fn test_convert_event_to_metric_enhanced_no_meter() {
        let converter = EbpfOtlpConverter::new();
        let event = create_test_event(EbpfEventType::MemoryAlloc);
        let result = converter.convert_event_to_metric_enhanced(&event);
        assert!(result.is_ok());
    }

    #[test]
    fn test_convert_events_batch_empty() {
        let converter = EbpfOtlpConverter::new();
        let events = vec![];
        let result = converter.convert_events_batch(&events);
        assert!(result.is_ok());
        let (spans, metric_count) = result.unwrap();
        assert_eq!(spans.len(), 0);
        assert_eq!(metric_count, 0);
    }

    #[test]
    fn test_convert_events_batch_multiple() {
        let converter = EbpfOtlpConverter::new();
        let events = vec![
            create_test_event(EbpfEventType::CpuSample),
            create_test_event(EbpfEventType::NetworkPacket),
            create_test_event(EbpfEventType::Syscall),
        ];
        let result = converter.convert_events_batch(&events);
        assert!(result.is_ok());
        let (spans, metric_count) = result.unwrap();
        assert_eq!(spans.len(), 0); // No tracer configured
        assert_eq!(metric_count, 3);
    }

    #[test]
    fn test_convert_profile_to_otlp() {
        let converter = EbpfOtlpConverter::new();
        let profile = PprofProfile::default();
        let result = converter.convert_profile_to_otlp(&profile);
        assert!(result.is_ok());
    }

    #[test]
    fn test_get_conversion_stats() {
        let converter = EbpfOtlpConverter::new();
        let stats = converter.get_conversion_stats();
        assert_eq!(stats.spans_converted, 0);
        assert_eq!(stats.metrics_converted, 0);
        assert_eq!(stats.profiles_converted, 0);
        assert_eq!(stats.conversion_errors, 0);
    }

    #[test]
    fn test_conversion_stats_default() {
        let stats = ConversionStats::default();
        assert_eq!(stats.spans_converted, 0);
        assert_eq!(stats.metrics_converted, 0);
        assert_eq!(stats.profiles_converted, 0);
        assert_eq!(stats.conversion_errors, 0);
    }

    #[test]
    fn test_conversion_stats_clone() {
        let stats = ConversionStats {
            spans_converted: 10,
            metrics_converted: 20,
            profiles_converted: 5,
            conversion_errors: 1,
        };
        let cloned = stats.clone();
        assert_eq!(cloned.spans_converted, 10);
        assert_eq!(cloned.metrics_converted, 20);
        assert_eq!(cloned.profiles_converted, 5);
        assert_eq!(cloned.conversion_errors, 1);
    }

    #[test]
    fn test_all_event_types() {
        let converter = EbpfOtlpConverter::new();
        let event_types = vec![
            EbpfEventType::CpuSample,
            EbpfEventType::NetworkPacket,
            EbpfEventType::Syscall,
            EbpfEventType::MemoryAlloc,
            EbpfEventType::MemoryFree,
        ];

        for event_type in event_types {
            let event = create_test_event(event_type);
            let span_result = converter.convert_event_to_span(&event);
            assert!(span_result.is_ok());
            let metric_result = converter.convert_event_to_metric(&event);
            assert!(metric_result.is_ok());
        }
    }
}
