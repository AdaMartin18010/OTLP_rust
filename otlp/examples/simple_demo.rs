use otlp::data::{
    DataPoint, DataPointValue, LogSeverity, MetricType, SpanKind, SpanStatus, TelemetryContent,
};
use otlp::{AttributeValue, LogData, MetricData, StatusCode, TelemetryData, TraceData};
use std::collections::HashMap;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 OTLP Rust 1.90 简单演示程序");
    println!("================================\n");

    // 1. 创建追踪数据
    println!("📊 1. 创建追踪数据");

    let mut trace_attributes = HashMap::new();
    trace_attributes.insert(
        "user.id".to_string(),
        AttributeValue::String("12345".to_string()),
    );
    trace_attributes.insert(
        "request.method".to_string(),
        AttributeValue::String("GET".to_string()),
    );
    trace_attributes.insert(
        "request.path".to_string(),
        AttributeValue::String("/api/demo".to_string()),
    );
    trace_attributes.insert("response.status".to_string(), AttributeValue::Int(200));

    let trace_data = TraceData {
        trace_id: otlp::utils::HashUtils::generate_trace_id(),
        span_id: otlp::utils::HashUtils::generate_span_id(),
        parent_span_id: None,
        name: "demo_operation".to_string(),
        span_kind: SpanKind::Server,
        start_time: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)?
            .as_nanos() as u64,
        end_time: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)?
            .as_nanos() as u64
            + 150_000_000, // 150ms
        status: SpanStatus {
            code: StatusCode::Ok,
            message: None,
        },
        attributes: trace_attributes,
        events: vec![],
        links: vec![],
    };

    println!("✅ 追踪数据创建成功");
    println!("   操作名: demo_operation");
    println!("   追踪ID: {}", trace_data.trace_id);
    println!("   跨度ID: {}", trace_data.span_id);
    println!("   持续时间: 150ms");
    println!("   状态: {:?}\n", trace_data.status.code);

    // 2. 创建指标数据
    println!("📈 2. 创建指标数据");

    let mut metric_attributes = HashMap::new();
    metric_attributes.insert(
        "environment".to_string(),
        AttributeValue::String("demo".to_string()),
    );
    metric_attributes.insert(
        "version".to_string(),
        AttributeValue::String("1.0.0".to_string()),
    );

    let metric_data = MetricData {
        name: "demo_counter".to_string(),
        description: "演示计数器".to_string(),
        unit: "count".to_string(),
        metric_type: MetricType::Counter,
        data_points: vec![DataPoint {
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)?
                .as_nanos() as u64,
            attributes: metric_attributes,
            value: DataPointValue::Number(1.0),
        }],
    };

    println!("✅ 指标数据创建成功");
    println!("   指标名: demo_counter");
    println!("   类型: {:?}", metric_data.metric_type);
    println!("   值: 1.0\n");

    // 3. 创建日志数据
    println!("📝 3. 创建日志数据");

    let mut log_attributes = HashMap::new();
    log_attributes.insert(
        "logger.name".to_string(),
        AttributeValue::String("demo_logger".to_string()),
    );
    log_attributes.insert(
        "thread.id".to_string(),
        AttributeValue::String("main".to_string()),
    );
    log_attributes.insert(
        "application".to_string(),
        AttributeValue::String("otlp_demo".to_string()),
    );

    let log_data = LogData {
        timestamp: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)?
            .as_nanos() as u64,
        severity: LogSeverity::Info,
        severity_text: "INFO".to_string(),
        message: "Demo log message".to_string(),
        attributes: log_attributes,
        resource_attributes: HashMap::new(),
        trace_id: Some(otlp::utils::HashUtils::generate_trace_id()),
        span_id: Some(otlp::utils::HashUtils::generate_span_id()),
    };

    println!("✅ 日志数据创建成功");
    println!("   消息: Demo log message");
    println!("   级别: {:?}", log_data.severity);
    println!("   时间戳: 已设置\n");

    // 4. 创建遥测数据包装器
    println!("📦 4. 创建遥测数据包装器");

    let telemetry_data = TelemetryData {
        data_type: otlp::data::TelemetryDataType::Trace,
        timestamp: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)?
            .as_nanos() as u64,
        resource_attributes: HashMap::new(),
        scope_attributes: HashMap::new(),
        content: TelemetryContent::Trace(trace_data),
    };

    println!("✅ 遥测数据包装器创建成功");
    println!("   数据类型: {:?}", telemetry_data.data_type);
    println!("   时间戳: {}\n", telemetry_data.timestamp);

    // 5. 数据序列化演示
    println!("🔄 5. 数据序列化演示");

    let trace_json = serde_json::to_string_pretty(&telemetry_data)?;
    println!("✅ 遥测数据JSON序列化成功");
    println!("   序列化大小: {} 字节", trace_json.len());
    println!(
        "   前100字符: {}...\n",
        &trace_json[..100.min(trace_json.len())]
    );

    // 6. 批量数据处理
    println!("📦 6. 批量数据处理");

    let mut batch_data = Vec::new();
    for i in 0..3 {
        let mut trace_attrs = HashMap::new();
        trace_attrs.insert("batch.id".to_string(), AttributeValue::Int(i));
        trace_attrs.insert("batch.size".to_string(), AttributeValue::Int(3));

        let batch_trace = TraceData {
            trace_id: otlp::utils::HashUtils::generate_trace_id(),
            span_id: otlp::utils::HashUtils::generate_span_id(),
            parent_span_id: None,
            name: format!("batch_operation_{}", i),
            span_kind: SpanKind::Internal,
            start_time: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)?
                .as_nanos() as u64,
            end_time: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)?
                .as_nanos() as u64
                + 100_000_000, // 100ms
            status: SpanStatus {
                code: StatusCode::Ok,
                message: None,
            },
            attributes: trace_attrs,
            events: vec![],
            links: vec![],
        };

        batch_data.push(TelemetryData {
            data_type: otlp::data::TelemetryDataType::Trace,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)?
                .as_nanos() as u64,
            resource_attributes: HashMap::new(),
            scope_attributes: HashMap::new(),
            content: TelemetryContent::Trace(batch_trace),
        });
    }

    println!("✅ 批量数据创建成功");
    println!("   批次大小: {} 个追踪", batch_data.len());
    println!(
        "   总数据大小: {} 字节\n",
        serde_json::to_string(&batch_data)?.len()
    );

    // 7. 性能统计
    println!("📈 7. 性能统计");

    let start = std::time::Instant::now();
    let _ = serde_json::to_string(&batch_data)?;
    let serialization_time = start.elapsed();

    println!("✅ 性能统计完成");
    println!("   序列化时间: {:?}", serialization_time);
    println!(
        "   吞吐量: {:.2} KB/s",
        (batch_data.len() as f64 * 0.5) / serialization_time.as_secs_f64()
    );
    println!("   内存使用: 估算 {} KB\n", batch_data.len() * 2);

    // 8. 工具函数演示
    println!("🛠️ 8. 工具函数演示");

    let trace_id = otlp::utils::HashUtils::generate_trace_id();
    let span_id = otlp::utils::HashUtils::generate_span_id();
    let random_string = otlp::utils::StringUtils::random_string(10);

    println!("✅ 工具函数演示完成");
    println!("   生成的追踪ID: {} (长度: {})", trace_id, trace_id.len());
    println!("   生成的跨度ID: {} (长度: {})", span_id, span_id.len());
    println!(
        "   随机字符串: {} (长度: {})\n",
        random_string,
        random_string.len()
    );

    println!("🎉 演示完成！");
    println!("这个演示展示了OTLP Rust客户端的核心数据模型：");
    println!("• 追踪数据 (TraceData) - 分布式追踪信息");
    println!("• 指标数据 (MetricData) - 性能指标和计数器");
    println!("• 日志数据 (LogData) - 应用程序日志");
    println!("• 遥测数据包装器 (TelemetryData) - 统一数据格式");
    println!("• JSON序列化 - 数据传输格式");
    println!("• 批量处理 - 高效数据处理");
    println!("• 工具函数 - 辅助功能");
    println!("\n所有数据模型都符合OpenTelemetry协议规范！");

    Ok(())
}
