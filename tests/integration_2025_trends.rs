//! 2025年技术趋势对齐集成测试
//!
//! 测试所有2025年新增功能的集成使用

use otlp::{
    BytecodeCompiler, GraduationStrategy, LabelSelector, OpampHealthStatus, OttlParser,
    RollbackManager,
};
use std::collections::HashMap;
use std::time::Duration;

#[test]
fn test_ottl_bytecode_integration() {
    // 测试OTTL字节码解析器的完整流程
    let ottl_statement = r#"set(span.attributes["test_key"], "test_value")"#;
    let mut parser = OttlParser::new(ottl_statement.to_string());

    let statements = parser.parse().expect("解析失败");
    assert!(!statements.is_empty());

    let mut compiler = BytecodeCompiler::new();
    let program = compiler.compile(&statements[0]).expect("编译失败");

    // 验证字节码程序
    assert!(!program.instructions.is_empty());
    assert!(!program.string_table.is_empty() || program.constants.is_empty());
}

#[test]
fn test_opamp_graduation_integration() {
    // 测试OPAMP灰度策略的完整流程
    let selector = LabelSelector::new().with_label("env".to_string(), "prod".to_string());

    let strategy = GraduationStrategy::new(selector)
        .with_weight(0.1)
        .with_rollback_window(Duration::from_secs(300));

    let mut agent_labels = HashMap::new();
    agent_labels.insert("env".to_string(), "prod".to_string());

    assert!(strategy.should_apply(&agent_labels));

    let target = strategy.calculate_target_instances(100, 95);
    assert!(target >= strategy.min_healthy_instances);
}

#[test]
fn test_rollback_manager_integration() {
    // 测试回滚管理器的完整流程
    let mut manager = RollbackManager::new(Duration::from_secs(300));

    // 记录健康配置
    manager.record_snapshot("config_v1".to_string(), OpampHealthStatus::Healthy);

    // 记录不健康配置
    manager.record_snapshot("config_v2".to_string(), OpampHealthStatus::Unhealthy);

    // 检查回滚
    let rollback = manager.should_rollback(&OpampHealthStatus::Critical);
    assert!(rollback.is_some());

    // 执行回滚
    let previous = manager.rollback();
    assert!(previous.is_some());
}

#[test]
fn test_const_api_integration() {
    // 测试Const API的使用
    use otlp::config::{validate_batch_size, DEFAULT_BATCH_SIZE, MAX_BATCH_SIZE, MIN_BATCH_SIZE};

    // 验证const常量
    assert!(DEFAULT_BATCH_SIZE >= MIN_BATCH_SIZE);
    assert!(DEFAULT_BATCH_SIZE <= MAX_BATCH_SIZE);

    // 验证const函数
    assert!(validate_batch_size(DEFAULT_BATCH_SIZE));
    assert!(!validate_batch_size(MAX_BATCH_SIZE + 1));
    assert!(!validate_batch_size(MIN_BATCH_SIZE - 1));
}

#[test]
fn test_ottl_transform_with_bytecode() {
    // 测试OTTL Transform使用字节码优化
    use otlp::ottl::{OtlpTransform, TransformConfig};

    let mut config = TransformConfig::new().with_bytecode(true); // 启用字节码优化

    // 添加语句
    let ottl_statement = r#"set(span.attributes["test"], "value")"#;
    let mut parser = OttlParser::new(ottl_statement.to_string());
    if let Ok(statements) = parser.parse() {
        for stmt in statements {
            config = config.add_statement(stmt);
        }
    }

    // 编译字节码
    let mut config = config;
    assert!(config.compile_bytecode().is_ok());

    // 创建转换器
    let transform = OtlpTransform::new(config).expect("创建转换器失败");
    // 转换器已准备好使用字节码优化
}

#[test]
fn test_opamp_messages_with_graduation() {
    // 测试OPAMP消息集成灰度策略
    use otlp::opamp::messages::ServerToAgent;

    let selector = LabelSelector::new().with_label("region".to_string(), "us-east-1".to_string());

    let strategy = GraduationStrategy::new(selector).with_weight(0.2);

    let mut message = ServerToAgent {
        remote_config: None,
        packages_available: HashMap::new(),
        packages_install: HashMap::new(),
        error_response: None,
        connection_settings: None,
        other_settings: None,
        graduation_strategy: Some(strategy),
        rollback_window: Some(Duration::from_secs(300)),
    };

    // 验证消息包含灰度策略
    assert!(message.graduation_strategy.is_some());
    assert!(message.rollback_window.is_some());
}

#[test]
fn test_ebpf_profiling_config() {
    // 测试eBPF Profiling配置 (仅验证配置，不实际运行)
    #[cfg(target_os = "linux")]
    {
        use otlp::{EbpfProfiler, EbpfProfilerConfig};

        let config = EbpfProfilerConfig::new()
            .with_sample_rate(99)
            .with_duration(Duration::from_secs(60));

        // 验证配置
        assert_eq!(config.sample_rate, 99);
        assert_eq!(config.duration, Duration::from_secs(60));

        // 创建分析器 (不实际启动)
        let profiler = EbpfProfiler::new(config);
        assert!(profiler.is_ok());
    }

    #[cfg(not(target_os = "linux"))]
    {
        // 非Linux平台跳过
        println!("eBPF Profiling仅在Linux平台支持");
    }
}

#[test]
fn test_end_to_end_workflow() {
    // 端到端测试：OTTL + OPAMP + Const API
    use otlp::config::DEFAULT_BATCH_SIZE;

    // 1. 使用Const API获取默认配置
    let batch_size = DEFAULT_BATCH_SIZE;

    // 2. 使用OTTL处理数据
    let ottl_statement = format!(r#"set(span.attributes["batch_size"], {})"#, batch_size);
    let mut parser = OttlParser::new(ottl_statement);
    let statements = parser.parse().expect("解析失败");

    // 3. 编译到字节码
    let mut compiler = BytecodeCompiler::new();
    let program = compiler.compile(&statements[0]).expect("编译失败");
    assert!(!program.instructions.is_empty());

    // 4. 使用OPAMP灰度策略
    let selector =
        LabelSelector::new().with_label("batch_size".to_string(), batch_size.to_string());

    let strategy = GraduationStrategy::new(selector).with_weight(0.1);

    let mut labels = HashMap::new();
    labels.insert("batch_size".to_string(), batch_size.to_string());

    assert!(strategy.should_apply(&labels));
}
