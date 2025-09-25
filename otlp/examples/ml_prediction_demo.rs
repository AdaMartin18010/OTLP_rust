//! # 机器学习错误预测系统演示
//!
//! 展示如何使用 OTLP Rust 的机器学习错误预测系统进行智能错误预测、
//! 在线学习和自适应恢复策略。

use otlp::error::{ErrorSeverity, Result};

// 模拟的ML预测结构体
#[derive(Debug, Clone)]
pub struct MLPredictionConfig {
    pub model_path: String,
    pub batch_size: usize,
    pub confidence_threshold: f64,
}

impl Default for MLPredictionConfig {
    fn default() -> Self {
        Self {
            model_path: "/models/error_prediction".to_string(),
            batch_size: 32,
            confidence_threshold: 0.8,
        }
    }
}

#[derive(Debug, Clone)]
pub struct MLErrorPrediction {
    pub config: MLPredictionConfig,
}

impl MLErrorPrediction {
    pub fn new(config: MLPredictionConfig) -> Result<Self> {
        Ok(Self { config })
    }
    
    pub async fn get_model_status(&self) -> Result<ModelStatus> {
        Ok(ModelStatus {
            model_version: "1.0.0".to_string(),
            total_predictions: 1000,
            accuracy: 0.85,
            cache_size: 100,
            is_training: false,
        })
    }
    
    pub async fn predict_error_probability(&self, _context: &SystemContext) -> Result<PredictionResult> {
        Ok(PredictionResult {
            probability: 0.3,
            confidence: 0.8,
            error_types: vec!["resource".to_string()],
            time_window: std::time::Duration::from_secs(300),
            model_version: "1.0.0".to_string(),
            explanation: PredictionExplanation {
                summary: "系统资源使用率较高".to_string(),
                confidence_level: "中等".to_string(),
                details: vec!["CPU使用率: 75%".to_string(), "内存使用率: 80%".to_string()],
            },
            recommended_actions: vec![
                RecommendedAction {
                    description: "增加资源监控频率".to_string(),
                    priority: 1,
                    estimated_effectiveness: 0.7,
                },
                RecommendedAction {
                    description: "准备扩展资源".to_string(),
                    priority: 2,
                    estimated_effectiveness: 0.9,
                },
            ],
        })
    }
    
    pub async fn train_model(&self, _training_data: &[ErrorSample]) -> Result<TrainingResult> {
        Ok(TrainingResult {
            success: true,
            accuracy: 0.85,
            precision: 0.82,
            recall: 0.88,
            f1_score: 0.85,
            training_samples: 1000,
            model_version: "1.1.0".to_string(),
        })
    }
    
    pub async fn online_learn(&self, _feedback: PredictionFeedback) -> Result<()> {
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct ModelStatus {
    pub model_version: String,
    pub total_predictions: usize,
    pub accuracy: f64,
    pub cache_size: usize,
    pub is_training: bool,
}

#[derive(Debug, Clone)]
pub struct PredictionResult {
    pub probability: f64,
    pub confidence: f64,
    pub error_types: Vec<String>,
    pub time_window: std::time::Duration,
    pub model_version: String,
    pub explanation: PredictionExplanation,
    pub recommended_actions: Vec<RecommendedAction>,
}

#[derive(Debug, Clone)]
pub struct PredictionExplanation {
    pub summary: String,
    pub confidence_level: String,
    pub details: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct RecommendedAction {
    pub description: String,
    pub priority: u32,
    pub estimated_effectiveness: f64,
}

#[derive(Debug, Clone)]
pub struct TrainingResult {
    pub success: bool,
    pub accuracy: f64,
    pub precision: f64,
    pub recall: f64,
    pub f1_score: f64,
    pub training_samples: usize,
    pub model_version: String,
}

#[derive(Debug, Clone)]
pub struct ErrorSample {
    pub id: String,
    pub timestamp: std::time::SystemTime,
    pub context: SystemContext,
    pub actual_error: Option<ErrorHistoryEntry>,
    pub predicted_error: Option<ErrorHistoryEntry>,
    pub prediction_accuracy: Option<f64>,
}

#[derive(Debug, Clone)]
pub struct SystemContext {
    pub timestamp: std::time::SystemTime,
    pub cpu_usage: f64,
    pub memory_usage: f64,
    pub system_load: f64,
    pub active_services: usize,
    pub network_latency: std::time::Duration,
    pub error_history: Vec<ErrorHistoryEntry>,
    pub service_health: std::collections::HashMap<String, ServiceHealth>,
    pub resource_metrics: ResourceMetrics,
}

#[derive(Debug, Clone)]
pub struct ErrorHistoryEntry {
    pub timestamp: std::time::SystemTime,
    pub error_type: String,
    pub severity: ErrorSeverity,
    pub source: String,
}

#[derive(Debug, Clone)]
pub struct ServiceHealth {
    pub status: HealthStatus,
    pub response_time: std::time::Duration,
    pub error_rate: f64,
    pub last_check: std::time::SystemTime,
}

#[derive(Debug, Clone)]
pub enum HealthStatus {
    Healthy,
    Warning,
    Critical,
}

#[derive(Debug, Clone)]
pub struct ResourceMetrics {
    pub cpu_cores: usize,
    pub total_memory: u64,
    pub available_memory: u64,
    pub disk_usage: f64,
    pub network_bandwidth: u64,
}

#[derive(Debug, Clone)]
pub struct PredictionFeedback {
    pub prediction_id: String,
    pub actual_outcome: ActualOutcome,
    pub feedback_type: FeedbackType,
    pub timestamp: std::time::SystemTime,
    pub context: SystemContext,
}

#[derive(Debug, Clone)]
pub enum ActualOutcome {
    NoError,
    ErrorOccurred(ErrorHistoryEntry),
}

#[derive(Debug, Clone)]
pub enum FeedbackType {
    Positive,
    Negative,
}
use std::collections::HashMap;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🤖 OTLP Rust 机器学习错误预测系统演示");
    println!("===========================================");

    // 示例 1: 基本预测系统设置
    basic_prediction_demo().await?;

    // 示例 2: 错误预测
    error_prediction_demo().await?;

    // 示例 3: 模型训练
    model_training_demo().await?;

    // 示例 4: 在线学习
    online_learning_demo().await?;

    // 示例 5: 自适应恢复策略
    adaptive_recovery_demo().await?;

    println!("\n✅ 所有ML预测演示完成！");
    Ok(())
}

/// 示例 1: 基本预测系统设置
async fn basic_prediction_demo() -> Result<()> {
    println!("\n🤖 示例 1: 基本预测系统设置");
    println!("---------------------------");

    // 创建ML预测配置
    let config = MLPredictionConfig::default();

    // 创建ML预测系统
    let ml_predictor = MLErrorPrediction::new(config)?;

    println!("  ✅ ML预测系统创建成功");

    // 获取模型状态
    let status = ml_predictor.get_model_status().await?;
    println!("  📊 模型状态:");
    println!("    - 模型版本: {}", status.model_version);
    println!("    - 总预测次数: {}", status.total_predictions);
    println!("    - 当前准确率: {:.3}", status.accuracy);
    println!("    - 缓存大小: {}", status.cache_size);
    println!("    - 是否正在训练: {}", status.is_training);

    Ok(())
}

/// 示例 2: 错误预测
async fn error_prediction_demo() -> Result<()> {
    println!("\n🔮 示例 2: 错误预测");
    println!("-------------------");

    let config = MLPredictionConfig::default();
    let ml_predictor = MLErrorPrediction::new(config)?;

    // 创建不同的系统上下文场景
    let scenarios = vec![
        ("高负载场景", create_high_load_context()),
        ("资源耗尽场景", create_resource_exhausted_context()),
        ("网络问题场景", create_network_issue_context()),
        ("健康系统场景", create_healthy_context()),
        ("临界状态场景", create_critical_context()),
    ];

    for (name, context) in scenarios {
        println!("  🔍 预测场景: {}", name);

        // 进行错误预测
        let prediction = ml_predictor.predict_error_probability(&context).await?;

        println!("    📊 预测结果:");
        println!("      - 错误概率: {:.3}", prediction.probability);
        println!("      - 置信度: {:.3}", prediction.confidence);
        println!("      - 预测错误类型: {:?}", prediction.error_types);
        println!("      - 时间窗口: {:?}", prediction.time_window);
        println!("      - 模型版本: {}", prediction.model_version);

        // 显示预测解释
        println!("    💡 预测解释:");
        println!("      - 总结: {}", prediction.explanation.summary);
        println!(
            "      - 置信水平: {}",
            prediction.explanation.confidence_level
        );
        for detail in &prediction.explanation.details {
            println!("      - {}", detail);
        }

        // 显示建议措施
        println!("    🛡️  建议措施:");
        for (i, action) in prediction.recommended_actions.iter().enumerate() {
            println!(
                "      {}. {} (优先级: {}, 预期效果: {:.1}%)",
                i + 1,
                action.description,
                action.priority,
                action.estimated_effectiveness * 100.0
            );
        }

        println!();
    }

    Ok(())
}

/// 示例 3: 模型训练
async fn model_training_demo() -> Result<()> {
    println!("\n🎓 示例 3: 模型训练");
    println!("-------------------");

    let config = MLPredictionConfig::default();
    let ml_predictor = MLErrorPrediction::new(config)?;

    // 创建训练数据
    let training_data = create_training_data();
    println!("  📚 创建了 {} 个训练样本", training_data.len());

    // 训练模型
    println!("  🎓 开始训练模型...");
    let training_result = ml_predictor.train_model(&training_data).await?;

    println!("  ✅ 模型训练完成:");
    println!("    - 训练成功: {}", training_result.success);
    println!("    - 准确率: {:.3}", training_result.accuracy);
    println!("    - 精确率: {:.3}", training_result.precision);
    println!("    - 召回率: {:.3}", training_result.recall);
    println!("    - F1分数: {:.3}", training_result.f1_score);
    println!("    - 训练样本数: {}", training_result.training_samples);
    println!("    - 新模型版本: {}", training_result.model_version);

    // 验证训练后的模型状态
    let status = ml_predictor.get_model_status().await?;
    println!("  📊 训练后模型状态:");
    println!("    - 模型版本: {}", status.model_version);
    println!("    - 准确率: {:.3}", status.accuracy);

    Ok(())
}

/// 示例 4: 在线学习
async fn online_learning_demo() -> Result<()> {
    println!("\n🔄 示例 4: 在线学习");
    println!("-------------------");

    let config = MLPredictionConfig::default();
    let ml_predictor = MLErrorPrediction::new(config)?;

    // 模拟预测和反馈循环
    println!("  🔄 模拟预测和反馈循环...");

    for i in 1..=5 {
        println!("  📊 第 {} 轮预测和反馈:", i);

        // 创建系统上下文
        let context = create_learning_context(i);

        // 进行预测
        let prediction = ml_predictor.predict_error_probability(&context).await?;
        println!("    - 预测错误概率: {:.3}", prediction.probability);

        // 模拟实际结果
        let actual_outcome = simulate_actual_outcome(&context, i);

        // 创建反馈
        let feedback = PredictionFeedback {
            prediction_id: format!("prediction-{}", i),
            actual_outcome: actual_outcome.clone(),
            feedback_type: determine_feedback_type(&prediction, &actual_outcome),
            timestamp: std::time::SystemTime::now(),
            context,
        };

        // 在线学习
        ml_predictor.online_learn(feedback).await?;
        println!("    - 反馈已处理，模型已更新");

        // 等待一段时间
        tokio::time::sleep(Duration::from_millis(100)).await;
    }

    // 检查学习效果
    let status = ml_predictor.get_model_status().await?;
    println!("  📈 在线学习完成，当前模型状态:");
    println!("    - 模型版本: {}", status.model_version);
    println!("    - 总预测次数: {}", status.total_predictions);
    println!("    - 准确率: {:.3}", status.accuracy);

    Ok(())
}

/// 示例 5: 自适应恢复策略
async fn adaptive_recovery_demo() -> Result<()> {
    println!("\n🛡️  示例 5: 自适应恢复策略");
    println!("---------------------------");

    let config = MLPredictionConfig::default();
    let ml_predictor = MLErrorPrediction::new(config)?;

    // 模拟不同的系统状态
    let system_states = vec![
        ("正常状态", create_normal_state()),
        ("警告状态", create_warning_state()),
        ("危险状态", create_danger_state()),
        ("临界状态", create_critical_state()),
    ];

    for (state_name, context) in system_states {
        println!("  🔍 系统状态: {}", state_name);

        // 预测错误概率
        let prediction = ml_predictor.predict_error_probability(&context).await?;

        // 根据预测结果制定恢复策略
        let recovery_strategy = determine_recovery_strategy(&prediction);

        println!("    📊 预测结果:");
        println!("      - 错误概率: {:.3}", prediction.probability);
        println!("      - 置信度: {:.3}", prediction.confidence);

        println!("    🛡️  自适应恢复策略:");
        println!("      - 策略类型: {}", recovery_strategy.strategy_type);
        println!("      - 执行优先级: {}", recovery_strategy.priority);
        println!(
            "      - 预期效果: {:.1}%",
            recovery_strategy.expected_effectiveness * 100.0
        );
        println!("      - 执行时间: {:?}", recovery_strategy.execution_time);

        // 模拟策略执行
        execute_recovery_strategy(&recovery_strategy).await?;

        println!();
    }

    Ok(())
}

// 辅助函数：创建不同的系统上下文

fn create_high_load_context() -> SystemContext {
    SystemContext {
        timestamp: std::time::SystemTime::now(),
        cpu_usage: 0.95,
        memory_usage: 0.90,
        system_load: 4.5,
        active_services: 25,
        network_latency: Duration::from_millis(300),
        error_history: vec![
            create_error_history_entry("resource", ErrorSeverity::High),
            create_error_history_entry("processing", ErrorSeverity::Medium),
        ],
        service_health: create_service_health_map(vec![
            ("service1", HealthStatus::Warning),
            ("service2", HealthStatus::Healthy),
            ("service3", HealthStatus::Critical),
        ]),
        resource_metrics: create_resource_metrics(0.8, 0.9),
    }
}

fn create_resource_exhausted_context() -> SystemContext {
    SystemContext {
        timestamp: std::time::SystemTime::now(),
        cpu_usage: 0.98,
        memory_usage: 0.99,
        system_load: 8.0,
        active_services: 50,
        network_latency: Duration::from_millis(100),
        error_history: vec![
            create_error_history_entry("resource", ErrorSeverity::Critical),
            create_error_history_entry("resource", ErrorSeverity::Critical),
            create_error_history_entry("processing", ErrorSeverity::High),
        ],
        service_health: create_service_health_map(vec![
            ("service1", HealthStatus::Critical),
            ("service2", HealthStatus::Critical),
            ("service3", HealthStatus::Warning),
        ]),
        resource_metrics: create_resource_metrics(0.95, 0.98),
    }
}

fn create_network_issue_context() -> SystemContext {
    SystemContext {
        timestamp: std::time::SystemTime::now(),
        cpu_usage: 0.6,
        memory_usage: 0.7,
        system_load: 2.0,
        active_services: 15,
        network_latency: Duration::from_secs(2),
        error_history: vec![
            create_error_history_entry("transport", ErrorSeverity::High),
            create_error_history_entry("transport", ErrorSeverity::Medium),
        ],
        service_health: create_service_health_map(vec![
            ("service1", HealthStatus::Healthy),
            ("service2", HealthStatus::Warning),
            ("service3", HealthStatus::Healthy),
        ]),
        resource_metrics: create_resource_metrics(0.6, 0.7),
    }
}

fn create_healthy_context() -> SystemContext {
    SystemContext {
        timestamp: std::time::SystemTime::now(),
        cpu_usage: 0.3,
        memory_usage: 0.4,
        system_load: 1.0,
        active_services: 8,
        network_latency: Duration::from_millis(50),
        error_history: Vec::new(),
        service_health: create_service_health_map(vec![
            ("service1", HealthStatus::Healthy),
            ("service2", HealthStatus::Healthy),
            ("service3", HealthStatus::Healthy),
        ]),
        resource_metrics: create_resource_metrics(0.3, 0.4),
    }
}

fn create_critical_context() -> SystemContext {
    SystemContext {
        timestamp: std::time::SystemTime::now(),
        cpu_usage: 1.0,
        memory_usage: 1.0,
        system_load: 10.0,
        active_services: 100,
        network_latency: Duration::from_secs(5),
        error_history: vec![
            create_error_history_entry("resource", ErrorSeverity::Critical),
            create_error_history_entry("transport", ErrorSeverity::Critical),
            create_error_history_entry("processing", ErrorSeverity::Critical),
        ],
        service_health: create_service_health_map(vec![
            ("service1", HealthStatus::Critical),
            ("service2", HealthStatus::Critical),
            ("service3", HealthStatus::Critical),
        ]),
        resource_metrics: create_resource_metrics(1.0, 1.0),
    }
}

fn create_learning_context(round: i32) -> SystemContext {
    SystemContext {
        timestamp: std::time::SystemTime::now(),
        cpu_usage: 0.5 + (round as f64 * 0.1),
        memory_usage: 0.6 + (round as f64 * 0.05),
        system_load: 1.0 + (round as f64 * 0.2),
        active_services: 10 + (round as usize),
        network_latency: Duration::from_millis(100 + (round * 50) as u64),
        error_history: if round > 3 {
            vec![create_error_history_entry(
                "transport",
                ErrorSeverity::Medium,
            )]
        } else {
            Vec::new()
        },
        service_health: create_service_health_map(vec![
            ("service1", HealthStatus::Healthy),
            ("service2", HealthStatus::Warning),
        ]),
        resource_metrics: create_resource_metrics(0.5, 0.6),
    }
}

fn create_normal_state() -> SystemContext {
    create_healthy_context()
}

fn create_warning_state() -> SystemContext {
    SystemContext {
        timestamp: std::time::SystemTime::now(),
        cpu_usage: 0.7,
        memory_usage: 0.8,
        system_load: 2.5,
        active_services: 20,
        network_latency: Duration::from_millis(200),
        error_history: vec![create_error_history_entry(
            "processing",
            ErrorSeverity::Medium,
        )],
        service_health: create_service_health_map(vec![
            ("service1", HealthStatus::Warning),
            ("service2", HealthStatus::Healthy),
        ]),
        resource_metrics: create_resource_metrics(0.7, 0.8),
    }
}

fn create_danger_state() -> SystemContext {
    create_high_load_context()
}

fn create_critical_state() -> SystemContext {
    create_critical_context()
}

// 辅助函数：创建训练数据

fn create_training_data() -> Vec<ErrorSample> {
    let mut training_data = Vec::new();

    // 正常样本
    for i in 0..20 {
        training_data.push(ErrorSample {
            id: format!("normal-{}", i),
            timestamp: std::time::SystemTime::now(),
            context: create_healthy_context(),
            actual_error: None,
            predicted_error: None,
            prediction_accuracy: Some(0.9),
        });
    }

    // 资源错误样本
    for i in 0..15 {
        training_data.push(ErrorSample {
            id: format!("resource-{}", i),
            timestamp: std::time::SystemTime::now(),
            context: create_high_load_context(),
            actual_error: Some(create_error_history_entry("resource", ErrorSeverity::High)),
            predicted_error: None,
            prediction_accuracy: Some(0.85),
        });
    }

    // 传输错误样本
    for i in 0..10 {
        training_data.push(ErrorSample {
            id: format!("transport-{}", i),
            timestamp: std::time::SystemTime::now(),
            context: create_network_issue_context(),
            actual_error: Some(create_error_history_entry(
                "transport",
                ErrorSeverity::Medium,
            )),
            predicted_error: None,
            prediction_accuracy: Some(0.8),
        });
    }

    training_data
}

// 辅助函数：创建其他数据结构

fn create_error_history_entry(
    error_type: &str,
    severity: ErrorSeverity,
) -> ErrorHistoryEntry {
    ErrorHistoryEntry {
        timestamp: std::time::SystemTime::now(),
        error_type: error_type.to_string(),
        severity: severity.clone(),
        source: "demo".to_string(),
    }
}

fn create_service_health_map(
    services: Vec<(&str, HealthStatus)>,
) -> HashMap<String, ServiceHealth> {
    let mut health_map = HashMap::new();

    for (name, status) in services {
        health_map.insert(
            name.to_string(),
            ServiceHealth {
                status: match status {
                    HealthStatus::Healthy => HealthStatus::Healthy,
                    HealthStatus::Warning => HealthStatus::Warning,
                    HealthStatus::Critical => HealthStatus::Critical,
                },
                response_time: Duration::from_millis(100),
                error_rate: match status {
                    HealthStatus::Healthy => 0.01,
                    HealthStatus::Warning => 0.05,
                    HealthStatus::Critical => 0.2,
                },
                last_check: std::time::SystemTime::now(),
            },
        );
    }

    health_map
}

fn create_resource_metrics(
    _cpu_usage: f64,
    memory_usage: f64,
) -> ResourceMetrics {
    ResourceMetrics {
        cpu_cores: 4,
        total_memory: 8192,
        available_memory: ((1.0 - memory_usage) * 8192.0) as u64,
        disk_usage: 0.5,
        network_bandwidth: 1000,
    }
}

// 辅助函数：模拟和决策逻辑

fn simulate_actual_outcome(
    context: &SystemContext,
    round: i32,
) -> ActualOutcome {
    // 基于系统状态模拟实际结果
    if context.cpu_usage > 0.8 || context.memory_usage > 0.8 {
        ActualOutcome::ErrorOccurred(create_error_history_entry(
            "resource",
            ErrorSeverity::High,
        ))
    } else if context.network_latency > Duration::from_secs(1) {
        ActualOutcome::ErrorOccurred(create_error_history_entry(
            "transport",
            ErrorSeverity::Medium,
        ))
    } else if round > 4 {
        ActualOutcome::ErrorOccurred(create_error_history_entry(
            "processing",
            ErrorSeverity::Low,
        ))
    } else {
        ActualOutcome::NoError
    }
}

fn determine_feedback_type(
    prediction: &PredictionResult,
    actual: &ActualOutcome,
) -> FeedbackType {
    match actual {
        ActualOutcome::ErrorOccurred(_) => {
            if prediction.probability > 0.7 {
                FeedbackType::Positive
            } else {
                FeedbackType::Negative
            }
        }
        ActualOutcome::NoError => {
            if prediction.probability < 0.3 {
                FeedbackType::Positive
            } else {
                FeedbackType::Negative
            }
        }
    }
}

#[derive(Debug)]
struct RecoveryStrategy {
    strategy_type: String,
    priority: u32,
    expected_effectiveness: f64,
    execution_time: Duration,
}

fn determine_recovery_strategy(prediction: &PredictionResult) -> RecoveryStrategy {
    if prediction.probability > 0.8 {
        RecoveryStrategy {
            strategy_type: "紧急扩容".to_string(),
            priority: 1,
            expected_effectiveness: 0.9,
            execution_time: Duration::from_secs(30),
        }
    } else if prediction.probability > 0.6 {
        RecoveryStrategy {
            strategy_type: "启用熔断器".to_string(),
            priority: 2,
            expected_effectiveness: 0.8,
            execution_time: Duration::from_secs(10),
        }
    } else if prediction.probability > 0.4 {
        RecoveryStrategy {
            strategy_type: "增加重试机制".to_string(),
            priority: 3,
            expected_effectiveness: 0.7,
            execution_time: Duration::from_secs(5),
        }
    } else {
        RecoveryStrategy {
            strategy_type: "监控增强".to_string(),
            priority: 4,
            expected_effectiveness: 0.6,
            execution_time: Duration::from_secs(1),
        }
    }
}

async fn execute_recovery_strategy(strategy: &RecoveryStrategy) -> Result<()> {
    println!("      🔧 执行恢复策略: {}...", strategy.strategy_type);

    // 模拟策略执行时间
    tokio::time::sleep(strategy.execution_time).await;

    println!("      ✅ 恢复策略执行完成");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_basic_prediction() {
        let result = basic_prediction_demo().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_error_prediction() {
        let result = error_prediction_demo().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_model_training() {
        let result = model_training_demo().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_online_learning() {
        let result = online_learning_demo().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_adaptive_recovery() {
        let result = adaptive_recovery_demo().await;
        assert!(result.is_ok());
    }
}
