//! # OPAMP 协议消息定义
//!
//! 定义了 OPAMP 协议中的所有消息类型和结构。

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
//use std::time::{Duration, SystemTime};

/// Agent 到 Server 的消息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AgentToServer {
    /// Agent 实例标识
    pub instance_uid: String,
    
    /// Agent 描述
    pub agent_description: Option<AgentDescription>,
    
    /// Agent 能力
    pub capabilities: Option<AgentCapabilities>,
    
    /// 远程配置状态
    pub remote_config_status: Option<RemoteConfigStatus>,
    
    /// 包状态
    pub package_statuses: Vec<PackageStatus>,
    
    /// Agent 健康状态
    pub agent_health: Option<AgentHealth>,
    
    /// 有效配置
    pub effective_config: Option<EffectiveConfig>,
    
    /// 遥测数据
    pub agent_telemetry: Option<AgentTelemetry>,
}

/// Server 到 Agent 的消息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServerToAgent {
    /// 远程配置
    pub remote_config: Option<RemoteConfig>,
    
    /// 包可用性
    pub packages_available: HashMap<String, PackageAvailable>,
    
    /// 包安装
    pub packages_install: HashMap<String, PackageInstall>,
    
    /// 服务器错误响应
    pub error_response: Option<ServerErrorResponse>,
    
    /// 连接设置
    pub connection_settings: Option<ConnectionSettings>,
    
    /// 其他设置
    pub other_settings: Option<OtherSettings>,
}

/// Agent 描述
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AgentDescription {
    /// 标识信息
    pub identifying_attributes: Vec<KeyValue>,
    
    /// 非标识属性
    pub non_identifying_attributes: Vec<KeyValue>,
}

/// Agent 能力
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AgentCapabilities {
    /// 报告有效配置
    pub reports_effective_config: bool,
    
    /// 报告自己的追踪
    pub reports_own_traces: bool,
    
    /// 报告自己的指标
    pub reports_own_metrics: bool,
    
    /// 报告自己的日志
    pub reports_own_logs: bool,
    
    /// 接受远程配置
    pub accepts_remote_config: bool,
    
    /// 接受包
    pub accepts_packages: bool,
    
    /// 报告健康状态
    pub reports_health: bool,
    
    /// 报告远程配置
    pub reports_remote_config: bool,
}

/// 远程配置状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RemoteConfigStatus {
    /// 最后远程配置哈希
    pub last_remote_config_hash: Vec<u8>,
    
    /// 状态
    pub status: RemoteConfigStatusType,
    
    /// 错误消息
    pub error_message: Option<String>,
}

/// 远程配置状态类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RemoteConfigStatusType {
    /// 未设置
    Unset,
    
    /// 应用成功
    Applied,
    
    /// 应用失败
    AppliedFailed,
    
    /// 未应用
    NotApplied,
}

/// 包状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PackageStatus {
    /// 包名
    pub name: String,
    
    /// 服务器提供的哈希
    pub server_provided_hash: Vec<u8>,
    
    /// 状态
    pub status: PackageStatusType,
    
    /// 错误消息
    pub error_message: Option<String>,
}

/// 包状态类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PackageStatusType {
    /// 未设置
    Unset,
    
    /// 已安装
    Installed,
    
    /// 安装失败
    InstallFailed,
    
    /// 安装中
    Installing,
}

/// Agent 健康状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AgentHealth {
    /// 健康状态
    pub healthy: bool,
    
    /// 开始时间
    pub start_time_unix_nano: u64,
    
    /// 上次错误时间
    pub last_error_time_unix_nano: Option<u64>,
    
    /// 上次错误消息
    pub last_error_message: Option<String>,
    
    /// 状态消息
    pub status_message: Option<String>,
}

/// 有效配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EffectiveConfig {
    /// 配置映射
    pub config_map: HashMap<String, ConfigFile>,
}

/// 配置文件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConfigFile {
    /// 文件内容
    pub body: Vec<u8>,
    
    /// 内容类型
    pub content_type: Option<String>,
}

/// Agent 遥测数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AgentTelemetry {
    /// 指标
    pub metrics: Option<TelemetryMetrics>,
    
    /// 日志
    pub logs: Option<TelemetryLogs>,
    
    /// 追踪
    pub traces: Option<TelemetryTraces>,
}

/// 遥测指标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TelemetryMetrics {
    /// 指标数据
    pub metrics: Vec<MetricData>,
}

/// 遥测日志
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TelemetryLogs {
    /// 日志数据
    pub logs: Vec<LogData>,
}

/// 遥测追踪
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TelemetryTraces {
    /// 追踪数据
    pub traces: Vec<TraceData>,
}

/// 远程配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RemoteConfig {
    /// 配置哈希
    pub config_hash: Vec<u8>,
    
    /// 配置映射
    pub config: HashMap<String, ConfigFile>,
}

/// 包可用性
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PackageAvailable {
    /// 包类型
    pub package_type: PackageType,
    
    /// 版本
    pub version: String,
    
    /// 哈希
    pub hash: Vec<u8>,
    
    /// 下载 URL
    pub download_url: Option<String>,
    
    /// 内容
    pub content: Option<Vec<u8>>,
    
    /// 签名
    pub signature: Option<Vec<u8>>,
}

/// 包安装
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PackageInstall {
    /// 包类型
    pub package_type: PackageType,
    
    /// 版本
    pub version: String,
    
    /// 哈希
    pub hash: Vec<u8>,
    
    /// 安装时间
    pub install_time_unix_nano: Option<u64>,
}

/// 包类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PackageType {
    /// 未设置
    Unset,
    
    /// 顶级包
    TopLevel,
    
    /// 插件包
    Plugin,
}

/// 服务器错误响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServerErrorResponse {
    /// 错误类型
    pub error_type: ServerErrorType,
    
    /// 错误消息
    pub error_message: String,
    
    /// 详细信息
    pub details: Option<Vec<u8>>,
}

/// 服务器错误类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ServerErrorType {
    /// 未设置
    Unset,
    
    /// 未知错误
    Unknown,
    
    /// 配置错误
    ConfigError,
    
    /// 包错误
    PackageError,
    
    /// 网络错误
    NetworkError,
}

/// 连接设置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConnectionSettings {
    /// 目标端点
    pub destination_endpoint: Option<String>,
    
    /// 头信息
    pub headers: HashMap<String, String>,
    
    /// 其他设置
    pub other_settings: HashMap<String, String>,
}

/// 其他设置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OtherSettings {
    /// 设置映射
    pub other_settings: HashMap<String, String>,
}

/// 键值对
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct KeyValue {
    /// 键
    pub key: String,
    
    /// 值
    pub value: Value,
}

/// 值类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Value {
    /// 字符串值
    StringValue(String),
    
    /// 布尔值
    BoolValue(bool),
    
    /// 整数
    IntValue(i64),
    
    /// 双精度浮点数
    DoubleValue(f64),
    
    /// 字节数组
    BytesValue(Vec<u8>),
}

/// 指标数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MetricData {
    /// 指标名
    pub name: String,
    
    /// 指标描述
    pub description: String,
    
    /// 单位
    pub unit: String,
    
    /// 数据类型
    pub data_type: MetricDataType,
    
    /// 数据点
    pub data_points: Vec<DataPoint>,
}

/// 指标数据类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MetricDataType {
    /// 计数器
    Counter,
    
    /// 仪表
    Gauge,
    
    /// 直方图
    Histogram,
    
    /// 摘要
    Summary,
}

/// 数据点
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DataPoint {
    /// 时间戳
    pub time_unix_nano: u64,
    
    /// 属性
    pub attributes: Vec<KeyValue>,
    
    /// 值
    pub value: DataPointValue,
}

/// 数据点值
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DataPointValue {
    /// 数值
    NumberValue(f64),
    
    /// 直方图值
    HistogramValue(HistogramData),
    
    /// 摘要值
    SummaryValue(SummaryData),
}

/// 直方图数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HistogramData {
    /// 计数
    pub count: u64,
    
    /// 总和
    pub sum: f64,
    
    /// 桶
    pub buckets: Vec<HistogramBucket>,
}

/// 直方图桶
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HistogramBucket {
    /// 计数
    pub count: u64,
    
    /// 上限
    pub upper_bound: f64,
}

/// 摘要数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SummaryData {
    /// 计数
    pub count: u64,
    
    /// 总和
    pub sum: f64,
    
    /// 分位数
    pub quantiles: Vec<Quantile>,
}

/// 分位数
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Quantile {
    /// 分位数
    pub quantile: f64,
    
    /// 值
    pub value: f64,
}

/// 日志数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogData {
    /// 时间戳
    pub time_unix_nano: u64,
    
    /// 严重程度
    pub severity_number: u32,
    
    /// 严重程度文本
    pub severity_text: String,
    
    /// 消息
    pub body: Value,
    
    /// 属性
    pub attributes: Vec<KeyValue>,
    
    /// 资源属性
    pub resource_attributes: Vec<KeyValue>,
}

/// 追踪数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraceData {
    /// 追踪 ID
    pub trace_id: Vec<u8>,
    
    /// 跨度 ID
    pub span_id: Vec<u8>,
    
    /// 父跨度 ID
    pub parent_span_id: Option<Vec<u8>>,
    
    /// 名称
    pub name: String,
    
    /// 类型
    pub kind: SpanKind,
    
    /// 开始时间
    pub start_time_unix_nano: u64,
    
    /// 结束时间
    pub end_time_unix_nano: u64,
    
    /// 属性
    pub attributes: Vec<KeyValue>,
    
    /// 事件
    pub events: Vec<SpanEvent>,
    
    /// 状态
    pub status: Option<SpanStatus>,
}

/// 跨度类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SpanKind {
    /// 未设置
    Unset,
    
    /// 内部
    Internal,
    
    /// 服务器
    Server,
    
    /// 客户端
    Client,
    
    /// 生产者
    Producer,
    
    /// 消费者
    Consumer,
}

/// 跨度事件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpanEvent {
    /// 时间戳
    pub time_unix_nano: u64,
    
    /// 名称
    pub name: String,
    
    /// 属性
    pub attributes: Vec<KeyValue>,
}

/// 跨度状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpanStatus {
    /// 代码
    pub code: StatusCode,
    
    /// 消息
    pub message: Option<String>,
}

/// 状态代码
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum StatusCode {
    /// 未设置
    Unset,
    
    /// 成功
    Ok,
    
    /// 错误
    Error,
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_agent_description_serialization() {
        let desc = AgentDescription {
            identifying_attributes: vec![
                KeyValue {
                    key: "service.name".to_string(),
                    value: Value::StringValue("test-service".to_string()),
                }
            ],
            non_identifying_attributes: vec![],
        };
        
        let serialized = serde_json::to_string(&desc).unwrap();
        let deserialized: AgentDescription = serde_json::from_str(&serialized).unwrap();
        
        assert_eq!(desc.identifying_attributes.len(), deserialized.identifying_attributes.len());
    }
    
    #[test]
    fn test_agent_capabilities() {
        let capabilities = AgentCapabilities {
            reports_effective_config: true,
            reports_own_traces: true,
            reports_own_metrics: true,
            reports_own_logs: true,
            accepts_remote_config: true,
            accepts_packages: true,
            reports_health: true,
            reports_remote_config: true,
        };
        
        assert!(capabilities.reports_effective_config);
        assert!(capabilities.accepts_remote_config);
    }
}
