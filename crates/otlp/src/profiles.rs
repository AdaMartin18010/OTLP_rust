//! OTLP Profiles 信号支持
//!
//! 实现 OpenTelemetry Protocol 1.9.0 中的 Profiles 信号，支持持续性能分析。
//!
//! ## 特性
//! - CPU 性能分析
//! - 内存分配分析
//! - 堆分析
//! - 互斥锁竞争分析
//! - 与 Trace 上下文关联
//!
//! 参考:
//! - https://opentelemetry.io/blog/2024/profiling/
//! - https://github.com/open-telemetry/opentelemetry-proto/tree/main/opentelemetry/proto/profiles/v1development

use opentelemetry::trace::SpanContext;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::Duration;

/// Profile 类型
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ProfileType {
    /// CPU 性能分析
    Cpu,
    /// 内存分配分析
    Allocation,
    /// 堆分析
    Heap,
    /// 互斥锁竞争分析
    Mutex,
    /// Goroutine 分析 (Go 专用)
    Goroutine,
    /// 墙钟时间分析
    Wall,
    /// 自定义类型
    Custom(String),
}

impl ProfileType {
    /// 获取 MIME 类型
    pub fn mime_type(&self) -> &'static str {
        match self {
            ProfileType::Cpu => "application/vnd.google.protobuf+gzip",
            ProfileType::Allocation => "application/vnd.google.protobuf+gzip",
            ProfileType::Heap => "application/vnd.google.protobuf+gzip",
            ProfileType::Mutex => "application/vnd.google.protobuf+gzip",
            ProfileType::Goroutine => "application/vnd.google.protobuf+gzip",
            ProfileType::Wall => "application/vnd.google.protobuf+gzip",
            ProfileType::Custom(_) => "application/octet-stream",
        }
    }

    /// 获取字符串表示
    pub fn as_str(&self) -> String {
        match self {
            ProfileType::Cpu => "cpu".to_string(),
            ProfileType::Allocation => "allocation".to_string(),
            ProfileType::Heap => "heap".to_string(),
            ProfileType::Mutex => "mutex".to_string(),
            ProfileType::Goroutine => "goroutine".to_string(),
            ProfileType::Wall => "wall".to_string(),
            ProfileType::Custom(s) => s.clone(),
        }
    }
}

/// Profile 样本
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProfileSample {
    /// 调用栈（函数名列表，从内到外）
    pub stack_trace: Vec<String>,
    /// 采样值（如 CPU 时间、内存大小等）
    pub value: i64,
    /// 标签（可选）
    pub labels: HashMap<String, String>,
}

/// Profile 数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProfileData {
    /// Profile 类型
    pub profile_type: ProfileType,
    /// 样本列表
    pub samples: Vec<ProfileSample>,
    /// 采样开始时间戳（Unix 秒）
    pub start_time_unix: u64,
    /// 采样持续时间（毫秒）
    pub duration_ms: u64,
    /// 关联的 Trace ID（如果有）
    pub linked_trace_id: Option<String>,
    /// 关联的 Span ID（如果有）
    pub linked_span_id: Option<String>,
    /// 资源属性
    pub resource_attributes: HashMap<String, String>,
    /// 原始 pprof 数据（如果有）
    #[serde(skip_serializing_if = "Option::is_none")]
    pub raw_pprof: Option<Vec<u8>>,
}

impl ProfileData {
    /// 创建新的 Profile 数据
    pub fn new(profile_type: ProfileType) -> Self {
        use std::time::{SystemTime, UNIX_EPOCH};
        Self {
            profile_type,
            samples: Vec::new(),
            start_time_unix: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs(),
            duration_ms: 0,
            linked_trace_id: None,
            linked_span_id: None,
            resource_attributes: HashMap::new(),
            raw_pprof: None,
        }
    }

    /// 添加样本
    pub fn add_sample(&mut self, stack_trace: Vec<String>, value: i64) {
        self.samples.push(ProfileSample {
            stack_trace,
            value,
            labels: HashMap::new(),
        });
    }

    /// 添加带标签的样本
    pub fn add_sample_with_labels(
        &mut self,
        stack_trace: Vec<String>,
        value: i64,
        labels: HashMap<String, String>,
    ) {
        self.samples.push(ProfileSample {
            stack_trace,
            value,
            labels,
        });
    }

    /// 关联 Trace 上下文
    pub fn link_trace_context(&mut self, span_context: SpanContext) {
        self.linked_trace_id = Some(span_context.trace_id().to_string());
        self.linked_span_id = Some(span_context.span_id().to_string());
    }

    /// 添加资源属性
    pub fn add_resource_attribute(&mut self, key: impl Into<String>, value: impl Into<String>) {
        self.resource_attributes.insert(key.into(), value.into());
    }

    /// 获取热点函数（消耗最多资源的函数）
    pub fn get_hotspots(&self, top_n: usize) -> Vec<(String, i64)> {
        let mut function_values: HashMap<String, i64> = HashMap::new();

        for sample in &self.samples {
            if let Some(function_name) = sample.stack_trace.first() {
                *function_values.entry(function_name.clone()).or_insert(0) += sample.value;
            }
        }

        let mut hotspots: Vec<(String, i64)> = function_values.into_iter().collect();
        hotspots.sort_by(|a, b| b.1.cmp(&a.1));
        hotspots.truncate(top_n);

        hotspots
    }

    /// 转换为火焰图格式
    pub fn to_flamegraph_format(&self) -> String {
        let mut lines = Vec::new();

        for sample in &self.samples {
            let stack = sample.stack_trace.join(";");
            lines.push(format!("{} {}", stack, sample.value));
        }

        lines.join("\n")
    }

    /// 合并相同调用栈的样本
    pub fn merge_samples(&mut self) {
        let mut merged: HashMap<Vec<String>, i64> = HashMap::new();

        for sample in &self.samples {
            *merged.entry(sample.stack_trace.clone()).or_insert(0) += sample.value;
        }

        self.samples = merged
            .into_iter()
            .map(|(stack_trace, value)| ProfileSample {
                stack_trace,
                value,
                labels: HashMap::new(),
            })
            .collect();
    }
}

/// Profile 导出器 trait
#[async_trait::async_trait]
pub trait ProfileExporter: Send + Sync {
    /// 导出 Profile 数据
    async fn export(&self, profile: &ProfileData) -> Result<(), ProfileError>;
    
    /// 关闭导出器
    async fn shutdown(&self) -> Result<(), ProfileError>;
}

/// Profile 错误
#[derive(Debug, thiserror::Error)]
pub enum ProfileError {
    #[error("Export failed: {0}")]
    ExportError(String),
    #[error("Invalid profile data: {0}")]
    InvalidData(String),
    #[error("Serialization failed: {0}")]
    SerializationError(#[from] serde_json::Error),
    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),
    #[error("HTTP error: {0}")]
    HttpError(String),
}

/// OTLP Profile 导出器
pub struct OtlpProfileExporter {
    endpoint: String,
    headers: HashMap<String, String>,
    client: reqwest::Client,
}

impl OtlpProfileExporter {
    /// 创建新的 OTLP Profile 导出器
    pub fn new(endpoint: impl Into<String>) -> Self {
        Self {
            endpoint: endpoint.into(),
            headers: HashMap::new(),
            client: reqwest::Client::new(),
        }
    }

    /// 添加自定义头
    pub fn with_header(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.headers.insert(key.into(), value.into());
        self
    }

    /// 设置超时
    pub fn with_timeout(mut self, timeout: Duration) -> Result<Self, ProfileError> {
        self.client = reqwest::Client::builder()
            .timeout(timeout)
            .build()
            .map_err(|e| ProfileError::HttpError(e.to_string()))?;
        Ok(self)
    }
}

#[async_trait::async_trait]
impl ProfileExporter for OtlpProfileExporter {
    async fn export(&self, profile: &ProfileData) -> Result<(), ProfileError> {
        let url = format!("{}/v1/profiles", self.endpoint);
        
        let body = serde_json::to_vec(profile)?;
        
        let mut request = self.client
            .post(&url)
            .header("Content-Type", "application/json");
        
        for (key, value) in &self.headers {
            request = request.header(key, value);
        }
        
        let response = request
            .body(body)
            .send()
            .await
            .map_err(|e| ProfileError::HttpError(e.to_string()))?;
        
        if !response.status().is_success() {
            return Err(ProfileError::ExportError(
                format!("HTTP {}: {}", response.status(), response.text().await.unwrap_or_default())
            ));
        }
        
        Ok(())
    }

    async fn shutdown(&self) -> Result<(), ProfileError> {
        // OTLP HTTP 客户端无需特殊关闭逻辑
        Ok(())
    }
}

/// 文件 Profile 导出器（用于调试）
pub struct FileProfileExporter {
    output_dir: std::path::PathBuf,
}

impl FileProfileExporter {
    /// 创建文件导出器
    pub fn new(output_dir: impl Into<std::path::PathBuf>) -> Self {
        Self {
            output_dir: output_dir.into(),
        }
    }
}

#[async_trait::async_trait]
impl ProfileExporter for FileProfileExporter {
    async fn export(&self, profile: &ProfileData) -> Result<(), ProfileError> {
        use tokio::io::AsyncWriteExt;

        // 确保输出目录存在
        tokio::fs::create_dir_all(&self.output_dir).await?;

        let filename = format!(
            "{}_{}.json",
            profile.profile_type.as_str(),
            chrono::Local::now().format("%Y%m%d_%H%M%S")
        );
        let filepath = self.output_dir.join(filename);

        let json = serde_json::to_string_pretty(profile)?;
        let mut file = tokio::fs::File::create(&filepath).await?;
        file.write_all(json.as_bytes()).await?;

        Ok(())
    }

    async fn shutdown(&self) -> Result<(), ProfileError> {
        Ok(())
    }
}

/// Profile 收集器
pub struct ProfileCollector {
    exporter: Box<dyn ProfileExporter>,
    profile_type: ProfileType,
    sample_rate: u32,
    max_samples: usize,
    current_profile: Option<ProfileData>,
}

impl ProfileCollector {
    /// 创建新的 Profile 收集器
    pub fn new(
        exporter: Box<dyn ProfileExporter>,
        profile_type: ProfileType,
    ) -> Self {
        Self {
            exporter,
            profile_type,
            sample_rate: 100, // 默认 100 samples/second
            max_samples: 10_000,
            current_profile: None,
        }
    }

    /// 设置采样率
    pub fn with_sample_rate(mut self, rate: u32) -> Self {
        self.sample_rate = rate;
        self
    }

    /// 设置最大样本数
    pub fn with_max_samples(mut self, max: usize) -> Self {
        self.max_samples = max;
        self
    }

    /// 开始收集
    pub fn start(&mut self) {
        self.current_profile = Some(ProfileData::new(self.profile_type.clone()));
    }

    /// 记录样本
    pub fn record_sample(&mut self, stack_trace: Vec<String>, value: i64) {
        if let Some(profile) = &mut self.current_profile {
            if profile.samples.len() < self.max_samples {
                profile.add_sample(stack_trace, value);
            }
        }
    }

    /// 停止并导出
    pub async fn stop_and_export(&mut self) -> Result<(), ProfileError> {
        if let Some(mut profile) = self.current_profile.take() {
            use std::time::{SystemTime, UNIX_EPOCH};
            let now = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs();
            profile.duration_ms = (now - profile.start_time_unix) * 1000;
            profile.merge_samples();
            self.exporter.export(&profile).await?;
        }
        Ok(())
    }

    /// 获取当前样本数
    pub fn sample_count(&self) -> usize {
        self.current_profile.as_ref().map(|p| p.samples.len()).unwrap_or(0)
    }
}

/// 与 Trace 集成的 Profile 扩展
#[allow(dead_code)]
trait ProfileTraceExtension {
    /// 在 Span 上下文中记录 Profile
    fn record_profile(&self, profile_type: ProfileType, duration: Duration);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_profile_type() {
        assert_eq!(ProfileType::Cpu.as_str(), "cpu");
        assert_eq!(ProfileType::Heap.as_str(), "heap");
    }

    #[test]
    fn test_profile_data() {
        let mut profile = ProfileData::new(ProfileType::Cpu);
        profile.add_sample(vec!["main".to_string(), "foo".to_string(), "bar".to_string()], 100);
        profile.add_sample(vec!["main".to_string(), "foo".to_string(), "baz".to_string()], 50);

        assert_eq!(profile.samples.len(), 2);

        let hotspots = profile.get_hotspots(10);
        assert!(!hotspots.is_empty());
        assert_eq!(hotspots[0].0, "main");
    }

    #[test]
    fn test_merge_samples() {
        let mut profile = ProfileData::new(ProfileType::Cpu);
        profile.add_sample(vec!["a".to_string(), "b".to_string()], 10);
        profile.add_sample(vec!["a".to_string(), "b".to_string()], 20);
        profile.add_sample(vec!["c".to_string(), "d".to_string()], 30);

        profile.merge_samples();

        assert_eq!(profile.samples.len(), 2);
        
        let ab_sample = profile.samples.iter().find(|s| s.stack_trace[0] == "a").unwrap();
        assert_eq!(ab_sample.value, 30);
    }

    #[test]
    fn test_flamegraph_format() {
        let mut profile = ProfileData::new(ProfileType::Cpu);
        profile.add_sample(vec!["main".to_string(), "foo".to_string()], 100);
        profile.add_sample(vec!["main".to_string(), "bar".to_string()], 50);

        let flamegraph = profile.to_flamegraph_format();
        assert!(flamegraph.contains("main;foo 100"));
        assert!(flamegraph.contains("main;bar 50"));
    }
}
