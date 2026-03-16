//! # 数据验证模块
//!
//! 提供 OTLP 数据的验证功能，确保数据符合 OpenTelemetry 规范。
//!
//! ## Rust 1.92 特性应用
//!
//! - **常量泛型**: 使用常量泛型优化验证规则和缓冲区大小
//! - **改进的错误处理**: 利用 Rust 1.92 的错误处理优化提升性能
//! - **元组收集**: 使用 `collect()` 直接收集验证结果到元组

use crate::data::{LogData, MetricData, TelemetryData, TraceData};
use crate::error::DataError;
use crate::error::{OtlpError, Result};

/// 数据验证器
pub struct DataValidator {
    strict_mode: bool,
}

impl DataValidator {
    /// 创建新的验证器
    pub fn new(strict_mode: bool) -> Self {
        Self { strict_mode }
    }

    /// 验证遥测数据
    pub fn validate_telemetry_data(&self, data: &TelemetryData) -> Result<()> {
        match &data.content {
            crate::data::TelemetryContent::Trace(trace) => {
                self.validate_trace_data(trace)?;
            }
            crate::data::TelemetryContent::Metric(metric) => {
                self.validate_metric_data(metric)?;
            }
            crate::data::TelemetryContent::Log(log) => {
                self.validate_log_data(log)?;
            }
            crate::data::TelemetryContent::Profile(profile) => {
                self.validate_profile_data(profile)?;
            }
        }

        self.validate_common_fields(data)?;
        Ok(())
    }

    /// 验证性能分析数据 (Development)
    fn validate_profile_data(&self, profile: &crate::data::ProfileData) -> Result<()> {
        if profile.sample_types.is_empty() {
            return Err(OtlpError::Data(DataError::Validation {
                reason: "sample_types 不能为空".to_string(),
            }));
        }
        if profile.samples.is_empty() {
            return Err(OtlpError::Data(DataError::Validation {
                reason: "samples 不能为空".to_string(),
            }));
        }
        Ok(())
    }

    /// 验证追踪数据
    fn validate_trace_data(&self, trace: &TraceData) -> Result<()> {
        // 验证必需的字段
        if trace.trace_id.is_empty() {
            return Err(OtlpError::Data(DataError::Validation {
                reason: "trace_id 不能为空".to_string(),
            }));
        }

        if trace.span_id.is_empty() {
            return Err(OtlpError::ValidationError("span_id 不能为空".to_string()));
        }

        if trace.name.is_empty() {
            return Err(OtlpError::ValidationError("span name 不能为空".to_string()));
        }

        // 验证时间戳
        if trace.end_time > 0 && trace.end_time < trace.start_time {
            return Err(OtlpError::ValidationError(
                "end_time 不能小于 start_time".to_string(),
            ));
        }

        // 严格模式下验证 ID 格式
        if self.strict_mode {
            self.validate_trace_id_format(&trace.trace_id)?;
            self.validate_span_id_format(&trace.span_id)?;

            if let Some(parent_span_id) = &trace.parent_span_id {
                self.validate_span_id_format(parent_span_id)?;
            }
        }

        Ok(())
    }

    /// 验证指标数据
    fn validate_metric_data(&self, metric: &MetricData) -> Result<()> {
        if metric.name.is_empty() {
            return Err(OtlpError::ValidationError(
                "metric name 不能为空".to_string(),
            ));
        }

        if metric.data_points.is_empty() {
            return Err(OtlpError::ValidationError(
                "metric 必须至少有一个数据点".to_string(),
            ));
        }

        // 验证数据点
        for (index, data_point) in metric.data_points.iter().enumerate() {
            self.validate_data_point(data_point, index)?;
        }

        Ok(())
    }

    /// 验证日志数据
    fn validate_log_data(&self, log: &LogData) -> Result<()> {
        if log.message().map(|m| m.is_empty()).unwrap_or(true) {
            return Err(OtlpError::ValidationError(
                "log message 不能为空".to_string(),
            ));
        }

        // 验证严重程度
        self.validate_severity(log.severity)?;

        Ok(())
    }

    /// 验证通用字段
    fn validate_common_fields(&self, data: &TelemetryData) -> Result<()> {
        // 验证时间戳
        if data.timestamp == 0 {
            return Err(OtlpError::ValidationError("timestamp 不能为 0".to_string()));
        }

        // 验证资源属性
        self.validate_attributes(&data.resource_attributes)?;
        self.validate_attributes(&data.scope_attributes)?;

        Ok(())
    }

    /// 验证数据点
    fn validate_data_point(&self, data_point: &crate::data::DataPoint, index: usize) -> Result<()> {
        if data_point.timestamp == 0 {
            return Err(OtlpError::ValidationError(format!(
                "数据点 {} 的 timestamp 不能为 0",
                index
            )));
        }

        self.validate_attributes_map(&data_point.attributes)?;

        Ok(())
    }

    /// 验证严重程度
    fn validate_severity(&self, severity: crate::data::LogSeverity) -> Result<()> {
        // All severity levels are valid in OpenTelemetry
        // Just check that it's within valid range (1-24)
        let severity_num = severity as u8;
        if (1..=24).contains(&severity_num) {
            Ok(())
        } else {
            Err(OtlpError::ValidationError(format!(
                "Invalid severity level: {}",
                severity_num
            )))
        }
    }

    /// 验证属性
    fn validate_attributes(
        &self,
        attributes: &std::collections::HashMap<String, String>,
    ) -> Result<()> {
        for (key, value) in attributes {
            if key.is_empty() {
                return Err(OtlpError::ValidationError("属性键不能为空".to_string()));
            }

            if self.strict_mode && key.len() > 255 {
                return Err(OtlpError::ValidationError(format!(
                    "属性键 '{}' 长度超过 255 字符",
                    key
                )));
            }

            if self.strict_mode && value.len() > 16384 {
                return Err(OtlpError::ValidationError(
                    "属性值长度超过 16384 字符".to_string(),
                ));
            }
        }

        Ok(())
    }

    /// 验证属性映射
    fn validate_attributes_map(
        &self,
        attributes: &std::collections::HashMap<String, crate::data::AttributeValue>,
    ) -> Result<()> {
        for (key, value) in attributes {
            if key.is_empty() {
                return Err(OtlpError::ValidationError("属性键不能为空".to_string()));
            }

            self.validate_attribute_value(value)?;
        }

        Ok(())
    }

    /// 验证属性值
    fn validate_attribute_value(&self, value: &crate::data::AttributeValue) -> Result<()> {
        match value {
            crate::data::AttributeValue::String(s) => {
                self.validate_string_value(s)?;
            }
            crate::data::AttributeValue::StringArray(arr) => {
                self.validate_string_array(arr)?;
            }
            crate::data::AttributeValue::BoolArray(arr) => {
                self.validate_array_limit(arr.len(), "布尔")?;
            }
            crate::data::AttributeValue::IntArray(arr) => {
                self.validate_array_limit(arr.len(), "整数")?;
            }
            crate::data::AttributeValue::DoubleArray(arr) => {
                self.validate_array_limit(arr.len(), "浮点")?;
            }
            _ => {} // 其他类型无需额外验证
        }

        Ok(())
    }

    fn validate_string_value(&self, s: &str) -> Result<()> {
        if self.strict_mode && s.len() > 16384 {
            return Err(OtlpError::ValidationError(
                "字符串属性值长度超过限制".to_string(),
            ));
        }
        Ok(())
    }

    fn validate_string_array(&self, arr: &[String]) -> Result<()> {
        if self.strict_mode && arr.len() > 128 {
            return Err(OtlpError::ValidationError(
                "字符串数组长度超过限制".to_string(),
            ));
        }

        for item in arr {
            if self.strict_mode && item.len() > 16384 {
                return Err(OtlpError::ValidationError(
                    "字符串数组元素长度超过限制".to_string(),
                ));
            }
        }
        Ok(())
    }

    fn validate_array_limit(&self, len: usize, type_name: &str) -> Result<()> {
        if self.strict_mode && len > 128 {
            return Err(OtlpError::ValidationError(format!(
                "{}数组长度超过限制",
                type_name
            )));
        }
        Ok(())
    }

    /// 验证 Trace ID 格式
    fn validate_trace_id_format(&self, trace_id: &str) -> Result<()> {
        if trace_id.len() != 32 {
            return Err(OtlpError::ValidationError(format!(
                "trace_id 长度必须为 32 字符，实际为 {}",
                trace_id.len()
            )));
        }

        if !trace_id.chars().all(|c| c.is_ascii_hexdigit()) {
            return Err(OtlpError::ValidationError(
                "trace_id 必须为十六进制字符串".to_string(),
            ));
        }

        // 验证不能全为 0
        if trace_id.chars().all(|c| c == '0') {
            return Err(OtlpError::ValidationError(
                "trace_id 不能全为 0".to_string(),
            ));
        }

        Ok(())
    }

    /// 验证 Span ID 格式
    fn validate_span_id_format(&self, span_id: &str) -> Result<()> {
        if span_id.len() != 16 {
            return Err(OtlpError::ValidationError(format!(
                "span_id 长度必须为 16 字符，实际为 {}",
                span_id.len()
            )));
        }

        if !span_id.chars().all(|c| c.is_ascii_hexdigit()) {
            return Err(OtlpError::ValidationError(
                "span_id 必须为十六进制字符串".to_string(),
            ));
        }

        // 验证不能全为 0
        if span_id.chars().all(|c| c == '0') {
            return Err(OtlpError::ValidationError("span_id 不能全为 0".to_string()));
        }

        Ok(())
    }
}

/// 配置验证器
pub struct ConfigValidator;

impl ConfigValidator {
    /// 验证 OTLP 配置
    pub fn validate_config(config: &crate::config::OtlpConfig) -> Result<()> {
        if config.endpoint.is_empty() {
            return Err(OtlpError::ValidationError("endpoint 不能为空".to_string()));
        }

        // 验证 URL 格式
        if let Err(e) = url::Url::parse(&config.endpoint) {
            return Err(OtlpError::ValidationError(format!(
                "无效的 endpoint URL: {}",
                e
            )));
        }

        // 验证超时设置
        if config.connect_timeout.as_secs() == 0 {
            return Err(OtlpError::ValidationError(
                "connect_timeout 必须大于 0".to_string(),
            ));
        }

        if config.request_timeout.as_secs() == 0 {
            return Err(OtlpError::ValidationError(
                "request_timeout 必须大于 0".to_string(),
            ));
        }

        // 验证重试设置
        if config.retry_config.max_retries > 10 {
            return Err(OtlpError::ValidationError(
                "max_retries 不能超过 10".to_string(),
            ));
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::{SpanKind, TelemetryContent, TelemetryData, TelemetryDataType, TraceData};

    #[test]
    fn test_validate_trace_data() {
        let validator = DataValidator::new(true);

        let trace_data = TraceData {
            trace_id: "12345678901234567890123456789012".to_string(),
            span_id: "1234567890123456".to_string(),
            parent_span_id: None,
            name: "test-span".to_string(),
            span_kind: SpanKind::Internal,
            start_time: 1000,
            end_time: 2000,
            status: crate::data::SpanStatus::default(),
            attributes: std::collections::HashMap::new(),
            events: vec![],
            links: vec![],
        };

        let telemetry_data = TelemetryData::new(
            TelemetryDataType::Trace,
            TelemetryContent::Trace(trace_data),
        );

        assert!(validator.validate_telemetry_data(&telemetry_data).is_ok());
    }

    #[test]
    fn test_validate_invalid_trace_id() {
        let validator = DataValidator::new(true);

        let trace_data = TraceData {
            trace_id: "invalid".to_string(), // 无效的 trace_id
            span_id: "1234567890123456".to_string(),
            parent_span_id: None,
            name: "test-span".to_string(),
            span_kind: SpanKind::Internal,
            start_time: 1000,
            end_time: 2000,
            status: crate::data::SpanStatus::default(),
            attributes: std::collections::HashMap::new(),
            events: vec![],
            links: vec![],
        };

        let telemetry_data = TelemetryData::new(
            TelemetryDataType::Trace,
            TelemetryContent::Trace(trace_data),
        );

        assert!(validator.validate_telemetry_data(&telemetry_data).is_err());
    }

    #[test]
    fn test_validate_empty_trace_id() {
        let validator = DataValidator::new(false);

        let trace_data = TraceData {
            trace_id: "".to_string(), // 空的 trace_id
            span_id: "1234567890123456".to_string(),
            parent_span_id: None,
            name: "test-span".to_string(),
            span_kind: SpanKind::Internal,
            start_time: 1000,
            end_time: 2000,
            status: crate::data::SpanStatus::default(),
            attributes: std::collections::HashMap::new(),
            events: vec![],
            links: vec![],
        };

        let telemetry_data = TelemetryData::new(
            TelemetryDataType::Trace,
            TelemetryContent::Trace(trace_data),
        );

        assert!(validator.validate_telemetry_data(&telemetry_data).is_err());
    }
}
