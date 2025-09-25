//! # 数据验证模块
//!
//! 提供 OTLP 数据的验证功能，确保数据符合 OpenTelemetry 规范。

use crate::data::{TelemetryData, TraceData, MetricData, LogData};
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
        }
        
        self.validate_common_fields(data)?;
        Ok(())
    }
    
    /// 验证追踪数据
    fn validate_trace_data(&self, trace: &TraceData) -> Result<()> {
        // 验证必需的字段
        if trace.trace_id.is_empty() {
            return Err(OtlpError::ValidationError("trace_id 不能为空".to_string()));
        }
        
        if trace.span_id.is_empty() {
            return Err(OtlpError::ValidationError("span_id 不能为空".to_string()));
        }
        
        if trace.name.is_empty() {
            return Err(OtlpError::ValidationError("span name 不能为空".to_string()));
        }
        
        // 验证时间戳
        if trace.end_time > 0 && trace.end_time < trace.start_time {
            return Err(OtlpError::ValidationError("end_time 不能小于 start_time".to_string()));
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
            return Err(OtlpError::ValidationError("metric name 不能为空".to_string()));
        }
        
        if metric.data_points.is_empty() {
            return Err(OtlpError::ValidationError("metric 必须至少有一个数据点".to_string()));
        }
        
        // 验证数据点
        for (index, data_point) in metric.data_points.iter().enumerate() {
            self.validate_data_point(data_point, index)?;
        }
        
        Ok(())
    }
    
    /// 验证日志数据
    fn validate_log_data(&self, log: &LogData) -> Result<()> {
        if log.message.is_empty() {
            return Err(OtlpError::ValidationError("log message 不能为空".to_string()));
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
            return Err(OtlpError::ValidationError(
                format!("数据点 {} 的 timestamp 不能为 0", index)
            ));
        }
        
        self.validate_attributes_map(&data_point.attributes)?;
        
        Ok(())
    }
    
    /// 验证严重程度
    fn validate_severity(&self, severity: crate::data::LogSeverity) -> Result<()> {
        match severity {
            crate::data::LogSeverity::Trace => Ok(()),
            crate::data::LogSeverity::Debug => Ok(()),
            crate::data::LogSeverity::Info => Ok(()),
            crate::data::LogSeverity::Warn => Ok(()),
            crate::data::LogSeverity::Error => Ok(()),
            crate::data::LogSeverity::Fatal => Ok(()),
        }
    }
    
    /// 验证属性
    fn validate_attributes(&self, attributes: &std::collections::HashMap<String, String>) -> Result<()> {
        for (key, value) in attributes {
            if key.is_empty() {
                return Err(OtlpError::ValidationError("属性键不能为空".to_string()));
            }
            
            if self.strict_mode && key.len() > 255 {
                return Err(OtlpError::ValidationError(
                    format!("属性键 '{}' 长度超过 255 字符", key)
                ));
            }
            
            if self.strict_mode && value.len() > 16384 {
                return Err(OtlpError::ValidationError(
                    format!("属性值长度超过 16384 字符")
                ));
            }
        }
        
        Ok(())
    }
    
    /// 验证属性映射
    fn validate_attributes_map(&self, attributes: &std::collections::HashMap<String, crate::data::AttributeValue>) -> Result<()> {
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
                if self.strict_mode && s.len() > 16384 {
                    return Err(OtlpError::ValidationError("字符串属性值长度超过限制".to_string()));
                }
            }
            crate::data::AttributeValue::StringArray(arr) => {
                if self.strict_mode && arr.len() > 128 {
                    return Err(OtlpError::ValidationError("字符串数组长度超过限制".to_string()));
                }
                
                for item in arr {
                    if self.strict_mode && item.len() > 16384 {
                        return Err(OtlpError::ValidationError("字符串数组元素长度超过限制".to_string()));
                    }
                }
            }
            crate::data::AttributeValue::BoolArray(arr) => {
                if self.strict_mode && arr.len() > 128 {
                    return Err(OtlpError::ValidationError("布尔数组长度超过限制".to_string()));
                }
            }
            crate::data::AttributeValue::IntArray(arr) => {
                if self.strict_mode && arr.len() > 128 {
                    return Err(OtlpError::ValidationError("整数数组长度超过限制".to_string()));
                }
            }
            crate::data::AttributeValue::DoubleArray(arr) => {
                if self.strict_mode && arr.len() > 128 {
                    return Err(OtlpError::ValidationError("浮点数组长度超过限制".to_string()));
                }
            }
            _ => {} // 其他类型无需额外验证
        }
        
        Ok(())
    }
    
    /// 验证 Trace ID 格式
    fn validate_trace_id_format(&self, trace_id: &str) -> Result<()> {
        if trace_id.len() != 32 {
            return Err(OtlpError::ValidationError(
                format!("trace_id 长度必须为 32 字符，实际为 {}", trace_id.len())
            ));
        }
        
        if !trace_id.chars().all(|c| c.is_ascii_hexdigit()) {
            return Err(OtlpError::ValidationError("trace_id 必须为十六进制字符串".to_string()));
        }
        
        // 验证不能全为 0
        if trace_id.chars().all(|c| c == '0') {
            return Err(OtlpError::ValidationError("trace_id 不能全为 0".to_string()));
        }
        
        Ok(())
    }
    
    /// 验证 Span ID 格式
    fn validate_span_id_format(&self, span_id: &str) -> Result<()> {
        if span_id.len() != 16 {
            return Err(OtlpError::ValidationError(
                format!("span_id 长度必须为 16 字符，实际为 {}", span_id.len())
            ));
        }
        
        if !span_id.chars().all(|c| c.is_ascii_hexdigit()) {
            return Err(OtlpError::ValidationError("span_id 必须为十六进制字符串".to_string()));
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
            return Err(OtlpError::ValidationError(
                format!("无效的 endpoint URL: {}", e)
            ));
        }
        
        // 验证超时设置
        if config.connect_timeout.as_secs() == 0 {
            return Err(OtlpError::ValidationError("connect_timeout 必须大于 0".to_string()));
        }
        
        if config.request_timeout.as_secs() == 0 {
            return Err(OtlpError::ValidationError("request_timeout 必须大于 0".to_string()));
        }
        
        // 验证重试设置
        if config.retry_config.max_retries > 10 {
            return Err(OtlpError::ValidationError("max_retries 不能超过 10".to_string()));
        }
        
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::{TelemetryData, TelemetryDataType, TelemetryContent, TraceData, SpanKind};
    
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
            TelemetryContent::Trace(trace_data)
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
            TelemetryContent::Trace(trace_data)
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
            TelemetryContent::Trace(trace_data)
        );
        
        assert!(validator.validate_telemetry_data(&telemetry_data).is_err());
    }
}
