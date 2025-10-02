//! Span 数据结构

use serde::{Serialize, Deserialize};
use std::collections::HashMap;

/// OTLP Span
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Span {
    /// Trace ID (16 字节)
    pub trace_id: [u8; 16],
    
    /// Span ID (8 字节)
    pub span_id: [u8; 8],
    
    /// Parent Span ID
    pub parent_span_id: Option<[u8; 8]>,
    
    /// Span 名称
    pub name: String,
    
    /// 开始时间 (纳秒)
    pub start_time_unix_nano: u64,
    
    /// 结束时间 (纳秒)
    pub end_time_unix_nano: u64,
    
    /// 属性
    pub attributes: HashMap<String, AttributeValue>,
    
    /// 状态
    pub status: SpanStatus,
}

/// 属性值
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum AttributeValue {
    String(String),
    Int(i64),
    Double(f64),
    Bool(bool),
}

/// Span 状态
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum SpanStatus {
    Unset,
    Ok,
    Error { message: String },
}

impl Span {
    /// 创建新 Span
    pub fn new(name: String) -> Self {
        Self {
            trace_id: rand_trace_id(),
            span_id: rand_span_id(),
            parent_span_id: None,
            name,
            start_time_unix_nano: current_time_nanos(),
            end_time_unix_nano: 0,
            attributes: HashMap::new(),
            status: SpanStatus::Unset,
        }
    }
    
    /// 添加属性
    pub fn with_attribute(mut self, key: String, value: AttributeValue) -> Self {
        self.attributes.insert(key, value);
        self
    }
    
    /// 结束 Span
    pub fn end(mut self) -> Self {
        self.end_time_unix_nano = current_time_nanos();
        self
    }
    
    /// 设置状态
    pub fn with_status(mut self, status: SpanStatus) -> Self {
        self.status = status;
        self
    }
}

/// 生成随机 Trace ID
fn rand_trace_id() -> [u8; 16] {
    use std::time::{SystemTime, UNIX_EPOCH};
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    
    let mut id = [0u8; 16];
    id[0..8].copy_from_slice(&now.to_le_bytes()[0..8]);
    id[8..16].copy_from_slice(&std::process::id().to_le_bytes().repeat(2)[0..8]);
    id
}

/// 生成随机 Span ID
fn rand_span_id() -> [u8; 8] {
    use std::time::{SystemTime, UNIX_EPOCH};
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    
    let mut id = [0u8; 8];
    id.copy_from_slice(&now.to_le_bytes()[0..8]);
    id
}

/// 当前时间 (纳秒)
fn current_time_nanos() -> u64 {
    use std::time::{SystemTime, UNIX_EPOCH};
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos() as u64
}

