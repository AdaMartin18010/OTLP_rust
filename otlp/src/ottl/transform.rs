//! # OTTL 转换引擎
//!
//! 提供 OTTL 语句的执行和数据转换功能。

use super::parser::{Expression, Path, Statement};
use crate::data::TelemetryData;
use crate::error::{OtlpError, Result};

/// OTTL 转换配置
#[derive(Debug, Clone)]
pub struct TransformConfig {
    /// 转换语句列表
    pub statements: Vec<Statement>,
}

impl Default for TransformConfig {
    fn default() -> Self {
        Self::new()
    }
}

impl TransformConfig {
    /// 创建新的转换配置
    pub fn new() -> Self {
        Self {
            statements: Vec::new(),
        }
    }

    /// 添加转换语句
    pub fn add_statement(mut self, statement: Statement) -> Self {
        self.statements.push(statement);
        self
    }
}

/// OTTL 转换器
pub struct OtlpTransform {
    config: TransformConfig,
}

/// 转换结果
#[derive(Debug, Clone)]
pub struct TransformResult {
    /// 转换后的数据
    pub data: Vec<TelemetryData>,
    /// 转换统计
    pub stats: TransformStats,
}

/// 转换统计
#[derive(Debug, Clone)]
pub struct TransformStats {
    /// 处理的数据条数
    pub processed_count: usize,
    /// 过滤的数据条数
    pub filtered_count: usize,
    /// 转换的数据条数
    pub transformed_count: usize,
}

impl OtlpTransform {
    /// 创建新的转换器
    pub fn new(config: TransformConfig) -> Result<Self> {
        Ok(Self { config })
    }

    /// 转换遥测数据
    pub async fn transform(&self, data: Vec<TelemetryData>) -> Result<TransformResult> {
        let mut result_data = Vec::new();
        let mut processed_count = 0;
        let mut filtered_count = 0;
        let mut transformed_count = 0;

        for telemetry_data in data {
            processed_count += 1;

            // 应用转换语句
            if let Some(transformed_data) = self.apply_statements(telemetry_data).await? {
                result_data.push(transformed_data);
                transformed_count += 1;
            } else {
                filtered_count += 1;
            }
        }

        Ok(TransformResult {
            data: result_data,
            stats: TransformStats {
                processed_count,
                filtered_count,
                transformed_count,
            },
        })
    }

    /// 应用转换语句
    async fn apply_statements(&self, mut data: TelemetryData) -> Result<Option<TelemetryData>> {
        for statement in &self.config.statements {
            match statement {
                Statement::Where { condition } => {
                    // 检查条件，如果不满足则过滤掉
                    if !self.evaluate_condition(condition, &data).await? {
                        return Ok(None);
                    }
                }
                Statement::Set { path, value } => {
                    // 设置属性值
                    self.set_attribute(&mut data, path, value).await?;
                }
                Statement::KeepKeys { path, keys } => {
                    // 保留指定的键
                    self.keep_keys(&mut data, path, keys).await?;
                }
                Statement::Limit { path, count } => {
                    // 限制数组长度
                    self.limit_array(&mut data, path, count).await?;
                }
                Statement::Convert { path, target_type } => {
                    // 转换数据类型
                    self.convert_type(&mut data, path, target_type).await?;
                }
                Statement::Route { path, destinations } => {
                    // 路由数据（简化实现）
                    self.route_data(&mut data, path, destinations).await?;
                }
            }
        }

        Ok(Some(data))
    }

    /// 评估条件表达式
    async fn evaluate_condition(
        &self,
        condition: &Expression,
        data: &TelemetryData,
    ) -> Result<bool> {
        match condition {
            Expression::Binary { left, op, right } => {
                let left_val = self.evaluate_expression(left, data).await?;
                let right_val = self.evaluate_expression(right, data).await?;

                match op {
                    super::parser::BinaryOp::Eq => Ok(left_val == right_val),
                    super::parser::BinaryOp::Ne => Ok(left_val != right_val),
                    super::parser::BinaryOp::Lt => Ok(!left_val & right_val),
                    super::parser::BinaryOp::Le => Ok(left_val <= right_val),
                    super::parser::BinaryOp::Gt => Ok(left_val & !right_val),
                    super::parser::BinaryOp::Ge => Ok(left_val >= right_val),
                    super::parser::BinaryOp::And => Ok(left_val && right_val),
                    super::parser::BinaryOp::Or => Ok(left_val || right_val),
                    _ => Err(OtlpError::ValidationError("不支持的比较操作".to_string())),
                }
            }
            _ => {
                let result = self.evaluate_expression(condition, data).await?;
                Ok(result)
            }
        }
    }

    /// 评估表达式
    async fn evaluate_expression(&self, expr: &Expression, data: &TelemetryData) -> Result<bool> {
        match expr {
            Expression::Literal(literal) => match literal {
                super::parser::Literal::Bool(b) => Ok(*b),
                _ => Err(OtlpError::ValidationError("期望布尔值".to_string())),
            },
            Expression::Path(path) => {
                let value = self.get_attribute_value(data, path).await?;
                Ok(value)
            }
            Expression::FunctionCall { name, args } => self.call_function(name, args, data).await,
            _ => Err(OtlpError::ValidationError("不支持的表达式类型".to_string())),
        }
    }

    /// 获取属性值
    async fn get_attribute_value(&self, data: &TelemetryData, path: &Path) -> Result<bool> {
        match path {
            Path::ResourceAttribute { key } => {
                let value = data
                    .resource_attributes
                    .get(key)
                    .map(|v| v.to_string())
                    .unwrap_or_default();
                Ok(!value.is_empty())
            }
            Path::ScopeAttribute { key } => {
                let value = data
                    .scope_attributes
                    .get(key)
                    .map(|v| v.to_string())
                    .unwrap_or_default();
                Ok(!value.is_empty())
            }
            _ => Ok(false),
        }
    }

    /// 设置属性值
    async fn set_attribute(
        &self,
        data: &mut TelemetryData,
        path: &Path,
        value: &Expression,
    ) -> Result<()> {
        match path {
            Path::ResourceAttribute { key } => {
                let val = self.evaluate_value_expression(value, data).await?;
                data.resource_attributes.insert(key.clone(), val);
            }
            Path::ScopeAttribute { key } => {
                let val = self.evaluate_value_expression(value, data).await?;
                data.scope_attributes.insert(key.clone(), val);
            }
            _ => return Err(OtlpError::ValidationError("不支持的路径类型".to_string())),
        }
        Ok(())
    }

    /// 评估值表达式
    async fn evaluate_value_expression(
        &self,
        expr: &Expression,
        _data: &TelemetryData,
    ) -> Result<String> {
        match expr {
            Expression::Literal(literal) => match literal {
                super::parser::Literal::String(s) => Ok(s.clone()),
                super::parser::Literal::Int(i) => Ok(i.to_string()),
                super::parser::Literal::Float(f) => Ok(f.to_string()),
                super::parser::Literal::Bool(b) => Ok(b.to_string()),
                _ => Err(OtlpError::ValidationError("不支持的字面量类型".to_string())),
            },
            _ => Err(OtlpError::ValidationError("不支持的表达式类型".to_string())),
        }
    }

    /// 保留键
    async fn keep_keys(
        &self,
        _data: &mut TelemetryData,
        _path: &Path,
        _keys: &[Expression],
    ) -> Result<()> {
        // 简化实现
        Ok(())
    }

    /// 限制数组长度
    async fn limit_array(
        &self,
        _data: &mut TelemetryData,
        _path: &Path,
        _count: &Expression,
    ) -> Result<()> {
        // 简化实现
        Ok(())
    }

    /// 转换数据类型
    async fn convert_type(
        &self,
        _data: &mut TelemetryData,
        _path: &Path,
        _target_type: &str,
    ) -> Result<()> {
        // 简化实现
        Ok(())
    }

    /// 路由数据
    async fn route_data(
        &self,
        _data: &mut TelemetryData,
        _path: &Path,
        _destinations: &[Expression],
    ) -> Result<()> {
        // 简化实现
        Ok(())
    }

    /// 调用函数
    async fn call_function(
        &self,
        name: &str,
        args: &[Expression],
        data: &TelemetryData,
    ) -> Result<bool> {
        match name {
            "has" => {
                if let Some(path_expr) = args.first() {
                    if let Expression::Path(path) = path_expr {
                        self.has_attribute(data, path).await
                    } else {
                        Ok(false)
                    }
                } else {
                    Ok(false)
                }
            }
            "exists" => {
                if let Some(path_expr) = args.first() {
                    if let Expression::Path(path) = path_expr {
                        self.exists_attribute(data, path).await
                    } else {
                        Ok(false)
                    }
                } else {
                    Ok(false)
                }
            }
            "match" => {
                if args.len() >= 2 {
                    let value = self.evaluate_value_expression(&args[0], data).await?;
                    let pattern = self.evaluate_value_expression(&args[1], data).await?;
                    Ok(self.match_pattern(&value, &pattern))
                } else {
                    Ok(false)
                }
            }
            "contains" => {
                if args.len() >= 2 {
                    let haystack = self.evaluate_value_expression(&args[0], data).await?;
                    let needle = self.evaluate_value_expression(&args[1], data).await?;
                    Ok(haystack.contains(&needle))
                } else {
                    Ok(false)
                }
            }
            "starts_with" => {
                if args.len() >= 2 {
                    let text = self.evaluate_value_expression(&args[0], data).await?;
                    let prefix = self.evaluate_value_expression(&args[1], data).await?;
                    Ok(text.starts_with(&prefix))
                } else {
                    Ok(false)
                }
            }
            "ends_with" => {
                if args.len() >= 2 {
                    let text = self.evaluate_value_expression(&args[0], data).await?;
                    let suffix = self.evaluate_value_expression(&args[1], data).await?;
                    Ok(text.ends_with(&suffix))
                } else {
                    Ok(false)
                }
            }
            "is_int" => {
                if let Some(value_expr) = args.first() {
                    let value = self.evaluate_value_expression(value_expr, data).await?;
                    Ok(value.parse::<i64>().is_ok())
                } else {
                    Ok(false)
                }
            }
            "is_double" => {
                if let Some(value_expr) = args.first() {
                    let value = self.evaluate_value_expression(value_expr, data).await?;
                    Ok(value.parse::<f64>().is_ok())
                } else {
                    Ok(false)
                }
            }
            "is_bool" => {
                if let Some(value_expr) = args.first() {
                    let value = self.evaluate_value_expression(value_expr, data).await?;
                    Ok(value.parse::<bool>().is_ok())
                } else {
                    Ok(false)
                }
            }
            "is_string" => {
                if let Some(value_expr) = args.first() {
                    let value = self.evaluate_value_expression(value_expr, data).await?;
                    Ok(!value.is_empty())
                } else {
                    Ok(false)
                }
            }
            "len" => {
                if let Some(value_expr) = args.first() {
                    let value = self.evaluate_value_expression(value_expr, data).await?;
                    Ok(value.len() > 0)
                } else {
                    Ok(false)
                }
            }
            "truncate" => {
                if args.len() >= 2 {
                    let text = self.evaluate_value_expression(&args[0], data).await?;
                    let length = self.evaluate_value_expression(&args[1], data).await?;
                    if let Ok(len) = length.parse::<usize>() {
                        Ok(text.len() > len)
                    } else {
                        Ok(false)
                    }
                } else {
                    Ok(false)
                }
            }
            "replace_all" => {
                if args.len() >= 3 {
                    let text = self.evaluate_value_expression(&args[0], data).await?;
                    let old = self.evaluate_value_expression(&args[1], data).await?;
                    let new = self.evaluate_value_expression(&args[2], data).await?;
                    Ok(text.contains(&old) && !new.is_empty())
                } else {
                    Ok(false)
                }
            }
            "split" => {
                if args.len() >= 2 {
                    let text = self.evaluate_value_expression(&args[0], data).await?;
                    let delimiter = self.evaluate_value_expression(&args[1], data).await?;
                    Ok(text.contains(&delimiter))
                } else {
                    Ok(false)
                }
            }
            "join" => {
                if args.len() >= 2 {
                    let delimiter = self.evaluate_value_expression(&args[0], data).await?;
                    Ok(!delimiter.is_empty())
                } else {
                    Ok(false)
                }
            }
            "substring" => {
                if args.len() >= 2 {
                    let text = self.evaluate_value_expression(&args[0], data).await?;
                    let start = self.evaluate_value_expression(&args[1], data).await?;
                    if let Ok(start_idx) = start.parse::<usize>() {
                        Ok(text.len() > start_idx)
                    } else {
                        Ok(false)
                    }
                } else {
                    Ok(false)
                }
            }
            "to_lower" => {
                if let Some(value_expr) = args.first() {
                    let value = self.evaluate_value_expression(value_expr, data).await?;
                    Ok(!value.is_empty())
                } else {
                    Ok(false)
                }
            }
            "to_upper" => {
                if let Some(value_expr) = args.first() {
                    let value = self.evaluate_value_expression(value_expr, data).await?;
                    Ok(!value.is_empty())
                } else {
                    Ok(false)
                }
            }
            "trim" => {
                if let Some(value_expr) = args.first() {
                    let value = self.evaluate_value_expression(value_expr, data).await?;
                    Ok(!value.is_empty())
                } else {
                    Ok(false)
                }
            }
            "now" => Ok(true),       // 当前时间总是存在
            "timestamp" => Ok(true), // 时间戳总是存在
            "time" => Ok(true),      // 时间总是存在
            "duration" => {
                if args.len() >= 2 {
                    let start = self.evaluate_value_expression(&args[0], data).await?;
                    let end = self.evaluate_value_expression(&args[1], data).await?;
                    Ok(!start.is_empty() && !end.is_empty())
                } else {
                    Ok(false)
                }
            }
            "format" => {
                if let Some(format_expr) = args.first() {
                    let format_str = self.evaluate_value_expression(format_expr, data).await?;
                    Ok(!format_str.is_empty())
                } else {
                    Ok(false)
                }
            }
            "concat" => {
                Ok(args.len() >= 2) // 至少需要两个参数
            }
            "coalesce" => {
                Ok(args.len() >= 2) // 至少需要两个参数
            }
            "merge" => {
                Ok(args.len() >= 2) // 至少需要两个参数
            }
            "delete" => {
                if let Some(path_expr) = args.first() {
                    if let Expression::Path(_) = path_expr {
                        Ok(true)
                    } else {
                        Ok(false)
                    }
                } else {
                    Ok(false)
                }
            }
            "copy" => {
                if args.len() >= 2 {
                    if let Expression::Path(_) = &args[0] {
                        if let Expression::Path(_) = &args[1] {
                            Ok(true)
                        } else {
                            Ok(false)
                        }
                    } else {
                        Ok(false)
                    }
                } else {
                    Ok(false)
                }
            }
            "move" => {
                if args.len() >= 2 {
                    if let Expression::Path(_) = &args[0] {
                        if let Expression::Path(_) = &args[1] {
                            Ok(true)
                        } else {
                            Ok(false)
                        }
                    } else {
                        Ok(false)
                    }
                } else {
                    Ok(false)
                }
            }
            _ => Err(OtlpError::ValidationError(format!("未知函数: {}", name))),
        }
    }

    /// 检查属性是否存在
    async fn has_attribute(&self, data: &TelemetryData, path: &Path) -> Result<bool> {
        match path {
            Path::ResourceAttribute { key } => Ok(data.resource_attributes.contains_key(key)),
            Path::ScopeAttribute { key } => Ok(data.scope_attributes.contains_key(key)),
            _ => Ok(false),
        }
    }

    /// 检查属性是否存在且不为空
    async fn exists_attribute(&self, data: &TelemetryData, path: &Path) -> Result<bool> {
        match path {
            Path::ResourceAttribute { key } => {
                if let Some(value) = data.resource_attributes.get(key) {
                    Ok(!value.to_string().is_empty())
                } else {
                    Ok(false)
                }
            }
            Path::ScopeAttribute { key } => {
                if let Some(value) = data.scope_attributes.get(key) {
                    Ok(!value.to_string().is_empty())
                } else {
                    Ok(false)
                }
            }
            _ => Ok(false),
        }
    }

    /// 模式匹配
    fn match_pattern(&self, value: &str, pattern: &str) -> bool {
        // 简单的通配符匹配实现
        if pattern.contains('*') {
            self.wildcard_match(value, pattern)
        } else if pattern.contains('?') {
            self.single_char_match(value, pattern)
        } else {
            value == pattern
        }
    }

    /// 通配符匹配
    fn wildcard_match(&self, value: &str, pattern: &str) -> bool {
        let pattern_chars: Vec<char> = pattern.chars().collect();
        let value_chars: Vec<char> = value.chars().collect();

        let mut pattern_idx = 0;
        let mut value_idx = 0;
        let mut star_idx = None;
        let mut match_idx = 0;

        while value_idx < value_chars.len() {
            if pattern_idx < pattern_chars.len()
                && (pattern_chars[pattern_idx] == '?'
                    || pattern_chars[pattern_idx] == value_chars[value_idx])
            {
                pattern_idx += 1;
                value_idx += 1;
            } else if pattern_idx < pattern_chars.len() && pattern_chars[pattern_idx] == '*' {
                star_idx = Some(pattern_idx);
                match_idx = value_idx;
                pattern_idx += 1;
            } else if let Some(star) = star_idx {
                pattern_idx = star + 1;
                match_idx += 1;
                value_idx = match_idx;
            } else {
                return false;
            }
        }

        while pattern_idx < pattern_chars.len() && pattern_chars[pattern_idx] == '*' {
            pattern_idx += 1;
        }

        pattern_idx == pattern_chars.len()
    }

    /// 单字符匹配
    fn single_char_match(&self, value: &str, pattern: &str) -> bool {
        if value.len() != pattern.len() {
            return false;
        }

        for (v_char, p_char) in value.chars().zip(pattern.chars()) {
            if p_char != '?' && p_char != v_char {
                return false;
            }
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::{
        SpanKind, SpanStatus, TelemetryContent, TelemetryData, TelemetryDataType, TraceData,
    };
    use std::collections::HashMap;

    #[tokio::test]
    async fn test_simple_transform() {
        let config = TransformConfig::new();
        let transformer = OtlpTransform::new(config)
            .expect("Failed to create OTLP transformer");

        let trace_data = TraceData {
            trace_id: "12345678901234567890123456789012".to_string(),
            span_id: "1234567890123456".to_string(),
            parent_span_id: None,
            name: "test-span".to_string(),
            span_kind: SpanKind::Internal,
            start_time: 1000,
            end_time: 2000,
            status: SpanStatus::default(),
            attributes: HashMap::new(),
            events: vec![],
            links: vec![],
        };

        let telemetry_data = TelemetryData {
            data_type: TelemetryDataType::Trace,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("System time should be after UNIX_EPOCH")
                .as_nanos() as u64,
            resource_attributes: HashMap::new(),
            scope_attributes: HashMap::new(),
            content: TelemetryContent::Trace(trace_data),
        };

        let result = transformer.transform(vec![telemetry_data]).await.expect("Failed to transform telemetry data");
        assert_eq!(result.stats.processed_count, 1);
        assert_eq!(result.stats.transformed_count, 1);
    }

    #[tokio::test]
    async fn test_where_filter() {
        use super::super::parser::{Expression, Literal, Statement};

        let config = TransformConfig::new().add_statement(Statement::Where {
            condition: Expression::Literal(Literal::Bool(false)),
        });

        let transformer = OtlpTransform::new(config)
            .expect("Failed to create OTLP transformer for filtering test");

        let trace_data = TraceData {
            trace_id: "12345678901234567890123456789012".to_string(),
            span_id: "1234567890123456".to_string(),
            parent_span_id: None,
            name: "test-span".to_string(),
            span_kind: SpanKind::Internal,
            start_time: 1000,
            end_time: 2000,
            status: SpanStatus::default(),
            attributes: HashMap::new(),
            events: vec![],
            links: vec![],
        };

        let telemetry_data = TelemetryData {
            data_type: TelemetryDataType::Trace,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("System time should be after UNIX_EPOCH")
                .as_nanos() as u64,
            resource_attributes: HashMap::new(),
            scope_attributes: HashMap::new(),
            content: TelemetryContent::Trace(trace_data),
        };

        let result = transformer.transform(vec![telemetry_data]).await
            .expect("Failed to transform telemetry data");
        assert_eq!(result.stats.processed_count, 1);
        assert_eq!(result.stats.filtered_count, 1);
        assert_eq!(result.stats.transformed_count, 0);
    }
}
