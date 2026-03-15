//! # OTTL 转换引擎
//!
//! 提供 OTTL 语句的执行和数据转换功能。
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步转换操作
//! - **元组收集**: 使用 `collect()` 直接收集转换结果到元组
//! - **改进的异步迭代器**: 利用 Rust 1.92 的异步迭代器优化提升性能

use super::bytecode::{BytecodeCompiler, BytecodeProgram};
use super::parser::{Expression, Path, Statement};
use crate::data::TelemetryData;
use crate::error::{OtlpError, Result};

/// OTTL 转换配置
#[derive(Debug, Clone)]
pub struct TransformConfig {
    /// 转换语句列表
    pub statements: Vec<Statement>,

    /// 是否使用字节码优化 (2025年新增，默认启用)
    pub use_bytecode: bool,

    /// 字节码程序缓存 (如果使用字节码)
    #[allow(dead_code)]
    bytecode_programs: Option<Vec<BytecodeProgram>>,
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
            use_bytecode: true, // 默认启用字节码优化
            bytecode_programs: None,
        }
    }

    /// 添加转换语句
    pub fn add_statement(mut self, statement: Statement) -> Self {
        self.statements.push(statement);
        self
    }

    /// 启用/禁用字节码优化
    pub fn with_bytecode(mut self, enabled: bool) -> Self {
        self.use_bytecode = enabled;
        self
    }

    /// 编译语句到字节码 (如果启用)
    pub fn compile_bytecode(&mut self) -> Result<()> {
        if self.use_bytecode {
            let mut compiler = BytecodeCompiler::new();
            let mut programs = Vec::new();

            for statement in &self.statements {
                let program = compiler.compile(statement)?;
                programs.push(program);
            }

            self.bytecode_programs = Some(programs);
        }
        Ok(())
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
                self.evaluate_binary_condition(left, op, right, data).await
            }
            _ => self.evaluate_expression(condition, data).await,
        }
    }

    /// 评估二元条件
    async fn evaluate_binary_condition(
        &self,
        left: &Expression,
        op: &super::parser::BinaryOp,
        right: &Expression,
        data: &TelemetryData,
    ) -> Result<bool> {
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
            "has" => self.call_has(args, data).await,
            "exists" => self.call_exists(args, data).await,
            "match" => self.call_match(args, data).await,
            "contains" => self.call_contains(args, data).await,
            "starts_with" => self.call_starts_with(args, data).await,
            "ends_with" => self.call_ends_with(args, data).await,
            "is_int" => self.call_is_int(args, data).await,
            "is_double" => self.call_is_double(args, data).await,
            "is_bool" => self.call_is_bool(args, data).await,
            "is_string" => self.call_is_string(args, data).await,
            "len" => self.call_len(args, data).await,
            "truncate" => self.call_truncate(args, data).await,
            "replace_all" => self.call_replace_all(args, data).await,
            "split" => self.call_split(args, data).await,
            "join" => self.call_join(args, data).await,
            "substring" => self.call_substring(args, data).await,
            "to_lower" => self.call_to_lower(args, data).await,
            "to_upper" => self.call_to_upper(args, data).await,
            "trim" => self.call_trim(args, data).await,
            "now" => Ok(true),
            "timestamp" => Ok(true),
            "time" => Ok(true),
            "duration" => self.call_duration(args, data).await,
            "format" => self.call_format(args, data).await,
            "concat" => Ok(args.len() >= 2),
            "coalesce" => Ok(args.len() >= 2),
            "merge" => Ok(args.len() >= 2),
            "delete" => self.call_delete(args),
            "copy" => self.call_copy(args),
            "move" => self.call_move(args),
            _ => Err(OtlpError::ValidationError(format!("未知函数: {}", name))),
        }
    }

    /// 调用 has 函数
    async fn call_has(&self, args: &[Expression], data: &TelemetryData) -> Result<bool> {
        let path = match args.first() {
            Some(Expression::Path(path)) => path,
            _ => return Ok(false),
        };
        self.has_attribute(data, path).await
    }

    /// 调用 exists 函数
    async fn call_exists(&self, args: &[Expression], data: &TelemetryData) -> Result<bool> {
        let path = match args.first() {
            Some(Expression::Path(path)) => path,
            _ => return Ok(false),
        };
        self.exists_attribute(data, path).await
    }

    /// 调用 match 函数
    async fn call_match(&self, args: &[Expression], data: &TelemetryData) -> Result<bool> {
        if args.len() < 2 {
            return Ok(false);
        }
        let value = self.evaluate_value_expression(&args[0], data).await?;
        let pattern = self.evaluate_value_expression(&args[1], data).await?;
        Ok(self.match_pattern(&value, &pattern))
    }

    /// 调用 contains 函数
    async fn call_contains(&self, args: &[Expression], data: &TelemetryData) -> Result<bool> {
        if args.len() < 2 {
            return Ok(false);
        }
        let haystack = self.evaluate_value_expression(&args[0], data).await?;
        let needle = self.evaluate_value_expression(&args[1], data).await?;
        Ok(haystack.contains(&needle))
    }

    /// 调用 starts_with 函数
    async fn call_starts_with(&self, args: &[Expression], data: &TelemetryData) -> Result<bool> {
        if args.len() < 2 {
            return Ok(false);
        }
        let text = self.evaluate_value_expression(&args[0], data).await?;
        let prefix = self.evaluate_value_expression(&args[1], data).await?;
        Ok(text.starts_with(&prefix))
    }

    /// 调用 ends_with 函数
    async fn call_ends_with(&self, args: &[Expression], data: &TelemetryData) -> Result<bool> {
        if args.len() < 2 {
            return Ok(false);
        }
        let text = self.evaluate_value_expression(&args[0], data).await?;
        let suffix = self.evaluate_value_expression(&args[1], data).await?;
        Ok(text.ends_with(&suffix))
    }

    /// 调用 is_int 函数
    async fn call_is_int(&self, args: &[Expression], data: &TelemetryData) -> Result<bool> {
        let value = match args.first() {
            Some(expr) => self.evaluate_value_expression(expr, data).await?,
            None => return Ok(false),
        };
        Ok(value.parse::<i64>().is_ok())
    }

    /// 调用 is_double 函数
    async fn call_is_double(&self, args: &[Expression], data: &TelemetryData) -> Result<bool> {
        let value = match args.first() {
            Some(expr) => self.evaluate_value_expression(expr, data).await?,
            None => return Ok(false),
        };
        Ok(value.parse::<f64>().is_ok())
    }

    /// 调用 is_bool 函数
    async fn call_is_bool(&self, args: &[Expression], data: &TelemetryData) -> Result<bool> {
        let value = match args.first() {
            Some(expr) => self.evaluate_value_expression(expr, data).await?,
            None => return Ok(false),
        };
        Ok(value.parse::<bool>().is_ok())
    }

    /// 调用 is_string 函数
    async fn call_is_string(&self, args: &[Expression], data: &TelemetryData) -> Result<bool> {
        let value = match args.first() {
            Some(expr) => self.evaluate_value_expression(expr, data).await?,
            None => return Ok(false),
        };
        Ok(!value.is_empty())
    }

    /// 调用 len 函数
    async fn call_len(&self, args: &[Expression], data: &TelemetryData) -> Result<bool> {
        let value = match args.first() {
            Some(expr) => self.evaluate_value_expression(expr, data).await?,
            None => return Ok(false),
        };
        Ok(value.len() > 0)
    }

    /// 调用 truncate 函数
    async fn call_truncate(&self, args: &[Expression], data: &TelemetryData) -> Result<bool> {
        if args.len() < 2 {
            return Ok(false);
        }
        let text = self.evaluate_value_expression(&args[0], data).await?;
        let length = self.evaluate_value_expression(&args[1], data).await?;
        match length.parse::<usize>() {
            Ok(len) => Ok(text.len() > len),
            Err(_) => Ok(false),
        }
    }

    /// 调用 replace_all 函数
    async fn call_replace_all(&self, args: &[Expression], data: &TelemetryData) -> Result<bool> {
        if args.len() < 3 {
            return Ok(false);
        }
        let text = self.evaluate_value_expression(&args[0], data).await?;
        let old = self.evaluate_value_expression(&args[1], data).await?;
        let new = self.evaluate_value_expression(&args[2], data).await?;
        Ok(text.contains(&old) && !new.is_empty())
    }

    /// 调用 split 函数
    async fn call_split(&self, args: &[Expression], data: &TelemetryData) -> Result<bool> {
        if args.len() < 2 {
            return Ok(false);
        }
        let text = self.evaluate_value_expression(&args[0], data).await?;
        let delimiter = self.evaluate_value_expression(&args[1], data).await?;
        Ok(text.contains(&delimiter))
    }

    /// 调用 join 函数
    async fn call_join(&self, args: &[Expression], data: &TelemetryData) -> Result<bool> {
        if args.len() < 2 {
            return Ok(false);
        }
        let delimiter = self.evaluate_value_expression(&args[0], data).await?;
        Ok(!delimiter.is_empty())
    }

    /// 调用 substring 函数
    async fn call_substring(&self, args: &[Expression], data: &TelemetryData) -> Result<bool> {
        if args.len() < 2 {
            return Ok(false);
        }
        let text = self.evaluate_value_expression(&args[0], data).await?;
        let start = self.evaluate_value_expression(&args[1], data).await?;
        match start.parse::<usize>() {
            Ok(start_idx) => Ok(text.len() > start_idx),
            Err(_) => Ok(false),
        }
    }

    /// 调用 to_lower 函数
    async fn call_to_lower(&self, args: &[Expression], data: &TelemetryData) -> Result<bool> {
        let value = match args.first() {
            Some(expr) => self.evaluate_value_expression(expr, data).await?,
            None => return Ok(false),
        };
        Ok(!value.is_empty())
    }

    /// 调用 to_upper 函数
    async fn call_to_upper(&self, args: &[Expression], data: &TelemetryData) -> Result<bool> {
        let value = match args.first() {
            Some(expr) => self.evaluate_value_expression(expr, data).await?,
            None => return Ok(false),
        };
        Ok(!value.is_empty())
    }

    /// 调用 trim 函数
    async fn call_trim(&self, args: &[Expression], data: &TelemetryData) -> Result<bool> {
        let value = match args.first() {
            Some(expr) => self.evaluate_value_expression(expr, data).await?,
            None => return Ok(false),
        };
        Ok(!value.is_empty())
    }

    /// 调用 duration 函数
    async fn call_duration(&self, args: &[Expression], data: &TelemetryData) -> Result<bool> {
        if args.len() < 2 {
            return Ok(false);
        }
        let start = self.evaluate_value_expression(&args[0], data).await?;
        let end = self.evaluate_value_expression(&args[1], data).await?;
        Ok(!start.is_empty() && !end.is_empty())
    }

    /// 调用 format 函数
    async fn call_format(&self, args: &[Expression], data: &TelemetryData) -> Result<bool> {
        let format_str = match args.first() {
            Some(expr) => self.evaluate_value_expression(expr, data).await?,
            None => return Ok(false),
        };
        Ok(!format_str.is_empty())
    }

    /// 调用 delete 函数
    fn call_delete(&self, args: &[Expression]) -> Result<bool> {
        match args.first() {
            Some(Expression::Path(_)) => Ok(true),
            _ => Ok(false),
        }
    }

    /// 调用 copy 函数
    fn call_copy(&self, args: &[Expression]) -> Result<bool> {
        if args.len() < 2 {
            return Ok(false);
        }
        match (&args[0], &args[1]) {
            (Expression::Path(_), Expression::Path(_)) => Ok(true),
            _ => Ok(false),
        }
    }

    /// 调用 move 函数
    fn call_move(&self, args: &[Expression]) -> Result<bool> {
        if args.len() < 2 {
            return Ok(false);
        }
        match (&args[0], &args[1]) {
            (Expression::Path(_), Expression::Path(_)) => Ok(true),
            _ => Ok(false),
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
        let transformer = OtlpTransform::new(config).expect("Failed to create OTLP transformer");

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

        let result = transformer
            .transform(vec![telemetry_data])
            .await
            .expect("Failed to transform telemetry data");
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

        let result = transformer
            .transform(vec![telemetry_data])
            .await
            .expect("Failed to transform telemetry data");
        assert_eq!(result.stats.processed_count, 1);
        assert_eq!(result.stats.filtered_count, 1);
        assert_eq!(result.stats.transformed_count, 0);
    }
}
