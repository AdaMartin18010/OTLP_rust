//! # OTTL (OpenTelemetry Transformation Language) Processor
//!
//! Implementation of OpenTelemetry Transformation Language for flexible
//! telemetry data processing within the OTLP pipeline.
//!
//! ## Specification
//!
//! Based on OTTL v1.0 specification:
//! - <https://opentelemetry.io/docs/specs/otel/ottl/>
//!
//! ## Features
//!
//! - **Statement Parsing**: Parse OTTL statements into executable AST
//! - **Context-aware**: Access span, metric, log, and resource attributes
//! - **Functions**: Built-in functions for common transformations
//! - **Editors**: Modify telemetry data in-place
//! - **Conditions**: Conditional statement execution
//!
//! ## Example OTTL Statements
//!
//! ```ottl
//! # Set attribute
//! set(attributes["service.name"], "my-service")
//!
//! # Delete attribute
//! delete_key(attributes, "temp_attr")
//!
//! # Conditional
//! set(attributes["high_latency"], true) where span.duration > 1000
//!
//! # Function call
//! set(attributes["timestamp_formatted"], FormatTime(span.start_time))
//! ```

use crate::error::{OtlpError, Result};
use std::collections::HashMap;

/// OTTL Statement types
#[derive(Debug, Clone, PartialEq)]
pub enum OttlStatement {
    /// Set statement: set(path, value)
    Set { path: OttlPath, value: OttlValue },
    
    /// Delete key statement: delete_key(map, key)
    DeleteKey { map: OttlPath, key: String },
    
    /// Keep keys statement: `keep_keys(map, [keys])`
    KeepKeys { map: OttlPath, keys: Vec<String> },
    
    /// Function call statement
    Call { function: String, args: Vec<OttlValue> },
}

/// OTTL Path expression
#[derive(Debug, Clone, PartialEq)]
pub enum OttlPath {
    /// Simple identifier
    Identifier(String),
    
    /// Map access: attributes["key"]
    MapAccess { base: Box<OttlPath>, key: String },
    
    /// Field access: span.name
    FieldAccess { base: Box<OttlPath>, field: String },
}

/// OTTL Value types
#[derive(Debug, Clone, PartialEq)]
pub enum OttlValue {
    /// String literal
    String(String),
    
    /// Integer literal
    Int(i64),
    
    /// Float literal
    Float(f64),
    
    /// Boolean literal
    Bool(bool),
    
    /// Path reference
    Path(OttlPath),
    
    /// Function call
    FunctionCall { name: String, args: Vec<OttlValue> },
}

/// OTTL Condition for WHERE clauses
#[derive(Debug, Clone, PartialEq)]
pub enum OttlCondition {
    /// Comparison: ==, !=, <, >, <=, >=
    Comparison {
        left: OttlValue,
        op: ComparisonOp,
        right: OttlValue,
    },
    
    /// Logical AND
    And(Box<OttlCondition>, Box<OttlCondition>),
    
    /// Logical OR
    Or(Box<OttlCondition>, Box<OttlCondition>),
    
    /// Logical NOT
    Not(Box<OttlCondition>),
}

/// Comparison operators
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ComparisonOp {
    Eq,  // ==
    Ne,  // !=
    Lt,  // <
    Gt,  // >
    Le,  // <=
    Ge,  // >=
}

/// OTTL Parser
pub struct OttlParser;

impl OttlParser {
    /// Parse an OTTL statement string
    pub fn parse(statement: &str) -> Result<OttlStatement> {
        // Simplified parser - in production would use proper grammar parser
        let trimmed = statement.trim();
        
        if trimmed.starts_with("set(") {
            Self::parse_set(trimmed)
        } else if trimmed.starts_with("delete_key(") {
            Self::parse_delete_key(trimmed)
        } else {
            Err(OtlpError::ValidationError(format!(
                "Unknown OTTL statement: {}",
                statement
            )))
        }
    }
    
    fn parse_set(statement: &str) -> Result<OttlStatement> {
        // Simplified: set(path, value)
        let inner = statement
            .trim_start_matches("set(")
            .trim_end_matches(")");
        
        let parts: Vec<&str> = inner.splitn(2, ',').collect();
        if parts.len() != 2 {
            return Err(OtlpError::ValidationError(
                "Invalid set statement: expected set(path, value)".to_string()
            ));
        }
        
        let path = Self::parse_path(parts[0].trim())?;
        let value = Self::parse_value(parts[1].trim())?;
        
        Ok(OttlStatement::Set { path, value })
    }
    
    fn parse_delete_key(statement: &str) -> Result<OttlStatement> {
        // Simplified: delete_key(map, "key")
        let inner = statement
            .trim_start_matches("delete_key(")
            .trim_end_matches(")");
        
        let parts: Vec<&str> = inner.splitn(2, ',').collect();
        if parts.len() != 2 {
            return Err(OtlpError::ValidationError(
                "Invalid delete_key statement: expected delete_key(map, key)".to_string()
            ));
        }
        
        let map = Self::parse_path(parts[0].trim())?;
        let key = Self::parse_string(parts[1].trim())?;
        
        Ok(OttlStatement::DeleteKey { map, key })
    }
    
    fn parse_path(s: &str) -> Result<OttlPath> {
        if s.contains("[") && s.contains("]") {
            // Map access: attributes["key"]
            let parts: Vec<&str> = s.splitn(2, '[').collect();
            let base = OttlPath::Identifier(parts[0].to_string());
            let key = parts[1].trim().trim_end_matches("]").trim_matches('"').to_string();
            Ok(OttlPath::MapAccess {
                base: Box::new(base),
                key,
            })
        } else if s.contains(".") {
            // Field access: span.name
            let parts: Vec<&str> = s.splitn(2, '.').collect();
            let base = OttlPath::Identifier(parts[0].to_string());
            let field = parts[1].to_string();
            Ok(OttlPath::FieldAccess {
                base: Box::new(base),
                field,
            })
        } else {
            Ok(OttlPath::Identifier(s.to_string()))
        }
    }
    
    fn parse_value(s: &str) -> Result<OttlValue> {
        if s.starts_with('"') && s.ends_with('"') {
            Ok(OttlValue::String(s.trim_matches('"').to_string()))
        } else if s == "true" {
            Ok(OttlValue::Bool(true))
        } else if s == "false" {
            Ok(OttlValue::Bool(false))
        } else if let Ok(n) = s.parse::<i64>() {
            Ok(OttlValue::Int(n))
        } else if let Ok(n) = s.parse::<f64>() {
            Ok(OttlValue::Float(n))
        } else {
            // Assume it's a path
            Ok(OttlValue::Path(Self::parse_path(s)?))
        }
    }
    
    fn parse_string(s: &str) -> Result<String> {
        Ok(s.trim().trim_matches('"').to_string())
    }
    
    /// Parse a WHERE condition
    pub fn parse_condition(condition_str: &str) -> Result<OttlCondition> {
        let trimmed = condition_str.trim();
        
        // 处理括号
        if trimmed.starts_with('(') && trimmed.ends_with(')') {
            return Self::parse_condition(&trimmed[1..trimmed.len()-1]);
        }
        
        // 处理逻辑运算符
        if let Some(pos) = Self::find_operator(trimmed, " and ") {
            let left = &trimmed[..pos];
            let right = &trimmed[pos + 5..];
            return Ok(OttlCondition::And(
                Box::new(Self::parse_condition(left)?),
                Box::new(Self::parse_condition(right)?)
            ));
        }
        
        if let Some(pos) = Self::find_operator(trimmed, " or ") {
            let left = &trimmed[..pos];
            let right = &trimmed[pos + 4..];
            return Ok(OttlCondition::Or(
                Box::new(Self::parse_condition(left)?),
                Box::new(Self::parse_condition(right)?)
            ));
        }
        
        if let Some(inner) = trimmed.strip_prefix("not ") {
            return Ok(OttlCondition::Not(Box::new(Self::parse_condition(inner)?)));
        }
        
        // 处理比较运算符
        Self::parse_comparison(trimmed)
    }
    
    fn find_operator(s: &str, op: &str) -> Option<usize> {
        let mut depth = 0;
        for (i, c) in s.char_indices() {
            match c {
                '(' => depth += 1,
                ')' => depth -= 1,
                _ if depth == 0 => {
                    if s[i..].starts_with(op) {
                        return Some(i);
                    }
                }
                _ => {}
            }
        }
        None
    }
    
    fn parse_comparison(s: &str) -> Result<OttlCondition> {
        let ops = [
            ("==", ComparisonOp::Eq),
            ("!=", ComparisonOp::Ne),
            ("<=", ComparisonOp::Le),
            (">=", ComparisonOp::Ge),
            ("<", ComparisonOp::Lt),
            (">", ComparisonOp::Gt),
        ];
        
        for (op_str, op) in &ops {
            if let Some(pos) = s.find(op_str) {
                let left = s[..pos].trim();
                let right = &s[pos + op_str.len()..].trim();
                
                return Ok(OttlCondition::Comparison {
                    left: Self::parse_value(left)?,
                    op: *op,
                    right: Self::parse_value(right)?,
                });
            }
        }
        
        Err(crate::error::OtlpError::ValidationError(
            format!("Invalid condition: {}", s)
        ))
    }
}

/// OTTL Execution Context
pub struct OttlContext<'a> {
    /// Resource attributes
    pub resource_attributes: &'a mut HashMap<String, String>,
    
    /// Span attributes (if processing spans)
    pub span_attributes: Option<&'a mut HashMap<String, String>>,
    
    /// Metric attributes (if processing metrics)
    pub metric_attributes: Option<&'a mut HashMap<String, String>>,
    
    /// Log attributes (if processing logs)
    pub log_attributes: Option<&'a mut HashMap<String, String>>,
}

/// OTTL Processor
pub struct OttlProcessor {
    statements: Vec<(OttlStatement, Option<OttlCondition>)>,
}

impl OttlProcessor {
    /// Create a new OTTL processor
    pub fn new() -> Self {
        Self {
            statements: Vec::new(),
        }
    }
    
    /// Add a statement with optional condition
    pub fn add_statement(&mut self, statement: OttlStatement, condition: Option<OttlCondition>) {
        self.statements.push((statement, condition));
    }
    
    /// Parse and add a statement from string
    pub fn parse_and_add(&mut self, statement_str: &str) -> Result<()> {
        let statement = OttlParser::parse(statement_str)?;
        self.add_statement(statement, None);
        Ok(())
    }
    
    /// Parse and add a statement with WHERE condition
    pub fn parse_and_add_with_condition(&mut self, statement_str: &str, condition_str: &str) -> Result<()> {
        let statement = OttlParser::parse(statement_str)?;
        let condition = OttlParser::parse_condition(condition_str)?;
        self.add_statement(statement, Some(condition));
        Ok(())
    }
    
    /// Execute all statements in the context
    pub fn execute(&self, ctx: &mut OttlContext) -> Result<()> {
        for (statement, condition) in &self.statements {
            self.execute_statement_with_condition(statement, condition, ctx)?;
        }
        Ok(())
    }

    /// Execute a single statement with optional condition
    fn execute_statement_with_condition(
        &self,
        statement: &OttlStatement,
        condition: &Option<OttlCondition>,
        ctx: &mut OttlContext,
    ) -> Result<()> {
        if let Some(cond) = condition
            && !self.evaluate_condition(cond, ctx)?
        {
            return Ok(());
        }
        self.execute_statement(statement, ctx)
    }
    
    fn execute_statement(&self, statement: &OttlStatement, ctx: &mut OttlContext) -> Result<()> {
        match statement {
            OttlStatement::Set { path, value } => {
                self.execute_set(path, value, ctx)?;
            }
            OttlStatement::DeleteKey { map, key } => {
                self.execute_delete_key(map, key, ctx)?;
            }
            OttlStatement::KeepKeys { map, keys } => {
                self.execute_keep_keys(map, keys, ctx)?;
            }
            OttlStatement::Call { function, args } => {
                self.execute_call(function, args, ctx)?;
            }
        }
        
        Ok(())
    }
    
    fn execute_set(&self, path: &OttlPath, value: &OttlValue, ctx: &mut OttlContext) -> Result<()> {
        let value_str = self.value_to_string(value, ctx)?;
        self.apply_set_value(path, value_str, ctx);
        Ok(())
    }

    fn apply_set_value(&self, path: &OttlPath, value_str: String, ctx: &mut OttlContext) {
        match path {
            OttlPath::Identifier(name) => {
                ctx.resource_attributes.insert(name.clone(), value_str);
            }
            OttlPath::MapAccess { base, key } => {
                self.set_span_attribute(base, key, value_str, ctx);
            }
            _ => {}
        }
    }

    fn set_span_attribute(
        &self,
        base: &OttlPath,
        key: &str,
        value_str: String,
        ctx: &mut OttlContext,
    ) {
        let OttlPath::Identifier(base_name) = base else { return };
        if base_name != "attributes" { return }
        
        if let Some(ref mut attrs) = ctx.span_attributes {
            attrs.insert(key.to_string(), value_str);
        }
    }
    
    fn execute_delete_key(&self, map: &OttlPath, key: &str, ctx: &mut OttlContext) -> Result<()> {
        let name = match map {
            OttlPath::Identifier(name) => name,
            _ => return Ok(()),
        };
        
        if name != "attributes" {
            return Ok(());
        }
        
        if let Some(ref mut attrs) = ctx.span_attributes {
            attrs.remove(key);
        }
        Ok(())
    }
    
    fn execute_keep_keys(&self, _map: &OttlPath, _keys: &[String], _ctx: &mut OttlContext) -> Result<()> {
        // Simplified implementation
        Ok(())
    }
    
    fn execute_call(&self, _function: &str, _args: &[OttlValue], _ctx: &mut OttlContext) -> Result<()> {
        // Simplified implementation
        Ok(())
    }
    
    fn evaluate_condition(&self, condition: &OttlCondition, ctx: &OttlContext) -> Result<bool> {
        match condition {
            OttlCondition::Comparison { left, op, right } => {
                self.evaluate_comparison(left, op, right, ctx)
            }
            OttlCondition::And(left, right) => self.evaluate_and(left, right, ctx),
            OttlCondition::Or(left, right) => self.evaluate_or(left, right, ctx),
            OttlCondition::Not(cond) => self.evaluate_not(cond, ctx),
        }
    }

    fn evaluate_comparison(
        &self,
        left: &OttlValue,
        op: &ComparisonOp,
        right: &OttlValue,
        ctx: &OttlContext,
    ) -> Result<bool> {
        let left_val = self.value_to_string(left, ctx)?;
        let right_val = self.value_to_string(right, ctx)?;
        
        // 尝试数值比较
        if let (Ok(left_num), Ok(right_num)) = (left_val.parse::<f64>(), right_val.parse::<f64>()) {
            return self.compare_numeric(left_num, op, right_num);
        }
        
        // 字符串比较
        self.compare_string(&left_val, op, &right_val)
    }

    fn compare_numeric(&self, left: f64, op: &ComparisonOp, right: f64) -> Result<bool> {
        match op {
            ComparisonOp::Eq => Ok((left - right).abs() < f64::EPSILON),
            ComparisonOp::Ne => Ok((left - right).abs() >= f64::EPSILON),
            ComparisonOp::Lt => Ok(left < right),
            ComparisonOp::Gt => Ok(left > right),
            ComparisonOp::Le => Ok(left <= right),
            ComparisonOp::Ge => Ok(left >= right),
        }
    }

    fn compare_string(&self, left: &str, op: &ComparisonOp, right: &str) -> Result<bool> {
        match op {
            ComparisonOp::Eq => Ok(left == right),
            ComparisonOp::Ne => Ok(left != right),
            ComparisonOp::Lt => Ok(left < right),
            ComparisonOp::Gt => Ok(left > right),
            ComparisonOp::Le => Ok(left <= right),
            ComparisonOp::Ge => Ok(left >= right),
        }
    }

    fn evaluate_and(
        &self,
        left: &OttlCondition,
        right: &OttlCondition,
        ctx: &OttlContext,
    ) -> Result<bool> {
        Ok(self.evaluate_condition(left, ctx)? && self.evaluate_condition(right, ctx)?)
    }

    fn evaluate_or(
        &self,
        left: &OttlCondition,
        right: &OttlCondition,
        ctx: &OttlContext,
    ) -> Result<bool> {
        Ok(self.evaluate_condition(left, ctx)? || self.evaluate_condition(right, ctx)?)
    }

    fn evaluate_not(&self, cond: &OttlCondition, ctx: &OttlContext) -> Result<bool> {
        Ok(!self.evaluate_condition(cond, ctx)?)
    }
    
    fn value_to_string(&self, value: &OttlValue, ctx: &OttlContext) -> Result<String> {
        match value {
            OttlValue::String(s) => Ok(s.clone()),
            OttlValue::Int(n) => Ok(n.to_string()),
            OttlValue::Float(n) => Ok(n.to_string()),
            OttlValue::Bool(b) => Ok(b.to_string()),
            OttlValue::Path(path) => self.resolve_path(path, ctx),
            OttlValue::FunctionCall { .. } => Ok("".to_string()), // Simplified
        }
    }
    
    /// Resolve an OTTL path to its value from the context
    fn resolve_path(&self, path: &OttlPath, ctx: &OttlContext) -> Result<String> {
        match path {
            OttlPath::Identifier(name) => {
                // Try span attributes first, then resource attributes
                if let Some(span_attrs) = &ctx.span_attributes
                    && let Some(val) = span_attrs.get(name)
                {
                    return Ok(val.clone());
                }
                if let Some(val) = ctx.resource_attributes.get(name) {
                    return Ok(val.clone());
                }
                Ok("".to_string())
            }
            OttlPath::FieldAccess { base, field } => {
                // Handle span.field pattern
                if let OttlPath::Identifier(base_name) = base.as_ref() {
                    if base_name == "span" || base_name == "attributes" {
                        if let Some(span_attrs) = &ctx.span_attributes
                            && let Some(val) = span_attrs.get(field)
                        {
                            return Ok(val.clone());
                        }
                    } else if base_name == "resource"
                        && let Some(val) = ctx.resource_attributes.get(field)
                    {
                        return Ok(val.clone());
                    }
                }
                Ok("".to_string())
            }
            OttlPath::MapAccess { base, key } => {
                // Handle attributes["key"] pattern
                if let OttlPath::Identifier(base_name) = base.as_ref() {
                    if base_name == "attributes" {
                        if let Some(span_attrs) = &ctx.span_attributes
                            && let Some(val) = span_attrs.get(key)
                        {
                            return Ok(val.clone());
                        }
                    } else if base_name == "resource"
                        && let Some(val) = ctx.resource_attributes.get(key)
                    {
                        return Ok(val.clone());
                    }
                }
                Ok("".to_string())
            }
        }
    }
}

impl Default for OttlProcessor {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_parse_set_statement() {
        let statement = OttlParser::parse("set(attributes[\"key\"], \"value\")").unwrap();
        
        match statement {
            OttlStatement::Set { path, value } => {
                match path {
                    OttlPath::MapAccess { base, key } => {
                        assert!(matches!(base.as_ref(), OttlPath::Identifier(_)));
                        assert_eq!(key, "key");
                    }
                    _ => panic!("Expected MapAccess"),
                }
                assert!(matches!(value, OttlValue::String(s) if s == "value"));
            }
            _ => panic!("Expected Set statement"),
        }
    }
    
    #[test]
    fn test_parse_delete_key() {
        let statement = OttlParser::parse("delete_key(attributes, \"temp\")").unwrap();
        
        match statement {
            OttlStatement::DeleteKey { map, key } => {
                assert!(matches!(map, OttlPath::Identifier(_)));
                assert_eq!(key, "temp");
            }
            _ => panic!("Expected DeleteKey statement"),
        }
    }
    
    #[test]
    fn test_processor_execute() {
        let mut processor = OttlProcessor::new();
        processor.parse_and_add("set(attributes[\"service\"], \"test\")").unwrap();
        
        let mut resource_attrs = HashMap::new();
        let mut span_attrs = HashMap::new();
        
        let mut ctx = OttlContext {
            resource_attributes: &mut resource_attrs,
            span_attributes: Some(&mut span_attrs),
            metric_attributes: None,
            log_attributes: None,
        };
        
        processor.execute(&mut ctx).unwrap();
        
        assert_eq!(span_attrs.get("service"), Some(&"test".to_string()));
    }
    
    #[test]
    fn test_parse_condition_comparison() {
        let condition = OttlParser::parse_condition("span.duration > 1000").unwrap();
        
        match condition {
            OttlCondition::Comparison { left, op, right } => {
                assert!(matches!(left, OttlValue::Path(_)));
                assert_eq!(op, ComparisonOp::Gt);
                assert!(matches!(right, OttlValue::Int(1000)));
            }
            _ => panic!("Expected Comparison condition"),
        }
    }
    
    #[test]
    fn test_parse_condition_logical_and() {
        let condition = OttlParser::parse_condition("span.duration > 1000 and span.status == \"error\"").unwrap();
        
        match condition {
            OttlCondition::And(left, right) => {
                assert!(matches!(left.as_ref(), OttlCondition::Comparison { .. }));
                assert!(matches!(right.as_ref(), OttlCondition::Comparison { .. }));
            }
            _ => panic!("Expected And condition"),
        }
    }
    
    #[test]
    fn test_parse_condition_logical_or() {
        let condition = OttlParser::parse_condition("span.status == \"error\" or span.status == \"unset\"").unwrap();
        
        match condition {
            OttlCondition::Or(left, right) => {
                assert!(matches!(left.as_ref(), OttlCondition::Comparison { .. }));
                assert!(matches!(right.as_ref(), OttlCondition::Comparison { .. }));
            }
            _ => panic!("Expected Or condition"),
        }
    }
    
    #[test]
    fn test_parse_condition_not() {
        let condition = OttlParser::parse_condition("not span.status == \"ok\"").unwrap();
        
        match condition {
            OttlCondition::Not(inner) => {
                assert!(matches!(inner.as_ref(), OttlCondition::Comparison { .. }));
            }
            _ => panic!("Expected Not condition"),
        }
    }
    
    #[test]
    fn test_evaluate_condition_numeric() {
        let processor = OttlProcessor::new();
        let mut resource_attrs = HashMap::new();
        let mut span_attrs = HashMap::new();
        span_attrs.insert("duration".to_string(), "1500".to_string());
        
        let ctx = OttlContext {
            resource_attributes: &mut resource_attrs,
            span_attributes: Some(&mut span_attrs),
            metric_attributes: None,
            log_attributes: None,
        };
        
        // Test numeric comparison
        let condition = OttlCondition::Comparison {
            left: OttlValue::Path(OttlPath::Identifier("duration".to_string())),
            op: ComparisonOp::Gt,
            right: OttlValue::Int(1000),
        };
        
        let result = processor.evaluate_condition(&condition, &ctx).unwrap();
        assert!(result);
    }
    
    #[test]
    fn test_evaluate_condition_string() {
        let processor = OttlProcessor::new();
        let mut resource_attrs = HashMap::new();
        resource_attrs.insert("service.name".to_string(), "test-service".to_string());
        
        let ctx = OttlContext {
            resource_attributes: &mut resource_attrs,
            span_attributes: None,
            metric_attributes: None,
            log_attributes: None,
        };
        
        let condition = OttlCondition::Comparison {
            left: OttlValue::Path(OttlPath::Identifier("service.name".to_string())),
            op: ComparisonOp::Eq,
            right: OttlValue::String("test-service".to_string()),
        };
        
        let result = processor.evaluate_condition(&condition, &ctx).unwrap();
        assert!(result);
    }
    
    #[test]
    fn test_evaluate_condition_and() {
        let processor = OttlProcessor::new();
        let mut resource_attrs = HashMap::new();
        let mut span_attrs = HashMap::new();
        span_attrs.insert("duration".to_string(), "1500".to_string());
        span_attrs.insert("status".to_string(), "error".to_string());
        
        let ctx = OttlContext {
            resource_attributes: &mut resource_attrs,
            span_attributes: Some(&mut span_attrs),
            metric_attributes: None,
            log_attributes: None,
        };
        
        let condition = OttlCondition::And(
            Box::new(OttlCondition::Comparison {
                left: OttlValue::Path(OttlPath::Identifier("duration".to_string())),
                op: ComparisonOp::Gt,
                right: OttlValue::Int(1000),
            }),
            Box::new(OttlCondition::Comparison {
                left: OttlValue::Path(OttlPath::Identifier("status".to_string())),
                op: ComparisonOp::Eq,
                right: OttlValue::String("error".to_string()),
            }),
        );
        
        let result = processor.evaluate_condition(&condition, &ctx).unwrap();
        assert!(result);
    }
    
    #[test]
    fn test_processor_with_condition() {
        let mut processor = OttlProcessor::new();
        
        // Add statement with condition
        let statement = OttlParser::parse("set(attributes[\"high_latency\"], \"true\")").unwrap();
        let condition = OttlParser::parse_condition("span.duration > 1000").unwrap();
        processor.add_statement(statement, Some(condition));
        
        let mut resource_attrs = HashMap::new();
        let mut span_attrs = HashMap::new();
        span_attrs.insert("duration".to_string(), "1500".to_string());
        
        let mut ctx = OttlContext {
            resource_attributes: &mut resource_attrs,
            span_attributes: Some(&mut span_attrs),
            metric_attributes: None,
            log_attributes: None,
        };
        
        processor.execute(&mut ctx).unwrap();
        
        // Should have set high_latency because duration > 1000
        assert_eq!(span_attrs.get("high_latency"), Some(&"true".to_string()));
    }
    
    #[test]
    fn test_processor_with_false_condition() {
        let mut processor = OttlProcessor::new();
        
        // Add statement with condition
        let statement = OttlParser::parse("set(attributes[\"high_latency\"], \"true\")").unwrap();
        let condition = OttlParser::parse_condition("span.duration > 1000").unwrap();
        processor.add_statement(statement, Some(condition));
        
        let mut resource_attrs = HashMap::new();
        let mut span_attrs = HashMap::new();
        span_attrs.insert("duration".to_string(), "500".to_string());
        
        let mut ctx = OttlContext {
            resource_attributes: &mut resource_attrs,
            span_attributes: Some(&mut span_attrs),
            metric_attributes: None,
            log_attributes: None,
        };
        
        processor.execute(&mut ctx).unwrap();
        
        // Should NOT have set high_latency because duration <= 1000
        assert_eq!(span_attrs.get("high_latency"), None);
    }
    
    #[test]
    fn test_parse_value_types() {
        // Test string
        let val = OttlParser::parse_value("\"hello\"").unwrap();
        assert!(matches!(val, OttlValue::String(s) if s == "hello"));
        
        // Test integer
        let val = OttlParser::parse_value("42").unwrap();
        assert!(matches!(val, OttlValue::Int(42)));
        
        // Test float
        let val = OttlParser::parse_value("3.14").unwrap();
        assert!(matches!(val, OttlValue::Float(f) if (f - 3.14).abs() < 0.001));
        
        // Test bool
        let val = OttlParser::parse_value("true").unwrap();
        assert!(matches!(val, OttlValue::Bool(true)));
        
        let val = OttlParser::parse_value("false").unwrap();
        assert!(matches!(val, OttlValue::Bool(false)));
    }
    
    #[test]
    fn test_parse_path_variants() {
        // Test simple identifier
        let path = OttlParser::parse_path("span").unwrap();
        assert!(matches!(path, OttlPath::Identifier(s) if s == "span"));
        
        // Test map access
        let path = OttlParser::parse_path("attributes[\"key\"]").unwrap();
        assert!(matches!(path, OttlPath::MapAccess { key, .. } if key == "key"));
        
        // Test field access
        let path = OttlParser::parse_path("span.name").unwrap();
        assert!(matches!(path, OttlPath::FieldAccess { field, .. } if field == "name"));
    }
}
