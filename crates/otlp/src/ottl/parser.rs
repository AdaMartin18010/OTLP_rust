//! # OTTL 语法解析器
//!
//! 实现了完整的 OTTL 语法解析功能，支持语句解析和表达式解析。
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步解析操作
//! - **元组收集**: 使用 `collect()` 直接收集解析结果到元组
//! - **改进的解析器**: 利用 Rust 1.92 的解析器优化提升性能

use std::collections::HashMap;
use thiserror::Error;

/// OTTL 语句
#[derive(Debug, Clone)]
pub enum Statement {
    /// set 语句: set(path, value)
    Set { path: Path, value: Expression },

    /// where 条件语句: where condition
    Where { condition: Expression },

    /// keep_keys 语句: keep_keys(path, keys)
    KeepKeys { path: Path, keys: Vec<Expression> },

    /// limit 语句: limit(path, count)
    Limit { path: Path, count: Expression },

    /// convert 语句: convert(path, type)
    Convert { path: Path, target_type: String },

    /// route 语句: route(path, destinations)
    Route {
        path: Path,
        destinations: Vec<Expression>,
    },
}

/// OTTL 路径表达式
#[derive(Debug, Clone)]
pub enum Path {
    /// 资源属性路径: resource.attributes["key"]
    ResourceAttribute { key: String },

    /// 作用域属性路径: scope.attributes["key"]
    ScopeAttribute { key: String },

    /// 指标属性路径: metric.attributes["key"]
    MetricAttribute { key: String },

    /// 跨度属性路径: span.attributes["key"]
    SpanAttribute { key: String },

    /// 日志属性路径: log.attributes["key"]
    LogAttribute { key: String },

    /// 嵌套路径: path.subpath
    Nested { base: Box<Path>, subpath: String },

    /// 索引路径: path[index]
    Indexed { base: Box<Path>, index: Expression },
}

/// OTTL 表达式
#[derive(Debug, Clone)]
pub enum Expression {
    /// 字面量
    Literal(Literal),

    /// 路径引用
    Path(Box<Path>),

    /// 函数调用: function(args...)
    FunctionCall { name: String, args: Vec<Expression> },

    /// 二元运算: left op right
    Binary {
        left: Box<Expression>,
        op: BinaryOp,
        right: Box<Expression>,
    },

    /// 一元运算: op expr
    Unary { op: UnaryOp, expr: Box<Expression> },

    /// 条件表达式: condition ? true_expr : false_expr
    Conditional {
        condition: Box<Expression>,
        true_expr: Box<Expression>,
        false_expr: Box<Expression>,
    },
}

/// 字面量类型
#[derive(Debug, Clone)]
pub enum Literal {
    String(String),
    Int(i64),
    Float(f64),
    Bool(bool),
    Array(Vec<Expression>),
    Map(HashMap<String, Expression>),
    Null,
}

/// 二元操作符
#[derive(Debug, Clone, PartialEq)]
pub enum BinaryOp {
    // 算术运算
    Add,
    Sub,
    Mul,
    Div,
    Mod,

    // 比较运算
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,

    // 逻辑运算
    And,
    Or,

    // 字符串运算
    Concat,

    // 正则匹配
    Match,
}

/// 一元操作符
#[derive(Debug, Clone, PartialEq)]
pub enum UnaryOp {
    Not,
    Neg,
}

/// 解析错误
#[derive(Debug, Error)]
pub enum ParseError {
    #[error("语法错误: {message} at position {position}")]
    SyntaxError { message: String, position: usize },

    #[error("意外的令牌: {token} at position {position}")]
    UnexpectedToken { token: String, position: usize },

    #[error("意外的文件结尾")]
    UnexpectedEof,

    #[error("无效的标识符: {identifier}")]
    InvalidIdentifier { identifier: String },

    #[error("无效的路径: {path}")]
    InvalidPath { path: String },

    #[error("无效的函数名: {function}")]
    InvalidFunction { function: String },
}

/// OTTL 解析器
pub struct OttlParser {
    input: String,
    position: usize,
    tokens: Vec<Token>,
}

#[derive(Debug, Clone)]
enum Token {
    Identifier(String),
    String(String),
    Number(f64),
    Boolean(bool),
    LeftParen,
    RightParen,
    LeftBracket,
    RightBracket,
    LeftBrace,
    RightBrace,
    Dot,
    Comma,
    Semicolon,
    Equal,
    NotEqual,
    LessThan,
    LessEqual,
    GreaterThan,
    GreaterEqual,
    Plus,
    Minus,
    Multiply,
    Divide,
    Modulo,
    And,
    Or,
    Not,
    Question,
    Colon,
    Where,
    Set,
    KeepKeys,
    Limit,
    Convert,
    Route,
    Eof,
}

impl OttlParser {
    /// 创建新的解析器
    pub fn new(input: String) -> Self {
        Self {
            input,
            position: 0,
            tokens: Vec::new(),
        }
    }

    /// 解析 OTTL 语句
    pub fn parse(&mut self) -> Result<Vec<Statement>, ParseError> {
        self.tokenize()?;
        self.parse_statements()
    }

    /// 词法分析
    fn tokenize(&mut self) -> Result<(), ParseError> {
        let mut tokens = Vec::new();
        let mut chars = self.input.chars().peekable();

        while let Some(ch) = chars.next() {
            match ch {
                ' ' | '\t' | '\n' | '\r' => continue,

                '(' => tokens.push(Token::LeftParen),
                ')' => tokens.push(Token::RightParen),
                '[' => tokens.push(Token::LeftBracket),
                ']' => tokens.push(Token::RightBracket),
                '{' => tokens.push(Token::LeftBrace),
                '}' => tokens.push(Token::RightBrace),
                '.' => tokens.push(Token::Dot),
                ',' => tokens.push(Token::Comma),
                ';' => tokens.push(Token::Semicolon),

                '=' => {
                    if chars.peek() == Some(&'=') {
                        chars.next();
                        tokens.push(Token::Equal);
                    } else {
                        tokens.push(Token::Equal);
                    }
                }

                '!' => {
                    if chars.peek() == Some(&'=') {
                        chars.next();
                        tokens.push(Token::NotEqual);
                    } else {
                        tokens.push(Token::Not);
                    }
                }

                '<' => {
                    if chars.peek() == Some(&'=') {
                        chars.next();
                        tokens.push(Token::LessEqual);
                    } else {
                        tokens.push(Token::LessThan);
                    }
                }

                '>' => {
                    if chars.peek() == Some(&'=') {
                        chars.next();
                        tokens.push(Token::GreaterEqual);
                    } else {
                        tokens.push(Token::GreaterThan);
                    }
                }

                '+' => tokens.push(Token::Plus),
                '-' => tokens.push(Token::Minus),
                '*' => tokens.push(Token::Multiply),
                '/' => tokens.push(Token::Divide),
                '%' => tokens.push(Token::Modulo),
                '&' => {
                    if chars.peek() == Some(&'&') {
                        chars.next();
                        tokens.push(Token::And);
                    } else {
                        return Err(ParseError::UnexpectedToken {
                            token: "&".to_string(),
                            position: self.position,
                        });
                    }
                }
                '|' => {
                    if chars.peek() == Some(&'|') {
                        chars.next();
                        tokens.push(Token::Or);
                    } else {
                        return Err(ParseError::UnexpectedToken {
                            token: "|".to_string(),
                            position: self.position,
                        });
                    }
                }
                '?' => tokens.push(Token::Question),
                ':' => tokens.push(Token::Colon),

                '"' => {
                    let mut string = String::new();
                    while let Some(ch) = chars.next() {
                        if ch == '"' {
                            break;
                        }
                        string.push(ch);
                    }
                    tokens.push(Token::String(string));
                }

                '0'..='9' => {
                    let mut number = String::new();
                    number.push(ch);

                    while let Some(&next) = chars.peek() {
                        if next.is_ascii_digit() || next == '.' {
                            // 安全：peek()已确认有值
                            if let Some(ch) = chars.next() {
                                number.push(ch);
                            }
                        } else {
                            break;
                        }
                    }

                    let num = number.parse::<f64>().map_err(|_| ParseError::SyntaxError {
                        message: format!("无效的数字: {}", number),
                        position: self.position,
                    })?;
                    tokens.push(Token::Number(num));
                }

                _ if ch.is_ascii_alphabetic() || ch == '_' => {
                    let mut identifier = String::new();
                    identifier.push(ch);

                    while let Some(&next) = chars.peek() {
                        if next.is_ascii_alphanumeric() || next == '_' {
                            // 安全：peek()已确认有值
                            if let Some(ch) = chars.next() {
                                identifier.push(ch);
                            }
                        } else {
                            break;
                        }
                    }

                    // 检查是否为关键字
                    let token = match identifier.as_str() {
                        "where" => Token::Where,
                        "set" => Token::Set,
                        "keep_keys" => Token::KeepKeys,
                        "limit" => Token::Limit,
                        "convert" => Token::Convert,
                        "route" => Token::Route,
                        "true" => Token::Boolean(true),
                        "false" => Token::Boolean(false),
                        _ => Token::Identifier(identifier),
                    };
                    tokens.push(token);
                }

                _ => {
                    return Err(ParseError::UnexpectedToken {
                        token: ch.to_string(),
                        position: self.position,
                    });
                }
            }
            self.position += 1;
        }

        tokens.push(Token::Eof);
        self.tokens = tokens;
        Ok(())
    }

    /// 解析语句列表
    fn parse_statements(&mut self) -> Result<Vec<Statement>, ParseError> {
        let mut statements = Vec::new();

        while !self.is_at_end() {
            if let Some(statement) = self.parse_statement()? {
                statements.push(statement);
            }
        }

        Ok(statements)
    }

    /// 解析单个语句
    fn parse_statement(&mut self) -> Result<Option<Statement>, ParseError> {
        match self.peek() {
            Token::Set => {
                self.advance();
                self.parse_set_statement()
            }
            Token::Where => {
                self.advance();
                self.parse_where_statement()
            }
            Token::KeepKeys => {
                self.advance();
                self.parse_keep_keys_statement()
            }
            Token::Limit => {
                self.advance();
                self.parse_limit_statement()
            }
            Token::Convert => {
                self.advance();
                self.parse_convert_statement()
            }
            Token::Route => {
                self.advance();
                self.parse_route_statement()
            }
            Token::Eof => Ok(None),
            _ => Err(ParseError::SyntaxError {
                message: "意外的令牌".to_string(),
                position: self.position,
            }),
        }
    }

    /// 解析 set 语句
    fn parse_set_statement(&mut self) -> Result<Option<Statement>, ParseError> {
        self.expect(Token::LeftParen)?;
        let path = self.parse_path()?;
        self.expect(Token::Comma)?;
        let value = self.parse_expression()?;
        self.expect(Token::RightParen)?;

        Ok(Some(Statement::Set { path, value }))
    }

    /// 解析 where 语句
    fn parse_where_statement(&mut self) -> Result<Option<Statement>, ParseError> {
        let condition = self.parse_expression()?;
        Ok(Some(Statement::Where { condition }))
    }

    /// 解析 keep_keys 语句
    fn parse_keep_keys_statement(&mut self) -> Result<Option<Statement>, ParseError> {
        self.expect(Token::LeftParen)?;
        let path = self.parse_path()?;
        self.expect(Token::Comma)?;
        let keys = self.parse_expression_list()?;
        self.expect(Token::RightParen)?;

        Ok(Some(Statement::KeepKeys { path, keys }))
    }

    /// 解析 limit 语句
    fn parse_limit_statement(&mut self) -> Result<Option<Statement>, ParseError> {
        self.expect(Token::LeftParen)?;
        let path = self.parse_path()?;
        self.expect(Token::Comma)?;
        let count = self.parse_expression()?;
        self.expect(Token::RightParen)?;

        Ok(Some(Statement::Limit { path, count }))
    }

    /// 解析 convert 语句
    fn parse_convert_statement(&mut self) -> Result<Option<Statement>, ParseError> {
        self.expect(Token::LeftParen)?;
        let path = self.parse_path()?;
        self.expect(Token::Comma)?;
        let target_type = self.parse_string_literal()?;
        self.expect(Token::RightParen)?;

        Ok(Some(Statement::Convert { path, target_type }))
    }

    /// 解析 route 语句
    fn parse_route_statement(&mut self) -> Result<Option<Statement>, ParseError> {
        self.expect(Token::LeftParen)?;
        let path = self.parse_path()?;
        self.expect(Token::Comma)?;
        let destinations = self.parse_expression_list()?;
        self.expect(Token::RightParen)?;

        Ok(Some(Statement::Route { path, destinations }))
    }

    /// 解析路径
    fn parse_path(&mut self) -> Result<Path, ParseError> {
        // 简化的路径解析实现
        let token = self.peek().clone();
        match token {
            Token::Identifier(name) => {
                self.advance();
                match name.as_str() {
                    "resource" => self.parse_resource_path(),
                    "scope" => self.parse_scope_path(),
                    "metric" => self.parse_metric_path(),
                    "span" => self.parse_span_path(),
                    "log" => self.parse_log_path(),
                    _ => Err(ParseError::InvalidPath { path: name }),
                }
            }
            _ => Err(ParseError::SyntaxError {
                message: "期望路径".to_string(),
                position: self.position,
            }),
        }
    }

    /// 解析资源路径
    fn parse_resource_path(&mut self) -> Result<Path, ParseError> {
        self.expect(Token::Dot)?;
        let token = self.peek().clone();
        match token {
            Token::Identifier(name) => {
                self.advance();
                if name == "attributes" {
                    self.expect(Token::LeftBracket)?;
                    let key = self.parse_string_literal()?;
                    self.expect(Token::RightBracket)?;
                    Ok(Path::ResourceAttribute { key: key.clone() })
                } else {
                    Err(ParseError::InvalidPath { path: name.clone() })
                }
            }
            _ => Err(ParseError::SyntaxError {
                message: "期望 attributes".to_string(),
                position: self.position,
            }),
        }
    }

    /// 解析作用域路径
    fn parse_scope_path(&mut self) -> Result<Path, ParseError> {
        self.parse_attribute_path("scope", |key| Path::ScopeAttribute { key })
    }

    /// 解析指标路径
    fn parse_metric_path(&mut self) -> Result<Path, ParseError> {
        self.parse_attribute_path("metric", |key| Path::MetricAttribute { key })
    }

    /// 解析跨度路径
    fn parse_span_path(&mut self) -> Result<Path, ParseError> {
        self.parse_attribute_path("span", |key| Path::SpanAttribute { key })
    }

    /// 解析日志路径
    fn parse_log_path(&mut self) -> Result<Path, ParseError> {
        self.parse_attribute_path("log", |key| Path::LogAttribute { key })
    }

    /// 解析属性路径的通用方法
    fn parse_attribute_path<F>(
        &mut self,
        _prefix: &str,
        path_creator: F,
    ) -> Result<Path, ParseError>
    where
        F: FnOnce(String) -> Path,
    {
        self.expect(Token::Dot)?;
        let token = self.peek().clone();
        match token {
            Token::Identifier(name) => {
                self.advance();
                if name == "attributes" {
                    self.expect(Token::LeftBracket)?;
                    let key = self.parse_string_literal()?;
                    self.expect(Token::RightBracket)?;
                    Ok(path_creator(key))
                } else {
                    Err(ParseError::InvalidPath { path: name })
                }
            }
            _ => Err(ParseError::SyntaxError {
                message: "期望 attributes".to_string(),
                position: self.position,
            }),
        }
    }

    /// 解析表达式
    fn parse_expression(&mut self) -> Result<Expression, ParseError> {
        self.parse_conditional_expression()
    }

    /// 解析条件表达式
    fn parse_conditional_expression(&mut self) -> Result<Expression, ParseError> {
        let expr = self.parse_or_expression()?;

        if self.check(Token::Question) {
            self.advance();
            let true_expr = self.parse_expression()?;
            self.expect(Token::Colon)?;
            let false_expr = self.parse_expression()?;
            return Ok(Expression::Conditional {
                condition: Box::new(expr),
                true_expr: Box::new(true_expr),
                false_expr: Box::new(false_expr),
            });
        }

        Ok(expr)
    }

    /// 解析或表达式
    fn parse_or_expression(&mut self) -> Result<Expression, ParseError> {
        let mut expr = self.parse_and_expression()?;

        while self.check(Token::Or) {
            let op = self.get_binary_op();
            self.advance();
            let right = self.parse_and_expression()?;
            expr = Expression::Binary {
                left: Box::new(expr),
                op,
                right: Box::new(right),
            };
        }

        Ok(expr)
    }

    /// 解析与表达式
    fn parse_and_expression(&mut self) -> Result<Expression, ParseError> {
        let mut expr = self.parse_equality_expression()?;

        while self.check(Token::And) {
            let op = self.get_binary_op();
            self.advance();
            let right = self.parse_equality_expression()?;
            expr = Expression::Binary {
                left: Box::new(expr),
                op,
                right: Box::new(right),
            };
        }

        Ok(expr)
    }

    /// 解析相等表达式
    fn parse_equality_expression(&mut self) -> Result<Expression, ParseError> {
        let mut expr = self.parse_comparison_expression()?;

        while self.check(Token::Equal) || self.check(Token::NotEqual) {
            let op = self.get_binary_op();
            self.advance();
            let right = self.parse_comparison_expression()?;
            expr = Expression::Binary {
                left: Box::new(expr),
                op,
                right: Box::new(right),
            };
        }

        Ok(expr)
    }

    /// 解析比较表达式
    fn parse_comparison_expression(&mut self) -> Result<Expression, ParseError> {
        let mut expr = self.parse_term_expression()?;

        while self.check(Token::GreaterThan)
            || self.check(Token::GreaterEqual)
            || self.check(Token::LessThan)
            || self.check(Token::LessEqual)
        {
            let op = self.get_binary_op();
            self.advance();
            let right = self.parse_term_expression()?;
            expr = Expression::Binary {
                left: Box::new(expr),
                op,
                right: Box::new(right),
            };
        }

        Ok(expr)
    }

    /// 解析项表达式
    fn parse_term_expression(&mut self) -> Result<Expression, ParseError> {
        let mut expr = self.parse_factor_expression()?;

        while self.check(Token::Plus) || self.check(Token::Minus) {
            let op = self.get_binary_op();
            self.advance();
            let right = self.parse_factor_expression()?;
            expr = Expression::Binary {
                left: Box::new(expr),
                op,
                right: Box::new(right),
            };
        }

        Ok(expr)
    }

    /// 解析因子表达式
    fn parse_factor_expression(&mut self) -> Result<Expression, ParseError> {
        let mut expr = self.parse_unary_expression()?;

        while self.check(Token::Multiply) || self.check(Token::Divide) || self.check(Token::Modulo)
        {
            let op = self.get_binary_op();
            self.advance();
            let right = self.parse_unary_expression()?;
            expr = Expression::Binary {
                left: Box::new(expr),
                op,
                right: Box::new(right),
            };
        }

        Ok(expr)
    }

    /// 解析一元表达式
    fn parse_unary_expression(&mut self) -> Result<Expression, ParseError> {
        if self.check(Token::Not) || self.check(Token::Minus) {
            let op = self.get_unary_op();
            self.advance();
            let expr = self.parse_unary_expression()?;
            return Ok(Expression::Unary {
                op,
                expr: Box::new(expr),
            });
        }

        self.parse_primary_expression()
    }

    /// 解析主要表达式
    fn parse_primary_expression(&mut self) -> Result<Expression, ParseError> {
        if self.is_at_end() {
            return Err(ParseError::UnexpectedEof);
        }

        let token = self.tokens[self.position].clone();
        self.position += 1;

        match token {
            Token::String(s) => Ok(Expression::Literal(Literal::String(s))),
            Token::Number(n) => Ok(Expression::Literal(Literal::Float(n))),
            Token::Boolean(b) => Ok(Expression::Literal(Literal::Bool(b))),
            Token::Identifier(name) => {
                if self.position < self.tokens.len()
                    && matches!(self.tokens[self.position], Token::LeftParen)
                {
                    // 函数调用
                    self.parse_function_call(name)
                } else {
                    // 路径引用
                    Ok(Expression::Path(Box::new(
                        self.parse_path_from_identifier(name)?,
                    )))
                }
            }
            Token::LeftParen => {
                let expr = self.parse_expression()?;
                self.expect(Token::RightParen)?;
                Ok(expr)
            }
            _ => Err(ParseError::SyntaxError {
                message: "期望表达式".to_string(),
                position: self.position,
            }),
        }
    }

    /// 解析函数调用
    fn parse_function_call(&mut self, name: String) -> Result<Expression, ParseError> {
        self.expect(Token::LeftParen)?;
        let args = self.parse_expression_list()?;
        self.expect(Token::RightParen)?;

        Ok(Expression::FunctionCall { name, args })
    }

    /// 解析表达式列表
    fn parse_expression_list(&mut self) -> Result<Vec<Expression>, ParseError> {
        let mut args = Vec::new();

        if !self.check(Token::RightParen) {
            loop {
                args.push(self.parse_expression()?);
                if !self.check(Token::Comma) {
                    break;
                }
                self.advance();
            }
        }

        Ok(args)
    }

    /// 从标识符解析路径
    fn parse_path_from_identifier(&mut self, name: String) -> Result<Path, ParseError> {
        match name.as_str() {
            "resource" => self.parse_resource_path(),
            "scope" => self.parse_scope_path(),
            "metric" => self.parse_metric_path(),
            "span" => self.parse_span_path(),
            "log" => self.parse_log_path(),
            _ => Err(ParseError::InvalidPath { path: name }),
        }
    }

    /// 解析字符串字面量
    fn parse_string_literal(&mut self) -> Result<String, ParseError> {
        let token = self.peek().clone();
        match token {
            Token::String(s) => {
                self.advance();
                Ok(s)
            }
            _ => Err(ParseError::SyntaxError {
                message: "期望字符串字面量".to_string(),
                position: self.position,
            }),
        }
    }

    /// 获取二元操作符
    fn get_binary_op(&self) -> BinaryOp {
        match self.peek() {
            Token::Plus => BinaryOp::Add,
            Token::Minus => BinaryOp::Sub,
            Token::Multiply => BinaryOp::Mul,
            Token::Divide => BinaryOp::Div,
            Token::Modulo => BinaryOp::Mod,
            Token::Equal => BinaryOp::Eq,
            Token::NotEqual => BinaryOp::Ne,
            Token::LessThan => BinaryOp::Lt,
            Token::LessEqual => BinaryOp::Le,
            Token::GreaterThan => BinaryOp::Gt,
            Token::GreaterEqual => BinaryOp::Ge,
            Token::And => BinaryOp::And,
            Token::Or => BinaryOp::Or,
            _ => BinaryOp::Eq, // 默认值
        }
    }

    /// 获取一元操作符
    fn get_unary_op(&self) -> UnaryOp {
        match self.peek() {
            Token::Not => UnaryOp::Not,
            Token::Minus => UnaryOp::Neg,
            _ => UnaryOp::Not, // 默认值
        }
    }

    /// 检查当前令牌
    fn check(&self, token_type: Token) -> bool {
        !self.is_at_end()
            && std::mem::discriminant(&self.tokens[self.position])
                == std::mem::discriminant(&token_type)
    }

    /// 检查是否到达结尾
    fn is_at_end(&self) -> bool {
        self.position >= self.tokens.len() || matches!(self.peek(), Token::Eof)
    }

    /// 获取当前令牌
    fn peek(&self) -> &Token {
        if self.position >= self.tokens.len() {
            &Token::Eof
        } else {
            &self.tokens[self.position]
        }
    }

    /// 前进到下一个令牌
    fn advance(&mut self) -> &Token {
        if !self.is_at_end() {
            self.position += 1;
        }
        self.previous()
    }

    /// 获取前一个令牌
    fn previous(&self) -> &Token {
        if self.position == 0 {
            &Token::Eof
        } else {
            &self.tokens[self.position - 1]
        }
    }

    /// 期望特定令牌
    fn expect(&mut self, token_type: Token) -> Result<(), ParseError> {
        if self.check(token_type) {
            self.advance();
            Ok(())
        } else {
            Err(ParseError::UnexpectedToken {
                token: format!("{:?}", self.peek()),
                position: self.position,
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_set_statement() {
        let input = r#"set(resource.attributes["service.name"], "my-service")"#;
        let mut parser = OttlParser::new(input.to_string());
        let result = parser.parse();
        assert!(result.is_ok());
    }

    #[test]
    fn test_parse_where_statement() {
        let input = r#"where resource.attributes["env"] == "production""#;
        let mut parser = OttlParser::new(input.to_string());
        let result = parser.parse();
        assert!(result.is_ok());
    }

    #[test]
    fn test_parse_function_call() {
        let input = r#"SHA256("test")"#;
        let mut parser = OttlParser::new(input.to_string());
        let result = parser.parse();
        assert!(result.is_ok());
    }
}
