//! # OTTL 语法解析器
//!
//! 实现了完整的 OTTL 语法解析功能，支持语句解析和表达式解析。

use std::collections::HashMap;
use thiserror::Error;

/// OTTL 语句
#[derive(Debug, Clone)]
pub enum Statement {
    Set { path: Path, value: Expression },
    Where { condition: Expression },
    KeepKeys { path: Path, keys: Vec<Expression> },
    Limit { path: Path, count: Expression },
    Convert { path: Path, target_type: String },
    Route { path: Path, destinations: Vec<Expression> },
}

/// OTTL 路径表达式
#[derive(Debug, Clone)]
pub enum Path {
    ResourceAttribute { key: String },
    ScopeAttribute { key: String },
    MetricAttribute { key: String },
    SpanAttribute { key: String },
    LogAttribute { key: String },
    Nested { base: Box<Path>, subpath: String },
    Indexed { base: Box<Path>, index: Expression },
}

/// OTTL 表达式
#[derive(Debug, Clone)]
pub enum Expression {
    Literal(Literal),
    Path(Box<Path>),
    FunctionCall { name: String, args: Vec<Expression> },
    Binary { left: Box<Expression>, op: BinaryOp, right: Box<Expression> },
    Unary { op: UnaryOp, expr: Box<Expression> },
    Conditional { condition: Box<Expression>, true_expr: Box<Expression>, false_expr: Box<Expression> },
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
    Add, Sub, Mul, Div, Mod,
    Eq, Ne, Lt, Le, Gt, Ge,
    And, Or, Concat, Match,
}

/// 一元操作符
#[derive(Debug, Clone, PartialEq)]
pub enum UnaryOp {
    Not, Neg,
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
    LeftParen, RightParen,
    LeftBracket, RightBracket,
    LeftBrace, RightBrace,
    Dot, Comma, Semicolon,
    Equal, NotEqual,
    LessThan, LessEqual,
    GreaterThan, GreaterEqual,
    Plus, Minus, Multiply, Divide, Modulo,
    And, Or, Not,
    Question, Colon,
    Where, Set, KeepKeys, Limit, Convert, Route,
    Eof,
}

impl OttlParser {
    pub fn new(input: String) -> Self {
        Self {
            input,
            position: 0,
            tokens: Vec::new(),
        }
    }

    pub fn parse(&mut self) -> Result<Vec<Statement>, ParseError> {
        self.tokenize()?;
        self.parse_statements()
    }

    fn tokenize(&mut self) -> Result<(), ParseError> {
        let mut tokens = Vec::new();
        let mut chars = self.input.chars().peekable();

        #[allow(clippy::while_let_on_iterator)]
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
                '+' => tokens.push(Token::Plus),
                '-' => tokens.push(Token::Minus),
                '*' => tokens.push(Token::Multiply),
                '/' => tokens.push(Token::Divide),
                '%' => tokens.push(Token::Modulo),
                '?' => tokens.push(Token::Question),
                ':' => tokens.push(Token::Colon),
                '=' => self.tokenize_equals(&mut chars, &mut tokens)?,
                '!' => self.tokenize_bang(&mut chars, &mut tokens)?,
                '<' => self.tokenize_less_than(&mut chars, &mut tokens)?,
                '>' => self.tokenize_greater_than(&mut chars, &mut tokens)?,
                '&' => self.tokenize_and(&mut chars, &mut tokens)?,
                '|' => self.tokenize_or(&mut chars, &mut tokens)?,
                '"' => self.tokenize_string(&mut chars, &mut tokens)?,
                '0'..='9' => self.tokenize_number(ch, &mut chars, &mut tokens)?,
                _ if ch.is_ascii_alphabetic() || ch == '_' => {
                    self.tokenize_identifier(ch, &mut chars, &mut tokens)?
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

    fn tokenize_equals(&self, chars: &mut std::iter::Peekable<std::str::Chars>, tokens: &mut Vec<Token>) -> Result<(), ParseError> {
        if chars.peek() == Some(&'=') {
            chars.next();
        }
        tokens.push(Token::Equal);
        Ok(())
    }

    fn tokenize_bang(&self, chars: &mut std::iter::Peekable<std::str::Chars>, tokens: &mut Vec<Token>) -> Result<(), ParseError> {
        if chars.peek() == Some(&'=') {
            chars.next();
            tokens.push(Token::NotEqual);
        } else {
            tokens.push(Token::Not);
        }
        Ok(())
    }

    fn tokenize_less_than(&self, chars: &mut std::iter::Peekable<std::str::Chars>, tokens: &mut Vec<Token>) -> Result<(), ParseError> {
        if chars.peek() == Some(&'=') {
            chars.next();
            tokens.push(Token::LessEqual);
        } else {
            tokens.push(Token::LessThan);
        }
        Ok(())
    }

    fn tokenize_greater_than(&self, chars: &mut std::iter::Peekable<std::str::Chars>, tokens: &mut Vec<Token>) -> Result<(), ParseError> {
        if chars.peek() == Some(&'=') {
            chars.next();
            tokens.push(Token::GreaterEqual);
        } else {
            tokens.push(Token::GreaterThan);
        }
        Ok(())
    }

    fn tokenize_and(&self, chars: &mut std::iter::Peekable<std::str::Chars>, tokens: &mut Vec<Token>) -> Result<(), ParseError> {
        if chars.peek() == Some(&'&') {
            chars.next();
            tokens.push(Token::And);
        } else {
            return Err(ParseError::UnexpectedToken {
                token: "&".to_string(),
                position: self.position,
            });
        }
        Ok(())
    }

    fn tokenize_or(&self, chars: &mut std::iter::Peekable<std::str::Chars>, tokens: &mut Vec<Token>) -> Result<(), ParseError> {
        if chars.peek() == Some(&'|') {
            chars.next();
            tokens.push(Token::Or);
        } else {
            return Err(ParseError::UnexpectedToken {
                token: "|".to_string(),
                position: self.position,
            });
        }
        Ok(())
    }

    fn tokenize_string(&self, chars: &mut std::iter::Peekable<std::str::Chars>, tokens: &mut Vec<Token>) -> Result<(), ParseError> {
        let mut string = String::new();
        for ch in chars.by_ref() {
            if ch == '"' {
                break;
            }
            string.push(ch);
        }
        tokens.push(Token::String(string));
        Ok(())
    }

    fn tokenize_number(&self, first: char, chars: &mut std::iter::Peekable<std::str::Chars>, tokens: &mut Vec<Token>) -> Result<(), ParseError> {
        let mut number = String::new();
        number.push(first);

        while let Some(&next) = chars.peek() {
            if next.is_ascii_digit() || next == '.' {
                chars.next();
                number.push(next);
            } else {
                break;
            }
        }

        let num = number.parse::<f64>().map_err(|_| ParseError::SyntaxError {
            message: format!("无效的数字: {}", number),
            position: self.position,
        })?;
        tokens.push(Token::Number(num));
        Ok(())
    }

    fn tokenize_identifier(&self, first: char, chars: &mut std::iter::Peekable<std::str::Chars>, tokens: &mut Vec<Token>) -> Result<(), ParseError> {
        let mut identifier = String::new();
        identifier.push(first);

        while let Some(&next) = chars.peek() {
            if next.is_ascii_alphanumeric() || next == '_' {
                chars.next();
                identifier.push(next);
            } else {
                break;
            }
        }

        let token = Self::keyword_or_identifier(&identifier);
        tokens.push(token);
        Ok(())
    }

    fn keyword_or_identifier(identifier: &str) -> Token {
        match identifier {
            "where" => Token::Where,
            "set" => Token::Set,
            "keep_keys" => Token::KeepKeys,
            "limit" => Token::Limit,
            "convert" => Token::Convert,
            "route" => Token::Route,
            "true" => Token::Boolean(true),
            "false" => Token::Boolean(false),
            _ => Token::Identifier(identifier.to_string()),
        }
    }

    fn parse_statements(&mut self) -> Result<Vec<Statement>, ParseError> {
        let mut statements = Vec::new();

        while !self.is_at_end() {
            if let Some(statement) = self.parse_statement()? {
                statements.push(statement);
            }
        }

        Ok(statements)
    }

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

    fn parse_set_statement(&mut self) -> Result<Option<Statement>, ParseError> {
        self.expect(Token::LeftParen)?;
        let path = self.parse_path()?;
        self.expect(Token::Comma)?;
        let value = self.parse_expression()?;
        self.expect(Token::RightParen)?;

        Ok(Some(Statement::Set { path, value }))
    }

    fn parse_where_statement(&mut self) -> Result<Option<Statement>, ParseError> {
        let condition = self.parse_expression()?;
        Ok(Some(Statement::Where { condition }))
    }

    fn parse_keep_keys_statement(&mut self) -> Result<Option<Statement>, ParseError> {
        self.expect(Token::LeftParen)?;
        let path = self.parse_path()?;
        self.expect(Token::Comma)?;
        let keys = self.parse_expression_list()?;
        self.expect(Token::RightParen)?;

        Ok(Some(Statement::KeepKeys { path, keys }))
    }

    fn parse_limit_statement(&mut self) -> Result<Option<Statement>, ParseError> {
        self.expect(Token::LeftParen)?;
        let path = self.parse_path()?;
        self.expect(Token::Comma)?;
        let count = self.parse_expression()?;
        self.expect(Token::RightParen)?;

        Ok(Some(Statement::Limit { path, count }))
    }

    fn parse_convert_statement(&mut self) -> Result<Option<Statement>, ParseError> {
        self.expect(Token::LeftParen)?;
        let path = self.parse_path()?;
        self.expect(Token::Comma)?;
        let target_type = self.parse_string_literal()?;
        self.expect(Token::RightParen)?;

        Ok(Some(Statement::Convert { path, target_type }))
    }

    fn parse_route_statement(&mut self) -> Result<Option<Statement>, ParseError> {
        self.expect(Token::LeftParen)?;
        let path = self.parse_path()?;
        self.expect(Token::Comma)?;
        let destinations = self.parse_expression_list()?;
        self.expect(Token::RightParen)?;

        Ok(Some(Statement::Route { path, destinations }))
    }

    fn parse_path(&mut self) -> Result<Path, ParseError> {
        let token = self.peek().clone();
        let Token::Identifier(name) = token else {
            return Err(ParseError::SyntaxError {
                message: "期望路径".to_string(),
                position: self.position,
            });
        };
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

    fn parse_resource_path(&mut self) -> Result<Path, ParseError> {
        self.expect(Token::Dot)?;
        let name = self.extract_identifier()?;
        
        if name != "attributes" {
            return Err(ParseError::InvalidPath { path: name });
        }
        
        self.expect(Token::LeftBracket)?;
        let key = self.parse_string_literal()?;
        self.expect(Token::RightBracket)?;
        Ok(Path::ResourceAttribute { key })
    }

    fn parse_scope_path(&mut self) -> Result<Path, ParseError> {
        self.parse_attribute_path("scope", |key| Path::ScopeAttribute { key })
    }

    fn parse_metric_path(&mut self) -> Result<Path, ParseError> {
        self.parse_attribute_path("metric", |key| Path::MetricAttribute { key })
    }

    fn parse_span_path(&mut self) -> Result<Path, ParseError> {
        self.parse_attribute_path("span", |key| Path::SpanAttribute { key })
    }

    fn parse_log_path(&mut self) -> Result<Path, ParseError> {
        self.parse_attribute_path("log", |key| Path::LogAttribute { key })
    }

    fn parse_attribute_path<F>(&mut self, _prefix: &str, path_creator: F) -> Result<Path, ParseError>
    where
        F: FnOnce(String) -> Path,
    {
        self.expect(Token::Dot)?;
        let name = self.extract_identifier()?;
        
        if name != "attributes" {
            return Err(ParseError::InvalidPath { path: name });
        }
        
        self.expect(Token::LeftBracket)?;
        let key = self.parse_string_literal()?;
        self.expect(Token::RightBracket)?;
        Ok(path_creator(key))
    }

    fn extract_identifier(&mut self) -> Result<String, ParseError> {
        match self.peek() {
            Token::Identifier(name) => {
                let name = name.clone();
                self.advance();
                Ok(name)
            }
            _ => Err(ParseError::SyntaxError {
                message: "期望 attributes".to_string(),
                position: self.position,
            }),
        }
    }

    fn parse_expression(&mut self) -> Result<Expression, ParseError> {
        self.parse_conditional_expression()
    }

    fn parse_conditional_expression(&mut self) -> Result<Expression, ParseError> {
        let expr = self.parse_or_expression()?;

        if !self.check(Token::Question) {
            return Ok(expr);
        }

        self.advance();
        let true_expr = self.parse_expression()?;
        self.expect(Token::Colon)?;
        let false_expr = self.parse_expression()?;
        
        Ok(Expression::Conditional {
            condition: Box::new(expr),
            true_expr: Box::new(true_expr),
            false_expr: Box::new(false_expr),
        })
    }

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

    fn parse_comparison_expression(&mut self) -> Result<Expression, ParseError> {
        let mut expr = self.parse_term_expression()?;

        while self.check_comparison_op() {
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

    fn check_comparison_op(&self) -> bool {
        self.check(Token::GreaterThan)
            || self.check(Token::GreaterEqual)
            || self.check(Token::LessThan)
            || self.check(Token::LessEqual)
    }

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

    fn parse_factor_expression(&mut self) -> Result<Expression, ParseError> {
        let mut expr = self.parse_unary_expression()?;

        while self.check(Token::Multiply) || self.check(Token::Divide) || self.check(Token::Modulo) {
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

    fn parse_unary_expression(&mut self) -> Result<Expression, ParseError> {
        if !self.check(Token::Not) && !self.check(Token::Minus) {
            return self.parse_primary_expression();
        }

        let op = self.get_unary_op();
        self.advance();
        let expr = self.parse_unary_expression()?;
        Ok(Expression::Unary {
            op,
            expr: Box::new(expr),
        })
    }

    fn parse_primary_expression(&mut self) -> Result<Expression, ParseError> {
        if self.is_at_end() {
            return Err(ParseError::UnexpectedEof);
        }

        let token = self.tokens[self.position].clone();
        self.position += 1;

        self.handle_primary_token(token)
    }

    fn handle_primary_token(&mut self, token: Token) -> Result<Expression, ParseError> {
        match token {
            Token::String(s) => Ok(Expression::Literal(Literal::String(s))),
            Token::Number(n) => Ok(Expression::Literal(Literal::Float(n))),
            Token::Boolean(b) => Ok(Expression::Literal(Literal::Bool(b))),
            Token::Identifier(name) => self.handle_identifier_expression(name),
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

    fn handle_identifier_expression(&mut self, name: String) -> Result<Expression, ParseError> {
        if self.is_function_call() {
            self.parse_function_call(name)
        } else {
            Ok(Expression::Path(Box::new(
                self.parse_path_from_identifier(name)?,
            )))
        }
    }

    fn is_function_call(&self) -> bool {
        self.position < self.tokens.len()
            && matches!(self.tokens[self.position], Token::LeftParen)
    }

    fn parse_function_call(&mut self, name: String) -> Result<Expression, ParseError> {
        self.expect(Token::LeftParen)?;
        let args = self.parse_expression_list()?;
        self.expect(Token::RightParen)?;

        Ok(Expression::FunctionCall { name, args })
    }

    fn parse_expression_list(&mut self) -> Result<Vec<Expression>, ParseError> {
        let mut args = Vec::new();

        if self.check(Token::RightParen) {
            return Ok(args);
        }

        loop {
            args.push(self.parse_expression()?);
            if !self.check(Token::Comma) {
                break;
            }
            self.advance();
        }

        Ok(args)
    }

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

    fn parse_string_literal(&mut self) -> Result<String, ParseError> {
        match self.peek() {
            Token::String(s) => {
                let s = s.clone();
                self.advance();
                Ok(s)
            }
            _ => Err(ParseError::SyntaxError {
                message: "期望字符串字面量".to_string(),
                position: self.position,
            }),
        }
    }

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
            _ => BinaryOp::Eq,
        }
    }

    fn get_unary_op(&self) -> UnaryOp {
        match self.peek() {
            Token::Not => UnaryOp::Not,
            Token::Minus => UnaryOp::Neg,
            _ => UnaryOp::Not,
        }
    }

    fn check(&self, token_type: Token) -> bool {
        !self.is_at_end()
            && std::mem::discriminant(&self.tokens[self.position])
                == std::mem::discriminant(&token_type)
    }

    fn is_at_end(&self) -> bool {
        self.position >= self.tokens.len() || matches!(self.peek(), Token::Eof)
    }

    fn peek(&self) -> &Token {
        if self.position >= self.tokens.len() {
            return &Token::Eof;
        }
        &self.tokens[self.position]
    }

    fn advance(&mut self) -> &Token {
        if !self.is_at_end() {
            self.position += 1;
        }
        self.previous()
    }

    fn previous(&self) -> &Token {
        if self.position == 0 {
            return &Token::Eof;
        }
        &self.tokens[self.position - 1]
    }

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
