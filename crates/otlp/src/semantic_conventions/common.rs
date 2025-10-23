//! Common types for semantic conventions

use std::collections::HashMap;
use std::fmt;

/// Attribute key type
pub type AttributeKey = String;

/// Attribute value variants
#[derive(Debug, Clone, PartialEq)]
pub enum AttributeValue {
    /// String value
    String(String),
    
    /// Integer value
    Int(i64),
    
    /// Floating point value
    Double(f64),
    
    /// Boolean value
    Bool(bool),
    
    /// Array of values
    Array(Vec<AttributeValue>),
}

impl fmt::Display for AttributeValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AttributeValue::String(s) => write!(f, "{}", s),
            AttributeValue::Int(i) => write!(f, "{}", i),
            AttributeValue::Double(d) => write!(f, "{}", d),
            AttributeValue::Bool(b) => write!(f, "{}", b),
            AttributeValue::Array(arr) => {
                write!(f, "[")?;
                for (i, v) in arr.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", v)?;
                }
                write!(f, "]")
            }
        }
    }
}

/// Attribute map type
pub type AttributeMap = HashMap<AttributeKey, AttributeValue>;

/// Semantic convention error
#[derive(Debug, thiserror::Error)]
pub enum SemanticConventionError {
    #[error("Missing required attribute: {0}")]
    MissingRequired(String),
    
    #[error("Invalid attribute value for {key}: {reason}")]
    InvalidValue {
        key: String,
        reason: String,
    },
    
    #[error("Validation failed: {0}")]
    ValidationFailed(String),
}

pub type Result<T> = std::result::Result<T, SemanticConventionError>;

/// Helper trait to convert values to AttributeValue
pub trait ToAttributeValue {
    fn to_attribute_value(self) -> AttributeValue;
}

impl ToAttributeValue for String {
    fn to_attribute_value(self) -> AttributeValue {
        AttributeValue::String(self)
    }
}

impl ToAttributeValue for &str {
    fn to_attribute_value(self) -> AttributeValue {
        AttributeValue::String(self.to_string())
    }
}

impl ToAttributeValue for i64 {
    fn to_attribute_value(self) -> AttributeValue {
        AttributeValue::Int(self)
    }
}

impl ToAttributeValue for u16 {
    fn to_attribute_value(self) -> AttributeValue {
        AttributeValue::Int(self as i64)
    }
}

impl ToAttributeValue for f64 {
    fn to_attribute_value(self) -> AttributeValue {
        AttributeValue::Double(self)
    }
}

impl ToAttributeValue for bool {
    fn to_attribute_value(self) -> AttributeValue {
        AttributeValue::Bool(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_attribute_value_display() {
        assert_eq!(AttributeValue::String("test".to_string()).to_string(), "test");
        assert_eq!(AttributeValue::Int(42).to_string(), "42");
        assert_eq!(AttributeValue::Double(3.14).to_string(), "3.14");
        assert_eq!(AttributeValue::Bool(true).to_string(), "true");
    }

    #[test]
    fn test_to_attribute_value() {
        let str_val = "test".to_attribute_value();
        assert_eq!(str_val, AttributeValue::String("test".to_string()));
        
        let int_val = 42i64.to_attribute_value();
        assert_eq!(int_val, AttributeValue::Int(42));
    }
}

