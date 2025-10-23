//! # HTTP Semantic Conventions
//!
//! Implementation of OpenTelemetry HTTP Semantic Conventions v1.29.0
//! https://opentelemetry.io/docs/specs/semconv/http/

use super::common::*;
use std::collections::HashMap;

/// HTTP request methods
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HttpMethod {
    Get,
    Post,
    Put,
    Delete,
    Head,
    Options,
    Patch,
    Trace,
    Connect,
}

impl HttpMethod {
    pub fn as_str(&self) -> &'static str {
        match self {
            HttpMethod::Get => "GET",
            HttpMethod::Post => "POST",
            HttpMethod::Put => "PUT",
            HttpMethod::Delete => "DELETE",
            HttpMethod::Head => "HEAD",
            HttpMethod::Options => "OPTIONS",
            HttpMethod::Patch => "PATCH",
            HttpMethod::Trace => "TRACE",
            HttpMethod::Connect => "CONNECT",
        }
    }
}

/// URL scheme
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HttpScheme {
    Http,
    Https,
}

impl HttpScheme {
    pub fn as_str(&self) -> &'static str {
        match self {
            HttpScheme::Http => "http",
            HttpScheme::Https => "https",
        }
    }
}

/// HTTP attributes following OpenTelemetry conventions
#[derive(Debug, Clone)]
pub struct HttpAttributes {
    attributes: AttributeMap,
}

impl HttpAttributes {
    /// Get all attributes as a map
    pub fn as_map(&self) -> &AttributeMap {
        &self.attributes
    }
    
    /// Get a specific attribute
    pub fn get(&self, key: &str) -> Option<&AttributeValue> {
        self.attributes.get(key)
    }
}

/// Builder for HTTP attributes
#[derive(Debug, Default)]
pub struct HttpAttributesBuilder {
    // Required attributes
    method: Option<HttpMethod>,
    
    // Common attributes
    url: Option<String>,
    status_code: Option<u16>,
    
    // Request attributes
    request_body_size: Option<i64>,
    request_header_content_length: Option<i64>,
    
    // Response attributes
    response_body_size: Option<i64>,
    response_header_content_length: Option<i64>,
    
    // URL components
    url_scheme: Option<HttpScheme>,
    url_path: Option<String>,
    url_query: Option<String>,
    url_fragment: Option<String>,
    
    // Server attributes
    server_address: Option<String>,
    server_port: Option<u16>,
    
    // Network attributes
    network_protocol_name: Option<String>,
    network_protocol_version: Option<String>,
    network_peer_address: Option<String>,
    network_peer_port: Option<u16>,
    
    // User agent
    user_agent_original: Option<String>,
    
    // Custom attributes
    custom: HashMap<String, AttributeValue>,
}

impl HttpAttributesBuilder {
    /// Create a new builder
    pub fn new() -> Self {
        Self::default()
    }
    
    /// Set HTTP method (required)
    pub fn method(mut self, method: HttpMethod) -> Self {
        self.method = Some(method);
        self
    }
    
    /// Set full URL
    pub fn url(mut self, url: impl Into<String>) -> Self {
        self.url = Some(url.into());
        self
    }
    
    /// Set HTTP status code
    pub fn status_code(mut self, code: u16) -> Self {
        self.status_code = Some(code);
        self
    }
    
    /// Set request body size in bytes
    pub fn request_body_size(mut self, size: i64) -> Self {
        self.request_body_size = Some(size);
        self
    }
    
    /// Set response body size in bytes
    pub fn response_body_size(mut self, size: i64) -> Self {
        self.response_body_size = Some(size);
        self
    }
    
    /// Set URL scheme
    pub fn url_scheme(mut self, scheme: HttpScheme) -> Self {
        self.url_scheme = Some(scheme);
        self
    }
    
    /// Set URL path
    pub fn url_path(mut self, path: impl Into<String>) -> Self {
        self.url_path = Some(path.into());
        self
    }
    
    /// Set URL query string
    pub fn url_query(mut self, query: impl Into<String>) -> Self {
        self.url_query = Some(query.into());
        self
    }
    
    /// Set server address
    pub fn server_address(mut self, address: impl Into<String>) -> Self {
        self.server_address = Some(address.into());
        self
    }
    
    /// Set server port
    pub fn server_port(mut self, port: u16) -> Self {
        self.server_port = Some(port);
        self
    }
    
    /// Set network protocol name (e.g., "http", "spdy")
    pub fn network_protocol_name(mut self, name: impl Into<String>) -> Self {
        self.network_protocol_name = Some(name.into());
        self
    }
    
    /// Set network protocol version (e.g., "1.1", "2", "3")
    pub fn network_protocol_version(mut self, version: impl Into<String>) -> Self {
        self.network_protocol_version = Some(version.into());
        self
    }
    
    /// Set user agent string
    pub fn user_agent(mut self, ua: impl Into<String>) -> Self {
        self.user_agent_original = Some(ua.into());
        self
    }
    
    /// Add a custom attribute
    pub fn custom_attribute(mut self, key: String, value: AttributeValue) -> Self {
        self.custom.insert(key, value);
        self
    }
    
    /// Build the HTTP attributes
    pub fn build(self) -> Result<HttpAttributes> {
        // Validate required fields
        let method = self.method.ok_or_else(|| {
            SemanticConventionError::MissingRequired("http.request.method".to_string())
        })?;
        
        let mut attributes = AttributeMap::new();
        
        // Required attributes
        attributes.insert(
            "http.request.method".to_string(),
            AttributeValue::String(method.as_str().to_string()),
        );
        
        // Optional attributes
        if let Some(url) = self.url {
            attributes.insert("url.full".to_string(), AttributeValue::String(url));
        }
        
        if let Some(status_code) = self.status_code {
            attributes.insert(
                "http.response.status_code".to_string(),
                AttributeValue::Int(status_code as i64),
            );
        }
        
        if let Some(size) = self.request_body_size {
            attributes.insert("http.request.body.size".to_string(), AttributeValue::Int(size));
        }
        
        if let Some(size) = self.response_body_size {
            attributes.insert("http.response.body.size".to_string(), AttributeValue::Int(size));
        }
        
        if let Some(scheme) = self.url_scheme {
            attributes.insert(
                "url.scheme".to_string(),
                AttributeValue::String(scheme.as_str().to_string()),
            );
        }
        
        if let Some(path) = self.url_path {
            attributes.insert("url.path".to_string(), AttributeValue::String(path));
        }
        
        if let Some(query) = self.url_query {
            attributes.insert("url.query".to_string(), AttributeValue::String(query));
        }
        
        if let Some(address) = self.server_address {
            attributes.insert("server.address".to_string(), AttributeValue::String(address));
        }
        
        if let Some(port) = self.server_port {
            attributes.insert("server.port".to_string(), AttributeValue::Int(port as i64));
        }
        
        if let Some(proto_name) = self.network_protocol_name {
            attributes.insert(
                "network.protocol.name".to_string(),
                AttributeValue::String(proto_name),
            );
        }
        
        if let Some(proto_ver) = self.network_protocol_version {
            attributes.insert(
                "network.protocol.version".to_string(),
                AttributeValue::String(proto_ver),
            );
        }
        
        if let Some(ua) = self.user_agent_original {
            attributes.insert("user_agent.original".to_string(), AttributeValue::String(ua));
        }
        
        // Add custom attributes
        attributes.extend(self.custom);
        
        Ok(HttpAttributes { attributes })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_http_method() {
        assert_eq!(HttpMethod::Get.as_str(), "GET");
        assert_eq!(HttpMethod::Post.as_str(), "POST");
    }

    #[test]
    fn test_http_scheme() {
        assert_eq!(HttpScheme::Http.as_str(), "http");
        assert_eq!(HttpScheme::Https.as_str(), "https");
    }

    #[test]
    fn test_http_attributes_builder_minimal() {
        let attrs = HttpAttributesBuilder::new()
            .method(HttpMethod::Get)
            .build()
            .unwrap();
        
        assert_eq!(
            attrs.get("http.request.method"),
            Some(&AttributeValue::String("GET".to_string()))
        );
    }

    #[test]
    fn test_http_attributes_builder_full() {
        let attrs = HttpAttributesBuilder::new()
            .method(HttpMethod::Post)
            .url("https://api.example.com/users")
            .status_code(201)
            .request_body_size(1024)
            .response_body_size(512)
            .url_scheme(HttpScheme::Https)
            .url_path("/users")
            .server_address("api.example.com")
            .server_port(443)
            .network_protocol_name("http")
            .network_protocol_version("2")
            .user_agent("Mozilla/5.0")
            .build()
            .unwrap();
        
        assert_eq!(
            attrs.get("http.request.method"),
            Some(&AttributeValue::String("POST".to_string()))
        );
        assert_eq!(
            attrs.get("http.response.status_code"),
            Some(&AttributeValue::Int(201))
        );
        assert_eq!(
            attrs.get("url.scheme"),
            Some(&AttributeValue::String("https".to_string()))
        );
    }

    #[test]
    fn test_http_attributes_builder_missing_required() {
        let result = HttpAttributesBuilder::new().build();
        
        assert!(result.is_err());
        match result {
            Err(SemanticConventionError::MissingRequired(field)) => {
                assert_eq!(field, "http.request.method");
            }
            _ => panic!("Expected MissingRequired error"),
        }
    }
}

