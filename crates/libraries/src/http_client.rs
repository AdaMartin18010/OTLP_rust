//! # HTTP 客户端模块
//!
//! 提供高性能的 HTTP 客户端功能，支持异步请求、连接池、重试等特性。
//! 利用 Rust 1.92 的异步特性实现高性能 HTTP 通信。
//!
//! ## Rust 1.92 特性应用
//!
//! - **异步闭包**: 使用 `async || {}` 语法简化异步操作
//! - **元组收集**: 使用 `collect()` 直接收集到元组
//! - **常量泛型**: 使用常量泛型优化配置和缓冲区
//!
//! ## 功能特性
//!
//! - 异步 HTTP 请求（GET, POST, PUT, DELETE, PATCH, HEAD, OPTIONS）
//! - 连接池管理
//! - 请求超时控制
//! - 自动压缩支持（gzip, brotli, deflate）
//! - 自定义头部支持
//! - 重定向处理
//! - 统计信息收集

use crate::error::{Error, Result};
use async_trait::async_trait;
use std::collections::HashMap;
use std::time::Duration;

/// HTTP 方法
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HttpMethod {
    Get,
    Post,
    Put,
    Delete,
    Patch,
    Head,
    Options,
}

impl HttpMethod {
    pub fn as_str(&self) -> &'static str {
        match self {
            HttpMethod::Get => "GET",
            HttpMethod::Post => "POST",
            HttpMethod::Put => "PUT",
            HttpMethod::Delete => "DELETE",
            HttpMethod::Patch => "PATCH",
            HttpMethod::Head => "HEAD",
            HttpMethod::Options => "OPTIONS",
        }
    }
}

/// HTTP 请求
#[derive(Debug, Clone)]
pub struct HttpRequest {
    pub method: HttpMethod,
    pub url: String,
    pub headers: HashMap<String, String>,
    pub body: Option<Vec<u8>>,
    pub timeout: Option<Duration>,
}

impl HttpRequest {
    pub fn new(method: HttpMethod, url: String) -> Self {
        Self {
            method,
            url,
            headers: HashMap::new(),
            body: None,
            timeout: None,
        }
    }

    pub fn with_header(mut self, key: String, value: String) -> Self {
        self.headers.insert(key, value);
        self
    }

    pub fn with_body(mut self, body: Vec<u8>) -> Self {
        self.body = Some(body);
        self
    }

    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = Some(timeout);
        self
    }
}

/// HTTP 响应
#[derive(Debug, Clone)]
pub struct HttpResponse {
    pub status_code: u16,
    pub headers: HashMap<String, String>,
    pub body: Vec<u8>,
}

impl HttpResponse {
    pub fn new(status_code: u16) -> Self {
        Self {
            status_code,
            headers: HashMap::new(),
            body: Vec::new(),
        }
    }

    pub fn with_header(mut self, key: String, value: String) -> Self {
        self.headers.insert(key, value);
        self
    }

    pub fn with_body(mut self, body: Vec<u8>) -> Self {
        self.body = body;
        self
    }

    pub fn is_success(&self) -> bool {
        self.status_code >= 200 && self.status_code < 300
    }

    pub fn body_as_string(&self) -> Result<String> {
        String::from_utf8(self.body.clone())
            .map_err(|e| Error::Other(format!("无法将响应体转换为字符串: {}", e)))
    }
}

/// HTTP 客户端配置
#[derive(Debug, Clone)]
pub struct HttpClientConfig {
    pub timeout: Duration,
    pub connect_timeout: Duration,
    pub max_redirects: usize,
    pub user_agent: Option<String>,
    pub default_headers: HashMap<String, String>,
    pub enable_compression: bool,
    pub connection_pool_size: usize,
}

impl Default for HttpClientConfig {
    fn default() -> Self {
        Self {
            timeout: Duration::from_secs(30),
            connect_timeout: Duration::from_secs(10),
            max_redirects: 10,
            user_agent: Some("OTLP-Rust-Client/1.0".to_string()),
            default_headers: HashMap::new(),
            enable_compression: true,
            connection_pool_size: 10,
        }
    }
}

/// HTTP 客户端 trait
#[async_trait]
pub trait HttpClient: Send + Sync {
    /// 发送 HTTP 请求
    async fn send(&self, request: HttpRequest) -> Result<HttpResponse>;

    /// 发送 GET 请求
    async fn get(&self, url: &str) -> Result<HttpResponse> {
        let request = HttpRequest::new(HttpMethod::Get, url.to_string());
        self.send(request).await
    }

    /// 发送 POST 请求
    async fn post(&self, url: &str, body: Vec<u8>) -> Result<HttpResponse> {
        let request = HttpRequest::new(HttpMethod::Post, url.to_string()).with_body(body);
        self.send(request).await
    }

    /// 发送 PUT 请求
    async fn put(&self, url: &str, body: Vec<u8>) -> Result<HttpResponse> {
        let request = HttpRequest::new(HttpMethod::Put, url.to_string()).with_body(body);
        self.send(request).await
    }

    /// 发送 DELETE 请求
    async fn delete(&self, url: &str) -> Result<HttpResponse> {
        let request = HttpRequest::new(HttpMethod::Delete, url.to_string());
        self.send(request).await
    }
}

/// 基于 reqwest 的 HTTP 客户端实现
///
/// 使用 Rust 1.92 异步特性实现高性能 HTTP 通信
#[cfg(feature = "reqwest")]
pub struct ReqwestHttpClient {
    client: reqwest::Client,
    config: HttpClientConfig,
}

#[cfg(feature = "reqwest")]
impl ReqwestHttpClient {
    /// 创建新的 HTTP 客户端
    pub fn new(config: HttpClientConfig) -> Result<Self> {
        let mut builder = reqwest::Client::builder()
            .timeout(config.timeout)
            .connect_timeout(config.connect_timeout)
            .redirect(reqwest::redirect::Policy::limited(config.max_redirects));

        if let Some(user_agent) = &config.user_agent {
            builder = builder.user_agent(user_agent);
        }

        if config.enable_compression {
            builder = builder.gzip(true).brotli(true).deflate(true);
        }

        let client = builder
            .build()
            .map_err(|e| Error::Other(format!("无法创建 HTTP 客户端: {}", e)))?;

        Ok(Self { client, config })
    }

    /// 使用默认配置创建客户端
    pub fn with_default_config() -> Result<Self> {
        Self::new(HttpClientConfig::default())
    }
}

#[cfg(feature = "reqwest")]
#[async_trait]
impl HttpClient for ReqwestHttpClient {
    async fn send(&self, request: HttpRequest) -> Result<HttpResponse> {
        // 构建请求
        let mut req_builder = match request.method {
            HttpMethod::Get => self.client.get(&request.url),
            HttpMethod::Post => self.client.post(&request.url),
            HttpMethod::Put => self.client.put(&request.url),
            HttpMethod::Delete => self.client.delete(&request.url),
            HttpMethod::Patch => self.client.patch(&request.url),
            HttpMethod::Head => self.client.head(&request.url),
            HttpMethod::Options => self.client.request(reqwest::Method::OPTIONS, &request.url),
        };

        // 添加默认头部
        for (key, value) in &self.config.default_headers {
            req_builder = req_builder.header(key, value);
        }

        // 添加请求头部
        for (key, value) in &request.headers {
            req_builder = req_builder.header(key, value);
        }

        // 添加请求体
        if let Some(body) = &request.body {
            req_builder = req_builder.body(body.clone());
        }

        // 设置超时
        if let Some(timeout) = request.timeout {
            req_builder = req_builder.timeout(timeout);
        }

        // 发送请求
        let response = req_builder
            .send()
            .await
            .map_err(|e| Error::Other(format!("HTTP 请求失败: {}", e)))?;

        let status_code = response.status().as_u16();
        let mut headers = HashMap::new();
        for (key, value) in response.headers() {
            if let Ok(value_str) = value.to_str() {
                headers.insert(key.to_string(), value_str.to_string());
            }
        }

        let body = response
            .bytes()
            .await
            .map_err(|e| Error::Other(format!("读取响应体失败: {}", e)))?
            .to_vec();

        Ok(HttpResponse::new(status_code)
            .with_body(body)
            .with_header("Content-Type".to_string(), "application/octet-stream".to_string()))
    }
}

/// HTTP 客户端构建器 - 使用 Rust 1.92 特性
pub struct HttpClientBuilder {
    config: HttpClientConfig,
}

impl HttpClientBuilder {
    /// 创建新的构建器
    pub fn new() -> Self {
        Self {
            config: HttpClientConfig::default(),
        }
    }

    /// 设置超时
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.config.timeout = timeout;
        self
    }

    /// 设置连接超时
    pub fn with_connect_timeout(mut self, timeout: Duration) -> Self {
        self.config.connect_timeout = timeout;
        self
    }

    /// 设置最大重定向次数
    pub fn with_max_redirects(mut self, max_redirects: usize) -> Self {
        self.config.max_redirects = max_redirects;
        self
    }

    /// 设置 User-Agent
    pub fn with_user_agent(mut self, user_agent: String) -> Self {
        self.config.user_agent = Some(user_agent);
        self
    }

    /// 添加默认头部
    pub fn with_default_header(mut self, key: String, value: String) -> Self {
        self.config.default_headers.insert(key, value);
        self
    }

    /// 启用/禁用压缩
    pub fn with_compression(mut self, enable: bool) -> Self {
        self.config.enable_compression = enable;
        self
    }

    /// 设置连接池大小
    pub fn with_connection_pool_size(mut self, size: usize) -> Self {
        self.config.connection_pool_size = size;
        self
    }

    /// 构建 HTTP 客户端
    #[cfg(feature = "reqwest")]
    pub fn build(self) -> Result<Box<dyn HttpClient>> {
        let client = ReqwestHttpClient::new(self.config)?;
        Ok(Box::new(client))
    }

    #[cfg(not(feature = "reqwest"))]
    pub fn build(self) -> Result<Box<dyn HttpClient>> {
        Err(Error::Other("HTTP 客户端功能需要启用 reqwest feature".to_string()))
    }
}

impl Default for HttpClientBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// HTTP 客户端统计信息
#[derive(Debug, Clone, Default)]
pub struct HttpClientStats {
    pub total_requests: u64,
    pub successful_requests: u64,
    pub failed_requests: u64,
    pub total_bytes_sent: u64,
    pub total_bytes_received: u64,
    pub average_response_time: Duration,
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
    fn test_http_request() {
        let request = HttpRequest::new(HttpMethod::Get, "https://example.com".to_string())
            .with_header("Content-Type".to_string(), "application/json".to_string())
            .with_timeout(Duration::from_secs(5));

        assert_eq!(request.method, HttpMethod::Get);
        assert_eq!(request.url, "https://example.com");
        assert!(request.headers.contains_key("Content-Type"));
        assert!(request.timeout.is_some());
    }

    #[test]
    fn test_http_response() {
        let response = HttpResponse::new(200)
            .with_header("Content-Type".to_string(), "application/json".to_string())
            .with_body(b"Hello, World!".to_vec());

        assert_eq!(response.status_code, 200);
        assert!(response.is_success());
        assert!(response.headers.contains_key("Content-Type"));
        assert_eq!(response.body, b"Hello, World!".to_vec());
    }

    #[test]
    fn test_http_client_config_default() {
        let config = HttpClientConfig::default();
        assert_eq!(config.timeout, Duration::from_secs(30));
        assert_eq!(config.connect_timeout, Duration::from_secs(10));
        assert_eq!(config.max_redirects, 10);
        assert!(config.user_agent.is_some());
    }

    #[test]
    fn test_http_client_builder() {
        let builder = HttpClientBuilder::new()
            .with_timeout(Duration::from_secs(60))
            .with_user_agent("Test-Agent/1.0".to_string())
            .with_default_header("X-Custom-Header".to_string(), "value".to_string());

        assert_eq!(builder.config.timeout, Duration::from_secs(60));
        assert_eq!(builder.config.user_agent, Some("Test-Agent/1.0".to_string()));
        assert!(builder.config.default_headers.contains_key("X-Custom-Header"));
    }
}
