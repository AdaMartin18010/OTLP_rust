# 结构化日志 - Rust 完整版

## 目录

- [结构化日志 - Rust 完整版](#结构化日志---rust-完整版)
  - [目录](#目录)
  - [1. 结构化日志概述](#1-结构化日志概述)
    - [1.1 什么是结构化日志](#11-什么是结构化日志)
    - [1.2 优势](#12-优势)
  - [2. 字段类型](#2-字段类型)
    - [2.1 基础类型](#21-基础类型)
    - [2.2 复杂类型](#22-复杂类型)
  - [3. tracing 结构化日志](#3-tracing-结构化日志)
    - [3.1 基础使用](#31-基础使用)
    - [3.2 字段记录](#32-字段记录)
    - [3.3 Span 字段](#33-span-字段)
  - [4. JSON 日志](#4-json-日志)
    - [4.1 JSON 格式化](#41-json-格式化)
    - [4.2 自定义序列化](#42-自定义序列化)
  - [5. 字段标准化](#5-字段标准化)
    - [5.1 通用字段](#51-通用字段)
    - [5.2 HTTP 字段](#52-http-字段)
    - [5.3 数据库字段](#53-数据库字段)
    - [5.4 错误字段](#54-错误字段)
  - [6. OpenTelemetry Logs](#6-opentelemetry-logs)
    - [6.1 Logs Bridge](#61-logs-bridge)
    - [6.2 日志导出](#62-日志导出)
  - [7. 日志聚合](#7-日志聚合)
    - [7.1 ELK Stack](#71-elk-stack)
    - [7.2 Loki](#72-loki)
    - [7.3 CloudWatch Logs](#73-cloudwatch-logs)
  - [8. 最佳实践](#8-最佳实践)
    - [8.1 字段命名](#81-字段命名)
    - [8.2 日志级别](#82-日志级别)
    - [8.3 性能优化](#83-性能优化)
  - [9. 安全性](#9-安全性)
    - [9.1 敏感信息过滤](#91-敏感信息过滤)
    - [9.2 PII 处理](#92-pii-处理)
  - [10. 完整示例](#10-完整示例)
    - [10.1 Web 应用日志](#101-web-应用日志)
    - [10.2 微服务日志](#102-微服务日志)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [字段标准对比](#字段标准对比)
    - [最佳实践清单](#最佳实践清单)

---

## 1. 结构化日志概述

### 1.1 什么是结构化日志

````text
结构化日志 vs 非结构化日志:

非结构化日志 (传统):
2025-10-09 12:34:56 INFO User john_doe logged in from 192.168.1.100

结构化日志 (JSON):
{
  "timestamp": "2025-10-09T12:34:56.123Z",
  "level": "INFO",
  "message": "User logged in",
  "user_id": 12345,
  "username": "john_doe",
  "ip_address": "192.168.1.100",
  "trace_id": "4bf92f3577b34da6a3ce929d0e0e4736",
  "span_id": "00f067aa0ba902b7"
}

优势:
1. 可查询: 按字段搜索
2. 可聚合: 按字段统计
3. 可关联: Trace ID 关联
4. 可分析: 机器可读
````

### 1.2 优势

````text
结构化日志的优势:

1. 查询效率
   - SELECT * WHERE user_id = 12345
   - 比文本搜索快 10-100x

2. 聚合分析
   - COUNT(*) GROUP BY status_code
   - 实时统计和监控

3. 多维度分析
   - 按用户、按接口、按错误类型
   - 灵活的数据透视

4. 自动化处理
   - 告警规则
   - 自动化运维
   - 异常检测

5. 关联追踪
   - Trace ID → 查询所有相关日志
   - 分布式追踪完整视图
````

---

## 2. 字段类型

### 2.1 基础类型

````rust
use tracing::{info, warn, error};

/// 基础类型字段
pub fn log_basic_types() {
    // 字符串
    info!(message = "User logged in", "Processing request");
    
    // 数字
    info!(user_id = 12345, status_code = 200, "Request completed");
    
    // 布尔值
    info!(is_admin = true, authenticated = false, "Access check");
    
    // 浮点数
    info!(latency_ms = 123.45, cpu_usage = 0.85, "Performance metrics");
}
````

### 2.2 复杂类型

````rust
use serde::Serialize;

#[derive(Serialize)]
pub struct User {
    pub id: u64,
    pub username: String,
    pub email: String,
}

#[derive(Serialize)]
pub struct RequestMetadata {
    pub method: String,
    pub path: String,
    pub query_params: Vec<(String, String)>,
}

/// 复杂类型字段
pub fn log_complex_types() {
    let user = User {
        id: 12345,
        username: "john_doe".to_string(),
        email: "john@example.com".to_string(),
    };
    
    // 使用 serde 序列化
    info!(user = ?user, "User logged in");
    
    // 使用 Display
    info!(user = %user.username, "Processing request");
    
    // 数组
    let tags = vec!["api", "authentication", "success"];
    info!(tags = ?tags, "Request tagged");
    
    // 嵌套对象
    let metadata = RequestMetadata {
        method: "POST".to_string(),
        path: "/api/login".to_string(),
        query_params: vec![
            ("redirect".to_string(), "/dashboard".to_string()),
        ],
    };
    info!(metadata = ?metadata, "Request metadata");
}
````

---

## 3. tracing 结构化日志

### 3.1 基础使用

````rust
use tracing::{info, warn, error, debug, trace};

/// tracing 基础使用
pub fn tracing_basics() {
    // 简单消息
    info!("Server started");
    
    // 带字段的日志
    info!(
        port = 8080,
        environment = "production",
        "Server listening"
    );
    
    // 多个字段
    info!(
        user_id = 12345,
        action = "login",
        ip = "192.168.1.100",
        timestamp = chrono::Utc::now().to_rfc3339(),
        "User action"
    );
    
    // 使用变量
    let user_id = 12345;
    let username = "john_doe";
    info!(user_id, username, "User logged in");
}
````

### 3.2 字段记录

````rust
use tracing::{info, Span};

/// 字段记录
pub fn record_fields() {
    let span = tracing::info_span!(
        "process_order",
        order_id = tracing::field::Empty,  // 稍后填充
        amount = tracing::field::Empty,
    );
    
    let _guard = span.enter();
    
    // 稍后记录字段
    span.record("order_id", "ORD-12345");
    span.record("amount", 99.99);
    
    info!("Order processed");
}

/// 条件字段记录
pub fn conditional_fields(is_debug: bool) {
    if is_debug {
        info!(
            debug_info = "Detailed information",
            stack_trace = "...",
            "Debug logging"
        );
    } else {
        info!("Normal logging");
    }
}
````

### 3.3 Span 字段

````rust
use tracing::{info, instrument};

#[instrument(
    name = "process_payment",
    skip(payment),
    fields(
        payment.id = %payment.id,
        payment.amount = payment.amount,
        payment.currency = %payment.currency,
    )
)]
pub async fn process_payment(payment: Payment) -> Result<(), anyhow::Error> {
    info!("Processing payment");
    
    // Span 字段自动记录
    // payment.id, payment.amount, payment.currency
    
    Ok(())
}

pub struct Payment {
    pub id: String,
    pub amount: f64,
    pub currency: String,
}
````

---

## 4. JSON 日志

### 4.1 JSON 格式化

````rust
use tracing_subscriber::{fmt, EnvFilter};

/// 初始化 JSON 日志
pub fn init_json_logging() {
    fmt()
        .with_env_filter(EnvFilter::from_default_env())
        .json()  // JSON 格式
        .with_current_span(true)  // 包含 Span 信息
        .with_span_list(true)     // 包含 Span 列表
        .with_target(true)        // 包含日志来源
        .with_thread_ids(true)    // 包含线程 ID
        .with_file(true)          // 包含文件名
        .with_line_number(true)   // 包含行号
        .init();
}
````

**JSON 输出示例**:

````json
{
  "timestamp": "2025-10-09T12:34:56.123456Z",
  "level": "INFO",
  "target": "my_app::api",
  "fields": {
    "message": "User logged in",
    "user_id": 12345,
    "username": "john_doe",
    "ip_address": "192.168.1.100"
  },
  "span": {
    "name": "handle_login",
    "request_id": "req-abc123"
  },
  "spans": [
    {
      "name": "http_server",
      "method": "POST",
      "path": "/api/login"
    },
    {
      "name": "handle_login"
    }
  ],
  "threadId": "ThreadId(1)",
  "file": "src/api/auth.rs",
  "line": 42
}
````

### 4.2 自定义序列化

````rust
use serde::Serialize;
use tracing_subscriber::fmt::format::json;

#[derive(Serialize)]
pub struct CustomLogEntry {
    pub timestamp: String,
    pub level: String,
    pub message: String,
    pub context: serde_json::Value,
}

/// 自定义 JSON 序列化
pub fn custom_json_format() {
    use tracing_subscriber::fmt::format;
    
    fmt()
        .json()
        .with_timer(format::time::SystemTime)
        .flatten_event(true)  // 扁平化事件
        .init();
}
````

---

## 5. 字段标准化

### 5.1 通用字段

````rust
/// 通用字段标准
pub mod common_fields {
    // 时间戳
    pub const TIMESTAMP: &str = "timestamp";
    
    // 日志级别
    pub const LEVEL: &str = "level";
    
    // 消息
    pub const MESSAGE: &str = "message";
    
    // Trace 上下文
    pub const TRACE_ID: &str = "trace_id";
    pub const SPAN_ID: &str = "span_id";
    
    // 服务信息
    pub const SERVICE_NAME: &str = "service.name";
    pub const SERVICE_VERSION: &str = "service.version";
    
    // 环境信息
    pub const ENVIRONMENT: &str = "environment";
    pub const HOST_NAME: &str = "host.name";
}

use tracing::info;

pub fn log_with_common_fields() {
    info!(
        timestamp = chrono::Utc::now().to_rfc3339(),
        level = "INFO",
        message = "Request processed",
        trace_id = "4bf92f3577b34da6a3ce929d0e0e4736",
        span_id = "00f067aa0ba902b7",
        "service.name" = "order-service",
        "service.version" = "1.2.3",
        environment = "production",
        "host.name" = "server-01",
    );
}
````

### 5.2 HTTP 字段

````rust
/// HTTP 字段标准
pub mod http_fields {
    // 请求
    pub const METHOD: &str = "http.method";
    pub const TARGET: &str = "http.target";
    pub const SCHEME: &str = "http.scheme";
    pub const HOST: &str = "http.host";
    pub const USER_AGENT: &str = "http.user_agent";
    
    // 响应
    pub const STATUS_CODE: &str = "http.status_code";
    pub const RESPONSE_SIZE: &str = "http.response.size";
    
    // 客户端
    pub const CLIENT_IP: &str = "http.client_ip";
}

pub fn log_http_request(
    method: &str,
    path: &str,
    status_code: u16,
    client_ip: &str,
) {
    info!(
        "http.method" = method,
        "http.target" = path,
        "http.status_code" = status_code,
        "http.client_ip" = client_ip,
        "HTTP request completed"
    );
}
````

### 5.3 数据库字段

````rust
/// 数据库字段标准
pub mod db_fields {
    pub const SYSTEM: &str = "db.system";         // postgresql, mysql, redis
    pub const NAME: &str = "db.name";             // 数据库名
    pub const STATEMENT: &str = "db.statement";   // SQL 语句
    pub const OPERATION: &str = "db.operation";   // SELECT, INSERT, UPDATE
    pub const TABLE: &str = "db.table";           // 表名
    pub const ROWS_AFFECTED: &str = "db.rows_affected";
    pub const DURATION_MS: &str = "db.duration_ms";
}

pub fn log_db_query(
    statement: &str,
    rows: u64,
    duration_ms: f64,
) {
    info!(
        "db.system" = "postgresql",
        "db.statement" = statement,
        "db.rows_affected" = rows,
        "db.duration_ms" = duration_ms,
        "Database query executed"
    );
}
````

### 5.4 错误字段

````rust
/// 错误字段标准
pub mod error_fields {
    pub const TYPE: &str = "error.type";
    pub const MESSAGE: &str = "error.message";
    pub const STACK_TRACE: &str = "error.stack_trace";
    pub const CODE: &str = "error.code";
}

pub fn log_error(error: &anyhow::Error) {
    error!(
        "error.type" = std::any::type_name_of_val(error),
        "error.message" = %error,
        "error.stack_trace" = ?error,
        "Error occurred"
    );
}
````

---

## 6. OpenTelemetry Logs

### 6.1 Logs Bridge

````rust
use opentelemetry::logs::{LoggerProvider, Severity};
use opentelemetry_sdk::logs::{Config, LoggerProvider as SdkLoggerProvider};
use tracing_subscriber::{layer::SubscriberExt, Registry};

/// 初始化 OpenTelemetry Logs
pub fn init_otlp_logs() -> Result<(), Box<dyn std::error::Error>> {
    // 创建 OTLP Exporter
    let exporter = opentelemetry_otlp::LogExporter::builder()
        .with_tonic()
        .with_endpoint("http://localhost:4317")
        .build()?;
    
    // 创建 LoggerProvider
    let logger_provider = SdkLoggerProvider::builder()
        .with_config(Config::default())
        .with_simple_exporter(exporter)
        .build();
    
    // 设置全局 LoggerProvider
    opentelemetry::global::set_logger_provider(logger_provider);
    
    // 创建 OpenTelemetry Layer
    let otel_layer = tracing_opentelemetry::OpenTelemetryLayer::new(
        opentelemetry::global::logger_provider().logger("my-app")
    );
    
    // 组合 Subscriber
    let subscriber = Registry::default()
        .with(tracing_subscriber::fmt::layer().json())
        .with(otel_layer);
    
    tracing::subscriber::set_global_default(subscriber)?;
    
    Ok(())
}
````

### 6.2 日志导出

````rust
use opentelemetry::logs::{Logger, LogRecord, Severity};

/// 直接使用 OpenTelemetry Logger
pub fn log_with_otlp() {
    let logger = opentelemetry::global::logger("my-app");
    
    let mut record = LogRecord::default();
    record.set_severity_text("INFO");
    record.set_severity_number(Severity::Info);
    record.set_body("User logged in".into());
    
    // 添加属性
    record.add_attribute("user_id", 12345);
    record.add_attribute("username", "john_doe");
    
    logger.emit(record);
}
````

---

## 7. 日志聚合

### 7.1 ELK Stack

````yaml
# Filebeat 配置 (filebeat.yml)
filebeat.inputs:
  - type: log
    enabled: true
    paths:
      - /var/log/my-app/*.log
    json.keys_under_root: true
    json.add_error_key: true

output.elasticsearch:
  hosts: ["localhost:9200"]
  index: "my-app-%{+yyyy.MM.dd}"

# Kibana 索引模板
setup.kibana:
  host: "localhost:5601"
````

**Elasticsearch 查询**:

````json
POST /my-app-*/_search
{
  "query": {
    "bool": {
      "must": [
        { "term": { "level": "ERROR" } },
        { "range": { "timestamp": { "gte": "now-1h" } } }
      ]
    }
  },
  "aggs": {
    "by_error_type": {
      "terms": { "field": "error.type" }
    }
  }
}
````

### 7.2 Loki

````yaml
# Promtail 配置 (promtail.yml)
server:
  http_listen_port: 9080

positions:
  filename: /tmp/positions.yaml

clients:
  - url: http://localhost:3100/loki/api/v1/push

scrape_configs:
  - job_name: my-app
    static_configs:
      - targets:
          - localhost
        labels:
          job: my-app
          __path__: /var/log/my-app/*.log
    pipeline_stages:
      - json:
          expressions:
            level: level
            message: message
            trace_id: trace_id
      - labels:
          level:
          trace_id:
````

**LogQL 查询**:

````logql
# 查询所有错误日志
{job="my-app"} | json | level="ERROR"

# 按 Trace ID 查询
{job="my-app"} | json | trace_id="4bf92f3577b34da6a3ce929d0e0e4736"

# 统计错误数量
sum(rate({job="my-app"} | json | level="ERROR" [5m]))
````

### 7.3 CloudWatch Logs

````rust
use aws_sdk_cloudwatchlogs::Client as CloudWatchClient;

/// 导出到 CloudWatch Logs
pub async fn export_to_cloudwatch(
    log_group: &str,
    log_stream: &str,
    message: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let config = aws_config::load_from_env().await;
    let client = CloudWatchClient::new(&config);
    
    client
        .put_log_events()
        .log_group_name(log_group)
        .log_stream_name(log_stream)
        .log_events(
            aws_sdk_cloudwatchlogs::types::InputLogEvent::builder()
                .timestamp(chrono::Utc::now().timestamp_millis())
                .message(message)
                .build()
                .unwrap()
        )
        .send()
        .await?;
    
    Ok(())
}
````

---

## 8. 最佳实践

### 8.1 字段命名

````text
字段命名规范:

1. 使用点号分隔命名空间
   ✅ http.method, db.statement, error.type
   ❌ httpMethod, dbStatement, errorType

2. 使用小写字母
   ✅ user_id, request_id
   ❌ UserId, RequestID

3. 使用下划线分隔单词
   ✅ user_id, order_id, created_at
   ❌ userid, orderid, createdat

4. 遵循语义约定
   ✅ 使用标准字段名 (OpenTelemetry Semantic Conventions)
   ❌ 自定义字段名 (除非必要)

5. 避免特殊字符
   ❌ user.name (点号可能被解析为嵌套)
   ✅ user_name 或 "user.name"
````

### 8.2 日志级别

````rust
use tracing::{trace, debug, info, warn, error};

/// 日志级别使用指南
pub fn logging_levels() {
    // TRACE: 非常详细的调试信息
    trace!(step = "validation", "Validating user input");
    
    // DEBUG: 调试信息
    debug!(cache_hit = true, "Cache lookup result");
    
    // INFO: 一般信息 (生产环境默认级别)
    info!(user_id = 12345, "User logged in");
    
    // WARN: 警告信息
    warn!(retry_count = 3, "Retry limit approaching");
    
    // ERROR: 错误信息
    error!(error = "Connection refused", "Failed to connect to database");
}
````

### 8.3 性能优化

````rust
/// 性能优化技巧
pub fn performance_optimization() {
    // 1. 使用条件日志
    if tracing::enabled!(tracing::Level::DEBUG) {
        let expensive_data = compute_expensive_data();
        debug!(data = ?expensive_data, "Debug information");
    }
    
    // 2. 延迟字段计算
    info!(
        user_id = tracing::field::display(lazy_user_id()),
        "User action"
    );
    
    // 3. 避免在热路径记录日志
    // ❌ 循环内记录日志
    for item in items {
        debug!(item_id = item.id, "Processing item");  // 性能问题
    }
    
    // ✅ 批量记录
    info!(item_count = items.len(), "Processing items");
}

fn compute_expensive_data() -> String {
    // 昂贵的计算
    "expensive data".to_string()
}

fn lazy_user_id() -> u64 {
    // 延迟计算
    12345
}
````

---

## 9. 安全性

### 9.1 敏感信息过滤

````rust
use tracing::info;

/// 敏感字段列表
const SENSITIVE_FIELDS: &[&str] = &[
    "password",
    "token",
    "api_key",
    "secret",
    "credit_card",
    "ssn",
];

/// 过滤敏感信息
pub fn sanitize_log(key: &str, value: &str) -> String {
    if SENSITIVE_FIELDS.iter().any(|&field| key.to_lowercase().contains(field)) {
        "***REDACTED***".to_string()
    } else {
        value.to_string()
    }
}

/// 安全日志记录
pub fn log_safely(user: &User) {
    info!(
        user_id = user.id,
        username = %user.username,
        // ❌ 不要记录密码
        // password = %user.password,
        "User information"
    );
}

pub struct User {
    pub id: u64,
    pub username: String,
    pub password: String,
}
````

### 9.2 PII 处理

````rust
/// PII (个人身份信息) 脱敏
pub fn mask_pii(value: &str, pii_type: &str) -> String {
    match pii_type {
        "email" => mask_email(value),
        "phone" => mask_phone(value),
        "credit_card" => mask_credit_card(value),
        _ => value.to_string(),
    }
}

fn mask_email(email: &str) -> String {
    if let Some(at_pos) = email.find('@') {
        let (local, domain) = email.split_at(at_pos);
        if local.len() > 2 {
            format!("{}***{}", &local[..2], domain)
        } else {
            format!("***{}", domain)
        }
    } else {
        "***".to_string()
    }
}

fn mask_phone(phone: &str) -> String {
    if phone.len() > 4 {
        format!("***{}", &phone[phone.len()-4..])
    } else {
        "***".to_string()
    }
}

fn mask_credit_card(card: &str) -> String {
    if card.len() > 4 {
        format!("****-****-****-{}", &card[card.len()-4..])
    } else {
        "****".to_string()
    }
}

pub fn log_with_pii_masking() {
    let email = "john.doe@example.com";
    let phone = "+1234567890";
    
    info!(
        email = mask_email(email),
        phone = mask_phone(phone),
        "User contact information"
    );
}
````

---

## 10. 完整示例

### 10.1 Web 应用日志

````rust
use axum::{
    extract::Request,
    middleware::{self, Next},
    response::Response,
    Router,
};
use tracing::{info, Span};
use uuid::Uuid;

/// HTTP 日志中间件
pub async fn logging_middleware(
    request: Request,
    next: Next,
) -> Response {
    let request_id = Uuid::new_v4().to_string();
    let method = request.method().to_string();
    let uri = request.uri().to_string();
    let client_ip = request
        .headers()
        .get("x-forwarded-for")
        .and_then(|v| v.to_str().ok())
        .unwrap_or("unknown");
    
    // 创建请求 Span
    let span = tracing::info_span!(
        "http_request",
        request_id = %request_id,
        "http.method" = %method,
        "http.target" = %uri,
        "http.client_ip" = %client_ip,
    );
    
    let _guard = span.enter();
    
    let start = std::time::Instant::now();
    
    info!("Request started");
    
    // 处理请求
    let response = next.run(request).await;
    
    let duration_ms = start.elapsed().as_millis();
    let status = response.status().as_u16();
    
    // 记录响应
    info!(
        "http.status_code" = status,
        "http.duration_ms" = duration_ms,
        "Request completed"
    );
    
    response
}
````

### 10.2 微服务日志

````rust
use tracing::{info, instrument};
use opentelemetry::trace::TraceContextExt;

#[instrument(
    name = "process_order",
    skip(order),
    fields(
        order.id = %order.id,
        order.amount = order.amount,
        order.status = tracing::field::Empty,
    )
)]
pub async fn process_order(order: Order) -> Result<(), anyhow::Error> {
    let span = Span::current();
    
    // 记录 Trace 上下文
    let context = opentelemetry::Context::current();
    let span_context = context.span().span_context();
    
    info!(
        trace_id = %span_context.trace_id(),
        span_id = %span_context.span_id(),
        "Processing order"
    );
    
    // 验证订单
    validate_order(&order).await?;
    span.record("order.status", "validated");
    
    // 处理支付
    process_payment(&order).await?;
    span.record("order.status", "payment_processed");
    
    // 更新库存
    update_inventory(&order).await?;
    span.record("order.status", "inventory_updated");
    
    info!(
        order.status = "completed",
        "Order completed successfully"
    );
    
    Ok(())
}

pub struct Order {
    pub id: String,
    pub amount: f64,
}

async fn validate_order(order: &Order) -> Result<(), anyhow::Error> {
    info!(order.id = %order.id, "Validating order");
    Ok(())
}

async fn process_payment(order: &Order) -> Result<(), anyhow::Error> {
    info!(order.id = %order.id, amount = order.amount, "Processing payment");
    Ok(())
}

async fn update_inventory(order: &Order) -> Result<(), anyhow::Error> {
    info!(order.id = %order.id, "Updating inventory");
    Ok(())
}
````

---

## 总结

### 核心要点

1. **结构化日志**: 机器可读的 JSON 格式
2. **字段标准化**: 遵循 OpenTelemetry Semantic Conventions
3. **Trace 关联**: 通过 trace_id/span_id 关联
4. **安全性**: 过滤敏感信息、PII 脱敏
5. **性能**: 条件日志、延迟计算
6. **聚合**: ELK、Loki、CloudWatch 集成

### 字段标准对比

| 类别 | 字段 | 示例值 |
|------|------|--------|
| 通用 | timestamp, level, message | 2025-10-09T12:34:56Z, INFO, User logged in |
| Trace | trace_id, span_id | 4bf92f3577b34da6a3ce929d0e0e4736, 00f067aa0ba902b7 |
| HTTP | http.method, http.status_code | POST, 200 |
| 数据库 | db.system, db.statement | postgresql, SELECT * FROM users |
| 错误 | error.type, error.message | SqlxError, Connection refused |
| 服务 | service.name, service.version | order-service, 1.2.3 |

### 最佳实践清单

- ✅ 使用 JSON 格式日志
- ✅ 遵循字段命名规范（点号分隔、小写）
- ✅ 包含 trace_id/span_id 实现关联
- ✅ 使用标准字段名（OpenTelemetry Semantic Conventions）
- ✅ 过滤敏感信息（password、token）
- ✅ PII 脱敏（email、phone、credit_card）
- ✅ 使用适当的日志级别
- ✅ 避免在热路径记录日志
- ✅ 使用条件日志（`tracing::enabled!`）
- ✅ 延迟字段计算
- ✅ 集成日志聚合系统（ELK、Loki）
- ❌ 不要记录明文密码
- ❌ 不要在循环中记录日志
- ❌ 不要使用非标准字段名

---

**相关文档**:

- [Logging 完整版](./01_Logging_Rust完整版.md)
- [分布式追踪进阶](./02_分布式追踪进阶_Rust完整版.md)
- [Logs 数据模型](../../01_数据模型/03_Logs_数据模型_Rust完整版.md)
- [安全最佳实践](../../07_安全与合规/00_Rust_OTLP_安全最佳实践_完整版.md)
