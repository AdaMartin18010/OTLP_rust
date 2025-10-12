# Anthropic Claude API 完整实现 - Rust 1.90 + OTLP 集成

## 目录

- [Anthropic Claude API 完整实现 - Rust 1.90 + OTLP 集成](#anthropic-claude-api-完整实现---rust-190--otlp-集成)
  - [目录](#目录)
  - [1. 核心概念与架构](#1-核心概念与架构)
    - [1.1 Claude 模型家族](#11-claude-模型家族)
    - [1.2 API 架构](#12-api-架构)
    - [1.3 国际标准对齐](#13-国际标准对齐)
  - [2. Rust 生态集成](#2-rust-生态集成)
    - [2.1 核心依赖](#21-核心依赖)
    - [2.2 项目结构](#22-项目结构)
  - [3. 基础API调用](#3-基础api调用)
    - [3.1 客户端初始化](#31-客户端初始化)
    - [3.2 消息API](#32-消息api)
    - [3.3 错误处理](#33-错误处理)
  - [4. Streaming 响应](#4-streaming-响应)
    - [4.1 SSE流式处理](#41-sse流式处理)
    - [4.2 实时响应](#42-实时响应)
    - [4.3 流式聚合](#43-流式聚合)
  - [5. Vision 能力](#5-vision-能力)
    - [5.1 图像输入](#51-图像输入)
    - [5.2 多模态处理](#52-多模态处理)
    - [5.3 PDF文档分析](#53-pdf文档分析)
  - [6. Function Calling](#6-function-calling)
    - [6.1 工具定义](#61-工具定义)
    - [6.2 工具执行](#62-工具执行)
    - [6.3 多轮对话](#63-多轮对话)
  - [7. 提示工程](#7-提示工程)
    - [7.1 System Prompt](#71-system-prompt)
    - [7.2 思维链](#72-思维链)
    - [7.3 Few-Shot Learning](#73-few-shot-learning)
  - [8. OTLP 可观测性](#8-otlp-可观测性)
    - [8.1 分布式追踪](#81-分布式追踪)
    - [8.2 指标监控](#82-指标监控)
    - [8.3 成本追踪](#83-成本追踪)
  - [9. 生产实践](#9-生产实践)
    - [9.1 速率限制](#91-速率限制)
    - [9.2 重试策略](#92-重试策略)
    - [9.3 缓存优化](#93-缓存优化)
  - [10. 测试策略](#10-测试策略)
  - [11. 参考资源](#11-参考资源)
    - [官方文档](#官方文档)
    - [Rust 生态](#rust-生态)
    - [国际标准](#国际标准)
    - [最佳实践](#最佳实践)

---

## 1. 核心概念与架构

### 1.1 Claude 模型家族

Anthropic Claude 提供多种模型,满足不同需求:

| 模型 | 能力 | 上下文 | 适用场景 |
|------|------|--------|----------|
| **Claude 3.5 Sonnet** | 最强能力 | 200K tokens | 复杂推理、代码生成、分析 |
| **Claude 3 Opus** | 最高智能 | 200K tokens | 研究、战略分析 |
| **Claude 3 Haiku** | 快速响应 | 200K tokens | 简单任务、实时交互 |
| **Claude 3 Sonnet** | 平衡性能 | 200K tokens | 通用任务 |

**核心特性**:

- ✅ **长上下文**: 200K tokens (约150K词)
- ✅ **Vision能力**: 图像理解与分析
- ✅ **Function Calling**: 工具使用与API集成
- ✅ **Streaming**: 实时流式响应
- ✅ **Constitutional AI**: 安全与对齐
- ✅ **多语言**: 支持中文等多种语言

### 1.2 API 架构

```text
┌─────────────────────────────────────────────────────────┐
│              Anthropic Claude API Architecture          │
│                                                         │
│  ┌────────────────────────────────────────────────────┐ │
│  │              Client Application                    │ │
│  │  ┌──────────────────────────────────────────────┐  │ │
│  │  │          Rust Claude Client                  │  │ │
│  │  │  - Authentication                            │  │ │
│  │  │  - Request Building                          │  │ │
│  │  │  - Response Parsing                          │  │ │
│  │  │  - Error Handling                            │  │ │
│  │  └──────────────────────────────────────────────┘  │ │
│  └────────────────────────────────────────────────────┘ │
│                          │                              │
│                          │ HTTPS                        │
│                          ▼                              │
│  ┌────────────────────────────────────────────────────┐ │
│  │          Anthropic API Gateway                     │ │
│  │  https://api.anthropic.com                         │ │
│  │                                                    │ │
│  │  ┌──────────────────────────────────────────────┐  │ │
│  │  │          API Endpoints                       │  │ │
│  │  │  - POST /v1/messages (Standard)              │  │ │
│  │  │  - POST /v1/messages (Streaming)             │  │ │
│  │  │  - POST /v1/complete (Legacy)                │  │ │
│  │  └──────────────────────────────────────────────┘  │ │
│  └────────────────────────────────────────────────────┘ │
│                          │                              │
│                          ▼                              │
│  ┌────────────────────────────────────────────────────┐ │
│  │          Claude Models                             │ │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐          │ │
│  │  │  Opus    │  │ Sonnet   │  │  Haiku   │          │ │
│  │  │  (Best)  │  │(Balanced)│  │  (Fast)  │          │ │
│  │  └──────────┘  └──────────┘  └──────────┘          │ │
│  └────────────────────────────────────────────────────┘ │
│                          │                              │
│                          ▼                              │
│  ┌────────────────────────────────────────────────────┐ │
│  │          Response Types                            │ │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐          │ │
│  │  │  Text    │  │  Image   │  │  Tool    │          │ │
│  │  │ Response │  │ Analysis │  │  Calls   │          │ │
│  │  └──────────┘  └──────────┘  └──────────┘          │ │
│  └────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────┘
```

### 1.3 国际标准对齐

| 标准/协议 | 应用场景 | Claude 实现 |
|-----------|----------|-------------|
| **HTTP/2 (RFC 7540)** | API通信 | REST API |
| **JSON (RFC 8259)** | 数据格式 | 请求/响应 |
| **SSE (Server-Sent Events)** | 流式传输 | Streaming |
| **OAuth 2.0 (RFC 6749)** | 认证授权 | API Key |
| **OpenTelemetry** | 可观测性 | 追踪与指标 |
| **Markdown** | 文本格式 | 响应格式 |
| **Base64 (RFC 4648)** | 图像编码 | Vision输入 |

---

## 2. Rust 生态集成

### 2.1 核心依赖

```toml
[package]
name = "claude-integration"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# HTTP 客户端
reqwest = { version = "0.12", features = ["json", "stream"] }
reqwest-eventsource = "0.6"

# 异步运行时
tokio = { version = "1.42", features = ["full"] }
tokio-stream = "0.1"
futures = "0.3"

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 错误处理
anyhow = "1.0"
thiserror = "2.0"

# OpenTelemetry (OTLP)
opentelemetry = "0.27"
opentelemetry-otlp = { version = "0.27", features = ["grpc-tonic", "metrics", "trace"] }
opentelemetry_sdk = { version = "0.27", features = ["rt-tokio"] }
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.28"

# Base64 (图像编码)
base64 = "0.22"

# 图像处理
image = "0.25"

# 速率限制
governor = "0.6"

# 时间处理
chrono = "0.4"

# 环境变量
dotenvy = "0.15"

# UUID
uuid = { version = "1.11", features = ["v4", "serde"] }
```

### 2.2 项目结构

```text
claude-integration/
├── src/
│   ├── main.rs                    # 入口
│   ├── client/
│   │   ├── mod.rs
│   │   ├── claude.rs              # Claude Client
│   │   └── config.rs              # 配置
│   ├── models/
│   │   ├── mod.rs
│   │   ├── message.rs             # Message API
│   │   ├── content.rs             # Content Types
│   │   └── tool.rs                # Tool Definitions
│   ├── streaming/
│   │   ├── mod.rs
│   │   └── sse.rs                 # SSE Stream
│   ├── vision/
│   │   ├── mod.rs
│   │   ├── image.rs               # 图像处理
│   │   └── pdf.rs                 # PDF处理
│   ├── function/
│   │   ├── mod.rs
│   │   ├── tool.rs                # 工具定义
│   │   └── executor.rs            # 工具执行
│   ├── prompt/
│   │   ├── mod.rs
│   │   ├── template.rs            # 提示模板
│   │   └── chain.rs               # 思维链
│   ├── observability/
│   │   ├── mod.rs
│   │   ├── tracing.rs             # 分布式追踪
│   │   └── metrics.rs             # 指标收集
│   ├── utils/
│   │   ├── mod.rs
│   │   ├── retry.rs               # 重试逻辑
│   │   └── cache.rs               # 缓存
│   └── error.rs                   # 错误定义
├── examples/
│   ├── basic_chat.rs
│   ├── streaming_chat.rs
│   ├── vision_analysis.rs
│   └── function_calling.rs
├── tests/
│   └── integration_test.rs
└── Cargo.toml
```

---

## 3. 基础API调用

### 3.1 客户端初始化

```rust
// src/client/claude.rs
use anyhow::Result;
use reqwest::Client;
use serde::{Deserialize, Serialize};
use tracing::{info, instrument};

/// Claude API Client
pub struct ClaudeClient {
    client: Client,
    api_key: String,
    base_url: String,
    default_model: ClaudeModel,
}

#[derive(Debug, Clone, Copy)]
pub enum ClaudeModel {
    Claude35Sonnet,
    Claude3Opus,
    Claude3Sonnet,
    Claude3Haiku,
}

impl ClaudeModel {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Claude35Sonnet => "claude-3-5-sonnet-20241022",
            Self::Claude3Opus => "claude-3-opus-20240229",
            Self::Claude3Sonnet => "claude-3-sonnet-20240229",
            Self::Claude3Haiku => "claude-3-haiku-20240307",
        }
    }
}

impl ClaudeClient {
    /// 创建新的 Claude 客户端
    #[instrument]
    pub fn new(api_key: String) -> Result<Self> {
        info!("Initializing Claude client");

        let client = Client::builder()
            .timeout(std::time::Duration::from_secs(120))
            .build()?;

        Ok(Self {
            client,
            api_key,
            base_url: "https://api.anthropic.com".to_string(),
            default_model: ClaudeModel::Claude35Sonnet,
        })
    }

    /// 设置默认模型
    pub fn with_model(mut self, model: ClaudeModel) -> Self {
        self.default_model = model;
        self
    }

    /// 从环境变量加载
    pub fn from_env() -> Result<Self> {
        let api_key = std::env::var("ANTHROPIC_API_KEY")
            .map_err(|_| anyhow::anyhow!("ANTHROPIC_API_KEY not set"))?;
        Self::new(api_key)
    }
}
```

### 3.2 消息API

```rust
// src/models/message.rs
use serde::{Deserialize, Serialize};

/// 消息请求
#[derive(Debug, Clone, Serialize)]
pub struct MessageRequest {
    pub model: String,
    pub messages: Vec<Message>,
    pub max_tokens: u32,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub system: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub temperature: Option<f32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub top_p: Option<f32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub top_k: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stop_sequences: Option<Vec<String>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stream: Option<bool>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Message {
    pub role: MessageRole,
    pub content: MessageContent,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum MessageRole {
    User,
    Assistant,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
pub enum MessageContent {
    Text(String),
    Blocks(Vec<ContentBlock>),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum ContentBlock {
    Text { text: String },
    Image { source: ImageSource },
    ToolUse { id: String, name: String, input: serde_json::Value },
    ToolResult { tool_use_id: String, content: String },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ImageSource {
    #[serde(rename = "type")]
    pub source_type: String,
    pub media_type: String,
    pub data: String, // Base64 encoded
}

/// 消息响应
#[derive(Debug, Clone, Deserialize)]
pub struct MessageResponse {
    pub id: String,
    #[serde(rename = "type")]
    pub response_type: String,
    pub role: MessageRole,
    pub content: Vec<ContentBlock>,
    pub model: String,
    pub stop_reason: Option<String>,
    pub stop_sequence: Option<String>,
    pub usage: Usage,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Usage {
    pub input_tokens: u32,
    pub output_tokens: u32,
}
```

**基础调用示例**:

```rust
// src/client/claude.rs (续)
impl ClaudeClient {
    /// 发送消息
    #[instrument(skip(self, messages))]
    pub async fn send_message(
        &self,
        messages: Vec<Message>,
        max_tokens: u32,
    ) -> Result<MessageResponse> {
        info!(message_count = %messages.len(), "Sending message to Claude");

        let request = MessageRequest {
            model: self.default_model.as_str().to_string(),
            messages,
            max_tokens,
            system: None,
            temperature: None,
            top_p: None,
            top_k: None,
            stop_sequences: None,
            stream: Some(false),
        };

        let response = self
            .client
            .post(format!("{}/v1/messages", self.base_url))
            .header("x-api-key", &self.api_key)
            .header("anthropic-version", "2023-06-01")
            .header("content-type", "application/json")
            .json(&request)
            .send()
            .await?;

        if response.status().is_success() {
            let message_response: MessageResponse = response.json().await?;

            info!(
                response_id = %message_response.id,
                input_tokens = %message_response.usage.input_tokens,
                output_tokens = %message_response.usage.output_tokens,
                "Received Claude response"
            );

            Ok(message_response)
        } else {
            let error_text = response.text().await?;
            anyhow::bail!("Claude API error: {}", error_text)
        }
    }

    /// 简单文本对话
    #[instrument(skip(self, prompt))]
    pub async fn chat(&self, prompt: &str) -> Result<String> {
        info!("Starting chat with Claude");

        let messages = vec![Message {
            role: MessageRole::User,
            content: MessageContent::Text(prompt.to_string()),
        }];

        let response = self.send_message(messages, 4096).await?;

        // 提取文本内容
        let text = response
            .content
            .iter()
            .filter_map(|block| {
                if let ContentBlock::Text { text } = block {
                    Some(text.clone())
                } else {
                    None
                }
            })
            .collect::<Vec<_>>()
            .join("\n");

        Ok(text)
    }

    /// 带系统提示的对话
    #[instrument(skip(self, system_prompt, user_prompt))]
    pub async fn chat_with_system(
        &self,
        system_prompt: &str,
        user_prompt: &str,
    ) -> Result<String> {
        info!("Chat with system prompt");

        let mut request = MessageRequest {
            model: self.default_model.as_str().to_string(),
            messages: vec![Message {
                role: MessageRole::User,
                content: MessageContent::Text(user_prompt.to_string()),
            }],
            max_tokens: 4096,
            system: Some(system_prompt.to_string()),
            temperature: None,
            top_p: None,
            top_k: None,
            stop_sequences: None,
            stream: Some(false),
        };

        let response = self
            .client
            .post(format!("{}/v1/messages", self.base_url))
            .header("x-api-key", &self.api_key)
            .header("anthropic-version", "2023-06-01")
            .json(&request)
            .send()
            .await?;

        let message_response: MessageResponse = response.json().await?;

        let text = message_response
            .content
            .iter()
            .filter_map(|block| {
                if let ContentBlock::Text { text } = block {
                    Some(text.clone())
                } else {
                    None
                }
            })
            .collect::<Vec<_>>()
            .join("\n");

        Ok(text)
    }
}
```

### 3.3 错误处理

```rust
// src/error.rs
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ClaudeError {
    #[error("API error: {0}")]
    ApiError(String),

    #[error("Rate limit exceeded")]
    RateLimitExceeded,

    #[error("Invalid API key")]
    InvalidApiKey,

    #[error("Model overloaded, retry later")]
    ModelOverloaded,

    #[error("Request too large: {0}")]
    RequestTooLarge(String),

    #[error("Network error: {0}")]
    NetworkError(#[from] reqwest::Error),

    #[error("JSON error: {0}")]
    JsonError(#[from] serde_json::Error),

    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),

    #[error("Other error: {0}")]
    Other(#[from] anyhow::Error),
}

impl ClaudeError {
    /// 是否应该重试
    pub fn is_retryable(&self) -> bool {
        matches!(
            self,
            Self::RateLimitExceeded | Self::ModelOverloaded | Self::NetworkError(_)
        )
    }
}
```

---

## 4. Streaming 响应

### 4.1 SSE流式处理

```rust
// src/streaming/sse.rs
use anyhow::Result;
use futures::stream::Stream;
use futures::StreamExt;
use reqwest_eventsource::{Event, EventSource};
use serde::{Deserialize, Serialize};
use tracing::{info, instrument, warn};

/// 流式事件类型
#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum StreamEvent {
    MessageStart { message: MessageStart },
    ContentBlockStart { index: u32, content_block: ContentBlockStart },
    ContentBlockDelta { index: u32, delta: ContentDelta },
    ContentBlockStop { index: u32 },
    MessageDelta { delta: MessageDelta, usage: UsageDelta },
    MessageStop,
    Ping,
    Error { error: ErrorDetails },
}

#[derive(Debug, Clone, Deserialize)]
pub struct MessageStart {
    pub id: String,
    pub model: String,
    pub role: String,
    pub usage: Usage,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum ContentBlockStart {
    Text { text: String },
}

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum ContentDelta {
    TextDelta { text: String },
}

#[derive(Debug, Clone, Deserialize)]
pub struct MessageDelta {
    pub stop_reason: Option<String>,
    pub stop_sequence: Option<String>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct UsageDelta {
    pub output_tokens: u32,
}

#[derive(Debug, Clone, Deserialize)]
pub struct ErrorDetails {
    #[serde(rename = "type")]
    pub error_type: String,
    pub message: String,
}

/// 流式客户端
impl ClaudeClient {
    /// 流式发送消息
    #[instrument(skip(self, messages))]
    pub async fn stream_message(
        &self,
        messages: Vec<Message>,
        max_tokens: u32,
    ) -> Result<impl Stream<Item = Result<StreamEvent>>> {
        info!("Starting streaming message");

        let mut request = MessageRequest {
            model: self.default_model.as_str().to_string(),
            messages,
            max_tokens,
            system: None,
            temperature: None,
            top_p: None,
            top_k: None,
            stop_sequences: None,
            stream: Some(true),
        };

        let url = format!("{}/v1/messages", self.base_url);

        let client = self.client.clone();
        let api_key = self.api_key.clone();

        let request_builder = client
            .post(&url)
            .header("x-api-key", api_key)
            .header("anthropic-version", "2023-06-01")
            .header("content-type", "application/json")
            .json(&request);

        let response = request_builder.send().await?;

        if !response.status().is_success() {
            let error_text = response.text().await?;
            anyhow::bail!("Claude API error: {}", error_text);
        }

        let event_source = EventSource::new(response)?;

        Ok(event_source.filter_map(|event_result| async move {
            match event_result {
                Ok(Event::Message(message)) => {
                    // 解析 JSON
                    match serde_json::from_str::<StreamEvent>(&message.data) {
                        Ok(event) => Some(Ok(event)),
                        Err(e) => {
                            warn!(error = %e, data = %message.data, "Failed to parse stream event");
                            None
                        }
                    }
                }
                Ok(Event::Open) => {
                    info!("Stream opened");
                    None
                }
                Err(e) => Some(Err(anyhow::anyhow!("Stream error: {}", e))),
            }
        }))
    }
}
```

### 4.2 实时响应

```rust
// examples/streaming_chat.rs
use anyhow::Result;
use claude_integration::*;
use futures::StreamExt;
use tracing::info;

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();

    let client = ClaudeClient::from_env()?;

    let prompt = "请详细解释什么是量子计算,包括其原理、应用和挑战。";

    let messages = vec![Message {
        role: MessageRole::User,
        content: MessageContent::Text(prompt.to_string()),
    }];

    let mut stream = client.stream_message(messages, 4096).await?;

    info!("开始接收流式响应:");
    print!("Claude: ");

    while let Some(event_result) = stream.next().await {
        match event_result? {
            StreamEvent::MessageStart { message } => {
                info!(
                    message_id = %message.id,
                    model = %message.model,
                    "Message started"
                );
            }
            StreamEvent::ContentBlockDelta { delta, .. } => {
                if let ContentDelta::TextDelta { text } = delta {
                    print!("{}", text);
                    std::io::Write::flush(&mut std::io::stdout())?;
                }
            }
            StreamEvent::MessageStop => {
                println!();
                info!("Message completed");
                break;
            }
            StreamEvent::Error { error } => {
                eprintln!("\nError: {} - {}", error.error_type, error.message);
                break;
            }
            _ => {}
        }
    }

    Ok(())
}
```

### 4.3 流式聚合

```rust
// src/streaming/aggregator.rs
use anyhow::Result;
use futures::stream::Stream;
use futures::StreamExt;
use tracing::instrument;

/// 聚合流式响应
pub struct StreamAggregator {
    pub message_id: Option<String>,
    pub model: Option<String>,
    pub content_blocks: Vec<String>,
    pub stop_reason: Option<String>,
    pub input_tokens: u32,
    pub output_tokens: u32,
}

impl StreamAggregator {
    pub fn new() -> Self {
        Self {
            message_id: None,
            model: None,
            content_blocks: vec![String::new()],
            stop_reason: None,
            input_tokens: 0,
            output_tokens: 0,
        }
    }

    /// 处理流式事件
    pub fn handle_event(&mut self, event: StreamEvent) -> Result<()> {
        match event {
            StreamEvent::MessageStart { message } => {
                self.message_id = Some(message.id);
                self.model = Some(message.model);
                self.input_tokens = message.usage.input_tokens;
            }
            StreamEvent::ContentBlockStart { index, .. } => {
                // 确保有足够的 block
                while self.content_blocks.len() <= index as usize {
                    self.content_blocks.push(String::new());
                }
            }
            StreamEvent::ContentBlockDelta { index, delta } => {
                if let ContentDelta::TextDelta { text } = delta {
                    if let Some(block) = self.content_blocks.get_mut(index as usize) {
                        block.push_str(&text);
                    }
                }
            }
            StreamEvent::MessageDelta { delta, usage } => {
                self.stop_reason = delta.stop_reason;
                self.output_tokens = usage.output_tokens;
            }
            _ => {}
        }

        Ok(())
    }

    /// 获取完整文本
    pub fn get_full_text(&self) -> String {
        self.content_blocks.join("\n")
    }

    /// 从流中聚合
    #[instrument(skip(stream))]
    pub async fn from_stream(
        mut stream: impl Stream<Item = Result<StreamEvent>> + Unpin,
    ) -> Result<Self> {
        let mut aggregator = Self::new();

        while let Some(event_result) = stream.next().await {
            let event = event_result?;

            if matches!(event, StreamEvent::MessageStop) {
                break;
            }

            aggregator.handle_event(event)?;
        }

        Ok(aggregator)
    }
}
```

---

## 5. Vision 能力

### 5.1 图像输入

```rust
// src/vision/image.rs
use anyhow::Result;
use base64::{Engine as _, engine::general_purpose};
use image::ImageFormat;
use std::path::Path;
use tracing::{info, instrument};

/// 图像工具
pub struct ImageProcessor;

impl ImageProcessor {
    /// 从文件加载并编码为 Base64
    #[instrument]
    pub fn load_and_encode(path: impl AsRef<Path>) -> Result<(String, String)> {
        let path = path.as_ref();

        info!(path = %path.display(), "Loading image");

        // 读取文件
        let image_data = std::fs::read(path)?;

        // 检测格式
        let format = image::guess_format(&image_data)?;
        let media_type = match format {
            ImageFormat::Jpeg => "image/jpeg",
            ImageFormat::Png => "image/png",
            ImageFormat::Gif => "image/gif",
            ImageFormat::WebP => "image/webp",
            _ => anyhow::bail!("Unsupported image format: {:?}", format),
        };

        // Base64 编码
        let encoded = general_purpose::STANDARD.encode(&image_data);

        info!(
            media_type = %media_type,
            size = %image_data.len(),
            "Image encoded"
        );

        Ok((media_type.to_string(), encoded))
    }

    /// 从 URL 加载
    #[instrument]
    pub async fn load_from_url(url: &str) -> Result<(String, String)> {
        info!(url = %url, "Fetching image from URL");

        let response = reqwest::get(url).await?;
        let content_type = response
            .headers()
            .get("content-type")
            .and_then(|v| v.to_str().ok())
            .unwrap_or("image/jpeg");

        let image_data = response.bytes().await?;
        let encoded = general_purpose::STANDARD.encode(&image_data);

        Ok((content_type.to_string(), encoded))
    }

    /// 压缩图像 (如果太大)
    #[instrument]
    pub fn compress_if_needed(data: &[u8], max_size: usize) -> Result<Vec<u8>> {
        if data.len() <= max_size {
            return Ok(data.to_vec());
        }

        info!(
            original_size = %data.len(),
            max_size = %max_size,
            "Compressing image"
        );

        // 加载图像
        let img = image::load_from_memory(data)?;

        // 计算缩放比例
        let scale = (max_size as f64 / data.len() as f64).sqrt();
        let new_width = (img.width() as f64 * scale) as u32;
        let new_height = (img.height() as f64 * scale) as u32;

        // 缩放
        let resized = img.resize(
            new_width,
            new_height,
            image::imageops::FilterType::Lanczos3,
        );

        // 编码为 JPEG
        let mut buffer = Vec::new();
        resized.write_to(
            &mut std::io::Cursor::new(&mut buffer),
            ImageFormat::Jpeg,
        )?;

        info!(compressed_size = %buffer.len(), "Image compressed");

        Ok(buffer)
    }
}
```

### 5.2 多模态处理

```rust
// src/client/claude.rs (续)
impl ClaudeClient {
    /// 发送带图像的消息
    #[instrument(skip(self, text, image_data))]
    pub async fn chat_with_image(
        &self,
        text: &str,
        image_path: impl AsRef<Path>,
    ) -> Result<String> {
        info!("Chat with image");

        let (media_type, encoded_image) = ImageProcessor::load_and_encode(image_path)?;

        let content_blocks = vec![
            ContentBlock::Image {
                source: ImageSource {
                    source_type: "base64".to_string(),
                    media_type,
                    data: encoded_image,
                },
            },
            ContentBlock::Text {
                text: text.to_string(),
            },
        ];

        let messages = vec![Message {
            role: MessageRole::User,
            content: MessageContent::Blocks(content_blocks),
        }];

        let response = self.send_message(messages, 4096).await?;

        let text = response
            .content
            .iter()
            .filter_map(|block| {
                if let ContentBlock::Text { text } = block {
                    Some(text.clone())
                } else {
                    None
                }
            })
            .collect::<Vec<_>>()
            .join("\n");

        Ok(text)
    }

    /// 分析多张图像
    #[instrument(skip(self, image_paths))]
    pub async fn analyze_multiple_images(
        &self,
        prompt: &str,
        image_paths: Vec<impl AsRef<Path>>,
    ) -> Result<String> {
        info!(image_count = %image_paths.len(), "Analyzing multiple images");

        let mut content_blocks = vec![ContentBlock::Text {
            text: prompt.to_string(),
        }];

        for path in image_paths {
            let (media_type, encoded_image) = ImageProcessor::load_and_encode(path)?;

            content_blocks.push(ContentBlock::Image {
                source: ImageSource {
                    source_type: "base64".to_string(),
                    media_type,
                    data: encoded_image,
                },
            });
        }

        let messages = vec![Message {
            role: MessageRole::User,
            content: MessageContent::Blocks(content_blocks),
        }];

        let response = self.send_message(messages, 4096).await?;

        let text = response
            .content
            .iter()
            .filter_map(|block| {
                if let ContentBlock::Text { text } = block {
                    Some(text.clone())
                } else {
                    None
                }
            })
            .collect::<Vec<_>>()
            .join("\n");

        Ok(text)
    }
}
```

### 5.3 PDF文档分析

```rust
// src/vision/pdf.rs
use anyhow::Result;
use std::path::Path;
use tracing::{info, instrument};

/// PDF 处理器
pub struct PdfProcessor;

impl PdfProcessor {
    /// 将 PDF 转换为图像 (需要 pdf2image 或类似工具)
    #[instrument]
    pub async fn pdf_to_images(pdf_path: impl AsRef<Path>) -> Result<Vec<Vec<u8>>> {
        let path = pdf_path.as_ref();
        info!(path = %path.display(), "Converting PDF to images");

        // 注意: 实际实现需要使用 pdfium-render 或调用外部工具
        // 这里提供一个简化示例

        todo!("Implement PDF to image conversion using pdfium-render or external tools")
    }

    /// 分析 PDF 文档
    #[instrument(skip(client))]
    pub async fn analyze_pdf(
        client: &ClaudeClient,
        pdf_path: impl AsRef<Path>,
        question: &str,
    ) -> Result<String> {
        info!("Analyzing PDF document");

        // 1. 转换 PDF 为图像
        let images = Self::pdf_to_images(pdf_path).await?;

        // 2. 为每张图像创建 content block
        let mut content_blocks = vec![ContentBlock::Text {
            text: question.to_string(),
        }];

        for image_data in images {
            let media_type = "image/png";
            let encoded = base64::engine::general_purpose::STANDARD.encode(&image_data);

            content_blocks.push(ContentBlock::Image {
                source: ImageSource {
                    source_type: "base64".to_string(),
                    media_type: media_type.to_string(),
                    data: encoded,
                },
            });
        }

        // 3. 发送请求
        let messages = vec![Message {
            role: MessageRole::User,
            content: MessageContent::Blocks(content_blocks),
        }];

        let response = client.send_message(messages, 4096).await?;

        let text = response
            .content
            .iter()
            .filter_map(|block| {
                if let ContentBlock::Text { text } = block {
                    Some(text.clone())
                } else {
                    None
                }
            })
            .collect::<Vec<_>>()
            .join("\n");

        Ok(text)
    }
}
```

---

## 6. Function Calling

### 6.1 工具定义

```rust
// src/models/tool.rs
use serde::{Deserialize, Serialize};
use serde_json::Value;

/// 工具定义
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Tool {
    pub name: String,
    pub description: String,
    pub input_schema: InputSchema,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InputSchema {
    #[serde(rename = "type")]
    pub schema_type: String,
    pub properties: serde_json::Map<String, Value>,
    pub required: Vec<String>,
}

/// 工具构建器
pub struct ToolBuilder {
    name: String,
    description: String,
    properties: serde_json::Map<String, Value>,
    required: Vec<String>,
}

impl ToolBuilder {
    pub fn new(name: impl Into<String>, description: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            description: description.into(),
            properties: serde_json::Map::new(),
            required: Vec::new(),
        }
    }

    pub fn add_string_param(
        mut self,
        name: impl Into<String>,
        description: impl Into<String>,
        required: bool,
    ) -> Self {
        let name = name.into();
        self.properties.insert(
            name.clone(),
            serde_json::json!({
                "type": "string",
                "description": description.into()
            }),
        );

        if required {
            self.required.push(name);
        }

        self
    }

    pub fn add_number_param(
        mut self,
        name: impl Into<String>,
        description: impl Into<String>,
        required: bool,
    ) -> Self {
        let name = name.into();
        self.properties.insert(
            name.clone(),
            serde_json::json!({
                "type": "number",
                "description": description.into()
            }),
        );

        if required {
            self.required.push(name);
        }

        self
    }

    pub fn add_boolean_param(
        mut self,
        name: impl Into<String>,
        description: impl Into<String>,
        required: bool,
    ) -> Self {
        let name = name.into();
        self.properties.insert(
            name.clone(),
            serde_json::json!({
                "type": "boolean",
                "description": description.into()
            }),
        );

        if required {
            self.required.push(name);
        }

        self
    }

    pub fn build(self) -> Tool {
        Tool {
            name: self.name,
            description: self.description,
            input_schema: InputSchema {
                schema_type: "object".to_string(),
                properties: self.properties,
                required: self.required,
            },
        }
    }
}

/// 示例工具定义
pub fn get_weather_tool() -> Tool {
    ToolBuilder::new(
        "get_weather",
        "获取指定城市的当前天气信息",
    )
    .add_string_param("city", "城市名称,例如'北京'或'Beijing'", true)
    .add_string_param(
        "unit",
        "温度单位,'celsius'或'fahrenheit',默认'celsius'",
        false,
    )
    .build()
}

pub fn search_web_tool() -> Tool {
    ToolBuilder::new(
        "search_web",
        "在互联网上搜索信息",
    )
    .add_string_param("query", "搜索关键词", true)
    .add_number_param("max_results", "最大结果数量", false)
    .build()
}

pub fn calculate_tool() -> Tool {
    ToolBuilder::new(
        "calculate",
        "执行数学计算",
    )
    .add_string_param("expression", "数学表达式,例如'2 + 2'或'sqrt(16)'", true)
    .build()
}
```

### 6.2 工具执行

```rust
// src/function/executor.rs
use anyhow::Result;
use serde_json::Value;
use std::collections::HashMap;
use tracing::{info, instrument};

/// 工具执行器
pub type ToolExecutor = Box<dyn Fn(Value) -> Result<String> + Send + Sync>;

/// 工具注册表
pub struct ToolRegistry {
    tools: HashMap<String, Tool>,
    executors: HashMap<String, ToolExecutor>,
}

impl ToolRegistry {
    pub fn new() -> Self {
        Self {
            tools: HashMap::new(),
            executors: HashMap::new(),
        }
    }

    /// 注册工具
    pub fn register(
        mut self,
        tool: Tool,
        executor: impl Fn(Value) -> Result<String> + Send + Sync + 'static,
    ) -> Self {
        let name = tool.name.clone();
        self.tools.insert(name.clone(), tool);
        self.executors.insert(name, Box::new(executor));
        self
    }

    /// 执行工具
    #[instrument(skip(self, input))]
    pub fn execute(&self, tool_name: &str, input: Value) -> Result<String> {
        info!(tool_name = %tool_name, "Executing tool");

        let executor = self
            .executors
            .get(tool_name)
            .ok_or_else(|| anyhow::anyhow!("Tool not found: {}", tool_name))?;

        executor(input)
    }

    /// 获取所有工具定义
    pub fn get_tools(&self) -> Vec<Tool> {
        self.tools.values().cloned().collect()
    }
}

/// 示例工具实现
pub fn create_sample_registry() -> ToolRegistry {
    ToolRegistry::new()
        .register(get_weather_tool(), |input| {
            let city = input
                .get("city")
                .and_then(|v| v.as_str())
                .ok_or_else(|| anyhow::anyhow!("Missing city parameter"))?;

            // 模拟天气查询
            Ok(format!(
                "{{\"city\": \"{}\", \"temperature\": 25, \"condition\": \"晴朗\", \"humidity\": 60}}",
                city
            ))
        })
        .register(search_web_tool(), |input| {
            let query = input
                .get("query")
                .and_then(|v| v.as_str())
                .ok_or_else(|| anyhow::anyhow!("Missing query parameter"))?;

            // 模拟搜索
            Ok(format!(
                "找到关于'{}'的以下结果:\n1. 结果1\n2. 结果2\n3. 结果3",
                query
            ))
        })
        .register(calculate_tool(), |input| {
            let expression = input
                .get("expression")
                .and_then(|v| v.as_str())
                .ok_or_else(|| anyhow::anyhow!("Missing expression parameter"))?;

            // 简单计算 (实际应使用 meval 等库)
            match expression {
                "2 + 2" => Ok("4".to_string()),
                "sqrt(16)" => Ok("4".to_string()),
                _ => Ok("计算结果: 42".to_string()),
            }
        })
}
```

### 6.3 多轮对话

```rust
// src/function/agent.rs
use anyhow::Result;
use tracing::{info, instrument};

/// Function Calling Agent
pub struct FunctionCallingAgent {
    client: ClaudeClient,
    registry: ToolRegistry,
    max_iterations: usize,
}

impl FunctionCallingAgent {
    pub fn new(client: ClaudeClient, registry: ToolRegistry) -> Self {
        Self {
            client,
            registry,
            max_iterations: 10,
        }
    }

    /// 运行 Agent
    #[instrument(skip(self, initial_prompt))]
    pub async fn run(&self, initial_prompt: &str) -> Result<String> {
        info!("Starting function calling agent");

        let mut messages = vec![Message {
            role: MessageRole::User,
            content: MessageContent::Text(initial_prompt.to_string()),
        }];

        let tools = self.registry.get_tools();

        for iteration in 0..self.max_iterations {
            info!(iteration = %iteration, "Agent iteration");

            // 构造请求
            let mut request = MessageRequest {
                model: self.client.default_model.as_str().to_string(),
                messages: messages.clone(),
                max_tokens: 4096,
                system: None,
                temperature: None,
                top_p: None,
                top_k: None,
                stop_sequences: None,
                stream: Some(false),
            };

            // 添加工具定义
            // 注意: Claude API 通过特殊参数传递工具,这里简化处理
            // 实际需要根据最新 API 文档调整

            let response = self.client.send_message(messages.clone(), 4096).await?;

            // 检查是否有工具调用
            let tool_uses: Vec<_> = response
                .content
                .iter()
                .filter_map(|block| {
                    if let ContentBlock::ToolUse { id, name, input } = block {
                        Some((id.clone(), name.clone(), input.clone()))
                    } else {
                        None
                    }
                })
                .collect();

            if tool_uses.is_empty() {
                // 没有工具调用,返回文本结果
                let text = response
                    .content
                    .iter()
                    .filter_map(|block| {
                        if let ContentBlock::Text { text } = block {
                            Some(text.clone())
                        } else {
                            None
                        }
                    })
                    .collect::<Vec<_>>()
                    .join("\n");

                return Ok(text);
            }

            // 添加 Assistant 的响应到历史
            messages.push(Message {
                role: MessageRole::Assistant,
                content: MessageContent::Blocks(response.content),
            });

            // 执行工具调用
            let mut tool_results = Vec::new();

            for (id, name, input) in tool_uses {
                info!(tool_id = %id, tool_name = %name, "Executing tool");

                let result = self.registry.execute(&name, input)?;

                tool_results.push(ContentBlock::ToolResult {
                    tool_use_id: id,
                    content: result,
                });
            }

            // 添加工具结果到历史
            messages.push(Message {
                role: MessageRole::User,
                content: MessageContent::Blocks(tool_results),
            });
        }

        anyhow::bail!("Max iterations reached")
    }
}
```

**使用示例**:

```rust
// examples/function_calling.rs
use anyhow::Result;
use claude_integration::*;

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();

    let client = ClaudeClient::from_env()?;
    let registry = create_sample_registry();

    let agent = FunctionCallingAgent::new(client, registry);

    let prompt = "北京今天天气怎么样?然后帮我搜索一下量子计算的最新进展。";

    let result = agent.run(prompt).await?;

    println!("Agent 结果:");
    println!("{}", result);

    Ok(())
}
```

---

## 7. 提示工程

### 7.1 System Prompt

```rust
// src/prompt/template.rs
/// 系统提示模板
pub struct SystemPromptTemplates;

impl SystemPromptTemplates {
    /// 代码助手
    pub fn code_assistant() -> &'static str {
        r#"You are an expert software engineer with deep knowledge of multiple programming languages,
best practices, and design patterns. You provide clear, concise, and production-ready code with
detailed explanations. Always consider:

1. Code quality and maintainability
2. Performance and efficiency
3. Error handling and edge cases
4. Security best practices
5. Testing strategies

When writing code:
- Use descriptive variable names
- Add helpful comments
- Follow language-specific conventions
- Provide usage examples"#
    }

    /// 数据分析师
    pub fn data_analyst() -> &'static str {
        r#"You are a professional data analyst with expertise in statistics, data visualization,
and business intelligence. You help users understand data through:

1. Exploratory data analysis
2. Statistical insights
3. Clear visualizations
4. Actionable recommendations

Always explain your reasoning and methodology."#
    }

    /// 技术文档撰写
    pub fn technical_writer() -> &'static str {
        r#"You are a technical writer who creates clear, comprehensive documentation.
Your documentation includes:

1. Clear explanations of complex concepts
2. Well-structured content with headings
3. Code examples with explanations
4. Best practices and common pitfalls
5. Links to relevant resources

Use Markdown formatting for better readability."#
    }

    /// 客户支持
    pub fn customer_support() -> &'static str {
        r#"You are a friendly and professional customer support agent. You:

1. Listen carefully to customer concerns
2. Provide clear and accurate information
3. Offer step-by-step solutions
4. Maintain a helpful and empathetic tone
5. Escalate complex issues when necessary

Always prioritize customer satisfaction."#
    }
}
```

### 7.2 思维链

```rust
// src/prompt/chain.rs
/// 思维链提示
pub struct ChainOfThought;

impl ChainOfThought {
    /// 生成思维链提示
    pub fn generate_prompt(question: &str) -> String {
        format!(
            r#"请使用思维链 (Chain of Thought) 方法回答以下问题:

问题: {}

请按照以下步骤思考:

1. **理解问题**: 首先明确问题的核心要求
2. **分解问题**: 将复杂问题分解为更小的子问题
3. **逐步推理**: 对每个子问题进行详细分析
4. **得出结论**: 基于推理过程给出最终答案

让我们一步步来:"#,
            question
        )
    }

    /// 数学问题思维链
    pub fn math_problem(problem: &str) -> String {
        format!(
            r#"请使用思维链方法解决这个数学问题:

问题: {}

步骤:
1. **识别已知信息**: 列出题目中给出的所有数据
2. **确定求解目标**: 明确需要计算什么
3. **选择方法**: 确定适用的数学公式或方法
4. **逐步计算**: 展示每一步的详细计算过程
5. **验证答案**: 检查答案的合理性

开始解答:"#,
            problem
        )
    }

    /// 推理问题
    pub fn reasoning_problem(problem: &str) -> String {
        format!(
            r#"请使用逻辑推理解决这个问题:

问题: {}

推理步骤:
1. **列出前提**: 明确所有已知条件
2. **识别关系**: 分析条件之间的逻辑关系
3. **推理过程**: 基于前提进行逐步推导
4. **得出结论**: 给出最终答案并解释原因

开始推理:"#,
            problem
        )
    }
}
```

### 7.3 Few-Shot Learning

```rust
// src/prompt/few_shot.rs
/// Few-Shot Learning 示例
pub struct FewShotExamples;

impl FewShotExamples {
    /// 情感分析示例
    pub fn sentiment_analysis_prompt(text: &str) -> String {
        format!(
            r#"请分析以下文本的情感倾向 (积极/中性/消极):

示例 1:
文本: "这个产品真的太棒了,完全超出我的期待!"
情感: 积极
理由: 使用了"太棒了"、"超出期待"等强烈的正面词汇

示例 2:
文本: "这个产品还行,没什么特别的。"
情感: 中性
理由: "还行"表示平平,没有明显的褒贬倾向

示例 3:
文本: "质量太差了,完全是浪费钱!"
情感: 消极
理由: "太差"、"浪费钱"等明显的负面评价

现在请分析:
文本: "{}"
情感:
理由:"#,
            text
        )
    }

    /// 文本分类示例
    pub fn text_classification_prompt(text: &str, categories: &[&str]) -> String {
        let categories_str = categories.join(", ");

        format!(
            r#"请将以下文本分类到以下类别之一: {}

示例 1:
文本: "苹果今天发布了新款iPhone,配备了更强大的处理器。"
类别: 科技

示例 2:
文本: "中国队在今天的比赛中以3:1战胜了对手。"
类别: 体育

示例 3:
文本: "央行宣布降低存款准备金率0.5个百分点。"
类别: 财经

现在请分类:
文本: "{}"
类别:"#,
            categories_str, text
        )
    }

    /// 信息抽取示例
    pub fn information_extraction_prompt(text: &str) -> String {
        format!(
            r#"请从以下文本中抽取结构化信息:

示例:
文本: "特斯拉CEO埃隆·马斯克在2023年宣布公司将在中国上海新建一座工厂。"
抽取结果:
- 公司: 特斯拉
- 人物: 埃隆·马斯克 (CEO)
- 时间: 2023年
- 地点: 中国上海
- 事件: 新建工厂

现在请抽取:
文本: "{}"
抽取结果:"#,
            text
        )
    }
}
```

---

## 8. OTLP 可观测性

### 8.1 分布式追踪

```rust
// src/observability/tracing.rs
use opentelemetry::trace::{FutureExt, TraceContextExt, Tracer};
use opentelemetry::{global, KeyValue};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::trace::{Sampler, TracerProvider};
use opentelemetry_sdk::Resource;
use tracing::{info, instrument, Span};
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::Registry;

/// 初始化 OpenTelemetry
pub fn init_telemetry() -> Result<()> {
    // 创建 OTLP Exporter
    let tracer = opentelemetry_otlp::SpanExporter::builder()
        .with_tonic()
        .with_endpoint("http://localhost:4317")
        .build()?;

    // 配置 TracerProvider
    let provider = TracerProvider::builder()
        .with_batch_exporter(tracer, opentelemetry_sdk::runtime::Tokio)
        .with_resource(Resource::new(vec![
            KeyValue::new("service.name", "claude-integration"),
            KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        ]))
        .with_sampler(Sampler::AlwaysOn)
        .build();

    global::set_tracer_provider(provider);

    // 配置 tracing subscriber
    let telemetry = tracing_opentelemetry::layer()
        .with_tracer(global::tracer("claude-integration"));

    let subscriber = Registry::default()
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .with(tracing_subscriber::fmt::layer())
        .with(telemetry);

    tracing::subscriber::set_global_default(subscriber)?;

    info!("OpenTelemetry initialized");

    Ok(())
}

/// 为 Claude API 调用添加追踪
impl ClaudeClient {
    #[instrument(
        skip(self, messages),
        fields(
            otel.kind = "client",
            otel.name = "claude.send_message",
            claude.model = %self.default_model.as_str(),
            claude.message_count = %messages.len(),
        )
    )]
    pub async fn send_message_traced(
        &self,
        messages: Vec<Message>,
        max_tokens: u32,
    ) -> Result<MessageResponse> {
        let span = Span::current();

        span.record("claude.max_tokens", max_tokens);

        let response = self.send_message(messages, max_tokens).await?;

        // 记录响应指标
        span.record("claude.response_id", response.id.as_str());
        span.record("claude.input_tokens", response.usage.input_tokens);
        span.record("claude.output_tokens", response.usage.output_tokens);
        span.record("claude.stop_reason", response.stop_reason.as_deref().unwrap_or("unknown"));

        Ok(response)
    }
}
```

### 8.2 指标监控

```rust
// src/observability/metrics.rs
use opentelemetry::metrics::{Counter, Histogram, Meter};
use opentelemetry::{global, KeyValue};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::metrics::{MeterProvider, PeriodicReader};
use std::sync::Arc;
use std::time::Duration;
use tracing::info;

/// Claude 指标收集器
pub struct ClaudeMetrics {
    request_counter: Counter<u64>,
    token_usage: Histogram<u64>,
    latency: Histogram<f64>,
    error_counter: Counter<u64>,
}

impl ClaudeMetrics {
    /// 初始化指标
    pub fn init() -> Result<Arc<Self>> {
        info!("Initializing Claude metrics");

        // 创建 OTLP Exporter
        let exporter = opentelemetry_otlp::MetricExporter::builder()
            .with_tonic()
            .with_endpoint("http://localhost:4317")
            .build()?;

        // 配置 MeterProvider
        let reader = PeriodicReader::builder(exporter, opentelemetry_sdk::runtime::Tokio)
            .with_interval(Duration::from_secs(30))
            .build();

        let provider = MeterProvider::builder()
            .with_reader(reader)
            .with_resource(opentelemetry_sdk::Resource::new(vec![
                KeyValue::new("service.name", "claude-integration"),
            ]))
            .build();

        global::set_meter_provider(provider.clone());

        let meter = provider.meter("claude-integration");

        let metrics = Self {
            request_counter: meter
                .u64_counter("claude.requests")
                .with_description("Total Claude API requests")
                .build(),

            token_usage: meter
                .u64_histogram("claude.tokens")
                .with_description("Token usage per request")
                .build(),

            latency: meter
                .f64_histogram("claude.latency")
                .with_description("Request latency in seconds")
                .build(),

            error_counter: meter
                .u64_counter("claude.errors")
                .with_description("Total Claude API errors")
                .build(),
        };

        Ok(Arc::new(metrics))
    }

    /// 记录请求
    pub fn record_request(&self, model: &str, success: bool) {
        self.request_counter.add(
            1,
            &[
                KeyValue::new("model", model.to_string()),
                KeyValue::new("success", success),
            ],
        );
    }

    /// 记录 Token 使用
    pub fn record_tokens(&self, input_tokens: u32, output_tokens: u32, model: &str) {
        self.token_usage.record(
            input_tokens as u64,
            &[
                KeyValue::new("type", "input"),
                KeyValue::new("model", model.to_string()),
            ],
        );

        self.token_usage.record(
            output_tokens as u64,
            &[
                KeyValue::new("type", "output"),
                KeyValue::new("model", model.to_string()),
            ],
        );
    }

    /// 记录延迟
    pub fn record_latency(&self, duration: Duration, model: &str) {
        self.latency.record(
            duration.as_secs_f64(),
            &[KeyValue::new("model", model.to_string())],
        );
    }

    /// 记录错误
    pub fn record_error(&self, error_type: &str, model: &str) {
        self.error_counter.add(
            1,
            &[
                KeyValue::new("error_type", error_type.to_string()),
                KeyValue::new("model", model.to_string()),
            ],
        );
    }
}
```

### 8.3 成本追踪

```rust
// src/observability/cost.rs
use chrono::{DateTime, Utc};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use tracing::info;

/// Claude 成本计算器
pub struct CostCalculator {
    total_input_tokens: Arc<AtomicU64>,
    total_output_tokens: Arc<AtomicU64>,
}

impl CostCalculator {
    pub fn new() -> Self {
        Self {
            total_input_tokens: Arc::new(AtomicU64::new(0)),
            total_output_tokens: Arc::new(AtomicU64::new(0)),
        }
    }

    /// 记录使用量
    pub fn record_usage(&self, input_tokens: u32, output_tokens: u32) {
        self.total_input_tokens
            .fetch_add(input_tokens as u64, Ordering::Relaxed);
        self.total_output_tokens
            .fetch_add(output_tokens as u64, Ordering::Relaxed);
    }

    /// 计算成本 (Claude 3.5 Sonnet 定价)
    pub fn calculate_cost(&self, model: ClaudeModel) -> f64 {
        let input_tokens = self.total_input_tokens.load(Ordering::Relaxed);
        let output_tokens = self.total_output_tokens.load(Ordering::Relaxed);

        let (input_price, output_price) = match model {
            ClaudeModel::Claude35Sonnet => (0.003, 0.015),  // per 1K tokens
            ClaudeModel::Claude3Opus => (0.015, 0.075),
            ClaudeModel::Claude3Sonnet => (0.003, 0.015),
            ClaudeModel::Claude3Haiku => (0.00025, 0.00125),
        };

        let input_cost = (input_tokens as f64 / 1000.0) * input_price;
        let output_cost = (output_tokens as f64 / 1000.0) * output_price;

        input_cost + output_cost
    }

    /// 获取统计信息
    pub fn get_stats(&self) -> CostStats {
        CostStats {
            input_tokens: self.total_input_tokens.load(Ordering::Relaxed),
            output_tokens: self.total_output_tokens.load(Ordering::Relaxed),
            timestamp: Utc::now(),
        }
    }

    /// 重置统计
    pub fn reset(&self) {
        self.total_input_tokens.store(0, Ordering::Relaxed);
        self.total_output_tokens.store(0, Ordering::Relaxed);
        info!("Cost statistics reset");
    }
}

#[derive(Debug, Clone)]
pub struct CostStats {
    pub input_tokens: u64,
    pub output_tokens: u64,
    pub timestamp: DateTime<Utc>,
}

impl CostStats {
    pub fn total_tokens(&self) -> u64 {
        self.input_tokens + self.output_tokens
    }

    pub fn format_report(&self, model: ClaudeModel) -> String {
        let calculator = CostCalculator {
            total_input_tokens: Arc::new(AtomicU64::new(self.input_tokens)),
            total_output_tokens: Arc::new(AtomicU64::new(self.output_tokens)),
        };

        let cost = calculator.calculate_cost(model);

        format!(
            r#"Claude API Usage Report
========================
Timestamp: {}
Model: {:?}

Input Tokens:  {:>10}
Output Tokens: {:>10}
Total Tokens:  {:>10}

Estimated Cost: ${:.4}
"#,
            self.timestamp.format("%Y-%m-%d %H:%M:%S UTC"),
            model,
            self.input_tokens,
            self.output_tokens,
            self.total_tokens(),
            cost
        )
    }
}
```

---

## 9. 生产实践

### 9.1 速率限制

```rust
// src/utils/rate_limit.rs
use governor::{Quota, RateLimiter};
use std::num::NonZeroU32;
use std::sync::Arc;
use tokio::time::{sleep, Duration};
use tracing::{info, warn, instrument};

/// 速率限制器
pub struct ClaudeRateLimiter {
    limiter: Arc<RateLimiter<governor::state::direct::NotKeyed, governor::clock::DefaultClock>>,
}

impl ClaudeRateLimiter {
    /// 创建速率限制器
    /// requests_per_minute: 每分钟允许的请求数
    pub fn new(requests_per_minute: u32) -> Self {
        let quota = Quota::per_minute(NonZeroU32::new(requests_per_minute).unwrap());
        let limiter = RateLimiter::direct(quota);

        info!(requests_per_minute = %requests_per_minute, "Rate limiter initialized");

        Self {
            limiter: Arc::new(limiter),
        }
    }

    /// 等待直到允许请求
    #[instrument(skip(self))]
    pub async fn acquire(&self) -> Result<()> {
        match self.limiter.check() {
            Ok(_) => {
                // 允许请求
                Ok(())
            }
            Err(not_until) => {
                let wait_duration = not_until.wait_time_from(std::time::Instant::now());

                warn!(
                    wait_seconds = %wait_duration.as_secs_f64(),
                    "Rate limit reached, waiting"
                );

                sleep(wait_duration).await;

                // 重试
                self.acquire().await
            }
        }
    }
}

/// 为 Claude Client 添加速率限制
pub struct RateLimitedClaudeClient {
    client: ClaudeClient,
    rate_limiter: ClaudeRateLimiter,
}

impl RateLimitedClaudeClient {
    pub fn new(client: ClaudeClient, requests_per_minute: u32) -> Self {
        Self {
            client,
            rate_limiter: ClaudeRateLimiter::new(requests_per_minute),
        }
    }

    #[instrument(skip(self, messages))]
    pub async fn send_message(
        &self,
        messages: Vec<Message>,
        max_tokens: u32,
    ) -> Result<MessageResponse> {
        // 等待速率限制
        self.rate_limiter.acquire().await?;

        // 发送请求
        self.client.send_message(messages, max_tokens).await
    }
}
```

### 9.2 重试策略

```rust
// src/utils/retry.rs
use anyhow::Result;
use std::time::Duration;
use tokio::time::sleep;
use tracing::{info, warn, instrument};

/// 重试配置
#[derive(Debug, Clone)]
pub struct RetryConfig {
    pub max_retries: u32,
    pub initial_backoff: Duration,
    pub max_backoff: Duration,
    pub backoff_multiplier: f64,
}

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            max_retries: 3,
            initial_backoff: Duration::from_secs(1),
            max_backoff: Duration::from_secs(60),
            backoff_multiplier: 2.0,
        }
    }
}

/// 指数退避重试
#[instrument(skip(config, operation))]
pub async fn retry_with_backoff<F, T, Fut>(
    config: RetryConfig,
    operation: F,
) -> Result<T>
where
    F: Fn() -> Fut,
    Fut: std::future::Future<Output = Result<T>>,
{
    let mut last_error = None;
    let mut backoff = config.initial_backoff;

    for attempt in 0..=config.max_retries {
        if attempt > 0 {
            info!(attempt = %attempt, backoff_secs = %backoff.as_secs_f64(), "Retrying");
            sleep(backoff).await;

            // 指数退避
            backoff = std::cmp::min(
                Duration::from_secs_f64(backoff.as_secs_f64() * config.backoff_multiplier),
                config.max_backoff,
            );
        }

        match operation().await {
            Ok(result) => {
                if attempt > 0 {
                    info!(attempt = %attempt, "Retry succeeded");
                }
                return Ok(result);
            }
            Err(e) => {
                warn!(attempt = %attempt, error = %e, "Operation failed");
                last_error = Some(e);
            }
        }
    }

    Err(last_error.unwrap())
}

/// 带重试的 Claude Client
pub struct RetryableClaudeClient {
    client: ClaudeClient,
    config: RetryConfig,
}

impl RetryableClaudeClient {
    pub fn new(client: ClaudeClient) -> Self {
        Self {
            client,
            config: RetryConfig::default(),
        }
    }

    pub fn with_config(client: ClaudeClient, config: RetryConfig) -> Self {
        Self { client, config }
    }

    #[instrument(skip(self, messages))]
    pub async fn send_message(
        &self,
        messages: Vec<Message>,
        max_tokens: u32,
    ) -> Result<MessageResponse> {
        let client = &self.client;
        let messages = messages.clone();

        retry_with_backoff(self.config.clone(), || async {
            client.send_message(messages.clone(), max_tokens).await
        })
        .await
    }
}
```

### 9.3 缓存优化

```rust
// src/utils/cache.rs
use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::sync::Arc;
use tokio::sync::RwLock;
use tracing::{info, instrument};

/// 请求缓存键
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CacheKey {
    model: String,
    messages_hash: u64,
}

impl CacheKey {
    pub fn new(model: &str, messages: &[Message]) -> Self {
        use std::collections::hash_map::DefaultHasher;

        let mut hasher = DefaultHasher::new();
        serde_json::to_string(messages)
            .unwrap_or_default()
            .hash(&mut hasher);

        Self {
            model: model.to_string(),
            messages_hash: hasher.finish(),
        }
    }
}

/// 响应缓存
pub struct ResponseCache {
    cache: Arc<RwLock<HashMap<CacheKey, MessageResponse>>>,
    max_size: usize,
}

impl ResponseCache {
    pub fn new(max_size: usize) -> Self {
        Self {
            cache: Arc::new(RwLock::new(HashMap::new())),
            max_size,
        }
    }

    /// 获取缓存
    #[instrument(skip(self))]
    pub async fn get(&self, key: &CacheKey) -> Option<MessageResponse> {
        let cache = self.cache.read().await;
        let result = cache.get(key).cloned();

        if result.is_some() {
            info!("Cache hit");
        }

        result
    }

    /// 设置缓存
    #[instrument(skip(self, response))]
    pub async fn set(&self, key: CacheKey, response: MessageResponse) {
        let mut cache = self.cache.write().await;

        // 简单的 LRU: 如果超过最大大小,清空缓存
        if cache.len() >= self.max_size {
            info!("Cache full, clearing");
            cache.clear();
        }

        cache.insert(key, response);
        info!("Response cached");
    }

    /// 清空缓存
    pub async fn clear(&self) {
        let mut cache = self.cache.write().await;
        cache.clear();
        info!("Cache cleared");
    }
}

/// 带缓存的 Claude Client
pub struct CachedClaudeClient {
    client: ClaudeClient,
    cache: ResponseCache,
}

impl CachedClaudeClient {
    pub fn new(client: ClaudeClient, cache_size: usize) -> Self {
        Self {
            client,
            cache: ResponseCache::new(cache_size),
        }
    }

    #[instrument(skip(self, messages))]
    pub async fn send_message(
        &self,
        messages: Vec<Message>,
        max_tokens: u32,
    ) -> Result<MessageResponse> {
        let cache_key = CacheKey::new(self.client.default_model.as_str(), &messages);

        // 尝试从缓存获取
        if let Some(cached_response) = self.cache.get(&cache_key).await {
            return Ok(cached_response);
        }

        // 发送请求
        let response = self.client.send_message(messages, max_tokens).await?;

        // 缓存响应
        self.cache.set(cache_key, response.clone()).await;

        Ok(response)
    }
}
```

---

## 10. 测试策略

```rust
// tests/integration_test.rs
#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::Result;

    #[tokio::test]
    #[ignore] // 需要真实的 API Key
    async fn test_basic_chat() -> Result<()> {
        let client = ClaudeClient::from_env()?;

        let response = client.chat("Hello, Claude!").await?;

        assert!(!response.is_empty());
        println!("Response: {}", response);

        Ok(())
    }

    #[tokio::test]
    #[ignore]
    async fn test_streaming() -> Result<()> {
        let client = ClaudeClient::from_env()?;

        let messages = vec![Message {
            role: MessageRole::User,
            content: MessageContent::Text("Count from 1 to 5.".to_string()),
        }];

        let mut stream = client.stream_message(messages, 1024).await?;

        let mut text = String::new();

        while let Some(event_result) = stream.next().await {
            let event = event_result?;

            if let StreamEvent::ContentBlockDelta { delta, .. } = event {
                if let ContentDelta::TextDelta { text: chunk } = delta {
                    text.push_str(&chunk);
                }
            }
        }

        assert!(!text.is_empty());
        println!("Streamed text: {}", text);

        Ok(())
    }

    #[tokio::test]
    #[ignore]
    async fn test_vision() -> Result<()> {
        let client = ClaudeClient::from_env()?;

        // 需要提供一个测试图像
        let response = client
            .chat_with_image("What is in this image?", "test_image.jpg")
            .await?;

        assert!(!response.is_empty());
        println!("Vision response: {}", response);

        Ok(())
    }

    #[test]
    fn test_tool_builder() {
        let tool = ToolBuilder::new("test_tool", "A test tool")
            .add_string_param("param1", "First parameter", true)
            .add_number_param("param2", "Second parameter", false)
            .build();

        assert_eq!(tool.name, "test_tool");
        assert_eq!(tool.input_schema.required.len(), 1);
        assert_eq!(tool.input_schema.properties.len(), 2);
    }

    #[test]
    fn test_cache_key() {
        let messages1 = vec![Message {
            role: MessageRole::User,
            content: MessageContent::Text("Hello".to_string()),
        }];

        let messages2 = vec![Message {
            role: MessageRole::User,
            content: MessageContent::Text("Hello".to_string()),
        }];

        let key1 = CacheKey::new("claude-3-5-sonnet", &messages1);
        let key2 = CacheKey::new("claude-3-5-sonnet", &messages2);

        assert_eq!(key1, key2);
    }

    #[test]
    fn test_cost_calculator() {
        let calculator = CostCalculator::new();

        calculator.record_usage(1000, 500);

        let cost = calculator.calculate_cost(ClaudeModel::Claude35Sonnet);

        // 1000 input tokens * 0.003 / 1K + 500 output tokens * 0.015 / 1K
        let expected_cost = 1.0 * 0.003 + 0.5 * 0.015;

        assert!((cost - expected_cost).abs() < 0.001);
    }
}
```

---

## 11. 参考资源

### 官方文档

- **Anthropic Claude API**: [https://docs.anthropic.com/claude/reference/getting-started](https://docs.anthropic.com/claude/reference/getting-started)
- **Claude Model Card**: [https://www.anthropic.com/claude](https://www.anthropic.com/claude)
- **API Pricing**: [https://www.anthropic.com/pricing](https://www.anthropic.com/pricing)

### Rust 生态

- **reqwest**: [https://docs.rs/reqwest](https://docs.rs/reqwest)
- **reqwest-eventsource**: [https://docs.rs/reqwest-eventsource](https://docs.rs/reqwest-eventsource)
- **OpenTelemetry Rust**: [https://docs.rs/opentelemetry](https://docs.rs/opentelemetry)

### 国际标准

- **HTTP/2 (RFC 7540)**: [https://tools.ietf.org/html/rfc7540](https://tools.ietf.org/html/rfc7540)
- **JSON (RFC 8259)**: [https://tools.ietf.org/html/rfc8259](https://tools.ietf.org/html/rfc8259)
- **Server-Sent Events (W3C)**: [https://www.w3.org/TR/eventsource/](https://www.w3.org/TR/eventsource/)
- **OAuth 2.0 (RFC 6749)**: [https://tools.ietf.org/html/rfc6749](https://tools.ietf.org/html/rfc6749)

### 最佳实践

- **Constitutional AI Paper**: [https://arxiv.org/abs/2212.08073](https://arxiv.org/abs/2212.08073)
- **Prompt Engineering Guide**: [https://www.promptingguide.ai](https://www.promptingguide.ai)
- **LLM Observability**: [https://opentelemetry.io/docs/llm/](https://opentelemetry.io/docs/llm/)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-12  
**Rust 版本**: 1.90+  
**OpenTelemetry**: 0.27+  
**作者**: OTLP Rust 项目组
