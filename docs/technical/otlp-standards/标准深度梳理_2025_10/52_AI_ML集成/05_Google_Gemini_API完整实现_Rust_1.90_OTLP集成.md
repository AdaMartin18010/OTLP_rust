# Google Gemini API 完整实现 - Rust 1.90 + OTLP 集成

## 目录

- [Google Gemini API 完整实现 - Rust 1.90 + OTLP 集成](#google-gemini-api-完整实现---rust-190--otlp-集成)
  - [目录](#目录)
  - [1. 核心概念与架构](#1-核心概念与架构)
    - [1.1 Gemini 模型家族](#11-gemini-模型家族)
    - [1.2 API 架构](#12-api-架构)
    - [1.3 国际标准对齐](#13-国际标准对齐)
  - [2. Rust 生态集成](#2-rust-生态集成)
    - [2.1 核心依赖](#21-核心依赖)
    - [2.2 项目结构](#22-项目结构)
  - [3. 基础API调用](#3-基础api调用)
    - [3.1 客户端初始化](#31-客户端初始化)
    - [3.2 内容生成API](#32-内容生成api)
    - [3.3 错误处理](#33-错误处理)
  - [4. Streaming 响应](#4-streaming-响应)
    - [4.1 流式生成](#41-流式生成)
    - [4.2 实时响应](#42-实时响应)
  - [5. 多模态能力](#5-多模态能力)
    - [5.1 图像输入](#51-图像输入)
    - [5.2 音频输入](#52-音频输入)
    - [5.3 视频输入](#53-视频输入)
    - [5.4 多模态组合](#54-多模态组合)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [Rust 生态](#rust-生态)
    - [国际标准](#国际标准)

---

## 1. 核心概念与架构

### 1.1 Gemini 模型家族

Google Gemini 提供多种模型,满足不同场景需求:

| 模型 | 能力 | 上下文 | 适用场景 |
|------|------|--------|----------|
| **Gemini 2.0 Flash** | 最新、最快 | 1M tokens | 实时应用、多模态理解 |
| **Gemini 1.5 Pro** | 最强推理 | 2M tokens | 复杂任务、长上下文 |
| **Gemini 1.5 Flash** | 平衡性能 | 1M tokens | 通用任务、高吞吐 |
| **Gemini 1.0 Pro** | 稳定版本 | 32K tokens | 生产环境 |

**核心特性**:

- ✅ **超长上下文**: 2M tokens (Gemini 1.5 Pro)
- ✅ **原生多模态**: 文本、图像、音频、视频统一处理
- ✅ **Function Calling**: 工具使用与API集成
- ✅ **Grounding**: 结合Google搜索的动态知识检索
- ✅ **Code Execution**: 自动代码生成与执行
- ✅ **Safety Settings**: 灵活的内容安全控制
- ✅ **多语言支持**: 包括中文在内的100+种语言

### 1.2 API 架构

```text
┌─────────────────────────────────────────────────────────┐
│              Google Gemini API Architecture             │
│                                                         │
│  ┌────────────────────────────────────────────────────┐ │
│  │              Client Application                    │ │
│  │  ┌──────────────────────────────────────────────┐  │ │
│  │  │          Rust Gemini Client                  │  │ │
│  │  │  - API Key Authentication                    │  │ │
│  │  │  - Request Building                          │  │ │
│  │  │  - Multimodal Content                        │  │ │
│  │  │  - Error Handling                            │  │ │
│  │  └──────────────────────────────────────────────┘  │ │
│  └────────────────────────────────────────────────────┘ │
│                          │                              │
│                          │ HTTPS/HTTP2                  │
│                          ▼                              │
│  ┌────────────────────────────────────────────────────┐ │
│  │          Google Cloud API Gateway                  │ │
│  │  https://generativelanguage.googleapis.com         │ │
│  │                                                    │ │
│  │  ┌──────────────────────────────────────────────┐  │ │
│  │  │          API Endpoints                       │  │ │
│  │  │  - POST /v1beta/models/{model}:generateContent│ │ |
│  │  │  - POST /v1beta/models/{model}:streamGenerate│  │ |
│  │  │  - POST /v1beta/models/{model}:countTokens   │  │ |
│  │  │  - GET  /v1beta/models                       │  │ |
│  │  └──────────────────────────────────────────────┘  │ │
│  └────────────────────────────────────────────────────┘ │
│                          │                              │
│                          ▼                              │
│  ┌────────────────────────────────────────────────────┐ │
│  │          Gemini Models                             │ │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐          │ │
│  │  │ 2.0 Flash│  │ 1.5 Pro  │  │1.5 Flash │          │ │
│  │  │ (Latest) │  │  (Best)  │  │ (Fast)   │          │ │
│  │  └──────────┘  └──────────┘  └──────────┘          │ │
│  └────────────────────────────────────────────────────┘ │
│                          │                              │
│                          ▼                              │
│  ┌────────────────────────────────────────────────────┐ │
│  │          Advanced Features                         │ │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐          │ │
│  │  │Function  │  │Grounding │  │   Code   │          │ │
│  │  │ Calling  │  │  Search  │  │Execution │          │ │
│  │  └──────────┘  └──────────┘  └──────────┘          │ │
│  └────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────┘
```

### 1.3 国际标准对齐

| 标准/协议 | 应用场景 | Gemini 实现 |
|-----------|----------|-------------|
| **HTTP/2 (RFC 9113)** | API通信 | REST API |
| **JSON (RFC 8259)** | 数据格式 | 请求/响应 |
| **Server-Sent Events** | 流式传输 | Streaming |
| **OAuth 2.0 (RFC 6749)** | 认证授权 | API Key + OAuth |
| **OpenTelemetry** | 可观测性 | 追踪与指标 |
| **Base64 (RFC 4648)** | 媒体编码 | 图像/音频/视频 |
| **MIME Types** | 内容类型 | Multipart |
| **gRPC** | 高性能RPC | 企业API |

---

## 2. Rust 生态集成

### 2.1 核心依赖

```toml
[package]
name = "gemini-integration"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# HTTP 客户端
reqwest = { version = "0.12", features = ["json", "stream", "multipart"] }

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

# Base64 编码
base64 = "0.22"

# 图像/音频/视频处理
image = "0.25"

# 速率限制
governor = "0.6"

# 时间处理
chrono = "0.4"

# 环境变量
dotenvy = "0.15"

# UUID
uuid = { version = "1.11", features = ["v4", "serde"] }

# MIME 类型
mime = "0.3"
```

### 2.2 项目结构

```text
gemini-integration/
├── src/
│   ├── main.rs                    # 入口
│   ├── client/
│   │   ├── mod.rs
│   │   ├── gemini.rs              # Gemini Client
│   │   └── config.rs              # 配置
│   ├── models/
│   │   ├── mod.rs
│   │   ├── content.rs             # Content Types
│   │   ├── part.rs                # Part Types (Text, Image, etc.)
│   │   └── tool.rs                # Tool/Function Definitions
│   ├── streaming/
│   │   ├── mod.rs
│   │   └── sse.rs                 # SSE Stream
│   ├── multimodal/
│   │   ├── mod.rs
│   │   ├── image.rs               # 图像处理
│   │   ├── audio.rs               # 音频处理
│   │   └── video.rs               # 视频处理
│   ├── function/
│   │   ├── mod.rs
│   │   ├── declaration.rs         # 函数声明
│   │   └── executor.rs            # 函数执行
│   ├── grounding/
│   │   ├── mod.rs
│   │   └── search.rs              # Google Search 集成
│   ├── code_execution/
│   │   ├── mod.rs
│   │   └── sandbox.rs             # 代码执行沙箱
│   ├── safety/
│   │   ├── mod.rs
│   │   └── settings.rs            # 安全设置
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
│   ├── multimodal.rs
│   ├── function_calling.rs
│   ├── grounding.rs
│   └── code_execution.rs
├── tests/
│   └── integration_test.rs
└── Cargo.toml
```

---

## 3. 基础API调用

### 3.1 客户端初始化

```rust
// src/client/gemini.rs
use anyhow::Result;
use reqwest::Client;
use serde::{Deserialize, Serialize};
use tracing::{info, instrument};

/// Gemini API Client
pub struct GeminiClient {
    client: Client,
    api_key: String,
    base_url: String,
    default_model: GeminiModel,
}

#[derive(Debug, Clone, Copy)]
pub enum GeminiModel {
    Gemini20Flash,
    Gemini15Pro,
    Gemini15Flash,
    Gemini10Pro,
}

impl GeminiModel {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Gemini20Flash => "gemini-2.0-flash-exp",
            Self::Gemini15Pro => "gemini-1.5-pro-latest",
            Self::Gemini15Flash => "gemini-1.5-flash-latest",
            Self::Gemini10Pro => "gemini-1.0-pro-latest",
        }
    }

    pub fn max_tokens(&self) -> usize {
        match self {
            Self::Gemini20Flash => 1_000_000,
            Self::Gemini15Pro => 2_000_000,
            Self::Gemini15Flash => 1_000_000,
            Self::Gemini10Pro => 32_000,
        }
    }
}

impl GeminiClient {
    /// 创建新的 Gemini 客户端
    #[instrument]
    pub fn new(api_key: String) -> Result<Self> {
        info!("Initializing Gemini client");

        let client = Client::builder()
            .timeout(std::time::Duration::from_secs(120))
            .build()?;

        Ok(Self {
            client,
            api_key,
            base_url: "https://generativelanguage.googleapis.com".to_string(),
            default_model: GeminiModel::Gemini20Flash,
        })
    }

    /// 设置默认模型
    pub fn with_model(mut self, model: GeminiModel) -> Self {
        self.default_model = model;
        self
    }

    /// 从环境变量加载
    pub fn from_env() -> Result<Self> {
        let api_key = std::env::var("GOOGLE_API_KEY")
            .or_else(|_| std::env::var("GEMINI_API_KEY"))
            .map_err(|_| anyhow::anyhow!("GOOGLE_API_KEY or GEMINI_API_KEY not set"))?;
        Self::new(api_key)
    }

    /// 获取API URL
    fn get_api_url(&self, endpoint: &str) -> String {
        format!(
            "{}/v1beta/models/{}{}",
            self.base_url,
            self.default_model.as_str(),
            endpoint
        )
    }
}
```

### 3.2 内容生成API

```rust
// src/models/content.rs
use serde::{Deserialize, Serialize};

/// 内容生成请求
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct GenerateContentRequest {
    pub contents: Vec<Content>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub generation_config: Option<GenerationConfig>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub safety_settings: Option<Vec<SafetySetting>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tools: Option<Vec<Tool>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Content {
    pub role: Role,
    pub parts: Vec<Part>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Role {
    User,
    Model,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
pub enum Part {
    Text { text: String },
    InlineData { inline_data: InlineData },
    FunctionCall { function_call: FunctionCall },
    FunctionResponse { function_response: FunctionResponse },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct InlineData {
    pub mime_type: String,
    pub data: String, // Base64 encoded
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct GenerationConfig {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub temperature: Option<f32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub top_p: Option<f32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub top_k: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub max_output_tokens: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stop_sequences: Option<Vec<String>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SafetySetting {
    pub category: HarmCategory,
    pub threshold: HarmBlockThreshold,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum HarmCategory {
    HarmCategoryUnspecified,
    HarmCategoryDerogatory,
    HarmCategoryToxicity,
    HarmCategoryViolence,
    HarmCategorySexual,
    HarmCategoryMedical,
    HarmCategoryDangerous,
    HarmCategoryHarassment,
    HarmCategoryHateSpeech,
    HarmCategorySexuallyExplicit,
    HarmCategoryDangerousContent,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum HarmBlockThreshold {
    HarmBlockThresholdUnspecified,
    BlockLowAndAbove,
    BlockMediumAndAbove,
    BlockOnlyHigh,
    BlockNone,
}

/// 内容生成响应
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct GenerateContentResponse {
    pub candidates: Vec<Candidate>,
    #[serde(default)]
    pub prompt_feedback: Option<PromptFeedback>,
    pub usage_metadata: UsageMetadata,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Candidate {
    pub content: Content,
    pub finish_reason: Option<FinishReason>,
    pub safety_ratings: Option<Vec<SafetyRating>>,
    pub citation_metadata: Option<CitationMetadata>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum FinishReason {
    FinishReasonUnspecified,
    Stop,
    MaxTokens,
    Safety,
    Recitation,
    Other,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SafetyRating {
    pub category: HarmCategory,
    pub probability: HarmProbability,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum HarmProbability {
    HarmProbabilityUnspecified,
    Negligible,
    Low,
    Medium,
    High,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct UsageMetadata {
    pub prompt_token_count: u32,
    pub candidates_token_count: u32,
    pub total_token_count: u32,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PromptFeedback {
    pub block_reason: Option<BlockReason>,
    pub safety_ratings: Vec<SafetyRating>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum BlockReason {
    BlockReasonUnspecified,
    Safety,
    Other,
}

#[derive(Debug, Clone, Deserialize)]
pub struct CitationMetadata {
    pub citation_sources: Vec<CitationSource>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CitationSource {
    pub start_index: Option<u32>,
    pub end_index: Option<u32>,
    pub uri: Option<String>,
    pub license: Option<String>,
}
```

**基础调用示例**:

```rust
// src/client/gemini.rs (续)
impl GeminiClient {
    /// 生成内容
    #[instrument(skip(self, request))]
    pub async fn generate_content(
        &self,
        request: GenerateContentRequest,
    ) -> Result<GenerateContentResponse> {
        info!(
            content_count = %request.contents.len(),
            "Generating content with Gemini"
        );

        let url = self.get_api_url(":generateContent");

        let response = self
            .client
            .post(&url)
            .query(&[("key", &self.api_key)])
            .json(&request)
            .send()
            .await?;

        if response.status().is_success() {
            let generate_response: GenerateContentResponse = response.json().await?;

            info!(
                candidates = %generate_response.candidates.len(),
                prompt_tokens = %generate_response.usage_metadata.prompt_token_count,
                total_tokens = %generate_response.usage_metadata.total_token_count,
                "Received Gemini response"
            );

            Ok(generate_response)
        } else {
            let error_text = response.text().await?;
            anyhow::bail!("Gemini API error: {}", error_text)
        }
    }

    /// 简单文本生成
    #[instrument(skip(self, prompt))]
    pub async fn generate_text(&self, prompt: &str) -> Result<String> {
        info!("Generating text with Gemini");

        let request = GenerateContentRequest {
            contents: vec![Content {
                role: Role::User,
                parts: vec![Part::Text {
                    text: prompt.to_string(),
                }],
            }],
            generation_config: None,
            safety_settings: None,
            tools: None,
        };

        let response = self.generate_content(request).await?;

        // 提取文本
        let text = response
            .candidates
            .first()
            .and_then(|c| c.content.parts.first())
            .and_then(|p| {
                if let Part::Text { text } = p {
                    Some(text.clone())
                } else {
                    None
                }
            })
            .ok_or_else(|| anyhow::anyhow!("No text in response"))?;

        Ok(text)
    }

    /// 带配置的文本生成
    #[instrument(skip(self, prompt))]
    pub async fn generate_text_with_config(
        &self,
        prompt: &str,
        config: GenerationConfig,
    ) -> Result<String> {
        info!("Generating text with config");

        let request = GenerateContentRequest {
            contents: vec![Content {
                role: Role::User,
                parts: vec![Part::Text {
                    text: prompt.to_string(),
                }],
            }],
            generation_config: Some(config),
            safety_settings: None,
            tools: None,
        };

        let response = self.generate_content(request).await?;

        let text = response
            .candidates
            .first()
            .and_then(|c| c.content.parts.first())
            .and_then(|p| {
                if let Part::Text { text } = p {
                    Some(text.clone())
                } else {
                    None
                }
            })
            .ok_or_else(|| anyhow::anyhow!("No text in response"))?;

        Ok(text)
    }
}
```

### 3.3 错误处理

```rust
// src/error.rs
use thiserror::Error;

#[derive(Error, Debug)]
pub enum GeminiError {
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

    #[error("Content blocked by safety filters: {0}")]
    ContentBlocked(String),

    #[error("Unsupported media type: {0}")]
    UnsupportedMediaType(String),

    #[error("Network error: {0}")]
    NetworkError(#[from] reqwest::Error),

    #[error("JSON error: {0}")]
    JsonError(#[from] serde_json::Error),

    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),

    #[error("Other error: {0}")]
    Other(#[from] anyhow::Error),
}

impl GeminiError {
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

### 4.1 流式生成

```rust
// src/streaming/sse.rs
use anyhow::Result;
use futures::stream::Stream;
use futures::StreamExt;
use serde::{Deserialize, Serialize};
use tracing::{info, instrument, warn};

/// 流式生成客户端
impl GeminiClient {
    /// 流式生成内容
    #[instrument(skip(self, request))]
    pub async fn stream_generate_content(
        &self,
        request: GenerateContentRequest,
    ) -> Result<impl Stream<Item = Result<GenerateContentResponse>>> {
        info!("Starting streaming generation");

        let url = self.get_api_url(":streamGenerateContent");

        let response = self
            .client
            .post(&url)
            .query(&[("key", &self.api_key), ("alt", &"sse".to_string())])
            .json(&request)
            .send()
            .await?;

        if !response.status().is_success() {
            let error_text = response.text().await?;
            anyhow::bail!("Gemini API error: {}", error_text);
        }

        // 解析 SSE 流
        let stream = response.bytes_stream().map(|chunk_result| {
            chunk_result
                .map_err(|e| anyhow::anyhow!("Stream error: {}", e))
                .and_then(|chunk| {
                    // 解析 SSE 格式: data: {...}\n\n
                    let text = String::from_utf8_lossy(&chunk);

                    for line in text.lines() {
                        if let Some(json_str) = line.strip_prefix("data: ") {
                            return serde_json::from_str::<GenerateContentResponse>(json_str)
                                .map_err(|e| anyhow::anyhow!("JSON parse error: {}", e));
                        }
                    }

                    Err(anyhow::anyhow!("No data in chunk"))
                })
        });

        Ok(stream)
    }

    /// 简单流式文本生成
    #[instrument(skip(self, prompt))]
    pub async fn stream_text(&self, prompt: &str) -> Result<impl Stream<Item = Result<String>>> {
        info!("Starting streaming text generation");

        let request = GenerateContentRequest {
            contents: vec![Content {
                role: Role::User,
                parts: vec![Part::Text {
                    text: prompt.to_string(),
                }],
            }],
            generation_config: None,
            safety_settings: None,
            tools: None,
        };

        let stream = self.stream_generate_content(request).await?;

        Ok(stream.filter_map(|result| async move {
            match result {
                Ok(response) => response
                    .candidates
                    .first()
                    .and_then(|c| c.content.parts.first())
                    .and_then(|p| {
                        if let Part::Text { text } = p {
                            Some(Ok(text.clone()))
                        } else {
                            None
                        }
                    }),
                Err(e) => Some(Err(e)),
            }
        }))
    }
}
```

### 4.2 实时响应

```rust
// examples/streaming_chat.rs
use anyhow::Result;
use futures::StreamExt;
use gemini_integration::*;
use tracing::info;

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();

    let client = GeminiClient::from_env()?;

    let prompt = "请详细解释什么是量子纠缠,包括其物理原理、实验证明和实际应用。";

    let mut stream = client.stream_text(prompt).await?;

    info!("开始接收流式响应:");
    print!("Gemini: ");

    while let Some(text_result) = stream.next().await {
        match text_result {
            Ok(text) => {
                print!("{}", text);
                std::io::Write::flush(&mut std::io::stdout())?;
            }
            Err(e) => {
                eprintln!("\nError: {}", e);
                break;
            }
        }
    }

    println!("\n\n响应完成!");

    Ok(())
}
```

---

## 5. 多模态能力

### 5.1 图像输入

```rust
// src/multimodal/image.rs
use anyhow::Result;
use base64::{Engine as _, engine::general_purpose};
use image::ImageFormat;
use std::path::Path;
use tracing::{info, instrument};

/// 图像处理器
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
        let mime_type = match format {
            ImageFormat::Jpeg => "image/jpeg",
            ImageFormat::Png => "image/png",
            ImageFormat::Gif => "image/gif",
            ImageFormat::WebP => "image/webp",
            _ => anyhow::bail!("Unsupported image format: {:?}", format),
        };

        // Base64 编码
        let encoded = general_purpose::STANDARD.encode(&image_data);

        info!(
            mime_type = %mime_type,
            size = %image_data.len(),
            "Image encoded"
        );

        Ok((mime_type.to_string(), encoded))
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
}

/// Gemini 图像能力
impl GeminiClient {
    /// 发送带图像的请求
    #[instrument(skip(self, image_path))]
    pub async fn generate_with_image(
        &self,
        prompt: &str,
        image_path: impl AsRef<Path>,
    ) -> Result<String> {
        info!("Generating with image");

        let (mime_type, encoded_image) = ImageProcessor::load_and_encode(image_path)?;

        let request = GenerateContentRequest {
            contents: vec![Content {
                role: Role::User,
                parts: vec![
                    Part::Text {
                        text: prompt.to_string(),
                    },
                    Part::InlineData {
                        inline_data: InlineData {
                            mime_type,
                            data: encoded_image,
                        },
                    },
                ],
            }],
            generation_config: None,
            safety_settings: None,
            tools: None,
        };

        let response = self.generate_content(request).await?;

        let text = response
            .candidates
            .first()
            .and_then(|c| c.content.parts.first())
            .and_then(|p| {
                if let Part::Text { text } = p {
                    Some(text.clone())
                } else {
                    None
                }
            })
            .ok_or_else(|| anyhow::anyhow!("No text in response"))?;

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

        let mut parts = vec![Part::Text {
            text: prompt.to_string(),
        }];

        for path in image_paths {
            let (mime_type, encoded_image) = ImageProcessor::load_and_encode(path)?;

            parts.push(Part::InlineData {
                inline_data: InlineData {
                    mime_type,
                    data: encoded_image,
                },
            });
        }

        let request = GenerateContentRequest {
            contents: vec![Content {
                role: Role::User,
                parts,
            }],
            generation_config: None,
            safety_settings: None,
            tools: None,
        };

        let response = self.generate_content(request).await?;

        let text = response
            .candidates
            .first()
            .and_then(|c| c.content.parts.first())
            .and_then(|p| {
                if let Part::Text { text } = p {
                    Some(text.clone())
                } else {
                    None
                }
            })
            .ok_or_else(|| anyhow::anyhow!("No text in response"))?;

        Ok(text)
    }
}
```

### 5.2 音频输入

```rust
// src/multimodal/audio.rs
use anyhow::Result;
use base64::{Engine as _, engine::general_purpose};
use std::path::Path;
use tracing::{info, instrument};

/// 音频处理器
pub struct AudioProcessor;

impl AudioProcessor {
    /// 从文件加载并编码为 Base64
    #[instrument]
    pub fn load_and_encode(path: impl AsRef<Path>) -> Result<(String, String)> {
        let path = path.as_ref();

        info!(path = %path.display(), "Loading audio");

        // 读取文件
        let audio_data = std::fs::read(path)?;

        // 根据文件扩展名确定 MIME 类型
        let mime_type = path
            .extension()
            .and_then(|ext| ext.to_str())
            .map(|ext| match ext.to_lowercase().as_str() {
                "mp3" => "audio/mpeg",
                "wav" => "audio/wav",
                "ogg" => "audio/ogg",
                "flac" => "audio/flac",
                "aac" => "audio/aac",
                _ => "audio/mpeg", // 默认
            })
            .unwrap_or("audio/mpeg");

        // Base64 编码
        let encoded = general_purpose::STANDARD.encode(&audio_data);

        info!(
            mime_type = %mime_type,
            size = %audio_data.len(),
            "Audio encoded"
        );

        Ok((mime_type.to_string(), encoded))
    }
}

/// Gemini 音频能力
impl GeminiClient {
    /// 发送带音频的请求
    #[instrument(skip(self, audio_path))]
    pub async fn generate_with_audio(
        &self,
        prompt: &str,
        audio_path: impl AsRef<Path>,
    ) -> Result<String> {
        info!("Generating with audio");

        let (mime_type, encoded_audio) = AudioProcessor::load_and_encode(audio_path)?;

        let request = GenerateContentRequest {
            contents: vec![Content {
                role: Role::User,
                parts: vec![
                    Part::Text {
                        text: prompt.to_string(),
                    },
                    Part::InlineData {
                        inline_data: InlineData {
                            mime_type,
                            data: encoded_audio,
                        },
                    },
                ],
            }],
            generation_config: None,
            safety_settings: None,
            tools: None,
        };

        let response = self.generate_content(request).await?;

        let text = response
            .candidates
            .first()
            .and_then(|c| c.content.parts.first())
            .and_then(|p| {
                if let Part::Text { text } = p {
                    Some(text.clone())
                } else {
                    None
                }
            })
            .ok_or_else(|| anyhow::anyhow!("No text in response"))?;

        Ok(text)
    }
}
```

### 5.3 视频输入

```rust
// src/multimodal/video.rs
use anyhow::Result;
use base64::{Engine as _, engine::general_purpose};
use std::path::Path;
use tracing::{info, instrument};

/// 视频处理器
pub struct VideoProcessor;

impl VideoProcessor {
    /// 从文件加载并编码为 Base64
    #[instrument]
    pub fn load_and_encode(path: impl AsRef<Path>) -> Result<(String, String)> {
        let path = path.as_ref();

        info!(path = %path.display(), "Loading video");

        // 读取文件
        let video_data = std::fs::read(path)?;

        // 根据文件扩展名确定 MIME 类型
        let mime_type = path
            .extension()
            .and_then(|ext| ext.to_str())
            .map(|ext| match ext.to_lowercase().as_str() {
                "mp4" => "video/mp4",
                "mov" => "video/quicktime",
                "avi" => "video/x-msvideo",
                "mkv" => "video/x-matroska",
                "webm" => "video/webm",
                _ => "video/mp4", // 默认
            })
            .unwrap_or("video/mp4");

        // Base64 编码
        let encoded = general_purpose::STANDARD.encode(&video_data);

        info!(
            mime_type = %mime_type,
            size = %video_data.len(),
            "Video encoded"
        );

        Ok((mime_type.to_string(), encoded))
    }
}

/// Gemini 视频能力
impl GeminiClient {
    /// 发送带视频的请求
    #[instrument(skip(self, video_path))]
    pub async fn generate_with_video(
        &self,
        prompt: &str,
        video_path: impl AsRef<Path>,
    ) -> Result<String> {
        info!("Generating with video");

        let (mime_type, encoded_video) = VideoProcessor::load_and_encode(video_path)?;

        let request = GenerateContentRequest {
            contents: vec![Content {
                role: Role::User,
                parts: vec![
                    Part::Text {
                        text: prompt.to_string(),
                    },
                    Part::InlineData {
                        inline_data: InlineData {
                            mime_type,
                            data: encoded_video,
                        },
                    },
                ],
            }],
            generation_config: None,
            safety_settings: None,
            tools: None,
        };

        let response = self.generate_content(request).await?;

        let text = response
            .candidates
            .first()
            .and_then(|c| c.content.parts.first())
            .and_then(|p| {
                if let Part::Text { text } = p {
                    Some(text.clone())
                } else {
                    None
                }
            })
            .ok_or_else(|| anyhow::anyhow!("No text in response"))?;

        Ok(text)
    }
}
```

### 5.4 多模态组合

```rust
// examples/multimodal.rs
use anyhow::Result;
use gemini_integration::*;

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();

    let client = GeminiClient::from_env()?.with_model(GeminiModel::Gemini15Pro);

    // 1. 图像分析
    println!("=== 图像分析 ===");
    let image_response = client
        .generate_with_image("请描述这张图片的内容", "image.jpg")
        .await?;
    println!("图像分析结果: {}", image_response);

    // 2. 音频转录
    println!("\n=== 音频转录 ===");
    let audio_response = client
        .generate_with_audio("请转录这段音频的内容", "audio.mp3")
        .await?;
    println!("音频转录结果: {}", audio_response);

    // 3. 视频理解
    println!("\n=== 视频理解 ===");
    let video_response = client
        .generate_with_video("请总结这个视频的主要内容", "video.mp4")
        .await?;
    println!("视频理解结果: {}", video_response);

    // 4. 多模态组合 (文本 + 多张图像)
    println!("\n=== 多模态组合 ===");
    let multi_response = client
        .analyze_multiple_images(
            "请比较这些图片的异同",
            vec!["image1.jpg", "image2.jpg", "image3.jpg"],
        )
        .await?;
    println!("多模态组合结果: {}", multi_response);

    Ok(())
}
```

---

## 参考资源

### 官方文档

- **Google Gemini API**: [https://ai.google.dev/docs](https://ai.google.dev/docs)
- **Gemini API Reference**: [https://ai.google.dev/api/rest](https://ai.google.dev/api/rest)
- **Pricing**: [https://ai.google.dev/pricing](https://ai.google.dev/pricing)

### Rust 生态

- **reqwest**: [https://docs.rs/reqwest](https://docs.rs/reqwest)
- **tokio**: [https://docs.rs/tokio](https://docs.rs/tokio)
- **OpenTelemetry Rust**: [https://docs.rs/opentelemetry](https://docs.rs/opentelemetry)

### 国际标准

- **HTTP/2 (RFC 9113)**: [https://httpwg.org/specs/rfc9113.html](https://httpwg.org/specs/rfc9113.html)
- **JSON (RFC 8259)**: [https://tools.ietf.org/html/rfc8259](https://tools.ietf.org/html/rfc8259)
- **Server-Sent Events**: [https://html.spec.whatwg.org/multipage/server-sent-events.html](https://html.spec.whatwg.org/multipage/server-sent-events.html)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-12  
**Rust 版本**: 1.90+  
**OpenTelemetry**: 0.27+  
**作者**: OTLP Rust 项目组

**注**: 本文档涵盖了 Google Gemini API 的核心功能(基础API、Streaming、多模态)。Function Calling、Grounding、Code Execution、Safety Settings、OTLP集成和生产实践等高级功能可参考官方文档进行扩展实现,实现方式与Claude API类似,主要差异在于API请求格式。
