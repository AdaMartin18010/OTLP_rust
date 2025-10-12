# OpenAI API 完整实现 - Rust 客户端 + Rust 1.90 + OTLP 集成

## 目录

- [OpenAI API 完整实现 - Rust 客户端 + Rust 1.90 + OTLP 集成](#openai-api-完整实现---rust-客户端--rust-190--otlp-集成)
  - [目录](#目录)
  - [1. OpenAI API 概述](#1-openai-api-概述)
    - [API 架构](#api-架构)
  - [2. 核心功能与架构](#2-核心功能与架构)
    - [2.1 Rust 客户端库对比](#21-rust-客户端库对比)
    - [2.2 API 端点](#22-api-端点)
  - [3. 项目配置](#3-项目配置)
    - [3.1 Cargo.toml](#31-cargotoml)
    - [3.2 环境变量配置](#32-环境变量配置)
  - [4. Chat Completion API](#4-chat-completion-api)
    - [4.1 基础客户端](#41-基础客户端)
    - [4.2 对话管理](#42-对话管理)
  - [5. Streaming 响应](#5-streaming-响应)
    - [5.1 Server-Sent Events (SSE)](#51-server-sent-events-sse)
    - [5.2 Axum 流式端点](#52-axum-流式端点)
  - [6. Function Calling](#6-function-calling)
    - [6.1 函数定义](#61-函数定义)
  - [7. Embeddings API](#7-embeddings-api)
    - [7.1 文本向量化](#71-文本向量化)
  - [8. Image Generation (DALL-E)](#8-image-generation-dall-e)
    - [8.1 图像生成](#81-图像生成)
  - [9. 错误处理与重试](#9-错误处理与重试)
    - [9.1 自定义错误类型](#91-自定义错误类型)
    - [9.2 指数退避重试](#92-指数退避重试)
  - [10. OTLP 可观测性集成](#10-otlp-可观测性集成)
    - [10.1 遥测初始化](#101-遥测初始化)
    - [10.2 自定义 Metrics](#102-自定义-metrics)
  - [11. 生产部署](#11-生产部署)
    - [11.1 Docker 配置](#111-docker-配置)
    - [11.2 Kubernetes 部署](#112-kubernetes-部署)
  - [12. 国际标准对齐](#12-国际标准对齐)
    - [12.1 API 标准](#121-api-标准)
    - [12.2 最佳实践](#122-最佳实践)
  - [总结](#总结)

---

## 1. OpenAI API 概述

**OpenAI API** 提供了强大的 AI 能力，包括：

- **GPT-4/GPT-3.5**: 自然语言生成与理解
- **Embeddings**: 文本向量化 (ada-002)
- **DALL-E**: 图像生成
- **Whisper**: 语音转文本
- **TTS**: 文本转语音

### API 架构

```text
┌──────────────────────────────────────────┐
│         OpenAI Rust Client               │
├──────────────────────────────────────────┤
│  Chat      │ Embeddings │ Images │ Audio │
│  Completion│            │        │       │
├──────────────────────────────────────────┤
│           HTTP/2 + TLS                   │
│  ┌────────────────────────────────────┐  │
│  │  Reqwest (async-std / tokio)       │  │
│  └────────────────────────────────────┘  │
├──────────────────────────────────────────┤
│          OTLP Observability              │
│  Tracing │ Metrics │ Logging             │
└──────────────────────────────────────────┘
```

---

## 2. 核心功能与架构

### 2.1 Rust 客户端库对比

| 库 | 版本 | 特性 | 维护状态 |
|---|------|------|----------|
| **async-openai** | 0.27 | 完整 API, 类型安全 | ✅ 活跃 |
| **openai-api-rs** | 5.1 | 简单易用 | ✅ 活跃 |
| **chatgpt_rs** | 2.2 | Chat 专用 | ⚠️ 维护较少 |

**推荐**: `async-openai` - 最完整的类型安全实现

### 2.2 API 端点

```text
POST /v1/chat/completions       # Chat Completion
POST /v1/embeddings             # Text Embeddings
POST /v1/images/generations     # Image Generation
POST /v1/audio/transcriptions   # Speech-to-Text
POST /v1/audio/speech           # Text-to-Speech
GET  /v1/models                 # List Models
```

---

## 3. 项目配置

### 3.1 Cargo.toml

```toml
[package]
name = "openai-rust-client"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# OpenAI 客户端
async-openai = "0.27"

# 异步运行时
tokio = { version = "1.42", features = ["full"] }
tokio-stream = "0.1"

# Web 框架
axum = "0.8"
tower = "0.5"

# HTTP 客户端
reqwest = { version = "0.12", features = ["json", "stream"] }

# OpenTelemetry (OTLP 0.25)
opentelemetry = "0.25"
opentelemetry-otlp = "0.25"
opentelemetry_sdk = { version = "0.25", features = ["rt-tokio"] }
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.26"

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 错误处理
anyhow = "1.0"
thiserror = "2.0"

# 环境变量
dotenvy = "0.15"

# 时间处理
chrono = "0.4"
```

### 3.2 环境变量配置

```bash
# .env
OPENAI_API_KEY=sk-proj-...
OPENAI_ORG_ID=org-...
OTLP_ENDPOINT=http://localhost:4317
RUST_LOG=info
```

---

## 4. Chat Completion API

### 4.1 基础客户端

```rust
use async_openai::{
    Client,
    types::{
        ChatCompletionRequestMessage, ChatCompletionRequestMessageArgs,
        CreateChatCompletionRequest, CreateChatCompletionRequestArgs,
        Role,
    },
};
use anyhow::Result;

/// OpenAI 客户端封装
pub struct OpenAIClient {
    client: Client<async_openai::config::OpenAIConfig>,
}

impl OpenAIClient {
    /// 创建客户端
    pub fn new() -> Result<Self> {
        let api_key = std::env::var("OPENAI_API_KEY")
            .context("OPENAI_API_KEY not set")?;
        
        let config = async_openai::config::OpenAIConfig::new()
            .with_api_key(&api_key);
        
        let client = Client::with_config(config);
        
        tracing::info!("OpenAI client initialized");
        
        Ok(Self { client })
    }
    
    /// Chat Completion (非流式)
    pub async fn chat_completion(
        &self,
        messages: Vec<ChatCompletionRequestMessage>,
        model: &str,
    ) -> Result<String> {
        let span = tracing::info_span!(
            "openai_chat_completion",
            model = %model,
            num_messages = %messages.len()
        );
        let _guard = span.enter();
        
        let start = std::time::Instant::now();
        
        // 创建请求
        let request = CreateChatCompletionRequestArgs::default()
            .model(model)
            .messages(messages)
            .temperature(0.7)
            .max_tokens(1000_u32)
            .build()?;
        
        // 发送请求
        let response = self.client.chat().create(request).await?;
        
        let duration = start.elapsed();
        
        // 提取响应
        let choice = response.choices.first()
            .context("No choices in response")?;
        let content = choice.message.content.clone()
            .context("No content in message")?;
        
        // 记录遥测
        tracing::info!(
            model = %model,
            prompt_tokens = %response.usage.as_ref().map(|u| u.prompt_tokens).unwrap_or(0),
            completion_tokens = %response.usage.as_ref().map(|u| u.completion_tokens).unwrap_or(0),
            total_tokens = %response.usage.as_ref().map(|u| u.total_tokens).unwrap_or(0),
            latency_ms = %duration.as_millis(),
            finish_reason = ?choice.finish_reason,
            "Chat completion successful"
        );
        
        Ok(content)
    }
}
```

### 4.2 对话管理

```rust
/// 对话历史管理
#[derive(Debug, Clone)]
pub struct Conversation {
    messages: Vec<ChatCompletionRequestMessage>,
    max_history: usize,
}

impl Conversation {
    pub fn new(system_prompt: &str, max_history: usize) -> Result<Self> {
        let system_message = ChatCompletionRequestMessageArgs::default()
            .role(Role::System)
            .content(system_prompt)
            .build()?;
        
        Ok(Self {
            messages: vec![system_message],
            max_history,
        })
    }
    
    /// 添加用户消息
    pub fn add_user_message(&mut self, content: &str) -> Result<()> {
        let message = ChatCompletionRequestMessageArgs::default()
            .role(Role::User)
            .content(content)
            .build()?;
        
        self.messages.push(message);
        self.trim_history();
        
        Ok(())
    }
    
    /// 添加助手消息
    pub fn add_assistant_message(&mut self, content: &str) -> Result<()> {
        let message = ChatCompletionRequestMessageArgs::default()
            .role(Role::Assistant)
            .content(content)
            .build()?;
        
        self.messages.push(message);
        self.trim_history();
        
        Ok(())
    }
    
    /// 裁剪历史记录 (保留 system message)
    fn trim_history(&mut self) {
        if self.messages.len() > self.max_history + 1 {
            let system_msg = self.messages[0].clone();
            self.messages.drain(1..self.messages.len() - self.max_history);
            self.messages.insert(0, system_msg);
        }
    }
    
    /// 获取所有消息
    pub fn messages(&self) -> &[ChatCompletionRequestMessage] {
        &self.messages
    }
}

/// 使用示例
pub async fn chat_example() -> Result<()> {
    let client = OpenAIClient::new()?;
    let mut conversation = Conversation::new(
        "You are a helpful Rust programming assistant.",
        10, // 最多保留 10 轮对话
    )?;
    
    // 第一轮对话
    conversation.add_user_message("What is ownership in Rust?")?;
    let response1 = client.chat_completion(
        conversation.messages().to_vec(),
        "gpt-4-turbo-preview",
    ).await?;
    conversation.add_assistant_message(&response1)?;
    
    println!("Assistant: {}", response1);
    
    // 第二轮对话
    conversation.add_user_message("Can you show me an example?")?;
    let response2 = client.chat_completion(
        conversation.messages().to_vec(),
        "gpt-4-turbo-preview",
    ).await?;
    conversation.add_assistant_message(&response2)?;
    
    println!("Assistant: {}", response2);
    
    Ok(())
}
```

---

## 5. Streaming 响应

### 5.1 Server-Sent Events (SSE)

```rust
use async_openai::types::CreateChatCompletionStreamResponse;
use tokio_stream::StreamExt;

impl OpenAIClient {
    /// Chat Completion (流式)
    pub async fn chat_completion_stream(
        &self,
        messages: Vec<ChatCompletionRequestMessage>,
        model: &str,
    ) -> Result<()> {
        let span = tracing::info_span!("openai_chat_stream", model = %model);
        let _guard = span.enter();
        
        // 创建流式请求
        let request = CreateChatCompletionRequestArgs::default()
            .model(model)
            .messages(messages)
            .temperature(0.7)
            .max_tokens(2000_u32)
            .stream(true) // 启用流式
            .build()?;
        
        let mut stream = self.client.chat().create_stream(request).await?;
        
        let mut full_response = String::new();
        let mut chunk_count = 0;
        
        // 处理流式响应
        while let Some(result) = stream.next().await {
            let response = result?;
            
            if let Some(choice) = response.choices.first() {
                if let Some(ref content) = choice.delta.content {
                    full_response.push_str(content);
                    print!("{}", content); // 实时打印
                    std::io::Write::flush(&mut std::io::stdout())?;
                    
                    chunk_count += 1;
                }
                
                // 检查结束原因
                if let Some(ref reason) = choice.finish_reason {
                    tracing::info!(
                        finish_reason = ?reason,
                        chunk_count = %chunk_count,
                        response_length = %full_response.len(),
                        "Stream completed"
                    );
                    break;
                }
            }
        }
        
        println!(); // 换行
        
        Ok(())
    }
}
```

### 5.2 Axum 流式端点

```rust
use axum::{
    response::{sse::{Event, Sse}, IntoResponse},
    Json,
};
use futures::stream::{Stream, StreamExt};

/// SSE 流式响应
pub async fn chat_stream_handler(
    Json(payload): Json<ChatRequest>,
) -> impl IntoResponse {
    let client = OpenAIClient::new().unwrap();
    
    let stream = chat_stream_impl(client, payload);
    
    Sse::new(stream)
}

/// 实现流式逻辑
async fn chat_stream_impl(
    client: OpenAIClient,
    request: ChatRequest,
) -> impl Stream<Item = Result<Event, anyhow::Error>> {
    let messages = request.to_openai_messages().unwrap();
    
    let request = CreateChatCompletionRequestArgs::default()
        .model("gpt-4-turbo-preview")
        .messages(messages)
        .stream(true)
        .build()
        .unwrap();
    
    let mut stream = client.client.chat().create_stream(request).await.unwrap();
    
    async_stream::stream! {
        while let Some(result) = stream.next().await {
            match result {
                Ok(response) => {
                    if let Some(choice) = response.choices.first() {
                        if let Some(ref content) = choice.delta.content {
                            yield Ok(Event::default().data(content));
                        }
                    }
                }
                Err(e) => {
                    tracing::error!(error = %e, "Stream error");
                    yield Err(anyhow::anyhow!("Stream error: {}", e));
                    break;
                }
            }
        }
    }
}
```

---

## 6. Function Calling

### 6.1 函数定义

```rust
use async_openai::types::{
    ChatCompletionFunctions, ChatCompletionFunctionsArgs,
    FunctionCall, FunctionCallArgs,
};
use serde_json::json;

/// 定义可调用函数
pub fn get_weather_function() -> ChatCompletionFunctions {
    ChatCompletionFunctionsArgs::default()
        .name("get_weather")
        .description("Get the current weather in a given location")
        .parameters(json!({
            "type": "object",
            "properties": {
                "location": {
                    "type": "string",
                    "description": "The city and state, e.g. San Francisco, CA"
                },
                "unit": {
                    "type": "string",
                    "enum": ["celsius", "fahrenheit"]
                }
            },
            "required": ["location"]
        }))
        .build()
        .unwrap()
}

/// 函数调用示例
pub async fn function_calling_example() -> Result<()> {
    let client = OpenAIClient::new()?;
    
    let messages = vec![
        ChatCompletionRequestMessageArgs::default()
            .role(Role::User)
            .content("What's the weather like in Boston?")
            .build()?,
    ];
    
    let request = CreateChatCompletionRequestArgs::default()
        .model("gpt-4-turbo-preview")
        .messages(messages.clone())
        .functions(vec![get_weather_function()])
        .function_call("auto") // 自动决定是否调用
        .build()?;
    
    let response = client.client.chat().create(request).await?;
    
    let choice = response.choices.first().context("No choices")?;
    
    // 检查是否需要调用函数
    if let Some(ref function_call) = choice.message.function_call {
        tracing::info!(
            function_name = %function_call.name,
            arguments = %function_call.arguments,
            "Function call requested"
        );
        
        // 解析参数
        let args: serde_json::Value = serde_json::from_str(&function_call.arguments)?;
        let location = args["location"].as_str().unwrap();
        let unit = args.get("unit")
            .and_then(|v| v.as_str())
            .unwrap_or("celsius");
        
        // 执行函数 (模拟)
        let weather_data = get_weather_impl(location, unit).await?;
        
        // 将函数结果返回给模型
        let mut messages = messages;
        messages.push(
            ChatCompletionRequestMessageArgs::default()
                .role(Role::Function)
                .name(&function_call.name)
                .content(&weather_data)
                .build()?,
        );
        
        let final_request = CreateChatCompletionRequestArgs::default()
            .model("gpt-4-turbo-preview")
            .messages(messages)
            .build()?;
        
        let final_response = client.client.chat().create(final_request).await?;
        
        let final_content = final_response.choices.first()
            .and_then(|c| c.message.content.as_ref())
            .context("No final content")?;
        
        println!("Final response: {}", final_content);
    }
    
    Ok(())
}

/// 模拟天气 API
async fn get_weather_impl(location: &str, unit: &str) -> Result<String> {
    // 实际应用中这里会调用真实的天气 API
    Ok(json!({
        "location": location,
        "temperature": 22,
        "unit": unit,
        "condition": "sunny"
    }).to_string())
}
```

---

## 7. Embeddings API

### 7.1 文本向量化

```rust
use async_openai::types::{CreateEmbeddingRequest, CreateEmbeddingRequestArgs};

impl OpenAIClient {
    /// 获取文本 Embedding
    pub async fn create_embedding(&self, text: &str) -> Result<Vec<f32>> {
        let span = tracing::info_span!("openai_embedding", text_len = %text.len());
        let _guard = span.enter();
        
        let start = std::time::Instant::now();
        
        let request = CreateEmbeddingRequestArgs::default()
            .model("text-embedding-ada-002")
            .input(text)
            .build()?;
        
        let response = self.client.embeddings().create(request).await?;
        
        let duration = start.elapsed();
        
        let embedding = response.data.first()
            .context("No embedding in response")?
            .embedding
            .clone();
        
        tracing::info!(
            embedding_dim = %embedding.len(),
            total_tokens = %response.usage.total_tokens,
            latency_ms = %duration.as_millis(),
            "Embedding created"
        );
        
        Ok(embedding)
    }
    
    /// 批量 Embedding
    pub async fn create_embeddings_batch(&self, texts: Vec<&str>) -> Result<Vec<Vec<f32>>> {
        let span = tracing::info_span!("openai_embeddings_batch", batch_size = %texts.len());
        let _guard = span.enter();
        
        let request = CreateEmbeddingRequestArgs::default()
            .model("text-embedding-ada-002")
            .input(texts)
            .build()?;
        
        let response = self.client.embeddings().create(request).await?;
        
        let embeddings: Vec<Vec<f32>> = response.data
            .into_iter()
            .map(|data| data.embedding)
            .collect();
        
        tracing::info!(
            num_embeddings = %embeddings.len(),
            total_tokens = %response.usage.total_tokens,
            "Batch embeddings created"
        );
        
        Ok(embeddings)
    }
}

/// 余弦相似度计算
pub fn cosine_similarity(a: &[f32], b: &[f32]) -> f32 {
    let dot_product: f32 = a.iter().zip(b.iter()).map(|(x, y)| x * y).sum();
    let norm_a: f32 = a.iter().map(|x| x * x).sum::<f32>().sqrt();
    let norm_b: f32 = b.iter().map(|x| x * x).sum::<f32>().sqrt();
    
    dot_product / (norm_a * norm_b)
}

/// 语义搜索示例
pub async fn semantic_search_example() -> Result<()> {
    let client = OpenAIClient::new()?;
    
    let documents = vec![
        "Rust is a systems programming language.",
        "Python is great for machine learning.",
        "Rust provides memory safety without garbage collection.",
    ];
    
    // 获取文档 embeddings
    let doc_embeddings = client.create_embeddings_batch(documents.clone()).await?;
    
    // 查询
    let query = "Tell me about Rust programming";
    let query_embedding = client.create_embedding(query).await?;
    
    // 计算相似度
    let similarities: Vec<(usize, f32)> = doc_embeddings
        .iter()
        .enumerate()
        .map(|(i, emb)| (i, cosine_similarity(&query_embedding, emb)))
        .collect();
    
    // 排序
    let mut similarities = similarities;
    similarities.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());
    
    for (idx, score) in similarities {
        println!("[{:.4}] {}", score, documents[idx]);
    }
    
    Ok(())
}
```

---

## 8. Image Generation (DALL-E)

### 8.1 图像生成

```rust
use async_openai::types::{
    CreateImageRequest, CreateImageRequestArgs,
    ImageSize, ImageQuality, ImageStyle,
};

impl OpenAIClient {
    /// DALL-E 图像生成
    pub async fn generate_image(
        &self,
        prompt: &str,
        size: ImageSize,
    ) -> Result<Vec<String>> {
        let span = tracing::info_span!(
            "openai_image_generation",
            prompt = %prompt,
            size = ?size
        );
        let _guard = span.enter();
        
        let start = std::time::Instant::now();
        
        let request = CreateImageRequestArgs::default()
            .prompt(prompt)
            .model("dall-e-3")
            .n(1_u8) // 生成数量
            .size(size)
            .quality(ImageQuality::HD)
            .style(ImageStyle::Vivid)
            .build()?;
        
        let response = self.client.images().create(request).await?;
        
        let duration = start.elapsed();
        
        let image_urls: Vec<String> = response.data
            .into_iter()
            .filter_map(|img| img.url)
            .collect();
        
        tracing::info!(
            num_images = %image_urls.len(),
            latency_ms = %duration.as_millis(),
            "Images generated"
        );
        
        Ok(image_urls)
    }
    
    /// 下载图像
    pub async fn download_image(&self, url: &str, output_path: &str) -> Result<()> {
        let response = reqwest::get(url).await?;
        let bytes = response.bytes().await?;
        
        tokio::fs::write(output_path, &bytes).await?;
        
        tracing::info!(
            url = %url,
            output_path = %output_path,
            size_bytes = %bytes.len(),
            "Image downloaded"
        );
        
        Ok(())
    }
}

/// 使用示例
pub async fn dalle_example() -> Result<()> {
    let client = OpenAIClient::new()?;
    
    let prompt = "A futuristic Rust crab robot in a cyberpunk city";
    let urls = client.generate_image(prompt, ImageSize::S1024x1024).await?;
    
    for (i, url) in urls.iter().enumerate() {
        client.download_image(url, &format!("generated_{}.png", i)).await?;
    }
    
    Ok(())
}
```

---

## 9. 错误处理与重试

### 9.1 自定义错误类型

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum OpenAIError {
    #[error("API error: {0}")]
    ApiError(String),
    
    #[error("Rate limit exceeded")]
    RateLimitExceeded,
    
    #[error("Invalid API key")]
    InvalidApiKey,
    
    #[error("Request timeout")]
    Timeout,
    
    #[error("Network error: {0}")]
    NetworkError(#[from] reqwest::Error),
    
    #[error("Serialization error: {0}")]
    SerializationError(#[from] serde_json::Error),
}
```

### 9.2 指数退避重试

```rust
use tokio::time::{sleep, Duration};

/// 带重试的 API 调用
pub async fn chat_with_retry(
    client: &OpenAIClient,
    messages: Vec<ChatCompletionRequestMessage>,
    max_retries: u32,
) -> Result<String> {
    let mut retry_count = 0;
    let mut backoff = Duration::from_secs(1);
    
    loop {
        match client.chat_completion(messages.clone(), "gpt-4-turbo-preview").await {
            Ok(response) => return Ok(response),
            Err(e) => {
                if retry_count >= max_retries {
                    tracing::error!(
                        error = %e,
                        retry_count = %retry_count,
                        "Max retries exceeded"
                    );
                    return Err(e);
                }
                
                tracing::warn!(
                    error = %e,
                    retry_count = %retry_count,
                    backoff_ms = %backoff.as_millis(),
                    "Retrying after error"
                );
                
                sleep(backoff).await;
                
                retry_count += 1;
                backoff *= 2; // 指数退避
            }
        }
    }
}
```

---

## 10. OTLP 可观测性集成

### 10.1 遥测初始化

```rust
use opentelemetry::{global, trace::TracerProvider, KeyValue};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{runtime, trace::Config, Resource};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};

/// 初始化 OpenAI 遥测
pub fn init_openai_telemetry() -> anyhow::Result<()> {
    let otlp_endpoint = std::env::var("OTLP_ENDPOINT")
        .unwrap_or_else(|_| "http://localhost:4317".to_string());
    
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint(&otlp_endpoint),
        )
        .with_trace_config(
            Config::default()
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", "openai-rust-client"),
                    KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
                    KeyValue::new("ai.provider", "openai"),
                ])),
        )
        .install_batch(runtime::Tokio)?;
    
    tracing_subscriber::registry()
        .with(EnvFilter::from_default_env())
        .with(tracing_subscriber::fmt::layer().json())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();
    
    tracing::info!("OpenAI telemetry initialized");
    Ok(())
}
```

### 10.2 自定义 Metrics

```rust
use opentelemetry::{metrics::{Counter, Histogram}, global};

/// AI Metrics 收集器
pub struct AIMetrics {
    request_counter: Counter<u64>,
    request_latency: Histogram<f64>,
    token_usage: Histogram<u64>,
}

impl AIMetrics {
    pub fn new() -> Self {
        let meter = global::meter("openai-client");
        
        Self {
            request_counter: meter
                .u64_counter("ai.request.count")
                .with_description("Total AI requests")
                .init(),
            
            request_latency: meter
                .f64_histogram("ai.request.duration")
                .with_description("AI request latency")
                .with_unit("s")
                .init(),
            
            token_usage: meter
                .u64_histogram("ai.token.usage")
                .with_description("Token usage per request")
                .init(),
        }
    }
    
    pub fn record_request(
        &self,
        duration: Duration,
        model: &str,
        tokens: u64,
    ) {
        self.request_counter.add(1, &[
            KeyValue::new("model", model.to_string()),
        ]);
        
        self.request_latency.record(duration.as_secs_f64(), &[]);
        self.token_usage.record(tokens, &[]);
    }
}
```

---

## 11. 生产部署

### 11.1 Docker 配置

```dockerfile
# Dockerfile
FROM rust:1.90-slim

RUN apt-get update && apt-get install -y \
    libssl-dev \
    pkg-config \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app
COPY Cargo.toml Cargo.lock ./
COPY src ./src

RUN cargo build --release

CMD ["./target/release/openai-rust-client"]
```

### 11.2 Kubernetes 部署

```yaml
# openai-deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: openai-service
spec:
  replicas: 3
  selector:
    matchLabels:
      app: openai-service
  template:
    metadata:
      labels:
        app: openai-service
    spec:
      containers:
      - name: openai
        image: openai-rust-client:latest
        env:
        - name: OPENAI_API_KEY
          valueFrom:
            secretKeyRef:
              name: openai-secret
              key: api-key
        - name: OTLP_ENDPOINT
          value: "http://otel-collector:4317"
        resources:
          limits:
            memory: "512Mi"
            cpu: "500m"
        ports:
        - containerPort: 8080
```

---

## 12. 国际标准对齐

### 12.1 API 标准

| 标准 | 规范 | 实现 |
|------|------|------|
| **OpenAI API** | v1 | `async-openai` |
| **HTTP/2** | RFC 7540 | `reqwest` |
| **Server-Sent Events** | W3C | `axum::sse` |
| **OpenTelemetry** | v1.31 | `tracing-opentelemetry` |
| **OAuth 2.0** | RFC 6749 | API Key Bearer |

### 12.2 最佳实践

- **Stanford HAI**: Responsible AI Guidelines
- **OpenAI**: Best Practices for Production
- **NIST AI Risk Management**: Framework 1.0

---

## 总结

**OpenAI API Rust 客户端** 提供了：

- ✅ 完整的 API 覆盖 (Chat, Embeddings, Images)
- ✅ 流式响应支持 (SSE)
- ✅ Function Calling 集成
- ✅ 错误处理与重试机制
- ✅ OTLP 可观测性集成
- ✅ 生产级部署配置

**下一步扩展**:

- Anthropic Claude API
- Google Gemini API
- Local LLM (Ollama, llama.cpp)
- Prompt 优化与缓存
