# Local LLM 完整实现 - Ollama + llama.cpp - Rust 1.90 + OTLP 集成

## 目录

- [Local LLM 完整实现 - Ollama + llama.cpp - Rust 1.90 + OTLP 集成](#local-llm-完整实现---ollama--llamacpp---rust-190--otlp-集成)
  - [目录](#目录)
  - [1. 核心概念与架构](#1-核心概念与架构)
    - [1.1 本地LLM优势](#11-本地llm优势)
    - [1.2 Ollama vs llama.cpp](#12-ollama-vs-llamacpp)
    - [1.3 国际标准对齐](#13-国际标准对齐)
  - [2. Ollama集成](#2-ollama集成)
    - [2.1 Rust依赖](#21-rust依赖)
    - [2.2 REST API客户端](#22-rest-api客户端)
    - [2.3 文本生成](#23-文本生成)
    - [2.4 对话管理](#24-对话管理)
    - [2.5 Embeddings向量](#25-embeddings向量)
    - [2.6 模型管理](#26-模型管理)
    - [2.7 流式响应](#27-流式响应)
  - [3. llama.cpp集成](#3-llamacpp集成)
    - [3.1 FFI绑定](#31-ffi绑定)
    - [3.2 模型加载](#32-模型加载)
    - [3.3 推理引擎](#33-推理引擎)
    - [3.4 量化支持](#34-量化支持)
    - [3.5 GPU加速](#35-gpu加速)
  - [4. 性能优化](#4-性能优化)
    - [4.1 KV Cache](#41-kv-cache)
    - [4.2 Batching](#42-batching)
    - [4.3 并发控制](#43-并发控制)
  - [5. OTLP可观测性](#5-otlp可观测性)
    - [5.1 推理追踪](#51-推理追踪)
    - [5.2 性能指标](#52-性能指标)
    - [5.3 资源监控](#53-资源监控)
  - [6. 生产部署](#6-生产部署)
    - [6.1 Docker部署](#61-docker部署)
    - [6.2 Kubernetes部署](#62-kubernetes部署)
  - [7. 参考资源](#7-参考资源)
    - [官方文档](#官方文档)
    - [Rust生态](#rust生态)
    - [模型资源](#模型资源)

---

## 1. 核心概念与架构

### 1.1 本地LLM优势

本地部署LLM相比云端API的核心优势:

| 维度 | 本地LLM | 云端API |
|------|---------|---------|
| **数据隐私** | ✅ 数据不出本地 | ⚠️ 需信任供应商 |
| **成本** | ✅ 硬件一次性投入 | ⚠️ 按Token计费 |
| **延迟** | ✅ 无网络延迟 | ⚠️ 网络往返 |
| **离线可用** | ✅ 完全离线 | ❌ 需要网络 |
| **定制化** | ✅ 完全控制 | ⚠️ 受限 |
| **扩展性** | ⚠️ 硬件限制 | ✅ 弹性伸缩 |
| **模型选择** | ✅ 开源模型多样 | ⚠️ 供应商模型 |
| **推理质量** | ⚠️ 取决于模型大小 | ✅ 顶级模型 |

### 1.2 Ollama vs llama.cpp

| 特性 | Ollama | llama.cpp |
|------|--------|-----------|
| **抽象层次** | 高级(REST API) | 低级(C++库) |
| **易用性** | ✅ 开箱即用 | ⚠️ 需要编译 |
| **性能** | 优秀 | ✅ 极致优化 |
| **模型管理** | ✅ 自动下载 | ⚠️ 手动管理 |
| **跨平台** | ✅ 全平台 | ✅ 全平台 |
| **GPU支持** | ✅ CUDA/ROCm/Metal | ✅ CUDA/ROCm/Metal |
| **量化** | ✅ 自动 | ✅ 多种格式 |
| **适用场景** | 快速原型、生产 | 嵌入式、极致性能 |

**架构图**:

```text
┌─────────────────────────────────────────────────────────┐
│              Local LLM Architecture                     │
│                                                         │
│  ┌────────────────────────────────────────────────────┐ │
│  │          Rust Application                          │ │
│  │  ┌──────────────────────────────────────────────┐  │ │
│  │  │       Unified LLM Interface                  │  │ │
│  │  │  - generate_text()                           │  │ │
│  │  │  - stream_text()                             │  │ │
│  │  │  - embeddings()                              │  │ │
│  │  └──────────────────────────────────────────────┘  │ │
│  │          │                      │                  │ │
│  │          │                      │                  │ │
│  │    ┌─────▼─────┐          ┌────▼─────┐             │ │
│  │    │  Ollama   │          │ llama.cpp│             │ │
│  │    │  Client   │          │   FFI    │             │ │
│  │    └─────┬─────┘          └────┬─────┘             │ │
│  └──────────┼──────────────────────┼──────────────────┘ │
│             │ HTTP                 │ C ABI              │
│             ▼                      ▼                    │
│  ┌──────────────────┐   ┌─────────────────────┐         │
│  │  Ollama Server   │   │  llama.cpp Library  │         │
│  │  (REST API)      │   │  (Native Code)      │         │
│  │  - Port 11434    │   │  - .so/.dylib/.dll  │         │
│  └──────────────────┘   └─────────────────────┘         │
│             │                      │                    │
│             ▼                      ▼                    │
│  ┌────────────────────────────────────────────────┐     │
│  │          GGUF Models                           │     │
│  │  ~/.ollama/models/  or  ./models/              │     │
│  │  - llama-3.1-8b-q4_0.gguf                      │     │
│  │  - mistral-7b-q5_k_m.gguf                      │     │
│  │  - codellama-13b-q8_0.gguf                     │     │
│  └────────────────────────────────────────────────┘     │
│             │                      │                    │
│             ▼                      ▼                    │
│  ┌────────────────────────────────────────────────┐     │
│  │          Hardware Acceleration                 │     │
│  │  - CUDA (NVIDIA GPU)                           │     │
│  │  - ROCm (AMD GPU)                              │     │
│  │  - Metal (Apple Silicon)                       │     │
│  │  - AVX2/AVX512 (CPU SIMD)                      │     │
│  └────────────────────────────────────────────────┘     │
└─────────────────────────────────────────────────────────┘
```

### 1.3 国际标准对齐

| 标准/协议 | 应用场景 | Local LLM实现 |
|-----------|----------|---------------|
| **HTTP/1.1 (RFC 7230)** | Ollama API | REST接口 |
| **JSON Lines (NDJSON)** | 流式响应 | Ollama Streaming |
| **JSON (RFC 8259)** | 数据格式 | 请求/响应 |
| **OpenTelemetry** | 可观测性 | 追踪与指标 |
| **GGUF Format** | 模型存储 | 量化模型 |
| **C ABI** | FFI | llama.cpp绑定 |

---

## 2. Ollama集成

### 2.1 Rust依赖

```toml
[package]
name = "local-llm-integration"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# HTTP客户端
reqwest = { version = "0.12", features = ["json", "stream"] }

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

# OpenTelemetry
opentelemetry = "0.27"
opentelemetry-otlp = { version = "0.27", features = ["grpc-tonic", "metrics", "trace"] }
opentelemetry_sdk = { version = "0.27", features = ["rt-tokio"] }
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
tracing-opentelemetry = "0.28"

# llama.cpp FFI (可选)
llama-cpp-rs = "0.1"  # 社区维护的绑定

# 或直接使用bindgen
# bindgen = "0.69"

# 时间处理
chrono = "0.4"

# UUID
uuid = { version = "1.11", features = ["v4"] }
```

### 2.2 REST API客户端

```rust
// src/ollama/client.rs
use anyhow::Result;
use reqwest::Client;
use serde::{Deserialize, Serialize};
use tracing::{info, instrument};

/// Ollama客户端
pub struct OllamaClient {
    client: Client,
    base_url: String,
}

impl OllamaClient {
    /// 创建新的Ollama客户端
    #[instrument]
    pub fn new(base_url: impl Into<String>) -> Result<Self> {
        info!("Initializing Ollama client");

        let client = Client::builder()
            .timeout(std::time::Duration::from_secs(300)) // 5分钟超时
            .build()?;

        Ok(Self {
            client,
            base_url: base_url.into(),
        })
    }

    /// 使用默认端口
    pub fn default() -> Result<Self> {
        Self::new("http://localhost:11434")
    }

    /// 健康检查
    #[instrument(skip(self))]
    pub async fn health_check(&self) -> Result<bool> {
        let response = self.client.get(&self.base_url).send().await?;
        Ok(response.status().is_success())
    }
}
```

### 2.3 文本生成

```rust
// src/ollama/generate.rs
use serde::{Deserialize, Serialize};

/// 生成请求
#[derive(Debug, Clone, Serialize)]
pub struct GenerateRequest {
    pub model: String,
    pub prompt: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub system: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub template: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub context: Option<Vec<i64>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub options: Option<GenerateOptions>,
    #[serde(default)]
    pub stream: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GenerateOptions {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub temperature: Option<f32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub top_p: Option<f32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub top_k: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub num_predict: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stop: Option<Vec<String>>,
}

/// 生成响应
#[derive(Debug, Clone, Deserialize)]
pub struct GenerateResponse {
    pub model: String,
    pub created_at: String,
    pub response: String,
    pub done: bool,
    #[serde(default)]
    pub context: Vec<i64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub total_duration: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub load_duration: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub prompt_eval_count: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub prompt_eval_duration: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub eval_count: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub eval_duration: Option<u64>,
}

impl OllamaClient {
    /// 生成文本
    #[instrument(skip(self, request))]
    pub async fn generate(&self, request: GenerateRequest) -> Result<GenerateResponse> {
        info!(model = %request.model, "Generating text with Ollama");

        let url = format!("{}/api/generate", self.base_url);

        let response = self
            .client
            .post(&url)
            .json(&request)
            .send()
            .await?;

        if response.status().is_success() {
            let generate_response: GenerateResponse = response.json().await?;

            info!(
                model = %generate_response.model,
                response_length = %generate_response.response.len(),
                "Generated text successfully"
            );

            Ok(generate_response)
        } else {
            let error_text = response.text().await?;
            anyhow::bail!("Ollama API error: {}", error_text)
        }
    }

    /// 简单文本生成
    #[instrument(skip(self, prompt))]
    pub async fn generate_simple(&self, model: &str, prompt: &str) -> Result<String> {
        let request = GenerateRequest {
            model: model.to_string(),
            prompt: prompt.to_string(),
            system: None,
            template: None,
            context: None,
            options: None,
            stream: false,
        };

        let response = self.generate(request).await?;
        Ok(response.response)
    }
}
```

### 2.4 对话管理

```rust
// src/ollama/chat.rs
use serde::{Deserialize, Serialize};

/// 对话请求
#[derive(Debug, Clone, Serialize)]
pub struct ChatRequest {
    pub model: String,
    pub messages: Vec<Message>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub options: Option<GenerateOptions>,
    #[serde(default)]
    pub stream: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Message {
    pub role: Role,
    pub content: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub images: Option<Vec<String>>, // Base64编码
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Role {
    System,
    User,
    Assistant,
}

/// 对话响应
#[derive(Debug, Clone, Deserialize)]
pub struct ChatResponse {
    pub model: String,
    pub created_at: String,
    pub message: Message,
    pub done: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub total_duration: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub load_duration: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub prompt_eval_count: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub eval_count: Option<u32>,
}

impl OllamaClient {
    /// 对话
    #[instrument(skip(self, request))]
    pub async fn chat(&self, request: ChatRequest) -> Result<ChatResponse> {
        info!(model = %request.model, messages = %request.messages.len(), "Chat with Ollama");

        let url = format!("{}/api/chat", self.base_url);

        let response = self
            .client
            .post(&url)
            .json(&request)
            .send()
            .await?;

        if response.status().is_success() {
            let chat_response: ChatResponse = response.json().await?;

            info!(
                model = %chat_response.model,
                response_length = %chat_response.message.content.len(),
                "Chat completed successfully"
            );

            Ok(chat_response)
        } else {
            let error_text = response.text().await?;
            anyhow::bail!("Ollama API error: {}", error_text)
        }
    }

    /// 简单对话
    #[instrument(skip(self, user_message))]
    pub async fn chat_simple(&self, model: &str, user_message: &str) -> Result<String> {
        let request = ChatRequest {
            model: model.to_string(),
            messages: vec![Message {
                role: Role::User,
                content: user_message.to_string(),
                images: None,
            }],
            options: None,
            stream: false,
        };

        let response = self.chat(request).await?;
        Ok(response.message.content)
    }
}
```

### 2.5 Embeddings向量

```rust
// src/ollama/embeddings.rs
use serde::{Deserialize, Serialize};

/// Embeddings请求
#[derive(Debug, Clone, Serialize)]
pub struct EmbeddingsRequest {
    pub model: String,
    pub prompt: String,
}

/// Embeddings响应
#[derive(Debug, Clone, Deserialize)]
pub struct EmbeddingsResponse {
    pub embedding: Vec<f32>,
}

impl OllamaClient {
    /// 获取文本向量
    #[instrument(skip(self, prompt))]
    pub async fn embeddings(&self, model: &str, prompt: &str) -> Result<Vec<f32>> {
        info!(model = %model, "Getting embeddings from Ollama");

        let url = format!("{}/api/embeddings", self.base_url);

        let request = EmbeddingsRequest {
            model: model.to_string(),
            prompt: prompt.to_string(),
        };

        let response = self
            .client
            .post(&url)
            .json(&request)
            .send()
            .await?;

        if response.status().is_success() {
            let embeddings_response: EmbeddingsResponse = response.json().await?;

            info!(
                dimensions = %embeddings_response.embedding.len(),
                "Got embeddings successfully"
            );

            Ok(embeddings_response.embedding)
        } else {
            let error_text = response.text().await?;
            anyhow::bail!("Ollama API error: {}", error_text)
        }
    }

    /// 批量获取向量
    #[instrument(skip(self, prompts))]
    pub async fn embeddings_batch(
        &self,
        model: &str,
        prompts: &[String],
    ) -> Result<Vec<Vec<f32>>> {
        info!(model = %model, count = %prompts.len(), "Getting batch embeddings");

        let mut embeddings = Vec::new();

        for prompt in prompts {
            let embedding = self.embeddings(model, prompt).await?;
            embeddings.push(embedding);
        }

        Ok(embeddings)
    }
}
```

### 2.6 模型管理

```rust
// src/ollama/models.rs
use serde::{Deserialize, Serialize};

/// 模型信息
#[derive(Debug, Clone, Deserialize)]
pub struct ModelInfo {
    pub name: String,
    pub modified_at: String,
    pub size: u64,
    pub digest: String,
    pub details: ModelDetails,
}

#[derive(Debug, Clone, Deserialize)]
pub struct ModelDetails {
    pub format: String,
    pub family: String,
    pub families: Option<Vec<String>>,
    pub parameter_size: String,
    pub quantization_level: String,
}

/// 模型列表响应
#[derive(Debug, Clone, Deserialize)]
pub struct ListModelsResponse {
    pub models: Vec<ModelInfo>,
}

/// Pull请求
#[derive(Debug, Clone, Serialize)]
pub struct PullRequest {
    pub name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub insecure: Option<bool>,
}

/// Pull响应
#[derive(Debug, Clone, Deserialize)]
pub struct PullResponse {
    pub status: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub digest: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub total: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub completed: Option<u64>,
}

impl OllamaClient {
    /// 列出本地模型
    #[instrument(skip(self))]
    pub async fn list_models(&self) -> Result<Vec<ModelInfo>> {
        info!("Listing local models");

        let url = format!("{}/api/tags", self.base_url);

        let response = self.client.get(&url).send().await?;

        if response.status().is_success() {
            let list_response: ListModelsResponse = response.json().await?;

            info!(count = %list_response.models.len(), "Listed models successfully");

            Ok(list_response.models)
        } else {
            let error_text = response.text().await?;
            anyhow::bail!("Ollama API error: {}", error_text)
        }
    }

    /// 拉取模型
    #[instrument(skip(self))]
    pub async fn pull_model(&self, name: &str) -> Result<()> {
        info!(name = %name, "Pulling model");

        let url = format!("{}/api/pull", self.base_url);

        let request = PullRequest {
            name: name.to_string(),
            insecure: None,
        };

        let response = self
            .client
            .post(&url)
            .json(&request)
            .send()
            .await?;

        if response.status().is_success() {
            info!(name = %name, "Model pulled successfully");
            Ok(())
        } else {
            let error_text = response.text().await?;
            anyhow::bail!("Ollama API error: {}", error_text)
        }
    }

    /// 删除模型
    #[instrument(skip(self))]
    pub async fn delete_model(&self, name: &str) -> Result<()> {
        info!(name = %name, "Deleting model");

        let url = format!("{}/api/delete", self.base_url);

        let request = serde_json::json!({
            "name": name
        });

        let response = self
            .client
            .delete(&url)
            .json(&request)
            .send()
            .await?;

        if response.status().is_success() {
            info!(name = %name, "Model deleted successfully");
            Ok(())
        } else {
            let error_text = response.text().await?;
            anyhow::bail!("Ollama API error: {}", error_text)
        }
    }
}
```

### 2.7 流式响应

```rust
// src/ollama/streaming.rs
use futures::stream::Stream;
use futures::StreamExt;
use tracing::{info, instrument, warn};

impl OllamaClient {
    /// 流式生成
    #[instrument(skip(self, request))]
    pub async fn generate_stream(
        &self,
        mut request: GenerateRequest,
    ) -> Result<impl Stream<Item = Result<GenerateResponse>>> {
        info!(model = %request.model, "Starting streaming generation");

        request.stream = true;

        let url = format!("{}/api/generate", self.base_url);

        let response = self
            .client
            .post(&url)
            .json(&request)
            .send()
            .await?;

        if !response.status().is_success() {
            let error_text = response.text().await?;
            anyhow::bail!("Ollama API error: {}", error_text);
        }

        // 解析JSON Lines流
        let stream = response.bytes_stream().map(|chunk_result| {
            chunk_result
                .map_err(|e| anyhow::anyhow!("Stream error: {}", e))
                .and_then(|chunk| {
                    let text = String::from_utf8_lossy(&chunk);

                    for line in text.lines() {
                        if !line.trim().is_empty() {
                            return serde_json::from_str::<GenerateResponse>(line)
                                .map_err(|e| anyhow::anyhow!("JSON parse error: {}", e));
                        }
                    }

                    Err(anyhow::anyhow!("No data in chunk"))
                })
        });

        Ok(stream)
    }

    /// 流式对话
    #[instrument(skip(self, request))]
    pub async fn chat_stream(
        &self,
        mut request: ChatRequest,
    ) -> Result<impl Stream<Item = Result<ChatResponse>>> {
        info!(model = %request.model, "Starting streaming chat");

        request.stream = true;

        let url = format!("{}/api/chat", self.base_url);

        let response = self
            .client
            .post(&url)
            .json(&request)
            .send()
            .await?;

        if !response.status().is_success() {
            let error_text = response.text().await?;
            anyhow::bail!("Ollama API error: {}", error_text);
        }

        let stream = response.bytes_stream().map(|chunk_result| {
            chunk_result
                .map_err(|e| anyhow::anyhow!("Stream error: {}", e))
                .and_then(|chunk| {
                    let text = String::from_utf8_lossy(&chunk);

                    for line in text.lines() {
                        if !line.trim().is_empty() {
                            return serde_json::from_str::<ChatResponse>(line)
                                .map_err(|e| anyhow::anyhow!("JSON parse error: {}", e));
                        }
                    }

                    Err(anyhow::anyhow!("No data in chunk"))
                })
        });

        Ok(stream)
    }
}

// 使用示例
// examples/ollama_streaming.rs
use anyhow::Result;
use futures::StreamExt;
use local_llm_integration::*;

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();

    let client = OllamaClient::default()?;

    let request = GenerateRequest {
        model: "llama3.1:8b".to_string(),
        prompt: "解释量子计算的基本原理".to_string(),
        system: None,
        template: None,
        context: None,
        options: None,
        stream: true,
    };

    let mut stream = client.generate_stream(request).await?;

    print!("Response: ");

    while let Some(response_result) = stream.next().await {
        match response_result {
            Ok(response) => {
                print!("{}", response.response);
                std::io::Write::flush(&mut std::io::stdout())?;

                if response.done {
                    println!("\n\nCompleted!");
                    if let Some(eval_count) = response.eval_count {
                        println!("Generated {} tokens", eval_count);
                    }
                    break;
                }
            }
            Err(e) => {
                eprintln!("\nError: {}", e);
                break;
            }
        }
    }

    Ok(())
}
```

---

## 3. llama.cpp集成

### 3.1 FFI绑定

```rust
// src/llama_cpp/bindings.rs
use std::ffi::{CStr, CString};
use std::os::raw::{c_char, c_float, c_int};
use std::ptr;

// llama.cpp C API绑定
#[repr(C)]
pub struct LlamaModel {
    _private: [u8; 0],
}

#[repr(C)]
pub struct LlamaContext {
    _private: [u8; 0],
}

#[repr(C)]
pub struct LlamaModelParams {
    pub n_gpu_layers: c_int,
    pub main_gpu: c_int,
    pub use_mmap: bool,
    pub use_mlock: bool,
}

#[repr(C)]
pub struct LlamaContextParams {
    pub n_ctx: u32,
    pub n_batch: u32,
    pub n_threads: c_int,
    pub rope_freq_base: c_float,
    pub rope_freq_scale: c_float,
}

#[link(name = "llama")]
extern "C" {
    // 模型加载
    pub fn llama_load_model_from_file(
        path: *const c_char,
        params: LlamaModelParams,
    ) -> *mut LlamaModel;

    pub fn llama_free_model(model: *mut LlamaModel);

    // 上下文创建
    pub fn llama_new_context_with_model(
        model: *const LlamaModel,
        params: LlamaContextParams,
    ) -> *mut LlamaContext;

    pub fn llama_free(ctx: *mut LlamaContext);

    // Token化
    pub fn llama_tokenize(
        ctx: *const LlamaContext,
        text: *const c_char,
        tokens: *mut c_int,
        n_max_tokens: c_int,
        add_bos: bool,
    ) -> c_int;

    // 推理
    pub fn llama_eval(
        ctx: *mut LlamaContext,
        tokens: *const c_int,
        n_tokens: c_int,
        n_past: c_int,
        n_threads: c_int,
    ) -> c_int;

    // 采样
    pub fn llama_sample_top_k(
        ctx: *mut LlamaContext,
        candidates: *mut c_int,
        n_candidates: c_int,
        k: c_int,
    );

    pub fn llama_sample_top_p(
        ctx: *mut LlamaContext,
        candidates: *mut c_int,
        n_candidates: c_int,
        p: c_float,
    );

    pub fn llama_sample_temperature(
        ctx: *mut LlamaContext,
        candidates: *mut c_int,
        n_candidates: c_int,
        temp: c_float,
    );
}
```

### 3.2 模型加载

```rust
// src/llama_cpp/model.rs
use anyhow::Result;
use std::ffi::CString;
use std::path::Path;
use tracing::{info, instrument};

/// llama.cpp模型包装
pub struct LlamaCppModel {
    model: *mut LlamaModel,
    context: *mut LlamaContext,
}

impl LlamaCppModel {
    /// 加载GGUF模型
    #[instrument]
    pub fn load(path: impl AsRef<Path>, n_gpu_layers: i32) -> Result<Self> {
        let path = path.as_ref();
        info!(path = %path.display(), n_gpu_layers = %n_gpu_layers, "Loading GGUF model");

        let path_cstr = CString::new(path.to_str().unwrap())?;

        let model_params = LlamaModelParams {
            n_gpu_layers,
            main_gpu: 0,
            use_mmap: true,
            use_mlock: false,
        };

        let model = unsafe { llama_load_model_from_file(path_cstr.as_ptr(), model_params) };

        if model.is_null() {
            anyhow::bail!("Failed to load model from {}", path.display());
        }

        let context_params = LlamaContextParams {
            n_ctx: 2048,      // 上下文窗口
            n_batch: 512,     // 批次大小
            n_threads: 8,     // CPU线程数
            rope_freq_base: 10000.0,
            rope_freq_scale: 1.0,
        };

        let context = unsafe { llama_new_context_with_model(model, context_params) };

        if context.is_null() {
            unsafe { llama_free_model(model) };
            anyhow::bail!("Failed to create context");
        }

        info!(path = %path.display(), "Model loaded successfully");

        Ok(Self { model, context })
    }
}

impl Drop for LlamaCppModel {
    fn drop(&mut self) {
        unsafe {
            if !self.context.is_null() {
                llama_free(self.context);
            }
            if !self.model.is_null() {
                llama_free_model(self.model);
            }
        }
    }
}

unsafe impl Send for LlamaCppModel {}
unsafe impl Sync for LlamaCppModel {}
```

### 3.3 推理引擎

```rust
// src/llama_cpp/inference.rs
use std::ffi::CString;
use tracing::{info, instrument};

impl LlamaCppModel {
    /// 生成文本
    #[instrument(skip(self, prompt))]
    pub fn generate(
        &mut self,
        prompt: &str,
        max_tokens: usize,
        temperature: f32,
    ) -> Result<String> {
        info!(prompt_len = %prompt.len(), max_tokens = %max_tokens, "Generating text");

        // Tokenize输入
        let prompt_cstr = CString::new(prompt)?;
        let mut tokens = vec![0i32; 1024];

        let n_prompt_tokens = unsafe {
            llama_tokenize(
                self.context,
                prompt_cstr.as_ptr(),
                tokens.as_mut_ptr(),
                tokens.len() as i32,
                true,
            )
        };

        if n_prompt_tokens < 0 {
            anyhow::bail!("Tokenization failed");
        }

        tokens.truncate(n_prompt_tokens as usize);

        // 评估prompt
        let result = unsafe {
            llama_eval(
                self.context,
                tokens.as_ptr(),
                tokens.len() as i32,
                0,
                8,
            )
        };

        if result != 0 {
            anyhow::bail!("Evaluation failed");
        }

        // 生成token
        let mut generated_text = String::new();
        let mut n_past = tokens.len() as i32;

        for _ in 0..max_tokens {
            // 采样下一个token
            let mut candidates = vec![0i32; 32000];
            
            // 应用温度采样
            unsafe {
                llama_sample_temperature(
                    self.context,
                    candidates.as_mut_ptr(),
                    candidates.len() as i32,
                    temperature,
                );
            }

            let next_token = candidates[0];

            // 评估新token
            let result = unsafe {
                llama_eval(
                    self.context,
                    &next_token,
                    1,
                    n_past,
                    8,
                )
            };

            if result != 0 {
                break;
            }

            // 解码token为文本 (简化示例)
            // 实际需要使用llama_token_to_piece
            generated_text.push_str(&format!("token_{} ", next_token));

            n_past += 1;

            // 检查EOS
            if next_token == 2 {  // 假设2是EOS token
                break;
            }
        }

        info!(generated_len = %generated_text.len(), "Text generated successfully");

        Ok(generated_text)
    }
}
```

### 3.4 量化支持

GGUF模型支持多种量化格式:

| 量化格式 | 大小 | 质量 | 速度 | 适用场景 |
|----------|------|------|------|----------|
| **Q4_0** | ~4 bits | 中等 | 快 | CPU推理 |
| **Q5_K_M** | ~5.5 bits | 良好 | 中 | 平衡 |
| **Q8_0** | ~8 bits | 优秀 | 慢 | 高质量 |
| **F16** | 16 bits | 最佳 | 最慢 | GPU推理 |

### 3.5 GPU加速

```rust
// 启用CUDA加速
let model = LlamaCppModel::load("model.gguf", 33)?;  // 33层卸载到GPU

// 启用Metal加速(Apple Silicon)
let model = LlamaCppModel::load("model.gguf", 1)?;   // Metal自动检测
```

---

## 4. 性能优化

### 4.1 KV Cache

```rust
// KV Cache管理
pub struct KVCache {
    cache: Vec<f32>,
    capacity: usize,
}

impl KVCache {
    pub fn new(capacity: usize) -> Self {
        Self {
            cache: Vec::with_capacity(capacity),
            capacity,
        }
    }

    pub fn update(&mut self, new_data: &[f32]) {
        if self.cache.len() + new_data.len() > self.capacity {
            let overflow = (self.cache.len() + new_data.len()) - self.capacity;
            self.cache.drain(0..overflow);
        }
        self.cache.extend_from_slice(new_data);
    }
}
```

### 4.2 Batching

```rust
// 批处理推理
pub async fn batch_inference(
    client: &OllamaClient,
    model: &str,
    prompts: Vec<String>,
) -> Result<Vec<String>> {
    let mut results = Vec::new();

    // 并发处理(限制并发数)
    let semaphore = Arc::new(tokio::sync::Semaphore::new(4));

    let tasks: Vec<_> = prompts
        .into_iter()
        .map(|prompt| {
            let client = client.clone();
            let model = model.to_string();
            let semaphore = semaphore.clone();

            tokio::spawn(async move {
                let _permit = semaphore.acquire().await?;
                client.generate_simple(&model, &prompt).await
            })
        })
        .collect();

    for task in tasks {
        results.push(task.await??);
    }

    Ok(results)
}
```

### 4.3 并发控制

```rust
use tokio::sync::Semaphore;
use std::sync::Arc;

pub struct ConcurrentInference {
    client: OllamaClient,
    semaphore: Arc<Semaphore>,
}

impl ConcurrentInference {
    pub fn new(client: OllamaClient, max_concurrent: usize) -> Self {
        Self {
            client,
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
        }
    }

    pub async fn generate(&self, model: &str, prompt: &str) -> Result<String> {
        let _permit = self.semaphore.acquire().await?;
        self.client.generate_simple(model, prompt).await
    }
}
```

---

## 5. OTLP可观测性

### 5.1 推理追踪

```rust
// src/observability/tracing.rs
use opentelemetry::trace::{Tracer, Span};
use tracing::{info, instrument};

#[instrument(
    skip(client, prompt),
    fields(
        otel.kind = "client",
        llm.model = %model,
        llm.type = "local",
        llm.prompt_tokens,
        llm.completion_tokens,
    )
)]
pub async fn generate_traced(
    client: &OllamaClient,
    model: &str,
    prompt: &str,
) -> Result<String> {
    let span = tracing::Span::current();

    let response = client.generate_simple(model, prompt).await?;

    // 记录token数(如果可用)
    span.record("llm.completion_tokens", response.len() / 4);  // 估算

    Ok(response)
}
```

### 5.2 性能指标

```rust
// 指标收集
llm_requests_total{model="llama3.1:8b",type="local"} 1234
llm_latency_seconds{model="llama3.1:8b",type="local"} 0.352
llm_tokens_per_second{model="llama3.1:8b"} 45.2
llm_model_load_duration_seconds{model="llama3.1:8b"} 2.1
llm_memory_usage_bytes{model="llama3.1:8b"} 5368709120
```

### 5.3 资源监控

```rust
// GPU监控(NVIDIA)
use nvml_wrapper::Nvml;

pub fn monitor_gpu_usage() -> Result<()> {
    let nvml = Nvml::init()?;
    let device = nvml.device_by_index(0)?;

    let utilization = device.utilization_rates()?;
    let memory_info = device.memory_info()?;

    info!(
        gpu_utilization = %utilization.gpu,
        memory_used_mb = %memory_info.used / 1024 / 1024,
        memory_total_mb = %memory_info.total / 1024 / 1024,
        "GPU status"
    );

    Ok(())
}
```

---

## 6. 生产部署

### 6.1 Docker部署

```dockerfile
# Dockerfile.ollama
FROM ollama/ollama:latest

# 预拉取模型
RUN ollama pull llama3.1:8b
RUN ollama pull mistral:7b

EXPOSE 11434

CMD ["ollama", "serve"]
```

```yaml
# docker-compose.yml
version: '3.8'

services:
  ollama:
    image: ollama/ollama:latest
    ports:
      - "11434:11434"
    volumes:
      - ollama_models:/root/.ollama
    deploy:
      resources:
        reservations:
          devices:
            - driver: nvidia
              count: 1
              capabilities: [gpu]

  app:
    build: .
    environment:
      - OLLAMA_BASE_URL=http://ollama:11434
      - OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4317
    depends_on:
      - ollama

volumes:
  ollama_models:
```

### 6.2 Kubernetes部署

```yaml
# k8s/ollama-deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: ollama
spec:
  replicas: 1
  selector:
    matchLabels:
      app: ollama
  template:
    metadata:
      labels:
        app: ollama
    spec:
      containers:
      - name: ollama
        image: ollama/ollama:latest
        ports:
        - containerPort: 11434
        resources:
          limits:
            nvidia.com/gpu: 1
            memory: 16Gi
          requests:
            nvidia.com/gpu: 1
            memory: 8Gi
        volumeMounts:
        - name: models
          mountPath: /root/.ollama
      volumes:
      - name: models
        persistentVolumeClaim:
          claimName: ollama-models-pvc
---
apiVersion: v1
kind: Service
metadata:
  name: ollama-svc
spec:
  selector:
    app: ollama
  ports:
  - port: 11434
    targetPort: 11434
```

---

## 7. 参考资源

### 官方文档

- **Ollama**: [https://ollama.ai/](https://ollama.ai/)
- **llama.cpp**: [https://github.com/ggerganov/llama.cpp](https://github.com/ggerganov/llama.cpp)
- **GGUF Format**: [https://github.com/ggerganov/ggml/blob/master/docs/gguf.md](https://github.com/ggerganov/ggml/blob/master/docs/gguf.md)

### Rust生态

- **reqwest**: [https://docs.rs/reqwest](https://docs.rs/reqwest)
- **tokio**: [https://docs.rs/tokio](https://docs.rs/tokio)
- **llama-cpp-rs**: [https://github.com/mdrokz/rust-llama.cpp](https://github.com/mdrokz/rust-llama.cpp)

### 模型资源

- **Hugging Face**: [https://huggingface.co/models](https://huggingface.co/models)
- **Ollama Models**: [https://ollama.ai/library](https://ollama.ai/library)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-13  
**Rust版本**: 1.90+  
**OpenTelemetry**: 0.27+  
**作者**: OTLP Rust 项目组
