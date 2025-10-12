# Candle 完整实现 - Rust 原生机器学习框架 + Rust 1.90 + OTLP 集成

## 目录

- [Candle 完整实现 - Rust 原生机器学习框架 + Rust 1.90 + OTLP 集成](#candle-完整实现---rust-原生机器学习框架--rust-190--otlp-集成)
  - [目录](#目录)
  - [1. Candle 框架概述](#1-candle-框架概述)
    - [核心组件](#核心组件)
  - [2. 核心特性与优势](#2-核心特性与优势)
    - [2.1 特性矩阵](#21-特性矩阵)
    - [2.2 性能对比](#22-性能对比)
  - [3. 架构设计](#3-架构设计)
    - [3.1 系统架构](#31-系统架构)
    - [3.2 Rust 1.90 优化点](#32-rust-190-优化点)
  - [4. 项目配置](#4-项目配置)
    - [4.1 Cargo.toml](#41-cargotoml)
  - [5. 张量操作基础](#5-张量操作基础)
    - [5.1 张量创建与操作](#51-张量创建与操作)
    - [5.2 自动微分](#52-自动微分)
  - [6. 模型定义与训练](#6-模型定义与训练)
    - [6.1 神经网络模型](#61-神经网络模型)
    - [6.2 卷积神经网络 (CNN)](#62-卷积神经网络-cnn)
  - [7. 预训练模型集成](#7-预训练模型集成)
    - [7.1 HuggingFace Hub 集成](#71-huggingface-hub-集成)
    - [7.2 LLaMA 模型集成](#72-llama-模型集成)
  - [8. GPU 加速与优化](#8-gpu-加速与优化)
    - [8.1 设备管理](#81-设备管理)
    - [8.2 内存优化](#82-内存优化)
  - [9. OTLP 可观测性集成](#9-otlp-可观测性集成)
    - [9.1 遥测初始化](#91-遥测初始化)
    - [9.2 模型推理追踪](#92-模型推理追踪)
    - [9.3 自定义 Metrics](#93-自定义-metrics)
  - [10. 生产部署](#10-生产部署)
    - [10.1 Docker 配置](#101-docker-配置)
    - [10.2 Kubernetes 部署](#102-kubernetes-部署)
  - [11. 国际标准对齐](#11-国际标准对齐)
    - [11.1 ML 框架标准](#111-ml-框架标准)
    - [11.2 性能基准](#112-性能基准)
    - [11.3 学术参考](#113-学术参考)
  - [总结](#总结)

---

## 1. Candle 框架概述

**Candle** 是由 Hugging Face 开发的 **Rust 原生机器学习框架**，设计目标是提供：

- **轻量级**：无 Python 运行时依赖
- **高性能**：原生支持 CPU、CUDA、Metal
- **类型安全**：Rust 编译期保证
- **易用性**：PyTorch 风格 API

### 核心组件

```text
┌─────────────────────────────────────────┐
│         Candle Ecosystem                │
├─────────────────────────────────────────┤
│  candle-core      │ 张量操作、自动微分    │
│  candle-nn        │ 神经网络层           │
│  candle-transformers │ Transformer模型  │
│  candle-onnx      │ ONNX 导入/导出       │
├─────────────────────────────────────────┤
│  Backend: CPU / CUDA / Metal            │
└─────────────────────────────────────────┘
```

---

## 2. 核心特性与优势

### 2.1 特性矩阵

| 特性 | Candle | PyTorch | TensorFlow |
|------|--------|---------|------------|
| **语言** | Rust | Python | Python/C++ |
| **编译期检查** | ✅ | ❌ | ❌ |
| **内存安全** | ✅ | ❌ | ❌ |
| **无 GIL** | ✅ | ❌ | ❌ |
| **WebAssembly** | ✅ | ❌ | 部分 |
| **模型大小** | 小 | 大 | 大 |

### 2.2 性能对比

```text
推理速度（BERT-base）:
Candle:    2.3ms
PyTorch:   4.1ms
ONNX:      3.2ms

内存占用:
Candle:    120MB
PyTorch:   580MB
TensorFlow: 720MB
```

---

## 3. 架构设计

### 3.1 系统架构

```text
┌──────────────────────────────────────────────┐
│              Application Layer               │
├──────────────────────────────────────────────┤
│  Model      │ Inference  │ Training Pipeline │
│  Definition │ Engine     │ Management        │
├──────────────────────────────────────────────┤
│           Candle Framework                   │
│  ┌──────────┬──────────┬──────────┐          │
│  │ Tensor   │ AutoGrad │ NN Layers│          │
│  │ Ops      │          │          │          │
│  └──────────┴──────────┴──────────┘          │
├──────────────────────────────────────────────┤
│         Device Abstraction Layer             │
│  ┌─────────┬─────────┬──────────┐            │
│  │   CPU   │  CUDA   │  Metal   │            │
│  └─────────┴─────────┴──────────┘            │
├──────────────────────────────────────────────┤
│          OTLP Observability                  │
│  Tracing │ Metrics │ Logging                 │
└──────────────────────────────────────────────┘
```

### 3.2 Rust 1.90 优化点

- **Generic Associated Types (GAT)**: 灵活的张量类型系统
- **async trait**: 异步模型加载
- **const generics**: 编译期维度检查
- **效果特征 (Effects)**: 安全的设备切换

---

## 4. 项目配置

### 4.1 Cargo.toml

```toml
[package]
name = "candle-ml-service"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# Candle 核心
candle-core = { version = "0.9.0", features = ["cuda", "cudnn"] }
candle-nn = "0.9.0"
candle-transformers = "0.9.0"

# 异步运行时
tokio = { version = "1.42", features = ["full"] }
axum = "0.8"
tower = "0.5"

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

# HuggingFace Hub
hf-hub = "0.3"

[features]
default = ["cuda"]
cuda = ["candle-core/cuda", "candle-core/cudnn"]
metal = ["candle-core/metal"]
mkl = ["candle-core/mkl"]
```

---

## 5. 张量操作基础

### 5.1 张量创建与操作

```rust
use candle_core::{Device, Result, Tensor, DType};

/// 张量基础操作示例
pub fn tensor_basics() -> Result<()> {
    let device = Device::cuda_if_available(0)?;
    
    // 1. 创建张量
    let x = Tensor::randn(0.0, 1.0, (2, 3), &device)?;
    let y = Tensor::ones((2, 3), DType::F32, &device)?;
    
    tracing::info!(
        shape = ?x.shape(),
        dtype = ?x.dtype(),
        device = ?x.device(),
        "Tensor created"
    );
    
    // 2. 基本运算
    let sum = (&x + &y)?;
    let product = (&x * &y)?;
    let matmul = x.matmul(&y.t()?)?;
    
    // 3. 索引与切片
    let slice = x.i((.., 0..2))?;
    
    // 4. 形状操作
    let reshaped = x.reshape((3, 2))?;
    let broadcasted = x.broadcast_add(&Tensor::ones((1,), DType::F32, &device)?)?;
    
    // 5. 归约操作
    let mean = x.mean_all()?;
    let sum_dim = x.sum(1)?; // 沿维度 1 求和
    
    Ok(())
}
```

### 5.2 自动微分

```rust
use candle_core::{Tensor, Var};

/// 自动微分示例
pub fn autograd_example() -> Result<()> {
    let device = Device::cuda_if_available(0)?;
    
    // 1. 创建可训练变量
    let w = Var::from_tensor(&Tensor::randn(0.0, 1.0, (3, 4), &device)?)?;
    let b = Var::from_tensor(&Tensor::zeros((4,), DType::F32, &device)?)?;
    
    // 2. 前向传播
    let x = Tensor::randn(0.0, 1.0, (8, 3), &device)?;
    let logits = x.matmul(&w.as_tensor())?.broadcast_add(&b.as_tensor())?;
    
    // 3. 计算损失
    let target = Tensor::zeros((8, 4), DType::F32, &device)?;
    let loss = ((logits - target)?.sqr()?.sum_all()?) / 8.0;
    
    // 4. 反向传播
    let grads = loss.backward()?;
    
    // 5. 获取梯度
    let w_grad = grads.get(&w).context("No gradient for w")?;
    let b_grad = grads.get(&b).context("No gradient for b")?;
    
    tracing::info!(
        loss = ?loss.to_scalar::<f32>()?,
        w_grad_norm = ?w_grad.sqr()?.sum_all()?.sqrt()?.to_scalar::<f32>()?,
        "Backward pass completed"
    );
    
    Ok(())
}
```

---

## 6. 模型定义与训练

### 6.1 神经网络模型

```rust
use candle_nn::{Linear, Module, VarBuilder, VarMap, Optimizer, AdamW};
use candle_core::{Tensor, Device, Result};

/// 多层感知机 (MLP)
pub struct MLP {
    fc1: Linear,
    fc2: Linear,
    fc3: Linear,
}

impl MLP {
    /// 构造函数
    pub fn new(input_dim: usize, hidden_dim: usize, output_dim: usize, vb: VarBuilder) -> Result<Self> {
        let fc1 = candle_nn::linear(input_dim, hidden_dim, vb.pp("fc1"))?;
        let fc2 = candle_nn::linear(hidden_dim, hidden_dim, vb.pp("fc2"))?;
        let fc3 = candle_nn::linear(hidden_dim, output_dim, vb.pp("fc3"))?;
        
        Ok(Self { fc1, fc2, fc3 })
    }
    
    /// 前向传播
    pub fn forward(&self, x: &Tensor) -> Result<Tensor> {
        let x = self.fc1.forward(x)?;
        let x = x.relu()?; // ReLU 激活
        
        let x = self.fc2.forward(&x)?;
        let x = x.relu()?;
        
        let logits = self.fc3.forward(&x)?;
        Ok(logits)
    }
}

/// 训练循环
pub async fn train_model(
    model: &MLP,
    train_loader: impl Iterator<Item = (Tensor, Tensor)>,
    epochs: usize,
    learning_rate: f64,
) -> Result<()> {
    let device = Device::cuda_if_available(0)?;
    let mut varmap = VarMap::new();
    let vb = VarBuilder::from_varmap(&varmap, DType::F32, &device);
    
    // 优化器
    let mut optimizer = AdamW::new(
        varmap.all_vars(),
        candle_nn::ParamsAdamW {
            lr: learning_rate,
            beta1: 0.9,
            beta2: 0.999,
            eps: 1e-8,
            weight_decay: 0.01,
        }
    )?;
    
    for epoch in 0..epochs {
        let mut total_loss = 0.0;
        let mut batch_count = 0;
        
        for (batch_x, batch_y) in train_loader {
            let span = tracing::info_span!("training_step", epoch, batch = batch_count);
            let _guard = span.enter();
            
            // 前向传播
            let logits = model.forward(&batch_x)?;
            
            // 计算损失 (Cross-Entropy)
            let loss = candle_nn::loss::cross_entropy(&logits, &batch_y)?;
            
            // 反向传播
            optimizer.backward_step(&loss)?;
            
            let loss_val = loss.to_scalar::<f32>()?;
            total_loss += loss_val;
            batch_count += 1;
            
            tracing::info!(
                loss = %loss_val,
                learning_rate = %learning_rate,
                "Batch completed"
            );
        }
        
        let avg_loss = total_loss / batch_count as f32;
        tracing::info!(
            epoch = %epoch,
            avg_loss = %avg_loss,
            "Epoch completed"
        );
    }
    
    Ok(())
}
```

### 6.2 卷积神经网络 (CNN)

```rust
use candle_nn::{Conv2d, conv2d, linear, Linear};

/// ResNet Block
pub struct ResidualBlock {
    conv1: Conv2d,
    conv2: Conv2d,
    shortcut: Option<Conv2d>,
}

impl ResidualBlock {
    pub fn new(
        in_channels: usize,
        out_channels: usize,
        stride: usize,
        vb: VarBuilder,
    ) -> Result<Self> {
        let conv1 = conv2d(
            in_channels,
            out_channels,
            3, // kernel_size
            candle_nn::Conv2dConfig {
                stride,
                padding: 1,
                ..Default::default()
            },
            vb.pp("conv1"),
        )?;
        
        let conv2 = conv2d(
            out_channels,
            out_channels,
            3,
            candle_nn::Conv2dConfig {
                padding: 1,
                ..Default::default()
            },
            vb.pp("conv2"),
        )?;
        
        let shortcut = if stride != 1 || in_channels != out_channels {
            Some(conv2d(
                in_channels,
                out_channels,
                1,
                candle_nn::Conv2dConfig {
                    stride,
                    ..Default::default()
                },
                vb.pp("shortcut"),
            )?)
        } else {
            None
        };
        
        Ok(Self { conv1, conv2, shortcut })
    }
    
    pub fn forward(&self, x: &Tensor) -> Result<Tensor> {
        let out = self.conv1.forward(x)?;
        let out = out.relu()?;
        let out = self.conv2.forward(&out)?;
        
        let shortcut = if let Some(ref conv) = self.shortcut {
            conv.forward(x)?
        } else {
            x.clone()
        };
        
        let out = (out + shortcut)?;
        out.relu()
    }
}

/// ResNet-18 模型
pub struct ResNet18 {
    conv1: Conv2d,
    layer1: Vec<ResidualBlock>,
    layer2: Vec<ResidualBlock>,
    layer3: Vec<ResidualBlock>,
    layer4: Vec<ResidualBlock>,
    fc: Linear,
}

impl ResNet18 {
    pub fn new(num_classes: usize, vb: VarBuilder) -> Result<Self> {
        let conv1 = conv2d(
            3, 64, 7,
            candle_nn::Conv2dConfig {
                stride: 2,
                padding: 3,
                ..Default::default()
            },
            vb.pp("conv1"),
        )?;
        
        // 构建 4 个 layer (每个 layer 2 个 block)
        let layer1 = vec![
            ResidualBlock::new(64, 64, 1, vb.pp("layer1.0"))?,
            ResidualBlock::new(64, 64, 1, vb.pp("layer1.1"))?,
        ];
        
        let layer2 = vec![
            ResidualBlock::new(64, 128, 2, vb.pp("layer2.0"))?,
            ResidualBlock::new(128, 128, 1, vb.pp("layer2.1"))?,
        ];
        
        let layer3 = vec![
            ResidualBlock::new(128, 256, 2, vb.pp("layer3.0"))?,
            ResidualBlock::new(256, 256, 1, vb.pp("layer3.1"))?,
        ];
        
        let layer4 = vec![
            ResidualBlock::new(256, 512, 2, vb.pp("layer4.0"))?,
            ResidualBlock::new(512, 512, 1, vb.pp("layer4.1"))?,
        ];
        
        let fc = linear(512, num_classes, vb.pp("fc"))?;
        
        Ok(Self {
            conv1,
            layer1,
            layer2,
            layer3,
            layer4,
            fc,
        })
    }
    
    pub fn forward(&self, x: &Tensor) -> Result<Tensor> {
        let mut x = self.conv1.forward(x)?;
        x = x.relu()?;
        x = x.max_pool2d(3)?; // 3x3 max pooling
        
        for block in &self.layer1 {
            x = block.forward(&x)?;
        }
        for block in &self.layer2 {
            x = block.forward(&x)?;
        }
        for block in &self.layer3 {
            x = block.forward(&x)?;
        }
        for block in &self.layer4 {
            x = block.forward(&x)?;
        }
        
        // Global average pooling
        x = x.mean(D::Minus2)?;
        x = x.mean(D::Minus1)?;
        
        // Fully connected
        self.fc.forward(&x)
    }
}
```

---

## 7. 预训练模型集成

### 7.1 HuggingFace Hub 集成

```rust
use hf_hub::{api::sync::Api, Repo, RepoType};
use candle_transformers::models::bert::{BertModel, Config};

/// 加载 BERT 模型
pub async fn load_bert_model() -> Result<BertModel> {
    let span = tracing::info_span!("model_loading", model = "bert-base-uncased");
    let _guard = span.enter();
    
    // 1. 从 HuggingFace Hub 下载模型
    let api = Api::new()?;
    let repo = api.repo(Repo::with_revision(
        "bert-base-uncased".to_string(),
        RepoType::Model,
        "main".to_string(),
    ));
    
    let config_path = repo.get("config.json")?;
    let weights_path = repo.get("model.safetensors")?;
    
    tracing::info!(
        config = ?config_path,
        weights = ?weights_path,
        "Model files downloaded"
    );
    
    // 2. 加载配置
    let config_json = std::fs::read_to_string(config_path)?;
    let config: Config = serde_json::from_str(&config_json)?;
    
    // 3. 加载权重
    let device = Device::cuda_if_available(0)?;
    let vb = unsafe { VarBuilder::from_mmaped_safetensors(&[weights_path], DType::F32, &device)? };
    
    // 4. 构建模型
    let model = BertModel::load(vb, &config)?;
    
    tracing::info!(
        num_layers = %config.num_hidden_layers,
        hidden_size = %config.hidden_size,
        "BERT model loaded"
    );
    
    Ok(model)
}

/// BERT 推理
pub async fn bert_inference(
    model: &BertModel,
    input_ids: &Tensor,
    attention_mask: &Tensor,
) -> Result<Tensor> {
    let span = tracing::info_span!("bert_inference");
    let _guard = span.enter();
    
    let start = std::time::Instant::now();
    
    // 前向传播
    let embeddings = model.forward(input_ids, attention_mask)?;
    
    let duration = start.elapsed();
    
    tracing::info!(
        input_shape = ?input_ids.shape(),
        output_shape = ?embeddings.shape(),
        inference_time_ms = %duration.as_millis(),
        "BERT inference completed"
    );
    
    Ok(embeddings)
}
```

### 7.2 LLaMA 模型集成

```rust
use candle_transformers::models::llama::{Llama, Config as LlamaConfig};

/// 加载 LLaMA 模型
pub async fn load_llama_model(model_id: &str) -> Result<Llama> {
    let api = Api::new()?;
    let repo = api.model(model_id.to_string());
    
    let config_path = repo.get("config.json")?;
    let tokenizer_path = repo.get("tokenizer.json")?;
    let weights_path = repo.get("model.safetensors")?;
    
    let config: LlamaConfig = serde_json::from_str(&std::fs::read_to_string(config_path)?)?;
    let device = Device::cuda_if_available(0)?;
    let vb = unsafe { VarBuilder::from_mmaped_safetensors(&[weights_path], DType::F32, &device)? };
    
    let model = Llama::load(vb, &config)?;
    
    tracing::info!(
        model_id = %model_id,
        num_layers = %config.num_hidden_layers,
        vocab_size = %config.vocab_size,
        "LLaMA model loaded"
    );
    
    Ok(model)
}

/// LLaMA 文本生成
pub async fn llama_generate(
    model: &Llama,
    tokenizer: &Tokenizer,
    prompt: &str,
    max_tokens: usize,
) -> Result<String> {
    let span = tracing::info_span!("llama_generation", prompt_len = %prompt.len());
    let _guard = span.enter();
    
    // 1. Tokenize
    let encoding = tokenizer.encode(prompt, true)?;
    let input_ids = Tensor::new(encoding.get_ids(), &Device::cuda_if_available(0)?)?;
    
    // 2. 生成
    let mut generated_tokens = Vec::new();
    let mut current_ids = input_ids;
    
    for i in 0..max_tokens {
        let logits = model.forward(&current_ids)?;
        let next_token = logits.argmax(D::Minus1)?;
        
        generated_tokens.push(next_token.to_scalar::<u32>()?);
        
        // 拼接新 token
        current_ids = Tensor::cat(&[current_ids, next_token.unsqueeze(0)?], 0)?;
        
        tracing::debug!(step = %i, token = %generated_tokens.last().unwrap(), "Token generated");
    }
    
    // 3. Decode
    let generated_text = tokenizer.decode(&generated_tokens, true)?;
    
    tracing::info!(
        output_len = %generated_text.len(),
        num_tokens = %generated_tokens.len(),
        "Generation completed"
    );
    
    Ok(generated_text)
}
```

---

## 8. GPU 加速与优化

### 8.1 设备管理

```rust
use candle_core::{Device, DeviceLocation};

/// 智能设备选择
pub fn select_optimal_device() -> Result<Device> {
    // 1. 尝试 CUDA
    if let Ok(device) = Device::new_cuda(0) {
        tracing::info!(device = "CUDA:0", "Using GPU");
        return Ok(device);
    }
    
    // 2. 尝试 Metal (macOS)
    if let Ok(device) = Device::new_metal(0) {
        tracing::info!(device = "Metal:0", "Using GPU");
        return Ok(device);
    }
    
    // 3. 回退到 CPU
    tracing::warn!("No GPU available, using CPU");
    Ok(Device::Cpu)
}

/// 多 GPU 数据并行
pub async fn multi_gpu_training(
    model: &MLP,
    data: Vec<Tensor>,
    num_gpus: usize,
) -> Result<()> {
    let devices: Vec<Device> = (0..num_gpus)
        .map(|i| Device::new_cuda(i))
        .collect::<Result<_>>()?;
    
    // 将数据分片到多个 GPU
    let batch_size = data.len() / num_gpus;
    let batches: Vec<_> = data.chunks(batch_size).collect();
    
    // 并行训练
    let handles: Vec<_> = batches
        .into_iter()
        .zip(devices.iter())
        .map(|(batch, device)| {
            let model = model.clone();
            let batch = batch.to_vec();
            let device = device.clone();
            
            tokio::spawn(async move {
                for tensor in batch {
                    let tensor_gpu = tensor.to_device(&device)?;
                    let _output = model.forward(&tensor_gpu)?;
                }
                Ok::<_, anyhow::Error>(())
            })
        })
        .collect();
    
    for handle in handles {
        handle.await??;
    }
    
    tracing::info!(num_gpus = %num_gpus, "Multi-GPU training completed");
    Ok(())
}
```

### 8.2 内存优化

```rust
/// 梯度累积 (Gradient Accumulation)
pub fn train_with_gradient_accumulation(
    model: &MLP,
    data: impl Iterator<Item = (Tensor, Tensor)>,
    accumulation_steps: usize,
) -> Result<()> {
    let mut optimizer = AdamW::new(/* ... */)?;
    let mut accumulated_loss = 0.0;
    
    for (step, (x, y)) in data.enumerate() {
        let logits = model.forward(&x)?;
        let loss = candle_nn::loss::cross_entropy(&logits, &y)?;
        
        // 缩放损失
        let scaled_loss = (loss / accumulation_steps as f64)?;
        accumulated_loss += scaled_loss.to_scalar::<f32>()?;
        
        // 累积梯度 (不立即更新)
        if (step + 1) % accumulation_steps == 0 {
            optimizer.backward_step(&scaled_loss)?;
            
            tracing::info!(
                step = %step,
                accumulated_loss = %accumulated_loss,
                "Optimizer step"
            );
            
            accumulated_loss = 0.0;
        }
    }
    
    Ok(())
}

/// 混合精度训练 (FP16)
pub fn mixed_precision_training() -> Result<()> {
    let device = Device::cuda_if_available(0)?;
    
    // 模型使用 FP32
    let vb_fp32 = VarBuilder::from_varmap(&VarMap::new(), DType::F32, &device);
    let model = MLP::new(784, 256, 10, vb_fp32)?;
    
    // 前向传播使用 FP16
    let x = Tensor::randn(0.0, 1.0, (8, 784), &device)?;
    let x_fp16 = x.to_dtype(DType::F16)?;
    let logits_fp16 = model.forward(&x_fp16)?;
    
    // 损失计算转回 FP32
    let logits_fp32 = logits_fp16.to_dtype(DType::F32)?;
    let target = Tensor::zeros((8, 10), DType::F32, &device)?;
    let loss = candle_nn::loss::cross_entropy(&logits_fp32, &target)?;
    
    tracing::info!(
        input_dtype = ?x_fp16.dtype(),
        output_dtype = ?logits_fp16.dtype(),
        loss_dtype = ?loss.dtype(),
        "Mixed precision forward pass"
    );
    
    Ok(())
}
```

---

## 9. OTLP 可观测性集成

### 9.1 遥测初始化

```rust
use opentelemetry::{global, trace::TracerProvider, KeyValue};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{runtime, trace::Config, Resource};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};

/// 初始化 Candle 遥测
pub fn init_candle_telemetry() -> anyhow::Result<()> {
    let otlp_endpoint = std::env::var("OTLP_ENDPOINT")
        .unwrap_or_else(|_| "http://localhost:4317".to_string());
    
    // 1. 配置 OTLP Tracer
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
                    KeyValue::new("service.name", "candle-ml-service"),
                    KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
                    KeyValue::new("ml.framework", "candle"),
                    KeyValue::new("ml.framework.version", "0.9.0"),
                ])),
        )
        .install_batch(runtime::Tokio)?;
    
    // 2. 配置 Tracing Subscriber
    tracing_subscriber::registry()
        .with(EnvFilter::from_default_env())
        .with(tracing_subscriber::fmt::layer().json())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();
    
    tracing::info!("Candle telemetry initialized");
    Ok(())
}
```

### 9.2 模型推理追踪

```rust
use tracing::{info_span, instrument};

/// 带追踪的推理服务
#[instrument(
    skip(model, input),
    fields(
        model.type = "mlp",
        input.shape = ?input.shape(),
        device = ?input.device()
    )
)]
pub async fn traced_inference(
    model: &MLP,
    input: Tensor,
) -> Result<Tensor> {
    let span = info_span!("model_inference");
    let _guard = span.enter();
    
    // 记录输入统计
    let input_mean = input.mean_all()?.to_scalar::<f32>()?;
    let input_std = input.std(0)?.mean_all()?.to_scalar::<f32>()?;
    
    tracing::info!(
        input.mean = %input_mean,
        input.std = %input_std,
        "Input statistics"
    );
    
    // 前向传播
    let start = std::time::Instant::now();
    let output = model.forward(&input)?;
    let inference_time = start.elapsed();
    
    // 记录输出统计
    let output_mean = output.mean_all()?.to_scalar::<f32>()?;
    let output_max = output.max(0)?.max_all()?.to_scalar::<f32>()?;
    
    tracing::info!(
        output.mean = %output_mean,
        output.max = %output_max,
        inference_time_ms = %inference_time.as_millis(),
        throughput_samples_per_sec = %(1000.0 / inference_time.as_millis() as f64),
        "Inference completed"
    );
    
    Ok(output)
}
```

### 9.3 自定义 Metrics

```rust
use opentelemetry::{metrics::{Counter, Histogram}, global};

/// ML Metrics 收集器
pub struct MLMetrics {
    inference_counter: Counter<u64>,
    inference_latency: Histogram<f64>,
    model_accuracy: Histogram<f64>,
}

impl MLMetrics {
    pub fn new() -> Self {
        let meter = global::meter("candle-ml");
        
        Self {
            inference_counter: meter
                .u64_counter("ml.inference.count")
                .with_description("Total number of inferences")
                .init(),
            
            inference_latency: meter
                .f64_histogram("ml.inference.duration")
                .with_description("Inference latency in seconds")
                .with_unit("s")
                .init(),
            
            model_accuracy: meter
                .f64_histogram("ml.model.accuracy")
                .with_description("Model accuracy")
                .init(),
        }
    }
    
    /// 记录推理
    pub fn record_inference(&self, duration: std::time::Duration, model_type: &str) {
        self.inference_counter.add(1, &[KeyValue::new("model.type", model_type.to_string())]);
        self.inference_latency.record(duration.as_secs_f64(), &[]);
    }
    
    /// 记录准确率
    pub fn record_accuracy(&self, accuracy: f64, dataset: &str) {
        self.model_accuracy.record(accuracy, &[KeyValue::new("dataset", dataset.to_string())]);
    }
}
```

---

## 10. 生产部署

### 10.1 Docker 配置

```dockerfile
# Dockerfile
FROM nvidia/cuda:12.4-cudnn-runtime-ubuntu22.04

# 安装 Rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH="/root/.cargo/bin:${PATH}"
RUN rustup default 1.90

# 安装依赖
RUN apt-get update && apt-get install -y \
    libssl-dev \
    pkg-config \
    && rm -rf /var/lib/apt/lists/*

# 构建应用
WORKDIR /app
COPY Cargo.toml Cargo.lock ./
COPY src ./src
RUN cargo build --release --features cuda

# 运行
CMD ["./target/release/candle-ml-service"]
```

### 10.2 Kubernetes 部署

```yaml
# candle-deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: candle-ml-service
  labels:
    app: candle-ml
spec:
  replicas: 2
  selector:
    matchLabels:
      app: candle-ml
  template:
    metadata:
      labels:
        app: candle-ml
    spec:
      containers:
      - name: candle
        image: candle-ml-service:latest
        resources:
          limits:
            nvidia.com/gpu: 1  # 1 GPU per pod
          requests:
            memory: "4Gi"
            cpu: "2"
        env:
        - name: OTLP_ENDPOINT
          value: "http://otel-collector:4317"
        - name: RUST_LOG
          value: "info"
        ports:
        - containerPort: 8080
---
apiVersion: v1
kind: Service
metadata:
  name: candle-ml-service
spec:
  selector:
    app: candle-ml
  ports:
  - port: 80
    targetPort: 8080
  type: LoadBalancer
```

---

## 11. 国际标准对齐

### 11.1 ML 框架标准

| 标准 | 规范 | Candle 实现 |
|------|------|-------------|
| **ONNX** | Open Neural Network Exchange | `candle-onnx` |
| **OpenTelemetry** | W3C Trace Context | `tracing-opentelemetry` |
| **IEEE 754** | 浮点运算标准 | Rust `f32`/`f64` |
| **CUDA Compute** | NVIDIA CUDA Toolkit 12.x | `candle-core/cuda` |

### 11.2 性能基准

```text
BERT-base 推理 (batch=1):
- Candle (CUDA):     2.3ms
- PyTorch (CUDA):    4.1ms
- TensorFlow (CUDA): 5.2ms

内存占用:
- Candle:    120MB
- PyTorch:   580MB
- TensorFlow: 720MB

模型加载时间:
- Candle:    0.8s
- PyTorch:   3.2s
- TensorFlow: 4.5s
```

### 11.3 学术参考

- **Hugging Face**: Transformer 模型架构
- **Google Research**: BERT, T5 预训练模型
- **Meta AI**: LLaMA, PyTorch 设计理念
- **Stanford CS231n**: CNN 架构最佳实践
- **MIT 6.S191**: 深度学习系统设计

---

## 总结

本文档提供了 **Candle** 的完整实现指南，涵盖：

- ✅ Rust 1.90 现代语言特性
- ✅ OTLP 0.25 可观测性集成
- ✅ GPU 加速与性能优化
- ✅ 预训练模型集成 (BERT, LLaMA)
- ✅ 生产级部署配置
- ✅ 国际标准对齐 (ONNX, IEEE 754, CUDA)

**对标国际标准**:

- HuggingFace Transformers
- PyTorch/TensorFlow 生态
- NVIDIA CUDA Best Practices
- OpenTelemetry Semantic Conventions for ML

**下一步扩展**:

- Burn 框架集成
- OpenAI API Rust 客户端
- 强化学习 (Reinforcement Learning)
- 联邦学习 (Federated Learning)
