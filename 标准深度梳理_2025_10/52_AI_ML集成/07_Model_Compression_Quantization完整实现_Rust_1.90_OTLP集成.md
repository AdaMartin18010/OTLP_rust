# Model Compression & Quantization 完整实现 - Rust 1.90 + OTLP 集成

## 目录

- [Model Compression \& Quantization 完整实现 - Rust 1.90 + OTLP 集成](#model-compression--quantization-完整实现---rust-190--otlp-集成)
  - [目录](#目录)
  - [1. 核心概念与理论](#1-核心概念与理论)
    - [1.1 模型压缩分类](#11-模型压缩分类)
    - [1.2 量化原理](#12-量化原理)
    - [1.3 国际标准对齐](#13-国际标准对齐)
  - [2. 量化技术](#2-量化技术)
    - [2.1 Post-Training Quantization (PTQ)](#21-post-training-quantization-ptq)
    - [2.2 Quantization-Aware Training (QAT)](#22-quantization-aware-training-qat)
    - [2.3 GGUF量化](#23-gguf量化)
    - [2.4 GPTQ量化](#24-gptq量化)
  - [3. 模型剪枝](#3-模型剪枝)
    - [3.1 结构化剪枝](#31-结构化剪枝)
    - [3.2 非结构化剪枝](#32-非结构化剪枝)
    - [3.3 动态剪枝](#33-动态剪枝)
  - [4. 知识蒸馏](#4-知识蒸馏)
    - [4.1 Teacher-Student架构](#41-teacher-student架构)
    - [4.2 Self-Distillation](#42-self-distillation)
    - [4.3 Progressive Distillation](#43-progressive-distillation)
  - [5. 低秩分解](#5-低秩分解)
    - [5.1 LoRA (Low-Rank Adaptation)](#51-lora-low-rank-adaptation)
    - [5.2 SVD分解](#52-svd分解)
  - [6. OTLP可观测性](#6-otlp可观测性)
    - [6.1 压缩追踪](#61-压缩追踪)
    - [6.2 性能指标](#62-性能指标)
  - [7. 生产实践](#7-生产实践)
    - [7.1 压缩流程](#71-压缩流程)
    - [7.2 质量评估](#72-质量评估)
  - [8. 参考资源](#8-参考资源)
    - [学术论文](#学术论文)
    - [Rust生态](#rust生态)
    - [工具与框架](#工具与框架)

---

## 1. 核心概念与理论

### 1.1 模型压缩分类

| 技术类别 | 原理 | 压缩比 | 精度损失 | 适用场景 |
|----------|------|--------|----------|----------|
| **量化(Quantization)** | 降低数值精度 | 2-8x | 低-中 | 推理优化 |
| **剪枝(Pruning)** | 移除冗余参数 | 2-10x | 低-中 | 模型瘦身 |
| **知识蒸馏(Distillation)** | 小模型学习大模型 | 3-100x | 中-高 | 部署优化 |
| **低秩分解(Decomposition)** | 矩阵分解 | 1.5-3x | 低 | 微调优化 |
| **神经架构搜索(NAS)** | 自动设计高效架构 | 2-5x | 低 | 架构优化 |

**压缩效果对比**:

```text
原始模型: LLaMA-7B (13.5 GB, FP16)
    │
    ├─ 量化 Q8_0    → 7.2 GB  (53% ↓, 精度损失 <1%)
    ├─ 量化 Q5_K_M  → 4.8 GB  (64% ↓, 精度损失 ~2%)
    ├─ 量化 Q4_0    → 3.8 GB  (72% ↓, 精度损失 ~5%)
    ├─ 剪枝 50%     → 6.8 GB  (50% ↓, 精度损失 ~3%)
    └─ 蒸馏 → LLaMA-1B → 2.7 GB (80% ↓, 精度损失 ~15%)
```

### 1.2 量化原理

**数值精度对比**:

| 类型 | 位数 | 范围 | 精度 | 内存占用(单值) |
|------|------|------|------|----------------|
| **FP32** | 32 bit | ±3.4×10³⁸ | ~7位有效数字 | 4 bytes |
| **FP16** | 16 bit | ±6.5×10⁴ | ~3位有效数字 | 2 bytes |
| **INT8** | 8 bit | -128~127 | 整数 | 1 byte |
| **INT4** | 4 bit | -8~7 | 整数 | 0.5 byte |

**量化映射公式**:

```text
量化: Q(x) = round((x - zero_point) / scale)
反量化: x' = Q(x) × scale + zero_point

其中:
- scale = (x_max - x_min) / (q_max - q_min)
- zero_point = q_min - x_min / scale
```

### 1.3 国际标准对齐

| 标准/框架 | 应用场景 | Rust实现 |
|-----------|----------|----------|
| **ONNX** | 模型交换 | onnxruntime-rs |
| **GGUF** | LLM量化 | llama.cpp |
| **GPTQ** | GPU量化 | Rust实现 |
| **IEEE 754** | 浮点标准 | Rust原生支持 |
| **OpenTelemetry** | 可观测性 | opentelemetry 0.27 |

---

## 2. 量化技术

### 2.1 Post-Training Quantization (PTQ)

训练后量化,无需重新训练:

```rust
// src/quantization/ptq.rs
use anyhow::Result;
use ndarray::{Array1, Array2};
use tracing::{info, instrument};

/// 后训练量化器
pub struct PTQuantizer {
    bits: u8,
    symmetric: bool,
}

impl PTQuantizer {
    pub fn new(bits: u8, symmetric: bool) -> Self {
        Self { bits, symmetric }
    }

    /// 量化单个张量
    #[instrument(skip(self, tensor))]
    pub fn quantize_tensor(&self, tensor: &Array1<f32>) -> Result<QuantizedTensor> {
        info!(bits = %self.bits, shape = ?tensor.shape(), "Quantizing tensor");

        let (scale, zero_point) = self.compute_params(tensor)?;

        let q_max = (1 << self.bits) - 1;
        let q_min = if self.symmetric { -(1 << (self.bits - 1)) } else { 0 };

        let quantized: Vec<i8> = tensor
            .iter()
            .map(|&x| {
                let q = ((x - zero_point) / scale).round();
                q.clamp(q_min as f32, q_max as f32) as i8
            })
            .collect();

        info!(
            original_size = %tensor.len() * 4,
            quantized_size = %quantized.len(),
            compression_ratio = %((tensor.len() * 4) as f32 / quantized.len() as f32),
            "Tensor quantized"
        );

        Ok(QuantizedTensor {
            data: quantized,
            scale,
            zero_point,
            bits: self.bits,
            shape: tensor.shape().to_vec(),
        })
    }

    /// 计算量化参数
    fn compute_params(&self, tensor: &Array1<f32>) -> Result<(f32, f32)> {
        let x_min = tensor.iter().cloned().fold(f32::INFINITY, f32::min);
        let x_max = tensor.iter().cloned().fold(f32::NEG_INFINITY, f32::max);

        let q_max = (1 << self.bits) - 1;
        let q_min = if self.symmetric { -(1 << (self.bits - 1)) } else { 0 };

        let scale = (x_max - x_min) / (q_max - q_min) as f32;
        let zero_point = if self.symmetric {
            0.0
        } else {
            q_min as f32 - x_min / scale
        };

        Ok((scale, zero_point))
    }
}

/// 量化后的张量
#[derive(Debug, Clone)]
pub struct QuantizedTensor {
    pub data: Vec<i8>,
    pub scale: f32,
    pub zero_point: f32,
    pub bits: u8,
    pub shape: Vec<usize>,
}

impl QuantizedTensor {
    /// 反量化
    #[instrument(skip(self))]
    pub fn dequantize(&self) -> Array1<f32> {
        info!(size = %self.data.len(), "Dequantizing tensor");

        let dequantized: Vec<f32> = self
            .data
            .iter()
            .map(|&q| q as f32 * self.scale + self.zero_point)
            .collect();

        Array1::from(dequantized)
    }

    /// 计算量化误差
    pub fn compute_error(&self, original: &Array1<f32>) -> f32 {
        let dequantized = self.dequantize();
        let diff = original - &dequantized;
        let mse = diff.mapv(|x| x * x).mean().unwrap();
        mse.sqrt() // RMSE
    }
}
```

### 2.2 Quantization-Aware Training (QAT)

训练时感知量化:

```rust
// src/quantization/qat.rs
use ndarray::Array1;
use tracing::{info, instrument};

/// 量化感知训练
pub struct QATTrainer {
    bits: u8,
    quantizer: PTQuantizer,
}

impl QATTrainer {
    pub fn new(bits: u8) -> Self {
        Self {
            bits,
            quantizer: PTQuantizer::new(bits, false),
        }
    }

    /// 前向传播(带量化)
    #[instrument(skip(self, input))]
    pub fn forward_quantized(&self, input: &Array1<f32>) -> Result<Array1<f32>> {
        info!("Forward pass with quantization");

        // 量化
        let quantized = self.quantizer.quantize_tensor(input)?;

        // 立即反量化(用于梯度计算)
        let dequantized = quantized.dequantize();

        Ok(dequantized)
    }

    /// Straight-Through Estimator (STE)
    /// 前向量化,反向直通
    pub fn ste_gradient(&self, grad: &Array1<f32>) -> Array1<f32> {
        // 梯度直接传递,不经过量化
        grad.clone()
    }
}
```

### 2.3 GGUF量化

llama.cpp的GGUF格式量化:

```rust
// src/quantization/gguf.rs
use std::fs::File;
use std::io::{Read, Write};
use tracing::{info, instrument};

/// GGUF量化类型
#[derive(Debug, Clone, Copy)]
pub enum GGUFQuantType {
    Q4_0,   // 4-bit, 32个元素一组
    Q4_1,   // 4-bit, 32个元素一组 + min
    Q5_0,   // 5-bit, 32个元素一组
    Q5_1,   // 5-bit, 32个元素一组 + min
    Q8_0,   // 8-bit, 32个元素一组
    Q8_1,   // 8-bit, 32个元素一组 + min
    Q5_K_M, // 5-bit K-quant, 中等质量
    Q6_K,   // 6-bit K-quant, 高质量
}

impl GGUFQuantType {
    pub fn block_size(&self) -> usize {
        match self {
            Self::Q4_0 | Self::Q4_1 | Self::Q5_0 | Self::Q5_1 | Self::Q8_0 | Self::Q8_1 => 32,
            Self::Q5_K_M | Self::Q6_K => 256,
        }
    }

    pub fn bits_per_weight(&self) -> f32 {
        match self {
            Self::Q4_0 => 4.5,  // 4 bits + scale
            Self::Q4_1 => 5.0,  // 4 bits + scale + min
            Self::Q5_0 => 5.5,
            Self::Q5_1 => 6.0,
            Self::Q8_0 => 8.5,
            Self::Q8_1 => 9.0,
            Self::Q5_K_M => 5.5,
            Self::Q6_K => 6.5,
        }
    }
}

/// GGUF量化器
pub struct GGUFQuantizer {
    quant_type: GGUFQuantType,
}

impl GGUFQuantizer {
    pub fn new(quant_type: GGUFQuantType) -> Self {
        Self { quant_type }
    }

    /// 量化权重矩阵
    #[instrument(skip(self, weights))]
    pub fn quantize_weights(&self, weights: &[f32]) -> Result<Vec<u8>> {
        info!(
            quant_type = ?self.quant_type,
            weight_count = %weights.len(),
            "Quantizing weights to GGUF format"
        );

        let block_size = self.quant_type.block_size();
        let num_blocks = (weights.len() + block_size - 1) / block_size;

        let mut quantized = Vec::new();

        for i in 0..num_blocks {
            let start = i * block_size;
            let end = (start + block_size).min(weights.len());
            let block = &weights[start..end];

            let quantized_block = self.quantize_block(block)?;
            quantized.extend_from_slice(&quantized_block);
        }

        info!(
            original_size = %weights.len() * 4,
            quantized_size = %quantized.len(),
            compression_ratio = %((weights.len() * 4) as f32 / quantized.len() as f32),
            "Weights quantized"
        );

        Ok(quantized)
    }

    /// 量化单个块
    fn quantize_block(&self, block: &[f32]) -> Result<Vec<u8>> {
        match self.quant_type {
            GGUFQuantType::Q4_0 => self.quantize_q4_0(block),
            GGUFQuantType::Q8_0 => self.quantize_q8_0(block),
            _ => anyhow::bail!("Quantization type not implemented"),
        }
    }

    /// Q4_0量化: 4 bits + FP16 scale
    fn quantize_q4_0(&self, block: &[f32]) -> Result<Vec<u8>> {
        let max_abs = block.iter().map(|x| x.abs()).fold(0.0f32, f32::max);
        let scale = max_abs / 7.0; // 4-bit: -7 to 7

        let mut result = Vec::new();

        // 写入scale (FP16)
        result.extend_from_slice(&(scale as f16).to_le_bytes());

        // 写入量化权重 (4 bits each, packed)
        for chunk in block.chunks(2) {
            let q1 = ((chunk[0] / scale).round().clamp(-7.0, 7.0) as i8 + 7) as u8;
            let q2 = if chunk.len() > 1 {
                ((chunk[1] / scale).round().clamp(-7.0, 7.0) as i8 + 7) as u8
            } else {
                0
            };

            result.push((q1 << 4) | q2);
        }

        Ok(result)
    }

    /// Q8_0量化: 8 bits + FP16 scale
    fn quantize_q8_0(&self, block: &[f32]) -> Result<Vec<u8>> {
        let max_abs = block.iter().map(|x| x.abs()).fold(0.0f32, f32::max);
        let scale = max_abs / 127.0;

        let mut result = Vec::new();

        // 写入scale (FP16)
        result.extend_from_slice(&(scale as f16).to_le_bytes());

        // 写入量化权重 (8 bits each)
        for &weight in block {
            let q = (weight / scale).round().clamp(-127.0, 127.0) as i8;
            result.push(q as u8);
        }

        Ok(result)
    }
}
```

### 2.4 GPTQ量化

GPU友好的量化算法:

```rust
// src/quantization/gptq.rs
use ndarray::{Array1, Array2};
use tracing::{info, instrument};

/// GPTQ量化器
pub struct GPTQQuantizer {
    bits: u8,
    group_size: usize,
}

impl GPTQQuantizer {
    pub fn new(bits: u8, group_size: usize) -> Self {
        Self { bits, group_size }
    }

    /// GPTQ量化 (基于Hessian矩阵)
    #[instrument(skip(self, weights, hessian))]
    pub fn quantize_gptq(
        &self,
        weights: &Array2<f32>,
        hessian: &Array2<f32>,
    ) -> Result<Array2<i8>> {
        info!(
            shape = ?weights.shape(),
            bits = %self.bits,
            group_size = %self.group_size,
            "Quantizing with GPTQ"
        );

        let (rows, cols) = weights.dim();
        let mut quantized = Array2::zeros((rows, cols));

        // 逐组量化
        for col_start in (0..cols).step_by(self.group_size) {
            let col_end = (col_start + self.group_size).min(cols);

            for row in 0..rows {
                for col in col_start..col_end {
                    let weight = weights[[row, col]];

                    // 量化
                    let q_max = (1 << (self.bits - 1)) - 1;
                    let q = weight.round().clamp(-q_max as f32, q_max as f32) as i8;
                    quantized[[row, col]] = q;

                    // 误差补偿 (利用Hessian)
                    let error = weight - q as f32;
                    // 将误差传播到后续权重 (简化实现)
                }
            }
        }

        info!("GPTQ quantization completed");

        Ok(quantized)
    }
}
```

---

## 3. 模型剪枝

### 3.1 结构化剪枝

移除整个神经元/通道:

```rust
// src/pruning/structured.rs
use ndarray::Array2;
use tracing::{info, instrument};

/// 结构化剪枝器
pub struct StructuredPruner {
    sparsity: f32, // 稀疏度 (0.0 - 1.0)
}

impl StructuredPruner {
    pub fn new(sparsity: f32) -> Self {
        Self { sparsity }
    }

    /// L1范数剪枝
    #[instrument(skip(self, weights))]
    pub fn prune_l1(&self, weights: &mut Array2<f32>) -> Result<PruneMask> {
        info!(
            sparsity = %self.sparsity,
            shape = ?weights.shape(),
            "Pruning with L1 norm"
        );

        let (rows, cols) = weights.dim();

        // 计算每行的L1范数
        let mut l1_norms: Vec<(usize, f32)> = (0..rows)
            .map(|i| {
                let row = weights.row(i);
                let l1 = row.iter().map(|x| x.abs()).sum::<f32>();
                (i, l1)
            })
            .collect();

        // 按L1范数排序
        l1_norms.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap());

        // 剪枝最小的 sparsity% 行
        let prune_count = (rows as f32 * self.sparsity) as usize;
        let mut mask = vec![true; rows];

        for i in 0..prune_count {
            let row_idx = l1_norms[i].0;
            mask[row_idx] = false;

            // 将该行权重设为0
            for col in 0..cols {
                weights[[row_idx, col]] = 0.0;
            }
        }

        info!(pruned_rows = %prune_count, "Pruning completed");

        Ok(PruneMask { mask })
    }

    /// 通道剪枝 (卷积层)
    #[instrument(skip(self, weights))]
    pub fn prune_channels(&self, weights: &mut Array2<f32>) -> Result<Vec<usize>> {
        info!("Pruning channels");

        // 计算每个通道的重要性
        let (channels, _) = weights.dim();
        let mut importance: Vec<(usize, f32)> = (0..channels)
            .map(|i| {
                let channel = weights.row(i);
                let l2 = channel.iter().map(|x| x * x).sum::<f32>().sqrt();
                (i, l2)
            })
            .collect();

        importance.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());

        let keep_count = (channels as f32 * (1.0 - self.sparsity)) as usize;
        let kept_channels: Vec<usize> = importance
            .iter()
            .take(keep_count)
            .map(|(idx, _)| *idx)
            .collect();

        info!(
            original_channels = %channels,
            kept_channels = %kept_channels.len(),
            "Channel pruning completed"
        );

        Ok(kept_channels)
    }
}

#[derive(Debug, Clone)]
pub struct PruneMask {
    pub mask: Vec<bool>,
}
```

### 3.2 非结构化剪枝

移除单个权重:

```rust
// src/pruning/unstructured.rs
use ndarray::Array2;
use tracing::{info, instrument};

/// 非结构化剪枝器
pub struct UnstructuredPruner {
    sparsity: f32,
}

impl UnstructuredPruner {
    pub fn new(sparsity: f32) -> Self {
        Self { sparsity }
    }

    /// 幅度剪枝 (Magnitude Pruning)
    #[instrument(skip(self, weights))]
    pub fn prune_magnitude(&self, weights: &mut Array2<f32>) -> Result<usize> {
        info!(sparsity = %self.sparsity, "Pruning by magnitude");

        let total = weights.len();
        let prune_count = (total as f32 * self.sparsity) as usize;

        // 收集所有权重的绝对值
        let mut abs_weights: Vec<(usize, f32)> = weights
            .iter()
            .enumerate()
            .map(|(i, &w)| (i, w.abs()))
            .collect();

        // 按幅度排序
        abs_weights.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap());

        // 剪枝最小的权重
        for i in 0..prune_count {
            let idx = abs_weights[i].0;
            let (row, col) = (idx / weights.ncols(), idx % weights.ncols());
            weights[[row, col]] = 0.0;
        }

        info!(
            total_weights = %total,
            pruned = %prune_count,
            actual_sparsity = %(prune_count as f32 / total as f32),
            "Magnitude pruning completed"
        );

        Ok(prune_count)
    }

    /// 计算稀疏度
    pub fn compute_sparsity(weights: &Array2<f32>) -> f32 {
        let zero_count = weights.iter().filter(|&&w| w.abs() < 1e-8).count();
        zero_count as f32 / weights.len() as f32
    }
}
```

### 3.3 动态剪枝

运行时自适应剪枝:

```rust
// src/pruning/dynamic.rs
use ndarray::Array2;
use std::collections::HashMap;
use tracing::{info, instrument};

/// 动态剪枝器
pub struct DynamicPruner {
    threshold: f32,
    pruning_rate: f32,
    layer_stats: HashMap<String, LayerStats>,
}

#[derive(Debug, Clone)]
struct LayerStats {
    activations: Vec<f32>,
    importance: f32,
}

impl DynamicPruner {
    pub fn new(threshold: f32, pruning_rate: f32) -> Self {
        Self {
            threshold,
            pruning_rate,
            layer_stats: HashMap::new(),
        }
    }

    /// 基于激活值的动态剪枝
    #[instrument(skip(self, weights, activations))]
    pub fn prune_dynamic(
        &mut self,
        layer_name: &str,
        weights: &mut Array2<f32>,
        activations: &Array2<f32>,
    ) -> Result<usize> {
        info!(layer = %layer_name, "Dynamic pruning");

        // 计算激活重要性
        let importance = activations.iter().map(|x| x.abs()).sum::<f32>() / activations.len() as f32;

        // 更新统计
        self.layer_stats.insert(
            layer_name.to_string(),
            LayerStats {
                activations: activations.iter().cloned().collect(),
                importance,
            },
        );

        // 自适应调整剪枝率
        let adaptive_rate = if importance < self.threshold {
            self.pruning_rate * 1.5 // 不重要的层剪枝更多
        } else {
            self.pruning_rate * 0.5 // 重要的层保留更多
        };

        let prune_count = (weights.len() as f32 * adaptive_rate) as usize;

        info!(
            importance = %importance,
            adaptive_rate = %adaptive_rate,
            prune_count = %prune_count,
            "Adaptive pruning applied"
        );

        Ok(prune_count)
    }
}
```

---

## 4. 知识蒸馏

### 4.1 Teacher-Student架构

```rust
// src/distillation/teacher_student.rs
use ndarray::Array1;
use tracing::{info, instrument};

/// 知识蒸馏器
pub struct KnowledgeDistiller {
    temperature: f32,
    alpha: f32, // hard loss权重
    beta: f32,  // soft loss权重
}

impl KnowledgeDistiller {
    pub fn new(temperature: f32, alpha: f32, beta: f32) -> Self {
        Self {
            temperature,
            alpha,
            beta,
        }
    }

    /// 计算蒸馏损失
    #[instrument(skip(self, teacher_logits, student_logits, true_labels))]
    pub fn distillation_loss(
        &self,
        teacher_logits: &Array1<f32>,
        student_logits: &Array1<f32>,
        true_labels: &Array1<f32>,
    ) -> Result<f32> {
        info!(temperature = %self.temperature, "Computing distillation loss");

        // Soft loss (KL散度)
        let teacher_probs = self.softmax_with_temperature(teacher_logits);
        let student_probs = self.softmax_with_temperature(student_logits);

        let kl_div = self.kl_divergence(&teacher_probs, &student_probs);
        let soft_loss = kl_div * self.temperature * self.temperature;

        // Hard loss (交叉熵)
        let student_probs_normal = self.softmax(student_logits);
        let hard_loss = self.cross_entropy(&student_probs_normal, true_labels);

        // 组合损失
        let total_loss = self.alpha * hard_loss + self.beta * soft_loss;

        info!(
            hard_loss = %hard_loss,
            soft_loss = %soft_loss,
            total_loss = %total_loss,
            "Distillation loss computed"
        );

        Ok(total_loss)
    }

    /// Softmax with temperature
    fn softmax_with_temperature(&self, logits: &Array1<f32>) -> Array1<f32> {
        let scaled = logits.mapv(|x| x / self.temperature);
        self.softmax(&scaled)
    }

    fn softmax(&self, x: &Array1<f32>) -> Array1<f32> {
        let max = x.iter().cloned().fold(f32::NEG_INFINITY, f32::max);
        let exp: Array1<f32> = x.mapv(|v| (v - max).exp());
        let sum = exp.sum();
        exp / sum
    }

    fn kl_divergence(&self, p: &Array1<f32>, q: &Array1<f32>) -> f32 {
        p.iter()
            .zip(q.iter())
            .map(|(&pi, &qi)| {
                if pi > 1e-8 {
                    pi * (pi / qi.max(1e-8)).ln()
                } else {
                    0.0
                }
            })
            .sum()
    }

    fn cross_entropy(&self, pred: &Array1<f32>, target: &Array1<f32>) -> f32 {
        -pred
            .iter()
            .zip(target.iter())
            .map(|(&p, &t)| t * p.max(1e-8).ln())
            .sum::<f32>()
    }
}
```

### 4.2 Self-Distillation

```rust
// src/distillation/self_distillation.rs
use ndarray::Array1;
use tracing::{info, instrument};

/// 自蒸馏
pub struct SelfDistiller {
    ensemble_size: usize,
    temperature: f32,
}

impl SelfDistiller {
    pub fn new(ensemble_size: usize, temperature: f32) -> Self {
        Self {
            ensemble_size,
            temperature,
        }
    }

    /// 集成多个epoch的输出进行自蒸馏
    #[instrument(skip(self, outputs_history))]
    pub fn self_distill(&self, outputs_history: &[Array1<f32>]) -> Result<Array1<f32>> {
        info!(
            ensemble_size = %self.ensemble_size,
            history_len = %outputs_history.len(),
            "Performing self-distillation"
        );

        // 取最近的N个输出
        let recent = &outputs_history[outputs_history.len().saturating_sub(self.ensemble_size)..];

        // 平均输出作为teacher
        let teacher_logits = self.average_logits(recent);

        Ok(teacher_logits)
    }

    fn average_logits(&self, logits: &[Array1<f32>]) -> Array1<f32> {
        let n = logits.len() as f32;
        let mut sum = Array1::zeros(logits[0].len());

        for logit in logits {
            sum = sum + logit;
        }

        sum / n
    }
}
```

### 4.3 Progressive Distillation

```rust
// src/distillation/progressive.rs
use tracing::{info, instrument};

/// 渐进式蒸馏
pub struct ProgressiveDistiller {
    stages: Vec<DistillationStage>,
    current_stage: usize,
}

#[derive(Debug, Clone)]
pub struct DistillationStage {
    pub student_size: f32,  // 相对于teacher的大小 (0.0 - 1.0)
    pub temperature: f32,
    pub epochs: usize,
}

impl ProgressiveDistiller {
    pub fn new(stages: Vec<DistillationStage>) -> Self {
        Self {
            stages,
            current_stage: 0,
        }
    }

    /// 进入下一阶段
    #[instrument(skip(self))]
    pub fn next_stage(&mut self) -> Option<&DistillationStage> {
        if self.current_stage < self.stages.len() {
            let stage = &self.stages[self.current_stage];
            info!(
                stage = %self.current_stage,
                student_size = %stage.student_size,
                temperature = %stage.temperature,
                "Moving to next distillation stage"
            );

            self.current_stage += 1;
            Some(stage)
        } else {
            None
        }
    }
}
```

---

## 5. 低秩分解

### 5.1 LoRA (Low-Rank Adaptation)

```rust
// src/decomposition/lora.rs
use ndarray::{Array2, ArrayView2};
use tracing::{info, instrument};

/// LoRA层
pub struct LoRALayer {
    rank: usize,
    alpha: f32,
    a: Array2<f32>, // (d, r)
    b: Array2<f32>, // (r, k)
}

impl LoRALayer {
    /// 创建LoRA层
    #[instrument]
    pub fn new(input_dim: usize, output_dim: usize, rank: usize, alpha: f32) -> Self {
        info!(
            input_dim = %input_dim,
            output_dim = %output_dim,
            rank = %rank,
            alpha = %alpha,
            "Creating LoRA layer"
        );

        // A: 正态分布初始化
        let a = Array2::from_shape_fn((input_dim, rank), |_| {
            rand::random::<f32>() * 0.01
        });

        // B: 零初始化
        let b = Array2::zeros((rank, output_dim));

        Self { rank, alpha, a, b }
    }

    /// 前向传播
    /// W' = W + (alpha / r) * A * B
    #[instrument(skip(self, input, base_weight))]
    pub fn forward(
        &self,
        input: &Array2<f32>,
        base_weight: &Array2<f32>,
    ) -> Result<Array2<f32>> {
        info!("LoRA forward pass");

        // 基础权重的输出
        let base_output = input.dot(base_weight);

        // LoRA的增量输出
        let lora_output = input.dot(&self.a).dot(&self.b);
        let scaled_lora = lora_output * (self.alpha / self.rank as f32);

        // 组合输出
        Ok(base_output + scaled_lora)
    }

    /// 合并LoRA到基础权重
    #[instrument(skip(self, base_weight))]
    pub fn merge_weights(&self, base_weight: &mut Array2<f32>) -> Result<()> {
        info!("Merging LoRA weights");

        let lora_weights = self.a.dot(&self.b) * (self.alpha / self.rank as f32);
        *base_weight = &*base_weight + &lora_weights;

        Ok(())
    }

    /// 参数数量
    pub fn num_parameters(&self) -> usize {
        self.a.len() + self.b.len()
    }
}
```

### 5.2 SVD分解

```rust
// src/decomposition/svd.rs
use ndarray::{Array1, Array2};
use ndarray_linalg::SVD;
use tracing::{info, instrument};

/// SVD分解器
pub struct SVDDecomposer {
    rank: usize,
}

impl SVDDecomposer {
    pub fn new(rank: usize) -> Self {
        Self { rank }
    }

    /// 低秩SVD分解
    /// W ≈ U * Σ * V^T
    #[instrument(skip(self, weight))]
    pub fn decompose(&self, weight: &Array2<f32>) -> Result<(Array2<f32>, Array1<f32>, Array2<f32>)> {
        info!(
            shape = ?weight.shape(),
            rank = %self.rank,
            "Performing SVD decomposition"
        );

        // SVD分解
        let (u_full, s_full, vt_full) = weight.svd(true, true)?;

        let u_full = u_full.unwrap();
        let vt_full = vt_full.unwrap();

        // 截断到指定rank
        let u = u_full.slice(s![.., ..self.rank]).to_owned();
        let s = s_full.slice(s![..self.rank]).to_owned();
        let vt = vt_full.slice(s![..self.rank, ..]).to_owned();

        let original_params = weight.len();
        let compressed_params = u.len() + s.len() + vt.len();

        info!(
            original_params = %original_params,
            compressed_params = %compressed_params,
            compression_ratio = %(original_params as f32 / compressed_params as f32),
            "SVD decomposition completed"
        );

        Ok((u, s, vt))
    }

    /// 重构权重
    pub fn reconstruct(
        &self,
        u: &Array2<f32>,
        s: &Array1<f32>,
        vt: &Array2<f32>,
    ) -> Array2<f32> {
        let s_diag = Array2::from_diag(s);
        u.dot(&s_diag).dot(vt)
    }
}
```

---

## 6. OTLP可观测性

### 6.1 压缩追踪

```rust
// src/observability/tracing.rs
use opentelemetry::trace::Span;
use tracing::{info, instrument};

#[instrument(
    skip(quantizer, weights),
    fields(
        otel.kind = "internal",
        compression.type = "quantization",
        compression.bits,
        compression.input_size,
        compression.output_size,
        compression.ratio,
    )
)]
pub async fn quantize_traced(
    quantizer: &PTQuantizer,
    weights: &Array1<f32>,
) -> Result<QuantizedTensor> {
    let span = tracing::Span::current();

    let input_size = weights.len() * 4; // FP32
    span.record("compression.input_size", input_size);
    span.record("compression.bits", quantizer.bits);

    let result = quantizer.quantize_tensor(weights)?;

    let output_size = result.data.len();
    let ratio = input_size as f32 / output_size as f32;

    span.record("compression.output_size", output_size);
    span.record("compression.ratio", ratio);

    info!(
        input_size = %input_size,
        output_size = %output_size,
        ratio = %ratio,
        "Quantization traced"
    );

    Ok(result)
}
```

### 6.2 性能指标

```rust
// 压缩指标
compression_ratio{type="quantization",bits="8"} 4.0
compression_ratio{type="pruning",sparsity="0.5"} 2.0
compression_ratio{type="distillation"} 10.0

compression_latency_seconds{type="quantization"} 0.123
compression_latency_seconds{type="pruning"} 0.456

model_accuracy{compressed="false"} 0.95
model_accuracy{compressed="true",type="q8"} 0.94
model_accuracy_loss{type="q8"} 0.01

model_inference_time_ms{compressed="false"} 150.0
model_inference_time_ms{compressed="true"} 45.0
inference_speedup{type="q8"} 3.33
```

---

## 7. 生产实践

### 7.1 压缩流程

```rust
// src/pipeline/compression.rs
use tracing::{info, instrument};

/// 压缩流程
pub struct CompressionPipeline {
    stages: Vec<CompressionStage>,
}

#[derive(Debug, Clone)]
pub enum CompressionStage {
    Quantization { bits: u8 },
    Pruning { sparsity: f32 },
    Distillation { temperature: f32 },
}

impl CompressionPipeline {
    pub fn new() -> Self {
        Self { stages: Vec::new() }
    }

    pub fn add_quantization(mut self, bits: u8) -> Self {
        self.stages.push(CompressionStage::Quantization { bits });
        self
    }

    pub fn add_pruning(mut self, sparsity: f32) -> Self {
        self.stages.push(CompressionStage::Pruning { sparsity });
        self
    }

    pub fn add_distillation(mut self, temperature: f32) -> Self {
        self.stages.push(CompressionStage::Distillation { temperature });
        self
    }

    /// 执行压缩流程
    #[instrument(skip(self))]
    pub async fn execute(&self) -> Result<CompressionResult> {
        info!(stages = %self.stages.len(), "Executing compression pipeline");

        let mut result = CompressionResult::default();

        for (i, stage) in self.stages.iter().enumerate() {
            info!(stage = %i, stage_type = ?stage, "Processing stage");

            match stage {
                CompressionStage::Quantization { bits } => {
                    info!(bits = %bits, "Applying quantization");
                    result.compression_ratio *= 32.0 / *bits as f32;
                }
                CompressionStage::Pruning { sparsity } => {
                    info!(sparsity = %sparsity, "Applying pruning");
                    result.compression_ratio *= 1.0 / (1.0 - sparsity);
                }
                CompressionStage::Distillation { temperature } => {
                    info!(temperature = %temperature, "Applying distillation");
                    // Distillation通常在训练阶段完成
                }
            }
        }

        info!(
            total_compression_ratio = %result.compression_ratio,
            "Compression pipeline completed"
        );

        Ok(result)
    }
}

#[derive(Debug, Default)]
pub struct CompressionResult {
    pub compression_ratio: f32,
    pub accuracy_loss: f32,
    pub speedup: f32,
}
```

### 7.2 质量评估

```rust
// src/evaluation/quality.rs
use ndarray::Array1;
use tracing::{info, instrument};

/// 质量评估器
pub struct QualityEvaluator;

impl QualityEvaluator {
    /// 评估压缩质量
    #[instrument(skip(original, compressed))]
    pub fn evaluate(
        original: &Array1<f32>,
        compressed: &Array1<f32>,
    ) -> Result<QualityMetrics> {
        info!("Evaluating compression quality");

        let mse = Self::mean_squared_error(original, compressed);
        let rmse = mse.sqrt();
        let psnr = Self::psnr(original, compressed);
        let cosine_sim = Self::cosine_similarity(original, compressed);

        let metrics = QualityMetrics {
            mse,
            rmse,
            psnr,
            cosine_similarity: cosine_sim,
        };

        info!(
            mse = %metrics.mse,
            rmse = %metrics.rmse,
            psnr = %metrics.psnr,
            cosine_similarity = %metrics.cosine_similarity,
            "Quality evaluation completed"
        );

        Ok(metrics)
    }

    fn mean_squared_error(a: &Array1<f32>, b: &Array1<f32>) -> f32 {
        let diff = a - b;
        diff.mapv(|x| x * x).mean().unwrap()
    }

    fn psnr(original: &Array1<f32>, compressed: &Array1<f32>) -> f32 {
        let mse = Self::mean_squared_error(original, compressed);
        let max_val = original.iter().cloned().fold(f32::NEG_INFINITY, f32::max);
        20.0 * max_val.log10() - 10.0 * mse.log10()
    }

    fn cosine_similarity(a: &Array1<f32>, b: &Array1<f32>) -> f32 {
        let dot = a.dot(b);
        let norm_a = a.dot(a).sqrt();
        let norm_b = b.dot(b).sqrt();
        dot / (norm_a * norm_b)
    }
}

#[derive(Debug)]
pub struct QualityMetrics {
    pub mse: f32,
    pub rmse: f32,
    pub psnr: f32,
    pub cosine_similarity: f32,
}
```

---

## 8. 参考资源

### 学术论文

- **量化**: "Quantization and Training of Neural Networks" (Google, 2018)
- **GPTQ**: "GPTQ: Accurate Post-Training Quantization" (Frantar et al., 2022)
- **剪枝**: "The Lottery Ticket Hypothesis" (Frankle & Carbin, 2019)
- **蒸馏**: "Distilling the Knowledge in a Neural Network" (Hinton et al., 2015)
- **LoRA**: "LoRA: Low-Rank Adaptation" (Hu et al., 2021)

### Rust生态

- **ndarray**: [https://docs.rs/ndarray](https://docs.rs/ndarray)
- **ndarray-linalg**: [https://docs.rs/ndarray-linalg](https://docs.rs/ndarray-linalg)
- **candle-core**: [https://github.com/huggingface/candle](https://github.com/huggingface/candle)

### 工具与框架

- **llama.cpp**: [https://github.com/ggerganov/llama.cpp](https://github.com/ggerganov/llama.cpp)
- **GPTQ-for-LLaMa**: [https://github.com/qwopqwop200/GPTQ-for-LLaMa](https://github.com/qwopqwop200/GPTQ-for-LLaMa)
- **bitsandbytes**: [https://github.com/TimDettmers/bitsandbytes](https://github.com/TimDettmers/bitsandbytes)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-13  
**Rust版本**: 1.90+  
**OpenTelemetry**: 0.27+  
**作者**: OTLP Rust 项目组
