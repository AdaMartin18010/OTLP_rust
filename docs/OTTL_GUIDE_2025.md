# OTTL 转换语言指南 2025

**创建日期**: 2025年1月
**状态**: 📚 使用指南
**Rust 版本**: 1.92+

---

## 📋 概述

OTTL (OpenTelemetry Transformation Language) 模块 (`crates/otlp/src/ottl/`) 提供了完整的 OTTL 实现，包括语法解析、表达式求值、数据转换和字节码编译等功能。

---

## 🚀 快速开始

### 基本使用

```rust
use otlp::ottl::{OtlpTransform, TransformConfig};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = TransformConfig::new()
        .add_statement("set(attributes[\"service.name\"], \"my-service\")")
        .add_statement("where resource.attributes[\"env\"] == \"production\"");

    let transformer = OtlpTransform::new(config)?;
    let result = transformer.transform(telemetry_data).await?;

    Ok(())
}
```

---

## 📖 详细说明

### 核心类型

#### OtlpTransform

OTTL 转换器，用于执行数据转换。

**方法**:
- `new(config: TransformConfig) -> Result<Self>` - 创建转换器
- `transform(data: TelemetryData) -> Result<TransformResult>` - 转换数据

#### TransformConfig

转换配置，包含 OTTL 语句。

**方法**:
- `new() -> Self` - 创建配置
- `add_statement(statement: impl Into<String>) -> Self` - 添加语句

#### BytecodeCompiler

字节码编译器，将 OTTL 语句编译为字节码以提高性能。

**方法**:
- `new() -> Self` - 创建编译器
- `compile(statement: &Statement) -> Result<BytecodeProgram>` - 编译语句

---

## 💡 示例代码

### 示例 1: 基本转换

```rust
use otlp::ottl::{OtlpTransform, TransformConfig};

async fn basic_transform() -> Result<(), Box<dyn std::error::Error>> {
    let config = TransformConfig::new()
        .add_statement("set(attributes[\"service.name\"], \"my-service\")");

    let transformer = OtlpTransform::new(config)?;
    let result = transformer.transform(data).await?;

    Ok(())
}
```

### 示例 2: 条件转换

```rust
use otlp::ottl::{OtlpTransform, TransformConfig};

async fn conditional_transform() -> Result<(), Box<dyn std::error::Error>> {
    let config = TransformConfig::new()
        .add_statement("where resource.attributes[\"env\"] == \"production\"")
        .add_statement("set(attributes[\"priority\"], \"high\")");

    let transformer = OtlpTransform::new(config)?;
    let result = transformer.transform(data).await?;

    Ok(())
}
```

### 示例 3: 字节码编译

```rust
use otlp::ottl::{BytecodeCompiler, Statement};

fn compile_ottl() -> Result<(), Box<dyn std::error::Error>> {
    let mut compiler = BytecodeCompiler::new();
    let statement = Statement::parse("set(attributes[\"key\"], \"value\")")?;
    let program = compiler.compile(&statement)?;

    // 执行字节码程序
    // ...

    Ok(())
}
```

---

## 🎯 最佳实践

### 1. 使用字节码编译

对于频繁执行的转换，使用字节码编译以提高性能：

```rust
let mut compiler = BytecodeCompiler::new();
let program = compiler.compile(&statement)?;
```

### 2. 批量转换

对于多个数据，使用批量转换：

```rust
for data in data_batch {
    transformer.transform(data).await?;
}
```

---

## ⚠️ 注意事项

### 1. 语法正确性

确保 OTTL 语句语法正确：

```rust
// ❌ 错误：语法错误
.add_statement("set(attributes[\"key\"]")  // 缺少右括号

// ✅ 正确：语法正确
.add_statement("set(attributes[\"key\"], \"value\")")
```

---

## 📚 参考资源

### 相关文档

- [OTTL 规范](https://opentelemetry.io/docs/specs/otel/transforms/)

### API 参考

- `OtlpTransform` - 转换器
- `TransformConfig` - 转换配置
- `BytecodeCompiler` - 字节码编译器
- `BytecodeProgram` - 字节码程序

---

**状态**: 📚 使用指南
**最后更新**: 2025年1月
