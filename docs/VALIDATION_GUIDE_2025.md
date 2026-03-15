# 数据验证指南 2025

**创建日期**: 2025年1月
**状态**: 📚 使用指南
**Rust 版本**: 1.92+

---

## 📋 概述

数据验证模块 (`crates/otlp/src/validation/`) 提供了数据格式验证和过滤功能，确保 OTLP 数据的正确性和完整性。

---

## 🚀 快速开始

### 基本使用

```rust
use otlp::validation::validate_telemetry_data;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let data = TelemetryData::new(/* ... */);

    // 验证数据
    validate_telemetry_data(&data)?;

    Ok(())
}
```

---

## 📖 详细说明

### 核心功能

#### 数据验证

验证 TelemetryData 的格式和内容。

**验证项**:

- 数据类型正确性
- 必需字段存在
- 字段值范围
- 时间戳有效性

---

## 💡 示例代码

### 示例 1: 基本验证

```rust
use otlp::validation::validate_telemetry_data;

fn validate_data(data: &TelemetryData) -> Result<(), Box<dyn std::error::Error>> {
    validate_telemetry_data(data)?;
    Ok(())
}
```

---

## 🎯 最佳实践

### 1. 尽早验证

在数据处理前进行验证：

```rust
// ✅ 推荐：先验证
validate_telemetry_data(&data)?;
process_data(data)?;

// ❌ 不推荐：后验证
process_data(data)?;
validate_telemetry_data(&data)?;
```

---

## 📚 参考资源

### API 参考

- `validate_telemetry_data` - 验证函数

---

**状态**: 📚 使用指南
**最后更新**: 2025年1月
