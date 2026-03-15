# 错误处理指南 2025

**创建日期**: 2025年1月
**状态**: 📚 使用指南
**Rust 版本**: 1.92+

---

## 📋 概述

错误处理模块 (`crates/otlp/src/error.rs`) 提供了统一的错误类型和处理机制，支持详细的错误信息、错误分类和错误上下文。

---

## 🚀 快速开始

### 基本错误处理

```rust
use otlp::error::{Result, OtlpError};

fn process_data() -> Result<()> {
    // 操作可能失败
    let result = some_operation()?;
    Ok(())
}

// 处理错误
match process_data() {
    Ok(()) => println!("成功"),
    Err(e) => eprintln!("错误: {}", e),
}
```

---

## 📖 详细说明

### 核心类型

#### OtlpError

主要的错误类型，包含所有 OTLP 相关的错误。

**变体**:

- `ValidationError(String)` - 校验错误
- `Configuration(ConfigurationError)` - 配置错误
- `Transport(TransportError)` - 传输错误
- `Data(DataError)` - 数据处理错误
- `Export(ExportError)` - 导出错误
- `Processing(ProcessingError)` - 处理错误
- `Performance(PerformanceError)` - 性能错误
- `Concurrency(ConcurrencyError)` - 并发错误
- `Resource(ResourceError)` - 资源错误
- `Compatibility(CompatibilityError)` - 兼容性错误
- `System(SystemError)` - 系统错误
- `Io(std::io::Error)` - IO 错误

#### Result<T>

类型别名：`Result<T> = std::result::Result<T, OtlpError>`

---

### 错误类型详解

#### ConfigurationError

配置相关的错误。

```rust
use otlp::error::ConfigurationError;

match error {
    ConfigurationError::InvalidEndpoint { url } => {
        eprintln!("无效的端点: {}", url);
    }
    ConfigurationError::InvalidTimeout { timeout } => {
        eprintln!("无效的超时: {:?}", timeout);
    }
    ConfigurationError::InvalidBatchConfig { message } => {
        eprintln!("无效的批处理配置: {}", message);
    }
    ConfigurationError::ValueOutOfRange { field, value, min, max } => {
        eprintln!("值超出范围: {} = {} (范围: {} - {})", field, value, min, max);
    }
}
```

#### TransportError

传输相关的错误。

```rust
use otlp::error::TransportError;

match error {
    TransportError::Connection { endpoint, reason } => {
        eprintln!("连接错误: {} - {}", endpoint, reason);
    }
    TransportError::Timeout { operation, timeout } => {
        eprintln!("超时错误: {} - {:?}", operation, timeout);
    }
    TransportError::Server { status, reason } => {
        eprintln!("服务器错误: {} - {}", status, reason);
    }
    TransportError::Serialization { reason } => {
        eprintln!("序列化错误: {}", reason);
    }
    TransportError::Deserialization { reason } => {
        eprintln!("反序列化错误: {}", reason);
    }
}
```

#### DataError

数据处理相关的错误。

```rust
use otlp::error::DataError;

match error {
    DataError::Validation { reason } => {
        eprintln!("数据验证失败: {}", reason);
    }
    DataError::Format { reason } => {
        eprintln!("数据格式错误: {}", reason);
    }
    DataError::Conversion { reason } => {
        eprintln!("数据转换错误: {}", reason);
    }
}
```

---

### 错误分类

#### ErrorSeverity

错误严重程度。

```rust
use otlp::error::ErrorSeverity;

pub enum ErrorSeverity {
    Info,      // 信息
    Warning,   // 警告
    Error,     // 错误
    Critical,  // 严重错误
}
```

#### ErrorCategory

错误类别。

```rust
use otlp::error::ErrorCategory;

pub enum ErrorCategory {
    Configuration,  // 配置错误
    Network,        // 网络错误
    Data,           // 数据错误
    System,         // 系统错误
    Performance,    // 性能错误
    Security,       // 安全错误
}
```

#### ErrorContext

错误上下文，提供额外的错误信息。

```rust
use otlp::error::ErrorContext;

let context = ErrorContext {
    severity: ErrorSeverity::Error,
    category: ErrorCategory::Network,
    timestamp: SystemTime::now(),
    metadata: HashMap::new(),
};
```

---

## 💡 示例代码

### 示例 1: 基本错误处理

```rust
use otlp::error::{Result, OtlpError};

fn process_data() -> Result<String> {
    // 可能失败的操作
    let data = fetch_data()?;
    Ok(data)
}

fn main() {
    match process_data() {
        Ok(data) => println!("数据: {}", data),
        Err(e) => eprintln!("错误: {}", e),
    }
}
```

### 示例 2: 错误类型匹配

```rust
use otlp::error::{OtlpError, ConfigurationError};

fn handle_error(error: OtlpError) {
    match error {
        OtlpError::Configuration(ConfigurationError::InvalidEndpoint { url }) => {
            eprintln!("请检查端点 URL: {}", url);
        }
        OtlpError::Transport(transport_error) => {
            eprintln!("传输错误: {}", transport_error);
        }
        OtlpError::Io(io_error) => {
            eprintln!("IO 错误: {}", io_error);
        }
        _ => {
            eprintln!("其他错误: {}", error);
        }
    }
}
```

### 示例 3: 错误上下文

```rust
use otlp::error::{ErrorContext, ErrorSeverity, ErrorCategory};
use std::collections::HashMap;
use std::time::SystemTime;

fn create_error_context() -> ErrorContext {
    let mut metadata = HashMap::new();
    metadata.insert("operation".to_string(), "export_data".to_string());
    metadata.insert("batch_size".to_string(), "1000".to_string());

    ErrorContext {
        severity: ErrorSeverity::Error,
        category: ErrorCategory::Network,
        timestamp: SystemTime::now(),
        metadata,
    }
}
```

### 示例 4: 错误转换

```rust
use otlp::error::{Result, OtlpError, ConfigurationError};

fn validate_config(value: usize) -> Result<()> {
    if value > 10000 {
        return Err(OtlpError::Configuration(
            ConfigurationError::ValueOutOfRange {
                field: "batch_size".to_string(),
                value: value as f64,
                min: 10.0,
                max: 10000.0,
            }
        ));
    }
    Ok(())
}
```

---

## 🎯 最佳实践

### 1. 使用 Result 类型

始终使用 `Result<T>` 类型来处理可能失败的操作：

```rust
use otlp::error::Result;

fn process_data() -> Result<String> {
    // 操作
    Ok("success".to_string())
}
```

### 2. 错误传播

使用 `?` 操作符来传播错误：

```rust
fn process_data() -> Result<String> {
    let config = load_config()?;  // 如果失败，自动返回错误
    let data = fetch_data()?;     // 如果失败，自动返回错误
    Ok(data)
}
```

### 3. 详细的错误信息

提供详细的错误信息，包括上下文：

```rust
use otlp::error::{OtlpError, ConfigurationError};

fn validate_endpoint(url: &str) -> Result<()> {
    if !url.starts_with("http") {
        return Err(OtlpError::Configuration(
            ConfigurationError::InvalidEndpoint {
                url: url.to_string(),
            }
        ));
    }
    Ok(())
}
```

### 4. 错误分类

根据错误的严重程度和类别进行分类：

```rust
use otlp::error::{ErrorSeverity, ErrorCategory};

fn classify_error(error: &OtlpError) -> (ErrorSeverity, ErrorCategory) {
    match error {
        OtlpError::Configuration(_) => (ErrorSeverity::Error, ErrorCategory::Configuration),
        OtlpError::Transport(_) => (ErrorSeverity::Warning, ErrorCategory::Network),
        OtlpError::Io(_) => (ErrorSeverity::Error, ErrorCategory::System),
        _ => (ErrorSeverity::Error, ErrorCategory::System),
    }
}
```

---

## ⚠️ 注意事项

### 1. 错误信息

确保错误信息清晰、有用：

```rust
// ❌ 错误：信息不清晰
return Err(OtlpError::ValidationError("错误".to_string()));

// ✅ 正确：信息清晰
return Err(OtlpError::ValidationError(
    format!("批处理大小 {} 超出范围 (10-10000)", batch_size)
));
```

### 2. 错误转换

使用 `From` trait 进行错误转换：

```rust
// 自动转换
let result: Result<()> = std::fs::read_to_string("file.txt")?;
```

### 3. 错误处理

不要忽略错误，始终处理：

```rust
// ❌ 错误：忽略错误
let _ = process_data();

// ✅ 正确：处理错误
match process_data() {
    Ok(data) => println!("成功: {}", data),
    Err(e) => eprintln!("错误: {}", e),
}
```

---

## 📚 参考资源

### 相关文档

- [配置指南](./CONFIG_GUIDE_2025.md) - 配置错误处理
- [客户端指南](./CLIENT_GUIDE_2025.md) - 客户端错误处理
- [导出器指南](./EXPORTER_GUIDE_2025.md) - 导出器错误处理

### API 参考

- `OtlpError` - 主要错误类型
- `Result<T>` - 结果类型别名
- `ErrorSeverity` - 错误严重程度
- `ErrorCategory` - 错误类别
- `ErrorContext` - 错误上下文

---

**状态**: 📚 使用指南
**最后更新**: 2025年1月
