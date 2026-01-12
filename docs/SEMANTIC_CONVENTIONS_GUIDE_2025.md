# 语义约定指南 2025

**创建日期**: 2025年1月
**状态**: 📚 使用指南
**Rust 版本**: 1.92+

---

## 📋 概述

语义约定模块 (`crates/otlp/src/semantic_conventions/`) 提供了 OpenTelemetry 语义约定的类型安全实现，确保跨所有遥测信号的一致属性命名和值。

---

## 🚀 快速开始

### 基本使用

```rust
use otlp::semantic_conventions::http::{HttpAttributesBuilder, HttpMethod};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let attrs = HttpAttributesBuilder::new()
        .method(HttpMethod::Get)
        .status_code(200)
        .url("https://api.example.com/users")
        .build()?;

    Ok(())
}
```

---

## 📖 详细说明

### 核心类型

#### HttpAttributes

HTTP 语义约定属性。

**方法**:

- `HttpAttributesBuilder::new() -> Self` - 创建构建器
- `method(method: HttpMethod) -> Self` - 设置 HTTP 方法
- `status_code(code: u16) -> Self` - 设置状态码
- `url(url: impl Into<String>) -> Self` - 设置 URL

#### DatabaseAttributes

数据库语义约定属性。

**方法**:

- `DatabaseAttributesBuilder::new() -> Self` - 创建构建器
- `system(system: DatabaseSystem) -> Self` - 设置数据库系统
- `operation(operation: DatabaseOperation) -> Self` - 设置操作类型

---

## 💡 示例代码

### 示例 1: HTTP 属性

```rust
use otlp::semantic_conventions::http::{HttpAttributesBuilder, HttpMethod};

fn create_http_attributes() -> Result<HttpAttributes, Box<dyn std::error::Error>> {
    let attrs = HttpAttributesBuilder::new()
        .method(HttpMethod::Post)
        .status_code(201)
        .url("https://api.example.com/users")
        .scheme("https")
        .user_agent("MyApp/1.0")
        .build()?;

    Ok(attrs)
}
```

### 示例 2: 数据库属性

```rust
use otlp::semantic_conventions::database::{DatabaseAttributesBuilder, DatabaseSystem, DatabaseOperation};

fn create_database_attributes() -> Result<DatabaseAttributes, Box<dyn std::error::Error>> {
    let attrs = DatabaseAttributesBuilder::new()
        .system(DatabaseSystem::Postgresql)
        .operation(DatabaseOperation::Select)
        .statement("SELECT * FROM users")
        .build()?;

    Ok(attrs)
}
```

---

## 🎯 最佳实践

### 1. 使用语义约定

始终使用语义约定而不是自定义属性：

```rust
// ✅ 推荐：使用语义约定
let attrs = HttpAttributesBuilder::new()
    .method(HttpMethod::Get)
    .status_code(200)
    .build()?;

// ❌ 不推荐：自定义属性
let mut attrs = HashMap::new();
attrs.insert("http.method".to_string(), "GET".to_string());
```

---

## 📚 参考资源

### 相关文档

- [OpenTelemetry 语义约定](https://opentelemetry.io/docs/specs/semconv/)

### API 参考

- `HttpAttributes` - HTTP 属性
- `DatabaseAttributes` - 数据库属性
- `MessagingAttributes` - 消息属性
- `K8sAttributes` - Kubernetes 属性

---

**状态**: 📚 使用指南
**最后更新**: 2025年1月
