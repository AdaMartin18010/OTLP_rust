# LogRecordExporter - Rust 完整实现指南

## 📋 目录

- [LogRecordExporter - Rust 完整实现指南](#logrecordexporter---rust-完整实现指南)
  - [📋 目录](#-目录)
  - [核心概念](#核心概念)
  - [Exporter 类型](#exporter-类型)
  - [Rust 实现](#rust-实现)
    - [OTLP Exporter](#otlp-exporter)
      - [**gRPC 传输**](#grpc-传输)
      - [**HTTP/JSON 传输**](#httpjson-传输)
      - [**TLS 认证**](#tls-认证)
      - [**Header 认证**](#header-认证)
    - [Stdout Exporter](#stdout-exporter)
    - [File Exporter](#file-exporter)
    - [自定义 Exporter](#自定义-exporter)
      - [**Elasticsearch Exporter**](#elasticsearch-exporter)
  - [错误处理](#错误处理)
    - [**重试机制**](#重试机制)
    - [**降级策略**](#降级策略)
  - [性能优化](#性能优化)
    - [**批量压缩**](#批量压缩)
    - [**连接池复用**](#连接池复用)
  - [最佳实践](#最佳实践)
    - [✅ **推荐**](#-推荐)
    - [❌ **避免**](#-避免)
  - [依赖库](#依赖库)
    - [**核心依赖**](#核心依赖)
    - [**自定义 Exporter 依赖**](#自定义-exporter-依赖)
  - [总结](#总结)

---

## 核心概念

**LogRecordExporter** 负责将日志数据发送到存储后端：

```text
┌─────────────────────────────────────────────┐
│     LogRecordProcessor                      │
│  ┌───────────────────────────────────────┐  │
│  │ 批量聚合日志记录                        │ │
│  └───────────────────────────────────────┘  │
│                  ↓                          │
│  ┌───────────────────────────────────────┐  │
│  │ LogRecordExporter                     │  │
│  │  - 序列化日志数据                      │  │
│  │  - 发送到后端                          │  │
│  └───────────────────────────────────────┘  │
│                  ↓                          │
│   Backend (OTLP/Elasticsearch/File/...)     │
└─────────────────────────────────────────────┘
```

---

## Exporter 类型

| Exporter | 协议 | 适用场景 |
|----------|------|---------|
| **OTLP** | gRPC/HTTP | 标准后端、Collector |
| **Stdout** | 标准输出 | 本地调试 |
| **File** | 文件系统 | 本地持久化、备份 |
| **自定义** | 任意 | Elasticsearch、Loki、Splunk |

---

## Rust 实现

### OTLP Exporter

#### **gRPC 传输**

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{
    logs::{BatchLogProcessor, LoggerProvider},
    Resource,
};
use opentelemetry_otlp::WithExportConfig;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建 OTLP gRPC Exporter
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .with_timeout(Duration::from_secs(10))
        .build_log_exporter()?;

    let processor = BatchLogProcessor::builder(exporter).build();

    let provider = LoggerProvider::builder()
        .with_resource(Resource::new(vec![
            KeyValue::new("service.name", "otlp-logs-demo"),
        ]))
        .with_log_processor(processor)
        .build();

    global::set_logger_provider(provider.clone());

    // 使用日志
    tracing::info!("Application started with OTLP logging");
    tracing::error!(error_code = 500, "Server error occurred");

    provider.shutdown()?;
    Ok(())
}
```

---

#### **HTTP/JSON 传输**

```rust
let exporter = opentelemetry_otlp::new_exporter()
    .http()
    .with_endpoint("http://localhost:4318/v1/logs")
    .with_timeout(Duration::from_secs(10))
    .build_log_exporter()?;
```

---

#### **TLS 认证**

```rust
let exporter = opentelemetry_otlp::new_exporter()
    .tonic()
    .with_endpoint("https://collector.example.com:4317")
    .with_tls_config(
        tonic::transport::ClientTlsConfig::new()
            .ca_certificate(tonic::transport::Certificate::from_pem(
                std::fs::read_to_string("ca.pem")?
            ))
            .domain_name("collector.example.com"),
    )
    .build_log_exporter()?;
```

---

#### **Header 认证**

```rust
let mut headers = std::collections::HashMap::new();
headers.insert("Authorization".to_string(), "Bearer YOUR_TOKEN".to_string());

let exporter = opentelemetry_otlp::new_exporter()
    .http()
    .with_endpoint("http://localhost:4318/v1/logs")
    .with_headers(headers)
    .build_log_exporter()?;
```

---

### Stdout Exporter

```rust
use opentelemetry_stdout::LogExporter;

let exporter = LogExporter::default();

let processor = BatchLogProcessor::builder(exporter).build();

let provider = LoggerProvider::builder()
    .with_log_processor(processor)
    .build();

global::set_logger_provider(provider.clone());

// 日志会输出到控制台
tracing::info!("This will be printed to stdout");
```

**依赖**：

```toml
[dependencies]
opentelemetry-stdout = { version = "0.24", features = ["logs"] }
```

---

### File Exporter

**自定义文件导出器**-

```rust
use opentelemetry::logs::LogRecord;
use opentelemetry_sdk::logs::{LogExporter, LogResult};
use std::fs::OpenOptions;
use std::io::Write;
use std::sync::Mutex;

struct FileLogExporter {
    file: Mutex<std::fs::File>,
}

impl FileLogExporter {
    fn new(path: &str) -> std::io::Result<Self> {
        let file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)?;
        
        Ok(Self {
            file: Mutex::new(file),
        })
    }
}

impl LogExporter for FileLogExporter {
    fn export(&self, batch: Vec<&LogRecord>) -> LogResult<()> {
        let mut file = self.file.lock().unwrap();
        
        for record in batch {
            let line = format!(
                "[{}] {}: {}\n",
                record.timestamp
                    .map(|t| format!("{:?}", t))
                    .unwrap_or_else(|| "unknown".to_string()),
                record.severity_text.as_ref().unwrap_or(&"INFO".to_string()),
                record.body.as_ref()
                    .map(|b| b.to_string())
                    .unwrap_or_else(|| "".to_string())
            );
            
            file.write_all(line.as_bytes())
                .map_err(|e| opentelemetry::logs::LogError::Other(e.to_string()))?;
        }
        
        file.flush()
            .map_err(|e| opentelemetry::logs::LogError::Other(e.to_string()))?;
        
        Ok(())
    }

    fn shutdown(&self) -> LogResult<()> {
        self.file.lock().unwrap().flush()
            .map_err(|e| opentelemetry::logs::LogError::Other(e.to_string()))?;
        Ok(())
    }
}

// 使用
let file_exporter = FileLogExporter::new("logs/app.log")?;
let processor = SimpleLogProcessor::new(Box::new(file_exporter));
```

---

### 自定义 Exporter

#### **Elasticsearch Exporter**

```rust
use elasticsearch::{Elasticsearch, IndexParts};
use serde_json::json;

struct ElasticsearchExporter {
    client: Elasticsearch,
    index: String,
}

impl ElasticsearchExporter {
    async fn new(url: &str, index: String) -> Result<Self, elasticsearch::Error> {
        let transport = elasticsearch::http::transport::Transport::single_node(url)?;
        let client = Elasticsearch::new(transport);
        
        Ok(Self { client, index })
    }
}

#[async_trait::async_trait]
impl LogExporter for ElasticsearchExporter {
    fn export(&self, batch: Vec<&LogRecord>) -> LogResult<()> {
        tokio::runtime::Handle::current().block_on(async {
            for record in batch {
                let doc = json!({
                    "timestamp": record.timestamp,
                    "severity": record.severity_text,
                    "body": record.body,
                    "attributes": record.attributes,
                    "trace_id": record.trace_context.as_ref().map(|ctx| ctx.trace_id),
                    "span_id": record.trace_context.as_ref().map(|ctx| ctx.span_id),
                });

                self.client
                    .index(IndexParts::Index(&self.index))
                    .body(doc)
                    .send()
                    .await
                    .map_err(|e| opentelemetry::logs::LogError::Other(e.to_string()))?;
            }
            Ok(())
        })
    }

    fn shutdown(&self) -> LogResult<()> {
        Ok(())
    }
}

// 使用
let es_exporter = ElasticsearchExporter::new(
    "http://localhost:9200",
    "logs-production".to_string()
).await?;

let processor = BatchLogProcessor::builder(es_exporter).build();
```

**依赖**：

```toml
[dependencies]
elasticsearch = "8.5"
serde_json = "1.0"
async-trait = "0.1"
```

---

## 错误处理

### **重试机制**

```rust
use std::time::Duration;

struct RetryableExporter {
    inner: Box<dyn LogExporter>,
    max_retries: usize,
}

impl LogExporter for RetryableExporter {
    fn export(&self, batch: Vec<&LogRecord>) -> LogResult<()> {
        let mut attempts = 0;
        
        loop {
            match self.inner.export(batch.clone()) {
                Ok(_) => return Ok(()),
                Err(e) if attempts < self.max_retries => {
                    attempts += 1;
                    eprintln!("Export failed, retry {}/{}: {:?}", attempts, self.max_retries, e);
                    std::thread::sleep(Duration::from_secs(2u64.pow(attempts as u32)));
                }
                Err(e) => return Err(e),
            }
        }
    }

    fn shutdown(&self) -> LogResult<()> {
        self.inner.shutdown()
    }
}
```

---

### **降级策略**

```rust
struct FallbackExporter {
    primary: Box<dyn LogExporter>,
    fallback: Box<dyn LogExporter>,
}

impl LogExporter for FallbackExporter {
    fn export(&self, batch: Vec<&LogRecord>) -> LogResult<()> {
        match self.primary.export(batch.clone()) {
            Ok(_) => Ok(()),
            Err(e) => {
                eprintln!("Primary exporter failed, using fallback: {:?}", e);
                self.fallback.export(batch)
            }
        }
    }

    fn shutdown(&self) -> LogResult<()> {
        self.primary.shutdown()?;
        self.fallback.shutdown()?;
        Ok(())
    }
}

// 使用示例：OTLP 失败时写入本地文件
let fallback_exporter = FallbackExporter {
    primary: Box::new(otlp_exporter),
    fallback: Box::new(FileLogExporter::new("logs/fallback.log")?),
};
```

---

## 性能优化

### **批量压缩**

```rust
use flate2::write::GzEncoder;
use flate2::Compression;

fn compress_logs(data: &[u8]) -> Vec<u8> {
    let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
    encoder.write_all(data).unwrap();
    encoder.finish().unwrap()
}

// 在自定义 Exporter 中使用
impl LogExporter for CustomExporter {
    fn export(&self, batch: Vec<&LogRecord>) -> LogResult<()> {
        let json = serde_json::to_vec(&batch).unwrap();
        let compressed = compress_logs(&json);
        
        self.client
            .post(&self.url)
            .header("Content-Encoding", "gzip")
            .body(compressed)
            .send()
            .map_err(|e| LogError::Other(e.to_string()))?;
        
        Ok(())
    }
}
```

---

### **连接池复用**

```rust
use reqwest::Client;
use std::sync::Arc;

struct PooledExporter {
    client: Arc<Client>,
    url: String,
}

impl PooledExporter {
    fn new(url: String) -> Self {
        let client = Client::builder()
            .pool_max_idle_per_host(10)
            .timeout(Duration::from_secs(10))
            .build()
            .unwrap();
        
        Self {
            client: Arc::new(client),
            url,
        }
    }
}
```

---

## 最佳实践

### ✅ **推荐**

1. **选择合适的传输协议**：
   - gRPC：低延迟、高性能
   - HTTP/JSON：防火墙友好、易调试
2. **配置超时**：避免阻塞 Processor
3. **实现重试**：网络抖动时自动重试（指数退避）
4. **压缩数据**：大批量日志导出应启用 gzip
5. **降级策略**：主 Exporter 失败时写入本地文件
6. **连接池**：复用 HTTP 连接减少握手开销
7. **监控导出状态**：记录成功率和延迟

### ❌ **避免**

1. **阻塞导出**：Exporter 不应执行同步阻塞操作
2. **忽略错误**：导出失败应记录到备份位置
3. **无限重试**：应设置最大重试次数
4. **未关闭资源**：`shutdown()` 应清理连接和缓冲区

---

## 依赖库

### **核心依赖**

```toml
[dependencies]
opentelemetry = "0.24"
opentelemetry-sdk = "0.24"
opentelemetry-otlp = "0.24"          # OTLP
opentelemetry-stdout = "0.24"        # Stdout
tokio = { version = "1", features = ["full"] }
```

### **自定义 Exporter 依赖**

```toml
reqwest = { version = "0.12", features = ["json", "gzip"] }
elasticsearch = "8.5"
async-trait = "0.1"
serde_json = "1.0"
flate2 = "1.0"             # gzip 压缩
```

---

## 总结

| Exporter | 协议 | 适用场景 | 配置要点 |
|----------|------|---------|---------|
| **OTLP gRPC** | gRPC | 标准后端 | `with_endpoint()` + `with_timeout()` |
| **OTLP HTTP** | HTTP/JSON | 防火墙环境 | `http()` + `with_headers()` |
| **Stdout** | 标准输出 | 本地调试 | 直接输出到控制台 |
| **File** | 文件系统 | 本地备份 | 实现自定义 `FileLogExporter` |
| **自定义** | 任意 | Elasticsearch/Loki | 实现 `LogExporter` trait |

**完成**：Logs SDK 模块全部文档已创建！
