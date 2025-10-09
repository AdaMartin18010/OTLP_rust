# Collector Pipeline 配置与管理 - Rust 完整版

## 目录

- [Collector Pipeline 配置与管理 - Rust 完整版](#collector-pipeline-配置与管理---rust-完整版)
  - [目录](#目录)
  - [1. Pipeline 概述](#1-pipeline-概述)
    - [1.1 Pipeline 架构](#11-pipeline-架构)
    - [1.2 Pipeline 类型](#12-pipeline-类型)
  - [2. 配置文件设计](#2-配置文件设计)
    - [2.1 YAML 配置结构](#21-yaml-配置结构)
    - [2.2 配置数据结构](#22-配置数据结构)
    - [2.3 配置加载](#23-配置加载)
  - [3. Pipeline 构建器](#3-pipeline-构建器)
    - [3.1 核心构建器](#31-核心构建器)
    - [3.2 Pipeline 运行](#32-pipeline-运行)
  - [4. 运行时管理](#4-运行时管理)
    - [4.1 Collector Service](#41-collector-service)
  - [5. 配置热更新](#5-配置热更新)
    - [5.1 文件监听](#51-文件监听)
  - [6. 健康检查与监控](#6-健康检查与监控)
    - [6.1 健康检查端点](#61-健康检查端点)
    - [6.2 内部指标](#62-内部指标)
  - [7. 完整示例](#7-完整示例)
    - [7.1 生产级 Collector 启动](#71-生产级-collector-启动)
  - [总结](#总结)

---

## 1. Pipeline 概述

**Pipeline** 是 Collector 的核心概念，定义了数据从 Receiver → Processor → Exporter 的完整流程。

### 1.1 Pipeline 架构

```text
┌──────────────────────────────────────────────┐
│              Service Config                  │
│  ┌────────────────────────────────────────┐ │
│  │  Traces Pipeline                       │ │
│  │  receivers: [otlp, jaeger]             │ │
│  │  processors: [batch, attributes]       │ │
│  │  exporters: [otlp, jaeger]             │ │
│  └────────────────────────────────────────┘ │
│  ┌────────────────────────────────────────┐ │
│  │  Metrics Pipeline                      │ │
│  │  receivers: [prometheus]               │ │
│  │  processors: [batch]                   │ │
│  │  exporters: [prometheus, otlp]         │ │
│  └────────────────────────────────────────┘ │
│  ┌────────────────────────────────────────┐ │
│  │  Logs Pipeline                         │ │
│  │  receivers: [otlp]                     │ │
│  │  processors: [filter, batch]           │ │
│  │  exporters: [otlp, logging]            │ │
│  └────────────────────────────────────────┘ │
└──────────────────────────────────────────────┘
```

### 1.2 Pipeline 类型

- **Traces Pipeline**：处理分布式追踪数据
- **Metrics Pipeline**：处理指标数据
- **Logs Pipeline**：处理日志数据

---

## 2. 配置文件设计

### 2.1 YAML 配置结构

```yaml
# collector-config.yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318
  
  jaeger:
    protocols:
      thrift_http:
        endpoint: 0.0.0.0:14268
  
  prometheus:
    config:
      scrape_configs:
        - job_name: 'app-metrics'
          scrape_interval: 15s
          static_configs:
            - targets: ['localhost:9090']

processors:
  batch:
    timeout: 10s
    send_batch_size: 1024
    send_batch_max_size: 2048
  
  memory_limiter:
    check_interval: 1s
    limit_mib: 512
    spike_limit_mib: 128
  
  attributes:
    actions:
      - key: environment
        value: production
        action: upsert
      - key: password
        action: delete
  
  filter:
    traces:
      span:
        - 'attributes["http.status_code"] == 200'

exporters:
  otlp:
    endpoint: backend:4317
    tls:
      insecure: false
      cert_file: /certs/cert.pem
      key_file: /certs/key.pem
    retry_on_failure:
      enabled: true
      initial_interval: 5s
      max_interval: 30s
      max_elapsed_time: 300s
  
  jaeger:
    endpoint: jaeger:14250
    tls:
      insecure: true
  
  prometheus:
    endpoint: 0.0.0.0:9464
  
  logging:
    loglevel: debug

extensions:
  health_check:
    endpoint: :13133
  
  pprof:
    endpoint: :1777
  
  zpages:
    endpoint: :55679

service:
  extensions: [health_check, pprof, zpages]
  
  pipelines:
    traces:
      receivers: [otlp, jaeger]
      processors: [memory_limiter, batch, attributes]
      exporters: [otlp, jaeger, logging]
    
    metrics:
      receivers: [prometheus, otlp]
      processors: [batch]
      exporters: [prometheus, otlp]
    
    logs:
      receivers: [otlp]
      processors: [filter, batch]
      exporters: [otlp, logging]
```

### 2.2 配置数据结构

```rust
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Deserialize, Serialize)]
pub struct CollectorConfig {
    pub receivers: HashMap<String, ReceiverConfig>,
    pub processors: HashMap<String, ProcessorConfig>,
    pub exporters: HashMap<String, ExporterConfig>,
    pub extensions: HashMap<String, ExtensionConfig>,
    pub service: ServiceConfig,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(tag = "type")]
pub enum ReceiverConfig {
    Otlp {
        protocols: OtlpProtocols,
    },
    Jaeger {
        protocols: JaegerProtocols,
    },
    Prometheus {
        config: PrometheusConfig,
    },
}

#[derive(Debug, Deserialize, Serialize)]
pub struct OtlpProtocols {
    pub grpc: Option<GrpcConfig>,
    pub http: Option<HttpConfig>,
}

#[derive(Debug, Deserialize, Serialize)]
pub struct GrpcConfig {
    pub endpoint: String,
}

#[derive(Debug, Deserialize, Serialize)]
pub struct HttpConfig {
    pub endpoint: String,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(tag = "type")]
pub enum ProcessorConfig {
    Batch {
        timeout: String,
        send_batch_size: usize,
        send_batch_max_size: usize,
    },
    MemoryLimiter {
        check_interval: String,
        limit_mib: usize,
        spike_limit_mib: usize,
    },
    Attributes {
        actions: Vec<AttributeAction>,
    },
    Filter {
        traces: Option<FilterTraces>,
    },
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(tag = "type")]
pub enum ExporterConfig {
    Otlp {
        endpoint: String,
        tls: Option<TlsConfig>,
        retry_on_failure: Option<RetryConfig>,
    },
    Jaeger {
        endpoint: String,
        tls: Option<TlsConfig>,
    },
    Prometheus {
        endpoint: String,
    },
    Logging {
        loglevel: String,
    },
}

#[derive(Debug, Deserialize, Serialize)]
pub struct ServiceConfig {
    pub extensions: Vec<String>,
    pub pipelines: HashMap<String, PipelineConfig>,
}

#[derive(Debug, Deserialize, Serialize)]
pub struct PipelineConfig {
    pub receivers: Vec<String>,
    pub processors: Vec<String>,
    pub exporters: Vec<String>,
}

#[derive(Debug, Deserialize, Serialize)]
pub struct TlsConfig {
    pub insecure: bool,
    pub cert_file: Option<String>,
    pub key_file: Option<String>,
}

#[derive(Debug, Deserialize, Serialize)]
pub struct RetryConfig {
    pub enabled: bool,
    pub initial_interval: String,
    pub max_interval: String,
    pub max_elapsed_time: String,
}
```

### 2.3 配置加载

```rust
use std::fs;

impl CollectorConfig {
    pub fn load(path: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let content = fs::read_to_string(path)?;
        let config: CollectorConfig = serde_yaml::from_str(&content)?;
        Ok(config)
    }
    
    pub fn validate(&self) -> Result<(), String> {
        // 验证引用完整性
        for (name, pipeline) in &self.service.pipelines {
            for receiver in &pipeline.receivers {
                if !self.receivers.contains_key(receiver) {
                    return Err(format!(
                        "Pipeline '{}' references unknown receiver '{}'",
                        name, receiver
                    ));
                }
            }
            
            for processor in &pipeline.processors {
                if !self.processors.contains_key(processor) {
                    return Err(format!(
                        "Pipeline '{}' references unknown processor '{}'",
                        name, processor
                    ));
                }
            }
            
            for exporter in &pipeline.exporters {
                if !self.exporters.contains_key(exporter) {
                    return Err(format!(
                        "Pipeline '{}' references unknown exporter '{}'",
                        name, exporter
                    ));
                }
            }
        }
        
        Ok(())
    }
}
```

---

## 3. Pipeline 构建器

### 3.1 核心构建器

```rust
use std::sync::Arc;
use tokio::sync::mpsc;

pub struct PipelineBuilder {
    config: CollectorConfig,
    receivers: HashMap<String, Arc<dyn Receiver>>,
    processors: HashMap<String, Arc<dyn Processor>>,
    exporters: HashMap<String, Arc<dyn CollectorExporter>>,
}

impl PipelineBuilder {
    pub fn new(config: CollectorConfig) -> Self {
        Self {
            config,
            receivers: HashMap::new(),
            processors: HashMap::new(),
            exporters: HashMap::new(),
        }
    }
    
    pub async fn build(mut self) -> Result<CollectorService, Box<dyn std::error::Error>> {
        // 1. 创建 Receivers
        for (name, config) in &self.config.receivers {
            let receiver = self.create_receiver(name, config).await?;
            self.receivers.insert(name.clone(), receiver);
        }
        
        // 2. 创建 Processors
        for (name, config) in &self.config.processors {
            let processor = self.create_processor(name, config)?;
            self.processors.insert(name.clone(), processor);
        }
        
        // 3. 创建 Exporters
        for (name, config) in &self.config.exporters {
            let exporter = self.create_exporter(name, config).await?;
            self.exporters.insert(name.clone(), exporter);
        }
        
        // 4. 构建 Pipelines
        let mut pipelines = HashMap::new();
        for (name, config) in &self.config.service.pipelines {
            let pipeline = self.build_pipeline(name, config)?;
            pipelines.insert(name.clone(), pipeline);
        }
        
        Ok(CollectorService {
            pipelines,
            receivers: self.receivers,
        })
    }
    
    async fn create_receiver(
        &self,
        name: &str,
        config: &ReceiverConfig,
    ) -> Result<Arc<dyn Receiver>, Box<dyn std::error::Error>> {
        match config {
            ReceiverConfig::Otlp { protocols } => {
                if let Some(grpc_config) = &protocols.grpc {
                    let (receiver, _, _, _) = OtlpGrpcReceiver::new(
                        grpc_config.endpoint.parse()?,
                        10000,
                    );
                    Ok(Arc::new(receiver))
                } else {
                    Err("OTLP receiver requires gRPC or HTTP config".into())
                }
            }
            ReceiverConfig::Jaeger { .. } => {
                // 创建 Jaeger Receiver
                todo!()
            }
            ReceiverConfig::Prometheus { .. } => {
                // 创建 Prometheus Receiver
                todo!()
            }
        }
    }
    
    fn create_processor(
        &self,
        name: &str,
        config: &ProcessorConfig,
    ) -> Result<Arc<dyn Processor>, Box<dyn std::error::Error>> {
        match config {
            ProcessorConfig::Batch { timeout, send_batch_size, .. } => {
                let timeout_duration = parse_duration(timeout)?;
                Ok(Arc::new(BatchProcessor::new(
                    *send_batch_size,
                    timeout_duration,
                    |_| {},
                )))
            }
            ProcessorConfig::Attributes { actions } => {
                Ok(Arc::new(AttributesProcessor::new(actions.clone())))
            }
            ProcessorConfig::Filter { .. } => {
                // 创建 Filter Processor
                todo!()
            }
            _ => Err(format!("Unknown processor type: {}", name).into()),
        }
    }
    
    async fn create_exporter(
        &self,
        name: &str,
        config: &ExporterConfig,
    ) -> Result<Arc<dyn CollectorExporter>, Box<dyn std::error::Error>> {
        match config {
            ExporterConfig::Otlp { endpoint, .. } => {
                Ok(Arc::new(OtlpGrpcExporter::new(endpoint.clone()).await?))
            }
            ExporterConfig::Jaeger { endpoint, .. } => {
                Ok(Arc::new(JaegerExporter::new(endpoint.clone())))
            }
            ExporterConfig::Logging { .. } => {
                Ok(Arc::new(LoggingExporter::new(true)))
            }
            _ => Err(format!("Unknown exporter type: {}", name).into()),
        }
    }
    
    fn build_pipeline(
        &self,
        name: &str,
        config: &PipelineConfig,
    ) -> Result<Pipeline, Box<dyn std::error::Error>> {
        let receivers = config.receivers
            .iter()
            .map(|name| self.receivers.get(name).unwrap().clone())
            .collect();
        
        let processors = config.processors
            .iter()
            .map(|name| self.processors.get(name).unwrap().clone())
            .collect();
        
        let exporters = config.exporters
            .iter()
            .map(|name| self.exporters.get(name).unwrap().clone())
            .collect();
        
        Ok(Pipeline {
            name: name.to_string(),
            receivers,
            processors,
            exporters,
        })
    }
}

fn parse_duration(s: &str) -> Result<Duration, Box<dyn std::error::Error>> {
    // 解析 "10s", "1m", "1h" 等格式
    let value: u64 = s[..s.len() - 1].parse()?;
    let unit = &s[s.len() - 1..];
    
    match unit {
        "s" => Ok(Duration::from_secs(value)),
        "m" => Ok(Duration::from_secs(value * 60)),
        "h" => Ok(Duration::from_secs(value * 3600)),
        _ => Err("Invalid duration unit".into()),
    }
}
```

### 3.2 Pipeline 运行

```rust
pub struct Pipeline {
    pub name: String,
    pub receivers: Vec<Arc<dyn Receiver>>,
    pub processors: Vec<Arc<dyn Processor>>,
    pub exporters: Vec<Arc<dyn CollectorExporter>>,
}

impl Pipeline {
    pub async fn run(&self) -> Result<(), Box<dyn std::error::Error>> {
        // 创建数据通道
        let (tx, mut rx) = mpsc::channel::<Vec<SpanData>>(1000);
        
        // 启动 Receivers
        for receiver in &self.receivers {
            let mut receiver = receiver.clone();
            receiver.start().await?;
        }
        
        // 数据处理循环
        tokio::spawn(async move {
            while let Some(mut spans) = rx.recv().await {
                // 通过所有 Processors
                for processor in &self.processors {
                    spans = processor.process_batch(spans).await;
                }
                
                // 通过所有 Exporters 导出
                for exporter in &self.exporters {
                    if let Err(e) = exporter.export_traces(spans.clone()).await {
                        eprintln!("Export error: {}", e);
                    }
                }
            }
        });
        
        Ok(())
    }
}
```

---

## 4. 运行时管理

### 4.1 Collector Service

```rust
pub struct CollectorService {
    pipelines: HashMap<String, Pipeline>,
    receivers: HashMap<String, Arc<dyn Receiver>>,
}

impl CollectorService {
    pub async fn start(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        // 启动所有 Pipelines
        for (name, pipeline) in &self.pipelines {
            println!("Starting pipeline: {}", name);
            pipeline.run().await?;
        }
        
        println!("Collector service started");
        Ok(())
    }
    
    pub async fn shutdown(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        // 优雅关闭所有 Receivers
        for (name, receiver) in &self.receivers {
            println!("Shutting down receiver: {}", name);
            let mut receiver = receiver.clone();
            receiver.shutdown().await?;
        }
        
        println!("Collector service stopped");
        Ok(())
    }
}
```

---

## 5. 配置热更新

### 5.1 文件监听

```rust
use notify::{Watcher, RecursiveMode, watcher, DebouncedEvent};
use std::sync::mpsc as std_mpsc;
use std::sync::{Arc, RwLock};

pub struct ConfigWatcher {
    config: Arc<RwLock<CollectorConfig>>,
    service: Arc<RwLock<Option<CollectorService>>>,
}

impl ConfigWatcher {
    pub fn new(config_path: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let config = CollectorConfig::load(config_path)?;
        
        Ok(Self {
            config: Arc::new(RwLock::new(config)),
            service: Arc::new(RwLock::new(None)),
        })
    }
    
    pub fn watch(&self, config_path: &str) -> Result<(), Box<dyn std::error::Error>> {
        let (tx, rx) = std_mpsc::channel();
        let mut watcher = watcher(tx, Duration::from_secs(2))?;
        
        watcher.watch(config_path, RecursiveMode::NonRecursive)?;
        
        let config = self.config.clone();
        let service = self.service.clone();
        let config_path = config_path.to_string();
        
        tokio::spawn(async move {
            for event in rx {
                match event {
                    DebouncedEvent::Write(_) | DebouncedEvent::Create(_) => {
                        println!("Config file changed, reloading...");
                        
                        match CollectorConfig::load(&config_path) {
                            Ok(new_config) => {
                                if let Err(e) = new_config.validate() {
                                    eprintln!("Invalid config: {}", e);
                                    continue;
                                }
                                
                                // 关闭旧服务
                                if let Some(mut old_service) = service.write().unwrap().take() {
                                    let _ = old_service.shutdown().await;
                                }
                                
                                // 启动新服务
                                match PipelineBuilder::new(new_config.clone()).build().await {
                                    Ok(mut new_service) => {
                                        if let Err(e) = new_service.start().await {
                                            eprintln!("Failed to start new service: {}", e);
                                        } else {
                                            *config.write().unwrap() = new_config;
                                            *service.write().unwrap() = Some(new_service);
                                            println!("Config reloaded successfully");
                                        }
                                    }
                                    Err(e) => {
                                        eprintln!("Failed to build new service: {}", e);
                                    }
                                }
                            }
                            Err(e) => {
                                eprintln!("Failed to load config: {}", e);
                            }
                        }
                    }
                    _ => {}
                }
            }
        });
        
        Ok(())
    }
}
```

---

## 6. 健康检查与监控

### 6.1 健康检查端点

```rust
use axum::{routing::get, Router, Json};
use serde_json::json;

pub async fn health_check_server(port: u16) {
    let app = Router::new()
        .route("/health", get(health_check))
        .route("/ready", get(readiness_check));
    
    let addr = format!("0.0.0.0:{}", port);
    println!("Health check server listening on {}", addr);
    
    axum::serve(
        tokio::net::TcpListener::bind(&addr).await.unwrap(),
        app,
    )
    .await
    .unwrap();
}

async fn health_check() -> Json<serde_json::Value> {
    Json(json!({
        "status": "ok",
        "timestamp": chrono::Utc::now().to_rfc3339(),
    }))
}

async fn readiness_check() -> Json<serde_json::Value> {
    // 检查所有 Receivers/Exporters 是否正常
    Json(json!({
        "status": "ready",
        "components": {
            "receivers": "ok",
            "processors": "ok",
            "exporters": "ok",
        }
    }))
}
```

### 6.2 内部指标

```rust
use prometheus::{Counter, Histogram, Registry};
use std::sync::Arc;

pub struct CollectorMetrics {
    pub spans_received: Counter,
    pub spans_exported: Counter,
    pub spans_dropped: Counter,
    pub export_latency: Histogram,
}

impl CollectorMetrics {
    pub fn new(registry: &Registry) -> Self {
        let spans_received = Counter::new("collector_spans_received_total", "Total spans received")
            .unwrap();
        let spans_exported = Counter::new("collector_spans_exported_total", "Total spans exported")
            .unwrap();
        let spans_dropped = Counter::new("collector_spans_dropped_total", "Total spans dropped")
            .unwrap();
        let export_latency = Histogram::new("collector_export_latency_seconds", "Export latency")
            .unwrap();
        
        registry.register(Box::new(spans_received.clone())).unwrap();
        registry.register(Box::new(spans_exported.clone())).unwrap();
        registry.register(Box::new(spans_dropped.clone())).unwrap();
        registry.register(Box::new(export_latency.clone())).unwrap();
        
        Self {
            spans_received,
            spans_exported,
            spans_dropped,
            export_latency,
        }
    }
}
```

---

## 7. 完整示例

### 7.1 生产级 Collector 启动

```rust
use tokio::signal;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 加载配置
    let config = CollectorConfig::load("collector-config.yaml")?;
    config.validate()?;
    
    // 2. 构建服务
    let mut service = PipelineBuilder::new(config).build().await?;
    
    // 3. 启动健康检查
    tokio::spawn(health_check_server(13133));
    
    // 4. 启动服务
    service.start().await?;
    
    // 5. 启动配置监听
    let config_watcher = ConfigWatcher::new("collector-config.yaml")?;
    config_watcher.watch("collector-config.yaml")?;
    
    // 6. 等待中断信号
    signal::ctrl_c().await?;
    println!("Received shutdown signal");
    
    // 7. 优雅关闭
    service.shutdown().await?;
    
    Ok(())
}
```

---

## 总结

Pipeline 配置与管理是 Collector 的**核心能力**，Rust 实现时需要注意：

1. **配置验证**：启动前检查引用完整性
2. **模块化构建**：通过 Builder 模式组装组件
3. **热更新**：支持配置文件变更后自动重载
4. **健康检查**：暴露 `/health` 和 `/ready` 端点
5. **可观测性**：收集 Collector 自身的指标

通过完善的配置管理，可以实现灵活、可靠的 Collector 部署。
