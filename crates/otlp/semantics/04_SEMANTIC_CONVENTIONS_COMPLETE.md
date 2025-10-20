# OTLP语义约定完整覆盖

> **版本**: 1.0  
> **日期**: 2025年10月17日  
> **状态**: ✅ 完整版

---

## 📋 目录

- [OTLP语义约定完整覆盖](#otlp语义约定完整覆盖)
  - [📋 目录](#-目录)
  - [第一部分: 语义约定概述](#第一部分-语义约定概述)
    - [1.1 什么是语义约定?](#11-什么是语义约定)
      - [核心价值](#核心价值)
    - [1.2 约定成熟度](#12-约定成熟度)
    - [1.3 属性命名规范](#13-属性命名规范)
  - [第二部分: 通用约定](#第二部分-通用约定)
    - [2.1 Resource属性](#21-resource属性)
      - [2.1.1 Service属性(稳定)](#211-service属性稳定)
      - [2.1.2 Deployment属性(稳定)](#212-deployment属性稳定)
      - [2.1.3 Kubernetes属性(稳定)](#213-kubernetes属性稳定)
      - [2.1.4 Cloud属性(稳定)](#214-cloud属性稳定)
  - [第三部分: HTTP约定](#第三部分-http约定)
    - [3.1 HTTP通用属性(稳定)](#31-http通用属性稳定)
    - [3.2 HTTP Client Span示例](#32-http-client-span示例)
    - [3.3 HTTP Server Span示例](#33-http-server-span示例)
  - [第四部分: 数据库约定](#第四部分-数据库约定)
    - [4.1 Database通用属性(稳定)](#41-database通用属性稳定)
    - [4.2 SQL数据库特定属性](#42-sql数据库特定属性)
    - [4.3 NoSQL数据库特定属性](#43-nosql数据库特定属性)
    - [4.4 Database Span示例](#44-database-span示例)
  - [第五部分: 消息系统约定](#第五部分-消息系统约定)
    - [5.1 Messaging通用属性(稳定)](#51-messaging通用属性稳定)
    - [5.2 Kafka特定属性](#52-kafka特定属性)
    - [5.3 Messaging Span示例](#53-messaging-span示例)
  - [第六部分: RPC约定](#第六部分-rpc约定)
    - [6.1 gRPC属性(稳定)](#61-grpc属性稳定)
    - [6.2 gRPC Span示例](#62-grpc-span示例)
  - [第七部分: CI/CD约定](#第七部分-cicd约定)
    - [7.1 CI/CD属性(实验性)](#71-cicd属性实验性)
    - [7.2 CI/CD Span示例](#72-cicd-span示例)
  - [第八部分: Gen-AI约定](#第八部分-gen-ai约定)
    - [8.1 Gen-AI属性(实验性)](#81-gen-ai属性实验性)
    - [8.2 Gen-AI Span示例](#82-gen-ai-span示例)
  - [第九部分: 云平台约定](#第九部分-云平台约定)
    - [9.1 AWS服务约定](#91-aws服务约定)
    - [9.2 Azure服务约定](#92-azure服务约定)
  - [第十部分: 自定义约定](#第十部分-自定义约定)
    - [10.1 定义自定义约定](#101-定义自定义约定)
    - [10.2 自定义约定示例](#102-自定义约定示例)
  - [📚 参考资源](#-参考资源)

---

## 第一部分: 语义约定概述

### 1.1 什么是语义约定?

**语义约定(Semantic Conventions)** 是OpenTelemetry定义的标准化属性命名和值规范,用于确保遥测数据的一致性和可互操作性。

#### 核心价值

```text
语义约定的价值:
├── 一致性: 统一的命名,跨团队、跨组织可理解
├── 互操作性: 不同工具和后端无缝集成
├── 查询便利: 标准化属性易于查询和聚合
├── 自动化: 工具可基于约定自动分析和可视化
└── 最佳实践: 经过社区验证的最佳实践
```

### 1.2 约定成熟度

| 成熟度 | 说明 | 稳定性 |
|--------|------|--------|
| **Stable** | 稳定,不再有破坏性变更 | ✅ 生产可用 |
| **Experimental** | 实验阶段,可能变更 | ⚠️ 谨慎使用 |
| **Deprecated** | 已弃用,将被移除 | ❌ 迁移到新约定 |

### 1.3 属性命名规范

```yaml
# 命名规则
naming_rules:
  # 1. 使用小写字母和点分隔
  format: "namespace.subsystem.attribute"
  examples:
    - "http.method"
    - "db.system"
    - "messaging.operation"
  
  # 2. 命名空间
  namespaces:
    - http: HTTP协议
    - db: 数据库
    - messaging: 消息系统
    - rpc: 远程过程调用
    - net: 网络
    - server: 服务器
    - client: 客户端
  
  # 3. 避免使用
  avoid:
    - 驼峰命名: ❌ httpMethod
    - 下划线: ❌ http_method (Python内部可用)
    - 特殊字符: ❌ http/method
```

---

## 第二部分: 通用约定

### 2.1 Resource属性

#### 2.1.1 Service属性(稳定)

```yaml
# service.* - 服务标识
service.name:
  type: string
  required: true
  description: "服务名称"
  examples: ["frontend", "payment-api", "order-processor"]

service.version:
  type: string
  required: false
  description: "服务版本"
  examples: ["1.0.0", "v2.3.1", "2023.10.17"]

service.namespace:
  type: string
  required: false
  description: "服务命名空间/环境"
  examples: ["production", "staging", "tenant-123"]

service.instance.id:
  type: string
  required: false
  description: "服务实例唯一标识"
  examples: ["pod-abc123", "i-0123456789", "vm-prod-01"]
```

```rust
// Rust示例
use opentelemetry::sdk::Resource;
use opentelemetry::KeyValue;

let resource = Resource::new(vec![
    KeyValue::new("service.name", "payment-api"),
    KeyValue::new("service.version", "1.0.0"),
    KeyValue::new("service.namespace", "production"),
    KeyValue::new("service.instance.id", "pod-payment-7d9c4"),
]);
```

#### 2.1.2 Deployment属性(稳定)

```yaml
deployment.environment:
  type: string
  required: false
  description: "部署环境"
  examples: ["production", "staging", "dev"]
  enum: [production, staging, development, test]
```

#### 2.1.3 Kubernetes属性(稳定)

```yaml
k8s.cluster.name:
  type: string
  description: "K8s集群名称"
  example: "prod-us-east-1"

k8s.namespace.name:
  type: string
  description: "K8s命名空间"
  example: "ecommerce"

k8s.pod.name:
  type: string
  description: "Pod名称"
  example: "frontend-5d9c7f-xyz"

k8s.pod.uid:
  type: string
  description: "Pod UID"
  example: "a1b2c3d4-e5f6-..."

k8s.container.name:
  type: string
  description: "容器名称"
  example: "app"

k8s.deployment.name:
  type: string
  description: "Deployment名称"
  example: "frontend"

k8s.replicaset.name:
  type: string
  description: "ReplicaSet名称"
  example: "frontend-5d9c7f"

k8s.statefulset.name:
  type: string
  description: "StatefulSet名称"
  example: "database"

k8s.daemonset.name:
  type: string
  description: "DaemonSet名称"
  example: "fluentd"

k8s.job.name:
  type: string
  description: "Job名称"
  example: "backup-job"

k8s.cronjob.name:
  type: string
  description: "CronJob名称"
  example: "daily-report"
```

#### 2.1.4 Cloud属性(稳定)

```yaml
cloud.provider:
  type: string (enum)
  description: "云提供商"
  examples: ["aws", "azure", "gcp", "alibaba_cloud"]

cloud.platform:
  type: string (enum)
  description: "云平台服务"
  examples: ["aws_ec2", "aws_ecs", "aws_lambda", "azure_vm", "gcp_compute_engine"]

cloud.region:
  type: string
  description: "云区域"
  examples: ["us-east-1", "eu-west-1", "asia-southeast1"]

cloud.availability_zone:
  type: string
  description: "可用区"
  examples: ["us-east-1a", "eu-west-1b"]

cloud.account.id:
  type: string
  description: "云账号ID"
  example: "123456789012"
```

```rust
// AWS EC2示例
let resource = Resource::new(vec![
    KeyValue::new("cloud.provider", "aws"),
    KeyValue::new("cloud.platform", "aws_ec2"),
    KeyValue::new("cloud.region", "us-east-1"),
    KeyValue::new("cloud.availability_zone", "us-east-1a"),
    KeyValue::new("cloud.account.id", "123456789012"),
    KeyValue::new("host.id", "i-0123456789abcdef0"),
    KeyValue::new("host.type", "t3.medium"),
]);
```

---

## 第三部分: HTTP约定

### 3.1 HTTP通用属性(稳定)

```yaml
# HTTP基础属性
http.method:
  type: string (enum)
  required: true
  description: "HTTP请求方法"
  examples: ["GET", "POST", "PUT", "DELETE", "PATCH", "HEAD", "OPTIONS"]

http.url:
  type: string
  description: "完整URL"
  example: "https://api.example.com/v1/users/123?detail=true"
  note: "包含敏感信息时应脱敏"

http.target:
  type: string
  description: "请求目标(路径+查询)"
  example: "/v1/users/123?detail=true"

http.host:
  type: string
  description: "Host header"
  example: "api.example.com"

http.scheme:
  type: string (enum)
  description: "协议scheme"
  examples: ["http", "https"]

http.status_code:
  type: int
  required: true (for server)
  description: "HTTP状态码"
  examples: [200, 404, 500]

http.request_content_length:
  type: int
  description: "请求体大小(字节)"
  example: 1024

http.response_content_length:
  type: int
  description: "响应体大小(字节)"
  example: 4096

http.user_agent:
  type: string
  description: "User-Agent header"
  example: "Mozilla/5.0 ..."

http.route:
  type: string
  description: "路由模式"
  example: "/v1/users/:id"
  note: "应参数化,避免高基数"
```

### 3.2 HTTP Client Span示例

```rust
use opentelemetry::trace::{Tracer, SpanKind, Status, StatusCode};
use opentelemetry::{Context, KeyValue};

async fn make_http_request(
    tracer: &impl Tracer,
    method: &str,
    url: &str,
) -> Result<Response, Error> {
    let mut span = tracer
        .span_builder(format!("{} {}", method, url))
        .with_kind(SpanKind::Client)
        .with_attributes(vec![
            KeyValue::new("http.method", method.to_string()),
            KeyValue::new("http.url", url.to_string()),
            KeyValue::new("http.scheme", "https"),
        ])
        .start(tracer);
    
    let cx = Context::current_with_span(span);
    
    // 执行HTTP请求
    let response = match reqwest::get(url).await {
        Ok(resp) => {
            let status = resp.status().as_u16();
            
            cx.span().set_attribute(KeyValue::new("http.status_code", status as i64));
            cx.span().set_attribute(KeyValue::new(
                "http.response_content_length",
                resp.content_length().unwrap_or(0) as i64,
            ));
            
            // 状态码>=400视为错误
            if status >= 400 {
                cx.span().set_status(Status::Error {
                    description: format!("HTTP {}", status).into(),
                });
            }
            
            resp
        }
        Err(e) => {
            cx.span().set_status(Status::Error {
                description: e.to_string().into(),
            });
            cx.span().record_exception(&e);
            return Err(e.into());
        }
    };
    
    cx.span().end();
    Ok(response)
}
```

### 3.3 HTTP Server Span示例

```rust
use axum::{
    extract::Request,
    middleware::{self, Next},
    response::Response,
};

async fn otel_http_middleware(
    request: Request,
    next: Next,
) -> Response {
    let tracer = global::tracer("http-server");
    
    let method = request.method().as_str();
    let uri = request.uri();
    let path = uri.path();
    
    let mut span = tracer
        .span_builder(format!("{} {}", method, path))
        .with_kind(SpanKind::Server)
        .with_attributes(vec![
            KeyValue::new("http.method", method.to_string()),
            KeyValue::new("http.target", uri.to_string()),
            KeyValue::new("http.scheme", "https"),
            KeyValue::new("http.host", 
                request.headers()
                    .get("host")
                    .and_then(|h| h.to_str().ok())
                    .unwrap_or("unknown")
                    .to_string()
            ),
            KeyValue::new("http.user_agent",
                request.headers()
                    .get("user-agent")
                    .and_then(|h| h.to_str().ok())
                    .unwrap_or("")
                    .to_string()
            ),
            // 参数化路由
            KeyValue::new("http.route", parameterize_route(path)),
        ])
        .start(&tracer);
    
    let cx = Context::current_with_span(span);
    
    // 处理请求
    let response = next.run(request).await;
    
    let status = response.status().as_u16();
    cx.span().set_attribute(KeyValue::new("http.status_code", status as i64));
    
    if status >= 500 {
        cx.span().set_status(Status::Error {
            description: format!("HTTP {}", status).into(),
        });
    }
    
    cx.span().end();
    response
}

// 路径参数化
fn parameterize_route(path: &str) -> String {
    // 示例: /users/123 -> /users/:id
    // 实际应使用路由框架的路由模式
    path.to_string()
}
```

---

## 第四部分: 数据库约定

### 4.1 Database通用属性(稳定)

```yaml
db.system:
  type: string (enum)
  required: true
  description: "数据库系统"
  examples: ["mysql", "postgresql", "mongodb", "redis", "elasticsearch", "cassandra"]

db.connection_string:
  type: string
  description: "连接字符串(脱敏)"
  example: "Server=myServerAddress;Database=myDataBase;User Id=***"
  note: "必须脱敏密码"

db.user:
  type: string
  description: "数据库用户"
  example: "app_user"

db.name:
  type: string
  description: "数据库名称"
  example: "ecommerce"

db.statement:
  type: string
  description: "SQL语句或命令"
  example: "SELECT * FROM users WHERE id = ?"
  note: "应参数化,限制长度"

db.operation:
  type: string
  description: "操作类型"
  examples: ["SELECT", "INSERT", "UPDATE", "DELETE", "findOne", "aggregate"]
```

### 4.2 SQL数据库特定属性

```yaml
db.sql.table:
  type: string
  description: "表名"
  example: "users"

db.cassandra.keyspace:
  type: string
  description: "Cassandra keyspace"
  example: "mykeyspace"

db.cassandra.table:
  type: string
  description: "Cassandra表"
  example: "users"

db.cassandra.consistency_level:
  type: string (enum)
  description: "一致性级别"
  examples: ["ONE", "QUORUM", "ALL"]
```

### 4.3 NoSQL数据库特定属性

```yaml
# MongoDB
db.mongodb.collection:
  type: string
  description: "集合名称"
  example: "users"

# Redis
db.redis.database_index:
  type: int
  description: "Redis数据库索引"
  example: 0

# Elasticsearch
db.elasticsearch.index:
  type: string
  description: "索引名称"
  example: "logs-2025.10"
```

### 4.4 Database Span示例

```rust
use sqlx::{Pool, Postgres};

async fn query_user(
    tracer: &impl Tracer,
    pool: &Pool<Postgres>,
    user_id: i64,
) -> Result<User, Error> {
    let mut span = tracer
        .span_builder("SELECT users")
        .with_kind(SpanKind::Client)
        .with_attributes(vec![
            KeyValue::new("db.system", "postgresql"),
            KeyValue::new("db.name", "ecommerce"),
            KeyValue::new("db.statement", "SELECT * FROM users WHERE id = $1"),
            KeyValue::new("db.operation", "SELECT"),
            KeyValue::new("db.sql.table", "users"),
            KeyValue::new("db.user", "app_user"),
        ])
        .start(tracer);
    
    let cx = Context::current_with_span(span);
    
    let result = sqlx::query_as::<_, User>("SELECT * FROM users WHERE id = $1")
        .bind(user_id)
        .fetch_one(pool)
        .await;
    
    match &result {
        Ok(_) => {
            cx.span().set_status(Status::Ok);
        }
        Err(e) => {
            cx.span().set_status(Status::Error {
                description: e.to_string().into(),
            });
            cx.span().record_exception(e);
        }
    }
    
    cx.span().end();
    result.map_err(Into::into)
}
```

---

## 第五部分: 消息系统约定

### 5.1 Messaging通用属性(稳定)

```yaml
messaging.system:
  type: string (enum)
  required: true
  description: "消息系统"
  examples: ["kafka", "rabbitmq", "rocketmq", "activemq", "aws_sqs", "azure_servicebus"]

messaging.operation:
  type: string (enum)
  required: true
  description: "操作类型"
  examples: ["publish", "receive", "process"]

messaging.destination:
  type: string
  description: "目标(队列/主题)"
  example: "orders"

messaging.destination_kind:
  type: string (enum)
  description: "目标类型"
  examples: ["queue", "topic"]

messaging.message_id:
  type: string
  description: "消息ID"
  example: "msg-123456"

messaging.conversation_id:
  type: string
  description: "会话ID"
  example: "conv-abc"

messaging.message_payload_size_bytes:
  type: int
  description: "消息大小"
  example: 1024

messaging.message_payload_compressed_size_bytes:
  type: int
  description: "压缩后大小"
  example: 512
```

### 5.2 Kafka特定属性

```yaml
messaging.kafka.partition:
  type: int
  description: "分区号"
  example: 0

messaging.kafka.consumer_group:
  type: string
  description: "消费者组"
  example: "order-processors"

messaging.kafka.client_id:
  type: string
  description: "客户端ID"
  example: "consumer-1"

messaging.kafka.message_key:
  type: string
  description: "消息Key"
  example: "user-123"
```

### 5.3 Messaging Span示例

```rust
// Producer Span
async fn send_kafka_message(
    tracer: &impl Tracer,
    producer: &FutureProducer,
    topic: &str,
    key: &str,
    value: &[u8],
) -> Result<(), Error> {
    let mut span = tracer
        .span_builder(format!("{} publish", topic))
        .with_kind(SpanKind::Producer)
        .with_attributes(vec![
            KeyValue::new("messaging.system", "kafka"),
            KeyValue::new("messaging.operation", "publish"),
            KeyValue::new("messaging.destination", topic.to_string()),
            KeyValue::new("messaging.destination_kind", "topic"),
            KeyValue::new("messaging.kafka.message_key", key.to_string()),
            KeyValue::new("messaging.message_payload_size_bytes", value.len() as i64),
        ])
        .start(tracer);
    
    let cx = Context::current_with_span(span);
    
    // 注入Trace Context到消息Header
    let mut record = FutureRecord::to(topic)
        .key(key)
        .payload(value);
    
    inject_trace_context(&cx, &mut record);
    
    let result = producer.send(record, Duration::from_secs(5)).await;
    
    match result {
        Ok((partition, offset)) => {
            cx.span().set_attribute(KeyValue::new("messaging.kafka.partition", partition));
            cx.span().set_attribute(KeyValue::new("messaging.kafka.offset", offset));
            cx.span().set_status(Status::Ok);
        }
        Err((e, _)) => {
            cx.span().set_status(Status::Error {
                description: e.to_string().into(),
            });
        }
    }
    
    cx.span().end();
    result.map(|_| ()).map_err(|(e, _)| e.into())
}

// Consumer Span
async fn consume_kafka_message(
    tracer: &impl Tracer,
    message: &BorrowedMessage,
) -> Result<(), Error> {
    // 提取Trace Context
    let parent_cx = extract_trace_context(message);
    
    let mut span = tracer
        .span_builder(format!("{} process", message.topic()))
        .with_kind(SpanKind::Consumer)
        .with_parent_context(parent_cx)
        .with_attributes(vec![
            KeyValue::new("messaging.system", "kafka"),
            KeyValue::new("messaging.operation", "process"),
            KeyValue::new("messaging.destination", message.topic().to_string()),
            KeyValue::new("messaging.kafka.partition", message.partition()),
            KeyValue::new("messaging.kafka.offset", message.offset()),
            KeyValue::new("messaging.message_payload_size_bytes", 
                message.payload().map(|p| p.len()).unwrap_or(0) as i64),
        ])
        .start(tracer);
    
    let cx = Context::current_with_span(span);
    
    // 处理消息
    let result = process_message(message).await;
    
    match &result {
        Ok(_) => cx.span().set_status(Status::Ok),
        Err(e) => {
            cx.span().set_status(Status::Error {
                description: e.to_string().into(),
            });
            cx.span().record_exception(e);
        }
    }
    
    cx.span().end();
    result
}
```

---

## 第六部分: RPC约定

### 6.1 gRPC属性(稳定)

```yaml
rpc.system:
  type: string
  required: true
  description: "RPC系统"
  example: "grpc"

rpc.service:
  type: string
  required: true
  description: "服务名"
  example: "myservice.EchoService"

rpc.method:
  type: string
  required: true
  description: "方法名"
  example: "Echo"

rpc.grpc.status_code:
  type: int (enum)
  description: "gRPC状态码"
  examples: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
  # 0=OK, 1=CANCELLED, 2=UNKNOWN, ...
```

### 6.2 gRPC Span示例

```rust
use tonic::{Request, Response, Status};

// gRPC Server
#[tonic::async_trait]
impl MyService for MyServiceImpl {
    async fn echo(
        &self,
        request: Request<EchoRequest>,
    ) -> Result<Response<EchoResponse>, Status> {
        let tracer = global::tracer("grpc-server");
        
        // 提取Trace Context
        let parent_cx = extract_from_grpc_metadata(request.metadata());
        
        let mut span = tracer
            .span_builder("myservice.EchoService/Echo")
            .with_kind(SpanKind::Server)
            .with_parent_context(parent_cx)
            .with_attributes(vec![
                KeyValue::new("rpc.system", "grpc"),
                KeyValue::new("rpc.service", "myservice.EchoService"),
                KeyValue::new("rpc.method", "Echo"),
                KeyValue::new("net.peer.ip", "127.0.0.1"),
            ])
            .start(&tracer);
        
        let cx = Context::current_with_span(span);
        
        // 处理请求
        let result = self.echo_impl(request).await;
        
        match &result {
            Ok(_) => {
                cx.span().set_attribute(KeyValue::new("rpc.grpc.status_code", 0));
                cx.span().set_status(Status::Ok);
            }
            Err(status) => {
                let code = status.code() as i32;
                cx.span().set_attribute(KeyValue::new("rpc.grpc.status_code", code));
                cx.span().set_status(Status::Error {
                    description: status.message().into(),
                });
            }
        }
        
        cx.span().end();
        result
    }
}
```

---

## 第七部分: CI/CD约定

### 7.1 CI/CD属性(实验性)

```yaml
cicd.pipeline.name:
  type: string
  description: "Pipeline名称"
  example: "build-and-deploy"

cicd.pipeline.run.id:
  type: string
  description: "Pipeline运行ID"
  example: "run-123456"

cicd.pipeline.task.name:
  type: string
  description: "任务名称"
  example: "build"

cicd.pipeline.task.type:
  type: string (enum)
  description: "任务类型"
  examples: ["build", "test", "deploy"]

cicd.pipeline.task.run.id:
  type: string
  description: "任务运行ID"
  example: "task-run-456"

cicd.pipeline.task.run.url:
  type: string
  description: "任务运行URL"
  example: "https://ci.example.com/runs/123456"
```

### 7.2 CI/CD Span示例

```rust
async fn run_ci_pipeline(
    tracer: &impl Tracer,
    pipeline: &Pipeline,
) -> Result<(), Error> {
    let mut span = tracer
        .span_builder(format!("Pipeline: {}", pipeline.name))
        .with_kind(SpanKind::Internal)
        .with_attributes(vec![
            KeyValue::new("cicd.pipeline.name", pipeline.name.clone()),
            KeyValue::new("cicd.pipeline.run.id", pipeline.run_id.clone()),
        ])
        .start(tracer);
    
    let cx = Context::current_with_span(span);
    
    for task in &pipeline.tasks {
        run_ci_task(&cx, tracer, task).await?;
    }
    
    cx.span().end();
    Ok(())
}

async fn run_ci_task(
    parent_cx: &Context,
    tracer: &impl Tracer,
    task: &Task,
) -> Result<(), Error> {
    let mut span = tracer
        .span_builder(format!("Task: {}", task.name))
        .with_kind(SpanKind::Internal)
        .with_parent_context(parent_cx.clone())
        .with_attributes(vec![
            KeyValue::new("cicd.pipeline.task.name", task.name.clone()),
            KeyValue::new("cicd.pipeline.task.type", task.task_type.clone()),
            KeyValue::new("cicd.pipeline.task.run.id", task.run_id.clone()),
        ])
        .start(tracer);
    
    let cx = Context::current_with_span(span);
    
    let result = task.execute().await;
    
    match &result {
        Ok(_) => cx.span().set_status(Status::Ok),
        Err(e) => {
            cx.span().set_status(Status::Error {
                description: e.to_string().into(),
            });
            cx.span().record_exception(e);
        }
    }
    
    cx.span().end();
    result
}
```

---

## 第八部分: Gen-AI约定

### 8.1 Gen-AI属性(实验性)

```yaml
# LLM调用
gen_ai.system:
  type: string
  description: "AI系统"
  examples: ["openai", "anthropic", "cohere", "huggingface"]

gen_ai.request.model:
  type: string
  description: "模型名称"
  examples: ["gpt-4", "claude-2", "llama-2-70b"]

gen_ai.request.max_tokens:
  type: int
  description: "最大token数"
  example: 2048

gen_ai.request.temperature:
  type: double
  description: "温度参数"
  example: 0.7

gen_ai.request.top_p:
  type: double
  description: "Top-p参数"
  example: 0.9

gen_ai.response.id:
  type: string
  description: "响应ID"
  example: "chatcmpl-123"

gen_ai.response.model:
  type: string
  description: "实际使用的模型"
  example: "gpt-4-0613"

gen_ai.response.finish_reason:
  type: string (enum)
  description: "完成原因"
  examples: ["stop", "length", "content_filter"]

gen_ai.usage.input_tokens:
  type: int
  description: "输入token数"
  example: 100

gen_ai.usage.output_tokens:
  type: int
  description: "输出token数"
  example: 250

gen_ai.usage.total_tokens:
  type: int
  description: "总token数"
  example: 350
```

### 8.2 Gen-AI Span示例

```rust
async fn call_openai_api(
    tracer: &impl Tracer,
    prompt: &str,
) -> Result<String, Error> {
    let mut span = tracer
        .span_builder("gen_ai chat.completions")
        .with_kind(SpanKind::Client)
        .with_attributes(vec![
            KeyValue::new("gen_ai.system", "openai"),
            KeyValue::new("gen_ai.request.model", "gpt-4"),
            KeyValue::new("gen_ai.request.max_tokens", 2048),
            KeyValue::new("gen_ai.request.temperature", 0.7),
        ])
        .start(tracer);
    
    let cx = Context::current_with_span(span);
    
    let request = CreateChatCompletionRequest {
        model: "gpt-4".to_string(),
        messages: vec![
            ChatCompletionMessage {
                role: "user".to_string(),
                content: prompt.to_string(),
            },
        ],
        max_tokens: Some(2048),
        temperature: Some(0.7),
        ..Default::default()
    };
    
    let response = match openai_client.chat().create(request).await {
        Ok(resp) => {
            // 记录响应属性
            cx.span().set_attribute(KeyValue::new(
                "gen_ai.response.id",
                resp.id.clone(),
            ));
            cx.span().set_attribute(KeyValue::new(
                "gen_ai.response.model",
                resp.model.clone(),
            ));
            
            if let Some(usage) = &resp.usage {
                cx.span().set_attribute(KeyValue::new(
                    "gen_ai.usage.input_tokens",
                    usage.prompt_tokens as i64,
                ));
                cx.span().set_attribute(KeyValue::new(
                    "gen_ai.usage.output_tokens",
                    usage.completion_tokens as i64,
                ));
                cx.span().set_attribute(KeyValue::new(
                    "gen_ai.usage.total_tokens",
                    usage.total_tokens as i64,
                ));
            }
            
            if let Some(choice) = resp.choices.first() {
                cx.span().set_attribute(KeyValue::new(
                    "gen_ai.response.finish_reason",
                    choice.finish_reason.clone().unwrap_or_default(),
                ));
            }
            
            cx.span().set_status(Status::Ok);
            resp
        }
        Err(e) => {
            cx.span().set_status(Status::Error {
                description: e.to_string().into(),
            });
            cx.span().record_exception(&e);
            return Err(e.into());
        }
    };
    
    cx.span().end();
    
    Ok(response.choices.first()
        .and_then(|c| c.message.content.clone())
        .unwrap_or_default())
}
```

---

## 第九部分: 云平台约定

### 9.1 AWS服务约定

```yaml
# Lambda
faas.execution:
  type: string
  description: "Lambda执行ID"
  example: "79104EXAMPLEB723"

aws.lambda.invoked_arn:
  type: string
  description: "Lambda ARN"
  example: "arn:aws:lambda:us-east-1:123456789012:function:my-function"

# DynamoDB
aws.dynamodb.table_names:
  type: string[]
  description: "DynamoDB表名"
  example: ["users", "orders"]

aws.dynamodb.consumed_capacity:
  type: double[]
  description: "消耗的容量单位"
  example: [1.5, 2.3]

# S3
aws.s3.bucket:
  type: string
  description: "S3 bucket"
  example: "my-bucket"

aws.s3.key:
  type: string
  description: "S3 key"
  example: "data/file.json"
```

### 9.2 Azure服务约定

```yaml
az.namespace:
  type: string
  description: "Azure命名空间"
  example: "Microsoft.Storage"

az.service_bus.queue_name:
  type: string
  description: "Service Bus队列"
  example: "orders"

az.cosmos_db.container:
  type: string
  description: "Cosmos DB容器"
  example: "users"

az.cosmos_db.request_charge:
  type: double
  description: "请求单位消耗"
  example: 5.2
```

---

## 第十部分: 自定义约定

### 10.1 定义自定义约定

```yaml
# 自定义约定原则
custom_conventions:
  principles:
    - "使用组织前缀避免冲突: myorg.*"
    - "遵循命名规范: 小写+点分隔"
    - "文档化自定义约定"
    - "在团队内推广"
  
  example:
    # 业务属性
    myorg.business_unit:
      type: string
      description: "业务单元"
      examples: ["retail", "wholesale"]
    
    myorg.tenant_id:
      type: string
      description: "租户ID"
      example: "tenant-abc123"
    
    myorg.feature_flag:
      type: string
      description: "特性开关"
      example: "new-checkout-flow"
    
    myorg.experiment_id:
      type: string
      description: "实验ID"
      example: "exp-v2-checkout"
```

### 10.2 自定义约定示例

```rust
// 定义自定义属性常量
pub mod custom_attributes {
    pub const BUSINESS_UNIT: &str = "myorg.business_unit";
    pub const TENANT_ID: &str = "myorg.tenant_id";
    pub const FEATURE_FLAG: &str = "myorg.feature_flag";
    pub const EXPERIMENT_ID: &str = "myorg.experiment_id";
    pub const USER_TIER: &str = "myorg.user_tier";
}

// 使用自定义属性
fn create_span_with_custom_attrs(tracer: &impl Tracer) -> Span {
    tracer
        .span_builder("custom operation")
        .with_attributes(vec![
            // 标准属性
            KeyValue::new("service.name", "my-service"),
            
            // 自定义属性
            KeyValue::new(custom_attributes::BUSINESS_UNIT, "retail"),
            KeyValue::new(custom_attributes::TENANT_ID, "tenant-123"),
            KeyValue::new(custom_attributes::FEATURE_FLAG, "new-checkout"),
            KeyValue::new(custom_attributes::USER_TIER, "premium"),
        ])
        .start(tracer)
}
```

---

## 📚 参考资源

- [OTel语义约定规范](https://github.com/open-telemetry/semantic-conventions)
- [语义约定注册表](https://opentelemetry.io/docs/specs/semconv/)
- [约定变更日志](https://github.com/open-telemetry/semantic-conventions/blob/main/CHANGELOG.md)

---

**完整的语义约定覆盖!** 🎓
