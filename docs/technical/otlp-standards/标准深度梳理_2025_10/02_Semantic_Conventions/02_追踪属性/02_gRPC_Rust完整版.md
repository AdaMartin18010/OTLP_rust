# gRPC 语义约定 - Rust 完整实现

> **Rust版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **Tonic**: 0.14.2  
> **最后更新**: 2025年10月9日

---

## 目录

- [gRPC 语义约定 - Rust 完整实现](#grpc-语义约定---rust-完整实现)
  - [目录](#目录)
  - [1. gRPC 语义约定概述](#1-grpc-语义约定概述)
  - [2. gRPC 客户端追踪](#2-grpc-客户端追踪)
  - [3. gRPC 服务器追踪](#3-grpc-服务器追踪)
  - [4. 双向流追踪](#4-双向流追踪)
  - [5. 错误处理](#5-错误处理)
  - [6. 完整示例](#6-完整示例)

---

## 1. gRPC 语义约定概述

根据 OpenTelemetry 规范，gRPC 追踪需要记录以下属性：

```rust
use opentelemetry_semantic_conventions::trace::{
    RPC_SYSTEM,
    RPC_SERVICE,
    RPC_METHOD,
    RPC_GRPC_STATUS_CODE,
};

/// gRPC Span 属性
pub struct GrpcAttributes {
    pub system: String,           // "grpc"
    pub service: String,          // "myapp.UserService"
    pub method: String,           // "GetUser"
    pub status_code: i32,         // gRPC status code
}

/// gRPC 状态码映射
pub fn grpc_status_to_span_status(code: tonic::Code) -> opentelemetry::trace::Status {
    use tonic::Code;
    use opentelemetry::trace::Status;
    
    match code {
        Code::Ok => Status::Ok,
        Code::Cancelled => Status::error("Cancelled"),
        Code::Unknown => Status::error("Unknown"),
        Code::InvalidArgument => Status::error("Invalid argument"),
        Code::DeadlineExceeded => Status::error("Deadline exceeded"),
        Code::NotFound => Status::error("Not found"),
        Code::AlreadyExists => Status::error("Already exists"),
        Code::PermissionDenied => Status::error("Permission denied"),
        Code::ResourceExhausted => Status::error("Resource exhausted"),
        Code::FailedPrecondition => Status::error("Failed precondition"),
        Code::Aborted => Status::error("Aborted"),
        Code::OutOfRange => Status::error("Out of range"),
        Code::Unimplemented => Status::error("Unimplemented"),
        Code::Internal => Status::error("Internal error"),
        Code::Unavailable => Status::error("Unavailable"),
        Code::DataLoss => Status::error("Data loss"),
        Code::Unauthenticated => Status::error("Unauthenticated"),
    }
}
```

---

## 2. gRPC 客户端追踪

**客户端拦截器实现**:

```rust
use tonic::{Request, Response, Status};
use tonic::service::Interceptor;
use opentelemetry::{global, trace::{SpanKind, TraceContextExt}, propagation::Injector};

/// gRPC 客户端拦截器
#[derive(Clone)]
pub struct TracingInterceptor;

impl Interceptor for TracingInterceptor {
    fn call(&mut self, mut request: Request<()>) -> Result<Request<()>, Status> {
        // 注入 trace context 到 metadata
        global::get_text_map_propagator(|propagator| {
            let cx = opentelemetry::Context::current();
            let mut injector = MetadataInjector(request.metadata_mut());
            propagator.inject_context(&cx, &mut injector);
        });
        
        Ok(request)
    }
}

/// Metadata 注入器
struct MetadataInjector<'a>(&'a mut tonic::metadata::MetadataMap);

impl<'a> Injector for MetadataInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        if let Ok(key) = tonic::metadata::MetadataKey::from_bytes(key.as_bytes()) {
            if let Ok(val) = tonic::metadata::MetadataValue::try_from(&value) {
                self.0.insert(key, val);
            }
        }
    }
}

/// 带追踪的 gRPC 客户端
pub struct TracedGrpcClient<T> {
    inner: T,
}

impl<T> TracedGrpcClient<T> {
    pub fn new(inner: T) -> Self {
        Self { inner }
    }
    
    /// 执行带追踪的 unary 调用
    pub async fn unary_call<Req, Resp>(
        &mut self,
        service: &str,
        method: &str,
        request: Request<Req>,
    ) -> Result<Response<Resp>, Status>
    where
        T: tonic::client::GrpcService<tonic::body::BoxBody>,
        T::Error: Into<Box<dyn std::error::Error + Send + Sync>>,
    {
        let tracer = global::tracer("grpc-client");
        
        let mut span = tracer
            .span_builder(format!("{}/{}", service, method))
            .with_kind(SpanKind::Client)
            .start(&tracer);
        
        // 设置 gRPC 属性
        span.set_attribute(RPC_SYSTEM.string("grpc"));
        span.set_attribute(RPC_SERVICE.string(service.to_string()));
        span.set_attribute(RPC_METHOD.string(method.to_string()));
        
        let cx = opentelemetry::Context::current_with_span(span);
        
        // 执行调用
        let result = {
            let _guard = cx.attach();
            // 实际的 gRPC 调用
            todo!("实际调用需要根据具体服务实现")
        };
        
        // 记录响应状态
        match &result {
            Ok(_) => {
                cx.span().set_attribute(RPC_GRPC_STATUS_CODE.i64(0)); // OK
                cx.span().set_status(opentelemetry::trace::Status::Ok);
            }
            Err(status) => {
                cx.span().set_attribute(RPC_GRPC_STATUS_CODE.i64(status.code() as i64));
                cx.span().set_status(grpc_status_to_span_status(status.code()));
            }
        }
        
        result
    }
}

/// 使用示例
use proto::greeter_client::GreeterClient;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建带拦截器的客户端
    let channel = tonic::transport::Channel::from_static("http://localhost:50051")
        .connect()
        .await?;
    
    let client = GreeterClient::with_interceptor(channel, TracingInterceptor);
    
    // 调用会自动追踪
    let request = tonic::Request::new(proto::HelloRequest {
        name: "World".to_string(),
    });
    
    let response = client.say_hello(request).await?;
    
    println!("Response: {:?}", response.into_inner());
    
    Ok(())
}
```

---

## 3. gRPC 服务器追踪

**服务器拦截器实现**:

```rust
use tonic::{Request, Response, Status};
use opentelemetry::{global, propagation::Extractor};
use std::time::Instant;

/// gRPC 服务器拦截器
pub async fn tracing_interceptor<T>(
    request: Request<T>,
) -> Result<Request<T>, Status> {
    // 提取 trace context
    let parent_cx = global::get_text_map_propagator(|propagator| {
        let extractor = MetadataExtractor(request.metadata());
        propagator.extract(&extractor)
    });
    
    let _guard = parent_cx.attach();
    
    Ok(request)
}

/// Metadata 提取器
struct MetadataExtractor<'a>(&'a tonic::metadata::MetadataMap);

impl<'a> Extractor for MetadataExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.0.get(key)?.to_str().ok()
    }
    
    fn keys(&self) -> Vec<&str> {
        self.0.keys().map(|k| k.as_str()).collect()
    }
}

/// 完整的服务实现示例
pub struct MyGreeterService;

#[tonic::async_trait]
impl proto::greeter_server::Greeter for MyGreeterService {
    #[tracing::instrument(skip(self))]
    async fn say_hello(
        &self,
        request: Request<proto::HelloRequest>,
    ) -> Result<Response<proto::HelloReply>, Status> {
        let name = request.into_inner().name;
        
        // 在 span 中记录业务逻辑
        tracing::info!("Received request for: {}", name);
        
        // 模拟业务处理
        tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
        
        let reply = proto::HelloReply {
            message: format!("Hello, {}!", name),
        };
        
        Ok(Response::new(reply))
    }
}

/// 启动服务器
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    use tonic::transport::Server;
    use proto::greeter_server::GreeterServer;
    
    let addr = "[::1]:50051".parse()?;
    let greeter = MyGreeterService;
    
    println!("gRPC server listening on {}", addr);
    
    Server::builder()
        .add_service(GreeterServer::new(greeter))
        .serve(addr)
        .await?;
    
    Ok(())
}
```

---

## 4. 双向流追踪

**Stream 追踪实现**:

```rust
use futures::Stream;
use std::pin::Pin;

/// 双向流服务实现
#[tonic::async_trait]
impl proto::chat_server::Chat for MyChatService {
    type ChatStream = Pin<Box<dyn Stream<Item = Result<proto::ChatMessage, Status>> + Send>>;
    
    #[tracing::instrument(skip(self, request))]
    async fn chat(
        &self,
        request: Request<tonic::Streaming<proto::ChatMessage>>,
    ) -> Result<Response<Self::ChatStream>, Status> {
        let mut stream = request.into_inner();
        let span = tracing::Span::current();
        
        // 创建响应流
        let output = async_stream::try_stream! {
            while let Some(msg) = stream.message().await? {
                let _enter = span.enter();
                
                tracing::info!("Received message: {:?}", msg);
                
                // 处理消息
                let response = proto::ChatMessage {
                    user: "server".to_string(),
                    message: format!("Echo: {}", msg.message),
                };
                
                yield response;
            }
        };
        
        Ok(Response::new(Box::pin(output)))
    }
}

/// 客户端流式调用
#[tracing::instrument]
async fn client_streaming_call() -> Result<(), Box<dyn std::error::Error>> {
    let channel = tonic::transport::Channel::from_static("http://localhost:50051")
        .connect()
        .await?;
    
    let mut client = proto::chat_client::ChatClient::with_interceptor(
        channel,
        TracingInterceptor,
    );
    
    // 创建请求流
    let requests = async_stream::stream! {
        for i in 0..5 {
            yield proto::ChatMessage {
                user: "client".to_string(),
                message: format!("Message {}", i),
            };
            
            tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        }
    };
    
    let request = tonic::Request::new(requests);
    
    let mut response = client.chat(request).await?.into_inner();
    
    // 接收响应流
    while let Some(msg) = response.message().await? {
        tracing::info!("Received response: {:?}", msg);
    }
    
    Ok(())
}
```

---

## 5. 错误处理

**gRPC 错误追踪**:

```rust
use tonic::{Code, Status};

/// 错误处理中间件
pub fn handle_grpc_error(
    error: Status,
    span: &opentelemetry::trace::Span,
) {
    // 记录错误信息
    span.record_error(&error as &dyn std::error::Error);
    
    // 设置状态
    span.set_status(grpc_status_to_span_status(error.code()));
    
    // 记录错误详情
    span.set_attribute(
        opentelemetry::KeyValue::new("grpc.error.message", error.message().to_string())
    );
    
    // 根据错误类型记录额外信息
    match error.code() {
        Code::DeadlineExceeded => {
            span.set_attribute(
                opentelemetry::KeyValue::new("error.timeout", true)
            );
        }
        Code::ResourceExhausted => {
            span.set_attribute(
                opentelemetry::KeyValue::new("error.resource_exhausted", true)
            );
        }
        _ => {}
    }
}

/// 使用示例
#[tracing::instrument(err)]
async fn call_with_error_handling(
    client: &mut GreeterClient<tonic::transport::Channel>,
) -> Result<String, Status> {
    let request = tonic::Request::new(proto::HelloRequest {
        name: "World".to_string(),
    });
    
    match client.say_hello(request).await {
        Ok(response) => Ok(response.into_inner().message),
        Err(status) => {
            let span = tracing::Span::current();
            handle_grpc_error(status.clone(), &span);
            Err(status)
        }
    }
}
```

---

## 6. 完整示例

**生产级 gRPC 服务**:

```rust
use tonic::{transport::Server, Request, Response, Status};
use opentelemetry::{global, KeyValue};
use opentelemetry_sdk::{trace::TracerProvider, Resource};

/// 初始化 OpenTelemetry
async fn init_telemetry() -> TracerProvider {
    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint("http://localhost:4317")
        .build_span_exporter()
        .expect("Failed to create exporter");
    
    let provider = TracerProvider::builder()
        .with_batch_exporter(exporter, tokio::spawn)
        .with_resource(Resource::new(vec![
            KeyValue::new("service.name", "grpc-example"),
        ]))
        .build();
    
    global::set_tracer_provider(provider.clone());
    provider
}

/// 完整服务实现
pub struct ProductService;

#[tonic::async_trait]
impl proto::product_service_server::ProductService for ProductService {
    #[tracing::instrument(skip(self))]
    async fn get_product(
        &self,
        request: Request<proto::GetProductRequest>,
    ) -> Result<Response<proto::Product>, Status> {
        let product_id = request.into_inner().id;
        
        tracing::info!("Getting product: {}", product_id);
        
        // 模拟数据库查询
        let product = proto::Product {
            id: product_id,
            name: "Example Product".to_string(),
            price: 99.99,
        };
        
        Ok(Response::new(product))
    }
    
    #[tracing::instrument(skip(self))]
    async fn list_products(
        &self,
        _request: Request<proto::ListProductsRequest>,
    ) -> Result<Response<proto::ListProductsResponse>, Status> {
        tracing::info!("Listing products");
        
        // 模拟数据库查询
        let products = vec![
            proto::Product {
                id: 1,
                name: "Product 1".to_string(),
                price: 10.0,
            },
            proto::Product {
                id: 2,
                name: "Product 2".to_string(),
                price: 20.0,
            },
        ];
        
        Ok(Response::new(proto::ListProductsResponse { products }))
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt::init();
    
    // 初始化 OpenTelemetry
    let provider = init_telemetry().await;
    
    // 启动服务器
    let addr = "[::1]:50051".parse()?;
    let product_service = ProductService;
    
    println!("gRPC server listening on {}", addr);
    
    Server::builder()
        .add_service(proto::product_service_server::ProductServiceServer::new(
            product_service,
        ))
        .serve(addr)
        .await?;
    
    // 关闭
    provider.shutdown()?;
    
    Ok(())
}
```

---

**相关文档**:

- [HTTP 语义约定 Rust实现](01_HTTP_Rust完整版.md)
- [gRPC传输层 Rust完整版](../../01_OTLP核心协议/02_传输层_gRPC_Rust完整版.md)
- [Context Propagation详解](../../04_核心组件/04_Context_Propagation详解_Rust完整版.md)

**文档状态**: ✅ 完成  
**最后更新**: 2025年10月9日
