# 电商平台分布式追踪 - OpenTelemetry Rust 完整实战

> **版本信息**
>
> - Rust: 1.90 (2024 Edition)
> - opentelemetry: 0.31.0
> - 更新日期: 2025-10-08
> - 行业: 电子商务

## 目录

- [电商平台分布式追踪 - OpenTelemetry Rust 完整实战](#电商平台分布式追踪---opentelemetry-rust-完整实战)
  - [目录](#目录)
  - [概述](#概述)
    - [核心特性](#核心特性)
  - [系统架构](#系统架构)
  - [核心依赖配置](#核心依赖配置)
    - [Cargo.toml](#cargotoml)
  - [1. 用户服务](#1-用户服务)
    - [用户模型](#用户模型)
    - [用户登录追踪](#用户登录追踪)
  - [2. 商品服务](#2-商品服务)
    - [商品模型](#商品模型)
    - [商品查询追踪](#商品查询追踪)
  - [3. 订单服务](#3-订单服务)
    - [订单模型](#订单模型)
    - [创建订单追踪](#创建订单追踪)
  - [4. 库存服务](#4-库存服务)
    - [库存模型](#库存模型)
    - [库存操作追踪](#库存操作追踪)
  - [5. 购物车服务](#5-购物车服务)
    - [购物车模型](#购物车模型)
    - [购物车操作追踪](#购物车操作追踪)
  - [6. 支付服务](#6-支付服务)
    - [支付模型](#支付模型)
    - [支付处理追踪](#支付处理追踪)
  - [7. 物流服务](#7-物流服务)
    - [物流模型](#物流模型)
    - [物流追踪](#物流追踪)
  - [8. 推荐服务](#8-推荐服务)
    - [推荐引擎追踪](#推荐引擎追踪)
  - [9. 搜索服务](#9-搜索服务)
    - [Elasticsearch 集成](#elasticsearch-集成)
  - [10. 分布式追踪实战](#10-分布式追踪实战)
    - [完整下单流程追踪](#完整下单流程追踪)
  - [11. 性能优化](#11-性能优化)
    - [缓存策略](#缓存策略)
    - [批量操作](#批量操作)
  - [12. 完整示例](#12-完整示例)
    - [main.rs](#mainrs)
  - [总结](#总结)

---

## 概述

电商平台是典型的微服务架构，涉及大量服务间调用。本文档展示如何使用 OpenTelemetry Rust SDK 实现完整的分布式追踪。

### 核心特性

- ✅ 微服务全链路追踪
- ✅ 异步消息队列追踪
- ✅ 缓存命中率监控
- ✅ 数据库查询性能分析
- ✅ 用户行为追踪
- ✅ 实时性能指标

---

## 系统架构

```text
┌─────────────────────────────────────────────────────┐
│              API Gateway (Axum)                      │
└───────────┬─────────────────────────────────────────┘
            │
    ┌───────┼───────┬───────┬───────┬───────┬───────┐
    │       │       │       │       │       │       │
┌───▼───┐ ┌─▼──┐ ┌─▼──┐ ┌─▼──┐ ┌─▼──┐ ┌─▼──┐ ┌─▼──┐
│ User  │ │Prod│ │Ord │ │Inv │ │Cart│ │Pay │ │Ship│
│Service│ │Svc │ │Svc │ │Svc │ │Svc │ │Svc │ │Svc │
└───┬───┘ └─┬──┘ └─┬──┘ └─┬──┘ └─┬──┘ └─┬──┘ └─┬──┘
    │       │      │      │      │      │      │
    └───────┴──────┴──────┴──────┴──────┴──────┘
                    │
        ┌───────────┼───────────┐
        │           │           │
    ┌───▼───┐   ┌───▼───┐   ┌───▼───┐
    │ Redis │   │  PG   │   │ Kafka │
    └───────┘   └───────┘   └───────┘
```

---

## 核心依赖配置

### Cargo.toml

```toml
[package]
name = "ecommerce-platform"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

[dependencies]
axum = "0.7.9"
tokio = { version = "1.43.0", features = ["full"] }
opentelemetry = "0.31.0"
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio"] }
opentelemetry-otlp = "0.24.0"
tracing = "0.1.41"
tracing-opentelemetry = "0.27.0"
sqlx = { version = "0.8.2", features = ["postgres", "runtime-tokio"] }
redis = { version = "0.27.6", features = ["tokio-comp"] }
rdkafka = "0.37.0"
serde = { version = "1.0.216", features = ["derive"] }
serde_json = "1.0.133"
uuid = { version = "1.11.0", features = ["v4", "serde"] }
chrono = "0.4.39"
rust_decimal = "1.37.0"
```

---

## 1. 用户服务

### 用户模型

```rust
use serde::{Deserialize, Serialize};
use uuid::Uuid;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct User {
    pub id: Uuid,
    pub username: String,
    pub email: String,
    pub phone: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

#[derive(Debug, Deserialize)]
pub struct LoginRequest {
    pub username: String,
    pub password: String,
}
```

### 用户登录追踪

```rust
use tracing::{instrument, info, warn};
use opentelemetry::KeyValue;

pub struct UserService {
    db_pool: sqlx::PgPool,
    redis_client: redis::Client,
}

impl UserService {
    #[instrument(
        name = "user.login",
        skip(self, request),
        fields(username = %request.username)
    )]
    pub async fn login(&self, request: LoginRequest) -> Result<User, UserError> {
        info!("User login attempt");
        
        // 查询用户
        let user = self.find_user_by_username(&request.username).await?;
        
        // 验证密码
        if !self.verify_password(&request.password, &user.password_hash).await? {
            warn!("Invalid password");
            return Err(UserError::InvalidCredentials);
        }
        
        // 创建会话
        let session_id = self.create_session(user.id).await?;
        
        info!(user_id = %user.id, session_id = %session_id, "Login successful");
        
        Ok(user)
    }
    
    #[instrument(skip(self))]
    async fn find_user_by_username(&self, username: &str) -> Result<User, UserError> {
        sqlx::query_as::<_, User>(
            "SELECT * FROM users WHERE username = $1"
        )
        .bind(username)
        .fetch_one(&self.db_pool)
        .await
        .map_err(|_| UserError::NotFound)
    }
}
```

---

## 2. 商品服务

### 商品模型

```rust
#[derive(Debug, Clone, Serialize, Deserialize, sqlx::FromRow)]
pub struct Product {
    pub id: Uuid,
    pub name: String,
    pub description: String,
    pub price: rust_decimal::Decimal,
    pub stock: i32,
    pub category_id: Uuid,
    pub created_at: chrono::DateTime<chrono::Utc>,
}
```

### 商品查询追踪

```rust
pub struct ProductService {
    db_pool: sqlx::PgPool,
    redis_client: redis::Client,
}

impl ProductService {
    #[instrument(name = "product.get", skip(self))]
    pub async fn get_product(&self, product_id: Uuid) -> Result<Product, ProductError> {
        // 先查缓存
        if let Some(product) = self.get_from_cache(product_id).await? {
            info!("Cache hit");
            return Ok(product);
        }
        
        info!("Cache miss, querying database");
        
        // 查数据库
        let product = sqlx::query_as::<_, Product>(
            "SELECT * FROM products WHERE id = $1"
        )
        .bind(product_id)
        .fetch_one(&self.db_pool)
        .await
        .map_err(|_| ProductError::NotFound)?;
        
        // 写入缓存
        self.set_to_cache(&product).await?;
        
        Ok(product)
    }
    
    #[instrument(skip(self))]
    async fn get_from_cache(&self, product_id: Uuid) -> Result<Option<Product>, ProductError> {
        let mut conn = self.redis_client.get_connection_manager().await?;
        let key = format!("product:{}", product_id);
        
        let data: Option<String> = redis::cmd("GET")
            .arg(&key)
            .query_async(&mut conn)
            .await?;
        
        match data {
            Some(json) => {
                let product = serde_json::from_str(&json)?;
                Ok(Some(product))
            }
            None => Ok(None),
        }
    }
}
```

---

## 3. 订单服务

### 订单模型

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Order {
    pub id: Uuid,
    pub user_id: Uuid,
    pub total_amount: rust_decimal::Decimal,
    pub status: OrderStatus,
    pub items: Vec<OrderItem>,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum OrderStatus {
    Pending,
    Confirmed,
    Paid,
    Shipped,
    Delivered,
    Cancelled,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OrderItem {
    pub product_id: Uuid,
    pub quantity: i32,
    pub price: rust_decimal::Decimal,
}
```

### 创建订单追踪

```rust
pub struct OrderService {
    db_pool: sqlx::PgPool,
    product_service: Arc<ProductService>,
    inventory_service: Arc<InventoryService>,
    kafka_producer: Arc<rdkafka::producer::FutureProducer>,
}

impl OrderService {
    #[instrument(
        name = "order.create",
        skip(self, request),
        fields(user_id = %request.user_id)
    )]
    pub async fn create_order(&self, request: CreateOrderRequest) -> Result<Order, OrderError> {
        info!("Creating order");
        
        // 1. 验证商品库存
        for item in &request.items {
            self.inventory_service.check_stock(item.product_id, item.quantity).await?;
        }
        
        // 2. 计算总价
        let total_amount = self.calculate_total(&request.items).await?;
        
        // 3. 创建订单
        let mut tx = self.db_pool.begin().await?;
        
        let order_id = Uuid::new_v4();
        sqlx::query(
            r#"
            INSERT INTO orders (id, user_id, total_amount, status, created_at)
            VALUES ($1, $2, $3, $4, $5)
            "#
        )
        .bind(order_id)
        .bind(request.user_id)
        .bind(total_amount)
        .bind("pending")
        .bind(chrono::Utc::now())
        .execute(&mut *tx)
        .await?;
        
        // 4. 插入订单明细
        for item in &request.items {
            sqlx::query(
                r#"
                INSERT INTO order_items (order_id, product_id, quantity, price)
                VALUES ($1, $2, $3, $4)
                "#
            )
            .bind(order_id)
            .bind(item.product_id)
            .bind(item.quantity)
            .bind(item.price)
            .execute(&mut *tx)
            .await?;
        }
        
        // 5. 扣减库存
        for item in &request.items {
            self.inventory_service.decrease_stock(item.product_id, item.quantity).await?;
        }
        
        tx.commit().await?;
        
        // 6. 发送订单创建事件
        self.publish_order_created_event(order_id).await?;
        
        info!(order_id = %order_id, "Order created successfully");
        
        Ok(Order {
            id: order_id,
            user_id: request.user_id,
            total_amount,
            status: OrderStatus::Pending,
            items: request.items.clone(),
            created_at: chrono::Utc::now(),
        })
    }
    
    #[instrument(skip(self))]
    async fn publish_order_created_event(&self, order_id: Uuid) -> Result<(), OrderError> {
        let event = serde_json::json!({
            "event_type": "order_created",
            "order_id": order_id,
            "timestamp": chrono::Utc::now(),
        });
        
        let payload = serde_json::to_string(&event)?;
        let record = rdkafka::producer::FutureRecord::to("order-events")
            .payload(&payload)
            .key(&order_id.to_string());
        
        self.kafka_producer
            .send(record, std::time::Duration::from_secs(5))
            .await
            .map_err(|(e, _)| OrderError::KafkaError(e.to_string()))?;
        
        Ok(())
    }
}
```

---

## 4. 库存服务

### 库存模型

```rust
#[derive(Debug, Clone)]
pub struct Inventory {
    pub product_id: Uuid,
    pub quantity: i32,
    pub reserved: i32,
    pub available: i32,
}
```

### 库存操作追踪

```rust
pub struct InventoryService {
    db_pool: sqlx::PgPool,
    redis_client: redis::Client,
}

impl InventoryService {
    #[instrument(name = "inventory.check_stock", skip(self))]
    pub async fn check_stock(
        &self,
        product_id: Uuid,
        required_quantity: i32,
    ) -> Result<bool, InventoryError> {
        let available = self.get_available_stock(product_id).await?;
        
        if available >= required_quantity {
            info!(product_id = %product_id, available = available, "Stock sufficient");
            Ok(true)
        } else {
            warn!(product_id = %product_id, available = available, required = required_quantity, "Insufficient stock");
            Err(InventoryError::InsufficientStock)
        }
    }
    
    #[instrument(name = "inventory.decrease", skip(self))]
    pub async fn decrease_stock(
        &self,
        product_id: Uuid,
        quantity: i32,
    ) -> Result<(), InventoryError> {
        sqlx::query(
            "UPDATE inventory SET quantity = quantity - $1, reserved = reserved + $2 WHERE product_id = $3"
        )
        .bind(quantity)
        .bind(quantity)
        .bind(product_id)
        .execute(&self.db_pool)
        .await?;
        
        // 清除缓存
        self.invalidate_cache(product_id).await?;
        
        info!(product_id = %product_id, quantity = quantity, "Stock decreased");
        Ok(())
    }
}
```

---

## 5. 购物车服务

### 购物车模型

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Cart {
    pub user_id: Uuid,
    pub items: Vec<CartItem>,
    pub updated_at: chrono::DateTime<chrono::Utc>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CartItem {
    pub product_id: Uuid,
    pub quantity: i32,
    pub price: rust_decimal::Decimal,
}
```

### 购物车操作追踪

```rust
pub struct CartService {
    redis_client: redis::Client,
}

impl CartService {
    #[instrument(name = "cart.add_item", skip(self, item))]
    pub async fn add_item(
        &self,
        user_id: Uuid,
        item: CartItem,
    ) -> Result<Cart, CartError> {
        let mut conn = self.redis_client.get_connection_manager().await?;
        let key = format!("cart:{}", user_id);
        
        // 获取现有购物车
        let mut cart = self.get_cart_internal(&mut conn, &key).await?
            .unwrap_or_else(|| Cart {
                user_id,
                items: Vec::new(),
                updated_at: chrono::Utc::now(),
            });
        
        // 添加商品
        if let Some(existing) = cart.items.iter_mut().find(|i| i.product_id == item.product_id) {
            existing.quantity += item.quantity;
        } else {
            cart.items.push(item);
        }
        
        cart.updated_at = chrono::Utc::now();
        
        // 保存到 Redis
        let cart_json = serde_json::to_string(&cart)?;
        redis::cmd("SET")
            .arg(&key)
            .arg(&cart_json)
            .arg("EX")
            .arg(86400) // 24小时过期
            .query_async(&mut conn)
            .await?;
        
        info!(user_id = %user_id, "Item added to cart");
        Ok(cart)
    }
    
    #[instrument(name = "cart.get", skip(self))]
    pub async fn get_cart(&self, user_id: Uuid) -> Result<Option<Cart>, CartError> {
        let mut conn = self.redis_client.get_connection_manager().await?;
        let key = format!("cart:{}", user_id);
        
        self.get_cart_internal(&mut conn, &key).await
    }
    
    async fn get_cart_internal(
        &self,
        conn: &mut redis::aio::ConnectionManager,
        key: &str,
    ) -> Result<Option<Cart>, CartError> {
        let data: Option<String> = redis::cmd("GET")
            .arg(key)
            .query_async(conn)
            .await?;
        
        match data {
            Some(json) => {
                let cart = serde_json::from_str(&json)?;
                Ok(Some(cart))
            }
            None => Ok(None),
        }
    }
}
```

---

## 6. 支付服务

### 支付模型

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Payment {
    pub id: Uuid,
    pub order_id: Uuid,
    pub amount: rust_decimal::Decimal,
    pub status: PaymentStatus,
    pub payment_method: PaymentMethod,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PaymentStatus {
    Pending,
    Processing,
    Success,
    Failed,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PaymentMethod {
    Alipay,
    WeChatPay,
    CreditCard,
}
```

### 支付处理追踪

```rust
pub struct PaymentService {
    db_pool: sqlx::PgPool,
    http_client: reqwest::Client,
}

impl PaymentService {
    #[instrument(
        name = "payment.process",
        skip(self, request),
        fields(order_id = %request.order_id, amount = %request.amount)
    )]
    pub async fn process_payment(&self, request: PaymentRequest) -> Result<Payment, PaymentError> {
        info!("Processing payment");
        
        // 创建支付记录
        let payment_id = Uuid::new_v4();
        sqlx::query(
            r#"
            INSERT INTO payments (id, order_id, amount, status, payment_method, created_at)
            VALUES ($1, $2, $3, $4, $5, $6)
            "#
        )
        .bind(payment_id)
        .bind(request.order_id)
        .bind(request.amount)
        .bind("pending")
        .bind(format!("{:?}", request.payment_method))
        .bind(chrono::Utc::now())
        .execute(&self.db_pool)
        .await?;
        
        // 调用第三方支付
        let external_payment_id = self.call_payment_gateway(&request).await?;
        
        info!(
            payment_id = %payment_id,
            external_payment_id = %external_payment_id,
            "Payment initiated"
        );
        
        Ok(Payment {
            id: payment_id,
            order_id: request.order_id,
            amount: request.amount,
            status: PaymentStatus::Processing,
            payment_method: request.payment_method,
            created_at: chrono::Utc::now(),
        })
    }
    
    #[instrument(skip(self, request))]
    async fn call_payment_gateway(&self, request: &PaymentRequest) -> Result<String, PaymentError> {
        // 调用第三方支付接口
        let response = self.http_client
            .post("https://payment-gateway.example.com/api/pay")
            .json(&request)
            .send()
            .await?;
        
        let payment_id = response.text().await?;
        Ok(payment_id)
    }
}
```

---

## 7. 物流服务

### 物流模型

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Shipment {
    pub id: Uuid,
    pub order_id: Uuid,
    pub tracking_number: String,
    pub carrier: String,
    pub status: ShipmentStatus,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ShipmentStatus {
    Pending,
    PickedUp,
    InTransit,
    OutForDelivery,
    Delivered,
}
```

### 物流追踪

```rust
pub struct ShipmentService {
    db_pool: sqlx::PgPool,
    kafka_producer: Arc<rdkafka::producer::FutureProducer>,
}

impl ShipmentService {
    #[instrument(name = "shipment.create", skip(self, request))]
    pub async fn create_shipment(&self, request: CreateShipmentRequest) -> Result<Shipment, ShipmentError> {
        let tracking_number = self.generate_tracking_number();
        let shipment_id = Uuid::new_v4();
        
        sqlx::query(
            r#"
            INSERT INTO shipments (id, order_id, tracking_number, carrier, status, created_at)
            VALUES ($1, $2, $3, $4, $5, $6)
            "#
        )
        .bind(shipment_id)
        .bind(request.order_id)
        .bind(&tracking_number)
        .bind(&request.carrier)
        .bind("pending")
        .bind(chrono::Utc::now())
        .execute(&self.db_pool)
        .await?;
        
        // 发送物流创建事件
        self.publish_shipment_created_event(shipment_id).await?;
        
        info!(shipment_id = %shipment_id, tracking_number = %tracking_number, "Shipment created");
        
        Ok(Shipment {
            id: shipment_id,
            order_id: request.order_id,
            tracking_number,
            carrier: request.carrier,
            status: ShipmentStatus::Pending,
            created_at: chrono::Utc::now(),
        })
    }
    
    fn generate_tracking_number(&self) -> String {
        format!("SF{}", uuid::Uuid::new_v4().simple())
    }
}
```

---

## 8. 推荐服务

### 推荐引擎追踪

```rust
pub struct RecommendationService {
    http_client: reqwest::Client,
    redis_client: redis::Client,
}

impl RecommendationService {
    #[instrument(name = "recommendation.get", skip(self))]
    pub async fn get_recommendations(
        &self,
        user_id: Uuid,
        limit: usize,
    ) -> Result<Vec<Product>, RecommendationError> {
        // 先查缓存
        if let Some(products) = self.get_cached_recommendations(user_id).await? {
            info!("Recommendations from cache");
            return Ok(products);
        }
        
        // 调用推荐算法服务
        let products = self.fetch_recommendations_from_ml_service(user_id, limit).await?;
        
        // 缓存结果
        self.cache_recommendations(user_id, &products).await?;
        
        info!(user_id = %user_id, count = products.len(), "Recommendations generated");
        Ok(products)
    }
    
    #[instrument(skip(self))]
    async fn fetch_recommendations_from_ml_service(
        &self,
        user_id: Uuid,
        limit: usize,
    ) -> Result<Vec<Product>, RecommendationError> {
        let response = self.http_client
            .get(format!("http://ml-service/recommend?user_id={}&limit={}", user_id, limit))
            .send()
            .await?;
        
        let products = response.json().await?;
        Ok(products)
    }
}
```

---

## 9. 搜索服务

### Elasticsearch 集成

```rust
pub struct SearchService {
    es_client: elasticsearch::Elasticsearch,
}

impl SearchService {
    #[instrument(name = "search.query", skip(self))]
    pub async fn search_products(&self, query: &str) -> Result<Vec<Product>, SearchError> {
        let response = self.es_client
            .search(elasticsearch::SearchParts::Index(&["products"]))
            .body(serde_json::json!({
                "query": {
                    "multi_match": {
                        "query": query,
                        "fields": ["name^3", "description", "category"]
                    }
                }
            }))
            .send()
            .await?;
        
        let body = response.json::<serde_json::Value>().await?;
        let hits = body["hits"]["hits"].as_array().unwrap();
        
        let products: Vec<Product> = hits
            .iter()
            .filter_map(|hit| serde_json::from_value(hit["_source"].clone()).ok())
            .collect();
        
        info!(query = query, results = products.len(), "Search completed");
        Ok(products)
    }
}
```

---

## 10. 分布式追踪实战

### 完整下单流程追踪

```rust
use opentelemetry::global;
use opentelemetry::trace::{TraceContextExt, Tracer};

/// 完整下单流程
#[instrument(name = "checkout.complete", skip(services))]
pub async fn complete_checkout(
    services: Arc<ServiceRegistry>,
    user_id: Uuid,
    cart_id: Uuid,
) -> Result<Order, CheckoutError> {
    let tracer = global::tracer("ecommerce");
    
    // 步骤 1: 获取购物车
    let cart = services.cart_service.get_cart(user_id).await?
        .ok_or(CheckoutError::CartNotFound)?;
    
    // 步骤 2: 验证库存
    for item in &cart.items {
        services.inventory_service
            .check_stock(item.product_id, item.quantity)
            .await?;
    }
    
    // 步骤 3: 创建订单
    let order = services.order_service
        .create_order(CreateOrderRequest {
            user_id,
            items: cart.items.clone(),
        })
        .await?;
    
    // 步骤 4: 处理支付
    let payment = services.payment_service
        .process_payment(PaymentRequest {
            order_id: order.id,
            amount: order.total_amount,
            payment_method: PaymentMethod::Alipay,
        })
        .await?;
    
    // 步骤 5: 创建物流
    let shipment = services.shipment_service
        .create_shipment(CreateShipmentRequest {
            order_id: order.id,
            carrier: "SF Express".to_string(),
        })
        .await?;
    
    // 步骤 6: 清空购物车
    services.cart_service.clear_cart(user_id).await?;
    
    info!(
        order_id = %order.id,
        payment_id = %payment.id,
        shipment_id = %shipment.id,
        "Checkout completed successfully"
    );
    
    Ok(order)
}
```

---

## 11. 性能优化

### 缓存策略

```rust
// ✅ 推荐：多级缓存
#[instrument(skip(self))]
pub async fn get_product_optimized(&self, product_id: Uuid) -> Result<Product, ProductError> {
    // L1: 本地内存缓存
    if let Some(product) = self.local_cache.get(&product_id) {
        return Ok(product);
    }
    
    // L2: Redis 缓存
    if let Some(product) = self.get_from_redis(product_id).await? {
        self.local_cache.insert(product_id, product.clone());
        return Ok(product);
    }
    
    // L3: 数据库
    let product = self.query_from_db(product_id).await?;
    self.set_to_redis(&product).await?;
    self.local_cache.insert(product_id, product.clone());
    
    Ok(product)
}
```

### 批量操作

```rust
// ✅ 推荐：批量查询减少 RT
#[instrument(skip(self, product_ids))]
pub async fn get_products_batch(
    &self,
    product_ids: &[Uuid],
) -> Result<Vec<Product>, ProductError> {
    let placeholders: Vec<String> = (1..=product_ids.len())
        .map(|i| format!("${}", i))
        .collect();
    
    let query = format!(
        "SELECT * FROM products WHERE id IN ({})",
        placeholders.join(", ")
    );
    
    let mut query_builder = sqlx::query_as::<_, Product>(&query);
    for id in product_ids {
        query_builder = query_builder.bind(id);
    }
    
    let products = query_builder.fetch_all(&self.db_pool).await?;
    Ok(products)
}
```

---

## 12. 完整示例

### main.rs

```rust
use axum::{Router, routing::post};
use tower_http::trace::TraceLayer;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化追踪
    init_tracer()?;
    
    // 初始化服务
    let db_pool = init_db_pool().await?;
    let redis_client = redis::Client::open("redis://localhost:6379")?;
    let kafka_producer = Arc::new(init_kafka_producer()?);
    
    let services = Arc::new(ServiceRegistry {
        user_service: Arc::new(UserService { db_pool: db_pool.clone(), redis_client: redis_client.clone() }),
        product_service: Arc::new(ProductService { db_pool: db_pool.clone(), redis_client: redis_client.clone() }),
        order_service: Arc::new(OrderService { /* ... */ }),
        // ... 其他服务
    });
    
    // 构建路由
    let app = Router::new()
        .route("/api/users/login", post(login_handler))
        .route("/api/products/:id", get(get_product_handler))
        .route("/api/orders", post(create_order_handler))
        .route("/api/cart/add", post(add_to_cart_handler))
        .route("/api/checkout", post(checkout_handler))
        .layer(TraceLayer::new_for_http())
        .with_state(services);
    
    // 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:8080").await?;
    axum::serve(listener, app).await?;
    
    Ok(())
}
```

---

## 总结

本文档展示了电商平台分布式追踪的完整实现：

1. ✅ **微服务架构**: 9大核心服务完整追踪
2. ✅ **分布式事务**: 下单流程全链路追踪
3. ✅ **性能优化**: 多级缓存、批量操作
4. ✅ **异步消息**: Kafka 事件驱动
5. ✅ **搜索服务**: Elasticsearch 集成
6. ✅ **实时监控**: 关键指标采集

通过本案例，您可以构建生产级电商平台可观测性系统。

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-08  
**维护者**: OTLP Rust Team  
**许可证**: MIT OR Apache-2.0
