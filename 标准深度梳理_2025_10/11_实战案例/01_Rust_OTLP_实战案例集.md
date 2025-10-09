# Rust OTLP 实战案例集

## 目录

- [Rust OTLP 实战案例集](#rust-otlp-实战案例集)
  - [目录](#目录)
  - [1. 电商系统](#1-电商系统)
    - [1.1 商品浏览](#11-商品浏览)
    - [1.2 购物车](#12-购物车)
    - [1.3 下单流程](#13-下单流程)
    - [1.4 支付处理](#14-支付处理)
  - [2. 金融系统](#2-金融系统)
    - [2.1 账户查询](#21-账户查询)
    - [2.2 转账交易](#22-转账交易)
    - [2.3 风控系统](#23-风控系统)
  - [3. 社交平台](#3-社交平台)
    - [3.1 动态发布](#31-动态发布)
  - [4. 视频平台](#4-视频平台)
    - [4.1 视频上传](#41-视频上传)
  - [5. IoT 系统](#5-iot-系统)
    - [5.1 设备数据采集](#51-设备数据采集)
  - [总结](#总结)
    - [设计模式总结](#设计模式总结)
    - [最佳实践总结](#最佳实践总结)

---

## 1. 电商系统

### 1.1 商品浏览

````rust
use axum::{Json, extract::Path};
use tracing::instrument;
use serde::{Serialize, Deserialize};

#[derive(Serialize)]
pub struct Product {
    pub id: String,
    pub name: String,
    pub price: f64,
    pub stock: i32,
}

/// 商品详情查询
#[instrument(
    name = "product.view",
    skip(db, cache),
    fields(
        product_id = %product_id,
        cache_hit = tracing::field::Empty,
        db_query_time_ms = tracing::field::Empty,
    )
)]
pub async fn view_product(
    Path(product_id): Path<String>,
    db: DatabasePool,
    cache: RedisClient,
) -> Result<Json<Product>, AppError> {
    let span = tracing::Span::current();
    
    // 1. 尝试缓存
    if let Some(product) = cache.get::<Product>(&product_id).await? {
        span.record("cache_hit", true);
        
        // 记录浏览指标
        metrics::counter!("product.views", "source" => "cache").increment(1);
        
        return Ok(Json(product));
    }
    span.record("cache_hit", false);
    
    // 2. 数据库查询
    let start = std::time::Instant::now();
    let product = sqlx::query_as!(
        Product,
        "SELECT id, name, price, stock FROM products WHERE id = $1",
        product_id
    )
    .fetch_one(&db)
    .await?;
    
    let query_time = start.elapsed().as_millis();
    span.record("db_query_time_ms", query_time as u64);
    
    // 3. 写入缓存
    cache.set(&product_id, &product, 3600).await?;
    
    // 4. 异步更新浏览量
    tokio::spawn(
        async move {
            increment_view_count(&db, &product_id).await;
        }
        .instrument(tracing::info_span!("product.increment_views"))
    );
    
    metrics::counter!("product.views", "source" => "database").increment(1);
    
    Ok(Json(product))
}

#[instrument(name = "product.increment_views", skip(db))]
async fn increment_view_count(db: &DatabasePool, product_id: &str) {
    let _ = sqlx::query!(
        "UPDATE products SET view_count = view_count + 1 WHERE id = $1",
        product_id
    )
    .execute(db)
    .await;
}
````

**Trace 示例**:

````text
product.view (105ms)
├─ cache.get (5ms) [cache_hit=false]
├─ db.query (80ms) [rows=1]
├─ cache.set (10ms)
└─ product.increment_views (10ms) [async]
````

---

### 1.2 购物车

````rust
#[derive(Serialize, Deserialize)]
pub struct CartItem {
    pub product_id: String,
    pub quantity: i32,
}

#[derive(Serialize, Deserialize)]
pub struct Cart {
    pub user_id: String,
    pub items: Vec<CartItem>,
    pub total: f64,
}

/// 添加到购物车
#[instrument(
    name = "cart.add_item",
    skip(cache, db),
    fields(
        user_id = %user_id,
        product_id = %item.product_id,
        quantity = item.quantity,
    )
)]
pub async fn add_to_cart(
    user_id: String,
    item: CartItem,
    cache: RedisClient,
    db: DatabasePool,
) -> Result<Json<Cart>, AppError> {
    // 1. 验证商品库存
    let stock = check_stock(&db, &item.product_id, item.quantity).await?;
    if !stock.available {
        return Err(AppError::OutOfStock);
    }
    
    // 2. 获取购物车
    let mut cart = get_or_create_cart(&cache, &user_id).await?;
    
    // 3. 更新购物车
    if let Some(existing) = cart.items.iter_mut()
        .find(|i| i.product_id == item.product_id)
    {
        existing.quantity += item.quantity;
    } else {
        cart.items.push(item);
    }
    
    // 4. 重新计算总价
    cart.total = calculate_cart_total(&db, &cart.items).await?;
    
    // 5. 保存购物车
    save_cart(&cache, &user_id, &cart).await?;
    
    // 6. 记录指标
    metrics::counter!("cart.items_added").increment(1);
    metrics::gauge!("cart.size", "user_id" => user_id.clone())
        .set(cart.items.len() as f64);
    
    Ok(Json(cart))
}

#[instrument(name = "cart.calculate_total", skip(db, items))]
async fn calculate_cart_total(
    db: &DatabasePool,
    items: &[CartItem],
) -> Result<f64, AppError> {
    let product_ids: Vec<&str> = items.iter()
        .map(|i| i.product_id.as_str())
        .collect();
    
    let prices = sqlx::query!(
        "SELECT id, price FROM products WHERE id = ANY($1)",
        &product_ids
    )
    .fetch_all(db)
    .await?;
    
    let total = items.iter()
        .filter_map(|item| {
            prices.iter()
                .find(|p| p.id == item.product_id)
                .map(|p| p.price * item.quantity as f64)
        })
        .sum();
    
    Ok(total)
}
````

---

### 1.3 下单流程

````rust
#[derive(Deserialize)]
pub struct OrderRequest {
    pub user_id: String,
    pub items: Vec<CartItem>,
    pub payment_method: String,
    pub shipping_address: String,
}

#[derive(Serialize)]
pub struct Order {
    pub id: String,
    pub user_id: String,
    pub total: f64,
    pub status: String,
    pub created_at: DateTime<Utc>,
}

/// 创建订单 (完整流程)
#[instrument(
    name = "order.create",
    skip(req, services),
    fields(
        user_id = %req.user_id,
        item_count = req.items.len(),
        order_id = tracing::field::Empty,
        order_status = tracing::field::Empty,
    )
)]
pub async fn create_order(
    req: OrderRequest,
    services: Arc<Services>,
) -> Result<Json<Order>, AppError> {
    let span = tracing::Span::current();
    
    // 1. 开始分布式事务
    let mut tx = services.db.begin().await?;
    
    // 2. 验证用户
    let user = validate_user(&tx, &req.user_id).await?;
    
    // 3. 验证商品和库存
    let items_validation = validate_items(&tx, &req.items).await?;
    if !items_validation.all_available {
        return Err(AppError::StockInsufficient);
    }
    
    // 4. 计算总价（含优惠）
    let pricing = calculate_pricing(&tx, &user, &req.items).await?;
    
    // 5. 创建订单记录
    let order_id = Uuid::new_v4().to_string();
    span.record("order_id", &order_id);
    
    let order = sqlx::query_as!(
        Order,
        r#"
        INSERT INTO orders (id, user_id, total, status, created_at)
        VALUES ($1, $2, $3, 'pending', NOW())
        RETURNING *
        "#,
        order_id,
        req.user_id,
        pricing.total
    )
    .fetch_one(&mut *tx)
    .await?;
    
    // 6. 创建订单明细
    for item in &req.items {
        create_order_item(&mut tx, &order_id, item).await?;
    }
    
    // 7. 预留库存
    reserve_inventory(&mut tx, &req.items).await?;
    
    // 8. 提交事务
    tx.commit().await?;
    
    span.record("order_status", "created");
    
    // 9. 异步处理（不阻塞响应）
    let order_clone = order.clone();
    let services_clone = services.clone();
    tokio::spawn(
        async move {
            // 9.1 处理支付
            if let Err(e) = process_payment_async(&services_clone, &order_clone).await {
                handle_payment_failure(&services_clone, &order_clone, e).await;
                return;
            }
            
            // 9.2 发送通知
            let _ = send_order_notification(&services_clone, &order_clone).await;
            
            // 9.3 清空购物车
            let _ = clear_cart(&services_clone.cache, &order_clone.user_id).await;
        }
        .instrument(tracing::info_span!("order.async_processing"))
    );
    
    // 10. 记录指标
    metrics::counter!("orders.created").increment(1);
    metrics::histogram!("orders.total_amount").record(pricing.total);
    
    Ok(Json(order))
}

#[instrument(name = "order.validate_items", skip(tx, items))]
async fn validate_items(
    tx: &mut Transaction<'_, Postgres>,
    items: &[CartItem],
) -> Result<ItemsValidation, AppError> {
    let product_ids: Vec<&str> = items.iter()
        .map(|i| i.product_id.as_str())
        .collect();
    
    let products = sqlx::query!(
        "SELECT id, stock FROM products WHERE id = ANY($1) FOR UPDATE",
        &product_ids
    )
    .fetch_all(&mut **tx)
    .await?;
    
    let all_available = items.iter().all(|item| {
        products.iter()
            .find(|p| p.id == item.product_id)
            .map(|p| p.stock >= item.quantity)
            .unwrap_or(false)
    });
    
    Ok(ItemsValidation { all_available })
}

#[instrument(name = "inventory.reserve", skip(tx, items))]
async fn reserve_inventory(
    tx: &mut Transaction<'_, Postgres>,
    items: &[CartItem],
) -> Result<(), AppError> {
    for item in items {
        sqlx::query!(
            "UPDATE products SET stock = stock - $1 WHERE id = $2",
            item.quantity,
            item.product_id
        )
        .execute(&mut **tx)
        .await?;
        
        // 记录库存变更
        sqlx::query!(
            r#"
            INSERT INTO inventory_logs (product_id, quantity, operation, created_at)
            VALUES ($1, $2, 'reserve', NOW())
            "#,
            item.product_id,
            item.quantity
        )
        .execute(&mut **tx)
        .await?;
    }
    
    Ok(())
}
````

**完整 Trace 示例**:

````text
order.create (850ms)
├─ db.begin_transaction (5ms)
├─ user.validate (20ms)
├─ order.validate_items (150ms)
│  └─ db.query [FOR UPDATE] (140ms)
├─ pricing.calculate (80ms)
│  ├─ coupon.validate (30ms)
│  └─ discount.calculate (40ms)
├─ db.insert_order (15ms)
├─ order_items.create (30ms)
├─ inventory.reserve (120ms)
│  └─ db.update [stock] (110ms)
├─ db.commit (20ms)
└─ order.async_processing (400ms) [detached]
   ├─ payment.process (200ms)
   │  └─ external_api.call (180ms)
   ├─ notification.send (100ms)
   └─ cart.clear (10ms)
````

---

### 1.4 支付处理

````rust
#[derive(Serialize, Deserialize)]
pub struct PaymentRequest {
    pub order_id: String,
    pub method: String,  // credit_card, alipay, wechat
    pub amount: f64,
}

#[derive(Serialize)]
pub struct PaymentResult {
    pub payment_id: String,
    pub status: String,
    pub transaction_id: Option<String>,
}

/// 支付处理（含重试和降级）
#[instrument(
    name = "payment.process",
    skip(req, services),
    fields(
        order_id = %req.order_id,
        method = %req.method,
        amount = req.amount,
        payment_status = tracing::field::Empty,
        retry_count = tracing::field::Empty,
    )
)]
pub async fn process_payment(
    req: PaymentRequest,
    services: Arc<Services>,
) -> Result<Json<PaymentResult>, AppError> {
    let span = tracing::Span::current();
    
    // 1. 幂等性检查
    if let Some(existing) = check_existing_payment(&services.db, &req.order_id).await? {
        span.record("payment_status", "duplicate");
        return Ok(Json(existing));
    }
    
    // 2. 风控检查
    let risk_score = assess_risk(&services, &req).await?;
    if risk_score > 0.8 {
        span.record("payment_status", "rejected_high_risk");
        return Err(AppError::PaymentRejected("High risk".into()));
    }
    
    // 3. 调用支付网关（带重试）
    let mut retry_count = 0;
    let payment_result = loop {
        retry_count += 1;
        span.record("retry_count", retry_count);
        
        match call_payment_gateway(&services, &req).await {
            Ok(result) => break result,
            Err(e) if retry_count < 3 && e.is_retriable() => {
                // 指数退避
                tokio::time::sleep(Duration::from_millis(100 * 2_u64.pow(retry_count))).await;
                continue;
            }
            Err(e) => {
                span.record("payment_status", "failed");
                
                // 降级处理：标记为待处理
                mark_payment_pending(&services.db, &req.order_id).await?;
                
                return Err(e.into());
            }
        }
    };
    
    // 4. 保存支付记录
    let payment = save_payment_record(&services.db, &req, &payment_result).await?;
    
    // 5. 更新订单状态
    update_order_status(&services.db, &req.order_id, "paid").await?;
    
    span.record("payment_status", "success");
    
    // 6. 记录指标
    metrics::counter!("payments.processed", "method" => req.method.clone()).increment(1);
    metrics::histogram!("payments.amount").record(req.amount);
    
    Ok(Json(payment))
}

#[instrument(name = "payment.risk_assessment", skip(services, req))]
async fn assess_risk(
    services: &Services,
    req: &PaymentRequest,
) -> Result<f64, AppError> {
    // 并行风控检查
    let (user_risk, device_risk, behavior_risk) = tokio::join!(
        check_user_risk(&services.db, &req.order_id),
        check_device_risk(&services.redis, &req.order_id),
        check_behavior_risk(&services.ml_service, &req.order_id),
    );
    
    // 综合风险评分
    let risk_score = (
        user_risk? * 0.4 +
        device_risk? * 0.3 +
        behavior_risk? * 0.3
    );
    
    Ok(risk_score)
}

#[instrument(name = "payment.gateway_call", skip(services, req), err)]
async fn call_payment_gateway(
    services: &Services,
    req: &PaymentRequest,
) -> Result<GatewayResponse, PaymentError> {
    let client = &services.http_client;
    
    // 构建请求
    let gateway_req = GatewayRequest {
        merchant_id: services.config.merchant_id.clone(),
        order_id: req.order_id.clone(),
        amount: req.amount,
        timestamp: Utc::now().timestamp(),
    };
    
    // 签名
    let signature = sign_request(&gateway_req, &services.config.secret_key);
    
    // 调用网关（带超时）
    let response = client
        .post(&services.config.payment_gateway_url)
        .json(&gateway_req)
        .header("X-Signature", signature)
        .timeout(Duration::from_secs(10))
        .send()
        .await
        .map_err(|e| PaymentError::NetworkError(e.to_string()))?;
    
    if !response.status().is_success() {
        return Err(PaymentError::GatewayError(response.status().as_u16()));
    }
    
    let gateway_response: GatewayResponse = response.json().await?;
    
    Ok(gateway_response)
}
````

---

## 2. 金融系统

### 2.1 账户查询

````rust
#[derive(Serialize)]
pub struct Account {
    pub id: String,
    pub user_id: String,
    pub balance: f64,
    pub currency: String,
    pub status: String,
}

/// 账户查询（多级缓存）
#[instrument(
    name = "account.query",
    skip(services),
    fields(
        account_id = %account_id,
        cache_level = tracing::field::Empty,
    )
)]
pub async fn query_account(
    account_id: String,
    services: Arc<Services>,
) -> Result<Json<Account>, AppError> {
    let span = tracing::Span::current();
    
    // L1: 本地缓存 (内存)
    if let Some(account) = services.local_cache.get(&account_id) {
        span.record("cache_level", "L1");
        return Ok(Json(account));
    }
    
    // L2: Redis 缓存
    if let Some(account) = services.redis.get::<Account>(&account_id).await? {
        span.record("cache_level", "L2");
        
        // 回填 L1
        services.local_cache.insert(account_id.clone(), account.clone());
        
        return Ok(Json(account));
    }
    
    // L3: 数据库
    let account = sqlx::query_as!(
        Account,
        "SELECT * FROM accounts WHERE id = $1",
        account_id
    )
    .fetch_one(&services.db)
    .await?;
    
    span.record("cache_level", "L3");
    
    // 回填缓存
    services.redis.set(&account_id, &account, 300).await?;
    services.local_cache.insert(account_id, account.clone());
    
    Ok(Json(account))
}
````

---

### 2.2 转账交易

````rust
#[derive(Deserialize)]
pub struct TransferRequest {
    pub from_account: String,
    pub to_account: String,
    pub amount: f64,
    pub currency: String,
    pub note: String,
}

#[derive(Serialize)]
pub struct TransferResult {
    pub transaction_id: String,
    pub status: String,
    pub timestamp: DateTime<Utc>,
}

/// 转账交易（ACID保证）
#[instrument(
    name = "transfer.execute",
    skip(req, services),
    fields(
        from_account = %req.from_account,
        to_account = %req.to_account,
        amount = req.amount,
        transaction_id = tracing::field::Empty,
    )
)]
pub async fn execute_transfer(
    req: TransferRequest,
    services: Arc<Services>,
) -> Result<Json<TransferResult>, AppError> {
    let span = tracing::Span::current();
    
    let transaction_id = Uuid::new_v4().to_string();
    span.record("transaction_id", &transaction_id);
    
    // 开始分布式锁（防止并发转账）
    let lock_key = format!("lock:transfer:{}", req.from_account);
    let _lock = services.redis.acquire_lock(&lock_key, 30).await?;
    
    // 开始数据库事务
    let mut tx = services.db.begin().await?;
    
    // 1. 锁定账户（FOR UPDATE）
    let from_account = sqlx::query_as!(
        Account,
        "SELECT * FROM accounts WHERE id = $1 FOR UPDATE",
        req.from_account
    )
    .fetch_one(&mut *tx)
    .await?;
    
    let to_account = sqlx::query_as!(
        Account,
        "SELECT * FROM accounts WHERE id = $1 FOR UPDATE",
        req.to_account
    )
    .fetch_one(&mut *tx)
    .await?;
    
    // 2. 余额检查
    if from_account.balance < req.amount {
        return Err(AppError::InsufficientBalance);
    }
    
    // 3. 扣款
    sqlx::query!(
        "UPDATE accounts SET balance = balance - $1 WHERE id = $2",
        req.amount,
        req.from_account
    )
    .execute(&mut *tx)
    .await?;
    
    // 4. 入账
    sqlx::query!(
        "UPDATE accounts SET balance = balance + $1 WHERE id = $2",
        req.amount,
        req.to_account
    )
    .execute(&mut *tx)
    .await?;
    
    // 5. 记录交易
    sqlx::query!(
        r#"
        INSERT INTO transactions 
        (id, from_account, to_account, amount, status, created_at)
        VALUES ($1, $2, $3, $4, 'completed', NOW())
        "#,
        transaction_id,
        req.from_account,
        req.to_account,
        req.amount
    )
    .execute(&mut *tx)
    .await?;
    
    // 6. 提交事务
    tx.commit().await?;
    
    // 7. 清除缓存
    services.redis.del(&req.from_account).await?;
    services.redis.del(&req.to_account).await?;
    
    // 8. 异步通知
    tokio::spawn(
        async move {
            notify_transfer_completed(&services, &transaction_id).await;
        }
        .instrument(tracing::info_span!("transfer.notify"))
    );
    
    // 9. 记录指标
    metrics::counter!("transfers.completed").increment(1);
    metrics::histogram!("transfers.amount").record(req.amount);
    
    Ok(Json(TransferResult {
        transaction_id,
        status: "completed".into(),
        timestamp: Utc::now(),
    }))
}
````

---

### 2.3 风控系统

````rust
#[derive(Serialize)]
pub struct RiskAssessment {
    pub risk_score: f64,
    pub risk_level: String,  // low, medium, high
    pub factors: Vec<RiskFactor>,
}

#[derive(Serialize)]
pub struct RiskFactor {
    pub name: String,
    pub score: f64,
    pub weight: f64,
}

/// 风险评估（实时）
#[instrument(
    name = "risk.assess",
    skip(services),
    fields(
        transaction_id = %transaction_id,
        risk_score = tracing::field::Empty,
        risk_level = tracing::field::Empty,
    )
)]
pub async fn assess_risk(
    transaction_id: String,
    services: Arc<Services>,
) -> Result<Json<RiskAssessment>, AppError> {
    let span = tracing::Span::current();
    
    // 并行检查多个风险维度
    let (
        user_history,
        device_fingerprint,
        location_analysis,
        behavior_pattern,
        ml_prediction,
    ) = tokio::join!(
        check_user_history(&services, &transaction_id),
        check_device_fingerprint(&services, &transaction_id),
        analyze_location(&services, &transaction_id),
        analyze_behavior_pattern(&services, &transaction_id),
        ml_risk_prediction(&services, &transaction_id),
    );
    
    // 计算综合风险分
    let factors = vec![
        RiskFactor {
            name: "user_history".into(),
            score: user_history?,
            weight: 0.2,
        },
        RiskFactor {
            name: "device_fingerprint".into(),
            score: device_fingerprint?,
            weight: 0.15,
        },
        RiskFactor {
            name: "location".into(),
            score: location_analysis?,
            weight: 0.15,
        },
        RiskFactor {
            name: "behavior".into(),
            score: behavior_pattern?,
            weight: 0.2,
        },
        RiskFactor {
            name: "ml_prediction".into(),
            score: ml_prediction?,
            weight: 0.3,
        },
    ];
    
    let risk_score: f64 = factors.iter()
        .map(|f| f.score * f.weight)
        .sum();
    
    let risk_level = match risk_score {
        s if s < 0.3 => "low",
        s if s < 0.7 => "medium",
        _ => "high",
    };
    
    span.record("risk_score", risk_score);
    span.record("risk_level", risk_level);
    
    // 高风险交易告警
    if risk_level == "high" {
        alert_high_risk(&services, &transaction_id, risk_score).await?;
    }
    
    Ok(Json(RiskAssessment {
        risk_score,
        risk_level: risk_level.into(),
        factors,
    }))
}

#[instrument(name = "risk.ml_prediction", skip(services))]
async fn ml_risk_prediction(
    services: &Services,
    transaction_id: &str,
) -> Result<f64, AppError> {
    // 调用机器学习服务
    let features = extract_features(services, transaction_id).await?;
    
    let response = services.http_client
        .post(&services.config.ml_service_url)
        .json(&features)
        .timeout(Duration::from_millis(500))
        .send()
        .await?;
    
    let prediction: MlPrediction = response.json().await?;
    
    Ok(prediction.risk_score)
}
````

---

## 3. 社交平台

### 3.1 动态发布

````rust
#[derive(Deserialize)]
pub struct PostRequest {
    pub user_id: String,
    pub content: String,
    pub images: Vec<String>,
    pub visibility: String,  // public, friends, private
}

#[derive(Serialize)]
pub struct Post {
    pub id: String,
    pub user_id: String,
    pub content: String,
    pub images: Vec<String>,
    pub created_at: DateTime<Utc>,
}

/// 发布动态（含图片上传、内容审核）
#[instrument(
    name = "post.create",
    skip(req, services),
    fields(
        user_id = %req.user_id,
        image_count = req.images.len(),
        post_id = tracing::field::Empty,
    )
)]
pub async fn create_post(
    req: PostRequest,
    services: Arc<Services>,
) -> Result<Json<Post>, AppError> {
    let span = tracing::Span::current();
    
    let post_id = Uuid::new_v4().to_string();
    span.record("post_id", &post_id);
    
    // 1. 内容审核
    let moderation_result = moderate_content(&services, &req.content).await?;
    if !moderation_result.approved {
        return Err(AppError::ContentViolation(moderation_result.reason));
    }
    
    // 2. 处理图片（并行）
    let image_futures = req.images.iter()
        .map(|img_url| process_image(&services, img_url));
    
    let processed_images = futures::future::try_join_all(image_futures).await?;
    
    // 3. 保存动态
    let post = sqlx::query_as!(
        Post,
        r#"
        INSERT INTO posts (id, user_id, content, images, visibility, created_at)
        VALUES ($1, $2, $3, $4, $5, NOW())
        RETURNING *
        "#,
        post_id,
        req.user_id,
        req.content,
        &processed_images,
        req.visibility
    )
    .fetch_one(&services.db)
    .await?;
    
    // 4. 异步处理（不阻塞响应）
    let post_clone = post.clone();
    let services_clone = services.clone();
    tokio::spawn(
        async move {
            // 4.1 推送到粉丝 timeline
            push_to_followers(&services_clone, &post_clone).await;
            
            // 4.2 更新搜索索引
            update_search_index(&services_clone, &post_clone).await;
            
            // 4.3 触发推荐系统
            trigger_recommendation(&services_clone, &post_clone).await;
        }
        .instrument(tracing::info_span!("post.async_processing"))
    );
    
    // 5. 记录指标
    metrics::counter!("posts.created").increment(1);
    
    Ok(Json(post))
}

#[instrument(name = "content.moderate", skip(services, content))]
async fn moderate_content(
    services: &Services,
    content: &str,
) -> Result<ModerationResult, AppError> {
    // 调用内容审核服务
    let response = services.http_client
        .post(&services.config.moderation_service_url)
        .json(&ModerationRequest {
            content: content.to_string(),
            language: "zh-CN".into(),
        })
        .timeout(Duration::from_secs(2))
        .send()
        .await?;
    
    response.json().await.map_err(Into::into)
}
````

---

## 4. 视频平台

### 4.1 视频上传

````rust
#[instrument(
    name = "video.upload",
    skip(services, file_data),
    fields(
        user_id = %user_id,
        file_size = file_data.len(),
        video_id = tracing::field::Empty,
    )
)]
pub async fn upload_video(
    user_id: String,
    file_data: Bytes,
    services: Arc<Services>,
) -> Result<Json<VideoUploadResult>, AppError> {
    let span = tracing::Span::current();
    
    let video_id = Uuid::new_v4().to_string();
    span.record("video_id", &video_id);
    
    // 1. 上传到对象存储
    let object_key = format!("videos/{}/{}.mp4", user_id, video_id);
    
    services.s3_client
        .put_object()
        .bucket(&services.config.bucket_name)
        .key(&object_key)
        .body(file_data.into())
        .send()
        .await?;
    
    // 2. 创建视频记录
    sqlx::query!(
        r#"
        INSERT INTO videos (id, user_id, object_key, status, created_at)
        VALUES ($1, $2, $3, 'processing', NOW())
        "#,
        video_id,
        user_id,
        object_key
    )
    .execute(&services.db)
    .await?;
    
    // 3. 触发转码任务
    trigger_transcoding(&services, &video_id, &object_key).await?;
    
    // 4. 记录指标
    metrics::counter!("videos.uploaded").increment(1);
    metrics::histogram!("videos.size_bytes")
        .record(file_data.len() as f64);
    
    Ok(Json(VideoUploadResult {
        video_id,
        status: "processing".into(),
    }))
}
````

---

## 5. IoT 系统

### 5.1 设备数据采集

````rust
#[derive(Deserialize)]
pub struct DeviceData {
    pub device_id: String,
    pub timestamp: i64,
    pub temperature: f64,
    pub humidity: f64,
    pub metrics: HashMap<String, f64>,
}

#[instrument(
    name = "iot.ingest",
    skip(data, services),
    fields(
        device_id = %data.device_id,
        data_points = data.metrics.len(),
    )
)]
pub async fn ingest_device_data(
    data: DeviceData,
    services: Arc<Services>,
) -> Result<StatusCode, AppError> {
    // 1. 验证设备
    validate_device(&services, &data.device_id).await?;
    
    // 2. 数据验证
    if data.temperature < -50.0 || data.temperature > 100.0 {
        return Err(AppError::InvalidData("temperature out of range"));
    }
    
    // 3. 写入时序数据库
    write_timeseries(&services, &data).await?;
    
    // 4. 检查告警规则
    check_alert_rules(&services, &data).await?;
    
    // 5. 记录指标
    metrics::counter!("iot.data_points", "device_id" => data.device_id.clone())
        .increment(data.metrics.len() as u64);
    
    Ok(StatusCode::ACCEPTED)
}
````

---

## 总结

### 设计模式总结

| 模式 | 应用场景 | 示例 |
|------|----------|------|
| 多级缓存 | 高频查询 | 账户查询 (L1/L2/L3) |
| 分布式锁 | 并发控制 | 转账交易 |
| 异步处理 | 耗时操作 | 订单创建、视频上传 |
| 重试机制 | 外部调用 | 支付网关 |
| 断路器 | 服务保护 | 风控服务 |
| 批量处理 | 大量数据 | IoT 数据采集 |

### 最佳实践总结

- ✅ 为关键业务操作创建 Span
- ✅ 记录完整的业务属性
- ✅ 异步处理不阻塞主流程
- ✅ 使用分布式锁保证一致性
- ✅ 多级缓存提升性能
- ✅ 重试+降级保证可用性
- ✅ 并行处理提升吞吐量
- ✅ 记录 Metrics 监控系统状态
- ✅ 错误处理和降级策略
- ✅ 使用数据库事务保证 ACID

---

**相关文档**:
- [微服务实战](../12_教程与示例/02_微服务实战_完整版.md)
- [分布式追踪最佳实践](../08_故障排查/03_分布式追踪最佳实践_Rust完整版.md)
- [性能优化](../05_采样与性能/01_Rust_1.90_性能优化完整指南.md)

