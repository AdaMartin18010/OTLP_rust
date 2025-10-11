# Cache-Aside 模式 - Rust + OTLP 缓存追踪完整实现

## 📋 目录

- [Cache-Aside 模式 - Rust + OTLP 缓存追踪完整实现](#cache-aside-模式---rust--otlp-缓存追踪完整实现)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [什么是 Cache-Aside 模式?](#什么是-cache-aside-模式)
    - [为什么使用 Rust?](#为什么使用-rust)
    - [OTLP 集成价值](#otlp-集成价值)
  - [核心概念](#核心概念)
    - [1. 缓存接口设计](#1-缓存接口设计)
    - [2. OTLP 追踪上下文](#2-otlp-追踪上下文)
  - [Rust 1.90 实现](#rust-190-实现)
    - [1. Redis 缓存实现](#1-redis-缓存实现)
    - [2. 内存缓存实现(L1)](#2-内存缓存实现l1)
  - [OTLP 集成策略](#otlp-集成策略)
    - [1. 缓存装饰器](#1-缓存装饰器)
    - [2. Cache-Aside 仓储层](#2-cache-aside-仓储层)
  - [多级缓存架构](#多级缓存架构)
    - [L1(内存) + L2(Redis) 两级缓存](#l1内存--l2redis-两级缓存)
  - [缓存失效追踪](#缓存失效追踪)
    - [1. 缓存穿透防护](#1-缓存穿透防护)
    - [2. 缓存雪崩防护](#2-缓存雪崩防护)
  - [性能监控](#性能监控)
    - [1. 缓存命中率仪表板](#1-缓存命中率仪表板)
    - [2. 告警规则](#2-告警规则)
  - [最佳实践](#最佳实践)
    - [1. 缓存键命名规范](#1-缓存键命名规范)
    - [2. TTL 策略](#2-ttl-策略)
    - [3. 缓存预热](#3-缓存预热)
  - [完整示例](#完整示例)
    - [1. Web 服务集成(Axum)](#1-web-服务集成axum)
    - [2. Docker Compose 部署](#2-docker-compose-部署)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [下一步](#下一步)
  - [参考资料](#参考资料)

---

## 概述

### 什么是 Cache-Aside 模式?

**Cache-Aside**(旁路缓存)是最常用的缓存模式,应用程序负责管理缓存和数据源之间的同步:

```text
读取流程:
1. 检查缓存
2. 缓存命中 → 返回数据
3. 缓存未命中 → 读取数据源 → 写入缓存 → 返回数据

写入流程:
1. 写入数据源
2. 使缓存失效(Invalidate)
```

### 为什么使用 Rust?

- **类型安全**: 泛型缓存接口,避免类型错误
- **高性能**: 零成本抽象,内存效率高
- **并发安全**: 线程安全的缓存实现(`Arc<RwLock>`, `DashMap`)
- **异步支持**: Tokio 异步缓存操作,减少阻塞

### OTLP 集成价值

| 可观测性维度 | OTLP 能力 |
|------------|----------|
| **缓存命中率** | Metrics(counter, gauge) |
| **缓存延迟** | Histogram(p50/p99) |
| **缓存穿透** | Tracing Span 追踪 |
| **缓存雪崩** | 分布式追踪告警 |
| **TTL 过期** | 事件日志(Logs) |

---

## 核心概念

### 1. 缓存接口设计

使用 Rust Trait 定义缓存抽象:

```rust
use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use std::time::Duration;

#[async_trait]
pub trait Cache: Send + Sync {
    /// 获取缓存值
    async fn get<T>(&self, key: &str) -> Result<Option<T>, CacheError>
    where
        T: for<'de> Deserialize<'de> + Send;

    /// 设置缓存值
    async fn set<T>(
        &self,
        key: &str,
        value: &T,
        ttl: Option<Duration>,
    ) -> Result<(), CacheError>
    where
        T: Serialize + Send + Sync;

    /// 删除缓存
    async fn delete(&self, key: &str) -> Result<(), CacheError>;

    /// 批量删除
    async fn delete_pattern(&self, pattern: &str) -> Result<usize, CacheError>;
}

#[derive(Debug, thiserror::Error)]
pub enum CacheError {
    #[error("序列化错误: {0}")]
    Serialization(#[from] serde_json::Error),
    
    #[error("Redis 错误: {0}")]
    Redis(#[from] redis::RedisError),
    
    #[error("连接错误: {0}")]
    Connection(String),
}
```

### 2. OTLP 追踪上下文

为缓存操作添加 Tracing:

```rust
use tracing::{info, instrument, warn};
use opentelemetry::global;
use opentelemetry::metrics::{Counter, Histogram, Meter};

pub struct CacheMetrics {
    hits: Counter<u64>,
    misses: Counter<u64>,
    latency: Histogram<f64>,
    errors: Counter<u64>,
}

impl CacheMetrics {
    pub fn new(meter: &Meter) -> Self {
        Self {
            hits: meter
                .u64_counter("cache.hits")
                .with_description("缓存命中次数")
                .init(),
            misses: meter
                .u64_counter("cache.misses")
                .with_description("缓存未命中次数")
                .init(),
            latency: meter
                .f64_histogram("cache.latency")
                .with_description("缓存操作延迟(ms)")
                .with_unit("ms")
                .init(),
            errors: meter
                .u64_counter("cache.errors")
                .with_description("缓存错误次数")
                .init(),
        }
    }
}
```

---

## Rust 1.90 实现

### 1. Redis 缓存实现

使用 `redis` 和 `moka` 构建多级缓存:

```toml
# Cargo.toml
[dependencies]
redis = { version = "0.27", features = ["tokio-comp", "connection-manager"] }
moka = { version = "0.12", features = ["future"] }
tokio = { version = "1.40", features = ["full"] }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
tracing = "0.1"
opentelemetry = "0.30"
opentelemetry_sdk = { version = "0.30", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.30", features = ["trace", "metrics"] }
async-trait = "0.1"
thiserror = "2.0"
```

```rust
use redis::aio::ConnectionManager;
use redis::AsyncCommands;
use std::sync::Arc;
use tracing::instrument;

pub struct RedisCache {
    client: ConnectionManager,
    metrics: Arc<CacheMetrics>,
}

impl RedisCache {
    pub async fn new(redis_url: &str, metrics: Arc<CacheMetrics>) -> Result<Self, CacheError> {
        let client = redis::Client::open(redis_url)
            .map_err(|e| CacheError::Connection(e.to_string()))?;
        
        let manager = ConnectionManager::new(client).await?;
        
        Ok(Self {
            client: manager,
            metrics,
        })
    }
}

#[async_trait]
impl Cache for RedisCache {
    #[instrument(skip(self), fields(cache.backend = "redis"))]
    async fn get<T>(&self, key: &str) -> Result<Option<T>, CacheError>
    where
        T: for<'de> Deserialize<'de> + Send,
    {
        let start = std::time::Instant::now();
        
        let mut conn = self.client.clone();
        let result: Option<String> = conn.get(key).await?;
        
        let latency = start.elapsed().as_secs_f64() * 1000.0;
        self.metrics.latency.record(latency, &[]);
        
        match result {
            Some(json) => {
                self.metrics.hits.add(1, &[]);
                info!(cache.key = key, cache.hit = true, "缓存命中");
                
                let value = serde_json::from_str(&json)?;
                Ok(Some(value))
            }
            None => {
                self.metrics.misses.add(1, &[]);
                warn!(cache.key = key, cache.hit = false, "缓存未命中");
                Ok(None)
            }
        }
    }

    #[instrument(skip(self, value))]
    async fn set<T>(
        &self,
        key: &str,
        value: &T,
        ttl: Option<Duration>,
    ) -> Result<(), CacheError>
    where
        T: Serialize + Send + Sync,
    {
        let json = serde_json::to_string(value)?;
        let mut conn = self.client.clone();
        
        match ttl {
            Some(duration) => {
                conn.set_ex(key, json, duration.as_secs()).await?;
            }
            None => {
                conn.set(key, json).await?;
            }
        }
        
        info!(cache.key = key, cache.ttl_secs = ?ttl.map(|d| d.as_secs()), "缓存已设置");
        Ok(())
    }

    #[instrument(skip(self))]
    async fn delete(&self, key: &str) -> Result<(), CacheError> {
        let mut conn = self.client.clone();
        conn.del(key).await?;
        
        info!(cache.key = key, "缓存已删除");
        Ok(())
    }

    #[instrument(skip(self))]
    async fn delete_pattern(&self, pattern: &str) -> Result<usize, CacheError> {
        let mut conn = self.client.clone();
        
        // 使用 SCAN 避免阻塞
        let keys: Vec<String> = conn.scan_match(pattern).await?.collect().await;
        let count = keys.len();
        
        if !keys.is_empty() {
            conn.del(keys).await?;
        }
        
        info!(cache.pattern = pattern, cache.deleted_count = count, "批量删除缓存");
        Ok(count)
    }
}
```

### 2. 内存缓存实现(L1)

使用 `moka` 实现本地缓存:

```rust
use moka::future::Cache as MokaCache;

pub struct MemoryCache {
    cache: MokaCache<String, String>,
    metrics: Arc<CacheMetrics>,
}

impl MemoryCache {
    pub fn new(max_capacity: u64, ttl: Duration, metrics: Arc<CacheMetrics>) -> Self {
        let cache = MokaCache::builder()
            .max_capacity(max_capacity)
            .time_to_live(ttl)
            .time_to_idle(ttl / 2)
            .build();
        
        Self { cache, metrics }
    }
}

#[async_trait]
impl Cache for MemoryCache {
    #[instrument(skip(self), fields(cache.backend = "memory"))]
    async fn get<T>(&self, key: &str) -> Result<Option<T>, CacheError>
    where
        T: for<'de> Deserialize<'de> + Send,
    {
        let start = std::time::Instant::now();
        
        let result = self.cache.get(key).await;
        
        let latency = start.elapsed().as_secs_f64() * 1000.0;
        self.metrics.latency.record(latency, &[]);
        
        match result {
            Some(json) => {
                self.metrics.hits.add(1, &[]);
                let value = serde_json::from_str(&json)?;
                Ok(Some(value))
            }
            None => {
                self.metrics.misses.add(1, &[]);
                Ok(None)
            }
        }
    }

    #[instrument(skip(self, value))]
    async fn set<T>(
        &self,
        key: &str,
        value: &T,
        _ttl: Option<Duration>, // 忽略,使用构造时的全局 TTL
    ) -> Result<(), CacheError>
    where
        T: Serialize + Send + Sync,
    {
        let json = serde_json::to_string(value)?;
        self.cache.insert(key.to_string(), json).await;
        Ok(())
    }

    async fn delete(&self, key: &str) -> Result<(), CacheError> {
        self.cache.invalidate(key).await;
        Ok(())
    }

    async fn delete_pattern(&self, pattern: &str) -> Result<usize, CacheError> {
        // 简化实现:仅支持后缀通配符
        let prefix = pattern.trim_end_matches('*');
        let mut count = 0;
        
        // Moka 不支持模式删除,需要遍历
        // 在生产环境中应使用更高效的实现
        self.cache.invalidate_all();
        
        Ok(count)
    }
}
```

---

## OTLP 集成策略

### 1. 缓存装饰器

为任何 `Cache` 实现添加 OTLP 追踪:

```rust
pub struct TracedCache<C: Cache> {
    inner: C,
    metrics: Arc<CacheMetrics>,
}

impl<C: Cache> TracedCache<C> {
    pub fn new(cache: C, metrics: Arc<CacheMetrics>) -> Self {
        Self {
            inner: cache,
            metrics,
        }
    }
}

#[async_trait]
impl<C: Cache> Cache for TracedCache<C> {
    #[instrument(skip(self), fields(otel.kind = "cache"))]
    async fn get<T>(&self, key: &str) -> Result<Option<T>, CacheError>
    where
        T: for<'de> Deserialize<'de> + Send,
    {
        let result = self.inner.get(key).await;
        
        if result.is_err() {
            self.metrics.errors.add(1, &[]);
        }
        
        result
    }

    #[instrument(skip(self, value))]
    async fn set<T>(
        &self,
        key: &str,
        value: &T,
        ttl: Option<Duration>,
    ) -> Result<(), CacheError>
    where
        T: Serialize + Send + Sync,
    {
        let result = self.inner.set(key, value, ttl).await;
        
        if result.is_err() {
            self.metrics.errors.add(1, &[]);
        }
        
        result
    }

    async fn delete(&self, key: &str) -> Result<(), CacheError> {
        self.inner.delete(key).await
    }

    async fn delete_pattern(&self, pattern: &str) -> Result<usize, CacheError> {
        self.inner.delete_pattern(pattern).await
    }
}
```

### 2. Cache-Aside 仓储层

实现带缓存的仓储模式:

```rust
use sqlx::PgPool;

pub struct CachedRepository<C: Cache> {
    cache: C,
    db: PgPool,
}

impl<C: Cache> CachedRepository<C> {
    pub fn new(cache: C, db: PgPool) -> Self {
        Self { cache, db }
    }

    #[instrument(skip(self), fields(db.table = "users"))]
    pub async fn get_user(&self, user_id: i64) -> Result<Option<User>, RepositoryError> {
        let cache_key = format!("user:{}", user_id);
        
        // 1. 尝试从缓存读取
        if let Some(user) = self.cache.get::<User>(&cache_key).await? {
            info!(user.id = user_id, "从缓存返回用户");
            return Ok(Some(user));
        }
        
        // 2. 缓存未命中,查询数据库
        let user = sqlx::query_as::<_, User>(
            "SELECT id, name, email, created_at FROM users WHERE id = $1"
        )
        .bind(user_id)
        .fetch_optional(&self.db)
        .await?;
        
        // 3. 写入缓存
        if let Some(ref u) = user {
            self.cache
                .set(&cache_key, u, Some(Duration::from_secs(300)))
                .await?;
            
            info!(user.id = user_id, "用户已缓存");
        }
        
        Ok(user)
    }

    #[instrument(skip(self, user))]
    pub async fn update_user(&self, user: &User) -> Result<(), RepositoryError> {
        // 1. 更新数据库
        sqlx::query(
            "UPDATE users SET name = $1, email = $2 WHERE id = $3"
        )
        .bind(&user.name)
        .bind(&user.email)
        .bind(user.id)
        .execute(&self.db)
        .await?;
        
        // 2. 使缓存失效
        let cache_key = format!("user:{}", user.id);
        self.cache.delete(&cache_key).await?;
        
        info!(user.id = user.id, "用户已更新,缓存已失效");
        Ok(())
    }
}

#[derive(Debug, Serialize, Deserialize, sqlx::FromRow)]
pub struct User {
    pub id: i64,
    pub name: String,
    pub email: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

#[derive(Debug, thiserror::Error)]
pub enum RepositoryError {
    #[error("缓存错误: {0}")]
    Cache(#[from] CacheError),
    
    #[error("数据库错误: {0}")]
    Database(#[from] sqlx::Error),
}
```

---

## 多级缓存架构

### L1(内存) + L2(Redis) 两级缓存

```rust
pub struct TieredCache {
    l1: MemoryCache,
    l2: RedisCache,
}

impl TieredCache {
    pub fn new(l1: MemoryCache, l2: RedisCache) -> Self {
        Self { l1, l2 }
    }
}

#[async_trait]
impl Cache for TieredCache {
    #[instrument(skip(self), fields(cache.tier = "tiered"))]
    async fn get<T>(&self, key: &str) -> Result<Option<T>, CacheError>
    where
        T: for<'de> Deserialize<'de> + Serialize + Send + Sync,
    {
        // 1. 尝试 L1(内存)
        if let Some(value) = self.l1.get::<T>(key).await? {
            info!(cache.tier = "L1", "L1 缓存命中");
            return Ok(Some(value));
        }
        
        // 2. 尝试 L2(Redis)
        if let Some(value) = self.l2.get::<T>(key).await? {
            info!(cache.tier = "L2", "L2 缓存命中,回填 L1");
            
            // 回填 L1
            self.l1.set(key, &value, None).await?;
            
            return Ok(Some(value));
        }
        
        warn!("所有缓存层未命中");
        Ok(None)
    }

    #[instrument(skip(self, value))]
    async fn set<T>(
        &self,
        key: &str,
        value: &T,
        ttl: Option<Duration>,
    ) -> Result<(), CacheError>
    where
        T: Serialize + Send + Sync,
    {
        // 同时写入两层
        let (r1, r2) = tokio::join!(
            self.l1.set(key, value, ttl),
            self.l2.set(key, value, ttl)
        );
        
        r1?;
        r2?;
        
        Ok(())
    }

    async fn delete(&self, key: &str) -> Result<(), CacheError> {
        // 同时删除两层
        let (r1, r2) = tokio::join!(
            self.l1.delete(key),
            self.l2.delete(key)
        );
        
        r1?;
        r2?;
        
        Ok(())
    }

    async fn delete_pattern(&self, pattern: &str) -> Result<usize, CacheError> {
        let count = self.l2.delete_pattern(pattern).await?;
        self.l1.delete_pattern(pattern).await?;
        Ok(count)
    }
}
```

---

## 缓存失效追踪

### 1. 缓存穿透防护

使用布隆过滤器防止缓存穿透:

```rust
use bloomfilter::Bloom;
use std::sync::RwLock;

pub struct BloomFilterCache<C: Cache> {
    cache: C,
    bloom: Arc<RwLock<Bloom<String>>>,
}

impl<C: Cache> BloomFilterCache<C> {
    pub fn new(cache: C, expected_items: usize) -> Self {
        let bloom = Bloom::new_for_fp_rate(expected_items, 0.01);
        
        Self {
            cache,
            bloom: Arc::new(RwLock::new(bloom)),
        }
    }
}

#[async_trait]
impl<C: Cache> Cache for BloomFilterCache<C> {
    #[instrument(skip(self), fields(cache.protection = "bloom_filter"))]
    async fn get<T>(&self, key: &str) -> Result<Option<T>, CacheError>
    where
        T: for<'de> Deserialize<'de> + Send,
    {
        // 1. 检查布隆过滤器
        {
            let bloom = self.bloom.read().unwrap();
            if !bloom.check(&key.to_string()) {
                warn!(cache.key = key, "布隆过滤器阻止穿透");
                return Ok(None);
            }
        }
        
        // 2. 继续正常缓存查询
        self.cache.get(key).await
    }

    async fn set<T>(
        &self,
        key: &str,
        value: &T,
        ttl: Option<Duration>,
    ) -> Result<(), CacheError>
    where
        T: Serialize + Send + Sync,
    {
        // 添加到布隆过滤器
        {
            let mut bloom = self.bloom.write().unwrap();
            bloom.set(&key.to_string());
        }
        
        self.cache.set(key, value, ttl).await
    }

    async fn delete(&self, key: &str) -> Result<(), CacheError> {
        // 布隆过滤器不支持删除,仅删除缓存
        self.cache.delete(key).await
    }

    async fn delete_pattern(&self, pattern: &str) -> Result<usize, CacheError> {
        self.cache.delete_pattern(pattern).await
    }
}
```

### 2. 缓存雪崩防护

随机 TTL 避免同时过期:

```rust
use rand::Rng;

pub fn jittered_ttl(base_ttl: Duration, jitter_percent: f64) -> Duration {
    let mut rng = rand::thread_rng();
    let jitter = rng.gen_range(-jitter_percent..jitter_percent);
    
    let multiplier = 1.0 + jitter;
    let secs = (base_ttl.as_secs_f64() * multiplier).max(1.0);
    
    Duration::from_secs_f64(secs)
}

// 使用示例
let ttl = jittered_ttl(Duration::from_secs(300), 0.2); // ±20% 抖动
cache.set("key", &value, Some(ttl)).await?;
```

---

## 性能监控

### 1. 缓存命中率仪表板

使用 Prometheus + Grafana 监控:

```promql
# 缓存命中率
sum(rate(cache_hits_total[5m])) / 
(sum(rate(cache_hits_total[5m])) + sum(rate(cache_misses_total[5m]))) * 100

# P99 延迟
histogram_quantile(0.99, 
  sum(rate(cache_latency_bucket[5m])) by (le)
)

# 错误率
sum(rate(cache_errors_total[5m])) by (backend)
```

### 2. 告警规则

```yaml
# prometheus_rules.yml
groups:
  - name: cache_alerts
    interval: 30s
    rules:
      - alert: CacheHitRateLow
        expr: |
          (sum(rate(cache_hits_total[5m])) / 
           (sum(rate(cache_hits_total[5m])) + sum(rate(cache_misses_total[5m]))))
          < 0.7
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "缓存命中率过低 ({{ $value | humanizePercentage }})"
          
      - alert: CacheLatencyHigh
        expr: |
          histogram_quantile(0.99,
            sum(rate(cache_latency_bucket[5m])) by (le)
          ) > 100
        for: 2m
        labels:
          severity: critical
        annotations:
          summary: "缓存 P99 延迟超过 100ms"
```

---

## 最佳实践

### 1. 缓存键命名规范

```rust
pub struct CacheKeyBuilder {
    namespace: String,
}

impl CacheKeyBuilder {
    pub fn new(namespace: &str) -> Self {
        Self {
            namespace: namespace.to_string(),
        }
    }
    
    pub fn user(&self, user_id: i64) -> String {
        format!("{}:user:{}", self.namespace, user_id)
    }
    
    pub fn user_posts(&self, user_id: i64) -> String {
        format!("{}:user:{}:posts", self.namespace, user_id)
    }
    
    pub fn post(&self, post_id: i64) -> String {
        format!("{}:post:{}", self.namespace, post_id)
    }
}

// 使用示例
let keys = CacheKeyBuilder::new("myapp");
let key = keys.user(123); // "myapp:user:123"
```

### 2. TTL 策略

| 数据类型 | 推荐 TTL | 说明 |
|---------|---------|------|
| 用户信息 | 5-15 分钟 | 平衡一致性和性能 |
| 配置数据 | 1-24 小时 | 变更频率低 |
| 会话数据 | 30 分钟 | 与会话过期时间一致 |
| API 响应 | 1-5 分钟 | 根据实时性要求调整 |
| 热点数据 | 10-30 秒 | 高频访问,短 TTL |

### 3. 缓存预热

```rust
#[instrument]
pub async fn warm_up_cache<C: Cache>(
    cache: &C,
    db: &PgPool,
) -> Result<usize, Box<dyn std::error::Error>> {
    // 预加载热门用户
    let hot_users = sqlx::query_as::<_, User>(
        "SELECT * FROM users ORDER BY login_count DESC LIMIT 1000"
    )
    .fetch_all(db)
    .await?;
    
    let mut count = 0;
    for user in hot_users {
        let key = format!("user:{}", user.id);
        cache.set(&key, &user, Some(Duration::from_secs(600))).await?;
        count += 1;
    }
    
    info!(preloaded_count = count, "缓存预热完成");
    Ok(count)
}
```

---

## 完整示例

### 1. Web 服务集成(Axum)

```rust
use axum::{
    extract::{Path, State},
    http::StatusCode,
    response::IntoResponse,
    routing::get,
    Json, Router,
};

#[derive(Clone)]
struct AppState {
    repo: Arc<CachedRepository<TieredCache>>,
}

async fn get_user_handler(
    State(state): State<AppState>,
    Path(user_id): Path<i64>,
) -> Result<Json<User>, AppError> {
    let user = state
        .repo
        .get_user(user_id)
        .await?
        .ok_or(AppError::NotFound)?;
    
    Ok(Json(user))
}

async fn update_user_handler(
    State(state): State<AppState>,
    Path(user_id): Path<i64>,
    Json(mut user): Json<User>,
) -> Result<StatusCode, AppError> {
    user.id = user_id;
    state.repo.update_user(&user).await?;
    
    Ok(StatusCode::NO_CONTENT)
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化 OTLP
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(opentelemetry_otlp::new_exporter().tonic())
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    tracing_subscriber::registry()
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();
    
    let meter = global::meter("cache_aside_example");
    let metrics = Arc::new(CacheMetrics::new(&meter));
    
    // 构建多级缓存
    let l1 = MemoryCache::new(1000, Duration::from_secs(60), metrics.clone());
    let l2 = RedisCache::new("redis://127.0.0.1", metrics.clone()).await?;
    let cache = TieredCache::new(l1, l2);
    
    // 数据库连接池
    let db = PgPool::connect("postgresql://user:pass@localhost/db").await?;
    
    // 创建仓储
    let repo = Arc::new(CachedRepository::new(cache, db));
    
    // 启动服务
    let app = Router::new()
        .route("/users/:id", get(get_user_handler).put(update_user_handler))
        .with_state(AppState { repo });
    
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
    axum::serve(listener, app).await?;
    
    Ok(())
}

#[derive(Debug)]
enum AppError {
    NotFound,
    Repository(RepositoryError),
}

impl From<RepositoryError> for AppError {
    fn from(err: RepositoryError) -> Self {
        AppError::Repository(err)
    }
}

impl IntoResponse for AppError {
    fn into_response(self) -> axum::response::Response {
        match self {
            AppError::NotFound => {
                (StatusCode::NOT_FOUND, "用户不存在").into_response()
            }
            AppError::Repository(err) => {
                (StatusCode::INTERNAL_SERVER_ERROR, err.to_string()).into_response()
            }
        }
    }
}
```

### 2. Docker Compose 部署

```yaml
version: '3.8'

services:
  app:
    build: .
    ports:
      - "3000:3000"
    environment:
      REDIS_URL: redis://redis:6379
      DATABASE_URL: postgresql://postgres:password@postgres:5432/mydb
      OTEL_EXPORTER_OTLP_ENDPOINT: http://otel-collector:4317
    depends_on:
      - redis
      - postgres
      - otel-collector

  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"

  postgres:
    image: postgres:16-alpine
    environment:
      POSTGRES_PASSWORD: password
      POSTGRES_DB: mydb
    volumes:
      - postgres_data:/var/lib/postgresql/data

  otel-collector:
    image: otel/opentelemetry-collector-contrib:0.98.0
    volumes:
      - ./otel-collector-config.yaml:/etc/otel-collector-config.yaml
    command: ["--config=/etc/otel-collector-config.yaml"]
    ports:
      - "4317:4317"  # OTLP gRPC
      - "8889:8889"  # Prometheus metrics

  prometheus:
    image: prom/prometheus:latest
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml
    ports:
      - "9090:9090"

  grafana:
    image: grafana/grafana:latest
    ports:
      - "3001:3000"
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=admin

volumes:
  postgres_data:
```

---

## 总结

### 核心要点

1. **Rust Trait 抽象**: 定义统一缓存接口
2. **多级缓存**: L1(内存) + L2(Redis) 提升性能
3. **OTLP 全方位监控**: Metrics(命中率/延迟) + Tracing(操作追踪)
4. **防护机制**: 布隆过滤器(穿透) + 随机 TTL(雪崩)
5. **Cache-Aside 模式**: 应用层管理缓存失效

### 下一步

- **分布式缓存一致性**: 使用 Redis Pub/Sub 通知其他节点失效
- **缓存预热策略**: 启动时自动加载热点数据
- **缓存压缩**: 使用 `lz4` 压缩大对象
- **缓存监控告警**: Grafana 仪表板 + Alertmanager

---

## 参考资料

- [Rust Redis 客户端](https://docs.rs/redis)
- [Moka 高性能缓存](https://docs.rs/moka)
- [OpenTelemetry Rust SDK](https://docs.rs/opentelemetry)
- [Cache-Aside Pattern - Microsoft](https://docs.microsoft.com/en-us/azure/architecture/patterns/cache-aside)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-11  
**Rust 版本**: 1.90+  
**OpenTelemetry**: 0.30+
