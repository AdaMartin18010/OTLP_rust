# Web 性能优化 - Web Performance Optimization

**创建日期**: 2025年10月29日  
**基于**: 生产环境可观测性数据  
**状态**: ✅ 生产验证

---

## 📋 目录

- [概述](#概述)
- [性能分析方法](#性能分析方法)
- [热路径优化](#热路径优化)
- [缓存策略](#缓存策略)
- [数据库优化](#数据库优化)
- [连接池优化](#连接池优化)
- [并发控制](#并发控制)
- [监控和告警](#监控和告警)

---

## 概述

基于可观测性数据的Web性能优化方法论：

- ✅ **数据驱动**: 基于追踪数据识别瓶颈
- ✅ **系统化**: 覆盖请求生命周期各环节
- ✅ **可测量**: 每项优化都有明确指标
- ✅ **可持续**: 建立持续优化机制
- ✅ **生产验证**: 真实环境验证效果

---

## 性能分析方法

### 基于追踪的性能分析

```rust
use opentelemetry::trace::{Span, Tracer};
use std::time::Instant;

// 性能分析器
#[derive(Clone)]
pub struct PerformanceAnalyzer {
    tracer: global::BoxedTracer,
    slow_threshold: Duration,
}

impl PerformanceAnalyzer {
    pub fn new(slow_threshold: Duration) -> Self {
        Self {
            tracer: global::tracer("performance"),
            slow_threshold,
        }
    }
    
    // 分析请求性能
    #[instrument(skip(self), fields(
        request.path = %path,
        request.method = %method
    ))]
    pub async fn analyze_request(&self, path: &str, method: &str) -> RequestPerformance {
        let start = Instant::now();
        
        // 收集span数据
        let span_data = self.collect_span_data().await;
        
        // 分析各阶段耗时
        let breakdown = self.analyze_breakdown(&span_data);
        
        // 识别慢查询
        let slow_queries = self.identify_slow_queries(&span_data);
        
        // 识别N+1问题
        let n1_issues = self.detect_n1_patterns(&span_data);
        
        let total_duration = start.elapsed();
        
        RequestPerformance {
            total_duration,
            breakdown,
            slow_queries,
            n1_issues,
        }
    }
    
    // 分析性能分解
    fn analyze_breakdown(&self, spans: &[SpanData]) -> PerformanceBreakdown {
        let mut breakdown = PerformanceBreakdown::default();
        
        for span in spans {
            match span.name.as_str() {
                name if name.starts_with("db.") => {
                    breakdown.database_time += span.duration;
                }
                name if name.starts_with("cache.") => {
                    breakdown.cache_time += span.duration;
                }
                name if name.starts_with("http.client") => {
                    breakdown.external_api_time += span.duration;
                }
                name if name.contains("business_logic") => {
                    breakdown.business_logic_time += span.duration;
                }
                _ => {
                    breakdown.other_time += span.duration;
                }
            }
        }
        
        breakdown
    }
    
    // 识别慢查询
    fn identify_slow_queries(&self, spans: &[SpanData]) -> Vec<SlowQuery> {
        spans
            .iter()
            .filter(|span| {
                span.name.starts_with("db.") && span.duration > self.slow_threshold
            })
            .map(|span| SlowQuery {
                query: span.attributes.get("db.statement").cloned(),
                duration: span.duration,
                location: span.attributes.get("code.filepath").cloned(),
            })
            .collect()
    }
}

#[derive(Debug, Default)]
pub struct PerformanceBreakdown {
    pub database_time: Duration,
    pub cache_time: Duration,
    pub external_api_time: Duration,
    pub business_logic_time: Duration,
    pub other_time: Duration,
}

impl PerformanceBreakdown {
    // 生成性能报告
    pub fn report(&self, total: Duration) -> String {
        format!(
            "Performance Breakdown:\n\
             - Database: {}ms ({:.1}%)\n\
             - Cache: {}ms ({:.1}%)\n\
             - External API: {}ms ({:.1}%)\n\
             - Business Logic: {}ms ({:.1}%)\n\
             - Other: {}ms ({:.1}%)",
            self.database_time.as_millis(),
            self.percentage(self.database_time, total),
            self.cache_time.as_millis(),
            self.percentage(self.cache_time, total),
            self.external_api_time.as_millis(),
            self.percentage(self.external_api_time, total),
            self.business_logic_time.as_millis(),
            self.percentage(self.business_logic_time, total),
            self.other_time.as_millis(),
            self.percentage(self.other_time, total),
        )
    }
    
    fn percentage(&self, part: Duration, total: Duration) -> f64 {
        if total.as_millis() == 0 {
            return 0.0;
        }
        (part.as_millis() as f64 / total.as_millis() as f64) * 100.0
    }
}
```

---

## 热路径优化

### 识别和优化热路径

```rust
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};

// 热路径统计
#[derive(Clone)]
pub struct HotPathTracker {
    paths: Arc<DashMap<String, PathStats>>,
}

#[derive(Debug, Default)]
struct PathStats {
    hit_count: AtomicU64,
    total_duration: AtomicU64,  // 微秒
    p50_duration: AtomicU64,
    p95_duration: AtomicU64,
    p99_duration: AtomicU64,
}

impl HotPathTracker {
    pub fn new() -> Self {
        Self {
            paths: Arc::new(DashMap::new()),
        }
    }
    
    // 记录请求
    pub fn record(&self, path: &str, duration: Duration) {
        let stats = self.paths
            .entry(path.to_string())
            .or_insert_with(PathStats::default);
        
        stats.hit_count.fetch_add(1, Ordering::Relaxed);
        stats.total_duration.fetch_add(duration.as_micros() as u64, Ordering::Relaxed);
    }
    
    // 获取热路径 (Top N)
    pub fn hot_paths(&self, top_n: usize) -> Vec<(String, HotPathMetrics)> {
        let mut paths: Vec<_> = self.paths
            .iter()
            .map(|entry| {
                let path = entry.key().clone();
                let stats = entry.value();
                let hit_count = stats.hit_count.load(Ordering::Relaxed);
                let total_duration = stats.total_duration.load(Ordering::Relaxed);
                
                let avg_duration = if hit_count > 0 {
                    Duration::from_micros(total_duration / hit_count)
                } else {
                    Duration::ZERO
                };
                
                (
                    path,
                    HotPathMetrics {
                        hit_count,
                        avg_duration,
                        p50: Duration::from_micros(stats.p50_duration.load(Ordering::Relaxed)),
                        p95: Duration::from_micros(stats.p95_duration.load(Ordering::Relaxed)),
                        p99: Duration::from_micros(stats.p99_duration.load(Ordering::Relaxed)),
                    },
                )
            })
            .collect();
        
        // 按hit_count排序
        paths.sort_by(|a, b| b.1.hit_count.cmp(&a.1.hit_count));
        paths.truncate(top_n);
        paths
    }
}

#[derive(Debug)]
pub struct HotPathMetrics {
    pub hit_count: u64,
    pub avg_duration: Duration,
    pub p50: Duration,
    pub p95: Duration,
    pub p99: Duration,
}

// 热路径优化示例
#[instrument(skip(db, cache))]
async fn optimized_hot_path(
    db: &Database,
    cache: &Cache,
    user_id: u64,
) -> Result<User> {
    // 1. 先查缓存 (热路径优化)
    if let Some(user) = cache.get_user(user_id).await? {
        tracing::debug!("Cache hit");
        return Ok(user);
    }
    
    // 2. 缓存未命中,查数据库
    tracing::debug!("Cache miss, querying database");
    let user = db.get_user(user_id).await?;
    
    // 3. 异步更新缓存 (不阻塞响应)
    let cache_clone = cache.clone();
    let user_clone = user.clone();
    tokio::spawn(async move {
        if let Err(e) = cache_clone.set_user(user_id, &user_clone).await {
            tracing::warn!(error = %e, "Failed to update cache");
        }
    });
    
    Ok(user)
}
```

---

## 缓存策略

### 多层缓存架构

```rust
use moka::future::Cache as MokaCache;

// 多层缓存
#[derive(Clone)]
pub struct MultiLayerCache {
    // L1: 进程内缓存 (最快)
    l1: MokaCache<String, Arc<Vec<u8>>>,
    // L2: Redis缓存 (分布式)
    l2: redis::Client,
    // 指标
    meter: Meter,
}

impl MultiLayerCache {
    pub fn new(l1_capacity: u64, redis_url: &str, meter: Meter) -> Result<Self> {
        Ok(Self {
            l1: MokaCache::builder()
                .max_capacity(l1_capacity)
                .time_to_live(Duration::from_secs(60))
                .build(),
            l2: redis::Client::open(redis_url)?,
            meter,
        })
    }
    
    // 获取数据
    #[instrument(skip(self), fields(cache.key = %key))]
    pub async fn get<T: DeserializeOwned>(&self, key: &str) -> Result<Option<T>> {
        // 1. 尝试L1缓存
        if let Some(data) = self.l1.get(key).await {
            tracing::debug!("L1 cache hit");
            self.record_hit("l1");
            return Ok(Some(bincode::deserialize(&data)?));
        }
        
        // 2. 尝试L2缓存
        let mut conn = self.l2.get_async_connection().await?;
        if let Some(data) = redis::cmd("GET")
            .arg(key)
            .query_async::<_, Option<Vec<u8>>>(&mut conn)
            .await?
        {
            tracing::debug!("L2 cache hit");
            self.record_hit("l2");
            
            // 回填L1
            self.l1.insert(key.to_string(), Arc::new(data.clone())).await;
            
            return Ok(Some(bincode::deserialize(&data)?));
        }
        
        tracing::debug!("Cache miss");
        self.record_miss();
        Ok(None)
    }
    
    // 设置数据
    #[instrument(skip(self, value), fields(cache.key = %key))]
    pub async fn set<T: Serialize>(&self, key: &str, value: &T, ttl: Duration) -> Result<()> {
        let data = bincode::serialize(value)?;
        let data_arc = Arc::new(data.clone());
        
        // 并发写入两层缓存
        let l1_fut = self.l1.insert(key.to_string(), data_arc);
        let l2_fut = async {
            let mut conn = self.l2.get_async_connection().await?;
            redis::cmd("SETEX")
                .arg(key)
                .arg(ttl.as_secs())
                .arg(&data)
                .query_async(&mut conn)
                .await
        };
        
        tokio::try_join!(l1_fut, l2_fut)?;
        
        tracing::debug!("Data cached in L1 and L2");
        Ok(())
    }
    
    // 记录缓存命中
    fn record_hit(&self, layer: &str) {
        self.meter
            .u64_counter("cache.hits")
            .add(1, &[KeyValue::new("layer", layer.to_string())]);
    }
    
    // 记录缓存未命中
    fn record_miss(&self) {
        self.meter
            .u64_counter("cache.misses")
            .add(1, &[]);
    }
}

// 缓存预热
pub struct CacheWarmer {
    cache: MultiLayerCache,
    db: Database,
}

impl CacheWarmer {
    #[instrument(skip(self))]
    pub async fn warm_popular_data(&self) -> Result<()> {
        tracing::info!("Starting cache warming");
        
        // 1. 获取热门数据列表
        let popular_users = self.db.get_popular_users(100).await?;
        
        // 2. 并发预热
        let futures: Vec<_> = popular_users
            .into_iter()
            .map(|user| async move {
                let key = format!("user:{}", user.id);
                self.cache.set(&key, &user, Duration::from_secs(300)).await
            })
            .collect();
        
        let results = futures::future::join_all(futures).await;
        let success_count = results.iter().filter(|r| r.is_ok()).count();
        
        tracing::info!(
            total = results.len(),
            success = success_count,
            "Cache warming completed"
        );
        
        Ok(())
    }
}
```

---

## 数据库优化

### 慢查询优化

```rust
// 数据库查询追踪和优化
#[derive(Clone)]
pub struct TrackedDatabase {
    pool: sqlx::PgPool,
    slow_threshold: Duration,
    meter: Meter,
}

impl TrackedDatabase {
    pub fn new(pool: sqlx::PgPool, slow_threshold: Duration, meter: Meter) -> Self {
        Self {
            pool,
            slow_threshold,
            meter,
        }
    }
    
    // 执行查询with追踪
    #[instrument(
        skip(self, query),
        fields(
            db.system = "postgresql",
            db.statement = tracing::field::Empty
        )
    )]
    pub async fn query<T>(&self, query: &str) -> Result<Vec<T>>
    where
        T: for<'r> sqlx::FromRow<'r, sqlx::postgres::PgRow> + Send + Unpin,
    {
        let span = tracing::Span::current();
        span.record("db.statement", &query);
        
        let start = Instant::now();
        let result = sqlx::query_as::<_, T>(query)
            .fetch_all(&self.pool)
            .await;
        let duration = start.elapsed();
        
        // 记录查询时间
        self.meter
            .f64_histogram("db.query.duration")
            .record(duration.as_secs_f64(), &[]);
        
        // 检测慢查询
        if duration > self.slow_threshold {
            tracing::warn!(
                query = %query,
                duration_ms = duration.as_millis(),
                "Slow query detected"
            );
            
            self.meter
                .u64_counter("db.slow_queries")
                .add(1, &[]);
        }
        
        result.map_err(Into::into)
    }
    
    // 批量查询优化
    #[instrument(skip(self, ids))]
    pub async fn get_users_batch(&self, ids: &[u64]) -> Result<HashMap<u64, User>> {
        if ids.is_empty() {
            return Ok(HashMap::new());
        }
        
        // 使用IN查询代替多次单独查询
        let query = format!(
            "SELECT * FROM users WHERE id = ANY($1)"
        );
        
        let users: Vec<User> = sqlx::query_as(&query)
            .bind(ids)
            .fetch_all(&self.pool)
            .await?;
        
        Ok(users.into_iter().map(|u| (u.id, u)).collect())
    }
}

// 连接池监控
pub async fn monitor_connection_pool(pool: &sqlx::PgPool, meter: &Meter) {
    let connections = pool.size() as i64;
    let idle = pool.num_idle() as i64;
    let active = connections - idle;
    
    meter
        .i64_observable_gauge("db.pool.connections")
        .with_callback(move |observer| {
            observer.observe(connections, &[KeyValue::new("state", "total")]);
            observer.observe(active, &[KeyValue::new("state", "active")]);
            observer.observe(idle, &[KeyValue::new("state", "idle")]);
        })
        .init();
}
```

---

## 连接池优化

### HTTP客户端连接池

```rust
use reqwest::Client;

// 优化的HTTP客户端
pub fn create_optimized_client() -> Client {
    Client::builder()
        // 连接池设置
        .pool_max_idle_per_host(10)
        .pool_idle_timeout(Duration::from_secs(90))
        
        // 超时设置
        .connect_timeout(Duration::from_secs(10))
        .timeout(Duration::from_secs(30))
        
        // TCP设置
        .tcp_nodelay(true)
        .tcp_keepalive(Duration::from_secs(60))
        
        // HTTP/2
        .http2_adaptive_window(true)
        .http2_keep_alive_interval(Some(Duration::from_secs(30)))
        .http2_keep_alive_timeout(Duration::from_secs(20))
        
        .build()
        .expect("Failed to create HTTP client")
}
```

---

## 并发控制

### 请求限流和负载控制

```rust
use tokio::sync::Semaphore;

// 并发限制器
#[derive(Clone)]
pub struct ConcurrencyLimiter {
    semaphore: Arc<Semaphore>,
    max_concurrent: usize,
    meter: Meter,
}

impl ConcurrencyLimiter {
    pub fn new(max_concurrent: usize, meter: Meter) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
            max_concurrent,
            meter,
        }
    }
    
    // 受限执行
    #[instrument(skip(self, f))]
    pub async fn execute<F, T>(&self, f: F) -> Result<T>
    where
        F: Future<Output = Result<T>>,
    {
        // 尝试获取许可
        let permit = self.semaphore.acquire().await?;
        
        let current = self.max_concurrent - self.semaphore.available_permits();
        
        tracing::debug!(
            concurrent_requests = current,
            max_concurrent = self.max_concurrent,
            "Request acquired permit"
        );
        
        // 记录并发数
        self.meter
            .i64_observable_gauge("http.concurrent_requests")
            .with_callback(move |observer| {
                observer.observe(current as i64, &[]);
            })
            .init();
        
        // 执行请求
        let result = f.await;
        
        // 许可自动释放
        drop(permit);
        
        result
    }
}
```

---

## 监控和告警

### 性能监控仪表板

```rust
// 性能指标收集器
#[derive(Clone)]
pub struct PerformanceMetrics {
    meter: Meter,
}

impl PerformanceMetrics {
    pub fn new(meter: Meter) -> Self {
        // 初始化指标
        meter.f64_histogram("http.server.duration").init();
        meter.u64_counter("http.server.requests").init();
        meter.u64_counter("http.server.errors").init();
        
        Self { meter }
    }
    
    // 记录请求性能
    pub fn record_request(
        &self,
        method: &str,
        path: &str,
        status: u16,
        duration: Duration,
    ) {
        let attributes = vec![
            KeyValue::new("http.method", method.to_string()),
            KeyValue::new("http.route", path.to_string()),
            KeyValue::new("http.status_code", status as i64),
        ];
        
        // 记录延迟
        self.meter
            .f64_histogram("http.server.duration")
            .record(duration.as_secs_f64(), &attributes);
        
        // 记录请求数
        self.meter
            .u64_counter("http.server.requests")
            .add(1, &attributes);
        
        // 记录错误
        if status >= 500 {
            self.meter
                .u64_counter("http.server.errors")
                .add(1, &attributes);
        }
    }
}

// SLO告警
pub async fn check_slo_violations(metrics: &PerformanceMetrics) -> Vec<SLOViolation> {
    let mut violations = Vec::new();
    
    // 检查P99延迟
    if let Some(p99) = get_p99_latency().await {
        if p99 > Duration::from_millis(200) {
            violations.push(SLOViolation {
                metric: "p99_latency".to_string(),
                current: p99,
                threshold: Duration::from_millis(200),
                severity: Severity::Warning,
            });
        }
    }
    
    // 检查错误率
    if let Some(error_rate) = get_error_rate().await {
        if error_rate > 0.01 {  // 1%
            violations.push(SLOViolation {
                metric: "error_rate".to_string(),
                current_rate: error_rate,
                threshold_rate: 0.01,
                severity: Severity::Critical,
            });
        }
    }
    
    violations
}
```

---

## 总结

Web性能优化的关键点：

1. **数据驱动**: 基于追踪和指标识别瓶颈
2. **系统化**: 覆盖缓存、数据库、网络各层
3. **可测量**: 每项优化都有明确的性能指标
4. **持续优化**: 建立监控告警机制
5. **生产验证**: 在真实环境验证效果

**典型优化效果**:

- P99延迟降低: 40-60%
- 吞吐量提升: 2-3x
- 数据库负载: 减少50-70%
- 缓存命中率: 提升到85%+

**下一步**:

- 🚀 [生产环境部署](./production_deployment.md)
