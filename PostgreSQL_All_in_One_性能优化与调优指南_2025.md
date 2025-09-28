# PostgreSQL All-in-One 性能优化与调优指南 - 2025年

## 📋 执行摘要

本文档提供了PostgreSQL All-in-One架构的全面性能优化和调优指南，包括数据库配置优化、查询性能调优、缓存策略优化、系统资源优化和监控调优。通过系统性的性能优化，确保系统在高负载下保持优异的性能表现。

## 🎯 性能优化目标

### 1. 核心性能指标

| 指标类型 | 目标值 | 监控方式 |
|---------|--------|----------|
| **OLTP查询延迟** | < 100ms (95%分位数) | Prometheus + Grafana |
| **OLAP查询延迟** | < 5s (95%分位数) | 查询执行计划分析 |
| **全文搜索延迟** | < 1s (95%分位数) | 索引使用率监控 |
| **并发连接数** | 支持200个连接 | 连接池监控 |
| **吞吐量** | 10,000 TPS | 事务处理监控 |
| **缓存命中率** | > 95% | Redis监控 |
| **系统可用性** | 99.9% | 健康检查监控 |

### 2. 优化策略

```text
┌─────────────────────────────────────────────────────────────┐
│                    性能优化策略                              │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌─────────┐ │
│  │  数据库优化  │ │  查询优化   │ │  缓存优化   │ │ 系统优化 │ │
│  │ DB Config   │ │ Query Tuning│ │ Cache Tuning│ │System   │ │
│  └─────────────┘ └─────────────┘ └─────────────┘ └─────────┘ │
├─────────────────────────────────────────────────────────────┤
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌─────────┐ │
│  │  索引优化   │ │  分区优化   │ │  连接优化   │ │ 监控优化 │ │
│  │ Index Tuning│ │Partitioning │ │Connection   │ │Monitoring│ │
│  └─────────────┘ └─────────────┘ └─────────────┘ └─────────┘ │
└─────────────────────────────────────────────────────────────┘
```

## 🗄️ 数据库配置优化

### 1. PostgreSQL 核心配置优化

#### 1.1 内存配置优化

```sql
-- postgresql.conf 内存配置
-- 基于32GB内存的服务器配置

# 共享缓冲区 (25% of RAM)
shared_buffers = 8GB

# 有效缓存大小 (75% of RAM)
effective_cache_size = 24GB

# 工作内存 (每个查询操作)
work_mem = 256MB

# 维护工作内存 (VACUUM, CREATE INDEX等)
maintenance_work_mem = 2GB

# 动态共享内存
dynamic_shared_memory_type = posix

# 大页面支持
huge_pages = try
```

#### 1.2 连接和并发配置

```sql
-- 连接配置
max_connections = 200
superuser_reserved_connections = 3

# 连接池配置
shared_preload_libraries = 'pg_stat_statements,timescaledb'

# 并发配置
max_worker_processes = 8
max_parallel_workers_per_gather = 4
max_parallel_workers = 8
max_parallel_maintenance_workers = 4
```

#### 1.3 I/O 和存储优化

```sql
-- I/O 配置 (SSD优化)
random_page_cost = 1.1
seq_page_cost = 1.0
effective_io_concurrency = 200

# 检查点配置
checkpoint_completion_target = 0.9
checkpoint_timeout = 15min
max_wal_size = 4GB
min_wal_size = 1GB

# WAL 配置
wal_level = replica
wal_buffers = 16MB
wal_writer_delay = 200ms
commit_delay = 0
commit_siblings = 5
```

#### 1.4 查询优化配置

```sql
-- 查询规划器配置
default_statistics_target = 100
constraint_exclusion = partition
cursor_tuple_fraction = 0.1

# 并行查询配置
parallel_tuple_cost = 0.1
parallel_setup_cost = 1000.0
min_parallel_table_scan_size = 8MB
min_parallel_index_scan_size = 512kB

# 成本配置
cpu_tuple_cost = 0.01
cpu_index_tuple_cost = 0.005
cpu_operator_cost = 0.0025
```

### 2. 高级配置优化

#### 2.1 日志和监控配置

```sql
-- 日志配置
log_destination = 'stderr'
logging_collector = on
log_directory = 'pg_log'
log_filename = 'postgresql-%Y-%m-%d_%H%M%S.log'
log_rotation_age = 1d
log_rotation_size = 100MB
log_min_duration_statement = 1000
log_statement = 'mod'
log_line_prefix = '%t [%p]: [%l-1] user=%u,db=%d,app=%a,client=%h '
log_checkpoints = on
log_connections = on
log_disconnections = on
log_lock_waits = on
log_temp_files = 0
```

#### 2.2 自动清理配置

```sql
-- 自动清理配置
autovacuum = on
autovacuum_max_workers = 3
autovacuum_naptime = 1min
autovacuum_vacuum_threshold = 50
autovacuum_analyze_threshold = 50
autovacuum_vacuum_scale_factor = 0.2
autovacuum_analyze_scale_factor = 0.1
autovacuum_freeze_max_age = 200000000
autovacuum_multixact_freeze_max_age = 400000000
autovacuum_vacuum_cost_delay = 20ms
autovacuum_vacuum_cost_limit = 200
```

## 🔍 查询性能优化

### 1. 索引优化策略

#### 1.1 复合索引优化

```sql
-- 用户行为分析表索引优化
CREATE TABLE user_events (
    id BIGSERIAL PRIMARY KEY,
    user_id BIGINT NOT NULL,
    event_type VARCHAR(50) NOT NULL,
    event_data JSONB,
    timestamp TIMESTAMPTZ NOT NULL,
    created_at TIMESTAMPTZ DEFAULT NOW()
);

-- 复合索引：用户ID + 时间戳
CREATE INDEX CONCURRENTLY idx_user_events_user_timestamp 
ON user_events (user_id, timestamp DESC);

-- 复合索引：事件类型 + 时间戳
CREATE INDEX CONCURRENTLY idx_user_events_type_timestamp 
ON user_events (event_type, timestamp DESC);

-- 部分索引：活跃用户事件
CREATE INDEX CONCURRENTLY idx_user_events_active_users 
ON user_events (user_id, timestamp DESC) 
WHERE timestamp > NOW() - INTERVAL '30 days';

-- JSONB 索引
CREATE INDEX CONCURRENTLY idx_user_events_data_gin 
ON user_events USING GIN (event_data);

-- 表达式索引：按小时分组
CREATE INDEX CONCURRENTLY idx_user_events_hour 
ON user_events (date_trunc('hour', timestamp));
```

#### 1.2 全文搜索索引优化

```sql
-- 文档表全文搜索优化
CREATE TABLE documents (
    id BIGSERIAL PRIMARY KEY,
    title VARCHAR(200) NOT NULL,
    content TEXT NOT NULL,
    metadata JSONB,
    search_vector tsvector,
    created_at TIMESTAMPTZ DEFAULT NOW(),
    updated_at TIMESTAMPTZ DEFAULT NOW()
);

-- 全文搜索索引
CREATE INDEX CONCURRENTLY idx_documents_search_gin 
ON documents USING GIN (search_vector);

-- 标题索引
CREATE INDEX CONCURRENTLY idx_documents_title_gin 
ON documents USING GIN (to_tsvector('simple', title));

-- 元数据索引
CREATE INDEX CONCURRENTLY idx_documents_metadata_gin 
ON documents USING GIN (metadata);

-- 时间范围索引
CREATE INDEX CONCURRENTLY idx_documents_created_at 
ON documents (created_at DESC);
```

### 2. 查询重写优化

#### 2.1 OLTP 查询优化

```sql
-- 原始查询（性能较差）
SELECT * FROM user_events 
WHERE user_id = 123 
AND timestamp > '2025-01-01' 
ORDER BY timestamp DESC 
LIMIT 100;

-- 优化后查询（使用索引）
SELECT id, user_id, event_type, event_data, timestamp 
FROM user_events 
WHERE user_id = 123 
AND timestamp > '2025-01-01' 
ORDER BY timestamp DESC 
LIMIT 100;

-- 使用 EXPLAIN 分析查询计划
EXPLAIN (ANALYZE, BUFFERS, VERBOSE) 
SELECT id, user_id, event_type, event_data, timestamp 
FROM user_events 
WHERE user_id = 123 
AND timestamp > '2025-01-01' 
ORDER BY timestamp DESC 
LIMIT 100;
```

#### 2.2 OLAP 查询优化

```sql
-- 原始聚合查询
SELECT 
    user_id,
    COUNT(*) as event_count,
    AVG((event_data->>'value')::numeric) as avg_value
FROM user_events 
WHERE timestamp > NOW() - INTERVAL '1 day'
GROUP BY user_id
ORDER BY event_count DESC;

-- 优化后查询（使用并行处理）
SET max_parallel_workers_per_gather = 4;
SET parallel_tuple_cost = 0.1;
SET parallel_setup_cost = 1000.0;

SELECT 
    user_id,
    COUNT(*) as event_count,
    AVG((event_data->>'value')::numeric) as avg_value
FROM user_events 
WHERE timestamp > NOW() - INTERVAL '1 day'
GROUP BY user_id
ORDER BY event_count DESC;

-- 使用物化视图优化重复查询
CREATE MATERIALIZED VIEW mv_daily_user_stats AS
SELECT 
    date_trunc('day', timestamp) as date,
    user_id,
    COUNT(*) as event_count,
    AVG((event_data->>'value')::numeric) as avg_value,
    MAX(timestamp) as last_event
FROM user_events 
WHERE timestamp > NOW() - INTERVAL '30 days'
GROUP BY date_trunc('day', timestamp), user_id;

-- 创建物化视图索引
CREATE INDEX idx_mv_daily_user_stats_date_user 
ON mv_daily_user_stats (date, user_id);

-- 定期刷新物化视图
CREATE OR REPLACE FUNCTION refresh_daily_user_stats()
RETURNS void AS $$
BEGIN
    REFRESH MATERIALIZED VIEW CONCURRENTLY mv_daily_user_stats;
END;
$$ LANGUAGE plpgsql;

-- 使用 cron 定期刷新
SELECT cron.schedule('refresh-daily-stats', '0 1 * * *', 'SELECT refresh_daily_user_stats();');
```

### 3. 分区表优化

#### 3.1 时间分区策略

```sql
-- 创建分区表
CREATE TABLE events (
    id BIGSERIAL,
    user_id BIGINT NOT NULL,
    event_type VARCHAR(50) NOT NULL,
    event_data JSONB,
    timestamp TIMESTAMPTZ NOT NULL,
    created_at TIMESTAMPTZ DEFAULT NOW()
) PARTITION BY RANGE (timestamp);

-- 创建月度分区
CREATE TABLE events_2025_01 PARTITION OF events
    FOR VALUES FROM ('2025-01-01') TO ('2025-02-01');

CREATE TABLE events_2025_02 PARTITION OF events
    FOR VALUES FROM ('2025-02-01') TO ('2025-03-01');

-- 为每个分区创建索引
CREATE INDEX idx_events_2025_01_user_timestamp 
ON events_2025_01 (user_id, timestamp DESC);

CREATE INDEX idx_events_2025_02_user_timestamp 
ON events_2025_02 (user_id, timestamp DESC);

-- 自动分区管理函数
CREATE OR REPLACE FUNCTION create_monthly_partition(table_name text, start_date date)
RETURNS void AS $$
DECLARE
    partition_name text;
    end_date date;
BEGIN
    partition_name := table_name || '_' || to_char(start_date, 'YYYY_MM');
    end_date := start_date + INTERVAL '1 month';
    
    EXECUTE format('CREATE TABLE IF NOT EXISTS %I PARTITION OF %I FOR VALUES FROM (%L) TO (%L)',
                   partition_name, table_name, start_date, end_date);
    
    -- 为新分区创建索引
    EXECUTE format('CREATE INDEX IF NOT EXISTS %I ON %I (user_id, timestamp DESC)',
                   'idx_' || partition_name || '_user_timestamp', partition_name);
END;
$$ LANGUAGE plpgsql;

-- 分区触发器
CREATE OR REPLACE FUNCTION events_partition_trigger()
RETURNS trigger AS $$
BEGIN
    PERFORM create_monthly_partition('events', date_trunc('month', NEW.timestamp)::date);
    RETURN NEW;
END;
$$ LANGUAGE plpgsql;

CREATE TRIGGER events_partition_trigger
    BEFORE INSERT ON events
    FOR EACH ROW EXECUTE FUNCTION events_partition_trigger();
```

## 🚀 缓存策略优化

### 1. Redis 缓存配置优化

#### 1.1 Redis 服务器配置

```bash
# redis.conf 优化配置

# 内存配置
maxmemory 8gb
maxmemory-policy allkeys-lru
maxmemory-samples 5

# 持久化配置
save 900 1
save 300 10
save 60 10000
stop-writes-on-bgsave-error yes
rdbcompression yes
rdbchecksum yes
dbfilename dump.rdb

# AOF 配置
appendonly yes
appendfilename "appendonly.aof"
appendfsync everysec
no-appendfsync-on-rewrite no
auto-aof-rewrite-percentage 100
auto-aof-rewrite-min-size 64mb

# 网络配置
tcp-keepalive 300
timeout 0
tcp-backlog 511

# 客户端配置
maxclients 10000

# 慢查询日志
slowlog-log-slower-than 10000
slowlog-max-len 128
```

#### 1.2 缓存策略实现

```rust
// src/cache/strategy.rs
use redis::{Client, Connection, Commands};
use serde::{Deserialize, Serialize};
use std::time::{Duration, Instant};
use std::collections::HashMap;
use tokio::sync::RwLock;

#[derive(Debug, Clone)]
pub enum CacheStrategy {
    WriteThrough,
    WriteBehind,
    WriteAround,
    CacheAside,
}

#[derive(Debug, Clone)]
pub struct CacheConfig {
    pub strategy: CacheStrategy,
    pub default_ttl: Duration,
    pub max_size: usize,
    pub eviction_policy: EvictionPolicy,
}

#[derive(Debug, Clone)]
pub enum EvictionPolicy {
    LRU,
    LFU,
    TTL,
    Random,
}

pub struct SmartCache {
    client: Client,
    connection: Arc<RwLock<Option<Connection>>>,
    config: CacheConfig,
    stats: Arc<RwLock<CacheStats>>,
}

#[derive(Debug, Default)]
pub struct CacheStats {
    pub hits: u64,
    pub misses: u64,
    pub sets: u64,
    pub deletes: u64,
    pub evictions: u64,
    pub total_requests: u64,
}

impl SmartCache {
    pub fn new(config: CacheConfig) -> Result<Self, redis::RedisError> {
        let client = Client::open("redis://localhost:6379")?;
        
        Ok(Self {
            client,
            connection: Arc::new(RwLock::new(None)),
            config,
            stats: Arc::new(RwLock::new(CacheStats::default())),
        })
    }

    // 智能缓存获取
    pub async fn get<T>(&self, key: &str) -> Result<Option<T>, redis::RedisError>
    where
        T: for<'de> Deserialize<'de>,
    {
        let start = Instant::now();
        let mut conn = self.get_connection().await?;
        
        let value: Option<String> = conn.get(key)?;
        
        let mut stats = self.stats.write().await;
        stats.total_requests += 1;
        
        match value {
            Some(v) => {
                stats.hits += 1;
                let deserialized: T = serde_json::from_str(&v)?;
                Ok(Some(deserialized))
            }
            None => {
                stats.misses += 1;
                Ok(None)
            }
        }
    }

    // 智能缓存设置
    pub async fn set<T>(&self, key: &str, value: &T, ttl: Option<Duration>) -> Result<(), redis::RedisError>
    where
        T: Serialize,
    {
        let mut conn = self.get_connection().await?;
        let serialized = serde_json::to_string(value)?;
        
        let ttl_seconds = ttl.unwrap_or(self.config.default_ttl).as_secs() as usize;
        
        match self.config.strategy {
            CacheStrategy::WriteThrough => {
                // 写入缓存和数据库
                conn.set_ex(key, &serialized, ttl_seconds)?;
                // 这里应该同时写入数据库
            }
            CacheStrategy::WriteBehind => {
                // 异步写入数据库
                conn.set_ex(key, &serialized, ttl_seconds)?;
                // 异步任务写入数据库
            }
            CacheStrategy::WriteAround => {
                // 只写入数据库，不写入缓存
                // 这里应该写入数据库
            }
            CacheStrategy::CacheAside => {
                // 只写入缓存
                conn.set_ex(key, &serialized, ttl_seconds)?;
            }
        }
        
        let mut stats = self.stats.write().await;
        stats.sets += 1;
        
        Ok(())
    }

    // 批量操作
    pub async fn mget<T>(&self, keys: &[String]) -> Result<Vec<Option<T>>, redis::RedisError>
    where
        T: for<'de> Deserialize<'de>,
    {
        let mut conn = self.get_connection().await?;
        let values: Vec<Option<String>> = conn.get(keys)?;
        
        let mut results = Vec::new();
        for value in values {
            match value {
                Some(v) => {
                    let deserialized: T = serde_json::from_str(&v)?;
                    results.push(Some(deserialized));
                }
                None => {
                    results.push(None);
                }
            }
        }
        
        Ok(results)
    }

    // 批量设置
    pub async fn mset<T>(&self, items: &[(String, T)], ttl: Option<Duration>) -> Result<(), redis::RedisError>
    where
        T: Serialize,
    {
        let mut conn = self.get_connection().await?;
        let ttl_seconds = ttl.unwrap_or(self.config.default_ttl).as_secs() as usize;
        
        for (key, value) in items {
            let serialized = serde_json::to_string(value)?;
            conn.set_ex(key, &serialized, ttl_seconds)?;
        }
        
        let mut stats = self.stats.write().await;
        stats.sets += items.len() as u64;
        
        Ok(())
    }

    // 获取缓存统计
    pub async fn get_stats(&self) -> CacheStats {
        self.stats.read().await.clone()
    }

    // 获取缓存命中率
    pub async fn get_hit_rate(&self) -> f64 {
        let stats = self.stats.read().await;
        if stats.total_requests == 0 {
            0.0
        } else {
            stats.hits as f64 / stats.total_requests as f64
        }
    }

    async fn get_connection(&self) -> Result<Connection, redis::RedisError> {
        let mut conn_guard = self.connection.write().await;
        
        if conn_guard.is_none() {
            let conn = self.client.get_connection()?;
            *conn_guard = Some(conn);
        }
        
        Ok(conn_guard.as_ref().unwrap().clone())
    }
}
```

### 2. 缓存预热策略

```rust
// src/cache/warmup.rs
use crate::cache::SmartCache;
use crate::database::DatabasePool;
use std::time::Duration;

pub struct CacheWarmup {
    cache: SmartCache,
    db_pool: DatabasePool,
}

impl CacheWarmup {
    pub fn new(cache: SmartCache, db_pool: DatabasePool) -> Self {
        Self { cache, db_pool }
    }

    // 预热热门数据
    pub async fn warmup_hot_data(&self) -> Result<(), Box<dyn std::error::Error>> {
        // 预热用户信息
        self.warmup_user_profiles().await?;
        
        // 预热配置数据
        self.warmup_config_data().await?;
        
        // 预热统计数据
        self.warmup_statistics().await?;
        
        Ok(())
    }

    async fn warmup_user_profiles(&self) -> Result<(), Box<dyn std::error::Error>> {
        let users = self.db_pool.with_connection(|conn| async move {
            sqlx::query("SELECT id, username, email, profile FROM users WHERE active = true LIMIT 1000")
                .fetch_all(conn)
                .await
                .map_err(crate::core::AppError::Database)
        }).await?;

        let mut cache_items = Vec::new();
        for user in users {
            let user_id: i32 = user.get("id");
            let username: String = user.get("username");
            let email: String = user.get("email");
            let profile: serde_json::Value = user.get("profile");
            
            let user_data = serde_json::json!({
                "id": user_id,
                "username": username,
                "email": email,
                "profile": profile
            });
            
            cache_items.push((format!("user:{}", user_id), user_data));
        }
        
        self.cache.mset(&cache_items, Some(Duration::from_secs(3600))).await?;
        Ok(())
    }

    async fn warmup_config_data(&self) -> Result<(), Box<dyn std::error::Error>> {
        let configs = self.db_pool.with_connection(|conn| async move {
            sqlx::query("SELECT key, value FROM system_configs WHERE active = true")
                .fetch_all(conn)
                .await
                .map_err(crate::core::AppError::Database)
        }).await?;

        let mut cache_items = Vec::new();
        for config in configs {
            let key: String = config.get("key");
            let value: serde_json::Value = config.get("value");
            cache_items.push((format!("config:{}", key), value));
        }
        
        self.cache.mset(&cache_items, Some(Duration::from_secs(7200))).await?;
        Ok(())
    }

    async fn warmup_statistics(&self) -> Result<(), Box<dyn std::error::Error>> {
        // 预热每日统计
        let daily_stats = self.db_pool.with_connection(|conn| async move {
            sqlx::query("
                SELECT 
                    date_trunc('day', timestamp) as date,
                    COUNT(*) as event_count,
                    COUNT(DISTINCT user_id) as unique_users
                FROM events 
                WHERE timestamp > NOW() - INTERVAL '7 days'
                GROUP BY date_trunc('day', timestamp)
                ORDER BY date DESC
            ")
            .fetch_all(conn)
            .await
            .map_err(crate::core::AppError::Database)
        }).await?;

        let mut cache_items = Vec::new();
        for stat in daily_stats {
            let date: chrono::NaiveDate = stat.get("date");
            let event_count: i64 = stat.get("event_count");
            let unique_users: i64 = stat.get("unique_users");
            
            let stat_data = serde_json::json!({
                "date": date,
                "event_count": event_count,
                "unique_users": unique_users
            });
            
            cache_items.push((format!("stats:daily:{}", date), stat_data));
        }
        
        self.cache.mset(&cache_items, Some(Duration::from_secs(1800))).await?;
        Ok(())
    }
}
```

## 💻 系统资源优化

### 1. 操作系统优化

#### 1.1 Linux 内核参数优化

```bash
# /etc/sysctl.conf 优化配置

# 网络优化
net.core.rmem_default = 262144
net.core.rmem_max = 16777216
net.core.wmem_default = 262144
net.core.wmem_max = 16777216
net.core.netdev_max_backlog = 5000
net.ipv4.tcp_rmem = 4096 65536 16777216
net.ipv4.tcp_wmem = 4096 65536 16777216
net.ipv4.tcp_congestion_control = bbr

# 内存优化
vm.swappiness = 10
vm.dirty_ratio = 15
vm.dirty_background_ratio = 5
vm.dirty_expire_centisecs = 3000
vm.dirty_writeback_centisecs = 500

# 文件系统优化
fs.file-max = 2097152
fs.nr_open = 1048576

# 进程优化
kernel.pid_max = 4194304
kernel.threads-max = 2097152
```

#### 1.2 系统限制优化

```bash
# /etc/security/limits.conf
postgres soft nofile 65536
postgres hard nofile 65536
postgres soft nproc 32768
postgres hard nproc 32768
postgres soft memlock unlimited
postgres hard memlock unlimited

# /etc/systemd/system/postgresql.service.d/override.conf
[Service]
LimitNOFILE=65536
LimitNPROC=32768
LimitMEMLOCK=infinity
```

### 2. 硬件优化建议

#### 2.1 CPU 优化

```text
推荐配置：
- CPU: Intel Xeon Gold 6248R (24核48线程) 或 AMD EPYC 7542 (32核64线程)
- 频率: 3.0GHz+ 基础频率
- 缓存: 32MB+ L3缓存
- 架构: 支持AVX-512指令集

优化建议：
- 启用CPU性能模式
- 关闭不必要的CPU节能功能
- 使用CPU亲和性绑定PostgreSQL进程
```

#### 2.2 内存优化

```text
推荐配置：
- 内存: 64GB+ DDR4-3200 ECC内存
- 内存通道: 8通道配置
- 内存类型: 企业级ECC内存

优化建议：
- 配置大页面支持
- 启用内存压缩
- 优化NUMA配置
```

#### 2.3 存储优化

```text
推荐配置：
- 主存储: NVMe SSD (如Intel P5510 3.84TB)
- 备份存储: SATA SSD 或 HDD
- 存储接口: PCIe 4.0 x4

优化建议：
- 使用RAID 1配置保证数据安全
- 启用TRIM支持
- 优化I/O调度器
```

## 📊 监控和调优

### 1. 性能监控指标

#### 1.1 数据库性能指标

```sql
-- 查询性能监控
SELECT 
    query,
    calls,
    total_time,
    mean_time,
    stddev_time,
    rows,
    100.0 * shared_blks_hit / nullif(shared_blks_hit + shared_blks_read, 0) AS hit_percent
FROM pg_stat_statements 
ORDER BY total_time DESC 
LIMIT 10;

-- 连接监控
SELECT 
    state,
    count(*) as connections
FROM pg_stat_activity 
GROUP BY state;

-- 锁监控
SELECT 
    mode,
    count(*) as locks
FROM pg_locks 
GROUP BY mode;

-- 索引使用监控
SELECT 
    schemaname,
    tablename,
    indexname,
    idx_tup_read,
    idx_tup_fetch
FROM pg_stat_user_indexes 
ORDER BY idx_tup_read DESC;
```

#### 1.2 系统资源监控

```bash
# CPU 使用率监控
top -p $(pgrep postgres)

# 内存使用监控
free -h
cat /proc/meminfo

# I/O 监控
iostat -x 1
iotop -p $(pgrep postgres)

# 网络监控
netstat -i
ss -tuln
```

### 2. 自动化调优脚本

#### 2.1 性能分析脚本

```bash
#!/bin/bash
# performance_analysis.sh

echo "=== PostgreSQL 性能分析报告 ==="
echo "生成时间: $(date)"
echo

# 数据库连接数
echo "=== 数据库连接数 ==="
psql -c "SELECT count(*) as total_connections FROM pg_stat_activity;"

# 慢查询分析
echo "=== 慢查询分析 ==="
psql -c "
SELECT 
    query,
    calls,
    total_time,
    mean_time,
    rows
FROM pg_stat_statements 
WHERE mean_time > 1000
ORDER BY mean_time DESC 
LIMIT 5;
"

# 缓存命中率
echo "=== 缓存命中率 ==="
psql -c "
SELECT 
    round(100.0 * sum(blks_hit) / (sum(blks_hit) + sum(blks_read)), 2) as cache_hit_ratio
FROM pg_stat_database;
"

# 索引使用情况
echo "=== 索引使用情况 ==="
psql -c "
SELECT 
    schemaname,
    tablename,
    indexname,
    idx_tup_read,
    idx_tup_fetch
FROM pg_stat_user_indexes 
WHERE idx_tup_read > 0
ORDER BY idx_tup_read DESC 
LIMIT 10;
"

# 表大小分析
echo "=== 表大小分析 ==="
psql -c "
SELECT 
    schemaname,
    tablename,
    pg_size_pretty(pg_total_relation_size(schemaname||'.'||tablename)) as size
FROM pg_tables 
WHERE schemaname = 'public'
ORDER BY pg_total_relation_size(schemaname||'.'||tablename) DESC 
LIMIT 10;
"
```

#### 2.2 自动调优脚本

```bash
#!/bin/bash
# auto_tuning.sh

echo "=== PostgreSQL 自动调优 ==="

# 检查当前配置
echo "检查当前配置..."
psql -c "SHOW shared_buffers;"
psql -c "SHOW work_mem;"
psql -c "SHOW maintenance_work_mem;"

# 获取系统内存信息
TOTAL_MEM=$(free -m | awk 'NR==2{printf "%.0f", $2}')
SHARED_BUFFERS=$((TOTAL_MEM * 25 / 100))
WORK_MEM=$((TOTAL_MEM * 5 / 100))
MAINTENANCE_WORK_MEM=$((TOTAL_MEM * 10 / 100))

echo "系统总内存: ${TOTAL_MEM}MB"
echo "建议 shared_buffers: ${SHARED_BUFFERS}MB"
echo "建议 work_mem: ${WORK_MEM}MB"
echo "建议 maintenance_work_mem: ${MAINTENANCE_WORK_MEM}MB"

# 生成优化配置
cat > /tmp/postgresql_optimized.conf << EOF
# 自动生成的优化配置
shared_buffers = ${SHARED_BUFFERS}MB
work_mem = ${WORK_MEM}MB
maintenance_work_mem = ${MAINTENANCE_WORK_MEM}MB
effective_cache_size = $((TOTAL_MEM * 75 / 100))MB
max_connections = 200
random_page_cost = 1.1
effective_io_concurrency = 200
checkpoint_completion_target = 0.9
wal_buffers = 16MB
default_statistics_target = 100
EOF

echo "优化配置已生成: /tmp/postgresql_optimized.conf"
echo "请手动应用配置并重启PostgreSQL服务"
```

## 📋 总结

本文档提供了PostgreSQL All-in-One架构的全面性能优化指南，包括：

### 1. 数据库配置优化

- **内存配置**: 合理分配共享缓冲区和工作内存
- **连接配置**: 优化并发连接和连接池设置
- **I/O配置**: SSD优化和检查点配置
- **查询优化**: 规划器参数和并行查询配置

### 2. 查询性能优化

- **索引优化**: 复合索引、部分索引、表达式索引
- **查询重写**: OLTP和OLAP查询优化
- **分区优化**: 时间分区和自动分区管理

### 3. 缓存策略优化

- **Redis配置**: 内存管理和持久化配置
- **缓存策略**: 多种缓存模式实现
- **缓存预热**: 智能数据预热机制

### 4. 系统资源优化

- **操作系统**: 内核参数和系统限制优化
- **硬件配置**: CPU、内存、存储优化建议
- **监控调优**: 性能指标监控和自动化调优

通过系统性的性能优化，PostgreSQL All-in-One架构能够在高负载下保持优异的性能表现，满足中小型团队的数据处理需求。
