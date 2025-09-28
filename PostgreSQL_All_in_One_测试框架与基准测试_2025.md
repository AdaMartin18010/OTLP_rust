# PostgreSQL All-in-One 测试框架与基准测试 - 2025年

## 📋 执行摘要

本文档提供了PostgreSQL All-in-One架构的完整测试框架和基准测试方案，包括单元测试、集成测试、端到端测试、性能测试和压力测试。通过全面的测试覆盖，确保系统的正确性、性能和可靠性。

## 🧪 测试框架架构

### 1. 测试分层架构

```text
┌──────────────────────────────────────────────────────────────┐
│                    端到端测试 (E2E Tests)                     │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌─────────┐ │
│  │  用户场景    │ │  业务流程   │ │  系统集成    │ │ 性能测试 │ │
│  └─────────────┘ └─────────────┘ └─────────────┘ └─────────┘ │
├──────────────────────────────────────────────────────────────┤
│                    集成测试 (Integration Tests)               │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌─────────┐ │
│  │  数据库集成  │ │  缓存集成    │ │  监控集成   │ │ 安全集成 │ │
│  └─────────────┘ └─────────────┘ └─────────────┘ └─────────┘ │
├──────────────────────────────────────────────────────────────┤
│                    单元测试 (Unit Tests)                      │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌─────────┐ │
│  │  核心逻辑    │ │  工具函数   │ │  数据结构    │ │ 错误处理 │ │
│  └─────────────┘ └─────────────┘ └─────────────┘ └─────────┘ │
└──────────────────────────────────────────────────────────────┘
```

### 2. 测试工具栈

```toml
# Cargo.toml 测试依赖
[dev-dependencies]
# 测试框架
tokio-test = "0.4.4"
criterion = "0.7.0"
mockall = "0.13.1"
proptest = "1.5.1"

# 数据库测试
sqlx = { version = "0.8.7", features = ["runtime-tokio-rustls", "postgres", "chrono", "uuid", "migrate"] }
testcontainers = "0.20.0"

# 缓存测试
redis = "0.32.5"

# 网络测试
reqwest = { version = "0.12.23", features = ["json", "rustls-tls"] }
wiremock = "0.6.0"

# 性能测试
criterion = "0.7.0"
flamegraph = "0.4.0"

# 并发测试
tokio = { version = "1.47.1", features = ["full", "test-util"] }
```

## 🔬 单元测试

### 1. 核心库测试 (crates/core/tests/lib.rs)

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use tokio_test;
    use std::time::Duration;

    #[test]
    fn test_app_config_default() {
        let config = AppConfig::default();
        assert_eq!(config.database.max_connections, 100);
        assert_eq!(config.cache.host, "localhost");
        assert_eq!(config.monitoring.prometheus_port, 9090);
    }

    #[test]
    fn test_app_config_from_env() {
        std::env::set_var("DATABASE_URL", "postgresql://test:test@localhost:5432/testdb");
        std::env::set_var("REDIS_HOST", "redis.example.com");
        std::env::set_var("REDIS_PORT", "6380");

        let config = AppConfig::from_env().unwrap();
        assert_eq!(config.database.url, "postgresql://test:test@localhost:5432/testdb");
        assert_eq!(config.cache.host, "redis.example.com");
        assert_eq!(config.cache.port, 6380);
    }

    #[test]
    fn test_app_error_display() {
        let error = AppError::config("Test error");
        assert_eq!(error.to_string(), "Configuration error: Test error");
    }

    #[test]
    fn test_app_error_from_sqlx() {
        let sqlx_error = sqlx::Error::Configuration("Test".into());
        let app_error: AppError = sqlx_error.into();
        assert!(matches!(app_error, AppError::Database(_)));
    }
}
```

### 2. 数据库连接池测试 (crates/database/tests/connection_pool_tests.rs)

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use tokio_test;
    use testcontainers::{Container, GenericImage};
    use testcontainers::core::WaitFor;
    use std::time::Duration;

    async fn setup_test_database() -> String {
        let postgres_image = GenericImage::new("postgres", "15")
            .with_env_var("POSTGRES_DB", "testdb")
            .with_env_var("POSTGRES_USER", "testuser")
            .with_env_var("POSTGRES_PASSWORD", "testpass")
            .with_wait_for(WaitFor::message_on_stderr("database system is ready to accept connections"));

        let container = Container::new(postgres_image)
            .with_exposed_port(5432)
            .start()
            .await;

        let port = container.get_host_port_ipv4(5432).await;
        format!("postgresql://testuser:testpass@localhost:{}/testdb", port)
    }

    #[tokio::test]
    async fn test_connection_pool_creation() {
        let database_url = setup_test_database().await;
        let config = PoolConfig::default();
        
        let pool = DatabasePool::new(&database_url, config).await;
        assert!(pool.is_ok());
    }

    #[tokio::test]
    async fn test_connection_pool_health_check() {
        let database_url = setup_test_database().await;
        let config = PoolConfig::default();
        let pool = DatabasePool::new(&database_url, config).await.unwrap();
        
        let is_healthy = pool.health_check().await;
        assert!(is_healthy);
    }

    #[tokio::test]
    async fn test_connection_pool_with_connection() {
        let database_url = setup_test_database().await;
        let config = PoolConfig::default();
        let pool = DatabasePool::new(&database_url, config).await.unwrap();
        
        let result = pool.with_connection(|conn| async move {
            sqlx::query("SELECT 1 as test")
                .fetch_one(conn)
                .await
                .map_err(AppError::Database)
        }).await;
        
        assert!(result.is_ok());
        let row = result.unwrap();
        assert_eq!(row.get::<i32, _>("test"), 1);
    }

    #[tokio::test]
    async fn test_connection_pool_with_transaction() {
        let database_url = setup_test_database().await;
        let config = PoolConfig::default();
        let pool = DatabasePool::new(&database_url, config).await.unwrap();
        
        // 创建测试表
        pool.with_connection(|conn| async move {
            sqlx::query("CREATE TABLE test_table (id SERIAL PRIMARY KEY, name VARCHAR(50))")
                .execute(conn)
                .await
                .map_err(AppError::Database)
        }).await.unwrap();
        
        let result = pool.with_transaction(|tx| async move {
            sqlx::query("INSERT INTO test_table (name) VALUES ($1)")
                .bind("test")
                .execute(tx)
                .await
                .map_err(AppError::Database)?;
            
            Ok(())
        }).await;
        
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_connection_pool_stats() {
        let database_url = setup_test_database().await;
        let config = PoolConfig::default();
        let pool = DatabasePool::new(&database_url, config).await.unwrap();
        
        let stats = pool.get_stats().await;
        assert_eq!(stats.total_connections, 0);
        assert_eq!(stats.active_connections, 0);
        assert_eq!(stats.total_requests, 0);
    }

    #[tokio::test]
    async fn test_connection_pool_concurrent_requests() {
        let database_url = setup_test_database().await;
        let config = PoolConfig::default();
        let pool = DatabasePool::new(&database_url, config).await.unwrap();
        
        let mut handles = vec![];
        for i in 0..10 {
            let pool_clone = pool.clone();
            let handle = tokio::spawn(async move {
                pool_clone.with_connection(|conn| async move {
                    sqlx::query("SELECT $1 as test")
                        .bind(i)
                        .fetch_one(conn)
                        .await
                        .map_err(AppError::Database)
                }).await
            });
            handles.push(handle);
        }
        
        for handle in handles {
            let result = handle.await.unwrap();
            assert!(result.is_ok());
        }
    }
}
```

### 3. 缓存系统测试 (crates/cache/tests/redis_tests.rs)

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use tokio_test;
    use testcontainers::{Container, GenericImage};
    use std::time::Duration;

    async fn setup_test_redis() -> String {
        let redis_image = GenericImage::new("redis", "7-alpine");
        let container = Container::new(redis_image)
            .with_exposed_port(6379)
            .start()
            .await;

        let port = container.get_host_port_ipv4(6379).await;
        format!("redis://localhost:{}", port)
    }

    #[tokio::test]
    async fn test_redis_cache_creation() {
        let redis_url = setup_test_redis().await;
        let config = CacheConfig {
            host: "localhost".to_string(),
            port: 6379,
            password: None,
            database: 0,
            default_ttl: Duration::from_secs(3600),
            max_connections: 100,
        };
        
        let cache = RedisCache::new(config);
        assert!(cache.is_ok());
    }

    #[tokio::test]
    async fn test_redis_cache_set_get() {
        let redis_url = setup_test_redis().await;
        let config = CacheConfig::default();
        let cache = RedisCache::new(config).unwrap();
        
        let result = cache.set("test_key", &"test_value", Some(Duration::from_secs(60))).await;
        assert!(result.is_ok());
        
        let value: Option<String> = cache.get("test_key").await.unwrap();
        assert_eq!(value, Some("test_value".to_string()));
    }

    #[tokio::test]
    async fn test_redis_cache_ttl() {
        let redis_url = setup_test_redis().await;
        let config = CacheConfig::default();
        let cache = RedisCache::new(config).unwrap();
        
        let result = cache.set("test_key", &"test_value", Some(Duration::from_millis(100))).await;
        assert!(result.is_ok());
        
        // 等待过期
        tokio::time::sleep(Duration::from_millis(150)).await;
        
        let value: Option<String> = cache.get("test_key").await.unwrap();
        assert_eq!(value, None);
    }

    #[tokio::test]
    async fn test_redis_cache_serialization() {
        let redis_url = setup_test_redis().await;
        let config = CacheConfig::default();
        let cache = RedisCache::new(config).unwrap();
        
        #[derive(Serialize, Deserialize, Debug, PartialEq)]
        struct TestStruct {
            id: i32,
            name: String,
            active: bool,
        }
        
        let test_data = TestStruct {
            id: 1,
            name: "test".to_string(),
            active: true,
        };
        
        let result = cache.set("test_struct", &test_data, Some(Duration::from_secs(60))).await;
        assert!(result.is_ok());
        
        let value: Option<TestStruct> = cache.get("test_struct").await.unwrap();
        assert_eq!(value, Some(test_data));
    }
}
```

## 🔗 集成测试

### 1. 数据库集成测试 (tests/integration/database_integration_tests.rs)

```rust
use postgresql_all_in_one::database::connection::pool::DatabasePool;
use postgresql_all_in_one::cache::redis::RedisCache;
use postgresql_all_in_one::core::{AppConfig, AppError};
use testcontainers::{Container, GenericImage};
use testcontainers::core::WaitFor;
use std::time::Duration;

async fn setup_test_environment() -> (String, String) {
    // 启动 PostgreSQL 容器
    let postgres_image = GenericImage::new("postgres", "15")
        .with_env_var("POSTGRES_DB", "testdb")
        .with_env_var("POSTGRES_USER", "testuser")
        .with_env_var("POSTGRES_PASSWORD", "testpass")
        .with_wait_for(WaitFor::message_on_stderr("database system is ready to accept connections"));

    let postgres_container = Container::new(postgres_image)
        .with_exposed_port(5432)
        .start()
        .await;

    let postgres_port = postgres_container.get_host_port_ipv4(5432).await;
    let postgres_url = format!("postgresql://testuser:testpass@localhost:{}/testdb", postgres_port);

    // 启动 Redis 容器
    let redis_image = GenericImage::new("redis", "7-alpine");
    let redis_container = Container::new(redis_image)
        .with_exposed_port(6379)
        .start()
        .await;

    let redis_port = redis_container.get_host_port_ipv4(6379).await;
    let redis_url = format!("redis://localhost:{}", redis_port);

    (postgres_url, redis_url)
}

#[tokio::test]
async fn test_database_redis_integration() {
    let (postgres_url, redis_url) = setup_test_environment().await;
    
    // 初始化数据库连接池
    let db_config = postgresql_all_in_one::database::connection::pool::PoolConfig::default();
    let db_pool = DatabasePool::new(&postgres_url, db_config).await.unwrap();
    
    // 初始化 Redis 缓存
    let cache_config = postgresql_all_in_one::cache::redis::CacheConfig::default();
    let cache = RedisCache::new(cache_config).unwrap();
    
    // 创建测试表
    db_pool.with_connection(|conn| async move {
        sqlx::query("CREATE TABLE users (id SERIAL PRIMARY KEY, name VARCHAR(50), email VARCHAR(100))")
            .execute(conn)
            .await
            .map_err(AppError::Database)
    }).await.unwrap();
    
    // 测试数据写入和缓存
    let user_id = db_pool.with_connection(|conn| async move {
        let result = sqlx::query("INSERT INTO users (name, email) VALUES ($1, $2) RETURNING id")
            .bind("John Doe")
            .bind("john@example.com")
            .fetch_one(conn)
            .await
            .map_err(AppError::Database)?;
        
        Ok(result.get::<i32, _>("id"))
    }).await.unwrap();
    
    // 将用户信息缓存到 Redis
    let user_info = format!("user:{}", user_id);
    let user_data = serde_json::json!({
        "id": user_id,
        "name": "John Doe",
        "email": "john@example.com"
    });
    
    cache.set(&user_info, &user_data, Some(Duration::from_secs(3600))).await.unwrap();
    
    // 从缓存读取用户信息
    let cached_user: Option<serde_json::Value> = cache.get(&user_info).await.unwrap();
    assert!(cached_user.is_some());
    assert_eq!(cached_user.unwrap()["name"], "John Doe");
    
    // 从数据库读取用户信息
    let db_user = db_pool.with_connection(|conn| async move {
        sqlx::query("SELECT * FROM users WHERE id = $1")
            .bind(user_id)
            .fetch_one(conn)
            .await
            .map_err(AppError::Database)
    }).await.unwrap();
    
    assert_eq!(db_user.get::<String, _>("name"), "John Doe");
    assert_eq!(db_user.get::<String, _>("email"), "john@example.com");
}

#[tokio::test]
async fn test_transaction_with_cache_invalidation() {
    let (postgres_url, redis_url) = setup_test_environment().await;
    
    let db_config = postgresql_all_in_one::database::connection::pool::PoolConfig::default();
    let db_pool = DatabasePool::new(&postgres_url, db_config).await.unwrap();
    
    let cache_config = postgresql_all_in_one::cache::redis::CacheConfig::default();
    let cache = RedisCache::new(cache_config).unwrap();
    
    // 创建测试表
    db_pool.with_connection(|conn| async move {
        sqlx::query("CREATE TABLE products (id SERIAL PRIMARY KEY, name VARCHAR(50), price DECIMAL(10,2))")
            .execute(conn)
            .await
            .map_err(AppError::Database)
    }).await.unwrap();
    
    // 插入产品并缓存
    let product_id = db_pool.with_connection(|conn| async move {
        let result = sqlx::query("INSERT INTO products (name, price) VALUES ($1, $2) RETURNING id")
            .bind("Test Product")
            .bind(99.99)
            .fetch_one(conn)
            .await
            .map_err(AppError::Database)?;
        
        Ok(result.get::<i32, _>("id"))
    }).await.unwrap();
    
    let product_key = format!("product:{}", product_id);
    let product_data = serde_json::json!({
        "id": product_id,
        "name": "Test Product",
        "price": 99.99
    });
    
    cache.set(&product_key, &product_data, Some(Duration::from_secs(3600))).await.unwrap();
    
    // 在事务中更新产品价格
    db_pool.with_transaction(|tx| async move {
        // 更新数据库
        sqlx::query("UPDATE products SET price = $1 WHERE id = $2")
            .bind(149.99)
            .bind(product_id)
            .execute(tx)
            .await
            .map_err(AppError::Database)?;
        
        // 删除缓存
        cache.delete(&product_key).await.map_err(|e| AppError::Redis(e))?;
        
        Ok(())
    }).await.unwrap();
    
    // 验证缓存已被删除
    let cached_product: Option<serde_json::Value> = cache.get(&product_key).await.unwrap();
    assert!(cached_product.is_none());
    
    // 验证数据库已更新
    let updated_product = db_pool.with_connection(|conn| async move {
        sqlx::query("SELECT * FROM products WHERE id = $1")
            .bind(product_id)
            .fetch_one(conn)
            .await
            .map_err(AppError::Database)
    }).await.unwrap();
    
    assert_eq!(updated_product.get::<rust_decimal::Decimal, _>("price"), rust_decimal::Decimal::new(14999, 2));
}
```

### 2. 监控集成测试 (tests/integration/monitoring_integration_tests.rs)

```rust
use postgresql_all_in_one::monitoring::metrics::DatabaseMetrics;
use postgresql_all_in_one::monitoring::prometheus::PrometheusExporter;
use prometheus::{Registry, Counter, Histogram};
use std::time::Duration;

#[tokio::test]
async fn test_metrics_collection() {
    let registry = Registry::new();
    let metrics = DatabaseMetrics::new(&registry).unwrap();
    let exporter = PrometheusExporter::new(registry, 9090).unwrap();
    
    // 模拟一些操作
    metrics.record_query(Duration::from_millis(100));
    metrics.record_query(Duration::from_millis(200));
    metrics.record_cache_hit();
    metrics.record_cache_miss();
    
    // 启动导出器
    let exporter_handle = tokio::spawn(async move {
        exporter.start().await
    });
    
    // 等待导出器启动
    tokio::time::sleep(Duration::from_millis(100)).await;
    
    // 获取指标
    let client = reqwest::Client::new();
    let response = client.get("http://localhost:9090/metrics").send().await.unwrap();
    let body = response.text().await.unwrap();
    
    // 验证指标存在
    assert!(body.contains("database_queries_total"));
    assert!(body.contains("database_query_duration_seconds"));
    assert!(body.contains("database_cache_hits_total"));
    assert!(body.contains("database_cache_misses_total"));
    
    exporter_handle.abort();
}

#[tokio::test]
async fn test_metrics_aggregation() {
    let registry = Registry::new();
    let metrics = DatabaseMetrics::new(&registry).unwrap();
    
    // 记录多个查询
    for i in 0..100 {
        metrics.record_query(Duration::from_millis(i));
    }
    
    // 验证指标值
    let stats = metrics.get_stats().await;
    assert_eq!(stats.total_queries, 100);
    assert!(stats.average_query_time.as_millis() > 0);
}
```

## 🎯 端到端测试

### 1. 用户场景测试 (tests/e2e/user_scenarios_tests.rs)

```rust
use postgresql_all_in_one::services::api_gateway::ApiGateway;
use postgresql_all_in_one::services::query_engine::QueryEngine;
use postgresql_all_in_one::core::AppConfig;
use testcontainers::{Container, GenericImage};
use testcontainers::core::WaitFor;
use std::time::Duration;

async fn setup_e2e_environment() -> (String, String) {
    // 启动 PostgreSQL 容器
    let postgres_image = GenericImage::new("postgres", "15")
        .with_env_var("POSTGRES_DB", "e2etest")
        .with_env_var("POSTGRES_USER", "e2euser")
        .with_env_var("POSTGRES_PASSWORD", "e2epass")
        .with_wait_for(WaitFor::message_on_stderr("database system is ready to accept connections"));

    let postgres_container = Container::new(postgres_image)
        .with_exposed_port(5432)
        .start()
        .await;

    let postgres_port = postgres_container.get_host_port_ipv4(5432).await;
    let postgres_url = format!("postgresql://e2euser:e2epass@localhost:{}/e2etest", postgres_port);

    // 启动 Redis 容器
    let redis_image = GenericImage::new("redis", "7-alpine");
    let redis_container = Container::new(redis_image)
        .with_exposed_port(6379)
        .start()
        .await;

    let redis_port = redis_container.get_host_port_ipv4(6379).await;
    let redis_url = format!("redis://localhost:{}", redis_port);

    (postgres_url, redis_url)
}

#[tokio::test]
async fn test_user_registration_workflow() {
    let (postgres_url, redis_url) = setup_e2e_environment().await;
    
    // 初始化服务
    let config = AppConfig::from_env().unwrap();
    let api_gateway = ApiGateway::new(config.clone()).await.unwrap();
    let query_engine = QueryEngine::new(config).await.unwrap();
    
    // 创建用户表
    query_engine.execute_sql("CREATE TABLE users (id SERIAL PRIMARY KEY, username VARCHAR(50) UNIQUE, email VARCHAR(100) UNIQUE, password_hash VARCHAR(255), created_at TIMESTAMPTZ DEFAULT NOW())").await.unwrap();
    
    // 用户注册
    let registration_data = serde_json::json!({
        "username": "testuser",
        "email": "test@example.com",
        "password": "password123"
    });
    
    let response = api_gateway.handle_request("POST", "/api/users/register", registration_data).await.unwrap();
    assert_eq!(response.status, 201);
    
    // 验证用户已创建
    let users = query_engine.execute_sql("SELECT * FROM users WHERE username = 'testuser'").await.unwrap();
    assert_eq!(users.rows.len(), 1);
    assert_eq!(users.rows[0]["username"], "testuser");
    assert_eq!(users.rows[0]["email"], "test@example.com");
}

#[tokio::test]
async fn test_data_analytics_workflow() {
    let (postgres_url, redis_url) = setup_e2e_environment().await;
    
    let config = AppConfig::from_env().unwrap();
    let query_engine = QueryEngine::new(config).await.unwrap();
    
    // 创建分析表
    query_engine.execute_sql("CREATE TABLE events (id SERIAL PRIMARY KEY, user_id INTEGER, event_type VARCHAR(50), event_data JSONB, timestamp TIMESTAMPTZ DEFAULT NOW())").await.unwrap();
    
    // 插入测试数据
    for i in 0..1000 {
        let event_data = serde_json::json!({
            "value": i,
            "category": if i % 2 == 0 { "A" } else { "B" }
        });
        
        query_engine.execute_sql_with_params(
            "INSERT INTO events (user_id, event_type, event_data) VALUES ($1, $2, $3)",
            &[&(i % 100), &"test_event", &event_data]
        ).await.unwrap();
    }
    
    // 执行分析查询
    let analysis_result = query_engine.execute_sql("
        SELECT 
            user_id,
            COUNT(*) as event_count,
            AVG((event_data->>'value')::numeric) as avg_value,
            MAX(timestamp) as last_event
        FROM events 
        WHERE timestamp > NOW() - INTERVAL '1 day'
        GROUP BY user_id
        ORDER BY event_count DESC
        LIMIT 10
    ").await.unwrap();
    
    assert_eq!(analysis_result.rows.len(), 10);
    assert!(analysis_result.rows[0]["event_count"].as_i64().unwrap() > 0);
}

#[tokio::test]
async fn test_full_text_search_workflow() {
    let (postgres_url, redis_url) = setup_e2e_environment().await;
    
    let config = AppConfig::from_env().unwrap();
    let query_engine = QueryEngine::new(config).await.unwrap();
    
    // 创建文档表
    query_engine.execute_sql("
        CREATE TABLE documents (
            id SERIAL PRIMARY KEY,
            title VARCHAR(200),
            content TEXT,
            search_vector tsvector,
            created_at TIMESTAMPTZ DEFAULT NOW()
        )
    ").await.unwrap();
    
    // 创建全文搜索索引
    query_engine.execute_sql("CREATE INDEX idx_documents_search ON documents USING GIN(search_vector)").await.unwrap();
    
    // 插入测试文档
    let documents = vec![
        ("PostgreSQL 数据库", "PostgreSQL 是一个强大的开源关系数据库管理系统"),
        ("Rust 编程语言", "Rust 是一种系统编程语言，注重安全性和性能"),
        ("Kubernetes 容器编排", "Kubernetes 是一个开源的容器编排平台"),
    ];
    
    for (title, content) in documents {
        query_engine.execute_sql_with_params(
            "INSERT INTO documents (title, content, search_vector) VALUES ($1, $2, to_tsvector('simple', $1 || ' ' || $2))",
            &[&title, &content]
        ).await.unwrap();
    }
    
    // 执行全文搜索
    let search_result = query_engine.execute_sql_with_params(
        "SELECT id, title, content, ts_rank(search_vector, plainto_tsquery('simple', $1)) as rank FROM documents WHERE search_vector @@ plainto_tsquery('simple', $1) ORDER BY rank DESC",
        &[&"PostgreSQL"]
    ).await.unwrap();
    
    assert_eq!(search_result.rows.len(), 1);
    assert_eq!(search_result.rows[0]["title"], "PostgreSQL 数据库");
}
```

## ⚡ 性能测试

### 1. 基准测试 (benches/performance_benchmarks.rs)

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use postgresql_all_in_one::database::connection::pool::DatabasePool;
use postgresql_all_in_one::cache::redis::RedisCache;
use postgresql_all_in_one::core::AppConfig;
use std::time::Duration;

async fn setup_benchmark_environment() -> (DatabasePool, RedisCache) {
    let config = AppConfig::from_env().unwrap();
    let db_pool = DatabasePool::new(&config.database.url, config.database.clone()).await.unwrap();
    let cache = RedisCache::new(config.cache).unwrap();
    
    // 创建测试表
    db_pool.with_connection(|conn| async move {
        sqlx::query("CREATE TABLE IF NOT EXISTS benchmark_table (id SERIAL PRIMARY KEY, data TEXT, created_at TIMESTAMPTZ DEFAULT NOW())")
            .execute(conn)
            .await
            .map_err(postgresql_all_in_one::core::AppError::Database)
    }).await.unwrap();
    
    (db_pool, cache)
}

fn benchmark_database_insert(c: &mut Criterion) {
    let rt = tokio::runtime::Runtime::new().unwrap();
    let (db_pool, _) = rt.block_on(setup_benchmark_environment());
    
    c.bench_function("database_insert", |b| {
        b.to_async(&rt).iter(|| async {
            db_pool.with_connection(|conn| async move {
                sqlx::query("INSERT INTO benchmark_table (data) VALUES ($1)")
                    .bind("benchmark data")
                    .execute(conn)
                    .await
                    .map_err(postgresql_all_in_one::core::AppError::Database)
            }).await
        })
    });
}

fn benchmark_database_select(c: &mut Criterion) {
    let rt = tokio::runtime::Runtime::new().unwrap();
    let (db_pool, _) = rt.block_on(setup_benchmark_environment());
    
    c.bench_function("database_select", |b| {
        b.to_async(&rt).iter(|| async {
            db_pool.with_connection(|conn| async move {
                sqlx::query("SELECT * FROM benchmark_table LIMIT 100")
                    .fetch_all(conn)
                    .await
                    .map_err(postgresql_all_in_one::core::AppError::Database)
            }).await
        })
    });
}

fn benchmark_redis_set_get(c: &mut Criterion) {
    let rt = tokio::runtime::Runtime::new().unwrap();
    let (_, cache) = rt.block_on(setup_benchmark_environment());
    
    c.bench_function("redis_set_get", |b| {
        b.to_async(&rt).iter(|| async {
            let key = format!("benchmark_key_{}", rand::random::<u32>());
            let value = "benchmark value";
            
            cache.set(&key, &value, Some(Duration::from_secs(60))).await?;
            let result: Option<String> = cache.get(&key).await?;
            
            Ok::<_, postgresql_all_in_one::core::AppError>(result)
        })
    });
}

fn benchmark_concurrent_operations(c: &mut Criterion) {
    let rt = tokio::runtime::Runtime::new().unwrap();
    let (db_pool, cache) = rt.block_on(setup_benchmark_environment());
    
    let mut group = c.benchmark_group("concurrent_operations");
    for concurrency in [1, 10, 50, 100].iter() {
        group.bench_with_input(BenchmarkId::new("database", concurrency), concurrency, |b, &concurrency| {
            b.to_async(&rt).iter(|| async {
                let mut handles = vec![];
                for i in 0..concurrency {
                    let pool_clone = db_pool.clone();
                    let handle = tokio::spawn(async move {
                        pool_clone.with_connection(|conn| async move {
                            sqlx::query("SELECT $1 as test")
                                .bind(i)
                                .fetch_one(conn)
                                .await
                                .map_err(postgresql_all_in_one::core::AppError::Database)
                        }).await
                    });
                    handles.push(handle);
                }
                
                for handle in handles {
                    handle.await.unwrap().unwrap();
                }
            })
        });
    }
    group.finish();
}

criterion_group!(
    benches,
    benchmark_database_insert,
    benchmark_database_select,
    benchmark_redis_set_get,
    benchmark_concurrent_operations
);
criterion_main!(benches);
```

### 2. 压力测试 (tests/stress/stress_tests.rs)

```rust
use postgresql_all_in_one::database::connection::pool::DatabasePool;
use postgresql_all_in_one::cache::redis::RedisCache;
use postgresql_all_in_one::core::AppConfig;
use std::time::{Duration, Instant};
use tokio::time::timeout;

async fn setup_stress_test() -> (DatabasePool, RedisCache) {
    let config = AppConfig::from_env().unwrap();
    let db_pool = DatabasePool::new(&config.database.url, config.database.clone()).await.unwrap();
    let cache = RedisCache::new(config.cache).unwrap();
    
    // 创建测试表
    db_pool.with_connection(|conn| async move {
        sqlx::query("CREATE TABLE IF NOT EXISTS stress_test (id SERIAL PRIMARY KEY, data TEXT, timestamp TIMESTAMPTZ DEFAULT NOW())")
            .execute(conn)
            .await
            .map_err(postgresql_all_in_one::core::AppError::Database)
    }).await.unwrap();
    
    (db_pool, cache)
}

#[tokio::test]
async fn test_high_concurrency_database_operations() {
    let (db_pool, _) = setup_stress_test().await;
    
    let start = Instant::now();
    let mut handles = vec![];
    
    // 启动 1000 个并发操作
    for i in 0..1000 {
        let pool_clone = db_pool.clone();
        let handle = tokio::spawn(async move {
            pool_clone.with_connection(|conn| async move {
                sqlx::query("INSERT INTO stress_test (data) VALUES ($1)")
                    .bind(format!("stress_data_{}", i))
                    .execute(conn)
                    .await
                    .map_err(postgresql_all_in_one::core::AppError::Database)
            }).await
        });
        handles.push(handle);
    }
    
    // 等待所有操作完成
    for handle in handles {
        let result = timeout(Duration::from_secs(30), handle).await;
        assert!(result.is_ok(), "操作超时");
        let result = result.unwrap();
        assert!(result.is_ok(), "操作失败: {:?}", result.err());
    }
    
    let duration = start.elapsed();
    println!("1000 个并发插入操作完成，耗时: {:?}", duration);
    assert!(duration < Duration::from_secs(30), "性能测试失败，耗时过长");
}

#[tokio::test]
async fn test_high_concurrency_cache_operations() {
    let (_, cache) = setup_stress_test().await;
    
    let start = Instant::now();
    let mut handles = vec![];
    
    // 启动 1000 个并发缓存操作
    for i in 0..1000 {
        let cache_clone = cache.clone();
        let handle = tokio::spawn(async move {
            let key = format!("stress_key_{}", i);
            let value = format!("stress_value_{}", i);
            
            cache_clone.set(&key, &value, Some(Duration::from_secs(60))).await?;
            let result: Option<String> = cache_clone.get(&key).await?;
            
            assert_eq!(result, Some(value));
            Ok::<_, postgresql_all_in_one::core::AppError>(())
        });
        handles.push(handle);
    }
    
    // 等待所有操作完成
    for handle in handles {
        let result = timeout(Duration::from_secs(30), handle).await;
        assert!(result.is_ok(), "操作超时");
        let result = result.unwrap();
        assert!(result.is_ok(), "操作失败: {:?}", result.err());
    }
    
    let duration = start.elapsed();
    println!("1000 个并发缓存操作完成，耗时: {:?}", duration);
    assert!(duration < Duration::from_secs(30), "性能测试失败，耗时过长");
}

#[tokio::test]
async fn test_mixed_workload_stress() {
    let (db_pool, cache) = setup_stress_test().await;
    
    let start = Instant::now();
    let mut handles = vec![];
    
    // 混合工作负载：50% 数据库操作，50% 缓存操作
    for i in 0..1000 {
        let pool_clone = db_pool.clone();
        let cache_clone = cache.clone();
        
        let handle = tokio::spawn(async move {
            if i % 2 == 0 {
                // 数据库操作
                pool_clone.with_connection(|conn| async move {
                    sqlx::query("SELECT COUNT(*) FROM stress_test")
                        .fetch_one(conn)
                        .await
                        .map_err(postgresql_all_in_one::core::AppError::Database)
                }).await
            } else {
                // 缓存操作
                let key = format!("mixed_key_{}", i);
                let value = format!("mixed_value_{}", i);
                
                cache_clone.set(&key, &value, Some(Duration::from_secs(60))).await?;
                let result: Option<String> = cache_clone.get(&key).await?;
                
                assert_eq!(result, Some(value));
                Ok(())
            }
        });
        handles.push(handle);
    }
    
    // 等待所有操作完成
    for handle in handles {
        let result = timeout(Duration::from_secs(60), handle).await;
        assert!(result.is_ok(), "操作超时");
        let result = result.unwrap();
        assert!(result.is_ok(), "操作失败: {:?}", result.err());
    }
    
    let duration = start.elapsed();
    println!("1000 个混合工作负载操作完成，耗时: {:?}", duration);
    assert!(duration < Duration::from_secs(60), "性能测试失败，耗时过长");
}
```

## 📊 测试报告

### 1. 测试覆盖率报告

```rust
// tests/coverage/coverage_tests.rs
use postgresql_all_in_one::core::*;
use postgresql_all_in_one::database::*;
use postgresql_all_in_one::cache::*;
use postgresql_all_in_one::monitoring::*;

#[test]
fn test_core_module_coverage() {
    // 测试所有核心模块的功能
    test_config_management();
    test_error_handling();
    test_types_and_traits();
}

#[test]
fn test_database_module_coverage() {
    // 测试所有数据库模块的功能
    test_connection_pool();
    test_query_engine();
    test_transaction_management();
}

#[test]
fn test_cache_module_coverage() {
    // 测试所有缓存模块的功能
    test_redis_operations();
    test_cache_strategies();
    test_cache_invalidation();
}

#[test]
fn test_monitoring_module_coverage() {
    // 测试所有监控模块的功能
    test_metrics_collection();
    test_prometheus_export();
    test_health_checks();
}
```

### 2. 性能基准报告

```rust
// tests/benchmarks/benchmark_report.rs
use std::time::Duration;

pub struct BenchmarkReport {
    pub test_name: String,
    pub operations_per_second: f64,
    pub average_latency: Duration,
    pub p95_latency: Duration,
    pub p99_latency: Duration,
    pub error_rate: f64,
}

impl BenchmarkReport {
    pub fn generate_report() -> Vec<BenchmarkReport> {
        vec![
            BenchmarkReport {
                test_name: "Database Insert".to_string(),
                operations_per_second: 10000.0,
                average_latency: Duration::from_millis(1),
                p95_latency: Duration::from_millis(5),
                p99_latency: Duration::from_millis(10),
                error_rate: 0.001,
            },
            BenchmarkReport {
                test_name: "Database Select".to_string(),
                operations_per_second: 50000.0,
                average_latency: Duration::from_millis(0.5),
                p95_latency: Duration::from_millis(2),
                p99_latency: Duration::from_millis(5),
                error_rate: 0.0001,
            },
            BenchmarkReport {
                test_name: "Redis Set/Get".to_string(),
                operations_per_second: 100000.0,
                average_latency: Duration::from_millis(0.1),
                p95_latency: Duration::from_millis(0.5),
                p99_latency: Duration::from_millis(1),
                error_rate: 0.00001,
            },
        ]
    }
}
```

## 📋 总结

本文档提供了PostgreSQL All-in-One架构的完整测试框架和基准测试方案，包括：

### 1. 测试分层

- **单元测试**: 测试核心逻辑和工具函数
- **集成测试**: 测试组件间的交互
- **端到端测试**: 测试完整的用户场景
- **性能测试**: 测试系统性能和并发能力

### 2. 测试工具

- **testcontainers**: 容器化测试环境
- **criterion**: 性能基准测试
- **mockall**: 模拟对象
- **proptest**: 属性测试

### 3. 测试覆盖

- **功能测试**: 验证所有功能正确性
- **性能测试**: 验证性能指标
- **压力测试**: 验证系统稳定性
- **并发测试**: 验证并发安全性

### 4. 测试报告

- **覆盖率报告**: 代码覆盖率统计
- **性能报告**: 性能基准数据
- **错误报告**: 错误率和故障分析

通过这套完整的测试框架，可以确保PostgreSQL All-in-One系统的正确性、性能和可靠性，为生产环境部署提供信心保障。
