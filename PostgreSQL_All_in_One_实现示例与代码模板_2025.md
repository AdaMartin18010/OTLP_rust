# PostgreSQL All-in-One 实现示例与代码模板 - 2025年

## 📋 执行摘要

本文档提供了PostgreSQL All-in-One架构的具体实现示例和代码模板，包括完整的项目结构、核心代码实现、配置文件和部署脚本。通过这些模板，开发团队可以快速启动项目并按照最佳实践进行开发。

## 🏗️ 项目结构模板

### 1. 完整项目结构

```text
postgresql-all-in-one/
├── Cargo.toml                    # 工作区配置
├── Cargo.lock                    # 依赖锁定
├── rust-toolchain.toml           # Rust工具链配置
├── README.md                     # 项目说明
├── LICENSE                       # 许可证
├── .gitignore                    # Git忽略文件
├── .github/                      # GitHub配置
│   └── workflows/
│       ├── ci.yml               # 持续集成
│       ├── cd.yml               # 持续部署
│       └── security.yml         # 安全扫描
├── docs/                         # 文档目录
│   ├── architecture/            # 架构文档
│   ├── api/                     # API文档
│   ├── deployment/              # 部署文档
│   └── examples/                # 示例文档
├── crates/                       # 核心库
│   ├── core/                    # 核心库
│   ├── database/                # 数据库层
│   ├── cache/                   # 缓存层
│   ├── monitoring/              # 监控层
│   └── security/                # 安全层
├── services/                     # 服务层
│   ├── api-gateway/             # API网关
│   ├── query-engine/            # 查询引擎
│   ├── data-processor/          # 数据处理器
│   └── monitoring-service/      # 监控服务
├── examples/                     # 示例代码
│   ├── basic-usage/             # 基础使用
│   ├── advanced-features/       # 高级功能
│   └── performance-tests/       # 性能测试
├── tests/                        # 测试代码
│   ├── unit/                    # 单元测试
│   ├── integration/             # 集成测试
│   └── e2e/                     # 端到端测试
├── scripts/                      # 脚本文件
│   ├── build.sh                 # 构建脚本
│   ├── test.sh                  # 测试脚本
│   └── deploy.sh                # 部署脚本
├── k8s/                          # Kubernetes配置
│   ├── postgres/                # PostgreSQL配置
│   ├── redis/                   # Redis配置
│   ├── monitoring/              # 监控配置
│   └── ingress/                 # 入口配置
├── docker/                       # Docker配置
│   ├── Dockerfile.postgres      # PostgreSQL镜像
│   ├── Dockerfile.redis         # Redis镜像
│   └── docker-compose.yml       # 组合配置
└── helm/                         # Helm图表
    └── postgresql-all-in-one/   # Helm图表
        ├── Chart.yaml           # 图表配置
        ├── values.yaml          # 默认值
        └── templates/           # 模板文件
```

## 🔧 核心代码实现

### 1. 工作区配置 (Cargo.toml)

```toml
[workspace]
resolver = "3"

members = [
    "crates/core",
    "crates/database", 
    "crates/cache",
    "crates/monitoring",
    "crates/security",
    "services/api-gateway",
    "services/query-engine",
    "services/data-processor",
    "services/monitoring-service"
]

[workspace.package]
edition = "2024"
rust-version = "1.90"
authors = ["PostgreSQL All-in-One Team"]
license = "MIT OR Apache-2.0"
repository = "https://github.com/your-org/postgresql-all-in-one"
keywords = ["postgresql", "database", "all-in-one", "rust"]
categories = ["database", "development-tools"]

[workspace.dependencies]
# 异步运行时
tokio = { version = "1.47.1", features = ["full"] }
tokio-util = "0.7.16"
futures = "0.3.31"

# 数据库相关
sqlx = { version = "0.8.7", features = ["runtime-tokio-rustls", "postgres", "chrono", "uuid"] }
sea-orm = { version = "1.1.16", features = ["sqlx-postgres", "runtime-tokio-rustls"] }

# 缓存相关
redis = "0.32.5"

# 序列化
serde = { version = "1.0.227", features = ["derive"] }
serde_json = "1.0.145"

# 错误处理
anyhow = "1.0.100"
thiserror = "2.0.16"

# 日志和追踪
tracing = "0.1.41"
tracing-subscriber = { version = "0.3.20", features = ["env-filter", "json"] }

# 监控
prometheus = "0.14.0"
metrics = "0.24.2"

# 时间处理
chrono = { version = "0.4.42", features = ["serde"] }
time = { version = "0.3.44", features = ["serde", "macros"] }

# 网络
reqwest = { version = "0.12.23", features = ["json", "rustls-tls"] }
hyper = { version = "1.7.0", features = ["full"] }

# 配置管理
config = "0.15.16"
toml = "0.9.7"

# 并发和同步
parking_lot = "0.12.4"
dashmap = "6.1.0"
crossbeam = "0.8.4"

# 测试
tokio-test = "0.4.4"
criterion = "0.7.0"
mockall = "0.13.1"

[profile.release]
opt-level = 3
lto = "fat"
codegen-units = 1
strip = "symbols"
panic = "abort"

[profile.dev]
opt-level = 0
debug = true
incremental = true
```

### 2. 核心库实现 (crates/core/src/lib.rs)

```rust
//! # PostgreSQL All-in-One Core Library
//!
//! 核心库提供基础类型、错误处理和配置管理功能

pub mod config;
pub mod error;
pub mod types;
pub mod traits;

pub use config::*;
pub use error::*;
pub use types::*;
pub use traits::*;

/// 库版本信息
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// 库名称
pub const NAME: &str = env!("CARGO_PKG_NAME");
```

### 3. 配置管理 (crates/core/src/config.rs)

```rust
use serde::{Deserialize, Serialize};
use std::time::Duration;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AppConfig {
    pub database: DatabaseConfig,
    pub cache: CacheConfig,
    pub monitoring: MonitoringConfig,
    pub security: SecurityConfig,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DatabaseConfig {
    pub url: String,
    pub max_connections: u32,
    pub min_connections: u32,
    pub acquire_timeout: Duration,
    pub idle_timeout: Duration,
    pub max_lifetime: Duration,
    pub health_check_interval: Duration,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheConfig {
    pub host: String,
    pub port: u16,
    pub password: Option<String>,
    pub database: u8,
    pub default_ttl: Duration,
    pub max_connections: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MonitoringConfig {
    pub prometheus_port: u16,
    pub metrics_path: String,
    pub health_check_path: String,
    pub log_level: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SecurityConfig {
    pub enable_ssl: bool,
    pub ssl_cert_path: Option<String>,
    pub ssl_key_path: Option<String>,
    pub max_connections_per_ip: u32,
    pub rate_limit_per_minute: u32,
}

impl Default for AppConfig {
    fn default() -> Self {
        Self {
            database: DatabaseConfig::default(),
            cache: CacheConfig::default(),
            monitoring: MonitoringConfig::default(),
            security: SecurityConfig::default(),
        }
    }
}

impl Default for DatabaseConfig {
    fn default() -> Self {
        Self {
            url: "postgresql://postgres:password@localhost:5432/myapp".to_string(),
            max_connections: 100,
            min_connections: 10,
            acquire_timeout: Duration::from_secs(30),
            idle_timeout: Duration::from_secs(600),
            max_lifetime: Duration::from_secs(1800),
            health_check_interval: Duration::from_secs(60),
        }
    }
}

impl Default for CacheConfig {
    fn default() -> Self {
        Self {
            host: "localhost".to_string(),
            port: 6379,
            password: None,
            database: 0,
            default_ttl: Duration::from_secs(3600),
            max_connections: 100,
        }
    }
}

impl Default for MonitoringConfig {
    fn default() -> Self {
        Self {
            prometheus_port: 9090,
            metrics_path: "/metrics".to_string(),
            health_check_path: "/health".to_string(),
            log_level: "info".to_string(),
        }
    }
}

impl Default for SecurityConfig {
    fn default() -> Self {
        Self {
            enable_ssl: false,
            ssl_cert_path: None,
            ssl_key_path: None,
            max_connections_per_ip: 1000,
            rate_limit_per_minute: 1000,
        }
    }
}

impl AppConfig {
    pub fn from_file(path: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let content = std::fs::read_to_string(path)?;
        let config: AppConfig = toml::from_str(&content)?;
        Ok(config)
    }

    pub fn from_env() -> Result<Self, Box<dyn std::error::Error>> {
        let mut config = AppConfig::default();
        
        if let Ok(url) = std::env::var("DATABASE_URL") {
            config.database.url = url;
        }
        
        if let Ok(host) = std::env::var("REDIS_HOST") {
            config.cache.host = host;
        }
        
        if let Ok(port) = std::env::var("REDIS_PORT") {
            config.cache.port = port.parse()?;
        }
        
        Ok(config)
    }
}
```

### 4. 错误处理 (crates/core/src/error.rs)

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum AppError {
    #[error("Database error: {0}")]
    Database(#[from] sqlx::Error),
    
    #[error("Redis error: {0}")]
    Redis(#[from] redis::RedisError),
    
    #[error("Configuration error: {0}")]
    Config(String),
    
    #[error("Validation error: {0}")]
    Validation(String),
    
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    
    #[error("Serialization error: {0}")]
    Serialization(#[from] serde_json::Error),
    
    #[error("Timeout error: {0}")]
    Timeout(String),
    
    #[error("Authentication error: {0}")]
    Authentication(String),
    
    #[error("Authorization error: {0}")]
    Authorization(String),
    
    #[error("Rate limit exceeded")]
    RateLimitExceeded,
    
    #[error("Resource not found: {0}")]
    NotFound(String),
    
    #[error("Internal server error: {0}")]
    Internal(String),
}

pub type Result<T> = std::result::Result<T, AppError>;

impl AppError {
    pub fn config(msg: impl Into<String>) -> Self {
        Self::Config(msg.into())
    }
    
    pub fn validation(msg: impl Into<String>) -> Self {
        Self::Validation(msg.into())
    }
    
    pub fn timeout(msg: impl Into<String>) -> Self {
        Self::Timeout(msg.into())
    }
    
    pub fn authentication(msg: impl Into<String>) -> Self {
        Self::Authentication(msg.into())
    }
    
    pub fn authorization(msg: impl Into<String>) -> Self {
        Self::Authorization(msg.into())
    }
    
    pub fn not_found(msg: impl Into<String>) -> Self {
        Self::NotFound(msg.into())
    }
    
    pub fn internal(msg: impl Into<String>) -> Self {
        Self::Internal(msg.into())
    }
}
```

### 5. 数据库连接池 (crates/database/src/connection/pool.rs)

```rust
use sqlx::{PgPool, PgConnection, Error as SqlxError};
use std::time::{Duration, Instant};
use std::sync::Arc;
use tokio::sync::{RwLock, Semaphore};
use serde::{Deserialize, Serialize};
use tracing::{info, warn, error};

use crate::core::{AppError, Result};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PoolConfig {
    pub max_connections: u32,
    pub min_connections: u32,
    pub acquire_timeout: Duration,
    pub idle_timeout: Duration,
    pub max_lifetime: Duration,
    pub health_check_interval: Duration,
}

#[derive(Debug)]
pub struct ConnectionStats {
    pub total_connections: u32,
    pub active_connections: u32,
    pub idle_connections: u32,
    pub waiting_requests: u32,
    pub total_requests: u64,
    pub successful_requests: u64,
    pub failed_requests: u64,
    pub average_response_time: Duration,
}

pub struct DatabasePool {
    pool: PgPool,
    config: PoolConfig,
    stats: Arc<RwLock<ConnectionStats>>,
    semaphore: Arc<Semaphore>,
    health_check_task: Option<tokio::task::JoinHandle<()>>,
}

impl DatabasePool {
    pub async fn new(database_url: &str, config: PoolConfig) -> Result<Self> {
        let pool = PgPool::builder()
            .max_connections(config.max_connections)
            .min_connections(config.min_connections)
            .acquire_timeout(config.acquire_timeout)
            .idle_timeout(config.idle_timeout)
            .max_lifetime(config.max_lifetime)
            .build(database_url)
            .await
            .map_err(AppError::Database)?;

        let stats = Arc::new(RwLock::new(ConnectionStats {
            total_connections: 0,
            active_connections: 0,
            idle_connections: 0,
            waiting_requests: 0,
            total_requests: 0,
            successful_requests: 0,
            failed_requests: 0,
            average_response_time: Duration::from_millis(0),
        }));

        let semaphore = Arc::new(Semaphore::new(config.max_connections as usize));

        let mut pool_instance = Self {
            pool,
            config,
            stats,
            semaphore,
            health_check_task: None,
        };

        pool_instance.start_health_check().await;
        Ok(pool_instance)
    }

    pub async fn with_connection<F, Fut, R>(&self, f: F) -> Result<R>
    where
        F: FnOnce(PgConnection) -> Fut,
        Fut: std::future::Future<Output = Result<R>> + Send + 'static,
        R: Send,
    {
        let start = Instant::now();
        let _permit = self.semaphore.acquire().await
            .map_err(|_| AppError::internal("Failed to acquire semaphore permit"))?;

        self.update_stats(|stats| {
            stats.waiting_requests += 1;
            stats.total_requests += 1;
        }).await;

        let result = async {
            let mut conn = self.pool.acquire().await
                .map_err(AppError::Database)?;
            
            self.update_stats(|stats| {
                stats.active_connections += 1;
                stats.waiting_requests -= 1;
            }).await;

            let result = f(conn).await;

            self.update_stats(|stats| {
                stats.active_connections -= 1;
                if result.is_ok() {
                    stats.successful_requests += 1;
                } else {
                    stats.failed_requests += 1;
                }
            }).await;

            result
        }.await;

        let duration = start.elapsed();
        self.update_stats(|stats| {
            stats.average_response_time = Duration::from_millis(
                (stats.average_response_time.as_millis() + duration.as_millis()) / 2
            );
        }).await;

        result
    }

    pub async fn with_transaction<F, Fut, R>(&self, f: F) -> Result<R>
    where
        F: FnOnce(sqlx::Transaction<'_, sqlx::Postgres>) -> Fut,
        Fut: std::future::Future<Output = Result<R>> + Send + 'static,
        R: Send,
    {
        let start = Instant::now();
        let _permit = self.semaphore.acquire().await
            .map_err(|_| AppError::internal("Failed to acquire semaphore permit"))?;

        self.update_stats(|stats| {
            stats.waiting_requests += 1;
            stats.total_requests += 1;
        }).await;

        let result = async {
            let mut tx = self.pool.begin().await
                .map_err(AppError::Database)?;
            
            self.update_stats(|stats| {
                stats.active_connections += 1;
                stats.waiting_requests -= 1;
            }).await;

            let result = f(tx).await;

            self.update_stats(|stats| {
                stats.active_connections -= 1;
                if result.is_ok() {
                    stats.successful_requests += 1;
                } else {
                    stats.failed_requests += 1;
                }
            }).await;

            if result.is_ok() {
                tx.commit().await.map_err(AppError::Database)?;
            } else {
                tx.rollback().await.map_err(AppError::Database)?;
            }

            result
        }.await;

        let duration = start.elapsed();
        self.update_stats(|stats| {
            stats.average_response_time = Duration::from_millis(
                (stats.average_response_time.as_millis() + duration.as_millis()) / 2
            );
        }).await;

        result
    }

    pub async fn get_stats(&self) -> ConnectionStats {
        self.stats.read().await.clone()
    }

    pub async fn health_check(&self) -> bool {
        match sqlx::query("SELECT 1").fetch_one(&self.pool).await {
            Ok(_) => true,
            Err(e) => {
                error!("Health check failed: {}", e);
                false
            }
        }
    }

    async fn start_health_check(&mut self) {
        let pool = self.pool.clone();
        let stats = self.stats.clone();
        let interval = self.config.health_check_interval;

        let task = tokio::spawn(async move {
            let mut interval_timer = tokio::time::interval(interval);
            loop {
                interval_timer.tick().await;
                
                match sqlx::query("SELECT 1").fetch_one(&pool).await {
                    Ok(_) => {
                        info!("Database health check passed");
                    }
                    Err(e) => {
                        error!("Database health check failed: {}", e);
                    }
                }

                // 更新连接统计
                if let Ok(mut stats_guard) = stats.write().await {
                    stats_guard.total_connections = pool.size();
                    stats_guard.idle_connections = pool.num_idle();
                }
            }
        });

        self.health_check_task = Some(task);
    }

    async fn update_stats<F>(&self, f: F)
    where
        F: FnOnce(&mut ConnectionStats),
    {
        if let Ok(mut stats) = self.stats.write().await {
            f(&mut stats);
        }
    }
}

impl Drop for DatabasePool {
    fn drop(&mut self) {
        if let Some(task) = self.health_check_task.take() {
            task.abort();
        }
    }
}
```

## 🚀 部署脚本

### 1. 构建脚本 (scripts/build.sh)

```bash
#!/bin/bash

# PostgreSQL All-in-One 构建脚本
set -e

echo "🚀 开始构建 PostgreSQL All-in-One..."

# 检查 Rust 版本
echo "📋 检查 Rust 版本..."
rustc --version
cargo --version

# 清理之前的构建
echo "🧹 清理之前的构建..."
cargo clean

# 运行测试
echo "🧪 运行测试..."
cargo test --workspace

# 运行 clippy 检查
echo "🔍 运行 clippy 检查..."
cargo clippy --workspace -- -D warnings

# 运行格式化检查
echo "📝 运行格式化检查..."
cargo fmt --all -- --check

# 构建发布版本
echo "🔨 构建发布版本..."
cargo build --release --workspace

# 构建 Docker 镜像
echo "🐳 构建 Docker 镜像..."
docker build -t postgresql-all-in-one:latest -f docker/Dockerfile.postgres .
docker build -t postgresql-all-in-one-redis:latest -f docker/Dockerfile.redis .

echo "✅ 构建完成！"
```

### 2. 测试脚本 (scripts/test.sh)

```bash
#!/bin/bash

# PostgreSQL All-in-One 测试脚本
set -e

echo "🧪 开始运行测试..."

# 启动测试环境
echo "🚀 启动测试环境..."
docker-compose -f docker/docker-compose.test.yml up -d

# 等待服务启动
echo "⏳ 等待服务启动..."
sleep 30

# 运行单元测试
echo "🔬 运行单元测试..."
cargo test --workspace --lib

# 运行集成测试
echo "🔗 运行集成测试..."
cargo test --workspace --test '*'

# 运行性能测试
echo "⚡ 运行性能测试..."
cargo bench --workspace

# 运行端到端测试
echo "🎯 运行端到端测试..."
cargo test --workspace --test e2e

# 停止测试环境
echo "🛑 停止测试环境..."
docker-compose -f docker/docker-compose.test.yml down

echo "✅ 测试完成！"
```

### 3. 部署脚本 (scripts/deploy.sh)

```bash
#!/bin/bash

# PostgreSQL All-in-One 部署脚本
set -e

ENVIRONMENT=${1:-development}
NAMESPACE=${2:-postgresql-all-in-one}

echo "🚀 开始部署到 $ENVIRONMENT 环境..."

# 检查 kubectl
if ! command -v kubectl &> /dev/null; then
    echo "❌ kubectl 未安装"
    exit 1
fi

# 检查 helm
if ! command -v helm &> /dev/null; then
    echo "❌ helm 未安装"
    exit 1
fi

# 创建命名空间
echo "📦 创建命名空间..."
kubectl create namespace $NAMESPACE --dry-run=client -o yaml | kubectl apply -f -

# 部署 PostgreSQL
echo "🐘 部署 PostgreSQL..."
helm upgrade --install postgresql-all-in-one ./helm/postgresql-all-in-one \
    --namespace $NAMESPACE \
    --values ./helm/postgresql-all-in-one/values-$ENVIRONMENT.yaml \
    --wait

# 部署 Redis
echo "🔴 部署 Redis..."
kubectl apply -f k8s/redis/ -n $NAMESPACE

# 部署监控
echo "📊 部署监控..."
kubectl apply -f k8s/monitoring/ -n $NAMESPACE

# 部署入口
echo "🌐 部署入口..."
kubectl apply -f k8s/ingress/ -n $NAMESPACE

# 等待部署完成
echo "⏳ 等待部署完成..."
kubectl wait --for=condition=available --timeout=300s deployment/postgresql-all-in-one -n $NAMESPACE

# 检查部署状态
echo "📋 检查部署状态..."
kubectl get pods -n $NAMESPACE
kubectl get services -n $NAMESPACE

echo "✅ 部署完成！"
```

## 🐳 Docker 配置

### 1. PostgreSQL Dockerfile (docker/Dockerfile.postgres)

```dockerfile
FROM timescale/timescaledb:latest-pg15

# 安装扩展
RUN apt-get update && apt-get install -y \
    postgresql-15-zhparser \
    postgresql-15-pg-stat-statements \
    postgresql-15-pgcrypto \
    && rm -rf /var/lib/apt/lists/*

# 复制配置文件
COPY docker/postgresql.conf /etc/postgresql/postgresql.conf
COPY docker/pg_hba.conf /etc/postgresql/pg_hba.conf

# 复制初始化脚本
COPY docker/init.sql /docker-entrypoint-initdb.d/

# 设置权限
RUN chown -R postgres:postgres /etc/postgresql/
RUN chmod 600 /etc/postgresql/postgresql.conf
RUN chmod 600 /etc/postgresql/pg_hba.conf

# 暴露端口
EXPOSE 5432

# 启动命令
CMD ["postgres", "-c", "config_file=/etc/postgresql/postgresql.conf"]
```

### 2. Docker Compose 配置 (docker/docker-compose.yml)

```yaml
version: '3.8'

services:
  postgres:
    build:
      context: .
      dockerfile: docker/Dockerfile.postgres
    container_name: postgresql-all-in-one
    environment:
      POSTGRES_DB: myapp
      POSTGRES_USER: postgres
      POSTGRES_PASSWORD: password
      POSTGRES_INITDB_ARGS: "--encoding=UTF-8 --lc-collate=C --lc-ctype=C"
    ports:
      - "5432:5432"
    volumes:
      - postgres_data:/var/lib/postgresql/data
      - ./docker/init.sql:/docker-entrypoint-initdb.d/init.sql
    command: >
      postgres
      -c shared_buffers=2GB
      -c effective_cache_size=6GB
      -c work_mem=256MB
      -c maintenance_work_mem=1GB
      -c max_connections=200
      -c random_page_cost=1.1
      -c effective_io_concurrency=200
      -c max_parallel_workers_per_gather=4
      -c max_parallel_workers=8
    healthcheck:
      test: ["CMD-SHELL", "pg_isready -U postgres"]
      interval: 30s
      timeout: 10s
      retries: 3
    restart: unless-stopped

  redis:
    image: redis:7-alpine
    container_name: postgresql-all-in-one-redis
    ports:
      - "6379:6379"
    volumes:
      - redis_data:/data
    command: redis-server --maxmemory 1gb --maxmemory-policy allkeys-lru
    healthcheck:
      test: ["CMD", "redis-cli", "ping"]
      interval: 30s
      timeout: 10s
      retries: 3
    restart: unless-stopped

  prometheus:
    image: prom/prometheus:latest
    container_name: postgresql-all-in-one-prometheus
    ports:
      - "9090:9090"
    volumes:
      - ./monitoring/prometheus.yml:/etc/prometheus/prometheus.yml
      - prometheus_data:/prometheus
    command:
      - '--config.file=/etc/prometheus/prometheus.yml'
      - '--storage.tsdb.path=/prometheus'
      - '--web.console.libraries=/etc/prometheus/console_libraries'
      - '--web.console.templates=/etc/prometheus/consoles'
      - '--storage.tsdb.retention.time=200h'
      - '--web.enable-lifecycle'
    restart: unless-stopped

  grafana:
    image: grafana/grafana:latest
    container_name: postgresql-all-in-one-grafana
    ports:
      - "3000:3000"
    volumes:
      - grafana_data:/var/lib/grafana
      - ./monitoring/grafana-dashboard.json:/var/lib/grafana/dashboards/postgresql-dashboard.json
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=admin
    restart: unless-stopped

volumes:
  postgres_data:
  redis_data:
  prometheus_data:
  grafana_data:

networks:
  default:
    name: postgresql-all-in-one-network
```

## 📊 监控配置

### 1. Prometheus 配置 (monitoring/prometheus.yml)

```yaml
global:
  scrape_interval: 15s
  evaluation_interval: 15s

rule_files:
  - "rules/*.yml"

scrape_configs:
  - job_name: 'postgresql'
    static_configs:
      - targets: ['postgres:5432']
    metrics_path: /metrics
    scrape_interval: 5s

  - job_name: 'redis'
    static_configs:
      - targets: ['redis:6379']
    metrics_path: /metrics
    scrape_interval: 5s

  - job_name: 'prometheus'
    static_configs:
      - targets: ['localhost:9090']

alerting:
  alertmanagers:
    - static_configs:
        - targets:
          - alertmanager:9093
```

### 2. Grafana 仪表板 (monitoring/grafana-dashboard.json)

```json
{
  "dashboard": {
    "id": null,
    "title": "PostgreSQL All-in-One Dashboard",
    "tags": ["postgresql", "database", "all-in-one"],
    "timezone": "browser",
    "panels": [
      {
        "id": 1,
        "title": "Database Connections",
        "type": "graph",
        "targets": [
          {
            "expr": "postgresql_stat_database_numbackends",
            "legendFormat": "Active Connections"
          }
        ],
        "yAxes": [
          {
            "label": "Connections",
            "min": 0
          }
        ]
      },
      {
        "id": 2,
        "title": "Query Performance",
        "type": "graph",
        "targets": [
          {
            "expr": "rate(postgresql_stat_database_tup_returned[5m])",
            "legendFormat": "Tuples Returned/sec"
          },
          {
            "expr": "rate(postgresql_stat_database_tup_fetched[5m])",
            "legendFormat": "Tuples Fetched/sec"
          }
        ]
      },
      {
        "id": 3,
        "title": "Cache Hit Ratio",
        "type": "singlestat",
        "targets": [
          {
            "expr": "rate(postgresql_stat_database_blks_hit[5m]) / (rate(postgresql_stat_database_blks_hit[5m]) + rate(postgresql_stat_database_blks_read[5m])) * 100",
            "legendFormat": "Cache Hit Ratio %"
          }
        ],
        "thresholds": "80,90"
      }
    ],
    "time": {
      "from": "now-1h",
      "to": "now"
    },
    "refresh": "5s"
  }
}
```

## 🧪 测试框架

### 1. 单元测试示例 (tests/unit/database_tests.rs)

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use tokio_test;
    use crate::core::AppConfig;

    #[tokio::test]
    async fn test_connection_pool_creation() {
        let config = PoolConfig::default();
        let pool = DatabasePool::new("postgresql://test:test@localhost:5432/testdb", config).await;
        assert!(pool.is_ok());
    }

    #[tokio::test]
    async fn test_connection_pool_health_check() {
        let config = PoolConfig::default();
        let pool = DatabasePool::new("postgresql://test:test@localhost:5432/testdb", config).await.unwrap();
        let is_healthy = pool.health_check().await;
        assert!(is_healthy);
    }

    #[tokio::test]
    async fn test_query_execution() {
        let config = PoolConfig::default();
        let pool = DatabasePool::new("postgresql://test:test@localhost:5432/testdb", config).await.unwrap();
        
        let result = pool.with_connection(|conn| async move {
            sqlx::query("SELECT 1 as test")
                .fetch_one(conn)
                .await
                .map_err(AppError::Database)
        }).await;
        
        assert!(result.is_ok());
    }
}
```

### 2. 集成测试示例 (tests/integration/full_system_tests.rs)

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use tokio_test;

    #[tokio::test]
    async fn test_full_system_workflow() {
        // 初始化系统
        let db_config = PoolConfig::default();
        let cache_config = CacheConfig::default();
        
        let db_pool = DatabasePool::new("postgresql://test:test@localhost:5432/testdb", db_config).await.unwrap();
        let cache = RedisCache::new(cache_config).unwrap();
        
        // 测试数据写入
        let result = db_pool.with_connection(|conn| async move {
            sqlx::query("INSERT INTO test_table (name) VALUES ($1)")
                .bind("test")
                .execute(conn)
                .await
                .map_err(AppError::Database)
        }).await;
        
        assert!(result.is_ok());
        
        // 测试缓存
        let cache_result = cache.set("test_key", &"test_value", Some(Duration::from_secs(60))).await;
        assert!(cache_result.is_ok());
        
        let cached_value: Option<String> = cache.get("test_key").await.unwrap();
        assert_eq!(cached_value, Some("test_value".to_string()));
    }
}
```

## 📋 总结

本文档提供了PostgreSQL All-in-One架构的完整实现示例和代码模板，包括：

### 1. 项目结构

- 清晰的分层架构
- 模块化的代码组织
- 完整的配置文件

### 2. 核心实现

- 数据库连接池
- 缓存系统
- 监控集成
- 错误处理

### 3. 部署工具

- Docker配置
- Kubernetes部署
- 自动化脚本

### 4. 测试框架

- 单元测试
- 集成测试
- 性能测试

通过这些模板，开发团队可以快速启动项目并按照最佳实践进行开发，实现一个高性能、高可用、易维护的PostgreSQL All-in-One系统。
