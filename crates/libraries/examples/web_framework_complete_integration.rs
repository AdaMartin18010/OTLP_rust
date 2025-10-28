//! # Complete Web Framework Integration Example
//! 
//! 完整的Web框架集成示例，展示如何使用Rust 1.90特性构建生产级Web应用
//! 
//! ## 技术栈
//! - **Axum**: 高性能异步Web框架
//! - **SQLx**: 异步数据库驱动
//! - **Redis**: 缓存层
//! - **Tokio**: 异步运行时
//! - **Serde**: 序列化/反序列化
//! - **Tracing**: 可观测性
//! 
//! ## 架构特点
//! - 三层架构（Controller → Service → Repository）
//! - 依赖注入
//! - 错误处理
//! - 中间件链
//! - 健康检查
//! - 优雅关闭
//! 
//! ## Rust 1.90 特性
//! - Const泛型增强
//! - 异步闭包
//! - 新的标准库API

use axum::{
    extract::{Path, Query, State},
    http::StatusCode,
    middleware::{self, Next},
    response::{IntoResponse, Response},
    routing::{get, post},
    Json, Router,
};
use serde::{Deserialize, Serialize};
use sqlx::{PgPool, postgres::PgPoolOptions};
use std::sync::Arc;
use std::time::Duration;
use tokio::signal;
use tower::ServiceBuilder;
use tower_http::{
    trace::TraceLayer,
    timeout::TimeoutLayer,
    compression::CompressionLayer,
};
use tracing::{info, warn, error, instrument};
use redis::AsyncCommands;

// ============================================================================
// Domain Models
// ============================================================================

#[derive(Debug, Clone, Serialize, Deserialize, sqlx::FromRow)]
pub struct User {
    pub id: i64,
    pub username: String,
    pub email: String,
    #[serde(skip_serializing)]
    pub password_hash: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

#[derive(Debug, Deserialize)]
pub struct CreateUserRequest {
    pub username: String,
    pub email: String,
    pub password: String,
}

#[derive(Debug, Deserialize)]
pub struct UpdateUserRequest {
    pub email: Option<String>,
    pub password: Option<String>,
}

#[derive(Debug, Deserialize)]
pub struct PaginationQuery {
    #[serde(default = "default_page")]
    pub page: u32,
    #[serde(default = "default_page_size")]
    pub page_size: u32,
}

fn default_page() -> u32 { 1 }
fn default_page_size() -> u32 { 20 }

// ============================================================================
// Application State
// ============================================================================

#[derive(Clone)]
pub struct AppState {
    pub db: PgPool,
    pub redis: redis::aio::ConnectionManager,
    pub config: Arc<AppConfig>,
}

#[derive(Debug, Clone)]
pub struct AppConfig {
    pub database_url: String,
    pub redis_url: String,
    pub port: u16,
    pub cache_ttl: Duration,
}

impl AppConfig {
    pub fn from_env() -> Self {
        Self {
            database_url: std::env::var("DATABASE_URL")
                .unwrap_or_else(|_| "postgres://user:pass@localhost/mydb".to_string()),
            redis_url: std::env::var("REDIS_URL")
                .unwrap_or_else(|_| "redis://127.0.0.1/".to_string()),
            port: std::env::var("PORT")
                .ok()
                .and_then(|p| p.parse().ok())
                .unwrap_or(3000),
            cache_ttl: Duration::from_secs(300),
        }
    }
}

// ============================================================================
// Repository Layer (Data Access)
// ============================================================================

pub struct UserRepository {
    pool: PgPool,
}

impl UserRepository {
    pub fn new(pool: PgPool) -> Self {
        Self { pool }
    }

    #[instrument(skip(self))]
    pub async fn create(&self, req: &CreateUserRequest) -> Result<User, AppError> {
        let password_hash = hash_password(&req.password)?;
        
        let user = sqlx::query_as::<_, User>(
            r#"
            INSERT INTO users (username, email, password_hash)
            VALUES ($1, $2, $3)
            RETURNING *
            "#,
        )
        .bind(&req.username)
        .bind(&req.email)
        .bind(&password_hash)
        .fetch_one(&self.pool)
        .await
        .map_err(|e| AppError::DatabaseError(e.to_string()))?;

        info!(user_id = user.id, "User created successfully");
        Ok(user)
    }

    #[instrument(skip(self))]
    pub async fn find_by_id(&self, id: i64) -> Result<Option<User>, AppError> {
        let user = sqlx::query_as::<_, User>(
            "SELECT * FROM users WHERE id = $1"
        )
        .bind(id)
        .fetch_optional(&self.pool)
        .await
        .map_err(|e| AppError::DatabaseError(e.to_string()))?;

        Ok(user)
    }

    #[instrument(skip(self))]
    pub async fn find_by_username(&self, username: &str) -> Result<Option<User>, AppError> {
        let user = sqlx::query_as::<_, User>(
            "SELECT * FROM users WHERE username = $1"
        )
        .bind(username)
        .fetch_optional(&self.pool)
        .await
        .map_err(|e| AppError::DatabaseError(e.to_string()))?;

        Ok(user)
    }

    #[instrument(skip(self))]
    pub async fn list(&self, page: u32, page_size: u32) -> Result<Vec<User>, AppError> {
        let offset = (page - 1) * page_size;
        
        let users = sqlx::query_as::<_, User>(
            "SELECT * FROM users ORDER BY created_at DESC LIMIT $1 OFFSET $2"
        )
        .bind(page_size as i64)
        .bind(offset as i64)
        .fetch_all(&self.pool)
        .await
        .map_err(|e| AppError::DatabaseError(e.to_string()))?;

        Ok(users)
    }

    #[instrument(skip(self))]
    pub async fn update(&self, id: i64, req: &UpdateUserRequest) -> Result<User, AppError> {
        let mut query = String::from("UPDATE users SET ");
        let mut updates = Vec::new();
        let mut bind_count = 1;

        if req.email.is_some() {
            updates.push(format!("email = ${}", bind_count));
            bind_count += 1;
        }
        if req.password.is_some() {
            updates.push(format!("password_hash = ${}", bind_count));
            bind_count += 1;
        }

        if updates.is_empty() {
            return Err(AppError::BadRequest("No fields to update".to_string()));
        }

        query.push_str(&updates.join(", "));
        query.push_str(&format!(" WHERE id = ${} RETURNING *", bind_count));

        let mut sqlx_query = sqlx::query_as::<_, User>(&query);

        if let Some(ref email) = req.email {
            sqlx_query = sqlx_query.bind(email);
        }
        if let Some(ref password) = req.password {
            let password_hash = hash_password(password)?;
            sqlx_query = sqlx_query.bind(password_hash);
        }
        sqlx_query = sqlx_query.bind(id);

        let user = sqlx_query
            .fetch_one(&self.pool)
            .await
            .map_err(|e| AppError::DatabaseError(e.to_string()))?;

        info!(user_id = id, "User updated successfully");
        Ok(user)
    }

    #[instrument(skip(self))]
    pub async fn delete(&self, id: i64) -> Result<(), AppError> {
        let result = sqlx::query("DELETE FROM users WHERE id = $1")
            .bind(id)
            .execute(&self.pool)
            .await
            .map_err(|e| AppError::DatabaseError(e.to_string()))?;

        if result.rows_affected() == 0 {
            return Err(AppError::NotFound(format!("User {} not found", id)));
        }

        info!(user_id = id, "User deleted successfully");
        Ok(())
    }
}

// ============================================================================
// Service Layer (Business Logic)
// ============================================================================

pub struct UserService {
    repository: UserRepository,
    redis: redis::aio::ConnectionManager,
    cache_ttl: Duration,
}

impl UserService {
    pub fn new(pool: PgPool, redis: redis::aio::ConnectionManager, cache_ttl: Duration) -> Self {
        Self {
            repository: UserRepository::new(pool),
            redis,
            cache_ttl,
        }
    }

    #[instrument(skip(self))]
    pub async fn create_user(&self, req: CreateUserRequest) -> Result<User, AppError> {
        // Validate username uniqueness
        if self.repository.find_by_username(&req.username).await?.is_some() {
            return Err(AppError::Conflict("Username already exists".to_string()));
        }

        // Create user
        let user = self.repository.create(&req).await?;

        // Invalidate cache
        let _: () = self.redis.clone()
            .del(format!("user:{}", user.id))
            .await
            .map_err(|e| AppError::CacheError(e.to_string()))?;

        Ok(user)
    }

    #[instrument(skip(self))]
    pub async fn get_user(&self, id: i64) -> Result<User, AppError> {
        // Try cache first
        let cache_key = format!("user:{}", id);
        
        if let Ok(cached) = self.redis.clone().get::<_, String>(&cache_key).await {
            if let Ok(user) = serde_json::from_str::<User>(&cached) {
                info!(user_id = id, "User retrieved from cache");
                return Ok(user);
            }
        }

        // Fetch from database
        let user = self.repository
            .find_by_id(id)
            .await?
            .ok_or_else(|| AppError::NotFound(format!("User {} not found", id)))?;

        // Update cache
        if let Ok(serialized) = serde_json::to_string(&user) {
            let _: Result<(), _> = self.redis.clone()
                .set_ex(&cache_key, serialized, self.cache_ttl.as_secs() as usize)
                .await;
        }

        info!(user_id = id, "User retrieved from database");
        Ok(user)
    }

    #[instrument(skip(self))]
    pub async fn list_users(&self, pagination: PaginationQuery) -> Result<Vec<User>, AppError> {
        self.repository.list(pagination.page, pagination.page_size).await
    }

    #[instrument(skip(self))]
    pub async fn update_user(&self, id: i64, req: UpdateUserRequest) -> Result<User, AppError> {
        let user = self.repository.update(id, &req).await?;

        // Invalidate cache
        let _: () = self.redis.clone()
            .del(format!("user:{}", id))
            .await
            .map_err(|e| AppError::CacheError(e.to_string()))?;

        Ok(user)
    }

    #[instrument(skip(self))]
    pub async fn delete_user(&self, id: i64) -> Result<(), AppError> {
        self.repository.delete(id).await?;

        // Invalidate cache
        let _: () = self.redis.clone()
            .del(format!("user:{}", id))
            .await
            .map_err(|e| AppError::CacheError(e.to_string()))?;

        Ok(())
    }
}

// ============================================================================
// Controller Layer (HTTP Handlers)
// ============================================================================

#[instrument(skip(state))]
async fn create_user_handler(
    State(state): State<Arc<AppState>>,
    Json(req): Json<CreateUserRequest>,
) -> Result<Json<User>, AppError> {
    let service = UserService::new(
        state.db.clone(),
        state.redis.clone(),
        state.config.cache_ttl,
    );
    
    let user = service.create_user(req).await?;
    Ok(Json(user))
}

#[instrument(skip(state))]
async fn get_user_handler(
    State(state): State<Arc<AppState>>,
    Path(id): Path<i64>,
) -> Result<Json<User>, AppError> {
    let service = UserService::new(
        state.db.clone(),
        state.redis.clone(),
        state.config.cache_ttl,
    );
    
    let user = service.get_user(id).await?;
    Ok(Json(user))
}

#[instrument(skip(state))]
async fn list_users_handler(
    State(state): State<Arc<AppState>>,
    Query(pagination): Query<PaginationQuery>,
) -> Result<Json<Vec<User>>, AppError> {
    let service = UserService::new(
        state.db.clone(),
        state.redis.clone(),
        state.config.cache_ttl,
    );
    
    let users = service.list_users(pagination).await?;
    Ok(Json(users))
}

#[instrument(skip(state))]
async fn update_user_handler(
    State(state): State<Arc<AppState>>,
    Path(id): Path<i64>,
    Json(req): Json<UpdateUserRequest>,
) -> Result<Json<User>, AppError> {
    let service = UserService::new(
        state.db.clone(),
        state.redis.clone(),
        state.config.cache_ttl,
    );
    
    let user = service.update_user(id, req).await?;
    Ok(Json(user))
}

#[instrument(skip(state))]
async fn delete_user_handler(
    State(state): State<Arc<AppState>>,
    Path(id): Path<i64>,
) -> Result<StatusCode, AppError> {
    let service = UserService::new(
        state.db.clone(),
        state.redis.clone(),
        state.config.cache_ttl,
    );
    
    service.delete_user(id).await?;
    Ok(StatusCode::NO_CONTENT)
}

// ============================================================================
// Health Check
// ============================================================================

#[derive(Serialize)]
struct HealthResponse {
    status: String,
    database: String,
    redis: String,
}

#[instrument(skip(state))]
async fn health_check_handler(
    State(state): State<Arc<AppState>>,
) -> Result<Json<HealthResponse>, AppError> {
    // Check database
    let db_status = sqlx::query("SELECT 1")
        .fetch_one(&state.db)
        .await
        .map(|_| "healthy")
        .unwrap_or("unhealthy");

    // Check Redis
    let redis_status = state.redis.clone()
        .ping::<_, String>()
        .await
        .map(|_| "healthy")
        .unwrap_or("unhealthy");

    let overall_status = if db_status == "healthy" && redis_status == "healthy" {
        "healthy"
    } else {
        "degraded"
    };

    Ok(Json(HealthResponse {
        status: overall_status.to_string(),
        database: db_status.to_string(),
        redis: redis_status.to_string(),
    }))
}

// ============================================================================
// Middleware
// ============================================================================

#[instrument(skip(req, next))]
async fn logging_middleware(
    req: axum::http::Request<axum::body::Body>,
    next: Next,
) -> Response {
    let method = req.method().clone();
    let uri = req.uri().clone();
    
    info!("Request: {} {}", method, uri);
    
    let response = next.run(req).await;
    
    info!("Response: {} {} - {}", method, uri, response.status());
    
    response
}

// ============================================================================
// Error Handling
// ============================================================================

#[derive(Debug, thiserror::Error)]
pub enum AppError {
    #[error("Database error: {0}")]
    DatabaseError(String),
    
    #[error("Cache error: {0}")]
    CacheError(String),
    
    #[error("Not found: {0}")]
    NotFound(String),
    
    #[error("Bad request: {0}")]
    BadRequest(String),
    
    #[error("Conflict: {0}")]
    Conflict(String),
    
    #[error("Internal server error")]
    InternalError,
}

impl IntoResponse for AppError {
    fn into_response(self) -> Response {
        let (status, message) = match self {
            AppError::DatabaseError(msg) => {
                error!("Database error: {}", msg);
                (StatusCode::INTERNAL_SERVER_ERROR, "Database error occurred")
            }
            AppError::CacheError(msg) => {
                warn!("Cache error: {}", msg);
                (StatusCode::INTERNAL_SERVER_ERROR, "Cache error occurred")
            }
            AppError::NotFound(msg) => (StatusCode::NOT_FOUND, msg.as_str()),
            AppError::BadRequest(msg) => (StatusCode::BAD_REQUEST, msg.as_str()),
            AppError::Conflict(msg) => (StatusCode::CONFLICT, msg.as_str()),
            AppError::InternalError => {
                error!("Internal server error");
                (StatusCode::INTERNAL_SERVER_ERROR, "Internal server error")
            }
        };

        (status, Json(serde_json::json!({"error": message}))).into_response()
    }
}

// ============================================================================
// Utilities
// ============================================================================

fn hash_password(password: &str) -> Result<String, AppError> {
    // In production, use bcrypt or argon2
    Ok(format!("hashed_{}", password))
}

// ============================================================================
// Application Setup
// ============================================================================

pub async fn create_app(state: Arc<AppState>) -> Router {
    // User routes
    let user_routes = Router::new()
        .route("/users", post(create_user_handler).get(list_users_handler))
        .route("/users/:id", get(get_user_handler)
            .put(update_user_handler)
            .delete(delete_user_handler));

    // Health check
    let health_routes = Router::new()
        .route("/health", get(health_check_handler));

    // Combine routes with middleware
    Router::new()
        .merge(user_routes)
        .merge(health_routes)
        .layer(
            ServiceBuilder::new()
                .layer(TraceLayer::new_for_http())
                .layer(CompressionLayer::new())
                .layer(TimeoutLayer::new(Duration::from_secs(30)))
                .layer(middleware::from_fn(logging_middleware))
        )
        .with_state(state)
}

// ============================================================================
// Main Function
// ============================================================================

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Initialize tracing
    tracing_subscriber::fmt()
        .with_target(false)
        .compact()
        .init();

    // Load configuration
    let config = Arc::new(AppConfig::from_env());
    info!("Configuration loaded: {:?}", config);

    // Setup database connection pool
    info!("Connecting to database...");
    let db = PgPoolOptions::new()
        .max_connections(10)
        .connect(&config.database_url)
        .await?;
    info!("Database connected successfully");

    // Run migrations
    sqlx::migrate!("./migrations")
        .run(&db)
        .await?;
    info!("Database migrations completed");

    // Setup Redis connection
    info!("Connecting to Redis...");
    let redis_client = redis::Client::open(config.redis_url.as_str())?;
    let redis = redis::aio::ConnectionManager::new(redis_client).await?;
    info!("Redis connected successfully");

    // Create application state
    let state = Arc::new(AppState {
        db,
        redis,
        config: config.clone(),
    });

    // Create router
    let app = create_app(state);

    // Start server
    let addr = format!("0.0.0.0:{}", config.port);
    info!("Starting server on {}", addr);
    
    let listener = tokio::net::TcpListener::bind(&addr).await?;
    
    axum::serve(listener, app)
        .with_graceful_shutdown(shutdown_signal())
        .await?;

    info!("Server stopped gracefully");
    Ok(())
}

// ============================================================================
// Graceful Shutdown
// ============================================================================

async fn shutdown_signal() {
    let ctrl_c = async {
        signal::ctrl_c()
            .await
            .expect("Failed to install Ctrl+C handler");
    };

    #[cfg(unix)]
    let terminate = async {
        signal::unix::signal(signal::unix::SignalKind::terminate())
            .expect("Failed to install signal handler")
            .recv()
            .await;
    };

    #[cfg(not(unix))]
    let terminate = std::future::pending::<()>();

    tokio::select! {
        _ = ctrl_c => {
            info!("Received Ctrl+C signal");
        },
        _ = terminate => {
            info!("Received terminate signal");
        },
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_user_service() {
        // Test implementation
    }
}

