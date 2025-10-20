//! 幂等守卫与存储接口（骨架）

use std::time::Duration;

#[derive(Debug, Clone)]
pub struct IdempotencyConfig {
    pub ttl: Duration,
}

impl Default for IdempotencyConfig {
    fn default() -> Self {
        Self { ttl: Duration::from_secs(300) }
    }
}

/// 幂等存储接口：由调用方实现具体后端（内存/Redis/数据库）
pub trait IdempotencyStore: Send + Sync + 'static {
    /// 尝试写入幂等键，若已存在则返回 false
    fn put_if_absent(&self, key: &str, ttl: Duration) -> bool;
    /// 删除幂等键（可选，用于在失败时释放）
    fn delete(&self, key: &str);
}

/// 简单内存实现（开发/测试用）
pub struct MemoryIdempotencyStore {
    inner: std::sync::Mutex<std::collections::HashMap<String, std::time::Instant>>, 
}

impl MemoryIdempotencyStore {
    pub fn new() -> Self { Self { inner: std::sync::Mutex::new(std::collections::HashMap::new()) } }
}

impl IdempotencyStore for MemoryIdempotencyStore {
    fn put_if_absent(&self, key: &str, ttl: Duration) -> bool {
        let mut map = self.inner.lock().unwrap();
        let now = std::time::Instant::now();
        // 清理过期
        map.retain(|_, &mut exp| exp > now);
        if map.contains_key(key) { return false; }
        map.insert(key.to_string(), now + ttl);
        true
    }
    fn delete(&self, key: &str) {
        let mut map = self.inner.lock().unwrap();
        map.remove(key);
    }
}

/// 幂等守卫
pub struct IdempotencyGuard<S: IdempotencyStore> {
    store: S,
    config: IdempotencyConfig,
}

impl<S: IdempotencyStore> IdempotencyGuard<S> {
    pub fn new(store: S, config: IdempotencyConfig) -> Self { Self { store, config } }

    /// 使用幂等键执行操作：若键已存在则拒绝重复
    pub async fn execute<T, F, Fut>(&self, key: &str, op: F) -> Result<T, &'static str>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<T, &'static str>>,
    {
        if !self.store.put_if_absent(key, self.config.ttl) {
            return Err("idempotent_duplicate");
        }
        let result = op().await;
        if result.is_err() {
            // 失败时可选择清理键，允许重试
            self.store.delete(key);
        }
        result
    }
}


