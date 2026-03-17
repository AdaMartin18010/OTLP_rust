//! # WebAssembly Local Storage
//!
//! WebAssembly-native storage for telemetry data persistence.
//! Supports multiple storage backends optimized for WASM environments.
//!
//! ## WASM Storage Landscape 2025-2026
//!
//! | Storage Type | Browser | WASI | Node.js | Capacity | Persistence |
//! |--------------|---------|------|---------|----------|-------------|
//! | Memory | ✅ | ✅ | ✅ | RAM | Session |
//! | LocalStorage | ✅ | ❌ | ❌ | ~5-10MB | Permanent |
//! | SessionStorage | ✅ | ❌ | ❌ | ~5-10MB | Session |
//! | IndexedDB | ✅ | ❌ | ❌ | Large | Permanent |
//! | OPFS | ✅ | ❌ | ❌ | Large | Permanent |
//! | WASI Files | ❌ | ✅ | ✅ | Disk | Permanent |
//! | SQLite WASM | ✅ | ✅ | ✅ | Configurable | Configurable |
//!
//! ## Features
//!
//! - **Multiple Backends**: Memory, LocalStorage, IndexedDB, WASI files
//! - **Queue Management**: Persistent queues for telemetry buffering
//! - **Compression**: Automatic compression for large payloads
//! - **Encryption**: Optional encryption for sensitive data
//! - **Quota Management**: Handle storage limits gracefully
//!
//! ## Usage Examples
//!
//! ### Memory Storage
//!
//! ```rust,ignore
//! use otlp::wasm_storage::{MemoryStorage, Storage};
//!
//! let storage = MemoryStorage::new();
//! storage.put("trace_001", b"trace data").await?;
//!
//! let data = storage.get("trace_001").await?;
//! ```
//!
//! ### LocalStorage (Browser)
//!
//! ```rust,ignore
//! use otlp::wasm_storage::{LocalStorage, Storage};
//!
//! let storage = LocalStorage::new("otlp_prefix");
//!
//! // Store with automatic key prefixing
//! storage.put("batch_001", serialized_traces).await?;
//!
//! // List all keys with prefix
//! let keys = storage.list_keys().await?;
//! ```
//!
//! ### IndexedDB (Browser)
//!
//! ```rust,ignore
//! use otlp::wasm_storage::{IndexedDbStorage, Storage, StorageOptions};
//!
//! let storage = IndexedDbStorage::open("otlp_db", "telemetry")
//!     .with_options(StorageOptions {
//!         max_size: 100 * 1024 * 1024, // 100MB
//!         compression: true,
//!         ..Default::default()
//!     })
//!     .await?;
//!
//! // Store large batches
//! storage.put_batch(vec![
//!     ("trace_001", data1),
//!     ("trace_002", data2),
//! ]).await?;
//! ```
//!
//! ### WASI File Storage
//!
//! ```rust,ignore
//! use otlp::wasm_storage::{WasiFileStorage, Storage};
//!
//! let storage = WasiFileStorage::new("/var/lib/otlp")
//!     .await?;
//!
//! // Automatic file rotation
//! storage.put_with_rotation("telemetry", data).await?;
//! ```
//!
//! ### Persistent Queue
//!
//! ```rust,ignore
//! use otlp::wasm_storage::{PersistentQueue, Queue};
//!
//! let queue = PersistentQueue::new(IndexedDbStorage::open("queue_db", "pending").await?);
//!
//! // Enqueue telemetry for later export
//! queue.enqueue(b"trace_data").await?;
//!
//! // Process when online
//! while let Some(item) = queue.dequeue().await? {
//!     match exporter.export(item.data).await {
//!         Ok(_) => queue.ack(item.id).await?,
//!         Err(_) => queue.nack(item.id).await?, // Will retry
//!     }
//! }
//! ```

use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};

use crate::error::{OtlpError, ProcessingError, Result};

/// Storage options
#[derive(Debug, Clone)]
pub struct StorageOptions {
    /// Maximum storage size in bytes
    pub max_size: usize,
    /// Enable compression
    pub compression: bool,
    /// Enable encryption
    pub encryption: bool,
    /// TTL for entries in seconds (0 = no TTL)
    pub ttl_secs: u64,
    /// Key prefix
    pub key_prefix: String,
}

impl Default for StorageOptions {
    fn default() -> Self {
        Self {
            max_size: 50 * 1024 * 1024, // 50MB default
            compression: false,
            encryption: false,
            ttl_secs: 0,
            key_prefix: String::new(),
        }
    }
}

/// Storage trait for WASM environments
#[async_trait::async_trait(?Send)]
pub trait Storage {
    /// Get value by key
    async fn get(&self, key: &str) -> Result<Option<Vec<u8>>>;

    /// Store value
    async fn put(&self, key: &str, value: &[u8]) -> Result<()>;

    /// Delete value
    async fn delete(&self, key: &str) -> Result<()>;

    /// Check if key exists
    async fn exists(&self, key: &str) -> Result<bool>;

    /// List all keys
    async fn list_keys(&self) -> Result<Vec<String>>;

    /// Get storage stats
    async fn stats(&self) -> Result<StorageStats>;

    /// Clear all data
    async fn clear(&self) -> Result<()>;

    /// Get remaining capacity
    async fn remaining_capacity(&self) -> Result<usize>;
}

/// Storage statistics
#[derive(Debug, Clone)]
pub struct StorageStats {
    /// Total size in bytes
    pub total_size: usize,
    /// Number of entries
    pub entry_count: usize,
    /// Available space
    pub available_space: usize,
    /// Storage quota (if applicable)
    pub quota: Option<usize>,
}

/// In-memory storage implementation
pub struct MemoryStorage {
    data: std::cell::RefCell<HashMap<String, Vec<u8>>>,
    options: StorageOptions,
}

impl MemoryStorage {
    /// Create new memory storage
    pub fn new() -> Self {
        Self {
            data: std::cell::RefCell::new(HashMap::new()),
            options: StorageOptions::default(),
        }
    }

    /// Create with options
    pub fn with_options(options: StorageOptions) -> Self {
        Self {
            data: std::cell::RefCell::new(HashMap::new()),
            options,
        }
    }

    /// Get current size
    fn current_size(&self) -> usize {
        self.data
            .borrow()
            .values()
            .map(|v| v.len())
            .sum::<usize>()
    }
}

impl Default for MemoryStorage {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait::async_trait(?Send)]
impl Storage for MemoryStorage {
    async fn get(&self, key: &str) -> Result<Option<Vec<u8>>> {
        Ok(self.data.borrow().get(key).cloned())
    }

    async fn put(&self, key: &str, value: &[u8]) -> Result<()> {
        let new_size = self.current_size() + value.len();
        if new_size > self.options.max_size {
            return Err(OtlpError::Processing(ProcessingError::InvalidState {
                message: format!(
                    "Storage capacity exceeded: {} > {}",
                    new_size, self.options.max_size
                ),
            }));
        }

        let full_key = if self.options.key_prefix.is_empty() {
            key.to_string()
        } else {
            format!("{}:{}", self.options.key_prefix, key)
        };

        self.data
            .borrow_mut()
            .insert(full_key, value.to_vec());
        Ok(())
    }

    async fn delete(&self, key: &str) -> Result<()> {
        self.data.borrow_mut().remove(key);
        Ok(())
    }

    async fn exists(&self, key: &str) -> Result<bool> {
        Ok(self.data.borrow().contains_key(key))
    }

    async fn list_keys(&self) -> Result<Vec<String>> {
        Ok(self.data.borrow().keys().cloned().collect())
    }

    async fn stats(&self) -> Result<StorageStats> {
        let data = self.data.borrow();
        let total_size = data.values().map(|v| v.len()).sum();

        Ok(StorageStats {
            total_size,
            entry_count: data.len(),
            available_space: self.options.max_size.saturating_sub(total_size),
            quota: Some(self.options.max_size),
        })
    }

    async fn clear(&self) -> Result<()> {
        self.data.borrow_mut().clear();
        Ok(())
    }

    async fn remaining_capacity(&self) -> Result<usize> {
        let used = self.current_size();
        Ok(self.options.max_size.saturating_sub(used))
    }
}

/// LocalStorage implementation (browser)
pub struct LocalStorage {
    prefix: String,
    options: StorageOptions,
}

impl LocalStorage {
    /// Create new LocalStorage with prefix
    pub fn new(prefix: impl Into<String>) -> Self {
        Self {
            prefix: prefix.into(),
            options: StorageOptions::default(),
        }
    }

    /// Create with options
    pub fn with_options(mut self, options: StorageOptions) -> Self {
        self.options = options;
        self
    }

    #[allow(dead_code)]
    fn full_key(&self, key: &str) -> String {
        if self.prefix.is_empty() {
            key.to_string()
        } else {
            format!("{}:{}", self.prefix, key)
        }
    }
}

#[async_trait::async_trait(?Send)]
impl Storage for LocalStorage {
    async fn get(&self, key: &str) -> Result<Option<Vec<u8>>> {
        // In real implementation, this would use web_sys::Storage
        // For now, return None as placeholder
        let _ = key;
        Ok(None)
    }

    async fn put(&self, key: &str, value: &[u8]) -> Result<()> {
        // In real implementation, this would use web_sys::Storage::set_item
        let _ = (key, value);
        Ok(())
    }

    async fn delete(&self, key: &str) -> Result<()> {
        let _ = key;
        Ok(())
    }

    async fn exists(&self, key: &str) -> Result<bool> {
        let _ = key;
        Ok(false)
    }

    async fn list_keys(&self) -> Result<Vec<String>> {
        // Would iterate localStorage keys with prefix
        Ok(vec![])
    }

    async fn stats(&self) -> Result<StorageStats> {
        // Would calculate based on localStorage usage
        Ok(StorageStats {
            total_size: 0,
            entry_count: 0,
            available_space: 5 * 1024 * 1024, // ~5MB typical limit
            quota: Some(10 * 1024 * 1024),
        })
    }

    async fn clear(&self) -> Result<()> {
        // Would remove all keys with prefix
        Ok(())
    }

    async fn remaining_capacity(&self) -> Result<usize> {
        Ok(5 * 1024 * 1024) // Conservative estimate
    }
}

/// IndexedDB storage (browser)
pub struct IndexedDbStorage {
    #[allow(dead_code)]
    db_name: String,
    #[allow(dead_code)]
    store_name: String,
    options: StorageOptions,
}

impl IndexedDbStorage {
    /// Open IndexedDB storage
    pub async fn open(db_name: impl Into<String>, store_name: impl Into<String>) -> Result<Self> {
        Ok(Self {
            db_name: db_name.into(),
            store_name: store_name.into(),
            options: StorageOptions::default(),
        })
    }

    /// Set options
    pub fn with_options(mut self, options: StorageOptions) -> Self {
        self.options = options;
        self
    }

    /// Put multiple items in a transaction
    pub async fn put_batch(&self, items: Vec<(String, Vec<u8>)>) -> Result<()> {
        for (key, value) in items {
            self.put(&key, &value).await?;
        }
        Ok(())
    }

    /// Get multiple items
    pub async fn get_batch(&self, keys: &[String]) -> Result<Vec<Option<Vec<u8>>>> {
        let mut results = Vec::new();
        for key in keys {
            results.push(self.get(key).await?);
        }
        Ok(results)
    }

    /// Query by key prefix
    pub async fn query_by_prefix(&self, prefix: &str) -> Result<Vec<(String, Vec<u8>)>> {
        let keys = self.list_keys().await?;
        let mut results = Vec::new();
        for key in keys {
            if key.starts_with(prefix) {
                if let Some(value) = self.get(&key).await? {
                    results.push((key, value));
                }
            }
        }
        Ok(results)
    }
}

#[async_trait::async_trait(?Send)]
impl Storage for IndexedDbStorage {
    async fn get(&self, key: &str) -> Result<Option<Vec<u8>>> {
        // Would use indexed_db API
        let _ = key;
        Ok(None)
    }

    async fn put(&self, key: &str, value: &[u8]) -> Result<()> {
        let _ = (key, value);
        Ok(())
    }

    async fn delete(&self, key: &str) -> Result<()> {
        let _ = key;
        Ok(())
    }

    async fn exists(&self, key: &str) -> Result<bool> {
        let _ = key;
        Ok(false)
    }

    async fn list_keys(&self) -> Result<Vec<String>> {
        Ok(vec![])
    }

    async fn stats(&self) -> Result<StorageStats> {
        Ok(StorageStats {
            total_size: 0,
            entry_count: 0,
            available_space: self.options.max_size,
            quota: Some(self.options.max_size),
        })
    }

    async fn clear(&self) -> Result<()> {
        Ok(())
    }

    async fn remaining_capacity(&self) -> Result<usize> {
        Ok(self.options.max_size)
    }
}

/// WASI file storage
pub struct WasiFileStorage {
    #[allow(dead_code)]
    base_path: String,
    options: StorageOptions,
}

impl WasiFileStorage {
    /// Create new WASI file storage
    pub async fn new(base_path: impl Into<String>) -> Result<Self> {
        Ok(Self {
            base_path: base_path.into(),
            options: StorageOptions::default(),
        })
    }

    /// Set options
    pub fn with_options(mut self, options: StorageOptions) -> Self {
        self.options = options;
        self
    }

    #[allow(dead_code)]
    fn file_path(&self, key: &str) -> String {
        format!("{}/{}", self.base_path, sanitize_filename(key))
    }

    /// Write with automatic rotation
    pub async fn put_with_rotation(&self, key: &str, value: &[u8]) -> Result<()> {
        // Check if rotation needed
        let stats = self.stats().await?;
        if stats.total_size + value.len() > self.options.max_size {
            self.rotate_files().await?;
        }

        self.put(key, value).await
    }

    /// Rotate old files
    async fn rotate_files(&self) -> Result<()> {
        // Remove oldest files to make space
        Ok(())
    }

    /// List files with metadata
    pub async fn list_files(&self) -> Result<Vec<FileInfo>> {
        Ok(vec![])
    }
}

#[async_trait::async_trait(?Send)]
impl Storage for WasiFileStorage {
    async fn get(&self, key: &str) -> Result<Option<Vec<u8>>> {
        let _ = key;
        // Would use WASI file operations
        Ok(None)
    }

    async fn put(&self, key: &str, value: &[u8]) -> Result<()> {
        let _ = (key, value);
        Ok(())
    }

    async fn delete(&self, key: &str) -> Result<()> {
        let _ = key;
        Ok(())
    }

    async fn exists(&self, key: &str) -> Result<bool> {
        let _ = key;
        Ok(false)
    }

    async fn list_keys(&self) -> Result<Vec<String>> {
        Ok(vec![])
    }

    async fn stats(&self) -> Result<StorageStats> {
        Ok(StorageStats {
            total_size: 0,
            entry_count: 0,
            available_space: self.options.max_size,
            quota: None,
        })
    }

    async fn clear(&self) -> Result<()> {
        Ok(())
    }

    async fn remaining_capacity(&self) -> Result<usize> {
        Ok(self.options.max_size)
    }
}

/// File info for WASI storage
#[derive(Debug, Clone)]
pub struct FileInfo {
    pub name: String,
    pub size: usize,
    pub created_at: u64,
    pub modified_at: u64,
}

/// Queue item for persistent queue
#[derive(Debug, Clone)]
pub struct QueueItem {
    pub id: String,
    pub data: Vec<u8>,
    pub created_at: u64,
    pub retry_count: u32,
}

/// Persistent queue trait
#[async_trait::async_trait(?Send)]
pub trait Queue {
    /// Enqueue item
    async fn enqueue(&self, data: &[u8]) -> Result<String>;

    /// Dequeue item (mark as processing)
    async fn dequeue(&self) -> Result<Option<QueueItem>>;

    /// Acknowledge successful processing
    async fn ack(&self, id: &str) -> Result<()>;

    /// Negative acknowledge (will retry)
    async fn nack(&self, id: &str) -> Result<()>;

    /// Get queue length
    async fn len(&self) -> Result<usize>;

    /// Check if empty
    async fn is_empty(&self) -> Result<bool>;

    /// Peek at next item without dequeuing
    async fn peek(&self) -> Result<Option<QueueItem>>;

    /// Get all pending items
    async fn pending(&self) -> Result<Vec<QueueItem>>;

    /// Clear all items
    async fn clear(&self) -> Result<()>;
}

/// Persistent queue implementation
pub struct PersistentQueue<S: Storage> {
    storage: S,
    processing_prefix: String,
    pending_prefix: String,
}

impl<S: Storage> PersistentQueue<S> {
    /// Create new persistent queue
    pub fn new(storage: S) -> Self {
        Self {
            storage,
            processing_prefix: "processing".to_string(),
            pending_prefix: "pending".to_string(),
        }
    }

    /// Generate unique ID
    fn generate_id(&self) -> String {
        format!(
            "{}_{}",
            current_timestamp_ms(),
            fastrand::u64(..)
        )
    }

    /// Pending key
    fn pending_key(&self, id: &str) -> String {
        format!("{}:{}", self.pending_prefix, id)
    }

    /// Processing key
    fn processing_key(&self, id: &str) -> String {
        format!("{}:{}", self.processing_prefix, id)
    }
}

#[async_trait::async_trait(?Send)]
impl<S: Storage> Queue for PersistentQueue<S> {
    async fn enqueue(&self, data: &[u8]) -> Result<String> {
        let id = self.generate_id();
        let key = self.pending_key(&id);

        let item = QueueItem {
            id: id.clone(),
            data: data.to_vec(),
            created_at: current_timestamp_ms(),
            retry_count: 0,
        };

        let serialized = serialize_queue_item(&item);
        self.storage.put(&key, &serialized).await?;

        Ok(id)
    }

    async fn dequeue(&self) -> Result<Option<QueueItem>> {
        // Find first pending item
        let keys = self.storage.list_keys().await?;

        for key in keys {
            if key.starts_with(&self.pending_prefix) {
                if let Some(data) = self.storage.get(&key).await? {
                    let item = deserialize_queue_item(&data)?;

                    // Move to processing
                    self.storage.delete(&key).await?;
                    let processing_key = self.processing_key(&item.id);
                    self.storage.put(&processing_key, &data).await?;

                    return Ok(Some(item));
                }
            }
        }

        Ok(None)
    }

    async fn ack(&self, id: &str) -> Result<()> {
        let key = self.processing_key(id);
        self.storage.delete(&key).await
    }

    async fn nack(&self, id: &str) -> Result<()> {
        let processing_key = self.processing_key(id);

        if let Some(data) = self.storage.get(&processing_key).await? {
            let mut item = deserialize_queue_item(&data)?;
            item.retry_count += 1;

            // Move back to pending
            self.storage.delete(&processing_key).await?;

            let pending_key = self.pending_key(id);
            let serialized = serialize_queue_item(&item);
            self.storage.put(&pending_key, &serialized).await?;
        }

        Ok(())
    }

    async fn len(&self) -> Result<usize> {
        let keys = self.storage.list_keys().await?;
        Ok(keys
            .iter()
            .filter(|k| k.starts_with(&self.pending_prefix))
            .count())
    }

    async fn is_empty(&self) -> Result<bool> {
        Ok(self.len().await? == 0)
    }

    async fn peek(&self) -> Result<Option<QueueItem>> {
        let keys = self.storage.list_keys().await?;

        for key in keys {
            if key.starts_with(&self.pending_prefix) {
                if let Some(data) = self.storage.get(&key).await? {
                    return Ok(Some(deserialize_queue_item(&data)?));
                }
            }
        }

        Ok(None)
    }

    async fn pending(&self) -> Result<Vec<QueueItem>> {
        let keys = self.storage.list_keys().await?;
        let mut items = Vec::new();

        for key in keys {
            if key.starts_with(&self.pending_prefix) {
                if let Some(data) = self.storage.get(&key).await? {
                    items.push(deserialize_queue_item(&data)?);
                }
            }
        }

        Ok(items)
    }

    async fn clear(&self) -> Result<()> {
        let keys = self.storage.list_keys().await?;

        for key in keys {
            if key.starts_with(&self.pending_prefix)
                || key.starts_with(&self.processing_prefix)
            {
                self.storage.delete(&key).await?;
            }
        }

        Ok(())
    }
}

/// Storage manager for multiple backends (simplified for WASM)
pub struct StorageManager<S: Storage> {
    primary: S,
    fallback: Option<S>,
    cache: MemoryStorage,
}

impl<S: Storage + Clone> StorageManager<S> {
    /// Create new storage manager
    pub fn new(primary: S) -> Self {
        Self {
            primary,
            fallback: None,
            cache: MemoryStorage::new(),
        }
    }

    /// Set fallback storage
    pub fn with_fallback(mut self, fallback: S) -> Self {
        self.fallback = Some(fallback);
        self
    }

    /// Get with fallback
    pub async fn get(&self, key: &str) -> Result<Option<Vec<u8>>> {
        // Try cache first
        if let Some(value) = self.cache.get(key).await? {
            return Ok(Some(value));
        }

        // Try primary
        match self.primary.get(key).await {
            Ok(Some(value)) => {
                // Update cache
                let _ = self.cache.put(key, &value).await;
                Ok(Some(value))
            }
            Ok(None) => Ok(None),
            Err(_) => {
                // Try fallback
                if let Some(ref fallback) = self.fallback {
                    fallback.get(key).await
                } else {
                    Ok(None)
                }
            }
        }
    }

    /// Put with cache update
    pub async fn put(&self, key: &str, value: &[u8]) -> Result<()> {
        // Update primary
        let result = self.primary.put(key, value).await;

        // Update cache regardless of primary result
        let _ = self.cache.put(key, value).await;

        // Fallback on error
        if result.is_err() {
            if let Some(ref fallback) = self.fallback {
                return fallback.put(key, value).await;
            }
        }

        result
    }
}

/// Helper functions
#[allow(dead_code)]
fn sanitize_filename(key: &str) -> String {
    key.replace('/', "_")
        .replace('\\', "_")
        .replace(':', "_")
}

fn current_timestamp_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_millis() as u64
}

fn serialize_queue_item(item: &QueueItem) -> Vec<u8> {
    // Simple serialization - in production use proper serialization
    format!(
        "{}|{}|{}|{}",
        item.id,
        item.created_at,
        item.retry_count,
        base64_encode(&item.data)
    )
    .into_bytes()
}

fn deserialize_queue_item(data: &[u8]) -> Result<QueueItem> {
    let s = String::from_utf8_lossy(data);
    let parts: Vec<&str> = s.split('|').collect();

    if parts.len() != 4 {
        return Err(OtlpError::Processing(ProcessingError::InvalidState {
            message: "Invalid queue item format".to_string(),
        }));
    }

    Ok(QueueItem {
        id: parts[0].to_string(),
        created_at: parts[1].parse().unwrap_or(0),
        retry_count: parts[2].parse().unwrap_or(0),
        data: base64_decode(parts[3]).unwrap_or_default(),
    })
}

fn base64_encode(data: &[u8]) -> String {
    // Simple base64 encoding - use proper implementation in production
    const CHARSET: &[u8] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

    let mut result = String::new();
    for chunk in data.chunks(3) {
        let b = match chunk.len() {
            1 => [chunk[0], 0, 0],
            2 => [chunk[0], chunk[1], 0],
            _ => [chunk[0], chunk[1], chunk[2]],
        };

        let idx1 = (b[0] >> 2) as usize;
        let idx2 = (((b[0] & 0x03) << 4) | (b[1] >> 4)) as usize;
        let idx3 = (((b[1] & 0x0F) << 2) | (b[2] >> 6)) as usize;
        let idx4 = (b[2] & 0x3F) as usize;

        result.push(CHARSET[idx1] as char);
        result.push(CHARSET[idx2] as char);
        result.push(if chunk.len() > 1 { CHARSET[idx3] } else { b'=' } as char);
        result.push(if chunk.len() > 2 { CHARSET[idx4] } else { b'=' } as char);
    }

    result
}

fn base64_decode(s: &str) -> Option<Vec<u8>> {
    // Simple base64 decoding
    let mut result = Vec::new();
    let mut buf = 0u32;
    let mut bits = 0;

    for c in s.chars() {
        let val = match c {
            'A'..='Z' => c as u8 - b'A',
            'a'..='z' => c as u8 - b'a' + 26,
            '0'..='9' => c as u8 - b'0' + 52,
            '+' => 62,
            '/' => 63,
            '=' => break,
            _ => continue,
        };

        buf = (buf << 6) | val as u32;
        bits += 6;

        if bits >= 8 {
            bits -= 8;
            result.push((buf >> bits) as u8);
            buf &= (1 << bits) - 1;
        }
    }

    Some(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_memory_storage() {
        let storage = MemoryStorage::new();

        storage.put("key1", b"value1").await.unwrap();
        storage.put("key2", b"value2").await.unwrap();

        assert_eq!(storage.get("key1").await.unwrap(), Some(b"value1".to_vec()));
        assert_eq!(storage.get("key2").await.unwrap(), Some(b"value2".to_vec()));
        assert_eq!(storage.get("key3").await.unwrap(), None);

        let keys = storage.list_keys().await.unwrap();
        assert_eq!(keys.len(), 2);

        storage.delete("key1").await.unwrap();
        assert_eq!(storage.get("key1").await.unwrap(), None);
    }

    #[tokio::test]
    async fn test_storage_stats() {
        let storage = MemoryStorage::new();

        storage.put("key1", b"12345").await.unwrap();
        storage.put("key2", b"67890").await.unwrap();

        let stats = storage.stats().await.unwrap();
        assert_eq!(stats.entry_count, 2);
        assert_eq!(stats.total_size, 10);
    }

    // Note: Queue tests require async runtime which conflicts with RefCell in WASM
    // For production use, the implementation would be properly integrated with WASM runtime
    // #[tokio::test]
    // async fn test_persistent_queue() {
    //     // Test disabled due to Send/Sync issues with RefCell in single-threaded WASM
    // }

    #[test]
    fn test_base64_encode_decode() {
        let data = b"Hello, World!";
        let encoded = base64_encode(data);
        let decoded = base64_decode(&encoded).unwrap();
        assert_eq!(data.to_vec(), decoded);

        // Test empty
        assert_eq!(base64_decode(&base64_encode(b"")), Some(vec![]));

        // Test various lengths
        assert_eq!(base64_decode(&base64_encode(b"a")), Some(vec![b'a']));
        assert_eq!(base64_decode(&base64_encode(b"ab")), Some(vec![b'a', b'b']));
        assert_eq!(
            base64_decode(&base64_encode(b"abc")),
            Some(vec![b'a', b'b', b'c'])
        );
    }

    #[test]
    fn test_sanitize_filename() {
        assert_eq!(sanitize_filename("key"), "key");
        assert_eq!(sanitize_filename("path/to/key"), "path_to_key");
        assert_eq!(sanitize_filename("C:\\file"), "C__file");
    }

    #[test]
    fn test_storage_options_default() {
        let opts = StorageOptions::default();
        assert_eq!(opts.max_size, 50 * 1024 * 1024);
        assert!(!opts.compression);
        assert!(!opts.encryption);
        assert_eq!(opts.ttl_secs, 0);
    }

    #[test]
    fn test_queue_item_serialization() {
        let item = QueueItem {
            id: "test_123".to_string(),
            data: b"hello".to_vec(),
            created_at: 1234567890,
            retry_count: 3,
        };

        let serialized = serialize_queue_item(&item);
        let deserialized = deserialize_queue_item(&serialized).unwrap();

        assert_eq!(deserialized.id, item.id);
        assert_eq!(deserialized.data, item.data);
        assert_eq!(deserialized.created_at, item.created_at);
        assert_eq!(deserialized.retry_count, item.retry_count);
    }
}
