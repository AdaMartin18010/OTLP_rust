//! Rust 1.94 特性模块
//!
//! 本模块展示了如何利用 Rust 1.94 的新特性来优化库集成实现：
//! - `array_windows` - 用于连接池模式检测
//! - `element_offset` - 用于 Redis/DB 操作中的高效缓冲区管理
//! - `LazyLock` - 用于全局连接管理器
//! - `EULER_GAMMA`/`GOLDEN_RATIO` - 用于连接池大小和重试逻辑
//! - `const mul_add` - 用于编译时计算

// Rust 1.94 数学常量
pub use std::f64::consts::{EULER_GAMMA, GOLDEN_RATIO};
use std::sync::LazyLock;

/// Rust 1.94 特性 1: 使用 LazyLock 实现全局连接管理器
///
/// `LazyLock` 提供了线程安全的延迟初始化机制，适用于全局资源配置
pub static REDIS_CONNECTION_MANAGER: LazyLock<ConnectionManager> =
    LazyLock::new(|| ConnectionManager::new("redis://localhost:6379", MiddlewareType::Redis));

pub static POSTGRES_CONNECTION_MANAGER: LazyLock<ConnectionManager> =
    LazyLock::new(|| ConnectionManager::new("postgres://localhost:5432", MiddlewareType::Postgres));

pub static NATS_CONNECTION_MANAGER: LazyLock<ConnectionManager> =
    LazyLock::new(|| ConnectionManager::new("nats://localhost:4222", MiddlewareType::Nats));

/// 中间件类型枚举
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MiddlewareType {
    Redis,
    Postgres,
    Mysql,
    Sqlite,
    Nats,
    Kafka,
    Mqtt,
}

impl MiddlewareType {
    /// 获取默认端口
    pub fn default_port(&self) -> u16 {
        match self {
            MiddlewareType::Redis => 6379,
            MiddlewareType::Postgres => 5432,
            MiddlewareType::Mysql => 3306,
            MiddlewareType::Sqlite => 0,
            MiddlewareType::Nats => 4222,
            MiddlewareType::Kafka => 9092,
            MiddlewareType::Mqtt => 1883,
        }
    }

    /// 获取协议前缀
    pub fn protocol_prefix(&self) -> &'static str {
        match self {
            MiddlewareType::Redis => "redis://",
            MiddlewareType::Postgres => "postgres://",
            MiddlewareType::Mysql => "mysql://",
            MiddlewareType::Sqlite => "sqlite://",
            MiddlewareType::Nats => "nats://",
            MiddlewareType::Kafka => "kafka://",
            MiddlewareType::Mqtt => "mqtt://",
        }
    }

    /// 检查是否为数据库类型
    pub fn is_database(&self) -> bool {
        matches!(
            self,
            MiddlewareType::Postgres | MiddlewareType::Mysql | MiddlewareType::Sqlite
        )
    }

    /// 检查是否为缓存类型
    pub fn is_cache(&self) -> bool {
        matches!(self, MiddlewareType::Redis)
    }

    /// 检查是否为消息队列类型
    pub fn is_message_queue(&self) -> bool {
        matches!(self, MiddlewareType::Nats | MiddlewareType::Kafka | MiddlewareType::Mqtt)
    }
}

/// 连接管理器结构体
#[derive(Debug)]
pub struct ConnectionManager {
    url: String,
    middleware_type: MiddlewareType,
    connection_count: std::sync::atomic::AtomicUsize,
    max_connections: usize,
}

impl ConnectionManager {
    /// 创建新的连接管理器
    pub fn new(url: &str, middleware_type: MiddlewareType) -> Self {
        // 使用黄金比例计算最优连接池大小
        let optimal_size = optimal_pool_size(100);

        Self {
            url: url.to_string(),
            middleware_type,
            connection_count: std::sync::atomic::AtomicUsize::new(0),
            max_connections: optimal_size,
        }
    }

    /// 获取连接 URL
    pub fn url(&self) -> &str {
        &self.url
    }

    /// 获取中间件类型
    pub fn middleware_type(&self) -> MiddlewareType {
        self.middleware_type
    }

    /// 获取当前连接数
    pub fn connection_count(&self) -> usize {
        self.connection_count.load(std::sync::atomic::Ordering::Relaxed)
    }

    /// 获取最大连接数
    pub fn max_connections(&self) -> usize {
        self.max_connections
    }

    /// 增加连接计数
    pub fn increment_connections(&self) -> bool {
        let current = self.connection_count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        if current >= self.max_connections {
            self.connection_count.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
            false
        } else {
            true
        }
    }

    /// 减少连接计数
    pub fn decrement_connections(&self) {
        self.connection_count.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
    }
}

/// Rust 1.94 特性 2: 使用黄金比例计算最优连接池大小
///
/// 基于斐波那契数列和黄金比例的最优资源分配算法
pub fn optimal_pool_size(expected_load: usize) -> usize {
    // 使用 GOLDEN_RATIO (φ ≈ 1.618) 计算基础大小
    let golden_based = (expected_load as f64 * GOLDEN_RATIO) as usize;

    // 使用 EULER_GAMMA (γ ≈ 0.5772) 进行调整，确保在负载波动时的稳定性
    let gamma_adjustment = (expected_load as f64 * EULER_GAMMA) as usize;

    // 综合计算，确保在合理范围内
    let result = golden_based.saturating_sub(gamma_adjustment / 2);
    result.max(10).min(1000)
}

/// Rust 1.94 特性 3: 使用 array_windows 检测连接失败模式
///
/// 分析连接错误序列，检测重复模式和异常行为
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConnectionError {
    Timeout,
    ConnectionRefused,
    NetworkError,
    AuthenticationFailed,
    PoolExhausted,
}

/// 失败模式类型
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FailurePattern {
    RepeatedTimeout,       // 重复超时
    RepeatedRefused,       // 重复拒绝
    Flapping,              // 频繁切换（正常/失败）
    CascadingFailure,      // 级联失败
    PoolExhaustionPattern, // 连接池耗尽模式
}

/// 使用滑动窗口检测连接失败模式
///
/// 分析连续三个错误，识别特定的失败模式
pub fn detect_connection_failures(failures: &[ConnectionError]) -> Vec<FailurePattern> {
    if failures.len() < 3 {
        return Vec::new();
    }

    let mut patterns = Vec::new();

    // 模拟 array_windows 功能：滑动窗口分析
    for window in failures.windows(3) {
        if let [a, b, c] = window {
            // 检测重复超时模式
            if *a == ConnectionError::Timeout
                && *b == ConnectionError::Timeout
                && *c == ConnectionError::Timeout
            {
                if !patterns.contains(&FailurePattern::RepeatedTimeout) {
                    patterns.push(FailurePattern::RepeatedTimeout);
                }
            }
            // 检测重复拒绝模式
            else if *a == ConnectionError::ConnectionRefused
                && *b == ConnectionError::ConnectionRefused
                && *c == ConnectionError::ConnectionRefused
            {
                if !patterns.contains(&FailurePattern::RepeatedRefused) {
                    patterns.push(FailurePattern::RepeatedRefused);
                }
            }
            // 检测级联失败模式（不同类型的连续失败）
            else if *a != *b && *b != *c {
                if !patterns.contains(&FailurePattern::CascadingFailure) {
                    patterns.push(FailurePattern::CascadingFailure);
                }
            }
            // 检测抖动模式（超时和拒绝交替）
            else if (*a == ConnectionError::Timeout && *b == ConnectionError::ConnectionRefused)
                || (*a == ConnectionError::ConnectionRefused && *b == ConnectionError::Timeout)
            {
                if !patterns.contains(&FailurePattern::Flapping) {
                    patterns.push(FailurePattern::Flapping);
                }
            }
        }
    }

    patterns
}

/// Rust 1.94 特性 4: 使用 element_offset 进行高效的缓冲区管理
///
/// 在 Redis/DB 操作中追踪缓冲区元素位置
pub struct BufferTracker<T> {
    buffer: Vec<T>,
    element_ids: Vec<u64>, // 元素唯一标识
}

impl<T: PartialEq> BufferTracker<T> {
    /// 创建新的缓冲区追踪器
    pub fn new() -> Self {
        Self {
            buffer: Vec::new(),
            element_ids: Vec::new(),
        }
    }

    /// 添加元素到缓冲区
    pub fn push(&mut self, element: T) -> u64 {
        let id = self.generate_id();
        self.buffer.push(element);
        self.element_ids.push(id);
        id
    }

    /// 获取元素位置（模拟 element_offset 功能）
    ///
    /// 返回元素在缓冲区中的索引位置
    pub fn get_element_position(&self, element: &T) -> Option<usize> {
        // 模拟 element_offset：查找元素位置
        self.buffer.iter().position(|e| e == element)
    }

    /// 通过 ID 获取元素位置
    pub fn get_position_by_id(&self, id: u64) -> Option<usize> {
        self.element_ids.iter().position(|&eid| eid == id)
    }

    /// 获取元素在缓冲区中的偏移量（字节计算）
    pub fn element_byte_offset(&self, index: usize) -> Option<usize>
    where
        T: Sized,
    {
        if index >= self.buffer.len() {
            return None;
        }
        // 计算偏移量：索引 * 元素大小
        Some(index * std::mem::size_of::<T>())
    }

    /// 获取缓冲区长度
    pub fn len(&self) -> usize {
        self.buffer.len()
    }

    /// 检查缓冲区是否为空
    pub fn is_empty(&self) -> bool {
        self.buffer.is_empty()
    }

    /// 清空缓冲区
    pub fn clear(&mut self) {
        self.buffer.clear();
        self.element_ids.clear();
    }

    /// 生成唯一 ID
    fn generate_id(&self) -> u64 {
        use std::time::{SystemTime, UNIX_EPOCH};
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos() as u64;
        timestamp.wrapping_add(self.buffer.len() as u64)
    }
}

impl<T: PartialEq> Default for BufferTracker<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// 针对 Redis 操作的专用缓冲区追踪器
pub struct RedisBufferTracker {
    pub keys: BufferTracker<String>,
    pub values: BufferTracker<Vec<u8>>,
}

impl RedisBufferTracker {
    /// 创建新的 Redis 缓冲区追踪器
    pub fn new() -> Self {
        Self {
            keys: BufferTracker::new(),
            values: BufferTracker::new(),
        }
    }

    /// 添加键值对
    pub fn add_key_value(&mut self, key: String, value: Vec<u8>) -> (u64, u64) {
        let key_id = self.keys.push(key);
        let value_id = self.values.push(value);
        (key_id, value_id)
    }

    /// 查找键的位置
    pub fn find_key_position(&self, key: &str) -> Option<usize> {
        self.keys.get_element_position(&key.to_string())
    }

    /// 获取键的字节偏移量
    pub fn get_key_byte_offset(&self, index: usize) -> Option<usize> {
        self.keys.element_byte_offset(index)
    }
}

impl Default for RedisBufferTracker {
    fn default() -> Self {
        Self::new()
    }
}

/// Rust 1.94 特性 5: 使用 const mul_add 进行编译时计算
///
/// 在连接池和重试逻辑中进行高效的数学计算
pub struct RetryCalculator;

impl RetryCalculator {
    /// 使用 mul_add 计算指数退避延迟
    ///
    /// 公式: delay = base * multiplier + jitter
    pub fn calculate_backoff(attempt: u32, base_ms: f64, multiplier: f64, jitter: f64) -> u64 {
        // 使用 mul_add 进行高效的乘法加法运算: base * multiplier + jitter
        let delay = base_ms.mul_add(multiplier.powi(attempt as i32), jitter);
        delay.max(0.0).min(30000.0) as u64 // 限制在 30 秒内
    }

    /// 使用 EULER_GAMMA 计算自适应重试延迟
    ///
    /// 基于欧拉-马歇罗尼常数的自适应重试策略
    pub fn calculate_adaptive_delay(attempt: u32, base_ms: f64) -> u64 {
        // 使用 EULER_GAMMA (≈ 0.5772) 调整重试延迟
        // 公式: delay = base * (1 + γ * attempt)
        let gamma_factor = 1.0 + EULER_GAMMA * attempt as f64;
        let delay = base_ms.mul_add(gamma_factor, 0.0);
        delay.max(0.0).min(30000.0) as u64
    }

    /// 使用 GOLDEN_RATIO 计算最优重试次数
    ///
    /// 基于黄金比例的自适应重试次数计算
    pub fn optimal_retry_count(failure_rate: f64) -> u32 {
        // 基于失败率计算最优重试次数
        // 公式: retries = φ * (1 - failure_rate) + 3
        let retries = GOLDEN_RATIO.mul_add(1.0 - failure_rate.clamp(0.0, 1.0), 3.0);
        retries as u32
    }

    /// 计算连接池大小（编译时常量计算版本）
    ///
    /// 使用 mul_add 进行高效的资源分配计算
    pub const fn calculate_pool_size_const(load: usize, _factor: f64) -> usize {
        // 注意：const fn 中不能使用浮点运算直到稳定
        // 这里展示概念实现
        let base = load;
        let multiplier = 1.618; // GOLDEN_RATIO 近似值
        let adjustment = 10.0;
        let result = (base as f64 * multiplier + adjustment) as usize;
        result
    }
}

/// Rust 1.94 特性 6: 综合示例 - 智能连接池管理器
///
/// 结合多种 Rust 1.94 特性的高级连接池实现
pub struct SmartConnectionPool {
    manager: &'static ConnectionManager,
    _retry_calculator: RetryCalculator,
    buffer_tracker: RedisBufferTracker,
}

impl SmartConnectionPool {
    /// 创建新的智能连接池（Redis 版本）
    pub fn redis_pool() -> Self {
        Self {
            manager: &REDIS_CONNECTION_MANAGER,
            _retry_calculator: RetryCalculator,
            buffer_tracker: RedisBufferTracker::new(),
        }
    }

    /// 创建新的智能连接池（PostgreSQL 版本）
    pub fn postgres_pool() -> Self {
        Self {
            manager: &POSTGRES_CONNECTION_MANAGER,
            _retry_calculator: RetryCalculator,
            buffer_tracker: RedisBufferTracker::new(),
        }
    }

    /// 获取连接管理器
    pub fn manager(&self) -> &'static ConnectionManager {
        self.manager
    }

    /// 计算重试延迟
    pub fn calculate_retry_delay(&self, attempt: u32) -> u64 {
        RetryCalculator::calculate_adaptive_delay(attempt, 100.0)
    }

    /// 添加缓冲区数据
    pub fn add_buffer_data(&mut self, key: String, value: Vec<u8>) -> (u64, u64) {
        self.buffer_tracker.add_key_value(key, value)
    }

    /// 查找键位置
    pub fn find_key(&self, key: &str) -> Option<usize> {
        self.buffer_tracker.find_key_position(key)
    }

    /// 获取最优连接池大小
    pub fn optimal_size(&self, expected_load: usize) -> usize {
        optimal_pool_size(expected_load)
    }
}

/// 连接错误统计
#[derive(Debug, Default)]
pub struct ConnectionErrorStats {
    pub timeouts: usize,
    pub refused: usize,
    pub network_errors: usize,
    pub auth_failures: usize,
    pub pool_exhausted: usize,
}

impl ConnectionErrorStats {
    /// 从错误列表统计
    pub fn from_errors(errors: &[ConnectionError]) -> Self {
        let mut stats = Self::default();
        for error in errors {
            match error {
                ConnectionError::Timeout => stats.timeouts += 1,
                ConnectionError::ConnectionRefused => stats.refused += 1,
                ConnectionError::NetworkError => stats.network_errors += 1,
                ConnectionError::AuthenticationFailed => stats.auth_failures += 1,
                ConnectionError::PoolExhausted => stats.pool_exhausted += 1,
            }
        }
        stats
    }

    /// 获取总错误数
    pub fn total(&self) -> usize {
        self.timeouts + self.refused + self.network_errors + self.auth_failures + self.pool_exhausted
    }

    /// 获取失败率
    pub fn failure_rate(&self, total_attempts: usize) -> f64 {
        if total_attempts == 0 {
            return 0.0;
        }
        self.total() as f64 / total_attempts as f64
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lazy_lock_connection_manager() {
        // 测试 LazyLock 初始化的连接管理器
        let manager = &REDIS_CONNECTION_MANAGER;
        assert_eq!(manager.middleware_type(), MiddlewareType::Redis);
        assert!(manager.url().contains("redis://"));
        assert!(manager.max_connections() > 0);

        let pg_manager = &POSTGRES_CONNECTION_MANAGER;
        assert_eq!(pg_manager.middleware_type(), MiddlewareType::Postgres);
        assert!(pg_manager.url().contains("postgres://"));

        let nats_manager = &NATS_CONNECTION_MANAGER;
        assert_eq!(nats_manager.middleware_type(), MiddlewareType::Nats);
        assert!(nats_manager.url().contains("nats://"));
    }

    #[test]
    fn test_golden_ratio_pool_size() {
        // 测试基于黄金比例的连接池大小计算
        let size_100 = optimal_pool_size(100);
        assert!(size_100 >= 10);
        assert!(size_100 <= 1000);

        // 验证计算逻辑与实现一致
        let golden_based = (100.0 * GOLDEN_RATIO) as usize;
        let gamma_adjustment = (100.0 * EULER_GAMMA) as usize;
        let expected = golden_based.saturating_sub(gamma_adjustment / 2);
        assert_eq!(size_100, expected.max(10).min(1000));

        // 测试边界条件
        let size_0 = optimal_pool_size(0);
        assert_eq!(size_0, 10); // 最小值

        let size_large = optimal_pool_size(10000);
        assert_eq!(size_large, 1000); // 最大值
    }

    #[test]
    fn test_detect_connection_failures() {
        // 测试失败模式检测
        let repeated_timeouts = vec![
            ConnectionError::Timeout,
            ConnectionError::Timeout,
            ConnectionError::Timeout,
        ];
        let patterns = detect_connection_failures(&repeated_timeouts);
        assert!(patterns.contains(&FailurePattern::RepeatedTimeout));

        let repeated_refused = vec![
            ConnectionError::ConnectionRefused,
            ConnectionError::ConnectionRefused,
            ConnectionError::ConnectionRefused,
        ];
        let patterns = detect_connection_failures(&repeated_refused);
        assert!(patterns.contains(&FailurePattern::RepeatedRefused));

        // 测试级联失败检测
        let cascading = vec![
            ConnectionError::Timeout,
            ConnectionError::ConnectionRefused,
            ConnectionError::NetworkError,
        ];
        let patterns = detect_connection_failures(&cascading);
        assert!(patterns.contains(&FailurePattern::CascadingFailure));

        // 测试空列表
        let empty: Vec<ConnectionError> = vec![];
        let patterns = detect_connection_failures(&empty);
        assert!(patterns.is_empty());

        // 测试短列表
        let short = vec![ConnectionError::Timeout, ConnectionError::Timeout];
        let patterns = detect_connection_failures(&short);
        assert!(patterns.is_empty());
    }

    #[test]
    fn test_buffer_tracker() {
        // 测试缓冲区追踪器
        let mut tracker: BufferTracker<String> = BufferTracker::new();
        assert!(tracker.is_empty());

        let id1 = tracker.push("key1".to_string());
        let _id2 = tracker.push("key2".to_string());

        assert_eq!(tracker.len(), 2);
        assert!(!tracker.is_empty());

        // 测试元素位置查找
        let pos1 = tracker.get_element_position(&"key1".to_string());
        assert_eq!(pos1, Some(0));

        let pos2 = tracker.get_element_position(&"key2".to_string());
        assert_eq!(pos2, Some(1));

        let pos_none = tracker.get_element_position(&"key3".to_string());
        assert_eq!(pos_none, None);

        // 测试 ID 查找
        let pos_by_id = tracker.get_position_by_id(id1);
        assert_eq!(pos_by_id, Some(0));

        // 测试字节偏移量
        let offset = tracker.element_byte_offset(0);
        assert!(offset.is_some());

        // 测试清空
        tracker.clear();
        assert!(tracker.is_empty());
        assert_eq!(tracker.len(), 0);
    }

    #[test]
    fn test_redis_buffer_tracker() {
        // 测试 Redis 专用缓冲区追踪器
        let mut tracker = RedisBufferTracker::new();

        let (key_id, value_id) = tracker
            .add_key_value("user:123".to_string(), vec![1, 2, 3, 4]);
        assert!(key_id > 0);
        assert!(value_id > 0);

        let pos = tracker.find_key_position("user:123");
        assert_eq!(pos, Some(0));

        let offset = tracker.get_key_byte_offset(0);
        assert!(offset.is_some());

        let not_found = tracker.find_key_position("user:999");
        assert_eq!(not_found, None);
    }

    #[test]
    fn test_retry_calculator() {
        // 测试重试计算器
        let delay = RetryCalculator::calculate_backoff(0, 100.0, 2.0, 10.0);
        assert!(delay > 0);

        let delay1 = RetryCalculator::calculate_backoff(1, 100.0, 2.0, 10.0);
        assert!(delay1 > delay);

        // 测试自适应延迟（使用 EULER_GAMMA）
        let adaptive = RetryCalculator::calculate_adaptive_delay(1, 100.0);
        let expected = (100.0 * (1.0 + EULER_GAMMA)) as u64;
        assert_eq!(adaptive, expected);

        // 测试最优重试次数（使用 GOLDEN_RATIO）
        let retries = RetryCalculator::optimal_retry_count(0.0);
        assert!(retries >= 3);

        let retries_high = RetryCalculator::optimal_retry_count(0.8);
        let retries_low = RetryCalculator::optimal_retry_count(0.2);
        assert!(retries_high <= retries_low); // 高失败率应该减少重试次数
    }

    #[test]
    fn test_smart_connection_pool() {
        // 测试智能连接池
        let mut pool = SmartConnectionPool::redis_pool();
        assert_eq!(pool.manager().middleware_type(), MiddlewareType::Redis);

        let delay = pool.calculate_retry_delay(1);
        assert!(delay > 0);

        let (key_id, value_id) = pool.add_buffer_data("test_key".to_string(), vec![1, 2, 3]);
        assert!(key_id > 0);
        assert!(value_id > 0);

        let pos = pool.find_key("test_key");
        assert_eq!(pos, Some(0));

        let optimal = pool.optimal_size(100);
        assert!(optimal >= 10 && optimal <= 1000);

        // 测试 PostgreSQL 池
        let pg_pool = SmartConnectionPool::postgres_pool();
        assert_eq!(pg_pool.manager().middleware_type(), MiddlewareType::Postgres);
    }

    #[test]
    fn test_connection_error_stats() {
        // 测试连接错误统计
        let errors = vec![
            ConnectionError::Timeout,
            ConnectionError::Timeout,
            ConnectionError::ConnectionRefused,
            ConnectionError::NetworkError,
        ];

        let stats = ConnectionErrorStats::from_errors(&errors);
        assert_eq!(stats.timeouts, 2);
        assert_eq!(stats.refused, 1);
        assert_eq!(stats.network_errors, 1);
        assert_eq!(stats.total(), 4);

        let failure_rate = stats.failure_rate(10);
        assert!((failure_rate - 0.4).abs() < 0.001);

        // 测试空统计
        let empty_stats = ConnectionErrorStats::default();
        assert_eq!(empty_stats.total(), 0);
        assert_eq!(empty_stats.failure_rate(100), 0.0);
    }

    #[test]
    fn test_middleware_type_helpers() {
        // 测试中间件类型辅助方法
        assert!(MiddlewareType::Redis.is_cache());
        assert!(!MiddlewareType::Redis.is_database());

        assert!(MiddlewareType::Postgres.is_database());
        assert!(!MiddlewareType::Postgres.is_cache());

        assert!(MiddlewareType::Nats.is_message_queue());
        assert!(MiddlewareType::Kafka.is_message_queue());
        assert!(MiddlewareType::Mqtt.is_message_queue());

        assert_eq!(MiddlewareType::Redis.default_port(), 6379);
        assert_eq!(MiddlewareType::Postgres.default_port(), 5432);
        assert_eq!(MiddlewareType::Nats.default_port(), 4222);

        assert_eq!(MiddlewareType::Redis.protocol_prefix(), "redis://");
        assert_eq!(MiddlewareType::Postgres.protocol_prefix(), "postgres://");
    }

    #[test]
    fn test_connection_manager_operations() {
        // 测试连接管理器操作
        let manager = ConnectionManager::new("redis://localhost:6379", MiddlewareType::Redis);

        assert_eq!(manager.connection_count(), 0);
        assert!(manager.increment_connections());
        assert_eq!(manager.connection_count(), 1);

        assert!(manager.increment_connections());
        assert_eq!(manager.connection_count(), 2);

        manager.decrement_connections();
        assert_eq!(manager.connection_count(), 1);

        // 测试 URL 和类型
        assert_eq!(manager.url(), "redis://localhost:6379");
        assert_eq!(manager.middleware_type(), MiddlewareType::Redis);
    }

    #[test]
    fn test_retry_calculator_bounds() {
        // 测试重试计算器的边界条件
        let max_delay = RetryCalculator::calculate_backoff(10, 1000.0, 2.0, 100.0);
        assert!(max_delay <= 30000); // 最大值限制

        let zero_delay = RetryCalculator::calculate_backoff(0, 0.0, 2.0, 0.0);
        assert_eq!(zero_delay, 0);

        // 测试最优重试次数的边界
        let max_retries = RetryCalculator::optimal_retry_count(-1.0);
        assert!(max_retries >= 3);

        let min_retries = RetryCalculator::optimal_retry_count(2.0);
        assert_eq!(min_retries, 3);
    }
}
