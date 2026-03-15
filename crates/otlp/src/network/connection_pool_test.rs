//! 连接池模块测试

#[cfg(test)]
mod tests {
    use super::super::*;

    #[test]
    fn test_connection_pool_config_default() {
        let config = ConnectionPoolConfig::default();
        assert_eq!(config.max_size, 10);
        assert_eq!(config.min_idle, 2);
        assert!(config.max_lifetime > Duration::from_secs(0));
    }

    #[test]
    fn test_connection_pool_config_builder() {
        let config = ConnectionPoolConfig {
            max_size: 20,
            min_idle: 5,
            max_lifetime: Duration::from_secs(300),
            connection_timeout: Duration::from_secs(10),
            retry_attempts: 3,
            health_check_interval: Duration::from_secs(30),
        };
        assert_eq!(config.max_size, 20);
        assert_eq!(config.min_idle, 5);
    }
}
