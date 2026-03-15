//! 连接池模块测试

#[cfg(test)]
mod tests {
    use super::super::*;
    use std::time::Duration;

    #[test]
    fn test_connection_pool_config_default() {
        let config = ConnectionPoolConfig::default();
        assert_eq!(config.min_connections, 5);
        assert_eq!(config.max_connections, 100);
        assert_eq!(config.max_idle_connections, 20);
        assert_eq!(config.connection_timeout, Duration::from_secs(10));
        assert_eq!(config.idle_timeout, Duration::from_secs(300));
        assert_eq!(config.retry_attempts, 3);
        assert_eq!(config.retry_delay, Duration::from_millis(100));
        assert!(matches!(config.load_balancing_strategy, LoadBalancingStrategy::RoundRobin));
    }

    #[test]
    fn test_connection_pool_config_custom() {
        let config = ConnectionPoolConfig {
            min_connections: 10,
            max_connections: 200,
            max_idle_connections: 50,
            connection_timeout: Duration::from_secs(30),
            idle_timeout: Duration::from_secs(600),
            health_check_interval: Duration::from_secs(60),
            retry_attempts: 5,
            retry_delay: Duration::from_millis(500),
            load_balancing_strategy: LoadBalancingStrategy::LeastConnections,
        };
        
        assert_eq!(config.min_connections, 10);
        assert_eq!(config.max_connections, 200);
        assert_eq!(config.max_idle_connections, 50);
        assert_eq!(config.connection_timeout, Duration::from_secs(30));
        assert_eq!(config.idle_timeout, Duration::from_secs(600));
        assert_eq!(config.retry_attempts, 5);
        assert_eq!(config.retry_delay, Duration::from_millis(500));
        assert!(matches!(config.load_balancing_strategy, LoadBalancingStrategy::LeastConnections));
    }

    #[test]
    fn test_load_balancing_strategy_variants() {
        // Test RoundRobin
        let strategy = LoadBalancingStrategy::RoundRobin;
        assert!(matches!(strategy, LoadBalancingStrategy::RoundRobin));

        // Test Random
        let strategy = LoadBalancingStrategy::Random;
        assert!(matches!(strategy, LoadBalancingStrategy::Random));

        // Test LeastConnections
        let strategy = LoadBalancingStrategy::LeastConnections;
        assert!(matches!(strategy, LoadBalancingStrategy::LeastConnections));

        // Test WeightedRoundRobin
        let weights = vec![1, 2, 3];
        let strategy = LoadBalancingStrategy::WeightedRoundRobin(weights.clone());
        assert!(matches!(strategy, LoadBalancingStrategy::WeightedRoundRobin(_)));
    }

    #[test]
    fn test_connection_pool_stats_clone() {
        let stats = ConnectionPoolStats::default();
        stats.total_connections.store(10, Ordering::Relaxed);
        stats.active_connections.store(5, Ordering::Relaxed);
        
        let cloned = stats.clone();
        assert_eq!(cloned.total_connections.load(Ordering::Relaxed), 10);
        assert_eq!(cloned.active_connections.load(Ordering::Relaxed), 5);
    }

    #[test]
    fn test_connection_pool_stats_default() {
        let stats = ConnectionPoolStats::default();
        assert_eq!(stats.total_connections.load(Ordering::Relaxed), 0);
        assert_eq!(stats.active_connections.load(Ordering::Relaxed), 0);
        assert_eq!(stats.idle_connections.load(Ordering::Relaxed), 0);
        assert_eq!(stats.connection_requests.load(Ordering::Relaxed), 0);
        assert_eq!(stats.connection_hits.load(Ordering::Relaxed), 0);
        assert_eq!(stats.connection_misses.load(Ordering::Relaxed), 0);
        assert_eq!(stats.connection_errors.load(Ordering::Relaxed), 0);
        assert_eq!(stats.average_connection_time.load(Ordering::Relaxed), 0);
        assert_eq!(stats.peak_connections.load(Ordering::Relaxed), 0);
    }
}
