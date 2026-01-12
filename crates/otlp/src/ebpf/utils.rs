//! # eBPF 工具函数
//!
//! 提供 eBPF 相关的工具函数和帮助函数
//!
//! ## Rust 1.92 特性应用
//!
//! - **改进的工具函数**: 利用 Rust 1.92 的工具函数优化提升性能
//! - **类型安全的工具**: 使用 Rust 1.92 的类型系统确保工具函数的安全性

use crate::error::Result;
use crate::ebpf::types::EbpfConfig;

/// 验证 eBPF 配置
pub fn validate_config(config: &EbpfConfig) -> Result<()> {
    // 验证采样频率
    if config.sample_rate == 0 {
        return Err(crate::error::OtlpError::Configuration(
            crate::error::ConfigurationError::ValueOutOfRange {
                field: "sample_rate".to_string(),
                value: config.sample_rate as f64,
                min: 1.0,
                max: 1000.0,
            },
        ));
    }

    if config.sample_rate > 1000 {
        return Err(crate::error::OtlpError::Configuration(
            crate::error::ConfigurationError::ValueOutOfRange {
                field: "sample_rate".to_string(),
                value: config.sample_rate as f64,
                min: 1.0,
                max: 1000.0,
            },
        ));
    }

    // 验证最大采样数
    if config.max_samples == 0 {
        return Err(crate::error::OtlpError::Configuration(
            crate::error::ConfigurationError::ValueOutOfRange {
                field: "max_samples".to_string(),
                value: config.max_samples as f64,
                min: 1.0,
                max: 10_000_000.0,
            },
        ));
    }

    // 验证持续时间
    if config.duration.as_secs() == 0 {
        return Err(crate::error::OtlpError::Configuration(
            crate::error::ConfigurationError::InvalidTimeout {
                timeout: config.duration,
            },
        ));
    }

    Ok(())
}

/// 计算推荐的采样频率
pub fn recommended_sample_rate(env: &str) -> u32 {
    match env {
        "production" | "prod" => 19,  // 生产环境：低采样率
        "staging" => 49,               // 预发布环境：中等采样率
        "development" | "dev" => 99,   // 开发环境：默认采样率
        "debug" => 199,                // 调试模式：高采样率
        _ => 99,                       // 默认：99Hz
    }
}

/// 计算推荐的采样持续时间
pub fn recommended_duration(env: &str) -> std::time::Duration {
    match env {
        "production" | "prod" => Duration::from_secs(300),  // 5分钟
        "staging" => Duration::from_secs(120),               // 2分钟
        "development" | "dev" => Duration::from_secs(60),    // 1分钟
        "debug" => Duration::from_secs(30),                  // 30秒
        _ => Duration::from_secs(60),                        // 默认：1分钟
    }
}

/// 根据环境创建推荐的配置
pub fn create_recommended_config(env: &str) -> EbpfConfig {
    EbpfConfig::new()
        .with_sample_rate(recommended_sample_rate(env))
        .with_duration(recommended_duration(env))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_validate_config_valid() {
        let config = EbpfConfig::default();
        assert!(validate_config(&config).is_ok());
    }

    #[test]
    fn test_validate_config_invalid_sample_rate() {
        let mut config = EbpfConfig::default();
        config.sample_rate = 0;
        assert!(validate_config(&config).is_err());
    }

    #[test]
    fn test_validate_config_invalid_max_samples() {
        let mut config = EbpfConfig::default();
        config.max_samples = 0;
        assert!(validate_config(&config).is_err());
    }

    #[test]
    fn test_recommended_sample_rate() {
        assert_eq!(recommended_sample_rate("production"), 19);
        assert_eq!(recommended_sample_rate("staging"), 49);
        assert_eq!(recommended_sample_rate("development"), 99);
        assert_eq!(recommended_sample_rate("debug"), 199);
        assert_eq!(recommended_sample_rate("unknown"), 99);
    }

    #[test]
    fn test_recommended_duration() {
        use std::time::Duration;
        assert_eq!(recommended_duration("production"), Duration::from_secs(300));
        assert_eq!(recommended_duration("staging"), Duration::from_secs(120));
        assert_eq!(recommended_duration("development"), Duration::from_secs(60));
        assert_eq!(recommended_duration("debug"), Duration::from_secs(30));
    }

    #[test]
    fn test_create_recommended_config() {
        let config = create_recommended_config("production");
        assert_eq!(config.sample_rate, 19);
        assert_eq!(config.duration.as_secs(), 300);
    }
}
