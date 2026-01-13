//! 压缩模块单元测试

use otlp::performance::{QuickOptimizationsManager, CompressionConfig, CompressionAlgorithm};

#[test]
fn test_compression_config_default() {
    let config = CompressionConfig::default();
    
    assert_eq!(config.algorithm, CompressionAlgorithm::Gzip);
    assert_eq!(config.level, 6);
}

#[test]
fn test_compress_gzip() {
    let manager = QuickOptimizationsManager::default();
    let data = b"test data for compression";
    
    let result = manager.compress(data, CompressionAlgorithm::Gzip);
    assert!(result.is_ok());
    
    let compressed = result.unwrap();
    assert!(!compressed.is_empty());
    assert!(compressed.len() < data.len()); // 压缩后应该更小（对于重复数据）
}

#[test]
fn test_compress_brotli() {
    let manager = QuickOptimizationsManager::default();
    let data = b"test data for compression";
    
    let result = manager.compress(data, CompressionAlgorithm::Brotli);
    assert!(result.is_ok());
    
    let compressed = result.unwrap();
    assert!(!compressed.is_empty());
}

#[test]
fn test_compress_zstd() {
    let manager = QuickOptimizationsManager::default();
    let data = b"test data for compression";
    
    let result = manager.compress(data, CompressionAlgorithm::Zstd);
    assert!(result.is_ok());
    
    let compressed = result.unwrap();
    assert!(!compressed.is_empty());
}

#[test]
fn test_decompress_gzip() {
    let manager = QuickOptimizationsManager::default();
    let data = b"test data for compression";
    
    // 压缩
    let compressed = manager.compress(data, CompressionAlgorithm::Gzip).unwrap();
    
    // 解压
    let result = manager.decompress(&compressed, CompressionAlgorithm::Gzip);
    assert!(result.is_ok());
    
    let decompressed = result.unwrap();
    assert_eq!(decompressed, data);
}

#[test]
fn test_compression_ratio() {
    let manager = QuickOptimizationsManager::default();
    let data = b"test data for compression test data for compression";
    
    let compressed = manager.compress(data, CompressionAlgorithm::Gzip).unwrap();
    
    let ratio = compressed.len() as f64 / data.len() as f64;
    assert!(ratio <= 1.0); // 压缩率应该 <= 1.0
}
