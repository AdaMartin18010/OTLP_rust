//! # 同态加密实现
//!
//! 使用 tfhe-rs 库实现全同态加密 (FHE) 功能。
//!
//! ## 功能特性
//!
//! - ✅ 整数同态加密 (8/16/32/64位)
//! - ✅ 同态加法
//! - ✅ 同态减法
//! - ✅ 同态乘法（有限次数）
//! - ✅ 同态标量运算
//!
//! ## 使用示例
//!
//! ```rust,no_run
//! use otlp::homomorphic::{HomomorphicEncryption, FheParams};
//!
//! #[tokio::main]
//! async fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     // 创建同态加密实例
//!     let mut fhe = HomomorphicEncryption::new(FheParams::default())?;
//!     
//!     // 生成密钥
//!     fhe.generate_keys().await?;
//!     
//!     // 加密数据
//!     let ct1 = fhe.encrypt(10u8).await?;
//!     let ct2 = fhe.encrypt(20u8).await?;
//!     
//!     // 同态加法
//!     let ct_sum = fhe.add(&ct1, &ct2).await?;
//!     
//!     // 解密结果
//!     let result: u8 = fhe.decrypt(&ct_sum).await?;
//!     assert_eq!(result, 30);
//!     
//!     Ok(())
//! }
//! ```

use anyhow::{Result, anyhow};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

/// 同态加密管理器
#[derive(Debug)]
pub struct HomomorphicEncryption {
    params: FheParams,
    #[cfg(feature = "homomorphic-encryption")]
    client_key: Option<tfhe::ClientKey>,
    #[cfg(feature = "homomorphic-encryption")]
    server_key: Option<tfhe::ServerKey>,
    #[cfg(feature = "homomorphic-encryption")]
    public_key: Option<tfhe::CompactPublicKey>,
    stats: Arc<FheStats>,
}

#[derive(Debug, Default)]
struct FheStats {
    encryptions: AtomicU64,
    decryptions: AtomicU64,
    homomorphic_ops: AtomicU64,
    failed_operations: AtomicU64,
}

/// 全同态加密参数
#[derive(Debug, Clone)]
pub struct FheParams {
    /// 使用的整数类型大小
    pub integer_size: FheIntegerSize,
    /// 是否使用紧凑公钥
    pub use_compact_public_key: bool,
}

impl Default for FheParams {
    fn default() -> Self {
        Self {
            integer_size: FheIntegerSize::U8,
            use_compact_public_key: false,
        }
    }
}

/// FHE 整数大小
#[derive(Debug, Clone, Copy)]
pub enum FheIntegerSize {
    U8,
    U16,
    U32,
    U64,
}

/// 密文
#[derive(Debug, Clone)]
pub struct Ciphertext {
    #[cfg(feature = "homomorphic-encryption")]
    inner: FheUint,
    #[cfg(not(feature = "homomorphic-encryption"))]
    #[allow(dead_code)]
    inner: Vec<u8>,
    pub timestamp: u64,
    pub size: FheIntegerSize,
}

#[cfg(feature = "homomorphic-encryption")]
#[derive(Debug, Clone)]
enum FheUint {
    U8(tfhe::FheUint8),
    U16(tfhe::FheUint16),
    U32(tfhe::FheUint32),
    U64(tfhe::FheUint64),
}

/// 明文 trait
pub trait FhePlaintext: Copy + Send + Sync {
    fn to_u64(self) -> u64;
    fn from_u64(val: u64) -> Self;
    fn size() -> FheIntegerSize;
}

impl FhePlaintext for u8 {
    fn to_u64(self) -> u64 { self as u64 }
    fn from_u64(val: u64) -> Self { val as u8 }
    fn size() -> FheIntegerSize { FheIntegerSize::U8 }
}

impl FhePlaintext for u16 {
    fn to_u64(self) -> u64 { self as u64 }
    fn from_u64(val: u64) -> Self { val as u16 }
    fn size() -> FheIntegerSize { FheIntegerSize::U16 }
}

impl FhePlaintext for u32 {
    fn to_u64(self) -> u64 { self as u64 }
    fn from_u64(val: u64) -> Self { val as u32 }
    fn size() -> FheIntegerSize { FheIntegerSize::U32 }
}

impl FhePlaintext for u64 {
    fn to_u64(self) -> u64 { self }
    fn from_u64(val: u64) -> Self { val }
    fn size() -> FheIntegerSize { FheIntegerSize::U64 }
}

impl HomomorphicEncryption {
    /// 创建新的同态加密实例
    pub fn new(params: FheParams) -> Result<Self> {
        #[cfg(feature = "homomorphic-encryption")]
        {
            Ok(Self {
                params,
                client_key: None,
                server_key: None,
                public_key: None,
                stats: Arc::new(FheStats::default()),
            })
        }
        
        #[cfg(not(feature = "homomorphic-encryption"))]
        {
            Ok(Self {
                params,
                stats: Arc::new(FheStats::default()),
            })
        }
    }
    
    /// 生成密钥对
    #[cfg(feature = "homomorphic-encryption")]
    pub async fn generate_keys(&mut self) -> Result<()> {
        use tfhe::{ConfigBuilder, generate_keys};
        
        let config = ConfigBuilder::all_disabled()
            .enable_default_uint8()
            .build();
        
        let (client_key, server_key) = generate_keys(config);
        
        self.client_key = Some(client_key);
        self.server_key = Some(server_key);
        
        // 设置全局服务器密钥用于 FHE 操作
        tfhe::set_server_key(self.server_key.as_ref().unwrap().clone());
        
        Ok(())
    }
    
    #[cfg(not(feature = "homomorphic-encryption"))]
    pub async fn generate_keys(&mut self) -> Result<()> {
        Err(anyhow!(
            "Homomorphic encryption is not available. \
            Enable the 'homomorphic-encryption' feature to use this functionality."
        ))
    }
    
    /// 加密整数
    #[cfg(feature = "homomorphic-encryption")]
    pub async fn encrypt<T: FhePlaintext>(&self, value: T) -> Result<Ciphertext> {
        let client_key = self.client_key.as_ref()
            .ok_or_else(|| anyhow!("Client key not generated. Call generate_keys() first."))?;
        
        let inner = match T::size() {
            FheIntegerSize::U8 => {
                let val = value.to_u64() as u8;
                FheUint::U8(tfhe::FheUint8::encrypt(val, client_key))
            }
            FheIntegerSize::U16 => {
                let val = value.to_u64() as u16;
                FheUint::U16(tfhe::FheUint16::encrypt(val, client_key))
            }
            FheIntegerSize::U32 => {
                let val = value.to_u64() as u32;
                FheUint::U32(tfhe::FheUint32::encrypt(val, client_key))
            }
            FheIntegerSize::U64 => {
                let val = value.to_u64();
                FheUint::U64(tfhe::FheUint64::encrypt(val, client_key))
            }
        };
        
        self.stats.encryptions.fetch_add(1, Ordering::Relaxed);
        
        Ok(Ciphertext {
            inner,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)?
                .as_secs(),
            size: T::size(),
        })
    }
    
    #[cfg(not(feature = "homomorphic-encryption"))]
    pub async fn encrypt<T: FhePlaintext>(&self, _value: T) -> Result<Ciphertext> {
        Err(anyhow!(
            "Homomorphic encryption is not available. \
            Enable the 'homomorphic-encryption' feature to use this functionality."
        ))
    }
    
    /// 解密密文
    #[cfg(feature = "homomorphic-encryption")]
    pub async fn decrypt<T: FhePlaintext>(&self, ciphertext: &Ciphertext) -> Result<T> {
        let client_key = self.client_key.as_ref()
            .ok_or_else(|| anyhow!("Client key not generated"))?;
        
        // 检查类型匹配
        if std::mem::discriminant(&ciphertext.size) != std::mem::discriminant(&T::size()) {
            return Err(anyhow!("Ciphertext size does not match requested type"));
        }
        
        let value = match &ciphertext.inner {
            FheUint::U8(ct) => ct.decrypt(client_key) as u64,
            FheUint::U16(ct) => ct.decrypt(client_key) as u64,
            FheUint::U32(ct) => ct.decrypt(client_key) as u64,
            FheUint::U64(ct) => ct.decrypt(client_key),
        };
        
        self.stats.decryptions.fetch_add(1, Ordering::Relaxed);
        
        Ok(T::from_u64(value))
    }
    
    #[cfg(not(feature = "homomorphic-encryption"))]
    pub async fn decrypt<T: FhePlaintext>(&self, _ciphertext: &Ciphertext) -> Result<T> {
        Err(anyhow!(
            "Homomorphic encryption is not available. \
            Enable the 'homomorphic-encryption' feature to use this functionality."
        ))
    }
    
    /// 同态加法
    #[cfg(feature = "homomorphic-encryption")]
    pub async fn add(&self, a: &Ciphertext, b: &Ciphertext) -> Result<Ciphertext> {
        // 确保服务器密钥已设置
        if self.server_key.is_none() {
            return Err(anyhow!("Server key not generated"));
        }
        
        // 检查类型匹配
        if std::mem::discriminant(&a.size) != std::mem::discriminant(&b.size) {
            return Err(anyhow!("Ciphertext sizes do not match"));
        }
        
        let inner = match (&a.inner, &b.inner) {
            (FheUint::U8(a), FheUint::U8(b)) => FheUint::U8(a + b),
            (FheUint::U16(a), FheUint::U16(b)) => FheUint::U16(a + b),
            (FheUint::U32(a), FheUint::U32(b)) => FheUint::U32(a + b),
            (FheUint::U64(a), FheUint::U64(b)) => FheUint::U64(a + b),
            _ => return Err(anyhow!("Ciphertext type mismatch")),
        };
        
        self.stats.homomorphic_ops.fetch_add(1, Ordering::Relaxed);
        
        Ok(Ciphertext {
            inner,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)?
                .as_secs(),
            size: a.size,
        })
    }
    
    #[cfg(not(feature = "homomorphic-encryption"))]
    pub async fn add(&self, _a: &Ciphertext, _b: &Ciphertext) -> Result<Ciphertext> {
        Err(anyhow!(
            "Homomorphic encryption is not available. \
            Enable the 'homomorphic-encryption' feature to use this functionality."
        ))
    }
    
    /// 同态减法
    #[cfg(feature = "homomorphic-encryption")]
    pub async fn sub(&self, a: &Ciphertext, b: &Ciphertext) -> Result<Ciphertext> {
        if self.server_key.is_none() {
            return Err(anyhow!("Server key not generated"));
        }
        
        if std::mem::discriminant(&a.size) != std::mem::discriminant(&b.size) {
            return Err(anyhow!("Ciphertext sizes do not match"));
        }
        
        let inner = match (&a.inner, &b.inner) {
            (FheUint::U8(a), FheUint::U8(b)) => FheUint::U8(a - b),
            (FheUint::U16(a), FheUint::U16(b)) => FheUint::U16(a - b),
            (FheUint::U32(a), FheUint::U32(b)) => FheUint::U32(a - b),
            (FheUint::U64(a), FheUint::U64(b)) => FheUint::U64(a - b),
            _ => return Err(anyhow!("Ciphertext type mismatch")),
        };
        
        self.stats.homomorphic_ops.fetch_add(1, Ordering::Relaxed);
        
        Ok(Ciphertext {
            inner,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)?
                .as_secs(),
            size: a.size,
        })
    }
    
    #[cfg(not(feature = "homomorphic-encryption"))]
    pub async fn sub(&self, _a: &Ciphertext, _b: &Ciphertext) -> Result<Ciphertext> {
        Err(anyhow!(
            "Homomorphic encryption is not available. \
            Enable the 'homomorphic-encryption' feature to use this functionality."
        ))
    }
    
    /// 同态乘法
    #[cfg(feature = "homomorphic-encryption")]
    pub async fn mul(&self, a: &Ciphertext, b: &Ciphertext) -> Result<Ciphertext> {
        if self.server_key.is_none() {
            return Err(anyhow!("Server key not generated"));
        }
        
        if std::mem::discriminant(&a.size) != std::mem::discriminant(&b.size) {
            return Err(anyhow!("Ciphertext sizes do not match"));
        }
        
        let inner = match (&a.inner, &b.inner) {
            (FheUint::U8(a), FheUint::U8(b)) => FheUint::U8(a * b),
            (FheUint::U16(a), FheUint::U16(b)) => FheUint::U16(a * b),
            (FheUint::U32(a), FheUint::U32(b)) => FheUint::U32(a * b),
            (FheUint::U64(a), FheUint::U64(b)) => FheUint::U64(a * b),
            _ => return Err(anyhow!("Ciphertext type mismatch")),
        };
        
        self.stats.homomorphic_ops.fetch_add(1, Ordering::Relaxed);
        
        Ok(Ciphertext {
            inner,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)?
                .as_secs(),
            size: a.size,
        })
    }
    
    #[cfg(not(feature = "homomorphic-encryption"))]
    pub async fn mul(&self, _a: &Ciphertext, _b: &Ciphertext) -> Result<Ciphertext> {
        Err(anyhow!(
            "Homomorphic encryption is not available. \
            Enable the 'homomorphic-encryption' feature to use this functionality."
        ))
    }
    
    /// 同态标量加法
    #[cfg(feature = "homomorphic-encryption")]
    pub async fn scalar_add<T: FhePlaintext>(&self, a: &Ciphertext, scalar: T) -> Result<Ciphertext> {
        if self.server_key.is_none() {
            return Err(anyhow!("Server key not generated"));
        }
        
        let inner = match (&a.inner, T::size()) {
            (FheUint::U8(a), FheIntegerSize::U8) => {
                FheUint::U8(a + (scalar.to_u64() as u8))
            }
            (FheUint::U16(a), FheIntegerSize::U16) => {
                FheUint::U16(a + (scalar.to_u64() as u16))
            }
            (FheUint::U32(a), FheIntegerSize::U32) => {
                FheUint::U32(a + (scalar.to_u64() as u32))
            }
            (FheUint::U64(a), FheIntegerSize::U64) => {
                FheUint::U64(a + scalar.to_u64())
            }
            _ => return Err(anyhow!("Ciphertext and scalar type mismatch")),
        };
        
        self.stats.homomorphic_ops.fetch_add(1, Ordering::Relaxed);
        
        Ok(Ciphertext {
            inner,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)?
                .as_secs(),
            size: a.size,
        })
    }
    
    #[cfg(not(feature = "homomorphic-encryption"))]
    pub async fn scalar_add<T: FhePlaintext>(&self, _a: &Ciphertext, _scalar: T) -> Result<Ciphertext> {
        Err(anyhow!(
            "Homomorphic encryption is not available. \
            Enable the 'homomorphic-encryption' feature to use this functionality."
        ))
    }
    
    /// 获取统计信息
    pub fn get_stats(&self) -> FheStatsSnapshot {
        FheStatsSnapshot {
            encryptions: self.stats.encryptions.load(Ordering::Relaxed),
            decryptions: self.stats.decryptions.load(Ordering::Relaxed),
            homomorphic_ops: self.stats.homomorphic_ops.load(Ordering::Relaxed),
            failed_operations: self.stats.failed_operations.load(Ordering::Relaxed),
        }
    }
    
    /// 获取参数
    pub fn params(&self) -> &FheParams {
        &self.params
    }
}

/// FHE 统计信息
#[derive(Debug, Clone)]
pub struct FheStatsSnapshot {
    pub encryptions: u64,
    pub decryptions: u64,
    pub homomorphic_ops: u64,
    pub failed_operations: u64,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    #[cfg(feature = "homomorphic-encryption")]
    async fn test_fhe_addition() {
        let mut fhe = HomomorphicEncryption::new(FheParams::default())
            .expect("Failed to create FHE");
        
        fhe.generate_keys().await.expect("Failed to generate keys");
        
        // Encrypt two values
        let ct1 = fhe.encrypt(10u8).await.expect("Failed to encrypt");
        let ct2 = fhe.encrypt(20u8).await.expect("Failed to encrypt");
        
        // Homomorphic addition
        let ct_sum = fhe.add(&ct1, &ct2).await.expect("Failed to add");
        
        // Decrypt result
        let result: u8 = fhe.decrypt(&ct_sum).await.expect("Failed to decrypt");
        
        assert_eq!(result, 30);
        
        // Check stats
        let stats = fhe.get_stats();
        assert_eq!(stats.encryptions, 2);
        assert_eq!(stats.decryptions, 1);
        assert_eq!(stats.homomorphic_ops, 1);
    }

    #[tokio::test]
    #[cfg(feature = "homomorphic-encryption")]
    async fn test_fhe_scalar_add() {
        let mut fhe = HomomorphicEncryption::new(FheParams::default())
            .expect("Failed to create FHE");
        
        fhe.generate_keys().await.expect("Failed to generate keys");
        
        // Encrypt a value
        let ct = fhe.encrypt(15u8).await.expect("Failed to encrypt");
        
        // Homomorphic scalar addition
        let ct_result = fhe.scalar_add(&ct, 5u8).await.expect("Failed to scalar add");
        
        // Decrypt result
        let result: u8 = fhe.decrypt(&ct_result).await.expect("Failed to decrypt");
        
        assert_eq!(result, 20);
    }

    #[tokio::test]
    #[cfg(feature = "homomorphic-encryption")]
    async fn test_fhe_multiplication() {
        let mut fhe = HomomorphicEncryption::new(FheParams::default())
            .expect("Failed to create FHE");
        
        fhe.generate_keys().await.expect("Failed to generate keys");
        
        // Encrypt two values
        let ct1 = fhe.encrypt(6u8).await.expect("Failed to encrypt");
        let ct2 = fhe.encrypt(7u8).await.expect("Failed to encrypt");
        
        // Homomorphic multiplication
        let ct_product = fhe.mul(&ct1, &ct2).await.expect("Failed to multiply");
        
        // Decrypt result
        let result: u8 = fhe.decrypt(&ct_product).await.expect("Failed to decrypt");
        
        assert_eq!(result, 42);
    }

    #[tokio::test]
    #[cfg(not(feature = "homomorphic-encryption"))]
    async fn test_fhe_unavailable_without_feature() {
        let mut fhe = HomomorphicEncryption::new(FheParams::default())
            .expect("Failed to create FHE");
        
        let result = fhe.generate_keys().await;
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("not available"));
    }
}
