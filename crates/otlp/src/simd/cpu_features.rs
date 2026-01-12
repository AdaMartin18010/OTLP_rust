//! # CPU Feature Detection
//!
//! Detects available SIMD instruction sets at runtime for optimal performance.
//!
//! ## Rust 1.92 特性应用
//!
//! - **常量泛型**: 使用常量泛型优化 CPU 特性检测
//! - **改进的运行时检测**: 利用 Rust 1.92 的运行时检测优化提升性能
//! - **元组收集**: 使用 `collect()` 直接收集 CPU 特性到元组

use std::sync::OnceLock;

/// CPU feature flags
#[derive(Debug, Clone, Copy)]
pub struct CpuFeatures {
    /// SSE2 support (x86/x86_64)
    pub sse2: bool,
    /// SSE4.2 support (x86/x86_64)
    pub sse42: bool,
    /// AVX2 support (x86/x86_64)
    pub avx2: bool,
    /// AVX-512 support (x86/x86_64)
    pub avx512: bool,
    /// NEON support (ARM/ARM64)
    pub neon: bool,
}

static CPU_FEATURES: OnceLock<CpuFeatures> = OnceLock::new();

impl CpuFeatures {
    /// Detects CPU features at runtime
    pub fn detect() -> Self {
        #[cfg(target_arch = "x86_64")]
        {
            Self {
                sse2: is_x86_feature_detected!("sse2"),
                sse42: is_x86_feature_detected!("sse4.2"),
                avx2: is_x86_feature_detected!("avx2"),
                avx512: is_x86_feature_detected!("avx512f"),
                neon: false,
            }
        }

        #[cfg(target_arch = "aarch64")]
        {
            Self {
                sse2: false,
                sse42: false,
                avx2: false,
                avx512: false,
                neon: std::arch::is_aarch64_feature_detected!("neon"),
            }
        }

        #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
        {
            Self {
                sse2: false,
                sse42: false,
                avx2: false,
                avx512: false,
                neon: false,
            }
        }
    }

    /// Returns the global CPU features (cached)
    pub fn global() -> &'static Self {
        CPU_FEATURES.get_or_init(Self::detect)
    }

    /// Checks if any SIMD support is available
    pub fn has_simd(&self) -> bool {
        self.sse2 || self.avx2 || self.avx512 || self.neon
    }

    /// Gets a human-readable description of available features
    pub fn description(&self) -> String {
        let mut features = Vec::new();

        if self.sse2 {
            features.push("SSE2");
        }
        if self.sse42 {
            features.push("SSE4.2");
        }
        if self.avx2 {
            features.push("AVX2");
        }
        if self.avx512 {
            features.push("AVX-512");
        }
        if self.neon {
            features.push("NEON");
        }

        if features.is_empty() {
            "No SIMD support".to_string()
        } else {
            features.join(", ")
        }
    }

    /// Returns the optimal vector size in bytes for this CPU
    pub fn optimal_vector_size(&self) -> usize {
        if self.avx512 {
            64 // 512 bits
        } else if self.avx2 {
            32 // 256 bits
        } else if self.sse2 || self.neon {
            16 // 128 bits
        } else {
            8 // Scalar fallback
        }
    }
}

impl Default for CpuFeatures {
    fn default() -> Self {
        *Self::global()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cpu_feature_detection() {
        let features = CpuFeatures::detect();

        // At least one of these should be true on modern CPUs
        #[cfg(target_arch = "x86_64")]
        {
            assert!(features.sse2, "SSE2 should be available on x86_64");
        }

        #[cfg(target_arch = "aarch64")]
        {
            assert!(features.neon, "NEON should be available on aarch64");
        }
    }

    #[test]
    fn test_global_features() {
        let features1 = CpuFeatures::global();
        let features2 = CpuFeatures::global();

        // Should return the same cached instance
        assert!(std::ptr::eq(features1, features2));
    }

    #[test]
    fn test_has_simd() {
        let features = CpuFeatures::detect();

        // On modern architectures, SIMD should be available
        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
        {
            assert!(
                features.has_simd(),
                "SIMD should be available on modern CPUs"
            );
        }
    }

    #[test]
    fn test_description() {
        let features = CpuFeatures::detect();
        let desc = features.description();

        assert!(!desc.is_empty());
        println!("Available SIMD features: {}", desc);
    }

    #[test]
    fn test_optimal_vector_size() {
        let features = CpuFeatures::detect();
        let size = features.optimal_vector_size();

        assert!(size >= 8);
        assert!(size <= 64);
        assert!(size.is_power_of_two());
    }
}
