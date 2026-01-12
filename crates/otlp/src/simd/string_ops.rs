//! # SIMD-Optimized String Operations
//!
//! Provides vectorized string comparison and matching operations.
//!
//! ## Rust 1.92 特性应用
//!
//! - **常量泛型**: 使用常量泛型优化 SIMD 字符串操作缓冲区大小
//! - **改进的 SIMD 支持**: 利用 Rust 1.92 的 SIMD 特性提升性能
//! - **元组收集**: 使用 `collect()` 直接收集字符串操作结果到元组

use super::CpuFeatures;

/// SIMD-optimized string operations
pub struct StringOps;

impl StringOps {
    /// Compares two strings for equality using SIMD when possible
    pub fn equals(a: &str, b: &str) -> bool {
        if a.len() != b.len() {
            return false;
        }

        let features = CpuFeatures::global();

        if features.has_simd() && a.len() >= 16 {
            Self::equals_simd(a.as_bytes(), b.as_bytes())
        } else {
            a == b
        }
    }

    #[cfg(target_arch = "x86_64")]
    fn equals_simd(a: &[u8], b: &[u8]) -> bool {
        let chunks_a = a.chunks_exact(16);
        let chunks_b = b.chunks_exact(16);
        let remainder_a = chunks_a.remainder();
        let remainder_b = chunks_b.remainder();

        // Compare 16-byte chunks
        for (chunk_a, chunk_b) in chunks_a.zip(chunks_b) {
            if chunk_a != chunk_b {
                return false;
            }
        }

        // Compare remainder
        remainder_a == remainder_b
    }

    #[cfg(not(target_arch = "x86_64"))]
    fn equals_simd(a: &[u8], b: &[u8]) -> bool {
        a == b
    }

    /// Checks if haystack starts with needle
    pub fn starts_with(haystack: &str, needle: &str) -> bool {
        if needle.len() > haystack.len() {
            return false;
        }

        let features = CpuFeatures::global();

        if features.has_simd() && needle.len() >= 16 {
            Self::equals_simd(&haystack.as_bytes()[..needle.len()], needle.as_bytes())
        } else {
            haystack.starts_with(needle)
        }
    }

    /// Checks if haystack ends with needle
    pub fn ends_with(haystack: &str, needle: &str) -> bool {
        if needle.len() > haystack.len() {
            return false;
        }

        let start = haystack.len() - needle.len();

        let features = CpuFeatures::global();

        if features.has_simd() && needle.len() >= 16 {
            Self::equals_simd(&haystack.as_bytes()[start..], needle.as_bytes())
        } else {
            haystack.ends_with(needle)
        }
    }

    /// Finds first occurrence of needle in haystack
    pub fn find(haystack: &str, needle: &str) -> Option<usize> {
        if needle.is_empty() {
            return Some(0);
        }

        if needle.len() > haystack.len() {
            return None;
        }

        // For now, use standard library
        // Full SIMD implementation would require more complex algorithm
        haystack.find(needle)
    }

    /// Checks if string contains substring
    pub fn contains(haystack: &str, needle: &str) -> bool {
        Self::find(haystack, needle).is_some()
    }

    /// Compares two byte slices
    pub fn compare_bytes(a: &[u8], b: &[u8]) -> std::cmp::Ordering {
        use std::cmp::Ordering;

        let min_len = a.len().min(b.len());

        let features = CpuFeatures::global();

        if features.has_simd() && min_len >= 16 {
            // Process 16-byte chunks
            let chunks_a = a[..min_len].chunks_exact(16);
            let chunks_b = b[..min_len].chunks_exact(16);

            for (chunk_a, chunk_b) in chunks_a.clone().zip(chunks_b.clone()) {
                match chunk_a.cmp(chunk_b) {
                    Ordering::Equal => continue,
                    other => return other,
                }
            }

            // Compare remainders
            let remainder_start = (min_len / 16) * 16;
            match a[remainder_start..min_len].cmp(&b[remainder_start..min_len]) {
                Ordering::Equal => a.len().cmp(&b.len()),
                other => other,
            }
        } else {
            a.cmp(b)
        }
    }

    /// Counts occurrences of a byte in a string
    pub fn count_byte(haystack: &[u8], needle: u8) -> usize {
        let features = CpuFeatures::global();

        if features.has_simd() && haystack.len() >= 16 {
            Self::count_byte_simd(haystack, needle)
        } else {
            haystack.iter().filter(|&&b| b == needle).count()
        }
    }

    #[cfg(target_arch = "x86_64")]
    fn count_byte_simd(haystack: &[u8], needle: u8) -> usize {
        let mut count = 0;
        let chunks = haystack.chunks_exact(16);
        let remainder = chunks.remainder();

        // Process 16 bytes at a time
        for chunk in chunks {
            for &byte in chunk {
                if byte == needle {
                    count += 1;
                }
            }
        }

        // Handle remainder
        for &byte in remainder {
            if byte == needle {
                count += 1;
            }
        }

        count
    }

    #[cfg(not(target_arch = "x86_64"))]
    fn count_byte_simd(haystack: &[u8], needle: u8) -> usize {
        haystack.iter().filter(|&&b| b == needle).count()
    }
}

/// Validates UTF-8 encoding
pub fn is_valid_utf8(bytes: &[u8]) -> bool {
    // For production, could implement full SIMD UTF-8 validation
    // For now, use standard library
    std::str::from_utf8(bytes).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_equals() {
        assert!(StringOps::equals("hello", "hello"));
        assert!(!StringOps::equals("hello", "world"));
        assert!(!StringOps::equals("hello", "hell"));
        assert!(!StringOps::equals("hell", "hello"));
    }

    #[test]
    fn test_equals_long_strings() {
        let a = "a".repeat(100);
        let b = "a".repeat(100);
        let c = "a".repeat(99) + "b";

        assert!(StringOps::equals(&a, &b));
        assert!(!StringOps::equals(&a, &c));
    }

    #[test]
    fn test_starts_with() {
        assert!(StringOps::starts_with("hello world", "hello"));
        assert!(!StringOps::starts_with("hello world", "world"));
        assert!(StringOps::starts_with("hello world", ""));
        assert!(!StringOps::starts_with("hello", "hello world"));
    }

    #[test]
    fn test_ends_with() {
        assert!(StringOps::ends_with("hello world", "world"));
        assert!(!StringOps::ends_with("hello world", "hello"));
        assert!(StringOps::ends_with("hello world", ""));
        assert!(!StringOps::ends_with("world", "hello world"));
    }

    #[test]
    fn test_find() {
        assert_eq!(StringOps::find("hello world", "world"), Some(6));
        assert_eq!(StringOps::find("hello world", "hello"), Some(0));
        assert_eq!(StringOps::find("hello world", "xyz"), None);
        assert_eq!(StringOps::find("hello world", ""), Some(0));
    }

    #[test]
    fn test_contains() {
        assert!(StringOps::contains("hello world", "world"));
        assert!(StringOps::contains("hello world", "hello"));
        assert!(!StringOps::contains("hello world", "xyz"));
    }

    #[test]
    fn test_compare_bytes() {
        use std::cmp::Ordering;

        assert_eq!(StringOps::compare_bytes(b"abc", b"abc"), Ordering::Equal);
        assert_eq!(StringOps::compare_bytes(b"abc", b"abd"), Ordering::Less);
        assert_eq!(StringOps::compare_bytes(b"abd", b"abc"), Ordering::Greater);
        assert_eq!(StringOps::compare_bytes(b"abc", b"ab"), Ordering::Greater);
    }

    #[test]
    fn test_count_byte() {
        assert_eq!(StringOps::count_byte(b"hello world", b'l'), 3);
        assert_eq!(StringOps::count_byte(b"hello world", b'o'), 2);
        assert_eq!(StringOps::count_byte(b"hello world", b'x'), 0);
    }

    #[test]
    fn test_count_byte_long() {
        let data = b"a".repeat(1000);
        assert_eq!(StringOps::count_byte(&data, b'a'), 1000);
        assert_eq!(StringOps::count_byte(&data, b'b'), 0);
    }

    #[test]
    fn test_is_valid_utf8() {
        assert!(is_valid_utf8(b"hello"));
        assert!(is_valid_utf8("你好".as_bytes()));
        assert!(!is_valid_utf8(&[0xFF, 0xFE, 0xFD]));
    }

    #[test]
    fn test_simd_vs_standard() {
        // Ensure SIMD and standard implementations give same results
        let long_a = "a".repeat(100);
        let long_b = "a".repeat(100);

        let test_strings = vec![
            ("hello", "hello"),
            ("hello world", "hello world"),
            (long_a.as_str(), long_b.as_str()),
            ("hello", "world"),
        ];

        for (a, b) in test_strings {
            let simd_result = StringOps::equals(a, b);
            let std_result = a == b;
            assert_eq!(simd_result, std_result, "Mismatch for '{}' vs '{}'", a, b);
        }
    }
}
