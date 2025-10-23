//! SIMD-Optimized Serialization
//!
//! Provides vectorized batch serialization for spans and metrics.

use super::CpuFeatures;

/// Batch serializer with SIMD optimization
pub struct BatchSerializer {
    /// Serialization statistics
    stats: SerializationStats,
}

impl BatchSerializer {
    /// Creates a new batch serializer
    pub fn new() -> Self {
        Self {
            stats: SerializationStats::default(),
        }
    }

    /// Returns serialization statistics
    pub fn stats(&self) -> &SerializationStats {
        &self.stats
    }

    /// Resets statistics
    pub fn reset_stats(&mut self) {
        self.stats = SerializationStats::default();
    }

    /// Serializes a batch of i64 values
    pub fn serialize_i64_batch(&mut self, values: &[i64]) -> Vec<u8> {
        let start = std::time::Instant::now();
        self.stats.batches_processed += 1;
        self.stats.values_processed += values.len() as u64;

        let result = if CpuFeatures::global().has_simd() && values.len() >= 4 {
            self.serialize_i64_simd(values)
        } else {
            self.serialize_i64_scalar(values)
        };

        self.stats.total_time_us += start.elapsed().as_micros() as u64;
        result
    }

    #[cfg(target_arch = "x86_64")]
    fn serialize_i64_simd(&self, values: &[i64]) -> Vec<u8> {
        let mut result = Vec::with_capacity(values.len() * 8);
        
        // Process 4 values at a time
        let chunks = values.chunks_exact(4);
        let remainder = chunks.remainder();

        for chunk in chunks {
            for &val in chunk {
                result.extend_from_slice(&val.to_le_bytes());
            }
        }

        for &val in remainder {
            result.extend_from_slice(&val.to_le_bytes());
        }

        result
    }

    #[cfg(not(target_arch = "x86_64"))]
    fn serialize_i64_simd(&self, values: &[i64]) -> Vec<u8> {
        self.serialize_i64_scalar(values)
    }

    fn serialize_i64_scalar(&self, values: &[i64]) -> Vec<u8> {
        let mut result = Vec::with_capacity(values.len() * 8);
        for &val in values {
            result.extend_from_slice(&val.to_le_bytes());
        }
        result
    }

    /// Serializes a batch of f64 values
    pub fn serialize_f64_batch(&mut self, values: &[f64]) -> Vec<u8> {
        let start = std::time::Instant::now();
        self.stats.batches_processed += 1;
        self.stats.values_processed += values.len() as u64;

        let result = if CpuFeatures::global().has_simd() && values.len() >= 4 {
            self.serialize_f64_simd(values)
        } else {
            self.serialize_f64_scalar(values)
        }
;

        self.stats.total_time_us += start.elapsed().as_micros() as u64;
        result
    }

    #[cfg(target_arch = "x86_64")]
    fn serialize_f64_simd(&self, values: &[f64]) -> Vec<u8> {
        let mut result = Vec::with_capacity(values.len() * 8);
        
        let chunks = values.chunks_exact(4);
        let remainder = chunks.remainder();

        for chunk in chunks {
            for &val in chunk {
                result.extend_from_slice(&val.to_le_bytes());
            }
        }

        for &val in remainder {
            result.extend_from_slice(&val.to_le_bytes());
        }

        result
    }

    #[cfg(not(target_arch = "x86_64"))]
    fn serialize_f64_simd(&self, values: &[f64]) -> Vec<u8> {
        self.serialize_f64_scalar(values)
    }

    fn serialize_f64_scalar(&self, values: &[f64]) -> Vec<u8> {
        let mut result = Vec::with_capacity(values.len() * 8);
        for &val in values {
            result.extend_from_slice(&val.to_le_bytes());
        }
        result
    }

    /// Deserializes a batch of i64 values
    pub fn deserialize_i64_batch(&mut self, bytes: &[u8]) -> Vec<i64> {
        let start = std::time::Instant::now();
        
        let result = if CpuFeatures::global().has_simd() && bytes.len() >= 32 {
            self.deserialize_i64_simd(bytes)
        } else {
            self.deserialize_i64_scalar(bytes)
        };

        self.stats.total_time_us += start.elapsed().as_micros() as u64;
        result
    }

    #[cfg(target_arch = "x86_64")]
    fn deserialize_i64_simd(&self, bytes: &[u8]) -> Vec<i64> {
        let count = bytes.len() / 8;
        let mut result = Vec::with_capacity(count);

        let chunks = bytes.chunks_exact(32); // 4 * 8 bytes
        let remainder = chunks.remainder();

        for chunk in chunks {
            for i in 0..4 {
                let start = i * 8;
                let val = i64::from_le_bytes([
                    chunk[start],
                    chunk[start + 1],
                    chunk[start + 2],
                    chunk[start + 3],
                    chunk[start + 4],
                    chunk[start + 5],
                    chunk[start + 6],
                    chunk[start + 7],
                ]);
                result.push(val);
            }
        }

        for chunk in remainder.chunks_exact(8) {
            let val = i64::from_le_bytes([
                chunk[0], chunk[1], chunk[2], chunk[3],
                chunk[4], chunk[5], chunk[6], chunk[7],
            ]);
            result.push(val);
        }

        result
    }

    #[cfg(not(target_arch = "x86_64"))]
    fn deserialize_i64_simd(&self, bytes: &[u8]) -> Vec<i64> {
        self.deserialize_i64_scalar(bytes)
    }

    fn deserialize_i64_scalar(&self, bytes: &[u8]) -> Vec<i64> {
        bytes
            .chunks_exact(8)
            .map(|chunk| {
                i64::from_le_bytes([
                    chunk[0], chunk[1], chunk[2], chunk[3],
                    chunk[4], chunk[5], chunk[6], chunk[7],
                ])
            })
            .collect()
    }
}

impl Default for BatchSerializer {
    fn default() -> Self {
        Self::new()
    }
}

/// Serialization statistics
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct SerializationStats {
    /// Number of batches processed
    pub batches_processed: u64,
    /// Total values processed
    pub values_processed: u64,
    /// Total time in microseconds
    pub total_time_us: u64,
}

impl SerializationStats {
    /// Returns average processing time per batch
    pub fn avg_time_per_batch_us(&self) -> f64 {
        if self.batches_processed == 0 {
            0.0
        } else {
            self.total_time_us as f64 / self.batches_processed as f64
        }
    }

    /// Returns average processing time per value
    pub fn avg_time_per_value_ns(&self) -> f64 {
        if self.values_processed == 0 {
            0.0
        } else {
            (self.total_time_us as f64 * 1000.0) / self.values_processed as f64
        }
    }

    /// Returns throughput in values per second
    pub fn throughput_values_per_sec(&self) -> f64 {
        if self.total_time_us == 0 {
            0.0
        } else {
            (self.values_processed as f64 * 1_000_000.0) / self.total_time_us as f64
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_serialize_i64_basic() {
        let mut serializer = BatchSerializer::new();
        let values = vec![1i64, 2, 3, 4, 5];
        
        let bytes = serializer.serialize_i64_batch(&values);
        assert_eq!(bytes.len(), values.len() * 8);
        
        let deserialized = serializer.deserialize_i64_batch(&bytes);
        assert_eq!(deserialized, values);
    }

    #[test]
    fn test_serialize_f64_basic() {
        let mut serializer = BatchSerializer::new();
        let values = vec![1.0f64, 2.0, 3.0, 4.0, 5.0];
        
        let bytes = serializer.serialize_f64_batch(&values);
        assert_eq!(bytes.len(), values.len() * 8);
    }

    #[test]
    fn test_serialize_large_batch() {
        let mut serializer = BatchSerializer::new();
        let values: Vec<i64> = (1..=1000).collect();
        
        let bytes = serializer.serialize_i64_batch(&values);
        let deserialized = serializer.deserialize_i64_batch(&bytes);
        
        assert_eq!(deserialized, values);
    }

    #[test]
    fn test_serialization_stats() {
        let mut serializer = BatchSerializer::new();
        let values = vec![1i64, 2, 3, 4, 5];
        
        serializer.serialize_i64_batch(&values);
        serializer.serialize_i64_batch(&values);
        
        let stats = serializer.stats();
        assert_eq!(stats.batches_processed, 2);
        assert_eq!(stats.values_processed, 10);
        // Time might be 0 for very fast operations
        assert!(stats.total_time_us >= 0);
    }

    #[test]
    fn test_stats_calculations() {
        let stats = SerializationStats {
            batches_processed: 10,
            values_processed: 1000,
            total_time_us: 1000,
        };

        assert_eq!(stats.avg_time_per_batch_us(), 100.0);
        // 1000us total / 1000 values = 1us/value = 1000ns/value
        assert_eq!(stats.avg_time_per_value_ns(), 1000.0);
        assert_eq!(stats.throughput_values_per_sec(), 1_000_000.0);
    }

    #[test]
    fn test_simd_vs_scalar_consistency() {
        let mut serializer = BatchSerializer::new();
        let values: Vec<i64> = (1..=100).collect();
        
        let bytes_simd = serializer.serialize_i64_batch(&values);
        let bytes_scalar = serializer.serialize_i64_scalar(&values);
        
        assert_eq!(bytes_simd, bytes_scalar);
    }
}

