//! # pprof Format Encoder
//!
//! This module provides functionality to encode profiling data in pprof format.
//! The pprof format is a compact binary format for representing profiles.
//!
//! Reference: https://github.com/google/pprof/tree/main/proto

use super::types::*;
use std::collections::HashMap;

/// PprofBuilder helps construct pprof profiles
pub struct PprofBuilder {
    profile: PprofProfile,
    string_table: HashMap<String, i64>,
    next_location_id: u64,
    next_function_id: u64,
    next_mapping_id: u64,
}

impl PprofBuilder {
    /// Create a new PprofBuilder
    pub fn new(profile_type: ProfileType) -> Self {
        let mut builder = Self {
            profile: PprofProfile::new(),
            string_table: HashMap::new(),
            next_location_id: 1,
            next_function_id: 1,
            next_mapping_id: 1,
        };
        
        // Add empty string at index 0
        builder.string_table.insert(String::new(), 0);
        
        // Set up sample type based on profile type
        let type_str = builder.intern_string(profile_type.name());
        let unit_str = builder.intern_string(profile_type.unit());
        
        builder.profile.sample_type.push(ValueType {
            type_: type_str,
            unit: unit_str,
        });
        
        builder
    }
    
    /// Intern a string in the string table and return its index
    pub fn intern_string(&mut self, s: &str) -> i64 {
        if let Some(&index) = self.string_table.get(s) {
            return index;
        }
        
        let index = self.profile.string_table.len() as i64;
        self.string_table.insert(s.to_string(), index);
        self.profile.string_table.push(s.to_string());
        index
    }
    
    /// Add a sample to the profile
    pub fn add_sample(&mut self, sample: Sample) {
        self.profile.sample.push(sample);
    }
    
    /// Create a sample from a stack trace
    pub fn create_sample_from_stack(
        &mut self,
        stack_frames: &[StackFrame],
        value: i64,
    ) -> Sample {
        let location_ids: Vec<u64> = stack_frames
            .iter()
            .map(|frame| self.get_or_create_location(frame))
            .collect();
        
        Sample {
            location_id: location_ids,
            value: vec![value],
            label: Vec::new(),
        }
    }
    
    /// Get or create a location for a stack frame
    fn get_or_create_location(&mut self, frame: &StackFrame) -> u64 {
        let location_id = self.next_location_id;
        self.next_location_id += 1;
        
        let function_id = self.get_or_create_function(frame);
        
        let location = Location {
            id: location_id,
            mapping_id: 0, // Could be mapped to actual memory mappings
            address: frame.address,
            line: vec![Line {
                function_id,
                line: frame.line_number as i64,
            }],
            is_folded: false,
        };
        
        self.profile.location.push(location);
        location_id
    }
    
    /// Get or create a function for a stack frame
    fn get_or_create_function(&mut self, frame: &StackFrame) -> u64 {
        let function_id = self.next_function_id;
        self.next_function_id += 1;
        
        let name_idx = self.intern_string(&frame.function_name);
        let filename_idx = self.intern_string(&frame.file_name);
        
        let function = Function {
            id: function_id,
            name: name_idx,
            system_name: name_idx, // Same as name for now
            filename: filename_idx,
            start_line: frame.line_number as i64,
        };
        
        self.profile.function.push(function);
        function_id
    }
    
    /// Add a mapping to the profile
    pub fn add_mapping(&mut self, mapping: Mapping) {
        self.profile.mapping.push(mapping);
    }
    
    /// Create a mapping for an executable
    pub fn create_mapping(
        &mut self,
        filename: &str,
        memory_start: u64,
        memory_limit: u64,
    ) -> Mapping {
        let id = self.next_mapping_id;
        self.next_mapping_id += 1;
        
        let filename_idx = self.intern_string(filename);
        
        Mapping {
            id,
            memory_start,
            memory_limit,
            file_offset: 0,
            filename: filename_idx,
            build_id: 0,
            has_functions: true,
            has_filenames: true,
            has_line_numbers: true,
            has_inline_frames: false,
        }
    }
    
    /// Set the duration of the profile
    pub fn set_duration(&mut self, duration_nanos: i64) {
        self.profile.duration_nanos = duration_nanos;
    }
    
    /// Set the period type and value
    pub fn set_period(&mut self, period_type: ValueType, period: i64) {
        self.profile.period_type = Some(period_type);
        self.profile.period = period;
    }
    
    /// Add a comment to the profile
    pub fn add_comment(&mut self, comment: &str) {
        let comment_idx = self.intern_string(comment);
        self.profile.comment.push(comment_idx);
    }
    
    /// Build the final profile
    pub fn build(self) -> PprofProfile {
        self.profile
    }
}

/// StackFrame represents a single frame in a stack trace
#[derive(Debug, Clone)]
pub struct StackFrame {
    /// Function name
    pub function_name: String,
    
    /// File name
    pub file_name: String,
    
    /// Line number
    pub line_number: u32,
    
    /// Memory address
    pub address: u64,
}

impl StackFrame {
    /// Create a new StackFrame
    pub fn new(
        function_name: impl Into<String>,
        file_name: impl Into<String>,
        line_number: u32,
        address: u64,
    ) -> Self {
        Self {
            function_name: function_name.into(),
            file_name: file_name.into(),
            line_number,
            address,
        }
    }
}

/// Encoder for pprof profiles
pub struct PprofEncoder;

impl PprofEncoder {
    /// Encode a pprof profile to JSON format (for debugging and compatibility)
    ///
    /// This is a simplified JSON encoding for development and debugging.
    /// For production use with pprof tools, you should implement protobuf encoding
    /// using the official pprof.proto definition from https://github.com/google/pprof
    pub fn encode_json(profile: &PprofProfile) -> Result<Vec<u8>, String> {
        serde_json::to_vec_pretty(profile)
            .map_err(|e| format!("Failed to encode profile to JSON: {}", e))
    }
    
    /// Decode a pprof profile from JSON format
    pub fn decode_json(data: &[u8]) -> Result<PprofProfile, String> {
        serde_json::from_slice(data)
            .map_err(|e| format!("Failed to decode profile from JSON: {}", e))
    }
    
    /// Encode a pprof profile to protobuf bytes (production format)
    /// 
    /// TODO: Implement actual protobuf encoding using prost
    /// 
    /// To implement this properly:
    /// 1. Add pprof.proto definition to proto/ directory
    /// 2. Use prost-build in build.rs to generate Rust code
    /// 3. Convert PprofProfile to generated protobuf types
    /// 4. Use prost::Message::encode() to serialize
    ///
    /// Example build.rs:
    /// ```rust,ignore
    /// fn main() {
    ///     prost_build::compile_protos(&["proto/pprof.proto"], &["proto/"]).unwrap();
    /// }
    /// ```
    pub fn encode_protobuf(_profile: &PprofProfile) -> Result<Vec<u8>, String> {
        Err("Protobuf encoding not yet implemented. Please implement using prost crate. \
             For now, use encode_json() for development/debugging purposes.".to_string())
    }
    
    /// Decode a pprof profile from protobuf bytes
    ///
    /// TODO: Implement actual protobuf decoding using prost
    pub fn decode_protobuf(_data: &[u8]) -> Result<PprofProfile, String> {
        Err("Protobuf decoding not yet implemented. Please implement using prost crate. \
             For now, use decode_json() for development/debugging purposes.".to_string())
    }
    
    /// Save profile to file (JSON format)
    pub fn save_json(profile: &PprofProfile, path: &std::path::Path) -> Result<(), String> {
        let data = Self::encode_json(profile)?;
        std::fs::write(path, data)
            .map_err(|e| format!("Failed to write profile to file: {}", e))
    }
    
    /// Load profile from file (JSON format)
    pub fn load_json(path: &std::path::Path) -> Result<PprofProfile, String> {
        let data = std::fs::read(path)
            .map_err(|e| format!("Failed to read profile from file: {}", e))?;
        Self::decode_json(&data)
    }
}

/// Helper to collect stack traces
pub struct StackTraceCollector;

impl StackTraceCollector {
    /// Collect current stack trace
    /// 
    /// Note: This uses backtrace crate functionality
    #[cfg(feature = "backtrace")]
    pub fn collect() -> Vec<StackFrame> {
        use backtrace::Backtrace;
        
        let bt = Backtrace::new();
        let mut frames = Vec::new();
        
        for frame in bt.frames() {
            for symbol in frame.symbols() {
                let function_name = symbol
                    .name()
                    .map(|n| n.to_string())
                    .unwrap_or_else(|| "<unknown>".to_string());
                
                let file_name = symbol
                    .filename()
                    .and_then(|p| p.to_str())
                    .unwrap_or("<unknown>")
                    .to_string();
                
                let line_number = symbol.lineno().unwrap_or(0);
                let address = frame.ip() as u64;
                
                frames.push(StackFrame::new(
                    function_name,
                    file_name,
                    line_number,
                    address,
                ));
            }
        }
        
        frames
    }
    
    /// Collect current stack trace (fallback without backtrace feature)
    #[cfg(not(feature = "backtrace"))]
    pub fn collect() -> Vec<StackFrame> {
        // Return a placeholder frame
        vec![StackFrame::new(
            "<backtrace disabled>",
            "<unknown>",
            0,
            0,
        )]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pprof_builder_creation() {
        let builder = PprofBuilder::new(ProfileType::Cpu);
        let profile = builder.build();
        
        assert_eq!(profile.sample_type.len(), 1);
        assert!(profile.string_table.len() >= 2); // At least empty string + "cpu"
    }

    #[test]
    fn test_string_interning() {
        let mut builder = PprofBuilder::new(ProfileType::Cpu);
        
        let idx1 = builder.intern_string("test");
        let idx2 = builder.intern_string("test");
        let idx3 = builder.intern_string("other");
        
        assert_eq!(idx1, idx2); // Same string returns same index
        assert_ne!(idx1, idx3); // Different strings return different indices
    }

    #[test]
    fn test_create_sample() {
        let mut builder = PprofBuilder::new(ProfileType::Cpu);
        
        let frames = vec![
            StackFrame::new("main", "main.rs", 10, 0x1000),
            StackFrame::new("foo", "lib.rs", 20, 0x2000),
        ];
        
        let sample = builder.create_sample_from_stack(&frames, 100);
        
        assert_eq!(sample.location_id.len(), 2);
        assert_eq!(sample.value, vec![100]);
        
        let profile = builder.build();
        assert_eq!(profile.location.len(), 2);
        assert_eq!(profile.function.len(), 2);
    }

    #[test]
    fn test_stack_frame_creation() {
        let frame = StackFrame::new("test_function", "test.rs", 42, 0x12345678);
        
        assert_eq!(frame.function_name, "test_function");
        assert_eq!(frame.file_name, "test.rs");
        assert_eq!(frame.line_number, 42);
        assert_eq!(frame.address, 0x12345678);
    }

    #[test]
    fn test_add_comment() {
        let mut builder = PprofBuilder::new(ProfileType::Cpu);
        builder.add_comment("Test profile");
        
        let profile = builder.build();
        assert_eq!(profile.comment.len(), 1);
    }

    #[test]
    fn test_set_duration() {
        let mut builder = PprofBuilder::new(ProfileType::Cpu);
        builder.set_duration(1_000_000_000); // 1 second in nanoseconds
        
        let profile = builder.build();
        assert_eq!(profile.duration_nanos, 1_000_000_000);
    }
    
    #[test]
    fn test_json_encode_decode() {
        let mut builder = PprofBuilder::new(ProfileType::Cpu);
        builder.add_comment("Test profile");
        builder.set_duration(1_000_000_000);
        
        let frames = vec![
            StackFrame::new("main", "main.rs", 10, 0x1000),
        ];
        let sample = builder.create_sample_from_stack(&frames, 100);
        builder.add_sample(sample);
        
        let profile = builder.build();
        
        // Encode to JSON
        let encoded = PprofEncoder::encode_json(&profile).expect("Failed to encode");
        assert!(!encoded.is_empty());
        
        // Decode from JSON
        let decoded = PprofEncoder::decode_json(&encoded).expect("Failed to decode");
        
        // Verify key fields
        assert_eq!(decoded.duration_nanos, profile.duration_nanos);
        assert_eq!(decoded.sample.len(), profile.sample.len());
        assert_eq!(decoded.comment.len(), profile.comment.len());
    }
    
    #[test]
    fn test_protobuf_not_implemented() {
        let builder = PprofBuilder::new(ProfileType::Cpu);
        let profile = builder.build();
        
        // Protobuf encoding should return error
        let result = PprofEncoder::encode_protobuf(&profile);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("not yet implemented"));
        
        // Protobuf decoding should return error
        let result = PprofEncoder::decode_protobuf(&[]);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("not yet implemented"));
    }
}

