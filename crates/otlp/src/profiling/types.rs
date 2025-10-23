//! # OpenTelemetry Profiling Data Types
//!
//! This module defines the data structures for OpenTelemetry Profiling.
//! Based on OpenTelemetry Profiling specification v0.1
//!
//! References:
//! - https://opentelemetry.io/docs/specs/otel/logs/data-model/
//! - https://github.com/open-telemetry/opentelemetry-proto/tree/main/opentelemetry/proto/profiles/v1experimental

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::SystemTime;

/// ProfileContainer represents the top-level data structure for a collection of profiles.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProfileContainer {
    /// Resource attributes shared across all profiles
    pub resource: Resource,
    
    /// Scope profiles (previously called InstrumentationLibraryProfiles)
    pub scope_profiles: Vec<ScopeProfiles>,
    
    /// Schema URL for the profile data
    pub schema_url: String,
}

/// Resource represents the entity producing telemetry
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Resource {
    /// Set of attributes describing the resource
    pub attributes: HashMap<String, AttributeValue>,
    
    /// Number of attributes dropped
    pub dropped_attributes_count: u32,
}

/// ScopeProfiles represents profiles from a single instrumentation scope
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ScopeProfiles {
    /// The instrumentation scope information
    pub scope: InstrumentationScope,
    
    /// List of profiles
    pub profiles: Vec<Profile>,
    
    /// Schema URL for this scope
    pub schema_url: String,
}

/// InstrumentationScope identifies the instrumentation library
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InstrumentationScope {
    /// Name of the instrumentation scope
    pub name: String,
    
    /// Version of the instrumentation scope
    pub version: String,
    
    /// Additional attributes
    pub attributes: HashMap<String, AttributeValue>,
    
    /// Number of dropped attributes
    pub dropped_attributes_count: u32,
}

/// Profile represents a single profile
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Profile {
    /// Unique identifier for the profile
    pub profile_id: Vec<u8>,
    
    /// Start time of the profile
    pub start_time_unix_nano: u64,
    
    /// End time of the profile  
    pub end_time_unix_nano: u64,
    
    /// Attributes specific to this profile
    pub attributes: HashMap<String, AttributeValue>,
    
    /// Number of dropped attributes
    pub dropped_attributes_count: u32,
    
    /// The actual profile data
    pub profile_data: ProfileData,
    
    /// Link to trace if available
    pub trace_id: Option<Vec<u8>>,
    
    /// Link to span if available
    pub span_id: Option<Vec<u8>>,
}

/// ProfileData contains the actual profiling data in various formats
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ProfileData {
    /// pprof format profile
    Pprof(PprofProfile),
    
    /// Custom format profile
    Custom(Vec<u8>),
}

/// PprofProfile represents profile data in pprof format
/// Based on https://github.com/google/pprof/tree/main/proto
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PprofProfile {
    /// Sample type descriptions
    pub sample_type: Vec<ValueType>,
    
    /// Samples
    pub sample: Vec<Sample>,
    
    /// Mappings (memory mappings)
    pub mapping: Vec<Mapping>,
    
    /// Locations (code locations)
    pub location: Vec<Location>,
    
    /// Functions
    pub function: Vec<Function>,
    
    /// String table (for deduplication)
    pub string_table: Vec<String>,
    
    /// Time when profile was collected
    pub time_nanos: i64,
    
    /// Duration of the profile
    pub duration_nanos: i64,
    
    /// Type of period
    pub period_type: Option<ValueType>,
    
    /// Period value
    pub period: i64,
    
    /// Comments
    pub comment: Vec<i64>,
    
    /// Default sample type
    pub default_sample_type: i64,
}

/// ValueType describes the type and unit of a value
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValueType {
    /// Type of the value (e.g., "cpu", "memory")
    pub type_: i64, // string table index
    
    /// Unit of the value (e.g., "nanoseconds", "bytes")
    pub unit: i64, // string table index
}

/// Sample represents a single profile sample
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Sample {
    /// Location IDs (stack trace)
    pub location_id: Vec<u64>,
    
    /// Values corresponding to sample_type
    pub value: Vec<i64>,
    
    /// Labels for this sample
    pub label: Vec<Label>,
}

/// Label represents a key-value label for a sample
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Label {
    /// Key (string table index)
    pub key: i64,
    
    /// String value (string table index, -1 if not present)
    pub str: i64,
    
    /// Numeric value (valid if str is -1)
    pub num: i64,
    
    /// Unit for numeric value (string table index)
    pub num_unit: i64,
}

/// Mapping represents a memory mapping
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Mapping {
    /// Unique identifier
    pub id: u64,
    
    /// Memory start address
    pub memory_start: u64,
    
    /// Memory limit address
    pub memory_limit: u64,
    
    /// File offset
    pub file_offset: u64,
    
    /// Filename (string table index)
    pub filename: i64,
    
    /// Build ID (string table index)
    pub build_id: i64,
    
    /// Has functions
    pub has_functions: bool,
    
    /// Has filenames
    pub has_filenames: bool,
    
    /// Has line numbers
    pub has_line_numbers: bool,
    
    /// Has inline frames
    pub has_inline_frames: bool,
}

/// Location represents a code location
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Location {
    /// Unique identifier
    pub id: u64,
    
    /// Mapping ID
    pub mapping_id: u64,
    
    /// Address
    pub address: u64,
    
    /// Line information
    pub line: Vec<Line>,
    
    /// Is folded
    pub is_folded: bool,
}

/// Line represents a line in source code
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Line {
    /// Function ID
    pub function_id: u64,
    
    /// Line number
    pub line: i64,
}

/// Function represents a function
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Function {
    /// Unique identifier
    pub id: u64,
    
    /// Function name (string table index)
    pub name: i64,
    
    /// System name (string table index)
    pub system_name: i64,
    
    /// Filename (string table index)
    pub filename: i64,
    
    /// Start line number
    pub start_line: i64,
}

/// AttributeValue represents a value of different types
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AttributeValue {
    String(String),
    Bool(bool),
    Int(i64),
    Double(f64),
    Bytes(Vec<u8>),
    Array(Vec<AttributeValue>),
    Map(HashMap<String, AttributeValue>),
}

/// ProfileType identifies the type of profile
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProfileType {
    /// CPU profiling
    Cpu,
    
    /// Heap memory profiling
    Heap,
    
    /// Lock contention profiling
    Mutex,
    
    /// Goroutine/thread profiling
    Goroutine,
    
    /// Wall clock time profiling
    Wall,
    
    /// Block profiling
    Block,
    
    /// Custom profile type
    Custom,
}

impl ProfileType {
    /// Get the standard name for this profile type
    pub fn name(&self) -> &'static str {
        match self {
            Self::Cpu => "cpu",
            Self::Heap => "heap",
            Self::Mutex => "mutex",
            Self::Goroutine => "goroutine",
            Self::Wall => "wall",
            Self::Block => "block",
            Self::Custom => "custom",
        }
    }
    
    /// Get the standard unit for this profile type
    pub fn unit(&self) -> &'static str {
        match self {
            Self::Cpu => "nanoseconds",
            Self::Heap => "bytes",
            Self::Mutex => "nanoseconds",
            Self::Goroutine => "count",
            Self::Wall => "nanoseconds",
            Self::Block => "nanoseconds",
            Self::Custom => "count",
        }
    }
}

impl Default for Resource {
    fn default() -> Self {
        Self {
            attributes: HashMap::new(),
            dropped_attributes_count: 0,
        }
    }
}

impl Default for InstrumentationScope {
    fn default() -> Self {
        Self {
            name: "otlp-rust-profiling".to_string(),
            version: env!("CARGO_PKG_VERSION").to_string(),
            attributes: HashMap::new(),
            dropped_attributes_count: 0,
        }
    }
}

impl Profile {
    /// Create a new Profile with current timestamp
    pub fn new(profile_id: Vec<u8>, profile_data: ProfileData) -> Self {
        let now = SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap()
            .as_nanos() as u64;
        
        Self {
            profile_id,
            start_time_unix_nano: now,
            end_time_unix_nano: now,
            attributes: HashMap::new(),
            dropped_attributes_count: 0,
            profile_data,
            trace_id: None,
            span_id: None,
        }
    }
    
    /// Link this profile to a trace span
    pub fn link_to_span(&mut self, trace_id: Vec<u8>, span_id: Vec<u8>) {
        self.trace_id = Some(trace_id);
        self.span_id = Some(span_id);
    }
    
    /// Add an attribute to the profile
    pub fn add_attribute(&mut self, key: String, value: AttributeValue) {
        self.attributes.insert(key, value);
    }
}

impl PprofProfile {
    /// Create a new empty pprof profile
    pub fn new() -> Self {
        let now = SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap()
            .as_nanos() as i64;
        
        Self {
            sample_type: Vec::new(),
            sample: Vec::new(),
            mapping: Vec::new(),
            location: Vec::new(),
            function: Vec::new(),
            string_table: vec![String::new()], // index 0 is always empty
            time_nanos: now,
            duration_nanos: 0,
            period_type: None,
            period: 0,
            comment: Vec::new(),
            default_sample_type: 0,
        }
    }
}

impl Default for PprofProfile {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_profile_creation() {
        let profile_data = ProfileData::Pprof(PprofProfile::new());
        let profile = Profile::new(vec![1, 2, 3, 4], profile_data);
        
        assert_eq!(profile.profile_id, vec![1, 2, 3, 4]);
        assert!(profile.trace_id.is_none());
        assert!(profile.span_id.is_none());
    }

    #[test]
    fn test_profile_link_to_span() {
        let profile_data = ProfileData::Pprof(PprofProfile::new());
        let mut profile = Profile::new(vec![1, 2, 3, 4], profile_data);
        
        profile.link_to_span(vec![5, 6, 7, 8], vec![9, 10, 11, 12]);
        
        assert_eq!(profile.trace_id, Some(vec![5, 6, 7, 8]));
        assert_eq!(profile.span_id, Some(vec![9, 10, 11, 12]));
    }

    #[test]
    fn test_profile_type_names() {
        assert_eq!(ProfileType::Cpu.name(), "cpu");
        assert_eq!(ProfileType::Heap.name(), "heap");
        assert_eq!(ProfileType::Cpu.unit(), "nanoseconds");
        assert_eq!(ProfileType::Heap.unit(), "bytes");
    }

    #[test]
    fn test_pprof_profile_creation() {
        let profile = PprofProfile::new();
        
        assert_eq!(profile.string_table.len(), 1);
        assert_eq!(profile.string_table[0], "");
        assert_eq!(profile.sample.len(), 0);
    }

    #[allow(dead_code)]
    #[allow(unused_variables)]
    #[test]
    fn test_attribute_value_variants() {
        let str_val = AttributeValue::String("test".to_string());
        let int_val = AttributeValue::Int(42);
        let bool_val = AttributeValue::Bool(true);
        let double_val = AttributeValue::Double(3.14);
        
        match str_val {
            AttributeValue::String(s) => assert_eq!(s, "test"),
            _ => panic!("Expected String variant"),
        }
        
        match int_val {
            AttributeValue::Int(i) => assert_eq!(i, 42),
            _ => panic!("Expected Int variant"),
        }
    }
}

