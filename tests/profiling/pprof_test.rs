//! pprof 编码/解码单元测试

use otlp::profiling::types::{PprofProfile, Sample, Location, Function};

#[test]
fn test_pprof_profile_new() {
    let profile = PprofProfile::new();
    
    assert!(profile.samples.is_empty());
    assert!(profile.locations.is_empty());
    assert!(profile.functions.is_empty());
}

#[test]
fn test_pprof_profile_add_sample() {
    let mut profile = PprofProfile::new();
    
    let sample = Sample {
        location_ids: vec![1, 2],
        values: vec![100, 200],
        labels: vec![],
    };
    
    profile.add_sample(sample.clone());
    assert_eq!(profile.samples.len(), 1);
    assert_eq!(profile.samples[0].location_ids, sample.location_ids);
}

#[test]
fn test_pprof_profile_encode_json() {
    let mut profile = PprofProfile::new();
    
    // 添加示例数据
    let sample = Sample {
        location_ids: vec![1],
        values: vec![100],
        labels: vec![],
    };
    profile.add_sample(sample);
    
    // 编码为JSON
    let result = profile.encode_json();
    assert!(result.is_ok());
    
    let json = result.unwrap();
    assert!(!json.is_empty());
    assert!(json.contains("samples"));
}

#[test]
fn test_pprof_profile_decode_json() {
    let json = r#"{
        "samples": [{
            "locationIds": [1],
            "values": [100],
            "labels": []
        }],
        "locations": [],
        "functions": []
    }"#;
    
    let result = PprofProfile::decode_json(json);
    assert!(result.is_ok());
    
    let profile = result.unwrap();
    assert_eq!(profile.samples.len(), 1);
}

#[test]
fn test_pprof_profile_add_location() {
    let mut profile = PprofProfile::new();
    
    let location = Location {
        id: 1,
        address: 0x1000,
        line: vec![],
        is_folded: false,
    };
    
    profile.add_location(location.clone());
    assert_eq!(profile.locations.len(), 1);
    assert_eq!(profile.locations[0].id, location.id);
}

#[test]
fn test_pprof_profile_add_function() {
    let mut profile = PprofProfile::new();
    
    let function = Function {
        id: 1,
        name: "test_function".to_string(),
        system_name: "test_function".to_string(),
        filename: "test.rs".to_string(),
        start_line: 10,
    };
    
    profile.add_function(function.clone());
    assert_eq!(profile.functions.len(), 1);
    assert_eq!(profile.functions[0].id, function.id);
}
