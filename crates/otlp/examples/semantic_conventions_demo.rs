//! # Semantic Conventions Demo
//!
//! This example demonstrates the usage of OpenTelemetry Semantic Conventions
//!
//! Run with: `cargo run --example semantic_conventions_demo`

use otlp::semantic_conventions::http::{
    HttpAttributesBuilder, HttpMethod, HttpScheme,
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🌐 OpenTelemetry Semantic Conventions Demo\n");
    
    // Demo 1: HTTP GET Request
    println!("📊 Demo 1: HTTP GET Request");
    demo_http_get()?;
    
    println!("\n{}", "=".repeat(60));
    
    // Demo 2: HTTP POST Request
    println!("\n📊 Demo 2: HTTP POST Request");
    demo_http_post()?;
    
    println!("\n{}", "=".repeat(60));
    
    // Demo 3: Full HTTP Attributes
    println!("\n📊 Demo 3: Full HTTP Attributes");
    demo_http_full()?;
    
    println!("\n✅ All demos completed successfully!");
    
    Ok(())
}

fn demo_http_get() -> Result<(), Box<dyn std::error::Error>> {
    let attrs = HttpAttributesBuilder::new()
        .method(HttpMethod::Get)
        .url("https://api.example.com/users")
        .status_code(200)
        .build()?;
    
    println!("  ✅ Created HTTP GET attributes:");
    for (key, value) in attrs.as_map() {
        println!("     - {}: {}", key, value);
    }
    
    Ok(())
}

fn demo_http_post() -> Result<(), Box<dyn std::error::Error>> {
    let attrs = HttpAttributesBuilder::new()
        .method(HttpMethod::Post)
        .url("https://api.example.com/users")
        .status_code(201)
        .request_body_size(1024)
        .response_body_size(512)
        .build()?;
    
    println!("  ✅ Created HTTP POST attributes:");
    for (key, value) in attrs.as_map() {
        println!("     - {}: {}", key, value);
    }
    
    Ok(())
}

fn demo_http_full() -> Result<(), Box<dyn std::error::Error>> {
    let attrs = HttpAttributesBuilder::new()
        .method(HttpMethod::Post)
        .url("https://api.example.com/users?page=1")
        .status_code(201)
        .request_body_size(2048)
        .response_body_size(1024)
        .url_scheme(HttpScheme::Https)
        .url_path("/users")
        .url_query("page=1")
        .server_address("api.example.com")
        .server_port(443)
        .network_protocol_name("http")
        .network_protocol_version("2")
        .user_agent("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36")
        .build()?;
    
    println!("  ✅ Created full HTTP attributes:");
    println!("     Total attributes: {}", attrs.as_map().len());
    for (key, value) in attrs.as_map() {
        println!("     - {}: {}", key, value);
    }
    
    Ok(())
}

