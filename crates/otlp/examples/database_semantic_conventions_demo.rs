//! Database Semantic Conventions Demo
//!
//! This example demonstrates the usage of database semantic conventions
//! for various database systems (PostgreSQL, MySQL, MongoDB, Redis, etc.).

use otlp::semantic_conventions::database::{
    DatabaseAttributesBuilder, DatabaseOperation, DatabaseSystem,
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🗄️  OpenTelemetry Database Semantic Conventions Demo\n");
    println!("============================================================\n");

    // Demo 1: PostgreSQL SELECT Query
    println!("📊 Demo 1: PostgreSQL SELECT Query");
    let pg_attrs = DatabaseAttributesBuilder::new()
        .system(DatabaseSystem::Postgresql)
        .name("users_db")
        .statement("SELECT * FROM users WHERE id = $1")
        .operation(DatabaseOperation::Select)
        .user("app_user")
        .sql_table("users")
        .server_address("postgres.example.com")
        .server_port(5432)
        .network_protocol_name("tcp")
        .build()?;

    println!("  ✅ Created PostgreSQL attributes:");
    for (key, value) in pg_attrs.to_attributes() {
        println!("     - {}: {}", key, value);
    }
    println!("\n============================================================\n");

    // Demo 2: MySQL INSERT Operation
    println!("📊 Demo 2: MySQL INSERT Operation");
    let mysql_attrs = DatabaseAttributesBuilder::new()
        .system(DatabaseSystem::Mysql)
        .name("ecommerce")
        .statement("INSERT INTO orders (user_id, total) VALUES (?, ?)")
        .operation(DatabaseOperation::Insert)
        .user("api_user")
        .sql_table("orders")
        .server_address("mysql.example.com")
        .server_port(3306)
        .build()?;

    println!("  ✅ Created MySQL attributes:");
    for (key, value) in mysql_attrs.to_attributes() {
        println!("     - {}: {}", key, value);
    }
    println!("\n============================================================\n");

    // Demo 3: MongoDB Query
    println!("📊 Demo 3: MongoDB Query");
    let mongo_attrs = DatabaseAttributesBuilder::new()
        .system(DatabaseSystem::Mongodb)
        .name("production")
        .mongodb_collection("users")
        .operation(DatabaseOperation::Find)
        .statement(r#"{"_id": "123"}"#)
        .server_address("mongodb.example.com")
        .server_port(27017)
        .build()?;

    println!("  ✅ Created MongoDB attributes:");
    for (key, value) in mongo_attrs.to_attributes() {
        println!("     - {}: {}", key, value);
    }
    println!("\n============================================================\n");

    // Demo 4: Redis GET Command
    println!("📊 Demo 4: Redis GET Command");
    let redis_attrs = DatabaseAttributesBuilder::new()
        .system(DatabaseSystem::Redis)
        .name("cache")
        .redis_database_index(0)
        .operation(DatabaseOperation::Get)
        .statement("GET user:123")
        .server_address("redis.example.com")
        .server_port(6379)
        .build()?;

    println!("  ✅ Created Redis attributes:");
    for (key, value) in redis_attrs.to_attributes() {
        println!("     - {}: {}", key, value);
    }
    println!("\n============================================================\n");

    // Demo 5: Redis HSET Command
    println!("📊 Demo 5: Redis HSET Command");
    let redis_hset_attrs = DatabaseAttributesBuilder::new()
        .system(DatabaseSystem::Redis)
        .name("sessions")
        .redis_database_index(1)
        .operation(DatabaseOperation::Hset)
        .statement("HSET session:abc123 user_id 456")
        .server_address("redis.example.com")
        .server_port(6379)
        .build()?;

    println!("  ✅ Created Redis HSET attributes:");
    for (key, value) in redis_hset_attrs.to_attributes() {
        println!("     - {}: {}", key, value);
    }
    println!("\n============================================================\n");

    // Demo 6: Cassandra Query
    println!("📊 Demo 6: Cassandra Query");
    let cassandra_attrs = DatabaseAttributesBuilder::new()
        .system(DatabaseSystem::Cassandra)
        .name("analytics")
        .cassandra_keyspace("events")
        .operation(DatabaseOperation::Select)
        .statement("SELECT * FROM events WHERE user_id = ?")
        .server_address("cassandra.example.com")
        .server_port(9042)
        .build()?;

    println!("  ✅ Created Cassandra attributes:");
    for (key, value) in cassandra_attrs.to_attributes() {
        println!("     - {}: {}", key, value);
    }
    println!("\n============================================================\n");

    // Demo 7: Elasticsearch Search
    println!("📊 Demo 7: Elasticsearch Search");
    let es_attrs = DatabaseAttributesBuilder::new()
        .system(DatabaseSystem::Elasticsearch)
        .name("logs")
        .operation(DatabaseOperation::Other("search".to_string()))
        .statement(r#"{"query": {"match": {"message": "error"}}}"#)
        .server_address("elasticsearch.example.com")
        .server_port(9200)
        .network_protocol_name("http")
        .network_protocol_version("1.1")
        .build()?;

    println!("  ✅ Created Elasticsearch attributes:");
    for (key, value) in es_attrs.to_attributes() {
        println!("     - {}: {}", key, value);
    }
    println!("\n============================================================\n");

    // Demo 8: Full SQL Example with all attributes
    println!("📊 Demo 8: Full SQL Example");
    let full_attrs = DatabaseAttributesBuilder::new()
        .system(DatabaseSystem::Postgresql)
        .name("production_db")
        .statement("UPDATE users SET last_login = NOW() WHERE id = $1")
        .operation(DatabaseOperation::Update)
        .user("api_service")
        .sql_table("users")
        .server_address("pg-primary.example.com")
        .server_port(5432)
        .network_protocol_name("tcp")
        .network_protocol_version("3.0")
        .connection_string("postgresql://pg-primary.example.com:5432/production_db")
        .build()?;

    println!("  ✅ Created full SQL attributes:");
    let attributes_map = full_attrs.to_attributes();
    println!("     Total attributes: {}", attributes_map.len());
    for (key, value) in attributes_map {
        println!("     - {}: {}", key, value);
    }
    println!("\n============================================================\n");

    println!("✅ All database semantic conventions demos completed successfully!\n");

    Ok(())
}

