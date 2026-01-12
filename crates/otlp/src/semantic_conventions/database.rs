//! Database Semantic Conventions
//!
//! This module implements OpenTelemetry semantic conventions for database operations.
//! It provides type-safe builders for creating database-related attributes.
//!
//! ## Supported Database Systems
//!
//! - **SQL Databases**: PostgreSQL, MySQL, MSSQL, Oracle, etc.
//! - **NoSQL Databases**: MongoDB, Redis, Cassandra, Elasticsearch, etc.
//!
//! ## Usage Example
//!
//! ```rust
//! use otlp::semantic_conventions::database::{
//!     DatabaseAttributesBuilder, DatabaseSystem, DatabaseOperation,
//! };
//!
//! let attrs = DatabaseAttributesBuilder::new()
//!     .system(DatabaseSystem::Postgresql)
//!     .name("users_db")
//!     .statement("SELECT * FROM users WHERE id = $1")
//!     .operation(DatabaseOperation::Select)
//!     .user("app_user")
//!     .build()
//!     .unwrap();
//! ```

use super::common::AttributeValue;
use std::collections::HashMap;

/// Supported database systems
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DatabaseSystem {
    /// PostgreSQL
    Postgresql,
    /// MySQL
    Mysql,
    /// Microsoft SQL Server
    Mssql,
    /// Oracle Database
    Oracle,
    /// IBM Db2
    Db2,
    /// SQLite
    Sqlite,
    /// MariaDB
    Mariadb,
    /// MongoDB
    Mongodb,
    /// Redis
    Redis,
    /// Apache Cassandra
    Cassandra,
    /// Elasticsearch
    Elasticsearch,
    /// CouchDB
    Couchdb,
    /// DynamoDB
    Dynamodb,
    /// Neo4j
    Neo4j,
    /// Other database system
    Other(String),
}

impl DatabaseSystem {
    /// Returns the string representation of the database system
    pub fn as_str(&self) -> &str {
        match self {
            DatabaseSystem::Postgresql => "postgresql",
            DatabaseSystem::Mysql => "mysql",
            DatabaseSystem::Mssql => "mssql",
            DatabaseSystem::Oracle => "oracle",
            DatabaseSystem::Db2 => "db2",
            DatabaseSystem::Sqlite => "sqlite",
            DatabaseSystem::Mariadb => "mariadb",
            DatabaseSystem::Mongodb => "mongodb",
            DatabaseSystem::Redis => "redis",
            DatabaseSystem::Cassandra => "cassandra",
            DatabaseSystem::Elasticsearch => "elasticsearch",
            DatabaseSystem::Couchdb => "couchdb",
            DatabaseSystem::Dynamodb => "dynamodb",
            DatabaseSystem::Neo4j => "neo4j",
            DatabaseSystem::Other(s) => s.as_str(),
        }
    }
}

impl std::fmt::Display for DatabaseSystem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Database operation types
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DatabaseOperation {
    /// SELECT operation
    Select,
    /// INSERT operation
    Insert,
    /// UPDATE operation
    Update,
    /// DELETE operation
    Delete,
    /// CREATE operation
    Create,
    /// DROP operation
    Drop,
    /// ALTER operation
    Alter,
    /// TRUNCATE operation
    Truncate,
    /// MongoDB: find
    Find,
    /// MongoDB: insert
    InsertOne,
    /// MongoDB: update
    UpdateOne,
    /// MongoDB: delete
    DeleteOne,
    /// Redis: GET
    Get,
    /// Redis: SET
    Set,
    /// Redis: DEL
    Del,
    /// Redis: HGET
    Hget,
    /// Redis: HSET
    Hset,
    /// Other operation
    Other(String),
}

impl DatabaseOperation {
    /// Returns the string representation of the operation
    pub fn as_str(&self) -> &str {
        match self {
            DatabaseOperation::Select => "select",
            DatabaseOperation::Insert => "insert",
            DatabaseOperation::Update => "update",
            DatabaseOperation::Delete => "delete",
            DatabaseOperation::Create => "create",
            DatabaseOperation::Drop => "drop",
            DatabaseOperation::Alter => "alter",
            DatabaseOperation::Truncate => "truncate",
            DatabaseOperation::Find => "find",
            DatabaseOperation::InsertOne => "insertOne",
            DatabaseOperation::UpdateOne => "updateOne",
            DatabaseOperation::DeleteOne => "deleteOne",
            DatabaseOperation::Get => "get",
            DatabaseOperation::Set => "set",
            DatabaseOperation::Del => "del",
            DatabaseOperation::Hget => "hget",
            DatabaseOperation::Hset => "hset",
            DatabaseOperation::Other(s) => s.as_str(),
        }
    }
}

impl std::fmt::Display for DatabaseOperation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Database attributes following OpenTelemetry semantic conventions
#[derive(Debug, Clone)]
pub struct DatabaseAttributes {
    /// Database system identifier (REQUIRED)
    pub system: DatabaseSystem,
    /// Database name (REQUIRED)
    pub name: String,
    /// Database statement being executed
    pub statement: Option<String>,
    /// Database operation being executed
    pub operation: Option<DatabaseOperation>,
    /// Database user
    pub user: Option<String>,
    /// Connection string (sanitized, without credentials)
    pub connection_string: Option<String>,
    /// SQL table name
    pub sql_table: Option<String>,
    /// Redis database index
    pub redis_database_index: Option<u32>,
    /// MongoDB collection name
    pub mongodb_collection: Option<String>,
    /// Cassandra keyspace name
    pub cassandra_keyspace: Option<String>,
    /// Server address (host)
    pub server_address: Option<String>,
    /// Server port
    pub server_port: Option<u16>,
    /// Network protocol name (e.g., "tcp", "unix")
    pub network_protocol_name: Option<String>,
    /// Network protocol version
    pub network_protocol_version: Option<String>,
}

impl DatabaseAttributes {
    /// Converts the attributes to a HashMap
    pub fn to_attributes(&self) -> HashMap<String, AttributeValue> {
        let mut map = HashMap::new();

        // Required fields
        map.insert(
            "db.system".to_string(),
            AttributeValue::String(self.system.as_str().to_string()),
        );
        map.insert(
            "db.name".to_string(),
            AttributeValue::String(self.name.clone()),
        );

        // Optional fields
        if let Some(ref statement) = self.statement {
            map.insert(
                "db.statement".to_string(),
                AttributeValue::String(statement.clone()),
            );
        }

        if let Some(ref operation) = self.operation {
            map.insert(
                "db.operation".to_string(),
                AttributeValue::String(operation.as_str().to_string()),
            );
        }

        if let Some(ref user) = self.user {
            map.insert("db.user".to_string(), AttributeValue::String(user.clone()));
        }

        if let Some(ref conn_str) = self.connection_string {
            map.insert(
                "db.connection_string".to_string(),
                AttributeValue::String(conn_str.clone()),
            );
        }

        // Database-specific attributes
        if let Some(ref table) = self.sql_table {
            map.insert(
                "db.sql.table".to_string(),
                AttributeValue::String(table.clone()),
            );
        }

        if let Some(index) = self.redis_database_index {
            map.insert(
                "db.redis.database_index".to_string(),
                AttributeValue::Int(index as i64),
            );
        }

        if let Some(ref collection) = self.mongodb_collection {
            map.insert(
                "db.mongodb.collection".to_string(),
                AttributeValue::String(collection.clone()),
            );
        }

        if let Some(ref keyspace) = self.cassandra_keyspace {
            map.insert(
                "db.cassandra.keyspace".to_string(),
                AttributeValue::String(keyspace.clone()),
            );
        }

        // Network attributes
        if let Some(ref address) = self.server_address {
            map.insert(
                "server.address".to_string(),
                AttributeValue::String(address.clone()),
            );
        }

        if let Some(port) = self.server_port {
            map.insert("server.port".to_string(), AttributeValue::Int(port as i64));
        }

        if let Some(ref protocol_name) = self.network_protocol_name {
            map.insert(
                "network.protocol.name".to_string(),
                AttributeValue::String(protocol_name.clone()),
            );
        }

        if let Some(ref protocol_version) = self.network_protocol_version {
            map.insert(
                "network.protocol.version".to_string(),
                AttributeValue::String(protocol_version.clone()),
            );
        }

        map
    }
}

/// Builder for DatabaseAttributes
#[derive(Debug, Default)]
pub struct DatabaseAttributesBuilder {
    system: Option<DatabaseSystem>,
    name: Option<String>,
    statement: Option<String>,
    operation: Option<DatabaseOperation>,
    user: Option<String>,
    connection_string: Option<String>,
    sql_table: Option<String>,
    redis_database_index: Option<u32>,
    mongodb_collection: Option<String>,
    cassandra_keyspace: Option<String>,
    server_address: Option<String>,
    server_port: Option<u16>,
    network_protocol_name: Option<String>,
    network_protocol_version: Option<String>,
}

impl DatabaseAttributesBuilder {
    /// Creates a new DatabaseAttributesBuilder
    pub fn new() -> Self {
        Self::default()
    }

    /// Sets the database system (REQUIRED)
    pub fn system(mut self, system: DatabaseSystem) -> Self {
        self.system = Some(system);
        self
    }

    /// Sets the database name (REQUIRED)
    pub fn name(mut self, name: impl Into<String>) -> Self {
        self.name = Some(name.into());
        self
    }

    /// Sets the database statement
    pub fn statement(mut self, statement: impl Into<String>) -> Self {
        self.statement = Some(statement.into());
        self
    }

    /// Sets the database operation
    pub fn operation(mut self, operation: DatabaseOperation) -> Self {
        self.operation = Some(operation);
        self
    }

    /// Sets the database user
    pub fn user(mut self, user: impl Into<String>) -> Self {
        self.user = Some(user.into());
        self
    }

    /// Sets the connection string (should be sanitized)
    pub fn connection_string(mut self, conn_str: impl Into<String>) -> Self {
        self.connection_string = Some(conn_str.into());
        self
    }

    /// Sets the SQL table name
    pub fn sql_table(mut self, table: impl Into<String>) -> Self {
        self.sql_table = Some(table.into());
        self
    }

    /// Sets the Redis database index
    pub fn redis_database_index(mut self, index: u32) -> Self {
        self.redis_database_index = Some(index);
        self
    }

    /// Sets the MongoDB collection name
    pub fn mongodb_collection(mut self, collection: impl Into<String>) -> Self {
        self.mongodb_collection = Some(collection.into());
        self
    }

    /// Sets the Cassandra keyspace name
    pub fn cassandra_keyspace(mut self, keyspace: impl Into<String>) -> Self {
        self.cassandra_keyspace = Some(keyspace.into());
        self
    }

    /// Sets the server address
    pub fn server_address(mut self, address: impl Into<String>) -> Self {
        self.server_address = Some(address.into());
        self
    }

    /// Sets the server port
    pub fn server_port(mut self, port: u16) -> Self {
        self.server_port = Some(port);
        self
    }

    /// Sets the network protocol name
    pub fn network_protocol_name(mut self, protocol: impl Into<String>) -> Self {
        self.network_protocol_name = Some(protocol.into());
        self
    }

    /// Sets the network protocol version
    pub fn network_protocol_version(mut self, version: impl Into<String>) -> Self {
        self.network_protocol_version = Some(version.into());
        self
    }

    /// Builds the DatabaseAttributes
    pub fn build(self) -> Result<DatabaseAttributes, String> {
        let system = self
            .system
            .ok_or_else(|| "db.system is required".to_string())?;
        let name = self.name.ok_or_else(|| "db.name is required".to_string())?;

        Ok(DatabaseAttributes {
            system,
            name,
            statement: self.statement,
            operation: self.operation,
            user: self.user,
            connection_string: self.connection_string,
            sql_table: self.sql_table,
            redis_database_index: self.redis_database_index,
            mongodb_collection: self.mongodb_collection,
            cassandra_keyspace: self.cassandra_keyspace,
            server_address: self.server_address,
            server_port: self.server_port,
            network_protocol_name: self.network_protocol_name,
            network_protocol_version: self.network_protocol_version,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_postgresql_basic() {
        let attrs = DatabaseAttributesBuilder::new()
            .system(DatabaseSystem::Postgresql)
            .name("users_db")
            .statement("SELECT * FROM users WHERE id = $1")
            .operation(DatabaseOperation::Select)
            .user("app_user")
            .build()
            .unwrap();

        let map = attrs.to_attributes();
        assert_eq!(
            map.get("db.system"),
            Some(&AttributeValue::String("postgresql".to_string()))
        );
        assert_eq!(
            map.get("db.name"),
            Some(&AttributeValue::String("users_db".to_string()))
        );
        assert_eq!(
            map.get("db.operation"),
            Some(&AttributeValue::String("select".to_string()))
        );
    }

    #[test]
    fn test_mongodb_with_collection() {
        let attrs = DatabaseAttributesBuilder::new()
            .system(DatabaseSystem::Mongodb)
            .name("production")
            .mongodb_collection("users")
            .operation(DatabaseOperation::Find)
            .statement("{\"_id\": \"123\"}")
            .build()
            .unwrap();

        let map = attrs.to_attributes();
        assert_eq!(
            map.get("db.system"),
            Some(&AttributeValue::String("mongodb".to_string()))
        );
        assert_eq!(
            map.get("db.mongodb.collection"),
            Some(&AttributeValue::String("users".to_string()))
        );
    }

    #[test]
    fn test_redis_with_index() {
        let attrs = DatabaseAttributesBuilder::new()
            .system(DatabaseSystem::Redis)
            .name("cache")
            .redis_database_index(0)
            .operation(DatabaseOperation::Get)
            .statement("GET user:123")
            .build()
            .unwrap();

        let map = attrs.to_attributes();
        assert_eq!(
            map.get("db.redis.database_index"),
            Some(&AttributeValue::Int(0))
        );
    }

    #[test]
    fn test_mysql_with_network_info() {
        let attrs = DatabaseAttributesBuilder::new()
            .system(DatabaseSystem::Mysql)
            .name("ecommerce")
            .sql_table("orders")
            .operation(DatabaseOperation::Insert)
            .server_address("mysql.example.com")
            .server_port(3306)
            .network_protocol_name("tcp")
            .build()
            .unwrap();

        let map = attrs.to_attributes();
        assert_eq!(
            map.get("server.address"),
            Some(&AttributeValue::String("mysql.example.com".to_string()))
        );
        assert_eq!(map.get("server.port"), Some(&AttributeValue::Int(3306)));
    }

    #[test]
    fn test_missing_required_fields() {
        let result = DatabaseAttributesBuilder::new().name("test_db").build();
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), "db.system is required");

        let result = DatabaseAttributesBuilder::new()
            .system(DatabaseSystem::Postgresql)
            .build();
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), "db.name is required");
    }
}
