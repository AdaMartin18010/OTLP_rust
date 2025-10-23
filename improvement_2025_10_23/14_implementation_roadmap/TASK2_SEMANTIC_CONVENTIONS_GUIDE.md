# 任务2: 语义约定完善 - 详细实施指南

**📅 启动日期**: 2025年11月13日  
**⏱️ 预计工期**: 4-6周  
**🎯 目标**: 实现90%+语义约定覆盖度  
**📊 优先级**: P0（最高）

---

## 📋 任务概览

### 目标

完善OpenTelemetry语义约定实现，确保项目符合最新的语义约定标准，提供类型安全的API，使用户能够正确地设置遥测数据属性。

### 预期成果

```yaml
覆盖度目标:
  HTTP语义约定: 100%
  数据库语义约定: 90%+
  消息队列语义约定: 90%+
  Kubernetes语义约定: 100%
  通用资源约定: 100%

质量目标:
  类型安全API: 100%
  验证工具: 完整
  文档: 优秀
  测试覆盖率: 80%+
  示例代码: 丰富
```

---

## 🗓️ 实施时间线

### Phase 1: HTTP语义约定 (Week 4-5)

**时间**: 11月13日 - 11月26日（2周）  
**负责人**: 待分配

#### Week 4详细计划 (11/13-11/19)

```yaml
周一-周二 (11/13-11/14):
  任务: HTTP客户端属性实现
  产出:
    - http.request.method
    - http.request.body.size
    - http.response.status_code
    - http.response.body.size
    - url.scheme, url.path, url.query
    - user_agent.original
  
周三-周四 (11/15-11/16):
  任务: HTTP服务端属性实现
  产出:
    - server.address
    - server.port
    - network.protocol.name
    - network.protocol.version
    - client.address
    - client.port

周五 (11/17):
  任务: 类型安全API设计
  产出:
    - HttpAttributes struct
    - HttpAttributesBuilder
    - HttpMethod enum
    - HttpStatusCode enum
```

#### Week 5详细计划 (11/20-11/26)

```yaml
周一-周二 (11/20-11/21):
  任务: 属性验证逻辑
  产出:
    - 必需字段验证
    - 类型验证
    - 值范围验证
    - 最佳实践检查

周三-周四 (11/22-11/23):
  任务: 测试和示例
  产出:
    - 单元测试
    - 集成测试
    - 使用示例
    - 最佳实践示例

周五 (11/24):
  任务: 文档和review
  产出:
    - API文档
    - 用户指南
    - 代码审查
```

### Phase 2: 数据库语义约定 (Week 6)

**时间**: 11月27日 - 12月3日（1周）  
**负责人**: 待分配

```yaml
周一-周二 (11/27-11/28):
  任务: 通用数据库属性
  产出:
    - db.system (postgresql, mysql, mongodb等)
    - db.name
    - db.statement
    - db.operation (select, insert, update, delete等)
    - db.user
    - db.connection_string (sanitized)

周三 (11/29):
  任务: SQL数据库特定属性
  产出:
    - db.sql.table
    - db.postgresql.* 
    - db.mysql.*
    - db.mssql.*

周四 (12/1):
  任务: NoSQL数据库特定属性
  产出:
    - db.redis.database_index
    - db.mongodb.collection
    - db.cassandra.keyspace
    - db.cosmosdb.*

周五 (12/2):
  任务: 测试和文档
  产出:
    - 单元测试
    - 使用示例
    - API文档
```

### Phase 3: 消息队列语义约定 (Week 7)

**时间**: 12月4日 - 12月10日（1周）  
**负责人**: 待分配

```yaml
周一-周二 (12/4-12/5):
  任务: 通用消息队列属性
  产出:
    - messaging.system (kafka, rabbitmq, sqs等)
    - messaging.operation (publish, receive, process)
    - messaging.destination
    - messaging.destination_kind
    - messaging.protocol
    - messaging.message_id
    - messaging.conversation_id

周三 (12/6):
  任务: Kafka特定属性
  产出:
    - messaging.kafka.topic
    - messaging.kafka.partition
    - messaging.kafka.consumer_group
    - messaging.kafka.offset

周四 (12/7):
  任务: RabbitMQ特定属性
  产出:
    - messaging.rabbitmq.exchange
    - messaging.rabbitmq.routing_key
    - messaging.rabbitmq.queue

周五 (12/8):
  任务: 测试和文档
  产出:
    - 单元测试
    - Kafka/RabbitMQ示例
    - API文档
```

### Phase 4: Kubernetes语义约定 (Week 8)

**时间**: 12月11日 - 12月17日（1周）  
**负责人**: 待分配

```yaml
周一-周二 (12/11-12/12):
  任务: K8s资源属性
  产出:
    - k8s.namespace.name
    - k8s.pod.name
    - k8s.pod.uid
    - k8s.deployment.name
    - k8s.container.name
    - k8s.container.image.name
    - k8s.node.name
    - k8s.cluster.name

周三 (12/13):
  任务: K8s元数据收集器
  产出:
    - 从环境变量读取
    - 从Downward API读取
    - 从Kubernetes API读取
    - 自动检测和填充

周四-周五 (12/14-12/15):
  任务: 测试和文档
  产出:
    - 单元测试
    - K8s环境集成测试
    - 部署示例
    - API文档
```

### Phase 5: 通用资源约定和验证工具 (Week 9)

**时间**: 12月18日 - 12月24日（1周）  
**负责人**: 待分配

```yaml
周一-周二 (12/18-12/19):
  任务: 通用资源属性
  产出:
    - service.name
    - service.version
    - service.namespace
    - service.instance.id
    - deployment.environment
    - telemetry.sdk.name
    - telemetry.sdk.language
    - telemetry.sdk.version

周三-周四 (12/20-12/21):
  任务: 验证工具实现
  产出:
    - SemanticValidator
    - 属性完整性检查
    - 类型和值验证
    - 最佳实践建议
    - 错误报告

周五 (12/22):
  任务: CLI工具和CI/CD集成
  产出:
    - otlp-semconv-check CLI
    - GitHub Action
    - 配置文件支持
    - 文档
```

---

## 💻 技术实现

### 1. 类型安全的属性系统

#### 设计原则

```rust
// 设计原则：
// 1. 类型安全 - 使用enum和struct强制正确性
// 2. 构建器模式 - 提供流畅的API
// 3. 验证 - 在编译时和运行时验证
// 4. 文档 - 每个属性都有文档注释
```

#### 核心结构

```rust
// src/semantic_conventions/mod.rs

/// 语义约定模块入口
pub mod http;
pub mod database;
pub mod messaging;
pub mod k8s;
pub mod resource;
pub mod validator;

// 通用trait
pub trait SemanticAttributes {
    /// 转换为键值对
    fn to_key_values(&self) -> Vec<(String, AttributeValue)>;
    
    /// 验证属性完整性
    fn validate(&self) -> Result<(), ValidationError>;
}

// 属性值类型
#[derive(Debug, Clone)]
pub enum AttributeValue {
    String(String),
    Int(i64),
    Float(f64),
    Bool(bool),
    Array(Vec<AttributeValue>),
}
```

### 2. HTTP语义约定

```rust
// src/semantic_conventions/http.rs

use super::{AttributeValue, SemanticAttributes};

/// HTTP请求方法
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HttpMethod {
    Get,
    Post,
    Put,
    Delete,
    Patch,
    Head,
    Options,
    Connect,
    Trace,
}

impl HttpMethod {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Get => "GET",
            Self::Post => "POST",
            Self::Put => "PUT",
            Self::Delete => "DELETE",
            Self::Patch => "PATCH",
            Self::Head => "HEAD",
            Self::Options => "OPTIONS",
            Self::Connect => "CONNECT",
            Self::Trace => "TRACE",
        }
    }
}

/// HTTP属性
#[derive(Debug, Clone)]
pub struct HttpAttributes {
    // 请求属性
    pub request_method: HttpMethod,
    pub request_body_size: Option<u64>,
    
    // 响应属性
    pub response_status_code: u16,
    pub response_body_size: Option<u64>,
    
    // URL属性
    pub url_scheme: String,
    pub url_path: String,
    pub url_query: Option<String>,
    
    // 服务器属性
    pub server_address: String,
    pub server_port: u16,
    
    // 网络属性
    pub network_protocol_name: Option<String>,
    pub network_protocol_version: Option<String>,
    
    // 用户代理
    pub user_agent_original: Option<String>,
}

impl HttpAttributes {
    /// 创建构建器
    pub fn builder() -> HttpAttributesBuilder {
        HttpAttributesBuilder::default()
    }
}

impl SemanticAttributes for HttpAttributes {
    fn to_key_values(&self) -> Vec<(String, AttributeValue)> {
        let mut kvs = vec![
            ("http.request.method".to_string(), 
             AttributeValue::String(self.request_method.as_str().to_string())),
            ("http.response.status_code".to_string(), 
             AttributeValue::Int(self.response_status_code as i64)),
            ("url.scheme".to_string(), 
             AttributeValue::String(self.url_scheme.clone())),
            ("url.path".to_string(), 
             AttributeValue::String(self.url_path.clone())),
            ("server.address".to_string(), 
             AttributeValue::String(self.server_address.clone())),
            ("server.port".to_string(), 
             AttributeValue::Int(self.server_port as i64)),
        ];
        
        // 添加可选属性
        if let Some(size) = self.request_body_size {
            kvs.push(("http.request.body.size".to_string(), 
                     AttributeValue::Int(size as i64)));
        }
        
        if let Some(size) = self.response_body_size {
            kvs.push(("http.response.body.size".to_string(), 
                     AttributeValue::Int(size as i64)));
        }
        
        if let Some(query) = &self.url_query {
            kvs.push(("url.query".to_string(), 
                     AttributeValue::String(query.clone())));
        }
        
        if let Some(name) = &self.network_protocol_name {
            kvs.push(("network.protocol.name".to_string(), 
                     AttributeValue::String(name.clone())));
        }
        
        if let Some(version) = &self.network_protocol_version {
            kvs.push(("network.protocol.version".to_string(), 
                     AttributeValue::String(version.clone())));
        }
        
        if let Some(ua) = &self.user_agent_original {
            kvs.push(("user_agent.original".to_string(), 
                     AttributeValue::String(ua.clone())));
        }
        
        kvs
    }
    
    fn validate(&self) -> Result<(), ValidationError> {
        // 验证状态码范围
        if !(100..=599).contains(&self.response_status_code) {
            return Err(ValidationError::InvalidValue {
                field: "response_status_code".to_string(),
                reason: "HTTP status code must be in range 100-599".to_string(),
            });
        }
        
        // 验证端口范围
        if self.server_port == 0 {
            return Err(ValidationError::InvalidValue {
                field: "server_port".to_string(),
                reason: "Port must be non-zero".to_string(),
            });
        }
        
        Ok(())
    }
}

/// HTTP属性构建器
#[derive(Default)]
pub struct HttpAttributesBuilder {
    request_method: Option<HttpMethod>,
    request_body_size: Option<u64>,
    response_status_code: Option<u16>,
    response_body_size: Option<u64>,
    url_scheme: Option<String>,
    url_path: Option<String>,
    url_query: Option<String>,
    server_address: Option<String>,
    server_port: Option<u16>,
    network_protocol_name: Option<String>,
    network_protocol_version: Option<String>,
    user_agent_original: Option<String>,
}

impl HttpAttributesBuilder {
    /// 设置请求方法（必需）
    pub fn request_method(mut self, method: HttpMethod) -> Self {
        self.request_method = Some(method);
        self
    }
    
    /// 设置请求体大小
    pub fn request_body_size(mut self, size: u64) -> Self {
        self.request_body_size = Some(size);
        self
    }
    
    /// 设置响应状态码（必需）
    pub fn response_status_code(mut self, code: u16) -> Self {
        self.response_status_code = Some(code);
        self
    }
    
    /// 设置响应体大小
    pub fn response_body_size(mut self, size: u64) -> Self {
        self.response_body_size = Some(size);
        self
    }
    
    /// 设置URL scheme（必需）
    pub fn url_scheme(mut self, scheme: impl Into<String>) -> Self {
        self.url_scheme = Some(scheme.into());
        self
    }
    
    /// 设置URL路径（必需）
    pub fn url_path(mut self, path: impl Into<String>) -> Self {
        self.url_path = Some(path.into());
        self
    }
    
    /// 设置URL查询字符串
    pub fn url_query(mut self, query: impl Into<String>) -> Self {
        self.url_query = Some(query.into());
        self
    }
    
    /// 设置服务器地址（必需）
    pub fn server_address(mut self, address: impl Into<String>) -> Self {
        self.server_address = Some(address.into());
        self
    }
    
    /// 设置服务器端口（必需）
    pub fn server_port(mut self, port: u16) -> Self {
        self.server_port = Some(port);
        self
    }
    
    /// 设置网络协议名称
    pub fn network_protocol_name(mut self, name: impl Into<String>) -> Self {
        self.network_protocol_name = Some(name.into());
        self
    }
    
    /// 设置网络协议版本
    pub fn network_protocol_version(mut self, version: impl Into<String>) -> Self {
        self.network_protocol_version = Some(version.into());
        self
    }
    
    /// 设置用户代理
    pub fn user_agent_original(mut self, ua: impl Into<String>) -> Self {
        self.user_agent_original = Some(ua.into());
        self
    }
    
    /// 构建HTTP属性
    pub fn build(self) -> Result<HttpAttributes, BuildError> {
        Ok(HttpAttributes {
            request_method: self.request_method
                .ok_or(BuildError::MissingField("request_method"))?,
            request_body_size: self.request_body_size,
            response_status_code: self.response_status_code
                .ok_or(BuildError::MissingField("response_status_code"))?,
            response_body_size: self.response_body_size,
            url_scheme: self.url_scheme
                .ok_or(BuildError::MissingField("url_scheme"))?,
            url_path: self.url_path
                .ok_or(BuildError::MissingField("url_path"))?,
            url_query: self.url_query,
            server_address: self.server_address
                .ok_or(BuildError::MissingField("server_address"))?,
            server_port: self.server_port
                .ok_or(BuildError::MissingField("server_port"))?,
            network_protocol_name: self.network_protocol_name,
            network_protocol_version: self.network_protocol_version,
            user_agent_original: self.user_agent_original,
        })
    }
}

// 常量定义
pub mod constants {
    pub const REQUEST_METHOD: &str = "http.request.method";
    pub const REQUEST_BODY_SIZE: &str = "http.request.body.size";
    pub const RESPONSE_STATUS_CODE: &str = "http.response.status_code";
    pub const RESPONSE_BODY_SIZE: &str = "http.response.body.size";
    pub const URL_SCHEME: &str = "url.scheme";
    pub const URL_PATH: &str = "url.path";
    pub const URL_QUERY: &str = "url.query";
    pub const SERVER_ADDRESS: &str = "server.address";
    pub const SERVER_PORT: &str = "server.port";
    pub const NETWORK_PROTOCOL_NAME: &str = "network.protocol.name";
    pub const NETWORK_PROTOCOL_VERSION: &str = "network.protocol.version";
    pub const USER_AGENT_ORIGINAL: &str = "user_agent.original";
}

#[derive(Debug, thiserror::Error)]
pub enum BuildError {
    #[error("Missing required field: {0}")]
    MissingField(&'static str),
}

#[derive(Debug, thiserror::Error)]
pub enum ValidationError {
    #[error("Invalid value for field '{field}': {reason}")]
    InvalidValue { field: String, reason: String },
}
```

### 3. 数据库语义约定

```rust
// src/semantic_conventions/database.rs

use super::{AttributeValue, SemanticAttributes};

/// 数据库系统类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DbSystem {
    // SQL数据库
    Postgresql,
    Mysql,
    Mssql,
    Oracle,
    Db2,
    Sqlite,
    
    // NoSQL数据库
    Redis,
    Mongodb,
    Cassandra,
    Dynamodb,
    Cosmosdb,
    Elasticsearch,
}

impl DbSystem {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Postgresql => "postgresql",
            Self::Mysql => "mysql",
            Self::Mssql => "mssql",
            Self::Oracle => "oracle",
            Self::Db2 => "db2",
            Self::Sqlite => "sqlite",
            Self::Redis => "redis",
            Self::Mongodb => "mongodb",
            Self::Cassandra => "cassandra",
            Self::Dynamodb => "dynamodb",
            Self::Cosmosdb => "cosmosdb",
            Self::Elasticsearch => "elasticsearch",
        }
    }
}

/// 数据库操作类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DbOperation {
    Select,
    Insert,
    Update,
    Delete,
    Create,
    Drop,
    Alter,
    Custom(&'static str),
}

impl DbOperation {
    pub fn as_str(&self) -> &str {
        match self {
            Self::Select => "select",
            Self::Insert => "insert",
            Self::Update => "update",
            Self::Delete => "delete",
            Self::Create => "create",
            Self::Drop => "drop",
            Self::Alter => "alter",
            Self::Custom(s) => s,
        }
    }
}

/// 数据库属性
#[derive(Debug, Clone)]
pub struct DatabaseAttributes {
    // 通用属性
    pub system: DbSystem,
    pub name: String,
    pub statement: Option<String>,
    pub operation: Option<DbOperation>,
    pub user: Option<String>,
    
    // SQL特定
    pub sql_table: Option<String>,
    
    // Redis特定
    pub redis_database_index: Option<u32>,
    
    // MongoDB特定
    pub mongodb_collection: Option<String>,
    
    // Cassandra特定
    pub cassandra_keyspace: Option<String>,
}

impl DatabaseAttributes {
    pub fn builder(system: DbSystem) -> DatabaseAttributesBuilder {
        DatabaseAttributesBuilder {
            system,
            ..Default::default()
        }
    }
}

impl SemanticAttributes for DatabaseAttributes {
    fn to_key_values(&self) -> Vec<(String, AttributeValue)> {
        let mut kvs = vec![
            ("db.system".to_string(), 
             AttributeValue::String(self.system.as_str().to_string())),
            ("db.name".to_string(), 
             AttributeValue::String(self.name.clone())),
        ];
        
        if let Some(stmt) = &self.statement {
            kvs.push(("db.statement".to_string(), 
                     AttributeValue::String(stmt.clone())));
        }
        
        if let Some(op) = &self.operation {
            kvs.push(("db.operation".to_string(), 
                     AttributeValue::String(op.as_str().to_string())));
        }
        
        if let Some(user) = &self.user {
            kvs.push(("db.user".to_string(), 
                     AttributeValue::String(user.clone())));
        }
        
        // SQL特定
        if let Some(table) = &self.sql_table {
            kvs.push(("db.sql.table".to_string(), 
                     AttributeValue::String(table.clone())));
        }
        
        // Redis特定
        if let Some(index) = self.redis_database_index {
            kvs.push(("db.redis.database_index".to_string(), 
                     AttributeValue::Int(index as i64)));
        }
        
        // MongoDB特定
        if let Some(coll) = &self.mongodb_collection {
            kvs.push(("db.mongodb.collection".to_string(), 
                     AttributeValue::String(coll.clone())));
        }
        
        // Cassandra特定
        if let Some(ks) = &self.cassandra_keyspace {
            kvs.push(("db.cassandra.keyspace".to_string(), 
                     AttributeValue::String(ks.clone())));
        }
        
        kvs
    }
    
    fn validate(&self) -> Result<(), ValidationError> {
        // 验证特定数据库的必需字段
        match self.system {
            DbSystem::Redis => {
                if self.redis_database_index.is_none() {
                    return Err(ValidationError::InvalidValue {
                        field: "redis_database_index".to_string(),
                        reason: "Required for Redis".to_string(),
                    });
                }
            }
            DbSystem::Mongodb => {
                if self.mongodb_collection.is_none() {
                    return Err(ValidationError::InvalidValue {
                        field: "mongodb_collection".to_string(),
                        reason: "Required for MongoDB".to_string(),
                    });
                }
            }
            DbSystem::Cassandra => {
                if self.cassandra_keyspace.is_none() {
                    return Err(ValidationError::InvalidValue {
                        field: "cassandra_keyspace".to_string(),
                        reason: "Required for Cassandra".to_string(),
                    });
                }
            }
            _ => {}
        }
        
        Ok(())
    }
}

#[derive(Default)]
pub struct DatabaseAttributesBuilder {
    system: DbSystem,
    name: Option<String>,
    statement: Option<String>,
    operation: Option<DbOperation>,
    user: Option<String>,
    sql_table: Option<String>,
    redis_database_index: Option<u32>,
    mongodb_collection: Option<String>,
    cassandra_keyspace: Option<String>,
}

impl DatabaseAttributesBuilder {
    pub fn name(mut self, name: impl Into<String>) -> Self {
        self.name = Some(name.into());
        self
    }
    
    pub fn statement(mut self, stmt: impl Into<String>) -> Self {
        self.statement = Some(stmt.into());
        self
    }
    
    pub fn operation(mut self, op: DbOperation) -> Self {
        self.operation = Some(op);
        self
    }
    
    pub fn user(mut self, user: impl Into<String>) -> Self {
        self.user = Some(user.into());
        self
    }
    
    pub fn sql_table(mut self, table: impl Into<String>) -> Self {
        self.sql_table = Some(table.into());
        self
    }
    
    pub fn redis_database_index(mut self, index: u32) -> Self {
        self.redis_database_index = Some(index);
        self
    }
    
    pub fn mongodb_collection(mut self, coll: impl Into<String>) -> Self {
        self.mongodb_collection = Some(coll.into());
        self
    }
    
    pub fn cassandra_keyspace(mut self, ks: impl Into<String>) -> Self {
        self.cassandra_keyspace = Some(ks.into());
        self
    }
    
    pub fn build(self) -> Result<DatabaseAttributes, BuildError> {
        Ok(DatabaseAttributes {
            system: self.system,
            name: self.name.ok_or(BuildError::MissingField("name"))?,
            statement: self.statement,
            operation: self.operation,
            user: self.user,
            sql_table: self.sql_table,
            redis_database_index: self.redis_database_index,
            mongodb_collection: self.mongodb_collection,
            cassandra_keyspace: self.cassandra_keyspace,
        })
    }
}
```

### 4. 验证工具

```rust
// src/semantic_conventions/validator.rs

use super::{SemanticAttributes, ValidationError};

/// 语义约定验证器
pub struct SemanticValidator {
    rules: Vec<Box<dyn ValidationRule>>,
}

impl SemanticValidator {
    pub fn new() -> Self {
        Self {
            rules: vec![
                Box::new(RequiredFieldsRule),
                Box::new(TypeCheckRule),
                Box::new(ValueRangeRule),
                Box::new(BestPracticeRule),
            ],
        }
    }
    
    /// 验证属性
    pub fn validate<A: SemanticAttributes>(&self, attrs: &A) -> ValidationResult {
        let mut errors = Vec::new();
        let mut warnings = Vec::new();
        
        // 运行所有验证规则
        for rule in &self.rules {
            match rule.check(attrs) {
                RuleResult::Pass => {}
                RuleResult::Error(e) => errors.push(e),
                RuleResult::Warning(w) => warnings.push(w),
            }
        }
        
        ValidationResult {
            passed: errors.is_empty(),
            errors,
            warnings,
        }
    }
}

/// 验证结果
#[derive(Debug)]
pub struct ValidationResult {
    pub passed: bool,
    pub errors: Vec<String>,
    pub warnings: Vec<String>,
}

impl ValidationResult {
    pub fn print_report(&self) {
        if self.passed {
            println!("✅ Validation passed!");
        } else {
            println!("❌ Validation failed with {} errors", self.errors.len());
            for error in &self.errors {
                println!("  ERROR: {}", error);
            }
        }
        
        if !self.warnings.is_empty() {
            println!("⚠️  {} warnings:", self.warnings.len());
            for warning in &self.warnings {
                println!("  WARN: {}", warning);
            }
        }
    }
}

/// 验证规则trait
trait ValidationRule {
    fn check<A: SemanticAttributes>(&self, attrs: &A) -> RuleResult;
}

enum RuleResult {
    Pass,
    Error(String),
    Warning(String),
}

// 必需字段检查
struct RequiredFieldsRule;

impl ValidationRule for RequiredFieldsRule {
    fn check<A: SemanticAttributes>(&self, attrs: &A) -> RuleResult {
        match attrs.validate() {
            Ok(_) => RuleResult::Pass,
            Err(e) => RuleResult::Error(format!("Required field check failed: {}", e)),
        }
    }
}

// 类型检查
struct TypeCheckRule;

impl ValidationRule for TypeCheckRule {
    fn check<A: SemanticAttributes>(&self, _attrs: &A) -> RuleResult {
        // 类型检查在编译时完成
        RuleResult::Pass
    }
}

// 值范围检查
struct ValueRangeRule;

impl ValidationRule for ValueRangeRule {
    fn check<A: SemanticAttributes>(&self, _attrs: &A) -> RuleResult {
        // 值范围检查逻辑
        RuleResult::Pass
    }
}

// 最佳实践检查
struct BestPracticeRule;

impl ValidationRule for BestPracticeRule {
    fn check<A: SemanticAttributes>(&self, _attrs: &A) -> RuleResult {
        // 最佳实践检查
        RuleResult::Pass
    }
}
```

---

## 📝 使用示例

### HTTP属性示例

```rust
use otlp::semantic_conventions::http::{HttpAttributes, HttpMethod};

// 使用构建器创建HTTP属性
let http_attrs = HttpAttributes::builder()
    .request_method(HttpMethod::Post)
    .request_body_size(1024)
    .response_status_code(200)
    .response_body_size(2048)
    .url_scheme("https")
    .url_path("/api/users")
    .url_query("page=1&size=20")
    .server_address("api.example.com")
    .server_port(443)
    .network_protocol_name("http")
    .network_protocol_version("1.1")
    .user_agent_original("Mozilla/5.0...")
    .build()?;

// 验证属性
http_attrs.validate()?;

// 转换为键值对
let kvs = http_attrs.to_key_values();

// 添加到span
span.set_attributes(kvs);
```

### 数据库属性示例

```rust
use otlp::semantic_conventions::database::{DatabaseAttributes, DbSystem, DbOperation};

// PostgreSQL示例
let db_attrs = DatabaseAttributes::builder(DbSystem::Postgresql)
    .name("myapp_db")
    .statement("SELECT * FROM users WHERE id = $1")
    .operation(DbOperation::Select)
    .user("app_user")
    .sql_table("users")
    .build()?;

// Redis示例
let redis_attrs = DatabaseAttributes::builder(DbSystem::Redis)
    .name("cache")
    .operation(DbOperation::Custom("GET"))
    .redis_database_index(0)
    .build()?;

// MongoDB示例
let mongo_attrs = DatabaseAttributes::builder(DbSystem::Mongodb)
    .name("myapp")
    .mongodb_collection("users")
    .operation(DbOperation::Select)
    .build()?;
```

### 验证工具使用示例

```rust
use otlp::semantic_conventions::validator::SemanticValidator;

let validator = SemanticValidator::new();

// 验证HTTP属性
let result = validator.validate(&http_attrs);
result.print_report();

// 验证数据库属性
let result = validator.validate(&db_attrs);
if !result.passed {
    eprintln!("Validation failed!");
    for error in result.errors {
        eprintln!("  {}", error);
    }
}
```

---

## ✅ 验收标准

### 功能完整性

```yaml
HTTP语义约定:
  ✅ 客户端属性 100%
  ✅ 服务端属性 100%
  ✅ URL属性 100%
  ✅ 网络属性 100%

数据库语义约定:
  ✅ 通用属性 100%
  ✅ SQL数据库 90%+
  ✅ NoSQL数据库 90%+

消息队列语义约定:
  ✅ 通用属性 100%
  ✅ Kafka 100%
  ✅ RabbitMQ 100%
  ✅ AWS SQS 90%+

Kubernetes语义约定:
  ✅ 资源属性 100%
  ✅ 元数据收集 100%

通用资源约定:
  ✅ Service属性 100%
  ✅ Deployment属性 100%
  ✅ SDK属性 100%

验证工具:
  ✅ 属性验证器 100%
  ✅ CLI工具 100%
  ✅ CI/CD集成 100%
```

### 质量标准

```yaml
代码质量:
  ✅ 类型安全API
  ✅ 构建器模式
  ✅ 错误处理完善
  ✅ 文档注释完整

测试覆盖率:
  ✅ 单元测试 >80%
  ✅ 集成测试 >70%
  ✅ 示例代码 100%

文档:
  ✅ API文档完整
  ✅ 用户指南清晰
  ✅ 示例丰富
  ✅ 最佳实践明确
```

---

## 📊 进度追踪

进度将在 `PROGRESS_TRACKER_Q4_2025.md` 中每周更新。

---

**创建日期**: 2025年10月23日  
**预计完成**: 2025年12月24日  
**负责人**: 待分配  

🚀 **让我们构建类型安全的语义约定系统！**
