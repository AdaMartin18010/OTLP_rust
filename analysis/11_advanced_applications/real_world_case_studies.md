# OTLP 实际应用案例深度分析

## 概述

本文档深入分析OpenTelemetry Protocol (OTLP)在真实世界中的高级应用案例，包括大规模分布式系统、云原生环境、边缘计算场景等。通过具体的案例分析，展示OTLP在实际工程中的价值和应用模式。

## 1. 电商平台可观测性架构

### 1.1 系统架构概述

```text
电商平台架构:
┌─────────────────────────────────────────────────────────────┐
│                    用户界面层                                │
│  (Web App, Mobile App, Admin Dashboard)                     │
├─────────────────────────────────────────────────────────────┤
│                    API网关层                                 │
│  (Kong, Istio Gateway, Rate Limiting, Authentication)       │
├─────────────────────────────────────────────────────────────┤
│                   微服务层                                   │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐            │
│  │ 用户服务     │ │ 商品服务    │ │ 订单服务     │ ...        │
│  │ (User Svc)  │ │(Product Svc)│ │(Order Svc)  │            │
│  └─────────────┘ └─────────────┘ └─────────────┘            │
├─────────────────────────────────────────────────────────────┤
│                   数据层                                     │
│  (PostgreSQL, Redis, MongoDB, Elasticsearch)                │
├─────────────────────────────────────────────────────────────┤
│                  基础设施层                                  │
│  (Kubernetes, Docker, Prometheus, Grafana)                  │
└─────────────────────────────────────────────────────────────┘
```

### 1.2 OTLP集成架构

```rust
// 电商平台OTLP集成示例
use opentelemetry::{global, Context, KeyValue};
use opentelemetry::trace::{Span, Tracer};
use opentelemetry_sdk::{Resource, TracerProvider};
use opentelemetry_otlp::WithExportConfig;

#[derive(Clone)]
pub struct ECommerceObservability {
    tracer: Tracer,
    metrics: MetricsCollector,
    logger: Logger,
}

impl ECommerceObservability {
    pub fn new() -> Self {
        let resource = Resource::new(vec![
            KeyValue::new("service.name", "ecommerce-platform"),
            KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
            KeyValue::new("deployment.environment", "production"),
        ]);

        let tracer_provider = TracerProvider::builder()
            .with_batch_span_processor(
                opentelemetry_otlp::new_pipeline()
                    .tracing()
                    .with_exporter(
                        opentelemetry_otlp::new_exporter()
                            .tonic()
                            .with_endpoint("https://otel-collector:4317")
                    )
                    .with_resource(resource)
                    .build()
            )
            .build();

        let tracer = tracer_provider.tracer("ecommerce-service");

        Self {
            tracer,
            metrics: MetricsCollector::new(),
            logger: Logger::new(),
        }
    }

    pub fn track_user_action(&self, user_id: &str, action: &str, context: &Context) -> Span {
        self.tracer
            .span_builder(format!("user_action:{}", action))
            .with_attributes(vec![
                KeyValue::new("user.id", user_id.to_string()),
                KeyValue::new("action.type", action.to_string()),
                KeyValue::new("service.component", "user-service"),
            ])
            .start_with_context(&self.tracer, context)
    }

    pub fn track_order_processing(&self, order_id: &str, context: &Context) -> Span {
        self.tracer
            .span_builder("order_processing")
            .with_attributes(vec![
                KeyValue::new("order.id", order_id.to_string()),
                KeyValue::new("service.component", "order-service"),
            ])
            .start_with_context(&self.tracer, context)
    }
}

// 用户服务集成示例
pub struct UserService {
    observability: ECommerceObservability,
    user_repository: UserRepository,
}

impl UserService {
    pub async fn create_user(&self, user_data: CreateUserRequest) -> Result<User, ServiceError> {
        let parent_context = Context::current();
        let span = self.observability.track_user_action("", "create_user", &parent_context);
        
        span.set_attribute(KeyValue::new("user.email", user_data.email.clone()));
        span.set_attribute(KeyValue::new("user.registration_source", user_data.source.clone()));

        let result = async {
            // 验证用户数据
            self.validate_user_data(&user_data).await?;
            
            // 检查邮箱是否已存在
            if self.user_repository.email_exists(&user_data.email).await? {
                return Err(ServiceError::EmailAlreadyExists);
            }

            // 创建用户
            let user = self.user_repository.create_user(user_data).await?;
            
            // 记录成功指标
            self.observability.metrics.increment_counter("user.created", 1);
            
            Ok(user)
        }.await;

        match &result {
            Ok(user) => {
                span.set_attribute(KeyValue::new("user.id", user.id.clone()));
                span.set_status(StatusCode::Ok, "User created successfully");
            }
            Err(error) => {
                span.set_status(StatusCode::Error, error.to_string());
                self.observability.metrics.increment_counter("user.creation_failed", 1);
            }
        }

        result
    }
}
```

### 1.3 关键性能指标监控

```rust
// 电商平台KPI监控
pub struct ECommerceKPIMonitor {
    metrics: MetricsCollector,
}

impl ECommerceKPIMonitor {
    pub fn track_conversion_funnel(&self, user_id: &str, step: &str) {
        self.metrics.increment_counter("conversion_funnel", 1, vec![
            KeyValue::new("step", step.to_string()),
            KeyValue::new("user_id", user_id.to_string()),
        ]);
    }

    pub fn track_revenue(&self, order_id: &str, amount: f64, currency: &str) {
        self.metrics.record_histogram("revenue", amount, vec![
            KeyValue::new("order_id", order_id.to_string()),
            KeyValue::new("currency", currency.to_string()),
        ]);
    }

    pub fn track_cart_abandonment(&self, user_id: &str, cart_value: f64) {
        self.metrics.record_histogram("cart_abandonment_value", cart_value, vec![
            KeyValue::new("user_id", user_id.to_string()),
        ]);
    }

    pub fn track_search_performance(&self, query: &str, results_count: i64, response_time_ms: f64) {
        self.metrics.record_histogram("search_response_time", response_time_ms, vec![
            KeyValue::new("query_length", query.len() as f64),
            KeyValue::new("results_count", results_count as f64),
        ]);
    }
}
```

### 1.4 异常检测和告警

```rust
// 电商平台异常检测
pub struct ECommerceAnomalyDetector {
    alerting_service: AlertingService,
    metrics: MetricsCollector,
}

impl ECommerceAnomalyDetector {
    pub async fn detect_payment_anomalies(&self, payment_data: &PaymentData) {
        // 检测异常支付金额
        if payment_data.amount > self.get_threshold("payment_amount_threshold") {
            self.alerting_service.send_alert(
                AlertLevel::High,
                "Unusual payment amount detected",
                format!("Payment amount: ${:.2}", payment_data.amount),
            ).await;
        }

        // 检测异常支付频率
        let recent_payments = self.get_recent_payments(&payment_data.user_id, Duration::from_secs(3600)).await;
        if recent_payments.len() > 10 {
            self.alerting_service.send_alert(
                AlertLevel::Medium,
                "High payment frequency detected",
                format!("User {} made {} payments in the last hour", 
                       payment_data.user_id, recent_payments.len()),
            ).await;
        }

        // 检测地理异常
        if self.is_geographic_anomaly(&payment_data.location, &payment_data.user_id).await {
            self.alerting_service.send_alert(
                AlertLevel::High,
                "Geographic anomaly in payment",
                format!("Payment from unexpected location: {:?}", payment_data.location),
            ).await;
        }
    }

    pub async fn detect_system_performance_issues(&self) {
        // 检测API响应时间异常
        let avg_response_time = self.metrics.get_gauge_value("api_response_time_avg");
        if avg_response_time > 2.0 {
            self.alerting_service.send_alert(
                AlertLevel::High,
                "API response time degradation",
                format!("Average response time: {:.2}s", avg_response_time),
            ).await;
        }

        // 检测错误率异常
        let error_rate = self.metrics.get_gauge_value("error_rate");
        if error_rate > 0.05 {
            self.alerting_service.send_alert(
                AlertLevel::Critical,
                "High error rate detected",
                format!("Error rate: {:.2}%", error_rate * 100.0),
            ).await;
        }
    }
}
```

## 2. 金融服务系统可观测性

### 2.1 金融系统架构

```text
金融服务系统架构:
┌─────────────────────────────────────────────────────────────┐
│                   交易前端                                   │
│  (Trading UI, Mobile App, API Gateway)                      │
├─────────────────────────────────────────────────────────────┤
│                   业务服务层                                 │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐            │
│  │ 交易服务     │ │ 风控服务     │ │ 清算服务    │            │
│  │(Trading Svc)│ │(Risk Svc)   │ │(Settlement) │            │
│  └─────────────┘ └─────────────┘ └─────────────┘            │
├─────────────────────────────────────────────────────────────┤
│                   核心系统层                                 │
│  (Order Management, Position Management, Risk Engine)       │
├─────────────────────────────────────────────────────────────┤
│                   数据层                                     │
│  (Market Data, Transaction DB, Risk Database)               │
├─────────────────────────────────────────────────────────────┤
│                   外部接口层                                 │
│  (Exchange APIs, Market Data Feeds, Clearing House)         │
└─────────────────────────────────────────────────────────────┘
```

### 2.2 金融交易追踪

```rust
// 金融交易OTLP集成
pub struct TradingObservability {
    tracer: Tracer,
    metrics: MetricsCollector,
    compliance_logger: ComplianceLogger,
}

impl TradingObservability {
    pub fn track_order_lifecycle(&self, order: &Order) -> OrderSpan {
        let span = self.tracer
            .span_builder("order_lifecycle")
            .with_attributes(vec![
                KeyValue::new("order.id", order.id.clone()),
                KeyValue::new("order.symbol", order.symbol.clone()),
                KeyValue::new("order.side", order.side.to_string()),
                KeyValue::new("order.quantity", order.quantity as f64),
                KeyValue::new("order.price", order.price),
                KeyValue::new("order.type", order.order_type.to_string()),
                KeyValue::new("trader.id", order.trader_id.clone()),
            ])
            .start(&self.tracer);

        // 记录合规信息
        self.compliance_logger.log_order_creation(order);

        OrderSpan::new(span, self.compliance_logger.clone())
    }

    pub fn track_trade_execution(&self, trade: &Trade) {
        let span = self.tracer
            .span_builder("trade_execution")
            .with_attributes(vec![
                KeyValue::new("trade.id", trade.id.clone()),
                KeyValue::new("trade.symbol", trade.symbol.clone()),
                KeyValue::new("trade.quantity", trade.quantity as f64),
                KeyValue::new("trade.price", trade.price),
                KeyValue::new("trade.timestamp", trade.timestamp as i64),
                KeyValue::new("exchange.id", trade.exchange_id.clone()),
            ])
            .start(&self.tracer);

        // 记录交易指标
        self.metrics.record_histogram("trade_value", trade.quantity as f64 * trade.price, vec![
            KeyValue::new("symbol", trade.symbol.clone()),
            KeyValue::new("exchange", trade.exchange_id.clone()),
        ]);

        // 记录合规信息
        self.compliance_logger.log_trade_execution(trade);

        span.end();
    }

    pub fn track_risk_calculation(&self, risk_data: &RiskData) {
        let span = self.tracer
            .span_builder("risk_calculation")
            .with_attributes(vec![
                KeyValue::new("portfolio.id", risk_data.portfolio_id.clone()),
                KeyValue::new("risk.type", risk_data.risk_type.clone()),
                KeyValue::new("risk.value", risk_data.value),
                KeyValue::new("confidence.level", risk_data.confidence_level),
            ])
            .start(&self.tracer);

        // 记录风险指标
        self.metrics.record_gauge("portfolio_risk", risk_data.value, vec![
            KeyValue::new("portfolio", risk_data.portfolio_id.clone()),
            KeyValue::new("risk_type", risk_data.risk_type.clone()),
        ]);

        span.end();
    }
}

// 订单生命周期追踪
pub struct OrderSpan {
    span: Span,
    compliance_logger: ComplianceLogger,
}

impl OrderSpan {
    pub fn new(span: Span, compliance_logger: ComplianceLogger) -> Self {
        Self { span, compliance_logger }
    }

    pub fn order_submitted(&mut self, order: &Order) {
        self.span.set_attribute(KeyValue::new("order.status", "submitted"));
        self.compliance_logger.log_order_status_change(order, "submitted");
    }

    pub fn order_acknowledged(&mut self, order: &Order) {
        self.span.set_attribute(KeyValue::new("order.status", "acknowledged"));
        self.compliance_logger.log_order_status_change(order, "acknowledged");
    }

    pub fn order_partially_filled(&mut self, order: &Order, fill_quantity: i64) {
        self.span.set_attribute(KeyValue::new("order.status", "partially_filled"));
        self.span.set_attribute(KeyValue::new("order.filled_quantity", fill_quantity as f64));
        self.compliance_logger.log_order_status_change(order, "partially_filled");
    }

    pub fn order_filled(&mut self, order: &Order) {
        self.span.set_attribute(KeyValue::new("order.status", "filled"));
        self.compliance_logger.log_order_status_change(order, "filled");
    }

    pub fn order_cancelled(&mut self, order: &Order, reason: &str) {
        self.span.set_attribute(KeyValue::new("order.status", "cancelled"));
        self.span.set_attribute(KeyValue::new("order.cancel_reason", reason.to_string()));
        self.compliance_logger.log_order_status_change(order, "cancelled");
    }
}
```

### 2.3 合规性和审计追踪

```rust
// 合规性追踪
pub struct ComplianceLogger {
    audit_trail: AuditTrail,
    regulatory_reporter: RegulatoryReporter,
}

impl ComplianceLogger {
    pub fn log_order_creation(&self, order: &Order) {
        let audit_event = AuditEvent {
            event_type: "order_created".to_string(),
            timestamp: SystemTime::now(),
            user_id: order.trader_id.clone(),
            resource_id: order.id.clone(),
            details: serde_json::to_value(order).unwrap(),
            compliance_flags: self.extract_compliance_flags(order),
        };

        self.audit_trail.record_event(audit_event);
    }

    pub fn log_trade_execution(&self, trade: &Trade) {
        let audit_event = AuditEvent {
            event_type: "trade_executed".to_string(),
            timestamp: SystemTime::now(),
            user_id: trade.trader_id.clone(),
            resource_id: trade.id.clone(),
            details: serde_json::to_value(trade).unwrap(),
            compliance_flags: self.extract_compliance_flags(trade),
        };

        self.audit_trail.record_event(audit_event);
        
        // 检查是否需要向监管机构报告
        if self.requires_regulatory_reporting(trade) {
            self.regulatory_reporter.report_trade(trade);
        }
    }

    fn extract_compliance_flags(&self, order: &Order) -> Vec<String> {
        let mut flags = Vec::new();
        
        // 检查大额交易
        if order.quantity as f64 * order.price > 1000000.0 {
            flags.push("large_trade".to_string());
        }
        
        // 检查异常时间交易
        let hour = chrono::Utc::now().hour();
        if hour < 6 || hour > 22 {
            flags.push("after_hours_trade".to_string());
        }
        
        // 检查高频交易
        if self.is_high_frequency_trader(&order.trader_id) {
            flags.push("high_frequency_trading".to_string());
        }
        
        flags
    }
}
```

## 3. 物联网设备监控

### 3.1 IoT设备架构

```text
物联网设备监控架构:
┌─────────────────────────────────────────────────────────────┐
│                   设备层                                    │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐           │
│  │ 传感器设备  │ │ 执行器设备  │ │ 网关设备    │           │
│  │ (Sensors)   │ │ (Actuators) │ │ (Gateways)  │           │
│  └─────────────┘ └─────────────┘ └─────────────┘           │
├─────────────────────────────────────────────────────────────┤
│                   边缘计算层                                │
│  (Edge Processing, Local Analytics, Real-time Control)    │
├─────────────────────────────────────────────────────────────┤
│                   网络层                                    │
│  (5G/6G, LoRaWAN, WiFi, Bluetooth, Cellular)              │
├─────────────────────────────────────────────────────────────┤
│                   云端平台层                                │
│  (Data Ingestion, Processing, Analytics, ML Models)       │
├─────────────────────────────────────────────────────────────┤
│                   应用层                                    │
│  (Dashboard, Alerts, Control Systems, Analytics)          │
└─────────────────────────────────────────────────────────────┘
```

### 3.2 IoT设备数据收集

```rust
// IoT设备OTLP集成
pub struct IoTDeviceMonitor {
    tracer: Tracer,
    metrics: MetricsCollector,
    device_registry: DeviceRegistry,
}

impl IoTDeviceMonitor {
    pub fn track_sensor_reading(&self, device_id: &str, reading: &SensorReading) {
        let span = self.tracer
            .span_builder("sensor_reading")
            .with_attributes(vec![
                KeyValue::new("device.id", device_id.to_string()),
                KeyValue::new("device.type", reading.sensor_type.clone()),
                KeyValue::new("sensor.value", reading.value),
                KeyValue::new("sensor.unit", reading.unit.clone()),
                KeyValue::new("sensor.location", reading.location.clone()),
                KeyValue::new("reading.timestamp", reading.timestamp as i64),
                KeyValue::new("reading.quality", reading.quality_score),
            ])
            .start(&self.tracer);

        // 记录传感器指标
        self.metrics.record_gauge(
            "sensor_value",
            reading.value,
            vec![
                KeyValue::new("device_id", device_id.to_string()),
                KeyValue::new("sensor_type", reading.sensor_type.clone()),
                KeyValue::new("location", reading.location.clone()),
            ]
        );

        // 检查异常值
        if self.is_anomalous_reading(device_id, reading) {
            span.set_attribute(KeyValue::new("reading.anomalous", true));
            self.trigger_anomaly_alert(device_id, reading);
        }

        span.end();
    }

    pub fn track_device_health(&self, device_id: &str, health_data: &DeviceHealth) {
        let span = self.tracer
            .span_builder("device_health_check")
            .with_attributes(vec![
                KeyValue::new("device.id", device_id.to_string()),
                KeyValue::new("health.battery_level", health_data.battery_level),
                KeyValue::new("health.signal_strength", health_data.signal_strength),
                KeyValue::new("health.temperature", health_data.temperature),
                KeyValue::new("health.uptime", health_data.uptime as i64),
                KeyValue::new("health.last_communication", health_data.last_communication as i64),
            ])
            .start(&self.tracer);

        // 记录设备健康指标
        self.metrics.record_gauge("device_battery_level", health_data.battery_level, vec![
            KeyValue::new("device_id", device_id.to_string()),
        ]);

        self.metrics.record_gauge("device_signal_strength", health_data.signal_strength, vec![
            KeyValue::new("device_id", device_id.to_string()),
        ]);

        // 检查设备健康状态
        if health_data.battery_level < 0.2 {
            self.trigger_low_battery_alert(device_id, health_data.battery_level);
        }

        if health_data.signal_strength < -80.0 {
            self.trigger_weak_signal_alert(device_id, health_data.signal_strength);
        }

        span.end();
    }

    pub fn track_device_control_command(&self, device_id: &str, command: &ControlCommand) {
        let span = self.tracer
            .span_builder("device_control_command")
            .with_attributes(vec![
                KeyValue::new("device.id", device_id.to_string()),
                KeyValue::new("command.type", command.command_type.clone()),
                KeyValue::new("command.parameters", serde_json::to_string(&command.parameters).unwrap()),
                KeyValue::new("command.source", command.source.clone()),
                KeyValue::new("command.priority", command.priority as f64),
            ])
            .start(&self.tracer);

        // 记录控制命令指标
        self.metrics.increment_counter("device_commands_sent", 1, vec![
            KeyValue::new("device_id", device_id.to_string()),
            KeyValue::new("command_type", command.command_type.clone()),
        ]);

        span.end();
    }

    fn is_anomalous_reading(&self, device_id: &str, reading: &SensorReading) -> bool {
        // 获取设备的历史数据统计
        let stats = self.device_registry.get_device_stats(device_id);
        
        // 检查是否超出正常范围
        let mean = stats.mean;
        let std_dev = stats.standard_deviation;
        let threshold = 3.0; // 3-sigma rule
        
        (reading.value - mean).abs() > threshold * std_dev
    }

    fn trigger_anomaly_alert(&self, device_id: &str, reading: &SensorReading) {
        // 发送异常告警
        let alert = Alert {
            severity: AlertLevel::Medium,
            device_id: device_id.to_string(),
            message: format!("Anomalous reading detected: {} {} (expected range: {:.2} ± {:.2})", 
                           reading.value, reading.unit, 
                           self.device_registry.get_device_stats(device_id).mean,
                           self.device_registry.get_device_stats(device_id).standard_deviation),
            timestamp: SystemTime::now(),
        };
        
        // 发送告警到告警系统
        self.send_alert(alert);
    }
}
```

### 3.3 边缘计算集成

```rust
// 边缘计算OTLP集成
pub struct EdgeComputingMonitor {
    tracer: Tracer,
    metrics: MetricsCollector,
    edge_nodes: HashMap<String, EdgeNode>,
}

impl EdgeComputingMonitor {
    pub fn track_edge_processing(&self, node_id: &str, processing_task: &ProcessingTask) {
        let span = self.tracer
            .span_builder("edge_processing")
            .with_attributes(vec![
                KeyValue::new("edge_node.id", node_id.to_string()),
                KeyValue::new("task.type", processing_task.task_type.clone()),
                KeyValue::new("task.priority", processing_task.priority as f64),
                KeyValue::new("task.data_size", processing_task.data_size as f64),
                KeyValue::new("task.complexity", processing_task.complexity as f64),
            ])
            .start(&self.tracer);

        // 记录边缘处理指标
        self.metrics.record_histogram(
            "edge_processing_time",
            processing_task.processing_time.as_secs_f64(),
            vec![
                KeyValue::new("edge_node_id", node_id.to_string()),
                KeyValue::new("task_type", processing_task.task_type.clone()),
            ]
        );

        // 记录资源使用情况
        self.metrics.record_gauge("edge_cpu_usage", processing_task.cpu_usage, vec![
            KeyValue::new("edge_node_id", node_id.to_string()),
        ]);

        self.metrics.record_gauge("edge_memory_usage", processing_task.memory_usage, vec![
            KeyValue::new("edge_node_id", node_id.to_string()),
        ]);

        span.end();
    }

    pub fn track_data_sync(&self, node_id: &str, sync_data: &SyncData) {
        let span = self.tracer
            .span_builder("data_sync")
            .with_attributes(vec![
                KeyValue::new("edge_node.id", node_id.to_string()),
                KeyValue::new("sync.direction", sync_data.direction.clone()),
                KeyValue::new("sync.data_size", sync_data.data_size as f64),
                KeyValue::new("sync.records_count", sync_data.records_count as f64),
                KeyValue::new("sync.compression_ratio", sync_data.compression_ratio),
            ])
            .start(&self.tracer);

        // 记录数据同步指标
        self.metrics.record_histogram(
            "data_sync_time",
            sync_data.sync_time.as_secs_f64(),
            vec![
                KeyValue::new("edge_node_id", node_id.to_string()),
                KeyValue::new("sync_direction", sync_data.direction.clone()),
            ]
        );

        self.metrics.record_gauge("sync_bandwidth_usage", sync_data.bandwidth_usage, vec![
            KeyValue::new("edge_node_id", node_id.to_string()),
        ]);

        span.end();
    }
}
```

## 4. 云原生微服务架构

### 4.1 服务网格可观测性

```rust
// 服务网格OTLP集成
pub struct ServiceMeshObservability {
    tracer: Tracer,
    metrics: MetricsCollector,
    service_registry: ServiceRegistry,
}

impl ServiceMeshObservability {
    pub fn track_service_request(&self, request: &ServiceRequest) -> ServiceRequestSpan {
        let span = self.tracer
            .span_builder("service_request")
            .with_attributes(vec![
                KeyValue::new("service.name", request.service_name.clone()),
                KeyValue::new("service.version", request.service_version.clone()),
                KeyValue::new("request.method", request.method.clone()),
                KeyValue::new("request.path", request.path.clone()),
                KeyValue::new("request.headers", serde_json::to_string(&request.headers).unwrap()),
                KeyValue::new("client.ip", request.client_ip.clone()),
                KeyValue::new("user.agent", request.user_agent.clone()),
            ])
            .start(&self.tracer);

        ServiceRequestSpan::new(span, self.metrics.clone())
    }

    pub fn track_service_dependency(&self, dependency: &ServiceDependency) {
        let span = self.tracer
            .span_builder("service_dependency")
            .with_attributes(vec![
                KeyValue::new("source.service", dependency.source_service.clone()),
                KeyValue::new("target.service", dependency.target_service.clone()),
                KeyValue::new("dependency.type", dependency.dependency_type.clone()),
                KeyValue::new("dependency.latency", dependency.latency.as_secs_f64()),
                KeyValue::new("dependency.success", dependency.success),
            ])
            .start(&self.tracer);

        // 记录服务依赖指标
        self.metrics.record_histogram(
            "service_dependency_latency",
            dependency.latency.as_secs_f64(),
            vec![
                KeyValue::new("source_service", dependency.source_service.clone()),
                KeyValue::new("target_service", dependency.target_service.clone()),
                KeyValue::new("dependency_type", dependency.dependency_type.clone()),
            ]
        );

        if dependency.success {
            self.metrics.increment_counter("service_dependency_success", 1, vec![
                KeyValue::new("source_service", dependency.source_service.clone()),
                KeyValue::new("target_service", dependency.target_service.clone()),
            ]);
        } else {
            self.metrics.increment_counter("service_dependency_failure", 1, vec![
                KeyValue::new("source_service", dependency.source_service.clone()),
                KeyValue::new("target_service", dependency.target_service.clone()),
                KeyValue::new("error_type", dependency.error_type.clone()),
            ]);
        }

        span.end();
    }

    pub fn track_circuit_breaker(&self, circuit_breaker: &CircuitBreakerEvent) {
        let span = self.tracer
            .span_builder("circuit_breaker")
            .with_attributes(vec![
                KeyValue::new("circuit_breaker.name", circuit_breaker.name.clone()),
                KeyValue::new("circuit_breaker.state", circuit_breaker.state.clone()),
                KeyValue::new("circuit_breaker.failure_rate", circuit_breaker.failure_rate),
                KeyValue::new("circuit_breaker.request_count", circuit_breaker.request_count as f64),
                KeyValue::new("circuit_breaker.failure_count", circuit_breaker.failure_count as f64),
            ])
            .start(&self.tracer);

        // 记录熔断器指标
        self.metrics.record_gauge("circuit_breaker_failure_rate", circuit_breaker.failure_rate, vec![
            KeyValue::new("circuit_breaker_name", circuit_breaker.name.clone()),
        ]);

        self.metrics.record_gauge("circuit_breaker_state", 
            match circuit_breaker.state.as_str() {
                "CLOSED" => 0.0,
                "OPEN" => 1.0,
                "HALF_OPEN" => 0.5,
                _ => -1.0,
            },
            vec![
                KeyValue::new("circuit_breaker_name", circuit_breaker.name.clone()),
            ]
        );

        span.end();
    }
}

// 服务请求追踪
pub struct ServiceRequestSpan {
    span: Span,
    metrics: MetricsCollector,
    start_time: Instant,
}

impl ServiceRequestSpan {
    pub fn new(span: Span, metrics: MetricsCollector) -> Self {
        Self {
            span,
            metrics,
            start_time: Instant::now(),
        }
    }

    pub fn set_response_status(&mut self, status_code: u16) {
        self.span.set_attribute(KeyValue::new("response.status_code", status_code as f64));
        
        // 记录响应状态指标
        self.metrics.increment_counter("http_requests_total", 1, vec![
            KeyValue::new("status_code", status_code.to_string()),
        ]);
    }

    pub fn set_response_size(&mut self, size: usize) {
        self.span.set_attribute(KeyValue::new("response.size", size as f64));
    }

    pub fn set_processing_time(&mut self) {
        let processing_time = self.start_time.elapsed();
        self.span.set_attribute(KeyValue::new("processing.time", processing_time.as_secs_f64()));
        
        // 记录处理时间指标
        self.metrics.record_histogram("request_processing_time", processing_time.as_secs_f64(), vec![]);
    }

    pub fn end(self) {
        self.set_processing_time();
        self.span.end();
    }
}
```

## 5. 性能优化案例分析

### 5.1 大规模数据处理优化

```rust
// 大规模数据处理OTLP优化
pub struct DataProcessingOptimizer {
    tracer: Tracer,
    metrics: MetricsCollector,
    batch_processor: BatchProcessor,
}

impl DataProcessingOptimizer {
    pub async fn process_large_dataset(&self, dataset: &Dataset) -> ProcessingResult {
        let span = self.tracer
            .span_builder("large_dataset_processing")
            .with_attributes(vec![
                KeyValue::new("dataset.size", dataset.size as f64),
                KeyValue::new("dataset.records", dataset.records_count as f64),
                KeyValue::new("dataset.type", dataset.data_type.clone()),
                KeyValue::new("processing.strategy", "batched_parallel".to_string()),
            ])
            .start(&self.tracer);

        // 分批处理大数据集
        let batch_size = self.calculate_optimal_batch_size(dataset.size);
        let batches = self.split_dataset_into_batches(dataset, batch_size);

        let mut processing_tasks = Vec::new();
        
        for (batch_id, batch) in batches.into_iter().enumerate() {
            let task = self.process_batch_async(batch_id, batch);
            processing_tasks.push(task);
        }

        // 并发处理所有批次
        let results = futures::future::join_all(processing_tasks).await;
        
        // 合并结果
        let final_result = self.merge_batch_results(results);

        // 记录处理指标
        self.metrics.record_histogram("dataset_processing_time", 
            span.start_time().elapsed().as_secs_f64(),
            vec![
                KeyValue::new("dataset_type", dataset.data_type.clone()),
            ]
        );

        span.end();
        final_result
    }

    fn calculate_optimal_batch_size(&self, dataset_size: usize) -> usize {
        // 基于系统资源和数据特征计算最优批次大小
        let available_memory = self.get_available_memory();
        let cpu_cores = num_cpus::get();
        
        // 每个批次应该占用约 1/CPU核心数的内存
        let memory_per_batch = available_memory / cpu_cores;
        let estimated_record_size = 1024; // 假设每条记录1KB
        
        (memory_per_batch / estimated_record_size).min(dataset_size)
    }

    async fn process_batch_async(&self, batch_id: usize, batch: DataBatch) -> BatchResult {
        let span = self.tracer
            .span_builder("batch_processing")
            .with_attributes(vec![
                KeyValue::new("batch.id", batch_id as f64),
                KeyValue::new("batch.size", batch.size as f64),
                KeyValue::new("batch.records", batch.records.len() as f64),
            ])
            .start(&self.tracer);

        let start_time = Instant::now();
        let result = self.batch_processor.process_batch(batch).await;
        let processing_time = start_time.elapsed();

        // 记录批次处理指标
        self.metrics.record_histogram("batch_processing_time", processing_time.as_secs_f64(), vec![
            KeyValue::new("batch_id", batch_id.to_string()),
        ]);

        span.end();
        result
    }
}
```

### 5.2 实时流处理优化

```rust
// 实时流处理OTLP优化
pub struct StreamProcessingOptimizer {
    tracer: Tracer,
    metrics: MetricsCollector,
    stream_processor: StreamProcessor,
}

impl StreamProcessingOptimizer {
    pub async fn process_stream(&self, stream_config: &StreamConfig) -> StreamProcessor {
        let span = self.tracer
            .span_builder("stream_processing_setup")
            .with_attributes(vec![
                KeyValue::new("stream.name", stream_config.name.clone()),
                KeyValue::new("stream.partitions", stream_config.partitions as f64),
                KeyValue::new("stream.consumer_groups", stream_config.consumer_groups.len() as f64),
                KeyValue::new("processing.window_size", stream_config.window_size.as_secs_f64()),
            ])
            .start(&self.tracer);

        // 创建流处理器
        let processor = self.stream_processor
            .with_batch_size(stream_config.batch_size)
            .with_parallelism(stream_config.parallelism)
            .with_backpressure_control(stream_config.backpressure_config.clone())
            .with_metrics_collector(self.metrics.clone())
            .build();

        span.end();
        processor
    }

    pub fn track_stream_metrics(&self, metrics: &StreamMetrics) {
        // 记录吞吐量指标
        self.metrics.record_gauge("stream_throughput", metrics.throughput, vec![
            KeyValue::new("stream_name", metrics.stream_name.clone()),
        ]);

        // 记录延迟指标
        self.metrics.record_histogram("stream_latency", metrics.latency.as_secs_f64(), vec![
            KeyValue::new("stream_name", metrics.stream_name.clone()),
        ]);

        // 记录错误率
        self.metrics.record_gauge("stream_error_rate", metrics.error_rate, vec![
            KeyValue::new("stream_name", metrics.stream_name.clone()),
        ]);

        // 记录背压指标
        if metrics.backpressure_level > 0.8 {
            self.metrics.record_gauge("stream_backpressure", metrics.backpressure_level, vec![
                KeyValue::new("stream_name", metrics.stream_name.clone()),
                KeyValue::new("backpressure_level", "high".to_string()),
            ]);
        }
    }
}
```

## 6. 最佳实践总结

### 6.1 性能优化原则

1. **分层监控**: 从基础设施到应用层的全方位监控
2. **智能采样**: 基于数据价值和系统负载的自适应采样
3. **批量处理**: 合理使用批量操作减少系统开销
4. **异步处理**: 异步处理非关键路径的可观测性数据
5. **缓存策略**: 合理使用缓存减少重复计算

### 6.2 可观测性设计原则

1. **语义一致性**: 确保跨系统的语义约定一致性
2. **上下文传播**: 正确传播和关联可观测性上下文
3. **错误处理**: 完善的错误处理和恢复机制
4. **安全考虑**: 保护敏感数据和隐私信息
5. **合规要求**: 满足行业和法规的合规要求

### 6.3 运维最佳实践

1. **告警策略**: 基于业务影响的分级告警策略
2. **自动化响应**: 自动化的故障检测和恢复机制
3. **容量规划**: 基于历史数据的容量规划和扩展策略
4. **性能调优**: 持续的性能监控和调优
5. **文档维护**: 完善的文档和知识管理

---

*本文档通过实际应用案例分析，展示了OTLP在不同行业和场景中的深度应用，为实际工程实践提供参考和指导。*
