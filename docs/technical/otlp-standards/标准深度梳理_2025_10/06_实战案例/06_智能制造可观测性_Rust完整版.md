# 智能制造可观测性 - OpenTelemetry Rust 完整实战

> **版本信息**
>
> - Rust: 1.90 (2024 Edition)
> - opentelemetry: 0.31.0
> - 更新日期: 2025-10-08
> - 行业: 智能制造 / 工业IoT

## 目录

- [智能制造可观测性 - OpenTelemetry Rust 完整实战](#智能制造可观测性---opentelemetry-rust-完整实战)
  - [目录](#目录)
  - [概述](#概述)
    - [核心特性](#核心特性)
  - [系统架构](#系统架构)
  - [核心依赖配置](#核心依赖配置)
    - [Cargo.toml](#cargotoml)
  - [1. 设备数据采集](#1-设备数据采集)
    - [设备模型](#设备模型)
    - [MQTT 数据采集追踪](#mqtt-数据采集追踪)
  - [2. 生产线监控](#2-生产线监控)
    - [生产线模型](#生产线模型)
    - [OEE 计算追踪](#oee-计算追踪)
  - [3. 质量检测追踪](#3-质量检测追踪)
    - [质量检测模型](#质量检测模型)
    - [质量检测追踪](#质量检测追踪)
  - [4. 设备预测性维护](#4-设备预测性维护)
    - [维护模型](#维护模型)
    - [预测性维护追踪](#预测性维护追踪)
  - [5. 能耗管理](#5-能耗管理)
    - [能耗模型](#能耗模型)
    - [能耗监控追踪](#能耗监控追踪)
  - [6. 仓储物流追踪](#6-仓储物流追踪)
    - [物料模型](#物料模型)
    - [物料追踪](#物料追踪)
  - [7. MES 系统集成](#7-mes-系统集成)
    - [MES 工单模型](#mes-工单模型)
    - [工单执行追踪](#工单执行追踪)
  - [8. 时序数据处理](#8-时序数据处理)
    - [时序数据查询](#时序数据查询)
  - [9. 实时告警](#9-实时告警)
    - [告警规则](#告警规则)
    - [告警处理](#告警处理)
  - [10. 完整示例](#10-完整示例)
    - [main.rs](#mainrs)
  - [总结](#总结)

---

## 概述

智能制造场景涉及大量IoT设备、实时数据采集和复杂的生产流程。
本文档展示如何使用 OpenTelemetry Rust SDK 实现工业场景的完整可观测性。

### 核心特性

- ✅ IoT 设备数据采集追踪
- ✅ 生产线实时监控
- ✅ 设备OEE (Overall Equipment Effectiveness) 计算
- ✅ 预测性维护
- ✅ 能耗分析
- ✅ 质量追溯

---

## 系统架构

```text
┌────────────────────────────────────────────────────┐
│               Edge Computing Layer                 │
│  ┌──────┐  ┌──────┐  ┌──────┐  ┌──────┐            │
│  │ PLC  │  │Sensor│  │Camera│  │Robot │            │
│  └───┬──┘  └───┬──┘  └───┬──┘  └───┬──┘            │
│      └──────────┴─────────┴─────────┘              │
│                    │                               │
│           ┌────────▼────────┐                      │
│           │  Edge Gateway   │                      │
│           │  (Rust + MQTT)  │                      │
│           └────────┬────────┘                      │
└────────────────────┼───────────────────────────────┘
                     │
        ┌────────────┼────────────┐
        │            │            │
┌───────▼────┐ ┌────▼────┐ ┌────▼────┐
│   MES      │ │ Device  │ │ Quality │
│  System    │ │ Manager │ │ Control │
└───────┬────┘ └────┬────┘ └────┬────┘
        │           │           │
        └───────────┴───────────┘
                    │
        ┌───────────┼───────────┐
        │           │           │
  ┌─────▼────┐ ┌───▼────┐ ┌───▼────┐
  │InfluxDB  │ │  Kafka │ │  PG    │
  │(时序数据) │ │  (MQ)  │ │  (业务)│
  └──────────┘ └────────┘ └────────┘
```

---

## 核心依赖配置

### Cargo.toml

```toml
[package]
name = "smart-manufacturing"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

[dependencies]
# OpenTelemetry
opentelemetry = "0.31.0"
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio", "metrics"] }
opentelemetry-otlp = "0.24.0"
tracing = "0.1.41"
tracing-opentelemetry = "0.27.0"

# 异步运行时
tokio = { version = "1.43.0", features = ["full"] }

# MQTT (设备通信)
rumqttc = "0.24.0"

# 时序数据库
influxdb = "0.7.2"

# 数据库
sqlx = { version = "0.8.2", features = ["postgres", "runtime-tokio"] }

# 消息队列
rdkafka = "0.37.0"

# 序列化
serde = { version = "1.0.216", features = ["derive"] }
serde_json = "1.0.133"

# 时间处理
chrono = "0.4.39"

# UUID
uuid = { version = "1.11.0", features = ["v4", "serde"] }

# 错误处理
thiserror = "2.0.9"
anyhow = "1.0.95"
```

---

## 1. 设备数据采集

### 设备模型

```rust
use serde::{Deserialize, Serialize};
use uuid::Uuid;
use chrono::{DateTime, Utc};

/// 设备类型
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum DeviceType {
    PLC,           // 可编程逻辑控制器
    Sensor,        // 传感器
    Robot,         // 机器人
    CNCMachine,    // 数控机床
    AGV,           // 自动导引车
    Conveyor,      // 输送带
}

/// 设备状态
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum DeviceStatus {
    Idle,          // 空闲
    Running,       // 运行中
    Maintenance,   // 维护中
    Error,         // 故障
    Offline,       // 离线
}

/// 设备信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Device {
    pub id: Uuid,
    pub device_code: String,
    pub device_type: DeviceType,
    pub name: String,
    pub location: String,
    pub status: DeviceStatus,
    pub last_heartbeat: DateTime<Utc>,
}

/// 设备数据点
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceDataPoint {
    pub device_id: Uuid,
    pub timestamp: DateTime<Utc>,
    pub metrics: Vec<Metric>,
}

/// 指标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Metric {
    pub name: String,
    pub value: f64,
    pub unit: String,
}
```

### MQTT 数据采集追踪

```rust
use rumqttc::{AsyncClient, MqttOptions, QoS};
use tracing::{instrument, info, warn, error};

/// 设备数据采集服务
pub struct DeviceDataCollector {
    mqtt_client: AsyncClient,
    influxdb_client: influxdb::Client,
}

impl DeviceDataCollector {
    /// 初始化MQTT连接
    pub async fn new() -> Result<Self, CollectorError> {
        let mut mqttoptions = MqttOptions::new("data-collector", "localhost", 1883);
        mqttoptions.set_keep_alive(std::time::Duration::from_secs(60));
        
        let (client, mut eventloop) = AsyncClient::new(mqttoptions, 100);
        
        // 订阅设备主题
        client.subscribe("devices/+/data", QoS::AtLeastOnce).await?;
        
        let influxdb_client = influxdb::Client::new("http://localhost:8086", "manufacturing");
        
        Ok(Self {
            mqtt_client: client,
            influxdb_client,
        })
    }
    
    /// 启动数据采集
    #[instrument(name = "collector.start", skip(self))]
    pub async fn start_collecting(&mut self) -> Result<(), CollectorError> {
        info!("Starting device data collection");
        
        loop {
            match self.eventloop.poll().await {
                Ok(notification) => {
                    if let rumqttc::Event::Incoming(rumqttc::Packet::Publish(publish)) = notification {
                        self.process_device_data(&publish).await?;
                    }
                }
                Err(e) => {
                    error!("MQTT error: {}", e);
                }
            }
        }
    }
    
    /// 处理设备数据
    #[instrument(name = "collector.process", skip(self, publish))]
    async fn process_device_data(
        &self,
        publish: &rumqttc::Publish,
    ) -> Result<(), CollectorError> {
        let topic = &publish.topic;
        let payload = String::from_utf8(publish.payload.to_vec())?;
        
        // 解析设备ID
        let device_id = self.extract_device_id_from_topic(topic)?;
        
        // 解析数据点
        let data_point: DeviceDataPoint = serde_json::from_str(&payload)?;
        
        info!(
            device_id = %device_id,
            metrics_count = data_point.metrics.len(),
            "Device data received"
        );
        
        // 写入时序数据库
        self.write_to_influxdb(&data_point).await?;
        
        // 检查异常
        self.check_anomalies(&data_point).await?;
        
        Ok(())
    }
    
    /// 写入 InfluxDB
    #[instrument(name = "collector.write_influxdb", skip(self, data_point))]
    async fn write_to_influxdb(
        &self,
        data_point: &DeviceDataPoint,
    ) -> Result<(), CollectorError> {
        use influxdb::{InfluxDbWriteable, Timestamp};
        
        for metric in &data_point.metrics {
            let query = influxdb::Query::write_query(
                Timestamp::Milliseconds(data_point.timestamp.timestamp_millis() as u128),
                "device_metrics"
            )
            .add_field("value", metric.value)
            .add_tag("device_id", data_point.device_id.to_string())
            .add_tag("metric_name", &metric.name)
            .add_tag("unit", &metric.unit);
            
            self.influxdb_client.query(query).await?;
        }
        
        info!("Data written to InfluxDB");
        Ok(())
    }
    
    fn extract_device_id_from_topic(&self, topic: &str) -> Result<Uuid, CollectorError> {
        let parts: Vec<&str> = topic.split('/').collect();
        if parts.len() >= 2 {
            Uuid::parse_str(parts[1]).map_err(|e| CollectorError::InvalidDeviceId(e.to_string()))
        } else {
            Err(CollectorError::InvalidTopic)
        }
    }
}
```

---

## 2. 生产线监控

### 生产线模型

```rust
/// 生产线
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProductionLine {
    pub id: Uuid,
    pub name: String,
    pub devices: Vec<Uuid>,
    pub status: ProductionLineStatus,
    pub current_batch: Option<Uuid>,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum ProductionLineStatus {
    Idle,
    Running,
    Paused,
    Stopped,
}

/// 生产批次
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProductionBatch {
    pub id: Uuid,
    pub product_code: String,
    pub quantity: i32,
    pub start_time: DateTime<Utc>,
    pub end_time: Option<DateTime<Utc>>,
    pub completed_count: i32,
    pub defect_count: i32,
}
```

### OEE 计算追踪

```rust
/// OEE (Overall Equipment Effectiveness) 计算服务
pub struct OEECalculationService {
    db_pool: sqlx::PgPool,
}

impl OEECalculationService {
    /// 计算设备 OEE
    #[instrument(
        name = "oee.calculate",
        skip(self),
        fields(device_id = %device_id)
    )]
    pub async fn calculate_oee(
        &self,
        device_id: Uuid,
        start_time: DateTime<Utc>,
        end_time: DateTime<Utc>,
    ) -> Result<OEEMetrics, OEEError> {
        info!("Calculating OEE");
        
        // 1. 计算可用性 (Availability)
        let availability = self.calculate_availability(device_id, start_time, end_time).await?;
        
        // 2. 计算性能 (Performance)
        let performance = self.calculate_performance(device_id, start_time, end_time).await?;
        
        // 3. 计算质量 (Quality)
        let quality = self.calculate_quality(device_id, start_time, end_time).await?;
        
        // 4. 计算 OEE
        let oee = availability * performance * quality;
        
        info!(
            availability = availability,
            performance = performance,
            quality = quality,
            oee = oee,
            "OEE calculated"
        );
        
        Ok(OEEMetrics {
            device_id,
            start_time,
            end_time,
            availability,
            performance,
            quality,
            oee,
        })
    }
    
    /// 计算可用性
    #[instrument(skip(self))]
    async fn calculate_availability(
        &self,
        device_id: Uuid,
        start_time: DateTime<Utc>,
        end_time: DateTime<Utc>,
    ) -> Result<f64, OEEError> {
        let total_time = (end_time - start_time).num_seconds() as f64;
        
        // 查询停机时间
        let downtime: Option<i64> = sqlx::query_scalar(
            r#"
            SELECT SUM(EXTRACT(EPOCH FROM (end_time - start_time)))
            FROM device_downtime
            WHERE device_id = $1 AND start_time >= $2 AND end_time <= $3
            "#
        )
        .bind(device_id)
        .bind(start_time)
        .bind(end_time)
        .fetch_one(&self.db_pool)
        .await?;
        
        let downtime = downtime.unwrap_or(0) as f64;
        let operating_time = total_time - downtime;
        
        Ok(operating_time / total_time)
    }
    
    /// 计算性能
    #[instrument(skip(self))]
    async fn calculate_performance(
        &self,
        device_id: Uuid,
        start_time: DateTime<Utc>,
        end_time: DateTime<Utc>,
    ) -> Result<f64, OEEError> {
        // 查询实际产量
        let actual_output: Option<i64> = sqlx::query_scalar(
            r#"
            SELECT SUM(output_count)
            FROM production_records
            WHERE device_id = $1 AND timestamp >= $2 AND timestamp <= $3
            "#
        )
        .bind(device_id)
        .bind(start_time)
        .bind(end_time)
        .fetch_one(&self.db_pool)
        .await?;
        
        // 查询理论产能
        let ideal_cycle_time: f64 = sqlx::query_scalar(
            "SELECT ideal_cycle_time FROM devices WHERE id = $1"
        )
        .bind(device_id)
        .fetch_one(&self.db_pool)
        .await?;
        
        let operating_time = self.get_operating_time(device_id, start_time, end_time).await?;
        let ideal_output = operating_time / ideal_cycle_time;
        
        let actual = actual_output.unwrap_or(0) as f64;
        Ok(actual / ideal_output)
    }
    
    /// 计算质量
    #[instrument(skip(self))]
    async fn calculate_quality(
        &self,
        device_id: Uuid,
        start_time: DateTime<Utc>,
        end_time: DateTime<Utc>,
    ) -> Result<f64, OEEError> {
        let (total, defects): (i64, i64) = sqlx::query_as(
            r#"
            SELECT 
                COUNT(*) as total,
                SUM(CASE WHEN is_defect THEN 1 ELSE 0 END) as defects
            FROM quality_records
            WHERE device_id = $1 AND timestamp >= $2 AND timestamp <= $3
            "#
        )
        .bind(device_id)
        .bind(start_time)
        .bind(end_time)
        .fetch_one(&self.db_pool)
        .await?;
        
        if total == 0 {
            return Ok(1.0);
        }
        
        let good_count = total - defects;
        Ok(good_count as f64 / total as f64)
    }
}

/// OEE 指标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OEEMetrics {
    pub device_id: Uuid,
    pub start_time: DateTime<Utc>,
    pub end_time: DateTime<Utc>,
    pub availability: f64,
    pub performance: f64,
    pub quality: f64,
    pub oee: f64,
}
```

---

## 3. 质量检测追踪

### 质量检测模型

```rust
/// 质量检测记录
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QualityInspection {
    pub id: Uuid,
    pub product_code: String,
    pub batch_id: Uuid,
    pub inspection_time: DateTime<Utc>,
    pub inspector: String,
    pub result: InspectionResult,
    pub defects: Vec<Defect>,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum InspectionResult {
    Pass,
    Fail,
    Rework,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Defect {
    pub defect_type: String,
    pub severity: Severity,
    pub description: String,
    pub image_url: Option<String>,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum Severity {
    Critical,
    Major,
    Minor,
}
```

### 质量检测追踪

```rust
pub struct QualityControlService {
    db_pool: sqlx::PgPool,
    kafka_producer: Arc<rdkafka::producer::FutureProducer>,
}

impl QualityControlService {
    /// 执行质量检测
    #[instrument(
        name = "quality.inspect",
        skip(self, inspection),
        fields(
            product_code = %inspection.product_code,
            batch_id = %inspection.batch_id
        )
    )]
    pub async fn perform_inspection(
        &self,
        mut inspection: QualityInspection,
    ) -> Result<QualityInspection, QualityError> {
        info!("Performing quality inspection");
        
        inspection.id = Uuid::new_v4();
        inspection.inspection_time = Utc::now();
        
        // 保存检测记录
        sqlx::query(
            r#"
            INSERT INTO quality_inspections (
                id, product_code, batch_id, inspection_time, 
                inspector, result, defects
            )
            VALUES ($1, $2, $3, $4, $5, $6, $7)
            "#
        )
        .bind(inspection.id)
        .bind(&inspection.product_code)
        .bind(inspection.batch_id)
        .bind(inspection.inspection_time)
        .bind(&inspection.inspector)
        .bind(format!("{:?}", inspection.result))
        .bind(serde_json::to_value(&inspection.defects)?)
        .execute(&self.db_pool)
        .await?;
        
        // 如果检测失败，发送告警
        if matches!(inspection.result, InspectionResult::Fail) {
            self.send_quality_alert(&inspection).await?;
        }
        
        // 发送质量事件
        self.publish_quality_event(&inspection).await?;
        
        info!(
            inspection_id = %inspection.id,
            result = ?inspection.result,
            defects_count = inspection.defects.len(),
            "Quality inspection completed"
        );
        
        Ok(inspection)
    }
    
    /// 发送质量告警
    #[instrument(skip(self, inspection))]
    async fn send_quality_alert(&self, inspection: &QualityInspection) -> Result<(), QualityError> {
        warn!(
            product_code = %inspection.product_code,
            batch_id = %inspection.batch_id,
            "Quality inspection failed - sending alert"
        );
        
        // 发送告警逻辑
        Ok(())
    }
    
    /// 发布质量事件
    #[instrument(skip(self, inspection))]
    async fn publish_quality_event(&self, inspection: &QualityInspection) -> Result<(), QualityError> {
        let event = serde_json::json!({
            "event_type": "quality_inspection",
            "inspection_id": inspection.id,
            "result": format!("{:?}", inspection.result),
            "timestamp": Utc::now(),
        });
        
        let payload = serde_json::to_string(&event)?;
        let record = rdkafka::producer::FutureRecord::to("quality-events")
            .payload(&payload)
            .key(&inspection.id.to_string());
        
        self.kafka_producer
            .send(record, std::time::Duration::from_secs(5))
            .await
            .map_err(|(e, _)| QualityError::KafkaError(e.to_string()))?;
        
        Ok(())
    }
}
```

---

## 4. 设备预测性维护

### 维护模型

```rust
/// 维护记录
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MaintenanceRecord {
    pub id: Uuid,
    pub device_id: Uuid,
    pub maintenance_type: MaintenanceType,
    pub scheduled_time: DateTime<Utc>,
    pub actual_time: Option<DateTime<Utc>>,
    pub technician: String,
    pub status: MaintenanceStatus,
    pub notes: Option<String>,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum MaintenanceType {
    Preventive,       // 预防性维护
    Predictive,       // 预测性维护
    Corrective,       // 纠正性维护
    Emergency,        // 紧急维护
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum MaintenanceStatus {
    Scheduled,
    InProgress,
    Completed,
    Cancelled,
}
```

### 预测性维护追踪

```rust
pub struct PredictiveMaintenanceService {
    db_pool: sqlx::PgPool,
    influxdb_client: influxdb::Client,
}

impl PredictiveMaintenanceService {
    /// 预测设备维护需求
    #[instrument(name = "maintenance.predict", skip(self))]
    pub async fn predict_maintenance_need(
        &self,
        device_id: Uuid,
    ) -> Result<MaintenancePrediction, MaintenanceError> {
        info!("Predicting maintenance need");
        
        // 1. 获取设备历史数据
        let historical_data = self.get_device_historical_data(device_id).await?;
        
        // 2. 分析振动数据
        let vibration_score = self.analyze_vibration(&historical_data)?;
        
        // 3. 分析温度数据
        let temperature_score = self.analyze_temperature(&historical_data)?;
        
        // 4. 分析运行时长
        let runtime_score = self.analyze_runtime(device_id).await?;
        
        // 5. 综合评分
        let overall_score = (vibration_score + temperature_score + runtime_score) / 3.0;
        
        // 6. 判断维护等级
        let urgency = if overall_score > 0.8 {
            MaintenanceUrgency::Urgent
        } else if overall_score > 0.6 {
            MaintenanceUrgency::High
        } else if overall_score > 0.4 {
            MaintenanceUrgency::Medium
        } else {
            MaintenanceUrgency::Low
        };
        
        info!(
            device_id = %device_id,
            overall_score = overall_score,
            urgency = ?urgency,
            "Maintenance prediction completed"
        );
        
        let prediction = MaintenancePrediction {
            device_id,
            predicted_at: Utc::now(),
            overall_score,
            vibration_score,
            temperature_score,
            runtime_score,
            urgency,
            recommended_date: self.calculate_recommended_date(urgency),
        };
        
        // 如果紧急，创建维护任务
        if matches!(urgency, MaintenanceUrgency::Urgent) {
            self.create_emergency_maintenance(device_id).await?;
        }
        
        Ok(prediction)
    }
    
    /// 分析振动数据
    fn analyze_vibration(&self, data: &[DeviceDataPoint]) -> Result<f64, MaintenanceError> {
        let vibration_values: Vec<f64> = data
            .iter()
            .flat_map(|dp| dp.metrics.iter())
            .filter(|m| m.name == "vibration")
            .map(|m| m.value)
            .collect();
        
        if vibration_values.is_empty() {
            return Ok(0.0);
        }
        
        let avg = vibration_values.iter().sum::<f64>() / vibration_values.len() as f64;
        let threshold = 2.0; // 正常阈值
        
        Ok((avg / threshold).min(1.0))
    }
    
    /// 分析温度数据
    fn analyze_temperature(&self, data: &[DeviceDataPoint]) -> Result<f64, MaintenanceError> {
        let temp_values: Vec<f64> = data
            .iter()
            .flat_map(|dp| dp.metrics.iter())
            .filter(|m| m.name == "temperature")
            .map(|m| m.value)
            .collect();
        
        if temp_values.is_empty() {
            return Ok(0.0);
        }
        
        let max_temp = temp_values.iter().fold(f64::NEG_INFINITY, |a, &b| a.max(b));
        let threshold = 80.0; // 正常阈值（摄氏度）
        
        Ok((max_temp / threshold).min(1.0))
    }
}

/// 维护预测结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MaintenancePrediction {
    pub device_id: Uuid,
    pub predicted_at: DateTime<Utc>,
    pub overall_score: f64,
    pub vibration_score: f64,
    pub temperature_score: f64,
    pub runtime_score: f64,
    pub urgency: MaintenanceUrgency,
    pub recommended_date: DateTime<Utc>,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum MaintenanceUrgency {
    Low,
    Medium,
    High,
    Urgent,
}
```

---

## 5. 能耗管理

### 能耗模型

```rust
/// 能耗记录
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnergyConsumption {
    pub device_id: Uuid,
    pub timestamp: DateTime<Utc>,
    pub power_kw: f64,
    pub energy_kwh: f64,
    pub cost: f64,
}
```

### 能耗监控追踪

```rust
pub struct EnergyManagementService {
    influxdb_client: influxdb::Client,
    db_pool: sqlx::PgPool,
}

impl EnergyManagementService {
    /// 记录能耗数据
    #[instrument(name = "energy.record", skip(self, consumption))]
    pub async fn record_energy_consumption(
        &self,
        consumption: EnergyConsumption,
    ) -> Result<(), EnergyError> {
        // 写入时序数据库
        let query = influxdb::Query::write_query(
            influxdb::Timestamp::Milliseconds(consumption.timestamp.timestamp_millis() as u128),
            "energy_consumption"
        )
        .add_field("power_kw", consumption.power_kw)
        .add_field("energy_kwh", consumption.energy_kwh)
        .add_field("cost", consumption.cost)
        .add_tag("device_id", consumption.device_id.to_string());
        
        self.influxdb_client.query(query).await?;
        
        info!(
            device_id = %consumption.device_id,
            power_kw = consumption.power_kw,
            "Energy consumption recorded"
        );
        
        Ok(())
    }
    
    /// 计算设备能耗
    #[instrument(name = "energy.calculate", skip(self))]
    pub async fn calculate_device_energy(
        &self,
        device_id: Uuid,
        start_time: DateTime<Utc>,
        end_time: DateTime<Utc>,
    ) -> Result<EnergyReport, EnergyError> {
        let query = format!(
            r#"SELECT SUM(energy_kwh), MAX(power_kw), MEAN(power_kw)
               FROM energy_consumption
               WHERE device_id = '{}'
                 AND time >= {}
                 AND time <= {}"#,
            device_id,
            start_time.timestamp_nanos(),
            end_time.timestamp_nanos()
        );
        
        // 查询 InfluxDB
        // ...
        
        info!(
            device_id = %device_id,
            "Energy calculation completed"
        );
        
        Ok(EnergyReport {
            device_id,
            start_time,
            end_time,
            total_energy_kwh: 0.0,
            max_power_kw: 0.0,
            avg_power_kw: 0.0,
            total_cost: 0.0,
        })
    }
}

/// 能耗报告
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnergyReport {
    pub device_id: Uuid,
    pub start_time: DateTime<Utc>,
    pub end_time: DateTime<Utc>,
    pub total_energy_kwh: f64,
    pub max_power_kw: f64,
    pub avg_power_kw: f64,
    pub total_cost: f64,
}
```

---

## 6. 仓储物流追踪

### 物料模型

```rust
/// 物料
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Material {
    pub id: Uuid,
    pub material_code: String,
    pub name: String,
    pub unit: String,
    pub stock_quantity: f64,
}

/// 物料移动
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MaterialMovement {
    pub id: Uuid,
    pub material_id: Uuid,
    pub from_location: String,
    pub to_location: String,
    pub quantity: f64,
    pub movement_type: MovementType,
    pub timestamp: DateTime<Utc>,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum MovementType {
    Inbound,      // 入库
    Outbound,     // 出库
    Transfer,     // 转移
    Return,       // 退货
}
```

### 物料追踪

```rust
pub struct WarehouseService {
    db_pool: sqlx::PgPool,
}

impl WarehouseService {
    /// 记录物料移动
    #[instrument(
        name = "warehouse.move_material",
        skip(self, movement),
        fields(
            material_id = %movement.material_id,
            from = %movement.from_location,
            to = %movement.to_location,
            quantity = movement.quantity
        )
    )]
    pub async fn record_material_movement(
        &self,
        mut movement: MaterialMovement,
    ) -> Result<MaterialMovement, WarehouseError> {
        movement.id = Uuid::new_v4();
        movement.timestamp = Utc::now();
        
        // 开始事务
        let mut tx = self.db_pool.begin().await?;
        
        // 插入移动记录
        sqlx::query(
            r#"
            INSERT INTO material_movements (
                id, material_id, from_location, to_location, 
                quantity, movement_type, timestamp
            )
            VALUES ($1, $2, $3, $4, $5, $6, $7)
            "#
        )
        .bind(movement.id)
        .bind(movement.material_id)
        .bind(&movement.from_location)
        .bind(&movement.to_location)
        .bind(movement.quantity)
        .bind(format!("{:?}", movement.movement_type))
        .bind(movement.timestamp)
        .execute(&mut *tx)
        .await?;
        
        // 更新库存
        match movement.movement_type {
            MovementType::Outbound => {
                self.decrease_stock(&mut tx, movement.material_id, movement.quantity).await?;
            }
            MovementType::Inbound => {
                self.increase_stock(&mut tx, movement.material_id, movement.quantity).await?;
            }
            _ => {}
        }
        
        tx.commit().await?;
        
        info!(movement_id = %movement.id, "Material movement recorded");
        
        Ok(movement)
    }
    
    async fn decrease_stock(
        &self,
        tx: &mut sqlx::Transaction<'_, sqlx::Postgres>,
        material_id: Uuid,
        quantity: f64,
    ) -> Result<(), WarehouseError> {
        sqlx::query(
            "UPDATE materials SET stock_quantity = stock_quantity - $1 WHERE id = $2"
        )
        .bind(quantity)
        .bind(material_id)
        .execute(&mut **tx)
        .await?;
        
        Ok(())
    }
    
    async fn increase_stock(
        &self,
        tx: &mut sqlx::Transaction<'_, sqlx::Postgres>,
        material_id: Uuid,
        quantity: f64,
    ) -> Result<(), WarehouseError> {
        sqlx::query(
            "UPDATE materials SET stock_quantity = stock_quantity + $1 WHERE id = $2"
        )
        .bind(quantity)
        .bind(material_id)
        .execute(&mut **tx)
        .await?;
        
        Ok(())
    }
}
```

---

## 7. MES 系统集成

### MES 工单模型

```rust
/// 生产工单
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkOrder {
    pub id: Uuid,
    pub order_number: String,
    pub product_code: String,
    pub quantity: i32,
    pub priority: Priority,
    pub status: WorkOrderStatus,
    pub start_time: Option<DateTime<Utc>>,
    pub end_time: Option<DateTime<Utc>>,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum Priority {
    Low,
    Normal,
    High,
    Urgent,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum WorkOrderStatus {
    Created,
    Scheduled,
    InProgress,
    Completed,
    Cancelled,
}
```

### 工单执行追踪

```rust
pub struct MESService {
    db_pool: sqlx::PgPool,
    kafka_producer: Arc<rdkafka::producer::FutureProducer>,
}

impl MESService {
    /// 启动工单
    #[instrument(name = "mes.start_work_order", skip(self))]
    pub async fn start_work_order(&self, order_id: Uuid) -> Result<WorkOrder, MESError> {
        info!("Starting work order");
        
        let mut order: WorkOrder = sqlx::query_as(
            "SELECT * FROM work_orders WHERE id = $1"
        )
        .bind(order_id)
        .fetch_one(&self.db_pool)
        .await?;
        
        order.status = WorkOrderStatus::InProgress;
        order.start_time = Some(Utc::now());
        
        sqlx::query(
            "UPDATE work_orders SET status = $1, start_time = $2 WHERE id = $3"
        )
        .bind(format!("{:?}", order.status))
        .bind(order.start_time)
        .bind(order.id)
        .execute(&self.db_pool)
        .await?;
        
        // 发送工单启动事件
        self.publish_work_order_event(&order, "started").await?;
        
        info!(order_id = %order.id, "Work order started");
        
        Ok(order)
    }
    
    /// 完成工单
    #[instrument(name = "mes.complete_work_order", skip(self))]
    pub async fn complete_work_order(&self, order_id: Uuid) -> Result<WorkOrder, MESError> {
        info!("Completing work order");
        
        let mut order: WorkOrder = sqlx::query_as(
            "SELECT * FROM work_orders WHERE id = $1"
        )
        .bind(order_id)
        .fetch_one(&self.db_pool)
        .await?;
        
        order.status = WorkOrderStatus::Completed;
        order.end_time = Some(Utc::now());
        
        sqlx::query(
            "UPDATE work_orders SET status = $1, end_time = $2 WHERE id = $3"
        )
        .bind(format!("{:?}", order.status))
        .bind(order.end_time)
        .bind(order.id)
        .execute(&self.db_pool)
        .await?;
        
        // 发送工单完成事件
        self.publish_work_order_event(&order, "completed").await?;
        
        info!(order_id = %order.id, "Work order completed");
        
        Ok(order)
    }
    
    async fn publish_work_order_event(
        &self,
        order: &WorkOrder,
        event_type: &str,
    ) -> Result<(), MESError> {
        let event = serde_json::json!({
            "event_type": event_type,
            "order_id": order.id,
            "order_number": order.order_number,
            "timestamp": Utc::now(),
        });
        
        let payload = serde_json::to_string(&event)?;
        let record = rdkafka::producer::FutureRecord::to("work-order-events")
            .payload(&payload)
            .key(&order.id.to_string());
        
        self.kafka_producer
            .send(record, std::time::Duration::from_secs(5))
            .await
            .map_err(|(e, _)| MESError::KafkaError(e.to_string()))?;
        
        Ok(())
    }
}
```

---

## 8. 时序数据处理

### 时序数据查询

```rust
use influxdb::{Client, Query, InfluxDbWriteable};

pub struct TimeSeriesService {
    influxdb_client: Client,
}

impl TimeSeriesService {
    /// 查询设备指标
    #[instrument(name = "timeseries.query_metrics", skip(self))]
    pub async fn query_device_metrics(
        &self,
        device_id: Uuid,
        metric_name: &str,
        start_time: DateTime<Utc>,
        end_time: DateTime<Utc>,
    ) -> Result<Vec<TimeSeriesPoint>, TimeSeriesError> {
        let query_str = format!(
            r#"SELECT time, value 
               FROM device_metrics 
               WHERE device_id = '{}'
                 AND metric_name = '{}'
                 AND time >= {}
                 AND time <= {}
               ORDER BY time ASC"#,
            device_id,
            metric_name,
            start_time.timestamp_nanos(),
            end_time.timestamp_nanos()
        );
        
        let read_query = Query::raw_read_query(&query_str);
        let result = self.influxdb_client.query(read_query).await?;
        
        // 解析结果
        let points = vec![]; // 解析逻辑
        
        info!(
            device_id = %device_id,
            metric_name = metric_name,
            points_count = points.len(),
            "Time series metrics queried"
        );
        
        Ok(points)
    }
}

#[derive(Debug, Clone)]
pub struct TimeSeriesPoint {
    pub timestamp: DateTime<Utc>,
    pub value: f64,
}
```

---

## 9. 实时告警

### 告警规则

```rust
pub struct AlertRule {
    pub id: Uuid,
    pub name: String,
    pub device_id: Option<Uuid>,
    pub metric_name: String,
    pub condition: AlertCondition,
    pub severity: AlertSeverity,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AlertCondition {
    GreaterThan(f64),
    LessThan(f64),
    Range { min: f64, max: f64 },
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum AlertSeverity {
    Info,
    Warning,
    Critical,
}
```

### 告警处理

```rust
pub struct AlertService {
    db_pool: sqlx::PgPool,
}

impl AlertService {
    /// 检查告警规则
    #[instrument(name = "alert.check_rules", skip(self, data_point))]
    pub async fn check_alert_rules(
        &self,
        data_point: &DeviceDataPoint,
    ) -> Result<Vec<Alert>, AlertError> {
        let rules = self.get_device_alert_rules(data_point.device_id).await?;
        let mut triggered_alerts = Vec::new();
        
        for rule in rules {
            for metric in &data_point.metrics {
                if metric.name == rule.metric_name {
                    if self.evaluate_condition(&rule.condition, metric.value) {
                        let alert = self.create_alert(&rule, metric.value).await?;
                        triggered_alerts.push(alert);
                    }
                }
            }
        }
        
        if !triggered_alerts.is_empty() {
            info!(
                device_id = %data_point.device_id,
                alerts_count = triggered_alerts.len(),
                "Alerts triggered"
            );
        }
        
        Ok(triggered_alerts)
    }
    
    fn evaluate_condition(&self, condition: &AlertCondition, value: f64) -> bool {
        match condition {
            AlertCondition::GreaterThan(threshold) => value > *threshold,
            AlertCondition::LessThan(threshold) => value < *threshold,
            AlertCondition::Range { min, max } => value < *min || value > *max,
        }
    }
    
    async fn create_alert(&self, rule: &AlertRule, value: f64) -> Result<Alert, AlertError> {
        let alert = Alert {
            id: Uuid::new_v4(),
            rule_id: rule.id,
            device_id: rule.device_id,
            metric_name: rule.metric_name.clone(),
            value,
            severity: rule.severity,
            timestamp: Utc::now(),
            acknowledged: false,
        };
        
        sqlx::query(
            r#"
            INSERT INTO alerts (
                id, rule_id, device_id, metric_name, value, 
                severity, timestamp, acknowledged
            )
            VALUES ($1, $2, $3, $4, $5, $6, $7, $8)
            "#
        )
        .bind(alert.id)
        .bind(alert.rule_id)
        .bind(alert.device_id)
        .bind(&alert.metric_name)
        .bind(alert.value)
        .bind(format!("{:?}", alert.severity))
        .bind(alert.timestamp)
        .bind(alert.acknowledged)
        .execute(&self.db_pool)
        .await?;
        
        Ok(alert)
    }
}

#[derive(Debug, Clone)]
pub struct Alert {
    pub id: Uuid,
    pub rule_id: Uuid,
    pub device_id: Option<Uuid>,
    pub metric_name: String,
    pub value: f64,
    pub severity: AlertSeverity,
    pub timestamp: DateTime<Utc>,
    pub acknowledged: bool,
}
```

---

## 10. 完整示例

### main.rs

```rust
use opentelemetry::global;
use tracing_subscriber::layer::SubscriberExt;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化追踪
    let tracer = init_tracer()?;
    global::set_tracer_provider(tracer);
    
    // 初始化日志
    let telemetry = tracing_opentelemetry::layer().with_tracer(tracer);
    let subscriber = tracing_subscriber::registry()
        .with(telemetry)
        .with(tracing_subscriber::fmt::layer());
    tracing::subscriber::set_global_default(subscriber)?;
    
    info!("Starting Smart Manufacturing System");
    
    // 初始化服务
    let db_pool = init_db_pool().await?;
    let influxdb_client = influxdb::Client::new("http://localhost:8086", "manufacturing");
    let kafka_producer = Arc::new(init_kafka_producer()?);
    
    // 启动数据采集
    let collector = DeviceDataCollector::new().await?;
    tokio::spawn(async move {
        collector.start_collecting().await
    });
    
    // 启动OEE计算任务
    let oee_service = Arc::new(OEECalculationService { db_pool: db_pool.clone() });
    tokio::spawn(async move {
        loop {
            // 每小时计算一次OEE
            tokio::time::sleep(std::time::Duration::from_secs(3600)).await;
            // 计算所有设备OEE
        }
    });
    
    // 启动预测性维护任务
    let maintenance_service = Arc::new(PredictiveMaintenanceService {
        db_pool: db_pool.clone(),
        influxdb_client: influxdb_client.clone(),
    });
    tokio::spawn(async move {
        loop {
            // 每天执行一次预测
            tokio::time::sleep(std::time::Duration::from_secs(86400)).await;
            // 预测维护需求
        }
    });
    
    info!("All services started successfully");
    
    // 保持运行
    tokio::signal::ctrl_c().await?;
    
    info!("Shutting down");
    global::shutdown_tracer_provider();
    
    Ok(())
}

fn init_tracer() -> Result<opentelemetry_sdk::trace::TracerProvider, Box<dyn std::error::Error>> {
    use opentelemetry_otlp::WithExportConfig;
    
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    Ok(tracer)
}
```

---

## 总结

本文档展示了智能制造场景的完整可观测性实现：

1. ✅ **IoT 数据采集**: MQTT + InfluxDB 时序数据库
2. ✅ **生产线监控**: OEE 计算和性能分析
3. ✅ **质量追溯**: 完整的质量检测追踪
4. ✅ **预测性维护**: 基于数据的设备维护预测
5. ✅ **能耗管理**: 能源消耗监控和优化
6. ✅ **MES 集成**: 生产工单全生命周期追踪
7. ✅ **实时告警**: 异常检测和告警通知

通过本案例，您可以构建生产级的工业IoT可观测性系统。

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-08  
**维护者**: OTLP Rust Team  
**许可证**: MIT OR Apache-2.0
