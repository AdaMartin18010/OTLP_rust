//! OpenTelemetry Collector 配置生成器
//!
//! 生成符合生产环境最佳实践的 Collector 配置文件。
//! 遵循 OpenTelemetry Collector 1.0 标准（2025年发布）。
//!
//! 参考:
//! - https://opentelemetry.io/docs/security/config-best-practices/
//! - https://oneuptime.com/blog/post/2026-01-25-opentelemetry-collector-production-setup/view

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Collector 配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CollectorConfig {
    /// 接收器配置
    pub receivers: ReceiversConfig,
    /// 处理器配置
    pub processors: ProcessorsConfig,
    /// 导出器配置
    pub exporters: ExportersConfig,
    /// 扩展配置
    pub extensions: ExtensionsConfig,
    /// 服务配置
    pub service: ServiceConfig,
}

impl CollectorConfig {
    /// 创建生产环境配置
    pub fn production() -> Self {
        Self {
            receivers: ReceiversConfig::default(),
            processors: ProcessorsConfig::production(),
            exporters: ExportersConfig::default(),
            extensions: ExtensionsConfig::production(),
            service: ServiceConfig::production(),
        }
    }

    /// 创建开发环境配置
    pub fn development() -> Self {
        Self {
            receivers: ReceiversConfig::default(),
            processors: ProcessorsConfig::development(),
            exporters: ExportersConfig::default(),
            extensions: ExtensionsConfig::development(),
            service: ServiceConfig::development(),
        }
    }

    /// 启用安全模式（TLS + 认证）
    pub fn with_security(mut self) -> Self {
        self.receivers.otlp.protocols.grpc.tls = Some(TlsConfig {
            cert_file: "/certs/server.crt".to_string(),
            key_file: "/certs/server.key".to_string(),
            client_ca_file: Some("/certs/ca.crt".to_string()),
        });
        self
    }

    /// 添加 OTLP HTTP 导出器
    pub fn with_otlp_http_exporter(
        mut self,
        name: &str,
        endpoint: &str,
        api_key: Option<&str>,
    ) -> Self {
        let mut headers = HashMap::new();
        if let Some(key) = api_key {
            headers.insert("Authorization".to_string(), format!("Bearer {}", key));
        }

        self.exporters.otlphttp.insert(
            name.to_string(),
            OtlpHttpExporterConfig {
                endpoint: endpoint.to_string(),
                headers,
                retry_on_failure: RetryConfig::default(),
                sending_queue: QueueConfig::default(),
            },
        );
        self
    }

    /// 添加调试导出器
    pub fn with_debug_exporter(mut self, verbosity: &str) -> Self {
        self.exporters.debug = Some(DebugExporterConfig {
            verbosity: verbosity.to_string(),
            sampling_initial: 5,
            sampling_thereafter: 200,
        });
        self
    }

    /// 转换为 YAML 格式
    pub fn to_yaml(&self) -> Result<String, serde_yaml::Error> {
        serde_yaml::to_string(self)
    }
}

/// 接收器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReceiversConfig {
    pub otlp: OtlpReceiverConfig,
}

impl Default for ReceiversConfig {
    fn default() -> Self {
        Self {
            otlp: OtlpReceiverConfig::default(),
        }
    }
}

/// OTLP 接收器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OtlpReceiverConfig {
    pub protocols: OtlpProtocolsConfig,
}

impl Default for OtlpReceiverConfig {
    fn default() -> Self {
        Self {
            protocols: OtlpProtocolsConfig::default(),
        }
    }
}

/// OTLP 协议配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OtlpProtocolsConfig {
    pub grpc: GrpcConfig,
    pub http: HttpConfig,
}

impl Default for OtlpProtocolsConfig {
    fn default() -> Self {
        Self {
            grpc: GrpcConfig::default(),
            http: HttpConfig::default(),
        }
    }
}

/// gRPC 配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GrpcConfig {
    /// 端点地址（注意：生产环境使用 localhost 或具体 IP，而非 0.0.0.0）
    pub endpoint: String,
    /// 最大接收消息大小 (MB)
    pub max_recv_msg_size_mib: u32,
    /// TLS 配置
    pub tls: Option<TlsConfig>,
}

impl Default for GrpcConfig {
    fn default() -> Self {
        Self {
            endpoint: "localhost:4317".to_string(),
            max_recv_msg_size_mib: 16,
            tls: None,
        }
    }
}

/// HTTP 配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HttpConfig {
    pub endpoint: String,
    pub cors: Option<CorsConfig>,
}

impl Default for HttpConfig {
    fn default() -> Self {
        Self {
            endpoint: "localhost:4318".to_string(),
            cors: Some(CorsConfig::default()),
        }
    }
}

/// CORS 配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CorsConfig {
    pub allowed_origins: Vec<String>,
}

impl Default for CorsConfig {
    fn default() -> Self {
        Self {
            allowed_origins: vec!["https://your-domain.com".to_string()],
        }
    }
}

/// TLS 配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TlsConfig {
    pub cert_file: String,
    pub key_file: String,
    pub client_ca_file: Option<String>,
}

/// 处理器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProcessorsConfig {
    /// 内存限制器（防止 OOM）
    pub memory_limiter: Option<MemoryLimiterConfig>,
    /// 批处理器
    pub batch: Option<BatchConfig>,
    /// 资源属性添加
    pub resource: Option<ResourceProcessorConfig>,
    /// 数据脱敏
    pub redaction: Option<RedactionConfig>,
    /// 过滤器
    pub filter: Option<FilterConfig>,
}

impl ProcessorsConfig {
    /// 生产环境配置
    pub fn production() -> Self {
        Self {
            memory_limiter: Some(MemoryLimiterConfig::default()),
            batch: Some(BatchConfig::default()),
            resource: Some(ResourceProcessorConfig::default()),
            redaction: None,
            filter: None,
        }
    }

    /// 开发环境配置
    pub fn development() -> Self {
        Self {
            memory_limiter: None,
            batch: Some(BatchConfig::development()),
            resource: Some(ResourceProcessorConfig::default()),
            redaction: None,
            filter: None,
        }
    }
}

/// 内存限制器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemoryLimiterConfig {
    /// 检查间隔
    pub check_interval: String,
    /// 内存限制 (MB)
    pub limit_mib: u32,
    /// 峰值限制 (MB)
    pub spike_limit_mib: u32,
}

impl Default for MemoryLimiterConfig {
    fn default() -> Self {
        Self {
            check_interval: "5s".to_string(),
            limit_mib: 1800,
            spike_limit_mib: 500,
        }
    }
}

/// 批处理器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchConfig {
    /// 发送批次大小
    pub send_batch_size: u32,
    /// 最大批次大小
    pub send_batch_max_size: u32,
    /// 超时时间
    pub timeout: String,
}

impl Default for BatchConfig {
    fn default() -> Self {
        Self {
            send_batch_size: 1024,
            send_batch_max_size: 2048,
            timeout: "5s".to_string(),
        }
    }
}

impl BatchConfig {
    /// 开发环境配置
    pub fn development() -> Self {
        Self {
            send_batch_size: 256,
            send_batch_max_size: 512,
            timeout: "1s".to_string(),
        }
    }
}

/// 资源处理器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceProcessorConfig {
    pub attributes: Vec<ResourceAttribute>,
}

impl Default for ResourceProcessorConfig {
    fn default() -> Self {
        Self {
            attributes: vec![
                ResourceAttribute {
                    key: "deployment.environment".to_string(),
                    value: "production".to_string(),
                    action: "upsert".to_string(),
                },
                ResourceAttribute {
                    key: "collector.version".to_string(),
                    value: "1.0.0".to_string(),
                    action: "insert".to_string(),
                },
            ],
        }
    }
}

/// 资源属性
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceAttribute {
    pub key: String,
    pub value: String,
    pub action: String,
}

/// 脱敏配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RedactionConfig {
    pub allow_all_keys: bool,
    pub allowed_keys: Vec<String>,
    pub ignored_keys: Vec<String>,
    pub blocked_values: Vec<String>,
    pub summary: String,
}

/// 过滤器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FilterConfig {
    pub error_mode: String,
    pub traces: FilterTracesConfig,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FilterTracesConfig {
    pub span: Vec<String>,
}

/// 导出器配置
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct ExportersConfig {
    /// OTLP HTTP 导出器
    #[serde(skip_serializing_if = "HashMap::is_empty", default)]
    pub otlphttp: HashMap<String, OtlpHttpExporterConfig>,
    /// 调试导出器
    #[serde(skip_serializing_if = "Option::is_none")]
    pub debug: Option<DebugExporterConfig>,
}

/// OTLP HTTP 导出器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OtlpHttpExporterConfig {
    pub endpoint: String,
    #[serde(skip_serializing_if = "HashMap::is_empty", default)]
    pub headers: HashMap<String, String>,
    pub retry_on_failure: RetryConfig,
    pub sending_queue: QueueConfig,
}

/// 重试配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RetryConfig {
    pub enabled: bool,
    pub initial_interval: String,
    pub max_interval: String,
    pub max_elapsed_time: String,
}

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            initial_interval: "5s".to_string(),
            max_interval: "30s".to_string(),
            max_elapsed_time: "300s".to_string(),
        }
    }
}

/// 队列配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QueueConfig {
    pub enabled: bool,
    pub num_consumers: u32,
    pub queue_size: u32,
}

impl Default for QueueConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            num_consumers: 10,
            queue_size: 5000,
        }
    }
}

/// 调试导出器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DebugExporterConfig {
    pub verbosity: String,
    pub sampling_initial: u32,
    pub sampling_thereafter: u32,
}

/// 扩展配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExtensionsConfig {
    /// 健康检查
    pub health_check: HealthCheckConfig,
    /// zpages（调试页面）
    pub zpages: ZpagesConfig,
    /// pprof（性能分析）
    pub pprof: PprofConfig,
}

impl ExtensionsConfig {
    /// 生产环境配置
    pub fn production() -> Self {
        Self {
            health_check: HealthCheckConfig::default(),
            zpages: ZpagesConfig::default(),
            pprof: PprofConfig::default(),
        }
    }

    /// 开发环境配置
    pub fn development() -> Self {
        Self {
            health_check: HealthCheckConfig::default(),
            zpages: ZpagesConfig::default(),
            pprof: PprofConfig::default(),
        }
    }
}

/// 健康检查配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HealthCheckConfig {
    pub endpoint: String,
    pub path: String,
}

impl Default for HealthCheckConfig {
    fn default() -> Self {
        Self {
            endpoint: "localhost:13133".to_string(),
            path: "/health".to_string(),
        }
    }
}

/// zpages 配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ZpagesConfig {
    pub endpoint: String,
}

impl Default for ZpagesConfig {
    fn default() -> Self {
        Self {
            endpoint: "localhost:55679".to_string(),
        }
    }
}

/// pprof 配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PprofConfig {
    pub endpoint: String,
}

impl Default for PprofConfig {
    fn default() -> Self {
        Self {
            endpoint: "localhost:1777".to_string(),
        }
    }
}

/// 服务配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceConfig {
    /// 使用的扩展
    pub extensions: Vec<String>,
    /// 管道配置
    pub pipelines: PipelinesConfig,
    /// 遥测配置
    pub telemetry: TelemetryConfig,
}

impl ServiceConfig {
    /// 生产环境配置
    pub fn production() -> Self {
        Self {
            extensions: vec!["health_check".to_string(), "zpages".to_string(), "pprof".to_string()],
            pipelines: PipelinesConfig::production(),
            telemetry: TelemetryConfig::default(),
        }
    }

    /// 开发环境配置
    pub fn development() -> Self {
        Self {
            extensions: vec!["health_check".to_string(), "zpages".to_string()],
            pipelines: PipelinesConfig::development(),
            telemetry: TelemetryConfig::default(),
        }
    }
}

/// 管道配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PipelinesConfig {
    pub traces: PipelineConfig,
    pub metrics: PipelineConfig,
    pub logs: PipelineConfig,
}

impl PipelinesConfig {
    /// 生产环境配置
    pub fn production() -> Self {
        Self {
            traces: PipelineConfig {
                receivers: vec!["otlp".to_string()],
                processors: vec!["memory_limiter".to_string(), "batch".to_string(), "resource".to_string()],
                exporters: vec!["otlphttp".to_string()],
            },
            metrics: PipelineConfig {
                receivers: vec!["otlp".to_string()],
                processors: vec!["memory_limiter".to_string(), "batch".to_string(), "resource".to_string()],
                exporters: vec!["otlphttp".to_string()],
            },
            logs: PipelineConfig {
                receivers: vec!["otlp".to_string()],
                processors: vec!["memory_limiter".to_string(), "batch".to_string(), "resource".to_string()],
                exporters: vec!["otlphttp".to_string()],
            },
        }
    }

    /// 开发环境配置
    pub fn development() -> Self {
        Self {
            traces: PipelineConfig {
                receivers: vec!["otlp".to_string()],
                processors: vec!["batch".to_string(), "resource".to_string()],
                exporters: vec!["debug".to_string()],
            },
            metrics: PipelineConfig {
                receivers: vec!["otlp".to_string()],
                processors: vec!["batch".to_string()],
                exporters: vec!["debug".to_string()],
            },
            logs: PipelineConfig {
                receivers: vec!["otlp".to_string()],
                processors: vec!["batch".to_string()],
                exporters: vec!["debug".to_string()],
            },
        }
    }
}

/// 单个管道配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PipelineConfig {
    pub receivers: Vec<String>,
    pub processors: Vec<String>,
    pub exporters: Vec<String>,
}

/// 遥测配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TelemetryConfig {
    pub logs: LogTelemetryConfig,
    pub metrics: MetricsTelemetryConfig,
}

impl Default for TelemetryConfig {
    fn default() -> Self {
        Self {
            logs: LogTelemetryConfig::default(),
            metrics: MetricsTelemetryConfig::default(),
        }
    }
}

/// 日志遥测配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogTelemetryConfig {
    pub level: String,
    pub initial_fields: HashMap<String, String>,
}

impl Default for LogTelemetryConfig {
    fn default() -> Self {
        let mut fields = HashMap::new();
        fields.insert("service".to_string(), "otel-collector".to_string());
        
        Self {
            level: "info".to_string(),
            initial_fields: fields,
        }
    }
}

/// 指标遥测配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MetricsTelemetryConfig {
    pub level: String,
    pub address: String,
}

impl Default for MetricsTelemetryConfig {
    fn default() -> Self {
        Self {
            level: "detailed".to_string(),
            address: "localhost:8888".to_string(),
        }
    }
}

/// Kubernetes 部署配置生成器
pub mod k8s {
    /// 生成 DaemonSet 配置
    pub fn generate_daemonset_config() -> String {
        r#"apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: otel-collector
  namespace: observability
spec:
  selector:
    matchLabels:
      name: collector
  template:
    metadata:
      labels:
        name: collector
    spec:
      containers:
        - name: collector
          image: otel/opentelemetry-collector:0.147.0
          ports:
            - containerPort: 4317
              hostPort: 4317
              protocol: TCP
              name: otlp-grpc
            - containerPort: 4318
              hostPort: 4318
              protocol: TCP
              name: otlp-http
          env:
            - name: MY_POD_IP
              valueFrom:
                fieldRef:
                  fieldPath: status.podIP
          resources:
            limits:
              memory: "2Gi"
              cpu: "1000m"
            requests:
              memory: "512Mi"
              cpu: "100m"
          volumeMounts:
            - name: config
              mountPath: /etc/otelcol
      volumes:
        - name: config
          configMap:
            name: otel-collector-config
"#.to_string()
    }

    /// 生成 HorizontalPodAutoscaler 配置
    pub fn generate_hpa_config() -> String {
        r#"apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: otel-collector-hpa
  namespace: observability
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: otel-collector
  minReplicas: 3
  maxReplicas: 10
  metrics:
    - type: Resource
      resource:
        name: cpu
        target:
          type: Utilization
          averageUtilization: 70
    - type: Resource
      resource:
        name: memory
        target:
          type: Utilization
          averageUtilization: 80
"#.to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_production_config() {
        let config = CollectorConfig::production();
        assert!(config.processors.memory_limiter.is_some());
        assert_eq!(config.service.extensions.len(), 3);
    }

    #[test]
    fn test_development_config() {
        let config = CollectorConfig::development();
        assert!(config.processors.memory_limiter.is_none());
    }

    #[test]
    fn test_config_to_yaml() {
        let config = CollectorConfig::development();
        let yaml = config.to_yaml();
        assert!(yaml.is_ok());
        
        let yaml_str = yaml.unwrap();
        assert!(yaml_str.contains("receivers:"));
        assert!(yaml_str.contains("processors:"));
        assert!(yaml_str.contains("exporters:"));
    }

    #[test]
    fn test_with_security() {
        let config = CollectorConfig::production().with_security();
        assert!(config.receivers.otlp.protocols.grpc.tls.is_some());
    }

    #[test]
    fn test_with_otlp_http_exporter() {
        let config = CollectorConfig::production()
            .with_otlp_http_exporter("backend", "https://api.example.com", Some("token123"));
        
        assert!(config.exporters.otlphttp.contains_key("backend"));
    }

    #[test]
    fn test_k8s_daemonset_config() {
        let config = k8s::generate_daemonset_config();
        assert!(config.contains("DaemonSet"));
        assert!(config.contains("otel-collector"));
        assert!(config.contains("4317"));
    }
}
