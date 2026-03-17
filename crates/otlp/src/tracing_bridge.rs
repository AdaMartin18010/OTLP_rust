//! Tracing-OpenTelemetry 桥接层
//!
//! 实现现代化的遥测基础设施，遵循 OpenTelemetry Rust 0.31.0 最佳实践：
//! - 使用 `tracing` crate 作为基础设施
//! - 通过 `tracing-opentelemetry` 桥接到 OTLP
//! - 支持 W3C Trace Context 传播
//! - 内部线程管理（无需显式 Runtime）
//!
//! 参考: https://opentelemetry.io/docs/languages/rust/

use opentelemetry::Context;
use opentelemetry_otlp::{SpanExporter, WithExportConfig};
use opentelemetry_sdk::propagation::TraceContextPropagator;
use opentelemetry_sdk::resource::Resource;
use opentelemetry_sdk::trace::SdkTracerProvider;
use std::time::Duration;

/// 遥测配置
#[derive(Debug, Clone)]
pub struct TelemetryConfig {
    /// 服务名称
    pub service_name: String,
    /// 服务版本
    pub service_version: String,
    /// 部署环境
    pub environment: String,
    /// OTLP 端点
    pub otlp_endpoint: String,
    /// 使用 gRPC (true) 或 HTTP (false)
    pub use_grpc: bool,
    /// 采样率 (0.0 - 1.0)
    pub sampling_ratio: f64,
}

impl Default for TelemetryConfig {
    fn default() -> Self {
        Self {
            service_name: "otlp-rust-service".to_string(),
            service_version: env!("CARGO_PKG_VERSION").to_string(),
            environment: std::env::var("DEPLOYMENT_ENVIRONMENT")
                .unwrap_or_else(|_| "development".to_string()),
            otlp_endpoint: std::env::var("OTEL_EXPORTER_OTLP_ENDPOINT")
                .unwrap_or_else(|_| "http://localhost:4317".to_string()),
            use_grpc: true,
            sampling_ratio: std::env::var("OTEL_TRACES_SAMPLER_ARG")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(1.0),
        }
    }
}

/// 遥测运行时
///
/// 管理所有 OpenTelemetry 组件的生命周期
#[allow(dead_code)]
pub struct TelemetryRuntime {
    tracer_provider: SdkTracerProvider,
    config: TelemetryConfig,
}

impl TelemetryRuntime {
    /// 初始化遥测系统
    pub fn init(config: TelemetryConfig) -> Result<Self, crate::error::OtlpError> {
        // 设置全局传播器（W3C Trace Context）
        opentelemetry::global::set_text_map_propagator(TraceContextPropagator::new());

        // 构建资源
        let resource = Self::build_resource(&config);

        // 初始化 Tracer Provider
        let tracer_provider = Self::init_tracer_provider(&config, resource)?;

        // 创建 runtime
        let runtime = Self {
            tracer_provider,
            config,
        };

        Ok(runtime)
    }

    /// 构建资源属性
    fn build_resource(config: &TelemetryConfig) -> Resource {
        let _host_name = hostname::get()
            .map(|h| h.to_string_lossy().to_string())
            .unwrap_or_else(|_| "unknown".to_string());

        Resource::builder()
            .with_service_name(config.service_name.clone())
            .build()
    }

    /// 初始化 Tracer Provider
    fn init_tracer_provider(
        config: &TelemetryConfig,
        resource: Resource,
    ) -> Result<SdkTracerProvider, crate::error::OtlpError> {
        // 使用 HTTP 导出器（ tonic 需要额外配置）
        let exporter = SpanExporter::builder()
            .with_http()
            .with_endpoint(format!("{}/v1/traces", config.otlp_endpoint))
            .with_timeout(Duration::from_secs(10))
            .build()
            .map_err(|e| crate::error::OtlpError::internal(format!("Failed to create exporter: {}", e)))?;

        let provider = SdkTracerProvider::builder()
            .with_batch_exporter(exporter)
            .with_resource(resource)
            .build();

        opentelemetry::global::set_tracer_provider(provider.clone());

        Ok(provider)
    }

    /// 获取 tracer
    pub fn tracer(&self, name: &'static str) -> opentelemetry::global::BoxedTracer {
        opentelemetry::global::tracer(name)
    }

    /// 创建 tracing 层
    ///
    /// 使用此层初始化 tracing 订阅者
    pub fn create_tracing_layer(
        &self,
    ) -> tracing_opentelemetry::OpenTelemetryLayer<tracing_subscriber::Registry, opentelemetry::global::BoxedTracer>
    {
        let tracer = self.tracer("tracing-bridge");
        tracing_opentelemetry::layer().with_tracer(tracer)
    }

    /// 优雅关闭
    pub fn shutdown(&self) -> Result<(), crate::error::OtlpError> {
        self.tracer_provider
            .shutdown()
            .map_err(|e| crate::error::OtlpError::internal(format!("Shutdown failed: {}", e)))?;

        Ok(())
    }
}

impl Drop for TelemetryRuntime {
    fn drop(&mut self) {
        let _ = self.shutdown();
    }
}

/// HTTP 头注入器
pub struct HeaderInjector<'a>(pub &'a mut http::HeaderMap);

impl<'a> opentelemetry::propagation::Injector for HeaderInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        if let Ok(name) = http::HeaderName::from_bytes(key.as_bytes()) {
            if let Ok(val) = http::HeaderValue::from_str(&value) {
                self.0.insert(name, val);
            }
        }
    }
}

/// HTTP 头提取器
pub struct HeaderExtractor<'a>(pub &'a http::HeaderMap);

impl<'a> opentelemetry::propagation::Extractor for HeaderExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.0.get(key).and_then(|v: &http::HeaderValue| v.to_str().ok())
    }

    fn keys(&self) -> Vec<&str> {
        self.0.keys().map(|k: &http::HeaderName| k.as_str()).collect()
    }
}

/// 从 HTTP 请求中提取父上下文
pub fn extract_parent_context(headers: &http::HeaderMap) -> Context {
    opentelemetry::global::get_text_map_propagator(|propagator| {
        propagator.extract(&HeaderExtractor(headers))
    })
}

/// 将当前上下文注入 HTTP 头
pub fn inject_context(headers: &mut http::HeaderMap) {
    opentelemetry::global::get_text_map_propagator(|propagator| {
        propagator.inject_context(&Context::current(), &mut HeaderInjector(headers));
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_telemetry_config_default() {
        let config = TelemetryConfig::default();
        assert!(!config.service_name.is_empty());
        assert!(!config.otlp_endpoint.is_empty());
    }

    #[test]
    fn test_header_injector() {
        let mut headers = http::HeaderMap::new();
        let mut injector = HeaderInjector(&mut headers);

        opentelemetry::propagation::Injector::set(
            &mut injector,
            "test-key",
            "test-value".to_string(),
        );

        assert_eq!(
            headers.get("test-key").unwrap().to_str().unwrap(),
            "test-value"
        );
    }

    #[test]
    fn test_header_extractor() {
        use opentelemetry::propagation::Extractor;
        
        let mut headers = http::HeaderMap::new();
        headers.insert(
            "traceparent",
            "00-12345678901234567890123456789012-1234567890123456-01"
                .parse()
                .unwrap(),
        );

        let extractor = HeaderExtractor(&headers);
        assert_eq!(
            extractor.get("traceparent"),
            Some("00-12345678901234567890123456789012-1234567890123456-01")
        );
    }
}
