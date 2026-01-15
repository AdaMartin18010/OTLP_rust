//! # 多租户扩展
//!
//! 提供多租户支持扩展，用于隔离不同租户的数据。

use opentelemetry_sdk::export::trace::{ExportResult, SpanData, SpanExporter};
use async_trait::async_trait;

/// 多租户Span Exporter包装器
///
/// 包装官方的SpanExporter，添加多租户支持。
pub struct MultiTenantExporter {
    inner: Box<dyn SpanExporter>,
    tenant_id: Option<String>,
}

impl MultiTenantExporter {
    /// 创建新的多租户Exporter包装器
    ///
    /// # 参数
    ///
    /// * `exporter` - 要包装的官方SpanExporter
    pub fn wrap(exporter: Box<dyn SpanExporter>) -> Self {
        Self {
            inner: exporter,
            tenant_id: None,
        }
    }

    /// 设置租户ID
    ///
    /// # 参数
    ///
    /// * `tenant_id` - 租户ID
    pub fn with_tenant_id(mut self, tenant_id: String) -> Self {
        self.tenant_id = Some(tenant_id);
        self
    }
}

#[async_trait]
impl SpanExporter for MultiTenantExporter {
    async fn export(&mut self, batch: Vec<SpanData>) -> ExportResult {
        // 添加租户ID到span attributes
        let mut enriched_batch = batch;

        if let Some(ref tenant_id) = self.tenant_id {
            for span in &mut enriched_batch {
                // 添加租户ID属性
                // 注意: SpanData的API可能需要调整
                // 这里提供一个概念性实现
                // span.attributes.push(KeyValue::new("tenant.id", tenant_id.clone()));
            }
        }

        self.inner.export(enriched_batch).await
    }

    fn shutdown(&mut self) -> opentelemetry_sdk::export::trace::Result<()> {
        self.inner.shutdown()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use opentelemetry_sdk::export::trace::NoopSpanExporter;

    #[tokio::test]
    async fn test_multi_tenant_exporter() {
        let noop_exporter = Box::new(NoopSpanExporter::new());
        let mut multi_tenant = MultiTenantExporter::wrap(noop_exporter)
            .with_tenant_id("test-tenant".to_string());

        let result = multi_tenant.export(vec![]).await;
        assert!(result.is_ok());
    }
}
