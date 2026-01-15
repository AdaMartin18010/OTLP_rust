//! # 增强的Exporter包装器
//!
//! 提供增强的Exporter包装器，支持扩展功能。

// 注意: opentelemetry_sdk 0.31版本中，SpanExporter位于export::trace模块
use opentelemetry_sdk::export::trace::SpanExporter;
use crate::extensions::simd::SimdSpanExporter;
use crate::extensions::tracezip::TracezipSpanExporter;
use crate::extensions::enterprise::{MultiTenantExporter, ComplianceExporter};
use crate::extensions::performance::{BatchOptimizedExporter, ConnectionPoolExporter};

/// 增强的Exporter构建器
pub struct EnhancedExporter {
    exporter: Option<Box<dyn SpanExporter>>,
    simd_enabled: bool,
    tracezip_enabled: bool,
    multi_tenant_enabled: bool,
    compliance_enabled: bool,
    batch_optimization_enabled: bool,
    connection_pool_enabled: bool,
    tenant_id: Option<String>,
}

impl EnhancedExporter {
    /// 创建新的增强Exporter构建器
    pub fn new() -> Self {
        Self {
            exporter: None,
            simd_enabled: false,
            tracezip_enabled: false,
            multi_tenant_enabled: false,
            compliance_enabled: false,
            batch_optimization_enabled: false,
            connection_pool_enabled: false,
            tenant_id: None,
        }
    }

    /// 设置基础Exporter
    ///
    /// # 参数
    ///
    /// * `exporter` - 官方的SpanExporter
    pub fn with_exporter(mut self, exporter: Box<dyn SpanExporter>) -> Self {
        self.exporter = Some(exporter);
        self
    }

    /// 启用SIMD优化
    pub fn with_simd_optimization(mut self, enabled: bool) -> Self {
        self.simd_enabled = enabled;
        self
    }

    /// 启用Tracezip压缩
    pub fn with_tracezip_compression(mut self, enabled: bool) -> Self {
        self.tracezip_enabled = enabled;
        self
    }

    /// 启用多租户支持
    pub fn with_multi_tenant(mut self, enabled: bool) -> Self {
        self.multi_tenant_enabled = enabled;
        self
    }

    /// 设置租户ID
    pub fn with_tenant_id(mut self, tenant_id: String) -> Self {
        self.tenant_id = Some(tenant_id);
        self.multi_tenant_enabled = true;
        self
    }

    /// 启用合规管理
    pub fn with_compliance(mut self, enabled: bool) -> Self {
        self.compliance_enabled = enabled;
        self
    }

    /// 启用批量处理优化
    pub fn with_batch_optimization(mut self, enabled: bool) -> Self {
        self.batch_optimization_enabled = enabled;
        self
    }

    /// 启用连接池优化
    pub fn with_connection_pool(mut self, enabled: bool) -> Self {
        self.connection_pool_enabled = enabled;
        self
    }

    /// 构建增强的Exporter
    ///
    /// # 返回
    ///
    /// 返回应用了所有扩展的Exporter
    pub fn build(self) -> Result<Box<dyn SpanExporter>, Box<dyn std::error::Error>> {
        let mut exporter = self.exporter.ok_or("Exporter not set")?;

        // 按顺序应用扩展（从内到外）
        // 1. 连接池（最外层）
        if self.connection_pool_enabled {
            exporter = Box::new(ConnectionPoolExporter::wrap(exporter)
                .with_connection_pool(true));
        }

        // 2. 批量处理
        if self.batch_optimization_enabled {
            exporter = Box::new(BatchOptimizedExporter::wrap(exporter));
        }

        // 3. Tracezip压缩
        if self.tracezip_enabled {
            exporter = Box::new(TracezipSpanExporter::wrap(exporter)
                .with_compression(true));
        }

        // 4. SIMD优化
        if self.simd_enabled {
            exporter = Box::new(SimdSpanExporter::wrap(exporter)
                .with_simd_optimization(true));
        }

        // 5. 多租户
        if self.multi_tenant_enabled {
            let mut multi_tenant = MultiTenantExporter::wrap(exporter);
            if let Some(tenant_id) = self.tenant_id {
                multi_tenant = multi_tenant.with_tenant_id(tenant_id);
            }
            exporter = Box::new(multi_tenant);
        }

        // 6. 合规管理（最内层）
        if self.compliance_enabled {
            exporter = Box::new(ComplianceExporter::wrap(exporter)
                .with_compliance(true));
        }

        Ok(exporter)
    }
}

impl Default for EnhancedExporter {
    fn default() -> Self {
        Self::new()
    }
}
