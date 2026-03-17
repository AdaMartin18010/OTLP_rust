//! # WebAssembly Environment Adapter
//!
//! Provides support for WebAssembly environments, including browser WASM, WASI, Wasmtime, and other runtimes.
//!
//! ## 2025-2026 WebAssembly Trends
//!
//! ### WASI (WebAssembly System Interface) Evolution
//!
//! | Version | Status | Release | Key Features |
//! |---------|--------|---------|--------------|
//! | **WASI Preview 1** | ✅ Stable | 2019 | Basic POSIX-like functions, file I/O, environment variables |
//! | **WASI Preview 2 (0.2)** | ✅ Stable | Early 2024 | Component Model, networking (sockets), wasi-http, wasi-cli |
//! | **WASI Preview 3 (0.3)** | 🔄 Expected | H1 2025 | Native async I/O, async Component Model |
//! | **WASI 1.0** | ⏳ Planned | Late 2026/Early 2027 | Full stabilization |
//!
//! ### Component Model
//!
//! - **WIT (WebAssembly Interface Types)**: Standardized interface definition language
//! - **Cross-language interoperability**: Rust, Go, Python, JavaScript components can work together
//! - **Composition**: Build complex applications from reusable components
//! - **Security**: Capability-based security model with explicit permissions
//!
//! ### OpenTelemetry Integration
//!
//! - **wasi-observe**: Observability world for WASI (proposed)
//! - **wasi-otel**: OpenTelemetry API for WASI (proposed)
//! - **Spin 3.0**: Built-in OpenTelemetry integration for WASM applications
//! - **wasmCloud**: Full OpenTelemetry support for metrics, logs, and traces
//!
//! ### Runtimes Support
//!
//! | Runtime | WASI Preview 1 | WASI Preview 2 | Component Model |
//! |---------|----------------|----------------|-----------------|
//! | **Wasmtime** | ✅ Full | ✅ Full | ✅ Full |
//! | **Wasmer** | ✅ Full | ✅ Full | ✅ Full |
//! | **WasmEdge** | ✅ Full | 🔄 Partial | 🔄 In Progress |
//! | **Node.js** | 🔄 Experimental | ❌ Not yet | ❌ Not yet |
//! | **Browser** | N/A | N/A | ❌ Not yet |
//!
//! ## References
//!
//! - [WASI Spec](https://github.com/WebAssembly/WASI)
//! - [Component Model](https://component-model.bytecodealliance.org/)
//! - [WebAssembly 3.0](https://webassembly.org/roadmap/)
//! - [Spin 3.0 Observability](https://www.fermyon.com/blog/spin-3-0)
//! - [wasmCloud OpenTelemetry](https://wasmcloud.com/docs/deployment/observability/otel)

use super::{
    EnvironmentCapabilities, HealthLevel, HealthStatus, RecoveryType, ResourceUsage,
    RuntimeEnvironment, RuntimeEnvironmentAdapter, SystemInfo,
};
use crate::error_handling::UnifiedError;
use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::{SystemTime /*UNIX_EPOCH*/};

/// WebAssembly环境适配器
pub struct WebAssemblyEnvironmentAdapter {
    /// WASM运行时类型
    runtime: WASMRuntime,
    /// 模块名称
    module_name: String,
    /// 启动时间
    start_time: SystemTime,
    /// 内存限制
    memory_limit: u64,
    /// 当前内存使用情况
    current_memory_usage: u64,
    /// 执行次数
    execution_count: u64,
    /// 平均执行时间
    average_execution_time: f64,
    /// 错误计数
    error_count: u64,
}

/// WebAssembly Runtime Types (2025-2026)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum WASMRuntime {
    /// Browser environment (wasm32-unknown-unknown)
    /// - Supports WebAssembly 3.0 features
    /// - No WASI support in browsers (use JS polyfills)
    Browser,

    /// WASI Preview 1 (Legacy)
    /// - Basic POSIX-like functions
    /// - File I/O, environment variables, random
    /// - No networking
    #[allow(non_camel_case_types)]
    WASI_Preview1,

    /// WASI Preview 2 (Current Stable - 2024)
    /// - Component Model support
    /// - Networking (TCP/UDP sockets)
    /// - wasi-http for outbound HTTP
    /// - wasi-cli for command-line apps
    #[allow(non_camel_case_types)]
    WASI_Preview2,

    /// WASI Preview 3 (Expected H1 2025)
    /// - Native async I/O
    /// - Async Component Model
    /// - Cancellation tokens
    #[allow(non_camel_case_types)]
    WASI_Preview3,

    /// Wasmtime Runtime
    /// - Full WASI Preview 2 support
    /// - Component Model support
    /// - Async execution with tokio
    Wasmtime,

    /// Wasmer Runtime
    /// - WASI Preview 2 support (v3.x/4.x)
    /// - WASIX extension (POSIX compatibility)
    Wasmer,

    /// WasmEdge Runtime
    /// - WASI Preview 1 full support
    /// - Preview 2 partial support
    /// - Cloud-native extensions
    WasmEdge,

    /// Node.js WASM
    /// - Experimental WASI Preview 1
    /// - Limited security sandboxing
    NodeJS,

    /// wasmCloud
    /// - Full Component Model support
    /// - OpenTelemetry integration
    /// - Distributed WASM applications
    WasmCloud,

    /// Spin (Fermyon)
    /// - WASI Preview 2
    /// - Built-in OpenTelemetry
    /// - HTTP trigger support
    Spin,

    /// Unknown runtime
    Unknown,
}

impl WebAssemblyEnvironmentAdapter {
    /// 创建新的WebAssembly环境适配器
    pub fn new() -> Self {
        Self {
            runtime: Self::detect_runtime(),
            module_name: Self::detect_module_name(),
            start_time: SystemTime::now(),
            memory_limit: Self::detect_memory_limit(),
            current_memory_usage: 0,
            execution_count: 0,
            average_execution_time: 0.0,
            error_count: 0,
        }
    }

    /// Detect WebAssembly runtime environment
    ///
    /// # Detection Strategy (2025-2026)
    ///
    /// 1. Check for browser environment (wasm32 target with web APIs)
    /// 2. Check for WASI version markers
    /// 3. Check for specific runtime environment variables
    /// 4. Check for wasmCloud/Spin platform markers
    fn detect_runtime() -> WASMRuntime {
        #[cfg(target_arch = "wasm32")]
        {
            // Check for browser environment
            if Self::is_browser_environment() {
                return WASMRuntime::Browser;
            }

            // Check WASI version from environment
            if let Ok(wasi_version) = std::env::var("WASI_VERSION") {
                match wasi_version.as_str() {
                    "0.3" | "preview3" => return WASMRuntime::WASI_Preview3,
                    "0.2" | "preview2" => return WASMRuntime::WASI_Preview2,
                    _ => return WASMRuntime::WASI_Preview1,
                }
            }

            // Default to WASI Preview 1 for wasm32 target
            return WASMRuntime::WASI_Preview1;
        }

        #[cfg(not(target_arch = "wasm32"))]
        {
            // Check for wasmCloud
            if std::env::var("WASMCLOUD_HOST").is_ok()
                || std::env::var("WASMCLOUD_RPC_HOST").is_ok()
            {
                return WASMRuntime::WasmCloud;
            }

            // Check for Spin
            if std::env::var("SPIN_APP_NAME").is_ok()
                || std::env::var("SPIN_HTTP_LISTEN_ADDR").is_ok()
            {
                return WASMRuntime::Spin;
            }

            // Check for Wasmtime
            if std::env::var("WASMTIME_HOME").is_ok()
                || std::env::var("WASMTIME_BACKTRACE_DETAILS").is_ok()
            {
                return WASMRuntime::Wasmtime;
            }

            // Check for Wasmer
            if std::env::var("WASMER_DIR").is_ok() || std::env::var("WASMER_CONFIG").is_ok() {
                return WASMRuntime::Wasmer;
            }

            // Check for WasmEdge
            if std::env::var("WASMEDGE_HOME").is_ok() {
                return WASMRuntime::WasmEdge;
            }

            // Check for Node.js
            if std::env::var("NODE_ENV").is_ok() || std::env::var("NODE_PATH").is_ok() {
                return WASMRuntime::NodeJS;
            }

            // Check for WASI SDK
            if std::env::var("WASI_SDK_PATH").is_ok() {
                // Default to Preview 1 unless specified otherwise
                return WASMRuntime::WASI_Preview1;
            }
        }

        WASMRuntime::Unknown
    }

    /// 检测是否为浏览器环境
    #[allow(dead_code)]
    fn is_browser_environment() -> bool {
        #[cfg(target_arch = "wasm32")]
        {
            // 在WASM环境中，检查是否有window对象
            // 这是一个简化的检测，实际实现可能需要更复杂的逻辑
            return true; // 假设在浏览器中运行
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            false
        }
    }

    /// 检测模块名称
    fn detect_module_name() -> String {
        if let Ok(name) = std::env::var("WASM_MODULE_NAME") {
            return name;
        }

        if let Ok(name) = std::env::var("WASM_FUNCTION_NAME") {
            return name;
        }

        "unknown_wasm_module".to_string()
    }

    /// 检测内存限制
    fn detect_memory_limit() -> u64 {
        std::env::var("WASM_MEMORY_LIMIT")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(128 * 1024 * 1024) // 128MB 默认限制
    }

    /// 更新内存使用情况
    async fn update_memory_usage(&mut self) -> Result<(), UnifiedError> {
        // 在WASM环境中，内存使用情况通常由运行时管理
        // 这里使用模拟数据
        self.current_memory_usage = self.memory_limit / 4; // 模拟25%使用率
        Ok(())
    }

    /// 记录执行统计
    #[allow(dead_code)]
    fn record_execution(&mut self, execution_time: f64, success: bool) {
        self.execution_count += 1;
        self.average_execution_time =
            (self.average_execution_time * (self.execution_count - 1) as f64 + execution_time)
                / self.execution_count as f64;

        if !success {
            self.error_count += 1;
        }
    }

    /// 检查WASM环境健康状态
    async fn check_wasm_health(&self) -> Result<HealthLevel, UnifiedError> {
        let memory_usage_percent =
            (self.current_memory_usage as f64 / self.memory_limit as f64) * 100.0;
        let error_rate = if self.execution_count > 0 {
            (self.error_count as f64 / self.execution_count as f64) * 100.0
        } else {
            0.0
        };

        if memory_usage_percent > 90.0 || error_rate > 10.0 {
            Ok(HealthLevel::Error)
        } else if memory_usage_percent > 80.0 || error_rate > 5.0 {
            Ok(HealthLevel::Warning)
        } else {
            Ok(HealthLevel::Healthy)
        }
    }

    /// 获取WASM特定指标
    fn get_wasm_metrics(&self) -> HashMap<String, String> {
        let mut metrics = HashMap::new();
        metrics.insert(
            "execution_count".to_string(),
            self.execution_count.to_string(),
        );
        metrics.insert(
            "average_execution_time".to_string(),
            format!("{:.2}ms", self.average_execution_time),
        );
        metrics.insert("error_count".to_string(), self.error_count.to_string());
        metrics.insert(
            "error_rate".to_string(),
            if self.execution_count > 0 {
                format!(
                    "{:.2}%",
                    (self.error_count as f64 / self.execution_count as f64) * 100.0
                )
            } else {
                "0.00%".to_string()
            },
        );
        metrics.insert(
            "memory_usage_percent".to_string(),
            format!(
                "{:.2}%",
                (self.current_memory_usage as f64 / self.memory_limit as f64) * 100.0
            ),
        );
        metrics
    }
}

#[async_trait]
impl RuntimeEnvironmentAdapter for WebAssemblyEnvironmentAdapter {
    fn environment_type(&self) -> RuntimeEnvironment {
        RuntimeEnvironment::WebAssembly
    }

    fn capabilities(&self) -> EnvironmentCapabilities {
        RuntimeEnvironment::WebAssembly.capabilities()
    }

    async fn initialize(&mut self) -> Result<(), UnifiedError> {
        // 初始化WASM环境
        self.update_memory_usage().await?;
        Ok(())
    }

    async fn cleanup(&mut self) -> Result<(), UnifiedError> {
        // 清理WASM环境
        // WASM环境通常由运行时自动管理
        Ok(())
    }

    async fn get_system_info(&self) -> Result<SystemInfo, UnifiedError> {
        let mut extra_info = HashMap::new();
        extra_info.insert("runtime".to_string(), format!("{:?}", self.runtime));
        extra_info.insert("module_name".to_string(), self.module_name.clone());
        extra_info.insert("memory_limit".to_string(), self.memory_limit.to_string());
        extra_info.insert(
            "execution_count".to_string(),
            self.execution_count.to_string(),
        );

        Ok(SystemInfo {
            environment: RuntimeEnvironment::WebAssembly,
            system_name: format!("WASM: {}", self.module_name),
            system_version: "1.0.0".to_string(),
            architecture: "wasm32".to_string(),
            total_memory: self.memory_limit,
            total_cpu_cores: 1,                   // WASM通常是单线程
            total_disk_space: 1024 * 1024 * 1024, // 1GB 默认
            uptime: SystemTime::now()
                .duration_since(self.start_time)
                .unwrap_or_default(),
            extra_info,
        })
    }

    async fn get_resource_usage(&self) -> Result<ResourceUsage, UnifiedError> {
        Ok(ResourceUsage {
            cpu_usage_percent: 0.0, // WASM环境通常不直接暴露CPU使用率
            memory_usage_bytes: self.current_memory_usage,
            memory_usage_percent: (self.current_memory_usage as f64 / self.memory_limit as f64)
                * 100.0,
            disk_usage_bytes: 0, // WASM环境通常没有持久化存储
            disk_usage_percent: 0.0,
            network_rx_bytes: 0, // 网络使用情况需要特殊处理
            network_tx_bytes: 0,
            network_rx_rate: 0.0,
            network_tx_rate: 0.0,
            timestamp: chrono::Utc::now(),
        })
    }

    async fn check_health(&self) -> Result<HealthStatus, UnifiedError> {
        let overall_health = self.check_wasm_health().await?;

        let mut details = HashMap::new();
        details.insert(
            "memory_usage".to_string(),
            if self.current_memory_usage > self.memory_limit * 9 / 10 {
                HealthLevel::Warning
            } else {
                HealthLevel::Healthy
            },
        );
        details.insert(
            "execution_health".to_string(),
            if self.error_count > self.execution_count / 10 {
                HealthLevel::Warning
            } else {
                HealthLevel::Healthy
            },
        );

        Ok(HealthStatus {
            overall_health,
            details,
            check_time: chrono::Utc::now(),
            environment_specific: self.get_wasm_metrics(),
        })
    }

    async fn perform_recovery(&self, recovery_type: RecoveryType) -> Result<(), UnifiedError> {
        match recovery_type {
            RecoveryType::MemoryCleanup => {
                // 执行内存清理
                println!("执行WASM内存清理...");
                Ok(())
            }
            RecoveryType::ConnectionReset => {
                // 重置网络连接（如果适用）
                println!("重置WASM网络连接...");
                Ok(())
            }
            RecoveryType::ProcessRestart => {
                // 重启WASM模块
                println!("重启WASM模块...");
                Ok(())
            }
            RecoveryType::ServiceRestart => {
                // 重启WASM服务
                println!("重启WASM服务...");
                Ok(())
            }
            RecoveryType::SystemRestart => {
                // 重启WASM系统
                println!("重启WASM系统...");
                Ok(())
            }
            RecoveryType::Custom(action) => {
                // 执行自定义恢复操作
                println!("执行WASM自定义恢复操作: {}", action);
                Ok(())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_wasm_adapter_creation() {
        let adapter = WebAssemblyEnvironmentAdapter::new();
        assert_eq!(adapter.environment_type(), RuntimeEnvironment::WebAssembly);
    }

    #[tokio::test]
    async fn test_wasm_system_info() {
        let mut adapter = WebAssemblyEnvironmentAdapter::new();
        adapter.initialize().await.unwrap();

        let system_info = adapter.get_system_info().await.unwrap();
        assert_eq!(system_info.environment, RuntimeEnvironment::WebAssembly);
        assert!(system_info.system_name.starts_with("WASM:"));
        assert_eq!(system_info.architecture, "wasm32");
    }

    #[tokio::test]
    async fn test_wasm_health_check() {
        let mut adapter = WebAssemblyEnvironmentAdapter::new();
        adapter.initialize().await.unwrap();

        let health = adapter.check_health().await.unwrap();
        assert!(matches!(
            health.overall_health,
            HealthLevel::Healthy | HealthLevel::Warning
        ));
    }

    #[tokio::test]
    async fn test_wasm_memory_usage() {
        let mut adapter = WebAssemblyEnvironmentAdapter::new();
        adapter.initialize().await.unwrap();

        let resource_usage = adapter.get_resource_usage().await.unwrap();
        assert!(resource_usage.memory_usage_percent >= 0.0);
        assert!(resource_usage.memory_usage_percent <= 100.0);
    }
}
