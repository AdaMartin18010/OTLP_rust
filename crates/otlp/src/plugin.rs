//! # 插件系统
//!
//! 提供插件架构，支持动态扩展功能。
//!
//! ## 功能特性
//!
//! - 插件注册和管理
//! - 插件数据处理管道
//! - 插件生命周期管理
//! - 插件配置管理
//!
//! ## 使用示例
//!
//! ### 基本使用
//!
//! ```rust,no_run
//! use otlp::plugin::{PluginManager, ValidationPlugin};
//! use otlp::data::TelemetryData;
//!
//! fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     let mut manager = PluginManager::default();
//!
//!     // 注册插件
//!     manager.register_plugin(Box::new(ValidationPlugin::new()))?;
//!
//!     // 处理数据
//!     let mut data = TelemetryData::trace("operation");
//!     manager.process_data(&mut data)?;
//!
//!     // 关闭所有插件
//!     manager.shutdown_all()?;
//!
//!     Ok(())
//! }
//! ```
//!
//! ### 创建自定义插件
//!
//! ```rust,no_run
//! use otlp::plugin::{Plugin, PluginConfig};
//! use otlp::data::TelemetryData;
//! use otlp::error::Result;
//!
//! struct CustomPlugin {
//!     name: String,
//! }
//!
//! impl Plugin for CustomPlugin {
//!     fn name(&self) -> &str { &self.name }
//!     fn version(&self) -> &str { "1.0.0" }
//!     fn initialize(&mut self, _config: &PluginConfig) -> Result<()> {
//!         Ok(())
//!     }
//!     fn process(&self, _data: &mut TelemetryData) -> Result<()> {
//!         // 自定义处理逻辑
//!         Ok(())
//!     }
//!     fn shutdown(&mut self) -> Result<()> {
//!         Ok(())
//!     }
//! }
//! ```

use crate::error::Result;
use crate::data::TelemetryData;
use std::collections::HashMap;

/// 插件配置
#[derive(Debug, Clone)]
pub struct PluginConfig {
    pub name: String,
    pub version: String,
    pub enabled: bool,
    pub settings: HashMap<String, String>,
}

impl Default for PluginConfig {
    fn default() -> Self {
        Self {
            name: String::new(),
            version: "1.0.0".to_string(),
            enabled: true,
            settings: HashMap::new(),
        }
    }
}

/// 插件trait
pub trait Plugin: Send + Sync {
    /// 插件名称
    fn name(&self) -> &str;

    /// 插件版本
    fn version(&self) -> &str;

    /// 初始化插件
    fn initialize(&mut self, config: &PluginConfig) -> Result<()>;

    /// 处理遥测数据
    fn process(&self, data: &mut TelemetryData) -> Result<()>;

    /// 关闭插件
    fn shutdown(&mut self) -> Result<()>;
}

/// 插件管理器
pub struct PluginManager {
    plugins: HashMap<String, Box<dyn Plugin>>,
    #[allow(dead_code)]
    config: PluginConfig,
}

impl PluginManager {
    /// 创建新的插件管理器
    pub fn new(config: PluginConfig) -> Self {
        Self {
            plugins: HashMap::new(),
            config,
        }
    }

    /// 注册插件
    pub fn register_plugin(&mut self, plugin: Box<dyn Plugin>) -> Result<()> {
        let name = plugin.name().to_string();
        if self.plugins.contains_key(&name) {
            return Err(crate::error::OtlpError::internal(format!(
                "Plugin {} already registered",
                name
            )));
        }
        self.plugins.insert(name, plugin);
        Ok(())
    }

    /// 获取插件
    pub fn get_plugin(&self, name: &str) -> Option<&dyn Plugin> {
        self.plugins.get(name).map(|p| p.as_ref())
    }

    /// 处理数据
    pub fn process_data(&self, data: &mut TelemetryData) -> Result<()> {
        for plugin in self.plugins.values() {
            plugin.process(data)?;
        }
        Ok(())
    }

    /// 获取插件数量
    pub fn plugin_count(&self) -> usize {
        self.plugins.len()
    }

    /// 关闭所有插件
    pub fn shutdown_all(&mut self) -> Result<()> {
        for (name, plugin) in self.plugins.iter_mut() {
            if let Err(e) = plugin.shutdown() {
                tracing::warn!("Failed to shutdown plugin {}: {}", name, e);
            }
        }
        Ok(())
    }
}

impl Default for PluginManager {
    fn default() -> Self {
        Self::new(PluginConfig::default())
    }
}

/// 示例插件：数据验证插件
pub struct ValidationPlugin {
    name: String,
    version: String,
}

impl ValidationPlugin {
    pub fn new() -> Self {
        Self {
            name: "validation".to_string(),
            version: "1.0.0".to_string(),
        }
    }
}

impl Plugin for ValidationPlugin {
    fn name(&self) -> &str {
        &self.name
    }

    fn version(&self) -> &str {
        &self.version
    }

    fn initialize(&mut self, _config: &PluginConfig) -> Result<()> {
        tracing::info!("Validation plugin initialized");
        Ok(())
    }

    fn process(&self, data: &mut TelemetryData) -> Result<()> {
        // 简单的验证逻辑
        match &data.content {
            crate::data::TelemetryContent::Trace(_) => {
                // 验证trace数据
            }
            crate::data::TelemetryContent::Metric(_) => {
                // 验证metric数据
            }
            crate::data::TelemetryContent::Log(_) => {
                // 验证log数据
            }
        }
        Ok(())
    }

    fn shutdown(&mut self) -> Result<()> {
        tracing::info!("Validation plugin shutdown");
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_plugin_manager() {
        let mut manager = PluginManager::default();
        let plugin = Box::new(ValidationPlugin::new());

        assert!(manager.register_plugin(plugin).is_ok());
        assert_eq!(manager.plugin_count(), 1);
    }

    #[test]
    fn test_plugin_manager_duplicate() {
        let mut manager = PluginManager::default();
        let plugin1 = Box::new(ValidationPlugin::new());
        let plugin2 = Box::new(ValidationPlugin::new());

        assert!(manager.register_plugin(plugin1).is_ok());
        assert!(manager.register_plugin(plugin2).is_err());
    }

    #[test]
    fn test_plugin_manager_get_plugin() {
        let mut manager = PluginManager::default();
        let plugin = Box::new(ValidationPlugin::new());

        assert!(manager.register_plugin(plugin).is_ok());
        assert!(manager.get_plugin("validation").is_some());
        assert!(manager.get_plugin("nonexistent").is_none());
    }

    #[test]
    fn test_plugin_manager_process_data() {
        let mut manager = PluginManager::default();
        let plugin = Box::new(ValidationPlugin::new());
        manager.register_plugin(plugin).unwrap();

        let mut data = TelemetryData::trace("test-operation");
        assert!(manager.process_data(&mut data).is_ok());
    }

    #[test]
    fn test_plugin_manager_shutdown_all() {
        let mut manager = PluginManager::default();
        let plugin = Box::new(ValidationPlugin::new());
        manager.register_plugin(plugin).unwrap();

        assert!(manager.shutdown_all().is_ok());
    }

    #[test]
    fn test_validation_plugin() {
        let mut plugin = ValidationPlugin::new();
        let config = PluginConfig::default();

        assert!(plugin.initialize(&config).is_ok());
        assert_eq!(plugin.name(), "validation");
        assert_eq!(plugin.version(), "1.0.0");
    }

    #[test]
    fn test_validation_plugin_process() {
        use crate::data::{MetricType, LogSeverity};
        let plugin = ValidationPlugin::new();

        let mut trace_data = TelemetryData::trace("test-operation");
        assert!(plugin.process(&mut trace_data).is_ok());

        let mut metric_data = TelemetryData::metric("test-metric", MetricType::Counter);
        assert!(plugin.process(&mut metric_data).is_ok());

        let mut log_data = TelemetryData::log("test message", LogSeverity::Info);
        assert!(plugin.process(&mut log_data).is_ok());
    }

    #[test]
    fn test_plugin_config() {
        let config = PluginConfig::default();
        assert_eq!(config.version, "1.0.0");
        assert!(config.enabled);
        assert!(config.settings.is_empty());
    }

    #[test]
    fn test_plugin_config_custom() {
        let mut config = PluginConfig {
            name: "custom".to_string(),
            version: "2.0.0".to_string(),
            enabled: false,
            settings: HashMap::new(),
        };
        config.settings.insert("key".to_string(), "value".to_string());

        assert_eq!(config.name, "custom");
        assert_eq!(config.version, "2.0.0");
        assert!(!config.enabled);
        assert_eq!(config.settings.get("key"), Some(&"value".to_string()));
    }
}
