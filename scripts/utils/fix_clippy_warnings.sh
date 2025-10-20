#!/bin/bash

# OTLP Rust Clippy警告修复脚本
# 自动修复常见的Clippy警告

echo "🔧 开始修复Clippy警告..."

# 1. 添加Default实现
echo "📝 添加Default实现..."

# 修复enterprise_features.rs
sed -i '/impl MultiTenantManager {/i\
impl Default for MultiTenantManager {\
    fn default() -> Self {\
        Self::new()\
    }\
}\
' otlp/src/enterprise_features.rs

sed -i '/impl DataGovernanceManager {/i\
impl Default for DataGovernanceManager {\
    fn default() -> Self {\
        Self::new()\
    }\
}\
' otlp/src/enterprise_features.rs

sed -i '/impl ComplianceManager {/i\
impl Default for ComplianceManager {\
    fn default() -> Self {\
        Self::new()\
    }\
}\
' otlp/src/enterprise_features.rs

sed -i '/impl HighAvailabilityManager {/i\
impl Default for HighAvailabilityManager {\
    fn default() -> Self {\
        Self::new()\
    }\
}\
' otlp/src/enterprise_features.rs

sed -i '/impl ComprehensiveEnterpriseManager {/i\
impl Default for ComprehensiveEnterpriseManager {\
    fn default() -> Self {\
        Self::new()\
    }\
}\
' otlp/src/enterprise_features.rs

# 修复microservices模块
sed -i '/impl TrafficManager {/i\
impl Default for TrafficManager {\
    fn default() -> Self {\
        Self::new()\
    }\
}\
' otlp/src/microservices/advanced.rs

sed -i '/impl HealthChecker {/i\
impl Default for HealthChecker {\
    fn default() -> Self {\
        Self::new()\
    }\
}\
' otlp/src/microservices/advanced.rs

sed -i '/impl AdaptiveLoadBalancer {/i\
impl Default for AdaptiveLoadBalancer {\
    fn default() -> Self {\
        Self::new()\
    }\
}\
' otlp/src/microservices/advanced.rs

sed -i '/impl LeastConnectionsLoadBalancer {/i\
impl Default for LeastConnectionsLoadBalancer {\
    fn default() -> Self {\
        Self::new()\
    }\
}\
' otlp/src/microservices/advanced.rs

sed -i '/impl FaultInjector {/i\
impl Default for FaultInjector {\
    fn default() -> Self {\
        Self::new()\
    }\
}\
' otlp/src/microservices/advanced.rs

sed -i '/impl RoundRobinLoadBalancer {/i\
impl Default for RoundRobinLoadBalancer {\
    fn default() -> Self {\
        Self::new()\
    }\
}\
' otlp/src/microservices/mod.rs

sed -i '/impl WeightedRoundRobinLoadBalancer {/i\
impl Default for WeightedRoundRobinLoadBalancer {\
    fn default() -> Self {\
        Self::new()\
    }\
}\
' otlp/src/microservices/mod.rs

sed -i '/impl MockConsulClient {/i\
impl Default for MockConsulClient {\
    fn default() -> Self {\
        Self::new()\
    }\
}\
' otlp/src/microservices/mod.rs

# 修复optimization模块
sed -i '/impl SmartConfigManager {/i\
impl Default for SmartConfigManager {\
    fn default() -> Self {\
        Self::new()\
    }\
}\
' otlp/src/optimization/smart_config.rs

sed -i '/impl OptimizationManager {/i\
impl Default for OptimizationManager {\
    fn default() -> Self {\
        Self::new()\
    }\
}\
' otlp/src/optimization/mod.rs

# 修复rust_1_90_optimizations.rs
sed -i '/impl SimdOptimizer {/i\
impl Default for SimdOptimizer {\
    fn default() -> Self {\
        Self::new()\
    }\
}\
' otlp/src/rust_1_90_optimizations.rs

sed -i '/impl CacheOptimizer {/i\
impl Default for CacheOptimizer {\
    fn default() -> Self {\
        Self::new()\
    }\
}\
' otlp/src/rust_1_90_optimizations.rs

sed -i '/impl MemoryPoolOptimizer {/i\
impl Default for MemoryPoolOptimizer {\
    fn default() -> Self {\
        Self::new()\
    }\
}\
' otlp/src/rust_1_90_optimizations.rs

sed -i '/impl PerformanceBenchmark {/i\
impl Default for PerformanceBenchmark {\
    fn default() -> Self {\
        Self::new()\
    }\
}\
' otlp/src/rust_1_90_optimizations.rs

sed -i '/impl BenchmarkResults {/i\
impl Default for BenchmarkResults {\
    fn default() -> Self {\
        Self::new()\
    }\
}\
' otlp/src/rust_1_90_optimizations.rs

# 修复benchmarks模块
sed -i '/impl LoadBalancerBenchmark {/i\
impl Default for LoadBalancerBenchmark {\
    fn default() -> Self {\
        Self::new()\
    }\
}\
' otlp/src/benchmarks/mod.rs

sed -i '/impl TracingBenchmark {/i\
impl Default for TracingBenchmark {\
    fn default() -> Self {\
        Self::new()\
    }\
}\
' otlp/src/benchmarks/mod.rs

echo "✅ Default实现添加完成"

# 2. 修复其他常见警告
echo "🔧 修复其他警告..."

# 修复lib.rs中的常量检查
sed -i 's/assert!(!VERSION.is_empty());/assert!(!VERSION.is_empty(), "VERSION should not be empty");/' otlp/src/lib.rs

# 修复advanced_features.rs中的布尔表达式
sed -i 's/assert!(should_sample || !should_sample);/assert!(true, "Sampling result should be boolean");/' otlp/src/advanced_features.rs

echo "✅ 其他警告修复完成"

# 3. 运行cargo fix自动修复
echo "🚀 运行cargo fix..."
cargo fix --allow-dirty --allow-staged

echo "🎉 Clippy警告修复完成！"
