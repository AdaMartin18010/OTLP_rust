//! # 增强的运行时环境检测示例
//!
//! 本示例展示了如何使用reliability框架的增强环境检测功能，
//! 支持13种不同的运行时环境类型。

use reliability::prelude::*;
use reliability::runtime_environments::RuntimeEnvironment;

#[tokio::main]
#[allow(clippy::result_large_err)]
async fn main() -> Result<(), UnifiedError> {
    println!("=== reliability 增强环境检测示例 ===\n");

    // 1. 自动检测当前环境
    let detected_env = RuntimeEnvironment::detect_current();
    println!("🔍 检测到的环境: {:?}", detected_env);
    println!("📝 环境描述: {}", detected_env.description());

    // 2. 显示环境能力
    let capabilities = detected_env.capabilities();
    println!("\n🔧 环境能力:");
    println!("  多进程支持: {}", capabilities.supports_multiprocessing);
    println!("  多线程支持: {}", capabilities.supports_multithreading);
    println!("  文件系统支持: {}", capabilities.supports_file_system);
    println!("  网络支持: {}", capabilities.supports_network);
    println!("  系统调用支持: {}", capabilities.supports_system_calls);
    println!("  中断支持: {}", capabilities.supports_interrupts);
    println!(
        "  混沌工程支持: {}",
        capabilities.supports_chaos_engineering
    );

    // 3. 显示资源限制
    println!("\n📊 资源限制:");
    if let Some(memory_limit) = capabilities.memory_limit {
        println!("  内存限制: {} MB", memory_limit / (1024 * 1024));
    } else {
        println!("  内存限制: 无限制");
    }

    if let Some(cpu_limit) = capabilities.cpu_limit {
        println!("  CPU限制: {} MHz", cpu_limit);
    } else {
        println!("  CPU限制: 无限制");
    }

    if let Some(disk_limit) = capabilities.disk_limit {
        println!("  磁盘限制: {} GB", disk_limit / (1024 * 1024 * 1024));
    } else {
        println!("  磁盘限制: 无限制");
    }

    if let Some(network_limit) = capabilities.network_limit {
        println!("  网络限制: {} MB/s", network_limit / (1024 * 1024));
    } else {
        println!("  网络限制: 无限制");
    }

    // 4. 根据环境类型调整策略
    adjust_strategy_for_environment(&detected_env, &capabilities).await?;

    // 5. 演示所有环境类型
    demonstrate_all_environments().await?;

    Ok(())
}

/// 根据环境类型调整可靠性策略
async fn adjust_strategy_for_environment(
    env: &RuntimeEnvironment,
    capabilities: &EnvironmentCapabilities,
) -> Result<(), UnifiedError> {
    println!("\n⚙️  根据环境调整策略:");

    match env {
        RuntimeEnvironment::OperatingSystem => {
            println!("  🖥️  操作系统环境 - 启用所有功能");
            // 启用完整的监控和容错功能
        }
        RuntimeEnvironment::EmbeddedBareMetal => {
            println!("  🔧 嵌入式裸机环境 - 最小化资源使用");
            // 禁用资源密集型功能，优化内存使用
        }
        RuntimeEnvironment::RealTimeOS => {
            println!("  ⏱️  实时操作系统环境 - 优化延迟");
            // 优先考虑实时性，使用确定性算法
        }
        RuntimeEnvironment::GameEngine => {
            println!("  🎮 游戏引擎环境 - 优化性能");
            // 启用高性能监控，优化渲染性能
        }
        RuntimeEnvironment::Mobile => {
            println!("  📱 移动应用环境 - 优化电池和网络");
            // 启用电池监控，处理网络切换
        }
        RuntimeEnvironment::VirtualMachine => {
            println!("  🖥️  虚拟机环境 - 启用虚拟化特性");
            // 启用快照和迁移功能
        }
        RuntimeEnvironment::MicroVM => {
            println!("  ⚡ 微虚拟机环境 - 快速启动优化");
            // 优化启动时间，启用轻量级监控
        }
        RuntimeEnvironment::Container => {
            println!("  🐳 容器环境 - 资源限制监控");
            // 监控容器资源限制，启用健康检查
        }
        RuntimeEnvironment::KubernetesPod => {
            println!("  ☸️  Kubernetes Pod环境 - 编排管理");
            // 启用服务发现和配置管理
        }
        RuntimeEnvironment::WebAssembly => {
            println!("  🌐 WebAssembly环境 - 沙箱优化");
            // 启用沙箱监控，优化内存使用
        }
        RuntimeEnvironment::FunctionAsAService => {
            println!("  ⚡ 函数即服务环境 - 冷启动优化");
            // 优化冷启动性能，监控执行时间
        }
        RuntimeEnvironment::EdgeComputing => {
            println!("  🌐 边缘计算环境 - 离线能力");
            // 启用离线模式，优化网络延迟
        }
        RuntimeEnvironment::Blockchain => {
            println!("  ⛓️  区块链环境 - 共识监控");
            // 监控共识机制，启用智能合约监控
        }
    }

    // 根据能力调整具体配置
    if !capabilities.supports_chaos_engineering {
        println!("  ⚠️  当前环境不支持混沌工程测试");
    }

    if !capabilities.supports_multiprocessing {
        println!("  ⚠️  当前环境不支持多进程，调整容错策略");
    }

    if capabilities.memory_limit.is_some() {
        println!("  📊 检测到内存限制，启用内存监控");
    }

    Ok(())
}

/// 演示所有环境类型
async fn demonstrate_all_environments() -> Result<(), UnifiedError> {
    println!("\n🌍 所有支持的环境类型:");

    let all_environments = [
        RuntimeEnvironment::OperatingSystem,
        RuntimeEnvironment::EmbeddedBareMetal,
        RuntimeEnvironment::RealTimeOS,
        RuntimeEnvironment::GameEngine,
        RuntimeEnvironment::Mobile,
        RuntimeEnvironment::VirtualMachine,
        RuntimeEnvironment::MicroVM,
        RuntimeEnvironment::Container,
        RuntimeEnvironment::KubernetesPod,
        RuntimeEnvironment::WebAssembly,
        RuntimeEnvironment::FunctionAsAService,
        RuntimeEnvironment::EdgeComputing,
        RuntimeEnvironment::Blockchain,
    ];

    for (i, env) in all_environments.iter().enumerate() {
        let capabilities = env.capabilities();
        println!("  {}. {:?}", i + 1, env);
        println!("     📝 {}", env.description());
        println!(
            "     🔧 多进程: {} | 网络: {} | 混沌工程: {}",
            capabilities.supports_multiprocessing,
            capabilities.supports_network,
            capabilities.supports_chaos_engineering
        );

        if let Some(memory_limit) = capabilities.memory_limit {
            println!("     📊 内存限制: {} MB", memory_limit / (1024 * 1024));
        }
        println!();
    }

    Ok(())
}

/// 环境检测测试函数
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_environment_detection() {
        let env = RuntimeEnvironment::detect_current();
        let capabilities = env.capabilities();

        // 基本能力检查
        assert!(capabilities.supports_memory_management);
        assert!(capabilities.supports_timers);
        assert!(capabilities.supports_logging);
        assert!(capabilities.supports_metrics);
        assert!(capabilities.supports_health_checks);
        assert!(capabilities.supports_auto_recovery);
    }

    #[test]
    fn test_all_environments_have_capabilities() {
        let all_environments = [
            RuntimeEnvironment::OperatingSystem,
            RuntimeEnvironment::EmbeddedBareMetal,
            RuntimeEnvironment::RealTimeOS,
            RuntimeEnvironment::GameEngine,
            RuntimeEnvironment::Mobile,
            RuntimeEnvironment::VirtualMachine,
            RuntimeEnvironment::MicroVM,
            RuntimeEnvironment::Container,
            RuntimeEnvironment::KubernetesPod,
            RuntimeEnvironment::WebAssembly,
            RuntimeEnvironment::FunctionAsAService,
            RuntimeEnvironment::EdgeComputing,
            RuntimeEnvironment::Blockchain,
        ];

        for env in &all_environments {
            let capabilities = env.capabilities();

            // 所有环境都应该支持基本能力
            assert!(capabilities.supports_memory_management);
            assert!(capabilities.supports_timers);
            assert!(capabilities.supports_logging);
            assert!(capabilities.supports_metrics);
            assert!(capabilities.supports_health_checks);
            assert!(capabilities.supports_auto_recovery);
        }
    }
}
