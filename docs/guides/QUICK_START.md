# 快速开始指南

欢迎使用 OTLP Rust 核心重构版本！本指南将帮助您在 5 分钟内开始使用。

---

## 📋 前置要求

- ✅ Rust 1.90 或更高版本
- ✅ Cargo (随 Rust 安装)
- ✅ Tokio 异步运行时
- ⏸️ Docker Desktop (可选，用于集成测试)

### 检查环境

```bash
# 检查 Rust 版本
rust --version  # 应该 >= 1.90.0

# 检查 Cargo 版本
cargo --version

# 检查 Docker (可选)
docker --version
```

---

## 🚀 5 分钟快速开始

### Step 1: 添加依赖

在您的 `Cargo.toml` 中添加:

```toml
[dependencies]
otlp = { path = "./otlp" }  # 或使用 git/crates.io 版本
tokio = { version = "1.40", features = ["full"] }
opentelemetry = "0.31"
```

### Step 2: 创建第一个示例

创建 `src/main.rs`:

```rust
use otlp::core::EnhancedOtlpClient;
use opentelemetry::KeyValue;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 启动 OTLP 客户端...");

    // 1. 创建客户端
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("quick-start-service")
        .build()
        .await?;

    println!("✅ 客户端创建成功!");

    // 2. 获取 Tracer
    let tracer = client.tracer("main");

    // 3. 创建 Span
    let span = tracer.start("hello-world");

    // 4. 添加属性
    span.set_attribute(KeyValue::new("greeting", "Hello OTLP!"));
    span.set_attribute(KeyValue::new("version", "0.1.0"));

    println!("📊 Span 已创建: hello-world");

    // 5. 模拟一些工作
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

    // 6. 结束 Span
    drop(span);

    println!("✅ Span 已导出!");

    // 7. 查看统计
    let stats = client.stats().await;
    println!("📈 统计信息:");
    println!("   - Spans 导出: {}", stats.spans_exported);
    println!("   - 错误数: {}", stats.errors);

    Ok(())
}
```

### Step 3: 运行示例

```bash
cargo run
```

**预期输出**:
```text
🚀 启动 OTLP 客户端...
✅ 客户端创建成功!
📊 Span 已创建: hello-world
✅ Span 已导出!
📈 统计信息:
   - Spans 导出: 1
   - 错误数: 0
```

---

## 📚 下一步

### 示例 1: 嵌套 Spans

```rust
use opentelemetry::trace::{TraceContextExt, Tracer};
use opentelemetry::Context;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("nested-service")
        .build()
        .await?;

    let tracer = client.tracer("main");

    // 父 Span
    let parent_span = tracer.start("parent-operation");
    let parent_cx = Context::current().with_span(parent_span);

    {
        // 子 Span 1
        let _guard = parent_cx.clone().attach();
        let child1_span = tracer.start("child-operation-1");
        
        tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
        
        drop(child1_span);

        // 子 Span 2
        let child2_span = tracer.start("child-operation-2");
        
        tokio::time::sleep(tokio::time::Duration::from_millis(30)).await;
        
        drop(child2_span);
    }

    drop(parent_cx);

    println!("✅ 嵌套 Spans 已导出!");

    Ok(())
}
```

### 示例 2: 错误处理

```rust
use opentelemetry::trace::StatusCode;

async fn risky_operation() -> Result<String, String> {
    // 模拟可能失败的操作
    Err("Something went wrong".to_string())
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("error-handling-service")
        .build()
        .await?;

    let tracer = client.tracer("main");
    let span = tracer.start("risky-operation");

    match risky_operation().await {
        Ok(result) => {
            span.set_status(StatusCode::Ok, "Success".to_string());
            println!("✅ 操作成功: {}", result);
        }
        Err(e) => {
            span.set_status(StatusCode::Error, format!("Failed: {}", e));
            span.add_event("error", vec![
                KeyValue::new("error.message", e.clone()),
            ]);
            println!("❌ 操作失败: {}", e);
        }
    }

    drop(span);

    Ok(())
}
```

### 示例 3: 性能优化

```rust
use otlp::core::{PerformanceOptimizer, BatchConfig, CompressionConfig, CompressionAlgorithm};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 配置性能优化
    let performance = PerformanceOptimizer::new()
        .with_batch_config(BatchConfig {
            max_batch_size: 100,
            max_wait_time: Duration::from_secs(5),
        })
        .with_compression(CompressionConfig {
            enabled: true,
            algorithm: CompressionAlgorithm::Gzip,
            level: 6,
            min_size_bytes: 1024,
        });

    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("performance-service")
        .with_performance(performance)
        .build()
        .await?;

    let tracer = client.tracer("main");

    // 创建多个 Spans
    for i in 0..10 {
        let span = tracer.start(&format!("operation-{}", i));
        span.set_attribute(KeyValue::new("iteration", i as i64));
        tokio::time::sleep(Duration::from_millis(10)).await;
        drop(span);
    }

    println!("✅ 10个 Spans 已批处理和压缩导出!");

    // 查看性能统计
    let perf_stats = client.performance().stats().await;
    println!("📊 性能统计:");
    println!("   - 批处理次数: {}", perf_stats.batches_processed);
    println!("   - 压缩次数: {}", perf_stats.compressions_performed);
    println!("   - 压缩率: {:.2}%", perf_stats.compression_ratio() * 100.0);

    Ok(())
}
```

### 示例 4: 可靠性保障

```rust
use otlp::core::{ReliabilityManager, RetryConfig, TimeoutConfig};
use std::time::Duration;

async fn unreliable_operation() -> Result<String, String> {
    // 模拟不可靠的操作
    use rand::Rng;
    let mut rng = rand::thread_rng();
    if rng.gen_bool(0.7) {  // 70% 失败率
        Err("Network error".to_string())
    } else {
        Ok("Success".to_string())
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 配置可靠性
    let reliability = ReliabilityManager::with_configs(
        RetryConfig {
            max_retries: 5,
            initial_delay: Duration::from_millis(500),
            max_delay: Duration::from_secs(10),
            multiplier: 2.0,
        },
        TimeoutConfig {
            default_timeout: Duration::from_secs(30),
            enabled: true,
        },
    );

    let client = EnhancedOtlpClient::builder()
        .with_endpoint("http://localhost:4317")
        .with_service_name("reliability-service")
        .with_reliability(reliability)
        .build()
        .await?;

    let tracer = client.tracer("main");

    // 使用重试执行不可靠的操作
    let result = client.reliability().retry(|| async {
        unreliable_operation().await
    }).await;

    match result {
        Ok(msg) => println!("✅ 操作成功: {}", msg),
        Err(e) => println!("❌ 操作失败 (所有重试耗尽): {}", e),
    }

    // 查看可靠性统计
    let rel_stats = client.reliability().stats().await;
    println!("📊 可靠性统计:");
    println!("   - 总重试次数: {}", rel_stats.total_retries);
    println!("   - 成功重试: {}", rel_stats.successful_retries);
    println!("   - 重试成功率: {:.2}%", rel_stats.retry_success_rate() * 100.0);

    Ok(())
}
```

---

## 🐳 使用 Docker 测试环境

### Step 1: 启动测试环境

```bash
cd otlp/tests/integration
docker-compose up -d
```

**包含服务**:
- OpenTelemetry Collector (端口 4317, 4318)
- Jaeger All-in-One (端口 16686)

### Step 2: 验证服务

```bash
# 检查 Collector 健康状态
curl http://localhost:13133/

# 检查 Jaeger UI
open http://localhost:16686
```

### Step 3: 运行您的应用

```bash
cd ../../..
cargo run --example enhanced_client_demo
```

### Step 4: 在 Jaeger UI 中查看 Traces

1. 打开浏览器访问 http://localhost:16686
2. 在 Service 下拉框中选择您的服务名
3. 点击 "Find Traces" 查看traces
4. 点击某个 trace 查看详情

### Step 5: 停止环境

```bash
cd otlp/tests/integration
docker-compose down
```

---

## 🧪 运行测试

### 单元测试

```bash
cd otlp
cargo test --lib
```

**输出**:
```text
running 21 tests
test core::enhanced_client::tests::test_client_builder ... ok
test core::enhanced_client::tests::test_client_stats ... ok
test core::performance_layer::tests::test_object_pool ... ok
... (18 more tests)

test result: ok. 21 passed; 0 failed
```

### 集成测试 (需要 Docker)

```bash
# 1. 启动 Docker 环境
cd otlp/tests/integration
docker-compose up -d

# 2. 等待服务就绪
sleep 30

# 3. 运行测试
cd ../..
cargo test --test integration_test -- --ignored --nocapture
```

---

## 📖 学习资源

### 文档

- [API 使用指南](otlp/docs/核心API使用指南.md) - 完整 API 文档
- [集成测试指南](otlp/docs/集成测试指南.md) - 集成测试教程
- [项目 README](README_核心重构_2025_10_18.md) - 项目总览

### 示例代码

- `otlp/examples/enhanced_client_demo.rs` - 完整示例
- 本文档中的所有示例

### 外部资源

- [OpenTelemetry 官方文档](https://opentelemetry.io/docs/)
- [OTLP 规范](https://github.com/open-telemetry/opentelemetry-specification/blob/main/specification/protocol/otlp.md)
- [Tokio 文档](https://tokio.rs/)

---

## 🐛 常见问题

### Q1: 编译错误 "cannot find crate `otlp`"

**解决方案**:
```bash
# 确保在正确的目录
cd otlp
cargo build
```

### Q2: "Connection refused" 错误

**原因**: OpenTelemetry Collector 未运行

**解决方案**:
```bash
# 启动 Docker 环境
cd otlp/tests/integration
docker-compose up -d

# 等待服务就绪
sleep 30
```

### Q3: Jaeger UI 中看不到 traces

**检查清单**:
1. ✅ Collector 是否运行? `curl http://localhost:13133/`
2. ✅ 服务名是否正确?
3. ✅ 时间范围是否合适?
4. ✅ Span 是否正确 drop?

**调试**:
```bash
# 查看 Collector 日志
docker-compose logs otel-collector

# 查看 Jaeger 日志
docker-compose logs jaeger
```

### Q4: 性能问题

**优化建议**:
1. 启用批处理
2. 启用压缩
3. 使用对象池
4. 调整批处理大小和超时

```rust
let performance = PerformanceOptimizer::new()
    .with_batch_config(BatchConfig {
        max_batch_size: 100,  // 增加批处理大小
        max_wait_time: Duration::from_secs(5),
    })
    .with_compression(CompressionConfig {
        enabled: true,
        algorithm: CompressionAlgorithm::Gzip,
        level: 6,  // 平衡压缩率和速度
        min_size_bytes: 1024,
    });
```

---

## 📞 获取帮助

### 问题反馈

如果遇到问题，请：
1. 查看 [常见问题](#常见问题)
2. 查看 [故障排查手册](otlp/docs/核心API使用指南.md#故障排查)
3. 提交 [Issue](https://github.com/yourusername/OTLP_rust/issues)

### 社区支持

- GitHub Discussions
- Rust 中文社区
- OpenTelemetry Slack

---

## 🎉 恭喜！

您已经完成了快速开始指南！

**下一步**:
- 📖 阅读 [API 使用指南](otlp/docs/核心API使用指南.md)
- 🧪 尝试更多示例
- 🚀 集成到您的项目中
- 🎓 学习高级特性

**Happy Tracing!** 🎊

---

**最后更新**: 2025-10-18  
**版本**: 0.1.0

---

