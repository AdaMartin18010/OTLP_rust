# OTLP_rust 快速入门指南

## 🎯 目标受众

本指南适用于希望快速上手OTLP_rust项目的开发者。

## ⚡ 5分钟快速上手

### 前置要求

```bash
# 检查Rust版本 (需要 >= 1.75)
rustc --version

# 如果版本过低，更新Rust
rustup update stable
```

### 第一步：克隆项目 (1分钟)

```bash
git clone https://github.com/your-org/OTLP_rust.git
cd OTLP_rust
```

### 第二步：构建项目 (2分钟)

```bash
# 构建所有crates
cargo build --workspace

# 运行测试确保环境正常
cargo test --workspace --lib
```

### 第三步：运行示例 (2分钟)

```bash
# 运行基础追踪示例
cargo run --example basic_tracing

# 运行性能优化示例
cargo run --example optimized_client --release
```

## 📚 学习路径

### 初学者路径 (1-2周)

```text
第1天: 了解OTLP基础
  ├── 📖 阅读 analysis/01_semantic_models/practical_semantic_models_guide.md
  └── 💻 运行 examples/basic_tracing.rs

第2-3天: 理解语义模型
  ├── 📖 阅读 analysis/01_semantic_models/otlp_semantic_foundations.md
  └── 💻 实践创建自定义语义属性

第4-5天: 实现基础客户端
  ├── 📖 阅读 analysis/09_implementation_guides/rust_implementation.md
  └── 💻 编写第一个OTLP客户端

第6-7天: 微服务集成
  ├── 📖 阅读 analysis/05_microservices_architecture/
  └── 💻 集成到现有项目

第2周: 性能优化和生产部署
  ├── 📖 阅读性能优化文档
  └── 💻 优化和部署应用
```

### 进阶路径 (2-4周)

```text
Week 1-2: 深入架构
  ├── 分布式系统架构 (analysis/02_distributed_architecture/)
  ├── 自我修复系统实现
  └── 分布式追踪深入

Week 3-4: 高级特性
  ├── eBPF性能分析 (analysis/04_ebpf_profiling/)
  ├── OTTL和OpAMP集成
  └── 形式化验证理解
```

## 🚀 常见使用场景

### 场景1：微服务追踪

```rust
use opentelemetry::{trace::Tracer, global, KeyValue};
use opentelemetry_sdk::Resource;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化追踪器
    let tracer = init_tracer()?;
    
    // 创建span追踪微服务调用
    tracer.in_span("process_order", |cx| {
        // 业务逻辑
        println!("处理订单...");
        
        // 添加自定义属性
        cx.span().set_attribute(KeyValue::new("order.id", "12345"));
        cx.span().set_attribute(KeyValue::new("customer.id", "67890"));
    });
    
    global::shutdown_tracer_provider();
    Ok(())
}

fn init_tracer() -> Result<impl Tracer, Box<dyn std::error::Error>> {
    // 初始化代码...
    unimplemented!()
}
```

### 场景2：性能监控

```rust
use opentelemetry::{metrics::MeterProvider, KeyValue};
use opentelemetry_sdk::metrics::SdkMeterProvider;

fn monitor_performance() {
    let meter = SdkMeterProvider::default().meter("my-service");
    
    // 创建计数器
    let request_counter = meter.u64_counter("http.requests").init();
    
    // 记录请求
    request_counter.add(1, &[
        KeyValue::new("method", "GET"),
        KeyValue::new("status", "200"),
    ]);
}
```

### 场景3：分布式日志

```rust
use opentelemetry::logs::{Logger, LoggerProvider};

fn distributed_logging() {
    let logger_provider = /* 初始化 */;
    let logger = logger_provider.logger("my-app");
    
    logger.emit(
        opentelemetry::logs::LogRecord::builder()
            .with_severity_text("ERROR")
            .with_body("数据库连接失败")
            .build()
    );
}
```

## 🔧 常见问题排查

### 问题1：编译失败

```bash
# 清理构建缓存
cargo clean

# 更新依赖
cargo update

# 重新构建
cargo build --workspace
```

### 问题2：版本冲突

```toml
# 在 Cargo.toml 中添加 patch
[patch.crates-io]
opentelemetry = { version = "0.31.0" }
opentelemetry_sdk = { version = "0.31.0" }
```

### 问题3：连接OTLP收集器失败

```bash
# 启动本地收集器
docker run -d \
  -p 4317:4317 \
  -p 4318:4318 \
  --name otel-collector \
  otel/opentelemetry-collector:latest

# 检查收集器状态
docker logs otel-collector
```

## 📖 核心文档导航

### 基础文档

- **[语义模型基础](01_semantic_models/otlp_semantic_foundations.md)** - 理解OTLP的核心概念
- **[实用指南](01_semantic_models/practical_semantic_models_guide.md)** - 实践应用
- **[Rust实现](09_implementation_guides/rust_implementation.md)** - Rust开发指南

### 高级主题

- **[分布式架构](02_distributed_architecture/)** - 分布式系统设计
- **[性能分析](04_ebpf_profiling/)** - eBPF和性能优化
- **[微服务](05_microservices_architecture/)** - 微服务可观测性

### 理论深入

- **[形式化语义](01_semantic_models/formal_semantics.md)** - 数学基础
- **[形式化验证](07_formal_verification/)** - 协议正确性
- **[学术标准](08_academic_standards/)** - 学术研究对齐

## 🎓 推荐学习资源

### 官方资源

- [OpenTelemetry官方文档](https://opentelemetry.io/)
- [OTLP协议规范](https://github.com/open-telemetry/opentelemetry-proto)
- [Rust OpenTelemetry SDK](https://github.com/open-telemetry/opentelemetry-rust)

### 社区资源

- OpenTelemetry Slack频道
- CNCF YouTube频道
- 相关技术博客和文章

## 💡 最佳实践

### 1. 性能优化

```rust
// 使用批处理减少网络开销
use opentelemetry_sdk::trace::BatchConfig;

let batch_config = BatchConfig::default()
    .with_max_queue_size(2048)
    .with_max_export_batch_size(512)
    .with_scheduled_delay(std::time::Duration::from_secs(5));
```

### 2. 错误处理

```rust
// 始终处理可能的错误
match tracer_provider.force_flush() {
    Ok(_) => println!("追踪数据已刷新"),
    Err(e) => eprintln!("刷新失败: {}", e),
}
```

### 3. 资源配置

```rust
// 提供完整的资源信息
let resource = Resource::new(vec![
    KeyValue::new("service.name", env!("CARGO_PKG_NAME")),
    KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
    KeyValue::new("deployment.environment", "production"),
    KeyValue::new("host.name", hostname()),
]);
```

## 🛠️ 开发工具推荐

### 调试工具

```bash
# 安装日志查看工具
cargo install cargo-watch

# 实时监控代码变化
cargo watch -x 'run --example basic_tracing'
```

### 性能分析

```bash
# 安装性能分析工具
cargo install cargo-flamegraph

# 生成火焰图
cargo flamegraph --example optimized_client
```

### 测试工具

```bash
# 安装测试覆盖率工具
cargo install cargo-tarpaulin

# 生成覆盖率报告
cargo tarpaulin --workspace --out Html
```

## 📞 获取帮助

### 遇到问题？

1. 检查 [常见问题](#常见问题排查)
2. 搜索项目 [Issues](https://github.com/your-org/OTLP_rust/issues)
3. 在 [Discussions](https://github.com/your-org/OTLP_rust/discussions) 提问
4. 参考 [完整文档索引](INDEX.md)

### 贡献代码

如果您想为项目做贡献，请参考：

- [贡献指南](../CONTRIBUTING.md)
- [代码规范](../docs/guides/CODING_STANDARDS.md)
- [提交PR流程](../docs/guides/PR_PROCESS.md)

## 🎯 下一步

完成快速入门后，您可以：

1. ✅ 探索更多[代码示例](../examples/)
2. 📚 深入阅读[分析文档](INDEX.md)
3. 🚀 将OTLP集成到您的项目
4. 🤝 参与社区讨论和贡献

---

**更新日期**: 2025年10月29日  
**文档版本**: v1.0  
**维护者**: OTLP_rust Team

祝您学习愉快！🎉

