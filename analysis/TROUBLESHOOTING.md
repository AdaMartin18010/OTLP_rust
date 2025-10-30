# OTLP_rust 故障排查指南

## 📋 目录

- [OTLP_rust 故障排查指南](#otlp_rust-故障排查指南)

## 🎯 目标

本文档提供OTLP_rust项目开发和使用过程中常见问题的诊断和解决方案。

---

## 编译和构建问题

### 问题1：编译失败 - "未找到crate"

**症状**：

```text
error[E0432]: unresolved import `opentelemetry`
  --> src/main.rs:1:5
```

**原因**：依赖未正确安装或版本不兼容

**解决方案**：

```bash
# 方案1：清理并重新构建
cargo clean
cargo build --workspace

# 方案2：更新依赖
cargo update

# 方案3：检查Cargo.toml配置
cat Cargo.toml | grep opentelemetry
```

**验证**：

```bash
cargo tree | grep opentelemetry
```

---

### 问题2：Rust版本过低

**症状**：

```text
error: package `opentelemetry v0.31.0` cannot be built because it requires rustc 1.75 or newer
```

**原因**：Rust编译器版本不满足要求

**解决方案**：

```bash
# 检查当前版本
rustc --version

# 更新到最新稳定版
rustup update stable

# 设置默认工具链
rustup default stable

# 验证版本
rustc --version  # 应该显示 >= 1.75
```

---

### 问题3：增量编译错误

**症状**：

```text
error: internal compiler error: ...
thread 'rustc' panicked at compiler/...
```

**原因**：增量编译缓存损坏

**解决方案**：

```bash
# 清理增量编译缓存
rm -rf target/debug/incremental
rm -rf target/release/incremental

# 或完全清理
cargo clean

# 禁用增量编译重新构建
CARGO_INCREMENTAL=0 cargo build
```

---

## 依赖和版本问题

### 问题4：OpenTelemetry版本冲突

**症状**：

```text
error: failed to select a version for `opentelemetry`
  multiple packages depend on `opentelemetry`:
    - package A depends on version `0.30.0`
    - package B depends on version `0.31.0`
```

**原因**：项目中同时存在多个不兼容的OpenTelemetry版本

**诊断**：

```bash
# 查看依赖树
cargo tree -i opentelemetry

# 查看冲突的包
cargo tree -i opentelemetry | grep -E "0.30|0.31"
```

**解决方案**：

```toml
# 在根 Cargo.toml 中添加 [patch.crates-io]
[patch.crates-io]
opentelemetry = { version = "0.31.0" }
opentelemetry_sdk = { version = "0.31.0" }
opentelemetry-otlp = { version = "0.31.0" }
```

```bash
# 清理并重新构建
cargo clean
cargo update
cargo build --workspace
```

**验证**：

```bash
cargo tree -i opentelemetry | grep "opentelemetry v"
# 应该只显示一个版本
```

---

### 问题5：依赖数量过多导致编译慢

**症状**：编译时间超过10分钟

**诊断**：

```bash
# 统计依赖数量
cargo tree --depth 1 | wc -l

# 查看编译时间最长的crate
cargo build --timings
# 打开生成的 target/cargo-timings/cargo-timing.html
```

**解决方案**：

```bash
# 1. 移除未使用的依赖
cargo install cargo-udeps
cargo +nightly udeps --workspace

# 2. 启用并行编译
export CARGO_BUILD_JOBS=8  # 根据CPU核心数调整

# 3. 使用sccache加速编译
cargo install sccache
export RUSTC_WRAPPER=sccache

# 4. 优化特性标志
# 在 Cargo.toml 中只启用必要的features
```

---

## 运行时问题

### 问题6：Panic - "已经初始化了全局TracerProvider"

**症状**：

```text
thread 'main' panicked at 'Cannot set global tracer provider: already initialized'
```

**原因**：尝试多次初始化全局追踪器

**解决方案**：

```rust
// ❌ 错误：多次初始化
fn main() {
    init_tracer();  // 第一次
    init_tracer();  // 第二次 - 会panic
}

// ✅ 正确：只初始化一次
use std::sync::Once;

static INIT: Once = Once::new();

fn init_tracer_once() {
    INIT.call_once(|| {
        // 初始化代码
        let tracer = init_tracer();
        opentelemetry::global::set_tracer_provider(tracer);
    });
}
```

---

### 问题7：内存泄漏或持续增长

**症状**：程序运行一段时间后内存使用持续增长

**诊断**：

```bash
# 使用valgrind检查内存泄漏（Linux）
cargo build
valgrind --leak-check=full ./target/debug/your_app

# 使用heaptrack分析内存（Linux）
heaptrack ./target/debug/your_app
heaptrack_gui heaptrack.your_app.*.gz
```

**常见原因和解决方案**：

```rust
// 原因1：忘记关闭TracerProvider
// ❌ 错误
fn main() {
    let tracer = init_tracer();
    // ... 使用tracer
    // 程序结束但没有关闭
}

// ✅ 正确
fn main() {
    let tracer = init_tracer();
    // ... 使用tracer

    // 优雅关闭
    opentelemetry::global::shutdown_tracer_provider();
}

// 原因2：批处理队列过大
// ✅ 调整批处理配置
use opentelemetry_sdk::trace::BatchConfig;

let batch_config = BatchConfig::default()
    .with_max_queue_size(2048)  // 减小队列大小
    .with_max_export_batch_size(512)
    .with_scheduled_delay(std::time::Duration::from_secs(5));
```

---

### 问题8：异步运行时冲突

**症状**：

```text
error: Cannot start a runtime from within a runtime
```

**原因**：在Tokio运行时内部尝试创建新的运行时

**解决方案**：

```rust
// ❌ 错误：嵌套运行时
#[tokio::main]
async fn main() {
    let runtime = tokio::runtime::Runtime::new().unwrap(); // 错误！
    runtime.block_on(async_function());
}

// ✅ 正确：使用现有运行时
#[tokio::main]
async fn main() {
    async_function().await;
}

// ✅ 正确：在同步代码中使用
fn main() {
    let runtime = tokio::runtime::Runtime::new().unwrap();
    runtime.block_on(async_function());
}
```

---

## 网络和连接问题

### 问题9：无法连接到OTLP收集器

**症状**：

```text
Error: Transport error: Connection refused (os error 111)
```

**诊断步骤**：

```bash
# 1. 检查收集器是否运行
docker ps | grep otel-collector

# 2. 检查端口是否开放
netstat -tulpn | grep 4317
# 或
lsof -i :4317

# 3. 测试连接
telnet localhost 4317
# 或
nc -zv localhost 4317

# 4. 检查防火墙
sudo iptables -L | grep 4317
```

**解决方案**：

```bash
# 方案1：启动OTLP收集器
docker run -d \
  -p 4317:4317 \
  -p 4318:4318 \
  --name otel-collector \
  otel/opentelemetry-collector:latest

# 方案2：使用正确的端点
# 在代码中使用
let endpoint = "http://localhost:4317";  // gRPC
# 或
let endpoint = "http://localhost:4318";  // HTTP

# 方案3：配置防火墙规则
sudo iptables -A INPUT -p tcp --dport 4317 -j ACCEPT
```

---

### 问题10：TLS/SSL证书验证失败

**症状**：

```text
Error: tls handshake failed: certificate verify failed
```

**解决方案**：

```rust
// 开发环境：禁用证书验证（不推荐生产使用）
use opentelemetry_otlp::WithExportConfig;

let exporter = opentelemetry_otlp::new_exporter()
    .tonic()
    .with_endpoint("https://localhost:4317")
    .with_tls_config(
        tonic::transport::ClientTlsConfig::new()
            .danger_accept_invalid_certs(true)  // 仅用于开发
    )
    .build_span_exporter()?;

// 生产环境：提供正确的证书
let cert = std::fs::read("path/to/ca.crt")?;
let tls_config = tonic::transport::ClientTlsConfig::new()
    .ca_certificate(tonic::transport::Certificate::from_pem(cert));

let exporter = opentelemetry_otlp::new_exporter()
    .tonic()
    .with_endpoint("https://otlp.example.com:4317")
    .with_tls_config(tls_config)
    .build_span_exporter()?;
```

---

### 问题11：超时错误

**症状**：

```text
Error: Timeout: operation timed out after 10s
```

**解决方案**：

```rust
use std::time::Duration;
use opentelemetry_otlp::WithExportConfig;

let exporter = opentelemetry_otlp::new_exporter()
    .tonic()
    .with_endpoint("http://localhost:4317")
    .with_timeout(Duration::from_secs(30))  // 增加超时时间
    .build_span_exporter()?;
```

---

## 性能问题

### 问题12：追踪开销过大

**症状**：启用追踪后应用性能下降明显

**诊断**：

```bash
# 性能对比测试
# 1. 不启用追踪
cargo run --release

# 2. 启用追踪
RUST_LOG=debug cargo run --release

# 3. 使用性能分析工具
cargo flamegraph --release
```

**优化方案**：

```rust
// 1. 使用采样降低开销
use opentelemetry_sdk::trace::{Sampler, SamplerDecision};

let sampler = Sampler::TraceIdRatioBased(0.1);  // 只采样10%的追踪

// 2. 优化批处理配置
use opentelemetry_sdk::trace::BatchConfig;

let batch_config = BatchConfig::default()
    .with_max_queue_size(4096)
    .with_max_export_batch_size(1024)
    .with_scheduled_delay(Duration::from_secs(10));

// 3. 使用异步导出
use opentelemetry_sdk::runtime::Tokio;

let provider = TracerProvider::builder()
    .with_batch_exporter(exporter, Tokio)  // 异步导出
    .build();

// 4. 减少属性数量
// ❌ 过多属性
span.set_attribute(KeyValue::new("attr1", "value1"));
span.set_attribute(KeyValue::new("attr2", "value2"));
// ... 100个属性

// ✅ 只记录关键属性
span.set_attribute(KeyValue::new("request.id", request_id));
span.set_attribute(KeyValue::new("user.id", user_id));
```

---

### 问题13：内存使用过高

**优化方案**：

```rust
// 1. 限制队列大小
let batch_config = BatchConfig::default()
    .with_max_queue_size(1024)  // 减小队列
    .with_max_export_batch_size(256);

// 2. 及时导出数据
provider.force_flush();

// 3. 使用对象池
use std::sync::Arc;
use parking_lot::Mutex;

lazy_static! {
    static ref SPAN_POOL: Arc<Mutex<Vec<Box<Span>>>> =
        Arc::new(Mutex::new(Vec::with_capacity(1000)));
}

// 4. 避免大量字符串分配
use std::borrow::Cow;

fn create_attribute(key: &'static str, value: Cow<'static, str>) -> KeyValue {
    KeyValue::new(key, value)
}
```

---

## 测试问题

### 问题14：测试中TracerProvider初始化冲突

**症状**：测试间相互影响或失败

**解决方案**：

```rust
#[cfg(test)]
mod tests {
    use super::*;

    // 方案1：为每个测试使用独立的Provider
    #[tokio::test]
    async fn test_tracing() {
        let provider = TracerProvider::builder()
            .with_simple_exporter(/* */)
            .build();

        let tracer = provider.tracer("test-tracer");
        // ... 测试代码

        // 清理
        drop(tracer);
        drop(provider);
    }

    // 方案2：使用测试专用的NoopProvider
    #[test]
    fn test_without_real_tracing() {
        let provider = opentelemetry::global::tracer_provider();
        // 使用noop provider进行测试
    }
}
```

---

### 问题15：测试覆盖率无法生成

**症状**：运行`cargo tarpaulin`失败

**解决方案**：

```bash
# 方案1：更新tarpaulin
cargo install cargo-tarpaulin --force

# 方案2：排除有问题的文件
cargo tarpaulin --workspace \
  --exclude-files "*/tests/*" \
  --exclude-files "*/benches/*" \
  --timeout 300

# 方案3：使用docker运行
docker run --security-opt seccomp=unconfined \
  -v "${PWD}:/volume" \
  xd009642/tarpaulin \
  cargo tarpaulin --workspace --out Html
```

---

## 平台特定问题

### Windows平台

#### 问题16：链接错误

```bash
# 安装Visual Studio Build Tools
# 或使用GNU工具链
rustup default stable-gnu
```

#### 问题17：路径长度限制

```bash
# 启用长路径支持
reg add HKLM\SYSTEM\CurrentControlSet\Control\FileSystem /v LongPathsEnabled /t REG_DWORD /d 1
```

### macOS平台

#### 问题18：OpenSSL链接问题

```bash
# 安装OpenSSL
brew install openssl

# 设置环境变量
export OPENSSL_DIR=/usr/local/opt/openssl
export PKG_CONFIG_PATH=/usr/local/opt/openssl/lib/pkgconfig
```

### Linux平台

#### 问题19：缺少系统库

```bash
# Ubuntu/Debian
sudo apt-get install build-essential pkg-config libssl-dev

# CentOS/RHEL
sudo yum groupinstall "Development Tools"
sudo yum install openssl-devel

# Arch Linux
sudo pacman -S base-devel openssl
```

---

## 🔍 诊断技巧

### 启用详细日志

```bash
# 设置日志级别
export RUST_LOG=debug
cargo run

# 仅显示特定模块
export RUST_LOG=opentelemetry=debug,opentelemetry_otlp=trace
cargo run
```

### 使用调试工具

```bash
# 安装调试工具
cargo install cargo-watch
cargo install cargo-expand
cargo install cargo-bloat

# 监控文件变化
cargo watch -x run

# 查看宏展开
cargo expand

# 分析二进制大小
cargo bloat --release
```

---

## 📞 获取更多帮助

如果上述方案无法解决您的问题：

1. **搜索Issues**: [GitHub Issues](https://github.com/your-org/OTLP_rust/issues)
2. **查看文档**: [完整文档索引](INDEX.md)
3. **提问讨论**: [GitHub Discussions](https://github.com/your-org/OTLP_rust/discussions)
4. **联系社区**: OpenTelemetry Slack

---

**最后更新**: 2025年10月29日
**维护者**: OTLP_rust Team
