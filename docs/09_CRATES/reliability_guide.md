# ⚡ Reliability Crate 使用指南

**版本**: 1.0
**定位**: Rust的运行、执行流、环境OS感知、度量的封装和组织
**最后更新**: 2025年10月26日
**状态**: 🟢 活跃维护

> **简介**: Reliability Crate 使用指南 - 执行流感知、环境适配和可靠性保障的完整指南。

---

## 📋 目录

- [⚡ Reliability Crate 使用指南](#-reliability-crate-使用指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [核心功能](#核心功能)
    - [📦 功能模块](#-功能模块)
  - [快速开始](#快速开始)
    - [安装依赖](#安装依赖)
    - [基础示例](#基础示例)
  - [执行流感知](#执行流感知)
    - [调用链追踪](#调用链追踪)
    - [执行图分析](#执行图分析)
    - [性能剖析](#性能剖析)
  - [运行时环境](#运行时环境)
    - [OS环境检测](#os环境检测)
    - [Kubernetes集成](#kubernetes集成)
  - [性能度量](#性能度量)
    - [CPU度量](#cpu度量)
    - [内存度量](#内存度量)
  - [自适应优化](#自适应优化)
    - [资源预测](#资源预测)
  - [容错机制](#容错机制)
    - [熔断器](#熔断器)
    - [重试机制](#重试机制)
    - [限流器](#限流器)
  - [最佳实践](#最佳实践)
    - [综合可靠性方案](#综合可靠性方案)
  - [完整文档](#完整文档)
    - [📚 详细文档](#-详细文档)
    - [📖 主要文档索引](#-主要文档索引)
    - [🎯 示例代码](#-示例代码)
  - [🔗 相关资源](#-相关资源)
    - [项目文档](#项目文档)
    - [架构文档](#架构文档)
    - [主文档](#主文档)
  - [🤝 贡献](#-贡献)

---

## 概述

`reliability` crate 提供了 Rust 应用的运行时基础设施支持。它专注于:

- ✅ **执行流感知**: 调用链追踪、执行图分析、性能分析
- ✅ **运行时环境**: OS环境感知、容器环境、K8s集成、嵌入式、Wasm
- ✅ **性能度量**: CPU、内存、I/O、网络的精确度量
- ✅ **自适应优化**: 资源预测、自动调优、拓扑发现
- ✅ **容错机制**: 熔断器、重试、超时、限流、降级

---

## 核心功能

### 📦 功能模块

```text
reliability/
├── 🔍 执行流感知 (execution_flow/)
│   ├── 调用链追踪 (call_chain_tracer)
│   ├── 执行图分析 (execution_graph)
│   ├── 性能剖析 (profiler)
│   ├── 火焰图 (flamegraph)
│   └── 调用栈分析 (stack_analyzer)
│
├── 🖥️ 运行时环境 (runtime_environments/)
│   ├── OS环境检测 (os_detector)
│   ├── 容器环境 (container)
│   ├── Kubernetes集成 (k8s)
│   ├── 嵌入式支持 (embedded)
│   └── WebAssembly (wasm)
│
├── 📊 性能度量 (metrics/)
│   ├── CPU度量 (cpu_metrics)
│   ├── 内存度量 (memory_metrics)
│   ├── I/O度量 (io_metrics)
│   ├── 网络度量 (network_metrics)
│   └── 自定义指标 (custom_metrics)
│
├── 🎯 自适应优化 (self_awareness/)
│   ├── 资源预测 (resource_predictor)
│   ├── 自动调优 (auto_tuner)
│   ├── 拓扑发现 (topology_discovery)
│   ├── 负载感知 (load_awareness)
│   └── 性能建模 (performance_model)
│
└── 🛡️ 容错机制 (fault_tolerance/)
    ├── 熔断器 (circuit_breaker)
    ├── 重试机制 (retry)
    ├── 超时控制 (timeout)
    ├── 限流器 (rate_limiter)
    └── 降级策略 (fallback)
```

---

## 快速开始

### 安装依赖

在 `Cargo.toml` 中添加:

```toml
[dependencies]
reliability = { path = "crates/reliability" }

# 或使用特性标志
reliability = { path = "crates/reliability", features = ["tracing", "metrics", "fault-tolerance"] }
```

### 基础示例

```rust
use reliability::prelude::*;

#[tokio::main]
async fn main() -> Result<()> {
    // 1. 执行流追踪
    let tracer = CallChainTracer::new();
    tracer.start_span("main_operation")?;

    // 2. 性能度量
    let metrics = PerformanceMetrics::new();
    metrics.record_cpu_usage().await?;

    // 3. 容错机制
    let circuit_breaker = CircuitBreaker::new(
        CircuitBreakerConfig::default()
    );
    circuit_breaker.call(|| async {
        risky_operation().await
    }).await?;

    // 4. 运行时环境检测
    let env = RuntimeEnvironment::detect()?;
    println!("Running in: {:?}", env.platform);

    Ok(())
}
```

---

## 执行流感知

### 调用链追踪

**调用链追踪**记录函数调用关系:

```rust
use reliability::execution_flow::*;

struct CallChainTracer {
    spans: Arc<RwLock<HashMap<String, Span>>>,
    current_span: Arc<RwLock<Option<String>>>,
}

impl CallChainTracer {
    fn new() -> Self {
        Self {
            spans: Arc::new(RwLock::new(HashMap::new())),
            current_span: Arc::new(RwLock::new(None)),
        }
    }

    fn start_span(&self, name: impl Into<String>) -> SpanId {
        let span_id = SpanId::new();
        let parent_id = self.current_span.read().unwrap().clone();

        let span = Span {
            id: span_id.clone(),
            name: name.into(),
            parent_id,
            start_time: Instant::now(),
            end_time: None,
            attributes: HashMap::new(),
        };

        self.spans.write().unwrap().insert(span_id.0.clone(), span);
        *self.current_span.write().unwrap() = Some(span_id.0.clone());

        span_id
    }

    fn end_span(&self, span_id: SpanId) {
        if let Some(span) = self.spans.write().unwrap().get_mut(&span_id.0) {
            span.end_time = Some(Instant::now());
        }

        // 恢复父 span 为当前 span
        if let Some(span) = self.spans.read().unwrap().get(&span_id.0) {
            *self.current_span.write().unwrap() = span.parent_id.clone();
        }
    }

    fn add_attribute(&self, span_id: SpanId, key: String, value: String) {
        if let Some(span) = self.spans.write().unwrap().get_mut(&span_id.0) {
            span.attributes.insert(key, value);
        }
    }

    fn get_call_chain(&self, span_id: SpanId) -> Vec<Span> {
        let mut chain = Vec::new();
        let spans = self.spans.read().unwrap();

        let mut current_id = Some(span_id.0);
        while let Some(id) = current_id {
            if let Some(span) = spans.get(&id) {
                chain.push(span.clone());
                current_id = span.parent_id.clone();
            } else {
                break;
            }
        }

        chain.reverse();
        chain
    }
}

// 使用示例
fn main() -> Result<()> {
    let tracer = CallChainTracer::new();

    // 开始追踪
    let span1 = tracer.start_span("operation_a");
    tracer.add_attribute(span1.clone(), "user_id".to_string(), "123".to_string());

    // 嵌套调用
    let span2 = tracer.start_span("operation_b");
    // ... 执行操作 ...
    tracer.end_span(span2.clone());

    tracer.end_span(span1.clone());

    // 获取调用链
    let chain = tracer.get_call_chain(span2);
    for span in chain {
        println!("{} -> {}", span.name, span.duration());
    }

    Ok(())
}
```

### 执行图分析

**执行图**可视化程序执行流:

```rust
use reliability::execution_flow::execution_graph::*;

struct ExecutionGraph {
    nodes: HashMap<String, Node>,
    edges: Vec<Edge>,
}

struct Node {
    id: String,
    name: String,
    execution_count: u64,
    total_time: Duration,
    self_time: Duration,
}

struct Edge {
    from: String,
    to: String,
    count: u64,
}

impl ExecutionGraph {
    fn from_traces(spans: &[Span]) -> Self {
        let mut graph = ExecutionGraph {
            nodes: HashMap::new(),
            edges: Vec::new(),
        };

        for span in spans {
            // 添加节点
            let node = graph.nodes.entry(span.id.clone()).or_insert_with(|| Node {
                id: span.id.clone(),
                name: span.name.clone(),
                execution_count: 0,
                total_time: Duration::ZERO,
                self_time: Duration::ZERO,
            });

            node.execution_count += 1;
            node.total_time += span.duration();

            // 添加边
            if let Some(parent_id) = &span.parent_id {
                graph.edges.push(Edge {
                    from: parent_id.clone(),
                    to: span.id.clone(),
                    count: 1,
                });
            }
        }

        graph
    }

    fn find_hotspots(&self) -> Vec<&Node> {
        let mut nodes: Vec<&Node> = self.nodes.values().collect();
        nodes.sort_by_key(|n| std::cmp::Reverse(n.self_time));
        nodes.into_iter().take(10).collect()
    }

    fn to_dot(&self) -> String {
        let mut dot = String::from("digraph G {\n");

        for node in self.nodes.values() {
            dot.push_str(&format!(
                "  \"{}\" [label=\"{}\\n{:.2}ms ({}x)\"];\n",
                node.id,
                node.name,
                node.self_time.as_secs_f64() * 1000.0,
                node.execution_count,
            ));
        }

        for edge in &self.edges {
            dot.push_str(&format!(
                "  \"{}\" -> \"{}\" [label=\"{}\"];\n",
                edge.from, edge.to, edge.count
            ));
        }

        dot.push_str("}\n");
        dot
    }
}
```

### 性能剖析

**性能剖析**分析程序性能瓶颈:

```rust
use reliability::execution_flow::profiler::*;

struct Profiler {
    samples: Arc<Mutex<Vec<Sample>>>,
    sampling_interval: Duration,
}

struct Sample {
    timestamp: Instant,
    stack_trace: Vec<Frame>,
    cpu_time: Duration,
    memory_usage: usize,
}

impl Profiler {
    fn new(sampling_interval: Duration) -> Self {
        Self {
            samples: Arc::new(Mutex::new(Vec::new())),
            sampling_interval,
        }
    }

    async fn start_profiling(&self) {
        let samples = Arc::clone(&self.samples);
        let interval = self.sampling_interval;

        tokio::spawn(async move {
            let mut interval_timer = tokio::time::interval(interval);

            loop {
                interval_timer.tick().await;

                // 采集样本
                let sample = Sample {
                    timestamp: Instant::now(),
                    stack_trace: Self::capture_stack_trace(),
                    cpu_time: Self::get_cpu_time(),
                    memory_usage: Self::get_memory_usage(),
                };

                samples.lock().unwrap().push(sample);
            }
        });
    }

    fn generate_flamegraph(&self) -> String {
        let samples = self.samples.lock().unwrap();

        // 聚合调用栈
        let mut stack_counts: HashMap<Vec<String>, usize> = HashMap::new();

        for sample in samples.iter() {
            let stack: Vec<String> = sample.stack_trace
                .iter()
                .map(|f| f.function.clone())
                .collect();

            *stack_counts.entry(stack).or_insert(0) += 1;
        }

        // 生成火焰图格式
        let mut flamegraph = String::new();
        for (stack, count) in stack_counts {
            flamegraph.push_str(&format!("{} {}\n", stack.join(";"), count));
        }

        flamegraph
    }

    fn get_hotspots(&self, top_n: usize) -> Vec<HotSpot> {
        let samples = self.samples.lock().unwrap();

        // 统计函数调用次数和时间
        let mut function_stats: HashMap<String, FunctionStats> = HashMap::new();

        for sample in samples.iter() {
            for frame in &sample.stack_trace {
                let stats = function_stats.entry(frame.function.clone()).or_insert_with(|| FunctionStats {
                    function: frame.function.clone(),
                    count: 0,
                    total_time: Duration::ZERO,
                });

                stats.count += 1;
                stats.total_time += sample.cpu_time;
            }
        }

        // 排序并返回 top N
        let mut hotspots: Vec<HotSpot> = function_stats.values()
            .map(|s| HotSpot {
                function: s.function.clone(),
                percentage: (s.count as f64 / samples.len() as f64) * 100.0,
                total_time: s.total_time,
            })
            .collect();

        hotspots.sort_by(|a, b| b.percentage.partial_cmp(&a.percentage).unwrap());
        hotspots.into_iter().take(top_n).collect()
    }
}

// 使用示例
#[tokio::main]
async fn main() -> Result<()> {
    let profiler = Profiler::new(Duration::from_millis(10));
    profiler.start_profiling().await;

    // 运行程序...
    tokio::time::sleep(Duration::from_secs(60)).await;

    // 分析结果
    let hotspots = profiler.get_hotspots(10);
    for hotspot in hotspots {
        println!("{}: {:.2}%", hotspot.function, hotspot.percentage);
    }

    // 生成火焰图
    let flamegraph = profiler.generate_flamegraph();
    std::fs::write("flamegraph.txt", flamegraph)?;

    Ok(())
}
```

---

## 运行时环境

### OS环境检测

**OS环境检测**识别运行平台:

```rust
use reliability::runtime_environments::*;

#[derive(Debug, Clone, PartialEq)]
enum Platform {
    Linux,
    Windows,
    MacOS,
    FreeBSD,
    Unknown,
}

#[derive(Debug, Clone)]
struct RuntimeEnvironment {
    platform: Platform,
    arch: String,
    os_version: String,
    cpu_count: usize,
    total_memory: u64,
    is_container: bool,
    is_k8s: bool,
    is_wasm: bool,
}

impl RuntimeEnvironment {
    fn detect() -> Result<Self> {
        Ok(Self {
            platform: Self::detect_platform(),
            arch: std::env::consts::ARCH.to_string(),
            os_version: Self::detect_os_version()?,
            cpu_count: num_cpus::get(),
            total_memory: Self::detect_total_memory()?,
            is_container: Self::is_running_in_container()?,
            is_k8s: Self::is_running_in_k8s()?,
            is_wasm: cfg!(target_arch = "wasm32"),
        })
    }

    fn detect_platform() -> Platform {
        #[cfg(target_os = "linux")]
        return Platform::Linux;

        #[cfg(target_os = "windows")]
        return Platform::Windows;

        #[cfg(target_os = "macos")]
        return Platform::MacOS;

        #[cfg(target_os = "freebsd")]
        return Platform::FreeBSD;

        Platform::Unknown
    }

    fn is_running_in_container() -> Result<bool> {
        // 检查 /.dockerenv 文件
        if std::path::Path::new("/.dockerenv").exists() {
            return Ok(true);
        }

        // 检查 cgroup
        if let Ok(cgroup) = std::fs::read_to_string("/proc/1/cgroup") {
            return Ok(cgroup.contains("docker") || cgroup.contains("kubepods"));
        }

        Ok(false)
    }

    fn is_running_in_k8s() -> Result<bool> {
        // 检查 Kubernetes 环境变量
        Ok(std::env::var("KUBERNETES_SERVICE_HOST").is_ok())
    }

    fn detect_total_memory() -> Result<u64> {
        #[cfg(target_os = "linux")]
        {
            let meminfo = std::fs::read_to_string("/proc/meminfo")?;
            for line in meminfo.lines() {
                if line.starts_with("MemTotal:") {
                    let parts: Vec<&str> = line.split_whitespace().collect();
                    if parts.len() >= 2 {
                        return Ok(parts[1].parse::<u64>()? * 1024); // KB to bytes
                    }
                }
            }
        }

        Ok(0)
    }

    fn optimize_for_environment(&self) -> EnvironmentConfig {
        let mut config = EnvironmentConfig::default();

        // 容器环境: 限制资源使用
        if self.is_container {
            config.max_threads = (self.cpu_count / 2).max(1);
            config.max_memory = self.total_memory / 2;
        }

        // K8s环境: 启用健康检查
        if self.is_k8s {
            config.enable_health_check = true;
            config.health_check_port = 8080;
        }

        // Wasm环境: 禁用线程
        if self.is_wasm {
            config.max_threads = 1;
            config.enable_threading = false;
        }

        config
    }
}

// 使用示例
fn main() -> Result<()> {
    let env = RuntimeEnvironment::detect()?;

    println!("Platform: {:?}", env.platform);
    println!("Architecture: {}", env.arch);
    println!("CPUs: {}", env.cpu_count);
    println!("Memory: {} GB", env.total_memory / 1024 / 1024 / 1024);
    println!("Container: {}", env.is_container);
    println!("Kubernetes: {}", env.is_k8s);

    // 根据环境优化配置
    let config = env.optimize_for_environment();
    println!("Optimized config: {:?}", config);

    Ok(())
}
```

### Kubernetes集成

**K8s集成**支持云原生部署:

```rust
use reliability::runtime_environments::k8s::*;

struct K8sIntegration {
    pod_name: String,
    namespace: String,
    service_account: String,
}

impl K8sIntegration {
    fn from_env() -> Result<Self> {
        Ok(Self {
            pod_name: std::env::var("HOSTNAME")?,
            namespace: std::fs::read_to_string("/var/run/secrets/kubernetes.io/serviceaccount/namespace")?,
            service_account: std::env::var("KUBERNETES_SERVICE_ACCOUNT")?,
        })
    }

    async fn register_health_check(&self, port: u16) {
        use axum::{routing::get, Router};

        let app = Router::new()
            .route("/healthz", get(|| async { "ok" }))
            .route("/readyz", get(Self::readiness_check));

        let addr = format!("0.0.0.0:{}", port).parse().unwrap();
        axum::Server::bind(&addr)
            .serve(app.into_make_service())
            .await
            .unwrap();
    }

    async fn readiness_check() -> &'static str {
        // 检查应用是否准备好接收流量
        if Self::is_ready().await {
            "ready"
        } else {
            "not ready"
        }
    }

    async fn watch_config_map(&self, name: &str) -> Result<()> {
        // 监听 ConfigMap 变化
        // 实现略
        Ok(())
    }

    async fn discover_services(&self) -> Result<Vec<Service>> {
        // 服务发现
        // 通过 Kubernetes API 发现其他服务
        Ok(vec![])
    }
}
```

---

## 性能度量

### CPU度量

```rust
use reliability::metrics::cpu::*;

struct CpuMetrics {
    usage_percent: f64,
    user_time: Duration,
    system_time: Duration,
    idle_time: Duration,
}

impl CpuMetrics {
    async fn collect() -> Result<Self> {
        #[cfg(target_os = "linux")]
        {
            let stat = std::fs::read_to_string("/proc/stat")?;
            let first_line = stat.lines().next().unwrap();
            let parts: Vec<u64> = first_line
                .split_whitespace()
                .skip(1)
                .map(|s| s.parse().unwrap())
                .collect();

            let user = parts[0];
            let system = parts[2];
            let idle = parts[3];
            let total = parts.iter().sum::<u64>();

            Ok(Self {
                usage_percent: (1.0 - idle as f64 / total as f64) * 100.0,
                user_time: Duration::from_millis(user * 10),
                system_time: Duration::from_millis(system * 10),
                idle_time: Duration::from_millis(idle * 10),
            })
        }

        #[cfg(not(target_os = "linux"))]
        {
            // 其他平台实现
            Ok(Self::default())
        }
    }
}
```

### 内存度量

```rust
use reliability::metrics::memory::*;

struct MemoryMetrics {
    total: u64,
    available: u64,
    used: u64,
    usage_percent: f64,
    rss: u64,          // Resident Set Size
    heap: u64,         // Heap usage
}

impl MemoryMetrics {
    async fn collect() -> Result<Self> {
        #[cfg(target_os = "linux")]
        {
            // 系统内存
            let meminfo = std::fs::read_to_string("/proc/meminfo")?;
            let mut total = 0;
            let mut available = 0;

            for line in meminfo.lines() {
                if line.starts_with("MemTotal:") {
                    total = line.split_whitespace().nth(1).unwrap().parse::<u64>()? * 1024;
                } else if line.starts_with("MemAvailable:") {
                    available = line.split_whitespace().nth(1).unwrap().parse::<u64>()? * 1024;
                }
            }

            let used = total - available;

            // 进程内存
            let status = std::fs::read_to_string("/proc/self/status")?;
            let mut rss = 0;

            for line in status.lines() {
                if line.starts_with("VmRSS:") {
                    rss = line.split_whitespace().nth(1).unwrap().parse::<u64>()? * 1024;
                }
            }

            Ok(Self {
                total,
                available,
                used,
                usage_percent: (used as f64 / total as f64) * 100.0,
                rss,
                heap: Self::get_heap_usage(),
            })
        }

        #[cfg(not(target_os = "linux"))]
        {
            Ok(Self::default())
        }
    }

    fn get_heap_usage() -> u64 {
        // 使用 jemalloc 或其他分配器的统计信息
        0
    }
}
```

---

## 自适应优化

### 资源预测

```rust
use reliability::self_awareness::resource_predictor::*;

struct ResourcePredictor {
    history: VecDeque<ResourceSample>,
    model: PredictionModel,
}

struct ResourceSample {
    timestamp: Instant,
    cpu_usage: f64,
    memory_usage: u64,
    request_rate: f64,
}

impl ResourcePredictor {
    fn predict_cpu(&self, horizon: Duration) -> f64 {
        // 使用移动平均或ARIMA模型预测
        let recent: Vec<f64> = self.history
            .iter()
            .rev()
            .take(60)
            .map(|s| s.cpu_usage)
            .collect();

        // 简单移动平均
        recent.iter().sum::<f64>() / recent.len() as f64
    }

    fn predict_memory(&self, horizon: Duration) -> u64 {
        // 线性回归预测
        let n = self.history.len();
        if n < 2 {
            return 0;
        }

        let x: Vec<f64> = (0..n).map(|i| i as f64).collect();
        let y: Vec<f64> = self.history.iter().map(|s| s.memory_usage as f64).collect();

        let (slope, intercept) = Self::linear_regression(&x, &y);

        let future_x = n as f64 + horizon.as_secs() as f64;
        (slope * future_x + intercept) as u64
    }

    fn recommend_scaling(&self) -> ScalingRecommendation {
        let predicted_cpu = self.predict_cpu(Duration::from_mins(5));
        let predicted_memory = self.predict_memory(Duration::from_mins(5));

        if predicted_cpu > 80.0 || predicted_memory > 80 * 1024 * 1024 * 1024 {
            ScalingRecommendation::ScaleUp
        } else if predicted_cpu < 20.0 && predicted_memory < 20 * 1024 * 1024 * 1024 {
            ScalingRecommendation::ScaleDown
        } else {
            ScalingRecommendation::NoChange
        }
    }
}
```

---

## 容错机制

### 熔断器

```rust
use reliability::fault_tolerance::circuit_breaker::*;

enum CircuitState {
    Closed,     // 正常状态
    Open,       // 熔断状态
    HalfOpen,   // 半开状态
}

struct CircuitBreaker {
    state: Arc<RwLock<CircuitState>>,
    failure_count: Arc<AtomicU32>,
    success_count: Arc<AtomicU32>,
    config: CircuitBreakerConfig,
}

struct CircuitBreakerConfig {
    failure_threshold: u32,
    success_threshold: u32,
    timeout: Duration,
}

impl CircuitBreaker {
    async fn call<F, T>(&self, f: F) -> Result<T>
    where
        F: FnOnce() -> BoxFuture<'static, Result<T>>,
    {
        let state = *self.state.read().unwrap();

        match state {
            CircuitState::Open => {
                // 熔断状态: 直接返回错误
                Err(anyhow!("Circuit breaker is open"))
            }
            CircuitState::Closed | CircuitState::HalfOpen => {
                // 执行请求
                match f().await {
                    Ok(result) => {
                        self.on_success();
                        Ok(result)
                    }
                    Err(e) => {
                        self.on_failure();
                        Err(e)
                    }
                }
            }
        }
    }

    fn on_success(&self) {
        let count = self.success_count.fetch_add(1, Ordering::SeqCst) + 1;

        let state = *self.state.read().unwrap();
        if matches!(state, CircuitState::HalfOpen) && count >= self.config.success_threshold {
            // 从半开状态转为关闭状态
            *self.state.write().unwrap() = CircuitState::Closed;
            self.failure_count.store(0, Ordering::SeqCst);
            self.success_count.store(0, Ordering::SeqCst);
        }
    }

    fn on_failure(&self) {
        let count = self.failure_count.fetch_add(1, Ordering::SeqCst) + 1;

        if count >= self.config.failure_threshold {
            // 熔断
            *self.state.write().unwrap() = CircuitState::Open;

            // 定时器: timeout 后转为半开状态
            let state = Arc::clone(&self.state);
            let timeout = self.config.timeout;
            tokio::spawn(async move {
                tokio::time::sleep(timeout).await;
                *state.write().unwrap() = CircuitState::HalfOpen;
            });
        }
    }
}

// 使用示例
#[tokio::main]
async fn main() -> Result<()> {
    let circuit_breaker = CircuitBreaker::new(CircuitBreakerConfig {
        failure_threshold: 5,
        success_threshold: 2,
        timeout: Duration::from_secs(30),
    });

    let result = circuit_breaker.call(|| Box::pin(async {
        // 可能失败的操作
        external_service_call().await
    })).await?;

    Ok(())
}
```

### 重试机制

```rust
use reliability::fault_tolerance::retry::*;

struct RetryPolicy {
    max_attempts: u32,
    initial_delay: Duration,
    max_delay: Duration,
    backoff_multiplier: f64,
}

impl RetryPolicy {
    async fn execute<F, T>(&self, mut f: F) -> Result<T>
    where
        F: FnMut() -> BoxFuture<'static, Result<T>>,
    {
        let mut attempts = 0;
        let mut delay = self.initial_delay;

        loop {
            attempts += 1;

            match f().await {
                Ok(result) => return Ok(result),
                Err(e) if attempts >= self.max_attempts => {
                    return Err(anyhow!("Max retry attempts ({}) exceeded: {}", self.max_attempts, e));
                }
                Err(_) => {
                    // 指数退避
                    tokio::time::sleep(delay).await;
                    delay = Duration::from_secs_f64(
                        (delay.as_secs_f64() * self.backoff_multiplier).min(self.max_delay.as_secs_f64())
                    );
                }
            }
        }
    }
}

// 使用示例
#[tokio::main]
async fn main() -> Result<()> {
    let retry_policy = RetryPolicy {
        max_attempts: 3,
        initial_delay: Duration::from_millis(100),
        max_delay: Duration::from_secs(5),
        backoff_multiplier: 2.0,
    };

    let result = retry_policy.execute(|| Box::pin(async {
        unreliable_operation().await
    })).await?;

    Ok(())
}
```

### 限流器

```rust
use reliability::fault_tolerance::rate_limiter::*;

struct RateLimiter {
    tokens: Arc<AtomicU32>,
    capacity: u32,
    refill_rate: f64,  // tokens per second
}

impl RateLimiter {
    fn new(capacity: u32, refill_rate: f64) -> Self {
        let limiter = Self {
            tokens: Arc::new(AtomicU32::new(capacity)),
            capacity,
            refill_rate,
        };

        // 启动补充tokens的任务
        limiter.start_refill_task();

        limiter
    }

    fn start_refill_task(&self) {
        let tokens = Arc::clone(&self.tokens);
        let capacity = self.capacity;
        let refill_rate = self.refill_rate;

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_millis(100));

            loop {
                interval.tick().await;

                let refill_amount = (refill_rate * 0.1) as u32;
                tokens.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |current| {
                    Some((current + refill_amount).min(capacity))
                }).ok();
            }
        });
    }

    async fn acquire(&self, tokens: u32) -> Result<()> {
        loop {
            let current = self.tokens.load(Ordering::SeqCst);

            if current >= tokens {
                if self.tokens.compare_exchange(
                    current,
                    current - tokens,
                    Ordering::SeqCst,
                    Ordering::SeqCst,
                ).is_ok() {
                    return Ok(());
                }
            } else {
                // 等待补充
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        }
    }
}

// 使用示例
#[tokio::main]
async fn main() -> Result<()> {
    let rate_limiter = RateLimiter::new(100, 10.0); // 100 tokens, 10 tokens/s

    for _ in 0..1000 {
        rate_limiter.acquire(1).await?;
        process_request().await?;
    }

    Ok(())
}
```

---

## 最佳实践

### 综合可靠性方案

```rust
use reliability::prelude::*;

struct ReliableService {
    circuit_breaker: CircuitBreaker,
    retry_policy: RetryPolicy,
    rate_limiter: RateLimiter,
    tracer: CallChainTracer,
    metrics: PerformanceMetrics,
}

impl ReliableService {
    async fn call_external_service(&self, request: Request) -> Result<Response> {
        // 1. 限流
        self.rate_limiter.acquire(1).await?;

        // 2. 追踪
        let span = self.tracer.start_span("external_service_call");

        // 3. 熔断器 + 重试
        let result = self.circuit_breaker.call(|| {
            Box::pin(async {
                self.retry_policy.execute(|| {
                    Box::pin(async {
                        // 实际调用
                        let start = Instant::now();
                        let response = external_api_call(&request).await?;

                        // 4. 记录指标
                        self.metrics.record_latency(
                            "external_service",
                            start.elapsed(),
                        ).await;

                        Ok(response)
                    })
                }).await
            })
        }).await;

        // 5. 结束追踪
        self.tracer.end_span(span);

        result
    }
}
```

---

## 完整文档

### 📚 详细文档

reliability crate 包含 **113+ 篇** 详细文档，覆盖:

- **执行流感知** (调用链追踪、执行图、性能剖析)
- **运行时环境** (OS、容器、K8s、嵌入式、Wasm)
- **性能度量** (CPU、内存、I/O、网络)
- **自适应优化** (资源预测、自动调优)
- **容错机制** (熔断器、重试、限流)

访问: [crates/reliability/docs/](../../crates/reliability/docs/)

### 📖 主要文档索引

| 文档 | 说明 | 规模 |
|------|------|------|
| [完整索引](../../crates/reliability/docs/00_MASTER_INDEX.md) | 文档导航 | 完整 |
| [错误处理指南](../../crates/reliability/docs/tier_02_guides/01_错误处理指南.md) | 容错机制 | 详细 |
| [重试与降级](../../crates/reliability/docs/tier_02_guides/02_重试与降级指南.md) | 可靠性模式 | 详细 |
| [监控可观测性](../../crates/reliability/docs/tier_02_guides/04_监控可观测性指南.md) | 度量和追踪 | 详细 |
| [架构概览](../../crates/reliability/docs/architecture/overview.md) | 系统架构 | 完整 |

### 🎯 示例代码

20个完整示例位于 `crates/reliability/examples/`:

```bash
# 运行示例
cd crates/reliability

# 基础示例
cargo run --example reliability_basic_usage

# 容错示例
cargo run --example fault_tolerance_composition

# 环境检测
cargo run --example runtime_environment_example
cargo run --example comprehensive_environment_demo

# 分布式系统
cargo run --example distributed_microservices_showcase
cargo run --example raft_consensus_demo

# Rust 1.90 特性
cargo run --example rust_190_features_demo

# 更多示例
cargo run --example monitoring_dashboard
cargo run --example enhanced_anomaly_detection
```

---

## 🔗 相关资源

### 项目文档

- [返回 Crates 总览](README.md)
- [libraries 使用指南](libraries_guide.md)
- [model 使用指南](model_guide.md)
- [otlp 使用指南](otlp_guide.md)

### 架构文档

- [架构重组计划](../CRATES_ARCHITECTURE_REORG_2025_10_26.md)
- [知识图谱](../CRATES_KNOWLEDGE_GRAPH_2025_10_26.md)
- [矩阵对比](../CRATES_MATRIX_COMPARISON_2025_10_26.md)

### 主文档

- [项目主文档](../README.md)
- [文档导航](../DOCUMENTATION_GUIDE.md)
- [快速开始](../01_GETTING_STARTED/README.md)

---

## 🤝 贡献

欢迎贡献！

1. **添加新功能**: 补充更多运行时支持
2. **改进文档**: 完善使用指南和最佳实践
3. **提供示例**: 分享实际项目经验
4. **报告问题**: 反馈使用中的问题

详见: [贡献指南](../guides/CONTRIBUTING.md)

---

**最后更新**: 2025年10月26日
**文档版本**: v1.0.0
**维护状态**: 🔄 持续维护中
