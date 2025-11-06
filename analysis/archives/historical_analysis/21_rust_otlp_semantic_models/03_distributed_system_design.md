# 分布式系统设计模型与 OTLP 集成论证

## 📋 目录

- [分布式系统设计模型与 OTLP 集成论证](#分布式系统设计模型与-otlp-集成论证)
  - [📋 目录](#-目录)
  - [分布式可观测性架构](#分布式可观测性架构)
    - [核心架构理念](#核心架构理念)
    - [系统层次架构](#系统层次架构)
    - [Rust 实现框架](#rust-实现框架)
  - [Agent-Gateway-Backend 三层模型](#agent-gateway-backend-三层模型)
    - [Agent 层设计 (边缘节点)](#agent-层设计-边缘节点)
      - [职责](#职责)
      - [Rust 实现](#rust-实现)
    - [Gateway 层设计 (中心聚合)](#gateway-层设计-中心聚合)
      - [职责1](#职责1)
      - [Rust 实现1](#rust-实现1)
    - [Backend 层设计 (存储与分析)](#backend-层设计-存储与分析)
  - [边缘计算与本地决策](#边缘计算与本地决策)
    - [边缘计算模型](#边缘计算模型)
    - [实时异常检测实现](#实时异常检测实现)
      - [EWMA (指数加权移动平均)](#ewma-指数加权移动平均)
      - [Z-Score 异常检测](#z-score-异常检测)
    - [本地决策引擎](#本地决策引擎)
  - [OTTL 数据平面可编程性](#ottl-数据平面可编程性)
    - [OTTL 语法概览](#ottl-语法概览)
    - [Rust OTTL 解释器设计](#rust-ottl-解释器设计)
    - [OTTL 实际应用场景](#ottl-实际应用场景)
      - [1. 敏感数据脱敏](#1-敏感数据脱敏)
      - [2. 降维聚合](#2-降维聚合)
  - [OPAMP 控制平面动态管理](#opamp-控制平面动态管理)
    - [OPAMP 协议核心消息](#opamp-协议核心消息)
    - [OPAMP 客户端实现](#opamp-客户端实现)
    - [配置热更新示例](#配置热更新示例)
  - [自我运维系统设计](#自我运维系统设计)
    - [完整闭环](#完整闭环)
    - [Rust 实现2](#rust-实现2)
  - [分布式一致性模型](#分布式一致性模型)
    - [因果一致性 (Causal Consistency)](#因果一致性-causal-consistency)
  - [总结](#总结)
    - [下一步](#下一步)

---

## 分布式可观测性架构

### 核心架构理念

**从"被动监控"到"主动自治"**:

```text
传统监控模式:
    采集 → 传输 → 存储 → 查询 → 人工分析 → 人工决策

OTLP 自我运维模式:
    采集 → [边缘分析] → 传输 → [中心分析] → 自动决策 → 自动执行
          ↑                                  ↓
          └──────────── 控制反馈 ────────────┘
```

### 系统层次架构

```text
┌───────────────────────────────────────────────────────────────┐
│                      应用层 (Application)                      │
│  微服务 A | 微服务 B | 微服务 C | ... | 微服务 N                │
└───────────────────────────────────────────────────────────────┘
                              │
                              ↓ OTLP (gRPC/HTTP)
┌───────────────────────────────────────────────────────────────┐
│                   边缘层 (Edge - Agent)                        │
│  ┌──────────────────────────────────────────────────────────┐ │
│  │ • 本地聚合 (Aggregation)                                  │ │
│  │ • 采样控制 (Sampling)                                     │ │
│  │ • 边缘分析 (Edge Analytics)                               │ │
│  │ • 本地决策 (Local Decision)                               │ │
│  │ • WASM/Lua 过滤器                                         │ │
│  └──────────────────────────────────────────────────────────┘ │
└───────────────────────────────────────────────────────────────┘
                              │
                              ↓ OTLP
┌───────────────────────────────────────────────────────────────┐
│                  中心层 (Central - Gateway)                    │
│  ┌──────────────────────────────────────────────────────────┐ │
│  │ • 全局聚合 (Global Aggregation)                           │ │
│  │ • 智能路由 (Smart Routing)                                │ │
│  │ • 负载均衡 (Load Balancing)                               │ │
│  │ • 协议转换 (Protocol Translation)                         │ │
│  │ • 全局策略 (Global Policy)                                │ │
│  └──────────────────────────────────────────────────────────┘ │
└───────────────────────────────────────────────────────────────┘
                              │
                              ↓
┌───────────────────────────────────────────────────────────────┐
│                   存储层 (Storage - Backend)                  │
│  ┌────────────┬────────────┬────────────┬──────────────────┐  │
│  │   Jaeger   │ Prometheus │    ELK     │   ClickHouse     │  │
│  │  (Traces)  │ (Metrics)  │   (Logs)   │ (All Signals)    │  │
│  └────────────┴────────────┴────────────┴──────────────────┘  │
└───────────────────────────────────────────────────────────────┘
                              │
                              ↓
┌───────────────────────────────────────────────────────────────┐
│                  分析层 (Analytics & AI)                       │
│  • 异常检测 (Anomaly Detection)                                │
│  • 根因分析 (Root Cause Analysis)                              │
│  • 预测性维护 (Predictive Maintenance)                         │
│  • 容量规划 (Capacity Planning)                                │
└───────────────────────────────────────────────────────────────┘
```

### Rust 实现框架

```rust
/// 分布式可观测性系统架构
pub struct ObservabilitySystem {
    /// 边缘层 - Agent
    agent: Arc<OtlpAgent>,

    /// 中心层 - Gateway
    gateway: Option<Arc<OtlpGateway>>,

    /// 控制平面 - OPAMP
    control_plane: Arc<OpampClient>,

    /// 配置
    config: Arc<RwLock<SystemConfig>>,
}

impl ObservabilitySystem {
    /// 启动完整系统
    pub async fn start(&self) -> Result<(), Error> {
        // 1. 启动 Agent (边缘层)
        self.agent.start().await?;

        // 2. 启动 Gateway (如果是中心节点)
        if let Some(gateway) = &self.gateway {
            gateway.start().await?;
        }

        // 3. 连接 OPAMP 控制平面
        self.control_plane.connect().await?;

        // 4. 启动健康检查
        self.start_health_check().await;

        Ok(())
    }
}
```

---

## Agent-Gateway-Backend 三层模型

### Agent 层设计 (边缘节点)

#### 职责

1. **数据收集**: 接收应用发送的遥测数据
2. **本地处理**: 聚合、采样、过滤
3. **边缘分析**: 实时异常检测
4. **本地决策**: 自动限流、降级
5. **数据上报**: 发送到 Gateway

#### Rust 实现

```rust
use tokio::sync::mpsc;
use std::sync::Arc;

/// OTLP Agent (DaemonSet 模式)
pub struct OtlpAgent {
    /// 接收器 - 从应用接收数据
    receiver: mpsc::Receiver<TelemetryData>,

    /// 发送器 - 向 Gateway 发送数据
    gateway_client: Arc<GatewayClient>,

    /// 本地处理器
    processor: Arc<LocalProcessor>,

    /// 边缘分析器
    analyzer: Arc<EdgeAnalyzer>,

    /// 配置
    config: Arc<RwLock<AgentConfig>>,
}

impl OtlpAgent {
    /// 主处理循环
    pub async fn run(&mut self) -> Result<(), Error> {
        let mut batch = Vec::with_capacity(100);
        let mut ticker = tokio::time::interval(Duration::from_secs(5));

        loop {
            tokio::select! {
                // 接收数据
                Some(data) = self.receiver.recv() => {
                    // 1. 本地处理 (采样、过滤)
                    if let Some(processed) = self.processor.process(data).await? {
                        batch.push(processed);
                    }

                    // 2. 边缘分析 (异常检测)
                    self.analyzer.analyze(&batch).await?;

                    // 3. 批量发送
                    if batch.len() >= 100 {
                        self.flush_batch(&mut batch).await?;
                    }
                }

                // 定时发送
                _ = ticker.tick() => {
                    if !batch.is_empty() {
                        self.flush_batch(&mut batch).await?;
                    }
                }
            }
        }
    }

    /// 刷新批次
    async fn flush_batch(&self, batch: &mut Vec<TelemetryData>) -> Result<(), Error> {
        self.gateway_client.send_batch(batch.clone()).await?;
        batch.clear();
        Ok(())
    }
}

/// 本地处理器
pub struct LocalProcessor {
    /// 采样器
    sampler: Arc<Sampler>,

    /// 过滤器
    filters: Vec<Box<dyn Filter + Send + Sync>>,
}

impl LocalProcessor {
    /// 处理单条数据
    pub async fn process(&self, data: TelemetryData) -> Result<Option<TelemetryData>, Error> {
        // 1. 采样决策
        if !self.sampler.should_sample(&data) {
            return Ok(None);
        }

        // 2. 应用过滤器
        let mut data = data;
        for filter in &self.filters {
            data = match filter.apply(data).await? {
                Some(d) => d,
                None => return Ok(None), // 被过滤掉
            };
        }

        Ok(Some(data))
    }
}

/// 边缘分析器 (实时异常检测)
pub struct EdgeAnalyzer {
    /// EWMA 异常检测
    ewma_detector: Arc<EwmaDetector>,

    /// 决策引擎
    decision_engine: Arc<DecisionEngine>,
}

impl EdgeAnalyzer {
    /// 分析批次数据
    pub async fn analyze(&self, batch: &[TelemetryData]) -> Result<(), Error> {
        for data in batch {
            // 提取指标
            if let Some(metric) = extract_latency_metric(data) {
                // 异常检测
                if self.ewma_detector.is_anomaly(metric).await {
                    // 触发本地决策
                    self.decision_engine.handle_anomaly(data).await?;
                }
            }
        }
        Ok(())
    }
}
```

### Gateway 层设计 (中心聚合)

#### 职责1

1. **全局聚合**: 汇总多个 Agent 的数据
2. **智能路由**: 根据规则路由到不同后端
3. **负载均衡**: 分散后端压力
4. **协议转换**: OTLP → Jaeger/Prometheus
5. **全局策略**: 下发采样率、过滤规则

#### Rust 实现1

```rust
/// OTLP Gateway (Deployment 模式)
pub struct OtlpGateway {
    /// gRPC 服务器
    grpc_server: Arc<GrpcServer>,

    /// HTTP 服务器
    http_server: Arc<HttpServer>,

    /// 路由器
    router: Arc<Router>,

    /// 后端连接池
    backends: Arc<RwLock<Vec<Backend>>>,

    /// 全局聚合器
    aggregator: Arc<GlobalAggregator>,
}

impl OtlpGateway {
    /// 启动 Gateway
    pub async fn start(&self) -> Result<(), Error> {
        // 1. 启动 gRPC 服务器 (4317)
        let grpc_handle = {
            let server = self.grpc_server.clone();
            tokio::spawn(async move {
                server.serve().await
            })
        };

        // 2. 启动 HTTP 服务器 (4318)
        let http_handle = {
            let server = self.http_server.clone();
            tokio::spawn(async move {
                server.serve().await
            })
        };

        // 3. 启动聚合任务
        let aggregator_handle = {
            let aggregator = self.aggregator.clone();
            tokio::spawn(async move {
                aggregator.run().await
            })
        };

        // 等待所有任务
        tokio::try_join!(grpc_handle, http_handle, aggregator_handle)?;

        Ok(())
    }
}

/// 智能路由器
pub struct Router {
    /// 路由规则
    rules: Arc<RwLock<Vec<RoutingRule>>>,
}

impl Router {
    /// 路由决策
    pub async fn route(&self, data: &TelemetryData) -> Result<Vec<BackendId>, Error> {
        let rules = self.rules.read().await;
        let mut targets = Vec::new();

        for rule in rules.iter() {
            if rule.matches(data) {
                targets.push(rule.backend_id.clone());
            }
        }

        Ok(targets)
    }
}

/// 路由规则 (支持 OTTL 表达式)
pub struct RoutingRule {
    /// 规则名称
    name: String,

    /// 匹配条件 (OTTL 表达式)
    condition: String,

    /// 目标后端
    backend_id: BackendId,

    /// 优先级
    priority: u32,
}

impl RoutingRule {
    /// 判断数据是否匹配规则
    pub fn matches(&self, data: &TelemetryData) -> bool {
        // 使用 OTTL 引擎评估条件
        // 例如: resource.attributes["service.name"] == "payment-service"
        ottl_eval(&self.condition, data).unwrap_or(false)
    }
}
```

### Backend 层设计 (存储与分析)

```rust
/// 后端抽象
#[async_trait]
pub trait Backend: Send + Sync {
    /// 发送数据
    async fn send(&self, data: Vec<TelemetryData>) -> Result<(), Error>;

    /// 健康检查
    async fn health_check(&self) -> Result<bool, Error>;
}

/// Jaeger 后端
pub struct JaegerBackend {
    endpoint: String,
    client: Arc<JaegerClient>,
}

#[async_trait]
impl Backend for JaegerBackend {
    async fn send(&self, data: Vec<TelemetryData>) -> Result<(), Error> {
        // 转换为 Jaeger 格式
        let spans = convert_to_jaeger_spans(data);
        self.client.send_batch(spans).await
    }

    async fn health_check(&self) -> Result<bool, Error> {
        self.client.ping().await
    }
}

/// Prometheus Remote Write 后端
pub struct PrometheusBackend {
    endpoint: String,
    client: Arc<reqwest::Client>,
}

#[async_trait]
impl Backend for PrometheusBackend {
    async fn send(&self, data: Vec<TelemetryData>) -> Result<(), Error> {
        // 转换为 Prometheus Remote Write 格式
        let timeseries = convert_to_prometheus(data);

        // 使用 Snappy 压缩
        let compressed = snappy_compress(&timeseries);

        // 发送
        self.client
            .post(&self.endpoint)
            .header("Content-Encoding", "snappy")
            .header("Content-Type", "application/x-protobuf")
            .body(compressed)
            .send()
            .await?;

        Ok(())
    }

    async fn health_check(&self) -> Result<bool, Error> {
        let resp = self.client.get(&self.endpoint).send().await?;
        Ok(resp.status().is_success())
    }
}
```

---

## 边缘计算与本地决策

### 边缘计算模型

**目标**: 在 Agent 层完成"感知 → 分析 → 决策 → 执行"闭环

```text
应用 Pod
    ↓ 发送遥测数据
Agent (DaemonSet)
    ├─ 实时分析 (< 100ms)
    ├─ 异常检测 (EWMA, Z-score)
    ├─ 本地决策
    │   ├─ CPU 过高 → 限流
    │   ├─ 内存泄漏 → 重启容器
    │   └─ 请求失败率高 → 降级
    └─ 自动执行
        ├─ iptables 规则
        ├─ kubectl 命令
        └─ 发送告警
```

### 实时异常检测实现

#### EWMA (指数加权移动平均)

```rust
/// EWMA 异常检测器
pub struct EwmaDetector {
    /// 平滑因子 (α)
    alpha: f64,

    /// 当前 EWMA 值
    ewma: Arc<RwLock<f64>>,

    /// 阈值 (标准差倍数)
    threshold: f64,
}

impl EwmaDetector {
    pub fn new(alpha: f64, threshold: f64) -> Self {
        Self {
            alpha,
            ewma: Arc::new(RwLock::new(0.0)),
            threshold,
        }
    }

    /// 更新并检测异常
    pub async fn is_anomaly(&self, value: f64) -> bool {
        let mut ewma = self.ewma.write().await;

        // 计算新的 EWMA
        let new_ewma = self.alpha * value + (1.0 - self.alpha) * *ewma;

        // 计算偏差
        let deviation = (value - new_ewma).abs();

        // 更新 EWMA
        *ewma = new_ewma;

        // 判断是否异常
        deviation > self.threshold * new_ewma
    }
}
```

#### Z-Score 异常检测

```rust
/// Z-Score 异常检测器
pub struct ZScoreDetector {
    /// 滑动窗口
    window: Arc<RwLock<VecDeque<f64>>>,

    /// 窗口大小
    window_size: usize,

    /// Z-Score 阈值 (通常 2.5 或 3.0)
    threshold: f64,
}

impl ZScoreDetector {
    /// 检测异常
    pub async fn is_anomaly(&self, value: f64) -> bool {
        let mut window = self.window.write().await;

        // 添加新值
        window.push_back(value);
        if window.len() > self.window_size {
            window.pop_front();
        }

        // 计算均值和标准差
        let mean = window.iter().sum::<f64>() / window.len() as f64;
        let variance = window.iter()
            .map(|x| (x - mean).powi(2))
            .sum::<f64>() / window.len() as f64;
        let std_dev = variance.sqrt();

        // 计算 Z-Score
        let z_score = ((value - mean) / std_dev).abs();

        z_score > self.threshold
    }
}
```

### 本地决策引擎

```rust
/// 决策引擎
pub struct DecisionEngine {
    /// 决策规则
    rules: Arc<RwLock<Vec<DecisionRule>>>,

    /// 执行器
    executor: Arc<ActionExecutor>,
}

/// 决策规则
pub struct DecisionRule {
    /// 规则名称
    name: String,

    /// 触发条件
    condition: Condition,

    /// 执行动作
    action: Action,

    /// 冷却时间 (避免频繁触发)
    cooldown: Duration,

    /// 上次执行时间
    last_executed: Arc<RwLock<Option<Instant>>>,
}

/// 条件
pub enum Condition {
    /// CPU 使用率超过阈值
    CpuAbove(f64),

    /// 内存使用率超过阈值
    MemoryAbove(f64),

    /// 请求错误率超过阈值
    ErrorRateAbove(f64),

    /// 请求延迟超过阈值
    LatencyAbove(Duration),
}

/// 动作
pub enum Action {
    /// 限流 (通过 iptables)
    RateLimit { port: u16, rate: u32 },

    /// 重启容器
    RestartContainer { pod_name: String },

    /// 发送告警
    SendAlert { severity: AlertSeverity, message: String },

    /// 降级服务
    Degrade { feature: String },
}

impl DecisionEngine {
    /// 处理异常
    pub async fn handle_anomaly(&self, data: &TelemetryData) -> Result<(), Error> {
        let rules = self.rules.read().await;

        for rule in rules.iter() {
            // 检查条件是否满足
            if self.check_condition(&rule.condition, data).await {
                // 检查冷却时间
                let last_executed = rule.last_executed.read().await;
                if let Some(last) = *last_executed {
                    if last.elapsed() < rule.cooldown {
                        continue; // 还在冷却期
                    }
                }
                drop(last_executed);

                // 执行动作
                self.executor.execute(&rule.action).await?;

                // 更新执行时间
                let mut last_executed = rule.last_executed.write().await;
                *last_executed = Some(Instant::now());

                tracing::info!(
                    "Decision rule executed: {}, action: {:?}",
                    rule.name,
                    rule.action
                );
            }
        }

        Ok(())
    }

    /// 检查条件
    async fn check_condition(&self, condition: &Condition, data: &TelemetryData) -> bool {
        match condition {
            Condition::CpuAbove(threshold) => {
                extract_cpu_usage(data)
                    .map(|cpu| cpu > *threshold)
                    .unwrap_or(false)
            }
            Condition::ErrorRateAbove(threshold) => {
                calculate_error_rate(data)
                    .map(|rate| rate > *threshold)
                    .unwrap_or(false)
            }
            _ => false,
        }
    }
}

/// 动作执行器
pub struct ActionExecutor;

impl ActionExecutor {
    /// 执行动作
    pub async fn execute(&self, action: &Action) -> Result<(), Error> {
        match action {
            Action::RateLimit { port, rate } => {
                self.apply_rate_limit(*port, *rate).await
            }
            Action::RestartContainer { pod_name } => {
                self.restart_pod(pod_name).await
            }
            Action::SendAlert { severity, message } => {
                self.send_alert(*severity, message).await
            }
            Action::Degrade { feature } => {
                self.degrade_feature(feature).await
            }
        }
    }

    /// 应用限流 (iptables)
    async fn apply_rate_limit(&self, port: u16, rate: u32) -> Result<(), Error> {
        let output = tokio::process::Command::new("iptables")
            .args(&[
                "-A", "INPUT",
                "-p", "tcp",
                "--dport", &port.to_string(),
                "-m", "limit",
                "--limit", &format!("{}/s", rate),
                "-j", "ACCEPT"
            ])
            .output()
            .await?;

        if !output.status.success() {
            return Err(Error::ExecutionFailed("iptables command failed".into()));
        }

        Ok(())
    }

    /// 重启 Pod (kubectl)
    async fn restart_pod(&self, pod_name: &str) -> Result<(), Error> {
        let output = tokio::process::Command::new("kubectl")
            .args(&["delete", "pod", pod_name])
            .output()
            .await?;

        if !output.status.success() {
            return Err(Error::ExecutionFailed("kubectl command failed".into()));
        }

        Ok(())
    }
}
```

---

## OTTL 数据平面可编程性

### OTTL 语法概览

```text
statement = condition ">" action

condition = boolean_expression
action = set(...) | keep_keys(...) | limit(...) | drop(...)

path = resource.attributes.x | metric.name | span.status.code
```

### Rust OTTL 解释器设计

```rust
/// OTTL 语句
pub struct OttlStatement {
    /// 条件表达式
    condition: Option<Expression>,

    /// 动作
    action: Action,
}

/// 表达式
pub enum Expression {
    /// 字面量
    Literal(Value),

    /// 路径访问
    Path(Vec<String>),

    /// 二元操作
    Binary {
        left: Box<Expression>,
        op: BinaryOp,
        right: Box<Expression>,
    },

    /// 函数调用
    Function {
        name: String,
        args: Vec<Expression>,
    },
}

/// 二元操作符
pub enum BinaryOp {
    Eq,    // ==
    Ne,    // !=
    Lt,    // <
    Gt,    // >
    And,   // &&
    Or,    // ||
}

/// OTTL 动作
pub enum OttlAction {
    /// 设置字段
    Set { path: Vec<String>, value: Expression },

    /// 保留指定键
    KeepKeys { paths: Vec<Vec<String>> },

    /// 限制数组大小
    Limit { path: Vec<String>, max: usize },

    /// 删除
    Drop,
}

/// OTTL 解释器
pub struct OttlInterpreter {
    /// 已注册的函数
    functions: HashMap<String, Box<dyn OttlFunction + Send + Sync>>,
}

impl OttlInterpreter {
    /// 执行 OTTL 语句
    pub fn execute(&self, stmt: &OttlStatement, data: &mut TelemetryData) -> Result<bool, Error> {
        // 1. 评估条件
        let should_execute = if let Some(condition) = &stmt.condition {
            self.eval_expression(condition, data)?.as_bool()?
        } else {
            true
        };

        // 2. 执行动作
        if should_execute {
            self.execute_action(&stmt.action, data)?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// 评估表达式
    fn eval_expression(&self, expr: &Expression, data: &TelemetryData) -> Result<Value, Error> {
        match expr {
            Expression::Literal(v) => Ok(v.clone()),

            Expression::Path(path) => {
                self.resolve_path(path, data)
            }

            Expression::Binary { left, op, right } => {
                let left_val = self.eval_expression(left, data)?;
                let right_val = self.eval_expression(right, data)?;
                self.eval_binary_op(&left_val, op, &right_val)
            }

            Expression::Function { name, args } => {
                let func = self.functions.get(name)
                    .ok_or(Error::UnknownFunction(name.clone()))?;

                let arg_values: Result<Vec<_>, _> = args.iter()
                    .map(|arg| self.eval_expression(arg, data))
                    .collect();

                func.call(&arg_values?)
            }
        }
    }

    /// 解析路径
    fn resolve_path(&self, path: &[String], data: &TelemetryData) -> Result<Value, Error> {
        // 例如: resource.attributes.service.name
        match path.as_slice() {
            ["resource", "attributes", key] => {
                data.resource_attributes
                    .get(*key)
                    .cloned()
                    .ok_or(Error::PathNotFound)
            }
            ["span", "name"] => {
                if let TelemetryContent::Trace(trace) = &data.content {
                    Ok(Value::String(trace.name.clone()))
                } else {
                    Err(Error::TypeMismatch)
                }
            }
            _ => Err(Error::InvalidPath),
        }
    }
}

/// OTTL 函数 trait
pub trait OttlFunction {
    fn call(&self, args: &[Value]) -> Result<Value, Error>;
}

/// SHA256 函数
pub struct Sha256Function;

impl OttlFunction for Sha256Function {
    fn call(&self, args: &[Value]) -> Result<Value, Error> {
        if args.len() != 1 {
            return Err(Error::InvalidArguments);
        }

        let input = args[0].as_string()?;
        let hash = sha2::Sha256::digest(input.as_bytes());
        Ok(Value::String(hex::encode(hash)))
    }
}
```

### OTTL 实际应用场景

#### 1. 敏感数据脱敏

```rust
// OTTL 语句:
// set(body, SHA256(body)) where resource.attributes["env"] == "prod"

let stmt = OttlStatement {
    condition: Some(Expression::Binary {
        left: Box::new(Expression::Path(vec![
            "resource".into(),
            "attributes".into(),
            "env".into(),
        ])),
        op: BinaryOp::Eq,
        right: Box::new(Expression::Literal(Value::String("prod".into()))),
    }),
    action: OttlAction::Set {
        path: vec!["body".into()],
        value: Expression::Function {
            name: "SHA256".into(),
            args: vec![Expression::Path(vec!["body".into()])],
        },
    },
};
```

#### 2. 降维聚合

```rust
// OTTL 语句:
// keep_keys(metric.attributes, ["cluster", "node"])

let stmt = OttlStatement {
    condition: None,
    action: OttlAction::KeepKeys {
        paths: vec![
            vec!["metric".into(), "attributes".into(), "cluster".into()],
            vec!["metric".into(), "attributes".into(), "node".into()],
        ],
    },
};
```

---

## OPAMP 控制平面动态管理

### OPAMP 协议核心消息

```rust
/// Agent → Server 心跳
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AgentToServer {
    /// Agent 实例 ID
    pub instance_uid: String,

    /// 配置状态
    pub remote_config_status: Option<RemoteConfigStatus>,

    /// 健康状态
    pub health: AgentHealth,

    /// 能力声明
    pub capabilities: AgentCapabilities,
}

/// Server → Agent 配置下发
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServerToAgent {
    /// 远程配置
    pub remote_config: Option<RemoteConfig>,

    /// 证书更新
    pub certificates: Option<TlsCertificates>,

    /// 二进制包
    pub package_available: Option<PackageAvailable>,
}

/// 远程配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RemoteConfig {
    /// 配置内容 (YAML/JSON)
    pub config: serde_json::Value,

    /// 配置哈希 (用于去重)
    pub config_hash: [u8; 32],
}

/// Agent 能力
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AgentCapabilities {
    /// 支持远程配置
    pub accepts_remote_config: bool,

    /// 支持 OTTL
    pub accepts_ottl: bool,

    /// 支持二进制更新
    pub accepts_package: bool,
}
```

### OPAMP 客户端实现

```rust
/// OPAMP 客户端
pub struct OpampClient {
    /// gRPC 客户端
    client: OpampServiceClient<Channel>,

    /// Agent ID
    instance_uid: String,

    /// 当前配置
    current_config: Arc<RwLock<Option<RemoteConfig>>>,

    /// 配置应用回调
    on_config_update: Arc<dyn Fn(RemoteConfig) -> BoxFuture<'static, Result<(), Error>> + Send + Sync>,
}

impl OpampClient {
    /// 启动心跳循环
    pub async fn start_heartbeat(&self) -> Result<(), Error> {
        let mut interval = tokio::time::interval(Duration::from_secs(10));

        loop {
            interval.tick().await;

            // 发送心跳
            let request = AgentToServer {
                instance_uid: self.instance_uid.clone(),
                remote_config_status: self.get_config_status().await,
                health: self.collect_health_metrics().await,
                capabilities: AgentCapabilities {
                    accepts_remote_config: true,
                    accepts_ottl: true,
                    accepts_package: true,
                },
            };

            // 接收响应
            let response = self.client.heartbeat(request).await?;

            // 处理响应
            self.handle_server_response(response).await?;
        }
    }

    /// 处理 Server 响应
    async fn handle_server_response(&self, response: ServerToAgent) -> Result<(), Error> {
        // 1. 处理远程配置
        if let Some(config) = response.remote_config {
            self.apply_remote_config(config).await?;
        }

        // 2. 处理证书更新
        if let Some(certs) = response.certificates {
            self.update_certificates(certs).await?;
        }

        // 3. 处理二进制更新
        if let Some(package) = response.package_available {
            self.upgrade_binary(package).await?;
        }

        Ok(())
    }

    /// 应用远程配置
    async fn apply_remote_config(&self, config: RemoteConfig) -> Result<(), Error> {
        // 检查配置哈希
        let current_config = self.current_config.read().await;
        if let Some(current) = &*current_config {
            if current.config_hash == config.config_hash {
                return Ok(()); // 配置未变化
            }
        }
        drop(current_config);

        // 应用新配置
        (self.on_config_update)(config.clone()).await?;

        // 更新当前配置
        let mut current_config = self.current_config.write().await;
        *current_config = Some(config);

        Ok(())
    }
}
```

### 配置热更新示例

```rust
/// 配置更新处理器
pub struct ConfigUpdateHandler {
    agent: Arc<OtlpAgent>,
}

impl ConfigUpdateHandler {
    /// 处理配置更新
    pub async fn handle(&self, config: RemoteConfig) -> Result<(), Error> {
        // 解析配置
        let agent_config: AgentConfig = serde_json::from_value(config.config)?;

        // 1. 更新采样率
        if let Some(sampling_ratio) = agent_config.sampling_ratio {
            self.agent.update_sampling_ratio(sampling_ratio).await;
        }

        // 2. 更新 OTTL 规则
        if let Some(ottl_rules) = agent_config.ottl_rules {
            self.agent.update_ottl_rules(ottl_rules).await?;
        }

        // 3. 更新后端地址
        if let Some(endpoint) = agent_config.gateway_endpoint {
            self.agent.update_gateway_endpoint(endpoint).await;
        }

        Ok(())
    }
}
```

---

## 自我运维系统设计

### 完整闭环

```text
感知 (Observe)
    ↓ OTLP Trace/Metric/Log
分析 (Analyze)
    ↓ OTTL + Edge Analytics
决策 (Decide)
    ↓ Decision Engine
执行 (Act)
    ↓ Action Executor
配置 (Configure)
    ↓ OPAMP
回到感知 (Loop)
```

### Rust 实现2

```rust
/// 自我运维系统
pub struct SelfOperatingSystem {
    /// 观测层
    observer: Arc<Observer>,

    /// 分析层
    analyzer: Arc<Analyzer>,

    /// 决策层
    decider: Arc<Decider>,

    /// 执行层
    executor: Arc<Executor>,

    /// 配置层
    configurator: Arc<Configurator>,
}

impl SelfOperatingSystem {
    /// 启动自我运维循环
    pub async fn run(&self) -> Result<(), Error> {
        loop {
            // 1. 感知
            let observations = self.observer.collect().await?;

            // 2. 分析
            let insights = self.analyzer.analyze(&observations).await?;

            // 3. 决策
            let decisions = self.decider.decide(&insights).await?;

            // 4. 执行
            for decision in decisions {
                self.executor.execute(decision).await?;
            }

            // 5. 配置反馈
            self.configurator.feedback(&insights).await?;

            // 等待下一轮
            tokio::time::sleep(Duration::from_secs(10)).await;
        }
    }
}
```

---

## 分布式一致性模型

### 因果一致性 (Causal Consistency)

OTLP 的 TraceId/SpanId 天然提供因果关系：

```rust
/// 因果关系保证
pub struct CausalityGuarantee {
    /// 向量时钟
    vector_clock: Arc<RwLock<VectorClock>>,
}

impl CausalityGuarantee {
    /// 记录事件
    pub async fn record_event(&self, span: &Span) {
        let mut clock = self.vector_clock.write().await;
        clock.increment(span.span_id.to_string());
    }

    /// 检查因果关系
    pub async fn happens_before(&self, a: &Span, b: &Span) -> bool {
        // 如果 a 是 b 的祖先，则 a happens-before b
        b.trace_id == a.trace_id && self.is_ancestor(a, b).await
    }
}
```

---

## 总结

本文档论证了基于 OTLP + Rust 构建分布式自我运维系统的完整架构，核心要点：

1. **三层架构**: Agent-Gateway-Backend 分层设计
2. **边缘计算**: 在 Agent 层完成实时分析和本地决策
3. **数据平面**: OTTL 提供可编程的数据处理能力
4. **控制平面**: OPAMP 实现动态配置和灰度发布
5. **自我闭环**: 感知-分析-决策-执行-配置的完整循环

### 下一步

阅读 [04_rust_otlp_libraries.md](./04_rust_otlp_libraries.md) 了解成熟的 Rust OTLP 库实现细节。
