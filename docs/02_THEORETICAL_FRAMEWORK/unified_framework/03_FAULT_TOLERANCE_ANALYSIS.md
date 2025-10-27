# OTLP 统一理论框架 - 第三部分

**版本**: 2.0  
**创建日期**: 2025年10月26日  
**前置**: 第一、二部分  
**状态**: 🟢 活跃维护

> **简介**: 统一理论框架第三部分 - 容错、排错、监测、控制、分析和故障定位。

---

## 目录

- [OTLP 统一理论框架 - 第三部分](#otlp-统一理论框架---第三部分)
  - [目录](#目录)
  - [第五部分: 容错、排错、监测、控制、分析、定位](#第五部分-容错排错监测控制分析定位)
    - [5.1 故障模型与分类](#51-故障模型与分类)
      - [5.1.1 故障层次结构](#511-故障层次结构)
      - [5.1.2 故障检测理论](#512-故障检测理论)
    - [5.2 容错机制的形式化](#52-容错机制的形式化)
      - [5.2.1 冗余技术](#521-冗余技术)
      - [5.2.2 重试与指数退避](#522-重试与指数退避)
      - [5.2.3 断路器模式](#523-断路器模式)
    - [5.3 错误检测算法](#53-错误检测算法)
      - [5.3.1 异常检测方法](#531-异常检测方法)
    - [5.4 根因分析与故障定位](#54-根因分析与故障定位)
      - [5.4.1 根因分析理论](#541-根因分析理论)

## 第五部分: 容错、排错、监测、控制、分析、定位

### 5.1 故障模型与分类

#### 5.1.1 故障层次结构

```text
【故障-错误-失效链】

Fault (故障) → Error (错误) → Failure (失效)

Fault: 系统的异常状态或缺陷
  例如: 硬件损坏、软件bug、配置错误

Error: 故障导致的系统状态偏差
  例如: 变量值错误、内存泄漏

Failure: 系统无法提供预期服务
  例如: 服务宕机、响应超时

【形式化定义】

System State = Correct | Erroneous | Failed

状态转移:
  Correct --[fault_activation]--> Erroneous
  Erroneous --[error_propagation]--> Failed
  Failed --[recovery]--> Correct | Erroneous

【故障分类】

按持续时间:
  - Transient (瞬时): 短暂出现后消失
  - Intermittent (间歇): 周期性出现
  - Permanent (永久): 持续存在

按来源:
  - Hardware: 硬件损坏
  - Software: 代码bug
  - Network: 网络问题
  - Human: 人为错误

按影响范围:
  - Local: 影响单个组件
  - Global: 影响整个系统

按行为:
  - Crash: 停止工作
  - Omission: 遗漏操作
  - Timing: 时序错误
  - Byzantine: 任意错误行为

【OTLP故障模型】

在OTLP中,故障表现为:

SpanFailure = {
  span: Span where span.status = ERROR,
  fault_type: FaultType,
  error_message: String,
  stack_trace: Option[StackTrace],
  recovery_action: Option[RecoveryAction]
}

FaultType = NetworkFailure
          | Timeout
          | ResourceExhaustion
          | SoftwareBug
          | ConfigurationError
          | DependencyFailure
```

#### 5.1.2 故障检测理论

```text
【故障检测器】

FailureDetector = (Suspects, Trusts, Accuracy, Completeness)

Suspects: 被怀疑故障的进程集合
Trusts: 被信任的进程集合

【故障检测器分类】

Perfect Failure Detector (P):
  - Strong Completeness: 最终检测所有崩溃进程
  - Strong Accuracy: 永不错误怀疑正确进程

Eventually Perfect (◇P):
  - Strong Completeness: 最终检测所有崩溃进程
  - Eventual Strong Accuracy: 最终不再错误怀疑

Eventually Strong (◇S):
  - Weak Completeness: 至少一个正确进程检测所有崩溃
  - Eventual Weak Accuracy: 最终存在一个进程不被怀疑

Weak (W):
  - Weak Completeness
  - Weak Accuracy

【FLP不可能性的回避】

FLP证明了在异步系统中,即使有一个进程可能崩溃,
确定性共识也无法解决。

但是:
  Consensus + ◇S = Solvable!

故障检测器提供了回避FLP的方法

【OTLP中的故障检测】
```

```rust
/// 故障检测器
pub struct FailureDetector {
    tracer: Tracer,
    suspects: Arc<RwLock<HashSet<NodeId>>>,
    heartbeat_timeout: Duration,
    last_heartbeat: Arc<RwLock<HashMap<NodeId, Instant>>>,
}

impl FailureDetector {
    /// 心跳检测
    pub async fn monitor(&self, nodes: Vec<NodeId>) -> Result<(), OtlpError> {
        let mut span = self.tracer.start_span("failure_detection");
        span.set_attribute("monitored_nodes", nodes.len() as i64);
        
        loop {
            for node in &nodes {
                let last_hb = self.last_heartbeat.read().await.get(node).copied();
                
                match last_hb {
                    Some(time) if time.elapsed() > self.heartbeat_timeout => {
                        // 超时,怀疑故障
                        self.suspects.write().await.insert(*node);
                        
                        span.add_event("node_suspected", vec![
                            ("node_id", node.to_string().into()),
                            ("elapsed_ms", time.elapsed().as_millis().to_string().into()),
                        ]);
                    }
                    None => {
                        // 首次监控
                        self.last_heartbeat.write().await.insert(*node, Instant::now());
                    }
                    _ => {
                        // 正常
                    }
                }
            }
            
            tokio::time::sleep(Duration::from_secs(1)).await;
        }
    }
    
    /// 接收心跳
    pub async fn receive_heartbeat(&self, node: NodeId) {
        let mut span = self.tracer.start_span("heartbeat_received");
        span.set_attribute("node_id", node.to_string());
        
        // 更新最后心跳时间
        self.last_heartbeat.write().await.insert(node, Instant::now());
        
        // 从怀疑列表移除
        if self.suspects.write().await.remove(&node) {
            span.add_event("node_recovered", vec![]);
        }
    }
    
    /// 查询是否怀疑某个节点
    pub async fn is_suspected(&self, node: NodeId) -> bool {
        self.suspects.read().await.contains(&node)
    }
    
    /// 获取所有存活节点
    pub async fn alive_nodes(&self, all_nodes: &[NodeId]) -> Vec<NodeId> {
        let suspects = self.suspects.read().await;
        all_nodes.iter()
            .filter(|n| !suspects.contains(n))
            .copied()
            .collect()
    }
}

/// 自适应故障检测器 (Chen et al.)
pub struct AdaptiveFailureDetector {
    tracer: Tracer,
    phi_threshold: f64,  // φ阈值
    arrival_intervals: VecDeque<Duration>,
    window_size: usize,
}

impl AdaptiveFailureDetector {
    /// 计算φ值
    fn calculate_phi(&self, time_since_last: Duration) -> f64 {
        let mean = self.mean_interval();
        let std_dev = self.std_deviation();
        
        let prob = normal_cdf((time_since_last.as_secs_f64() - mean) / std_dev);
        -f64::log10(1.0 - prob)
    }
    
    /// 判断是否故障
    pub async fn is_failed(&self, node: NodeId) -> bool {
        let last_hb = get_last_heartbeat(node);
        let phi = self.calculate_phi(last_hb.elapsed());
        
        let mut span = self.tracer.start_span("adaptive_failure_detection");
        span.set_attribute("node_id", node.to_string());
        span.set_attribute("phi_value", phi);
        span.set_attribute("threshold", self.phi_threshold);
        
        phi > self.phi_threshold
    }
}
```

### 5.2 容错机制的形式化

#### 5.2.1 冗余技术

```text
【冗余分类】

信息冗余(Information Redundancy):
  - 校验和(Checksum)
  - 循环冗余校验(CRC)
  - 纠删码(Erasure Coding)
  - 前向纠错(FEC)

时间冗余(Time Redundancy):
  - 重试(Retry)
  - 超时(Timeout)

空间冗余(Space Redundancy):
  - 主备复制(Primary-Backup)
  - 状态机复制(State Machine Replication)
  - N版本编程(N-Version Programming)

【N版本编程】

运行N个不同实现的程序,投票决定结果:

result = vote([impl₁(input), impl₂(input), ..., implₙ(input)])

假设:
  - 不同实现的失效独立
  - 多数实现正确

【状态机复制】

将服务建模为确定性状态机:

StateMachine = (States, Inputs, Outputs, δ, λ, s₀)

δ: States × Inputs → States  (状态转移)
λ: States × Inputs → Outputs (输出函数)

复制多份:
  SM₁, SM₂, ..., SMₙ

保证:
  1. 所有副本收到相同的输入序列
  2. 输入顺序一致
  3. 确定性执行

结果:
  所有副本的状态和输出完全一致

【OTLP中的复制追踪】
```

```rust
/// 状态机复制追踪
pub struct StateMachineReplicationTracer {
    tracer: Tracer,
    replica_id: ReplicaId,
}

impl StateMachineReplicationTracer {
    /// 追踪状态转移
    pub async fn trace_transition(
        &self,
        input: &Input,
        state_before: &State,
        state_after: &State,
        output: &Output,
    ) -> Result<(), OtlpError> {
        let mut span = self.tracer.start_span("sm_transition");
        span.set_attribute("replica_id", self.replica_id.to_string());
        span.set_attribute("input", input.to_string());
        span.set_attribute("state_before", state_before.hash());
        span.set_attribute("state_after", state_after.hash());
        span.set_attribute("output", output.to_string());
        
        // 记录状态变化
        span.add_event("state_changed", vec![
            ("changed_fields", state_diff(state_before, state_after).into()),
        ]);
        
        Ok(())
    }
    
    /// 验证副本一致性
    pub async fn verify_consistency(
        &self,
        replicas: &[ReplicaId],
    ) -> Result<ConsistencyReport, OtlpError> {
        let mut span = self.tracer.start_span("verify_replication_consistency");
        span.set_attribute("replica_count", replicas.len() as i64);
        
        // 收集所有副本的状态
        let mut states = Vec::new();
        for replica in replicas {
            let state = get_replica_state(*replica).await?;
            states.push((replica, state));
        }
        
        // 比较状态哈希
        let mut consistent = true;
        let first_hash = states[0].1.hash();
        
        for (replica, state) in &states {
            let hash = state.hash();
            if hash != first_hash {
                consistent = false;
                span.add_event("inconsistency_detected", vec![
                    ("replica", replica.to_string().into()),
                    ("expected_hash", first_hash.into()),
                    ("actual_hash", hash.into()),
                ]);
            }
        }
        
        span.set_attribute("consistent", consistent);
        
        Ok(ConsistencyReport { consistent, states })
    }
}

/// 纠删码追踪
pub struct ErasureCodingTracer {
    tracer: Tracer,
    n: usize,  // 总块数
    k: usize,  // 数据块数(n-k为冗余块)
}

impl ErasureCodingTracer {
    /// 编码数据
    pub async fn encode(&self, data: &[u8]) -> Result<Vec<Block>, OtlpError> {
        let mut span = self.tracer.start_span("erasure_encode");
        span.set_attribute("data_size", data.len() as i64);
        span.set_attribute("n", self.n as i64);
        span.set_attribute("k", self.k as i64);
        span.set_attribute("redundancy_ratio", ((self.n - self.k) as f64 / self.k as f64));
        
        let encoder = ReedSolomon::new(self.k, self.n - self.k)?;
        let blocks = encoder.encode(data)?;
        
        span.set_attribute("block_count", blocks.len() as i64);
        Ok(blocks)
    }
    
    /// 解码数据 (可容忍最多n-k个块丢失)
    pub async fn decode(&self, blocks: Vec<Option<Block>>) -> Result<Vec<u8>, OtlpError> {
        let mut span = self.tracer.start_span("erasure_decode");
        
        let available = blocks.iter().filter(|b| b.is_some()).count();
        let missing = blocks.len() - available;
        
        span.set_attribute("total_blocks", blocks.len() as i64);
        span.set_attribute("available_blocks", available as i64);
        span.set_attribute("missing_blocks", missing as i64);
        
        if available < self.k {
            span.add_event("decode_failed", vec![
                ("reason", "insufficient_blocks".into()),
                ("required", self.k.to_string().into()),
                ("available", available.to_string().into()),
            ]);
            return Err(OtlpError::InsufficientBlocks);
        }
        
        let decoder = ReedSolomon::new(self.k, self.n - self.k)?;
        let data = decoder.reconstruct(&blocks)?;
        
        span.set_attribute("decoded_size", data.len() as i64);
        Ok(data)
    }
}
```

#### 5.2.2 重试与指数退避

```text
【重试策略】

固定延迟重试:
  retry_delay = constant

线性退避:
  retry_delay(n) = base_delay × n

指数退避:
  retry_delay(n) = base_delay × backoff_factor^n

指数退避+抖动:
  retry_delay(n) = base_delay × backoff_factor^n × (1 + jitter)
  jitter ∈ [-0.5, 0.5]

【形式化定义】

RetryPolicy = (max_attempts, delay_function, should_retry)

max_attempts: ℕ
delay_function: ℕ → Duration
should_retry: Error → Bool

retry_execution: (RetryPolicy, Operation) → Result
retry_execution(policy, op) = 
  attempt(op, 0, policy)

attempt(op, n, policy) =
  if n >= policy.max_attempts then
    Err(MaxRetriesExceeded)
  else
    match op() {
      Ok(result) => Ok(result)
      Err(e) if policy.should_retry(e) =>
        sleep(policy.delay_function(n))
        attempt(op, n+1, policy)
      Err(e) => Err(e)
    }

【重试预算(Retry Budget)】

限制总重试比例,避免重试风暴:

retry_budget = total_requests × max_retry_ratio

if current_retries > retry_budget then
  reject_new_retries()
```

实现:

```rust
/// 智能重试器
pub struct IntelligentRetrier {
    tracer: Tracer,
    policy: RetryPolicy,
    retry_budget: Arc<RwLock<RetryBudget>>,
}

#[derive(Clone)]
pub struct RetryPolicy {
    pub max_attempts: usize,
    pub base_delay: Duration,
    pub backoff_factor: f64,
    pub max_delay: Duration,
    pub jitter: bool,
}

impl RetryPolicy {
    /// 计算第n次重试的延迟
    pub fn delay(&self, attempt: usize) -> Duration {
        let mut delay = self.base_delay.as_millis() as f64
            * self.backoff_factor.powi(attempt as i32);
        
        if self.jitter {
            let jitter = rand::thread_rng().gen_range(-0.5..=0.5);
            delay *= 1.0 + jitter;
        }
        
        let delay = Duration::from_millis(delay as u64);
        delay.min(self.max_delay)
    }
    
    /// 判断错误是否可重试
    pub fn is_retryable(&self, error: &OtlpError) -> bool {
        match error {
            OtlpError::NetworkFailure(_) => true,
            OtlpError::Timeout => true,
            OtlpError::ServiceUnavailable => true,
            OtlpError::TooManyRequests => true,
            _ => false,
        }
    }
}

impl IntelligentRetrier {
    /// 执行操作with重试
    pub async fn execute<F, T, E>(&self, operation: F) -> Result<T, OtlpError>
    where
        F: Fn() -> Future<Output = Result<T, E>>,
        E: Into<OtlpError>,
    {
        let mut span = self.tracer.start_span("retry_execution");
        span.set_attribute("max_attempts", self.policy.max_attempts as i64);
        
        for attempt in 0..self.policy.max_attempts {
            // 检查重试预算
            if !self.retry_budget.write().await.can_retry() {
                span.add_event("retry_budget_exceeded", vec![]);
                return Err(OtlpError::RetryBudgetExceeded);
            }
            
            span.add_event("attempt_started", vec![
                ("attempt_number", (attempt + 1).to_string().into()),
            ]);
            
            match operation().await {
                Ok(result) => {
                    span.set_attribute("attempts_used", (attempt + 1) as i64);
                    span.add_event("operation_succeeded", vec![]);
                    return Ok(result);
                }
                Err(e) => {
                    let error: OtlpError = e.into();
                    
                    span.add_event("attempt_failed", vec![
                        ("attempt", (attempt + 1).to_string().into()),
                        ("error", error.to_string().into()),
                    ]);
                    
                    // 检查是否可重试
                    if !self.policy.is_retryable(&error) {
                        span.add_event("error_not_retryable", vec![]);
                        return Err(error);
                    }
                    
                    // 最后一次尝试失败
                    if attempt == self.policy.max_attempts - 1 {
                        span.add_event("max_attempts_reached", vec![]);
                        return Err(error);
                    }
                    
                    // 计算退避延迟
                    let delay = self.policy.delay(attempt);
                    span.add_event("backing_off", vec![
                        ("delay_ms", delay.as_millis().to_string().into()),
                    ]);
                    
                    // 消耗重试预算
                    self.retry_budget.write().await.consume();
                    
                    tokio::time::sleep(delay).await;
                }
            }
        }
        
        Err(OtlpError::MaxRetriesExceeded)
    }
}

/// 重试预算管理
pub struct RetryBudget {
    total_requests: AtomicU64,
    retry_requests: AtomicU64,
    max_retry_ratio: f64,
}

impl RetryBudget {
    pub fn can_retry(&self) -> bool {
        let total = self.total_requests.load(Ordering::Relaxed);
        let retries = self.retry_requests.load(Ordering::Relaxed);
        
        if total == 0 {
            return true;
        }
        
        (retries as f64 / total as f64) < self.max_retry_ratio
    }
    
    pub fn consume(&self) {
        self.retry_requests.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn record_request(&self) {
        self.total_requests.fetch_add(1, Ordering::Relaxed);
    }
}
```

#### 5.2.3 断路器模式

```text
【断路器状态机】

States = {Closed, Open, HalfOpen}

Closed (关闭):
  - 正常请求通过
  - 记录失败次数
  - 失败率超过阈值 → Open

Open (开启):
  - 快速失败,拒绝所有请求
  - 超时后 → HalfOpen

HalfOpen (半开):
  - 允许少量请求通过
  - 成功 → Closed
  - 失败 → Open

【状态转移】

                    failure_threshold_exceeded
        Closed ---------------------------------> Open
          ↑                                        |
          |                                        |
          | success                     timeout    |
          |                                        ↓
        HalfOpen <--------------------------------┘

【形式化定义】

CircuitBreaker = (State, FailureCount, Threshold, Timeout)

transition: State × Event → State

transition(Closed, Failure) =
  if failure_count + 1 > threshold then Open
  else Closed

transition(Open, Timeout) = HalfOpen

transition(HalfOpen, Success) = Closed

transition(HalfOpen, Failure) = Open
```

实现:

```rust
/// 断路器
pub struct CircuitBreaker {
    tracer: Tracer,
    state: Arc<RwLock<CircuitState>>,
    config: CircuitBreakerConfig,
    metrics: Arc<CircuitBreakerMetrics>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum CircuitState {
    Closed,
    Open { opened_at: Instant },
    HalfOpen { allowed_requests: usize },
}

pub struct CircuitBreakerConfig {
    pub failure_threshold: usize,
    pub success_threshold: usize,
    pub timeout: Duration,
    pub half_open_max_requests: usize,
}

pub struct CircuitBreakerMetrics {
    pub total_requests: AtomicU64,
    pub successful_requests: AtomicU64,
    pub failed_requests: AtomicU64,
    pub rejected_requests: AtomicU64,
}

impl CircuitBreaker {
    /// 执行操作(受断路器保护)
    pub async fn call<F, T>(&self, operation: F) -> Result<T, OtlpError>
    where
        F: FnOnce() -> Future<Output = Result<T, OtlpError>>,
    {
        let mut span = self.tracer.start_span("circuit_breaker_call");
        
        // 检查当前状态
        let state = self.state.read().await.clone();
        span.set_attribute("circuit_state", format!("{:?}", state));
        
        match state {
            CircuitState::Open { opened_at } => {
                // 检查是否该转换到半开状态
                if opened_at.elapsed() >= self.config.timeout {
                    self.transition_to_half_open().await;
                    span.add_event("transitioned_to_half_open", vec![]);
                    // 递归调用,现在是半开状态
                    return self.call(operation).await;
                } else {
                    // 断路器开启,快速失败
                    self.metrics.rejected_requests.fetch_add(1, Ordering::Relaxed);
                    span.add_event("request_rejected", vec![
                        ("reason", "circuit_open".into()),
                    ]);
                    return Err(OtlpError::CircuitBreakerOpen);
                }
            }
            
            CircuitState::HalfOpen { allowed_requests } => {
                if allowed_requests >= self.config.half_open_max_requests {
                    // 半开状态下请求数已达上限
                    self.metrics.rejected_requests.fetch_add(1, Ordering::Relaxed);
                    span.add_event("request_rejected", vec![
                        ("reason", "half_open_limit".into()),
                    ]);
                    return Err(OtlpError::CircuitBreakerOpen);
                }
                
                // 允许请求通过
                *self.state.write().await = CircuitState::HalfOpen {
                    allowed_requests: allowed_requests + 1,
                };
            }
            
            CircuitState::Closed => {
                // 正常状态,请求通过
            }
        }
        
        // 执行操作
        self.metrics.total_requests.fetch_add(1, Ordering::Relaxed);
        let result = operation().await;
        
        match result {
            Ok(value) => {
                self.on_success().await;
                span.add_event("operation_succeeded", vec![]);
                Ok(value)
            }
            Err(e) => {
                self.on_failure().await;
                span.add_event("operation_failed", vec![
                    ("error", e.to_string().into()),
                ]);
                Err(e)
            }
        }
    }
    
    /// 成功回调
    async fn on_success(&self) {
        self.metrics.successful_requests.fetch_add(1, Ordering::Relaxed);
        
        let mut state = self.state.write().await;
        match *state {
            CircuitState::HalfOpen { .. } => {
                // 半开状态下成功,转换到关闭
                *state = CircuitState::Closed;
                let mut span = self.tracer.start_span("circuit_closed");
                span.add_event("circuit_recovered", vec![]);
            }
            _ => {}
        }
    }
    
    /// 失败回调
    async fn on_failure(&self) {
        self.metrics.failed_requests.fetch_add(1, Ordering::Relaxed);
        
        let mut state = self.state.write().await;
        let should_open = self.should_open_circuit();
        
        match *state {
            CircuitState::Closed if should_open => {
                *state = CircuitState::Open { opened_at: Instant::now() };
                let mut span = self.tracer.start_span("circuit_opened");
                span.add_event("circuit_breaker_triggered", vec![
                    ("failure_rate", self.failure_rate().to_string().into()),
                ]);
            }
            CircuitState::HalfOpen { .. } => {
                // 半开状态下失败,立即打开
                *state = CircuitState::Open { opened_at: Instant::now() };
                let mut span = self.tracer.start_span("circuit_reopened");
                span.add_event("half_open_failed", vec![]);
            }
            _ => {}
        }
    }
    
    fn should_open_circuit(&self) -> bool {
        let total = self.metrics.total_requests.load(Ordering::Relaxed);
        let failed = self.metrics.failed_requests.load(Ordering::Relaxed);
        
        if total < 10 {
            // 样本量太小
            return false;
        }
        
        failed >= self.config.failure_threshold as u64
    }
    
    fn failure_rate(&self) -> f64 {
        let total = self.metrics.total_requests.load(Ordering::Relaxed);
        let failed = self.metrics.failed_requests.load(Ordering::Relaxed);
        
        if total == 0 {
            0.0
        } else {
            failed as f64 / total as f64
        }
    }
    
    async fn transition_to_half_open(&self) {
        *self.state.write().await = CircuitState::HalfOpen { allowed_requests: 0 };
    }
}
```

### 5.3 错误检测算法

#### 5.3.1 异常检测方法

```text
【统计方法】

1. 基于阈值:
   anomaly(x) ⟺ x > μ + k×σ
   
   μ: 均值
   σ: 标准差
   k: 阈值倍数(通常k=3)

2. 四分位距(IQR):
   anomaly(x) ⟺ x < Q₁ - 1.5×IQR ∨ x > Q₃ + 1.5×IQR
   
   Q₁: 第一四分位数
   Q₃: 第三四分位数
   IQR = Q₃ - Q₁

3. Z-Score:
   z = (x - μ) / σ
   anomaly(x) ⟺ |z| > threshold

【机器学习方法】

1. Isolation Forest:
   - 随机选择特征和分割点
   - 异常点更快被孤立
   - 路径长度短 → 异常

2. One-Class SVM:
   - 学习正常数据的边界
   - 边界外 → 异常

3. Autoencoder:
   - 训练重构正常数据
   - 重构误差大 → 异常

【时序异常检测】

1. 移动平均(MA):
   MA_t = (x_{t-n+1} + ... + x_t) / n
   anomaly(x_t) ⟺ |x_t - MA_t| > threshold

2. ARIMA模型:
   预测未来值,实际值偏离预测 → 异常

3. LSTM:
   学习时序模式,预测下一个值
```

实现:

```rust
/// 异常检测器
pub struct AnomalyDetector {
    tracer: Tracer,
    method: DetectionMethod,
}

pub enum DetectionMethod {
    Statistical(StatisticalConfig),
    MachineLearning(MLModel),
    Hybrid,
}

pub struct StatisticalConfig {
    pub window_size: usize,
    pub threshold_factor: f64,
}

impl AnomalyDetector {
    /// 统计方法异常检测
    pub async fn detect_statistical(
        &self,
        metrics: &[f64],
        config: &StatisticalConfig,
    ) -> Vec<Anomaly> {
        let mut span = self.tracer.start_span("statistical_anomaly_detection");
        span.set_attribute("metric_count", metrics.len() as i64);
        span.set_attribute("window_size", config.window_size as i64);
        
        let mut anomalies = Vec::new();
        
        for i in config.window_size..metrics.len() {
            let window = &metrics[i - config.window_size..i];
            
            // 计算统计量
            let mean = window.iter().sum::<f64>() / window.len() as f64;
            let variance = window.iter()
                .map(|x| (x - mean).powi(2))
                .sum::<f64>() / window.len() as f64;
            let std_dev = variance.sqrt();
            
            // Z-Score检测
            let current = metrics[i];
            let z_score = (current - mean) / std_dev;
            
            if z_score.abs() > config.threshold_factor {
                anomalies.push(Anomaly {
                    index: i,
                    value: current,
                    expected: mean,
                    deviation: z_score,
                    severity: Self::calculate_severity(z_score),
                });
                
                span.add_event("anomaly_detected", vec![
                    ("index", i.to_string().into()),
                    ("value", current.to_string().into()),
                    ("z_score", z_score.to_string().into()),
                ]);
            }
        }
        
        span.set_attribute("anomaly_count", anomalies.len() as i64);
        anomalies
    }
    
    /// 使用Isolation Forest
    pub async fn detect_ml(
        &self,
        features: &[Vec<f64>],
    ) -> Vec<Anomaly> {
        let mut span = self.tracer.start_span("ml_anomaly_detection");
        span.set_attribute("sample_count", features.len() as i64);
        
        // 训练Isolation Forest
        let forest = IsolationForest::new(100, 256);  // 100棵树,样本大小256
        forest.fit(features);
        
        // 预测异常分数
        let mut anomalies = Vec::new();
        for (i, feature_vec) in features.iter().enumerate() {
            let anomaly_score = forest.anomaly_score(feature_vec);
            
            if anomaly_score > 0.5 {  // 阈值
                anomalies.push(Anomaly {
                    index: i,
                    value: feature_vec[0],  // 主要特征
                    expected: 0.0,          // ML方法无明确期望值
                    deviation: anomaly_score,
                    severity: Self::calculate_severity(anomaly_score),
                });
            }
        }
        
        span.set_attribute("anomaly_count", anomalies.len() as i64);
        anomalies
    }
    
    fn calculate_severity(score: f64) -> Severity {
        match score.abs() {
            s if s > 5.0 => Severity::Critical,
            s if s > 4.0 => Severity::High,
            s if s > 3.0 => Severity::Medium,
            _ => Severity::Low,
        }
    }
}

/// 多维异常检测
pub struct MultiDimensionalAnomalyDetector {
    tracer: Tracer,
}

impl MultiDimensionalAnomalyDetector {
    /// 马氏距离异常检测
    pub async fn detect_mahalanobis(
        &self,
        data: &[Vec<f64>],
    ) -> Vec<Anomaly> {
        let mut span = self.tracer.start_span("mahalanobis_anomaly_detection");
        
        // 计算均值向量
        let mean = self.calculate_mean(data);
        
        // 计算协方差矩阵
        let covariance = self.calculate_covariance(data, &mean);
        
        // 计算逆矩阵
        let inv_cov = covariance.try_inverse()
            .ok_or(OtlpError::SingularMatrix)?;
        
        let mut anomalies = Vec::new();
        
        for (i, point) in data.iter().enumerate() {
            // 计算马氏距离
            let diff = DVector::from_vec(
                point.iter().zip(&mean).map(|(x, m)| x - m).collect()
            );
            let distance = (&diff.transpose() * &inv_cov * &diff)[(0, 0)].sqrt();
            
            // 卡方分布检验
            let threshold = chi_squared_quantile(point.len(), 0.95);
            
            if distance > threshold {
                anomalies.push(Anomaly {
                    index: i,
                    value: distance,
                    expected: threshold,
                    deviation: distance - threshold,
                    severity: Self::calculate_severity((distance - threshold) / threshold),
                });
            }
        }
        
        span.set_attribute("anomaly_count", anomalies.len() as i64);
        Ok(anomalies)
    }
}
```

### 5.4 根因分析与故障定位

#### 5.4.1 根因分析理论

```text
【根因分析方法】

1. 5 Whys:
   重复问"为什么"5次,找到根本原因

2. 鱼骨图(Ishikawa):
   从问题出发,分析可能的原因类别

3. 故障树分析(FTA):
   从顶层失效逆向推导可能的原因组合

4. 因果图(Causal Graph):
   建立变量间的因果关系图

【因果推断】

Pearl因果模型:

CausalModel = (V, E, P)

V: 变量集合
E: 因果边 (X → Y表示X是Y的原因)
P: 概率分布

do-演算:
  P(Y | do(X=x)) ≠ P(Y | X=x)
  
  do(X=x): 干预,强制设置X=x
  观察 vs 干预

【结构因果模型(SCM)】

每个变量由其父变量和噪声决定:

Y = f_Y(Pa(Y), U_Y)

Pa(Y): Y的父变量
U_Y: 外生噪声

【反事实推理】

"如果X没有发生,Y会怎样?"

Y_{X←x'} = f_Y(x', other_parents, U_Y)

【OTLP中的因果分析】
```

实现:

```rust
/// 根因分析器
pub struct RootCauseAnalyzer {
    tracer: Tracer,
}

impl RootCauseAnalyzer {
    /// 构建因果图
    pub async fn build_causal_graph(&self, trace: &Trace) -> CausalGraph {
        let mut span = self.tracer.start_span("build_causal_graph");
        span.set_attribute("span_count", trace.spans.len() as i64);
        
        let mut graph = CausalGraph::new();
        
        // 添加所有span作为节点
        for span in &trace.spans {
            graph.add_node(span.span_id, SpanNode {
                span_id: span.span_id,
                name: span.name.clone(),
                status: span.status.clone(),
                duration: span.end_time - span.start_time,
                attributes: span.attributes.clone(),
            });
        }
        
        // 添加因果边
        for span in &trace.spans {
            // Parent-child: 明确的因果关系
            if let Some(parent_id) = span.parent_span_id {
                graph.add_edge(
                    parent_id,
                    span.span_id,
                    CausalEdge::ParentChild,
                    1.0,  // 确定性
                );
            }
            
            // 同步调用: 强因果关系
            for link in &span.links {
                graph.add_edge(
                    link.span_context.span_id,
                    span.span_id,
                    CausalEdge::SyncCall,
                    0.9,  // 高度相关
                );
            }
            
            // 时序关系: 弱因果关系
            for other in &trace.spans {
                if span.span_id != other.span_id &&
                   same_service(span, other) &&
                   span.end_time < other.start_time &&
                   other.start_time - span.end_time < Duration::from_secs(1) {
                    let correlation = self.calculate_correlation(span, other);
                    if correlation > 0.5 {
                        graph.add_edge(
                            span.span_id,
                            other.span_id,
                            CausalEdge::Temporal,
                            correlation,
                        );
                    }
                }
            }
        }
        
        span.set_attribute("edge_count", graph.edge_count() as i64);
        graph
    }
    
    /// 找到故障的根因
    pub async fn find_root_cause(
        &self,
        trace: &Trace,
        failure_span: SpanId,
    ) -> Vec<RootCause> {
        let mut span = self.tracer.start_span("root_cause_analysis");
        span.set_attribute("failure_span", failure_span.to_string());
        
        // 构建因果图
        let causal_graph = self.build_causal_graph(trace).await;
        
        // 找到所有祖先节点(潜在根因)
        let ancestors = causal_graph.ancestors(failure_span);
        
        span.set_attribute("potential_causes", ancestors.len() as i64);
        
        // 评分每个潜在根因
        let mut candidates = Vec::new();
        for ancestor_id in ancestors {
            let ancestor_span = trace.find_span(ancestor_id)?;
            
            let score = self.score_root_cause(
                ancestor_span,
                failure_span,
                &causal_graph,
            );
            
            candidates.push(RootCause {
                span_id: ancestor_id,
                span: ancestor_span.clone(),
                confidence: score,
                explanation: self.explain_causation(ancestor_span, failure_span),
            });
        }
        
        // 按置信度排序
        candidates.sort_by(|a, b| b.confidence.partial_cmp(&a.confidence).unwrap());
        
        // 记录前3个根因
        for (i, cause) in candidates.iter().take(3).enumerate() {
            span.add_event("root_cause_candidate", vec![
                ("rank", (i + 1).to_string().into()),
                ("span_id", cause.span_id.to_string().into()),
                ("confidence", cause.confidence.to_string().into()),
                ("span_name", cause.span.name.clone().into()),
            ]);
        }
        
        Ok(candidates)
    }
    
    /// 评分根因候选
    fn score_root_cause(
        &self,
        cause_span: &Span,
        effect_span: SpanId,
        graph: &CausalGraph,
    ) -> f64 {
        let mut score = 0.0;
        
        // 1. 时序得分: 原因必须先于结果
        if cause_span.end_time < effect_span.start_time {
            score += 0.3;
        }
        
        // 2. 因果路径强度
        let path_strength = graph.path_strength(cause_span.span_id, effect_span);
        score += 0.4 * path_strength;
        
        // 3. 错误传播
        if cause_span.status == SpanStatus::Error {
            score += 0.3;
        }
        
        // 4. 异常属性
        if self.has_abnormal_attributes(cause_span) {
            score += 0.2;
        }
        
        score.min(1.0)
    }
    
    /// 计算两个span的相关性
    fn calculate_correlation(&self, span1: &Span, span2: &Span) -> f64 {
        let mut correlation = 0.0;
        
        // 检查共同属性
        let common_keys: HashSet<_> = span1.attributes.keys()
            .filter(|k| span2.attributes.contains_key(*k))
            .collect();
        
        correlation += 0.3 * (common_keys.len() as f64 / span1.attributes.len().max(1) as f64);
        
        // 检查service关系
        if same_service(span1, span2) {
            correlation += 0.3;
        }
        
        // 检查时序接近性
        let time_gap = (span2.start_time - span1.end_time).as_millis() as f64;
        correlation += 0.2 * (-time_gap / 1000.0).exp();  // 指数衰减
        
        // 检查错误传播
        if span1.status == SpanStatus::Error && span2.status == SpanStatus::Error {
            correlation += 0.2;
        }
        
        correlation.min(1.0)
    }
}

/// 程序切片(Program Slicing)
pub struct ProgramSlicer {
    tracer: Tracer,
}

impl ProgramSlicer {
    /// 计算后向切片(找到影响某个点的所有语句)
    pub async fn backward_slice(
        &self,
        trace: &Trace,
        target_span: SpanId,
        variable: &str,
    ) -> Vec<SpanId> {
        let mut span = self.tracer.start_span("backward_slice");
        span.set_attribute("target_span", target_span.to_string());
        span.set_attribute("variable", variable);
        
        let mut slice = Vec::new();
        let mut worklist = vec![target_span];
        let mut visited = HashSet::new();
        
        while let Some(current) = worklist.pop() {
            if visited.contains(&current) {
                continue;
            }
            visited.insert(current);
            
            let current_span = trace.find_span(current)?;
            
            // 检查当前span是否写入目标变量
            if writes_variable(current_span, variable) {
                slice.push(current);
                
                // 添加所有读取的变量到工作列表
                for read_var in reads_variables(current_span) {
                    let defs = find_definitions(trace, current, &read_var);
                    worklist.extend(defs);
                }
            }
            
            // 添加前驱节点
            if let Some(parent) = current_span.parent_span_id {
                worklist.push(parent);
            }
        }
        
        span.set_attribute("slice_size", slice.len() as i64);
        Ok(slice)
    }
    
    /// 计算前向切片(找到受某个点影响的所有语句)
    pub async fn forward_slice(
        &self,
        trace: &Trace,
        source_span: SpanId,
        variable: &str,
    ) -> Vec<SpanId> {
        let mut span = self.tracer.start_span("forward_slice");
        span.set_attribute("source_span", source_span.to_string());
        span.set_attribute("variable", variable);
        
        let mut slice = Vec::new();
        let mut worklist = vec![(source_span, variable.to_string())];
        let mut visited = HashSet::new();
        
        while let Some((current, var)) = worklist.pop() {
            if visited.contains(&(current, var.clone())) {
                continue;
            }
            visited.insert((current, var.clone()));
            
            let current_span = trace.find_span(current)?;
            
            // 检查当前span是否使用该变量
            if reads_variable(current_span, &var) {
                slice.push(current);
                
                // 添加所有写入的变量到工作列表
                for write_var in writes_variables(current_span) {
                    let uses = find_uses(trace, current, &write_var);
                    for use_span in uses {
                        worklist.push((use_span, write_var.clone()));
                    }
                }
            }
            
            // 添加后继节点
            for child in children(trace, current) {
                worklist.push((child, var.clone()));
            }
        }
        
        span.set_attribute("slice_size", slice.len() as i64);
        Ok(slice)
    }
}
```

---

**（待续: 第四部分将包含Rust异步映射、多维度数据分析和自动化运维）**-

本文档第三部分建立了:

- 完整的故障模型和分类体系
- 故障检测理论和实现
- 各种容错机制(冗余、重试、断路器)的形式化和实现
- 异常检测算法(统计和机器学习方法)
- 根因分析和故障定位方法

这为构建高可靠性的OTLP系统提供了理论基础和实践指导。
