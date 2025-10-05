# SLO/SLA 管理

## 目录

- [SLO/SLA 管理](#slosla-管理)
  - [目录](#目录)
  - [概述](#概述)
  - [SLI/SLO/SLA 定义](#slislosla-定义)
    - [概念区分](#概念区分)
    - [OTLP SLO 定义](#otlp-slo-定义)
  - [错误预算](#错误预算)
    - [错误预算计算](#错误预算计算)
    - [错误预算策略](#错误预算策略)
  - [SLO 监控](#slo-监控)
    - [Prometheus 查询](#prometheus-查询)
    - [Grafana 仪表板](#grafana-仪表板)
  - [SLO 设置方法](#slo-设置方法)
    - [1. 确定 SLI（服务质量指标）](#1-确定-sli服务质量指标)
    - [2. 设定 SLO（服务质量目标）](#2-设定-slo服务质量目标)
    - [3. 制定 SLA（服务质量协议）](#3-制定-sla服务质量协议)
  - [错误预算实践](#错误预算实践)
    - [错误预算燃烧率](#错误预算燃烧率)
    - [错误预算策略1](#错误预算策略1)
  - [实战案例](#实战案例)
    - [案例1：错误预算管理实践](#案例1错误预算管理实践)
    - [案例2：SLO 驱动的发布决策](#案例2slo-驱动的发布决策)
  - [SLO 审查流程](#slo-审查流程)
    - [定期审查](#定期审查)
  - [工具和自动化](#工具和自动化)
    - [SLO 计算脚本](#slo-计算脚本)

## 概述

SLO/SLA 管理确保服务质量满足承诺，平衡可靠性和创新速度。

## SLI/SLO/SLA 定义

### 概念区分

- **SLI** (Service Level Indicator): 服务质量指标
- **SLO** (Service Level Objective): 服务质量目标
- **SLA** (Service Level Agreement): 服务质量协议

### OTLP SLO 定义

```rust
pub struct ServiceLevelObjective {
    pub name: String,
    pub target: f64,           // 目标值 (如 0.999 表示 99.9%)
    pub measurement_window: Duration,
}

pub struct OtlpSLOs {
    pub availability: ServiceLevelObjective,
    pub latency_p99: ServiceLevelObjective,
    pub success_rate: ServiceLevelObjective,
}

impl Default for OtlpSLOs {
    fn default() -> Self {
        Self {
            availability: ServiceLevelObjective {
                name: "Availability".to_string(),
                target: 0.999,  // 99.9%
                measurement_window: Duration::from_secs(30 * 24 * 3600), // 30 days
            },
            latency_p99: ServiceLevelObjective {
                name: "P99 Latency".to_string(),
                target: 0.1,    // 100ms
                measurement_window: Duration::from_secs(24 * 3600), // 1 day
            },
            success_rate: ServiceLevelObjective {
                name: "Success Rate".to_string(),
                target: 0.99,   // 99%
                measurement_window: Duration::from_secs(24 * 3600), // 1 day
            },
        }
    }
}
```

## 错误预算

### 错误预算计算

```rust
pub struct ErrorBudget {
    slo: ServiceLevelObjective,
    total_requests: u64,
    failed_requests: u64,
}

impl ErrorBudget {
    pub fn new(slo: ServiceLevelObjective) -> Self {
        Self {
            slo,
            total_requests: 0,
            failed_requests: 0,
        }
    }

    pub fn record_request(&mut self, success: bool) {
        self.total_requests += 1;
        if !success {
            self.failed_requests += 1;
        }
    }

    /// 计算剩余错误预算
    pub fn remaining_budget(&self) -> i64 {
        if self.total_requests == 0 {
            return 0;
        }

        let allowed_failures = ((1.0 - self.slo.target) * self.total_requests as f64) as i64;
        allowed_failures - self.failed_requests as i64
    }

    /// 错误预算消耗百分比
    pub fn budget_consumption(&self) -> f64 {
        if self.total_requests == 0 {
            return 0.0;
        }

        let allowed_failures = (1.0 - self.slo.target) * self.total_requests as f64;
        if allowed_failures == 0.0 {
            return 100.0;
        }

        (self.failed_requests as f64 / allowed_failures) * 100.0
    }

    /// 当前 SLI 值
    pub fn current_sli(&self) -> f64 {
        if self.total_requests == 0 {
            return 1.0;
        }

        let success_requests = self.total_requests - self.failed_requests;
        success_requests as f64 / self.total_requests as f64
    }

    /// 是否满足 SLO
    pub fn meets_slo(&self) -> bool {
        self.current_sli() >= self.slo.target
    }
}
```

### 错误预算策略

```rust
pub struct ErrorBudgetPolicy {
    budget: ErrorBudget,
}

impl ErrorBudgetPolicy {
    /// 根据错误预算决定是否可以发布
    pub fn can_deploy(&self) -> DeploymentDecision {
        let consumption = self.budget.budget_consumption();

        if consumption > 100.0 {
            DeploymentDecision::Block {
                reason: "错误预算已耗尽".to_string(),
            }
        } else if consumption > 80.0 {
            DeploymentDecision::Caution {
                reason: format!("错误预算剩余 {:.1}%", 100.0 - consumption),
            }
        } else {
            DeploymentDecision::Proceed
        }
    }
}

pub enum DeploymentDecision {
    Proceed,
    Caution { reason: String },
    Block { reason: String },
}
```

## SLO 监控

### Prometheus 查询

```yaml
# 可用性 SLI
- record: slo:availability:ratio_rate30d
  expr: |
    sum(rate(otlp_requests_total{status="success"}[30d]))
    /
    sum(rate(otlp_requests_total[30d]))

# 延迟 SLI (P99 < 100ms 的比例)
- record: slo:latency:good_ratio_rate1d
  expr: |
    sum(rate(otlp_request_duration_bucket{le="0.1"}[1d]))
    /
    sum(rate(otlp_request_duration_count[1d]))

# 错误预算消耗
- record: slo:error_budget:consumption
  expr: |
    (1 - slo:availability:ratio_rate30d) 
    / (1 - 0.999) * 100

# SLO 告警
- alert: SLOBudgetExhausted
  expr: slo:error_budget:consumption > 100
  for: 5m
  labels:
    severity: critical
  annotations:
    summary: "Error budget exhausted"
    description: "SLO error budget has been exceeded"

- alert: SLOBudgetBurning
  expr: slo:error_budget:consumption > 80
  for: 15m
  labels:
    severity: warning
  annotations:
    summary: "Error budget burning fast"
    description: "{{ $value }}% of error budget consumed"
```

### Grafana 仪表板

```json
{
  "dashboard": {
    "title": "OTLP SLO Dashboard",
    "panels": [
      {
        "title": "Availability SLO",
        "targets": [
          {
            "expr": "slo:availability:ratio_rate30d * 100",
            "legendFormat": "Current"
          },
          {
            "expr": "99.9",
            "legendFormat": "Target"
          }
        ]
      },
      {
        "title": "Error Budget Remaining",
        "targets": [
          {
            "expr": "100 - slo:error_budget:consumption",
            "legendFormat": "Remaining %"
          }
        ]
      }
    ]
  }
}
```

## SLO 设置方法

### 1. 确定 SLI（服务质量指标）

**选择原则**：

- 与用户体验直接相关
- 可测量、可量化
- 能够持续监控

**常见 SLI 类型**：

```rust
/// SLI 类型定义
#[derive(Debug, Clone)]
pub enum SliType {
    /// 可用性：成功请求比例
    Availability,
    /// 延迟：请求响应时间
    Latency { percentile: f64 },
    /// 吞吐量：每秒处理请求数
    Throughput,
    /// 错误率：失败请求比例
    ErrorRate,
    /// 数据新鲜度：数据延迟时间
    Freshness,
}

/// SLI 计算器
pub struct SliCalculator {
    sli_type: SliType,
    measurements: Vec<Measurement>,
}

#[derive(Debug, Clone)]
pub struct Measurement {
    timestamp: u64,
    value: f64,
    success: bool,
}

impl SliCalculator {
    pub fn new(sli_type: SliType) -> Self {
        Self {
            sli_type,
            measurements: Vec::new(),
        }
    }

    pub fn add_measurement(&mut self, measurement: Measurement) {
        self.measurements.push(measurement);
    }

    /// 计算当前 SLI 值
    pub fn calculate_sli(&self, window: Duration) -> f64 {
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        let cutoff = now - window.as_secs();
        
        let recent: Vec<_> = self.measurements.iter()
            .filter(|m| m.timestamp >= cutoff)
            .collect();

        if recent.is_empty() {
            return 1.0;
        }

        match self.sli_type {
            SliType::Availability | SliType::ErrorRate => {
                let success_count = recent.iter().filter(|m| m.success).count();
                success_count as f64 / recent.len() as f64
            }
            SliType::Latency { percentile } => {
                let mut values: Vec<f64> = recent.iter().map(|m| m.value).collect();
                values.sort_by(|a, b| a.partial_cmp(b).unwrap());
                let index = ((percentile * values.len() as f64) as usize).min(values.len() - 1);
                values[index]
            }
            _ => 0.0,
        }
    }
}
```

### 2. 设定 SLO（服务质量目标）

**设定步骤**：

1. **分析历史数据**

   ```bash
   # 查询过去30天的可用性
   promtool query instant 'sum(rate(otlp_requests_total{status="success"}[30d])) / sum(rate(otlp_requests_total[30d]))'
   ```

2. **考虑业务需求**
   - 用户期望
   - 竞品水平
   - 成本约束

3. **设置合理目标**

   ```rust
   /// SLO 设置建议
   pub struct SloRecommendation;
   
   impl SloRecommendation {
       /// 根据历史数据推荐 SLO
       pub fn recommend_slo(historical_sli: f64, business_tier: BusinessTier) -> f64 {
           let base_target = match business_tier {
               BusinessTier::Critical => 0.9999,  // 99.99% (4个9)
               BusinessTier::High => 0.999,       // 99.9% (3个9)
               BusinessTier::Medium => 0.99,      // 99% (2个9)
               BusinessTier::Low => 0.95,         // 95%
           };
           
           // 确保目标不超过历史表现
           base_target.min(historical_sli * 0.98) // 留2%缓冲
       }
   }
   
   #[derive(Debug, Clone, Copy)]
   pub enum BusinessTier {
       Critical,
       High,
       Medium,
       Low,
   }
   ```

### 3. 制定 SLA（服务质量协议）

**SLA 模板**：

```markdown
# OTLP 服务级别协议 (SLA)

## 1. 服务范围
本 SLA 适用于 OTLP Collector 服务。

## 2. 服务承诺

### 2.1 可用性
- **承诺**：99.9% 月度可用性
- **测量方法**：成功请求数 / 总请求数
- **排除项**：
  - 计划内维护（提前7天通知）
  - 客户端错误（4xx）
  - 不可抗力

### 2.2 性能
- **P99 延迟**：< 100ms
- **P50 延迟**：< 50ms
- **测量窗口**：24小时滚动窗口

### 2.3 数据完整性
- **数据丢失率**：< 0.01%
- **数据延迟**：< 5秒

## 3. 补偿条款

| 可用性 | 服务积分 |
|--------|----------|
| < 99.9% | 10% |
| < 99.0% | 25% |
| < 95.0% | 50% |

## 4. 支持响应时间

| 优先级 | 首次响应 | 解决时间 |
|--------|----------|----------|
| P0 | 15分钟 | 4小时 |
| P1 | 1小时 | 24小时 |
| P2 | 4小时 | 3天 |
| P3 | 1工作日 | 1周 |
```

## 错误预算实践

### 错误预算燃烧率

**概念**：错误预算消耗的速度

**计算方法**：

```rust
/// 错误预算燃烧率计算器
pub struct BurnRateCalculator {
    window_size: Duration,
    slo_target: f64,
}

impl BurnRateCalculator {
    pub fn new(window_size: Duration, slo_target: f64) -> Self {
        Self {
            window_size,
            slo_target,
        }
    }

    /// 计算燃烧率
    /// 返回值：1.0 表示正常消耗，> 1.0 表示消耗过快
    pub fn calculate_burn_rate(&self, current_error_rate: f64) -> f64 {
        let allowed_error_rate = 1.0 - self.slo_target;
        
        if allowed_error_rate == 0.0 {
            return f64::INFINITY;
        }
        
        current_error_rate / allowed_error_rate
    }

    /// 预测错误预算耗尽时间
    pub fn time_to_exhaustion(&self, current_burn_rate: f64, remaining_budget: f64) -> Duration {
        if current_burn_rate <= 0.0 {
            return Duration::MAX;
        }
        
        let budget_window = self.window_size.as_secs_f64();
        let time_remaining = (remaining_budget / 100.0) * budget_window / current_burn_rate;
        
        Duration::from_secs_f64(time_remaining.max(0.0))
    }
}
```

**多窗口燃烧率告警**：

```yaml
# 快速燃烧（1小时窗口）
- alert: ErrorBudgetFastBurn
  expr: |
    (
      1 - (
        sum(rate(otlp_requests_success_total[1h]))
        /
        sum(rate(otlp_requests_total[1h]))
      )
    ) / (1 - 0.999) > 14.4  # 14.4倍燃烧率
  for: 2m
  labels:
    severity: critical
    burn_rate: fast
  annotations:
    summary: "错误预算快速燃烧"
    description: "按当前速率，错误预算将在 {{ $value }} 小时内耗尽"

# 中速燃烧（6小时窗口）
- alert: ErrorBudgetMediumBurn
  expr: |
    (
      1 - (
        sum(rate(otlp_requests_success_total[6h]))
        /
        sum(rate(otlp_requests_total[6h]))
      )
    ) / (1 - 0.999) > 6  # 6倍燃烧率
  for: 15m
  labels:
    severity: warning
    burn_rate: medium
  annotations:
    summary: "错误预算中速燃烧"

# 慢速燃烧（24小时窗口）
- alert: ErrorBudgetSlowBurn
  expr: |
    (
      1 - (
        sum(rate(otlp_requests_success_total[24h]))
        /
        sum(rate(otlp_requests_total[24h]))
      )
    ) / (1 - 0.999) > 3  # 3倍燃烧率
  for: 1h
  labels:
    severity: warning
    burn_rate: slow
  annotations:
    summary: "错误预算慢速燃烧"
```

### 错误预算策略1

**策略框架**：

```rust
/// 错误预算策略引擎
pub struct ErrorBudgetPolicyEngine {
    policies: Vec<Policy>,
}

#[derive(Debug, Clone)]
pub struct Policy {
    name: String,
    condition: PolicyCondition,
    action: PolicyAction,
}

#[derive(Debug, Clone)]
pub enum PolicyCondition {
    BudgetRemaining { threshold: f64 },
    BurnRate { threshold: f64, window: Duration },
    SloViolation { consecutive_periods: usize },
}

#[derive(Debug, Clone)]
pub enum PolicyAction {
    BlockDeployments,
    RequireApproval,
    AlertTeam { channel: String },
    FreezeChanges,
    EnableSafeMode,
}

impl ErrorBudgetPolicyEngine {
    pub fn new() -> Self {
        Self {
            policies: vec![
                Policy {
                    name: "预算耗尽阻止发布".to_string(),
                    condition: PolicyCondition::BudgetRemaining { threshold: 0.0 },
                    action: PolicyAction::BlockDeployments,
                },
                Policy {
                    name: "预算不足需要审批".to_string(),
                    condition: PolicyCondition::BudgetRemaining { threshold: 20.0 },
                    action: PolicyAction::RequireApproval,
                },
                Policy {
                    name: "快速燃烧告警".to_string(),
                    condition: PolicyCondition::BurnRate {
                        threshold: 10.0,
                        window: Duration::from_secs(3600),
                    },
                    action: PolicyAction::AlertTeam {
                        channel: "#sre-oncall".to_string(),
                    },
                },
            ],
        }
    }

    /// 评估策略
    pub fn evaluate(&self, budget: &ErrorBudget, burn_rate: f64) -> Vec<PolicyAction> {
        let mut actions = Vec::new();
        
        for policy in &self.policies {
            if self.matches_condition(&policy.condition, budget, burn_rate) {
                actions.push(policy.action.clone());
            }
        }
        
        actions
    }

    fn matches_condition(
        &self,
        condition: &PolicyCondition,
        budget: &ErrorBudget,
        burn_rate: f64,
    ) -> bool {
        match condition {
            PolicyCondition::BudgetRemaining { threshold } => {
                let remaining = 100.0 - budget.budget_consumption();
                remaining <= *threshold
            }
            PolicyCondition::BurnRate { threshold, .. } => {
                burn_rate >= *threshold
            }
            _ => false,
        }
    }
}
```

## 实战案例

### 案例1：错误预算管理实践

**场景**：

- 服务：OTLP Collector
- SLO：99.9% 可用性（30天窗口）
- 月初错误预算：43.2分钟（30天 × 0.1%）

**时间线**：

```text
第1周：
- 可用性：99.95%
- 错误预算消耗：50%
- 状态：正常 ✓

第2周：
- 发生故障，可用性降至 99.85%
- 错误预算消耗：150%（超支）
- 行动：
  1. 阻止所有非紧急发布
  2. 启动稳定性改进计划
  3. 每日 SLO 审查会议

第3-4周：
- 专注稳定性，暂停新功能
- 可用性恢复至 99.92%
- 月末累计可用性：99.91%
- 结果：勉强达标，吸取教训
```

**经验教训**：

```rust
/// 错误预算使用报告
pub struct ErrorBudgetReport {
    period: String,
    target_slo: f64,
    actual_sli: f64,
    budget_consumed: f64,
    incidents: Vec<Incident>,
    lessons_learned: Vec<String>,
}

impl ErrorBudgetReport {
    pub fn generate_monthly_report() -> Self {
        Self {
            period: "2025-10".to_string(),
            target_slo: 0.999,
            actual_sli: 0.9991,
            budget_consumed: 150.0,
            incidents: vec![
                Incident {
                    date: "2025-10-08".to_string(),
                    duration_minutes: 45,
                    impact: "数据库连接池耗尽".to_string(),
                    root_cause: "慢查询未优化".to_string(),
                },
            ],
            lessons_learned: vec![
                "需要更严格的数据库查询审查".to_string(),
                "连接池监控告警阈值过高".to_string(),
                "缺少自动扩容机制".to_string(),
            ],
        }
    }

    pub fn print_report(&self) {
        println!("=== 错误预算报告 ===");
        println!("周期: {}", self.period);
        println!("目标 SLO: {:.2}%", self.target_slo * 100.0);
        println!("实际 SLI: {:.2}%", self.actual_sli * 100.0);
        println!("预算消耗: {:.1}%", self.budget_consumed);
        println!("\n故障事件:");
        for incident in &self.incidents {
            println!("  - {}: {} ({}分钟)", incident.date, incident.impact, incident.duration_minutes);
        }
        println!("\n经验教训:");
        for lesson in &self.lessons_learned {
            println!("  - {}", lesson);
        }
    }
}

#[derive(Debug, Clone)]
pub struct Incident {
    date: String,
    duration_minutes: u64,
    impact: String,
    root_cause: String,
}
```

### 案例2：SLO 驱动的发布决策

**决策流程**：

```rust
/// 发布决策系统
pub struct ReleaseDecisionSystem {
    error_budget: ErrorBudget,
    burn_rate_calculator: BurnRateCalculator,
    policy_engine: ErrorBudgetPolicyEngine,
}

impl ReleaseDecisionSystem {
    /// 评估是否可以发布
    pub fn evaluate_release(&self, release: &Release) -> ReleaseDecision {
        // 1. 检查错误预算
        let budget_remaining = 100.0 - self.error_budget.budget_consumption();
        
        // 2. 检查燃烧率
        let current_error_rate = 1.0 - self.error_budget.current_sli();
        let burn_rate = self.burn_rate_calculator.calculate_burn_rate(current_error_rate);
        
        // 3. 应用策略
        let actions = self.policy_engine.evaluate(&self.error_budget, burn_rate);
        
        // 4. 做出决策
        if actions.iter().any(|a| matches!(a, PolicyAction::BlockDeployments)) {
            return ReleaseDecision::Blocked {
                reason: format!(
                    "错误预算不足 (剩余: {:.1}%)",
                    budget_remaining
                ),
                required_actions: vec![
                    "等待错误预算恢复".to_string(),
                    "或获得高级管理层批准".to_string(),
                ],
            };
        }
        
        if actions.iter().any(|a| matches!(a, PolicyAction::RequireApproval)) {
            return ReleaseDecision::RequiresApproval {
                reason: format!(
                    "错误预算较低 (剩余: {:.1}%)",
                    budget_remaining
                ),
                approvers: vec!["SRE Lead", "Engineering Manager"],
            };
        }
        
        ReleaseDecision::Approved {
            conditions: vec![
                "监控发布影响".to_string(),
                "准备快速回滚".to_string(),
            ],
        }
    }
}

#[derive(Debug)]
pub struct Release {
    version: String,
    risk_level: RiskLevel,
}

#[derive(Debug)]
pub enum RiskLevel {
    Low,
    Medium,
    High,
}

#[derive(Debug)]
pub enum ReleaseDecision {
    Approved { conditions: Vec<String> },
    RequiresApproval { reason: String, approvers: Vec<&'static str> },
    Blocked { reason: String, required_actions: Vec<String> },
}
```

## SLO 审查流程

### 定期审查

**审查频率**：

- 每周：SLO 达成情况
- 每月：错误预算使用情况
- 每季度：SLO 目标合理性

**审查清单**：

```markdown
## SLO 月度审查清单

### 1. SLO 达成情况
- [ ] 可用性 SLO：达成 / 未达成
- [ ] 延迟 SLO：达成 / 未达成
- [ ] 成功率 SLO：达成 / 未达成

### 2. 错误预算分析
- [ ] 本月预算消耗：____%
- [ ] 主要消耗事件：____
- [ ] 趋势分析：改善 / 恶化 / 稳定

### 3. 根因分析
- [ ] 故障次数：____
- [ ] 主要故障类型：____
- [ ] 改进措施：____

### 4. SLO 调整建议
- [ ] 当前 SLO 是否合理：是 / 否
- [ ] 建议调整：____
- [ ] 调整理由：____

### 5. 行动项
- [ ] 待改进项：____
- [ ] 责任人：____
- [ ] 完成时间：____
```

## 工具和自动化

### SLO 计算脚本

```bash
#!/bin/bash
# SLO 计算和报告脚本

PROMETHEUS_URL="http://prometheus:9090"
SLO_TARGET=0.999
WINDOW="30d"

echo "=== OTLP SLO 报告 ==="
echo "时间窗口: $WINDOW"
echo "目标 SLO: $(echo "$SLO_TARGET * 100" | bc)%"
echo ""

# 1. 计算可用性 SLI
AVAILABILITY=$(curl -s "$PROMETHEUS_URL/api/v1/query" \
  --data-urlencode "query=sum(rate(otlp_requests_total{status=\"success\"}[$WINDOW])) / sum(rate(otlp_requests_total[$WINDOW]))" \
  | jq -r '.data.result[0].value[1]')

echo "当前可用性: $(echo "$AVAILABILITY * 100" | bc -l | cut -c1-6)%"

# 2. 计算错误预算
TOTAL_REQUESTS=$(curl -s "$PROMETHEUS_URL/api/v1/query" \
  --data-urlencode "query=sum(increase(otlp_requests_total[$WINDOW]))" \
  | jq -r '.data.result[0].value[1]')

ALLOWED_FAILURES=$(echo "($TOTAL_REQUESTS * (1 - $SLO_TARGET))" | bc -l)
ACTUAL_FAILURES=$(echo "($TOTAL_REQUESTS * (1 - $AVAILABILITY))" | bc -l)
REMAINING_BUDGET=$(echo "($ALLOWED_FAILURES - $ACTUAL_FAILURES)" | bc -l)

echo "总请求数: $TOTAL_REQUESTS"
echo "允许失败: $(echo $ALLOWED_FAILURES | cut -c1-10)"
echo "实际失败: $(echo $ACTUAL_FAILURES | cut -c1-10)"
echo "剩余预算: $(echo $REMAINING_BUDGET | cut -c1-10)"

# 3. SLO 状态
if (( $(echo "$AVAILABILITY >= $SLO_TARGET" | bc -l) )); then
    echo "✓ SLO 达成"
else
    echo "✗ SLO 未达成"
fi
```

---

**相关文档**：

- [告警规则设计](./告警规则设计.md)
- [可观测性最佳实践](./可观测性最佳实践.md)
- [可靠性分析](../../07_理论基础/容错理论/可靠性分析.md)
