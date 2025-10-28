# 高级监控和 SRE 实践完整指南

**Crate:** c10_otlp  
**主题:** Advanced Monitoring & SRE Practices  
**Rust 版本:** 1.90.0  
**最后更新:** 2025年10月28日

---

## 📋 目录

- [高级监控和 SRE 完整指南](#高级监控和-sre-完整指南)
  - [📋 目录](#-目录)
  - [🎯 高级监控概述](#-高级监控概述)
    - [SRE 的核心理念](#sre-的核心理念)
    - [SRE vs DevOps](#sre-vs-devops)
  - [📊 SLI/SLO/SLA](#-slislosla)
    - [1. SLI (Service Level Indicator)](#1-sli-service-level-indicator)
    - [2. SLO (Service Level Objective)](#2-slo-service-level-objective)
    - [3. SLA (Service Level Agreement)](#3-sla-service-level-agreement)
  - [💰 错误预算](#-错误预算)
    - [实现](#实现)
  - [📞 On-Call 管理](#-on-call-管理)
    - [On-Call 轮换系统](#on-call-轮换系统)
  - [📖 Runbook 自动化](#-runbook-自动化)
    - [Runbook 模板](#runbook-模板)
  - [🔍 根因分析](#-根因分析)
    - [5 Whys 方法](#5-whys-方法)
  - [📈 容量规划](#-容量规划)
    - [实现](#实现-1)
  - [⚡ 性能工程](#-性能工程)
    - [性能预算](#性能预算)
  - [📚 总结](#-总结)
    - [SRE 清单](#sre-清单)
    - [最佳实践](#最佳实践)

---

## SRE 概述

### SRE 的核心理念

```
┌────────────────────────────────────────┐
│          SRE 核心原则                   │
├────────────────────────────────────────┤
│ 1. 拥抱风险 (Embrace Risk)              │
│ 2. 服务等级目标 (SLOs)                  │
│ 3. 消除琐事 (Eliminate Toil)            │
│ 4. 监控分布式系统                        │
│ 5. 自动化 (Automation)                  │
│ 6. 发布工程 (Release Engineering)       │
│ 7. 简单性 (Simplicity)                  │
└────────────────────────────────────────┘
```

### SRE vs DevOps

```
SRE = DevOps + Software Engineering

SRE 强调:
- 量化可靠性目标 (SLO)
- 错误预算
- 减少琐事 (Toil)
- 数据驱动的决策
```

---

## SLI/SLO/SLA 设计

### 1. SLI (Service Level Indicator)

#### 定义 SLI

```rust
use serde::{Serialize, Deserialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SLI {
    /// 可用性：成功请求 / 总请求
    Availability {
        successful_requests: u64,
        total_requests: u64,
    },
    
    /// 延迟：P99 延迟 < 阈值
    Latency {
        p99_latency_ms: f64,
        threshold_ms: f64,
    },
    
    /// 错误率：错误请求 / 总请求
    ErrorRate {
        error_requests: u64,
        total_requests: u64,
    },
    
    /// 吞吐量：每秒请求数
    Throughput {
        requests_per_second: f64,
    },
}

impl SLI {
    /// 计算 SLI 值 (0.0 - 1.0)
    pub fn value(&self) -> f64 {
        match self {
            SLI::Availability { successful_requests, total_requests } => {
                if *total_requests == 0 {
                    1.0
                } else {
                    *successful_requests as f64 / *total_requests as f64
                }
            }
            
            SLI::Latency { p99_latency_ms, threshold_ms } => {
                if *p99_latency_ms <= *threshold_ms {
                    1.0
                } else {
                    threshold_ms / p99_latency_ms
                }
            }
            
            SLI::ErrorRate { error_requests, total_requests } => {
                if *total_requests == 0 {
                    1.0
                } else {
                    1.0 - (*error_requests as f64 / *total_requests as f64)
                }
            }
            
            SLI::Throughput { requests_per_second } => {
                // 归一化到 0-1 范围
                (*requests_per_second / 1000.0).min(1.0)
            }
        }
    }
    
    /// 是否符合目标
    pub fn meets_target(&self, target: f64) -> bool {
        self.value() >= target
    }
}

// 使用示例
fn calculate_availability_sli(
    total_requests: u64,
    failed_requests: u64,
) -> SLI {
    let successful_requests = total_requests - failed_requests;
    
    SLI::Availability {
        successful_requests,
        total_requests,
    }
}
```

---

### 2. SLO (Service Level Objective)

#### 定义 SLO

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SLO {
    /// SLO 名称
    pub name: String,
    
    /// SLI 类型
    pub sli_type: SLIType,
    
    /// 目标值 (例如 99.9% = 0.999)
    pub target: f64,
    
    /// 时间窗口 (例如 30 天)
    pub window: Duration,
    
    /// 当前状态
    pub current_value: f64,
    
    /// 剩余错误预算
    pub error_budget_remaining: f64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SLIType {
    Availability,
    Latency,
    ErrorRate,
}

impl SLO {
    pub fn new(name: String, sli_type: SLIType, target: f64, window: Duration) -> Self {
        Self {
            name,
            sli_type,
            target,
            window,
            current_value: 1.0,
            error_budget_remaining: 1.0 - target,
        }
    }
    
    /// 更新 SLO 状态
    pub fn update(&mut self, sli_value: f64) {
        self.current_value = sli_value;
        
        // 计算剩余错误预算
        let allowed_failures = 1.0 - self.target;
        let actual_failures = 1.0 - sli_value;
        self.error_budget_remaining = (allowed_failures - actual_failures) / allowed_failures;
    }
    
    /// 是否符合 SLO
    pub fn is_compliant(&self) -> bool {
        self.current_value >= self.target
    }
    
    /// 错误预算是否耗尽
    pub fn is_error_budget_exhausted(&self) -> bool {
        self.error_budget_remaining <= 0.0
    }
    
    /// 获取告警级别
    pub fn alert_level(&self) -> AlertLevel {
        if self.error_budget_remaining <= 0.0 {
            AlertLevel::Critical
        } else if self.error_budget_remaining < 0.2 {
            AlertLevel::Warning
        } else {
            AlertLevel::Ok
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum AlertLevel {
    Ok,
    Warning,
    Critical,
}

// 使用示例
async fn monitor_slo(
    pool: &PgPool,
    slo: &mut SLO,
) -> Result<()> {
    // 1. 查询最近一小时的请求
    let stats = sqlx::query!(
        r#"
        SELECT 
            COUNT(*) as total,
            COUNT(*) FILTER (WHERE status < 500) as successful
        FROM requests
        WHERE timestamp > NOW() - INTERVAL '1 hour'
        "#
    )
    .fetch_one(pool)
    .await?;
    
    // 2. 计算 SLI
    let sli = SLI::Availability {
        successful_requests: stats.successful.unwrap_or(0) as u64,
        total_requests: stats.total.unwrap_or(0) as u64,
    };
    
    // 3. 更新 SLO
    slo.update(sli.value());
    
    // 4. 检查告警
    match slo.alert_level() {
        AlertLevel::Critical => {
            send_alert(&format!(
                "SLO {} is critical! Current: {:.2}%, Target: {:.2}%",
                slo.name,
                slo.current_value * 100.0,
                slo.target * 100.0
            )).await?;
        }
        AlertLevel::Warning => {
            send_warning(&format!(
                "SLO {} is approaching limit. Error budget: {:.2}%",
                slo.name,
                slo.error_budget_remaining * 100.0
            )).await?;
        }
        AlertLevel::Ok => {}
    }
    
    Ok(())
}
```

---

### 3. SLA (Service Level Agreement)

#### 定义 SLA

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SLA {
    /// SLA 名称
    pub name: String,
    
    /// 承诺的可用性 (例如 99.9%)
    pub committed_availability: f64,
    
    /// 测量窗口 (通常为月度)
    pub measurement_window: Duration,
    
    /// 违反 SLA 的后果
    pub penalties: Vec<SLAPenalty>,
    
    /// 当前合规性
    pub compliance_status: ComplianceStatus,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SLAPenalty {
    /// 可用性阈值
    pub threshold: f64,
    
    /// 信用返还百分比
    pub credit_percentage: f64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ComplianceStatus {
    Compliant,
    AtRisk,
    Violated { credit_percentage: f64 },
}

impl SLA {
    pub fn check_compliance(&mut self, actual_availability: f64) {
        if actual_availability >= self.committed_availability {
            self.compliance_status = ComplianceStatus::Compliant;
        } else if actual_availability >= self.committed_availability - 0.01 {
            self.compliance_status = ComplianceStatus::AtRisk;
        } else {
            // 查找适用的惩罚
            let credit = self.penalties.iter()
                .filter(|p| actual_availability < p.threshold)
                .map(|p| p.credit_percentage)
                .max_by(|a, b| a.partial_cmp(b).unwrap())
                .unwrap_or(0.0);
            
            self.compliance_status = ComplianceStatus::Violated {
                credit_percentage: credit,
            };
        }
    }
}

// 使用示例
fn define_sla() -> SLA {
    SLA {
        name: "API Service SLA".to_string(),
        committed_availability: 0.999,  // 99.9%
        measurement_window: Duration::from_secs(30 * 24 * 3600),  // 30 days
        penalties: vec![
            SLAPenalty {
                threshold: 0.999,
                credit_percentage: 10.0,  // < 99.9%: 10% 信用
            },
            SLAPenalty {
                threshold: 0.995,
                credit_percentage: 25.0,  // < 99.5%: 25% 信用
            },
            SLAPenalty {
                threshold: 0.99,
                credit_percentage: 50.0,  // < 99%: 50% 信用
            },
        ],
        compliance_status: ComplianceStatus::Compliant,
    }
}
```

---

## 错误预算管理

### 实现

```rust
pub struct ErrorBudgetManager {
    slos: HashMap<String, SLO>,
    burn_rate_alerts: Vec<BurnRateAlert>,
}

#[derive(Debug, Clone)]
pub struct BurnRateAlert {
    /// 燃烧率阈值 (例如 10x 表示错误预算以 10 倍速度消耗)
    pub threshold: f64,
    
    /// 窗口期
    pub window: Duration,
    
    /// 告警级别
    pub severity: AlertSeverity,
}

#[derive(Debug, Clone, PartialEq)]
pub enum AlertSeverity {
    Page,      // 立即通知 on-call
    Ticket,    // 创建工单
    Warning,   // 仅记录
}

impl ErrorBudgetManager {
    pub fn new() -> Self {
        Self {
            slos: HashMap::new(),
            burn_rate_alerts: vec![
                // 快速燃烧：1小时内燃烧 5% 错误预算
                BurnRateAlert {
                    threshold: 14.4,  // (30天 / 1小时) * 0.05 / 0.1
                    window: Duration::from_secs(3600),
                    severity: AlertSeverity::Page,
                },
                // 中速燃烧：6小时内燃烧 10% 错误预算
                BurnRateAlert {
                    threshold: 6.0,
                    window: Duration::from_secs(6 * 3600),
                    severity: AlertSeverity::Ticket,
                },
                // 慢速燃烧：3天内燃烧 50% 错误预算
                BurnRateAlert {
                    threshold: 1.0,
                    window: Duration::from_secs(3 * 24 * 3600),
                    severity: AlertSeverity::Warning,
                },
            ],
        }
    }
    
    /// 计算错误预算燃烧率
    pub fn calculate_burn_rate(
        &self,
        slo: &SLO,
        window: Duration,
    ) -> f64 {
        // 实际错误率
        let actual_error_rate = 1.0 - slo.current_value;
        
        // 允许的错误率
        let allowed_error_rate = 1.0 - slo.target;
        
        // 燃烧率 = 实际错误率 / 允许的错误率
        if allowed_error_rate > 0.0 {
            actual_error_rate / allowed_error_rate
        } else {
            0.0
        }
    }
    
    /// 检查燃烧率告警
    pub async fn check_burn_rate_alerts(
        &self,
        slo_name: &str,
    ) -> Vec<BurnRateAlertTriggered> {
        let mut triggered = Vec::new();
        
        if let Some(slo) = self.slos.get(slo_name) {
            for alert in &self.burn_rate_alerts {
                let burn_rate = self.calculate_burn_rate(slo, alert.window);
                
                if burn_rate >= alert.threshold {
                    triggered.push(BurnRateAlertTriggered {
                        slo_name: slo_name.to_string(),
                        burn_rate,
                        threshold: alert.threshold,
                        window: alert.window,
                        severity: alert.severity.clone(),
                    });
                }
            }
        }
        
        triggered
    }
}

#[derive(Debug)]
pub struct BurnRateAlertTriggered {
    pub slo_name: String,
    pub burn_rate: f64,
    pub threshold: f64,
    pub window: Duration,
    pub severity: AlertSeverity,
}
```

---

## On-Call 最佳实践

### On-Call 轮换系统

```rust
use chrono::{DateTime, Utc, Duration as ChronoDuration};

#[derive(Debug, Clone)]
pub struct OnCallSchedule {
    /// 值班人员列表
    pub engineers: Vec<Engineer>,
    
    /// 轮换周期 (例如 7 天)
    pub rotation_period: Duration,
    
    /// 当前值班人员索引
    pub current_index: usize,
    
    /// 上次轮换时间
    pub last_rotation: DateTime<Utc>,
}

#[derive(Debug, Clone)]
pub struct Engineer {
    pub id: String,
    pub name: String,
    pub email: String,
    pub phone: String,
    pub timezone: String,
}

impl OnCallSchedule {
    pub fn current_on_call(&self) -> &Engineer {
        &self.engineers[self.current_index]
    }
    
    pub fn next_on_call(&self) -> &Engineer {
        let next_index = (self.current_index + 1) % self.engineers.len();
        &self.engineers[next_index]
    }
    
    pub fn should_rotate(&self) -> bool {
        let now = Utc::now();
        let elapsed = now.signed_duration_since(self.last_rotation);
        
        elapsed >= ChronoDuration::from_std(self.rotation_period).unwrap()
    }
    
    pub fn rotate(&mut self) {
        self.current_index = (self.current_index + 1) % self.engineers.len();
        self.last_rotation = Utc::now();
    }
}

// 告警路由
pub struct AlertRouter {
    schedule: OnCallSchedule,
}

impl AlertRouter {
    pub async fn send_alert(&self, alert: &Alert) -> Result<()> {
        let on_call = self.schedule.current_on_call();
        
        match alert.severity {
            AlertSeverity::Page => {
                // 立即通知：电话 + SMS + Email
                self.call_phone(&on_call.phone, alert).await?;
                self.send_sms(&on_call.phone, alert).await?;
                self.send_email(&on_call.email, alert).await?;
            }
            AlertSeverity::Ticket => {
                // 创建工单 + Email
                self.create_ticket(alert).await?;
                self.send_email(&on_call.email, alert).await?;
            }
            AlertSeverity::Warning => {
                // 仅 Email
                self.send_email(&on_call.email, alert).await?;
            }
        }
        
        Ok(())
    }
}

#[derive(Debug)]
pub struct Alert {
    pub title: String,
    pub description: String,
    pub severity: AlertSeverity,
    pub timestamp: DateTime<Utc>,
    pub runbook_url: Option<String>,
}
```

---

## Runbook 编写

### Runbook 模板

```rust
#[derive(Debug, Serialize, Deserialize)]
pub struct Runbook {
    /// 告警名称
    pub alert_name: String,
    
    /// 描述
    pub description: String,
    
    /// 影响
    pub impact: String,
    
    /// 诊断步骤
    pub diagnosis_steps: Vec<DiagnosisStep>,
    
    /// 修复步骤
    pub remediation_steps: Vec<RemediationStep>,
    
    /// 升级路径
    pub escalation_path: Vec<EscalationContact>,
    
    /// 相关文档链接
    pub related_docs: Vec<String>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct DiagnosisStep {
    pub step_number: u32,
    pub description: String,
    pub command: Option<String>,
    pub expected_output: Option<String>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct RemediationStep {
    pub step_number: u32,
    pub description: String,
    pub command: Option<String>,
    pub rollback_command: Option<String>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct EscalationContact {
    pub level: u32,
    pub name: String,
    pub contact: String,
    pub escalate_after: Duration,
}

// 示例 Runbook
fn create_high_latency_runbook() -> Runbook {
    Runbook {
        alert_name: "HighAPILatency".to_string(),
        description: "API 响应时间超过 500ms".to_string(),
        impact: "用户体验下降，可能导致超时".to_string(),
        
        diagnosis_steps: vec![
            DiagnosisStep {
                step_number: 1,
                description: "检查当前 P99 延迟".to_string(),
                command: Some("curl http://localhost:9090/metrics | grep http_request_duration_p99".to_string()),
                expected_output: Some("< 500ms".to_string()),
            },
            DiagnosisStep {
                step_number: 2,
                description: "检查数据库连接池".to_string(),
                command: Some("kubectl exec -it pod-name -- curl localhost:8080/health".to_string()),
                expected_output: Some("pool_available > 5".to_string()),
            },
            DiagnosisStep {
                step_number: 3,
                description: "检查 CPU 使用率".to_string(),
                command: Some("kubectl top pods".to_string()),
                expected_output: Some("< 80%".to_string()),
            },
        ],
        
        remediation_steps: vec![
            RemediationStep {
                step_number: 1,
                description: "增加 Pod 副本数".to_string(),
                command: Some("kubectl scale deployment/api --replicas=10".to_string()),
                rollback_command: Some("kubectl scale deployment/api --replicas=5".to_string()),
            },
            RemediationStep {
                step_number: 2,
                description: "清理缓存".to_string(),
                command: Some("redis-cli FLUSHDB".to_string()),
                rollback_command: None,
            },
        ],
        
        escalation_path: vec![
            EscalationContact {
                level: 1,
                name: "On-Call Engineer".to_string(),
                contact: "oncall@example.com".to_string(),
                escalate_after: Duration::from_secs(15 * 60),
            },
            EscalationContact {
                level: 2,
                name: "Team Lead".to_string(),
                contact: "team-lead@example.com".to_string(),
                escalate_after: Duration::from_secs(30 * 60),
            },
            EscalationContact {
                level: 3,
                name: "Director of Engineering".to_string(),
                contact: "director@example.com".to_string(),
                escalate_after: Duration::from_secs(60 * 60),
            },
        ],
        
        related_docs: vec![
            "https://wiki.example.com/api-architecture".to_string(),
            "https://wiki.example.com/database-troubleshooting".to_string(),
        ],
    }
}
```

---

## 根因分析

### 5 Whys 方法

```rust
#[derive(Debug, Serialize, Deserialize)]
pub struct RootCauseAnalysis {
    pub incident_id: String,
    pub title: String,
    pub occurred_at: DateTime<Utc>,
    pub detected_at: DateTime<Utc>,
    pub resolved_at: Option<DateTime<Utc>>,
    
    /// 事件时间线
    pub timeline: Vec<TimelineEvent>,
    
    /// 5 个为什么
    pub five_whys: Vec<WhyStep>,
    
    /// 根本原因
    pub root_cause: String,
    
    /// 纠正措施
    pub corrective_actions: Vec<CorrectiveAction>,
    
    /// 预防措施
    pub preventive_actions: Vec<PreventiveAction>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct TimelineEvent {
    pub timestamp: DateTime<Utc>,
    pub description: String,
    pub actor: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct WhyStep {
    pub step: u32,
    pub question: String,
    pub answer: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct CorrectiveAction {
    pub description: String,
    pub owner: String,
    pub due_date: DateTime<Utc>,
    pub status: ActionStatus,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct PreventiveAction {
    pub description: String,
    pub owner: String,
    pub due_date: DateTime<Utc>,
    pub status: ActionStatus,
}

#[derive(Debug, Serialize, Deserialize)]
pub enum ActionStatus {
    Todo,
    InProgress,
    Done,
    Blocked,
}

// 示例 RCA
fn create_rca() -> RootCauseAnalysis {
    RootCauseAnalysis {
        incident_id: "INC-2025-001".to_string(),
        title: "API 服务 30 分钟不可用".to_string(),
        occurred_at: Utc::now() - ChronoDuration::hours(2),
        detected_at: Utc::now() - ChronoDuration::hours(2) + ChronoDuration::minutes(5),
        resolved_at: Some(Utc::now() - ChronoDuration::hours(1) + ChronoDuration::minutes(30)),
        
        timeline: vec![
            TimelineEvent {
                timestamp: Utc::now() - ChronoDuration::hours(2),
                description: "部署新版本 v1.2.0".to_string(),
                actor: "CI/CD Pipeline".to_string(),
            },
            TimelineEvent {
                timestamp: Utc::now() - ChronoDuration::hours(2) + ChronoDuration::minutes(5),
                description: "告警触发：Error rate > 50%".to_string(),
                actor: "Prometheus".to_string(),
            },
            TimelineEvent {
                timestamp: Utc::now() - ChronoDuration::hours(2) + ChronoDuration::minutes(10),
                description: "On-call 工程师开始调查".to_string(),
                actor: "John Doe".to_string(),
            },
        ],
        
        five_whys: vec![
            WhyStep {
                step: 1,
                question: "为什么 API 服务不可用？".to_string(),
                answer: "所有 Pod 都在崩溃重启".to_string(),
            },
            WhyStep {
                step: 2,
                question: "为什么 Pod 崩溃重启？".to_string(),
                answer: "内存溢出 (OOM)".to_string(),
            },
            WhyStep {
                step: 3,
                question: "为什么出现内存溢出？".to_string(),
                answer: "新版本引入了内存泄漏".to_string(),
            },
            WhyStep {
                step: 4,
                question: "为什么新版本有内存泄漏？".to_string(),
                answer: "缓存清理逻辑有bug".to_string(),
            },
            WhyStep {
                step: 5,
                question: "为什么缓存清理bug没被发现？".to_string(),
                answer: "缺少内存压力测试".to_string(),
            },
        ],
        
        root_cause: "缺少内存压力测试导致内存泄漏bug未被发现".to_string(),
        
        corrective_actions: vec![
            CorrectiveAction {
                description: "回滚到 v1.1.9".to_string(),
                owner: "John Doe".to_string(),
                due_date: Utc::now(),
                status: ActionStatus::Done,
            },
            CorrectiveAction {
                description: "修复缓存清理bug".to_string(),
                owner: "Jane Smith".to_string(),
                due_date: Utc::now() + ChronoDuration::days(1),
                status: ActionStatus::InProgress,
            },
        ],
        
        preventive_actions: vec![
            PreventiveAction {
                description: "添加内存压力测试到 CI/CD".to_string(),
                owner: "Jane Smith".to_string(),
                due_date: Utc::now() + ChronoDuration::days(7),
                status: ActionStatus::Todo,
            },
            PreventiveAction {
                description: "实施金丝雀发布策略".to_string(),
                owner: "DevOps Team".to_string(),
                due_date: Utc::now() + ChronoDuration::days(14),
                status: ActionStatus::Todo,
            },
        ],
    }
}
```

---

## 容量规划

### 实现

```rust
pub struct CapacityPlanner {
    /// 历史使用数据
    usage_history: Vec<UsageData>,
}

#[derive(Debug, Clone)]
pub struct UsageData {
    pub timestamp: DateTime<Utc>,
    pub cpu_usage: f64,
    pub memory_usage: f64,
    pub requests_per_second: f64,
}

impl CapacityPlanner {
    /// 预测未来使用量
    pub fn forecast(&self, days_ahead: u32) -> ForecastResult {
        // 使用线性回归预测
        let cpu_forecast = self.linear_regression_forecast(
            &self.usage_history.iter()
                .map(|d| d.cpu_usage)
                .collect::<Vec<_>>(),
            days_ahead
        );
        
        let memory_forecast = self.linear_regression_forecast(
            &self.usage_history.iter()
                .map(|d| d.memory_usage)
                .collect::<Vec<_>>(),
            days_ahead
        );
        
        ForecastResult {
            forecast_date: Utc::now() + ChronoDuration::days(days_ahead as i64),
            predicted_cpu_usage: cpu_forecast,
            predicted_memory_usage: memory_forecast,
        }
    }
    
    fn linear_regression_forecast(&self, data: &[f64], days_ahead: u32) -> f64 {
        if data.is_empty() {
            return 0.0;
        }
        
        // 简单线性回归
        let n = data.len() as f64;
        let x_mean = (n - 1.0) / 2.0;
        let y_mean = data.iter().sum::<f64>() / n;
        
        let mut numerator = 0.0;
        let mut denominator = 0.0;
        
        for (i, &y) in data.iter().enumerate() {
            let x = i as f64;
            numerator += (x - x_mean) * (y - y_mean);
            denominator += (x - x_mean) * (x - x_mean);
        }
        
        let slope = numerator / denominator;
        let intercept = y_mean - slope * x_mean;
        
        // 预测
        let future_x = n - 1.0 + days_ahead as f64;
        slope * future_x + intercept
    }
    
    /// 计算所需容量
    pub fn calculate_required_capacity(
        &self,
        current_capacity: u32,
        target_utilization: f64,
    ) -> u32 {
        let forecast_30_days = self.forecast(30);
        
        let max_usage = forecast_30_days.predicted_cpu_usage
            .max(forecast_30_days.predicted_memory_usage);
        
        // 考虑峰值和缓冲
        let required_capacity = (max_usage / target_utilization * 1.2) as u32;
        
        required_capacity.max(current_capacity)
    }
}

#[derive(Debug)]
pub struct ForecastResult {
    pub forecast_date: DateTime<Utc>,
    pub predicted_cpu_usage: f64,
    pub predicted_memory_usage: f64,
}
```

---

## 性能工程

### 性能预算

```rust
#[derive(Debug, Clone)]
pub struct PerformanceBudget {
    /// 页面加载时间预算 (ms)
    pub page_load_time: f64,
    
    /// API 响应时间预算 (ms)
    pub api_response_time: f64,
    
    /// 首次内容绘制预算 (ms)
    pub first_contentful_paint: f64,
    
    /// 总页面大小预算 (KB)
    pub total_page_size: f64,
}

impl PerformanceBudget {
    pub fn check_compliance(&self, metrics: &PerformanceMetrics) -> Vec<BudgetViolation> {
        let mut violations = Vec::new();
        
        if metrics.page_load_time > self.page_load_time {
            violations.push(BudgetViolation {
                metric: "page_load_time".to_string(),
                budget: self.page_load_time,
                actual: metrics.page_load_time,
                overage: metrics.page_load_time - self.page_load_time,
            });
        }
        
        if metrics.api_response_time > self.api_response_time {
            violations.push(BudgetViolation {
                metric: "api_response_time".to_string(),
                budget: self.api_response_time,
                actual: metrics.api_response_time,
                overage: metrics.api_response_time - self.api_response_time,
            });
        }
        
        violations
    }
}

#[derive(Debug)]
pub struct PerformanceMetrics {
    pub page_load_time: f64,
    pub api_response_time: f64,
    pub first_contentful_paint: f64,
    pub total_page_size: f64,
}

#[derive(Debug)]
pub struct BudgetViolation {
    pub metric: String,
    pub budget: f64,
    pub actual: f64,
    pub overage: f64,
}
```

---

## 总结

### SRE 清单

- ✅ **SLI/SLO/SLA**: 量化可靠性目标
- ✅ **错误预算**: 燃烧率监控和管理
- ✅ **On-Call**: 轮换和告警路由
- ✅ **Runbook**: 标准化操作手册
- ✅ **RCA**: 5 Whys 根因分析
- ✅ **容量规划**: 预测和扩容
- ✅ **性能工程**: 性能预算管理

### 最佳实践

1. **数据驱动**: 基于 SLI/SLO 做决策
2. **自动化**: 减少琐事和人工干预
3. **文档化**: Runbook 和 RCA 标准化
4. **预防性**: 错误预算和容量规划
5. **持续改进**: 从每次事件中学习

---

**文档贡献者:** AI Assistant  
**审核状态:** ✅ 已完成  
**最后更新:** 2025年10月28日

