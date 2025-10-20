# OTLP Collector 运维手册

> **版本**: 2.0  
> **日期**: 2025年10月17日  
> **状态**: ✅ 完整版

---

## 📋 文档概述

本运维手册（Runbook）提供OTLP Collector在生产环境中的**标准运维流程**、**故障排查方法**和**应急响应措施**。

### 适用场景

- ✅ 日常运维操作
- ✅ 告警响应处理
- ✅ 故障快速定位
- ✅ 配置变更管理
- ✅ 应急事件处理

---

## 🎯 运维理念

### OODA循环

```text
观测 (Observe) → 定位 (Orient) → 决策 (Decide) → 行动 (Act)
```

### 核心原则

1. **可观测优先**: 所有操作基于指标和日志
2. **渐进式变更**: 小步快跑，灰度验证
3. **可回滚性**: 所有变更都有回滚方案
4. **文档化**: 记录所有重要操作和决策

---

## 🔍 观测入口

### 1. Grafana仪表板

**主要仪表板**:

| 仪表板 | URL | 用途 |
|--------|-----|------|
| **Collector Overview** | `http://grafana:3000/d/otel-collector` | 整体健康状态 |
| **Performance Analysis** | `http://grafana:3000/d/otel-perf` | 性能指标分析 |
| **Troubleshooting** | `http://grafana:3000/d/otel-debug` | 故障排查专用 |

**关键面板**:

- 数据流量（接收/导出/失败率）
- 资源使用（CPU/内存/网络）
- 队列状态（大小/容量/积压）
- 延迟分布（P50/P95/P99）

### 2. Jaeger UI

**访问**: `http://jaeger:16686`

**用途**:

- 验证Traces是否成功导出
- 分析服务调用链路
- 检查Span完整性
- 排查数据质量问题

### 3. Prometheus查询

**访问**: `http://prometheus:9090`

**常用查询**（见[MEASUREMENT_GUIDE.md](./MEASUREMENT_GUIDE.md)）:

```promql
# 导出速率
rate(otelcol_exporter_sent_spans[1m])

# 导出失败率
rate(otelcol_exporter_send_failed_spans[1m])

# CPU使用率
rate(process_cpu_seconds_total[1m])

# 内存使用
process_resident_memory_bytes
```

### 4. Collector日志

**Kubernetes环境**:

```bash
# 查看实时日志
kubectl logs -f deployment/otel-collector -n observability

# 查看最近100行
kubectl logs --tail=100 deployment/otel-collector -n observability

# 按时间过滤
kubectl logs --since=10m deployment/otel-collector -n observability
```

**Docker环境**:

```bash
# 查看日志
docker-compose logs -f otel-collector

# 最近100行
docker-compose logs --tail=100 otel-collector
```

---

## 🚨 常见告警与处置

### 告警1: 导出失败率升高

**告警名称**: `OTLPCollectorHighExportFailureRate`

#### 症状

- 导出失败率>0持续5分钟
- Grafana显示failed spans增加
- 可能出现数据丢失

#### 诊断步骤

**步骤1: 确认后端可用性**:

```bash
# 检查Jaeger健康状态
curl http://jaeger:14269/

# 检查Prometheus健康状态
curl http://prometheus:9090/-/healthy

# 如果是远程后端，测试连接
telnet backend-host 4317
```

**步骤2: 检查Collector日志**:

```bash
# 查找错误信息
kubectl logs deployment/otel-collector | grep -i error

# 常见错误模式
kubectl logs deployment/otel-collector | grep -E "connection refused|timeout|authentication failed"
```

**步骤3: 验证网络连通性**:

```bash
# 从Collector pod内测试
kubectl exec -it deploy/otel-collector -- /bin/sh
wget -O- http://jaeger:14250/healthz
```

**步骤4: 检查认证配置**:

```bash
# 检查证书有效期
kubectl get secret otel-collector-certs -o yaml
# 验证mTLS配置是否正确
```

#### 解决方案

| 原因 | 解决方法 |
|------|----------|
| **后端不可用** | 联系后端团队恢复服务；启用重试机制 |
| **网络问题** | 检查网络策略和防火墙；验证Service/Ingress配置 |
| **认证失败** | 更新证书；检查API Key配置 |
| **配置错误** | 回滚到上一个正常配置 |
| **后端过载** | 启用采样降低负载；扩容后端 |

#### 临时缓解措施

```yaml
# 启用重试（如果未启用）
exporters:
  otlp:
    endpoint: backend:4317
    retry_on_failure:
      enabled: true
      initial_interval: 5s
      max_interval: 30s
      max_elapsed_time: 300s
```

### 告警2: CPU使用率过高

**告警名称**: `OTLPCollectorHighCPU`

#### 症状2

- CPU使用率>70%持续10分钟
- 处理延迟增加
- 可能影响数据吞吐

#### 诊断步骤2

**步骤1: 确认CPU使用趋势**:

```promql
# 查看CPU趋势（过去1小时）
rate(process_cpu_seconds_total{job="otel-collector"}[5m])

# 对比历史基线
avg_over_time(rate(process_cpu_seconds_total[5m])[7d:5m])
```

**步骤2: 分析处理器负载**:

```bash
# 检查OTTL规则执行次数
kubectl logs deployment/otel-collector | grep "transform"

# 查看批处理统计
```

```promql
# OTTL执行频率
rate(otelcol_processor_transform_statements_executed[1m])

# 批处理效率
rate(otelcol_processor_batch_batch_send_size_sum[1m])
/
rate(otelcol_processor_batch_batch_send_size_count[1m])
```

**步骤3: 检查数据量变化**:

```promql
# 接收速率变化
rate(otelcol_receiver_accepted_spans[5m])

# 与基线对比
```

#### 解决方案2

| 原因 | 解决方法 |
|------|----------|
| **OTTL规则复杂** | 简化规则；移除不必要的转换；使用更高效的函数 |
| **数据量突增** | 启用采样；增加Collector实例数 |
| **批处理配置不当** | 增大批处理大小；调整发送间隔 |
| **资源限制不足** | 增加CPU限制；水平扩展 |

#### 优化配置示例

```yaml
processors:
  # 优化批处理
  batch:
    timeout: 10s
    send_batch_size: 1000
    send_batch_max_size: 1500
  
  # 简化OTTL规则
  transform:
    error_mode: ignore  # 忽略非关键错误
    trace_statements:
      - context: span
        statements:
          # 只保留必要的转换
          - set(attributes["simplified"], true) where attributes["complex"] == "value"
```

### 告警3: 内存使用过高

**告警名称**: `OTLPCollectorHighMemory`

#### 症状3

- 内存使用>1.5GB持续10分钟
- 可能出现OOM
- Pod重启风险

#### 诊断步骤3

**步骤1: 确认内存使用**:

```promql
# 当前内存使用
process_resident_memory_bytes{job="otel-collector"}

# 内存增长速率
rate(process_resident_memory_bytes[5m])
```

**步骤2: 检查队列积压**:

```promql
# 导出队列大小
otelcol_exporter_queue_size

# 队列容量
otelcol_exporter_queue_capacity
```

**步骤3: 分析内存泄漏**:

```bash
# 查看Pod重启历史
kubectl get pods -n observability

# 检查OOM事件
kubectl describe pod otel-collector-xxx | grep -i oom
```

#### 解决方案3

| 原因 | 解决方法 |
|------|----------|
| **队列积压** | 减小队列大小；增加导出器并发 |
| **批处理太大** | 减小batch_size |
| **内存泄漏** | 升级到最新版本；报告bug |
| **限制不足** | 增加内存限制；启用内存限制器 |

#### 配置内存限制器

```yaml
processors:
  memory_limiter:
    check_interval: 1s
    limit_mib: 1536  # 1.5GB
    spike_limit_mib: 512  # 允许512MB突发
```

### 告警4: 队列积压

**告警名称**: `OTLPCollectorQueueBacklog`

#### 症状4

- 队列使用率>80%
- 数据延迟增加
- 可能丢弃数据

#### 诊断步骤4

```promql
# 队列使用率
otelcol_exporter_queue_size / otelcol_exporter_queue_capacity

# 发送速率vs接收速率
rate(otelcol_exporter_sent_spans[5m])
vs
rate(otelcol_receiver_accepted_spans[5m])
```

#### 解决方案4

```yaml
exporters:
  otlp:
    endpoint: backend:4317
    sending_queue:
      enabled: true
      num_consumers: 20  # 增加消费者
      queue_size: 5000   # 增加队列大小
```

---

## 🔄 配置变更流程

### 变更类型

| 类型 | 风险等级 | 审批要求 | 回滚准备 |
|------|----------|----------|----------|
| **OTTL规则** | 高 | SRE+安全 | 必需 |
| **导出器配置** | 高 | SRE | 必需 |
| **资源限制** | 中 | SRE | 推荐 |
| **接收器配置** | 中 | SRE | 推荐 |
| **日志级别** | 低 | 自助 | 可选 |

### 标准变更流程

#### 步骤1: 变更准备

```bash
# 1. 备份当前配置
kubectl get configmap otel-collector-config -o yaml > backup-$(date +%Y%m%d-%H%M%S).yaml

# 2. 验证新配置语法
otelcol validate --config=new-config.yaml

# 3. 准备回滚脚本
cat > rollback.sh <<'EOF'
#!/bin/bash
kubectl apply -f backup-latest.yaml
kubectl rollout restart deployment/otel-collector
EOF
chmod +x rollback.sh
```

#### 步骤2: 灰度发布（如使用OpAMP）

参考[OPAMP_ROLLOUT_STRATEGY.md](./OPAMP_ROLLOUT_STRATEGY.md)

```yaml
# 灰度策略
rollout:
  phase1:
    selector: {env: "canary"}
    weight: 10%
    duration: 15m
  phase2:
    selector: {env: "staging"}
    weight: 30%
    duration: 30m
  phase3:
    selector: {env: "production"}
    weight: 100%
    duration: 60m
```

#### 步骤3: 变更执行

```bash
# Kubernetes环境
kubectl apply -f new-config.yaml
kubectl rollout status deployment/otel-collector

# Docker Compose环境
docker-compose up -d --force-recreate otel-collector
```

#### 步骤4: 变更验证

**验证清单**（15分钟观察窗口）:

- [ ] 导出失败率≈0
- [ ] CPU使用率<阈值
- [ ] 内存使用率正常
- [ ] 导出速率稳定
- [ ] 后端接收数据正常
- [ ] 无错误日志

**验证命令**:

```bash
# 快速验证脚本
./scripts/prom_query.sh

# 或手动查询
curl -G 'http://prometheus:9090/api/v1/query' \
  --data-urlencode 'query=rate(otelcol_exporter_send_failed_spans[5m])'
```

#### 步骤5: 记录与归档

```bash
# 生成变更报告
./scripts/snapshot_results.sh > change-report-$(date +%Y%m%d).txt

# 更新变更日志
echo "$(date): Applied config change - version 2.1" >> CHANGELOG.md
```

---

## 🔙 回滚操作

### 快速回滚

```bash
# Kubernetes
kubectl rollout undo deployment/otel-collector
kubectl rollout status deployment/otel-collector

# 验证回滚成功
kubectl rollout history deployment/otel-collector
```

### 指定版本回滚

```bash
# 查看历史版本
kubectl rollout history deployment/otel-collector

# 回滚到特定版本
kubectl rollout undo deployment/otel-collector --to-revision=3
```

### OpAMP自动回滚

如果使用OpAMP，参考[OPAMP_ROLLOUT_STRATEGY.md](./OPAMP_ROLLOUT_STRATEGY.md)中的自动回滚配置。

**触发条件**:

- 导出失败率>阈值
- CPU/内存使用异常
- 错误率超限

---

## 📊 日常运维任务

### 每日检查

- [ ] 检查告警状态（无未处理告警）
- [ ] 查看仪表板（所有指标正常）
- [ ] 验证数据流（后端接收正常）
- [ ] 审查日志（无错误/警告）

### 每周任务

- [ ] 性能趋势分析
- [ ] 容量规划评估
- [ ] 配置备份验证
- [ ] 更新运维文档

### 每月任务

- [ ] 安全补丁更新
- [ ] 证书到期检查
- [ ] 成本优化评估
- [ ] 灾备演练

---

## 🆘 应急响应

### P0事件（数据完全中断）

**响应时间**: 立即

#### 1. 快速评估

```bash
# 检查Collector是否运行
kubectl get pods -n observability

# 检查后端是否可达
curl http://jaeger:14269/
curl http://prometheus:9090/-/healthy
```

#### 2. 应急措施

```bash
# 如果Collector崩溃
kubectl rollout restart deployment/otel-collector

# 如果后端不可用
# 临时切换到备用后端或本地存储
kubectl edit configmap otel-collector-config
```

#### 3. 通知

```bash
# 发送通知
curl -X POST https://slack-webhook/... \
  -d '{"text": "P0: OTLP Collector数据中断"}'
```

### P1事件（性能严重下降）

**响应时间**: 30分钟内

#### 1. 性能分析

```promql
# CPU突增
rate(process_cpu_seconds_total[1m])

# 内存突增
rate(process_resident_memory_bytes[1m])

# 队列积压
otelcol_exporter_queue_size
```

#### 2. 临时缓解

```bash
# 快速扩容
kubectl scale deployment/otel-collector --replicas=5

# 或启用采样
kubectl edit configmap otel-collector-config
# 添加采样配置
```

---

## 🔧 故障排查工具箱

### 1. 日志分析脚本

```bash
#!/bin/bash
# analyze-logs.sh

# 统计错误类型
kubectl logs deployment/otel-collector | \
  grep -i error | \
  awk '{print $NF}' | \
  sort | uniq -c | sort -rn

# 查找慢查询
kubectl logs deployment/otel-collector | \
  grep -i "took longer than"
```

### 2. 性能诊断

```bash
#!/bin/bash
# diagnose-perf.sh

echo "=== CPU使用率 ==="
curl -s 'http://prometheus:9090/api/v1/query?query=rate(process_cpu_seconds_total[5m])' | jq .

echo "=== 内存使用 ==="
curl -s 'http://prometheus:9090/api/v1/query?query=process_resident_memory_bytes' | jq .

echo "=== 队列状态 ==="
curl -s 'http://prometheus:9090/api/v1/query?query=otelcol_exporter_queue_size' | jq .
```

### 3. 连接测试

```bash
#!/bin/bash
# test-connectivity.sh

# 测试后端连接
backends=("jaeger:14250" "prometheus:9090" "tempo:4317")

for backend in "${backends[@]}"; do
  echo "Testing $backend..."
  nc -zv ${backend/:/ } 2>&1 | grep succeeded && echo "✓" || echo "✗"
done
```

---

## 📚 相关文档

- [告警基线](./ALERTING_BASELINE.md) - 告警规则和仪表板
- [测量指南](./MEASUREMENT_GUIDE.md) - 指标查询参考
- [规则治理](./RULES_GOVERNANCE.md) - OTTL规则管理
- [OpAMP策略](./OPAMP_ROLLOUT_STRATEGY.md) - 配置灰度发布
- [性能优化](./PERFORMANCE_OPTIMIZATION_MANUAL.md) - 性能调优指南

---

## 📞 支持渠道

### 内部支持

- **一线支持**: SRE团队（Slack: #otlp-support）
- **配置问题**: 平台团队（Slack: #platform）
- **安全问题**: 安全团队（Slack: #security）

### 外部资源

- **OpenTelemetry文档**: <https://opentelemetry.io/docs/>
- **Collector问题**: <https://github.com/open-telemetry/opentelemetry-collector/issues>
- **社区Slack**: <https://cloud-native.slack.com/>

---

## 📝 变更历史

| 版本 | 日期 | 说明 |
|------|------|------|
| 2.0 | 2025-10-17 | 完整版发布：扩展为生产级运维手册 |
| 1.0 | 2025-09-XX | 初始版本：基础运维流程 |

---

**规范运维流程，保障系统稳定运行！** 🔧✨
