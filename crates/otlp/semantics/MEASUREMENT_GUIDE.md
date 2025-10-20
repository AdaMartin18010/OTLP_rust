# OTLP性能测量与指标查询指南

> **版本**: 2.0  
> **日期**: 2025年10月17日  
> **状态**: ✅ 完整版

---

## 📋 文档概述

本文档提供OTLP Collector性能测量的完整指南，包括指标定义、PromQL查询、测量方法和基准填报。

---

## 🎯 核心指标分类

### 1. 吞吐量指标

| 指标名称 | PromQL查询 | 说明 | 单位 |
|---------|-----------|------|------|
| **Span接收速率** | `rate(otelcol_receiver_accepted_spans[1m])` | 每秒接收的Span数 | spans/s |
| **Span导出速率** | `rate(otelcol_exporter_sent_spans[1m])` | 每秒导出的Span数 | spans/s |
| **Metric接收速率** | `rate(otelcol_receiver_accepted_metric_points[1m])` | 每秒接收的指标点数 | points/s |
| **Metric导出速率** | `rate(otelcol_exporter_sent_metric_points[1m])` | 每秒导出的指标点数 | points/s |
| **Log接收速率** | `rate(otelcol_receiver_accepted_log_records[1m])` | 每秒接收的日志记录数 | records/s |

### 2. 可靠性指标

| 指标名称 | PromQL查询 | 说明 |
|---------|-----------|------|
| **导出失败率** | `rate(otelcol_exporter_send_failed_spans[1m])` | Span导出失败速率 |
| **接收拒绝率** | `rate(otelcol_receiver_refused_spans[1m])` | Span接收拒绝速率 |
| **导出成功率** | `rate(otelcol_exporter_sent_spans[5m]) / (rate(otelcol_exporter_sent_spans[5m]) + rate(otelcol_exporter_send_failed_spans[5m])) * 100` | 导出成功百分比 |

### 3. 性能指标

| 指标名称 | PromQL查询 | 说明 | 目标 |
|---------|-----------|------|------|
| **CPU使用率** | `rate(process_cpu_seconds_total[1m])` | CPU核心使用 | <0.7 (70%) |
| **内存使用** | `process_resident_memory_bytes` | 常驻内存 | <1.5GB |
| **导出延迟P95** | `histogram_quantile(0.95, rate(otelcol_exporter_send_latency_bucket[5m]))` | 95分位延迟 | <50ms |
| **导出延迟P99** | `histogram_quantile(0.99, rate(otelcol_exporter_send_latency_bucket[5m]))` | 99分位延迟 | <100ms |

### 4. 队列指标

| 指标名称 | PromQL查询 | 说明 |
|---------|-----------|------|
| **队列大小** | `otelcol_exporter_queue_size` | 当前队列中的项目数 |
| **队列容量** | `otelcol_exporter_queue_capacity` | 队列最大容量 |
| **队列使用率** | `otelcol_exporter_queue_size / otelcol_exporter_queue_capacity * 100` | 队列使用百分比 |

---

## 🔧 前置准备

### 环境要求

```yaml
# 本地环境
required_services:
  - otel-collector: "localhost:8889"  # Prometheus metrics端点
  - prometheus: "localhost:9090"
  - grafana: "localhost:3000"
  - jaeger: "localhost:16686"
  - tracegen: 压测工具

# 验证服务
services_check:
  - curl http://localhost:8889/metrics  # Collector指标
  - curl http://localhost:9090/-/healthy  # Prometheus健康检查
  - curl http://localhost:16686/  # Jaeger UI
```

### 启动环境

```bash
# 使用Docker Compose
cd otlp/semantics/scaffold
./scripts/run_compose.sh up

# 等待服务就绪
sleep 30

# 验证
./scripts/prom_query.sh
```

---

## 📊 基准测量流程

### 步骤1: 基线测量（无负载）

```bash
#!/bin/bash
# baseline-measurement.sh

echo "=== 基线测量（无负载） ==="

# 停止数据生成器
docker-compose stop tracegen

# 等待队列清空
sleep 60

# 测量基线
baseline_cpu=$(curl -s 'http://localhost:9090/api/v1/query?query=rate(process_cpu_seconds_total[5m])' | \
  jq -r '.data.result[0].value[1]')
baseline_memory=$(curl -s 'http://localhost:9090/api/v1/query?query=process_resident_memory_bytes' | \
  jq -r '.data.result[0].value[1]')

echo "基线CPU: $baseline_cpu 核"
echo "基线内存: $(echo "scale=2; $baseline_memory / 1024 / 1024 / 1024" | bc) GB"

# 保存基线
cat > baseline.json <<EOF
{
  "timestamp": "$(date -Iseconds)",
  "cpu": $baseline_cpu,
  "memory": $baseline_memory
}
EOF
```

### 步骤2: 负载测试

```bash
#!/bin/bash
# load-test.sh

RATE=${1:-1000}  # 默认1000 spans/s
DURATION=${2:-15}  # 默认15分钟

echo "=== 负载测试 (${RATE} spans/s, ${DURATION}分钟) ==="

# 启动tracegen
docker-compose up -d tracegen
docker-compose exec tracegen tracegen \
  --otlp-endpoint=otel-collector:4317 \
  --otlp-insecure \
  --rate=$RATE \
  --duration=${DURATION}m \
  --workers=4

echo "✓ 负载测试启动"
echo "等待${DURATION}分钟收集数据..."
sleep $((DURATION * 60))

echo "✓ 负载测试完成"
```

### 步骤3: 指标收集

```bash
#!/bin/bash
# collect-metrics.sh

echo "=== 收集性能指标 ==="

# 吞吐量
spans_received=$(curl -s 'http://localhost:9090/api/v1/query?query=rate(otelcol_receiver_accepted_spans[15m])' | \
  jq -r '.data.result[0].value[1]')
spans_exported=$(curl -s 'http://localhost:9090/api/v1/query?query=rate(otelcol_exporter_sent_spans[15m])' | \
  jq -r '.data.result[0].value[1]')
spans_failed=$(curl -s 'http://localhost:9090/api/v1/query?query=rate(otelcol_exporter_send_failed_spans[15m])' | \
  jq -r '.data.result[0].value[1] // 0')

# 性能
cpu=$(curl -s 'http://localhost:9090/api/v1/query?query=rate(process_cpu_seconds_total[15m])' | \
  jq -r '.data.result[0].value[1]')
memory=$(curl -s 'http://localhost:9090/api/v1/query?query=process_resident_memory_bytes' | \
  jq -r '.data.result[0].value[1]')
latency_p95=$(curl -s 'http://localhost:9090/api/v1/query?query=histogram_quantile(0.95, rate(otelcol_exporter_send_latency_bucket[15m]))' | \
  jq -r '.data.result[0].value[1] // 0')

# 可靠性
failure_rate=$(echo "scale=4; $spans_failed / $spans_received * 100" | bc)

# 输出结果
cat > results.json <<EOF
{
  "timestamp": "$(date -Iseconds)",
  "throughput": {
    "spans_received_per_sec": $spans_received,
    "spans_exported_per_sec": $spans_exported,
    "spans_failed_per_sec": $spans_failed
  },
  "performance": {
    "cpu_cores": $cpu,
    "memory_bytes": $memory,
    "latency_p95_ms": $latency_p95
  },
  "reliability": {
    "failure_rate_percent": $failure_rate
  }
}
EOF

cat results.json | jq .
```

---

## 📈 PromQL查询速查表

### 基础查询

```promql
# 1. 当前接收速率
rate(otelcol_receiver_accepted_spans[1m])

# 2. 按接收器分组
sum by (receiver) (rate(otelcol_receiver_accepted_spans[1m]))

# 3. 按导出器分组
sum by (exporter) (rate(otelcol_exporter_sent_spans[1m]))

# 4. 总体吞吐量
sum(rate(otelcol_receiver_accepted_spans[1m]))
```

### 高级查询

```promql
# 5. 导出成功率
sum(rate(otelcol_exporter_sent_spans[5m])) 
/ 
(sum(rate(otelcol_exporter_sent_spans[5m])) + sum(rate(otelcol_exporter_send_failed_spans[5m]))) 
* 100

# 6. CPU使用率变化
(rate(process_cpu_seconds_total[5m]) - rate(process_cpu_seconds_total[5m] offset 1h)) 
/ 
rate(process_cpu_seconds_total[5m] offset 1h) 
* 100

# 7. 内存增长率
deriv(process_resident_memory_bytes[10m])

# 8. 批处理效率
rate(otelcol_processor_batch_batch_send_size_sum[1m])
/
rate(otelcol_processor_batch_batch_send_size_count[1m])

# 9. 队列健康度
(otelcol_exporter_queue_size / otelcol_exporter_queue_capacity) < 0.8

# 10. 延迟分布对比
histogram_quantile(0.50, rate(otelcol_exporter_send_latency_bucket[5m])) as p50,
histogram_quantile(0.95, rate(otelcol_exporter_send_latency_bucket[5m])) as p95,
histogram_quantile(0.99, rate(otelcol_exporter_send_latency_bucket[5m])) as p99
```

### 告警相关查询

```promql
# 11. 检测异常失败率
rate(otelcol_exporter_send_failed_spans[5m]) > 
bool 2 * avg_over_time(rate(otelcol_exporter_send_failed_spans[5m])[7d:5m])

# 12. CPU异常
rate(process_cpu_seconds_total[5m]) > 0.7

# 13. 内存异常
process_resident_memory_bytes > 1.5e9

# 14. 队列积压
otelcol_exporter_queue_size / otelcol_exporter_queue_capacity > 0.8
```

---

## 🎯 性能门槛建议

### 基准门槛

| 维度 | 指标 | 目标 | 说明 |
|------|------|------|------|
| **吞吐量** | Spans接收 | ≥10,000 spans/s | 中等规模 |
| | Spans导出 | ≥99%接收量 | 数据完整性 |
| **性能** | CPU | <40% | 单核使用率 |
| | 内存 | <1GB | 常驻内存 |
| | 延迟P95 | <50ms | 用户感知 |
| **可靠性** | 失败率 | <0.1% | 数据可靠性 |
| | 队列使用 | <80% | 有缓冲空间 |

### OTTL规则影响门槛

```yaml
# OTTL规则性能影响评估
ottl_overhead_thresholds:
  simple_transform:
    cpu_overhead: "<2%"
    latency_overhead: "<5ms"
  
  hash_function:
    cpu_overhead: "<5%"
    latency_overhead: "<10ms"
  
  regex_match:
    cpu_overhead: "<10%"
    latency_overhead: "<15ms"
  
  complex_logic:
    cpu_overhead: "<15%"
    latency_overhead: "<20ms"
```

---

## 📝 测量报告模板

### 简化版报告

```markdown
# OTLP Collector性能测量报告

**日期**: 2025-10-17
**环境**: Docker Compose / 本地
**负载**: 1000 spans/s × 15分钟

## 基准指标

| 指标 | 值 | 目标 | 状态 |
|------|---|------|------|
| Span接收速率 | 1,002 spans/s | ≥1,000 | ✅ |
| Span导出速率 | 1,001 spans/s | ≥990 | ✅ |
| CPU使用率 | 0.35 核 | <0.4 | ✅ |
| 内存使用 | 856 MB | <1024 MB | ✅ |
| 导出失败率 | 0.01% | <0.1% | ✅ |
| P95延迟 | 42 ms | <50 ms | ✅ |

## 结论

所有指标达标，系统运行正常。
```

### 完整版报告

参考：[RESULTS_REPORT_TEMPLATE.md](./RESULTS_REPORT_TEMPLATE.md)

---

## 🔬 高级测量技巧

### 1. 对比测试

```bash
# 测试OTTL规则前后性能
# 1. 基线测试（无OTTL）
./load-test.sh 1000 15
./collect-metrics.sh > baseline-no-ottl.json

# 2. 应用OTTL规则
kubectl apply -f ottl-rules.yaml

# 3. 对比测试
./load-test.sh 1000 15
./collect-metrics.sh > with-ottl.json

# 4. 计算差异
jq -s '.[1].performance.cpu_cores - .[0].performance.cpu_cores' \
  baseline-no-ottl.json with-ottl.json
```

### 2. 压力测试

```bash
# 逐步增加负载找到性能拐点
for rate in 1000 2000 5000 10000 20000 50000; do
  echo "测试速率: $rate spans/s"
  ./load-test.sh $rate 10
  ./collect-metrics.sh > results-${rate}.json
  
  # 检查是否达到瓶颈
  cpu=$(jq -r '.performance.cpu_cores' results-${rate}.json)
  if (( $(echo "$cpu > 0.8" | bc -l) )); then
    echo "⚠️  达到CPU瓶颈: $cpu"
    break
  fi
done
```

### 3. 长时间稳定性测试

```bash
# 24小时稳定性测试
./load-test.sh 5000 1440  # 24小时

# 每小时采样
for hour in {1..24}; do
  sleep 3600
  ./collect-metrics.sh > stability-hour-${hour}.json
  
  # 检查内存泄漏
  memory=$(jq -r '.performance.memory_bytes' stability-hour-${hour}.json)
  echo "Hour $hour: Memory = $(echo "scale=2; $memory / 1024 / 1024 / 1024" | bc) GB"
done
```

---

## 🛠️ 自动化脚本

### 完整测量脚本

```bash
#!/bin/bash
# full-benchmark.sh

set -e

RATE=${1:-10000}
DURATION=${2:-15}
OUTPUT_DIR="benchmark-$(date +%Y%m%d-%H%M%S)"

mkdir -p $OUTPUT_DIR
cd $OUTPUT_DIR

echo "=== OTLP Collector完整基准测试 ==="
echo "速率: $RATE spans/s"
echo "时长: $DURATION 分钟"
echo ""

# 1. 环境信息
cat > environment.json <<EOF
{
  "date": "$(date -Iseconds)",
  "hostname": "$(hostname)",
  "os": "$(uname -s)",
  "arch": "$(uname -m)",
  "cpu_count": $(nproc),
  "total_memory": "$(free -b | awk '/Mem:/ {print $2}')"
}
EOF

# 2. 基线测量
echo "[1/4] 基线测量..."
../baseline-measurement.sh

# 3. 负载测试
echo "[2/4] 负载测试..."
../load-test.sh $RATE $DURATION

# 4. 指标收集
echo "[3/4] 指标收集..."
../collect-metrics.sh

# 5. 生成报告
echo "[4/4] 生成报告..."
cat > report.md <<EOF
# OTLP Collector性能基准报告

**生成时间**: $(date)
**测试负载**: $RATE spans/s × $DURATION 分钟

## 环境信息
\`\`\`json
$(cat environment.json)
\`\`\`

## 基线指标
\`\`\`json
$(cat baseline.json)
\`\`\`

## 测试结果
\`\`\`json
$(cat results.json)
\`\`\`

## 性能评估

$(jq -r '
  if .reliability.failure_rate_percent < 0.1 then "✅ 可靠性: 优秀" else "⚠️  可靠性: 需改进" end,
  if .performance.cpu_cores < 0.4 then "✅ CPU: 优秀" else "⚠️  CPU: 需优化" end,
  if (.performance.memory_bytes / 1024 / 1024 / 1024) < 1 then "✅ 内存: 优秀" else "⚠️  内存: 需优化" end
' results.json)
EOF

echo ""
echo "✅ 测试完成"
echo "报告位置: $OUTPUT_DIR/report.md"
cat report.md
```

---

## 📚 相关文档

- [告警基线](./ALERTING_BASELINE.md) - 告警规则配置
- [运维手册](./RUNBOOK.md) - 日常运维流程
- [性能优化](./PERFORMANCE_OPTIMIZATION_MANUAL.md) - 优化建议
- [结果报告模板](./RESULTS_REPORT_TEMPLATE.md) - 详细报告格式
- [项目对标矩阵](./PROJECT_MAPPING_MATRIX.md) - 指标填报

---

## 📝 变更历史

| 版本 | 日期 | 说明 |
|------|------|------|
| 2.0 | 2025-10-17 | 完整版发布：扩展为生产级测量指南 |
| 1.0 | 2025-09-XX | 初始版本 |

---

**科学测量，精确优化！** 📊✨
