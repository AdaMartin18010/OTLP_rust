# PostgreSQL All-in-One 监控面板与告警配置 - 2025年

## 📋 执行摘要

本文档提供了PostgreSQL All-in-One架构的完整监控面板和告警配置方案，包括Prometheus指标收集、Grafana仪表板设计、告警规则配置和自动化运维脚本。
通过全面的监控体系，确保系统的高可用性和性能优化。

## 🎯 监控体系架构

### 1. 监控分层架构

```text
┌───────────────────────────────────────────────────────────────┐
│                    监控展示层 (Visualization)                  │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌─────────┐  │
│  │  Grafana    │ │  Kibana     │ │  Jaeger     │ │ 自定义  │  │
│  │ 仪表板       │ │ 日志分析    │ │ 链路追踪     │ │ 监控    │  │
│  └─────────────┘ └─────────────┘ └─────────────┘ └─────────┘  │
├───────────────────────────────────────────────────────────────┤
│                    监控分析层 (Analysis)                      │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌─────────┐ │
│  │ Prometheus  │ │  AlertManager│ │  Thanos     │ │ 自定义  │ │
│  │ 指标收集     │ │ 告警管理     │ │ 长期存储    │ │ 分析     │ │
│  └─────────────┘ └─────────────┘ └─────────────┘ └─────────┘ │
├───────────────────────────────────────────────────────────────┤
│                    数据收集层 (Collection)                     │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌─────────┐  │
│  │ PostgreSQL  │ │   Redis     │ │  System     │ │ 应用    │  │
│  │  Exporter   │ │  Exporter   │ │  Exporter   │ │ 指标    │  │
│  └─────────────┘ └─────────────┘ └─────────────┘ └─────────┘  │
└───────────────────────────────────────────────────────────────┘
```

### 2. 监控指标分类

| 指标类别 | 监控内容 | 告警阈值 | 重要性 |
|---------|----------|----------|--------|
| **可用性指标** | 服务状态、连接数、错误率 | 服务不可用 | 🔴 高 |
| **性能指标** | 响应时间、吞吐量、资源使用率 | 响应时间>1s | 🟡 中 |
| **容量指标** | 存储使用率、内存使用率 | 使用率>80% | 🟡 中 |
| **业务指标** | 用户数、交易量、成功率 | 成功率<95% | 🔴 高 |

## 📊 Prometheus 配置

### 1. Prometheus 主配置

```yaml
# prometheus.yml
global:
  scrape_interval: 15s
  evaluation_interval: 15s
  external_labels:
    cluster: 'postgresql-all-in-one'
    environment: 'production'

rule_files:
  - "rules/*.yml"

alerting:
  alertmanagers:
    - static_configs:
        - targets:
          - alertmanager:9093

scrape_configs:
  # PostgreSQL 监控
  - job_name: 'postgresql'
    static_configs:
      - targets: ['postgresql-exporter:9187']
    scrape_interval: 5s
    metrics_path: /metrics
    relabel_configs:
      - source_labels: [__address__]
        target_label: instance
        regex: '([^:]+):.*'
        replacement: '${1}'

  # Redis 监控
  - job_name: 'redis'
    static_configs:
      - targets: ['redis-exporter:9121']
    scrape_interval: 5s
    metrics_path: /metrics

  # 系统监控
  - job_name: 'node'
    static_configs:
      - targets: ['node-exporter:9100']
    scrape_interval: 15s
    metrics_path: /metrics

  # 应用监控
  - job_name: 'postgresql-all-in-one-app'
    static_configs:
      - targets: ['app:8080']
    scrape_interval: 10s
    metrics_path: /metrics

  # Prometheus 自身监控
  - job_name: 'prometheus'
    static_configs:
      - targets: ['localhost:9090']
    scrape_interval: 15s

  # Grafana 监控
  - job_name: 'grafana'
    static_configs:
      - targets: ['grafana:3000']
    scrape_interval: 30s
    metrics_path: /metrics
```

### 2. 告警规则配置

#### 2.1 数据库告警规则

```yaml
# rules/postgresql.yml
groups:
- name: postgresql
  rules:
  # 数据库连接告警
  - alert: PostgreSQLDown
    expr: pg_up == 0
    for: 1m
    labels:
      severity: critical
    annotations:
      summary: "PostgreSQL 数据库不可用"
      description: "PostgreSQL 数据库在 {{ $labels.instance }} 上已经不可用超过 1 分钟"

  - alert: PostgreSQLTooManyConnections
    expr: pg_stat_database_numbackends / pg_settings_max_connections * 100 > 80
    for: 2m
    labels:
      severity: warning
    annotations:
      summary: "PostgreSQL 连接数过高"
      description: "PostgreSQL 连接数使用率已达到 {{ $value }}%，超过 80% 阈值"

  # 查询性能告警
  - alert: PostgreSQLSlowQueries
    expr: rate(pg_stat_statements_total_time[5m]) > 1000
    for: 5m
    labels:
      severity: warning
    annotations:
      summary: "PostgreSQL 慢查询告警"
      description: "PostgreSQL 平均查询时间超过 1 秒，当前值: {{ $value }}ms"

  # 缓存命中率告警
  - alert: PostgreSQLLowCacheHitRatio
    expr: rate(pg_stat_database_blks_hit[5m]) / (rate(pg_stat_database_blks_hit[5m]) + rate(pg_stat_database_blks_read[5m])) * 100 < 90
    for: 5m
    labels:
      severity: warning
    annotations:
      summary: "PostgreSQL 缓存命中率过低"
      description: "PostgreSQL 缓存命中率仅为 {{ $value }}%，低于 90% 阈值"

  # 锁等待告警
  - alert: PostgreSQLLockWaits
    expr: pg_locks_count{mode="ExclusiveLock"} > 10
    for: 1m
    labels:
      severity: warning
    annotations:
      summary: "PostgreSQL 锁等待过多"
      description: "PostgreSQL 存在 {{ $value }} 个排他锁等待"

  # 复制延迟告警
  - alert: PostgreSQLReplicationLag
    expr: pg_replication_lag > 30
    for: 2m
    labels:
      severity: warning
    annotations:
      summary: "PostgreSQL 复制延迟过高"
      description: "PostgreSQL 复制延迟已达到 {{ $value }} 秒"
```

#### 2.2 系统资源告警规则

```yaml
# rules/system.yml
groups:
- name: system
  rules:
  # CPU 使用率告警
  - alert: HighCPUUsage
    expr: 100 - (avg by(instance) (rate(node_cpu_seconds_total{mode="idle"}[5m])) * 100) > 80
    for: 5m
    labels:
      severity: warning
    annotations:
      summary: "CPU 使用率过高"
      description: "CPU 使用率已达到 {{ $value }}%，超过 80% 阈值"

  # 内存使用率告警
  - alert: HighMemoryUsage
    expr: (1 - (node_memory_MemAvailable_bytes / node_memory_MemTotal_bytes)) * 100 > 85
    for: 5m
    labels:
      severity: warning
    annotations:
      summary: "内存使用率过高"
      description: "内存使用率已达到 {{ $value }}%，超过 85% 阈值"

  # 磁盘使用率告警
  - alert: HighDiskUsage
    expr: (1 - (node_filesystem_avail_bytes / node_filesystem_size_bytes)) * 100 > 80
    for: 5m
    labels:
      severity: warning
    annotations:
      summary: "磁盘使用率过高"
      description: "磁盘使用率已达到 {{ $value }}%，超过 80% 阈值"

  # 网络连接数告警
  - alert: HighNetworkConnections
    expr: node_netstat_Tcp_CurrEstab > 10000
    for: 2m
    labels:
      severity: warning
    annotations:
      summary: "网络连接数过高"
      description: "当前网络连接数已达到 {{ $value }}，超过 10000 阈值"
```

#### 2.3 Redis 告警规则

```yaml
# rules/redis.yml
groups:
- name: redis
  rules:
  # Redis 服务状态告警
  - alert: RedisDown
    expr: redis_up == 0
    for: 1m
    labels:
      severity: critical
    annotations:
      summary: "Redis 服务不可用"
      description: "Redis 服务在 {{ $labels.instance }} 上已经不可用超过 1 分钟"

  # Redis 内存使用率告警
  - alert: RedisHighMemoryUsage
    expr: redis_memory_used_bytes / redis_memory_max_bytes * 100 > 80
    for: 2m
    labels:
      severity: warning
    annotations:
      summary: "Redis 内存使用率过高"
      description: "Redis 内存使用率已达到 {{ $value }}%，超过 80% 阈值"

  # Redis 连接数告警
  - alert: RedisTooManyConnections
    expr: redis_connected_clients > 800
    for: 2m
    labels:
      severity: warning
    annotations:
      summary: "Redis 连接数过多"
      description: "Redis 连接数已达到 {{ $value }}，超过 800 阈值"

  # Redis 慢查询告警
  - alert: RedisSlowQueries
    expr: rate(redis_slowlog_length[5m]) > 10
    for: 5m
    labels:
      severity: warning
    annotations:
      summary: "Redis 慢查询过多"
      description: "Redis 慢查询数量过多，当前速率: {{ $value }} 次/秒"
```

## 📈 Grafana 仪表板配置

### 1. PostgreSQL 主仪表板

```json
{
  "dashboard": {
    "id": null,
    "title": "PostgreSQL All-in-One Dashboard",
    "tags": ["postgresql", "database", "all-in-one"],
    "timezone": "browser",
    "refresh": "5s",
    "time": {
      "from": "now-1h",
      "to": "now"
    },
    "panels": [
      {
        "id": 1,
        "title": "数据库连接数",
        "type": "graph",
        "gridPos": {"h": 8, "w": 12, "x": 0, "y": 0},
        "targets": [
          {
            "expr": "pg_stat_database_numbackends",
            "legendFormat": "活跃连接数",
            "refId": "A"
          },
          {
            "expr": "pg_settings_max_connections",
            "legendFormat": "最大连接数",
            "refId": "B"
          }
        ],
        "yAxes": [
          {
            "label": "连接数",
            "min": 0
          }
        ],
        "thresholds": [
          {
            "value": 160,
            "colorMode": "critical",
            "op": "gt"
          }
        ]
      },
      {
        "id": 2,
        "title": "查询性能",
        "type": "graph",
        "gridPos": {"h": 8, "w": 12, "x": 12, "y": 0},
        "targets": [
          {
            "expr": "rate(pg_stat_database_tup_returned[5m])",
            "legendFormat": "返回行数/秒",
            "refId": "A"
          },
          {
            "expr": "rate(pg_stat_database_tup_fetched[5m])",
            "legendFormat": "获取行数/秒",
            "refId": "B"
          }
        ],
        "yAxes": [
          {
            "label": "行数/秒",
            "min": 0
          }
        ]
      },
      {
        "id": 3,
        "title": "缓存命中率",
        "type": "singlestat",
        "gridPos": {"h": 4, "w": 6, "x": 0, "y": 8},
        "targets": [
          {
            "expr": "rate(pg_stat_database_blks_hit[5m]) / (rate(pg_stat_database_blks_hit[5m]) + rate(pg_stat_database_blks_read[5m])) * 100",
            "legendFormat": "缓存命中率 %",
            "refId": "A"
          }
        ],
        "thresholds": "80,90",
        "valueName": "current",
        "format": "percent",
        "decimals": 2
      },
      {
        "id": 4,
        "title": "事务处理速率",
        "type": "singlestat",
        "gridPos": {"h": 4, "w": 6, "x": 6, "y": 8},
        "targets": [
          {
            "expr": "rate(pg_stat_database_xact_commit[5m]) + rate(pg_stat_database_xact_rollback[5m])",
            "legendFormat": "TPS",
            "refId": "A"
          }
        ],
        "valueName": "current",
        "format": "short",
        "decimals": 0
      },
      {
        "id": 5,
        "title": "锁等待",
        "type": "singlestat",
        "gridPos": {"h": 4, "w": 6, "x": 12, "y": 8},
        "targets": [
          {
            "expr": "pg_locks_count{mode=\"ExclusiveLock\"}",
            "legendFormat": "排他锁",
            "refId": "A"
          }
        ],
        "valueName": "current",
        "format": "short",
        "thresholds": "5,10"
      },
      {
        "id": 6,
        "title": "数据库大小",
        "type": "singlestat",
        "gridPos": {"h": 4, "w": 6, "x": 18, "y": 8},
        "targets": [
          {
            "expr": "pg_database_size_bytes",
            "legendFormat": "数据库大小",
            "refId": "A"
          }
        ],
        "valueName": "current",
        "format": "bytes",
        "decimals": 2
      },
      {
        "id": 7,
        "title": "慢查询统计",
        "type": "table",
        "gridPos": {"h": 8, "w": 24, "x": 0, "y": 12},
        "targets": [
          {
            "expr": "topk(10, rate(pg_stat_statements_total_time[5m]))",
            "legendFormat": "{{query}}",
            "refId": "A",
            "format": "table"
          }
        ],
        "columns": [
          {
            "text": "查询",
            "value": "query"
          },
          {
            "text": "平均时间(ms)",
            "value": "Value"
          }
        ]
      }
    ]
  }
}
```

### 2. 系统资源仪表板

```json
{
  "dashboard": {
    "id": null,
    "title": "System Resources Dashboard",
    "tags": ["system", "resources", "monitoring"],
    "timezone": "browser",
    "refresh": "10s",
    "panels": [
      {
        "id": 1,
        "title": "CPU 使用率",
        "type": "graph",
        "gridPos": {"h": 8, "w": 12, "x": 0, "y": 0},
        "targets": [
          {
            "expr": "100 - (avg by(instance) (rate(node_cpu_seconds_total{mode=\"idle\"}[5m])) * 100)",
            "legendFormat": "CPU 使用率 %",
            "refId": "A"
          }
        ],
        "yAxes": [
          {
            "label": "百分比",
            "min": 0,
            "max": 100
          }
        ],
        "thresholds": [
          {
            "value": 80,
            "colorMode": "critical",
            "op": "gt"
          }
        ]
      },
      {
        "id": 2,
        "title": "内存使用率",
        "type": "graph",
        "gridPos": {"h": 8, "w": 12, "x": 12, "y": 0},
        "targets": [
          {
            "expr": "(1 - (node_memory_MemAvailable_bytes / node_memory_MemTotal_bytes)) * 100",
            "legendFormat": "内存使用率 %",
            "refId": "A"
          }
        ],
        "yAxes": [
          {
            "label": "百分比",
            "min": 0,
            "max": 100
          }
        ],
        "thresholds": [
          {
            "value": 85,
            "colorMode": "critical",
            "op": "gt"
          }
        ]
      },
      {
        "id": 3,
        "title": "磁盘使用率",
        "type": "graph",
        "gridPos": {"h": 8, "w": 12, "x": 0, "y": 8},
        "targets": [
          {
            "expr": "(1 - (node_filesystem_avail_bytes / node_filesystem_size_bytes)) * 100",
            "legendFormat": "{{mountpoint}} 使用率 %",
            "refId": "A"
          }
        ],
        "yAxes": [
          {
            "label": "百分比",
            "min": 0,
            "max": 100
          }
        ],
        "thresholds": [
          {
            "value": 80,
            "colorMode": "critical",
            "op": "gt"
          }
        ]
      },
      {
        "id": 4,
        "title": "网络流量",
        "type": "graph",
        "gridPos": {"h": 8, "w": 12, "x": 12, "y": 8},
        "targets": [
          {
            "expr": "rate(node_network_receive_bytes_total[5m])",
            "legendFormat": "{{device}} 接收",
            "refId": "A"
          },
          {
            "expr": "rate(node_network_transmit_bytes_total[5m])",
            "legendFormat": "{{device}} 发送",
            "refId": "B"
          }
        ],
        "yAxes": [
          {
            "label": "字节/秒",
            "min": 0
          }
        ]
      }
    ]
  }
}
```

### 3. Redis 监控仪表板

```json
{
  "dashboard": {
    "id": null,
    "title": "Redis Monitoring Dashboard",
    "tags": ["redis", "cache", "monitoring"],
    "timezone": "browser",
    "refresh": "5s",
    "panels": [
      {
        "id": 1,
        "title": "Redis 连接数",
        "type": "graph",
        "gridPos": {"h": 8, "w": 12, "x": 0, "y": 0},
        "targets": [
          {
            "expr": "redis_connected_clients",
            "legendFormat": "连接数",
            "refId": "A"
          }
        ],
        "yAxes": [
          {
            "label": "连接数",
            "min": 0
          }
        ]
      },
      {
        "id": 2,
        "title": "Redis 内存使用",
        "type": "graph",
        "gridPos": {"h": 8, "w": 12, "x": 12, "y": 0},
        "targets": [
          {
            "expr": "redis_memory_used_bytes",
            "legendFormat": "已使用内存",
            "refId": "A"
          },
          {
            "expr": "redis_memory_max_bytes",
            "legendFormat": "最大内存",
            "refId": "B"
          }
        ],
        "yAxes": [
          {
            "label": "字节",
            "min": 0
          }
        ]
      },
      {
        "id": 3,
        "title": "Redis 操作统计",
        "type": "graph",
        "gridPos": {"h": 8, "w": 12, "x": 0, "y": 8},
        "targets": [
          {
            "expr": "rate(redis_commands_processed_total[5m])",
            "legendFormat": "命令处理速率",
            "refId": "A"
          }
        ],
        "yAxes": [
          {
            "label": "命令/秒",
            "min": 0
          }
        ]
      },
      {
        "id": 4,
        "title": "Redis 命中率",
        "type": "singlestat",
        "gridPos": {"h": 4, "w": 6, "x": 12, "y": 8},
        "targets": [
          {
            "expr": "rate(redis_keyspace_hits_total[5m]) / (rate(redis_keyspace_hits_total[5m]) + rate(redis_keyspace_misses_total[5m])) * 100",
            "legendFormat": "命中率 %",
            "refId": "A"
          }
        ],
        "valueName": "current",
        "format": "percent",
        "decimals": 2,
        "thresholds": "80,90"
      },
      {
        "id": 5,
        "title": "Redis 键数量",
        "type": "singlestat",
        "gridPos": {"h": 4, "w": 6, "x": 18, "y": 8},
        "targets": [
          {
            "expr": "redis_db_keys",
            "legendFormat": "键数量",
            "refId": "A"
          }
        ],
        "valueName": "current",
        "format": "short",
        "decimals": 0
      }
    ]
  }
}
```

## 🚨 AlertManager 配置

### 1. AlertManager 主配置

```yaml
# alertmanager.yml
global:
  smtp_smarthost: 'localhost:587'
  smtp_from: 'alerts@postgresql-all-in-one.com'
  smtp_auth_username: 'alerts@postgresql-all-in-one.com'
  smtp_auth_password: 'password'

route:
  group_by: ['alertname']
  group_wait: 10s
  group_interval: 10s
  repeat_interval: 1h
  receiver: 'web.hook'
  routes:
  - match:
      severity: critical
    receiver: 'critical-alerts'
  - match:
      severity: warning
    receiver: 'warning-alerts'

receivers:
- name: 'web.hook'
  webhook_configs:
  - url: 'http://127.0.0.1:5001/'

- name: 'critical-alerts'
  email_configs:
  - to: 'admin@postgresql-all-in-one.com'
    subject: '[CRITICAL] PostgreSQL All-in-One Alert'
    body: |
      {{ range .Alerts }}
      Alert: {{ .Annotations.summary }}
      Description: {{ .Annotations.description }}
      {{ end }}
  slack_configs:
  - api_url: 'https://hooks.slack.com/services/YOUR/SLACK/WEBHOOK'
    channel: '#alerts'
    title: 'Critical Alert'
    text: '{{ range .Alerts }}{{ .Annotations.summary }}{{ end }}'

- name: 'warning-alerts'
  email_configs:
  - to: 'ops@postgresql-all-in-one.com'
    subject: '[WARNING] PostgreSQL All-in-One Alert'
    body: |
      {{ range .Alerts }}
      Alert: {{ .Annotations.summary }}
      Description: {{ .Annotations.description }}
      {{ end }}
```

### 2. 告警通知模板

#### 2.1 邮件模板

```html
<!-- email_template.html -->
<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <title>PostgreSQL All-in-One 告警通知</title>
    <style>
        body { font-family: Arial, sans-serif; margin: 20px; }
        .header { background-color: #f44336; color: white; padding: 10px; }
        .content { padding: 20px; }
        .alert { border-left: 4px solid #f44336; padding: 10px; margin: 10px 0; }
        .warning { border-left-color: #ff9800; }
        .critical { border-left-color: #f44336; }
        .footer { background-color: #f5f5f5; padding: 10px; font-size: 12px; }
    </style>
</head>
<body>
    <div class="header">
        <h1>🚨 PostgreSQL All-in-One 告警通知</h1>
    </div>
    
    <div class="content">
        <h2>告警详情</h2>
        {{ range .Alerts }}
        <div class="alert {{ .Labels.severity }}">
            <h3>{{ .Annotations.summary }}</h3>
            <p><strong>描述:</strong> {{ .Annotations.description }}</p>
            <p><strong>实例:</strong> {{ .Labels.instance }}</p>
            <p><strong>时间:</strong> {{ .StartsAt.Format "2006-01-02 15:04:05" }}</p>
            {{ if .Annotations.runbook_url }}
            <p><strong>处理手册:</strong> <a href="{{ .Annotations.runbook_url }}">查看详情</a></p>
            {{ end }}
        </div>
        {{ end }}
        
        <h2>系统状态</h2>
        <p>请及时处理上述告警，确保系统正常运行。</p>
    </div>
    
    <div class="footer">
        <p>此邮件由 PostgreSQL All-in-One 监控系统自动发送</p>
        <p>发送时间: {{ .GroupLabels.alertname }} - {{ .GroupLabels.alertname }}</p>
    </div>
</body>
</html>
```

#### 2.2 Slack 通知模板

```json
{
  "attachments": [
    {
      "color": "{{ if eq .Status \"firing\" }}danger{{ else }}good{{ end }}",
      "title": "PostgreSQL All-in-One 告警",
      "text": "{{ range .Alerts }}{{ .Annotations.summary }}{{ end }}",
      "fields": [
        {
          "title": "告警级别",
          "value": "{{ range .Alerts }}{{ .Labels.severity }}{{ end }}",
          "short": true
        },
        {
          "title": "实例",
          "value": "{{ range .Alerts }}{{ .Labels.instance }}{{ end }}",
          "short": true
        },
        {
          "title": "描述",
          "value": "{{ range .Alerts }}{{ .Annotations.description }}{{ end }}",
          "short": false
        }
      ],
      "footer": "PostgreSQL All-in-One 监控系统",
      "ts": "{{ .GroupLabels.timestamp }}"
    }
  ]
}
```

## 🔧 自动化运维脚本

### 1. 健康检查脚本

```bash
#!/bin/bash
# health_check.sh

echo "=== PostgreSQL All-in-One 健康检查 ==="
echo "检查时间: $(date)"
echo

# 检查 PostgreSQL 状态
echo "=== PostgreSQL 状态检查 ==="
if pg_isready -h localhost -p 5432 -U postgres; then
    echo "✅ PostgreSQL 服务正常"
    
    # 检查连接数
    CONNECTIONS=$(psql -h localhost -p 5432 -U postgres -d postgres -t -c "SELECT count(*) FROM pg_stat_activity;")
    echo "📊 当前连接数: $CONNECTIONS"
    
    # 检查数据库大小
    DB_SIZE=$(psql -h localhost -p 5432 -U postgres -d postgres -t -c "SELECT pg_size_pretty(pg_database_size('postgres'));")
    echo "💾 数据库大小: $DB_SIZE"
    
    # 检查缓存命中率
    CACHE_HIT=$(psql -h localhost -p 5432 -U postgres -d postgres -t -c "SELECT round(100.0 * sum(blks_hit) / (sum(blks_hit) + sum(blks_read)), 2) FROM pg_stat_database;")
    echo "🎯 缓存命中率: $CACHE_HIT%"
else
    echo "❌ PostgreSQL 服务异常"
    exit 1
fi

echo

# 检查 Redis 状态
echo "=== Redis 状态检查 ==="
if redis-cli ping > /dev/null 2>&1; then
    echo "✅ Redis 服务正常"
    
    # 检查连接数
    REDIS_CONNECTIONS=$(redis-cli info clients | grep connected_clients | cut -d: -f2 | tr -d '\r')
    echo "📊 Redis 连接数: $REDIS_CONNECTIONS"
    
    # 检查内存使用
    REDIS_MEMORY=$(redis-cli info memory | grep used_memory_human | cut -d: -f2 | tr -d '\r')
    echo "💾 Redis 内存使用: $REDIS_MEMORY"
    
    # 检查命中率
    REDIS_HITS=$(redis-cli info stats | grep keyspace_hits | cut -d: -f2 | tr -d '\r')
    REDIS_MISSES=$(redis-cli info stats | grep keyspace_misses | cut -d: -f2 | tr -d '\r')
    if [ "$REDIS_HITS" -gt 0 ] || [ "$REDIS_MISSES" -gt 0 ]; then
        REDIS_HIT_RATE=$(echo "scale=2; $REDIS_HITS * 100 / ($REDIS_HITS + $REDIS_MISSES)" | bc)
        echo "🎯 Redis 命中率: $REDIS_HIT_RATE%"
    fi
else
    echo "❌ Redis 服务异常"
    exit 1
fi

echo

# 检查系统资源
echo "=== 系统资源检查 ==="
CPU_USAGE=$(top -bn1 | grep "Cpu(s)" | awk '{print $2}' | cut -d'%' -f1)
echo "🖥️  CPU 使用率: $CPU_USAGE%"

MEMORY_USAGE=$(free | grep Mem | awk '{printf "%.1f", $3/$2 * 100.0}')
echo "🧠 内存使用率: $MEMORY_USAGE%"

DISK_USAGE=$(df -h / | awk 'NR==2{print $5}' | cut -d'%' -f1)
echo "💿 磁盘使用率: $DISK_USAGE%"

echo

# 检查监控服务
echo "=== 监控服务检查 ==="
if curl -s http://localhost:9090/-/healthy > /dev/null; then
    echo "✅ Prometheus 服务正常"
else
    echo "❌ Prometheus 服务异常"
fi

if curl -s http://localhost:3000/api/health > /dev/null; then
    echo "✅ Grafana 服务正常"
else
    echo "❌ Grafana 服务异常"
fi

echo
echo "=== 健康检查完成 ==="
```

### 2. 自动备份脚本

```bash
#!/bin/bash
# backup.sh

BACKUP_DIR="/backup/postgresql"
DATE=$(date +%Y%m%d_%H%M%S)
BACKUP_FILE="postgresql_backup_$DATE.sql"
RETENTION_DAYS=7

echo "=== PostgreSQL 自动备份 ==="
echo "备份时间: $(date)"
echo "备份文件: $BACKUP_FILE"
echo

# 创建备份目录
mkdir -p $BACKUP_DIR

# 执行备份
echo "开始备份数据库..."
pg_dump -h localhost -p 5432 -U postgres -d postgres \
    --verbose \
    --no-password \
    --format=custom \
    --compress=9 \
    --file="$BACKUP_DIR/$BACKUP_FILE"

if [ $? -eq 0 ]; then
    echo "✅ 数据库备份成功"
    
    # 压缩备份文件
    gzip "$BACKUP_DIR/$BACKUP_FILE"
    echo "📦 备份文件已压缩"
    
    # 计算备份文件大小
    BACKUP_SIZE=$(du -h "$BACKUP_DIR/$BACKUP_FILE.gz" | cut -f1)
    echo "💾 备份文件大小: $BACKUP_SIZE"
    
    # 清理旧备份
    echo "🧹 清理 $RETENTION_DAYS 天前的备份文件..."
    find $BACKUP_DIR -name "postgresql_backup_*.sql.gz" -mtime +$RETENTION_DAYS -delete
    echo "✅ 旧备份文件清理完成"
    
else
    echo "❌ 数据库备份失败"
    exit 1
fi

echo
echo "=== 备份完成 ==="
```

### 3. 性能分析脚本

```bash
#!/bin/bash
# performance_analysis.sh

REPORT_DIR="/reports/performance"
DATE=$(date +%Y%m%d_%H%M%S)
REPORT_FILE="performance_report_$DATE.html"

echo "=== PostgreSQL 性能分析报告 ==="
echo "生成时间: $(date)"
echo

# 创建报告目录
mkdir -p $REPORT_DIR

# 生成 HTML 报告
cat > "$REPORT_DIR/$REPORT_FILE" << EOF
<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <title>PostgreSQL 性能分析报告</title>
    <style>
        body { font-family: Arial, sans-serif; margin: 20px; }
        .header { background-color: #2196F3; color: white; padding: 20px; }
        .section { margin: 20px 0; padding: 15px; border: 1px solid #ddd; }
        .metric { display: inline-block; margin: 10px; padding: 10px; background-color: #f5f5f5; }
        table { width: 100%; border-collapse: collapse; }
        th, td { border: 1px solid #ddd; padding: 8px; text-align: left; }
        th { background-color: #f2f2f2; }
    </style>
</head>
<body>
    <div class="header">
        <h1>PostgreSQL 性能分析报告</h1>
        <p>生成时间: $(date)</p>
    </div>
    
    <div class="section">
        <h2>系统概览</h2>
        <div class="metric">
            <strong>数据库版本:</strong> $(psql -h localhost -p 5432 -U postgres -d postgres -t -c "SELECT version();" | head -1)
        </div>
        <div class="metric">
            <strong>运行时间:</strong> $(psql -h localhost -p 5432 -U postgres -d postgres -t -c "SELECT pg_postmaster_start_time();")
        </div>
        <div class="metric">
            <strong>当前连接数:</strong> $(psql -h localhost -p 5432 -U postgres -d postgres -t -c "SELECT count(*) FROM pg_stat_activity;")
        </div>
    </div>
    
    <div class="section">
        <h2>慢查询分析</h2>
        <table>
            <tr>
                <th>查询</th>
                <th>调用次数</th>
                <th>总时间(ms)</th>
                <th>平均时间(ms)</th>
                <th>行数</th>
            </tr>
EOF

# 添加慢查询数据
psql -h localhost -p 5432 -U postgres -d postgres -t -c "
SELECT 
    left(query, 100) as query,
    calls,
    round(total_time::numeric, 2) as total_time,
    round(mean_time::numeric, 2) as mean_time,
    rows
FROM pg_stat_statements 
WHERE mean_time > 1000
ORDER BY mean_time DESC 
LIMIT 10;
" | while read line; do
    if [ ! -z "$line" ]; then
        echo "            <tr><td>$line</td></tr>" >> "$REPORT_DIR/$REPORT_FILE"
    fi
done

cat >> "$REPORT_DIR/$REPORT_FILE" << EOF
        </table>
    </div>
    
    <div class="section">
        <h2>索引使用情况</h2>
        <table>
            <tr>
                <th>表名</th>
                <th>索引名</th>
                <th>索引扫描次数</th>
                <th>索引元组读取</th>
                <th>索引元组获取</th>
            </tr>
EOF

# 添加索引使用数据
psql -h localhost -p 5432 -U postgres -d postgres -t -c "
SELECT 
    tablename,
    indexname,
    idx_tup_read,
    idx_tup_fetch
FROM pg_stat_user_indexes 
WHERE idx_tup_read > 0
ORDER BY idx_tup_read DESC 
LIMIT 10;
" | while read line; do
    if [ ! -z "$line" ]; then
        echo "            <tr><td>$line</td></tr>" >> "$REPORT_DIR/$REPORT_FILE"
    fi
done

cat >> "$REPORT_DIR/$REPORT_FILE" << EOF
        </table>
    </div>
    
    <div class="section">
        <h2>表大小分析</h2>
        <table>
            <tr>
                <th>表名</th>
                <th>大小</th>
                <th>行数</th>
            </tr>
EOF

# 添加表大小数据
psql -h localhost -p 5432 -U postgres -d postgres -t -c "
SELECT 
    schemaname||'.'||tablename as table_name,
    pg_size_pretty(pg_total_relation_size(schemaname||'.'||tablename)) as size,
    n_tup_ins - n_tup_del as row_count
FROM pg_tables t
JOIN pg_stat_user_tables s ON t.tablename = s.relname
WHERE schemaname = 'public'
ORDER BY pg_total_relation_size(schemaname||'.'||tablename) DESC 
LIMIT 10;
" | while read line; do
    if [ ! -z "$line" ]; then
        echo "            <tr><td>$line</td></tr>" >> "$REPORT_DIR/$REPORT_FILE"
    fi
done

cat >> "$REPORT_DIR/$REPORT_FILE" << EOF
        </table>
    </div>
    
    <div class="section">
        <h2>缓存命中率</h2>
        <p>数据库缓存命中率: $(psql -h localhost -p 5432 -U postgres -d postgres -t -c "SELECT round(100.0 * sum(blks_hit) / (sum(blks_hit) + sum(blks_read)), 2) FROM pg_stat_database;")%</p>
    </div>
    
    <div class="section">
        <h2>建议</h2>
        <ul>
            <li>定期分析慢查询并优化索引</li>
            <li>监控缓存命中率，确保在90%以上</li>
            <li>定期清理无用的索引和表</li>
            <li>根据业务需求调整数据库配置参数</li>
        </ul>
    </div>
</body>
</html>
EOF

echo "✅ 性能分析报告已生成: $REPORT_DIR/$REPORT_FILE"
echo "📊 报告大小: $(du -h "$REPORT_DIR/$REPORT_FILE" | cut -f1)"

echo
echo "=== 性能分析完成 ==="
```

## 📋 总结

本文档提供了PostgreSQL All-in-One架构的完整监控面板和告警配置方案，包括：

### 1. 监控体系架构

- **分层监控**: 数据收集、分析、展示三层架构
- **指标分类**: 可用性、性能、容量、业务四类指标
- **工具集成**: Prometheus、Grafana、AlertManager完整集成

### 2. Prometheus 配置

- **指标收集**: PostgreSQL、Redis、系统、应用指标
- **告警规则**: 数据库、系统、Redis告警规则
- **数据存储**: 长期存储和查询优化

### 3. Grafana 仪表板

- **PostgreSQL仪表板**: 连接数、查询性能、缓存命中率
- **系统资源仪表板**: CPU、内存、磁盘、网络监控
- **Redis监控仪表板**: 连接数、内存使用、操作统计

### 4. 告警管理

- **AlertManager配置**: 告警路由、通知渠道
- **通知模板**: 邮件、Slack通知模板
- **告警级别**: 严重、警告两级告警

### 5. 自动化运维

- **健康检查**: 全面的系统健康检查脚本
- **自动备份**: 数据库自动备份和清理
- **性能分析**: 自动生成性能分析报告

通过这套完整的监控体系，可以实时掌握PostgreSQL All-in-One系统的运行状态，及时发现和处理问题，确保系统的高可用性和性能优化。
