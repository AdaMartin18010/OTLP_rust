# 快速入门指南

本指南将帮助您在几分钟内启动并运行 OTLP Rust 服务器。

## 前提条件

- Rust 1.90 或更高版本
- Docker (可选)
- Kubernetes 集群 (可选)

## 安装

### 方法 1: 从源码构建

```bash
# 克隆仓库
git clone https://github.com/your-org/otlp-rust.git
cd otlp-rust

# 构建项目
cargo build --release

# 运行服务器
./target/release/otlp-server
```

### 方法 2: 使用 Docker

```bash
# 拉取镜像
docker pull otlp/otlp-server:latest

# 运行容器
docker run -p 4317:4317 -p 4318:4318 -p 8080:8080 -p 8081:8081 otlp/otlp-server:latest
```

### 方法 3: 使用 Kubernetes

```bash
# 应用 Kubernetes 配置
kubectl apply -f k8s/otlp-deployment.yaml
kubectl apply -f k8s/otlp-hpa.yaml
kubectl apply -f k8s/otlp-ingress.yaml

# 检查部署状态
kubectl get pods -n otlp-system
kubectl get services -n otlp-system
```

## 基本配置

创建配置文件 `config.yaml`:

```yaml
server:
  grpc:
    endpoint: "0.0.0.0:4317"
    max_connections: 1000
  http:
    endpoint: "0.0.0.0:4318"
    max_connections: 1000
  metrics:
    endpoint: "0.0.0.0:8080"
    path: "/metrics"
  health:
    endpoint: "0.0.0.0:8081"
    path: "/health"

performance:
  circuit_breaker:
    failure_threshold: 10
    recovery_timeout: 5s
    half_open_max_calls: 5
    sliding_window_size: 60s
    minimum_calls: 10
  memory_pool:
    max_size: 100
    initial_size: 10
    object_ttl: 300s
    cleanup_interval: 60s
  batch_processor:
    max_batch_size: 1000
    min_batch_size: 10
    batch_timeout: 100ms
    max_wait_time: 5s
    concurrency: 4
    enable_compression: true
    memory_limit: 100MB
  connection_pool:
    max_connections: 100
    min_connections: 5
    connection_timeout: 30s
    idle_timeout: 300s
    max_lifetime: 3600s
    health_check_interval: 60s

resilience:
  retry:
    max_attempts: 3
    initial_delay: 100ms
    max_delay: 5s
    multiplier: 2.0
    jitter: true
  timeout:
    request_timeout: 30s
    connection_timeout: 10s
    read_timeout: 30s
    write_timeout: 30s
  graceful_degradation:
    enabled: true
    fallback_enabled: true
    cache_enabled: true
    cache_ttl: 300s

monitoring:
  metrics:
    enabled: true
    interval: 10s
    retention: 24h
  logging:
    level: "info"
    format: "json"
    output: "stdout"
  tracing:
    enabled: true
    sampling_rate: 0.1
    jaeger_endpoint: "http://jaeger-collector:14268/api/traces"

storage:
  type: "memory"
  max_size: "1GB"
  cleanup_interval: "1h"
  compression: true
```

## 验证安装

### 健康检查

```bash
# 检查服务器健康状态
curl http://localhost:8081/health

# 预期响应
{
  "status": "healthy",
  "timestamp": "2024-01-01T00:00:00Z",
  "version": "1.0.0",
  "uptime": "1h30m45s"
}
```

### 指标检查

```bash
# 查看 Prometheus 指标
curl http://localhost:8080/metrics

# 预期响应
# HELP otlp_requests_total Total number of requests
# TYPE otlp_requests_total counter
otlp_requests_total{method="grpc",status="success"} 1000
otlp_requests_total{method="http",status="success"} 500
# HELP otlp_response_time_seconds Response time in seconds
# TYPE otlp_response_time_seconds histogram
otlp_response_time_seconds_bucket{le="0.001"} 100
otlp_response_time_seconds_bucket{le="0.005"} 500
otlp_response_time_seconds_bucket{le="0.01"} 800
otlp_response_time_seconds_bucket{le="+Inf"} 1000
```

## 发送测试数据

### 使用 gRPC 客户端

```rust
use otlp::{OtlpClient, TraceData, MetricData, LogData};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建客户端
    let client = OtlpClient::new()
        .with_endpoint("http://localhost:4317")
        .with_timeout(std::time::Duration::from_secs(30))
        .build()?;
    
    // 发送追踪数据
    let trace_data = TraceData {
        trace_id: "test-trace-id".to_string(),
        span_id: "test-span-id".to_string(),
        parent_span_id: None,
        name: "test-operation".to_string(),
        span_kind: otlp::data::SpanKind::Internal,
        start_time: 0,
        end_time: 1000000,
        status: otlp::data::SpanStatus::default(),
        attributes: std::collections::HashMap::new(),
        events: vec![],
        links: vec![],
    };
    
    client.send_trace(trace_data).await?;
    
    // 发送指标数据
    let metric_data = MetricData {
        name: "test_metric".to_string(),
        description: "Test metric".to_string(),
        unit: "count".to_string(),
        data_type: otlp::data::MetricDataType::Counter,
        data_points: vec![],
        resource_attributes: std::collections::HashMap::new(),
        scope_attributes: std::collections::HashMap::new(),
    };
    
    client.send_metric(metric_data).await?;
    
    // 发送日志数据
    let log_data = LogData {
        timestamp: 0,
        severity: otlp::data::Severity::Info,
        body: "Test log message".to_string(),
        attributes: std::collections::HashMap::new(),
        resource_attributes: std::collections::HashMap::new(),
        scope_attributes: std::collections::HashMap::new(),
    };
    
    client.send_log(log_data).await?;
    
    println!("数据发送成功！");
    Ok(())
}
```

### 使用 HTTP 客户端

```bash
# 发送追踪数据
curl -X POST http://localhost:4318/v1/traces \
  -H "Content-Type: application/json" \
  -d '{
    "resourceSpans": [{
      "resource": {
        "attributes": [{
          "key": "service.name",
          "value": {"stringValue": "test-service"}
        }]
      },
      "scopeSpans": [{
        "scope": {
          "name": "test-scope",
          "version": "1.0.0"
        },
        "spans": [{
          "traceId": "test-trace-id",
          "spanId": "test-span-id",
          "name": "test-operation",
          "kind": "SPAN_KIND_INTERNAL",
          "startTimeUnixNano": "0",
          "endTimeUnixNano": "1000000",
          "status": {"code": "STATUS_CODE_OK"}
        }]
      }]
    }]
  }'

# 发送指标数据
curl -X POST http://localhost:4318/v1/metrics \
  -H "Content-Type: application/json" \
  -d '{
    "resourceMetrics": [{
      "resource": {
        "attributes": [{
          "key": "service.name",
          "value": {"stringValue": "test-service"}
        }]
      },
      "scopeMetrics": [{
        "scope": {
          "name": "test-scope",
          "version": "1.0.0"
        },
        "metrics": [{
          "name": "test_metric",
          "description": "Test metric",
          "unit": "count",
          "sum": {
            "dataPoints": [{
              "timeUnixNano": "0",
              "asInt": "1"
            }]
          }
        }]
      }]
    }]
  }'

# 发送日志数据
curl -X POST http://localhost:4318/v1/logs \
  -H "Content-Type: application/json" \
  -d '{
    "resourceLogs": [{
      "resource": {
        "attributes": [{
          "key": "service.name",
          "value": {"stringValue": "test-service"}
        }]
      },
      "scopeLogs": [{
        "scope": {
          "name": "test-scope",
          "version": "1.0.0"
        },
        "logRecords": [{
          "timeUnixNano": "0",
          "severityText": "INFO",
          "body": {"stringValue": "Test log message"}
        }]
      }]
    }]
  }'
```

## 监控和观察

### 查看实时指标

```bash
# 查看 Prometheus 指标
curl http://localhost:8080/metrics | grep otlp_

# 查看健康状态
curl http://localhost:8081/health

# 查看就绪状态
curl http://localhost:8081/ready
```

### 使用 Grafana 仪表板

1. 访问 Grafana: <http://localhost:3000>
2. 使用默认凭据登录: admin/admin
3. 导入 OTLP 仪表板
4. 查看实时监控数据

## 故障排查

### 常见问题

1. **端口被占用**

   ```bash
   # 检查端口使用情况
   netstat -tlnp | grep :4317
   lsof -i :4317
   ```

2. **内存不足**

   ```bash
   # 检查内存使用
   free -h
   # 调整内存限制
   export RUST_MAX_MEMORY=1GB
   ```

3. **连接超时**

   ```bash
   # 检查网络连接
   telnet localhost 4317
   # 调整超时设置
   export OTLP_TIMEOUT=60s
   ```

### 日志分析

```bash
# 查看服务器日志
tail -f /var/log/otlp/server.log

# 查看错误日志
grep "ERROR" /var/log/otlp/server.log

# 查看性能日志
grep "PERF" /var/log/otlp/server.log
```

## 下一步

- 阅读 [配置指南](configuration.md) 了解详细配置选项
- 查看 [示例代码](examples.md) 了解更多使用场景
- 参考 [API 文档](../api/client.md) 了解完整的 API 接口
- 学习 [性能优化](../advanced/performance.md) 提升系统性能

## 获取帮助

如果您遇到问题，请：

1. 查看 [故障排查指南](../deployment/troubleshooting.md)
2. 在 [GitHub Issues](https://github.com/your-org/otlp-rust/issues) 中搜索相关问题
3. 创建新的 Issue 描述您的问题
4. 加入我们的 [讨论区](https://github.com/your-org/otlp-rust/discussions) 进行交流
