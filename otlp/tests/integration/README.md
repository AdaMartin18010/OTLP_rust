# 集成测试环境

本目录包含与 OpenTelemetry Collector 集成测试所需的 Docker Compose 配置。

## 🚀 快速开始

### 1. 启动环境

```bash
# 启动所有服务
docker-compose up -d

# 查看日志
docker-compose logs -f otel-collector

# 检查健康状态
curl http://localhost:13133/
```

### 2. 运行测试

```bash
# 返回项目根目录
cd ../../..

# 运行所有集成测试
cargo test --test integration_test -- --ignored --nocapture

# 运行单个测试
cargo test --test integration_test test_basic_span_export -- --ignored --nocapture
```

### 3. 查看结果

**Jaeger UI** (Traces 可视化):
```
http://localhost:16686
```

**Collector Metrics** (Prometheus):
```
http://localhost:8888/metrics
```

**Health Check**:
```
http://localhost:13133/
```

### 4. 停止环境

```bash
docker-compose down

# 清除所有数据
docker-compose down -v
```

---

## 📊 服务说明

### OpenTelemetry Collector

- **gRPC 端口**: 4317
- **HTTP 端口**: 4318
- **Metrics**: 8888
- **Health Check**: 13133

### Jaeger

- **UI**: 16686
- **gRPC**: 14250

---

## 🔧 配置文件

### `docker-compose.yml`

Docker Compose 服务定义：
- `otel-collector`: OpenTelemetry Collector
- `jaeger`: Jaeger All-in-One

### `otel-collector-config.yaml`

Collector 配置：
- **Receivers**: OTLP (gRPC + HTTP)
- **Processors**: Batch, Resource
- **Exporters**: Logging, Jaeger, Prometheus

---

## 🧪 可用测试

1. `test_basic_span_export` - 基本 span 导出
2. `test_nested_spans` - 嵌套 spans
3. `test_span_attributes_and_events` - 属性和事件
4. `test_concurrent_spans` - 并发 spans
5. `test_error_handling` - 错误处理
6. `test_high_volume_spans` - 高容量 (1000 spans)
7. `test_client_configuration` - 客户端配置

---

## 📝 故障排查

### 问题: 容器无法启动

```bash
# 检查日志
docker-compose logs

# 重新构建
docker-compose up -d --force-recreate
```

### 问题: 端口被占用

```bash
# 检查端口
netstat -an | grep 4317

# 修改 docker-compose.yml 中的端口映射
```

### 问题: Traces 未显示在 Jaeger

1. 检查 Collector 日志:
   ```bash
   docker-compose logs otel-collector | grep "Traces received"
   ```

2. 检查 Jaeger 连接:
   ```bash
   docker-compose logs jaeger
   ```

3. 验证配置:
   确保 `otel-collector-config.yaml` 中 Jaeger exporter 配置正确

---

## 🔍 调试提示

### 查看 Collector 接收的数据

```bash
docker-compose logs -f otel-collector
```

查找:
```
Traces received: X
Spans exported: Y
```

### 验证 OTLP 端点

```bash
# 测试 gRPC 端点
grpcurl -plaintext localhost:4317 list

# 测试 HTTP 端点  
curl http://localhost:4318/v1/traces -X POST
```

---

## 📖 相关文档

- [OpenTelemetry Collector](https://opentelemetry.io/docs/collector/)
- [Jaeger](https://www.jaegertracing.io/docs/)
- [OTLP Specification](https://github.com/open-telemetry/opentelemetry-specification/blob/main/specification/protocol/otlp.md)

---

**最后更新**: 2025-10-18

