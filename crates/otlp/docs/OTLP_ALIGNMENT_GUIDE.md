# OTLP 规范对齐指南

> **版本**: v2.0  
> **最后更新**: 2025年10月17日  
> **状态**: ✅ 完整版  
> **类型**: 元文档 - 文档编写规范

---

## 📋 概述

本指南是**元文档**，用于统一本仓库所有文档在内容组织、术语使用、规范映射方面的对齐方式，确保所有文档在不引用项目代码的前提下，与OpenTelemetry和OTLP规范保持一致。

### 适用范围

- ✅ 所有`otlp/docs`目录下的文档
- ✅ 项目级别的说明文档（README等）
- ✅ 技术指南和最佳实践文档
- ✅ API文档和用户手册

### 目标读者

- 📝 文档编写者
- 🔍 文档审核者
- 👥 技术写作团队
- 🎯 开源贡献者

---

## 一、文档对齐范围

### 1.1 数据模型对齐

**Traces数据模型**:

- ✅ Resource、Scope、Span结构层次
- ✅ Span类型: INTERNAL、SERVER、CLIENT、PRODUCER、CONSUMER
- ✅ Span状态: Unset、Ok、Error
- ✅ SpanContext: TraceId、SpanId、TraceFlags、TraceState
- ✅ 时间戳使用纳秒精度Unix时间

**Metrics数据模型**:

- ✅ Gauge、Sum、Histogram、Summary、ExponentialHistogram
- ✅ 聚合时间性（Temporality）: Delta vs Cumulative
- ✅ 指标命名约定: lowercase, underscore, unit suffix
- ✅ 示例: `http.server.request.duration` (秒), `system.memory.usage` (字节)

**Logs数据模型**:

- ✅ Severity级别: TRACE、DEBUG、INFO、WARN、ERROR、FATAL
- ✅ Body字段: string、structured data
- ✅ 与Traces关联: TraceId、SpanId字段
- ✅ 资源和属性使用语义约定

**参考规范**:

- [OTLP/Traces](https://opentelemetry.io/docs/specs/otlp/#otlpgrpc-traces)
- [OTLP/Metrics](https://opentelemetry.io/docs/specs/otlp/#otlpgrpc-metrics)
- [OTLP/Logs](https://opentelemetry.io/docs/specs/otlp/#otlpgrpc-logs)

---

### 1.2 协议与序列化对齐

**gRPC传输**:

- ✅ 默认端口: `4317`
- ✅ 服务定义:
  - `opentelemetry.proto.collector.trace.v1.TraceService`
  - `opentelemetry.proto.collector.metrics.v1.MetricsService`
  - `opentelemetry.proto.collector.logs.v1.LogsService`
- ✅ 响应处理: 部分成功、错误码、重试头

**HTTP传输**:

- ✅ 默认端口: `4318`
- ✅ 端点路径:
  - `/v1/traces`
  - `/v1/metrics`
  - `/v1/logs`
- ✅ Content-Type:
  - `application/x-protobuf` (Protobuf编码)
  - `application/json` (JSON编码)
- ✅ HTTP状态码语义:
  - `200 OK` - 成功
  - `400 Bad Request` - 请求错误
  - `401 Unauthorized` - 认证失败
  - `429 Too Many Requests` - 限流
  - `500 Internal Server Error` - 服务器错误
  - `503 Service Unavailable` - 暂时不可用（需重试）

**参考规范**:

- [OTLP/gRPC](https://opentelemetry.io/docs/specs/otlp/#otlpgrpc)
- [OTLP/HTTP](https://opentelemetry.io/docs/specs/otlp/#otlphttp)

---

### 1.3 处理与导出对齐

**批处理（Batching）**:

- ✅ 推荐批大小: 512-2048 spans/metrics/logs
- ✅ 推荐发送间隔: 5-10秒
- ✅ 最大队列大小: 2048-10000
- ✅ 超时处理: 强制发送部分批次

**重试策略**:

- ✅ 指数退避 (Exponential Backoff)
- ✅ 初始间隔: 100ms
- ✅ 最大间隔: 30s
- ✅ 乘数: 2.0
- ✅ 抖动 (Jitter): ±25%
- ✅ 最大重试次数: 3-5次
- ✅ 幂等保证: 使用请求ID或序列号

**示例配置**:

```yaml
retry:
  enabled: true
  initial_interval: 100ms
  max_interval: 30s
  max_elapsed_time: 5m
  multiplier: 2.0
```

**压缩**:

- ✅ gRPC: `gzip`、`snappy`（通过`grpc-encoding`头）
- ✅ HTTP: `gzip`、`deflate`（通过`Content-Encoding`头）
- ✅ 权衡: CPU vs 网络带宽
- ✅ 建议: 生产环境启用gzip（压缩率70-80%）

**背压处理**:

- ✅ 优先保护下游服务稳定性
- ✅ 队列满时的策略:
  - Drop oldest (丢弃最旧数据)
  - Drop newest (丢弃最新数据)
  - Block (阻塞，可能导致应用卡顿)
- ✅ 记录丢弃事件到监控指标
- ✅ 触发告警通知运维

**参考规范**:

- [OTLP/Exporter](https://opentelemetry.io/docs/specs/otel/trace/sdk/#span-exporter)

---

### 1.4 运行环境对齐

**云原生环境**:

- ✅ Kubernetes资源属性:
  - `k8s.namespace.name`
  - `k8s.pod.name`
  - `k8s.deployment.name`
  - `k8s.container.name`
- ✅ 服务网格集成: Istio、Linkerd、Consul Connect
- ✅ 自动伸缩: HPA基于CPU/内存/自定义指标
- ✅ 健康检查: `/health/live`、`/health/ready`

**企业应用**:

- ✅ 多租户隔离: 通过Resource属性或独立端点
- ✅ 配额和限流: 基于租户或API Key
- ✅ 审计日志: 记录所有配置变更和敏感操作
- ✅ 合规性: GDPR、SOC2、HIPAA等

**安全要求**:

- ✅ TLS/mTLS: 传输层加密和双向认证
- ✅ 认证: Bearer Token、API Key、OAuth2
- ✅ 授权: RBAC、ABAC
- ✅ 数据脱敏: PII数据自动过滤或混淆

**监控与告警**:

- ✅ 导出自身遥测数据（self-observability）
- ✅ 关键指标:
  - 接收速率、导出速率
  - 错误率、丢弃率
  - 延迟P50/P95/P99
  - 队列大小、内存使用
- ✅ 告警阈值建议:
  - 错误率 > 5% (warning)
  - 错误率 > 10% (critical)
  - 队列使用 > 80% (warning)
  - 内存使用 > 90% (critical)

---

## 二、术语与命名规范

### 2.1 OpenTelemetry官方术语

**核心概念**（必须使用）:

| 术语 | 说明 | ❌ 避免使用 |
|------|------|-----------|
| **Trace** | 分布式追踪 | tracing, 追踪链 |
| **Span** | 追踪单元 | segment, 片段 |
| **Tracer** | 追踪器 | tracker, 跟踪器 |
| **TracerProvider** | 追踪提供者 | trace factory, 追踪工厂 |
| **Metric** | 指标 | measurement, 度量 |
| **Meter** | 指标器 | metrics recorder |
| **MeterProvider** | 指标提供者 | metrics factory |
| **Log** | 日志 | event log, 事件 |
| **Logger** | 日志器 | log writer |
| **LoggerProvider** | 日志提供者 | logger factory |
| **Resource** | 资源 | entity, 实体 |
| **Attribute** | 属性 | tag, label, property |
| **Exporter** | 导出器 | sender, publisher |
| **Processor** | 处理器 | handler, transformer |
| **Sampler** | 采样器 | filter, selector |
| **Context** | 上下文 | scope, environment |
| **Propagator** | 传播器 | injector/extractor |

**数据类型**:

| 术语 | 说明 | 使用场景 |
|------|------|---------|
| **Counter** | 单调递增计数器 | 请求总数、错误总数 |
| **UpDownCounter** | 可增可减计数器 | 活跃连接数 |
| **Gauge** | 瞬时值 | 内存使用量、CPU使用率 |
| **Histogram** | 直方图 | 请求延迟分布 |
| **Summary** | 摘要 | P50/P95/P99延迟 |

---

### 2.2 语义约定（Semantic Conventions）

**资源属性命名规则**:

- ✅ 小写字母
- ✅ 使用点号分隔命名空间
- ✅ 使用下划线分隔单词
- ✅ 示例: `service.name`, `deployment.environment`, `host.name`

**常用资源属性**:

```yaml
# 服务标识
service.name: "payment-service"
service.version: "1.2.3"
service.instance.id: "payment-service-7d4f5b6c8-xk9zl"
service.namespace: "production"

# 部署环境
deployment.environment: "production"
deployment.environment.name: "us-west-2"

# 主机信息
host.name: "node-123.example.com"
host.id: "i-0a1b2c3d4e5f6"
host.type: "m5.xlarge"

# Kubernetes
k8s.namespace.name: "backend"
k8s.pod.name: "payment-service-7d4f5b6c8-xk9zl"
k8s.deployment.name: "payment-service"
k8s.container.name: "app"
k8s.cluster.name: "prod-cluster"

# 云提供商
cloud.provider: "aws"
cloud.region: "us-west-2"
cloud.account.id: "123456789012"
```

**Span属性命名**:

```yaml
# HTTP
http.method: "GET"
http.status_code: 200
http.url: "https://api.example.com/v1/users"
http.route: "/v1/users"
http.target: "/v1/users?page=1"
http.user_agent: "Mozilla/5.0..."

# Database
db.system: "postgresql"
db.name: "users_db"
db.statement: "SELECT * FROM users WHERE id = ?"
db.operation: "SELECT"
db.connection_string: "postgresql://localhost:5432/users_db"

# RPC/gRPC
rpc.system: "grpc"
rpc.service: "UserService"
rpc.method: "GetUser"
rpc.grpc.status_code: 0

# Messaging
messaging.system: "kafka"
messaging.destination: "orders"
messaging.operation: "publish"
messaging.message_id: "msg-12345"
```

**参考规范**:

- [Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/)
- [Resource Conventions](https://opentelemetry.io/docs/specs/semconv/resource/)
- [HTTP Conventions](https://opentelemetry.io/docs/specs/semconv/http/)
- [Database Conventions](https://opentelemetry.io/docs/specs/semconv/database/)

---

### 2.3 禁止使用的术语

**❌ 避免使用实现细节**:

- "我们的代码中..."
- "在src/modules/..."
- "通过XXX函数实现..."
- "底层使用XXX库..."

**✅ 正确表述**:

- "OTLP协议规定..."
- "根据OpenTelemetry规范..."
- "标准实现应当..."
- "推荐配置为..."

---

## 三、文档结构模板

### 3.1 标准文档结构

```markdown
# 文档标题

> **版本**: v1.0  
> **最后更新**: YYYY-MM-DD  
> **状态**: ✅ 完整版 / ⚠️ 草稿 / 🚧 进行中  
> **维护者**: 团队名称

---

## 📋 概述

[简要说明文档目的、适用范围]

### 目标读者

- 角色1
- 角色2

### 前置知识

- 需要了解的概念或文档

---

## 🎯 核心内容

### 章节1

[详细内容]

### 章节2

[详细内容]

---

## 📚 相关文档

- [相关文档1](链接)
- [相关文档2](链接)

---

## 🔗 参考资料

- OpenTelemetry官方文档
- 相关规范链接

---

**版本**: v1.0  
**最后更新**: YYYY-MM-DD  
**维护者**: 团队名称
```

---

### 3.2 必需章节

**所有技术文档必须包含**:

1. **📋 概述**
   - 文档目的
   - 目标读者
   - 适用范围

2. **🎯 核心内容**
   - 主题详细说明
   - 代码示例（如适用）
   - 配置示例（如适用）

3. **📚 相关文档**
   - 内部文档链接
   - 相关章节引用

4. **🔗 参考资料**
   - OpenTelemetry规范链接
   - 外部权威资源

5. **元数据**（文档顶部和底部）
   - 版本号
   - 更新日期
   - 状态标识
   - 维护者

---

### 3.3 可选章节

**根据文档类型可选**:

- **🚀 快速开始** - 快速入门指南
- **⚙️ 配置说明** - 详细配置选项
- **🔍 故障排查** - 常见问题和解决方案
- **💡 最佳实践** - 推荐用法和技巧
- **⚠️ 注意事项** - 重要警告和限制
- **📈 性能考虑** - 性能优化建议
- **🔒 安全考虑** - 安全配置和建议
- **🔄 变更历史** - 文档修订记录

---

## 四、常见对齐要点

### 4.1 采样策略

**规范要求**:

- ✅ 采样决策在Span创建时确定
- ✅ 父Span采样，子Span必须采样
- ✅ 支持远程采样（Remote Sampling）
- ✅ 采样率可动态调整

**最佳实践**:

```yaml
# 基于概率的采样
sampler:
  type: "parent_based"
  parent:
    type: "trace_id_ratio"
    ratio: 0.1  # 10%采样率

# 基于属性的采样
sampler:
  type: "parent_based"
  parent:
    type: "attribute"
    rules:
      - attribute: "http.status_code"
        values: ["5xx"]
        sample_rate: 1.0  # 错误全部采样
      - attribute: "http.route"
        values: ["/health"]
        sample_rate: 0.01  # 健康检查低采样率
```

**避免**:

- ❌ 默认100%采样（生产环境）
- ❌ 固定不可调整的采样率
- ❌ 没有与SLO/成本联动的采样策略

---

### 4.2 压缩与编码权衡

**决策因素**:

| 因素 | 无压缩 | gzip | snappy |
|------|--------|------|--------|
| CPU开销 | 低 | 高 | 中 |
| 压缩率 | 0% | 70-80% | 50-60% |
| 延迟 | 低 | +5-10ms | +1-3ms |
| 适用场景 | 低延迟要求 | 高带宽成本 | 平衡方案 |

**推荐策略**:

```yaml
# 生产环境推荐
compression: gzip

# 超低延迟场景
compression: none

# 平衡方案
compression: snappy
```

---

### 4.3 重试策略详解

**标准重试逻辑**:

```python
# 伪代码示例
def export_with_retry(data):
    attempt = 0
    max_attempts = 5
    backoff = 100ms  # 初始退避
    
    while attempt < max_attempts:
        try:
            response = send(data)
            if response.status_code == 200:
                return SUCCESS
            elif response.status_code in [429, 503]:
                # 可重试错误
                attempt += 1
                sleep(backoff * (2 ** attempt) * (1 + random(-0.25, 0.25)))
            else:
                # 不可重试错误
                return FAILURE
        except NetworkError:
            attempt += 1
            sleep(backoff * (2 ** attempt))
    
    return FAILURE
```

**关键点**:

- ✅ 区分可重试和不可重试错误
- ✅ 指数退避 + 随机抖动避免惊群
- ✅ 设置最大重试次数和总超时时间
- ✅ 幂等性保证（使用请求ID）
- ✅ 记录重试次数到指标

---

### 4.4 背压与流控

**背压策略优先级**:

1. **保护下游** > 保证数据完整性
2. **有界丢弃** > 无界积压
3. **记录审计** > 静默丢弃

**实现示例**:

```yaml
# 队列配置
queue:
  size: 10000
  overflow_policy: "drop_oldest"  # 丢弃最旧数据
  
# 流控配置
rate_limit:
  enabled: true
  max_rps: 10000
  burst: 5000

# 监控和告警
metrics:
  dropped_spans:
    alert_threshold: 100/minute
```

---

### 4.5 跨信号关联

**Traces与Logs关联**:

```json
{
  "timestamp": "2024-01-15T10:30:00Z",
  "severity": "ERROR",
  "body": "Database connection failed",
  "trace_id": "0123456789abcdef0123456789abcdef",
  "span_id": "0123456789abcdef",
  "attributes": {
    "service.name": "payment-service",
    "error.type": "ConnectionError"
  }
}
```

**Traces与Metrics关联**:

```yaml
# 指标添加trace_id作为exemplar
http_request_duration_seconds{
  method="GET",
  status="200"
} 0.145 # trace_id=abc123
```

---

## 五、质量与可维护性

### 5.1 文档质量检查清单

**内容质量**:

- [ ] 所有术语使用OpenTelemetry官方术语
- [ ] 所有配置示例可直接复制使用
- [ ] 所有代码示例语法正确
- [ ] 没有提及内部实现细节
- [ ] 与OTLP规范保持一致

**结构质量**:

- [ ] 包含必需的元数据（版本、日期、维护者）
- [ ] 章节结构符合模板要求
- [ ] 包含"相关文档"和"参考资料"章节
- [ ] 使用统一的Emoji图标和格式

**链接质量**:

- [ ] 所有内部链接可访问
- [ ] 所有外部链接有效
- [ ] OpenTelemetry规范链接指向最新版本

**可读性**:

- [ ] 目标读者明确
- [ ] 有清晰的阅读路径
- [ ] 代码块有语言标识
- [ ] 表格格式正确

---

### 5.2 文档审核流程

**提交前自检**:

1. 运行拼写检查
2. 检查所有链接
3. 验证代码示例
4. 核对版本号和日期

**Peer Review检查点**:

1. 术语使用是否规范
2. 是否与规范对齐
3. 示例是否可运行
4. 结构是否完整

**维护者最终审核**:

1. 文档定位是否准确
2. 是否与现有文档重复
3. 是否需要更新相关文档

---

### 5.3 文档更新策略

**定期更新**:

- 🔄 每季度检查OpenTelemetry规范更新
- 🔄 每月检查外部链接有效性
- 🔄 每周检查社区反馈

**触发更新**:

- 📢 OpenTelemetry新版本发布
- 📢 重大功能变更
- 📢 用户反馈的错误或不清楚之处

**版本管理**:

- v1.0 → v1.1: 小幅更新（修复、澄清）
- v1.0 → v2.0: 大幅更新（结构调整、新增章节）
- 保留变更历史记录

---

## 六、参考资料

### OpenTelemetry官方资源

**核心规范**:

- [OTLP Specification](https://opentelemetry.io/docs/specs/otlp/)
- [OpenTelemetry API/SDK](https://opentelemetry.io/docs/specs/otel/)
- [Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/)

**Protocol Buffers定义**:

- [opentelemetry-proto](https://github.com/open-telemetry/opentelemetry-proto)

**语义约定详解**:

- [Resource Conventions](https://opentelemetry.io/docs/specs/semconv/resource/)
- [HTTP Conventions](https://opentelemetry.io/docs/specs/semconv/http/)
- [Database Conventions](https://opentelemetry.io/docs/specs/semconv/database/)
- [RPC Conventions](https://opentelemetry.io/docs/specs/semconv/rpc/)
- [Messaging Conventions](https://opentelemetry.io/docs/specs/semconv/messaging/)

### 技术写作指南

**Style Guides**:

- [Google Developer Documentation Style Guide](https://developers.google.com/style)
- [Microsoft Writing Style Guide](https://docs.microsoft.com/en-us/style-guide/)
- [Kubernetes Documentation Style Guide](https://kubernetes.io/docs/contribute/style/style-guide/)

### CNCF和云原生最佳实践

**CNCF资源**:

- [CNCF Technical Oversight Committee](https://github.com/cncf/toc)
- [CNCF Best Practices](https://www.cncf.io/blog/)

**SRE和可观测性**:

- [Google SRE Books](https://sre.google/books/)
- [The Twelve-Factor App](https://12factor.net/)

---

## 七、快速参考

### 7.1 常用术语速查

| 中文 | 英文 | 说明 |
|------|------|------|
| 分布式追踪 | Distributed Tracing | 跨服务调用链追踪 |
| 追踪单元 | Span | 单个操作的时间片段 |
| 追踪上下文 | Trace Context | TraceId + SpanId |
| 采样 | Sampling | 选择性记录追踪数据 |
| 批处理 | Batching | 聚合多条数据一次发送 |
| 背压 | Backpressure | 下游压力反馈到上游 |
| 幂等性 | Idempotency | 重复请求结果一致 |
| 指数退避 | Exponential Backoff | 重试间隔指数增长 |

---

### 7.2 文档模板速查

**快速创建新文档**:

```bash
# 复制模板
cp docs/TEMPLATE.md docs/新文档.md

# 替换占位符
sed -i 's/{{TITLE}}/文档标题/g' docs/新文档.md
sed -i 's/{{DATE}}/2025-10-17/g' docs/新文档.md
```

---

## 八、常见问题（FAQ）

### Q1: 如何处理中英文术语混用？

**A**: 优先使用英文术语，中文括号注释：

- ✅ "Span（追踪单元）"
- ✅ "使用Tracer创建Span"
- ❌ "使用追踪器创建跟踪片段"

---

### Q2: 代码示例应该使用什么语言？

**A**: 按优先级：

1. **配置**: YAML（最通用）
2. **伪代码**: Python-like（易读）
3. **实际代码**: Rust、Go、Java等

---

### Q3: 如何引用外部规范？

**A**: 使用完整链接和版本号：

```markdown
根据[OTLP v1.0规范](https://opentelemetry.io/docs/specs/otlp/)...
```

---

### Q4: 文档多久更新一次？

**A**:

- 错误修复: 立即更新
- 小幅优化: 每月汇总
- 大版本更新: 跟随OpenTelemetry发布

---

## 九、附录

### A. 文档分类标识

使用Emoji快速识别文档类型：

| Emoji | 类型 | 说明 |
|-------|------|------|
| 📋 | 概述 | 总览性内容 |
| 🚀 | 快速开始 | 入门教程 |
| 📖 | 指南 | 详细教程 |
| 🔧 | 配置 | 配置说明 |
| 💡 | 最佳实践 | 推荐用法 |
| 🐛 | 故障排查 | 问题诊断 |
| ⚠️ | 注意事项 | 警告信息 |
| ✅ | 完成 | 已完成项 |
| 🚧 | 进行中 | 开发中 |
| 📚 | 参考 | 参考资料 |

---

### B. 版本控制规范

**版本号格式**: `vX.Y`

- **X (主版本)**: 结构重大变更、新增主要章节
- **Y (次版本)**: 内容更新、错误修复、小幅改进

**示例**:

- v1.0: 初始版本
- v1.1: 修复错误、补充示例
- v1.2: 新增小节、更新链接
- v2.0: 重构结构、大幅扩展

---

**本文档为元文档，指导所有其他文档的撰写与校对；不涉及仓库内部实现细节。**

---

**版本**: v2.0  
**最后更新**: 2025年10月17日  
**状态**: ✅ 完整元文档  
**维护者**: OTLP文档团队

---

**🎉 完整的文档编写规范！确保所有文档与OpenTelemetry规范保持一致！**
