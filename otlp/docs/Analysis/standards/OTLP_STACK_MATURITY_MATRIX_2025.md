# 2. OTLP 开源软件堆栈成熟版本矩阵（2025Q3）

## 2.1 目录

1. 范围与方法
2. 核心组件与版本建议
3. 参考组合与兼容性矩阵
4. 生产级配置建议
5. 风险与回滚策略

## 2.2 范围与方法

- 覆盖 Collector、各语言 SDK（含 Rust）、常见后端（Tracing/Logs/Metrics）与可视化层。
- 以稳定分支/发布版本为主，优先 LTS/长期维护渠道。

## 2.3 核心组件与版本建议（示例）

- Collector：`otel/opentelemetry-collector` 稳定最新小版本。
- Rust 端：`tokio 1.x`、`tonic 0.11+`、`prost 0.12+`、压缩库（`flate2`/`zstd`/`brotli`）。
- 后端：
  - Tracing：Jaeger（或 Tempo），
  - Metrics：Prometheus + Grafana，
  - Logs：Elastic Stack 或 Loki。

注：具体小版本以当月官方发布为准，CI 覆盖最新次版本。

## 2.4 参考组合与兼容性矩阵（摘要）

- 组合A（轻量本地）：
  - Collector（单实例）→ Jaeger + Prometheus + Loki
  - 适用：开发/集成环境；优点：易部署；缺点：高可用不足。
- 组合B（生产标准）：
  - Collector（无状态横向扩展）+ 队列（Kafka/NATS 可选）→ Tempo/Jaeger + Prometheus + Loki + Grafana
  - 适用：中高规模；优点：解耦与弹性；缺点：运维复杂度提升。
- 组合C（云原生托管）：
  - Collector Agent/DaemonSet + 托管 APM/TSDB（厂商托管）
  - 适用：上云环境；优点：少维护；缺点：成本与厂商绑定。

## 2.5 生产级配置建议（要点）

1. 批处理：`max_export_batch_size`/`scheduled_delay` 按目标 QPS 调整。
2. 重试：指数退避 + 熔断；对可重试错误分类。
3. 压缩：gRPC 场景优先 Gzip；大批量链路可评估 Zstd。
4. TLS：开启双向校验（内外网分级策略）。
5. 资源语义：统一 `service.name`/`service.version`/`deployment.environment`。
6. 采样：按入口服务集中控制；下游仅转发标记。

## 2.6 风险与回滚策略

1. Collector 插件升级导致导出失败：灰度 + 双写观察；保留上版本镜像回滚。
2. 后端限速或 schema 变更：启用队列与缓冲区，缩短探活与告警 MTTR。
3. SDK 与运行时不兼容：锁定次要版本，分支环境验证后再合入。
