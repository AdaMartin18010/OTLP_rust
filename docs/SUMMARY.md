# Summary

[简介](README.md)

---

## 快速开始

- [快速开始](guides/getting-started/README.md)
  - [安装指南](guides/getting-started/installation.md)
  - [第一个追踪](guides/getting-started/first-trace.md)
  - [配置说明](guides/getting-started/configuration.md)

---

## 用户指南

- [教程](guides/tutorials/README.md)
  - [基础使用](guides/tutorials/01-basic-usage.md)
  - [高级特性](guides/tutorials/02-advanced-features.md)
  - [微服务集成](guides/tutorials/03-microservices.md)
  - [生产部署](guides/tutorials/04-production-deployment.md)

- [操作指南](guides/howto/README.md)
  - [自定义导出器](guides/howto/custom-exporter.md)
  - [性能调优](guides/howto/performance-tuning.md)
  - [故障排查](guides/howto/troubleshooting.md)

- [最佳实践](guides/best-practices/README.md)
  - [错误处理](guides/best-practices/error-handling.md)
  - [监控策略](guides/best-practices/monitoring.md)
  - [安全加固](guides/best-practices/security.md)

---

## 架构设计

- [架构概览](architecture/overview.md)
- [Crate 设计](architecture/crate-design.md)
- [依赖关系图](architecture/dependency-graph.md)
- [模块组织](architecture/module-organization.md)

---

## API 参考

- [otlp-core](api/otlp-core/README.md)
  - [数据类型](api/otlp-core/types.md)
  - [验证器](api/otlp-core/validation.md)
  - [错误类型](api/otlp-core/error.md)

- [otlp-proto](api/otlp-proto/README.md)
  - [编解码器](api/otlp-proto/codec.md)
  - [类型转换](api/otlp-proto/convert.md)

- [otlp-transport](api/otlp-transport/README.md)
  - [gRPC 传输](api/otlp-transport/grpc.md)
  - [HTTP 传输](api/otlp-transport/http.md)
  - [连接池](api/otlp-transport/connection-pool.md)

- [otlp](api/otlp/README.md)
  - [客户端](api/otlp/client.md)
  - [导出器](api/otlp/exporter.md)
  - [处理器](api/otlp/processor.md)
  - [性能优化](api/otlp/performance.md)
  - [监控集成](api/otlp/monitoring.md)

- [reliability](api/reliability/README.md)
  - [错误处理](api/reliability/error-handling.md)
  - [容错机制](api/reliability/fault-tolerance.md)
  - [运行时监控](api/reliability/runtime-monitoring.md)
  - [运行环境](api/reliability/runtime-environments.md)

- [扩展 Crates](api/integrations/README.md)
  - [otlp-microservices](api/integrations/microservices.md)
  - [otlp-integrations](api/integrations/integrations.md)
  - [otlp-reliability-bridge](api/integrations/reliability-bridge.md)

---

## 设计文档

- [RFC](design/rfcs/README.md)
  - [RFC-0001: 核心重构](design/rfcs/0001-core-refactor.md)
  - [RFC-0002: 可靠性集成](design/rfcs/0002-reliability-integration.md)

- [架构决策记录 (ADR)](design/decisions/README.md)
  - [ADR-0001: Crate 拆分](design/decisions/0001-crate-split.md)
  - [ADR-0002: 异步运行时](design/decisions/0002-async-runtime.md)
  - [ADR-0003: 错误处理](design/decisions/0003-error-handling.md)

- [规范文档](design/specifications/README.md)
  - [OTLP 扩展规范](design/specifications/otlp-extensions.md)
  - [性能要求](design/specifications/performance-requirements.md)

---

## 实现细节

- [语义模型](implementation/semantic-models/README.md)
  - [形式化语义](implementation/semantic-models/formal-semantics.md)
  - [分布式架构](implementation/semantic-models/distributed-architecture.md)
  - [Rust 特定实现](implementation/semantic-models/rust-specific.md)

- [算法实现](implementation/algorithms/README.md)
  - [压缩算法](implementation/algorithms/compression.md)
  - [批处理](implementation/algorithms/batching.md)
  - [负载均衡](implementation/algorithms/load-balancing.md)

- [优化技术](implementation/optimizations/README.md)
  - [SIMD 优化](implementation/optimizations/simd.md)
  - [零拷贝](implementation/optimizations/zero-copy.md)
  - [内存池](implementation/optimizations/memory-pool.md)

---

## 运维文档

- [部署](operations/deployment/README.md)
  - [Kubernetes](operations/deployment/kubernetes.md)
  - [Docker](operations/deployment/docker.md)
  - [裸机部署](operations/deployment/bare-metal.md)

- [监控](operations/monitoring/README.md)
  - [Prometheus](operations/monitoring/prometheus.md)
  - [Grafana](operations/monitoring/grafana.md)
  - [告警配置](operations/monitoring/alerts.md)

- [维护](operations/maintenance/README.md)
  - [升级指南](operations/maintenance/upgrades.md)
  - [备份恢复](operations/maintenance/backup-recovery.md)
  - [容量规划](operations/maintenance/capacity-planning.md)

---

## 报告和分析

- [基准测试](reports/benchmarks/README.md)
- [性能分析](reports/performance/README.md)
- [进度报告](reports/progress/README.md)

---

## 研究探索

- [量子可观测性](research/quantum-observability/README.md)
- [神经形态监控](research/neuromorphic-monitoring/README.md)
- [AI 自动化](research/ai-automation/README.md)

---

## 参考资料

- [术语表](reference/glossary.md)
- [常见问题](reference/faq.md)
- [外部资源](reference/resources.md)

---

## 贡献指南

- [如何贡献](contributing/CONTRIBUTING.md)
- [代码风格](contributing/code-style.md)
- [测试规范](contributing/testing.md)
- [发布流程](contributing/release-process.md)
