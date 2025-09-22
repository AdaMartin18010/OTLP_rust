# 3. 分布式 OTLP 组件组合架构蓝图（2025）

## 3.1 目录

1. 目标与范围
2. 组件清单与职责
3. 参考拓扑与部署形态
4. 数据通道与协议约定
5. 弹性与可靠性设计
6. 安全与合规
7. 运维与监控

## 3.2 目标与范围

- 支持 Traces/Metrics/Logs 全遥测面。
- 兼容 gRPC/HTTP/Protobuf，面向云原生与多环境落地。

## 3.3 组件清单与职责

1. SDK（应用内）
   - 负责埋点、资源语义、采样；将数据推送至本地/远端 Collector。
2. Collector（Agent/Sidecar/Gateway）
   - 接收、限流、过滤、转换、聚合、导出；可选缓冲与队列。
3. 队列（可选：Kafka/NATS）
   - 解耦高峰；提供重放与回压隔离。
4. 后端
   - Tracing：Jaeger/Tempo；Metrics：Prometheus；Logs：Loki/Elastic。
5. 可视化
   - Grafana/Jaeger UI/Kibana。

## 3.4 参考拓扑与部署形态

1. Agent 模式（节点本地）：
   - 应用 → 本机 Collector Agent → 汇聚层 Collector Gateway → 后端。
2. Sidecar 模式（容器）：
   - Pod 内应用 → Sidecar Collector → Gateway → 后端。
3. Gateway 模式（中心）：
   - 应用 SDK 直连 Gateway；适合受控网络与统一策略。

## 3.5 数据通道与协议约定

1. 协议：优先 OTLP/gRPC；跨域或受限网络采用 HTTP/Protobuf。
2. 压缩：Gzip 默认，批量/大对象链路评估 Zstd。
3. 超时与重试：端到端一致；统一幂等语义与错误分类。

## 3.6 弹性与可靠性设计

1. 限流与背压：Collector 接入层优先；应用侧快速失败+重试。
2. 暂存与重放：启用磁盘队列（批量、最大保留时长）。
3. 多 AZ/多副本：Gateway 无状态横向扩展；后端按各自高可用方案部署。

## 3.7 安全与合规

1. 传输安全：mTLS；证书轮转与最小权限。
2. 数据治理：PII 脱敏/掩码；字段白名单；租户隔离。
3. 审计：Collector/导出器操作审计与配置变更留痕。

## 3.8 运维与监控

1. 健康探针：Collector/导出器/队列/后端。
2. SLO：采集延迟、丢失率、导出吞吐、错误率；统一告警门限。
3. 灰度：双写与暗发布；按租户/服务维度逐步放量。
