# 云原生与 OTLP

## 概述

本目录聚焦云原生环境中的 OTLP 实践与方法论，涵盖容器化、编排、服务网格、配置与密钥管理、弹性与伸缩、观测与诊断等主题，帮助在 Kubernetes 等平台上构建高可靠、高弹性、易observability 的遥测管道。

## 与 OTLP 规范对齐（Spec ↔ Cloud-Native）

- 端点与协议对齐：Collector 暴露 gRPC/HTTP(Proto/JSON) 端点；工作负载通过环境变量/配置中心统一指向 Collector；遵循 OTLP 内容类型与端口约定。
- 资源语义对齐：在资源属性中附带 k8s.namespace、k8s.pod.name、k8s.node.name、container.name、deployment、service 等语义信息，满足规范化资源建模要求。
- 安全与合规：优先使用 mTLS、命名空间隔离、最小权限（RBAC/PSP 替代方案、PodSecurity/OPA Gatekeeper）以满足传输安全与合规要求。
- 可用性与弹性：遵循 Collector 无状态/可横向扩展原则，采用 HPA/VPA、优先级与抢占、PodDisruptionBudget、反亲和调度确保数据面稳定。
- 可观测与告警：对 Collector 本身暴露健康与指标端点，统一收集并建立 SLO（成功率/延迟/吞吐/丢弃率）。

## 核心主题

1. 容器化和镜像最佳实践（只读根文件系统、非 root、最小镜像、签名与 SBOM）
2. 编排与部署（Deployment/DaemonSet、滚动升级、蓝绿/金丝雀、HPA/VPA）
3. 网络与服务治理（ClusterIP/Headless、ServiceAccount、NetworkPolicy、Service Mesh 集成）
4. 配置与密钥（ConfigMap、Secret、密钥轮换、集中配置与多环境分层）
5. 存储与缓存（临时卷、只读卷、sidecar 缓冲、队列/代理集成）
6. 伸缩与弹性（反压、批量与队列水位、优先级/限流、断路与重试）
7. 观测与诊断（自监控指标、探针、事件与日志、调试集群）

## 推荐阅读路径

1. 先通读“与 OTLP 规范对齐”确保语义一致
2. 根据集群形态选择部署模式：集中式 Collector、Sidecar、DaemonSet、网格内出口
3. 配置安全（mTLS、证书轮换、密钥管理）与资源属性映射
4. 建立 SLO 与扩缩容策略，验证在高峰与故障场景的稳定性

## 术语与参考

- OTLP 规范与数据模型（OpenTelemetry 官方文档）
- Kubernetes 架构与最佳实践（调度、网络、存储、安全）
- 服务网格（Istio/Linkerd）遥测路径与 mTLS 策略
- 云原生供应链安全（签名、SBOM、镜像策略）
