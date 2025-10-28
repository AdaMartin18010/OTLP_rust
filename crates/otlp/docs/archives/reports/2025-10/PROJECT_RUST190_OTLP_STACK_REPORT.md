# OTLP Rust 1.90 对标与成熟栈组合 · 架构方案（2025-09）

本报告面向本仓（workspace edition=2024, rust-version=1.90）在当前生态（Rust 1.89 稳定为主、1.90 预期近发布）下的对标结论、成熟软件栈版本组合与分布式 OTLP 架构建议，并附升级与验证计划。

## 📖 系统与时间

- 操作系统（环境信息）: Windows 10 (Build 26100)
- 当前时间: 2025-09-23T03:22:11.2873870+08:00

## 📝 Rust 1.90 语言/工具链对标

- 本仓声明: edition = 2024, rust-version = 1.90；在 1.89 稳定工具链下可正常构建与运行。
- 与 1.89/edition-2024 对齐要点：
  - 生命周期语法与新 lint 更严格：避免在函数签名混用省略与显式生命周期；公共 API 建议显式化。
  - 常量泛型 `_` 推断增强：谨慎在公共 API 处依赖 `_`，保证可读性与稳定推断。
  - 依赖解析 `resolver = "3"` 与工作区统一版本已启用，利于瘦身与冲突收敛。
- 编译配置（本仓）：Release 使用 `lto=fat`、`codegen-units=1`、`panic=abort`、`strip=symbols`，体积/性能权衡合理；CPU 指令集优化需在构建配置或环境中显式指定 `target-cpu/target-feature`。

## 🔍 成熟软件栈版本组合（Rust 侧）

以下为 2025-09 时点的稳健组合（与本仓已基本一致），适合生产：

- OpenTelemetry（Rust）：
  - opentelemetry = 0.30.x
  - opentelemetry_sdk = 0.30.x（features: rt-tokio）
  - opentelemetry-otlp = 0.30.x（优先 gRPC；HTTP/JSON 备用）
  - opentelemetry-proto = 0.31.x
  - tracing = 0.1.x / tracing-subscriber = 0.3.x / tracing-opentelemetry = 0.31
- 异步/网络：tokio = 1.47.x，hyper = 1.7.x，reqwest = 0.12.x，h2 = 0.5.x
- gRPC/Proto：tonic = 0.14.x，prost = 0.14.x（强制 protobuf = 3.7.2 以规避已知安全问题）
- TLS：rustls = 0.23.x，tokio-rustls = 0.26.x，webpki-roots = 1.x
- 压缩：zstd、gzip（flate2）、可选 brotli

Collector 与后端：

- OpenTelemetry Collector：采用官方稳定通道最新小版本，启用 otlp receiver、batch/memory_limiter/tail_sampling 处理链、otlp/exporter。
- 后端：Tempo（Trace）/ Prometheus（Metrics）/ Loki（Logs）+ Grafana 可视化。

## 🔧 分布式 OTLP 组件与组合架构

推荐分层拓扑：

1) 应用内 SDK：业务服务内集成 opentelemetry + tracing-opentelemetry，启用批处理、压缩、重试。
2) 节点级 Collector（Agent/Sidecar）：就近接收 OTLP gRPC/HTTP 数据，执行限流/缓冲/初步过滤。
3) 区域汇聚 Collector：集中进行 tail-based 采样、路由、脱敏、扇出导出。
4) 后端与可视化：Tempo/Prometheus/Loki → Grafana。

关键策略：

- 采样：SDK 端 Head-based + Collector 端 Tail-based 混合；关键链路全量保真，非关键链路比例采样。
- 安全：端到端 mTLS（rustls），Collector 层 ACL；敏感字段通过 AttributeProcessor 脱敏。
- 配置与运维：集中配置仓库；金丝雀/蓝绿发布；监控导出失败率、队列滞留、出口速率、端到端 P99 时延。

## 📊 Web/生态版本更新结论（2025-09 快速核查）

- Rust 稳定为 1.89.x，1.90 预计近期开源发布；暂以 1.89 构建为基线，待 1.90 GA 后复核新 lint/推断路径。
- OTel Rust 仍以 0.30.x 为主；未见破坏性大版本跃迁公告。Collector 走稳定通道即可。

## 🌟 升级与验证计划（最小惊扰）

目标：在不破坏现有行为的前提下，消化小版本修复/安全更新，并预备 1.90。

步骤：

1) 小步升级试探：对以下关键包仅做小版本更新并记录变更：opentelemetry*、tracing*、tokio*、hyper*、tonic*、prost*、rustls*、h2、reqwest。
2) 兼容性构建矩阵：Windows/Linux，Rust stable 1.89 与（待发布后）1.90；开启 `RUSTFLAGS` 一致化。
3) 基准与回归：运行仓内 benches（批/单请求、序列化、内存占用），对比吞吐与 P99；关注 CPU/内存回退风险。
4) Collector 金丝雀：并行部署新 Collector 池，5% 流量灰度 24–48h，无异常再逐步切换主流量。
5) 回滚预案：若发现导出失败率/滞留/时延指标恶化，立即回退到上一稳定小版本与 Collector 旧池。

## 🔬 立即可执行的落地要点

- SDK 侧：启用 BatchSpanProcessor，`max_export_batch_size` 与 `scheduled_delay_millis` 按流量调优；Transport 开启 zstd/gzip。
- 安全：落地 mTLS（rustls）与证书轮换；敏感字段统一脱敏策略。
- 可观测性自举：对导出链路本身埋点与指标化，纳入告警。

---
维护者备注：若需要将本报告转化为 CI 审计步骤与自动对比报表，可在后续 PR 增加最小增量验证工作流与基准结果归档，但不改变现有发布流程与风险面。
