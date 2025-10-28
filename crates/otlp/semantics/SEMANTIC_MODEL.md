# OTLP/OTel 全棧語義模型（梳理）

## 🎯 結構總覽

- Resource：生成遙測數據的實體（服務/主機/容器/K8s 等）
- Context：TraceId/SpanId/Link/Baggage/TraceState
- Traces：Span、Event、Attribute、Status、Link、SpanKind
- Metrics：儀表類型（Counter、UpDownCounter、Histogram、Gauge 等）、數據點與聚合
- Logs：時間戳、Severity、Body、Attributes、Trace/Span 關聯
- Profiles（可選）：pprof 結構 + OTLP Resource/Attributes 封裝

## 📝 Resource 語義（核心屬性）

- service.*、deployment.*、k8s.*、cloud.*、host.*、process.*、telemetry.*
- 要求：四支柱共用同一 Resource 標籤，確保跨信號關聯

## 💡 Traces 語義

- 因果鏈：TraceId → SpanId → ParentId；跨進程/跨主機關聯
- 常用屬性：net.*、http.*、db.*、messaging.*、rpc.* 等語義約定

## 🔧 Metrics 語義

- 名稱/單位/描述一致性；事件時間/聚合語義（Sum、Histogram、ExpHistogram）
- 高基數治理與屬性降維策略

## 📊 Logs 語義

- 結構化優先；關聯 Trace/Span；脫敏與等級管理

## 🚀 Profiles 語義（若引入）

- pprof 結構保持兼容；新增 profile.* 屬性（type/period/collision 等）

## 🔍 語義一致性策略

- 命名規範、屬性白名單、單位與維度治理、跨信號關聯驗證

## 💻 參考

- OpenTelemetry Semantic Conventions（HTTP/DB/MQ/CI/CD/Gen-AI 等）
