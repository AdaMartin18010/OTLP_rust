# 2025 標準與趨勢對標（摘要）

## 🎯 OTLP（協議）

- 協議穩定：1.x 穩定線，Traces/Metrics/Logs/Profiles 一致的傳輸面
- 多目標導出/重試/壓縮/安全（mTLS）實踐增強
- 參考錨點：規範版本/Release Notes/實作兼容矩陣（[otlp-spec](https://opentelemetry.io/docs/specs/otlp/)、[collector-release](https://github.com/open-telemetry/opentelemetry-collector/releases)）

### 1.1 落地要點

- HTTP/gRPC 客戶端與 Collector 版本對齊，開啟壓縮與重試策略
- 多目標導出時的隔離隊列與背壓治理

## 📝 OTTL（Transform）

- 可編程數據面：聲明式規則，函數庫擴展，批量/向量化優化
- 熱更新/沙箱化（WASM/本地擴展）趨勢增強
- 參考錨點：transform processor/規則語法/函數庫清單（[transform-processor](https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/processor/transformprocessor)、[ottl-syntax](https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/pkg/ottl)、[ottl-functions](https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/pkg/ottl/ottlfuncs)）

### 2.1 落地要點

- 規則治理：命名/評審/灰度/回滾/衝突檢測
- 高基數與成本守門：屬性白名單、降維、採樣與聚合

## 💡 OPAMP（控制面）

- 反向通道穩定化：配置/證書/包管理/規則灰度與回滾
- 能力宣告與選擇器（標籤/權重/窗口）精細化
- 參考錨點：規範/Go/Rust 實作/Operator（[opamp-spec](https://github.com/open-telemetry/opamp-spec)、[opamp-go](https://github.com/open-telemetry/opamp-go)、[opamp-rs](https://github.com/open-telemetry/opamp-rs)）

### 3.1 落地要點

- 下發 SLO：P95 延遲、成功率、回滾時間；審批與審計
- 憑證輪換與簽名驗證；配置哈希防重放

## 🔧 Profiles（第四支柱）

- pprof 事實標準 + OTLP Resource/Attributes 封裝
- Collector receiver/exporter 生態完善；與 Trace 聯動分析
- 參考錨點：profiles.proto/collector-contrib/後端（[profiles-proto](https://github.com/open-telemetry/opentelemetry-proto/tree/main/opentelemetry/proto/profiles/v1)、[profilingreceiver](https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/receiver/profilingreceiver)、[parca](https://github.com/parca-dev/parca)、[pyroscope](https://github.com/grafana/pyroscope)、[elastic-up](https://www.elastic.co/guide/en/observability/current/universal-profiling.html)）

### 4.1 落地要點

- 低頻優先（9–49 Hz）→ 帶寬/CPU 成本可控；與告警聯動按需升頻
- 與 Trace 關聯（Resource/屬性一致），面板一鍵跳轉

## 📊 語義約定

- HTTP/DB/MQ 等 Stable；CI/CD、Gen-AI 等領域加速演進
- 目標：跨後端/儀表板“一次定義，處處可用”
- 參考錨點：對應領域的 Semantic Conventions（[http-semconv](https://opentelemetry.io/docs/specs/semconv/http/)、[db-semconv](https://opentelemetry.io/docs/specs/semconv/database/)、[ci-cd-semconv](https://github.com/open-telemetry/semantic-conventions/tree/main/model/ci)、[genai-semconv](https://github.com/open-telemetry/semantic-conventions/tree/main/model/gen-ai)）

### 5.1 落地要點

- 建立本項目語義覆蓋清單與差距表；統一單位/命名/屬性鍵
- 生成可復用的儀表板模板與查詢片段

## 🚀 eBPF 與零代碼

- eBPF 採樣與內核限制並存；零代碼儀表化需權衡安全邊界
- 建議提供降級路徑與合規策略
- 參考錨點：parca-agent、pyroscope/elastic 文檔（[parca-agent](https://github.com/parca-dev/parca-agent)、[pyroscope-ebpf](https://grafana.com/docs/pyroscope/latest/configure-agent/ebpf/)、[elastic-up-docs](https://www.elastic.co/guide/en/observability/current/universal-profiling.html)）

### 6.1 落地要點

- 內核/容器環境基線校驗；最小權限原則；禁用路徑準備
- 降級矩陣：禁用→降頻→後端合併→關閉

## 🔍 落地檢查清單（Checklist）

- 協議：客戶端/Collector/後端版本矩陣、壓縮/重試/多目標導出驗證
- OTTL：規則審核流與灰度策略、生產基準報告與回歸
- OPAMP：證書輪換演練、下發 P95/SUCCESS/回滾 SLA 實測
- Profiles：帶寬/CPU 成本測量、Trace 連通性驗證
- 語義約定：覆蓋清單/差距表、模板化面板
- 安全/合規：脫敏模板、審計與留痕、數據保留策略

## 💻 引用鏈接（匯總）

- [otlp-spec](https://opentelemetry.io/docs/specs/otlp/)
- [collector-release](https://github.com/open-telemetry/opentelemetry-collector/releases)
- [transform-processor](https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/processor/transformprocessor)
- [ottl-syntax](https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/pkg/ottl)
- [ottl-functions](https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/pkg/ottl/ottlfuncs)
- [opamp-spec](https://github.com/open-telemetry/opamp-spec)
- [opamp-go](https://github.com/open-telemetry/opamp-go)
- [opamp-rs](https://github.com/open-telemetry/opamp-rs)
- [profiles-proto](https://github.com/open-telemetry/opentelemetry-proto/tree/main/opentelemetry/proto/profiles/v1)
- [profilingreceiver](https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/receiver/profilingreceiver)
- [parca](https://github.com/parca-dev/parca)
- [pyroscope](https://github.com/grafana/pyroscope)
- [elastic-up](https://www.elastic.co/guide/en/observability/current/universal-profiling.html)
- [http-semconv](https://opentelemetry.io/docs/specs/semconv/http/)
- [db-semconv](https://opentelemetry.io/docs/specs/semconv/database/)
- [ci-cd-semconv](https://github.com/open-telemetry/semantic-conventions/tree/main/model/ci)
- [genai-semconv](https://github.com/open-telemetry/semantic-conventions/tree/main/model/gen-ai)
- [parca-agent](https://github.com/parca-dev/parca-agent)
- [pyroscope-ebpf](https://grafana.com/docs/pyroscope/latest/configure-agent/ebpf/)
- [elastic-up-docs](https://www.elastic.co/guide/en/observability/current/universal-profiling.html)
