# 指標測量與填報指南（OTLP 基準）

## 1. 前置

- 本地已啟動 docker-compose：Collector/Jaeger/Prometheus/Grafana/tracegen
- Prometheus 目標：`otel-collector:8889`

## 2. 基本指標（PromQL）

- Span 導出速率（按 exporter 分組）：
  - `rate(otelcol_exporter_sent_spans[1m])`
- 導出失敗速率：
  - `rate(otelcol_exporter_send_failed_spans[1m])`
- Collector CPU（秒/秒 → 近似 CPU 核心占用）：
  - `rate(process_cpu_seconds_total[1m])`
- Collector 常駐內存：
  - `process_resident_memory_bytes`
- OTLP 接收速率（Traces）：
  - `rate(otelcol_receiver_accepted_spans[1m])`

## 3. 建議門檻（可調整）

- OTTL/Collector 單核 CPU < 40%
- 導出 P95 延遲<50ms（需自定延遲指標或以 Jaeger 端觀測）
- 失敗率接近 0；異常升高需排查後端/網絡

## 4. 自動化查詢

- 使用 `scaffold/scripts/prom_query.sh` 或 `prom_query.ps1` 拉取 Prometheus 即時計算結果。

## 5. 對標矩陣填報（PROJECT_MAPPING_MATRIX.md）

- “現狀”列填入：
  - 吞吐（accepted/ exported spans rate）
  - CPU（`rate(process_cpu_seconds_total[1m])`）
  - 內存（`process_resident_memory_bytes`）
  - 失敗率（`rate(otelcol_exporter_send_failed_spans[1m])`）
- 附時間窗口與環境（機型/核心數/速率配置）說明
