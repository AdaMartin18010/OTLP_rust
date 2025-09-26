# 基準測量結果模板（填報用）

## 1. 環境

- 機型/CPU/內存：
- 操作系統/內核：
- Docker/Compose 版本：

## 2. 配置

- tracegen：`--rate=`、`--traces=` 等
- Collector：關鍵導出/規則/壓縮/重試
- 後端：Jaeger/Prometheus/Grafana 版本

## 3. 指標（15 分鐘窗口）

- OTLP 接收速率：`rate(otelcol_receiver_accepted_spans[1m])` =
- 導出速率：`rate(otelcol_exporter_sent_spans[1m])` =
- 導出失敗率：`rate(otelcol_exporter_send_failed_spans[1m])` =
- CPU（核）：`rate(process_cpu_seconds_total[1m])` =
- RSS（bytes）：`process_resident_memory_bytes` =

## 4. 圖表截圖（可選）

- Grafana 面板：CPU/RSS/導出速率

## 5. 結論

- 是否達到門檻：
- 風險與優化點：
- 待辦：
