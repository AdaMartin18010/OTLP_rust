# 告警與儀表板基線（初稿）

## 1. 告警規則（PromQL 示例）

- Exporter 失敗率 > 0（連續 5m）：
  - `rate(otelcol_exporter_send_failed_spans[5m]) > 0`
- CPU（Collector）> 0.7 核（連續 5m）：
  - `rate(process_cpu_seconds_total[5m]) > 0.7`
- RSS > 1.5GB（連續 10m）：
  - `process_resident_memory_bytes > 1.5e9`

## 2. 儀表板必備面板

- 導出/接收速率（spans/s）
- 失敗速率（spans/s）
- CPU（核）/RSS（bytes）
- 後端錯誤率（可選：以 exporter/後端面板顯示）

## 3. 門檻與行動

- 觸發後先驗證後端可用性與 Collector 重試；再審查 OTTL 規則與速率
- 門檻需按硬件與負載調整，建議隨基準報告定期修訂
