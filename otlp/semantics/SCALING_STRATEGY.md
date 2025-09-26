# 伸縮策略與自定義指標接入（初稿）

## 1. 目標

- 在可觀測門檻下自動擴縮；避免抖動；兼顧成本

## 2. 指標來源

- Prometheus（Collector 暴露 8889）
- 典型指標：
  - `rate(otelcol_receiver_accepted_spans[1m])`（吞吐代理）
  - `rate(process_cpu_seconds_total[1m])`（CPU 核）
  - `process_resident_memory_bytes`（RSS）
  - 失敗率：`rate(otelcol_exporter_send_failed_spans[1m])`

## 3. 策略示例

- CPU 驅動：目標值 0.5–0.7 核/Pod
- 吞吐驅動：以接收速率/Pod 為目標，計算期望副本數
- 混合：CPU 為主，吞吐為次，設置上下限與冷卻時間

## 4. HPA 與自定義指標

- HPA v2 以 `metrics.k8s.io` 或 adaptor（如 Prometheus Adapter）暴露的指標驅動
- 建議：使用 Prometheus Adapter 暴露自定義指標（吞吐/失敗率）

## 5. 反抖動設置

- 冷卻時間（scale up/down stabilization window）
- 最小/最大副本數、步進與背壓策略

## 6. 驗證

- 壓測下觀測縮放曲線與 SLO，並以 `results.json` 歸檔
