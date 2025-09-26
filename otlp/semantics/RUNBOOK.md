# 運維 Runbook（觀測→定位→回滾→驗證）

## 1. 觀測入口

- Grafana 儀表板：OTel Collector Overview（導出速率/失敗率/CPU/RSS）
- Jaeger UI：服務/操作/延遲分佈
- Prometheus 即時查詢：見 `MEASUREMENT_GUIDE.md`

## 2. 常見告警與處置

- 導出失敗率升高：檢查後端可用性/Collector 重試/網絡
- CPU 過高：降頻/降維/限流；審查 OTTL 規則複雜度
- 高基數：審查屬性鍵；啟用白名單/聚合

## 3. 快速定位流程

- 驗證 Collector → 後端（Jaeger/Prometheus）連通
- 對比 accepted vs exported；查看 exporter 失敗與重試
- 逐步停用/回滾最近的 OTTL/配置變更

## 4. 回滾

- OTTL 規則回滾：使用治理流程中的上一版本 ConfigHash
- 配置/包回滾：按 `OPAMP_ROLLOUT_STRATEGY.md` 執行，觀測門檻觸發自動回滾

## 5. 變更後驗證

- 15 分鐘窗口：失敗率≈0、CPU<門檻、導出速率穩定
- 生成 `results.json` 與報告模板，存檔於變更記錄
