# Profiling 集成（PoC 路線）

## 1. 後端選擇

- Pyroscope（本地 compose 已提供）
- Parca/Elastic（可選）

## 2. 集成路線

- pprof push：應用以 pprof 方式向 Pyroscope 推送（語言 Agent）
- eBPF 採樣：以 eBPF agent 在節點側采樣（需內核權限）
- OTLP-Profile：若採用 OTel profiles receiver/exporter，與 Trace/Metric/Log 共用 Resource 標籤

## 3. PoC 步驟（建議）

1) 先以 pprof push 集成單一進程，驗證 UI 與指標
2) 低頻（9–49Hz）→ 按需升頻；測量帶寬/CPU 開銷
3) 與 Trace 聯動：在相同 Resource 下建立關聯，儀表板一鍵跳轉

## 4. 風險與邊界

- eBPF 需內核基線與最小權限；雲環境可能受限
- 高頻採樣帶來 CPU/帶寬成本，需在 `EVIDENCE_PLAN.md` 中驗證

## 5. 下一步

- 添加最小 pprof push 客戶端示例
- 可選：K8s 節點部署 eBPF agent 與指標報表
