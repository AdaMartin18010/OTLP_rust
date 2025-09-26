# 證據化與基準計畫（可中斷）

## 1. 工程產物

- docker-compose / k8s 清單、一鍵腳本、Grafana/Tempo/Mimir/Parca 面板 JSON
- 報告：OTTL/Collector 資源曲線、OPAMP 下發與回滾、Profiling 成本

## 2. 基準場景

- 數據合成器：Traces/Metrics/Logs/Profile 混合速率
- OTTL 規則組：脫敏/降維/標記/路由；WASM 熱更新回歸
- 控制面：標籤/權重/窗口灰度 + 失敗回滾演練

## 3. 驗收門檻（示例）

- 100k span/s 與 50k dp/s 穩定；下發 P95 < 5s；回滾 < 30s；帶寬 < 200KB/s/節點

## 4. 里程碑（8 週，可中斷）

- W1-2：標準差距/語義清單/PoC 環境；產物：差距表、環境腳本
- W3-4：OTTL 基準與治理；產物：基準報告、規則審核與灰度流程
- W5：OPAMP 下發/回滾演練；產物：SLO 報告、審計記錄
- W6：Profiling 成本評估；產物：帶寬/CPU 報告與面板
- W7：合規與安全；產物：脫敏模板、密鑰輪換演練記錄
- W8：SRE 化沉澱；產物：Runbook、容量/成本模型

## 5. 中斷/恢復

- 每週打包：版本、參數、面板 JSON、數據快照、報告
- 恢復順序：環境 → 數據 → 規則 → 演練
