# 實驗腳手架

- docker-compose：本地一鍵復現 Collector/Generator/Jaeger/Tempo/Prometheus/Grafana
- k8s：部署 Collector/Jaeger/Tempo/tracegen/Prometheus/Grafana
- scripts：一鍵啟停/數據合成與回放

## 本地（docker-compose）

```bash
cd otlp/semantics/scaffold
./scripts/run_compose.sh up   # Windows: ./scripts/run_compose.ps1 up
# Jaeger UI:     http://localhost:16686
# Tempo Query:   http://localhost:3200  (原生 API，可接 Grafana Tempo datasource)
# Prometheus:    http://localhost:9090
# Grafana:       http://localhost:3000  (admin/admin)
```

## 測量與快照

```bash
# 快速查詢
./scripts/prom_query.sh   # Windows: ./scripts/prom_query.ps1

# 生成快照文件（results.json / results.txt）
./scripts/snapshot_results.sh
```

## K8s（base）

```bash
kubectl apply -f k8s/base/jaeger.yaml
kubectl apply -f k8s/base/tempo.yaml
kubectl apply -f k8s/base/otel-collector.yaml
kubectl apply -f k8s/base/tracegen.yaml
kubectl apply -f k8s/base/prometheus.yaml
kubectl apply -f k8s/base/grafana.yaml
# 訪問
kubectl port-forward deploy/jaeger 16686:16686
kubectl port-forward deploy/grafana 3000:3000
# 打開
# Jaeger:  http://localhost:16686
# Grafana: http://localhost:3000  (admin/admin)
```
