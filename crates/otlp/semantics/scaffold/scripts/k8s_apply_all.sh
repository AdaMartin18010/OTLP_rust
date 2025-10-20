#!/usr/bin/env bash
set -euo pipefail

BASE_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$BASE_DIR"

kubectl apply -f k8s/base/jaeger.yaml
kubectl apply -f k8s/base/tempo.yaml || true
kubectl apply -f k8s/base/otel-collector.yaml
kubectl apply -f k8s/base/tracegen.yaml
kubectl apply -f k8s/base/prometheus.yaml
kubectl apply -f k8s/base/grafana.yaml

echo
echo "All resources applied. Sample port-forward commands:"
echo "  kubectl port-forward deploy/jaeger 16686:16686"
echo "  kubectl port-forward deploy/grafana 3000:3000"
echo "Open Jaeger:  http://localhost:16686"
echo "Open Grafana: http://localhost:3000 (admin/admin)"
