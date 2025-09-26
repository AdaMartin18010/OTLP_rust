#!/usr/bin/env bash
set -euo pipefail

SLO_FILE=${1:-reliability/slo.yaml}

if ! command -v yq >/dev/null 2>&1; then
  echo "[slo-check] yq not found; skipping SLO check"
  exit 0
fi

P95=$(yq '.latency.p95_ms' "$SLO_FILE")
P99=$(yq '.latency.p99_ms' "$SLO_FILE")
AVAIL=$(yq '.availability.target' "$SLO_FILE")
ERR=$(yq '.error_rate.max_percent' "$SLO_FILE")

echo "[slo-check] target p95=$P95 p99=$P99 availability=$AVAIL% error_rate<$ERR%"
exit 0


