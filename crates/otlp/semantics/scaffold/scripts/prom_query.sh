#!/usr/bin/env bash
set -euo pipefail

PROM=${PROM:-http://localhost:9090}

declare -A QUERIES=(
  [spans_rate]='rate(otelcol_exporter_sent_spans[1m])'
  [spans_failed]='rate(otelcol_exporter_send_failed_spans[1m])'
  [cpu_rate]='rate(process_cpu_seconds_total[1m])'
  [rss]='process_resident_memory_bytes'
)

for name in "${!QUERIES[@]}"; do
  q=${QUERIES[$name]}
  val=$(curl -sG --data-urlencode "query=$q" "$PROM/api/v1/query" | jq -r '.data.result[]? | "\(.metric) -> \(.value[1])"')
  echo "[#] $name"
  if [[ -z "$val" ]]; then
    echo "(no data)"
  else
    echo "$val"
  fi
  echo
done
