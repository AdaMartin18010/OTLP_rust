#!/usr/bin/env bash
set -euo pipefail

PROM=${PROM:-http://localhost:9090}
OUT_JSON=${OUT_JSON:-results.json}
OUT_TXT=${OUT_TXT:-results.txt}

jq_bin=$(command -v jq || true)
if [[ -z "$jq_bin" ]]; then
  echo "jq is required" >&2
  exit 1
fi

declare -A QUERIES=(
  [accepted]='rate(otelcol_receiver_accepted_spans[1m])'
  [exported]='rate(otelcol_exporter_sent_spans[1m])'
  [failed]='rate(otelcol_exporter_send_failed_spans[1m])'
  [cpu]='rate(process_cpu_seconds_total[1m])'
  [rss]='process_resident_memory_bytes'
)

rm -f "$OUT_JSON" "$OUT_TXT"

echo '{' > "$OUT_JSON"
first=1
for name in "${!QUERIES[@]}"; do
  q=${QUERIES[$name]}
  resp=$(curl -sG --data-urlencode "query=$q" "$PROM/api/v1/query")
  echo "[#] $name" | tee -a "$OUT_TXT"
  echo "$resp" | jq '.' >> "$OUT_TXT"
  value=$(echo "$resp" | jq -r '.data.result[0].value[1] // empty')
  if [[ -z "$value" ]]; then value="null"; fi
  if [[ $first -eq 0 ]]; then echo ',' >> "$OUT_JSON"; fi
  echo "  \"$name\": $value" >> "$OUT_JSON"
  first=0
  echo >> "$OUT_TXT"

done
echo '}' >> "$OUT_JSON"

echo "Saved $OUT_JSON and $OUT_TXT"
