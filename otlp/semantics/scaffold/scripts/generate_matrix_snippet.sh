#!/usr/bin/env bash
set -euo pipefail

IN_JSON=${1:-results.json}
OUT_MD=${OUT_MD:-CURRENT_STATUS_SNIPPET.md}

jq_bin=$(command -v jq || true)
if [[ -z "$jq_bin" ]]; then
  echo "jq is required" >&2
  exit 1
fi

if [[ ! -f "$IN_JSON" ]]; then
  echo "input $IN_JSON not found" >&2
  exit 2
fi

accepted=$(jq -r '.accepted // empty' "$IN_JSON")
exported=$(jq -r '.exported // empty' "$IN_JSON")
failed=$(jq -r '.failed // empty' "$IN_JSON")
cpu=$(jq -r '.cpu // empty' "$IN_JSON")
rss=$(jq -r '.rss // empty' "$IN_JSON")

echo "# 對標矩陣現狀片段（自動生成）" > "$OUT_MD"
echo >> "$OUT_MD"
echo "- 接收速率（spans/s）：$accepted" >> "$OUT_MD"
echo "- 導出速率（spans/s）：$exported" >> "$OUT_MD"
echo "- 失敗速率（spans/s）：$failed" >> "$OUT_MD"
echo "- CPU（核）：$cpu" >> "$OUT_MD"
echo "- RSS（bytes）：$rss" >> "$OUT_MD"
echo >> "$OUT_MD"
echo "可將以上數值填入 \`PROJECT_MAPPING_MATRIX.md\` 的 \"現狀\" 列。" >> "$OUT_MD"

echo "Saved $OUT_MD"
