#!/usr/bin/env bash
set -euo pipefail

BASELINE_DIR="reliability/benches/_baseline"
RESULT_DIR="target/criterion"
THRESHOLD_PCT=${BENCH_THRESHOLD_PCT:-10}

if [[ ! -d "$BASELINE_DIR" ]]; then
  echo "[bench-guard] baseline dir not found: $BASELINE_DIR (skip)"
  exit 0
fi

if [[ ! -d "$RESULT_DIR" ]]; then
  echo "[bench-guard] result dir not found: $RESULT_DIR (skip)"
  exit 0
fi

fail=0

compare_json() {
  local baseline_json=$1
  local result_json=$2
  # Extract mean estimate nanoseconds via jq
  local b_mean=$(jq -r '.mean.point_estimate // .Mean.point_estimate // 0' "$baseline_json")
  local r_mean=$(jq -r '.mean.point_estimate // .Mean.point_estimate // 0' "$result_json")
  if [[ "$b_mean" == "0" || "$r_mean" == "0" ]]; then
    return 0
  fi
  local allowed=$(python - <<PY
b=$b_mean
t=$THRESHOLD_PCT
print(b * (1 + t/100.0))
PY
)
  # If result is worse than allowed upper bound -> fail
  python - <<PY || fail=1
r=$r_mean
allowed=$allowed
import sys
sys.exit(0 if r <= allowed else 1)
PY
}

# Iterate baseline JSONs and try to match current ones by filename
shopt -s globstar nullglob
for baseline_json in $BASELINE_DIR/**/*.json; do
  name=$(basename "$baseline_json")
  # Look for result jsons with same name anywhere under criterion
  mapfile -t matches < <(find "$RESULT_DIR" -name "$name" -type f)
  if [[ ${#matches[@]} -eq 0 ]]; then
    echo "[bench-guard] no result for $name (skip)"
    continue
  fi
  for result_json in "${matches[@]}"; do
    compare_json "$baseline_json" "$result_json" || {
      echo "[bench-guard] regression detected for $name -> $result_json (>${THRESHOLD_PCT}% over baseline)"
    }
  done
done

if [[ $fail -ne 0 ]]; then
  echo "[bench-guard] benchmark regression detected"
  exit 1
fi

echo "[bench-guard] OK"
exit 0


