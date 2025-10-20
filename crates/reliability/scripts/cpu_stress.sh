#!/usr/bin/env bash
set -euo pipefail

# Burn CPU using yes or python tight loop
# Usage: reliability/scripts/cpu_stress.sh <duration_s> [workers]

DURATION=${1:-30}
WORKERS=${2:-$(nproc || echo 2)}

cleanup() {
  trap - INT TERM EXIT
}
trap cleanup INT TERM EXIT

echo "[cpu-stress] duration=${DURATION}s workers=${WORKERS}"

pids=()
for _ in $(seq 1 "$WORKERS"); do
  (python - <<'PY'
import time
import threading

def busy():
    while True:
        pass

for _ in range(1):
    t = threading.Thread(target=busy)
    t.daemon = True
    t.start()

time.sleep(10**9)
PY
) & p=$!; pids+=("$p"); done

sleep "$DURATION" || true
for p in "${pids[@]}"; do kill "$p" >/dev/null 2>&1 || true; done
echo "[cpu-stress] done"


