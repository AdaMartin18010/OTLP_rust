#!/usr/bin/env bash
set -euo pipefail

# Allocate memory to create pressure
# Usage: reliability/scripts/mem_pressure.sh <mb> <duration_s>

MB=${1:-512}
DURATION=${2:-30}

python - <<PY
import time
mb = int(${MB})
buf = bytearray(mb * 1024 * 1024)
for i in range(0, len(buf), 4096):
    buf[i] = 1
time.sleep(int(${DURATION}))
PY

echo "[mem-pressure] allocated ${MB}MB for ${DURATION}s"


