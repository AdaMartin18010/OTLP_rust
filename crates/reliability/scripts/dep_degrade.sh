#!/usr/bin/env bash
set -euo pipefail

# Simulate dependency degradation by adding random delay to given host:port via tc if available
# Usage: reliability/scripts/dep_degrade.sh <duration_s> [delay_ms]

DURATION=${1:-30}
DELAY=${2:-300}
IFACE=${IFACE:-eth0}

if command -v tc >/dev/null 2>&1; then
  sudo tc qdisc add dev "$IFACE" root netem delay ${DELAY}ms 25ms distribution normal || true
  echo "[dep-degrade] added delay ${DELAY}ms for ${DURATION}s"
  sleep "$DURATION"
  sudo tc qdisc del dev "$IFACE" root netem || true
  echo "[dep-degrade] restored"
else
  echo "[dep-degrade] tc not found; noop"
  sleep "$DURATION"
fi


