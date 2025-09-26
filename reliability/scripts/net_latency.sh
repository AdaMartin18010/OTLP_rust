#!/usr/bin/env bash
set -euo pipefail

# Simulate network latency using tc/netem (Linux only)
# Usage: sudo reliability/scripts/net_latency.sh add 1000 30  # 1000ms for 30s

ACTION=${1:-help}
DELAY_MS=${2:-1000}
DURATION_S=${3:-30}
IFACE=${IFACE:-eth0}

case "$ACTION" in
  add)
    sudo tc qdisc add dev "$IFACE" root netem delay ${DELAY_MS}ms || true
    echo "[net-latency] added ${DELAY_MS}ms on $IFACE for ${DURATION_S}s"
    sleep "$DURATION_S"
    sudo tc qdisc del dev "$IFACE" root netem || true
    echo "[net-latency] restored"
    ;;
  del)
    sudo tc qdisc del dev "$IFACE" root netem || true
    echo "[net-latency] restored"
    ;;
  *)
    echo "Usage: $0 add <delay_ms> <duration_s> | del"
    exit 1
    ;;
esac


