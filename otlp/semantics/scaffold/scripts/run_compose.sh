#!/usr/bin/env bash
set -euo pipefail

ACTION="${1:-up}"

case "$ACTION" in
  up)
    docker compose up -d --remove-orphans
    echo "otel-collector is starting..."
    ;;
  down)
    docker compose down -v
    echo "otel-collector is stopped."
    ;;
  *)
    echo "Usage: $0 [up|down]" >&2
    exit 1
    ;;
fi
