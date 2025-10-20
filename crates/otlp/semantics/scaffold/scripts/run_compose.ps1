param(
  [ValidateSet('up','down')]
  [string]$Action = 'up'
)

$ErrorActionPreference = 'Stop'

if ($Action -eq 'up') {
  docker compose up -d --remove-orphans
  Write-Host "otel-collector is starting..."
} else {
  docker compose down -v
  Write-Host "otel-collector is stopped."
}
