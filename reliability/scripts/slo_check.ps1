Param(
  [string]$SloFile = 'reliability/slo.yaml'
)

$ErrorActionPreference = 'Stop'
if (-not (Test-Path $SloFile)) {
  Write-Host "[slo-check] SLO file not found: $SloFile (skip)"
  exit 0
}

Write-Host "[slo-check] reading $SloFile"
# Minimal parse: just print content; full check can be added with a PS YAML module
Get-Content -Path $SloFile | Write-Host
exit 0


