Param(
  [int]$DurationSec = 30,
  [int]$DelayMs = 300
)

$ErrorActionPreference = 'Stop'
Write-Host "[dep-degrade] Windows demo (requires external tooling for network shaping)."
Start-Sleep -Seconds $DurationSec
Write-Host "[dep-degrade] done"


