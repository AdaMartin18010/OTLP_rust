Param(
  [int]$MB = 512,
  [int]$DurationSec = 30
)

$ErrorActionPreference = 'Stop'
Write-Host "[mem-pressure] allocating ${MB}MB for ${DurationSec}s"

$bytes = New-Object byte[] ($MB * 1MB)
for ($i = 0; $i -lt $bytes.Length; $i += 4096) { $bytes[$i] = 1 }
Start-Sleep -Seconds $DurationSec
Write-Host "[mem-pressure] done"


