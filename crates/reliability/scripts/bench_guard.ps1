Param(
  [int]$ThresholdPct = $(if ($env:BENCH_THRESHOLD_PCT) { [int]$env:BENCH_THRESHOLD_PCT } else { 10 })
)

$ErrorActionPreference = 'Stop'
$BaselineDir = Join-Path $PSScriptRoot '..' 'benches' '_baseline'
$ResultDir = Join-Path (Get-Location) 'target' 'criterion'

if (-not (Test-Path $BaselineDir)) {
  Write-Host "[bench-guard] baseline dir not found: $BaselineDir (skip)"
  exit 0
}
if (-not (Test-Path $ResultDir)) {
  Write-Host "[bench-guard] result dir not found: $ResultDir (skip)"
  exit 0
}

$fail = 0

function Get-MeanFromJson($jsonPath) {
  try {
    $json = Get-Content -Raw -Path $jsonPath | ConvertFrom-Json
    if ($null -ne $json.mean.point_estimate) { return [double]$json.mean.point_estimate }
    if ($null -ne $json.Mean.point_estimate) { return [double]$json.Mean.point_estimate }
  } catch {}
  return 0
}

Get-ChildItem -Recurse -Filter *.json -Path $BaselineDir | ForEach-Object {
  $baselineJson = $_.FullName
  $name = $_.Name
  $matches = Get-ChildItem -Recurse -Filter $name -Path $ResultDir | Select-Object -ExpandProperty FullName
  if (-not $matches) { return }
  foreach ($resultJson in $matches) {
    $b = Get-MeanFromJson $baselineJson
    $r = Get-MeanFromJson $resultJson
    if ($b -eq 0 -or $r -eq 0) { continue }
    $allowed = $b * (1 + $ThresholdPct/100.0)
    if ($r -gt $allowed) {
      Write-Host "[bench-guard] regression detected for $name -> $resultJson (>$ThresholdPct% over baseline)"
      $fail = 1
    }
  }
}

if ($fail -ne 0) {
  Write-Host "[bench-guard] benchmark regression detected"
  exit 1
}

Write-Host "[bench-guard] OK"
exit 0


