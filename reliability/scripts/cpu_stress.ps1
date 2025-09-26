Param(
  [int]$DurationSec = 30,
  [int]$Workers = 2
)

$ErrorActionPreference = 'Stop'
Write-Host "[cpu-stress] duration=$DurationSec workers=$Workers"

$jobs = @()
for ($i = 0; $i -lt $Workers; $i++) {
  $jobs += Start-Job -ScriptBlock {
    $sw = [Diagnostics.Stopwatch]::StartNew()
    while ($true) { [Math]::Sqrt(123456.789) | Out-Null }
  }
}

Start-Sleep -Seconds $DurationSec
$jobs | ForEach-Object { Stop-Job $_ -Force; Remove-Job $_ -Force }
Write-Host "[cpu-stress] done"


