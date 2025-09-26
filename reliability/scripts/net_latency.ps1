Param(
  [ValidateSet('add','del')][string]$Action = 'add',
  [int]$DelayMs = 1000,
  [int]$DurationSec = 30,
  [string]$Interface = 'Ethernet'
)

$ErrorActionPreference = 'Stop'

function Add-Latency {
  param([int]$Delay, [string]$Iface)
  # Windows: leverage New-NetQosPolicy with DSCP tagging is not equivalent to latency.
  # For demo purposes, we rely on dev tools like clumsy (if available) or skip with message.
  Write-Host "[net-latency] Windows latency simulation requires external tool (e.g., clumsy). Skipping."
}

function Remove-Latency {
  param([string]$Iface)
  Write-Host "[net-latency] restore noop on Windows demo"
}

switch ($Action) {
  'add' {
    Add-Latency -Delay $DelayMs -Iface $Interface
    Start-Sleep -Seconds $DurationSec
    Remove-Latency -Iface $Interface
  }
  'del' { Remove-Latency -Iface $Interface }
}

exit 0


