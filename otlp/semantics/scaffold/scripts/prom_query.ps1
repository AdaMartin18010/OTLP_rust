param(
  [string]$Prom = 'http://localhost:9090'
)

$ErrorActionPreference = 'Stop'

$queries = @{
  spans_rate = 'rate(otelcol_exporter_sent_spans[1m])'
  spans_failed = 'rate(otelcol_exporter_send_failed_spans[1m])'
  cpu_rate = 'rate(process_cpu_seconds_total[1m])'
  rss = 'process_resident_memory_bytes'
}

foreach ($k in $queries.Keys) {
  $q = [System.Web.HttpUtility]::UrlEncode($queries[$k])
  $resp = Invoke-RestMethod -Uri "$Prom/api/v1/query?query=$q" -Method Get -ErrorAction Stop
  Write-Host "[#] $k"
  if (!$resp.data.result) {
    Write-Host "(no data)"
  } else {
    foreach ($r in $resp.data.result) {
      $metric = ($r.metric | ConvertTo-Json -Compress)
      $value = $r.value[1]
      Write-Host "$metric -> $value"
    }
  }
  Write-Host
}
