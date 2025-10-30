# 查找无实质内容的文件
param(
    [string]$RootPath = ".",
    [int]$MinContentLines = 10,  # 最少实质内容行数
    [switch]$IncludeMarkdown = $true,
    [switch]$IncludeCode = $true
)

Write-Host "=== Empty/Minimal Content Files Finder ===" -ForegroundColor Cyan
Write-Host ""

# 初始化统计
$stats = @{
    EmptyFiles = @()
    MinimalContent = @()
    OnlyTODO = @()
    TotalScanned = 0
}

# 查找所有文件
$extensions = @()
if ($IncludeMarkdown) { $extensions += "*.md" }
if ($IncludeCode) { $extensions += @("*.rs", "*.toml", "*.yaml", "*.yml", "*.json") }

foreach ($ext in $extensions) {
    $files = Get-ChildItem -Path $RootPath -Filter $ext -Recurse -File -ErrorAction SilentlyContinue | Where-Object {
        $_.FullName -notlike "*\target\*" -and
        $_.FullName -notlike "*\node_modules\*" -and
        $_.FullName -notlike "*\.git\*"
    }

    foreach ($file in $files) {
        $stats.TotalScanned++
        $content = Get-Content $file.FullName -Raw -ErrorAction SilentlyContinue

        if (-not $content -or $content.Trim().Length -eq 0) {
            # 完全空文件
            $stats.EmptyFiles += $file.FullName.Replace((Get-Location).Path, "").TrimStart('\')
            continue
        }

        # 计算实质内容行数（排除空行、注释、标题等）
        $lines = $content -split "`n"
        $contentLines = $lines | Where-Object {
            $trimmed = $_.Trim()
            $trimmed.Length -gt 0 -and
            -not $trimmed.StartsWith("#") -and
            -not $trimmed.StartsWith("//") -and
            -not $trimmed.StartsWith("/*") -and
            -not $trimmed.StartsWith("*") -and
            -not $trimmed.StartsWith("<!--") -and
            -not ($trimmed -match "^-+$") -and
            -not ($trimmed -match "^=+$")
        }

        $actualContentLines = $contentLines.Count

        # 检查是否只有TODO/FIXME/待办事项
        $todoPattern = "(?i)(TODO|FIXME|待办|WIP|Coming Soon|To be implemented)"
        $isTodoOnly = $content -match $todoPattern -and $actualContentLines -lt 5

        if ($isTodoOnly) {
            $stats.OnlyTODO += [PSCustomObject]@{
                Path = $file.FullName.Replace((Get-Location).Path, "").TrimStart('\')
                Lines = $lines.Count
                ContentLines = $actualContentLines
            }
        }
        elseif ($actualContentLines -lt $MinContentLines) {
            $stats.MinimalContent += [PSCustomObject]@{
                Path = $file.FullName.Replace((Get-Location).Path, "").TrimStart('\')
                Lines = $lines.Count
                ContentLines = $actualContentLines
            }
        }
    }
}

# 输出结果
Write-Host "=== Scan Results ===" -ForegroundColor Cyan
Write-Host "Total files scanned: $($stats.TotalScanned)" -ForegroundColor White
Write-Host "Empty files: $($stats.EmptyFiles.Count)" -ForegroundColor Yellow
Write-Host "Files with minimal content (< $MinContentLines lines): $($stats.MinimalContent.Count)" -ForegroundColor Yellow
Write-Host "Files with only TODO/placeholders: $($stats.OnlyTODO.Count)" -ForegroundColor Yellow
Write-Host ""

# 保存报告
$reportPath = "empty_files_report.txt"
$report = @"
=== Empty/Minimal Content Files Report ===
Generated: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")

SUMMARY:
--------
Total files scanned: $($stats.TotalScanned)
Empty files: $($stats.EmptyFiles.Count)
Minimal content files: $($stats.MinimalContent.Count)
TODO-only files: $($stats.OnlyTODO.Count)

EMPTY FILES (0 bytes or blank):
------------------------------
$($stats.EmptyFiles | ForEach-Object { "- $_" } | Out-String)

FILES WITH MINIMAL CONTENT (< $MinContentLines content lines):
-------------------------------------------------------------
$($stats.MinimalContent | ForEach-Object { "- $($_.Path) (Total: $($_.Lines) lines, Content: $($_.ContentLines) lines)" } | Out-String)

FILES WITH ONLY TODO/PLACEHOLDERS:
---------------------------------
$($stats.OnlyTODO | ForEach-Object { "- $($_.Path) (Total: $($_.Lines) lines, Content: $($_.ContentLines) lines)" } | Out-String)
"@

$report | Out-File -FilePath $reportPath -Encoding UTF8
Write-Host "Report saved to: $reportPath" -ForegroundColor Green

# 返回统计信息
return $stats

