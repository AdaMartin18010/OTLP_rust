# 检查目录格式的一致性
param(
    [string]$RootPath = "."
)

Write-Host "=== TOC Format Consistency Checker ===" -ForegroundColor Cyan
Write-Host ""

# 统计不同的目录格式
$formatStats = @{}
$filesByFormat = @{}

# 查找所有markdown文件
$mdFiles = Get-ChildItem -Path $RootPath -Filter "*.md" -Recurse -File | Where-Object {
    $_.FullName -notlike "*\target\*" -and
    $_.FullName -notlike "*\node_modules\*" -and
    $_.FullName -notlike "*\.git\*"
}

foreach ($file in $mdFiles) {
    $content = Get-Content $file.FullName -Raw -ErrorAction SilentlyContinue
    if (-not $content) { continue }
    
    # 移除代码块中的内容（简单处理）
    $contentWithoutCodeBlocks = $content -replace '(?s)```.*?```', ''
    
    # 检查各种目录格式
    $tocPatterns = @{
        '## 目录' = '## 目录'
        '## 📊 目录' = '## 📊 目录'
        '## 📋 目录' = '## 📋 目录'
        '## Table of Contents' = '## Table of Contents'
        '## 📚 Table of Contents' = '## 📚 Table of Contents'
        '## Contents' = '## Contents'
        '## 内容目录' = '## 内容目录'
    }
    
    foreach ($format in $tocPatterns.Keys) {
        $pattern = [regex]::Escape($tocPatterns[$format])
        if ($contentWithoutCodeBlocks -match "(?m)^$pattern\s*$") {
            $relativePath = $file.FullName.Replace((Get-Location).Path, "").TrimStart('\')
            
            if (-not $formatStats.ContainsKey($format)) {
                $formatStats[$format] = 0
                $filesByFormat[$format] = @()
            }
            $formatStats[$format]++
            $filesByFormat[$format] += $relativePath
            break  # 只统计第一个匹配的格式
        }
    }
}

# 输出统计结果
Write-Host "=== TOC Format Statistics ===" -ForegroundColor Cyan
Write-Host ""

$sortedFormats = $formatStats.GetEnumerator() | Sort-Object -Property Value -Descending

foreach ($entry in $sortedFormats) {
    $percentage = [math]::Round($entry.Value / ($formatStats.Values | Measure-Object -Sum).Sum * 100, 2)
    Write-Host "$($entry.Key): $($entry.Value) files ($percentage%)" -ForegroundColor Green
}

Write-Host ""
Write-Host "=== Recommendation ===" -ForegroundColor Cyan

$mostCommon = $sortedFormats[0]
Write-Host "Most common format: '$($mostCommon.Key)' ($($mostCommon.Value) files)" -ForegroundColor Yellow
Write-Host "Consider standardizing all TOCs to this format." -ForegroundColor Yellow
Write-Host ""

# 保存详细结果
$reportPath = "toc_format_report.txt"
$report = @"
=== TOC Format Analysis Report ===
Generated: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")

FORMAT STATISTICS:
-----------------
$($sortedFormats | ForEach-Object { "$($_.Key): $($_.Value) files" } | Out-String)

RECOMMENDATION:
--------------
Most common format: '$($mostCommon.Key)' with $($mostCommon.Value) files
Consider standardizing all TOCs to this format.

FILES BY FORMAT:
---------------
$($filesByFormat.GetEnumerator() | ForEach-Object {
    "`n[$($_.Key)]`n" + ($_.Value | ForEach-Object { "  - $_" } | Out-String)
} | Out-String)
"@

$report | Out-File -FilePath $reportPath -Encoding UTF8
Write-Host "Detailed report saved to: $reportPath" -ForegroundColor Cyan

