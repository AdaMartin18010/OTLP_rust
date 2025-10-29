# 检查所有Markdown文件的目录结构
param(
    [string]$RootPath = "."
)

Write-Host "=== Markdown TOC Checker ===" -ForegroundColor Cyan
Write-Host ""

# 初始化统计
$stats = @{
    TotalFiles = 0
    WithTOC = 0
    WithoutTOC = 0
    MultipleTOC = 0
    InconsistentFormat = 0
    Files = @{
        WithTOC = @()
        WithoutTOC = @()
        MultipleTOC = @()
        InconsistentFormat = @()
    }
}

# 查找所有markdown文件
$mdFiles = Get-ChildItem -Path $RootPath -Filter "*.md" -Recurse -File | Where-Object {
    $_.FullName -notlike "*\target\*" -and
    $_.FullName -notlike "*\node_modules\*" -and
    $_.FullName -notlike "*\.git\*"
}

$stats.TotalFiles = $mdFiles.Count
Write-Host "Found $($stats.TotalFiles) markdown files" -ForegroundColor Green
Write-Host ""

foreach ($file in $mdFiles) {
    $content = Get-Content $file.FullName -Raw -ErrorAction SilentlyContinue
    if (-not $content) { continue }
    
    # 检查各种目录格式
    $tocPatterns = @(
        '## 目录',
        '## 📊 目录',
        '## Table of Contents',
        '## 📚 Table of Contents',
        '## Contents',
        '## 内容目录'
    )
    
    $tocCount = 0
    $tocFormats = @()
    
    foreach ($pattern in $tocPatterns) {
        $matches = ([regex]::Matches($content, [regex]::Escape($pattern))).Count
        if ($matches -gt 0) {
            $tocCount += $matches
            $tocFormats += $pattern
        }
    }
    
    $relativePath = $file.FullName.Replace((Get-Location).Path, "").TrimStart('\')
    
    if ($tocCount -eq 0) {
        $stats.WithoutTOC++
        $stats.Files.WithoutTOC += $relativePath
    }
    elseif ($tocCount -eq 1) {
        $stats.WithTOC++
        $stats.Files.WithTOC += $relativePath
    }
    else {
        $stats.MultipleTOC++
        $stats.Files.MultipleTOC += $relativePath
    }
    
    # 检查格式不一致（有多种不同格式的目录）
    if ($tocFormats.Count -gt 1) {
        $stats.InconsistentFormat++
        $stats.Files.InconsistentFormat += $relativePath
    }
}

# 输出统计结果
Write-Host "=== Statistics ===" -ForegroundColor Cyan
Write-Host "Total Files: $($stats.TotalFiles)" -ForegroundColor White
Write-Host "Files with TOC: $($stats.WithTOC) ($([math]::Round($stats.WithTOC/$stats.TotalFiles*100, 2))%)" -ForegroundColor Green
Write-Host "Files without TOC: $($stats.WithoutTOC) ($([math]::Round($stats.WithoutTOC/$stats.TotalFiles*100, 2))%)" -ForegroundColor Yellow
Write-Host "Files with multiple TOCs: $($stats.MultipleTOC)" -ForegroundColor Red
Write-Host "Files with inconsistent format: $($stats.InconsistentFormat)" -ForegroundColor Red
Write-Host ""

# 保存详细结果到文件
$reportPath = "markdown_toc_report.txt"
$report = @"
=== Markdown TOC Analysis Report ===
Generated: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")

STATISTICS:
-----------
Total Files: $($stats.TotalFiles)
Files with TOC: $($stats.WithTOC)
Files without TOC: $($stats.WithoutTOC)
Files with multiple TOCs: $($stats.MultipleTOC)
Files with inconsistent format: $($stats.InconsistentFormat)

FILES WITHOUT TOC (First 50):
-----------------------------
$($stats.Files.WithoutTOC | Select-Object -First 50 | ForEach-Object { "- $_" } | Out-String)

FILES WITH MULTIPLE TOCs:
------------------------
$($stats.Files.MultipleTOC | ForEach-Object { "- $_" } | Out-String)

FILES WITH INCONSISTENT FORMAT:
------------------------------
$($stats.Files.InconsistentFormat | ForEach-Object { "- $_" } | Out-String)
"@

$report | Out-File -FilePath $reportPath -Encoding UTF8
Write-Host "Detailed report saved to: $reportPath" -ForegroundColor Cyan

