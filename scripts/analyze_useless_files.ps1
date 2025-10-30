# 分析无用文件和目录
param(
    [string]$RootPath = "."
)

Write-Host "=== Useless Files Analysis ===" -ForegroundColor Cyan
Write-Host ""

$toDelete = @{
    EmptyReadmes = @()      # 只有标题的README
    PlaceholderCode = @()   # 占位符代码
    DuplicateFiles = @()    # 重复文件
    EmptyDirs = @()         # 空目录
}

# 1. 查找只有标题的README
Write-Host "Scanning for minimal READMEs..." -ForegroundColor Yellow
$readmes = Get-ChildItem -Path $RootPath -Filter "README.md" -Recurse -File -ErrorAction SilentlyContinue | Where-Object {
    $_.FullName -notlike "*\target\*" -and
    $_.FullName -notlike "*\node_modules\*" -and
    $_.FullName -notlike "*\.git\*"
}

foreach ($readme in $readmes) {
    $content = Get-Content $readme.FullName -Raw -ErrorAction SilentlyContinue
    if ($content) {
        $lines = ($content -split "`n") | Where-Object { $_.Trim().Length -gt 0 }

        # 检查是否只有1-2行内容
        if ($lines.Count -le 2) {
            $toDelete.EmptyReadmes += [PSCustomObject]@{
                Path = $readme.FullName.Replace((Get-Location).Path, "").TrimStart('\')
                Lines = $lines.Count
                Content = $content.Trim()
            }
        }
        # 检查是否只有一个标题和简单描述
        elseif ($lines.Count -le 5 -and $content -match "^#\s+.+$" -and $content.Length -lt 100) {
            $toDelete.EmptyReadmes += [PSCustomObject]@{
                Path = $readme.FullName.Replace((Get-Location).Path, "").TrimStart('\')
                Lines = $lines.Count
                Content = $content.Trim()
            }
        }
    }
}

# 2. 查找空目录
Write-Host "Scanning for empty directories..." -ForegroundColor Yellow
$allDirs = Get-ChildItem -Path $RootPath -Directory -Recurse -ErrorAction SilentlyContinue | Where-Object {
    $_.FullName -notlike "*\target\*" -and
    $_.FullName -notlike "*\node_modules\*" -and
    $_.FullName -notlike "*\.git\*"
}

foreach ($dir in $allDirs) {
    $items = Get-ChildItem -Path $dir.FullName -ErrorAction SilentlyContinue
    if ($items.Count -eq 0) {
        $toDelete.EmptyDirs += $dir.FullName.Replace((Get-Location).Path, "").TrimStart('\')
    }
}

# 生成报告
Write-Host ""
Write-Host "=== Analysis Results ===" -ForegroundColor Cyan
Write-Host "Minimal/Empty READMEs: $($toDelete.EmptyReadmes.Count)" -ForegroundColor Yellow
Write-Host "Empty Directories: $($toDelete.EmptyDirs.Count)" -ForegroundColor Yellow
Write-Host ""

# 保存详细报告
$reportPath = "useless_files_report.txt"
$report = @"
=== Useless Files Analysis Report ===
Generated: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")

SUMMARY:
--------
Minimal/Empty READMEs: $($toDelete.EmptyReadmes.Count)
Empty Directories: $($toDelete.EmptyDirs.Count)

MINIMAL/EMPTY READMEs:
---------------------
$($toDelete.EmptyReadmes | ForEach-Object {
    "File: $($_.Path)`nLines: $($_.Lines)`nContent: $($_.Content)`n---"
} | Out-String)

EMPTY DIRECTORIES:
-----------------
$($toDelete.EmptyDirs | ForEach-Object { "- $_" } | Out-String)

RECOMMENDED ACTIONS:
-------------------
1. Review the minimal READMEs and either delete or enhance them
2. Delete empty directories
3. Check for placeholder code files that can be removed

"@

$report | Out-File -FilePath $reportPath -Encoding UTF8
Write-Host "Report saved to: $reportPath" -ForegroundColor Green

return $toDelete

