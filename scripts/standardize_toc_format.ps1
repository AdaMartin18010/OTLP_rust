# 统一所有Markdown文件的目录格式为 "## 📋 目录"
param(
    [string]$RootPath = ".",
    [switch]$DryRun = $false
)

Write-Host "=== TOC Format Standardization ===" -ForegroundColor Cyan
Write-Host ""

if ($DryRun) {
    Write-Host "DRY RUN MODE - No files will be modified" -ForegroundColor Yellow
    Write-Host ""
}

$standardFormat = "## 📋 目录"
$changedFiles = 0
$errorFiles = 0

# 要替换的格式
$formatsToReplace = @{
    '## 📊 目录' = $standardFormat
    '## 目录' = $standardFormat
    '## Contents' = $standardFormat
    '## Table of Contents' = $standardFormat
    '## 📚 Table of Contents' = $standardFormat
    '## 内容目录' = $standardFormat
}

# 查找所有markdown文件
$mdFiles = Get-ChildItem -Path $RootPath -Filter "*.md" -Recurse -File | Where-Object {
    $_.FullName -notlike "*\target\*" -and
    $_.FullName -notlike "*\node_modules\*" -and
    $_.FullName -notlike "*\.git\*" -and
    $_.FullName -notlike "*\scripts\*"
}

Write-Host "Processing $($mdFiles.Count) markdown files..." -ForegroundColor Green
Write-Host ""

foreach ($file in $mdFiles) {
    try {
        $content = Get-Content $file.FullName -Raw -Encoding UTF8 -ErrorAction Stop
        if (-not $content) { continue }
        
        $modified = $false
        $newContent = $content
        
        # 对每个格式进行替换
        foreach ($oldFormat in $formatsToReplace.Keys) {
            $newFormat = $formatsToReplace[$oldFormat]
            
            # 只替换不在代码块中的标题
            # 使用正则表达式匹配行首的标题
            $pattern = "(?m)^" + [regex]::Escape($oldFormat) + "\s*$"
            
            if ($newContent -match $pattern) {
                $newContent = $newContent -replace $pattern, $newFormat
                $modified = $true
                
                $relativePath = $file.FullName.Replace((Get-Location).Path, "").TrimStart('\')
                Write-Host "  [CHANGED] $relativePath" -ForegroundColor Yellow
                Write-Host "    $oldFormat -> $newFormat" -ForegroundColor Gray
            }
        }
        
        if ($modified) {
            if (-not $DryRun) {
                $newContent | Out-File -FilePath $file.FullName -Encoding UTF8 -NoNewline
            }
            $changedFiles++
        }
    }
    catch {
        $errorFiles++
        Write-Host "  [ERROR] $($file.Name): $_" -ForegroundColor Red
    }
}

Write-Host ""
Write-Host "=== Summary ===" -ForegroundColor Cyan
Write-Host "Files processed: $($mdFiles.Count)" -ForegroundColor White
Write-Host "Files changed: $changedFiles" -ForegroundColor Green
Write-Host "Errors: $errorFiles" -ForegroundColor $(if ($errorFiles -gt 0) { "Red" } else { "Green" })

if ($DryRun) {
    Write-Host ""
    Write-Host "This was a DRY RUN. No files were actually modified." -ForegroundColor Yellow
    Write-Host "Run without -DryRun flag to apply changes." -ForegroundColor Yellow
}

