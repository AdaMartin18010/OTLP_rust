# 最终验证所有Markdown文件的目录格式

$ErrorActionPreference = "Continue"

$projectRoot = Split-Path -Parent $PSScriptRoot
$standardToc = "## 📋 目录"

$script:total = 0
$script:hasToc = 0
$script:noToc = 0
$script:duplicateToc = 0
$script:wrongFormat = 0
$script:correctFormat = 0

function Verify-File {
    param([string]$filePath)

    $script:total++
    $relativePath = $filePath.Replace($projectRoot + "\", "").Replace($projectRoot + "/", "")

    try {
        $lines = [System.IO.File]::ReadAllLines($filePath, [System.Text.Encoding]::UTF8)

        # 查找所有目录位置
        $tocPositions = @()
        for ($i = 0; $i -lt $lines.Length; $i++) {
            if ($lines[$i] -match '^##\s+📋\s+目录\s*$') {
                $tocPositions += $i
            }
            elseif ($lines[$i] -match '^##\s+目录\s*$') {
                # 非标准格式
                $tocPositions += $i
                $script:wrongFormat++
                Write-Host "⚠️  非标准格式: $relativePath (行 $($i+1))" -ForegroundColor Yellow
            }
        }

        if ($tocPositions.Count -eq 0) {
            $script:noToc++
            return
        }

        $script:hasToc++

        # 检查重复
        if ($tocPositions.Count -gt 1) {
            $script:duplicateToc++
            Write-Host "❌ 重复目录: $relativePath (发现 $($tocPositions.Count) 个)" -ForegroundColor Red
            return
        }

        # 检查格式
        $firstToc = $tocPositions[0]
        if ($lines[$firstToc] -match '^##\s+📋\s+目录\s*$') {
            # 检查空行
            if ($firstToc + 1 -lt $lines.Length) {
                if ($lines[$firstToc + 1].Trim() -eq "") {
                    $script:correctFormat++
                }
                else {
                    Write-Host "⚠️  目录后缺少空行: $relativePath (行 $($firstToc+2))" -ForegroundColor Yellow
                }
            }
            else {
                $script:correctFormat++
            }
        }

    }
    catch {
        Write-Host "❌ 错误: $relativePath - $_" -ForegroundColor Red
    }
}

Write-Host "=========================================" -ForegroundColor Green
Write-Host "最终验证所有Markdown文件的目录格式" -ForegroundColor Green
Write-Host "=========================================" -ForegroundColor Green
Write-Host ""

$mdFiles = Get-ChildItem -Path $projectRoot -Filter "*.md" -Recurse -File |
Where-Object {
    $fullPath = $_.FullName
    $fullPath -notmatch "\\target\\" -and
    $fullPath -notmatch "\\.git\\" -and
    $fullPath -notmatch "\\node_modules\\" -and
    $fullPath -notmatch "\\.vscode\\" -and
    $fullPath -notmatch "\\.github\\"
} |
Sort-Object FullName

Write-Host "检查 $($mdFiles.Count) 个文件..." -ForegroundColor Cyan
Write-Host ""

foreach ($file in $mdFiles) {
    Verify-File -filePath $file.FullName
}

Write-Host ""
Write-Host "=========================================" -ForegroundColor Green
Write-Host "验证完成！" -ForegroundColor Green
Write-Host "=========================================" -ForegroundColor Green
Write-Host "总文件数: $script:total" -ForegroundColor Cyan
Write-Host "有目录: $script:hasToc" -ForegroundColor Cyan
Write-Host "无目录: $script:noToc" -ForegroundColor Gray
Write-Host "格式正确: $script:correctFormat" -ForegroundColor Green
Write-Host "非标准格式: $script:wrongFormat" -ForegroundColor Yellow
Write-Host "重复目录: $script:duplicateToc" -ForegroundColor Red
Write-Host ""
