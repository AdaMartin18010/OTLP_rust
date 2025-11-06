# 全面修复所有Markdown文件的目录格式问题
# 1. 删除重复目录
# 2. 统一目录标题格式
# 3. 修复目录列表格式（编号改为标准格式）
# 4. 确保目录后有空行

$ErrorActionPreference = "Continue"

$projectRoot = Split-Path -Parent $PSScriptRoot
$standardToc = "## 📋 目录"

$script:total = 0
$script:processed = 0
$script:noToc = 0
$script:duplicateRemoved = 0
$script:titleFixed = 0
$script:listFormatFixed = 0
$script:spacingFixed = 0
$script:errors = 0

function Process-File {
    param([string]$filePath)

    $script:total++
    $relativePath = $filePath.Replace($projectRoot + "\", "").Replace($projectRoot + "/", "")

    try {
        $content = [System.IO.File]::ReadAllText($filePath, [System.Text.Encoding]::UTF8)
        $lines = $content -split "`r?`n"
        $modified = $false

        # 查找所有目录位置
        $tocPositions = @()
        for ($i = 0; $i -lt $lines.Length; $i++) {
            if ($lines[$i] -match '^##\s+📋\s+目录\s*$|^##\s+目录\s*$') {
                $tocPositions += $i
            }
        }

        if ($tocPositions.Count -eq 0) {
            $script:noToc++
            return
        }

        $script:processed++

        # 删除重复目录
        if ($tocPositions.Count -gt 1) {
            Write-Host "🔧 删除重复目录: $relativePath ($($tocPositions.Count) 个)" -ForegroundColor Yellow
            $script:duplicateRemoved++

            $keepFirst = $tocPositions[0]
            $newLines = @()
            $skipRanges = @()

            for ($idx = 1; $idx -lt $tocPositions.Count; $idx++) {
                $start = $tocPositions[$idx]
                $end = $lines.Length
                for ($j = $start + 1; $j -lt $lines.Length; $j++) {
                    if ($lines[$j] -match '^##\s+') {
                        $end = $j
                        break
                    }
                }
                $skipRanges += @{Start = $start; End = $end }
            }

            for ($i = 0; $i -lt $lines.Length; $i++) {
                $shouldSkip = $false
                foreach ($range in $skipRanges) {
                    if ($i -ge $range.Start -and $i -lt $range.End) {
                        $shouldSkip = $true
                        break
                    }
                }
                if (-not $shouldSkip) {
                    $newLines += $lines[$i]
                }
            }

            $lines = $newLines
            $modified = $true

            # 重新查找目录位置
            $tocPositions = @()
            for ($i = 0; $i -lt $lines.Length; $i++) {
                if ($lines[$i] -match '^##\s+📋\s+目录\s*$|^##\s+目录\s*$') {
                    $tocPositions += $i
                }
            }
        }

        if ($tocPositions.Count -gt 0) {
            $firstToc = $tocPositions[0]

            # 修复标题格式
            if ($lines[$firstToc] -notmatch '^##\s+📋\s+目录\s*$') {
                Write-Host "🔧 修复标题格式: $relativePath" -ForegroundColor Cyan
                $lines[$firstToc] = $standardToc
                $script:titleFixed++
                $modified = $true
            }

            # 确保空行
            if ($firstToc + 1 -lt $lines.Length) {
                if ($lines[$firstToc + 1].Trim() -ne "") {
                    Write-Host "🔧 添加空行: $relativePath" -ForegroundColor Cyan
                    $newLines = @()
                    for ($i = 0; $i -le $firstToc; $i++) {
                        $newLines += $lines[$i]
                    }
                    $newLines += ""
                    for ($i = $firstToc + 1; $i -lt $lines.Length; $i++) {
                        $newLines += $lines[$i]
                    }
                    $lines = $newLines
                    $script:spacingFixed++
                    $modified = $true
                }
            }
            else {
                $lines += ""
                $script:spacingFixed++
                $modified = $true
            }

            # 修复目录列表格式（编号改为标准格式）
            $tocEnd = $lines.Length
            for ($j = $firstToc + 1; $j -lt $lines.Length; $j++) {
                if ($lines[$j] -match '^##\s+') {
                    $tocEnd = $j
                    break
                }
            }

            $hasNumberedList = $false
            for ($j = $firstToc + 2; $j -lt $tocEnd; $j++) {
                if ($lines[$j] -match '^\s*\d+\.\s+\[') {
                    $hasNumberedList = $true
                    break
                }
            }

            if ($hasNumberedList) {
                Write-Host "🔧 修复列表格式: $relativePath" -ForegroundColor Magenta
                for ($j = $firstToc + 2; $j -lt $tocEnd; $j++) {
                    if ($lines[$j] -match '^(\s*)\d+\.\s+\[(.+)\]\((.+)\)') {
                        $indent = $matches[1]
                        $text = $matches[2]
                        $link = $matches[3]
                        $lines[$j] = "$indent- [$text]($link)"
                        $script:listFormatFixed++
                        $modified = $true
                    }
                }
            }
        }

        # 保存修改
        if ($modified) {
            $content = ($lines -join "`r`n") + "`r`n"
            [System.IO.File]::WriteAllText($filePath, $content, [System.Text.Encoding]::UTF8)
        }

    }
    catch {
        Write-Host "❌ 错误: $relativePath - $_" -ForegroundColor Red
        $script:errors++
    }
}

Write-Host "=========================================" -ForegroundColor Green
Write-Host "全面修复所有Markdown文件的目录格式" -ForegroundColor Green
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

Write-Host "处理 $($mdFiles.Count) 个文件..." -ForegroundColor Cyan
Write-Host ""

$progress = 0
foreach ($file in $mdFiles) {
    $progress++
    if ($progress % 100 -eq 0) {
        Write-Host "进度: $progress / $($mdFiles.Count)" -ForegroundColor Gray
    }
    Process-File -filePath $file.FullName
}

Write-Host ""
Write-Host "=========================================" -ForegroundColor Green
Write-Host "处理完成！" -ForegroundColor Green
Write-Host "=========================================" -ForegroundColor Green
Write-Host "总文件数: $script:total" -ForegroundColor Cyan
Write-Host "有目录文件: $script:processed" -ForegroundColor Cyan
Write-Host "无目录文件: $script:noToc" -ForegroundColor Gray
Write-Host "删除重复目录: $script:duplicateRemoved" -ForegroundColor Yellow
Write-Host "修复标题格式: $script:titleFixed" -ForegroundColor Yellow
Write-Host "修复列表格式: $script:listFormatFixed" -ForegroundColor Magenta
Write-Host "修复空行: $script:spacingFixed" -ForegroundColor Cyan
if ($script:errors -gt 0) {
    Write-Host "错误: $script:errors" -ForegroundColor Red
}
Write-Host ""
