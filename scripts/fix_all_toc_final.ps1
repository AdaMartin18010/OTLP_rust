# 统一所有Markdown文件的目录格式 - 最终版本
# 确保每个文件只有一个目录，格式统一

$ErrorActionPreference = "Continue"

$projectRoot = Split-Path -Parent $PSScriptRoot
$standardToc = "## 📋 目录"

# 统计
$script:total = 0
$script:processed = 0
$script:noToc = 0
$script:duplicateRemoved = 0
$script:formatFixed = 0
$script:errors = 0

function Process-File {
    param([string]$filePath)

    $script:total++
    $relativePath = $filePath.Replace($projectRoot + "\", "").Replace($projectRoot + "/", "")

    try {
        # 读取文件
        $lines = [System.IO.File]::ReadAllLines($filePath, [System.Text.Encoding]::UTF8)
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

        # 删除重复目录（只保留第一个）
        if ($tocPositions.Count -gt 1) {
            Write-Host "🔧 删除重复目录: $relativePath (发现 $($tocPositions.Count) 个)" -ForegroundColor Yellow
            $script:duplicateRemoved++

            # 从后往前删除
            $rangesToRemove = @()
            for ($idx = $tocPositions.Count - 1; $idx -gt 0; $idx--) {
                $startLine = $tocPositions[$idx]

                # 找到结束位置
                $endLine = $lines.Length
                for ($j = $startLine + 1; $j -lt $lines.Length; $j++) {
                    if ($lines[$j] -match '^##\s+') {
                        $endLine = $j
                        break
                    }
                }

                $rangesToRemove += @{Start = $startLine; End = $endLine }
            }

            # 删除范围（从后往前）
            $newLines = @()
            $skipRanges = $rangesToRemove | Sort-Object -Property Start -Descending

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

            # 重新查找第一个目录位置
            $tocPositions = @()
            for ($i = 0; $i -lt $lines.Length; $i++) {
                if ($lines[$i] -match '^##\s+📋\s+目录\s*$|^##\s+目录\s*$') {
                    $tocPositions += $i
                }
            }
        }

        # 统一格式
        if ($tocPositions.Count -gt 0) {
            $firstToc = $tocPositions[0]
            $needsFix = $false

            # 检查标题格式
            if ($lines[$firstToc] -notmatch '^##\s+📋\s+目录\s*$') {
                $needsFix = $true
            }

            # 检查空行
            if ($firstToc + 1 -lt $lines.Length) {
                if ($lines[$firstToc + 1].Trim() -ne "") {
                    $needsFix = $true
                }
            }
            else {
                $needsFix = $true
            }

            if ($needsFix) {
                Write-Host "🔧 统一格式: $relativePath" -ForegroundColor Cyan
                $script:formatFixed++

                # 修复标题
                $lines[$firstToc] = $standardToc

                # 确保空行
                if ($firstToc + 1 -ge $lines.Length -or $lines[$firstToc + 1].Trim() -ne "") {
                    $newLines = @()
                    for ($i = 0; $i -le $firstToc; $i++) {
                        $newLines += $lines[$i]
                    }
                    $newLines += ""
                    for ($i = $firstToc + 1; $i -lt $lines.Length; $i++) {
                        $newLines += $lines[$i]
                    }
                    $lines = $newLines
                }

                $modified = $true
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

# 主处理
Write-Host "=========================================" -ForegroundColor Green
Write-Host "统一所有Markdown文件的目录格式" -ForegroundColor Green
Write-Host "=========================================" -ForegroundColor Green
Write-Host ""

Write-Host "开始处理文件..." -ForegroundColor Yellow
Write-Host ""

# 获取所有Markdown文件
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

$fileCount = $mdFiles.Count
Write-Host "找到 $fileCount 个Markdown文件" -ForegroundColor Cyan
Write-Host ""

$progress = 0
foreach ($file in $mdFiles) {
    $progress++
    if ($progress % 100 -eq 0) {
        Write-Host "处理进度: $progress / $fileCount" -ForegroundColor Gray
    }
    Process-File -filePath $file.FullName
}

Write-Host ""
Write-Host "=========================================" -ForegroundColor Green
Write-Host "处理完成！" -ForegroundColor Green
Write-Host "=========================================" -ForegroundColor Green
Write-Host "总文件数: $script:total" -ForegroundColor Cyan
Write-Host "已有目录: $script:processed" -ForegroundColor Cyan
Write-Host "无目录文件: $script:noToc" -ForegroundColor Cyan
Write-Host "删除重复目录: $script:duplicateRemoved" -ForegroundColor Yellow
Write-Host "统一格式: $script:formatFixed" -ForegroundColor Yellow
if ($script:errors -gt 0) {
    Write-Host "错误: $script:errors" -ForegroundColor Red
}
Write-Host ""
