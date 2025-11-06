# 修复目录中包含标题的问题

$ErrorActionPreference = "Continue"

$projectRoot = Split-Path -Parent $PSScriptRoot

$script:total = 0
$script:fixed = 0

function Process-File {
    param([string]$filePath)

    $script:total++
    $relativePath = $filePath.Replace($projectRoot + "\", "").Replace($projectRoot + "/", "")

    try {
        $content = [System.IO.File]::ReadAllText($filePath, [System.Text.Encoding]::UTF8)
        $lines = $content -split "`r?`n"
        $modified = $false

        # 查找目录位置
        $tocLine = -1
        for ($i = 0; $i -lt $lines.Length; $i++) {
            if ($lines[$i] -match '^##\s+📋\s+目录\s*$') {
                $tocLine = $i
                break
            }
        }

        if ($tocLine -eq -1) {
            return
        }

        # 查找目录结束位置
        $tocEnd = $lines.Length
        for ($j = $tocLine + 1; $j -lt $lines.Length; $j++) {
            if ($lines[$j] -match '^##\s+') {
                $tocEnd = $j
                break
            }
        }

        # 检查目录部分是否有标题
        $headersToRemove = @()
        for ($i = $tocLine + 2; $i -lt $tocEnd; $i++) {
            if ($lines[$i] -match '^###\s+|^##\s+[^📋]') {
                $headersToRemove += $i
            }
        }

        if ($headersToRemove.Count -gt 0) {
            Write-Host "🔧 删除目录中的标题: $relativePath" -ForegroundColor Yellow
            $script:fixed++

            # 从后往前删除
            $newLines = @()
            for ($i = 0; $i -lt $lines.Length; $i++) {
                if ($headersToRemove -notcontains $i) {
                    $newLines += $lines[$i]
                }
                else {
                    # 如果是标题，检查下一行是否为空，如果是也删除
                    if ($i + 1 -lt $lines.Length -and $lines[$i + 1].Trim() -eq "") {
                        # 跳过空行
                        continue
                    }
                }
            }

            $lines = $newLines
            $modified = $true
        }

        # 保存修改
        if ($modified) {
            $content = ($lines -join "`r`n") + "`r`n"
            [System.IO.File]::WriteAllText($filePath, $content, [System.Text.Encoding]::UTF8)
        }

    }
    catch {
        Write-Host "❌ 错误: $relativePath - $_" -ForegroundColor Red
    }
}

Write-Host "修复目录中包含标题的文件..." -ForegroundColor Yellow
Write-Host ""

$mdFiles = Get-ChildItem -Path $projectRoot -Filter "*.md" -Recurse -File |
Where-Object {
    $fullPath = $_.FullName
    $fullPath -notmatch "\\target\\" -and
    $fullPath -notmatch "\\.git\\" -and
    $fullPath -notmatch "\\node_modules\\" -and
    $fullPath -notmatch "\\.vscode\\" -and
    $fullPath -notmatch "\\.github\\"
}

foreach ($file in $mdFiles) {
    Process-File -filePath $file.FullName
}

Write-Host ""
Write-Host "修复完成！" -ForegroundColor Green
Write-Host "处理文件数: $script:total" -ForegroundColor Cyan
Write-Host "修复文件数: $script:fixed" -ForegroundColor Yellow
Write-Host ""
