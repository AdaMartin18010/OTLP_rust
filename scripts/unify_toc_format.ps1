# 统一Markdown文件的目录格式
# 标准格式：
# - 标题：## 📋 目录
# - 空行
# - 目录列表使用2空格缩进

$ErrorActionPreference = "Stop"

$projectRoot = Split-Path -Parent $PSScriptRoot
$analysisDir = Join-Path $projectRoot "analysis"

if (-not (Test-Path $analysisDir)) {
    Write-Host "目录不存在: $analysisDir" -ForegroundColor Red
    exit 1
}

$mdFiles = Get-ChildItem -Path $analysisDir -Filter "*.md" -Recurse

Write-Host "找到 $($mdFiles.Count) 个Markdown文件" -ForegroundColor Green

$modifiedCount = 0

foreach ($file in $mdFiles) {
    try {
        $content = Get-Content -Path $file.FullName -Raw -Encoding UTF8
        $lines = $content -split "`n"
        $modified = $false

        # 查找目录部分
        $tocStart = -1
        for ($i = 0; $i -lt $lines.Length; $i++) {
            if ($lines[$i] -match '^##+\s*📋\s*目录|^##+\s*目录') {
                $tocStart = $i
                break
            }
        }

        if ($tocStart -ge 0) {
            # 确保标题格式正确
            if ($lines[$tocStart] -notmatch '^##\s+📋\s+目录') {
                $lines[$tocStart] = "## 📋 目录"
                $modified = $true
            }

            # 确保标题后面有空行
            if ($tocStart + 1 -lt $lines.Length -and $lines[$tocStart + 1].Trim() -ne "") {
                $lines = $lines[0..$tocStart] + @("") + $lines[($tocStart + 1)..($lines.Length - 1)]
                $modified = $true
            }

            # 标准化目录内容缩进
            $tocEnd = $lines.Length
            for ($i = $tocStart + 2; $i -lt $lines.Length; $i++) {
                $line = $lines[$i]
                if ($line.Trim() -match '^##+\s+') {
                    # 找到下一个同级别或更高级别的标题
                    $level = ($line -match '^(##+)').Groups[1].Length
                    if ($level -le 2) {
                        $tocEnd = $i
                        break
                    }
                }

                # 标准化缩进
                if ($line.Trim() -match '^-\s+\[.*\]') {
                    $indent = $line.Length - $line.TrimStart().Length
                    $level = [Math]::Floor($indent / 2)
                    $normalizedLine = ("  " * $level) + $line.TrimStart()
                    if ($normalizedLine -ne $line) {
                        $lines[$i] = $normalizedLine
                        $modified = $true
                    }
                }
            }
        }

        if ($modified) {
            $newContent = $lines -join "`n"
            Set-Content -Path $file.FullName -Value $newContent -Encoding UTF8 -NoNewline
            $modifiedCount++
            Write-Host "已更新: $($file.FullName.Replace($projectRoot, '').TrimStart('\'))" -ForegroundColor Yellow
        }
    }
    catch {
        Write-Host "处理文件 $($file.FullName) 时出错: $_" -ForegroundColor Red
    }
}

Write-Host "`n完成！共更新了 $modifiedCount 个文件" -ForegroundColor Green
