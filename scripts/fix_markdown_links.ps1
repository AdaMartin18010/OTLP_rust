# 批量修复Markdown链接片段错误
# 修复MD051: link-fragments should be valid

param(
    [string]$Path = "crates/reliability/docs",
    [switch]$DryRun
)

$fixCount = 0
$fileCount = 0

# 获取所有markdown文件
$mdFiles = Get-ChildItem -Path $Path -Filter *.md -Recurse

Write-Host "找到 $($mdFiles.Count) 个Markdown文件"

foreach ($file in $mdFiles) {
    $fileCount++
    Write-Host "`n处理: $($file.Name)" -ForegroundColor Cyan
    
    $content = Get-Content $file.FullName -Raw -Encoding UTF8
    $originalContent = $content
    $fileFixed = $false
    
    # 修复1: 移除目录链接中的emoji和特殊符号
    # 例如: [📊 目录](#-目录) -> [目录](#目录)
    $pattern1 = '\[[\u{1F300}-\u{1F9FF}]?\s*([^\]]+?)\]\(#[\u{1F300}-\u{1F9FF}]?-([^\)]+)\)'
    if ($content -match $pattern1) {
        $content = $content -replace $pattern1, '[$1](#$2)'
        $fileFixed = $true
        Write-Host "  - 修复emoji链接"
    }
    
    # 修复2: 删除重复的目录结构
    # 检测连续的"## 目录"或"## 📋 目录"
    $tocPattern = '(##\s+[\u{1F300}-\u{1F9FF}]?\s*目录.*?(?=\n##\s+[^#]|\n###|\Z))'
    $tocMatches = [regex]::Matches($content, $tocPattern, [System.Text.RegularExpressions.RegexOptions]::Singleline)
    
    if ($tocMatches.Count -gt 1) {
        Write-Host "  - 发现 $($tocMatches.Count) 个目录，删除重复"
        # 保留第一个，删除其他
        for ($i = $tocMatches.Count - 1; $i -gt 0; $i--) {
            $content = $content.Remove($tocMatches[$i].Index, $tocMatches[$i].Length)
        }
        $fileFixed = $true
    }
    
    # 修复3: 移除标题中的emoji
    # 例如: ## 🔧 技术亮点 -> ## 技术亮点
    $titlePattern = '(^#{1,6})\s*[\u{1F300}-\u{1F9FF}]\s+'
    if ($content -match $titlePattern) {
        $content = $content -replace $titlePattern, '$1 '
        $fileFixed = $true
        Write-Host "  - 移除标题emoji"
    }
    
    # 修复4: 修正常见的不匹配标题
    # 移除标题中的代码标记和额外描述
    $replacements = @{
        '(###?\s+\d+\.\s+[^(]+)\s*\([^)]+\)' = '$1'  # 移除括号中的内容
    }
    
    foreach ($pattern in $replacements.Keys) {
        if ($content -match $pattern) {
            $content = $content -replace $pattern, $replacements[$pattern]
            $fileFixed = $true
            Write-Host "  - 简化标题格式"
        }
    }
    
    # 如果有修改
    if ($fileFixed) {
        $fixCount++
        
        if ($DryRun) {
            Write-Host "  ✓ [预览模式] 文件需要修复" -ForegroundColor Yellow
        } else {
            # 保存文件
            $content | Set-Content $file.FullName -Encoding UTF8 -NoNewline
            Write-Host "  ✓ 文件已修复" -ForegroundColor Green
        }
    } else {
        Write-Host "  - 无需修复" -ForegroundColor Gray
    }
}

Write-Host "`n================================" -ForegroundColor Cyan
Write-Host "修复完成!" -ForegroundColor Green
Write-Host "  处理文件: $fileCount"
Write-Host "  修复文件: $fixCount"
if ($DryRun) {
    Write-Host "`n提示: 使用 -DryRun:$false 参数来实际应用修复" -ForegroundColor Yellow
}

