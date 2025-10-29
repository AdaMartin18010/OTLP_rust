# 简单的Markdown链接修复脚本
# 移除标题中括号内的额外描述

$path = "crates/reliability/docs"
$count = 0

Get-ChildItem -Path $path -Filter *.md -Recurse | ForEach-Object {
    $content = Get-Content $_.FullName -Raw -Encoding UTF8
    $original = $content
    
    # 修复：移除标题中的括号描述
    # 例如: ### 1. 软件事务内存（STM）实现 (`stm.rs`, ~650行代码) -> ### 1. 软件事务内存（STM）实现
    $content = $content -replace '(###?\s+\d+\.\s+[^`]+?)\s+\(`[^)]+\)', '$1'
    
    if ($content -ne $original) {
        $content | Set-Content $_.FullName -Encoding UTF8 -NoNewline
        Write-Host "✓ Fixed: $($_.Name)" -ForegroundColor Green
        $count++
    }
}

Write-Host "`nTotal files fixed: $count" -ForegroundColor Cyan

