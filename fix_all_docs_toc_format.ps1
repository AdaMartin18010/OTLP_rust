# 批量修复所有文档的目录格式
# 将数字序号格式转换为 emoji + 层次结构格式

Write-Host "开始修复所有文档的目录格式..." -ForegroundColor Cyan
Write-Host ""

$files = @(
    "docs\09_CRATES\CONCEPTS.md",
    "docs\09_CRATES\COMPARISON_MATRIX.md",
    "docs\09_CRATES\KNOWLEDGE_GRAPH.md"
)

$fixed = 0
$skipped = 0

foreach ($file in $files) {
    if (Test-Path $file) {
        Write-Host "处理: $file" -ForegroundColor Yellow
        
        $content = Get-Content $file -Raw -Encoding UTF8
        $originalContent = $content
        
        # 检查是否使用了旧的数字序号格式
        if ($content -match '(?m)^1\. \[') {
            Write-Host "  发现旧格式，开始转换..." -ForegroundColor Gray
            
            # 根据文件类型应用不同的转换规则
            if ($file -like "*CONCEPTS.md") {
                # CONCEPTS.md 的标准格式
                $content = $content -replace '(?m)^## (\d+)\. ', '## 📖 '
            }
            elseif ($file -like "*COMPARISON_MATRIX.md") {
                # COMPARISON_MATRIX.md 的标准格式
                $content = $content -replace '(?m)^## (\d+)\. ', '## 📊 '
            }
            elseif ($file -like "*KNOWLEDGE_GRAPH.md") {
                # KNOWLEDGE_GRAPH.md 的标准格式
                $content = $content -replace '(?m)^## (\d+)\. ', '## 🔗 '
            }
            
            if ($content -ne $originalContent) {
                Set-Content $file -Value $content -NoNewline -Encoding UTF8
                Write-Host "  ✅ 已修复" -ForegroundColor Green
                $fixed++
            }
            else {
                Write-Host "  ⚠️  未发现变化" -ForegroundColor Yellow
                $skipped++
            }
        }
        else {
            Write-Host "  ℹ️  已是标准格式" -ForegroundColor Cyan
            $skipped++
        }
    }
    else {
        Write-Host "  ❌ 文件不存在" -ForegroundColor Red
        $skipped++
    }
    Write-Host ""
}

Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan
Write-Host "修复完成！" -ForegroundColor Green
Write-Host "✅ 已修复: $fixed 个文件" -ForegroundColor Green
Write-Host "⏭️  已跳过: $skipped 个文件" -ForegroundColor Yellow
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan

