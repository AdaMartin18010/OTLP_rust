# 批量修复所有目录下的 CONCEPTS, COMPARISON_MATRIX, KNOWLEDGE_GRAPH 文档格式

Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan
Write-Host "开始批量修复42个文档的格式" -ForegroundColor Cyan
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━`n" -ForegroundColor Cyan

$directories = @(
    "docs\00_INDEX",
    "docs\01_GETTING_STARTED",
    "docs\02_THEORETICAL_FRAMEWORK",
    "docs\03_API_REFERENCE",
    "docs\04_ARCHITECTURE",
    "docs\05_IMPLEMENTATION",
    "docs\06_DEPLOYMENT",
    "docs\07_INTEGRATION",
    "docs\08_REFERENCE",
    "docs\10_DEVELOPMENT",
    "docs\11_EXAMPLES",
    "docs\12_GUIDES",
    "docs\13_PLANNING",
    "docs\14_TECHNICAL"
)

$fixed = 0
$skipped = 0
$errors = 0

foreach ($dir in $directories) {
    Write-Host "处理目录: $dir" -ForegroundColor Yellow
    
    # CONCEPTS.md
    $conceptsFile = Join-Path $dir "CONCEPTS.md"
    if (Test-Path $conceptsFile) {
        try {
            $content = Get-Content $conceptsFile -Raw -Encoding UTF8
            
            # 只更新章节标题（移除数字序号，添加emoji）
            $updated = $content -replace '(?m)^## 1\. ', '## 📖 ' `
                -replace '(?m)^## 2\. ', '## 🔍 ' `
                -replace '(?m)^## 3\. ', '## 💡 ' `
                -replace '(?m)^## 4\. ', '## ⚙️ ' `
                -replace '(?m)^## 5\. ', '## 📊 ' `
                -replace '(?m)^## 6\. ', '## 🛠️ ' `
                -replace '(?m)^## 7\. ', '## ✅ ' `
                -replace '(?m)^## 8\. ', '## 📚 '
            
            if ($updated -ne $content) {
                Set-Content $conceptsFile -Value $updated -NoNewline -Encoding UTF8
                Write-Host "  ✅ CONCEPTS.md" -ForegroundColor Green
                $fixed++
            } else {
                Write-Host "  ⏭️  CONCEPTS.md (无变化)" -ForegroundColor Gray
                $skipped++
            }
        }
        catch {
            Write-Host "  ❌ CONCEPTS.md 失败: $_" -ForegroundColor Red
            $errors++
        }
    }
    
    # COMPARISON_MATRIX.md
    $matrixFile = Join-Path $dir "COMPARISON_MATRIX.md"
    if (Test-Path $matrixFile) {
        try {
            $content = Get-Content $matrixFile -Raw -Encoding UTF8
            
            $updated = $content -replace '(?m)^## 1\. ', '## ⚖️ ' `
                -replace '(?m)^## 2\. ', '## 🔗 ' `
                -replace '(?m)^## 3\. ', '## ⚡ ' `
                -replace '(?m)^## 4\. ', '## 🎯 ' `
                -replace '(?m)^## 5\. ', '## 📚 ' `
                -replace '(?m)^## 6\. ', '## 📊 ' `
                -replace '(?m)^## 7\. ', '## 💡 ' `
                -replace '(?m)^## 8\. ', '## ✅ '
            
            if ($updated -ne $content) {
                Set-Content $matrixFile -Value $updated -NoNewline -Encoding UTF8
                Write-Host "  ✅ COMPARISON_MATRIX.md" -ForegroundColor Green
                $fixed++
            } else {
                Write-Host "  ⏭️  COMPARISON_MATRIX.md (无变化)" -ForegroundColor Gray
                $skipped++
            }
        }
        catch {
            Write-Host "  ❌ COMPARISON_MATRIX.md 失败: $_" -ForegroundColor Red
            $errors++
        }
    }
    
    # KNOWLEDGE_GRAPH.md
    $graphFile = Join-Path $dir "KNOWLEDGE_GRAPH.md"
    if (Test-Path $graphFile) {
        try {
            $content = Get-Content $graphFile -Raw -Encoding UTF8
            
            $updated = $content -replace '(?m)^## 1\. ', '## 🌐 ' `
                -replace '(?m)^## 2\. ', '## 🔗 ' `
                -replace '(?m)^## 3\. ', '## 📊 ' `
                -replace '(?m)^## 4\. ', '## 💡 ' `
                -replace '(?m)^## 5\. ', '## ⚙️ ' `
                -replace '(?m)^## 6\. ', '## 📚 '
            
            if ($updated -ne $content) {
                Set-Content $graphFile -Value $updated -NoNewline -Encoding UTF8
                Write-Host "  ✅ KNOWLEDGE_GRAPH.md" -ForegroundColor Green
                $fixed++
            } else {
                Write-Host "  ⏭️  KNOWLEDGE_GRAPH.md (无变化)" -ForegroundColor Gray
                $skipped++
            }
        }
        catch {
            Write-Host "  ❌ KNOWLEDGE_GRAPH.md 失败: $_" -ForegroundColor Red
            $errors++
        }
    }
    
    Write-Host ""
}

Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan
Write-Host "批量修复完成！" -ForegroundColor Green
Write-Host ""
Write-Host "✅ 已修复: $fixed 个文档" -ForegroundColor Green
Write-Host "⏭️  已跳过: $skipped 个文档" -ForegroundColor Yellow
Write-Host "❌ 错误: $errors 个文档" -ForegroundColor Red
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan

