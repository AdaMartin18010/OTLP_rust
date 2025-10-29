# 修复剩余所有使用数字序号的文档

Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan
Write-Host "批量修复剩余文档" -ForegroundColor Cyan
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━`n" -ForegroundColor Cyan

$fixed = 0
$skipped = 0

# 获取所有需要修复的crates文档
$cratesFiles = Get-ChildItem -Path "crates" -Filter "*.md" -Recurse | Where-Object { 
    $_.DirectoryName -match "docs"
}

Write-Host "扫描 crates 目录..." -ForegroundColor Yellow

foreach ($file in $cratesFiles) {
    try {
        $content = Get-Content $file.FullName -Raw -Encoding UTF8 -ErrorAction Stop
        
        # 检查是否有数字序号章节
        if ($content -match '(?m)^## \d+\. ') {
            $relativePath = $file.FullName.Substring($PWD.Path.Length + 1)
            Write-Host "修复: $relativePath" -ForegroundColor Yellow
            
            # 通用替换模式 - 使用更全面的emoji映射
            $updated = $content `
                -replace '(?m)^## 1\. (概述|简介|介绍|Overview)', '## 🎯 $1' `
                -replace '(?m)^## 1\. (快速|开始|入门|Getting)', '## 🚀 $1' `
                -replace '(?m)^## 1\. ', '## 📖 ' `
                -replace '(?m)^## 2\. (安装|配置|Setup)', '## ⚙️ $1' `
                -replace '(?m)^## 2\. (架构|结构|Architecture)', '## 🏗️ $1' `
                -replace '(?m)^## 2\. ', '## 📝 ' `
                -replace '(?m)^## 3\. (实现|Implementation|开发)', '## 💻 $1' `
                -replace '(?m)^## 3\. (示例|Examples|案例)', '## 💡 $1' `
                -replace '(?m)^## 3\. ', '## 🔍 ' `
                -replace '(?m)^## 4\. (配置|Configuration)', '## ⚙️ $1' `
                -replace '(?m)^## 4\. (API|接口)', '## 🔌 $1' `
                -replace '(?m)^## 4\. ', '## 🔧 ' `
                -replace '(?m)^## 5\. (性能|Performance)', '## ⚡ $1' `
                -replace '(?m)^## 5\. (测试|Testing)', '## 🧪 $1' `
                -replace '(?m)^## 5\. ', '## 📊 ' `
                -replace '(?m)^## 6\. (部署|Deployment)', '## 🚀 $1' `
                -replace '(?m)^## 6\. (监控|Monitoring)', '## 📊 $1' `
                -replace '(?m)^## 6\. ', '## 🌟 ' `
                -replace '(?m)^## 7\. (安全|Security)', '## 🛡️ $1' `
                -replace '(?m)^## 7\. (故障|Troubleshooting)', '## 🔍 $1' `
                -replace '(?m)^## 7\. ', '## 🔬 ' `
                -replace '(?m)^## 8\. (参考|Reference)', '## 📚 $1' `
                -replace '(?m)^## 8\. (总结|Conclusion)', '## 🎊 $1' `
                -replace '(?m)^## 8\. ', '## 💻 ' `
                -replace '(?m)^## 9\. (附录|Appendix)', '## 📎 $1' `
                -replace '(?m)^## 9\. ', '## 📚 ' `
                -replace '(?m)^## 10\. ', '## ✅ ' `
                -replace '(?m)^## 11\. ', '## 🌈 ' `
                -replace '(?m)^## 12\. ', '## 🎓 ' `
                -replace '(?m)^## 13\. ', '## 🔗 ' `
                -replace '(?m)^## 14\. ', '## 💡 ' `
                -replace '(?m)^## 15\. ', '## 🎯 '
            
            if ($updated -ne $content) {
                Set-Content $file.FullName -Value $updated -NoNewline -Encoding UTF8
                Write-Host "  ✅ 已修复" -ForegroundColor Green
                $fixed++
            } else {
                Write-Host "  ⏭️  无变化" -ForegroundColor Gray
                $skipped++
            }
        }
    }
    catch {
        Write-Host "  ❌ 错误: $_" -ForegroundColor Red
    }
}

# 获取所有需要修复的docs文档
Write-Host "`n扫描 docs 目录..." -ForegroundColor Yellow

$docsFiles = Get-ChildItem -Path "docs" -Filter "*.md" -Recurse | Where-Object { 
    $_.DirectoryName -notmatch "archives" -and
    $_.Name -notmatch "(PHASE|STATUS|PROGRESS|COMPLETE|SUMMARY|REPORT).*\.md$"
}

foreach ($file in $docsFiles) {
    try {
        $content = Get-Content $file.FullName -Raw -Encoding UTF8 -ErrorAction Stop
        
        # 检查是否有数字序号章节
        if ($content -match '(?m)^## \d+\. ') {
            $relativePath = $file.FullName.Substring($PWD.Path.Length + 1)
            Write-Host "修复: $relativePath" -ForegroundColor Yellow
            
            # 通用替换模式
            $updated = $content `
                -replace '(?m)^## 1\. ', '## 🎯 ' `
                -replace '(?m)^## 2\. ', '## 📝 ' `
                -replace '(?m)^## 3\. ', '## 💡 ' `
                -replace '(?m)^## 4\. ', '## 🔧 ' `
                -replace '(?m)^## 5\. ', '## 📊 ' `
                -replace '(?m)^## 6\. ', '## 🚀 ' `
                -replace '(?m)^## 7\. ', '## 🔍 ' `
                -replace '(?m)^## 8\. ', '## 💻 ' `
                -replace '(?m)^## 9\. ', '## 📚 ' `
                -replace '(?m)^## 10\. ', '## ✅ ' `
                -replace '(?m)^## 11\. ', '## 🌟 ' `
                -replace '(?m)^## 12\. ', '## 🎓 '
            
            if ($updated -ne $content) {
                Set-Content $file.FullName -Value $updated -NoNewline -Encoding UTF8
                Write-Host "  ✅ 已修复" -ForegroundColor Green
                $fixed++
            } else {
                Write-Host "  ⏭️  无变化" -ForegroundColor Gray
                $skipped++
            }
        }
    }
    catch {
        Write-Host "  ❌ 错误: $_" -ForegroundColor Red
    }
}

Write-Host "`n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan
Write-Host "批量修复完成！" -ForegroundColor Green
Write-Host ""
Write-Host "✅ 已修复: $fixed 个文档" -ForegroundColor Green
Write-Host "⏭️  已跳过: $skipped 个文档" -ForegroundColor Yellow
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan

