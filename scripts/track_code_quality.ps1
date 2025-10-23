# 代码质量追踪脚本
# 用于持续监控项目质量指标

param(
    [string]$OutputFile = "code_quality_report.txt"
)

Write-Host "🔍 开始代码质量分析..." -ForegroundColor Cyan
Write-Host ""

$report = @"
# 代码质量追踪报告
生成时间: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 📊 基本统计

"@

# 1. Rust文件统计
Write-Host "📁 统计Rust文件..." -ForegroundColor Yellow
$rustFiles = (Get-ChildItem -Path "crates/otlp/src" -Filter "*.rs" -Recurse -File).Count
$report += "`nRust文件数: $rustFiles 个`n"
Write-Host "   Rust文件: $rustFiles 个" -ForegroundColor Green

# 2. 测试函数统计
Write-Host "🧪 统计测试函数..." -ForegroundColor Yellow
$testFns = (rg "fn test_" crates/otlp/src -c --type rust 2>$null | Measure-Object -Sum).Sum
if (!$testFns) { $testFns = 0 }
$report += "测试函数数: $testFns 个`n"
Write-Host "   测试函数: $testFns 个" -ForegroundColor Green

# 3. Async测试统计
Write-Host "⚡ 统计异步测试..." -ForegroundColor Yellow
$asyncTests = (rg "#\[tokio::test\]" crates/otlp/src -c 2>$null | Measure-Object -Sum).Sum
if (!$asyncTests) { $asyncTests = 0 }
$report += "异步测试数: $asyncTests 个`n"
Write-Host "   异步测试: $asyncTests 个" -ForegroundColor Green

# 4. Unsafe代码统计
Write-Host "⚠️  统计Unsafe代码..." -ForegroundColor Yellow
$unsafeCount = (rg "\bunsafe\b" crates/otlp/src --type rust -c 2>$null | Measure-Object -Sum).Sum
if (!$unsafeCount) { $unsafeCount = 0 }
$report += "Unsafe块数: $unsafeCount 个`n"
Write-Host "   Unsafe块: $unsafeCount 个" -ForegroundColor Green

$report += @"

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 🎯 性能指标

"@

# 5. Clone操作统计
Write-Host "📋 统计Clone操作..." -ForegroundColor Yellow
$cloneCount = (rg "clone\(\)" crates/otlp/src --type rust -c 2>$null | Measure-Object -Sum).Sum
if (!$cloneCount) { $cloneCount = 0 }
$report += "Clone操作: $cloneCount 次`n"
Write-Host "   Clone操作: $cloneCount 次" -ForegroundColor Green

# 6. Arc使用统计
Write-Host "🔗 统计Arc使用..." -ForegroundColor Yellow
$arcCount = (rg "Arc::new" crates/otlp/src --type rust -c 2>$null | Measure-Object -Sum).Sum
if (!$arcCount) { $arcCount = 0 }
$report += "Arc::new: $arcCount 次`n"
Write-Host "   Arc::new: $arcCount 次" -ForegroundColor Green

# 7. Await点统计
Write-Host "⏳ 统计Await点..." -ForegroundColor Yellow
$awaitCount = (rg "\.await" crates/otlp/src --type rust -c 2>$null | Measure-Object -Sum).Sum
if (!$awaitCount) { $awaitCount = 0 }
$report += "Await点: $awaitCount 个`n"
Write-Host "   Await点: $awaitCount 个" -ForegroundColor Green

$report += @"

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 🏗️  架构指标

"@

# 8. 公共结构体统计
Write-Host "📦 统计公共结构体..." -ForegroundColor Yellow
$structCount = (rg "pub struct" crates/otlp/src --type rust -c 2>$null | Measure-Object -Sum).Sum
if (!$structCount) { $structCount = 0 }
$report += "公共结构体: $structCount 个`n"
Write-Host "   公共结构体: $structCount 个" -ForegroundColor Green

# 9. 公共枚举统计
Write-Host "🔢 统计公共枚举..." -ForegroundColor Yellow
$enumCount = (rg "pub enum" crates/otlp/src --type rust -c 2>$null | Measure-Object -Sum).Sum
if (!$enumCount) { $enumCount = 0 }
$report += "公共枚举: $enumCount 个`n"
Write-Host "   公共枚举: $enumCount 个" -ForegroundColor Green

# 10. 公共Trait统计
Write-Host "🎭 统计公共Trait..." -ForegroundColor Yellow
$traitCount = (rg "pub trait" crates/otlp/src --type rust -c 2>$null | Measure-Object -Sum).Sum
if (!$traitCount) { $traitCount = 0 }
$report += "公共Trait: $traitCount 个`n"
Write-Host "   公共Trait: $traitCount 个" -ForegroundColor Green

$report += @"

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 📈 质量趋势

"@

# 计算质量指标
$testCoverage = if ($rustFiles -gt 0) { [math]::Round($testFns / $rustFiles, 2) } else { 0 }
$asyncRatio = if ($testFns -gt 0) { [math]::Round($asyncTests / $testFns * 100, 1) } else { 0 }

$report += @"

每文件测试数: $testCoverage 个/文件
异步测试占比: $asyncRatio%
Clone/文件比: $([math]::Round($cloneCount / $rustFiles, 2))
Unsafe/文件比: $([math]::Round($unsafeCount / $rustFiles, 2))

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 🎯 改进目标对比

当前 vs 目标:

测试函数:     $testFns → 400+ $(if ($testFns -ge 400) {"✅"} else {"⏳"})
Clone操作:    $cloneCount → 340 $(if ($cloneCount -le 340) {"✅"} else {"⏳"})
Unsafe文档:   估计0% → 100% ⏳
Rust文件:     $rustFiles → <60 $(if ($rustFiles -le 60) {"✅"} else {"⏳"})
公共结构体:   $structCount → 300 $(if ($structCount -le 300) {"✅"} else {"⏳"})

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 💡 建议

"@

# 生成建议
$suggestions = @()

if ($testFns -lt 400) {
    $needed = 400 - $testFns
    $suggestions += "- 需要增加 $needed 个测试函数"
}

if ($cloneCount -gt 340) {
    $reduce = $cloneCount - 340
    $suggestions += "- 需要减少 $reduce 次clone操作"
}

if ($unsafeCount -gt 0) {
    $suggestions += "- 需要为 $unsafeCount 个unsafe块添加safety文档"
}

if ($rustFiles -gt 60) {
    $reduce = $rustFiles - 60
    $suggestions += "- 需要减少 $reduce 个Rust文件（合并模块）"
}

if ($structCount -gt 300) {
    $reduce = $structCount - 300
    $suggestions += "- 需要减少 $reduce 个公共结构体（隐藏内部实现）"
}

if ($suggestions.Count -eq 0) {
    $report += "`n所有目标已达成! 🎉`n"
} else {
    $report += "`n"
    $suggestions | ForEach-Object {
        $report += "$_`n"
    }
}

$report += @"

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

报告生成完成！

可以使用以下命令定期运行此脚本追踪进度：
    powershell -File scripts/track_code_quality.ps1

"@

# 输出报告
$report | Out-File -FilePath $OutputFile -Encoding UTF8

Write-Host ""
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan
Write-Host "✅ 报告已生成: $OutputFile" -ForegroundColor Green
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan
Write-Host ""

# 显示报告
Write-Host "📄 报告摘要:" -ForegroundColor Cyan
Write-Host ""
Write-Host "   Rust文件:    $rustFiles" -ForegroundColor White
Write-Host "   测试函数:    $testFns" -ForegroundColor White
Write-Host "   Clone操作:   $cloneCount" -ForegroundColor White
Write-Host "   Unsafe块:    $unsafeCount" -ForegroundColor White
Write-Host "   公共结构体:  $structCount" -ForegroundColor White
Write-Host ""

if ($suggestions.Count -gt 0) {
    Write-Host "⚠️  待改进项目: $($suggestions.Count) 个" -ForegroundColor Yellow
} else {
    Write-Host "🎉 所有目标已达成!" -ForegroundColor Green
}

Write-Host ""
Write-Host "详细报告请查看: $OutputFile" -ForegroundColor Cyan

