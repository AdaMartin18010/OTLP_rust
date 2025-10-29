# 修复剩余的内容文档

Write-Host "开始修复剩余文档..." -ForegroundColor Cyan

# RUST_QUICK_REFERENCE_2025.md
$file = "docs\RUST_QUICK_REFERENCE_2025.md"
$content = Get-Content $file -Raw -Encoding UTF8
$content = $content -replace '## 1\. Rust 1\.90 新特性', '## 🆕 Rust 1.90 新特性' `
    -replace '## 2\. OpenTelemetry集成', '## 🔭 OpenTelemetry集成' `
    -replace '## 3\. 分布式系统模式', '## 🌐 分布式系统模式' `
    -replace '## 4\. 编译期优化', '## ⚙️ 编译期优化' `
    -replace '## 5\. 运行时优化', '## ⚡ 运行时优化' `
    -replace '## 6\. Cargo命令速查', '## 📦 Cargo命令速查' `
    -replace '## 7\. Rustup命令速查', '## 🛠️ Rustup命令速查' `
    -replace '## 8\. 常见编译错误', '## ❌ 常见编译错误' `
    -replace '## 9\. 延迟目标', '## 📈 延迟目标' `
    -replace '## 10\. 吞吐量目标', '## 📊 吞吐量目标'
Set-Content $file -Value $content -NoNewline -Encoding UTF8
Write-Host "✅ RUST_QUICK_REFERENCE" -ForegroundColor Green

# RUST_KNOWLEDGE_GRAPH_2025_10.md
$file = "docs\RUST_KNOWLEDGE_GRAPH_2025_10.md"
$content = Get-Content $file -Raw -Encoding UTF8
$content = $content -replace '## 1\. 知识图谱总览', '## 🌐 知识图谱总览' `
    -replace '## 2\. 核心概念关系图', '## 🔗 核心概念关系图' `
    -replace '## 3\. 多维度矩阵对比', '## 📊 多维度矩阵对比' `
    -replace '## 4\. 属性特性分析', '## 💎 属性特性分析' `
    -replace '## 5\. 技术栈依赖图', '## 🔧 技术栈依赖图' `
    -replace '## 6\. 演进路径图', '## 📈 演进路径图' `
    -replace '## 7\. 实践应用映射', '## 💡 实践应用映射' `
    -replace '## 8\. 性能维度分析', '## ⚡ 性能维度分析' `
    -replace '## 9\. 知识图谱应用指南', '## 📖 知识图谱应用指南' `
    -replace '## 10\. 交互式查询指南', '## 🔍 交互式查询指南'
Set-Content $file -Value $content -NoNewline -Encoding UTF8
Write-Host "✅ RUST_KNOWLEDGE_GRAPH" -ForegroundColor Green

# RUST_FAQ_DEEP_DIVE_2025.md
$file = "docs\RUST_FAQ_DEEP_DIVE_2025.md"
$content = Get-Content $file -Raw -Encoding UTF8
$content = $content -replace '## 1\. 编译性能问题', '## ⚙️ 编译性能问题' `
    -replace '## 2\. 所有权系统', '## 🔒 所有权系统' `
    -replace '## 3\. 生命周期', '## ⏱️ 生命周期' `
    -replace '## 4\. Async/Await机制', '## ⚡ Async/Await机制'
Set-Content $file -Value $content -NoNewline -Encoding UTF8
Write-Host "✅ RUST_FAQ_DEEP_DIVE" -ForegroundColor Green

# RUST_CODE_EXAMPLES_2025.md
$file = "docs\RUST_CODE_EXAMPLES_2025.md"
$content = Get-Content $file -Raw -Encoding UTF8
$content = $content -replace '## 1\. Web服务', '## 🌐 Web服务' `
    -replace '## 2\. 异步编程', '## ⚡ 异步编程' `
    -replace '## 3\. 并发模式', '## 🔄 并发模式' `
    -replace '## 4\. 数据处理', '## 📊 数据处理' `
    -replace '## 5\. 错误处理', '## ❌ 错误处理' `
    -replace '## 6\. 性能优化', '## 🚀 性能优化' `
    -replace '## 7\. OpenTelemetry集成', '## 🔭 OpenTelemetry集成' `
    -replace '## 8\. 微服务模式', '## 🌐 微服务模式'
Set-Content $file -Value $content -NoNewline -Encoding UTF8
Write-Host "✅ RUST_CODE_EXAMPLES" -ForegroundColor Green

# PERFORMANCE_OPTIMIZATION_COOKBOOK_2025.md
$file = "docs\PERFORMANCE_OPTIMIZATION_COOKBOOK_2025.md"
$content = Get-Content $file -Raw -Encoding UTF8
$content = $content -replace '## 1\. 编译期优化（立即可得）', '## ⚙️ 编译期优化（立即可得）' `
    -replace '## 2\. 算法优化（最大收益）', '## 🧮 算法优化（最大收益）' `
    -replace '## 3\. 零拷贝技术', '## 📋 零拷贝技术' `
    -replace '## 4\. 并发优化', '## 🔄 并发优化' `
    -replace '## 5\. 异步IO优化', '## ⚡ 异步IO优化' `
    -replace '## 6\. 内存优化', '## 💾 内存优化' `
    -replace '## 7\. SIMD加速', '## 🚀 SIMD加速' `
    -replace '## 8\. 性能测量', '## 📊 性能测量' `
    -replace '## 9\. 实战案例', '## 💡 实战案例' `
    -replace '## 10\. 优化检查清单', '## ✅ 优化检查清单'
Set-Content $file -Value $content -NoNewline -Encoding UTF8
Write-Host "✅ PERFORMANCE_OPTIMIZATION_COOKBOOK" -ForegroundColor Green

# FOLDER_STRUCTURE_TEMPLATE.md
$file = "docs\FOLDER_STRUCTURE_TEMPLATE.md"
$content = Get-Content $file -Raw -Encoding UTF8
$content = $content -replace '## 1\. 第一章', '## 📖 第一章' `
    -replace '## 2\. 第二章', '## 📘 第二章'
Set-Content $file -Value $content -NoNewline -Encoding UTF8
Write-Host "✅ FOLDER_STRUCTURE_TEMPLATE" -ForegroundColor Green

Write-Host "`n✅ 所有7个文档已完成修复！" -ForegroundColor Green

