# 更新所有剩余文档的章节标题

Write-Host "批量更新所有剩余章节..." -ForegroundColor Cyan

# STM (软件事务内存) for advanced_concurrency_patterns.md  
$file = "crates\model\docs\advanced\advanced_concurrency_patterns.md"
$content = Get-Content $file -Raw -Encoding UTF8
$content = $content -replace 'STM \(软件事务内存\)', '软件事务内存'
Set-Content $file -Value $content -NoNewline -Encoding UTF8

# cloud_native_best_practices.md
$file = "crates\otlp\docs\advanced\cloud_native_best_practices.md"
$content = Get-Content $file -Raw -Encoding UTF8
$content = $content -replace '(?m)^## 云原生概述', '## 🎯 云原生概述' `
    -replace '(?m)^## 12-Factor App 原则', '## 📝 12-Factor App' `
    -replace '(?m)^## 容器化最佳实践', '## 🐳 容器化最佳实践' `
    -replace '(?m)^## Kubernetes 生产部署', '## ☸️ Kubernetes 部署' `
    -replace '(?m)^## 服务网格集成', '## 🕸️ 服务网格' `
    -replace '(?m)^## 配置管理', '## ⚙️ 配置管理' `
    -replace '(?m)^## CI/CD 流程', '## 🔄 CI/CD 流水线' `
    -replace '(?m)^## GitOps 实践', '## 📂 GitOps' `
    -replace '(?m)^## 总结', '## 📚 总结'
Set-Content $file -Value $content -NoNewline -Encoding UTF8
Write-Host "✅ cloud_native_best_practices.md" -ForegroundColor Green

Write-Host "`n✅ 完成！" -ForegroundColor Cyan

