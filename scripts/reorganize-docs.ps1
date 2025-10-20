# 文档重组脚本 - PowerShell 版本
# 用途: 按照新的文档架构重组现有文档
# 运行: .\scripts\reorganize-docs.ps1

param(
    [switch]$DryRun = $false,  # 模拟运行，不实际移动文件
    [switch]$Backup = $true     # 是否备份原文件
)

$ErrorActionPreference = "Stop"

Write-Host "================================================" -ForegroundColor Cyan
Write-Host "   OTLP Rust 文档重组脚本" -ForegroundColor Cyan
Write-Host "================================================" -ForegroundColor Cyan
Write-Host ""

if ($DryRun) {
    Write-Host "[模拟模式] 将显示操作但不实际执行" -ForegroundColor Yellow
    Write-Host ""
}

# 创建新的文档目录结构
$newDocs = @{
    "docs/architecture" = @()
    "docs/guides/getting-started" = @()
    "docs/guides/tutorials" = @()
    "docs/guides/howto" = @()
    "docs/guides/best-practices" = @()
    "docs/api/otlp-core" = @()
    "docs/api/otlp-proto" = @()
    "docs/api/otlp-transport" = @()
    "docs/api/otlp" = @()
    "docs/api/reliability" = @()
    "docs/api/integrations" = @()
    "docs/design/rfcs" = @()
    "docs/design/decisions" = @()
    "docs/design/specifications" = @()
    "docs/implementation/semantic-models" = @()
    "docs/implementation/algorithms" = @()
    "docs/implementation/optimizations" = @()
    "docs/operations/deployment" = @()
    "docs/operations/monitoring" = @()
    "docs/operations/maintenance" = @()
    "docs/reports/benchmarks" = @()
    "docs/reports/security" = @()
    "docs/reports/performance" = @()
    "docs/reports/progress" = @()
    "docs/research/quantum-observability" = @()
    "docs/research/neuromorphic-monitoring" = @()
    "docs/research/ai-automation" = @()
    "docs/contributing" = @()
    "docs/reference" = @()
}

# 创建目录
Write-Host "创建新的文档目录结构..." -ForegroundColor Green
foreach ($dir in $newDocs.Keys) {
    if (-not (Test-Path $dir)) {
        if (-not $DryRun) {
            New-Item -ItemType Directory -Path $dir -Force | Out-Null
        }
        Write-Host "  ✓ 创建目录: $dir" -ForegroundColor Gray
    }
}
Write-Host ""

# 文件迁移映射
$migrations = @(
    # 从 analysis/ 迁移语义模型
    @{
        Pattern = "analysis/01_semantic_models/*.md"
        Target = "docs/implementation/semantic-models/01-fundamentals/"
        Description = "语义模型基础"
    },
    @{
        Pattern = "analysis/02_distributed_architecture/*.md"
        Target = "docs/implementation/semantic-models/02-distributed/"
        Description = "分布式架构"
    },
    @{
        Pattern = "analysis/21_rust_otlp_semantic_models/*.md"
        Target = "docs/implementation/semantic-models/rust-specific/"
        Description = "Rust 特定语义"
    },
    
    # 从 benchmarks/results/ 迁移报告
    @{
        Pattern = "benchmarks/results/*.md"
        Target = "docs/reports/benchmarks/"
        Description = "基准测试报告"
    },
    @{
        Pattern = "benchmarks/results/*.txt"
        Target = "docs/reports/benchmarks/raw-data/"
        Description = "原始基准数据"
    },
    
    # 从 docs/reports/ 迁移进度报告
    @{
        Pattern = "docs/reports/2025-10/*.md"
        Target = "docs/reports/progress/2025-10/"
        Description = "2025年10月进度报告"
    },
    
    # 从 otlp/docs/ 迁移 API 文档
    @{
        Pattern = "otlp/docs/architecture/*.md"
        Target = "docs/api/otlp/architecture/"
        Description = "OTLP 架构文档"
    },
    @{
        Pattern = "otlp/docs/guides/*.md"
        Target = "docs/guides/tutorials/otlp/"
        Description = "OTLP 教程"
    },
    
    # 迁移部署相关
    @{
        Pattern = "docker/*.md"
        Target = "docs/operations/deployment/docker/"
        Description = "Docker 部署文档"
    },
    @{
        Pattern = "otlp/deploy/*.md"
        Target = "docs/operations/deployment/kubernetes/"
        Description = "Kubernetes 部署文档"
    },
    
    # 研究文档
    @{
        Pattern = "analysis/23_quantum_inspired_observability/*.md"
        Target = "docs/research/quantum-observability/"
        Description = "量子启发的可观测性"
    },
    @{
        Pattern = "analysis/24_neuromorphic_monitoring/*.md"
        Target = "docs/research/neuromorphic-monitoring/"
        Description = "神经形态监控"
    },
    @{
        Pattern = "analysis/25_edge_ai_fusion/*.md"
        Target = "docs/research/ai-automation/"
        Description = "边缘AI融合"
    }
)

# 执行迁移
Write-Host "执行文档迁移..." -ForegroundColor Green
$totalMigrated = 0
$totalSkipped = 0

foreach ($migration in $migrations) {
    $pattern = $migration.Pattern
    $target = $migration.Target
    $description = $migration.Description
    
    Write-Host "`n  迁移: $description" -ForegroundColor Cyan
    Write-Host "    从: $pattern" -ForegroundColor Gray
    Write-Host "    到: $target" -ForegroundColor Gray
    
    # 确保目标目录存在
    if (-not (Test-Path $target)) {
        if (-not $DryRun) {
            New-Item -ItemType Directory -Path $target -Force | Out-Null
        }
    }
    
    # 查找匹配的文件
    $files = Get-ChildItem -Path $pattern -ErrorAction SilentlyContinue
    
    if ($files) {
        foreach ($file in $files) {
            $targetFile = Join-Path $target $file.Name
            
            if (Test-Path $targetFile) {
                Write-Host "    ⚠ 跳过（已存在）: $($file.Name)" -ForegroundColor Yellow
                $totalSkipped++
            } else {
                if ($DryRun) {
                    Write-Host "    → 将移动: $($file.Name)" -ForegroundColor Gray
                } else {
                    Copy-Item -Path $file.FullName -Destination $targetFile
                    Write-Host "    ✓ 已迁移: $($file.Name)" -ForegroundColor Green
                }
                $totalMigrated++
            }
        }
    } else {
        Write-Host "    ℹ 未找到匹配文件" -ForegroundColor DarkGray
    }
}

Write-Host ""
Write-Host "================================================" -ForegroundColor Cyan
Write-Host "迁移完成!" -ForegroundColor Green
Write-Host "  迁移文件数: $totalMigrated" -ForegroundColor Green
Write-Host "  跳过文件数: $totalSkipped" -ForegroundColor Yellow
Write-Host "================================================" -ForegroundColor Cyan
Write-Host ""

# 创建索引文件
Write-Host "创建文档索引..." -ForegroundColor Green

$readmeContent = @"
# OTLP Rust 文档中心

欢迎来到 OTLP Rust 项目文档中心！

## 📚 文档导航

### 🚀 快速开始
- [安装指南](guides/getting-started/installation.md)
- [第一个追踪](guides/getting-started/first-trace.md)
- [配置说明](guides/getting-started/configuration.md)

### 📖 教程
- [基础使用](guides/tutorials/01-basic-usage.md)
- [高级特性](guides/tutorials/02-advanced-features.md)
- [微服务集成](guides/tutorials/03-microservices.md)
- [生产部署](guides/tutorials/04-production-deployment.md)

### 🏗️ 架构设计
- [架构概览](architecture/overview.md)
- [Crate 设计](architecture/crate-design.md)
- [依赖关系图](architecture/dependency-graph.md)
- [模块组织](architecture/module-organization.md)

### 📚 API 参考
- [otlp-core API](api/otlp-core/)
- [otlp-proto API](api/otlp-proto/)
- [otlp-transport API](api/otlp-transport/)
- [otlp API](api/otlp/)
- [reliability API](api/reliability/)

### 🔧 操作指南
- [Docker 部署](operations/deployment/docker/)
- [Kubernetes 部署](operations/deployment/kubernetes/)
- [Prometheus 监控](operations/monitoring/prometheus.md)
- [Grafana 集成](operations/monitoring/grafana.md)

### 📊 报告和分析
- [基准测试报告](reports/benchmarks/)
- [性能分析](reports/performance/)
- [进度报告](reports/progress/)

### 🔬 研究探索
- [量子可观测性](research/quantum-observability/)
- [神经形态监控](research/neuromorphic-monitoring/)
- [AI 自动化](research/ai-automation/)

### 🤝 贡献指南
- [如何贡献](contributing/CONTRIBUTING.md)
- [代码风格](contributing/code-style.md)
- [测试规范](contributing/testing.md)

### 📖 参考资料
- [术语表](reference/glossary.md)
- [常见问题](reference/faq.md)
- [外部资源](reference/resources.md)

---

## 📝 文档结构

本文档库采用以下结构组织：

``````
docs/
├── architecture/       # 架构设计文档
├── guides/            # 用户指南和教程
├── api/               # API 参考文档
├── design/            # 设计决策和规范
├── implementation/    # 实现细节
├── operations/        # 运维文档
├── reports/           # 报告和分析
├── research/          # 研究探索
├── contributing/      # 贡献指南
└── reference/         # 参考资料
``````

## 🔍 搜索文档

使用 [mdBook](https://rust-lang.github.io/mdBook/) 构建的文档站点支持全文搜索。

在本地预览：
``````bash
cd docs/book
mdbook serve
``````

## 📝 文档贡献

发现文档问题或有改进建议？欢迎：
- 提交 [Issue](https://github.com/your-org/otlp-rust/issues)
- 发起 [Pull Request](https://github.com/your-org/otlp-rust/pulls)

---

**最后更新**: 2025-10-20  
**版本**: 1.0
"@

if (-not $DryRun) {
    $readmeContent | Out-File -FilePath "docs/README.md" -Encoding UTF8
    Write-Host "  ✓ 创建: docs/README.md" -ForegroundColor Green
}

Write-Host ""
Write-Host "================================================" -ForegroundColor Cyan
Write-Host "全部完成!" -ForegroundColor Green
Write-Host ""
if ($DryRun) {
    Write-Host "这是模拟运行。要实际执行，请运行:" -ForegroundColor Yellow
    Write-Host "  .\scripts\reorganize-docs.ps1" -ForegroundColor Cyan
} else {
    Write-Host "下一步:" -ForegroundColor Yellow
    Write-Host "  1. 查看 docs/ 目录" -ForegroundColor Cyan
    Write-Host "  2. 运行: cd docs/book && mdbook build" -ForegroundColor Cyan
    Write-Host "  3. 预览: cd docs/book && mdbook serve" -ForegroundColor Cyan
}
Write-Host "================================================" -ForegroundColor Cyan

