# OTLP Rust 性能基准测试运行脚本 (PowerShell)
# 
# 用法:
#   .\scripts\run_benchmarks.ps1 [选项]
#
# 选项:
#   all             - 运行所有基准测试（默认）
#   quick           - 快速基准测试（降低采样）
#   core            - 仅核心功能基准测试
#   performance     - 仅性能优化基准测试
#   comprehensive   - 综合场景基准测试
#   compare <base>  - 与基线对比
#   ci              - CI 模式（保存结果）
#   report          - 生成性能报告
#   clean           - 清理基准测试结果
#   help            - 显示帮助信息

param(
    [Parameter(Position=0)]
    [string]$Command = "all",
    
    [Parameter(Position=1)]
    [string]$Baseline = ""
)

# 颜色输出函数
function Write-Info {
    param([string]$Message)
    Write-Host "[INFO] $Message" -ForegroundColor Blue
}

function Write-Success {
    param([string]$Message)
    Write-Host "[SUCCESS] $Message" -ForegroundColor Green
}

function Write-Warning {
    param([string]$Message)
    Write-Host "[WARNING] $Message" -ForegroundColor Yellow
}

function Write-ErrorMessage {
    param([string]$Message)
    Write-Host "[ERROR] $Message" -ForegroundColor Red
}

# 检查依赖
function Test-Dependencies {
    Write-Info "检查依赖..."
    
    if (-not (Get-Command cargo -ErrorAction SilentlyContinue)) {
        Write-ErrorMessage "未找到 cargo，请先安装 Rust 工具链"
        exit 1
    }
    
    Write-Success "依赖检查完成"
}

# 运行所有基准测试
function Invoke-AllBenchmarks {
    Write-Info "运行所有基准测试..."
    
    cargo bench --benches -- --save-baseline latest
    
    if ($LASTEXITCODE -eq 0) {
        Write-Success "所有基准测试完成"
        Write-Info "报告位置: target/criterion/report/index.html"
    } else {
        Write-ErrorMessage "基准测试失败"
        exit 1
    }
}

# 快速基准测试
function Invoke-QuickBenchmarks {
    Write-Info "运行快速基准测试..."
    
    cargo bench --benches -- --sample-size 10 --measurement-time 2
    
    if ($LASTEXITCODE -eq 0) {
        Write-Success "快速基准测试完成"
    } else {
        Write-ErrorMessage "基准测试失败"
        exit 1
    }
}

# 运行核心功能基准测试
function Invoke-CoreBenchmarks {
    Write-Info "运行核心功能基准测试..."
    
    cargo bench --bench otlp_benchmarks -- --save-baseline core-latest
    
    if ($LASTEXITCODE -eq 0) {
        Write-Success "核心功能基准测试完成"
    } else {
        Write-ErrorMessage "基准测试失败"
        exit 1
    }
}

# 运行性能优化基准测试
function Invoke-PerformanceBenchmarks {
    Write-Info "运行性能优化基准测试..."
    
    $benchmarks = @(
        "performance_benchmarks",
        "extended_simd_benchmarks",
        "memory_pool_benchmarks",
        "network_io_benchmarks",
        "resilience_benchmarks",
        "optimization_benchmarks"
    )
    
    foreach ($bench in $benchmarks) {
        Write-Info "运行 $bench..."
        cargo bench --bench $bench -- --save-baseline "$bench-latest"
        
        if ($LASTEXITCODE -ne 0) {
            Write-ErrorMessage "$bench 失败"
            exit 1
        }
    }
    
    Write-Success "性能优化基准测试完成"
}

# 运行综合场景基准测试
function Invoke-ComprehensiveBenchmarks {
    Write-Info "运行综合场景基准测试..."
    
    cargo bench --bench comprehensive_benchmarks -- --save-baseline comprehensive-latest
    
    if ($LASTEXITCODE -eq 0) {
        Write-Success "综合场景基准测试完成"
    } else {
        Write-ErrorMessage "基准测试失败"
        exit 1
    }
}

# 与基线对比
function Compare-WithBaseline {
    param([string]$BaselineName)
    
    if ([string]::IsNullOrEmpty($BaselineName)) {
        Write-ErrorMessage "请指定基线名称"
        exit 1
    }
    
    Write-Info "与基线 $BaselineName 对比..."
    
    cargo bench --benches -- --baseline $BaselineName
    
    if ($LASTEXITCODE -eq 0) {
        Write-Success "对比完成"
    } else {
        Write-ErrorMessage "对比失败"
        exit 1
    }
}

# CI 模式
function Invoke-CIBenchmarks {
    Write-Info "运行 CI 模式基准测试..."
    
    # 获取当前提交哈希或时间戳
    if ($env:CI_COMMIT_SHA) {
        $baseline = "ci-$($env:CI_COMMIT_SHA)"
    } elseif ($env:GITHUB_SHA) {
        $baseline = "ci-$($env:GITHUB_SHA)"
    } else {
        $baseline = "ci-$(Get-Date -Format 'yyyyMMdd-HHmmss')"
    }
    
    Write-Info "基线名称: $baseline"
    
    # 运行基准测试并保存基线
    cargo bench --benches -- --save-baseline $baseline
    
    if ($LASTEXITCODE -ne 0) {
        Write-ErrorMessage "基准测试失败"
        exit 1
    }
    
    # 生成报告
    Write-Info "生成报告..."
    
    # 创建结果目录
    $resultsDir = "benchmark-results"
    if (-not (Test-Path $resultsDir)) {
        New-Item -ItemType Directory -Path $resultsDir | Out-Null
    }
    
    # 复制报告到结果目录
    if (Test-Path "target/criterion") {
        Copy-Item -Path "target/criterion" -Destination $resultsDir -Recurse -Force
    }
    
    Write-Success "CI 基准测试完成"
    Write-Info "结果位置: $resultsDir/"
}

# 生成性能报告
function New-PerformanceReport {
    Write-Info "生成性能报告..."
    
    $reportPath = "target/criterion/report/index.html"
    
    if (Test-Path $reportPath) {
        # 在默认浏览器中打开报告
        Start-Process $reportPath
        Write-Success "性能报告已打开"
    } else {
        Write-Warning "报告不存在: $reportPath"
        Write-Info "请先运行基准测试"
    }
}

# 清理基准测试结果
function Clear-Benchmarks {
    Write-Info "清理基准测试结果..."
    
    if (Test-Path "target/criterion") {
        Remove-Item -Path "target/criterion" -Recurse -Force
        Write-Success "清理完成"
    } else {
        Write-Warning "没有需要清理的结果"
    }
}

# 显示帮助信息
function Show-Help {
    $helpText = @"
OTLP Rust 性能基准测试运行脚本

用法:
    .\scripts\run_benchmarks.ps1 [选项]

选项:
    all             运行所有基准测试（默认）
    quick           快速基准测试（降低采样）
    core            仅核心功能基准测试
    performance     仅性能优化基准测试
    comprehensive   综合场景基准测试
    compare <base>  与指定基线对比
    ci              CI 模式（保存结果）
    report          生成性能报告
    clean           清理基准测试结果
    help            显示帮助信息

示例:
    # 运行所有基准测试
    .\scripts\run_benchmarks.ps1 all

    # 快速基准测试
    .\scripts\run_benchmarks.ps1 quick

    # 与主分支对比
    .\scripts\run_benchmarks.ps1 compare main

    # CI 模式
    .\scripts\run_benchmarks.ps1 ci

    # 生成报告
    .\scripts\run_benchmarks.ps1 report

    # 清理结果
    .\scripts\run_benchmarks.ps1 clean
"@
    
    Write-Host $helpText
}

# 主函数
function Main {
    Test-Dependencies
    
    switch ($Command.ToLower()) {
        "all" {
            Invoke-AllBenchmarks
        }
        "quick" {
            Invoke-QuickBenchmarks
        }
        "core" {
            Invoke-CoreBenchmarks
        }
        "performance" {
            Invoke-PerformanceBenchmarks
        }
        "comprehensive" {
            Invoke-ComprehensiveBenchmarks
        }
        "compare" {
            Compare-WithBaseline -BaselineName $Baseline
        }
        "ci" {
            Invoke-CIBenchmarks
        }
        "report" {
            New-PerformanceReport
        }
        "clean" {
            Clear-Benchmarks
        }
        "help" {
            Show-Help
        }
        default {
            Write-ErrorMessage "未知命令: $Command"
            Show-Help
            exit 1
        }
    }
}

# 运行主函数
Main

