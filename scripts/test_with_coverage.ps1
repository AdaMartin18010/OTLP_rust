# 测试覆盖率脚本 (PowerShell)
# 用于运行测试并生成覆盖率报告

Write-Host "==========================================" -ForegroundColor Cyan
Write-Host "  🧪 运行测试并生成覆盖率报告" -ForegroundColor Cyan
Write-Host "==========================================" -ForegroundColor Cyan
Write-Host ""

# 检查是否安装了 cargo-llvm-cov
$cargoLlcov = Get-Command cargo-llvm-cov -ErrorAction SilentlyContinue
if (-not $cargoLlcov) {
    Write-Host "⚠️  cargo-llvm-cov 未安装" -ForegroundColor Yellow
    Write-Host "安装命令: cargo install cargo-llvm-cov"
    Write-Host ""
    Write-Host "使用 cargo test 代替..." -ForegroundColor Yellow
    cargo test --workspace --all-features
    exit 0
}

# 运行测试
Write-Host "📋 运行测试..." -ForegroundColor Green
cargo test --workspace --all-features

# 生成覆盖率报告
Write-Host ""
Write-Host "📊 生成覆盖率报告..." -ForegroundColor Green
cargo llvm-cov --workspace --all-features --lcov --output-path lcov.info

# 生成 HTML 报告
Write-Host "📄 生成 HTML 报告..." -ForegroundColor Green
cargo llvm-cov --workspace --all-features --html --output-dir coverage/

# 显示覆盖率摘要
Write-Host ""
Write-Host "✅ 覆盖率报告生成完成！" -ForegroundColor Green
Write-Host ""
Write-Host "📁 报告位置:" -ForegroundColor Cyan
Write-Host "  - LCOV 格式: lcov.info" -ForegroundColor White
Write-Host "  - HTML 格式: coverage/index.html" -ForegroundColor White
Write-Host ""
Write-Host "💡 查看 HTML 报告:" -ForegroundColor Cyan
Write-Host "  Start-Process coverage/index.html  # Windows PowerShell" -ForegroundColor White
