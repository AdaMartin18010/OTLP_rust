# 完整构建脚本 (PowerShell)
# 用于构建、测试和检查整个项目

Write-Host "==========================================" -ForegroundColor Cyan
Write-Host "  🏗️  完整构建和检查" -ForegroundColor Cyan
Write-Host "==========================================" -ForegroundColor Cyan
Write-Host ""

$ErrorActionPreference = "Stop"

# 1. 格式化检查
Write-Host "1️⃣  检查代码格式化..." -ForegroundColor Green
cargo fmt --all -- --check
if ($LASTEXITCODE -ne 0) {
    Write-Host "⚠️  代码格式化不一致，运行 cargo fmt --all 修复" -ForegroundColor Yellow
    exit 1
}

# 2. Clippy 检查
Write-Host "2️⃣  运行 Clippy 检查..." -ForegroundColor Green
cargo clippy --workspace --all-targets --all-features -- -D warnings

# 3. 编译检查
Write-Host "3️⃣  编译检查..." -ForegroundColor Green
cargo check --workspace --all-features

# 4. 运行测试
Write-Host "4️⃣  运行测试..." -ForegroundColor Green
cargo test --workspace --all-features

# 5. 文档检查
Write-Host "5️⃣  检查文档..." -ForegroundColor Green
cargo doc --workspace --all-features --no-deps

Write-Host ""
Write-Host "✅ 所有检查通过！" -ForegroundColor Green
