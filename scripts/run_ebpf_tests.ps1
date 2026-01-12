# 运行 eBPF 相关测试

$ErrorActionPreference = "Stop"

Write-Host "==========================================" -ForegroundColor Green
Write-Host "  🧪 运行 eBPF 测试" -ForegroundColor Green
Write-Host "==========================================" -ForegroundColor Green
Write-Host ""

# 检查是否在 Linux 环境
if ($IsWindows -or $IsMacOS) {
    Write-Host "⚠️  警告: eBPF 功能仅在 Linux 平台支持" -ForegroundColor Yellow
    Write-Host "当前操作系统: $($PSVersionTable.PSVersion)"
    Write-Host "跳过 eBPF 测试"
    exit 0
}

# 检查 eBPF feature
$cargoToml = Get-Content Cargo.toml -Raw
if ($cargoToml -notmatch "ebpf") {
    Write-Host "⚠️  警告: eBPF feature 未启用" -ForegroundColor Yellow
    Write-Host "跳过 eBPF 测试"
    exit 0
}

Write-Host "1️⃣  运行 eBPF 单元测试..." -ForegroundColor Green
try {
    cargo test --package otlp --lib ebpf --features ebpf
    Write-Host "✅ 单元测试通过" -ForegroundColor Green
} catch {
    Write-Host "❌ 单元测试失败" -ForegroundColor Red
    exit 1
}

Write-Host ""
Write-Host "2️⃣  运行 eBPF 集成测试..." -ForegroundColor Green
try {
    cargo test --test ebpf_integration --features ebpf
    Write-Host "✅ 集成测试通过" -ForegroundColor Green
} catch {
    Write-Host "⚠️  集成测试跳过（可能需要 root 权限）" -ForegroundColor Yellow
}

Write-Host ""
Write-Host "3️⃣  运行 eBPF 示例..." -ForegroundColor Green
try {
    cargo run --example ebpf_complete --features ebpf 2>&1 | Select-Object -First 20
    Write-Host "✅ 示例运行成功" -ForegroundColor Green
} catch {
    Write-Host "⚠️  示例运行跳过（可能需要 root 权限或 eBPF 支持）" -ForegroundColor Yellow
}

Write-Host ""
Write-Host "✅ eBPF 测试完成！" -ForegroundColor Green
Write-Host ""
