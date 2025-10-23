# OTLP Rust Project - Module Analysis Script (PowerShell)
# Date: 2025-10-23
# Description: Analyzes current module structure and identifies duplicates

Write-Host "🔍 OTLP Rust Project - Module Analysis" -ForegroundColor Cyan
Write-Host "=======================================" -ForegroundColor Cyan
Write-Host ""

$ErrorActionPreference = "Stop"

# Check if we're in the right directory
if (-not (Test-Path "Cargo.toml")) {
    Write-Host "Error: Cargo.toml not found. Please run this script from the project root." -ForegroundColor Red
    exit 1
}

# Function to count lines in a file
function Get-LineCount {
    param($file)
    if (Test-Path $file) {
        return (Get-Content $file | Measure-Object -Line).Lines
    }
    return 0
}

# 1. Performance modules analysis
Write-Host "📦 Analyzing performance-related modules..." -ForegroundColor Yellow
Write-Host ""

$performanceModules = @(
    "crates/otlp/src/performance",
    "crates/otlp/src/advanced_performance.rs",
    "crates/otlp/src/performance_enhancements.rs",
    "crates/otlp/src/performance_monitoring.rs",
    "crates/otlp/src/performance_optimization_advanced.rs",
    "crates/otlp/src/performance_optimized.rs",
    "crates/otlp/src/performance_optimizer.rs"
)

$totalLines = 0
$existingModules = @()

foreach ($module in $performanceModules) {
    if (Test-Path $module) {
        if (Test-Path $module -PathType Container) {
            # Directory
            $lines = (Get-ChildItem -Path $module -Recurse -Include "*.rs" | Get-Content | Measure-Object -Line).Lines
            Write-Host "  ✓ $module (directory): $lines lines" -ForegroundColor Green
            $existingModules += $module
            $totalLines += $lines
        } else {
            # File
            $lines = Get-LineCount $module
            Write-Host "  ✓ $module (file): $lines lines" -ForegroundColor Green
            $existingModules += $module
            $totalLines += $lines
        }
    } else {
        Write-Host "  ✗ $module (not found)" -ForegroundColor Gray
    }
}

Write-Host ""
Write-Host "Performance modules summary:" -ForegroundColor Cyan
Write-Host "  Total modules found: $($existingModules.Count)" -ForegroundColor White
Write-Host "  Total lines of code: $totalLines" -ForegroundColor White
Write-Host ""

# 2. Project statistics
Write-Host "📊 Project statistics..." -ForegroundColor Yellow
Write-Host ""

$rustFiles = Get-ChildItem -Path . -Recurse -Include "*.rs" -Exclude "target" | Where-Object { $_.FullName -notmatch "\\target\\" }
$rustFilesCount = $rustFiles.Count
$rustLinesTotal = ($rustFiles | Get-Content | Measure-Object -Line).Lines

$mdFiles = Get-ChildItem -Path . -Recurse -Include "*.md"
$mdFilesCount = $mdFiles.Count

Write-Host "  Rust files: $rustFilesCount" -ForegroundColor White
Write-Host "  Total lines of Rust code: $rustLinesTotal" -ForegroundColor White
Write-Host "  Markdown files: $mdFilesCount" -ForegroundColor White
Write-Host ""

# 3. Module imports analysis
Write-Host "🔍 Analyzing module imports in lib.rs..." -ForegroundColor Yellow
Write-Host ""

$libRsPath = "crates/otlp/src/lib.rs"
if (Test-Path $libRsPath) {
    $libRsContent = Get-Content $libRsPath
    $moduleDeclarations = $libRsContent | Select-String -Pattern "^\s*pub\s+mod\s+\w+" -AllMatches
    
    Write-Host "  Found $($moduleDeclarations.Count) public module declarations" -ForegroundColor White
    Write-Host ""
    
    Write-Host "  Modules declared:" -ForegroundColor Cyan
    foreach ($match in $moduleDeclarations) {
        Write-Host "    - $($match.Line.Trim())" -ForegroundColor Gray
    }
} else {
    Write-Host "  lib.rs not found!" -ForegroundColor Red
}
Write-Host ""

# 4. Unrelated modules check
Write-Host "🔍 Checking for unrelated modules..." -ForegroundColor Yellow
Write-Host ""

$unrelatedModules = @(
    "crates/otlp/src/ai_ml",
    "crates/otlp/src/blockchain",
    "crates/otlp/src/edge_computing"
)

$foundUnrelated = @()
foreach ($module in $unrelatedModules) {
    if (Test-Path $module) {
        Write-Host "  ⚠️  Found: $module (should be removed)" -ForegroundColor Yellow
        $foundUnrelated += $module
    } else {
        Write-Host "  ✓ $module (not found, good!)" -ForegroundColor Green
    }
}

Write-Host ""

# 5. Generate recommendation report
Write-Host "=====================================" -ForegroundColor Cyan
Write-Host "📋 Recommendations" -ForegroundColor Cyan
Write-Host "=====================================" -ForegroundColor Cyan
Write-Host ""

if ($existingModules.Count -gt 2) {
    Write-Host "🔴 High Priority: Merge performance modules" -ForegroundColor Red
    Write-Host "  Found $($existingModules.Count) performance-related modules" -ForegroundColor White
    Write-Host "  Recommendation: Consolidate into crates/otlp/src/performance/" -ForegroundColor White
    Write-Host ""
}

if ($foundUnrelated.Count -gt 0) {
    Write-Host "🔴 High Priority: Remove unrelated modules" -ForegroundColor Red
    Write-Host "  Found $($foundUnrelated.Count) unrelated modules:" -ForegroundColor White
    foreach ($module in $foundUnrelated) {
        Write-Host "    - $module" -ForegroundColor White
    }
    Write-Host "  Recommendation: Delete these modules" -ForegroundColor White
    Write-Host ""
}

if ($rustFilesCount -gt 100) {
    Write-Host "🟡 Medium Priority: Simplify codebase" -ForegroundColor Yellow
    Write-Host "  Current: $rustFilesCount Rust files" -ForegroundColor White
    Write-Host "  Target: <60 files" -ForegroundColor White
    Write-Host "  Recommendation: Remove unused modules and merge duplicates" -ForegroundColor White
    Write-Host ""
}

if ($mdFilesCount -gt 500) {
    Write-Host "🟡 Medium Priority: Clean up documentation" -ForegroundColor Yellow
    Write-Host "  Current: $mdFilesCount Markdown files" -ForegroundColor White
    Write-Host "  Target: <300 files" -ForegroundColor White
    Write-Host "  Recommendation: Remove theoretical docs and duplicates" -ForegroundColor White
    Write-Host ""
}

Write-Host "=====================================" -ForegroundColor Cyan
Write-Host "✅ Analysis complete!" -ForegroundColor Green
Write-Host "=====================================" -ForegroundColor Cyan
Write-Host ""
Write-Host "Next steps:" -ForegroundColor Cyan
Write-Host "  1. Run: ./scripts/cleanup_phase1.sh (on Linux/macOS)" -ForegroundColor White
Write-Host "     Or manually delete identified modules (on Windows)" -ForegroundColor White
Write-Host "  2. Update lib.rs to remove deleted module exports" -ForegroundColor White
Write-Host "  3. Run: cargo check --workspace" -ForegroundColor White
Write-Host "  4. Commit changes" -ForegroundColor White
Write-Host ""

# Save report to file
$reportFile = "module_analysis_report.txt"
$report = @"
OTLP Rust Project - Module Analysis Report
Generated: $(Get-Date)
==========================================

Performance Modules:
- Found: $($existingModules.Count) modules
- Total lines: $totalLines

Project Statistics:
- Rust files: $rustFilesCount
- Total Rust lines: $rustLinesTotal
- Markdown files: $mdFilesCount

Unrelated Modules:
$($foundUnrelated -join "`n")

Recommendations:
$( if ($existingModules.Count -gt 2) { "- Merge performance modules`n" } )
$( if ($foundUnrelated.Count -gt 0) { "- Remove unrelated modules`n" } )
$( if ($rustFilesCount -gt 100) { "- Simplify codebase`n" } )
$( if ($mdFilesCount -gt 500) { "- Clean up documentation`n" } )
"@

$report | Out-File -FilePath $reportFile -Encoding UTF8
Write-Host "Report saved to: $reportFile" -ForegroundColor Cyan

