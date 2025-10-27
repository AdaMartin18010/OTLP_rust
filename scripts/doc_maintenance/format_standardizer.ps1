# Document Format Standardizer
# Scans and reports format inconsistencies in markdown documents

param(
    [string]$TargetDir = ".",
    [switch]$Fix = $false,
    [switch]$Report = $true
)

$ErrorActionPreference = "Stop"

Write-Host "`n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan
Write-Host "📋 Document Format Standardizer" -ForegroundColor Green
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━`n" -ForegroundColor Cyan

# Statistics
$stats = @{
    TotalFiles = 0
    LargeFiles = 0
    WithTOC = 0
    WithoutTOC = 0
    WithNumbering = 0
    WithoutNumbering = 0
    WithMetadata = 0
    WithoutMetadata = 0
    Issues = @()
}

# Check if a file has Table of Contents
function Test-HasTOC {
    param([string]$Content)
    return $Content -match '##\s*(Table of Contents|目录|📋\s*目录)'
}

# Check if a file has numbered sections
function Test-HasNumbering {
    param([string]$Content)
    return $Content -match '###?\s+\d+\.'
}

# Check if a file has metadata
function Test-HasMetadata {
    param([string]$Content)
    return $Content -match '\*\*版本\*\*:|>\s*\*\*版本\*\*:|Version:'
}

# Scan directory
Write-Host "🔍 Scanning directory: $TargetDir`n" -ForegroundColor Yellow

$mdFiles = Get-ChildItem -Path $TargetDir -Filter "*.md" -Recurse | Where-Object {
    $_.Name -ne "CHANGELOG.md" -and 
    $_.Name -ne "LICENSE.md" -and
    $_.Length -gt 1KB
}

$stats.TotalFiles = $mdFiles.Count

foreach ($file in $mdFiles) {
    $content = Get-Content $file.FullName -Raw
    $relativePath = $file.FullName.Replace($PWD, '.').Replace('\', '/')
    
    # Check if file is large enough to need TOC
    $isLarge = $file.Length -gt 5KB
    if ($isLarge) { $stats.LargeFiles++ }
    
    # Check TOC
    $hasTOC = Test-HasTOC $content
    if ($hasTOC) {
        $stats.WithTOC++
    } else {
        $stats.WithoutTOC++
        if ($isLarge) {
            $stats.Issues += @{
                File = $relativePath
                Issue = "Missing TOC"
                Severity = "Medium"
                Size = [math]::Round($file.Length / 1KB, 1)
            }
        }
    }
    
    # Check numbering
    $hasNumbering = Test-HasNumbering $content
    if ($hasNumbering) {
        $stats.WithNumbering++
    } else {
        $stats.WithoutNumbering++
    }
    
    # Check metadata
    $hasMetadata = Test-HasMetadata $content
    if ($hasMetadata) {
        $stats.WithMetadata++
    } else {
        $stats.WithoutMetadata++
        if ($isLarge) {
            $stats.Issues += @{
                File = $relativePath
                Issue = "Missing metadata"
                Severity = "Low"
                Size = [math]::Round($file.Length / 1KB, 1)
            }
        }
    }
}

# Report
if ($Report) {
    Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan
    Write-Host "📊 Format Analysis Report" -ForegroundColor Green
    Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━`n" -ForegroundColor Cyan
    
    Write-Host "📈 Statistics:" -ForegroundColor Yellow
    Write-Host "  Total Markdown Files: $($stats.TotalFiles)" -ForegroundColor White
    Write-Host "  Large Files (>5KB): $($stats.LargeFiles)" -ForegroundColor White
    Write-Host ""
    
    Write-Host "📋 Table of Contents:" -ForegroundColor Yellow
    Write-Host "  With TOC: $($stats.WithTOC) ($([math]::Round($stats.WithTOC / $stats.TotalFiles * 100, 1))%)" -ForegroundColor Green
    Write-Host "  Without TOC: $($stats.WithoutTOC) ($([math]::Round($stats.WithoutTOC / $stats.TotalFiles * 100, 1))%)" -ForegroundColor Red
    Write-Host ""
    
    Write-Host "🔢 Section Numbering:" -ForegroundColor Yellow
    Write-Host "  With Numbering: $($stats.WithNumbering) ($([math]::Round($stats.WithNumbering / $stats.TotalFiles * 100, 1))%)" -ForegroundColor Cyan
    Write-Host "  Without Numbering: $($stats.WithoutNumbering) ($([math]::Round($stats.WithoutNumbering / $stats.TotalFiles * 100, 1))%)" -ForegroundColor Cyan
    Write-Host ""
    
    Write-Host "📝 Metadata:" -ForegroundColor Yellow
    Write-Host "  With Metadata: $($stats.WithMetadata) ($([math]::Round($stats.WithMetadata / $stats.TotalFiles * 100, 1))%)" -ForegroundColor Green
    Write-Host "  Without Metadata: $($stats.WithoutMetadata) ($([math]::Round($stats.WithoutMetadata / $stats.TotalFiles * 100, 1))%)" -ForegroundColor Red
    Write-Host ""
    
    if ($stats.Issues.Count -gt 0) {
        Write-Host "⚠️  Issues Found: $($stats.Issues.Count)" -ForegroundColor Yellow
        Write-Host ""
        
        $mediumIssues = $stats.Issues | Where-Object { $_.Severity -eq "Medium" }
        $lowIssues = $stats.Issues | Where-Object { $_.Severity -eq "Low" }
        
        if ($mediumIssues.Count -gt 0) {
            Write-Host "  🟡 Medium Priority ($($mediumIssues.Count)):" -ForegroundColor Yellow
            foreach ($issue in $mediumIssues | Select-Object -First 10) {
                Write-Host "     • $($issue.File) - $($issue.Issue) ($($issue.Size) KB)" -ForegroundColor Gray
            }
            if ($mediumIssues.Count -gt 10) {
                Write-Host "     ... and $($mediumIssues.Count - 10) more" -ForegroundColor Gray
            }
            Write-Host ""
        }
        
        if ($lowIssues.Count -gt 0) {
            Write-Host "  🟢 Low Priority ($($lowIssues.Count)):" -ForegroundColor Cyan
            foreach ($issue in $lowIssues | Select-Object -First 5) {
                Write-Host "     • $($issue.File) - $($issue.Issue) ($($issue.Size) KB)" -ForegroundColor Gray
            }
            if ($lowIssues.Count -gt 5) {
                Write-Host "     ... and $($lowIssues.Count - 5) more" -ForegroundColor Gray
            }
        }
    } else {
        Write-Host "✅ No issues found!" -ForegroundColor Green
    }
    
    Write-Host "`n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan
    Write-Host "📋 Recommendations:" -ForegroundColor Yellow
    Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━`n" -ForegroundColor Cyan
    
    $tocPercentage = $stats.WithTOC / $stats.TotalFiles * 100
    if ($tocPercentage < 80) {
        Write-Host "  ⚠️  TOC coverage is low ($([math]::Round($tocPercentage, 1))%)" -ForegroundColor Yellow
        Write-Host "     → Add TOC to large files (>5KB)" -ForegroundColor Gray
        Write-Host ""
    }
    
    $metadataPercentage = $stats.WithMetadata / $stats.TotalFiles * 100
    if ($metadataPercentage < 50) {
        Write-Host "  ⚠️  Metadata coverage is low ($([math]::Round($metadataPercentage, 1))%)" -ForegroundColor Yellow
        Write-Host "     → Add version and date metadata to documents" -ForegroundColor Gray
        Write-Host ""
    }
    
    Write-Host "  📖 See: docs/00_INDEX/STANDARDS.md for format guidelines" -ForegroundColor Cyan
    Write-Host ""
}

Write-Host "✅ Scan complete!`n" -ForegroundColor Green

