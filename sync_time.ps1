# 系统时间同步脚本
# 需要管理员权限运行

param(
    [string[]]$TimeServers = @("ntp.aliyun.com", "time.windows.com", "cn.pool.ntp.org"),
    [switch]$Force = $false
)

# 检查管理员权限
function Test-Administrator {
    $currentUser = [Security.Principal.WindowsIdentity]::GetCurrent()
    $principal = New-Object Security.Principal.WindowsPrincipal($currentUser)
    return $principal.IsInRole([Security.Principal.WindowsBuiltInRole]::Administrator)
}

# 显示当前时间状态
function Show-TimeStatus {
    Write-Host "=== 当前时间状态 ===" -ForegroundColor Green
    Write-Host "系统时间: $(Get-Date)" -ForegroundColor Yellow
    Write-Host ""
    
    try {
        $status = w32tm /query /status
        Write-Host "时间同步状态:" -ForegroundColor Cyan
        $status | ForEach-Object { Write-Host "  $_" -ForegroundColor White }
    } catch {
        Write-Host "无法获取时间同步状态: $_" -ForegroundColor Red
    }
    Write-Host ""
}

# 配置时间服务器
function Set-TimeServers {
    param([string[]]$Servers)
    
    Write-Host "=== 配置时间服务器 ===" -ForegroundColor Green
    $serverList = $Servers -join ","
    Write-Host "使用时间服务器: $serverList" -ForegroundColor Yellow
    
    try {
        # 配置时间服务器
        $result = w32tm /config /manualpeerlist:$serverList /syncfromflags:manual /reliable:yes /update 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✓ 时间服务器配置成功" -ForegroundColor Green
        } else {
            Write-Host "✗ 时间服务器配置失败" -ForegroundColor Red
            if ($result) {
                Write-Host "  错误信息: $($result -join ' ')" -ForegroundColor DarkRed
            }
            return $false
        }
        
        # 重启时间服务
        Write-Host "重启时间服务..." -ForegroundColor Yellow
        net stop w32time | Out-Null
        Start-Sleep -Seconds 2
        net start w32time | Out-Null
        
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✓ 时间服务重启成功" -ForegroundColor Green
        } else {
            Write-Host "✗ 时间服务重启失败" -ForegroundColor Red
            return $false
        }
        
        return $true
    } catch {
        Write-Host "✗ 配置时间服务器时出错: $_" -ForegroundColor Red
        return $false
    }
}

# 同步时间
function Sync-Time {
    Write-Host "=== 同步时间 ===" -ForegroundColor Green
    
    try {
        # 立即同步
        $result = w32tm /resync 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✓ 时间同步成功" -ForegroundColor Green
        } else {
            Write-Host "✗ 时间同步失败" -ForegroundColor Red
            if ($result) {
                Write-Host "  错误信息: $($result -join ' ')" -ForegroundColor DarkRed
            }
            return $false
        }
        
        # 等待同步完成
        Write-Host "等待同步完成..." -ForegroundColor Yellow
        Start-Sleep -Seconds 5
        
        return $true
    } catch {
        Write-Host "✗ 同步时间时出错: $_" -ForegroundColor Red
        return $false
    }
}

# 测试时间服务器连接
function Test-TimeServer {
    param([string]$Server)
    
    try {
        Write-Host "测试时间服务器: $Server" -ForegroundColor Yellow
        $result = w32tm /stripchart /computer:$Server /samples:1 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✓ $Server 连接正常" -ForegroundColor Green
            # 可选：显示延迟信息
            if ($result -match "延迟: (\d+\.?\d*)ms") {
                Write-Host "  延迟: $($matches[1])ms" -ForegroundColor Gray
            }
            return $true
        } else {
            Write-Host "✗ $Server 连接失败" -ForegroundColor Red
            if ($result) {
                Write-Host "  错误信息: $($result -join ' ')" -ForegroundColor DarkRed
            }
            return $false
        }
    } catch {
        Write-Host "✗ 测试 $Server 时出错: $_" -ForegroundColor Red
        return $false
    }
}

# 主函数
function Main {
    Write-Host "===========================================" -ForegroundColor Cyan
    Write-Host "           系统时间同步工具" -ForegroundColor Cyan
    Write-Host "===========================================" -ForegroundColor Cyan
    Write-Host ""
    
    # 检查管理员权限
    if (-not (Test-Administrator)) {
        Write-Host "✗ 此脚本需要管理员权限运行" -ForegroundColor Red
        Write-Host "请以管理员身份运行 PowerShell，然后重新执行此脚本" -ForegroundColor Yellow
        Write-Host ""
        Write-Host "或者运行以下命令:" -ForegroundColor Yellow
        Write-Host "Start-Process PowerShell -Verb RunAs -ArgumentList '-File $PSCommandPath'" -ForegroundColor White
        return
    }
    
    Write-Host "✓ 管理员权限检查通过" -ForegroundColor Green
    Write-Host ""
    
    # 显示当前状态
    Show-TimeStatus
    
    # 测试时间服务器
    Write-Host "=== 测试时间服务器连接 ===" -ForegroundColor Green
    $availableServers = @()
    foreach ($server in $TimeServers) {
        if (Test-TimeServer -Server $server) {
            $availableServers += $server
        }
    }
    
    if ($availableServers.Count -eq 0) {
        Write-Host "✗ 没有可用的时间服务器" -ForegroundColor Red
        return
    }
    
    Write-Host ""
    
    # 配置时间服务器
    if (-not (Set-TimeServers -Servers $availableServers)) {
        Write-Host "✗ 配置时间服务器失败" -ForegroundColor Red
        return
    }
    
    Write-Host ""
    
    # 同步时间
    if (-not (Sync-Time)) {
        Write-Host "✗ 时间同步失败" -ForegroundColor Red
        return
    }
    
    Write-Host ""
    
    # 显示最终状态
    Write-Host "=== 同步后状态 ===" -ForegroundColor Green
    Show-TimeStatus
    
    Write-Host "===========================================" -ForegroundColor Cyan
    Write-Host "           时间同步完成！" -ForegroundColor Green
    Write-Host "===========================================" -ForegroundColor Cyan
}

# 运行主函数
Main
