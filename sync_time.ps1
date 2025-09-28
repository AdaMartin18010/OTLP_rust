# ===========================================
# 系统时间同步脚本 - 2025年1月最新版本
# ===========================================
# 功能：自动同步系统时间到标准时间服务器
# 特点：支持多时间服务器、连接测试、错误处理
# 要求：需要管理员权限运行
# 兼容：Windows 10/11, PowerShell 5.1+
# 更新时间：2025年1月
# ===========================================

# ========== 参数配置 ==========
# 时间服务器列表（按优先级排序）
# 1. ntp.aliyun.com - 阿里云NTP服务器（国内访问快）
# 2. time.windows.com - 微软官方时间服务器
# 3. cn.pool.ntp.org - 中国NTP服务器池
param(
    [string[]]$TimeServers = @("ntp.aliyun.com", "time.windows.com", "cn.pool.ntp.org"),
    [switch]$Force = $false  # 强制同步标志（暂未实现）
)

# ========== 权限检查函数 ==========
# 检查当前用户是否具有管理员权限
# 返回：$true 如果有管理员权限，$false 否则
function Test-Administrator {
    $currentUser = [Security.Principal.WindowsIdentity]::GetCurrent()
    $principal = New-Object Security.Principal.WindowsPrincipal($currentUser)
    return $principal.IsInRole([Security.Principal.WindowsBuiltInRole]::Administrator)
}

# ========== 时间状态显示函数 ==========
# 显示当前系统时间状态和同步信息
# 包括：系统时间、时间服务状态、同步配置等
function Show-TimeStatus {
    Write-Host "=== 当前时间状态 ===" -ForegroundColor Green
    Write-Host "系统时间: $(Get-Date)" -ForegroundColor Yellow
    Write-Host ""
    
    try {
        # 查询Windows时间服务状态
        $status = w32tm /query /status
        Write-Host "时间同步状态:" -ForegroundColor Cyan
        $status | ForEach-Object { Write-Host "  $_" -ForegroundColor White }
    } catch {
        Write-Host "无法获取时间同步状态: $_" -ForegroundColor Red
    }
    Write-Host ""
}

# ========== 时间服务器配置函数 ==========
# 配置Windows时间服务使用指定的时间服务器
# 参数：$Servers - 时间服务器列表
# 返回：$true 配置成功，$false 配置失败
function Set-TimeServers {
    param([string[]]$Servers)
    
    Write-Host "=== 配置时间服务器 ===" -ForegroundColor Green
    $serverList = $Servers -join ","
    Write-Host "使用时间服务器: $serverList" -ForegroundColor Yellow
    
    try {
        # 配置时间服务器参数说明：
        # /manualpeerlist: 手动指定对等服务器列表
        # /syncfromflags:manual 手动同步标志
        # /reliable:yes 标记为可靠时间源
        # /update 立即更新配置
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
        
        # 重启时间服务以应用新配置
        Write-Host "重启时间服务..." -ForegroundColor Yellow
        net stop w32time | Out-Null
        Start-Sleep -Seconds 2  # 等待服务完全停止
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

# ========== 时间同步函数 ==========
# 执行时间同步操作
# 返回：$true 同步成功，$false 同步失败
function Sync-Time {
    Write-Host "=== 同步时间 ===" -ForegroundColor Green
    
    try {
        # 立即执行时间同步
        # w32tm /resync 强制时间服务立即同步
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
        
        # 等待同步操作完成
        # 给时间服务足够的时间来完成同步
        Write-Host "等待同步完成..." -ForegroundColor Yellow
        Start-Sleep -Seconds 5
        
        return $true
    } catch {
        Write-Host "✗ 同步时间时出错: $_" -ForegroundColor Red
        return $false
    }
}

# ========== 时间服务器连接测试函数 ==========
# 测试指定时间服务器的连接性和响应时间
# 参数：$Server - 时间服务器地址
# 返回：$true 连接成功，$false 连接失败
function Test-TimeServer {
    param([string]$Server)
    
    try {
        Write-Host "测试时间服务器: $Server" -ForegroundColor Yellow
        
        # 使用 w32tm /stripchart 测试服务器连接
        # /computer: 指定要测试的服务器
        # /samples:1 只取一个样本（快速测试）
        $result = w32tm /stripchart /computer:$Server /samples:1 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✓ $Server 连接正常" -ForegroundColor Green
            # 解析并显示延迟信息（如果可用）
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

# ========== 主函数 ==========
# 脚本主执行流程
# 1. 权限检查
# 2. 显示当前时间状态
# 3. 测试时间服务器连接
# 4. 配置时间服务器
# 5. 执行时间同步
# 6. 显示同步后状态
function Main {
    # 显示脚本标题和版本信息
    Write-Host "===========================================" -ForegroundColor Cyan
    Write-Host "           系统时间同步工具" -ForegroundColor Cyan
    Write-Host "           版本: 2025.01" -ForegroundColor Cyan
    Write-Host "===========================================" -ForegroundColor Cyan
    Write-Host ""
    
    # 步骤1：检查管理员权限
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
    
    # 步骤2：显示当前时间状态
    Write-Host "步骤 1/5: 检查当前时间状态" -ForegroundColor Magenta
    Show-TimeStatus
    
    # 步骤3：测试时间服务器连接
    Write-Host "步骤 2/5: 测试时间服务器连接" -ForegroundColor Magenta
    Write-Host "=== 测试时间服务器连接 ===" -ForegroundColor Green
    $availableServers = @()
    foreach ($server in $TimeServers) {
        if (Test-TimeServer -Server $server) {
            $availableServers += $server
        }
    }
    
    if ($availableServers.Count -eq 0) {
        Write-Host "✗ 没有可用的时间服务器" -ForegroundColor Red
        Write-Host "请检查网络连接或尝试其他时间服务器" -ForegroundColor Yellow
        return
    }
    
    Write-Host ""
    
    # 步骤4：配置时间服务器
    Write-Host "步骤 3/5: 配置时间服务器" -ForegroundColor Magenta
    if (-not (Set-TimeServers -Servers $availableServers)) {
        Write-Host "✗ 配置时间服务器失败" -ForegroundColor Red
        return
    }
    
    Write-Host ""
    
    # 步骤5：执行时间同步
    Write-Host "步骤 4/5: 执行时间同步" -ForegroundColor Magenta
    if (-not (Sync-Time)) {
        Write-Host "✗ 时间同步失败" -ForegroundColor Red
        return
    }
    
    Write-Host ""
    
    # 步骤6：显示最终状态
    Write-Host "步骤 5/5: 验证同步结果" -ForegroundColor Magenta
    Write-Host "=== 同步后状态 ===" -ForegroundColor Green
    Show-TimeStatus
    
    # 显示完成信息
    Write-Host "===========================================" -ForegroundColor Cyan
    Write-Host "           时间同步完成！" -ForegroundColor Green
    Write-Host "           系统时间已与标准时间同步" -ForegroundColor Green
    Write-Host "===========================================" -ForegroundColor Cyan
}

# ========== 脚本入口点 ==========
# 脚本执行入口，调用主函数开始时间同步流程
Main
