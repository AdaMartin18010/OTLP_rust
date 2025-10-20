#!/bin/bash
# OTLP Rust 性能基准测试运行脚本
# 
# 用法:
#   ./scripts/run_benchmarks.sh [选项]
#
# 选项:
#   all             - 运行所有基准测试（默认）
#   quick           - 快速基准测试（降低采样）
#   core            - 仅核心功能基准测试
#   performance     - 仅性能优化基准测试
#   comprehensive   - 综合场景基准测试
#   compare <base>  - 与基线对比
#   ci              - CI 模式（保存结果）

set -e

# 颜色输出
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# 打印带颜色的消息
print_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

print_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

print_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

print_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# 检查依赖
check_dependencies() {
    print_info "检查依赖..."
    
    if ! command -v cargo &> /dev/null; then
        print_error "未找到 cargo，请先安装 Rust 工具链"
        exit 1
    fi
    
    print_success "依赖检查完成"
}

# 运行所有基准测试
run_all_benchmarks() {
    print_info "运行所有基准测试..."
    
    cargo bench --benches -- --save-baseline latest
    
    print_success "所有基准测试完成"
    print_info "报告位置: target/criterion/report/index.html"
}

# 快速基准测试
run_quick_benchmarks() {
    print_info "运行快速基准测试..."
    
    cargo bench --benches -- --sample-size 10 --measurement-time 2
    
    print_success "快速基准测试完成"
}

# 运行核心功能基准测试
run_core_benchmarks() {
    print_info "运行核心功能基准测试..."
    
    cargo bench --bench otlp_benchmarks -- --save-baseline core-latest
    
    print_success "核心功能基准测试完成"
}

# 运行性能优化基准测试
run_performance_benchmarks() {
    print_info "运行性能优化基准测试..."
    
    cargo bench --bench performance_benchmarks -- --save-baseline perf-latest
    cargo bench --bench extended_simd_benchmarks -- --save-baseline simd-latest
    cargo bench --bench memory_pool_benchmarks -- --save-baseline pool-latest
    cargo bench --bench network_io_benchmarks -- --save-baseline network-latest
    cargo bench --bench resilience_benchmarks -- --save-baseline resilience-latest
    cargo bench --bench optimization_benchmarks -- --save-baseline opt-latest
    
    print_success "性能优化基准测试完成"
}

# 运行综合场景基准测试
run_comprehensive_benchmarks() {
    print_info "运行综合场景基准测试..."
    
    cargo bench --bench comprehensive_benchmarks -- --save-baseline comprehensive-latest
    
    print_success "综合场景基准测试完成"
}

# 与基线对比
compare_with_baseline() {
    local baseline=$1
    
    if [ -z "$baseline" ]; then
        print_error "请指定基线名称"
        exit 1
    fi
    
    print_info "与基线 $baseline 对比..."
    
    cargo bench --benches -- --baseline "$baseline"
    
    print_success "对比完成"
}

# CI 模式
run_ci_benchmarks() {
    print_info "运行 CI 模式基准测试..."
    
    # 获取当前分支或提交哈希
    if [ -n "$CI_COMMIT_SHA" ]; then
        baseline="ci-$CI_COMMIT_SHA"
    elif [ -n "$GITHUB_SHA" ]; then
        baseline="ci-$GITHUB_SHA"
    else
        baseline="ci-$(date +%Y%m%d-%H%M%S)"
    fi
    
    print_info "基线名称: $baseline"
    
    # 运行基准测试并保存基线
    cargo bench --benches -- --save-baseline "$baseline"
    
    # 生成报告
    print_info "生成报告..."
    
    # 创建结果目录
    mkdir -p benchmark-results
    
    # 复制报告到结果目录
    cp -r target/criterion benchmark-results/
    
    print_success "CI 基准测试完成"
    print_info "结果位置: benchmark-results/"
}

# 生成性能报告
generate_performance_report() {
    print_info "生成性能报告..."
    
    # 打开 HTML 报告
    if command -v xdg-open &> /dev/null; then
        xdg-open target/criterion/report/index.html
    elif command -v open &> /dev/null; then
        open target/criterion/report/index.html
    elif command -v start &> /dev/null; then
        start target/criterion/report/index.html
    else
        print_warning "无法自动打开报告，请手动打开: target/criterion/report/index.html"
    fi
    
    print_success "性能报告生成完成"
}

# 清理基准测试结果
clean_benchmarks() {
    print_info "清理基准测试结果..."
    
    rm -rf target/criterion
    
    print_success "清理完成"
}

# 显示帮助信息
show_help() {
    cat << EOF
OTLP Rust 性能基准测试运行脚本

用法:
    $0 [选项]

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
    $0 all

    # 快速基准测试
    $0 quick

    # 与主分支对比
    $0 compare main

    # CI 模式
    $0 ci

    # 生成报告
    $0 report

    # 清理结果
    $0 clean
EOF
}

# 主函数
main() {
    check_dependencies
    
    local command="${1:-all}"
    
    case "$command" in
        all)
            run_all_benchmarks
            ;;
        quick)
            run_quick_benchmarks
            ;;
        core)
            run_core_benchmarks
            ;;
        performance)
            run_performance_benchmarks
            ;;
        comprehensive)
            run_comprehensive_benchmarks
            ;;
        compare)
            compare_with_baseline "$2"
            ;;
        ci)
            run_ci_benchmarks
            ;;
        report)
            generate_performance_report
            ;;
        clean)
            clean_benchmarks
            ;;
        help|--help|-h)
            show_help
            ;;
        *)
            print_error "未知命令: $command"
            show_help
            exit 1
            ;;
    esac
}

# 运行主函数
main "$@"

