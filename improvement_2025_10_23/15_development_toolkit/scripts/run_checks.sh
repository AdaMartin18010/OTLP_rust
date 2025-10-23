#!/bin/bash
# Code Quality Checks Script
# 代码质量检查脚本

set -e

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# Configuration
MODE="${1:---full}"
START_TIME=$(date +%s)

print_header() {
    echo -e "${BLUE}========================================${NC}"
    echo -e "${BLUE}  Code Quality Checks${NC}"
    echo -e "${BLUE}========================================${NC}"
    echo ""
}

print_step() {
    echo -e "${GREEN}[✓]${NC} $1"
}

print_fail() {
    echo -e "${RED}[✗]${NC} $1"
}

print_info() {
    echo -e "${BLUE}[i]${NC} $1"
}

run_format_check() {
    print_info "Running format check..."
    if cargo fmt -- --check; then
        print_step "Format check passed"
        return 0
    else
        print_fail "Format check failed"
        echo "  Run 'cargo fmt' to fix formatting issues"
        return 1
    fi
}

run_clippy() {
    print_info "Running Clippy..."
    if cargo clippy --all-targets --all-features -- -D warnings; then
        print_step "Clippy check passed"
        return 0
    else
        print_fail "Clippy check failed"
        return 1
    fi
}

run_compile_check() {
    print_info "Running compile check..."
    if cargo check --all-targets --all-features; then
        print_step "Compile check passed"
        return 0
    else
        print_fail "Compile check failed"
        return 1
    fi
}

run_tests() {
    print_info "Running tests..."
    if command -v cargo-nextest &> /dev/null; then
        if cargo nextest run --all-features; then
            print_step "Tests passed"
            return 0
        else
            print_fail "Tests failed"
            return 1
        fi
    else
        if cargo test --all-features; then
            print_step "Tests passed"
            return 0
        else
            print_fail "Tests failed"
            return 1
        fi
    fi
}

run_doc_check() {
    print_info "Running doc check..."
    if cargo doc --no-deps --document-private-items; then
        print_step "Doc check passed"
        return 0
    else
        print_fail "Doc check failed"
        return 1
    fi
}

run_coverage() {
    print_info "Running coverage analysis..."
    if command -v cargo-tarpaulin &> /dev/null; then
        if cargo tarpaulin --out Html --output-dir coverage --skip-clean; then
            print_step "Coverage report generated: coverage/index.html"
            return 0
        else
            print_fail "Coverage analysis failed"
            return 1
        fi
    else
        print_info "cargo-tarpaulin not installed, skipping coverage"
        return 0
    fi
}

run_audit() {
    print_info "Running security audit..."
    if command -v cargo-audit &> /dev/null; then
        if cargo audit; then
            print_step "Security audit passed"
            return 0
        else
            print_fail "Security audit found issues"
            return 1
        fi
    else
        print_info "cargo-audit not installed, skipping audit"
        return 0
    fi
}

run_benchmarks() {
    print_info "Running benchmarks..."
    if cargo bench --no-run; then
        print_step "Benchmarks compiled successfully"
        return 0
    else
        print_fail "Benchmark compilation failed"
        return 1
    fi
}

print_summary() {
    local end_time=$(date +%s)
    local duration=$((end_time - START_TIME))
    
    echo ""
    echo -e "${BLUE}========================================${NC}"
    echo -e "${BLUE}  Summary${NC}"
    echo -e "${BLUE}========================================${NC}"
    echo ""
    
    if [ ${#PASSED[@]} -gt 0 ]; then
        echo -e "${GREEN}Passed checks (${#PASSED[@]}):${NC}"
        for check in "${PASSED[@]}"; do
            echo -e "  ${GREEN}✓${NC} $check"
        done
        echo ""
    fi
    
    if [ ${#FAILED[@]} -gt 0 ]; then
        echo -e "${RED}Failed checks (${#FAILED[@]}):${NC}"
        for check in "${FAILED[@]}"; do
            echo -e "  ${RED}✗${NC} $check"
        done
        echo ""
    fi
    
    echo "Time taken: ${duration}s"
    echo ""
    
    if [ ${#FAILED[@]} -eq 0 ]; then
        echo -e "${GREEN}All checks passed! ✨${NC}"
        return 0
    else
        echo -e "${RED}Some checks failed!${NC}"
        return 1
    fi
}

# Arrays to track results
PASSED=()
FAILED=()

run_check() {
    local check_name=$1
    local check_func=$2
    
    if $check_func; then
        PASSED+=("$check_name")
    else
        FAILED+=("$check_name")
    fi
}

main() {
    cd crates/otlp || exit 1
    
    print_header
    
    case $MODE in
        --quick)
            print_info "Running quick checks..."
            run_check "Format" run_format_check
            run_check "Compile" run_compile_check
            ;;
        --full)
            print_info "Running full checks..."
            run_check "Format" run_format_check
            run_check "Clippy" run_clippy
            run_check "Compile" run_compile_check
            run_check "Tests" run_tests
            run_check "Documentation" run_doc_check
            run_check "Security Audit" run_audit
            ;;
        --ci)
            print_info "Running CI checks..."
            run_check "Format" run_format_check
            run_check "Clippy" run_clippy
            run_check "Compile" run_compile_check
            run_check "Tests" run_tests
            run_check "Documentation" run_doc_check
            run_check "Coverage" run_coverage
            run_check "Security Audit" run_audit
            run_check "Benchmarks" run_benchmarks
            ;;
        *)
            echo "Usage: $0 [--quick|--full|--ci]"
            echo ""
            echo "Modes:"
            echo "  --quick  Fast checks (format + compile)"
            echo "  --full   Complete checks (default)"
            echo "  --ci     CI mode (all checks + reports)"
            exit 1
            ;;
    esac
    
    print_summary
}

main "$@"

