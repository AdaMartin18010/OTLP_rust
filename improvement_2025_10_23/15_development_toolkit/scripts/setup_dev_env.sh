#!/bin/bash
# Development Environment Setup Script
# 开发环境搭建脚本

set -e  # Exit on error

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Configuration
RUST_VERSION="1.90"
REQUIRED_TOOLS=(
    "cargo-watch"
    "cargo-nextest"
    "cargo-tarpaulin"
    "cargo-flamegraph"
    "cargo-expand"
    "cargo-audit"
)

OPTIONAL_TOOLS=(
    "cargo-edit"
    "cargo-outdated"
    "cargo-tree"
)

# Functions
print_header() {
    echo -e "${BLUE}========================================${NC}"
    echo -e "${BLUE}  OTLP Rust Development Environment${NC}"
    echo -e "${BLUE}========================================${NC}"
    echo ""
}

print_step() {
    echo -e "${GREEN}[✓]${NC} $1"
}

print_info() {
    echo -e "${BLUE}[i]${NC} $1"
}

print_warn() {
    echo -e "${YELLOW}[!]${NC} $1"
}

print_error() {
    echo -e "${RED}[✗]${NC} $1"
}

check_rust_version() {
    print_info "Checking Rust version..."
    
    if ! command -v rustc &> /dev/null; then
        print_error "Rust is not installed!"
        print_info "Please install Rust from https://rustup.rs/"
        exit 1
    fi
    
    CURRENT_VERSION=$(rustc --version | awk '{print $2}')
    print_step "Rust version: $CURRENT_VERSION"
    
    # Note: This is a simplified version check
    if [[ "$CURRENT_VERSION" < "$RUST_VERSION" ]]; then
        print_warn "Rust version $RUST_VERSION or higher is recommended"
        print_info "Current version: $CURRENT_VERSION"
        read -p "Continue anyway? (y/n) " -n 1 -r
        echo
        if [[ ! $REPLY =~ ^[Yy]$ ]]; then
            exit 1
        fi
    fi
}

install_required_tools() {
    print_info "Installing required cargo tools..."
    
    for tool in "${REQUIRED_TOOLS[@]}"; do
        if cargo install --list | grep -q "^$tool "; then
            print_step "$tool already installed"
        else
            print_info "Installing $tool..."
            cargo install "$tool" || print_warn "Failed to install $tool"
        fi
    done
}

install_optional_tools() {
    print_info "Installing optional cargo tools..."
    
    read -p "Install optional tools? (y/n) " -n 1 -r
    echo
    if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        return
    fi
    
    for tool in "${OPTIONAL_TOOLS[@]}"; do
        if cargo install --list | grep -q "^$tool "; then
            print_step "$tool already installed"
        else
            print_info "Installing $tool..."
            cargo install "$tool" || print_warn "Failed to install $tool"
        fi
    done
}

setup_git_hooks() {
    print_info "Setting up Git hooks..."
    
    HOOKS_DIR=".git/hooks"
    if [ ! -d "$HOOKS_DIR" ]; then
        print_warn "Not in a Git repository, skipping hooks setup"
        return
    fi
    
    # Pre-commit hook
    cat > "$HOOKS_DIR/pre-commit" << 'EOF'
#!/bin/bash
# Pre-commit hook: Run formatting and basic checks

echo "Running pre-commit checks..."

# Format check
if ! cargo fmt -- --check; then
    echo "❌ Formatting check failed. Run 'cargo fmt' to fix."
    exit 1
fi

# Quick clippy check
if ! cargo clippy --all-targets -- -D warnings; then
    echo "❌ Clippy check failed. Fix the warnings before committing."
    exit 1
fi

echo "✅ Pre-commit checks passed!"
EOF
    
    chmod +x "$HOOKS_DIR/pre-commit"
    print_step "Git hooks configured"
}

create_vscode_settings() {
    print_info "Creating VS Code settings..."
    
    read -p "Create VS Code workspace settings? (y/n) " -n 1 -r
    echo
    if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        return
    fi
    
    mkdir -p .vscode
    
    cat > .vscode/settings.json << 'EOF'
{
    "rust-analyzer.checkOnSave.command": "clippy",
    "rust-analyzer.checkOnSave.extraArgs": ["--all-targets", "--", "-D", "warnings"],
    "editor.formatOnSave": true,
    "editor.rulers": [100],
    "files.trimTrailingWhitespace": true,
    "files.insertFinalNewline": true,
    "[rust]": {
        "editor.defaultFormatter": "rust-lang.rust-analyzer",
        "editor.tabSize": 4
    }
}
EOF
    
    cat > .vscode/extensions.json << 'EOF'
{
    "recommendations": [
        "rust-lang.rust-analyzer",
        "vadimcn.vscode-lldb",
        "serayuzgur.crates",
        "tamasfe.even-better-toml"
    ]
}
EOF
    
    print_step "VS Code settings created"
}

verify_installation() {
    print_info "Verifying installation..."
    
    cd crates/otlp || exit 1
    
    print_info "Running cargo check..."
    if cargo check --all-targets; then
        print_step "Cargo check passed"
    else
        print_error "Cargo check failed"
        exit 1
    fi
    
    print_info "Running cargo test..."
    if cargo test --no-fail-fast --quiet; then
        print_step "Tests passed"
    else
        print_warn "Some tests failed (this might be expected)"
    fi
}

print_summary() {
    echo ""
    print_header
    echo -e "${GREEN}Environment setup complete!${NC}"
    echo ""
    echo "Next steps:"
    echo "  1. cd crates/otlp"
    echo "  2. cargo build"
    echo "  3. cargo test"
    echo ""
    echo "Useful commands:"
    echo "  cargo watch -x check -x test  # Auto-run on changes"
    echo "  cargo nextest run             # Fast test runner"
    echo "  cargo clippy --all-targets    # Linter"
    echo "  cargo fmt                     # Format code"
    echo "  cargo tarpaulin               # Code coverage"
    echo ""
    echo "Documentation:"
    echo "  improvement_2025_10_23/14_implementation_roadmap/"
    echo ""
    print_step "Happy coding! 🚀"
}

# Main execution
main() {
    print_header
    
    check_rust_version
    install_required_tools
    install_optional_tools
    setup_git_hooks
    create_vscode_settings
    verify_installation
    print_summary
}

# Run main function
main "$@"

