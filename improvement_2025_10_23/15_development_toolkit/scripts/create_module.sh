#!/bin/bash
# Module Creation Script
# 新模块创建脚本

set -e

# Colors
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m'

# Check arguments
if [ $# -lt 2 ]; then
    echo "Usage: $0 <category> <module_name>"
    echo ""
    echo "Examples:"
    echo "  $0 profiling cpu"
    echo "  $0 semantic_conventions http"
    echo "  $0 compression tracezip"
    exit 1
fi

CATEGORY=$1
MODULE_NAME=$2
SRC_DIR="crates/otlp/src/$CATEGORY"
TEST_DIR="crates/otlp/tests/$CATEGORY"
BENCH_DIR="crates/otlp/benches/$CATEGORY"

echo -e "${BLUE}Creating module: $CATEGORY/$MODULE_NAME${NC}"

# Create source file
mkdir -p "$SRC_DIR"
MODULE_FILE="$SRC_DIR/$MODULE_NAME.rs"

if [ -f "$MODULE_FILE" ]; then
    echo -e "${YELLOW}Module file already exists: $MODULE_FILE${NC}"
    read -p "Overwrite? (y/n) " -n 1 -r
    echo
    if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        exit 1
    fi
fi

# Generate module file
cat > "$MODULE_FILE" << EOF
//! $MODULE_NAME module
//!
//! This module implements ...

use crate::common::*;
use std::fmt;

/// Main structure for $MODULE_NAME
#[derive(Debug, Clone)]
pub struct ${MODULE_NAME^} {
    // TODO: Add fields
}

impl ${MODULE_NAME^} {
    /// Creates a new instance
    pub fn new() -> Self {
        Self {
            // TODO: Initialize
        }
    }
}

impl Default for ${MODULE_NAME^} {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let instance = ${MODULE_NAME^}::new();
        // TODO: Add assertions
    }
}
EOF

echo -e "${GREEN}✓${NC} Created source file: $MODULE_FILE"

# Create test file
mkdir -p "$TEST_DIR"
TEST_FILE="$TEST_DIR/${MODULE_NAME}_test.rs"

cat > "$TEST_FILE" << EOF
//! Integration tests for $MODULE_NAME

use otlp::$CATEGORY::$MODULE_NAME::*;

#[test]
fn test_integration_basic() {
    // TODO: Add integration test
}

#[test]
fn test_integration_advanced() {
    // TODO: Add advanced integration test
}
EOF

echo -e "${GREEN}✓${NC} Created test file: $TEST_FILE"

# Create benchmark file
mkdir -p "$BENCH_DIR"
BENCH_FILE="$BENCH_DIR/${MODULE_NAME}_bench.rs"

cat > "$BENCH_FILE" << EOF
//! Benchmarks for $MODULE_NAME

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use otlp::$CATEGORY::$MODULE_NAME::*;

fn bench_${MODULE_NAME}_new(c: &mut Criterion) {
    c.bench_function("${MODULE_NAME}_new", |b| {
        b.iter(|| {
            ${MODULE_NAME^}::new()
        });
    });
}

fn bench_${MODULE_NAME}_operation(c: &mut Criterion) {
    let instance = ${MODULE_NAME^}::new();
    
    c.bench_function("${MODULE_NAME}_operation", |b| {
        b.iter(|| {
            // TODO: Add benchmark operation
            black_box(&instance);
        });
    });
}

criterion_group!(benches, bench_${MODULE_NAME}_new, bench_${MODULE_NAME}_operation);
criterion_main!(benches);
EOF

echo -e "${GREEN}✓${NC} Created benchmark file: $BENCH_FILE"

# Update mod.rs
MOD_FILE="$SRC_DIR/mod.rs"
if [ -f "$MOD_FILE" ]; then
    if ! grep -q "pub mod $MODULE_NAME;" "$MOD_FILE"; then
        echo "pub mod $MODULE_NAME;" >> "$MOD_FILE"
        echo -e "${GREEN}✓${NC} Updated $MOD_FILE"
    else
        echo -e "${YELLOW}!${NC} Module already declared in $MOD_FILE"
    fi
else
    cat > "$MOD_FILE" << EOF
//! $CATEGORY module

pub mod $MODULE_NAME;
EOF
    echo -e "${GREEN}✓${NC} Created $MOD_FILE"
fi

# Summary
echo ""
echo -e "${GREEN}Module created successfully!${NC}"
echo ""
echo "Files created:"
echo "  - $MODULE_FILE"
echo "  - $TEST_FILE"
echo "  - $BENCH_FILE"
echo ""
echo "Next steps:"
echo "  1. Implement the module logic in $MODULE_FILE"
echo "  2. Add tests in $TEST_FILE"
echo "  3. Add benchmarks in $BENCH_FILE"
echo "  4. cargo build"
echo "  5. cargo test"
echo ""
echo -e "${GREEN}Happy coding! 🚀${NC}"

