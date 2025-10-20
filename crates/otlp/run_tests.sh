#!/bin/bash

# OTLP Rust 测试运行脚本

set -e

echo "🚀 开始运行OTLP Rust测试..."

# 检查Rust环境
if ! command -v cargo &> /dev/null; then
    echo "❌ 错误: 未找到cargo命令，请确保已安装Rust"
    exit 1
fi

echo "📋 运行单元测试..."
cargo test --lib

echo "📋 运行集成测试..."
cargo test --test integration_tests

echo "📋 运行性能测试..."
cargo test --test performance_tests

echo "📋 运行基准测试..."
cargo bench

echo "📋 检查代码格式..."
cargo fmt -- --check

echo "📋 运行Clippy检查..."
cargo clippy -- -D warnings

echo "📋 检查文档..."
cargo doc --no-deps

echo "✅ 所有测试完成！"
