//! OTTL性能基准测试
//!
//! 测试OTTL解析器的性能，目标达到300k span/s (10×提升)

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use otlp::ottl::bytecode::BytecodeCompiler;
use otlp::ottl::parser::{OttlParser, Statement};

fn generate_test_statements(count: usize) -> Vec<String> {
    (0..count)
        .map(|i| {
            format!(
                "set(span.attributes[\"test_key_{}\"], \"test_value_{}\")",
                i, i
            )
        })
        .collect()
}

fn ottl_parse_scalar(c: &mut Criterion) {
    let mut group = c.benchmark_group("ottl_parse_scalar");

    for size in [100, 1000, 10000] {
        let statements = generate_test_statements(size);

        group.bench_with_input(
            BenchmarkId::new("scalar", size),
            &statements,
            |b, statements| {
                b.iter(|| {
                    let mut parser = OttlParser::new(statements.join(";"));
                    let _ = parser.parse();
                });
            },
        );
    }

    group.finish();
}

fn ottl_parse_bytecode(c: &mut Criterion) {
    let mut group = c.benchmark_group("ottl_parse_bytecode");

    for size in [100, 1000, 10000] {
        let statements = generate_test_statements(size);

        group.bench_with_input(
            BenchmarkId::new("bytecode", size),
            &statements,
            |b, statements| {
                let mut compiler = BytecodeCompiler::new();
                b.iter(|| {
                    for stmt_str in statements {
                        let mut parser = OttlParser::new(stmt_str.clone());
                        if let Ok(stmts) = parser.parse() {
                            for stmt in stmts {
                                let _ = compiler.compile(&stmt);
                            }
                        }
                    }
                });
            },
        );
    }

    group.finish();
}

fn ottl_execute_bytecode(c: &mut Criterion) {
    let mut group = c.benchmark_group("ottl_execute_bytecode");

    for size in [100, 1000, 10000] {
        let statements = generate_test_statements(size);
        let mut compiler = BytecodeCompiler::new();
        let mut programs = Vec::new();

        for stmt_str in &statements {
            let mut parser = OttlParser::new(stmt_str.clone());
            if let Ok(stmt) = parser.parse_statement() {
                if let Ok(program) = compiler.compile(&stmt) {
                    programs.push(program);
                }
            }
        }

        group.bench_with_input(
            BenchmarkId::new("execute", size),
            &programs,
            |b, programs| {
                b.iter(|| {
                    for program in programs {
                        // 执行字节码 (实际实现需要TelemetryData)
                        let _ = program.instructions.len();
                    }
                });
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    ottl_parse_scalar,
    ottl_parse_bytecode,
    ottl_execute_bytecode
);
criterion_main!(benches);
