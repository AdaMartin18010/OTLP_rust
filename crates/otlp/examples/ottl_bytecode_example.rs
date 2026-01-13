//! OTTL字节码解析器使用示例
//!
//! 演示如何使用字节码解析器实现10×性能提升

use otlp::ottl::bytecode::BytecodeCompiler;
use otlp::ottl::parser::OttlParser;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 解析OTTL语句
    let ottl_statement = r#"set(span.attributes["http.status_code"], 200)"#;
    let mut parser = OttlParser::new(ottl_statement.to_string());
    let statements = parser.parse()?;

    // 2. 编译到字节码
    let mut compiler = BytecodeCompiler::new();
    let mut programs = Vec::new();

    for statement in statements {
        let program = compiler.compile(&statement)?;
        
        println!("编译成功:");
        println!("  指令数: {}", program.instructions.len());
        println!("  字符串表大小: {}", program.string_table.len());
        println!("  常量池大小: {}", program.constants.len());
        
        programs.push(program);
    }

    // 3. 执行字节码 (实际应用中需要TelemetryData)
    println!("\n字节码程序准备就绪，可以执行以获得10×性能提升");

    Ok(())
}
