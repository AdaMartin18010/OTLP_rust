use std::io::Result;

fn main() -> Result<()> {
    // Compile pprof proto file
    prost_build::compile_protos(&["proto/pprof.proto"], &["proto/"])?;
    Ok(())
}
