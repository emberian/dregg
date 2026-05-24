//! Lint the SP1 guest source code emitted by `gen_sp1`.
//!
//! Running the SP1 guest requires the SP1 RISC-V toolchain (`cargo prove
//! build`, the zkVM ELF, etc) which we don't bundle in this test crate.
//! As a stand-in we statically check the emitted Rust source: it has a
//! `main`, declares an `sp1_zkvm::io::read()` for each parameter, and
//! commits a trailing success flag.

/// Lint the emitted SP1 guest source.
pub fn lint(source: &str, param_names: &[&str]) -> Result<(), String> {
    if !source.contains("pub fn main()") {
        return Err("SP1 guest source missing `pub fn main()`".into());
    }
    if !source.contains("sp1_zkvm::entrypoint!(main);") {
        return Err("SP1 guest source missing `sp1_zkvm::entrypoint!(main);`".into());
    }
    if !source.contains("sp1_zkvm::io::commit(&1u8)") {
        return Err("SP1 guest source missing success commitment".into());
    }
    for &param in param_names {
        let needle = format!("let {param}:");
        let needle_mut = format!("let mut {param}:");
        if !source.contains(&needle) && !source.contains(&needle_mut) {
            return Err(format!("SP1 guest source missing read for param `{param}`"));
        }
    }
    Ok(())
}
