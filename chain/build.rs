fn main() {
    // The SP1 guest program is built separately via `cargo prove build`.
    // When the `prove` feature is enabled, sp1-build handles locating the ELF.
    // In mock mode, no guest program build is needed.
    #[cfg(feature = "prove")]
    {
        sp1_build::build_program("./program");
    }
}
