// build.rs — wire the Rust binary to the compiled Lean kernel + Lean runtime.
//
// We link against:
//   * libdregg_lean.a — a single static archive of the native objects emitted by the
//     Lean compiler for `Dregg2.Exec.FFI` and its ENTIRE transitive dependency
//     closure (Dregg2 modules + mathlib + batteries + aesop + Qq + … — ~8200 .o).
//     The archive lives next to this build.rs; it was produced by compiling each
//     module's `.c` (lake's `:c` facet) with `leanc -c` and archiving with `llvm-ar`.
//   * the Lean runtime + stdlib in the elan toolchain `lib/lean` dir
//     (leancpp/Init/Std/Lean/leanrt + gmp/uv/c++), discovered from the active toolchain.
//
// Toolchain paths are discovered from `lake env` (LEAN_SYSROOT) with a fallback to the
// pinned elan toolchain, so this stays robust to elan being on PATH.

use std::path::PathBuf;
use std::process::Command;

fn lean_sysroot() -> PathBuf {
    // Prefer `lake env` (authoritative for the project's toolchain).
    if let Ok(out) = Command::new("lake")
        .args(["env", "printenv", "LEAN_SYSROOT"])
        .current_dir("/Users/ember/dev/breadstuffs/metatheory")
        .output()
    {
        let s = String::from_utf8_lossy(&out.stdout).trim().to_string();
        if !s.is_empty() {
            return PathBuf::from(s);
        }
    }
    // Fallback: the pinned toolchain.
    PathBuf::from("/Users/ember/.elan/toolchains/leanprover--lean4---v4.30.0")
}

fn main() {
    let crate_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let sysroot = lean_sysroot();
    let lean_lib = sysroot.join("lib").join("lean");
    let lean_include = sysroot.join("include");

    // Compile the C init shim (it uses the `static inline` runtime helpers from
    // <lean/lean.h>, which have no linkable symbol and so must be used from C).
    cc::Build::new()
        .file("src/lean_init.c")
        .include(&lean_include)
        .compile("dregg_ffi_shim");

    // Our archive of the compiled Lean kernel + transitive closure.
    println!("cargo:rustc-link-search=native={}", crate_dir.display());
    println!("cargo:rustc-link-lib=static=dregg_lean");

    // The Lean runtime + stdlib (mirrors `leanc --print-ldflags`).
    println!("cargo:rustc-link-search=native={}", lean_lib.display());
    println!("cargo:rustc-link-search=native={}", sysroot.join("lib").display());
    for lib in ["leancpp", "Init", "Std", "Lean", "leanrt", "Lake", "gmp", "uv"] {
        println!("cargo:rustc-link-lib=static={lib}");
    }
    // C++ runtime + system frameworks the Lean runtime needs on macOS.
    println!("cargo:rustc-link-lib=dylib=c++");

    // Rebuild triggers.
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=src/lean_init.c");
    println!("cargo:rerun-if-changed=libdregg_lean.a");
}
