// build.rs: compile minidregg's Selvage/AuditFlashProveDecide.lean (core Lean only) to C with the
// Lean toolchain, compile it and csrc/shim.c with leanc, and link the result with the static Lean
// runtime. There is no fallback: without MINIDREGG_DIR and a Lean toolchain the build fails, so the
// auditor can never run on a decision other than the compiled Lean one.
use std::path::{Path, PathBuf};
use std::process::Command;

fn run(cmd: &mut Command) {
    let st = cmd
        .status()
        .unwrap_or_else(|e| panic!("audit-flashprove build: cannot run {cmd:?}: {e}"));
    assert!(
        st.success(),
        "audit-flashprove build: {cmd:?} failed with {st}"
    );
}

fn sha256_hex(p: &Path) -> String {
    let out = Command::new(if cfg!(target_os = "macos") {
        "shasum"
    } else {
        "sha256sum"
    })
    .args(if cfg!(target_os = "macos") {
        vec!["-a", "256"]
    } else {
        vec![]
    })
    .arg(p)
    .output()
    .expect("audit-flashprove build: sha256 of the decision source");
    String::from_utf8_lossy(&out.stdout)
        .split_whitespace()
        .next()
        .unwrap_or("")
        .to_string()
}

fn main() {
    println!("cargo:rerun-if-env-changed=MINIDREGG_DIR");
    println!("cargo:rerun-if-env-changed=LEAN");
    println!("cargo:rerun-if-changed=csrc/shim.c");
    let md = PathBuf::from(std::env::var("MINIDREGG_DIR").expect(
        "audit-flashprove: set MINIDREGG_DIR to a minidregg checkout holding Selvage/AuditFlashProveDecide.lean",
    ));
    let src = md.join("Selvage/AuditFlashProveDecide.lean");
    assert!(
        src.exists(),
        "audit-flashprove: {} is missing",
        src.display()
    );
    println!("cargo:rerun-if-changed={}", src.display());
    let lean = std::env::var("LEAN").unwrap_or_else(|_| "lean".into());
    let prefix = Command::new(&lean)
        .arg("--print-prefix")
        .output()
        .expect("audit-flashprove: lean on PATH");
    let prefix = PathBuf::from(String::from_utf8(prefix.stdout).unwrap().trim());
    let out = PathBuf::from(std::env::var("OUT_DIR").unwrap());
    let c = out.join("decide.c");
    run(Command::new(&lean)
        .arg(format!("--root={}", md.display()))
        .arg("-c")
        .arg(&c)
        .arg(&src));
    let leanc = prefix.join("bin/leanc");
    for (from, to) in [
        (c.clone(), out.join("decide.o")),
        (PathBuf::from("csrc/shim.c"), out.join("shim.o")),
    ] {
        run(Command::new(&leanc)
            .args(["-c", "-O2", "-fPIC", "-o"])
            .arg(&to)
            .arg(&from));
    }
    let lib = out.join("libminidregg_fp_audit.a");
    let _ = std::fs::remove_file(&lib);
    run(Command::new("ar")
        .arg("rcs")
        .arg(&lib)
        .arg(out.join("decide.o"))
        .arg(out.join("shim.o")));
    println!(
        "cargo:rustc-env=FPAUDIT_DECIDE_SRC_SHA256={}",
        sha256_hex(&src)
    );
    println!("cargo:rustc-env=FPAUDIT_LEAN_PREFIX={}", prefix.display());
    println!("cargo:rustc-link-search=native={}", out.display());
    println!("cargo:rustc-link-lib=static=minidregg_fp_audit");
    println!(
        "cargo:rustc-link-search=native={}",
        prefix.join("lib/lean").display()
    );
    println!(
        "cargo:rustc-link-search=native={}",
        prefix.join("lib").display()
    );
    for l in ["Init", "leanrt"] {
        println!("cargo:rustc-link-lib=static={l}");
    }
    if cfg!(target_os = "linux") {
        for l in ["gmp", "uv", "c++", "c++abi", "unwind"] {
            println!("cargo:rustc-link-lib=static={l}");
        }
        for l in ["m", "dl", "pthread"] {
            println!("cargo:rustc-link-lib=dylib={l}");
        }
    } else {
        for l in ["gmp", "uv"] {
            println!("cargo:rustc-link-lib=static={l}");
        }
        println!("cargo:rustc-link-lib=dylib=c++");
    }
}
