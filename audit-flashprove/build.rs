// build.rs: compile minidregg's audit decision modules (core Lean only: Selvage/AuditDecideCore,
// Selvage/AuditFlashProveDecide, Selvage/AuditExactDecide) to C with the Lean toolchain, in import
// order, compile them and csrc/shim.c with leanc, and link the result with the static Lean runtime. There is no fallback: without MINIDREGG_DIR and a Lean toolchain the build fails, so the
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
    let mods = [
        "AuditDecideCore",
        "AuditFlashProveDecide",
        "AuditExactDecide",
    ];
    let srcs: Vec<PathBuf> = mods
        .iter()
        .map(|m| md.join(format!("Selvage/{m}.lean")))
        .collect();
    for src in &srcs {
        assert!(
            src.exists(),
            "audit-flashprove: {} is missing",
            src.display()
        );
        println!("cargo:rerun-if-changed={}", src.display());
    }
    let lean = std::env::var("LEAN").unwrap_or_else(|_| "lean".into());
    let prefix = Command::new(&lean)
        .arg("--print-prefix")
        .output()
        .expect("audit-flashprove: lean on PATH");
    let prefix = PathBuf::from(String::from_utf8(prefix.stdout).unwrap().trim());
    let out = PathBuf::from(std::env::var("OUT_DIR").unwrap());
    // Each module is elaborated against the .olean files of the ones before it, written here.
    let olean = out.join("olean");
    std::fs::create_dir_all(olean.join("Selvage")).unwrap();
    let leanc = prefix.join("bin/leanc");
    let mut objs = Vec::new();
    let mut cat = Vec::new();
    for (m, src) in mods.iter().zip(&srcs) {
        let c = out.join(format!("{m}.c"));
        run(Command::new(&lean)
            .env("LEAN_PATH", &olean)
            .arg(format!("--root={}", md.display()))
            .arg("-o")
            .arg(olean.join(format!("Selvage/{m}.olean")))
            .arg("-c")
            .arg(&c)
            .arg(src));
        let o = out.join(format!("{m}.o"));
        run(Command::new(&leanc)
            .args(["-c", "-O2", "-fPIC", "-o"])
            .arg(&o)
            .arg(&c));
        objs.push(o);
        cat.extend_from_slice(format!("{m}\0").as_bytes());
        cat.extend_from_slice(&std::fs::read(src).unwrap());
        cat.push(0);
    }
    run(Command::new(&leanc)
        .args(["-c", "-O2", "-fPIC", "-o"])
        .arg(out.join("shim.o"))
        .arg("csrc/shim.c"));
    objs.push(out.join("shim.o"));
    let lib = out.join("libminidregg_fp_audit.a");
    let _ = std::fs::remove_file(&lib);
    run(Command::new("ar").arg("rcs").arg(&lib).args(&objs));
    // The decision source digest: SHA-256 over `name NUL source NUL` for each module, in order.
    let catp = out.join("decide-src.cat");
    std::fs::write(&catp, &cat).unwrap();
    println!(
        "cargo:rustc-env=FPAUDIT_DECIDE_SRC_SHA256={}",
        sha256_hex(&catp)
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
