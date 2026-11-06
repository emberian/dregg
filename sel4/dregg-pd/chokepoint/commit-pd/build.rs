// Link the Lean step (out/libchokepoint_lean_elf.a, from scripts/build-lean.sh) + the
// seL4-built Lean runtime (leanrt + Init only: the step imports nothing else) + GMP + the
// seL4 musl libc + the static C++ runtime, the same archive sources the executor PD links.
use std::env;
use std::path::PathBuf;
use std::process::Command;

const EXEC_SEL4: &str =
    "/Users/ember/dev/breadstuffs/sel4/dregg-pd/executor-rootserver/out/exec-sel4";
const MUSL_SEL4: &str =
    "/Users/ember/dev/breadstuffs/sel4/dregg-pd/executor-rootserver/out/musl-sel4";
const MUSL_TC: &str = "/opt/homebrew/Cellar/aarch64-unknown-linux-musl/15.2.0/toolchain";

fn main() {
    let out = PathBuf::from(env::var("OUT_DIR").unwrap());
    let here = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let lean = here.join("../out/libchokepoint_lean_elf.a");
    let lean_inc = env::var("LEAN_SYSROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            PathBuf::from(env::var("HOME").unwrap())
                .join(".elan/toolchains/leanprover--lean4---v4.30.0")
        })
        .join("include");
    println!("cargo:rerun-if-changed=csrc/driver.c");
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed={}", lean.display());
    assert!(
        lean.exists(),
        "run scripts/build-lean.sh first: {}",
        lean.display()
    );

    let driver_o = out.join("driver.o");
    let ok = Command::new(format!("{MUSL_TC}/bin/aarch64-linux-musl-gcc"))
        .args(["-O2", "-ffreestanding", "-fno-stack-protector", "-c"])
        .arg("-isystem")
        .arg(format!("{MUSL_SEL4}/include"))
        .arg("-I")
        .arg(&lean_inc)
        .arg("csrc/driver.c")
        .arg("-o")
        .arg(&driver_o)
        .status()
        .expect("musl gcc")
        .success();
    assert!(ok, "driver.c failed to compile");

    println!("cargo:rustc-link-arg=--gc-sections");
    println!("cargo:rustc-link-arg={}", driver_o.display());
    // libc gaps of a static no-loader PD (secure_getenv, dl_iterate_phdr), and the stubs for
    // kernel/elaborator entry points the runtime archives reference but the step never calls.
    for o in [
        "libc-compat.o",
        "kernel-stub.o",
        "aux-defs.o",
        "dead-stub.o",
    ] {
        println!("cargo:rustc-link-arg={EXEC_SEL4}/{o}");
    }
    println!("cargo:rustc-link-arg=--start-group");
    println!("cargo:rustc-link-arg={}", lean.display());
    for a in ["libleanrt_elf.a", "libInit_elf.a"] {
        println!("cargo:rustc-link-arg={EXEC_SEL4}/{a}");
    }
    println!("cargo:rustc-link-arg=--end-group");
    println!("cargo:rustc-link-arg={EXEC_SEL4}/libgmp.a");
    let stdcpp = format!("{MUSL_TC}/aarch64-unknown-linux-musl/lib64");
    let gcc = format!("{MUSL_TC}/lib/gcc/aarch64-unknown-linux-musl/15.2.0");
    println!("cargo:rustc-link-arg=--start-group");
    for a in [
        format!("{stdcpp}/libstdc++.a"),
        format!("{stdcpp}/libsupc++.a"),
        format!("{gcc}/libgcc.a"),
        format!("{gcc}/libgcc_eh.a"),
    ] {
        println!("cargo:rustc-link-arg={a}");
    }
    println!("cargo:rustc-link-arg=-lc");
    println!("cargo:rustc-link-arg=--end-group");
}
