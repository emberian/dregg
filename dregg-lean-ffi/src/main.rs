//! dregg-lean-ffi — Rust hosts the compiled Lean kernel and calls it for real.
//!
//! This is the dregg2 cascade seam (§8: the Rust boundary hosts the verified kernel).
//! The functions below are the SAME `Metatheory.Exec.exec` / `authorizedB` whose
//! conservation (`exec_conserves`) and integrity (`exec_authorized`) are *proved* in
//! Lean — we call the compiled artifact, not a reimplementation.
//!
//! Before any exported function may run we must perform the Lean C-embedding init
//! ritual exactly once:
//!   1. `lean_initialize_runtime_module()` — bring up the Lean runtime (GC, etc.);
//!   2. `initialize_Metatheory_Metatheory_Exec_FFI(builtin)` — the generated module
//!      initializer, which transitively initializes every imported module (Kernel,
//!      mathlib, …) and returns an `IO` result object;
//!   3. `lean_io_mark_end_initialization()` — freeze initialization.

// --- Lean entry points (C ABI). ---
extern "C" {
    // Our C shim (src/lean_init.c): runs the full embedding init ritual
    // (lean_initialize_runtime_module -> initialize_Metatheory_Metatheory_Exec_FFI
    //  -> lean_io_mark_end_initialization). Returns 0 on success.
    fn dregg_ffi_init() -> i32;

    // Our @[export]ed kernel entry points.
    fn dregg_kernel_transfer_total(a: u64, b: u64, amt: u64) -> u64;
    fn dregg_kernel_authorized(actor: u64) -> u8;
}

fn main() {
    let rc = unsafe { dregg_ffi_init() };
    assert_eq!(rc, 0, "Lean module initialization failed (rc={rc})");

    // (a) Conserved-total transfer through the proved kernel.
    //     State: cell0=100, cell1=5, accounts {0,1}; turn moves 30 from 0->1 under
    //     actor 0's own authority. By `exec_conserves` the live total is preserved:
    //     100 + 5 = 105 (and on a fail-closed `none` we return the unchanged input
    //     total, also 105 for these args).
    let total = unsafe { dregg_kernel_transfer_total(100, 5, 30) };
    println!("dregg_kernel_transfer_total(100, 5, 30) = {total}  (expected 105)");
    assert_eq!(total, 105, "conservation broken: kernel returned {total}, expected 105");

    // (b) Authority check in isolation (empty cap table => authorized iff actor owns
    //     src=0, i.e. actor == 0). This is `Exec.authorizedB`, the integrity predicate
    //     guarding `exec`.
    let auth0 = unsafe { dregg_kernel_authorized(0) };
    let auth2 = unsafe { dregg_kernel_authorized(2) };
    println!("dregg_kernel_authorized(0)            = {auth0}  (expected 1, owns src)");
    println!("dregg_kernel_authorized(2)            = {auth2}  (expected 0, unauthorized)");
    assert_eq!(auth0, 1, "actor 0 should be authorized over its own cell");
    assert_eq!(auth2, 0, "actor 2 must be fail-closed (no cap on src 0)");

    println!("OK: Rust round-tripped the verified Lean kernel.");
}
