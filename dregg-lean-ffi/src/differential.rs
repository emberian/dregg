//! differential.rs — the FIRST cascade step out of `./metatheory` into Rust.
//!
//! A **property-based differential harness** that makes the verified Lean kernel
//! the GOLDEN ORACLE for a Rust reference implementation. This is the
//! `dregg-dsl-differential` "backend #8" concept, realized for the kernel:
//!
//!   * The Lean side is `Metatheory.Exec.exec` / `authorizedB`, whose conservation
//!     (`exec_conserves`) and integrity (`exec_authorized`) are *PROVED* in Lean.
//!     We call the compiled artifact via FFI — not a reimplementation.
//!   * The Rust side is a small native reference (the "dregg1-style" code) that
//!     re-states the same 2-account transfer + authority semantics.
//!
//! The harness drives randomized inputs through BOTH and asserts agreement. Any
//! divergence aborts with a non-zero exit code. Agreement is the migration
//! certificate: once a Rust component is differentially-equal to the Lean oracle,
//! it can be replaced with confidence that it matches the proved semantics.

use std::process::ExitCode;

// --- Lean entry points (C ABI), identical to src/main.rs. ---
extern "C" {
    /// C shim (src/lean_init.c): runs the full Lean embedding init ritual.
    /// Returns 0 on success.
    fn dregg_ffi_init() -> i32;

    /// `@[export] Metatheory.Exec.FFI.transferTotal` — runs one proved kernel
    /// transfer and returns the conserved total.
    fn dregg_kernel_transfer_total(a: u64, b: u64, amt: u64) -> u64;

    /// `@[export] Metatheory.Exec.FFI.authorized` — the authority bit, in isolation.
    fn dregg_kernel_authorized(actor: u64) -> u8;
}

// =============================================================================
// The Rust reference ("dregg1-style native" side).
//
// This re-states, in plain Rust, the exact semantics the Lean kernel proves:
//
//   transferTotal(balA, balB, amt):
//     State {0,1}, bal 0 = balA, bal 1 = balB, empty caps.
//     Turn { actor: 0, src: 0, dst: 1, amt }.
//     The actor (0) owns src (0), so it is always authorized; src != dst and both
//     cells are live. The kernel commits iff 0 <= amt <= balA. Either way the
//     returned LIVE TOTAL is balA + balB:
//       - commit:  total is conserved by `exec_conserves` => balA + balB;
//       - reject:  `getD k` yields the unchanged input => total balA + balB.
//     So the reference total is simply the conserved sum balA + balB.
//
//   authorized(actor):
//     Empty cap table; `authorizedB` is true iff actor == src (== 0), i.e. actor
//     owns the source cell.
// =============================================================================

/// Rust reference for `dregg_kernel_transfer_total`.
fn ref_transfer_total(bal_a: u64, bal_b: u64, _amt: u64) -> u64 {
    // The conserved total over the two live accounts. `amt` never changes it
    // (conserved on commit, unchanged input on fail-closed reject).
    bal_a + bal_b
}

/// Rust reference for `dregg_kernel_authorized`: authorized iff the actor owns
/// the source cell 0.
fn ref_authorized(actor: u64) -> u8 {
    if actor == 0 {
        1
    } else {
        0
    }
}

// --- A tiny self-contained PRNG (xorshift64*) so we pull no extra crates. ---
struct Rng(u64);

impl Rng {
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    /// A balance/amount bounded so `balA + balB` cannot overflow u64. We cap each
    /// operand to 2^40, well under u64::MAX/2, so the reference sum is exact.
    fn next_bounded(&mut self) -> u64 {
        self.next_u64() % (1u64 << 40)
    }
}

const N: usize = 10_000;

fn main() -> ExitCode {
    let rc = unsafe { dregg_ffi_init() };
    if rc != 0 {
        eprintln!("FATAL: Lean module initialization failed (rc={rc})");
        return ExitCode::FAILURE;
    }

    let mut rng = Rng(0x9E37_79B9_7F4A_7C15); // fixed seed => reproducible
    let mut agreed = 0usize;
    let mut diverged = 0usize;

    for i in 0..N {
        // Randomized inputs, bounded to keep balA + balB within u64.
        let bal_a = rng.next_bounded();
        let bal_b = rng.next_bounded();
        // `amt` spans both the available (<= balA) and over-draw (> balA) regimes.
        let amt = rng.next_bounded();
        // Actor 0 a third of the time (authorized), otherwise an arbitrary id.
        let actor = if rng.next_u64() % 3 == 0 { 0 } else { rng.next_u64() };

        let lean_total = unsafe { dregg_kernel_transfer_total(bal_a, bal_b, amt) };
        let lean_auth = unsafe { dregg_kernel_authorized(actor) };

        let rust_total = ref_transfer_total(bal_a, bal_b, amt);
        let rust_auth = ref_authorized(actor);

        let total_ok = lean_total == rust_total;
        let auth_ok = lean_auth == rust_auth;

        if total_ok && auth_ok {
            agreed += 1;
        } else {
            diverged += 1;
            eprintln!(
                "DIVERGENCE @case {i}: inputs balA={bal_a} balB={bal_b} amt={amt} actor={actor}"
            );
            if !total_ok {
                eprintln!("  total: lean={lean_total} rust={rust_total}");
            }
            if !auth_ok {
                eprintln!("  auth:  lean={lean_auth} rust={rust_auth}");
            }
        }
    }

    if diverged == 0 {
        println!("{agreed}/{N} cases agree — Lean kernel \u{2261} Rust reference");
        ExitCode::SUCCESS
    } else {
        eprintln!("{diverged}/{N} cases DIVERGED — Lean kernel \u{2262} Rust reference");
        ExitCode::FAILURE
    }
}
