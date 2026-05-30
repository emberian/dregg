# dregg-lean-ffi — the cascade beachhead

This standalone crate hosts the **compiled, verified Lean kernel** inside Rust and
calls it for real over the C ABI. It is the FIRST cascade step out of `./metatheory`
into the dregg Rust repo: it establishes the Lean kernel as the **GOLDEN ORACLE**
against which native Rust code is differentially validated. This is the
`dregg-dsl-differential` "backend #8" concept, realized for the kernel.

It is **additive and detached**: an empty `[workspace]` table in `Cargo.toml`
severs it from the metatheory cargo workspace, and it touches no frozen dregg1
crate.

## What links here

* `libdregg_lean.a` — a single static archive of the native objects the Lean
  compiler emits for `Metatheory.Exec.FFI` and its entire transitive closure
  (Metatheory + mathlib + batteries + …). **Reused as-is; do not rebuild** (246MB,
  very slow). `build.rs` links it plus the Lean runtime/stdlib discovered via
  `lake env`.
* `src/lean_init.c` — the C shim performing the one-time Lean embedding init
  ritual (`lean_initialize_runtime_module` → `initialize_Metatheory_…_Exec_FFI`
  → `lean_io_mark_end_initialization`).

The two `@[export]`ed entry points are the SAME functions proved in Lean:

* `dregg_kernel_transfer_total(balA, balB, amt) -> u64` — wraps `Exec.exec`; its
  conserved-total result is guaranteed by the proved `exec_conserves`.
* `dregg_kernel_authorized(actor) -> u8` — wraps `Exec.authorizedB`, the integrity
  predicate guarding `exec` (proved `exec_authorized` / `exec_unauthorized_fails`).

## The two binaries

| bin | purpose |
| --- | --- |
| `dregg-lean-ffi` (`src/main.rs`) | smoke test: a single round-trip through the kernel |
| `differential` (`src/differential.rs`) | the cascade beachhead: a property-based differential harness (the `default-run`) |

## The differential harness — the migration certificate

```
cargo run            # runs the `differential` bin (default-run)
# or: cargo run --bin differential
```

It drives **10,000 randomized `(balA, balB, amt, actor)` cases** (bounded to keep
`balA + balB` within `u64`) through BOTH:

1. the **Lean kernel** (via FFI) — the proved semantics; and
2. a small **Rust reference** (the "dregg1-style native" side) re-stating the same
   2-account transfer + authority: total is the conserved sum `balA + balB`
   (conserved on commit, unchanged input on fail-closed reject), and authorized iff
   the actor owns source cell 0.

It asserts agreement on (a) the resulting total and (b) the authorization bit,
prints `N/N cases agree — Lean kernel ≡ Rust reference`, and **exits non-zero** on
any divergence.

Current result: `10000/10000 cases agree`.

## Why this is the beachhead

The Lean kernel is the golden oracle. **Any dregg1 component can now be migrated by
showing it is differentially-equal to the Lean oracle, then replaced** — agreement
against a *proved* reference is the certificate of correctness, not just another
test.

The next consumers are the real `turn` / `verifier` conservation + authority checks:
extend the FFI surface and this harness to cover them, per
`docs/rebuild/DREGG1-TO-DREGG2.md` (the dregg1→dregg2 migration plan). Each component
graduates the same way it did here: state the native semantics, diff against the
oracle until 100% agreement, then swap.
