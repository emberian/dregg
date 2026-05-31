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

A third `@[export]` marshals **real record cell-state** (not a scalar) across the C ABI:

* `dregg_record_kernel_step(input: String) -> String` — wraps the PROVED
  `Exec.recKExec` (conservation/authority/fail-closed all proved in
  `Dregg2/Exec/RecordKernel.lean`). Input is a canonical JSON encoding of a
  `RecordKernelState` (per-cell `Value` records) + the turn; output is the post-state
  cells + a commit bit. Driven from Rust through the C string bridge
  `dregg_record_kernel_step_str` in `src/lean_init.c` (needed because `lean_string_cstr`
  is a `static inline`).

## The marshalling boundary (minimal-TCB)

The Lean↔Rust wire for record state is a small canonical JSON grammar that BOTH sides
agree on (Lean: `Dregg2.Exec.FFI.encodeValue`/`parseInput`; Rust:
`src/state_differential.rs` codec). It is the only thing the two sides must agree on, and
the `state_differential` harness is what certifies the agreement empirically. The grammar
(no whitespace, as emitted):

```
VALUE  := {"int":N} | {"dig":N} | {"sym":N} | {"rec":FIELDS}
FIELDS := [] | [["NAME",VALUE](,["NAME",VALUE])*]
CELLS  := [] | [[ID,VALUE](,[ID,VALUE])*]
state  := {"cells":CELLS,"actor":N,"src":N,"dst":N,"amt":N}      (input)
out    := {"cells":CELLS,"ok":B}                                 (output; B ∈ {0,1})
```

This codec is **TCB, not proved**: the differential is cross-validation (Lean oracle vs a
Rust reference `recKExec`), not a certification of the codec. Nested records are handled
(the grammar/codec recurse over the int/dig/sym/record leaves), so the boundary covers the
full `Value` leaf set, not only a flat `balance` record.

### Marshalling the HELD-CAP authority table

`dregg_record_kernel_step` marshals the record cell-state but hard-codes the cap table
empty (`caps := fun _ => []`), so authority there is by OWNERSHIP only (`actor = src`). For
the cascade swap, the node's turn-decision must exercise the FULL `Kernel.authorizedB` gate
— including the **cross-vat / held-cap case**: an `actor ≠ owner` is authorized iff it HOLDS
a discharging cap on `src` (a `node src` cap, or an `endpoint src` cap carrying `Auth.write`).
A fourth `@[export]` marshals the `Caps` table alongside the record state:

* `dregg_record_kernel_step_caps(input: String) -> String` — same PROVED `Exec.recKExec`,
  but the input wire also carries the `Caps` table (`Label → List Cap`), so a held-cap turn
  can commit. Output wire is IDENTICAL to `dregg_record_kernel_step`. Driven through the C
  bridge `dregg_record_kernel_step_caps_str` in `src/lean_init.c`.

The cap wire grammar extends the input object with a `"caps"` field (output unchanged):

```
CAP        := {"null":0} | {"node":N} | {"ep":[N,AUTHS]}   (null / node target / endpoint)
AUTHS      := [] | [A(,A)*]   A := 0=read 1=write 2=grant 3=call 4=reply 5=reset 6=control
CAPLIST    := [] | [CAP(,CAP)*]
CAPS       := [] | [[HOLDER,CAPLIST](,[HOLDER,CAPLIST])*]
state_caps := {"cells":CELLS,"caps":CAPS,"actor":N,"src":N,"dst":N,"amt":N}   (input)
```

A `Caps` value is a TOTAL function `Label → List Cap`; it is marshalled as the finite list of
holders with a non-empty slot and reconstructed as "listed slot, else `[]`". The auth tags are
the `Dregg2.Authority.Auth` constructor order (`read`=0 … `control`=6).

This caps codec is **also TCB, not proved** — the caps differential (`state_differential`
phase 3) is its cross-validation: Lean `dregg_record_kernel_step_caps` (the proved `recKExec`,
authority gate included) vs the Rust reference `ref_rec_k_exec_caps`/`ref_authorized`, which
re-states `authorizedB` over the marshalled table. The differential confirms a held-cap turn
(actor ≠ owner, holds a discharging cap) round-trips and COMMITS, while an unauthorized turn
(no discharging cap) REJECTS — fail-closed. Current result: **30000/30000 step cases agree**
(10k single-field + 10k multi-field + 10k held-cap; +40000 value round-trips), with the named
witnesses `WITNESS A` (write-endpoint holder commits) and `WITNESS B` (read-only holder
rejects).

## The three binaries

| bin | purpose |
| --- | --- |
| `dregg-lean-ffi` (`src/main.rs`) | smoke test: a single round-trip through the kernel |
| `differential` (`src/differential.rs`) | the cascade beachhead: a scalar property-based differential harness (the `default-run`) |
| `state_differential` (`src/state_differential.rs`) | the SWAP-enabler: marshals real record cell-state AND the held-cap table, diffs `recKExec` vs a Rust reference (30000/30000 step cases agree + 40000 value round-trips; held-cap authorize/reject witnesses) |

> Rebuilding `libdregg_lean.a`: the archive uses flat per-module object names. After
> adding/changing an `@[export]`, regenerate the affected Lean modules' `:c` facets
> (`lake build <Mod>:c`), compile each with `lake env leanc -c <Mod.c> -o <base>.o`, and
> splice them in with `ar r libdregg_lean.a <base>.o && ranlib libdregg_lean.a`. Only the
> ~9-module `Dregg2` closure of `FFI` needs recompiling; the mathlib/batteries objects in
> the archive are reused unchanged. (Module symbols mangle as `Dregg2_Dregg2_<Mod>`.)

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
