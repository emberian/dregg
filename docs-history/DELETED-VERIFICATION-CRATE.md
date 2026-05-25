# Deleted: `verification/` (pyana-verification)

**Date:** 2026-05-24
**Removed in:** this commit
**Last commit touching the crate before deletion:** `1c3f648c`
("verification: model Stage 3 Effect VM AIR additions")

## What the crate was

A standalone Rust binary (`pyana-verification`, ~1850 LOC across
`lib.rs` + `pyana_model.rs` + `main.rs` + `STAGE-3-AUDIT.md`) that built
an in-memory graph of "proof statements" (EffectVm, IvcFoldChain,
IssuerMembership, DerivationProof, PresentationProof), declared
semantic-typed bindings between their public inputs, and ran four
checks: type consistency, assumption coverage, acyclicity, and
unbound-input detection. It then printed a long human-readable report.

It was **not** in the workspace (`Cargo.toml` declared its own
`[workspace]`), so nothing depended on it and no CI ran it.

## Why delete

After an honest read of the code and the Stage 3 audit output, the
crate failed every useful test of value:

1. **It catches nothing.** All five proof statements and five bindings
   are hand-authored in the same file by the same person. Type
   consistency over a graph you wrote yourself isn't verification —
   it's a smoke test for typos. Acyclicity is trivially satisfied for
   a 5-node DAG.

2. **It is not grounded in reality.** The model declares
   `EffectVmProof` has 5 public inputs of certain semantic types, but
   nothing checks this matches `circuit/src/effect_vm.rs`. If someone
   adds a public input to the real circuit, the model silently lies
   and the analysis still prints "SOUND."

3. **The genuinely useful artifact is prose, not code.** The
   trust-boundary inventory ("executor honesty for state commitment,
   federation consensus for nullifier completeness, prover RNG for
   unlinkability, …") and the threat analyses ("compromised executor",
   "stale federation state") are written as `println!` strings, then
   re-articulated as Markdown in `STAGE-3-AUDIT.md`. The same
   information lives in a one-page document and can be maintained by
   editing that document.

4. **No-one acts on its output.** No CI, no production dependency, no
   downstream consumer. The verdict line — "CONDITIONALLY SOUND (gaps
   exist)" — has been the same since v0.1.0 and is acknowledged in
   the Stage 3 audit to reflect "checker-tuning issues, not Stage 3
   issues." If the answer never changes, it isn't measuring.

5. **No healthy investment trajectory.** The two plausible upgrades —
   (a) ground the model in real circuit metadata, or (b) emit a
   TLA+/Lean fragment from the graph — both have better non-crate
   paths. For (a), the right shape is a CI assertion in `circuit/`
   that pins the `NUM_PUBLIC_INPUTS` constants and their semantics in
   a doctest or `const _: () = assert!(…)`. For (b), `spec/` already
   has `CellModel.tla` (the parallel substrate spec); a richer formal
   model belongs there, written by hand against the substrate, not
   auto-extracted from a hand-written Rust mirror of the proof shapes.

## What replaces it

- **Substrate-level invariants:** `spec/CellModel.tla` (id integrity,
  nonce monotonicity, attenuation lattice) — owned by the formal-spec
  work in `spec/`.
- **Proof-composition trust inventory:** the existing prose audits
  (`verification/STAGE-3-AUDIT.md`'s content; the trust boundary
  enumeration in `main.rs`'s `print_topology`). These are useful as
  Markdown; a future commit can fold them into `spec/` or a
  `docs/trust-boundary.md` if anyone wants the inventory preserved.
  The deletion does not block that — it just stops pretending the
  Rust crate was doing the work.
- **Public-input shape pinning:** when this becomes worthwhile, the
  right place is a small const-assertion or doctest inside
  `circuit/src/effect_vm.rs` etc., guarding the actual
  `NUM_PUBLIC_INPUTS` against drift. This catches the real failure
  mode (someone changes the circuit, forgets to update downstream
  composers) far better than mirroring the shape in a separate enum.

## Reasoning audit

Decision criteria from the task brief, applied:

| Criterion | Answer |
|---|---|
| Does its output cause anyone to do anything differently? | No. |
| Does it CATCH things that would otherwise slip? | No. |
| Could the same information be a Markdown audit + grep-checks? | Yes, trivially. |
| Is the typed graph itself a useful IR for a real backend? | In principle, but the substrate already has TLA+ and the proof side wants real circuit data, not a hand-written mirror. |
| Healthy investment trajectory to a real soundness statement? | No — every step forward requires throwing the current shape away. |

Net judgment: documentation cosplaying as verification. Delete, keep
the prose elsewhere when someone wants it.
