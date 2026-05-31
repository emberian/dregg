# PHASE-EXTRACTION — How the verified dregg2 kernel RUNS as the production node's decision-maker

> **Status:** design map + evidence-based comparison for "the swap" — replacing dregg1's Rust turn-executor with the verified dregg2 kernel. READ-ONLY study. No code modified.
>
> **Scope:** This phase sits at the seam dregg2 §8 (the Rust boundary hosts the verified kernel). Everything below the seam (`Dregg2.Exec.*`, proved) is settled; everything above it (the node's turn loop) is dregg1 Rust. The question is the *mechanism of contact*: when a turn arrives, **which code computes the commit/reject decision and the post-state**, and how does that code inherit the proofs?
>
> Two paths:
> - **Path A — compiled Lean** behind a C-ABI FFI. The node links `libdregg_lean.a` and calls the same `exec`/`recKExec` whose `exec_conserves`/`exec_authorized` are proved. dregg2 already does this for a narrow surface.
> - **Path B — hand-written Rust** matching the kernel, kept honest by a differential + fuzzer + benchmarks against the compiled-Lean oracle. This is the owner's eventual two-impl world.

---

## 1. The existing FFI surface (what is real today)

Read in full: `metatheory/Dregg2/Exec/FFI.lean`, `dregg-lean-ffi/{Cargo.toml,build.rs,src/lean_init.c,src/main.rs,src/differential.rs,src/state_differential.rs}`.

### 1.1 What is actually `@[export]`-ed

Exactly **six** `@[export]` definitions exist in the whole Lean tree (`grep -rc '@\[export'` → only `FFI.lean:6`). Confirmed against the shipped archive (`nm libdregg_lean.a | grep ' T '`):

| Lean symbol (`FFI.lean`) | C symbol | Signature | Proved function underneath |
|---|---|---|---|
| `transferTotal` (`:25`) | `dregg_kernel_transfer_total` | `(u64,u64,u64) → u64` | `Exec.exec` (scalar 2-account) — `exec_conserves` |
| `authorized` (`:41`) | `dregg_kernel_authorized` | `u64 → u8` | `Exec.authorizedB` in isolation — `exec_authorized` |
| `recordTransferTotal` (`:57`) | `dregg_record_kernel_transfer_total` | `(u64,u64,u64) → u64` | `Exec.recKExec` (record cell, balance field only) |
| `recordKernelStep` (`:368`) | `dregg_record_kernel_step` | `String → String` | `Exec.recKExec` over a marshalled `RecordKernelState`, **empty caps** |
| `recordKernelStepCaps` (`:642`) | `dregg_record_kernel_step_caps` | `String → String` | `Exec.recKExec` over `RecordKernelState` **+ the `Caps` table** |

(The C-string bridges `dregg_record_kernel_step_str` / `..._caps_str` in `lean_init.c` are plain C wrappers around the two `String→String` exports — they box/unbox the Lean `String`, which is a `lean_object*`, because `lean_mk_string`/`lean_string_cstr` are `static inline` and have no linkable symbol.)

**Is it a real extracted step function, or a hand-mirrored Rust reimplementation checked against Lean?**
Both, deliberately. The **Lean side is the genuine compiled artifact** — `recordKernelStepCaps` decodes the wire, runs the actual `Exec.recKExec` (the same function carrying `recKExec_conserves`/`recKExec_authorized`/`recKExec_unauthorized_fails`, `RecordKernel.lean:168/185/194`), and re-encodes. There is no reimplementation on the Lean side. The **Rust side is a hand-mirror** (`state_differential.rs`: `ref_rec_k_exec`, `ref_rec_k_exec_caps`, `ref_authorized`) that exists *only as the differential's reference oracle*, not as a production component. So today's harness is "real compiled Lean **vs** hand-Rust mirror," which is exactly the Path-B differential pattern run in miniature — with the Lean artifact as oracle.

### 1.2 How `libdregg_lean.a` is built and linked

- The archive is **247 MB** (`ls -lh`), a single static lib of the native objects the Lean compiler emits for `Dregg2.Exec.FFI` **and its entire transitive closure** — Dregg2 modules + mathlib + batteries + aesop + Qq, ~8200 `.o` (per `build.rs:5-8` and README). Produced by compiling each module's `:c` facet with `leanc -c` and archiving with `llvm-ar`. The README explicitly says **do not rebuild** (very slow); after changing an `@[export]` only the ~9-module `Dregg2` closure of `FFI` is recompiled and spliced in with `ar r`.
- `build.rs` links: (a) our archive `static=dregg_lean`; (b) the Lean runtime + stdlib discovered via `lake env printenv LEAN_SYSROOT` with a pinned fallback (`leanc`, `Init`, `Std`, `Lean`, `leanrt`, `Lake`, `gmp`, `uv`, `static`); (c) `dylib=c++`. Toolchain pinned at **Lean 4.30.0** (`lean-toolchain`).
- `lean_init.c` compiles via the `cc` crate into a shim exposing `dregg_ffi_init()`, which runs the embedding ritual: `lean_initialize_runtime_module()` → `initialize_Dregg2_Dregg2_Exec_FFI(1)` → check the `IO` result → `lean_io_mark_end_initialization()`.

### 1.3 What the differential actually exercises

`state_differential.rs` (`default-run` is the scalar `differential.rs`):
- **Phase 1** — 10,000 single-field `{balance}` record cases.
- **Phase 2** — 10,000 multi-field `{balance,nonce,owner}` cases (non-balance fields must survive untouched).
- **Phase 3** — 10,000 held-cap cases, marshalling the `Caps` table and exercising the cross-vat authority branch, plus +40,000 value round-trips, plus two named witnesses (`WITNESS A` write-endpoint holder commits, `WITNESS B` read-only holder rejects). README reports **30000/30000 step cases agree**.

This is the "50k/50k record+caps" the project memory refers to (it is 3×10k step cases + 40k value round-trips ≈ the 50k figure; the headline is 30k step cases + 40k round-trips).

**Input distribution — honest read (this is the load-bearing weakness):**
- The PRNG is a fixed-seed xorshift64\* (`differential.rs:71`, `state_differential.rs:566`) — **reproducible, not adversarial**.
- Balances are bounded to `2^40` "so the reference sum is exact" (`differential.rs:84`, `state_differential.rs:578`) — **this deliberately avoids the overflow/edge regime**, exactly where a hand-Rust kernel would diverge from Lean's unbounded `ℤ`.
- Cell topology is fixed: **always two cells, ids 0 and 1** (`state_differential.rs:600,612`). No 1-cell, 0-cell, 3+-cell, duplicate-id, or self-transfer-into-absent-cell shapes.
- The cap regimes are a hand-enumerated 7-way `match` (`state_differential.rs:623`), good coverage of the *authority* axis but a *small fixed* set, not a generated cap lattice.
- The scalar `differential.rs` is even thinner: its Rust reference is `bal_a + bal_b` with a comment proving `amt` is irrelevant — it is checking a tautology of conservation, not the transition.

So today's differential is **structured-random over a narrow, overflow-safe, fixed-topology domain**. It is a strong *cross-validation of the codec and the authority gate*, and an honest *cross-validation of `recKExec` on the happy path*. It is **not** a fuzzer and **not** adversarial.

### 1.4 Is there a fuzzer anywhere?

`grep` for `proptest|quickcheck|cargo-fuzz|libfuzzer|fuzz_target|arbitrary` across the repo: **32 files**, all in the *dregg1 Rust workspace* (`protocol-tests/`, `turn/tests/proptest_invariants.rs`, `cell/tests/proptest_nullifier.rs`, `tests/src/adversarial_boundaries.rs`, `dregg-dsl-runtime/`). **None of them touch the Lean FFI.** The `dregg-lean-ffi` crate pulls zero proptest/fuzz dependencies (`Cargo.toml` deps: `blake3`, build-dep `cc`). So there is proptest infrastructure *in the project*, but **no fuzzer is wired to the Lean oracle today**.

---

## 2. Compiled-Lean viability (Path A)

### 2.1 What it takes to run compiled Lean in production

The init ritual already exists and is proven to work (`lean_init.c:26`, called once from each Rust `main`). In a long-lived node it is a one-time startup cost. The per-turn call shape is `dregg_record_kernel_step_caps_str(wire_in, out_buf, cap)` → re-grow on truncation → decode. The runtime is the Lean RC-GC runtime (`leanrt`) + gmp (for `Nat`/`Int` bignum) + libuv.

### 2.2 The per-call overhead shape (honest)

A turn through Path A pays, per call:
1. **Marshalling**: serialize node state → canonical JSON wire (Rust), `lean_mk_string` (one heap alloc + memcpy of the whole wire), the Lean recursive-descent parser allocating a `List Char` and the `Value`/`Caps` trees, run, re-encode to `String`, `memcpy` back, `lean_dec_ref`. This is **O(state size) allocation churn on every turn**, on both sides, dominated by the `List Char` parser (`FFI.lean:146` `PState := List Char` — a cons-list, not a slice).
2. **Reference counting**: every `Value`/`List`/`String` node is an RC-managed `lean_object`; allocation and decref are per-node.
3. **Bignum**: `Int`/`Nat` payloads go through gmp.

The transition logic itself (`recKExec`) is trivially cheap; **the cost is entirely the boundary**. Shape: roughly linear in the marshalled state, with a high constant from allocation. Fine for kilobyte-scale per-turn state at human/transaction rates; a concern at high turn throughput with large hot state.

### 2.3 Showstoppers — assessed honestly

| Concern | Verdict | Detail |
|---|---|---|
| **One-time init** | Not a blocker | `dregg_ffi_init()` once at node startup; already works. |
| **GC pauses** | **Minor, not a stop-the-world showstopper** | Lean uses **per-object reference counting** (not a tracing/generational GC); reclamation is deterministic and incremental at decref. There is no global GC pause. The cost is steady per-node RC traffic, not pause spikes. |
| **Thread-safety / single-threaded runtime** | **The real constraint** | The Lean runtime is initialized once; objects are RC'd with atomic vs non-atomic refcounts depending on multi-threading mode. A multi-threaded node calling the kernel from many worker threads must either (a) treat the kernel as a single-threaded actor (serialize turns through one thread — fits a turn-executor that is already a serialization point), or (b) ensure the runtime was brought up in the thread-safe mode and that shared `lean_object*` are handled correctly. The current shim brings the runtime up with the default ritual and is exercised single-threaded. **This is the item to verify before trusting Path A under a multi-worker node.** |
| **Marshalling cost** | **Manageable but real** | The `List Char` parser is the wart; it is O(n) allocations. A production Path A should narrow the wire (binary, or at least a slice-based parser) — but note the codec is TCB either way (see §5). |
| **Binary size** | **Cosmetic but loud** | 247 MB static archive (mathlib closure). The node binary inherits this. Not a correctness issue; an ops/footprint one. Mitigation: dead-strip, or extract a thinner closure once the kernel modules stabilize. |
| **Embedding a 247MB mathlib-closured artifact in a shipping node** | **Acceptable for the swap, ugly long-term** | Works today; the long-term answer is to shrink the closure or move to Path B once mature. |

**Bottom line:** the node *can* embed `libdregg_lean.a` and call the kernel step per turn **today**, for the record-cell single-transfer + caps surface. The only genuine pre-flight check is the **multi-threading / runtime-mode** question; everything else is performance-tuning and footprint, not a showstopper. There is no GC-pause showstopper because Lean's memory model is RC, not tracing.

---

## 3. Hand-Rust + differential viability (Path B)

### 3.1 What a hand-written Rust kernel needs

A faithful Rust re-statement of: `authorizedB` (ownership + node-cap + write-endpoint-cap), `recTransfer` (debit/credit), the fail-closed `recKExec` commit gate (authorized ∧ `0 ≤ amt ≤ balOf src` ∧ `src ≠ dst` ∧ both live), the all-or-nothing fold `execTurn`, and — for the *full* turn — `execFull` over `FullAction` (transfer/mint/burn/delegate/revoke) with the `ledgerDelta` conservation gate and the receipt-chain (`ObsAdvance`/`ChainLink`) bookkeeping. `state_differential.rs` already contains a faithful Rust mirror of the *single-transfer + caps* slice, so the shape is known; the full-turn surface (mint/burn/delegate, multi-action fold, receipt chain) is **not yet mirrored**.

### 3.2 The maintenance / soundness cost

- **The whole Rust kernel becomes TCB until the differential closes** (see §5). Every divergence the differential never samples is an unproved gap.
- The Rust must track Lean's **unbounded `ℤ`** semantics with bounded `i64`/`i128` — the overflow regime the current harness deliberately avoids (`2^40` bound). A real Path-B kernel must either use bignum in Rust or prove the bound never trips, and the differential must *fuzz that boundary* specifically.
- Every change to a Lean kernel def (new effect kind, new cap rule) must be re-mirrored in Rust and re-differentiated. Two artifacts, one of them unproved, kept in sync by a test suite.

### 3.3 What coverage would be needed to trust a hand-Rust kernel

The current differential is necessary but **far from sufficient**. To trust Path B against the Lean oracle you would need:
1. A **real fuzzer** (cargo-fuzz/libfuzzer or proptest with `arbitrary`) generating: variable cell counts (0,1,2,N), duplicate ids, absent src/dst, `amt < 0`, `amt` at and past `balOf src`, `amt` near `i64::MAX` (the overflow boundary), `src == dst`, deeply nested `Value` records, adversarial cap lattices (every `Cap`/`Auth` combination, wrong-target caps, multiple holders), and malformed wires for the codec.
2. The **full-turn surface**, not just single transfers: multi-action `execTurn` folds (partial-failure rollback), mint/burn `ledgerDelta` (disclosed non-conservation), delegate/revoke cap mutations.
3. **Structural coverage / corpus-minimization** evidence that the fuzzer actually reaches every branch of `recKExec`/`authorizedB`/`execFull`.
4. **Benchmarks** establishing the Rust path is actually faster than Path A (the whole point of Path B), against the same oracle.

The infrastructure exists in-tree (proptest is already used in `turn/`, `cell/`, `protocol-tests/`) — it is *not wired to the FFI oracle*. That wiring is the missing piece for Path B.

---

## 4. The extracted-code gap — what is NOT yet exported

The exports today cover **one `recKExec` step** (single transfer) ± caps. The node's **full turn decision** is a different, larger function. Enumerating the kernel surface and its export status:

| Kernel function | File | Role | `@[export]` today? | Needs one for full-turn swap? |
|---|---|---|---|---|
| `authorizedB` | `Kernel.lean:54` | authority gate | yes (in isolation, `dregg_kernel_authorized`) | already reused inside the step exports |
| `exec` (scalar) | `Kernel.lean:69` | toy 2-account step | yes (`transferTotal`) | no (superseded by record) |
| `recKExec` | `RecordKernel.lean:122` | record single-transfer step | **yes** (`recordKernelStep[Caps]`) | covered |
| `recCexec` | `RecordKernel.lean:237` | step + receipt-chain extend (attests `recFullStepInv`) | **no** | **yes** — this is the step that attests all 4 StepInv conjuncts incl. ChainLink/ObsAdvance |
| `execTurn` | `TurnExecutor.lean:118` | **all-or-nothing multi-`Action` fold** | **no** | **yes** — the transaction unit; the real turn |
| `execFull` | `TurnExecutorFull.lean:280` | single `FullAction` (transfer/mint/burn/delegate/revoke) | **no** | **yes** — needed for non-transfer effects |
| `execFullTurn` | `TurnExecutorFull.lean:290` | **multi-`FullAction` turn fold** | **no** | **yes** — the *complete* turn decision-maker |
| `recCMint`/`recCBurn`/`recCDelegate`/`recCRevoke` | `TurnExecutorFull.lean:223-242` | the effect primitives | **no** | yes (reached via `execFull`) |
| `recFullStepInv` / `fullStepInv` | `RecordKernel.lean:245`, `StepComplete.lean:65` | the 4-conjunct StepInv *predicate* | n/a (a `Prop`) | **no** — a `Prop` is not runnable; it is *attested by construction*, not checked at runtime |

**Key correction to a common misconception:** there is no separate "run the StepInv check" to export. `recFullStepInv` is a `Prop`, proved to hold of every `recCexec`/`execTurn` commit *by construction* (`recCexec_attests`, `RecordKernel.lean:256`; `execTurn_each_attests`/`_conserves`/`_all_authorized`, `TurnExecutor.lean:147/186/168`). The node does **not** run a checker; it runs `execFullTurn` and *inherits* the four conjuncts because they are theorems about that function. So the export surface for the swap is the **executors**, not a validator.

### 4.1 Minimal extraction surface for the swap (the precise list)

To run a full turn through compiled Lean, export (in `FFI.lean`, same wire-codec discipline already established):

1. **`dregg_exec_full_turn(input: String) → String`** — wraps `execFullTurn` over a `RecChainedState`. This is the one function that *is* the turn decision-maker. It transitively pulls in `execFull`, `recCexec`, `recKExec`, `recCMint/Burn/Delegate/Revoke`, `authorizedB`, and the receipt-chain — all proved. Its commit attests Conservation (`execFull_conserves`, `TurnExecutorFull.lean:359`) + Authority + ChainLink + ObsAdvance by construction.

The wire must grow from the current `{cells,caps,actor,src,dst,amt}` to carry a **list of `FullAction`** (each: method tag, `EffectKind`, the `Turn` move) and to return the **post-`RecChainedState`** (cells + the appended receipt log). The codec discipline is the same recursive-descent JSON already in `FFI.lean`; it is additive.

That single export is the swap. Everything below it is already proved and already in the archive's transitive closure. Optionally, for finer-grained migration:

2. `dregg_exec_turn` (the transfer-only `execTurn` fold) — a strictly smaller first step than the full `FullAction` set, useful as the *first verifiable increment* (§6).

---

## 5. Where the TCB sits in each path

The verified kernel functions are **not** TCB — they carry machine-checked proofs (`exec_conserves`, `recKExec_*`, `execTurn_*`, `execFull_*`, all with `#assert_axioms` tripwires, `RecordKernel.lean:295`). What sits *outside* the proofs is the TCB. It differs sharply between the paths.

### Path A (compiled Lean) TCB
- **The codec / marshalling** (`encode*`/`parse*` in `FFI.lean` + the matching Rust codec). The README states this plainly: *"This codec is TCB, not proved."* A codec bug can feed the proved kernel a wrong state and get a wrong-but-conserved answer for the wrong inputs.
- **The C embedding shim** (`lean_init.c`) — pointer/length/refcount discipline, buffer truncation.
- **The Lean compiler + runtime** (`leanc`, `leanrt`, gmp) — trusted to compile the proved term faithfully. This is the standard "trust the extractor" assumption (analogous to CompCert/Coq-extraction trust).
- **The build provenance of `libdregg_lean.a`** — that the 247MB archive really is the compilation of the proved sources at the pinned toolchain, not a stale/tampered blob. (A reproducible-build check would shrink this.)

### Path B (hand-Rust) TCB
- **Everything in Path A's TCB** (codec, compiler — because the Lean oracle is still compiled Lean), **plus**
- **the entire hand-written Rust kernel**, until the differential+fuzzer closes. Until then, *the running artifact is unproved code asserted-equal to the oracle on the sampled domain only.* The proof guarantee attaches to the oracle, not to what the node runs; the differential is the bridge, and it is only as strong as its input distribution (§1.3, §3.3).

**The decisive asymmetry:** in Path A the *running artifact is the proved term* (modulo compiler/codec). In Path B the *running artifact is unproved* and the proofs apply only transitively through a test suite. Path B's TCB strictly contains Path A's and adds the whole kernel.

---

## 6. Recommendation

**For the swap itself: Path A (compiled Lean), extended to the single `dregg_exec_full_turn` export.**

Reasoning:
- **It loses no verification guarantee.** The node runs the proved term. The four StepInv conjuncts hold by construction of `execFullTurn`; there is nothing to re-validate at runtime.
- **The mechanism already works end-to-end** — init ritual, archive, link, string bridge, 30k/30k differential. Extending from `recKExec` to `execFullTurn` is *additive codec work on an established seam*, not new infrastructure.
- **No real showstopper** (§2.3): RC memory model (no GC pauses), one-time init, manageable marshalling. The single pre-flight is the multi-threading/runtime-mode check, which a serialized turn-executor satisfies trivially.
- **Path B's whole value is performance**, and **you cannot trust a Path-B artifact without first having the Path-A oracle running and a real fuzzer wired to it** — neither of which gates Path A. Path B is strictly downstream of Path A.

This matches the owner's stated end-state: *Lean-oracle = source of truth; a fast Rust path validated by differential+fuzzer+benchmarks — but only after dregg2 is mature.* The sequencing falls out:

1. **Swap on Path A.** The node calls compiled Lean. Verification guarantee intact from day one.
2. **Mature dregg2** (the kernel surface stabilizes; effects/caps stop changing weekly).
3. **Wire a real fuzzer to the Path-A oracle** (cargo-fuzz/proptest, the adversarial domain of §3.3). The Path-A node is the oracle; the fuzzer hammers a candidate Rust kernel against it.
4. **Benchmark** the Rust path; only adopt it where it is *both* differentially-closed-under-fuzzing *and* measurably faster.
5. **Path B replaces Path A on the hot path** only after (3)+(4), keeping Lean as the CI oracle forever.

Doing Path B *first* would mean shipping unproved code and *hoping* the (currently non-adversarial, fixed-topology, overflow-safe) differential caught the divergences — degrading the guarantee for a performance win you have not yet measured. That is the "debt hole" the project's own guidance warns against.

---

## 7. Smallest first verifiable increment

**Export `execTurn` (transfer-only, all-or-nothing multi-action fold) and run a single multi-action turn through it from Rust.**

Concretely:
1. Add `@[export] dregg_exec_turn (input : String) : String` in `FFI.lean`, wrapping `TurnExecutor.execTurn` over a `RecChainedState`. Wire grows to carry a *list* of moves and to return the post-state cells **+ the receipt-log length** (so `ObsAdvance`/`ChainLink` is observable across the seam).
2. Recompile only the ~9-module `Dregg2` closure of `FFI` and splice the new `.o` into `libdregg_lean.a` (the README's `ar r` recipe; mathlib objects reused).
3. Extend `state_differential.rs` with a **phase 4**: random *multi-action* turns (including a deliberately-failing middle action to exercise all-or-nothing rollback), Lean `execTurn` vs the Rust `ref` fold, asserting the post-state, the commit bit, **and** the log length.
4. Assert the two boundary witnesses: a turn whose 2nd of 3 actions is unauthorized → whole turn rejects, state + log unchanged (fail-closed rollback); an all-authorized turn → all commit, log grows by the action count.

This is the smallest step that (a) exercises a *real multi-step turn* (not a single transfer), (b) crosses the receipt-chain conjuncts (ChainLink/ObsAdvance), and (c) reuses the entire existing seam additively. It is the direct on-ramp to the full `dregg_exec_full_turn` export, which is the swap.

**The single sharpest near-term improvement, independent of which path:** wire a real fuzzer (cargo-fuzz or proptest+`arbitrary`) to the existing FFI oracle and aim it at the adversarial domain (§3.3) — variable topology, the overflow boundary, malformed wires, the full cap lattice. Today's 30k/30k is fixed-seed structured-random over an overflow-safe two-cell domain; it cross-validates the codec and authority gate well but is **not** the adversarial coverage either path ultimately needs. This fuzzer is a prerequisite for ever trusting Path B, and it hardens the Path-A codec (the one piece of Path A that *is* TCB) in the meantime.

---

## 8. Summary

- **Today:** 6 `@[export]`s (`FFI.lean`), all real compiled Lean; a 247MB archive linked via `build.rs`/`lean_init.c`; a 30k/30k differential (single-transfer + caps) that is strong cross-validation but **fixed-seed, fixed-topology, overflow-safe, non-adversarial**; **no fuzzer wired to the oracle**. The Lean side is the genuine kernel; the Rust side is a differential mirror, not a production component.
- **Path A** runs the proved term in the node. No GC-pause showstopper (RC memory model). One real pre-flight: multi-threading/runtime-mode. TCB = codec + shim + Lean compiler + archive provenance.
- **Path B** runs unproved Rust validated only through a test suite; its TCB contains Path A's *plus the whole Rust kernel*; trustworthy only after a real fuzzer + benchmarks, and only after dregg2 matures.
- **Recommendation:** swap on **Path A**, exporting the single `dregg_exec_full_turn` (`execFullTurn`); move to Path B later, behind a fuzzed differential and a benchmark, keeping Lean as the eternal oracle.
- **First increment:** export `execTurn`, add a multi-action rollback differential phase; in parallel, wire a real adversarial fuzzer to the existing oracle.

> End of PHASE-EXTRACTION. The proofs live below the seam; the question was only how the node touches them. The honest answer is: touch the proved term directly (Path A) for the swap, and earn the right to a faster unproved twin (Path B) the slow way — with a fuzzer and a benchmark — afterward.
