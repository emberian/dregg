# DECISION — Recursion shape, lookups & ZK for the turn proof

> Sibling to `DECISION-recursion-strategy.md` (which picks the recursion *primitive*).
> This memo decides the recursion *shape* dregg actually needs, plus the lookup and ZK
> decisions for the real prove path. Markers: **[C]** = grounded in code (`file:line`),
> **[A]** = assumption / design claim, **[F]** = from the cited papers.

---

## dregg's constraints ([C] from code vs [A]) — what `prove_full_turn` composes today

The real composition is `sdk/src/full_turn_proof.rs::prove_full_turn` (`:243`). It assembles up
to five sub-proofs and stitches them:

- **[C] Five sub-statements, each its own STARK over the *custom* prover** (`stark::prove`):
  1. Effect VM state transition (`:251-254`), 2. authorization / derivation chain (`:269-291`),
  3. c-list Merkle membership (`:297-322`), 4. conservation (`:332-347` — *no separate proof*,
  just a PI equality check on the Effect VM's `net_delta`), 5. non-revocation Merkle
  non-membership (`:352-368`).
- **[C] The "composition" is classical PI matching, not recursion.** `compose_aggregate` /
  `generate_and_trace` (`:373-388`) builds a *one-row* trace whose columns are the concatenated
  sub-proof public inputs plus sub-proof VK-hashes and `compute_proof_hash` digests. The outer
  STARK proves *consistency of the merged PI row*; it does **not** verify the inner STARKs in
  circuit. Verification (`verify_full_turn`, `:442-582`) re-runs each `stark::verify` on the
  attached sub-proofs *in the clear* and then checks cross-proof PI bindings (e.g. auth
  `state_root == membership root`, effect `old_commit == auth-bound cell`) in plain Rust.
- **[C] Same pattern one level down (per-action) and one level up (bilateral).**
  `circuit/src/effect_vm/per_action.rs` proves a single CallForest action as a real Effect VM
  STARK, then `compose_action_summaries` stitches N of them by checking, *in the clear*:
  commitment chain (`new_commit[i]==old_commit[i+1]`), effects-hash cover, and Σ`net_delta`. Its
  own header calls this "**composed-by-summary**, NOT a single recursive STARK … that is
  Golden-vision algebraic folding." `bilateral_aggregation_air.rs` *does* lift per-cell PIs into
  one outer AIR (CG-2..CG-5), but cross-side existence (CG-5) is still enforced "outside the AIR
  by the prover's schedule-construction logic." So the real shape today is **bounded fan-in,
  summary-glued, non-recursive**.
- **[C] Range / underflow checks are executor-side, NOT in-circuit.** `effect_vm/trace.rs:230`:
  "These checks run at proof generation time. They do **NOT** add constraints to the STARK." The
  balance-limb range tests and per-effect underflow tests (`:241-393`) are `assert!`/error in
  *trace generation*; the comments literally read "executor rejects; STARK constraint would wrap
  in BabyBear" (`:289`, `:302`). A note says a verifier "must additionally verify … final state
  … has valid limb ranges" (`verify_balance_limb_ranges`) — i.e. trust is pushed to the verifier
  re-check, not the proof.
- **[C] A lookup *facility exists but is not a lookup argument*.** `dsl/circuit.rs` defines
  `LookupTable` (`:30`) and `ConstraintExpr::Lookup` (`:162`) with a doc-comment promising a
  "log-derivative (LogUp) or permutation argument" (`:160`). But the actual evaluator
  (`:354-372`) does `table.entries.iter().any(|entry| entry == &query)` → returns `ZERO`/`ONE`.
  That is a **witness-time membership scan**, not a committed running-sum/grand-product. There is
  **no LogUp accumulator column anywhere**, and *every* real circuit ships `lookup_tables: vec![]`
  (descriptors.rs, derivation.rs, revocation.rs, note_spending.rs, fold.rs, … — all empty). So
  range/auth-membership soundness is the *same class* as the executor panics: prover-side, not
  cryptographically enforced.
- **[C] ZK exists but is wired to nothing on the prove path.** `circuit/src/stark_zk.rs` adopts
  Plonky3 `HidingFriPcs` + `MerkleTreeHidingMmcs` (`prove_zk`/`verify_zk`/`create_zk_config`) and
  explicitly states the custom `stark::prove` "is succinct and sound but **NOT** zero-knowledge:
  its FRI query openings reveal raw witness evaluations." Grep confirms `prove_zk`/`HidingFriPcs`
  are referenced **only inside `stark_zk.rs`**; the entire `prove_full_turn` path uses the
  non-ZK `stark::prove`. The synthesis §7 step 7 agrees: "**ZK (port EffectVM onto HidingFriPcs)
  — last.**"
- **[C] The auth binding is narrow.** `binding.rs:8-12`: binding domain is `(action, resource)`
  only; anti-replay (nonce, timestamp) is deliberately excluded. Synthesis §5.3: today auth is
  plain Rust in `authorize.rs` and the proof "binds only (action,resource) and excludes
  auth/replay fields."

**One-line state:** dregg has a *bounded, fixed-arity, summary-glued* composition of five real
STARKs, with range/auth enforced prover-side (no real lookups) and zero ZK on the live path.

---

## Decision 1: IVC vs aggregation — **bounded-depth aggregation, NOT unbounded IVC**

**Decision: dregg's per-turn composition needs BOUNDED-DEPTH AGGREGATION (a fixed small fan-in
of per-action/per-cell proofs combined, optionally under a one-level recursive wrapper). It does
NOT need true unbounded IVC.** The hypothesis is **confirmed.**

### The structural argument (from the code)
A turn is *finite and bounded by construction*: a flattened CallForest of actions, ≤ the five
validity aspects, ≤ N cells in a bilateral bundle. There is **no place in dregg where an
unbounded-length chain must collapse to constant-size proof at runtime** — that would be the
*receipt chain across an entire cell's lifetime*, and the synthesis explicitly does **not** ask
the proof to absorb history: "**within a boundary the log is the manifest truth … across a
boundary the proof is the export format of that log, generated lazily, retroactively, at the
crossing**" (§2.4). The deferred-prover (§6, the keystone) proves a *segment* on demand, not an
ever-growing fold. So the runtime obligation is: combine a **statically-bounded number** of
sub-statements into one verifiable artifact per membrane crossing. That is aggregation, not IVC.

### Why the papers say "don't reach for unbounded IVC"
- **[F] Valiant (TCC'08)** gives IVC only via *CS proofs of knowledge* and only by recursively
  embedding "I have seen convincing π₁ and π₂" — and is *up front* that the recursion already
  breaks the standard random-oracle methodology at the first level ("statements of the form 'M
  with oracle access to O accepts…' — standard applications of random oracles do not appear to
  help"). IVC is *expensive and model-fragile by its nature*.
- **[F] Hall-Andersen & Nielsen (2022/542)** prove Valiant's conjecture: the **standard ROM does
  not allow IVC without computational assumptions** under mild extra conditions — and **one of
  the two sufficient extra conditions is that the proof system is *zero-knowledge*.** This is
  the load-bearing fact for dregg: dregg *wants* ZK (Decision 3) **and** is hash/ROM-based
  (Plonky3 FRI). A *ZK + ROM + unbounded-IVC* system sits exactly inside their impossibility.
  Bounded aggregation sidesteps it entirely — you never recursively absorb an unbounded chain,
  so there is no "verifier knows only genesis, witness arrives incrementally" structure to break.
- **[F] Campanelli–Fiore–Pancholi (2025/1413)** show most practical IVC is only *provably* sound
  at **constant depth**; security does **not degrade gracefully** (no "a little soundness at
  superconstant depth" — they prove that's impossible); polynomial depth rests on *heuristic*
  assumptions. Their *depth-boosting* (secure at d ⇒ secure at d^ρ, black-box, log overhead) is
  the escape hatch *if* dregg ever needs more depth — i.e. start at small bounded depth and boost
  only on demand, rather than assuming unbounded soundness up front.
- **[F] Datta–Jain–Jin–Korb–Mathialagan–Sahai (2025/1546)** get IVC-for-NP from "standard"
  assumptions only via **subexponential iO + LWE** (or trapdoor-IVC languages). iO is not a
  deployable primitive for dregg. This is the *positive* result and it confirms the cost: real
  unbounded IVC for NP is, today, either idealized, knowledge-assumption-based, or iO-based.
- **[F] Ceno (2024/387)** is the *shape to copy*: split execution into **segments**, prove
  segments with **data-parallel circuits**, then a **second stage reconstructs control/data
  flow** from segment proofs — and that second stage "**can be further attested by a uniform
  recursive proof**" (emphasis: *can*, optional). This is precisely dregg's per-action →
  per-turn → per-bundle ladder, and it says the recursive wrapper is an *optional* top, not a
  per-step necessity.

### The concrete shape
- **Per-action / per-cell = real STARKs** (already true: `per_action.rs`, the five sub-proofs).
- **Per-turn aggregation = bounded fan-in.** Replace the *clear-text* summary glue
  (`compose_action_summaries`, `verify_full_turn`'s in-the-clear re-verify) with **one
  bounded-arity recursive/aggregation wrapper** that verifies the fixed set of sub-proofs in
  circuit and outputs one proof. Depth is **1** (a single wrapper level), fan-in is **statically
  bounded** (≤ actions-in-turn, ≤ 5 aspects, ≤ N cells). This is "tree/batch aggregation," the
  cheap regime — *not* a fold chain whose length is data-dependent at runtime.
- **Across the receipt chain = NOT recursion.** Prove a *segment* (deferred-prover) as a bounded
  aggregation, hash-chain segments by `previous_receipt_hash` *in the clear* between membranes.
  If a single succinct proof of a long segment is ever needed, **depth-boost (1413) from the
  bounded wrapper** rather than running unbounded IVC.

---

## Decision 2: lookups for range/auth — **YES, move range + auth-table membership to a real
log-derivative (LogUp) lookup argument; this IS the right unblock**

**Decision: adopt a real LogUp (log-derivative grand-sum) lookup argument and use it for (a)
balance-limb range checks and (b) auth-table / c-list set membership. Prefer LogUp over Lasso for
dregg's small-field FRI STARK; keep Lasso/Jolt as the reference for *what* the tables prove, not
*how* to commit them.** This directly closes the "range checks are executor-side, blocked on
lookup args" gap.

### Why this is the right unblock
- The gap is **[C] real**: range/underflow are `assert!` in trace-gen (`trace.rs:230-393`) and
  the existing `Lookup` constraint is a witness-time scan with no committed accumulator
  (`circuit.rs:354-372`). Both are "trust the prover did the check." A lookup argument is exactly
  the device that turns "I checked membership while building the trace" into "the proof *attests*
  membership" — the cryptographic version of what the code already shapes but does not enforce.
- **[F] Jolt (2023/1217)** is the "lookup singularity" demonstration: a zkVM whose circuits
  *primarily perform lookups* into structured tables (incl. range tables), proven by **Lasso**.
  It shows range/decomposition/ISA-semantics are *natural* lookup workloads — validation that
  dregg's range + auth-membership belong in tables.
- **[F] Lasso (2025/1169 explainer)** is sum-check + multilinear + Spark/Surge sparse-matrix
  commitment + offline memory checking — powerful for *gigantic structured* tables (2^128). But
  Lasso's machinery is **multilinear-PCS / sum-check-native**, which is a different arithmetization
  than dregg's **univariate FRI small-field STARK** (`stark.rs`, Plonky3). Bolting Lasso/Surge
  onto the FRI path is a large impedance mismatch.

### Recommendation (decisive)
1. **[A] Implement LogUp, not Lasso, for dregg.** LogUp (log-derivative lookups) is the
   *univariate-STARK-native* lookup argument: it adds **one committed running-sum column**
   enforcing Σ 1/(x+query) = Σ mult/(x+table) at a Fiat-Shamir challenge. It composes with the
   existing FRI quotient/DEEP machinery and the Plonky3 backend with *no change to the
   arithmetization style*. dregg's tables are **small** (range = 2^30/2^31 limb decomposition;
   auth/c-list = a committed set root) — none need Lasso's 2^128-table sparse-commitment trick.
2. **Range checks → lookups.** Decompose `balance_lo`/`balance_hi` (and per-effect amounts) into
   bytes/limbs and LogUp them against a fixed `[0, 2^k)` table. This *replaces* the `trace.rs`
   asserts with in-circuit constraints — the EffectVM AIR finally enforces "no BabyBear wrap."
3. **Auth-table & c-list membership → lookups (where the set is a *table*, not a path).** Merkle
   *path* membership (current `membership.rs`) stays a hash-AIR. But *small enumerated* auth
   facts (permission-lattice rows, authorized-sender sets, the `Custom { vk_hash }` predicate
   registry — `cell/predicate.rs`) are better as **committed lookup tables** than as per-row hash
   recomputation: one LogUp against the table root beats N Poseidon2 invocations.
4. **Reuse the existing surface.** `ConstraintExpr::Lookup` and `LookupTable` already exist; the
   work is replacing the `.any(...)` scan with a real LogUp accumulator column + boundary
   constraint, and populating `lookup_tables` (today all `vec![]`). This is *additive*, not a
   rewrite — it makes the already-named facility load-bearing.

---

## Decision 3: ZK approach — **port the real prove path onto Plonky3 `HidingFriPcs`; do not
hand-roll masking; never use the FFT-type quotient split**

**Decision: make `prove_full_turn`'s STARKs use the existing `stark_zk::prove_zk` (Plonky3
`HidingFriPcs` + salted `MerkleTreeHidingMmcs`) instead of the non-ZK `stark::prove`. Port AIR by
AIR (EffectVM first), keep the custom prover only for not-yet-ported AIRs and explicitly *not*
advertised as ZK.** This is endorsed by the ZK-for-STARKs note and matches the in-code decision.

### Why
- **[C] The infrastructure is already chosen and justified.** `stark_zk.rs` adopts `HidingFriPcs`
  (PCS `ZK=true`): same `p3_uni_stark::prove`/`verify` entry points automatically (a) double the
  trace with random rows, (b) commit a random FRI batch codeword, (c) salt every Merkle leaf —
  "query openings reveal nothing about the witness beyond the public inputs," "with zero AIR
  changes." The decision *not* to hand-roll is recorded in the module: hand-rolled masking on the
  custom BLAKE3/additive-FRI prover "is a classic soundness footgun."
- **[F] Haböck & Al-Kindi (2024/1037)** is the authority that validates this: ZK-for-STARK is
  "neglected," and they *found real gaps* in the ZK treatment of **Plonky2, Risc-Zero, and
  Triton**. The two pitfalls are (1) base-field witness randomization (manageable) and (2)
  **quotient decomposition** — the **FFT-type split `q(x)=q₀(xᵈ)+x·q₁(xᵈ)+…` is "not amenable to
  randomization" and its simulator analysis is "particularly delicate."** Take-aways for dregg:
  (i) using a *reviewed* hiding PCS (Plonky3) instead of patching the hand-rolled FRI is exactly
  the right call (the named systems all had *protocol-design* gaps); (ii) **if** any custom
  masking is ever added, avoid the FFT-type quotient split; prefer monomial / Lagrange (by-value)
  decomposition. The note's existence is the reason this should be "adopt, don't invent."
- **The IVC linkage (Decision 1).** ZK is one of the two conditions under which 2022/542 makes
  unbounded IVC impossible in the ROM. So **ZK + bounded aggregation** is consistent and safe;
  **ZK + unbounded-IVC-in-ROM** is exactly the forbidden corner. Decision 1 and Decision 3 are
  *mutually reinforcing*: choosing aggregation is what *lets* dregg be ZK without hitting the
  impossibility.

### Recommendation (decisive)
1. **Route the live prove path through `prove_zk`.** EffectVM is the highest-value first port
   (it carries balances/state and is the main leakage surface). Then derivation/membership/
   revocation. The aggregation wrapper (Decision 1) must itself be ZK or it re-leaks the
   sub-proof PIs.
2. **Keep `stark::prove` for un-ported AIRs but flag it non-ZK** (as the module already says).
3. **Hard rule: no FFT-type quotient decomposition in any masked path** (per 1037 §intro). If a
   masked custom path is ever needed, use Lagrange/by-value decomposition and the BSCR+19 masking
   step verbatim.

---

## What to build (concrete, per decision)

**D1 — bounded aggregation wrapper (depth 1, static fan-in):**
- Replace the clear-text glue in `sdk/src/full_turn_proof.rs::verify_full_turn` (`:442-582`) and
  `effect_vm/per_action.rs::compose_action_summaries` with **one recursive/aggregation AIR** that
  verifies the bounded set of sub-proofs in circuit and emits a single proof. Reuse the
  `bilateral_aggregation_air.rs` "PIs-as-columns + expected-projection" pattern — it is already
  90% of an aggregation AIR; the missing piece is *verifying the inner proof* (not just its PI
  row). Couple to the deferred-prover (§6 keystone): segment → bounded-aggregate → hash-chain.
- Do **not** build a runtime fold whose length is data-dependent. If long-segment succinctness is
  needed, implement **depth-boosting (1413)** on top of the depth-1 wrapper.

**D2 — real LogUp:**
- Add a LogUp running-sum column + Fiat-Shamir challenge to the DSL prover; replace
  `ConstraintExpr::Lookup`'s `.any()` scan (`dsl/circuit.rs:354-372`) with the accumulator
  constraint + boundary check.
- Add a fixed range table (`[0,2^k)`) and limb-decompose balances; populate `lookup_tables`
  (currently all `vec![]`) in `effect_vm` and the auth descriptors. Delete the corresponding
  `trace.rs:230-393` "executor-side" asserts once the in-circuit range holds (improve, don't keep
  both — per MEMORY "Improve Don't Degrade").
- Move small enumerated auth/permission-lattice/predicate-registry sets to committed lookup
  tables; keep tree-shaped c-list as the Merkle hash-AIR.

**D3 — ZK port:**
- Switch EffectVM proving in `prove_full_turn` to `stark_zk::prove_zk`/`verify_zk`; cascade to the
  other four AIRs and the D1 wrapper. Add an adversarial test that two proofs of the *same*
  statement with *different* witnesses are indistinguishable in their openings (ZK regression).
- Audit every masked path against 1037: assert no FFT-type quotient split is used.

---

## Risks & open questions to confirm in code

- **[A→C] Does Plonky3's `HidingFriPcs` actually accept dregg's EffectVM AIR unchanged?**
  `stark_zk.rs` claims "zero AIR changes," but the live path uses the *custom* `stark`/`plonky3`
  prover — confirm `EffectVmAir` is expressible as a `p3_uni_stark` AIR (it may already be via
  `effect_vm_p3_air.rs`; verify that file is the same constraint system).
- **LogUp soundness across the small field.** BabyBear is ~31 bits; the LogUp challenge must come
  from the *extension* field (as `binding.rs:16-20` already worries: a single BabyBear element is
  only ~2^15.5). Confirm the challenger draws extension-field challenges for the grand-sum.
- **Aggregation-wrapper recursion needs in-circuit FRI verification.** `stark_zk.rs` already has
  `FriVerifierGadget`/`RecursiveFriAir` (CG-1) but with an **honest residual**: BLAKE3 Merkle
  paths are checked *natively*, not as AIR constraints. Confirm whether the D1 wrapper can lean
  on CG-1 as-is, or whether porting inner proofs to a Poseidon2/algebraic-hash Merkle (so the
  path *is* in-AIR) is a prerequisite. This is the single biggest unknown for "true" depth-1
  recursion vs. continued summary-glue.
- **Binding scope.** `binding.rs` excludes nonce/timestamp; the aggregation wrapper is the place
  to also bind `turn_hash`/`previous_receipt_hash`/`actor_nonce` (bilateral CG-2 already lifts
  these) so replay is in-proof, closing the §5.3 auth-in-proof gap simultaneously.
- **Conservation is still a PI equality, not a proof** (`full_turn_proof.rs:332-347`); Pedersen
  range proofs live over Ristretto and "cannot be composed into BabyBear STARK." Confirm whether
  D2's range lookups can subsume the field-value conservation case and leave only the committed
  (Pedersen) case out-of-band.
