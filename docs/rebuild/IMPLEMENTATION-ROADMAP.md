# IMPLEMENTATION-ROADMAP — the staged, braided plan from "ready-now Lean fills" to "the gated swap"

> **Status:** the plan ember and the agents steer the implementation from. Synthesized
> (READ-ONLY, no code changed) from the four assessment docs written this session —
> `SWAP-READINESS.md`, `DREGG2-GAP-MAP.md`, `APPS-READINESS.md`, `DOWNSTREAM-READINESS.md`
> — plus the live task ledger (E1–E6 done: full effect catalog executable+proved #98–104,
> FFI export #95, proof-forest #101/#102, caveat/attestation carry-forward #122/#124,
> consistency witness #126, zero-sorry+CI #128 in flight).
>
> **THE SWAP FRAMING (binding, do NOT violate — repeated because it is the spine of this doc):**
> deleting dregg1's Rust kernel and routing the node through the Lean FFI is a **MASSIVE
> staged rewrite, NOT an FFI drop-in.** It is gated on (1) the executor being complete,
> (2) the FFI hosting a *real* turn, and (3) the **differential as the safety net —
> kernel-vs-new-Rust, NEVER vs. the buggy old dregg1** (matching a buggy oracle launders
> the bug). This roadmap recommends **no blind deletion**: every wave is *addition +
> oracle-gate*, deletion is dead last and fully gated.

---

## 0. The braid, in one breath

ember demanded a **braid**: every implementation wave is paired with a verification wave —
*implement → verify/adversarially-correct → next*. Nothing advances on an unverified step.
The braid has two strands and one gate:

```
  STRAND A (ready-now): Lean+FFI fills — no node code touched, no swap
  ════════════════════════════════════════════════════════════════════
   WAVE 0  Lean/FFI core fills        (per-asset · escrow/note · constraints · handler · WAL)
              │  each paired with its own verify-braid (proof + adversarial differential)
   WAVE 1  FFI/Rust-Lean interface     (export more of the kernel · harden the differential RATCHET)
              │
  ╔═══════════════════════════════════ THE SWAP GATE ═══════════════════════════════════╗
  ║  Below this line: no production node/SDK code routes through Lean.                    ║
  ║  Above it: we begin RE-WIRING (addition + oracle-gate), never deletion, behind        ║
  ║  the differential. Crossing requires the WAVE-1 ratchet GREEN in CI + WAVE-0          ║
  ║  soundness fills landed (per-asset vector + escrow/note in the executable turn).      ║
  ╚══════════════════════════════════════════════════════════════════════════════════════╝
   WAVE 2  FIRST SAFE REWIRING         (shadow ONE real turn-decision through Lean; observe-only)
              │
   WAVE 3  FIRST STARBRIDGE-APP        (nameservice on the Lean kernel, differentially pinned)
              │
   WAVE 4  THE GATED SWAP              (canary → primary → DELETE Rust kernel — only after the ratchet)
              │
   WAVE 5  DOWNSTREAM                  (SDK backend boundary · node sites · wasm-stays-Rust · authorizer seam)
```

**The single critical-path insight (from the GAP-MAP):** FILL 1 (per-asset conservation
vector) changes the **conserved measure** that every other fill re-proves its conservation
against. Do it FIRST or CONCURRENT in WAVE 0, or the spine gets re-proved twice (once over
scalar `recTotal`, once over the vector). This ordering is load-bearing.

---

# STRAND A — READY-NOW (no swap; Lean + FFI fills, each self-braided)

These waves touch **only** the Lean metatheory and the detached `dregg-lean-ffi` PoC crate.
No `node`/`turn`/`sdk` production code changes. They are safe to run in parallel lanes; the
only intra-strand ordering constraint is **FILL 1 leads**.

## WAVE 0 — the ready-now Lean/FFI core fills

The meta-fill behind 0.1/0.2/0.6/0.7: **widen `FullAction` + `execFull` into the genuine
effect core and re-prove the conservation/authority/forward-sim spine over the wider sum.**
Most fills below are facets of it; each already proved in isolation, so this is *re-binding
proved lemmas to a wider dispatch*, not greenfield theory.

---

### 0.1 — Per-asset conservation VECTOR (the #1 soundness gap) · LEADS THE WAVE

- **Deliverable.** Generalize the executable kernel from conserving **one scalar** to
  conserving **per-asset-class** (`AssetId`-indexed). A scalar kernel accepts a turn that
  mints asset B while burning equal asset A — sound-looking, per-asset-violating; dregg is
  multi-asset, so the scalar kernel is *unsound as a replacement*.
- **File surface (Lean).** Generalize `RecordKernel.balOf`/`recTotal`/`recKExec`
  (`metatheory/Dregg2/Exec/RecordKernel.lean:47,104,208`) and every effect's debit/credit
  from the single `"balance"` field to an asset-indexed map; re-thread `TurnExecutorFull.lean`
  and the FFI codec (`FFI.lean:58-71,369,936`). **The correct law already exists, unintegrated:**
  `MultiAsset.lean:46` (`bal : MACellId → AssetId → ℤ`) + keystone
  `maExec_conserves_per_asset` (`:130`). The work is *porting that template onto the record
  kernel* and re-binding downstream lemmas.
- **Verify-braid.**
  1. *Proof:* per-asset `recKExec_conserves` over the record kernel; a forward-sim that the
     abstract `Spec` step conserves *each* asset class.
  2. *Adversarial differential (the teeth):* exhibit a **scalar-conserving-but-per-asset-violating**
     turn that the new kernel REJECTS — the negative test is what proves it is not the old
     scalar law wearing a vector hat. Land it in `full_turn_differential.rs`.
- **Dependency.** None — but it **gates the conserved measure** of 0.2/0.6/0.7. Do it first.
- **Size.** Large. **Criticality.** SOUNDNESS-CRITICAL (the single biggest). **Task:** new
  (FILL 1; no existing task id).

---

### 0.2 — Escrow holding-store + note nullifier-set INTO the executable turn

- **Deliverable.** Widen `FullAction` so the FFI's `execFullTurn` can actually *perform* an
  escrow lock / settle / refund and a note spend. Today these semantics are **proved but
  stranded** outside the 5-variant dispatch (`balance/delegate/revoke/mint/burn`); a node
  that can't lock escrow or spend a note is not a dregg successor.
- **File surface (Lean).** Add `createEscrow/releaseEscrow/refundEscrow/noteSpend` (+ obligation
  variants) to `FullAction` (`TurnExecutorFull.lean:255-265`); extend `execFull` (`:280-286`)
  to dispatch to the already-proved chained primitives in `RecordKernel.lean:333-520`
  (`createEscrowK`/`releaseEscrowK`/`refundEscrowK`, `escrow_create_conserves_combined` PROVED)
  and `EffectsPaired.lean:426-680` (`noteSpendChain`, `noteSpend_no_double_spend` PROVED);
  swap the conserved measure to `recTotalWithEscrow` (`RecordKernel.lean:395`); extend the FFI
  wire codec (`FFI.lean:759-936`).
- **Verify-braid.**
  1. *Proof:* `execFullTurn` conserves `recTotalWithEscrow` (combined cell-ledger + holding-store
     + note-supply); double-spend negative threaded through the FULL turn.
  2. *Adversarial differential:* an escrow lock→settle round-trip through the FFI; a
     double-spend that the kernel fail-closes.
- **Dependency.** The conserved-measure choice from 0.1 (`recTotal` → `recTotalWithEscrow` →
  the 0.1 vector). Do **after/with** 0.1 to avoid re-proving twice.
- **Size.** Medium. **Criticality.** INTEGRATION-CRITICAL. **Task:** new (FILL 2).

---

### 0.3 — Committed-escrow + `noteCreate` through the holding-store (close the FID-ESCROW regression)

- **Deliverable.** FID-ESCROW (#116) de-shadowed plain escrow/obligation/note-*spend* to the
  real holding-store, but **left the committed-escrow triple + `noteCreate` on the old
  two-cell-transfer shadow** — the exact failure mode the project already rejected once
  (matching a Lean simplification, not the Rust). Close it.
- **File surface (Lean).** Reuse `EscrowRecord`/`escrows` (`RecordKernel.lean:333-520`) with a
  commitment-typed payload + opening-predicate settle; reuse the nullifier-set for a
  commitment-insert `noteCreateChain`. Today only the header *names*
  `createCommittedEscrow`/… (`EffectsPaired.lean:10-12`) with no holding-store definition. The
  crypto (Pedersen/range proof) stays a `CryptoPortal` hypothesis (`EffectsPaired.lean:48-52`),
  exactly as `noteSpend` carries it.
- **Verify-braid.**
  1. *Proof:* `committed_escrow_create_conserves_combined` (same combined-total law);
     `escrow_obligation_committed_note_are_distinct` (extend the de-conflation theorem
     `EffectsPaired.lean:626` to the committed triple + noteCreate).
  2. *Adversarial:* a `noteCreate → noteSpend` round-trip conserving the note supply; a
     committed-escrow that does NOT collapse to a balance-conserving two-cell transfer.
- **Dependency.** 0.2's holding-store integration. **Size.** Small-Medium.
  **Criticality.** FIDELITY (regression). **Task:** #121 (FID-COMMITTED-NOTE, pending).

---

### 0.4 — `StateConstraint` vocabulary 16 → ~74 (the storage cell-programs need it)

- **Deliverable.** Grow the Lean `StateConstraint` catalog (~16 variants today) toward the
  Rust evaluator's 74, adding the ones the storage cell-program templates need and that the
  apps' base flows touch. A `RelayOperator` whose `BoundedBy` bond-bound and `RateLimitBySum`
  quota are *unevaluated* (return `true`) is an unenforced economic cell-program — the
  "moved-complexity" trap.
- **File surface (Lean).** Add the missing variants (`RateLimit`/`RateLimitBySum`,
  `SenderAuthorized`, `WitnessedPredicate`, `TemporalGate`, `PreimageGate`, `BoundedBy`) to
  `StateConstraint` (`Program.lean:55-103`) and give each a *real* `eval` (`:110-160`) — note
  `boundDelta` is DECLARED but its evaluator returns `true` (`Program.lean:99-102`). Bind
  `SenderAuthorized` to a sender-set; discharge `WitnessedPredicate` through the existing
  registry (`Authority/Predicate.lean`). Close the `CapInbox` `SenderAuthorized → sender_set_root`
  `-- OPEN:` (`CapInbox.lean:318-325`).
- **Verify-braid.**
  1. *Proof:* `eval` soundness per new variant; `RelayOperator`/`BlindedQueue` template
     invariants re-proved against the *evaluated* (not deferred) constraints.
  2. *Adversarial:* the storage-template differential — a quota-exceeding `RateLimitBySum`,
     an unauthorized `SenderAuthorized`, each rejected.
- **Dependency.** Independent of 0.1–0.3; PREREQ for sound storage userspace **and** the
  WAVE-3 apps ladder (subscription/identity/governed-namespace seams). **Size.** Medium.
  **Criticality.** FIDELITY → SOUNDNESS-CRITICAL for storage userspace. **Task:** new (FILL 4).

---

### 0.5 — Storage durability: make the `CellRuntime` `rfl`-checkpoint HONEST

- **Deliverable.** `checkpoint`/`restore`/`replay` are pure in-memory `Snapshot` round-trips:
  `checkpoint_restore_roundtrip` is **`= rfl`** (`CellRuntime.lean:60`). There is NO WAL, NO
  fsync, NO torn-write recovery — yet the Rust ground truth is log-before-apply + fsync +
  per-line BLAKE3 torn-write checksum + replay + truncate (`storage/src/wal.rs`) and redb ACID
  atomic note-spend (`persist/src/lib.rs:625`). The `rfl` must not read as "durability proved."
  Two-tier deliverable: **(cheap, up front) RELABEL** `checkpoint_restore_roundtrip` as a
  *cache-rebuild* law, not a durability law; **(later) model** a minimal crash/recovery
  semantics so the claim has content.
- **File surface (Lean).** `CellRuntime.lean:54-101`. Add a `WalLog` + fault-injection point;
  prove `recover (crash (apply log s)) = s` under a torn-write fault. Keep redb/erasure as a
  documented host-tier assumption.
- **Verify-braid.**
  1. *Relabel pass (immediate):* rename the law + a doc-comment stating it proves cache-rebuild,
     not durability.
  2. *Proof (later):* `recover_from_wal` replay equals pre-crash state under a torn-write fault;
     atomic note-spend (nullifier-insert + commitment-store) all-or-nothing across a crash.
- **Dependency.** Independent. Do the relabel **up front** (cheap honesty). **Size.** Small
  (relabel) / Medium-Large (real semantics). **Criticality.** FIDELITY (sharp `rfl`-fiction
  flag). **Task:** new (FILL 5).

---

### 0.6 — The higher-order handler-transformer PROVE (the comodel-morphism keystone)

- **Deliverable.** `HandlerTransformer.lean` proves `safe_transformer_composes` (instantiated
  twice — camera + forest — with teeth: `unsafe_transformer_rejected`), but leaves OPEN the
  keystone biconditional: that **`Fpu`-preservation IS the gluing condition** (one law, not
  two), and the recursive-camera tier. Prove the keystone, or — if it resolves negative —
  honestly record the two-law split.
- **File surface (Lean).** `HandlerTransformer.lean` (esp. the `-- OPEN:` at `:44-56,118-130`);
  needs a shared carrier (a real `Handler → Handler` with a built `act` functor) before the
  weld stops being a pun. Context: `HANDLER-TRANSFORMER-CONJECTURE.md`.
- **Verify-braid.** *Proof:* the `Fpu`-preservation ⟺ gluing biconditional; the recursive-camera
  tier instantiation. No differential (pure metatheory).
- **Dependency.** Independent; ABOVE-CORE / research frontier (dregg4). **Not a swap
  prerequisite** — sequenced into WAVE 0 because it is a *ready-now Lean fill* with a clean
  verify-braid, but it does not block the gate. **Size.** Large/research.
  **Criticality.** ABOVE-CORE. **Task:** new (FILL 9).

---

### WAVE 0 closeout — also in this strand, parallel lanes (carry the Rust crypto forward)

- **0.7 caveat/attestation crypto face (FILL 8a/8b/8e):** the caveat *gates* effects. Lean
  caveats are a bare `Ctx → Bool` (`Authority/Caveat.lean:43`); the macaroon is an HMAC chain
  `Tᵢ = HMAC(Tᵢ₋₁, Cᵢ)` whose tail compare detects caveat removal — the Lean *cannot express*
  removal. Make the §8 obligations explicit (8a HMAC-chain integrity, 8b 3P-discharge crypto,
  8e Stealth/StarkDelegation modes — `AuthModes.lean` omits Stealth entirely). At minimum
  explicit obligations; ideally model the crypto. *Verify-braid: removal-detection negative
  test; Stealth/StarkDelegation mode dispatch. PREREQUISITE-FOR-SWAP (the gate would weaken
  authorization without it). Size: medium. Tasks: relates to #79, #122, #124.*
- **0.8 zero-sorry + CI guard (#128, in flight):** retire the last by-design sorries + a CI
  check forbidding `sorry`. *This is itself a verify-braid spine — finish it; it underwrites
  every other proof claim in the strand.*
- **DEFERRED to ABOVE-CORE (named, not scheduled into a swap-gating wave):** FILL 8c/8d
  (selective disclosure, multi-show unlinkability wiring — #127 DV-BLINDEDSET), FILL 8f
  (repudiation / designated-verifier dial — NEW theory), FILL 11 (return-projection + fork —
  CORE-but-after-the-living-cell; checkpoint/replay/time-travel are then *theorems*, not
  effects).

---

## WAVE 1 — the FFI / Rust-Lean interface extension + the differential RATCHET

This wave makes the kernel *callable for more* and turns the safety net from a one-shot into
a ratchet. **It is the last wave before the gate** — the gate criteria are literally "WAVE 1
ratchet GREEN in CI + WAVE 0 soundness fills landed."

---

### 1.1 — Export the widened kernel + the record-domain door through the FFI

- **Deliverable.** As WAVE 0 widens `FullAction`, grow the FFI wire codec to marshal the new
  variants (escrow/note/committed/half-edge), and add a **new** `@[export] dregg_exec_record_turn`
  over `RecordCell.recExec` so the *record/cell-program* turn-decision (the axis every shipped
  app lives on) becomes callable — today the FFI exposes only the resource/capability axis.
- **File surface.** `FFI.lean:715-936` (wire grammar + `execFullTurnStep`); add a sibling export
  marshalling `{cell, method, op, program}` → `RecordCell.recExec` (`RecordCell.lean:104`,
  `recExec_some_iff_admits` `:140`) → `{new, ok}`. All callee machinery (`applyOp`/`admits`/
  `evalConstraint`) is already proved and `#eval`-able — codec + `@[export]`, **no new theorems.**
- **Verify-braid.** The new exports are exercised by 1.2's grown differential; per-export the
  proved law travels with it (`recExec_some_iff_admits`, `execFullTurn_each_attests`).
- **Dependency.** WAVE 0 (the variants must exist to export). **Size.** Medium.
  **Criticality.** INTEGRATION-CRITICAL. **Task:** extends #95 (W9-FFI-EXTRACT).

---

### 1.2 — Harden the differential into a CI RATCHET (the swap safety-net)

- **Deliverable.** The differential exists and is GREEN today (`full_turn_differential.rs`:
  5000 structured + 4000 adversarial, 0 divergence, 3384 rollbacks — verified this session),
  framed correctly as **kernel-vs-fresh-Rust-reference, NEVER vs. dregg1.** But it is **NOT a
  ratchet**: the crate has a detached `[workspace]` (`dregg-lean-ffi/Cargo.toml`), CI never
  builds or runs it (`.github/workflows/ci.yml:23,40,53` are `--workspace` only), the
  `libdregg_lean.a` archive is hand-rebuilt. A net not wired to a trigger is a one-shot. Make it:
  1. **auto-rebuild** the archive when `metatheory/Dregg2/Exec/**` or `dregg-lean-ffi/**` changes;
  2. **run in CI as a REQUIRED check**, blocking merges on any divergence;
  3. **grow** the Rust reference to mirror the *real* SDK/node effect set (not just
     transfer/mint/burn/delegate/revoke) + the record-domain (1.1) + the encrypted/conditional
     shapes (`DOWNSTREAM-READINESS.md` N3, the "single sharpest near-term improvement").
- **File surface.** `dregg-lean-ffi/src/full_turn_differential.rs` (grow the reference `:257`,
  the authority mirror `:210-229`, the fuzz counts `:809,:1067`); add a new
  `record_turn_differential.rs` mirroring `dregg_cell::CellProgram::evaluate`
  (`cell/src/program.rs:1007`); CI job + archive rebuild rule.
- **Verify-braid.** *This wave IS the verification spine for the whole swap.* Its own
  adversarial coverage (overflow/underflow at the i64 boundary, unauthorized delegates,
  double-mints, mis-ordered lists) is the regression net. Drive divergence to 0 on each grown
  domain before the gate opens.
- **Dependency.** 1.1 (exports to diff against). **Size.** Medium (the bulk is mirroring).
  **Criticality.** SOUNDNESS-CRITICAL (this is the net). **Task:** extends #95.

---

# ═══════════════ THE SWAP GATE ═══════════════

**Crossing condition (ALL must hold):**

1. **WAVE 1.2 ratchet is GREEN and REQUIRED in CI** — archive auto-rebuilt, differential a
   blocking check at 0 divergence, framed kernel-vs-new-Rust (never dregg1).
2. **WAVE 0 soundness fills landed:** the per-asset vector (0.1) and escrow/note in the
   executable turn (0.2) — so "the FFI hosts a *real* turn" is true beyond a 5-effect scalar
   kernel, and the kernel is sound for multi-asset dregg.
3. **The record-domain door exists** (1.1) — required for the WAVE-3 app pilot.

Below the gate: nothing in `node`/`turn`/`sdk` production code routed through Lean (verified:
`grep` for `dregg_exec_full_turn`/`execFullTurn` in node/turn/bridge → empty). Above the gate:
**addition + oracle-gate only.** Deletion is WAVE 4, after a burn-in.

# ═════════════════════════════════════════════

---

# STRAND B — NEEDS-THE-SWAP (re-wiring; addition + oracle-gate, never deletion)

## WAVE 2 — the FIRST SAFE REWIRING: shadow ONE real turn-decision through Lean

- **Deliverable.** Route exactly **one** turn-decision through the Lean FFI **as an observer,
  never a decider** — the *oracle-shadow* of the **balance-conservation sub-decision** of a
  balance-only turn (transfer/mint/burn, actor owns `src`, no crypto modes, no caps). This is
  the exact FIRST SAFE step `SWAP-READINESS.md` prescribes: addition behind a feature flag,
  the Rust path stays 100% authoritative.
- **File surface (Rust, production — first touch).** Behind a **`lean-shadow` cargo feature
  (default OFF, never in the consensus path)**, after the Rust `execute`
  (`turn/src/executor/execute.rs:54`) decides a balance-only turn, lower it to the
  `dregg_exec_full_turn` wire form, call the FFI, and **compare** the commit-bit + post-balances.
  On mismatch: increment a metric + log loudly (`node/src/metrics.rs`); **do not alter the
  decision.** Reversible (a flag), cannot affect consensus (observe-only).
- **Verify-braid (the differential IS the regression net here).**
  1. *Shadow-as-test:* every mismatch is a *finding*; the Rust path remains authoritative.
  2. *Promote shadow traffic to differential seeds:* feed real turns observed in the shadow
     back into `full_turn_differential.rs` as regression corpus; drive divergence to zero on
     **production traffic shapes** (the "100% on real inputs" of `SUCCESSOR-ROADMAP.md` Phase B,
     on the balance subset).
- **Dependency.** THE GATE (the ratchet must be green first — a stale oracle is worse than
  none). **Size.** Small-Medium. **Criticality.** This is the first re-wiring; observe-only, so
  low-risk by construction. **Task:** new (SWAP-READINESS §"first safe rewiring step").

---

## WAVE 3 — the FIRST STARBRIDGE-APP on the new system: nameservice, verified

- **Deliverable.** The first *shipped app* whose **acceptance decision is made by the proved
  Lean kernel**, differentially pinned. Pilot = **nameservice register/renew/transfer** —
  chosen because its *entire* base-flow constraint vocabulary (`WriteOnce`, `Monotonic`) is
  **already proved in `Program.lean`**, its authority rides the cap domain the FFI already
  enforces, and it needs **zero** new predicate/verifier portals. Shortest path to a real app
  turn decided by Lean.
- **File surface.**
  - *Lean:* reuse 1.1's `dregg_exec_record_turn` over `RecordCell.recExec`; encode
    `name_cell_program` = `predicate [writeOnce "name_hash", monotonic "expiry", writeOnce
    "revoked"]` in the wire (bridge the Rust slot-schema NAME_HASH=2 etc.,
    `nameservice/src/lib.rs:104-122`, to the name-keyed Lean `RecordProgram`,
    `Program.lean:11`).
  - *Rust (differential):* new `dregg-lean-ffi/src/record_turn_differential.rs` — a Rust
    reference reimplementing `recExec`+`admits` against the **new** `dregg_cell::CellProgram::evaluate`
    (`cell/src/program.rs:1007`), proptest-fuzzing Lean `recExec` ≡ Rust evaluate on adversarial
    (old,new,op) triples: register-then-reregister (WriteOnce reject), expiry-decrement
    (Monotonic reject), legal renewal (accept). **Never diff against dregg1's old nameservice.**
  - *Rust (rewiring):* a feature-gated branch in the app's `EmbeddedExecutor` path
    (`nameservice/src/lib.rs:585`) that, for a register turn, calls `dregg_exec_record_turn`
    and asserts accept/reject + post-state agree; land as an integration test beside
    `tests/integration_register_full_flow.rs`.
- **Verify-braid.** The record-domain differential (the safety net) + the integration test.
  **Claim when green:** *"the nameservice register/renew/transfer admissibility decision is made
  by the proved Lean `recExec`/`RecordProgram.admits`, with `WriteOnce`/`Monotonic` soundness
  carried by `Program.lean`, cross-checked against the production Rust `CellProgram::evaluate`
  over an adversarial fuzz domain."*
- **Dependency.** 1.1 (record-domain door) + the gate. The other three apps inherit this door:
  **subscription/identity** add ONE seam (bind `SenderAuthorized{PublicRoot}` membership to the
  predicate portal, pin `MonotonicSequence ↦ fieldDelta f 1`); **governed-namespace** last (adds
  the `Authorization::Custom{vk_hash}` → registered-threshold-verifier routing). These ladder
  steps depend on WAVE 0.4 (the constraint vocabulary) being landed.
- **Size.** Steps 1-2 a few days (codec, no new proofs); Step 3 (differential) the bulk; Step
  4-5 integration. **Bounded by existing proved machinery — no new metatheory for nameservice.**
  **Criticality.** First app-level swap foothold. **Task:** new (APPS-READINESS §5).

---

## WAVE 4 — THE GATED SWAP: canary → primary → DELETE the Rust kernel

> **Deletion is dead last, and only after the differential ratchet is solid + the executor
> proven complete.** "Frozen v1 stays until its check is oracle-equal" — delete last, never
> first. Anything short of the gate below launders an unverified gap into the TCB.

- **Deliverable, in three irreversible-only-at-the-end sub-stages:**
  1. **Shadow** (done in WAVE 2, extended): Lean observes, Rust decides, divergence = finding.
  2. **Canary:** Lean *decides*, Rust *shadows*, **divergence = HALT.** Behind the flag, a
     burn-in window on real traffic.
  3. **Primary → DELETE:** Lean authoritative; only after the burn-in window is clean across
     the *full* effect surface do we remove `verify_authorization`/`authorize.rs`.
- **File surface (the deletion target).** `turn/src/executor/authorize.rs` (`verify_authorization`
  `:8`), the 9 node `TurnExecutor` sites (`node/src/api.rs:1879,…,5451`), re-seated onto the
  FFI-shim — **HTTP request/response types held byte-stable** so CLI/bot/extension never notice.
- **GATE CRITERIA for the deletion (ALL required — from `SWAP-READINESS.md` §"what gates the
  actual Rust deletion"):**
  1. **Cryptographic authority modeled or portal-discharged** — a `CryptoKernel` Rust impl
     (Ed25519/STARK/Pedersen/Poseidon) whose discharge of the Lean portal laws is argued sound
     (`PHASE-CRYPTO-TCB.md`), so the 9 `Authorization` modes reduce to verified cap-table facts.
     *Until then the security-critical half of `authorize.rs` has NO Lean counterpart.*
  2. **Call-forest + effect-catalog parity** — a `Turn`/`Effect`-tree → Lean-executor lowering
     covering the 51 effects, differential at 100% on real inputs incl. tree-shaped per-node
     authorization (the node's `execute_tree` is a *tree*; `execFullTurn` is a flat list).
  3. **Admission preamble decided** — nonce/fee/freeze/receipt-chain/budget either kept
     permanently Rust-side (admission ≠ kernel) or modeled — *explicitly chosen.*
  4. **The differential is a green REQUIRED CI ratchet over the FULL surface** (not just the
     5-kind ledger), archive auto-rebuilt, 0 divergence on a real-traffic corpus.
  5. **A staged cutover with the Lean path authoritative behind the differential for a burn-in
     window** (shadow → canary-with-halt → primary) **BEFORE** the Rust is removed.
- **Verify-braid.** The full-surface differential ratchet (criterion 4) is the net throughout;
  the canary's divergence=HALT is the live regression guard; the burn-in window is the
  empirical proof before deletion.
- **Dependency.** WAVE 2 + WAVE 3 + ALL five gate criteria. The crypto-authority criterion (1)
  pulls in the WAVE-0.7 caveat face + a `CryptoKernel` Rust impl (`PHASE-CRYPTO-TCB.md`); the
  effect-catalog criterion (2) pulls in exposing the E3-breadth modules (#104) through the FFI.
  **Size.** Large (the bulk of the whole rewrite). **Criticality.** Terminal. **Task:** new.

---

## WAVE 5 — DOWNSTREAM: SDK / discord-bot / consumers, sequenced WITH the swap

The product surface above the node is **already insulated** (CLI/discord-bot/sdk-ts/extension
go through the node HTTP boundary or the SDK *construction* API; neither exposes `TurnExecutor`
in its signature). Only **two crates embed a `TurnExecutor` in-process** — `dregg-sdk`'s
`AgentRuntime` and `dregg-wasm`'s `DreggRuntime` — and those are the load-bearing changes.

### Can do NOW (interface-stable, pre-swap — these PREPARE the seam, run in STRAND A timeframe)
- **N1.** Make `AgentRuntime`'s executor a **backend boundary** (trait/enum) without changing
  its public API (today a concrete field `executor: TurnExecutor`, `sdk/src/runtime.rs:61`).
  Pure refactor; lets a future `kernel-ffi` feature drop in.
- **N2.** **Freeze + contract-test the node HTTP API** (`SubmitTurnRequest/Response` et al.,
  `node/src/api.rs:1821+`) — the single most important stability boundary; the swap must
  preserve it byte-for-byte so the whole product surface is swap-invisible.
- **N4.** **Golden-vector `compute_signing_message`** (`sdk/src/runtime.rs:254`) — pure,
  construction-side, must produce identical bytes across the swap or every signature/receipt
  chain breaks.
- **N5.** **CI guard:** `dregg-sdk --no-default-features` (the wasm config) and `dregg-wasm`
  **never** transitively pull `dregg-lean-ffi` — the wasm-no-FFI invariant (non-negotiable).
- **N3** = WAVE 1.2 (grow the differential to the real effect set) — already scheduled.

### Gated on the swap (sequenced AFTER the corresponding node stage)
- **G2 (with WAVE 4):** re-seat the 9 node `TurnExecutor` sites onto the FFI-shim, staged
  **effect-class by effect-class**, starting with transfer/mint/burn/delegate/revoke (already
  FFI-covered), HTTP contract frozen. *Success criterion: CLI/discord-bot/sdk-ts/extension see
  nothing change.*
- **G1 (after WAVE 4):** route `AgentRuntime::execute` through the FFI behind a **non-wasm32,
  non-default `kernel-ffi` feature**, once its effect set is covered + differentially equal.
- **G4 — wasm STAYS RUST.** The FFI cannot cross-compile to wasm32 (it links a 247 MB native
  Lean archive + `gmp`/`uv`/`c++` — `dregg-lean-ffi/build.rs:54-58`). The browser keeps the
  Rust `TurnExecutor`; new wasm semantics **delegate to the node** (the CLI/extension pattern)
  or keep a differentially-validated Rust fast-path. wasm-compiled-Lean is a later research arc.
- **G3 (last):** encrypted (`apply_encrypted_turn`) + conditional node paths — no FFI export
  exists yet.
- **G5 (separate seam, after the executor swap):** the authorizer/predicate migration
  (`/cipherclerk/authorize`, the `Authorizer` trait) onto the `Laws.Verifiable` seam — *not*
  the turn-executor swap; sequence after it.

- **Verify-braid (downstream).** N2/N4 are golden/contract tests (the swap must be
  *non-observable*); G1/G2 each gated on the per-effect differential being green for the
  consumer's effect set. **Dependency.** N1/N2/N4/N5 now; G-series tracks WAVE 4.

---

## Appendix A — fill ↔ task ↔ wave cross-reference

| Fill (GAP-MAP) | What | Wave | Task | Swap-class |
|---|---|---|---|---|
| FILL 1 | per-asset conservation vector | 0.1 | new | **PREREQ** |
| FILL 2 | escrow/note → `FullAction` | 0.2 | new | **PREREQ** |
| FILL 3 | committed-escrow + noteCreate | 0.3 | #121 | PREREQ (regression) |
| FILL 4 | `StateConstraint` 16→74 | 0.4 | new | PREREQ (storage) |
| FILL 5 | WAL durability honesty | 0.5 | new | PREREQ (≥ relabel) |
| FILL 6 | CG-5 cross-cell half-edge effect | 0.2-family (widen `FullAction`) | new | PREREQ (multi-cell) |
| FILL 7 | ρ_in/ρ_out vat membrane | 0.2-family | new | PREREQ (cross-vat) |
| FILL 8a/b/e | caveat-chain / 3P-discharge / Stealth modes | 0.7 | #79,#122,#124 | PREREQ (auth face) |
| FILL 8c/d | selective disclosure / multi-show wiring | deferred | #127 | ABOVE-CORE |
| FILL 8f | repudiation / designated-verifier dial | deferred | new | ABOVE-CORE |
| FILL 9 | higher-order handler tier | 0.6 | new | ABOVE-CORE |
| FILL 10 | distributed conformance (consensus/gossip/Stingray/revocation) | deferred (node-level) | #106 et al. | ABOVE-CORE (CRITICAL for node claim) |
| FILL 11 | return-projection + fork | deferred | new | ABOVE-CORE |
| — | zero-sorry + CI guard | 0.8 | #128 | verify-spine |
| — | FFI export widen + record door | 1.1 | #95 | gate |
| — | differential ratchet in CI | 1.2 | #95 | **gate (the net)** |

## Appendix B — the four source docs

- `docs/rebuild/SWAP-READINESS.md` — can the Lean kernel HOST a real turn; the first safe
  rewiring step; the deletion gate.
- `docs/rebuild/DREGG2-GAP-MAP.md` (and the `metatheory/docs/rebuild/` copy) — the 11 fills,
  criticality, sizes, dependency order, PREREQ-vs-ABOVE-CORE split.
- `docs/rebuild/APPS-READINESS.md` — the four shipped apps, the constraint-coverage table, the
  nameservice pilot increment.
- `docs/rebuild/DOWNSTREAM-READINESS.md` — SDK/bot/wasm/CLI consumers, the stable-vs-shifting
  interface, the wasm32 blocker, the now-vs-gated sequencing.

---

*A closing couplet, since the egg is still warm:*
*first vector the sum, then widen the door, / shadow before deciding, and ratchet before more;*
*the buggy old oracle is never the test — / it's kernel-vs-fresh-Rust that gates the rest.* 🐉🥚

*— braided so each build has a proof at its side, ( ˘▾˘ )*

---

# VERDICT — the skeptic's readiness assessment (2026-05-31, READ-ONLY)

> Appended by an independent adversarial reviewer. Default-skeptical, especially on the
> **irreversible** swap-deletion gate. Every load-bearing claim below was *re-verified against
> the live tree* this session (not taken from the prose) — file:line evidence inline. Where the
> roadmap is honest I say so plainly; where it is optimistic I flag it; where a claimed
> READY-now hides a prerequisite I name the prerequisite.

## The honest answer to ember's "are we ready"

**Ready for what, exactly — there are three different "ready"s, and only the first is true.**

1. **Ready to start the STRAND-A Lean/FFI fills (WAVE 0–1)?** → **YES.** These touch only the
   metatheory + the detached PoC crate. The proved machinery the fills rebind genuinely exists
   (verified: `Program.lean:68,70,120,124` has the `writeOnce`/`monotonic` evaluators;
   `MultiAsset.lean` has the per-asset template; the sorry-discipline is real — **0 `sorry`
   tactics** outside doc-comments across `metatheory/Dregg2/`, guarded by `Tactics.lean`'s
   `#assert_axioms`/`sorryAx` check). Nothing in STRAND A can affect the running node. Go.

2. **Ready to begin the FIRST SAFE REWIRING (WAVE 2, observe-only shadow)?** → **NO, GATED.**
   Not because the step is risky in itself (it is reversible + observe-only by construction) but
   because its stated prerequisite is *not yet met*: the differential **is not a ratchet** (the
   crate has a detached `[workspace]`, `dregg-lean-ffi/Cargo.toml:4`; **no CI workflow references
   it** — verified `grep` of all 10 `.github/workflows/*.yml` for `differential|lean-ffi|
   libdregg_lean|dregg_exec` → empty). A stale oracle is worse than none. WAVE 1.2 must land
   first. **Verdict: GATED-ON the ratchet (WAVE 1.2).**

3. **Ready to DELETE the Rust kernel (WAVE 4)?** → **EMPHATICALLY NO. NOT-YET, and not close.**
   Today **zero** production code routes through Lean (re-verified: `grep` of `node/src turn/src
   bridge/src sdk/src` for `dregg_exec_full_turn|execFullTurn|dregg-lean-ffi` → empty; the only
   consumer of the FFI is the differential harness itself). The hosted `execFullTurn` decides
   **5 abstract action kinds** over an **abstract cap table**; the node's real gate decides a
   **51-variant `Effect` forest** (`turn/src/action.rs:760`, counted 52 arms) under **10
   cryptographic `Authorization` modes** (`turn/src/action.rs:206`: Signature/Proof/Breadstuff/
   Bearer/Unchecked/CapTpDelivered/Custom/OneOf/Stealth/Token — *none* of which the Lean kernel
   models; it models the *right*, not the *proof*). The security-critical half of `authorize.rs`
   **has no Lean counterpart at all** until a `CryptoKernel` Rust impl + a portal-discharge
   argument exist. Deleting now would launder the entire cryptographic-authority TCB into nothing.

**One-sentence answer for ember:** *We are ready to build (STRAND A) and ready to harden the net
(WAVE 1); we are not ready to rewire (the net isn't a ratchet yet) and we are nowhere near ready
to delete (the crypto-authority and effect-forest halves of the real kernel are entirely
unmodeled). The roadmap's ordering is correct and its framing is sound — the only optimism is in
how it labels a few "READY-now" items that actually carry a quiet prerequisite (below).*

## Per-wave verdict

| Wave | Verdict | The honest gate / hidden prerequisite |
|---|---|---|
| **0.1** per-asset vector | **READY-now** | Genuinely buildable: `MultiAsset.lean` template + `maExec_conserves_per_asset` exist; this is porting + re-binding, not new theory. *Caveat:* it is **Large** and it re-keys the conserved measure for 0.2/0.3 — if not done first, the spine is re-proved twice. **Do it first, as stated.** |
| **0.2** escrow/note → `FullAction` | **READY-now** (after 0.1) | The chained primitives are PROVED-but-stranded (`RecordKernel.lean`, `EffectsPaired.lean`); this is widening the dispatch + the codec. Honest. |
| **0.3** committed-escrow + noteCreate | **READY-now** (after 0.2) | Closes a real regression (FID-ESCROW left the committed triple on the old shadow). Honestly flagged as the exact failure mode the project rejected once. |
| **0.4** `StateConstraint` 16→74 | **READY-now, with a SHARP honesty caveat** | The trap is real and **verified**: `Program.lean:151` `boundDelta` evaluator literally `=> true` (unenforced). Several other advanced constraints (`RateLimit`/`BoundedBy`/`TemporalGate`/`PreimageGate`) are **absent**, not merely stubbed. This is **PREREQ for the WAVE-3 apps ladder** (subscription/identity/gov), *not* for nameservice. Buildable, but larger than "add a few variants" — each needs a *real* `eval` + soundness lemma, and the witnessed/sender ones need the predicate portal. |
| **0.5** WAL durability honesty | **RELABEL = READY-now; real semantics = NOT-YET** | The two-tier framing is correct and important: `checkpoint_restore_roundtrip` is `= rfl` — a cache-rebuild identity, **not** a durability proof. **Do the relabel immediately** (cheap honesty); the crash/recovery model is Medium-Large and not swap-gating. |
| **0.6** handler-transformer keystone | **READY-now but ABOVE-CORE** | Pure metatheory, research-grade, **not a swap prerequisite** (correctly so labeled). May resolve negative; the roadmap honestly admits that outcome. Do not let it block the gate. |
| **0.7** caveat/attestation crypto face | **READY-now (obligations); GATED (real crypto)** | The gap is real: Lean caveats are `Ctx → Bool` and **cannot express caveat *removal*** (the macaroon HMAC-chain tail-compare that detects it). Stating explicit §8 obligations is ready-now; modeling the HMAC chain is larger. **PREREQUISITE-FOR-SWAP** (it is half of deletion-gate criterion 1) — correctly flagged. |
| **0.8** zero-sorry + CI guard (#128) | **NEARLY DONE — and it is the verify-spine** | Re-verified: the discipline is genuine (0 real `sorry` tactics; `Tactics.lean` `#assert_axioms` guard exists). #128 truly is "retire the last few + add the CI forbid." **Finish it — it underwrites every other proof claim.** |
| **1.1** FFI export widen + record door | **GATED-ON WAVE 0** | Honest: "no new theorems, codec + `@[export]`." Verified `dregg_exec_record_turn` does **not** exist yet — so this is real work, and the nameservice pilot genuinely cannot start before it. |
| **1.2** differential → CI RATCHET | **NOT-YET — and this is the single most important unbuilt thing** | Verified: differential exists (`full_turn_differential.rs`, 41 KB, `N_STRUCTURED=5000`/`N_FUZZ=4000`), archive is **fresh** (`libdregg_lean.a` 05:59 ≥ `FFI.lean` 05:56), framing is **correct** (Rust *reference*, never dregg1). But it is **NOT in CI** and the crate is workspace-detached. **A net not wired to a trigger is a one-shot.** This wave is the gate's load-bearing strand. |
| **THE SWAP GATE** | **CLOSED. All three crossing conditions currently FALSE.** | (1) ratchet not green-in-CI — it's not in CI at all; (2) WAVE-0 soundness fills not landed; (3) record door doesn't exist. **Do not cross.** |
| **2** first safe rewiring (shadow) | **GATED-ON the gate (esp. 1.2 ratchet)** | The step itself is low-risk *by construction* (feature-flag, observe-only, never in consensus path) — that design is sound. But it must not run against a stale oracle. Gate first. |
| **3** nameservice app pilot | **GATED-ON 1.1 (record door)** — but the *choice* is honest | nameservice **is** genuinely the smallest: re-verified its base program is exactly `WriteOnce(NAME_HASH)`/`Monotonic(EXPIRY)`/`WriteOnce(REVOKED)` (`nameservice/src/lib.rs:175-187`), all three present in `Program.lean`. **The gap is honestly stated:** the attested tier (`SenderAuthorized{CredentialSet}` + `BlindedSet`) is explicitly deferred, and the pilot needs the not-yet-built `dregg_exec_record_turn` + a *new* record-domain differential. It is not "ready-now"; it is "ready *after* 1.1," correctly. |
| **4** THE GATED SWAP (delete) | **NOT-YET (terminal). The five deletion criteria are the right ones; none are met.** | Crypto-authority (criterion 1) is the headline blocker and is *entirely* unbuilt. Effect-forest parity (2) needs the 51-effect catalog `@[export]`-ed + tree-shaped (not flat-list) authorization. **Delete dead last, behind shadow→canary(halt)→primary→burn-in.** Conservative and correct. |
| **5** downstream (SDK/wasm/bot) | **N1/N2/N4/N5 READY-now; G-series GATED on WAVE 4** | The insulation claim is verified (CLI has zero `dregg-*` deps; only `AgentRuntime` + `DreggRuntime` embed a `TurnExecutor`). The **wasm32 blocker is real and decisive**: the FFI links a **247 MB native archive** (`libdregg_lean.a` is 259,560,080 bytes — confirmed) + `gmp`/`uv`/`c++`; it cannot cross-compile. wasm STAYS RUST is the right call. |

## The three skeptic's challenges ember asked me to press on

**(1) "Are the claimed READY-now fills truly buildable on the current Lean, or do they hide a
prerequisite?"** — **Mostly buildable; three carry a quiet prerequisite that should be stated as
a gate, not a footnote:**
- **0.1 leads, and is Large** — not a quick win; it re-keys the conserved measure, so its
  *ordering* is itself a prerequisite for 0.2/0.3 being one-pass. The roadmap says this; keep it
  front-and-center.
- **0.4 is bigger than "16→74"** — several constraints are *absent* (not stubbed), and the
  sender/witnessed ones (`SenderAuthorized`, `WitnessedPredicate`) **require the predicate
  portal** to be wired, which is its own seam. Treat 0.4 as "Medium→Large + a portal dependency,"
  and note it gates the *apps ladder* (WAVE 3 beyond nameservice), so it is on the critical path
  to a *second* app even though it is not on the gate.
- **0.7's caveat-removal gap is structural** — the Lean type (`Ctx → Bool`) literally cannot
  express the thing the macaroon HMAC chain protects against. "State the obligation" is ready-now;
  "model it" is real crypto-modeling work and is half of deletion-criterion-1. Don't let the
  ready-now relabel hide the not-yet model.

**(2) "Is the differential a sufficient swap safety-net to gate a DELETION, or does it need
adversarial/exhaustive coverage first?"** — **It is the right *kind* of net (correct framing:
kernel-vs-fresh-Rust, never dregg1; real adversarial fuzzing at the i64 boundary). It is NOT
sufficient to gate a deletion, for three reasons the harness *itself admits* and one it doesn't:**
- *(admitted, verified at `full_turn_differential.rs:24-28`)* It **cannot certify the codec** —
  "a codec bug that corrupts BOTH sides identically would pass." The codec is **TCB**. For a
  deletion, the marshalling layer needs its own assurance (golden vectors against a hand-checked
  oracle, or a Lean-side round-trip-identity proof of `decode ∘ encode = id`), because after the
  swap the codec sits *between consensus and the verified kernel*.
- *(admitted)* It is **sampled (5000+4000), not exhaustive** — fine for *shadowing* (find
  divergences on real traffic), **not** for licensing an *irreversible* deletion. Before deletion,
  the net needs (a) a real-traffic corpus driven to 0 divergence, AND (b) coverage of the *full*
  effect surface + the *tree-shaped* per-node authorization (today it mirrors a *flat list*; the
  node's `execute_tree` is a tree — a whole class of authorization bugs is *outside the sampled
  domain by construction*).
- *(admitted)* Agreement does **not** certify the Rust reference — only Lean carries proofs. So
  the net proves "two implementations agree," which is necessary but not sufficient; the *proof*
  is what makes Lean authoritative, and the proof only covers the 5 kinds today.
- *(NOT admitted, my addition)* The differential covers **none** of the cryptographic
  `Authorization` modes — they are absent from `execFullTurn` entirely, so there is *nothing to
  diff*. A green differential over the ledger says **zero** about whether the crypto-authority
  swap is safe. **Do not read differential-green as deletion-ready.**

  **Net:** the differential gates *shadowing* (WAVE 2) and the *app pilot* (WAVE 3) well. It does
  **not** gate deletion until it is (i) a CI ratchet, (ii) codec-assured separately, (iii)
  full-effect + tree-shaped, (iv) driven to 0 on a real-traffic corpus, and (v) backed by a
  crypto-authority model that gives it something to diff. That is exactly WAVE-4 criteria 1–4 —
  so the roadmap is right, *provided* nobody short-circuits "the differential is green" into
  "we can delete." Guard that conflation explicitly.

**(3) "Is routing ONE turn through the FFI actually low-risk, or does the codec/marshalling TCB
make it riskier than it looks?"** — **The WAVE-2 *shadow* is genuinely low-risk** (feature-flag
default-off, observe-only, never in the consensus path, reversible — all verified in the design).
**But the codec TCB is the sharp edge, and it bites the moment Lean *decides* (WAVE 4 canary),
not when it observes.** During shadow, a codec bug produces a *false divergence* (a finding) or a
*false agreement* (both sides corrupted identically) — annoying, not dangerous, because Rust still
decides. The instant the canary lets Lean decide, a silent codec bug that the differential cannot
catch (by its own admission) becomes a *consensus-affecting* fault. **Therefore: the codec needs
its own assurance line item before WAVE 4** — it is currently implicit in the roadmap (folded into
"the differential"). Recommend promoting it: a `decode ∘ encode = id` Lean lemma over the wire
grammar + a golden-vector suite checked against a hand-verified oracle, as an explicit WAVE-1.5
deliverable between the ratchet and the gate.

## What honestly should NOT advance / where the roadmap is slightly optimistic

- The **"5%/5%" framing in SWAP-READINESS** ("FFI is the last 5% of making the kernel callable;
  routing is the first 5% of the rewrite") is rhetorically tidy but undersells the rewrite: the
  crypto-authority + effect-forest bulk is closer to **the whole iceberg**, and the doc's own §
  body says so. Keep the iceberg, lose the "5%."
- WAVE 4 lists **9 node `TurnExecutor` sites**; I count **13** `execute`/`new` callsites in
  `node/src/api.rs`. Minor, but the re-seating is *more* surface than stated — size it up.
- The roadmap is otherwise **unusually honest** — it repeats the no-deletion framing, labels
  ABOVE-CORE vs PREREQ correctly, and never claims the swap is near. That honesty is the asset;
  protect it.

## The single most important thing to do FIRST

**Land WAVE 1.2: make the differential a REQUIRED CI ratchet — *before* any rewiring, and
concurrently with the WAVE-0.1 per-asset fill.**

Concretely, in priority order:
1. **Re-attach the crate / wire CI.** Add a CI job that, on any change under
   `metatheory/Dregg2/Exec/**` or `dregg-lean-ffi/**`, auto-rebuilds `libdregg_lean.a` and runs
   `full_turn_differential` as a **required, merge-blocking** check at 0 divergence. Until this
   exists, the net silently rots on every kernel edit and **WAVE 2 must not begin.** This is the
   load-bearing strand of the entire swap and it is the cheapest high-value thing on the board.
2. **In parallel (independent lane): WAVE 0.1 (per-asset vector) + the 0.5 relabel + finish
   #128.** 0.1 because it re-keys the conserved measure every later fill proves against (do it
   first or pay twice); the 0.5 relabel and #128 because they are cheap honesty that underwrites
   every proof claim.
3. **Promote the codec to an explicit assurance item (the proposed WAVE-1.5)** so the
   marshalling-TCB hole the differential admits is closed *before* Lean is ever allowed to decide.

Everything below the gate stays where it is — *closed* — until (1) is green. The egg is warm and
the ordering is right; the one missing reflex is the ratchet, and a deletion must never be gated
on a net that only runs when a human remembers to run it.

*— skeptic's note, kernel-vs-fresh-Rust and never the buggy old bird: ratchet first, decide later,
delete last. ( ⌐■_■ )*
