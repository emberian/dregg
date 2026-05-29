# dregg2 — Implementation ROADMAP

> **Status:** the build-sequence handoff. Reads forward from `dregg2.md` (the
> canonical architecture) + `dregg2-multicell-privacy.md` (JointTurn + privacy) +
> `00-synthesis.md` + `pdfs/decisions.md` + the `study-*.md` set, and pins the
> metatheory discharge order (`metatheory/`). **Dependency-ordered,
> soundness-critical-first.** Every item is tagged **REUSE** (wire/harden existing
> code — do *not* rebuild) or **BUILD-NEW**.
>
> **The one inviolable rule (see also OPEN-PROBLEMS):** cross-cell soundness is
> **NOT** `per-cell-sound ∧ per-cell-sound`. The JointTurn binding (CG-2 ⊗ CG-5)
> is an **explicit hypothesis**, never a lemma derived from the per-cell proofs.
> Encoding it as derivable makes the entire Boundary module unsound
> (`study-category §1.3`).
>
> Tags: `[G]` grounded-in-paper · `[C]` grounded-in-code (`file:line`) · `[F]`
> forward-design.

---

## Phase 0 — #1 SOUNDNESS-CRITICAL: audit step-completeness (GATES EVERYTHING)

**Nothing downstream is sound until this is answered and, if negative, fixed.**

**The audit.** Is `StepInv = Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance`
*actually all four in-circuit*? The expectation, from memory + the candidate docs
+ a code probe, is **NO**:

- **Authority is checked outside the proof.** Auth runs as plain Rust in
  `turn/src/executor/authorize.rs`; the PI surface lacks `AUTH_ROOT`,
  `ACTION_AUTHORITY_DIGEST`, `CONSERVATION_VECTOR`, `CONSTRAINT_MANIFEST_HASH`
  (grep of `circuit/src/` returns none of these; no `prove_full_turn` /
  `StepInv` symbol exists). `[C]`
- **Intent predicates are unenforced.** (memory) `[C]`
- **Graph-folding is flat / non-recursive.** (memory) `[C]`

**Why this is the gate (not recursion).** A live cell is codata; soundness is a
`▶`-guarded bisimulation that holds **iff each step is contractive in the full
`StepInv`**. A step-incomplete proof is *worse* than an inductive local error: under
coinduction a non-contractive step "permits a drifting future" — a chain that locally
type-checks while slowly leaking `Σ_k` (`decisions §2`, `Boundary.lean` docstring).
`[G]`

**The fix is step-completion, NOT recursion.** Recursion stays deferred behind the
`RecursionBackend` trait (Phase 3); it is a feature (teleport/late-join/audit), not a
soundness requirement (`decisions §0.2`). Do not let it leak onto this path or into
the Lean law.

**Deliverable:** a written verdict — for each of the four conjuncts, in-circuit or
not — and, for each gap, the specific PI field + AIR chip that closes it (feeds
Phase 2).

---

## Phase 1 — the collapses (cheap, high-leverage; mostly REUSE-by-merging)

Run first because each *removes* a zoo and shrinks the surface Phase 2 must prove
over. None is soundness-critical; all are pure simplification (`00-synthesis §7.1`,
`dregg2 §5.2`).

1. **Four gates → one `WitnessedCondition`.** `Precondition`, `StateConstraint`,
   `CapabilityCaveat`, `Authorization::Custom` all already wrap one predicate;
   unify on `{ binding: BindingSite, engine: Datalog | WitnessedPredicate | Await }`
   (`00-synthesis §3.1`). Keep Datalog and WitnessedPredicate as **two sibling
   engines** — merging the vocabularies regresses. **REUSE** (`cell/src/predicate.rs`).
2. **Sets → cells.** Nullifier/revocation/authorized-sender side-tables get a
   `CellId` + set-root + append-only program, queried through the existing slot-root
   path. **REUSE→BUILD** (`token/src/revocation.rs`, `credentials/src/revocation.rs`
   are the accumulator to fold in).
3. **Flatten `CallForest` → `Vec<Action>` (or give it real frames).** dregg copied
   Mina's tree + `May_use_token` enum but never built the caller frames that make it
   load-bearing — the modes are dead. Either flatten to `Vec<Action>` + explicit
   `Introduce` effects (what the executor honors today), **or** build Mina's
   `caller`/`caller_caller` frames around dregg's capability model
   (`study-mina-relink §2`). **BUILD-NEW** (decision required).
4. **Merge `Breadstuff` into `Token`/`Bearer`.** Collapse the bare-32-byte-hash
   representation; unify the two attenuation checks into one order relation. **REUSE**.

---

## Phase 2 — the soundness spine (THE critical path; BUILD-NEW over REUSE chips)

Make the per-turn proof step-complete. Recursion-independent. Each clause deletes a
slice of `authorize.rs`'s trust as it closes (`00-synthesis §7.3`, `decisions §7.2`).

1. **Auth-in-proof — the 6-clause statement.**
   `key → delegation → policy-entailment → effect-fold → replay → cell-root-binding`,
   each clause cross-PI-bound to the canonical turn (`dregg2 §7.1`). The auth-AIR
   primitive **exists** — `circuit/src/schnorr_air.rs` (+ `schnorr_sig.rs`,
   `native_signature_air` in `circuit/src/lib.rs`). **REUSE the AIR; BUILD-NEW the
   composition** into the turn proof's PI. Adopt Mina's per-field, in-circuit
   permission check against a monotone lattice (`spec_eval`, `study-mina-relink §3`).
2. **`effects_hash` as an in-circuit fold.** Re-derive `EFFECTS_HASH` inside the
   circuit, not as a trusted input. The EffectVM machinery exists
   (`circuit/src/effect_vm/`, `effects_hash` already threaded through
   `effect_vm/mod.rs`, `pi.rs`, `columns.rs`, `per_action.rs`). **REUSE→harden**.
3. **Per-asset value-conservation folded INTO the proof (the "second rib").** A
   per-`LinearityClass` `CONSERVATION_VECTOR` sum-check chip on the same effect-stream
   rows the effect-fold absorbs: Pedersen sum-to-zero + range + asset-type +
   fee-as-asset, sharing the in-proof bus. Makes a badge a *value*-bearing artifact,
   not just a state-transition attestation (`dregg2 §6.1`). The value-commitment
   primitive exists (`cell/value_commitment.rs`, Ristretto). **BUILD-NEW** (the
   in-proof fold) over **REUSE** (the commitment).
4. **ChainLink + ObsAdvance.** Bind `PREVIOUS_RECEIPT_HASH` (the `▶` guard) and the
   committed `Obs`-delta into the PI. **BUILD-NEW**.
5. **The return-projection + settled-call await face.** A forward turn is the
   structure-map step `c : X → F X`; the **return** is a second observation the caller
   awaits: (a) a typed `Obs`-delta result in the proof PI; (b) a "settled-call" await
   face (request → response + detached proof; caller suspends on "the callee's `Obs`
   advanced past receipt R") — the **backward** resolver of the await family
   (`dregg2 §6 gap #2, §4`). This is the zkRPC product shape. **BUILD-NEW** over the
   await substrate (`turn/src/conditional.rs`, `pending.rs`).

**PI surface (the entire trust boundary):** `AIR_VERSION, OLD/NEW_COMMIT,
EFFECTS_HASH (re-derived in-circuit), AUTH_ROOT, ACTION_AUTHORITY_DIGEST,
CONSERVATION_VECTOR (per-class), TURN_HASH / ACTOR_NONCE / PREVIOUS_RECEIPT_HASH,
CONSTRAINT_MANIFEST_HASH` (`dregg2 §7.1`).

---

## Phase 3 — the JointTurn (multi-cell ⊗; REUSE γ.2, BUILD-NEW the binding object)

**The JointTurn IS Mina's `zkapp_command` account-update forest, re-grounded** — the
proven precedent (`study-mina-relink §1`). A turn over N cells = a morphism on the
tensor `C₁ ⊗ … ⊗ Cₙ`; joint validity = three bound parts:

1. a **shared turn-identity** every per-cell step-proof commits to in its PI
   (= Mina `account_updates_hash`; the **CG-2 pullback**);
2. per-cell step-proofs (each `CellProgram` admits its share — Phase 2);
3. the **cross-cell conservation-over-commitments** N-lateral aggregate (**CG-5**).

**REUSE — this is already built as γ.2; do NOT rebuild:**
- `turn::aggregate_bilateral_prover` (`turn/src/lib.rs`) drives
- `circuit::bilateral_aggregation_air` (`circuit/src/bilateral_aggregation_air.rs`,
  `CrossSideExistenceAir`): **CG-2** turn-identity agreement (every row agrees on
  `TURN_HASH`/`EFFECTS_HASH`/`ACTOR_NONCE`/`PREVIOUS_RECEIPT_HASH` = the pullback) +
  **CG-5** cross-side existence (signed half-edge balance sum == 0 = the equalizer).
  The half-edges are declared by `StateConstraint::BoundDelta { peer_cell, peer_slot,
  delta_relation: EqualAndOpposite }` (`cell/src/program.rs:747`).
- **Atomicity is a PROOF property, not a live coordinator** (ADOPT from Mina): an
  in-circuit cumulative AND (`will_succeed` prophecy + `success`), gating one commit.
  The conjunction exists in `bilateral_aggregation_air`; copy the prophecy-then-verify
  discipline (`study-mina-relink §1`).

**BUILD-NEW:** the N-ary generalization of the bilateral case; **token-owner-as-
co-participant** (a turn moving asset A includes A's owner-cell as a participant —
Mina `may_use_token`/caller frames, grounds the value rib in the multi-cell frame);
the per-cell tier-local commit gated on the *same* shared aggregate proof (Mina's
single durable write → per-cell finality, proof shared).

---

## Phase 4 — the cell coalgebra core (REUSE program.rs, surface the structure-map)

The cell model that Phases 2–3 prove over. Mostly already in code, buried; the work
is *surfacing* it, not building it.

1. **`CellProgram` = the coalgebra structure-map.** It IS the `AdmissibleTurn ⇒ Cell`
   arrow: it decides the arrow's *domain* (admissibility filter) and *codomain*
   (effect-semantics). The ~29-variant `StateConstraint` catalog maps onto
   compositions of `WitnessedCondition`s; `Cases` with **default-deny on no-match**
   (`program.rs:1106`) makes the arrow partial-and-fail-closed. **REUSE**
   (`cell/src/program.rs:53`).
2. **GC = cell-liveness, the dual of coinductive existence.** Codata unfolds forever
   (`ν`) UNLESS unreachable; reachability is the well-foundedness side-condition.
   **REUSE** the refcount half (`captp/src/gc.rs`: `ExportGcManager`/`ImportGcManager`,
   session-validated `DropRef`). **Honest scope (`study-gc`):** ship **acyclic**
   distributed GC only; cross-vat cycles + lost/partitioned drops are reclaimed by
   **lease expiry** (`expires_at`, `stale_exports`), never by global reachability
   (which is non-co-witnessable by design). Land `gc.rs:14`'s `TODO(unified-lace)`
   (key GC on `StrandId`, not `FederationId`) — drop-attribution under 3-party handoff
   is the one place the Byzantine-safety argument is load-bearing on an unfinished
   migration. **REUSE→finish**.
3. **The vat layer.** **REUSE `captp/`** wholesale: sessions, sturdyrefs, handoff, gc,
   store-forward, pipeline.

---

## Phase 5 — privacy (three tiers; REUSE existing primitives)

Not a subset — the full three-tier stack on primitives that exist (`dregg2 §6a`):

1. **Field privacy** — `FieldVisibility` on `Preserves` fields. **REUSE**.
2. **Value privacy** — the value rib (Phase 2.3): Pedersen + Bulletproof range, folded
   into `CONSERVATION_VECTOR`. The JointTurn's conservation equalizer runs **over
   commitments** (homomorphic `Σ = 0`), so the cross-cell balance hypothesis is over
   commitments, never cleartext. **REUSE** (`cell/value_commitment.rs`).
3. **Graph privacy** — ZK-hidden auth-derivation-chain (anonymous delegation) +
   holder-blinded set-membership (`AuthorizedSet::BlindedSet`/`CredentialSet`,
   `program.rs:316/338`) + **stealth one-time keys** (`cell/src/stealth.rs`,
   unlinkable invocation) + **blinded queue** (a set-cell with ZK-blinded
   membership/consumption — the missing inbox primitive recovered as a cell,
   `storage/src/blinded.rs`). **REUSE**.

---

## Phase 6 — the anti-brick clause (BUILD-NEW; BEFORE any recursion-backend swap)

**This must land before Phase 7.** dregg2 *will* swap the recursion backend / AIR
encoding (Phase 7: depth-as-security-parameter). When it does, every live
`Circuit{circuit_hash}` cell pinned to the old proof system becomes **bricked** — the
exact failure Mina's `verification_key_perm_fallback_to_signature_with_older_version`
(`permissions.ml:77`) was built to prevent (`dregg2-multicell-privacy §3`,
`study-mina-relink §4`).

**ADOPT:** a `set_program` upgrade-admissibility clause pinning a proof-system /
`AIR_VERSION`; when a cell's pinned version is older than the live verifier, the
upgrade authority **falls back to a signature by the cell's owner** — a verifier
upgrade can never strand a sovereign cell. (`AIR_VERSION` is already threaded in
`turn/src/executor/mod.rs`; the upgrade clause + signature fallback is BUILD-NEW.)
dregg2's migration is otherwise *stronger* than Mina's: transparent + conservative +
content-hash-preserving.

---

## Phase 7 — DEFERRED: recursion + ZK polish (behind the trait; NOT soundness-critical)

1. **Write the `RecursionBackend` trait** (`MAX_DEPTH: Option<u64>`,
   `needs_cycle: bool`; **never an `additive_combine` method** — that forks into two
   IVC layers). Route all IVC through it. This is the no-regret PQ hinge; write it
   *now* even though the impl is deferred (`decisions §3, §7.3`). **BUILD-NEW.**
2. **PCS / Fiat-Shamir adversarial tests** — the 11-item checklist tied to Orion-1164
   + Gemini-565; reconcile the FRI-param disagreement (`plonky3_prover` 50/blowup-3 vs
   `stark.rs` 80/blowup-4); set a soundness-bit target. The unaudited PCS layer is the
   real risk (`decisions §6, §8`). **BUILD-NEW.**
3. **LogUp** for range/auth (FRI-native running-sum; *not* Lasso). **BUILD-NEW.**
4. **Port `prove_full_turn` → `HidingFriPcs`** for ZK; **ban FFT-type quotient splits**
   (Haböck/Al-Kindi footgun). **BUILD-NEW.**
5. **Run M1** (FRI-verifier-in-circuit per-step cost on degree-7 BabyBear AIRs) **+ M2**
   (close the in-AIR-Merkle gap: algebraic Poseidon2 Merkle verified *in-AIR*, not
   native BLAKE3) → decide the recursion-impl primary. Interim = the ~80%-built
   Pickles/IPA Halo-accumulation port behind the trait (pre-quantum, coinductively
   clean, audited upstream); PQ target = lattice-IVsC (Neo/SuperNeo/Lova). Keep AIRs
   CCS-expressible as the portability hedge. Leaf stays FRI/BabyBear/Poseidon2 → WHIR
   later (cheapens the recursive verifier). (`decisions §4, §7.6`)

---

## Deferred strata (above the core — design later, NOT core blockers)

These do not change the semantics (`dregg2 §10`):

- **Economic** — computrons/fees/budget/bonds, the 50/30/20 relay split
  (`coord/budget.rs`, `relay_service`). Conservation (the value rib) is core;
  *incentives* are not.
- **Agent / product** — the concrete MCP daemon hosting the ~46 `dregg_*` tools
  (`node/src/mcp.rs`); the app-framework; the zkRPC surface. The caps + await + badge
  *core* is in-core (Phases 2–5); the daemon hosting it is not.
- **Operational / transport** — node daemon (`node/`), gossip (Plumtree,
  `net/src/gossip.rs`), relay/BLE, on-chain settlement (SP1→Groth16→EVM, `chain/`).
- **The coordination / choreography module** — multi-party, multi-turn, session-typed
  choreography reified as a protocol-cell, privacy-by-projection, the statically-
  classified I-confluent fragment (`dregg2-multicell-privacy §6`). **Its central
  theorem is research-grade — see OPEN-PROBLEMS #1.** Build the JointTurn (Phase 3)
  first; this composes JointTurns over time.

Plus the genuinely-deferred: arbitrary-depth IVC recursion (a named security
parameter, Phase 7) and schema-DAG fork/merge migration (linear-chain transparency is
proven; the DAG case is open, `dregg2 §5`).

---

## The metatheory discharge order (`metatheory/`, Lean4, spec-first/grind-up)

Mirrors l4v: Core + Laws first, the boundary law last. Each module is scaffolded with
`sorry`'d theorems; below is what each `sorry` needs.

### 1. `Core.lean` — the monoid-hom conservation (FIRST)
- `conservation_ordinary` — needs the `Category`/`MonoidalCategory`/`SymmetricCategory`
  instances on `TurnCat` and `count` realized as a genuine `MonoidHom`
  `(|TurnCat|, ⊗, I) → (ℕ, +, 0)`. **Per `study-category §2`: state it as a monoid-hom
  + an *invariance property of the `ordinary` morphism class*, NOT as "strong monoidal
  functor" — functoriality is vacuous on a discrete target and misleads toward the
  thin-posetal trap (which cannot carry Law 1's symmetry iso).** Fill `unit_zero`/
  `tensor_add` placeholders with `count I = 0` / `count (A⊗B) = count A + count B`.
- `mint_delta` / `burn_delta` — the two privileged generators; equality (`=`), not `≥`.
- `withholding_comonoid_coherence` — the no-copy-`Δ` / no-erase-`◇` statement.

### 2. `Laws.lean` — the Galois `Predicate ⊣ Witness` (FIRST, with Core)
- `search_sound` — the sole search contract (returned witnesses verify; no
  completeness/termination). The VERIFY/FIND asymmetry is in the *types* (`Bool` vs
  `Option`), honest.
- `predicate_witness_galois` — **needs the two preorders pinned**: predicate entailment
  `≤` and witness specificity `≤`, instantiated as the slot-caveat entailment and
  witness-refinement orders (`study-category §3`, "stated but not grounded" until then).
- `predicate_heyting` — the residual `a ⊓ b ≤ c ↔ a ≤ b ⇨ c`; this `⇨` IS attenuation,
  the same one `Positional`'s `LossyMorphism` uses.

### 3. `Authority/Positional.lean` — the l4v integrity lift (THEN)
- `boundary_law` — the lift of `integrity_obj_atomic`/`call_kernel_integrity`: under
  `PasRefined`, every admissible turn respects `Integrity` (intra = trivial witness /
  cross = `Discharged p w`). Replace the `admissible : True` placeholder with a real
  "this is a kernel transition" hypothesis.
- `confinement_preserved` — `PasRefined` preserved across a turn (authority never grows
  beyond the policy upper bound). Replace the `step : True` placeholder.
- `lossy_attenuation_only` — `ρ_in a ≤ a ∧ ρ_out a ≤ a`: crossing a vat boundary only
  ATTENUATES (the Heyting `≤`); loss = revocation-by-construction.

### 4. `Confluence.lean` — I-confluence, the THIRD judgement (with/after Authority)
- `admits_sound` — the `FinalityRule.admits` gate: a cell may select **tier-1**
  (causal-only / coordination-free / partition-tolerant) **iff** its invariant `I`
  is I-confluent (`∀ x y, I x → I y → I (x ⊔ y)`, BEC Thm 3.1 over the cell's
  join-semilattice state). Needs the real classifier over the write-set × state-lattice
  (`discoveries §3.7`); soundness = a tier-1 cell's concurrent merges preserve `I`.
- `nonpairwise_escalation` — when `I` is NOT I-confluent, contention is a
  **sum/coverage predicate over the WHOLE concurrent set** (three pairwise-fine spends
  jointly overspend), not pairwise; the coupled fragment escalates to consensus on that
  predicate (CryptoConcurrency COD). **Independent of Core**: `balance ≥ 0` is linear
  (conserved) but not I-confluent; a grow-only set is I-confluent but not linear — so
  this is a genuinely separate obligation, not derivable from `conservation_ordinary`.
  Precedent: Gomes–Kleppmann (SEC in Isabelle), Burckhardt, certified-mergeable-RDTs,
  Katara; CALM/Hydro for compiling the I-confluent fragment. Feeds Boundary: the
  per-cell tier is what `JointTurn` consumes when deciding cross-group blocking.

### 5. `Boundary.lean` — coinductive `▶`-guarded bisimulation (LAST)
- `sound_of_step_complete` — **THE keystone**: `StepComplete Impl … → Sound Impl Spec
  x`. Needs the coinductive `Sound`/`IsBisim` discharged via the `Later` guard (typed
  off `previous_receipt_hash`); productivity from the guard, soundness from
  contractivity in the full `StepInv`.
- `step_complete_of_sound` — the converse (the `iff` half).
- `boundary_respecting_sound` — links the coinductive `BoundaryRespecting` to
  `Authority.Integrity`.
- **BUILD-NEW (spec'd in `dregg2-multicell-privacy §5`, to apply when the prover
  recovers):** add a **`JointTurn`** equalizer object — `sharedTurnId` + a
  `JointBinding` hypothesis carrying CG-2 (turn-identity pullback) ⊗ CG-5 (cross-side
  conservation), and `joint_sound : (∀i, StepComplete (Cᵢ)) → JointBinding →
  Sound (JointTurn)`. **The binding is a PREMISE, NEVER derived from the per-cell
  `Sound`s** — `study-category §1.4` proves deriving it would be unsound (`νF₁ ⊗ νF₂`
  is not the final coalgebra of a product behaviour; the binding lives in the *base*
  category as an equalizer, outside any tensored `step`). Also add `set_program`
  upgrade admissibility to `Positional` with the `older_version ⇒ signature_fallback`
  lemma (`upgrade_never_bricks`), and the conservation functor's commitment target
  instance (`commitment_conservation`) for value-privacy.

**§8 caveat:** crypto-soundness (the binding/extractability of `Verify P w`) is a
*circuit* obligation, discharged separately; the Lean law treats `Verify` as a
decidable oracle. **NEVER merge crypto-soundness into the Lean law.** The Lean↔Rust
bridge is backend #8 of `dregg-dsl-differential` (Lean = golden oracle; empirical
cross-validation over `sorry`'d regions, not certification).

---

## Dependency graph (what blocks what)

```
Phase 0 (audit step-completeness)  ───────────────► GATES EVERYTHING BELOW
   │
   ├─► Phase 1 (collapses) ──────────┐  (independent; cheap; do early)
   │                                 │
   └─► Phase 2 (soundness spine) ◄────┘  the critical path
          │   auth-in-proof · effects-fold · value rib · chainlink/obsadvance · return-projection
          │
          ├─► Phase 3 (JointTurn ⊗)        needs per-cell step-completeness (Phase 2)
          │        │   REUSE γ.2; binding = HYPOTHESIS, not derived
          │        │
          │        └─► Phase 5 (privacy)   value/graph tiers ride the proof + JointTurn
          │
          ├─► Phase 4 (cell coalgebra/GC)  surfaces CellProgram; REUSE captp
          │
          └─► Phase 6 (anti-brick set_program)  ── MUST precede ──► Phase 7 (recursion swap)
                                                                       │ DEFERRED, not soundness-critical
                                                                       │ behind RecursionBackend trait

Metatheory (parallel track):  Core + Laws ─► Authority/Positional ─► Boundary (+ JointTurn)
   Lean = golden oracle; bridges to Rust via dregg-dsl-differential backend #8.
```

**The Lean↔Rust bridge.** Lean is the *golden oracle* for the semantic layer
(`Verify`-as-decidable, the laws, the bisimulation); Rust stays the
crypto/proving/transport/wasm engine. They are reconciled by **differential testing**
(`dregg-dsl-differential`), not by certification — empirical cross-validation over the
`sorry`'d regions. Do NOT reimplement the prover in Lean; do NOT merge crypto-soundness
into the law.
