# APPS-READINESS: Getting the shipped starbridge-apps running on the Lean-kernel-hosted system

**Date:** 2026-05-31
**Mode:** READ-ONLY assessment. No code changed.
**Scope:** the four shipped starbridge-apps (`nameservice`, `identity`,
`subscription`, `governed-namespace`), the SDK / `app-framework` /
`dregg-storage-templates` they sit on, and the GAP to running each
through the new (Lean-FFI-hosted) kernel — under the SWAP framing
(staged rewrite gated on a real-turn FFI + the kernel-vs-new-Rust
differential, NEVER a blind delete or a match against buggy dregg1).

This complements `COVERAGE-APPS.md` (which asks *"is the app modelled in
Lean?"* → no). This document asks the operational question: *"what would
it take to RUN the app on the Lean kernel and verify it end-to-end?"* The
answer is sharper and more hopeful than COVERAGE-APPS implied, because
the constraint evaluator the apps depend on **already exists in Lean** —
it is simply not yet wired into the FFI'd executor.

---

## 0. The one load-bearing fact: WHERE the apps live vs. WHERE the FFI executes

Every shipped app is **userspace policy expressed in two generic things**:

1. **Generic effects** — only `Effect::SetField`, `Effect::EmitEvent`,
   and (for transfer/handoff) `Effect::GrantCapability` /
   `RevokeCapability`. No app introduces a domain `Effect` variant. The
   nameservice register turn is literally three `SetField`s + one
   `EmitEvent` (`starbridge-apps/nameservice/src/lib.rs:336-359`).

2. **A `CellProgram` of `StateConstraint`s** baked into the cell's
   factory descriptor — the per-cell admissibility gate. Nameservice:
   `WriteOnce(NAME_HASH)`, `Monotonic(EXPIRY)`, `WriteOnce(REVOKED)`
   (`starbridge-apps/nameservice/src/lib.rs:175-187`). The Rust gate is
   `dregg_cell::CellProgram::evaluate` (`cell/src/program.rs:1007`,
   constraint catalog at `cell/src/program.rs:597`).

The new Lean kernel, as hosted through the FFI **today**, executes a
*different* domain:

- `@[export dregg_exec_full_turn]` → `execFullTurnStep`
  (`metatheory/Dregg2/Exec/FFI.lean:937`) runs
  `TurnExecutorFull.execFullTurn` over a `List FullAction` whose only
  variants are **balance / delegate / revoke / mint / burn**
  (`dregg-lean-ffi/src/full_turn_differential.rs:244-253` mirrors the
  exact wire grammar). It decodes `{"bal":…}|{"del":…}|{"rev":…}|
  {"mint":…}|{"burn":…}` — there is **no** `SetField`/`EmitEvent`/record
  op in the wire, and it never instantiates a `RecordProgram` or calls
  `.admits`.

So the gap is **not** "the kernel can't do what the apps need" — it is
that **the FFI surface exposes the resource/capability turn-decision but
not the record/cell-program turn-decision**. The apps are entirely on the
second axis.

### The good news the coverage audit understated

The record / cell-program axis is **already modelled and proved in Lean**;
it is just behind a different (non-FFI'd) door:

- **`Dregg2/Exec/Program.lean`** (291 lines) is the *faithful Lean
  transcription* of dregg1's `RecordProgram` + `StateConstraint` catalog
  (`Program.lean:80-103`, `:200-223`). It models exactly the structural
  variants the apps use — `immutable`, `writeOnce`, `monotonic`,
  `strictMono`, `fieldDelta`, `fieldLeField`, `sumEquals`,
  `sumEqualsAcross`, `fieldDeltaInRange`, `allowedTransitions`, `anyOf`
  (Heyting ⊔), `not` (Heyting ¬), plus `cases`/`methodIs` with
  **default-deny** (`Program.lean:216-223`, proved `admits_cases_nil`
  `:235`). The `admits` evaluator is decidable, computable, `#eval`-able.

- **`Dregg2/Exec/RecordCell.lean:104`** is the gated record arrow
  `recExec : RecordProgram → method → old → RecOp → Option Value` — apply
  the op, **commit iff the program admits** (`recExec_some_iff_admits`,
  `RecordCell.lean:140`). This is precisely the `SetField`-through-
  `CellProgram.evaluate` semantics the apps depend on, with its
  commit-iff-admit law proved.

- The **storage templates already have Lean twins**, each carrying the
  real `StateConstraint` vectors and proved admissibility theorems:
  `Dregg2/Exec/PubSubTopic.lean` (326 lines, `topicProgram`
  `PubSubTopic.lean:90`, `publish_admitted` `:141`),
  `Dregg2/Exec/CapInbox.lean` (387 lines, `inboxProgram` `:77`),
  `Dregg2/Exec/RelayOperator.lean` (300 lines, `relayProgram` `:72`,
  `bond_floor_held` `:151`), `Dregg2/Exec/BlindedQueue.lean` (309 lines,
  `blinded_no_double_spend` `:129`). These mirror the Rust
  `dregg-storage-templates` modules of the same names.

The strategic consequence: the first-app pilot is **mostly a wiring +
differential task, not a modelling-from-scratch task.** The proved
machinery exists; it needs a new FFI export and a record-domain
differential harness.

---

## 1. The runtime dependency chain (what every app sits on)

```
app crate (nameservice/…)            ← FactoryDescriptor + turn-builders (pure data + signing)
  │  uses dregg_app_framework re-exports:
  │    Action, Authorization, Effect, Event, symbol   (= dregg_turn::action::*, app-framework/src/lib.rs:129)
  │    AppCipherclerk.make_action(...)                (signing; app-framework/src/cipherclerk.rs)
  │    CellProgram, StateConstraint, FieldConstraint  (= dregg_cell::*, re-exported)
  │    EmbeddedExecutor / DreggEngine                 (= dregg_sdk::embed, app-framework/src/lib.rs:102)
  ▼
dregg_turn::TurnExecutor  +  dregg_cell::CellProgram::evaluate   ← THE TWO RUNTIME PIECES TO REPLACE
  │     (turn acceptance: authority + conservation + cell-program admissibility)
  ▼
[ Lean kernel via FFI ]   ← today hosts ONLY balance/cap turn-decision (execFullTurn), FFI.lean:937
```

Every app's `register(ctx)` mounts factory descriptors + inspectors onto
a `StarbridgeAppContext` that holds an `AppCipherclerk` + an
`EmbeddedExecutor` (`starbridge-apps/nameservice/src/lib.rs:585-606`).
The executor is the swap point. The signing (`AppCipherclerk`) and the
proof-generation (SDK) are **off-kernel** and stay in Rust — the kernel's
job is *acceptance* (does this signed turn satisfy authority +
conservation + the cell program?), exactly what dregg2 proves.

---

## 2. Per-app: what it does, what it depends on, the gap

### 2.1 nameservice  — SMALLEST; RECOMMENDED PILOT

**What it does.** Per-name sovereign cells with a rent + ownership state
machine. Five turn-builders, each a `SetField`(s) + `EmitEvent`:
`register` (3 SetField + event, `lib.rs:325-362`), `renew`
(`lib.rs:373-395`), `transfer` (`lib.rs:408-435`), `revoke`
(tombstone, `lib.rs:451-472`), `set_target` (`lib.rs:487-508`).

**Cell program (the gate).** `name_cell_program()` =
`WriteOnce(NAME_HASH=2)`, `Monotonic(EXPIRY=4)`, `WriteOnce(REVOKED=5)`
(`lib.rs:175-187`). Factory adds creation-time `FieldConstraint::NonZero`
on NAME_HASH and EXPIRY (`lib.rs:249-256`). There is also an *optional*
identity-attested tier using `SenderAuthorized{CredentialSet}` +
a `WitnessedPredicate::BlindedSet` (`lib.rs:717-751`) — **not** part of
the base flow; defer it.

**Depends on.** `AppCipherclerk` signing; the turn executor;
`dregg_cell::CellProgram::evaluate` for the three constraints.

**Gap to running on the Lean kernel.**
- *Effects:* needs `SetField` + `EmitEvent` executed by the kernel — the
  FFI does neither today. But `RecordCell.applyOp`/`recExec`
  (`RecordCell.lean:63,104`) already model the SetField semantics and the
  gating; `EmitEvent` is a `Neutral` non-balance effect already modelled
  in `EffectsState.lean` (`EffectsState.lean:18`, the `SetField`/
  `EmitEvent` family).
- *Constraints:* `WriteOnce` and `Monotonic` are **already in Lean**:
  `SimpleConstraint.writeOnce`/`.monotonic` with the exact dregg1
  semantics (init-from-zero allowed; new ≥ old) — `Program.lean:67-70`,
  evaluator `Program.lean:117-127`. The fail-closed-on-absent-field
  discipline matches dregg1's `evaluate` (`Program.lean:111-130`).
- *Authority:* register/renew/transfer ride the per-cell capability
  layer (owner cap), which the kernel's cap domain
  (`authorizedB`/`mintAuthorizedB`, mirrored
  `full_turn_differential.rs:210-229`) already enforces.
- **Net gap = wiring, not modelling.** Nameservice uses ONLY constraints
  that are already proved in `Program.lean`. Nothing app-specific is
  missing from the metatheory.

**Why it is the pilot.** Smallest constraint set (3 simple transition
constraints, all already in Lean); no `SenderAuthorized` in the base
flow; no `MonotonicSequence`; no `Authorization::Custom`; single factory;
the register/renew/transfer/revoke lifecycle is a clean state machine
already exercised by `tests/lifecycle.rs` and
`integration_register_full_flow.rs`.

### 2.2 subscription  — storage-backed, mostly-Lean-modelled

**What it does.** Pub/sub topic cell: `publish` (head +1, new
message_root), `consume` (tail +1), `grant_publisher`/`grant_consumer`.
`build_publish_action` etc. emit SetField + EmitEvent
(`subscription/src/lib.rs:559-685`).

**Cell program.** A `Cases`/`MethodIs` program with an `Always`-invariant
arm + one arm per method (`subscription_program()`,
`subscription/src/lib.rs:258-420`). Constraints used: `Immutable`,
`FieldLteField` (tail ≤ head), `MonotonicSequence` (head/tail +1),
`FieldGte`, `slot_changed`, **`SenderAuthorized{PublicRoot}}`** (publisher
/ consumer membership).

**Depends on.** Same chain as nameservice + the storage-template
`PubSubTopic` shape.

**Gap.** Most of this is already the **Lean `PubSubTopic.lean`** model
(`topicProgram`, `publishConstraints`/`subscribeConstraints`,
`PubSubTopic.lean:71-90`), with `publish_admitted` proved (`:141`). Two
seams remain: (a) **`MonotonicSequence`** (strictly +1) — `Program.lean`
has `strictMono` (new > old) and `fieldDelta` (new = old + 1); +1 is
expressible as `fieldDelta f 1`, so the variant exists but the named
`MonotonicSequence` mapping should be pinned in the bridge. (b)
**`SenderAuthorized{PublicRoot}`** is sender-bound — it needs the
verify/find seam (`Program.boundDelta`/witnessed-style deferral,
`Program.lean:98-102`,`:151`); in dregg1 this is an executor-side set
membership check, modelled in dregg2 via the predicate/verifier portal
(`Authority/Predicate.lean`). **Net gap = wire SetField+Cases through the
FFI + bind the `PublicRoot` membership check to the predicate portal.**

### 2.3 identity  — credential issuer; needs the witnessed-predicate seam

**What it does.** Per-issuer sovereign cell; turn-builders
`build_issue_credential` / `revoke` / `present` / `verify_presentation`
(`identity/src/lib.rs:344-500`), each SetField/EmitEvent. The ZK heavy
lifting (blinded merkle, predicate disclosure, ring, non-revocation)
lives in `dregg-credentials`, **not** in the app and **not** on the
kernel acceptance path.

**Cell program.** `issuer_program()` = `Immutable(SCHEMA)`,
`MonotonicSequence(ISSUANCE_COUNTER)`, `Monotonic(REVOCATION_ROOT)`,
`SenderAuthorized{PublicRoot(ISSUER_AUTH_ROOT)}` (`identity/src/lib.rs:185`).

**Depends on.** Same chain + `dregg-credentials` (off-kernel) +
the `SenderAuthorized` verify seam.

**Gap.** `Immutable`/`Monotonic`/`MonotonicSequence` are in `Program.lean`.
The blocker is **`SenderAuthorized{PublicRoot}`** (same seam as
subscription) plus the fact that the **credential proof itself is verified
off-kernel** — dregg2 models verification as a *portal* (accept/reject),
not as proof-checking. So identity can run on the Lean kernel for its
*state-machine acceptance* (issuance counter monotone, schema immutable,
revocation-root append-only) while the credential ZK stays a Layer-A
carrier. **Net gap = SetField+Cases FFI wiring + `PublicRoot` membership
portal; credential ZK explicitly stays out-of-kernel (honest seam).**

### 2.4 governed-namespace  — LARGEST; needs the Authorization::Custom lane

**What it does.** Threshold-governed route table: `propose_table_update`,
`vote_on_proposal`, `commit_table_update`, `register_service`. The commit
turn carries an **`Authorization::Custom`** whose `WitnessedPredicate` is
`Custom{ vk_hash: GOVERNANCE_VK }` — a threshold-signature verifier
(`governed-namespace/src/lib.rs:79-85`, `:107-127`).

**Cell program.** A multi-arm `Cases` program: `Immutable`(committee root,
threshold), `Monotonic`(version, dispute-window), `MonotonicSequence`,
`SenderAuthorized{PublicRoot}` per method (`governance_program()`,
`lib.rs:285-460`).

**Gap.** All the *state* constraints are in `Program.lean`. The two real
blockers: (a) **`Authorization::Custom` propagation** — the kernel must
route a custom verifier vk_hash to a registered threshold-sig verifier;
in dregg2 this is the predicate-registry / verifier portal
(`Authority/Predicate.lean`, the `WitnessedPredicateKind::Custom` slot).
(b) **`SenderAuthorized{PublicRoot}`** (shared seam). This is the
heaviest app: defer it to last. **Net gap = SetField+Cases FFI wiring +
custom-verifier portal + PublicRoot portal + the threshold-sig verifier
binding (the same machinery the Bridge predicate already exercises).**

---

## 3. The constraint-coverage table (apps' vocabulary vs. Lean today)

| Constraint (Rust `program.rs:597+`) | Used by | In `Program.lean`? | Seam |
|---|---|---|---|
| `WriteOnce` | nameservice | YES (`writeOnce`, `:68`/`:120`) | none — runs today |
| `Immutable` | sub, id, gov | YES (`immutable`, `:66`/`:117`) | none |
| `Monotonic` | name, id, gov | YES (`monotonic`, `:70`/`:124`) | none |
| `StrictMonotonic` | (storage) | YES (`strictMono`, `:72`/`:126`) | none |
| `FieldDelta` | name (renew) | YES (`fieldDelta`, `:74`/`:128`) | none |
| `FieldLteField` | subscription | YES (`fieldLeField`, `:86`/`:135`) | none |
| `FieldGte`/`FieldLte` | sub, gov | YES (`fieldGe`/`fieldLe`, `:61-64`) | none |
| `SumEquals`/`SumEqualsAcross` | (storage) | YES (`:87-91`/`:137-141`) | none |
| `FieldDeltaInRange` | (storage) | YES (`:92`/`:142`) | none |
| `AllowedTransitions` | (storage SM) | YES (`allowedTransitions`, `:94`/`:146`) | none |
| `AnyOf` / `Not` | sub `slot_changed` | YES (Heyting ⊔/¬, `:96`,`:75`) | none |
| `MonotonicSequence` (+1) | sub, id, gov | PARTIAL — expressible as `fieldDelta f 1`; not named | pin the mapping |
| `SenderAuthorized{PublicRoot}` | sub, id, gov | DECLARED-ELSEWHERE — sender-bound, needs membership portal | **predicate portal** |
| `SenderAuthorized{CredentialSet}` | name (attested tier, optional) | portal | **predicate portal** |
| `Authorization::Custom{vk_hash}` | gov (commit) | portal (`WitnessedPredicateKind::Custom`) | **verifier portal** |
| `BoundDelta` (cross-cell) | (storage relay) | DECLARED, deferred to JointTurn (`:98-102`,`:151`) | JointTurn aggregate |
| `RateLimit`/`RateLimitBySum`/`TemporalGate`/`PreimageGate`/`BoundedBy`/`CapabilityUniqueness` | (storage/advanced) | NOT in `Program.lean` | model later if a pilot needs it |

**Reading:** nameservice's *entire* vocabulary is in the "none — runs
today" rows. subscription/identity add exactly one seam (`PublicRoot`
membership). governed-namespace adds two (`PublicRoot` + custom verifier).

---

## 4. PILOT RECOMMENDATION: nameservice register/renew/transfer

Nameservice is the pilot because its full base-flow constraint set
(`WriteOnce`, `Monotonic`) is already proved in `Program.lean`, its
authority rides the cap domain the FFI already enforces, and it needs
**zero** new predicate/verifier portals. It is the shortest path to a
*real app turn decided by the proved Lean kernel, cross-checked by a
differential* — which is exactly the SWAP gate the framing demands
(kernel-vs-new-Rust, not vs buggy dregg1).

---

## 5. THE FIRST CONCRETE INCREMENT (nameservice on the Lean kernel)

A staged, differential-gated increment — **add an FFI door, do not delete
the Rust executor.** Mirrors the proven `execFullTurn` cascade
(`full_turn_differential.rs`).

**Step 1 — new FFI export `dregg_exec_record_turn` over `recExec`.**
Add a sibling to `execFullTurnStep` (`FFI.lean:937`) that marshals a
record-domain turn: `{ "cell": Value, "method": Nat, "op": RecOp,
"program": RecordProgram }` → run `RecordCell.recExec`
(`RecordCell.lean:104`) → emit `{ "new": Value, "ok": Bool }`. All the
callee machinery (`applyOp`, `admits`, `evalConstraint`) is already
proved and `#eval`-able; this is a codec + `@[export]`, no new theorems.
Reuse the existing JSON `Value` grammar already in
`full_turn_differential.rs:361-377` (`{"rec":…}`/`{"int":…}`).

**Step 2 — encode the nameservice program in the wire.** `name_cell_program`
= `predicate [writeOnce "name_hash", monotonic "expiry", writeOnce
"revoked"]`. (Bridge the slot-index Rust schema, NAME_HASH=2 etc.
`lib.rs:104-122`, to the name-keyed Lean `RecordProgram` — the Lean model
is name-keyed by design, `Program.lean:11`.) Encode `register` as
`RecOp` SetFields on name_hash/owner_hash/expiry; `renew` as a
`fieldDelta`-respecting expiry bump; `transfer` as an owner SetField.

**Step 3 — the record-domain DIFFERENTIAL (the safety net).** Clone
`full_turn_differential.rs` into `dregg-lean-ffi/src/record_turn_differential.rs`:
a Rust reference reimplementing `recExec` + `admits` against the **new**
Rust `dregg_cell::CellProgram::evaluate` (`cell/src/program.rs:1007`), and
a proptest fuzzer asserting Lean `recExec` ≡ Rust `CellProgram::evaluate`
on adversarial (old, new, op) triples — register-then-reregister
(WriteOnce reject), expiry-decrement (Monotonic reject), legal renewal
(accept). This is the kernel-vs-Rust differential that gates the swap;
**never** diff against dregg1's old buggy nameservice.

**Step 4 — route one nameservice turn through it.** In the
`EmbeddedExecutor` path the app already uses
(`starbridge-apps/nameservice/src/lib.rs:585`), add a feature-gated branch
that, for a register turn, calls `dregg_exec_record_turn` and asserts the
accept/reject + post-state agree with the in-tree executor. Land it as a
new integration test alongside `tests/integration_register_full_flow.rs`.

**Step 5 — verification claim.** Once Steps 1-4 are green: *"the
nameservice register/renew/transfer admissibility decision is made by the
proved Lean `recExec`/`RecordProgram.admits`, with `WriteOnce`/`Monotonic`
soundness carried by `Program.lean`, cross-checked against the production
Rust `CellProgram::evaluate` over an adversarial fuzz domain."* That is
the first shipped app with a kernel-decided, differentially-pinned turn —
the foothold the other three apps then inherit.

**Effort.** Steps 1-2 ≈ a few days (codec + export, no new proofs).
Step 3 ≈ the bulk (mirror the existing differential harness). Step 4-5 ≈
integration. The whole pilot is **bounded by the existing proved
machinery** — no new metatheory is required for nameservice.

---

## 6. The ladder after the pilot (smallest-seam-first)

1. **nameservice** — pilot above; zero portals. (DONE = the record-FFI
   door + differential exist.)
2. **subscription / identity** — inherit the record-FFI door; add ONE
   seam: bind `SenderAuthorized{PublicRoot}` set-membership to the
   predicate portal (`Authority/Predicate.lean`). Pin the
   `MonotonicSequence ↦ fieldDelta f 1` mapping. The `PubSubTopic.lean` /
   issuer constraint models already exist; the work is the membership
   portal + the FFI wire for `Cases`/`MethodIs` programs.
3. **governed-namespace** — last; inherits the above; adds the
   `Authorization::Custom{vk_hash}` → registered-threshold-verifier
   routing (reuses the Bridge-predicate verifier-portal machinery,
   `Crypto/Bridge.lean`).

Cross-cutting deferrals (NOT pilot blockers, honest seams): cross-cell
`BoundDelta` (JointTurn aggregate), the credential/threshold ZK
proof-checking (stays off-kernel as a verify portal), and the storage-only
constraints (`RateLimit`, `TemporalGate`, `PreimageGate`, …) which no
shipped app's base flow uses.

---

## 7. Honest scope statement

- **What this buys when the pilot lands:** one shipped app's *acceptance
  decision* runs on the proved Lean kernel, with the constraint soundness
  (`WriteOnce`/`Monotonic`) machine-checked in `Program.lean` and the
  Rust↔Lean equivalence pinned by a fuzzed differential. The app's turn
  *construction* and *signing* stay in Rust (correctly — they are the
  implementation, not the spec).
- **What it does NOT buy:** it does not verify the SDK's proof generation,
  the cipherclerk's key management, the credential/threshold ZK, or
  cross-chain atomicity. Those are separate axes (see `COVERAGE-APPS.md`
  §4 Tier-3, `PHASE-BRIDGE.md`).
- **The SWAP discipline is preserved:** every step adds an FFI door + a
  kernel-vs-new-Rust differential; nothing is deleted; the differential
  is never against the old dregg1 implementation.

---

## 8. Files cited

**Apps (Rust):**
- `starbridge-apps/nameservice/src/lib.rs:104-122` (slot schema),
  `:175-187` (cell program), `:239-271` (factory), `:325-508`
  (turn-builders), `:585-677` (register/mount), `:717-824` (attested tier)
- `starbridge-apps/identity/src/lib.rs:185` (issuer_program), `:251`
  (factory), `:344-500` (turn-builders)
- `starbridge-apps/subscription/src/lib.rs:258-420` (subscription_program),
  `:559-685` (turn-builders)
- `starbridge-apps/governed-namespace/src/lib.rs:79-127` (Authorization::
  Custom commit lane), `:285-460` (governance_program)
- `app-framework/src/lib.rs:128-138` (re-export surface),
  `:102` (EmbeddedExecutor/DreggEngine), `cipherclerk.rs` (signing)
- `dregg-storage-templates/src/lib.rs:93-101` (the five templates)
- `cell/src/program.rs:53` (CellProgram), `:597` (StateConstraint catalog),
  `:1007` (evaluate)

**Kernel (Lean):**
- `metatheory/Dregg2/Exec/FFI.lean:937` (`execFullTurnStep`, the current
  FFI door — balance/cap only)
- `metatheory/Dregg2/Exec/Program.lean:80-103` (StateConstraint catalog),
  `:113-150` (evaluators), `:200-223` (RecordProgram.admits, default-deny)
- `metatheory/Dregg2/Exec/RecordCell.lean:63` (applyOp), `:104` (recExec),
  `:140` (recExec_some_iff_admits)
- `metatheory/Dregg2/Exec/EffectsState.lean:18` (SetField/EmitEvent
  non-balance family + non-interference)
- `metatheory/Dregg2/Exec/{PubSubTopic,CapInbox,RelayOperator,BlindedQueue}.lean`
  (storage-template twins with proved admissibility)

**Differential (the swap net):**
- `dregg-lean-ffi/src/full_turn_differential.rs` (the existing
  balance/cap differential — the template for the record-domain one)

---

> End of APPS-READINESS.md. READ-ONLY analysis; no code modified.
