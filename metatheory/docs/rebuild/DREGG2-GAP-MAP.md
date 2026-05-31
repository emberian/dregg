# DREGG2-GAP-MAP — what is still MISSING / under-implemented in the Lean dregg2 model that real execution needs

> **Scope / method.** READ-ONLY assessment. No code changed. Synthesizes the four grounding/design
> docs (`docs/rebuild/EFFECT-ISA-DESIGN.md`, `GROUND-AUTH-ATTESTATION.md`, `GROUND-STORAGE-PROGRAMS.md`,
> `CARRY-FORWARD-SYNTHESIS.md`, the two `FAITHFULNESS-AUDIT*.md`, `COVERAGE-{AUTHORITY,DISTRIBUTED}.md`)
> against a direct read of the Lean (`metatheory/Dregg2/**`). The driving directive: **carry forward the
> Rust semantics (or a coherently-extrapolated vision), not a Lean fiction.** The SWAP framing is
> non-negotiable: routing the node through the Lean FFI is a MASSIVE staged rewrite gated on (a) the
> executor being complete, (b) the FFI hosting a real turn, and (c) the differential (kernel-vs-new-Rust,
> NEVER vs the buggy old dregg1) as the safety net. This map prioritizes the genuine fills, gives each a
> soundness-criticality, rough size, and the verification it needs, then orders them by dependency and
> splits PREREQUISITE-FOR-SWAP from ABOVE-CORE.

---

## 0. The one structural finding that reframes everything: the EXECUTABLE TURN is narrow

The single most important fact for the swap is not any individual feature gap — it is that **the FFI's
actual executable turn is far narrower than the proved law-surface implies.** The swap routes the node
through `@[export] dregg_exec_full_turn` (`Dregg2/Exec/FFI.lean:936`), which marshals a `List FullAction`
and runs `TurnExecutorFull.execFullTurn`. `FullAction` (`Dregg2/Exec/TurnExecutorFull.lean:255-265`) has
**exactly five variants**: `balance` (transfer), `delegate`, `revoke`, `mint`, `burn`. `execFull`
(`TurnExecutorFull.lean:280-286`) dispatches only those five.

Everything else dregg2 has proved — the escrow holding-store, the note nullifier-set, committed escrow,
the CG-5 cross-cell half-edge, the vat-boundary membrane, the per-asset conservation vector, the storage
cell-programs — lives in **separate law-modules with their own state types or their own private
`RecChainedState` chains, none of which `FullAction`/`execFullTurn`/the FFI can dispatch.** They are
proved *about* a machine, but they are not *in the one machine the swap runs.*

So the gap list below has a recurring shape: **"the law is proved in module X, but X is not wired into
the `FullAction` dispatch the FFI exports."** The unifying meta-fill — **widen `FullAction` + `execFull`
into the genuine effect core and re-prove the conservation/authority/forward-sim spine over the wider
sum** — is the spine the swap actually depends on. Most fills below are facets of it.

This is *good news*: each facet is already proved in isolation, so the integration is re-binding proved
lemmas to a wider dispatch, not greenfield theory. But until it happens, "the FFI hosts a real turn" is
only true for a 5-effect kernel.

---

## 1. The prioritized fill-list

Criticality scale: **SOUNDNESS-CRITICAL** (a wrong/absent model lets the kernel accept an invalid state
transition — the kernel would be *unsound* as a replacement) · **INTEGRATION-CRITICAL** (the semantics
are proved but not in the executable turn the FFI runs — the swap can't route through them) ·
**FIDELITY** (a Lean abstraction is load-bearingly thinner than the Rust; not unsound but the proof
covers less than the running system does) · **ABOVE-CORE** (a genuine capability, not a prerequisite for
a sound minimal swap).

---

### FILL 1 — Per-asset-class balance: the `CONSERVATION_VECTOR` (the #1 soundness gap)

- **What.** The executable kernel conserves **one scalar**. `RecordKernel.balOf`
  (`Dregg2/Exec/RecordKernel.lean:47`) reads a single `"balance"` field; `recTotal`
  (`RecordKernel.lean:104`) sums that one field over `accounts`; `recKExec_conserves`
  (`RecordKernel.lean:208`) and the whole `TurnExecutorFull` spine conserve exactly that scalar. A
  dregg cell holds **many** assets (`AssetId`), and conservation must be **per-asset**, never one
  aggregate (`EFFECT-ISA-DESIGN.md:315,320-323`; `cand-A §1.3`). A scalar kernel cannot conserve more
  than one asset class: it would accept a turn that mints asset B while burning an equal amount of asset
  A (scalar-conserving, per-asset-violating).
- **Where.** Scalar: `RecordKernel.lean:41,47,104,208`; rides through `TurnExecutorFull.lean` and the
  FFI (`FFI.lean:58-71,369,936`). A correct per-asset model **already exists but is unintegrated**:
  `Dregg2/Exec/MultiAsset.lean` has `bal : MACellId → AssetId → ℤ` (`:46`) and the keystone
  `maExec_conserves_per_asset` (`MultiAsset.lean:130`). It is imported only by `Conserve.lean` and
  `Exec/Effect.lean` — **NOT by `RecordKernel`/`TurnExecutorFull`/`FFI`.** So the per-asset law is a
  sibling toy; the executable kernel the swap runs is scalar.
- **Soundness-criticality.** **SOUNDNESS-CRITICAL — the single biggest one.** Without it the kernel is
  unsound for any multi-asset state, which dregg is. This must be CORE before the kernel replaces Rust
  (`EFFECT-ISA-DESIGN.md:323,343`).
- **Rough size.** **Large.** Generalize `balOf`/`recTotal`/`recKExec` (and every effect's debit/credit) from
  a scalar `"balance"` field to an asset-indexed map; re-prove `recKExec_conserves` per-asset; re-thread
  through `TurnExecutorFull` and the FFI codec. The proof template is `MultiAsset.maExec_conserves_per_asset`
  — the work is porting it onto the *record* kernel and re-binding all downstream lemmas. Ripples like
  FID-ESCROW did, but wider (touches every Conservative effect + the FFI wire codec).
- **Verification.** Per-asset `recKExec_conserves` over the record kernel; a forward-sim that the
  abstract `Spec` step conserves each asset class; an adversarial differential exhibiting a
  scalar-conserving-but-per-asset-violating turn that the new kernel rejects (the negative test is what
  proves it's not the old scalar law wearing a vector hat).

---

### FILL 2 — Integrate the escrow holding-store / note nullifier-set into the executable turn

- **What.** FID-ESCROW (#116) landed a **faithful** holding-store: `RecordKernelState.escrows`
  (`RecordKernel.lean:97`), `escrowHeld` (`:392`), the combined conserved total `recTotalWithEscrow`
  (`RecordKernel.lean:395`), and `createEscrowK`/`releaseEscrowK`/`refundEscrowK`
  (`RecordKernel.lean:~439-490`) that do the real single-cell-debit-into-side-table (not the old paired
  two-cell shadow), with `escrow_create_conserves_combined` PROVED. The note path has a real nullifier
  SET (`noteSpendChain`, `EffectsPaired.lean:588`) with `noteSpend_no_double_spend` PROVED. **But none of
  this is in `FullAction`** (`TurnExecutorFull.lean:255-265` has no escrow/note/obligation variant), so
  the FFI's `execFullTurn` cannot perform an escrow lock, a settle, or a note spend. The proved
  semantics are stranded outside the executable turn.
- **Where.** Proved-and-faithful: `RecordKernel.lean:49-97,333-520`, `EffectsPaired.lean:426-680`.
  Missing from the dispatch: `TurnExecutorFull.lean:255-286` and the FFI codec `FFI.lean:759-936`.
- **Soundness-criticality.** **INTEGRATION-CRITICAL.** The semantics are sound; the gap is that the
  swap can't route an escrow/note turn through the kernel at all. A node that can't lock escrow or spend
  a note is not a dregg successor.
- **Rough size.** **Medium.** Add `createEscrow/releaseEscrow/refundEscrow/noteSpend` (and obligation
  variants) to `FullAction`; extend `execFull` to dispatch to the already-proved chained primitives;
  extend `ledgerDelta`/`Conserving`/`fullActionInv` to use `recTotalWithEscrow` as the conserved measure
  for the escrow legs; re-prove `execFullTurn_conserves` over the combined total; extend the FFI wire
  codec. The hard theorems exist; this is re-binding + a conserved-measure swap (scalar `recTotal` →
  `recTotalWithEscrow`, and eventually the FILL-1 vector).
- **Verification.** `execFullTurn` conserves `recTotalWithEscrow` (combined cell-ledger + holding-store +
  note-supply); the double-spend negative test threaded through the full turn; the FFI differential over
  an escrow lock→settle round-trip.

---

### FILL 3 — Committed-escrow + `noteCreate` through the holding-store (the FID-ESCROW coverage REGRESSION, task #121)

- **What.** FID-ESCROW de-shadowed plain escrow/obligation/note-*spend* to the real holding-store /
  nullifier-set, but **left the committed-escrow triple and `noteCreate` on the old `pairedStep`
  two-cell-transfer shadow** — a coverage regression relative to the rest of the cluster.
  `EffectsPaired.lean:10-12` *names* `createCommittedEscrow`/`releaseCommittedEscrow`/`refundCommittedEscrow`
  in its header, but a grep finds **no holding-store definition** of them anywhere in `Dregg2/Exec/*.lean`
  (only the header mention). dregg1's `apply_create_escrow` for the committed variant
  (`apply.rs:2049`, per `EFFECT-ISA-DESIGN.md:74`) is single-cell-debit + a side-table insert of a
  *Pedersen-commitment* record + a range proof — the **same lock/settle automaton** as plain escrow with
  a commitment-typed record and a commitment-opening release predicate (`EFFECT-ISA-DESIGN.md:266,
  EffectsPaired.lean:10-11`). `noteCreate` is the commitment-insert dual of `noteSpend`
  (`EFFECT-ISA-DESIGN.md:94,250`) and currently has no nullifier-tree/holding-store insert model.
- **Where.** The shadow: `EffectsPaired.lean` `pairedStep` family (`:205-310`); the faithful target it
  must match: `RecordKernel.lean`'s `escrows` holding-store (`:333-520`) + the nullifier SET
  (`EffectsPaired.lean:588`). The de-conflation theorem `escrow_obligation_note_are_distinct`
  (`EffectsPaired.lean:626`) covers escrow/obligation/note-*spend* but NOT the committed triple or
  noteCreate.
- **Soundness-criticality.** **FIDELITY (regression).** A committed escrow modeled as a
  balance-conserving two-cell transfer is *exactly* the FID-ESCROW failure mode the project already
  rejected once (matching a Lean simplification, not the Rust). It is not unsound for a single committed
  escrow viewed in isolation, but it conflates two distinct conserved domains and re-introduces the
  shadow FID-ESCROW killed.
- **Rough size.** **Small-Medium.** Reuse the `EscrowRecord`/`escrows` machinery with a
  commitment-typed payload + an opening-predicate settle; reuse the note nullifier-set for a
  commitment-insert `noteCreateChain`. The crypto (Pedersen/range proof) stays a `CryptoPortal`
  hypothesis (`EffectsPaired.lean:48-52`), exactly as `noteSpend` carries it.
- **Verification.** `committed_escrow_create_conserves_combined` (same combined-total law as plain
  escrow); `escrow_obligation_committed_note_are_distinct` extended to the committed triple + noteCreate
  (the de-conflation must cover them); a noteCreate→noteSpend round-trip conserving the note supply.

---

### FILL 4 — `StateConstraint` vocabulary 16 → ~74 (the storage programs need it)

- **What.** The Lean `StateConstraint` (`Dregg2/Exec/Program.lean:82-103`) has ~16 variants
  (`fieldEquals/Ge/Le`, `immutable`, `writeOnce`, `monotonic`, `strictMono`, `fieldDelta`, `not`,
  `fieldLeField`, `sumEquals`, `sumEqualsAcross`, `fieldDeltaInRange`, `allowedTransitions`, `anyOf`,
  `boundDelta`). The Rust `cell/src/program.rs` evaluator has **74 variants**, and the real storage
  cell-program templates need ones the Lean **does not have**: `RateLimit`/`RateLimitBySum`,
  `SenderAuthorized`, `WitnessedPredicate`, `TemporalGate`, `PreimageGate`, `BoundedBy`
  (`GROUND-STORAGE-PROGRAMS.md:189-190,214,257-263`). `Program.lean:20-23` *honestly defers* these to
  "dedicated passes" (and `boundDelta` is DECLARED but its single-cell evaluator returns `true`,
  `Program.lean:99-102`). Consequence: the Lean cannot *evaluate* `RelayOperator` (needs `BoundedBy` +
  `RateLimitBySum`) or `BlindedQueue` (needs `WitnessedPredicate`) — exactly the templates the
  storage-as-cell-programs thesis rests on (`GROUND-STORAGE-PROGRAMS.md:182-190`).
- **Where.** `Program.lean:55-103` (catalog) + `:110-160` (`evalSimple`/`eval`); the deferral note
  `:20-23,99-102`. Rust ground truth: `cell/src/program.rs:45,161,307,489,597`.
- **Soundness-criticality.** **FIDELITY → SOUNDNESS-CRITICAL for storage userspace.** Storage is
  DSL-userspace over the effect core (`GROUND-STORAGE-PROGRAMS.md §5`, `EFFECT-ISA-DESIGN.md:272-280`),
  but a userspace program is only as sound as the constraint evaluator that gates it. A
  `RelayOperator` whose `BoundedBy` bond-bound and `RateLimitBySum` quota are *unevaluated* (return
  `true`) is an unenforced economic cell-program — the "moved-complexity" trap
  (`EFFECT-ISA-DESIGN.md:371-377`): relocating the queue automaton into the DSL without proving the
  program-obligation just moves the unverified surface.
- **Rough size.** **Medium.** Add the ~6 missing variants to `StateConstraint`, give each a real `eval`
  (the `RateLimitBySum`/`BoundedBy` arithmetic, the `SenderAuthorized` token-subject binding, the
  `WitnessedPredicate` registry dispatch — the registry already exists, `Authority/Predicate.lean`).
  Some are pure arithmetic (small); `SenderAuthorized`-to-sender-set binding and `WitnessedPredicate`
  discharge are the load-bearing ones (medium).
- **Verification.** `eval` soundness per new variant; the `RelayOperator`/`BlindedQueue` template
  invariants re-proved against the *evaluated* (not deferred) constraints; the `CapInbox`
  `SenderAuthorized`→`sender_set_root` binding closed (today `-- OPEN:`, `CapInbox.lean:318-325`).

---

### FILL 5 — Storage durability: the `CellRuntime` checkpoint `rfl`-fiction vs the real WAL

- **What.** `Dregg2/Exec/CellRuntime.lean` names `checkpoint`/`restore`/`replay` but they are pure
  in-memory `Snapshot` round-trips: `checkpoint_restore_roundtrip` is **`= rfl`**
  (`CellRuntime.lean:60`), `restore ∘ checkpoint = id` by definitional equality (`:64-65`). There is NO
  WAL, NO fsync, NO torn-write recovery, NO log truncation, NO crash model. The Rust durability
  semantics — log-before-apply + fsync + per-line BLAKE3 torn-write checksum + replay + truncate
  (`storage/src/wal.rs`), and redb ACID + atomic note-spend (`persist/src/lib.rs:625`) — are the
  load-bearing "your data survives a crash, double-spends are rejected atomically" property, and the
  Lean models **none of it** (`GROUND-STORAGE-PROGRAMS.md:217,238-246`). The replay-determinism theorems
  (`CellRuntime.lean:79,101`) are *correct coalgebra* theorems (the cache-rebuild law) but say nothing
  about durability.
- **Where.** `CellRuntime.lean:54-101`. Rust ground truth: `storage/src/wal.rs:106-299`,
  `persist/src/lib.rs:625-661`.
- **Soundness-criticality.** **FIDELITY (with a sharp `rfl`-fiction flag).** Durability is infrastructure
  *below* the ISA (`CARRY-FORWARD-SYNTHESIS.md:88-91`, `GROUND-STORAGE-PROGRAMS.md:307`) — but if the
  verified kernel is to *replace* the Rust, the crash/recovery contract must be modeled honestly
  (a log + a fault point + replay-equals-pre-crash-state), NOT renamed away as a snapshot round-trip.
  The danger is the `rfl` reads as "durability proved" when it proves nothing about crashes.
- **Rough size.** **Medium-Large** if modeled as real semantics; **Small** if explicitly relabeled as an
  honest below-ISA portal/assumption. The recommended posture: model a minimal crash/recovery semantics
  (a `WalLog`, a fault injection point, `recover (crash (apply log s)) = s`) so the durability claim has
  content; keep the redb/erasure layers as a documented host-tier assumption.
- **Verification.** `recover_from_wal` replay equals the pre-crash state under a torn-write fault; atomic
  note-spend (nullifier-insert + commitment-store) is all-or-nothing across a crash. Until then,
  explicitly relabel `checkpoint_restore_roundtrip` as a *cache-rebuild* law, not a durability law.

---

### FILL 6 — The cross-cell BoundDelta half-edge (CG-5) as a CORE effect

- **What.** dregg has **no global ledger**; a bilateral turn moves value out of ledger A and into ledger
  B, conserving neither alone — only the cross-side aggregate (`JointCell.lean:10-15`). The CG-5
  conservation is **proved on a machine** (`joint_cg5_conserves`, the half-edges cancel,
  `JointCell.lean:183-204`) — but over a bespoke `BiTurn` with its own two ledgers
  (`JointCell.lean:60-84`), **not** as a `FullAction` over the real `RecChainedState`. The intra-turn
  seed `balance_change: Option<i64>` exists in dregg1 (`action.rs:96`, `EFFECT-ISA-DESIGN.md:66,306`),
  but the **cross-cell** half-edge with a peer-existence witness (CG-5) is on the soundness-critical path
  for any multi-cell atomic commit and is not in the executable turn.
- **Where.** Proved-in-isolation: `JointCell.lean:60-254`, `JointTurn.lean`, `Hyperedge.lean`. Missing
  from: `TurnExecutorFull.lean` `FullAction`. Rust seed: `action.rs:96`,
  `StateConstraint::BoundDelta` `program.rs:747` (and the deferred Lean `boundDelta`, `Program.lean:102`).
- **Soundness-criticality.** **SOUNDNESS-CRITICAL for multi-cell atomicity.** `νF₁⊗νF₂` is not final
  (`EFFECT-ISA-DESIGN.md:325`); the cross-side existence binding is irreducible. Without a half-edge
  *effect* (with the peer-existence witness), the kernel cannot soundly commit a cross-cell atomic move
  — it would have to model it as the (wrong) global-ledger transfer.
- **Rough size.** **Medium.** Add `boundDeltaHalfEdge(peer, δ, existence-witness)` to `FullAction`; the
  conservation algebra is `JointCell.half_edges_sum_zero`; the new work is binding the peer-existence
  witness (the CG-2 shared turn-id, `JointCell.lean:45`) into the executable dispatch and re-proving the
  aggregate conservation over `RecChainedState` pairs. The boundDelta `StateConstraint` (FILL 4) is its
  single-cell evaluable companion.
- **Verification.** `execFullTurn` over a half-edge pair conserves the cross-side aggregate; a negative
  test where one half commits and the other doesn't (the existence-witness must fail-close the pair); the
  CG-2 single-identity binding (both halves pin the same turn-id).

---

### FILL 7 — Vat-boundary ρ_in / ρ_out as typed CORE effects (the membrane)

- **What.** The cap↔key crossing is *the* vat membrane (`cand-C §398`, `cand-A §11`). The Lean has a
  vat-boundary *admissibility law* (`VatBoundary.lean:67-118`, `vat_boundary_law` PROVED: cross-vat ⇒ a
  presented keys-as-caps token must discharge the request) — a real gate on the living cell. But there is
  **no ρ_out effect** (serialize a held cap-slot → a biscuit key-as-cap, attenuation-only) and **no ρ_in
  effect** (verify a key → mint a c-list slot) in `FullAction`. dregg1 splits this across
  `ExportSturdyRef`/`EnlivenRef` (the CapTP *swiss* flavor) + `Authorization::Token` (the biscuit
  carrier) with no unifying effect (`EFFECT-ISA-DESIGN.md:307-308,330-332`). A verified capability OS
  needs ρ_out/ρ_in as first-class, named-lossy primitives — this is what makes it cross-vat at all.
- **Where.** Admissibility law (proved): `VatBoundary.lean:67-118`. Carrier exists in auth modeling but
  the *effect* is missing: `Exec/CapTP.lean`, `Authority/Caveat.lean` (the token layer). Missing from:
  `FullAction`.
- **Soundness-criticality.** **SOUNDNESS-CRITICAL for cross-vat** (the membrane is the boundary of the
  whole capability discipline) but slightly **after FILLs 1-2** in dependency order — a single-vat
  kernel is sound without it; a cross-vat one is not.
- **Rough size.** **Medium.** Add `Boundary.exportKey`/`Boundary.importKey` to `FullAction`; the
  admissibility theorem `vat_boundary_law` is the gate; the new work is the cap→key serialization
  (attenuation-only, reuse `Token.attenuate`/`attenuate_narrows`, `Authority/Caveat.lean`) and the
  key→slot mint (reuse the cap-graph-add). The lossiness is the `Spec.VatBoundary.phi` morphism (whose
  functoriality is a by-design `sorry` over an abstract `Verifiable`, `VatBoundary.lean:401` per
  `FAITHFULNESS-AUDIT-CORE.md §0` — a concrete witness is proved alongside).
- **Verification.** ρ_out only attenuates (granted ≤ held on serialization); ρ_in mints only a slot the
  presented key discharges; round-trip ρ_in ∘ ρ_out is lossy-but-authority-non-amplifying.

---

### FILL 8 — The caveat / attestation FACE: the cryptographic substance (the overlooked dimension)

The turn is a **three-faced generator** — effects ⊕ caveat-gates ⊕ attestation
(`CARRY-FORWARD-SYNTHESIS.md §0`, `GROUND-AUTH-ATTESTATION.md:172-185`). dregg2 grew the EFFECTS face
deeply; the CAVEAT and ATTESTATION faces are where **the Rust is substantially richer than the Lean** and
the Lean is a fiction/overlook. These are FIDELITY fills (the algebraic discipline — attenuation-only,
discharge-monotone, six-mode dispatch — is faithfully proved; the *cryptographic* substance is absent):

- **8a. HMAC caveat-chain integrity.** Lean caveats are a bare `Ctx → Bool` (`Authority/Caveat.lean:43`);
  the real macaroon is an HMAC chain `Tᵢ = HMAC(Tᵢ₋₁, Cᵢ)` whose constant-time tail compare detects
  caveat removal/tamper (`macaroon.rs:204-262`). The Lean proves attenuation *narrows* but **cannot even
  express** that an adversary can't *remove* a caveat (`GROUND-AUTH-ATTESTATION.md:199,216-222`). This is
  an **unstated §8 obligation** — make it explicit. *Size: medium. Criticality: FIDELITY (the macaroon's
  reason to exist).*
- **8b. Third-party discharge crypto.** The discharge *monotonicity* is beautifully modeled
  (`Authority/Discharge.lean`); the cryptographic protocol — encrypted ticket/VID, ephemeral `r`
  recoverable only by the chain-replayer, bind-to-parent, 300s freshness (`caveat_3p.rs:71-102`,
  `macaroon.rs:267-347`) — is a `Bool` flip (`GROUND-AUTH-ATTESTATION.md:201-202,223-227`). *Size:
  medium. Criticality: FIDELITY.*
- **8c. Credential selective disclosure + predicate proofs.** `VC.claim` is one opaque `Nat`; `verify` is
  all-or-nothing (`Authority/Credential.lean:153-155`). The Rust headline feature — disclose an attribute
  *subset* + Gte/Lte/InRange predicate proofs over hidden attributes (`presentation.rs:256-351`) — has no
  analog (`GROUND-AUTH-ATTESTATION.md:205-206,228-230`). *Size: medium-large. Criticality: FIDELITY.*
- **8d. Anonymous multi-show unlinkability, WIRED to the credential.** The hiding law exists
  (`Privacy.lean:489-507`) but is **disconnected** from the credential `present`/`verify` path that
  actually performs multi-show (`Credential.lean` has no unlinkability statement)
  (`GROUND-AUTH-ATTESTATION.md:207,231-232`). *Size: small (re-wire an existing law). Criticality:
  FIDELITY.* (Related: task #127 DV-BLINDEDSET, the one TRIVIAL-ONLY HolderAnonymity finding.)
- **8e. Stealth + StarkDelegation as first-class auth modes.** `AuthModes.lean`'s "six modes" **omit
  Stealth entirely** and model bearer only *in the clear* — exactly the two `Authorization` variants that
  carry actor-anonymity (`authorize.rs:1252-1417`, `cell/src/stealth.rs`)
  (`GROUND-AUTH-ATTESTATION.md:209-210,236-239`). *Size: medium. Criticality: FIDELITY.*
- **8f. The repudiation / designated-verifier DIAL (a genuinely NEW axis).** dregg is hardwired to
  maximal transferability = non-repudiable; it HAS anonymity, LACKS deniability and designated-verifier
  *entirely* (grep-confirmed, no ring/chameleon/disavowal anywhere)
  (`GROUND-AUTH-ATTESTATION.md:308-346`). The Lean `Discharged` is a *single universal predicate* — which
  is precisely why the model can't express "convincing only to V." The fix is a **verifier-indexed
  `Discharged`** + a parallel private artifact (DVZK / deniable auth / ring repudiation) on the bilateral
  channel, keeping the transferable badge for the consensus/forest path. *Size: large (new theory).
  Criticality: ABOVE-CORE (a privacy capability, not a soundness prerequisite for the swap).*

> **Counter-note (carry the Lean FORWARD here):** CapTP non-amplification `granted ≤ held` is *proved* in
> `AuthModes.lean:268-296` and was *missing* from Rust `verify_captp_delivered` — task #94 already fixed
> the Rust to match. This is the FID-ESCROW pattern in reverse (the Lean is the better spec); it is DONE,
> noted here only so the gap map is complete (`GROUND-AUTH-ATTESTATION.md:241-249`, `COVERAGE-AUTHORITY.md §2`).

---

### FILL 9 — The higher-order handler tier (the comodel-morphism frontier)

- **What.** `HandlerTransformer.lean` proves a genuine `safe_transformer_composes` (safe transformers
  compose, instantiated twice — camera + forest — with teeth: `unsafe_transformer_rejected`). But it
  **honestly leaves OPEN** the conjecture's keystone: that `Fpu`-preservation *IS* the gluing condition
  (one law, not two), and the higher-order **recursive-camera** tier
  (`HandlerTransformer.lean:44-56,118-130`). The `act` functor (`Handler → Handler`'s action on a camera)
  is made explicit as a resource action because the real `Await.Handler` functor is "not yet built"
  (`HandlerTransformer.lean:118-123`). So the higher-order tier is a *frontier*, not a fill the swap needs.
- **Where.** `HandlerTransformer.lean` (the whole module, esp. the `-- OPEN:` at `:44-56,118-130`);
  context in `HANDLER-TRANSFORMER-CONJECTURE.md`, `DREGG2-FOUNDATIONS.md`.
- **Soundness-criticality.** **ABOVE-CORE.** This is the dregg4 generalization (the turn as a uniform
  3-faced generator, `CARRY-FORWARD-SYNTHESIS.md §4`), not a kernel-soundness prerequisite. The swap does
  not depend on it.
- **Rough size.** **Large / research.** Needs a shared carrier (a real `Handler → Handler` with a built
  `act` functor) before the weld stops being a pun.
- **Verification.** `Fpu`-preservation ⟺ gluing (the keystone biconditional); the recursive-camera tier.

---

### FILL 10 — Distributed-conformance gaps (consensus model, gossip, Stingray, revocation)

Per `COVERAGE-DISTRIBUTED.md`, the Lean is a strong **consensus-theory sandbox** but does not faithfully
model dregg1's distributed reality. These matter for a *node*, not for the *single-cell kernel turn*, so
they are sequenced after the core kernel for the swap, but several are CRITICAL for a faithful node:

- **10a. Consensus model fit.** `Proof/BFT.lean` models classical voting-round BFT; dregg1 runs Cordial
  Miners DAG. Task #106 (MG-CONSENSUS) modeled the *actual* DAG consensus + a safety property — verify it
  *supersedes* the inapplicable BFT theorems for the node claim (`COVERAGE-DISTRIBUTED.md §II.1`).
  *Criticality: ABOVE-CORE for the kernel; CRITICAL for a node-level claim.*
- **10b. Gossip / cordial dissemination.** All network-dependent proofs rest on the `World.recv_mono`
  oracle (`COVERAGE-DISTRIBUTED.md §II.2`); the push/pull/pull-response protocol that must *achieve*
  `recv_mono` is unformalized. *Criticality: ABOVE-CORE / honest-portal — document the oracle explicitly.*
- **10c. Stingray bounded counters** (Layer 3, `coord/budget.rs`) — concurrent spending entirely
  unmodeled (`COVERAGE-DISTRIBUTED.md §II.5`). *Criticality: ABOVE-CORE.*
- **10d. Federation revocation Merkle tree** (`federation/revocation.rs`) — absent
  (`COVERAGE-DISTRIBUTED.md §II.6`). *Criticality: ABOVE-CORE, but a security feature.*
- **10e. Coordination deadlock-freedom** — `Coordination.lean` carries `sorry` bodies (CONFIRMED-OPEN
  choreography problems, `COVERAGE-DISTRIBUTED.md §II.4`). *Criticality: ABOVE-CORE.*
- **10f. CapTP promise GC cross-vat cycle-freedom** — `Exec/CapTP.lean` documents it as `-- OPEN:`, not
  proved (`COVERAGE-AUTHORITY.md §2 HIGH`). *Criticality: ABOVE-CORE.*

---

### FILL 11 — The deferred coalgebra faces: return-projection + fork (after the living cell)

- **What.** Turns are one-directional today. The typed `Obs`-delta **return projection** (the callee
  commits, the caller awaits — the zkRPC second observation, `cand-A §2.2/§3`,
  `EFFECT-ISA-DESIGN.md:313,334`) and **fork-as-span/pushout** (the one structural hole; time-travel and
  merge derive from it, `cand-A §6`, `EFFECT-ISA-DESIGN.md:335`) are MISSING as typed effects. zkpromise/
  zkawait (task #82) is the await-engine embryo; the one-shot linear continuation typing is missing
  (`COVERAGE-AUTHORITY.md §II.5`).
- **Soundness-criticality.** **ABOVE-CORE** (CORE-but-after-the-living-cell-lands,
  `EFFECT-ISA-DESIGN.md:344-345`). Not a minimal-swap prerequisite.
- **Rough size.** **Large.** New coalgebra ops. checkpoint/restore/replay/time-travel/merge are then
  *theorems*, NOT effects (`EFFECT-ISA-DESIGN.md:346-349`) — adding them as effects is a category error.

---

## 2. Dependency order

```
                 ┌─────────────────────────────────────────────────────────┐
                 │  META-FILL: widen FullAction + execFull into the effect  │
                 │  core; re-prove conservation/authority/forward-sim spine │
                 │  over the wider sum. (FILLs 2,3,6,7 are facets of this.)  │
                 └─────────────────────────────────────────────────────────┘
                                          │
  FILL 1 (per-asset vector) ──────────────┤  (do FIRST or CONCURRENT: it changes the conserved
   SOUNDNESS-CRITICAL, large              │   MEASURE every other fill re-proves against; doing it
                                          │   late means re-proving twice)
                                          │
  FILL 2 (escrow/note → FullAction) ──────┤  depends on the conserved-measure choice (recTotal →
   INTEGRATION-CRITICAL, medium           │   recTotalWithEscrow, then the FILL-1 vector)
                                          │
  FILL 3 (committed-escrow/noteCreate) ───┤  depends on FILL 2's holding-store integration
   FIDELITY regression (#121), small-med  │
                                          │
  FILL 4 (StateConstraint 16→74) ─────────┤  independent of 1-3; PREREQ for sound storage userspace;
   FIDELITY→SOUNDNESS (storage), medium   │   the boundDelta evaluator is FILL 6's companion
                                          │
  FILL 6 (CG-5 half-edge effect) ─────────┤  depends on the wider FullAction + FILL 4's boundDelta
   SOUNDNESS-CRITICAL (multi-cell), med   │
                                          │
  FILL 7 (ρ_in/ρ_out membrane) ───────────┘  depends on the wider FullAction + the token layer
   SOUNDNESS-CRITICAL (cross-vat), med

  FILL 5 (WAL durability honesty) ── independent; do early as a RELABEL (cheap honesty), later as
   FIDELITY (rfl-fiction), med           real semantics

  FILL 8 (caveat/attestation crypto) ── 8a-8e independent FIDELITY fills (carry the Rust crypto);
   FIDELITY (8a-8e) / ABOVE-CORE (8f)    8f is a NEW axis (verifier-indexed Discharged), above core

  FILL 9  (higher-order handler tier) ── ABOVE-CORE, research frontier (dregg4)
  FILL 10 (distributed conformance) ──── ABOVE-CORE for kernel; CRITICAL for a node-level claim
  FILL 11 (return-projection + fork) ─── ABOVE-CORE, after the living cell
```

**The critical-path insight:** FILL 1 (per-asset vector) changes the **conserved measure** that FILLs
2/3/6/7 each re-prove their conservation against. Do FILL 1 first (or concurrently), or you re-prove the
spine twice (once over scalar `recTotal`, once over the vector). The cheapest sequencing is: FILL 1 →
widen `FullAction` (meta) absorbing FILLs 2/6/7 → FILL 3 (regression) → FILL 4 (storage soundness),
with FILL 5 relabeled honestly up front and FILL 8a-8e proceeding in parallel as the caveat face.

---

## 3. PREREQUISITES-FOR-SWAP vs ABOVE-CORE

The swap = delete the Rust kernel, route the node through the Lean FFI, with the differential
(kernel-vs-new-Rust) as the net. The kernel the FFI exports must be **sound** (no invalid transition
accepted) and must **host a real turn** (the executable turn must cover the effects a dregg node performs).

### PREREQUISITE FOR THE SWAP (the kernel must be sound + host a real turn)

| Fill | Why it gates the swap |
|---|---|
| **FILL 1 — per-asset vector** | A scalar-conserving kernel is *unsound* for multi-asset dregg. The #1 gap. |
| **META + FILL 2 — widen FullAction; escrow/note in the executable turn** | Today the FFI turn is 5 effects (balance/delegate/revoke/mint/burn). A node can't lock escrow or spend a note. "The FFI hosts a real turn" is false until this lands. |
| **FILL 3 — committed-escrow/noteCreate (#121)** | Closes the FID-ESCROW regression so no shadow re-enters the executable turn. |
| **FILL 4 — StateConstraint 16→74** | Storage cell-programs (`RelayOperator`/`BlindedQueue`/`CapInbox`) are unenforced (eval returns `true`) without the missing variants — moved-complexity, not soundness, unless evaluated. |
| **FILL 6 — CG-5 half-edge effect** | Multi-cell atomic commit is unsound without the cross-side half-edge (no global ledger; `νF₁⊗νF₂` not final). |
| **FILL 7 — ρ_in/ρ_out membrane** | Cross-vat is the boundary of the capability discipline; a cross-vat kernel is unsound without the typed membrane. (Single-vat sound without it — sequence after 1/2.) |
| **FILL 5 — WAL durability honesty (at least the RELABEL)** | If the kernel claims to *replace* the durable Rust store, the `rfl`-fiction must not read as "durability proved." At minimum relabel; ideally model crash/recovery. |
| **FILL 8a/8b/8e — caveat-chain integrity, 3P discharge crypto, Stealth/StarkDelegation modes** | The caveat face *gates* effects. If the Lean caveat model can't express caveat-removal or the discharge binding, the authorization gate the kernel enforces is thinner than the Rust's — the swap would *weaken* authorization. At minimum make these explicit §8 obligations; ideally model the crypto. |

### ABOVE-CORE (genuine capabilities / node-level / research; NOT swap prerequisites)

| Fill | Note |
|---|---|
| **FILL 8c/8d — selective disclosure, multi-show unlinkability wiring** | Credential richness; the gate is sound without subset-disclosure (it's all-or-nothing, conservative). Carry forward, but not a swap blocker. |
| **FILL 8f — repudiation / designated-verifier dial** | A NEW privacy axis (verifier-indexed `Discharged`). Genuinely new theory + new circuits. Above core. |
| **FILL 9 — higher-order handler tier** | dregg4 generalization; research frontier. |
| **FILL 10 — distributed conformance** (consensus-fit, gossip, Stingray, revocation, deadlock-freedom, GC cycles) | Matters for a *node-level* faithfulness claim, not the single-cell kernel turn. Several are CRITICAL for the node story; sequence after the core kernel. Document the `recv_mono` oracle explicitly. |
| **FILL 11 — return-projection + fork** | CORE-but-after-the-living-cell; checkpoint/replay/time-travel/merge are then theorems, not effects. |

---

## 4. The honest one-paragraph summary

The Lean dregg2 has proved a deep, faithful **law-surface** — but the **executable turn the FFI actually
exports is a 5-effect scalar kernel** (`TurnExecutorFull.FullAction`: balance/delegate/revoke/mint/burn,
`recTotal` over one `"balance"` field). The genuine fills that real execution needs are, in priority:
**(1) per-asset conservation vector** (the #1 soundness gap — the kernel is unsound for >1 asset; the
correct law exists in `MultiAsset.lean` but is unintegrated); **(2) widen `FullAction` to absorb the
already-proved escrow holding-store + note nullifier-set** (INTEGRATION-CRITICAL — proved but stranded
outside the executable turn); **(3) close the committed-escrow + `noteCreate` regression** through the
holding-store (#121); **(4) grow `StateConstraint` 16→74** so storage cell-programs are *evaluated*, not
deferred; **(5) make the `CellRuntime` `rfl`-checkpoint honest** about durability; **(6) the CG-5
cross-cell half-edge** and **(7) the ρ_in/ρ_out vat membrane** as CORE effects (proved in
`JointCell`/`VatBoundary` but not in the dispatch); and **(8) the caveat/attestation cryptographic
substance** (HMAC chain, 3P discharge, Stealth/StarkDelegation modes) the Rust has and the Lean abstracts
to a `Bool`. The unifying meta-fill is the same for 2/6/7: **widen the `FullAction` dispatch into the real
effect core and re-prove the conservation/authority/forward-sim spine over the wider sum, with the
per-asset vector as the conserved measure.** Above-core: the repudiation dial (a new axis), the
higher-order handler tier, distributed conformance, and the coalgebra return/fork faces. Do FILL 1 first
(it sets the conserved measure everything else re-proves against), relabel FILL 5 honestly up front, and
carry the caveat crypto in parallel.

---

*A closing couplet, since the egg is still warm:*
*five effects in the turn, but the laws number more — / the proofs sit beside the machine, not in its core;*
*so widen the dispatch, vector the conserved sum, / and the kernel that replaces will know what it's done.* 🐉🥚
