# TRUST-BASE-CENSUS — the surviving soundness carriers, adversarially classified

**Adversarial Audit, Lane 1.** Repo `/Users/ember/dev/breadstuffs` @ `main`
HEAD `b5fe0ff97` (`deos-hermes: brain-in-jail`). READ-ONLY census: this document
edits nothing but itself. Every row is grounded to `file:line`.

The faithful-commitment campaign is complete (every deployed Merkle-root felt
widened to faithful 8-felt ~124-bit, matching the ~130-bit FRI floor; a real turn
verified live). This lane stops proving it works and starts trying to make it
**lie**: enumerate every surviving trust assumption and classify each as

- **terminal-by-design** — a real external/cryptographic floor or an ember-decision, correctly named;
- **reducible-open** — labeled/read as terminal, but actually a hole an adversary could exploit or that we could close (the scar: calling a reducible hole terminal);
- **closed-but-mislabeled** — a doc/comment says open, but the code at HEAD already closes it;
- **ATTACK-SURFACE** — a genuine gap worth a dedicated refutation lane.

Method: five parallel forensic sweeps (axiom floor · carrier teeth · named seams ·
apex claim · deployed-vs-proven), each grounded independently and cross-checked
against HEAD, then reconciled below. The dominant, load-bearing finding is that
dregg's "name every residual" discipline **largely holds** under adversarial
reading — the labels are mostly accurate — with a small set of genuine
reducible-opens.

> **CORRECTION (2026-07-03, R1 deep-dive).** This census's headline "one
> honestly-named-but-understated **live ledgerless soundness gap** (the setField
> VALUE8 written-slot seam, S1/§6 R1)" was **refuted on attack**. It grounded on
> `v3OfFrozenSetField` / `fieldsCompletionFreezesExcept` — a defined-but-**not-
> deployed** descriptor. The DEPLOYED setField member (`EffectVmEmitRotationV3.lean:5363`,
> `v3OfFrozen`) freezes ALL completion lanes including the written slot's; a forge
> of the high 224 bits is UNSAT (freeze bites), so a ledgerless client is not
> fooled. The genuine residual is a **completeness** seam (honest large-value writes
> cannot prove), not a soundness forge. Proof: `circuit/tests/setfield_completion_lane_forge.rs`
> (3 green teeth). See §6 R1. **Lesson (verify-before-pessimism): ground an audit
> claim on the DEPLOYED artifact, not a same-named alternate in source.**

---

## 0. Reconciliation notes an auditor must carry

Two cross-cutting facts change how the rest of this census reads:

1. **`docs/WELD-STATE.md` is STALE-pessimistic (closed-but-mislabeled DOC).**
   It is grounded at `bae447985` and classifies all six non-custom carriers as
   "vacuous / third-edge ABSENT / `*BackingAttack.lean` STANDS." A full
   **v12-geom + v13-geom epoch landed after it** (`746435722..b5fe0ff97`, visible
   in the HEAD git log: factory `child_vk8`/hatchery `contract_hash8` octet PI
   pins, the membership `authorized_root` third-edge ROOT leg, sovereign
   `withSovereignKeyCommit`). At HEAD **all 7 carriers carry committed
   `*BindingFromFold.lean` positive flips**, each `#assert_axioms`-clean. So a
   reader who trusts WELD-STATE will *over*-pessimize. The document, not the
   system, is out of date. (This is itself a finding: the deploy census doc
   drifted behind the code.)

2. **The two claims "carriers are flipped" and "carriers are not soundly
   deployed" are BOTH true, at different layers.** The Lean flip is real; the
   *structural* residual under every flip (§2 row C0) is also real: each
   `*_binding_from_fold` rests on `SatXFold.connect`, `hfri`, and `hbacks` as
   **assumptions**, and the equation "deployed aggregate ≡ fold model" lives in
   **unverified Rust**. Do not read "the bang fired" as "the deployed aggregate
   enforces the connect." It does not, in Lean.

---

## 1. The axiom floor — the terminal cryptographic carriers

The kernel-clean allow-list is `Dregg2.cleanAxioms = [propext, Classical.choice,
Quot.sound]` (`metatheory/Dregg2/Tactics.lean:31`). `#assert_axioms` fails a build
if any pinned theorem depends on an axiom outside it. Crypto carriers are supposed
to enter as **Prop classes / typeclass hypotheses** (invisible to `collectAxioms`),
never as `axiom`-keyword declarations.

**Verified: there are exactly TWO `axiom`-keyword declarations in the whole
metatheory, and both are inert demo fixtures** — nothing real rests on them.
Zero `sorry` / `admit` / `sorryAx`. One benign `native_decide` (below).

| Carrier / axiom | file:line | Assumes | Classification | Note |
|---|---|---|---|---|
| `demoEd25519VerifyExtern : (1:Nat)=1` | `Dregg2/Widget/Basic.lean:298` | nothing (1=1) | terminal-by-design (inert) | Widget badge-tier fixture; docstring `:294` states "never used by any real dregg proof." Only consumer: `demo_via_carrier`. |
| `demoUnvettedAssumption : (2:Nat)=2` | `Dregg2/Widget/Basic.lean:299` | nothing | terminal-by-design (inert) | Sibling red-tier fixture. |
| `StarkSound` | `Circuit/CircuitSoundness.lean:382` | `verifyBatch accept ⟹ ∃ Satisfied2 witness publishing `pi.toPublished`` | **terminal-by-design** | FRI/p3 extraction, a `class … : Prop`, "NOT provable in Lean." |
| `AlgoStarkSound` | `Circuit/FriVerifierBridge.lean:75` | same extraction over the *specified* `verifyAlgo` | terminal-by-design | With `DeployedRefines` turns `StarkSound` into a theorem (`starkSound_of_verifyAlgo:106`). |
| `StarkComplete` | `Circuit/CircuitCompleteness.lean:147` | `Satisfied2 ⟹ ∃ accepting proof` | terminal-by-design | FRI completeness dual. |
| `Poseidon2SpongeCR` | `Circuit/Poseidon2Binding.lean:169` | `sponge xs = sponge ys → xs = ys` | terminal-by-design | Standard CR as injectivity. |
| `CommitSurface` CR set (`cmbInj/compInj/compNInj/leafInj/restFrame`) | `Circuit/CircuitSoundness.lean:113`; defs `Circuit/StateCommit.lean:207-229` | Poseidon combiner/node/sponge/leaf injectivity + `RestHashIffFrame` | terminal-by-design | All pure hash injectivity; `RestHashIffFrame` enumerates every kernel field incl. `heaps` — not a hidden frame law. |
| `FriExtract` | `Circuit/AggAirSound.lean:140` | in-circuit child-verifier satisfied ⟹ ∃ verifying child proof | terminal-by-design | "SNARK of a fixed verifier circuit is sound," one aggregation node. |
| `Compress8CR` | `Circuit/DeployedCapTree.lean:630` | node8 arity-16 compression injective | terminal-by-design | The shared 8-felt Merkle node CR. |
| PortalFloor kernels (`SignatureKernel/VerifierKernel/PedersenKernel/Poseidon2Kernel/Blake3Kernel/NullifierKernel/SealKernel/MacKernelE`) | `Crypto/PortalFloor.lean:102,145,…` | §8 `@[extern]` oracle + per-primitive soundness Prop | terminal-by-design | Post-cutover TCB; each `*_floor_sound` takes the carrier as explicit hypothesis. |
| `Ed25519EufCma` / `SchnorrDLHard` / BLS `SnarkOk`,`BlsAggregateOk` | `Crypto/Ed25519Reduction.lean:18`, `Crypto/SchnorrCurveField.lean`, `Crypto/BlsThreshold.lean:148-150` | EUF-CMA game / DL hardness / pairing+SNARK accept bits | terminal-by-design | Prop carriers whose negation is a concrete solver; two-sided teeth (`forge_not_eufCma`). |
| `GnarkRefines` / `TranscriptRefines` | `Circuit/FriVerifier.lean:849,861` | gnark circuit computes the SAME Bool / challenger as Lean `verifyAlgo` | terminal **code-trust** (not crypto) | A Rust/Go↔Lean *code refinement*, honestly labeled, fixture-anchored. |
| **`DeployedRefines`** | `Circuit/FriVerifierBridge.lean:92` | deployed Rust `verify_batch` accept ⟹ spec `verifyAlgo` accept | **CHECKED (terminal code-refinement, battery-backed)** — was ATTACK-SURFACE | Discharged 2026-07-03 by `circuit/tests/deployed_refines_verifier_teeth.rs` (per-tooth tamper battery, green) + a source cross-map (§6 R2): every `verifyAlgo` reject-tooth bites in the deployed `verify_batch`; no modeled check is absent. Residual = the `GnarkRefines`-class Rust↔spec refinement. |
| **`DeployedFaithful{,Eff,8}`** | `Circuit/DeployedCapTree.lean:305 / 353 / 732` | a conferring member leaf opened in the deployed depth-16 cap-tree IS backed by a real held `FacetCap` (toy-caps ↔ deployed-leaf codec faithfulness) | **reducible-open** | The ONE carrier that is a *dregg-specific representation/codec* property, not a standard crypto primitive. Sits on the authority leg (`deployedCapOpen_implies_authorizedB:327`) + the exercise hold-gate (`Dregg2.lean:652`). Honestly a `structure … : Prop`, not laundered — but provable-in-principle by modeling the leaf codec. |

**`#assert_namespace_axioms except` clauses:** the tactic supports `except`
(`Tactics.lean:155`) but **no invocation in the tree uses it** — zero keystones
rest on an excepted non-kernel axiom.

**Lone `native_decide`:** `Exec/ConditionalTurn.lean:989`, inside an anonymous
`example` over a decidable prop (`topoOrder … = none`). Sound and non-load-bearing,
but it contradicts the codebase's own "native_decide is banned" invariant
(`Tactics.lean:8`, `Claims.lean:27`) and leaks `Lean.ofReduceBool` into that
example's axiom set where no `#assert_axioms` catches it. Minor hygiene nit.

**`:= True` reference instances** (`CryptoKernel.lean:130`, `Crypto/*`) are toy
inhabitants proving each carrier interface is *inhabitable*; the apexes consume the
carriers as typeclass/hypothesis arguments and never see them, and a FALSE
counter-half is pinned (`PortalFloor.lean:466-529`). Confirmed non-vacuous.

**Verdict (floor):** the crypto floor is genuinely terminal and correctly scoped —
no dregg-specific property is parked as a crypto `axiom` — **except**
`DeployedFaithful{,Eff,8}` (a reducible codec-faithfulness property inside the
"terminal" floor) and `DeployedRefines` (a code-trust equation marketed as
verifier-out-of-TCB but never discharged). Those two are the floor's soft spots.

---

## 2. The carrier teeth — what each `BindingFromFold` proves, and its residual

**C0 — the structural residual common to ALL seven carriers.** Every
`*_binding_from_fold` is a ~7-line template of the same shape and rests its real
content on three **assumptions**, not on facts proven of the deployed AIR:

- `hfri : XLeafFriFloor E …` — the localized FRI-extraction floor (descends from
  `AggAirSound.FriExtract` via `xLeafFriFloor_of_aggFriExtract`, so not a *new*
  axiom, but still assumed in the binding theorem);
- `SatXFold.connect : f.leafCommit = f.c` — the in-circuit "connect" is modeled as
  an **assumed equality**, never proven to be enforced by the deployed descriptor;
- `hbacks` — "a verifying sub-proof exposing commitment `c` IS the real-world
  predicate," carried as a **named premise**. That is the entire semantic bridge.

So every tooth is conditional: *IF* the aggregate re-verifies the leaf AND the
connect holds AND the adapter maps sub-proof→semantics, THEN the PI is backed by a
verifying sub-proof with a determined VK. The Lean proof is a rewrite; the
load-bearing content ("the deployed aggregate equals this model") lives in
**unverified Rust** (`circuit-prove/src/*_leaf_adapter.rs`,
`prove_*_binding_node_segmented`, the descriptor pins).

**On the `*BackingAttack.lean` files (skeptic's correction):** they do NOT prove
"the deployed gate rejects a forged trace." They prove the *opposite*,
non-vacuously — `forged_deployed_accepts` exhibits a concrete forged `VmRowEnv`
the deployed transition intent ACCEPTS, yielding `deployed_admits_X` (the deployed
AIR alone is **fail-open**). The only "rejection" proven (`forged_X_unsat_demo`) is
over the abstract `SatXFold` *model*, whose `connect`/`hfri`/adapter are
assumptions. The pair establishes: "deployed-AIR-alone is vacuous; the fold *model*
rejects" — with "deployed aggregate ≡ fold model" residing in unverified Rust.

| Carrier | Binding thm (file:line) | Floor | Per-carrier residual (the gap) | Backing-attack non-vacuity | Clean? | Class |
|---|---|---|---|---|---|---|
| **custom** (strongest) | `CustomBindingFromFold.lean:147` (`custom_companion_grounded:175`) | `FriExtract`+`Poseidon2SpongeCR`+connect; `StarkSoundCustom` GONE | Smallest gap: guarantee IS "PI backed by verifying sub-proof, VK determined"; no extra off-AIR predicate. Deployed per-row gate is vacuous `True` (`| .proofBind _ => True`, `:8`), so deployed-AIR-alone binds nothing — only the fold does. + the universal C0 connect. | `CustomCarrierAttack.lean:122 deployed_admits_unbacked` / `:149`; model reject `:272` | yes `:282` | terminal-by-design (mod C0) |
| **factory** | `FactoryBindingFromFold.lean:145` (`authorized_from_fold:171`) | template | Child-VK *derivation/caps/budget* NOT in binding — the `hbacks` adapter (`:171`). BUT carrier material grounded: committed `child_vk8` (limbs 88..95) pinned PIs 47..54 (`factoryV3Carriers`), so the connect *target* is commitment-bound. Standing attacks: `deployed_admits_overbudget_factory:283`, `_outside_cap_factory:310`. | `FactoryBackingAttack.lean:256`; model reject `:259` | yes `:269` | reducible-open (mod C0) |
| **sovereign** | `SovereignBindingFromFold.lean:147` (`authorized_from_fold:172`) | template | Has the strongest *in-AIR third edge*: KEY_COMMIT chip-compress welds published teeth to the committed pubkey octet (`makeSovereignV3DeployedWide_publishes_key_commit`). BUT sequence-replay freshness stays EXECUTOR-side (`SovereignBackingAttack.lean:312 deployed_admits_replayed_sequence` STANDS); pre-state anchor off-AIR (`:248`); owner-signature semantics is assumed `hbacks`. | `SovereignBackingAttack.lean:214`; model reject `:260` | yes `:270` | reducible-open (mod C0) |
| **membership** (weakest) | `MembershipBindingFromFold.lean:134` (`authorized_from_fold:159`) | template | **Biggest tooth-vs-claim gap.** Its own companion `Emit/MembershipAuthRootEdge.lean:62` says "the fold tooth does NOT yet fully bite membership, so no `MembershipBindingFromFold` flip is claimed here" — while the binding file **claims exactly that flip.** The sender-leaf leg is an unbuilt STOP (`:37` "CANNOT be bound non-vacuously"); binding it to `B_PUBKEY_OCTET` would bind the WRONG party (`:47`, "a LAUNDERED vacuity"); the in-AIR Merkle path is unbound — "binds the TUPLE, NOT the path" (`:54`). Only the ROOT leg is refuted (`withMembershipAuthRoot_rejects_injected_root:114`). | `MembershipBackingAttack.lean:201,235`; model reject `:243` | yes `:253` | **ATTACK-SURFACE** — see §4 |
| **dsl** | `DslBindingFromFold.lean:154` (`dslWitnessed_from_fold:181`) | `FriExtract`+`Poseidon2SpongeCR`+`dslEngineBinding_of_route_commitment_factoring`+connect | The Dfa caveat has ZERO deployed-effect-vm op — `DslBackingAttack.lean:184 deployed_does_not_force_witnessed` STAYS TRUE. The vacuous ZERO-sentinel is refused **HOST-side, not in-circuit** (`:57`): a light client trusts the prover's host arm to pick the re-exec rung. | `DslBackingAttack.lean:118,106`; model reject `:282` | yes `:292` | reducible-open (mod C0) |
| **bridge** | `BridgeBindingFromFold.lean:167` (`backedAt_from_fold:200`) | `FriExtract`+`Poseidon2SpongeCR`+identity factoring+connect | **Double-mint prevention is OUTSIDE the fold.** `BackedAt`'s ¬consumed half comes from an `hfresh` hypothesis — the consume-once guard is the executor-side RE-EXEC tooth (`BridgedNullifierSet`/`bridge_ledger.rs`), NOT a fold edge; `deployed_admits_consumed_nullifier:186` STANDS. Folding the binding-only `bridge_action_air` was REFUSED as unsound (`:33`). A light client witnesses mint *identity linkage*, not that the nullifier is unconsumed. | `BridgeBackingAttack.lean:146,186`; model reject `:313` | yes `:324` | **ATTACK-SURFACE** (economic) |
| **hatchery** | `HatcheryBindingFromFold.lean:121` (`backed_from_fold:145`) | template | Rides factory's octet machinery: committed `contract_hash8` (limbs 96..103) pinned PIs 55..62, so connect target grounded. The *attestation semantics* ("sub-proof IS a verifying `CellContract` attestation") is assumed `hbacks`. Standing: `deployed_admits_wrong_contract:242`, `_unbacked_hatchery:207`. | `HatcheryBackingAttack.lean:207,242`; model reject `:227` | yes `:237` | reducible-open (mod C0) |

**Ranking (weakest tooth first):** membership → bridge → dsl → {sovereign,
factory, hatchery} → custom. Membership's binding file claims a flip its own
companion explicitly declines; bridge omits the highest-value economic attack
(double-mint) from what a light client sees.

---

## 3. The named seams (across Lean + Rust + docs)

| # | Seam | file:line (+doc) | Leaves open | Status @ HEAD | Class | If attack-surface: claim to refute |
|---|---|---|---|---|---|---|
| **S1** | **setField written-slot completion lanes** (CORRECTED — see §6 R1) | deployed: `EffectVmEmitRotationV3.lean:5363` (`v3OfFrozen`, freeze-ALL); the cited `:2913,3164` (`v3OfFrozenSetField`, except) is DEFINED-BUT-NOT-DEPLOYED; tooth `circuit/tests/setfield_completion_lane_forge.rs` | The DEPLOYED descriptor FREEZES the written slot's completion lanes (before==after), binding them to the pre-state. The forge (arbitrary high bits) is UNSAT (freeze bites #93..99). The real residual: an honest LARGE-value write cannot prove (high bytes frozen) — a completeness seam; lane 0 stays the ~31-bit fold (D6). | OPEN as a **completeness** seam (VALUE8 weld is the close; VK-affecting, gated) | reducible-open (completeness, NOT a soundness forge) | REFUTED as a forge: the deployed freeze binds; no ledgerless silent-forge. The close (VALUE8 weld) buys faithful large-value writes, not soundness. |
| **S2** | committee-restart hole | `node/src/blocklace_sync.rs:4529-4546`, `persist/src/federation.rs:84`; pin `persist/src/tests.rs:137`; `docs/HANDOFF-committee-restart-fix.md` | Full-mode commit persists a `StoredAttestedRoot` with 1 local sig at `threshold=committee-size`; on restart `verify_signatures` needs a quorum → node **fail-CLOSES** after ≥1 finalized height. Blocked by non-deterministic wall-clock preimage + votes binding `block_id`, not `merkle_root`. | OPEN — only *diagnosed* at `29ab74bc1`; Fix A/B NOT landed (domain still `-v4`) | reducible-open (liveness) | Not a safety hole — a single-sig root IS refused (safety preserved). Availability bug; Fix B designed. |
| **S3** | transferCapOpenTB 1-felt LC fallback | `sdk/src/full_turn_proof.rs:4285-4295`; `docs/reference/faithful-commitment.md:235` | The sole cap-open key with no wide twin; LC falls back to the 1-felt V3 registry → the transfer's `(actor,src,dst)` identity is bound at **~31 bits** (below the ~130-bit FRI floor). | OPEN — "the ONE load-bearing ~31-bit LC surface left"; reject tooth `:4266` bars fallback for any key WITH a wide twin | **ATTACK-SURFACE** | "Grind a 31-bit collision on a transferCapOpenTB identity felt to bind a different `(actor,src,dst)` than proved." Bounded (identity only). Close = wide-twin grind. |
| **S4** | cross-cell Σδ=0 not live-enforced | `node/src/turn_proving.rs:935,1312` (`conservation: None`); `CrossCellConservation.lean` | AIR+Lean proven & drift-green, but the deployed path proves **per-cell-isolated** transitions; no point collects ≥2 cells' deltas. A Transfer's debit/credit legs are separate proofs. | OPEN — build-half proven, live-enforcement blocked (batch collector NOT landed) | reducible-open | "Publish a turn whose per-cell legs each pass but whose cross-cell asset sum ≠ 0." Full-node ledger catches it; ledgerless LC does not get turn-wide Σδ=0. Needs a block-level batch collector. |
| **S5** | agent turn-auth Ed25519 off-circuit | `.docs-history-noclaude/LIGHT-CLIENT-TRUST-SURFACE.md:54,84`; `sovereign_leaf_adapter.rs:50` | Deployed turn auth is Ed25519, verified off-circuit (`authorize.rs`); only a Schnorr/BabyBear^8 stepping-stone is in-circuit. A ledgerless LC cannot conclude "the rightful agent authorized THIS turn." | OPEN (largest LC trust surface) | terminal-by-design | Genuine crypto floor; close needs an in-AIR Ed25519 (Edwards decompress + `[S]B=R+[k]A`) or re-bind to the in-circuit key. |
| **S6** | flat pre-limb twins zero-fill lanes 67..87 | `cell/src/commitment.rs:702,1019`; `turn/src/rotation_witness.rs:67` | The two flat-record producers enter nullifier/commitments roots as 1-felt `hash_bytes` in lanes 67..87 (the CIRCUIT trace producers DO fill genuine 8-felt node roots). | OPEN (named residual) | reducible-open (narrow) | Circuit-trace path is faithful; the flat twins are the consistency-tag path. |
| **S7** | refusal ledgerless authority + `setFieldDyn` inert | `turn/src/executor/proof_verify.rs:360,389` (`Anchor::RecordDigest`); `.../trace.rs:417` | Refusal's post-`fields_root` depends on the whole pre-cell map → anchored off-circuit (needs the openable-fields_root map-op #103). `setFieldDyn` (field_idx≥8) panics in trace-gen (dead-but-latent). | OPEN (refusal); setFieldDyn unreachable | terminal-adjacent / reducible | Full-node-safe today; ledgerless close = new soundness (openable root), not a re-point. |
| **S8** | revokeCapability apex pin lag (`Rfix 24`) | `CircuitSoundnessAssembled.lean:580`; `sdk/src/full_turn_proof.rs:2331-2352`; `faithful-commitment.md:256` | Apex `Rfix 24` still pins the authority-only `revokeCapabilityCapOpenV3`; deployed prover rides the REMOVE write wrapper via a *named* empty-c-list fallback. The Lean write wrapper + `ClosureAll` rung exist (`ClosureAll.lean:971`). | OPEN — "one re-pin + re-verify" | closed-but-mislabeled-adjacent | Low risk ("named, not a silent forge"). Move the pin onto the write wrapper. |
| **S9** | custom deeper per-turn `proofBind True→boundAt` + 4→8-felt lift | `CustomApex.lean`; `docs/reference/lean-circuit.md`; WELD-STATE §5 | The recursion-tree fold is buffed; the in-AIR per-turn `proofBind` gate is still vacuous `True` and the commitment is 4-felt. | OPEN — a separate deliberately-gated VK epoch | terminal-by-design (gated epoch) | Custom is buff-in-production for the fold; this is the deeper per-turn gate. |
| — | `Faithful8` Rust type-wall | `docs/FAITHFUL-COMMITMENT-LAW.md:84`; `.ast-grep/rules/faithful-commitment-felt.yml:46` | Planned Rust newtype capstone (only constructor = faithful conversions). Not implemented. | OPEN (defense-in-depth) | reducible-open (belt-and-suspenders) | Distinct from the existing Lean `DeployedFaithful8`. |
| — | net mTLS allowlist / captp envelope magic | `net/src/node.rs` (`ad5ca77e0`), `captp/src/store_forward.rs` (`9ac052806`) | redteam `THREAT-MODEL-FUZZ`: allowlist client w/ no client cert; wrong-magic envelope accepted | **CLOSED** at HEAD | resolved | — |
| — | DECO / Web-PKI / honest-endpoint | (not found) | Named in the brief, but **no such live seam exists** in code — the only "DECO" is "DECOUPLED" (`bilateral_aggregation_air.rs`). The real signature trust surface is S5 (Ed25519 off-circuit). | n/a | brief mislabel | — |

---

## 4. The apex claim — daylight between "axiom-clean" and "genuinely unfoolable"

**`lightclient_unfoolable`** (`Circuit/CircuitSoundness.lean:453`, `#assert_axioms`
`:1058`). From `verifyBatch (vkOfRegistry R) pi π = accept` (a light client that
runs nothing) it concludes:

```
∃ pre post, StateDecode S pi.toPublished pre post ∧ kstep pi.effect pre post
          ∧ pi.pre = S.commit pre.kernel pi.turn ∧ pi.post = S.commit post.kernel pi.turn
```

i.e. **single-transition authenticity** — an accepted batch decodes to a real
kernel step whose endpoint commitments ARE the published PIs. Carriers (the module
ledgers them at `:48-80`): `[StarkSound]` (`:382`), `Poseidon2SpongeCR` (`:455`),
`CommitSurface` CR set (`:113`), `hrefines : ∀ e, descriptorRefines …` (`:457`),
`WitnessDecodes` (`:446`). `StateDecode` faithfulness is *derived* from
`commit_binds` (`:187`), not carried.

**The grounded variant lattice** reduces these one module at a time but never
composes them into one theorem: `lightclient_unfoolable_via_algo`
(`FriVerifierBridge.lean:125`, verifier out of TCB, but rests on `DeployedRefines`;
**this file has NO `#assert_axioms` pin** — hygiene nit); the fold headline
`lightclient_unfoolable_circuit_sound` (`ClosureFinal.lean:161`, one witness floor
parametric in `pi.effect`); the grounded `lightclient_unfoolable_grounded_live`
(`GroundedApex.lean:258`, family proven whole by `descriptorRefines_complete`,
`WitnessDecodes` realized). All are `#assert_axioms`-clean.

**The 5 guarantee apexes** (`Dregg2/AssuranceCase.lean`, floor enumerated
`:22-48`; conjunction `deployed_system_secure:886`, `:942`):

| # | Apex | file:line | Guarantees | clean |
|---|---|---|---|---|
| A Authority | `authority_guarantee` | `:166` | introduce confers a non-amplifying subset; amplifying grant rejected | `:175` |
| B Conservation | `conservation_guarantee` | `:259` | every asset total = 0 on all reachable states; no cross-asset leakage per move | `:278` |
| C Integrity | `integrity_guarantee` | `:412` | executor is a memory program: receipt binds the WHOLE post-state (17 fields+log), composed to the turn | `:435`,`:470`,`:506` |
| D Freshness | `freshness_guarantee` | `:581` | a committed noteSpend: nullifier was fresh, now spent, replay fails closed | `:590` |
| E Unfoolability | `unfoolability_guarantee` | `:666` | a client checking only `verify agg.root` learns AggregateAttests ∧ whole-history conservation, no prover-supplied state | `:680` |

The apexes are genuinely axiom-clean and the honest ledgers unusually complete
(anti-vacuity teeth `amplifying_grant_rejected`, `kstepAll_not_total`,
forged-log-UNSAT all bite). The **daylight** an adversary presses:

- **A-1 (freshness is out of the apex).** `lightclient_unfoolable` proves ONLY a
  single transition at a given `pi.turn`; it says nothing about replay/ordering
  (conceded at `CircuitSoundness.lean:412-435`). Freshness rests on the deployed
  commitment-chain CAS + nonce monotonicity. The separate close
  (`CrossTurnFreshness.lean:164 no_replay`) holds over an *abstract* `TurnChain`
  and names two residuals (`:1403-1428`): **R1** wiring the real
  `runTurn`-accepted sequence into a `TurnChain` (unassembled plumbing) and **R2**
  net nonce strictly increases across prologue+body (the body half IS discharged,
  `:688`). **Refutable claim:** "a client running only `verify(pi,π)` re-accepts a
  spent transition." Conceded, not refuted; R1 is the named-but-unassembled item.
- **A-2 (the per-effect family bottoms on a limb-decode carrier the ledger cannot
  certify).** `descriptorRefines_complete` (`DescriptorRefinesComplete.lean:88`)
  assembles `∀ e` over 31 tags with no catch-all — BUT the reduction bottoms on the
  `ClosureReadouts` bundle (`<e>TraceReadout = Satisfied2 ⟹ <e>Encodes`).
  `CircuitSoundnessAssembled.lean:605` states plainly WHY the ledger-root
  `StateDecode` cannot do this (it commits only the root and never mentions the
  trace `t`, while `<e>Encode` is about `t`'s columns). So EVERY effect carries a
  `WitnessDecodes`-class limb-decode carrier — realizable, assumed, one per effect.
- **A-3 (`WitnessDecodes` realized for honest provers only).**
  `witnessDecodes_of_genuine_roots` (`WitnessRealizing.lean:83`) derives it only
  when `pi.pre/post` ARE `S.commit` of genuine `AccountsWF` kernels — a theorem for
  an honest prover, still a named carrier for the hostile "could an accepted proof
  publish roots that are commitments of NO well-formed kernel?" question (which is
  exactly what `StarkSound`'s strengthened extraction supplies).
- **A-4 (the groundings never compose).** Algo-out-of-TCB, family-proven, and
  witness-realized live in *separate weld modules*; there is no single final
  theorem carrying the minimal floor. An auditor cannot point to one `#assert`
  and read off the true trust base.

No dregg-*specific* open soundness hole surfaced at the apex; the daylight is the
standard crypto floor + named engineering seams, with A-1's R1 the most refutable
"named-but-unassembled" item.

---

## 5. The deployed-vs-proven gap

Three independent consistency checks are frequently conflated; only their
non-overlap explains the v13 catch:

1. **sha256 FP round-trip** — `sha256(descriptor.json) == its committed `_FP``
   (`circuit/src/effect_vm_descriptors.rs:1547`). Self-consistency of a file with
   its own hash.
2. **Descriptor drift gate** — Lean-emit bytes == checked-in JSON/TSV + `_FP`s
   (`scripts/check-descriptor-drift.sh`; CI `.github/workflows/ci.yml:253-287`).
   GUARDED set = `circuit/descriptors/` + five generated Rust FP files.
3. **prove+verify roundtrip** — the Rust *trace producer's* geometry actually
   satisfies the descriptor (`circuit/tests/effect_vm_wide_roundtrip.rs`).

**Neither (1) nor (2) covers (3): whether the hand-maintained Rust trace producer
agrees with the descriptor.** The v13 catch (`be732a9dd`): `EmitWideRegistryProbe`
laid the AFTER-block at stale `bb+151` while the producer read `bb+227`; Lean-emit
and TSV were mutually consistent (both stale) so (1)+(2) PASS — it was caught only
by (3) failing with `OodEvaluationMismatch`.

| # | Deployed path | file:line | Lean proves | Gated how | Class | Divergence to test |
|---|---|---|---|---|---|---|
| **D1** | Rust STARK verifier `verify_batch` vs Lean `verifyAlgo` | `circuit/src/descriptor_ir2.rs:5036` (`verify_vm_descriptor2`→`p3_batch_stark::verify_batch`); Lean `FriVerifierBridge.lean:92` | apex holds under `DeployedRefines` (Rust accept ⟹ spec accept) | **DISCHARGED-BY-TEST** (`circuit/tests/deployed_refines_verifier_teeth.rs`, green): per-tooth tamper battery — every proven `verifyAlgo` reject-tooth bites in the deployed verifier; source cross-map finds no `verifyAlgo` check absent from `verify_batch` | **CHECKED (terminal code-refinement, battery-backed)** | Residual = the same class as `GnarkRefines` (Rust↔spec refinement); the battery shows biting-by-rejection, not Boolean-equivalence-by-proof. |
| **D2** | Rust wide/rotated trace producer geometry | `circuit/src/effect_vm/trace_rotated.rs` (`AFTER_BASE`, `B_SPAN`, host widths, carrier lanes) | descriptor JSON is Lean-authoritative; producer must satisfy it | **NOT drift-gated** (outside GUARDED set); only prove+verify roundtrip binds it | **DRIFT-RISK (the v13 class, structural)** | Any wide/rotated member without a `*_proves_verifies` roundtrip test, or any producer-const change not exercised by one, diverges silently while the drift gate stays green. Audit roundtrip coverage vs the full registry. |
| **D3** | Rust executor `TurnExecutor::execute` vs Lean `recKExec` | `turn/src/executor/apply.rs`; harness `exec-lean/tests/rust_lean_parity_gauntlet.rs`, `rejection_parity.rs`; `docs/RUST-LEAN-EXECUTOR-PARITY.md` | only `Exec ⊑ Spec` for the *Lean* executor; **no `execute = recKExec` theorem** | audited + differential, NOT proven; gauntlet **self-skips when `libdregg_lean.a` absent** | ASSUMED-CARRIER / partial-CHECKED | Confirm the gauntlet actually runs in CI (needs the ~150MB linked archive); if only nightly/local, PRs don't gate executor parity. Named safe-direction residuals: `Burn`, `Mint`. |
| **D4** | Light-client VK / descriptor anchor | `circuit/descriptors/*.json`; `node/src/genesis.rs:365-383` (genesis carries per-app factory VKs, not the recursion/LC VK); `docs/HANDOFF-v13-VK-EPOCH.md §1c` | apex assumes a fixed VK/descriptor set | **No runtime VK pin/attestation** — "VK distribution" = `git push` + client rebuild | ASSUMED-CARRIER | A client built against a divergent descriptor set verifies against the wrong circuit; nothing on-chain attests the recursion/LC VK. |
| **D5** | transferCapOpenTB 1-felt fallback | `sdk/src/full_turn_proof.rs:4285-4295` | faithful 8-felt for the six roots | deployed as ~31-bit fallback (sole cap-open key w/o wide twin) | ATTACK-SURFACE (named) | = S3. Collision-grind the fold. |
| **D6** | flat `fields[0..7]` + lanes 67..87 twins | `cell/src/commitment.rs:990`; `turn/src/rotation_witness.rs:360` | faithful 8-felt roots | ~31-bit `fold_bytes32_to_bb`, **ast-grep-allowlisted** (`scripts/check-no-degraded-felt.sh`) | ATTACK-SURFACE (named, allowlisted) | = S1/S6. The `fields[0..7]`/flat-mem grind. |
| **D7** | `emit_descriptors.py` routing | `scripts/emit_descriptors.py:1-80` | routing "in lockstep with how the prover consumes" | hand-maintained Python mirroring Rust | DRIFT-RISK (meta) | If the split/routing drifts from Rust consumption, the drift gate re-derives into the wrong file and goes blind. No test pins routing == consumption. |

**Skeptic's bottom line (deployed):** the drift gate is real and CI-enforced, but
it guards only the Lean↔JSON cache edge. The two edges that actually decide whether
the *running* system matches the *proven* model — (a) Rust-verifier ≡
Lean-`verifyAlgo` (`DeployedRefines`, **now DISCHARGED-BY-TEST** — a per-tooth
tamper battery + a source cross-map finding no `verifyAlgo` check absent from the
deployed `verify_batch`; see §6 R2 / `circuit/tests/deployed_refines_verifier_teeth.rs`)
and (b) Rust-trace-producer ≡ descriptor (**tested only by whatever roundtrip
coverage happens to exist**) — the drift gate does not touch either.

---

## 6. Ranked refutation targets (the scope for the deeper lanes)

Ordered by exploitability × tractability. The first three are the highest-value:
each is a genuine hole (not a terminal floor) with a concrete refutation to try.

1. **R1 — setField written-slot completion lanes — REFUTED AS A SOUNDNESS FORGE;
   reclassified as a COMPLETENESS seam (attacked 2026-07-03, tooth
   `circuit/tests/setfield_completion_lane_forge.rs`).** The original R1 claim (a
   live ledgerless silent-forge of the written field's high 224 bits) grounded on
   the **wrong descriptor**. It cited `v3OfFrozenSetField` /
   `fieldsCompletionFreezesExcept slot` (`EffectVmEmitRotationV3.lean:2913,3164`) —
   the "except the written slot" variant that IS defined and carries the
   `setFieldV3_pins_value` keystones, **but is NOT wired into the deployed
   registry.** The DEPLOYED cohort member (`v3RegistryBare`,
   `EffectVmEmitRotationV3.lean:5363`) is `withSelectorGate SEL_SET_FIELD (v3OfFrozen
   (setFieldTickFace slot))` — the freeze-**ALL** variant (`fieldsCompletionFreezes`,
   all 56 completion lanes BEFORE↔AFTER). The committed
   `setFieldVmDescriptor2-3R24` (`rotation-v3-staged-registry.tsv`) confirms this:
   all 56 completion-lane `colEq` freezes are present, **including** the written
   slot 3's lanes (limbs 133..139). No Lean↔JSON drift — the emit and the TSV agree
   on freeze-ALL.

   **Empirical verdict (3 teeth, all green):** (a) the forge — set the written
   slot's completion lanes 1..7 to arbitrary nonzero (≠ pre-state 0), keep lane 0
   honest, recompute NEW_COMMIT to absorb them (the wire view) — is **UNSAT through
   `prove`/`verify_vm_descriptor2` alone** (the freeze bites on the active row,
   constraints #93..99). A ledgerless client is **not** fooled: the written field's
   high 224 bits are FROZEN to the pre-state (faithfully bound, the *opposite* of
   "unconstrained"). (b) An honest SMALL-value setField (high bytes zero) proves +
   verifies. (c) An honest LARGE-value setField (nonzero high bytes) **fails** the
   deployed freeze (#94) — this is the **real residual: a completeness seam**, not a
   soundness hole. The deployed setField can only faithfully write ≤ lane-0 values;
   the high bytes cannot change (and lane 0 remains the lossy ~31-bit
   `fold_bytes32_to_bb`, the separate D6/fields-octet concern). **The proper close
   is the VALUE8 weld** (force the written slot's 7 completion lanes to the declared
   `value8` params, replacing the freeze) — but it is **VK-affecting and gated**
   (an ember-decision / v-epoch), and fixes a completeness limitation, NOT a live
   forge. **(NOT exploitable on the LC wire; the freeze binds. The value8 weld is a
   completeness/faithfulness improvement, deliberately not fired here.)**

2. **R2 — `DeployedRefines` — DISCHARGED-BY-TEST for the soundness-relevant teeth
   (attacked 2026-07-03, `circuit/tests/deployed_refines_verifier_teeth.rs`).** The
   claim (`FriVerifierBridge.lean:92`) is one-directional: `verify_batch accept ⟹
   verifyAlgo accept`. The dangerous direction is the deployed verifier ACCEPTING
   what `verifyAlgo`'s proven teeth reject (a check `verifyAlgo` models but
   `verify_batch` skips → the light client trusts a weaker verifier). Two findings:

   **(a) Cross-map (by reading the deployed source):** every `verifyAlgo` reject-tooth
   has a PRESENT counterpart in the deployed `p3_batch_stark::verify_batch` (reached
   via `descriptor_ir2::verify_vm_descriptor2`, `verifier/mod.rs`): `vk.shapeMatches`→
   InstanceCountMismatch + trace-width checks; degree pin (`tableOk_rejects_wrong_degree`)
   →`validate_degree_bits` + the `LIMB_BITS` pin (`descriptor_ir2.rs:5080`);
   `foldConsistent`/`merkleRecompute_binds`→`pcs.verify` opening; quotient identity
   (`batchTablesCheck_rejects_tampered_quotient`)→`verify_constraints_with_lookups`
   OOD; bus balance (`batchTablesCheck_rejects_unbalanced_bus`)→`verify_global_sum`;
   grinding (`queryPowCheck`)→the `query_proof_of_work_bits = 16` FRI gate; publics/
   segment→transcript absorption of the public values. **No `verifyAlgo` check is
   absent from `verify_batch`** — no dangerous-direction gap found.

   **(b) Test (green):** an honest transfer proof is minted and tampered at each
   modeled field; the deployed verifier REJECTS every one. Teeth 1–2 (instance shape,
   degree pin) reject before `verify_batch` with their own diagnostics. Teeth 3–6
   (opened trace, opened quotient, bus cumulative sum, forged publics) all reject via
   the deployed FRI PCS's Fiat-Shamir + 16-bit grinding gate (`InvalidPowWitness`) —
   because `pcs.verify` absorbs commitments / opened values / publics into the
   transcript BEFORE the grinding check, so ANY mutation invalidates the honest
   proof's PoW nonce. That is a POSITIVE fact: the transcript binding + grinding teeth
   are TOTAL (no opened value floats free of Fiat-Shamir). The deep checks masked by
   that gate have their own isolated coverage on honest-transcript proofs:
   `verify_global_sum` by `ir2_denotational_differential.rs` PART K (genuinely
   unbalanced bus), the constraint/quotient tooth by `effect_vm_ir2_validate.rs`
   (forged-witness re-prove). **Residual (honestly named): the test discharges
   `DeployedRefines` at the tamper points via observable REJECTION, not a proof of
   Boolean equivalence; the irreducible remainder is the same class as
   `GnarkRefines` — a Rust↔spec code-refinement, now backed by a biting battery
   rather than 0 references.** Reclassify D1 from ATTACK-SURFACE → **CHECKED
   (terminal code-refinement, battery-backed).**

3. **R3 — the Rust trace producer is outside the drift gate (D2), the v13 class is
   structural.** The drift gate proves Lean≡JSON; producer≡JSON lives only in
   prove+verify roundtrip tests. `be732a9dd` proves this diverges silently.
   **Refutation lane:** audit roundtrip coverage across every wide/rotated/welded
   registry member and every producer host-const; find a member/const with no
   `*_proves_verifies` test and mutate its geometry to show the drift gate stays
   green while the producer diverges. **(exploitable via any coverage gap;
   tractable as a coverage audit.)**

4. **R4 — `DeployedFaithful{,Eff,8}` codec faithfulness parked in the floor (§1).**
   The one dregg-specific representation property inside the "terminal" crypto
   floor, load-bearing on the authority leg + exercise hold-gate. Provable in
   principle by modeling the deployed depth-16 cap-tree leaf codec. **Refutation /
   close:** exhibit a deployed leaf that opens as conferring but is NOT backed by a
   real held `FacetCap` (test the codec's injectivity), or discharge the hypothesis
   by proving the codec. **(medium exploitability; medium tractability.)**

5. **R5 — transferCapOpenTB ~31-bit LC binding (S3 / D5).** A live sub-floor
   commitment on a cap-open transfer's turn identity — grindable below the ~130-bit
   soundness floor, the exact class the Faithful-Commitment Law exists to kill.
   Bounded to identity, not value. **Refutation:** grind a 31-bit collision to bind
   a different `(actor,src,dst)`. **(bounded scope; tractable close = wide-twin
   grind.)**

6. **R6 — carrier structural residual C0 + membership/bridge teeth (§2).** For
   every carrier, "deployed aggregate ≡ fold model" is unverified Rust
   (`connect`/`hfri`/`hbacks` assumed). Membership's binding file claims a flip its
   own companion (`MembershipAuthRootEdge.lean:62`) explicitly declines (sender-leaf
   leg an unbuilt STOP); bridge omits double-mint from what a light client sees
   (`deployed_admits_consumed_nullifier` STANDS). **Refutation lanes:** (a) for one
   carrier, exhibit a deployed aggregate that verifies while the connect fails —
   i.e. show the Rust adapter does NOT enforce `f.leafCommit = f.c`; (b) for
   membership, forge a sender the caveat does not authorize and show a ledgerless
   client cannot see it. **(deployment-status caveat: the recent v12/v13-geom epoch
   landed the flips + carrier material, so the connect targets are commitment-bound
   for factory/sovereign/hatchery; membership/dsl remain the softest.)**

7. **R7 — cross-cell Σδ=0 not live-enforced (S4).** Turn-wide conservation proven
   in Lean/AIR but the deployed path is per-cell-isolated (`conservation: None`).
   **Refutation:** publish a turn whose per-cell legs each pass but whose cross-cell
   asset sum ≠ 0; a ledgerless client is not shown turn-wide balance. Needs a
   block-level batch collector. **(architectural close.)**

8. **R8 — executor parity may not gate CI (D3) + no runtime VK anchor (D4).**
   Confirm the Rust↔Lean executor gauntlet actually runs at PR time (it self-skips
   without the linked Lean archive); and that a light client has any independent
   check that its baked descriptors/VK match the apex's assumed set.

**Terminal-by-design (NOT refutation targets), for completeness:** `StarkSound` /
`AlgoStarkSound` / `StarkComplete` / `Poseidon2SpongeCR` / `CommitSurface` CR /
`FriExtract` / `Compress8CR` / the PortalFloor kernels / `Ed25519EufCma` /
`SchnorrDLHard` / BLS carriers (§1); the agent Ed25519 off-circuit signature seam
(S5); the custom deeper per-turn `proofBind` gated epoch (S9); the refusal
openable-root soundness step (S7). The committee-restart hole (S2) is fail-closed —
an availability/liveness bug, not a safety hole.

**Two doc-hygiene findings:** `docs/WELD-STATE.md` is stale-pessimistic (calls the
now-flipped carriers vacuous — §0); `FriVerifierBridge.lean` carries no
`#assert_axioms` pin though its docstring asserts hygiene. The brief's "DECO
Web-PKI / honest-endpoint floor" does not correspond to any live seam in code (the
real signature surface is S5).
