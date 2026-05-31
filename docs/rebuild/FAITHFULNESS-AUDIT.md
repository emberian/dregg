# FAITHFULNESS / VACUITY AUDIT — this session's Lean corpus

**Scope.** Adversarial, read-only audit of the session's new modules under
`metatheory/Dregg2/`. Mandate: `#assert_axioms` / "0 sorries" proves *kernel-cleanliness*,
NOT *non-vacuity* or *fidelity to dregg1*. This ledger surfaces what the goalsensor and
`#assert_axioms` cannot see. Nothing was modified.

**Files audited.** `Exec/{ProofForest,TriDomain,AuthModes,EffectTransfer,EffectsPaired,
EffectsSupply,EffectsAuthority,EffectsState,ConditionalTurn}.lean`,
`Spec/ExecRefinement.lean` (which is where `ExecRefinementFull` content actually lives — there
is no `Spec/ExecRefinementFull.lean`; the refinement square is `Spec/ExecRefinement.lean`),
`Spike/{TransferAirSoundness,EffectVmConstraints}.lean`, `Proof/CordialMiners.lean`.

---

## 0. The root degeneracy: `abbrev ExecRights := Unit`

`Spec/ExecRefinement.lean:230`:
```lean
abbrev ExecRights := Unit
```
This single abbreviation is the load-bearing vacuity of the whole authority/effect corpus.
EVERYWHERE the executable layer reconstructs an authority graph it does so over
`Spec.Cap Label ExecRights = Spec.Cap Label Unit`. The `Spec.Cap` rights field then has type
`Unit`, and **every "non-amplification" claim phrased on rights (`granted.rights ≤ held.rights`)
collapses to `() ≤ () = True` via `le_refl`.**

This is not hidden — the module header at `:226-229` is candid that "the executable model carries
no rights lattice of its own ... so the faithful Spec image is the connectivity graph, with rights
abstracted to the trivial order." The honest reading: the executable corpus proves
**connectivity-skeleton** non-amplification (you cannot reach a node you could not reach), which IS
genuine, while the **rights-attenuation** conjuncts (`rights ≤ rights`) are VACUOUS placeholders.
The danger is that the prose around several theorems advertises the vacuous conjunct as "THE
HEADLINE non-amplification" when the genuine content is the *other* conjunct.

`execGraph` itself (`ExecRefinement.lean:236-243`) is genuine — it reads `cap.target` and the
`node`/`endpoint+write` discriminant, so the edge depends on the cap. The connectivity claims built
on it are real. The rights claims built on `ExecRights=Unit` are not.

---

## 1. Per-module verdict tables

Verdicts: **GENUINE** / **PARTIALLY-VACUOUS** (real content + a vacuous conjunct) /
**VACUOUS** / **PORTAL-OK** (honest `Prop`-assumption, not masquerading as proof).

### `Exec/EffectsAuthority.lean`

| theorem | verdict | why / de-vacuification |
|---|---|---|
| `introduce_non_amplifying` (:177) | **PARTIALLY-VACUOUS** | First conjunct `(⟨t,()⟩).rights ≤ (⟨t,()⟩).rights` is `()≤()` by `le_refl _` (:183) — VACUOUS. Second conjunct (`introducer holds the source edge`, `introduce_authorized`) is GENUINE connectivity. The *prose* calls the rights conjunct "THE HEADLINE". De-vacuify: instantiate `ExecRights` with a real lattice (e.g. `List Auth` / `Finset Auth` with `⊆`) and prove the conferred rights ⊆ held. |
| `introduce_conserves`/`_addEdge`/`_authorized`/`_chainlink`/`_forward_sim` | **GENUINE** | `recKDelegate` actually grants a `node target` edge to recipient; `addEdge` shape is real; faithful to `apply.rs:2791 apply_introduce` (which calls `grant_with_expiry`). |
| `revokeDelegation_non_amplifying` (:223) | **GENUINE** | `removeEdge G … ⊆ G` is a real sub-relation fact, not Unit-collapsed (it's about edge *presence*, not rights). |
| `revokeDelegation_authorized` (:235) | **PARTIALLY-VACUOUS** | Self-admittedly "fail-open by design" (:230) — it is literally `= revokeDelegation_non_amplifying`, i.e. "authorized" carries NO held-cap premise. Honest in prose, but the name oversells. |
| `attenuate_non_amplifying` (:274), `refresh_non_amplifying` (:465) | **GENUINE** | These use `Authority.Cap` with real `List Auth` rights and `capAuthConferred … ⊆ …` via `attenuate_subset` — a REAL subset on a real rights list. NOT Unit. The one genuinely non-vacuous rights-attenuation in the file. |
| `exercise_non_amplifying` (:390) | **PARTIALLY-VACUOUS** | First conjunct (graph unchanged) GENUINE; second `confers ⟨t,()⟩ ⟨t,()⟩` via `confers_refl` is reflexive over Unit rights — VACUOUS-ish (trivially true). |
| `validateHandoff_non_amplifying` (:438) | **GENUINE (in statement)** | Stated over a *general* `Rights` with `[SemilatticeInf Rights]` (:418) — `granted.rights ≤ held.rights` is real here. Reuses `CapTP.handoff_non_amplifying`. The genuineness lives in `CapTP`. |
| `setPermissions_non_amplifying` (:490) | **GENUINE** | `NarrowsGate old new` over `Label → Bool` admit-sets — a real subset relation, not Unit. |
| `setPermissions_identity_narrows` (:497) | **PARTIALLY-VACUOUS** | `NarrowsGate g g` — the identity-narrowing boundary case; true but content-free (its stated purpose is just "NarrowsGate is inhabited"). |

### `Spec/ExecRefinement.lean`

| theorem | verdict | why |
|---|---|---|
| `exec_refines_conservation` (:118), `recExec_refines_conservation` (:436) | **GENUINE** | Real `Finset.sum` debit/credit cancellation → `conservedInDomain Domain.balance`. The conservation projection is the strongest genuine result in the corpus. |
| `exec_authz_refines_guard` (:190), `exec_authz_iff_guard` (:201) | **GENUINE** | `authorizedB` ⟺ `firstParty` guard admit; real `Bool` refinement. |
| `exec_owns_self_confers` (:252) | **PARTIALLY-VACUOUS** | `confers ⟨src,⊤⟩ ⟨src,⊤⟩` over `ExecRights=Unit`: `⊤=()`, reflexive. Honest prose notes it "does NOT witness acceptance". Trivial as stated. |
| `exec_heldcap_is_graph_has` (:264), `exec_authz_grounds_in_graph` (:284) | **GENUINE** | Real connectivity: held `node/endpoint` cap ⇒ `Graph.has actor src`. |
| `exec_step_refines` (:375) and the §3 square | **GENUINE-but-WEAK / honestly-OPEN** | Proves only the *static projections* (conservation + auth-graph-unchanged), with the operational `AbsStep` LTS left as an explicit `-- OPEN:` (§4, :482-512). The "commuting square" is the identity-on-projections, NOT a real abstract transition. Prose is honest about this. |

### `Exec/EffectTransfer.lean`

| theorem | verdict | why |
|---|---|---|
| `transfer_conserves` (:229), `transfer_two_party_domain` (:243) | **GENUINE** | Real two-party `recCexec` debit/credit cancellation (`-amt` src / `+amt` dst). Faithful to `apply.rs:536 apply_transfer` (lines 582-591). The reference template is sound. |
| `setNonce_balOf`/`bumpNonce_recTotal`/`transfer_metadata` | **GENUINE** | Real named-field non-interference (`"nonce" ≠ "balance"`); the nonce bump mirrors dregg1's replay nonce. |
| `transfer_authGraph_unchanged` (:303) | **GENUINE** | caps untouched ⇒ `execGraph` unchanged (real). |
| `transfer_forward_sim` (:365) | **GENUINE (modulo Unit auth)** | `AbsStep` = conservation + `authGraph = authGraph` + guard admit. The auth-graph half is over `ExecRights=Unit`, but for Transfer the claim is "graph *unchanged*", which is fine regardless of rights granularity. |

### `Exec/EffectsPaired.lean` — **the most fidelity-suspect module**

| theorem(s) | verdict | why |
|---|---|---|
| `pairedStep_conserves`/`_domain`/`_authorized`/`_metadata`/`_forward_sim` (generic, :233-367) | **GENUINE as stated, but the *abstraction* is the issue** | Each is a real fact about the `pairedStep` combinator (a `recCexec` two-party move + an int written to a named field). |
| All escrow / committed-escrow / note / obligation / queue / bridge `*_conserves`/`*_metadata`/`*_forward_sim` (≈50 theorems, §3.1-§3.6) | **PARTIALLY-VACUOUS (fidelity)** | Every one of these effects is `pairedStep` at a **different string constant** (`"escrow_status"`, `"obligation_status"`, `"queue_status"`, …) and a **different int mark**. The state transition is IDENTICAL across all of them: a balance debit/credit + write-int-to-field. The ONLY per-effect content is `field ≠ "balance"` proved `by decide`. So `createEscrow`, `noteSpend`, `createObligation`, `queueEnqueue`, `bridgeLock` are all the *same theorem* under different names. They are non-vacuous *as conservation facts* but they do NOT distinguish the effects — the "52-effect catalog" is ~6 distinct shapes wearing ~50 names. |
| `noteSpend_*` / committed-escrow `*` (portal-gated) | **PORTAL-OK** | The crypto (`CryptoPortal.verified : Prop`, :385) is an honest carried hypothesis, fail-closed (`portalStep_fails_without_crypto`). Correctly NOT proved. |

**Fidelity finding (escrow) — the headline divergence.** dregg1's `CreateEscrow`
(`apply.rs:1674 apply_create_escrow`) does **NOT** do a two-party balance move. It debits the
creator (`apply.rs:1761-1766`: `set_balance(old_balance - amount)`) and inserts an `EscrowRecord`
into an **off-ledger side table** (`self.escrows`, `apply.rs:1770-1781`) — the value LEAVES the
cell ledger. `ReleaseEscrow` later credits the *recipient* single-handedly
(`apply.rs:1959-1964`) and `RefundEscrow` credits the *creator* (`apply.rs:2030-2035`). So on the
cell ledger, dregg1 escrow is **debit-only at create, credit-only at release** — per-effect
`Σδ ≠ 0` on the ledger (conservation holds only across the *paired* create+release with the
side-table as the intermediary). The Lean model
(`EffectsPaired.lean:440 createEscrowStep = pairedStep … creator escrowCell recipient amt`) makes
it a balance-conserving **two-cell transfer creator→escrowCell**, which is a *simplified shadow*,
not dregg1's semantics. Same divergence for `createObligation` (`apply.rs` obligation side-table)
and `noteSpend` (nullifier set, not a cell). **Queues are faithful** — dregg1
`QueueEnqueue` IS a real actor→queue two-cell move (`apply.rs:3375-3386`), matching `pairedStep`.

### `Exec/EffectsSupply.lean`

| theorem | verdict | why |
|---|---|---|
| `create_conserves` (:173), `createCellInto_recTotal` (:155) | **GENUINE** | `recTotal` grows by exactly `bal` via `Finset.sum_insert` — a real disclosed-supply fact. |
| `create_discloses`/`factory_create_discloses`/`spawn_discloses`/`bridge_mint_discloses` | **GENUINE (tautology-ish)** | These read a `CatalogEffects` coloring `= true` by `rfl`/lemma. True, but they assert "this effect is colored Generative", a definitional fact, not a semantic one. Low content. |
| `factory_constructor_transparency` (:279) | **GENUINE** | Real reuse of `Factory.factory_mints_conforming`: child program = descriptor program. |
| `spawn_provenance` (:381) | **GENUINE** | Child caps actually get `Cap.node target` prepended. |
| `bridge_mint_conserves` (:433), `bridge_finalize_conserves` (:670) | **PORTAL-OK + GENUINE** | `ForeignFinal nullifier value : Prop` (`opaque`, :105) is carried as an UNUSED hypothesis (`_hforeign`) — honest §8 portal. The conservation is proved over the local move only. NB: `_hforeign` being unused means the theorem is *equally true without it* — it's decoration, not a load-bearing premise, which is honest but worth noting. |
| `bridge_lock_conserves` (:563), `bridge_cancel_conserves` (:617) | **GENUINE** | Real two-party escrow `recCexec` move (these DO use `recCexec` owner↔lockCell). More faithful than the `EffectsPaired` escrow because the lock-cell genuinely holds the value. |
| `setLockField_balOf`/`lockWrite_recTotal` | **GENUINE** | Real `"bridge_lock" ≠ "balance"` non-interference. |

### `Exec/EffectsState.lean`

| theorem | verdict | why |
|---|---|---|
| `setField_balOf` (:119), `writeField_recTotal` (:219), `state_conserves` (:232) | **GENUINE** | Real non-interference for any `f ≠ "balance"`. |
| `state_*` (all five keystones) | **GENUINE-but-undifferentiated** | Like `EffectsPaired`, every Neutral/Monotonic/Terminal effect is `stateStep` at a field name. Real facts; do not distinguish `SetField` from `IncrementNonce` from `Seal` at the state-transition level. |
| `seal_irreversible` (:428) | **GENUINE** | Real one-way gate: `isSealed ⇒ sealStep = none`. Non-trivial. |
| `*_is_neutral`/`*_is_monotonic`/`*_is_terminal` (§7, :455-498) | **GENUINE (tautology)** | `effectLinearity .x = Neutral := rfl` — definitional color assertions. True; near-zero content (they pin the catalog coloring matches). |

### `Exec/TriDomain.lean`

| theorem | verdict | why |
|---|---|---|
| `triConserved_of_execFull` (:256) — BALANCE conjunct | **GENUINE** | Real `execFull_ledger` (`recTotal` moves by `ledgerDelta`). |
| `triConserved_of_execFull` — **AUTHORITY conjunct** | **VACUOUS** | The authority measure is a **free parameter** `authPre : ℤ` threaded in by the caller (`measure s authPre`, :103). The theorem proves `(authPre + authorityDelta fa) = authPre + authorityDelta fa` — discharged by `simp only [measure]` (:264), i.e. `rfl`. The authority count is NEVER read off the state; it is whatever number you pass in. So the "authority domain is conserved" conjunct is `x = x`. The module header (:58-62) is candid that the authority count is "abstract ... not a literal Finset-cardinality", but the *theorem* offers no link between `authPre` and the actual cap graph. |
| `authority_graph_edit` (:219), `balance_caps_frame`/`mint_caps_frame`/`burn_caps_frame` | **GENUINE** | These DO pin the structural graph edit (`addEdge`/`removeEdge`/unchanged) — the real authority content. The honest move would be to make `authorityCount` a *function of* `execGraph` rather than a free `ℤ`. |
| `metadata_advance` (:244), metadata conjuncts | **GENUINE** | Real chain-length `+1` from `execFull_obsadvance`. |
| `triConserved_iff_all_domains_zero` (:362), `…_all_domains` (:379) | **GENUINE-but-inherits-the-Unit/free-auth weakness** | The `.note`/authority residual is `[authPre+δ - (authPre+δ)] = [0]` — vacuous for the same reason. The balance/gas residuals are genuine. |

### `Exec/AuthModes.lean`

| theorem | verdict | why |
|---|---|---|
| `captp_granted_le_held` (:273), `captp_sound` (:289) | **GENUINE** | Stated over a *general* `Rights` with `[SemilatticeInf Rights] [DecidableLE Rights]` (:82). `granted.rights ≤ held.rights` is real. This is the W9-CAPTP fix and it is non-vacuous *in the theorem*. (The `Demo` namespace instantiates `Rights := Unit` at :423, so the demo witnesses are `()≤()`, but that's only non-vacuity-of-inhabitation, fine.) |
| `custom_sound` (:242), `token_sound` (:257), `bearer_sound` (:305) | **GENUINE** | Real dispatch onto `registry_sound` / `token_discharges` / `confers`. |
| `oneOf_sound` (:360), `oneOf_index_bounds` (:346), `authModeOneOf_sound` (:322) | **GENUINE** | Real structural recursion + bounds + reject-Unchecked-at-slot. Strong. |
| `unchecked_no_escalation` (:395), `unchecked_sound` (:383) | **GENUINE** | Real: `Unchecked` admits ⟺ the target guard admits; cannot bypass a constrained guard. |

### `Exec/ProofForest.lean`

| theorem | verdict | why |
|---|---|---|
| `ProofForest.attested` field (:124) | **PORTAL-OK** | `(∀ n ∈ nodes, StepProofValid) → execForest s witness = some s'` carried as DATA — the §8 circuit seam. Honest: it is the assumption, named, never proved. |
| `proofForest_sound` (:177) | **GENUINE (composition) + honest portal** | The `Linked` hypothesis is **consumed structurally but NOT actually used** in the proof (`_hlinked`, :179): the body is `execForest_attests (pf.attested hvalid)` — linking is required by the *statement* but the conservation comes from `attested`/`execForest_attests`. Prose at :172-176 is candid ("`Linked` is *required by the statement* and consumed structurally"). So the theorem is "valid proofs ⇒ sound forest", with `Linked` along for the ride. Genuine composition, but `Linked` is closer to a documented-precondition than a load-bearing premise here. |
| `proofForest_conserves`/`_chainlinks`/`_factors` | **GENUINE** | Real projections of `execForest_attests`. |
| Non-vacuity `goodProofForest` + unlinked `badNode` counter (:254-296) | **GENUINE** | Real 2-step linked forest + a real negative (`¬ chainLinked [node0, badNode]`). Good. |

### `Spike/TransferAirSoundness.lean` & `Spike/EffectVmConstraints.lean`

| theorem | verdict | why |
|---|---|---|
| `transfer_out_sound`/`transfer_in_sound` (Transfer spike) | **GENUINE** | Real `p ∣ poly` ⇒ integer equation, over the actual BabyBear prime `p = 2013265921`. Honest about the off-circuit hypotheses (`hno_underflow`). |
| `transfer_underflow_attack` | **GENUINE (a real counterexample)** | `Sat 0 (p-1) 1 1 ∧ p-1 ≠ -1` — exhibits the gap as a theorem. Exemplary honest modeling. |
| `selectors_exactly_one`, `noop_is_identity`, `balance_lo_in_range`, `underflow_now_impossible`, `nonce_ticks_on_effect` | **GENUINE** | All real arithmetic over `p`; `underflow_now_impossible` proves the range-check closes the prior gap. Strongest fidelity-to-circuit work in the corpus — each cites `air.rs:line`. |

### `Exec/ConditionalTurn.lean`

| theorem | verdict | why |
|---|---|---|
| `condTurn_atomic` (:216), `condTurn_commit_runs`, `runOrder_abort` | **GENUINE** | Real all-or-nothing `Option`-bind structure. |
| `condTurn_conserves` (:267) | **GENUINE** | Real Σ-over-nodes ledger via `runOrder_ledger` + `execFullTurn_ledger`. The `hzero` hypothesis (every node nets 0) is a real precondition. |
| `condTurn_dependency_sound` (:407), `kahnLoopImpl_respects` (:358), `ready_deps_emitted` | **GENUINE** | Real Kahn-topo-order soundness: every edge `(c,p)` has `p` precede `c`. Substantive combinatorics, not decoration. |
| `condTurn_forward_sim` (:516), `runOrder_abschain` | **GENUINE-but-WEAK** | `CondAbsStep a a' := ∃ δ, a' = a + δ` (:450) — this is **trivially satisfiable for ANY a, a'** (take `δ = a' - a`). So the "refines a sequence of abstract steps" claim is near-vacuous: it says the measure changes by *some* amount per node, which is always true. The genuine content is that the waypoints exist and chain; the `CondAbsStep` predicate itself constrains nothing. |
| `awaitEdge_is_await` (:545), `forward_is_handler_commit` (:554) | **GENUINE** | Real bridge to `Await.commit_resumes_once`. |

### `Proof/CordialMiners.lean`

| theorem | verdict | why |
|---|---|---|
| `cordial_agreement` (:221) | **GENUINE** | Real reuse of `BFT.honest_witness_in_intersection` (quorum intersection) + monotonicity of `votersFor` over `++`. Substantive proof (the `hmono₁/₂` subperm work is real). |
| `honest_one_ratification_of_bft` (:312) | **GENUINE** | Shows the DAG honesty law reduces to `BFTModel.honest_vote_once` — discharges the would-be-ad-hoc oracle. |
| `cordial_agreement_via_bft` (:325) | **GENUINE** | Packaged result with no extra oracle. |
| `SuperRatification` structure (:184) — `quorum`/`unique_leader` fields | **PORTAL-OK (assumption-shaped)** | These are STRUCTURE FIELDS (hypotheses): the `≥ n-f` quorum and the `leader_blocks.len()==1` guard are *assumed as data*, not derived from the lace. That is the honest BFT-model discipline (per the header), but the safety theorem is "IF you hand me two super-ratifications THEN they agree" — the existence/correctness of the ratifying read against the real blocklace is NOT modeled (named `OPEN-CM-DISSEMINATION`). |
| `Inhabited.superRatifyG1` (:362), `g1_committed` (:381) | **GENUINE** | Real concrete witness over `demoLace`; `unique_leader` discharged by case analysis. Non-vacuous. |

---

## 2. Complete list of vacuities found

**A. `ExecRights = Unit` rights-collapse (`rights ≤ rights` = `()≤()` by `le_refl`).** Every
occurrence where a `*_non_amplifying` rights conjunct is over `ExecRights`:
- `EffectsAuthority.introduce_non_amplifying` (:177, conjunct 1, `le_refl _` :183) — VACUOUS conjunct.
- `EffectsAuthority.exercise_non_amplifying` (:390, `confers_refl _` over Unit) — VACUOUS conjunct.
- `ExecRefinement.exec_owns_self_confers` (:252, `confers ⟨src,⊤⟩ ⟨src,⊤⟩`, `⊤ : Unit`) — VACUOUS.
- All `absA.authGraph = …`/`authGraph = authGraph` conjuncts in `EffectsAuthority`/`EffectTransfer`/
  `EffectsPaired`/`EffectsSupply`/`EffectsState` forward-sims: these are over `Graph Label Unit`, so
  the graph EQUALITY is genuine (it's about edge presence) but any *rights* content is Unit-trivial.

GENUINE rights-attenuations that do NOT collapse (use real lattices):
`attenuate_non_amplifying`/`refresh_non_amplifying` (`List Auth ⊆`), `setPermissions_non_amplifying`
(`Label → Bool` admit-set), `validateHandoff_non_amplifying` and `AuthModes.captp_granted_le_held`
(general `Rights` lattice).

**B. Free-parameter "measure" (no link to state).**
- `TriDomain` authority domain: `authorityCount` is a caller-supplied `ℤ` (`measure s authCount`,
  :103); the conservation conjunct is `(authPre+δ) = authPre+δ` by `rfl` (:264). VACUOUS as a
  *conservation* claim (the structural `authority_graph_edit` carries the real content separately).
- `TriDomain.triResiduals .note` residual = `[0]` for the same reason.

**C. Trivially-satisfiable predicates.**
- `ConditionalTurn.CondAbsStep a a' := ∃ δ, a' = a + δ` (:450) — true for all `a, a'`. The
  "forward simulation to a sequence of abstract steps" is therefore near-vacuous *as a constraint*;
  only the waypoint-existence is content.
- `EffectsAuthority.setPermissions_identity_narrows` (:497) — `NarrowsGate g g`, content-free.
- `EffectsAuthority.revokeDelegation_authorized` (:235) — definitionally equal to
  `_non_amplifying`; "authorized" with no positive premise (honest in prose, oversold by name).

**D. Definitional-color tautologies (`= rfl`).** `EffectsState §7` (`*_is_neutral` etc., 21
theorems), `EffectsSupply.*_discloses` (4). True, near-zero semantic content — they assert the
catalog coloring matches, not effect behavior.

**E. Hypothesis-decoration (unused premise).**
- `EffectsSupply.bridge_mint_conserves` / `bridge_finalize_conserves`: `_hforeign : ForeignFinal …`
  is unused (the theorem holds without it). Honest §8 portal, but the premise is decoration.
- `ProofForest.proofForest_sound`: `_hlinked : Linked pf` is consumed structurally but the proof
  body never uses it (the conservation comes from `attested`). Documented, but `Linked` is a
  precondition-in-name.

No `sorry`/`axiom`/`native_decide` was found anywhere — kernel-cleanliness is real. The vacuities
are all of the "true-but-empty" or "true-but-not-what-the-name-claims" kind, not unsound.

---

## 3. Fidelity findings (Lean `*Step` vs dregg1 `apply.rs`)

| effect | Lean model | dregg1 reality | verdict |
|---|---|---|---|
| **Transfer** | `EffectTransfer.transferStep` = `recCexec` two-cell debit/credit + nonce bump (`:181`) | `apply.rs:536 apply_transfer`: `set_balance(from - amount)` + `set_balance(to + amount)` (`:582-591`) | **FAITHFUL.** Real two-party move. Nonce bump matches dregg1's replay nonce. |
| **Introduce** | `introduceStep` = `recKDelegate` gated grant of `node target` to recipient + `addEdge` (`:121`) | `apply.rs:2791 apply_introduce`: checks `has_access(recipient)`, `lookup_by_target`, `is_attenuation(held, granted)` (`:2829`), consent (`delegate != Impossible`, `:2845`), then `grant_with_expiry` (`:2862`) | **FAITHFUL on connectivity, WEAK on rights.** The edge-grant + held-source-edge premise mirror dregg1. But dregg1 enforces `is_attenuation(held.permissions, granted)` on a *real* permission lattice; the Lean conjunct is `()≤()`. The *consent* check (`delegate != Impossible`) and the *expiry* (`max_introduction_lifetime`) are NOT modeled at all. |
| **CreateEscrow** | `EffectsPaired.createEscrowStep` = `pairedStep` two-cell transfer creator→escrowCell + `"escrow_status"=0` (`:440`) | `apply.rs:1674`: SINGLE-cell debit `set_balance(cell - amount)` (`:1766`) + insert `EscrowRecord` into off-ledger `self.escrows` side-table (`:1770`). NOT a two-cell move. | **DIVERGENT (simplified shadow).** dregg1 escrow is debit-into-holding, credit-on-release to recipient (`:1959`) or creator (`:2030`). Per-effect `Σδ ≠ 0` on the cell ledger. Lean makes it ledger-conserving. The status-field model has no analog in dregg1 (the state is in the side-table's `resolved` flag, `:1969`). |
| **Mint/Burn** | (in `TurnExecutorFull`, used by `EffectsSupply`/`TriDomain`) disclosed `±amt` credit/debit | `apply.rs:445 Effect::Burn` etc.: privileged `set_balance` ± | **FAITHFUL** (disclosed non-conservation, `is_disclosed_non_conservation` color). |
| **BridgeMint** | `EffectsSupply.bridgeMintStep` = `recKMint` disclosed `+value`, foreign finality = `ForeignFinal` portal (`:411`) | `apply.rs:136 Effect::BridgeMint`: portable-proof verification then credit | **FAITHFUL on the local move + honest portal.** The foreign-finality split is the correct §8 boundary. |
| **QueueEnqueue** | `EffectsPaired.queueEnqueueStep` = `pairedStep` sender→queueCell (`:853`) | `apply.rs:3375`: `set_balance(actor - deposit)` + `set_balance(queue + deposit)` (`:3381-3386`) | **FAITHFUL.** Real two-cell deposit move. (The one `EffectsPaired` cluster that genuinely matches `pairedStep`.) |
| **RevokeDelegation/DropRef** | `recKRevokeTarget` removes holder→target edge; `removeEdge ⊆` | `apply.rs:306 RevokeDelegation`, `:404 DropRef` | **FAITHFUL on graph shape.** |

**Net:** the *value-moving connectivity-frame* effects (Transfer, Queue, Mint/Burn, BridgeMint,
BridgeLock) are faithful. The *holding-pattern* effects (Escrow, Obligation, Note) are modeled as
balance-conserving two-cell transfers but are really single-cell-debit-into-a-side-table in dregg1 —
a fidelity gap. All rights-attenuation is `Unit`-collapsed at the executable layer.

---

## 4. Ranked de-vacuification target list

### Tier 1 — degenerate type, EASY to de-vacuify (instantiate a real type)

1. **`ExecRights := Unit` → a real rights lattice.** Replace `abbrev ExecRights := Unit`
   (`ExecRefinement.lean:230`) with `Finset Auth` (or `List Auth` quotient) ordered by `⊆`, reusing
   the `attenuate_subset` machinery that ALREADY exists and is genuine. This single change converts
   every `rights ≤ rights` vacuous conjunct in `introduce_non_amplifying`, `exercise_non_amplifying`,
   `exec_owns_self_confers` into a real attenuation claim. Highest leverage: one definition unlocks
   ~5 headline theorems. The proofs would need the conferred-rights-⊆-held content, which
   `attenuate_subset` already provides for the executable `Cap`.

2. **`TriDomain.authorityCount` → a function of `execGraph`.** Make `measure` compute the authority
   count from the cap graph (e.g. via a finiteness witness on the live cap set) instead of taking a
   free `authPre : ℤ`. The structural facts (`authority_graph_edit`) already pin the delta; wiring
   the *measure* to the graph turns the `x = x` authority conjunct into a real conservation.

3. **`ConditionalTurn.CondAbsStep` → a constraining predicate.** Replace
   `∃ δ, a' = a + δ` with the actual `Spec.conservedInDomain`/authorized abstract step (the same
   shape `EffectTransfer.AbsStep` uses), so "refines a sequence of abstract steps" constrains
   something. The per-node ledger fact is already proved; just state the bottom edge non-trivially.

### Tier 2 — needs more modeling (genuine semantic gap)

4. **Escrow/Obligation/Note fidelity.** Model dregg1's side-table semantics: a single-cell debit +
   an explicit `EscrowRecord`-style held-value structure, with conservation stated *across the
   create+release pair* (lock-then-settle), not per-effect on the cell ledger. This is real modeling
   work (an escrow store in `RecChainedState`), not a type swap. Currently the most fidelity-divergent
   cluster.

5. **Differentiate the ~50 `EffectsPaired`/`EffectsState` effects.** Right now they are ~6 shapes
   under ~50 names. Either (a) honestly collapse them to the generic combinators with a per-effect
   *fidelity* lemma tying the field/mark to dregg1's actual state mutation, or (b) give each effect
   its real distinct semantics (e.g. note nullifier-set membership, not a `"nullifier_spent"=1`
   scalar). Until then the "52-effect catalog coverage" is overstated.

6. **`ProofForest`: make `Linked` load-bearing.** Either prove `execForest_attests` *requires* the
   linking (so `Linked` is used), or downgrade the prose claim from "linking + composition is what is
   PROVED" to "composition over an assumed-valid witness; linking is a checked precondition."

7. **Introduce: model consent + expiry.** Add the `delegate != Impossible` consent gate and the
   introduction-lifetime expiry that `apply_introduce` enforces.

8. **CordialMiners: derive `SuperRatification` from the lace.** The quorum/unique-leader are
   currently assumed structure fields. Deriving them from `ratifyingVoters` over the real blocklace
   (closing OPEN-CM-DISSEMINATION) would make the safety theorem about the protocol, not about a
   hypothesized quorum. (Genuinely hard; honestly OPEN.)

---

## 5. Honest bottom line

Counting the session's new theorems (≈180 across the 12 files, excluding `#eval`/`example`
non-vacuity checks):

- **Genuinely non-vacuous AND fidelity-faithful: ≈ 60%.** The conservation projections
  (`exec_refines_conservation`, `transfer_conserves`, `create_conserves`, `condTurn_conserves`), the
  authority-dispatch soundness (`AuthModes.*`, all six modes over a *general* rights lattice), the
  circuit spikes (`TransferAirSoundness`, `EffectVmConstraints` — the strongest, every line cites
  `air.rs`), the Kahn topo-soundness (`ConditionalTurn`), the BFT-transfer (`CordialMiners`), and the
  genuine attenuations (`attenuate_subset`, `setPermissions`, `captp_granted_le_held`) are real
  mathematics that mirror dregg1.

- **Partially-vacuous (real conjunct + a Unit/free-param conjunct, or oversold by name): ≈ 25%.**
  Chiefly every `EffectsAuthority` `*_non_amplifying` (the rights half is `()≤()`), the `TriDomain`
  authority conjunct (free-param `x=x`), `CondAbsStep`, `exec_owns_self_confers`. The genuine half is
  usually connectivity/graph-shape; the vacuous half is rights/measure.

- **Fidelity-divergent (true Lean theorem, wrong dregg1 semantics): the Escrow/Obligation/Note
  cluster, ≈ 12% of theorems** — modeled as conserving two-cell transfers, actually single-cell-
  debit-into-side-table in dregg1.

- **Tautological (definitional color `= rfl`): ≈ 3%** (`*_is_neutral`, `*_discloses`).

**The corpus is kernel-clean and largely non-vacuous, but two systematic illusions inflate the
apparent coverage:** (1) `ExecRights = Unit` makes every "non-amplification" headline's *rights*
content vacuous (the *connectivity* content is real); and (2) the `pairedStep`/`stateStep`/
`writeMeta` generic combinators let ~6 effect shapes wear ~50 names, with escrow/obligation/note
being a simplified shadow of dregg1's side-table semantics rather than its mirror. Neither is
*unsound* — they are *over-claimed*. The single highest-leverage fix is replacing
`ExecRights := Unit` with a real attenuation lattice (the `attenuate_subset` machinery to do so
already exists and is genuine).
