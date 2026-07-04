/-
# Dregg2.Deos — the VERIFIED-DEOS crown: "a verified desktop OS" made literal.

`docs/deos/DEOS.md` §"the verified-deos program": *"every visual/interactive primitive reduces to a
kernel theorem. None are new mathematics — they are the firmament's existing proofs (attenuation,
gateOK, the receipt chain, unfoolability) restated for pixels, affordances, and rehydration."*

`deos` is the agentic desktop userlayer: cap-confined surfaces, the certified compositor, the
web-of-cells, the rehydratable frustum-snapshots — *dregg made visual, with zero new trust*. The Rust
realization already shipped (the rehydration + affordance steel in `starbridge-web-surface`); this lane
is the PROOF that it cannot amplify / the liveness-type IS the confined fragment. The four targets, each
a kernel theorem restated for the desktop:

  1. **Surface-as-capability** (`Dregg2.Deos.Surface`) — a `Target::Surface(cell)` is a kernel
     `Cap.endpoint cell rights`; a window confers no authority beyond its rights, and a view/notify-only
     surface confers NO Granovetter edge (`viewSurface_confers_no_edge`, the
     `notifyCap_confers_no_edge` shape). Projecting a surface to fewer rights cannot amplify
     (`surface_attenuate_no_amplify` = `Dregg2.Exec.attenuate_subset`).

  2. **Membrane non-amplification** (`Dregg2.Deos.Membrane`) — the rehydration membrane composes
     attenuation across hops: `reshare A→B→C ⟹ C ⊆ B ⊆ A` (`reshare_chain_attenuates`, the per-hop
     `attenuate_subset` lifted by `List.Subset.trans`), generalized to arbitrarily-long reshare chains
     (`reshareN_attenuates`). The Rust `Membrane` is the realization; this is the proof it cannot
     amplify. A widening is darkened, not granted (`reshare_refuses_amplification`).

  3. **Rehydration confinement = the liveness-type** (`Dregg2.Deos.Rehydration`) — THE CROWN.
     `ReplayedDeterministic` IS *exactly* the confined fragment: for a non-`Live` context,
     `classify = ReplayedDeterministic ↔ every interaction was a witnessed attested turn`
     (`replayedDeterministic_iff_confined`). The doc's "derived" row, as an `↔`. The replay payoff
     (`replayedDeterministic_replays`) rides the EXISTING receipt-chain tamper-evidence
     (`Dregg2.Exec.Receipts.chain_tamper_evident`) under the §8 digest oracle, carried as NAMED
     hypotheses.

  4. **Affordance soundness** (`Dregg2.Deos.Affordance`) — a cell-affordance interaction is a verified
     turn: an agent fires ONLY the affordances its caps authorize (`fire_authorized_iff`, the
     `is_attenuation` gate `required ⊆ held`), the post-state surface binds the attested root
     (`firedSurface_binds_attested_root`, the receipt's `newCommit`), and progressive enhancement is
     progressive ATTENUATION (`projectFor_monotone`).

## Honesty ledger (legs fully discharged vs carried as named hypotheses)

  * Legs 1, 2, 4 and the leg-3 CLASSIFIER CROWN (`replayedDeterministic_iff_confined` + its dual) are
    FULLY DISCHARGED — pure structural facts over the kernel cap/attenuation lattice and the receipt
    record, no oracle, every keystone `#assert_all_clean` (kernel-clean: only `propext` /
    `Classical.choice` / `Quot.sound`).
  * Leg 3's REPLAY PAYOFF (`replayedDeterministic_replays`) carries the receipt-digest
    collision-resistance as NAMED hypotheses `HInj : Function.Injective H` / `HFresh : ∀ p, H p ≠
    genesisSentinel` — the SAME `dregg2 §8` oracle `Dregg2.Exec.Receipts.chain_tamper_evident` already
    names, NEVER a Lean axiom and NEVER an unproved hole. This is the one honest seam (the digest's
    collision-resistance), in the house honesty-ledger style: a named crypto primitive, not a laundered
    vacuity. The CROWN itself (the confinement `↔`) needs no such hypothesis.

Everything builds LOCAL (`lake build Dregg2`, cwd `metatheory/`) green + axiom-clean. `metatheory/`
only; no core-`Auth`/`Cap`/`Receipt` edit — every theorem is an existing kernel proof restated for
surfaces / membranes / rehydration / affordances.
-/
import Dregg2.Deos.Surface
import Dregg2.Deos.Membrane
import Dregg2.Deos.DerivedCell
-- The SEALED-ESCROW house-capacity, GROUNDED (`docs/deos/HOUSE-CAPACITY-FRAMEWORK.md`): an atomic
-- 2-of-2 value swap completes all-or-nothing and ONCE, proven BY REUSE of the committed-heap root
-- (`Substrate.Heap.root_binds_get`) + the one-shot Consumed discipline. deposit_both_ready (honest
-- swap) + replay_rejected (the one-shot tooth: a settled leg is a spent nullifier) +
-- nonconforming_claim_rejected + over_claim_rejected + leg_status_bound_in_root (the anti-ghost). The
-- Rust escrow_sealed.rs is wired via invariant_matches_lean_rung. #assert_all_clean.
import Dregg2.Deos.SealedEscrow
-- The STANDING-OBLIGATION house-capacity, GROUNDED: a recurring duty is discharged once-per-period,
-- on-schedule, never early or skipped, proven BY REUSE of the committed-heap root + the
-- StrictMonotonic cursor discipline (the version/supply-slot monotone law). cursor_strict_mono +
-- replay_rejected (one-shot per period) + early/over/behind-schedule teeth + cursor_bound_in_root.
-- The Rust obligation_standing.rs is wired via invariant_matches_lean_rung. #assert_all_clean.
import Dregg2.Deos.StandingObligation
-- The FUSED budget-escrow ⊗ obligation prepaid lease (P1): one atomic write advances the
-- StrictMonotonic meter cursor AND draws exactly rent from the escrowed prepaid budget, so
-- meter/pay drift is UNREPRESENTABLE (metered_equals_drawn + budget_never_overdrawn, both
-- polarities, bound in the heap root). Rust cell/src/prepaid_lease.rs. #assert_all_clean.
import Dregg2.Deos.PrepaidLease
-- The SHARE-VAULT house-capacity, GROUNDED: an ERC-4626-style vault whose minted shares equal the
-- share-price relation d·S/T, where existing holders are NEVER diluted (deposit_price_non_decreasing)
-- and the classic first-depositor INFLATION ATTACK is REJECTED (zero_mint_rejected + donation_immunity
-- via internal committed accounting). Proven BY REUSE of the committed-heap root + the derived-cell
-- share-price pattern; the Rust vault.rs share-vault is wired via share_vault_matches_lean_rung.
-- #assert_all_clean. The proven share-price is stronger than ERC-4626's exploit-prone share math.
import Dregg2.Deos.Vault
-- The CONSTRAINT-BINDING soundness core for the house-capacity in-circuit welds: a DECLARED capacity
-- caveat cannot be OMITTED. The §6 weld rungs prove a PRESENT manifest entry forces its invariant;
-- this rung closes the load-bearing gap that the entry must be present at all. The cell's declared
-- constraint-set is bound into committed state (compute_authority_digest_felt → record_digest → the
-- ~124-bit wide commit), so a verifier re-deriving the required tags and DEMANDING coverage cannot be
-- fooled by omission: omission_caught_under_binding (the soundness core, under the authority-digest CR
-- floor) + omission_rejected/unsatisfied_rejected + the escrow bridge to SealedEscrow.SettleGate.
-- #assert_all_clean. docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md.
import Dregg2.Deos.ConstraintBinding
-- PIECE 1 of the VK epoch — the CARRIER rung: the capacity manifest is FORCED on the already-deployed
-- rotated caveat carrier (caveatCommit → PI 45, in every R=24 cohort VK). Upgrades the soundness core
-- from "verifier HOLDS the committed manifest opening" to a PURE light client (commitments only):
-- carrier_manifest_forced + carrier_omission_impossible (omission on the bound leg is impossible —
-- the published manifest IS the committed one, by caveatCommit_binds) + the composed pure-light-client
-- keystone carrier_omission_caught_pure_lightclient (both bindings: caveat commit + DeclCommitBinds).
-- NOT VK-affecting (the carrier binding is already deployed; capacity tags are DATA on existing cols).
-- #assert_all_clean. docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md §6.
import Dregg2.Deos.CapacityCarrier
-- PIECE 2 of the VK epoch — the SATISFACTION rung (the genuinely-VK-affecting weld, STAGED): the
-- capacity gate's slot reads are welded IN-AIR to the rotated BEFORE/AFTER state-block FIELD columns
-- (r3..r10), so the gate verdict is FORCED by the before/after state commits a PURE light client binds
-- in the wide commit — not re-evaluated against caller-supplied initial_fields/final_fields. Upgrades
-- the cap-membership posture (SealedEscrow.settle_gate_root_bound, over the HEAP root the caller held)
-- to a pure light client over the FIELD columns the wide commit DIRECTLY absorbs: satisfaction_witnessed
-- (equal state commits ⟹ same gate verdict, REUSE of the Poseidon2SpongeCR field-binding) +
-- partial/phantom teeth + the composed keystone capacity_witnessed_pure_lightclient (coverage PIECE 1 ∧
-- satisfaction PIECE 2). The in-AIR constraint itself is STAGED in circuit/src/effect_vm/satisfaction_weld.rs
-- (NOT yet emitted into a committed welded descriptor/VK, NOT flipped). #assert_all_clean.
-- docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md §6.
import Dregg2.Deos.CapacitySatisfaction
-- The WELDED sealed-escrow satisfaction DESCRIPTOR, made REAL (the prior pass's named-only gap):
-- settleEscrowSatVmDescriptor2R24 = graduateV1 (rotateV3 settle-base) + the four selector-gated
-- satisfaction gates over the rotated FIELD columns + the selector PI pin (the deployed fifth-pin
-- shape). The REFINEMENT rung settleEscrowSatV3_forces_settle_gate proves a satisfying trace FORCES
-- the sealed-escrow gate (both legs Deposited before / Consumed after) IN-PROOF, with partial/phantom
-- UNSAT teeth. STAGED beside the deployed cohort (no live routing, no VK committed). #assert_all_clean.
import Dregg2.Deos.SettleEscrowSatDescriptor
-- The escrow capacity SELECTOR is bound to the cell's COMMITTED declaration (§6 item-2 soundness
-- keystone for the flip): HALF A — under DeclCommitBinds the selector demand is un-dodgeable by a
-- hollow declaration; HALF B — the descriptor's PI pin forces the demanded selector ON, which the
-- refinement keystone turns into the welded gate over the committed fields. So a forger can dodge the
-- weld neither by an alternate declaration nor by sel=0. SPEC + soundness of the verifier obligation
-- the still-unbuilt realization must meet; the weld is NOT yet flipped. #assert_all_clean.
import Dregg2.Deos.SettleEscrowSelectorBinding
-- The welded sealed-escrow satisfaction descriptor GRADUATED to a WIDE (8-felt, ~124-bit) member
-- (§6 BLOCKER 1, sub-gap (1) — the GENTIAN FULCRUM): settleEscrowSatVmDescriptor2R24Wide =
-- wideAppend (graduateV1 (rotateV3 settle-base)) bb (bb+51) + the four satisfaction gates + the
-- selector PI pin. The refinement (settleEscrowWide_forces_settle_gate) + partial/phantom UNSAT teeth
-- carry the V3 proof verbatim over the wide form; the GRADUATION keystone (beforeFieldCol_absorbed /
-- afterFieldCol_absorbed) proves the satisfaction-gate field columns bb+4+k / bb+51+4+k lie INSIDE the
-- 37 pre-iroot limbs the wide carriers absorb into the published 8-felt commit, so a PURE light client
-- binding the wide commit now binds those columns (closing the "1-felt V3, columns not absorbed" gap
-- at the proof level). STAGED — no producer, no committed VK, no live routing, no flip. The remaining
-- flip distance: the wide producer + STARK prove, the in-AIR B_AUTHORITY_DIGEST→selector forcing
-- (§6 item 2, the terminal blocker), and live-path admission. #assert_all_clean.
import Dregg2.Deos.SettleEscrowSatWideDescriptor
-- The GENTIAN KEYSTONE — the in-AIR authority-digest→selector forcing gadget (the TERMINAL blocker of
-- the escrow VK flip, §6 item 2). Three degree-≤2 in-AIR gates (recompute-bind, decode-boolean,
-- selector-force) on the WIDE welded descriptor FORCE the capacity selector ON from the COMMITTED
-- authority-digest limb (r23, wide-bound) under the `DeclCommitBinds` collision-resistance floor — so a
-- PURE light client demands the satisfaction weld with NO off-band verifier discipline, discharging
-- `SettleEscrowSelectorBinding.escrow_selector_bound_to_declaration`'s `hverifier` obligation in-AIR.
-- STAGED — a Lean definition; nothing emitted into the deployed VK, nothing routed, no flip. The named
-- remaining: the literal in-AIR `hash_bytes` recompute over the witnessed declaration + the
-- required-tag decode (the VK-affecting byte-sponge / felt-domain-limb work). #assert_all_clean.
import Dregg2.Deos.InAirAuthorityDigestSelector
-- The GENTIAN KEYSTONE with `hrecompute`/`hdecode` DISCHARGED: Option B realized (the felt-domain
-- chip-lookup recompute + the in-AIR is-zero/OR-fold decode), so the selector-forcing holds under
-- ONLY the two CR floors (`ChipTableSound`/`FloorDigestBinds`) — no off-band verifier discipline.
import Dregg2.Deos.InAirAuthorityDigestGadget
-- The GENTIAN floor BINDING DISCHARGED (PATH b): the required-tag floor the selector reads is decoded
-- from the already-coverage-bound caveat-manifest type-tag columns, so the last `hcommitLimb` is
-- DISCHARGED — the floor is PROVABLY the cell's real declared floor (via the EXISTING `caveatCommit`
-- carrier, NO new binding VK, NO recompute lookup, NO `FloorDigestBinds`), not a forgeable free limb.
-- The forged-floor dodge is closed at the binding (`gentian_forged_floor_unsat_carrier`); only the
-- in-AIR decode + selector-force arithmetic gates remain a (small, staged) VK delta.
import Dregg2.Deos.CarrierBoundFloorGadget
-- The HATCHERY abstraction-mint house-capacity, GROUNDED (the LAST of the six — the house COMPLETE):
-- a user-defined verified KIND's declared invariant IS enforced, forever, and its attestation is REAL.
-- Enforcement is the SAME `CellProgram::evaluate_with_meta` gate (`evalStep`), a violating turn →
-- ConstraintViolated; the "holds forever" crown is the REUSE of the Hatchery's `Verify.Contract.
-- CellContract` carry skeleton (Inv + step_ob ⟹ forever). THE KEY BINDING: `HpresProof::Attested` ⟺ a
-- machine-checked `CellContract` — the `Attested` structure cannot be built without a real contract
-- (hence a real step_ob), so an attestation is a PROVED forever-crown (attested_enforces_forever), not
-- a trusted flag; binds_pending_is_false + forged_attestation_rejected are the negative teeth.
-- Forge-detector: program_missing_invariant_rejected (ProgramMissingInvariant). The Rust
-- sdk/src/hatchery_mint.rs is wired via invariant_matches_lean_rung. #assert_all_clean.
import Dregg2.Deos.Hatchery
import Dregg2.Deos.Rehydration
import Dregg2.Deos.Affordance
-- The COMPOSITION / RERENDER / VISIBILITY widening (2026-06-14): the desktop's UI-composition
-- theorems — phrased to be MORE assured than the Cross-Domain Desktop Compositor (CDDC) ever was
-- (which trusted its compositor TCB for cross-domain isolation and shipped no machine-checked
-- non-interference). These three lanes make that proof.
import Dregg2.Deos.FogOfWar     -- per-viewer visibility NON-INTERFERENCE (the CDDC-beating headline)
import Dregg2.Deos.Compositor   -- the compositing ALGEBRA: damage is exact, paint is order-free
import Dregg2.Deos.Rerender     -- re-rendering a component is FUNCTORIAL (the rerender square)
-- The CAP ∧ STATE conjunction (2026-06-14, the language uplift): the deos affordance gate was CAP-ONLY
-- (fireGate: required⊆held) and the cell-program gate STATE-ONLY (RecordProgram.admitsCtx) — they never
-- composed. A GatedAffordance pairs the REAL cap-gate with the REAL state-gate and fireGated commits IFF
-- BOTH bite (fireGated_iff); the four cross-polarity teeth prove neither alone suffices (caps-OK-but-
-- stale and ready-but-unheld both refuse), the htmx tooth (fireGated_reactive) proves the SAME viewer's
-- button reacts to STATE, and projectGatedFor lifts the membrane-negotiated frustum to STATE-awareness.
import Dregg2.Deos.GatedAffordance
-- The TEMPORAL/REACTIVE rung (2026-06-14, the language uplift): beyond GatedAffordance's single-state
-- gate — TransitionGate (the `link` reads BOTH old+new, so a property of `new` alone can never witness
-- it), deadline/window gates (past `close` an authorized transition auto-refuses), and
-- membrane-as-predicate — two viewers at EQUAL cap-authority but different witness-graph permits project
-- DISTINCT surfaces (`membrane_two_viewers_distinct`: the per-viewer frustum divides by projection, not
-- just caps). 16 keystones #assert_all_clean.
import Dregg2.Deos.Reactive
-- The THREE OPEN CONTINENTS sharpened (2026-06-14, `desktop-os-research/FRUSTUM-REPLAY-MEMBRANE.md`):
-- advances the crown past its three named-but-waved residuals. C1 — the replay DERIVATION: replay
-- DETERMINISM (the fold is a function of the witnessed trace) is DISTINCT from the crown's tamper-
-- evidence payoff and needs NO §8 oracle — it is FORCED by `confined` (every step reads only the
-- witness; `confined_replay_deterministic` + `replay_extensional_in_witness`; `.ambient` is the typed
-- floor, `ambient_trace_unconfined`). C2 — the membrane-NEGOTIATION semantics ("the unspecified
-- continent"): the negotiated projection IS the meet `held ⊓ ask` (= `attenuate`), and the two
-- compositional FAILURE MODES are theorems — the confused-deputy (`deputy_confers_no_unheld_target`:
-- `attenuate` preserves the target, so a requester cannot retarget G's cap) and attenuation-drift
-- (`drift_cannot_recover_dropped_authority`: path-independence on top of `reshareN_attenuates`'s value
-- bound). C3 — the dregg4 forward: the single-machine n=1 atomicity collapse
-- (`single_machine_commit_needs_no_binding` = `family_atomicity` at `ι := Unit` — commit ⇔ the one
-- cell's success, NO CG-5 binding; the cross-cell cut is the price of n≥2). 8 keystones #assert_all_clean.
import Dregg2.Deos.ReplayMembrane
-- The CHOREOGRAPHY COHERENCE (2026-06-14, the "composable flows?" question answered): the deos surface
-- does NOT fork the existing Protocol/Workflow + choreography stack — it RENDERS it. A Protocol.Workflow
-- step IS a sequenced GatedAffordance/Reactive fire: workflowStep_is_gatedAffordance (a step's
-- (authorizedParty, precond) IS a cap∧state button), workflow_fires_iff_affordance_fires (exec ↔
-- gated-fire ∧ attest), phaseTransition_is_reactiveAffordance (a precond→postPhase IS the transition
-- gate); the order/skip/cap teeth carry through. 10 keystones #assert_all_clean.
import Dregg2.Deos.WorkflowBridge
-- The FLOW-COMPOSITION ALGEBRA is RIGHT-SKEWED (2026-06-14, the "does choice distribute over
-- composition?" question answered with a Lean proof): dregg's workflow/affordance-flow algebra satisfies
-- only the HALF `(P⋆R)⊔(Q⋆R) ≤ (P⊔Q)⋆R` (flow_choice_halfdistrib) — the converse FAILS
-- (flow_choice_right_skewed, the headline), so it is a right-skewed Kleene algebra with distributive
-- meets (RSKA_d⊓, à la Pradic's Weihrauch lattice). The separation is NOT in the trace language (both
-- sides denote the same set — flow_choice_languages_equal, the dregg Example 1.1); it lives in the
-- ONLINE step-by-step simulation order (≤ᶠ), the algebraic shadow of the reactive rung: in (P⊔Q)⋆R the
-- choice reads R's OUTPUT (the TransitionGate's old+new read), which the early-branch side cannot
-- anticipate with no lookahead. The distributive meet is real (flow_meet_semilattice). PAYOFF (the
-- PRECONDITION, here): right-skew ⟹ "does flow/caveat-policy A refine B" is DECIDABLE via Pradic's
-- Büchi-game characterization — built in Dregg2.Deos.FlowRefine below. 18 keystones #assert_all_clean.
import Dregg2.Deos.FlowAlgebra
-- The FLOW-REFINEMENT DECISION PROCEDURE (2026-06-14, the right-skew PAYOFF made CONSTRUCTIVE): "does flow
-- / caveat-policy A refine B?" (A ≤ᶠ B) is DECIDABLE. The dregg analogue of Pradic's Theorem 1.4 — the
-- ONLINE simulation order ≤ᶠ is characterized by a finite σ-free SIMULATION GAME (DupSim, Duplicator-win =
-- a PStep-simulation; the Büchi acceptance collapses because the iteration-free fragment makes procSize
-- strictly decrease, pstep_decreases) and decided by a kernel-reducible fuel-bounded greatest-simulation
-- check (decideRefines : Proc → Proc → Bool, decideRefines_iff: = true ↔ A ≤ᶠ B, SOUND+COMPLETE). The
-- σ-UNIFORMITY linchpin (step_to_pstep/pstep_to_step: no Step rule's letter/successor is gated by the
-- threaded state) collapses ≤ᶠ's ∀σ to ONE game, yielding the full Decidable (A ≤ᶠ B) instance
-- (instDecidableSim) — the ARGUS "refines" bar is a DECISION, not a hope. The procedure RECOMPUTES the
-- right-skew on FlowAlgebra's own counterexample, both polarities (decideRefines earlyEx lateEx = true,
-- decideRefines lateEx earlyEx = false — #guard, kernel-evaluated, agreeing with flow_choice_halfdistrib /
-- flow_choice_right_skewed). 18 keystones #assert_all_clean.
import Dregg2.Deos.FlowRefine
-- TRANSCLUSION (2026-06-14, "Xanadu that shipped"): Ted Nelson's transclusion — include-by-reference
-- with preserved provenance + unbreakable links + per-viewer confinement — made HONEST. A transclusion
-- IS a verified cross-cell observation: `Transclusion := Authority.ImportBinding.ImportedEq`, a peer
-- cell's finalized field cited at an immutable receipt. The four Xanadu properties, each a REUSE of an
-- existing kernel theorem: transclusion_is_observed_finalized_read (the bridge = ImportedEq.admits_iff),
-- transclusion_provenance_faithful (the quote equals its source, a forge cannot be cited =
-- importedEq_binds_provenanced_value + importedEq_lying_import_rejected), transclusion_no_amplify (a
-- quote is a READ, per-viewer through the membrane = Membrane.reshareN_attenuates), and the crown
-- transclusion_stable_under_source_advance (THE UNBREAKABLE LINK — the quote never rots =
-- importedEq_stable_under_source_advance, the I-confluence). 10 keystones #assert_all_clean.
import Dregg2.Deos.Transclusion
-- TRANSCLUSION COMPOSES TRANSITIVELY (2026-06-14, the deep Xanadu intertwingularity): a quote of a
-- quote of a quote stays provenance-faithful and unbreakable END-TO-END. Two `Transclusion` legs welded
-- at one field (`ChainLink`: A quotes the very field B used for its quote of C). Three intertwingularity
-- properties, each a COMPOSITION of landed single-transclusion facts: transclusion_chain_provenance_
-- faithful (a quote-of-a-quote resolves to the ORIGINAL author's committed bytes through B = transclusion_
-- provenance_faithful ∘ the weld ∘ bc-validity; the forged-middle tooth refuses a lying intermediary), the
-- keystone transclusion_chain_stable (THE TRANSITIVE UNBREAKABLE LINK — the chain never rots when ANY
-- source advances, inner/middle/both = importedEq_stable_under_source_advance composed across both legs),
-- and transclusion_chain_no_amplify (an N-hop quote chain confers ⊆ the FIRST holder = Membrane.reshareN_
-- attenuates lifted). Non-vacuity: a concrete THREE-CELL chain resolves to C's `7` through B and survives
-- both sources advancing; a forged middle (B claiming C's title was `99`) is refused. 12 keystones
-- #assert_all_clean.
import Dregg2.Deos.TransclusionChain
-- SURFACE GATE ≡ EXECUTOR GATE (the "a darkened affordance can't be bypassed" guarantee): the deos surface
-- state-gate `GatedAffordance.fireGated` and the EXECUTOR's installed-program gate `Argus.Policy.policyGuarded`
-- — two gates over the SAME installed `RecordProgram`, each proven on its own side — provably DECIDE THE SAME
-- TRANSITIONS (installedProgram_gate_eq_surface_stateGate, via executorGate_eq_all_eval / surfaceStateGate_eq_
-- all_eval both collapsing to ∀-constraint-eval). So firing a turn straight at the executor cannot bypass a
-- darkened button: bypass_refused_by_executor, surface_dark_iff_executor_refuses (both polarities), gated_
-- surface_and_executor_both_dark, and the workflow lift workflow_out_of_phase_bypass_refused; agreement_
-- nonvacuous + gates_agree_pointwise exhibit a concrete `memberOf "role"` program where surface-lights ⟺
-- executor-admits and a wrong role darkens BOTH. 10 keystones #assert_all_clean.
import Dregg2.Deos.FireProgramAgreement
-- THE DOCUMENT MERGE IS THE LEAST-UPPER-BOUND JOIN (the colimit-by-union the Pijul pushout computes), and
-- a conflict is a FIRST-CLASS STATE (the dreggverse document language, `docs/deos/DOCUMENT-LANGUAGE.md`
-- §2.1-2.4 + §4.4 RESEARCH; differential = `dregg-doc/src/{merge,graph,content,atom}.rs`). A document is a
-- Pijul graph-of-atoms (`DocGraph` = a KEYED atom map `AtomId → Option AtomVal` (the BTreeMap, ≤1 status
-- per id) + order-edge Finset + field Finset); `merge` is componentwise — atoms join POINTWISE by the
-- Dead-wins `Status.join` (the REAL `graph.rs::union_in_place`, not a struct-union), order/fields union.
-- THE JOIN LAWS, about the real status-joining merge: merge_comm, merge_assoc, merge_idem, merge_total
-- (always-defined), and merge_status_dead_wins (the status-join GENUINELY exercised — alive⊔dead = dead at
-- a shared id; the proof the old Finset-Atom model could not even STATE). THE UNIVERSAL PROPERTY, stated
-- HONESTLY as the LATTICE JOIN / LEAST UPPER BOUND in the document inclusion order ⊑ (NOT "the categorical
-- pushout up to unique iso" — that residual, the category P / the span a←a⊓b→b / functoriality, is NAMED,
-- not claimed): merge_is_lub (merge a b is the LEAST graph including both legs; merge_includes_left/right
-- are the cocone legs, merge_least is leastness). CONFLICT-AS-STATE uses TRANSITIVE reachability
-- (Reaches = Relation.ReflTransGen of the edge relation, matching content.rs::reachable — NOT a one-hop
-- shadow): ConflictAt is two distinct live atoms after a shared p that are MUTUALLY non-reachable
-- (a transitive antichain). merge_has_conflict exhibits a concrete two-fork conflict that is a WELL-FORMED
-- merged DocGraph (not a failure); resolve_collapses — adding an order-edge (an additive Connect patch)
-- makes one reach the other (the antichain collapses) and is additive (g ⊑ resolved). THE TWO-REGIME SPLIT
-- (§2.4) connected to Confluence.IConfluent: prose_iconfluent (grow-only liveness survives merge — benign)
-- vs field_not_iconfluent (a single-valued field clashes — the non-monotone boundary, a clashing pair
-- CONSTRUCTED whose merge holds two values at one name). 18 keystones #assert_axioms-clean; 12 #guard teeth.
import Dregg2.Deos.DocMerge

namespace Dregg2.Deos

/-! ## The verified-deos namespace assembles the four core legs + three composition lanes. Each
sub-module pins its own keystones kernel-clean (`#assert_all_clean`); this umbrella re-exports them as
the single `Dregg2.Deos` surface.

The four core targets, as one sentence: a deos surface is a kernel cap (leg 1) whose per-viewer
projection and membrane reshares cannot amplify (legs 1+2), whose affordances fire only under the
`is_attenuation` gate and bind the attested root (leg 4), and whose rehydration liveness-type IS exactly
the confined fragment (leg 3, the crown).

The three composition lanes lift the desktop from "every primitive is a kernel theorem" to "every UI
COMPOSITION is a kernel theorem" — the things a windowing system's correctness actually rests on, and
the things the CDDC *trusted its TCB to provide*:

  5. **Per-viewer visibility non-interference** (`Dregg2.Deos.FogOfWar`) — THE CDDC-BEATING HEADLINE.
     A low viewer's render is a FUNCTION of the low-authorized state ALONE: changing a hidden cell leaves
     the view bit-identical (`noninterference` + `hidden_change_invisible`), a hidden cell is structurally
     ABSENT (`hiddenCell_absent`), two viewers diverge by exactly their authority (`divergence`), and
     vision is monotone in capability (`vision_monotone`). The cross-domain non-interference the CDDC
     trusted its compositor process to provide — here a machine-checked theorem about the projection.
     This is the information-flow sibling of leg-3's confinement crown: "what you see" is determined by
     exactly the fragment inside your capability, the same shape as "what replays".

  6. **The compositing algebra** (`Dregg2.Deos.Compositor`) — built on `Apps.Compositor`'s verified
     scene-graph. Damage is EXACT (`present_damage_exact` + `unchanged_outside_target`: a present dirties
     exactly its declared regions, the dirty-region tracking is sound), paint is ORDER-FREE on a
     well-formed scene (`paint_order_independent`: T1's disjointness makes z-order irrelevant to the
     pixels, so the glass is well-defined independent of paint order), ownership is unambiguous
     (`ownerAt_unique`), the frame property holds (`render_frame_property`: editing one window cannot
     perturb another's pixels — the compositional dual of non-interference), and the scene-graph is
     closed under disjoint composition (`compose_preserves_wellFormed` + `compose_assoc`).

  7. **Rerender functoriality** (`Dregg2.Deos.Rerender`) — re-rendering is a FUNCTOR over `projectFor`.
     The rerender SQUARE commutes (`rerender_square`: re-rendering after a state update equals updating
     the rendered surface — `project ∘ step = step ∘ project`, the central web-framework guarantee),
     it is deterministic + idempotent (`rerender_idempotent`), buttons are stable across content updates
     (`rerender_after_step_authorized`), and the frustum-snapshot re-expands faithfully + per-viewer
     (`snapshot_roundtrip` + `snapshot_roundtrip_attenuated`: a snapshot is a lossless, per-viewer handle
     to the surface, not a lossy thumbnail).

"A verified desktop OS": every visual/interactive primitive AND every UI composition reduces to a kernel
theorem — and the cross-domain isolation the CDDC trusted is, here, proven. -/

end Dregg2.Deos
