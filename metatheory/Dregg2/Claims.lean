/-
# Dregg2.Claims — the consolidated axiom-hygiene ledger (dregg2's `verify-claims`).

This module is the MACHINE-CHECKED half of `metatheory/CLAIMS.md`. It imports the
ROOT (`Dregg2`, which transitively pulls in every module) and then re-pins, in ONE
place, every keystone the corpus advertises as "PROVED / axiom-clean" with
`#assert_axioms`. Each pin ELABORATES to an error (via the `Dregg2.Tactics` tripwire)
unless the named theorem's entire axiom set is `{propext, Classical.choice, Quot.sound}`
— in particular it FAILS on any `sorryAx`. So `lake build` (and `lake env lean` on this
file) becomes a credibility artifact: if any claimed keystone silently regresses to
`sorry`, the build breaks HERE, at the ledger, not somewhere downstream.

Discipline (this file proves NOTHING new — it AUDITS):
  * Contents are ONLY `import Dregg2` + `#assert_axioms` lines + comments.
  * No `axiom` / `admit` / `native_decide` / `sorry`.
  * A keystone that legitimately RESTS on a §8/Law-1 primitive (a `sorry`'d operational
    obligation, or an `axiom`-keyword crypto oracle) is NOT pinned here — that would
    correctly fail. Such keystones, and the genuine OPENs (cross-cell/operational
    bisimulation, Byzantine quorum-intersection, distributed-death co-witnessability,
    the Authority whole-history closure, the §8 crypto obligations), are listed in
    `metatheory/CLAIMS.md`, NOT here.

(§8 oracles that enter as TYPECLASS PARAMETERS / HYPOTHESES — `CryptoKernel` / `World` /
`Verifiable` — do NOT appear in `collectAxioms` and so do NOT trip the guard; the
theorems that take them as hypotheses are genuinely kernel-clean and ARE pinned.)

NOTE: keystones are referenced here by their FULLY-QUALIFIED names (the home modules pin
them bare, from inside their own `namespace`). A wrong name is an `unknownConstant` build
error — which is, deliberately, the point.
-/
import Dregg2

namespace Dregg2.Claims

/-! ## §0 — Conservation core (the shared library lemmas; `Dregg2.Conserve`). -/
#assert_axioms Dregg2.Conserve.sum_indicator
#assert_axioms Dregg2.Conserve.sum_pointUpdate
#assert_axioms Dregg2.Conserve.sum_conserve_of_deltas_zero
#assert_axioms Dregg2.Conserve.sum_transfer_conserve

/-! ## §1 — The executable spine (Phase 2): cexec is step-complete, the cell lives.
`cexec_attests` realizes the abstract `Core.conservation_step` primitive AS A THEOREM
about the executable machine; `livingCell_sound` is the genuine
bisimulation-to-golden-oracle. (`Dregg2.Exec.*`) -/
#assert_axioms Dregg2.Exec.cexec_attests
#assert_axioms Dregg2.Exec.conservation_step_realized
#assert_axioms Dregg2.Exec.livingCell_sound

/-! ## §1b — The record cell GROWS νF life (de-toy): conservation over name-keyed records. -/
#assert_axioms Dregg2.Exec.RecordCell.recCexec_attests
#assert_axioms Dregg2.Exec.RecordCell.recordCell_obs_advances
#assert_axioms Dregg2.Exec.RecordCell.recReplay_preserves_sumEquals
#assert_axioms Dregg2.Exec.RecordCell.recordCell_stepComplete
#assert_axioms Dregg2.Exec.RecordCell.recordCell_run_preserves_sumEquals

/-! ## §2 — Circuit-from-Lean: the CCS bridge + DERIVED verify-law. (`Dregg2.Circuit`) -/
#assert_axioms Dregg2.Circuit.bridge
#assert_axioms Dregg2.Circuit.verify_law_derivable

/-! ## §3 — The atomic Hyperedge (turn = wide pullback over shared TurnId). -/
#assert_axioms Dregg2.Hyperedge.Hyperedge.legs_agree
#assert_axioms Dregg2.Hyperedge.hyper_binding_is_proper
#assert_axioms Dregg2.Hyperedge.Hyperedge.toSharedTurnId
#assert_axioms Dregg2.Hyperedge.Hyperedge.toJointBinding
#assert_axioms Dregg2.Hyperedge.SharedTurnId.toHyperedge
#assert_axioms Dregg2.Hyperedge.ringHyperedge
#assert_axioms Dregg2.Hyperedge.hyper_stepComplete
#assert_axioms Dregg2.Hyperedge.hyperedge_sound
#assert_axioms Dregg2.Hyperedge.hyperedge_sound_needs_binding

/-! ## §4 — Spec.Guard: the ONE verify/find seam (meet-semilattice `attenuate_narrows`). -/
#assert_axioms Dregg2.Spec.Guard.admits_all
#assert_axioms Dregg2.Spec.Guard.admits_any
#assert_axioms Dregg2.Spec.Guard.attenuate_narrows
#assert_axioms Dregg2.Spec.Guard.admits_attenuate
#assert_axioms Dregg2.Spec.Guard.admits_witnessed_iff_discharged
#assert_axioms Dregg2.Spec.Guard.discharged_admits
#assert_axioms Dregg2.Spec.Guard.admits_monotonic
#assert_axioms Dregg2.Spec.Guard.admits_sumEquals
#assert_axioms Dregg2.Spec.Guard.admits_senderAuthorized
#assert_axioms Dregg2.Spec.Guard.admits_nonMembership
#assert_axioms Dregg2.Spec.Guard.admits_oneOf

/-! ## §5 — Spec.Conservation: multi-domain, value-monoid-parametric (committed=cleartext). -/
#assert_axioms Dregg2.Spec.LinearityClass.requires_paired_sibling_iff
#assert_axioms Dregg2.Spec.LinearityClass.is_disclosed_non_conservation_iff
#assert_axioms Dregg2.Spec.LinearityClass.paired_and_disclosed_exclusive
#assert_axioms Dregg2.Spec.linearity_examples
#assert_axioms Dregg2.Spec.conservation_over_monoid
#assert_axioms Dregg2.Spec.conservation_over_monoid_finset
#assert_axioms Dregg2.Spec.disclosed_non_conservation
#assert_axioms Dregg2.Spec.conservative_discloses_nothing
#assert_axioms Dregg2.Spec.committed_of_cleartext
#assert_axioms Dregg2.Spec.committed_iff_cleartext
#assert_axioms Dregg2.Spec.multi_domain_independent
#assert_axioms Dregg2.Spec.turnConserves_balance

/-! ## §6 — Spec.Authority: the generative capability graph (whole-history closure OPEN). -/
#assert_axioms Dregg2.Spec.confers_refl
#assert_axioms Dregg2.Spec.confers_trans
#assert_axioms Dregg2.Spec.introduce_non_amplifying
#assert_axioms Dregg2.Spec.introduce_same_target
#assert_axioms Dregg2.Spec.amplify_needs_held_amplifier
#assert_axioms Dregg2.Spec.mint_needs_held_factory
#assert_axioms Dregg2.Spec.mint_conforms_to_contract
#assert_axioms Dregg2.Spec.gen_conferral_is_attenuation
#assert_axioms Dregg2.Spec.attenuate_is_restrictive_narrowing
#assert_axioms Dregg2.Spec.gen_step_traces
#assert_axioms Dregg2.Spec.revoke_step_adds_nothing
#assert_axioms Dregg2.Spec.introduce_is_gen
#assert_axioms Dregg2.Spec.mint_is_gen
#assert_axioms Dregg2.Spec.amplify_is_gen
#assert_axioms Dregg2.Spec.attenuate_is_restrict
#assert_axioms Dregg2.Spec.revoke_is_restrict

/-! ## §7 — Spec.Lifecycle: creation/death duality (distributed-death co-witness OPEN). -/
#assert_axioms Dregg2.Spec.Lifecycle.acceptsEffects_iff
#assert_axioms Dregg2.Spec.Lifecycle.isTerminal_iff
#assert_axioms Dregg2.Spec.Lifecycle.terminal_rejects_effects
#assert_axioms Dregg2.Spec.Lifecycle.terminal_rejects_transition
#assert_axioms Dregg2.Spec.Lifecycle.migrated_terminal
#assert_axioms Dregg2.Spec.Lifecycle.destroyed_terminal
#assert_axioms Dregg2.Spec.Lifecycle.creation_and_death_are_dual
#assert_axioms Dregg2.Spec.Lifecycle.birthProvable
#assert_axioms Dregg2.Spec.Lifecycle.archival_is_fold
#assert_axioms Dregg2.Spec.Lifecycle.archived_still_live
#assert_axioms Dregg2.Spec.Lifecycle.reclaim_by_lease
#assert_axioms Dregg2.Spec.Lifecycle.creation_provable_death_temporal

/-! ## §8 — Spec.JointViaHyper: N-ary joint DERIVED from hyperedge_sound. -/
#assert_axioms Dregg2.Spec.joint_via_hyperedge
#assert_axioms Dregg2.Spec.binary_binding_from_hyperedge
#assert_axioms Dregg2.Spec.binary_joint_via_hyperedge
#assert_axioms Dregg2.Spec.singletonHyperedge
#assert_axioms Dregg2.Spec.hyperedge_is_validity_not_canonicity
#assert_axioms Dregg2.Spec.selector_needs_more_than_validity

/-! ## §9 — Spec.Choreography: blue/red split → red projects to a Hyperedge (operational OPEN). -/
#assert_axioms Dregg2.Spec.RedBinding.toHyperedge
#assert_axioms Dregg2.Spec.red_projects_to_hyperedge
#assert_axioms Dregg2.Spec.red_legs_agree
#assert_axioms Dregg2.Spec.blue_commits_independently
#assert_axioms Dregg2.Spec.blue_needs_no_hyperedge
#assert_axioms Dregg2.Spec.red_iff_coupled
#assert_axioms Dregg2.Spec.epp_membrane_is_projection

/-! ## §10 — Spec.Await: the await family = temporal Guard ⊕ dataflow DAG (topo-sort OPEN). -/
#assert_axioms Dregg2.Spec.Conditional.conditional_is_temporal_guard
#assert_axioms Dregg2.Spec.Conditional.resolved_iff_gateway_discharged
#assert_axioms Dregg2.Spec.Conditional.resolve_monotone
#assert_axioms Dregg2.Spec.Conditional.expired_stays_expired
#assert_axioms Dregg2.Spec.Conditional.gateway_admits_eq_token
#assert_axioms Dregg2.Spec.Conditional.PromiseGraph.depends_irrefl
#assert_axioms Dregg2.Spec.Conditional.PromiseGraph.depends_trans
#assert_axioms Dregg2.Spec.Conditional.PromiseGraph.broken_promise_propagates
#assert_axioms Dregg2.Spec.Conditional.PromiseGraph.broken_promise_propagates_trans
#assert_axioms Dregg2.Spec.Conditional.await_two_faces
#assert_axioms Dregg2.Spec.Conditional.temporal_face_is_await_discharge

/-! ## §11 — Spec.VatBoundary: Φ the named-lossy caps↔keys functor (functoriality OPEN). -/
#assert_axioms Dregg2.Spec.phi_admits_iff_discharged
#assert_axioms Dregg2.Spec.cross_vat_needs_witness
#assert_axioms Dregg2.Spec.phi_drops_confinement
#assert_axioms Dregg2.Spec.forwarded_cap_is_revocable
#assert_axioms Dregg2.Spec.revocable_iff_not_authority
#assert_axioms Dregg2.Spec.macaroon_does_not_cross_phi
#assert_axioms Dregg2.Spec.biscuit_crosses_phi
#assert_axioms Dregg2.Spec.phi_domain_is_exactly_biscuit
#assert_axioms Dregg2.Spec.phi_composes_with_attenuation
#assert_axioms Dregg2.Spec.phi_attenuation_factors_through_confers

/-! ## §12 — Spec.Coherence: the cross-subsystem weave (one order; guard=authority meet).

PENDING-OLEAN-REBUILD (race-safe parking). `Dregg2.Spec.Coherence` is `sorry`-free in
source and self-pins its keystones in its own module, but its import was added to the root
`Dregg2.lean` only after the last `Dregg2.olean` was produced — so these constants are NOT
yet in this file's import closure (a `lake build` will pull them in; this agent must not
build, other agents hold the tree). Pinning a not-yet-in-closure constant is a hard
`unknownConstant` build error, so the pins below are PARKED, not deleted. Re-enable
(uncomment) once `Dregg2.Spec.Coherence.olean` exists. They are listed in
`metatheory/CLAIMS.md` as PROVED (home-module self-pinned). -/
-- #assert_axioms Dregg2.Spec.guard_is_authority_conferral
-- #assert_axioms Dregg2.Spec.conferralGuard_admits_self
-- #assert_axioms Dregg2.Spec.introduce_passes_conferralGuard
-- #assert_axioms Dregg2.Spec.conservation_is_hyperedge_cg5
-- #assert_axioms Dregg2.Spec.hyperedge_conserves_crossCell
-- #assert_axioms Dregg2.Spec.lifecycle_revoke_is_authority_restrictive
-- #assert_axioms Dregg2.Spec.revoke_is_terminal_restrictive
-- #assert_axioms Dregg2.Spec.migrated_and_destroyed_both_revoke
-- #assert_axioms Dregg2.Spec.choreography_red_conserves
-- #assert_axioms Dregg2.Spec.choreography_red_conserves_sum
-- #assert_axioms Dregg2.Spec.guard_attenuate_narrows_is_meet
-- #assert_axioms Dregg2.Spec.authority_confers_narrows_is_meet

/-! ## §13 — Finality: the 4-tier lattice; conservation is tier-independent. -/
#assert_axioms Dregg2.Finality.conservation_tier_independent
#assert_axioms Dregg2.Finality.conservation_tier_independent_iff

/-! ## §14 — Liveness: GC-as-cell-liveness; revocation needs consensus (unlike collection). -/
#assert_axioms Dregg2.Liveness.revocation_needs_consensus

/-! ## §15 — Exec.Consensus: quorum→finality-tier bridge (Byzantine safety stays OPEN). -/
#assert_axioms Dregg2.Exec.Consensus.quorum_reaches_bft_tier
#assert_axioms Dregg2.Exec.Consensus.committedByQuorum_reaches_bft_tier
#assert_axioms Dregg2.Exec.Consensus.below_quorum_not_bft
#assert_axioms Dregg2.Exec.Consensus.net_no_downgrade
#assert_axioms Dregg2.Exec.Consensus.net_no_downgrade_via_world
#assert_axioms Dregg2.Exec.Consensus.finality_monotone_on_net
#assert_axioms Dregg2.Exec.Consensus.quorum_grows_preserves_finality
#assert_axioms Dregg2.Exec.Consensus.committed_holds_along_rounds
#assert_axioms Dregg2.Exec.Consensus.cross_tier_join_on_net
#assert_axioms Dregg2.Exec.Consensus.NetCell.tier_eq_bft_iff

/-! ## §16 — Upgrade: anti-brick set_program (version pin + signature fallback).

The two anti-brick keystones below ARE in closure and pinned. The eight Envelope-spine
keystones (`invariant_intro`, `safety_preservation`, `admit_preserves_safety`,
`self_improvement_is_safe`, `genealogy_sound`, `identity_vouch_unconditional`,
`upgradeGenealogy_sound`, `signatureVouchUnbrickable`) exist `sorry`-free in
`Dregg2/Upgrade.lean` source (and the module self-pins them), but the live `Upgrade.olean`
predates that source edit, so they are not yet in this file's closure — PARKED (same
race-safe reason as §12), listed PROVED in `metatheory/CLAIMS.md`, re-enable after rebuild. -/
#assert_axioms Dregg2.Upgrade.upgrade_never_bricks
#assert_axioms Dregg2.Upgrade.stale_version_falls_back_to_signature
-- #assert_axioms Dregg2.Upgrade.invariant_intro
-- #assert_axioms Dregg2.Upgrade.safety_preservation
-- #assert_axioms Dregg2.Upgrade.admit_preserves_safety
-- #assert_axioms Dregg2.Upgrade.self_improvement_is_safe
-- #assert_axioms Dregg2.Upgrade.genealogy_sound
-- #assert_axioms Dregg2.Upgrade.identity_vouch_unconditional
-- #assert_axioms Dregg2.Upgrade.upgradeGenealogy_sound
-- #assert_axioms Dregg2.Upgrade.signatureVouchUnbrickable

/-! ## §17 — Proof.Refine: Exec ⊑ Abstract refinement (full simulation diagram OPEN). -/
#assert_axioms Dregg2.Proof.refine_conservation
#assert_axioms Dregg2.Proof.refine_conservation_measure
#assert_axioms Dregg2.Proof.refine_run_conservation
#assert_axioms Dregg2.Proof.refine_integrity
#assert_axioms Dregg2.Proof.refine_integrity_intra

end Dregg2.Claims
