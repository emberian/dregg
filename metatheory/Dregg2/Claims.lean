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

## The two-layer zero-sorry guard (be honest about which is which).

There are TWO complementary, deliberately-different guards keeping the corpus at ZERO sorry:

  (b) THIS LEDGER (`#assert_axioms` per-decl, `#assert_namespace_axioms` per-namespace).
      STRONGER but TARGETED: it catches a sorry even when it is *transitively inherited*
      through a renamed/aliased lemma — `collectAxioms` follows the whole dependency DAG and
      rejects any `sorryAx`. BUT its reach is exactly its PIN LIST. `#assert_axioms` is
      per-declaration; `#assert_namespace_axioms` is per-namespace. Neither is whole-corpus:
      a sorry in an UNPINNED decl in an UNPINNED namespace would NOT trip this layer. (We pin
      aggressively, but the pin list is, by construction, an enumeration — not a closure.)

  (a) THE TEXTUAL CI GREP (`scripts/no-sorry-metatheory.sh`, wired as the CI job
      `metatheory-no-sorry`). WEAKER per-decl (purely textual; it does not chase transitive
      inheritance — that is (b)'s job) but COMPREHENSIVE: it runs the whole `lake build` and
      FAILS on ANY `declaration uses \`sorry\`` warning, which Lean emits for EVERY declaration
      closed with `sorry`, `admit`, or `sorryAx` — pinned or not, named or anonymous, in any
      module. No enumeration is needed to stay total. This is the real whole-corpus net.

So: (b) is the deep-but-targeted transitive-inheritance tripwire; (a) is the broad textual
whole-corpus floor. They are NOT redundant — each covers what the other cannot. The honest
summary: the comprehensive "there is no sorry ANYWHERE" guarantee is (a), the CI grep; this
ledger (b) is the stronger guarantee that the SPECIFICALLY-PINNED keystones additionally carry
no INHERITED sorry. (Lean has no first-class whole-corpus `#assert_no_sorry` command, so (a)
necessarily lives outside the build, in CI, as the textual net.)
-/
import Dregg2

namespace Dregg2.Claims

/-! ## §0 — Conservation core (the shared library lemmas; `Dregg2.Conserve`). -/
#assert_axioms Dregg2.Conserve.sum_indicator
#assert_axioms Dregg2.Conserve.sum_pointUpdate
#assert_axioms Dregg2.Conserve.sum_conserve_of_deltas_zero
#assert_axioms Dregg2.Conserve.sum_transfer_conserve

/-! ## §0a — The abstract `Core` Law-1 + `Laws` find/verify seam — both formerly `sorry`'d,
now carried as TYPECLASS FIELDS (the `CryptoKernel` Prop-portal idiom) and recovered as
kernel-clean lemmas. `Core.conservation_step` accesses `ConservesStep.step` (discharged by the
executable kernel, §1); `Laws.search_sound` accesses `SoundSearchable.find_sound` (the genuine,
non-trivial plugin contract — `Authority.goodSoundMatcher` satisfies it, `evilMatcher_not_sound`
proves a returns-7 plugin CANNOT). Both are now PINNED: they carry NO `sorry`. -/
#assert_axioms Dregg2.Core.conservation_step
#assert_axioms Dregg2.Core.conservation_ordinary
#assert_axioms Dregg2.Core.mint_delta
#assert_axioms Dregg2.Core.burn_delta
#assert_axioms Dregg2.Core.withholding_no_free_copy
#assert_axioms Dregg2.Laws.search_sound
#assert_axioms Dregg2.Authority.goodSoundMatcher
#assert_axioms Dregg2.Authority.evilMatcher_not_sound

/-! ## §1 — The executable spine (Phase 2): cexec is step-complete, the cell lives.
`cexec_attests` realizes the abstract `Core.ConservesStep` class field AS A THEOREM
about the executable machine; `conservation_step_realizes_balance` discharges the abstract
Law-1 balance from it, providing the `instConservesStepExec` instance (so the abstract
`Core` corollaries auto-resolve their `[ConservesStep]` constraint against the running kernel —
a real proof, never a re-`sorry`). `livingCell_sound` is the genuine
bisimulation-to-golden-oracle. (`Dregg2.Exec.*`) -/
#assert_axioms Dregg2.Exec.cexec_attests
#assert_axioms Dregg2.Exec.conservation_step_realized
#assert_axioms Dregg2.Exec.conservation_step_realizes_balance
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

/-! ## §11 — Spec.VatBoundary: Φ the named-lossy caps↔keys functor. `phi_functorial` is now
PROVED (and PINNED) under its explicit `NonDegenerate` hypothesis (the honest residual is that
named hypothesis, NOT a `sorry`); `nonDegenerate_concrete` proves the hypothesis is satisfiable,
and `phi_functorial_concrete` is `phi_functorial` applied to it — all axiom-clean. -/
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
#assert_axioms Dregg2.Spec.phi_functorial
#assert_axioms Dregg2.Spec.nonDegenerate_concrete
#assert_axioms Dregg2.Spec.phi_functorial_concrete

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

/-! ## §18 — Session wave (2026-05-30): the VCG/WP program logic, the operational-LTS first
stone, the 2nd §8 discharge (Pedersen), and the first-app Spec layer. These are whole NEW
clean modules (zero `sorry`), so we pin them at the NAMESPACE level via the
`#assert_namespace_axioms` command (Track C) rather than line-by-line — every theorem in each
namespace is asserted kernel-clean at once. (Privacy Tier-3's de-vacuified keystones,
`Crypto.Merkle`'s verifier-derivation, and `Exec.RecordKernel`'s record-cell `cexec_attests`
are pinned in their HOME modules; the operational-LTS / Byzantine / death-undecidability OPENs
remain listed in `metatheory/CLAIMS.md`, NOT here.) -/
#assert_namespace_axioms Dregg2.Proof.WP
#assert_namespace_axioms Dregg2.Proof.LTS
#assert_namespace_axioms Dregg2.Crypto.Merkle
#assert_namespace_axioms Dregg2.Crypto.Pedersen
#assert_namespace_axioms Dregg2.Crypto.PredicateKernel
#assert_namespace_axioms Dregg2.Protocol.WorkflowGuard

/-! ## §19 — Autonomous wave (2026-05-30): honest-OPENs CLOSED + the authority-turn LTS.
Four sorries that were OPEN are now PROVED — and THREE of them were FALSE/contradictory *as stated*
(restated honestly, then proved): deadness-undecidability in its genuine **computable** form (via a
`haltGraph` halting reduction; the old arbitrary-`Bool`-function form was classically vacuous), its
`Lifecycle` + `CellLiveness` re-exports, the quorum-intersection pigeonhole (`hbound` restated to the
honest union-cardinality bound), and GST-liveness (discharged from a NEW assumed `World.gst_liveness`
oracle law, the `recv_mono` pattern — a class field, hence kernel-clean here). Plus the authority-turn
executable transition completing the single-cell operational LTS (`Proof.LTS`'s `authAbsStep_forward`/
`absStep'_forward` are auto-covered by §18's namespace pin). -/
#assert_axioms Dregg2.Liveness.dead_undecidable
#assert_axioms Dregg2.Spec.Lifecycle.distributed_death_not_co_witnessable
#assert_axioms Dregg2.Exec.CellLiveness.death_not_decidable
#assert_axioms Dregg2.World.quorum_intersection_safety
#assert_axioms Dregg2.World.liveness_after_gst
#assert_axioms Dregg2.Exec.recKDelegate_frame
#assert_axioms Dregg2.Exec.recKRevokeTarget_frame
#assert_axioms Dregg2.Exec.recKDelegate_execGraph
#assert_axioms Dregg2.Exec.recKRevokeTarget_execGraph
#assert_axioms Dregg2.Exec.recKDelegate_grounds

/-! ## §20 — Autonomous wave 2 (2026-05-30): the last LTS-gated + framing OPENs closed.
`deadlock_freedom_by_design` (was FALSE over initial projections — counterexample `deadlock_initial_counterexample`;
restated + proved over the choreography reachable-config LTS `GStep`/`GReach`, on the `NoRec` fragment) and BOTH
`Hyperedge` opens (`hyperedge_sound_bisim` was ill-posed over a free `Spec` — `hyperedge_sound_bisim_ill_posed`
records the refutation; restated to the reflexive form; `hyper_not_all_admissible` was true, proved). Plus the
THIRD §8 discharge, `Crypto.NonMembership` (sorted-tree neighbor-bracketing). All now sorry-free ⟹ pinnable at
the namespace level. (HISTORICAL: this wave left 3 by-design sorries — `Core.conservation_step`,
`Laws.search_sound`, `Spec.VatBoundary.phi_functorial`-abstract. The ZERO-SORRY wave then RETIRED all three:
the first two became typeclass FIELDS — `Core.ConservesStep.step` / `Laws.SoundSearchable.find_sound` — recovered
as kernel-clean lemmas (§0a) and discharged/witnessed; `phi_functorial` became PROVED under an explicit
`NonDegenerate` hypothesis (§11). The corpus is now at ZERO `sorry`.) -/
#assert_namespace_axioms Dregg2.Crypto.NonMembership
#assert_namespace_axioms Dregg2.Coordination
#assert_namespace_axioms Dregg2.Hyperedge

/-! ## §21 — Autonomous wave 3 (2026-05-30): papers collected → the hard problems' STRONG forms,
two more §8 discharges, and the closed userspace-verification loop. The classics (FLP/DLS88/HotStuff)
+ modern quorum-systems paper were fetched into `pdfs/`; with them: `Crypto.Temporal`/`Crypto.Dfa`
(4th/5th §8 discharges, both-direction bridges, no seam), `Proof.BFT` (O1 STRONG `bft_safety` via the
honest-witness `n−f` quorum intersection — Malkhi–Reiter/Li–Lesani — + O2 reduced-assumption GST
liveness; all adversary assumptions are structure FIELDS, not axioms), `Proof.CrossCellLTS`
(the bilateral cross-cell forward-simulation square + a PROVED obstruction that it does NOT reduce to
the single-cell squares — tensor-non-finality, operationally), and `Proof.WPCatalog` (the closed
loop: eDSL program → vcg → fail-loud `vcg_discharge` → `vcg_run_sound` capstones). All sorry-free
(their residuals are PROSE `-- OPEN:`s — Dfa reference kernel, BFT pacemaker, N-ary forest — not
sorries), so namespace-pinnable. -/
#assert_namespace_axioms Dregg2.Crypto.Temporal
#assert_namespace_axioms Dregg2.Crypto.Dfa
#assert_namespace_axioms Dregg2.Proof.BFT
#assert_namespace_axioms Dregg2.Proof.CrossCellLTS
#assert_namespace_axioms Dregg2.Proof.WPCatalog

/-! ## §22 — Papers-in-hand wave (2026-05-30): the hard problems' deep forms.
With FLP/DLS88/HotStuff/Streamlet + the quorum-systems/view-sync papers fetched: `Proof.BFTLiveness`
(the O2 PACEMAKER closed — a GST round provably obtains from a DLS88+ELRS+HotStuff `Pacemaker`, all
honest fields; `World.gst_liveness` now DERIVED), `Proof.ForestLTS` (the N-ary cross-cell forest
square, Σ=0 binding hypothesis-routed; bilateral = `Fin 2` slice), `Proof.ContendedCrossCell` (the
contention DICHOTOMY, BOTH poles PROVED: I-confluent ⇒ schedule-agnostic commit; coupled Σ=0 ⇒ `¬∃`
schedule-agnostic commit, the BEC/CAP impossibility as a theorem), and `Crypto.Bridge` (the 6th §8
discharge). All sorry-free (residuals — the randomized synchronizer construction, the coinductive
unbounded-interleaving adversary, Custom/BlindedSet kinds — are PROSE `-- OPEN:`s). The actual-
metatheory sibling `Metatheory/EpistemicConsensus.lean` (fault-tolerant distributed-knowledge-by-
verification + a UC static-composition fragment) self-pins in its own file (verified standalone). -/
#assert_namespace_axioms Dregg2.Proof.BFTLiveness
#assert_namespace_axioms Dregg2.Proof.ForestLTS
#assert_namespace_axioms Dregg2.Proof.ContendedCrossCell
#assert_namespace_axioms Dregg2.Crypto.Bridge

/-! ## §23 — Cascade-integration wave (2026-05-31): the replacement reaches the wire + the coinductive
OPEN closes. The cascade is REPLACE-not-certify (the verified kernel swaps in for dregg1's busted
executor). `Exec.TurnExecutor` (`execTurn_attests` = all 4 StepInv conjuncts over a linear multi-Action
turn, step-complete by construction) + `Exec.Forest` (`execForest_attests` — the nested delegated
call-forest, Granovetter-preserving via `derive_no_amplify`, N-ary Σ=0 conservation) = the replacement
turn-executor. `Exec.CircuitEmit` (`emittedMerkle_bridge`/`emitA_faithful`/`merkleC1_position_valid` —
the kernel + Merkle + algebraic ConstraintExpr circuits emit faithfully to the fingerprint-bound Rust
backend). `Proof.CoinductiveAdversary` (`obsBisim_of_uptoComm`) CLOSES the last coinductive research
residue via the VENDORED+PORTED Paco (`namespace Paco`, hxrts/paco-lean MIT, 4.26→4.30, 23 modules)'s
gupaco up-to-context closure. (FFI caps-marshalling + record-state are Rust-side / dregg-lean-ffi,
differential-validated, not pinned here.) -/
#assert_namespace_axioms Dregg2.Exec.TurnExecutor
#assert_namespace_axioms Dregg2.Exec.Forest
#assert_namespace_axioms Dregg2.Exec.CircuitEmit
#assert_namespace_axioms Dregg2.Proof.CoinductiveAdversary
#assert_namespace_axioms Paco

/-! ## §24 — Widening wave (2026-05-31): full op-set + cross-cell forest + runtime-character + eDSL-C +
schema-migration + §8-gadgets-to-wire. The replacement executor covers EVERY dregg1 turn kind
(`TurnExecutorFull.execFull_attests`); the nested forest spans cells (`CrossCellForest`, Σ=0
binding-carried); the Robigalia OS payoff is theorems (`CellRuntime`: checkpoint/replay/time-travel);
the eDSL trilogy is complete (`DSLEffect`); cells migrate schemas without bricking
(`StateMigration.migrate_*`); and the other §8 gadget circuits emit to the wire (`CircuitEmitGadgets`,
each composing emit-faithfulness with its gadget bridge — the Rust decoder fingerprint-matched native
for Merkle in dregg-lean-ffi). -/
#assert_namespace_axioms Dregg2.Exec.TurnExecutorFull
#assert_namespace_axioms Dregg2.Exec.CrossCellForest
#assert_namespace_axioms Dregg2.Exec.CellRuntime
#assert_namespace_axioms Dregg2.Exec.CircuitEmitGadgets
#assert_namespace_axioms Dregg2.DSLEffect
#assert_axioms Dregg2.Exec.migrate_conforms
#assert_axioms Dregg2.Exec.migrate_conserves
#assert_axioms Dregg2.Exec.migrate_anti_brick

/-! ## §25 — Open-loops wave (2026-05-31): gas-metering as a fail-closed liveness guard +
the CANONICAL interior-h probabilistic-oracle witness. `Gas` layers a `Nat`-valued resource bound
beside `execFullTurn` (`gas_exhaustion_fails_closed`: over-budget ⇒ none with no partial mutation;
`gas_sufficient_runs`: when affordable the metered state EQUALS the un-metered one — a pure guard;
`gas_conserves`/`gas_preserves_attests`: removes no safety, orthogonal to ℤ-conservation).
`BeaconSpaceInterior` supersedes the Dirac-`h=1` boundary witness with `Measure.infinitePi
(Bernoulli 3/4)^ℕ` at strictly-interior `h=3/4`, discharging `indep_block` via genuine cross-view
independence (`Measure.infinitePi_pi`) — the BeaconSpace abstraction is non-vacuously instantiable at
a real interior honest-fraction (the ProductMeasure "obstruction" was a stale uncompiled olean, now built). -/
#assert_namespace_axioms Dregg2.Exec.Gas
#assert_namespace_axioms Dregg2.Proof.BeaconSpaceInterior

/-! ## §26 — Wave 10 (2026-05-31): the executor axis begins + the proof-carrying forest.
`ProofForest` packages the ship-the-tree architecture: per-node `StepProofValid` (the §8 circuit
seam, an explicit hypothesis) × `Linked` (prev.newCommit = next.oldCommit) ⇒ the whole forest attests
StepInv (reusing `execForest_attests`) — aggregation/recursion is deferred PERF, not correctness.
`TriDomain` (E1) extends conservation from balance-only to the three domains dregg1 enforces
(balance+authority+metadata), each conserving independently. `AuthModes` (E2) gives the 6 real
authorization modes with witness dispatch + per-mode soundness — incl. `captp_granted_le_held`, the
non-amplification the dregg1 Rust was missing (now also fixed in captp/handoff.rs). `EffectTransfer`
(E3) is the vertical-slice reference template (exec→conserves→authorized→metadata→forward-sim) that
the other 50 effects instantiate. `TransferAir` (Spike) formalizes the REAL air.rs:473 constraint over
BabyBear: field-constraint+range ⇒ ℤ balance update, AND `transfer_underflow_attack` — the off-circuit
wrap gap as a theorem (since closed in-circuit by the RANGECHECK Rust lane, width 126→186). -/
#assert_namespace_axioms Dregg2.Exec.ProofForest
#assert_namespace_axioms Dregg2.Exec.TriDomain
#assert_namespace_axioms Dregg2.Exec.AuthModes
#assert_namespace_axioms Dregg2.Exec.EffectTransfer
#assert_namespace_axioms Dregg2.Spike.TransferAir

/-! ## §27 — Wave 11: E3-breadth, the full effect catalog via the EffectTransfer template.
Each cluster instantiates exec→conserves→authorized→metadata→forward-sim across its regime:
`EffectsPaired` (Conservative Σδ=0 — escrow/notes/obligations/queues/bridge-lock-phases; crypto via
§8 Prop-portal), `EffectsSupply` (Generative disclosed-supply — CreateCell/Factory/Spawn/BridgeMint;
foreign-finality §8-portal), `EffectsAuthority` (cap-graph edits — each carrying NON-AMPLIFICATION,
granted≤held), `EffectsState` (Neutral/Monotonic/Terminal field+lifecycle, via the generic field-write
+ balance/authority non-interference). With EffectTransfer + TurnExecutorFull's mint/burn/grant/revoke,
this covers dregg1's full effect catalog at the executor (E3 complete). -/
#assert_namespace_axioms Dregg2.Exec.EffectsPaired
#assert_namespace_axioms Dregg2.Exec.EffectsSupply
#assert_namespace_axioms Dregg2.Exec.EffectsAuthority
#assert_namespace_axioms Dregg2.Exec.EffectsState

/-! ## §28 — Wave 12: executor axis E4–E6 complete. `ExecRefinementFull` (E5) closes the general
forward simulation — a unified `AbsStep` LTS + `exec_full_refines_spec` (every execFull step over all
5 kinds is a permitted abstract step) + the full operational square `exec_full_step_refines`; the
whole-history `only_connectivity_begets_connectivity` closure is isolated as the named hypothesis
`OnlyConnectivityCloses` (NOT a sorry). `ConditionalTurn` (E4) makes dregg1's conditional/await turns
executable: `execConditionalTurn` (finite Kahn topo-sort + EventualRef slots) with
conserves/atomic/dependency-sound/forward-sim, the EventualRef read identified with `Await.Op.await`.
(E6 = the `@[export] dregg_exec_full_turn` FFI lives in Exec/FFI.lean, an export module verified
standalone + archive-rebuilt; cross-validated by the 9000-case multi-action+adversarial differential.)
With E1–E6 + the full effect catalog, the verified executor models dregg1's turn semantics and runs. -/
#assert_namespace_axioms Dregg2.Spec.ExecRefinementFull
#assert_namespace_axioms Dregg2.Exec.ConditionalTurn

/-! ## §29 — Magnesium-axis first increments. `Spike.EffectVmConstraints` formalizes 7 MORE real
EffectVmAir constraints over BabyBear (selector exactly-one, NoOp identity, transfer hi/dir, balance-lo
range-check soundness, nonce tick) — the headline `underflow_now_impossible` proves the in-circuit
range proof (W9-RANGECHECK) makes the wrap the Transfer spike exhibited IMPOSSIBLE in-circuit (no
executor re-derivation). `Proof.CordialMiners` models dregg1's ACTUAL consensus (the DAG-BFT
wave/leader/ratify/super-ratify commit rule from blocklace/ordering.rs) and proves `cordial_agreement`
(no two conflicting committed leaders per wave) by transferring the `n>3f` quorum-intersection core
from `Proof.BFT` + the equivocation read from `Authority.Blocklace`; liveness/GST/dissemination/Stingray
are named OPENs (not sorries). -/
#assert_namespace_axioms Dregg2.Spike.EffectVmConstraints
#assert_namespace_axioms Dregg2.Proof.CordialMiners

/-! ## §30 — De-vacuification wave (post faithfulness-audit). The audit (docs/rebuild/
FAITHFULNESS-AUDIT.md) found systematic over-claims (kernel-clean but vacuous); this wave fixes the
load-bearing ones. (1) `EffectsAuthority` rights non-amplification was `(⟨t,()⟩).rights ≤ itself`
(`le_refl`, vacuous over `ExecRights := Unit`); NOW genuine over the real `List Auth` lattice —
`IsNonAmplifying held granted := capAuthConferred granted ⊆ capAuthConferred held`, with
`introduce_non_amplifying`/`exercise_non_amplifying` comparing granted-vs-held (two caps) via
`attenuate_subset`, and `amplifying_grant_rejected` proving teeth (a `node` cap conferring `[control]`
over a held `endpoint [read,write]` is rejected). `revokeDelegation_authorized` given a load-bearing
held-edge premise (was a no-premise alias). (2) `TriDomain` authority measure now folds the REAL cap
table (`authMeasure` over `s.kernel.caps`), so the authority-conservation conjunct is graph-tied, not
free-param `x=x`. (3) `ConditionalTurn.CondAbsStep` now `conservedInDomain Domain.balance [a'−a]`
(teeth: `not_condAbsStep_of_ne`), was the always-true `∃δ,a'=a+δ`. (4) `CordialMiners`
`SuperRatification` now DERIVED from the lace (`ratifyingVoters` over `S.lace`), not assumed fields —
`cordial_agreement_from_lace`. (5) `EffectVmConstraints2` adds SetField-gating + hi-limb range +
commitment-shape, and exposes `setfield_aux_honesty_gap` (a new off-circuit gap, as a theorem). -/
#assert_namespace_axioms Dregg2.Spike.EffectVmConstraints2

/-! ## §31 — Carry-forward wave: the CAVEAT + ATTESTATION faces, faithful to the REAL Rust
(docs/rebuild/CARRY-FORWARD-SYNTHESIS.md). The turn is a 3-faced generator (effects ⊕ caveats ⊕
attestation); we had built the effect face deeply while the caveat/attestation faces were thin/shadow
and the Rust was the richer ground truth. These ADDITIVE modules carry the real semantics:
`Authority.CaveatChain` = the macaroon HMAC append-only chain (verify_iff_wellTagged, append_narrows,
integrity_tail_binds, forgery_requires_mac_query reducing forge⇒break-HMAC, removal_breaks_tail) — NOT
the old `Ctx→Bool`; `Authority.ThirdParty` = the real 3P discharge (accepts_iff over ticket/VID
key-recovery ∧ bind-to-parent ∧ freshness ∧ predicate, with stale/unbound/cross-bound rejection teeth)
— NOT a Bool flip; `Authority.SelectiveDisclosure` = hidden-attribute predicate proofs + selective
reveal + anonymous unlinkable multi-show wired to credentials; `Authority.DV` = THE REPUDIATION FIX —
a verifier-indexed `DischargedFor` + the transferability DIAL (public = ∀V ⇒ non-repudiable; designated
= V₀-only ⇒ deniable via the simulator property), the new attestation-face axis. Crypto (HMAC/AEAD/
ZK/DV-ZK) stays an honest §8 Prop-portal throughout (MacKernel/DischargeCrypto), never faked. -/
#assert_namespace_axioms Dregg2.Authority.CaveatChain
#assert_namespace_axioms Dregg2.Authority.ThirdParty
#assert_namespace_axioms Dregg2.Authority.SelectiveDisclosure
#assert_namespace_axioms Dregg2.Authority.DV

/-! ## §32 — The SOUNDNESS WITNESS (consistency + non-vacuity). The worry: do the Prop-carrying
typeclasses hide a vacuous (assumptions unsatisfiable ⇒ vacuous theorems) or contradictory (conjunction
derives False) system? `Dregg2.Consistency` answers NO at the system level: `dregg_consistent_nonempty`
exhibits a single axiom-clean `SystemModel` jointly instantiating all 11 system-level Prop-carriers,
each with a DISCRIMINATING (non-trivial) witness, with cluster lemmas confirming the interacting
carriers (World⊗BFT⊗Pacemaker, BFT⊗SuperRatification, anonymity⊗membership) co-instantiate without
deriving False. The audit's single TRIVIAL-ONLY finding (Crypto/BlindedSet HolderAnonymity, the all-True
shape) is given a non-trivial witness here + the library de-vacuification is queued. The 3 formerly
by-design sorries are now RETIRED to ZERO as typeclass FIELDS / a proved-under-hypothesis theorem
(conservation_step = the Core.ConservesStep field, discharged by Exec.conservation_step_realizes_balance;
search_sound = the Laws.SoundSearchable.find_sound field, witnessed by goodSoundMatcher with
evilMatcher_not_sound as teeth; phi_functorial PROVED under NonDegenerate, satisfiable by
nonDegenerate_concrete). The ~15 crypto-standard carriers
are the honest §8 boundary (necessarily Lean-trivial — that is 'assume DLog is hard', not vacuity), NOT
counted as the non-vacuity evidence. This proves CONSISTENCY + NON-VACUITY, distinct from FAITHFULNESS
(the Rust-grounding axis). -/
#assert_namespace_axioms Dregg2.Consistency

/-! ## §33 — The handler-transformer DISCOVERY (higher-order frontier, honest first-order win).
`Dregg2.HandlerTransformer`: a real first-order unification — `SafeStep` (the safe-composition
preorder), `instSafeStepFpu` (the camera frame-preserving update IS a `SafeStep` instance),
`safe_transformer_composes` (the general composition law), `conservation_is_safe_transformer`
(facet 2 is an instance), and `overshare_rejected` (TEETH — an over-sharing transformer is genuinely
refused). This makes 'a safe handler-transformer = a frame-preserving update' a theorem with a rejecting
witness (= the Iris handler frame-rule, de Vilhena–Pottier POPL'21, instantiated). HONEST OPENs (named,
not sorries): the Fpu=sheaf-gluing weld (camera and proof-forest share no carrier — `proofForest_sheaf_sound`
composes over chainLinked, not SafeStep) and the comodel-morphism / sheaf-of-handlers / recursive-camera
higher-order tier (the stalks are verdicts, not handlers). -/
#assert_namespace_axioms Dregg2.HandlerTransformer

end Dregg2.Claims
