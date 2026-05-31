-- Dregg2: candidate-independent core for the dregg2 vat model.
--
-- Three modules are candidate-INDEPENDENT (all three dregg2 candidates share
-- the conservation law, the Predicate ⊣ Witness law, and the positional
-- authority model lifted from seL4/l4v integrity):
--
--   * Dregg2.Core              — symmetric-monoidal cells/turns + Σ_k conservation
--   * Dregg2.Laws              — Predicate ⊣ Witness Galois connection + verify/find seam
--   * Dregg2.Authority.Positional — the l4v integrity lift / vat-boundary law template
--   * Dregg2.Confluence        — the THIRD judgement: I-confluence / tier-1 eligibility
--
-- The Boundary/Soundness module is candidate-DEPENDENT. The dregg2 decision picks
-- the COINDUCTIVE (A-style, ▶-guarded bisimulation) shape (see
-- docs/rebuild/dregg2.md §1.3/§8 and metatheory/README.md §"candidate-dependent").
import Dregg2.Tactics       -- shared proof automation
import Dregg2.Core
import Dregg2.Resource
import Dregg2.Laws
import Dregg2.Authority.Positional
import Dregg2.Authority.Caveat   -- keys-as-caps token layer (biscuit/macaroon/caveat/discharge): attenuation chain + attenuate_narrows (the one rule, PROVED) + biscuit/macaroon=vat-boundary + token-as-Verify bridge + #eval
import Dregg2.Confluence
import Dregg2.Boundary
-- Wave (multi-cell + distributed + privacy + coordination + effects + lifecycle):
import Dregg2.StepCamera     -- step-indexed Iris camera (higher-order resources; shares Boundary's ▶)
import Dregg2.JointTurn      -- cross-cell ⊗ : equalizer + CG-2 pullback + CG-5 aggregate, binding-as-hypothesis
import Dregg2.Finality       -- judgement 2: the 4-tier finality lattice + cross-tier join
import Dregg2.Privacy        -- field / value (Pedersen) / graph (stealth+nullifier) privacy tiers
import Dregg2.Coordination   -- MPST global type G → projection → protocol-cell; deadlock-freedom
import Dregg2.Projection     -- cand-D choreography front-end: blue/red split + epp_correspondence (= boundary_law at two altitudes)
import Dregg2.Await          -- algebraic effects + one-shot continuations; turn-as-rollback-handler
import Dregg2.Liveness       -- GC-as-cell-liveness; lease-expiry; cross-vat cycle leak (impossibility)
import Dregg2.Upgrade        -- anti-brick set_program: AIR_VERSION pin + signature fallback
import Dregg2.Execution      -- userspace programs: configurations, runs, invariant-preservation (PROVED)
import Dregg2.CryptoKernel    -- THE PORTAL: crypto ops as an uninterpreted interface (Lean⟷Rust); verify/find seam instantiated; cross-vat bridge closed
import Dregg2.PrivacyKernel   -- privacy realized over the portal: committed_conservation + nullifier anti-double-spend PROVED via the interface laws
-- ─── The 3-layer CryptoKernel split (docs/rebuild/PHASE-CRYPTOKERNEL.md) ───
import Dregg2.Crypto.Primitives      -- Layer A: CryptoPrimitives (Poseidon2 compress/compressN, Pedersen commit+commit_hom PROVED, nullifier); collisionHard/binding/unlinkable as Prop CARRIERS (not idealized hash_inj)
import Dregg2.Crypto.Merkle          -- The first §8 discharge: CircuitIR (mirrors ConstraintExpr subset) + merkleCircuit + merkle_bridge (Satisfies ↔ MerkleMembers; path-recomposition sound∧complete, no primitive seam) PROVED
import Dregg2.Crypto.VerifierKernel  -- Layer B: verify DEFINED as circuit-satisfiable; merkle_verify_sound DERIVED off merkle_bridge (accept ⇒ membership, given the STARK extractable carrier) — the §8 verify-law, derived not assumed
import Dregg2.Crypto.PredicateKernel -- Layer C: per-kind KindObligation (statement+relation+Dial floor); merkle_registry_cascade (registry_sound ∘ verify_sound) + merkle_dial_wired (EpistemicDial pinned to the Merkle verifier at the acceptanceOnly ZK floor) PROVED
import Dregg2.World           -- the sibling portal: network/clock/randomness oracle for consensus; quorum finality over it (PROVED) + Byzantine/GST OPEN
import Dregg2.Exec.Value      -- the Preserves data substrate (dregg2 §5): name-keyed records over a Schema; type-directed flatten with PROVED fixed width (the circuit-over-records foundation)
import Dregg2.Exec.Program    -- the RecordProgram structure-map over records (dregg1 cell/program.rs, name-keyed): name-keyed StateConstraint catalog + Cases/TransitionGuard dispatch + default-deny; Heyting fragment (PROVED) + #eval
import Dregg2.Exec.Cell        -- THE LIVING COINDUCTIVE CELL (Mg keystone): cexec as a Boundary.TurnCoalg; livingCell_sound = genuine bisimulation-to-golden-oracle (sound_of_step_complete recovered, step-completeness supplied by cexec_attests); checkpoint/replay as theorems
import Dregg2.Exec.VatBoundary -- the vat-boundary authority law ON the living cell: intra-vat=authorizedB (Integrity.intra) / cross-vat=token discharges (Integrity.cross); unifies Cell+Caveat+Authority (PROVED) + #eval
import Dregg2.Exec.Kernel     -- the EXECUTABLE kernel (Design-Spec layer): exec checks conservation+authority, fail-closed; PROVED + #eval
import Dregg2.Exec.Generators -- mint/burn conservation generators (mint_delta/burn_delta PROVED)
import Dregg2.Exec.Caps        -- capability ops (grant/attenuate/derive/revoke/invoke) + integrity bridge (PROVED)
import Dregg2.Exec.Unified      -- ONE KernelOp + step: unified conservation (step_delta) + ledger (PROVED)
import Dregg2.Exec.StepComplete -- THE SPINE (Phase 2): cexec attests all 4 StepInv conjuncts (PROVED); conservation_step realized; end-to-end soundness
import Dregg2.Exec.RecordKernel -- Phase (i) CONCRETE-CELL: KernelState's bal:ℤ lifted to a CONTENT-ADDRESSED Value record; recKExec_conserves/recKExec_authorized/recCexec_attests RE-PROVED over the named `balance` FIELD (#assert_axioms-clean)
import Dregg2.Exec.FFI         -- @[export] scalar + record-cell entries → the Lean⟷Rust cascade beachhead (Rust hosts the compiled kernel; PoC round-trips)
import Dregg2.Circuit          -- circuit-from-Lean: CCS IR + bridge (satisfied kernelCircuit ↔ fullStepInv) PROVED; verify-law DERIVED, not assumed
import Dregg2.Exec.CellProgram -- the CellProgram DSL = the executable coalgebra structure-map; denote_conserves PROVED
import Dregg2.Proof.Refine    -- Exec ⊑ Abstract: conservation + integrity-intra refinement (PROVED), simulation diagram OPEN
-- Executable protocols (concrete, computable, theorems PROVED — no sorry):
import Dregg2.Protocol.Transfer  -- two-cell atomic token transfer + payment-channel run; conservation/CG-5/atomicity proved + #eval
import Dregg2.Protocol.Workflow  -- RDII demonstrator: authenticated, capability-gated, attested multi-party workflow (DocuSign-for-workflows); all guarantees PROVED + #eval
-- ─── Swarm wave (living-cell growth across many slices; each a new module on the green core) ───
import Dregg2.Authority.Discharge   -- discharge = the await authority-face: admits_mono_discharge (resolves forward, never un-resolves; PROVED)
import Dregg2.Authority.CDT          -- the capability-derivation-tree spine: path_attenuates (authority shrinks down any derivation chain; PROVED) + CDT≡biscuit bridge to Caveat
import Dregg2.Authority.Intent       -- intent = the ∃-resolver / inverse-vat-boundary await face: intent_fill_verifies (soundness-by-verification vs adversarial matcher; FIND stays undecidable/OPEN)
import Dregg2.Exec.MultiAsset        -- multi-asset conservation: maExec_conserves_per_asset (per-asset Σ_k; PROVED) + camera-FPU bridge
import Dregg2.Exec.RecordCell        -- the RecordProgram IS the structure-map on a record cell: recExec_admitted (nothing commits the program rejects; PROVED)
import Dregg2.Exec.JointCell         -- executable bilateral JointTurn: joint_cg5_conserves (cross-side conservation, no global ledger; PROVED) + binding-as-hypothesis
import Dregg2.Exec.CellFinality      -- finality tier on the cell: commit_at_join (max) + the I-confluence tier-1 eligibility GATE (PROVED, enforced not prose)
import Dregg2.Exec.CellPrivacy       -- the value-rib: committed_transfer_conserves (conservation over Pedersen commitments / hidden amounts; PROVED)
import Dregg2.Exec.CellUpgrade       -- anti-brick upgrade turn: execUpgrade_never_bricks + stale→owner-signature fallback (PROVED)
import Dregg2.Exec.NullifierCell     -- sets→cells: the nullifier set as an I-confluent tier-1-safe cell; spend_no_double_spend (PROVED) + balance≥0 NOT tier-1
import Dregg2.Exec.CellLiveness      -- GC = cell-liveness: death_is_timed_out (lease-expiry; death never decided; PROVED) + cross-vat-cycle impossibility
-- ─── Swarm wave: storage-as-cell-programs (STORAGE-AS-CELL-PROGRAMS.md) + the VK layer ───
import Dregg2.Exec.Factory          -- the EROS constructor / FactoryDescriptor: constructor_transparency (a factory mints cells carrying EXACTLY its contract; PROVED) — closes gaps-1(e)
import Dregg2.Authority.VerificationKey -- dregg1's canonical_vk_v2 mirrored: content-addressed circuit identity + proof_binds_current_vk + proved_state + ChildVkStrategy (PROVED); §8 collision-resistance kept an oracle hypothesis
import Dregg2.Exec.CapInbox          -- CapInbox as a cell-program pattern: inbox_fifo (tail≤head, cursors monotone; PROVED) + sender-auth via the token layer
import Dregg2.Exec.PubSubTopic       -- PubSubTopic as a cell-program pattern: pubsub_append_only (log grows, cursors only forward; PROVED)
import Dregg2.Exec.BlindedQueue      -- BlindedQueue (commitments-in/nullifiers-out): blinded_no_double_spend (reuses NullifierCell) + consume_needs_verify (§8 oracle; PROVED)
import Dregg2.Exec.RelayOperator     -- RelayOperator (bonded relay): bond_floor_held + bond_decrease_needs_dispute + quota_enforced (PROVED) — the economic cell
-- ─── Swarm wave 4: predicate registry / algebraic effects / receipt chain / verifiable credentials ───
import Dregg2.Authority.Predicate     -- the verify/find predicate registry: registry_sound + adversarial_find_cannot_forge (matcher untrusted, verifier TCB; PROVED)
import Dregg2.Exec.Effect             -- algebraic effects as turns: conservation_of_effects + disclosed_non_conservation + exhaustive linearity (PROVED)
import Dregg2.Exec.Receipt            -- the per-cell WitnessedReceipt chain: chain_tamper_evident (HInj/HFresh hyps) + cexec_appends_receipt (PROVED)
import Dregg2.Authority.Credential    -- verifiable credentials as keys-as-caps: credential_verifies_iff_issued_and_not_revoked + revoke_blocks_verify + revocation no-loss I-confluence (PROVED; §8 attestation = oracle)
-- ─── De-toy: the record cell GROWS νF life (REORIENT §5 step 1) ───
import Dregg2.Exec.RecordCellLive     -- the Value/RecordProgram cell as a real Boundary.TurnCoalg: recCexec_attests (4-conjunct step-completeness) + CONSERVATION OVER NAME-KEYED RECORDS (recReplay_preserves_sumEquals) + stepComplete_preserves instance (PROVED; #assert_axioms-clean)
-- ─── Tactics + parked proof-infra (conservation library + consensus bridge) ───
import Dregg2.Conserve                 -- shared conservation lemma library + `conserve`/`commit_cases` tactics (fail-loud, structural; #assert_axioms-clean)
import Dregg2.Catalog                  -- catalog code-gen (`catalog … where` → smart-ctor + admits-char + auto-#assert_axioms triple; regenerates Guard §7) + `discharge` guard-seam tactic + `Dregg2` aesop rule-set + `#assert_namespace_axioms` (all fail-loud; #assert_axioms-clean)
import Dregg2.Exec.Consensus          -- quorum→finality-tier bridge: committedByQuorum→bft tier, net_no_downgrade, finality_monotone_on_net (PROVED, axiom-clean)
-- ─── THE ATOMIC HYPEREDGE (turn = wide pullback over shared TurnId; bilateral/ring/forest as incidences) ───
import Dregg2.Hyperedge               -- Hyperedge = wide-pullback over TurnId + N-ary CG-5; hyperedge_sound PROVED-clean (single-object framing loosens family_joint_sound); SharedTurnId/ring recovered as special cases
-- ─── THE FACTORED MIDDLE LAYER: abstract spec of the ACTUAL dregg2 semantics (Dregg2.Spec) ───
import Dregg2.Spec.Guard              -- ONE verify/find seam (demand⊣supply, first-party|witnessed, meet-semilattice attenuate_narrows NOT Heyting, OneOf coproduct); legacy constraints/auths as DERIVED (PROVED, 0 open)
import Dregg2.Spec.Conservation       -- multi-domain LinearityClass-typed conservation, value-monoid-parametric: committed_iff_cleartext (hidden-yet-conserved) + multi_domain_independent (PROVED; range-rib §8)
import Dregg2.Spec.Authority          -- the GENERATIVE capability graph (the big gap): introduce/amplify/mint + "only connectivity begets connectivity" (gen_step_traces PROVED-clean; whole-history closure 1 honest OPEN)
import Dregg2.Spec.Lifecycle          -- lifecycle = the ATTESTED dual of creation: creation_and_death_are_dual + archival_is_fold(IVC) + reclaim_by_lease + creation_provable_death_temporal (PROVED; co-witnessability 1 OPEN)
-- ─── Spec wave 2: the cross-links (choreography↔hyperedge, joint-via-hyper, await, vat-boundary Φ) ───
import Dregg2.Spec.JointViaHyper      -- N-ary joint soundness DERIVED from hyperedge_sound + hyperedge_is_validity_not_canonicity (validity=proof-check, canonicity=consensus) (PROVED)
import Dregg2.Spec.Choreography       -- blue/red projection-split → red projects to a Hyperedge, blue commits independently (red_projects_to_hyperedge, blue_needs_no_hyperedge; PROVED, operational 1 OPEN)
import Dregg2.Spec.Await              -- the await family = temporal Guard (Conditional, conditional_is_temporal_guard + resolve_monotone) ⊕ dataflow DAG (Promise); zkpromise/zkawait unification (PROVED; topo-sort 1 OPEN)
import Dregg2.Spec.VatBoundary        -- Φ the named-lossy caps↔keys functor: phi_drops_confinement (permission survives, authority doesn't) + forwarded_cap_is_revocable + biscuit/macaroon=Φ-domain (PROVED; functoriality 1 OPEN)
import Dregg2.Spec.Coherence          -- THE WEB (not islands): guard_is_authority_conferral, conservation_is_hyperedge_cg5, lifecycle_revoke_is_authority_restrictive, choreography_red_conserves, guard_attenuate_narrows_is_meet ⇄ authority_confers_narrows_is_meet (PROVED, 0 open) + the Prelude plan
import Dregg2.Spec.ExecRefinement     -- Exec ⊑ Spec beachhead: exec_refines_conservation (toy ℤ ledger = balance domain) + exec_authz_refines_guard (authorizedB = Guard.firstParty onto Authority.Graph); operational LTS honest-OPEN
-- ─── Session wave: program logic, surface, second §8 discharge, first-app Spec layer, the operational LTS ───
import Dregg2.Proof.WP                 -- VCG/WP calculus over the Option-monad transition: wp/Triple + vcg + vcg_run_sound (THE soundness obligation, reduces to stepComplete_preserves) + monotonic-counter & single-ledger escrow worked green; cross-vat escrow hypothesis-routed OPEN
import Dregg2.Exec.AuthTurn            -- the AUTHORITY-mutating executable transition (dual of recKExec's balance turn): recKDelegate/recKRevokeTarget edit `caps`; dual frame (recTotal FIXED) + graph-change match (cap-edit IS Spec.addEdge/removeEdge = Endow/Revoke `result`) PROVED
import Dregg2.Proof.LTS                -- the operational LTS: recAbsStep_forward (balance-turn square) + authAbsStep_forward (authority-turn square via Endow) UNIONED in absStep'_forward — the SINGLE-CELL operational LTS COMPLETE; residual = cross-cell whole-history closure
import Dregg2.Crypto.NonMembership     -- the THIRD §8 discharge: nonmembership_bridge (Satisfies ↔ NonMember, both directions; sorted_gap_excludes the combinatorial heart, two reused Merkle sub-proofs + adjacency gadget, no seam) + nonmembership_verify_sound (derived) + dial at the acceptanceOnly ZK floor
-- ─── Autonomous wave: 4th/5th §8 discharges, the BFT adversary model, the cross-cell LTS, the closed userspace-verification loop ───
import Dregg2.Crypto.Temporal          -- the FOURTH §8 discharge: temporal_bridge (Satisfies ↔ InWindow, both directions; two range_iff comparison gadgets, no primitive seam) + temporal_verify_sound (derived) + dial at `selective`
import Dregg2.Crypto.Dfa               -- the FIFTH §8 discharge: dfa_bridge (Satisfies ↔ DfaAccepts, both directions; per-step Lookup-validity + chaining + initial/accept boundary, Lookup abstracted as δ, no seam) + dfa_verify_sound (derived) + dial at `fullDisclosure` (reference kernel an honest OPEN)
import Dregg2.Proof.BFT                -- the Byzantine/honesty model over World: O1 STRONG bft_safety (conflicting quorums ⇒ ⊥ via honest-witness intersection, Malkhi–Reiter/Li–Lesani, n−f quorum) + O2 reduced-assumption GST liveness; all model assumptions are structure fields, #assert_axioms-clean
import Dregg2.Proof.CrossCellLTS       -- the CROSS-CELL operational LTS: crossAbsStep_forward (bilateral jointApply square: joint-conservation + 2-sided authority frame + 2-sided grounding) + crossAbsRun_forward; CG-2 binding hypothesis-routed; machine-checked obstruction that cross-cell does NOT reduce to single-cell (tensor-non-finality); N-ary forest OPEN
import Dregg2.Proof.WPCatalog          -- the userspace-verification loop CLOSED end-to-end: vcg_discharge (fail-loud, fail_if_success-tested) + eDSL-authored multi-field ledgerSM → vcg → vcg_discharge → vcg_run_sound capstones (conservation + monotonic seq)
-- ─── Papers-in-hand wave: BFT liveness pacemaker, the cross-cell forest + contention dichotomy, the 6th §8 ───
import Dregg2.Proof.BFTLiveness        -- closes the O2 pacemaker OPEN: a GSTRound provably obtains from a DLS88-GST + ELRS-synchronizer + HotStuff-responsive-quorum Pacemaker (all honest fields); World.gst_liveness DERIVED; randomized synchronizer construction the one-layer-deeper OPEN
import Dregg2.Proof.Synchronizer       -- the randomized leader-rotation synchronizer: expected_views_O1 (E[views]=1/h ≤ 3/2 for h>2/3, ELRS expected-O(1)) + honest_hit_as (a.s. hit) PROVED; reduces Pacemaker.synchronizes to the randomness+honest-fraction model; World.rand probability-measure bridge the named OPEN
import Dregg2.Proof.CoinductiveAdversary -- the unbounded-interleaving adversary: obsBisim_traj_of_bisim (confluence-up-to-bisimulation over νF via Lean-4.30 native coinductive) PROVED for the safe fragment given the bisim; deriving it from the finite dichotomy needs an up-to-context closure (Paco/CSLib) — sharp OPEN
import Dregg2.Proof.BeaconSpace        -- the PROBABILISTIC oracle layer (sibling to World's deterministic rand): a Measure over beacon streams + Bernoulli(h) independence; noHonestEverGe_measure_zero + honestLeader_index_exists DISCHARGE Synchronizer.hhit (reduces Pacemaker.synchronizes to the randomness model); interior-h witness gated on an unbuilt mathlib module (Dirac h=1 witness suffices)
-- ─── §8 kinds 7+8 (registry COMPLETE), Phase-(ii) catalog, eDSL-B, + the next dregg1-semantics mirror (CapTP / blocklace / DFA-routing) ───
import Dregg2.Crypto.BlindedSet        -- §8 #7: blindedset_bridge (= merkle_bridge; a BlindedSet membership IS Merkle vs the issuer root) + HolderAnonymity carrier + dial acceptanceOnly (holder hidden)
import Dregg2.Crypto.Custom            -- §8 #8 (registry COMPLETE + OPEN): custom_bridge PARAMETRIC over a CustomRegistration's own bridge field; any future kind registers (vk,circuit,relation,bridge) and inherits the cascade
import Dregg2.CatalogInstances         -- Phase (ii): dregg1's StateConstraint(27)/Authorization(9) catalogs as DERIVED Guard smart-constructors via the `catalog … where` codegen + Effect::linearity coloring; 101 thms #assert_namespace_axioms-clean
import Dregg2.DSLChoreo                -- DSL-B: the `dregg_choreo {…}` choreography eDSL → Coordination.GlobalType (full surface incl recursion; auction inherits deadlock_freedom + privacy_by_projection; #check_projectable elaboration gate)
import Dregg2.Exec.CapTP               -- CapTP transport mirrored: pipelining_preserves_seam + handoff_is_introduce/_non_amplifying/_forwarder_revocable (3-vat Granovetter handoff = Spec.Authority.Introduce crossing Φ); reuses Await/VatBoundary/Authority (distributed-GC liveness 1 OPEN)
import Dregg2.Authority.Blocklace      -- the C-spine's CONCRETE byzantine-repelling DAG: equivocation_detectable (paper 2402.08068 §5) + honest_no_equivocation + cdt_is_blocklace bridge + attested finality (eventual-exclusion-under-partition 1 OPEN)
import Dregg2.Exec.DfaRouting          -- dregg1's DFA message-ROUTING automaton: routed_message_followed_accepting_route (delivery soundness, fail-closed) + route_authorization (per-hop Guard) + unique_route + routing_projects_message_flow; reuses Crypto.Dfa.DfaAccepts
import Dregg2.Crypto.UCBridge          -- UC cross-system bridge: FComDischarge bundles CryptHOL's Pedersen F_com guarantees (perfect_hiding ⇒ unlinkable, pedersen_bind ⇒ binding-under-DLog, real AFP Sigma_Commit_Crypto thms) as Prop carriers; binding_unlinkable_discharged_by_crypthol PROVED in Lean from them (#assert_axioms-clean). CAVEATED: trust widens to Isabelle/HOL + transport fidelity; Isabelle theory in uc-crypthol/ (local green build blocked by afp-devel↔RC3 skew, see PHASE-UC-TRANSPORT.md)
import Dregg2.Proof.ForestLTS          -- the N-ARY cross-cell forest LTS: forestAbsStep_forward (forestApply square, Finset.sum joint conservation, Σ=0 binding hypothesis-routed) + forestAbsRun_forward; bilateral = ι=Fin 2 slice
import Dregg2.Proof.ContendedCrossCell -- the CONTENTION DICHOTOMY, both poles PROVED: contended_commits_confluent (disjoint/I-confluent ⇒ schedule-agnostic, partition-tolerant) + coupled_no_schedule_agnostic_commit (coupled Σ=0 ⇒ ¬∃ schedule-agnostic commit — BEC/CAP impossibility as ¬∃); bridged to Confluence
import Dregg2.Crypto.Bridge            -- the SIXTH §8 discharge: bridge_bridge (Satisfies ↔ BridgeRelation, both directions; comparison via RecordCircuit.range fully proven + abstract compress-opening, no seam) + bridge_verify_sound (derived) + dial at `selective`
import Dregg2.Crypto.Pedersen         -- the SECOND §8 discharge: pedersen_conservation_bridge (Satisfies ↔ Conserves, both directions, commit_hom-grounded, range-gadget non-negativity, no seam) + pedersen_verify_sound (derived) + dial at the `selective` floor
import Dregg2.Protocol.WorkflowGuard  -- the first verified app's Spec layer: Workflow's authz/order/attest gates RE-FOUNDED as Spec.Guard instances; 3 refinement ↔s + whole-step Guard.all equivalence + exec⇒admits bridge (PROVED) + discriminating #eval
import Dregg2.DSL                      -- DSL-A: the `dregg_program {…}` cell-program eDSL → RecordProgram (parser onto proved smart-constructors; counter/escrow elaborate by rfl; #eval admit/reject)
