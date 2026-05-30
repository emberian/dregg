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
