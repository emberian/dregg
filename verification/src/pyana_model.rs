//! Pyana proof composition model.
//!
//! This module instantiates the deductive verification framework for pyana's
//! actual proof system. It defines:
//! - Each proof statement (EffectVM, Presentation, Membership, IVC, FullTurn)
//! - All bindings between them
//! - Discharges for known trust requirements
//!
//! Running the analysis reveals exactly what the composed system guarantees
//! cryptographically and where trust is required.

use crate::{
    Assumption, CompositionBinding, CompositionGraph, Discharge, InputRef, Property,
    ProofStatement, SemanticType,
};

/// Build the complete pyana proof composition model.
///
/// This models the FULL TURN pipeline:
/// ```text
/// EffectVmProof  -->  verifies effect sequence execution
/// IvcFoldProof   -->  verifies attenuation chain (fold steps)
/// MembershipProof -->  verifies issuer is in federation
/// DerivationProof -->  verifies Datalog authorization (ALLOW)
/// PresentationProof --> composes all above with binding commitments
/// ```
pub fn build_pyana_model() -> CompositionGraph {
    let mut graph = CompositionGraph::new();

    // ========================================================================
    // Proof 1: IVC Fold Chain Proof
    // ========================================================================
    let ivc_proof = build_ivc_fold_proof();
    graph.add_proof(ivc_proof);

    // ========================================================================
    // Proof 2: Membership Proof (issuer in federation)
    // ========================================================================
    let membership_proof = build_membership_proof();
    graph.add_proof(membership_proof);

    // ========================================================================
    // Proof 3: Derivation Proof (Datalog -> ALLOW)
    // ========================================================================
    let derivation_proof = build_derivation_proof();
    graph.add_proof(derivation_proof);

    // ========================================================================
    // Proof 4: Effect VM Proof (turn execution)
    // ========================================================================
    let effect_vm_proof = build_effect_vm_proof();
    graph.add_proof(effect_vm_proof);

    // ========================================================================
    // Proof 5: Presentation Proof (composition wrapper)
    // ========================================================================
    let presentation_proof = build_presentation_proof();
    graph.add_proof(presentation_proof);

    // ========================================================================
    // Bindings: how proofs connect
    // ========================================================================
    add_bindings(&mut graph);

    graph
}

/// IVC Fold Chain: proves attenuation chain is valid.
fn build_ivc_fold_proof() -> ProofStatement {
    let mut proof = ProofStatement::new("IvcFoldChain");

    // Public inputs
    let initial_root = proof.add_input("initial_root", SemanticType::StateCommitment);
    let final_root = proof.add_input("final_root", SemanticType::StateCommitment);
    let _step_count = proof.add_input("step_count", SemanticType::Nonce);
    let accumulated_hash = proof.add_input("accumulated_hash", SemanticType::AccumulatedHash);

    // Guarantees
    proof.add_guarantee(Property::MonotonicNarrowing {
        initial: initial_root.clone(),
        final_state: final_root.clone(),
    });
    proof.add_guarantee(Property::HashChainIntegrity {
        initial: initial_root.clone(),
        final_hash: accumulated_hash,
        steps: InputRef::new(2),
    });
    proof.add_guarantee(Property::ValidTransition {
        from: initial_root,
        to: final_root,
    });

    // Assumptions
    proof.add_assumption(Assumption::FreshState {
        root: InputRef::new(0),
        max_age_blocks: 100,
    });

    // Discharge: freshness via verifier nonce protocol
    proof.set_discharge(
        0,
        Discharge::ByProtocol {
            mechanism: "verifier_nonce in challenge-response ensures proof is fresh".to_string(),
        },
    );

    proof.cryptographic = true;
    proof
}

/// Membership Proof: proves issuer key is in the federation Merkle tree.
fn build_membership_proof() -> ProofStatement {
    let mut proof = ProofStatement::new("IssuerMembership");

    // Public inputs
    let leaf_hash = proof.add_input("issuer_key_hash", SemanticType::StateCommitment);
    let federation_root = proof.add_input("federation_root", SemanticType::MerkleRoot);
    let _action_binding = proof.add_wide_input("action_binding", SemanticType::ActionBinding);
    let _composition_commitment =
        proof.add_wide_input("composition_commitment", SemanticType::CompositionCommitment);

    // Guarantees
    proof.add_guarantee(Property::Membership {
        element: leaf_hash,
        set: federation_root.clone(),
    });

    // Assumptions
    proof.add_assumption(Assumption::FreshState {
        root: federation_root,
        max_age_blocks: 50,
    });
    proof.add_assumption(Assumption::Custom(
        "federation_root reflects current membership (no key revocation missed)".to_string(),
    ));

    // Discharge 0: freshness
    proof.set_discharge(
        0,
        Discharge::ByProtocol {
            mechanism: "verifier checks federation_root against their latest known root".to_string(),
        },
    );
    // Discharge 1: revocation completeness
    proof.set_discharge(
        1,
        Discharge::RequiresTrust {
            component: "federation consensus".to_string(),
            rationale: "revocation propagation depends on all federation nodes syncing".to_string(),
        },
    );

    proof.cryptographic = true;
    proof
}

/// Derivation Proof: proves Datalog evaluation reached ALLOW.
fn build_derivation_proof() -> ProofStatement {
    let mut proof = ProofStatement::new("DerivationProof");

    // Public inputs
    let state_root = proof.add_input("state_root", SemanticType::StateCommitment);
    let _request_hash = proof.add_input("request_hash", SemanticType::ActionBinding);
    let _not_after_height = proof.add_input("not_after_height", SemanticType::Timestamp);
    let _conclusion = proof.add_input("conclusion", SemanticType::Decision);

    // Guarantees
    proof.add_guarantee(Property::Authorization {
        facts: state_root.clone(),
        rules: InputRef::new(1),
    });

    // Assumptions
    proof.add_assumption(Assumption::TrustedExecution {
        commitment: state_root,
    });
    proof.add_assumption(Assumption::AccurateClock {
        timestamp: InputRef::new(2),
    });

    // Discharge 0: trusted execution
    proof.set_discharge(
        0,
        Discharge::RequiresTrust {
            component: "cell executor".to_string(),
            rationale: "derivation state_root is computed by executor; the circuit proves \
                        the derivation is valid GIVEN the state_root, but the state_root itself \
                        must be honestly computed from the actual fact set"
                .to_string(),
        },
    );
    // Discharge 1: clock accuracy
    proof.set_discharge(
        1,
        Discharge::RequiresTrust {
            component: "verifier's local clock / block height oracle".to_string(),
            rationale: "not_after_height expiry is checked against verifier-declared height"
                .to_string(),
        },
    );

    proof.cryptographic = true;
    proof
}

/// Effect VM Proof: proves a sequence of effects executed correctly.
///
/// # Post-Stage-3 shape (2026-05-24)
///
/// The Effect VM AIR now has 46 selectors (was 24), covering 22 new variants:
/// RevokeCapability, EmitEvent, SetPermissions, SetVerificationKey,
/// CreateSealPair, RefreshDelegation, RevokeDelegation, CreateCell,
/// SpawnWithDelegation, BridgeCancel, ExerciseViaCapability, Introduce,
/// PipelinedSend, CreateEscrow, BridgeLock, CreateCommittedEscrow,
/// BridgeMint, BridgeFinalize, ReleaseEscrow, RefundEscrow,
/// ReleaseCommittedEscrow, RefundCommittedEscrow.
///
/// Public input shape is UNCHANGED (still 5 inputs). The composition graph
/// therefore needs no new edges — Stage 3 lives entirely "inside" the AIR.
/// What DOES change is the assumption set:
///
/// - 17 of 22 are **passthrough**: AIR enforces full state passthrough
///   (balance/fields/cap_root unchanged) and binds a variant-specific hash
///   into `effects_hash`. ValidTransition + Conservation still hold trivially
///   (delta = 0).
///
/// - 3 affect balance via real constraints (mirror NoteSpend/NoteCreate):
///   * CreateEscrow — debit
///   * BridgeLock — debit
///   * BridgeMint — credit
///   These are properly covered by the existing Conservation guarantee.
///
/// - 1 has a cap_root transition (RevokeCapability mirrors GrantCapability):
///   ValidTransition covers it as a state transition. **Note:** the AIR does
///   NOT enforce "this cap was previously granted" — like GrantCapability, it
///   only enforces the Merkle-hash update is consistent. Capability honesty
///   is a fold-chain / executor responsibility.
///
/// - 6 (CreateCommittedEscrow, BridgeFinalize, ReleaseEscrow, RefundEscrow,
///   ReleaseCommittedEscrow, RefundCommittedEscrow) are passthrough in the
///   AIR but represent **real off-trace balance movement**. The AIR proves
///   state passthrough; the executor is trusted to reconcile the actual
///   balance change (escrow/bridge ledgers live off-trace).
///   This is a NEW trust requirement Stage 3 introduces.
fn build_effect_vm_proof() -> ProofStatement {
    let mut proof = ProofStatement::new("EffectVmProof");

    // Public inputs (from effect_vm.rs: old_commitment, new_commitment, net_delta, effects_hash, etc.)
    // NOTE: post-Stage-3 the public input layout is UNCHANGED. Only the
    // internal selector count + per-row constraints changed.
    let old_commitment = proof.add_input("old_state_commitment", SemanticType::StateCommitment);
    let new_commitment = proof.add_input("new_state_commitment", SemanticType::StateCommitment);
    let _net_delta = proof.add_input("net_delta", SemanticType::NetDelta);
    let effects_hash = proof.add_input("effects_hash", SemanticType::EffectsHash);
    let _custom_count = proof.add_input("custom_effect_count", SemanticType::Nonce);

    // Guarantees
    proof.add_guarantee(Property::ValidTransition {
        from: old_commitment.clone(),
        to: new_commitment.clone(),
    });
    proof.add_guarantee(Property::Conservation {
        inputs_sum: InputRef::new(2),
        outputs_sum: InputRef::new(2),
    });
    // Stage 3: every variant binds a variant-specific hash into effects_hash
    // (event_hash, vk_hash, escrow_id, cap_slot_hash, etc.). This ensures
    // the prover cannot equivocate about WHICH variants ran — the verifier
    // can reconstruct the expected effects_hash from the claimed trace.
    proof.add_guarantee(Property::Custom(
        "EffectsHashBindingCompleteness: every effect row binds its \
         variant-specific witness into effects_hash, so the verifier can \
         detect any mismatch between the claimed effect sequence and the \
         prover's actual trace (covers all 46 selectors post-Stage-3)"
            .to_string(),
    ));

    // Assumptions
    proof.add_assumption(Assumption::TrustedExecution {
        commitment: old_commitment,
    });
    proof.add_assumption(Assumption::AtomicExecution {
        effects_hash: effects_hash,
    });
    // Stage 3 trust gap: 6 passthrough variants record off-trace balance
    // movements (escrow / bridge ledgers). The AIR proves state passthrough
    // — it does NOT prove the executor's escrow_root or bridge_ledger
    // updates are consistent with the recorded escrow_id / nullifier hash.
    proof.add_assumption(Assumption::Custom(
        "OffTraceBalanceReconciliation: escrow/bridge passthrough variants \
         (CreateCommittedEscrow, BridgeFinalize, Release/RefundEscrow, \
         Release/RefundCommittedEscrow) bind escrow_id / receipt hashes \
         into effects_hash but leave the actual balance reconciliation \
         (e.g., releasing escrowed funds to the recipient) to the executor's \
         off-trace bookkeeping. A malicious executor could replay or skip \
         these reconciliations without the AIR detecting it."
            .to_string(),
    ));
    // Stage 3 trust gap: CreateCommittedEscrow hides value in a Pedersen
    // commitment. The AIR cannot enforce the debit amount without opening
    // the commitment; range-proof + opening proof are external concerns.
    proof.add_assumption(Assumption::Custom(
        "CommittedValueRangeProof: CreateCommittedEscrow's value is hidden \
         in a Pedersen commitment. The Effect VM AIR treats this variant as \
         passthrough (cannot enforce a debit on a hidden value). A separate \
         range-proof + Pedersen-opening proof is required outside the \
         Effect VM scope to bind the commitment to a real balance debit."
            .to_string(),
    ));
    // Stage 3 observation: RevokeCapability AIR enforces the Merkle update
    // shape (new_root = hash(old_root, slot_hash)) but does NOT prove the
    // revoked slot was previously present in the c-list. This mirrors
    // GrantCapability's symmetric weakness — capability-set honesty depends
    // on the executor maintaining a consistent c-list snapshot.
    proof.add_assumption(Assumption::Custom(
        "CapabilitySlotPresence: RevokeCapability (like GrantCapability) \
         enforces the cap_root Merkle-hash update but does not prove the \
         revoked slot was actually present in the old c-list. The executor \
         is trusted to only emit revoke effects for currently-held slots."
            .to_string(),
    ));

    // Discharge 0: old state computed by executor
    proof.set_discharge(
        0,
        Discharge::RequiresTrust {
            component: "cell executor".to_string(),
            rationale: "old_state_commitment is the executor's claimed pre-state; \
                        the circuit proves effects applied correctly FROM this state, \
                        but the starting state must match the actual cell state"
                .to_string(),
        },
    );
    // Discharge 1: atomic execution
    proof.set_discharge(
        1,
        Discharge::RequiresTrust {
            component: "cell executor + journal".to_string(),
            rationale: "atomicity (all-or-nothing) of the effect sequence is enforced \
                        by the executor's journal-based rollback, not by the STARK proof. \
                        A malicious executor could apply partial effects."
                .to_string(),
        },
    );
    // Discharge 2: off-trace balance reconciliation (Stage 3)
    proof.set_discharge(
        2,
        Discharge::RequiresTrust {
            component: "cell executor + escrow/bridge ledger".to_string(),
            rationale: "escrow_root and bridge_ledger live outside the VM trace; \
                        the executor is trusted to honestly reconcile balance \
                        movements that the AIR records only as passthrough + \
                        escrow_id/receipt hash bindings. Mitigation: a separate \
                        EscrowLedgerProof / BridgeLedgerProof would close this gap \
                        by proving the off-trace ledger transitions are consistent \
                        with the effects_hash bindings."
                .to_string(),
        },
    );
    // Discharge 3: committed value range proof (Stage 3)
    proof.set_discharge(
        3,
        Discharge::RequiresTrust {
            component: "external Pedersen range proof".to_string(),
            rationale: "CreateCommittedEscrow's hidden value requires a separate \
                        range proof + Pedersen opening to bind to a real debit; \
                        the Effect VM AIR alone cannot enforce conservation for \
                        commitment-hidden values. Until a CommittedValueProof is \
                        added to the composition graph, conservation is \
                        only enforced for the cleartext (cell balance) ledger, \
                        not for committed-value escrow ledgers."
                .to_string(),
        },
    );
    // Discharge 4: capability slot presence (Stage 3, symmetric with pre-Stage-3 GrantCap)
    proof.set_discharge(
        4,
        Discharge::RequiresTrust {
            component: "cell executor (c-list snapshot)".to_string(),
            rationale: "RevokeCapability binds slot_hash into the cap_root \
                        Merkle update but does not prove slot membership in \
                        the pre-state c-list. The executor must only emit \
                        revoke effects for slots it actually holds; otherwise \
                        cap_root drifts from the executor's c-list snapshot \
                        and downstream membership checks become unsound."
                .to_string(),
        },
    );

    proof.cryptographic = true;
    proof
}

/// Presentation Proof: the top-level composition that binds everything together.
fn build_presentation_proof() -> ProofStatement {
    let mut proof = ProofStatement::new("PresentationProof");

    // Public inputs (from PresentationPublicInputs)
    let federation_root = proof.add_input("federation_root", SemanticType::MerkleRoot);
    let action_binding = proof.add_wide_input("request_predicate", SemanticType::ActionBinding);
    let _timestamp = proof.add_input("timestamp", SemanticType::Timestamp);
    let presentation_tag = proof.add_input("presentation_tag", SemanticType::PresentationTag);
    let _revealed_facts =
        proof.add_wide_input("revealed_facts_commitment", SemanticType::RevealedFactsCommitment);
    let composition_commitment =
        proof.add_wide_input("composition_commitment", SemanticType::CompositionCommitment);
    let _verifier_nonce = proof.add_input("verifier_nonce", SemanticType::Nonce);
    let _verifier_block_height = proof.add_input("verifier_block_height", SemanticType::Timestamp);

    // Guarantees (the composed properties)
    proof.add_guarantee(Property::Unlinkability {
        tag: presentation_tag,
    });
    proof.add_guarantee(Property::SubProofBinding {
        commitment: composition_commitment,
    });
    proof.add_guarantee(Property::Membership {
        element: InputRef::new(0), // federation_root is verified
        set: federation_root.clone(),
    });
    proof.add_guarantee(Property::Authorization {
        facts: InputRef::new(0), // bound to federation root
        rules: action_binding,
    });

    // Assumptions
    proof.add_assumption(Assumption::FreshState {
        root: federation_root,
        max_age_blocks: 100,
    });
    proof.add_assumption(Assumption::HonestRandomness {
        value: InputRef::new(3), // presentation_tag depends on randomness
    });
    proof.add_assumption(Assumption::AccurateClock {
        timestamp: InputRef::new(2), // timestamp
    });

    // Discharges
    proof.set_discharge(
        0,
        Discharge::ByProtocol {
            mechanism: "verifier validates federation_root against their local state".to_string(),
        },
    );
    proof.set_discharge(
        1,
        Discharge::RequiresTrust {
            component: "prover's RNG".to_string(),
            rationale: "presentation_randomness must be truly random for unlinkability; \
                        if the prover reuses randomness, presentations become linkable \
                        (privacy loss, not soundness loss)"
                .to_string(),
        },
    );
    proof.set_discharge(
        2,
        Discharge::RequiresTrust {
            component: "verifier's local clock / block height oracle".to_string(),
            rationale: "timestamp freshness depends on verifier's clock honesty".to_string(),
        },
    );

    proof.cryptographic = true;
    proof
}

/// Add all composition bindings between proofs.
fn add_bindings(graph: &mut CompositionGraph) {
    // Binding 1: IVC final_root -> Derivation state_root
    // The fold chain's final state root is the derivation's starting state.
    graph.add_binding(CompositionBinding {
        source_proof: "IvcFoldChain".to_string(),
        source_output: 1, // final_root
        target_proof: "DerivationProof".to_string(),
        target_input: 0, // state_root
        semantic_type: SemanticType::StateCommitment,
        description: "fold chain's final root feeds into derivation as the fact set root"
            .to_string(),
    });

    // Binding 2: Presentation federation_root -> Membership federation_root
    // The presentation's declared federation root must match what membership proves against.
    graph.add_binding(CompositionBinding {
        source_proof: "PresentationProof".to_string(),
        source_output: 0, // federation_root
        target_proof: "IssuerMembership".to_string(),
        target_input: 1, // federation_root
        semantic_type: SemanticType::MerkleRoot,
        description: "presentation's federation root must match membership proof's root"
            .to_string(),
    });

    // Binding 3: Presentation action_binding -> Membership action_binding
    // The action commitment binds the membership proof to a specific authorization request.
    graph.add_binding(CompositionBinding {
        source_proof: "PresentationProof".to_string(),
        source_output: 1, // request_predicate (action binding)
        target_proof: "IssuerMembership".to_string(),
        target_input: 2, // action_binding
        semantic_type: SemanticType::ActionBinding,
        description: "action binding prevents membership proof replay across requests".to_string(),
    });

    // Binding 4: Presentation composition_commitment -> Membership composition_commitment
    // The composition commitment cryptographically binds all sub-proofs together.
    graph.add_binding(CompositionBinding {
        source_proof: "PresentationProof".to_string(),
        source_output: 5, // composition_commitment
        target_proof: "IssuerMembership".to_string(),
        target_input: 3, // composition_commitment
        semantic_type: SemanticType::CompositionCommitment,
        description: "composition commitment binds membership proof to this specific presentation"
            .to_string(),
    });

    // Binding 5: EffectVM new_state -> IVC initial_root
    // The effect VM's output state is the starting state for the fold chain.
    graph.add_binding(CompositionBinding {
        source_proof: "EffectVmProof".to_string(),
        source_output: 1, // new_state_commitment
        target_proof: "IvcFoldChain".to_string(),
        target_input: 0, // initial_root
        semantic_type: SemanticType::StateCommitment,
        description: "effect VM output state feeds into fold chain as initial state".to_string(),
    });
}

/// Build the model and run analysis, returning the graph for further inspection.
pub fn analyze_pyana_composition() -> (CompositionGraph, crate::AnalysisResult) {
    let graph = build_pyana_model();
    let result = graph.analyze();
    (graph, result)
}

/// Perform a focused analysis: what happens if the executor is compromised?
pub fn analyze_executor_compromise(graph: &CompositionGraph) -> String {
    let mut report = String::new();
    report.push_str("\n");
    report.push_str("==============================================================================\n");
    report.push_str("  THREAT ANALYSIS: COMPROMISED EXECUTOR\n");
    report.push_str("==============================================================================\n\n");

    report.push_str("If the cell executor is compromised (Byzantine), it can:\n\n");

    // Find all properties that depend on executor trust
    let mut at_risk = Vec::new();
    let mut still_holds = Vec::new();

    for proof in &graph.proofs {
        let executor_dependency = proof.assumptions.iter().enumerate().any(|(i, a)| {
            matches!(a, Assumption::TrustedExecution { .. } | Assumption::AtomicExecution { .. })
                && proof
                    .discharges
                    .get(i)
                    .and_then(|d| d.as_ref())
                    .map(|d| matches!(d, Discharge::RequiresTrust { component, .. } if component.contains("executor")))
                    .unwrap_or(false)
        });

        for prop in &proof.guarantees {
            if executor_dependency {
                at_risk.push(format!("[{}] {}", proof.name, prop));
            } else {
                still_holds.push(format!("[{}] {}", proof.name, prop));
            }
        }
    }

    report.push_str("Properties LOST (no longer guaranteed):\n");
    for p in &at_risk {
        report.push_str(&format!("  - {}\n", p));
    }

    report.push_str("\nProperties PRESERVED (cryptographic enforcement independent of executor):\n");
    for p in &still_holds {
        report.push_str(&format!("  + {}\n", p));
    }

    report.push_str("\nConclusion:\n");
    report.push_str("  A compromised executor can forge state transitions and break atomicity,\n");
    report.push_str("  but CANNOT:\n");
    report.push_str("  - Forge issuer membership (Merkle proof is cryptographic)\n");
    report.push_str("  - Break fold chain monotonicity (IVC proves each step narrows)\n");
    report.push_str("  - Forge derivation logic (STARK proves Datalog evaluation)\n");
    report.push_str("  - Link presentations (blinding is prover-side)\n");
    report.push_str("\n");
    report.push_str("  The executor IS trusted for:\n");
    report.push_str("  - Computing the correct initial state commitment\n");
    report.push_str("  - Applying effects atomically (journal rollback)\n");
    report.push_str("  - Not injecting stale/incorrect state roots into proofs\n");
    report.push_str("\n  MITIGATION: Run executor in a TEE, or require multiple executor\n");
    report.push_str("  attestations (quorum) before accepting state transitions.\n");

    report
}

/// Perform focused analysis: what happens with stale federation state?
pub fn analyze_stale_state(graph: &CompositionGraph) -> String {
    let mut report = String::new();
    report.push_str("\n");
    report.push_str("==============================================================================\n");
    report.push_str("  THREAT ANALYSIS: STALE FEDERATION STATE\n");
    report.push_str("==============================================================================\n\n");

    report.push_str("If the verifier accepts a stale federation_root, an attacker can:\n\n");
    report.push_str("  1. Use a revoked issuer key (key was valid in old root, revoked in current)\n");
    report.push_str("  2. Present an expired token (not_after_height exceeded but old root accepted)\n");
    report.push_str("  3. Double-spend nullifiers (nullifier was fresh in old state)\n");
    report.push_str("\n");

    // Find which proofs depend on fresh state
    let mut fresh_dependent = Vec::new();
    for proof in &graph.proofs {
        for assumption in &proof.assumptions {
            if let Assumption::FreshState { max_age_blocks, .. } = assumption {
                fresh_dependent.push(format!(
                    "[{}] requires state no older than {} blocks",
                    proof.name, max_age_blocks
                ));
            }
        }
    }

    report.push_str("Proofs with freshness requirements:\n");
    for p in &fresh_dependent {
        report.push_str(&format!("  - {}\n", p));
    }

    report.push_str("\nMitigation:\n");
    report.push_str("  - Verifier MUST check federation_root against their own latest known root\n");
    report.push_str("  - Use verifier_nonce (challenge-response) to bind proof to current session\n");
    report.push_str("  - Use verifier_block_height to enforce token expiry\n");
    report.push_str("  - These are PROTOCOL-LEVEL mitigations (not cryptographic)\n");

    report
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pyana_model_builds() {
        let graph = build_pyana_model();
        assert_eq!(graph.proofs.len(), 5);
        assert!(!graph.bindings.is_empty());
    }

    #[test]
    fn test_pyana_model_type_checks() {
        let graph = build_pyana_model();
        let errors = graph.check_type_consistency();
        assert!(errors.is_empty(), "Type errors: {:?}", errors);
    }

    #[test]
    fn test_pyana_model_is_acyclic() {
        let graph = build_pyana_model();
        assert!(graph.check_acyclicity());
    }

    #[test]
    fn test_pyana_model_analysis() {
        let (_, result) = analyze_pyana_composition();
        // Should have no type errors
        assert!(result.type_errors.is_empty());
        // Should be acyclic
        assert!(result.is_acyclic);
        // Should have composed guarantees
        assert!(!result.composed_guarantees.is_empty());
        // Should have residual trust (executor, clock, etc.)
        assert!(!result.residual_trust.is_empty());
    }
}
