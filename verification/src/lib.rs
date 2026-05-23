//! Deductive verification framework for proof composition soundness.
//!
//! This crate implements a TYPED COMPOSITION CHECKER that verifies:
//! 1. All proof bindings have matching semantic types (type consistency)
//! 2. All assumptions are discharged by another proof or flagged as trust-required
//! 3. No circular dependencies exist in the composition graph
//! 4. The composed system's guarantees and residual trust are clearly identified
//!
//! # Key Insight
//!
//! We don't need a full theorem prover. Each proof has:
//! - Input types (what it requires)
//! - Output types (what it guarantees)
//! - Binding constraints (how inputs/outputs connect to other proofs)
//!
//! Composition checking becomes type checking over a directed graph of proofs.

pub mod pyana_model;

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;

// ============================================================================
// Core type system
// ============================================================================

/// Semantic types for public inputs. These carry meaning beyond "just a field element."
/// Two bindings match only if their semantic types are identical.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SemanticType {
    /// Poseidon2 hash of cell state (commitment to a fact set).
    StateCommitment,
    /// Root of a Merkle tree (federation membership, fact tree, etc.).
    MerkleRoot,
    /// H(action, resource) commitment binding a proof to an action.
    ActionBinding,
    /// Hash of an effect sequence (EffectVM output).
    EffectsHash,
    /// Monotonic counter (replay protection, ordering).
    Nonce,
    /// Value amount (balance, stake, etc.).
    Balance,
    /// Spend-once token (nullifier).
    NullifierHash,
    /// Freshness bound (timestamp or block height).
    Timestamp,
    /// Identity of a federation.
    FederationId,
    /// Identity of a cell.
    CellId,
    /// Capability secret (swiss number / unguessable token).
    SwissNumber,
    /// A running hash chain (IVC accumulation).
    AccumulatedHash,
    /// Blinded presentation tag (unlinkability).
    PresentationTag,
    /// Composition commitment (sub-proof binding).
    CompositionCommitment,
    /// Revealed facts commitment (selective disclosure).
    RevealedFactsCommitment,
    /// Net balance delta (conservation check).
    NetDelta,
    /// Verification key hash (identifies which circuit was used).
    VkHash,
    /// Boolean / decision (ALLOW/DENY).
    Decision,
    /// Custom extensible type.
    Custom(String),
}

impl fmt::Display for SemanticType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::StateCommitment => write!(f, "StateCommitment"),
            Self::MerkleRoot => write!(f, "MerkleRoot"),
            Self::ActionBinding => write!(f, "ActionBinding"),
            Self::EffectsHash => write!(f, "EffectsHash"),
            Self::Nonce => write!(f, "Nonce"),
            Self::Balance => write!(f, "Balance"),
            Self::NullifierHash => write!(f, "NullifierHash"),
            Self::Timestamp => write!(f, "Timestamp"),
            Self::FederationId => write!(f, "FederationId"),
            Self::CellId => write!(f, "CellId"),
            Self::SwissNumber => write!(f, "SwissNumber"),
            Self::AccumulatedHash => write!(f, "AccumulatedHash"),
            Self::PresentationTag => write!(f, "PresentationTag"),
            Self::CompositionCommitment => write!(f, "CompositionCommitment"),
            Self::RevealedFactsCommitment => write!(f, "RevealedFactsCommitment"),
            Self::NetDelta => write!(f, "NetDelta"),
            Self::VkHash => write!(f, "VkHash"),
            Self::Decision => write!(f, "Decision"),
            Self::Custom(s) => write!(f, "Custom({})", s),
        }
    }
}

/// A typed public input slot in a proof statement.
#[derive(Clone, Debug)]
pub struct TypedInput {
    /// Human-readable name for this input.
    pub name: String,
    /// The semantic type of this input.
    pub semantic_type: SemanticType,
    /// Whether this is a wide hash (4 elements) or a single element.
    pub wide: bool,
}

/// A reference to an input slot within a proof (by index).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct InputRef {
    pub index: usize,
}

impl InputRef {
    pub fn new(index: usize) -> Self {
        Self { index }
    }
}

// ============================================================================
// Properties and assumptions
// ============================================================================

/// A property that a proof guarantees (what the verifier learns).
#[derive(Clone, Debug)]
pub enum Property {
    /// State transitioned validly from input[from] to input[to].
    ValidTransition { from: InputRef, to: InputRef },
    /// Element is a member of set (Merkle inclusion).
    Membership { element: InputRef, set: InputRef },
    /// Element was not in set at time T (non-membership).
    NonMembership { element: InputRef, set: InputRef, time: InputRef },
    /// Datalog evaluation reached ALLOW.
    Authorization { facts: InputRef, rules: InputRef },
    /// Attenuation chain is monotonically narrowing (only removes capabilities).
    MonotonicNarrowing { initial: InputRef, final_state: InputRef },
    /// Note is unspent (nullifier is fresh).
    Unspent { commitment: InputRef, nullifier: InputRef },
    /// Value is conserved (no creation/destruction of value).
    Conservation { inputs_sum: InputRef, outputs_sum: InputRef },
    /// Hash chain integrity (all intermediate states are committed).
    HashChainIntegrity { initial: InputRef, final_hash: InputRef, steps: InputRef },
    /// Presentation is unlinkable (tag is properly blinded).
    Unlinkability { tag: InputRef },
    /// Sub-proofs are cryptographically bound together.
    SubProofBinding { commitment: InputRef },
    /// Custom property (for extensibility).
    Custom(String),
}

impl fmt::Display for Property {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ValidTransition { from, to } => {
                write!(f, "ValidTransition(input[{}] -> input[{}])", from.index, to.index)
            }
            Self::Membership { element, set } => {
                write!(f, "Membership(input[{}] in input[{}])", element.index, set.index)
            }
            Self::NonMembership { element, set, time } => {
                write!(f, "NonMembership(input[{}] not in input[{}] at input[{}])", element.index, set.index, time.index)
            }
            Self::Authorization { facts, rules } => {
                write!(f, "Authorization(facts=input[{}], rules=input[{}])", facts.index, rules.index)
            }
            Self::MonotonicNarrowing { initial, final_state } => {
                write!(f, "MonotonicNarrowing(input[{}] -> input[{}])", initial.index, final_state.index)
            }
            Self::Unspent { commitment, nullifier } => {
                write!(f, "Unspent(commitment=input[{}], nullifier=input[{}])", commitment.index, nullifier.index)
            }
            Self::Conservation { inputs_sum, outputs_sum } => {
                write!(f, "Conservation(in=input[{}], out=input[{}])", inputs_sum.index, outputs_sum.index)
            }
            Self::HashChainIntegrity { initial, final_hash, steps } => {
                write!(f, "HashChainIntegrity(input[{}]->input[{}], {} steps)", initial.index, final_hash.index, steps.index)
            }
            Self::Unlinkability { tag } => {
                write!(f, "Unlinkability(tag=input[{}])", tag.index)
            }
            Self::SubProofBinding { commitment } => {
                write!(f, "SubProofBinding(commitment=input[{}])", commitment.index)
            }
            Self::Custom(s) => write!(f, "Custom({})", s),
        }
    }
}

/// An assumption: what must be true for the proof to be meaningful.
/// Assumptions can be DISCHARGED by another proof, or remain as TRUST REQUIREMENTS.
#[derive(Clone, Debug)]
pub enum Assumption {
    /// This Merkle root is the CURRENT federation/cell state (not stale).
    FreshState { root: InputRef, max_age_blocks: u64 },
    /// The executor correctly computed this state transition (no proof, just trust).
    TrustedExecution { commitment: InputRef },
    /// This signature was verified externally (not in-circuit).
    ExternalSignatureValid { signer: InputRef, message: InputRef },
    /// The nullifier set is complete (no double-spends hidden).
    CompleteNullifierSet { set: InputRef },
    /// The timestamp/block height is accurate (clock honesty).
    AccurateClock { timestamp: InputRef },
    /// The network delivered all relevant messages (liveness).
    NetworkLiveness { federation: InputRef },
    /// The executor applied effects atomically (no partial application).
    AtomicExecution { effects_hash: InputRef },
    /// The random blinding factor is truly random (not chosen adversarially).
    HonestRandomness { value: InputRef },
    /// Custom assumption.
    Custom(String),
}

impl fmt::Display for Assumption {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::FreshState { root, max_age_blocks } => {
                write!(f, "FreshState(root=input[{}], max_age={})", root.index, max_age_blocks)
            }
            Self::TrustedExecution { commitment } => {
                write!(f, "TrustedExecution(commitment=input[{}])", commitment.index)
            }
            Self::ExternalSignatureValid { signer, message } => {
                write!(f, "ExternalSignatureValid(signer=input[{}], msg=input[{}])", signer.index, message.index)
            }
            Self::CompleteNullifierSet { set } => {
                write!(f, "CompleteNullifierSet(set=input[{}])", set.index)
            }
            Self::AccurateClock { timestamp } => {
                write!(f, "AccurateClock(timestamp=input[{}])", timestamp.index)
            }
            Self::NetworkLiveness { federation } => {
                write!(f, "NetworkLiveness(federation=input[{}])", federation.index)
            }
            Self::AtomicExecution { effects_hash } => {
                write!(f, "AtomicExecution(effects_hash=input[{}])", effects_hash.index)
            }
            Self::HonestRandomness { value } => {
                write!(f, "HonestRandomness(value=input[{}])", value.index)
            }
            Self::Custom(s) => write!(f, "Custom({})", s),
        }
    }
}

/// How an assumption can be discharged.
#[derive(Clone, Debug)]
pub enum Discharge {
    /// Discharged by a cryptographic proof (another proof in the graph guarantees it).
    ByCryptographicProof { proof_name: String, property_index: usize },
    /// Discharged by a protocol mechanism (e.g., challenge-response for freshness).
    ByProtocol { mechanism: String },
    /// Cannot be discharged -- requires trust in the named component.
    RequiresTrust { component: String, rationale: String },
}

impl fmt::Display for Discharge {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ByCryptographicProof { proof_name, property_index } => {
                write!(f, "discharged by proof '{}' (property #{})", proof_name, property_index)
            }
            Self::ByProtocol { mechanism } => {
                write!(f, "discharged by protocol: {}", mechanism)
            }
            Self::RequiresTrust { component, rationale } => {
                write!(f, "TRUST REQUIRED: {} ({})", component, rationale)
            }
        }
    }
}

// ============================================================================
// Proof statements
// ============================================================================

/// A proof statement: what does accepting this proof guarantee?
#[derive(Clone, Debug)]
pub struct ProofStatement {
    /// Name of this proof (e.g., "IvcFoldChain", "MembershipProof").
    pub name: String,
    /// What the verifier learns (public inputs with semantic types).
    pub public_inputs: Vec<TypedInput>,
    /// What property is guaranteed if the proof verifies.
    pub guarantees: Vec<Property>,
    /// What this proof ASSUMES (must be provided externally).
    pub assumptions: Vec<Assumption>,
    /// How each assumption is discharged (filled in during analysis).
    pub discharges: Vec<Option<Discharge>>,
    /// Whether this proof uses real cryptographic verification (STARK/IVC) or
    /// just constraint checking (which provides no security to a remote verifier).
    pub cryptographic: bool,
}

impl ProofStatement {
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            public_inputs: Vec::new(),
            guarantees: Vec::new(),
            assumptions: Vec::new(),
            discharges: Vec::new(),
            cryptographic: true,
        }
    }

    pub fn add_input(&mut self, name: &str, semantic_type: SemanticType) -> InputRef {
        let index = self.public_inputs.len();
        self.public_inputs.push(TypedInput {
            name: name.to_string(),
            semantic_type,
            wide: false,
        });
        InputRef::new(index)
    }

    pub fn add_wide_input(&mut self, name: &str, semantic_type: SemanticType) -> InputRef {
        let index = self.public_inputs.len();
        self.public_inputs.push(TypedInput {
            name: name.to_string(),
            semantic_type,
            wide: true,
        });
        InputRef::new(index)
    }

    pub fn add_guarantee(&mut self, property: Property) {
        self.guarantees.push(property);
    }

    pub fn add_assumption(&mut self, assumption: Assumption) {
        self.assumptions.push(assumption);
        self.discharges.push(None);
    }

    pub fn set_discharge(&mut self, assumption_index: usize, discharge: Discharge) {
        if assumption_index < self.discharges.len() {
            self.discharges[assumption_index] = Some(discharge);
        }
    }
}

// ============================================================================
// Composition bindings
// ============================================================================

/// A binding between two proofs: an output of one feeds as input to another.
#[derive(Clone, Debug)]
pub struct CompositionBinding {
    /// Name of the source proof.
    pub source_proof: String,
    /// Index into the source proof's public_inputs.
    pub source_output: usize,
    /// Name of the target proof.
    pub target_proof: String,
    /// Index into the target proof's public_inputs.
    pub target_input: usize,
    /// The semantic type that must match on both sides.
    pub semantic_type: SemanticType,
    /// Human-readable description of this binding.
    pub description: String,
}

// ============================================================================
// Error types
// ============================================================================

/// A type error: semantic types don't match across a binding.
#[derive(Clone, Debug)]
pub struct TypeError {
    pub binding_index: usize,
    pub source_proof: String,
    pub source_output: usize,
    pub source_type: SemanticType,
    pub target_proof: String,
    pub target_input: usize,
    pub target_type: SemanticType,
    pub description: String,
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "TYPE ERROR in binding #{}: {}.output[{}] ({}) -> {}.input[{}] ({}). {}",
            self.binding_index, self.source_proof, self.source_output, self.source_type,
            self.target_proof, self.target_input, self.target_type, self.description,
        )
    }
}

/// An undischarged assumption: trust is required.
#[derive(Clone, Debug)]
pub struct UndischargedAssumption {
    pub proof_name: String,
    pub assumption_index: usize,
    pub assumption: Assumption,
    pub suggested_discharge: Option<Discharge>,
}

impl fmt::Display for UndischargedAssumption {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "UNDISCHARGED in '{}' assumption #{}: {}",
            self.proof_name, self.assumption_index, self.assumption
        )?;
        if let Some(ref discharge) = self.suggested_discharge {
            write!(f, " [suggestion: {}]", discharge)?;
        }
        Ok(())
    }
}

/// A gap: a binding that SHOULD exist but doesn't.
#[derive(Clone, Debug)]
pub struct CompositionGap {
    pub proof_name: String,
    pub input_index: usize,
    pub input_name: String,
    pub semantic_type: SemanticType,
    pub description: String,
}

impl fmt::Display for CompositionGap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "GAP: '{}'.input[{}] ({}: {}) has no binding. {}",
            self.proof_name, self.input_index, self.input_name, self.semantic_type, self.description
        )
    }
}

// ============================================================================
// The composition graph and checker
// ============================================================================

/// The composition graph: proofs + bindings between them.
pub struct CompositionGraph {
    pub proofs: Vec<ProofStatement>,
    pub bindings: Vec<CompositionBinding>,
}

/// Full analysis result from running all checks.
#[derive(Debug)]
pub struct AnalysisResult {
    pub type_errors: Vec<TypeError>,
    pub undischarged: Vec<UndischargedAssumption>,
    pub gaps: Vec<CompositionGap>,
    pub is_acyclic: bool,
    pub composed_guarantees: Vec<(String, Property)>,
    pub residual_trust: Vec<(String, Assumption, Discharge)>,
    pub trust_boundary: Vec<TrustBoundaryEntry>,
}

/// An entry in the trust boundary report.
#[derive(Debug)]
pub struct TrustBoundaryEntry {
    pub component: String,
    pub trust_type: TrustType,
    pub properties_at_risk: Vec<String>,
    pub mitigation: String,
}

/// Type of trust required.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TrustType {
    /// No trust needed -- cryptographic enforcement.
    Cryptographic,
    /// Trust the executor to compute correctly.
    ExecutorHonesty,
    /// Trust the network/federation for liveness.
    NetworkLiveness,
    /// Trust a clock source for freshness.
    ClockHonesty,
    /// Trust that randomness is not adversarial.
    RandomnessHonesty,
}

impl fmt::Display for TrustType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Cryptographic => write!(f, "CRYPTOGRAPHIC (no trust needed)"),
            Self::ExecutorHonesty => write!(f, "EXECUTOR HONESTY"),
            Self::NetworkLiveness => write!(f, "NETWORK LIVENESS"),
            Self::ClockHonesty => write!(f, "CLOCK HONESTY"),
            Self::RandomnessHonesty => write!(f, "RANDOMNESS HONESTY"),
        }
    }
}

impl CompositionGraph {
    pub fn new() -> Self {
        Self {
            proofs: Vec::new(),
            bindings: Vec::new(),
        }
    }

    pub fn add_proof(&mut self, proof: ProofStatement) {
        self.proofs.push(proof);
    }

    pub fn add_binding(&mut self, binding: CompositionBinding) {
        self.bindings.push(binding);
    }

    /// Find a proof by name.
    pub fn find_proof(&self, name: &str) -> Option<&ProofStatement> {
        self.proofs.iter().find(|p| p.name == name)
    }

    /// Find a proof by name (mutable).
    pub fn find_proof_mut(&mut self, name: &str) -> Option<&mut ProofStatement> {
        self.proofs.iter_mut().find(|p| p.name == name)
    }

    // ========================================================================
    // Check 1: Type consistency
    // ========================================================================

    /// Verify all bindings have matching semantic types on both sides.
    pub fn check_type_consistency(&self) -> Vec<TypeError> {
        let mut errors = Vec::new();
        let proof_map: HashMap<&str, &ProofStatement> =
            self.proofs.iter().map(|p| (p.name.as_str(), p)).collect();

        for (i, binding) in self.bindings.iter().enumerate() {
            let source = proof_map.get(binding.source_proof.as_str());
            let target = proof_map.get(binding.target_proof.as_str());

            match (source, target) {
                (Some(src), Some(tgt)) => {
                    // Check source output exists
                    if binding.source_output >= src.public_inputs.len() {
                        errors.push(TypeError {
                            binding_index: i,
                            source_proof: binding.source_proof.clone(),
                            source_output: binding.source_output,
                            source_type: binding.semantic_type.clone(),
                            target_proof: binding.target_proof.clone(),
                            target_input: binding.target_input,
                            target_type: binding.semantic_type.clone(),
                            description: format!(
                                "source output index {} out of bounds (proof has {} inputs)",
                                binding.source_output, src.public_inputs.len()
                            ),
                        });
                        continue;
                    }
                    // Check target input exists
                    if binding.target_input >= tgt.public_inputs.len() {
                        errors.push(TypeError {
                            binding_index: i,
                            source_proof: binding.source_proof.clone(),
                            source_output: binding.source_output,
                            source_type: binding.semantic_type.clone(),
                            target_proof: binding.target_proof.clone(),
                            target_input: binding.target_input,
                            target_type: binding.semantic_type.clone(),
                            description: format!(
                                "target input index {} out of bounds (proof has {} inputs)",
                                binding.target_input, tgt.public_inputs.len()
                            ),
                        });
                        continue;
                    }

                    let src_type = &src.public_inputs[binding.source_output].semantic_type;
                    let tgt_type = &tgt.public_inputs[binding.target_input].semantic_type;

                    // Check type match with binding's declared type
                    if src_type != &binding.semantic_type {
                        errors.push(TypeError {
                            binding_index: i,
                            source_proof: binding.source_proof.clone(),
                            source_output: binding.source_output,
                            source_type: src_type.clone(),
                            target_proof: binding.target_proof.clone(),
                            target_input: binding.target_input,
                            target_type: tgt_type.clone(),
                            description: format!(
                                "source type {} does not match binding's declared type {}",
                                src_type, binding.semantic_type
                            ),
                        });
                    }
                    if tgt_type != &binding.semantic_type {
                        errors.push(TypeError {
                            binding_index: i,
                            source_proof: binding.source_proof.clone(),
                            source_output: binding.source_output,
                            source_type: src_type.clone(),
                            target_proof: binding.target_proof.clone(),
                            target_input: binding.target_input,
                            target_type: tgt_type.clone(),
                            description: format!(
                                "target type {} does not match binding's declared type {}",
                                tgt_type, binding.semantic_type
                            ),
                        });
                    }
                    // Check source matches target
                    if src_type != tgt_type {
                        errors.push(TypeError {
                            binding_index: i,
                            source_proof: binding.source_proof.clone(),
                            source_output: binding.source_output,
                            source_type: src_type.clone(),
                            target_proof: binding.target_proof.clone(),
                            target_input: binding.target_input,
                            target_type: tgt_type.clone(),
                            description: "semantic type mismatch between source and target"
                                .to_string(),
                        });
                    }
                }
                (None, _) => {
                    errors.push(TypeError {
                        binding_index: i,
                        source_proof: binding.source_proof.clone(),
                        source_output: binding.source_output,
                        source_type: binding.semantic_type.clone(),
                        target_proof: binding.target_proof.clone(),
                        target_input: binding.target_input,
                        target_type: binding.semantic_type.clone(),
                        description: format!("source proof '{}' not found", binding.source_proof),
                    });
                }
                (_, None) => {
                    errors.push(TypeError {
                        binding_index: i,
                        source_proof: binding.source_proof.clone(),
                        source_output: binding.source_output,
                        source_type: binding.semantic_type.clone(),
                        target_proof: binding.target_proof.clone(),
                        target_input: binding.target_input,
                        target_type: binding.semantic_type.clone(),
                        description: format!("target proof '{}' not found", binding.target_proof),
                    });
                }
            }
        }
        errors
    }

    // ========================================================================
    // Check 2: Assumption coverage
    // ========================================================================

    /// Check all assumptions -- are they discharged by another proof or flagged as trust?
    pub fn check_assumption_coverage(&self) -> Vec<UndischargedAssumption> {
        let mut undischarged = Vec::new();

        for proof in &self.proofs {
            for (i, assumption) in proof.assumptions.iter().enumerate() {
                let discharge = if i < proof.discharges.len() {
                    proof.discharges[i].as_ref()
                } else {
                    None
                };

                if discharge.is_none() {
                    // Try to find a proof that guarantees what this assumption needs
                    let suggested = self.suggest_discharge(proof, assumption);
                    undischarged.push(UndischargedAssumption {
                        proof_name: proof.name.clone(),
                        assumption_index: i,
                        assumption: assumption.clone(),
                        suggested_discharge: suggested,
                    });
                }
            }
        }
        undischarged
    }

    /// Try to automatically suggest how an assumption could be discharged.
    fn suggest_discharge(&self, _proof: &ProofStatement, assumption: &Assumption) -> Option<Discharge> {
        match assumption {
            Assumption::FreshState { .. } => {
                Some(Discharge::ByProtocol {
                    mechanism: "verifier-issued nonce in challenge-response protocol".to_string(),
                })
            }
            Assumption::TrustedExecution { .. } => {
                Some(Discharge::RequiresTrust {
                    component: "cell executor".to_string(),
                    rationale: "state transitions not proven in-circuit; executor computes new state".to_string(),
                })
            }
            Assumption::ExternalSignatureValid { .. } => {
                Some(Discharge::RequiresTrust {
                    component: "signature verification layer".to_string(),
                    rationale: "ed25519 signatures verified outside the STARK circuit".to_string(),
                })
            }
            Assumption::CompleteNullifierSet { .. } => {
                Some(Discharge::RequiresTrust {
                    component: "federation consensus".to_string(),
                    rationale: "nullifier set completeness depends on all nodes reporting spends".to_string(),
                })
            }
            Assumption::AccurateClock { .. } => {
                Some(Discharge::RequiresTrust {
                    component: "verifier's local clock / block height oracle".to_string(),
                    rationale: "timestamps cannot be verified cryptographically".to_string(),
                })
            }
            Assumption::NetworkLiveness { .. } => {
                Some(Discharge::RequiresTrust {
                    component: "network layer".to_string(),
                    rationale: "message delivery is not provable".to_string(),
                })
            }
            Assumption::AtomicExecution { .. } => {
                Some(Discharge::RequiresTrust {
                    component: "cell executor + journal".to_string(),
                    rationale: "atomicity enforced by executor rollback, not proven in-circuit".to_string(),
                })
            }
            Assumption::HonestRandomness { .. } => {
                Some(Discharge::RequiresTrust {
                    component: "prover's RNG".to_string(),
                    rationale: "blinding factor must be truly random for unlinkability".to_string(),
                })
            }
            Assumption::Custom(_) => None,
        }
    }

    // ========================================================================
    // Check 3: Acyclicity
    // ========================================================================

    /// Check that the composition graph is acyclic (no circular dependencies).
    pub fn check_acyclicity(&self) -> bool {
        // Build adjacency list: source -> targets
        let proof_names: Vec<&str> = self.proofs.iter().map(|p| p.name.as_str()).collect();
        let name_to_idx: HashMap<&str, usize> = proof_names
            .iter()
            .enumerate()
            .map(|(i, &n)| (n, i))
            .collect();

        let n = self.proofs.len();
        let mut in_degree = vec![0usize; n];
        let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];

        for binding in &self.bindings {
            if let (Some(&src_idx), Some(&tgt_idx)) = (
                name_to_idx.get(binding.source_proof.as_str()),
                name_to_idx.get(binding.target_proof.as_str()),
            ) {
                if src_idx != tgt_idx {
                    adj[src_idx].push(tgt_idx);
                    in_degree[tgt_idx] += 1;
                }
            }
        }

        // Kahn's algorithm for topological sort
        let mut queue: VecDeque<usize> = VecDeque::new();
        for i in 0..n {
            if in_degree[i] == 0 {
                queue.push_back(i);
            }
        }

        let mut visited = 0;
        while let Some(node) = queue.pop_front() {
            visited += 1;
            for &neighbor in &adj[node] {
                in_degree[neighbor] -= 1;
                if in_degree[neighbor] == 0 {
                    queue.push_back(neighbor);
                }
            }
        }

        visited == n
    }

    // ========================================================================
    // Check 4: Gaps (unbound inputs)
    // ========================================================================

    /// Find inputs that have no binding from another proof.
    /// These are either:
    /// - External inputs (provided by the environment, e.g., federation_root from consensus)
    /// - Gaps that indicate missing composition rules
    pub fn find_gaps(&self) -> Vec<CompositionGap> {
        let mut bound_inputs: HashSet<(String, usize)> = HashSet::new();

        for binding in &self.bindings {
            bound_inputs.insert((binding.target_proof.clone(), binding.target_input));
        }

        let mut gaps = Vec::new();
        for proof in &self.proofs {
            for (i, input) in proof.public_inputs.iter().enumerate() {
                if !bound_inputs.contains(&(proof.name.clone(), i)) {
                    // This is an unbound input -- classify it
                    let is_external = self.is_likely_external_input(&input.semantic_type);
                    if !is_external {
                        gaps.push(CompositionGap {
                            proof_name: proof.name.clone(),
                            input_index: i,
                            input_name: input.name.clone(),
                            semantic_type: input.semantic_type.clone(),
                            description: format!(
                                "No proof provides this {} -- possible composition gap",
                                input.semantic_type
                            ),
                        });
                    }
                }
            }
        }
        gaps
    }

    /// Heuristic: is this semantic type typically provided externally (not by another proof)?
    fn is_likely_external_input(&self, ty: &SemanticType) -> bool {
        matches!(
            ty,
            SemanticType::FederationId
                | SemanticType::Timestamp
                | SemanticType::Nonce
                | SemanticType::ActionBinding
                | SemanticType::CellId
        )
    }

    // ========================================================================
    // Reports
    // ========================================================================

    /// What properties does the COMPOSED system guarantee?
    pub fn composed_guarantees(&self) -> Vec<(String, Property)> {
        let mut guarantees = Vec::new();
        for proof in &self.proofs {
            if proof.cryptographic {
                for prop in &proof.guarantees {
                    guarantees.push((proof.name.clone(), prop.clone()));
                }
            }
        }
        guarantees
    }

    /// What trust assumptions remain undischarged?
    pub fn residual_trust(&self) -> Vec<(String, Assumption, Discharge)> {
        let mut residual = Vec::new();
        for proof in &self.proofs {
            for (i, assumption) in proof.assumptions.iter().enumerate() {
                if let Some(Some(discharge)) = proof.discharges.get(i) {
                    if matches!(discharge, Discharge::RequiresTrust { .. }) {
                        residual.push((
                            proof.name.clone(),
                            assumption.clone(),
                            discharge.clone(),
                        ));
                    }
                }
            }
        }
        residual
    }

    /// Compute the trust boundary: for each component, what trust is needed and what's at risk.
    pub fn trust_boundary(&self) -> Vec<TrustBoundaryEntry> {
        let mut entries: HashMap<String, TrustBoundaryEntry> = HashMap::new();

        for proof in &self.proofs {
            for (i, assumption) in proof.assumptions.iter().enumerate() {
                let discharge = proof.discharges.get(i).and_then(|d| d.as_ref());
                if let Some(Discharge::RequiresTrust { component, rationale }) = discharge {
                    let trust_type = match assumption {
                        Assumption::TrustedExecution { .. } | Assumption::AtomicExecution { .. } => {
                            TrustType::ExecutorHonesty
                        }
                        Assumption::NetworkLiveness { .. } | Assumption::CompleteNullifierSet { .. } => {
                            TrustType::NetworkLiveness
                        }
                        Assumption::AccurateClock { .. } => TrustType::ClockHonesty,
                        Assumption::HonestRandomness { .. } => TrustType::RandomnessHonesty,
                        _ => TrustType::ExecutorHonesty,
                    };

                    let entry = entries.entry(component.clone()).or_insert_with(|| {
                        TrustBoundaryEntry {
                            component: component.clone(),
                            trust_type: trust_type.clone(),
                            properties_at_risk: Vec::new(),
                            mitigation: rationale.clone(),
                        }
                    });
                    // Add the proof's guarantees as "at risk" if this trust is violated
                    for prop in &proof.guarantees {
                        entry.properties_at_risk.push(format!(
                            "{}: {}",
                            proof.name, prop
                        ));
                    }
                }
            }
        }

        entries.into_values().collect()
    }

    // ========================================================================
    // Full analysis
    // ========================================================================

    /// Run all checks and produce a complete analysis.
    pub fn analyze(&self) -> AnalysisResult {
        let type_errors = self.check_type_consistency();
        let undischarged = self.check_assumption_coverage();
        let is_acyclic = self.check_acyclicity();
        let gaps = self.find_gaps();
        let composed_guarantees = self.composed_guarantees();
        let residual_trust = self.residual_trust();
        let trust_boundary = self.trust_boundary();

        AnalysisResult {
            type_errors,
            undischarged,
            gaps,
            is_acyclic,
            composed_guarantees,
            residual_trust,
            trust_boundary,
        }
    }
}

// ============================================================================
// Report formatting
// ============================================================================

impl AnalysisResult {
    /// Format as a human-readable report.
    pub fn format_report(&self) -> String {
        let mut report = String::new();

        report.push_str("==============================================================================\n");
        report.push_str("  PROOF COMPOSITION VERIFICATION REPORT\n");
        report.push_str("==============================================================================\n\n");

        // Type consistency
        report.push_str("--- TYPE CONSISTENCY ---\n");
        if self.type_errors.is_empty() {
            report.push_str("  ALL BINDINGS TYPE-CHECK. No semantic type mismatches.\n");
        } else {
            for err in &self.type_errors {
                report.push_str(&format!("  ERROR: {}\n", err));
            }
        }
        report.push('\n');

        // Acyclicity
        report.push_str("--- ACYCLICITY ---\n");
        if self.is_acyclic {
            report.push_str("  COMPOSITION IS ACYCLIC. No circular proof dependencies.\n");
        } else {
            report.push_str("  WARNING: CYCLE DETECTED in composition graph!\n");
            report.push_str("  Circular proof dependencies make the system unsound.\n");
        }
        report.push('\n');

        // Gaps
        report.push_str("--- COMPOSITION GAPS ---\n");
        if self.gaps.is_empty() {
            report.push_str("  No gaps found. All non-external inputs are bound.\n");
        } else {
            for gap in &self.gaps {
                report.push_str(&format!("  {}\n", gap));
            }
        }
        report.push('\n');

        // Composed guarantees
        report.push_str("--- COMPOSED GUARANTEES (cryptographically enforced) ---\n");
        for (proof_name, prop) in &self.composed_guarantees {
            report.push_str(&format!("  [{}] {}\n", proof_name, prop));
        }
        report.push('\n');

        // Undischarged assumptions
        report.push_str("--- UNDISCHARGED ASSUMPTIONS ---\n");
        if self.undischarged.is_empty() {
            report.push_str("  All assumptions discharged.\n");
        } else {
            for ua in &self.undischarged {
                report.push_str(&format!("  {}\n", ua));
            }
        }
        report.push('\n');

        // Trust boundary
        report.push_str("--- TRUST BOUNDARY ---\n");
        if self.trust_boundary.is_empty() {
            report.push_str("  Fully trustless (all properties cryptographically enforced).\n");
        } else {
            for entry in &self.trust_boundary {
                report.push_str(&format!("  Component: {}\n", entry.component));
                report.push_str(&format!("    Trust type: {}\n", entry.trust_type));
                report.push_str(&format!("    Rationale: {}\n", entry.mitigation));
                report.push_str("    Properties at risk if compromised:\n");
                for prop in &entry.properties_at_risk {
                    report.push_str(&format!("      - {}\n", prop));
                }
                report.push('\n');
            }
        }

        // Residual trust
        report.push_str("--- RESIDUAL TRUST REQUIREMENTS ---\n");
        if self.residual_trust.is_empty() {
            report.push_str("  None (fully trustless).\n");
        } else {
            for (proof_name, assumption, discharge) in &self.residual_trust {
                report.push_str(&format!(
                    "  [{}] {} -- {}\n",
                    proof_name, assumption, discharge
                ));
            }
        }
        report.push('\n');

        // Summary
        report.push_str("--- SUMMARY ---\n");
        let total_guarantees = self.composed_guarantees.len();
        let total_trust = self.residual_trust.len();
        let total_gaps = self.gaps.len();
        let total_errors = self.type_errors.len();
        report.push_str(&format!("  Cryptographic guarantees: {}\n", total_guarantees));
        report.push_str(&format!("  Trust requirements:       {}\n", total_trust));
        report.push_str(&format!("  Composition gaps:         {}\n", total_gaps));
        report.push_str(&format!("  Type errors:              {}\n", total_errors));
        report.push_str(&format!("  Acyclic:                  {}\n", if self.is_acyclic { "YES" } else { "NO" }));

        let soundness = if total_errors == 0 && self.is_acyclic && total_gaps == 0 {
            "SOUND (modulo trust requirements)"
        } else if total_errors == 0 && self.is_acyclic {
            "CONDITIONALLY SOUND (gaps exist)"
        } else {
            "UNSOUND (type errors or cycles detected)"
        };
        report.push_str(&format!("  Overall:                  {}\n", soundness));

        report
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_consistency_pass() {
        let mut graph = CompositionGraph::new();

        let mut p1 = ProofStatement::new("Proof1");
        p1.add_input("root_out", SemanticType::MerkleRoot);

        let mut p2 = ProofStatement::new("Proof2");
        p2.add_input("root_in", SemanticType::MerkleRoot);

        graph.add_proof(p1);
        graph.add_proof(p2);
        graph.add_binding(CompositionBinding {
            source_proof: "Proof1".to_string(),
            source_output: 0,
            target_proof: "Proof2".to_string(),
            target_input: 0,
            semantic_type: SemanticType::MerkleRoot,
            description: "root flows from proof1 to proof2".to_string(),
        });

        let errors = graph.check_type_consistency();
        assert!(errors.is_empty());
    }

    #[test]
    fn test_type_consistency_fail() {
        let mut graph = CompositionGraph::new();

        let mut p1 = ProofStatement::new("Proof1");
        p1.add_input("root_out", SemanticType::MerkleRoot);

        let mut p2 = ProofStatement::new("Proof2");
        p2.add_input("balance_in", SemanticType::Balance);

        graph.add_proof(p1);
        graph.add_proof(p2);
        graph.add_binding(CompositionBinding {
            source_proof: "Proof1".to_string(),
            source_output: 0,
            target_proof: "Proof2".to_string(),
            target_input: 0,
            semantic_type: SemanticType::MerkleRoot,
            description: "mismatched binding".to_string(),
        });

        let errors = graph.check_type_consistency();
        assert!(!errors.is_empty());
    }

    #[test]
    fn test_acyclicity() {
        let mut graph = CompositionGraph::new();

        let mut p1 = ProofStatement::new("A");
        p1.add_input("out", SemanticType::StateCommitment);
        let mut p2 = ProofStatement::new("B");
        p2.add_input("in", SemanticType::StateCommitment);
        p2.add_input("out", SemanticType::StateCommitment);
        let mut p3 = ProofStatement::new("C");
        p3.add_input("in", SemanticType::StateCommitment);

        graph.add_proof(p1);
        graph.add_proof(p2);
        graph.add_proof(p3);

        graph.add_binding(CompositionBinding {
            source_proof: "A".to_string(),
            source_output: 0,
            target_proof: "B".to_string(),
            target_input: 0,
            semantic_type: SemanticType::StateCommitment,
            description: "A -> B".to_string(),
        });
        graph.add_binding(CompositionBinding {
            source_proof: "B".to_string(),
            source_output: 1,
            target_proof: "C".to_string(),
            target_input: 0,
            semantic_type: SemanticType::StateCommitment,
            description: "B -> C".to_string(),
        });

        assert!(graph.check_acyclicity());
    }

    #[test]
    fn test_cycle_detection() {
        let mut graph = CompositionGraph::new();

        let mut p1 = ProofStatement::new("A");
        p1.add_input("x", SemanticType::StateCommitment);
        let mut p2 = ProofStatement::new("B");
        p2.add_input("x", SemanticType::StateCommitment);

        graph.add_proof(p1);
        graph.add_proof(p2);

        // A -> B
        graph.add_binding(CompositionBinding {
            source_proof: "A".to_string(),
            source_output: 0,
            target_proof: "B".to_string(),
            target_input: 0,
            semantic_type: SemanticType::StateCommitment,
            description: "".to_string(),
        });
        // B -> A (cycle!)
        graph.add_binding(CompositionBinding {
            source_proof: "B".to_string(),
            source_output: 0,
            target_proof: "A".to_string(),
            target_input: 0,
            semantic_type: SemanticType::StateCommitment,
            description: "".to_string(),
        });

        assert!(!graph.check_acyclicity());
    }
}
