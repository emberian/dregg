//! SP1 proof backend: Succinct's RISC-V zkVM for provable Datalog evaluation.
//!
//! # Architecture
//!
//! Unlike the other backends (Binius, Mina, STARK) which hand-write AIR constraints
//! for specific computations, the SP1 backend proves *execution* of our Datalog
//! evaluator as a standard Rust program running inside a RISC-V zkVM. This means:
//!
//! - No manual constraint writing for the derivation logic
//! - The guest program is just normal Rust code (derivation_air's logic)
//! - SP1 generates a STARK proof that the RISC-V execution was correct
//! - Verification is fast and proof size is ~1-2 KB (with recursion/SNARK wrapping)
//!
//! # Full Setup (not scaffolded here)
//!
//! A complete SP1 integration requires:
//!
//! 1. **Guest crate** (`sp1-guest/` at workspace root):
//!    - A separate `no_std` crate compiled to RISC-V via `sp1-build`
//!    - Contains the Datalog evaluation logic: takes (rule, body_facts, substitution)
//!      as input and produces a derived_fact_hash as output
//!    - Uses `sp1_zkvm::io::read()` for inputs, `sp1_zkvm::io::commit()` for outputs
//!    - Must be compiled with the SP1 toolchain (`cargo prove build`)
//!
//! 2. **Build script** (`circuit/build.rs` or workspace-level):
//!    - Invokes `sp1-build` to compile the guest crate to a RISC-V ELF
//!    - Embeds the ELF binary at compile time via `include_bytes!`
//!    - Requires `sp1-build` as a build dependency
//!
//! 3. **ELF embedding**:
//!    - The compiled guest ELF is embedded in the host binary
//!    - Referenced via a constant like `const DATALOG_ELF: &[u8] = include_bytes!(...)`
//!    - SP1 SDK loads this ELF to set up the prover
//!
//! 4. **SP1 toolchain installation**:
//!    - `curl -L https://sp1up.dev | bash && sp1up`
//!    - Provides the RISC-V target and `cargo prove` subcommand
//!
//! # Feature Flag
//!
//! Enable with `--features sp1`. Without the feature flag, this module provides
//! a structural stub that validates inputs and produces simulated proofs (same
//! pattern as the `binius` backend).
//!
//! # Tradeoffs vs. Hand-Written AIR
//!
//! | Property           | SP1 (zkVM)           | Hand-written AIR (STARK/Binius) |
//! |-------------------|---------------------|-------------------------------|
//! | Development speed  | Fast (just Rust)    | Slow (constraint engineering) |
//! | Proving time       | ~10-30s             | ~0.2-2s                       |
//! | Proof size         | ~1-2 KB (wrapped)   | ~24-48 KB (STARK), ~1-4 KB (Binius) |
//! | Verification time  | ~1ms (Groth16 wrap) | ~5-50ms                       |
//! | Auditability       | High (standard code)| Lower (custom constraints)    |
//! | Flexibility        | Any Rust logic      | Must redesign AIR per change  |

use super::ProofBackend;
use serde::{Deserialize, Serialize};

// ============================================================================
// SP1 imports (feature-gated)
// ============================================================================

#[cfg(feature = "sp1")]
use sp1_sdk::{ProverClient, SP1ProofWithPublicValues, SP1Stdin};

// ============================================================================
// Proof type
// ============================================================================

/// An SP1 proof wrapping zkVM execution of the Datalog evaluator.
///
/// The proof attests that:
/// - A valid Datalog rule application was executed
/// - Given the committed body facts, the derived fact is correct
/// - The execution followed the exact derivation logic (same code as our AIR)
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Sp1Proof {
    /// The serialized SP1 proof bytes (STARK or Groth16-wrapped).
    pub proof_bytes: Vec<u8>,
    /// Public values committed by the guest program.
    /// For membership: [leaf_hash, root_hash]
    /// For derivation: [state_root, derived_fact_hash]
    /// For fold: [old_root, new_root, removal_commitment]
    pub public_values: Vec<[u8; 32]>,
    /// Which circuit/program was proven.
    pub program_type: Sp1ProgramType,
    /// Whether this is a core STARK proof or a Groth16-wrapped proof.
    pub proof_mode: Sp1ProofMode,
}

/// The type of guest program proven.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum Sp1ProgramType {
    /// Merkle membership: guest verifies a hash path from leaf to root.
    Membership,
    /// Datalog derivation: guest evaluates a rule and produces a derived fact.
    Derivation,
    /// Fold step: guest verifies fact removal from a committed set.
    FoldStep,
    /// Full caveat discharge: HMAC chain + predicate evaluation + Merkle membership.
    ///
    /// This is the legacy SP1 program. It proves "this macaroon token is authorized
    /// in context C against state S" as a single RISC-V execution. The proof attests:
    /// - The HMAC-SHA256 chain is valid (no caveats tampered/removed)
    /// - All caveats are satisfied against the provided context
    /// - The token ID is a leaf in the committed Merkle state tree
    CaveatDischarge,
    /// Full Datalog evaluation with private rules and private data.
    ///
    /// This is the new flagship SP1 program. It proves "query Q is derivable from
    /// committed state S under private policy P" as a single RISC-V execution:
    /// - Forward-chaining Datalog evaluation to fixed point (with stratification)
    /// - Private predicate evaluation (arithmetic, temporal, relational, set membership)
    /// - Multi-step attenuation (capability narrowing) + derivation pipeline
    /// - Merkle state binding for all initial facts
    ///
    /// Guest program source: `circuit/sp1-guest/src/main.rs`
    DatalogEvaluation,
}

/// SP1 proof wrapping mode.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum Sp1ProofMode {
    /// Core STARK proof (~hundreds of KB, fast to generate).
    Core,
    /// Compressed via recursion (~50-100 KB).
    Compressed,
    /// Groth16-wrapped for on-chain verification (~1-2 KB, slow to generate).
    Groth16,
}

// ============================================================================
// Guest program ELF (placeholder)
// ============================================================================

// TODO: Once the guest crate is built, embed the ELF here:
//
// const MEMBERSHIP_ELF: &[u8] = include_bytes!("../../../sp1-guest/elf/membership");
// const DERIVATION_ELF: &[u8] = include_bytes!("../../../sp1-guest/elf/derivation");
// const FOLD_STEP_ELF: &[u8] = include_bytes!("../../../sp1-guest/elf/fold_step");
//
// Caveat discharge guest (the flagship program):
//   Source: circuit/sp1-guest/src/main.rs
//   Build:  cd circuit/sp1-guest && cargo prove build
//   ELF:    circuit/sp1-guest/elf/riscv32im-succinct-zkvm-elf
//
// const CAVEAT_DISCHARGE_ELF: &[u8] =
//     include_bytes!("../../sp1-guest/elf/riscv32im-succinct-zkvm-elf");

// ============================================================================
// SP1 prover functions (feature-gated)
// ============================================================================

/// Prove Merkle membership inside SP1.
///
/// The guest program:
/// 1. Reads leaf, siblings, expected_root from stdin
/// 2. Computes the Merkle root from leaf + siblings (using blake3)
/// 3. Asserts computed_root == expected_root
/// 4. Commits (leaf, root) as public values
#[cfg(feature = "sp1")]
fn prove_membership_sp1(
    leaf: &[u8; 32],
    siblings: &[Vec<[u8; 32]>],
    root: &[u8; 32],
) -> Result<Sp1Proof, String> {
    // TODO: Replace with actual ELF once guest crate is compiled.
    // let client = ProverClient::builder().cpu().build();
    // let (pk, vk) = client.setup(MEMBERSHIP_ELF);
    //
    // let mut stdin = SP1Stdin::new();
    // stdin.write(leaf);
    // stdin.write(&siblings.len());
    // for level in siblings {
    //     stdin.write(&level.len());
    //     for sib in level {
    //         stdin.write(sib);
    //     }
    // }
    // stdin.write(root);
    //
    // let proof = client.prove(&pk, &stdin)
    //     .compressed()
    //     .run()
    //     .map_err(|e| format!("SP1 prove error: {e}"))?;
    //
    // // Verify locally before returning
    // client.verify(&proof, &vk)
    //     .map_err(|e| format!("SP1 local verify failed: {e}"))?;
    //
    // let proof_bytes = bincode::serialize(&proof)
    //     .map_err(|e| format!("serialize error: {e}"))?;
    //
    // Ok(Sp1Proof {
    //     proof_bytes,
    //     public_values: vec![*leaf, *root],
    //     program_type: Sp1ProgramType::Membership,
    //     proof_mode: Sp1ProofMode::Compressed,
    // })

    Err("SP1 guest ELF not yet compiled. Run `cd sp1-guest && cargo prove build` first.".into())
}

/// Verify an SP1 membership proof.
#[cfg(feature = "sp1")]
fn verify_membership_sp1(proof: &Sp1Proof, root: &[u8; 32]) -> Result<bool, String> {
    // TODO: Replace with actual verification once guest crate is compiled.
    // let client = ProverClient::builder().cpu().build();
    // let (_, vk) = client.setup(MEMBERSHIP_ELF);
    //
    // let sp1_proof: SP1ProofWithPublicValues = bincode::deserialize(&proof.proof_bytes)
    //     .map_err(|e| format!("deserialize error: {e}"))?;
    //
    // client.verify(&sp1_proof, &vk)
    //     .map_err(|e| format!("SP1 verify error: {e}"))?;
    //
    // // Check that the committed root matches what we expect
    // let committed_root: [u8; 32] = sp1_proof.public_values.read();
    // if &committed_root != root {
    //     return Ok(false);
    // }
    //
    // Ok(true)

    let _ = (proof, root);
    Err("SP1 guest ELF not yet compiled. Run `cd sp1-guest && cargo prove build` first.".into())
}

/// Prove a Datalog derivation step inside SP1.
///
/// The guest program:
/// 1. Reads rule_id, body_fact_hashes, substitution_values, head template
/// 2. Applies substitution to produce the derived fact
/// 3. Verifies body fact membership against the state root
/// 4. Computes derived_fact_hash = hash(head_pred, head_terms)
/// 5. Commits (state_root, derived_fact_hash) as public values
///
/// This is the key advantage of SP1: the derivation logic is just Rust code,
/// not hand-written AIR constraints. Changes to the rule evaluation semantics
/// only require recompiling the guest, not redesigning a 171-column trace.
#[cfg(feature = "sp1")]
fn prove_derivation_sp1(
    _state_root: &[u8; 32],
    _rule_id: u32,
    _body_hashes: &[[u8; 32]],
    _substitution: &[u64],
    _head_predicate: u64,
    _head_terms: &[u64],
) -> Result<Sp1Proof, String> {
    // TODO: Implement once DERIVATION_ELF is available.
    Err("SP1 guest ELF not yet compiled. Run `cd sp1-guest && cargo prove build` first.".into())
}

/// Prove a fold step inside SP1.
#[cfg(feature = "sp1")]
fn prove_fold_step_sp1(
    _old_root: &[u8; 32],
    _new_root: &[u8; 32],
    _removals: &[[u8; 32]],
) -> Result<Sp1Proof, String> {
    // TODO: Implement once FOLD_STEP_ELF is available.
    Err("SP1 guest ELF not yet compiled. Run `cd sp1-guest && cargo prove build` first.".into())
}

/// Verify a fold step proof in SP1.
#[cfg(feature = "sp1")]
fn verify_fold_sp1(_proof: &Sp1Proof) -> Result<bool, String> {
    // TODO: Implement once FOLD_STEP_ELF is available.
    Err("SP1 guest ELF not yet compiled. Run `cd sp1-guest && cargo prove build` first.".into())
}

// ============================================================================
// Stub helpers (used when feature is disabled)
// ============================================================================

/// Hash a Merkle node (same logic as binius backend, for consistency).
fn merkle_hash(current: &[u8; 32], siblings: &[[u8; 32]]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"sp1-merkle-4ary:");
    hasher.update(current);
    for sib in siblings {
        hasher.update(sib);
    }
    *hasher.finalize().as_bytes()
}

/// Compute the Merkle root from a leaf and sibling path.
fn compute_merkle_root(leaf: &[u8; 32], siblings: &[Vec<[u8; 32]>]) -> [u8; 32] {
    let mut current = *leaf;
    for level_sibs in siblings {
        current = merkle_hash(&current, level_sibs);
    }
    current
}

/// Compute a commitment to removal hashes.
fn compute_removal_commitment(removals: &[[u8; 32]]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"sp1-removal-v1:");
    for removal in removals {
        hasher.update(removal);
    }
    *hasher.finalize().as_bytes()
}

// ============================================================================
// Backend implementation
// ============================================================================

/// The SP1 proof backend using Succinct's RISC-V zkVM.
///
/// When the `sp1` feature is enabled, this attempts to use the SP1 prover to
/// generate real zkVM proofs of Datalog evaluation. Without the feature (or
/// before the guest ELF is compiled), it provides structural stubs.
pub struct Sp1Backend;

impl ProofBackend for Sp1Backend {
    type Proof = Sp1Proof;

    fn prove_membership(
        leaf: &[u8; 32],
        siblings: &[Vec<[u8; 32]>],
        root: &[u8; 32],
    ) -> Result<Self::Proof, String> {
        let depth = siblings.len();
        if depth == 0 {
            return Err("Merkle path must have at least one level".into());
        }

        // Verify the witness is valid before attempting to prove.
        let computed_root = compute_merkle_root(leaf, siblings);
        if &computed_root != root {
            return Err(format!(
                "Invalid witness: computed root {:?} != expected root {:?}",
                &computed_root[..4],
                &root[..4]
            ));
        }

        #[cfg(feature = "sp1")]
        {
            return prove_membership_sp1(leaf, siblings, root);
        }

        #[cfg(not(feature = "sp1"))]
        {
            // Structural stub: simulates the proof structure.
            let mut proof_bytes = Vec::new();
            proof_bytes.extend_from_slice(b"SP1V"); // magic
            proof_bytes.push(1); // version
            proof_bytes.extend_from_slice(&(depth as u32).to_le_bytes());
            // Simulate a proof commitment.
            let mut hasher = blake3::Hasher::new();
            hasher.update(b"sp1-stub-membership:");
            hasher.update(leaf);
            hasher.update(root);
            proof_bytes.extend_from_slice(hasher.finalize().as_bytes());

            Ok(Sp1Proof {
                proof_bytes,
                public_values: vec![*leaf, *root],
                program_type: Sp1ProgramType::Membership,
                proof_mode: Sp1ProofMode::Core,
            })
        }
    }

    fn verify_membership(proof: &Self::Proof, root: &[u8; 32]) -> Result<bool, String> {
        if proof.program_type != Sp1ProgramType::Membership {
            return Err("wrong program type for membership verification".into());
        }
        if proof.public_values.len() < 2 {
            return Err("insufficient public values".into());
        }
        if &proof.public_values[1] != root {
            return Ok(false);
        }

        #[cfg(feature = "sp1")]
        {
            return verify_membership_sp1(proof, root);
        }

        #[cfg(not(feature = "sp1"))]
        {
            // Stub verification: check structural validity.
            if proof.proof_bytes.len() < 9 {
                return Err("proof too short".into());
            }
            if &proof.proof_bytes[..4] != b"SP1V" {
                return Err("invalid proof magic".into());
            }
            if proof.proof_bytes[4] != 1 {
                return Err("unsupported proof version".into());
            }
            Ok(true)
        }
    }

    fn prove_fold_step(
        old_root: &[u8; 32],
        new_root: &[u8; 32],
        removals: &[[u8; 32]],
    ) -> Result<Self::Proof, String> {
        if removals.is_empty() {
            return Err("fold step must remove at least one fact".into());
        }

        #[cfg(feature = "sp1")]
        {
            return prove_fold_step_sp1(old_root, new_root, removals);
        }

        #[cfg(not(feature = "sp1"))]
        {
            let removal_commitment = compute_removal_commitment(removals);

            let mut proof_bytes = Vec::new();
            proof_bytes.extend_from_slice(b"SP1V");
            proof_bytes.push(1);
            proof_bytes.extend_from_slice(&(removals.len() as u32).to_le_bytes());
            proof_bytes.extend_from_slice(&removal_commitment);

            Ok(Sp1Proof {
                proof_bytes,
                public_values: vec![*old_root, *new_root, removal_commitment],
                program_type: Sp1ProgramType::FoldStep,
                proof_mode: Sp1ProofMode::Core,
            })
        }
    }

    fn verify_fold(proof: &Self::Proof) -> Result<bool, String> {
        if proof.program_type != Sp1ProgramType::FoldStep {
            return Err("wrong program type for fold verification".into());
        }
        if proof.public_values.len() < 3 {
            return Err("insufficient public values for fold proof".into());
        }

        #[cfg(feature = "sp1")]
        {
            return verify_fold_sp1(proof);
        }

        #[cfg(not(feature = "sp1"))]
        {
            if proof.proof_bytes.len() < 9 {
                return Err("proof too short".into());
            }
            if &proof.proof_bytes[..4] != b"SP1V" {
                return Err("invalid proof magic".into());
            }
            if proof.proof_bytes[4] != 1 {
                return Err("unsupported proof version".into());
            }
            Ok(true)
        }
    }

    fn proof_size(proof: &Self::Proof) -> usize {
        proof.proof_bytes.len() + proof.public_values.len() * 32
    }

    fn backend_name() -> &'static str {
        "sp1-risc-v-zkvm"
    }
}

// ============================================================================
// Derivation-specific API (beyond the ProofBackend trait)
// ============================================================================

/// Input for a Datalog derivation proof in SP1.
///
/// This captures the same information as `DerivationAir` but in a form suitable
/// for passing to the SP1 guest program (serializable, no field elements).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Sp1DerivationInput {
    /// The rule being applied.
    pub rule_id: u32,
    /// Hashes of the body facts (up to MAX_BODY_ATOMS).
    pub body_fact_hashes: Vec<[u8; 32]>,
    /// The state root that body facts are verified against.
    pub state_root: [u8; 32],
    /// Substitution values (variable bindings).
    pub substitution: Vec<u64>,
    /// Head predicate identifier.
    pub head_predicate: u64,
    /// Head terms (after substitution application).
    pub head_terms: Vec<u64>,
}

/// Output committed by the SP1 guest program after successful derivation.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Sp1DerivationOutput {
    /// The state root used for body fact verification.
    pub state_root: [u8; 32],
    /// Hash of the newly derived fact.
    pub derived_fact_hash: [u8; 32],
}

impl Sp1Backend {
    /// Prove a Datalog derivation step using SP1.
    ///
    /// This is the primary use case for the SP1 backend: proving that a rule
    /// application correctly derives a new fact, without hand-writing AIR
    /// constraints for the derivation logic.
    ///
    /// # Arguments
    /// - `input`: The derivation inputs (rule, body facts, substitution, head)
    ///
    /// # Returns
    /// An `Sp1Proof` that attests to the correctness of the derivation.
    pub fn prove_derivation(input: &Sp1DerivationInput) -> Result<Sp1Proof, String> {
        if input.body_fact_hashes.is_empty() {
            return Err("derivation must have at least one body fact".into());
        }
        if input.head_terms.is_empty() {
            return Err("derived fact must have at least one term".into());
        }

        #[cfg(feature = "sp1")]
        {
            return prove_derivation_sp1(
                &input.state_root,
                input.rule_id,
                &input.body_fact_hashes,
                &input.substitution,
                input.head_predicate,
                &input.head_terms,
            );
        }

        #[cfg(not(feature = "sp1"))]
        {
            // Stub: compute the derived fact hash the same way the real guest would.
            let derived_fact_hash = {
                let mut hasher = blake3::Hasher::new();
                hasher.update(b"sp1-derived-fact:");
                hasher.update(&input.head_predicate.to_le_bytes());
                for term in &input.head_terms {
                    hasher.update(&term.to_le_bytes());
                }
                *hasher.finalize().as_bytes()
            };

            let mut proof_bytes = Vec::new();
            proof_bytes.extend_from_slice(b"SP1V");
            proof_bytes.push(1);
            proof_bytes.extend_from_slice(b"DERV");
            proof_bytes.extend_from_slice(&input.rule_id.to_le_bytes());
            // Simulated proof commitment.
            let mut hasher = blake3::Hasher::new();
            hasher.update(b"sp1-stub-derivation:");
            hasher.update(&input.state_root);
            hasher.update(&derived_fact_hash);
            proof_bytes.extend_from_slice(hasher.finalize().as_bytes());

            Ok(Sp1Proof {
                proof_bytes,
                public_values: vec![input.state_root, derived_fact_hash],
                program_type: Sp1ProgramType::Derivation,
                proof_mode: Sp1ProofMode::Core,
            })
        }
    }

    /// Verify a Datalog derivation proof.
    ///
    /// Checks that the SP1 proof is valid and that the committed public values
    /// match the expected state root and derived fact hash.
    pub fn verify_derivation(
        proof: &Sp1Proof,
        expected_state_root: &[u8; 32],
        expected_derived_hash: &[u8; 32],
    ) -> Result<bool, String> {
        if proof.program_type != Sp1ProgramType::Derivation {
            return Err("wrong program type for derivation verification".into());
        }
        if proof.public_values.len() < 2 {
            return Err("insufficient public values for derivation proof".into());
        }
        if &proof.public_values[0] != expected_state_root {
            return Ok(false);
        }
        if &proof.public_values[1] != expected_derived_hash {
            return Ok(false);
        }

        #[cfg(feature = "sp1")]
        {
            // TODO: Full SP1 verification once ELF is available.
            let _ = proof;
            return Err(
                "SP1 guest ELF not yet compiled. Run `cd sp1-guest && cargo prove build` first."
                    .into(),
            );
        }

        #[cfg(not(feature = "sp1"))]
        {
            // Stub verification.
            if proof.proof_bytes.len() < 13 {
                return Err("proof too short".into());
            }
            if &proof.proof_bytes[..4] != b"SP1V" {
                return Err("invalid proof magic".into());
            }
            if &proof.proof_bytes[5..9] != b"DERV" {
                return Err("invalid derivation marker".into());
            }
            Ok(true)
        }
    }
}

// ============================================================================
// Caveat Discharge API (the flagship SP1 use case)
// ============================================================================

/// Input for a full macaroon caveat discharge proof.
///
/// This mirrors the `DischargeInput` type in the SP1 guest program
/// (`circuit/sp1-guest/src/main.rs`). It captures everything needed to prove
/// that a bearer token is authorized in a specific context against a committed state.
///
/// # What Gets Proven
///
/// The SP1 guest program executes three verification steps in sequence:
///
/// 1. **HMAC chain**: Replays `HMAC(root_key, nonce)` through all caveats,
///    verifying the token's cryptographic integrity.
///
/// 2. **Caveat evaluation**: Evaluates every first-party caveat against the
///    authorization context. Supported predicates: ExpiresAt, ResourceScope,
///    ActionMask, MaxUses, IpRange, AttributeGte.
///
/// 3. **Merkle membership**: Verifies the token ID hash is a leaf in the
///    4-ary blake3 Merkle tree committed at `state_root`.
///
/// The combined proof attests: "token T is authorized for context C against state S."
///
/// # Privacy Properties
///
/// The proof reveals ONLY the public outputs (token_id_hash, state_root,
/// context_hash, authorized). The root key, caveat bodies, and Merkle path
/// siblings remain private inside the zkVM execution trace.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Sp1CaveatDischargeInput {
    /// The root key (secret — private witness, never revealed).
    pub root_key: [u8; 32],

    /// The macaroon's nonce (serialized bytes for HMAC input).
    pub nonce_bytes: Vec<u8>,

    /// The ordered list of caveats in wire format.
    /// Each entry: (caveat_type, body_bytes).
    pub caveats: Vec<Sp1WireCaveat>,

    /// The expected HMAC chain tail (the token's signature tag).
    pub expected_tail: [u8; 32],

    /// The authorization context to evaluate caveats against.
    pub context: Sp1AuthContext,

    /// Merkle proof: 3 sibling hashes at each level of the 4-ary tree (leaf-to-root).
    pub merkle_siblings: Vec<[[u8; 32]; 3]>,

    /// The expected Merkle state root.
    pub state_root: [u8; 32],
}

/// Wire caveat for the SP1 guest (mirrors `WireCaveat` from the macaroon crate).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Sp1WireCaveat {
    /// Caveat type identifier.
    pub caveat_type: u16,
    /// Serialized caveat body.
    pub body: Vec<u8>,
}

impl Sp1WireCaveat {
    /// Encode for HMAC chaining: [type_id LE u16][body].
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(2 + self.body.len());
        out.extend_from_slice(&self.caveat_type.to_le_bytes());
        out.extend_from_slice(&self.body);
        out
    }
}

/// Authorization context for caveat evaluation inside SP1.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Sp1AuthContext {
    /// Current unix timestamp (seconds since epoch).
    pub current_time: u64,
    /// The resource being accessed (opaque identifier).
    pub resource_id: u64,
    /// The actions being performed (bitmask).
    pub action_mask: u64,
    /// How many times this token has been used previously.
    pub usage_count: u64,
    /// Source IP address (as u32 for IPv4).
    pub source_ip: u32,
    /// Generic attribute values: (attr_id, value).
    pub attributes: Vec<(u32, u64)>,
}

/// Output committed by the SP1 caveat discharge guest program.
///
/// These are the public values anyone can check after verifying the SP1 proof.
/// They answer: "Which token? Against which state? For which request? Was it valid?"
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Sp1CaveatDischargeOutput {
    /// blake3 hash of the token's key ID (the Merkle leaf).
    pub token_id_hash: [u8; 32],
    /// The Merkle state root the token was verified against.
    pub state_root: [u8; 32],
    /// blake3 hash of the authorization context (prevents proof replay).
    pub context_hash: [u8; 32],
    /// Whether ALL checks passed.
    pub authorized: bool,
}

/// Caveat type constants (must match the guest program and macaroon crate).
pub mod caveat_types {
    pub const EXPIRES_AT: u16 = 1;
    pub const RESOURCE_SCOPE: u16 = 2;
    pub const ACTION_MASK: u16 = 3;
    pub const MAX_USES: u16 = 4;
    pub const IP_RANGE: u16 = 5;
    pub const ATTRIBUTE_GTE: u16 = 6;
    pub const THIRD_PARTY: u16 = 254;
    pub const BIND_TO_PARENT: u16 = 255;
}

impl Sp1Backend {
    /// Prove a full macaroon caveat discharge using SP1.
    ///
    /// This is the most compelling SP1 use case: a single proof that attests
    /// "token T is authorized for context C against state S", covering:
    /// - HMAC-SHA256 chain integrity (cryptographic tamper-proofing)
    /// - Predicate evaluation of all caveats (authorization logic)
    /// - Merkle membership (binding to committed state)
    ///
    /// # Arguments
    /// - `input`: The full discharge input (root key, caveats, context, Merkle path).
    ///
    /// # Returns
    /// An `Sp1Proof` with `program_type == CaveatDischarge`. The public values
    /// contain `[token_id_hash, state_root, context_hash]`.
    ///
    /// # SP1 Toolchain Required
    ///
    /// Real proof generation requires:
    /// 1. `cd circuit/sp1-guest && cargo prove build`
    /// 2. The `sp1` feature enabled in this crate
    ///
    /// Without the toolchain, this produces a structural stub proof that validates
    /// the input correctness (same as other stub backends).
    pub fn prove_caveat_discharge(input: &Sp1CaveatDischargeInput) -> Result<Sp1Proof, String> {
        // Validate inputs.
        if input.nonce_bytes.is_empty() {
            return Err("nonce bytes must not be empty".into());
        }
        if input.merkle_siblings.is_empty() {
            return Err("Merkle path must have at least one level".into());
        }

        // Compute the token ID hash (same as guest program).
        let token_id_hash = {
            let mut hasher = blake3::Hasher::new();
            hasher.update(b"pyana-token-id:");
            hasher.update(&input.nonce_bytes);
            *hasher.finalize().as_bytes()
        };

        // Verify the Merkle witness is valid.
        let computed_root = {
            let mut current = token_id_hash;
            for level_sibs in &input.merkle_siblings {
                current = merkle_hash(&current, level_sibs);
            }
            current
        };
        if computed_root != input.state_root {
            return Err(format!(
                "Invalid Merkle witness: computed root {:?}.. != expected {:?}..",
                &computed_root[..4],
                &input.state_root[..4]
            ));
        }

        // Verify the HMAC chain locally (same as guest program).
        let computed_tail = {
            let mut current = hmac_sha256_host(&input.root_key, &input.nonce_bytes);
            for caveat in &input.caveats {
                let encoded = caveat.encode();
                current = hmac_sha256_host(&current, &encoded);
            }
            current
        };
        if computed_tail != input.expected_tail {
            return Err("HMAC chain verification failed: tail mismatch".into());
        }

        // Compute the context hash (same as guest program).
        let context_hash = compute_context_hash_host(&input.context);

        #[cfg(feature = "sp1")]
        {
            // Real SP1 proof generation.
            // let client = ProverClient::builder().cpu().build();
            // let (pk, vk) = client.setup(CAVEAT_DISCHARGE_ELF);
            //
            // let mut stdin = SP1Stdin::new();
            // stdin.write(&input);  // The guest reads the entire DischargeInput.
            //
            // let proof = client.prove(&pk, &stdin)
            //     .compressed()
            //     .run()
            //     .map_err(|e| format!("SP1 prove error: {e}"))?;
            //
            // client.verify(&proof, &vk)
            //     .map_err(|e| format!("SP1 local verify failed: {e}"))?;
            //
            // let proof_bytes = bincode::serialize(&proof)
            //     .map_err(|e| format!("serialize error: {e}"))?;
            //
            // Ok(Sp1Proof {
            //     proof_bytes,
            //     public_values: vec![token_id_hash, input.state_root, context_hash],
            //     program_type: Sp1ProgramType::CaveatDischarge,
            //     proof_mode: Sp1ProofMode::Compressed,
            // })

            return Err("SP1 caveat discharge ELF not yet compiled. \
                 Run `cd circuit/sp1-guest && cargo prove build` first."
                .into());
        }

        #[cfg(not(feature = "sp1"))]
        {
            // Structural stub: validates logic, produces a simulated proof.
            let mut proof_bytes = Vec::new();
            proof_bytes.extend_from_slice(b"SP1V"); // magic
            proof_bytes.push(1); // version
            proof_bytes.extend_from_slice(b"DSCH"); // discharge marker
            proof_bytes.extend_from_slice(&(input.caveats.len() as u32).to_le_bytes());

            // Simulated proof commitment (hash of all inputs).
            let mut hasher = blake3::Hasher::new();
            hasher.update(b"sp1-stub-discharge:");
            hasher.update(&token_id_hash);
            hasher.update(&input.state_root);
            hasher.update(&context_hash);
            proof_bytes.extend_from_slice(hasher.finalize().as_bytes());

            Ok(Sp1Proof {
                proof_bytes,
                public_values: vec![token_id_hash, input.state_root, context_hash],
                program_type: Sp1ProgramType::CaveatDischarge,
                proof_mode: Sp1ProofMode::Core,
            })
        }
    }

    /// Verify a caveat discharge proof.
    ///
    /// Checks that:
    /// - The proof type is CaveatDischarge
    /// - The committed state root matches the expected one
    /// - The context hash matches (proving the proof is for THIS request)
    /// - The SP1 proof itself is valid (with real SP1, this verifies the STARK)
    pub fn verify_caveat_discharge(
        proof: &Sp1Proof,
        expected_state_root: &[u8; 32],
        expected_context_hash: &[u8; 32],
    ) -> Result<bool, String> {
        if proof.program_type != Sp1ProgramType::CaveatDischarge {
            return Err("wrong program type for caveat discharge verification".into());
        }
        if proof.public_values.len() < 3 {
            return Err("insufficient public values for discharge proof".into());
        }

        // Check state root matches.
        if &proof.public_values[1] != expected_state_root {
            return Ok(false);
        }
        // Check context hash matches (prevents proof replay across contexts).
        if &proof.public_values[2] != expected_context_hash {
            return Ok(false);
        }

        #[cfg(feature = "sp1")]
        {
            // TODO: Full SP1 verification once ELF is available.
            return Err("SP1 caveat discharge ELF not yet compiled. \
                 Run `cd circuit/sp1-guest && cargo prove build` first."
                .into());
        }

        #[cfg(not(feature = "sp1"))]
        {
            // Stub verification: check structural validity.
            if proof.proof_bytes.len() < 13 {
                return Err("proof too short".into());
            }
            if &proof.proof_bytes[..4] != b"SP1V" {
                return Err("invalid proof magic".into());
            }
            if proof.proof_bytes[4] != 1 {
                return Err("unsupported proof version".into());
            }
            if &proof.proof_bytes[5..9] != b"DSCH" {
                return Err("invalid discharge marker".into());
            }
            Ok(true)
        }
    }

    /// Extract the token ID hash from a verified discharge proof.
    ///
    /// After `verify_caveat_discharge` returns Ok(true), call this to get
    /// the token identifier that was proven authorized.
    pub fn discharge_token_id(proof: &Sp1Proof) -> Result<[u8; 32], String> {
        if proof.program_type != Sp1ProgramType::CaveatDischarge {
            return Err("wrong program type".into());
        }
        if proof.public_values.is_empty() {
            return Err("no public values".into());
        }
        Ok(proof.public_values[0])
    }
}

/// Compute HMAC-SHA256 on the host side (for input validation).
fn hmac_sha256_host(key: &[u8], data: &[u8]) -> [u8; 32] {
    // Use blake3 keyed-hash as a stand-in for HMAC-SHA256 in the stub.
    // The real SP1 guest uses actual HMAC-SHA256 via the hmac crate.
    // For structural validation in the stub, we replicate the same logic.
    //
    // NOTE: In production with feature = "sp1", the host would use the real
    // hmac crate (same as the guest) for input validation. The stub uses blake3
    // to avoid pulling hmac as a non-optional dependency of the circuit crate.
    let mut hasher = blake3::Hasher::new_keyed(&{
        // blake3 keyed hash needs exactly 32 bytes; if key is shorter, pad.
        let mut k = [0u8; 32];
        let len = key.len().min(32);
        k[..len].copy_from_slice(&key[..len]);
        k
    });
    hasher.update(data);
    *hasher.finalize().as_bytes()
}

/// Compute context hash on the host side (must match guest program).
fn compute_context_hash_host(context: &Sp1AuthContext) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"pyana-auth-context-v1:");
    hasher.update(&context.current_time.to_le_bytes());
    hasher.update(&context.resource_id.to_le_bytes());
    hasher.update(&context.action_mask.to_le_bytes());
    hasher.update(&context.usage_count.to_le_bytes());
    hasher.update(&context.source_ip.to_le_bytes());
    hasher.update(&(context.attributes.len() as u32).to_le_bytes());
    for (attr_id, value) in &context.attributes {
        hasher.update(&attr_id.to_le_bytes());
        hasher.update(&value.to_le_bytes());
    }
    *hasher.finalize().as_bytes()
}

// ============================================================================
// Full Datalog Evaluation API (the new flagship SP1 use case)
// ============================================================================

/// A term in the Datalog language for the SP1 guest program.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Sp1Term {
    /// A ground constant value.
    Const(u64),
    /// A logic variable, identified by index within the rule.
    Var(u32),
    /// Wildcard — matches anything, does not bind.
    Wildcard,
}

/// A Datalog atom for the SP1 guest program.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Sp1Atom {
    /// Predicate symbol (interned as u64).
    pub predicate: u64,
    /// Terms of this atom.
    pub terms: Vec<Sp1Term>,
}

/// A built-in predicate constraint for the SP1 guest.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Sp1BuiltinConstraint {
    /// term_a >= term_b.
    Gte { a: Sp1Term, b: Sp1Term },
    /// term_a > term_b.
    Gt { a: Sp1Term, b: Sp1Term },
    /// term_a == term_b.
    Eq { a: Sp1Term, b: Sp1Term },
    /// term_a != term_b.
    Neq { a: Sp1Term, b: Sp1Term },
    /// term_a + term_b == result.
    Add {
        a: Sp1Term,
        b: Sp1Term,
        result: Sp1Term,
    },
    /// term_a * term_b == result.
    Mul {
        a: Sp1Term,
        b: Sp1Term,
        result: Sp1Term,
    },
    /// Temporal: timestamp must be within duration_secs of current_time.
    WithinDuration {
        timestamp: Sp1Term,
        duration_secs: u64,
    },
    /// Set membership: term IN set.
    InSet { term: Sp1Term, set: Vec<u64> },
}

/// A Datalog rule for the SP1 guest program.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Sp1Rule {
    /// The head atom (conclusion).
    pub head: Sp1Atom,
    /// Body atoms (conjunction).
    pub body: Vec<Sp1Atom>,
    /// Built-in constraints.
    pub constraints: Vec<Sp1BuiltinConstraint>,
    /// Stratum for stratified evaluation.
    pub stratum: u32,
}

/// A ground fact for the SP1 guest program.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Sp1Fact {
    pub predicate: u64,
    pub terms: Vec<u64>,
}

/// Merkle proof for a fact in the 4-ary BLAKE3 tree.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Sp1MerkleProof {
    /// Sibling hashes at each level (3 per level for 4-ary tree).
    pub siblings: Vec<[[u8; 32]; 3]>,
    /// Position index at each level (0-3).
    pub positions: Vec<u8>,
}

/// An attenuation step: remove capabilities from a token's fact set.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Sp1AttenuationStep {
    /// Facts to remove (capability narrowing).
    pub removed_facts: Vec<Sp1Fact>,
    /// Merkle proofs for each removed fact.
    pub removal_proofs: Vec<Sp1MerkleProof>,
}

/// Complete input for a Datalog evaluation proof in SP1.
///
/// This is the new flagship SP1 program input. It captures everything needed to
/// prove that a query is derivable from a committed fact database under a private
/// rule set (policy), with private attribute values and optional attenuation.
///
/// # What Gets Proven
///
/// The SP1 guest program executes:
/// 1. **Policy commitment**: Hashes the rule set to produce a verifiable commitment
/// 2. **Merkle membership**: Verifies all initial facts against the committed state root
/// 3. **Attenuation pipeline**: Verifies and processes capability narrowing steps
/// 4. **Forward-chaining Datalog**: Evaluates rules to fixed point with stratification
/// 5. **Query check**: Determines if the requested fact is in the derived database
///
/// # Privacy Properties
///
/// - Rule set (policy): PRIVATE — verifier only sees policy_commitment hash
/// - Attribute values: PRIVATE — verifier only sees predicates were satisfied
/// - Merkle proofs: PRIVATE — verifier only sees the root
/// - Attenuation steps: PRIVATE — verifier only sees the effective state root
/// - Query fact and authorization result: PUBLIC
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Sp1DatalogInput {
    // ── Private witnesses ──
    /// The Datalog rule set (PRIVATE).
    pub rules: Vec<Sp1Rule>,

    /// Merkle proofs for initial facts (PRIVATE).
    pub merkle_proofs: Vec<(Sp1Fact, Sp1MerkleProof)>,

    /// Private attribute values: (attribute_id, value).
    pub attribute_values: Vec<(u64, u64)>,

    /// Attenuation steps (PRIVATE).
    pub attenuation_steps: Vec<Sp1AttenuationStep>,

    /// Initial facts (must have valid Merkle proofs above).
    pub initial_facts: Vec<Sp1Fact>,

    // ── Public inputs ──
    /// The Merkle root of the initial fact database (PUBLIC).
    pub fact_db_root: [u8; 32],

    /// The query to evaluate (PUBLIC).
    pub query: Sp1Fact,

    /// Current timestamp for temporal predicates (PUBLIC).
    pub current_time: u64,
}

/// Public output of the Datalog evaluation proof.
///
/// These are the values committed by the SP1 guest program and verifiable by anyone:
/// - `authorized`: Was the query derivable from the committed state under the policy?
/// - `derived_fact_hash`: BLAKE3 hash of the queried fact
/// - `state_root`: The effective state root (post-attenuation)
/// - `policy_commitment`: hash(rule_set) — check against approved policy registry
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Sp1DatalogOutput {
    /// Whether the query was successfully derived.
    pub authorized: bool,
    /// BLAKE3 hash of the derived conclusion fact.
    pub derived_fact_hash: [u8; 32],
    /// The effective state root (post-attenuation if applicable).
    pub state_root: [u8; 32],
    /// Policy commitment: hash of the rule set.
    pub policy_commitment: [u8; 32],
}

impl Sp1Backend {
    /// Prove a full Datalog evaluation using SP1.
    ///
    /// This is the new flagship SP1 use case: proving complex authorization logic
    /// with private rules and private data. The proof attests:
    ///
    /// - "Query Q is derivable from committed state S under some policy P"
    /// - Without revealing: the rules, the attribute values, or the Merkle paths
    /// - The verifier checks policy_commitment against their approved policy registry
    ///
    /// # Why This Matters vs. Hand-Written AIR
    ///
    /// The hand-written `DerivationAir` (171 columns) supports at most 8 body atoms,
    /// 8 variables, and a fixed set of constraint types. The `MultiStepAir` chains up
    /// to 32 derivation steps. Together they require ~4000 lines of constraint code.
    ///
    /// This SP1 guest program supports:
    /// - Arbitrary rule shapes (any number of body atoms and variables)
    /// - Stratified evaluation (correct semantics for layered derivation)
    /// - Recursive rules (with fixed-point detection)
    /// - Rich built-in predicates (arithmetic, temporal, set membership)
    /// - Attenuation pipeline (fold + derivation in one proof)
    ///
    /// All in ~500 lines of straightforward Rust, with the same proof interface.
    pub fn prove_datalog_evaluation(input: &Sp1DatalogInput) -> Result<Sp1Proof, String> {
        // Validate inputs.
        if input.rules.is_empty() {
            return Err("rule set must not be empty".into());
        }
        if input.initial_facts.is_empty() {
            return Err("initial facts must not be empty".into());
        }

        // Verify Merkle proofs for all initial facts.
        for (fact, proof) in &input.merkle_proofs {
            if !verify_fact_merkle_proof(fact, proof, &input.fact_db_root) {
                return Err(format!(
                    "Merkle proof failed for fact with predicate {}",
                    fact.predicate
                ));
            }
        }

        // Process attenuation to get effective state root.
        let effective_root =
            process_attenuation_host(&input.attenuation_steps, &input.fact_db_root)?;

        // Compute policy commitment (same as guest).
        let policy_commitment = compute_policy_commitment_host(&input.rules);

        // Run the Datalog evaluation locally (same logic as guest) to determine result.
        let authorized = evaluate_datalog_locally(input);

        // Compute derived fact hash.
        let derived_fact_hash = hash_fact_host(&input.query);

        #[cfg(feature = "sp1")]
        {
            // Real SP1 proof generation.
            // let client = ProverClient::builder().cpu().build();
            // let (pk, vk) = client.setup(DATALOG_EVALUATION_ELF);
            //
            // let mut stdin = SP1Stdin::new();
            // stdin.write(&input);
            //
            // let proof = client.prove(&pk, &stdin)
            //     .compressed()
            //     .run()
            //     .map_err(|e| format!("SP1 prove error: {e}"))?;
            //
            // client.verify(&proof, &vk)
            //     .map_err(|e| format!("SP1 local verify failed: {e}"))?;
            //
            // let proof_bytes = bincode::serialize(&proof)
            //     .map_err(|e| format!("serialize error: {e}"))?;
            //
            // Ok(Sp1Proof {
            //     proof_bytes,
            //     public_values: vec![
            //         derived_fact_hash,
            //         effective_root,
            //         policy_commitment,
            //     ],
            //     program_type: Sp1ProgramType::DatalogEvaluation,
            //     proof_mode: Sp1ProofMode::Compressed,
            // })

            return Err("SP1 datalog evaluation ELF not yet compiled. \
                 Run `cd circuit/sp1-guest && cargo prove build` first."
                .into());
        }

        #[cfg(not(feature = "sp1"))]
        {
            // Structural stub: validates logic, produces a simulated proof.
            let mut proof_bytes = Vec::new();
            proof_bytes.extend_from_slice(b"SP1V"); // magic
            proof_bytes.push(2); // version 2 (datalog evaluation)
            proof_bytes.extend_from_slice(b"DLOG"); // datalog marker
            proof_bytes.push(authorized as u8);
            proof_bytes.extend_from_slice(&(input.rules.len() as u32).to_le_bytes());
            proof_bytes.extend_from_slice(&(input.initial_facts.len() as u32).to_le_bytes());

            // Simulated proof commitment.
            let mut hasher = blake3::Hasher::new();
            hasher.update(b"sp1-stub-datalog:");
            hasher.update(&derived_fact_hash);
            hasher.update(&effective_root);
            hasher.update(&policy_commitment);
            hasher.update(&[authorized as u8]);
            proof_bytes.extend_from_slice(hasher.finalize().as_bytes());

            Ok(Sp1Proof {
                proof_bytes,
                public_values: vec![derived_fact_hash, effective_root, policy_commitment],
                program_type: Sp1ProgramType::DatalogEvaluation,
                proof_mode: Sp1ProofMode::Core,
            })
        }
    }

    /// Verify a Datalog evaluation proof.
    ///
    /// The verifier provides:
    /// - `expected_state_root`: The committed state they trust
    /// - `expected_policy_commitment`: Hash of an approved policy (from their registry)
    /// - `expected_query_hash`: Hash of the query fact (to confirm what was asked)
    ///
    /// Returns Ok(true) if the proof is valid and the query was derivable.
    pub fn verify_datalog_evaluation(
        proof: &Sp1Proof,
        expected_state_root: &[u8; 32],
        expected_policy_commitment: &[u8; 32],
        expected_query_hash: &[u8; 32],
    ) -> Result<bool, String> {
        if proof.program_type != Sp1ProgramType::DatalogEvaluation {
            return Err("wrong program type for datalog evaluation verification".into());
        }
        if proof.public_values.len() < 3 {
            return Err("insufficient public values for datalog evaluation proof".into());
        }

        // public_values[0] = derived_fact_hash (the query hash)
        // public_values[1] = effective_state_root
        // public_values[2] = policy_commitment
        if &proof.public_values[0] != expected_query_hash {
            return Ok(false);
        }
        if &proof.public_values[1] != expected_state_root {
            return Ok(false);
        }
        if &proof.public_values[2] != expected_policy_commitment {
            return Ok(false);
        }

        #[cfg(feature = "sp1")]
        {
            return Err("SP1 datalog evaluation ELF not yet compiled. \
                 Run `cd circuit/sp1-guest && cargo prove build` first."
                .into());
        }

        #[cfg(not(feature = "sp1"))]
        {
            // Stub verification: check structural validity.
            if proof.proof_bytes.len() < 14 {
                return Err("proof too short".into());
            }
            if &proof.proof_bytes[..4] != b"SP1V" {
                return Err("invalid proof magic".into());
            }
            if proof.proof_bytes[4] != 2 {
                return Err("unsupported proof version for datalog evaluation".into());
            }
            if &proof.proof_bytes[5..9] != b"DLOG" {
                return Err("invalid datalog evaluation marker".into());
            }
            // proof_bytes[9] is the authorized flag.
            let authorized = proof.proof_bytes[9] != 0;
            Ok(authorized)
        }
    }

    /// Extract the authorization result from a verified datalog evaluation proof.
    ///
    /// After `verify_datalog_evaluation` returns Ok(true/false), this gives additional
    /// detail about what was proven.
    pub fn datalog_evaluation_output(proof: &Sp1Proof) -> Result<Sp1DatalogOutput, String> {
        if proof.program_type != Sp1ProgramType::DatalogEvaluation {
            return Err("wrong program type".into());
        }
        if proof.public_values.len() < 3 {
            return Err("insufficient public values".into());
        }
        if proof.proof_bytes.len() < 10 {
            return Err("proof too short to extract output".into());
        }

        let authorized = proof.proof_bytes[9] != 0;

        Ok(Sp1DatalogOutput {
            authorized,
            derived_fact_hash: proof.public_values[0],
            state_root: proof.public_values[1],
            policy_commitment: proof.public_values[2],
        })
    }
}

// ============================================================================
// Host-side Datalog evaluation (mirrors guest logic for stub validation)
// ============================================================================

/// Hash a fact (must match the guest program's hash_fact function).
fn hash_fact_host(fact: &Sp1Fact) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"pyana-fact-v1:");
    hasher.update(&fact.predicate.to_le_bytes());
    hasher.update(&(fact.terms.len() as u32).to_le_bytes());
    for term in &fact.terms {
        hasher.update(&term.to_le_bytes());
    }
    *hasher.finalize().as_bytes()
}

/// Verify a Merkle proof for a fact (must match guest logic).
fn verify_fact_merkle_proof(
    fact: &Sp1Fact,
    proof: &Sp1MerkleProof,
    expected_root: &[u8; 32],
) -> bool {
    if proof.siblings.len() != proof.positions.len() {
        return false;
    }
    if proof.siblings.is_empty() {
        return &hash_fact_host(fact) == expected_root;
    }

    let mut current = hash_fact_host(fact);

    for (level_sibs, &pos) in proof.siblings.iter().zip(proof.positions.iter()) {
        if pos > 3 {
            return false;
        }
        let mut children = [[0u8; 32]; 4];
        let mut sib_idx = 0;
        for i in 0..4u8 {
            if i == pos {
                children[i as usize] = current;
            } else {
                children[i as usize] = level_sibs[sib_idx];
                sib_idx += 1;
            }
        }

        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-merkle-4ary:");
        for child in &children {
            hasher.update(child);
        }
        current = *hasher.finalize().as_bytes();
    }

    current == *expected_root
}

/// Process attenuation steps on the host side (same logic as guest).
fn process_attenuation_host(
    steps: &[Sp1AttenuationStep],
    initial_root: &[u8; 32],
) -> Result<[u8; 32], String> {
    if steps.is_empty() {
        return Ok(*initial_root);
    }

    let mut current_root = *initial_root;

    for (step_idx, step) in steps.iter().enumerate() {
        for (fact_idx, (fact, proof)) in step
            .removed_facts
            .iter()
            .zip(step.removal_proofs.iter())
            .enumerate()
        {
            if !verify_fact_merkle_proof(fact, proof, &current_root) {
                return Err(format!(
                    "attenuation step {}: Merkle proof failed for removal fact {} (predicate {})",
                    step_idx, fact_idx, fact.predicate
                ));
            }
        }

        // Compute new root after removals (same as guest).
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-attenuate-v1:");
        hasher.update(&current_root);
        hasher.update(&(step.removed_facts.len() as u32).to_le_bytes());
        for fact in &step.removed_facts {
            hasher.update(&hash_fact_host(fact));
        }
        current_root = *hasher.finalize().as_bytes();
    }

    Ok(current_root)
}

/// Compute policy commitment on the host side (same as guest).
fn compute_policy_commitment_host(rules: &[Sp1Rule]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"pyana-policy-v1:");
    hasher.update(&(rules.len() as u32).to_le_bytes());

    for rule in rules {
        hasher.update(&rule.head.predicate.to_le_bytes());
        hasher.update(&(rule.head.terms.len() as u32).to_le_bytes());
        for term in &rule.head.terms {
            hash_sp1_term_into(&mut hasher, term);
        }

        hasher.update(&(rule.body.len() as u32).to_le_bytes());
        for atom in &rule.body {
            hasher.update(&atom.predicate.to_le_bytes());
            hasher.update(&(atom.terms.len() as u32).to_le_bytes());
            for term in &atom.terms {
                hash_sp1_term_into(&mut hasher, term);
            }
        }

        hasher.update(&(rule.constraints.len() as u32).to_le_bytes());
        for constraint in &rule.constraints {
            hash_sp1_constraint_into(&mut hasher, constraint);
        }

        hasher.update(&rule.stratum.to_le_bytes());
    }

    *hasher.finalize().as_bytes()
}

fn hash_sp1_term_into(hasher: &mut blake3::Hasher, term: &Sp1Term) {
    match term {
        Sp1Term::Const(c) => {
            hasher.update(&[0u8]);
            hasher.update(&c.to_le_bytes());
        }
        Sp1Term::Var(v) => {
            hasher.update(&[1u8]);
            hasher.update(&v.to_le_bytes());
        }
        Sp1Term::Wildcard => {
            hasher.update(&[2u8]);
        }
    }
}

fn hash_sp1_constraint_into(hasher: &mut blake3::Hasher, constraint: &Sp1BuiltinConstraint) {
    match constraint {
        Sp1BuiltinConstraint::Gte { a, b } => {
            hasher.update(&[1u8]);
            hash_sp1_term_into(hasher, a);
            hash_sp1_term_into(hasher, b);
        }
        Sp1BuiltinConstraint::Gt { a, b } => {
            hasher.update(&[2u8]);
            hash_sp1_term_into(hasher, a);
            hash_sp1_term_into(hasher, b);
        }
        Sp1BuiltinConstraint::Eq { a, b } => {
            hasher.update(&[3u8]);
            hash_sp1_term_into(hasher, a);
            hash_sp1_term_into(hasher, b);
        }
        Sp1BuiltinConstraint::Neq { a, b } => {
            hasher.update(&[4u8]);
            hash_sp1_term_into(hasher, a);
            hash_sp1_term_into(hasher, b);
        }
        Sp1BuiltinConstraint::Add { a, b, result } => {
            hasher.update(&[5u8]);
            hash_sp1_term_into(hasher, a);
            hash_sp1_term_into(hasher, b);
            hash_sp1_term_into(hasher, result);
        }
        Sp1BuiltinConstraint::Mul { a, b, result } => {
            hasher.update(&[6u8]);
            hash_sp1_term_into(hasher, a);
            hash_sp1_term_into(hasher, b);
            hash_sp1_term_into(hasher, result);
        }
        Sp1BuiltinConstraint::WithinDuration {
            timestamp,
            duration_secs,
        } => {
            hasher.update(&[7u8]);
            hash_sp1_term_into(hasher, timestamp);
            hasher.update(&duration_secs.to_le_bytes());
        }
        Sp1BuiltinConstraint::InSet { term, set } => {
            hasher.update(&[8u8]);
            hash_sp1_term_into(hasher, term);
            hasher.update(&(set.len() as u32).to_le_bytes());
            for v in set {
                hasher.update(&v.to_le_bytes());
            }
        }
    }
}

/// Run the Datalog evaluation locally on the host (for stub proofs).
///
/// This mirrors the guest program's logic exactly: stratified forward-chaining
/// evaluation with built-in constraint checking.
fn evaluate_datalog_locally(input: &Sp1DatalogInput) -> bool {
    let mut facts: Vec<Sp1Fact> = input.initial_facts.clone();

    // Build attribute lookup.
    let attributes = &input.attribute_values;

    // Determine max stratum.
    let max_stratum = input.rules.iter().map(|r| r.stratum).max().unwrap_or(0);

    for stratum in 0..=max_stratum {
        let stratum_rules: Vec<&Sp1Rule> = input
            .rules
            .iter()
            .filter(|r| r.stratum == stratum)
            .collect();
        if stratum_rules.is_empty() {
            continue;
        }

        let mut iterations = 0u32;
        loop {
            let mut new_facts = Vec::new();

            for rule in &stratum_rules {
                let derived = apply_rule_host(rule, &facts, attributes, input.current_time);
                for fact in derived {
                    if !facts.contains(&fact) && !new_facts.contains(&fact) {
                        new_facts.push(fact);
                    }
                }
            }

            if new_facts.is_empty() {
                break;
            }

            facts.extend(new_facts);
            iterations += 1;
            if iterations > 1000 {
                break;
            }
        }
    }

    facts.contains(&input.query)
}

/// Apply a single rule against the fact database (host-side, mirrors guest logic).
fn apply_rule_host(
    rule: &Sp1Rule,
    facts: &[Sp1Fact],
    attributes: &[(u64, u64)],
    current_time: u64,
) -> Vec<Sp1Fact> {
    let mut derived = Vec::new();
    let num_vars = count_vars_in_sp1_rule(rule);

    if rule.body.is_empty() {
        let sub = HostSubstitution::new(num_vars);
        if evaluate_constraints_host(&rule.constraints, &sub, attributes, current_time) {
            if let Some(fact) = instantiate_head_host(&rule.head, &sub) {
                if !facts.contains(&fact) {
                    derived.push(fact);
                }
            }
        }
        return derived;
    }

    // Nested loop join over body atoms.
    let initial_sub = HostSubstitution::new(num_vars);
    let mut subs = vec![initial_sub];

    for body_atom in &rule.body {
        let mut next_subs = Vec::new();
        for sub in &subs {
            for fact in facts {
                if let Some(new_sub) = unify_atom_host(body_atom, fact, sub) {
                    next_subs.push(new_sub);
                }
            }
        }
        subs = next_subs;
        if subs.is_empty() {
            break;
        }
    }

    for sub in &subs {
        if evaluate_constraints_host(&rule.constraints, sub, attributes, current_time) {
            if let Some(fact) = instantiate_head_host(&rule.head, sub) {
                if !facts.contains(&fact) && !derived.contains(&fact) {
                    derived.push(fact);
                }
            }
        }
    }

    derived
}

/// Host-side substitution (mirrors guest Substitution).
#[derive(Clone, Debug)]
struct HostSubstitution {
    bindings: Vec<Option<u64>>,
}

impl HostSubstitution {
    fn new(num_vars: usize) -> Self {
        Self {
            bindings: vec![None; num_vars],
        }
    }

    fn bind(&mut self, var: u32, value: u64) -> bool {
        let idx = var as usize;
        if idx >= self.bindings.len() {
            return false;
        }
        match self.bindings[idx] {
            None => {
                self.bindings[idx] = Some(value);
                true
            }
            Some(existing) => existing == value,
        }
    }

    fn get(&self, var: u32) -> Option<u64> {
        self.bindings.get(var as usize).copied().flatten()
    }

    fn resolve_term(&self, term: &Sp1Term) -> Option<u64> {
        match term {
            Sp1Term::Const(c) => Some(*c),
            Sp1Term::Var(v) => self.get(*v),
            Sp1Term::Wildcard => None,
        }
    }
}

fn unify_atom_host(
    atom: &Sp1Atom,
    fact: &Sp1Fact,
    sub: &HostSubstitution,
) -> Option<HostSubstitution> {
    if atom.predicate != fact.predicate {
        return None;
    }
    if atom.terms.len() != fact.terms.len() {
        return None;
    }

    let mut new_sub = sub.clone();
    for (term, &value) in atom.terms.iter().zip(fact.terms.iter()) {
        match term {
            Sp1Term::Const(c) => {
                if *c != value {
                    return None;
                }
            }
            Sp1Term::Var(v) => {
                if !new_sub.bind(*v, value) {
                    return None;
                }
            }
            Sp1Term::Wildcard => {}
        }
    }
    Some(new_sub)
}

fn instantiate_head_host(head: &Sp1Atom, sub: &HostSubstitution) -> Option<Sp1Fact> {
    let mut terms = Vec::with_capacity(head.terms.len());
    for term in &head.terms {
        match term {
            Sp1Term::Const(c) => terms.push(*c),
            Sp1Term::Var(v) => terms.push(sub.get(*v)?),
            Sp1Term::Wildcard => return None,
        }
    }
    Some(Sp1Fact {
        predicate: head.predicate,
        terms,
    })
}

fn evaluate_constraints_host(
    constraints: &[Sp1BuiltinConstraint],
    sub: &HostSubstitution,
    attributes: &[(u64, u64)],
    current_time: u64,
) -> bool {
    for constraint in constraints {
        if !evaluate_single_constraint_host(constraint, sub, attributes, current_time) {
            return false;
        }
    }
    true
}

fn resolve_term_with_attrs(
    term: &Sp1Term,
    sub: &HostSubstitution,
    attributes: &[(u64, u64)],
) -> Option<u64> {
    match term {
        Sp1Term::Const(c) => {
            if *c >= (1u64 << 60) {
                let attr_id = *c & ((1u64 << 60) - 1);
                attributes
                    .iter()
                    .find(|(id, _)| *id == attr_id)
                    .map(|(_, v)| *v)
            } else {
                Some(*c)
            }
        }
        Sp1Term::Var(v) => sub.get(*v),
        Sp1Term::Wildcard => None,
    }
}

fn evaluate_single_constraint_host(
    constraint: &Sp1BuiltinConstraint,
    sub: &HostSubstitution,
    attributes: &[(u64, u64)],
    current_time: u64,
) -> bool {
    match constraint {
        Sp1BuiltinConstraint::Gte { a, b } => {
            match (
                resolve_term_with_attrs(a, sub, attributes),
                resolve_term_with_attrs(b, sub, attributes),
            ) {
                (Some(va), Some(vb)) => va >= vb,
                _ => false,
            }
        }
        Sp1BuiltinConstraint::Gt { a, b } => {
            match (
                resolve_term_with_attrs(a, sub, attributes),
                resolve_term_with_attrs(b, sub, attributes),
            ) {
                (Some(va), Some(vb)) => va > vb,
                _ => false,
            }
        }
        Sp1BuiltinConstraint::Eq { a, b } => {
            match (
                resolve_term_with_attrs(a, sub, attributes),
                resolve_term_with_attrs(b, sub, attributes),
            ) {
                (Some(va), Some(vb)) => va == vb,
                _ => false,
            }
        }
        Sp1BuiltinConstraint::Neq { a, b } => {
            match (
                resolve_term_with_attrs(a, sub, attributes),
                resolve_term_with_attrs(b, sub, attributes),
            ) {
                (Some(va), Some(vb)) => va != vb,
                _ => false,
            }
        }
        Sp1BuiltinConstraint::Add { a, b, result } => {
            match (
                resolve_term_with_attrs(a, sub, attributes),
                resolve_term_with_attrs(b, sub, attributes),
                resolve_term_with_attrs(result, sub, attributes),
            ) {
                (Some(va), Some(vb), Some(vr)) => va.wrapping_add(vb) == vr,
                _ => false,
            }
        }
        Sp1BuiltinConstraint::Mul { a, b, result } => {
            match (
                resolve_term_with_attrs(a, sub, attributes),
                resolve_term_with_attrs(b, sub, attributes),
                resolve_term_with_attrs(result, sub, attributes),
            ) {
                (Some(va), Some(vb), Some(vr)) => va.wrapping_mul(vb) == vr,
                _ => false,
            }
        }
        Sp1BuiltinConstraint::WithinDuration {
            timestamp,
            duration_secs,
        } => match resolve_term_with_attrs(timestamp, sub, attributes) {
            Some(ts) => {
                let earliest = current_time.saturating_sub(*duration_secs);
                ts >= earliest && ts <= current_time
            }
            None => false,
        },
        Sp1BuiltinConstraint::InSet { term, set } => {
            match resolve_term_with_attrs(term, sub, attributes) {
                Some(v) => set.binary_search(&v).is_ok(),
                None => false,
            }
        }
    }
}

fn count_vars_in_sp1_rule(rule: &Sp1Rule) -> usize {
    let mut max_var: u32 = 0;
    let mut has_vars = false;

    let check_term = |term: &Sp1Term, max: &mut u32, found: &mut bool| {
        if let Sp1Term::Var(v) = term {
            *found = true;
            if *v > *max {
                *max = *v;
            }
        }
    };

    for term in &rule.head.terms {
        check_term(term, &mut max_var, &mut has_vars);
    }
    for atom in &rule.body {
        for term in &atom.terms {
            check_term(term, &mut max_var, &mut has_vars);
        }
    }
    for constraint in &rule.constraints {
        match constraint {
            Sp1BuiltinConstraint::Gte { a, b }
            | Sp1BuiltinConstraint::Gt { a, b }
            | Sp1BuiltinConstraint::Eq { a, b }
            | Sp1BuiltinConstraint::Neq { a, b } => {
                check_term(a, &mut max_var, &mut has_vars);
                check_term(b, &mut max_var, &mut has_vars);
            }
            Sp1BuiltinConstraint::Add { a, b, result }
            | Sp1BuiltinConstraint::Mul { a, b, result } => {
                check_term(a, &mut max_var, &mut has_vars);
                check_term(b, &mut max_var, &mut has_vars);
                check_term(result, &mut max_var, &mut has_vars);
            }
            Sp1BuiltinConstraint::WithinDuration { timestamp, .. } => {
                check_term(timestamp, &mut max_var, &mut has_vars);
            }
            Sp1BuiltinConstraint::InSet { term, .. } => {
                check_term(term, &mut max_var, &mut has_vars);
            }
        }
    }

    if has_vars { (max_var + 1) as usize } else { 0 }
}

// ============================================================================
// Extended trait implementations (DerivationBackend, PredicateBackend, etc.)
// ============================================================================

use super::{
    AccumulatorBackend, AccumulatorInput, CompoundPredicateInput, CrossStateBackend,
    CrossStateCombiningRule, CrossStateOutput, CrossStateSource, DerivationBackend,
    DerivationInput, DerivationOutput, FieldElement, IvcBackend, IvcFoldStep, IvcOutput,
    PredicateBackend, PredicateInput, PredicateKind, PresentationBackend, PresentationInput,
    PresentationOutput, RelationalPredicateInput, TemporalPredicateInput, TemporalPredicateOutput,
};

// -- Helper: convert a FieldElement (u64) to a [u8; 32] for internal use --

fn field_to_bytes(f: FieldElement) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[..8].copy_from_slice(&f.to_le_bytes());
    out
}

fn bytes_to_field(b: &[u8; 32]) -> FieldElement {
    let mut buf = [0u8; 8];
    buf.copy_from_slice(&b[..8]);
    u64::from_le_bytes(buf)
}

// ============================================================================
// DerivationBackend
// ============================================================================

impl DerivationBackend for Sp1Backend {
    type DerivationProof = Sp1Proof;

    fn prove_derivation(input: &DerivationInput) -> Result<Self::DerivationProof, String> {
        // Map the abstract DerivationInput to our Sp1DatalogInput.
        // The derivation proves: rule R applied to body facts under state_root
        // yields derived_fact under substitution sigma.

        // Build body facts from hashes (we don't know the full facts, but we can
        // construct synthetic facts whose hashes match for Merkle verification).
        let body_fact_hashes_bytes: Vec<[u8; 32]> = input
            .body_fact_hashes
            .iter()
            .map(|h| field_to_bytes(*h))
            .collect();

        let state_root_bytes = field_to_bytes(input.state_root);

        // Build the head terms.
        let head_terms: Vec<u64> = input.derived_terms.iter().copied().collect();

        let sp1_input = Sp1DerivationInput {
            rule_id: input.rule_id,
            body_fact_hashes: body_fact_hashes_bytes,
            state_root: state_root_bytes,
            substitution: input.substitution.clone(),
            head_predicate: input.derived_predicate,
            head_terms,
        };

        let proof = Sp1Backend::prove_derivation(&sp1_input)?;

        Ok(proof)
    }

    fn verify_derivation(proof: &Self::DerivationProof) -> Result<DerivationOutput, String> {
        if proof.program_type != Sp1ProgramType::Derivation {
            return Err("wrong program type for derivation verification".into());
        }
        if proof.public_values.len() < 2 {
            return Err("insufficient public values for derivation proof".into());
        }

        Ok(DerivationOutput {
            derived_fact_hash: bytes_to_field(&proof.public_values[1]),
            state_root: bytes_to_field(&proof.public_values[0]),
        })
    }
}

// ============================================================================
// PredicateBackend
// ============================================================================

impl PredicateBackend for Sp1Backend {
    type PredicateProof = Sp1Proof;
    type TemporalProof = Sp1Proof;
    type CompoundProof = Sp1Proof;
    type RelationalProof = Sp1Proof;

    fn prove_predicate(input: &PredicateInput) -> Result<Self::PredicateProof, String> {
        // Map to a single-rule Datalog evaluation with a constraint matching the predicate.
        let constraint = match input.kind {
            PredicateKind::Gte => Sp1BuiltinConstraint::Gte {
                a: Sp1Term::Const(input.value),
                b: Sp1Term::Const(input.threshold),
            },
            PredicateKind::Lte => Sp1BuiltinConstraint::Gte {
                a: Sp1Term::Const(input.threshold),
                b: Sp1Term::Const(input.value),
            },
            PredicateKind::Gt => Sp1BuiltinConstraint::Gt {
                a: Sp1Term::Const(input.value),
                b: Sp1Term::Const(input.threshold),
            },
            PredicateKind::Lt => Sp1BuiltinConstraint::Gt {
                a: Sp1Term::Const(input.threshold),
                b: Sp1Term::Const(input.value),
            },
            PredicateKind::Neq => Sp1BuiltinConstraint::Neq {
                a: Sp1Term::Const(input.value),
                b: Sp1Term::Const(input.threshold),
            },
        };

        // Evaluate the constraint directly on host.
        let satisfied = match input.kind {
            PredicateKind::Gte => input.value >= input.threshold,
            PredicateKind::Lte => input.value <= input.threshold,
            PredicateKind::Gt => input.value > input.threshold,
            PredicateKind::Lt => input.value < input.threshold,
            PredicateKind::Neq => input.value != input.threshold,
        };

        if !satisfied {
            return Err("predicate not satisfied".into());
        }

        // Produce a stub proof that encodes the predicate check.
        let mut proof_bytes = Vec::new();
        proof_bytes.extend_from_slice(b"SP1V");
        proof_bytes.push(2);
        proof_bytes.extend_from_slice(b"PRED");
        proof_bytes.push(input.kind as u8);

        let mut hasher = blake3::Hasher::new();
        hasher.update(b"sp1-stub-predicate:");
        hasher.update(&input.value.to_le_bytes());
        hasher.update(&input.threshold.to_le_bytes());
        hasher.update(&input.value_commitment.to_le_bytes());
        hash_sp1_constraint_into(&mut hasher, &constraint);
        proof_bytes.extend_from_slice(hasher.finalize().as_bytes());

        Ok(Sp1Proof {
            proof_bytes,
            public_values: vec![
                field_to_bytes(input.threshold),
                field_to_bytes(input.value_commitment),
            ],
            program_type: Sp1ProgramType::DatalogEvaluation,
            proof_mode: Sp1ProofMode::Core,
        })
    }

    fn verify_predicate(proof: &Self::PredicateProof) -> Result<bool, String> {
        if proof.proof_bytes.len() < 10 {
            return Err("proof too short".into());
        }
        if &proof.proof_bytes[..4] != b"SP1V" {
            return Err("invalid proof magic".into());
        }
        if &proof.proof_bytes[5..9] != b"PRED" {
            return Err("invalid predicate marker".into());
        }
        Ok(true)
    }

    fn prove_temporal(input: &TemporalPredicateInput) -> Result<Self::TemporalProof, String> {
        if input.values.is_empty() {
            return Err("temporal predicate requires at least one step".into());
        }
        if input.values.len() != input.state_roots.len() {
            return Err("values and state_roots must have same length".into());
        }

        // Check predicate holds at every step.
        for value in &input.values {
            let satisfied = match input.kind {
                PredicateKind::Gte => *value >= input.threshold,
                PredicateKind::Lte => *value <= input.threshold,
                PredicateKind::Gt => *value > input.threshold,
                PredicateKind::Lt => *value < input.threshold,
                PredicateKind::Neq => *value != input.threshold,
            };
            if !satisfied {
                return Err("temporal predicate not satisfied at all steps".into());
            }
        }

        let num_steps = input.values.len() as u32;
        let initial_state_root = input.state_roots[0];
        let final_state_root = *input.state_roots.last().unwrap();

        let mut proof_bytes = Vec::new();
        proof_bytes.extend_from_slice(b"SP1V");
        proof_bytes.push(2);
        proof_bytes.extend_from_slice(b"TEMP");
        proof_bytes.extend_from_slice(&num_steps.to_le_bytes());
        proof_bytes.push(input.kind as u8);

        let mut hasher = blake3::Hasher::new();
        hasher.update(b"sp1-stub-temporal:");
        hasher.update(&num_steps.to_le_bytes());
        hasher.update(&initial_state_root.to_le_bytes());
        hasher.update(&final_state_root.to_le_bytes());
        hasher.update(&input.threshold.to_le_bytes());
        proof_bytes.extend_from_slice(hasher.finalize().as_bytes());

        Ok(Sp1Proof {
            proof_bytes,
            public_values: vec![
                field_to_bytes(initial_state_root),
                field_to_bytes(final_state_root),
                field_to_bytes(input.threshold),
            ],
            program_type: Sp1ProgramType::DatalogEvaluation,
            proof_mode: Sp1ProofMode::Core,
        })
    }

    fn verify_temporal(proof: &Self::TemporalProof) -> Result<TemporalPredicateOutput, String> {
        if proof.proof_bytes.len() < 14 {
            return Err("proof too short".into());
        }
        if &proof.proof_bytes[..4] != b"SP1V" {
            return Err("invalid proof magic".into());
        }
        if &proof.proof_bytes[5..9] != b"TEMP" {
            return Err("invalid temporal marker".into());
        }

        let num_steps = u32::from_le_bytes([
            proof.proof_bytes[9],
            proof.proof_bytes[10],
            proof.proof_bytes[11],
            proof.proof_bytes[12],
        ]);

        if proof.public_values.len() < 3 {
            return Err("insufficient public values".into());
        }

        Ok(TemporalPredicateOutput {
            num_steps,
            initial_state_root: bytes_to_field(&proof.public_values[0]),
            final_state_root: bytes_to_field(&proof.public_values[1]),
            threshold: bytes_to_field(&proof.public_values[2]),
        })
    }

    fn prove_compound(input: &CompoundPredicateInput) -> Result<Self::CompoundProof, String> {
        if input.sub_predicates.is_empty() {
            return Err("compound predicate requires at least one sub-predicate".into());
        }

        // Evaluate all sub-predicates.
        let mut results = Vec::with_capacity(input.sub_predicates.len());
        for sub in &input.sub_predicates {
            let satisfied = match sub.kind {
                PredicateKind::Gte => sub.value >= sub.threshold,
                PredicateKind::Lte => sub.value <= sub.threshold,
                PredicateKind::Gt => sub.value > sub.threshold,
                PredicateKind::Lt => sub.value < sub.threshold,
                PredicateKind::Neq => sub.value != sub.threshold,
            };
            results.push(satisfied);
        }

        // Evaluate the boolean formula over results.
        // Formula encoding: 0 = AND all, 1 = OR all, 2+ = custom expression.
        let overall = if input.formula.is_empty() || input.formula[0] == 0 {
            // Default: AND of all sub-predicates.
            results.iter().all(|r| *r)
        } else if input.formula[0] == 1 {
            // OR of all sub-predicates.
            results.iter().any(|r| *r)
        } else {
            // Treat as AND for now (extensible).
            results.iter().all(|r| *r)
        };

        if !overall {
            return Err("compound predicate not satisfied".into());
        }

        let mut proof_bytes = Vec::new();
        proof_bytes.extend_from_slice(b"SP1V");
        proof_bytes.push(2);
        proof_bytes.extend_from_slice(b"CMPD");
        proof_bytes.push(input.sub_predicates.len() as u8);

        let mut hasher = blake3::Hasher::new();
        hasher.update(b"sp1-stub-compound:");
        for (i, sub) in input.sub_predicates.iter().enumerate() {
            hasher.update(&(i as u32).to_le_bytes());
            hasher.update(&sub.value_commitment.to_le_bytes());
        }
        hasher.update(&input.formula);
        proof_bytes.extend_from_slice(hasher.finalize().as_bytes());

        Ok(Sp1Proof {
            proof_bytes,
            public_values: input
                .sub_predicates
                .iter()
                .map(|s| field_to_bytes(s.value_commitment))
                .collect(),
            program_type: Sp1ProgramType::DatalogEvaluation,
            proof_mode: Sp1ProofMode::Core,
        })
    }

    fn verify_compound(proof: &Self::CompoundProof) -> Result<bool, String> {
        if proof.proof_bytes.len() < 10 {
            return Err("proof too short".into());
        }
        if &proof.proof_bytes[..4] != b"SP1V" {
            return Err("invalid proof magic".into());
        }
        if &proof.proof_bytes[5..9] != b"CMPD" {
            return Err("invalid compound marker".into());
        }
        Ok(true)
    }

    fn prove_relational(input: &RelationalPredicateInput) -> Result<Self::RelationalProof, String> {
        // The prover knows my_value. We prove the relationship between my_value
        // and an implicit their_value committed under their_commitment.
        // In the stub, we verify structurally; the real guest would verify both
        // commitments and the relation inside the zkVM.

        // For the stub, we can only verify our own side (we don't know their value).
        // We produce a proof that commits to both commitments and the kind.

        let mut proof_bytes = Vec::new();
        proof_bytes.extend_from_slice(b"SP1V");
        proof_bytes.push(2);
        proof_bytes.extend_from_slice(b"RELN");
        proof_bytes.push(input.kind as u8);

        let mut hasher = blake3::Hasher::new();
        hasher.update(b"sp1-stub-relational:");
        hasher.update(&input.my_commitment.to_le_bytes());
        hasher.update(&input.their_commitment.to_le_bytes());
        hasher.update(&input.my_value.to_le_bytes());
        proof_bytes.extend_from_slice(hasher.finalize().as_bytes());

        Ok(Sp1Proof {
            proof_bytes,
            public_values: vec![
                field_to_bytes(input.my_commitment),
                field_to_bytes(input.their_commitment),
            ],
            program_type: Sp1ProgramType::DatalogEvaluation,
            proof_mode: Sp1ProofMode::Core,
        })
    }

    fn verify_relational(proof: &Self::RelationalProof) -> Result<bool, String> {
        if proof.proof_bytes.len() < 10 {
            return Err("proof too short".into());
        }
        if &proof.proof_bytes[..4] != b"SP1V" {
            return Err("invalid proof magic".into());
        }
        if &proof.proof_bytes[5..9] != b"RELN" {
            return Err("invalid relational marker".into());
        }
        Ok(true)
    }
}

// ============================================================================
// AccumulatorBackend
// ============================================================================

impl AccumulatorBackend for Sp1Backend {
    type AccumulatorProof = Sp1Proof;

    fn prove_non_membership(input: &AccumulatorInput) -> Result<Self::AccumulatorProof, String> {
        if input.ancestor_hashes.is_empty() {
            return Err("must have at least one ancestor hash to prove non-membership".into());
        }
        if input.ancestor_hashes.len() > 8 {
            return Err("maximum 8 ancestor hashes supported".into());
        }

        // Map to the guest's InSet constraint (inverted — proving NOT in set).
        // The guest's InSet checks membership; for non-membership, we verify that
        // evaluating the polynomial accumulator at each ancestor hash yields a
        // non-zero product.
        //
        // In the real SP1 guest, this would:
        // 1. Reconstruct the accumulator polynomial from its commitment
        // 2. Evaluate at each ancestor hash point
        // 3. Verify all evaluations are non-zero (proving non-membership)
        //
        // For the stub, we produce a structurally valid proof.

        let mut proof_bytes = Vec::new();
        proof_bytes.extend_from_slice(b"SP1V");
        proof_bytes.push(2);
        proof_bytes.extend_from_slice(b"ACCM");
        proof_bytes.push(input.ancestor_hashes.len() as u8);

        let mut hasher = blake3::Hasher::new();
        hasher.update(b"sp1-stub-accumulator:");
        for h in &input.ancestor_hashes {
            hasher.update(&h.to_le_bytes());
        }
        for a in &input.accumulator {
            hasher.update(&a.to_le_bytes());
        }
        for a in &input.alpha {
            hasher.update(&a.to_le_bytes());
        }
        proof_bytes.extend_from_slice(hasher.finalize().as_bytes());

        // Public values: accumulator + alpha (8 field elements as bytes).
        let mut pub_vals = Vec::new();
        let mut acc_bytes = [0u8; 32];
        for (i, v) in input.accumulator.iter().enumerate() {
            acc_bytes[i * 8..(i + 1) * 8].copy_from_slice(&v.to_le_bytes());
        }
        pub_vals.push(acc_bytes);

        let mut alpha_bytes = [0u8; 32];
        for (i, v) in input.alpha.iter().enumerate() {
            alpha_bytes[i * 8..(i + 1) * 8].copy_from_slice(&v.to_le_bytes());
        }
        pub_vals.push(alpha_bytes);

        Ok(Sp1Proof {
            proof_bytes,
            public_values: pub_vals,
            program_type: Sp1ProgramType::DatalogEvaluation,
            proof_mode: Sp1ProofMode::Core,
        })
    }

    fn verify_non_membership(
        proof: &Self::AccumulatorProof,
        _accumulator: &[FieldElement; 4],
        _alpha: &[FieldElement; 4],
        _num_ancestors: usize,
    ) -> Result<bool, String> {
        if proof.proof_bytes.len() < 10 {
            return Err("proof too short".into());
        }
        if &proof.proof_bytes[..4] != b"SP1V" {
            return Err("invalid proof magic".into());
        }
        if &proof.proof_bytes[5..9] != b"ACCM" {
            return Err("invalid accumulator marker".into());
        }
        Ok(true)
    }
}

// ============================================================================
// IvcBackend
// ============================================================================

impl IvcBackend for Sp1Backend {
    type IvcProof = Sp1Proof;

    fn prove_ivc(
        initial_root: FieldElement,
        steps: &[IvcFoldStep],
    ) -> Result<Self::IvcProof, String> {
        if steps.is_empty() {
            return Err("IVC must have at least one fold step".into());
        }

        // Validate chain continuity: each step's old_root must equal the prior step's new_root.
        let mut current = initial_root;
        for (i, step) in steps.iter().enumerate() {
            if step.old_root != current {
                return Err(format!(
                    "IVC chain broken at step {}: expected old_root={}, got={}",
                    i, current, step.old_root
                ));
            }
            current = step.new_root;
        }
        let final_root = current;

        // Map to the SP1 attenuation pipeline.
        // Each IvcFoldStep maps to an Sp1AttenuationStep with removal facts
        // constructed from removed_fact_hashes.
        let attenuation_steps: Vec<Sp1AttenuationStep> = steps
            .iter()
            .map(|step| {
                let removed_facts: Vec<Sp1Fact> = step
                    .removed_fact_hashes
                    .iter()
                    .enumerate()
                    .map(|(i, _h)| Sp1Fact {
                        // Synthetic fact whose hash encodes the removal.
                        predicate: 0xFFFF_FFFF_FFFF_0000 | (i as u64),
                        terms: vec![*_h],
                    })
                    .collect();
                Sp1AttenuationStep {
                    removed_facts,
                    // In the real implementation, these would be actual Merkle proofs
                    // from the state tree. The stub accepts without full verification.
                    removal_proofs: vec![],
                }
            })
            .collect();

        // Compute accumulated hash (chain history commitment).
        let accumulated_hash = {
            let mut hasher = blake3::Hasher::new();
            hasher.update(b"sp1-ivc-chain-v1:");
            hasher.update(&initial_root.to_le_bytes());
            for step in steps {
                hasher.update(&step.old_root.to_le_bytes());
                hasher.update(&step.new_root.to_le_bytes());
                hasher.update(&(step.removed_fact_hashes.len() as u32).to_le_bytes());
                for h in &step.removed_fact_hashes {
                    hasher.update(&h.to_le_bytes());
                }
            }
            let hash = *hasher.finalize().as_bytes();
            // Split into 4 u64s for the output format.
            let mut acc = [0u64; 4];
            for i in 0..4 {
                let mut buf = [0u8; 8];
                buf.copy_from_slice(&hash[i * 8..(i + 1) * 8]);
                acc[i] = u64::from_le_bytes(buf);
            }
            acc
        };

        let step_count = steps.len() as u32;
        let _ = attenuation_steps; // Used in real SP1 path.

        // Build stub proof.
        let mut proof_bytes = Vec::new();
        proof_bytes.extend_from_slice(b"SP1V");
        proof_bytes.push(2);
        proof_bytes.extend_from_slice(b"IVCP");
        proof_bytes.extend_from_slice(&step_count.to_le_bytes());
        proof_bytes.extend_from_slice(&initial_root.to_le_bytes());
        proof_bytes.extend_from_slice(&final_root.to_le_bytes());

        let mut hasher = blake3::Hasher::new();
        hasher.update(b"sp1-stub-ivc:");
        hasher.update(&initial_root.to_le_bytes());
        hasher.update(&final_root.to_le_bytes());
        hasher.update(&step_count.to_le_bytes());
        for a in &accumulated_hash {
            hasher.update(&a.to_le_bytes());
        }
        proof_bytes.extend_from_slice(hasher.finalize().as_bytes());

        // Encode accumulated_hash into public values.
        let mut acc_bytes = [0u8; 32];
        for (i, v) in accumulated_hash.iter().enumerate() {
            acc_bytes[i * 8..(i + 1) * 8].copy_from_slice(&v.to_le_bytes());
        }

        Ok(Sp1Proof {
            proof_bytes,
            public_values: vec![
                field_to_bytes(initial_root),
                field_to_bytes(final_root),
                acc_bytes,
            ],
            program_type: Sp1ProgramType::DatalogEvaluation,
            proof_mode: Sp1ProofMode::Core,
        })
    }

    fn verify_ivc(proof: &Self::IvcProof) -> Result<IvcOutput, String> {
        if proof.proof_bytes.len() < 25 {
            return Err("proof too short for IVC".into());
        }
        if &proof.proof_bytes[..4] != b"SP1V" {
            return Err("invalid proof magic".into());
        }
        if &proof.proof_bytes[5..9] != b"IVCP" {
            return Err("invalid IVC marker".into());
        }

        let step_count = u32::from_le_bytes([
            proof.proof_bytes[9],
            proof.proof_bytes[10],
            proof.proof_bytes[11],
            proof.proof_bytes[12],
        ]);

        if proof.public_values.len() < 3 {
            return Err("insufficient public values for IVC proof".into());
        }

        let initial_root = bytes_to_field(&proof.public_values[0]);
        let final_root = bytes_to_field(&proof.public_values[1]);

        // Decode accumulated_hash from the third public value.
        let acc_bytes = &proof.public_values[2];
        let mut accumulated_hash = [0u64; 4];
        for i in 0..4 {
            let mut buf = [0u8; 8];
            buf.copy_from_slice(&acc_bytes[i * 8..(i + 1) * 8]);
            accumulated_hash[i] = u64::from_le_bytes(buf);
        }

        Ok(IvcOutput {
            initial_root,
            final_root,
            step_count,
            accumulated_hash,
        })
    }

    fn max_chain_depth() -> u32 {
        // SP1 can handle long chains since it's general-purpose execution.
        // Limit by practical proving time (~30s per step in compressed mode).
        256
    }
}

// ============================================================================
// PresentationBackend
// ============================================================================

impl PresentationBackend for Sp1Backend {
    type PresentationProof = Sp1Proof;

    fn prove_presentation(input: &PresentationInput) -> Result<Self::PresentationProof, String> {
        // The presentation proof combines:
        // 1. IVC fold chain (attenuation)
        // 2. Derivation (authorization from final state)
        // 3. Issuer membership (issuer in federation)
        // 4. Presentation tag (unlinkability)
        // 5. Composition commitment

        // Map the fold steps to attenuation steps for the Datalog guest.
        let attenuation_steps: Vec<Sp1AttenuationStep> = input
            .fold_steps
            .iter()
            .map(|step| {
                let removed_facts: Vec<Sp1Fact> = step
                    .removed_fact_hashes
                    .iter()
                    .enumerate()
                    .map(|(i, h)| Sp1Fact {
                        predicate: 0xFFFF_FFFF_FFFF_0000 | (i as u64),
                        terms: vec![*h],
                    })
                    .collect();
                Sp1AttenuationStep {
                    removed_facts,
                    removal_proofs: vec![],
                }
            })
            .collect();

        // Build derivation rule from the DerivationInput.
        let derivation_rule = Sp1Rule {
            head: Sp1Atom {
                predicate: input.derivation.derived_predicate,
                terms: input
                    .derivation
                    .derived_terms
                    .iter()
                    .map(|t| Sp1Term::Const(*t))
                    .collect(),
            },
            body: input
                .derivation
                .body_fact_hashes
                .iter()
                .enumerate()
                .map(|(i, _)| Sp1Atom {
                    predicate: 0xFFFF_FFFF_FFFE_0000 | (i as u64),
                    terms: vec![Sp1Term::Var(i as u32)],
                })
                .collect(),
            constraints: vec![],
            stratum: 0,
        };

        // Build initial facts from body fact hashes.
        let initial_facts: Vec<Sp1Fact> = input
            .derivation
            .body_fact_hashes
            .iter()
            .enumerate()
            .map(|(i, h)| Sp1Fact {
                predicate: 0xFFFF_FFFF_FFFE_0000 | (i as u64),
                terms: vec![*h],
            })
            .collect();

        // Verify issuer membership in the federation.
        let issuer_leaf_bytes = field_to_bytes(input.issuer_leaf);
        let issuer_siblings_bytes: Vec<Vec<[u8; 32]>> = input
            .issuer_siblings
            .iter()
            .map(|level| level.iter().map(|s| field_to_bytes(*s)).collect())
            .collect();
        let federation_root_bytes = field_to_bytes(input.federation_root);
        let computed_fed_root = compute_merkle_root(&issuer_leaf_bytes, &issuer_siblings_bytes);
        if computed_fed_root != federation_root_bytes {
            return Err("issuer not in federation: Merkle verification failed".into());
        }

        // Compute the presentation tag (blinded, unlinkable across shows).
        let presentation_tag = {
            let mut hasher = blake3::Hasher::new();
            hasher.update(b"sp1-presentation-tag:");
            hasher.update(&input.issuer_leaf.to_le_bytes());
            hasher.update(&input.presentation_randomness.to_le_bytes());
            hasher.update(&input.blinding_factor.to_le_bytes());
            hasher.update(&input.verifier_nonce.to_le_bytes());
            let hash = *hasher.finalize().as_bytes();
            bytes_to_field(&hash)
        };

        // Compute the composition commitment (binds all sub-proofs together).
        let composition_commitment = {
            let mut hasher = blake3::Hasher::new();
            hasher.update(b"sp1-composition-v1:");
            hasher.update(&input.federation_root.to_le_bytes());
            hasher.update(&input.timestamp.to_le_bytes());
            hasher.update(&input.verifier_nonce.to_le_bytes());
            for p in &input.request_predicate {
                hasher.update(&p.to_le_bytes());
            }
            hasher.update(&presentation_tag.to_le_bytes());
            let hash = *hasher.finalize().as_bytes();
            bytes_to_field(&hash)
        };

        let _ = (attenuation_steps, derivation_rule, initial_facts);

        // Build stub proof.
        let mut proof_bytes = Vec::new();
        proof_bytes.extend_from_slice(b"SP1V");
        proof_bytes.push(2);
        proof_bytes.extend_from_slice(b"PRES");
        proof_bytes.extend_from_slice(&input.federation_root.to_le_bytes());
        proof_bytes.extend_from_slice(&input.timestamp.to_le_bytes());

        let mut hasher = blake3::Hasher::new();
        hasher.update(b"sp1-stub-presentation:");
        hasher.update(&input.federation_root.to_le_bytes());
        hasher.update(&presentation_tag.to_le_bytes());
        hasher.update(&composition_commitment.to_le_bytes());
        proof_bytes.extend_from_slice(hasher.finalize().as_bytes());

        // Encode request_predicate as a [u8; 32].
        let mut req_pred_bytes = [0u8; 32];
        for (i, v) in input.request_predicate.iter().enumerate() {
            req_pred_bytes[i * 8..(i + 1) * 8].copy_from_slice(&v.to_le_bytes());
        }

        Ok(Sp1Proof {
            proof_bytes,
            public_values: vec![
                field_to_bytes(input.federation_root),
                req_pred_bytes,
                field_to_bytes(input.timestamp),
                field_to_bytes(presentation_tag),
                field_to_bytes(input.revealed_facts_commitment),
                field_to_bytes(composition_commitment),
                field_to_bytes(input.verifier_nonce),
                field_to_bytes(input.verifier_block_height),
            ],
            program_type: Sp1ProgramType::DatalogEvaluation,
            proof_mode: Sp1ProofMode::Core,
        })
    }

    fn verify_presentation(proof: &Self::PresentationProof) -> Result<PresentationOutput, String> {
        if proof.proof_bytes.len() < 10 {
            return Err("proof too short for presentation".into());
        }
        if &proof.proof_bytes[..4] != b"SP1V" {
            return Err("invalid proof magic".into());
        }
        if &proof.proof_bytes[5..9] != b"PRES" {
            return Err("invalid presentation marker".into());
        }
        if proof.public_values.len() < 8 {
            return Err("insufficient public values for presentation proof".into());
        }

        let federation_root = bytes_to_field(&proof.public_values[0]);

        // Decode request_predicate from bytes.
        let req_bytes = &proof.public_values[1];
        let mut request_predicate = [0u64; 4];
        for i in 0..4 {
            let mut buf = [0u8; 8];
            buf.copy_from_slice(&req_bytes[i * 8..(i + 1) * 8]);
            request_predicate[i] = u64::from_le_bytes(buf);
        }

        let timestamp = bytes_to_field(&proof.public_values[2]);
        let presentation_tag = bytes_to_field(&proof.public_values[3]);
        let revealed_facts_commitment = bytes_to_field(&proof.public_values[4]);
        let composition_commitment = bytes_to_field(&proof.public_values[5]);
        let verifier_nonce = bytes_to_field(&proof.public_values[6]);
        let verifier_block_height = bytes_to_field(&proof.public_values[7]);

        Ok(PresentationOutput {
            federation_root,
            request_predicate,
            timestamp,
            presentation_tag,
            revealed_facts_commitment,
            composition_commitment,
            verifier_nonce,
            verifier_block_height,
        })
    }

    fn presentation_proof_size(proof: &Self::PresentationProof) -> usize {
        proof.proof_bytes.len() + proof.public_values.len() * 32
    }
}

// ============================================================================
// CrossStateBackend
// ============================================================================

impl CrossStateBackend for Sp1Backend {
    type CrossStateProof = Sp1Proof;

    fn prove_cross_state(
        sources: &[CrossStateSource],
        combining_rule: &CrossStateCombiningRule,
    ) -> Result<Self::CrossStateProof, String> {
        if sources.is_empty() {
            return Err("cross-state derivation requires at least one source".into());
        }

        // Each source produces an independent derivation under its own state root.
        // We compose them into a single proof via the SP1 Datalog evaluator's
        // multi-root capability.

        // Compute intermediate derived fact hashes (one per source).
        let mut intermediate_hashes: Vec<[u8; 32]> = Vec::with_capacity(sources.len());
        for source in sources {
            let derived_fact_hash = {
                let mut hasher = blake3::Hasher::new();
                hasher.update(b"sp1-derived-fact:");
                hasher.update(&source.derivation.derived_predicate.to_le_bytes());
                for term in &source.derivation.derived_terms {
                    hasher.update(&term.to_le_bytes());
                }
                *hasher.finalize().as_bytes()
            };
            intermediate_hashes.push(derived_fact_hash);
        }

        // Build composition root: Poseidon2 tree of intermediate derived facts.
        // (Using blake3 in the stub, matching guest behavior.)
        let composition_root = {
            let mut hasher = blake3::Hasher::new();
            hasher.update(b"sp1-composition-tree:");
            hasher.update(&(intermediate_hashes.len() as u32).to_le_bytes());
            for h in &intermediate_hashes {
                hasher.update(h);
            }
            let hash = *hasher.finalize().as_bytes();
            bytes_to_field(&hash)
        };

        // Compute the final derived fact hash from the combining rule.
        let final_derived_hash = {
            let mut hasher = blake3::Hasher::new();
            hasher.update(b"sp1-derived-fact:");
            hasher.update(&combining_rule.head_predicate.to_le_bytes());
            for term in &combining_rule.derived_terms {
                hasher.update(&term.to_le_bytes());
            }
            bytes_to_field(hasher.finalize().as_bytes())
        };

        let source_roots: Vec<FieldElement> = sources.iter().map(|s| s.source_root).collect();

        // Build stub proof.
        let mut proof_bytes = Vec::new();
        proof_bytes.extend_from_slice(b"SP1V");
        proof_bytes.push(2);
        proof_bytes.extend_from_slice(b"XSTT");
        proof_bytes.push(sources.len() as u8);
        proof_bytes.extend_from_slice(&combining_rule.rule_id.to_le_bytes());

        let mut hasher = blake3::Hasher::new();
        hasher.update(b"sp1-stub-cross-state:");
        hasher.update(&composition_root.to_le_bytes());
        hasher.update(&final_derived_hash.to_le_bytes());
        for r in &source_roots {
            hasher.update(&r.to_le_bytes());
        }
        proof_bytes.extend_from_slice(hasher.finalize().as_bytes());

        // Public values: composition_root, final_derived_hash, then source roots.
        let mut pub_vals = vec![
            field_to_bytes(composition_root),
            field_to_bytes(final_derived_hash),
        ];
        // Pack source roots: up to 4 per [u8; 32] (each is u64 = 8 bytes).
        for root in &source_roots {
            pub_vals.push(field_to_bytes(*root));
        }

        Ok(Sp1Proof {
            proof_bytes,
            public_values: pub_vals,
            program_type: Sp1ProgramType::DatalogEvaluation,
            proof_mode: Sp1ProofMode::Core,
        })
    }

    fn verify_cross_state(proof: &Self::CrossStateProof) -> Result<CrossStateOutput, String> {
        if proof.proof_bytes.len() < 10 {
            return Err("proof too short for cross-state".into());
        }
        if &proof.proof_bytes[..4] != b"SP1V" {
            return Err("invalid proof magic".into());
        }
        if &proof.proof_bytes[5..9] != b"XSTT" {
            return Err("invalid cross-state marker".into());
        }

        let num_sources = proof.proof_bytes[9] as usize;

        if proof.public_values.len() < 2 + num_sources {
            return Err("insufficient public values for cross-state proof".into());
        }

        let composition_root = bytes_to_field(&proof.public_values[0]);
        let final_derived_hash = bytes_to_field(&proof.public_values[1]);
        let source_roots: Vec<FieldElement> = proof.public_values[2..2 + num_sources]
            .iter()
            .map(|b| bytes_to_field(b))
            .collect();

        Ok(CrossStateOutput {
            composition_root,
            source_roots,
            final_derived_hash,
        })
    }
}

// ============================================================================
// FullProofBackend marker
// ============================================================================

impl super::FullProofBackend for Sp1Backend {}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sp1_backend_name() {
        assert_eq!(Sp1Backend::backend_name(), "sp1-risc-v-zkvm");
    }

    #[test]
    fn sp1_prove_and_verify_membership_stub() {
        let leaf = [0x42u8; 32];
        let sibling_0 = vec![[0x01u8; 32], [0x02u8; 32], [0x03u8; 32]];
        let sibling_1 = vec![[0x04u8; 32], [0x05u8; 32], [0x06u8; 32]];
        let siblings = vec![sibling_0, sibling_1];

        let root = compute_merkle_root(&leaf, &siblings);

        let proof = Sp1Backend::prove_membership(&leaf, &siblings, &root).unwrap();
        assert_eq!(proof.program_type, Sp1ProgramType::Membership);
        assert_eq!(proof.public_values.len(), 2);
        assert_eq!(proof.public_values[0], leaf);
        assert_eq!(proof.public_values[1], root);

        let valid = Sp1Backend::verify_membership(&proof, &root).unwrap();
        assert!(valid);
    }

    #[test]
    fn sp1_verify_wrong_root_fails() {
        let leaf = [0x42u8; 32];
        let siblings = vec![vec![[0x01u8; 32], [0x02u8; 32], [0x03u8; 32]]];
        let root = compute_merkle_root(&leaf, &siblings);

        let proof = Sp1Backend::prove_membership(&leaf, &siblings, &root).unwrap();

        let wrong_root = [0xFFu8; 32];
        let valid = Sp1Backend::verify_membership(&proof, &wrong_root).unwrap();
        assert!(!valid);
    }

    #[test]
    fn sp1_invalid_witness_rejected() {
        let leaf = [0x42u8; 32];
        let siblings = vec![vec![[0x01u8; 32]]];
        let wrong_root = [0xAAu8; 32];

        let result = Sp1Backend::prove_membership(&leaf, &siblings, &wrong_root);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Invalid witness"));
    }

    #[test]
    fn sp1_prove_and_verify_fold_stub() {
        let old_root = [0x10u8; 32];
        let new_root = [0x20u8; 32];
        let removals = vec![[0xAAu8; 32], [0xBBu8; 32]];

        let proof = Sp1Backend::prove_fold_step(&old_root, &new_root, &removals).unwrap();
        assert_eq!(proof.program_type, Sp1ProgramType::FoldStep);
        assert_eq!(proof.public_values.len(), 3);

        let valid = Sp1Backend::verify_fold(&proof).unwrap();
        assert!(valid);
    }

    #[test]
    fn sp1_fold_empty_removals_rejected() {
        let old_root = [0x10u8; 32];
        let new_root = [0x20u8; 32];

        let result = Sp1Backend::prove_fold_step(&old_root, &new_root, &[]);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("at least one fact"));
    }

    #[test]
    fn sp1_prove_and_verify_derivation_stub() {
        let input = Sp1DerivationInput {
            rule_id: 1,
            body_fact_hashes: vec![[0xAA; 32], [0xBB; 32]],
            state_root: [0x11; 32],
            substitution: vec![42, 100],
            head_predicate: 7,
            head_terms: vec![42, 100, 200],
        };

        let proof = Sp1Backend::prove_derivation(&input).unwrap();
        assert_eq!(proof.program_type, Sp1ProgramType::Derivation);
        assert_eq!(proof.public_values.len(), 2);
        assert_eq!(proof.public_values[0], input.state_root);

        // Derive the expected hash the same way.
        let expected_hash = {
            let mut hasher = blake3::Hasher::new();
            hasher.update(b"sp1-derived-fact:");
            hasher.update(&7u64.to_le_bytes());
            for term in &[42u64, 100, 200] {
                hasher.update(&term.to_le_bytes());
            }
            *hasher.finalize().as_bytes()
        };

        let valid =
            Sp1Backend::verify_derivation(&proof, &input.state_root, &expected_hash).unwrap();
        assert!(valid);
    }

    #[test]
    fn sp1_derivation_no_body_facts_rejected() {
        let input = Sp1DerivationInput {
            rule_id: 1,
            body_fact_hashes: vec![],
            state_root: [0x11; 32],
            substitution: vec![42],
            head_predicate: 7,
            head_terms: vec![42],
        };

        let result = Sp1Backend::prove_derivation(&input);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("at least one body fact"));
    }

    #[test]
    fn sp1_proof_size_compact() {
        let leaf = [0x42u8; 32];
        let siblings = vec![
            vec![[1u8; 32], [2u8; 32], [3u8; 32]],
            vec![[4u8; 32], [5u8; 32], [6u8; 32]],
        ];
        let root = compute_merkle_root(&leaf, &siblings);

        let proof = Sp1Backend::prove_membership(&leaf, &siblings, &root).unwrap();
        let size = Sp1Backend::proof_size(&proof);

        // Stub proofs are small; real SP1 compressed proofs are ~50-100 KB.
        assert!(
            size < 1_000,
            "stub proof should be compact, got {size} bytes"
        );
    }

    // =========================================================================
    // Caveat discharge tests
    // =========================================================================

    /// Helper: build a valid caveat discharge input with proper HMAC chain and Merkle tree.
    fn make_discharge_input(caveats: Vec<Sp1WireCaveat>) -> Sp1CaveatDischargeInput {
        let root_key = [0x42u8; 32];
        let nonce_bytes = b"test-token-nonce-001".to_vec();

        // Compute HMAC chain tail.
        let mut current_tail = hmac_sha256_host(&root_key, &nonce_bytes);
        for caveat in &caveats {
            let encoded = caveat.encode();
            current_tail = hmac_sha256_host(&current_tail, &encoded);
        }

        // Compute the token ID hash (leaf).
        let token_id_hash = {
            let mut hasher = blake3::Hasher::new();
            hasher.update(b"pyana-token-id:");
            hasher.update(&nonce_bytes);
            *hasher.finalize().as_bytes()
        };

        // Build a 2-level 4-ary Merkle tree around the token_id_hash.
        let sibs_0 = [[0x01u8; 32], [0x02u8; 32], [0x03u8; 32]];
        let level_0_hash = merkle_hash(&token_id_hash, &sibs_0);
        let sibs_1 = [[0x04u8; 32], [0x05u8; 32], [0x06u8; 32]];
        let state_root = merkle_hash(&level_0_hash, &sibs_1);

        let context = Sp1AuthContext {
            current_time: 1700000000,
            resource_id: 42,
            action_mask: 0b0011, // read + write
            usage_count: 5,
            source_ip: 0xC0A80001, // 192.168.0.1
            attributes: vec![(1, 500), (2, 1000)],
        };

        Sp1CaveatDischargeInput {
            root_key,
            nonce_bytes,
            caveats,
            expected_tail: current_tail,
            context,
            merkle_siblings: vec![sibs_0, sibs_1],
            state_root,
        }
    }

    #[test]
    fn sp1_caveat_discharge_no_caveats() {
        // A macaroon with no caveats — just HMAC chain + Merkle membership.
        let input = make_discharge_input(vec![]);
        let proof = Sp1Backend::prove_caveat_discharge(&input).unwrap();

        assert_eq!(proof.program_type, Sp1ProgramType::CaveatDischarge);
        assert_eq!(proof.public_values.len(), 3);

        let context_hash = compute_context_hash_host(&input.context);
        let valid =
            Sp1Backend::verify_caveat_discharge(&proof, &input.state_root, &context_hash).unwrap();
        assert!(valid);
    }

    #[test]
    fn sp1_caveat_discharge_with_expiry() {
        // ExpiresAt caveat: token expires at t=1800000000, context time is 1700000000.
        let expires_caveat = Sp1WireCaveat {
            caveat_type: caveat_types::EXPIRES_AT,
            body: 1800000000u64.to_le_bytes().to_vec(),
        };

        let input = make_discharge_input(vec![expires_caveat]);
        let proof = Sp1Backend::prove_caveat_discharge(&input).unwrap();

        let context_hash = compute_context_hash_host(&input.context);
        let valid =
            Sp1Backend::verify_caveat_discharge(&proof, &input.state_root, &context_hash).unwrap();
        assert!(valid);
    }

    #[test]
    fn sp1_caveat_discharge_multiple_caveats() {
        // Stack multiple caveats: expiry + resource scope + action mask + attribute check.
        let caveats = vec![
            Sp1WireCaveat {
                caveat_type: caveat_types::EXPIRES_AT,
                body: 1800000000u64.to_le_bytes().to_vec(),
            },
            Sp1WireCaveat {
                caveat_type: caveat_types::RESOURCE_SCOPE,
                body: 42u64.to_le_bytes().to_vec(),
            },
            Sp1WireCaveat {
                caveat_type: caveat_types::ACTION_MASK,
                body: 0b0111u64.to_le_bytes().to_vec(), // allows read+write+exec
            },
            Sp1WireCaveat {
                caveat_type: caveat_types::ATTRIBUTE_GTE,
                body: {
                    let mut b = Vec::new();
                    b.extend_from_slice(&1u32.to_le_bytes()); // attr_id = 1
                    b.extend_from_slice(&100u64.to_le_bytes()); // threshold = 100
                    b
                },
            },
        ];

        let input = make_discharge_input(caveats);
        let proof = Sp1Backend::prove_caveat_discharge(&input).unwrap();

        assert_eq!(proof.program_type, Sp1ProgramType::CaveatDischarge);

        let context_hash = compute_context_hash_host(&input.context);
        let valid =
            Sp1Backend::verify_caveat_discharge(&proof, &input.state_root, &context_hash).unwrap();
        assert!(valid);
    }

    #[test]
    fn sp1_caveat_discharge_wrong_tail_rejected() {
        let mut input = make_discharge_input(vec![]);
        // Corrupt the expected tail (simulates a tampered token).
        input.expected_tail = [0xFF; 32];

        let result = Sp1Backend::prove_caveat_discharge(&input);
        assert!(result.is_err());
        assert!(
            result
                .unwrap_err()
                .contains("HMAC chain verification failed")
        );
    }

    #[test]
    fn sp1_caveat_discharge_wrong_merkle_rejected() {
        let mut input = make_discharge_input(vec![]);
        // Corrupt the state root (simulates wrong state commitment).
        input.state_root = [0xFF; 32];

        let result = Sp1Backend::prove_caveat_discharge(&input);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Invalid Merkle witness"));
    }

    #[test]
    fn sp1_caveat_discharge_verify_wrong_state_root() {
        let input = make_discharge_input(vec![]);
        let proof = Sp1Backend::prove_caveat_discharge(&input).unwrap();

        let context_hash = compute_context_hash_host(&input.context);
        let wrong_root = [0xFF; 32];
        let valid =
            Sp1Backend::verify_caveat_discharge(&proof, &wrong_root, &context_hash).unwrap();
        assert!(!valid, "should reject proof with wrong state root");
    }

    #[test]
    fn sp1_caveat_discharge_verify_wrong_context() {
        let input = make_discharge_input(vec![]);
        let proof = Sp1Backend::prove_caveat_discharge(&input).unwrap();

        let wrong_context_hash = [0xFF; 32];
        let valid =
            Sp1Backend::verify_caveat_discharge(&proof, &input.state_root, &wrong_context_hash)
                .unwrap();
        assert!(!valid, "should reject proof with wrong context hash");
    }

    #[test]
    fn sp1_caveat_discharge_empty_nonce_rejected() {
        let mut input = make_discharge_input(vec![]);
        input.nonce_bytes = vec![];

        let result = Sp1Backend::prove_caveat_discharge(&input);
        assert!(result.is_err());
        assert!(
            result
                .unwrap_err()
                .contains("nonce bytes must not be empty")
        );
    }

    #[test]
    fn sp1_caveat_discharge_token_id_extraction() {
        let input = make_discharge_input(vec![]);
        let proof = Sp1Backend::prove_caveat_discharge(&input).unwrap();

        let token_id = Sp1Backend::discharge_token_id(&proof).unwrap();

        // Verify it matches the expected token ID hash.
        let expected = {
            let mut hasher = blake3::Hasher::new();
            hasher.update(b"pyana-token-id:");
            hasher.update(&input.nonce_bytes);
            *hasher.finalize().as_bytes()
        };
        assert_eq!(token_id, expected);
    }

    #[test]
    fn sp1_caveat_discharge_proof_is_compact() {
        let caveats = vec![
            Sp1WireCaveat {
                caveat_type: caveat_types::EXPIRES_AT,
                body: 1800000000u64.to_le_bytes().to_vec(),
            },
            Sp1WireCaveat {
                caveat_type: caveat_types::RESOURCE_SCOPE,
                body: 42u64.to_le_bytes().to_vec(),
            },
        ];
        let input = make_discharge_input(caveats);
        let proof = Sp1Backend::prove_caveat_discharge(&input).unwrap();
        let size = Sp1Backend::proof_size(&proof);

        // Stub is small; real SP1 compressed would be ~50-100 KB.
        assert!(
            size < 1_000,
            "stub discharge proof should be compact, got {size} bytes"
        );
    }

    // =========================================================================
    // Datalog evaluation tests
    // =========================================================================

    /// Helper: compute a Merkle root from a set of facts (single-level 4-ary tree).
    fn build_merkle_tree(facts: &[Sp1Fact]) -> ([u8; 32], Vec<(Sp1Fact, Sp1MerkleProof)>) {
        // For testing, build a 1-level 4-ary tree. Pad with zeros if < 4 facts.
        assert!(facts.len() <= 4, "test helper only supports up to 4 facts");

        let mut leaves = [[0u8; 32]; 4];
        for (i, fact) in facts.iter().enumerate() {
            leaves[i] = hash_fact_host(fact);
        }

        // Root = hash of all 4 children.
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-merkle-4ary:");
        for leaf in &leaves {
            hasher.update(leaf);
        }
        let root = *hasher.finalize().as_bytes();

        // Build proofs for each fact.
        let mut proofs = Vec::new();
        for (i, fact) in facts.iter().enumerate() {
            let mut siblings = [[0u8; 32]; 3];
            let mut sib_idx = 0;
            for j in 0..4usize {
                if j != i {
                    siblings[sib_idx] = leaves[j];
                    sib_idx += 1;
                }
            }
            proofs.push((
                fact.clone(),
                Sp1MerkleProof {
                    siblings: vec![siblings],
                    positions: vec![i as u8],
                },
            ));
        }

        (root, proofs)
    }

    /// Predicate constants for tests.
    const PRED_ROLE: u64 = 100;
    const PRED_PERMISSION: u64 = 101;
    const PRED_ALLOW: u64 = 102;
    const PRED_HAS_BALANCE: u64 = 103;

    #[test]
    fn sp1_datalog_simple_derivation() {
        // Simple RBAC: role(alice, admin). permission(admin, write).
        // Rule: allow(User, Action) :- role(User, Role), permission(Role, Action).
        let alice = 1u64;
        let admin = 2u64;
        let write = 3u64;

        let initial_facts = vec![
            Sp1Fact {
                predicate: PRED_ROLE,
                terms: vec![alice, admin],
            },
            Sp1Fact {
                predicate: PRED_PERMISSION,
                terms: vec![admin, write],
            },
        ];

        let (root, merkle_proofs) = build_merkle_tree(&initial_facts);

        let rules = vec![Sp1Rule {
            head: Sp1Atom {
                predicate: PRED_ALLOW,
                terms: vec![Sp1Term::Var(0), Sp1Term::Var(2)],
            },
            body: vec![
                Sp1Atom {
                    predicate: PRED_ROLE,
                    terms: vec![Sp1Term::Var(0), Sp1Term::Var(1)],
                },
                Sp1Atom {
                    predicate: PRED_PERMISSION,
                    terms: vec![Sp1Term::Var(1), Sp1Term::Var(2)],
                },
            ],
            constraints: vec![],
            stratum: 0,
        }];

        let query = Sp1Fact {
            predicate: PRED_ALLOW,
            terms: vec![alice, write],
        };

        let input = Sp1DatalogInput {
            rules,
            merkle_proofs,
            attribute_values: vec![],
            attenuation_steps: vec![],
            initial_facts,
            fact_db_root: root,
            query: query.clone(),
            current_time: 1700000000,
        };

        let proof = Sp1Backend::prove_datalog_evaluation(&input).unwrap();
        assert_eq!(proof.program_type, Sp1ProgramType::DatalogEvaluation);

        // Verify the proof.
        let policy_commitment = compute_policy_commitment_host(&input.rules);
        let query_hash = hash_fact_host(&query);
        let valid =
            Sp1Backend::verify_datalog_evaluation(&proof, &root, &policy_commitment, &query_hash)
                .unwrap();
        assert!(valid, "simple RBAC derivation should succeed");
    }

    #[test]
    fn sp1_datalog_query_not_derivable() {
        // role(alice, viewer). permission(admin, write).
        // Query: allow(alice, write) — should NOT be derivable (alice is viewer, not admin).
        let alice = 1u64;
        let admin = 2u64;
        let viewer = 4u64;
        let write = 3u64;

        let initial_facts = vec![
            Sp1Fact {
                predicate: PRED_ROLE,
                terms: vec![alice, viewer],
            },
            Sp1Fact {
                predicate: PRED_PERMISSION,
                terms: vec![admin, write],
            },
        ];

        let (root, merkle_proofs) = build_merkle_tree(&initial_facts);

        let rules = vec![Sp1Rule {
            head: Sp1Atom {
                predicate: PRED_ALLOW,
                terms: vec![Sp1Term::Var(0), Sp1Term::Var(2)],
            },
            body: vec![
                Sp1Atom {
                    predicate: PRED_ROLE,
                    terms: vec![Sp1Term::Var(0), Sp1Term::Var(1)],
                },
                Sp1Atom {
                    predicate: PRED_PERMISSION,
                    terms: vec![Sp1Term::Var(1), Sp1Term::Var(2)],
                },
            ],
            constraints: vec![],
            stratum: 0,
        }];

        let query = Sp1Fact {
            predicate: PRED_ALLOW,
            terms: vec![alice, write],
        };

        let input = Sp1DatalogInput {
            rules,
            merkle_proofs,
            attribute_values: vec![],
            attenuation_steps: vec![],
            initial_facts,
            fact_db_root: root,
            query: query.clone(),
            current_time: 1700000000,
        };

        let proof = Sp1Backend::prove_datalog_evaluation(&input).unwrap();

        // The proof should indicate NOT authorized.
        let policy_commitment = compute_policy_commitment_host(&input.rules);
        let query_hash = hash_fact_host(&query);
        let result =
            Sp1Backend::verify_datalog_evaluation(&proof, &root, &policy_commitment, &query_hash)
                .unwrap();
        // verify returns the authorized flag from the proof.
        assert!(!result, "query should not be derivable");
    }

    #[test]
    fn sp1_datalog_with_constraint() {
        // Rule: allow(User, transfer) :- has_balance(User, Bal), Bal >= 1000.
        // Fact: has_balance(alice, 5000).
        let alice = 1u64;
        let transfer = 5u64;

        let initial_facts = vec![Sp1Fact {
            predicate: PRED_HAS_BALANCE,
            terms: vec![alice, 5000],
        }];

        let (root, merkle_proofs) = build_merkle_tree(&initial_facts);

        let rules = vec![Sp1Rule {
            head: Sp1Atom {
                predicate: PRED_ALLOW,
                terms: vec![Sp1Term::Var(0), Sp1Term::Const(transfer)],
            },
            body: vec![Sp1Atom {
                predicate: PRED_HAS_BALANCE,
                terms: vec![Sp1Term::Var(0), Sp1Term::Var(1)],
            }],
            constraints: vec![Sp1BuiltinConstraint::Gte {
                a: Sp1Term::Var(1),
                b: Sp1Term::Const(1000),
            }],
            stratum: 0,
        }];

        let query = Sp1Fact {
            predicate: PRED_ALLOW,
            terms: vec![alice, transfer],
        };

        let input = Sp1DatalogInput {
            rules,
            merkle_proofs,
            attribute_values: vec![],
            attenuation_steps: vec![],
            initial_facts,
            fact_db_root: root,
            query: query.clone(),
            current_time: 1700000000,
        };

        let proof = Sp1Backend::prove_datalog_evaluation(&input).unwrap();
        let policy_commitment = compute_policy_commitment_host(&input.rules);
        let query_hash = hash_fact_host(&query);
        let valid =
            Sp1Backend::verify_datalog_evaluation(&proof, &root, &policy_commitment, &query_hash)
                .unwrap();
        assert!(valid, "balance check should pass (5000 >= 1000)");
    }

    #[test]
    fn sp1_datalog_constraint_fails() {
        // Same rule but balance = 500 < 1000 threshold.
        let alice = 1u64;
        let transfer = 5u64;

        let initial_facts = vec![Sp1Fact {
            predicate: PRED_HAS_BALANCE,
            terms: vec![alice, 500],
        }];

        let (root, merkle_proofs) = build_merkle_tree(&initial_facts);

        let rules = vec![Sp1Rule {
            head: Sp1Atom {
                predicate: PRED_ALLOW,
                terms: vec![Sp1Term::Var(0), Sp1Term::Const(transfer)],
            },
            body: vec![Sp1Atom {
                predicate: PRED_HAS_BALANCE,
                terms: vec![Sp1Term::Var(0), Sp1Term::Var(1)],
            }],
            constraints: vec![Sp1BuiltinConstraint::Gte {
                a: Sp1Term::Var(1),
                b: Sp1Term::Const(1000),
            }],
            stratum: 0,
        }];

        let query = Sp1Fact {
            predicate: PRED_ALLOW,
            terms: vec![alice, transfer],
        };

        let input = Sp1DatalogInput {
            rules,
            merkle_proofs,
            attribute_values: vec![],
            attenuation_steps: vec![],
            initial_facts,
            fact_db_root: root,
            query: query.clone(),
            current_time: 1700000000,
        };

        let proof = Sp1Backend::prove_datalog_evaluation(&input).unwrap();
        let policy_commitment = compute_policy_commitment_host(&input.rules);
        let query_hash = hash_fact_host(&query);
        let result =
            Sp1Backend::verify_datalog_evaluation(&proof, &root, &policy_commitment, &query_hash)
                .unwrap();
        assert!(!result, "balance check should fail (500 < 1000)");
    }

    #[test]
    fn sp1_datalog_private_attributes() {
        // Rule uses attribute references (high-bit constants) for private data.
        // allow(User, premium) :- role(User, member), attr:balance >= 2000.
        // Attribute 1 = balance = 3000 (private, not revealed in proof).
        let alice = 1u64;
        let member = 6u64;
        let premium = 7u64;
        let attr_balance = (1u64 << 60) | 1; // Attribute reference for id=1.

        let initial_facts = vec![Sp1Fact {
            predicate: PRED_ROLE,
            terms: vec![alice, member],
        }];

        let (root, merkle_proofs) = build_merkle_tree(&initial_facts);

        let rules = vec![Sp1Rule {
            head: Sp1Atom {
                predicate: PRED_ALLOW,
                terms: vec![Sp1Term::Var(0), Sp1Term::Const(premium)],
            },
            body: vec![Sp1Atom {
                predicate: PRED_ROLE,
                terms: vec![Sp1Term::Var(0), Sp1Term::Const(member)],
            }],
            constraints: vec![Sp1BuiltinConstraint::Gte {
                a: Sp1Term::Const(attr_balance), // references attribute 1
                b: Sp1Term::Const(2000),
            }],
            stratum: 0,
        }];

        let query = Sp1Fact {
            predicate: PRED_ALLOW,
            terms: vec![alice, premium],
        };

        let input = Sp1DatalogInput {
            rules,
            merkle_proofs,
            attribute_values: vec![(1, 3000)], // balance = 3000 (PRIVATE!)
            attenuation_steps: vec![],
            initial_facts,
            fact_db_root: root,
            query: query.clone(),
            current_time: 1700000000,
        };

        let proof = Sp1Backend::prove_datalog_evaluation(&input).unwrap();
        let policy_commitment = compute_policy_commitment_host(&input.rules);
        let query_hash = hash_fact_host(&query);
        let valid =
            Sp1Backend::verify_datalog_evaluation(&proof, &root, &policy_commitment, &query_hash)
                .unwrap();
        assert!(valid, "private attribute check should pass (3000 >= 2000)");
    }

    #[test]
    fn sp1_datalog_recursive_derivation() {
        // Transitive closure: reachable(X, Y) :- edge(X, Y).
        //                     reachable(X, Z) :- reachable(X, Y), edge(Y, Z).
        // Facts: edge(a, b), edge(b, c), edge(c, d).
        // Query: reachable(a, d) — requires 2 recursive steps.
        let pred_edge: u64 = 200;
        let pred_reach: u64 = 201;
        let a = 10u64;
        let b = 11u64;
        let c = 12u64;
        let d = 13u64;

        let initial_facts = vec![
            Sp1Fact {
                predicate: pred_edge,
                terms: vec![a, b],
            },
            Sp1Fact {
                predicate: pred_edge,
                terms: vec![b, c],
            },
            Sp1Fact {
                predicate: pred_edge,
                terms: vec![c, d],
            },
        ];

        let (root, merkle_proofs) = build_merkle_tree(&initial_facts);

        let rules = vec![
            // Base case: reachable(X, Y) :- edge(X, Y).
            Sp1Rule {
                head: Sp1Atom {
                    predicate: pred_reach,
                    terms: vec![Sp1Term::Var(0), Sp1Term::Var(1)],
                },
                body: vec![Sp1Atom {
                    predicate: pred_edge,
                    terms: vec![Sp1Term::Var(0), Sp1Term::Var(1)],
                }],
                constraints: vec![],
                stratum: 0,
            },
            // Recursive case: reachable(X, Z) :- reachable(X, Y), edge(Y, Z).
            Sp1Rule {
                head: Sp1Atom {
                    predicate: pred_reach,
                    terms: vec![Sp1Term::Var(0), Sp1Term::Var(2)],
                },
                body: vec![
                    Sp1Atom {
                        predicate: pred_reach,
                        terms: vec![Sp1Term::Var(0), Sp1Term::Var(1)],
                    },
                    Sp1Atom {
                        predicate: pred_edge,
                        terms: vec![Sp1Term::Var(1), Sp1Term::Var(2)],
                    },
                ],
                constraints: vec![],
                stratum: 0,
            },
        ];

        let query = Sp1Fact {
            predicate: pred_reach,
            terms: vec![a, d],
        };

        let input = Sp1DatalogInput {
            rules,
            merkle_proofs,
            attribute_values: vec![],
            attenuation_steps: vec![],
            initial_facts,
            fact_db_root: root,
            query: query.clone(),
            current_time: 1700000000,
        };

        let proof = Sp1Backend::prove_datalog_evaluation(&input).unwrap();
        let policy_commitment = compute_policy_commitment_host(&input.rules);
        let query_hash = hash_fact_host(&query);
        let valid =
            Sp1Backend::verify_datalog_evaluation(&proof, &root, &policy_commitment, &query_hash)
                .unwrap();
        assert!(
            valid,
            "transitive reachability should derive reachable(a, d)"
        );
    }

    #[test]
    fn sp1_datalog_stratified_evaluation() {
        // Stratum 0: derive intermediate facts.
        // Stratum 1: derive final conclusion using stratum 0 results.
        let pred_base: u64 = 300;
        let pred_intermediate: u64 = 301;
        let pred_final: u64 = 302;

        let initial_facts = vec![Sp1Fact {
            predicate: pred_base,
            terms: vec![1, 42],
        }];

        let (root, merkle_proofs) = build_merkle_tree(&initial_facts);

        let rules = vec![
            // Stratum 0: intermediate(X) :- base(X, Y), Y >= 40.
            Sp1Rule {
                head: Sp1Atom {
                    predicate: pred_intermediate,
                    terms: vec![Sp1Term::Var(0)],
                },
                body: vec![Sp1Atom {
                    predicate: pred_base,
                    terms: vec![Sp1Term::Var(0), Sp1Term::Var(1)],
                }],
                constraints: vec![Sp1BuiltinConstraint::Gte {
                    a: Sp1Term::Var(1),
                    b: Sp1Term::Const(40),
                }],
                stratum: 0,
            },
            // Stratum 1: final(X) :- intermediate(X).
            Sp1Rule {
                head: Sp1Atom {
                    predicate: pred_final,
                    terms: vec![Sp1Term::Var(0)],
                },
                body: vec![Sp1Atom {
                    predicate: pred_intermediate,
                    terms: vec![Sp1Term::Var(0)],
                }],
                constraints: vec![],
                stratum: 1,
            },
        ];

        let query = Sp1Fact {
            predicate: pred_final,
            terms: vec![1],
        };

        let input = Sp1DatalogInput {
            rules,
            merkle_proofs,
            attribute_values: vec![],
            attenuation_steps: vec![],
            initial_facts,
            fact_db_root: root,
            query: query.clone(),
            current_time: 1700000000,
        };

        let proof = Sp1Backend::prove_datalog_evaluation(&input).unwrap();
        let policy_commitment = compute_policy_commitment_host(&input.rules);
        let query_hash = hash_fact_host(&query);
        let valid =
            Sp1Backend::verify_datalog_evaluation(&proof, &root, &policy_commitment, &query_hash)
                .unwrap();
        assert!(valid, "stratified evaluation should derive final(1)");
    }

    #[test]
    fn sp1_datalog_wrong_policy_rejected() {
        // Verify that a proof with wrong policy commitment is rejected.
        let initial_facts = vec![Sp1Fact {
            predicate: PRED_ROLE,
            terms: vec![1, 2],
        }];

        let (root, merkle_proofs) = build_merkle_tree(&initial_facts);

        let rules = vec![Sp1Rule {
            head: Sp1Atom {
                predicate: PRED_ALLOW,
                terms: vec![Sp1Term::Var(0)],
            },
            body: vec![Sp1Atom {
                predicate: PRED_ROLE,
                terms: vec![Sp1Term::Var(0), Sp1Term::Wildcard],
            }],
            constraints: vec![],
            stratum: 0,
        }];

        let query = Sp1Fact {
            predicate: PRED_ALLOW,
            terms: vec![1],
        };

        let input = Sp1DatalogInput {
            rules,
            merkle_proofs,
            attribute_values: vec![],
            attenuation_steps: vec![],
            initial_facts,
            fact_db_root: root,
            query: query.clone(),
            current_time: 1700000000,
        };

        let proof = Sp1Backend::prove_datalog_evaluation(&input).unwrap();
        let query_hash = hash_fact_host(&query);

        // Use a wrong policy commitment.
        let wrong_policy = [0xFFu8; 32];
        let result =
            Sp1Backend::verify_datalog_evaluation(&proof, &root, &wrong_policy, &query_hash)
                .unwrap();
        assert!(!result, "wrong policy commitment should be rejected");
    }

    #[test]
    fn sp1_datalog_empty_rules_rejected() {
        let initial_facts = vec![Sp1Fact {
            predicate: PRED_ROLE,
            terms: vec![1, 2],
        }];
        let (root, merkle_proofs) = build_merkle_tree(&initial_facts);

        let input = Sp1DatalogInput {
            rules: vec![],
            merkle_proofs,
            attribute_values: vec![],
            attenuation_steps: vec![],
            initial_facts,
            fact_db_root: root,
            query: Sp1Fact {
                predicate: PRED_ALLOW,
                terms: vec![1],
            },
            current_time: 1700000000,
        };

        let result = Sp1Backend::prove_datalog_evaluation(&input);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("rule set must not be empty"));
    }

    #[test]
    fn sp1_datalog_temporal_constraint() {
        // Rule: allow(User, action) :- role(User, R), timestamp within 3600s.
        let alice = 1u64;
        let admin = 2u64;
        let current_time = 1700000000u64;

        let initial_facts = vec![
            Sp1Fact {
                predicate: PRED_ROLE,
                terms: vec![alice, admin],
            },
            // A fact with a timestamp.
            Sp1Fact {
                predicate: 400,
                terms: vec![alice, current_time - 100],
            }, // 100 secs ago
        ];

        let (root, merkle_proofs) = build_merkle_tree(&initial_facts);

        let rules = vec![Sp1Rule {
            head: Sp1Atom {
                predicate: PRED_ALLOW,
                terms: vec![Sp1Term::Var(0), Sp1Term::Const(99)],
            },
            body: vec![
                Sp1Atom {
                    predicate: PRED_ROLE,
                    terms: vec![Sp1Term::Var(0), Sp1Term::Wildcard],
                },
                Sp1Atom {
                    predicate: 400,
                    terms: vec![Sp1Term::Var(0), Sp1Term::Var(1)],
                },
            ],
            constraints: vec![Sp1BuiltinConstraint::WithinDuration {
                timestamp: Sp1Term::Var(1),
                duration_secs: 3600,
            }],
            stratum: 0,
        }];

        let query = Sp1Fact {
            predicate: PRED_ALLOW,
            terms: vec![alice, 99],
        };

        let input = Sp1DatalogInput {
            rules,
            merkle_proofs,
            attribute_values: vec![],
            attenuation_steps: vec![],
            initial_facts,
            fact_db_root: root,
            query: query.clone(),
            current_time,
        };

        let proof = Sp1Backend::prove_datalog_evaluation(&input).unwrap();
        let policy_commitment = compute_policy_commitment_host(&input.rules);
        let query_hash = hash_fact_host(&query);
        let valid =
            Sp1Backend::verify_datalog_evaluation(&proof, &root, &policy_commitment, &query_hash)
                .unwrap();
        assert!(valid, "temporal constraint should pass (100s < 3600s)");
    }

    #[test]
    fn sp1_datalog_output_extraction() {
        let initial_facts = vec![Sp1Fact {
            predicate: PRED_ROLE,
            terms: vec![1, 2],
        }];
        let (root, merkle_proofs) = build_merkle_tree(&initial_facts);

        let rules = vec![Sp1Rule {
            head: Sp1Atom {
                predicate: PRED_ALLOW,
                terms: vec![Sp1Term::Var(0)],
            },
            body: vec![Sp1Atom {
                predicate: PRED_ROLE,
                terms: vec![Sp1Term::Var(0), Sp1Term::Wildcard],
            }],
            constraints: vec![],
            stratum: 0,
        }];

        let query = Sp1Fact {
            predicate: PRED_ALLOW,
            terms: vec![1],
        };

        let input = Sp1DatalogInput {
            rules: rules.clone(),
            merkle_proofs,
            attribute_values: vec![],
            attenuation_steps: vec![],
            initial_facts,
            fact_db_root: root,
            query: query.clone(),
            current_time: 1700000000,
        };

        let proof = Sp1Backend::prove_datalog_evaluation(&input).unwrap();
        let output = Sp1Backend::datalog_evaluation_output(&proof).unwrap();

        assert!(output.authorized);
        assert_eq!(output.derived_fact_hash, hash_fact_host(&query));
        assert_eq!(output.state_root, root); // No attenuation.
        assert_eq!(
            output.policy_commitment,
            compute_policy_commitment_host(&rules)
        );
    }
}
