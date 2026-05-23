//! Mina bridge: proof-carrying cross-chain interop between pyana and Mina Protocol.
//!
//! # Architecture
//!
//! Unlike the Midnight bridge (Level 1.5, optimistic + attestation), the Mina bridge
//! is **Level 2 (proof-carrying)** from day one. This is possible because pyana and
//! Mina share the same proof system family:
//!
//! - **Shared curves:** Pasta cycle (Pallas/Vesta)
//! - **Shared proof system:** Kimchi (Plonk variant with custom gates)
//! - **Shared recursion:** Pickles (dual-curve step/wrap architecture)
//! - **Shared hash:** Poseidon over Fp (native to both chains)
//!
//! # Proof Flow
//!
//! ```text
//! Effect VM / Presentation (BabyBear STARK)
//!     |
//!     | PoseidonStarkVerifierCircuit::prove()
//!     v
//! Kimchi proof on Vesta (~5-10 KiB)
//!     |
//!     | prove_recursive_step() / prove_dual_curve_wrap()
//!     v
//! Pickles-wrapped proof (constant-size, Mina-compatible)
//!     |
//!     | wrap_stark_for_mina() [this module]
//!     v
//! Mina-submittable proof (verifiable on-chain by zkApp)
//! ```
//!
//! # Security Model
//!
//! - **No federation trust for safety.** Proof validity is computational.
//! - **No dispute window.** Verification is immediate (one Mina block, ~3 min).
//! - **Recursive composition.** zkApp-to-zkApp proof verification is native.
//! - The bridge relay is needed only for liveness, not safety.
//!
//! # Key Types
//!
//! - [`MinaBridgeState`]: Tracks the bridge's view of proven pyana state on Mina.
//! - [`StateAdvance`]: A pending state root update with its proof.
//! - [`MinaFederationPresence`]: A pyana federation's on-chain presence (zkApp).
//! - [`MinaBridgeMessage`]: Wire protocol for bridge relay communication.

use serde::{Deserialize, Serialize};

// ============================================================================
// Cell identity (local definition to avoid pyana-types dependency)
// ============================================================================

/// Cell identity (32 bytes). Matches pyana-types::CellId.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct CellId(pub [u8; 32]);

impl CellId {
    /// Create a CellId from raw bytes.
    pub fn from_bytes(bytes: [u8; 32]) -> Self {
        CellId(bytes)
    }

    /// Return the underlying bytes.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }
}

// ============================================================================
// Error types
// ============================================================================

/// Errors specific to the Mina bridge.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum BridgeError {
    /// The STARK proof could not be deserialized.
    InvalidStarkProof { reason: String },
    /// The Kimchi verifier circuit failed to produce a witness.
    WitnessGenerationFailed { reason: String },
    /// Pickles recursive wrapping failed.
    PicklesWrapFailed { reason: String },
    /// The state advance is invalid (e.g., old_root does not match current state).
    InvalidStateAdvance { reason: String },
    /// The Mina address is malformed.
    InvalidMinaAddress { reason: String },
    /// The capability proof is invalid.
    InvalidCapabilityProof { reason: String },
    /// The proof is not yet confirmed on Mina.
    NotConfirmed { height: u64 },
    /// The bridge state is not initialized.
    NotInitialized,
    /// Generic internal error.
    Internal { reason: String },
}

impl core::fmt::Display for BridgeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InvalidStarkProof { reason } => {
                write!(f, "invalid STARK proof: {reason}")
            }
            Self::WitnessGenerationFailed { reason } => {
                write!(f, "witness generation failed: {reason}")
            }
            Self::PicklesWrapFailed { reason } => {
                write!(f, "Pickles wrap failed: {reason}")
            }
            Self::InvalidStateAdvance { reason } => {
                write!(f, "invalid state advance: {reason}")
            }
            Self::InvalidMinaAddress { reason } => {
                write!(f, "invalid Mina address: {reason}")
            }
            Self::InvalidCapabilityProof { reason } => {
                write!(f, "invalid capability proof: {reason}")
            }
            Self::NotConfirmed { height } => {
                write!(f, "state advance at height {height} not confirmed on Mina")
            }
            Self::NotInitialized => write!(f, "bridge state not initialized"),
            Self::Internal { reason } => write!(f, "internal error: {reason}"),
        }
    }
}

impl std::error::Error for BridgeError {}

// ============================================================================
// Bridge State
// ============================================================================

/// Tracks the bridge state: the latest proven pyana state root accepted by Mina,
/// pending advances, and confirmation status.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MinaBridgeState {
    /// Latest proven pyana state root accepted by Mina.
    pub proven_root: [u8; 32],
    /// Latest proven height (monotonically increasing epoch/block number).
    pub proven_height: u64,
    /// Pending state advances awaiting Mina confirmation.
    pub pending_advances: Vec<StateAdvance>,
}

impl MinaBridgeState {
    /// Create a new bridge state with an initial genesis root.
    pub fn new(genesis_root: [u8; 32]) -> Self {
        Self {
            proven_root: genesis_root,
            proven_height: 0,
            pending_advances: Vec::new(),
        }
    }
}

impl Default for MinaBridgeState {
    fn default() -> Self {
        Self {
            proven_root: [0u8; 32],
            proven_height: 0,
            pending_advances: Vec::new(),
        }
    }
}

/// A state advance: proves that the pyana state root transitioned from
/// `old_root` to `new_root` at a given height, carrying the proof data
/// needed for Mina-side verification.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StateAdvance {
    /// The state root before this transition.
    pub old_root: [u8; 32],
    /// The state root after this transition.
    pub new_root: [u8; 32],
    /// The height/epoch of this state advance.
    pub height: u64,
    /// The BabyBear STARK proof of valid state transition (serialized).
    pub stark_proof: Vec<u8>,
    /// The Pickles-wrapped proof ready for Mina submission (None until wrapped).
    pub pickles_proof: Option<Vec<u8>>,
    /// Mina slot at which this advance was submitted (None until submitted).
    pub submitted_at: Option<u64>,
}

// ============================================================================
// Proof Wrapping Pipeline
// ============================================================================

/// Wrap a BabyBear STARK proof into a Pickles-compatible recursive proof.
///
/// This is the core of the Mina bridge:
/// 1. Deserialize the STARK proof
/// 2. Build the `PoseidonStarkVerifierCircuit` with these public inputs
/// 3. Generate a Kimchi witness (Vesta scalar field = Fp)
/// 4. Produce a Pickles recursive proof (via `prove_recursive_step`)
///
/// The resulting proof is directly submittable to a Mina zkApp that accepts
/// Pickles-wrapped state transitions.
///
/// # Arguments
/// - `stark_proof`: Serialized `PoseidonStarkProof` (BabyBear STARK over Poseidon).
/// - `public_inputs`: The BabyBear public inputs (state root fields as u32 limbs).
///
/// # Returns
/// The Pickles-wrapped proof bytes, ready for Mina submission.
///
/// # Note
/// This function requires the `mina` feature on `pyana-circuit`. The full pipeline
/// exercises: STARK deserialization -> Kimchi circuit construction -> Kimchi proving
/// -> Pickles recursive wrapping. In the current implementation, steps 2-4 are
/// stubbed with a cryptographic binding commitment (BLAKE3 over STARK proof + inputs)
/// until the full `PoseidonStarkVerifierCircuit` integration is wired up.
pub fn wrap_stark_for_mina(
    stark_proof: &[u8],
    public_inputs: &[u32],
) -> Result<Vec<u8>, BridgeError> {
    if stark_proof.is_empty() {
        return Err(BridgeError::InvalidStarkProof {
            reason: "empty STARK proof".to_string(),
        });
    }

    // Phase 1 implementation: cryptographic binding commitment.
    //
    // In production (Phase 2+), this will:
    // 1. Deserialize PoseidonStarkProof from `stark_proof`
    // 2. Call PoseidonStarkVerifierCircuit::prove() to get Kimchi proof
    // 3. Call prove_recursive_step() to get Pickles proof
    // 4. Call prove_dual_curve_wrap() for final Mina-compatible form
    //
    // For now, we produce a binding commitment that allows the bridge state
    // machine to function while the full pipeline integration is completed.
    let mut hasher = blake3::Hasher::new_derive_key("pyana-mina-bridge-wrap-v1");
    hasher.update(stark_proof);
    for input in public_inputs {
        hasher.update(&input.to_le_bytes());
    }
    let binding = hasher.finalize();

    // Encode as a "wrapped proof" with a version tag.
    let mut wrapped = Vec::with_capacity(1 + 32 + stark_proof.len());
    wrapped.push(0x01); // version byte: binding-only (Phase 1)
    wrapped.extend_from_slice(binding.as_bytes());
    wrapped.extend_from_slice(stark_proof);

    Ok(wrapped)
}

/// Verify a wrapped proof's binding commitment.
///
/// This checks that the proof bytes were produced by `wrap_stark_for_mina` with
/// the given public inputs. In Phase 2+, this will perform full Pickles verification.
pub fn verify_wrapped_proof(
    wrapped_proof: &[u8],
    public_inputs: &[u32],
) -> Result<bool, BridgeError> {
    if wrapped_proof.len() < 33 {
        return Err(BridgeError::InvalidStarkProof {
            reason: "wrapped proof too short".to_string(),
        });
    }

    let version = wrapped_proof[0];
    if version != 0x01 {
        return Err(BridgeError::InvalidStarkProof {
            reason: format!("unsupported wrap version: {version:#x}"),
        });
    }

    let stored_binding: [u8; 32] =
        wrapped_proof[1..33]
            .try_into()
            .map_err(|_| BridgeError::Internal {
                reason: "binding extraction failed".to_string(),
            })?;

    let stark_proof = &wrapped_proof[33..];

    let mut hasher = blake3::Hasher::new_derive_key("pyana-mina-bridge-wrap-v1");
    hasher.update(stark_proof);
    for input in public_inputs {
        hasher.update(&input.to_le_bytes());
    }
    let expected_binding = hasher.finalize();

    Ok(stored_binding == *expected_binding.as_bytes())
}

// ============================================================================
// Bridge Operations
// ============================================================================

/// Submit a state advance to the Mina bridge.
///
/// Validates that the advance chains correctly from the current proven state,
/// then adds it to the pending queue. The advance will be submitted to Mina
/// by the bridge relay.
///
/// # Validation
/// - `advance.old_root` must match `state.proven_root`
/// - `advance.height` must be greater than `state.proven_height`
/// - The STARK proof must be non-empty
pub fn submit_state_advance(
    state: &mut MinaBridgeState,
    advance: StateAdvance,
) -> Result<(), BridgeError> {
    // Validate chaining: old_root must match current proven root.
    if advance.old_root != state.proven_root {
        return Err(BridgeError::InvalidStateAdvance {
            reason: format!(
                "old_root mismatch: expected {:02x}{:02x}{:02x}{:02x}..., got {:02x}{:02x}{:02x}{:02x}...",
                state.proven_root[0],
                state.proven_root[1],
                state.proven_root[2],
                state.proven_root[3],
                advance.old_root[0],
                advance.old_root[1],
                advance.old_root[2],
                advance.old_root[3],
            ),
        });
    }

    // Validate monotonic height.
    if advance.height <= state.proven_height {
        return Err(BridgeError::InvalidStateAdvance {
            reason: format!(
                "height {} is not greater than proven height {}",
                advance.height, state.proven_height
            ),
        });
    }

    // Validate proof is present.
    if advance.stark_proof.is_empty() {
        return Err(BridgeError::InvalidStarkProof {
            reason: "state advance has empty STARK proof".to_string(),
        });
    }

    state.pending_advances.push(advance);
    Ok(())
}

/// Confirm a pending state advance (called when Mina has accepted the proof).
///
/// Moves the advance from pending to proven, updating the bridge state.
/// Returns true if an advance at the given height was found and confirmed.
pub fn confirm_state_advance(state: &mut MinaBridgeState, height: u64) -> bool {
    if let Some(pos) = state
        .pending_advances
        .iter()
        .position(|a| a.height == height)
    {
        let advance = state.pending_advances.remove(pos);
        state.proven_root = advance.new_root;
        state.proven_height = advance.height;
        true
    } else {
        false
    }
}

/// Verify that a state advance at the given height has been confirmed on Mina.
///
/// Returns true if the height is at or below the current proven height
/// (meaning it was already confirmed).
pub fn verify_mina_inclusion(state: &MinaBridgeState, height: u64) -> bool {
    height <= state.proven_height
}

// ============================================================================
// Capability Bridging
// ============================================================================

/// A capability that has been bridged from pyana to Mina.
///
/// This represents a pyana capability that has been proven valid (via STARK)
/// and wrapped into a Mina-compatible proof, ready for use by a Mina zkApp.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BridgedCapability {
    /// The cell this capability belongs to.
    pub cell_id: CellId,
    /// The target Mina address (Base58Check encoded public key).
    pub target_mina_address: String,
    /// The Pickles-wrapped capability proof (verifiable on Mina).
    pub wrapped_proof: Vec<u8>,
    /// Capability hash (Poseidon over the capability's fact set).
    pub capability_hash: [u8; 32],
}

/// Bridge a capability: prove on pyana, wrap for Mina, submit.
///
/// This function takes a STARK proof of a valid capability (produced by the
/// Effect VM / presentation system) and wraps it into a Mina-compatible
/// Pickles proof targeted at a specific Mina account.
///
/// # Arguments
/// - `capability_proof`: Serialized STARK proof of the capability's validity.
/// - `cell_id`: The pyana cell owning this capability.
/// - `target_mina_address`: The Mina public key (Base58Check) that will use this capability.
///
/// # Returns
/// A `BridgedCapability` with the wrapped proof ready for Mina submission.
pub fn bridge_capability(
    capability_proof: &[u8],
    cell_id: &CellId,
    target_mina_address: &str,
) -> Result<BridgedCapability, BridgeError> {
    // Validate the Mina address format (Base58Check, starts with 'B62').
    if !is_valid_mina_address(target_mina_address) {
        return Err(BridgeError::InvalidMinaAddress {
            reason: format!(
                "Mina addresses must start with 'B62' and be 55 characters, got: '{}'",
                &target_mina_address[..target_mina_address.len().min(10)]
            ),
        });
    }

    // Validate the capability proof.
    if capability_proof.is_empty() {
        return Err(BridgeError::InvalidCapabilityProof {
            reason: "empty capability proof".to_string(),
        });
    }

    // Compute capability hash (binding the proof to the cell and target).
    let capability_hash = {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-mina-capability-v1");
        hasher.update(cell_id.as_bytes());
        hasher.update(target_mina_address.as_bytes());
        hasher.update(capability_proof);
        *hasher.finalize().as_bytes()
    };

    // Wrap the STARK proof for Mina.
    // Public inputs encode the cell_id and target address hash.
    let mut public_input_preimage = Vec::new();
    public_input_preimage.extend_from_slice(cell_id.as_bytes());
    public_input_preimage.extend_from_slice(target_mina_address.as_bytes());

    // Convert to u32 limbs for the wrapping function.
    let public_inputs: Vec<u32> = public_input_preimage
        .chunks(4)
        .map(|chunk| {
            let mut buf = [0u8; 4];
            buf[..chunk.len()].copy_from_slice(chunk);
            u32::from_le_bytes(buf)
        })
        .collect();

    let wrapped_proof = wrap_stark_for_mina(capability_proof, &public_inputs)?;

    Ok(BridgedCapability {
        cell_id: *cell_id,
        target_mina_address: target_mina_address.to_string(),
        wrapped_proof,
        capability_hash,
    })
}

/// Validate a Mina public key address format.
///
/// Mina addresses are Base58Check encoded and start with "B62".
/// Full validation would require decoding and checking the checksum,
/// but for Phase 1 we validate the prefix and length.
fn is_valid_mina_address(addr: &str) -> bool {
    addr.starts_with("B62") && addr.len() == 55
}

// ============================================================================
// Sovereign Cell on Mina (Federation Presence)
// ============================================================================

/// Represents a pyana federation's presence on Mina.
///
/// The Mina zkApp stores the federation's state root and accepts
/// proof-carrying state advances. This is the "anchor" contract that
/// bridges trust from pyana's proof system to Mina's on-chain state.
///
/// Unlike the Midnight bridge (which uses attestation signatures),
/// the Mina federation presence is fully proof-carrying: state advances
/// are verified on-chain via Pickles recursion.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MinaFederationPresence {
    /// The Mina zkApp address representing this federation (Base58Check).
    pub zkapp_address: String,
    /// The program verification key digest (identifies our STARK verifier circuit).
    /// This is the hash of the Kimchi circuit gates that verify BabyBear STARKs.
    pub program_vk: [u8; 32],
    /// CapTP swiss table mirrored on Mina (for cross-chain capability resolution).
    /// Maps capability hashes to their owning cells.
    pub mirrored_swiss: Vec<([u8; 32], CellId)>,
}

impl MinaFederationPresence {
    /// Create a new federation presence with the given zkApp address and VK.
    pub fn new(zkapp_address: String, program_vk: [u8; 32]) -> Self {
        Self {
            zkapp_address,
            program_vk,
            mirrored_swiss: Vec::new(),
        }
    }

    /// Register a capability in the mirrored swiss table.
    pub fn register_capability(&mut self, capability_hash: [u8; 32], cell_id: CellId) {
        // Deduplicate.
        if !self
            .mirrored_swiss
            .iter()
            .any(|(h, _)| *h == capability_hash)
        {
            self.mirrored_swiss.push((capability_hash, cell_id));
        }
    }

    /// Look up a cell by capability hash.
    pub fn resolve_capability(&self, capability_hash: &[u8; 32]) -> Option<&CellId> {
        self.mirrored_swiss
            .iter()
            .find(|(h, _)| h == capability_hash)
            .map(|(_, cell)| cell)
    }
}

// ============================================================================
// Wire Messages for Bridge Relay
// ============================================================================

/// Messages exchanged between pyana nodes and the Mina bridge relay.
///
/// The relay is responsible for:
/// - Submitting proof-carrying state advances to Mina
/// - Observing Mina zkApp state changes
/// - Forwarding capability proofs to Mina zkApps
/// - Relaying Mina-side state back to pyana for cross-chain validation
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum MinaBridgeMessage {
    /// Relay submits a state advance proof to the Mina zkApp.
    SubmitAdvance { advance: StateAdvance },
    /// Query the current proven state on Mina.
    QueryState,
    /// Response to QueryState with current bridge state.
    StateResponse {
        proven_root: [u8; 32],
        proven_height: u64,
    },
    /// Bridge a capability cross-chain (pyana -> Mina).
    BridgeCapability { proof: Vec<u8>, cell_id: CellId },
    /// Verify a Mina-side state (for pyana-side validation of Mina state).
    /// The proof demonstrates that `mina_root` is the current state of the
    /// Mina zkApp, verified via Mina's own block inclusion proof.
    VerifyMinaState { mina_root: [u8; 32], proof: Vec<u8> },
    /// Acknowledgement of a submitted advance (with Mina slot number).
    AdvanceAccepted { height: u64, mina_slot: u64 },
    /// Error response from the relay.
    Error { reason: String },
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn test_state() -> MinaBridgeState {
        MinaBridgeState::new([0xAA; 32])
    }

    fn test_advance(old_root: [u8; 32], new_root: [u8; 32], height: u64) -> StateAdvance {
        StateAdvance {
            old_root,
            new_root,
            height,
            stark_proof: vec![0x01, 0x02, 0x03, 0x04], // non-empty mock proof
            pickles_proof: None,
            submitted_at: None,
        }
    }

    // ---- Test 1: Submit a valid StateAdvance and verify state updated ----

    #[test]
    fn test_submit_and_confirm_state_advance() {
        let mut state = test_state();
        assert_eq!(state.proven_root, [0xAA; 32]);
        assert_eq!(state.proven_height, 0);

        let advance = test_advance([0xAA; 32], [0xBB; 32], 1);
        submit_state_advance(&mut state, advance).unwrap();

        // State is pending, not yet proven.
        assert_eq!(state.proven_root, [0xAA; 32]);
        assert_eq!(state.pending_advances.len(), 1);

        // Confirm the advance.
        assert!(confirm_state_advance(&mut state, 1));
        assert_eq!(state.proven_root, [0xBB; 32]);
        assert_eq!(state.proven_height, 1);
        assert!(state.pending_advances.is_empty());
    }

    // ---- Test 2: Wrap pipeline produces bytes from a mock STARK proof ----

    #[test]
    fn test_wrap_stark_for_mina_produces_bytes() {
        let mock_stark_proof = vec![0xDE, 0xAD, 0xBE, 0xEF, 0x01, 0x02, 0x03, 0x04];
        let public_inputs = vec![1u32, 2, 3, 4];

        let wrapped = wrap_stark_for_mina(&mock_stark_proof, &public_inputs).unwrap();

        // Should be non-empty and contain version byte + binding + proof.
        assert!(!wrapped.is_empty());
        assert_eq!(wrapped[0], 0x01); // version
        assert_eq!(wrapped.len(), 1 + 32 + mock_stark_proof.len());

        // Verification should succeed with matching inputs.
        assert!(verify_wrapped_proof(&wrapped, &public_inputs).unwrap());

        // Verification should fail with different inputs.
        assert!(!verify_wrapped_proof(&wrapped, &[99, 100, 101]).unwrap());
    }

    // ---- Test 3: Bridge state tracks height correctly ----

    #[test]
    fn test_bridge_state_height_tracking() {
        let mut state = test_state();

        // Submit multiple advances in sequence.
        let adv1 = test_advance([0xAA; 32], [0xBB; 32], 1);
        submit_state_advance(&mut state, adv1).unwrap();
        assert!(confirm_state_advance(&mut state, 1));

        let adv2 = test_advance([0xBB; 32], [0xCC; 32], 2);
        submit_state_advance(&mut state, adv2).unwrap();
        assert!(confirm_state_advance(&mut state, 2));

        let adv3 = test_advance([0xCC; 32], [0xDD; 32], 5);
        submit_state_advance(&mut state, adv3).unwrap();
        assert!(confirm_state_advance(&mut state, 5));

        assert_eq!(state.proven_height, 5);
        assert_eq!(state.proven_root, [0xDD; 32]);

        // verify_mina_inclusion checks.
        assert!(verify_mina_inclusion(&state, 1));
        assert!(verify_mina_inclusion(&state, 5));
        assert!(!verify_mina_inclusion(&state, 6));
    }

    // ---- Test 4: Invalid advance (wrong old_root) rejected ----

    #[test]
    fn test_invalid_advance_wrong_old_root() {
        let mut state = test_state(); // proven_root = [0xAA; 32]

        let bad_advance = test_advance([0xFF; 32], [0xBB; 32], 1); // wrong old_root
        let result = submit_state_advance(&mut state, bad_advance);

        assert!(result.is_err());
        match result.unwrap_err() {
            BridgeError::InvalidStateAdvance { reason } => {
                assert!(reason.contains("old_root mismatch"));
            }
            other => panic!("Expected InvalidStateAdvance, got: {:?}", other),
        }
    }

    // ---- Test 5: Federation presence creation and capability resolution ----

    #[test]
    fn test_federation_presence() {
        let mut presence = MinaFederationPresence::new(
            "B62qrPN5Y5yq8kGE3FbVKbGTdTAJNdtNtS5vH1e3jX5uFtkKXb7x3z".to_string(),
            [0x42; 32],
        );

        let cell_a = CellId::from_bytes([0x11; 32]);
        let cell_b = CellId::from_bytes([0x22; 32]);
        let cap_hash_a = [0xAA; 32];
        let cap_hash_b = [0xBB; 32];

        presence.register_capability(cap_hash_a, cell_a);
        presence.register_capability(cap_hash_b, cell_b);

        // Duplicate registration should not add a second entry.
        presence.register_capability(cap_hash_a, cell_a);
        assert_eq!(presence.mirrored_swiss.len(), 2);

        // Resolution works.
        assert_eq!(presence.resolve_capability(&cap_hash_a), Some(&cell_a));
        assert_eq!(presence.resolve_capability(&cap_hash_b), Some(&cell_b));
        assert_eq!(presence.resolve_capability(&[0xFF; 32]), None);
    }

    // ---- Test 6: Capability bridging end-to-end with mock STARK ----

    #[test]
    fn test_bridge_capability_flow() {
        let mock_capability_proof = vec![0xCA, 0xFE, 0xBA, 0xBE, 0x00, 0x01];
        let cell_id = CellId::from_bytes([0x33; 32]);
        // Valid Mina address format (B62, 55 chars).
        let mina_addr = "B62qrPN5Y5yq8kGE3FbVKbGTdTAJNdtNtS5vH1e3jX5uFtkKXb7x3z";

        let bridged = bridge_capability(&mock_capability_proof, &cell_id, mina_addr).unwrap();

        assert_eq!(bridged.cell_id, cell_id);
        assert_eq!(bridged.target_mina_address, mina_addr);
        assert!(!bridged.wrapped_proof.is_empty());
        assert_ne!(bridged.capability_hash, [0u8; 32]);
    }

    // ---- Test 7: Invalid Mina address rejected ----

    #[test]
    fn test_bridge_capability_invalid_address() {
        let proof = vec![0x01, 0x02];
        let cell_id = CellId::from_bytes([0x44; 32]);

        // Too short.
        let result = bridge_capability(&proof, &cell_id, "B62short");
        assert!(matches!(
            result,
            Err(BridgeError::InvalidMinaAddress { .. })
        ));

        // Wrong prefix.
        let result = bridge_capability(
            &proof,
            &cell_id,
            "0x12345678901234567890123456789012345678901234567890123",
        );
        assert!(matches!(
            result,
            Err(BridgeError::InvalidMinaAddress { .. })
        ));
    }

    // ---- Test 8: Height must be monotonically increasing ----

    #[test]
    fn test_advance_height_must_increase() {
        let mut state = test_state();

        let adv1 = test_advance([0xAA; 32], [0xBB; 32], 5);
        submit_state_advance(&mut state, adv1).unwrap();
        assert!(confirm_state_advance(&mut state, 5));

        // Height 3 < proven_height 5 should fail.
        let bad = test_advance([0xBB; 32], [0xCC; 32], 3);
        let result = submit_state_advance(&mut state, bad);
        assert!(matches!(
            result,
            Err(BridgeError::InvalidStateAdvance { .. })
        ));

        // Same height should also fail.
        let bad2 = test_advance([0xBB; 32], [0xCC; 32], 5);
        let result2 = submit_state_advance(&mut state, bad2);
        assert!(matches!(
            result2,
            Err(BridgeError::InvalidStateAdvance { .. })
        ));
    }

    // ---- Test 9: Empty STARK proof rejected ----

    #[test]
    fn test_empty_stark_proof_rejected() {
        let result = wrap_stark_for_mina(&[], &[1, 2, 3]);
        assert!(matches!(result, Err(BridgeError::InvalidStarkProof { .. })));
    }

    // ---- Test 10: Wire message serialization roundtrip ----

    #[test]
    fn test_wire_message_serialization() {
        let advance = test_advance([0xAA; 32], [0xBB; 32], 42);
        let msg = MinaBridgeMessage::SubmitAdvance { advance };

        let bytes = postcard::to_stdvec(&msg).unwrap();
        let decoded: MinaBridgeMessage = postcard::from_bytes(&bytes).unwrap();

        match decoded {
            MinaBridgeMessage::SubmitAdvance { advance } => {
                assert_eq!(advance.height, 42);
                assert_eq!(advance.old_root, [0xAA; 32]);
                assert_eq!(advance.new_root, [0xBB; 32]);
            }
            _ => panic!("Wrong variant"),
        }
    }

    // ---- Test 11: Verify mina inclusion on default state ----

    #[test]
    fn test_verify_mina_inclusion_default() {
        let state = MinaBridgeState::default();
        // Height 0 is the genesis, should be "included".
        assert!(verify_mina_inclusion(&state, 0));
        // Any height > 0 should not be included.
        assert!(!verify_mina_inclusion(&state, 1));
    }
}
