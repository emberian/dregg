//! Receipt chain verification for proof-carrying state.
//!
//! A receipt chain is a sequence of [`TurnReceipt`]s linked by hash pointers.
//! Each receipt's `previous_receipt_hash` field contains the hash of the prior
//! receipt in the chain. The chain proves that the agent's state evolved through
//! a sequence of valid, executor-checked turns from genesis.
//!
//! This module provides verification functions that check:
//! - Hash continuity: each receipt points to the previous one
//! - State continuity: each receipt's pre_state_hash matches the prior's post_state_hash
//! - Agent consistency: all receipts in a chain belong to the same agent
//! - Genesis validity: the first receipt has `previous_receipt_hash = None`

use ed25519_dalek;
use pyana_cell::CellId;

use crate::turn::TurnReceipt;

/// Errors that can occur during receipt chain verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    /// The chain is empty (no receipts to verify).
    EmptyChain,

    /// The first receipt in the chain has a non-None previous_receipt_hash.
    /// The genesis receipt must have `previous_receipt_hash = None`.
    GenesisHasPrevious {
        /// The unexpected previous hash found on the genesis receipt.
        previous_hash: [u8; 32],
    },

    /// A receipt's `previous_receipt_hash` does not match the hash of the
    /// preceding receipt in the chain.
    HashChainBreak {
        /// Index of the receipt with the mismatch (1-indexed into the chain).
        index: usize,
        /// The expected hash (computed from the previous receipt).
        expected: [u8; 32],
        /// The actual `previous_receipt_hash` found on this receipt.
        actual: [u8; 32],
    },

    /// A receipt's `pre_state_hash` does not match the prior receipt's `post_state_hash`.
    /// This means there's a gap in the state transitions.
    StateChainBreak {
        /// Index of the receipt with the mismatch (1-indexed into the chain).
        index: usize,
        /// The expected pre_state_hash (from the prior receipt's post_state_hash).
        expected_pre_state: [u8; 32],
        /// The actual pre_state_hash found.
        actual_pre_state: [u8; 32],
    },

    /// A receipt in the chain belongs to a different agent than the first receipt.
    AgentMismatch {
        /// Index of the mismatched receipt.
        index: usize,
        /// The expected agent (from the first receipt).
        expected_agent: CellId,
        /// The actual agent found.
        actual_agent: CellId,
    },

    /// A receipt's executor signature failed verification against all known
    /// executor public keys.
    ExecutorSignatureInvalid {
        /// Index of the receipt with the invalid signature.
        index: usize,
    },
}

impl core::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            VerifyError::EmptyChain => write!(f, "receipt chain is empty"),
            VerifyError::GenesisHasPrevious { .. } => {
                write!(f, "genesis receipt has a non-None previous_receipt_hash")
            }
            VerifyError::HashChainBreak { index, .. } => {
                write!(f, "hash chain break at receipt index {index}")
            }
            VerifyError::StateChainBreak { index, .. } => {
                write!(f, "state chain break at receipt index {index}")
            }
            VerifyError::AgentMismatch {
                index,
                expected_agent,
                actual_agent,
            } => {
                write!(
                    f,
                    "agent mismatch at receipt index {index}: expected {expected_agent}, got {actual_agent}"
                )
            }
            VerifyError::ExecutorSignatureInvalid { index } => {
                write!(f, "executor signature invalid at receipt index {index}")
            }
        }
    }
}

impl std::error::Error for VerifyError {}

/// Verify a receipt chain for a single agent.
///
/// Checks:
/// 1. The chain is non-empty.
/// 2. The first receipt has `previous_receipt_hash == None` (genesis).
/// 3. Each subsequent receipt's `previous_receipt_hash` matches the BLAKE3 hash
///    of the previous receipt.
/// 4. Each subsequent receipt's `pre_state_hash` matches the prior receipt's
///    `post_state_hash` (state continuity).
/// 5. All receipts in the chain belong to the same agent.
///
/// This function does NOT verify that the turns themselves were valid (that was the
/// executor's job at commit time). It only verifies the chain structure is intact.
pub fn verify_receipt_chain(receipts: &[TurnReceipt]) -> Result<(), VerifyError> {
    if receipts.is_empty() {
        return Err(VerifyError::EmptyChain);
    }

    // Check genesis receipt.
    let genesis = &receipts[0];
    if let Some(prev_hash) = genesis.previous_receipt_hash {
        return Err(VerifyError::GenesisHasPrevious {
            previous_hash: prev_hash,
        });
    }

    let expected_agent = genesis.agent;

    // Walk the chain.
    for i in 1..receipts.len() {
        let prev = &receipts[i - 1];
        let curr = &receipts[i];

        // Check agent consistency.
        if curr.agent != expected_agent {
            return Err(VerifyError::AgentMismatch {
                index: i,
                expected_agent,
                actual_agent: curr.agent,
            });
        }

        // Check hash chain continuity.
        let expected_hash = prev.receipt_hash();
        match curr.previous_receipt_hash {
            Some(actual_hash) if actual_hash == expected_hash => {}
            Some(actual_hash) => {
                return Err(VerifyError::HashChainBreak {
                    index: i,
                    expected: expected_hash,
                    actual: actual_hash,
                });
            }
            None => {
                return Err(VerifyError::HashChainBreak {
                    index: i,
                    expected: expected_hash,
                    actual: [0u8; 32],
                });
            }
        }

        // Check state continuity.
        if curr.pre_state_hash != prev.post_state_hash {
            return Err(VerifyError::StateChainBreak {
                index: i,
                expected_pre_state: prev.post_state_hash,
                actual_pre_state: curr.pre_state_hash,
            });
        }
    }

    Ok(())
}

/// Verify a receipt chain and return the final state commitment.
///
/// On success, returns the `post_state_hash` of the last receipt in the chain.
/// This is the current state commitment that the chain proves.
pub fn verify_receipt_chain_head(receipts: &[TurnReceipt]) -> Result<[u8; 32], VerifyError> {
    verify_receipt_chain(receipts)?;
    Ok(receipts.last().unwrap().post_state_hash)
}

/// Verify that a single receipt correctly extends a chain ending with `previous`.
///
/// This is the "online" check used when appending to a chain: you already trust
/// the chain up to `previous`, and you want to verify `next` links correctly.
pub fn verify_receipt_extends(
    previous: &TurnReceipt,
    next: &TurnReceipt,
) -> Result<(), VerifyError> {
    // Check agent consistency.
    if next.agent != previous.agent {
        return Err(VerifyError::AgentMismatch {
            index: 1,
            expected_agent: previous.agent,
            actual_agent: next.agent,
        });
    }

    // Check hash chain.
    let expected_hash = previous.receipt_hash();
    match next.previous_receipt_hash {
        Some(actual_hash) if actual_hash == expected_hash => {}
        Some(actual_hash) => {
            return Err(VerifyError::HashChainBreak {
                index: 1,
                expected: expected_hash,
                actual: actual_hash,
            });
        }
        None => {
            return Err(VerifyError::HashChainBreak {
                index: 1,
                expected: expected_hash,
                actual: [0u8; 32],
            });
        }
    }

    // Check state continuity.
    if next.pre_state_hash != previous.post_state_hash {
        return Err(VerifyError::StateChainBreak {
            index: 1,
            expected_pre_state: previous.post_state_hash,
            actual_pre_state: next.pre_state_hash,
        });
    }

    Ok(())
}

/// Verify a receipt chain with executor signature verification.
///
/// In addition to the structural checks performed by [`verify_receipt_chain`], this
/// function verifies the Ed25519 executor signature on each receipt that has one.
///
/// If a receipt has an `executor_signature`, it must verify against at least one
/// of the provided `executor_pubkeys`. If no signatures are present on any receipt,
/// this is equivalent to `verify_receipt_chain`.
pub fn verify_receipt_chain_with_keys(
    receipts: &[TurnReceipt],
    executor_pubkeys: &[[u8; 32]],
) -> Result<(), VerifyError> {
    // First, verify structural integrity.
    verify_receipt_chain(receipts)?;

    // Then verify executor signatures on receipts that have them.
    for (i, receipt) in receipts.iter().enumerate() {
        if let Some(ref sig_bytes) = receipt.executor_signature {
            if sig_bytes.len() != 64 {
                return Err(VerifyError::ExecutorSignatureInvalid { index: i });
            }
            let sig_array: [u8; 64] = sig_bytes[..64].try_into().unwrap();
            let receipt_hash = receipt.receipt_hash();
            let signature = ed25519_dalek::Signature::from_bytes(&sig_array);

            let mut verified = false;
            for pubkey_bytes in executor_pubkeys {
                if let Ok(vk) = ed25519_dalek::VerifyingKey::from_bytes(pubkey_bytes) {
                    if vk.verify_strict(&receipt_hash, &signature).is_ok() {
                        verified = true;
                        break;
                    }
                }
            }

            if !verified {
                return Err(VerifyError::ExecutorSignatureInvalid { index: i });
            }
        }
    }

    Ok(())
}

/// Sign a receipt with the given Ed25519 signing key.
/// Returns the 64-byte signature over the receipt hash.
pub fn sign_receipt(receipt: &TurnReceipt, signing_key: &[u8; 32]) -> Vec<u8> {
    use ed25519_dalek::Signer;
    let sk = ed25519_dalek::SigningKey::from_bytes(signing_key);
    let receipt_hash = receipt.receipt_hash();
    let sig = sk.sign(&receipt_hash);
    sig.to_bytes().to_vec()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: create a test receipt with specific state hashes and chain link.
    fn make_receipt(
        agent: CellId,
        pre_state: [u8; 32],
        post_state: [u8; 32],
        previous_receipt_hash: Option<[u8; 32]>,
    ) -> TurnReceipt {
        TurnReceipt {
            turn_hash: [0u8; 32],
            forest_hash: [0u8; 32],
            pre_state_hash: pre_state,
            post_state_hash: post_state,
            timestamp: 1000,
            effects_hash: [0u8; 32],
            computrons_used: 100,
            action_count: 1,
            previous_receipt_hash,
            agent,
            federation_id: [0u8; 32],
            routing_directives: Vec::new(),
            introduction_exports: Vec::new(),
            derivation_records: vec![],
            emitted_events: vec![],
            executor_signature: None,
            finality: Default::default(),
        }
    }

    /// Build a valid chain of N receipts for a given agent.
    fn build_valid_chain(agent: CellId, n: usize) -> Vec<TurnReceipt> {
        let mut chain: Vec<TurnReceipt> = Vec::with_capacity(n);
        let mut state = [1u8; 32];

        for i in 0..n {
            let pre_state = state;
            // Advance state deterministically.
            state[0] = (i + 2) as u8;
            let post_state = state;

            let previous_receipt_hash = if i == 0 {
                None
            } else {
                Some(chain[i - 1].receipt_hash())
            };

            chain.push(make_receipt(
                agent,
                pre_state,
                post_state,
                previous_receipt_hash,
            ));
        }

        chain
    }

    #[test]
    fn test_verify_empty_chain() {
        let result = verify_receipt_chain(&[]);
        assert_eq!(result.unwrap_err(), VerifyError::EmptyChain);
    }

    #[test]
    fn test_verify_single_receipt_genesis() {
        let agent = CellId::from_bytes([1u8; 32]);
        let receipt = make_receipt(agent, [1u8; 32], [2u8; 32], None);
        assert!(verify_receipt_chain(&[receipt]).is_ok());
    }

    #[test]
    fn test_verify_single_receipt_non_genesis_fails() {
        let agent = CellId::from_bytes([1u8; 32]);
        let receipt = make_receipt(agent, [1u8; 32], [2u8; 32], Some([99u8; 32]));
        let err = verify_receipt_chain(&[receipt]).unwrap_err();
        assert!(matches!(err, VerifyError::GenesisHasPrevious { .. }));
    }

    #[test]
    fn test_verify_valid_chain_of_three() {
        let agent = CellId::from_bytes([1u8; 32]);
        let chain = build_valid_chain(agent, 3);
        assert!(verify_receipt_chain(&chain).is_ok());
    }

    #[test]
    fn test_verify_valid_chain_of_ten() {
        let agent = CellId::from_bytes([1u8; 32]);
        let chain = build_valid_chain(agent, 10);
        assert!(verify_receipt_chain(&chain).is_ok());
    }

    #[test]
    fn test_verify_hash_chain_break() {
        let agent = CellId::from_bytes([1u8; 32]);
        let mut chain = build_valid_chain(agent, 3);

        // Corrupt the second receipt's previous_receipt_hash.
        chain[1].previous_receipt_hash = Some([0xDE; 32]);

        let err = verify_receipt_chain(&chain).unwrap_err();
        match err {
            VerifyError::HashChainBreak { index, .. } => assert_eq!(index, 1),
            other => panic!("expected HashChainBreak, got {other:?}"),
        }
    }

    #[test]
    fn test_verify_state_chain_break() {
        let agent = CellId::from_bytes([1u8; 32]);
        let mut chain = build_valid_chain(agent, 3);

        // Corrupt the third receipt's pre_state_hash so it doesn't match
        // the second receipt's post_state_hash.
        chain[2].pre_state_hash = [0xFF; 32];
        // Fix the hash chain link to still be valid.
        chain[2].previous_receipt_hash = Some(chain[1].receipt_hash());

        let err = verify_receipt_chain(&chain).unwrap_err();
        match err {
            VerifyError::StateChainBreak { index, .. } => assert_eq!(index, 2),
            other => panic!("expected StateChainBreak, got {other:?}"),
        }
    }

    #[test]
    fn test_verify_agent_mismatch() {
        let agent1 = CellId::from_bytes([1u8; 32]);
        let agent2 = CellId::from_bytes([2u8; 32]);
        let mut chain = build_valid_chain(agent1, 3);

        // Change the agent on the second receipt.
        chain[1].agent = agent2;

        let err = verify_receipt_chain(&chain).unwrap_err();
        match err {
            VerifyError::AgentMismatch {
                index,
                expected_agent,
                actual_agent,
            } => {
                assert_eq!(index, 1);
                assert_eq!(expected_agent, agent1);
                assert_eq!(actual_agent, agent2);
            }
            other => panic!("expected AgentMismatch, got {other:?}"),
        }
    }

    #[test]
    fn test_verify_receipt_chain_head() {
        let agent = CellId::from_bytes([1u8; 32]);
        let chain = build_valid_chain(agent, 5);
        let expected_head = chain.last().unwrap().post_state_hash;
        let result = verify_receipt_chain_head(&chain).unwrap();
        assert_eq!(result, expected_head);
    }

    #[test]
    fn test_verify_receipt_extends_valid() {
        let agent = CellId::from_bytes([1u8; 32]);
        let chain = build_valid_chain(agent, 2);
        assert!(verify_receipt_extends(&chain[0], &chain[1]).is_ok());
    }

    #[test]
    fn test_verify_receipt_extends_wrong_hash() {
        let agent = CellId::from_bytes([1u8; 32]);
        let chain = build_valid_chain(agent, 2);
        let mut bad_next = chain[1].clone();
        bad_next.previous_receipt_hash = Some([0xAA; 32]);
        let err = verify_receipt_extends(&chain[0], &bad_next).unwrap_err();
        assert!(matches!(err, VerifyError::HashChainBreak { .. }));
    }

    #[test]
    fn test_verify_receipt_extends_wrong_agent() {
        let agent1 = CellId::from_bytes([1u8; 32]);
        let agent2 = CellId::from_bytes([2u8; 32]);
        let chain = build_valid_chain(agent1, 2);
        let mut bad_next = chain[1].clone();
        bad_next.agent = agent2;
        let err = verify_receipt_extends(&chain[0], &bad_next).unwrap_err();
        assert!(matches!(err, VerifyError::AgentMismatch { .. }));
    }

    #[test]
    fn test_verify_receipt_extends_wrong_pre_state() {
        let agent = CellId::from_bytes([1u8; 32]);
        let chain = build_valid_chain(agent, 2);
        let mut bad_next = chain[1].clone();
        bad_next.pre_state_hash = [0xCC; 32];
        // Fix the hash link.
        bad_next.previous_receipt_hash = Some(chain[0].receipt_hash());
        let err = verify_receipt_extends(&chain[0], &bad_next).unwrap_err();
        assert!(matches!(err, VerifyError::StateChainBreak { .. }));
    }

    #[test]
    fn test_receipt_hash_determinism() {
        let agent = CellId::from_bytes([1u8; 32]);
        let r1 = make_receipt(agent, [1u8; 32], [2u8; 32], None);
        let r2 = make_receipt(agent, [1u8; 32], [2u8; 32], None);
        assert_eq!(r1.receipt_hash(), r2.receipt_hash());
    }

    #[test]
    fn test_receipt_hash_includes_previous() {
        let agent = CellId::from_bytes([1u8; 32]);
        let r_none = make_receipt(agent, [1u8; 32], [2u8; 32], None);
        let r_some = make_receipt(agent, [1u8; 32], [2u8; 32], Some([3u8; 32]));
        // Different previous_receipt_hash should produce different receipt hashes.
        assert_ne!(r_none.receipt_hash(), r_some.receipt_hash());
    }
}
