//! Midnight observation node: watches finalized Midnight blocks for bridge events.
//!
//! # Design (mirrors Midnight's own Cardano bridge observation)
//!
//! Midnight's `c2m-bridge` pallet uses a `TransferHandler` trait that receives
//! pre-parsed bridge transfers from the Partner Chains substrate runtime. Their
//! node watches the Cardano mainchain via an SPO (stake pool operator) and feeds
//! observed transactions as inherent data.
//!
//! We follow the same pattern but in reverse:
//! - Watch Midnight's Substrate chain via WebSocket RPC.
//! - Subscribe to finalized block headers (GRANDPA finality).
//! - For each finalized block, query events for the bridge contract.
//! - Parse `BridgeLock` events into `MidnightToPyanaMessage`.
//! - Submit to pyana federation consensus.
//!
//! # Integration
//!
//! This module defines the observer as a standalone async task (`run_observer`).
//! It can be spawned from the pyana node binary or run as a sidecar process.
//! The submission callback is generic to allow both direct integration and
//! message-passing architectures.
//!
//! # Crash Recovery
//!
//! The observer persists `ObserverState` (last processed height + dedup set).
//! On restart, it resumes from `last_processed_height + 1` and skips any
//! already-processed events. This provides at-least-once delivery with
//! idempotent deduplication on the federation side.

use crate::midnight::{
    MidnightBridgeConfig, MidnightBridgeError, MidnightBridgeEvent, MidnightToPyanaMessage,
    ObserverState, validate_midnight_to_pyana,
};

use std::future::Future;

// ============================================================================
// Observer trait (submission callback)
// ============================================================================

/// Trait for submitting observed bridge events to the pyana federation.
///
/// Implementors handle the actual submission (e.g., direct consensus proposal,
/// RPC to the local node, message queue).
pub trait BridgeEventSubmitter: Send + Sync + 'static {
    /// Submit a validated bridge message for minting on pyana.
    ///
    /// Returns Ok(()) if the message was accepted for processing.
    /// The actual minting happens asynchronously through federation consensus.
    fn submit(
        &self,
        message: MidnightToPyanaMessage,
    ) -> impl Future<Output = Result<(), MidnightBridgeError>> + Send;
}

// ============================================================================
// Mock Substrate RPC types (stand-in until we add jsonrpsee/subxt)
// ============================================================================

/// A finalized block header from a Substrate chain.
///
/// This is a simplified representation; the real Substrate header includes
/// parent_hash, state_root, extrinsics_root, digest, etc.
#[derive(Clone, Debug)]
pub struct SubstrateBlockHeader {
    /// Block number.
    pub number: u64,
    /// Block hash (Blake2-256).
    pub hash: [u8; 32],
    /// Parent block hash.
    pub parent_hash: [u8; 32],
}

/// A system event from a Substrate block.
///
/// In a real integration, this would be decoded from the SCALE-encoded event
/// records via subxt or manual SCALE decoding.
#[derive(Clone, Debug)]
pub struct SubstrateEvent {
    /// The pallet index that emitted the event.
    pub pallet_index: u8,
    /// The event variant index within the pallet.
    pub variant_index: u8,
    /// The SCALE-encoded event data.
    pub data: Vec<u8>,
    /// The extrinsic index within the block (for tx_hash correlation).
    pub extrinsic_index: Option<u32>,
}

/// Trait abstracting the Substrate RPC connection.
///
/// This allows mocking the Midnight node for testing without an actual
/// WebSocket connection.
pub trait SubstrateRpcClient: Send + Sync + 'static {
    /// Subscribe to finalized block headers.
    ///
    /// Returns a stream of finalized headers. In production, this would use
    /// `chain_subscribeFinalizedHeads` via jsonrpsee.
    fn subscribe_finalized_heads(
        &self,
    ) -> impl Future<Output = Result<FinalizedHeadStream, MidnightBridgeError>> + Send;

    /// Get all system events for a given block hash.
    ///
    /// In production, this queries `system.events()` storage at the block.
    fn get_events(
        &self,
        block_hash: [u8; 32],
    ) -> impl Future<Output = Result<Vec<SubstrateEvent>, MidnightBridgeError>> + Send;

    /// Get the extrinsic hash for a given block and extrinsic index.
    ///
    /// Used to compute the tx_hash for the `MidnightToPyanaMessage`.
    fn get_extrinsic_hash(
        &self,
        block_hash: [u8; 32],
        extrinsic_index: u32,
    ) -> impl Future<Output = Result<[u8; 32], MidnightBridgeError>> + Send;
}

/// A stream of finalized block headers.
///
/// In production, this would be a `jsonrpsee::core::client::Subscription<Header>`.
/// For our purposes, we define it as a trait object that yields headers.
pub struct FinalizedHeadStream {
    /// Internal: boxed async iterator. In production, this wraps a jsonrpsee subscription.
    pub(crate) _inner: Box<dyn FinalizedHeadIterator>,
}

/// Async iterator over finalized heads (object-safe portion).
pub trait FinalizedHeadIterator: Send {
    /// Get the next finalized header, or None if the stream ended.
    fn next(
        &mut self,
    ) -> std::pin::Pin<Box<dyn Future<Output = Option<SubstrateBlockHeader>> + Send + '_>>;
}

// ============================================================================
// Event parsing (Midnight bridge contract events → our types)
// ============================================================================

/// The pallet index for our bridge contract on Midnight.
///
/// In a real deployment, this would be configured based on the runtime metadata.
/// For now, it's a placeholder constant.
const BRIDGE_PALLET_INDEX: u8 = 42;

/// Event variant indices within the bridge pallet.
const EVENT_BRIDGE_LOCK: u8 = 0;
const EVENT_BRIDGE_UNLOCK: u8 = 1;

/// Parse a Substrate event into a `MidnightBridgeEvent` if it belongs to the bridge pallet.
///
/// Returns `None` if the event is from a different pallet or has an unknown variant.
pub fn parse_bridge_event(event: &SubstrateEvent) -> Option<MidnightBridgeEvent> {
    if event.pallet_index != BRIDGE_PALLET_INDEX {
        return None;
    }

    match event.variant_index {
        EVENT_BRIDGE_LOCK => parse_lock_event(&event.data),
        EVENT_BRIDGE_UNLOCK => parse_unlock_event(&event.data),
        _ => None,
    }
}

/// Parse a `BridgeLock` event from SCALE-encoded data.
///
/// Expected layout (packed, little-endian):
/// - amount: u64 (8 bytes)
/// - pyana_recipient: [u8; 32] (32 bytes)
/// - nonce: u64 (8 bytes)
///
/// Total: 48 bytes minimum.
fn parse_lock_event(data: &[u8]) -> Option<MidnightBridgeEvent> {
    if data.len() < 48 {
        return None;
    }

    let amount = u64::from_le_bytes(data[0..8].try_into().ok()?);
    let pyana_recipient: [u8; 32] = data[8..40].try_into().ok()?;
    let nonce = u64::from_le_bytes(data[40..48].try_into().ok()?);

    Some(MidnightBridgeEvent::Lock {
        amount,
        pyana_recipient,
        nonce,
    })
}

/// Parse a `BridgeUnlock` event from SCALE-encoded data.
///
/// Expected layout:
/// - amount: u64 (8 bytes)
/// - midnight_recipient_len: u32 (4 bytes, SCALE compact would differ but we simplify)
/// - midnight_recipient: [u8; midnight_recipient_len]
/// - nullifier: [u8; 32]
fn parse_unlock_event(data: &[u8]) -> Option<MidnightBridgeEvent> {
    if data.len() < 44 {
        // Minimum: 8 + 4 + 0 + 32 = 44 (empty recipient)
        return None;
    }

    let amount = u64::from_le_bytes(data[0..8].try_into().ok()?);
    let recipient_len = u32::from_le_bytes(data[8..12].try_into().ok()?) as usize;

    let expected_len = 12 + recipient_len + 32;
    if data.len() < expected_len {
        return None;
    }

    let midnight_recipient = data[12..12 + recipient_len].to_vec();
    let nullifier: [u8; 32] = data[12 + recipient_len..12 + recipient_len + 32]
        .try_into()
        .ok()?;

    Some(MidnightBridgeEvent::Unlock {
        amount,
        midnight_recipient,
        nullifier,
    })
}

// ============================================================================
// Observer main loop
// ============================================================================

/// Run the Midnight bridge observer as an async task.
///
/// This function subscribes to finalized Midnight blocks, parses bridge events,
/// validates them, and submits valid `MidnightToPyanaMessage`s to the federation.
///
/// # Arguments
///
/// * `rpc` - The Substrate RPC client (connects to Midnight node).
/// * `submitter` - The bridge event submitter (sends validated messages to federation).
/// * `config` - Bridge configuration (contract address, limits, etc.).
/// * `state` - Mutable observer state (persisted for crash recovery).
///
/// # Returns
///
/// This function runs indefinitely (or until the RPC stream ends / errors out).
/// On error, it returns the error so the caller can decide whether to retry.
pub async fn run_observer<R, S>(
    rpc: R,
    submitter: S,
    config: MidnightBridgeConfig,
    state: &mut ObserverState,
) -> Result<(), MidnightBridgeError>
where
    R: SubstrateRpcClient,
    S: BridgeEventSubmitter,
{
    let mut head_stream = rpc.subscribe_finalized_heads().await?;

    while let Some(header) = head_stream._inner.next().await {
        // Skip blocks we've already processed (crash recovery).
        if header.number <= state.last_processed_height {
            continue;
        }

        // Fetch events for this block.
        let events = rpc.get_events(header.hash).await?;

        // Process each event.
        for (log_index, event) in events.iter().enumerate() {
            let Some(bridge_event) = parse_bridge_event(event) else {
                continue;
            };

            // We only care about Lock events (Midnight → pyana direction).
            let MidnightBridgeEvent::Lock {
                amount,
                pyana_recipient,
                nonce: _,
            } = bridge_event
            else {
                continue;
            };

            // Compute tx_hash for this event.
            let tx_hash = if let Some(ext_idx) = event.extrinsic_index {
                rpc.get_extrinsic_hash(header.hash, ext_idx).await?
            } else {
                // If no extrinsic index, use block_hash as fallback (less ideal).
                header.hash
            };

            let message = MidnightToPyanaMessage {
                midnight_tx_hash: tx_hash,
                amount,
                pyana_recipient,
                midnight_height: header.number,
                log_index: log_index as u32,
            };

            // Validate before submission.
            if let Err(e) = validate_midnight_to_pyana(
                &message,
                &config,
                state,
                header.number, // finalized_height = current header (it IS finalized)
            ) {
                // Log and skip invalid/duplicate events.
                // In production, this would use tracing.
                eprintln!(
                    "midnight observer: skipping event at height {}, log {}: {}",
                    header.number, log_index, e
                );
                continue;
            }

            // Submit to federation.
            submitter.submit(message.clone()).await?;

            // Mark as processed (for dedup on restart).
            state.mark_processed(tx_hash, log_index as u32);
        }

        // Advance the watermark.
        state.advance_height(header.number);

        // Periodic pruning of the dedup set (keep it bounded).
        state.prune_if_large(10_000);
    }

    Ok(())
}

// ============================================================================
// Mock implementations for testing
// ============================================================================

#[cfg(test)]
pub mod mock {
    use super::*;
    use std::sync::{Arc, Mutex};

    /// A mock RPC client that yields pre-configured blocks and events.
    pub struct MockRpcClient {
        pub headers: Vec<SubstrateBlockHeader>,
        pub events: std::collections::HashMap<[u8; 32], Vec<SubstrateEvent>>,
    }

    impl SubstrateRpcClient for MockRpcClient {
        fn subscribe_finalized_heads(
            &self,
        ) -> impl Future<Output = Result<FinalizedHeadStream, MidnightBridgeError>> + Send {
            let headers = self.headers.clone();
            async move {
                Ok(FinalizedHeadStream {
                    _inner: Box::new(MockHeadIterator { headers, index: 0 }),
                })
            }
        }

        fn get_events(
            &self,
            block_hash: [u8; 32],
        ) -> impl Future<Output = Result<Vec<SubstrateEvent>, MidnightBridgeError>> + Send {
            let events = self.events.get(&block_hash).cloned().unwrap_or_default();
            async move { Ok(events) }
        }

        fn get_extrinsic_hash(
            &self,
            block_hash: [u8; 32],
            extrinsic_index: u32,
        ) -> impl Future<Output = Result<[u8; 32], MidnightBridgeError>> + Send {
            // Deterministic hash from block_hash + index for testing.
            let mut hasher = blake3::Hasher::new();
            hasher.update(&block_hash);
            hasher.update(&extrinsic_index.to_le_bytes());
            let hash = *hasher.finalize().as_bytes();
            async move { Ok(hash) }
        }
    }

    struct MockHeadIterator {
        headers: Vec<SubstrateBlockHeader>,
        index: usize,
    }

    impl FinalizedHeadIterator for MockHeadIterator {
        fn next(
            &mut self,
        ) -> std::pin::Pin<Box<dyn Future<Output = Option<SubstrateBlockHeader>> + Send + '_>>
        {
            Box::pin(async move {
                if self.index < self.headers.len() {
                    let header = self.headers[self.index].clone();
                    self.index += 1;
                    Some(header)
                } else {
                    None
                }
            })
        }
    }

    /// A mock submitter that collects submitted messages.
    #[derive(Clone, Default)]
    pub struct MockSubmitter {
        pub messages: Arc<Mutex<Vec<MidnightToPyanaMessage>>>,
    }

    impl BridgeEventSubmitter for MockSubmitter {
        fn submit(
            &self,
            message: MidnightToPyanaMessage,
        ) -> impl Future<Output = Result<(), MidnightBridgeError>> + Send {
            self.messages.lock().unwrap().push(message);
            async { Ok(()) }
        }
    }

    /// Build a mock lock event (SCALE-like encoding matching our parser).
    pub fn make_lock_event_data(amount: u64, pyana_recipient: [u8; 32], nonce: u64) -> Vec<u8> {
        let mut data = Vec::with_capacity(48);
        data.extend_from_slice(&amount.to_le_bytes());
        data.extend_from_slice(&pyana_recipient);
        data.extend_from_slice(&nonce.to_le_bytes());
        data
    }
}

#[cfg(test)]
mod tests {
    use super::mock::*;
    use super::*;

    #[test]
    fn test_parse_lock_event() {
        let recipient = [0xAA; 32];
        let data = make_lock_event_data(5_000_000, recipient, 42);
        let event = SubstrateEvent {
            pallet_index: BRIDGE_PALLET_INDEX,
            variant_index: EVENT_BRIDGE_LOCK,
            data,
            extrinsic_index: Some(1),
        };

        let parsed = parse_bridge_event(&event).unwrap();
        match parsed {
            MidnightBridgeEvent::Lock {
                amount,
                pyana_recipient,
                nonce,
            } => {
                assert_eq!(amount, 5_000_000);
                assert_eq!(pyana_recipient, recipient);
                assert_eq!(nonce, 42);
            }
            _ => panic!("expected Lock event"),
        }
    }

    #[test]
    fn test_parse_lock_event_wrong_pallet() {
        let data = make_lock_event_data(100, [0xBB; 32], 1);
        let event = SubstrateEvent {
            pallet_index: 99, // wrong pallet
            variant_index: EVENT_BRIDGE_LOCK,
            data,
            extrinsic_index: None,
        };
        assert!(parse_bridge_event(&event).is_none());
    }

    #[test]
    fn test_parse_lock_event_too_short() {
        let event = SubstrateEvent {
            pallet_index: BRIDGE_PALLET_INDEX,
            variant_index: EVENT_BRIDGE_LOCK,
            data: vec![0u8; 10], // too short
            extrinsic_index: None,
        };
        assert!(parse_bridge_event(&event).is_none());
    }

    #[test]
    fn test_parse_unlock_event() {
        let mut data = Vec::new();
        let amount: u64 = 1_000_000;
        let recipient = vec![0xCC; 32];
        let nullifier = [0xDD; 32];

        data.extend_from_slice(&amount.to_le_bytes());
        data.extend_from_slice(&(recipient.len() as u32).to_le_bytes());
        data.extend_from_slice(&recipient);
        data.extend_from_slice(&nullifier);

        let event = SubstrateEvent {
            pallet_index: BRIDGE_PALLET_INDEX,
            variant_index: EVENT_BRIDGE_UNLOCK,
            data,
            extrinsic_index: Some(0),
        };

        let parsed = parse_bridge_event(&event).unwrap();
        match parsed {
            MidnightBridgeEvent::Unlock {
                amount: a,
                midnight_recipient,
                nullifier: n,
            } => {
                assert_eq!(a, 1_000_000);
                assert_eq!(midnight_recipient, recipient);
                assert_eq!(n, nullifier);
            }
            _ => panic!("expected Unlock event"),
        }
    }

    #[tokio::test]
    async fn test_observer_processes_lock_events() {
        let recipient = [0xEE; 32];
        let block_hash = [0x01; 32];

        let rpc = MockRpcClient {
            headers: vec![SubstrateBlockHeader {
                number: 100,
                hash: block_hash,
                parent_hash: [0x00; 32],
            }],
            events: {
                let mut m = std::collections::HashMap::new();
                m.insert(
                    block_hash,
                    vec![SubstrateEvent {
                        pallet_index: BRIDGE_PALLET_INDEX,
                        variant_index: EVENT_BRIDGE_LOCK,
                        data: make_lock_event_data(5_000_000, recipient, 1),
                        extrinsic_index: Some(0),
                    }],
                );
                m
            },
        };

        let submitter = MockSubmitter::default();
        let config = crate::midnight::MidnightBridgeConfig {
            contract_address: [0xCC; 32],
            midnight_rpc_url: "ws://localhost:9944".to_string(),
            confirmations: 0,
            federation_keys: vec![],
            min_amount: 1_000_000,
            max_amount: 1_000_000_000_000,
        };

        let mut state = ObserverState::default();

        let result = run_observer(rpc, submitter.clone(), config, &mut state).await;
        assert!(result.is_ok());

        let messages = submitter.messages.lock().unwrap();
        assert_eq!(messages.len(), 1);
        assert_eq!(messages[0].amount, 5_000_000);
        assert_eq!(messages[0].pyana_recipient, recipient);
        assert_eq!(messages[0].midnight_height, 100);
        assert_eq!(state.last_processed_height, 100);
    }

    #[tokio::test]
    async fn test_observer_skips_already_processed() {
        let recipient = [0xFF; 32];
        let block_hash = [0x02; 32];

        let rpc = MockRpcClient {
            headers: vec![SubstrateBlockHeader {
                number: 50,
                hash: block_hash,
                parent_hash: [0x01; 32],
            }],
            events: {
                let mut m = std::collections::HashMap::new();
                m.insert(
                    block_hash,
                    vec![SubstrateEvent {
                        pallet_index: BRIDGE_PALLET_INDEX,
                        variant_index: EVENT_BRIDGE_LOCK,
                        data: make_lock_event_data(2_000_000, recipient, 1),
                        extrinsic_index: Some(0),
                    }],
                );
                m
            },
        };

        let submitter = MockSubmitter::default();
        let config = crate::midnight::MidnightBridgeConfig {
            contract_address: [0xCC; 32],
            midnight_rpc_url: "ws://localhost:9944".to_string(),
            confirmations: 0,
            federation_keys: vec![],
            min_amount: 1_000_000,
            max_amount: 1_000_000_000_000,
        };

        // State already at height 100 → block 50 should be skipped.
        let mut state = ObserverState {
            last_processed_height: 100,
            processed_events: vec![],
        };

        let result = run_observer(rpc, submitter.clone(), config, &mut state).await;
        assert!(result.is_ok());

        let messages = submitter.messages.lock().unwrap();
        assert_eq!(
            messages.len(),
            0,
            "already-processed block should be skipped"
        );
    }

    #[tokio::test]
    async fn test_observer_skips_below_minimum() {
        let recipient = [0xAB; 32];
        let block_hash = [0x03; 32];

        let rpc = MockRpcClient {
            headers: vec![SubstrateBlockHeader {
                number: 200,
                hash: block_hash,
                parent_hash: [0x02; 32],
            }],
            events: {
                let mut m = std::collections::HashMap::new();
                m.insert(
                    block_hash,
                    vec![SubstrateEvent {
                        pallet_index: BRIDGE_PALLET_INDEX,
                        variant_index: EVENT_BRIDGE_LOCK,
                        data: make_lock_event_data(100, recipient, 1), // below minimum
                        extrinsic_index: Some(0),
                    }],
                );
                m
            },
        };

        let submitter = MockSubmitter::default();
        let config = crate::midnight::MidnightBridgeConfig {
            contract_address: [0xCC; 32],
            midnight_rpc_url: "ws://localhost:9944".to_string(),
            confirmations: 0,
            federation_keys: vec![],
            min_amount: 1_000_000,
            max_amount: 1_000_000_000_000,
        };

        let mut state = ObserverState::default();

        let result = run_observer(rpc, submitter.clone(), config, &mut state).await;
        assert!(result.is_ok());

        let messages = submitter.messages.lock().unwrap();
        assert_eq!(messages.len(), 0, "below-minimum event should be skipped");
    }

    #[tokio::test]
    async fn test_observer_multiple_blocks_and_events() {
        let recipient1 = [0x11; 32];
        let recipient2 = [0x22; 32];
        let block1 = [0x10; 32];
        let block2 = [0x20; 32];

        let rpc = MockRpcClient {
            headers: vec![
                SubstrateBlockHeader {
                    number: 1,
                    hash: block1,
                    parent_hash: [0x00; 32],
                },
                SubstrateBlockHeader {
                    number: 2,
                    hash: block2,
                    parent_hash: block1,
                },
            ],
            events: {
                let mut m = std::collections::HashMap::new();
                m.insert(
                    block1,
                    vec![SubstrateEvent {
                        pallet_index: BRIDGE_PALLET_INDEX,
                        variant_index: EVENT_BRIDGE_LOCK,
                        data: make_lock_event_data(3_000_000, recipient1, 1),
                        extrinsic_index: Some(0),
                    }],
                );
                m.insert(
                    block2,
                    vec![
                        SubstrateEvent {
                            pallet_index: BRIDGE_PALLET_INDEX,
                            variant_index: EVENT_BRIDGE_LOCK,
                            data: make_lock_event_data(7_000_000, recipient2, 2),
                            extrinsic_index: Some(0),
                        },
                        // Non-bridge event (different pallet).
                        SubstrateEvent {
                            pallet_index: 10,
                            variant_index: 0,
                            data: vec![1, 2, 3],
                            extrinsic_index: Some(1),
                        },
                    ],
                );
                m
            },
        };

        let submitter = MockSubmitter::default();
        let config = crate::midnight::MidnightBridgeConfig {
            contract_address: [0xCC; 32],
            midnight_rpc_url: "ws://localhost:9944".to_string(),
            confirmations: 0,
            federation_keys: vec![],
            min_amount: 1_000_000,
            max_amount: 1_000_000_000_000,
        };

        let mut state = ObserverState::default();

        let result = run_observer(rpc, submitter.clone(), config, &mut state).await;
        assert!(result.is_ok());

        let messages = submitter.messages.lock().unwrap();
        assert_eq!(messages.len(), 2);
        assert_eq!(messages[0].pyana_recipient, recipient1);
        assert_eq!(messages[0].amount, 3_000_000);
        assert_eq!(messages[1].pyana_recipient, recipient2);
        assert_eq!(messages[1].amount, 7_000_000);
        assert_eq!(state.last_processed_height, 2);
    }
}
