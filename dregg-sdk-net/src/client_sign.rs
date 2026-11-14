//! The pure half of `dregg-client-sign`: what a send turn IS, how it is
//! prepared from a node-reported head, and what a third party checks to know
//! that a finalized turn anchored a given payload. No function here does I/O
//! except [`Head::fetch`]; the binary owns the rest.
//!
//! # The send turn
//!
//! One hybrid-signed action on the signer's own cell carrying one
//! `EmitEvent { cell, topic: symbol(topic), data: pack_payload(payload) }`,
//! with the payload string as the turn memo. `Turn::hash` absorbs the memo
//! (length-prefixed) and the call forest, which absorbs the action, which
//! absorbs the effect's cell, topic and data words. So the turn hash commits
//! the topic and the exact payload, and the receipt commits the turn hash.
//!
//! # Prepare, then submit
//!
//! [`prepare_send`] is a function of `(identity, head, topic, payload)` and
//! nothing else: no clock, no randomness (the ML-DSA half is the deterministic
//! FIPS 204 variant), no network. Its result carries the turn hash and the
//! exact postcard `SignedTurn` bytes. A caller binds the hash into its own
//! record first and submits those bytes later; a retry sends the same bytes.
//! The node admits the bytes only while the head still holds (same nonce, same
//! receipt head, deadline not passed), so the same bytes commit at most once.
//!
//! # The anchor witness
//!
//! The witness for "turn `H` anchored `(topic, payload)`" is the `SignedTurn`
//! bytes themselves, which are the prepared bytes. [`check_witness`] decodes
//! them, recomputes `H` with `Turn::hash`, checks both signature halves over
//! `H`, and finds the event and the memo. It changes no consensus byte and
//! adds no format: the path from the payload to the turn hash is recomputed by
//! the code that defines it, not described by a second encoding of it.
//!
//! Finality is a separate question with two strengths, and the checker keeps
//! them apart. A receipt row served by a node for `H` is the node's word. A
//! `TurnAnchorV1` (`GET /api/turn/{hash}/anchor`) verified against a committee
//! roster the checker already holds is the committee's signature over a
//! receipt whose hash commits `H` and the emitted events, and
//! [`check_anchor_discloses`] reads the event out of that signed receipt.
//!
//! One limit, stated: the event data words pack the payload 8 bytes per word
//! with zero padding, so the words alone do not distinguish a payload from
//! the same payload with trailing NUL bytes in its last word. The memo does,
//! and the memo is in the turn hash. A check through the witness is exact; a
//! check through the receipt's events alone is exact up to that padding.

use dregg_federation::turn_anchor::{AnchorCommittee, TurnAnchorV1};
use dregg_sdk::{AgentCipherclerk, CellId, SignedTurn};
use dregg_turn::action::{Action, Authorization, Effect, Event, symbol};
use dregg_turn::{ComputronCosts, Turn, TurnExecutor};

use crate::NodeHttpClient;

/// The low-lane payload packing: 8 bytes per 32-byte word, in `word[24..32]`.
/// A value confined to the low 8 bytes is a valid element of ANY field the
/// executors interpret words in (< 2^64), the same discipline the node's
/// Lean-authoritative state projection enforces for `SetField` lanes.
pub const LANE_LO: usize = 24;
/// Payload bytes carried per event data word.
pub const LANE_BYTES: usize = 8;
/// How many block heights past the node's `latest_height` a signed turn stays
/// admissible. `Turn::valid_until` is a block HEIGHT (the unit the verified
/// kernel reads, `Exec/Admission.lean`), so every verb stamps
/// `latest_height + TURN_VALID_FOR_HEIGHTS`: a turn refused for a reason that
/// leaves the nonce and head unchanged cannot be replayed once the node has
/// moved this far on. The node's height advances on turn-bearing finality, so
/// the window is counted in committed heights, not wall-clock time.
pub const TURN_VALID_FOR_HEIGHTS: u64 = 64;

/// Pack a payload into event data words.
pub fn pack_payload(payload: &[u8]) -> Vec<[u8; 32]> {
    payload
        .chunks(LANE_BYTES)
        .map(|chunk| {
            let mut word = [0u8; 32];
            word[LANE_LO..LANE_LO + chunk.len()].copy_from_slice(chunk);
            word
        })
        .collect()
}

/// The chat send's single action, UNSIGNED: one `EmitEvent` on `cell`.
pub fn chat_action(cell: CellId, topic: &str, payload: &str) -> Action {
    let effect = Effect::EmitEvent {
        cell,
        event: Event {
            topic: symbol(topic),
            data: pack_payload(payload.as_bytes()),
        },
    };
    dregg_sdk::raw::unsigned_action_named(cell, topic, vec![effect])
}

/// Wrap an already-authorized chat action in the send's turn envelope.
/// No signing happens here.
pub fn chat_turn(
    clerk: &AgentCipherclerk,
    cell: CellId,
    action: Action,
    nonce: u64,
    payload: &str,
    valid_until: i64,
) -> Turn {
    let mut turn = clerk.make_turn_with_actions(vec![action]);
    turn.agent = cell;
    turn.nonce = nonce;
    turn.memo = Some(payload.to_string());
    turn.valid_until = Some(valid_until);
    turn
}

/// The send turn with its action hybrid-signed, fee and receipt head unset.
pub fn build_chat_turn(
    clerk: &AgentCipherclerk,
    cell: CellId,
    topic: &str,
    payload: &str,
    federation_id: &[u8; 32],
    nonce: u64,
    valid_until: i64,
) -> Turn {
    let action = clerk.sign_action_hybrid(chat_action(cell, topic, payload), federation_id, nonce);
    chat_turn(clerk, cell, action, nonce, payload, valid_until)
}

/// The fee `build_chat_turn` would declare, computed WITHOUT signing.
///
/// `TurnExecutor::estimate_cost` reads the coordination class (effects and
/// `balance_change`), then per action `action_base`, the authorization
/// VARIANT (`HybridSignature` costs `2 * signature_verify`) and each effect's
/// cost. It never reads the nonce, the federation id, the memo, the deadline or
/// any signature byte. So a `HybridSignature` with empty placeholder halves
/// estimates exactly what the signed turn estimates, at any nonce. The test
/// `unsigned_fee_estimate_equals_the_signed_turns_fee` holds that equality
/// against a really signed turn, so a future fee rule that reads signature
/// bytes fails there, not in production.
pub fn chat_fee(
    clerk: &AgentCipherclerk,
    costs: ComputronCosts,
    cell: CellId,
    topic: &str,
    payload: &str,
) -> u64 {
    let placeholder = Action {
        authorization: Authorization::HybridSignature {
            ed25519: [0u8; 64],
            ml_dsa: Vec::new(),
            ml_dsa_pk: Vec::new(),
        },
        ..chat_action(cell, topic, payload)
    };
    TurnExecutor::new(costs).estimate_cost(&chat_turn(clerk, cell, placeholder, 0, payload, 0))
}

// ─────────────────────────────── the head ───────────────────────────────────

/// Everything a send turn takes from the node. With an identity, a topic and a
/// payload it determines the turn, byte for byte.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Head {
    /// The executor's federation id (the action signature binds it).
    pub federation_id: [u8; 32],
    /// The agent cell's nonce (the action signature and the turn bind it).
    pub nonce: u64,
    /// The node's latest height; the deadline is this plus
    /// [`TURN_VALID_FOR_HEIGHTS`].
    pub latest_height: u64,
    /// The head of THIS agent's receipt chain, `None` before its first turn.
    pub previous_receipt_hash: Option<[u8; 32]>,
    /// `/status.coordination_fee_exempt`.
    pub coordination_exempt: bool,
    /// `/status.coordination_exempt_ceiling`.
    pub coordination_exempt_ceiling: u64,
}

fn hex32(what: &str, value: &serde_json::Value) -> Result<[u8; 32], String> {
    let text = value
        .as_str()
        .ok_or_else(|| format!("head field {what} is not a string"))?;
    let bytes = hex::decode(text).map_err(|e| format!("head field {what}: {e}"))?;
    bytes
        .as_slice()
        .try_into()
        .map_err(|_| format!("head field {what} is {} bytes, not 32", bytes.len()))
}

impl Head {
    /// The cost model the declared fee is estimated against.
    pub fn cost_model(&self) -> ComputronCosts {
        let mut costs = ComputronCosts::default();
        costs.coordination_exempt = self.coordination_exempt;
        costs.coordination_exempt_ceiling = self.coordination_exempt_ceiling;
        costs
    }

    /// The JSON the `head` verb prints and `prepare --head` reads.
    pub fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "federation_id": hex::encode(self.federation_id),
            "nonce": self.nonce,
            "latest_height": self.latest_height,
            "previous_receipt_hash": self.previous_receipt_hash.map(hex::encode),
            "coordination_fee_exempt": self.coordination_exempt,
            "coordination_exempt_ceiling": self.coordination_exempt_ceiling,
        })
    }

    /// Read a head back. Every field is required and typed: a head with a
    /// missing or misspelt field would silently prepare a different turn.
    pub fn from_json(v: &serde_json::Value) -> Result<Self, String> {
        let u = |name: &str| {
            v.get(name)
                .and_then(|x| x.as_u64())
                .ok_or_else(|| format!("head field {name} is not an unsigned integer"))
        };
        let previous = v
            .get("previous_receipt_hash")
            .ok_or("head field previous_receipt_hash is absent (use null for none)")?;
        Ok(Head {
            federation_id: hex32(
                "federation_id",
                v.get("federation_id").unwrap_or(&serde_json::Value::Null),
            )?,
            nonce: u("nonce")?,
            latest_height: u("latest_height")?,
            previous_receipt_hash: if previous.is_null() {
                None
            } else {
                Some(hex32("previous_receipt_hash", previous)?)
            },
            coordination_exempt: v
                .get("coordination_fee_exempt")
                .and_then(|x| x.as_bool())
                .ok_or("head field coordination_fee_exempt is not a boolean")?,
            coordination_exempt_ceiling: u("coordination_exempt_ceiling")?,
        })
    }

    /// Read the head for `cell` from a node. Four GETs, no writes.
    pub async fn fetch(node: &NodeHttpClient, cell: &CellId) -> Result<Self, String> {
        let federation_id = node
            .fetch_executor_federation_id()
            .await
            .map_err(|e| format!("fetch executor federation id: {e}"))?;
        let class = node
            .fetch_coordination_class()
            .await
            .map_err(|e| format!("read the node's coordination class: {e}"))?;
        let nonce = node
            .fetch_cell_nonce(cell)
            .await
            .map_err(|e| format!("fetch own-cell nonce: {e}"))?;
        let latest_height = node
            .fetch_latest_height()
            .await
            .map_err(|e| format!("read the node's latest height for the turn deadline: {e}"))?;
        // THE AGENT'S OWN RECEIPT HEAD, not the node-wide tip. The node admits
        // a signed turn only when `previous_receipt_hash` equals the head of
        // THIS agent's chain, and the node-wide tip is another seat's receipt
        // whenever another seat committed since (see
        // `NodeHttpClient::fetch_agent_receipt_head`).
        let previous_receipt_hash = node
            .fetch_agent_receipt_head(cell)
            .await
            .map_err(|e| format!("fetch own-cell receipt head: {e}"))?;
        Ok(Head {
            federation_id,
            nonce,
            latest_height,
            previous_receipt_hash,
            coordination_exempt: class.exempt,
            coordination_exempt_ceiling: class.ceiling,
        })
    }
}

// ─────────────────────────────── prepare ────────────────────────────────────

/// A send turn signed and serialized, not yet submitted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Prepared {
    /// `Turn::hash` of the signed turn: the identity a receipt will carry.
    pub turn_hash: [u8; 32],
    /// The postcard `SignedTurn`, exactly as `/turns/submit` takes it. Also
    /// the anchor witness.
    pub bytes: Vec<u8>,
    /// The agent cell the turn acts as.
    pub agent: CellId,
    /// The nonce the turn binds.
    pub nonce: u64,
    /// The fee the turn declares.
    pub fee: u64,
    /// The height the turn is valid until.
    pub valid_until: i64,
}

/// Build, sign and serialize the send turn for `(clerk, head, topic, payload)`.
/// Pure: equal inputs give equal bytes.
pub fn prepare_send(
    clerk: &AgentCipherclerk,
    head: &Head,
    topic: &str,
    payload: &str,
) -> Result<Prepared, String> {
    let cell = clerk.cell_id("default");
    let valid_until = dregg_turn::valid_until_at(head.latest_height, TURN_VALID_FOR_HEIGHTS);
    let mut turn = build_chat_turn(
        clerk,
        cell,
        topic,
        payload,
        &head.federation_id,
        head.nonce,
        valid_until,
    );
    turn.fee = TurnExecutor::new(head.cost_model()).estimate_cost(&turn);
    turn.previous_receipt_hash = head.previous_receipt_hash;
    let signed = clerk.sign_turn(&turn);
    let bytes = postcard::to_stdvec(&signed).map_err(|e| format!("serialize SignedTurn: {e}"))?;
    Ok(Prepared {
        turn_hash: signed.turn.hash(),
        bytes,
        agent: cell,
        nonce: turn.nonce,
        fee: turn.fee,
        valid_until,
    })
}

/// Decode prepared bytes strictly: exactly one `SignedTurn`, nothing after it.
/// The node refuses trailing bytes too, so a file that decodes here is the
/// file the node will read.
pub fn decode_signed_turn(bytes: &[u8]) -> Result<SignedTurn, String> {
    match postcard::take_from_bytes::<SignedTurn>(bytes) {
        Ok((signed, [])) => Ok(signed),
        Ok((_, rest)) => Err(format!(
            "{} trailing bytes after the SignedTurn envelope",
            rest.len()
        )),
        Err(e) => Err(format!("not a postcard SignedTurn: {e}")),
    }
}

// ───────────────────────────── the anchor witness ───────────────────────────

/// What a witness establishes on its own, with no node.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WitnessFacts {
    /// `Turn::hash` recomputed from the witness. A receipt for this hash is a
    /// receipt for a turn carrying the event below.
    pub turn_hash: [u8; 32],
    /// The Ed25519 key whose signature over the turn hash verified.
    pub signer: [u8; 32],
    /// The ML-DSA-65 key whose signature over the turn hash verified. Carried
    /// in the witness; the node's admission is what ties it to the cell.
    pub ml_dsa_signer: Vec<u8>,
    /// The cell the turn acts as and emits on: the signer's default cell.
    pub agent: CellId,
    /// The turn's nonce.
    pub nonce: u64,
    /// The event topic word, `symbol(topic)`.
    pub topic: [u8; 32],
    /// The event data words, `pack_payload(payload)`.
    pub data: Vec<[u8; 32]>,
}

/// Why a witness does not establish the anchor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WitnessError {
    /// The bytes are not exactly one `SignedTurn`.
    Malformed(String),
    /// The caller expected another turn hash than the witness hashes to.
    AnotherTurn { expected: String, witness: String },
    /// The Ed25519 half does not verify over the turn hash.
    Ed25519Invalid,
    /// The ML-DSA-65 half is absent or does not verify over the turn hash.
    MlDsaInvalid,
    /// The turn's agent is not the signer's default cell.
    AgentIsNotTheSigner,
    /// No action of the turn emits `(topic, payload)` on the agent cell.
    EventAbsent,
    /// The event is there but the memo is not exactly the payload.
    MemoDiffers,
}

impl std::fmt::Display for WitnessError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            WitnessError::Malformed(why) => write!(f, "the witness is malformed: {why}"),
            WitnessError::AnotherTurn { expected, witness } => write!(
                f,
                "the witness is turn {witness}, not the expected turn {expected}"
            ),
            WitnessError::Ed25519Invalid => write!(
                f,
                "the witness's Ed25519 signature does not verify over its turn hash"
            ),
            WitnessError::MlDsaInvalid => write!(
                f,
                "the witness's ML-DSA-65 signature is absent or does not verify over its turn hash"
            ),
            WitnessError::AgentIsNotTheSigner => write!(
                f,
                "the witness turn's agent is not its signer's default cell"
            ),
            WitnessError::EventAbsent => write!(
                f,
                "no action of the witness turn emits this topic and payload on the agent cell"
            ),
            WitnessError::MemoDiffers => write!(
                f,
                "the witness turn emits the packed payload but its memo is not exactly this payload"
            ),
        }
    }
}

impl std::error::Error for WitnessError {}

/// Check that `witness` is a signed turn carrying `(topic, payload)`, and
/// return the turn hash it commits to. `expected_turn_hash`, when given, is
/// the hash the caller holds (from its row or a receipt) and must match.
///
/// `Ok(facts)` means: the bytes are one `SignedTurn`; `facts.turn_hash` is its
/// `Turn::hash`; both envelope signatures verify over that hash; the agent is
/// the signer's default cell; some action in the call forest carries
/// `EmitEvent { cell: agent, topic: symbol(topic), data: pack_payload(payload) }`;
/// and the memo is exactly `payload`.
pub fn check_witness(
    witness: &[u8],
    topic: &str,
    payload: &str,
    expected_turn_hash: Option<&[u8; 32]>,
) -> Result<WitnessFacts, WitnessError> {
    let signed = decode_signed_turn(witness).map_err(WitnessError::Malformed)?;
    let turn_hash = signed.turn.hash();
    if let Some(expected) = expected_turn_hash
        && *expected != turn_hash
    {
        return Err(WitnessError::AnotherTurn {
            expected: hex::encode(expected),
            witness: hex::encode(turn_hash),
        });
    }
    if !signed.signer.verify(&turn_hash, &signed.signature) {
        return Err(WitnessError::Ed25519Invalid);
    }
    dregg_sdk::install_verified_pq_cores();
    if !dregg_turn::pq::ml_dsa_verify(&signed.pq_signer, &turn_hash, &signed.pq_signature) {
        return Err(WitnessError::MlDsaInvalid);
    }
    let agent = signed.turn.agent;
    let default_token = *blake3::hash(b"default").as_bytes();
    if agent != CellId::derive_raw(&signed.signer.0, &default_token) {
        return Err(WitnessError::AgentIsNotTheSigner);
    }
    let want_topic = symbol(topic);
    let want_data = pack_payload(payload.as_bytes());
    let emits = signed.turn.call_forest.iter_dfs().any(|tree| {
        tree.action.effects.iter().any(|effect| {
            matches!(
                effect,
                Effect::EmitEvent { cell, event }
                    if *cell == agent && event.topic == want_topic && event.data == want_data
            )
        })
    });
    if !emits {
        return Err(WitnessError::EventAbsent);
    }
    if signed.turn.memo.as_deref() != Some(payload) {
        return Err(WitnessError::MemoDiffers);
    }
    Ok(WitnessFacts {
        turn_hash,
        signer: signed.signer.0,
        ml_dsa_signer: signed.pq_signer,
        agent,
        nonce: signed.turn.nonce,
        topic: want_topic,
        data: want_data,
    })
}

/// What a committee-verified anchor says about the witnessed turn.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AnchoredFacts {
    /// The receipt hash, recomputed from the receipt the committee signed.
    pub receipt_hash: [u8; 32],
    /// The finalized height.
    pub height: u64,
    /// Distinct committee members whose signature reaches the receipt.
    pub signers: usize,
    /// The quorum the committee requires.
    pub threshold: usize,
}

/// Check a `TurnAnchorV1` against `committee`, and that the receipt the
/// committee signed is the witnessed turn's and discloses the witnessed event.
///
/// The committee is the trust root. Passing the roster the node served makes
/// the node its own judge; the caller decides whether that is acceptable and
/// says so in what it reports.
pub fn check_anchor_discloses(
    anchor: &TurnAnchorV1,
    committee: &AnchorCommittee,
    facts: &WitnessFacts,
) -> Result<AnchoredFacts, String> {
    let verified = anchor
        .verify(committee)
        .map_err(|e| format!("the turn anchor does not verify against the committee: {e}"))?;
    if verified.turn_hash != facts.turn_hash {
        return Err(format!(
            "the anchor is for turn {}, not the witnessed turn {}",
            hex::encode(verified.turn_hash),
            hex::encode(facts.turn_hash)
        ));
    }
    if anchor.receipt.agent != facts.agent {
        return Err(format!(
            "the anchored receipt's agent {} is not the witnessed agent {}",
            hex::encode(anchor.receipt.agent.as_bytes()),
            hex::encode(facts.agent.as_bytes())
        ));
    }
    let disclosed = anchor
        .receipt
        .emitted_events
        .iter()
        .any(|ev| ev.cell == facts.agent && ev.topic == facts.topic && ev.data == facts.data);
    if !disclosed {
        return Err(
            "the committee-signed receipt does not list the witnessed event among its \
             emitted events"
                .to_string(),
        );
    }
    Ok(AnchoredFacts {
        receipt_hash: verified.receipt_hash,
        height: verified.height,
        signers: verified.receipt_quorum_signers,
        threshold: committee.threshold,
    })
}

#[cfg(test)]
mod tests {
    use dregg_turn::TurnReceipt;
    use dregg_turn::turn::EmittedEvent;
    use dregg_types::{
        AttestedRoot, FederationId, PublicKey, SigningKey, merkle_root_of_receipt_hashes, sign,
    };

    use super::*;

    fn clerk(byte: u8) -> AgentCipherclerk {
        dregg_pq_testkit::install_or_panic();
        AgentCipherclerk::from_seed([byte; 64])
    }

    fn head() -> Head {
        Head {
            federation_id: [9u8; 32],
            nonce: 4,
            latest_height: 100,
            previous_receipt_hash: Some([4u8; 32]),
            coordination_exempt: true,
            coordination_exempt_ceiling: 10_000,
        }
    }

    // ── prepare ─────────────────────────────────────────────────────────────

    #[test]
    fn prepare_is_a_function_of_identity_head_topic_and_payload() {
        let c = clerk(3);
        let a = prepare_send(&c, &head(), "helm.chat", "row digest 1").unwrap();
        // A second identity object from the same seed, and a head that went
        // through its JSON form: nothing else is an input.
        let again = prepare_send(
            &clerk(3),
            &Head::from_json(&head().to_json()).unwrap(),
            "helm.chat",
            "row digest 1",
        )
        .unwrap();
        assert_eq!(a, again, "equal inputs must give equal bytes and hash");

        // The hash is the hash of the bytes' turn, and the deadline is the
        // head's height plus the window.
        let signed = decode_signed_turn(&a.bytes).unwrap();
        assert_eq!(signed.turn.hash(), a.turn_hash);
        assert_eq!(a.valid_until, 100 + TURN_VALID_FOR_HEIGHTS as i64);
        assert_eq!(a.nonce, 4);
        assert_eq!(signed.turn.previous_receipt_hash, Some([4u8; 32]));

        // Each input moves the hash.
        let mut seen = std::collections::HashSet::from([a.turn_hash]);
        let moved: Vec<(&str, Prepared)> = vec![
            (
                "identity",
                prepare_send(&clerk(5), &head(), "helm.chat", "row digest 1").unwrap(),
            ),
            (
                "topic",
                prepare_send(&c, &head(), "helm.chat2", "row digest 1").unwrap(),
            ),
            (
                "payload",
                prepare_send(&c, &head(), "helm.chat", "row digest 2").unwrap(),
            ),
            (
                "nonce",
                prepare_send(
                    &c,
                    &Head { nonce: 5, ..head() },
                    "helm.chat",
                    "row digest 1",
                )
                .unwrap(),
            ),
            (
                "height",
                prepare_send(
                    &c,
                    &Head {
                        latest_height: 101,
                        ..head()
                    },
                    "helm.chat",
                    "row digest 1",
                )
                .unwrap(),
            ),
            (
                "receipt head",
                prepare_send(
                    &c,
                    &Head {
                        previous_receipt_hash: None,
                        ..head()
                    },
                    "helm.chat",
                    "row digest 1",
                )
                .unwrap(),
            ),
            (
                "federation",
                prepare_send(
                    &c,
                    &Head {
                        federation_id: [8u8; 32],
                        ..head()
                    },
                    "helm.chat",
                    "row digest 1",
                )
                .unwrap(),
            ),
            (
                "fee class",
                prepare_send(
                    &c,
                    &Head {
                        coordination_exempt: false,
                        ..head()
                    },
                    "helm.chat",
                    "row digest 1",
                )
                .unwrap(),
            ),
        ];
        for (what, p) in moved {
            assert!(
                seen.insert(p.turn_hash),
                "changing the {what} must change the turn hash"
            );
        }
    }

    #[test]
    fn a_head_with_a_missing_or_mistyped_field_is_refused() {
        let good = head().to_json();
        assert_eq!(Head::from_json(&good).unwrap(), head());
        let none = Head {
            previous_receipt_hash: None,
            ..head()
        };
        assert_eq!(Head::from_json(&none.to_json()).unwrap(), none);
        for field in [
            "federation_id",
            "nonce",
            "latest_height",
            "previous_receipt_hash",
            "coordination_fee_exempt",
            "coordination_exempt_ceiling",
        ] {
            let mut bad = good.clone();
            bad.as_object_mut().unwrap().remove(field);
            assert!(
                Head::from_json(&bad).is_err(),
                "a head without {field} must be refused"
            );
            let mut bad = good.clone();
            bad[field] = serde_json::json!([1]);
            assert!(
                Head::from_json(&bad).is_err(),
                "a head with an array {field} must be refused"
            );
        }
    }

    #[test]
    fn prepared_bytes_with_anything_after_them_do_not_decode() {
        let p = prepare_send(&clerk(3), &head(), "t", "p").unwrap();
        decode_signed_turn(&p.bytes).expect("the prepared bytes decode");
        let mut longer = p.bytes.clone();
        longer.push(0);
        assert!(
            decode_signed_turn(&longer)
                .unwrap_err()
                .contains("trailing")
        );
        assert!(decode_signed_turn(&p.bytes[..p.bytes.len() - 1]).is_err());
    }

    // ── the witness ─────────────────────────────────────────────────────────

    #[test]
    fn the_prepared_bytes_witness_their_topic_and_payload() {
        let c = clerk(3);
        let p = prepare_send(&c, &head(), "helm.chat", "row digest 1").unwrap();
        let facts = check_witness(&p.bytes, "helm.chat", "row digest 1", Some(&p.turn_hash))
            .expect("the honest witness holds");
        assert_eq!(facts.turn_hash, p.turn_hash);
        assert_eq!(facts.signer, c.public_key().0);
        assert_eq!(facts.agent, c.cell_id("default"));
        assert_eq!(facts.ml_dsa_signer, c.ml_dsa_public_bytes());
        // With no expected hash the witness still yields the hash to look up.
        assert_eq!(
            check_witness(&p.bytes, "helm.chat", "row digest 1", None).unwrap(),
            facts
        );
    }

    #[test]
    fn a_witness_for_another_payload_topic_or_turn_is_refused() {
        let c = clerk(3);
        let p = prepare_send(&c, &head(), "helm.chat", "row digest 1").unwrap();
        assert_eq!(
            check_witness(&p.bytes, "helm.chat", "row digest 2", None),
            Err(WitnessError::EventAbsent)
        );
        assert_eq!(
            check_witness(&p.bytes, "helm.chat2", "row digest 1", None),
            Err(WitnessError::EventAbsent)
        );
        // The witness of a DIFFERENT turn carrying the same payload does not
        // stand in for the turn whose receipt the auditor holds.
        let other = prepare_send(
            &c,
            &Head { nonce: 5, ..head() },
            "helm.chat",
            "row digest 1",
        )
        .unwrap();
        assert!(matches!(
            check_witness(
                &other.bytes,
                "helm.chat",
                "row digest 1",
                Some(&p.turn_hash)
            ),
            Err(WitnessError::AnotherTurn { .. })
        ));
    }

    #[test]
    fn a_payload_that_differs_only_in_trailing_nul_is_told_apart_by_the_memo() {
        // The packing is not injective on trailing NULs of the last word; the
        // memo is exact. This is the case the memo check exists for.
        assert_eq!(pack_payload(b"abc"), pack_payload(b"abc\0"));
        let p = prepare_send(&clerk(3), &head(), "t", "abc").unwrap();
        assert_eq!(
            check_witness(&p.bytes, "t", "abc\0", None),
            Err(WitnessError::MemoDiffers)
        );
    }

    #[test]
    fn a_witness_whose_content_was_altered_after_signing_is_refused() {
        let c = clerk(3);
        let p = prepare_send(&c, &head(), "helm.chat", "row digest 1").unwrap();
        // Swap in another payload, memo and event both, keeping the signatures.
        let mut signed = decode_signed_turn(&p.bytes).unwrap();
        let forged = build_chat_turn(
            &c,
            c.cell_id("default"),
            "helm.chat",
            "row digest 2",
            &[9u8; 32],
            4,
            signed.turn.valid_until.unwrap(),
        );
        signed.turn.call_forest = forged.call_forest;
        signed.turn.memo = forged.memo;
        let bytes = postcard::to_stdvec(&signed).unwrap();
        assert_eq!(
            check_witness(&bytes, "helm.chat", "row digest 2", None),
            Err(WitnessError::Ed25519Invalid),
            "the envelope signature is over the original hash"
        );
        // And against the hash the auditor holds, it is simply another turn.
        assert!(matches!(
            check_witness(&bytes, "helm.chat", "row digest 2", Some(&p.turn_hash)),
            Err(WitnessError::AnotherTurn { .. })
        ));

        // A stripped or bent PQ half is refused: the witness is hybrid.
        let mut stripped = decode_signed_turn(&p.bytes).unwrap();
        stripped.pq_signature.clear();
        assert_eq!(
            check_witness(
                &postcard::to_stdvec(&stripped).unwrap(),
                "helm.chat",
                "row digest 1",
                None
            ),
            Err(WitnessError::MlDsaInvalid)
        );

        // Someone else's envelope around this agent's turn.
        let mut resigned = clerk(5).sign_turn(&decode_signed_turn(&p.bytes).unwrap().turn);
        assert_eq!(
            check_witness(
                &postcard::to_stdvec(&resigned).unwrap(),
                "helm.chat",
                "row digest 1",
                None
            ),
            Err(WitnessError::AgentIsNotTheSigner)
        );
        resigned.signer = c.public_key();
        assert_eq!(
            check_witness(
                &postcard::to_stdvec(&resigned).unwrap(),
                "helm.chat",
                "row digest 1",
                None
            ),
            Err(WitnessError::Ed25519Invalid)
        );
        assert!(matches!(
            check_witness(b"not a turn", "t", "p", None),
            Err(WitnessError::Malformed(_))
        ));
    }

    // ── the committee anchor ────────────────────────────────────────────────

    const FEDERATION: FederationId = FederationId([0x5F; 32]);
    const BLOCK_ID: [u8; 32] = [0x81; 32];
    const HEIGHT: u64 = 42;

    fn member(seed: u8) -> (SigningKey, PublicKey) {
        let sk = SigningKey::from_bytes(&[seed; 32]);
        let pk = sk.public_key();
        (sk, pk)
    }

    /// The anchor a node serves for a receipt, signed by `signers`.
    fn anchor_for(receipt: TurnReceipt, signers: &[(SigningKey, PublicKey)]) -> TurnAnchorV1 {
        let mut attested = AttestedRoot {
            merkle_root: [0x33; 32],
            note_tree_root: None,
            nullifier_set_root: None,
            height: HEIGHT,
            timestamp: 1_800_000_000,
            blocklace_block_id: Some(BLOCK_ID),
            finality_round: Some(7),
            quorum_signatures: Vec::new(),
            threshold_qc: None,
            threshold: signers.len().max(1),
            federation_id: FEDERATION,
            receipt_stream_root: Some(merkle_root_of_receipt_hashes(&[receipt.receipt_hash()])),
            hybrid_quorum: Vec::new(),
        };
        let message = attested.signing_message();
        for (sk, pk) in signers {
            attested.quorum_signatures.push((*pk, sign(sk, &message)));
        }
        TurnAnchorV1 {
            protocol: dregg_federation::turn_anchor::TURN_ANCHOR_PROTOCOL_V1.to_string(),
            turn_hash: receipt.turn_hash,
            receipt,
            height: HEIGHT,
            block_id: BLOCK_ID,
            attested,
            served_committee: AnchorCommittee::default(),
        }
    }

    fn committee(signers: &[(SigningKey, PublicKey)]) -> AnchorCommittee {
        AnchorCommittee {
            ed25519: signers.iter().map(|(_, pk)| *pk).collect(),
            ml_dsa: Vec::new(),
            threshold: signers.len(),
            federation_id: FEDERATION,
        }
    }

    fn receipt_of(facts: &WitnessFacts) -> TurnReceipt {
        TurnReceipt {
            turn_hash: facts.turn_hash,
            agent: facts.agent,
            federation_id: FEDERATION.0,
            emitted_events: vec![EmittedEvent {
                cell: facts.agent,
                topic: facts.topic,
                data: facts.data.clone(),
            }],
            ..Default::default()
        }
    }

    #[test]
    fn a_committee_signed_receipt_that_lists_the_event_anchors_it() {
        let p = prepare_send(&clerk(3), &head(), "helm.chat", "row digest 1").unwrap();
        let facts = check_witness(&p.bytes, "helm.chat", "row digest 1", None).unwrap();
        let signers = vec![member(1), member(2)];
        let anchor = anchor_for(receipt_of(&facts), &signers);
        let anchored = check_anchor_discloses(&anchor, &committee(&signers), &facts)
            .expect("the honest anchor holds");
        assert_eq!(anchored.receipt_hash, anchor.receipt.receipt_hash());
        assert_eq!(anchored.height, HEIGHT);
        assert_eq!((anchored.signers, anchored.threshold), (2, 2));
    }

    #[test]
    fn an_anchor_that_does_not_reach_this_event_is_refused() {
        let p = prepare_send(&clerk(3), &head(), "helm.chat", "row digest 1").unwrap();
        let facts = check_witness(&p.bytes, "helm.chat", "row digest 1", None).unwrap();
        let signers = vec![member(1), member(2)];

        // A committee the signers are not in.
        let anchor = anchor_for(receipt_of(&facts), &signers);
        let strangers = vec![member(7), member(8)];
        let e = check_anchor_discloses(&anchor, &committee(&strangers), &facts).unwrap_err();
        assert!(e.contains("does not verify against the committee"), "{e}");

        // A validly signed receipt for ANOTHER turn.
        let mut other = receipt_of(&facts);
        other.turn_hash = [0xEE; 32];
        let e = check_anchor_discloses(&anchor_for(other, &signers), &committee(&signers), &facts)
            .unwrap_err();
        assert!(e.contains("not the witnessed turn"), "{e}");

        // A validly signed receipt for this turn hash that lists no such event,
        // or lists it with another data word, or on another cell.
        let mut empty = receipt_of(&facts);
        empty.emitted_events.clear();
        let mut bent = receipt_of(&facts);
        bent.emitted_events[0].data[0][31] ^= 1;
        let mut elsewhere = receipt_of(&facts);
        elsewhere.emitted_events[0].cell = CellId([0x77; 32]);
        for receipt in [empty, bent, elsewhere] {
            let e = check_anchor_discloses(
                &anchor_for(receipt, &signers),
                &committee(&signers),
                &facts,
            )
            .unwrap_err();
            assert!(e.contains("does not list the witnessed event"), "{e}");
        }

        // The receipt altered AFTER the committee signed: the recomputed
        // receipt hash leaves the attested stream.
        let mut tampered = anchor_for(receipt_of(&facts), &signers);
        tampered.receipt.emitted_events[0].data[0][31] ^= 1;
        let e = check_anchor_discloses(&tampered, &committee(&signers), &facts).unwrap_err();
        assert!(e.contains("does not verify against the committee"), "{e}");
    }
}
