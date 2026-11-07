//! **Actually VERIFY the fetched full-turn STARK — against something the committee signed.**
//!
//! `/proof turn` (and `/explorer proof`) fetch a committed turn's proof artifact off the node
//! (`/api/turn/{hash}/proof`) and re-run the SAME audited verifier a remote peer would
//! ([`dregg_sdk::verify_full_turn`]). This module is that check. It is NOT a "this turn happened"
//! verdict, and the surface must never render as one: read the seams below before touching
//! [`verdict_text`].
//!
//! # ⚑ THE ANCHOR IS A REQUIRED ARGUMENT
//!
//! Until 2026-08-06 this module passed the turn hash **from the request URL** and read the
//! before/after 8-felt commits **out of the artifact**, handing those straight back to the
//! verifier as the values it should expect. The two endpoint `CommitmentMismatch` teeth therefore
//! compared `x != x` and structurally could not fire.
//!
//! [`check_proof_hex`] now takes a [`CheckedAnchor`] — a
//! [`dregg_sdk::TurnAnchorV1`] fetched from `/api/turn/{hash}/anchor` and **verified in
//! this process against a committee roster** — and uses ITS turn hash. There is no unanchored
//! entry point: a caller that cannot obtain and verify an anchor cannot obtain a verdict from
//! here at all, which is the point. The same forcing shape `verify_full_turn_bound` uses for
//! `expected_turn_hash`.
//!
//! ## What that buys, precisely
//!
//! The anchor's turn hash comes out of a `TurnReceipt` whose `receipt_hash()` this process
//! recomputed, which roots the `receipt_stream_root` inside `AttestedRoot::signing_message()`,
//! over which `>= threshold` committee members signed. So the identity the artifact is judged
//! against is **the committee's**, not the URL's and not the artifact's. A proof served under
//! turn B, checked against turn A's anchor, is REFUSED — and a malicious *node* (as distinct from
//! a malicious committee) cannot forge the anchor to make it pass.
//!
//! ## What is (and is not) established
//!
//! * **Established:** the bytes ARE a sound composed STARK — every attached leg verifies under the
//!   audited Plonky3 verifier, the legs chain leg-to-leg (`chain_adjacency`, which DOES fire), the
//!   object binds one composed VK hash, and every effect-vm leg publishes the COMMITTEE-SIGNED
//!   turn hash at `pi::TURN_HASH_BASE`.
//! * **ESTABLISHED SINCE 2026-08-07, and it was seam 1: the two endpoint commitment teeth now
//!   FIRE.** `expected_old_commit` / `expected_new_commit` are no longer read out of the artifact.
//!   `GET /api/turn/{h}/anchor` serves `proof_state_commits` — the 8-felt pair the NODE derived at
//!   commit time (`RotationTurnWitness::wide_commit_anchors`, generate-only over the executor's
//!   trusted pre-state and the turn's effects, independent of the proof bytes, and gated on by
//!   `verify_full_turn_bound` before the artifact was published) — and [`check_proof_hex`] passes
//!   THAT. A proof whose published commitments disagree with the served pair is REFUSED with
//!   `CommitmentMismatch`. ⚑ There is no unbound entry point: an anchor carrying no pair
//!   (`proof_commit_status: "absent"`) yields **no verdict at all**, which is what a
//!   `sdk::cipherclerk` artifact gets — a ledgerless producer cannot compute this chain's
//!   whole-ledger context, so no honest pair exists to serve and none is invented.
//! * **NOT established, seam 1' (whose claim the bound pair is).** It is the NODE's, not the
//!   committee's. The committee signs `TurnReceipt::{pre,post}_state_hash`, a **different**
//!   commitment of the same transition — measured cause by cause in
//!   `turn/tests/receipt_state_commit_is_not_the_proof_state_commit.rs` (the receipt anchor uses
//!   `state_commit::consensus_ctx`: whole-ledger `cells_root`, `iroot = empty_iroot_8()`, the
//!   executor's live `revoked_root`, `Default` carrier material; the proof-side builders use a
//!   single-cell context ledger, a per-producer `iroot`, the empty revoked root, and a factory
//!   turn's installed `child_vk`). Feeding the receipt's pair here still refuses every honest
//!   proof. So what a malicious NODE can still do is serve a forged artifact together with a
//!   matching forged pair; what it can no longer do is serve an artifact whose own commitments
//!   contradict what its commit path derived. ⚑ **Undone work, not a theorem**: aligning the two
//!   `V9RotationContext`s is priced in `docs/DESIGN-pi-authority.md` §4(a).
//! * **NOT established, seam 2 (the identity is prover-CHOSEN, not prover-FORCED).** No AIR
//!   constraint reads those four felts — 0 of the 57 `WIDE_REGISTRY_STAGED_TSV` members bind a
//!   `pi_index` in `33..37` — so what the check forbids is RELABELLING an artifact. A malicious
//!   prover can still mint a fresh proof of some other transition and publish this turn's hash
//!   beside it. `docs/DESIGN-pi-authority.md` §3 argues this one is a **theorem of the model**
//!   (`Turn::hash` absorbs the proof bytes, so a sovereign proof can never publish it), not
//!   transmutable debt.
//! * **NOT established, seam 3 (how big the committee really is).** On the live path
//!   `AttestedRoot::quorum_signatures` receives exactly ONE push — the local node's — so on a
//!   federation with `threshold > 1` no anchor verifies at all and this command refuses. That
//!   refusal is the honest outcome, not a bug to route around. Closing it means putting
//!   `receipt_stream_root` into the finalization-vote preimage so the `>= threshold` hybrid vote
//!   quorum reaches the receipt. Also undone work.
//!
//! All three seams are reported at runtime, not only here: [`check_proof_hex`] fills
//! [`ProofCheck::unbound`] and [`verdict_text`] prints it under the verdict.

use dregg_circuit::effect_vm::pi as effect_pi;
use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
use dregg_circuit::field::BabyBear;
use dregg_dsl_runtime::composition::{AttachedSubProof, ComposedProof};
// The anchor types come through `dregg_sdk`'s re-export, not a direct
// `dregg-federation` edge: this bot is a SEPARATE cargo workspace whose lock cannot be
// re-resolved at HEAD (`dregg-storage`'s `poly-commitment` pins `rayon =1.10.0` while
// `p3-maybe-rayon` needs `^1.11`), so ANY new direct dependency here fails to resolve.
// That is a pre-existing wound, reproduced with an unrelated probe dep; the re-export
// routes around it without adding a twin.
use dregg_sdk::full_turn_proof::{FullTurnProof, TurnProofComponents};
use dregg_sdk::verify_full_turn;
use dregg_sdk::{AnchorCommittee, TurnAnchorV1, VerifiedTurnAnchor};

/// Where the committee roster an anchor was judged against came from. This is the difference
/// between "the committee signed it" and "a server told me who its judges are", and it must ride
/// with every verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RosterProvenance {
    /// From this bot's own configuration (`DREGG_COMMITTEE_ED25519` + `DREGG_COMMITTEE_THRESHOLD`
    /// + `DREGG_COMMITTEE_FEDERATION_ID`). The anchor was judged against a trust root the node
    /// serving it does not control.
    Configured,
    /// From the anchor itself (`TurnAnchorV1::served_committee`). The node named its own judges,
    /// so the signature check proves internal consistency and NOT committee authority.
    ServedByTheNode,
}

impl RosterProvenance {
    /// One line naming what this provenance does and does not buy — printed under the verdict.
    pub fn caveat(self) -> &'static str {
        match self {
            Self::Configured => {
                "The committee roster came from this bot's configuration, so the node serving the \
                 anchor did not get to name its own judges."
            }
            Self::ServedByTheNode => {
                "⚠ The committee roster came from the ANCHOR ITSELF — the node named its own \
                 judges. The signatures check out against keys that node published, which proves \
                 internal consistency and NOT committee authority. Set \
                 `DREGG_COMMITTEE_ED25519` / `DREGG_COMMITTEE_THRESHOLD` / \
                 `DREGG_COMMITTEE_FEDERATION_ID` from genesis to make this a real trust root."
            }
        }
    }
}

/// A verified anchor plus where its trust root came from. Constructed only by
/// [`verify_anchor_hex`], so holding one means the signature chain was checked here.
#[derive(Debug, Clone)]
pub struct CheckedAnchor {
    /// What the anchor established.
    pub verified: VerifiedTurnAnchor,
    /// Whose roster decided that.
    pub roster: RosterProvenance,
    /// ⚑ **The 8-felt `(old_commit, new_commit)` pair the SERVING NODE derived at commit time**,
    /// off the anchor response's `proof_state_commits`. This is what [`check_proof_hex`] passes to
    /// `verify_full_turn_bound` as `expected_old_commit` / `expected_new_commit`, replacing the
    /// values it used to read out of the artifact.
    ///
    /// `None` means the node published no bindable pair (`proof_commit_status: "absent"`) — a
    /// proof-carrying sovereign turn, an artifact minted by the ledgerless `sdk::cipherclerk`, a
    /// pre-cutover entry, or a node with proving disabled. [`check_proof_hex`] then REFUSES. It
    /// never falls back to the artifact's own values: that fallback IS the defect this closes.
    pub bindable_commits: Option<([BabyBear; 8], [BabyBear; 8])>,
}

/// Parse a committee roster from configuration strings. **Pure** — the fail-closed rule is
/// testable without touching the process environment.
///
/// `keys` is comma/whitespace-separated 64-hex ed25519 public keys; `threshold` a positive
/// integer; `federation_id` 64 hex. Any malformed or empty part is an error, never a silently
/// weaker roster: a roster that quietly loses a member lowers the bar it exists to raise.
pub fn parse_committee(
    keys: &str,
    threshold: &str,
    federation_id: &str,
) -> Result<AnchorCommittee, String> {
    let mut ed25519 = Vec::new();
    for tok in keys.split([',', ' ', '\t', '\n']).filter(|t| !t.is_empty()) {
        let bytes =
            hex::decode(tok).map_err(|e| format!("committee key `{tok}` is not hex: {e}"))?;
        let key: [u8; 32] = bytes
            .try_into()
            .map_err(|_| format!("committee key `{tok}` is not 32 bytes"))?;
        ed25519.push(dregg_types::PublicKey(key));
    }
    if ed25519.is_empty() {
        return Err("the committee roster is empty".into());
    }
    let threshold: usize = threshold
        .trim()
        .parse()
        .map_err(|e| format!("committee threshold is not a number: {e}"))?;
    if threshold == 0 {
        return Err("a zero committee threshold is not an authority".into());
    }
    let fed = hex::decode(federation_id.trim())
        .map_err(|e| format!("committee federation id is not hex: {e}"))?;
    let fed: [u8; 32] = fed
        .try_into()
        .map_err(|_| "committee federation id is not 32 bytes".to_string())?;
    Ok(AnchorCommittee {
        ed25519,
        // The hybrid CHAIN-POSITION leg is optional and never gates acceptance; leaving the
        // enrolled roster empty makes `verify` skip that leg rather than downgrade it.
        ml_dsa: Vec::new(),
        threshold,
        federation_id: dregg_types::FederationId(fed),
    })
}

/// The configured roster, if all three variables are present and well-formed.
///
/// A PARTIALLY configured roster is an error, not a fallback: an operator who set two of three
/// variables meant to configure a trust root, and silently serving them the node's own roster
/// instead is precisely the substitution this module exists to stop.
pub fn committee_from_env() -> Result<Option<AnchorCommittee>, String> {
    let keys = std::env::var("DREGG_COMMITTEE_ED25519").ok();
    let threshold = std::env::var("DREGG_COMMITTEE_THRESHOLD").ok();
    let fed = std::env::var("DREGG_COMMITTEE_FEDERATION_ID").ok();
    match (keys, threshold, fed) {
        (None, None, None) => Ok(None),
        (Some(k), Some(t), Some(f)) => parse_committee(&k, &t, &f).map(Some),
        _ => Err("DREGG_COMMITTEE_ED25519, DREGG_COMMITTEE_THRESHOLD and \
                  DREGG_COMMITTEE_FEDERATION_ID must be set together (a partly-configured \
                  committee is refused rather than silently replaced by the node's own roster)"
            .into()),
    }
}

/// **Verify a served anchor.** `anchor_hex` is the node's `anchor_hex` field (postcard-encoded
/// [`TurnAnchorV1`]). `bindable_commits` is the node's `proof_state_commits` pair, already parsed
/// (see [`parse_proof_state_commits`]) — passed explicitly, and never defaulted, so a call site
/// cannot end up with no pair by omission rather than by decision. `configured` is the caller's own
/// roster; when `None` the anchor's served roster is used and the result says so.
///
/// `Err` names which link of the custody chain failed, in the anchor type's own words.
pub fn verify_anchor_hex(
    anchor_hex: &str,
    bindable_commits: Option<([BabyBear; 8], [BabyBear; 8])>,
    configured: Option<&AnchorCommittee>,
) -> Result<CheckedAnchor, String> {
    let bytes = hex::decode(anchor_hex.trim())
        .map_err(|e| format!("the anchor hex does not decode: {e}"))?;
    let anchor: TurnAnchorV1 = postcard::from_bytes(&bytes)
        .map_err(|e| format!("the served bytes do not parse as a turn anchor: {e}"))?;
    let (committee, roster) = match configured {
        Some(c) => (c.clone(), RosterProvenance::Configured),
        None => (
            anchor.served_committee().clone(),
            RosterProvenance::ServedByTheNode,
        ),
    };
    let verified = anchor
        .verify(&committee)
        .map_err(|e| format!("the anchor does not verify: {e}"))?;
    Ok(CheckedAnchor {
        verified,
        roster,
        bindable_commits,
    })
}

/// Parse the anchor response's `proof_state_commits` object into the pair
/// [`check_proof_hex`] binds against. **Pure**, so the fail-closed rule is testable without a node.
///
/// `Ok(None)` is the honest absence — `proof_commit_status` is not `"derived"`, which is what a
/// `sdk::cipherclerk` artifact, a proof-carrying sovereign turn, or a pre-cutover entry produces.
/// `Err` is a MALFORMED pair: present but undecodable, wrong length, or a non-canonical lane. Those
/// are different facts and must not collapse — an absence is a node saying "I have nothing to bind
/// against", a malformation is a node saying something this checker could not read, and quietly
/// treating the second as the first would hide a broken (or hostile) server behind the same
/// refusal text.
pub fn parse_proof_state_commits(
    body: &serde_json::Value,
) -> Result<Option<([BabyBear; 8], [BabyBear; 8])>, String> {
    let status = body
        .get("proof_commit_status")
        .and_then(|v| v.as_str())
        .unwrap_or("absent");
    if status != "derived" {
        return Ok(None);
    }
    let commits = body.get("proof_state_commits").ok_or_else(|| {
        "proof_commit_status is `derived` but no `proof_state_commits`".to_string()
    })?;
    let field = |name: &str| -> Result<[BabyBear; 8], String> {
        let hexs = commits
            .get(name)
            .and_then(|v| v.as_str())
            .ok_or_else(|| format!("`proof_state_commits.{name}` is missing or not a string"))?;
        dregg_circuit::commit8_wire::commit8_from_hex(hexs).ok_or_else(|| {
            format!("`proof_state_commits.{name}` is not 64 hex characters of canonical lanes")
        })
    };
    Ok(Some((field("old_commit")?, field("new_commit")?)))
}

/// **Fetch and verify the anchor for `turn_hash_hex`.** ONE implementation, shared by every
/// command that reports on a proof, so no surface can quietly do the unanchored thing.
///
/// Uses the configured committee when one is set and the anchor's served roster otherwise; the
/// returned [`CheckedAnchor`] carries which, and [`verdict_text`] prints it.
pub async fn fetch_and_verify_anchor(
    client: &reqwest::Client,
    node_url: &str,
    turn_hash_hex: &str,
) -> Result<CheckedAnchor, String> {
    let configured = committee_from_env()?;
    let url = format!(
        "{}/api/turn/{turn_hash_hex}/anchor",
        node_url.trim_end_matches('/')
    );
    let resp = client
        .get(&url)
        .send()
        .await
        .map_err(|e| format!("could not reach the node for the anchor: {e}"))?;
    let status = resp.status().as_u16();
    let body: serde_json::Value = resp
        .json()
        .await
        .map_err(|e| format!("the anchor response is not JSON: {e}"))?;
    if status != 200 {
        let why = body
            .get("anchor_status")
            .and_then(|v| v.as_str())
            .unwrap_or("unknown");
        let detail = body.get("error").and_then(|v| v.as_str()).unwrap_or("");
        return Err(format!(
            "the node served no anchor (HTTP {status}, anchor_status `{why}`) {detail}"
        ));
    }
    let anchor_hex = body
        .get("anchor_hex")
        .and_then(|v| v.as_str())
        .ok_or_else(|| "the anchor response carries no `anchor_hex`".to_string())?
        .to_string();
    // The node's derived 8-felt pair, if it minted this turn's artifact. A malformed pair is an
    // ERROR here (it fails the whole fetch); an ABSENT one rides through as `None` so the refusal
    // is produced by `check_proof_hex`, which is where the reason belongs.
    let bindable_commits = parse_proof_state_commits(&body)?;
    let checked = verify_anchor_hex(&anchor_hex, bindable_commits, configured.as_ref())?;
    // The anchor must be for the turn we asked about. The node routes by hash, but a verdict is
    // not the place to take routing on trust.
    if hex::encode(checked.verified.turn_hash) != turn_hash_hex.trim().to_ascii_lowercase() {
        return Err(format!(
            "the node served an anchor for turn {} under the URL for {turn_hash_hex}",
            hex::encode(checked.verified.turn_hash)
        ));
    }
    Ok(checked)
}

/// The outcome of re-verifying a served proof artifact — everything the embed reports.
#[derive(Debug, Clone)]
pub struct ProofCheck {
    /// The audited verifier accepted the whole composed object.
    pub verified: bool,
    /// The composed circuit's VK hash (hex) the proof binds — which circuit the legs were
    /// checked against, not which turn they describe.
    pub vk_hex: String,
    /// The attached sub-proof legs, by label (what was actually verified).
    pub legs: Vec<String>,
    /// The pre-state 8-felt commit anchor the ARTIFACT PUBLISHES (hex lanes). Read out of the
    /// proof by [`extract_commits`]: it is what the prover said. Seam 1.
    pub published_old_commit: String,
    /// The post-state 8-felt commit anchor the ARTIFACT PUBLISHES (hex lanes). Same provenance
    /// caveat as [`ProofCheck::published_old_commit`].
    pub published_new_commit: String,
    /// The COMMITTEE-SIGNED 8-felt pre-state commit, from the anchor's receipt. Reported for the
    /// reader, never passed to the verifier — it is a different commitment (see the module docs).
    pub anchored_pre_state_commit: String,
    /// The committee-signed 8-felt post-state commit. Same.
    pub anchored_post_state_commit: String,
    /// ⚑ The pair actually PASSED to `verify_full_turn_bound` as `expected_old_commit` /
    /// `expected_new_commit` — the node's derived pair off the anchor response, NOT the artifact's.
    /// Reported so a reader can see that the two endpoint teeth had a real second value to compare
    /// against; when it equals [`ProofCheck::published_old_commit`] / `published_new_commit` the
    /// artifact agreed with what the node's commit path derived.
    pub bound_old_commit: String,
    /// The `expected_new_commit` actually passed. Same provenance.
    pub bound_new_commit: String,
    /// What the anchor established — the chain position and quorum this verdict rests on.
    pub anchor_summary: String,
    /// What this check did NOT establish, populated by [`check_proof_hex`] itself (see
    /// [`unbound_claims`]) so the surface cannot drift away from the code.
    pub unbound: Vec<String>,
    /// The verifier's failure detail when `verified == false` (empty on success).
    pub detail: String,
}

/// **The seams, as data.** What running [`check_proof_hex`] does NOT establish, in the order a
/// reader should meet them. A function, not a constant, because it is the code's own account of
/// its call site — change what [`check_proof_hex`] passes and this list is wrong.
pub fn unbound_claims(roster: RosterProvenance) -> Vec<String> {
    vec![
        String::from(
            "WHOSE claim the state-commit pair is. The two endpoint commitment checks DID fire \
             here — `expected_old_commit` / `expected_new_commit` came from the node's \
             `/anchor` response, derived by its commit path from the executor's trusted pre-state \
             and the turn's effects, not read out of the artifact. But that pair is the NODE's \
             assertion, not the COMMITTEE's. The committee signs the receipt's \
             `pre_state_hash`/`post_state_hash`, which is a DIFFERENT commitment of the same \
             transition (whole-ledger `cells_root`, pinned empty receipt-chain `iroot`, the \
             executor's live `revoked_root` and `Default` carrier material, against the proof \
             side's single-cell context ledger, per-producer `iroot`, empty revoked root and a \
             factory turn's installed child VK; measured cause by cause in \
             `turn/tests/receipt_state_commit_is_not_the_proof_state_commit.rs`), so passing it \
             would refuse every honest proof. A hostile NODE can therefore still serve a forged \
             artifact beside a matching forged pair. This is UNDONE WORK, not a theorem: it \
             closes when the executor's and the prover's rotation contexts are aligned to one \
             commit per turn.",
        ),
        String::from(
            "The turn identity is prover-CHOSEN, not prover-FORCED. This turn's hash came from a \
             committee-signed receipt and every effect-vm leg publishes it, welded in by \
             Fiat-Shamir — so a proof of a DIFFERENT turn served here is REFUSED. What is not \
             settled is that the transition proven is the one this turn asked for: no AIR \
             constraint reads those four felts, so a malicious prover could mint a proof of \
             something else and label it with this turn. `docs/DESIGN-pi-authority.md` §3 argues \
             this one is terminal — `Turn::hash` absorbs the proof bytes, so a sovereign proof \
             can never publish it.",
        ),
        format!(
            "How much committee is behind the anchor. Acceptance rested on signatures over \
             `AttestedRoot::signing_message()`, the only preimage that reaches the receipt — and \
             on the live path exactly ONE node ever signs it. The `>= threshold` hybrid vote \
             quorum signs `(block_id, merkle_root)` and reaches no receipt, so it cannot stand \
             in. {}",
            roster.caveat()
        ),
    ]
}

/// **Verify a served proof artifact against a verified anchor.**
///
/// `proof_hex` is the node's `proof_hex` field (the postcard-serialized `ComposedProof` the
/// commit path persisted); `anchor` is the committee-verified anchor for the turn it was fetched
/// for. **The turn hash comes from the anchor**, never from a URL and never from the artifact —
/// and since 2026-08-07 so does the 8-felt commit pair.
///
/// `Err` means either that the bytes could not be interpreted (not-a-proof) **or that the anchor
/// carries no bindable commit pair**. The second is not a softer outcome: without a pair the only
/// values available are the artifact's own, which is exactly the reflexive comparison this module
/// exists to stop, so there is no verdict to give.
///
/// `Ok(check)` carries the verifier's verdict either way.
pub fn check_proof_hex(proof_hex: &str, anchor: &CheckedAnchor) -> Result<ProofCheck, String> {
    // ⚑ NO UNBOUND PATH. Refuse before decoding anything: a caller must not be able to obtain a
    // verdict for an artifact this process cannot judge against an externally-obtained pair.
    let Some((expected_old, expected_new)) = anchor.bindable_commits else {
        return Err(
            "the node served no bindable state-commit pair for this turn \
             (`proof_commit_status` is not `derived`), so the only before/after commits available \
             would be the artifact's own — which is the reflexive comparison this check exists to \
             refuse. A ledgerless producer (`sdk::cipherclerk`) cannot compute this chain's \
             whole-ledger rotation context, so its artifacts have no honest pair to serve and none \
             is invented; a proof-carrying sovereign turn and a pre-cutover entry look the same \
             from here. NO VERDICT."
                .to_string(),
        );
    };
    let bytes =
        hex::decode(proof_hex.trim()).map_err(|e| format!("the proof hex does not decode: {e}"))?;
    let composed: ComposedProof = postcard::from_bytes(&bytes)
        .map_err(|e| format!("the served bytes do not parse as a composed full-turn proof: {e}"))?;

    let legs: Vec<String> = composed
        .sub_proofs
        .iter()
        .map(|sp| sp.label.clone())
        .collect();
    // Reconstruct the component flags from the attached legs — the same facts the prover set
    // them from (the wire form carries the legs; the flags are derived presence bits).
    let components = TurnProofComponents {
        has_state_transition: legs.iter().any(|l| l.starts_with("effect-vm")),
        has_membership: legs.iter().any(|l| l == "membership"),
        has_conservation: legs.iter().any(|l| l == "conservation"),
        // (has_non_revocation RETIRED — felt-width #11 fold-in: freshness is
        // in-circuit on the rotated note-spend leg, not a separate leg.)
        has_cap_membership: legs.iter().any(|l| l == "cap-membership"),
    };

    // The artifact's OWN anchors — read for REPORTING only since 2026-08-07. They used to be
    // handed straight back as the verifier's `expected_*`, which is what made the two endpoint
    // `CommitmentMismatch` teeth compare `x != x`. They are now one side of a real comparison:
    // `expected_old`/`expected_new` below come from the node's `/anchor` response.
    let (published_old, published_new) = extract_commits(&composed.sub_proofs)?;
    let vk_hex = hex::encode(composed.composed_vk_hash);

    // ⚑ THE EXTERNAL ANCHOR. The turn hash comes from the committee-signed receipt this process
    // verified — not the URL, not the artifact. `verify_full_turn` requires it and compares it
    // against the felts every effect-vm leg PUBLISHES at `pi::TURN_HASH_BASE` (bound into the
    // leg's Fiat-Shamir transcript at prove time), so a proof of a DIFFERENT turn is REFUSED.
    let turn_hash = anchor.verified.turn_hash;

    let proof = FullTurnProof {
        composed,
        components,
        turn_hash,
        proof_bytes: bytes,
    };
    // ⚑ THE ENDPOINT TEETH, WITH A SECOND VALUE TO BITE ON. `expected_old`/`expected_new` are the
    // node's derived pair, obtained from a route this process fetched itself. A proof whose wide
    // legs publish anything else fails with `CommitmentMismatch` — the refusal that structurally
    // could not fire while both arguments came out of the artifact.
    let (verified, detail) = match verify_full_turn(&proof, turn_hash, expected_old, expected_new) {
        Ok(()) => (true, String::new()),
        Err(e) => (false, format!("{e:?}")),
    };
    Ok(ProofCheck {
        verified,
        vk_hex,
        legs,
        published_old_commit: commit_hex(&published_old),
        published_new_commit: commit_hex(&published_new),
        anchored_pre_state_commit: hex::encode(anchor.verified.receipt_pre_state_commit),
        anchored_post_state_commit: hex::encode(anchor.verified.receipt_post_state_commit),
        bound_old_commit: commit_hex(&expected_old),
        bound_new_commit: commit_hex(&expected_new),
        anchor_summary: anchor_summary(anchor),
        unbound: unbound_claims(anchor.roster),
        detail,
    })
}

/// One line describing what the anchor established, for the embed.
pub fn anchor_summary(anchor: &CheckedAnchor) -> String {
    let v = &anchor.verified;
    format!(
        "turn `{turn}…` finalized at height {h}, block `{blk}…`, ledger root `{root}…`; \
         {sig}/{th} committee signature(s) over the receipt-covering preimage, and the \
         chain-position hybrid quorum {pos}.",
        turn = &hex::encode(v.turn_hash)[..16],
        h = v.height,
        blk = &hex::encode(v.block_id)[..16],
        root = &hex::encode(v.ledger_root)[..16],
        sig = v.receipt_quorum_signers,
        th = v.threshold,
        pos = if v.position_quorum_met {
            "also verified"
        } else {
            "did NOT verify (it reaches no receipt either way)"
        },
    )
}

/// The async face: run [`check_proof_hex`] on a blocking thread (a STARK verify is real CPU
/// work, not something for a Discord worker's async slot).
pub async fn check_proof_hex_blocking(
    proof_hex: String,
    anchor: CheckedAnchor,
) -> Result<ProofCheck, String> {
    tokio::task::spawn_blocking(move || check_proof_hex(&proof_hex, &anchor))
        .await
        .unwrap_or_else(|e| Err(format!("the verifier task did not complete: {e}")))
}

/// The proof's own published (before, after) 8-felt commit anchors — read exactly the way
/// `verify_full_turn_bound` binds them: a WIDE rotated leg (its `vk_hash` is a wide-registry
/// descriptor fingerprint) publishes the full 8-felt commits as the LAST 16 PIs; a narrow
/// cap-open leg carries a single felt at `pi::OLD_COMMIT`/`pi::NEW_COMMIT`, broadcast into
/// slot 0. First leg's BEFORE + last leg's AFTER are the turn's endpoints.
///
/// ⚠ Because this is the SAME rule `verify_full_turn_bound` applies internally, feeding this
/// result back in as the verifier's `expected_*` makes its endpoint comparison REFLEXIVE — which
/// is what this module did until 2026-08-07. It is now read for REPORTING ONLY: the values passed
/// to the verifier are [`CheckedAnchor::bindable_commits`], obtained from the node's `/anchor`
/// route. **Do not restore this as the `expected_*` argument.**
fn extract_commits(subs: &[AttachedSubProof]) -> Result<([BabyBear; 8], [BabyBear; 8]), String> {
    let legs: Vec<&AttachedSubProof> = subs
        .iter()
        .filter(|sp| sp.label == "effect-vm" || sp.label == "effect-vm-rotated")
        .collect();
    if legs.is_empty() {
        return Err("the proof carries no effect-vm leg (nothing binds the state commits)".into());
    }
    let (before, _) = leg_commit(legs[0])?;
    let (_, after) = leg_commit(legs[legs.len() - 1])?;
    Ok((before, after))
}

/// Whether a leg bound a WIDE descriptor: its `vk_hash` is the blake3 fingerprint of a
/// committed wide-registry descriptor row (the SAME classification the SDK verifier uses).
fn leg_is_wide(leg: &AttachedSubProof) -> bool {
    WIDE_REGISTRY_STAGED_TSV.lines().any(|line| {
        line.splitn(3, '\t')
            .nth(2)
            .map(|json| blake3::hash(json.as_bytes()).as_bytes() == &leg.vk_hash)
            .unwrap_or(false)
    })
}

/// One leg's (before8, after8) commit anchors at the leg's true width.
fn leg_commit(leg: &AttachedSubProof) -> Result<([BabyBear; 8], [BabyBear; 8]), String> {
    let n = leg.sub_public_inputs.len();
    if leg_is_wide(leg) {
        if n < 16 {
            return Err(format!(
                "wide effect-vm leg too short for the 8-felt commit tail: {n} PIs < 16"
            ));
        }
        let before: [BabyBear; 8] = leg.sub_public_inputs[n - 16..n - 8]
            .try_into()
            .expect("slice of len 8");
        let after: [BabyBear; 8] = leg.sub_public_inputs[n - 8..n]
            .try_into()
            .expect("slice of len 8");
        Ok((before, after))
    } else {
        if n <= effect_pi::NEW_COMMIT {
            return Err(format!(
                "narrow effect-vm leg too short for its commit felts: {n} PIs"
            ));
        }
        let mut before = [BabyBear::ZERO; 8];
        let mut after = [BabyBear::ZERO; 8];
        before[0] = leg.sub_public_inputs[effect_pi::OLD_COMMIT];
        after[0] = leg.sub_public_inputs[effect_pi::NEW_COMMIT];
        Ok((before, after))
    }
}

/// An 8-felt commit anchor as one hex string (8 lanes × 8 hex chars).
fn commit_hex(felts: &[BabyBear; 8]) -> String {
    felts.iter().map(|f| format!("{:08x}", f.0)).collect()
}

/// The embed field reporting the verdict — the honest register, pure so tests read it.
///
/// The success arm leads with the LIMIT, not with a checkmark: what passed is a check on the
/// bytes against a committee-signed IDENTITY, and the fact a reader actually wants — that these
/// bytes prove the chain's state transition — is still in [`ProofCheck::unbound`].
pub fn verdict_text(check: &Result<ProofCheck, String>) -> String {
    match check {
        Ok(c) if c.verified => format!(
            "**A LIMITED CHECK PASSED. This is not a claim that the chain's state moved the way \
             these bytes describe.**\nEstablished: every attached leg ({legs}) verifies under the \
             same audited Plonky3 verifier a remote peer would run \
             (`dregg_sdk::verify_full_turn`), the legs chain leg to leg (each leg's BEFORE anchor \
             equals the previous leg's AFTER), the object binds the composed VK `{vk}…`, \
             every leg publishes the turn hash **taken from a committee-signed anchor this bot \
             verified itself** — not from the URL and not from the artifact — so a proof of \
             another turn served here is refused, and **the artifact's before/after state \
             commitments were compared against a pair fetched from the node's `/anchor` route \
             rather than read back out of the artifact**, so the two endpoint commitment checks \
             genuinely fired. Checked just now over the fetched bytes, not trusted.\nAnchor: \
             {anchor}\nBOUND against (the node's derived pair, `expected_old`/`expected_new`): \
             `{bold}…` → `{bnew}…`.\nAnchors the artifact PUBLISHES (the prover's claim, and they \
             matched): `{old}…` → `{new}…`.\nCommittee-signed state commits (the receipt's — a \
             DIFFERENT commitment of the same transition, reported and never bound against): \
             `{apre}…` → `{apost}…`.\nNOT established:\n{unbound}",
            vk = &c.vk_hex[..16.min(c.vk_hex.len())],
            legs = if c.legs.is_empty() {
                "(none)".to_string()
            } else {
                c.legs.join(", ")
            },
            anchor = c.anchor_summary,
            apre = &c.anchored_pre_state_commit[..16.min(c.anchored_pre_state_commit.len())],
            apost = &c.anchored_post_state_commit[..16.min(c.anchored_post_state_commit.len())],
            bold = &c.bound_old_commit[..16.min(c.bound_old_commit.len())],
            bnew = &c.bound_new_commit[..16.min(c.bound_new_commit.len())],
            old = &c.published_old_commit[..16.min(c.published_old_commit.len())],
            new = &c.published_new_commit[..16.min(c.published_new_commit.len())],
            unbound = if c.unbound.is_empty() {
                "(the unbound list is EMPTY, which is itself a bug: this call site has three \
                 standing seams, see `proof_verify`'s docblock)"
                    .to_string()
            } else {
                c.unbound
                    .iter()
                    .map(|u| format!("• {u}"))
                    .collect::<Vec<_>>()
                    .join("\n")
            },
        ),
        Ok(c) => format!(
            "✗ **The fetched bytes DO NOT verify** under VK `{vk}…` against the committee-signed \
             anchor and the node's derived state-commit pair. Do not trust this \
             artifact.\nAnchor: {anchor}\nBOUND against: `{bold}…` → `{bnew}…`.\nThe artifact \
             PUBLISHES: `{old}…` → `{new}…`.\n`{detail}`\n(A `CommitmentMismatch` here means the \
             artifact's own before/after commitments contradict what the serving node's commit \
             path derived for this turn — the check that could not fire before 2026-08-07.)",
            vk = &c.vk_hex[..16.min(c.vk_hex.len())],
            anchor = c.anchor_summary,
            bold = &c.bound_old_commit[..16.min(c.bound_old_commit.len())],
            bnew = &c.bound_new_commit[..16.min(c.bound_new_commit.len())],
            old = &c.published_old_commit[..16.min(c.published_old_commit.len())],
            new = &c.published_new_commit[..16.min(c.published_new_commit.len())],
            detail = c.detail,
        ),
        Err(e) => format!(
            "**No verdict.** This bot refuses to report on an artifact it cannot judge against \
             values it obtained independently.\nWhat failed: {e}"
        ),
    }
}

/// What to say when there is no verifiable anchor. **Not a verdict** — the whole point of making
/// the anchor a required argument is that this path cannot produce one.
pub fn no_anchor_text(turn_hash_hex: &str, why: &str) -> String {
    format!(
        "**No verdict.** This bot refuses to report on a proof artifact it cannot bind to a \
         committee-signed anchor, because without one the check would compare the artifact \
         against values read out of the artifact.\nWhat failed: {why}\nWhat to do: fetch \
         `/api/turn/{turn_hash_hex}/anchor` yourself and read which link of the custody chain it \
         names — receipt↔turn, receipt↔attested stream, or the committee quorum over the \
         receipt-covering preimage. A `ReceiptQuorumNotMet` here is the expected answer on a \
         federation with more than one validator: only the local node ever signs the preimage \
         that reaches a receipt."
    )
}

/// The re-check-it-yourself incantation — verification must be possible OUTSIDE the bot.
///
/// It names BOTH fetches, because the interesting part of `verify_full_turn` is its ARGUMENTS:
/// reproduce the bot's calls exactly and you reproduce the bot's seams.
pub fn offline_recheck_text(node_url: &str, turn_hash_hex: &str) -> String {
    format!(
        "```\ncurl {base}/api/turn/{turn_hash_hex}/anchor | jq '{{anchor_hex, \
         proof_commit_status, proof_state_commits}}'\ncurl \
         {base}/api/turn/{turn_hash_hex}/proof  | jq -r .proof_hex\n```\nDecode the anchor hex \
         into `dregg_federation::TurnAnchorV1` and call `.verify(&committee)` with a roster you \
         got from GENESIS, not from the node — it recomputes the receipt hash, re-roots it into \
         the attestation's `receipt_stream_root`, and checks `>= threshold` committee signatures \
         over `AttestedRoot::signing_message()`. Then hand the proof bytes, the VERIFIED anchor's \
         `turn_hash`, and the two octets from `proof_state_commits` (parse with \
         `dregg_circuit::commit8_wire::commit8_from_hex`) to `dregg_sdk::verify_full_turn` \
         (`sdk/src/full_turn_proof.rs`).\nMind the ARGUMENTS, because they are what the check IS. \
         The turn-hash argument is committee-signed: every leg publishes it. The two 8-felt commit \
         arguments come from `proof_state_commits`, which the node DERIVED at commit time from its \
         executor's trusted pre-state — so the comparison is real, and it is the NODE's word \
         rather than the committee's. If `proof_commit_status` is `absent` there is no bindable \
         pair: REFUSE, do not read the pair out of the artifact (that is the reflexive comparison \
         this route exists to end). The anchor's committee-signed `pre_state_hash` / \
         `post_state_hash` are a DIFFERENT commitment of the same transition and passing them \
         refuses every honest proof — see \
         `turn/tests/receipt_state_commit_is_not_the_proof_state_commit.rs`.",
        base = node_url.trim_end_matches('/'),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn an_octet(seed: u32) -> [BabyBear; 8] {
        let mut o = [BabyBear::ZERO; 8];
        for (i, l) in o.iter_mut().enumerate() {
            *l = BabyBear::new(seed.wrapping_mul(i as u32 + 3).wrapping_add(1));
        }
        o
    }

    fn a_checked_anchor(roster: RosterProvenance) -> CheckedAnchor {
        a_checked_anchor_with(roster, Some((an_octet(5), an_octet(9))))
    }

    fn a_checked_anchor_with(
        roster: RosterProvenance,
        bindable_commits: Option<([BabyBear; 8], [BabyBear; 8])>,
    ) -> CheckedAnchor {
        CheckedAnchor {
            verified: VerifiedTurnAnchor {
                turn_hash: [0xAB; 32],
                receipt_hash: [0xCD; 32],
                height: 42,
                block_id: [0x81; 32],
                ledger_root: [0x33; 32],
                receipt_pre_state_commit: [0x11; 32],
                receipt_post_state_commit: [0x22; 32],
                receipt_quorum_signers: 1,
                position_quorum_met: false,
                threshold: 1,
            },
            roster,
            bindable_commits,
        }
    }

    /// Garbage hex / not-a-proof bytes fail LOUDLY (an Err naming why), never a silent ✅.
    #[test]
    fn garbage_bytes_fail_loudly() {
        let anchor = a_checked_anchor(RosterProvenance::Configured);
        let err = check_proof_hex("zz-not-hex", &anchor).expect_err("non-hex must not verify");
        assert!(err.contains("does not decode"), "{err}");

        let err = check_proof_hex(&"ab".repeat(40), &anchor)
            .expect_err("random bytes must not parse as a composed proof");
        assert!(err.contains("do not parse"), "{err}");
    }

    /// ⚑ **THE `cipherclerk` BOUNDARY, AS A REFUSAL.** An anchor with no derived pair yields NO
    /// VERDICT — not a softened one, and above all not a fallback to the artifact's own commits.
    /// The refusal fires BEFORE the bytes are even decoded, so it cannot be reached around by
    /// handing this function a well-formed proof.
    #[test]
    fn an_anchor_with_no_bindable_pair_yields_no_verdict() {
        let anchor = a_checked_anchor_with(RosterProvenance::Configured, None);
        let err = check_proof_hex(&"ab".repeat(40), &anchor)
            .expect_err("no bindable pair must produce no verdict");
        assert!(err.contains("no bindable state-commit pair"), "{err}");
        assert!(err.contains("cipherclerk"), "{err}");
        assert!(err.contains("NO VERDICT"), "{err}");
        // …and it refuses before parsing, so the message is about the PAIR, not about the bytes.
        assert!(!err.contains("do not parse"), "{err}");
    }

    /// Garbage anchor bytes fail LOUDLY too — an anchor that does not parse must never fall back
    /// to "check it unanchored".
    #[test]
    fn a_malformed_anchor_yields_no_verdict() {
        let err =
            verify_anchor_hex("zz-not-hex", None, None).expect_err("non-hex anchor must refuse");
        assert!(err.contains("does not decode"), "{err}");
        let err = verify_anchor_hex(&"ab".repeat(40), None, None)
            .expect_err("random bytes must not parse");
        assert!(err.contains("do not parse"), "{err}");
    }

    /// The `proof_state_commits` parser separates the three outcomes a node can produce, because
    /// collapsing them would hide a broken server behind the honest-absence refusal.
    #[test]
    fn the_served_commit_pair_parser_separates_absent_from_malformed() {
        let (old, new) = (an_octet(31), an_octet(77));
        let good = serde_json::json!({
            "proof_commit_status": "derived",
            "proof_state_commits": {
                "old_commit": dregg_circuit::commit8_wire::commit8_to_hex(&old),
                "new_commit": dregg_circuit::commit8_wire::commit8_to_hex(&new),
            },
        });
        assert_eq!(
            parse_proof_state_commits(&good).expect("a well-formed pair parses"),
            Some((old, new))
        );

        // ABSENT — the honest "I minted nothing for this turn".
        let absent = serde_json::json!({ "proof_commit_status": "absent",
                                         "proof_state_commits": serde_json::Value::Null });
        assert_eq!(
            parse_proof_state_commits(&absent).expect("absent is Ok"),
            None
        );
        // A response with no status field at all is absent, never "derived by default".
        assert_eq!(
            parse_proof_state_commits(&serde_json::json!({})).expect("no field is Ok"),
            None
        );

        // MALFORMED — `derived` with nothing / garbage behind it is an ERROR, not an absence.
        let claimed = serde_json::json!({ "proof_commit_status": "derived" });
        assert!(parse_proof_state_commits(&claimed).is_err());
        let junk = serde_json::json!({
            "proof_commit_status": "derived",
            "proof_state_commits": { "old_commit": "zz", "new_commit": "zz" },
        });
        assert!(parse_proof_state_commits(&junk).is_err());
    }

    /// A partly-configured committee is an ERROR, not a silent fallback to the node's own roster.
    /// This is the substitution the whole module exists to stop, in its cheapest form.
    #[test]
    fn a_partly_configured_committee_is_refused() {
        // Pure parse-level equivalents of the env combinations, so the test touches no globals.
        assert!(parse_committee("", "1", &"00".repeat(32)).is_err());
        assert!(parse_committee(&"ab".repeat(32), "0", &"00".repeat(32)).is_err());
        assert!(parse_committee(&"ab".repeat(32), "1", "not-hex").is_err());
        assert!(parse_committee("nothex", "1", &"00".repeat(32)).is_err());
        assert!(parse_committee(&"ab".repeat(31), "1", &"00".repeat(32)).is_err());

        let ok = parse_committee(
            &format!("{},{}", "ab".repeat(32), "cd".repeat(32)),
            "2",
            &"11".repeat(32),
        )
        .expect("a well-formed roster parses");
        assert_eq!(ok.ed25519.len(), 2);
        assert_eq!(ok.threshold, 2);
        assert_eq!(ok.federation_id.0, [0x11; 32]);
    }

    fn a_passing_check(roster: RosterProvenance) -> ProofCheck {
        let anchor = a_checked_anchor(roster);
        ProofCheck {
            verified: true,
            vk_hex: "de3f".repeat(16),
            legs: vec!["effect-vm-rotated".into(), "membership".into()],
            published_old_commit: "11".repeat(32),
            published_new_commit: "22".repeat(32),
            anchored_pre_state_commit: "33".repeat(32),
            anchored_post_state_commit: "44".repeat(32),
            bound_old_commit: "11".repeat(32),
            bound_new_commit: "22".repeat(32),
            anchor_summary: anchor_summary(&anchor),
            unbound: unbound_claims(roster),
            detail: String::new(),
        }
    }

    /// The verdict register is honest in all three shapes: verified / refuted / uncheckable.
    #[test]
    fn the_verdict_text_carries_the_honest_register() {
        let ok = a_passing_check(RosterProvenance::Configured);
        let text = verdict_text(&Ok(ok.clone()));
        assert!(
            text.contains("Checked just now over the fetched bytes, not trusted"),
            "{text}"
        );
        assert!(text.contains("effect-vm-rotated"), "{text}");

        let bad = ProofCheck {
            verified: false,
            detail: "MainProofInvalid".into(),
            ..ok
        };
        let text = verdict_text(&Ok(bad));
        assert!(text.contains("DO NOT verify"), "{text}");
        assert!(text.contains("MainProofInvalid"), "{text}");

        // An `Err` is a REFUSAL, not a soft failure: it must read as "no verdict", because the
        // commonest Err is now "this node served no bindable pair".
        let text = verdict_text(&Err("boom".into()));
        assert!(text.contains("**No verdict.**"), "{text}");
        assert!(text.contains("boom"), "{text}");
        assert!(!text.contains("LIMITED CHECK PASSED"), "{text}");
    }

    /// ⚑ **THE TOOTH IS VISIBLE IN THE VERDICT.** A passing check must show BOTH sides of the
    /// endpoint comparison — the pair it bound against and the pair the artifact published — and a
    /// failing one must name the mismatch as a contradiction with the node's own derivation. A
    /// reader has no other way to tell a real comparison from the reflexive one it replaced.
    #[test]
    fn the_verdict_shows_the_pair_it_bound_against() {
        let ok = a_passing_check(RosterProvenance::Configured);
        let text = verdict_text(&Ok(ok.clone()));
        assert!(text.contains("BOUND against"), "{text}");
        assert!(
            text.contains("rather than read back out of the artifact"),
            "{text}"
        );

        let mismatched = ProofCheck {
            verified: false,
            detail: "CommitmentMismatch".into(),
            published_old_commit: "ee".repeat(32),
            ..ok
        };
        let text = verdict_text(&Ok(mismatched));
        assert!(text.contains("CommitmentMismatch"), "{text}");
        assert!(text.contains("BOUND against"), "{text}");
        assert!(
            text.contains("could not fire before"),
            "the failing arm must say what this check newly catches: {text}"
        );
    }

    /// **The anti-checkmark test.** A passing check must NOT read as "this proof is verified":
    /// the limit comes FIRST, and all three standing seams are printed in the body.
    #[test]
    fn a_passing_verdict_leads_with_the_limit_and_prints_every_seam() {
        let text = verdict_text(&Ok(a_passing_check(RosterProvenance::Configured)));

        assert!(
            !text.contains("Verifies under VK"),
            "the unqualified verified-claim came back: {text}"
        );
        let limit = text
            .find("A LIMITED CHECK PASSED")
            .expect("the success arm must state the limit");
        assert_eq!(limit, 2, "the limit must be the FIRST thing read: {text}");
        assert!(
            limit < text.find("Established").expect("what passed is named"),
            "the limit must precede the claim: {text}"
        );
        assert!(text.contains("NOT established:"), "{text}");
        // The anchor must be visible in the verdict, not merely used.
        assert!(text.contains("committee-signed anchor this bot"), "{text}");

        for u in unbound_claims(RosterProvenance::Configured) {
            assert!(
                text.contains(&u),
                "unbound entry dropped from the verdict: {u}"
            );
        }
    }

    /// The seam list is EXACTLY the three standing seams, and `ProofCheck` carries it as DATA
    /// (not as prose in one format string a later edit can quietly drop).
    #[test]
    fn the_unbound_list_names_exactly_the_three_standing_seams() {
        let unbound = unbound_claims(RosterProvenance::Configured);
        assert_eq!(unbound.len(), 3, "{unbound:#?}");
        // ⚑ Entry 0 is no longer "the comparison is reflexive" — that seam CLOSED. It is now
        // "whose claim the bound pair is", and the test pins the distinction so a regression back
        // to reading the pair out of the artifact cannot leave this list looking right.
        assert!(
            unbound[0].contains("The two endpoint commitment checks DID fire")
                && unbound[0].contains("not read out of the artifact"),
            "entry 0 must record that the endpoint teeth now fire: {}",
            unbound[0]
        );
        assert!(
            unbound[0].contains("the NODE's assertion, not the COMMITTEE's"),
            "entry 0 must name whose claim the bound pair is: {}",
            unbound[0]
        );
        // ⚑ And it must classify itself: undone work, never an "honestly labelled" terminal.
        assert!(
            unbound[0].contains("UNDONE WORK, not a theorem"),
            "entry 0 must say the remaining seam is transmutable: {}",
            unbound[0]
        );
        assert!(
            unbound[1].contains("prover-CHOSEN, not prover-FORCED")
                && unbound[1].contains("no AIR constraint reads those four felts"),
            "entry 1 must name what the turn-hash binding does NOT force: {}",
            unbound[1]
        );
        assert!(
            unbound[2].contains("exactly ONE node ever signs it"),
            "entry 2 must name how much committee is actually behind the anchor: {}",
            unbound[2]
        );
        assert_eq!(
            a_passing_check(RosterProvenance::Configured).unbound,
            unbound
        );
    }

    /// ⚑ A node-served roster must SAY it is a node-served roster, in the verdict a reader sees.
    #[test]
    fn a_node_served_roster_is_confessed_in_the_verdict() {
        let text = verdict_text(&Ok(a_passing_check(RosterProvenance::ServedByTheNode)));
        assert!(
            text.contains("the node named its own judges"),
            "a served roster must be confessed: {text}"
        );
        assert!(
            text.contains("DREGG_COMMITTEE_ED25519"),
            "and it must say how to fix it: {text}"
        );
        // The configured case must NOT carry that confession.
        let configured = verdict_text(&Ok(a_passing_check(RosterProvenance::Configured)));
        assert!(
            !configured.contains("the node named its own judges"),
            "a configured roster must not confess a served one: {configured}"
        );
    }

    /// The no-anchor path is a REFUSAL, never a softened verdict.
    #[test]
    fn the_no_anchor_path_reports_no_verdict() {
        let text = no_anchor_text(&"ab".repeat(32), "the anchor does not verify: …");
        assert!(text.contains("**No verdict.**"), "{text}");
        assert!(!text.contains("LIMITED CHECK PASSED"), "{text}");
        assert!(text.contains("/anchor"), "{text}");
    }

    /// The offline incantation names BOTH routes + the real verifier entry points, and warns off
    /// the one substitution that would refuse every honest proof.
    #[test]
    fn the_offline_recheck_names_both_routes_and_the_verifiers() {
        let text = offline_recheck_text("http://node:8080/", &"ab".repeat(32));
        assert!(text.contains("/api/turn/"), "{text}");
        assert!(text.contains("/anchor"), "{text}");
        assert!(text.contains("verify_full_turn"), "{text}");
        assert!(text.contains("TurnAnchorV1"), "{text}");
        assert!(text.contains("refuses every honest proof"), "{text}");
        // …and it must name the route that supplies the two commit arguments, plus the refusal
        // when it is absent — an incantation that omits them reproduces the reflexive check.
        assert!(text.contains("proof_state_commits"), "{text}");
        assert!(text.contains("commit8_from_hex"), "{text}");
        assert!(
            text.contains("REFUSE, do not read the pair out of"),
            "{text}"
        );
        assert!(!text.contains("8080//"), "trailing slash trimmed: {text}");
    }
}
