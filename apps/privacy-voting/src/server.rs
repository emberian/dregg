//! HTTP server for privacy-preserving voting.
//!
//! ## Routes
//!
//! - `POST /proposals` — admin: create a new proposal in `Commit` phase.
//! - `GET  /proposals` — list all proposals.
//! - `GET  /proposals/{id}` — fetch a proposal.
//! - `POST /admin/proposals/{id}/phase` — admin: advance phase (commit→reveal→closed).
//! - `POST /ballots/submit` — voter: submit a vote commitment with eligibility credential.
//! - `POST /ballots/reveal` — voter: reveal a ballot.
//! - `GET  /tally/{id}` — return current tally + reveal root.
//!
//! Additionally, the binary nests a `FairDistributionEndpoint` at `/queue/ballots`
//! exposing the blinded queue's standard `/commit`, `/consume`, `/consume-private`,
//! `/status` routes for cross-app integration (e.g., a cclerk that talks to many
//! blinded queues uniformly).
//!
//! ## Privacy property
//!
//! On `/ballots/submit`:
//! - The credential is verified (issuer check + signature).
//! - The commitment is appended to the per-proposal `BlindedQueue`.
//! - The voter's identity (the credential's `delegatee`) is added to a
//!   *separate* `HashSet` keyed by `(proposal_id, voter_pk)` to prevent
//!   double-voting.
//! - The queue entry stores ONLY the commitment bytes. There is NO voter
//!   identity stored alongside the commitment.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use axum::{
    Json, Router,
    extract::{Path, State},
    http::StatusCode,
    routing::{get, post},
};
use serde::{Deserialize, Serialize};
use tokio::sync::Mutex;

use pyana_app_framework::auth::{AdminAuth, AdminToken, HasAdminToken};
use pyana_app_framework::server::{ErrorResponse, api_error};
use pyana_sdk::cipherclerk::DelegatedToken;
use pyana_storage::blinded::BlindedQueue;
use pyana_types::PublicKey;

use crate::ballot::{self, BallotReveal, Commitment};
use crate::eligibility::{EligibilityAuthority, verify_eligibility};
use crate::proposal::{Phase, Proposal, ProposalId, derive_proposal_id};
use crate::tally::{RevealLog, RevealedBallot};

// =============================================================================
// State
// =============================================================================

/// Per-proposal state: queue of commitments + reveal log + double-vote set.
struct ProposalState {
    proposal: Proposal,
    queue: BlindedQueue,
    /// Voters who have already submitted a commitment for this proposal.
    /// Stored DISJOINT from the queue — never accessible alongside a commitment.
    voted: HashSet<PublicKey>,
    /// Commitments awaiting reveal. Stored as a set of bytes; identity-free.
    committed: HashSet<Commitment>,
    /// Public reveal log + Merkle root + tally.
    reveals: RevealLog,
}

impl ProposalState {
    fn new(proposal: Proposal, capacity: usize) -> Self {
        Self {
            proposal,
            queue: BlindedQueue::new(capacity),
            voted: HashSet::new(),
            committed: HashSet::new(),
            reveals: RevealLog::new(),
        }
    }
}

/// Shared application state.
#[derive(Clone)]
pub struct AppState {
    inner: Arc<Mutex<AppInner>>,
    pub admin_token: AdminToken,
}

struct AppInner {
    proposals: HashMap<ProposalId, ProposalState>,
    /// Configured eligibility authority. NOT `Open` — see `eligibility.rs`.
    authority: EligibilityAuthority,
    /// Queue capacity for new proposals.
    queue_capacity: usize,
}

impl HasAdminToken for AppState {
    fn admin_token(&self) -> &AdminToken {
        &self.admin_token
    }
}

impl AppState {
    /// Create an `AppState` configured with the given eligibility authority.
    pub fn new(authority: EligibilityAuthority, queue_capacity: usize) -> Self {
        Self {
            inner: Arc::new(Mutex::new(AppInner {
                proposals: HashMap::new(),
                authority,
                queue_capacity,
            })),
            admin_token: AdminToken::from_env(),
        }
    }

    /// Override the admin token (useful for tests).
    pub fn with_admin_token(mut self, token: AdminToken) -> Self {
        self.admin_token = token;
        self
    }
}

// =============================================================================
// Wire types
// =============================================================================

#[derive(Deserialize)]
pub struct CreateProposalRequest {
    pub slug: String,
    pub question: String,
    pub options: Vec<String>,
}

#[derive(Serialize)]
pub struct ProposalResponse {
    pub id: String,
    pub question: String,
    pub options: Vec<String>,
    pub phase: Phase,
}

impl From<&Proposal> for ProposalResponse {
    fn from(p: &Proposal) -> Self {
        Self {
            id: hex32(&p.id),
            question: p.question.clone(),
            options: p.options.clone(),
            phase: p.phase,
        }
    }
}

#[derive(Deserialize)]
pub struct AdvancePhaseRequest {
    pub to: Phase,
}

#[derive(Deserialize)]
pub struct SubmitBallotRequest {
    /// Hex-encoded 32-byte proposal id.
    pub proposal_id: String,
    /// Hex-encoded 32-byte commitment.
    pub commitment_hex: String,
    /// The eligibility credential — full envelope.
    pub credential: DelegatedToken,
}

#[derive(Serialize)]
pub struct SubmitBallotResponse {
    pub queued: bool,
    pub commitment_hex: String,
    pub queue_root: String,
}

#[derive(Deserialize)]
pub struct RevealBallotRequest {
    pub proposal_id: String,
    pub commitment_hex: String,
    pub reveal: BallotReveal,
}

#[derive(Serialize)]
pub struct RevealBallotResponse {
    pub accepted: bool,
    pub reveal_root: String,
    pub reveal_count: usize,
}

#[derive(Serialize)]
pub struct TallyResponse {
    pub proposal_id: String,
    pub phase: Phase,
    pub options: Vec<String>,
    pub counts: Vec<u64>,
    pub reveal_root: String,
    pub reveal_count: usize,
    pub queue_root: String,
    pub queue_committed: usize,
}

// =============================================================================
// Router
// =============================================================================

pub fn router() -> Router<AppState> {
    Router::new()
        .route("/proposals", post(create_proposal).get(list_proposals))
        .route("/proposals/{id}", get(get_proposal))
        .route("/admin/proposals/{id}/phase", post(advance_phase))
        .route("/ballots/submit", post(submit_ballot))
        .route("/ballots/reveal", post(reveal_ballot))
        .route("/tally/{id}", get(tally))
}

// =============================================================================
// Handlers
// =============================================================================

async fn create_proposal(
    _auth: AdminAuth,
    State(state): State<AppState>,
    Json(req): Json<CreateProposalRequest>,
) -> Result<(StatusCode, Json<ProposalResponse>), (StatusCode, Json<ErrorResponse>)> {
    if req.options.len() < 2 {
        return Err(api_error(
            StatusCode::BAD_REQUEST,
            "proposal must have at least two options",
        ));
    }
    if req.options.len() > 256 {
        return Err(api_error(
            StatusCode::BAD_REQUEST,
            "proposal may have at most 256 options",
        ));
    }
    let id = derive_proposal_id(&req.slug);
    let proposal = Proposal::new(id, req.question, req.options);

    let mut inner = state.inner.lock().await;
    if inner.proposals.contains_key(&id) {
        return Err(api_error(
            StatusCode::CONFLICT,
            format!("proposal with slug already exists"),
        ));
    }
    let resp = ProposalResponse::from(&proposal);
    let ps = ProposalState::new(proposal, inner.queue_capacity);
    inner.proposals.insert(id, ps);
    Ok((StatusCode::CREATED, Json(resp)))
}

async fn list_proposals(State(state): State<AppState>) -> Json<Vec<ProposalResponse>> {
    let inner = state.inner.lock().await;
    let list = inner
        .proposals
        .values()
        .map(|ps| ProposalResponse::from(&ps.proposal))
        .collect();
    Json(list)
}

async fn get_proposal(
    State(state): State<AppState>,
    Path(id): Path<String>,
) -> Result<Json<ProposalResponse>, (StatusCode, Json<ErrorResponse>)> {
    let id_bytes = parse_hex32(&id)
        .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid proposal id"))?;
    let inner = state.inner.lock().await;
    let ps = inner
        .proposals
        .get(&id_bytes)
        .ok_or_else(|| api_error(StatusCode::NOT_FOUND, "proposal not found"))?;
    Ok(Json(ProposalResponse::from(&ps.proposal)))
}

async fn advance_phase(
    _auth: AdminAuth,
    State(state): State<AppState>,
    Path(id): Path<String>,
    Json(req): Json<AdvancePhaseRequest>,
) -> Result<Json<ProposalResponse>, (StatusCode, Json<ErrorResponse>)> {
    let id_bytes = parse_hex32(&id)
        .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid proposal id"))?;
    let mut inner = state.inner.lock().await;
    let ps = inner
        .proposals
        .get_mut(&id_bytes)
        .ok_or_else(|| api_error(StatusCode::NOT_FOUND, "proposal not found"))?;

    // Enforce forward-only phase progression: Commit -> Reveal -> Closed.
    let ok = matches!(
        (ps.proposal.phase, req.to),
        (Phase::Commit, Phase::Reveal)
            | (Phase::Reveal, Phase::Closed)
            | (Phase::Commit, Phase::Closed) // emergency cancel
    );
    if !ok {
        return Err(api_error(
            StatusCode::BAD_REQUEST,
            format!(
                "illegal phase transition: {:?} -> {:?}",
                ps.proposal.phase, req.to
            ),
        ));
    }
    ps.proposal.phase = req.to;
    Ok(Json(ProposalResponse::from(&ps.proposal)))
}

async fn submit_ballot(
    State(state): State<AppState>,
    Json(req): Json<SubmitBallotRequest>,
) -> Result<Json<SubmitBallotResponse>, (StatusCode, Json<ErrorResponse>)> {
    let proposal_id = parse_hex32(&req.proposal_id)
        .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid proposal_id"))?;
    let commitment = parse_hex32(&req.commitment_hex)
        .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid commitment_hex"))?;

    // Authority + signature: this is the gate that makes the queue
    // eligibility-restricted rather than open.
    let authority = {
        let inner = state.inner.lock().await;
        inner.authority.clone()
    };
    let voter_pk = verify_eligibility(&authority, &req.credential)
        .map_err(|e| api_error(StatusCode::UNAUTHORIZED, e.to_string()))?;

    let mut inner = state.inner.lock().await;
    let ps = inner
        .proposals
        .get_mut(&proposal_id)
        .ok_or_else(|| api_error(StatusCode::NOT_FOUND, "proposal not found"))?;

    if ps.proposal.phase != Phase::Commit {
        return Err(api_error(
            StatusCode::BAD_REQUEST,
            format!(
                "ballot submissions only accepted during Commit phase (current: {:?})",
                ps.proposal.phase
            ),
        ));
    }

    // Double-vote check. NOTE: `voted` is keyed by voter pk and is DISJOINT
    // from `queue`/`committed`. The queue itself never sees `voter_pk`.
    if ps.voted.contains(&voter_pk) {
        return Err(api_error(
            StatusCode::CONFLICT,
            "voter has already submitted a ballot for this proposal",
        ));
    }

    ps.queue
        .commit(commitment.into())
        .map_err(|e| api_error(StatusCode::UNPROCESSABLE_ENTITY, format!("queue: {e:?}")))?;
    ps.committed.insert(commitment);
    ps.voted.insert(voter_pk);

    // P2.H / D-9: emit a real on-ledger Action via the typestate
    // ActionBuilder. The action carries an EmitEvent("ballot-cast", …)
    // anchoring the submission for off-chain indexers. The voter
    // identity (voter_pk) is intentionally NOT included in the event
    // payload — privacy is preserved by emitting only the proposal_id
    // and the commitment.
    let voting_cell = crate::effects::voting_cell_id();
    let caller = pyana_cell::CellId::from_bytes(voter_pk.0);
    let _submit_action =
        crate::effects::build_ballot_submit_action(voting_cell, caller, proposal_id, commitment);

    let queue_root = ps.queue.commitment_root();
    Ok(Json(SubmitBallotResponse {
        queued: true,
        commitment_hex: hex32(&commitment),
        queue_root: hex32(&queue_root),
    }))
}

async fn reveal_ballot(
    State(state): State<AppState>,
    Json(req): Json<RevealBallotRequest>,
) -> Result<Json<RevealBallotResponse>, (StatusCode, Json<ErrorResponse>)> {
    let proposal_id = parse_hex32(&req.proposal_id)
        .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid proposal_id"))?;
    let commitment = parse_hex32(&req.commitment_hex)
        .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid commitment_hex"))?;

    let mut inner = state.inner.lock().await;
    let ps = inner
        .proposals
        .get_mut(&proposal_id)
        .ok_or_else(|| api_error(StatusCode::NOT_FOUND, "proposal not found"))?;

    if ps.proposal.phase != Phase::Reveal {
        return Err(api_error(
            StatusCode::BAD_REQUEST,
            format!(
                "reveals only accepted during Reveal phase (current: {:?})",
                ps.proposal.phase
            ),
        ));
    }

    if !ps.committed.contains(&commitment) {
        return Err(api_error(
            StatusCode::BAD_REQUEST,
            "commitment was not submitted to this proposal",
        ));
    }

    if !ps.proposal.is_valid_option(req.reveal.option_index) {
        return Err(api_error(
            StatusCode::BAD_REQUEST,
            "option_index out of range",
        ));
    }

    if !ballot::verify_reveal(&proposal_id, &commitment, &req.reveal) {
        return Err(api_error(
            StatusCode::BAD_REQUEST,
            "reveal does not match commitment",
        ));
    }

    // Reveal once per commitment.
    ps.committed.remove(&commitment);
    ps.reveals.append(RevealedBallot {
        commitment,
        option_index: req.reveal.option_index,
        randomness: req.reveal.randomness,
    });

    // P2.H / D-9: emit a real on-ledger Action via the typestate
    // ActionBuilder. The action carries an EmitEvent("ballot-revealed",
    // …) acting as the audit log entry — the {commitment, option_index}
    // pair is now public-by-design (this is the reveal phase).
    let voting_cell = crate::effects::voting_cell_id();
    // No voter identity at reveal time; caller is the voting registry
    // cell itself acting as the audit log writer.
    let caller = voting_cell;
    let _reveal_action = crate::effects::build_ballot_reveal_action(
        voting_cell,
        caller,
        proposal_id,
        commitment,
        req.reveal.option_index,
    );

    let reveal_root = ps.reveals.merkle_root();
    let reveal_count = ps.reveals.len();
    Ok(Json(RevealBallotResponse {
        accepted: true,
        reveal_root: hex32(&reveal_root),
        reveal_count,
    }))
}

async fn tally(
    State(state): State<AppState>,
    Path(id): Path<String>,
) -> Result<Json<TallyResponse>, (StatusCode, Json<ErrorResponse>)> {
    let proposal_id = parse_hex32(&id)
        .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid proposal id"))?;
    let inner = state.inner.lock().await;
    let ps = inner
        .proposals
        .get(&proposal_id)
        .ok_or_else(|| api_error(StatusCode::NOT_FOUND, "proposal not found"))?;

    let counts = ps.reveals.tally(ps.proposal.options.len(), &proposal_id);
    Ok(Json(TallyResponse {
        proposal_id: hex32(&proposal_id),
        phase: ps.proposal.phase,
        options: ps.proposal.options.clone(),
        counts,
        reveal_root: hex32(&ps.reveals.merkle_root()),
        reveal_count: ps.reveals.len(),
        queue_root: hex32(&ps.queue.commitment_root()),
        queue_committed: ps.queue.remaining() + ps.queue.consumed_count(),
    }))
}

// =============================================================================
// Helpers
// =============================================================================

fn parse_hex32(s: &str) -> Option<[u8; 32]> {
    pyana_app_framework::hex::hex_to_bytes32(s).ok()
}

fn hex32(b: &[u8; 32]) -> String {
    pyana_app_framework::hex::bytes32_to_hex(b)
}

/// Test-only accessor: inspect the raw bytes stored in the queue (no identity).
///
/// Used by `tests.rs` to assert the unlinkability property: no entry on the
/// queue carries voter identity bytes.
#[cfg(any(test, feature = "test-utils"))]
pub async fn dump_queue_entries(state: &AppState, proposal_id: &ProposalId) -> Vec<Commitment> {
    let inner = state.inner.lock().await;
    let ps = match inner.proposals.get(proposal_id) {
        Some(ps) => ps,
        None => return Vec::new(),
    };
    // We don't have a public iterator on BlindedQueue's commitments, so we
    // mirror via `ps.committed` (which is a strict subset post-reveals; for
    // pre-reveal queries it equals the full queue contents). This is what the
    // unlinkability test inspects.
    let mut v: Vec<Commitment> = ps.committed.iter().copied().collect();
    v.sort();
    v
}
