//! THE LIVE FACE of the remote mirror — following a remote dregg image's DYNAMICS
//! stream across distance, gated by the mirror-cap's reflective depth.
//!
//! [`remote_mirror`](crate::remote_mirror) gives the mirror its STATIC read face:
//! [`RemoteMirror::reflect`](crate::remote_mirror::RemoteMirror::reflect) resolves
//! a one-shot snapshot of a remote cell at the cap's depth. But the `Live` depth
//! promises more than a snapshot — it promises to *follow the live dynamics stream
//! as the remote image evolves* ([`MirrorDepth::reveals_dynamics`]). That promise
//! is what this module makes concrete: a [`LiveMirror`] welds the existing live
//! dynamics organ ([`ReceiptFeed`] — the SSE receipt stream the local inspector
//! already consumes) to a [`MirrorCap`], surfacing the remote cell's evolution as
//! it commits — and ONLY when the cap's depth is `Live`.
//!
//! ## The depth axis, made concrete on the live stream (the second polarity)
//!
//! A mirror's reflective depth is a real attenuation coordinate
//! (`Structure ⊑ ReadState ⊑ Live`). The static face already enforces it (a
//! `Structure` mirror redacts state). The live face enforces the TOP of the
//! lattice: only a `Live`-depth mirror may *follow the dynamics tail*. A
//! `ReadState` mirror reads the remote cell's current state but is REFUSED the
//! live stream ([`LiveRefusal::DepthTooShallow`]) — the `widens_to` tooth on the
//! reflection axis, now biting on the evolution face, not just the snapshot. This
//! is the mirror's no-amplification rule reaching the most-trusted depth: *seeing
//! the remote's state confers no edge to watch it change.*
//!
//! ## It REUSES the dynamics organ — no parallel stream
//!
//! The live tail is the genuine [`ReceiptFeed`] the local inspector's receipt
//! pane already drives off `GET /api/events/stream`. The mirror does not invent a
//! second stream model: it holds a `&ReceiptFeed` fed by the SAME transport that
//! backs [`RemoteImage`](crate::remote_mirror::RemoteImage), and PROJECTS the tail
//! down to exactly the receipts that NAME the mirror's cell (a remote turn that
//! never touched this cell is not this mirror's to see). The projection rides
//! [`ReceiptEvent::cells`] — the cells a committed turn named — so the live face is
//! the same per-cell delta the local `dynamics`/memo fold already keys on.
//!
//! ## Read-only by construction (no write edge from the live face)
//!
//! A `LiveMirror` exposes ONLY observation — the evolving tail. It carries no
//! edit verb; the write face stays the static mirror's gated
//! [`RemoteMirror::propose_edit`](crate::remote_mirror::RemoteMirror::propose_edit),
//! which a read-only cap refuses (`viewSurface_confers_no_edge`). Watching a remote
//! image evolve confers no edge to drive its evolution. This is the firmament
//! property [`viewSurface_confers_no_edge`] taken to the live axis: a mirror that
//! *watches* still cannot *write*.
//!
//! ## Distance is honest here too
//!
//! Every live reflection carries the firmament [`Bounds`] for the transport's
//! distance. At `n = 1` the stream is strong-local (immediate); at `n > 1` it is
//! the eventual netlayer tail (at-least-once across reconnects, the `ReceiptFeed`'s
//! own dedup-by-`chain_index` discipline). The verbs are unchanged across `n`;
//! only the bounds relax — the firmament's `n`-collapse, on the live face.
//!
//! gpui-free; `cargo test`-able under `embedded-executor` (reuses `live_node`'s
//! `ReceiptFeed` + `remote_mirror`'s `MirrorCap`/`Bounds`, no network).

use dregg_firmament::Bounds;
#[cfg(test)]
use dregg_types::CellId;

use crate::live_node::ReceiptFeed;
use crate::model::ReceiptEvent;
use crate::remote_mirror::{MirrorCap, MirrorDepth, RemoteImage};

// ===========================================================================
// THE LIVE TAIL — the remote cell's evolution, projected to this mirror's cell
// ===========================================================================

/// One step in a remote cell's live evolution: a committed turn that NAMED the
/// mirror's cell, projected down from a streamed [`ReceiptEvent`]. Pure data; the
/// thin gpui layer renders it as a row in the live dynamics tail (the same shape
/// the local receipt pane draws).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LiveStep {
    /// The chain index of the committing turn (monotone; the dedup/resume key).
    pub chain_index: u64,
    /// The block height the turn committed at (the freshness anchor).
    pub height: u64,
    /// The committed receipt's hash (hex) — the navigable receipt this step IS.
    pub receipt_hash: String,
    /// The turn's hash (hex).
    pub turn_hash: String,
    /// The effect kinds this turn carried (the turn's verb vocabulary).
    pub kinds: Vec<String>,
    /// Whether the turn carried a proof (the light-client face of this step).
    pub has_proof: bool,
    pub proof_status: Option<String>,
}

impl LiveStep {
    /// Project a streamed [`ReceiptEvent`] into a live step. The full event names
    /// possibly-many cells; this carries only the turn-level summary — the
    /// per-cell filtering happens at the [`LiveMirror`] boundary.
    fn from_event(ev: &ReceiptEvent) -> Self {
        LiveStep {
            chain_index: ev.chain_index,
            height: ev.height,
            receipt_hash: ev.receipt_hash.clone(),
            turn_hash: ev.turn_hash.clone(),
            kinds: ev.kinds.clone(),
            has_proof: ev.has_proof,
            proof_status: ev.proof_status.clone(),
        }
    }
}

/// The result of following a remote cell's live evolution through a `Live` mirror:
/// the steps that named the cell, the depth it was followed at (always `Live`),
/// and the honest [`Bounds`] for the distance.
#[derive(Clone, Debug)]
pub struct LiveTail {
    /// The depth this tail was followed at — always [`MirrorDepth::Live`] (the
    /// only depth that authorizes the dynamics stream).
    pub depth: MirrorDepth,
    /// The firmament bounds that held — relaxed honestly with distance.
    pub bounds: Bounds,
    /// The evolution steps that NAMED the mirror's cell, oldest first (the
    /// `ReceiptFeed`'s retention order).
    pub steps: Vec<LiveStep>,
}

impl LiveTail {
    /// The most recent step (the live head the dynamics pane scrolls to), if any.
    pub fn latest(&self) -> Option<&LiveStep> {
        self.steps.last()
    }

    /// How many evolution steps named the cell in the followed tail.
    pub fn len(&self) -> usize {
        self.steps.len()
    }

    /// Whether the cell has evolved at all in the followed tail.
    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }
}

/// Why following a remote cell's live evolution was REFUSED — surfaced honestly,
/// never faked into an empty-but-successful tail.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LiveRefusal {
    /// The mirror-cap does not authorize reflection at all (`Impossible` rights) —
    /// the same floor the static face refuses on.
    NoReflectAuthority,
    /// The mirror's depth is too shallow to follow the live stream: only a `Live`
    /// mirror may. Carries the depth the mirror DID hold, for the honest log — the
    /// `widens_to` tooth on the live axis (`viewState_confers_no_dynamics`).
    DepthTooShallow { held: MirrorDepth },
    /// The mirror is not over a remote (distributed) cell — not a mirror.
    NotARemoteCell,
}

// ===========================================================================
// THE LIVE MIRROR — a Live-depth mirror-cap aimed at a live dynamics feed
// ===========================================================================

/// A **live mirror**: a mirror-cap pointed at a live dynamics [`ReceiptFeed`], so
/// the reflexive image FOLLOWS a remote cell's evolution across distance — read
/// only, and only at the `Live` depth.
///
/// It holds the same [`MirrorCap`] the static [`RemoteMirror`](crate::remote_mirror::RemoteMirror)
/// holds (over a remote cell, at a reflective depth) plus a `&ReceiptFeed` — the
/// live dynamics organ — and the transport (for the honest distance/[`Bounds`]).
/// [`LiveMirror::follow`] yields the cell's evolution tail, refusing every mirror
/// whose depth is below `Live`.
pub struct LiveMirror<'a, T: RemoteImage> {
    cap: MirrorCap,
    feed: &'a ReceiptFeed,
    transport: &'a T,
}

impl<'a, T: RemoteImage> LiveMirror<'a, T> {
    /// Aim a mirror-cap at a live dynamics feed + its transport. The feed is the
    /// genuine [`ReceiptFeed`] fed off the remote node's SSE stream; the transport
    /// supplies the honest distance.
    pub fn new(cap: MirrorCap, feed: &'a ReceiptFeed, transport: &'a T) -> Self {
        LiveMirror {
            cap,
            feed,
            transport,
        }
    }

    /// The mirror-cap this live mirror holds.
    pub fn cap(&self) -> &MirrorCap {
        &self.cap
    }

    /// The firmament bounds for a resolution at this transport's distance — the
    /// honest `n`-relaxation (identical to the static mirror's `bounds()`).
    pub fn bounds(&self) -> Bounds {
        Bounds::distributed(self.transport.distance())
    }

    /// **FOLLOW** the remote cell's live evolution — the live read face.
    ///
    /// Projects the live dynamics [`ReceiptFeed`] down to exactly the steps that
    /// NAMED the mirror's cell, and carries the honest [`Bounds`]. Refuses
    /// (returns `Err`) if the mirror has no reflect authority, is not over a remote
    /// cell, or — the keystone of this module — its depth is below `Live`: a
    /// `ReadState`/`Structure` mirror reads state but may NOT follow the dynamics
    /// tail (the depth-axis attenuation on the live face). Never a faked tail.
    pub fn follow(&self) -> Result<LiveTail, LiveRefusal> {
        // Floor: the cap must authorize reflection at all (shared with the static
        // face — `Impossible` rights authorize nothing).
        if !self.cap.can_reflect() {
            return Err(LiveRefusal::NoReflectAuthority);
        }
        // Depth gate: ONLY a `Live` mirror may follow the dynamics stream. This is
        // the no-amplification tooth on the live axis — a `ReadState` mirror that
        // tried to follow is asking to widen ReadState -> Live, refused exactly as
        // `MirrorDepth::widens_to(Live)` is `true`.
        if !self.cap.depth().reveals_dynamics() {
            return Err(LiveRefusal::DepthTooShallow {
                held: self.cap.depth(),
            });
        }
        let cell = self.cap.cell().ok_or(LiveRefusal::NotARemoteCell)?;

        // Project the live tail down to the steps that NAMED this cell. The
        // `ReceiptFeed` is the genuine dynamics organ; we filter on
        // `ReceiptEvent::cells` — the same per-cell delta the local memo fold keys
        // on — so a remote turn that never touched this cell is not surfaced.
        let cell_hex = dregg_types::hex_encode(cell.as_bytes());
        let steps: Vec<LiveStep> = self
            .feed
            .receipts()
            .iter()
            .filter(|ev| event_names_cell(ev, &cell_hex))
            .map(LiveStep::from_event)
            .collect();

        Ok(LiveTail {
            depth: MirrorDepth::Live,
            bounds: self.bounds(),
            steps,
        })
    }
}

/// Does a streamed [`ReceiptEvent`] NAME the given cell (hex)? The per-cell
/// projection key — a committed turn names every cell it touched in
/// [`ReceiptEvent::cells`]; a live mirror over `cell` sees a step iff the turn
/// named `cell`. Tolerant of case (the wire is lowercase hex).
fn event_names_cell(ev: &ReceiptEvent, cell_hex: &str) -> bool {
    ev.cells.iter().any(|c| c.eq_ignore_ascii_case(cell_hex))
}

// ===========================================================================
// TESTS — both polarities:
//   ✓ a Live mirror follows the remote cell's evolution (projected to the cell)
//   ✗ a ReadState mirror is REFUSED the dynamics tail (depth too shallow)
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::remote_mirror::FixtureImage;
    use dregg_firmament::AuthRequired;

    fn cid(b: u8) -> CellId {
        let mut k = [0u8; 32];
        k[0] = b;
        CellId::derive_raw(&k, &[0u8; 32])
    }

    /// A streamed receipt naming `cells`, at `chain_index`/`height`.
    fn ev(chain_index: u64, height: u64, cells: &[CellId], kinds: &[&str]) -> ReceiptEvent {
        ReceiptEvent {
            chain_index,
            receipt_hash: format!("{:064x}", chain_index),
            turn_hash: format!("{:064x}", 0xA0u64.wrapping_add(chain_index)),
            cells: cells
                .iter()
                .map(|c| dregg_types::hex_encode(c.as_bytes()))
                .collect(),
            kinds: kinds.iter().map(|s| s.to_string()).collect(),
            height,
            has_proof: true,
            proof_status: None,
            finality: "final".to_string(),
            timestamp: 0,
        }
    }

    #[test]
    fn coordination_policy_survives_live_step_projection() {
        let mut event = ev(0, 1, &[], &["emit_event"]);
        event.has_proof = false;
        event.proof_status = Some("not_required".into());
        let step = LiveStep::from_event(&event);
        assert_eq!(step.proof_status.as_deref(), Some("not_required"));
        assert!(!step.has_proof);
    }

    /// A feed pre-loaded with a sequence of streamed receipts (the live tail).
    fn feed_with(evs: Vec<ReceiptEvent>) -> ReceiptFeed {
        let mut f = ReceiptFeed::new(256);
        for e in evs {
            f.ingest(e);
        }
        f
    }

    // ---- POLARITY ✓ : a Live mirror follows the cell's evolution -------------

    #[test]
    fn live_mirror_follows_remote_cell_evolution() {
        let watched = cid(7);
        let other = cid(8);
        // The remote stream: two turns touched `watched`, one touched only `other`.
        let feed = feed_with(vec![
            ev(1, 100, &[watched], &["Transfer"]),
            ev(2, 101, &[other], &["Seal"]),
            ev(3, 102, &[watched, other], &["Transfer"]),
        ]);
        let img = FixtureImage::new(4);
        let mirror = LiveMirror::new(
            MirrorCap::read_only(watched, MirrorDepth::Live),
            &feed,
            &img,
        );

        let tail = mirror
            .follow()
            .expect("a Live mirror follows the dynamics tail");
        assert_eq!(tail.depth, MirrorDepth::Live);
        // ONLY the two turns that NAMED `watched` are surfaced (the per-cell delta).
        assert_eq!(
            tail.len(),
            2,
            "the live tail is projected to the mirror's cell"
        );
        assert_eq!(tail.steps[0].chain_index, 1);
        assert_eq!(tail.steps[1].chain_index, 3);
        assert_eq!(tail.latest().unwrap().height, 102);
        // The honest distance bounds rode the reflection (n > 1 ⇒ eventual).
        assert_eq!(tail.bounds.n, 4);
        assert!(!tail.bounds.revocation_immediate);
    }

    #[test]
    fn n1_live_tail_is_strong_local() {
        let watched = cid(1);
        let feed = feed_with(vec![ev(1, 5, &[watched], &["Transfer"])]);
        // A "remote" image in fact on this box (n = 1).
        let img = FixtureImage::new(1);
        let mirror = LiveMirror::new(
            MirrorCap::read_only(watched, MirrorDepth::Live),
            &feed,
            &img,
        );
        let tail = mirror.follow().unwrap();
        assert_eq!(tail.bounds, Bounds::LOCAL);
        assert!(tail.bounds.revocation_immediate && tail.bounds.commit_synchronous);
    }

    // ---- POLARITY ✗ : a shallow mirror is REFUSED the dynamics tail ----------

    #[test]
    fn read_state_mirror_cannot_follow_dynamics() {
        let watched = cid(7);
        let feed = feed_with(vec![ev(1, 100, &[watched], &["Transfer"])]);
        let img = FixtureImage::new(4);
        // A ReadState mirror: it may read the remote STATE (the static face) but
        // NOT follow the live dynamics stream — the depth attenuation on the live
        // axis. viewState_confers_no_dynamics.
        let mirror = LiveMirror::new(
            MirrorCap::read_only(watched, MirrorDepth::ReadState),
            &feed,
            &img,
        );
        match mirror.follow() {
            Err(LiveRefusal::DepthTooShallow { held }) => {
                assert_eq!(held, MirrorDepth::ReadState);
            }
            other => panic!("a ReadState mirror must NOT follow the dynamics tail, got {other:?}"),
        }
    }

    #[test]
    fn structure_mirror_cannot_follow_dynamics() {
        let watched = cid(7);
        let feed = feed_with(vec![ev(1, 100, &[watched], &["Transfer"])]);
        let img = FixtureImage::new(4);
        // The least-trusted mirror is refused even harder.
        let mirror = LiveMirror::new(MirrorCap::structure_only(watched), &feed, &img);
        assert_eq!(
            mirror.follow().unwrap_err(),
            LiveRefusal::DepthTooShallow {
                held: MirrorDepth::Structure
            }
        );
    }

    #[test]
    fn impossible_mirror_cannot_follow() {
        let watched = cid(9);
        let feed = feed_with(vec![ev(1, 1, &[watched], &["Transfer"])]);
        let img = FixtureImage::new(1);
        // `Impossible` rights fail the reflect floor BEFORE the depth gate.
        let mirror = LiveMirror::new(
            MirrorCap::new(watched, AuthRequired::Impossible, MirrorDepth::Live),
            &feed,
            &img,
        );
        assert_eq!(
            mirror.follow().unwrap_err(),
            LiveRefusal::NoReflectAuthority
        );
    }

    // ---- the projection is honest: a cell that never evolved has an empty tail -

    #[test]
    fn unevolved_cell_has_empty_tail_not_a_fake() {
        let watched = cid(7);
        let other = cid(8);
        // The stream touched only `other`; `watched` never evolved.
        let feed = feed_with(vec![ev(1, 1, &[other], &["Transfer"])]);
        let img = FixtureImage::new(2);
        let mirror = LiveMirror::new(
            MirrorCap::read_only(watched, MirrorDepth::Live),
            &feed,
            &img,
        );
        let tail = mirror
            .follow()
            .expect("a Live mirror over an unevolved cell still succeeds");
        assert!(
            tail.is_empty(),
            "no turn named the cell ⇒ an honest empty tail"
        );
        assert!(tail.latest().is_none());
    }
}
