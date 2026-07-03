//! `#[wasm_bindgen]` entry points for TRANSCLUSION — Xanadu made honest, carried
//! to the browser (the minimal resolve/render path of
//! [`starbridge_web_surface::transclusion`]).
//!
//! This is the smallest wasm entry that lets a site visitor TOUCH a live
//! honest-quote: a browser drives the REAL `dregg://` finalized read NAMED as Ted
//! Nelson's transcluded quote
//! ([`starbridge_web_surface::transclusion::TranscludedField::include`]) over a
//! real [`starbridge_web_surface::web_of_cells::WebOfCells`] (a genuine
//! [`dregg_cell::Ledger`] + the genuine [`dregg_types::AttestedRoot`] receipt-stream
//! verifier). The demo `transclusion.js` drives:
//!
//!   1. **transclude** a source span → [`transclusion_include`] performs the verified
//!      finalized read; the displayed bytes ARE the source's committed bytes;
//!   2. **amend** the source → [`transclusion_amend`] advances the SAME `dregg://` ref
//!      to a new finalized value, and a LIVE re-read ([`transclusion_read_live`])
//!      follows it (the unbreakable link), while a SNAPSHOT
//!      ([`transclusion_read_snapshot`]) stays pinned (I-confluence);
//!   3. **forge** → [`transclusion_forge_attempt`] tampers the served bytes and runs
//!      the genuine client verify; it REFUSES with `ContentHashMismatch` — a forged
//!      quote cannot be opened;
//!   4. **no-amplification** → [`transclusion_project_for`] projects the quote
//!      per-viewer through the REAL [`starbridge_web_surface::rehydrate::Membrane`]; a
//!      weaker viewer's projection cannot amplify (`granted ⊆ held`);
//!   5. **the two-way link** → [`transclusion_include_into`] records each quote in the
//!      real [`starbridge_web_surface::transclusion::Backlinks`] reverse index, and
//!      [`transclusion_backlinks`] enumerates "who quotes this cell" — each entry
//!      pinned to the cited receipt + content commitment (a verifiable fact, never
//!      Xanadu's hand-maintained pointer).
//!
//! It does NOT touch the circuit prover or the recursion path — only the
//! resolve/render path reaches the browser. Same `handle: usize` +
//! `with_*`-closure shape as `bindings_surface.rs`, but over a SEPARATE
//! [`TransclusionDemo`] store (its own ledger + the named-doc registry the demo
//! needs), so it is disjoint from the `DreggRuntime` surface store.

use std::cell::RefCell;

use serde::Serialize;
use wasm_bindgen::prelude::*;

use dregg_cell::{AuthRequired, CellId};
use starbridge_web_surface::SurfaceCapability;
use starbridge_web_surface::rehydrate::Membrane;
use starbridge_web_surface::transclusion::{Backlinks, TranscludedField, TransclusionError};
use starbridge_web_surface::web_of_cells::{DreggUri, FetchError, WebOfCells};

// ============================================================================
// The transclusion demo store (WASM is single-threaded, so this is safe).
// A handle owns a real WebOfCells + a tiny registry mapping the demo's named
// documents to their `dregg://` cell ids, so JS can publish/amend/include by a
// stable string name instead of round-tripping the 64-hex cell id every call.
// ============================================================================

/// A single demo world: a real [`WebOfCells`] (a genuine ledger + attestation)
/// plus a name→`dregg://`-ref registry for the documents the demo publishes.
struct TransclusionDemo {
    web: WebOfCells,
    /// Demo document name → its published `dregg://` ref (the origin cell). The
    /// names are the demo's UX handles ("constitution", "my-essay"); the ref is the
    /// REAL content-addressed cell the finalized read resolves.
    docs: Vec<(String, DreggUri)>,
    /// A monotone seed so each `publish` seeds a DISTINCT origin cell (the
    /// `WebOfCells::seed_origin` key derivation is seed-addressed).
    next_seed: u8,
    /// The REAL reverse index of Nelson's two-way link: source cell → the observer
    /// documents that transclude it, each record pinned to the cited receipt +
    /// content commitment. Populated by [`transclusion_include_into`], read by
    /// [`transclusion_backlinks`].
    backlinks: Backlinks,
}

impl TransclusionDemo {
    fn new() -> Self {
        TransclusionDemo {
            // A 3-of-3 federation quorum — the published source is genuinely
            // finalized (quorum-attested), so `include`'s finalized gate passes.
            web: WebOfCells::new(3),
            docs: Vec::new(),
            next_seed: 1,
            backlinks: Backlinks::new(),
        }
    }

    fn uri_of(&self, name: &str) -> Result<DreggUri, String> {
        self.docs
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, u)| u.clone())
            .ok_or_else(|| format!("no published document named {name:?}"))
    }
}

thread_local! {
    static DEMOS: RefCell<Vec<Option<TransclusionDemo>>> = const { RefCell::new(Vec::new()) };
}

fn with_demo<F, R>(handle: usize, f: F) -> Result<R, JsError>
where
    F: FnOnce(&mut TransclusionDemo) -> Result<R, String>,
{
    DEMOS.with(|demos| {
        let mut demos = demos.borrow_mut();
        let demo = demos
            .get_mut(handle)
            .and_then(|slot| slot.as_mut())
            .ok_or_else(|| JsError::new("invalid transclusion-demo handle"))?;
        f(demo).map_err(|e| JsError::new(&e))
    })
}

fn with_demo_ref<F, R>(handle: usize, f: F) -> Result<R, JsError>
where
    F: FnOnce(&TransclusionDemo) -> Result<R, String>,
{
    DEMOS.with(|demos| {
        let demos = demos.borrow();
        let demo = demos
            .get(handle)
            .and_then(|slot| slot.as_ref())
            .ok_or_else(|| JsError::new("invalid transclusion-demo handle"))?;
        f(demo).map_err(|e| JsError::new(&e))
    })
}

// ============================================================================
// Serde return shapes (the demo reads these in transclusion.js).
// ============================================================================

/// What [`transclusion_include`] / the live/snapshot reads return — a verified
/// quote: the displayed bytes (the source's committed value) + its honest,
/// dated provenance citation, all drawn from the verified finalized read.
#[derive(Serialize)]
struct QuoteView {
    /// The quoted bytes as UTF-8 text (the demo's source docs are HTML/text). These
    /// ARE the source's committed bytes — content-addressed, not a copy.
    text: String,
    /// `blake3(text)` as hex — the content address the citation pins.
    content_hash: String,
    /// The cited serve-receipt hash as hex — the immutable past the quote pins
    /// (the Lean `Import.provenance`). Advances when the source is amended.
    receipt_hash: String,
    /// The source `dregg://<cell>` ref string the value was quoted FROM.
    source_uri: String,
    /// Whether the cited read carried quorum (the "finalized" flag).
    finalized: bool,
    /// The federation height the source was at when this read resolved (the
    /// monotone freshness field; advances on every amend).
    at_height: u64,
    /// The trusted-path origin badge, drawn from the LEDGER (cell id + committed
    /// url + rights + finality) — never the page's own claim.
    chrome_badge: String,
    /// Whether this read re-verifies RIGHT NOW (the content→commitment→receipt→
    /// root→quorum chain). Always `true` for a faithful read; the demo asserts it.
    verifies: bool,
}

/// What [`transclusion_forge_attempt`] returns — the refusal is the headline.
#[derive(Serialize)]
struct ForgeView {
    /// `true` iff the forged quote was REFUSED (the demo's tooth: it must be).
    refused: bool,
    /// The named refusal reason (`ContentHashMismatch` for the byte-tamper forge) —
    /// the genuine `FetchError` variant, rendered as the teaching string.
    reason: String,
    /// The bytes the forger TRIED to substitute (what a lying node would serve).
    forged_text: String,
    /// The content address the citation still pins (the committed hash the forge
    /// fails to match) — proof the quote is bound to the source's value, not the
    /// forger's bytes.
    committed_content_hash: String,
}

/// What [`transclusion_project_for`] returns — the per-viewer no-amplification
/// readout (a quote is a READ, projected through the real membrane).
#[derive(Serialize)]
struct ProjectionView {
    /// `true` iff the projection succeeded (a weaker-or-equal viewer can observe).
    projected: bool,
    /// The viewer's rights string after projection (e.g. `"Signature"`, `"Either"`)
    /// — the ATTENUATED ceiling, never wider than the viewer held.
    viewer_rights: String,
    /// The source lineage's rights string (what the quote is served under).
    lineage_rights: String,
    /// `true` iff the projection is a strict attenuation of the lineage (the
    /// no-amplification property: the projected rights ⊆ the lineage rights).
    no_amplify: bool,
    /// On refusal, the reason (an over-broad / incomparable viewer cannot project).
    reason: String,
}

/// One backlink row of [`transclusion_backlinks`] — the verifiable claim "observer
/// O quoted source S's value V at receipt R", every field drawn from the recorded
/// observation, never from the page's own say-so.
#[derive(Serialize)]
struct BacklinkView {
    /// The observing document's `dregg://<cell>` ref (the document that quotes).
    observer_uri: String,
    /// The demo name the observer was registered under (`""` when the observing
    /// cell is not one of the demo's named documents).
    observer_name: String,
    /// The receipt the observation was pinned to, as hex — the cited immutable
    /// past. A later amend of the source does NOT rewrite this recorded fact.
    receipt_hash: String,
    /// The source content commitment that was observed, as hex — WHAT value the
    /// observer quoted (dateable: an old quote visibly cites an old value).
    content_hash: String,
}

/// What [`transclusion_backlinks`] returns — the reverse half of Nelson's two-way
/// link: WHO transcludes the source, each entry receipt-pinned.
#[derive(Serialize)]
struct BacklinksReadout {
    /// The source `dregg://<cell>` ref the observers quote FROM.
    source_uri: String,
    /// The in-degree: how many distinct observers transclude the source.
    count: usize,
    /// The observers, insertion-ordered — each a verifiable claim, not a pointer.
    observers: Vec<BacklinkView>,
}

/// A handle to a fresh `dregg://` document the demo published (so JS can refer to
/// it + render its `dregg://<cell>` link).
#[derive(Serialize)]
struct PublishView {
    /// The demo name the document was registered under.
    name: String,
    /// The `dregg://<cell>` ref string (the content-addressed cell — the address IS
    /// the access grant).
    source_uri: String,
    /// The federation height after publishing (advances each publish/amend).
    at_height: u64,
}

// ============================================================================
// Bindings.
// ============================================================================

/// **CREATE** a fresh transclusion demo world (a real [`WebOfCells`] with a 3-of-3
/// quorum) and return its handle. Mirrors `create_runtime`.
#[wasm_bindgen]
pub fn transclusion_create() -> usize {
    DEMOS.with(|demos| {
        let mut demos = demos.borrow_mut();
        for (i, slot) in demos.iter_mut().enumerate() {
            if slot.is_none() {
                *slot = Some(TransclusionDemo::new());
                return i;
            }
        }
        let handle = demos.len();
        demos.push(Some(TransclusionDemo::new()));
        handle
    })
}

/// **DESTROY** a demo world, freeing it. Returns true iff the handle was live.
#[wasm_bindgen]
pub fn transclusion_destroy(handle: usize) -> bool {
    DEMOS.with(|demos| {
        let mut demos = demos.borrow_mut();
        match demos.get_mut(handle) {
            Some(slot @ Some(_)) => {
                *slot = None;
                true
            }
            _ => false,
        }
    })
}

/// **PUBLISH** a `dregg://` source document: commit `content`'s hash into a fresh
/// origin cell's real state + bind a `committed_url`, registering it under `name`.
///
/// The REAL [`WebOfCells::publish`] — a genuine cell-state write of the content
/// commitment + a 3-of-3 quorum attestation, so the published source is a faithful
/// finalized read source (a transclusion of it will resolve + verify). Returns a
/// [`PublishView`] with the `dregg://<cell>` ref the demo renders as the link.
#[wasm_bindgen]
pub fn transclusion_publish(
    handle: usize,
    name: &str,
    content: &str,
    committed_url: &str,
) -> Result<JsValue, JsError> {
    with_demo(handle, |demo| {
        let seed = demo.next_seed;
        demo.next_seed = demo.next_seed.wrapping_add(1).max(1);
        let uri = demo.web.publish(seed, content.as_bytes(), committed_url);
        // Register (or re-register) the name → ref. A re-publish under an existing
        // name points it at the NEW origin cell.
        if let Some(entry) = demo.docs.iter_mut().find(|(n, _)| n == name) {
            entry.1 = uri.clone();
        } else {
            demo.docs.push((name.to_string(), uri.clone()));
        }
        let view = PublishView {
            name: name.to_string(),
            source_uri: uri.to_uri_string(),
            at_height: demo.web.height(),
        };
        serde_wasm_bindgen::to_value(&view).map_err(|e| e.to_string())
    })
}

/// **INCLUDE** (the definitional bridge `transclusion_is_observed_finalized_read`):
/// transclude the source named `name` — perform the REAL `dregg://` finalized read,
/// VERIFY its provenance, and return the verified quote.
///
/// This is [`TranscludedField::include`]: the displayed bytes ARE the source's
/// committed bytes; the citation dates them. A forged/absent/unfinalized source
/// REFUSES here (the genuine gate). Returns a [`QuoteView`].
#[wasm_bindgen]
pub fn transclusion_include(handle: usize, name: &str) -> Result<JsValue, JsError> {
    with_demo_ref(handle, |demo| {
        let uri = demo.uri_of(name)?;
        let field =
            TranscludedField::include(&demo.web, &uri).map_err(describe_transclusion_err)?;
        let view = quote_view(&field, demo.web.height())?;
        serde_wasm_bindgen::to_value(&view).map_err(|e| e.to_string())
    })
}

/// **INCLUDE INTO** an observing document (the two-way-link write): transclude the
/// source named `source_name` INTO the published document named `observer_name` —
/// the same verified finalized read as [`transclusion_include`], PLUS recording the
/// observation in the demo's [`Backlinks`] reverse index (the real
/// [`Backlinks::observe`]). The backlink carries the cited receipt + content
/// commitment from the quote's provenance, so "who quotes this cell" becomes a
/// verifiable fact, not Xanadu's hand-maintained pointer. Returns a [`QuoteView`].
///
/// The observer must itself be a PUBLISHED document (it observes from its own
/// `dregg://` cell) — an unpublished observer name is a clear error, never a
/// silent default.
#[wasm_bindgen]
pub fn transclusion_include_into(
    handle: usize,
    observer_name: &str,
    source_name: &str,
) -> Result<JsValue, JsError> {
    with_demo(handle, |demo| {
        let observer_uri = demo.uri_of(observer_name)?;
        let source_uri = demo.uri_of(source_name)?;
        let field =
            TranscludedField::include(&demo.web, &source_uri).map_err(describe_transclusion_err)?;
        // The reverse-index write: the observation is recorded with the quote's
        // OWN provenance (receipt + content commitment) — idempotent on identical
        // records, so re-rendering a quote never inflates the in-degree.
        demo.backlinks.observe(observer_uri.cell, &field);
        let view = quote_view(&field, demo.web.height())?;
        serde_wasm_bindgen::to_value(&view).map_err(|e| e.to_string())
    })
}

/// **BACKLINKS** (the two-way link, finally honest): enumerate WHO transcludes the
/// source named `name` — the reverse index [`transclusion_include_into`] populates,
/// wrapping the real [`Backlinks::observers_of`]. Each entry carries the cited
/// receipt + content commitment from the observation's provenance, so a backlink is
/// a verifiable claim ("observer O quoted source S's value V at receipt R") that a
/// third party can recheck — never a dangling pointer. Returns a
/// [`BacklinksReadout`]; a source nobody quotes yields an EMPTY readout, not an
/// error.
#[wasm_bindgen]
pub fn transclusion_backlinks(handle: usize, name: &str) -> Result<JsValue, JsError> {
    with_demo_ref(handle, |demo| {
        let uri = demo.uri_of(name)?;
        let observers: Vec<BacklinkView> = demo
            .backlinks
            .observers_of(uri.cell)
            .iter()
            .map(|o| BacklinkView {
                observer_uri: DreggUri::new(o.observer).to_uri_string(),
                observer_name: demo
                    .docs
                    .iter()
                    .find(|(_, u)| u.cell == o.observer)
                    .map(|(n, _)| n.clone())
                    .unwrap_or_default(),
                receipt_hash: hex32(&o.receipt_hash),
                content_hash: hex32(&o.content_hash),
            })
            .collect();
        let readout = BacklinksReadout {
            source_uri: uri.to_uri_string(),
            count: observers.len(),
            observers,
        };
        serde_wasm_bindgen::to_value(&readout).map_err(|e| e.to_string())
    })
}

/// **AMEND** the source named `name` to `new_content` — advance the SAME `dregg://`
/// ref to a NEW finalized value at a NEW height (a verified state advance).
///
/// The REAL [`WebOfCells::amend`]: the `dregg://` ref is UNCHANGED (Nelson's
/// unbreakable link), but it now resolves to the source's NEW committed value, with
/// a fresh serve-receipt + an advanced federation height. A subsequent LIVE read
/// follows it; a SNAPSHOT taken before stays pinned. Returns the new height.
#[wasm_bindgen]
pub fn transclusion_amend(handle: usize, name: &str, new_content: &str) -> Result<u64, JsError> {
    with_demo(handle, |demo| {
        let uri = demo.uri_of(name)?;
        demo.web
            .amend(&uri, new_content.as_bytes())
            .map_err(describe_fetch_err)
    })
}

/// **READ LIVE** the source named `name` — re-resolve to its CURRENT finalized
/// value (the live quote follows every amend). This is a fresh
/// [`TranscludedField::include`] each call, so as the source advances the read
/// shows the new committed value. Returns a [`QuoteView`].
///
/// (The demo distinguishes this from a pinned snapshot taken earlier in JS: the
/// LIVE read updates after `transclusion_amend`, the snapshot does not.)
#[wasm_bindgen]
pub fn transclusion_read_live(handle: usize, name: &str) -> Result<JsValue, JsError> {
    // A live read is definitionally identical to `include` (re-resolve now); the
    // separate entry NAMES the dial position the demo is exercising.
    transclusion_include(handle, name)
}

/// **FORGE ATTEMPT** (the anti-ghost tooth `transclusion_forge_refused`): fetch the
/// source named `name`, then TAMPER the served bytes to `forged_content` and run the
/// genuine client-side verification.
///
/// A lying node that swaps the bytes after the commitment is caught by hop (1) of
/// [`AttestedResource::verify`] — `blake3(bytes) != content_hash` → REFUSED with
/// [`FetchError::ContentHashMismatch`]. A forged quote cannot be opened. Returns a
/// [`ForgeView`] whose `refused` MUST be `true` (the demo asserts the polarity).
#[wasm_bindgen]
pub fn transclusion_forge_attempt(
    handle: usize,
    name: &str,
    forged_content: &str,
) -> Result<JsValue, JsError> {
    with_demo_ref(handle, |demo| {
        let uri = demo.uri_of(name)?;
        // A GENUINE fetch — the honest envelope the source committed.
        let (mut resource, _chrome) = demo.web.fetch(&uri).map_err(describe_fetch_err)?;
        // Tamper the bytes (a malicious node serves different content), keeping the
        // committed content_hash — exactly the forge the client must catch.
        let committed_content_hash = hex32(&resource.content_hash);
        resource.content_bytes = forged_content.as_bytes().to_vec();
        // Run the REAL client verification. It MUST refuse.
        let verdict = resource.verify();
        let (refused, reason) = match &verdict {
            Ok(()) => (
                false,
                "NOT REFUSED — the forge slipped through (bug)".to_string(),
            ),
            Err(e) => (true, fetch_err_name(e)),
        };
        let view = ForgeView {
            refused,
            reason,
            forged_text: forged_content.to_string(),
            committed_content_hash,
        };
        serde_wasm_bindgen::to_value(&view).map_err(|e| e.to_string())
    })
}

/// **PROJECT FOR** a viewer (the no-amplification tooth `transclusion_no_amplify`):
/// transclude the source named `name`, then project it PER-VIEWER through the REAL
/// [`Membrane`] at `viewer_rights`, with the source served under `lineage_rights`.
///
/// A quote confers no authority over the source beyond observing the cited value:
/// the projection meets the viewer's held authority with the lineage through the
/// genuine `is_attenuation` ([`TranscludedField::project_for`]). A weaker viewer
/// receives a strictly attenuated surface; the projection CANNOT amplify. Returns a
/// [`ProjectionView`]. `*_rights` speak the real `AuthRequired` lattice
/// (`none`/`signature`/`proof`/`either`/`impossible`).
#[wasm_bindgen]
pub fn transclusion_project_for(
    handle: usize,
    name: &str,
    viewer_rights: &str,
    lineage_rights: &str,
) -> Result<JsValue, JsError> {
    with_demo_ref(handle, |demo| {
        let uri = demo.uri_of(name)?;
        let field =
            TranscludedField::include(&demo.web, &uri).map_err(describe_transclusion_err)?;

        let viewer_auth = parse_rights(viewer_rights)?;
        let lineage_auth = parse_rights(lineage_rights)?;

        // The source lineage: an authority over the doc cell at `lineage_rights`.
        let lineage = SurfaceCapability::root(uri.cell, lineage_auth.clone());
        // The viewer's own membrane (a distinct cell at `viewer_rights`).
        let viewer = Membrane::new(SurfaceCapability::root(viewer_cell(), viewer_auth.clone()));

        let view = match field.project_for(&viewer, &lineage) {
            Ok(projected) => {
                let projected_rights = projected.window.rights.clone();
                // No-amplification: the projected rights must be ⊆ the lineage rights
                // (the projection never grants MORE than the source's authority). We
                // assert it via the real `is_attenuation` (granted ⊆ held).
                let no_amplify = dregg_cell::is_attenuation(&lineage_auth, &projected_rights);
                ProjectionView {
                    projected: true,
                    viewer_rights: format!("{projected_rights:?}"),
                    lineage_rights: format!("{lineage_auth:?}"),
                    no_amplify,
                    reason: String::new(),
                }
            }
            Err(e) => ProjectionView {
                projected: false,
                viewer_rights: format!("{viewer_auth:?}"),
                lineage_rights: format!("{lineage_auth:?}"),
                no_amplify: true, // a refused projection grants nothing — trivially non-amplifying
                reason: format!("{e:?}"),
            },
        };
        serde_wasm_bindgen::to_value(&view).map_err(|e| e.to_string())
    })
}

// ============================================================================
// Helpers.
// ============================================================================

/// Build a [`QuoteView`] from a verified [`TranscludedField`] (re-verifying it so
/// the `verifies` flag is the live truth, not a stale claim).
fn quote_view(field: &TranscludedField, at_height: u64) -> Result<QuoteView, String> {
    let prov = field.cite();
    let bytes = field.quoted_bytes();
    Ok(QuoteView {
        text: String::from_utf8_lossy(bytes).into_owned(),
        content_hash: hex32(&prov.content_hash),
        receipt_hash: hex32(&prov.receipt_hash),
        source_uri: prov.source.to_uri_string(),
        finalized: prov.finalized,
        at_height,
        chrome_badge: field.chrome.badge(),
        verifies: field.verify().is_ok(),
    })
}

/// Map a [`TransclusionError`] to its teaching string (the genuine variant name).
fn describe_transclusion_err(e: TransclusionError) -> String {
    match e {
        TransclusionError::Fetch(f) => format!("Fetch({})", fetch_err_name(&f)),
        TransclusionError::ProvenanceUnverified(f) => {
            format!("ProvenanceUnverified({})", fetch_err_name(&f))
        }
        TransclusionError::NotFinalized => "NotFinalized".to_string(),
    }
}

/// Map a [`FetchError`] to its teaching string (used where the binding surfaces a
/// raw fetch/amend error).
fn describe_fetch_err(e: FetchError) -> String {
    fetch_err_name(&e)
}

/// The genuine `FetchError` variant name — the demo renders `ContentHashMismatch`
/// for the byte-tamper forge.
fn fetch_err_name(e: &FetchError) -> String {
    match e {
        FetchError::OriginNotFound => "OriginNotFound",
        FetchError::NoContentCommitted => "NoContentCommitted",
        FetchError::ContentHashMismatch => "ContentHashMismatch",
        FetchError::ContentDoesNotMatchCommitment => "ContentDoesNotMatchCommitment",
        FetchError::ReceiptNotInStream => "ReceiptNotInStream",
        FetchError::ReceiptStreamRootMismatch => "ReceiptStreamRootMismatch",
        FetchError::NoQuorum => "NoQuorum",
        FetchError::Unattested => "Unattested",
        FetchError::NonceOverflow => "NonceOverflow",
    }
    .to_string()
}

/// Parse the demo's rights string into the REAL `AuthRequired` lattice element.
/// Speaks the genuine vocabulary (the same the surface bindings accept).
fn parse_rights(s: &str) -> Result<AuthRequired, String> {
    match s.trim().to_ascii_lowercase().as_str() {
        "none" | "writable-open" => Ok(AuthRequired::None),
        "signature" | "read-only" | "sig" => Ok(AuthRequired::Signature),
        "proof" => Ok(AuthRequired::Proof),
        "either" | "writable" => Ok(AuthRequired::Either),
        "impossible" | "sealed" => Ok(AuthRequired::Impossible),
        other => Err(format!(
            "unknown rights {other:?} (want none/signature/proof/either/impossible)"
        )),
    }
}

/// A deterministic, distinct viewer cell id (so the viewer membrane is its OWN cell,
/// incomparable to the source lineage's cell — the projection meets authorities, it
/// does not share a cell).
fn viewer_cell() -> CellId {
    let mut b = [0u8; 32];
    b[0] = 0xAB;
    b[31] = 0xCD;
    CellId::from_bytes(b)
}

/// Lowercase hex of a 32-byte hash.
fn hex32(bytes: &[u8; 32]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

// ---------------------------------------------------------------------------
// BOTH-POLARITY teeth over the EXACT path the `#[wasm_bindgen]` wrappers drive
// (run under plain `cargo test` — they call the real `starbridge-web-surface`
// API directly, no `JsValue`/wasm runtime). Each demo claim is proven TRUE and
// its negation FALSE, so the demo cannot be silently vacuous.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    use super::*;
    use starbridge_web_surface::SurfaceCapability;
    use starbridge_web_surface::rehydrate::Membrane;
    use starbridge_web_surface::transclusion::TranscludedField;
    use starbridge_web_surface::web_of_cells::WebOfCells;

    // (1) INCLUDE — a transclusion IS the verified finalized read: the displayed
    //     bytes ARE the source's committed bytes AND the quote re-verifies (positive),
    //     and an absent source REFUSES (negative).
    #[test]
    fn include_shows_committed_bytes_and_verifies_absent_refuses() {
        let mut web = WebOfCells::new(3);
        let body = b"<h1>the charter</h1>";
        let uri = web.publish(1, body, "dregg://constitution");

        // POSITIVE: the verified read shows the committed bytes + verifies.
        let field = TranscludedField::include(&web, &uri).expect("include resolves");
        assert_eq!(
            field.quoted_bytes(),
            body,
            "displayed bytes ARE the source's"
        );
        assert!(
            field.verify().is_ok(),
            "the quote re-verifies (content→…→quorum)"
        );
        let view = quote_view(&field, web.height()).expect("view");
        assert!(view.verifies, "the QuoteView reports verifies=true");
        assert!(view.finalized, "a 3-of-3 published source is finalized");
        assert_eq!(view.content_hash, hex32(blake3::hash(body).as_bytes()));

        // NEGATIVE: an absent dregg:// ref does not resolve to a finalized read.
        let mut k = [0u8; 32];
        k[0] = 200;
        let absent = DreggUri::new(CellId::derive_raw(&k, &[0u8; 32]));
        let r = TranscludedField::include(&web, &absent);
        assert!(
            matches!(r, Err(TransclusionError::Fetch(FetchError::OriginNotFound))),
            "an absent source is refused at the fetch, got {r:?}"
        );
    }

    // (2) THE LIVE/SNAPSHOT DIAL — after an amend, a LIVE re-read FOLLOWS the new value
    //     (positive: it changed), while a SNAPSHOT captured before STAYS PINNED
    //     (negative: it did NOT change). This is the live-quote tooth the demo touches.
    #[test]
    fn amend_makes_live_follow_while_snapshot_stays_pinned() {
        let mut web = WebOfCells::new(3);
        let v0 = b"<p>threshold = 3</p>";
        let uri = web.publish(2, v0, "dregg://constitution");

        // Capture a snapshot of v0 (a client-side pin of the verified quote).
        let snapshot = TranscludedField::include(&web, &uri).expect("snapshot v0");
        let snap_hash = snapshot.cite().content_hash;
        assert_eq!(snapshot.quoted_bytes(), v0);

        // Amend the SAME ref to v1 (a new finalized value at a new height).
        let v1 = b"<p>threshold = 5 (amended)</p>";
        let h0 = web.height();
        let h1 = web.amend(&uri, v1).expect("amend resolves");
        assert!(h1 > h0, "the federation height advanced");

        // POSITIVE — the LIVE re-read followed the amend (a fresh include shows v1).
        let live = TranscludedField::include(&web, &uri).expect("live re-read");
        assert_eq!(live.quoted_bytes(), v1, "the live quote followed the amend");
        assert_ne!(
            live.cite().content_hash,
            snap_hash,
            "live diverged from the snapshot (the source moved)"
        );
        assert!(live.verify().is_ok(), "the live read still verifies");

        // NEGATIVE — the SNAPSHOT stayed pinned: its cached bytes are STILL v0, and it
        // STILL verifies (its pinned receipt remains a valid leaf — I-confluence). The
        // pin did NOT follow the amend.
        assert_eq!(snapshot.quoted_bytes(), v0, "the snapshot stayed at v0");
        assert_eq!(
            snapshot.cite().content_hash,
            snap_hash,
            "the pin did not move"
        );
        assert!(
            snapshot.verify().is_ok(),
            "the pinned snapshot re-verifies forever"
        );
    }

    // (3) THE FORGE — a lying node that swaps the bytes is REFUSED with
    //     ContentHashMismatch (positive: refused), while the GENUINE bytes pass
    //     (negative: an un-tampered fetch verifies). The anti-ghost tooth.
    #[test]
    fn forge_is_refused_with_content_hash_mismatch_genuine_passes() {
        let mut web = WebOfCells::new(3);
        let real = b"<h1>the charter</h1>";
        let uri = web.publish(3, real, "dregg://constitution");

        // NEGATIVE (the honest path): the un-tampered fetch verifies.
        let (genuine, _chrome) = web.fetch(&uri).expect("genuine fetch");
        assert!(genuine.verify().is_ok(), "the genuine envelope verifies");

        // POSITIVE (the forge): tamper the served bytes; the client refuses, and the
        // refusal is specifically ContentHashMismatch — blake3(forged) ≠ content_hash.
        let (mut forged, _c) = web.fetch(&uri).expect("fetch");
        forged.content_bytes = b"<h1>PWNED</h1>".to_vec();
        assert_eq!(
            forged.verify(),
            Err(FetchError::ContentHashMismatch),
            "a byte-tamper forge is refused with ContentHashMismatch"
        );
        // And the binding's name-mapper renders exactly that teaching string.
        assert_eq!(
            fetch_err_name(&FetchError::ContentHashMismatch),
            "ContentHashMismatch"
        );
    }

    // (4) NO AMPLIFICATION — a weaker viewer's projection is ATTENUATED to its ceiling
    //     (positive: weaker stays weaker), and a wide-open viewer can NEVER amplify past
    //     a read-only lineage (negative: the projected rights ⊆ the lineage rights). A
    //     quote is a READ, per-viewer, through the real membrane.
    #[test]
    fn projection_attenuates_weaker_and_never_amplifies() {
        let mut web = WebOfCells::new(3);
        let uri = web.publish(4, b"<h1>doc</h1>", "dregg://constitution");
        let field = TranscludedField::include(&web, &uri).expect("include");

        // POSITIVE — a weaker (Signature) viewer of an Either lineage projects to its
        // own Signature ceiling (attenuated, never the strong lineage's Either).
        let lineage = SurfaceCapability::root(uri.cell, AuthRequired::Either);
        let weak = Membrane::new(SurfaceCapability::root(
            viewer_cell(),
            AuthRequired::Signature,
        ));
        let proj = field
            .project_for(&weak, &lineage)
            .expect("weaker viewer projects");
        assert_eq!(
            proj.window.rights,
            AuthRequired::Signature,
            "the transclusion is attenuated to the weaker viewer"
        );
        assert!(
            dregg_cell::is_attenuation(&AuthRequired::Either, &proj.window.rights),
            "projected ⊆ lineage (no amplification)"
        );

        // NEGATIVE — a wide-open (None) viewer of a READ-ONLY (Signature) lineage is
        // met DOWN to the lineage's ceiling; the projection cannot grant more than the
        // source serves. The projected rights are attenuated by the Signature lineage,
        // so they never amplify past read-only.
        let ro_lineage = SurfaceCapability::root(uri.cell, AuthRequired::Signature);
        let wide = Membrane::new(SurfaceCapability::root(viewer_cell(), AuthRequired::None));
        let proj2 = field
            .project_for(&wide, &ro_lineage)
            .expect("wide viewer projects");
        assert!(
            dregg_cell::is_attenuation(&AuthRequired::Signature, &proj2.window.rights),
            "a wide-open viewer NEVER amplifies past the read-only lineage (projected ⊆ Signature)"
        );
    }

    // (5) THE DEMO STORE — publish registers a name→ref the include path resolves
    //     (positive), and an unknown name is a clear error (negative). The handle store
    //     the wasm wrappers ride.
    #[test]
    fn demo_store_resolves_published_names_unknown_errors() {
        let mut demo = TransclusionDemo::new();
        let uri = demo
            .web
            .publish(demo.next_seed, b"<p>x</p>", "dregg://constitution");
        demo.docs.push(("constitution".to_string(), uri.clone()));

        // POSITIVE: the registered name resolves to the published ref.
        assert_eq!(demo.uri_of("constitution").unwrap(), uri);
        // NEGATIVE: an unknown name is a clear error (never a silent default).
        assert!(demo.uri_of("nope").is_err(), "an unknown doc name errors");
    }

    // (7) THE TWO-WAY LINK — the include-into path records a receipt-pinned backlink
    //     the readout enumerates (positive), re-quoting at the same receipt is
    //     idempotent AND an unquoted source has an EMPTY readout / an unpublished
    //     observer is a clear error (negative). The exact store+registry logic the
    //     `transclusion_include_into` / `transclusion_backlinks` wrappers ride.
    #[test]
    fn include_into_records_backlinks_unquoted_empty_unknown_observer_errors() {
        let mut demo = TransclusionDemo::new();
        // Publish a source + TWO observer documents (each a real published cell —
        // an observer quotes FROM its own dregg:// cell).
        let src = demo
            .web
            .publish(1, b"<h1>the charter</h1>", "dregg://constitution");
        demo.docs.push(("constitution".to_string(), src.clone()));
        let essay = demo.web.publish(2, b"<p>my essay</p>", "dregg://essay");
        demo.docs.push(("essay".to_string(), essay.clone()));
        let review = demo.web.publish(3, b"<p>a review</p>", "dregg://review");
        demo.docs.push(("review".to_string(), review.clone()));

        // POSITIVE: both observers transclude the source; the reverse index
        // enumerates exactly the two, each pinned to the quote's OWN provenance
        // (receipt + content commitment — the verifiable backlink).
        let field = TranscludedField::include(&demo.web, &src).expect("include resolves");
        demo.backlinks.observe(essay.cell, &field);
        demo.backlinks.observe(review.cell, &field);
        // …and the essay re-quoting at the same receipt is idempotent (a re-render
        // never inflates the in-degree):
        demo.backlinks.observe(essay.cell, &field);

        let observers = demo.backlinks.observers_of(src.cell);
        assert_eq!(
            observers.len(),
            2,
            "two distinct observers, no double-count"
        );
        assert!(
            observers
                .iter()
                .all(|o| o.receipt_hash == field.cite().receipt_hash
                    && o.content_hash == field.cite().content_hash),
            "every backlink is pinned to the cited receipt + content commitment"
        );
        // The name mapping the readout renders: an observer cell that IS a named
        // demo document resolves back to its name.
        let named: Vec<&str> = observers
            .iter()
            .filter_map(|o| {
                demo.docs
                    .iter()
                    .find(|(_, u)| u.cell == o.observer)
                    .map(|(n, _)| n.as_str())
            })
            .collect();
        assert!(named.contains(&"essay") && named.contains(&"review"));

        // NEGATIVE: a source nobody quotes has an EMPTY readout (not an error)…
        assert!(
            demo.backlinks.observers_of(essay.cell).is_empty(),
            "nobody quotes the essay — empty readout"
        );
        // …and an unpublished observer name is a clear error via the store (the
        // wrapper's observer gate), never a silent default.
        assert!(
            demo.uri_of("ghost").is_err(),
            "an unpublished observer errors"
        );
    }

    // (6) The rights vocabulary the projection accepts is the REAL AuthRequired lattice.
    #[test]
    fn parse_rights_speaks_the_real_lattice() {
        assert_eq!(parse_rights("none").unwrap(), AuthRequired::None);
        assert_eq!(parse_rights("signature").unwrap(), AuthRequired::Signature);
        assert_eq!(parse_rights("read-only").unwrap(), AuthRequired::Signature);
        assert_eq!(parse_rights("either").unwrap(), AuthRequired::Either);
        assert_eq!(parse_rights("writable").unwrap(), AuthRequired::Either);
        assert_eq!(
            parse_rights("impossible").unwrap(),
            AuthRequired::Impossible
        );
        assert!(
            parse_rights("garbage").is_err(),
            "unknown rights error, no silent default"
        );
    }
}
