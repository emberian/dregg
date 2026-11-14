//! THE ONE UNIFIED BOOT — node + cockpit-panes in a SINGLE window/frame.
//!
//! [`crate::self_hosting`] proves the editor↔terminal self-hosting loop over an
//! EMBEDDED `World`. This view proves the OTHER unification: the same cockpit
//! panes (FirmamentFs editor + live PTY terminal) standing ALONGSIDE a LIVE
//! `--node`-attached pane whose cells/receipts/status come from a real running
//! `dregg-node` over the wire (`/status` + `/api/cells` + `/api/receipts`),
//! reflected through the SAME [`crate::live_node::LiveReflection`] the cockpit's
//! own live-node strip uses — not a mock.
//!
//! Three panes, one frame:
//!
//!   * **LIVE NODE** — a real [`crate::client::LiveNode::sync`] snapshot of the
//!     attached node: its `/status` (lean producer, height, dag) + every live
//!     cell + the latest receipt, each projected into the uniform reflective
//!     model. This is what proves the attach is LIVE, not embedded: the cells and
//!     the receipt shown are the node's, pulled over HTTP at build time.
//!
//!   * **EDITOR** — a [`crate::dock::editor_surface::EditorPane::firmament_over`]
//!     the cockpit's LOCAL `World`. A save is a cap-gated `SetField` turn on that
//!     LOCAL ledger. (The write-back seam — whether that turn reaches the NODE's
//!     ledger — is exercised + reported by the headless bake, not papered over:
//!     today the save lands on the cockpit World, the node is read-only-synced.)
//!
//!   * **TERMINAL** — a live alacritty PTY running a real command INSIDE deos.
//!
//! The headless bake (`--render-unified-boot` in `main.rs`) wires all three over a
//! running node, drives a real editor save, re-reads the node's receipt count to
//! settle the write-back question empirically, and captures the PNG.

use std::cell::RefCell;
use std::rc::Rc;

use gpui::{
    div, px, App, AppContext, Context, Entity, FocusHandle, Focusable, InteractiveElement,
    IntoElement, ParentElement, Render, Styled, Window,
};

use crate::client::{LiveNode, LiveSnapshot};
use crate::dock::editor_surface::EditorPane;
use crate::dock::surface::CockpitSurface;
use crate::dock::terminal_surface::TerminalPane;
use crate::reflect::{Field, FieldValue, Inspectable, ObjectKind};
use crate::world::World;

/// The palette is [`crate::views::theme`] — this file used to hold its own
/// transcription of the hexes.
///
/// ⚠ And that transcription had DRIFTED: its `good()` was a visibly MINTIER green
/// than every sibling copy's — rgb(91,209,139) against rgb(87,217,119). The fold
/// preserves this surface's green bit-exact by reading
/// `views::theme::good_mint`, which carries the hex, the delta, and the choice
/// between the two greens, all in one place.
use crate::views::theme;

use crate::views::theme::good_mint as good;

/// The seed project the firmament editor opens onto, installed on the LOCAL
/// cockpit `World`. A save here is a receipted turn on THAT ledger.
const UNIFIED_SEED: &[(&str, &str)] = &[(
    "/main.rs",
    "// edit me — a save is a cap-gated SetField turn (a real TurnReceipt) on the\n\
     // cockpit's LOCAL World ledger. The live-node pane to the left reflects a\n\
     // SEPARATE, real running dregg-node over the wire.\n\
     fn main() {\n    println!(\"v1\");\n}\n",
)];

/// The dev passphrase the unified-boot bake uses to unlock the attached node's
/// operator cipherclerk. On a fresh dev node the FIRST unlock SETS this; on a
/// re-run against the same data dir it must match (the runbook node uses this).
/// This is the cockpit's local key custody for node writes (see
/// [`crate::client::NodeClient::unlock`]).
const NODE_DEV_PASSPHRASE: &str = "deos-dev-unified-boot";

/// The root view mounting all three unified-boot panes.
pub struct UnifiedBootView {
    /// A wrapped client to the attached node, so the bake can RE-READ the node's
    /// live receipt/cell count after an editor save (the write-back probe).
    ///
    /// When the cockpit is `--node`-attached AND the node unlocks, this client
    /// carries the operator bearer token, so the editor save can route a real
    /// `SetField` turn through the node's verified executor (`/turn/submit`) — the
    /// write-back seam, closed. An unreachable/locked node leaves it read-only.
    live_node: Option<LiveNode>,
    /// The last fetched live snapshot of the attached node (status + cells).
    snapshot: Option<LiveSnapshot>,
    /// The latest receipt reflected from the node (the live provenance head).
    receipt_view: Option<Inspectable>,
    editor: EditorPane,
    terminal: TerminalPane,
    /// The local cockpit `World` the editor saves into.
    world: Rc<RefCell<World>>,
    /// The proof the LAST in-editor save produced on the node, set by the editor's
    /// own save callback (the node wire). `None` until the first node-routed save.
    /// The interactive-save bake reads this AFTER driving the editor pane's own
    /// `save` to prove the node receipt grew through the Cmd-S path (not a direct
    /// `save_to_node` call).
    #[cfg(feature = "embedded-executor")]
    last_node_save: Rc<RefCell<Option<ClientSignedProof>>>,
    focus: FocusHandle,
}

impl UnifiedBootView {
    /// Build the unified-boot view: the live-node pane (a real snapshot of the
    /// node at `node_url`, if reachable) + a firmament editor over `world` + a
    /// live-PTY terminal. An unreachable / absent node leaves the pane showing
    /// "(no node attached)" and the editor+terminal fully live — honest.
    pub fn build(
        world: Rc<RefCell<World>>,
        node_url: Option<String>,
        terminal_cmd: Option<(String, Vec<String>)>,
        window: &mut Window,
        cx: &mut App,
    ) -> anyhow::Result<Self> {
        Self::build_with_user(world, node_url, None, terminal_cmd, window, cx)
    }

    /// Build the unified-boot view, optionally threading the LOGGED-IN USER's dev
    /// signing seed (`session.signing_seed`). When a seed is present AND the node is
    /// attached + write-credentialed, the editor pane's OWN save path (the callback a
    /// real Cmd-S invokes) is wired to submit a CLIENT-SIGNED turn to the live node —
    /// the interactive self-hosting wire. Without a seed (or without a node) the save
    /// stays local-only, unchanged.
    pub fn build_with_user(
        world: Rc<RefCell<World>>,
        node_url: Option<String>,
        user_seed: Option<[u8; 64]>,
        terminal_cmd: Option<(String, Vec<String>)>,
        window: &mut Window,
        cx: &mut App,
    ) -> anyhow::Result<Self> {
        let root = std::env::current_dir().unwrap_or_else(|_| std::path::PathBuf::from("."));

        // LIVE NODE — wrap a real HTTP client and take ONE blocking snapshot. This
        // is the SAME `LiveNode::sync` the cockpit's `--node` attach uses; the
        // cells/receipts shown are the node's, pulled over the wire right now.
        let (live_node, snapshot, receipt_view) = match node_url {
            Some(url) => {
                // Read with a plain client; then UNLOCK the node's operator
                // cipherclerk so the editor save can WRITE BACK (route a real
                // `SetField` turn through `/turn/submit`). The unlocked, authed
                // client replaces the plain one; if unlock fails (node locked with
                // a different passphrase) we keep the read-only client and the
                // write-back honestly reports it could not authenticate.
                let plain = crate::client::NodeClient::http(url.clone());
                let authed = match plain.unlock(NODE_DEV_PASSPHRASE) {
                    Ok(token) => plain.with_bearer(token),
                    Err(e) => {
                        eprintln!(
                            "unified-boot: node {url} unlock failed ({e:#}); editor save will \
                             be read-only against the node (no write-back credential)"
                        );
                        plain
                    }
                };
                let ln = LiveNode::new(authed);
                let snap = ln.sync().ok();
                // The latest committed receipt. `/api/receipts` returns the FULL
                // receipt shape (a superset of the SSE-summary `ReceiptEvent`), so
                // the typed `receipts()` parse rejects it; reflect the raw JSON of
                // the chain head directly — the genuine on-node provenance node.
                let receipt = ln
                    .client()
                    .receipts_raw()
                    .ok()
                    .and_then(|rs| rs.into_iter().next())
                    .map(|raw| raw_receipt_inspectable(&raw));
                (Some(ln), snap, receipt)
            }
            None => (None, None, None),
        };

        // EDITOR — firmament over the LOCAL cockpit World (a save = a real turn on
        // THAT ledger). This is the write-back seam under test.
        let editor =
            EditorPane::firmament_over(1, world.clone(), root.clone(), UNIFIED_SEED, window, cx)?;

        #[cfg(feature = "embedded-executor")]
        let last_node_save: Rc<RefCell<Option<ClientSignedProof>>> = Rc::new(RefCell::new(None));

        // THE INTERACTIVE NODE WIRE: when `--node`-attached, write-credentialed, AND
        // we hold the logged-in user's signing seed, install the editor's OWN save
        // callback (the closure a real Cmd-S → `Editor::save` invokes) to ALSO submit
        // a client-signed turn to the live node. So an in-editor save is BOTH a local
        // firmament turn AND a real on-node receipt under the USER's authority — the
        // last self-hosting wire, driven by the editor pane itself, not a direct call.
        #[cfg(feature = "embedded-executor")]
        if let (Some(seed), Some(ln)) = (user_seed, live_node.as_ref()) {
            if ln.client().bearer().is_some() {
                // The node pubkey (federation-id source) off the live snapshot.
                let node_pubkey_hex = snapshot
                    .as_ref()
                    .map(|s| s.status.public_key.clone())
                    .unwrap_or_default();
                // Capture cheap clones into the 'static save callback: the client (by
                // value `Clone`), the node pubkey hex, the user seed (Copy), and a
                // handle to record the proof for the bake to read.
                let client = ln.client().clone();
                let proof_slot = last_node_save.clone();
                // A monotonic slot per save so successive saves write distinct field
                // elements (the node's nonce advances; the slot keeps the content
                // fingerprint addressable). Closure-owned, bumped each fire.
                let slot = std::cell::Cell::new(7usize);
                let cb: deos_zed::editor::SaveCallback = Box::new(move |content: &str| {
                    let clerk = dregg_sdk::AgentCipherclerk::from_seed(seed);
                    let idx = slot.get();
                    slot.set(idx + 1);
                    // A short content fingerprint (the node's `parse_field_element`
                    // convention): the low bytes of a blake3 of the saved content.
                    let fp = {
                        let h = blake3::hash(content.as_bytes());
                        let mut n = [0u8; 8];
                        n.copy_from_slice(&h.as_bytes()[..8]);
                        u64::from_le_bytes(n).to_string()
                    };
                    match client_signed_save(&client, &node_pubkey_hex, &clerk, idx, &fp) {
                        Ok(proof) => {
                            let note = format!(
                                "node receipts {}→{} (client-signed, agent {}…)",
                                proof.before,
                                proof.after,
                                proof.receipt_agent.chars().take(8).collect::<String>(),
                            );
                            *proof_slot.borrow_mut() = Some(proof);
                            Ok(note)
                        }
                        Err(e) => Err(format!("{e:#}")),
                    }
                });
                editor.set_save_callback(cb, cx);
            }
        }

        // TERMINAL — a live PTY running a real command.
        let terminal = TerminalPane::spawn(2, terminal_cmd, cx)?;

        Ok(Self {
            live_node,
            snapshot,
            receipt_view,
            editor,
            terminal,
            world,
            #[cfg(feature = "embedded-executor")]
            last_node_save,
            focus: cx.focus_handle(),
        })
    }

    /// The proof the LAST in-editor save produced on the node (set by the editor's
    /// own save callback). `None` until an in-editor save routed to the node. The
    /// interactive-save bake reads this after driving the editor pane's `save`.
    #[cfg(feature = "embedded-executor")]
    pub fn last_node_save(&self) -> Option<ClientSignedProof> {
        self.last_node_save.borrow().clone()
    }

    /// Whether the editor pane has the node-wire save callback installed (the
    /// cockpit is `--node`-attached + write-credentialed + holds the user seed).
    pub fn editor_has_node_wire(&self, cx: &App) -> bool {
        self.editor.editor().read(cx).has_save_callback()
    }

    /// Fire a REAL editor save (set buffer + the editor's genuine `save`, a
    /// cap-gated `SetField` turn through the verified executor on the LOCAL
    /// World). Returns the LOCAL on-ledger receipt count after the save.
    pub fn fire_save(
        &self,
        content: &str,
        window: &mut Window,
        cx: &mut App,
    ) -> anyhow::Result<usize> {
        let editor = self.editor.editor().clone();
        editor.update(cx, |ed, cx| {
            ed.set_text(content, window, cx);
            ed.save(cx)
        })?;
        Ok(self.editor.receipt_count().unwrap_or(0))
    }

    /// The local cockpit World's receipt count (the editor-save ledger).
    pub fn world_receipt_count(&self) -> usize {
        self.world.borrow().receipts().len()
    }

    /// ROUTE AN EDITOR SAVE TO THE NODE — the write-back seam, closed.
    ///
    /// When the cockpit is `--node`-attached and the node is unlocked, an editor
    /// save becomes a real `SetField` turn submitted to the NODE's verified
    /// executor (`POST /turn/submit`): the node runs it through the same
    /// `gateOK`/conservation/authority gates as every turn, commits it to its
    /// ledger (growing `/api/receipts`), signs it as the operator cipherclerk, and
    /// orders/gossips it — exactly what a separate client of that node would see.
    /// The `target` is omitted, so the node defaults it to the operator's own
    /// agent cell (which it always has authority over); `index`/`value` carry the
    /// save's content fingerprint into a state slot — a genuine on-ledger write.
    ///
    /// Returns `Ok((before, after))` node receipt counts (the empirical proof:
    /// `after == before + 1`), or an error if the node refused the turn (in-band)
    /// or the submit failed (e.g. no write credential). `None` if no node attached.
    pub fn save_to_node(
        &self,
        index: usize,
        value: &str,
    ) -> Option<anyhow::Result<(usize, usize)>> {
        let ln = self.live_node.as_ref()?;
        Some(self.save_to_node_inner(ln, index, value))
    }

    fn save_to_node_inner(
        &self,
        ln: &LiveNode,
        index: usize,
        value: &str,
    ) -> anyhow::Result<(usize, usize)> {
        use crate::model::{SubmitTurnRequest, TurnActionSpec, TurnEffectSpec};

        let client = ln.client();
        if client.bearer().is_none() {
            anyhow::bail!(
                "node has no operator write credential (unlock failed at attach); the editor \
                 save cannot write back to the node ledger"
            );
        }
        let before = client.receipts_count()?;

        // A real `SetField` turn: target omitted (defaults to the operator's own
        // agent cell), one state slot set to the save's content fingerprint. This
        // is the smallest genuine end-to-end write — a save = a verified turn on
        // the node, not a local-only `World` commit.
        let req = SubmitTurnRequest {
            // Advisory only (the node derives the real signer from its cipherclerk
            // pubkey — confused-deputy hardening). Carry the node's pubkey so the
            // diagnostic is meaningful; it is parsed for validation, never trusted.
            agent: self
                .snapshot
                .as_ref()
                .map(|s| s.status.public_key.clone())
                .unwrap_or_default(),
            nonce: 0, // node auto-fills the agent cell's live nonce
            fee: 0,
            memo: Some("deos editor save (unified boot)".into()),
            actions: vec![TurnActionSpec {
                target: None,
                method: Some("save".into()),
                effects: vec![TurnEffectSpec::SetField {
                    cell: None,
                    index,
                    value: value.to_string(),
                }],
            }],
        };

        let resp = client.submit_turn(&req)?;
        if !resp.accepted {
            anyhow::bail!(
                "the node REFUSED the editor save turn: {}",
                resp.error.unwrap_or_else(|| "no reason given".into())
            );
        }
        let after = client.receipts_count()?;
        Ok((before, after))
    }

    /// ROUTE AN EDITOR SAVE TO THE NODE AS A *CLIENT-SIGNED* TURN — the "corporate
    /// account" model: the agent of the committed turn is the LOGGED-IN USER's OWN
    /// cell, signed under the user's OWN ed25519 key, NOT the node operator.
    ///
    /// The node (`POST /turns/submit`) VERIFIES the user's signature, derives the
    /// agent as `derive_raw(user_pubkey, blake3("default"))`, requires the turn's
    /// agent to equal that (so the signer IS the agent — a non-operator client
    /// cell), then runs the SAME `gateOK`/conservation/authority gates and commits
    /// under the CLIENT's authority. One node thus hosts many sovereign identities,
    /// each signing their own turns; the node orders + validates but never
    /// impersonates.
    ///
    /// Steps (proven by running):
    ///   1. Faucet-materialize the user's default cell at balance 0 (a turn cannot
    ///      conjure its own agent cell; the node rejects an unknown agent).
    ///   2. Build a `SetField` turn, signed over the node's executor federation id
    ///      (`blake3(node_pubkey)` on an unconfigured solo node — the same domain the
    ///      executor verifies each action signature against), stamp `valid_until`
    ///      (so it stays on the verified Lean producer's wire marshal), and submit it.
    ///   3. Assert the node `/api/receipts` grew AND the new receipt's agent is the
    ///      USER's cell, not the operator's.
    ///
    /// `clerk` is the logged-in user's `AgentCipherclerk` (held by the session, dev
    /// seed for now). Returns the proof on success, an error on refusal. `None` if
    /// no node attached.
    #[cfg(feature = "embedded-executor")]
    pub fn save_to_node_client_signed(
        &self,
        clerk: &dregg_sdk::AgentCipherclerk,
        index: usize,
        value: &str,
    ) -> Option<anyhow::Result<ClientSignedProof>> {
        let ln = self.live_node.as_ref()?;
        Some(self.client_signed_inner(ln, clerk, index, value))
    }

    #[cfg(feature = "embedded-executor")]
    fn client_signed_inner(
        &self,
        ln: &LiveNode,
        clerk: &dregg_sdk::AgentCipherclerk,
        index: usize,
        value: &str,
    ) -> anyhow::Result<ClientSignedProof> {
        // The node's executor federation id derives from the node pubkey on the
        // live `/status` snapshot — read it off the snapshot this view holds, then
        // delegate to the free function (the SAME code the in-editor save callback
        // runs, so one client-signed path, two callers).
        let node_pubkey_hex = self
            .snapshot
            .as_ref()
            .map(|s| s.status.public_key.clone())
            .ok_or_else(|| anyhow::anyhow!("no node snapshot — cannot derive the federation id"))?;
        client_signed_save(ln.client(), &node_pubkey_hex, clerk, index, value)
    }
}

/// SUBMIT A CLIENT-SIGNED EDITOR SAVE TO THE NODE — the free function both the
/// bake's direct [`UnifiedBootView::save_to_node_client_signed`] and the in-editor
/// save callback ([`UnifiedBootView::build`]'s node wire) run, so the interactive
/// Cmd-S path and the direct bake call exercise the EXACT same client-signed turn.
///
/// The agent is the logged-in user's OWN cell (signed under the user's ed25519
/// key); the node verifies the signature, requires `agent == derive_raw(user_pubkey,
/// blake3("default"))`, runs the same `gateOK`/conservation/authority gates, and
/// commits under the CLIENT's authority. Returns the [`ClientSignedProof`] (receipt
/// count grew + the committed agent is the user's cell, not the operator's).
#[cfg(feature = "embedded-executor")]
pub fn client_signed_save(
    client: &crate::client::NodeClient,
    node_pubkey_hex: &str,
    clerk: &dregg_sdk::AgentCipherclerk,
    index: usize,
    value: &str,
) -> anyhow::Result<ClientSignedProof> {
    if client.bearer().is_none() {
        anyhow::bail!(
            "node has no operator write credential (unlock failed at attach); /turns/submit \
             is bearer-gated even for a client-signed turn"
        );
    }

    // The node's executor federation id: for an unconfigured solo node this is
    // `blake3(node_pubkey)`. The client MUST sign each action over THIS domain
    // or the executor rejects the Ed25519 signature.
    let node_pubkey = decode_hex32(node_pubkey_hex)
        .ok_or_else(|| anyhow::anyhow!("node /status public_key is not 32-byte hex"))?;
    let federation_id = *blake3::hash(&node_pubkey).as_bytes();

    // The user's OWN cell (the agent the node will derive + require). The
    // operator's own agent cell (for the "agent != operator" proof) is the node
    // pubkey's default cell — derived identically.
    let user_cell = clerk.cell_id("default");
    let user_pubkey = clerk.public_key().0;
    let user_cell_hex = hex::encode(user_cell.0);
    let user_pubkey_hex = hex::encode(user_pubkey);
    let operator_cell =
        dregg_cell::CellId::derive_raw(&node_pubkey, blake3::hash(b"default").as_bytes());
    let operator_cell_hex = hex::encode(operator_cell.0);

    // (1) Materialize the user cell so its first turn has an existing agent.
    if !client.faucet_materialize(&user_cell_hex, &user_pubkey_hex)? {
        anyhow::bail!(
            "faucet could not materialize the user cell {user_cell_hex} (is the node \
                 started with --enable-faucet?)"
        );
    }

    let before = client.receipts_count()?;

    // The node's executor requires the turn's `previous_receipt_hash` to equal THIS
    // AGENT's own receipt-chain head, not the node's. A client cannot know that
    // locally — its own clerk chain is empty — so read it off `/api/cell/{id}`, which
    // serves exactly `agent_receipt_head_hash` as `last_receipt_hash`. Reading
    // `/api/receipts` newest-first (what this did) answers a different question: that
    // array interleaves every agent, so the moment the faucet materialize above
    // committed — one line earlier, every single boot — the head belonged to the
    // FAUCET and the user's turn was refused as a receipt-chain mismatch. `None`
    // (a cell at genesis) leaves it unstamped.
    let prev_head = client
        .cell_receipt_head(&user_cell_hex)
        .ok()
        .flatten()
        .and_then(|h| decode_hex32(&h));

    // (2) Build + sign the SetField turn AS THE USER, over the node's federation id.
    let effect = dregg_turn::Effect::SetField {
        cell: user_cell,
        index: index as u64,
        value: field_element_from(value),
    };
    let action = clerk.make_action(user_cell, "save", vec![effect], &federation_id);
    let mut turn = clerk.make_turn(action);
    // Thread the node's chain head so the executor's receipt-chain check passes.
    turn.previous_receipt_hash = prev_head;
    // Stamp `valid_until` so the turn stays on the verified Lean producer's wire
    // marshal (an unstamped turn falls back to the Rust path; it still commits,
    // but we keep it on the covered producer to match the operator path). It is a
    // block height: the node's `latest_height` plus the default horizon.
    let latest_height = client.status()?.latest_height;
    turn.valid_until = Some(dregg_turn::valid_until_at(
        latest_height,
        dregg_turn::DEFAULT_TURN_VALIDITY_HORIZON_BLOCKS,
    ));
    let signed = clerk.sign_turn(&turn);

    // (3) Submit + assert.
    let resp = client.submit_signed_turn(&signed)?;
    if !resp.accepted {
        anyhow::bail!(
            "the node REFUSED the client-signed turn: {}",
            resp.error.unwrap_or_else(|| "no reason given".into())
        );
    }
    let after = client.receipts_count()?;

    // The new receipt's agent, read off the chain head — must be the USER's cell.
    let receipt_agent = client
        .receipts_raw()
        .ok()
        .and_then(|rs| rs.into_iter().next())
        .and_then(|raw| raw.get("agent").and_then(|v| v.as_str()).map(String::from))
        .unwrap_or_default();

    Ok(ClientSignedProof {
        before,
        after,
        user_cell: user_cell_hex,
        operator_cell: operator_cell_hex,
        receipt_agent,
        signer: resp.signer.unwrap_or_default(),
        turn_hash: resp.turn_hash.unwrap_or_default(),
    })
}

impl UnifiedBootView {
    /// RE-SYNC the attached node over the wire (status + cells + chain-head
    /// receipt) so the live-node pane reflects the post-write-back state — e.g.
    /// the new receipt the editor save just committed shows up in the screenshot.
    /// No-op if no node is attached.
    pub fn refresh_node(&mut self) {
        let Some(ln) = self.live_node.as_ref() else {
            return;
        };
        if let Ok(snap) = ln.sync() {
            self.snapshot = Some(snap);
        }
        self.receipt_view = ln
            .client()
            .receipts_raw()
            .ok()
            .and_then(|rs| rs.into_iter().next())
            .map(|raw| raw_receipt_inspectable(&raw));
    }

    /// RE-READ the ATTACHED NODE's live receipt count over the wire — the
    /// write-back probe. If an editor save reaches the node's ledger, this grows;
    /// if the save is local-only (today's reality), it does not. `None` if no node.
    pub fn node_receipt_count(&self) -> Option<usize> {
        let ln = self.live_node.as_ref()?;
        ln.client().receipts_count().ok()
    }

    /// RE-READ the attached node's live cell count over the wire.
    pub fn node_cell_count(&self) -> Option<usize> {
        let ln = self.live_node.as_ref()?;
        ln.client().cells().ok().map(|cs| cs.len())
    }

    /// Whether a node is attached AND its last snapshot reported the lean producer.
    pub fn node_lean_producer(&self) -> Option<bool> {
        self.snapshot.as_ref().map(|s| s.status.lean_producer)
    }

    /// Write a line to the live PTY (e.g. a command + `\n`).
    pub fn terminal_input(&self, s: &str, cx: &App) {
        self.terminal.view().read(cx).terminal.write_str(s);
    }

    /// Scrape the terminal grid into a newline-joined string (the live child's
    /// genuine on-grid output, for the host to assert against).
    pub fn terminal_text(&self, cx: &App) -> String {
        let content = self.terminal.view().read(cx).terminal.content();
        let cols = content.columns.max(1);
        let rows = content.screen_lines.max(1);
        let mut grid = vec![vec![' '; cols]; rows];
        for cell in &content.cells {
            let line = cell.line;
            if line < 0 {
                continue;
            }
            let (r, c) = (line as usize, cell.column);
            if r < rows && c < cols {
                grid[r][c] = cell.c;
            }
        }
        grid.into_iter()
            .map(|row| row.into_iter().collect::<String>().trim_end().to_string())
            .collect::<Vec<_>>()
            .join("\n")
    }
}

impl Focusable for UnifiedBootView {
    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus.clone()
    }
}

impl Render for UnifiedBootView {
    fn render(&mut self, window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        let editor_body = self.editor.render_body(window, cx);
        let terminal_body = self.terminal.render_body(window, cx);

        let local_receipts = self.world_receipt_count();
        let local_height = self.world.borrow().height();
        let local_cells = self.world.borrow().cell_count();

        let header = div()
            .flex()
            .items_center()
            .gap_3()
            .px_4()
            .py_2()
            .w_full()
            .bg(theme::panel())
            .border_b_1()
            .border_color(theme::border())
            .child(
                div()
                    .text_color(theme::accent())
                    .child("deos · UNIFIED BOOT — live node + editor + terminal, one window"),
            )
            .child(badge(&format!("local h{local_height}"), theme::accent()))
            .child(badge(
                &format!("{local_cells} local cells"),
                theme::accent(),
            ))
            .child(badge(
                &format!("{local_receipts} local receipts"),
                theme::accent(),
            ));

        let node_pane = framed(
            "live node · --node (a real running dregg-node, over the wire)",
            "its /status + cells + latest receipt, reflected live",
            self.render_node_pane(),
        );
        // When the node is attached AND unlocked (we hold its operator bearer),
        // the editor save writes BACK to the node: a real SetField turn through
        // the node's verified executor. Label honestly per the live credential.
        let node_writeback = self
            .live_node
            .as_ref()
            .map(|ln| ln.client().bearer().is_some())
            .unwrap_or(false);
        let (editor_title, editor_sub) = if node_writeback {
            (
                "editor · deos-zed (firmament over the LIVE NODE)",
                "a save = a cap-gated SetField turn → committed on the NODE ledger (/turn/submit)",
            )
        } else {
            (
                "editor · deos-zed (firmament over the cockpit's LOCAL World)",
                "a save = a cap-gated SetField turn → a real TurnReceipt (local ledger)",
            )
        };
        let editor_pane = framed(editor_title, editor_sub, editor_body);
        let terminal_pane = framed(
            "terminal · deos-terminal (live alacritty PTY)",
            "real cargo/git running INSIDE deos",
            terminal_body,
        );

        div()
            .key_context("UnifiedBoot")
            .track_focus(&self.focus)
            .flex()
            .flex_col()
            .size_full()
            .bg(theme::bg())
            .text_color(theme::text())
            .font_family("Menlo")
            .child(header)
            .child(
                div()
                    .flex()
                    .gap_3()
                    .flex_1()
                    .min_h(px(0.))
                    .w_full()
                    .p_3()
                    .child(node_pane)
                    .child(editor_pane)
                    .child(terminal_pane),
            )
    }
}

impl UnifiedBootView {
    /// Render the live-node pane body from the fetched snapshot + receipt.
    fn render_node_pane(&self) -> gpui::AnyElement {
        let mut col = div().flex().flex_col().gap_2().p_2().size_full();

        match &self.snapshot {
            Some(s) => {
                let st = &s.status;
                col = col.child(
                    div()
                        .flex()
                        .flex_wrap()
                        .gap_1()
                        .items_center()
                        .child(pill(
                            if st.healthy { "healthy" } else { "DOWN" },
                            if st.healthy { good() } else { theme::warn() },
                        ))
                        .child(pill(
                            &format!("producer {}", st.state_producer),
                            if st.lean_producer {
                                good()
                            } else {
                                theme::warn()
                            },
                        ))
                        .child(pill(&format!("h{}", st.latest_height), theme::accent()))
                        .child(pill(&format!("dag {}", st.dag_height), theme::muted()))
                        .child(pill(
                            &format!("{} effects", st.producer_root_agreeing_effects),
                            theme::muted(),
                        )),
                );
                col = col.child(div().text_xs().text_color(theme::muted()).child(format!(
                    "{} live cells · synced over /api/cells",
                    s.cell_views.len()
                )));
                for cv in s.cell_views.iter().take(4) {
                    col = col.child(inspectable_card(cv));
                }
            }
            None => {
                col = col.child(
                    div()
                        .text_color(theme::warn())
                        .child("(no node attached / unreachable)"),
                );
            }
        }

        if let Some(rv) = &self.receipt_view {
            col = col.child(
                div()
                    .mt_1()
                    .text_xs()
                    .text_color(theme::accent())
                    .child("LATEST NODE RECEIPT · /api/receipts"),
            );
            col = col.child(inspectable_card(rv));
        }

        col.into_any_element()
    }
}

/// Reflect a raw `/api/receipts` JSON node (the FULL receipt shape) into the
/// uniform [`Inspectable`] the live-node pane renders — the genuine on-node
/// provenance head, drawn straight from the node's own receipt record.
fn raw_receipt_inspectable(raw: &serde_json::Value) -> Inspectable {
    let s = |k: &str| {
        raw.get(k)
            .and_then(|v| v.as_str())
            .unwrap_or("")
            .to_string()
    };
    let n = |k: &str| raw.get(k).and_then(|v| v.as_u64()).unwrap_or(0);
    let b = |k: &str| raw.get(k).and_then(|v| v.as_bool()).unwrap_or(false);
    let receipt_hash = s("receipt_hash");
    let fields = vec![
        Field::text("receipt_hash", short(&receipt_hash)),
        Field::text("turn_hash", short(&s("turn_hash"))),
        Field::count("chain_index", n("chain_index")),
        Field::text("pre_state", short(&s("pre_state"))),
        Field::text("post_state", short(&s("post_state"))),
        Field::count("action_count", n("action_count")),
        Field::count("computrons_used", n("computrons_used")),
        Field::boolean("has_proof", b("has_proof")),
        Field::text("proof_status", s("proof_status")),
        Field::boolean("executor_signed", b("executor_signed")),
        Field::boolean("has_witness", b("has_witness")),
        Field::text("finality", s("finality")),
    ];
    Inspectable {
        kind: ObjectKind::Receipt,
        title: format!("Receipt {}", short(&receipt_hash)),
        subtitle: format!(
            "node · #{} · {} actions · {} computrons",
            n("chain_index"),
            n("action_count"),
            n("computrons_used")
        ),
        fields,
    }
}

/// The proof a client-signed editor save produced on the node: the receipt count
/// grew AND the committed turn's agent is the USER's own cell (not the operator's).
#[cfg(feature = "embedded-executor")]
#[derive(Debug, Clone)]
pub struct ClientSignedProof {
    /// Node `/api/receipts` count before the submit.
    pub before: usize,
    /// Node `/api/receipts` count after (must be `before + 1`).
    pub after: usize,
    /// The logged-in user's own default cell (hex) — the turn's agent.
    pub user_cell: String,
    /// The node OPERATOR's own default cell (hex) — what the agent must NOT be.
    pub operator_cell: String,
    /// The agent of the just-committed receipt, read off the chain head (hex). For
    /// the proof to hold this must equal `user_cell` and differ from `operator_cell`.
    pub receipt_agent: String,
    /// The signer the node reported (hex pubkey) — the user's key, not the node's.
    pub signer: String,
    /// The committed turn hash.
    pub turn_hash: String,
}

#[cfg(feature = "embedded-executor")]
impl ClientSignedProof {
    /// The load-bearing check: the receipt grew by one AND its agent is the user's
    /// own cell, NOT the operator's. This is "a sovereign client signed a turn the
    /// node committed under the client's authority".
    pub fn proves_user_authority(&self) -> bool {
        self.after == self.before + 1
            && self.receipt_agent == self.user_cell
            && self.receipt_agent != self.operator_cell
    }
}

/// Decode a 64-char hex string into a 32-byte array, or `None` if malformed.
#[cfg(feature = "embedded-executor")]
fn decode_hex32(s: &str) -> Option<[u8; 32]> {
    let bytes = hex::decode(s.trim()).ok()?;
    if bytes.len() != 32 {
        return None;
    }
    let mut out = [0u8; 32];
    out.copy_from_slice(&bytes);
    Some(out)
}

/// Encode a save's content fingerprint into a 32-byte field element (a short
/// hex/decimal scalar little-endian into the low 8 bytes; a full 64-char hex used
/// verbatim) — the SAME convention the node's `parse_field_element` decodes.
#[cfg(feature = "embedded-executor")]
fn field_element_from(s: &str) -> [u8; 32] {
    let t = s.trim();
    if t.len() == 64 && t.bytes().all(|b| b.is_ascii_hexdigit()) {
        if let Some(b) = decode_hex32(t) {
            return b;
        }
    }
    let scalar: u64 = t
        .strip_prefix("0x")
        .and_then(|h| u64::from_str_radix(h, 16).ok())
        .or_else(|| t.parse::<u64>().ok())
        .unwrap_or(0);
    let mut out = [0u8; 32];
    out[..8].copy_from_slice(&scalar.to_le_bytes());
    out
}

/// First 8 + last 4 hex chars of a long id, for compact display.
fn short(hex: &str) -> String {
    if hex.len() <= 16 {
        hex.to_string()
    } else {
        format!("{}…{}", &hex[..8], &hex[hex.len() - 4..])
    }
}

/// A self-contained card for a reflected node object (status/cell/receipt) — the
/// uniform [`Inspectable`] shape, rendered without reaching into the cockpit's
/// `pub(crate)` helpers.
fn inspectable_card(ins: &Inspectable) -> impl IntoElement {
    let mut card = div()
        .flex()
        .flex_col()
        .gap_0p5()
        .px_2()
        .py_1()
        .rounded_md()
        .bg(theme::panel_hi())
        .border_1()
        .border_color(theme::border())
        .child(
            div()
                .text_xs()
                .text_color(theme::text())
                .child(ins.title.clone()),
        )
        .child(
            div()
                .text_xs()
                .text_color(theme::muted())
                .child(ins.subtitle.clone()),
        );
    for f in ins.fields.iter().take(6) {
        let (val, color) = field_display(&f.value);
        card = card.child(
            div()
                .flex()
                .justify_between()
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child(f.key.clone()),
                )
                .child(div().text_xs().text_color(color).child(val)),
        );
    }
    card
}

fn field_display(v: &FieldValue) -> (String, gpui::Hsla) {
    match v {
        FieldValue::Text(s) => (s.clone(), theme::text()),
        FieldValue::Balance(b) => (
            b.to_string(),
            if *b < 0 { theme::warn() } else { theme::text() },
        ),
        FieldValue::Count(c) => (c.to_string(), theme::text()),
        FieldValue::Bool(b) => (b.to_string(), if *b { good() } else { theme::muted() }),
        FieldValue::Id(id) => (crate::reflect::short_hex(id), theme::accent()),
        FieldValue::Hash(h) => (crate::reflect::short_hex(h), good()),
        FieldValue::CapEdge { target, slot } => (
            format!("→ {} (slot {slot})", crate::reflect::short_hex(target)),
            theme::accent(),
        ),
        FieldValue::FieldSlot { hex, .. } => {
            (crate::reflect::short_hex_hexstr(hex), theme::muted())
        }
    }
}

/// Mount the unified-boot view as a root view for the headless capture.
pub fn build_root(
    world: Rc<RefCell<World>>,
    node_url: Option<String>,
    terminal_cmd: Option<(String, Vec<String>)>,
    window: &mut Window,
    cx: &mut App,
) -> anyhow::Result<Entity<UnifiedBootView>> {
    build_root_with_user(world, node_url, None, terminal_cmd, window, cx)
}

/// Mount the unified-boot view, threading the logged-in user's signing seed so the
/// editor pane's OWN save routes a client-signed turn to the live node (the
/// interactive self-hosting wire). See [`UnifiedBootView::build_with_user`].
pub fn build_root_with_user(
    world: Rc<RefCell<World>>,
    node_url: Option<String>,
    user_seed: Option<[u8; 64]>,
    terminal_cmd: Option<(String, Vec<String>)>,
    window: &mut Window,
    cx: &mut App,
) -> anyhow::Result<Entity<UnifiedBootView>> {
    let view = cx.new(|cx| {
        UnifiedBootView::build_with_user(world, node_url, user_seed, terminal_cmd, window, cx)
            .expect("unified-boot view mount")
    });
    view.update(cx, |v, cx| {
        let focus = v.focus.clone();
        focus.focus(window, cx);
    });
    Ok(view)
}

fn badge(text: &str, color: gpui::Hsla) -> impl IntoElement {
    div()
        .px_2()
        .py_1()
        .rounded_md()
        .bg(theme::panel_hi())
        .border_1()
        .border_color(theme::border())
        .text_color(color)
        .text_xs()
        .child(text.to_string())
}

fn pill(text: &str, color: gpui::Hsla) -> impl IntoElement {
    div()
        .px_1p5()
        .py_0p5()
        .rounded_md()
        .bg(theme::panel())
        .border_1()
        .border_color(theme::border())
        .text_color(color)
        .text_xs()
        .child(text.to_string())
}

fn framed(title: &str, subtitle: &str, body: gpui::AnyElement) -> impl IntoElement {
    div()
        .flex()
        .flex_col()
        .flex_1()
        .min_w(px(0.))
        .h_full()
        .rounded_md()
        .border_1()
        .border_color(theme::border())
        .bg(theme::panel())
        .child(
            div()
                .flex()
                .flex_col()
                .gap_0p5()
                .px_3()
                .py_2()
                .border_b_1()
                .border_color(theme::border())
                .child(div().text_color(theme::text()).child(title.to_string()))
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child(subtitle.to_string()),
                ),
        )
        .child(div().flex_1().min_h(px(0.)).overflow_hidden().child(body))
}
