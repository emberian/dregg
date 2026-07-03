//! **THE REAL, CAP-SCOPED CONSOLE** — the live read surface behind "My Dregg Computer",
//! narrowed to exactly the viewer's own cells by a REAL dregg-auth caveat chain (not a
//! string compare, not a fixture allow-list).
//!
//! [`crate::console`] holds the dashboard view-models ([`VatView`], [`HermesView`], the
//! `ConsoleModel` → [`ViewNode`](crate::tree::ViewNode) builder) and a convenience
//! [`ConsoleModel::scoped_to`] that filters by plain string equality. THIS module supplies
//! the two pieces that make the console the *signed-in* front door rather than a demo
//! render:
//!
//! 1. **A [`Catalog`] source trait** — the seam onto the REAL read surfaces of the World.
//!    An implementation reads OUR cells (the vat cells behind `dregg-cell`'s committed
//!    heaps, the resident-hermes cells, the $DREGG balance/spend cells) and yields the
//!    cloud-wide, multi-tenant resource set. The console NEVER serves that raw; it narrows
//!    it to one subject. There is deliberately NO bespoke HTTP server here — the console is
//!    a portable [`ViewNode`] card, and the catalog is a trait a live World reader fills,
//!    not a socket.
//!
//! 2. **The cap-scope ([`CapScope`])** — the capability gate, expressed in the proven
//!    dregg-auth credential algebra ([`dregg_auth::credential`]). The viewer presents a
//!    credential whose caveat chain names their **subject**; a resource owned by `owner` is
//!    in the view *iff* the credential VERIFIES against a context binding `subject = owner`
//!    (the real [`Credential::verify`] — the ed25519 signature chain plus the fail-closed
//!    caveat meet). Because the check is `AttrEq { subject } == owner`, the admitted set is
//!    exactly `{ owner : owner == viewer-subject }`: you see a cell iff its owner-cap
//!    subject is you. Amplification is inexpressible (attenuation only narrows), and a
//!    context that fails to bind the subject admits NOTHING — fail-closed, so a wiring bug
//!    can never leak a stranger's cell.
//!
//! [`ConsoleModel::from_catalog`] assembles the two: read the multi-tenant catalog, keep
//! only the rows the [`CapScope`] admits, recompute the spend total from the survivors,
//! and read the viewer's own $DREGG balance. The result feeds the SAME
//! [`console_card`](crate::console::console_card) the native gpui renderer, the web
//! renderer, and the phone all walk — so the cap-scoped card runs everywhere the IR does.
//!
//! ## The write path is gated by the same chain
//!
//! A row's action is not a bare turn — it lowers to a [`CapTurn`]: the firing affordance
//! (`turn` + `arg`) bound to the owning subject whose capability must admit it. The
//! console can only *act* on a cell the viewer owns, checked by the identical caveat-chain
//! gate that scoped the *read* ([`CapTurn::admitted`]). Read-scope and write-gate are one
//! authority, not two.
//!
//! (Provenance, for the ledger — kept out of the card, out of the code: the aggregation +
//! cap-scoping shape here was ported from a prior imperative console module and re-anchored
//! on our cells and the [`dregg_auth`] credential core; there is no dependency on, and no
//! weld back to, that prototype.)

use std::collections::BTreeMap;

use dregg_auth::credential::{Caveat, Context, Credential, Pred, PublicKey, RootKey};

use crate::console::{ConsoleModel, HermesView, LedgerView, SpendLine, VatView};
use crate::tree::MenuItem;

/// The request-attribute key a resource's **owner-subject** binds under in the cap
/// [`Context`], and the key the viewer's scoping caveat constrains. One name, used by both
/// sides of the check, so the read-scope and the write-gate are the SAME predicate.
pub const SUBJECT_ATTR: &str = "subject";

// ─────────────────────────────────────────────────────────────────────────────
// THE CATALOG SOURCE — the seam onto the REAL read surfaces (our cells)
// ─────────────────────────────────────────────────────────────────────────────

/// **The cloud-wide read surface.** An implementation aggregates the live World's resource
/// cells across ALL tenants — the console then narrows the result to exactly the signed-in
/// subject ([`ConsoleModel::from_catalog`]). Each row carries its owner-cap subject
/// (`VatView::owner` / `HermesView::owner` / `SpendLine::owner`), which is the only fact the
/// cap-scope reads; a row whose owner cannot be established must simply be absent (an
/// un-ownable row can never be scoped, so surfacing it would risk a cross-tenant leak —
/// fail closed at the source).
///
/// This is a trait, not a socket: a live reader implements it over OUR cells (the vat
/// cells, the resident-hermes cells, the $DREGG balance/spend cells); [`SnapshotCatalog`]
/// implements it over an already-read in-memory snapshot (the shape a reader fills, and the
/// shape the tests exercise). Object-safe — the console holds a `&dyn Catalog`.
pub trait Catalog {
    /// Every Dregg Computer (vat cell) the surface exposes, across all tenants.
    fn computers(&self) -> Vec<VatView>;
    /// Every resident hermes cell, across all tenants.
    fn hermeses(&self) -> Vec<HermesView>;
    /// Every $DREGG spend line, across all tenants.
    fn spend(&self) -> Vec<SpendLine>;
    /// The $DREGG balance recorded for `subject` (0 when the surface has none — a balance
    /// is read for the VIEWER only, never enumerated across tenants).
    fn balance(&self, subject: &str) -> u64;
    /// When this snapshot was read (RFC3339) — the card's honest data-age line.
    fn generated_at(&self) -> String;
}

/// An in-memory [`Catalog`] over an already-read multi-tenant snapshot — the exact shape a
/// live World reader fills (owner-tagged vat/hermes views, spend lines, per-subject
/// balances). The tests drive the cap-scope over this; a production reader produces the
/// same value type from the committed cell heaps.
#[derive(Debug, Clone, Default)]
pub struct SnapshotCatalog {
    /// Every vat cell, across all tenants (each tagged with its owner-cap subject).
    pub computers: Vec<VatView>,
    /// Every resident hermes cell, across all tenants.
    pub hermeses: Vec<HermesView>,
    /// Every $DREGG spend line, across all tenants.
    pub spend: Vec<SpendLine>,
    /// Per-subject $DREGG balances (the console reads only the viewer's).
    pub balances: BTreeMap<String, u64>,
    /// The snapshot's read time (RFC3339).
    pub generated_at: String,
}

impl Catalog for SnapshotCatalog {
    fn computers(&self) -> Vec<VatView> {
        self.computers.clone()
    }
    fn hermeses(&self) -> Vec<HermesView> {
        self.hermeses.clone()
    }
    fn spend(&self) -> Vec<SpendLine> {
        self.spend.clone()
    }
    fn balance(&self, subject: &str) -> u64 {
        self.balances.get(subject).copied().unwrap_or(0)
    }
    fn generated_at(&self) -> String {
        self.generated_at.clone()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE CAP-SCOPE — the caveat-chain subject gate (dregg-auth Context/Pred)
// ─────────────────────────────────────────────────────────────────────────────

/// Mint a viewer credential whose caveat chain **is** `subject`: a single first-party
/// caveat requiring `subject == <subject>`. A resource owned by `owner` is admitted by this
/// credential iff a [`Context`] binding `subject = owner` satisfies the caveat — i.e. iff
/// `owner == subject`. This is the identity a signed-in viewer presents; a real deployment
/// mints it from the same [`RootKey`] the auth edge holds (and may attenuate it with a
/// temporal window — the cap-scope honours every caveat, see [`CapScope::admits`]).
pub fn subject_credential(root: &RootKey, subject: &str) -> Credential {
    root.mint([Caveat::FirstParty(Pred::AttrEq {
        key: SUBJECT_ATTR.to_string(),
        value: subject.to_string(),
    })])
}

/// **The capability scope a signed-in viewer presents.** It carries the viewer's credential
/// (the caveat chain naming their subject), the issuer [`PublicKey`] it verifies under, and
/// the monotone `clock` any temporal caveat reads. Everything the console shows or fires is
/// decided by [`CapScope::admits`] — one authority for both the read-scope and the
/// write-gate.
pub struct CapScope {
    root: PublicKey,
    cred: Credential,
    clock: u64,
}

impl CapScope {
    /// Present a credential to scope by, verified under `root`, with the `clock` temporal
    /// caveats read against.
    pub fn new(root: PublicKey, cred: Credential, clock: u64) -> Self {
        CapScope { root, cred, clock }
    }

    /// The convenience path for the common case: mint a subject-only credential from `root`
    /// and scope by it. Real deployments present an already-minted, possibly-attenuated
    /// credential via [`CapScope::new`]; this is the "just scope me to my subject" shortcut
    /// the tests and simple front doors use.
    pub fn for_subject(root: &RootKey, subject: &str, clock: u64) -> Self {
        CapScope::new(root.public(), subject_credential(root, subject), clock)
    }

    /// The caveat-chain **subject** — the value of the credential's `subject`-equality
    /// caveat. DERIVED from the chain (never supplied alongside it), so it cannot drift from
    /// the identity the credential actually admits. `None` if the chain installs no subject
    /// caveat (a credential that scopes nothing by subject — the console then shows an empty
    /// view, since no owner can equal an absent subject).
    pub fn subject(&self) -> Option<String> {
        self.cred.caveats().find_map(|(_, c)| match c {
            Caveat::FirstParty(Pred::AttrEq { key, value }) if key.as_str() == SUBJECT_ATTR => {
                Some(value.clone())
            }
            _ => None,
        })
    }

    /// **The scoping decision.** A resource owned by `owner` is in scope iff the viewer's
    /// credential VERIFIES against a context binding `subject = owner`: the full
    /// [`Credential::verify`] — the ed25519 signature chain AND the fail-closed caveat meet
    /// (so a temporal window that has closed, or any other caveat, closes the view too).
    /// Fail-closed: a refusal — including the context failing to bind the subject — is
    /// `false`, never a leak.
    pub fn admits(&self, owner: &str) -> bool {
        let ctx = Context::new().at(self.clock).attr(SUBJECT_ATTR, owner);
        self.cred.verify(&self.root, &ctx).is_ok()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// ASSEMBLE — the cloud-wide catalog, narrowed to the viewer's own cells
// ─────────────────────────────────────────────────────────────────────────────

impl ConsoleModel {
    /// **Assemble the cap-scoped console model** from a live [`Catalog`] and the viewer's
    /// [`CapScope`]: keep only the computers / hermeses / spend lines the scope admits,
    /// recompute `total_spent` from the surviving lines (never trust a pre-aggregated total
    /// across a scope cut), and read the viewer's own $DREGG balance. The teeth: nothing
    /// another subject owns can appear, because [`CapScope::admits`] is a real credential
    /// verify against each row's owner. Feed the result to
    /// [`console_card`](crate::console::console_card) to paint it on any renderer.
    ///
    /// The viewer's subject is taken from the caveat chain ([`CapScope::subject`]); an
    /// absent subject yields an empty view (no owner equals nothing) rather than a wide one.
    pub fn from_catalog(catalog: &dyn Catalog, scope: &CapScope) -> ConsoleModel {
        let subject = scope.subject().unwrap_or_default();

        let computers: Vec<VatView> = catalog
            .computers()
            .into_iter()
            .filter(|v| scope.admits(&v.owner))
            .collect();
        let hermeses: Vec<HermesView> = catalog
            .hermeses()
            .into_iter()
            .filter(|h| scope.admits(&h.owner))
            .collect();
        let entries: Vec<SpendLine> = catalog
            .spend()
            .into_iter()
            .filter(|e| scope.admits(&e.owner))
            .collect();
        let total_spent = entries.iter().map(|e| e.units).sum();

        ConsoleModel {
            subject: subject.clone(),
            generated_at: catalog.generated_at(),
            computers,
            hermeses,
            dregg: LedgerView {
                balance: catalog.balance(&subject),
                subject,
                total_spent,
                entries,
            },
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE WRITE PATH — a row action lowered to a cap-gated verified turn
// ─────────────────────────────────────────────────────────────────────────────

/// **A row's action, lowered to a cap-gated verified turn.** A dashboard row (a vat's
/// wake/sleep/fork/verify, a hermes' step/resume, …) fires an affordance `{turn, arg}`; on
/// the write path that affordance is gated by the OWNING subject's capability. A [`CapTurn`]
/// binds the two: the turn to fire, and the subject whose [`CapScope`] must admit it. The
/// console can act on a cell only when the viewer owns it — the SAME caveat-chain check that
/// scoped the read ([`CapTurn::admitted`]), now on the write.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CapTurn {
    /// The affordance to fire (a [`crate::console`] turn name, e.g. `vat.sleep`).
    pub turn: String,
    /// The affordance argument (the row's index in its list — the executor's dispatch key).
    pub arg: i64,
    /// The owner-cap subject that gates this turn: it fires only if the viewer's scope
    /// admits `subject`.
    pub subject: String,
}

impl CapTurn {
    /// Lower a row's `(owner, turn, arg)` to its cap-gated turn.
    pub fn new(owner: impl Into<String>, turn: impl Into<String>, arg: i64) -> Self {
        CapTurn {
            turn: turn.into(),
            arg,
            subject: owner.into(),
        }
    }

    /// Lower a rendered [`MenuItem`] (a card row's action) to its cap-gated turn, bound to
    /// the row's `owner`. The menu's `enabled` flag is the LIFECYCLE tooth (wake only a
    /// sleeper); [`CapTurn::admitted`] is the orthogonal OWNERSHIP tooth — both must open for
    /// the turn to fire.
    pub fn from_menu(owner: impl Into<String>, item: &MenuItem) -> Self {
        CapTurn {
            turn: item.turn.clone(),
            arg: item.arg,
            subject: owner.into(),
        }
    }

    /// Is this turn admitted for `scope`? The write-side capability gate: the viewer's
    /// caveat chain must admit the owning subject (you can only act on your own cell).
    pub fn admitted(&self, scope: &CapScope) -> bool {
        scope.admits(&self.subject)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE DEMO CATALOG — the multi-tenant snapshot the cap-scope is exercised over
// ─────────────────────────────────────────────────────────────────────────────

/// A deterministic multi-tenant [`SnapshotCatalog`], sourced from
/// [`demo_console`](crate::console::demo_console) so the read surfaces carry BOTH the demo
/// subject's cells and a second tenant's — the cap-scope is exercised non-vacuously (the
/// stranger's rows MUST be filtered out). Balances are recorded per subject so the viewer's
/// own $DREGG is read and the stranger's is never leaked.
pub fn demo_catalog() -> SnapshotCatalog {
    let all = crate::console::demo_console();
    let mut balances = BTreeMap::new();
    balances.insert(crate::console::DEMO_SUBJECT.to_string(), all.dregg.balance);
    balances.insert(crate::console::OTHER_SUBJECT.to_string(), 12_000);
    SnapshotCatalog {
        computers: all.computers,
        hermeses: all.hermeses,
        spend: all.dregg.entries,
        balances,
        generated_at: all.generated_at,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// TESTS — the cap-scope narrows to exactly the viewer's cells (no leak), and a
// row action lowers to a cap-gated turn admitted only under the owner's chain.
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::console::{
        console_bind_values, console_card, DEMO_SUBJECT, OTHER_SUBJECT, TURN_VAT_SLEEP,
        TURN_VAT_WAKE,
    };
    use crate::tree::ViewNode;

    /// Pre-order walk (matches the renderers' + bind cursor's order).
    fn walk<'a>(n: &'a ViewNode, f: &mut impl FnMut(&'a ViewNode)) {
        f(n);
        match n {
            ViewNode::VStack(cs) | ViewNode::Row(cs) | ViewNode::List(cs) | ViewNode::Table(cs) => {
                cs.iter().for_each(|c| walk(c, f))
            }
            ViewNode::Section { children, .. } | ViewNode::Grid { children, .. } => {
                children.iter().for_each(|c| walk(c, f))
            }
            ViewNode::Tabs { panels, .. } => panels.iter().for_each(|c| walk(c, f)),
            ViewNode::Host { view: Some(v), .. } => walk(v, f),
            ViewNode::Adept(inner) => walk(inner, f),
            _ => {}
        }
    }

    fn root() -> RootKey {
        // Deterministic seed — the golden-vector discipline (no OS randomness in tests).
        RootKey::from_seed([7u8; 32])
    }

    // ── THE CATALOG SHOWS EXACTLY THE SUBJECT'S OWNED CELLS (no cross-tenant leak) ──
    #[test]
    fn catalog_shows_exactly_the_subjects_own_cells() {
        let root = root();
        let cat = demo_catalog();
        // The read surface is genuinely multi-tenant (scoping must not be vacuous).
        assert!(cat.computers.iter().any(|v| v.owner == OTHER_SUBJECT));
        assert!(cat.hermeses.iter().any(|h| h.owner == OTHER_SUBJECT));
        assert!(cat.spend.iter().any(|e| e.owner == OTHER_SUBJECT));

        let scope = CapScope::for_subject(&root, DEMO_SUBJECT, 1_000);
        assert_eq!(scope.subject().as_deref(), Some(DEMO_SUBJECT));

        let model = ConsoleModel::from_catalog(&cat, &scope);
        assert_eq!(model.subject, DEMO_SUBJECT);
        // Exactly the demo subject's cells survive — the fixture has two vats + one hermes.
        assert_eq!(model.computers.len(), 2, "the demo subject's two computers");
        assert_eq!(model.hermeses.len(), 1, "the demo subject's one hermes");
        assert!(model.computers.iter().all(|v| v.owner == DEMO_SUBJECT));
        assert!(model.hermeses.iter().all(|h| h.owner == DEMO_SUBJECT));
        assert!(model.dregg.entries.iter().all(|e| e.owner == DEMO_SUBJECT));
        // The viewer's own balance is read; the foreign 900-unit spend line is gone from
        // the TOTAL, not just the list (10+10+10+2).
        assert_eq!(model.dregg.balance, 9_968);
        assert_eq!(model.dregg.total_spent, 32);
        // NOTHING the other tenant owns leaks — not into the model, not onto the card.
        assert!(!model.computers.iter().any(|v| v.name == "other-srv"));
        assert!(!model.hermeses.iter().any(|h| h.name == "other-bot"));
        let card = console_card(&model);
        let mut text = String::new();
        walk(&card, &mut |n| {
            if let ViewNode::Text(t) = n {
                text.push_str(t);
            }
        });
        assert!(
            !text.contains("other-srv") && !text.contains("other-bot"),
            "no foreign resource name reaches the cap-scoped card"
        );
        // The card still lives: its pre-order binds match the snapshot contract.
        let binds = console_bind_values(&model);
        let mut n_binds: usize = 0;
        walk(&card, &mut |n| {
            if matches!(n, ViewNode::Bind { .. }) {
                n_binds += 1;
            }
        });
        assert_eq!(n_binds, binds.len(), "each Bind has one snapshot value");
    }

    // ── THE OTHER PRINCIPAL'S VIEW IS DISJOINT (the cut cuts both ways) ─────────────
    #[test]
    fn a_different_principal_sees_only_theirs() {
        let root = root();
        let cat = demo_catalog();
        let scope = CapScope::for_subject(&root, OTHER_SUBJECT, 1_000);
        let model = ConsoleModel::from_catalog(&cat, &scope);
        assert_eq!(model.subject, OTHER_SUBJECT);
        assert_eq!(model.computers.len(), 1);
        assert!(model.computers.iter().all(|v| v.owner == OTHER_SUBJECT));
        // The demo subject's cells never leak into the stranger's view.
        assert!(!model.computers.iter().any(|v| v.name == "mybox"));
        assert!(!model.computers.iter().any(|v| v.name == "scratchpad"));
        assert_eq!(model.dregg.balance, 12_000);
        // Direct on the gate: the demo subject's credential admits its subject, refuses the
        // other — fail-closed both ways.
        let demo = CapScope::for_subject(&root, DEMO_SUBJECT, 1_000);
        assert!(demo.admits(DEMO_SUBJECT));
        assert!(!demo.admits(OTHER_SUBJECT));
    }

    // ── FAIL-CLOSED: an unrelated caveat chain (wrong subject) admits nothing ───────
    #[test]
    fn the_scope_is_fail_closed() {
        let root = root();
        let cat = demo_catalog();
        // A viewer whose subject owns nothing in the catalog sees an empty view.
        let stranger = CapScope::for_subject(&root, "dregg:0000000000000000", 1_000);
        let model = ConsoleModel::from_catalog(&cat, &stranger);
        assert!(model.computers.is_empty());
        assert!(model.hermeses.is_empty());
        assert!(model.dregg.entries.is_empty());
        assert_eq!(model.dregg.balance, 0, "a foreign balance is never read");
        assert_eq!(model.dregg.total_spent, 0);
    }

    // ── THE CHAIN, NOT A STRING COMPARE: an expired cap closes the whole view ───────
    #[test]
    fn an_expired_cap_admits_nothing_even_its_own_owner() {
        let root = root();
        // A credential caveated to the demo subject AND to a temporal deadline.
        let cred = root.mint([
            Caveat::FirstParty(Pred::AttrEq {
                key: SUBJECT_ATTR.to_string(),
                value: DEMO_SUBJECT.to_string(),
            }),
            Caveat::FirstParty(Pred::NotAfter { at: 1_000 }),
        ]);
        // Inside the window: the owner's cells are admitted.
        let live = CapScope::new(root.public(), cred, 900);
        assert!(live.admits(DEMO_SUBJECT));
        // Past the deadline the SAME chain refuses — a plain string compare never would.
        // (A fresh credential of the same shape, since verify consumes only &self but the
        // scope owns it.)
        let cred2 = root.mint([
            Caveat::FirstParty(Pred::AttrEq {
                key: SUBJECT_ATTR.to_string(),
                value: DEMO_SUBJECT.to_string(),
            }),
            Caveat::FirstParty(Pred::NotAfter { at: 1_000 }),
        ]);
        let expired = CapScope::new(root.public(), cred2, 2_000);
        assert!(
            !expired.admits(DEMO_SUBJECT),
            "the temporal caveat closed the view"
        );
        let model = ConsoleModel::from_catalog(&demo_catalog(), &expired);
        assert!(model.computers.is_empty(), "an expired cap shows nothing");
    }

    // ── A ROW ACTION LOWERS TO A CAP-GATED TURN (admitted only under the owner) ─────
    #[test]
    fn a_row_action_lowers_to_a_cap_gated_turn() {
        let root = root();
        let cat = demo_catalog();
        let scope = CapScope::for_subject(&root, DEMO_SUBJECT, 1_000);
        let model = ConsoleModel::from_catalog(&cat, &scope);

        // The first computer is the running `mybox`, owned by the demo subject.
        let vat = &model.computers[0];
        assert_eq!(vat.owner, DEMO_SUBJECT);

        // Pull the REAL rendered row action (the vat's sleep menu item) off the card and
        // lower it — this is the row's affordance, not a synthetic one.
        let card = console_card(&model);
        let mut sleep_item: Option<MenuItem> = None;
        walk(&card, &mut |n| {
            if let ViewNode::Menu { items } = n {
                if items.iter().any(|i| i.turn == TURN_VAT_WAKE) {
                    // A vat menu (recognised by its wake verb); grab its sleep row once.
                    if sleep_item.is_none() {
                        sleep_item = items.iter().find(|i| i.turn == TURN_VAT_SLEEP).cloned();
                    }
                }
            }
        });
        let item = sleep_item.expect("the running vat's menu carries a sleep row");
        let turn = CapTurn::from_menu(&vat.owner, &item);
        assert_eq!(turn.turn, TURN_VAT_SLEEP);
        assert_eq!(turn.arg, item.arg);
        assert_eq!(turn.subject, DEMO_SUBJECT);

        // THE CAP GATE: the owner's scope admits the turn; a different principal's does NOT
        // (you can only act on a cell you own — the same caveat chain that scoped the read).
        assert!(turn.admitted(&scope), "the owner may fire the turn");
        let stranger = CapScope::for_subject(&root, OTHER_SUBJECT, 1_000);
        assert!(
            !turn.admitted(&stranger),
            "a stranger's cap cannot fire a turn on someone else's cell"
        );

        // And the ergonomic constructor lowers the same way (owner + turn + row index).
        let direct = CapTurn::new(vat.owner.clone(), TURN_VAT_SLEEP, 0);
        assert!(direct.admitted(&scope));
        assert!(!direct.admitted(&stranger));
    }
}
