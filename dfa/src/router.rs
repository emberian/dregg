//! Routing surface: `RouteTarget`, `RouteTable`, `Router`, `GovernedRouter`,
//! and the userspace kind registry.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use serde::{Deserialize, Serialize};

use crate::compiler::{DEAD_STATE, Dfa, Pattern, StateId};

// ---------------------------------------------------------------------------
// RouteTarget
// ---------------------------------------------------------------------------

/// Where a classified message should be dispatched.
///
/// `Userspace` is the open variant: starbridge-apps register a `kind` string
/// in a [`KindRegistry`] at startup and stash app-defined payloads (typically
/// a `bincode` / `postcard` blob encoding their own destination type) under
/// that kind. The registry exists so that a constitutionally bound route
/// table can be audited end-to-end ("does every userspace kind appear in
/// the registry?") without losing destination flexibility.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RouteTarget {
    /// Deliver to a named handler within the local process. The semantic
    /// meaning of the name is up to the dispatcher (e.g. `"cell:abcd"`,
    /// `"intent_pool"`, `"admin"`).
    Handler(String),
    /// Forward to another reference group / federation.
    Federation { group_id: [u8; 32] },
    /// Silently discard (capability revoked, blocked topic, etc.).
    Drop,
    /// Userspace-defined destination. `kind` is a registered identifier
    /// (see [`KindRegistry`]); `payload` is opaque to the router and
    /// decoded by the dispatcher's `kind` handler.
    Userspace(UserspaceTarget),
}

/// The payload-bearing form of `RouteTarget::Userspace`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct UserspaceTarget {
    pub kind: String,
    pub payload: Vec<u8>,
}

impl RouteTarget {
    pub fn handler(name: impl Into<String>) -> Self {
        RouteTarget::Handler(name.into())
    }

    pub fn federation(group_id: [u8; 32]) -> Self {
        RouteTarget::Federation { group_id }
    }

    pub fn drop() -> Self {
        RouteTarget::Drop
    }

    pub fn userspace(kind: impl Into<String>, payload: impl Into<Vec<u8>>) -> Self {
        RouteTarget::Userspace(UserspaceTarget {
            kind: kind.into(),
            payload: payload.into(),
        })
    }
}

// ---------------------------------------------------------------------------
// Kind registry
// ---------------------------------------------------------------------------

/// A registry of `RouteTarget::Userspace { kind: ... }` identifiers that an
/// app is allowed to use. Validation rejects any route table referencing
/// a kind that isn't registered.
///
/// This is the audit hook for the open `Userspace` variant: a federation's
/// constitution can declare which kinds it understands, and any installed
/// route table is validated against that declaration before commitment-binding.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct KindRegistry {
    kinds: BTreeSet<String>,
}

impl KindRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn register(&mut self, kind: impl Into<String>) {
        self.kinds.insert(kind.into());
    }

    pub fn contains(&self, kind: &str) -> bool {
        self.kinds.contains(kind)
    }

    pub fn kinds(&self) -> impl Iterator<Item = &str> {
        self.kinds.iter().map(|s| s.as_str())
    }

    /// Validate that every `RouteTarget::Userspace` in the table references a
    /// registered kind. Returns the offending unknown kinds (if any).
    pub fn validate_table(&self, table: &RouteTable) -> Result<(), Vec<String>> {
        let mut bad: BTreeSet<String> = BTreeSet::new();
        for tgt in table.accept_map.values() {
            if let RouteTarget::Userspace(u) = tgt {
                if !self.contains(&u.kind) {
                    bad.insert(u.kind.clone());
                }
            }
        }
        if bad.is_empty() {
            Ok(())
        } else {
            Err(bad.into_iter().collect())
        }
    }
}

// ---------------------------------------------------------------------------
// RouteTable
// ---------------------------------------------------------------------------

/// A compiled route table: DFA + accept-map keyed by `StateId` (`u32`).
///
/// The transition table is laid out as `[state * 256 + byte] -> next_state`.
/// State 0 is the dead state; the start state is always 1.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RouteTable {
    /// BLAKE3 commitment of the canonical serialization (transitions ‖
    /// accept-map ‖ prefix-lens). This is what's bound into a federation
    /// constitution.
    pub commitment: [u8; 32],
    /// Number of states (including the dead state).
    pub num_states: u32,
    /// Flat transition table.
    pub transitions: Vec<StateId>,
    /// Maps accepting state IDs to their route targets.
    pub accept_map: BTreeMap<StateId, RouteTarget>,
    /// For URL-style routes, the declared-prefix byte length per accepting
    /// state. `Classification::matched_prefix` honors this entry when set,
    /// otherwise falls back to the longest-match span the DFA consumed.
    #[serde(default)]
    pub prefix_lens: BTreeMap<StateId, usize>,
    /// Start state (always 1 for freshly compiled tables).
    pub start: StateId,
}

impl RouteTable {
    /// Build a `RouteTable` from a [`Dfa`] and an explicit accept-map.
    /// The accept-map's keys must be a subset of `dfa.accepting`; any
    /// non-accepting state in the map is ignored.
    pub fn from_dfa(dfa: Dfa, accept_map: BTreeMap<StateId, RouteTarget>) -> Self {
        let prefix_lens = BTreeMap::new();
        let commitment = compute_commitment(&dfa.transitions, &accept_map, &prefix_lens);
        RouteTable {
            commitment,
            num_states: dfa.num_states,
            transitions: dfa.transitions,
            accept_map,
            prefix_lens,
            start: dfa.start,
        }
    }

    /// Recompute the commitment (useful after manual mutation).
    pub fn recompute_commitment(&mut self) {
        self.commitment =
            compute_commitment(&self.transitions, &self.accept_map, &self.prefix_lens);
    }
}

fn compute_commitment(
    transitions: &[StateId],
    accept_map: &BTreeMap<StateId, RouteTarget>,
    prefix_lens: &BTreeMap<StateId, usize>,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-dfa-route-table-v1");
    for t in transitions {
        hasher.update(&t.to_le_bytes());
    }
    let encoded =
        postcard::to_allocvec(accept_map).expect("RouteTarget postcard encoding cannot fail");
    hasher.update(&(encoded.len() as u64).to_le_bytes());
    hasher.update(&encoded);
    let plens = postcard::to_allocvec(prefix_lens).expect("prefix_lens encoding cannot fail");
    hasher.update(&(plens.len() as u64).to_le_bytes());
    hasher.update(&plens);
    *hasher.finalize().as_bytes()
}

// ---------------------------------------------------------------------------
// RouteTable builder
// ---------------------------------------------------------------------------

/// Convenience builder for assembling a [`RouteTable`] out of `(Pattern, RouteTarget)`
/// pairs.
///
/// Each route compiles to its own DFA; the builder unions them and tags each
/// path's accepting state with the corresponding target. Patterns are kept in
/// insertion order; on overlap, the first-added pattern wins for the matched
/// state (note: union-determinization places the disjuncts' accepts on a
/// common state, so distinct overlaps require the patterns to be disjoint —
/// the builder routes them to per-pattern accept tags via product
/// construction).
pub struct RouteTableBuilder {
    /// Compiled per-route components. Each component DFA accepts only on its
    /// designated boundary (literal end for exact routes, prefix end for
    /// `prefix/*` routes); the keep-alive role for `prefix/*` is built into
    /// the same DFA by using `prefix_of(literal)` as the transition skeleton
    /// while restricting `accepting` to the boundary state.
    items: Vec<RouteItem>,
}

#[derive(Clone, Debug)]
struct RouteItem {
    /// Component DFA whose `accepting` is the singleton boundary state (or
    /// however the user-supplied pattern accepts, for `route_pattern`).
    dfa: Dfa,
    /// The target to attribute when this component accepts.
    target: RouteTarget,
    /// If this is a URL-style route, the byte length of the declared prefix
    /// (the literal piece, excluding the `*`). Used to populate
    /// [`Classification::matched_prefix`] / `remainder`.
    declared_prefix_len: Option<usize>,
}

impl RouteTableBuilder {
    pub fn new() -> Self {
        Self { items: Vec::new() }
    }

    /// Add a URL-style path route. The pattern language is intentionally
    /// minimal:
    ///
    /// - `"/cells/stablecoin/*"` matches `/cells/stablecoin/` followed by
    ///   anything. The declared prefix (`/cells/stablecoin/`) is the bytes
    ///   that will be reported as `matched_prefix`; whatever follows is the
    ///   `remainder`.
    /// - `"/health"` is an exact-match literal route.
    /// - For richer patterns (alternation, byte ranges, intersection), use
    ///   [`RouteTableBuilder::route_pattern`].
    pub fn route(mut self, pattern: &str, target: RouteTarget) -> Self {
        let (literal_bytes, is_prefix) = parse_url_style(pattern);
        let dfa = if is_prefix {
            // For "/prefix/*": compile `prefix_of(literal)` so the DFA stays
            // alive past the boundary (allowing deeper sibling routes to
            // match), but restrict `accepting` to the state at the boundary
            // so the route fires exactly once.
            let mut dfa = Pattern::prefix_of(Pattern::word(literal_bytes)).compile();
            let boundary = dfa.run(literal_bytes);
            let mut acc = BTreeSet::new();
            if boundary != DEAD_STATE {
                acc.insert(boundary);
            }
            dfa.accepting = acc;
            dfa
        } else {
            Pattern::word(literal_bytes).compile()
        };
        self.items.push(RouteItem {
            dfa,
            target,
            declared_prefix_len: Some(literal_bytes.len()),
        });
        self
    }

    /// Add a route specified by an explicit [`Pattern`].
    ///
    /// The pattern's accept set is honored as-is: the matched prefix in the
    /// resulting [`Classification`] will be the entire span the DFA consumed
    /// before fixing on its longest accept (longest-match semantics).
    pub fn route_pattern(mut self, pattern: Pattern, target: RouteTarget) -> Self {
        let dfa = pattern.compile();
        self.items.push(RouteItem {
            dfa,
            target,
            declared_prefix_len: None,
        });
        self
    }

    /// Finalize the builder into a [`RouteTable`].
    ///
    /// Strategy: we build a single combined DFA whose accepting states are
    /// tagged with the target index, via union-with-tagging. Concretely we
    /// produce a fresh DFA whose state IDs partition by which input pattern
    /// matched (longest match wins on overlap, matching order wins on ties).
    pub fn compile(self) -> RouteTable {
        // Combine via a sequential per-pattern product: build a master DFA
        // tracking which pattern matched. Simpler: run each DFA in parallel
        // at runtime via cross-product. That blows up state. Instead, we
        // build one combined DFA where every state remembers a winning
        // pattern index.
        //
        // We compute the cross-product of all patterns iteratively. At each
        // composite state, the winning pattern is the earliest-added pattern
        // whose component DFA is in an accepting state.
        if self.items.is_empty() {
            // Empty table — accept nothing.
            let dfa = Dfa {
                num_states: 1,
                transitions: vec![DEAD_STATE; 256],
                start: 0,
                accepting: BTreeSet::new(),
            };
            return RouteTable::from_dfa(dfa, BTreeMap::new());
        }

        let (combined_dfa, accept_map, prefix_lens) = compose_tagged_union(&self.items);
        let mut table = RouteTable::from_dfa(combined_dfa, accept_map);
        table.prefix_lens = prefix_lens;
        table
    }
}

impl Default for RouteTableBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// Parse a URL-style route string. Returns `(literal_bytes, is_prefix)`.
/// A trailing `*` (with or without a preceding `/`) marks a prefix route;
/// the literal part is everything before the `*`.
fn parse_url_style(s: &str) -> (&[u8], bool) {
    let bytes = s.as_bytes();
    if !bytes.is_empty() && bytes[bytes.len() - 1] == b'*' {
        (&bytes[..bytes.len() - 1], true)
    } else {
        (bytes, false)
    }
}

/// Build a combined DFA from per-route components.
///
/// Composite state = tuple of component-DFA states. Composite accepts when at
/// least one component is in its accept set; the accept tag is the component
/// with the longest declared prefix (the longest-match winner) and on tie,
/// the earliest-added.
fn compose_tagged_union(
    items: &[RouteItem],
) -> (
    Dfa,
    BTreeMap<StateId, RouteTarget>,
    BTreeMap<StateId, usize>,
) {
    use std::collections::VecDeque;

    let n = items.len();
    let mut state_map: BTreeMap<Vec<StateId>, StateId> = BTreeMap::new();
    let mut transitions: Vec<StateId> = Vec::new();
    let mut accept_map: BTreeMap<StateId, RouteTarget> = BTreeMap::new();
    let mut prefix_lens: BTreeMap<StateId, usize> = BTreeMap::new();
    let mut accepting: BTreeSet<StateId> = BTreeSet::new();

    let dead_key: Vec<StateId> = vec![DEAD_STATE; n];
    state_map.insert(dead_key.clone(), DEAD_STATE);
    transitions.extend(std::iter::repeat(DEAD_STATE).take(256));

    let start_key: Vec<StateId> = items.iter().map(|r| r.dfa.start).collect();
    let start_id: StateId = 1;
    state_map.insert(start_key.clone(), start_id);
    transitions.extend(std::iter::repeat(DEAD_STATE).take(256));
    if let Some(idx) = winning_component(items, &start_key) {
        accepting.insert(start_id);
        accept_map.insert(start_id, items[idx].target.clone());
        if let Some(len) = items[idx].declared_prefix_len {
            prefix_lens.insert(start_id, len);
        }
    }

    let mut worklist: VecDeque<Vec<StateId>> = VecDeque::new();
    worklist.push_back(start_key);
    let mut next_id: StateId = 2;

    while let Some(key) = worklist.pop_front() {
        let cur_id = state_map[&key];
        for byte in 0u16..=255u16 {
            let b = byte as u8;
            let next_key: Vec<StateId> = key
                .iter()
                .enumerate()
                .map(|(i, &s)| {
                    if s == DEAD_STATE {
                        DEAD_STATE
                    } else {
                        items[i].dfa.transitions[(s as usize) * 256 + (b as usize)]
                    }
                })
                .collect();

            if next_key.iter().all(|&s| s == DEAD_STATE) {
                transitions[(cur_id as usize) * 256 + (b as usize)] = DEAD_STATE;
                continue;
            }

            let target_id = if let Some(&existing) = state_map.get(&next_key) {
                existing
            } else {
                let id = next_id;
                next_id += 1;
                state_map.insert(next_key.clone(), id);
                transitions.extend(std::iter::repeat(DEAD_STATE).take(256));
                if let Some(idx) = winning_component(items, &next_key) {
                    accepting.insert(id);
                    accept_map.insert(id, items[idx].target.clone());
                    if let Some(len) = items[idx].declared_prefix_len {
                        prefix_lens.insert(id, len);
                    }
                }
                worklist.push_back(next_key);
                id
            };
            transitions[(cur_id as usize) * 256 + (b as usize)] = target_id;
        }
    }

    (
        Dfa {
            num_states: next_id,
            transitions,
            start: start_id,
            accepting,
        },
        accept_map,
        prefix_lens,
    )
}

/// Pick the winning component at a composite state.
///
/// Selection rule: among accepting components, prefer the one with the
/// longest declared prefix length. On ties (or both unspecified), the
/// earliest-added route wins. This gives URL-style routes the
/// longest-prefix-match behavior consumers expect.
fn winning_component(items: &[RouteItem], key: &[StateId]) -> Option<usize> {
    let mut best: Option<(usize, isize)> = None;
    for (i, (item, &s)) in items.iter().zip(key.iter()).enumerate() {
        if s == DEAD_STATE || !item.dfa.accepting.contains(&s) {
            continue;
        }
        let len = item.declared_prefix_len.map(|l| l as isize).unwrap_or(-1);
        match best {
            None => best = Some((i, len)),
            Some((_, prev_len)) if len > prev_len => best = Some((i, len)),
            _ => {}
        }
    }
    best.map(|(i, _)| i)
}

// ---------------------------------------------------------------------------
// Router (live dispatch)
// ---------------------------------------------------------------------------

/// Classification result: which target matched, and where the match landed
/// (matched prefix + remainder).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Classification<'a> {
    pub target: &'a RouteTarget,
    pub matched_prefix: &'a [u8],
    pub remainder: &'a [u8],
}

/// The live router.
#[derive(Clone, Debug)]
pub struct Router {
    table: RouteTable,
}

impl Router {
    pub fn new(table: RouteTable) -> Self {
        Router { table }
    }

    /// Classify a raw message; returns the route target whose pattern accepts.
    /// Uses **longest-match** semantics: the deepest position where the DFA
    /// landed on an accepting state wins.
    pub fn classify<'a>(&'a self, message: &'a [u8]) -> Option<Classification<'a>> {
        self.classify_inner(message)
    }

    /// Classify a URL-style path. Identical to `classify` — kept as a named
    /// alias for caller clarity.
    pub fn classify_path<'a>(&'a self, path: &'a [u8]) -> Option<Classification<'a>> {
        self.classify_inner(path)
    }

    fn classify_inner<'a>(&'a self, input: &'a [u8]) -> Option<Classification<'a>> {
        // Walk the DFA, recording the *deepest* (last visited) accept state
        // along with the byte index at which it was reached.
        let mut state: StateId = self.table.start;
        let mut last_accept: Option<(StateId, usize)> = None;
        if self.table.accept_map.contains_key(&state) {
            last_accept = Some((state, 0));
        }
        for (i, &byte) in input.iter().enumerate() {
            let idx = (state as usize) * 256 + (byte as usize);
            if idx >= self.table.transitions.len() {
                break;
            }
            let next = self.table.transitions[idx];
            if next == DEAD_STATE {
                break;
            }
            state = next;
            if self.table.accept_map.contains_key(&state) {
                last_accept = Some((state, i + 1));
            }
        }
        let (accept_state, walked_len) = last_accept?;
        let target = self.table.accept_map.get(&accept_state)?;
        // For URL-style routes the declared prefix length governs the
        // matched_prefix / remainder split. For pattern routes we fall back
        // to the longest-accept walk length.
        let prefix_len = self
            .table
            .prefix_lens
            .get(&accept_state)
            .copied()
            .unwrap_or(walked_len)
            .min(input.len());
        Some(Classification {
            target,
            matched_prefix: &input[..prefix_len],
            remainder: &input[prefix_len..],
        })
    }

    /// Reconstruct the underlying DFA (for AIR trace generation or
    /// inspection). The DFA's `accepting` set equals the route table's
    /// `accept_map` keys.
    pub fn as_dfa(&self) -> Dfa {
        Dfa {
            num_states: self.table.num_states,
            transitions: self.table.transitions.clone(),
            start: self.table.start,
            accepting: self.table.accept_map.keys().copied().collect(),
        }
    }

    pub fn table(&self) -> &RouteTable {
        &self.table
    }

    pub fn commitment(&self) -> &[u8; 32] {
        &self.table.commitment
    }
}

// ---------------------------------------------------------------------------
// Dispatch decision (typed wrapper for callers that don't want to match the
// `RouteTarget` enum at every site)
// ---------------------------------------------------------------------------

/// Higher-level dispatch result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DispatchDecision {
    Handler(String),
    Federation([u8; 32]),
    Userspace(UserspaceTarget),
    Drop,
    Unrouted,
}

impl DispatchDecision {
    pub fn from_target(t: Option<&RouteTarget>) -> Self {
        match t {
            Some(RouteTarget::Handler(s)) => DispatchDecision::Handler(s.clone()),
            Some(RouteTarget::Federation { group_id }) => DispatchDecision::Federation(*group_id),
            Some(RouteTarget::Userspace(u)) => DispatchDecision::Userspace(u.clone()),
            Some(RouteTarget::Drop) => DispatchDecision::Drop,
            None => DispatchDecision::Unrouted,
        }
    }
}

// ---------------------------------------------------------------------------
// Governance
// ---------------------------------------------------------------------------

/// A threshold-signature verifier abstracted over the concrete federation
/// scheme. The DFA crate is dependency-light, so we accept any verifier
/// implementing this trait. The default [`StubVerifier`] only checks the
/// commitment-CAS — it's the seam Lane M's federation unification fills in.
pub trait ThresholdVerifier: Send + Sync {
    /// Verify that `proof_data` is a valid threshold signature over the
    /// message `commitment_pair = old_commitment ‖ new_commitment`.
    fn verify(
        &self,
        old_commitment: &[u8; 32],
        new_commitment: &[u8; 32],
        proof_data: &[u8],
    ) -> Result<(), String>;
}

/// Stub verifier that accepts any non-empty `proof_data` and rejects an empty
/// one. The accompanying commitment-CAS in [`GovernedRouter::update_routes`]
/// is the load-bearing safety net while a real verifier is wired in.
///
/// In production, replace this with a wrapper around
/// `federation::FederationCommittee::verify` (`hints` BLS aggregate
/// signature) or whatever Lane M's federation unification settles on.
#[derive(Clone, Debug, Default)]
pub struct StubVerifier;

impl ThresholdVerifier for StubVerifier {
    fn verify(&self, _old: &[u8; 32], _new: &[u8; 32], proof_data: &[u8]) -> Result<(), String> {
        if proof_data.is_empty() {
            Err("empty proof_data (StubVerifier rejects empty proofs)".to_string())
        } else {
            Ok(())
        }
    }
}

/// A governance proof bundling the threshold signature with the CAS hint.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct GovernanceProof {
    pub expected_old_commitment: [u8; 32],
    /// Threshold-signature bytes over `old_commitment ‖ new_commitment`. The
    /// concrete format is whatever the [`ThresholdVerifier`] understands.
    pub proof_data: Vec<u8>,
}

/// A router that enforces governance on table swaps.
///
/// The CAS check (commitment must match) is local and always enforced.
/// The cryptographic check is delegated to a [`ThresholdVerifier`] supplied
/// at construction time.
pub struct GovernedRouter {
    current: Router,
    commitment: [u8; 32],
    registry: KindRegistry,
    verifier: Arc<dyn ThresholdVerifier>,
}

impl std::fmt::Debug for GovernedRouter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GovernedRouter")
            .field("commitment", &hex_short(&self.commitment))
            .field("registry", &self.registry)
            .field("current", &self.current)
            .finish()
    }
}

fn hex_short(b: &[u8; 32]) -> String {
    let mut s = String::new();
    for byte in &b[..4] {
        s.push_str(&format!("{byte:02x}"));
    }
    s.push_str("…");
    s
}

impl Clone for GovernedRouter {
    fn clone(&self) -> Self {
        GovernedRouter {
            current: self.current.clone(),
            commitment: self.commitment,
            registry: self.registry.clone(),
            verifier: self.verifier.clone(),
        }
    }
}

impl GovernedRouter {
    /// Build a `GovernedRouter` with the default `StubVerifier`. Suitable for
    /// in-process apps and tests; production deployments should use
    /// [`GovernedRouter::with_verifier`].
    pub fn new(table: RouteTable) -> Self {
        let commitment = table.commitment;
        GovernedRouter {
            current: Router::new(table),
            commitment,
            registry: KindRegistry::new(),
            verifier: Arc::new(StubVerifier),
        }
    }

    /// Build a `GovernedRouter` with a caller-supplied threshold verifier.
    pub fn with_verifier(table: RouteTable, verifier: Arc<dyn ThresholdVerifier>) -> Self {
        let commitment = table.commitment;
        GovernedRouter {
            current: Router::new(table),
            commitment,
            registry: KindRegistry::new(),
            verifier,
        }
    }

    /// Replace the registered userspace-kind set.
    pub fn set_kind_registry(&mut self, registry: KindRegistry) {
        self.registry = registry;
    }

    pub fn kind_registry(&self) -> &KindRegistry {
        &self.registry
    }

    pub fn commitment(&self) -> &[u8; 32] {
        &self.commitment
    }

    pub fn classify_path<'a>(&'a self, path: &'a [u8]) -> Option<Classification<'a>> {
        self.current.classify_path(path)
    }

    pub fn classify<'a>(&'a self, message: &'a [u8]) -> Option<Classification<'a>> {
        self.current.classify(message)
    }

    pub fn router(&self) -> &Router {
        &self.current
    }

    /// Atomically replace the route table.
    ///
    /// Performs three checks in order:
    ///   1. **CAS**: `proof.expected_old_commitment` must equal the current commitment.
    ///   2. **Threshold verification**: `verifier.verify(old, new, proof_data)` must succeed.
    ///   3. **Kind validation**: every `RouteTarget::Userspace.kind` in the new table
    ///      must appear in the kind registry.
    pub fn update_routes(
        &mut self,
        new_table: RouteTable,
        proof: &GovernanceProof,
    ) -> Result<(), RouteUpdateError> {
        if proof.expected_old_commitment != self.commitment {
            return Err(RouteUpdateError::CommitmentMismatch {
                expected: proof.expected_old_commitment,
                actual: self.commitment,
            });
        }
        if let Err(msg) =
            self.verifier
                .verify(&self.commitment, &new_table.commitment, &proof.proof_data)
        {
            return Err(RouteUpdateError::ThresholdVerificationFailed(msg));
        }
        if let Err(unknown) = self.registry.validate_table(&new_table) {
            return Err(RouteUpdateError::UnknownUserspaceKinds(unknown));
        }
        self.commitment = new_table.commitment;
        self.current = Router::new(new_table);
        Ok(())
    }
}

/// Errors from [`GovernedRouter::update_routes`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RouteUpdateError {
    CommitmentMismatch {
        expected: [u8; 32],
        actual: [u8; 32],
    },
    ThresholdVerificationFailed(String),
    UnknownUserspaceKinds(Vec<String>),
}

impl std::fmt::Display for RouteUpdateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RouteUpdateError::CommitmentMismatch { expected, actual } => {
                write!(
                    f,
                    "commitment mismatch: expected {}, got {}",
                    hex_short(expected),
                    hex_short(actual)
                )
            }
            RouteUpdateError::ThresholdVerificationFailed(msg) => {
                write!(f, "threshold verification failed: {msg}")
            }
            RouteUpdateError::UnknownUserspaceKinds(kinds) => {
                write!(f, "unknown userspace kinds: {kinds:?}")
            }
        }
    }
}

impl std::error::Error for RouteUpdateError {}

// ---------------------------------------------------------------------------
// `Dfa` ergonomic builder entry point
// ---------------------------------------------------------------------------

impl Dfa {
    /// Start building a `RouteTable`. Equivalent to `RouteTableBuilder::new()`,
    /// re-exported here for the documented userspace ergonomics.
    pub fn builder() -> RouteTableBuilder {
        RouteTableBuilder::new()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn group(b: u8) -> [u8; 32] {
        [b; 32]
    }

    #[test]
    fn five_line_userspace_example() {
        // This is the canonical starbridge-app authoring example.
        let table = Dfa::builder()
            .route("/health", RouteTarget::handler("health_check"))
            .route(
                "/cells/stablecoin/*",
                RouteTarget::handler("cell:stablecoin"),
            )
            .route("/blocked/*", RouteTarget::Drop)
            .compile();
        let router = GovernedRouter::new(table);

        let c = router.classify_path(b"/health").unwrap();
        assert_eq!(c.target, &RouteTarget::handler("health_check"));
        assert_eq!(c.matched_prefix, b"/health");
        assert_eq!(c.remainder, b"");

        let c = router.classify_path(b"/cells/stablecoin/transfer").unwrap();
        assert_eq!(c.target, &RouteTarget::handler("cell:stablecoin"));
        assert_eq!(c.remainder, b"transfer");

        let c = router.classify_path(b"/blocked/anything").unwrap();
        assert_eq!(c.target, &RouteTarget::Drop);
    }

    #[test]
    fn commitment_deterministic_and_sensitive() {
        let t1 = Dfa::builder()
            .route("/x/*", RouteTarget::handler("x"))
            .compile();
        let t2 = Dfa::builder()
            .route("/x/*", RouteTarget::handler("x"))
            .compile();
        assert_eq!(t1.commitment, t2.commitment);

        let t3 = Dfa::builder()
            .route("/x/*", RouteTarget::handler("y"))
            .compile();
        assert_ne!(t1.commitment, t3.commitment);
    }

    #[test]
    fn governed_update_requires_cas() {
        let t1 = Dfa::builder()
            .route("/a/*", RouteTarget::handler("a1"))
            .compile();
        let mut governed = GovernedRouter::new(t1.clone());

        let t2 = Dfa::builder()
            .route("/a/*", RouteTarget::handler("a2"))
            .compile();

        // Wrong commitment → reject.
        let bad = GovernanceProof {
            expected_old_commitment: [0xFF; 32],
            proof_data: vec![1],
        };
        assert!(matches!(
            governed.update_routes(t2.clone(), &bad),
            Err(RouteUpdateError::CommitmentMismatch { .. })
        ));

        // Empty proof_data → StubVerifier rejects.
        let empty_proof = GovernanceProof {
            expected_old_commitment: t1.commitment,
            proof_data: vec![],
        };
        assert!(matches!(
            governed.update_routes(t2.clone(), &empty_proof),
            Err(RouteUpdateError::ThresholdVerificationFailed(_))
        ));

        // Right commitment + non-empty proof → accept (StubVerifier).
        let good = GovernanceProof {
            expected_old_commitment: t1.commitment,
            proof_data: vec![1, 2, 3],
        };
        governed.update_routes(t2, &good).unwrap();

        let c = governed.classify_path(b"/a/x").unwrap();
        assert_eq!(c.target, &RouteTarget::handler("a2"));
    }

    #[test]
    fn unknown_userspace_kind_rejected() {
        let t1 = Dfa::builder()
            .route("/x/*", RouteTarget::handler("noop"))
            .compile();
        let mut governed = GovernedRouter::new(t1.clone());

        // Register only "alpha".
        let mut reg = KindRegistry::new();
        reg.register("alpha");
        governed.set_kind_registry(reg);

        // New table references both "alpha" (ok) and "beta" (unknown).
        let t2 = Dfa::builder()
            .route("/a/*", RouteTarget::userspace("alpha", b"".to_vec()))
            .route("/b/*", RouteTarget::userspace("beta", b"".to_vec()))
            .compile();

        let proof = GovernanceProof {
            expected_old_commitment: t1.commitment,
            proof_data: vec![1],
        };

        match governed.update_routes(t2, &proof) {
            Err(RouteUpdateError::UnknownUserspaceKinds(k)) => {
                assert_eq!(k, vec!["beta".to_string()]);
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn longest_match_wins() {
        // "/a" and "/abc" — input "/abcd" should resolve via the prefix tag
        // that consumed the most bytes. With `route("/abc", ...)` + `route("/a", ...)`,
        // "/abc" should win for "/abcd".
        let table = Dfa::builder()
            .route_pattern(Pattern::word(b"/abc"), RouteTarget::handler("longer"))
            .route_pattern(Pattern::word(b"/a"), RouteTarget::handler("shorter"))
            .compile();
        let router = Router::new(table);

        // "/abc" exact: should match the longer route.
        let c = router.classify_path(b"/abc").unwrap();
        assert_eq!(c.target, &RouteTarget::handler("longer"));
        // "/a" exact: only the shorter route accepts.
        let c = router.classify_path(b"/a").unwrap();
        assert_eq!(c.target, &RouteTarget::handler("shorter"));
        // "/ab" — only "/a" prefix accepts at byte 1 (depth 2).
        // (No accept for "/ab".)
        let c = router.classify_path(b"/ab");
        assert!(c.is_some());
        assert_eq!(c.unwrap().target, &RouteTarget::handler("shorter"));
    }

    #[test]
    fn federation_route_carries_group_id() {
        let table = Dfa::builder()
            .route("/federated/*", RouteTarget::federation(group(7)))
            .compile();
        let router = Router::new(table);
        let c = router.classify_path(b"/federated/sync").unwrap();
        assert_eq!(c.target, &RouteTarget::federation(group(7)));
    }

    #[test]
    fn many_routes_stress_passes_u8_cap() {
        // The old `wire::dfa_router` capped at 255 live states. Build 80
        // disjoint routes to blow well past it.
        let mut b = RouteTableBuilder::new();
        for i in 0..80 {
            b = b.route(
                &format!("/svc/handler_{i:03}/*"),
                RouteTarget::handler(format!("h{i}")),
            );
        }
        let table = b.compile();
        assert!(table.num_states > 256, "states={}", table.num_states);
        let router = Router::new(table);
        for i in 0..80 {
            let p = format!("/svc/handler_{i:03}/action");
            let c = router.classify_path(p.as_bytes()).unwrap();
            assert_eq!(c.target, &RouteTarget::handler(format!("h{i}")));
        }
    }
}
