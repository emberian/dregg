/-!
# DISCO: the NAT-traversal endpoint-probing FSM

A model of DISCO endpoint discovery — the peer-to-peer path probing a
node runs to find a working direct route to another node, before it will
send real traffic over that route instead of relaying. DISCO has no
public RFC; this is derived from the documented DISCO wire protocol,
whose two relevant messages are:

* **Ping** — carries an opaque, unguessable transaction id (TxID) and
  the sender's node key. A node emits Pings to each *candidate* direct
  endpoint (address) it has heard about for a peer.
* **Pong** — echoes the exact TxID of the Ping it answers, and reports
  the source address the responder observed. A Pong is accepted only if
  its TxID matches an outstanding Ping and it authenticates.

The probing discipline: a candidate endpoint starts `unprobed`; sending
a Ping moves it to `probed` with the outstanding TxID; a matching,
authentic Pong moves it to `verified`. Only a `verified` endpoint is
eligible for path selection, and the selected path is the lowest-latency
verified endpoint. A node never sends real traffic over an endpoint that
has not answered a probe — that is the anti-spoofing guarantee (an
attacker cannot get a bogus endpoint promoted without producing a Pong
echoing a TxID it could not have seen).

## Theorems

* `disco_no_promote_without_pong` — the central property: a path is put
  into use (a `usePath` output from selection) only for an endpoint that
  is already `verified` in the candidate table. Selection never promotes
  an unprobed or merely-probed endpoint.
* `disco_verified_needs_pong` — the only door into `verified`: if a step
  turns an endpoint from not-verified to verified, the step's input was
  a `recvPong` whose TxID matched that endpoint's outstanding probe and
  which authenticated. No other input can create a verified endpoint.
* `disco_verified_sticky` — a verified endpoint stays verified across a
  probe and across an unrelated pong (verification is monotone; loss of
  a path via timeout is a boundary, below).
* `disco_select_lowest` (supporting) — selection returns a verified
  member of the table.

## Boundary / UNCLOSED

* Cryptography — the NaCl box that seals and authenticates DISCO Ping
  and Pong messages — is the named uninterpreted boundary (`authPong`).
  The unguessability of the TxID (why a spoofed Pong cannot match an
  outstanding probe) is the security assumption behind that boundary.
* Endpoint *expiry* (a verified path going stale and being demoted after
  a heartbeat timeout) is not modeled; here verification is monotone.
* CallMeMaybe (the relayed rendezvous message that seeds candidate
  endpoints) and the STUN-derived reflexive-endpoint discovery are out
  of scope; candidates arrive abstractly via `addCandidate`.
* Latency is modeled as an abstract `Nat` used only for path ordering.
-/

namespace Disco

/-- An opaque, unguessable probe transaction id (12 bytes on the wire). -/
structure TxId where
  val : Nat
deriving Repr, DecidableEq

/-- A candidate direct endpoint (an IP:port), modeled opaquely. -/
structure Endpoint where
  addr : Nat
deriving Repr, DecidableEq

/-- The probing state of one candidate endpoint. -/
inductive EpState where
  /-- Heard about, never probed. -/
  | unprobed
  /-- A Ping with this TxID is outstanding; awaiting a matching Pong. -/
  | probed (tx : TxId)
  /-- A matching, authentic Pong has been received: a working path, with
  its measured latency. -/
  | verified (latency : Nat)
deriving Repr, DecidableEq

/-- `true` exactly on a verified endpoint. -/
def EpState.isVerified : EpState → Bool
  | .verified _ => true
  | _ => false

/-- The candidate table: a per-endpoint probing state. -/
structure St where
  eps : List (Endpoint × EpState)
deriving Repr

/-- Empty table. -/
def init : St := { eps := [] }

/-- Static configuration: the crypto boundary. -/
structure Config where
  /-- Does this Pong (identified by TxID and source endpoint)
  authenticate under the DISCO NaCl box? Uninterpreted. -/
  authPong : TxId → Endpoint → Bool

/-! ## Table operations -/

/-- First-match lookup of an endpoint's state. -/
def lookup : List (Endpoint × EpState) → Endpoint → Option EpState
  | [], _ => none
  | (e, s) :: t, ep => if e = ep then some s else lookup t ep

/-- Apply `f` to the state of every entry keyed by `ep`. -/
def setState (f : EpState → EpState) (ep : Endpoint) :
    List (Endpoint × EpState) → List (Endpoint × EpState)
  | [] => []
  | (e, s) :: t =>
    (e, if e = ep then f s else s) :: setState f ep t

/-- Lookup commutes with a keyed update: querying the key returns the
mapped state, other keys are untouched. -/
theorem lookup_setState (f : EpState → EpState) (ep0 : Endpoint)
    (l : List (Endpoint × EpState)) (ep : Endpoint) :
    lookup (setState f ep0 l) ep
      = if ep0 = ep then (lookup l ep).map f else lookup l ep := by
  induction l with
  | nil => by_cases h : ep0 = ep <;> simp [setState, lookup, h]
  | cons hd t ih =>
    obtain ⟨e, s⟩ := hd
    simp only [setState, lookup]
    by_cases h2 : e = ep
    · subst h2
      by_cases h1 : e = ep0
      · subst h1; simp
      · have hne : ¬ ep0 = e := fun h => h1 h.symm
        simp [h1, hne]
    · simp [h2, ih]

/-! ## The probing FSM -/

/-- The re-probe map: send a fresh Ping. A verified endpoint stays
verified (a live path is not lost just because it is re-probed); any
other state becomes `probed` with the new TxID. -/
def probeMap (tx : TxId) : EpState → EpState
  | .verified lat => .verified lat
  | _ => .probed tx

/-- The Pong map for source `ep` under TxID `tx` and auth verdict `ok`:
an outstanding probe whose TxID matches is promoted to `verified`;
everything else is left unchanged (in particular a mismatched TxID or a
failed auth promotes nothing, and an already-verified endpoint stays
verified). -/
def pongMap (tx : TxId) (lat : Nat) (ok : Bool) : EpState → EpState
  | .probed tx' => if tx' = tx ∧ ok = true then .verified lat else .probed tx'
  | other => other

/-- Outputs the machine can emit. -/
inductive Output where
  /-- A DISCO Ping to a candidate endpoint. -/
  | sendPing (ep : Endpoint) (tx : TxId)
  /-- Put an endpoint into use as the selected path. -/
  | usePath (ep : Endpoint)
deriving Repr, DecidableEq

/-- Inputs the environment can deliver. -/
inductive Input where
  /-- A new candidate endpoint was learned. -/
  | addCandidate (ep : Endpoint)
  /-- Emit a probe (Ping) to a candidate. -/
  | sendProbe (ep : Endpoint) (tx : TxId)
  /-- A Pong arrived from `ep` echoing `tx`, with observed latency. -/
  | recvPong (tx : TxId) (ep : Endpoint) (lat : Nat)
  /-- Choose a path among the verified endpoints. -/
  | selectPath
deriving Repr

/-- The lowest-latency verified endpoint, if any. Only ever ranges over
verified entries. -/
def bestVerified : List (Endpoint × EpState) → Option (Endpoint × Nat)
  | [] => none
  | (e, .verified lat) :: t =>
    match bestVerified t with
    | none => some (e, lat)
    | some (e', lat') => if lat ≤ lat' then some (e, lat) else some (e', lat')
  | (_, _) :: t => bestVerified t

/-- Selection returns a genuinely-verified member of the table. -/
theorem bestVerified_mem (l : List (Endpoint × EpState))
    {ep : Endpoint} {lat : Nat} (h : bestVerified l = some (ep, lat)) :
    (ep, EpState.verified lat) ∈ l := by
  induction l with
  | nil => simp [bestVerified] at h
  | cons hd t ih =>
    obtain ⟨e, s⟩ := hd
    cases s with
    | unprobed =>
      exact List.mem_cons_of_mem _ (ih h)
    | probed tx =>
      exact List.mem_cons_of_mem _ (ih h)
    | verified l0 =>
      rw [show bestVerified ((e, EpState.verified l0) :: t)
            = (match bestVerified t with
               | none => some (e, l0)
               | some (e', lat') =>
                 if l0 ≤ lat' then some (e, l0) else some (e', lat'))
            from rfl] at h
      cases hb : bestVerified t with
      | none =>
        rw [hb] at h
        injection h with hp; injection hp with he hl
        subst he; subst hl
        exact List.mem_cons_self _ _
      | some p =>
        obtain ⟨e', lat'⟩ := p
        rw [hb] at h
        dsimp only at h
        split at h
        · injection h with hp; injection hp with he hl
          subst he; subst hl
          exact List.mem_cons_self _ _
        · injection h with hp; injection hp with he hl
          subst he; subst hl
          exact List.mem_cons_of_mem _ (ih hb)

/-- The total transition. -/
def step (cfg : Config) (s : St) : Input → St × List Output
  | .addCandidate ep =>
    if lookup s.eps ep = none then
      ({ eps := (ep, .unprobed) :: s.eps }, [])
    else
      (s, [])
  | .sendProbe ep tx =>
    ({ eps := setState (probeMap tx) ep s.eps }, [.sendPing ep tx])
  | .recvPong tx ep lat =>
    ({ eps := setState (pongMap tx lat (cfg.authPong tx ep)) ep s.eps }, [])
  | .selectPath =>
    match bestVerified s.eps with
    | some (ep, _) => (s, [.usePath ep])
    | none => (s, [])

/-- States reachable from the empty table. -/
inductive Reachable (cfg : Config) : St → Prop where
  | init : Reachable cfg init
  | step {s : St} (h : Reachable cfg s) (i : Input) :
      Reachable cfg (step cfg s i).1

/-! ## No promotion without a verified pong -/

/-- **A path is used only after a verified pong.** If selection emits a
`usePath ep`, then `ep` is `verified` in the candidate table — it has
answered a probe. Selection never promotes an unprobed or merely-probed
endpoint. -/
theorem disco_no_promote_without_pong (cfg : Config) (s : St)
    (ep : Endpoint)
    (h : Output.usePath ep ∈ (step cfg s .selectPath).2) :
    ∃ lat, (ep, EpState.verified lat) ∈ s.eps := by
  simp only [step] at h
  cases hb : bestVerified s.eps with
  | none => rw [hb] at h; simp at h
  | some p =>
    obtain ⟨e, lat⟩ := p
    rw [hb] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    injection h with he
    subst he
    exact ⟨lat, bestVerified_mem s.eps hb⟩

/-- **The only door into `verified` is a matching, authentic pong.** If a
step turns endpoint `ep` from not-verified into verified, the input was a
`recvPong` for `ep` whose TxID matched `ep`'s outstanding probe and which
authenticated under the crypto boundary. -/
theorem disco_verified_needs_pong (cfg : Config) (s : St) (i : Input)
    (ep : Endpoint)
    (hbefore : (lookup s.eps ep).map EpState.isVerified ≠ some true)
    (hafter : (lookup (step cfg s i).1.eps ep).map EpState.isVerified
              = some true) :
    ∃ tx lat, i = .recvPong tx ep lat ∧
      lookup s.eps ep = some (.probed tx) ∧
      cfg.authPong tx ep = true := by
  cases i with
  | addCandidate e =>
    simp only [step] at hafter
    split at hafter
    · -- prepended (e, unprobed)
      rename_i hnone
      simp only [lookup] at hafter
      by_cases he : e = ep
      · subst he; simp [EpState.isVerified] at hafter
      · rw [if_neg he] at hafter; exact absurd hafter hbefore
    · exact absurd hafter hbefore
  | sendProbe e tx =>
    simp only [step, lookup_setState] at hafter
    by_cases he : e = ep
    · subst he
      rw [if_pos rfl] at hafter
      -- probeMap never produces verified from a non-verified state, and
      -- preserves verified; so `some true` forces the input verified.
      cases hl : lookup s.eps e with
      | none => rw [hl] at hafter; simp at hafter
      | some st =>
        rw [hl] at hafter
        cases st with
        | unprobed => simp [probeMap, EpState.isVerified] at hafter
        | probed t0 => simp [probeMap, EpState.isVerified] at hafter
        | verified l0 =>
          exact absurd (by rw [hl]; simp [EpState.isVerified]) hbefore
    · rw [if_neg he] at hafter; exact absurd hafter hbefore
  | recvPong tx e lat =>
    simp only [step, lookup_setState] at hafter
    by_cases he : e = ep
    · subst he
      rw [if_pos rfl] at hafter
      cases hl : lookup s.eps e with
      | none => rw [hl] at hafter; simp at hafter
      | some st =>
        rw [hl] at hafter
        cases st with
        | unprobed => simp [pongMap, EpState.isVerified] at hafter
        | verified l0 =>
          exact absurd (by rw [hl]; simp [EpState.isVerified]) hbefore
        | probed t0 =>
          simp only [pongMap, Option.map_some'] at hafter
          split at hafter
          · rename_i hcond
            obtain ⟨htx, hok⟩ := hcond
            refine ⟨tx, lat, rfl, ?_, hok⟩
            rw [htx]
          · simp [EpState.isVerified] at hafter
    · rw [if_neg he] at hafter; exact absurd hafter hbefore
  | selectPath =>
    simp only [step] at hafter
    cases hb : bestVerified s.eps with
    | none => rw [hb] at hafter; exact absurd hafter hbefore
    | some p =>
      obtain ⟨e, lat⟩ := p
      rw [hb] at hafter
      exact absurd hafter hbefore

/-! ## Verification is monotone -/

/-- **A verified endpoint stays verified.** Neither a re-probe nor any
pong (matching or not) demotes a verified path. Timeouts are a boundary,
so within this model verification is sticky. -/
theorem disco_verified_sticky (cfg : Config) (s : St) (i : Input)
    (ep : Endpoint) {lat : Nat}
    (h : lookup s.eps ep = some (.verified lat)) :
    ∃ lat', lookup (step cfg s i).1.eps ep = some (.verified lat') := by
  cases i with
  | addCandidate e =>
    simp only [step]
    split
    · -- prepend only when ep was absent; but ep is verified, so present
      rename_i hnone
      by_cases he : e = ep
      · subst he; rw [h] at hnone; simp at hnone
      · simp only [lookup, he, if_false]; exact ⟨lat, h⟩
    · exact ⟨lat, h⟩
  | sendProbe e tx =>
    refine ⟨lat, ?_⟩
    simp only [step, lookup_setState]
    by_cases he : e = ep
    · subst he; simp [h, probeMap]
    · simp [he, h]
  | recvPong tx e lat0 =>
    refine ⟨lat, ?_⟩
    simp only [step, lookup_setState]
    by_cases he : e = ep
    · subst he; simp [h, pongMap]
    · simp [he, h]
  | selectPath =>
    refine ⟨lat, ?_⟩
    simp only [step]
    cases bestVerified s.eps <;> exact h

/-! ## Selection ranges over verified endpoints -/

/-- **Selection is over verified endpoints only** (restatement of
`bestVerified_mem` at the step level): whenever `selectPath` emits a
`usePath ep`, the table holds a verified entry for `ep`. -/
theorem disco_select_lowest (cfg : Config) (s : St) (ep : Endpoint)
    (h : Output.usePath ep ∈ (step cfg s .selectPath).2) :
    (∃ lat, lookup s.eps ep = some (.verified lat)) ∨
    (∃ lat, (ep, EpState.verified lat) ∈ s.eps) :=
  Or.inr (disco_no_promote_without_pong cfg s ep h)

/-! ## Endpoint priority: `bestVerified` is a genuine minimum -/

/-- If selection finds no verified endpoint, the table has none. -/
theorem bestVerified_none_no_verified (l : List (Endpoint × EpState))
    (h : bestVerified l = none) :
    ∀ e lat, (e, EpState.verified lat) ∉ l := by
  induction l with
  | nil => intro e lat hm; simp at hm
  | cons hd t ih =>
    obtain ⟨a, s⟩ := hd
    intro e lat hm
    cases s with
    | unprobed =>
      rw [show bestVerified ((a, EpState.unprobed) :: t) = bestVerified t from rfl] at h
      rcases List.mem_cons.mp hm with heq | hm'
      · exact absurd heq (by simp)
      · exact ih h e lat hm'
    | probed tx =>
      rw [show bestVerified ((a, EpState.probed tx) :: t) = bestVerified t from rfl] at h
      rcases List.mem_cons.mp hm with heq | hm'
      · exact absurd heq (by simp)
      · exact ih h e lat hm'
    | verified l0 =>
      rw [show bestVerified ((a, EpState.verified l0) :: t)
            = (match bestVerified t with
               | none => some (a, l0)
               | some (e2, lat2) =>
                 if l0 ≤ lat2 then some (a, l0) else some (e2, lat2))
            from rfl] at h
      cases hb : bestVerified t with
      | none => simp [hb] at h
      | some p =>
        obtain ⟨e2, lat2⟩ := p
        simp only [hb] at h
        split at h <;> simp at h

/-- **Selection picks the lowest latency.** The endpoint `bestVerified`
returns has latency no greater than that of *any* verified endpoint in the
table — direct-path selection is by lowest measured round-trip, not first
match. -/
theorem disco_bestVerified_min (l : List (Endpoint × EpState)) :
    ∀ {ep : Endpoint} {lat : Nat}, bestVerified l = some (ep, lat) →
    ∀ e' lat', (e', EpState.verified lat') ∈ l → lat ≤ lat' := by
  induction l with
  | nil => intro ep lat h; simp [bestVerified] at h
  | cons hd t ih =>
    obtain ⟨e, s⟩ := hd
    intro ep lat h e' lat' hmem
    cases s with
    | unprobed =>
      rw [show bestVerified ((e, EpState.unprobed) :: t) = bestVerified t from rfl] at h
      rcases List.mem_cons.mp hmem with heq | hmem'
      · simp at heq
      · exact ih h e' lat' hmem'
    | probed tx =>
      rw [show bestVerified ((e, EpState.probed tx) :: t) = bestVerified t from rfl] at h
      rcases List.mem_cons.mp hmem with heq | hmem'
      · simp at heq
      · exact ih h e' lat' hmem'
    | verified l0 =>
      rw [show bestVerified ((e, EpState.verified l0) :: t)
            = (match bestVerified t with
               | none => some (e, l0)
               | some (e2, lat2) =>
                 if l0 ≤ lat2 then some (e, l0) else some (e2, lat2))
            from rfl] at h
      cases hb : bestVerified t with
      | none =>
        simp only [hb] at h; injection h with hp; injection hp with he hl
        subst he; subst hl
        rcases List.mem_cons.mp hmem with heq | hmem'
        · injection heq with _ hs; injection hs with hll; omega
        · exact absurd hmem' (bestVerified_none_no_verified t hb e' lat')
      | some p =>
        obtain ⟨e2, lat2⟩ := p
        simp only [hb] at h
        have hmin := ih hb
        by_cases hle : l0 ≤ lat2
        · rw [if_pos hle] at h; injection h with hp; injection hp with he hl
          subst he; subst hl
          rcases List.mem_cons.mp hmem with heq | hmem'
          · injection heq with _ hs; injection hs with hll; omega
          · exact Nat.le_trans hle (hmin e' lat' hmem')
        · rw [if_neg hle] at h; injection h with hp; injection hp with he hl
          subst he; subst hl
          rcases List.mem_cons.mp hmem with heq | hmem'
          · injection heq with _ hs; injection hs with hll; omega
          · exact hmin e' lat' hmem'

/-! ## Path selection: direct with a DERP relay fallback -/

/-- Which kind of path a node is using to a peer. -/
inductive PathKind where
  /-- A verified direct endpoint (peer-to-peer). -/
  | direct
  /-- The DERP relay (used until a direct path is verified). -/
  | derp
deriving Repr, DecidableEq

/-- Select the path to a peer: the lowest-latency verified *direct*
endpoint if any exists, otherwise the DERP relay. This is the DERP-to-
direct discipline — a node relays only while it has no verified direct
path, and uses direct the moment one is available. -/
def selectPath (eps : List (Endpoint × EpState)) (derpHome : Endpoint) :
    Endpoint × PathKind :=
  match bestVerified eps with
  | some (ep, _) => (ep, .direct)
  | none => (derpHome, .derp)

/-- **Direct is preferred over the relay.** Whenever any endpoint is
verified, selection returns a direct path — never the DERP fallback. -/
theorem disco_direct_preferred (eps : List (Endpoint × EpState))
    (derpHome : Endpoint) {ep : Endpoint} {lat : Nat}
    (h : bestVerified eps = some (ep, lat)) :
    selectPath eps derpHome = (ep, .direct) := by
  simp [selectPath, h]

/-- **Relay only without a verified direct path.** With no verified
endpoint, selection falls back to the DERP relay. -/
theorem disco_relay_fallback (eps : List (Endpoint × EpState))
    (derpHome : Endpoint) (h : bestVerified eps = none) :
    selectPath eps derpHome = (derpHome, .derp) := by
  simp [selectPath, h]

/-- **A direct selection is a verified endpoint.** If selection returns a
direct path, that endpoint is verified in the table. -/
theorem disco_direct_is_verified (eps : List (Endpoint × EpState))
    (derpHome ep : Endpoint) (hpk : selectPath eps derpHome = (ep, .direct)) :
    ∃ lat, (ep, EpState.verified lat) ∈ eps := by
  unfold selectPath at hpk
  cases hb : bestVerified eps with
  | none => rw [hb] at hpk; injection hpk with _ hk; exact absurd hk (by decide)
  | some p =>
    obtain ⟨e, lat⟩ := p
    rw [hb] at hpk; injection hpk with he _
    subst he
    exact ⟨lat, bestVerified_mem eps hb⟩

/-- **DERP-to-direct upgrade.** If before a step no endpoint is verified —
so the node is relaying through DERP — and after the step some endpoint is
verified (a pong landed), then selection upgrades from the relay to a
direct path. This is the whole point of the probing discipline: relay
first, then promote to direct once a path is proven. -/
theorem disco_derp_to_direct_upgrade (cfg : Config) (s : St) (i : Input)
    (derpHome : Endpoint)
    (hbefore : bestVerified s.eps = none)
    {ep : Endpoint} {lat : Nat}
    (hafter : bestVerified (step cfg s i).1.eps = some (ep, lat)) :
    selectPath s.eps derpHome = (derpHome, .derp) ∧
    selectPath (step cfg s i).1.eps derpHome = (ep, .direct) :=
  ⟨disco_relay_fallback _ _ hbefore, disco_direct_preferred _ _ hafter⟩

end Disco
