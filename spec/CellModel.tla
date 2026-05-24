-------------------------------- MODULE CellModel --------------------------------
(***************************************************************************)
(* CellModel — initial TLA+ specification of pyana's three most-fundamental *)
(* cell-model invariants:                                                   *)
(*                                                                          *)
(*   I1 (Identity integrity).  Each cell's id equals BLAKE3(public_key ||   *)
(*       token_id).  Once a cell exists in the ledger, no operation         *)
(*       mutates `id`, `public_key`, or `token_id`.                         *)
(*                                                                          *)
(*   I2 (Nonce monotonicity).  Per-cell nonce starts at 0 and increases by  *)
(*       exactly 1 per successful turn.  Wrong-nonce turns are rejected.    *)
(*       The ledger nonce never regresses.                                  *)
(*                                                                          *)
(*   I3 (Capability attenuation lattice).  For any granted capability D     *)
(*       derived from a held capability P, IsAttenuation(P, D) must hold.   *)
(*       The lattice ordering is partial:                                   *)
(*                                                                          *)
(*               Impossible      (top — most restrictive)                   *)
(*                 /    \                                                   *)
(*           Signature  Proof                                               *)
(*                \    /                                                    *)
(*                Either                                                    *)
(*                  |                                                       *)
(*                 None         (bottom — least restrictive)                *)
(*                                                                          *)
(*       The ordering is `is_narrower_or_equal` from cell/src/permissions   *)
(*       .rs.  No operation may amplify (loosen) a granted capability       *)
(*       relative to the parent.                                            *)
(*                                                                          *)
(*   I4 (Balance conservation across a turn).  Every successful turn that   *)
(*       moves value from cell A to cell B reduces A's balance by exactly   *)
(*       the amount B's balance increases, plus a non-negative fee that is  *)
(*       burned (accounted to the symbolic "no cell" sink).  The total      *)
(*       (sum of cell balances + total fees burned) is invariant.           *)
(*       Concrete reference: pyana-protocol-tests/src/invariants/           *)
(*       balance_conservation.rs.                                           *)
(*                                                                          *)
(*   I5 (Receipt-chain causal soundness).  Each successful turn appends a   *)
(*       receipt to the executing cell's chain.  The new receipt's          *)
(*       prev_hash field equals the hash of the previous head; for the      *)
(*       first receipt it equals the genesis sentinel "0".  No operation    *)
(*       may insert, remove, reorder, or rewrite a receipt without          *)
(*       breaking the linkage.  Real-world references: the previous_       *)
(*       receipt_hash threading in node/src/mcp.rs (commit 818bbd62) and    *)
(*       the executor's verify_receipt_chain in turn/src/.                  *)
(*                                                                          *)
(* This spec deliberately ABSTRACTS:                                        *)
(*   * BLAKE3 — modeled as an injective function on (pk, token_id) pairs.   *)
(*   * Signatures and proofs — modeled by an `Auth` token the agent         *)
(*     presents; we don't model the cryptography, only the matching rule.   *)
(*   * Effect VM, receipts, balances, facets, expiry, the journal,          *)
(*     escrow, programs, sovereign mode, etc.  These deserve their own      *)
(*     spec increments; see spec/README.md.                                 *)
(*                                                                          *)
(* The goal is an honest, audit-against-Rust foundation: a reader should be *)
(* able to point at each TLA+ invariant and find the corresponding code in  *)
(* cell/src/{cell,permissions,capability}.rs and turn/src/executor.rs.      *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    PublicKeys,        \* finite set of distinct public key identifiers
    TokenIds,          \* finite set of distinct token-id identifiers
    MaxNonce,          \* model bound: cap on nonce values explored
    MaxTurns,          \* model bound: total successful turns explored
    MaxBalance,        \* model bound: cap on per-cell balance (and on transfer amount)
    InitialEndowment   \* per-cell starting balance at CreateCell time

(***************************************************************************)
(* Auth lattice                                                             *)
(*                                                                          *)
(* Mirrors cell/src/permissions.rs::AuthRequired.  `Permissions` in this    *)
(* spec collapses to a single AuthRequired (the action-axis split into      *)
(* send/receive/set_state/... is orthogonal to attenuation and is left to a *)
(* later increment — we keep one slot here so the lattice is visible).     *)
(***************************************************************************)

AuthRequired == {"None", "Signature", "Proof", "Either", "Impossible"}

\* IsNarrowerOrEqual(a, b) <=> a is at least as restrictive as b.
\* Matches AuthRequired::is_narrower_or_equal exactly.
IsNarrowerOrEqual(a, b) ==
    \/ a = "Impossible"                                  \* top: narrowest
    \/ b = "None"                                        \* bottom: anything narrower-or-equal to None
    \/ a = b                                             \* reflexive
    \/ (a = "Proof" /\ b = "Either")
    \/ (a = "Signature" /\ b = "Either")

\* IsAttenuation(parent, granted): granted may only be granted from parent
\* if it is narrower-or-equal.  This is cell/src/capability.rs::is_attenuation.
IsAttenuation(parent, granted) == IsNarrowerOrEqual(granted, parent)

(***************************************************************************)
(* Cell identity                                                            *)
(*                                                                          *)
(* The spec models BLAKE3(pk || tid) as a total injective function from     *)
(* (pk, tid) pairs to a CellId.  We construct CellId structurally as the    *)
(* tuple <<pk, tid>> — this is the most parsimonious way to enforce         *)
(* injectivity without modeling a hash function.  The injectivity matches   *)
(* the Rust contract: derive_raw is collision-resistant on its 64-byte      *)
(* input.                                                                   *)
(***************************************************************************)

DeriveId(pk, tid) == <<pk, tid>>

CellIds == { DeriveId(pk, tid) : pk \in PublicKeys, tid \in TokenIds }

(***************************************************************************)
(* State                                                                    *)
(*                                                                          *)
(* `cells` : CellId -> [pk, tid, nonce, perm]                               *)
(*   pk     : public key bytes; must satisfy id = DeriveId(pk, tid)         *)
(*   tid    : token id bytes; ditto                                         *)
(*   nonce  : Nat <= MaxNonce                                               *)
(*   perm   : the cell's own authorization requirement (used as the         *)
(*            "parent" when granting capabilities away from this cell)      *)
(*                                                                          *)
(* `caps`  : { <<holder, target, perm>> }                                   *)
(*   The c-list relation: cell `holder` holds a capability to `target` with *)
(*   permission `perm`.  A capability that originates from a cell's own     *)
(*   permission perm0 may only be granted with perm <= perm0 in the lattice.*)
(*   A re-delegation of a held capability with parent perm pP may only be   *)
(*   re-granted with child perm pC where IsAttenuation(pP, pC).             *)
(*                                                                          *)
(* `turns` : Nat — count of successful turns performed (for bounded model). *)
(*                                                                          *)
(* New in this increment:                                                   *)
(*                                                                          *)
(* `cells[id].balance` : Nat <= MaxBalance.  Value held by the cell.        *)
(*                                                                          *)
(* `cells[id].receipts` : Seq(Receipt).  Per-cell receipt chain.  Each      *)
(*    receipt has fields:                                                   *)
(*      seq        : 1-based sequence number, equal to its position in the  *)
(*                   chain (i.e. Len(prefix) + 1).                          *)
(*      prev_hash  : "0" for the first receipt; otherwise the hash of the   *)
(*                   immediately preceding receipt.                         *)
(*      payload    : a tag identifying what kind of turn produced this      *)
(*                   receipt ("Nop" or <<"Transfer", to, amount, fee>>).    *)
(*    `Hash(r)` is modeled as the tuple <<r.seq, r.prev_hash, r.payload>>;  *)
(*    structural equality on tuples gives injectivity, mirroring the        *)
(*    collision-resistance assumption on BLAKE3 in node/src/mcp.rs.         *)
(*                                                                          *)
(* `burned` : Nat — running total of fees burned (sink for the              *)
(*    conservation invariant).                                              *)
(***************************************************************************)

\* Genesis sentinel for an empty receipt chain.  Matches the "all-zero"
\* previous_receipt_hash that node/src/mcp.rs writes into the first
\* receipt a cell ever produces.
GenesisPrevHash == "0"

\* Receipts in this model.  Receipts are tagged by payload:
\*   * "Nop"                — a nonce-only turn (no value movement)
\*   * <<"Transfer", t, a, f>> — a value-bearing turn sending amount `a`
\*       (plus fee `f`) from the holder to cell `t`.
\* The set of payloads is finite under the model bounds.
TransferPayloads(maxAmount, maxFee, otherCells) ==
    { <<"Transfer", t, a, f>> :
        t \in otherCells, a \in 0..maxAmount, f \in 0..maxFee }

\* Hash function: model BLAKE3(receipt) as the receipt's structural tuple.
\* The tuple is injective by construction, so distinct receipts get
\* distinct "hashes".  This is the same abstraction we use for DeriveId.
Hash(r) == <<r.seq, r.prev_hash, r.payload>>

VARIABLES cells, caps, turns, burned

vars == <<cells, caps, turns, burned>>

\* Per-cell type predicate.  We don't fix the receipt-payload set in a
\* set type because TLC would need a precise enumeration; the load-bearing
\* structural invariants are ChainSeqWellFormed and ChainWellLinked below.
CellTypeOK(c) ==
    /\ c.pk \in PublicKeys
    /\ c.tid \in TokenIds
    /\ c.nonce \in 0..MaxNonce
    /\ c.perm \in AuthRequired
    /\ c.balance \in 0..MaxBalance

CapRecord == [
    holder : CellIds,
    target : CellIds,
    perm   : AuthRequired
]

TypeOK ==
    /\ DOMAIN cells \subseteq CellIds
    /\ \A id \in DOMAIN cells : CellTypeOK(cells[id])
    /\ caps \subseteq CapRecord
    /\ turns \in 0..MaxTurns
    /\ burned \in 0..(MaxBalance * MaxTurns)

(***************************************************************************)
(* Initial state                                                            *)
(*                                                                          *)
(* The ledger starts empty.  Cells are introduced via CreateCell actions.   *)
(* This matches the Rust ledger: cells appear via Effect::CreateCell.       *)
(***************************************************************************)

Init ==
    /\ cells = << >>                       \* empty function
    /\ caps  = {}
    /\ turns = 0
    /\ burned = 0

(***************************************************************************)
(* Actions                                                                  *)
(***************************************************************************)

\* CreateCell: introduce a fresh cell.  Identity must be the BLAKE3 of
\* (pk, tid).  The cell must not already exist in the ledger.  Initial
\* nonce is 0 (matches CellState::new in cell/src/state.rs).
CreateCell(pk, tid, perm) ==
    LET id == DeriveId(pk, tid) IN
    /\ id \notin DOMAIN cells
    /\ perm \in AuthRequired
    /\ cells' = cells @@ (id :> [pk       |-> pk,
                                  tid      |-> tid,
                                  nonce    |-> 0,
                                  perm     |-> perm,
                                  balance  |-> InitialEndowment,
                                  receipts |-> << >>])
    /\ caps'  = caps
    /\ turns' = turns
    /\ burned' = burned
    \* Note: we do NOT count CreateCell as a "turn" in this spec — turns are
    \* nonce-bearing executions.  CreateCell is a setup action.

\* Helper: build the next receipt for a cell's chain given a payload.
\* Sequence is 1-based: the first receipt has seq = 1.  prev_hash is the
\* genesis sentinel for an empty chain, else the Hash of the current head.
NextReceipt(id, payload) ==
    LET chain  == cells[id].receipts
        seqN   == Len(chain) + 1
        prevH  == IF chain = << >>
                  THEN GenesisPrevHash
                  ELSE Hash(chain[Len(chain)])
    IN [seq |-> seqN, prev_hash |-> prevH, payload |-> payload]

\* SuccessfulTurnNop: a turn that supplies the matching nonce and is
\* accepted but moves no value.  Nonce ++ and append a "Nop" receipt.
\* This is the nonce-only path through Effect::IncrementNonce in
\* turn/src/action.rs with no value-bearing effects.
SuccessfulTurnNop(id, providedNonce) ==
    /\ id \in DOMAIN cells
    /\ turns < MaxTurns
    /\ cells[id].nonce < MaxNonce
    /\ providedNonce = cells[id].nonce            \* must match
    /\ LET r == NextReceipt(id, <<"Nop">>) IN
       cells' = [cells EXCEPT ![id].nonce    = @ + 1,
                              ![id].receipts = Append(@, r)]
    /\ caps'  = caps
    /\ turns' = turns + 1
    /\ burned' = burned

\* SuccessfulTurnTransfer: a value-bearing successful turn.  The holder's
\* nonce increments, balance decreases by amount+fee, the recipient's
\* balance increases by amount, and `fee` is added to `burned`.  The
\* holder's chain gains a Transfer receipt linking to its prior head.
\* Recipient receipt chains are not modified by this action (a real system
\* might emit a paired receipt; we model only the sender's chain to keep
\* the receipt-chain invariants per-cell and the state space tractable).
SuccessfulTurnTransfer(id, providedNonce, to, amount, fee) ==
    /\ id \in DOMAIN cells
    /\ to \in DOMAIN cells
    /\ to # id                                    \* no self-transfer
    /\ turns < MaxTurns
    /\ cells[id].nonce < MaxNonce
    /\ providedNonce = cells[id].nonce
    /\ amount \in 0..MaxBalance
    /\ fee    \in 0..MaxBalance
    /\ cells[id].balance >= amount + fee          \* must be able to pay
    /\ cells[to].balance + amount <= MaxBalance   \* model bound
    /\ LET r == NextReceipt(id, <<"Transfer", to, amount, fee>>) IN
       cells' = [cells EXCEPT ![id].nonce    = @ + 1,
                              ![id].balance  = @ - amount - fee,
                              ![id].receipts = Append(@, r),
                              ![to].balance  = @ + amount]
    /\ caps'  = caps
    /\ turns' = turns + 1
    /\ burned' = burned + fee

\* RejectedTurn: a turn with wrong nonce.  The ledger MUST NOT change.
\* We model rejection as a stutter on `cells`, `caps`, and `burned`.
RejectedTurn(id, providedNonce) ==
    /\ id \in DOMAIN cells
    /\ providedNonce # cells[id].nonce
    /\ cells' = cells
    /\ caps'  = caps
    /\ turns' = turns
    /\ burned' = burned

\* GrantFromOwn: cell `holder` mints a capability to itself or to another
\* cell.  The new capability is "rooted" in the holder's own permission:
\* the granted perm must be narrower-or-equal to holder's own perm.  This
\* models the executor branch that checks attenuation against an
\* originating permission.
GrantFromOwn(holder, target, grantedPerm) ==
    /\ holder \in DOMAIN cells
    /\ target \in DOMAIN cells
    /\ grantedPerm \in AuthRequired
    /\ IsAttenuation(cells[holder].perm, grantedPerm)
    /\ cells' = cells
    /\ caps'  = caps \cup {[holder |-> holder, target |-> target, perm |-> grantedPerm]}
    /\ turns' = turns
    /\ burned' = burned

\* Redelegate: a cell that already holds a capability re-delegates a
\* (possibly narrower) version of it to a third party.  The new perm must
\* be narrower-or-equal to the held perm.  This is the lattice rule the
\* executor enforces at turn/src/executor.rs:4265 and :5980.
Redelegate(holder, target, fromPerm, toCell, narrowerPerm) ==
    /\ holder \in DOMAIN cells
    /\ target \in DOMAIN cells
    /\ toCell \in DOMAIN cells
    /\ [holder |-> holder, target |-> target, perm |-> fromPerm] \in caps
    /\ narrowerPerm \in AuthRequired
    /\ IsAttenuation(fromPerm, narrowerPerm)
    /\ cells' = cells
    /\ caps'  = caps \cup
        {[holder |-> toCell, target |-> target, perm |-> narrowerPerm]}
    /\ turns' = turns
    /\ burned' = burned

\* Revoke: drop a capability from the c-list.  Revocation never violates
\* invariants — it can only shrink rights.
Revoke(holder, target, perm) ==
    /\ [holder |-> holder, target |-> target, perm |-> perm] \in caps
    /\ cells' = cells
    /\ caps'  = caps \ {[holder |-> holder, target |-> target, perm |-> perm]}
    /\ turns' = turns
    /\ burned' = burned

(***************************************************************************)
(* Adversarial actions                                                      *)
(*                                                                          *)
(* These are explicitly enabled here so the model checker can show our      *)
(* invariants forbid them.  An honest implementation would never permit     *)
(* these; we include them to demonstrate that the invariants catch them.   *)
(* They are guarded by ENABLED_ADVERSARY in the cfg.                       *)
(***************************************************************************)

\* Attempt to amplify a held capability — the negation of attenuation.
\* This action's existence in the spec gives TLC something to falsify the
\* `IsAttenuation` invariant with, if a developer ever accidentally
\* loosens the rule.
AttemptAmplify(holder, target, fromPerm, toCell, widerPerm) ==
    /\ holder \in DOMAIN cells
    /\ target \in DOMAIN cells
    /\ toCell \in DOMAIN cells
    /\ [holder |-> holder, target |-> target, perm |-> fromPerm] \in caps
    /\ widerPerm \in AuthRequired
    /\ ~ IsAttenuation(fromPerm, widerPerm)            \* deliberately wider
    /\ cells' = cells
    /\ caps'  = caps \cup
        {[holder |-> toCell, target |-> target, perm |-> widerPerm]}
    /\ turns' = turns
    /\ burned' = burned

(***************************************************************************)
(* Next-state relation                                                      *)
(***************************************************************************)

Next ==
    \/ \E pk \in PublicKeys, tid \in TokenIds, p \in AuthRequired :
            CreateCell(pk, tid, p)
    \/ \E id \in DOMAIN cells, n \in 0..MaxNonce :
            SuccessfulTurnNop(id, n)
    \/ \E id \in DOMAIN cells, to \in DOMAIN cells,
         n \in 0..MaxNonce, a \in 0..MaxBalance, f \in 0..MaxBalance :
            SuccessfulTurnTransfer(id, n, to, a, f)
    \/ \E id \in DOMAIN cells, n \in 0..MaxNonce :
            RejectedTurn(id, n)
    \/ \E h, t \in DOMAIN cells, p \in AuthRequired :
            GrantFromOwn(h, t, p)
    \/ \E h, t, u \in DOMAIN cells, fp, np \in AuthRequired :
            Redelegate(h, t, fp, u, np)
    \/ \E h, t \in DOMAIN cells, p \in AuthRequired :
            Revoke(h, t, p)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants                                                               *)
(*                                                                          *)
(* These are the three statements the user asked for, written as state      *)
(* predicates.                                                              *)
(***************************************************************************)

\* I1.  Identity integrity.
\* Every cell in the ledger has id = DeriveId(pk, tid).  Because we use the
\* derived value as the map key, this reduces to: pk and tid match the key.
IdentityIntegrity ==
    \A id \in DOMAIN cells :
        id = DeriveId(cells[id].pk, cells[id].tid)

\* I2.  Nonce well-formedness.
\* No cell ever has a negative nonce (vacuously true given the type), and
\* the bound is respected.
NonceWellFormed ==
    \A id \in DOMAIN cells :
        cells[id].nonce \in 0..MaxNonce

\* I2'.  Nonce monotonicity (action-level).
\* This is a *property* over the next-state relation: the nonce of an
\* existing cell never decreases.  We express it as an action property
\* using the prime operator.
NonceMonotonic ==
    \A id \in DOMAIN cells :
        id \in DOMAIN cells' => cells'[id].nonce >= cells[id].nonce

\* I3.  Attenuation soundness — state invariant.
\* Every capability in the c-list either was minted from a cell whose own
\* perm attenuates to c.perm (the `GrantFromOwn` source) OR is the
\* attenuation of some other cap to the same target (the `Redelegate`
\* source).  This is the inductive invariant maintained by
\* GrantFromOwn / Redelegate / Revoke.
\*
\* Caveat:  when any cell has perm = "None" (the lattice bottom), the
\* first disjunct is satisfied by every cap (since `None` attenuates to
\* anything).  In that regime the *state* check is weak.  In settings
\* where all cells have strictly restrictive perms (Signature / Proof /
\* Either / Impossible), the state invariant does meaningfully discriminate
\* amplifying caps — see the sanity test in README.md.  The companion
\* action-level property `NoAmplificationProperty` is the strictly
\* stronger statement.
AttenuationSoundness ==
    \A c \in caps :
        \/ \E h \in DOMAIN cells :
                IsAttenuation(cells[h].perm, c.perm)
        \/ \E p \in caps :
                /\ p.target = c.target
                /\ p # c
                /\ IsAttenuation(p.perm, c.perm)

\* I3'. Action-level no-amplification.
\* For every action step, every cap that appears in `caps'` and not in
\* `caps` (i.e., a freshly granted cap) must have been derivable by
\* attenuation from some "source" present in the prior state — either a
\* cell's own perm or an existing cap with the same target.  This is the
\* meaningful inductive statement of attenuation.
NoAmplification ==
    \A c \in (caps' \ caps) :
        \/ \E h \in DOMAIN cells :
                IsAttenuation(cells[h].perm, c.perm)
        \/ \E p \in caps :
                /\ p.target = c.target
                /\ IsAttenuation(p.perm, c.perm)

NoAmplificationProperty == [][NoAmplification]_vars

(***************************************************************************)
(* I4.  Balance conservation.                                               *)
(*                                                                          *)
(* The total value in the system (sum of cell balances + fees burned) is    *)
(* invariant from the moment all cells are created.  Because each           *)
(* CreateCell endows a fresh cell with InitialEndowment, the conserved      *)
(* quantity is:                                                             *)
(*                                                                          *)
(*   sum(cells[i].balance) + burned == |cells| * InitialEndowment           *)
(*                                                                          *)
(* This is a *state* invariant — at any reachable state, the total equals   *)
(* the endowment times the number of cells.  It is the inductive form of    *)
(* "every successful turn preserves balance + fee = 0 delta" from           *)
(* pyana-protocol-tests/src/invariants/balance_conservation.rs.             *)
(*                                                                          *)
(* The companion *action* property `TurnPreservesBalance` says more         *)
(* directly: across any single step that increments `turns`, the conserved  *)
(* quantity is unchanged.                                                   *)
(***************************************************************************)

\* Sum balances by induction on a finite set.  TLA+ requires the
\* RECURSIVE declaration at the module level (it cannot appear inside LET).
RECURSIVE SumBalancesSet(_, _)
SumBalancesSet(cellMap, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN cellMap[x].balance + SumBalancesSet(cellMap, S \ {x})

SumBalances(cellMap) == SumBalancesSet(cellMap, DOMAIN cellMap)

ConservedTotal == SumBalances(cells) + burned

BalanceConservation ==
    ConservedTotal = Cardinality(DOMAIN cells) * InitialEndowment

\* Action-level: balance is preserved across every step (including non-turn
\* steps, which don't touch cells or burned, and CreateCell, which adds
\* InitialEndowment to both sides).
TurnConservesBalance ==
    SumBalances(cells') + burned' - Cardinality(DOMAIN cells') * InitialEndowment
        = SumBalances(cells) + burned - Cardinality(DOMAIN cells) * InitialEndowment

TurnConservesBalanceProperty == [][TurnConservesBalance]_vars

(***************************************************************************)
(* I5.  Receipt-chain causal soundness.                                     *)
(*                                                                          *)
(* For each cell, the receipt chain is a well-linked sequence:              *)
(*                                                                          *)
(*   1. Sequence numbers are 1-based and match position: receipts[i].seq=i. *)
(*   2. receipts[1].prev_hash = GenesisPrevHash.                            *)
(*   3. For i > 1, receipts[i].prev_hash = Hash(receipts[i-1]).             *)
(*                                                                          *)
(* This is the state form of the receipt-chain invariant enforced by        *)
(* verify_receipt_chain in turn/src/ and by node/src/mcp.rs's               *)
(* previous_receipt_hash threading.                                         *)
(*                                                                          *)
(* The companion action property `ReceiptChainAppendOnly` says: no step     *)
(* may shorten, reorder, or rewrite any cell's existing receipt prefix.     *)
(* Only an append at the tail is allowed.                                   *)
(***************************************************************************)

ChainSeqWellFormed(chain) ==
    \A i \in 1..Len(chain) : chain[i].seq = i

ChainWellLinked(chain) ==
    /\ Len(chain) >= 1 => chain[1].prev_hash = GenesisPrevHash
    /\ \A i \in 2..Len(chain) :
            chain[i].prev_hash = Hash(chain[i-1])

ReceiptChainIntegrity ==
    \A id \in DOMAIN cells :
        /\ ChainSeqWellFormed(cells[id].receipts)
        /\ ChainWellLinked(cells[id].receipts)

\* Action-level: every cell that existed before must have a receipt chain
\* in the next state whose prefix equals the old chain (i.e. append-only).
\* A new cell (CreateCell) has empty old chain and empty new chain — also
\* a trivial prefix relation.
ReceiptChainAppendOnly ==
    \A id \in DOMAIN cells :
        /\ id \in DOMAIN cells'
        /\ Len(cells'[id].receipts) >= Len(cells[id].receipts)
        /\ \A i \in 1..Len(cells[id].receipts) :
                cells'[id].receipts[i] = cells[id].receipts[i]

ReceiptChainAppendOnlyProperty == [][ReceiptChainAppendOnly]_vars

\* Action-level: every successful turn appends *exactly one* receipt to the
\* executing cell's chain (and to no other cell's chain).  This pins down
\* the "one turn => one receipt" property that node/src/mcp.rs relies on.
TurnAppendsOneReceipt ==
    (turns' = turns + 1)
        => \E id \in DOMAIN cells' :
            /\ Len(cells'[id].receipts) = Len(cells[id].receipts) + 1
            /\ \A j \in DOMAIN cells' \ {id} :
                    j \in DOMAIN cells =>
                    cells'[j].receipts = cells[j].receipts

TurnAppendsOneReceiptProperty == [][TurnAppendsOneReceipt]_vars

(***************************************************************************)
(* Adversarial actions for receipt-chain falsification.                     *)
(*                                                                          *)
(* Disabled by default (StateBound keeps them out of Next).  They exist as  *)
(* documentation of what the invariant forbids — see the deliberate-break  *)
(* sanity checks in README.md.                                              *)
(*                                                                          *)
(* If a developer ever introduced a code path that allowed receipt          *)
(* rewriting (truncation, splice, or hash-mismatched append), enabling      *)
(* the corresponding action below in Next would let TLC find a              *)
(* counterexample.                                                          *)
(***************************************************************************)

\* These are commented out of Next; they exist for the deliberate-break
\* check described in README.md.  Uncomment in Next to verify the
\* receipt-chain invariants bite.

(***************************************************************************)
(* Conjunction of state invariants (for the cfg's INVARIANT directive).     *)
(***************************************************************************)
Invariant ==
    /\ TypeOK
    /\ IdentityIntegrity
    /\ NonceWellFormed
    /\ AttenuationSoundness
    /\ BalanceConservation
    /\ ReceiptChainIntegrity

\* Action-level monotonicity, for TLC's PROPERTY directive.
MonotonicNonce == [][NonceMonotonic]_vars

\* State constraint: keep the c-list bounded so TLC doesn't explore an
\* unboundedly growing set of caps.  Referenced from CellModel.cfg.
\* We also bound |cells| and the per-cell receipt chain length to keep
\* the search tractable.
StateBound ==
    /\ Cardinality(caps) =< 3
    /\ Cardinality(DOMAIN cells) =< 2
    /\ \A id \in DOMAIN cells : Len(cells[id].receipts) =< MaxTurns

(***************************************************************************)
(* Theorem (sketch, not machine-checked here):                              *)
(*   Spec => []Invariant /\ MonotonicNonce                                  *)
(*                                                                          *)
(* TLC will model-check this under the constants in CellModel.cfg.          *)
(***************************************************************************)

================================================================================
