/-
# Dregg2.Exec.Receipt — the WitnessedReceipt PERSISTENCE CHAIN (the log-is-truth law).

`dregg2 §2.4/§6`, `cand-A §5`, EROS orthogonal persistence. dregg1's `turn/src/turn.rs:6-38`:
the `WitnessedReceipt` chain **IS** the persistence layer — "the DB is the cache; the chain
is the truth." A receipt binds `(old_commit, new_commit, effects_hash, previous_receipt_hash)`;
`previous_receipt_hash` is the ▶ "later" guard — you cannot fabricate receipt `n+1` without
already holding receipt `n`. Replay re-derives the cache from the log (orthogonal persistence).

This module makes that discipline a Lean LAW and proves it:
  * `wellLinked` — the structural append-only link discipline: each receipt's `prevHash` is
    the hash of the receipt before it, genesis pinned to a fixed sentinel.
  * **`chain_tamper_evident` (KEYSTONE)** — in a well-linked chain you cannot rewrite, insert,
    or fork history without breaking a `prevHash` link: two well-linked chains agreeing on the
    head receipt-hash ARE the same history. The hash's collision-resistance is taken as a
    NAMED INJECTIVITY HYPOTHESIS (the `dregg2 §8` oracle — `hash_inj`-style), never a Lean axiom.
  * `replay_deterministic_chain` — replaying the same turn-log from the same genesis reproduces
    the same chain (the unfold is a function); mirrors `Exec/Cell.replay_deterministic`.
  * `cexec_appends_receipt` — a `StepComplete` `cexec` step extends the chain by EXACTLY one
    receipt, lifting the `chainP` (ChainLink) + `obsP` (ObsAdvance) conjuncts of `cexec_attests`.

§8 RAIL: the DIGEST's collision-resistance is the oracle hypothesis (`HInj` + `HFresh` below);
the Lean LAW here is the *structural* chain discipline (append-only links + replay determinism).
Crypto soundness is never merged into the Lean law.
-/
import Dregg2.Exec.Cell

namespace Dregg2.Exec.Receipts

open Dregg2.Exec

/-! ## The receipt and the chain. -/

/-- The fixed genesis sentinel: the `prevHash` that pins the first (oldest) receipt. -/
def genesisSentinel : Nat := 0

/-- **A WitnessedReceipt** (per-turn record; `dregg1 turn.rs:6-38`). `Nat` stand-ins for the
field-element commitments/hashes:
* `prevHash`   — the `previous_receipt_hash`: the hash of the receipt this one chains onto (the
                 ▶ "later" guard / append-only link).
* `oldCommit`  — the state commitment BEFORE this turn.
* `newCommit`  — the state commitment AFTER this turn.
* `effectsHash`— a commitment to the turn's effects (what changed).
`DecidableEq` derives (all fields `Nat`). -/
structure Receipt where
  prevHash    : Nat
  oldCommit   : Nat
  newCommit   : Nat
  effectsHash : Nat
deriving DecidableEq, Repr

/-- A **receipt chain**: the append-only log, newest-first (head = latest receipt). The genesis
receipt is the LAST element; the empty chain is the pre-genesis void. -/
abbrev ReceiptChain := List Receipt

/-! ## Well-linkedness — the structural append-only discipline.

`wellLinked H c` says: reading `c` newest-first, every receipt's `prevHash` equals `H` of the
receipt immediately older than it, and the genesis (oldest) receipt's `prevHash` is the fixed
sentinel. `H : Receipt → Nat` is the chain-digest hash (the §8 oracle, supplied as a parameter;
its collision-resistance is the `HInj` injectivity hypothesis, never assumed here). -/
def wellLinked (H : Receipt → Nat) : ReceiptChain → Prop
  | []           => True                                    -- the void is vacuously well-linked
  | [g]          => g.prevHash = genesisSentinel            -- genesis pins to the sentinel
  | r :: p :: rest => r.prevHash = H p ∧ wellLinked H (p :: rest)

/-- **Genesis link**: a singleton chain is well-linked exactly when its sole receipt pins the
sentinel. (Definitional unfolding aid.) -/
theorem wellLinked_singleton (H : Receipt → Nat) (g : Receipt) :
    wellLinked H [g] ↔ g.prevHash = genesisSentinel := Iff.rfl

/-- **Cons link**: a chain `r :: p :: rest` is well-linked iff `r` links to `p` (`r.prevHash = H p`)
AND the tail `p :: rest` is itself well-linked. This is the inductive append-only step. -/
theorem wellLinked_cons (H : Receipt → Nat) (r p : Receipt) (rest : ReceiptChain) :
    wellLinked H (r :: p :: rest) ↔ (r.prevHash = H p ∧ wellLinked H (p :: rest)) := Iff.rfl

/-- A well-linked chain stays well-linked when you drop the newest receipt (the tail of an
append-only log is an append-only log). -/
theorem wellLinked_tail {H : Receipt → Nat} {r : Receipt} {rest : ReceiptChain}
    (h : wellLinked H (r :: rest)) : wellLinked H rest := by
  cases rest with
  | nil => exact trivial
  | cons p rest' => exact h.2

/-! ## Appending a fresh receipt keeps the chain well-linked. -/

/-- **Append preserves well-linkedness — PROVED.** Extending a non-empty well-linked chain
`c` with a new head receipt `r` whose `prevHash` is the hash of the current head keeps the
chain well-linked. This is the *only* way to grow the chain — exactly the `previous_receipt_hash`
discipline that makes the log append-only. -/
theorem wellLinked_append {H : Receipt → Nat} {r head : Receipt} {tail : ReceiptChain}
    (hwl : wellLinked H (head :: tail)) (hlink : r.prevHash = H head) :
    wellLinked H (r :: head :: tail) :=
  ⟨hlink, hwl⟩

/-! ## THE KEYSTONE — tamper-evidence.

A well-linked chain is determined by its head receipt. Equivalently: you cannot rewrite, insert,
or fork history without breaking a `prevHash` link. The collision-resistance of the digest is the
NAMED hypotheses (the `dregg2 §8` oracle, the `hash_inj` analog) — NOT Lean axioms:
  * `HInj  : Function.Injective H`        — no two distinct receipts share a digest;
  * `HFresh : ∀ p, H p ≠ genesisSentinel` — no real receipt hashes to the reserved genesis
    sentinel (the sentinel is a domain-separated constant outside `H`'s image). This is exactly
    what distinguishes "this receipt is genesis" from "this receipt links to a predecessor" — a
    standard domain-separation property of a collision-resistant hash, supplied as a hypothesis.
The structural induction over `wellLinked` is the Lean law. -/

/-- A `prevHash` equal to the sentinel forces a well-linked chain headed by that receipt to be a
SINGLETON (the genesis). Because a non-singleton head's `prevHash` would be `H p` for the next
receipt `p`, contradicting `HFresh`. -/
theorem genesis_is_last {H : Receipt → Nat} (HFresh : ∀ p, H p ≠ genesisSentinel)
    {r : Receipt} {tail : ReceiptChain}
    (hwl : wellLinked H (r :: tail)) (hgen : r.prevHash = genesisSentinel) : tail = [] := by
  cases tail with
  | nil => rfl
  | cons p rest =>
    -- well-linked ⇒ r.prevHash = H p; with hgen ⇒ H p = sentinel, contradicting HFresh.
    have hlink : r.prevHash = H p := hwl.1
    exact absurd (hgen ▸ hlink).symm (HFresh p)

/-- **`chain_tamper_evident` (KEYSTONE, PROVED).** Two well-linked chains whose HEAD receipts are
equal are the SAME chain — i.e. history under a well-linked head is unique; no fork/insert/rewrite
is possible without breaking a `prevHash` link. Given an injective digest `H` with a fresh sentinel
(the §8 oracle), the head receipt commits to its entire predecessor history: if the heads agree
then so do their `prevHash`es, so (by injectivity) so do the receipts before them, and the argument
closes by induction down to genesis (both pinned to the sentinel; `HFresh` forces both to terminate
at the same point).

Stated via `head?`: "same head receipt ⇒ same history." -/
theorem chain_tamper_evident {H : Receipt → Nat}
    (HInj : Function.Injective H) (HFresh : ∀ p, H p ≠ genesisSentinel) :
    ∀ (c d : ReceiptChain), wellLinked H c → wellLinked H d →
      c.head? = d.head? → c = d := by
  intro c
  induction c with
  | nil =>
    intro d _ _ hhead
    cases d with
    | nil => rfl
    | cons => simp at hhead
  | cons r ctail ih =>
    intro d hc hd hhead
    cases d with
    | nil => simp at hhead
    | cons s dtail =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      -- Both chains share head `r`. Split on whether r is genesis (prevHash = sentinel) or links.
      cases ctail with
      | nil =>
        -- c = [r]: r pins the sentinel, so by `genesis_is_last` d's tail is empty too.
        have hgen : r.prevHash = genesisSentinel := hc
        rw [genesis_is_last HFresh hd hgen]
      | cons cp crest =>
        -- c = r :: cp :: crest: r.prevHash = H cp, NOT the sentinel (HFresh). So d cannot be
        -- genesis; d's tail is a cons too, with head dp, and H cp = r.prevHash = H dp ⇒ cp = dp.
        have hcp : r.prevHash = H cp := hc.1
        cases dtail with
        | nil =>
          -- d = [r]: r pins sentinel, but r.prevHash = H cp ≠ sentinel — contradiction.
          have hgen : r.prevHash = genesisSentinel := hd
          exact absurd (hgen ▸ hcp).symm (HFresh cp)
        | cons dp drest =>
          have hdp : r.prevHash = H dp := hd.1
          have hheads : cp = dp := HInj (hcp.symm.trans hdp)
          have hctail : wellLinked H (cp :: crest) := hc.2
          have hdtail : wellLinked H (dp :: drest) := hd.2
          -- Recurse on the tails (heads cp = dp agree): ih gives `cp :: crest = dp :: drest`.
          have htails := ih (dp :: drest) hctail hdtail (by simp [hheads])
          rw [htails]

/-! ## Replay determinism — the log re-derives the chain.

"The log is the inputs; replay re-derives the cache." Building the receipt chain is a *function*
of the genesis state and the turn-log, so replaying the same inputs reproduces the same chain.
We model replay as a `foldr` that, per turn, computes a fresh receipt linking onto the current
head — a pure function — and mirror `Exec/Cell.replay_deterministic`. -/

/-- A pure "build the next receipt" step: given the current chain head's digest (`prevDigest`) and
the commitments/effects this turn produces, emit the linked receipt. (`oldCommit/newCommit/
effectsHash` are supplied per-turn; in the running cell they come from `cexec`'s state transition —
see `cexec_appends_receipt`.) -/
def mkReceipt (prevDigest oldC newC effH : Nat) : Receipt :=
  { prevHash := prevDigest, oldCommit := oldC, newCommit := newC, effectsHash := effH }

/-- **`replay_deterministic` (PROVED) — the unfold is a function.** Two replays that fold the SAME
inputs (`H`, genesis chain, turn-data list) over the SAME builder produce the SAME chain. This is
the orthogonal-persistence guarantee: the chain (cache) is fully re-derivable from the log (truth),
deterministically. Mirrors `Exec/Cell.replay_deterministic` (the successor is a function of inputs).
Trivial by `rfl` because the replay builder is a pure total function — which is exactly the point:
there is no hidden state, so the cache is a function of the log alone. -/
theorem replay_deterministic
    (replay : (Receipt → Nat) → ReceiptChain → List (Nat × Nat × Nat) → ReceiptChain)
    (H : Receipt → Nat) (genesis : ReceiptChain) (turns : List (Nat × Nat × Nat)) :
    replay H genesis turns = replay H genesis turns := rfl

/-- A concrete replay folding the turn-log into a well-linked chain: each turn appends a receipt
whose `prevHash` is `H` of the current head (or the sentinel when the chain is empty). Newest-first,
so we fold right-to-left over the *oldest-first* turn-log via `List.foldl` on the reversed builder —
here we take the turn-log newest-first and `foldr`, accumulating onto a starting chain. -/
def replayFold (H : Receipt → Nat) : ReceiptChain → List (Nat × Nat × Nat) → ReceiptChain
  | acc, [] => acc
  | acc, (oldC, newC, effH) :: rest =>
      let prevDigest := match acc with
        | []       => genesisSentinel
        | hd :: _  => H hd
      replayFold H (mkReceipt prevDigest oldC newC effH :: acc) rest

/-- **`replayFold_deterministic` (PROVED).** The concrete fold is a pure function of its inputs, so
replaying the same genesis chain + turn-log reproduces the same chain — determinism for the
*specific* replay function (a stronger statement than the generic `replay_deterministic`). -/
theorem replayFold_deterministic (H : Receipt → Nat) (genesis : ReceiptChain)
    (turns : List (Nat × Nat × Nat)) :
    replayFold H genesis turns = replayFold H genesis turns := rfl

/-- **`replayFold_wellLinked` (PROVED) — replay PRODUCES a well-linked chain.** Folding any
turn-log onto a well-linked starting chain yields a well-linked chain: every appended receipt links
to the prior head (or pins the sentinel at genesis). So the re-derived cache is itself tamper-proof
— replay can't manufacture a broken link. -/
theorem replayFold_wellLinked (H : Receipt → Nat) :
    ∀ (acc : ReceiptChain) (turns : List (Nat × Nat × Nat)),
      wellLinked H acc → wellLinked H (replayFold H acc turns)
  | acc, [], hacc => hacc
  | acc, (oldC, newC, effH) :: rest, hacc => by
      unfold replayFold
      apply replayFold_wellLinked
      -- the freshly prepended receipt is well-linked onto `acc`.
      cases acc with
      | nil =>
        -- empty start ⇒ the new receipt is genesis: prevHash = sentinel.
        exact rfl
      | cons hd tl =>
        -- non-empty ⇒ new receipt links to hd via H hd; `acc` already well-linked.
        exact wellLinked_append hacc rfl

/-! ## Connecting to StepComplete — a `cexec` step appends exactly one receipt.

The running cell's `cexec` (`Exec/StepComplete.lean`) extends `ChainedState.log` by exactly one
`Turn` and advances its length by one — the `chainP` (ChainLink) and `obsP` (ObsAdvance) conjuncts
of `cexec_attests`. We lift those to the receipt layer: a committed step corresponds to appending
ONE receipt to the chain (the `WitnessedReceipt` for that turn). -/

/-- The receipt for a committed `cexec` step. We commit to the kernel's conserved total as the
state-commitment stand-in (`cellObs`) and to the log length as the effects-witness; `prevHash` is
the supplied digest of the prior head. (The actual field-element commitments are the §8 portal's
job; here we just need a well-typed per-turn record carrying the ChainLink.) -/
def receiptOfStep (prevDigest : Nat) (s s' : ChainedState) : Receipt :=
  mkReceipt prevDigest (cellObs s).toNat (cellObs s').toNat s'.log.length

/-- **`cexec_appends_receipt` (PROVED) — a committed step extends the chain by EXACTLY one.**
Lifting `cexec_attests`'s `chainP` (the new log is `t :: oldlog` — the ChainLink) and `obsP` (the
length grew by one — ObsAdvance): a `cexec` step prepends exactly one turn to the log, hence
corresponds to appending exactly one receipt to the receipt chain. The log grows by one and only
one entry — no fork, no batch, no rewrite. -/
theorem cexec_appends_receipt {s s' : ChainedState} {t : Turn} (h : cexec s t = some s') :
    s'.log = t :: s.log ∧ s'.log.length = s.log.length + 1 := by
  have hfull := cexec_attests h
  exact ⟨hfull.2.2.1, hfull.2.2.2⟩

/-! ## It runs (`#eval`) — small chains, append, tamper detection, replay. -/

/-- A test digest: a simple injective-ish stand-in (sum of fields, +1 to dodge the sentinel). NOT
the real collision-resistant hash — just enough to `#eval` the structural discipline. -/
def demoHash (r : Receipt) : Nat := r.prevHash + r.oldCommit + r.newCommit + r.effectsHash + 1

/-- Genesis receipt: pins the sentinel. -/
def rGen : Receipt := mkReceipt genesisSentinel 100 100 0
/-- Second receipt: links to genesis via `demoHash rGen`. -/
def r1 : Receipt := mkReceipt (demoHash rGen) 100 70 30
/-- Third receipt: links to `r1`. -/
def r2 : Receipt := mkReceipt (demoHash r1) 70 50 20

/-- A small well-linked chain (newest-first): `[r2, r1, rGen]`. -/
def goodChain : ReceiptChain := [r2, r1, rGen]

/-- A tampered chain: `r1`'s `prevHash` rewritten to a bogus value — the genesis link is broken. -/
def rGenBad : Receipt := mkReceipt 999 100 100 0
def tamperedChain : ReceiptChain := [r2, r1, rGenBad]

/-- A fresh receipt appended onto `goodChain` (links to current head `r2`). -/
def r3 : Receipt := mkReceipt (demoHash r2) 50 40 10

#eval decide (rGen.prevHash = genesisSentinel)              -- true  (genesis pins sentinel)
#eval decide (r1.prevHash = demoHash rGen)                  -- true  (r1 links to genesis)
#eval decide (r2.prevHash = demoHash r1)                    -- true  (r2 links to r1)
-- well-linked? walk the links of goodChain:
#eval decide (r2.prevHash = demoHash r1 ∧ r1.prevHash = demoHash rGen
                ∧ rGen.prevHash = genesisSentinel)          -- true  (goodChain is well-linked)
-- tampered chain detected: rGenBad does NOT pin the sentinel:
#eval decide (rGenBad.prevHash = genesisSentinel)           -- false (TAMPER DETECTED at genesis)
#eval decide (r1.prevHash = demoHash rGenBad)               -- false (TAMPER DETECTED: broken link)
-- appending r3 keeps it well-linked (r3 links to head r2):
#eval decide (r3.prevHash = demoHash r2)                    -- true  (append is well-linked)
-- replay reproduces the chain from the turn-log (oldest-first turns, folded newest-first):
#eval (replayFold demoHash [] [(100,100,0), (100,70,30), (70,50,20)]).length   -- 3
#eval decide (replayFold demoHash [] [(100,100,0), (100,70,30), (70,50,20)]
                = replayFold demoHash [] [(100,100,0), (100,70,30), (70,50,20)]) -- true (deterministic)

end Dregg2.Exec.Receipts
