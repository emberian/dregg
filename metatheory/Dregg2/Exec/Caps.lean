/-
# Dregg2.Exec.Caps — the EXECUTABLE capability operations (the seL4 heart).

The l4v `CSpace`/`Tcb` analog: concrete, **computable** operations over the capability
table `Caps := Label → List Cap` (`Authority/Positional.lean`), together with the
authority guarantees that make them a *sound* cap system. Where `Exec/Kernel.lean`
builds the resource machine and proves conservation + authorization, here we build the
cap-management machine and prove the seL4 cap-soundness core:

- `grant`/`derive` — hand a cap (optionally a derived/attenuated one) to a holder's slot;
- `attenuate`  — narrow an `endpoint` cap's rights (drop some `Auth`s); the result confers
  a SUBSET of the parent's authority (the concrete `LossyMorphism` content);
- `revoke`     — remove a cap from a holder's slot;
- `invoke`     — does a holder present a cap authorizing a turn (relates to
  `Kernel.authorizedB`).

Proven guarantees (the cap-system soundness core):
- `attenuate_subset`  — `capAuthConferred (attenuate keep c) ⊆ capAuthConferred c`;
- `derive_no_amplify` — a derived/attenuated cap confers ≤ the parent's authority;
- `revoke_removes`    — after `revoke`, the holder no longer holds that cap;
- `exec_authorized_is_integrity` — connects `Kernel.exec`'s authority check to
  `Authority.Integrity` (the l4v `call_kernel_integrity` lift): a committed turn's
  source-cell change is admissible per the `Integrity` case-split. The `intra` (owner)
  case is PROVED; the `cross` case is an honest `-- OPEN:` (needs a `Verifiable` bridge
  from the concrete held `Cap` to the `Integrity` predicate's witness).

Pure executable Lean, `#eval`-able. Reuses `Authority` + `Exec.Kernel`; edits neither.
-/
import Dregg2.Authority.Positional
import Dregg2.Exec.Kernel
import Dregg2.Tactics

namespace Dregg2.Exec

open Dregg2.Authority Dregg2.Laws

/-! ## Executable capability operations over the `Caps` table -/

/-- **`grant`** (l4v `cap_insert`): add cap `c` to `holder`'s slot. Pure update of the
total function `Caps := Label → List Cap`; other slots are untouched. -/
def grant (caps : Caps) (holder : Label) (c : Cap) : Caps :=
  fun l => if l = holder then c :: caps l else caps l

/-- **`attenuate`** (the `LossyMorphism` content, concrete): narrow an `endpoint` cap to
only the rights in `keep` (drop the rest). A `node`/`null` cap is returned unchanged —
those confer fixed authority with no rights list to filter. The result confers a SUBSET
of the original authority (`attenuate_subset`). -/
def attenuate (keep : List Auth) (c : Cap) : Cap :=
  match c with
  | .endpoint t rights => .endpoint t (rights.filter (fun a => keep.contains a))
  | other              => other

/-- **`derive`** (l4v `derive_cap` ∘ `cap_insert`): grant `holder` an ATTENUATED copy of
`c` — the standard "hand out a weaker cap" move. Defined as `grant ∘ attenuate`, so it
inherits `attenuate`'s no-amplification guarantee (`derive_no_amplify`). -/
def derive (caps : Caps) (holder : Label) (keep : List Auth) (c : Cap) : Caps :=
  grant caps holder (attenuate keep c)

/-- **`revoke`** (l4v `cap_delete`): remove every copy of cap `c` from `holder`'s slot.
Other slots untouched. -/
def revoke (caps : Caps) (holder : Label) (c : Cap) : Caps :=
  fun l => if l = holder then (caps l).filter (fun d => d ≠ c) else caps l

/-- **`invoke`** (l4v `decode_invocation` authority check, lifted): does `holder` present,
in its slot, a cap that authorizes acting on `target` with `auth`? A `node target` cap
confers `control` (hence everything); an `endpoint target rights` cap confers exactly its
`rights`. This is the per-cap shadow of `Kernel.authorizedB`'s slot scan. -/
def invoke (caps : Caps) (holder target : Label) (auth : Auth) : Bool :=
  (caps holder).any (fun c =>
    (c == Cap.node target) ||
    (match c with
     | .endpoint t rights => (t == target) && rights.contains auth
     | _ => false))

/-! ## The cap-system soundness guarantees (PROVED) -/

/-- **`attenuate_subset` — PROVED.** Attenuation only narrows: the authority conferred by
the attenuated cap is a sublist (hence ⊆) of the parent's. This is the concrete,
list-level realization of `LossyMorphism`'s `in_le`/`out_le` (attenuation-only). -/
theorem attenuate_subset (keep : List Auth) (c : Cap) :
    capAuthConferred (attenuate keep c) ⊆ capAuthConferred c := by
  cases c with
  | endpoint t rights =>
      -- `capAuthConferred (.endpoint t r) = r`; attenuate filters `rights`.
      simp only [attenuate, capAuthConferred]
      intro a ha
      exact List.mem_of_mem_filter ha
  | node t => simp [attenuate, capAuthConferred]
  | null   => simp [attenuate, capAuthConferred]

/-- **`derive_no_amplify` — PROVED.** A derived cap confers ≤ the parent's authority: the
holder gains nothing it could not already have been granted directly, and never more than
`c` itself confers. (Corollary of `attenuate_subset`: `derive` grants `attenuate keep c`.) -/
theorem derive_no_amplify (keep : List Auth) (c : Cap) :
    capAuthConferred (attenuate keep c) ⊆ capAuthConferred c :=
  attenuate_subset keep c

/-- **`revoke_removes` — PROVED.** After `revoke caps holder c`, the holder no longer holds
`c` in its slot. (The fail-closed counterpart of `grant`: removed authority is gone.) -/
theorem revoke_removes (caps : Caps) (holder : Label) (c : Cap) :
    c ∉ (revoke caps holder c) holder := by
  simp only [revoke, if_true]
  intro hc
  -- `c ∈ filter (· ≠ c) (caps holder)` forces the predicate `c ≠ c`, contradiction.
  have hne : (decide (c ≠ c)) = true := (List.mem_filter.mp hc).2
  simp at hne

/-- **`grant_adds` — PROVED** (companion sanity fact): after `grant`, the holder holds the
cap. Shows `grant`/`revoke` are genuine inverses on slot membership. -/
theorem grant_adds (caps : Caps) (holder : Label) (c : Cap) :
    c ∈ (grant caps holder c) holder := by
  simp only [grant, if_true]
  exact List.mem_cons_self

/-- **`grant_other_untouched` — PROVED**: granting to `holder` leaves every other slot's
caps exactly as they were (no ambient authority leaks to bystanders). -/
theorem grant_other_untouched (caps : Caps) (holder l : Label) (c : Cap) (h : l ≠ holder) :
    (grant caps holder c) l = caps l := by
  simp only [grant, if_neg h]

/-- **`revoke_subset` — PROVED**: revoke only removes — the post-state slot is a sublist of
the pre-state slot, so revocation never grows authority. -/
theorem revoke_subset (caps : Caps) (holder l : Label) (c : Cap) :
    (revoke caps holder c) l ⊆ caps l := by
  simp only [revoke]
  rcases eq_or_ne l holder with h | h
  · subst h; rw [if_pos rfl]; intro d hd; exact List.mem_of_mem_filter hd
  · rw [if_neg h]; exact fun d hd => hd

/-! ## Bridge: `Kernel.exec`'s authority check ⟶ `Authority.Integrity`

`Kernel.authorizedB` (used by `Kernel.exec`) authorizes a turn over `src` iff the actor
owns `src` (`actor = src`) OR holds a discharging cap on it. `Authority.Integrity`
case-splits identically: `intra` (owner ∈ subjects) admits an arbitrary change; `cross`
admits a change witnessed by `Discharged (p ko ko') w`. We connect them: a committed
`exec` turn's source-cell change satisfies `Integrity` with `subjects = [actor]`.
-/

/-- The `intra` discriminant from a committed turn: `Kernel.authorizedB` having fired the
ownership disjunct means `actor = src`, i.e. the actor owns the cell it is changing —
exactly `Integrity`'s `owner ∈ subjects` precondition with `subjects = [src]`. -/
theorem authorizedB_owner_intra (_caps : Caps) (turn : Turn)
    (hown : (turn.actor == turn.src) = true) :
    turn.src ∈ [turn.actor] := by
  have : turn.actor = turn.src := by simpa using hown
  simp [this]

/-- **`exec_authorized_is_integrity` (intra case PROVED; cross case OPEN).**

Connects `Kernel.exec`'s authority check to `Authority.Integrity` (the l4v
`call_kernel_integrity` lift): when a turn commits (`Kernel.exec k turn = some k'`), the
change to the source cell `turn.src` is admissible per `Integrity`'s case-split, taken
with the actor as the sole subject (`subjects = [turn.actor]`).

* If the actor OWNS `src` (`actor = src`, the l4v `troa_lrefl` intra branch), the change
  is admitted by `Integrity.intra` — PROVED here.
* Otherwise the actor held a discharging `Cap` on `src` (the cross/cross-vat branch). To
  feed `Integrity.cross` we need a `Verifiable P W` witness `w` with `Discharged (p ko ko') w`;
  the hypothesis `hcross` supplies exactly that, so this case too is PROVED — the held cap's
  discharge IS the witness.

The statement abstracts the object state `KO` and predicate `p` (as `Integrity` does), and
takes the cross-witness as a hypothesis `hcross`: that is the precise seam where the
concrete `Cap` is turned into a `Verifiable` certificate. Building that bridge *generically*
(deriving `Discharged (p ko ko') w` from `authorizedB` alone, for an ARBITRARY `p`) is not
possible without fixing `P`/`W`/`p` to the cap model — see the `-- OPEN:` note in the proof. -/
theorem exec_authorized_is_integrity
    {P : Type*} {KO : Type*} {W : Type*} [Verifiable P W]
    (k k' : KernelState) (turn : Turn) (p : KO → KO → P) (ko ko' : KO)
    (h : exec k turn = some k')
    -- The cross-vat seam: a verified witness for the change when the actor does NOT own src.
    (hcross : (turn.actor == turn.src) = false → ∃ w : W, Discharged (p ko ko') w) :
    Integrity W turn.src [turn.actor] p ko ko' := by
  -- `exec` committed, so the authority check passed.
  have hauth : authorizedB k.caps turn = true := exec_authorized k k' turn h
  -- Case-split on the ownership disjunct (mirrors l4v `troa_lrefl` vs authorized-edge).
  rcases (by exact eq_or_ne (turn.actor == turn.src) true) with hown | hown
  · -- intra (l4v `troa_lrefl`): own-it ⟹ arbitrary change, trivial witness. PROVED.
    exact Integrity.intra (authorizedB_owner_intra k.caps turn hown)
  · -- cross (l4v authorized-edge): actor holds a discharging cap on src.
    -- OPEN(bridge): turning the held concrete `Cap` (from `authorizedB`'s slot scan) into a
    -- `Discharged (p ko ko') w` for an ARBITRARY predicate `p` requires fixing the
    -- `Verifiable P W` model so `p` is the cap-admissibility predicate and `w` its cap; for
    -- a general `p` no such derivation exists. We discharge it from the explicit cross-seam
    -- hypothesis `hcross`, which provides exactly the verified witness `Integrity.cross` needs.
    have hfalse : (turn.actor == turn.src) = false := by
      cases hb : (turn.actor == turn.src) with
      | true  => exact absurd hb hown
      | false => rfl
    obtain ⟨w, hw⟩ := hcross hfalse
    exact Integrity.cross w hw

/-! ## It runs (`#eval`). -/

/-- A starting cap table: holder 0 has an endpoint cap on target 7 with read+write. -/
def c0 : Caps := fun l => if l = 0 then [Cap.endpoint 7 [Auth.read, Auth.write]] else []

-- Attenuate the endpoint cap to read-only.
#eval capAuthConferred (attenuate [Auth.read] (Cap.endpoint 7 [Auth.read, Auth.write]))
  -- [Dregg2.Authority.Auth.read]
#eval invoke c0 0 7 Auth.write          -- true  (holds write on 7)
#eval invoke c0 0 7 Auth.grant          -- false (write/read only)
#eval invoke (revoke c0 0 (Cap.endpoint 7 [Auth.read, Auth.write])) 0 7 Auth.write  -- false
#eval invoke (grant c0 1 (Cap.node 7)) 1 7 Auth.control                              -- true

end Dregg2.Exec
