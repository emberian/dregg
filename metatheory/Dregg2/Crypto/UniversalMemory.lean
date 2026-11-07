/-
# Dregg2.Crypto.UniversalMemory — ONE Blum multiset for ALL of dregg's state (the deepest collapse).

THE THESIS under test (.docs-history-noclaude/EPOCH-DESIGN.md tables → .docs-history-noclaude/CONVERGENT-CIRCUIT.md collapse): every
state access — register read/write, heap get/set, capability membership check, nullifier
insert/freshness — is a tuple in ONE memory multiset over a unified DOMAIN-TAGGED address space,
and the four map roots (cap_root, nullifier_root, heap_root, index root) are DERIVED boundary
views over the final memory cells. 5 tables → main + chip + range + ONE memory (+ the boundary
derivation absorbed into map-ops). The question this module answers: is that SOUND?

THE VERDICT (proved below): YES, with the boundary conditions named.

  * INTERIOR — `universal_memory_sound`: the ONE Blum balance (`MemoryChecking.memcheck_sound`)
    over the unified `Domain × κ` address space implies consistency of EVERY per-domain
    projection, each as a STANDALONE κ-addressed memory (`domTrace`/`stripOp`). One LogUp
    argument soundly covers registers + heap + caps + nullifiers + index. Zero per-access hashing.
    The combinatorial workhorses are `consistentFrom_filter` (consistency restricts to any
    address class — other-domain ops can't touch this domain's cells) and `consistentFrom_strip`
    (the tag peels off a single-domain trace injectively).
  * THE FINAL COLUMN IS PINNED — `memcheck_pins_final`: under the balance + discipline, the
    prover's claimed final value at every declared address IS the genuine fold of the trace
    (`chains_pin_fold`, the value-twin of `consistentFrom_of_chains`). So the boundary view
    derived from the final column is trustworthy, not prover-chosen.
  * BOUNDARY — `boundary_root_derived` / `boundary_root_from_memcheck`: the sorted-Poseidon2
    root of a domain's final memory cells (`boundaryCells`, the present-`some` cells in sorted
    address order) EQUALS today's map root whenever the map and the final memory have the same
    lookup semantics — by `Heap.root_deterministic`/`ext_get`, NO crypto. The derived view
    AGREES with the existing roots: a refactor, not a semantic change.
  * THE NULLIFIER WIN — `nullifier_fresh_sound`: intra-proof freshness IS a memory property:
    a read returning `none` at `(nullifiers, x)`, under the balance + the insert-only discipline,
    PROVES `x` absent from the proof's initial nullifier view AND never inserted earlier in the
    trace (no intra-proof double spend). NO Merkle path intra-proof. The composition
    `nullifier_fresh_binds_root` rides `Heap.root_injective`: the published root pins absence in
    ANY heap claiming it — cross-proof persistence lives entirely at the boundary.

What does NOT ride the memory multiset: move's conservation. The multiset argument is
PER-ADDRESS (rectangular); `Calculus/BiorthTensor.lean` proved conservation is NOT expressible
by any rectangular/per-component family (`conservation_not_behaviour_rectangular`) — Σδ=0 needs
the CORRELATED pair, so it stays an in-row paired-write constraint on the move row.

Non-vacuity, both polarities, on concrete multi-domain `(Domain × ℤ, Option ℤ)` traces:
the honest five-domain trace balances and every projection is consistent; a cross-domain
tuple-steal UNBALANCES (the tag makes domains disjoint sub-multisets); the flat UNTAGGED space
ALIASES (a cap check reads a nullifier's value — the tag is semantically load-bearing); the
intra-proof double-spend read is refused.

Axiom hygiene: `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} everywhere. Crypto
enters ONLY as a DECIDABLE PER-INSTANCE residual — `¬ Heap.HeapRootColl hash h₁ h₂`, "the deployed
sponge does not collide at the ONE pair `Heap.rootFind` names for these two heaps" — never as an
axiom, and (since 2026-08-01) no longer as the refuted `Poseidon2SpongeCR` floor this file used to
carry at five keystones. Lean/design only — no circuit Rust here.
-/
import Dregg2.Crypto.MemoryChecking
import Dregg2.Substrate.Heap
import Dregg2.Tactics

namespace Dregg2.Crypto.UniversalMemory

open Dregg2.Crypto.MemoryChecking
open Dregg2.Substrate
open Dregg2.Substrate.Heap (FeltHeap)

universe u v

/-! ## §1 — the unified address space: one memory, domain-tagged.

The five state structures become five DOMAINS of one address space. An address is
`(domain, key)`; the deployment realization is `addr = hash[domain_tag, collection_id, key]`
(injective under the same sponge-CR floor as everything else — the tag here is the abstract
content of that hashing). Domains are DISJOINT sub-multisets by construction: a tuple written in
one domain can never cancel a claim in another (`Entry` equality requires address equality). -/

/-- The state domains of the unified memory: the five COMMITTED collections of
`EPOCH-DESIGN.md`'s commitment layout (registers · heap · capabilities · nullifiers · receipt
index), plus the transient `working` scratch. A future state component is a NEW domain value,
never a new table.

`working` is the universal-memory realization of the Rust `UDomain::Working`
(`turn/src/umem.rs:118`): a service cell's / the interpreter's / a long-running effect's
TRANSIENT scratch. It rides the ONE memcheck trace exactly like every other domain — so it is
consistent for free (`universal_memory_sound` quantifies over it like any `d`) and its cells
get their OWN non-aliasing address class by the same tag isolation (`consistentFrom_filter`).
But, exactly like `registers`, it is DESIGNED to publish NO committed boundary: it is never
projected into the state commitment (`working_commitment_inert` below makes "never projected ⇒
inert" a theorem, not a Rust `debug_assert`). Its boundary IS derivable on demand
(`working_umem_root`, the §4 checkpoint, and the level-1 image of `recursive_open_sound`),
it simply never enters consensus state. -/
inductive Domain : Type where
  | registers
  | heap
  | caps
  | nullifiers
  | index
  | working
deriving DecidableEq, Repr

/-- The unified address: a domain tag paired with the in-domain key. The abstract form of the
deployed `addr = hash[domain_tag, collection_id, key]` (CR makes the concrete form injective,
i.e. exactly this pair). -/
abbrev UAddr (κ : Type u) : Type u := Domain × κ

variable {κ : Type u} {ν : Type v}

/-- The domain projection of a unified trace: the ops touching domain `d`, in trace order. -/
def domTrace (d : Domain) (tr : List (Op (UAddr κ) ν)) : List (Op (UAddr κ) ν) :=
  tr.filter fun op => decide (op.addr.1 = d)

/-- Strip the domain tag off an op (used on single-domain traces, where the tag is constant —
the projection becomes a STANDALONE κ-addressed memory trace). -/
def stripOp (op : Op (UAddr κ) ν) : Op κ ν :=
  ⟨op.kind, op.addr.2, op.val, op.prevVal, op.prevSerial⟩

@[simp] theorem stripOp_kind (op : Op (UAddr κ) ν) : (stripOp op).kind = op.kind := rfl
@[simp] theorem stripOp_addr (op : Op (UAddr κ) ν) : (stripOp op).addr = op.addr.2 := rfl

/-! ## §2 — THE KEYSTONE: one balance covers every domain.

`memcheck_sound` gives consistency of the WHOLE unified trace. The two lemmas below push that
to every projection: `consistentFrom_filter` (general — consistency restricts to any address
class, because ops outside the class never move the class's cells) and `consistentFrom_strip`
(on a single-domain trace the tag peels off). Together: ONE multiset-balance argument is a sound
memory argument for registers, heap, caps, nullifiers, and the index SIMULTANEOUSLY. -/

section Projection

variable {Addr : Type u} {Val : Type v} [DecidableEq Addr]

/-- **Consistency restricts to every address class.** If a trace is consistent from `m`, the
sub-trace of ops whose address satisfies `p` is consistent from any memory agreeing with `m` on
the class: dropped ops only write OUTSIDE the class, so the class's cells evolve identically.
(The projection half of the keystone — pure semantics, no multisets needed.) -/
theorem consistentFrom_filter (p : Addr → Bool) {tr : List (Op Addr Val)} :
    ∀ {m m' : Addr → Val},
      (∀ a, p a = true → m' a = m a) →
      ConsistentFrom m tr →
      ConsistentFrom m' (tr.filter fun op => p op.addr) := by
  induction tr with
  | nil => intro m m' _ _; exact trivial
  | cons op tr ih =>
    intro m m' hagree hcons
    obtain ⟨hread, hrest⟩ := hcons
    by_cases hp : p op.addr = true
    · rw [List.filter_cons, if_pos (by simpa using hp)]
      refine ⟨fun hk => (hread hk).trans (hagree _ hp).symm, ?_⟩
      refine ih (m := step m op) (m' := step m' op) ?_ hrest
      intro a hpa
      by_cases hc : op.kind = .write ∧ a = op.addr
      · rw [step, step, if_pos hc, if_pos hc]
      · rw [step, step, if_neg hc, if_neg hc]
        exact hagree a hpa
    · rw [List.filter_cons, if_neg (by simpa using hp)]
      refine ih (m := step m op) (m' := m') ?_ hrest
      intro a hpa
      have hne : a ≠ op.addr := fun h => hp (h ▸ hpa)
      rw [step_other hne]
      exact hagree a hpa

end Projection

section Strip

variable [DecidableEq κ]

/-- **The tag peels off a single-domain trace.** A consistent trace all of whose addresses live
in domain `d` is, stripped, a consistent STANDALONE κ-addressed memory trace (from the domain-`d`
slice of the initial memory). The tag-injectivity `(d, a) = (d, b) ↔ a = b` is the whole
content. -/
theorem consistentFrom_strip (d : Domain) {tr : List (Op (UAddr κ) ν)} :
    ∀ {m : UAddr κ → ν} {m' : κ → ν},
      (∀ op ∈ tr, op.addr.1 = d) →
      (∀ a, m' a = m (d, a)) →
      ConsistentFrom m tr → ConsistentFrom m' (tr.map stripOp) := by
  induction tr with
  | nil => intro m m' _ _ _; exact trivial
  | cons op tr ih =>
    intro m m' hdom hagree hcons
    obtain ⟨hread, hrest⟩ := hcons
    have hd : op.addr = (d, op.addr.2) := by
      have h1 : op.addr.1 = d := hdom op (List.mem_cons_self ..)
      exact Prod.ext h1 rfl
    refine ⟨?_, ?_⟩
    · intro hk
      rw [stripOp_addr, hagree]
      exact (hread hk).trans (congrArg m hd)
    · refine ih (m := step m op) (m' := step m' (stripOp op))
        (fun o ho => hdom o (List.mem_cons_of_mem _ ho)) ?_ hrest
      intro a
      by_cases hk : op.kind = .write
      · by_cases ha : a = op.addr.2
        · subst ha
          rw [show step m' (stripOp op) op.addr.2 = op.val by
                exact step_write (op := stripOp op) hk m',
              show step m op (d, op.addr.2) = op.val by
                rw [← hd]; exact step_write hk m]
        · rw [step_other (op := stripOp op) (by simpa using ha) m',
              step_other (op := op) (by rw [hd]; simp [Prod.ext_iff, ha]) m]
          exact hagree a
      · have hkr : op.kind = .read := by
          cases hop : op.kind with
          | read => rfl
          | write => exact absurd hop hk
        rw [step_read (op := stripOp op) (by simpa using hkr) m',
            step_read hkr m]
        exact hagree a

/-- **`universal_memory_sound` — THE KEYSTONE.** ONE Blum multiset balance over the unified
domain-tagged address space soundly covers EVERY state structure: the whole trace is consistent,
AND each domain's projection — stripped to a standalone κ-addressed memory — is consistent from
that domain's slice of the initial memory. Registers, heap ops, cap checks, nullifier touches,
index appends: one memory argument, zero intra-proof hashing. -/
theorem universal_memory_sound
    {init : UAddr κ → ν} {fin : UAddr κ → ν × Nat}
    {addrs : List (UAddr κ)} {tr : List (Op (UAddr κ) ν)}
    (hnd : addrs.Nodup) (hcl : ∀ op ∈ tr, op.addr ∈ addrs)
    (hdisc : Disciplined tr) (hmc : MemCheck init fin addrs tr) :
    Consistent init tr ∧
      ∀ d : Domain,
        Consistent (fun a => init (d, a)) ((domTrace d tr).map stripOp) := by
  have hcons : Consistent init tr := memcheck_sound hnd hcl hdisc hmc
  refine ⟨hcons, fun d => ?_⟩
  have hfil : ConsistentFrom init (tr.filter fun op => decide (op.addr.1 = d)) :=
    consistentFrom_filter (fun a => decide (a.1 = d)) (fun _ _ => rfl) hcons
  show Consistent (fun a => init (d, a))
    ((tr.filter fun op => decide (op.addr.1 = d)).map stripOp)
  exact consistentFrom_strip d
    (fun op hop => of_decide_eq_true (List.mem_filter.mp hop).2)
    (fun _ => rfl) hfil

/-- **Single-cell universal soundness — the cohort-specialized single-row boundary.** With at most
ONE declared `(domain, key)` address the `Nodup` hypothesis `universal_memory_sound` stands on is
free (`List.nodup_singleton`), so the inter-row lexicographic comparator the general universal
boundary uses to establish it is VACUOUS and the keystone still gives the whole-trace consistency
AND every domain projection's consistency. This is the soundness obligation of the width-9
`Ir2Air::UMemBoundaryCohort` AIR (the welded single-domain leg): it drops the comparator columns
because at most one row exists, and Nodup follows from the row being alone — not from any
in-circuit comparison. -/
theorem universal_memory_sound_single
    {init : UAddr κ → ν} {fin : UAddr κ → ν × Nat}
    {a : UAddr κ} {tr : List (Op (UAddr κ) ν)}
    (hcl : ∀ op ∈ tr, op.addr ∈ [a])
    (hdisc : Disciplined tr) (hmc : MemCheck init fin [a] tr) :
    Consistent init tr ∧
      ∀ d : Domain,
        Consistent (fun a => init (d, a)) ((domTrace d tr).map stripOp) :=
  universal_memory_sound (List.nodup_singleton a) hcl hdisc hmc

end Strip

/-! ## §3 — the final column is PINNED (the boundary view is trustworthy).

The boundary derivation reads the prover's claimed final tuples (`fin`). For the derived root to
mean anything, those claims must be FORCED. They are: under the balance + discipline, every
declared address's final claim equals the genuine fold of the trace — the value-twin of
`consistentFrom_of_chains`, threading the same per-address chain invariant. -/

section FinalPin

variable {Addr : Type u} {Val : Type v} [DecidableEq Addr]

/-- Per-address predecessor chains + the read echo pin each FINAL claim's value to the real fold
semantics (the same threading as `MemoryChecking.consistentFrom_of_chains`, concluding in the
value world instead of the consistency world). -/
theorem chains_pin_fold {tr : List (Op Addr Val)} :
    ∀ {n : Nat} {m : Addr → Val} {cur fin : Addr → Entry Addr Val},
      (∀ op ∈ tr, op.kind = .read → op.val = op.prevVal) →
      (∀ a, Chained (cur a) (opsAt a n tr) (fin a)) →
      (∀ a, (cur a).val = m a) →
      ∀ a, (fin a).val = (tr.foldl step m) a := by
  induction tr with
  | nil =>
    intro n m cur fin _ hchain hval a
    have h := hchain a
    rw [opsAt_nil, chained_nil] at h
    rw [List.foldl_nil, h]
    exact hval a
  | cons op tr ih =>
    intro n m cur fin hecho hchain hval a
    have hopc := hchain op.addr
    rw [opsAt_cons_pos rfl] at hopc
    obtain ⟨hr, hrest⟩ := hopc
    rw [List.foldl_cons]
    apply ih (n := n + 1) (m := step m op)
      (cur := fun b => if b = op.addr then writeEntry op n else cur b) (fin := fin)
    · exact fun op' h hk => hecho op' (List.mem_cons_of_mem _ h) hk
    · intro b
      by_cases hb : b = op.addr
      · subst hb
        rw [if_pos rfl]
        exact hrest
      · rw [if_neg hb]
        have h := hchain b
        rwa [opsAt_cons_neg (fun h' => hb h'.symm)] at h
    · intro b
      by_cases hb : b = op.addr
      · subst hb
        rw [if_pos rfl]
        show op.val = step m op op.addr
        cases hk : op.kind with
        | read =>
          rw [step_read hk]
          have hprev : op.prevVal = m op.addr := by
            have hv := congrArg Entry.val hr
            simp only [readEntry] at hv
            rw [hv, hval op.addr]
          exact (hecho op (List.mem_cons_self ..) hk).trans hprev
        | write => rw [step_write hk]
      · rw [if_neg hb, step_other hb]
        exact hval b

/-- **`memcheck_pins_final`** — under the ONE balance, the prover's claimed final value at every
declared address IS the genuine final memory (the fold of the trace). The final column the
boundary roots are derived from is forced, not chosen. -/
theorem memcheck_pins_final {init : Addr → Val} {fin : Addr → Val × Nat}
    {addrs : List Addr} {tr : List (Op Addr Val)}
    (hnd : addrs.Nodup) (hcl : ∀ op ∈ tr, op.addr ∈ addrs)
    (hdisc : Disciplined tr) (hmc : MemCheck init fin addrs tr) :
    ∀ a ∈ addrs, (fin a).1 = (tr.foldl step init) a := by
  intro a ha
  have h := chains_pin_fold (n := 0) (m := init) (cur := fun b => initEntry init b)
    (fin := fun b => if b ∈ addrs then finEntry fin b else initEntry init b)
    (disciplined_echo hdisc)
    (fun b => by
      show Chained (initEntry init b) (opsAt b 0 tr)
        (if b ∈ addrs then finEntry fin b else initEntry init b)
      by_cases hb : b ∈ addrs
      · rw [if_pos hb]
        exact per_address_chain hnd hdisc hmc hb
      · rw [if_neg hb, opsAt_nil_of_closure hb hcl]
        exact rfl)
    (fun _ => rfl) a
  rw [if_pos ha] at h
  simp only [finEntry] at h
  exact h

end FinalPin

/-! ## §4 — the BOUNDARY derivation: the map roots are views over the final memory cells.

A map domain stores `Option ν` values: `some v` = present cell, `none` = absent. The derived
boundary view of a domain is `boundaryCells`: the present cells of the declared addresses, in
sorted address order — exactly a sorted leaf list in `Substrate/Heap.lean`'s sense. The
derivation theorem: today's map root (`Heap.root` of the cap/nullifier/heap leaf list) EQUALS
the root of the derived view whenever the two have the same lookup semantics — by canonicity
(`ext_get` / `root_deterministic`), NO crypto. So materializing the roots only at the boundary
is a refactor of WHERE the commitment is computed, not of WHAT it commits to. -/

section Boundary

variable [LinearOrder κ]

/-- The derived boundary view of a domain: the PRESENT (`some`) final cells over the declared
address list, in declared order. On a sorted declared list this is a sorted leaf list — the
exact thing `Heap.root` sponges. -/
def boundaryCells (fin' : κ → Option ν) : List κ → List (κ × ν)
  | [] => []
  | a :: as =>
    match fin' a with
    | some v => (a, v) :: boundaryCells fin' as
    | none => boundaryCells fin' as

omit [LinearOrder κ] in
/-- A derived-view key comes from the declared address list. -/
theorem mem_keys_boundaryCells {fin' : κ → Option ν} :
    ∀ {as : List κ} {x : κ}, x ∈ Heap.keys (boundaryCells fin' as) → x ∈ as := by
  intro as
  induction as with
  | nil => intro x hx; simp [boundaryCells, Heap.keys] at hx
  | cons a as ih =>
    intro x
    simp only [boundaryCells]
    cases hfa : fin' a with
    | some v =>
      show x ∈ Heap.keys ((a, v) :: boundaryCells fin' as) → _
      intro hx
      rw [Heap.keys_cons] at hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih hx')
    | none =>
      show x ∈ Heap.keys (boundaryCells fin' as) → _
      intro hx
      exact List.mem_cons_of_mem _ (ih hx)

/-- The derived view of a sorted declared list satisfies the heap invariant (sorted keys) —
it IS a well-formed openable map. -/
theorem boundaryCells_sorted {fin' : κ → Option ν} :
    ∀ {as : List κ}, as.Pairwise (· < ·) → Heap.SortedKeys (boundaryCells fin' as) := by
  intro as
  induction as with
  | nil => intro _; simp [boundaryCells, Heap.SortedKeys, Heap.keys]
  | cons a as ih =>
    intro hp
    obtain ⟨hlt, hrest⟩ := List.pairwise_cons.mp hp
    simp only [boundaryCells]
    cases hfa : fin' a with
    | some v =>
      show Heap.SortedKeys ((a, v) :: boundaryCells fin' as)
      exact List.pairwise_cons.mpr
        ⟨fun x hx => hlt x (mem_keys_boundaryCells hx), ih hrest⟩
    | none =>
      show Heap.SortedKeys (boundaryCells fin' as)
      exact ih hrest

/-- The derived view's lookup semantics: `get` returns the final memory value on declared
addresses and `none` off them. (The characterization `boundary_root_derived` matches against.) -/
theorem get_boundaryCells {fin' : κ → Option ν} :
    ∀ {as : List κ}, as.Pairwise (· < ·) →
      ∀ a, Heap.get (boundaryCells fin' as) a = if a ∈ as then fin' a else none := by
  intro as
  induction as with
  | nil => intro _ a; simp [boundaryCells]
  | cons a' as ih =>
    intro hp a
    obtain ⟨hlt, hrest⟩ := List.pairwise_cons.mp hp
    have hcons_iff : a ∈ a' :: as ↔ a = a' ∨ a ∈ as := List.mem_cons
    simp only [boundaryCells]
    cases hfa : fin' a' with
    | some v =>
      show Heap.get ((a', v) :: boundaryCells fin' as) a = _
      by_cases ha : a = a'
      · subst ha
        rw [Heap.get_cons_self, if_pos (List.mem_cons_self ..), hfa]
      · rw [Heap.get_cons_ne _ _ ha, ih hrest a]
        by_cases hmem : a ∈ as
        · rw [if_pos hmem, if_pos (List.mem_cons_of_mem _ hmem)]
        · rw [if_neg hmem,
            if_neg (fun h => (List.mem_cons.mp h).elim ha hmem)]
    | none =>
      show Heap.get (boundaryCells fin' as) a = _
      by_cases ha : a = a'
      · subst ha
        rw [if_pos (List.mem_cons_self ..), hfa, Heap.get_eq_none_iff]
        intro hk
        exact lt_irrefl a (hlt a (mem_keys_boundaryCells hk))
      · rw [ih hrest a]
        by_cases hmem : a ∈ as
        · rw [if_pos hmem, if_pos (List.mem_cons_of_mem _ hmem)]
        · rw [if_neg hmem,
            if_neg (fun h => (List.mem_cons.mp h).elim ha hmem)]

end Boundary

/-- **`boundary_root_derived` — the map roots are DERIVED views (the refactor theorem).** If
today's committed map `h` (the cap/nullifier/heap sorted leaf list) and the final memory's
domain view agree as lookups — `h` holds exactly the declared addresses' final values, nothing
else — then today's root EQUALS the root of the derived boundary view. Pure canonicity
(`Heap.root_deterministic` riding `ext_get`): the root is a function of the map's MEANING, and
the meanings coincide. NO crypto hypothesis. Materializing roots at the boundary changes WHERE
the commitment is computed, not WHAT it commits to. -/
theorem boundary_root_derived (hash : List ℤ → ℤ) {h : FeltHeap}
    {fin' : ℤ → Option ℤ} {as : List ℤ}
    (hs : Heap.SortedKeys h) (has : as.Pairwise (· < ·))
    (hsem : ∀ a, Heap.get h a = if a ∈ as then fin' a else none) :
    Heap.root hash h = Heap.root hash (boundaryCells fin' as) :=
  Heap.root_deterministic hash hs (boundaryCells_sorted has)
    (fun k => (hsem k).trans (get_boundaryCells has k).symm)

/-- **`boundary_root_from_memcheck` — the boundary derivation, welded to the ONE balance.** The
derived boundary root computed from the prover's claimed final column equals today's map root
computed from the GENUINE post-state — because `memcheck_pins_final` forces the claims to the
real fold. One Blum balance + canonicity: the per-domain commitment at the proof's edge is
exactly the commitment the maps carry today. -/
theorem boundary_root_from_memcheck (hash : List ℤ → ℤ) (d : Domain)
    {init : UAddr ℤ → Option ℤ} {fin : UAddr ℤ → Option ℤ × Nat}
    {addrs : List (UAddr ℤ)} {tr : List (Op (UAddr ℤ) (Option ℤ))}
    {h : FeltHeap} {as : List ℤ}
    (hnd : addrs.Nodup) (hcl : ∀ op ∈ tr, op.addr ∈ addrs)
    (hdisc : Disciplined tr) (hmc : MemCheck init fin addrs tr)
    (hs : Heap.SortedKeys h) (has : as.Pairwise (· < ·))
    (hda : ∀ a ∈ as, (d, a) ∈ addrs)
    (hsem : ∀ a : ℤ, Heap.get h a
      = if a ∈ as then (tr.foldl step init) (d, a) else none) :
    Heap.root hash h = Heap.root hash (boundaryCells (fun a => (fin (d, a)).1) as) := by
  refine boundary_root_derived hash hs has (fun a => ?_)
  rw [hsem a]
  by_cases ha : a ∈ as
  · rw [if_pos ha, if_pos ha,
      memcheck_pins_final hnd hcl hdisc hmc (d, a) (hda a ha)]
  · rw [if_neg ha, if_neg ha]

/-! ### §4b — the INIT boundary is BOUND to committed PRE-state (the PI-v3 ride-along anchor).

The FINAL boundary derivation (`boundary_root_from_memcheck`) shows the prover's *post*-state
boundary view commits to the same object the deployed map roots commit to. Its mirror image is
what makes the universal boundary's INIT column TRUSTWORTHY rather than free-witnessed: the
boundary's declared init image must EQUAL the committed PRE-state, not be prover-chosen.

`boundary_init_root_derived` is exactly `boundary_root_derived` instantiated at `fin' = init`
(the init image is the GIVEN, so no memcheck pinning is needed — it is even simpler than the
final side). Welded to the circuit by pinning the computed boundary-init root to a committed
pre-state map root supplied as a public input, this is the soundness theorem behind the
in-circuit init binding: absent a sponge collision at the named pair (`Heap.root_injective`),
a boundary whose init image differs from the committed pre-state produces a DIFFERENT
sorted-Poseidon2 leaf list, hence a different root, hence the pin REFUSES. The bound boundary
init root = the committed map root, by canonicity, NO crypto in the derivation itself
(the CR floor enters only at the injectivity tooth, exactly as on the final side). -/
theorem boundary_init_root_derived (hash : List ℤ → ℤ) {h : FeltHeap}
    {init : ℤ → Option ℤ} {as : List ℤ}
    (hs : Heap.SortedKeys h) (has : as.Pairwise (· < ·))
    (hsem : ∀ a, Heap.get h a = if a ∈ as then init a else none) :
    Heap.root hash h = Heap.root hash (boundaryCells init as) :=
  boundary_root_derived hash hs has hsem

/-- **`boundary_init_root_bound` — the binding is sound (the anti-forgery tooth).** A committed
pre-state map `hcommitted` and the prover's declared init heap `hdeclared` carrying the SAME root
ARE the same map. So pinning the boundary-init root to the committed root forces the declared init
heap to be the committed pre-state — a tampered init image CANNOT keep the published root. The
init-side companion of `nullifier_fresh_binds_root`.

⚑ **PORTED OFF `Poseidon2SpongeCR` (2026-08-01).** The floor is FALSE at deployed BabyBear
(`Circuit.HashFloorHonesty.poseidon2SpongeCR_false_babyBear`), so this statement said nothing about
the deployed prover. What it assumes now is `Heap.root_injective`'s own per-instance residual: the
deployed sponge does NOT collide at the ONE pair `Heap.rootFind` returns for THESE two heaps.
Decidable, dischargeable by the honest committer with no cryptographic assumption at all
(`Heap.heapRootColl_dischargeable`, when the two heaps coincide), refutable at the constant sponge
(`Heap.heapRootColl_refutable`) — and it REFUTES the old premise outright
(`Heap.heapRootColl_refutes_poseidon2CR`), so this is strictly STRONGER with an unchanged
conclusion. A caller still holding the floor rewires through the tree's UNIVERSAL bridge
`Poseidon2Binding.spongeColl_refutable_of_injective _ hCR _` — no per-site `_of_CR` twin. -/
theorem boundary_init_root_bound (hash : List ℤ → ℤ)
    {hcommitted hdeclared : FeltHeap}
    (hno : ¬ Heap.HeapRootColl hash hdeclared hcommitted)
    (hroot : Heap.root hash hdeclared = Heap.root hash hcommitted) :
    hdeclared = hcommitted :=
  Heap.root_injective hash hno hroot

/-- **THE FLOOR-FREE DICHOTOMY behind `boundary_init_root_bound`** — NO hypothesis on `hash` at
all, so unlike the pre-cutover form it is TRUE at deployed BabyBear parameters. A declared init
image publishing the committed root either IS the committed pre-state, or the equivocation is a
GENUINE collision of the deployed sponge at the pair `Heap.rootFind` hands back. This is the
theorem the keystone is a `.resolve_right` of; it is stated so the boundary cone has the
dichotomy locally and no consumer has to reach for the floor to get one. -/
theorem boundary_init_root_binds_or_collides (hash : List ℤ → ℤ)
    {hcommitted hdeclared : FeltHeap}
    (hroot : Heap.root hash hdeclared = Heap.root hash hcommitted) :
    hdeclared = hcommitted ∨ Heap.HeapRootColl hash hdeclared hcommitted :=
  Heap.root_binds_or_collides hash hroot

/-! ### §4c — the WHOLE-IMAGE boundary equality (the no-extra-cells direction).

`boundary_init_root_bound` proves the binding REFUSES a tampered declared heap. §4b's per-cell
realization (the deployed cross-cell-read, `satisfied2U_init_root`) proves only the SUBSET view:
each TOUCHED address `(d, a)` with `a ∈ as` opens to its declared value under the committed root.
That is sound for "this peer field IS the committed value" but it does NOT, on its own, forbid a
committed heap that holds the declared cells AND EXTRA cells the boundary never declared.

This section closes the no-extra-cells direction at the Lean level, by the route the in-circuit
WHOLE-boundary root-fold realizes: recompute the sorted-Poseidon2 root of the ENTIRE declared
boundary image `boundaryCells init as` and PIN it to the committed pre-state root. That single
pin, via `root_injective`, forces the committed heap to BE the boundary view — so the committed
heap's lookup semantics is EXACTLY the declared image: present-and-declared cells carry their
declared value, and EVERY address off the declared list is ABSENT in the committed heap (no
extra cells, no hidden cell). The two directions stated separately:
  * `boundary_image_eq_of_root` — the committed heap equals the boundary view (the leaf-list
    equality `root_injective` yields, the structural anti-ghost);
  * `boundary_whole_image_sem` — its consequence in lookup terms: the committed heap agrees with
    the declared image at EVERY address, INCLUDING absence off the declared list.

NO new crypto: the residual enters once, exactly as in `boundary_init_root_bound`. This is the
SAME `Heap.HeapRootColl` tooth, applied to the whole-image fold instead of a per-cell opening.
The deferred work is entirely the in-circuit AIR that COMPUTES `Heap.root hash (boundaryCells
…)` over the universal boundary table and pins it to the committed-root public input; that fold
rides the universal-map rotation (it needs the rotation's per-domain sorted-leaf fold chip). The
Lean obligation it must discharge is precisely the hypothesis `hpin` below. -/

/-- **`boundary_image_eq_of_root` — the committed heap IS the boundary view (no extra cells).**
If the committed pre-state heap `hcommitted` carries the SAME root as the sorted-Poseidon2 fold
of the ENTIRE declared boundary image `boundaryCells init as`, then — absent a sponge collision at
the ONE pair `Heap.rootFind` names for this pin (`hno`, the per-instance residual that replaced the
refuted `Poseidon2SpongeCR` floor here on 2026-08-01) — the
committed heap EQUALS that boundary view as a leaf list. This is the structural no-extra-cells
fact: the committed heap can hold NOTHING the boundary did not declare, because a single extra
or altered leaf moves the root. The whole-image companion of `boundary_init_root_bound`, against
the recomputed fold rather than a separately-declared heap. -/
theorem boundary_image_eq_of_root (hash : List ℤ → ℤ)
    {hcommitted : FeltHeap} {init : ℤ → Option ℤ} {as : List ℤ}
    (hno : ¬ Heap.HeapRootColl hash hcommitted (boundaryCells init as))
    (hpin : Heap.root hash hcommitted = Heap.root hash (boundaryCells init as)) :
    hcommitted = boundaryCells init as :=
  Heap.root_injective hash hno hpin

/-- **`boundary_whole_image_sem` — the committed heap agrees with the declared image EVERYWHERE.**
The lookup-world consequence of `boundary_image_eq_of_root`: on the same per-instance residual,
pinning the
committed pre-state root to the whole-boundary fold forces the committed heap's `get` to equal
the declared image at EVERY address — declared cells open to their declared value, and every
address OFF the declared list is absent. This is the full whole-image equality `hsem` that the
per-cell subset realization (`satisfied2U_init_root`'s hypothesis) had to ASSUME: here it is
DERIVED from the single whole-boundary root pin, with the no-extra-cells direction included.
(`as` sorted is needed for the boundary view to be the canonical sorted leaf list it folds as.) -/
theorem boundary_whole_image_sem (hash : List ℤ → ℤ)
    {hcommitted : FeltHeap} {init : ℤ → Option ℤ} {as : List ℤ}
    (has : as.Pairwise (· < ·))
    (hno : ¬ Heap.HeapRootColl hash hcommitted (boundaryCells init as))
    (hpin : Heap.root hash hcommitted = Heap.root hash (boundaryCells init as)) :
    ∀ a, Heap.get hcommitted a = if a ∈ as then init a else none := by
  intro a
  rw [boundary_image_eq_of_root hash hno hpin]
  exact get_boundaryCells has a

/-! ### §4d — the WORKING domain is INERT in the commitment (never-projected ⇒ a theorem).

The Rust `UDomain::Working` (`turn/src/umem.rs:118`) is transient scratch: it rides the ONE
memcheck trace (consistent for free) but is NEVER emitted by `project_cell`/`project_ledger`/
`project_executor_state`, so its boundary root never enters the state commitment. That guarantee
was load-bearing only by the Rust FACT that the projection happens to never construct a
`UKey::Working` — a `debug_assert_no_working` comment (`turn/src/umem.rs:347`), not a checked
property.

`working_commitment_inert` makes it a THEOREM, by the same tag-disjointness that powers the whole
module: the committed boundary view of ANY committed domain `d ≠ working` reads `fin` ONLY at the
addresses `(d, a)` — addresses whose tag is `d`, never `working`. So two final memories that
agree everywhere OFF the working domain (the only place a working write can differ) derive the
IDENTICAL committed boundary view. A working address therefore cannot move any committed
boundary: it is inert in the state commitment, exactly as `registers` is. -/

/-- **`working_commitment_inert` — A WORKING ADDRESS NEVER ENTERS A COMMITTED BOUNDARY.** For any
committed domain `d` (`d ≠ working`), two final memories that AGREE everywhere off the working
domain produce the SAME committed boundary view. Working writes — the only cells where the two
can differ — leave every committed domain's boundary untouched, because that boundary reads `fin`
only at tag-`d` addresses (never tag-`working`). The "never projected ⇒ inert" Rust invariant,
made a theorem by tag-disjointness (the dual of `consistentFrom_filter`'s class isolation). -/
theorem working_commitment_inert {d : Domain} (hd : d ≠ Domain.working)
    {fin₁ fin₂ : UAddr κ → Option ν} {as : List κ}
    (hagree : ∀ a : UAddr κ, a.1 ≠ Domain.working → fin₁ a = fin₂ a) :
    boundaryCells (fun a => fin₁ (d, a)) as = boundaryCells (fun a => fin₂ (d, a)) as := by
  have hfun : (fun a => fin₁ (d, a)) = (fun a => fin₂ (d, a)) := by
    funext a; exact hagree (d, a) hd
  rw [hfun]

/-- **`working_commitment_root_inert` — the committed boundary ROOT is inert to working cells.**
The sorted-Poseidon2 root of a committed domain's boundary is INVARIANT under any change confined
to the working domain (the value-world consequence of `working_commitment_inert`, by `congrArg`).
A working umem cannot perturb a single committed map root — it costs nothing on the consensus
path, regardless of how much working scratch a service writes. -/
theorem working_commitment_root_inert (hash : List ℤ → ℤ) {d : Domain} (hd : d ≠ Domain.working)
    {fin₁ fin₂ : UAddr ℤ → Option ℤ} {as : List ℤ}
    (hagree : ∀ a : UAddr ℤ, a.1 ≠ Domain.working → fin₁ a = fin₂ a) :
    Heap.root hash (boundaryCells (fun a => fin₁ (d, a)) as)
      = Heap.root hash (boundaryCells (fun a => fin₂ (d, a)) as) :=
  congrArg (Heap.root hash) (working_commitment_inert hd hagree)

/-! ### §4e — COMPOSABLE umems: the recursive open is TWO binds at DISJOINT levels.

A `UVal::UmemRef` (`turn/src/umem.rs:316`) makes one umem hold, at a key, the committed root of
ANOTHER umem. Reading "through" the ref is `open_through_umem_ref` (`turn/src/umem.rs:716`): bind
the OUTER service umem's committed boundary (the `working` domain) as an init image, read the
child root it names there, then bind THAT root as the INNER cell heap's (the `heap` domain) init
image and open the requested key. Two independent `boundary_init_root_bound` applications — the
keystone composed with itself.

The two levels CANNOT alias: the outer cells live in the `working` domain and the inner cells in
the `heap` domain, disjoint by tag. `recursive_levels_disjoint` makes that disjointness a theorem
(the two domain projections of ONE consistent trace are INDEPENDENT standalone memories,
`universal_memory_sound` at `working` and at `heap`); `recursive_open_sound` is the two-level bind
itself. A tamper at either level derives a different sorted-Poseidon2 root and the matching pin
refuses — soundness compositional for free. -/

/-- **`recursive_levels_disjoint` — the outer (working) and inner (heap) levels are independent.**
From ONE Blum balance, the outer service umem (`working` domain) and the inner cell heap (`heap`
domain) project to INDEPENDENT consistent standalone memories: a working op never moves a heap
cell and vice versa (tag isolation, two instances of `universal_memory_sound`). So the two
`boundary_init_root_bound` applications in `recursive_open_sound` bind genuinely independent
images — no cross-level aliasing. -/
theorem recursive_levels_disjoint [DecidableEq κ]
    {init : UAddr κ → ν} {fin : UAddr κ → ν × Nat}
    {addrs : List (UAddr κ)} {tr : List (Op (UAddr κ) ν)}
    (hnd : addrs.Nodup) (hcl : ∀ op ∈ tr, op.addr ∈ addrs)
    (hdisc : Disciplined tr) (hmc : MemCheck init fin addrs tr) :
    Consistent (fun a => init (Domain.working, a))
        ((domTrace Domain.working tr).map stripOp) ∧
      Consistent (fun a => init (Domain.heap, a))
        ((domTrace Domain.heap tr).map stripOp) :=
  let h := (universal_memory_sound hnd hcl hdisc hmc).2
  ⟨h Domain.working, h Domain.heap⟩

/-- **`recursive_open_sound` — THE COMPOSABLE-UMEM RECURSIVE OPEN (Stage D).** The Rust
`open_through_umem_ref` two-level bind made a theorem: `boundary_init_root_bound` applied at TWO
levels.
  * LEVEL 1 — the outer service umem's declared image carries the committed boundary root
    (`houter`) ⟹ absent an outer-level collision the declared OUTER image IS the committed
    working umem (`outerDeclared = outerCommitted`).
  * the bound outer umem NAMES `childRoot` at the ref address (`hnames`, the `UmemRef` cell), and
    that named root IS the genuine inner umem's committed root (`hchildRoot`).
  * LEVEL 2 — the declared inner heap is pinned to the named child root (`hchild`) ⟹ absent an
    inner-level collision the declared INNER image IS the committed child heap
    (`childDeclared = childCommitted`).
Two independent `boundary_init_root_bound` teeth; the levels are tag-disjoint
(`recursive_levels_disjoint`), so they cannot forge each other. The conclusion also re-exposes the
named child root through the (now-forced) outer DECLARED image — what the reader actually holds.

⚑ **PORTED OFF `Poseidon2SpongeCR` (2026-08-01).** The two levels now carry TWO SEPARATE
per-instance residuals — `hnoOuter` at the outer pair and `hnoInner` at the inner pair — which is
strictly more informative than the single floor binder they replace: the composition's crypto
reliance is visibly two independent events at two named pairs, not one global assumption reused.
Both are decidable and both are dischargeable by an honest committer at that level
(`Heap.heapRootColl_dischargeable`). A caller still holding the floor supplies each with
`Poseidon2Binding.spongeColl_refutable_of_injective _ hCR _`. -/
theorem recursive_open_sound (hash : List ℤ → ℤ)
    {outerCommitted outerDeclared childCommitted childDeclared : FeltHeap}
    {refKey childRoot : ℤ}
    (hnoOuter : ¬ Heap.HeapRootColl hash outerDeclared outerCommitted)
    (hnoInner : ¬ Heap.HeapRootColl hash childDeclared childCommitted)
    (houter : Heap.root hash outerDeclared = Heap.root hash outerCommitted)
    (hnames : Heap.get outerCommitted refKey = some childRoot)
    (hchildRoot : Heap.root hash childCommitted = childRoot)
    (hchild : Heap.root hash childDeclared = childRoot) :
    outerDeclared = outerCommitted ∧ childDeclared = childCommitted ∧
      Heap.get outerDeclared refKey = some childRoot := by
  have h1 : outerDeclared = outerCommitted := boundary_init_root_bound hash hnoOuter houter
  have h2 : childDeclared = childCommitted :=
    boundary_init_root_bound hash hnoInner (hchild.trans hchildRoot.symm)
  exact ⟨h1, h2, by rw [h1]; exact hnames⟩

/-! ## §5 — THE NULLIFIER WIN: freshness is a memory property (no Merkle path intra-proof).

A nullifier domain cell is `none` (never spent) or `some _` (spent). Inserts are the only writes
(`InsertOnlyAt` — nobody un-spends). Then a read returning `none` at `(nullifiers, x)` — one row
of the memory table, certified by the same single balance as everything else — PROVES both:
`x` was absent from the proof's INITIAL nullifier view (= the incoming boundary set), and no
earlier op in this proof inserted it (no intra-proof double spend). Cross-proof persistence is
the boundary's: the initial view is loaded from the committed map, whose root pins absence in
any heap claiming it (`root_injective`). -/

section Nullifier

variable {Addr : Type u} {β : Type v} [DecidableEq Addr]

/-- A read mid-trace returns the CURRENT memory value (the fold of its prefix) — consistency,
read off at a split point. -/
theorem consistent_read_pins {op : Op Addr β} {post : List (Op Addr β)} :
    ∀ {pre : List (Op Addr β)} {m : Addr → β},
      ConsistentFrom m (pre ++ op :: post) → op.kind = .read →
      op.val = (pre.foldl step m) op.addr := by
  intro pre
  induction pre with
  | nil =>
    intro m hcons hk
    exact hcons.1 hk
  | cons op' pre ih =>
    intro m hcons hk
    rw [List.foldl_cons]
    exact ih hcons.2 hk

/-- **The insert-only discipline** at an address: every write there installs `some _` (a
nullifier is inserted, never erased). The one structural fact that turns "reads `none`" into
"was never written". -/
def InsertOnlyAt (a : Addr) (tr : List (Op Addr (Option β))) : Prop :=
  ∀ op ∈ tr, op.addr = a → op.kind = .write → op.val ≠ none

instance instDecidableInsertOnlyAt [DecidableEq β] (a : Addr)
    (tr : List (Op Addr (Option β))) : Decidable (InsertOnlyAt a tr) :=
  inferInstanceAs (Decidable (∀ op ∈ tr, _))

/-- Under insert-only writes, a `none` cell was ALWAYS `none`: the fold reading `none` at `a`
forces the initial value `none` AND no write to `a` anywhere in the prefix. -/
theorem fold_none_of_insert_only {a : Addr} :
    ∀ {pre : List (Op Addr (Option β))} {m : Addr → Option β},
      InsertOnlyAt a pre →
      (pre.foldl step m) a = none →
      m a = none ∧ ∀ op ∈ pre, op.addr = a → op.kind ≠ .write := by
  intro pre
  induction pre with
  | nil =>
    intro m _ h
    exact ⟨h, fun op hop => absurd hop (List.not_mem_nil)⟩
  | cons op pre ih =>
    intro m hio h
    rw [List.foldl_cons] at h
    obtain ⟨hstep, hrest⟩ := ih (fun o ho => hio o (List.mem_cons_of_mem _ ho)) h
    have hopnw : op.addr = a → op.kind ≠ .write := fun haddr hw =>
      hio op (List.mem_cons_self ..) haddr hw (by
        have hsw := step_write (op := op) hw m
        rw [haddr] at hsw
        rw [← hsw]
        exact hstep)
    have hma : m a = none := by
      by_cases hc : op.kind = .write ∧ a = op.addr
      · exact absurd hc.1 (hopnw hc.2.symm)
      · rw [← hstep, step, if_neg hc]
    refine ⟨hma, fun o ho haddr => ?_⟩
    rcases List.mem_cons.mp ho with rfl | ho'
    · exact hopnw haddr
    · exact hrest o ho' haddr

end Nullifier

/-- **`nullifier_fresh_sound` — THE NULLIFIER-AS-MEMORY THEOREM.** In a consistent unified trace
(one Blum balance away, via `universal_memory_sound`/`memcheck_sound`), a read returning `none`
at `(nullifiers, x)` under the insert-only discipline PROVES: (1) `x` was absent from the
proof's INITIAL nullifier view, and (2) no earlier op in this proof inserted `x` — intra-proof
double spends are impossible. Freshness = "this address was never written in the nullifier
domain", a pure memory property: NO Merkle path, NO gap opening, NO hashing intra-proof. -/
theorem nullifier_fresh_sound [DecidableEq κ] {β : Type v}
    {init : UAddr κ → Option β} {pre post : List (Op (UAddr κ) (Option β))}
    {rop : Op (UAddr κ) (Option β)} {x : κ}
    (hcons : Consistent init (pre ++ rop :: post))
    (hread : rop.kind = .read) (haddr : rop.addr = (Domain.nullifiers, x))
    (hnone : rop.val = none)
    (hio : InsertOnlyAt (Domain.nullifiers, x) pre) :
    init (Domain.nullifiers, x) = none ∧
      ∀ op ∈ pre, op.addr = (Domain.nullifiers, x) → op.kind ≠ .write := by
  have hpin := consistent_read_pins hcons hread
  rw [hnone, haddr] at hpin
  exact fold_none_of_insert_only hio hpin.symm

/-- **`nullifier_fresh_binds_root` — cross-proof persistence rides the boundary root.** Load the
initial nullifier view from the committed map `nmap`; then the intra-proof freshness read pins
absence in `nmap` — and, absent a sponge collision at the ONE pair `Heap.rootFind` names for this
equivocation, in ANY heap publishing the same root (`root_injective`): a prover cannot keep the
published nullifier root while hiding a spent nullifier. The Merkle machinery appears HERE, at the
boundary, once — never per access.

⚑ **PORTED OFF `Poseidon2SpongeCR` (2026-08-01)** — the floor is refuted at deployed BabyBear, so
the anti-double-spend tooth used to be vacuous exactly where it matters. It now carries the
decidable per-instance residual `hno`; the honest single-map case discharges it outright
(`Heap.heapRootColl_dischargeable`), and a caller holding the floor rewires through
`Poseidon2Binding.spongeColl_refutable_of_injective _ hCR _`. -/
theorem nullifier_fresh_binds_root (hash : List ℤ → ℤ)
    {nmap nmap' : FeltHeap} {init : UAddr ℤ → Option ℤ}
    {pre post : List (Op (UAddr ℤ) (Option ℤ))}
    {rop : Op (UAddr ℤ) (Option ℤ)} {x : ℤ}
    (hload : ∀ a : ℤ, init (Domain.nullifiers, a) = Heap.get nmap a)
    (hno : ¬ Heap.HeapRootColl hash nmap' nmap)
    (hroot : Heap.root hash nmap' = Heap.root hash nmap)
    (hcons : Consistent init (pre ++ rop :: post))
    (hread : rop.kind = .read) (haddr : rop.addr = (Domain.nullifiers, x))
    (hnone : rop.val = none)
    (hio : InsertOnlyAt (Domain.nullifiers, x) pre) :
    Heap.get nmap' x = none ∧ x ∉ Heap.keys nmap' := by
  have habs := (nullifier_fresh_sound hcons hread haddr hnone hio).1
  rw [hload] at habs
  have heq : nmap' = nmap := Heap.root_injective hash hno hroot
  rw [heq]
  exact ⟨habs, (Heap.get_eq_none_iff nmap x).mp habs⟩

/-! ## §6 — NON-VACUITY: both polarities, concrete multi-domain traces, #guard-witnessed.

One trace touching FOUR domains (register write/read · heap set · cap absence check · nullifier
freshness + insert), balanced and consistent under ONE check; every per-domain projection
consistent standalone. Negatives: the cross-domain tuple-steal UNBALANCES (domains are disjoint
sub-multisets), the flat untagged space ALIASES (the tag is semantically load-bearing), and the
intra-proof double-spend read is REFUSED. -/

section NonVacuity

private def R0 : UAddr ℤ := (Domain.registers, 0)
private def H10 : UAddr ℤ := (Domain.heap, 10)
private def C5 : UAddr ℤ := (Domain.caps, 5)
private def N7 : UAddr ℤ := (Domain.nullifiers, 7)

/-- All domains start empty (`none`) — registers unset, maps empty, no nullifier spent. -/
private def uinit : UAddr ℤ → Option ℤ := fun _ => none

/-- THE honest five-domain trace: register write 42 · heap set 99 · cap-absence check ·
nullifier-freshness check · nullifier insert · register read-back. Serials 1..6. -/
private def trU : List (Op (UAddr ℤ) (Option ℤ)) :=
  [⟨.write, R0, some 42, none, 0⟩,      -- 1: register write
   ⟨.write, H10, some 99, none, 0⟩,     -- 2: heap set
   ⟨.read, C5, none, none, 0⟩,          -- 3: cap membership check — ABSENT (reads init none)
   ⟨.read, N7, none, none, 0⟩,          -- 4: nullifier FRESHNESS — no Merkle path, one mem row
   ⟨.write, N7, some 1, none, 4⟩,       -- 5: the nullifier INSERT (claims the read-back at 4)
   ⟨.read, R0, some 42, some 42, 1⟩]    -- 6: register read-back

/-- The honest final claims (value, last-touch serial) per declared address. -/
private def ufin : UAddr ℤ → Option ℤ × Nat := fun a =>
  if a = R0 then (some 42, 6)
  else if a = H10 then (some 99, 2)
  else if a = C5 then (none, 3)
  else if a = N7 then (some 1, 5)
  else (none, 0)

private def uaddrs : List (UAddr ℤ) := [R0, H10, C5, N7]

-- The honest unified trace BALANCES (one check), is disciplined, and is consistent.
#guard decide (MemCheck uinit ufin uaddrs trU)
#guard decide (Disciplined trU)
#guard decide (Consistent uinit trU)

-- Every per-domain projection, stripped to a standalone memory, is consistent — the
-- executable shadow of `universal_memory_sound` (registers picks ops 1+6, nullifiers 4+5, …).
#guard decide (Consistent (fun a => uinit (Domain.registers, a))
  ((domTrace Domain.registers trU).map stripOp))
#guard decide (Consistent (fun a => uinit (Domain.heap, a))
  ((domTrace Domain.heap trU).map stripOp))
#guard decide (Consistent (fun a => uinit (Domain.caps, a))
  ((domTrace Domain.caps trU).map stripOp))
#guard decide (Consistent (fun a => uinit (Domain.nullifiers, a))
  ((domTrace Domain.nullifiers trU).map stripOp))

-- THE KEYSTONE fires end-to-end on the honest instance (every hypothesis by `decide` —
-- nothing vacuous in the pipeline).
example : Consistent uinit trU ∧
    ∀ d : Domain, Consistent (fun a => uinit (d, a)) ((domTrace d trU).map stripOp) :=
  universal_memory_sound (init := uinit) (fin := ufin) (addrs := uaddrs)
    (by decide) (by decide) (by decide) (by decide)

-- THE NULLIFIER THEOREM fires on the honest instance: the freshness read (position 4) proves
-- nullifier 7 absent from the initial view AND never inserted in the prefix.
example :
    uinit (Domain.nullifiers, 7) = none ∧
      ∀ op ∈ [(⟨.write, R0, some 42, none, 0⟩ : Op (UAddr ℤ) (Option ℤ)),
              ⟨.write, H10, some 99, none, 0⟩, ⟨.read, C5, none, none, 0⟩],
        op.addr = (Domain.nullifiers, 7) → op.kind ≠ .write :=
  nullifier_fresh_sound (β := ℤ)
    (pre := [⟨.write, R0, some 42, none, 0⟩, ⟨.write, H10, some 99, none, 0⟩,
             ⟨.read, C5, none, none, 0⟩])
    (post := [⟨.write, N7, some 1, none, 4⟩, ⟨.read, R0, some 42, some 42, 1⟩])
    (rop := ⟨.read, N7, none, none, 0⟩)
    (by decide) rfl rfl rfl (by decide)

/-! ### Negative polarity 1 — the cross-domain tuple-steal UNBALANCES.

A nullifier-domain read claiming the heap-domain write's tuple: the addresses differ in the TAG
alone, so the claimed entry matches no write — the balance refuses. Domains are disjoint
sub-multisets; the tag does the separating. -/

private def N10 : UAddr ℤ := (Domain.nullifiers, 10)

private def trSteal : List (Op (UAddr ℤ) (Option ℤ)) :=
  [⟨.write, H10, some 99, none, 0⟩,
   ⟨.read, N10, some 99, some 99, 1⟩]   -- claims the HEAP write as its predecessor

private def finSteal : UAddr ℤ → Option ℤ × Nat := fun a =>
  if a = H10 then (some 99, 1) else if a = N10 then (some 99, 2) else (none, 0)

#guard decide (Disciplined trSteal)                                   -- locally fine…
#guard decide (¬ Consistent uinit trSteal)                            -- …but a lie…
#guard decide (¬ MemCheck uinit finSteal [H10, N10] trSteal)          -- …and the balance refuses

/-! ### Negative polarity 2 — the FLAT (untagged) space ALIASES: the tag is load-bearing.

Tagged: inserting nullifier 7 leaves cap 7 untouched — the honest cap-absence read passes.
Flat: the same two touches collide at address 7 — the cap check READS THE NULLIFIER'S VALUE
(a ghost capability), and the honest absence read is REFUSED. -/

-- Tagged: cap 7 still absent after nullifier 7 is inserted (domains separate).
#guard decide (Consistent uinit
  ([⟨.write, (Domain.nullifiers, 7), some 1, none, 0⟩,
    ⟨.read, (Domain.caps, 7), none, none, 0⟩] : List (Op (UAddr ℤ) (Option ℤ))))
-- Flat: the cap read at 7 RETURNS the nullifier's value — the ghost is CONSISTENT (disaster)…
#guard decide (Consistent (fun _ => (none : Option ℤ))
  ([⟨.write, 7, some 1, none, 0⟩, ⟨.read, 7, some 1, some 1, 1⟩] : List (Op ℤ (Option ℤ))))
-- …and the honest "cap 7 absent" read is REFUSED in the flat space.
#guard decide (¬ Consistent (fun _ => (none : Option ℤ))
  ([⟨.write, 7, some 1, none, 0⟩, ⟨.read, 7, none, none, 0⟩] : List (Op ℤ (Option ℤ))))

/-! ### Negative polarity 3 — the intra-proof DOUBLE SPEND is refused.

Insert nullifier 7, then claim it's still fresh: the lying read's claimed tuple cancels nothing
(the insert's tuple is `some 1`), so no final claim can balance the multisets. -/

private def trDouble : List (Op (UAddr ℤ) (Option ℤ)) :=
  [⟨.write, N7, some 1, none, 0⟩,    -- the insert (serial 1)
   ⟨.read, N7, none, none, 0⟩]       -- "still fresh" (serial 2) — the double-spend lie

#guard decide (Disciplined trDouble)                                  -- locally fine…
#guard decide (¬ Consistent uinit trDouble)                           -- …but a lie…
#guard decide (¬ MemCheck uinit (fun _ => ((none : Option ℤ), 2)) [N7] trDouble)
#guard decide (¬ MemCheck uinit (fun _ => (some 1, 1)) [N7] trDouble) -- …either claim refused

/-! ### Boundary non-vacuity — the derived view and its root, concretely.

The heap domain's final cells derived from the memory's (pinned) final column = the directly
built map; same sorted leaf list, same sponge root. And `boundary_root_derived` fires on it. -/

-- The derived boundary view of the heap domain is exactly the one-cell map…
#guard boundaryCells (fun a => (ufin (Domain.heap, a)).1) [10] == [(10, 99)]
-- …with the same sorted-sponge root as the directly-built map (the refSponge instance).
#guard Heap.root Heap.refSponge (boundaryCells (fun a => (ufin (Domain.heap, a)).1) [10])
  == Heap.root Heap.refSponge [((10 : ℤ), (99 : ℤ))]
-- The lookup characterization, executably: declared-and-present / declared-and-absent / off-list.
#guard Heap.get (boundaryCells (fun a => (ufin (Domain.heap, a)).1) [10]) 10 == some 99
#guard Heap.get (boundaryCells (fun a => (ufin (Domain.caps, a)).1) [5]) 5 == none
#guard Heap.get (boundaryCells (fun a => (ufin (Domain.heap, a)).1) [10]) 11 == none

/-- `boundary_root_derived` fires on the concrete instance: today's map `[(10, 99)]` has the
same root as the boundary view derived from the memory's final column. -/
example :
    Heap.root Heap.refSponge [((10 : ℤ), (99 : ℤ))]
      = Heap.root Heap.refSponge
          (boundaryCells (fun a => (ufin (Domain.heap, a)).1) [10]) := by
  refine boundary_root_derived Heap.refSponge ?_ ?_ ?_
  · simp [Heap.SortedKeys, Heap.keys]
  · simp
  · intro a
    by_cases ha : a = (10 : ℤ)
    · subst ha; decide
    · rw [if_neg (fun h => ha (List.mem_singleton.mp h)),
        Heap.get_cons_ne _ _ ha, Heap.get_nil]

/-- The INIT-side anchor fires too: the committed pre-state map `[(10, 7)]` (the heap-domain
init image) has the same root as the boundary view derived from `uinit`. Both polarities of the
boundary derivation (init AND final) are concrete-witnessed. -/
private def uinit_one : UAddr ℤ → Option ℤ := fun a => if a = (Domain.heap, 10) then some 7 else none

example :
    Heap.root Heap.refSponge [((10 : ℤ), (7 : ℤ))]
      = Heap.root Heap.refSponge
          (boundaryCells (fun a => uinit_one (Domain.heap, a)) [10]) := by
  refine boundary_init_root_derived Heap.refSponge ?_ ?_ ?_
  · simp [Heap.SortedKeys, Heap.keys]
  · simp
  · intro a
    by_cases ha : a = (10 : ℤ)
    · subst ha; decide
    · rw [if_neg (fun h => ha (List.mem_singleton.mp h)),
        Heap.get_cons_ne _ _ ha, Heap.get_nil]

/-! ### Whole-image (no-extra-cells) non-vacuity — the extra cell MOVES the fold root.

`boundary_image_eq_of_root` / `boundary_whole_image_sem` carry the no-extra-cells punch under the
abstract CR floor; these guards exhibit it on the computable `refSponge`, the executable shadow.
A committed heap that holds the declared boundary cell `[(10, 7)]` AND an EXTRA cell `(20, 5)`
the boundary never declared has a DIFFERENT root from the whole-boundary fold `boundaryCells uinit
[10]` — so the whole-image root pin REFUSES it (a hidden cell cannot survive the fold), exactly
the direction the per-cell subset opening could not see. -/

-- The whole-boundary fold of the one-cell init image is the one-cell leaf list (positive):
#guard boundaryCells (fun a => uinit_one (Domain.heap, a)) [10] == [((10 : ℤ), (7 : ℤ))]
-- A committed heap with an EXTRA undeclared cell (20,5) has a DIFFERENT fold root — REFUSED:
#guard (Heap.root Heap.refSponge [((10 : ℤ), (7 : ℤ)), ((20 : ℤ), (5 : ℤ))]
  != Heap.root Heap.refSponge (boundaryCells (fun a => uinit_one (Domain.heap, a)) [10]))
-- The honest committed heap (exactly the boundary cell) MATCHES the fold root — admitted:
#guard (Heap.root Heap.refSponge [((10 : ℤ), (7 : ℤ))]
  == Heap.root Heap.refSponge (boundaryCells (fun a => uinit_one (Domain.heap, a)) [10]))
-- The whole-image lookup characterization: OFF-list address 20 is ABSENT in the boundary view
-- (the no-extra-cells direction in lookup terms — `boundary_whole_image_sem`'s `else none`):
#guard Heap.get (boundaryCells (fun a => uinit_one (Domain.heap, a)) [10]) (20 : ℤ) == none

/-- `boundary_whole_image_sem` fires structurally on a concrete committed heap = its boundary
view: the heap agrees with the declared image at the declared address AND is absent off-list.

⚑ **THE PORT MADE THIS WITNESS FLOOR-FREE.** It used to need an abstract `hCR` because the keystone
rode the named floor; the per-instance residual is DISCHARGED here for EVERY `hash`, with no
cryptographic assumption at all — the honest committer publishes ONE heap, so the extractor bottoms
out at an equal pair (`Heap.heapRootColl_dischargeable`). That is precisely what the deleted floor
could never do: `Poseidon2SpongeCR` is unavailable at the deployed sponge even to an honest party,
so the pre-cutover witness exhibited nothing at deployed parameters. -/
example (hash : List ℤ → ℤ)
    (init : ℤ → Option ℤ) (as : List ℤ) (has : as.Pairwise (· < ·)) :
    ∀ a, Heap.get (boundaryCells init as) a = if a ∈ as then init a else none :=
  boundary_whole_image_sem hash has (Heap.heapRootColl_dischargeable hash _) rfl

/-! ### Working-inert non-vacuity — a working write moves the working boundary but NOT a
committed one, and the committed root is unchanged. -/

-- Two final memories differing ONLY at a working cell `(working, 0)`: agree off the working
-- domain. (The hypothesis `working_commitment_inert` takes, exhibited concretely.)
private def finA : UAddr ℤ → Option ℤ := fun a => if a = (Domain.heap, 10) then some 99 else none
private def finB : UAddr ℤ → Option ℤ := fun a =>
  if a = (Domain.heap, 10) then some 99
  else if a = (Domain.working, 0) then some 7 else none

-- The committed HEAP boundary is IDENTICAL across the two (the working write is inert)…
#guard boundaryCells (fun a => finA (Domain.heap, a)) [10]
  == boundaryCells (fun a => finB (Domain.heap, a)) [10]
-- …but the WORKING boundary genuinely DIFFERS (finB wrote a working cell finA did not) —
-- the inert guarantee is about COMMITTED domains, and working really is a live (uncommitted) plane.
#guard boundaryCells (fun a => finA (Domain.working, a)) [0]
  != boundaryCells (fun a => finB (Domain.working, a)) [0]

/-- `working_commitment_inert` fires: `finA`/`finB` agree off the working domain, so the heap
domain's committed boundary view coincides — the working cell never enters it. -/
example :
    boundaryCells (fun a => finA (Domain.heap, a)) [10]
      = boundaryCells (fun a => finB (Domain.heap, a)) [10] :=
  working_commitment_inert (d := Domain.heap) (by decide)
    (fun a ha => by
      -- off the working domain finA and finB agree (they differ only at (working, 0))
      simp only [finA, finB]
      by_cases h0 : a = (Domain.working, 0)
      · exact absurd (h0 ▸ rfl) ha
      · rw [if_neg h0])

/-! ### Recursive-open non-vacuity — the two-level bind fires on a concrete UmemRef shape.

The inner umem `[(0, 99)]` has root `R`; the outer umem holds `R` at ref key `5` (a `UmemRef`).
Both binds discharge by `rfl` on the matching declared/committed heaps, and — since the port —
BOTH per-instance residuals discharge outright too, at every `hash`, so the two-level bind fires at
DEPLOYED parameters rather than only under a hypothesis nothing satisfies. -/

example (hash : List ℤ → ℤ) :
    ([((5 : ℤ), Heap.root hash [((0 : ℤ), (99 : ℤ))])] : FeltHeap)
        = [((5 : ℤ), Heap.root hash [((0 : ℤ), (99 : ℤ))])]
      ∧ ([((0 : ℤ), (99 : ℤ))] : FeltHeap) = [((0 : ℤ), (99 : ℤ))]
      ∧ Heap.get ([((5 : ℤ), Heap.root hash [((0 : ℤ), (99 : ℤ))])] : FeltHeap) 5
          = some (Heap.root hash [((0 : ℤ), (99 : ℤ))]) :=
  recursive_open_sound hash (refKey := 5)
    (outerCommitted := [((5 : ℤ), Heap.root hash [((0 : ℤ), (99 : ℤ))])])
    (childCommitted := [((0 : ℤ), (99 : ℤ))]) (childDeclared := [((0 : ℤ), (99 : ℤ))])
    (Heap.heapRootColl_dischargeable hash _) (Heap.heapRootColl_dischargeable hash _)
    rfl (by simp) rfl rfl

end NonVacuity

/-! ## Axiom-hygiene pins -/

#assert_axioms consistentFrom_filter
#assert_axioms consistentFrom_strip
#assert_axioms universal_memory_sound
#assert_axioms universal_memory_sound_single
#assert_axioms chains_pin_fold
#assert_axioms memcheck_pins_final
#assert_axioms boundaryCells_sorted
#assert_axioms get_boundaryCells
#assert_axioms boundary_root_derived
#assert_axioms boundary_root_from_memcheck
#assert_axioms boundary_init_root_derived
#assert_axioms boundary_init_root_bound
#assert_axioms boundary_init_root_binds_or_collides
#assert_axioms boundary_image_eq_of_root
#assert_axioms boundary_whole_image_sem
#assert_axioms working_commitment_inert
#assert_axioms working_commitment_root_inert
#assert_axioms recursive_levels_disjoint
#assert_axioms recursive_open_sound
#assert_axioms consistent_read_pins
#assert_axioms fold_none_of_insert_only
#assert_axioms nullifier_fresh_sound
#assert_axioms nullifier_fresh_binds_root
#assert_namespace_axioms Dregg2.Crypto.UniversalMemory

end Dregg2.Crypto.UniversalMemory
