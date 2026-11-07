/-
# Dregg2.Exec.Continuation — the MID-TURN yield point: suspend/resume between two effects.

`Exec/ForestMemoryProgram.lean` composes the per-verb memory programs to a WHOLE-turn / whole-forest
memory program: the executor's trace folds the pre-projection to the post-projection, and the
property is closed under sequential composition (`memprog_trans` / `List.foldl_append`).

That composition reads the trace as a single block reached at COMMIT. This module sharpens it to the
MID-TURN seam the continuations lane (`turn/src/continuation.rs`) needs: a `yield_point` BETWEEN two
effects of a single in-flight turn. The executor's journal-so-far is a PREFIX of the whole-turn
trace; suspending at a cut captures the prefix's folded state and forwards the rest.

THE GUARANTEE (mirroring the Rust `continuation.rs` module banner):

```text
  run straight through:   pre --[op0 op1 | op2 op3]--> post
  suspend at the cut:     pre --[op0 op1]--> MID          (capture MID as a boundary)
  resume from MID:        MID --[op2 op3]--> post
  THE EQUALITY:  fold pre (all_ops) = fold (fold pre (prefix)) (rest)
```

This is the *journal-prefix snapshot + forward-the-rest equals running straight through* statement,
proven over the SAME `MemoryChecking.step` fold the executor-state bridge and the whole-turn
composition use. The split is pure list algebra (`List.take_append_drop` / `List.foldl_append`), so
the mid-turn cut adds ZERO new memory semantics: a suspend point is an identity on the run.

Two movements, both `#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}):

  1. **THE FOLD SPLIT** (`midturn_split`, `yield_resume_sound`): the fold of the whole trace equals
     the resume-fold over the suspend-fold, at ANY cut. The captured mid-state is a genuine boundary
     on the run; resuming reaches the exact straight-through post.

  2. **THE TAIL IS A STANDALONE PROGRAM** (`disciplinedFrom_drop`, `resumed_tail_disciplined`): the
     remaining ops, re-based so the captured boundary is the new init, are self-`Disciplined`. This
     is what makes a suspended continuation PASSABLE — the tail validates on its own, exactly the
     fail-closed `disciplined(&remaining)` check `Continuation::resume` enforces.

Honesty (the receipt / atomicity boundary): this proves the STATE-fold equality of the cut, NOT that
a mid-turn boundary is independently committable. A turn is all-or-nothing — the receipt is emitted
only at whole-turn completion, never at the cut. The captured boundary is sound as a REPRESENTATION
of mid-flight state ("this prefix, to be completed by the rest of THIS turn"); resume re-drives the
remainder so the commit/rollback decision still spans the whole turn. `midturn_split` is precisely
the state half of that statement and nothing more.
-/
import Dregg2.Crypto.MemoryChecking
import Dregg2.Tactics

namespace Dregg2.Exec.Continuation

open Dregg2.Crypto.MemoryChecking (Op Kind step DisciplinedFrom Disciplined)

universe u v

variable {Addr : Type u} {Val : Type v}

/-! ## §1 — THE FOLD SPLIT: a yield point is an identity on the run. -/

section Fold
variable [DecidableEq Addr]

/-- **`fold_split`** — folding a trace `pre ++ post` equals folding `post` over the fold of `pre`.
The whole content of "a mid-turn boundary is sound": the `MemoryChecking.step` fold distributes over
concatenation (`List.foldl_append`). A suspend cut that splits `ops` into `(pre, post)` reaches the
same state as running straight through, with the captured boundary `m.foldl step pre` in between. -/
theorem fold_split (m : Addr → Val) (pre post : List (Op Addr Val)) :
    (pre ++ post).foldl step m = post.foldl step (pre.foldl step m) :=
  List.foldl_append

/-- **`midturn_split`** — THE MID-TURN YIELD EQUALITY at a cut index `k`. Folding the whole trace
equals folding the tail (`drop k`) over the captured prefix boundary (`fold m (take k)`). The
journal-prefix snapshot, then forward-the-rest, equals running straight through — for EVERY cut. -/
theorem midturn_split (m : Addr → Val) (ops : List (Op Addr Val)) (k : Nat) :
    ops.foldl step m = (ops.drop k).foldl step ((ops.take k).foldl step m) := by
  conv_lhs => rw [← List.take_append_drop k ops]
  exact fold_split m (ops.take k) (ops.drop k)

/-- **`yield_resume_sound`** — the suspend/resume round-trip reaches the executor's post-state.
Given the whole-turn fact `fold pre ops = post` (the executor-state bridge square), suspending at
ANY cut `k` (capturing `mid := fold pre (take k ops)`) and resuming (`fold mid (drop k ops)`) reaches
EXACTLY `post`. This is the Lean twin of `continuation.rs`'s
`resume(suspend(pre, ops, cut)) = fold(pre, ops)`. -/
theorem yield_resume_sound (pre : Addr → Val) (ops : List (Op Addr Val)) (post : Addr → Val)
    (k : Nat) (hturn : ops.foldl step pre = post) :
    (ops.drop k).foldl step ((ops.take k).foldl step pre) = post := by
  rw [← midturn_split, hturn]

/-- A yield at the END of the run (cut past the trace) resumes to the captured boundary unchanged:
the continuation is COMPLETE (`continuation.rs::is_complete`). `drop k = []` for `k ≥ length`. -/
theorem yield_complete (m : Addr → Val) (ops : List (Op Addr Val)) {k : Nat}
    (hk : ops.length ≤ k) :
    (ops.drop k).foldl step ((ops.take k).foldl step m) = (ops.take k).foldl step m := by
  rw [List.drop_eq_nil_of_le hk]; rfl

end Fold

/-! ## §2 — THE RESUMED TAIL IS A STANDALONE, SELF-DISCIPLINED PROGRAM.

A suspended continuation is PASSABLE only if its remaining ops validate on their own (the captured
boundary is the new init). `continuation.rs::suspend` re-bases the tail's serials so it is
self-`Disciplined`; here we prove the structural half: dropping a prefix of a `DisciplinedFrom n`
trace leaves a `DisciplinedFrom (n + k)` trace — and a read still returns its claimed prior. The
serial-rebase (subtracting the cut) is the Rust wire concern; the discipline SHAPE is preserved. -/

/-- **`disciplinedFrom_drop`** — discipline is closed under dropping a prefix. If a trace is
`DisciplinedFrom n`, its `k`-suffix is `DisciplinedFrom (n + k)`. The remaining ops of a suspended
continuation inherit the per-op memcheck discipline; the resume tail is a genuine memory program. -/
theorem disciplinedFrom_drop :
    ∀ (k n : Nat) (tr : List (Op Addr Val)),
      DisciplinedFrom n tr → DisciplinedFrom (n + k) (tr.drop k)
  | 0, n, tr, h => by simpa using h
  | _ + 1, _, [], _ => by simp [DisciplinedFrom]
  | k + 1, n, _ :: tr, h => by
    have hrest : DisciplinedFrom (n + 1) tr := h.2
    have hd := disciplinedFrom_drop k (n + 1) tr hrest
    -- `(op :: tr).drop (k+1) = tr.drop k` and `(n+1)+k = n+(k+1)`.
    have heq : (n + 1) + k = n + (k + 1) := by omega
    rw [heq] at hd
    simpa [List.drop] using hd

/-- **`resumed_tail_disciplined`** — the tail of a `Disciplined` whole-turn trace, dropped at cut
`k`, is itself `DisciplinedFrom k`. The standalone shape the passable continuation carries: the
remaining ops are a legal memcheck program from the captured boundary onward (serial floor `k`,
which the Rust `suspend` re-bases to `0`). -/
theorem resumed_tail_disciplined (ops : List (Op Addr Val)) (k : Nat)
    (h : Disciplined ops) : DisciplinedFrom k (ops.drop k) := by
  have := disciplinedFrom_drop k 0 ops h
  simpa using this

/-! ## §3 — non-vacuity: the cut is REAL on a genuine two-op program. -/

/-- A two-write program whose mid-cut boundary genuinely differs from both endpoints — the suspend
point is not trivially the pre- or post-state. Witnesses that `midturn_split` is non-vacuous: there
exist runs whose cut captures a real intermediate boundary. -/
theorem midturn_cut_nonvacuous :
    ∃ (m : Nat → Nat) (ops : List (Op Nat Nat)),
      ((ops.take 1).foldl step m) ≠ m ∧
      ((ops.take 1).foldl step m) ≠ ops.foldl step m := by
  refine ⟨(fun _ => 0), [⟨Kind.write, 0, 1, 0, 0⟩, ⟨Kind.write, 0, 2, 1, 1⟩], ?_, ?_⟩
  · intro h; have := congrFun h 0; simp [step] at this
  · intro h; have := congrFun h 0; simp [step] at this

/-! ## Axiom hygiene — every keystone of this module is kernel-clean. -/

#assert_all_clean [fold_split, midturn_split, yield_resume_sound, yield_complete,
  disciplinedFrom_drop, resumed_tail_disciplined, midturn_cut_nonvacuous]

end Dregg2.Exec.Continuation
