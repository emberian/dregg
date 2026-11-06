/-
# Dregg2.Stream.ClaudePolicy: the demo policy's theorems, and the flag-DFA mutant refuted

About `ClaudeCore.policyA` / `policyVC` / `classify`, the objects `lake exe stream-check` runs.

* `policy_valid`: the verdict certificate is valid for Büchi acceptance, so every theorem of
  `Stream.Omega` / `Stream.Window` applies (`policy_windows_compose` instantiates `windows_compose`).
* `policy_accepts_iff`: the policy's Büchi language is "no forbidden command, ever" ∩ "infinitely often
  no prompt is waiting" (`prod_accepts_iff`).
* `respLive_is_liveness`: the liveness half has no bad prefix (every finite word extends to an accepted
  ω-word): a genuine liveness property in Alpern–Schneider's sense, so no finite receipt can say `viol`
  on its account, only the safety half can.
* `unknown_is_genuine`: whenever the verdict is `unknown`, the prefix has both an accepted and a
  rejected extension, so `unknown` is LTL3's `?`, not a lazy answer (the certificate is complete here).
* **The flag-DFA mutant**, refuted twice: `flag_mutant_unsound` (reading "currently in `F`" as `sat`
  is wrong: the empty prefix is in `F` and its all-forbidden extension is rejected), and
  `reach_once_not_buchi` (on `other, prompt^ω` the receipt counter is 1 forever, so "`F` reached" or
  "counter ≥ 1" says accepted, and the Büchi condition rejects).
* `policyVC.good` is empty, so `verdict_sat_sound` is vacuous at this policy (a safety half that can
  still trip forbids `sat`); `sat` is exercised only by the general theorem.
* `classify_cases`, `commandForbidden_cases`: the classifier on hand-written lines and commands, both
  polarities, by compiled evaluation.
-/
import Dregg2.Stream.Window
import Dregg2.Stream.ClaudeCore

namespace Dregg2.Stream.Claude

open Dregg2.Stream

theorem safeMon_absorbing : safeMon.Absorbing := by
  intro s a h; simp [safeMon] at h ⊢; simp [h]

theorem policy_valid : policyVC.Valid policyA .buchi := prodVCert_valid safeMon respLive safeMon_absorbing

theorem policy_accepts_iff (σ : OWord Ev) :
    policyA.Accepts .buchi σ ↔ safeMon.Safe σ ∧ respLive.Accepts .buchi σ :=
  prod_accepts_iff safeMon respLive safeMon_absorbing σ

/-- Pad a finite word with a constant symbol. -/
def padWith (u : List Ev) (a : Ev) : OWord Ev := fun i => if h : i < u.length then u[i] else a

theorem padWith_extends (u : List Ev) (a : Ev) : Extends (padWith u a) u := by
  intro i h; simp [padWith, h]

theorem padWith_tail (u : List Ev) (a : Ev) (n : ℕ) (h : u.length ≤ n) : padWith u a n = a := by
  simp [padWith, show ¬ n < u.length by omega]

/-- After the prefix, the all-`reply` tail keeps `policyA` at `(tripped, false)`. -/
theorem run_reply_tail (u : List Ev) (k : ℕ) :
    policyA.run (padWith u .reply) (u.length + 1 + k) =
      ((policyA.run (padWith u .reply) u.length).1, false) := by
  induction k with
  | zero =>
    show policyA.step (policyA.run (padWith u .reply) u.length) (padWith u .reply u.length) = _
    rw [padWith_tail u _ _ (le_refl _)]
    simp [policyA, prodSafety, safeMon, respLive]
  | succ k ih =>
    show policyA.step (policyA.run (padWith u .reply) (u.length + 1 + k)) (padWith u .reply (u.length + 1 + k)) = _
    rw [ih, padWith_tail u _ _ (by omega)]
    simp [policyA, prodSafety, safeMon, respLive]

theorem respLive_step_reply (w : Bool) : respLive.step w .reply = false := rfl

/-- **The liveness half is a liveness property**: every finite word extends to an accepted ω-word. -/
theorem respLive_is_liveness (u : List Ev) : ∃ σ, Extends σ u ∧ respLive.Accepts .buchi σ := by
  refine ⟨padWith u .reply, padWith_extends u _, fun N => ⟨N + u.length + 1, by omega, ?_⟩⟩
  have : ∀ k, respLive.run (padWith u .reply) (u.length + 1 + k) = false := by
    intro k
    induction k with
    | zero =>
      show respLive.step _ (padWith u .reply u.length) = false
      rw [padWith_tail u _ _ (le_refl _)]; rfl
    | succ k ih =>
      show respLive.step _ (padWith u .reply (u.length + 1 + k)) = false
      rw [padWith_tail u _ _ (by omega)]; rfl
  have h := this N
  rw [show u.length + 1 + N = N + u.length + 1 by omega] at h
  show respLive.mark (respLive.run (padWith u .reply) (N + u.length + 1)) = true
  rw [h]; rfl

/-- **`unknown` is genuine**: an `unknown` verdict leaves both outcomes open. -/
theorem unknown_is_genuine (u : List Ev) (h : verdictOf policyVC (policyA.exec policyA.start u) = .unknown) :
    (∃ σ, Extends σ u ∧ policyA.Accepts .buchi σ) ∧ (∃ σ, Extends σ u ∧ ¬ policyA.Accepts .buchi σ) := by
  have hnt : (policyA.exec policyA.start u).1 = false := by
    unfold verdictOf at h
    cases hx : (policyA.exec policyA.start u).1
    · rfl
    · simp [policyVC, prodVCert, safeMon, hx] at h
  refine ⟨⟨padWith u .reply, padWith_extends u _, fun N => ⟨u.length + 1 + N, by omega, ?_⟩⟩,
    ⟨padWith u .forbidden, padWith_extends u _, ?_⟩⟩
  · show policyA.mark (policyA.run (padWith u .reply) (u.length + 1 + N)) = true
    rw [run_reply_tail, policyA.run_eq_exec (padWith_extends u _), hnt]
    rfl
  · apply dead_rejects policy_valid _ (u.length + 1)
    show safeMon.bad (policyA.step _ (padWith u .forbidden u.length)).1 = true
    rw [padWith_tail u _ _ (le_refl _)]
    simp [policyA, prodSafety, safeMon]

/-- The mutant verdict: "currently marked" read as `sat`. -/
def flagVerdict (q : Bool × Bool) : Verdict :=
  if policyVC.dead q then .viol else if policyA.mark q then .sat else .unknown

/-- **The flag-DFA mutant is unsound**: it says `sat` on the empty prefix, which has a rejected
extension. -/
theorem flag_mutant_unsound :
    flagVerdict (policyA.exec policyA.start []) = .sat ∧ ¬ GoodPrefix (policyA.Accepts .buchi) [] := by
  refine ⟨by decide, fun hg => ?_⟩
  have := (unknown_is_genuine [] (by decide)).2
  obtain ⟨σ, hσ, hrej⟩ := this
  exact hrej (hg σ hσ)

/-- The stream `other, prompt, prompt, …`: one marked position after the start, then never again. -/
def onceThenWait : OWord Ev := fun n => if n = 0 then .other else .prompt

/-- **Reaching `F` once is not Büchi acceptance, and a nonzero counter is not acceptance either**:
on `other, prompt^ω` the receipts' counter is `1` at every `n ≥ 1` (so a mutant reading
"`countOut ≥ 1`" or "`F` reached" as accepted says yes), and the Büchi condition rejects. -/
theorem reach_once_not_buchi :
    (∀ n, 1 ≤ n → policyA.marks onceThenWait n = 1) ∧ ¬ policyA.Accepts .buchi onceThenWait := by
  have h1 : policyA.run onceThenWait 1 = (false, false) := rfl
  have hrun : ∀ n, policyA.run onceThenWait (n + 2) = (false, true) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      show policyA.step (policyA.run onceThenWait (n + 2)) (onceThenWait (n + 2)) = _
      rw [ih]; rfl
  have hm : ∀ n, policyA.marks onceThenWait (n + 1) = 1 := by
    intro n
    induction n with
    | zero => show 0 + (if policyA.mark (policyA.run onceThenWait 1) then 1 else 0) = 1; rw [h1]; rfl
    | succ n ih =>
      show policyA.marks onceThenWait (n + 1) + (if policyA.mark (policyA.run onceThenWait (n + 2)) then 1 else 0) = 1
      rw [ih, hrun]; rfl
  refine ⟨fun n hn => ?_, fun h => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact hm k
  · obtain ⟨n, hn, hmk⟩ := h 2
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [hrun] at hmk
    simp [policyA, prodSafety, safeMon, respLive] at hmk

/-- Two of `windows_compose`'s five conjuncts at the demo policy (tracking, and `viol` is a bad
prefix), for any hash and any entry encoding; the rest instantiate the same way. -/
theorem policy_windows_compose {E : Type} (hash : List Int → Int) (val : E → Int) (sym : E → Ev)
    {W : List (List E × WindowCert (Bool × Bool))} {acc : Acc (Bool × Bool)}
    (hc : (policyOver hash val sym).checkChain (policyOver hash val sym).genesis W = some acc) :
    Tracks (policyOver hash val sym) (W.flatMap Prod.fst) acc ∧
    (verdictOf policyVC acc.st.q = .viol →
      BadPrefix (policyA.Accepts .buchi) ((W.flatMap Prod.fst).map sym)) :=
  let h := windows_compose (policyOver hash val sym) policy_valid hc
  ⟨h.1, h.2.2.1⟩

#assert_axioms safeMon_absorbing
#assert_axioms policy_valid
#assert_axioms policy_accepts_iff
#assert_axioms respLive_is_liveness
#assert_axioms unknown_is_genuine
#assert_axioms flag_mutant_unsound
#assert_axioms reach_once_not_buchi
#assert_axioms policy_windows_compose

/-! ## The classifier, both polarities

Concrete facts about the classifier on hand-written transcript lines and commands, checked by compiled
evaluation (`native_decide`, pinned with `#assert_compiled`) under the standing policy. -/

theorem classify_cases : (
    (classify "{\"type\":\"user\",\"message\":{\"role\":\"user\",\"content\":\"hi claude\"}}" == .prompt) &&
    (classify "{\"type\":\"user\",\"isMeta\":true,\"message\":{\"content\":\"hi\"}}" == .other) &&
    (classify "{\"type\":\"user\",\"message\":{\"content\":[{\"type\":\"tool_result\",\"content\":\"ok\"}]}}" == .other) &&
    (classify "{\"type\":\"user\",\"message\":{\"content\":\"<command-name>/clear</command-name>\"}}" == .other) &&
    (classify "{\"type\":\"assistant\",\"message\":{\"content\":[{\"type\":\"text\",\"text\":\"done\"}]}}" == .reply) &&
    (classify "{\"type\":\"assistant\",\"message\":{\"content\":[{\"type\":\"thinking\",\"thinking\":\"hm\"}]}}" == .other) &&
    (classify "{\"type\":\"assistant\",\"message\":{\"content\":[{\"type\":\"tool_use\",\"name\":\"Bash\",\"input\":{\"command\":\"cd /x && git stash\"}}]}}" == .forbidden) &&
    (classify "{\"type\":\"assistant\",\"message\":{\"content\":[{\"type\":\"tool_use\",\"name\":\"Bash\",\"input\":{\"command\":\"grep -n 'git stash' RULES.md\"}}]}}" == .other) &&
    (classify "{\"type\":\"assistant\",\"message\":{\"content\":[{\"type\":\"tool_use\",\"name\":\"Bash\",\"input\":{\"command\":\"git stashed-thing\"}}]}}" == .other) &&
    (classify "{\"type\":\"assistant\",\"message\":{\"content\":[{\"type\":\"tool_use\",\"name\":\"Bash\",\"input\":{\"command\":\"ls; pkill -f cat\"}}]}}" == .forbidden) &&
    (classify "not json" == .other) &&
    (classify "{\"type\":\"user\",\"message\":{\"content\":[{\"type\":\"image\"},{\"type\":\"text\",\"text\":\"look\"}]}}" == .prompt)) = true := by native_decide

theorem commandForbidden_cases : (
    (commandForbidden "sudo killall node") &&
    (commandForbidden "bash -c 'git stash pop'") &&
    (commandForbidden "git -C /x stash") &&
    (commandForbidden "pkill -9 -f worker") &&
    (commandForbidden "pkill -x cat") &&
    (commandForbidden "git add -Av") &&
    (commandForbidden "env git stash") &&
    (commandForbidden "timeout 120 ssh -o BatchMode=yes hbox 'pkill -f sample.sh; echo'") &&
    (!commandForbidden "git status && git add src/a.rs") &&
    (!commandForbidden "kill 1234") &&
    (!commandForbidden "pgrep -fl cat") &&
    (!commandForbidden "echo stash") &&
    (commandForbidden "env X=1 git stash") &&
    (!commandForbidden "echo \"x; git stash\"") &&
    (!commandForbidden "git commit -m 'never git stash'") &&
    (commandForbidden "ssh -p 22 bb2 \"cd /x && git add --all\"")) = true := by native_decide

#assert_compiled classify_cases
#assert_compiled commandForbidden_cases

end Dregg2.Stream.Claude
