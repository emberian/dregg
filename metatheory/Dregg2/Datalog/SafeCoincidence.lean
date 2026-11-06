/-
# Dregg2.Datalog.SafeCoincidence — for safe programs the active-domain semantics IS the unrestricted
one (lane A, 2026-11-06).

`FixpointCert.Derives` and `StratifiedCert.DerivesAt` restrict rule substitutions to the ACTIVE
DOMAIN (the constants of the EDB and the program). The UNRESTRICTED semantics (`DerivesU`,
`DerivesAtU`, `DerivesSU`) lets a substitution be any list of integers of the right length, the
Herbrand semantics over all of `ℤ`. For a SAFE (range-restricted) program, where every variable of
a rule occurs in a positive body atom (`JoinClosure.safeB`, `safeRuleB` for positive rules), the two
coincide. "Safe" here is range restriction WITH DENSE variable numbering (codex round 4,
item 15): every index below the rule's variable bound occurs positively. A range-restricted rule
that skips an index is outside the hypothesis (and `datalog-check` refuses it):

  * `derives_iff_unrestricted`: `Derives P edb f ↔ DerivesU P edb f` (positive Datalog);
  * `derivesAt_iff_unrestricted`: per stratum, given a lower database whose arguments lie in `dom`
    and program constants in `dom`;
  * `derivesS_eq_unrestricted`: `DerivesS P strata edb = DerivesSU P strata edb` (stratified);
  * corollaries `verify_sound_unrestricted` and `verifyS_sound_unrestricted`: an accepted
    certificate for a safe program yields EXACTLY the facts of the standard semantics.

The proof direction "unrestricted ⇒ active" carries the invariant that every derived fact's
arguments are in the domain; safety turns that into "every substitution value is in the domain",
because each variable is read off a derived positive fact.

Falsifier (`unsafe_semantics_differ`): for the unsafe `p(X) :- q()` over `{q(), d(1)}`, `p(5)` is
derivable in the unrestricted semantics and NOT in the active-domain one, as a theorem. Safety is
needed.

Prior art: the coincidence for safe programs is textbook (Abiteboul-Hull-Vianu, ch. 12, "domain
independence"); what is here is its kernel-checked form for these definitions.

## Axiom hygiene
`#assert_all_clean` on every theorem. NEW file; imports read-only. -/
import Dregg2.Datalog.JoinClosure

namespace Dregg2.Datalog.SafeCoincidence

open Dregg2.Datalog.FixpointCert
open Dregg2.Datalog.StratifiedCert
open Dregg2.Datalog.JoinClosure
open Dregg2.Lightclient.MMR (mroot)

set_option autoImplicit false

/-! ## §1 — Instantiation lemmas. -/

theorem mapM_applyTerm {s : Subst} : ∀ (ts : List Term) (vs : List ℤ),
    ts.mapM (applyTerm s) = some vs →
    (∀ x ∈ vs, ∃ t ∈ ts, applyTerm s t = some x) ∧ (∀ t ∈ ts, ∃ v ∈ vs, applyTerm s t = some v)
  | [], vs, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simp
  | t :: ts, vs, h => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨v, hv, vs', hvs', rfl⟩ := h
    obtain ⟨h1, h2⟩ := mapM_applyTerm ts vs' hvs'
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨t, List.mem_cons_self, hv⟩
      · obtain ⟨t', ht', h'⟩ := h1 x hx; exact ⟨t', List.mem_cons_of_mem _ ht', h'⟩
    · intro t' ht'
      rcases List.mem_cons.mp ht' with rfl | ht'
      · exact ⟨v, List.mem_cons_self, hv⟩
      · obtain ⟨v', hv', h'⟩ := h2 t' ht'; exact ⟨v', List.mem_cons_of_mem _ hv', h'⟩

theorem applyAtom_args {s : Subst} {a : Atom} {f : Fact} (h : applyAtom s a = some f) :
    (∀ x ∈ f.2, ∃ t ∈ a.args, applyTerm s t = some x) ∧
    (∀ t ∈ a.args, ∃ v ∈ f.2, applyTerm s t = some v) := by
  unfold applyAtom at h
  obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.mp h
  exact mapM_applyTerm _ _ hvs

/-- If every argument of every positive instance is in `dom`, and every variable below `n` occurs
in a positive atom, then a substitution of length `n` takes its values in `dom`. -/
theorem subst_in_dom {s : Subst} {dom : List ℤ} {atoms : List Atom} {n : Nat}
    (hlen : s.length = n) (hcov : ∀ i, i < n → ∃ a ∈ atoms, Term.var i ∈ a.args)
    (hpos : ∀ a ∈ atoms, ∃ f, applyAtom s a = some f ∧ ∀ x ∈ f.2, x ∈ dom) :
    s ∈ substs dom n := by
  rw [mem_substs_iff]
  refine ⟨hlen, fun x hx => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  obtain ⟨a, ha, hva⟩ := hcov i (hlen ▸ hi)
  obtain ⟨f, hf, hfd⟩ := hpos a ha
  obtain ⟨v, hv, happ⟩ := (applyAtom_args hf).2 _ hva
  simp only [applyTerm, List.getElem?_eq_getElem hi, Option.some.injEq] at happ
  rw [happ]; exact hfd v hv

theorem const_mem_ruleConsts {r : Rule} {a : Atom} {c : ℤ} (ha : a ∈ r.head :: r.body)
    (hc : Term.const c ∈ a.args) : c ∈ ruleConsts r := by
  unfold ruleConsts
  exact List.mem_flatMap.mpr ⟨a, ha, List.mem_filterMap.mpr ⟨_, hc, rfl⟩⟩

/-- The head's arguments are substitution values or rule constants. -/
theorem head_in_dom {s : Subst} {dom : List ℤ} {r : Rule} {h : Fact} (hs : ∀ x ∈ s, x ∈ dom)
    (hc : ∀ c ∈ ruleConsts r, c ∈ dom) (hh : applyAtom s r.head = some h) : ∀ x ∈ h.2, x ∈ dom := by
  intro x hx
  obtain ⟨t, ht, happ⟩ := (applyAtom_args hh).1 x hx
  cases t with
  | var i => exact hs x (List.mem_of_getElem? happ)
  | const c =>
    simp only [applyTerm, Option.some.injEq] at happ
    subst happ
    exact hc _ (const_mem_ruleConsts List.mem_cons_self ht)

/-! ## §2 — Positive Datalog. -/

/-- Safety of a positive rule: every variable occurs in a body atom. -/
def safeRuleB (r : Rule) : Bool :=
  (List.range (varBound r)).all fun i => decide (i ∈ r.body.flatMap atomVars)

/-- **The unrestricted semantics** — substitutions are ANY integer lists of the rule's length. -/
inductive DerivesU (P : Program) (edb : List Fact) : Fact → Prop
  | edb {f : Fact} : f ∈ edb → DerivesU P edb f
  | fire {r : Rule} {s : Subst} {h : Fact} :
      r ∈ P → s.length = varBound r →
      (∀ b ∈ r.body, (applyAtom s b).isSome = true) →
      (∀ b ∈ r.body, ∀ f, applyAtom s b = some f → DerivesU P edb f) →
      applyAtom s r.head = some h → DerivesU P edb h

theorem derives_to_U {P : Program} {edb : List Fact} {f : Fact} (h : Derives P edb f) :
    DerivesU P edb f := by
  induction h with
  | edb h => exact DerivesU.edb h
  | fire hr hs hsome _ hhead ih =>
    exact DerivesU.fire hr ((mem_substs_iff _ _ _).mp hs).1 hsome ih hhead

theorem derivesU_to_active {P : Program} {edb : List Fact}
    (hsafe : ∀ r ∈ P, safeRuleB r = true) {f : Fact} (h : DerivesU P edb f) :
    Derives P edb f ∧ ∀ x ∈ f.2, x ∈ activeDomain P edb := by
  induction h with
  | edb h =>
    refine ⟨Derives.edb h, fun x hx => ?_⟩
    unfold activeDomain
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, h, hx⟩)
  | @fire r s hd hr hlen hsome _ hhead ih =>
    have hcov : ∀ i, i < varBound r → ∃ a ∈ r.body, Term.var i ∈ a.args := by
      intro i hi
      have := hsafe r hr
      unfold safeRuleB at this
      rw [List.all_eq_true] at this
      have hx := this i (List.mem_range.mpr hi)
      simp only [decide_eq_true_eq, List.mem_flatMap] at hx
      obtain ⟨a, ha, hia⟩ := hx
      exact ⟨a, ha, mem_atomVars.mp hia⟩
    have hpos : ∀ a ∈ r.body, ∃ f, applyAtom s a = some f ∧ ∀ x ∈ f.2, x ∈ activeDomain P edb := by
      intro a ha
      obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp (hsome a ha)
      exact ⟨f, hf, (ih a ha f hf).2⟩
    have hs := subst_in_dom hlen hcov hpos
    refine ⟨Derives.fire hr hs hsome (fun b hb f hf => (ih b hb f hf).1) hhead, ?_⟩
    refine head_in_dom (((mem_substs_iff _ _ _).mp hs).2) ?_ hhead
    intro c hc
    unfold activeDomain
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨r, hr, hc⟩)

/-- ⚑ **`derives_iff_unrestricted`** — for a safe positive program, the active-domain least
fixpoint is the unrestricted one. -/
theorem derives_iff_unrestricted {P : Program} {edb : List Fact}
    (hsafe : ∀ r ∈ P, safeRuleB r = true) (f : Fact) : Derives P edb f ↔ DerivesU P edb f :=
  ⟨derives_to_U, fun h => (derivesU_to_active hsafe h).1⟩

/-- ⚑ **`verify_sound_unrestricted`** — `FixpointCert.verify` acceptance for a safe program: the
database is EXACTLY the standard (unrestricted) least fixpoint. -/
theorem verify_sound_unrestricted (hash : List ℤ → ℤ) (st : Statement) (c : Certificate)
    (hsafe : ∀ r ∈ st.program, safeRuleB r = true) (h : verify hash st c = true) :
    mroot hash (flatten c.edb) = st.root ∧ ∃ db : List Fact, db.Nodup ∧
      (∀ f, f ∈ db ↔ DerivesU st.program c.edb f) ∧ countQ db st.pred = st.count := by
  obtain ⟨hr, db, hn, hm, hc⟩ := verify_sound hash st c h
  exact ⟨hr, db, hn, fun f => (hm f).trans (derives_iff_unrestricted hsafe f), hc⟩

/-! ## §3 — Stratified Datalog. -/

/-- The unrestricted stratum fixpoint. -/
inductive DerivesAtU (P : SProgram) (S : List Nat) (L : Fact → Prop) : Fact → Prop
  | base {f : Fact} : L f → DerivesAtU P S L f
  | fire {i : Nat} {r : SRule} {s : Subst} {h : Fact} :
      i ∈ S → P[i]? = some r → s.length = varBoundS r →
      (∀ a, Lit.pos a ∈ r.body → (applyAtom s a).isSome = true) →
      (∀ a, Lit.pos a ∈ r.body → ∀ f, applyAtom s a = some f → DerivesAtU P S L f) →
      (∀ a, Lit.neg a ∈ r.body → ∃ f, applyAtom s a = some f ∧ ¬ L f) →
      applyAtom s r.head = some h → DerivesAtU P S L h

def stratDbFromU (P : SProgram) : Strata → (Fact → Prop) → Fact → Prop
  | [], L => L
  | S :: rest, L => stratDbFromU P rest (DerivesAtU P S L)

/-- **The unrestricted stratified model.** -/
def DerivesSU (P : SProgram) (strata : Strata) (edb : List Fact) : Fact → Prop :=
  stratDbFromU P strata (· ∈ edb)

theorem derivesAt_to_U {P : SProgram} {dom : List ℤ} {S : List Nat} {L : Fact → Prop} {f : Fact}
    (h : DerivesAt P dom S L f) : DerivesAtU P S L f := by
  induction h with
  | base h => exact DerivesAtU.base h
  | fire hi hr hs hsome _ hneg hhead ih =>
    exact DerivesAtU.fire hi hr ((mem_substs_iff _ _ _).mp hs).1 hsome ih hneg hhead

theorem derivesAtU_to_active {P : SProgram} {dom : List ℤ} {S : List Nat} {L : Fact → Prop}
    (hsafe : ∀ r ∈ P, safeB r = true)
    (hL : ∀ f, L f → ∀ x ∈ f.2, x ∈ dom)
    (hc : ∀ r ∈ P, ∀ c ∈ ruleConsts r.toRule, c ∈ dom)
    {f : Fact} (h : DerivesAtU P S L f) : DerivesAt P dom S L f ∧ ∀ x ∈ f.2, x ∈ dom := by
  induction h with
  | base h => exact ⟨DerivesAt.base h, hL _ h⟩
  | @fire i r s hd hi hr hlen hsome _ hneg hhead ih =>
    have hrP : r ∈ P := List.mem_of_getElem? hr
    have hcov : ∀ j, j < varBoundS r → ∃ a ∈ posAtoms r, Term.var j ∈ a.args := by
      intro j hj
      have := hsafe r hrP
      unfold safeB at this
      rw [List.all_eq_true] at this
      have hx := this j (List.mem_range.mpr hj)
      simp only [decide_eq_true_eq, List.mem_flatMap] at hx
      obtain ⟨a, ha, hja⟩ := hx
      exact ⟨a, ha, mem_atomVars.mp hja⟩
    have hpos : ∀ a ∈ posAtoms r, ∃ f, applyAtom s a = some f ∧ ∀ x ∈ f.2, x ∈ dom := by
      intro a ha
      have ha' := mem_posAtoms.mp ha
      obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp (hsome a ha')
      exact ⟨f, hf, (ih a ha' f hf).2⟩
    have hs := subst_in_dom hlen hcov hpos
    refine ⟨DerivesAt.fire hi hr hs hsome (fun a ha f hf => (ih a ha f hf).1) hneg hhead, ?_⟩
    exact head_in_dom (((mem_substs_iff _ _ _).mp hs).2) (hc r hrP) hhead

/-- ⚑ **`derivesAt_iff_unrestricted`** — per stratum: for a safe program whose constants are in
`dom`, over a lower database whose arguments are in `dom`, the domain restriction changes nothing. -/
theorem derivesAt_iff_unrestricted {P : SProgram} {dom : List ℤ} {S : List Nat}
    {L : Fact → Prop} (hsafe : ∀ r ∈ P, safeB r = true) (hL : ∀ f, L f → ∀ x ∈ f.2, x ∈ dom)
    (hc : ∀ r ∈ P, ∀ c ∈ ruleConsts r.toRule, c ∈ dom) (f : Fact) :
    DerivesAt P dom S L f ↔ DerivesAtU P S L f :=
  ⟨derivesAt_to_U, fun h => (derivesAtU_to_active hsafe hL hc h).1⟩

theorem stratDb_coincide {P : SProgram} {dom : List ℤ} (hsafe : ∀ r ∈ P, safeB r = true)
    (hc : ∀ r ∈ P, ∀ c ∈ ruleConsts r.toRule, c ∈ dom) :
    ∀ (strata : Strata) (L : Fact → Prop), (∀ f, L f → ∀ x ∈ f.2, x ∈ dom) →
      stratDbFrom P dom strata L = stratDbFromU P strata L
  | [], L, _ => rfl
  | S :: rest, L, hL => by
    have heq : DerivesAt P dom S L = DerivesAtU P S L :=
      funext fun f => propext (derivesAt_iff_unrestricted hsafe hL hc f)
    have hL' : ∀ f, DerivesAt P dom S L f → ∀ x ∈ f.2, x ∈ dom :=
      fun f hf => (derivesAtU_to_active hsafe hL hc (derivesAt_to_U hf)).2
    simp only [stratDbFrom, stratDbFromU]
    rw [stratDb_coincide hsafe hc rest _ hL', heq]

/-- ⚑ **`derivesS_eq_unrestricted`** — for a safe stratified program, the active-domain
stratified model IS the unrestricted one. -/
theorem derivesS_eq_unrestricted {P : SProgram} (strata : Strata) (edb : List Fact)
    (hsafe : ∀ r ∈ P, safeB r = true) : DerivesS P strata edb = DerivesSU P strata edb := by
  unfold DerivesS DerivesSU
  refine stratDb_coincide hsafe ?_ strata _ ?_
  · intro r hr c hcr
    unfold activeDomainS activeDomain
    exact List.mem_append_right _
      (List.mem_flatMap.mpr ⟨r.toRule, List.mem_map.mpr ⟨r, hr, rfl⟩, hcr⟩)
  · intro f hf x hx
    unfold activeDomainS activeDomain
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨f, hf, hx⟩)

/-- ⚑ **`verifyS_sound_unrestricted`** — `verifyS` acceptance (hence `datalog-check` acceptance,
`verifyJ_verifyS`) for a safe program: the database is EXACTLY the standard stratified model. -/
theorem verifyS_sound_unrestricted (hash : List ℤ → ℤ) (st : SStatement) (c : SCertificate)
    (hsafe : ∀ r ∈ st.program, safeB r = true) (h : verifyS hash st c = true) :
    mroot hash (flatten c.edb) = st.root ∧ ∃ db : List Fact, db.Nodup ∧
      (∀ f, f ∈ db ↔ DerivesSU st.program st.strata c.edb f) ∧ countQ db st.pred = st.count := by
  obtain ⟨_, hr, db, hn, hm, hc⟩ := verifyS_sound hash st c h
  refine ⟨hr, db, hn, fun f => ?_, hc⟩
  rw [hm f, derivesS_eq_unrestricted st.strata c.edb hsafe]

/-- The executable's safety check is exactly the hypothesis: `verifyJ` acceptance gives the
standard semantics with no side condition. -/
theorem verifyJ_safe {hash : List ℤ → ℤ} {st : SStatement} {c : SCertificate}
    (h : verifyJ hash st c = true) : ∀ r ∈ st.program, safeB r = true := by
  intro r hr
  have hst : stratifiedB st.program st.strata = true := by
    unfold verifyJ at h; simp only [Bool.and_eq_true] at h; exact h.1.1.1
  obtain ⟨i, hi, T, hT, hiT⟩ := stratifiedB_cover hst hr
  unfold verifyJ at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨_, hrest⟩ := h
  cases hrun : runStrataJ st.program (domFast st.program c.edb) st.strata c.traces c.edb with
  | none => rw [hrun] at hrest; exact absurd hrest (by simp)
  | some db =>
    -- every stratum's closedJoinS passed, and it checks safeB of each of its rules
    have key : ∀ (strata : Strata) (ts : List Trace) (d d' : List Fact),
        runStrataJ st.program (domFast st.program c.edb) strata ts d = some d' →
        ∀ T ∈ strata, ∀ i ∈ T, ∀ r, st.program[i]? = some r → safeB r = true := by
      intro strata
      induction strata with
      | nil => intro _ _ _ _ T hT; simp at hT
      | cons S rest ih =>
        intro ts d d' hrun' T hT j hj r' hr'
        cases ts with
        | nil => simp [runStrataJ] at hrun'
        | cons t ts =>
          simp only [runStrataJ] at hrun'
          cases hrp : replayS st.program (domFast st.program c.edb) S d d t.rounds with
          | none => rw [hrp] at hrun'; exact absurd hrun' (by simp)
          | some d₁ =>
            rw [hrp] at hrun'
            simp only at hrun'
            by_cases hc : closedJoinS st.program S d d₁ = true
            · rw [if_pos hc] at hrun'
              rcases List.mem_cons.mp hT with rfl | hT
              · unfold closedJoinS at hc
                rw [List.all_eq_true] at hc
                have := hc j hj
                rw [hr'] at this
                simp only [Bool.and_eq_true] at this
                exact this.1
              · exact ih ts d₁ d' hrun' T hT j hj r' hr'
            · rw [if_neg hc] at hrun'; exact absurd hrun' (by simp)
    exact key _ _ _ _ hrun T hT i hiT r hi

/-- ⚑ **`verifyJ_sound_unrestricted`** — what `lake exe datalog-check` accepts is EXACTLY the
standard stratified model, with no side condition. -/
theorem verifyJ_sound_unrestricted (hash : List ℤ → ℤ) (st : SStatement) (c : SCertificate)
    (h : verifyJ hash st c = true) :
    mroot hash (flatten c.edb) = st.root ∧ ∃ db : List Fact, db.Nodup ∧
      (∀ f, f ∈ db ↔ DerivesSU st.program st.strata c.edb f) ∧ countQ db st.pred = st.count :=
  verifyS_sound_unrestricted hash st c (verifyJ_safe h) (verifyJ_verifyS hash st c h)

/-- ⚑ **`verifyJ_receipt`** — the receipt-level export for `lake exe datalog-check` (codex round 4,
item 17): root, the database EXACTLY the standard (unrestricted) stratified model, the count, and the
supported-model property of that same database, together. -/
theorem verifyJ_receipt (hash : List ℤ → ℤ) (st : SStatement) (c : SCertificate)
    (h : verifyJ hash st c = true) :
    stratifiedB st.program st.strata = true ∧ mroot hash (flatten c.edb) = st.root ∧
    ∃ db : List Fact, db.Nodup ∧ (∀ f, f ∈ db ↔ DerivesSU st.program st.strata c.edb f) ∧
      countQ db st.pred = st.count ∧
      ∀ f, f ∈ db ↔ (f ∈ c.edb ∨ ∃ r ∈ st.program,
        ∃ s ∈ substs (activeDomainS st.program c.edb) (varBoundS r), ruleFiresS r s db db = some f) := by
  obtain ⟨hst, hroot, db, hn, hm, hc, hsup⟩ := verifyS_receipt hash st c (verifyJ_verifyS hash st c h)
  refine ⟨hst, hroot, db, hn, fun f => ?_, hc, hsup⟩
  rw [hm f, derivesS_eq_unrestricted st.strata c.edb (verifyJ_safe h)]

/-! ## §4 — Falsifier: an unsafe rule, where the two semantics differ. -/

namespace Reference

open Dregg2.Datalog.JoinClosure.Reference (unsafeProg unsafeEdb unsafeRule)

/-- ⚑ **`unsafe_semantics_differ`** — `p(X) :- q()` over `{q(), d(1)}`: `p(5)` holds in the
unrestricted model and NOT in the active-domain one. Safety is needed. -/
theorem unsafe_semantics_differ :
    DerivesSU unsafeProg [[0]] unsafeEdb (2, [5]) ∧ ¬ DerivesS unsafeProg [[0]] unsafeEdb (2, [5]) := by
  refine ⟨?_, ?_⟩
  · show DerivesAtU unsafeProg [0] (· ∈ unsafeEdb) (2, [5])
    refine DerivesAtU.fire (i := 0) (r := unsafeRule) (s := [5]) (by simp) rfl (by decide) ?_ ?_ ?_
      (by decide)
    · intro a ha
      simp only [unsafeRule, List.mem_singleton, Lit.pos.injEq] at ha
      subst ha; decide
    · intro a ha f hf
      simp only [unsafeRule, List.mem_singleton, Lit.pos.injEq] at ha
      subst ha
      have h' : applyAtom [5] (⟨3, []⟩ : Atom) = some (3, []) := by decide
      rw [h'] at hf
      simp only [Option.some.injEq] at hf
      subst hf
      exact DerivesAtU.base (by decide)
    · intro a ha
      simp [unsafeRule] at ha
  · intro h
    change DerivesAt unsafeProg (activeDomainS unsafeProg unsafeEdb) [0] (· ∈ unsafeEdb) (2, [5]) at h
    cases h with
    | base hb => exact absurd hb (by decide)
    | @fire i r s _ hi hr hs _ _ _ hhead =>
      simp only [List.mem_singleton] at hi
      subst hi
      simp only [unsafeProg, List.getElem?_cons_zero, Option.some.injEq] at hr
      subst hr
      obtain ⟨hl, hd⟩ := (mem_substs_iff _ _ _).mp hs
      match s, hl with
      | [x], _ =>
        have hx : x = 5 := by simpa [applyAtom, applyTerm, unsafeRule] using hhead
        subst hx
        exact absurd (hd 5 List.mem_cons_self) (by decide)

#guard safeB unsafeRule = false

end Reference

#assert_all_clean [mapM_applyTerm, applyAtom_args, subst_in_dom, const_mem_ruleConsts, head_in_dom,
  derives_to_U, derivesU_to_active, derives_iff_unrestricted, verify_sound_unrestricted,
  derivesAt_to_U, derivesAtU_to_active, derivesAt_iff_unrestricted, stratDb_coincide,
  derivesS_eq_unrestricted, verifyS_sound_unrestricted, verifyJ_safe, verifyJ_sound_unrestricted,
  Reference.unsafe_semantics_differ, verifyJ_receipt]

end Dregg2.Datalog.SafeCoincidence
