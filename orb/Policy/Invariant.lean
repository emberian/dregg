/-
Policy — the declared-surface admission invariant.

`Wf` is the conjunction of the cold-plane safety clauses.  The headline results:

  * `served_on_declared_listener` (#1) — every observed response is attributed
    to a listener the live config declares; nothing is served on an undeclared
    listener.
  * `tls_required_never_plaintext` (#2) — a listener whose config sets
    `tlsRequired` never appears in the log with a plaintext response.
  * `reload_atomic` (#3) — a reload swaps the config snapshot as one whole
    value and moves nothing else: the bound set, TLS contexts, live counts and
    log are unchanged, so no observer sees a listener transiently unbound or
    double-bound, nor a config mixing the two snapshots.
  * `accept_respects_cap` (#4) — `accept` never raises a listener's live count
    above its declared cap.
  * `Wf` is inductive: `wf_init` at cold boot and `wf_step` across every
    transition, hence `reachable_wf` — `Wf` holds throughout every run.

`Wf` is exactly the property older notes called "confinement," here stated as
an ordinary transition-system invariant with no dramatization: the realized
surface never exceeds the declared surface, and stays that way under reload.
-/

import Policy.Model

namespace Policy

/-- The declared-surface admission invariant: the conjunction preserved by
every transition. -/
structure Wf (st : Running) : Prop where
  /-- No listener is bound twice (no double-bound listener). -/
  boundNodup : st.bound.Nodup
  /-- Every bound listener is declared by the live config. -/
  boundDeclared : ∀ lid ∈ st.bound, (st.cfg.listener? lid).isSome
  /-- Every bound listener's live count is within its declared cap. -/
  capBound : ∀ lid ∈ st.bound, ∀ l, st.cfg.listener? lid = some l → st.live lid ≤ l.connCap
  /-- An unbound listener carries no live connections. -/
  unboundZero : ∀ lid, lid ∉ st.bound → st.live lid = 0
  /-- A bound listener has an active TLS context exactly when it is declared
  TLS-required — the set of active contexts is exactly the declared surface. -/
  tlsCoupled : ∀ lid ∈ st.bound, (lid ∈ st.tlsCtx ↔ st.cfg.tlsListener lid)
  /-- Only bound listeners carry TLS contexts. -/
  tlsCtxBound : ∀ lid ∈ st.tlsCtx, lid ∈ st.bound
  /-- Every observation was served on a bound listener. -/
  servedOnBound : ∀ s ∈ st.served, s.lid ∈ st.bound
  /-- No observation on a TLS-required listener is plaintext. -/
  servedTls : ∀ s ∈ st.served, ∀ l,
    st.cfg.listener? s.lid = some l → l.tlsRequired = true → s.plaintext = false

/-! ### Small bridges -/

/-- The adoption Bool decides the adoption predicate. -/
theorem adoptableB_iff {c' : Config} {st : Running} :
    adoptableB c' st = true ↔ ∀ lid ∈ st.bound, c'.listener? lid = st.cfg.listener? lid := by
  simp only [adoptableB, List.all_eq_true, decide_eq_true_eq]

/-- `tlsListener` depends only on the listener lookup, so equal lookups agree. -/
theorem tlsListener_congr {c c' : Config} {lid : Nat}
    (he : c'.listener? lid = c.listener? lid) :
    c'.tlsListener lid ↔ c.tlsListener lid := by
  unfold Config.tlsListener; rw [he]

/-- Characterization of a successful serve: it is attributed to a bound
listener and never carries plaintext on a TLS-required listener. -/
theorem serveDecision_sound {lid : Nat} {rk : RouteKey} {pt : Bool}
    {st : Running} {s : Served} (h : serveDecision lid rk pt st = some s) :
    s.lid ∈ st.bound ∧
      (∀ l, st.cfg.listener? s.lid = some l → l.tlsRequired = true → s.plaintext = false) := by
  cases hl : st.cfg.listener? lid with
  | none => simp [serveDecision, hl] at h
  | some l =>
    simp only [serveDecision, hl] at h
    by_cases hb : lid ∈ st.bound
    · rw [if_neg (not_not_intro hb)] at h
      by_cases h1 : l.tlsRequired = true ∧ pt = true
      · rw [if_pos h1] at h; simp at h
      · rw [if_neg h1] at h
        by_cases h2 : l.tlsRequired = true ∧ lid ∉ st.tlsCtx
        · rw [if_pos h2] at h; simp at h
        · rw [if_neg h2] at h
          by_cases h3 : st.cfg.declaresRoute rk = false
          · rw [if_pos h3] at h; simp at h
          · rw [if_neg h3] at h
            -- emit branch: h : some ⟨lid, rk, pt⟩ = some s
            have hs : (⟨lid, rk, pt⟩ : Served) = s := Option.some.inj h
            subst hs
            refine ⟨hb, ?_⟩
            intro l' hl' htls
            -- s.lid = lid, so the lookup is `some l`; hence l' = l
            have hll : l = l' := by rw [hl] at hl'; exact Option.some.inj hl'
            subst hll
            -- pt = false: on a TLS-required listener, plaintext is refused (h1)
            cases pt with
            | false => rfl
            | true => exact absurd ⟨htls, rfl⟩ h1
    · rw [if_pos hb] at h; simp at h

/-! ### Preservation, one transition at a time -/

/-- `accept` preserves the invariant. -/
theorem wf_accept (lid : Nat) {st : Running} (h : Wf st) : Wf (accept lid st) := by
  cases hl : st.cfg.listener? lid with
  | none => simp only [accept, hl]; exact h
  | some l =>
    simp only [accept, hl]
    by_cases hg : lid ∈ st.bound ∧ st.live lid < l.connCap
    · rw [if_pos hg]
      exact {
        boundNodup := h.boundNodup
        boundDeclared := h.boundDeclared
        capBound := by
          intro k hk l' hl'
          by_cases hkl : k = lid
          · subst hkl
            have hll : l = l' := by rw [hl] at hl'; exact Option.some.inj hl'
            subst hll
            show bumpAt k st.live k ≤ l.connCap
            rw [bumpAt_self]
            have := hg.2
            omega
          · show bumpAt lid st.live k ≤ l'.connCap
            rw [bumpAt_other st.live hkl]
            exact h.capBound k hk l' hl'
        unboundZero := by
          intro k hk
          show bumpAt lid st.live k = 0
          have hkl : k ≠ lid := fun he => hk (he ▸ hg.1)
          rw [bumpAt_other st.live hkl]
          exact h.unboundZero k hk
        tlsCoupled := h.tlsCoupled
        tlsCtxBound := h.tlsCtxBound
        servedOnBound := h.servedOnBound
        servedTls := h.servedTls
      }
    · rw [if_neg hg]; exact h

/-- `serve` preserves the invariant. -/
theorem wf_serve (lid : Nat) (rk : RouteKey) (pt : Bool) {st : Running}
    (h : Wf st) : Wf (serve lid rk pt st) := by
  unfold serve
  cases hd : serveDecision lid rk pt st with
  | none => exact h
  | some s =>
    obtain ⟨hbnd, htls⟩ := serveDecision_sound hd
    exact {
      boundNodup := h.boundNodup
      boundDeclared := h.boundDeclared
      capBound := h.capBound
      unboundZero := h.unboundZero
      tlsCoupled := h.tlsCoupled
      tlsCtxBound := h.tlsCtxBound
      servedOnBound := by
        intro s' hs'
        rcases List.mem_cons.mp hs' with hh | hh
        · exact hh ▸ hbnd
        · exact h.servedOnBound s' hh
      servedTls := by
        intro s' hs' l hl' hreq
        rcases List.mem_cons.mp hs' with hh | hh
        · subst hh; exact htls l hl' hreq
        · exact h.servedTls s' hh l hl' hreq
    }

/-- `reload` preserves the invariant (the adoption precondition carries the
declared entry of every bound listener across the swap). -/
theorem wf_reload (c' : Config) {st : Running} (h : Wf st) : Wf (reload c' st) := by
  unfold reload
  by_cases hA : adoptableB c' st = true
  · rw [if_pos hA]
    have hado := adoptableB_iff.mp hA
    exact {
      boundNodup := h.boundNodup
      boundDeclared := by
        intro lid hlid
        rw [hado lid hlid]; exact h.boundDeclared lid hlid
      capBound := by
        intro lid hlid l hl
        rw [hado lid hlid] at hl
        exact h.capBound lid hlid l hl
      unboundZero := h.unboundZero
      tlsCoupled := by
        intro lid hlid
        rw [tlsListener_congr (hado lid hlid)]
        exact h.tlsCoupled lid hlid
      tlsCtxBound := h.tlsCtxBound
      servedOnBound := h.servedOnBound
      servedTls := by
        intro s hs l hl hreq
        rw [hado s.lid (h.servedOnBound s hs)] at hl
        exact h.servedTls s hs l hl hreq
    }
  · rw [if_neg hA]; exact h

/-- `adopt` preserves the invariant. -/
theorem wf_adopt (lid : Nat) {st : Running} (h : Wf st) : Wf (adopt lid st) := by
  unfold adopt
  by_cases hb : lid ∈ st.bound
  · rw [if_pos hb]; exact h
  · rw [if_neg hb]
    cases hl : st.cfg.listener? lid with
    | none => exact h
    | some l =>
      -- lid ∉ bound and lid ∉ tlsCtx (contexts live only on bound listeners)
      have hlidTls : lid ∉ st.tlsCtx := fun hc => hb (h.tlsCtxBound lid hc)
      exact {
        boundNodup := List.nodup_cons.mpr ⟨hb, h.boundNodup⟩
        boundDeclared := by
          intro k hk
          rcases List.mem_cons.mp hk with hh | hh
          · subst hh; rw [hl]; rfl
          · exact h.boundDeclared k hh
        capBound := by
          intro k hk l' hl'
          rcases List.mem_cons.mp hk with hh | hh
          · subst hh
            rw [h.unboundZero k hb]; exact Nat.zero_le _
          · exact h.capBound k hh l' hl'
        unboundZero := by
          intro k hk
          have hk' : k ∉ st.bound := fun hc => hk (List.mem_cons_of_mem lid hc)
          exact h.unboundZero k hk'
        tlsCoupled := by
          intro k hk
          rcases List.mem_cons.mp hk with hh | hh
          · -- k = lid
            subst hh
            have htl : st.cfg.tlsListener k ↔ l.tlsRequired = true := by
              unfold Config.tlsListener; rw [hl]; simp
            rw [htl]
            by_cases ht : l.tlsRequired = true
            · simp [ht]
            · simp only [ht, if_false]
              constructor
              · intro hc; exact absurd hc hlidTls
              · intro hc; exact absurd hc (by simp)
          · -- k ∈ bound, so k ≠ lid
            have hkl : k ≠ lid := fun he => hb (he ▸ hh)
            have hmem : (k ∈ (if l.tlsRequired then lid :: st.tlsCtx else st.tlsCtx))
                ↔ k ∈ st.tlsCtx := by
              by_cases ht : l.tlsRequired
              · simp [ht, List.mem_cons, hkl]
              · simp [ht]
            rw [hmem]
            exact h.tlsCoupled k hh
        tlsCtxBound := by
          intro k hk
          by_cases ht : l.tlsRequired
          · simp only [ht, if_true] at hk
            rcases List.mem_cons.mp hk with hh | hh
            · exact hh ▸ List.mem_cons_self _ _
            · exact List.mem_cons_of_mem lid (h.tlsCtxBound k hh)
          · simp only [ht, if_false] at hk
            exact List.mem_cons_of_mem lid (h.tlsCtxBound k hk)
        servedOnBound := by
          intro s hs
          exact List.mem_cons_of_mem lid (h.servedOnBound s hs)
        servedTls := h.servedTls
      }

/-! ### The invariant is inductive -/

/-- Every transition preserves `Wf`. -/
theorem wf_step {st st' : Running} (h : Wf st) (hs : Step st st') : Wf st' := by
  cases hs with
  | accept lid _ => exact wf_accept lid h
  | serve lid rk pt _ => exact wf_serve lid rk pt h
  | reload c' _ => exact wf_reload c' h
  | adopt lid _ => exact wf_adopt lid h

/-- `Wf` holds at cold boot. -/
theorem wf_init (c : Config) : Wf (init c) where
  boundNodup := by simp [init]
  boundDeclared := by intro lid hlid; simp [init] at hlid
  capBound := by intro lid hlid; simp [init] at hlid
  unboundZero := by intro lid _; rfl
  tlsCoupled := by intro lid hlid; simp [init] at hlid
  tlsCtxBound := by intro lid hlid; simp [init] at hlid
  servedOnBound := by intro s hs; simp [init] at hs
  servedTls := by intro s hs; simp [init] at hs

/-- **The invariant holds throughout every run.**  From a cold boot, every
reachable state satisfies `Wf`. -/
theorem reachable_wf {c : Config} {st : Running} (h : Reachable c st) : Wf st := by
  induction h with
  | init => exact wf_init c
  | step _ hstep ih => exact wf_step ih hstep

/-! ### The headline theorems -/

/-- **#1 — declared-surface attribution.**  Every observed response is
attributed to a listener the live config declares. -/
theorem served_on_declared_listener {st : Running} (h : Wf st) :
    ∀ s ∈ st.served, st.cfg.declaresListener s.lid := by
  intro s hs
  exact h.boundDeclared s.lid (h.servedOnBound s hs)

/-- **#2 — TLS enforcement.**  A listener the config declares TLS-required
never appears in the log with a plaintext response. -/
theorem tls_required_never_plaintext {st : Running} (h : Wf st) :
    ∀ s ∈ st.served, st.cfg.tlsListener s.lid → s.plaintext = false := by
  intro s hs htls
  obtain ⟨l, hl, hreq⟩ := htls
  exact h.servedTls s hs l hl hreq

/-- **#3 — reload atomicity.**  A reload swaps only the config snapshot, as one
whole value: the bound set, TLS contexts, live counts and observation log are
untouched (no listener is transiently unbound or double-bound), and the
observed config is either the new snapshot whole or the old snapshot whole —
never a field-wise mix. -/
theorem reload_atomic (c' : Config) (st : Running) :
    (reload c' st).bound = st.bound
  ∧ (reload c' st).tlsCtx = st.tlsCtx
  ∧ (reload c' st).live = st.live
  ∧ (reload c' st).served = st.served
  ∧ ((reload c' st).cfg = c' ∨ (reload c' st).cfg = st.cfg) := by
  unfold reload
  by_cases hA : adoptableB c' st = true
  · rw [if_pos hA]; exact ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩
  · rw [if_neg hA]; exact ⟨rfl, rfl, rfl, rfl, Or.inr rfl⟩

/-- Under the adoption precondition, the reload commits the new snapshot whole. -/
theorem reload_swaps_snapshot {c' : Config} {st : Running}
    (h : adoptableB c' st = true) : (reload c' st).cfg = c' := by
  unfold reload; rw [if_pos h]

/-- A reload never leaves a listener double-bound: the bound set is unchanged
and stays duplicate-free. -/
theorem reload_no_double_bind (c' : Config) {st : Running} (h : Wf st) :
    (reload c' st).bound.Nodup := (wf_reload c' h).boundNodup

/-- **#4 — admission bounds.**  `accept` never raises the target listener's
live count above its declared cap. -/
theorem accept_respects_cap (lid : Nat) {st : Running} (h : Wf st) :
    ∀ l, st.cfg.listener? lid = some l → (accept lid st).live lid ≤ l.connCap := by
  intro l hl
  simp only [accept, hl]
  by_cases hg : lid ∈ st.bound ∧ st.live lid < l.connCap
  · rw [if_pos hg]
    show bumpAt lid st.live lid ≤ l.connCap
    rw [bumpAt_self]
    have := hg.2
    omega
  · rw [if_neg hg]
    by_cases hbnd : lid ∈ st.bound
    · exact h.capBound lid hbnd l hl
    · rw [h.unboundZero lid hbnd]; exact Nat.zero_le _

end Policy
