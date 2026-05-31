/-
# Dregg2.Apps.OrbitalScreen — a CONSERVATIVE, continuous-time-SOUND collision screen.

This module replaces the *toy 1-D snapshot* `Verify` of `Dregg2.Apps.RightOfWay` with a
genuine **orbital relative-motion screen** whose "clear" verdict is sound on the **continuous
trajectory**, not merely at sampled times. It discharges the single substantive piece the
`right-of-way-response.md` flags as NOT inherited from the dregg2 core:

  > "The sharp risk is **discretization error**: a 'clear' verdict on *sampled* times that
  >  misses a between-samples closest approach. The soundness hinges on the screen being
  >  provably *conservative*."

The headline theorem (`screen_clear_imp_continuous_clear`): if the screen returns `clear`
for a pair over a maneuver step, then **no continuous-time conjunction occurs anywhere in the
step** — the screen OVER-APPROXIMATES the conjunction set, so a "clear" verdict is genuinely
sound against the between-samples closest approach.

================================================================================
## HONESTY LABEL — what is REAL physics, what is a modelling choice, what is the residual.
================================================================================

**REAL (proved, with teeth):**
  * The relative trajectory over one maneuver step is modelled as an **affine function of
    time** `d(t) = d0 + v·t` (per spatial axis). This is EXACTLY the structure of linearized
    relative orbital motion over a short step — the Clohessy–Wiltshire / Hill relative
    equations are linear, and over one screening step the closing motion is to first order
    `d0 + v·t`; equivalently it is the first-order (rectilinear) bound on any C¹ relative
    trajectory. For an affine trajectory the squared separation `‖d(t)‖²` is a quadratic
    (an upward parabola in `t`), so its minimum over the continuous interval `[0,T]` is
    attained at a *computable* time and we screen it EXACTLY — `screen_clear_imp_continuous_clear`
    is a real continuous-time soundness theorem, not a sampling.
  * A second, *strictly more conservative* screen (`coarseClear`) that needs only a velocity
    bound `‖v‖ ≤ vmax`: it certifies clearance via `sep(0) − vmax·T ≥ thr` and is sound for
    **any** trajectory whose relative speed is ≤ `vmax` over the step (`coarse_clear_imp_lipschitz_clear`),
    i.e. it does not even assume affinity — it is the honest Lipschitz fallback.

**MODELLING CHOICES (honest, labelled):**
  * Positions/velocities are rationals (`ℚ`) on a per-axis basis with `sq`-separation, so the
    whole screen is decidable and `#eval`-able. The geometry is the genuine 3-D Euclidean
    `‖·‖²`; we never approximate the metric.
  * "One maneuver step" is the screening window `[0,T]`. A real deployment screens a sequence
    of steps (a propagated ephemeris); chaining is exactly the dregg2 `chained_sound`
    invariant-lifting shape and is OUT OF SCOPE here (it is inherited, not re-proved).

**THE RESIDUAL (stated precisely, never faked):**
  * Real orbital relative motion is NOT globally affine — over long horizons the CW solution
    has trigonometric terms (the `n·t` secular + oscillatory parts). The affine model is the
    first-order truth over ONE short step; for a longer step the HONEST screen is the
    `coarseClear` Lipschitz bound (sound for any speed-bounded trajectory) with `vmax` the
    max relative speed over the step. We do NOT claim the affine screen is exact for a full
    orbit — we claim it is exact for the affine model and conservative-sound (via `coarseClear`)
    for any speed-bounded continuous trajectory. Upgrading to a curvature-aware bound (a second
    derivative / `n²`-term envelope) is the next refinement and is flagged OPEN below.

Zero `sorry`/`admit`/`native_decide`/`axiom`. Keystones `#assert_axioms`-pinned.
-/
import Mathlib.Tactic
import Dregg2.Tactics

namespace Dregg2.Apps.OrbitalScreen

/-! ## 1. Geometry — 3-D relative state as rationals, with squared separation.

We work with the **relative** state of an object pair (object B relative to object A): a
3-vector position `d` and 3-vector relative velocity `v`. Squared Euclidean separation is the
genuine metric; we keep it squared to stay in `ℚ` (no `sqrt`). The conjunction threshold is
likewise carried squared (`thrSq`). -/

/-- A 3-D vector of rationals (a relative position or velocity in the local-vertical /
local-horizontal Hill frame). -/
structure Vec3 where
  /-- radial / x component -/
  x : ℚ
  /-- along-track / y component -/
  y : ℚ
  /-- cross-track / z component -/
  z : ℚ
deriving Repr, DecidableEq

namespace Vec3

/-- Vector addition. -/
def add (a b : Vec3) : Vec3 := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

/-- Scalar multiple `t • v`. -/
def smul (t : ℚ) (v : Vec3) : Vec3 := ⟨t * v.x, t * v.y, t * v.z⟩

/-- Squared Euclidean norm `‖v‖²` (kept squared to stay rational). -/
def normSq (v : Vec3) : ℚ := v.x ^ 2 + v.y ^ 2 + v.z ^ 2

theorem normSq_nonneg (v : Vec3) : 0 ≤ v.normSq := by
  unfold normSq; positivity

end Vec3

/-! ## 2. The relative trajectory over a maneuver step.

Over one screening step, the relative position of the pair is the **affine** function
`rel d0 v t = d0 + t • v`. As explained in the header this is the first-order (rectilinear)
relative motion — the exact structure of the linearized CW/Hill relative dynamics over a
short step, and the honest first-order truth for any C¹ relative trajectory. -/

/-- The relative position at time `t` into the step: `d(t) = d0 + t·v`. -/
def rel (d0 v : Vec3) (t : ℚ) : Vec3 := Vec3.add d0 (Vec3.smul t v)

/-- The squared separation of the pair at time `t`, `sepSq d0 v t = ‖d0 + t·v‖²`. As a
function of `t` this is the quadratic `a·t² + b·t + c` with `a = ‖v‖² ≥ 0`,
`b = 2⟨d0,v⟩`, `c = ‖d0‖²` — an upward parabola. -/
def sepSq (d0 v : Vec3) (t : ℚ) : ℚ := (rel d0 v t).normSq

/-- The quadratic coefficients of `t ↦ sepSq d0 v t`. -/
def aCoef (v : Vec3) : ℚ := v.normSq
/-- The linear coefficient `2⟨d0, v⟩`. -/
def bCoef (d0 v : Vec3) : ℚ := 2 * (d0.x * v.x + d0.y * v.y + d0.z * v.z)
/-- The constant coefficient `‖d0‖²`. -/
def cCoef (d0 : Vec3) : ℚ := d0.normSq

/-- **`sepSq` IS the quadratic `a t² + b t + c` (PROVED).** Pins the geometric squared
separation to its quadratic-in-`t` form, the algebraic fact the soundness rests on. -/
theorem sepSq_eq_quadratic (d0 v : Vec3) (t : ℚ) :
    sepSq d0 v t = aCoef v * t ^ 2 + bCoef d0 v * t + cCoef d0 := by
  unfold sepSq rel Vec3.add Vec3.smul Vec3.normSq aCoef bCoef cCoef Vec3.normSq
  ring

theorem aCoef_nonneg (v : Vec3) : 0 ≤ aCoef v := Vec3.normSq_nonneg v

/-! ## 3. The EXACT continuous-time minimum of the squared separation over `[0,T]`.

For an upward parabola `q(t) = a t² + b t + c` with `a ≥ 0`, the unconstrained minimizer is
`t* = -b/(2a)`. On the interval `[0,T]` the minimum is at `clamp t* [0,T]`. We compute that
clamp and prove it is a genuine lower bound on `q` over the WHOLE interval — this is the move
that turns a sampled check into a continuous one. -/

/-- The unconstrained parabola vertex `t* = -b / (2a)` (when `a > 0`); for `a = 0` (no
relative motion) the separation is constant and the vertex is irrelevant — we return `0`. -/
def vertex (d0 v : Vec3) : ℚ :=
  let a := aCoef v
  if a = 0 then 0 else (- bCoef d0 v) / (2 * a)

/-- The **closest-approach time** over the step `[0,T]`: the vertex clamped into `[0,T]`. The
continuous minimum of `sepSq` over `[0,T]` is attained here. -/
def tca (d0 v : Vec3) (T : ℚ) : ℚ := max 0 (min T (vertex d0 v))

/-- **`sepSq_min_at_tca` — the closest-approach value is a LOWER BOUND on the continuous
separation over the whole step (PROVED).** For every `t ∈ [0,T]`, `sepSq d0 v t ≥ sepSq d0 v
(tca d0 v T)`. This is the heart: the value at the clamped vertex bounds the separation at
EVERY continuous time in the step — so checking one point (the `tca`) certifies the whole
interval. -/
theorem sepSq_min_at_tca (d0 v : Vec3) (T : ℚ) (t : ℚ) (h0 : 0 ≤ t) (hT : t ≤ T) :
    sepSq d0 v (tca d0 v T) ≤ sepSq d0 v t := by
  rw [sepSq_eq_quadratic, sepSq_eq_quadratic]
  set a := aCoef v with ha
  set b := bCoef d0 v with hb
  set c := cCoef d0 with hc
  have hann : 0 ≤ a := aCoef_nonneg v
  -- Let `tm := tca`. We show `a tm² + b tm + c ≤ a t² + b t + c`, i.e.
  -- `0 ≤ a(t² - tm²) + b(t - tm) = (t - tm)·(a(t+tm) + b)`.
  set tm := tca d0 v T with htm
  have hkey : a * t ^ 2 + b * t + c - (a * tm ^ 2 + b * tm + c)
      = (t - tm) * (a * (t + tm) + b) := by ring
  -- It suffices to show the RHS factorization is `≥ 0`.
  rw [← sub_nonneg]
  rw [show a * t ^ 2 + b * t + c - (a * tm ^ 2 + b * tm + c)
        = (t - tm) * (a * (t + tm) + b) from hkey]
  -- Two cases on `a = 0` vs `a > 0`.
  rcases eq_or_lt_of_le hann with hazero | hapos
  · -- `a = 0`: parabola degenerates to a line `b t + c`. Then `tm = max 0 (min T 0) = 0`
    -- since `vertex = 0` when `a = 0`. The line's min over `[0,T]` is at an endpoint;
    -- with `tm = 0` we need `(t - 0)·(0 + b) ≥ 0`, i.e. `t·b ≥ 0`. This need NOT hold for a
    -- line with `b < 0` (min is at `t = T`, not `0`). So the degenerate `a = 0` clamp choice
    -- `vertex := 0` is WRONG for a falling line; we instead observe `a = 0` means `‖v‖² = 0`,
    -- hence `v = 0`, hence `b = 2⟨d0,v⟩ = 0`, so the line is CONSTANT and the bound is trivial.
    have hv0 : v.normSq = 0 := by rw [ha, aCoef] at hazero; exact hazero.symm
    have hvx : v.x = 0 ∧ v.y = 0 ∧ v.z = 0 := by
      unfold Vec3.normSq at hv0
      refine ⟨?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg v.x, sq_nonneg v.y, sq_nonneg v.z]
    have hb0 : b = 0 := by
      rw [hb, bCoef]; obtain ⟨hx, hy, hz⟩ := hvx; rw [hx, hy, hz]; ring
    rw [hb0, ← hazero]; simp
  · -- `a > 0`: genuine parabola. `tm = max 0 (min T t*)` with `t* = -b/(2a)`.
    -- Show `(t - tm)·(a(t+tm)+b) ≥ 0` by sign analysis around the vertex `t* = -b/(2a)`.
    -- Note `a(t+tm)+b = a·t + (a·tm + b)`. Express via the vertex: `a·t* = -b/2`.
    have hane : a ≠ 0 := ne_of_gt hapos
    -- `vertex = -b/(2a)`, so `2a·vertex = -b`, i.e. `a·vertex + (a·vertex + b) = a·vertex`,
    -- cleanly: `2*a*vertex + b = 0`.
    have ha2 : (2 : ℚ) * a ≠ 0 := by
      have : (0 : ℚ) < 2 * a := by linarith
      exact ne_of_gt this
    have hvtx : 2 * a * vertex d0 v + b = 0 := by
      have hvval : vertex d0 v = (- b) / (2 * a) := by
        unfold vertex
        rw [if_neg (by rw [← ha]; exact hane), ← ha, ← hb]
      rw [hvval]
      rw [mul_div_assoc'] -- 2*a*(-b)/(2*a) + b
      rw [mul_comm (2 * a) (-b), mul_div_assoc, div_self ha2, mul_one]
      ring
    -- Let `w := vertex d0 v`. `tm = max 0 (min T w)`.
    set w := vertex d0 v with hw
    -- We do the standard clamp sign argument.
    -- Case A: `w ≤ 0`. Then `tm = max 0 (min T w)`. Since `w ≤ 0 ≤ T`, `min T w = w ≤ 0`,
    --   so `tm = max 0 w = 0`. Need `(t-0)(a(t+0)+b) = t(at+b) ≥ 0`. Since `2aw + b = 0`,
    --   `b = -2aw ≥ 0` (as `w ≤ 0, a > 0`), and `t ≥ 0`, so `at + b ≥ 0`, product ≥ 0.
    -- Case B: `w ≥ T`. Then `min T w = T`, `tm = max 0 T = T` (T ≥ 0 since `0 ≤ t ≤ T`).
    --   Need `(t - T)(a(t+T)+b) ≥ 0`. `t - T ≤ 0`. And `a(t+T)+b`: since `b = -2aw ≤ -2aT`
    --   (w ≥ T, a>0), `a(t+T)+b ≤ a(t+T) - 2aT = a(t - T) ≤ 0`. Product of two ≤0 is ≥0.
    -- Case C: `0 ≤ w ≤ T`. Then `tm = w`. `a(t+w)+b = a t + (a w + b) = a t + (a w + b)`.
    --   `2aw + b = 0 ⇒ aw + b = -aw ⇒ aw = -(aw+b)`... cleaner: `a(t+w)+b = a t - a w` (since
    --   `aw + b = -aw`). Wait: `a(t+w)+b = at + aw + b = at + (aw + b)`. From `2aw+b=0`,
    --   `aw + b = -aw`. So `a(t+w)+b = at - aw = a(t-w)`. Then `(t-w)·a(t-w) = a(t-w)² ≥ 0`. ✓
    have hTnn : 0 ≤ T := le_trans h0 hT
    rcases lt_or_ge w 0 with hwlt0 | hwge0
    · -- Case A: `w < 0`, so `tm = 0`.
      have hwle : w ≤ 0 := le_of_lt hwlt0
      have htm0 : tm = 0 := by
        rw [htm, tca, ← hw]
        have : min T w = w := min_eq_right (le_trans hwle hTnn)
        rw [this, max_eq_left hwle]
      rw [htm0]
      have hbnn : 0 ≤ b := by nlinarith [hvtx, hapos, hwle]
      have : 0 ≤ a * (t + 0) + b := by nlinarith [hapos, h0, hbnn]
      have ht0 : 0 ≤ t - 0 := by linarith
      positivity
    · -- `w ≥ 0`. Split on `w ≥ T` (Case B) vs `w < T` (Case C).
      rcases lt_or_ge w T with hwlt | hwge
      · -- Case C: `0 ≤ w < T`, so `tm = w`.
        have htmw : tm = w := by
          rw [htm, tca, ← hw]
          have h1 : min T w = w := min_eq_right (le_of_lt hwlt)
          rw [h1, max_eq_right hwge0]
        rw [htmw]
        -- `a(t+w)+b = a(t-w)` via `aw + b = -aw`
        have hfac : a * (t + w) + b = a * (t - w) := by nlinarith [hvtx]
        rw [hfac]
        nlinarith [sq_nonneg (t - w), hapos]
      · -- Case B: `w ≥ T`, so `tm = T`.
        have htmT : tm = T := by
          rw [htm, tca, ← hw]
          have : min T w = T := min_eq_left hwge
          rw [this, max_eq_right hTnn]
        rw [htmT]
        have hle : t - T ≤ 0 := by linarith
        -- `a(t+T)+b ≤ 0`
        have hb_le : a * (t + T) + b ≤ 0 := by nlinarith [hvtx, hapos, hwge]
        nlinarith [mul_nonneg (neg_nonneg.mpr hle) (neg_nonneg.mpr hb_le)]

/-! ## 4. THE SCREEN — `clear` iff the continuous minimum separation clears the threshold.

`screen` checks the closest-approach squared separation (at the `tca`) against the squared
threshold. By `sepSq_min_at_tca`, a `clear` verdict bounds the separation at EVERY continuous
time in the step. -/

/-- The **conservative orbital screen** for a pair `(d0, v)` over step `[0,T]` at squared
threshold `thrSq`. Returns `true` (clear) iff the squared separation at the closest-approach
time is `≥ thrSq`. Decidable, total, `#eval`-able — the VERIFY side of the seam, now carrying
real continuous-time-sound physics. -/
def screen (d0 v : Vec3) (T thrSq : ℚ) : Bool :=
  decide (thrSq ≤ sepSq d0 v (tca d0 v T))

/-- **`screen_clear_imp_continuous_clear` — THE KEYSTONE (PROVED).** If the screen returns
`clear` (`true`) for a pair over the step `[0,T]`, then at EVERY continuous time `t ∈ [0,T]`
the squared separation is at least the threshold — there is NO between-samples conjunction.
The screen OVER-APPROXIMATES the conjunction set: a `clear` verdict is sound on the continuous
trajectory, not merely at sampled times. This is the real-physics content `referee_sound`
carries when this `screen` is plugged in at the verify seam. -/
theorem screen_clear_imp_continuous_clear
    (d0 v : Vec3) (T thrSq : ℚ) (hscreen : screen d0 v T thrSq = true)
    (t : ℚ) (h0 : 0 ≤ t) (hT : t ≤ T) :
    thrSq ≤ sepSq d0 v t := by
  unfold screen at hscreen
  have hmin : thrSq ≤ sepSq d0 v (tca d0 v T) := by simpa using of_decide_eq_true hscreen
  exact le_trans hmin (sepSq_min_at_tca d0 v T t h0 hT)

/-- **`screen_clear_imp_no_conjunction` — the negative form (PROVED).** A `clear` verdict
means there is no continuous time in the step at which the pair is in conjunction (separation
strictly below threshold). This is the form a referee consumes: "clear ⇒ no conjunction
anywhere in the maneuver step." -/
theorem screen_clear_imp_no_conjunction
    (d0 v : Vec3) (T thrSq : ℚ) (hscreen : screen d0 v T thrSq = true) :
    ¬ ∃ t : ℚ, 0 ≤ t ∧ t ≤ T ∧ sepSq d0 v t < thrSq := by
  rintro ⟨t, h0, hT, hlt⟩
  exact absurd (screen_clear_imp_continuous_clear d0 v T thrSq hscreen t h0 hT) (not_le.mpr hlt)

/-! ## 5. TEETH — the screen catches a between-samples conjunction the sampler MISSES.

This is the whole point. We exhibit a pair that is CLEAR at both endpoints `t=0` and `t=T` but
has a true conjunction strictly between them — a sampler at `{0,T}` says "clear" (UNSOUND), but
our continuous screen says "NOT clear" (SOUND). -/

/-- A crossing pair: at `t=0` it is at radial separation `10` closing along-track at velocity
`-2` per unit time; over a step of `T = 10` it passes through the origin-ish region. Concretely
`d0 = (0, 10, 0)`, `v = (0, -2, 0)`: `d(t) = (0, 10 - 2t, 0)`, which hits `(0,0,0)` at `t = 5`
— a dead-center conjunction in the middle of the step. -/
def crossingD0 : Vec3 := ⟨0, 10, 0⟩
/-- The along-track closing velocity of the crossing pair. -/
def crossingV  : Vec3 := ⟨0, -2, 0⟩
/-- The step length over which the crossing happens. -/
def crossingT  : ℚ := 10
/-- Squared threshold `thrSq = 25` (a `5`-unit miss-distance threshold). -/
def crossingThrSq : ℚ := 25

/-- **The naive endpoint sampler is FOOLED (PROVED).** At `t=0` separation² is `100 ≥ 25` and
at `t=T=10` separation² is `(10 - 20)² = 100 ≥ 25` — BOTH endpoints clear. A sampler checking
only `{0, T}` returns "clear". -/
theorem endpoints_look_clear :
    crossingThrSq ≤ sepSq crossingD0 crossingV 0
      ∧ crossingThrSq ≤ sepSq crossingD0 crossingV crossingT := by
  refine ⟨?_, ?_⟩ <;>
    simp only [sepSq, rel, Vec3.add, Vec3.smul, Vec3.normSq, crossingD0, crossingV,
      crossingThrSq, crossingT] <;> norm_num

/-- **But there IS a real mid-step conjunction (PROVED).** At `t=5` the pair is at the origin,
separation² `= 0 < 25` — a genuine collision the endpoint sampler missed. -/
theorem midstep_conjunction_exists :
    sepSq crossingD0 crossingV 5 < crossingThrSq := by
  unfold sepSq rel Vec3.add Vec3.smul Vec3.normSq crossingD0 crossingV crossingThrSq; norm_num

/-- **THE TEETH — the continuous screen REJECTS the crossing pair (PROVED).** Unlike the
endpoint sampler, our `screen` returns `false`: the closest-approach time `tca` lands at the
true mid-step minimum and the screen sees separation² `< 25`. So `screen = clear` is genuinely
stronger than "clear at the samples" — it is sound against the between-samples closest
approach. (Were the screen UNSOUND it would have returned `true` here like the sampler.) -/
theorem screen_rejects_crossing :
    screen crossingD0 crossingV crossingT crossingThrSq = false := by
  unfold screen tca vertex aCoef bCoef sepSq rel Vec3.add Vec3.smul Vec3.normSq
    crossingD0 crossingV crossingThrSq crossingT
  norm_num

/-! ## 6. The coarse Lipschitz screen — the HONEST general-trajectory fallback.

The affine screen is exact for the affine model. For a trajectory that is only known to be
*speed-bounded* (`‖d'(t)‖ ≤ vmax` over the step — a Lipschitz bound, valid for ANY C¹ relative
motion including the full nonlinear CW solution over a bounded step), the conservative screen
is the triangle-inequality bound: `sep(t) ≥ sep(0) − vmax·t ≥ sep(0) − vmax·T`. If
`sep(0) − vmax·T ≥ thr` then the pair is clear for the whole step regardless of the trajectory
shape. We prove this *linear-separation* lower bound; it is strictly more conservative than the
affine screen but assumes less. -/

/-- The **coarse Lipschitz screen**: clear iff `sep0 − vmax·T ≥ thr`, working with the linear
(non-squared) separation lower bound `sep0` and a speed bound `vmax ≥ 0` over `[0,T]`. -/
def coarseClear (sep0 vmax T thr : ℚ) : Bool :=
  decide (thr ≤ sep0 - vmax * T)

/-- **`coarse_clear_imp_lipschitz_clear` — the conservative Lipschitz bound (PROVED).** Given a
trajectory whose linear separation satisfies the reverse-triangle bound `sep(t) ≥ sep0 −
vmax·t` over the step (the content of a `vmax` speed bound), if `coarseClear` is `true` then
`sep(t) ≥ thr` for every `t ∈ [0,T]`. This is sound for ANY speed-bounded continuous
trajectory — not just the affine model — and is the honest fallback when affinity cannot be
assumed. -/
theorem coarse_clear_imp_lipschitz_clear
    (sep0 vmax T thr : ℚ) (hv : 0 ≤ vmax)
    (sepFn : ℚ → ℚ) (hlip : ∀ t, 0 ≤ t → t ≤ T → sep0 - vmax * t ≤ sepFn t)
    (hclear : coarseClear sep0 vmax T thr = true)
    (t : ℚ) (h0 : 0 ≤ t) (hT : t ≤ T) :
    thr ≤ sepFn t := by
  unfold coarseClear at hclear
  have hbound : thr ≤ sep0 - vmax * T := by simpa using of_decide_eq_true hclear
  have hmono : sep0 - vmax * T ≤ sep0 - vmax * t := by
    have : vmax * t ≤ vmax * T := mul_le_mul_of_nonneg_left hT hv
    linarith
  exact le_trans hbound (le_trans hmono (hlip t h0 hT))

/-! ## 7. `#eval` witnesses — the screen, runnable.

A clear pair accepted; the crossing pair (clear at endpoints) REJECTED; the coarse screen. -/

/-- A genuinely-clear pair: parallel tracks `8` apart, `thrSq = 25` (miss distance 5). -/
def clearD0 : Vec3 := ⟨8, 0, 0⟩
/-- Velocity of the clear pair: purely along-track, so separation never drops. -/
def clearV  : Vec3 := ⟨0, 3, 0⟩

#eval screen clearD0 clearV 10 25                       -- true  (separation never closes; CLEAR)
#eval screen crossingD0 crossingV crossingT crossingThrSq -- false (mid-step crossing caught)
-- The closest-approach time of the crossing pair is mid-step (≈ 5), NOT an endpoint:
#eval tca crossingD0 crossingV crossingT                -- 5   (the between-samples minimum)
#eval sepSq crossingD0 crossingV 0                      -- 100 (endpoint: clear)
#eval sepSq crossingD0 crossingV 5                      -- 0   (mid-step: COLLISION the sampler missed)
#eval sepSq crossingD0 crossingV 10                     -- 100 (endpoint: clear)
-- The coarse Lipschitz screen: sep0=8, vmax=0.5, T=10, thr=2  →  8 - 5 = 3 ≥ 2 ⇒ clear.
#eval coarseClear 8 (1/2) 10 2                          -- true
-- vmax=1 closes faster: 8 - 10 = -2 < 2 ⇒ not clear (conservative rejection).
#eval coarseClear 8 1 10 2                              -- false

/-! ## 8. Axiom hygiene + the OPEN refinement. -/

#assert_axioms sepSq_eq_quadratic
#assert_axioms sepSq_min_at_tca
#assert_axioms screen_clear_imp_continuous_clear
#assert_axioms screen_clear_imp_no_conjunction
#assert_axioms endpoints_look_clear
#assert_axioms midstep_conjunction_exists
#assert_axioms screen_rejects_crossing
#assert_axioms coarse_clear_imp_lipschitz_clear

/-
OPEN (the curvature refinement, honestly flagged). The affine screen is EXACT for the affine
relative model and the `coarseClear` Lipschitz screen is SOUND for any speed-bounded
trajectory. The remaining gap to a fully-general continuous-time guarantee over a LONG step is
the **curvature term**: the true CW relative solution adds bounded oscillatory/secular terms
`O(n²·t²)` (n = mean motion). A curvature-aware screen would bound `sepSq(t)` below by the
affine value minus a `½·κ·t²` envelope (κ a second-derivative bound), recovering an exact
continuous guarantee without assuming affinity. That second-order envelope is the next
refinement; it is NOT proved here. The honest current guarantee: EXACT for affine, CONSERVATIVE
(Lipschitz) for speed-bounded — never a sampled check masquerading as a continuous one.
-/

end Dregg2.Apps.OrbitalScreen
