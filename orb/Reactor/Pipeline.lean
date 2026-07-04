import Reactor.Serialize

/-!
# Reactor.Pipeline — the modular stage pipeline (the extensible serve calculus)

The deployed serve (`Reactor.Deploy.deployResp` / `serveGuarded`) is a MONOLITH:
adding a byte-driving feature means editing one shared function. This file
replaces that response path with an extensible **fold over a `List Stage`** — the
middleware onion (`Middleware.lean`) promoted to the deployed serve as the primary
structure. Adding a feature becomes a disjoint one-file operation: a new
`Reactor/Stage/<Lib>.lean` defining `<lib>Stage : Stage` plus one byte-effect
theorem via `pipeline_stage_effect`, appended to the registered `deployStages`.

## The abstraction

A `Stage` wraps the handler on both sides of the exchange:

* `onRequest : Ctx → StageStep` — the REQUEST phase, run in list order. A stage may
  `.respond r` (a gate: short-circuit with a response, skipping the handler and
  every later stage) or `.continue c'` (pass through, optionally transforming the
  context).
* `onResponse : Ctx → ResponseBuilder → ResponseBuilder` — the RESPONSE phase, run
  in REVERSE list order (the onion): the outermost stage sees the request first and
  the response last. The response is threaded as an AFFINE `ResponseBuilder` (§ The
  affine response builder) — one accumulating cell mutated in place, NOT a fresh
  `Response` record rebuilt per stage — so N stages cost one build, not N
  reallocations.

`Ctx` carries the parsed request, the raw input bytes the deployed serve drives
its plan off of, and an extensible attribute bag for accumulated state (auth
identity, matched route, …) so a new stage never has to widen the shared struct.

## The composition calculus (proven ONCE here — the reusable kernel)

* `pipeline_empty`            — `runPipeline [] h c = h c` (identity).
* `pipeline_cons`             — the defining onion recursion (head/tail factoring).
* `pipeline_gate_short_circuits` — a gate's `.respond r` IS the output; the
  handler and later stages do not contribute (`pipeline_gate_ignores_rest` states
  the independence directly).
* `pipeline_stage_effect`     — a passing stage's `onResponse` wraps the tail
  result: THE hook each lib's byte-effect theorem instantiates.
* `pipeline_onion_order`      — `onResponse` runs in the exact reverse of
  `onRequest`.

Every theorem is generic over arbitrary stages/handler/ctx and closes by
`rfl`/`rw`, so it depends on no axioms beyond `{propext, Quot.sound}`.

See `exampleStage` / `exampleStage_header_present` at the end for the exact,
kernel-checked pattern a fan-out lib copies.
-/

namespace Reactor.Pipeline

open Proto (Bytes Request)

/-! ## The pipeline data -/

/-- The serve context threaded through the pipeline. Carries the dispatched
request, the raw input bytes (the deployed plan/DNS/proxy pass is driven off
these), and an extensible attribute bag so a new stage can stash accumulated
state (matched route, auth identity, rate token, …) WITHOUT widening this shared
structure — the extension point that keeps stage files disjoint. -/
structure Ctx where
  /-- The raw request bytes the deployed serve received (drives `deploySubs`). -/
  input : Bytes
  /-- The dispatched request the stages gate/transform on. -/
  req : Request
  /-- Extensible accumulated state; new stages read/write their own keys. -/
  attrs : List (String × Bytes) := []

/-- The outcome of a stage's request phase: either short-circuit the whole
pipeline with a response (a gate), or pass control inward with a — possibly
transformed — context. -/
inductive StageStep where
  /-- Gate: answer now with `r`; the handler and every later stage are skipped. -/
  | respond (r : Response)
  /-- Pass through to the next stage with context `c`. -/
  | continue (c : Ctx)

/-! ## The affine response builder

A build-once-in-place response writer builds the response **once, in place**: one
pooled buffer extended in place and a single header map mutated with insert — the
whole response phase allocates nothing steady-state. A functional
`onResponse : Ctx → Response → Response` that does
`{ r with headers := r.headers ++ [x] }` per stage instead reallocates the whole
`Response` record and copies the header list once PER STAGE (~N× per request for N
response-transform stages) — the perf gap this builder closes.

`ResponseBuilder` closes that gap in the MODEL: a single accumulating cell (`acc`
— the pooled buffer) threaded through the response phase, with append-only /
overwrite operations (`addHeader` = a header push, `appendBody` = an in-place
buffer extend, `setStatus`/`setReason` = one field store, `mapResp` = a
whole-header-map rewrite as an in-place insert/strip sequence).

The discipline is **AFFINE**: each builder value is *consumed exactly once* — every
op takes a builder by value and returns the next builder, and the finalizer
`build` consumes it and hands back a non-builder `Response`, so no builder is ever
read-then-reused (`BuildLife`/`built_absorbing` below state the "no reuse after
finalize" safety property directly, mirroring `Dsl.Primitives.linear`'s
acquire→use→release-once and `Uring.Lts`'s recycle-once lease). That linearity is
exactly what lets the compiler lower each op to an in-place mutation instead of a
functional-update reallocation (see `## CODEGEN OBLIGATIONS`).

Faithfulness (`build_addHeader` … `build_addHeaders`): building after any sequence
of ops yields the SAME `Response` the immutable `{ r with … }` chain would — the
builder changes HOW the response is computed (in-place-able), never WHAT. So every
byte-equality / `serialize` fact is preserved: `ResponseBuilder` is a faithful
refinement of the pure `Response`. -/
structure ResponseBuilder where
  /-- The accumulating response — the single reused cell (the build-once-in-place
  pooled buffer + mutated header map). Every op mutates THIS in place. -/
  acc : Response
deriving Repr

/-- Start a builder from a base response — acquire the cell, seeded with the
handler's response. The finalize of `build ∘ ofResponse` is the identity: wrapping
never changes the response. -/
def ResponseBuilder.ofResponse (r : Response) : ResponseBuilder := ⟨r⟩

/-- Finalize the builder to its accumulated `Response` — the last move of the
affine lifecycle (`build`s the wire response the serializer renders). Consumes the
builder (returns a non-builder), so nothing reuses it afterward. -/
def ResponseBuilder.build (b : ResponseBuilder) : Response := b.acc

/-- Push a header onto the accumulating cell — an in-place header-map insert.
Append at the END, matching the functional `r.headers ++ [nv]`. -/
def ResponseBuilder.addHeader (b : ResponseBuilder) (nv : Bytes × Bytes) : ResponseBuilder :=
  ⟨{ b.acc with headers := b.acc.headers ++ [nv] }⟩

/-- Overwrite the status in place — one field store. -/
def ResponseBuilder.setStatus (b : ResponseBuilder) (s : Nat) : ResponseBuilder :=
  ⟨{ b.acc with status := s }⟩

/-- Overwrite the reason phrase in place — one field store. -/
def ResponseBuilder.setReason (b : ResponseBuilder) (rs : Bytes) : ResponseBuilder :=
  ⟨{ b.acc with reason := rs }⟩

/-- Append to the body in place — an in-place buffer extend. -/
def ResponseBuilder.appendBody (b : ResponseBuilder) (extra : Bytes) : ResponseBuilder :=
  ⟨{ b.acc with body := b.acc.body ++ extra }⟩

/-- Apply a whole-`Response` transform to the accumulating cell in place — the
escape hatch for a stage whose rewrite is not a single append (e.g. a header-map
`Header.run` program: strip hop-by-hop + `set` Server/upstream/corr, exactly the
old code's in-place `hdr_map.insert()`/strip sequence). Its in-place-ness is the
transform's own concern; here it is one affine step on the builder. -/
def ResponseBuilder.mapResp (b : ResponseBuilder) (f : Response → Response) : ResponseBuilder :=
  ⟨f b.acc⟩

/-! ### Faithfulness — the builder is a refinement of the pure `Response` -/

/-- Wrapping then building is the identity (`build ∘ ofResponse = id`). -/
@[simp] theorem build_ofResponse (r : Response) :
    (ResponseBuilder.ofResponse r).build = r := rfl

/-- `addHeader` builds to the functional header append — same `Response`. -/
@[simp] theorem build_addHeader (b : ResponseBuilder) (nv : Bytes × Bytes) :
    (b.addHeader nv).build = { b.build with headers := b.build.headers ++ [nv] } := rfl

/-- `setStatus` builds to the functional status update. -/
@[simp] theorem build_setStatus (b : ResponseBuilder) (s : Nat) :
    (b.setStatus s).build = { b.build with status := s } := rfl

/-- `setReason` builds to the functional reason update. -/
@[simp] theorem build_setReason (b : ResponseBuilder) (rs : Bytes) :
    (b.setReason rs).build = { b.build with reason := rs } := rfl

/-- `appendBody` builds to the functional body append. -/
@[simp] theorem build_appendBody (b : ResponseBuilder) (extra : Bytes) :
    (b.appendBody extra).build = { b.build with body := b.build.body ++ extra } := rfl

/-- `mapResp` builds to the transform applied to the built base — same `Response`
the functional `onResponse : Response → Response` would produce. -/
@[simp] theorem build_mapResp (b : ResponseBuilder) (f : Response → Response) :
    (b.mapResp f).build = f b.build := rfl

/-- **The key faithfulness fact.** Building after a whole SEQUENCE of `addHeader`s
(the affine, threaded, mutate-in-place form) yields exactly the `Response` the
immutable `{ r with headers := r.headers ++ … }` chain would — all the headers
appended to the base, in order. So threading the builder computes the SAME bytes
`serialize` renders; it only changes that the ~N appends are one in-place buffer
growth, not N `Response` reallocations. This is the theorem that carries
byte-equality across the representation change. -/
theorem build_addHeaders (b : ResponseBuilder) (nvs : List (Bytes × Bytes)) :
    (nvs.foldl ResponseBuilder.addHeader b).build
      = { b.build with headers := b.build.headers ++ nvs } := by
  induction nvs generalizing b with
  | nil =>
    show b.build = { b.build with headers := b.build.headers ++ [] }
    rw [List.append_nil]
  | cons nv rest ih =>
    rw [List.foldl_cons, ih]
    show { (b.addHeader nv).build with headers := (b.addHeader nv).build.headers ++ rest } = _
    rw [build_addHeader]
    simp [List.append_assoc]

/-! ### The affine usage discipline (mirrors `Dsl.Primitives.linear`)

Stated the same way `Dsl.Primitives.linear` (acquire→use→release-once) and
`Uring.Lts` (recycle-once lease) state theirs: a tiny lifecycle whose finalized
state is absorbing. This is what "consumed once" MEANS operationally — once a
builder is `build`-finalized it is never mutated again; the API shape (every op
returns a fresh builder, `build` returns a non-builder) makes that hold by
construction, and `built_absorbing` records the safety property the compiler
relies on to reuse the cell's storage. -/

/-- A builder is `open` while stages thread/mutate it, then `built` once `build`
finalizes it; `built` is absorbing. Mirrors `linear`'s `fresh/held/released`. -/
inductive BuildLife where
  /-- Being threaded through the response phase — mutated in place. -/
  | open
  /-- Finalized by `build`; absorbing — no op reuses it. -/
  | built
deriving DecidableEq, Repr

/-- A builder move: an in-place mutation (`addHeader`/`setStatus`/…) or `build`. -/
inductive BuildOp where
  | mutate
  | finalize
deriving Repr

/-- The affine lifecycle. A finalized builder absorbs every operation (no reuse):
the "consumed once" discipline, total by making illegal reuse a no-op — exactly
`Dsl.Primitives.linStep`'s shape. -/
def buildStep : BuildLife → BuildOp → BuildLife
  | .open, .mutate   => .open
  | .open, .finalize => .built
  | s, _             => s

/-- **Finalize-once.** A `built` builder stays `built` — no operation reuses or
re-mutates it (the affine discipline's safety property, the analogue of
`Dsl.Primitives.released_absorbing`; it is what licenses the in-place lowering). -/
theorem built_absorbing (op : BuildOp) : buildStep .built op = .built := by
  cases op <;> rfl

/-- A mutation never resurrects a finalized builder. -/
theorem no_mutate_after_build : buildStep .built .mutate = .built := rfl

/-- A pipeline stage: a named pair of a request-phase transform (which may gate)
and a response-phase transform. This is the unit of the fan-out — one lib, one
`Stage`, one byte-effect theorem. -/
structure Stage where
  /-- A human name for the stage (diagnostics; not load-bearing). -/
  name : String
  /-- Request phase (run in list order): gate or pass through. -/
  onRequest : Ctx → StageStep
  /-- Response phase (run in REVERSE list order — the onion). Threads the AFFINE
  `ResponseBuilder` — one cell mutated in place, not a `Response` rebuilt. -/
  onResponse : Ctx → ResponseBuilder → ResponseBuilder

/-- **The pipeline fold.** Run the request phase in order; the first stage that
`.respond`s short-circuits (the handler and later stages are skipped). If every
stage passes, run `handler` on the final context and seed the affine
`ResponseBuilder` from its response (`ofResponse` — acquire the cell). The response
phase then threads that ONE builder back outward — each passed stage's
`onResponse`, in reverse order (the onion) — mutating it in place. The caller
`build`s the final builder to the wire `Response`. A gating stage seeds the builder
from its `.respond` response, so the already-passed outer stages still thread it. -/
def runPipeline : List Stage → (Ctx → Response) → Ctx → ResponseBuilder
  | [], handler, c => ResponseBuilder.ofResponse (handler c)
  | s :: rest, handler, c =>
    match s.onRequest c with
    | .respond r   => ResponseBuilder.ofResponse r
    | .continue c' => s.onResponse c' (runPipeline rest handler c')

/-! ## The composition calculus -/

/-- **`pipeline_empty` — identity.** With no stages, the pipeline is the bare
handler, seeded into a builder (`ofResponse` — the acquire that the response phase
mutates in place). -/
theorem pipeline_empty (handler : Ctx → Response) (c : Ctx) :
    runPipeline [] handler c = ResponseBuilder.ofResponse (handler c) := rfl

/-- **`pipeline_cons` — the onion recursion (head/tail factoring).** Running
`s :: rest` gates on `s.onRequest`: a `.respond r` seeds the builder; a
`.continue c'` runs the inner pipeline on `c'` and threads the resulting builder
through `s.onResponse`. This is the defining equation a stage's local proof factors
through — now over the builder. -/
theorem pipeline_cons (s : Stage) (rest : List Stage) (handler : Ctx → Response)
    (c : Ctx) :
    runPipeline (s :: rest) handler c
      = match s.onRequest c with
        | .respond r   => ResponseBuilder.ofResponse r
        | .continue c' => s.onResponse c' (runPipeline rest handler c') := rfl

/-- **`pipeline_gate_short_circuits` — a gate's response IS the output.** If `s`
fires `.respond r`, the pipeline builder is exactly `ofResponse r` — for ANY tail
and handler. Because the result does not mention `rest` or `handler`, neither the
handler nor any stage after `s` runs; `build` of it is `r`. -/
theorem pipeline_gate_short_circuits (s : Stage) (rest : List Stage)
    (handler : Ctx → Response) (c : Ctx) (r : Response)
    (hg : s.onRequest c = .respond r) :
    runPipeline (s :: rest) handler c = ResponseBuilder.ofResponse r := by
  rw [pipeline_cons, hg]

/-- **`pipeline_gate_ignores_rest` — the skip, stated directly.** When `s` gates,
swapping the tail AND the handler leaves the output unchanged: the handler and
every stage after `s` are genuinely not run. -/
theorem pipeline_gate_ignores_rest (s : Stage) (rest rest' : List Stage)
    (handler handler' : Ctx → Response) (c : Ctx) (r : Response)
    (hg : s.onRequest c = .respond r) :
    runPipeline (s :: rest) handler c = runPipeline (s :: rest') handler' c := by
  rw [pipeline_gate_short_circuits s rest handler c r hg,
      pipeline_gate_short_circuits s rest' handler' c r hg]

/-- **`pipeline_stage_effect` — the byte-effect hook.** When `s` passes
(`.continue c'`), the pipeline builder is `s.onResponse c'` applied to the inner
pipeline's builder. THIS is the theorem each lib's byte-effect theorem
instantiates: a lib proves `(s.onResponse c' X).build` carries its byte (via
`build_addHeader` etc.), and this lemma puts that contribution into the real
`runPipeline` output — locally, without the whole stage list. Unchanged in shape
by the builder move; the effect is now on the threaded `ResponseBuilder`. -/
theorem pipeline_stage_effect (s : Stage) (rest : List Stage)
    (handler : Ctx → Response) (c c' : Ctx)
    (hc : s.onRequest c = .continue c') :
    runPipeline (s :: rest) handler c
      = s.onResponse c' (runPipeline rest handler c') := by
  rw [pipeline_cons, hc]

/-- **`pipeline_onion_order` — response phase reverses request phase.** With two
passing stages, the request phase visits `s₁` then `s₂` (`c → c₁ → c₂`), and the
response phase visits them in the exact reverse: `s₂.onResponse` (inner) wraps the
handler first, then `s₁.onResponse` (outer) wraps that. The onion law; the
general N-stage case is `pipeline_cons`/`pipeline_stage_effect` unfolded
recursively. -/
theorem pipeline_onion_order (s₁ s₂ : Stage) (handler : Ctx → Response)
    (c c₁ c₂ : Ctx)
    (h1 : s₁.onRequest c = .continue c₁) (h2 : s₂.onRequest c₁ = .continue c₂) :
    runPipeline [s₁, s₂] handler c
      = s₁.onResponse c₁ (s₂.onResponse c₂ (ResponseBuilder.ofResponse (handler c₂))) := by
  rw [pipeline_stage_effect s₁ [s₂] handler c c₁ h1,
      pipeline_stage_effect s₂ [] handler c₁ c₂ h2,
      pipeline_empty]

/-! ## THE STAGE TEMPLATE (copy this for `Reactor/Stage/<Lib>.lean`)

A fan-out lib adds a byte-driving feature in ONE file by copying the pattern
below. `exampleStage` is a response-transform stage (it always passes, then
stamps a header); a GATE stage instead returns `.respond someResponse` from
`onRequest` on its condition (see `IpFilter`/`Rate` in the design). Its
byte-effect theorem rides on `pipeline_stage_effect`:

```
-- Reactor/Stage/MyLib.lean
def myHeaderName : Bytes := "x-mylib".toUTF8.toList
def myHeaderVal  : Bytes := "on".toUTF8.toList

def myStage : Stage where
  name := "mylib"
  onRequest  := fun c => .continue c                       -- a gate: `.respond r`
  onResponse := fun _ b => b.addHeader (myHeaderName, myHeaderVal)   -- affine push

-- the byte-effect: the lib's header appears in the BUILT pipeline output, for ANY tail.
theorem myStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    (myHeaderName, myHeaderVal) ∈ ((runPipeline (myStage :: rest) h c).build).headers := by
  rw [pipeline_stage_effect myStage rest h c c rfl]; simp
```

The `onResponse` now threads the affine `ResponseBuilder` (`b.addHeader …` =
`headers.push` on the one pooled cell) instead of rebuilding a `Response` with
`{ r with … ++ … }`; the byte-effect theorem ranges over `.build` (the finalized
response the serializer renders), discharged by `build_addHeader`. A gate stage is
unchanged — it `.respond`s a `Response` from `onRequest`.

Then append `myStage` to `Reactor.Deploy.deployStages`. Disjoint file, one
theorem, the proven fold composes it. The worked, kernel-checked instance: -/

/-- Example header name (`x-example`) a template stage stamps. -/
def exampleHeaderName : Bytes := "x-example".toUTF8.toList

/-- Example header value the template stage stamps. -/
def exampleHeaderVal : Bytes := "1".toUTF8.toList

/-- **The worked template stage.** A response-transform stage: it always passes on
the request phase, then pushes its header onto the affine builder on the response
phase (`addHeader` = one in-place `headers.push`, not a `Response` realloc). A gate
stage would instead `.respond` from `onRequest`. -/
def exampleStage : Stage where
  name := "example"
  onRequest := fun c => .continue c
  onResponse := fun _ b => b.addHeader (exampleHeaderName, exampleHeaderVal)

/-- The template stage factors through `pipeline_stage_effect`: its `onResponse`
threads the tail builder (adding its header in place). -/
theorem exampleStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    runPipeline (exampleStage :: rest) h c
      = (runPipeline rest h c).addHeader (exampleHeaderName, exampleHeaderVal) :=
  pipeline_stage_effect exampleStage rest h c c rfl

/-- **The byte-effect.** The template stage's header genuinely appears in the
BUILT pipeline output — for ANY tail and handler. This is what a fan-out lib
proves of its own header: a real byte-driver, not an attachment. `build_addHeader`
carries the affine push into the finalized `Response` the serializer renders. -/
theorem exampleStage_header_present (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    (exampleHeaderName, exampleHeaderVal)
      ∈ ((runPipeline (exampleStage :: rest) h c).build).headers := by
  rw [exampleStage_effect, build_addHeader]
  simp

/-! ## CODEGEN OBLIGATIONS

Two obligations the whole-program specializing backend must discharge for this
pipeline to match a hand-unrolled imperative serve; the Lean design makes them
SOUND but does not give them for free:

1. **Dispatch (spine + inline).** `Reactor.Deploy.deployStages` must stay a
   COMPILE-TIME LITERAL (a top-level `def` of explicit `::`-cons cells of top-level
   stage `def`s — never assembled at runtime from config). Then the backend
   specializes `runPipeline deployStages` at the known spine (unroll the fold — the
   `pipeline_cons`/`pipeline_stage_effect` reductions, done at compile time) and
   projects-and-inlines the known `Stage` function fields (defunctionalization of a
   closed set → direct call → inline), emitting a straight-line zero-dispatch
   sequence with no `List` node and no closure/indirect call.

2. **Affine builder (in-place mutation).** The `ResponseBuilder` must be emitted as
   an IN-PLACE MUTABLE cell: `addHeader` → a header push, `appendBody` → an
   in-place buffer extend, `setStatus`/`setReason` → one field store, `mapResp` →
   the transform's own in-place header-map ops. The AFFINE discipline
   (`built_absorbing` — each builder consumed once, never reused) is exactly what
   makes this SOUND: the old cell is provably dead after each op, so its storage is
   reused rather than a fresh `Response` reallocated. Without this the response
   phase regresses to one `Response` reallocation + list copy PER STAGE per request.
   `build_*` proves the in-place form computes the same bytes as the functional one.

**Per-core share-nothing invariant.** The verified pipeline is ONE shard; N shards
run share-nothing (move-only, per-event-loop, no cross-shard handoff). A stage's
`ResponseBuilder` (and its `Ctx`) is per-request on one shard — no `onRequest` /
`onResponse` may reach for cross-shard shared state or hand a builder to another
shard on the hot path, or the parallelism-by-partition scaling is forfeited. -/

end Reactor.Pipeline
