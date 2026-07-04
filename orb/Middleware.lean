/-!
# Middleware chain framework (the onion composition law)

A **middleware** wraps a handler on both sides of the request/response
exchange: a request-phase transform `onReq : Req → Req` that runs *before*
the inner handler sees the request, and a response-phase transform
`onResp : Resp → Resp` that runs *after* the inner handler produces the
response.  A **chain** is an ordered list of middlewares composed in the
classic "onion" discipline: the request phase runs the list left-to-right
(outermost first), the inner handler fires, and the response phase runs the
list *right-to-left* (outermost last).  Each middleware is the skin of an
onion — a request travels inward through every layer, hits the core, and the
response travels back outward through the same layers in reverse.

This file is the composition framework only; concrete members (CORS,
security headers, IP filtering) live in sibling files.  As a worked
byte-transform member it also carries a **content codec** boundary
(gzip RFC 1952, brotli RFC 7932, zstd RFC 8878): each of those formats is a
*lossless* compressed data format (RFC 1952 §1.1; RFC 7932 §1; RFC 8878 §1),
so the codec is modeled as an uninterpreted pair `compress`/`decompress`
carrying the single algebraic fact that matters — `decompress ∘ compress =
id` (the round-trip is lossless).  No actual codec is implemented; the
theorems hold for every lossless codec.

## What is proved

* `run_cons` — the onion recursion: running `m :: ms` is
  `m.onResp (run ms h (m.onReq req))`.  `m` sees the request first and the
  response last; this *is* the onion.
* `chain_onion_order` — the response phase visits the chain in the exact
  reverse of the order the request phase visited it.
* `chain_assoc` — middleware composition (`Mw.comp`) is associative, so how
  a chain is parenthesized never changes its behavior.
* `chain_identity` — the empty chain is the identity handler wrapper
  (`run [] h = h`); `idMw` is a unit for `Mw.comp`.
* `compress_roundtrip` — a compression member is transparent end-to-end:
  decompressing the chain's output recovers the handler's original body,
  for every lossless codec.

## Boundary / UNCLOSED

* The codec's internal format (DEFLATE / brotli / zstd bitstreams) is not
  modeled; `compress`/`decompress` are uninterpreted total functions
  constrained only by losslessness.  RFC 1952/7932/8878 wire formats are a
  boundary.
* `onReq`/`onResp` are pure total transforms; middlewares that short-circuit
  (answer without calling the inner handler) or perform effects are out of
  scope for this framework file.
-/

namespace Middleware

universe u v

/-- A middleware: a request-phase transform and a response-phase transform
around an inner handler. -/
structure Mw (Req : Type u) (Resp : Type v) where
  onReq : Req → Req
  onResp : Resp → Resp

variable {Req : Type u} {Resp : Type v}

/-- Left-to-right function pipeline: `pipe [f, g, h] x = h (g (f x))` —
`f` is applied first. -/
def pipe {α : Type _} : List (α → α) → α → α
  | [], x => x
  | f :: fs, x => pipe fs (f x)

/-- The request phase of a chain: each `onReq`, left-to-right (outermost
middleware first). -/
def reqPhase (ms : List (Mw Req Resp)) : Req → Req :=
  pipe (ms.map Mw.onReq)

/-- The response phase of a chain: each `onResp`, in *reverse* list order
(outermost middleware last). -/
def respPhase (ms : List (Mw Req Resp)) : Resp → Resp :=
  pipe ((ms.map Mw.onResp).reverse)

/-- Run a chain around an inner handler: request phase, then the handler,
then the response phase. -/
def run (ms : List (Mw Req Resp)) (h : Req → Resp) (req : Req) : Resp :=
  respPhase ms (h (reqPhase ms req))

/-- The identity middleware: touches neither request nor response. -/
def idMw : Mw Req Resp := { onReq := id, onResp := id }

/-- Compose two middlewares into one, preserving the onion discipline:
`a`'s request transform runs first and its response transform runs last. -/
def Mw.comp (a b : Mw Req Resp) : Mw Req Resp :=
  { onReq := b.onReq ∘ a.onReq
    onResp := a.onResp ∘ b.onResp }

/-! ### Pipeline lemmas -/

/-- Appending one stage to the end of a pipeline wraps the whole result. -/
theorem pipe_snoc {α} (fs : List (α → α)) (g : α → α) (x : α) :
    pipe (fs ++ [g]) x = g (pipe fs x) := by
  induction fs generalizing x with
  | nil => rfl
  | cons f fs ih =>
    show pipe (f :: (fs ++ [g])) x = g (pipe (f :: fs) x)
    simp only [pipe]
    exact ih (f x)

/-- `map` commutes with `reverse` (proved locally to stay Mathlib-free). -/
theorem map_reverse' {α β} (f : α → β) (l : List α) :
    (l.reverse).map f = (l.map f).reverse := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.reverse_cons, List.map_append, ih]

/-! ### The chain laws -/

/-- Request phase peels the head: the first middleware transforms the
request before the rest of the chain. -/
theorem reqPhase_cons (m : Mw Req Resp) (ms : List (Mw Req Resp)) (req : Req) :
    reqPhase (m :: ms) req = reqPhase ms (m.onReq req) := by
  simp [reqPhase, pipe]

/-- Response phase peels the head *last*: the first middleware transforms
the response after the rest of the chain. -/
theorem respPhase_cons (m : Mw Req Resp) (ms : List (Mw Req Resp)) (resp : Resp) :
    respPhase (m :: ms) resp = m.onResp (respPhase ms resp) := by
  show pipe (((m :: ms).map Mw.onResp).reverse) resp
       = m.onResp (pipe ((ms.map Mw.onResp).reverse) resp)
  rw [List.map_cons, List.reverse_cons, pipe_snoc]

/-- **The onion recursion.** Running the chain `m :: ms` puts `m` on the
outside: `m` sees the request first (`m.onReq`) and the response last
(`m.onResp`), with the rest of the chain nested inside. -/
theorem run_cons (m : Mw Req Resp) (ms : List (Mw Req Resp))
    (h : Req → Resp) (req : Req) :
    run (m :: ms) h req = m.onResp (run ms h (m.onReq req)) := by
  simp [run, reqPhase_cons, respPhase_cons]

/-- **Onion ordering.** The response phase visits the chain in the exact
reverse of the request phase: `reqPhase` is `pipe (map onReq ms)`, and
`respPhase` is `pipe (map onResp ms.reverse)`. -/
theorem chain_onion_order (ms : List (Mw Req Resp)) :
    respPhase ms = pipe ((ms.reverse).map Mw.onResp) := by
  unfold respPhase
  rw [map_reverse']

/-- **Associativity.** Middleware composition is associative, so a chain's
behavior is independent of how it is parenthesized. -/
theorem chain_assoc (a b c : Mw Req Resp) :
    (a.comp b).comp c = a.comp (b.comp c) := rfl

/-- **Empty chain = identity handler wrapper.** -/
theorem chain_identity (h : Req → Resp) : run [] h = h := by
  funext req; rfl

/-- `idMw` is a left unit for composition. -/
theorem idMw_comp (a : Mw Req Resp) : idMw.comp a = a := rfl

/-- `idMw` is a right unit for composition. -/
theorem comp_idMw (a : Mw Req Resp) : a.comp idMw = a := rfl

/-! ### A worked byte-transform member: content compression -/

/-- Raw byte strings. -/
abbrev Bytes := List UInt8

/-- A content codec (gzip / brotli / zstd) as a boundary: two uninterpreted
total transforms whose only law is that decompression inverts compression.
RFC 1952 §1.1, RFC 7932 §1, and RFC 8878 §1 each define a *lossless* format,
which is exactly this equation. -/
structure Codec where
  compress : Bytes → Bytes
  decompress : Bytes → Bytes
  /-- Losslessness: the round-trip is the identity (the only property the
  chain framework needs from a real codec). -/
  lossless : ∀ b, decompress (compress b) = b

/-- Content-encoding middleware over a body-valued response: leaves the
request alone and compresses the response body. -/
def compressMw (c : Codec) : Mw Req Bytes :=
  { onReq := id, onResp := c.compress }

/-- **Compression is end-to-end transparent.** Decompressing what a
compression-only chain emits recovers exactly the handler's original body —
for every lossless codec. -/
theorem compress_roundtrip (c : Codec) (h : Req → Bytes) (req : Req) :
    c.decompress (run [compressMw c] h req) = h req := by
  rw [run_cons, chain_identity]
  show c.decompress (c.compress (h (id req))) = h req
  simpa using c.lossless (h req)

end Middleware
