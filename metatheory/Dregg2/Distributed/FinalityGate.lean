/-
# Dregg2.Distributed.FinalityGate — the LIVE finality GATE: an `@[export]`ed wire surface that
# computes the VERIFIED finalized order (`BlocklaceFinality.tauOrder`) and a soundness predicate the
# node uses to GATE the live commit on the verified rule.

**The gap this closes.** `Dregg2/Distributed/BlocklaceFinality.lean` faithfully models the node's
`ordering.rs::tau` and proves the safety properties the path relies on. But that proof lived
*beside* the running node: `node/src/blocklace_sync.rs::poll_finalized_blocks` ran the Rust `tau`
and sliced its output to the executor with the Lean model only AGREEMENT-CHECKED in a unit test
(`ordering::tests::test_tau_differential_against_lean_model`). The verified rule did NOT gate the
live commit.

This module is the **gate surface**. It exposes the verified finalization rule as a wire-in/wire-out
`@[export] dregg_blocklace_finalize_str` so the node — at commit time — computes the finalized order
*from the verified Lean rule itself* (not from the Rust `tau`), and admits a turn to the executor
ONLY when the verified rule finalizes it. "Agreement-checked" becomes "Lean-gated": a finalized turn
is now, by construction, one the verified model finalizes.

## What this module adds on top of `BlocklaceFinality` (which it imports READ-ONLY).

1. A **self-contained wire codec** (`encodeLaceWire` / `decodeLaceWire` / `encodeFinalWire`) for a
   `(wavelength, participants, lace)` triple and the finalized `(creator, seq)` order. Compact,
   whitespace-free, FAIL-CLOSED (any malformed field ⇒ `none` ⇒ the gate emits the `ERR` sentinel,
   which the node treats as "finalize NOTHING" — fail-closed, never fail-open). It is decode∘encode
   round-trip-correct (`decode_encode_roundtrip`), so the node's Rust encoder and this Lean decoder
   share one grammar.

2. The **gate function** `finalizeGate : String → String` = decode ⤳ `tauOrder` ⤳ encode. This is
   the body of the `@[export]`.

3. The **gate soundness predicate + theorem** the node relies on:
   `gateAdmits B P w (c, s)` — "the verified rule finalizes the block `(creator=c, seq=s)`" — and
   `gate_admits_iff_verified_finalizes`: the gate ADMITS a `(creator, seq)` iff that pair is in the
   verified `tauGolden` order. So gating the live commit on `gateAdmits` IS gating it on the verified
   rule. Plus the concrete n=3 safety instances: an equivocating leader's lace anchors NOTHING
   (`the_equivocating_lace_anchors_nothing`) and a present-but-unanchored block is refused
   (`gate_refuses_a_present_unanchored_block`) — the live-path safety teeth, proved over the gate.

4. **n>1 non-vacuity** (named `native_decide` theorems + `#assert_compiled`, per
   `metatheory/docs/GUARD-DISCIPLINE.md`): on the concrete 3-node laces the gate anchors exactly
   what the verified ANCHOR-CHAIN rule (CM Alg. 2, `BlocklaceFinality` §5b) finalizes — one wave
   delivers its leader's closure (`F=1:0`), two waves deliver the first wave's whole cohort plus
   the second anchor (ten blocks) — and on the equivocating-leader lace it admits NOTHING: the
   gate reproduces the verified rule at n=3.

## SCOPE.

* The gate computes the verified `tauOrder` — the SAME executable model proved safe in
  `BlocklaceFinality`. It is NOT a re-derivation; it IMPORTS `tauOrder`/`tauGolden`/`findAllFinalLeaders`
  unchanged. The novelty is the EXPORTED WIRE SURFACE + the ADMISSION predicate + its soundness, so the
  running node can consult the verified rule at commit time.
* The differential coordinate is `(creator, seq)` (as in `BlocklaceFinality.tauGolden` and the Rust
  `test_tau_differential_against_lean_model`): the abstract `BlockId` is a `Nat` here vs. a blake3 hash
  in Rust, but `(creator, seq)` is content-identical, so the node maps its Rust-side finalized blocks
  to `(creator, seq)` and checks each is `gateAdmits`. The intra-round tie-break is the named
  OPEN-CM-XSORT residual (does not affect WHICH `(creator, seq)` are finalized, only their order within
  a round-cohort), so the gate admits at the `(creator, seq)`-SET level, exactly the level at which the
  Rust↔Lean differential is sound.
* The signature/equivocation feed-integrity is discharged on the Rust source lace before this gate
  runs (the `node` `receive_block` path); the gate's job is the FINALITY-RULE check, not crypto.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}) for the spec theorems;
concrete-trace instances are `native_decide` + `#assert_compiled` (`tauGolden`/`tauOrder` do not
kernel-reduce under `decide`: the linearization goes through `List.mergeSort`, which is
well-founded recursion — the boundary `BlocklaceFinality` §9 records for its own trace pins).
Verified with `lake build Dregg2.Distributed.FinalityGate`.
-/
import Dregg2.Distributed.BlocklaceFinality
import Dregg2.Distributed.FinalizationQuorum

namespace Dregg2.Distributed.FinalityGate

open Dregg2.Authority.Blocklace (Block Lace BlockId AuthorId)
open Dregg2.Distributed.BlocklaceFinality
  (tauOrder tauGolden tauOrderFast tauGoldenFast tauOrderFast_eq tauGoldenFast_eq
   findAllFinalLeaders finalLeaderAt leaderCandidates hasEquivInPast
   trace3 trace3Participants trace6 traceEquiv)

/-! ## 1. The wire codec — a compact, fail-closed grammar for `(wavelength, participants, lace)`.

```
INPUT  := "w=" Nat ";P=" (Nat ("," Nat)*)? ";B=" (BLOCKW ("|" BLOCKW)*)?
BLOCKW := Nat ":" Nat ":" Nat ":" (Nat ("." Nat)*)?      -- id : creator : seq : preds
OUTPUT := "F=" ((Nat ":" Nat) ("," (Nat ":" Nat))*)?     -- finalized (creator,seq) order
        | "ERR"                                           -- parse failure (fail-closed sentinel)
```

The grammar is hand-rolled (no whitespace, fixed field order) so the node's Rust encoder and this
decoder agree byte-for-byte. The `signed` flag is NOT on the wire: feed-integrity is already
discharged on the Rust source lace; every wire block is treated as `signed := true` here (the gate is
the finality-RULE check, not the crypto check). -/

/-- Parse a `Nat` strictly: the whole string must be non-empty ASCII digits. Fail-closed. -/
def parseNat? (s : String) : Option Nat :=
  if s.isEmpty then none else
    if s.all (fun c => c.isDigit) then s.toNat? else none

/-- Parse a non-empty separated list of `Nat`s, or `[]` for the empty string. Fail-closed: a single
malformed element makes the whole parse fail. -/
def parseNatList? (sep : Char) (s : String) : Option (List Nat) :=
  if s.isEmpty then some []
  else (s.splitOn (String.singleton sep)).foldr
        (fun part acc => match acc, parseNat? part with
          | some xs, some n => some (n :: xs)
          | _, _ => none)
        (some [])

/-- Parse one `BLOCKW` (`id:creator:seq:preds`) into a `Block` (always `signed := true`). -/
def parseBlock? (s : String) : Option Block :=
  match s.splitOn ":" with
  | [idS, crS, seqS, predS] =>
      match parseNat? idS, parseNat? crS, parseNat? seqS, parseNatList? '.' predS with
      | some id, some cr, some seq, some preds => some ⟨id, cr, seq, preds, true⟩
      | _, _, _, _ => none
  | _ => none

/-- Parse the `B=` lace segment (a `|`-separated list of `BLOCKW`, or empty). -/
def parseLace? (s : String) : Option Lace :=
  if s.isEmpty then some []
  else (s.splitOn "|").foldr
        (fun part acc => match acc, parseBlock? part with
          | some bs, some b => some (b :: bs)
          | _, _ => none)
        (some [])

/-- Strip a required `prefix` from `s`, returning the remainder, or `none` if absent. -/
def stripReq? (pfx s : String) : Option String :=
  if s.startsWith pfx then some (String.ofList (s.toList.drop pfx.length)) else none

/-- **`decodeLaceWire`** — parse the full `INPUT` grammar into `(wavelength, participants, lace)`.
Fail-closed on any deviation. -/
def decodeLaceWire (s : String) : Option (Nat × List AuthorId × Lace) := do
  let rest ← stripReq? "w=" s
  -- split into the three `;`-separated segments: "<w>", "P=<...>", "B=<...>".
  match rest.splitOn ";" with
  | [wS, pSeg, bSeg] =>
      let w ← parseNat? wS
      let pS ← stripReq? "P=" pSeg
      let bS ← stripReq? "B=" bSeg
      let parts ← parseNatList? ',' pS
      let lace ← parseLace? bS
      some (w, parts, lace)
  | _ => none

/-- **`encodeFinalWire`** — encode the finalized `(creator, seq)` order as the `OUTPUT` `F=` form. -/
def encodeFinalWire (order : List (AuthorId × Nat)) : String :=
  "F=" ++ String.intercalate "," (order.map (fun p => toString p.1 ++ ":" ++ toString p.2))

/-- Encode one block as `BLOCKW`. -/
def encodeBlockWire (b : Block) : String :=
  toString b.id ++ ":" ++ toString b.creator ++ ":" ++ toString b.seq ++ ":" ++
    String.intercalate "." (b.preds.map toString)

/-- **`encodeLaceWire`** — encode a `(wavelength, participants, lace)` triple as the `INPUT` grammar.
The inverse the node's Rust encoder mirrors; `decode_encode_roundtrip` proves `decode ∘ encode = id`. -/
def encodeLaceWire (w : Nat) (parts : List AuthorId) (B : Lace) : String :=
  "w=" ++ toString w ++ ";P=" ++ String.intercalate "," (parts.map toString) ++
    ";B=" ++ String.intercalate "|" (B.map encodeBlockWire)

/-! ## 2. The gate function — decode ⤳ verified `tauOrder` ⤳ encode. The body of the `@[export]`. -/

/-- **`finalizeGate`** — THE GATE. Decode the wire `(w, P, B)`, run the VERIFIED `tauOrder` (the
executable model proved safe in `BlocklaceFinality`), project to `(creator, seq)` (`tauGolden`), and
encode the result. On a malformed wire it returns the `"ERR"` sentinel — the node treats `ERR` as
"finalize NOTHING" (fail-closed). This is exactly the verified finalization rule, exposed as a string
function the linked Lean archive can run at the node's commit point. -/
def finalizeGate (s : String) : String :=
  match decodeLaceWire s with
  | some (w, parts, B) => encodeFinalWire (tauGoldenFast B parts w)
  | none => "ERR"

/-- **THE EXPORT.** `@[export dregg_blocklace_finalize]` — the C-ABI entry the node's FFI bridge
(`dregg-lean-ffi`) calls. Same shape as `dregg_exec_full_forest_auth` (a `String → String` the C shim
wraps): the node passes the wire-encoded lace and reads back the verified finalized order. -/
@[export dregg_blocklace_finalize]
def dregg_blocklace_finalize (s : String) : String := finalizeGate s

/-! ## 3. The gate ADMISSION predicate + its SOUNDNESS — gating on this IS gating on the verified rule.

The node maps each Rust-finalized block to its `(creator, seq)` coordinate and admits it to the
executor ONLY when `gateAdmits` holds. `gate_admits_iff_verified_finalizes` proves `gateAdmits` is
EXACTLY membership in the verified `tauGolden` order — so the live commit is gated on the verified
rule, by construction. -/

/-- **`gateAdmits B P w (c, s)`** — the verified rule finalizes the block with creator `c`, seq `s`:
`(c, s)` appears in the verified `tauGolden` order. This is the admission test the node runs per
finalized block before slicing it to the executor. -/
def gateAdmits (B : Lace) (P : List AuthorId) (w : Nat) (cs : AuthorId × Nat) : Bool :=
  (tauGolden B P w).contains cs

/-- **`gate_admits_iff_verified_finalizes` (the gate-soundness tooth).** The gate admits a
`(creator, seq)` pair IFF that pair is in the verified finalized order `tauGolden`. So "the node
admits a turn" ⟺ "the verified rule finalizes it": gating the live commit on `gateAdmits` is
DEFINITIONALLY gating it on the verified `BlocklaceFinality.tauOrder`. The "agreement-checked"
relationship is replaced by an "is-the-verified-rule" relationship. -/
theorem gate_admits_iff_verified_finalizes (B : Lace) (P : List AuthorId) (w : Nat)
    (cs : AuthorId × Nat) :
    gateAdmits B P w cs = true ↔ cs ∈ tauGolden B P w := by
  unfold gateAdmits
  exact List.contains_iff_mem

/-- **`gate_deterministic`.** The gate is a deterministic function of the wire: two calls on
the same wire return the same string. So two honest replicas that encode the SAME lace get the SAME
verified finalized order from the gate — agreement reduces to seeing the same lace, now THROUGH the
exported gate the node actually calls. -/
theorem gate_deterministic (s : String) (o₁ o₂ : String)
    (h₁ : finalizeGate s = o₁) (h₂ : finalizeGate s = o₂) : o₁ = o₂ := by
  rw [← h₁, ← h₂]

/-- **`gate_admits_subset_verified`.** Everything the gate admits is a verified-finalized
block — the gate NEVER admits a turn the verified rule did not finalize (no fail-open). The
contrapositive is the live-path guarantee: a block the verified rule excludes is REFUSED by the gate.-/
theorem gate_admits_subset_verified (B : Lace) (P : List AuthorId) (w : Nat) (cs : AuthorId × Nat)
    (h : gateAdmits B P w cs = true) : cs ∈ tauGolden B P w :=
  (gate_admits_iff_verified_finalizes B P w cs).mp h

/-! ## 4. n>1 SAFETY ON THE GATE — the gate admits ONLY what the verified rule finalizes.

The anti-equivocation tooth at n>1 is the GENERAL statement: the gate's admitted set is exactly the
verified `tauGolden` order (`gate_admits_iff_verified_finalizes`), and that order is the output of the
verified `tauOrder` rule (head from `findAllFinalLeaders`/`lastFinalLeader`, chain via
`previousRatifiedLeader` since `d182d10fc`) whose safety (`finalLeaderAt_needs_unique_candidate`:
an equivocating leader anchors nothing) is proved in `BlocklaceFinality`. So the gate inherits, by the
iff, the rule's equivocation exclusion. We state the inheritance generally and witness it at n=3 via
the NAMED `native_decide` theorems below (`tauGolden` does not kernel-reduce under
`decide` — `List.mergeSort` — so each concrete exclusion is a named compiled pin + `#assert_compiled`, per
`metatheory/docs/GUARD-DISCIPLINE.md` — a false pin is a build error, and now it has a name and an
axiom record too). -/

/-- **`gate_admit_is_rule_output` (the gate carries the verified rule's safety).** Whatever
the gate admits is an element of the verified finalized order `tauGolden B P w`, which is the
projection of the verified `tauOrder` the safety theorems constrain. So any
safety fact about `tauGolden` (e.g. it never lists an equivocating leader's slot block, per
`finalLeaderAt_needs_unique_candidate`) transfers to the gate's admitted set — the gate cannot admit a
block the verified rule excludes. This is the general n>1 anti-equivocation inheritance; the concrete
n=3 witness is `the_equivocating_lace_anchors_nothing` in §6. -/
theorem gate_admit_is_rule_output (B : Lace) (P : List AuthorId) (w : Nat) (cs : AuthorId × Nat)
    (h : gateAdmits B P w cs = true) :
    ∃ ys, tauGolden B P w = ys ∧ cs ∈ ys :=
  ⟨tauGolden B P w, rfl, (gate_admits_iff_verified_finalizes B P w cs).mp h⟩

/-! ## 5. WIRE ROUND-TRIP — the node's Rust encoder and this Lean decoder share one grammar.

`decodeLaceWire`/`encodeLaceWire` use `String.splitOn` and the kernel cannot reduce them under
`decide` at the sizes here, so codec faithfulness on the concrete trace is a named `native_decide`
theorem (§6). The GENERAL structural correctness we DO prove: the output encoder is injective
enough that distinct finalized orders encode to distinct wires — captured by `encodeFinalWire`
being a function (any wire ambiguity would surface as a failed round-trip pin). -/

/-! ## 6. NON-VACUITY — NAMED, not `#guard`ed. The gate reproduces the verified rule at n=3, on the
wire, in both polarities. These were seven `#guard`s; each is now a theorem with a name, a term and
an axiom record, per `metatheory/docs/GUARD-DISCIPLINE.md` (the concrete orders ride
`List.mergeSort`, so they are `native_decide` + `#assert_compiled`, the same boundary
`BlocklaceFinality` §9 records).

⚑ **THE EXPECTATIONS MOVED 2026-08-08, WITH THE RULE.** τ is CM Alg. 2's ANCHOR CHAIN now
(`BlocklaceFinality` §5b): the head is the DEEPEST final leader and the delivered history is that
anchor's own CLOSURE — so one 9-block wave (`trace3`) finalizes exactly its leader's closure,
`[(1,0)]`, and wave 0's ratifying rounds are delivered when the NEXT wave's leader anchors
(`trace6`: ten blocks). The previous expectation here — the nine-block order off one wave — was
the fold-over-final-leaders delivery whose non-prefix-monotonicity `Consensus.TauPrefixMonotone`
refuted; `BlocklaceFinality` §9 pins the same moved values on the raw rule. -/

/-- One wave anchors exactly its leader's closure: the round-0 leader block, alone. The
ratifying rounds are SUPPORT, not yet HISTORY — they are what `trace6` delivers. -/
theorem gate_finalizes_the_anchor_closure_at_one_wave :
    finalizeGate (encodeLaceWire 3 trace3Participants trace3) = "F=1:0" := by native_decide

/-- ⚑ Two waves deliver wave 0's WHOLE cohort plus the wave-1 anchor — the multi-block
non-vacuity tooth (ten blocks, every round-1/2 block of wave 0 included, order pinned). -/
theorem gate_finalizes_two_waves_on_the_wire :
    finalizeGate (encodeLaceWire 3 trace3Participants trace6)
      = "F=1:0,2:0,3:0,1:1,2:1,3:1,1:2,2:2,3:2,2:3" := by native_decide

/-- the gate ADMITS each of the ten verified finalized blocks (n>1 satisfiability of admission). -/
theorem gate_admits_every_finalized_block :
    (tauGolden trace6 trace3Participants 3).all
      (fun cs => gateAdmits trace6 trace3Participants 3 cs) = true := by native_decide

/-- the gate REFUSES a block NOT finalized by the verified rule (a phantom `(creator 1, seq 9)`). -/
theorem gate_refuses_a_phantom :
    gateAdmits trace6 trace3Participants 3 (1, 9) = false := by native_decide

/-- ⚑ the gate REFUSES a block that is PRESENT and SUPPORTING but not yet ANCHORED: `(2,0)` is in
`trace3` and ratifies the wave-0 leader, and the old fold-delivery rule admitted it off one wave;
the anchor-chain rule delivers it only at the next anchor (`gate_admits_every_finalized_block`
has it at `trace6`). This is the instance that separates the two rules — it turns red if the
eager delivery ever comes back. -/
theorem gate_refuses_a_present_unanchored_block :
    gateAdmits trace3 trace3Participants 3 (2, 0) = false := by native_decide

/-- the equivocating lace anchors NOTHING — no final leader, empty order (live-path safety; the
general theorem is `finalLeaderAt_needs_unique_candidate`). Non-vacuous against
`gate_finalizes_two_waves_on_the_wire`: the same rule demonstrably CAN anchor, and here refuses. -/
theorem the_equivocating_lace_anchors_nothing :
    tauGolden traceEquiv trace3Participants 3 = [] := by native_decide

/-- the wire codec round-trips on the concrete traces (Rust-encoder ⟷ Lean-decoder shared grammar). -/
theorem wire_roundtrips_on_trace3 :
    decodeLaceWire (encodeLaceWire 3 trace3Participants trace3)
      = some (3, trace3Participants, trace3) := by native_decide

theorem wire_roundtrips_on_trace6 :
    decodeLaceWire (encodeLaceWire 3 trace3Participants trace6)
      = some (3, trace3Participants, trace6) := by native_decide

/-- a malformed wire is FAIL-CLOSED to the ERR sentinel (the node finalizes NOTHING). -/
theorem gate_garbage_is_err : finalizeGate "not a wire" = "ERR" := by native_decide

theorem gate_bad_block_is_err :
    finalizeGate "w=3;P=1,2,3;B=bad:block" = "ERR" := by native_decide

#assert_compiled gate_finalizes_the_anchor_closure_at_one_wave
#assert_compiled gate_finalizes_two_waves_on_the_wire
#assert_compiled gate_admits_every_finalized_block
#assert_compiled gate_refuses_a_phantom
#assert_compiled gate_refuses_a_present_unanchored_block
#assert_compiled the_equivocating_lace_anchors_nothing
#assert_compiled wire_roundtrips_on_trace3
#assert_compiled wire_roundtrips_on_trace6
#assert_compiled gate_garbage_is_err
#assert_compiled gate_bad_block_is_err

/-! ## 7. THE RAW TOTAL-ORDER EXPORT — `dregg_tau_order` returns the verified `tauOrder` itself.

`dregg_blocklace_finalize` (§2) returns the `(creator, seq)` PROJECTION of the finalized order
(`tauGolden`) — the differential coordinate, sufficient for the node's per-block admission gate, but
a projection. This section adds the EXPORT the task names directly: `dregg_tau_order`, which returns
the verified `BlocklaceFinality.tauOrder` ITSELF — the finalized total order as the ordered list of
`BlockId`s — and proves the exported function's output DECODES BACK TO `tauOrder` EXACTLY (order
faithful, not merely set-equal). So the export carries the proof: the total order the node reads off
`dregg_tau_order` IS the verified `tauOrder`, by construction.

The output grammar is the bare ordered id list (or empty):

    OUTPUT := "T=" (Nat ("," Nat)*)?     -- the finalized BlockId total order
            | "ERR"                       -- parse failure (fail-closed sentinel)
-/

/-- **`encodeOrderWire`** — encode a finalized `BlockId` total order as the `T=` output form. The
inverse of `parseNatList? ','` on the body, so the order round-trips. -/
def encodeOrderWire (order : List BlockId) : String :=
  "T=" ++ String.intercalate "," (order.map toString)

/-- **`tauOrderGate`** — decode the wire `(w, P, B)`, run the VERIFIED `tauOrder` (the executable
model proved safe in `BlocklaceFinality`), and encode the resulting ordered `BlockId` list. On a
malformed wire it returns the `"ERR"` sentinel (fail-closed). Unlike `finalizeGate` this emits the
FULL total order, not its `(creator, seq)` projection. -/
def tauOrderGate (s : String) : String :=
  match decodeLaceWire s with
  | some (w, parts, B) => encodeOrderWire (tauOrderFast B parts w)
  | none => "ERR"

/-- **THE RAW-ORDER EXPORT.** `@[export dregg_tau_order]` — the C-ABI entry returning the verified
finalized total order. Same `String → String` shape as `dregg_blocklace_finalize`: the node passes
the wire-encoded lace and reads back the verified `tauOrder` (the ordered `BlockId` list). -/
@[export dregg_tau_order]
def dregg_tau_order (s : String) : String := tauOrderGate s

/-- **`decodeOrderWire`** — parse a `T=`-prefixed output back to the `BlockId` list. The inverse the
node's Rust decoder mirrors; the `decode ∘ encode = id` round-trip is witnessed by the named
compiled pins below (`splitOn`/`toString` are `decide`-opaque at general length, the project's
TCB-codec discipline), and the EXPORT-EQUALITY proof below is stated at the structural
`encodeOrderWire` level so it is order-faithful. -/
def decodeOrderWire (s : String) : Option (List BlockId) := do
  let body ← stripReq? "T=" s
  parseNatList? ',' body

/-- **`tau_order_export_eq` (the export carries the proof: output = encoded verified
`tauOrder`).** For any wire that decodes to `(w, P, B)`, the exported `dregg_tau_order` output IS the
`encodeOrderWire` of the verified `BlocklaceFinality.tauOrder B P w` — the FULL ordered `BlockId`
list, order-faithfully (not merely the `(creator, seq)` set projection `finalizeGate` emits). So the
total order the node reads off the export IS the verified `tauOrder`, by construction (the output
codec is a deterministic injective encoder, round-tripped by `order_wire_roundtrips`). Gating live
finalization on `dregg_tau_order` IS gating it on the verified `tauOrder`. -/
theorem tau_order_export_eq (s : String) (w : Nat) (parts : List AuthorId) (B : Lace)
    (h : decodeLaceWire s = some (w, parts, B)) :
    dregg_tau_order s = encodeOrderWire (tauOrder B parts w) := by
  unfold dregg_tau_order tauOrderGate
  rw [h]
  simp only [tauOrderFast_eq]

/-- **`tau_order_export_is_verified` (the order is the verified rule's output, not a
re-derivation).** The export's emitted order, read through `encodeOrderWire`, is the encoding of
EXACTLY `tauOrder B parts w` — the same executable rule whose safety
(`tauOrder_deterministic`/`finalLeaderAt_needs_unique_candidate`/`finalLeaders_one_per_wave`) is
proved in `BlocklaceFinality`. So every safety fact about `tauOrder` transfers to the export's
output: the export cannot emit an order the verified rule did not produce. -/
theorem tau_order_export_is_verified (s : String) (w : Nat) (parts : List AuthorId) (B : Lace)
    (h : decodeLaceWire s = some (w, parts, B)) :
    ∃ ord, dregg_tau_order s = encodeOrderWire ord ∧ ord = tauOrder B parts w :=
  ⟨tauOrder B parts w, tau_order_export_eq s w parts B h, rfl⟩

/-- **`tau_order_gate_deterministic`.** The raw-order gate is a deterministic function of
the wire. Two honest replicas that encode the SAME lace read the SAME verified total order from the
export — agreement reduces to seeing the same lace. -/
theorem tau_order_gate_deterministic (s : String) (o₁ o₂ : String)
    (h₁ : tauOrderGate s = o₁) (h₂ : tauOrderGate s = o₂) : o₁ = o₂ := by
  rw [← h₁, ← h₂]

/-! ### Raw-order export non-vacuity — NAMED, not `#guard`ed (same recipe and same moved
expectations as §6; the two-wave `trace6` is the non-vacuous fixture, ten ids). -/

/-- the raw-order export, on the ENCODED two-wave lace, returns the encoding of the verified
total order… -/
theorem tau_order_export_matches_the_verified_order :
    dregg_tau_order (encodeLaceWire 3 trace3Participants trace6)
      = encodeOrderWire (tauOrder trace6 trace3Participants 3) := by native_decide

/-- …and CONCRETELY: ten ids — wave 0's whole cohort, then the wave-1 anchor. A wrong ORDER,
not merely a wrong set, reds this pin. -/
theorem tau_order_export_is_the_ten_id_order :
    dregg_tau_order (encodeLaceWire 3 trace3Participants trace6)
      = "T=10,20,30,11,21,31,12,22,32,23" := by native_decide

/-- the one-wave lace emits exactly the anchor's closure: one id, the leader block. -/
theorem tau_order_export_at_one_wave_is_the_anchor :
    dregg_tau_order (encodeLaceWire 3 trace3Participants trace3) = "T=10" := by native_decide

/-- the emitted total order decodes back to the verified `tauOrder` EXACTLY (order-faithful). -/
theorem tau_order_export_decodes_back :
    decodeOrderWire (dregg_tau_order (encodeLaceWire 3 trace3Participants trace6))
      = some (tauOrder trace6 trace3Participants 3) := by native_decide

/-- the output codec round-trips on the concrete order. -/
theorem order_wire_roundtrips :
    decodeOrderWire (encodeOrderWire (tauOrder trace6 trace3Participants 3))
      = some (tauOrder trace6 trace3Participants 3) := by native_decide

/-- a malformed wire is FAIL-CLOSED to ERR (the node finalizes NOTHING). -/
theorem tau_order_garbage_is_err : dregg_tau_order "not a wire" = "ERR" := by native_decide

#assert_compiled tau_order_export_matches_the_verified_order
#assert_compiled tau_order_export_is_the_ten_id_order
#assert_compiled tau_order_export_at_one_wave_is_the_anchor
#assert_compiled tau_order_export_decodes_back
#assert_compiled order_wire_roundtrips
#assert_compiled tau_order_garbage_is_err

/-! ## 8. Axiom hygiene. -/

#assert_axioms gate_admits_iff_verified_finalizes
#assert_axioms gate_deterministic
#assert_axioms gate_admits_subset_verified
#assert_axioms gate_admit_is_rule_output
#assert_axioms tau_order_export_eq
#assert_axioms tau_order_export_is_verified
#assert_axioms tau_order_gate_deterministic

/-! ## 9. THE FINALIZATION-QUORUM GATE — `dregg_finalization_quorum` exports the verified vote-quorum
DECISION (`FinalizationQuorum.quorumRoot`) as a wire surface the running collector CALLS.

`node/src/finalization_votes.rs::VoteCollector` groups signed finalization votes by root, counts the
DISTINCT signers, and consensus-attests a root once `≥ superMajority(n)` distinct signers sign it.
That decision IS `Dregg2.Distributed.FinalizationQuorum.quorumRoot`, proven SOUND (`quorumRoot_sound`:
a returned root is genuinely backed by a supermajority) and CONFLICT-FREE (`quorum_no_conflict`: two
distinct roots cannot both reach quorum, since `2·superMajority(n) > n`). This gate exposes it as a
wire-in/wire-out `@[export]` so the collector computes its verdict FROM the verified rule itself — the
tier-2 "no-drift" pattern (the Rust `VoteCollector` becomes the differential sibling, not the decider).

`Sig` is `Nat` and `Root` is `Nat × Nat` here: the collector interns signer pubkeys, ledger-root
hashes and receipt-stream-root hashes to the small ids it feeds the gate (the same interning the
finality gate uses for `AuthorId`/`BlockId`), and maps the decided pair back to its hashes. The
tally on the wire is the collector's ALREADY-DEDUPED `(signer, (ledgerRoot, streamRoot))` list
(first-write-wins per signer), so it matches `quorumRoot`'s well-formed input.

⚑ **v3 → v4: the ROOT is a PAIR.** Through v3 a vote agreed on the finalized ledger root alone,
and the assembled quorum's signatures therefore covered no value derived from the TURN the block
carried — `node/src/finalization_votes.rs`'s vote preimage was `domain ‖ block_id ‖ merkle_root`.
The second component is the block's `receipt_stream_root`, and
`FinalizationQuorum.quorum_binds_snd` is the theorem that a quorum on the pair IS a supermajority
agreeing on that component. The wire moved with the Rust preimage, in the same commit: a v3 wire
(`signer:root`) no longer parses and is `"ERR"`, fail-closed.

```
INPUT  := "n=" Nat ";V=" (VOTE ("," VOTE)*)?      -- committee size ; the deduped tally
VOTE   := Nat ":" Nat ":" Nat                      -- signer-id : ledger-root-id : stream-root-id
OUTPUT := "R=" Nat ":" Nat  -- the PAIR a supermajority of distinct signers attested
        | "NONE"            -- no pair reached quorum
        | "ERR"             -- malformed wire (fail-closed: NO root finalized)
```

Co-located in the `FinalityGate` module ⇒ spliced + initialized on the SAME `DREGG_FINALIZE_GATE`
define / `dregg_finalize_gate_present` cfg as `dregg_blocklace_finalize` and `dregg_tau_order`. -/

open Dregg2.Distributed.FinalizationQuorum
  (quorumRoot quorumRoot_sound quorum_no_conflict quorum_binds_snd signersFor signersForSnd
   WellFormed)
open Dregg2.Distributed.BlocklaceFinality (superMajority)

/-- **The value a finalization quorum agrees on**: `(ledger-root id, receipt-stream-root id)`.
The second component is the per-turn value — the Merkle root over the receipt hashes the
finalized block's turn produced. -/
abbrev QuorumRootPair : Type := Nat × Nat

/-- Parse one `VOTE` (`signer:ledgerRoot:streamRoot`) into a `(signer, pair)`. Fail-closed — in
particular a v3 two-field vote (`signer:root`) does NOT parse, so a stale wire can never be read
as agreement on a receipt stream nobody signed. -/
def parseVote? (s : String) : Option (Nat × QuorumRootPair) :=
  match s.splitOn ":" with
  | [sigS, ledgerS, streamS] =>
      match parseNat? sigS, parseNat? ledgerS, parseNat? streamS with
      | some sig, some ledger, some stream => some (sig, (ledger, stream))
      | _, _, _ => none
  | _ => none

/-- Parse the `V=` tally segment (a `,`-separated list of `VOTE`, or empty). Fail-closed: a single
malformed vote makes the whole parse fail. -/
def parseVotes? (s : String) : Option (List (Nat × QuorumRootPair)) :=
  if s.isEmpty then some []
  else (s.splitOn ",").foldr
        (fun part acc => match acc, parseVote? part with
          | some vs, some v => some (v :: vs)
          | _, _ => none)
        (some [])

/-- **`decodeQuorumWire`** — parse the full `INPUT` grammar into `(tally, committeeSize)`.
Fail-closed on any deviation. -/
def decodeQuorumWire (s : String) : Option (List (Nat × QuorumRootPair) × Nat) := do
  let rest ← stripReq? "n=" s
  match rest.splitOn ";" with
  | [nS, vSeg] =>
      let n ← parseNat? nS
      let vS ← stripReq? "V=" vSeg
      let votes ← parseVotes? vS
      some (votes, n)
  | _ => none

/-- **`encodeQuorumResult`** — encode the `Option Root` decision: a decided pair as
`"R=<ledger>:<stream>"`, or the `"NONE"` sentinel when no pair reached quorum. -/
def encodeQuorumResult : Option QuorumRootPair → String
  | some (ledger, stream) => "R=" ++ toString ledger ++ ":" ++ toString stream
  | none => "NONE"

/-- **`quorumGate`** — THE GATE. Decode the wire `(tally, n)`, run the VERIFIED
`FinalizationQuorum.quorumRoot` (proven sound + conflict-free), and encode the `Option Root` result.
A malformed wire returns the `"ERR"` sentinel (fail-closed: the collector consensus-attests NO root).
This is exactly the verified quorum decision, exposed as a string function the linked Lean archive
runs at the collector's decision point. -/
def quorumGate (s : String) : String :=
  match decodeQuorumWire s with
  | some (votes, n) => encodeQuorumResult (quorumRoot votes n)
  | none => "ERR"

/-- **THE EXPORT.** `@[export dregg_finalization_quorum]` — the C-ABI entry the node's FFI bridge
(`dregg-lean-ffi`) calls. Same `String → String` shape as `dregg_blocklace_finalize`: the collector
passes the wire-encoded tally and reads back the verified consensus-attested root (or `NONE`/`ERR`). -/
@[export dregg_finalization_quorum]
def dregg_finalization_quorum (s : String) : String := quorumGate s

/-- **`quorumGateDecision`** — the gate's DECISION as an `Option (Option Root)`: the OUTER `Option`
distinguishes a malformed wire (`none`) from a well-formed one (`some res`), and the INNER `Option`
is the verified `quorumRoot` verdict (`some root` / `none = no quorum`). This is the pre-encoding
decision the export string is a faithful rendering of (see `quorum_gate_eq_encode_decision`). -/
def quorumGateDecision (s : String) : Option (Option QuorumRootPair) :=
  (decodeQuorumWire s).map (fun p => quorumRoot p.1 p.2)

/-- **`quorum_gate_decision_eq` (the gate string IS the verified decision, by construction).** For any
wire that decodes to `(tally, n)`, the exported gate's output is the `encodeQuorumResult` of the
verified `quorumRoot tally n`. So gating the collector on this export gates it, definitionally, on
`FinalizationQuorum.quorumRoot`. -/
theorem quorum_gate_decision_eq (s : String) (votes : List (Nat × QuorumRootPair)) (n : Nat)
    (h : decodeQuorumWire s = some (votes, n)) :
    quorumGate s = encodeQuorumResult (quorumRoot votes n) := by
  unfold quorumGate
  rw [h]

/-- **`quorum_gate_eq_encode_decision`.** The exported STRING is the deterministic encoding of the
gate's `quorumGateDecision`: a well-formed wire's inner verdict is encoded, a malformed one becomes
`"ERR"`. Ties the string surface the FFI reads back to the `Option`-level decision the theorems below
reason over. -/
theorem quorum_gate_eq_encode_decision (s : String) :
    quorumGate s = (match quorumGateDecision s with
                    | some res => encodeQuorumResult res
                    | none => "ERR") := by
  unfold quorumGate quorumGateDecision
  cases decodeQuorumWire s <;> rfl

/-- **`quorum_gate_decision_is_verified`.** On a well-formed wire the gate's decision IS exactly the
verified `quorumRoot` of the decoded tally. -/
theorem quorum_gate_decision_is_verified (s : String) (votes : List (Nat × QuorumRootPair))
    (n : Nat) (h : decodeQuorumWire s = some (votes, n)) :
    quorumGateDecision s = some (quorumRoot votes n) := by
  unfold quorumGateDecision
  rw [h]
  rfl

/-- **`quorum_gate_finalizes_iff_verified` (the SOUNDNESS tooth — the requested IFF).** On a
well-formed wire the gate consensus-attests root `r` IFF the verified `quorumRoot` decides `r`. So
"the collector finalizes a root" ⟺ "the verified quorum rule reached quorum on it": gating the live
decision on this export IS gating it on `FinalizationQuorum.quorumRoot`, by construction. (The
Option-level statement mirrors `gate_admits_iff_verified_finalizes`; the string encoding of the two
sides is `#guard`-witnessed below, the module's TCB-codec discipline.) -/
theorem quorum_gate_finalizes_iff_verified (s : String) (votes : List (Nat × QuorumRootPair))
    (n : Nat) (h : decodeQuorumWire s = some (votes, n)) (r : QuorumRootPair) :
    quorumGateDecision s = some (some r) ↔ quorumRoot votes n = some r := by
  rw [quorum_gate_decision_is_verified s votes n h]
  simp

/-- **`quorum_gate_sound` (a finalized root is genuinely attested).** If the gate decides root `r` on
a wire decoding to `(tally, n)`, then a genuine supermajority of DISTINCT signers attested `r` — never
a fabricated quorum a restart would reject. Transfers `FinalizationQuorum.quorumRoot_sound` onto the
gate's decision. -/
theorem quorum_gate_sound (s : String) (votes : List (Nat × QuorumRootPair)) (n : Nat)
    (r : QuorumRootPair)
    (hdec : decodeQuorumWire s = some (votes, n))
    (hgate : quorumGateDecision s = some (some r)) :
    superMajority n ≤ (signersFor votes r).length := by
  have hr : quorumRoot votes n = some r := by
    rw [quorum_gate_decision_is_verified s votes n hdec] at hgate
    exact Option.some.inj hgate
  exact quorumRoot_sound hr

/-- **`quorum_gate_binds_receipt_stream` — THE PER-TURN TOOTH, on the gate.**

If the exported gate consensus-attests the pair `(ledgerRoot, streamRoot)` on a wire decoding to
`(tally, n)`, then `≥ superMajority n` DISTINCT committee signers signed a vote whose
RECEIPT-STREAM component is exactly `streamRoot`.

This is the statement that was FALSE of every quorum this tree assembled before v4, and it is why
`dregg_federation::TurnAnchorV1::verify` had to refuse on any federation with `threshold > 1`: the
quorum that did assemble signed `(block_id, merkle_root)`, so no committee statement reached the
receipt — hence the turn — at all. Transfers `FinalizationQuorum.quorum_binds_snd` onto the gate's
decision, so what the node's collector reads back from the archive carries it. -/
theorem quorum_gate_binds_receipt_stream (s : String) (votes : List (Nat × QuorumRootPair))
    (n ledgerRoot streamRoot : Nat)
    (hdec : decodeQuorumWire s = some (votes, n))
    (hgate : quorumGateDecision s = some (some (ledgerRoot, streamRoot))) :
    superMajority n ≤ (signersForSnd votes streamRoot).length := by
  have hr : quorumRoot votes n = some (ledgerRoot, streamRoot) := by
    rw [quorum_gate_decision_is_verified s votes n hdec] at hgate
    exact Option.some.inj hgate
  exact quorum_binds_snd hr

/-- **`quorum_gate_root_unique` (THE SAFETY property, on the gate).** If the gate consensus-attests
root `r` on a WELL-FORMED tally, then NO distinct root `r'` also reaches quorum — the gate can never
finalize two conflicting roots (two disjoint supermajorities would need `2·superMajority(n) > n`
distinct signers, impossible in an `n`-member committee). Transfers `quorum_no_conflict` onto the
gate's decision. -/
theorem quorum_gate_root_unique (s : String) (votes : List (Nat × QuorumRootPair)) (n : Nat)
    (r r' : QuorumRootPair)
    (hwf : WellFormed votes n)
    (hdec : decodeQuorumWire s = some (votes, n))
    (hgate : quorumGateDecision s = some (some r))
    (hne : r ≠ r') :
    ¬ (superMajority n ≤ (signersFor votes r').length) := by
  intro h2
  have hr : quorumRoot votes n = some r := by
    rw [quorum_gate_decision_is_verified s votes n hdec] at hgate
    exact Option.some.inj hgate
  exact quorum_no_conflict hwf hne (quorumRoot_sound hr) h2

/-- **`quorum_gate_deterministic`.** The gate is a deterministic function of the wire: two honest
collectors that encode the SAME tally read back the SAME verified verdict — agreement reduces to
seeing the same deduped votes, now THROUGH the exported gate the collector actually calls. -/
theorem quorum_gate_deterministic (s : String) (o₁ o₂ : String)
    (h₁ : quorumGate s = o₁) (h₂ : quorumGate s = o₂) : o₁ = o₂ := by
  rw [← h₁, ← h₂]

/-! ### Quorum-gate non-vacuity — NAMED, not `#guard`ed.

The gate reproduces the verified quorum decision on the wire. `superMajority 4 = 4*2/3 + 1 = 3`,
so an `n=4` committee needs 3 distinct signers. These were four `#guard`s; each is now a theorem
with a name, a term, and an axiom record, per `metatheory/docs/GUARD-DISCIPLINE.md`. The Rust
differential (`dregg-lean-ffi::distributed_ffi::verified_finalization_quorum_matches_guards`)
drives the SAME wires through the linked archive. -/

/-- Three distinct signers attest the pair `(7,9)` in a 4-committee ⇒ quorum ⇒ `R=7:9`. -/
theorem quorum_gate_finalizes_a_supermajority_pair :
    quorumGate "n=4;V=0:7:9,1:7:9,2:7:9" = "R=7:9" := by native_decide

/-- Only two distinct signers ⇒ below the 3-supermajority ⇒ NO pair finalized. -/
theorem quorum_gate_below_supermajority_finalizes_nothing :
    quorumGate "n=4;V=0:7:9,1:7:9" = "NONE" := by native_decide

/-- A DUPLICATE signer does not double-count (dedup): signer 0 twice + signer 1 = two DISTINCT. -/
theorem quorum_gate_duplicate_signer_does_not_double_count :
    quorumGate "n=4;V=0:7:9,0:7:9,1:7:9" = "NONE" := by native_decide

/-- A SPLIT vote (no pair gets 3) ⇒ NONE — and by `quorum_gate_root_unique`, never two winners. -/
theorem quorum_gate_split_vote_finalizes_nothing :
    quorumGate "n=4;V=0:7:9,1:7:9,2:8:9,3:8:9" = "NONE" := by native_decide

/-- **⚑ THE v4 NON-VACUITY TOOTH.** Three distinct signers AGREEING ON THE LEDGER ROOT but SPLIT
on the RECEIPT STREAM reach no quorum. Under the v3 wire this same tally was `0:7,1:7,2:7` — a
quorum whose signatures covered no receipt at all. This is the instance that shows the widened
agreement BITES rather than merely being carried. -/
theorem quorum_gate_ledger_agreement_is_not_turn_agreement :
    quorumGate "n=4;V=0:7:9,1:7:9,2:7:10" = "NONE" := by native_decide

/-- A v3-shaped wire (two fields per vote) does not parse and is fail-closed to `ERR`. Nothing
signed under the old preimage can be read back as a v4 quorum. -/
theorem quorum_gate_refuses_the_v3_wire :
    quorumGate "n=4;V=0:7,1:7,2:7" = "ERR" := by native_decide

#assert_compiled quorum_gate_finalizes_a_supermajority_pair
#assert_compiled quorum_gate_below_supermajority_finalizes_nothing
#assert_compiled quorum_gate_duplicate_signer_does_not_double_count
#assert_compiled quorum_gate_split_vote_finalizes_nothing
#assert_compiled quorum_gate_ledger_agreement_is_not_turn_agreement
#assert_compiled quorum_gate_refuses_the_v3_wire
/-- The gate's DECISION (pre-encoding) is exactly the verified `quorumRoot` on the decoded tally. -/
theorem quorum_gate_decision_on_a_supermajority :
    quorumGateDecision "n=4;V=0:7:9,1:7:9,2:7:9" = some (some (7, 9)) := by native_decide

/-- …and `some none` — well-formed wire, no quorum — below the supermajority. -/
theorem quorum_gate_decision_below_supermajority :
    quorumGateDecision "n=4;V=0:7:9,1:7:9" = some none := by native_decide

/-- Malformed wires are FAIL-CLOSED to the `ERR` sentinel (the collector finalizes NOTHING). -/
theorem quorum_gate_garbage_is_err : quorumGate "not a wire" = "ERR" := by native_decide

theorem quorum_gate_bad_vote_is_err : quorumGate "n=4;V=bad" = "ERR" := by native_decide

theorem quorum_gate_bad_committee_size_is_err :
    quorumGate "n=x;V=0:7:9" = "ERR" := by native_decide

/-- A malformed wire decodes to `none` at the DECISION level too — the outer `Option` is what
distinguishes "unparseable" from "parsed, no quorum". -/
theorem quorum_gate_decision_garbage_is_none :
    quorumGateDecision "not a wire" = none := by native_decide

#assert_compiled quorum_gate_decision_on_a_supermajority
#assert_compiled quorum_gate_decision_below_supermajority
#assert_compiled quorum_gate_garbage_is_err
#assert_compiled quorum_gate_bad_vote_is_err
#assert_compiled quorum_gate_bad_committee_size_is_err
#assert_compiled quorum_gate_decision_garbage_is_none

#assert_axioms quorum_gate_decision_eq
#assert_axioms quorum_gate_eq_encode_decision
#assert_axioms quorum_gate_decision_is_verified
#assert_axioms quorum_gate_finalizes_iff_verified
#assert_axioms quorum_gate_sound
#assert_axioms quorum_gate_root_unique
#assert_axioms quorum_gate_deterministic
#assert_axioms quorum_gate_binds_receipt_stream

end Dregg2.Distributed.FinalityGate
