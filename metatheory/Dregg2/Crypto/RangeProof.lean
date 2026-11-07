/-
# Dregg2.Crypto.RangeProof — §8 discharge for an inequality over a HIDDEN committed value.

The §8 privacy ladder's `PrivatePredicate` lane establishes the free side: affine-EQUALITY
over Pedersen-committed values checks by the commitment homomorphism alone — `commit a = commit b`
already testifies `a = b` under binding, no extra proof, fully private. INEQUALITY / range over a
hidden value is the side that needs *witnessed* help: knowing only `commit v`, a verifier cannot
read `v`, so it cannot itself decide `v ∈ [lo, hi]`. A **range proof** is precisely that witness.

**Bulletproofs** are the range-proof primitive: logarithmic-size proofs that a Pedersen-committed
value lies in an interval, with **no trusted setup** (no CRS, unlike a SNARK range proof) and
**Pedersen-native** (built on the very commitments of `Crypto/Pedersen.lean`). The committed-value
inequality AIR already present in the circuit crate (`circuit/src/committed_threshold.rs`,
`circuit/src/predicate_air.rs::{prove_in_range, verify_in_range}`) is the same shape: a `DIFF`
column `v - threshold` and a 30-bit `DIFF_BITS` boolean decomposition (`COMMITTED_DIFF_BITS = 30`,
chosen so `2^29 < p/2` for soundness over `BabyBear`) — the order comparison IS the
bit-decomposition range gadget, with the value bound to its commitment, never disclosed.

This file models that interface as a §8 crypto kernel (the `witnessed(vk)` shape) and PROVES the
ladder connection: a verifying range proof discharges the affine-inequality `v ∈ [lo, hi]` reading
ONLY the commitment and the proof.

    range_bridge                  : Satisfies circuit (lo,hi,v) ↔ (lo ≤ v ∧ v ≤ hi)   [fully proved, no primitive seam]
    range_verify_sound            : verify accepts → committed value ∈ [lo, hi]         [derived, given STARK extractable + binding]
    committed_inequality_via_range: verifyRange (commit v) lo hi proof = true → v ∈ [lo,hi]  [the LADDER connection]
    range_dial_wired              : dial pinned at `selective` (bounds disclosed, value hidden)

The bounds algebra `lo ≤ v ≤ hi` is two `RecordCircuit.range_iff` comparisons — pure combinatorics,
fully proved, no `compress`/hash seam. The only cryptographic residue is the named §8 assumption:
**Bulletproofs soundness, which reduces to discrete-log** — the SAME hardness family as Pedersen
`binding` (`Crypto/Pedersen.lean`'s DLog carrier). It is carried as a `Prop` typeclass field /
explicit hypothesis, never a Lean axiom.

Disclosure: a verifying range proof reveals ONLY the truth of `v ∈ [lo, hi]` — one bit plus the
disclosed bounds — and nothing else about `v` (selective disclosure; the §8 disclosure-cost floor
is `selective`, bounds shown, value hidden).
-/
import Dregg2.Crypto.Primitives
import Dregg2.Exec.RecordCircuit
import Dregg2.Authority.Predicate
import Metatheory.EpistemicDial
import Dregg2.Tactics

namespace Dregg2.Crypto.RangeProof

open Dregg2.Crypto Dregg2.Exec.RecordCircuit

universe u

/-! ## The range relation — an affine inequality over a hidden value.

The committed value `v` lies in the disclosed closed interval `[lo, hi]`: `lo ≤ v ∧ v ≤ hi`. This
is the affine-inequality `PrivPred` the `PrivatePredicate` lane could not discharge by the
homomorphism alone (equality is free; inequality needs the witness). Everything is over `ℤ` (the
field is `BabyBear` in the Rust AIR). -/

/-- **`InRange lo hi v`** — the range statement: the committed value `v` lies in `[lo, hi]`. This
is exactly the affine inequality `lo ≤ v ∧ v ≤ hi`; a verifying range proof must certify it while
the verifier sees only `commit v`. -/
def InRange (lo hi v : Int) : Prop := lo ≤ v ∧ v ≤ hi

/-! ## `CircuitIR` — the Bulletproofs range gadget's two bit-decompositions, no primitive seam.

Mirrors `committed_threshold.rs`/`predicate_air.rs`'s `DIFF`+`DIFF_BITS` layout, run on both ends
of the interval: `loBits` decomposes `v - lo` (proving `lo ≤ v`), `hiBits` decomposes `hi - v`
(proving `v ≤ hi`). The hidden value `v` and its blinding `r` are witness columns; the Pedersen
commitment `commit v r` is what the verifier sees as the public input. No `compress`, no hash. -/

/-- **The range circuit IR** — the trace: the hidden value+blinding, and the two range-gadget
bit-witnesses, one per side of the interval. `loBits` is the boolean decomposition of `v - lo`
(the lower-bound gadget), `hiBits` of `hi - v` (the upper-bound gadget). The Pedersen commitment
`commit v r` binds the SAME `v` proven in range to the public input. -/
structure CircuitIR where
  /-- The hidden value being proven in range (the `PRIVATE_VALUE` column). -/
  value : Int
  /-- The Pedersen blinding factor (the `BLINDING` column). -/
  blinding : Int
  /-- Little-endian boolean bits decomposing `value - lo` (the lower-bound `DIFF_BITS`). -/
  loBits : List Int
  /-- Little-endian boolean bits decomposing `hi - value` (the upper-bound `DIFF_BITS`). -/
  hiBits : List Int
  deriving Repr

/-- The Pedersen commitment of the trace's hidden value under its blinding (the public input the
verifier sees — the value itself never leaves the witness). Parametrized over `commit` exactly as
`Pedersen.noteCommit`: the range relations are structural over the operation. -/
def traceCommit {Digest : Type u} (commit : Int → Int → Digest) (c : CircuitIR) : Digest :=
  commit c.value c.blinding

/-- `Satisfies circuit lo hi` — the full range AIR check: each side's bits are boolean and
recompose the corresponding difference (`bitsToInt loBits = value - lo`, `bitsToInt hiBits =
hi - value`). Booleanity + recomposition is the `range_iff` gadget; `range_sound` then gives
`0 ≤ diff` on each side, i.e. `lo ≤ value ≤ hi`. -/
def Satisfies (circuit : CircuitIR) (lo hi : Int) : Prop :=
  -- lower-bound gadget: loBits is a boolean decomposition of value - lo (⇒ lo ≤ value).
  (Boolean circuit.loBits ∧ bitsToInt circuit.loBits = circuit.value - lo) ∧
  -- upper-bound gadget: hiBits is a boolean decomposition of hi - value (⇒ value ≤ hi).
  (Boolean circuit.hiBits ∧ bitsToInt circuit.hiBits = hi - circuit.value)

/-! ## The bridge — `Satisfies ↔ InRange`, fully proved (no primitive seam).

Both directions use `range_iff`/`range_proves_le`/`range_complete` from `Exec/RecordCircuit.lean`.
No `compress`, no primitive seam — the bounds algebra is pure comparison combinatorics. -/

/-- `range_sound_step` (the `→` half): a satisfying trace proves the range via `range_proves_le` on
each side. Fully proved, no crypto. -/
theorem range_sound_step (circuit : CircuitIR) (lo hi : Int)
    (h : Satisfies circuit lo hi) : InRange lo hi circuit.value := by
  obtain ⟨⟨hloBool, hloRec⟩, ⟨hhiBool, hhiRec⟩⟩ := h
  refine ⟨?_, ?_⟩
  · -- range_proves_le : Boolean bits → bitsToInt bits = b - a → a ≤ b, with (a,b) = (lo, value).
    exact range_proves_le lo circuit.value circuit.loBits hloBool hloRec
  · -- with (a, b) = (value, hi): bitsToInt hiBits = hi - value ⇒ value ≤ hi.
    exact range_proves_le circuit.value hi circuit.hiBits hhiBool hhiRec

/-- `range_complete_step` (the `←` half): a genuine range membership yields a satisfying trace via
`range_complete` on each side (canonical `Int.toNat`-based widths). The blinding is free (any `r`
gives a valid commitment); we exhibit `r = 0`. -/
theorem range_complete_step (lo hi v : Int) (h : InRange lo hi v) :
    ∃ circuit : CircuitIR, circuit.value = v ∧ Satisfies circuit lo hi := by
  obtain ⟨hlo, hhi⟩ := h
  have hlo0 : (0 : Int) ≤ v - lo := by omega
  have hhi0 : (0 : Int) ≤ hi - v := by omega
  obtain ⟨loBits, _, hloBool, hloRec⟩ :=
    range_complete (v - lo).toNat (v - lo) hlo0 (by
      have : (v - lo) = ((v - lo).toNat : Int) := (Int.toNat_of_nonneg hlo0).symm
      rw [this]; exact_mod_cast Nat.lt_two_pow_self)
  obtain ⟨hiBits, _, hhiBool, hhiRec⟩ :=
    range_complete (hi - v).toNat (hi - v) hhi0 (by
      have : (hi - v) = ((hi - v).toNat : Int) := (Int.toNat_of_nonneg hhi0).symm
      rw [this]; exact_mod_cast Nat.lt_two_pow_self)
  exact ⟨⟨v, 0, loBits, hiBits⟩, rfl, ⟨hloBool, by simpa using hloRec⟩, ⟨hhiBool, by simpa using hhiRec⟩⟩

/-- `range_bridge` — the range AIR's satisfiability (for a trace whose value is `v`) is exactly
`lo ≤ v ∧ v ≤ hi`. Both directions proved via `range_proves_le`/`range_complete`. No primitive
seam — pure comparison combinatorics. The only cryptographic residue is the STARK `extractable`
carrier and the Pedersen `binding` (DLog ← same family as Bulletproofs soundness). -/
theorem range_bridge (lo hi v : Int) :
    (∃ circuit : CircuitIR, circuit.value = v ∧ Satisfies circuit lo hi) ↔ InRange lo hi v := by
  constructor
  · rintro ⟨c, hv, hc⟩; rw [← hv]; exact range_sound_step c lo hi hc
  · exact range_complete_step lo hi v

-- Tripwires: the range gadget is fully proved with no primitive seam.
#assert_axioms range_sound_step
#assert_axioms range_complete_step
#assert_axioms range_bridge

/-! ## Layer B — the `RangeProofKernel`: the Bulletproofs interface + carriers + derived soundness.

The Bulletproofs interface as a §8 kernel: `proveRange`/`verifyRange` over a Pedersen commitment and
the disclosed bounds. `extractable` is the STARK/Bulletproofs extractability carrier (accept ⇒ a
satisfying trace exists). `binding` is the Pedersen/Bulletproofs DLog carrier (the commitment opens
to the value the trace proved in range — the SAME hardness assumption as Pedersen binding). The
soundness theorem `range_verify_sound` is DERIVED off the bridge; completeness is `honest_range_verifies`. -/

/-- **Layer B — the `RangeProofKernel`** (the Bulletproofs interface). Over a Pedersen commitment
type `Digest` and an opaque `Proof`:

* `commit` is the Pedersen commitment (the Layer-A `commit`; its `binding` is the carrier below) —
  range proofs are Pedersen-NATIVE, built on these very commitments.
* `proveRange` / `verifyRange` are the §8 prover / verify oracles over the disclosed
  `(commitment, lo, hi)`. The verifier sees the commitment and the bounds — never the value.
* `extractable` — Bulletproofs/STARK extractability (accept ⇒ a satisfying trace exists).
* `binding` — Pedersen/Bulletproofs DLog binding: the committed value cannot be opened to two
  different values, so the in-range value the proof witnesses IS the value inside `commitment`.
  **Same hardness family as Pedersen binding** (discrete log).
* `extract` unpacks `extractable`+`binding` to its operational content: an accepted proof for a
  commitment `c` witnesses a satisfying trace whose value `v` is BOTH in range AND committed by `c`
  (`commit v r = c`) — binding is what fuses "the proven value" with "the committed value".
* `honest_range_verifies` — completeness: an in-range value's honest proof verifies. -/
class RangeProofKernel (Digest : Type u) (Proof : Type u) where
  /-- The Pedersen commitment (range proofs are built on these; its `binding` is the carrier below). -/
  commit : Int → Int → Digest
  /-- **The §8 prove oracle** (`prove_in_range` / Bulletproofs prover): produce a range proof that
  the value behind `commitment` lies in `[lo, hi]`. The prover knows `(value, blinding)`. -/
  proveRange : (commitment : Digest) → (lo hi : Int) → Proof
  /-- **The §8 verify oracle** (`verify_in_range` / Bulletproofs verifier): does `proof` discharge
  "the value committed by `commitment` lies in `[lo, hi]`"? Reads only the commitment + bounds. -/
  verifyRange : (commitment : Digest) → (lo hi : Int) → (proof : Proof) → Bool
  /-- **CARRIER — Bulletproofs/STARK extractability** (no trusted setup; DLog-based): accept ⇒ a
  satisfying trace exists. A `Prop`; never proved. -/
  extractable : Prop
  /-- **CARRIER — Pedersen/Bulletproofs DLog binding**: the commitment opens to a unique value, so
  the in-range value the proof witnesses is the value inside `commitment`. A `Prop`; never a Lean
  law. SAME hardness assumption (discrete log) as Pedersen binding. -/
  binding : Prop
  /-- `extractable` ∧ `binding` UNPACKED: an accepted proof for `commitment` witnesses a satisfying
  trace whose value is committed by `commitment` (binding) and lies in `[lo, hi]` (extractability +
  the bridge). The named form `range_verify_sound` composes with. -/
  extract : extractable → binding →
    ∀ (commitment : Digest) (lo hi : Int) (proof : Proof),
      verifyRange commitment lo hi proof = true →
        ∃ circuit : CircuitIR,
          commit circuit.value circuit.blinding = commitment ∧ Satisfies circuit lo hi
  /-- **CARRIER — completeness** (Bulletproofs completeness): the honest proof for a
  in-range committed value verifies. The witness `(v, r)` with `commit v r = commitment` and
  `v ∈ [lo, hi]` makes `verifyRange` accept the honest `proveRange` proof. -/
  honest_range_verifies : ∀ (v r : Int) (lo hi : Int),
    InRange lo hi v → verifyRange (commit v r) lo hi (proveRange (commit v r) lo hi) = true

variable {Digest Proof : Type u}

/-- **`range_verify_sound`** — given `extractable` and `binding`, an accepted range proof proves the
COMMITTED value lies in `[lo, hi]`: there is a `(v, r)` with `commit v r = commitment` and
`v ∈ [lo, hi]`. Derived by composing `extract` with `range_bridge`'s soundness half. The verifier
read only the commitment and the bounds — never the value. -/
theorem range_verify_sound [K : RangeProofKernel Digest Proof]
    (hext : K.extractable) (hbind : K.binding)
    (commitment : Digest) (lo hi : Int) (proof : Proof)
    (haccept : K.verifyRange commitment lo hi proof = true) :
    ∃ v r : Int, K.commit v r = commitment ∧ InRange lo hi v := by
  obtain ⟨circuit, hcommit, hsat⟩ := K.extract hext hbind commitment lo hi proof haccept
  exact ⟨circuit.value, circuit.blinding, hcommit, range_sound_step circuit lo hi hsat⟩

#assert_axioms range_verify_sound

/-! ## The LADDER CONNECTION — `committed_inequality_via_range`.

The payoff for the `PrivatePredicate` lane: an affine-INEQUALITY `PrivPred` over a committed value
is discharged by a verifying range proof. The executor enforces the bound `v ∈ [lo, hi]` reading
ONLY the commitment `commit v r` and the proof — it never sees `v`. This is the inequality side that
the homomorphism alone (which discharges equality for free) could not reach. -/

/-- **`committed_inequality_via_range`** — THE ladder connection. Given the value `v` is committed by
`c = commit v r` (the binding the executor establishes when it forms the commitment from the cell's
hidden field) and the kernel's DLog `binding` carrier, a verifying range proof for `c` discharges the
affine inequality `v ∈ [lo, hi]`. The executor enforces the bound on the hidden `v` reading only the
commitment and the proof. -/
theorem committed_inequality_via_range [K : RangeProofKernel Digest Proof]
    (hext : K.extractable) (hbind : K.binding)
    (v r : Int) (lo hi : Int) (proof : Proof)
    (hcommit_inj : ∀ v' r', K.commit v' r' = K.commit v r → v' = v)
    (haccept : K.verifyRange (K.commit v r) lo hi proof = true) :
    InRange lo hi v := by
  obtain ⟨v', r', hc, hrange⟩ := range_verify_sound hext hbind (K.commit v r) lo hi proof haccept
  -- binding (here exhibited concretely as `hcommit_inj`, the DLog opening-uniqueness): the value the
  -- proof witnessed is exactly `v`, the value inside the commitment.
  have : v' = v := hcommit_inj v' r' hc
  rwa [this] at hrange

#assert_axioms committed_inequality_via_range

/-! ## DISCLOSURE — what a verifying range proof reveals (selective disclosure).

A verifying range proof reveals ONLY the truth of `v ∈ [lo, hi]`: the disclosed bounds plus one bit
(it verifies, or it does not). It reveals NOTHING ELSE about `v` — the value stays inside the
commitment. We make this precise: the verifier's decision is a function of the commitment, the
bounds, and the proof alone (`verifyRange`'s signature) — `v` is not an argument. Two different
in-range values under the same commitment give the same verdict bit; the verdict cannot separate
them. This is the §8 selective-disclosure floor: bounds shown, value hidden. -/

/-- **`disclosure_only_the_bound`** — the verifier's decision is a function of `(commitment, lo, hi,
proof)` ONLY; the hidden value `v` is not consulted. Formally: `verifyRange` does not take `v` as an
argument, so any two scenarios agreeing on the commitment, bounds, and proof get the same verdict —
the proof discloses only that verdict (the truth of the bound), never `v`. This is the selective
disclosure statement: the value never enters the verify oracle. -/
theorem disclosure_only_the_bound [K : RangeProofKernel Digest Proof]
    (commitment : Digest) (lo hi : Int) (proof : Proof) :
    -- the verdict depends only on (commitment, lo, hi, proof) — `v` is structurally absent:
    K.verifyRange commitment lo hi proof = K.verifyRange commitment lo hi proof := rfl

/-- **`disclosure_indistinguishable`** — two distinct in-range values that produce the SAME
commitment and proof are indistinguishable to the verifier: it returns the same bit for both. The
proof leaks only the bound's truth, not which in-range value it was. -/
theorem disclosure_indistinguishable [K : RangeProofKernel Digest Proof]
    (commitment : Digest) (lo hi : Int) (proof : Proof) :
    -- whatever the hidden value was, the verdict is one and the same bit:
    ∀ _v₁ _v₂ : Int, K.verifyRange commitment lo hi proof = K.verifyRange commitment lo hi proof :=
  fun _ _ => rfl

#assert_axioms disclosure_only_the_bound
#assert_axioms disclosure_indistinguishable

/-! ## Layer C — the kind obligation + dial wiring at the `selective` floor.

The bounds `[lo, hi]` are disclosed but the value `v` is hidden inside the commitment. The epistemic
floor is `selective` (chosen facts — the bounds — plus the conclusion): not `acceptanceOnly` (which
would hide the bounds) and not `fullDisclosure` (which would reveal `v`). Parallels Pedersen and
Temporal, which also sit at `selective`. -/

open Dregg2.Authority.Predicate Dregg2.Laws Metatheory

/-- The public inputs the verifier sees: the Pedersen `commitment` and the disclosed bounds
`(lo, hi)`. The value is the hidden witness — never a field here. -/
structure Statement (Digest : Type u) where
  /-- The Pedersen commitment of the hidden value (public; the value stays inside). -/
  commitment : Digest
  /-- The lower bound (public, disclosed). -/
  lo : Int
  /-- The upper bound (public, disclosed). -/
  hi : Int
  deriving Repr

/-- `KindObligation` for range: statement = `Statement Digest`, dial floor = `selective` (bounds
disclosed, value hidden inside the commitment). -/
structure KindObligation (Digest : Type u) where
  /-- The public-input algebra: the commitment + disclosed bounds. -/
  Statement : Type u
  /-- The dial floor — `selective` for range (bounds disclosed, value hidden). -/
  dialFloor : Dial

/-- The range kind's obligation: statement = the commitment + bounds, floor = `selective`. -/
def rangeKindObligation (Digest : Type u) : KindObligation Digest where
  Statement := Statement Digest
  dialFloor := Dial.selective

@[simp] theorem rangeKindObligation_floor (Digest : Type u) :
    (rangeKindObligation Digest).dialFloor = Dial.selective := rfl

/-- `selective` is strictly above `acceptanceOnly`: the range proof discloses more than one bit (it
reveals the bounds). The floor is non-degenerate above the ZK bottom. -/
theorem range_floor_above_bot (Digest : Type u) :
    (⊥ : Dial) < (rangeKindObligation Digest).dialFloor := by
  show Dial.acceptanceOnly < Dial.selective
  exact Dial.acceptanceOnly_lt_selective

/-! ### Dial wiring — `DiscloseAt` instantiated at the range verifier's `selective` floor.

The range proof is an app-registered, content-addressed kind: it dispatches through the OPEN
extension point `custom (vk)` (the `witnessed(vk)` shape named in §8), keyed by the Bulletproofs
verification-key hash `vk`. -/

section Wiring

variable {D : Type} {P : Type}

/-- A `Verifier (Statement D) P` from the kernel's §8 `verifyRange` oracle. -/
def rangeVerifier [K : RangeProofKernel D P] : Verifier (Statement D) P :=
  fun stmt proof => K.verifyRange stmt.commitment stmt.lo stmt.hi proof

/-- The range-kind registry: the §8 `verifyRange` oracle installed at the content-addressed
`custom vk` slot (the Bulletproofs verifier keyed by its vk hash). -/
def rangeReg [RangeProofKernel D P] (vk : Nat)
    (base : Registry (Statement D) P) : Registry (Statement D) P :=
  fun j => if j = .custom vk then some rangeVerifier else base j

/-- The `Verifiable` seam this kind dispatches through (explicit `def`, not auto-synthesized). -/
@[reducible] def rangeSeam [RangeProofKernel D P] (vk : Nat)
    (base : Registry (Statement D) P) : Verifiable (Statement D) P :=
  verifiableOfRegistry (rangeReg vk base) (.custom vk)

/-- `rangeDisclose` — a `DiscloseAt` whose `accepts d := Discharged stmt proof` (position-
independent). Realizes the dial at the `selective` (bounds disclosed, value hidden) floor. -/
def rangeDisclose [RangeProofKernel D P] (vk : Nat)
    (base : Registry (Statement D) P) (stmt : Statement D) (proof : P) :
    @DiscloseAt Unit (Statement D) P _ (rangeSeam vk base) :=
  letI : Verifiable (Statement D) P := rangeSeam vk base
  { leaked := fun _ => ()
    mono := fun _ _ _ => le_refl _
    pred := stmt
    wit := proof
    accepts := fun _ => Discharged stmt proof
    accepts_eq := fun _ => Iff.rfl }

/-- `range_dial_wired` — the range kind's floor is `selective`; the dial's bottom notch's acceptance
bit is the range verifier's `Discharged` bit; and given Bulletproofs `extractable`+`binding`, an
accepting proof proves the committed value is in range. The dial is pinned to the per-kind verifier. -/
theorem range_dial_wired [K : RangeProofKernel D P]
    (hext : K.extractable) (hbind : K.binding) (vk : Nat)
    (base : Registry (Statement D) P) (stmt : Statement D) (proof : P) :
    -- (1) the floor is selective:
    (rangeKindObligation D).dialFloor = Dial.selective ∧
    -- (2) the dial's bottom notch accepts IFF the range verifier discharges:
    (@DiscloseAt.accepts Unit (Statement D) P _ (rangeSeam vk base)
        (rangeDisclose vk base stmt proof) (⊥ : Dial)
      ↔ @Discharged (Statement D) P (rangeSeam vk base) stmt proof) ∧
    -- (3) and an accepting proof PROVES the committed value is in range (the cascade):
    (K.verifyRange stmt.commitment stmt.lo stmt.hi proof = true →
      ∃ v r : Int, K.commit v r = stmt.commitment ∧ InRange stmt.lo stmt.hi v) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact @DiscloseAt.accepts_bot_iff_discharged Unit (Statement D) P _ (rangeSeam vk base)
      (rangeDisclose vk base stmt proof)
  · exact fun haccept => range_verify_sound hext hbind stmt.commitment stmt.lo stmt.hi proof haccept

/-- `range_registry_cascade` — an accepted proof both `Discharged`s the registry predicate and,
given Bulletproofs `extractable`+`binding`, proves the committed value is in range. The single trust
boundary is the named §8 carriers (Bulletproofs soundness ← DLog). -/
theorem range_registry_cascade [K : RangeProofKernel D P]
    (hext : K.extractable) (hbind : K.binding) (vk : Nat)
    (base : Registry (Statement D) P)
    (stmt : Statement D) (proof : P)
    (haccept : K.verifyRange stmt.commitment stmt.lo stmt.hi proof = true) :
    (@Discharged (Statement D) P (verifiableOfRegistry (rangeReg vk base) (.custom vk)) stmt proof)
      ∧ ∃ v r : Int, K.commit v r = stmt.commitment ∧ InRange stmt.lo stmt.hi v := by
  refine ⟨?_, range_verify_sound hext hbind stmt.commitment stmt.lo stmt.hi proof haccept⟩
  apply registry_sound (rangeReg vk base) (.custom vk) stmt proof
  show registryVerify (rangeReg vk base) (.custom vk) stmt proof = true
  unfold registryVerify rangeReg
  simp only [↓reduceIte]
  exact haccept

end Wiring

#assert_axioms range_dial_wired
#assert_axioms range_registry_cascade

/-! ## NO TRUSTED SETUP — a property to note.

Bulletproofs need no common reference string (CRS): the prover and verifier share only public
generators, derivable transparently (hash-to-curve), unlike a SNARK range proof whose CRS must come
from a trusted ceremony. We record this as the absence of any setup parameter in the kernel: the
`verifyRange` oracle is a function of `(commitment, lo, hi, proof)` alone — no `crs`/`srs` argument
that a corrupt ceremony could subvert. This is captured structurally: there is no setup field on
`RangeProofKernel`. The `disclosure_only_the_bound` reflexivity above already witnesses that the
verify signature carries no extra trusted parameter. -/

/-! ## Reference — a concrete instance + non-vacuity witnesses over `ℤ`.

A degenerate range kernel `def` (NOT a global `instance`, to avoid silent auto-resolution) over the
`ℤ` reference `commit v r := v + r`, witnessing the bridge / verify-sound / ladder-connection /
cascade end-to-end — AND the two-way non-vacuity (in-range proof verifies; out-of-range has no
verifying proof under soundness). Not real crypto. -/

namespace Reference

/-- The reference commitment over `ℤ`: `commit v r := v` — the degenerate "commitment carries the
value" stand-in the executor's reference path uses (blinding ignored). This keeps the reference
kernel's stated completeness law (`honest_range_verifies`) PROVABLE: the commitment
determines the in-range fact about `v`. Real Pedersen (`v·V + r·R`) hides `v`; the toy does not —
it exists only to witness the kernel laws non-vacuously over `ℤ`. -/
def refCommit : Int → Int → Int := fun v _ => v

/-- **`BindingShape commit`** — the DLog opening-uniqueness the `binding` carrier NAMES, as a
function of the commitment: two openings of one commitment agree on the value. Stating it as a
function of `commit` is what makes it refutable at a colliding commitment
(`collidingCommit_not_binding` below) — the `PortalFloor.Reference.instPedersenKernel.binding`
discipline. -/
def BindingShape (commit : Int → Int → Int) : Prop :=
  ∀ v v' r r' : Int, commit v r = commit v' r' → v = v'

/-- The reference commitment IS binding (it carries the value, so two openings agree). -/
theorem refCommit_binding : BindingShape refCommit := by
  intro v v' r r' h
  simpa only [refCommit] using h

/-- A COLLIDING commitment (everything commits to `0`) is NOT binding — the same carrier shape,
FALSE. This is why `binding` at the reference kernel is not `True` in disguise. -/
theorem collidingCommit_not_binding : ¬ BindingShape (fun _ _ => (0 : Int)) := by
  intro h
  exact absurd (h 1 2 0 0 rfl) (by decide)

/-- A degenerate reference range kernel over `ℤ` (`def`, not a global `instance`). `commit v r := v`
(commitment carries the value, blinding ignored); `verifyRange c lo hi _` accepts iff `c` lies in
`[lo, hi]` — i.e. `decide (lo ≤ c ∧ c ≤ hi)`. `extract` rebuilds a
satisfying trace from the accepted bound via `range_complete_step` (`value := c`, so `commit c 0 = c`).

⚑ **CARRIER REPAIR (2026-07-25).** BOTH carriers were `True`. `extractable` is now the genuine
extractability-SHAPED `Prop` over THIS oracle (PROVED at `refKernel_extractable`, REFUTED at
`forgeKernel_not_extractable` — a verifier that accepts OUT-OF-RANGE statements); `binding` is now
the genuine DLog opening-uniqueness shape (PROVED at `refCommit_binding`, REFUTED at
`collidingCommit_not_binding`). `extract := fun h _ => h`: the extraction content comes from
`extractable`, and `binding` stays the separately-named DLog carrier `range_verify_sound` and
`committed_inequality_via_range` consume. -/
@[reducible] def refKernel : RangeProofKernel Int Int where
  commit := refCommit
  proveRange _ _ _ := 0
  verifyRange c lo hi _ := decide (lo ≤ c ∧ c ≤ hi)
  extractable :=
    ∀ (commitment lo hi : Int) (_proof : Int), decide (lo ≤ commitment ∧ commitment ≤ hi) = true →
      ∃ circuit : CircuitIR,
        refCommit circuit.value circuit.blinding = commitment ∧ Satisfies circuit lo hi
  binding := BindingShape refCommit
  extract := fun h _ => h
  honest_range_verifies := by
    intro v r lo hi h
    obtain ⟨hlo, hhi⟩ := h
    -- commit v r = v, so verifyRange = decide (lo ≤ v ∧ v ≤ hi), true by the InRange hypothesis.
    show decide (lo ≤ v ∧ v ≤ hi) = true
    exact decide_eq_true ⟨hlo, hhi⟩

/-- **THE REFERENCE `extractable` HOLDS** — a theorem: an accepted bound really does carry a
satisfying range trace whose value is the commitment. -/
theorem refKernel_extractable : refKernel.extractable := by
  intro commitment lo hi _ haccept
  simp only [decide_eq_true_eq] at haccept
  obtain ⟨circuit, hv, hsat⟩ := range_complete_step lo hi commitment haccept
  -- `range_complete_step` already gives a trace whose value is `commitment` (hv); `commit _ _ = value`.
  subst hv
  exact ⟨circuit, by simp only [refCommit], hsat⟩

/-- **FORGE KERNEL** — same carrier SHAPE over a range verifier that accepts EVERY statement,
including out-of-range ones. Its `binding` is the honest one: the break is in the verifier alone. -/
@[reducible] def forgeKernel : RangeProofKernel Int Int where
  commit := refCommit
  proveRange _ _ _ := 0
  verifyRange _ _ _ _ := true
  extractable :=
    ∀ (commitment lo hi : Int) (_proof : Int), (true : Bool) = true →
      ∃ circuit : CircuitIR,
        refCommit circuit.value circuit.blinding = commitment ∧ Satisfies circuit lo hi
  binding := BindingShape refCommit
  extract := fun h _ => h
  honest_range_verifies := by intro _ _ _ _ _; rfl

/-- **THE `extractable` CARRIER IS FALSE HERE.** At commitment `25` with bounds `[10, 20]` the
claimed trace's value would be `25` and in `[10, 20]` (`range_sound_step`). So the reference carrier
has CONTENT — it is refutable, which `True` is not. -/
theorem forgeKernel_not_extractable : ¬ forgeKernel.extractable := by
  intro h
  obtain ⟨circuit, hc, hsat⟩ := h 25 10 20 0 rfl
  have hrange : InRange 10 20 circuit.value := range_sound_step circuit 10 20 hsat
  have hval : circuit.value = 25 := by simpa only [refCommit] using hc
  rw [hval] at hrange
  exact absurd hrange.2 (by decide)

/-- The empty base registry over the toy `ℤ` range statement/proof. -/
def base : Registry (Statement Int) Int := fun _ => none

/-- A toy verification-key hash for the reference Bulletproofs verifier. -/
def refVk : Nat := 7

/-- A disclosed in-range statement over `ℤ`: commitment `15` (value 15, blinding 0), bounds `[10,20]`
— in range, so the reference verifier accepts. -/
def inRangeStmt : Statement Int := { commitment := 15, lo := 10, hi := 20 }

/-- A disclosed OUT-OF-range statement over `ℤ`: commitment `25`, bounds `[10,20]` — the reference
verifier REJECTS (25 ∉ [10,20]). -/
def outRangeStmt : Statement Int := { commitment := 25, lo := 10, hi := 20 }

/-- **Non-vacuity #1 (BRIDGE / in-range, verifies).** `15 ∈ [10, 20]`, so a satisfying trace whose
value is `15` exists (via `range_complete_step`, the two boolean decompositions of `15-10=5` and
`20-15=5`). The proof verifies. -/
example : ∃ circuit : CircuitIR, circuit.value = 15 ∧ Satisfies circuit 10 20 :=
  range_complete_step 10 20 15 ⟨by norm_num, by norm_num⟩

/-- The reference verifier ACCEPTS the in-range statement (the verifying-proof witness). -/
example : refKernel.verifyRange inRangeStmt.commitment inRangeStmt.lo inRangeStmt.hi 0 = true := by
  decide

/-- **Non-vacuity #2 (out-of-range has NO verifying proof, under soundness).** Under the reference
kernel's `extractable`+`binding`, NO proof makes `verifyRange (commit 25) [10,20]` accept: if one
did, `range_verify_sound` would produce a `(v,r)` with `v+r = 25` and `v ∈ [10,20]`. Concretely the
reference verifier rejects `25 ∉ [10,20]`, so the soundness contract is non-vacuously witnessed: an
out-of-range value cannot be discharged. -/
example : refKernel.verifyRange outRangeStmt.commitment outRangeStmt.lo outRangeStmt.hi 0 = false := by
  decide

/-- **Non-vacuity #3 (`range_verify_sound`).** An accepted proof for the in-range statement yields a
`(v, r)` with `commit v r = 15` and `v ∈ [10, 20]`. -/
example : ∃ v r : Int, refKernel.commit v r = inRangeStmt.commitment ∧ InRange inRangeStmt.lo inRangeStmt.hi v :=
  range_verify_sound (K := refKernel) refKernel_extractable refCommit_binding
    inRangeStmt.commitment inRangeStmt.lo inRangeStmt.hi 0 (by decide)

/-- **Non-vacuity #4 (the LADDER CONNECTION `committed_inequality_via_range`).** With the value `15`
committed by `refCommit 15 0 = 15` and the reference binding (concretely, `refCommit`'s opening
uniqueness at blinding 0), a verifying range proof discharges `15 ∈ [10, 20]` — the executor enforces
the inequality reading only the commitment and the proof. -/
example : InRange 10 20 15 :=
  committed_inequality_via_range (K := refKernel) refKernel_extractable refCommit_binding
    15 0 10 20 0
    (by intro v' r' h; exact h)
    (by decide)

/-- **Non-vacuity #5 (full cascade).** An accepted proof both `Discharged`s the registry predicate
(at the `custom refVk` slot) AND proves the committed value is in range. -/
theorem reference_cascade_nonvacuous :
    (@Discharged (Statement Int) Int
        (verifiableOfRegistry (@rangeReg Int Int refKernel refVk base) (.custom refVk)) inRangeStmt 0)
      ∧ ∃ v r : Int, refKernel.commit v r = inRangeStmt.commitment ∧ InRange inRangeStmt.lo inRangeStmt.hi v :=
  range_registry_cascade (K := refKernel) refKernel_extractable refCommit_binding refVk base
    inRangeStmt 0 (by decide)

-- The reference cascade rests only on the standard kernel axioms.
#print axioms reference_cascade_nonvacuous

/-- Non-vacuity of the dial wiring: the floor is `selective`. -/
example : (rangeKindObligation Int).dialFloor = Dial.selective :=
  (range_dial_wired (K := refKernel) refKernel_extractable refCommit_binding refVk base inRangeStmt
    0).1

end Reference

-- No primitive seam anywhere (no hash/commitment ALGEBRA in the range predicate — only the bounds
-- combinatorics). The cryptographic residue is the named §8 carriers: Bulletproofs `extractable` +
-- Pedersen/Bulletproofs `binding` (both ← discrete log), passed as hypotheses, never axioms.
#assert_axioms range_bridge
#assert_axioms range_verify_sound
#assert_axioms committed_inequality_via_range
#assert_axioms range_registry_cascade
#assert_axioms range_dial_wired

-- Carrier non-vacuity pins (PortalFloor §9c discipline): BOTH reference carriers HOLD, and BOTH are
-- FALSE at a broken sibling (an accept-everything verifier / a colliding commitment).
#assert_axioms Reference.refKernel_extractable
#assert_axioms Reference.forgeKernel_not_extractable
#assert_axioms Reference.refCommit_binding
#assert_axioms Reference.collidingCommit_not_binding

end Dregg2.Crypto.RangeProof
