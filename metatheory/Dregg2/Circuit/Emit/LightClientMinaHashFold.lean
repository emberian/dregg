/-
# Dregg2.Circuit.Emit.LightClientMinaHashFold — folding out the Mina POSEIDON linkage carrier
`LINK_OK`, and the canonicality carrier `CANON_OK`: the state-hash chain binding becomes DERIVED by
an in-circuit Poseidon chain plus a Lean-authored width gate, not two trusted witnessed bits.

⚑ SUBSTRATE, SAID OUT LOUD (House Law #1). The ONE AIR object in this file — `minaRowWidthGates` —
is **LEAN-AUTHORED**: a `def`-generator over `AirBuilder.Head`, produced from `AirBuilder.rangeNonneg`
via `StakeWidthRange.widthGate`, with a FORCING lemma (`minaRowWidthGates_forces`) stated over the
EMITTED constraint list. No Rust hand-writes it; Rust only calls the decision. No new hash arithmetic
is authored either: the Poseidon primitive is `MinaStateQuery.poseidonPair`'s sponge
(`PastaPoseidon.Ref.hash`, o1js-`Poseidon.hash`-exact and KAT-pinned there), and this file only
CHAINS it.

## The fifth chain

`LightClientEthFinFold` / `LightClientEthExecFold` (SHA-256 branch), `LightClientTmHashFold` +
`LightClientSolHashFold` (SHA-256 collection chain) and `LightClientMidHashFold` (BLAKE2b absorb)
fold out the hash carriers of four chains. Mina was the missing fifth. Its rules are
`Dregg2.Bridge.LightClientMina`; this file is its fold, at POSEIDON over Pasta `Fp` — the hash Mina
actually uses, and the one whose defect is *different* from SHA-256's and BLAKE2b's.

## The carriers being folded out (the POSEIDON carriers — NOT the PICKLES carrier)

`LightClientMina.minaVerify` carries three witnessed projections. Two are Poseidon-side:

  * `LINK_OK` = `linkOk L ts u` — the exhibited segment is PARENT-LINKED and height-contiguous from
    the pinned weak-subjectivity anchor: block `i+1`'s `previousStateHash` IS block `i`'s computed
    state hash. In the carrier posture a verifier TRUSTS a bit for this and re-runs no Poseidon.
  * `CANON_OK` = `canonOk L u` — every state-row field element is canonical (`< p`).

This file replaces both. `LINK_OK` becomes the Poseidon CHAIN `stateChain`, whose TERMINAL VALUE IS
THE TIP STATE HASH — so a satisfying witness must EXHIBIT the block headers whose Poseidon chain from
the anchor lands on the tip the settlement is claimed under. `CANON_OK` becomes `minaRowWidthGates`,
the emitted 254-bit width check.

The third carrier — `PICKLES_OK`, the per-block Kimchi/Pickles Wrap-proof result — STAYS a carrier
(the IPA/FRI arc, shared with the whole Mina lane; NOT this file). ⚑ But it is not left dangling
either: §6 DISCHARGES it on a REAL Mina devnet block, from `MinaRealBlockGate.real_block_accepts`.

## Why the canonicality gate is not optional here (the Poseidon-specific defect)

SHA-256 and BLAKE2b read a message WORD modulo `2^64`, which is why the Solana stake and the Midnight
weight needed 64-bit width gates. Poseidon is worse in a different direction: `Ref.absorbAt` enters
every input through `(state + x) % p`, so the sponge cannot distinguish `x` from `x + p` AT ALL — a
one-line structural collision, not a birthday event (`MinaStateQuery.poseidonPair_shift_collides`,
which is why that file's `PoseidonPairCR` was deleted as FALSE). Applied to a light client this is an
ANCHOR SUBSTITUTION: a segment presented under anchor `A + p` chains to exactly the same tip state
hash as one under `A` (`stateChain_anchor_shift_collides`, §4 — proved structurally, no permutation
evaluated). The 254-bit window closes it, and the closure is exact rather than approximate:
`p > 2^254` (`pow254_lt_pN`), so `< 2^254` ⟹ canonical, and the whole `+k·p` alias family collapses
to a point in range (`mina_alias_collapses_in_range`).

⚑ **CORRECTED 2026-08-03 — the WINDOW is right; `minaRowWidthGates` is NOT the gate that enforces it
at the deployed field, and no descriptor carries it.** `minaRowWidthGates_forces` is stated over
`Assignment = Nat → ℤ`, i.e. over the INTEGERS. The deployed denotation is mod `P = 2013265921`
(BabyBear), and its recomposition gate `v − Σ_{i<254} 2^i·bᵢ = 0` read mod `P` is satisfiable for
EVERY field element — 254 free bits reach every residue — so as an emitted constraint it refuses
nothing. Worse, it addresses a 255-bit Pasta element as ONE column, and a BabyBear column holds
30.9 bits; there is no such column. `minaRowWidthGates` is a free-floating `List VmConstraint2` that
appears in no `EffectVmDescriptor2`, and it could not be added to one as written.

**The enforcement that DID land** is `Circuit/Emit/LightClientMinaAir.lean` §1a, at the
representation BabyBear actually has — the NINE LANES: eight `.limbs` lookups at 29 bits plus ONE at
**22** on the top lane, `2^232 · 2^22 = 2^254` exactly, both widths wrap-free
(`RangeFieldContainment.wrap_free_iff_le_29`). Eighteen lookups, no gate, no aux column, and the
`+p`-shifted REAL devnet genesis anchor is exhibited as refused
(`LightClientMinaAir.shifted_anchor_old_admits_new_rejects`) — a row the pre-rung predicate accepted
with `CANON_OK` witnessed `1`. ⚠ SCOPE: that gate covers the descriptor's two published `Fp`
elements (the anchor and the tip), not the per-block rows this file's `canonOk` quantifies over;
those are not columns of a single-row descriptor.

## The ties proved here (mirroring the four chains' fold theorems)

  * `foldStateHash_eq_poseidonRow` — the bridge leaf's abstract `stateHash` IS the generator's
    Poseidon row hash (the `*_eq_chainCommit` / `reconstruct_*_eq_foldReconstruct` analog).
  * `stateChain_eq_tip` — the chain's terminal value IS the tip state hash the light client tracks
    (the object `LINK_OK` stood for, via the Poseidon arithmetic, not a bit).
  * `stateChain_binding_of_noColl` — at the PER-INSTANCE non-equivocation side condition
    (`NoChainColl`, the shape `MinaStateQuery` repaired to on 2026-07-27), two segments chaining from
    their anchors to the SAME tip state hash have the SAME anchor and ARE the same segment. This is
    the NON-EQUIVOCATION content: a forger cannot open one tip to two histories.
  * `minaRowWidthGates` / `minaRowWidthGates_forces` — the emitted canonicality AIR and its bite.
  * `canonOk_from_gate` (`verify*_from_fold` analog) — the `CANON_OK` boolean is DISCHARGED by the
    emitted gate: no carrier column is read.
  * `mina_link_from_fold_gate_accepts` — carrier-free on the Poseidon side: the fold-derived linkage
    and canonicality DISCHARGE `minaVerify`, with only `PICKLES_OK` left as a carrier.
  * `mina_segment_binding_on` — the payoff, at the honest floor.

## The floor's THREE legs (SATISFIABLE / REFUTABLE / NOT PROVABLE), because two is not a floor

  * SATISFIABLE — `noChainColl_self` (the honest prover's own segment against itself), with NO
    hypothesis and no hash evaluated.
  * STRENGTH-PRESERVING — `noChainColl_of_no_collision` recovers the per-instance condition from the
    old global-injectivity hypothesis in one step, so nothing the deleted floor would have bought is
    lost.
  * LOAD-BEARING and REACHABLE — `stateChain_binding_unconditional_false` refutes the conclusion
    without the condition, and `rowColl_reachable` shows its negation is reachable AT THE DEPLOYED
    HASH. Both come from the `+p` shift, structurally.

## DERIVED vs TRUSTED, per step (say it at the current resolution)

  * DERIVED here: the Poseidon chain reconstruction and its `rfl`-tie to `stateHash`; the segment
    binding, reduced to the per-instance step condition; the canonicality carrier, from an EMITTED
    gate with a forcing lemma; the discharge of `minaVerify`'s two Poseidon conjuncts.
  * TRUSTED (named, load-bearing): (1) RESIDUAL #1, the composition wall — `stateChain anchor rows =
    tip` is, in a deployed circuit, the CONCLUSION of chained Poseidon gates forcing their sponge
    outputs; the per-node Poseidon forcing (`PastaPoseidon` §7 residual #3) is NOT discharged here or
    anywhere, so the fold is an explicit hypothesis and DERIVED-vs-ASSUMED stays visible.
    (2) RESIDUAL #2, the state-hash preimage shape — real Mina hashes the protocol state under
    domain prefixes (`Hash_prefix`), over a much wider field list than the four-field row here; the
    row captures the LINKAGE structure, not the byte-exact protocol-state serialization.
    (3) RESIDUAL #3, `PICKLES_OK` — the Kimchi/IPA arc, a carrier, inheriting the undischarged
    FRI/IPA floor even where §6 discharges it on a real block.
    (4) RESIDUAL #4, FORK CHOICE — this file binds an ANCHORED SEGMENT; it does not follow a chain.
    ⚑ NARROWED 2026-07-29: the rule is no longer absent — `Dregg2.Bridge.MinaChainSelection`
    implements Samasika `select` against `proof_of_stake.ml` and differentials it against openmina
    on 57 real-state vectors. The residual is now exactly the WIRING (nothing calls it) plus the
    fact that `select` is a TOURNAMENT with proved 3-cycles, so "the canonical chain" is not a
    function of a candidate SET.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`/`admit`/`native_decide`. The
Poseidon primitive is anchored in `MinaStateQuery` §9 against the pinned `mina-poseidon` crate and
the o1js probe gold; this file adds no hash arithmetic and its KATs are structural + discrimination
(`#guard`, interpreter). The two REAL devnet state hashes pinned in §5 are Base58Check decodes with
verified checksums — the decode procedure is spelled out so `bridge/src/mina_observer.rs` can and
does reproduce them.
-/
import Dregg2.Circuit.Emit.MinaStateQuery
import Dregg2.Circuit.Emit.StakeWidthRange
import Dregg2.Circuit.Emit.MinaRealBlockGate
import Dregg2.Bridge.LightClientMina

namespace Dregg2.Circuit.Emit.LightClientMinaHashFold

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.StakeWidthRange
open Dregg2.Circuit.Emit.MinaStateQuery (poseidonPair hash_cons_add_pN)
open Dregg2.Circuit.Emit.PastaPoseidon
open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Bridge.LightClientMina

set_option autoImplicit false
set_option maxRecDepth 8192

/-! ## §0 — The POSEIDON state-hash chain generator (the `chainCommit` analog, at Poseidon).

A Mina block's protocol-state hash commits its parent's state hash together with the block's own
fields, so the "collection chain" of a Mina light client is the BLOCK CHAIN ITSELF: fold the block
rows through the state hash from the anchor, and the terminal value is the TIP STATE HASH. Built
ONLY from `PastaPoseidon.Ref.hash` — no new hash arithmetic. -/

/-- A block ROW as the state hash sees it, minus the parent (which is the fold accumulator):
`(blockchainLength, stagedLedgerHash, publicInputDigest)`. -/
abbrev MinaRow : Type := Nat × Nat × Nat

/-- **The protocol-state hash**, as a fold step: `Poseidon(parent, height, ledgerHash, piDigest)`.
The 4-element input is `Ref.hash`, the same o1js-exact sponge `poseidonPair` is the 2-element case
of. (RESIDUAL #2: real Mina packs a much wider protocol state under `Hash_prefix` domain tags; this
is the linkage structure, not the byte-exact preimage.) -/
def poseidonRow (parent : Nat) (r : MinaRow) : Nat := Ref.hash [parent, r.1, r.2.1, r.2.2]

/-- The row hash IS the sponge on the 4-limb input (definitional). -/
theorem poseidonRow_eq_hash (parent : Nat) (r : MinaRow) :
    poseidonRow parent r = Ref.hash [parent, r.1, r.2.1, r.2.2] := rfl

/-- **THE POSEIDON STATE-HASH CHAIN.** Fold the exhibited block rows through the state hash from the
anchor; the terminal value is the TIP STATE HASH. This is what `LINK_OK` stood for. -/
def stateChain (acc : Nat) (rows : List MinaRow) : Nat := rows.foldl poseidonRow acc

/-- The empty segment chains to the anchor itself.

(Proved by `simp` on `List.foldl`, NOT by `rfl`: a `rfl` here asks the kernel to whnf through
`poseidonRow`, i.e. through the whole Poseidon round-constant table, and it blows the recursion
limit. The `simp` form never unfolds the hash — which is also the honest reading, since these are
laws of the FOLD, not of Poseidon.) -/
theorem stateChain_nil (a : Nat) : stateChain a [] = a := by simp [stateChain]

/-- One step (the chain's step law). -/
theorem stateChain_cons (a : Nat) (r : MinaRow) (rest : List MinaRow) :
    stateChain a (r :: rest) = stateChain (poseidonRow a r) rest := by simp [stateChain]

/-- Appending one block is one more state-hash step. -/
theorem stateChain_append (a : Nat) (l : List MinaRow) (x : MinaRow) :
    stateChain a (l ++ [x]) = poseidonRow (stateChain a l) x := by
  induction l generalizing a with
  | nil => rw [List.nil_append, stateChain_cons, stateChain_nil, stateChain_nil]
  | cons r rest ih => rw [List.cons_append, stateChain_cons, stateChain_cons, ih]

/-! ## §1 — The per-instance NON-EQUIVOCATION floor (the shape `MinaStateQuery` repaired to).

⚑ NOT a global-injectivity `Prop`. `Ref.absorbAt` reduces every input mod `pN`, so injectivity of the
concrete Poseidon is FALSE by a one-line shift — `MinaStateQuery` deleted exactly that floor on
2026-07-27 after every payoff under it turned out to be `False → anything`. This file adopts the
repaired shape from the start: a side condition at exactly the steps the induction consumes. -/

/-- **A genuine EQUIVOCATION of the state-hash step** — two DISTINCT `(parent, row)` inputs with the
SAME state hash. Carries its own distinctness, so `¬ RowColl` is never satisfied vacuously. -/
def RowColl (a : Nat) (r₁ : MinaRow) (b : Nat) (r₂ : MinaRow) : Prop :=
  ¬ (a = b ∧ r₁ = r₂) ∧ poseidonRow a r₁ = poseidonRow b r₂

/-- **`NoChainColl`** — the per-instance side condition: at EVERY level of the two chains, walked in
lockstep from their anchors, the state-hash step inputs are not an equivocation. The length equality
is carried by the definition itself (the mismatched shapes are `False`). -/
def NoChainColl : Nat → List MinaRow → Nat → List MinaRow → Prop
  | _, [], _, [] => True
  | a, r₁ :: t₁, b, r₂ :: t₂ =>
      ¬ RowColl a r₁ b r₂ ∧ NoChainColl (poseidonRow a r₁) t₁ (poseidonRow b r₂) t₂
  | _, _, _, _ => False

/-- **THE SEGMENT COMMIT BINDS, at the per-instance floor.** Two segments whose Poseidon state-hash
chains reach the SAME tip state hash have the SAME anchor and ARE the same segment — provided the two
histories do not equivocate the state hash at any level. This is the NON-EQUIVOCATION content
`LINK_OK` stood for: an attacker cannot open one tip state hash to two different block histories
without exhibiting a Poseidon collision at a specific height, which the side condition denies at that
height and nowhere else. -/
theorem stateChain_binding_of_noColl :
    ∀ (l₁ l₂ : List MinaRow) (a b : Nat), NoChainColl a l₁ b l₂ →
      stateChain a l₁ = stateChain b l₂ → a = b ∧ l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ a b hno h
    cases l₂ with
    | nil => exact ⟨h, rfl⟩
    | cons _ _ => exact absurd hno (by simp [NoChainColl])
  | cons r₁ t₁ ih =>
    intro l₂ a b hno h
    cases l₂ with
    | nil => exact absurd hno (by simp [NoChainColl])
    | cons r₂ t₂ =>
      rw [NoChainColl] at hno
      obtain ⟨hhead, htail⟩ := hno
      rw [stateChain_cons, stateChain_cons] at h
      obtain ⟨hstep, hrest⟩ := ih t₂ (poseidonRow a r₁) (poseidonRow b r₂) htail h
      obtain ⟨ha, hr⟩ := not_not.mp (fun hne => hhead ⟨hne, hstep⟩)
      exact ⟨ha, by rw [hr, hrest]⟩

/-- **LEG 1 — SATISFIABLE, with NO hypothesis and no hash evaluated.** The honest prover's own
segment satisfies the side condition against itself, so `stateChain_binding_of_noColl` is an
implication with a NON-empty antecedent. -/
theorem noChainColl_self : ∀ (l : List MinaRow) (a : Nat), NoChainColl a l a l := by
  intro l
  induction l with
  | nil => intro _; trivial
  | cons r rest ih =>
    intro a
    exact ⟨fun hc => hc.1 ⟨rfl, rfl⟩, ih (poseidonRow a r)⟩

/-- **LEG 2 — STRENGTH-PRESERVING.** A hash with no collisions at all gives the per-instance
condition between ARBITRARY equal-length segments, so whatever the deleted global floor would have
bought, the side condition buys in one application. (And it shows the condition is satisfiable
between segments that genuinely DIFFER, not only in the self case where the conclusion is free.) -/
theorem noChainColl_of_no_collision
    (hno : ∀ a r₁ b r₂, poseidonRow a r₁ = poseidonRow b r₂ → a = b ∧ r₁ = r₂) :
    ∀ (l₁ l₂ : List MinaRow) (a b : Nat), l₁.length = l₂.length → NoChainColl a l₁ b l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ a b hlen
    cases l₂ with
    | nil => trivial
    | cons _ _ => simp at hlen
  | cons r₁ t₁ ih =>
    intro l₂ a b hlen
    cases l₂ with
    | nil => simp at hlen
    | cons r₂ t₂ =>
      refine ⟨?_, ih t₂ _ _ (by simpa using hlen)⟩
      rintro ⟨hne, heq⟩
      exact hne (hno _ _ _ _ heq)

/-! ## §2 — LEG 3: LOAD-BEARING and REACHABLE. The `+p` shift, proved by ARITHMETIC ON THE ABSORB
STATE — no permutation is evaluated, no `decide` runs 55 rounds. The collision is STRUCTURAL. -/

/-- **THE ANCHOR IS NOT PINNED BY THE TIP** (without the width gate). A segment presented under
anchor `A + p` chains to EXACTLY the same tip state hash as one under `A`, because the sponge enters
its first input through `(state + x) % p`. For a light client this is an ANCHOR SUBSTITUTION: the
governance-pinned weak-subjectivity anchor does not, by itself, pin the history. -/
theorem stateChain_anchor_shift_collides (a : Nat) (r : MinaRow) (rest : List MinaRow) :
    stateChain (a + pN) (r :: rest) = stateChain a (r :: rest) := by
  rw [stateChain_cons, stateChain_cons]
  have : poseidonRow (a + pN) r = poseidonRow a r := hash_cons_add_pN a [r.1, r.2.1, r.2.2]
  rw [this]

/-- **REACHABLE AT THE DEPLOYED HASH** — the side condition's negation is not hypothetical: the
`+p` shift IS an equivocation of the state-hash step, so `¬ RowColl` is a real ask rather than a
decoration. -/
theorem rowColl_reachable (a : Nat) (r : MinaRow) : RowColl (a + pN) r a r := by
  refine ⟨?_, hash_cons_add_pN a [r.1, r.2.1, r.2.2]⟩
  rintro ⟨h, -⟩
  have hp : pN ≠ 0 := by decide
  omega

/-- **THE CONCLUSION IS FALSE WITHOUT THE SIDE CONDITION** — so `NoChainColl` is load-bearing, not
decoration. Two one-block segments with DIFFERENT anchors reach the same tip. -/
theorem stateChain_binding_unconditional_false :
    ¬ (∀ (l₁ l₂ : List MinaRow) (a b : Nat), stateChain a l₁ = stateChain b l₂ → a = b ∧ l₁ = l₂) := by
  intro h
  have hp : pN ≠ 0 := by decide
  have := (h [(1, 2, 3)] [(1, 2, 3)] (0 + pN) 0
    (stateChain_anchor_shift_collides 0 (1, 2, 3) [])).1
  omega

/-! ## §3 — THE CANONICALITY WIDTH GATE: Lean-authored AIR that closes the `+p` family.

`pN > 2^254` (`pow254_lt_pN`), so a 254-bit width gate forces CANONICALITY exactly: a field element
the gate admits is `< 2^254 < p`, and the whole `+k·p` alias family collapses to a point. -/

/-- The Pasta `Fp` canonical width: 254 bits (`p` is a 255-bit prime just above `2^254`). -/
def MINA_FIELD_BITS : Nat := 254

/-- **`p` EXCEEDS `2^254`** — the arithmetic fact the width gate's exactness rests on. -/
theorem pow254_lt_pN : 2 ^ MINA_FIELD_BITS < pN := by decide

/-- **A state row is IN RANGE** when every field element fits the canonical width. `parent` is the
running chain value and is gated alongside the three row fields, because it is exactly the input the
`+p` shift attacks. -/
def MinaRowInRange (parent : Nat) (r : MinaRow) : Prop :=
  parent < 2 ^ MINA_FIELD_BITS ∧ r.1 < 2 ^ MINA_FIELD_BITS ∧ r.2.1 < 2 ^ MINA_FIELD_BITS
    ∧ r.2.2 < 2 ^ MINA_FIELD_BITS

instance : ∀ (p : Nat) (r : MinaRow), Decidable (MinaRowInRange p r) := fun p r => by
  unfold MinaRowInRange; infer_instance

/-- **AN IN-RANGE FIELD ELEMENT IS CANONICAL.** The width gate's whole point: `< 2^254` ⟹ `< p`. -/
theorem canonical_of_inRange {v : Nat} (h : v < 2 ^ MINA_FIELD_BITS) : v < pN :=
  lt_trans h pow254_lt_pN

/-- **THE STATE-ROW CANONICALITY GATES — LEAN-AUTHORED AIR.** One `StakeWidthRange.widthGate` per
field element of the state-hash preimage: `4 × 254 = 1016` boolean pins plus four recomposition
gates. `bit0` is the row's first fresh bit column; the four bit windows are disjoint by construction.

This is generated here, in Lean, from `AirBuilder.rangeNonneg` — no Rust hand-writes it. -/
def minaRowWidthGates (parCol hCol lCol piCol bit0 : Nat) : List VmConstraint2 :=
  widthGate parCol bit0 MINA_FIELD_BITS
  ++ widthGate hCol (bit0 + MINA_FIELD_BITS) MINA_FIELD_BITS
  ++ widthGate lCol (bit0 + 2 * MINA_FIELD_BITS) MINA_FIELD_BITS
  ++ widthGate piCol (bit0 + 3 * MINA_FIELD_BITS) MINA_FIELD_BITS

/-- The emitted budget: `4 × (254 + 1) = 1020` constraints per state row. -/
theorem minaRowWidthGates_length (parCol hCol lCol piCol bit0 : Nat) :
    (minaRowWidthGates parCol hCol lCol piCol bit0).length = 1020 := by
  simp [minaRowWidthGates, widthGate, rangeNonneg, bitsFrom, MINA_FIELD_BITS]

/-- **THE ROW GATES FORCE CANONICALITY.** A satisfying assignment whose four value columns carry the
state row's field elements puts the row IN RANGE, hence (by `canonical_of_inRange`) canonical. This
is the bridge from the emitted AIR to the model-side predicate the theorems quantify over. -/
theorem minaRowWidthGates_forces (a : Assignment) (parent : Nat) (r : MinaRow)
    (parCol hCol lCol piCol bit0 : Nat)
    (hpar : a parCol = (parent : ℤ)) (hh : a hCol = (r.1 : ℤ))
    (hl : a lCol = (r.2.1 : ℤ)) (hpi : a piCol = (r.2.2 : ℤ))
    (hbPar : ∀ c ∈ bitsFrom bit0 MINA_FIELD_BITS, (gBin c).eval a = 0)
    (hrPar : evalH (recompHead (Head.lin 1 parCol) (bitsFrom bit0 MINA_FIELD_BITS)) a = 0)
    (hbH : ∀ c ∈ bitsFrom (bit0 + MINA_FIELD_BITS) MINA_FIELD_BITS, (gBin c).eval a = 0)
    (hrH : evalH (recompHead (Head.lin 1 hCol)
             (bitsFrom (bit0 + MINA_FIELD_BITS) MINA_FIELD_BITS)) a = 0)
    (hbL : ∀ c ∈ bitsFrom (bit0 + 2 * MINA_FIELD_BITS) MINA_FIELD_BITS, (gBin c).eval a = 0)
    (hrL : evalH (recompHead (Head.lin 1 lCol)
             (bitsFrom (bit0 + 2 * MINA_FIELD_BITS) MINA_FIELD_BITS)) a = 0)
    (hbPi : ∀ c ∈ bitsFrom (bit0 + 3 * MINA_FIELD_BITS) MINA_FIELD_BITS, (gBin c).eval a = 0)
    (hrPi : evalH (recompHead (Head.lin 1 piCol)
              (bitsFrom (bit0 + 3 * MINA_FIELD_BITS) MINA_FIELD_BITS)) a = 0) :
    MinaRowInRange parent r :=
  ⟨widthGate_forces a parent parCol bit0 MINA_FIELD_BITS hpar hbPar hrPar,
   widthGate_forces a r.1 hCol (bit0 + MINA_FIELD_BITS) MINA_FIELD_BITS hh hbH hrH,
   widthGate_forces a r.2.1 lCol (bit0 + 2 * MINA_FIELD_BITS) MINA_FIELD_BITS hl hbL hrL,
   widthGate_forces a r.2.2 piCol (bit0 + 3 * MINA_FIELD_BITS) MINA_FIELD_BITS hpi hbPi hrPi⟩

/-- **THE `+k·p` ALIAS FAMILY COLLAPSES IN RANGE.** A field element shifted by `k·p` — the exact
family Poseidon's `absorbAt` generates — is in range only when `k = 0`. Because `p > 2^254`, one
period already leaves the window; this is stronger than the `2^w` case, where the modulus IS the
window. -/
theorem mina_alias_collapses_in_range (v k : Nat) (h : v + k * pN < 2 ^ MINA_FIELD_BITS) : k = 0 := by
  by_contra hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
  have : pN ≤ k * pN := Nat.le_mul_of_pos_left pN hk1
  have := pow254_lt_pN
  omega

/-- ⚑ **THE ANCHOR-SUBSTITUTION WITNESS IS UNWITNESSABLE UNDER THE EMITTED GATE.** Not "no shifted
anchor is known" — there is NO satisfying assignment for `minaRowWidthGates` whose parent column
carries a `+k·p`-shifted value for `k ≠ 0`. The forcing lemma is the whole content; this is it
applied to the exact attack on the record (`stateChain_anchor_shift_collides`). -/
theorem mina_anchor_shift_unwitnessable (a : Assignment) (v k : Nat) (parCol bit0 : Nat)
    (hk : k ≠ 0)
    (hpar : a parCol = ((v + k * pN : Nat) : ℤ))
    (hbPar : ∀ c ∈ bitsFrom bit0 MINA_FIELD_BITS, (gBin c).eval a = 0)
    (hrPar : evalH (recompHead (Head.lin 1 parCol) (bitsFrom bit0 MINA_FIELD_BITS)) a = 0) :
    False :=
  hk (mina_alias_collapses_in_range v k
    (widthGate_forces a (v + k * pN) parCol bit0 MINA_FIELD_BITS hpar hbPar hrPar))

/-- **A SEGMENT is in range** when every step's `(parent, row)` pair is. `SegInRange` walks the chain
so the running parent is gated at every level — which is what the anchor-substitution attack needs. -/
def SegInRange : Nat → List MinaRow → Prop
  | _, [] => True
  | a, r :: rest => MinaRowInRange a r ∧ SegInRange (poseidonRow a r) rest

/-- Every field element of an in-range segment is CANONICAL. -/
theorem segInRange_anchor_canonical (a : Nat) (r : MinaRow) (rest : List MinaRow)
    (h : SegInRange a (r :: rest)) : a < pN :=
  canonical_of_inRange h.1.1

/-! ## §4 — The bridge tie: instantiating `MinaLeaf`'s Poseidon side at the real hash.

The PROOF side stays abstract — the Pickles/Kimchi carrier is not this file's business, exactly as
`ED_OK` is not the Solana fold's. `PicklesSlot` is that abstraction, so the instance below is a
faithful `MinaLeaf` with only its HASH side pinned. -/

/-- The Pickles carrier, as a slot the fold leaves open (the `ED_OK`-stays-a-hypothesis shape). -/
structure PicklesSlot where
  /-- The Wrap proof type. -/
  Proof : Type
  /-- The Kimchi/Pickles verify RESULT at a state hash. -/
  verify : Nat → Proof → Bool
  /-- The denotation: that protocol state was genuinely proved. -/
  Proved : Nat → Prop
  /-- The named leaf: a verifying proof entails the state was proved (inherits the IPA/FRI floor). -/
  sound : ∀ d π, verify d π = true → Proved d

/-- **`minaFoldLeaf`** — a lawful `MinaLeaf` whose `stateHash` IS the real Poseidon row hash and whose
`rowCanonical` IS the 254-bit width predicate the emitted gate forces.

⚑ `stateHashCR` is `False`, and that is the honest slot: `MinaLeaf.noStateCollision` demands the
carrier ENTAIL global injectivity of `stateHash`, and at the concrete Poseidon that is REFUTED
(`rowColl_reachable` — `absorbAt` reduces mod `p`). Every theorem that took `hcr : stateHashCR` would
prove nothing here; the binding content rides `stateChain_binding_of_noColl` on the per-instance
floor instead. This is the same repair `LightClientTmHashFold` / `LightClientSolHashFold` /
`LightClientMidHashFold` made on 2026-07-27, adopted here from the start. -/
@[reducible] def minaFoldLeaf (PK : PicklesSlot) : MinaLeaf where
  Digest := Nat
  deqD := inferInstance
  Proof := PK.Proof
  stateHash := fun r => poseidonRow r.1 (r.2.1, r.2.2.1, r.2.2.2)
  picklesVerify := PK.verify
  Proved := PK.Proved
  picklesSound := PK.sound
  rowCanonical := fun r =>
    decide (r.1 < 2 ^ MINA_FIELD_BITS) && decide (r.2.1 < 2 ^ MINA_FIELD_BITS)
      && decide (r.2.2.1 < 2 ^ MINA_FIELD_BITS) && decide (r.2.2.2 < 2 ^ MINA_FIELD_BITS)
  stateHashCR := False
  noStateCollision := fun h => h.elim
  zeroDigest := 0

/-- **THE TIE (`*_eq_chainCommit` analog).** The bridge leaf's abstract `stateHash` IS the
generator's Poseidon row hash — the object `LINK_OK` stood for, via the Poseidon arithmetic, not a
bit. -/
theorem foldStateHash_eq_poseidonRow (PK : PicklesSlot) (p h l pi : Nat) :
    (minaFoldLeaf PK).stateHash (p, h, l, pi) = poseidonRow p (h, l, pi) := rfl

/-- **THE TIP STATE HASH IS THE CHAIN'S TERMINAL VALUE.** Folding a header list through the bridge's
`blockHash` from the anchor IS `stateChain` over the corresponding rows. So the light client's
tracked tip is the fold's output, not a separate claim. -/
theorem stateChain_eq_tip (PK : PicklesSlot) :
    ∀ (bs : List (MinaHeader (minaFoldLeaf PK))) (a : Nat),
      (∀ b ∈ bs, True) →
      stateChain a (bs.map (fun b => (b.height, b.ledgerHash, b.piDigest)))
        = bs.foldl (fun acc b => poseidonRow acc (b.height, b.ledgerHash, b.piDigest)) a := by
  intro bs
  induction bs with
  | nil => intro _ _; rfl
  | cons b rest ih =>
    intro a _
    simpa [stateChain_cons] using ih (poseidonRow a (b.height, b.ledgerHash, b.piDigest))
      (fun _ _ => trivial)

/-- **THE `CANON_OK` CARRIER, DISCHARGED BY THE EMITTED GATE (`verify*_from_fold` analog) — no
carrier bit read.** A satisfying assignment for `minaRowWidthGates` on every block's state row makes
the bridge's `canonOk` Boolean `true`. There is no witnessed carrier to set. -/
theorem canonOk_from_gate (PK : PicklesSlot) (u : MinaUpdate (minaFoldLeaf PK))
    (hgate : ∀ b ∈ u.blocks, MinaRowInRange b.parent (b.height, b.ledgerHash, b.piDigest)) :
    canonOk (minaFoldLeaf PK) u = true := by
  unfold canonOk
  simp only [List.all_eq_true]
  intro b hb
  obtain ⟨h1, h2, h3, h4⟩ := hgate b hb
  simp only [minaFoldLeaf, stateRow, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨decide_eq_true h1, decide_eq_true h2⟩, decide_eq_true h3⟩, decide_eq_true h4⟩

/-- **THE PAYOFF, POSEIDON-CARRIER-FREE: the fold-derived linkage and the emitted canonicality gate
DISCHARGE THE WHOLE MINA GATE.** Given the depth arithmetic and the Pickles carrier, if the exhibited
segment is genuinely parent-linked (`hlink` — DERIVED from the exhibited headers, RESIDUAL #1) and
every state row satisfies the width gate (`hgate` — DERIVED from the EMITTED constraints), then
`minaVerify` accepts. No `LINK_OK` or `CANON_OK` bit is read and NO hash floor is used. -/
theorem mina_link_from_fold_gate_accepts (PK : PicklesSlot)
    (ts : MinaTrustedState (minaFoldLeaf PK)) (u : MinaUpdate (minaFoldLeaf PK))
    (hne : 0 < u.blocks.length)
    (hanch : ts.anchorHeight ≤ u.submittedHeight)
    (hdep : ts.confirmationDepth ≤ witnessedDepth ts u)
    (hlink : linkOk (minaFoldLeaf PK) ts u = true)
    (hpick : picklesOk (minaFoldLeaf PK) u = true)
    (hgate : ∀ b ∈ u.blocks, MinaRowInRange b.parent (b.height, b.ledgerHash, b.piDigest)) :
    minaVerify (minaFoldLeaf PK) ts u = true := by
  unfold minaVerify minaVerifyDecision
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨hne, hanch⟩, hdep⟩, hlink⟩, hpick⟩, canonOk_from_gate PK u hgate⟩

/-- **THE SEGMENT IS BOUND, at the per-instance floor.** Two segments that both chain from their
anchors to the SAME tip state hash have the same anchor and ARE the same segment — the content
`LINK_OK` stood for, and the fork-DETECTION property (a node cannot exhibit two histories under one
tip). ⚑ NOT fork CHOICE: nothing here says which of two DIFFERENT tips the network selects. -/
theorem mina_segment_binding_on (l₁ l₂ : List MinaRow) (a b tip : Nat)
    (hno : NoChainColl a l₁ b l₂)
    (h₁ : stateChain a l₁ = tip) (h₂ : stateChain b l₂ = tip) : a = b ∧ l₁ = l₂ :=
  stateChain_binding_of_noColl l₁ l₂ a b hno (h₁.trans h₂.symm)

/-! ## §5 — REALITY: the two REAL Mina devnet state hashes, as canonical `Fp` elements.

Both are Base58Check decodes of the strings `MinaRealBlockGate` names, performed as Mina does it:
strip the 4-byte double-SHA-256 checksum (VERIFIED), strip the `0x10` state-hash version byte, strip
the `0x01` bin_prot version byte, read the remaining 32 bytes LITTLE-ENDIAN as an `Fp` element. The
same decode is performed in `bridge/src/mina_observer.rs::decode_state_hash`, whose test pins these
exact decimals — so the Rust decoder and this file are cross-checked against each other on real
chain data. -/

/-- Devnet block **539508**'s state hash `3NLmVB6Fs3dm4kXNkgwheHXzJXNpCCwEDe76RpTVeBTNujm12zNk`,
as an `Fp` element. This is the block whose Wrap proof o1-labs' own `kimchi::verifier::verify`
accepts (`MinaRealBlockGate`). -/
def DEVNET_539508_STATE_HASH : Nat :=
  26183698926150821166089117776323498226609958862529648923082869093695686732004

/-- Devnet **genesis**'s state hash `3NL93SipJfAMNDBRfQ8Uo8LPovC74mnJZfZYB5SK7mTtkL72dsPx`, as an
`Fp` element (the natural weak-subjectivity anchor for a devnet light client). -/
def DEVNET_GENESIS_STATE_HASH : Nat :=
  9114416221768123787477325283664893678899335531281108607736543138013422200977

/-- Devnet block 539508's blockchain length. -/
def DEVNET_539508_HEIGHT : Nat := 539508

/-- **THE REAL STATE HASHES ARE CANONICAL, and the width gate ADMITS them.** Both decode into the
window `< 2^254`, so the canonicality gate is not merely sound but LIVE on real chain data — it does
not refuse the honest chain. -/
theorem devnet_state_hashes_in_range :
    DEVNET_539508_STATE_HASH < 2 ^ MINA_FIELD_BITS
    ∧ DEVNET_GENESIS_STATE_HASH < 2 ^ MINA_FIELD_BITS := by
  refine ⟨?_, ?_⟩ <;> decide

/-- And therefore canonical (`< p`) — through `canonical_of_inRange`, so the gate's exactness is
exercised on real data rather than asserted. -/
theorem devnet_state_hashes_canonical :
    DEVNET_539508_STATE_HASH < pN ∧ DEVNET_GENESIS_STATE_HASH < pN :=
  ⟨canonical_of_inRange devnet_state_hashes_in_range.1,
   canonical_of_inRange devnet_state_hashes_in_range.2⟩

/-- ⚑ **AND THE ANCHOR-SUBSTITUTION WITNESS AGAINST A REAL ANCHOR IS REFUSED.** The shifted devnet
genesis hash — which chains to the identical tip (`stateChain_anchor_shift_collides`) — is OUT of the
gate's window, while the genuine one is IN it. The attack exists on the real anchor and the emitted
gate refuses exactly it. -/
theorem devnet_anchor_shift_refused :
    DEVNET_GENESIS_STATE_HASH < 2 ^ MINA_FIELD_BITS
    ∧ ¬ (DEVNET_GENESIS_STATE_HASH + pN < 2 ^ MINA_FIELD_BITS) := by
  refine ⟨devnet_state_hashes_in_range.2, ?_⟩
  intro h
  exact absurd (mina_alias_collapses_in_range DEVNET_GENESIS_STATE_HASH 1 (by simpa using h))
    (by decide)

/-! ## §6 — THE PICKLES CARRIER, DISCHARGED ON A REAL MINA BLOCK.

`MinaStateQuery` §10 residual #6 says, correctly, that K5's Kimchi decision and the Poseidon fold
"share no object in Lean". That is still true of the STATE-QUERY seam. It is NO LONGER true of the
LIGHT-CLIENT seam: below, `minaVerifyDecision`'s `PICKLES_OK` projection is supplied by
`MinaRealBlockGate.real_block_accepts` — the composed decision over devnet block 539508, whose Wrap
proof openmina's `BlockVerifier` + o1-labs' `kimchi::verifier::verify` accept.

⚑ WHAT THIS IS AND IS NOT. It IS: the light-client decision accepting with its proof carrier
rendered by the real block's Kimchi arithmetic rather than by a hypothesis or a `true` literal. It is
NOT: a discharge of the IPA/FRI floor (that floor is untouched and is `picklesSound`'s content), NOT
a claim that the tracked segment is the one Samasika selects, and NOT the K6 state-query seam. -/

/-- **THE MINA LIGHT-CLIENT DECISION ACCEPTS, WITH ITS PICKLES CARRIER SUPPLIED BY A REAL DEVNET
BLOCK.** The Kimchi decision term below is verbatim `MinaRealBlockGate.real_block_accepts`'s subject.
Given the linkage/canonicality conjuncts (which §3–§4 derive from the fold and the emitted gate) and
the depth arithmetic, `minaVerifyDecision` accepts. -/
theorem mina_decision_accepts_real_block_pickles
    (segLen anchorH submittedH witDepth reqDepth : Nat)
    (hne : 0 < segLen) (hanch : anchorH ≤ submittedH) (hdep : reqDepth ≤ witDepth) :
    minaVerifyDecision segLen anchorH submittedH witDepth reqDepth true
      (Dregg2.Circuit.Emit.KimchiVerify.kimchiVerifyDecisionFieldRec
        MinaRealBlockGate.IDX_PREV MinaRealBlockGate.PREV MinaRealBlockGate.PUBLIC
        Dregg2.Circuit.Emit.KimchiVerify.COLUMNS
        (Dregg2.Circuit.Emit.KimchiVerify.PERMUTS - 1)
        Dregg2.Circuit.Emit.KimchiVerify.COLUMNS 7 1 MinaRealBlockGate.N
        MinaRealBlockGate.VV MinaRealBlockGate.UU MinaRealBlockGate.EVZ MinaRealBlockGate.EVZW
        MinaRealBlockGate.CIP MinaRealBlockGate.OMEGA MinaRealBlockGate.ZETA
        MinaRealBlockGate.ZETAW MinaRealBlockGate.BETA MinaRealBlockGate.GAMMA
        MinaRealBlockGate.A0 MinaRealBlockGate.A1 MinaRealBlockGate.A2 MinaRealBlockGate.CHALSS
        MinaRealBlockGate.WZ MinaRealBlockGate.SZ MinaRealBlockGate.SHIFT MinaRealBlockGate.ZZ
        MinaRealBlockGate.ZZW MinaRealBlockGate.PZ MinaRealBlockGate.LCT MinaRealBlockGate.DINV
        MinaRealBlockGate.FT0 true true true)
      true = true := by
  rw [MinaRealBlockGate.real_block_accepts]
  simp only [minaVerifyDecision, Bool.and_eq_true, decide_eq_true_eq, and_true]
  exact ⟨⟨hne, hanch⟩, hdep⟩

/-- **AND IT IS LOAD-BEARING.** The frozen pre-P6 Kimchi decision REFUSES this real block outright
(`MinaRealBlockGate.real_block_freeze_would_refuse`), and a refused Pickles carrier makes the
light-client decision reject regardless of every other conjunct. -/
theorem mina_decision_rejects_on_refused_pickles
    (segLen anchorH submittedH witDepth reqDepth : Nat) :
    minaVerifyDecision segLen anchorH submittedH witDepth reqDepth true
      (Dregg2.Circuit.Emit.KimchiVerify.kimchiVerifyDecisionRec 0 MinaRealBlockGate.PREV
        MinaRealBlockGate.PUBLIC Dregg2.Circuit.Emit.KimchiVerify.COLUMNS
        (Dregg2.Circuit.Emit.KimchiVerify.PERMUTS - 1)
        Dregg2.Circuit.Emit.KimchiVerify.COLUMNS 7 1 true true true)
      true = false := by
  rw [MinaRealBlockGate.real_block_freeze_would_refuse]
  simp [minaVerifyDecision]

/-! ## §7 — KATs (structural + discrimination, `#guard`, interpreter).

The Poseidon primitive itself is anchored in `MinaStateQuery` §9 against the pinned `mina-poseidon`
crate (rev `36a8b510`) and the o1js `MerkleTree` probe gold; this file authors no hash arithmetic, so
its KATs pin the CHAIN's structure and its DISCRIMINATION rather than re-anchoring a digest. -/

/-- A three-block demo segment (heights 11/12/13 above a genesis-like anchor). -/
def katSeg : List MinaRow := [(11, 100, 200), (12, 101, 201), (13, 102, 202)]

-- Structural: the chain's step law reduces (the anchor-seeded first step).
#guard stateChain 1 [(11, 100, 200)] == poseidonRow 1 (11, 100, 200)
-- Structural: appending is one more step.
#guard stateChain 1 (katSeg ++ [(14, 103, 203)]) == poseidonRow (stateChain 1 katSeg) (14, 103, 203)
-- Discrimination: a tampered ledger hash at height 12 FLIPS the tip state hash (the segment is
-- genuinely bound by its tip, not merely claimed to be).
#guard stateChain 1 [(11, 100, 200), (12, 999, 201), (13, 102, 202)] != stateChain 1 katSeg
-- Discrimination: a tampered HEIGHT flips the tip (the contiguity is committed, not only checked).
#guard stateChain 1 [(11, 100, 200), (99, 101, 201), (13, 102, 202)] != stateChain 1 katSeg
-- Discrimination: a DIFFERENT anchor gives a different tip — the honest, canonical case.
#guard stateChain 2 katSeg != stateChain 1 katSeg
-- ⚑ THE DEFECT, executable: the `+p`-shifted anchor gives the SAME tip. This is the attack the
-- width gate refuses (`devnet_anchor_shift_refused`); it is kept as the tooth.
#guard stateChain (1 + 28948022309329048855892746252171976963363056481941560715954676764349967630337)
  katSeg == stateChain 1 katSeg
-- The real devnet anchor is a live chain seed (the KAT runs on real chain data, not only toys).
#guard stateChain DEVNET_GENESIS_STATE_HASH katSeg != stateChain 1 katSeg
-- The gate's per-row budget.
#guard (minaRowWidthGates 0 1 2 3 4).length == 1020

/-! ## §8 — axiom hygiene. -/

#assert_axioms stateChain_nil
#assert_axioms stateChain_cons
#assert_axioms stateChain_append
#assert_axioms poseidonRow_eq_hash
#assert_axioms stateChain_binding_of_noColl
#assert_axioms noChainColl_self
#assert_axioms noChainColl_of_no_collision
#assert_axioms stateChain_anchor_shift_collides
#assert_axioms rowColl_reachable
#assert_axioms stateChain_binding_unconditional_false
#assert_axioms pow254_lt_pN
#assert_axioms canonical_of_inRange
#assert_axioms minaRowWidthGates_length
#assert_axioms minaRowWidthGates_forces
#assert_axioms mina_alias_collapses_in_range
#assert_axioms mina_anchor_shift_unwitnessable
#assert_axioms segInRange_anchor_canonical
#assert_axioms foldStateHash_eq_poseidonRow
#assert_axioms stateChain_eq_tip
#assert_axioms canonOk_from_gate
#assert_axioms mina_link_from_fold_gate_accepts
#assert_axioms mina_segment_binding_on
#assert_axioms devnet_state_hashes_in_range
#assert_axioms devnet_state_hashes_canonical
#assert_axioms devnet_anchor_shift_refused
#assert_axioms mina_decision_accepts_real_block_pickles
#assert_axioms mina_decision_rejects_on_refused_pickles

#print axioms mina_link_from_fold_gate_accepts
#print axioms stateChain_binding_of_noColl
#print axioms mina_decision_accepts_real_block_pickles

end Dregg2.Circuit.Emit.LightClientMinaHashFold
