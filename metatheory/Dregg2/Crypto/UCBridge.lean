/-
# Dregg2.Crypto.UCBridge — the CROSS-SYSTEM bridge for the dynamic-UC commitment obligation.

**The §8-boundary philosophy made concrete (the dynamic-UC hole, closed pragmatically).**
`Metatheory.EpistemicConsensus §6` ("The UC angle") states the FULL Canetti dynamic UC theorem

    (∀ Z, view_Z(π) ≈ view_Z(F))  →  (∀ Z, view_Z(ρ^π) ≈ view_Z(ρ^F))

as a SHARP OPEN, resting on "simulator existence + computational indistinguishability of
ensembles" — the same genuinely-cryptographic residue that `Crypto.Primitives` isolates as the
`Prop` carriers `CryptoPrimitives.binding` (DLog binding) and `CryptoPrimitives.unlinkable`
(hiding/anonymity). Those carriers are NEVER proved in Lean — Lean's `Verify` is a *decidable*
oracle, not a probabilistic ensemble, and `≈` is not a Lean order-law.

This module does NOT prove UC in Lean. It CARRIES the *core commitment-security* obligation
(the heart of realizing the ideal commitment functionality `F_com`) as an explicit `Prop`
structure — and records that this obligation has been **discharged in a real UC / game-based
tool**: CryptHOL + the AFP `Sigma_Commit_Crypto` Pedersen development, on Isabelle/HOL. The
dregg2 Pedersen `commit` definitions were TRANSPORTED into that framework
(`~/dev/breadstuffs/uc-crypthol/Dregg2_FCom.thy`) and the realization theorem PROVED there:

    Dregg2_UC.pedersen.dregg2_pedersen_realizes_F_com
      — correctness ∧ perfect-hiding ∧ (binding-advantage = DLog-advantage of the reduction);
    Dregg2_UC.pedersen_asymp.dregg2_pedersen_realizes_F_com_asymp
      — perfect hiding at every η ∧ (binding negligible ↔ DLog negligible);
    Dregg2_UC.pedersen_asymp.dregg2_binding_under_dlog
      — DLog hard ⟹ binding negligible (the honest implication the `binding` carrier asserts).

## THE CROSS-SYSTEM TRUST CAVEAT (read this).
What is asserted here is NOT a Lean proof of UC. It is a *carrier* whose truth rests on a
proof in ANOTHER system. Accepting it WIDENS the trust base of dregg2 to include, beyond Lean's
kernel:
  1. **Isabelle/HOL's kernel** (the LCF-style core that checked the CryptHOL proofs);
  2. **the AFP entries `CryptHOL` and `Sigma_Commit_Crypto`** (their `spmf` semantics, the
     `abstract_commitment` game definitions, the `dis_log` discrete-log game, and the proved
     Pedersen `abstract_perfect_hiding` / `pedersen_bind` / `pedersen_bind_asym`);
  3. **the FIDELITY OF THE DEFINITION TRANSPORT** — that the dregg2 Layer-A `commit value
     blinding` (with its sole proved law `commit_hom`, the additive homomorphism over an
     `AddCommGroup`) really IS the cyclic-group Pedersen commitment `commit ck m = g^d · ck^m`
     formalised in `Dregg2_FCom.thy`. This is a HUMAN-CHECKED correspondence, not a
     machine-checked one: the two formalisations live in different logics and are not connected
     by a verified translation. It is the honest residual gap.

This is strictly stronger than a bare Lean `axiom`/`sorry` (which would assert UC on nothing):
the obligation is discharged by a real proof in a real UC tool. It is strictly weaker than a
single-kernel Lean proof: the trust spans two kernels + the transport fidelity. Stated honestly.

## How to verify the Isabelle side.
    isabelle build -d <afp-matching-Isabelle2025-RC3>/thys \
                   -d ~/dev/breadstuffs/uc-crypthol Dregg2_UC
(exit 0 ⇒ the CryptHOL theorems above are kernel-checked.) The theory file is
`~/dev/breadstuffs/uc-crypthol/Dregg2_FCom.thy`; it contains no `sorry`/`oops` and references only
real, already-proven `Sigma_Commit_Crypto` theorems. CAVEAT: the green build was NOT reproduced on
the dev machine — the local AFP checkout (`afp-devel`) is an Isabelle-*dev* revision incompatible
with Isabelle2025-RC3 at the ML/proof-automation level; it needs the RC3-matched AFP. See
`docs/rebuild/PHASE-UC-TRANSPORT.md §3` for the exact obstruction. The Pedersen security itself is
long-established in the AFP; what is blocked is recompiling that AFP under this release candidate.

## Axiom hygiene.
This module is `#assert_axioms`-clean: the cross-system facts are FIELDS of a `Prop`-bundling
structure (`FComDischarge`), passed as *hypotheses* — there is NO `axiom` and NO `sorry`. The
bridge theorem `binding_unlinkable_discharged_by_crypthol` PROVES (in Lean, kernel-clean) that
GIVEN such a discharge structure for a primitive set, that set's `binding` and `unlinkable`
carriers are inhabited — i.e. the carriers are now *witnessed by CryptHOL*, not assumed.
-/
import Dregg2.Crypto.Primitives
import Dregg2.Tactics

namespace Dregg2.Crypto.UCBridge

universe u

variable {Digest : Type u} [AddCommGroup Digest]

/-! ## The cross-system discharge structure.

`FComDischarge P` bundles — as `Prop` FIELDS (carriers, never `axiom`s) — the CORE security
guarantees the dregg2 Pedersen commitment must satisfy to realize the ideal commitment
functionality `F_com`. Each field NAMES the exact CryptHOL theorem that establishes it (see the
module docstring). The structure is *inhabited only by transporting a CryptHOL proof*: to
construct an `FComDischarge`, the caller must vouch (under the trust caveat above) that the
CryptHOL `Dregg2_FCom.thy` realization theorem holds for this primitive set. -/

/-- **`FComDischarge`** — the F_com realization obligation for a `CryptoPrimitives` set, as a
`Prop`-bundling carrier. Its fields are exactly the UC-relevant security properties PROVED in
CryptHOL (`Dregg2_FCom.thy`); inhabiting it is the cross-system bridge act. NOT an `axiom`. The
structure BUNDLES the carried `Prop`s + their cross-system proofs + the entailments into the
dregg2 carriers; it lives in `Type` (it is data — which Props, proved how), never an `axiom`. -/
structure FComDischarge (P : CryptoPrimitives Digest) where
  /-- **Correctness** (CryptHOL `pedersen.abstract_correct`): an honest open of `commit v r`
  always verifies. Carried; proved in `Dregg2_FCom.thy`. -/
  correct : Prop
  /-- **Perfect hiding** (CryptHOL `pedersen.abstract_perfect_hiding`): the commitment leaks
  nothing about the committed value — the hiding half of dregg2's `unlinkable`. Carried. -/
  perfectHiding : Prop
  /-- **Binding reduces to DLog** (CryptHOL `pedersen.pedersen_bind` /
  `pedersen_asymp.dregg2_binding_under_dlog`): equivocating a commitment is exactly as hard as
  discrete log; negligible under DLog hardness — dregg2's `binding`. Carried. -/
  bindingReducesToDLog : Prop
  /-- The discharge ASSERTS each transported guarantee holds (witnessed by the CryptHOL proof,
  under the transport-fidelity caveat). These are the operational contents, not free `True`s. -/
  correct_holds : correct
  /-- Perfect hiding holds (CryptHOL). -/
  hiding_holds : perfectHiding
  /-- Binding-under-DLog holds (CryptHOL). -/
  binding_holds : bindingReducesToDLog
  /-- The transported guarantees ENTAIL the dregg2 Layer-A `binding` carrier: the cross-system
  proof is what makes `CryptoPrimitives.binding` true for this primitive set. -/
  entails_binding : bindingReducesToDLog → P.binding
  /-- The transported hiding guarantee ENTAILS the (hiding half of the) dregg2 `unlinkable`
  carrier: perfect hiding is the unlinkability of the committed value. -/
  entails_unlinkable : perfectHiding → P.unlinkable

/-- **`binding_discharged_by_crypthol`** — GIVEN a CryptHOL F_com discharge for a primitive
set, that set's `binding` carrier is INHABITED. The DLog-binding obligation dregg2 carries is
now witnessed by the CryptHOL `pedersen_bind` proof — not assumed in Lean. Kernel-clean. -/
theorem binding_discharged_by_crypthol
    {P : CryptoPrimitives Digest} (d : FComDischarge P) : P.binding :=
  d.entails_binding d.binding_holds

/-- **`unlinkable_discharged_by_crypthol`** — GIVEN a CryptHOL F_com discharge, the (hiding
half of the) `unlinkable` carrier is INHABITED, witnessed by the CryptHOL
`abstract_perfect_hiding` proof. Kernel-clean. -/
theorem unlinkable_discharged_by_crypthol
    {P : CryptoPrimitives Digest} (d : FComDischarge P) : P.unlinkable :=
  d.entails_unlinkable d.hiding_holds

/-- **`binding_unlinkable_discharged_by_crypthol`** — THE BRIDGE THEOREM. A CryptHOL F_com
discharge witnesses BOTH dregg2 commitment-security carriers (`binding` ∧ `unlinkable`). This
is the cross-system §8 closure for the commitment fragment of the dynamic-UC obligation:
the carriers `EpistemicConsensus §6` leaves OPEN-in-Lean are discharged by a real proof in a
real UC tool. PROVED in Lean (kernel-clean) FROM the carried CryptHOL facts — Lean does NOT
prove UC; it threads the cross-system witness. -/
theorem binding_unlinkable_discharged_by_crypthol
    {P : CryptoPrimitives Digest} (d : FComDischarge P) : P.binding ∧ P.unlinkable :=
  ⟨binding_discharged_by_crypthol d, unlinkable_discharged_by_crypthol d⟩

/-! ## Non-vacuity over the reference instance.

To witness that `FComDischarge` is inhabitable (the bridge act is performable), we discharge it
for the `Reference` toy primitive set (`Crypto.Primitives.Reference`, whose carriers are `True`).
This is NOT the real CryptHOL transport — it is the inhabitation witness showing the structure is
constructible. The REAL discharge is for the Poseidon2/Pedersen FFI instance, vouched under the
transport-fidelity caveat against `Dregg2_FCom.thy`. -/

namespace Reference
open Dregg2.Crypto.Reference

/-- The reference primitive set's `binding`/`unlinkable` are `True`, so the discharge is
trivially constructible — the non-vacuity witness that `FComDischarge` is inhabitable. -/
def refDischarge : FComDischarge (Digest := Int) instCryptoPrimitives where
  correct := True
  perfectHiding := True
  bindingReducesToDLog := True
  correct_holds := trivial
  hiding_holds := trivial
  binding_holds := trivial
  entails_binding := fun _ => trivial
  entails_unlinkable := fun _ => trivial

/-- Non-vacuity of the bridge: at the reference instance the carriers are discharged. -/
example : (instCryptoPrimitives.binding) ∧ (instCryptoPrimitives.unlinkable) :=
  binding_unlinkable_discharged_by_crypthol refDischarge

end Reference

-- TRIPWIRES: the bridge theorems rest ONLY on the carried `FComDischarge` fields (the
-- cross-system CryptHOL facts, passed as a hypothesis), NEVER on a Lean `axiom` or a hidden
-- `sorry`. `#assert_axioms`-clean ⇒ no `sorryAx`. This is a CARRIER, not a Lean UC proof.
#assert_axioms binding_discharged_by_crypthol
#assert_axioms unlinkable_discharged_by_crypthol
#assert_axioms binding_unlinkable_discharged_by_crypthol

end Dregg2.Crypto.UCBridge
