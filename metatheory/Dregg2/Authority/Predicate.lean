/-
# Dregg2.Authority.Predicate — the WitnessedPredicate registry: verify/find seam plugins.

Models dregg1's `WitnessedPredicateRegistry` (`cell/src/predicate.rs`): a map from
`WitnessedPredicateKind` (`Dfa | Temporal | MerkleMembership | NonMembership | Pedersen |
BlindedSet | Bridge | Custom{vk_hash}`) to decidable verifier plugins. Each plugin is a
`Verify : statement → witness → Bool` in the TCB; the registry dispatches by kind. The
prover (the `WitnessProducer` / matcher) is the untrusted `find` side: opaque, no
completeness, no termination.

Keystone: a witness the registry accepts for a kind discharges that kind's predicate
(soundness-by-verification), holding against any prover including adversarial ones.

§8 portal: the actual crypto soundness of the crypto kinds (Merkle binding, Pedersen
homomorphism, STARK extractability) is NEVER a Lean law. For those kinds the registry
routes through `CryptoKernel.verify` — the §8 oracle. The Lean law models dispatch +
soundness-by-verification only; the `find`/prover stays untrusted and undecidable.

Pure, `#eval`-able. Defines only new names under `namespace Dregg2.Authority.Predicate`.
-/
import Dregg2.Laws
import Dregg2.CryptoKernel

namespace Dregg2.Authority.Predicate

open Dregg2.Laws Dregg2.Crypto

/-! ## `WitnessedKind` — the registry key (lift of dregg1 `WitnessedPredicateKind`). -/

/-- The kinds of witness-bearing predicate the registry dispatches over. Faithful to
`cell/src/predicate.rs::WitnessedPredicateKind` (`predicate.rs:206`): the seven built-in,
platform-reserved kinds plus the open `custom (vk)` extension point. `Custom` carries a
verification-key hash (`Nat` here; a 32-byte BLAKE3 keyed-hash in dregg1) — it is *not* a built-in;
it lives in the registry's `custom` map keyed on `vk`. -/
inductive WitnessedKind where
  /-- DFA structural-match proof (`WitnessedPredicateKind::Dfa`). -/
  | dfa
  /-- Temporal-predicate proof (`WitnessedPredicateKind::Temporal`). -/
  | temporal
  /-- Merkle-membership proof (`WitnessedPredicateKind::MerkleMembership`). -/
  | merkleMembership
  /-- Sorted-set non-membership / non-revocation proof (`WitnessedPredicateKind::NonMembership`). -/
  | nonMembership
  /-- Pedersen-equality conservation proof (`WitnessedPredicateKind::PedersenEquality`). -/
  | pedersen
  /-- Blinded-set membership proof (`WitnessedPredicateKind::BlindedSet`). -/
  | blindedSet
  /-- Bridge-predicate proof (`WitnessedPredicateKind::BridgePredicate`). -/
  | bridge
  /-- The OPEN extension point: an app-registered, content-addressed verifier keyed by `vk`
  (`WitnessedPredicateKind::Custom { vk_hash }`). -/
  | custom (vk : Nat)
  deriving DecidableEq, Repr

/-! ## The registry = a map of verifier plugins; dispatch by kind. -/

/-- A single verifier plugin: the decidable, in-TCB `Verify : stmt → witness → Bool`. This is the
`WitnessedPredicateVerifier::verify` method (`predicate.rs:489`) — pure, no state mutation, a
checkable accept/reject bit. -/
abbrev Verifier (Stmt Wit : Type) := Stmt → Wit → Bool

/-- **The registry** (lift of `WitnessedPredicateRegistry`, `predicate.rs:658`). A map from kind to
the verifier plugin installed for that kind. `none` means "no verifier registered for this kind"
(dregg1's `KindNotRegistered`); the built-ins live under the closed kinds, `custom (vk)` under the
`vk`-keyed entry. Modelling statement/witness abstractly keeps the law parametric over the actual
proof algebra (which, for the crypto kinds, is the §8 `CryptoKernel.verify` oracle). -/
abbrev Registry (Stmt Wit : Type) := WitnessedKind → Option (Verifier Stmt Wit)

/-- **The dispatch** (lift of `WitnessedPredicateRegistry::verify`, `predicate.rs:844`): look up the
verifier for `k`, then run it. `none` (no registered verifier) fails closed — `false`, never an
accept. This is the only TCB action: route by kind, run the in-TCB checker. -/
def registryVerify {Stmt Wit : Type}
    (reg : Registry Stmt Wit) (k : WitnessedKind) (stmt : Stmt) (wit : Wit) : Bool :=
  match reg k with
  | some v => v stmt wit
  | none   => false

/-- **A registry instantiates the abstract verify/find seam (`Laws.Verifiable`) at a fixed kind.**
The predicate is the *statement-for-kind-`k`* and the witness is `Wit`; `Verify` is the dispatch at
`k`. This is how the registry's per-kind checker becomes the seam's decidable `Verify` — exactly the
move `Crypto.verifiableOfCryptoKernel` makes for the bare CryptoKernel, lifted through dispatch. -/
@[reducible] def verifiableOfRegistry {Stmt Wit : Type}
    (reg : Registry Stmt Wit) (k : WitnessedKind) : Verifiable Stmt Wit where
  Verify stmt wit := registryVerify reg k stmt wit

/-- `Discharged` under the registry-at-`k` instance is *definitionally* "the registry accepts": the
seam object and the dispatch coincide. -/
theorem discharged_iff_registryVerify {Stmt Wit : Type}
    (reg : Registry Stmt Wit) (k : WitnessedKind) (stmt : Stmt) (wit : Wit) :
    @Discharged Stmt Wit (verifiableOfRegistry reg k) stmt wit
      ↔ registryVerify reg k stmt wit = true :=
  Iff.rfl

/-! ## The keystone — soundness-by-verification through the registry. -/

/-- **`registry_sound`** — a witness the registry accepts for kind `k` discharges that
kind's predicate. Soundness-by-verification through `Laws.Discharged` at the registry-at-`k`
seam instance. The TCB is the registry's `Verify`; nothing about the prover enters. -/
theorem registry_sound {Stmt Wit : Type}
    (reg : Registry Stmt Wit) (k : WitnessedKind) (stmt : Stmt) (wit : Wit)
    (haccept : registryVerify reg k stmt wit = true) :
    @Discharged Stmt Wit (verifiableOfRegistry reg k) stmt wit :=
  -- `Discharged` at this instance unfolds, by defeq, to exactly `registryVerify … = true`.
  haccept

/-- **`registry_sound_find` — the keystone wired to the untrusted `find` (reuses `search_sound`'s
shape).** Given the prover plugin (`Laws.Searchable.find`, the untrusted `WitnessProducer`) returns
`some wit` for a statement AND the registry independently ACCEPTS it, the witness is discharged. The
prover only *proposes*; acceptance is decided solely by the in-TCB dispatch. This is the
`predicate.rs` contract literally: the producer is the left adjoint, the registry is the gate. -/
theorem registry_sound_find {Stmt Wit : Type}
    (reg : Registry Stmt Wit) (k : WitnessedKind)
    [Searchable Stmt Wit] (stmt : Stmt) (wit : Wit)
    (_hfound : Searchable.find stmt = some wit)
    (haccept : registryVerify reg k stmt wit = true) :
    @Discharged Stmt Wit (verifiableOfRegistry reg k) stmt wit :=
  -- `_hfound` is irrelevant to soundness: the gate, not the producer, decides. We carry it to
  -- document the seam (a returned witness must still pass `Verify`); soundness is `haccept` alone.
  registry_sound reg k stmt wit haccept

/-! ## The prover side carries no completeness / termination guarantee. -/

/-- **`find_untrusted`** — a prover returning `none` does not imply no witness exists.
Concretely: there exist a registry and a statement where the prover gives up yet the
registry accepts `()`. Completeness is not on the table. -/
theorem find_untrusted :
    ∃ (Stmt Wit : Type) (reg : Registry Stmt Wit) (k : WitnessedKind)
      (find : Stmt → Option Wit) (stmt : Stmt) (wit : Wit),
        find stmt = none ∧ registryVerify reg k stmt wit = true := by
  refine ⟨Unit, Unit, (fun _ => some (fun _ _ => true)), .dfa, (fun _ => none), (), (), rfl, ?_⟩
  -- The registry has a verifier for `.dfa` that always accepts; dispatch returns its bit.
  rfl

/-- **`adversarial_find_cannot_forge` — soundness holds against ANY prover.** No matter what witness
an adversarial prover synthesizes, it cannot make the registry accept against an honest verifier
that rejects it: if the kind-`k` verifier rejects `(stmt, wit)`, the dispatch rejects too — there is
no prover-controlled path to acceptance. The prover is fully quantified over and never appears in the
conclusion: the gate is the sole authority. -/
theorem adversarial_find_cannot_forge {Stmt Wit : Type}
    (reg : Registry Stmt Wit) (k : WitnessedKind) (v : Verifier Stmt Wit)
    (hreg : reg k = some v) (stmt : Stmt) (wit : Wit)
    (hreject : v stmt wit = false) :
    -- For every prover (`find`) and every witness it might produce: acceptance is impossible.
    ∀ (find : Stmt → Option Wit), find stmt = some wit → registryVerify reg k stmt wit = false := by
  intro _find _hfound
  unfold registryVerify
  rw [hreg]
  exact hreject

/-! ## `custom_is_open_extension` — `custom (vk)` is the content-addressed open extension point. -/

/-- **`custom_is_open_extension`.** Registering an app verifier under `custom (vk)` makes the
registry dispatch *that* verifier for *that* `vk`, and soundness flows through unchanged: an accepted
witness discharges. This is dregg1's `custom` map keyed on `vk_hash` (`predicate.rs:300`,
`predicate.rs:660`) — the open variant for app-registered kinds, content-addressed by `vk`. The
built-in kinds are untouched (we only override the `custom vk` slot). -/
theorem custom_is_open_extension {Stmt Wit : Type}
    (base : Registry Stmt Wit) (vk : Nat) (v : Verifier Stmt Wit)
    (stmt : Stmt) (wit : Wit) (haccept : v stmt wit = true) :
    -- Install `v` at `custom vk`, leaving every other kind as in `base`.
    let reg : Registry Stmt Wit :=
      fun k => if k = .custom vk then some v else base k
    @Discharged Stmt Wit (verifiableOfRegistry reg (.custom vk)) stmt wit := by
  intro reg
  -- Dispatch at `custom vk` resolves to `v`, which accepts; keystone closes it.
  apply registry_sound reg (.custom vk) stmt wit
  show registryVerify reg (.custom vk) stmt wit = true
  unfold registryVerify
  simp only [reg, if_pos rfl, haccept]

/-- **`custom_distinct_vk` — content-addressing separates extensions.** Two custom kinds with
DISTINCT `vk`s are distinct registry keys, so a verifier installed at `custom vk₁` is NOT consulted
for `custom vk₂`. This is the `vk_hash`-keying that makes the open extension point collision-safe:
distinct predicate bytes ⇒ distinct `vk` ⇒ distinct dispatch slot. -/
theorem custom_distinct_vk {Stmt Wit : Type}
    (base : Registry Stmt Wit) (vk₁ vk₂ : Nat) (hne : vk₁ ≠ vk₂) (v : Verifier Stmt Wit)
    (stmt : Stmt) (wit : Wit) :
    let reg : Registry Stmt Wit :=
      fun k => if k = .custom vk₁ then some v else base k
    registryVerify reg (.custom vk₂) stmt wit = registryVerify base (.custom vk₂) stmt wit := by
  intro reg
  unfold registryVerify
  have : (WitnessedKind.custom vk₂ = .custom vk₁) = False := by
    simp only [WitnessedKind.custom.injEq, eq_iff_iff, iff_false]
    exact fun h => hne h.symm
  simp only [reg, this, if_false]

/-! ## Routing a crypto kind through the §8 oracle.

For the crypto kinds (`pedersen`, `merkleMembership`, …) the verifier plugin is the
`CryptoKernel.verify` oracle (§8 portal). The Lean law models the dispatch and
soundness-by-verification discipline; it never reasons into the crypto. -/

/-- The verifier plugin for a crypto kind = the §8 `CryptoKernel.verify` oracle, wrapped to the
registry's `Verifier` shape (statement = `Digest`, witness = `Proof`). -/
def cryptoVerifier {Digest Proof : Type} [AddCommGroup Digest] [CryptoKernel Digest Proof] :
    Verifier Digest Proof :=
  fun stmt proof => CryptoKernel.verify stmt proof

/-- **`crypto_kind_routes_to_oracle`** — when a crypto kind is registered with the
`CryptoKernel.verify` oracle, an accepted proof discharges the kind's predicate. Acceptance
means the oracle said true; no Lean reasoning into the crypto occurs. Binding and
extractability remain circuit obligations (§8 portal). -/
theorem crypto_kind_routes_to_oracle {Digest Proof : Type} [AddCommGroup Digest]
    [CryptoKernel Digest Proof]
    (base : Registry Digest Proof) (k : WitnessedKind) (stmt : Digest) (proof : Proof)
    (horacle : CryptoKernel.verify stmt proof = true) :
    let reg : Registry Digest Proof := fun j => if j = k then some cryptoVerifier else base j
    @Discharged Digest Proof (verifiableOfRegistry reg k) stmt proof := by
  intro reg
  apply registry_sound reg k stmt proof
  show registryVerify reg k stmt proof = true
  unfold registryVerify
  simp only [reg, if_pos rfl]
  exact horacle

/-! ## `#eval` demos — a registry with toy verifiers; accept discharges, bad witness rejected even
from an adversarial prover. -/

namespace Demo

/-- Toy statement: a target `Nat`. -/
abbrev Stmt := Nat
/-- Toy witness: a claimed `Nat`. -/
abbrev Wit := Nat

/-- A toy `dfa` verifier: accepts iff the witness equals the statement (an "echo" matcher — the
DFA "ran" and produced the right acceptance label). -/
def dfaVerifier : Verifier Stmt Wit := fun stmt wit => decide (wit = stmt)

/-- A toy `pedersen` verifier: accepts iff the witness is twice the statement (a stand-in for a
homomorphic conservation check). -/
def pedersenVerifier : Verifier Stmt Wit := fun stmt wit => decide (wit = 2 * stmt)

/-- A demo registry: `dfa` and `pedersen` installed; every other kind unregistered (fails closed). -/
def demoReg : Registry Stmt Wit := fun
  | .dfa      => some dfaVerifier
  | .pedersen => some pedersenVerifier
  | _         => none

/-- An ADVERSARIAL prover: it always proposes the bogus witness `999`, ignoring the statement. -/
def adversarialFind : Stmt → Option Wit := fun _ => some 999

-- Accept: the honest witness `7` discharges the `dfa` predicate at statement `7`.
#guard registryVerify demoReg .dfa 7 7            -- accepted ⇒ Discharged by `registry_sound`
-- Accept: `10` discharges the `pedersen` predicate at statement `5` (10 = 2*5).
#guard registryVerify demoReg .pedersen 5 10
-- Reject: a BAD witness is rejected even though the adversarial prover proposes it.
#guard (adversarialFind 7).map (registryVerify demoReg .dfa 7) == some false
-- Reject (fail closed): an unregistered kind never accepts, whatever the witness.
#guard registryVerify demoReg .bridge 7 7 == false  -- KindNotRegistered ⇒ no accept

/-- Install a custom verifier at `custom 42` (the open extension point), content-addressed by `42`. -/
def customReg : Registry Stmt Wit :=
  fun k => if k = .custom 42 then some (fun stmt wit => decide (wit = stmt + 1)) else demoReg k

-- The custom verifier dispatches for `custom 42`: `8` discharges at statement `7` (8 = 7+1).
#guard registryVerify customReg (.custom 42) 7 8
-- A DIFFERENT vk (`custom 43`) does not see the `custom 42` verifier — content-addressed separation.
#guard registryVerify customReg (.custom 43) 7 8 == false

end Demo

end Dregg2.Authority.Predicate
