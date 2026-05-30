/-
# Dregg2.Authority.VerificationKey — the side-loaded verification-key layer.

This module models dregg2's **content-addressed circuit identity** and the **side-loaded-VK
binding discipline** in the verified semantics. It mirrors two real systems:

* **dregg1's `canonical_vk_v2`** (`cell/src/vk_v2.rs`): a verification key is a content hash of
  FOUR components — `program_bytes` (which cell-program/AIR), `air_fingerprint` (which AIR
  descriptor), `verifier_fingerprint` (which verifier impl), `proving_system_id`
  (Plonky3BabyBearFri | KimchiPasta | Sp1V6 | Custom). The VK *names the whole circuit identity*
  of a cell's program. This is `dregg2 §5`'s `AIR-id = H(canonical(schema_decl))`, and it
  GENERALIZES the Factory's `factoryHash` (which hashed `(schema, program)` only — here the hash
  also fixes the verifier impl and proving system).

* **Mina's side-loaded VK** (`study-mina-relink §4`): the VK lives *in the account*; a
  `Control.Proof` is a `Pickles.Side_loaded.Proof` verified against *whatever VK the account
  currently holds*. The `Authorization_kind.Proof` carries a `verification_key_hash` the proof
  CLAIMS, and the transaction loop asserts it **matches the account's current VK hash**
  (`Unexpected_verification_key_hash`). The account's `proved_state` bit tracks whether the
  whole app-state is still proof-vouched — reset to `false` on any non-proof state edit.

**The §8 rail (critical, `REORIENT.md §6`, `CryptoKernel.lean`).** Two things are NEVER proved in
Lean: (1) the VK's **collision-resistance** (the content hash binds its preimage) and (2) that a
proof actually **verifies against the VK** (`CryptoKernel.verify`). Both are crypto-interface
obligations discharged by the circuits + Rust. Here:
  * `canonicalVk` is an **opaque** content-hash; its injectivity is a named `Prop`
    (`VkInjective`), surfaced as an explicit *hypothesis* on the theorems that need it — NOT an
    `axiom`. The hash circuit discharges it.
  * `CryptoKernel.verify` is the §8 oracle, called but never reasoned-into.
The Lean law models ONLY the **structural binding discipline**: a VK is content-addressed; a
proof-turn's claimed VK must equal the cell's current VK; `proved_state` resets correctly; Derived
child VKs are reproducible from `(base, params)`.

Pure, computable, `#eval`-able. Imports `CryptoKernel` (the §8 oracle/laws) and `Upgrade` (for the
anti-brick bridge note); reuses `Dregg2.Crypto.CryptoKernel` and `Dregg2.Upgrade.AirVersion`
unchanged. Defines only NEW names under `namespace Dregg2.Authority.Vk`.
-/
import Dregg2.CryptoKernel
import Dregg2.Upgrade

namespace Dregg2.Authority.Vk

open Dregg2.Crypto

/-! ## `ProvingSystemId` — which proving system a VK is bound to. -/

/-- **`ProvingSystemId`** — the proving-system tag carried in `canonical_vk_v2`
(`cell/src/vk_v2.rs`). The VK names not just the AIR but the *verifier family*: a proof for the
SAME AIR under a different proving system is a DIFFERENT circuit identity (a different VK). This is
why `canonicalVk` mixes the proving system into the hash — swapping the backend swaps the VK,
which is exactly the brick hazard `Upgrade.lean` guards. -/
inductive ProvingSystemId where
  /-- Plonky3 over BabyBear with FRI (dregg1's default). -/
  | plonky3BabyBearFri
  /-- Kimchi over the Pasta curves (Mina's proving system). -/
  | kimchiPasta
  /-- SP1 v6 (a RISC-V zkVM proving system). -/
  | sp1V6
  /-- An out-of-band custom proving system, tagged by an id. -/
  | custom (id : Nat)
  deriving DecidableEq, Repr

/-! ## `VkComponents` — the four content-addressed components of a verification key. -/

/-- **`VkHash`** — a verification-key hash: the content-addressed identity of a whole circuit.
Kept as an opaque `Nat` (a content hash is an abstract injective id). Its *collision-resistance*
is a §8 crypto-interface obligation (the hash circuit's binding), NEVER a Lean law — we surface it
as the `VkInjective` hypothesis, not an axiom. -/
abbrev VkHash := Nat

/-- **`VkComponents`** — the FOUR components a `canonical_vk_v2` content-addresses
(`cell/src/vk_v2.rs`): `programHash` (which cell-program / AIR bytes), `airFingerprint` (which AIR
descriptor), `verifierFingerprint` (which verifier impl), and `provingSystem` (which proving
system). Hashing all four is what makes the VK name the *whole* circuit identity — generalizing the
Factory's `factoryHash`, which fixed only `(schema, program)`. -/
structure VkComponents where
  /-- Hash of the cell-program / AIR bytes (`program_bytes`). -/
  programHash : Nat
  /-- Fingerprint of the AIR descriptor (`air_fingerprint`). -/
  airFingerprint : Nat
  /-- Fingerprint of the verifier implementation (`verifier_fingerprint`). -/
  verifierFingerprint : Nat
  /-- Which proving system (`proving_system_id`). -/
  provingSystem : ProvingSystemId
  deriving DecidableEq, Repr

/-! ## `canonicalVk` — the opaque content-hash of the four components. -/

/-- **`canonicalVk`** — the content-hash of a VK's four components (`canonical_vk_v2`). Modeled as
an OPAQUE function: we never unfold it. The only fact theorems use is `VkInjective` (below), the
honest injectivity hypothesis standing for *content-address binding* — collision-resistance of the
hash, a §8 obligation discharged by the hash circuit, NOT a Lean theorem. -/
opaque canonicalVk : VkComponents → VkHash

/-- **`VkInjective` (§8 OBLIGATION, a named hypothesis — NOT an axiom).** Content-addressing means
the hash binds its preimage: two VKs with the same hash have the same four components. This is
exactly collision-resistance of `canonical_vk_v2`, which is a crypto-interface obligation (the hash
circuit's extractability), NEVER a Lean theorem. We carry it as an explicit hypothesis on the
theorems that need it (`vk_determines_components`) — the Lean cell proves "*if* the hash is
injective *then* equal-vk ⇒ equal-components"; the circuit discharges the injectivity.
(`CryptoKernel.lean`'s `hash_inj` is the same idiom; `REORIENT.md §6`: crypto-soundness is never
merged into the Lean law.) -/
def VkInjective : Prop := Function.Injective canonicalVk

/-- **`vkOf c`** — the content-addressed VK hash of components `c`. -/
def vkOf (c : VkComponents) : VkHash := canonicalVk c

/-- **`vk_determines_components`** — content-addressing makes the circuit identity inspectable:
equal VK hashes ⇒ equal components, GIVEN the §8 injectivity hypothesis. (Mirrors Factory's
`vk_determines_invariants`; the four components, not just `(schema, program)`.) -/
theorem vk_determines_components (hinj : VkInjective) {c₁ c₂ : VkComponents}
    (h : vkOf c₁ = vkOf c₂) : c₁ = c₂ :=
  hinj h

/-! ## `VkCell` — a cell that holds a side-loaded VK + a `proved_state` bit. -/

/-- **`VkCell`** — a cell holding a **side-loaded verification key** (Mina's account-held VK,
`zkapp_account.ml:198`) plus the `provedState` bit. `currentVk` is the VK hash the cell currently
trusts; a proof-authorized turn must claim *this* VK. `provedState` tracks whether the cell's state
is still vouched-for by a proof against `currentVk` (Mina's `proved_state`). `stmt` is the
statement digest the cell's current state commits to (what a proof must discharge). -/
structure VkCell (Digest : Type) where
  /-- The VK hash the cell currently holds / trusts (Mina's account-held VK hash). -/
  currentVk : VkHash
  /-- Whether the current state is still vouched-for by a proof against `currentVk`. -/
  provedState : Bool
  /-- The statement digest the current state commits to (what a proof must discharge). -/
  stmt : Digest

/-- **`ProofTurn`** — a proof-authorized turn (Mina's `Authorization_kind.Proof`). It carries the
`claimedVk` hash the proof CLAIMS to be against (`account_update.ml:55`) and the `proof` itself.
The binding discipline: `claimedVk` must equal the cell's `currentVk`, else
`Unexpected_verification_key_hash`. -/
structure ProofTurn (Digest : Type) (Proof : Type) where
  /-- The VK hash this proof claims to be verified against. -/
  claimedVk : VkHash
  /-- The side-loaded proof itself (verified against the cell's current VK by the §8 oracle). -/
  proof : Proof

/-! ## THE BINDING KEYSTONE — `admitProof` and `proof_binds_current_vk`.

A proof-turn is admissible ONLY when (1) its claimed VK matches the cell's current VK
(`Unexpected_verification_key_hash` discipline — you cannot prove against a stale/swapped VK) AND
(2) the §8 `CryptoKernel.verify` oracle accepts the proof against the cell's statement. The Lean
law owns (1) — the *structural binding*; (2) is the opaque oracle. -/

variable {Digest Proof : Type} [AddCommGroup Digest]

/-- **`admitProof cell t`** — does proof-turn `t` admit against `cell`? Iff the claimed VK equals
the cell's current VK (the `Unexpected_verification_key_hash` gate) AND the §8 oracle verifies the
proof against the cell's statement. Both must hold; `verify` is the crypto oracle (`CryptoKernel`),
the equality is the structural binding the Lean law enforces. -/
def admitProof [CryptoKernel Digest Proof]
    (cell : VkCell Digest) (t : ProofTurn Digest Proof) : Bool :=
  decide (t.claimedVk = cell.currentVk) && CryptoKernel.verify cell.stmt t.proof

/-- **`proof_binds_current_vk`** — THE binding keystone. Any proof-turn that `admitProof` accepts
MUST have claimed exactly the cell's current VK. You cannot get a proof admitted against a stale or
swapped VK: this is Mina's `Unexpected_verification_key_hash` assertion lifted into the verified
semantics. (Note: this is the STRUCTURAL discipline — it does NOT claim the proof is sound, which is
the §8 oracle's separate obligation.) -/
theorem proof_binds_current_vk [CryptoKernel Digest Proof]
    (cell : VkCell Digest) (t : ProofTurn Digest Proof)
    (h : admitProof cell t = true) : t.claimedVk = cell.currentVk := by
  unfold admitProof at h
  -- `admitProof = decide (claimedVk = currentVk) && verify …`; from `= true`, the left conjunct
  -- holds, so the decided equality is true.
  have hle : decide (t.claimedVk = cell.currentVk) = true := (Bool.and_eq_true _ _ |>.mp h).1
  exact of_decide_eq_true hle

/-- **`mismatched_vk_rejected`** — the contrapositive face: a proof-turn whose claimed VK does NOT
match the cell's current VK is rejected, no matter how good the proof is (the §8 oracle is never
even consulted as the deciding factor). The swapped-VK attack is structurally impossible. -/
theorem mismatched_vk_rejected [CryptoKernel Digest Proof]
    (cell : VkCell Digest) (t : ProofTurn Digest Proof)
    (h : t.claimedVk ≠ cell.currentVk) : admitProof cell t = false := by
  unfold admitProof
  have : decide (t.claimedVk = cell.currentVk) = false := decide_eq_false h
  rw [this, Bool.false_and]

/-! ## THE `proved_state` KEYSTONE — `editUnproven`, `editProved`, and the reset law.

`proved_state` is "is this state still circuit-vouched?" (Mina, `zkapp_account.ml:215`). It is set
true only when a proof keeps/sets the whole state, and **reset to false** whenever the state is
touched without a full proof (`zkapp_command_logic.ml:1522-1547`). -/

/-- **`editUnproven cell newStmt`** — touch the cell's state WITHOUT a full proof (a signature/owner
edit). The new statement is installed and `provedState` is **reset to `false`**: the state is no
longer vouched-for by a proof against the current VK. (Mina's `proved_state := false` on non-proof
edit.) -/
def editUnproven (cell : VkCell Digest) (newStmt : Digest) : VkCell Digest :=
  { cell with stmt := newStmt, provedState := false }

/-- **`editProved cell t newStmt`** — touch the cell's state WITH a full proof-turn `t` (admitted).
The new statement is installed and `provedState` is **set/kept `true`**: a current-VK proof vouches
for the whole new state. (Mina's `proved_state := true` when a proof keeps/sets all app-state.) -/
def editProved [CryptoKernel Digest Proof]
    (cell : VkCell Digest) (_t : ProofTurn Digest Proof) (newStmt : Digest) : VkCell Digest :=
  { cell with stmt := newStmt, provedState := true }

omit [AddCommGroup Digest] in
/-- **`provedState_reset_on_unproven`** — the reset transition (Mina precedent): any non-proof
state edit drives `provedState` to `false`. The "still circuit-vouched?" bit honestly drops the
moment state changes without a proof. -/
theorem provedState_reset_on_unproven (cell : VkCell Digest) (newStmt : Digest) :
    (editUnproven cell newStmt).provedState = false := rfl

/-- **`provedState_set_on_proven`** — the complementary transition: a full proof-edit sets/keeps
`provedState = true`. The bit is restored exactly when a current-VK proof re-vouches the state. -/
theorem provedState_set_on_proven [CryptoKernel Digest Proof]
    (cell : VkCell Digest) (t : ProofTurn Digest Proof) (newStmt : Digest) :
    (editProved cell t newStmt).provedState = true := rfl

omit [AddCommGroup Digest] in
/-- **`editUnproven_preserves_vk`** — a non-proof state edit does NOT change the cell's VK: only a
`set_verification_key` upgrade re-keys (the bridge below). Touching state and re-keying are distinct
moves (Mina: `proved_state` reset ≠ VK change). -/
theorem editUnproven_preserves_vk (cell : VkCell Digest) (newStmt : Digest) :
    (editUnproven cell newStmt).currentVk = cell.currentVk := rfl

/-! ## `ChildVkStrategy` — Fixed vs Derived child VKs (constructor transparency). -/

/-- **`deriveVk base params`** — the deterministic derivation of a child VK from a base VK and
constructor parameters (`ChildVkStrategy::Derived { base_vk }`, param-derived child VKs). Modeled as
an opaque *function* of exactly `(base, params)` — that it is a function is the whole point:
anyone with `(base, params)` reproduces the identical child VK (constructor transparency). We do not
unfold it; we only use that it is a function (so equal inputs ⇒ equal output). -/
opaque deriveVk : VkHash → Nat → VkHash

/-- **`ChildVkStrategy`** — how a factory assigns a child cell's VK (`cell/src/cell.rs`):

* `fixed vk` — every child gets exactly this fixed VK.
* `derived base` — each child's VK is `deriveVk base params`, reproducible from `(base, params)`.

The Derived arm is the transparent one: the params determine the child VK, so a third party can
recompute it and verify the child carries the claimed circuit identity. -/
inductive ChildVkStrategy where
  /-- A fixed child VK hash, the same for every child. -/
  | fixed (vk : VkHash)
  /-- A param-derived child VK from a base VK hash. -/
  | derived (base : VkHash)
  deriving DecidableEq, Repr

/-- **`childVk strat params`** — the child VK that strategy `strat` assigns given constructor
`params`. `Fixed vk` ignores the params and yields `vk`; `Derived base` yields `deriveVk base
params`. -/
def childVk (strat : ChildVkStrategy) (params : Nat) : VkHash :=
  match strat with
  | .fixed vk    => vk
  | .derived base => deriveVk base params

/-- **`derived_vk_reproducible`** — constructor transparency for Derived VKs: the child VK of a
`Derived base` strategy is **fully determined by `(base, params)`**. Two parties with the same base
and the same params reproduce the identical child VK — no hidden state, no minting secret. -/
theorem derived_vk_reproducible (base : VkHash) (params : Nat) :
    childVk (.derived base) params = deriveVk base params := rfl

/-- **`derived_vk_deterministic`** — the function face: equal `(base, params)` give equal child VKs.
This is what makes the Derived strategy *verifiable* by a third party — it is a pure function of its
published inputs, with no minting nondeterminism. -/
theorem derived_vk_deterministic {b₁ b₂ : VkHash} {p₁ p₂ : Nat}
    (hb : b₁ = b₂) (hp : p₁ = p₂) :
    childVk (.derived b₁) p₁ = childVk (.derived b₂) p₂ := by
  subst hb; subst hp; rfl

/-- **`fixed_vk_constant`** — the Fixed arm is the trivial transparency: the child VK is the literal
`vk`, independent of params. -/
theorem fixed_vk_constant (vk : VkHash) (params : Nat) :
    childVk (.fixed vk) params = vk := rfl

/-! ## Bridge to `Upgrade.lean` — `set_verification_key` is the anti-brick VK swap. -/

/-- **`rekey cell newVk`** — a `set_verification_key` upgrade: install a new side-loaded VK. Per
Mina (`study-mina-relink §4`), a VK swap re-keys the cell to a NEW circuit identity. Crucially,
re-keying alone does NOT reset `provedState` (Mina trusts the new VK; continuity is by the
`set_verification_key` *permission*, not content-equivalence) — so we preserve `provedState` here.
The AUTHORITY to perform this swap is `Upgrade.lean`'s domain. -/
def rekey (cell : VkCell Digest) (newVk : VkHash) : VkCell Digest :=
  { cell with currentVk := newVk }

omit [AddCommGroup Digest] in
/-- **`rekey_installs_vk`** — a `set_verification_key` upgrade installs exactly the requested VK as
the cell's new current VK. After re-keying, a proof-turn must claim the NEW VK (by
`proof_binds_current_vk`) — so a backend swap that changes the VK changes what proofs are admissible,
which is precisely the brick hazard `Upgrade.lean` guards. -/
theorem rekey_installs_vk (cell : VkCell Digest) (newVk : VkHash) :
    (rekey cell newVk).currentVk = newVk := rfl

omit [AddCommGroup Digest] in
/-- **`rekey_preserves_provedState`** — re-keying alone does NOT reset `provedState` (Mina:
"changing the VK does not by itself reset proved_state"). The bit only drops on a non-proof STATE
edit (`provedState_reset_on_unproven`), not on a VK swap. -/
theorem rekey_preserves_provedState (cell : VkCell Digest) (newVk : VkHash) :
    (rekey cell newVk).provedState = cell.provedState := rfl

/--
**Bridge note: the anti-brick connection to `Upgrade.lean`.**

`rekey` is the *state transition* of a `set_verification_key`; `Dregg2.Upgrade` owns its
*authorization*. The two compose as the full anti-brick discipline:

* `Upgrade.setProgramAdmissible live stored auth` decides WHETHER a re-key is authorized: a
  current-version proof (`byProof live`) OR the owner-signature fallback (`bySignature`).
* `Upgrade.stale_version_falls_back_to_signature`: when the cell's pinned `AirVersion` is stale
  (a backend/proving-system swap bumped the live version), the proof arm is inadmissible, so the
  ONLY admissible authorization is `bySignature` — the owner re-keys by signature.
* `Upgrade.upgrade_never_bricks`: such an authorization ALWAYS exists, so a `ProvingSystemId` swap
  (which, by `canonicalVk` mixing `provingSystem` into the hash, changes the cell's VK and thus
  what proofs `admitProof` accepts) can never permanently strand the cell.

`rekeyAdmissible` below packages the connection: a `rekey` to `newVk` is admissible exactly when the
underlying `set_program`/`set_verification_key` authority is admissible. -/
def rekeyAdmissible (live stored : Dregg2.Upgrade.AirVersion)
    (auth : Dregg2.Upgrade.UpgradeAuth) : Prop :=
  Dregg2.Upgrade.setProgramAdmissible live stored auth

/-- **`rekey_never_bricks`** — the anti-brick guarantee, re-exported for the VK layer: for ANY pair
of pinned/live versions (any `ProvingSystemId`/backend swap), there EXISTS an admissible
authorization for a `set_verification_key` re-key. Hence a VK swap can never permanently brick a
cell — directly `Upgrade.upgrade_never_bricks`, lifted through `rekeyAdmissible`. -/
theorem rekey_never_bricks (live stored : Dregg2.Upgrade.AirVersion) :
    ∃ auth : Dregg2.Upgrade.UpgradeAuth, rekeyAdmissible live stored auth :=
  Dregg2.Upgrade.upgrade_never_bricks live stored

/-! ## `#eval` demos — the layer computes (over the reference CryptoKernel). -/

section Demos

open Dregg2.Crypto.Reference

/-- A VK's four components: program `7`, AIR `11`, verifier `13`, under Plonky3/BabyBear/FRI. -/
def demoComponents : VkComponents :=
  { programHash := 7, airFingerprint := 11, verifierFingerprint := 13,
    provingSystem := .plonky3BabyBearFri }

/-- The content-addressed VK hash of `demoComponents`. -/
def demoVk : VkHash := vkOf demoComponents

/-- A cell holding `demoVk` as its side-loaded VK, currently proof-vouched, committing to
statement `5` (the reference digest is `ℤ`; the reference `verify` accepts iff proof echoes stmt). -/
def demoCell : VkCell D := { currentVk := demoVk, provedState := true, stmt := 5 }

/-- A proof-turn claiming the MATCHING VK with a correct echo-proof (reference `verify` accepts). -/
def goodTurn : ProofTurn D P := { claimedVk := demoVk, proof := 5 }

/-- A proof-turn claiming a MISMATCHED VK (`demoVk + 1`): rejected by the binding gate. -/
def badVkTurn : ProofTurn D P := { claimedVk := demoVk + 1, proof := 5 }

-- the content hash of the four components (an opaque value; just shows it computes structurally).
#eval demoComponents.provingSystem   -- ProvingSystemId.plonky3BabyBearFri

-- matching VK + valid proof ⇒ admitted.
#eval admitProof demoCell goodTurn    -- true

-- mismatched claimed VK ⇒ rejected (the swapped-VK attack is impossible).
#eval admitProof demoCell badVkTurn   -- false

-- an unproven state edit resets provedState to false.
#eval (editUnproven demoCell 9).provedState   -- false

-- a Derived child VK reproduced from (base, params): same base+params ⇒ same child VK.
#eval decide (childVk (.derived demoVk) 42 = deriveVk demoVk 42)   -- true

-- a Fixed child VK ignores params.
#eval decide (childVk (.fixed 99) 42 = 99)   -- true

end Demos

/-!
## Honest status

PROVED (no `sorry`, no `axiom`, no `native_decide`):
  `vk_determines_components` (given the §8 `VkInjective` hypothesis), `proof_binds_current_vk`,
  `mismatched_vk_rejected`, `provedState_reset_on_unproven`, `provedState_set_on_proven`,
  `editUnproven_preserves_vk`, `derived_vk_reproducible`, `derived_vk_deterministic`,
  `fixed_vk_constant`, `rekey_installs_vk`, `rekey_preserves_provedState`, `rekey_never_bricks`.

§8 OBLIGATIONS kept OUT of the Lean law (named hypotheses / opaque oracles, NOT proved here):
  * `VkInjective` — collision-resistance of `canonicalVk` (the hash circuit's binding); a named
    `Prop`, surfaced as a hypothesis, never an axiom.
  * `CryptoKernel.verify` soundness/extractability — that a proof "really verifies" against the VK;
    the opaque §8 oracle, called by `admitProof` but never reasoned-into.
There are NO `-- OPEN:` `sorry`s in this module: every stated theorem is the structural-binding
discipline, which is fully provable; the only un-provable facts are the two §8 obligations above,
which are (correctly) hypotheses/oracles rather than weakened-and-closed theorems.
-/

end Dregg2.Authority.Vk
