# Study — re-linking dregg2's JointTurn to the Mina zkApp model

> **Thesis:** dregg2's multi-cell **JointTurn** is, structurally, Mina's
> **`Zkapp_command`** — an atomically-committed **forest of account-updates** bound by a
> single transaction commitment. Mina is the proven precedent (one global ledger,
> Pickles recursion, custom tokens, side-loaded VKs in production since 2023). This doc
> maps the four pillars (forest/commit, token, auth, VK-upgrade) and states the one
> divergence axis and the one thing dregg2 is missing.
>
> **Sources (read):** `~/dev/mina/src/lib/mina_base/{zkapp_command,account_update,
> zkapp_account,permissions,control,account}.ml` + `transaction_logic/
> {zkapp_command_logic,mina_transaction_logic}.ml`; `docs/rebuild/dregg2.md` §1.5/§1.6.

---

## 1. The account-update FOREST = the JointTurn

**Mina.** A `Zkapp_command.t` is `{ fee_payer; account_updates; memo }` where
`account_updates` is a `Call_forest` — a list of trees, each
`{ account_update; calls = (sub-forest) }` (`zkapp_command.ml:4`, `Call_forest.Tree`).
The forest is committed **atomically** by one hash:

- `account_updates_hash t = Call_forest.hash t.account_updates` (`zkapp_command.ml:1426`)
  — a Merkle fold over the whole tree (`accumulate_hashes`, each node carries
  `stack_hash = Digest.Forest.cons (Digest.Tree.create tree) (hash rest)`,
  `:472`). **Order + nesting are in the hash.**
- `commitment t = Transaction_commitment.create ~account_updates_hash` (`:1428`) — the
  **partial** commitment (the forest only).
- `full_commitment = hash[ memo_hash; fee_payer_hash; commitment ]`
  (`Transaction_commitment.create_complete`, `:1408`) — binds memo + fee-payer too.
- **`use_full_commitment`** (per account-update, `account_update.ml:1141`) selects, *at
  signature-check time*, **which** commitment an account-update's signature must sign:
  `if use_full_commitment then full_transaction_commitment else
  transaction_commitment` (`zkapp_command_logic.ml:1291-1298`). A proof-authorized
  update is always bound to the partial commitment via its public input. So **every
  update in the forest is cryptographically bound to the same shared digest** — the
  digest *is* the turn-id; signing/proving against it is each cell's agreement to the
  identical joint turn.

**This is exactly dregg2's "shared turn-id + N-lateral aggregate."** `account_updates_hash`
= the shared turn-id; per-update binding to it = the per-cell step-proof's
`TURN_HASH/EFFECTS_HASH` agreement (γ.2 **CG-2 turn-identity agreement**,
`dregg2.md` §1.6). The forest = the tensor `C₁ ⊗ … ⊗ Cₙ`; the shared-commitment
binding = the **equalizer/pullback** over the turn-id. **dregg2 should adopt Mina's
construction wholesale here** — including the `use_full_commitment` distinction: it is
precisely the choice of *how much context a participant's authorization binds*
(forest-only vs forest+memo+fee), which dregg2 currently lacks an explicit knob for.

**Atomic-apply — what the local-state machine teaches the n-lateral 2PC.** Mina applies
the forest by a **fold over a single `Local_state`** (`zkapp_command_logic.ml:1099+`).
The load-bearing trick is **two booleans, not a coordinator**:

- `will_succeed` — computed once at the *start* of the command (`:1120`), a **prophecy**:
  "this whole forest will succeed." Threaded read-only through every step.
- `success` — set to false by the *first* `Local_state.add_check … false` (the dozens of
  `Update_not_permitted_*` / overflow / precondition checks, `:1263–1753`); never reset
  mid-forest.

At the **last** account-update an assertion welds them:
`assert (not is_last ∨ will_succeed ∨ not success)` (`:1913-1918`) — i.e. **if anyone
failed, the prophesied success must have been false**, and only
`is_successful_last_party` writes the second-pass ledger (`:1922-1933`). So the entire
forest is **all-or-none against the ledger**: partial application is impossible because
the durable write happens *once*, at the end, gated on cumulative `success`.

> **Lesson for dregg2's emergent n-lateral 2PC.** dregg2's JointTurn is "ad-hoc per-turn
> n-lateral 2PC, no global quorum." Mina shows the 2PC can be **proof-internal, not a
> live protocol**: the "prepare" votes are each cell's binding to the shared commitment
> (the prophecy `will_succeed`), and the "commit" is a *single in-circuit conjunction*
> `success = ⋀ checksᵢ` that gates the one durable write. dregg2 already has the
> conjunction (CG-2 ⊗ CG-5 in `bilateral_aggregation_air`); what it should copy is the
> **prophecy-then-verify discipline** — commit/abort is **one boolean folded over the
> whole tuple**, decided in-proof, never a network round-trip. The 2PC is *settled* by
> the aggregate proof existing; there is no separate vote phase to stall.

---

## 2. Token model = cross-cell authority + the value rib

**Mina.** Custom tokens are not a balance type — they are a **caller-frame discipline**.
Each account-update carries `may_use_token : No | Parents_own_token |
Inherit_from_parent` (`account_update.ml:156`) and the apply-loop maintains a
`Stack_frame` with `caller` and `caller_caller` (`zkapp_command_logic.ml:457-469`). The
derived authority for a child is (`:996-1005`):

```
caller_id = if inherit_from_parent then caller_caller
            else if parents_own_token then caller            (the parent's token-owner)
            else default_token
```

and the **gate** (`:1170-1183`): a non-default-token update is admissible **only if**
`account_update_token_id = caller_id` — i.e. **the token-owner account-update must be an
ancestor in the forest that consented** (`Token_owner_not_caller` check). So a
token-owner coordinates its children by *being their parent frame*; the forest's nesting
**is** the cross-asset authority structure, and a custom token can only move when its
owner-cell is present in the same atomic turn.

**dregg2 adopt.** dregg2's per-asset conservation + cross-cell `⊗` should take the
**caller-frame = ancestor-consent** model directly. Map: `caller_id` ⟶ the
`peer_cell`/owner-cell named in `StateConstraint::BoundDelta` (`program.rs:747`);
`may_use_token` ⟶ a per-half-edge flag on whether a transfer draws on
the-owner-in-this-turn vs an inherited frame. The point Mina proves: **multi-asset is
not a balance schema, it is a structural requirement that the asset's authority-cell
participate in the same JointTurn** — exactly dregg2's "a custom token moves only inside
a turn that contains its owner-cell." This subsumes the value rib (§6.1): conservation
is *per-token-id*, and a token-id is meaningful only relative to its owner-frame.

---

## 3. Auth = control + permissions

**Mina.** Three orthogonal pieces:

1. **`Control`** (`control.ml:11`): the *witness* attached to an update —
   `Proof of side_loaded_proof | Signature | None_given`.
2. **`Authorization_kind`** (`account_update.ml:23`): the update's *declared intent* —
   `Signature | Proof of vk_hash | None_given`, structured as
   `{ is_signed; is_proved; verification_key_hash }` and **folded into the
   account-update's own hash** (`:59`). This binds *which VK* a proof claims to satisfy
   into the committed forest — you cannot swap the VK after the fact.
3. **`Permissions`** (`permissions.ml:357`): a per-account **lattice** mapping each
   mutation (`edit_state`, `set_verification_key`, `increment_nonce`,
   `set_permissions`, `send`, `receive`, `access`, …) to an `Auth_required`
   (`None | Either | Proof | Signature | Impossible`). `Auth_required` is precisely the
   set of **monotone-increasing** boolean functions of `{has_sig, has_proof}`
   (`:15-48`) — a genuine lattice, not an enum.

The apply-loop computes `proof_verifies`/`signature_verifies` once
(`:1291`), then **every** state-mutation re-checks `Controller.check ~proof_verifies
~signature_verifies (permission_for_that_field)` (`:1348, 1465, 1503, 1582, 1696, …`),
emitting `Update_not_permitted_*` on failure. **Authorization is checked per-field,
in-circuit, against the account's own permission lattice.**

**Re-link.** This is dregg2's **auth-in-proof** (`StepInv`'s Authority conjunct, §7.1)
plus the **CellProgram admissibility filter** (§1.5). Map:

| Mina | dregg2 |
|---|---|
| `Control` (the witness) | the turn's `Authorization` / proof or `Token` (`action.rs:422`) |
| `Authorization_kind` (declared, hashed into the update) | the cell-program's `Circuit{circuit_hash}` / `AIR-id` bound into `TURN_HASH` |
| `Permissions` lattice per field | `CellProgram` = `None | Predicate | Cases | Circuit` — the **admissibility filter** deciding the arrow's domain per method (`program.rs:53`) |
| `Auth_required` monotone-boolean lattice | the Heyting gate-algebra (`AnyOf` ⊔, `Not`, `implies`, `program.rs:463`) |

The crucial Mina lesson dregg2 already half-has: **the permission check is uniform and
per-mutation**, not a single up-front gate. dregg2's `Cases([{guard,[c…]}…])` with
**default-deny on no-match** (`program.rs:1106`) is the same fail-closed shape as Mina's
`Impossible` / `Update_not_permitted_*`. The improvement dregg2 makes over Mina:
admissibility can be an **opaque AIR** (`Circuit{circuit_hash}`), where Mina is limited
to the fixed permission-field enum.

---

## 4. VK + upgradability (the under-covered pillar)

**Mina's actual upgrade discipline** — a zkApp upgrades *its own circuit* by replacing
its on-account verification key:

- The VK lives **in the account** (`Zkapp_account.Poly.verification_key`,
  `zkapp_account.ml:198`), alongside `zkapp_version`, `proved_state`, and
  `action_state`. It is **side-loaded**: `Control.Proof` is a
  `Pickles.Side_loaded.Proof` (`control.ml:13`) verified against *whatever VK the
  account currently holds*, not a VK fixed at compile time. `Authorization_kind.Proof`
  carries the `verification_key_hash` the proof claims (`account_update.ml:55`), and the
  loop asserts it **matches the account's current VK hash**
  (`Unexpected_verification_key_hash`, `zkapp_command_logic.ml:1255-1263`).
- **Upgrade = a `set_verification_key` update**, gated by the
  `set_verification_key` permission — uniquely a **pair**
  `('controller, 'txn_version)` (`permissions.ml:367`). The check
  (`zkapp_command_logic.ml:1564-1592`): if the account's stored
  `set_verification_key_txn_version` is **older than the current protocol txn-version**,
  the permission **falls back to `Signature`**
  (`verification_key_perm_fallback_to_signature_with_older_version`,
  `permissions.ml:77`). This is the **anti-brick discipline**: a hard-fork that changes
  the proof system cannot strand a zkApp whose old VK is now unverifiable — the owner
  can always re-key by signature.
- **`proved_state`** (`zkapp_account.ml:215`) tracks whether the *entire* app-state was
  set by a proof: set true only when a proof keeps/sets all of app-state, **reset to
  false** whenever app-state is touched without a full proof
  (`zkapp_command_logic.ml:1522-1547`). It is the bit that says "this state is still
  vouched-for by the current circuit." Crucially, **changing the VK does not by itself
  reset `proved_state`** — Mina trusts the new VK; continuity is by the
  `set_verification_key` permission, not by content-equivalence.

**Re-link to dregg2.** dregg2's `CellProgram` **is** the side-loaded VK: `AIR-id =
H(canonical(schema_decl))` (§5), `Circuit{circuit_hash}` *is* its hash, and it is a
content-addressed object the CDT can name (§1.5). The correspondences:

| Mina | dregg2 |
|---|---|
| account-held side-loaded VK | the cell's `CellProgram` (content-addressed AIR-id) |
| `set_verification_key` permission + `txn_version` fallback | a `StateConstraint`-gated **program-upgrade turn** (currently *implicit*) |
| `zkapp_version` | the AIR-id version / `AIR_VERSION` PI (§7.1) |
| `proved_state` reset on non-proof state edit | dregg2's **transparency** invariant (lazily-migrated ≡ fresh-at-v2, §5) |
| `Authorization_kind.verification_key_hash` bound into the update | `CONSTRAINT_MANIFEST_HASH` / `AIR_VERSION` bound into `TURN_HASH` (§7.1) |

**Does dregg2 match or improve?** dregg2's typed-schema-upgrade is **stronger on
soundness, weaker on operational maturity:**

- **Improves:** dregg2 demands schema-upgrade be **transparent** (commitment-equality:
  migrated ≡ fresh) **and conservative** (a DROP over a linear slot emits
  `Σbefore = Σafter + Σdropped`, §5). Mina has **no analogous content-continuity
  guarantee** — a `set_verification_key` can swap the circuit to one with arbitrarily
  different semantics over the same `app_state` vector; only the *permission* gates it,
  not any equivalence. dregg2's "preserves content-hash" is a **real upgrade-soundness
  theorem Mina lacks.**
- **Missing / weaker (adopt from Mina):** dregg2 has **no explicit upgrade-permission
  knob** with a **protocol-version fallback**. Mina's `txn_version`-gated fallback-to-
  signature is the *anti-brick* mechanism for the case dregg2 *will* hit — the recursion
  backend / AIR encoding changes (§7's "depth is a security parameter; named assumption
  required") and old `Circuit{circuit_hash}` programs become unverifiable under the new
  proof system. **dregg2 must add a `set_program` admissibility clause carrying a
  proof-system-version, with a signature-fallback when the cell's pinned version is
  older than the live verifier.** Without it, a verifier upgrade bricks live cells —
  the exact failure Mina engineered around.

---

## 5. ADOPT vs DIVERGE

**Adopt wholesale (the proven core):**

1. **The forest-as-atomic-commit.** `account_updates_hash` as the shared turn-id; every
   participant bound to it; `use_full_commitment` as the "how much context my auth binds"
   knob. (§1)
2. **The prophecy-then-conjunction 2PC.** `will_succeed` (prophecy) + `success`
   (in-circuit cumulative AND) + single end-of-forest durable write. Atomicity is a
   *proof property*, not a live coordinator. (§1)
3. **Per-field, in-circuit permission checks** against a monotone lattice
   (`Auth_required`); fail-closed `Impossible` / default-deny. (§3)
4. **Side-loaded VK + `set_verification_key`-permission + `txn_version` fallback** as the
   upgrade discipline. (§4)
5. **Token-owner-as-ancestor-frame** (`may_use_token` + `caller`/`caller_caller`):
   multi-asset = the asset's owner-cell must co-participate in the turn. (§2)

**Must diverge (Mina is one global synchronous ledger; dregg2 is not):**

- **No global ledger / no single durable write.** Mina's atomicity rests on *one*
  second-pass ledger updated once. dregg2 has **per-cell finality tiers** (§2.2): a
  JointTurn commits at the **join** of its cells' tiers, effects held until that join
  commits, no finalized value downgrades. The "single durable write" must become
  "each cell's tier-local commit, gated on the *same* aggregate proof" — the proof is
  shared, the finality is per-cell.
- **Emergent consensus, not a fixed validator set.** Mina has a global BFT producing
  one total order. dregg2's JointTurn is ad-hoc n-lateral with **no global quorum**;
  the only consensus seam is **revocation root-epoch agreement** (§3). Adopt the
  *in-proof* 2PC; reject the *global-order* substrate it sits on.
- **The cross-disjoint-group case Mina never has.** Because Mina is one ledger, every
  account-update is in the same namespace; `caller_id` is always resolvable. dregg2's
  cells can live in **mutually-disjoint reference-groups / trust-roots**. The JointTurn
  must therefore carry the **cross-side existence** binding (γ.2 **CG-5**) as an
  *irreducible bilateral obligation* — Mina never needs an analog because its forest is
  always within one ledger. This is dregg2's `dregg2.md` §10 honesty-note seam:
  cross-cell soundness is **not** reducible to per-cell soundness; it needs the joint
  agreement binding. **Keep it — it is the price of having no global ledger.**
- **Privacy.** Mina's forest, commitments, and `caller` frames are **public** on-chain.
  dregg2 adds the three-tier privacy stack (§6a): the forest topology itself (who-with-
  whom) is graph-private (ZK auth-chain + holder-blinding + stealth). dregg2's JointTurn
  must hide the equalizer structure Mina publishes.

---

## The single most important thing dregg2 is missing

**The `txn_version`-gated `set_verification_key` *anti-brick* upgrade clause.** dregg2
has the *better* upgrade-soundness story (transparent + conservative, content-hash-
preserving migration — §5, which Mina lacks), and it has the forest-commit and the
in-proof conjunction. But the current multi-cell design has **no explicit
program-upgrade authorization carrying a proof-system version with a signature
fallback.** dregg2 *will* change its recursion backend / AIR encoding (§7 explicitly
makes "depth a security parameter" and recursion deferrable), at which point every live
`Circuit{circuit_hash}` cell pinned to the old proof system becomes **unverifiable and
bricked** — the precise failure Mina's `verification_key_perm_fallback_to_signature_
with_older_version` (`permissions.ml:77`, applied at `zkapp_command_logic.ml:1568-1579`)
was built to prevent. **Adopt it:** add to `CellProgram` upgrade a
`set_program` admissibility clause that pins a proof-system/`AIR_VERSION` and, when the
cell's pinned version is older than the live verifier, **falls the upgrade authority
back to a signature by the cell's owner** — so a verifier upgrade can never strand a
sovereign cell.
