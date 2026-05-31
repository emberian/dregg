# Phase 0 — Step-Completeness Audit of dregg1's Turn Executor

> **⚠ FRAMING CORRECTION (ember, 2026-05-31).** The gap analysis below is the keystone deliverable — *keep it*. But its conclusion ("rework dregg1's PI / move auth in-circuit to make dregg1 step-complete") is the **WRONG move and is RETIRED.** The cascade goal is **not** "fix and bless dregg1's executor" — it is "grow dregg2's verified kernel until it **replaces dregg1's busted executor wholesale**, then swap it in and delete the legacy." dregg1's step-incompleteness is not a gate to fix in dregg1; **it is the reason dregg1's executor gets deleted.** dregg2's kernel is step-complete *by construction* (`cexec_attests` proves all four conjuncts; `Circuit.lean`'s `kernelCircuit` encodes all four as gates, now emittable to the real backends via `Dregg2/Exec/CircuitEmit`). So: **read the per-conjunct table below as the REPLACEMENT-COVERAGE CHECKLIST** — what dregg2's kernel + circuit must own to swap in — not as a to-do list for patching dregg1. The swap *delivers* step-completeness for free, because the dregg2-emitted circuit attests all four. The differential is the swap-safety regression check, not a blessing of the old code.

> **Verdict (one line):** dregg1's turn executor is **step-INCOMPLETE**. Of the four
> `fullStepInv` conjuncts that `Dregg2/Exec/StepComplete.lean` proves every committed
> turn attests (`Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance`), the per-turn STARK
> proof's public-input surface attests **at most one (Conservation) — and only on one of
> two code paths**. **Authority is verified entirely in plain Rust, outside any proof.**
> ChainLink/ObsAdvance are carried in PI fields but are bound only by an *executor-trusted*
> off-AIR PI-matching loop, not by an in-circuit constraint that ties them to the real
> chain. This confirms Risk #1 / Gap #1 of `DREGG1-TO-DREGG2.md` §E and **gates Cascade-2**.
>
> Scope: this is a READ-ONLY audit. No code was changed. Every claim below is grounded in
> `file:line` against the actual Rust + the Lean target.

---

## 0. The target (what step-complete *means*)

`Dregg2/Exec/StepComplete.lean` defines the per-step invariant as four concrete conjuncts
and **proves** every committed chained step attests all four:

- `consP` — `total s'.kernel = total s.kernel` (Conservation) — `StepComplete.lean:47`
- `authP` — `authorizedB s.kernel.caps t = true` (Authority) — `StepComplete.lean:51`
- `chainP` — `s'.log = t :: s.log` (ChainLink) — `StepComplete.lean:56`
- `obsP`  — `s'.log.length = s.log.length + 1` (ObsAdvance) — `StepComplete.lean:61`
- `fullStepInv := consP ∧ authP ∧ chainP ∧ obsP` — `StepComplete.lean:65`
- `theorem cexec_attests … : fullStepInv s t s'` — `StepComplete.lean:74` (PROVED)

The proof is *cheap* because the kernel's `exec` **gates** on authority and conservation
before committing: `exec` returns `some` only when `authorizedB k.caps turn = true ∧ 0 ≤
turn.amt ∧ turn.amt ≤ k.bal turn.src` (`Dregg2/Exec/Kernel.lean:69`). Hence `exec_authorized`
(`Kernel.lean:125`) and `exec_conserves` (`Kernel.lean:109`) are theorems, and the chain
extension is structural. In Lean, **the same object that decides admissibility carries the
attestation** — there is no gap between "what the executor checked" and "what the proof
binds." Step-completeness is exactly the property that this gap is zero.

dregg1 violates that property: the thing that *decides* (the plain-Rust executor) and the
thing that *attests to a remote verifier* (the STARK PI) are different surfaces, and the
authority decision lives only in the former.

---

## (a) Does the turn proof's PI include AUTH_ROOT / CONSERVATION_VECTOR / constraint-manifest-hash?

The per-turn proof's PI surface is the **Effect VM AIR** public-input layout,
`circuit/src/effect_vm/pi.rs` (`BASE_COUNT = 198`, `pi.rs:553`). Full enumeration of the
relevant fields:

| concern | PI field(s) present? | evidence |
|---|---|---|
| **AUTH_ROOT / ACTION_AUTHORITY_DIGEST** | **NO.** There is no capability-root, no authorizer-key root, no per-action authority digest in the PI. `GrantCapability`/`RevokeCapability` update an in-trace `capability_root` column (`air.rs:746`, `air.rs:923`), but no PI field commits *who was authorized to invoke this turn*. The only key material in PI is `SOVEREIGN_WITNESS_KEY_COMMIT` (`pi.rs:197`), and even there the **signature is verified off-AIR** (see (b)). | `pi.rs:15-552` (no AUTH_ROOT); `air.rs:2796-2799` |
| **CONSERVATION_VECTOR** | **PARTIAL.** Not a multi-asset supply vector, but per-cell balance limbs `INIT_BAL_LO/HI`, `FINAL_BAL_LO/HI` (`pi.rs:42-48`) and a signed `NET_DELTA_MAG`/`NET_DELTA_SIGN` (`pi.rs:51-52`). The AIR binds per-effect balance deltas (Transfer `air.rs:457`, NoteSpend credit `air.rs:949`, NoteCreate debit `air.rs:972`, etc.) and constrains `net_delta_sign ∈ {0,1}` (`air.rs:2531`) and `actual_delta == signed_delta` (`air.rs:2562`). This is single-cell, single-asset value flow — **not** the turn-wide conservation across all touched cells. | `pi.rs:40-52`, `air.rs:457`, `air.rs:2531-2579` |
| **constraint-manifest-hash** | **PARTIAL/SHAPE-ONLY.** `SLOT_CAVEAT_COUNT` + `SLOT_CAVEAT_MANIFEST[24]` (`pi.rs:342-351`) carry the cell program's declared `StateConstraint` set into PI — a *manifest surface*. But per its own docstring (`pi.rs:319-340`) Block 3 lands only the surface; "a future row-bound AIR gadget" would pin the constraints to trace columns. Today the manifest is re-evaluated **off-AIR** by the verifier. Cells with `> MAX_SLOT_CAVEATS (4)` "fall back to executor-only enforcement (the AIR cannot bind them)" (`pi.rs:343-345`). So there is no hash of the *full* constraint program bound in-circuit. | `pi.rs:319-351` |

There is rich turn-identity PI — `TURN_HASH[4]` (`pi.rs:86`), `EFFECTS_HASH_GLOBAL[4]`
(`pi.rs:92`), `ACTOR_NONCE` (`pi.rs:99`), `PREVIOUS_RECEIPT_HASH[4]` (`pi.rs:103`) — but
the docstring is explicit that for γ.0 these are "executor-trusted" and merely cross-checked
across the bundle, not in-AIR bound (`pi.rs:73-104`). See (b)/§(ChainLink) for why that is
not attestation.

**Answer (a): NO AUTH_ROOT; a partial single-cell conservation vector (not turn-wide); only
a shape-only constraint manifest. The single most important field for step-completeness —
an in-circuit authority commitment — does not exist.**

---

## (b) In-circuit (attested) vs plain Rust (unconstrained), per concern

### Authority — **PLAIN RUST, UNCONSTRAINED.**

The executor self-describes its trust level: **"EXECUTOR-TRUSTED"** (`turn/src/executor/mod.rs:5`).
Soundness "is guaranteed IF all federation members execute the same turns … and reach
consensus" (`mod.rs:7-13`) — i.e. it rests on BFT replication, *not* on the proof.
`verify_authorization()` is listed as trust-critical: "gates all state mutations; bypass =
unauthorized writes" (`mod.rs:21`).

The authorization logic itself (`turn/src/executor/authorize.rs`, 108 KB) is pure Rust
control flow returning `TurnError::InvalidAuthorization`:
- `Authorization::Signature` → Ed25519 `verify_signature` (`authorize.rs:691,778`)
- `Authorization::Bearer` → `verify_bearer_cap` over a delegation proof (`authorize.rs:808`)
- `Authorization::Token` → datalog evaluation bound to the call's `AuthRequest` (`authorize.rs:194`)
- `Authorization::CapTpDelivered` → handoff-cert `verify_signature` (`authorize.rs:365`)
- `Authorization::Custom` → defers to a witnessed-predicate verifier (`authorize.rs:489,849`)
- `Authorization::Unchecked` → explicitly rejected in the strict path (`authorize.rs:46,822`)

**None of these are circuit constraints.** A turn proof can verify (the STARK PI binds
state commitments + value deltas + turn identity) while the actor's authority is decided by
Rust the remote verifier never re-runs. The optional `"authorization"` sub-proof in
`FullTurnProof` (`sdk/src/full_turn_proof.rs:461`) is a **derivation-chain** circuit whose
PI[0] is a `state_root` cross-checked against the Effect VM `OLD_COMMIT` (`full_turn_proof.rs:564-592`).
It proves *a key derives to a cell's state root*; it does **not** verify a signature over the
turn body, nor bind the authorizing capability to the specific effects, and it is **optional**
(`if proof.components.has_authorization`, `full_turn_proof.rs:516,564`). For the classical
call-forest path (the common path), authority never enters a proof at all.

### Conservation — **IN-CIRCUIT on the per-cell value path; PLAIN RUST on the cleartext path.**

Two distinct mechanisms, neither of which is the Lean `total s' = total s`:
- The **Effect VM AIR** binds per-effect, per-cell balance deltas and the net-delta sign
  decomposition (`air.rs:457`, `air.rs:2531-2579`). This is genuinely in-circuit but is
  **single-cell**: it attests *this cell's* balance arithmetic, not the turn-wide sum over
  all touched cells.
- **Cleartext note conservation** is a plain-Rust sum comparison per asset type:
  `check_note_conservation` → `input_total != output_total → Err` (`finalize.rs:150-180`).
  This is unconstrained by any proof.
- **Committed (Pedersen) note conservation** uses a *separate* `conservation_proof`
  (Pedersen/Schnorr), verified off the Effect VM AIR (`finalize.rs:183-210`,
  `check_committed_conservation`). This is cryptographic but is a sidecar proof, not the
  turn proof's PI, and is itself gated by the executor choosing to require it.

So conservation is attested *somewhere* for some paths, but **not as a single in-circuit
turn-wide CONSERVATION_VECTOR in the per-turn proof's PI**, and the cleartext path is plain
Rust.

### ChainLink — **PI FIELD EXISTS, but bound OFF-AIR / EXECUTOR-TRUSTED.**

`PREVIOUS_RECEIPT_HASH[4]` is a PI field (`pi.rs:103`) and is written into the PI by the
trace generator from `context.previous_receipt_hash` (`trace.rs:1523`). But:
- The AIR's descriptor lists it as a **shared-PI** field (`air.rs:112`), and the docstring
  states for γ.0 these turn-identity fields are "executor-trusted" — only "the verifier's
  cross-proof PI matching loop enforces equality across the N proofs" (`pi.rs:73-82`).
- The actual enforcement is `verify_proof_carrying_turn_bundle` (`proof_verify.rs:592`),
  which checks all per-cell PIs *agree* on `PREVIOUS_RECEIPT_HASH` and (when the turn is
  supplied) that they match `compute_turn_identity_pi(turn)` — the **executor's own view of
  the turn** (`proof_verify.rs:617-639,679-687`).

There is **no in-circuit constraint** that the `previous_receipt_hash` in PI is the digest
of the genuinely-previous committed receipt. The chain head itself lives client-side in the
SDK cipherclerk: `append_receipt` does fork detection by comparing `receipt.previous_receipt_hash`
to `self.receipt_chain.last()` (`sdk/src/cipherclerk.rs:1888-1911`). That is honest local
bookkeeping, but it is plain Rust on the prover's machine, not a property the turn proof
attests to a remote verifier.

### ObsAdvance — **NOT ATTESTED in-circuit.**

There is no PI field and no AIR constraint asserting "the chain/observation strictly
advanced by exactly this turn." The closest mechanisms are off-AIR: the cipherclerk's
strict append (`cipherclerk.rs:1888`) and `ACTOR_NONCE` agreement (executor-checked,
`proof_verify.rs:629`). Replay-detection ("the chain would not advance", `StepComplete.lean:59`)
is therefore an executor/SDK-trusted property, not a proof-attested one.

---

## (c) Per-conjunct attestation table

| `StepInv` conjunct | Lean (`StepComplete.lean`) | dregg1 mechanism | In the turn proof's PI? | Attested to a remote verifier? |
|---|---|---|---|---|
| **Conservation** | `consP`, proved via `exec_conserves` (`Kernel.lean:109`) | Per-cell balance-delta AIR (`air.rs:457,2562`); cleartext path plain Rust (`finalize.rs:150`); committed path sidecar Pedersen proof (`finalize.rs:183`) | **Partial** — per-cell value deltas yes; turn-wide vector no; cleartext path no | **Partial** — single-cell only; not turn-wide |
| **Authority** | `authP`, proved via `exec_authorized` (`Kernel.lean:125`) | `verify_authorization()` plain Rust (`mod.rs:21`, `authorize.rs` sig/bearer/token/captp/custom) | **NO** | **NO** — executor-trusted (`mod.rs:5`) |
| **ChainLink** | `chainP`, `s'.log = t :: s.log` (`StepComplete.lean:56`) | `PREVIOUS_RECEIPT_HASH` PI + off-AIR bundle PI-match (`proof_verify.rs:679`); SDK fork detect (`cipherclerk.rs:1888`) | **Field present, not in-AIR bound** | **NO** — executor-trusted PI from the prover's own turn view |
| **ObsAdvance** | `obsP`, length+1 (`StepComplete.lean:61`) | `ACTOR_NONCE` PI (executor-checked, `proof_verify.rs:629`); SDK strict append | **NO** (no advance constraint) | **NO** |

**Net:** of four conjuncts the Lean kernel attests, dregg1's *per-turn proof* attests **≈ ½
of one** (single-cell conservation), with the other 3½ resting on the EXECUTOR-TRUSTED
assumption and SDK-local bookkeeping.

---

## The gap, and why a step-incomplete proof is unsound

**Precisely what the turn proof does NOT attest:** that the actor was *authorized* to invoke
this turn (no AUTH_ROOT / signature-over-turn in PI), that conservation holds *turn-wide
across all touched cells* (only per-cell value deltas are bound), and that the new state's
receipt chain genuinely *extends the unique previous committed receipt* (the PI value is the
prover's own claim, cross-checked only for self-consistency, never anchored in-circuit to
the real chain head).

**Why this is unsound** — exactly the `Boundary.stepComplete_preserves` failure mode. The
Lean keystone says: *if* every step attests `fullStepInv`, soundness holds along the whole
run (`chained_sound`, `StepComplete.lean:106`). The contrapositive is the danger: a step
that does *not* attest the full invariant "permits a drifting future" under coinduction —
nothing downstream of it is sound. Concretely, a verifier that accepts dregg1's turn proof
accepts:

1. **A forged-authority turn.** Because authority is decided in `authorize.rs` and never
   bound in PI, a malicious/buggy executor (or any party constructing a proof bundle out of
   band) can produce a turn whose STARK verifies — correct state-commitment transition,
   correct value deltas — for an action the actor had **no capability to invoke**. The
   remote verifier has no proof obligation that would reject it; it can only trust the
   federation re-executed `verify_authorization` (`mod.rs:7-15`). Outside that trust
   boundary (a bridge, a light client, a peer federation) the authority claim is vapor.

2. **A leaked-conservation turn.** A turn touching multiple cells, or using the cleartext
   note path, can satisfy each per-cell AIR while violating turn-wide supply (the per-cell
   AIR never sees the other cells; the cleartext sum check is plain Rust). A verifier
   trusting the per-turn proof for "value is conserved" is trusting a property the proof
   does not carry.

3. **A replayed / forked turn.** Since `PREVIOUS_RECEIPT_HASH` is the prover's own PI value
   (anchored only to `compute_turn_identity_pi`, the executor's view) and ObsAdvance is
   unconstrained, a verifier cannot distinguish a turn that extends the canonical chain from
   one spliced onto a fork. The chain *law* (append-only + advancing) that Lean proves
   structurally is, in dregg1, an SDK convention.

This is the "drifting future": each individually-verifying turn can drift the accepted
history away from the conserving/authorized/linear one, and because the proof does not
constrain the drift, an honest verifier cannot detect it. The Lean `Boundary` keystone
(`sound_of_step_complete`) therefore cannot fire for dregg1 today — it must stay an honest
open until the executor is made step-complete.

---

## The rework plan (minimal change to make dregg1's turn-executor step-complete)

The goal is to collapse the gap between "what the executor decides" and "what the per-turn
proof binds," so that the verifier-accepted set is exactly the `exec`-admissible set —
mirroring the Lean kernel where `exec` is *both* the gate and the attestation. Four moves,
each mapped onto a `fullStepInv` conjunct.

### 1. Authority → in-circuit (`authP`). **The load-bearing change.**

Add an **`AUTH_ROOT`** (or `ACTION_AUTHORITY_DIGEST`) PI field to `effect_vm/pi.rs` and an
AIR constraint that binds it:
- **PI field:** `AUTH_ROOT[4]` (4-felt Poseidon2), appended after `OWNER_CELL_ID`
  (`pi.rs:550`), with `BASE_COUNT` bumped (`pi.rs:553`). Reuse the v2 PI-length-versioning
  pattern (`pi.rs:259-277`) so verifiers reject old-shape proofs.
- **What it commits:** the digest of the authorization that admitted *each authorized
  action in this turn* — for signatures, a Schnorr/Ed25519 verification gadget
  (`circuit/src/schnorr_air.rs`, `native_signature_air.rs` already exist) over the turn's
  canonical signing message, with the verifying key folded into `AUTH_ROOT`; for
  bearer/token caps, the capability-chain digest the datalog/biscuit verifier accepted,
  folded into the same root. The "authorization" derivation sub-proof
  (`full_turn_proof.rs:461`) is the seed: make it **mandatory** and extend it from "key
  derives to state_root" to "key/capability authorizes *these effects*," with its PI[0]
  already cross-bound to `OLD_COMMIT` (`full_turn_proof.rs:564`) and now also to `AUTH_ROOT`.
- **AIR constraint:** a row-0 boundary pinning the in-trace authorizer-identity aux columns
  to `AUTH_ROOT`, exactly mirroring the existing sovereign-witness teeth
  (`air.rs:2782-2826`) — but for the *general* actor, not only sovereign cells, and with the
  **signature verified inside the gadget** rather than the executor "supplying PI from the
  signature-verified key" (`air.rs:2796-2799`).
- **Maps to:** `authP s t s' = (authorizedB s.kernel.caps t = true)` (`StepComplete.lean:51`).
  After this change, "the STARK verifies" ⇒ "the actor was authorized," matching
  `exec_authorized`.

### 2. Conservation → turn-wide in-circuit (`consP`).

Promote the per-cell value deltas to a **turn-wide `CONSERVATION_VECTOR`**:
- **PI field:** a small fixed-size `(asset_type, signed_net_delta)` vector (reuse the
  `NET_DELTA_MAG`/`NET_DELTA_SIGN` decomposition, `pi.rs:51-52`, and the bilateral
  aggregation roots already in PI, `pi.rs:147-168`) summed across all per-cell proofs of the
  turn. The aggregation micro-AIR the γ.1 docstring already anticipates
  (`pi.rs:88-93` "elevates the effects_hash_global → Σ effects_local merge to an
  aggregation micro-AIR") is the right vehicle: extend it to also assert
  `Σ per-cell net_delta == 0` per asset.
- Bring the **cleartext note path** under the same vector (today plain Rust,
  `finalize.rs:150-180`) so it is not a proof bypass, and keep the committed Pedersen path
  (`finalize.rs:183`) as the hidden-amount instance of the same equation
  (`PrivacyKernel.committed_conservation_kernel` is the Lean target).
- **Maps to:** `consP s t s' = (total s'.kernel = total s.kernel)` (`StepComplete.lean:47`),
  i.e. `exec_conserves` turn-wide rather than per-cell.

### 3. ChainLink → in-circuit anchor (`chainP`).

The PI field already exists (`PREVIOUS_RECEIPT_HASH`, `pi.rs:103`); the missing piece is an
**in-AIR (or aggregation-AIR) constraint** that `NEW_COMMIT`/receipt is `H(prev_receipt ‖
turn_body ‖ …)` — i.e. the new chain head is a hash of the *attested* previous head plus
*this* turn, not a free PI value. Move the cipherclerk's fork-detection equality
(`cipherclerk.rs:1888-1911`) from plain Rust into this constraint so the link is proof-borne.
- **Maps to:** `chainP s t s' = (s'.log = t :: s.log)` (`StepComplete.lean:56`).

### 4. ObsAdvance → in-circuit monotonicity (`obsP`).

Add a constraint that the chain/observation counter strictly increments by one for the
committed turn — bind `ACTOR_NONCE`/a chain-length field at row 0 to `prev + 1` (today only
executor-checked, `proof_verify.rs:629`). This makes replay detectable by the *proof*
(`StepComplete.lean:59`).
- **Maps to:** `obsP s t s' = (s'.log.length = s.log.length + 1)` (`StepComplete.lean:61`).

### Sequencing / what unblocks

- The **minimal** step-complete kernel is (1)+(2): authority-in-circuit + turn-wide
  conservation, because those are the two safety-critical conjuncts a remote verifier most
  needs and the two with no honest in-circuit story today. (3)+(4) make replay/fork
  proof-borne and complete the parity with `fullStepInv`, but the chain law is already
  structurally honest in the SDK and is a smaller risk.
- Land this **before Cascade-2** (`DREGG1-TO-DREGG2.md` §D): only once "the STARK verifies"
  ⇒ `fullStepInv` can the `TurnExecutor`'s decision core be routed through `Exec.step` with
  the Rust executor reduced to driver/journaling/I-O. The differential harness
  (`dregg-dsl-differential`, backend #8) should assert Rust-accept ≡ Lean `exec = some` on
  the new PI surface throughout the transition.
- Once (1)+(2) hold in-circuit and the bridge is green, `Boundary.sound_of_step_complete`
  fires for the concrete machine: `Core.conservation_step` (`Dregg2/Core.lean:154`, today a
  `sorry`/operational obligation, `Core.lean:162`) is discharged for dregg1 exactly as
  `conservation_step_realized` discharges it for the Lean kernel (`StepComplete.lean:91`).

---

## Appendix — primary evidence index

- Lean target: `metatheory/Dregg2/Exec/StepComplete.lean:47,51,56,61,65,74,91,106`;
  `metatheory/Dregg2/Exec/Kernel.lean:69,109,125`; `metatheory/Dregg2/Core.lean:154,162`.
- Executor trust model + auth-gate: `turn/src/executor/mod.rs:5,7-15,21`.
- Authorization in plain Rust: `turn/src/executor/authorize.rs:46,194,365,489,691,778,808,822,849`.
- Conservation (cleartext plain Rust / committed sidecar): `turn/src/executor/finalize.rs:150-180,183-210`.
- Per-cell conservation in-AIR: `circuit/src/effect_vm/air.rs:457,949,972,2531-2579`.
- PI layout (no AUTH_ROOT; partial conservation vector; shape-only manifest):
  `circuit/src/effect_vm/pi.rs:15-552`, esp. `42-52` (balances), `86-104` (turn identity),
  `319-351` (slot-caveat manifest), `553` (`BASE_COUNT`).
- Sovereign-witness teeth (the in-AIR pattern to generalize; signature still off-AIR):
  `circuit/src/effect_vm/air.rs:2782-2826`.
- ChainLink/ObsAdvance off-AIR enforcement: `circuit/src/effect_vm/trace.rs:1523`;
  `turn/src/executor/proof_verify.rs:592,617-639,679-687`; `sdk/src/cipherclerk.rs:1888-1911`.
- FullTurnProof verify path (optional, derivation-only "authorization" sub-proof):
  `sdk/src/full_turn_proof.rs:429,461,516,564-592`.
</content>
</invoke>
