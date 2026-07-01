# PROGRESS — feat/stripe-kernel-attested

**Goal:** Stripe-via-kernel-primitives (K1–K6 + DECO zkTLS), **T2-mandatory** (G1 closed:
pure-light-client-verifiable attested mint/burn).
**Plan:** `superintelligent-DreggNet/docs/STRIPE-KERNEL-BUILD-PLAN.md`
**Design:** `superintelligent-DreggNet/docs/STRIPE-MIRROR-SEMANTIC-SOUNDNESS.md`
**Worktree:** `C:/Github/dregg-stripe-kernel-wt` off dregg `main` 58e5e60bc.
**Decisions:** T2 mandatory · DECO-lineage zknotary · worktree + local commits only (no push,
never touch main/WIP, no history rewrite).

## Status
- [x] Phase 0 — worktree + branch + this tracker
- [x] Phase 0 — baseline build green: cargo `dregg-turn`/`dregg-bridge` ✓; `lake` `Dregg2.Apps.BridgeCell` ✓
      (deps reused from main's `.lake/packages` via junction; `lakefile.toml`+`lake-manifest.json` copied
      from WIP and `--assume-unchanged` so they stay out of commits)
- [~] Phase A — K1: **Lean witness LANDED GREEN** (`Dregg2.Verify.StripeAttest`: `Claim` +
      `stripe_attest_sound` via `registry_sound`, **no sorry**, #guards pass; committed). NEXT: weld onto
      `BridgeCell` finality gate (abstract `witnessed`-Pred discharge) + the Rust `Verified W` side.
- [~] Phase B — K2/K3 **CORE GREEN** (`Dregg2.Verify.StripeBridge`: `stripe_release_conserves` +
      `stripe_release_requires_attestation` + `stripe_release_discharges_claim`, no sorry, committed).
      NEXT: at-most-once (no-double mint) + reversal dual (`cancelBridge`) + retirement law; then finality tier.
- [ ] Phase C — K4 quorum unify + K6 consume-once + rollback mechanized
- [ ] Phase D — K5 DECO zkTLS predicate; **D3** recursive-aggregate fold (T2)
- [ ] Phase E — integration + live sandbox attested-flow demo + light-client demo + docs

## Anchors (Dregg2 recon — Phase A) — primitives largely ALREADY PROVED; this is composition

- **K1 witness** ← `Dregg2.AttestCube.Turn.Attest V` (`AttestCube.lean:69`): product of
  **Disclosure** (`Metatheory.Dial`: acceptanceOnly<selective<full — zkTLS selective-disclosure axis)
  × **Transferability** (`Authority.DV.TransferDial`: transferable|designated — public-verifiability axis)
  × **Agreement** (`Finality.Tier`: causal<ackThreshold<bft<constitutional). Carries `BftQuorumVerifiable`
  (`:195`) + corner `deniable_bft_quorum_empty` (BFT finality ⇒ quorum-verifiable/transferable).
  → a Stripe payment witness = a `Turn.Attest` instance.
- **K3 provisional→final** ← the Agreement/`Finality.Tier` axis (provisional = tier < bft; finalize =
  raise to bft/constitutional; `Finality.no_downgrade`).
- **K4 quorum** ← `Finality.Tier.bft` + `BftQuorumVerifiable`; `Crypto/BlsThreshold.lean`
  `ThresholdCert`+`SnarkContract` (`:311,:318`); `Distributed/FinalizedLightClient.lean`
  `CertQuorum`/`FinalizedHistoryAttested` (`:110,:165`).
- **K2 dual + lifecycle** ← `Apps/BridgeCell.lean` `lockBridge`/`mintBridgeCell`/`finalizeBridge`/
  `cancelBridge` (`:137,:183,:206,:212`) — verify how complete the cancel(=reversal) + finalize duals are.
- **K6 / conservation / authority** ← `Privacy.Nullifier` (`:324`), `Spec/Conservation.turnConserves`
  (`:363`) + `disclosed_non_conservation`, `Spec/Authority.Mint` (`:189`).
- **D3 / G1** ← `Circuit/Argus/Effects/BridgeMint.lean` `compileBridgeMint : EffectVmDescriptor`
  (`:104,:116,:229`) — bridge mint ALREADY a circuit descriptor; fold = extend its public inputs with the
  payment facts so `FinalizedLightClient` witnesses them. `BlsThreshold.SnarkContract` = threshold certs
  already SNARK-ify (composes with the recursive fold).

PLAN COMPRESSION: K1/K3/K4 ≈ instantiate/compose `Turn.Attest`+`Finality.Tier`+`BlsThreshold`;
K2 ≈ complete `BridgeCell.cancelBridge` as the attested reversal dual + its retirement law;
D3/G1 ≈ extend `compileBridgeMint` public inputs + `FinalizedLightClient`. NEW = the DECO zkTLS witness
as a `Turn.Attest` (disclosure/transferability) instance + its verify predicate + the payment-fact binding.

## Decisions taken (autonomous, with rationale)
- **Lean is verifiable locally** (lake 5.0.0 / Lean 4.30.0 == metatheory pin). Proof gates run here.
- **K2/K3 anchor = `Apps/BridgeCell.lean`** — the lock/finalize/cancel lifecycle is ALREADY proved
  axiom-clean (conservation a, no-double b, witness-gate c, liveness d). The abstract `witnessed(vk)`
  finality-witness Pred (doc: "a swappable abstract Pred-discharge") is the K1/K5 seam: a Stripe
  payment's DECO zkTLS proof discharges it. So K2 = `cancelBridge` (reversal dual) + its proved
  `cancel_conserves`/`no_double`; K3 = the `{locked,finalized,cancelled}` automaton.
- **DIRECTION mapping (default, proceeding):** inbound Stripe payment→mint maps onto the bridge-cell
  *finalize-to-recipient gated on the payment attestation*; refund/dispute → *cancel*. Conservation /
  no-double / witness-gate / liveness all inherited from the proved lifecycle.
- **OPEN (to resolve while grounding, not yet user-load-bearing):** reconcile the Lean factory-cell
  `BridgeCell` model vs the Rust `turn/.../bridge_ledger.rs` note-nullifier path — same invariants, two
  encodings. Need the canonical witness-seam (is `bridge_ledger` the Rust image of `BridgeCell`, or a
  separate older path to re-point?). Decides where the zkTLS witness plugs in on the Rust side.
- **K1/K5 SEAM = `Authority/Predicate.lean` WitnessedPredicate registry (FOUND, proved).**
  `WitnessedKind` has `bridge` + open `custom (vk)`; `Verifier := Stmt→Wit→Bool` plugins; `registryVerify`
  dispatch; keystone `registry_sound` (registry accepts ⇒ predicate `Discharged`; prover `find` untrusted).
  §8 portal: crypto soundness routes through `CryptoKernel.verify` (NOT a Lean law). →
  **K1** = register a Stripe-payment `Verifier` (Stmt = payment binding {amount,currency,recipient,pi_id};
  Wit = DECO zkTLS proof) under a `stripe`/`custom` kind; `BridgeCell`'s `witnessed(vk)` finality gate IS
  this discharge. **Lean protocol soundness ≈ free** (`registry_sound` ∘ BridgeCell keystones). **HARD work
  = K5/D3:** the DECO zkTLS verify as the §8 `CryptoKernel` oracle + bind facts into `compileBridgeMint`
  public inputs (descriptor already exists). Matches the plan's risk model (D3 = the frontier).
- **K2/K3 WELD PRIMITIVE = `EscrowFactoryProbe.escrowReleaseGated (g : Int→Int→Bool)` (§HARD-iii, FOUND).**
  PROVED for ANY gate `g`: `gated_release_conserves` (conserves) + `gated_release_requires_discharge`
  (fail-closed). Keystones (a) conservation / (b) no-double / (d) liveness are orthogonal to the discharge
  kind (only need a fail-closing Prop gate). So the weld = instantiate `g` with the Stripe registry
  discharge `registryVerify reg (stripeKind vk) (encClaim c) (encWit w)`; then a committed Stripe-attested
  release inherits conservation+no-double+reversal AND, via `stripe_attest_sound`, discharges the payment
  `Claim` (⇒ the mint corresponds to a verified payment). NEXT MODULE: `Dregg2.Verify.StripeBridge`
  (import StripeAttest+EscrowFactoryProbe; `stripeGate`/`stripeAttestedRelease` + the composed soundness
  theorems + #guards). `Exec/BlindedQueue.lean` is the `Custom`-vk precedent if needed.

## DESIGN SETTLED (2026-06-30) — reserve design + proof strategy
Canonical doc: `superintelligent-DreggNet/docs/STRIPE-RESERVE-DESIGN-AND-PROOF-STRATEGY.md` (from 4 explorers +
a visionary-scholar). RESULT: money-in soundness = **loss-bounded under an adversarial oracle** (NOT
Stripe-faithful). The apex `stripe_money_in_loss_bounded` (`∀n net ≥ −R`) is a symbol-binding INSTANCE of
`Apps/Trustline.escrow_solvent_forever` (:1362, `settled≤drawn≤ceiling`) ⊗ `conservation%` — ZERO new proof
for the core bound. Provisional lifecycle = `Intent/Lifecycle` publish/fulfill/refund + finalized-XOR-burned
(:294/:311). zkTLS witness = the committed `stripe_attest_sound` (opaque observation). NEW content only:
(1) `affine_le%` catalog macro [G] (generalize `automaton_inv%` `=`→`⋈`); (2) Stripe reserve instantiation
[Route α, 0 new proof]; (3) gated-spend `step_ob` (`draw_within_line` recipe); (4) **StripeBridge v2 —
re-weld K2/K3 onto the MINT model** (current escrow-release StripeBridge is superseded; K1 StripeAttest reused);
(5) Rust `check_exposure_bound` + FFI. The Layer-B→A bridge is the only new KERNEL theorem and is OFF critical
path. BUILD ORDER = the doc's 19-theorem list. Supersedes the earlier float-vs-mint fork (mint model chosen).

## SURFACED to Ember/Alif (guardrail-#2 — load-bearing fork, 2026-06-30)
**Conservation MODEL: ICS-20 float (escrow-release) vs Effect::Mint (issuer-well).** The K2/K3 weld
(`StripeBridge`) proved conservation via `escrowReleaseGated`→`escrowSettle` — i.e. the bridge-pot
*pre-holds a float* and RELEASES it to the recipient against the attestation (conserves by MOVE; total
unchanged). This is literally **ICS-20** (escrow on source, release on dest). BUT the current Rust
(`bridge/src/stripe_mirror.rs` + `turn/.../bridge_ledger.rs`) uses **`Effect::Mint`** (issuer-well debit
— credit CREATED, backed by the payment). Two different conservation mechanisms / economic models. The
choice shapes: the conservation proof, the reversal dual (refund-the-float vs attested-Burn), and whether
dregg pre-funds a treasury. AWAITING the call before building reversal/finality/quorum on the wrong base.

## Gate log
- 2026-06-30 — Phase 0 worktree created off main 58e5e60bc; baseline build started.
- 2026-06-30 — ✅ baseline `cargo build -p dregg-turn -p dregg-bridge` GREEN (7m34s, 1 warning).
- 2026-06-30 — ✅ Lean toolchain present: lake 5.0.0 / Lean 4.30.0 (== metatheory pin). Proofs verifiable here.
- 2026-06-30 — Lean baseline build of anchor module `Dregg2.Apps.BridgeCell` started (worktree .lake cold).
- 2026-06-30 — ✅ Lean wiring fixed (mathlib path `../../../src/mathlib4` absent → reused main's built deps
  via `.lake/packages` junction + WIP config). `lake build Dregg2.Apps.BridgeCell` GREEN (3031 jobs). **PHASE 0 DONE.**
- 2026-06-30 — Phase A start: warming anchors (AttestCube/BlsThreshold/BridgeMint/FinalizedLightClient);
  reading `Authority/Predicate.lean` (the `witnessed` Pred = the K1/K5 witness seam).
- 2026-06-30 — ✅ K1 `Dregg2.Verify.StripeAttest` GREEN (824 jobs, no sorry) + committed (5fa37ad61).
- 2026-06-30 — ✅ K2/K3 core `Dregg2.Verify.StripeBridge` GREEN (943 jobs, no sorry): attested mint
  conserves + fail-closed + discharges-claim. Composes §HARD-iii `escrowReleaseGated` + `stripe_attest_sound`.
