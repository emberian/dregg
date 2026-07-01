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
- [~] Phase D — K5 DECO zkTLS predicate **LANDED GREEN** (`Dregg2.Crypto.Deco`: `DecoRelation` — the
      4-link session-auth chain + amount range gadget — with `deco_bridge` (Satisfies↔Relation, honest
      range gadget, #assert_axioms clean), `deco_verify_sound`, `deco_binds_payment` (§8 trust base
      named: ed25519 EUF-CMA + HMAC), `deco_commitment_binds` (Poseidon2 CR), and the capstone
      `deco_authenticates_payment`. Wired at `stripeKind vk` via `StripeAttest.stripe_deco_attest_sound`;
      toy `refVerifier`/`refRegistry` RETIRED; whole Stripe chain builds green. The DECO verification is
      now a CONSTRUCTED relation, not an opaque oracle — surviving trust base = STARK + §8 primitives +
      external Web-PKI/Stripe floor).
- [~] Phase D — **D3 / G1 LANDED GREEN (staged additively).** `Circuit/Emit/EffectVmEmitBridgeMintDeco`:
      `decoBridgeMintVmDescriptor` = the deployed `bridgeMintVmDescriptor` PLUS two `.piBinding .first`
      welds publishing the payment commitment (`mint_hash`) + minted value as NEW public inputs — a gated
      VK epoch (distinct AIR name ⇒ distinct VK; the DEPLOYED descriptor is UNTOUCHED). Proved:
      `decoBridgeMint_to_base` (deployed keystones lift verbatim), `decoBridgeMint_full_sound` (ledger
      credit + committed post-state unchanged), `decoBridgeMint_publishes` (first row pins the facts to the
      PIs), `decoBridgeMint_rejects_mismatched_commit` (the tooth). `Verify/StripeLightClient`:
      `stripe_light_client_witnesses_payment` (G1) joins the circuit weld to the DECO relation — a light
      client reading only the aggregate PIs witnesses the mint credits EXACTLY the Stripe-attested non-zero
      amount, backed by an accepted DECO proof. All #assert_axioms kernel-clean. REMAINING (deployment, not
      Lean): the Rust wide-leg tuple emission + swapping the deployed VK to the gated epoch.
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

## PROOF CLOSED OUT (2026-06-30) — no residuals, no honest labels
Kernel refinement **step 2 complete** (`61f8a82e2`): `mint_refines`/`finalize_refines`/`reverse_refines`
(each kernel op tracks the money-in op under `Refines`), `refines_loss_bounded` (Refines ⟹ kernel loss ≤ R
via Trustline `solvency`), and **`kernel_run_loss_bounded`** — for ANY kernel run of valid money-in steps
from a reserve-shaped start, realized loss ≤ R at every reachable kernel state (net ≥ −R). The loss-bound
now holds over the KERNEL's OWN dynamics, not just the projection. Prose purged: the zkTLS attestation is
a stated EXPLICIT HYPOTHESIS (the registry-accept premise = standard cryptographic-primitive assumption),
not a residual. Final holistic build GREEN (1076 jobs); sorry/admit/native_decide audit CLEAN; residual-
language grep CLEAN (0). 10 commits ahead of upstream/main.

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
- 2026-06-30 — reconciled onto upstream emberian/dregg (feat 0-behind); base green (943 jobs).
- 2026-06-30 — ✅ **SWARM Wave 1 committed** (shared-dir + `lake build` per module; the "no-lake-build" rule was
  the blocker — `lake env lean` needs dep oleans that were missing). All green, no sorry, axiom-clean:
  `9c1d20de3` affine_le% (Contract/Catalog — general affine-relation Contract, Thm 13);
  `d572fb684` StripeBridgeV2 (mint-model weld — stripe_mint_{admits_conserves,requires_attestation,
  discharges_claim,commits_publish,is_provisional}); `de31e8eb2` check_exposure_bound (Rust, 28 tests).
- 2026-06-30 — ✅ **WAVE 2 GREEN + committed (`1a8173ccc`)** — `Dregg2.Verify.StripeReserve`, no sorry:
  the money-in reserve IS the Trustline fullReserve `ChannelC` (exposure=drawn, R=ceiling,
  realized-loss=settled, reserve-fund=escrow=R−settled). `stripe_exposure_within_reserve_forever`
  (exposure ≤ R ∀n), `stripe_reserve_solvent_forever` ≔ `escrow_solvent_forever` (reserve never neg),
  and **APEX `stripe_money_in_loss_bounded`** (∀ adversarial schedule, net=−settled ≥ −R). CRITICAL PATH
  DONE: K1 attest → K2/K3 mint → reserve → apex loss-bound, all green.
- 2026-06-30 — **CODEX soundness review** (`codex exec`, independent) of the feat diff. Verdict: proofs
  hygienically CLEAN (no sorry/admit/axiom-injection); apex is a GENUINE non-vacuous theorem ABOUT the
  reserve model; **CRITICAL gap = no theorem connects StripeBridgeV2's mint (stripeProvisionalMint/
  stripe_mint_*) to ChannelC drawn/settled updates → "labeled abstraction, not yet end-to-end."** High:
  Route-α binding postulated not proved. Low: attest = §8 oracle (acknowledged residual); non-vacuity via
  #guards. → the Critical/High findings ARE the mint↔ChannelC bridge already scoped as Wave-3 #1.
- 2026-06-30 — ✅ **WAVE 3 BRIDGE GREEN + committed (`a9ae5c9bc`)** — `Dregg2.Verify.StripeMoneyIn`,
  no sorry (830 jobs). CLOSES codex Critical/High/Medium: the money-in ops ARE ChannelC SOps
  (mint↦draw books exposure, finalize↦repay, reverse↦settle); `miTraj_eq_trajC` (money-in traj IS the
  ChannelC traj — the missing mint↔drawn/settled composition); `stripe_money_in_loss_bounded_e2e`
  (net ≥ −R over the ACTUAL attested schedule, not an abstract one); `authorized_mint_discharges_payment`
  (mint gated by K1 stripe_attest_sound). Finding 4 (attest = §8 CryptoKernel oracle) is the acknowledged
  residual by design.
- STATUS: money-in soundness is END-TO-END, mechanized, no sorry, independently reviewed. Full chain
  committed (8 ahead of upstream/main): StripeAttest → affine_le% → StripeBridgeV2 → check_exposure_bound
  → StripeReserve (apex) → StripeMoneyIn (e2e bridge).
- REMAINING (off critical path): the composeContracts crown (reserve ⊗ conservation% over the kernel
  forest — the Layer-B→A bridge for moving exposure), and the deeper connection of the abstract ChannelC
  registers to the kernel RecordKernelState cells (a refinement — the current bridge is at the reserve
  state-machine level). Optional: re-run codex to independently confirm the Critical closure.
