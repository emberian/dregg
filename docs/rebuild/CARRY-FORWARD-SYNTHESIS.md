# CARRY-FORWARD SYNTHESIS — the three-faced turn, and what dregg2/4 faithfully carries forward

> Synthesis of four grounding/design docs (2026-06-01, read-only investigations):
> `EFFECT-ISA-DESIGN.md` (the effect ISA: shrink + expand), `GROUND-AUTH-ATTESTATION.md`
> (the caveat/token/attestation layer + repudiation), `GROUND-STORAGE-PROGRAMS.md`
> (storage-as-cell-programs), and the two `FAITHFULNESS-AUDIT*.md`. The driving directive:
> **carry forward the *Rust* semantics (or a coherently-extrapolated vision), not a Lean fiction.**

---

## 0. The reframe: the turn is a THREE-FACED generator, and we built one face

dregg's `EffectVmAir` lens made us treat the turn as "a list of effects." It is not. A turn is one
generator with **three co-equal faces** — exactly REORIENT's A/B/C projections:

| Face | What it is | REORIENT | Rust ground truth | Lean state |
|---|---|---|---|---|
| **EFFECTS** | the state-transition | A (living cell step) | the 54-effect VM + side-tables | built DEEPLY (this session) |
| **CAVEATS / AUTH** | authorization-narrowing (verify/find) | B (the law) + C (authority CDT) | macaroon HMAC chains, 3P discharge, selective disclosure, anon multi-show, stealth, StarkDelegation | THIN / OVERLOOKED |
| **ATTESTATION** | the output badge (permitted ∧ committed) | the observable | WitnessedReceipt (publicly-verifiable STARK) | present, but **non-repudiable, no dial** |

**The headline finding:** we have been growing the EFFECTS face deeply (and just de-vacuified +
de-shadowed it) while the CAVEAT and ATTESTATION faces are thin — and on those two faces **the Rust
is substantially richer than the Lean.** The "right basis" isn't a better effect set; it's all three
faces modeled faithfully.

---

## 1. The bidirectional carry-forward principle

Fidelity is not one-directional. The grounding showed both failure modes:

- **Rust → Lean (the advanced features):** the Lean is a *fiction or overlook* exactly where the Rust
  is rich — caveats are a bare `Ctx → Bool` (the real macaroon is an HMAC chain), 3P discharge is a
  `Bool` flip (real: encrypted ticket/VID + ephemeral key + bind-to-parent + freshness), selective
  disclosure is absent, anonymous multi-show lives in `Privacy.lean` *disconnected* from the credential
  path, Stealth + StarkDelegation are dropped from the "six modes," storage durability (WAL/redb) is
  unmodeled, the constraint vocabulary is 16 variants vs the Rust's 74. **Carry the Rust semantics.**
- **Lean → Rust (the proven laws):** the Lean *leads* where it proved a law the Rust omits — CapTP
  `granted ≤ held` non-amplification is *proved* in `AuthModes.lean` and *missing* from Rust
  `verify_captp_delivered`. **Carry the Lean proof; fix the Rust.**

So "carry forward the Rust semantics" = carry the Rust's **rich feature semantics** + the Lean's
**proven core laws**, and reconcile the two into one faithful model. The escrow shadow (FID-ESCROW)
was the first instance fixed; the caveat/discharge/disclosure shadows are the next.

---

## 2. Per-face carry-forward checklist (ranked)

### Face 1 — EFFECTS (mostly done; ISA reshape pending)
- **Collapse** ≈24 "state-passthrough + bind-hash + tick-nonce" selectors → one `Meta.bind(tag, hash)`
  (Phase R, ~60% constraint-surface cut, low-risk). *[EFFECT-ISA-DESIGN Part A]*
- **Expand (soundness):** per-asset-class balance (`bal` is one scalar; need a `CONSERVATION_VECTOR`)
  — the biggest soundness gap; cross-cell BoundDelta half-edge (CG-5); vat-boundary ρ_in/ρ_out as a
  typed membrane effect. *[Part B]*
- **Constraint vocabulary:** Lean `StateConstraint` 16 → the Rust's 74 (`RateLimit(BySum)`,
  `SenderAuthorized`, `WitnessedPredicate`, `BoundedBy`…) needed by the real storage programs.

### Face 2 — CAVEATS / AUTH (the overlooked face; Rust is ground truth)
1. **HMAC caveat-chain integrity** — model the macaroon as an append-only authenticated chain, not a
   `Ctx → Bool`. (#1 carry-forward.)
2. **Third-party discharge** — the real ticket/VID + bind-to-parent + freshness protocol, not a `Bool`.
3. **Selective disclosure / predicate proofs** (Gte/Lte/InRange over hidden attributes) — absent from
   `Credential.lean`.
4. **Anonymous unlinkable multi-show** — wire `Privacy.lean`'s unlinkability *into* the credential path.
5. **Stealth + StarkDelegation** — restore as real authorization modes (dropped from the six).

### Face 3 — ATTESTATION (the repudiation hole)
- dregg is **hardwired to maximal transferability** = non-repudiable. It HAS anonymity (hide *who*),
  LACKS deniability (authorizer can deny) and designated-verifier (non-transferable proof) **entirely**
  — grep-confirmed, no ring/chameleon/disavowal anywhere.
- The existing disclosure dials (`FieldVisibility`, `disclose`) control *what* is revealed, never *to
  whom the proof is convincing* — an orthogonal axis, pinned at maximal. **This is a genuine privacy
  hole for an anonymous-collaboration OS.**
- **The fix is a new axis, not a patch:** keep the transferable badge for the consensus/forest path
  (it's required there), add a *parallel private artifact* on the bilateral channel
  (designated-verifier ZK / deniable authentication / ring repudiation). The Lean `Discharged` predicate
  must become **verifier-indexed** (today it's a single universal predicate — which is *precisely* why
  the model can't even express "convincing only to V").

---

## 3. Storage validates the small-core direction
Storage-as-cell-programs **holds**: `CapInbox`/`ProgrammableQueue`/`PubSubTopic`/`BlindedQueue` are
`FactoryDescriptor`s carrying `CellProgram::Cases` over *existing* effects — DSL-userspace, not bespoke
kernel features. The one core primitive storage needs (a holding-store/side-table) is *already* in the
kernel (FID-ESCROW). WAL/redb/erasure/content-store are **infrastructure below the ISA** (model as a
portal or honest assumption, not as semantic law). The `CellRuntime` checkpoint/restore is currently a
*label-fiction* (`restore∘checkpoint = rfl`, no durability) — honest at the abstract level, but the
load-bearing crash-safety is the WAL, which must be acknowledged as the real (below-ISA) semantics.

⟹ **A small orthogonal effect core + verified DSL-composed userspace is the right shape** (seL4-style).

---

## 4. The dregg2 → dregg4 picture
- **dregg2 (complete the faithful kernel):** three faces modeled faithfully — effect face reshaped
  (collapse + per-asset/half-edge/membrane), caveat face carried from the Rust (HMAC/3P/disclosure),
  attestation face given the repudiation dial; small effect core + DSL storage; Rust↔Lean reconciled.
- **dregg4 (the generalization):** the turn as a uniform 3-faced generator where *every* higher-level
  capability — storage, advanced credentials, deniable/designated-verifier interaction, cross-chain —
  is composed from the small core + the caveat algebra + the attestation modes, with the
  transferability and disclosure dials as first-class. No bespoke 54-effect VM, no ad-hoc token system
  bolted beside it — one generator, three faces, two dials.

---

## 5. Recommended phased path (each reconcile-verified, Rust-grounded)
1. **Phase R** — effect-face collapse (`Meta.bind`), low-risk, proves the reshape pattern.
2. **Caveat face** — carry the real macaroon HMAC chain + 3P discharge + selective disclosure
   (the highest-fidelity-debt items; the Lean is most a fiction here).
3. **Per-asset balance** — the soundness expansion (ripples like escrow but bigger; subsumes #121).
4. **Repudiation dial** — verifier-indexed `Discharged` + a designated-verifier/deniable private mode.
5. **Cross-cell half-edge + vat-boundary membrane** — the remaining effect-face expansions.
6. **DSL demotion** — only behind verified `CellProgram` laws; else keep DERIVED-MACRO.

**Carry-forward discipline (non-negotiable):** every step grounds in the Rust semantics (or a
documented coherent extrapolation), reconcile-builds green, and never reintroduces a shadow. The Lean
must *be* the protocol — faithfully — because it will replace the Rust kernel.
