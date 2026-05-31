# DREGG4-CRYPTO-MENU — the advanced-cryptosystem toolbox mapped onto the three-faced turn

> **READ-ONLY galaxy-brain design exploration.** No code changed. This doc surveys the full
> anonymous-cryptosystem / advanced-crypto toolbox and maps each primitive onto dregg's
> *three-faced turn* — **EFFECTS ⊕ CAVEATS/AUTH ⊕ ATTESTATION**, with the two dials
> (**disclosure** ∈ {acceptance-only, selective, full} and **transferability** ∈ {public,
> designated, deniable}) — established by `CARRY-FORWARD-SYNTHESIS.md §0–§4` and
> `GROUND-AUTH-ATTESTATION.md §2.3–2.4`. The goal is to surface the advanced features and
> galaxy-brain rethinks that could *define* dregg4, beyond the deniability/designated-verifier
> gap already found. For each entry: the **capability it unlocks**, **which face it lives on**,
> **how it fits the §8 portal discipline**, **roughly what it would take**, and whether it is a
> **genuinely-new capability** or a **rephrasing of what exists**. Ends with a ranked shortlist
> (value × feasibility) and the most-surprising flags.
>
> **Discipline carried in (non-negotiable, `REORIENT.md §6`):** crypto-soundness is *never*
> merged into the Lean law. `Verify P w : Bool` is a decidable oracle; its binding/extractability
> is a §8 *portal* obligation, discharged by Rust+circuits, never by a Lean theorem
> (`metatheory/Dregg2/CryptoKernel.lean:43–95` — the portal IS `Laws.Verifiable`, consulted only
> across a vat-boundary). Every entry below states which obligation lands in the portal vs the law.

---

## 0. The frame: a turn is a 3-faced generator with 2 dials

The single structural fact that organizes this whole menu (`CARRY-FORWARD-SYNTHESIS.md §0`):

| Face | What it is | REORIENT projection | Rust ground truth |
|---|---|---|---|
| **EFFECTS** | the state-transition | A — the living-cell step | the (to-be-reshaped) ~13-CORE effect VM (`EFFECT-ISA-DESIGN.md §5`) |
| **CAVEATS / AUTH** | authorization-narrowing (verify/find seam) | B (the law) + C (authority CDT) | macaroon HMAC chains, 3P discharge, selective disclosure, stealth, StarkDelegation |
| **ATTESTATION** | the output badge (permitted ∧ committed) | the observable `Obs` | `WitnessedReceipt` (publicly-verifiable STARK; `turn/src/witnessed_receipt.rs:245`) |

The two **dials** are *orthogonal axes on the faces*, not faces themselves:
- **disclosure** — *what* is revealed (`FieldVisibility::{Public,Committed,SelectivelyDisclosable}`,
  `cell/src/state.rs:16`; presentation `disclose`, `credentials/src/presentation.rs:36`). Rich.
- **transferability** — *to whom the proof is convincing*. **Pinned at "public/maximal" today**
  (`GROUND-AUTH-ATTESTATION.md §2.1`): every badge is universally re-verifiable ⇒ non-repudiable.
  The deniability/designated-verifier gap is *this dial being a constant*.

**The galaxy-brain reframe this doc argues for dregg4:** most of the advanced-crypto toolbox is
*not* a pile of new features — it is **the set of legal values of the two dials, plus a third dial
the architecture has been silently pinning: the *quorum/time* dial on the AUTH face** ("who/when
must concur for this turn to be admissible"). Threshold, MPC, time-lock, VDF, witness-encryption,
commit-reveal and PSI all turn out to be **values of an authorization-*condition* algebra** that
dregg already half-has (the `WitnessedCondition` engine — Datalog | STARK | Await,
`GLOSSARY.md:84–90`). dregg4's thesis: **one generator, three faces, *three* dials.**

---

## 1. The menu (each: capability · face · §8 fit · cost · new-vs-rephrase)

Verdict legend: **NEW** = a capability dregg cannot express today; **DIAL** = a new value of an
existing dial (powerful, but the slot exists); **REPHRASE** = essentially already present under
another name. Effort: **S** (weeks, one portal + Lean predicate), **M** (a new circuit/protocol +
Lean dial), **L** (new theory: a non-final tensor, a new judgement, or an interactive protocol).

### 1.1 Threshold / MPC turns (k-of-n authorizes without revealing which) — **DIAL→NEW**, M–L

- **Capability unlocked.** A turn admissible *iff* k-of-n parties concur, where the badge reveals
  *that* k concurred but not *which* k. This is the missing **collective sovereign cell**: a DAO /
  multisig / committee-owned cell whose authority is a threshold predicate, with signer-anonymity.
  dregg today has only OneOf (disjunction) and AND-of-caveats (conjunction); it has **no k-of-n**,
  and certainly no *anonymous* k-of-n.
- **Which face.** Primarily **AUTH** (the authorization condition becomes a threshold predicate),
  with an **ATTESTATION** consequence (the badge attests the threshold met). It is exactly a new
  *quorum dial* value on the AUTH face: `quorum ∈ {single, k-of-n, anonymous-k-of-n}`.
- **§8 portal fit.** Clean. A threshold/FROST signature or a *silent-threshold* aggregate
  (`pdfs/dyna-hints` — silent threshold sigs over dynamic committees) verifies as a single
  `Verify(stmt, agg_proof)` at the portal; the Lean law sees only "the threshold predicate
  discharged." The anonymity (which-k) is a portal property (the aggregate hides the subset), never
  a law. This composes with the existing `AuthMode` dispatch (`metatheory/Dregg2/Exec/AuthModes.lean`)
  as a *new mode* `Threshold{n, k, committee_commitment}` whose `*_sound` lemma is `agg ⇒ ≥k held`.
- **What it would take.** (M) FROST/threshold-Schnorr verifies as one Ed25519-shaped check — nearly
  drop-in at the portal; add an `AuthMode::Threshold` + a Lean soundness lemma. (L) *Anonymous* k-of-n
  and *dynamic* committees want silent-threshold sigs (`dyna-hints`) and a committee-membership
  accumulator (§1.8) — a real new circuit. **The MPC variant (compute the post-state under MPC, not
  just authorize)** is genuinely L: it needs the *witness* (private inputs of n parties) to be
  jointly computed, which is the JointTurn tensor (`νF₁⊗…⊗νFₙ` non-final, `study-category.md`) with
  *secret-shared* per-cell witnesses — the cross-cell binding (CG-5) over MPC outputs is new theory.
- **New vs rephrase.** The single-signer threshold is a **DIAL** (slot exists in the condition
  algebra). Anonymous-k-of-n and MPC-computed turns are **NEW**. *Surprising sub-point:* a JointTurn
  whose per-cell witnesses are secret-shared **is** an MPC turn — the multi-cell machinery dregg
  already needs for atomic cross-cell commit is *one secret-sharing layer away* from general MPC.

### 1.2 Time-lock puzzles / VDF turns (a turn that unlocks at a time) — **NEW**, M

- **Capability unlocked.** A turn whose admissibility predicate is "≥ T sequential squarings have
  elapsed" (time-lock puzzle) or "this beacon output is the unique VDF of the seed" (VDF). Unlocks:
  **sealed-bid auctions that self-open** (no trusted opener), **dead-man switches**, **fair leader
  election / unbiasable randomness beacons**, **timed-release escrow**, **front-running-resistant
  ordering** (the order is fixed *before* contents are decryptable).
- **Which face.** **AUTH** — a new value of the *time/condition dial*: the gate is satisfied not by
  logic, proof, or an external await, but by **elapsed sequential work**. This is a *fourth engine*
  for `WitnessedCondition` (today Datalog | STARK | Await): add **VDF/time**.
- **§8 portal fit.** Excellent and PQ-friendly-ish: a VDF *proof of correct evaluation* is a cheap
  `Verify` (Wesolowski/Pietrzak proofs are short) — exactly the portal's shape. The Lean law sees
  "the timelock predicate discharged at block-height/epoch h"; the sequentiality assumption is a
  §8 PRIMITIVE (a hardness assumption, like Pedersen binding). It binds naturally to the existing
  `BindingSite { when: block_height }` (`GLOSSARY.md:86`).
- **What it would take.** (M) A VDF verifier portal (RSA-group or class-group VDF; or a hash-chain
  VDF for PQ posture) + an `Await::TimeLock` resolver in the await family (`GLOSSARY.md:92`,
  `EFFECT-ISA-DESIGN.md §B` return/await). The puzzle *generation* is untrusted (find), the proof
  *verification* is the gate (verify) — a perfect verify/find-seam instance.
- **New vs rephrase.** **NEW.** dregg has block-height validity windows (`ValidityWindow`,
  `token/src/dregg_caveats.rs`) but those trust the *clock/consensus*; a VDF/time-lock gives a turn
  whose unlock is *cryptographically* time-bound and *self-opening without a trusted party* — a
  different trust model. *Surprising:* this retires the `private_vickrey` app's reliance on an honest
  reveal phase — the auction can be **non-interactively self-revealing**.

### 1.3 Witness encryption (a turn whose payload decrypts only if a statement is true) — **NEW**, L

- **Capability unlocked.** Encrypt a turn's payload (or a capability) to a *statement* rather than a
  *key*: "this delegation decrypts iff the recipient later proves they satisfy predicate P", or
  "this escrow's contents open iff the chain reaches finality on event E." Unlocks **conditional
  capability handoff with no online issuer**, **escrow that opens to whoever can prove a fact**, and
  the cleanest form of **intent settlement** ("pay decrypts to whoever fills the order").
- **Which face.** Spans **AUTH** (decryptability = a predicate) and **EFFECTS** (the decrypted thing
  is the effect payload). It is the *encryption-dual* of the `∃P` intent face of the await family
  (`GLOSSARY.md:99` — "any filler satisfying P"): intent gates the *missing half*; witness-encryption
  *encrypts to* the missing half.
- **§8 portal fit.** Awkward — and that's the honest flag. General witness-encryption from
  well-founded assumptions is not yet practical/standardized; the portal would carry a heavy
  PRIMITIVE assumption. **The pragmatic dregg4 substitute is witness-encryption-*from-the-existing-
  STARK*: extractable witness encryption via "encrypt to the hash the circuit would output"** —
  i.e. lock the payload under a key derivable only from a satisfying witness to an existing AIR.
  That is buildable today and fits the portal as "decrypt key = f(valid witness)".
- **What it would take.** (L) Either a genuine WE scheme (research-grade) or (M, recommended) the
  STARK-derived extractable variant: a KDF keyed on a circuit's accepting transcript. The Lean dial:
  payload becomes `Sealed-to-Predicate P` and the `Discharged P w` predicate *also* yields the key.
- **New vs rephrase.** **NEW** as stated; the STARK-derived approximation is a **NEW** capability
  built from existing parts. *Surprising:* dregg's "verify = the only trusted judgment" stance makes
  witness-encryption philosophically *native* — the system already treats a valid witness as the
  unit of truth, so "the witness *is* the decryption key" is the same idea pushed one notch.

### 1.4 Recursive / folding privacy — private IVC over the proof-forest — **NEW**, L

- **Capability unlocked.** The proof-forest (`circuit/src/proof_forest.rs`, `Exec/ProofForest.lean`)
  folds many turn-proofs into one. **Private IVC** makes the *folded* proof reveal nothing about the
  *individual* turns — a cell's entire history compresses to one badge that proves "all my turns were
  valid" while hiding which turns, amounts, and counterparties. Unlocks **succinct private cell
  state** (a cell ships its whole verified life as O(1) bytes, zero-knowledge), **private rollups of
  cross-cell activity**, and **history-hiding checkpoints** (`cand-A §5` checkpoint becomes ZK).
- **Which face.** **ATTESTATION** (the badge is the fold) crossed with the **disclosure dial** (the
  fold is zero-knowledge over its leaves). It is the *recursive* lift of the existing
  `committed_transfer_conserves` privacy (`Exec/CellPrivacy.lean:161`) from one turn to a folded
  history.
- **§8 portal fit.** Native — folding/accumulation is exactly the `RecursionBackend` trait
  (`GLOSSARY.md:204`) and the whole `pdfs/` §18 line (Nova/Protostar/HyperNova/Mova; ZK-PCD from
  accumulation, `pdfs/zk-pcd-from-accumulation-2026-289.pdf`). The ZK property is a portal attribute;
  the law sees only "the fold verifies." **Caution (`REORIENT.md §2`):** depth is a security
  parameter — no unconditional arbitrary-depth IVC; this is honest-bounded.
- **What it would take.** (L) A ZK-folding backend behind `RecursionBackend` + per-leaf blinding, and
  the anti-brick `AIR_VERSION` discipline (`GLOSSARY.md:172`) so a folded private history survives a
  backend swap. The decisions corpus already studied this (`pdfs/PATHB-accumulation-abstraction.md`,
  `pdfs/decisions.md`).
- **New vs rephrase.** **NEW.** Folding *exists* (non-private); *private* folding is new. *Surprising:*
  this is the deepest galaxy-brain item — it makes **"the cell's entire verified past = one private
  badge"** literally true, which is the strongest possible form of the "checkpoint/replay are
  theorems" claim (`cand-A §5`): a checkpoint becomes a *zero-knowledge succinct proof of the prefix*.

### 1.5 Ring / group signatures for repudiation — **NEW (the named gap)**, M

- **Capability unlocked.** The deniability hole from `GROUND-AUTH-ATTESTATION.md §2.2(b)`: a ring
  signature gives "one of {S₁…Sₙ} authorized this; you cannot prove which, and any of us could have
  forged the appearance." Group signatures add an *opener* (accountable anonymity). Unlocks **deniable
  authorization** on the private channel and **accountable-anonymous** authority (a committee where a
  designated opener can de-anonymize on dispute — the de-jure/de-facto split made cryptographic).
- **Which face.** **ATTESTATION** + the **transferability dial** (the badge becomes *less* than
  universally-convincing about *who*) — and partly **AUTH** (the ring is the authorization set).
- **§8 portal fit.** Clean: a ring/group signature verifies as one `Verify`. The opener key (group
  sig) is a portal-held secret used only in the dispute path (`app-framework/src/dispute.rs`). The
  Lean dial: the `Discharged` predicate gains a *ring* index (the anonymity set) and, for group sigs,
  an opener-recoverable identity — a verifier-indexed but *set*-valued discharge.
- **What it would take.** (M) A ring-signature verifier portal + the auth-mode `Ring{set_commitment}`
  + wiring the existing `BlindedSet` anonymity-set commitment (`credentials/src/presentation.rs:176`,
  `cell/src/predicate.rs:274`) into a *signature* (not just a membership *proof*). Per the ground
  doc, "this is the smallest delta to get *some* repudiation."
- **New vs rephrase.** **NEW** — but the *anonymity-set commitment* it builds on already exists, so
  it is the *cheapest* of the three repudiation mechanisms. (The other two — DVZK and deniable
  interactive auth — are §1.13.)

### 1.6 Blind signatures (issuer signs without seeing the message) — **DIAL→NEW**, S–M

- **Capability unlocked.** An issuer signs a *blinded* credential/token so the issuer cannot link
  issuance to later use. Unlocks **unlinkable bearer tokens / e-cash-style capabilities** (the
  issuer grants authority it cannot later trace), **anonymous rate-limited access** (one blind
  token per epoch), and **privacy-preserving feature grants**.
- **Which face.** **AUTH** — it is a property of how the macaroon/biscuit caveat-chain is *issued*.
  It strengthens the existing `Authorization::Token` path (`turn/src/action.rs:422`) with
  issuer-unlinkability.
- **§8 portal fit.** Clean: blind-signature verification is an ordinary signature check at the
  portal; the *blinding* is the issuer-side untrusted operation. The Lean caveat model
  (`Authority/Caveat.lean`) already proves attenuation-narrowing; blindness adds an *unlinkability*
  lemma in the same shape as `Privacy.unlinkable`.
- **What it would take.** (S–M) A blind-Schnorr or BBS+ issuance path in the token backend
  (`token/src/macaroon_backend.rs`) — and BBS+ is *already the natural credential format* for the
  selective-disclosure work the carry-forward synthesis demands (`coconut-threshold-selective-
  disclosure-credentials`). So this **rides for nearly free** on the credential reconciliation.
- **New vs rephrase.** **DIAL→NEW.** The token/credential slot exists; issuer-unlinkability is a new
  property. *Surprising:* the Coconut paper (`pdfs/coconut-...`) gives blind **+ threshold** issuance
  together — so §1.1 (threshold) and §1.6 (blind) are *one* primitive if dregg adopts Coconut-style
  credentials, collapsing two menu items into one build.

### 1.7 Accumulator-based revocation — **DIAL**, S–M

- **Capability unlocked.** Anonymous, O(1)-witness revocation: a credential/cap proves *non-membership*
  in a revoked-set accumulator without revealing identity. dregg today revokes via a nullifier
  G-Set with I-confluence (`Credential.lean:226`, `credentials/src/revocation.rs`); an accumulator
  gives **succinct, privacy-preserving, partition-tolerant** revocation and **delegatable
  non-membership-proof updates** (`pdfs/private-delegation-nonmembership-proof-updates-accumulators`).
- **Which face.** **AUTH** — the revocation check inside the caveat/credential gate. It refines an
  *existing* mechanism (nullifier G-Set) into a better-shaped one.
- **§8 portal fit.** Native: accumulator membership/non-membership is a `Verify`. The PQ variant
  exists (`pdfs/lattice-accumulator-anonymous-credential-2025-1099.pdf`) — relevant to §1.9 below.
- **What it would take.** (S–M) Swap the G-Set non-revocation root for an accumulator
  (RSA/bilinear, or lattice for PQ); add a Lean non-membership lemma. The honest bound stays:
  revocation has a recency floor under partition (`REORIENT.md §2`, `OPEN-PROBLEMS.md`).
- **New vs rephrase.** Mostly **REPHRASE/DIAL** — better cryptographic shape for revocation dregg
  already does. Worth it for the *private + PQ* combination, not for novelty.

### 1.8 Post-quantum posture — the Pedersen/DH soft underbelly — **NEW (hardening)**, L

- **Capability unlocked / threat retired.** The STARK side is **already PQ** (hash-based,
  `pdfs/PATHB-pq-hashnative-track.md`). But the *commitment and signature* substrate is **not**:
  Pedersen value-commitments (`wasm/src/privacy.rs`, `sdk/src/committed_turn.rs`,
  `metatheory/Dregg2/Crypto/Pedersen.lean`), Ed25519 signatures everywhere (handoff, stealth,
  delegation), X25519 stealth DH (`cell/src/stealth.rs`), and the macaroon's DH-flavored 3P discharge
  all rest on discrete-log — **broken by a quantum adversary.** A "harvest-now-decrypt-later"
  attacker can *retroactively* de-anonymize stealth addresses and forge old delegations once a QC
  exists. For a *persistent* OS whose badges live forever, this is the gravest long-horizon hole.
- **Which face.** *All three* — Pedersen sits on EFFECTS (value conservation) + ATTESTATION
  (committed badges); Ed25519/stealth sit on AUTH.
- **§8 portal fit.** This is *the* argument for the portal discipline: because crypto is isolated
  behind `CryptoKernel.verify` and the `commit_hom` interface law (`CryptoKernel.lean`,
  `Pedersen.lean`), **the Lean laws do not change** when the primitive is swapped — only the portal
  instance does. The law proves "homomorphic-sum conserves"; the *instance* can be Pedersen *or* a
  lattice commitment. The PQ folding/PCS track is already studied (`pdfs/latticefold`,
  `latticefold-plus`, `greyhound-lattice-pcs`, `hachi-lattice-multilinear-pcs`, `neo-lattice-folding`).
- **What it would take.** (L) Replace Pedersen with a lattice/hash commitment with a homomorphic-sum
  interface; replace Ed25519 with a PQ signature (or hash-based for the non-aggregating paths);
  rebuild stealth on a PQ KEM. The anti-brick `AIR_VERSION` clause (`GLOSSARY.md:172`) is *exactly*
  the migration mechanism. This is a large but well-scoped portal-swap.
- **New vs rephrase.** **NEW capability (PQ posture)** delivered by **swapping portal instances** —
  the cleanest demonstration that the portal discipline pays off. *Surprising and load-bearing:* the
  most consequential dregg4 item here is not a feature but a **realization** — *the anonymity
  guarantees (stealth, nullifiers) are not PQ, so dregg's privacy story has a quantum expiry date the
  STARK story doesn't.* Flag for the shortlist.

### 1.9 Commit-reveal — **REPHRASE (mostly present)**, S

- **Capability.** Sealed-bid / hidden-then-revealed values. dregg **already has the pieces**: Pedersen
  committed escrow (`apply.rs:2049` CreateCommittedEscrow + range proof), `FieldVisibility::Committed`
  (`cell/src/state.rs`), and an app using it (`apps/gallery/src/private_vickrey.rs`). The commit phase
  is a side-table lock (C9, `EFFECT-ISA-DESIGN.md §5`); reveal is a settle with an opening predicate (C10).
- **Which face.** EFFECTS (the committed value) + disclosure dial (Committed→opened).
- **§8 fit / cost.** Already wired. (S) The only *new* thing worth adding is making reveal
  **non-interactive/self-opening via VDF** (§1.2) so it needs no honest reveal phase.
- **New vs rephrase.** **REPHRASE.** Listed for completeness — its value is as the *consumer* of
  §1.2 (VDF reveal), not as a standalone build.

### 1.10 Verifiable shuffles — **NEW**, M

- **Capability unlocked.** A proof that an output list is a permutation of an input list under
  re-randomization, revealing nothing about the permutation. Unlocks **mix-net turns** (a turn that
  shuffles a batch of commitments — anonymous payments, anonymous voting tallies), **fair ordering /
  anti-MEV batch turns**, and **anonymous credential re-issuance**. Pairs with the mixnet line
  (`pdfs/sphinx-...`, `loopix-...`, `riposte-...`, `vuvuzela-...`).
- **Which face.** EFFECTS (a batch state-transition that permutes) + ATTESTATION (the shuffle proof
  is the badge) + disclosure dial (the permutation is hidden).
- **§8 portal fit.** Clean: a shuffle argument is a `Verify`. It fits the JointTurn/forest layer —
  a shuffle turn is a *many-input many-output* turn, structurally a `BoundDelta` batch.
- **What it would take.** (M) A shuffle-argument circuit (Bayer-Groth-style or a STARK shuffle) as a
  CORE-or-DSL turn, with the permutation as private witness. Anti-MEV ordering pairs it with §1.2 VDF.
- **New vs rephrase.** **NEW.** Nothing in dregg permutes a batch privately today.

### 1.11 Private set intersection for cross-cell interaction — **NEW**, M–L

- **Capability unlocked.** Two cells learn the intersection of private sets (or just its size /
  a predicate over it) without revealing the rest. Unlocks **privacy-preserving matchmaking / intent
  matching** (do two intents overlap without revealing the orders?), **contact discovery between
  vats**, **compliance checks** ("is this counterparty on my blocklist?" without revealing either
  list), and **private auctions/markets**.
- **Which face.** Spans AUTH (a turn admissible iff intersection-predicate holds) and the EFFECTS of
  a JointTurn (the intersection result drives the post-state). It is the **privacy lift of the intent
  `∃P` matcher** (`GLOSSARY.md:99`, `LEARNINGS-intent-matching.md`): today the matcher finds a fill
  over *cleartext* facts; PSI lets it match over *private* facts.
- **§8 portal fit.** Trickier — PSI is interactive or uses oblivious primitives (OPRF). The portal
  carries the PSI proof; but the *protocol* is a multi-round interaction, so it lands in the
  choreography/protocol-cell layer (`GLOSSARY.md:136`) more than the single-turn law. The verify/find
  seam still applies: *finding* the intersection is the untrusted protocol; *verifying* the claimed
  intersection (e.g. via a STARK over committed sets) is the gate.
- **What it would take.** (M) Circuit-based PSI (prove "x ∈ both committed sets") for the
  small-set / verify-only case — fits a single turn. (L) Full interactive PSI for large sets — needs
  the protocol-cell choreography + OPRF portal. Recommend the circuit-based form first.
- **New vs rephrase.** **NEW.** *Surprising:* PSI reframes **intent matching as a privacy problem**,
  not just a search problem — the matcher (already an untrusted soundness-only plugin) becomes a
  *private* matcher with no change to its trust status. dregg's verify/find seam was *built for this*.

### 1.12 — additions the toolbox implies that the prompt didn't list (galaxy-brain)

- **Distributed key generation (DKG) for sovereign committee cells — NEW, L.** A collective cell
  needs its threshold key born without a trusted dealer. DKG is the *genesis* of a §1.1 threshold
  cell; it is a multi-round choreography (protocol-cell). Pairs with `dyna-hints` dynamic committees.
- **Proactive secret resharing / key rotation — NEW, M.** A long-lived sovereign cell must rotate
  its threshold shares as membership churns *without* changing its identity (the cell's `Obs` head
  stays stable while the key reshares). This is the *cell-lifecycle* meaning of forward secrecy.
- **Forward-secret / puncturable attestation — NEW, M.** Because badges are persistent
  (`GROUND-AUTH §2.1`), a leaked signing key today forges *past* badges. Puncturable/forward-secure
  signatures let a cell *prove a turn happened at epoch e* such that compromise at e+1 cannot forge
  epoch-e badges. Directly addresses the persistence threat that also drives §1.8.
- **Oblivious storage (ORAM) for the blinded queue — NEW, M.** `GROUND-STORAGE-PROGRAMS.md`'s
  `BlindedQueue` hides *contents*; ORAM (`pdfs/path-oram`, `oblivious-data-structures`) hides *access
  patterns* — which cell read which slot when. The metadata-private complement to the existing
  content-private queue. Fits as a storage-portal below the ISA.
- **Anonymous-but-rate-limited access (anonymous tokens / privacy-pass) — DIAL→NEW, S.** k-anonymous
  rate limiting via blind tokens (§1.6) + nullifiers (already present). Near-free given §1.6.
- **Verifiable encryption to a designated party (the dual of DVZK) — NEW, M.** Encrypt a witness
  under a verifier's key *with a proof it decrypts to a satisfying witness* — the missing piece for
  "I'll convince only you, *and* you can later open it on dispute." Bridges DVZK (§1.13) and
  group-sig opener (§1.5).

### 1.13 The named transferability gap (carried from GROUND-AUTH §2.4), for completeness — **NEW**, M–L

- **Designated-verifier ZK (DVZK)** — prove `(turn authorized) ∨ (I know V's sk)`; convincing only
  to V. **AUTH/ATTESTATION** + transferability dial → `designated`. (M) An OR-composition circuit over
  the existing presentation AIR + a Schnorr-knowledge clause. The keystone Lean move: make
  `Discharged` **verifier-indexed** (today a single universal predicate — *the* reason the model
  cannot even express "convincing only to V", `GROUND-AUTH §2.4`).
- **Deniable interactive authentication** — SIGMA/OTR-style on the captp channel
  (`captp/src/handoff.rs`); the recipient is convinced live but holds no transferable transcript.
  Transferability dial → `deniable`. (M–L, interactive). The *introducer* signature stays
  non-repudiable; only the *presentation* becomes deniable.

---

## 2. Cross-cutting galaxy-brain rethinks (the structure, not the primitives)

1. **The third dial: quorum/time/condition.** The biggest reframe. dregg has a *disclosure* dial and
   a (pinned) *transferability* dial. Threshold (§1.1), time-lock/VDF (§1.2), witness-encryption
   (§1.3), commit-reveal (§1.9), and PSI (§1.11) are *all* values of a third axis — **the
   admissibility-condition dial** on the AUTH face: `condition ∈ {logic, proof, await, threshold,
   time/VDF, witness-decrypt, set-predicate}`. dregg already has the seed: the `WitnessedCondition`
   engine (Datalog | STARK | Await, `GLOSSARY.md:84`). **dregg4 = three faces, three dials.** This
   single move turns ~6 menu items from "features to bolt on" into "engines to register" — the same
   way the await family unified four superficially-different awaits into one `Resolver` inductive.

2. **The portal discipline *is* the crypto-agility theorem.** §1.8 (PQ) is the proof: because every
   primitive is `CryptoKernel.verify` behind the `commit_hom`/Verify interface, swapping Pedersen→
   lattice, Ed25519→PQ-sig, or adding threshold/ring/blind *changes only the portal instance and the
   anti-brick `AIR_VERSION` pin* — never a Lean law. dregg4's defensible headline isn't any single
   primitive; it's that **the whole menu is portal-pluggable by construction**, which almost no
   verified system can claim. The carry-forward synthesis's "small core + DSL userspace" shape
   (`§3`) extends to crypto: *small Verify interface + pluggable primitive instances*.

3. **The verify/find seam was built for private search.** PSI (§1.11) and witness-encryption (§1.3)
   reveal that dregg's untrusted-solver/trusted-verifier seam (`cand-B`, `discoveries.md §1`) is
   *already* the right shape for privacy: the *finder* (matcher, decryptor, intersector) can be
   private/untrusted because only the *verifier's accept* is trusted. Privacy-preserving search adds
   *zero* TCB. This is a genuine "we already have the bones" insight, not a rephrase of a feature.

4. **MPC = secret-shared JointTurn.** §1.1's deepest point: the cross-cell tensor dregg *must* build
   for atomic multi-cell commit (`νF₁⊗νF₂` non-final, CG-2⊗CG-5 binding, `study-category.md`,
   `JointTurn.lean`) becomes a general MPC turn the moment per-cell witnesses are secret-shared. The
   hardest existing theory obligation (cross-cell binding) is *one layer* from the most general
   primitive (MPC). Surprising and high-leverage.

5. **Persistence is the adversary the crypto menu actually answers.** dregg is a *persistent* OS:
   badges live forever (`REORIENT §0`). That makes three otherwise-niche items *load-bearing*: PQ
   posture (§1.8 — old badges must not become forgeable/de-anonymizable), forward-secret attestation
   (§1.12 — key leak must not forge the past), and private folding (§1.4 — a forever-growing history
   must compress and hide). The time dimension is what elevates these above "nice to have."

---

## 3. Ranked shortlist — value × feasibility

Score = rough value (capability impact on the Mg Vision) × feasibility (inverse effort), with the
"already have the bones" bonus. Top tier first.

| # | Item | Face / dial | New? | Effort | Why it ranks |
|---|---|---|---|---|---|
| **1** | **The third dial (condition algebra) + register VDF/time-lock as an engine** (§2.1, §1.2) | AUTH / new condition dial | NEW (frame) + NEW (VDF) | M | Unifies 6 items into one architectural move; VDF is the cheapest concrete payoff (self-opening auctions, beacons, anti-MEV). Highest leverage per unit work. |
| **2** | **Threshold (FROST/silent) auth mode + Coconut blind-threshold credentials** (§1.1, §1.6) | AUTH / quorum dial | DIAL→NEW | M | Unlocks collective sovereign cells (DAOs/committees) — a whole *class* of dregg apps. Blind+threshold collapse into one build via Coconut. Verifies as one signature at the portal. |
| **3** | **Ring/group signatures (the deniability gap)** (§1.5, §1.13 DVZK) | ATTESTATION / transferability dial | NEW | M | Closes the *named* hole; ring is the cheapest repudiation (reuses the BlindedSet anonymity-set commitment). Verifier-indexed `Discharged` is the keystone Lean move. |
| **4** | **Private folding / ZK-IVC over the proof-forest** (§1.4) | ATTESTATION × disclosure | NEW | L | The galaxy-brain crown: a cell's entire verified history = one private succinct badge; makes "checkpoint/replay are theorems" maximally strong. Rides the existing `RecursionBackend`/accumulation track. |
| **5** | **PQ portal swap (Pedersen/Ed25519/stealth → lattice/PQ)** (§1.8) | all faces | NEW (posture) | L | The persistence-defining hardening; demonstrates the portal = crypto-agility theorem. Large but well-scoped; the lattice-folding/PCS reading is already done. |
| **6** | **Blind signatures / anonymous rate-limited tokens** (§1.6, §1.12) | AUTH | DIAL→NEW | S–M | Nearly free if BBS+/Coconut is adopted for the selective-disclosure credential work the carry-forward already mandates. |
| **7** | **PSI for private intent matching** (§1.11) | AUTH × EFFECTS | NEW | M–L | Reframes matching as privacy; adds zero TCB (verify/find seam). Circuit-based small-set form first. |
| **8** | **Verifiable shuffle (mix-net turns)** (§1.10) | EFFECTS × disclosure | NEW | M | Anonymous payments/voting + anti-MEV; pairs with VDF ordering. |
| **9** | **Witness encryption (STARK-derived extractable form)** (§1.3) | AUTH × EFFECTS | NEW | M (approx) / L (general) | Conditional cap handoff with no online issuer; philosophically native to "the witness is truth," but general WE is research-grade — ship the STARK-KDF approximation. |
| **10** | **Accumulator revocation + forward-secret attestation + ORAM blinded queue** (§1.7, §1.12) | AUTH / storage | DIAL / NEW | S–M each | Refinements of existing mechanisms; do alongside the credential and storage reconciliation, not standalone. |

**Most-promising (build-soon) shortlist:** #1 (condition dial + VDF), #2 (threshold/Coconut),
#3 (ring + DVZK — closes the named gap). These three are M-effort, high-value, and each turns an
existing seed (WitnessedCondition engine; AuthMode dispatch; BlindedSet commitment) into a new dial
value — the carry-forward-faithful way to grow.

**Most-surprising flags (the non-obvious truths):**

- 🟣 **MPC is one secret-sharing layer from the JointTurn dregg already must build.** The hardest
  open theory obligation (`νF⊗νF` non-final cross-cell binding) is the *substrate* for the most
  general primitive. (§1.1, §2.4)
- 🟣 **dregg's privacy has a quantum expiry date its proofs don't.** The STARK is PQ; stealth,
  nullifiers, Pedersen and Ed25519 are *not* — so a persistent OS's anonymity can be *retroactively*
  broken, while its validity cannot. The asymmetry is the real PQ story. (§1.8, §2.5)
- 🟣 **The verify/find seam is a privacy engine, not just a soundness engine.** Private search (PSI,
  witness-encryption, private matching) adds *zero* TCB because only the verifier's accept is
  trusted — dregg built the right shape for privacy before it knew it. (§1.3, §1.11, §2.3)
- 🟣 **Witness-encryption is philosophically native:** a system whose unit of truth is "a valid
  witness" already believes "the witness *is* the key." (§1.3)
- 🟣 **A cell's whole life can be one private badge.** Private folding makes the strongest form of
  checkpoint-as-theorem real: O(1) zero-knowledge proof of an unbounded verified history. (§1.4)

---

## 4. What is genuinely NEW vs a rephrasing (the honest ledger)

- **Genuinely-new capabilities** (cannot be expressed today): threshold/anonymous-k-of-n & MPC turns
  (§1.1), time-lock/VDF turns (§1.2), witness encryption (§1.3), private folding (§1.4), ring/group
  signatures & DVZK & deniable auth (§1.5, §1.13), PQ posture (§1.8), verifiable shuffles (§1.10),
  PSI (§1.11), DKG/resharing/forward-secret attestation/ORAM (§1.12).
- **New values of an existing dial** (slot exists, value is new): blind-signature issuance (§1.6 —
  the Token slot exists), single-signer threshold (§1.1 — the condition slot exists).
- **Rephrasings of what exists** (listed only for completeness / as consumers): commit-reveal (§1.9 —
  committed escrow + `private_vickrey` already do it; its value is as the *consumer* of VDF reveal),
  accumulator revocation (§1.7 — a better-shaped version of the nullifier-G-Set revocation dregg
  already has).
- **A frame, not a feature** (the most valuable single item): the **third dial / condition algebra**
  (§2.1) and the **portal-as-crypto-agility-theorem** observation (§2.2) — these reorganize the menu
  rather than add to it, and are what would actually *define* dregg4.

---

```
( ⌐■_■ )  three faces, three dials, one verify —
          the menu is long, but the kernel stays small:
          every primitive a portal swaps in,
          and the law never learns a single secret at all.   🐉🥚
```
