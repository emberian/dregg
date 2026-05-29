# LEARNINGS — Keys-as-caps, proof-carrying auth & schema evolution

> Axis: keys-as-caps · proof-carrying auth · schema evolution. Grounded in the six PDFs named
> below + `docs/rebuild/00-synthesis.md`. Tags: **[G]** = grounded in a paper/synthesis §/code
> coordinate; **[F]** = forward design (mine, extrapolated). Honest about where the mapping is
> tight vs. aspirational.

## Papers read

1. **`proof-carrying-authentication-appel-felten.pdf`** (PCA, Princeton 1999) — authentication
   frameworks (Taos, SPKI/SDSI, X.509) *all expressible in one higher-order logic*; the verifier
   checks a **proof**, not an ACL. Logic is **undecidable**, but **proof-checking is simple**;
   burden of proof is on the requester.
2. **`intro-to-proof-carrying-authorization-garg.pdf`** (Garg lecture notes, 2007) — accessible
   PCA over **first-order intuitionistic / indexed lax logic** with a `K says A` modality;
   judgments `P ⟹ M : A` carry a **proof-term `M`** (a literal certificate); the "irony": the
   requester reasons cheaply why it has access, the monitor cannot — so ship the proof.
3. **`macaroons.pdf`** (Birgisson/Politz/Erlingsson et al., NDSS 2014) — bearer tokens =
   **nested chained HMACs**; **first-party caveats** = predicates the target checks against
   request context; **third-party caveats** = required **holder-of-key discharge proofs** from a
   named gateway; `bindForRequest` seals discharges to the root macaroon; formalized in Abadi
   `says`-logic. Disadvantage stated outright: **verifiable only by the target service** (shared
   secret), unlike public-key PCA.
4. **`ucan-spec.pdf`** (UCAN v1.0.0-rc.1) — **DID-rooted, self-certifying capability chains**;
   no Authorization Server (the resource *is* the RS); `iss→aud` delegation with attenuation
   down the chain; proofs = "positive evidence (witnesses)"; explicitly **PC/EL** (partition-
   tolerant, eventually-consistent), **no confinement**, revocation as "last resort."
5. **`preserves-spec.pdf`** (Garnock-Jones, 2025) — a **data model** (not a syntax): Records
   (user-defined label + fields), Sequences, **Sets**, Dictionaries, atoms, **Embeddeds**
   (capabilities / stateful refs); a **total order defined on the data model**, not on bytes →
   **canonical encoding** → content-addressing for free; **annotations** carry provenance
   separately from data.
6. **`safe-on-the-fly-relational-schema-evolution.pdf`** (SQLite, SPJR+versions calculus) —
   **lazy, per-tuple-versioned** migration: `UPDATEDB(new_schema)` returns immediately; old
   (ν=1) and new (ν=2) tuples coexist; a function **`z()`** migrates-on-read; **Theorem 3.1**:
   `erase(⟦Q⟧(z(I))) = erase(⟦Q⟧(I²))` — querying a lazily-migrated DB is **indistinguishable**
   from one created entirely at v2. **No downtime, provably transparent.**

---

## Key ideas (attributed)

- **[G, Appel-Felten]** *Authorization is provability in a logic.* "Because our logic has no
  decision procedure — although proof checking is simple — users must submit proofs with their
  requests." A principal is *the set of formulas it admits*; `K signed S`, `keybind(k,p)`,
  `p controls S` (= `p(S)→S`) are the primitive operators; ACL membership becomes a *lemma*.
  Different frameworks (SPKI, Taos) become *application-specific definitions proved as lemmas
  over one inference kernel* → they **interoperate** ("combine a theorem proved with SPKI defs
  and one proved with Taos defs to convince a server that has seen neither"). **This is exactly
  composable auth.**
- **[G, Appel-Felten]** *The decidability split is the architecture.* A simple decidable logic
  makes meta-theorems easy ("there's no way Alice can read bar") but is too weak; higher-order
  (quantify over predicates) is expressive but undecidable. PCA resolves it by **moving search to
  the prover and keeping only checking in the TCB**.
- **[G, Garg]** *Generic reference-monitor inference is intractable* (propositional = NP-complete;
  their lax logic undecidable, a useful fragment ≥PSPACE). *Proof-checking is linear in proof
  size.* The `says` modality + `affirms` judgment localize trust: `ACM says canDownload(Alice)`
  is what Alice must witness; "no obligation to establish it to any other principal."
- **[G, Macaroons]** *Two caveat species.* **First-party** = `predicate(request-context)` checked
  locally by the target. **Third-party** = `cav@Location⟨cId, vId⟩`: an obligation discharged by
  presenting a **separate discharge macaroon** minted by the named third party after *it* checks
  its own predicate. The caveat carries an encrypted root key two ways: `cId` (for the third
  party) and `vId` (for the target to verify). **Discharge is recursive** (discharge macaroons can
  carry their own third-party caveats). `bindForRequest` = `H(M'.sig :: M.sig)` seals each
  discharge to *this* authorizing macaroon → prevents replay/re-use across requests.
- **[G, Macaroons]** *Revocation is the known weak point*, addressed only by (i) short lifetimes,
  (ii) freshness caveats, (iii) external revocation-list/epoch state, (iv) split-and-recollect.
  No native revocation; a third-party caveat *to a revocation-checking service* is the idiom.
- **[G, UCAN]** *Self-certifying delegation + reference passing ⇒ inversion of control*: the
  resource grants authority directly, no AS mediates. The **delegation chain is by definition a
  provenance log.** Movie-ticket analogy: *who you are is irrelevant; possession is authority* —
  this is **keys-as-caps stated plainly**. Cost: "a valid chain can be semantically invalid;
  the Executor MUST verify ownership of external resources at execution time"; **no confinement**
  (can't know all sub-delegations); revocation is a last resort needing unique IDs + sharing.
- **[G, Preserves]** *Meaning is independent of syntax; comparison is defined on the data model.*
  Records are **labelled tuples** (label usually a Symbol); Sets are **canonicalized by sorting
  elements under the total order**; Dictionaries by sorted key-pairs. Therefore **two values are
  equal iff their canonical encodings are** → `hash(canonical(value))` is a stable content
  address that *does not depend on field/insertion order or implementation*. **Embeddeds** are a
  first-class escape hatch for capabilities ("object capabilities, file descriptors, … rewritten
  at network and process boundaries"). **Annotations** separate provenance/trace from data.
- **[G, Schema-evolution]** *Lazy versioned migration with a safety gate.* Each tuple carries a
  version ν; `z()` is the migration adapter run on read; a query that touches un-migrated tuples
  in the changed region (`R∆`) is migrated first, else answered directly. Theorem 3.1 proves the
  client cannot tell a lazily-migrated DB from a fully-v2 one. Control returns in <400ms; full
  speed after background sweep completes.

---

## Takeaways for dregg (idea → move)

| # | Paper idea | dregg move | Maps to |
|---|---|---|---|
| T1 **[G→F]** | PCA: verifier checks a proof, not an ACL | **auth-in-proof**: STARK PI attests "actor was permitted" — the membrane is a PCA reference monitor whose proof-language is the STARK statement | synthesis §5.3, §0; `authorize.rs`, `binding.rs:8-12` |
| T2 **[G]** | Search undecidable / checking cheap | This *is* the synthesis VERIFY/FIND seam (§3.2). PCA names it canonically: **prover does search, TCB does linear check**. The deferred-prover IS the requester-side proof constructor | synthesis §3.2, §6 keystone |
| T3 **[G]** | Garg `says` modality + per-principal policy | The permission-lattice (`spec_eval`) + `Authorization` coproduct are dregg's `says`/`controls`; encode them as the **authorization-logic fragment** the STARK enforces | synthesis §5.1; `turn/src/action.rs:206` |
| T4 **[G]** | Macaroon 3rd-party caveat = discharge | Already isomorphic to `ConditionalTurn`; fold **discharge in as the `Await` engine** of `WitnessedCondition` | synthesis §3.1, §3.2 (discharge row), §3.3(4) |
| T5 **[G]** | Macaroon `bindForRequest` seals discharge to root | The **intent-seal AEAD** (commit `6cccd276`) + binding-site (`AuthRequest`, `when=block_height`) are dregg's `bindForRequest`; ensure await-resolutions are bound to the *specific* turn, not replayable | synthesis §3.1 BindingSite; recent commits |
| T6 **[G→F]** | Macaroon ID-range `CaveatType` registry | Synthesis already notes `Custom{vk_hash}` predicate-registry is *modeled on* this; make it a **content-addressed registry** (AIR-id = hash, §Schema below) | synthesis §3.1 note; `cell/src/predicate.rs` |
| T7 **[G]** | UCAN: chain = provenance log; PC/EL | Direct match to **liquid-first + receipt-chain-as-truth**; UCAN is the keys-as-caps export format of the within-boundary log | synthesis §2.4, §2.2 |
| T8 **[G]** | UCAN attenuation down chain | The **caps↔keys functor** below; unify `Breadstuff`/`Token`/`Bearer` attenuation into one order relation | synthesis §5.2 (merge cap reps) |
| T9 **[G]** | Preserves canonical Record/Set + content-address | **Cell-state = schema-typed Record; facet = canonical Set of effect-symbols; AIR-id = hash(canonical schema)** — closes EffectMask bit-fragility AND frozen-AIR | synthesis §5.2 (8-slots→content-addressed), §6.7 |
| T10 **[G]** | Schema-evolution: per-tuple version + `z()` + Thm 3.1 | **Typed old→new migration with no downtime**; pair with linear-drop (below) | synthesis §5.2 (typed-schema-upgrade), houyhnhnm |
| T11 **[G]** | Preserves Embedded = capability ref | Cell-state Records embed **capabilities as Embeddeds**, "rewritten at network/process boundaries" — exactly the **caps→keys conversion at the membrane** (§2.2) | synthesis §2.2 conversion point |
| T12 **[F]** | Garg "no obligation to other principals" | Per-membrane local verification: each boundary checks only the proof for *its* policy — supports the **per-cell phase** model, no global ACL | synthesis §2.1, §4 |

**Lean hooks [F]:** the metatheory's item-3 "two authority models + lossy morphism" (synthesis §8)
gets concrete content from this axis: positional-caps = a category where authority is a *slot*
(no admissible-formula set); epistemic-keys = the Appel-Felten "principal = set of formulas it
admits" / UCAN DID-chain. The **membrane law** (§8 item-4: within-root needs no witness, crossing
needs the `Predicate⊣Witness` witness side) is *literally* the PCA reference-monitor boundary —
inside a trust root the monitor is the live mediator (caps-as-caps); across it, the requester
must **carry a proof** (keys-as-caps). PCA is the existing-literature grounding for that theorem.

---

## The caps↔keys functor (what's preserved / lost)

**Statement [F, grounded in synthesis §2.2 + UCAN + Macaroons]:** there is a structure-forgetting
functor `Φ : Caps → Keys` from positional capabilities to epistemic credentials. A key/token IS
an attenuated capability: `Φ(positional-cap) = signed/HMACed certificate carrying the attenuation
as caveats`. UCAN's `iss→aud` delegation and macaroon caveat-chaining are both the *image* of cap
delegation under Φ.

**Preserved by Φ:**
- **Attenuation as a monotone order.** Macaroon "add a caveat" and UCAN "sub-delegate with less"
  are *strictly downward* in the authority lattice — same partial order as cap diminish. The
  HMAC chain / signature chain *enforces monotonicity cryptographically* (you can only add
  caveats; you can't strip them without the root key). **[G, Macaroons §III; UCAN PoLA]**
- **Composition / chaining** (delegation chains compose; discharge nests recursively). **[G]**
- **Unforgeability** — but the *source* changes: caps-as-caps unforgeable **by construction**
  (mediator/CDT/slot); keys-as-caps unforgeable **by cryptography** (HMAC/signature/proof). **[G]**
- **Provenance** — Φ actually *adds* it: the chain is a provenance log (UCAN), absent in a bare
  positional cap. **[G]**

**Lost by Φ (the principled-lossy conversion of synthesis §2.2):**
- **The mediator's structural guarantee.** A positional cap can't be *copied* (no secret to copy);
  a key can be *freely copied* — possession ≠ exclusive. **[G, synthesis §2.2]**
- **Confinement.** "UCANs do not offer confinement … impossible to guarantee knowledge of all
  sub-delegations." caps-as-caps under a mediator *can* confine (seL4 CDT enumerable). **[G, UCAN]**
- **Cheap revocation.** Positional: drop the slot, done. Keys: needs external state / short TTL /
  re-collection (macaroon's four strategies; UCAN "last resort"). **[G, both]**
- **Liveness of mediation** (near vs far). The mediator can *interpose* per-invocation (revoke
  mid-session, rate-limit, log); a bearer credential is checked only when presented. **[G]**

**Inverse `Φ⁻¹ : Keys → Caps` needs a trusted minter** to re-establish a mediator (synthesis §2.2:
"keys→caps needs a trusted minter"). So Φ is **not an isomorphism** — it has a left-inverse only
on mediator islands (seL4 kernel, live CapTP session, trusted host). This is the precise content
of the synthesis "membrane is the caps↔keys conversion point, principled-lossy."

**What proof-carrying auth recovers (the partial section-5 answer):** PCA/STARK auth-in-proof
*recovers composability and offline-verifiability that bearer-HMAC loses* (macaroon's stated
flaw: "verifiable only by the target service"). A STARK/PCA credential is **publicly verifiable**
(like UCAN's public-key chains, unlike macaroon's shared-secret) AND can attest *richer* predicates
than a signature chain (arbitrary in-circuit policy, not just caveat conjunction). It does **not**
recover revocation, confinement, or interposition — those need a live mediator (the Tier-1 liquid
interior) or external revocation state.

---

## Auth-in-proof: concrete encoding [F, grounded in §5.3 + PCA + Garg]

The move (synthesis §5.3): compose `auth-AIR (schnorr/native_signature) + permission-lattice
(spec_eval) + EffectVM` into one statement whose **public input is the committed authorized turn**.
PCA tells us *what shape the statement should be*:

```
Public input  PI = H( actor_principal ‖ resource_cell_id ‖ effects_root ‖
                       prev_receipt_hash ‖ block_height ‖ policy_air_id )
Statement (∃ witness w):
  1. KEY/IDENTITY    : w binds actor_principal to a key       (schnorr_air / DID)   -- "K signed"
  2. DELEGATION      : a chain w.chain attenuates root→actor   (monotone caveat order) -- keybind/says
  3. POLICY ENTAILMENT: policy(air_id) ⊢ actor controls effects (spec_eval; the lattice) -- "controls_e"
  4. EFFECT BINDING  : EffectVM(w.actions) folds to effects_root                      -- conservation
  5. REPLAY          : prev_receipt_hash chains; block_height fresh                   -- freshness caveat
```

- **PCA correspondence [G]:** step 3 is `controls_e` (`p controls S ∧ p(S) ⊢ S`); step 2 is the
  `keybind`/`says`-chain (`Kc signed keybind(Ka,Alice)`); the STARK is the **proof-term `M`** that
  the verifier (membrane) checks in linear time. Today only `(action,resource)` is bound and
  **auth/replay are excluded** (`binding.rs:8-12`) — i.e. dregg currently ships steps 4 partially
  and **omits 1–3,5 from the proof**, doing them in trusted `authorize.rs`. The recovery is to
  pull 1–3,5 *into PI*.
- **The logic/lattice to encode [G→F]:** the **authorization-logic fragment** is exactly Mina's
  permission lattice `None < Either < {Proof|Signature} < Impossible` + dregg's `Custom{vk_hash}`,
  read as Garg-style `says`: a slot's permission is "what principals the cell *admits* may write
  it." `spec_eval` (Mina's 3-bool in-circuit check) is the decidable *checker*; keep the search
  (which delegation path, which discharge) **outside the circuit** in the deferred-prover.
- **Decidability mirror [G]:** PCA's "checking simple, search undecidable" = synthesis VERIFY/FIND
  seam *one level up*. **In-circuit policy entailment must stay in a decidable/bounded fragment**
  (spec_eval is a fixed boolean circuit) — do NOT put the *matcher* (∃-fill, undecidable, §3.2) in
  the auth statement. Auth-in-proof verifies a *named* authorization; finding which authorization
  applies is the prover's (off-circuit, bounded) job — same discipline as RingSolver.
- **`policy_air_id` in PI [F]:** binds the proof to a *specific content-addressed policy schema*
  (next §). This is how PCA's "interoperate proofs from definitions a server never saw" becomes
  sound here: the verifier checks `policy_air_id == hash(its policy)` rather than re-deriving.

---

## Schema / Preserves: concrete cell-state & AIR-id shapes [G Preserves; F dregg mapping]

**Problem (synthesis §5.2):** 8 fixed slots (`Nat.N8`), bit-positional `EffectMask`, frozen
AIR/program → the "Urbit trap." Preserves fixes *both* with one idea: **identity = hash of the
canonical data-model value, not a byte/bit position.**

### Cell-state as schema-typed Record

```preserves
; cell state is a labelled Record; slots are NAME-KEYED, not positional
<cell-state @schema #x"<air-id>"          ; AIR-id = hash(canonical(schema-decl)); see below
  { balance:        1000                  ; Dictionary: Symbol key -> Value; order-independent
    owner:          #!<cap ...>           ; Embedded = a capability reference (caps→keys at membrane)
    nonce:          7
    rate-limit:     <bucket 100 60>       ; heterogeneous slots that DON'T fit 8xField today
    delegations:    #{ <del Ka read> <del Kb write> } }>  ; canonical Set
```

- **Why this closes frozen-AIR [G]:** the AIR-id is `hash(canonical(schema-declaration))`. A
  schema *is* a Preserves Value (the spec even gives schema-as-Value, "definitions match the JSON
  subset"); its canonical encoding is order-/impl-independent (total order on the data model), so
  **AIR-id is a stable content address**. Changing the schema → new AIR-id → a *different* program,
  explicitly migrated (next), never a silent reinterpretation of frozen slots.
- **Why this closes EffectMask fragility [G]:** an EffectMask is currently a bitfield (effect N =
  bit N — adding an effect renumbers everything). Replace with a **canonical Set of effect
  Symbols**:

### Facet as canonical Set of effect-symbols

```preserves
<facet
  grants: #{ read write transfer:limited }   ; Set of Symbols (+ Records for parameterized grants)
  on:     #!<cap cell-42> >
```

  Set membership/equality is by the data-model total order (Preserves sorts elements), so
  `#{read write}` ≡ `#{write read}` — **adding `transfer` adds an element, it does not shift bit
  positions**; two facets are equal iff their canonical-Set encodings are; `hash(canonical(facet))`
  is the facet's content-addressed identity (synthesis §5.2: "facet/interface identity =
  hash-of-canonicalized-description, not bit position"). **[G, Preserves Sets §; synthesis §5.2]**
- **Annotations for provenance [G→F]:** Preserves annotations separate metadata from data — use
  them for the receipt-chain / trace info (`prev_receipt_hash`, block_height) so the *committed
  state value* hashes identically regardless of provenance decoration.

### AIR-id derivation

```
air_id          = H( canonical_encode( schema_decl ) )    ; schema_decl is itself a Preserves Value
slot lookup     = by Symbol name in the Record/Dictionary  ; NOT by index 0..7
effect identity = H( canonical_encode( effect_symbol ) )   ; NOT bit position
facet identity  = H( canonical_encode( <facet grants:..> ) )
```

---

## Schema migration: typed, no-downtime, + linear-drop [G schema-paper; F dregg/houyhnhnm]

The schema-evolution paper gives the **operational recipe** and a **safety theorem** that transfer
directly to content-addressed cell-state:

- **Per-tuple/per-cell version tag → per-cell `@schema air-id`.** Old cells stay at `air-id₁`, new
  cells minted at `air-id₂`; **both coexist** (the paper's ν=1/ν=2). No global stop-the-world. **[G]**
- **`z()` = the typed migration adapter, run on read/turn.** When a cell at `air-id₁` is touched by
  a program expecting `air-id₂`, run `z` (the old→new transform) first, then the turn; cells in the
  unchanged region answer directly. This is **lazy migration**, control returns immediately. **[G]**
- **Theorem 3.1 transfers [G→F]:** `erase(⟦turn⟧(z(cell))) = erase(⟦turn⟧(cell@v2))` — a lazily-
  migrated cell is **indistinguishable** from one created at the new schema. For dregg the
  "indistinguishability" must hold *under hashing/commitment*: i.e. the migrated state-root must
  equal what a fresh-at-v2 cell would commit. This is the soundness obligation the migration AIR
  must prove (a small `migrate-air` whose PI is `(air-id₁, air-id₂, state_root₁, state_root₂)`).
- **Typed old→new [G+F]:** SMO study shows the real-world ops are dominated by **ADD COLUMN /
  DROP COLUMN** (≈73% combined) — i.e. add-named-slot / drop-named-slot. With name-keyed Records
  these are: ADD = insert `name: default`; DROP = the migration must **explicitly drop** the slot.
- **Pair with linear-drop (houyhnhnm "explicitly drop what you don't keep") [G synthesis; F]:**
  the conservation law (`LinearityClass`, `action.rs:698`, exhaustive no-default match) says a
  migration that *removes* a slot holding a linear resource is **unsound unless it conserves** —
  the dropped value must be accounted (burned/transferred/explicitly dropped), not silently
  vanished. So the `z` adapter for a DROP COLUMN over a linear slot must emit a **conservation
  obligation**: `migrate-air` proves `Σ(linear before) = Σ(linear after) + Σ(explicitly-dropped)`.
  **This is the join of the two papers:** schema-evolution gives *no-downtime lazy versioning*;
  linear-drop gives *soundness of what migration removes*. An upgrade is sound iff it is (a)
  transparent (Thm 3.1, commitment-equal) **and** (b) conservative (linear-drop accounted).

---

## Tensions & corrections

1. **Macaroon = shared-secret; dregg wants public verifiability.** [G] Macaroons are "verifiable
   only by the target service." dregg's membrane is often a *third party* (another cell/host), so
   the **bearer-HMAC construction does not transfer directly** — use the macaroon *structure*
   (caveat order, third-party-caveat=discharge, bindForRequest) but the *PCA/STARK or UCAN public-
   key* verification mechanism. The synthesis biscuit(Datalog)/macaroon split already keeps these
   as sibling engines (§3.1); don't collapse the *engines*, only the binding-site.
2. **UCAN "no confinement" vs dregg's seL4 ambition.** [G] UCAN explicitly cannot confine. dregg's
   §2.1 host/seL4 trust-root *is* a confinement mechanism — so dregg is **not pure keys-as-caps**;
   it's keys-between, caps-inside (§2.2). Correction to any reading that "proof-is-truth ⇒ pure
   UCAN": the mediator islands genuinely retain caps-as-caps confinement; auth-in-proof does not
   recover confinement, only verifiability.
3. **Decidability discipline must be enforced, not assumed.** [G] PCA/Garg warn generic inference
   is intractable. The risk for dregg auth-in-proof is putting *search* (delegation-path finding,
   ∃-fill matching) inside the circuit. Keep the **circuit a decidable checker** (spec_eval shape),
   search in the deferred-prover. This mirrors §3.2's "general matcher provably out of reach."
4. **Preserves total-order = canonicalization, but floats/embeddeds are subtle.** [G] Doubles use
   IEEE totalOrder; Embeddeds compare by *domain rules*. For content-addressed cell-state, **forbid
   Doubles in committed state** (NaN/-0 hazards) and **define how Embedded caps canonicalize** (by
   their content-address, not by live identity) before hashing — else AIR-id stability breaks.
5. **Schema paper assumes single linear v1→v2 step; dregg cells fork/merge.** [G paper says "single
   update for simplicity"; F] dregg needs *chained* AIR-ids (a DAG of schema versions) and must
   handle migration across a fork/merge (synthesis §6 hole). The paper's safety proof is for a
   linear chain; **extending Thm 3.1 to the schema-DAG is open** (below).
6. **"Chain valid but semantically invalid" (UCAN).** [G] A structurally-valid delegation/proof
   chain can still be wrong if the *root* didn't actually own the resource. Auth-in-proof must
   bind the proof to the **current committed cell-state-root**, not just the chain — i.e. step 6
   of the encoding (PI includes `resource_cell_id` + its root) is load-bearing, not optional.

---

## Open questions / what to read next

- **Q1 [F]:** Extend schema-evolution Thm 3.1 (linear chain) to the **schema-DAG with fork/merge**
  (synthesis §6). What is the migration analog of "merge = re-root iff every edge stays a monotone
  attenuation"? — read **`take-grant-protection-model.pdf`**, **`typed-access-matrix-model-sandhu.pdf`**
  for the attenuation/safety-decidability framing.
- **Q2:** Does putting the full delegation-chain check in-circuit blow up the STARK? Compare with
  **`anoncreds-from-ecdsa-2024-2010.pdf`** and **`did-vc-survey-2402.02455.pdf`** (in-circuit
  signature/credential-chain verification cost) and **`ucan-spec`** sub-specs (Delegation/Revocation).
- **Q3:** Revocation is the unrecovered loss. Read **`revocable-proof-systems.pdf`** and the
  synthesis's sorted-Merkle non-membership accumulator (§5.1) — can auth-in-proof include a
  `not_revoked` non-membership proof as a standing caveat (synthesis §6.5: "W3-F never checks
  not_revoked")? This is the concrete fix for the macaroon/UCAN revocation gap.
- **Q4 [F]:** Formalize Φ (caps→keys) and its left-inverse-only-on-islands as the Lean **lossy
  morphism** (synthesis §8 item-3). PCA's "principal = admissible-formula set" is the candidate
  semantics for the Keys side; positional slot for the Caps side. Read
  **`capability-myths-demolished.pdf`** (the UCAN-cited source) for the precise caps-vs-ACL-vs-keys
  distinctions before fixing the functor's signature.
- **Q5:** Preserves *Schema* language (separate doc, not in this PDF — only the data model is here).
  Fetch the Preserves schema spec to ground the `schema_decl`-as-Value claim and the canonical
  schema-declaration encoding that AIR-id hashes.
- **Q6:** Garg/Appel proof-*terms* are explicit certificates (`M`). Is the STARK proof the
  proof-term, or should dregg keep a *separate* lightweight proof-term (the delegation path) that
  the STARK merely *attests was checked*? (Bears on proof size + the "interoperate unseen
  definitions" property.) Read **`proof-carrying-authorization-system-bauer.pdf`** (the Grey system,
  cited by Garg) for an implemented PCA reference monitor.
