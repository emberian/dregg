# grain-verify's home — an architectural coordination note

**Status:** the cross-repo dep is REMOVED (breadstuffs references DreggNet zero times). The R2 end-to-end test's proper home is DreggNet — a coordination note for that lane.

## What happened

`grain-turn` (a **breadstuffs** workspace member) dev-depended on `grain-verify`, which
lives in the **DreggNet** repo (`~/dev/DreggNet/grain-verify`, path `../../DreggNet/grain-verify`).
This created three problems:

1. **breadstuffs was not self-contained** — you could not clone-and-build it, and it
   could never be CI-green standalone (the gauntlet's ~17s manifest fast-fail:
   `failed to read ~/dev/DreggNet/grain-verify/Cargo.toml`).
2. **Inverted dependency** — the *core* (breadstuffs) reached *up* into the *operated
   layer* (DreggNet). Layer-on-core is correct; core-on-layer is the inversion.
3. **Circular across repos** — `breadstuffs/grain-turn → DreggNet/grain-verify →
   breadstuffs/dregg-agent` (grain-verify path-deps `../../breadstuffs/dregg-agent`).

The coupling is real, not incidental: `grain-verify` *composes* `dregg_agent::verify_agent_run`
(a breadstuffs crate), and its own header says R3 (the whole-history STARK fold) "needs
grain turns minted as rotated EffectVM legs — **a breadstuffs-side build**" (which is what
`grain-turn` is). So `grain-verify` is deeply breadstuffs-coupled but lives in DreggNet.

## Short-term fix (landed, `b156b140f`)

`grain-verify` → **optional** dep behind a `grain-integration` feature (off by default);
`grain-turn/tests/kernel_turns.rs` gated on it. Default build pulls zero grain-verify
→ breadstuffs is standalone. The full R2 end-to-end test runs with
`cargo test -p grain-turn --features grain-integration` and `~/dev/DreggNet` present.

This unbreaks standalone CI **without touching DreggNet** (the other terminal's active lane).

## Proper fix (needs coordination — DO NOT do unilaterally)

The blast radius is small (one integration test), but the *home* of `grain-verify` is a
shared architectural call. Options, best-first:

- **(A) Move `grain-verify`'s core into breadstuffs.** The `GrainAttestation` /
  `GrainVerifyError` types + the R0–R3 verifiers (which compose `dregg-agent`) are
  core verification and belong beside the kernel. DreggNet then deps *down* into
  breadstuffs (correct direction), and the `grain-integration` feature-gate goes away.
  Cleanest, but moves a crate out of DreggNet — **coordinate with the DreggNet lane first**
  (grain-verify has active recent commits there: `cd3a7e3`, `0d50f05`, `7ac3bbf`).
- **(B) Move the test to DreggNet.** `kernel_turns.rs` is genuinely a cross-repo
  integration test (breadstuffs producer × DreggNet verifier); it could live in DreggNet
  where both halves are already deps. Keeps grain-verify in DreggNet; breadstuffs loses
  the test but stays standalone. Less clean (the producer's non-vacuity witness lives
  away from the producer).
- **(C) Status quo** — keep the feature-gate. Works, but leaves the inverted/circular
  dep latent and the R2 e2e test off by default in breadstuffs CI.

**Recommendation: (A)**, once coordinated — it corrects the dependency direction and
puts the grain attestation ladder where its `dregg-agent`/rotated-EffectVM coupling
already lives. Until then, (C) holds and CI is green.

## The broader question this surfaced

Is there *other* work sitting in DreggNet that's actually breadstuffs-core? The
`PATH-PRESERVE Phase 5b` refactor (rotation witness through the commit path) on
persvati's DreggNet checkout is adjacent to the same rotated-descriptor machinery.
Worth a joint pass with the DreggNet lane: what belongs in the core vs the operated layer.
