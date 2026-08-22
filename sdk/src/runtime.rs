//! Agent runtime: high-level orchestration of cipherclerk, ledger, and execution.
//!
//! The [`AgentRuntime`] ties together:
//! - An agent cipherclerk (identity + tokens)
//! - A local ledger (cell state)
//! - A turn executor (atomic execution)
//!
//! It provides the highest-level API for agent operations: execute effects,
//! spawn sub-agents with attenuated capabilities, and manage the local cell.

use std::sync::{Arc, Mutex, RwLock};

use dregg_cell::{Cell, CellId, Ledger, VerificationKey};
use dregg_token::{Attenuation, AuthToken, BiscuitToken, biscuit_auth};
use dregg_turn::{
    Action, Authorization, BudgetGate, BudgetSlice, CallForest, ComputronCosts, DelegationMode,
    Effect, TokenKeyRef, Turn, TurnExecutor, TurnReceipt, TurnResult, action::symbol,
};
use dregg_types::PublicKey;
use zeroize::Zeroizing;

use crate::cipherclerk::{AgentCipherclerk, HeldToken};
use crate::error::SdkError;
use crate::raw;
use crate::turns::TurnBuilder;

/// THE SWAP (FLIPPED DEFAULT) — the VERIFIED Lean executor is the authoritative state producer on
/// this runtime's execute paths BY DEFAULT (for the swap-safe covered set), with the Rust
/// `TurnExecutor` demoted to a parallel differential cross-check. Reads an opt-OUT:
/// `DREGG_LEAN_PRODUCER=0` (or `false`/`off`/`no`) falls back to the legacy Rust-producer path; any
/// other value (or unset) keeps the verified producer ON.
///
/// Mirrors `dregg_node::state::lean_producer_env_enabled` so the node and the SDK read the SAME
/// switch. Under the `no-lean-link` platform gate (wasm32/zkvm) this always returns `false`
/// (the producer path is not compiled in), so wasm/default consumers never link the Lean archive.
pub fn lean_producer_env_enabled() -> bool {
    #[cfg(not(feature = "no-lean-link"))]
    {
        !matches!(
            std::env::var("DREGG_LEAN_PRODUCER").ok().as_deref(),
            Some("0")
                | Some("false")
                | Some("FALSE")
                | Some("off")
                | Some("OFF")
                | Some("no")
                | Some("NO")
        )
    }
    #[cfg(feature = "no-lean-link")]
    {
        false
    }
}

/// Install the Lean-verified REAL ML-DSA verify core as `dregg_pq::ml_dsa_verify`'s accept/reject AUTHORITY
/// for THIS process — taking the `fips204` crate out of the SDK-hosted process's verify TCB.
///
/// `dregg_pq::ml_dsa_verify` is the process-global ML-DSA-65 verify behind the SDK-hosted surfaces the
/// crate-TCB audit flagged: the wire `SiloServer`'s token/revocation verify (`wire/src/server.rs` sites
/// V2/V3) and the SDK's own turn/captp receipt verifies. It routes through an install-time function pointer;
/// with the REAL core installed it takes its verdict from the extracted, full-byte `MlDsaVerifyReal.verifyCore`
/// (BRICK 8) and NEVER consults the `fips204` crate. Only the node installed it before — so an SDK-hosted
/// process (or starbridge-v2) was falling through to the crate at every verify. This is the SAME shared
/// install the node performs (`dregg_pq::install_verified_mldsa_verify_core`), injecting the two
/// `dregg-lean-ffi` archive symbols; it is idempotent and once-per-process.
///
/// Gated on `fips204_verify_real_core_available()`: install ONLY when the linked archive EXPORTS the real
/// core. Returns the outcome so callers / the running-binary gate can assert routing.
///
/// ⚑ `ExportAbsent` IS NOT A FALLBACK. This doc used to say a build without the export "keeps the
/// `fips204`-crate fallback (a valid FIPS-204 verify) rather than bricking verify". That has been
/// FALSE since `dregg-pq`'s audit gate went live: with no verified core installed,
/// `dregg_pq::ml_dsa_verify` REFUSES — `refuse_unaudited` → `process::abort()` — unless the operator
/// declared `DREGG_ALLOW_UNAUDITED_PQ=1`. The sentence was stale in the UNSAFE direction for a
/// reader: it told an operator that a stale archive costs them the Lean authority, when it actually
/// costs them the process. `mldsa_verify_disposition` (twin#13) is the authority on this.
///
/// ⚑ PREFER [`install_verified_pq_cores`]. This is the single-direction adapter; a call site that
/// picks directions one at a time is how the verify core came to be armed on a strictly narrower
/// path than a consumer could take. See that function's header.
pub fn install_verified_mldsa_verify_core() -> dregg_pq::MlDsaVerifyCoreInstall {
    dregg_pq::install_verified_mldsa_verify_core(
        dregg_lean_ffi::fips204_verify_real_core_available,
        |w| dregg_lean_ffi::shadow_fips204_verify_real(w).ok(),
    )
}

/// Install the Lean-verified REAL, FULL-BYTE ML-DSA-65 SIGN core as the PRODUCER behind the deployed
/// byte-level signer `dregg_pq::MlDsaKey::sign` / `ml_dsa_sign_from_seed` for THIS process — taking the
/// `fips204` crate out of the SDK-hosted process's SIGN TCB.
///
/// The sign-side twin of [`install_verified_mldsa_verify_core`], and it closes the SAME hole on the other
/// half: an SDK-hosted process does not sign in 'sdk/src` directly, but it signs TRANSITIVELY through the
/// dregg libraries it hosts — `captp/src/handoff.rs` (handoff receipts), `cell-crypto/src/capability_proof.rs`,
/// `token/src/revocation.rs`, and `turn/src/pq.rs` all reach `MlDsaKey`. Every one of those was crate-
/// authoritative here. With `dregg-pq's audit gate live, they are worse than crate-authoritative: the first
/// such sign ABORTS the process unless a verified core is installed.
///
/// Same shared install the node performs (`dregg_pq::install_verified_mldsa_sign_core_real`), injecting the
/// two `dregg-lean-ffi` archive symbols; idempotent and once-per-process.
///
/// WARNING: on the installed path the signer is DETERMINISTIC (`rnd = 0`, the FIPS 204 deterministic
/// variant — spec-valid), where the crate fallback is hedged/randomized.
///
/// Gated on `fips204_sign_real_core_available()`, and deliberately NOT fatal on `ExportAbsent` — unlike the
/// `drorb` dataplane (which asserts, because it is a single serving binary that always links the archive),
/// the SDK is also built for `no-lean-link` wasm/zkvm targets that have no archive to export from. Bricking
/// those is not the tradeoff here; the audit gate still refuses to SIGN unaudited at the point of use.
pub fn install_verified_mldsa_sign_core_real() -> dregg_pq::MlDsaSignCoreRealInstall {
    dregg_pq::install_verified_mldsa_sign_core_real(
        dregg_lean_ffi::fips204_sign_real_core_available,
        |w| dregg_lean_ffi::shadow_fips204_sign_real(w).ok(),
    )
}

/// Perform the once-per-process SIGN-core install at SDK agent-runtime startup, logging the outcome once.
fn ensure_verified_mldsa_sign_core_installed() {
    use dregg_pq::MlDsaSignCoreRealInstall as S;
    use std::sync::Once;
    static LOGGED: Once = Once::new();
    let outcome = install_verified_mldsa_sign_core_real();
    LOGGED.call_once(|| match outcome {
        S::Installed => tracing::info!(
            "ML-DSA sign: verified Lean REAL sign core installed at SDK agent-runtime startup — the \
             extracted full-byte `MlDsaSignReal.signCore` is now the PRODUCER behind \
             `dregg_pq::MlDsaKey::sign` for this process (captp handoff receipts, cell-crypto capability \
             proofs, token revocations, turn); the `fips204` crate is out of the SDK-hosted SIGN TCB. \
             Signing is now DETERMINISTIC (rnd=0, the FIPS 204 deterministic variant)."
        ),
        S::AlreadyInstalled => tracing::debug!(
            "ML-DSA sign: a verified Lean REAL sign core was already installed this process (install is \
             once-per-process) — the `fips204` crate remains out of the SDK-hosted SIGN TCB"
        ),
        S::ExportAbsent => tracing::warn!(
            "ML-DSA sign: the linked Lean archive does NOT export the real sign core \
             (`fips204_sign_real_core_available()` is false) — NO verified sign core is installed, so any \
             ML-DSA sign this process reaches will be REFUSED by dregg-pq's audit gate (process abort) \
             unless DREGG_ALLOW_UNAUDITED_PQ=1. Rebuild against a HEAD-matching archive to route sign \
             through Lean."
        ),
    });
}

/// Perform the once-per-process verify-core install at SDK agent-runtime startup, logging the outcome once.
/// Called from every [`AgentRuntime`] constructor so ANY SDK-hosted process routes its wire-silo +
/// turn/captp verifies through the Lean-verified core without the host having to remember to install.
fn ensure_verified_mldsa_verify_core_installed() {
    use dregg_pq::MlDsaVerifyCoreInstall as I;
    use std::sync::Once;
    static LOGGED: Once = Once::new();
    let outcome = install_verified_mldsa_verify_core();
    LOGGED.call_once(|| match outcome {
        I::Installed => tracing::info!(
            "ML-DSA verify: verified Lean core installed at SDK agent-runtime startup — the extracted \
             full-byte `MlDsaVerifyReal.verifyCore` is now `dregg_pq::ml_dsa_verify`'s accept/reject \
             authority for this process (wire silo + turn/captp verifies); the `fips204` crate is out of \
             the SDK-hosted verify TCB"
        ),
        I::AlreadyInstalled => tracing::debug!(
            "ML-DSA verify: a verified Lean core was already installed this process (install is \
             once-per-process) — the `fips204` crate remains out of the SDK-hosted verify TCB"
        ),
        I::ExportAbsent => tracing::warn!(
            "ML-DSA verify: the linked Lean archive does NOT export the real verify core \
             (`fips204_verify_real_core_available()` is false) — NO verified verify core is installed, \
             so any ML-DSA verify this process reaches will be REFUSED by dregg-pq's audit gate \
             (process abort) unless DREGG_ALLOW_UNAUDITED_PQ=1. This line used to say the verify \
             'falls back to the `fips204` crate (a valid FIPS-204 verify)'; that stopped being true \
             when the audit gate went live, and it is the sentence an operator would have acted on. \
             Rebuild against a HEAD-matching archive to route verify through Lean."
        ),
    });
}

/// Install the Lean-verified REAL, FULL-BYTE ML-KEM-768 ENCAPS core as the ciphertext+shared-secret
/// AUTHORITY behind `dregg_pq::ml_kem768_encaps` / `hybrid_kem::initiate` for THIS process — taking the
/// `ml-kem` crate out of the SDK-hosted process's KEM-encaps TCB.
///
/// The KEM-encaps twin of [`install_verified_mldsa_verify_core`] / [`install_verified_mldsa_sign_core_real`],
/// closing the LAST unrouted PQ surface for an SDK-hosted process. `sdk/src` does not KEM directly, but any
/// KEM op it hosts (the X-Wing / `X25519MLKEM768` session establishment its wire/transport layers reach, the
/// hybrid session combiners) routes through `dregg_pq::ml_kem768_encaps` — which, with `dregg-pq`'s audit
/// gate live, ABORTS the process on the first encaps unless a verified core is installed. Before this the SDK
/// installed verify + sign but NOT the KEM cores, so every SDK-hosted KEM op hit that gate and aborted
/// (fail-closed, but a real gap).
///
/// Same shared install the node / drorb dataplane performs
/// (`dregg_pq::install_verified_mlkem_encaps_core`), injecting the two `dregg-lean-ffi` archive symbols;
/// idempotent and once-per-process. The extracted core is `Dregg2.Crypto.MlKemEncaps.mlkemEncaps` (FIPS 203
/// Alg 16, full n=256 ring / NTT / real codec), NIST-ACVP-anchored (byte-exact on the 25 ML-KEM-768
/// encapDecap cases) — NOT the `ml-kem` crate.
///
/// Gated on `mlkem_encaps_real_core_available()`, and deliberately NOT fatal on `ExportAbsent` — exactly like
/// the sign twin above and for the same reason: unlike the `drorb` dataplane (a single serving binary that
/// always links the archive, so it asserts), the SDK is also built for `no-lean-link` wasm/zkvm targets that
/// have no archive to export from. Bricking those at construction is not the tradeoff; the audit gate still
/// refuses to run an unaudited KEM at the point of use (process abort unless `DREGG_ALLOW_UNAUDITED_PQ=1`).
pub fn install_verified_mlkem_encaps_core() -> dregg_pq::MlKemEncapsCoreInstall {
    dregg_pq::install_verified_mlkem_encaps_core(
        dregg_lean_ffi::mlkem_encaps_real_core_available,
        |w| dregg_lean_ffi::shadow_mlkem_encaps_real(w).ok(),
    )
}

/// Install the Lean-verified REAL, FULL-BYTE ML-KEM-768 DECAPS core as the shared-secret AUTHORITY behind
/// `dregg_pq::ml_kem768_decaps` / `HybridResponder::finish` for THIS process — taking the `ml-kem` crate out
/// of the SDK-hosted process's KEM-decaps TCB.
///
/// The decaps mirror of [`install_verified_mlkem_encaps_core`]; the other half the same SDK-hosted KEM
/// surface reaches. Same shared install the node / drorb dataplane performs
/// (`dregg_pq::install_verified_mlkem_decaps_core`), injecting the two `dregg-lean-ffi` archive symbols;
/// idempotent and once-per-process. The extracted core is `Dregg2.Crypto.MlKemDecaps.mlkemDecaps` (the full
/// FIPS 203 FO decaps pipeline with implicit reject), NIST-ACVP-anchored — NOT the `ml-kem` crate.
///
/// Gated on `mlkem_decaps_real_core_available()`, and deliberately NOT fatal on `ExportAbsent`, for the same
/// `no-lean-link` reason as its encaps twin. A stale archive lacking the export would make an installed core
/// return `None` on every call, and `HybridResponder::finish` / `ml_kem768_decaps` fail CLOSED on a core
/// fault — so keeping the export-gated install (fallback preserved off-archive) is what avoids bricking
/// decaps on wasm/zkvm; the audit gate still refuses the unaudited decaps at the point of use.
pub fn install_verified_mlkem_decaps_core() -> dregg_pq::MlKemDecapsCoreInstall {
    dregg_pq::install_verified_mlkem_decaps_core(
        dregg_lean_ffi::mlkem_decaps_real_core_available,
        |w| dregg_lean_ffi::shadow_mlkem_decaps_real(w).ok(),
    )
}

/// Install the Lean-verified REAL, FULL-BYTE ML-KEM-768 KEYGEN core as the keypair AUTHORITY behind
/// `dregg_pq::ml_kem768_keygen` for THIS process -- taking the `ml-kem` crate out of the SDK-hosted process's
/// KEM-keygen TCB. The keygen mirror of [`install_verified_mlkem_encaps_core`] /
/// [`install_verified_mlkem_decaps_core`]. The extracted core is `Dregg2.Crypto.MlKemKeygen.mlkemKeygen`
/// (deterministic FIPS 203 ML-KEM.KeyGen_internal), NIST-ACVP-anchored (KAT, the byte<->ring refinement is
/// OPEN) -- NOT the `ml-kem` crate.
///
/// Gated on `mlkem_keygen_real_core_available()`, and deliberately NOT fatal on `ExportAbsent` -- like the
/// encaps/decaps twins, for the `no-lean-link` wasm/zkvm targets. Unlike encaps/decaps (whose audit gate
/// ABORTS at the point of use), the keygen audit gate WARNS and proceeds on the crate; installing the
/// verified core here routes SDK-hosted keygen through the proven object instead.
pub fn install_verified_mlkem_keygen_core() -> dregg_pq::MlKemKeygenCoreInstall {
    dregg_pq::install_verified_mlkem_keygen_core(
        dregg_lean_ffi::mlkem_keygen_real_core_available,
        |w| dregg_lean_ffi::shadow_mlkem_keygen_real(w).ok(),
    )
}

/// Install the extracted, Lean-verified REAL ML-DSA-65 KEYGEN core as the expander behind
/// `dregg_pq::MlDsaKey::from_ed25519_seed` — so this SDK-hosted process mints its NODE IDENTITY key via
/// the proven `MlDsaKeygen.mldsaKeygenInternal` (deterministic FIPS 204 ML-DSA.KeyGen_internal), NIST-ACVP
/// -anchored (KAT, the byte<->ring refinement is OPEN) — NOT the `fips204` crate.
///
/// Gated on `mldsa_keygen_real_core_available()`, and deliberately NOT fatal on `ExportAbsent` — like the
/// ML-KEM keygen twin, for the `no-lean-link` wasm/zkvm targets. Installing the verified core here routes
/// SDK-hosted identity-key derivation through the proven object instead of the crate.
pub fn install_verified_mldsa_keygen_core_real() -> dregg_pq::MlDsaKeygenCoreRealInstall {
    dregg_pq::install_verified_mldsa_keygen_core_real(
        dregg_lean_ffi::mldsa_keygen_real_core_available,
        |w| dregg_lean_ffi::shadow_mldsa_keygen_real(w).ok(),
    )
}

/// Perform the once-per-process ML-KEM ENCAPS-core install at SDK agent-runtime startup, logging once.
fn ensure_verified_mlkem_encaps_core_installed() {
    use dregg_pq::MlKemEncapsCoreInstall as E;
    use std::sync::Once;
    static LOGGED: Once = Once::new();
    let outcome = install_verified_mlkem_encaps_core();
    LOGGED.call_once(|| match outcome {
        E::Installed => tracing::info!(
            "ML-KEM encaps: verified Lean REAL encaps core installed at SDK agent-runtime startup — the \
             extracted full-byte `MlKemEncaps.mlkemEncaps` is now the ciphertext+shared-secret AUTHORITY \
             behind `dregg_pq::ml_kem768_encaps` / hybrid `initiate` for this process; the `ml-kem` crate \
             is out of the SDK-hosted KEM-encaps TCB"
        ),
        E::AlreadyInstalled => tracing::debug!(
            "ML-KEM encaps: a verified Lean REAL encaps core was already installed this process (install is \
             once-per-process) — the `ml-kem` crate remains out of the SDK-hosted KEM-encaps TCB"
        ),
        E::ExportAbsent => tracing::warn!(
            "ML-KEM encaps: the linked Lean archive does NOT export the real encaps core \
             (`mlkem_encaps_real_core_available()` is false) — NO verified encaps core is installed, so any \
             ML-KEM encaps this process reaches will be REFUSED by dregg-pq's audit gate (process abort) \
             unless DREGG_ALLOW_UNAUDITED_PQ=1. Rebuild against a HEAD-matching archive to route encaps \
             through Lean."
        ),
    });
}

/// Perform the once-per-process ML-KEM KEYGEN-core install at SDK agent-runtime startup, logging once.
fn ensure_verified_mlkem_keygen_core_installed() {
    use dregg_pq::MlKemKeygenCoreInstall as K;
    use std::sync::Once;
    static LOGGED: Once = Once::new();
    let outcome = install_verified_mlkem_keygen_core();
    LOGGED.call_once(|| match outcome {
        K::Installed => tracing::info!(
            "ML-KEM keygen: verified Lean REAL keygen core installed at SDK agent-runtime startup - the \
             extracted deterministic FIPS 203 `MlKemKeygen.mlkemKeygen` (KAT-anchored) is now the keypair \
             AUTHORITY behind `dregg_pq::ml_kem768_keygen` for this process; the `ml-kem` crate is out of \
             the SDK-hosted KEM-keygen TCB"
        ),
        K::AlreadyInstalled => tracing::debug!(
            "ML-KEM keygen: a verified Lean REAL keygen core was already installed this process (install is \
             once-per-process) - the `ml-kem` crate remains out of the SDK-hosted KEM-keygen TCB"
        ),
        K::ExportAbsent => tracing::warn!(
            "ML-KEM keygen: the linked Lean archive does NOT export the real keygen core \
             (`mlkem_keygen_real_core_available()` is false) - NO verified keygen core is installed, so this \
             process's ML-KEM keypairs are minted by the UNAUDITED `ml-kem` crate behind dregg-pq's loud \
             keygen warning (keygen WARNS, it does not abort). Rebuild against a HEAD-matching archive to \
             route keygen through Lean."
        ),
    });
}

/// Perform the once-per-process ML-DSA-65 KEYGEN-core install at SDK agent-runtime startup, logging once.
fn ensure_verified_mldsa_keygen_core_installed() {
    use dregg_pq::MlDsaKeygenCoreRealInstall as K;
    use std::sync::Once;
    static LOGGED: Once = Once::new();
    let outcome = install_verified_mldsa_keygen_core_real();
    LOGGED.call_once(|| match outcome {
        K::Installed => tracing::info!(
            "ML-DSA keygen: verified Lean REAL keygen core installed at SDK agent-runtime startup - the \
             extracted deterministic FIPS 204 `MlDsaKeygen.mldsaKeygenInternal` (KAT-anchored) is now the \
             IDENTITY-keypair AUTHORITY behind `dregg_pq::MlDsaKey::from_ed25519_seed` for this process; the \
             `fips204` crate is out of the SDK-hosted IDENTITY-KEY keygen TCB"
        ),
        K::AlreadyInstalled => tracing::debug!(
            "ML-DSA keygen: a verified Lean REAL keygen core was already installed this process (install is \
             once-per-process) - the `fips204` crate remains out of the SDK-hosted IDENTITY-KEY keygen TCB"
        ),
        K::ExportAbsent => tracing::warn!(
            "ML-DSA keygen: the linked Lean archive does NOT export the real keygen core \
             (`mldsa_keygen_real_core_available()` is false) - NO verified keygen core is installed, so this \
             process's ML-DSA IDENTITY keypair is minted by the UNAUDITED `fips204` crate behind dregg-pq's \
             loud keygen warning (keygen WARNS, it does not abort). Rebuild against a HEAD-matching archive \
             to route identity keygen through Lean."
        ),
    });
}

/// **THE ONE NAMED INSTALLER** — arm ALL SIX Lean-verified post-quantum cores for this SDK-hosted
/// process, once, so that no call site anywhere has to decide WHICH directions it needs.
///
/// Idempotent, thread-safe, once-per-process. Every install inside it is export-gated by
/// `dregg-pq`, so an archive that exports nothing installs nothing and the refusal at the point of
/// use still stands. The mirror of `dregg_node::install_verified_pq_cores` for SDK hosts.
///
/// # ⚑ THE BUG THIS EXISTS TO MAKE UNREPRESENTABLE: A CALL SITE THAT PICKED A SUBSET
///
/// This function replaces `ensure_verified_mldsa_identity_cores_installed`, which armed exactly
/// KEYGEN and SIGN — "the two cores the hybrid identity path needs". That was a reasonable
/// sentence and it was wrong, because the identity path does not end at signing: the SAME process
/// then VERIFIES, through `dregg_turn::pq::ml_dsa_verify` (the executor's `HybridSignature`
/// admission, `CreateHybridCell` / `RotatePqIdentity` possession proofs) and through
/// `dregg_lightclient`'s hybrid quorum halves. The verify core was armed ONLY by an
/// [`AgentRuntime`] constructor, so:
///
///   * `dregg_sdk::embed::DreggEngine` — the documented no-I/O service-integration engine, which
///     builds its own `TurnExecutor` and never touches `AgentRuntime` — aborted on the first
///     hybrid turn it executed, and every turn an SDK cipherclerk signs is hybrid by default;
///   * `dregg_sdk::verify_finalized_history` — the "Noun 2" light-client entry, whose whole point
///     is that a verifier holds NOTHING but a trust anchor — aborted on the first committee vote's
///     PQ half.
///
/// Neither is a test artifact and neither is exotic; they are the two shapes the public surface
/// advertises. `sdk/tests/hybrid_pq_turn.rs` merely happened to be the file that opened the door,
/// because it signs through a cipherclerk (armed) and then verifies (not armed), and its abort
/// banner named `ML-DSA-65 verify` rather than keygen.
///
/// So the fix is not "add verify to the identity pair". It is that a SUBSET is no longer something
/// an SDK call site can express: every gateway calls THIS, and the only judgement left is *whether*
/// to arm, never *what*. The six single-direction `install_verified_*` functions remain public
/// because a host that wants to match on ONE outcome (the running-binary routing gates in
/// `tests/mldsa_wire_silo_verify.rs`, `tests/mlkem_sdk_kem_verified.rs`) needs them — but nothing
/// in the SDK calls them to ARM any more.
///
/// # Why the point of use, and not only at startup
///
/// Kept verbatim from the function this replaces, because the reasoning is unchanged and was paid
/// for once already. Before it, the only thing in the tree that installed the identity cores was an
/// [`AgentRuntime`] constructor — so whether a process signed with the verified core or reached
/// `dregg-pq`'s refusal depended on whether something had already built a runtime: an ORDERING, not
/// a property of the signing code. In a libtest binary the THREAD COUNT decided it. libtest runs
/// tests in alphabetical order; at `--test-threads=1` an earlier test that happens to construct an
/// `EmbeddedExecutor` installs the cores and carries every later signer, so the suite is green. At
/// 8 threads the signing tests start first and the process aborts mid-suite, with no panic message,
/// on whichever test won the race. `starbridge-tool-access-delegation` was green at 1–4 threads and
/// aborted 5/5 at 8. GitHub's hosted runners are 4-core, so CI never saw it and every developer box
/// with 8+ cores did.
///
/// # What this deliberately does NOT do
///
/// It does not run before `main`. A `.init_array` / `__DATA,__mod_init_func` initializer (what
/// `dregg-pq-testkit`'s `install_at_process_start!` gives a TEST binary) would remove the ordering
/// question entirely — and it would also force the ~125 MB Lean archive into every binary that
/// merely links `dregg-sdk`, whether or not it ever performs a PQ operation, and run Lean archive
/// probes at process start for consumers that embed the SDK inside something larger. That price is
/// not this bug's to charge. The residual is therefore real and named: a consumer that calls
/// `dregg_turn::pq::ml_dsa_verify` or `dregg_lightclient::*` DIRECTLY, having constructed no SDK
/// object at all, still aborts — correctly, since it never asked the SDK for anything.
/// `sdk/tests/pq_cores_without_runtime.rs` pins that boundary from both sides.
pub fn install_verified_pq_cores() {
    use std::sync::Once;
    static ENSURED: Once = Once::new();
    ENSURED.call_once(|| {
        // The ACCEPT/REJECT gate. First, because it is the one whose absence is a security verdict
        // taken by an unaudited crate rather than a value produced by one.
        ensure_verified_mldsa_verify_core_installed();
        ensure_verified_mldsa_sign_core_installed();
        ensure_verified_mldsa_keygen_core_installed();
        ensure_verified_mlkem_encaps_core_installed();
        ensure_verified_mlkem_decaps_core_installed();
        ensure_verified_mlkem_keygen_core_installed();
    });
}

/// **Install the verified deployed-executor oracles** — the constraint oracle and the
/// conservation oracle — once per process, at SDK agent-runtime startup.
///
/// # Why this belongs HERE and not in each binary
///
/// `dregg_exec_lean::register_constraint_oracle()` had, until this line, exactly TWO callers in the
/// whole repo: `node/src/lib.rs` and `dreggnet-web/src/verified_settlement.rs`. Every OTHER
/// SDK-hosted process that drives a turn in-process was unarmed, and the failure is silent-then-fatal:
/// `dregg_cell::program::eval` routes the Lean-evaluated `StateConstraint` subset through the
/// installed oracle and FAILS CLOSED when there is none, but only under
/// `#[cfg(all(not(debug_assertions), any(unix, windows)))]` — **native RELEASE only**. Every test in
/// this repo builds debug, takes the Rust guest-path evaluator, and passes. Nothing goes red until a
/// release binary opens a programmed cell on a box.
///
/// Measured on the deployed edge, 2026-07-26, with both bots built from a HEAD-matching archive
/// (135 `dregg_*` text symbols each — the archive was never the problem):
///
///   * `dreggnet-telegram-bot` PANICS at startup — `dreggnet-surfaces/src/cheevo.rs:155`, because
///     its self-check drives a real turn;
///   * `dregg-discord-bot` boots, connects, registers its slash commands and looks completely
///     healthy while `reveal_cron: Daily reveal did not fire` on every tick, forever.
///
/// The second one is the reason this lives in `AgentRuntime::new` rather than in the two bots: a
/// per-binary fix leaves the next SDK consumer to rediscover it from a cron that quietly never
/// fires. `AgentRuntime::new` is the one place every SDK-hosted turn-driver already passes through,
/// and it is already where the verified PQ cores are installed for exactly the same reason.
///
/// # Warn, do not abort
///
/// Unlike the PQ sign/verify cores (which abort at `dregg-pq`'s audit gate), an absent oracle is
/// reported and execution continues: the fail-closed refusal already lives downstream in
/// `dregg_cell::program::eval`, which is the correct place for it and which a debug/test build
/// legitimately does not reach. Aborting here would break every `default-features = false`
/// (wasm/zkvm) embedding that has no archive to install from and no need of one.
/// # Why `not(debug_assertions)` — the blast radius this deliberately does NOT have
///
/// `dregg_cell::program::eval` uses an installed oracle on **every** target; it is only the
/// *no-oracle refusal* that is release-gated. So installing from `AgentRuntime::new` unconditionally
/// would re-route every programmed-cell decision in every DEBUG test across the workspace from the
/// Rust guest-path evaluator to the Lean oracle — a workspace-wide behaviour change, shipped from a
/// deploy lane, that no one had run the suite against.
///
/// The bug being fixed is native-RELEASE-only by construction, so the fix is too. Debug and test
/// builds keep the guest evaluator and stay exactly as green (or as red) as they were, which is the
/// documented intent in `eval.rs`'s own note: `not(debug_assertions)` is "cell's OWN production
/// convention". The oracle path still has direct coverage in
/// `exec-lean/tests/constraint_oracle_reality_gate.rs`, which installs it explicitly.
///
/// ⚑ THE PROFILE HALF OF THAT GATE IS NO LONGER RESTATED HERE. It reads
/// `dregg_cell::program::constraint_subset_fails_closed_without_oracle()` — the same `const fn`
/// `eval.rs` branches on — instead of a hand-copied `not(debug_assertions)`. The two had already
/// drifted: this function's copy omitted `any(unix, windows)`, so it and the gate did not agree
/// about what a deployed build is. Two further effects, both wanted: the install body is now
/// TYPE-CHECKED in a debug build (before, it compiled only in release — a whole code path `cargo
/// test` could never see), and the remaining `cfg` gates the existence of the dependency.
///
/// ⚑ AND THAT `cfg` NOW ASKS THE TARGET, NOT A FEATURE. It was `feature = "exec-lean"`, default-on
/// — so whether this installer had a body at all UNIFIED across the resolve, and a `-p` build of a
/// consumer that passed `default-features = false` compiled the empty one while `--workspace`
/// compiled this. "Can this target link `libdregg_lean.a`" is a fact about the target; a
/// `[target.'cfg']` dependency cannot unify. See the dep block in `sdk/Cargo.toml`.
#[cfg(not(any(target_arch = "wasm32", target_os = "zkvm")))]
fn ensure_deployed_executor_oracles_installed() {
    use std::sync::Once;
    static LOGGED: Once = Once::new();
    ARMING_REACHED.store(true, std::sync::atomic::Ordering::Relaxed);
    // Install exactly where `dregg-cell`'s refusal bites, and nowhere else — asking the gate rather
    // than describing it. `false` here (every DEBUG build, wasm32, the zkVM guest) means `eval` runs
    // its Rust guest-path evaluator and arming the oracle would silently re-route every
    // programmed-cell decision in the workspace's suite.
    if !dregg_cell::program::constraint_subset_fails_closed_without_oracle() {
        return;
    }
    let constraint = dregg_exec_lean::register_constraint_oracle();
    let conservation = dregg_exec_lean::register_conservation_oracle();
    LOGGED.call_once(|| {
        if constraint {
            tracing::info!(
                "constraint oracle: the deployed executor's Lean-subset StateConstraint/HeapAtom \
                 admission is decided by the verified `dregg_constraint_admits` for this process"
            );
        } else {
            tracing::warn!(
                "constraint oracle: the linked Lean archive does NOT export \
                 `dregg_constraint_admits` — NO oracle is installed, so on a native RELEASE build \
                 `dregg-cell` fails CLOSED for the whole Lean-evaluated constraint subset and EVERY \
                 programmed-cell turn (the Descent, the dungeon, the campaign) will be refused. \
                 Rebuild against a HEAD-matching archive."
            );
        }
        if conservation {
            tracing::info!(
                "conservation oracle: per-asset Σδ=0 is decided by the verified \
                 `dregg_cross_cell_conserves` for this process"
            );
        } else {
            // ⚑ This branch is only reachable INSIDE the release-native guard above, i.e.
            // exactly where `executor/atomic.rs:497` DOES fail closed and the Rust twin is
            // not even compiled. The prior text ("This does not fail closed; it silently
            // decides") described the pre-fail-closed world and was the sentence an
            // operator would act on — stale in the SAFE direction, but still wrong.
            tracing::warn!(
                "conservation oracle: the linked Lean archive does NOT export \
                 `dregg_cross_cell_conserves` — NO oracle is installed, so on this native \
                 RELEASE build every value-moving turn is REFUSED with \
                 `ConservationGateUnavailable` (the unverified Rust twin is not compiled \
                 here, so it cannot silently decide). Rebuild against a HEAD-matching archive."
            );
        }
    });
}

/// Installs nothing on wasm32 / the zkVM guest: those targets link no archive to install FROM, and
/// `dregg-cell`'s fail-closed gate is inactive on them anyway, so the Rust guest-path evaluator is
/// that build's documented (labeled-unverified) path. It still RECORDS that the arming point was
/// reached — see the `ARMING_REACHED` note below, which is why this is not simply an empty body.
///
/// ⚑ THIS ARM IS NOW UNREACHABLE ON NATIVE, WHICH IS THE POINT. Under the old
/// `#[cfg(not(feature = "exec-lean"))]` a NATIVE build landed here whenever the resolve happened
/// not to turn the feature on — a deployed x86_64 bot silently taking the do-nothing installer.
#[cfg(any(target_arch = "wasm32", target_os = "zkvm"))]
fn ensure_deployed_executor_oracles_installed() {
    ARMING_REACHED.store(true, std::sync::atomic::Ordering::Relaxed);
}

/// **Was the deployed-executor arming point REACHED in this process?** — set by
/// [`ensure_deployed_executor_oracles_installed`] on EVERY target and EVERY profile, including the
/// builds where it deliberately installs nothing.
///
/// ⚑ WHY A SEPARATE FLAG FROM "the oracle is installed". The bug this exists to detect is *nothing
/// called the installer*, and that bug is invisible to a test that asks whether the oracle is
/// installed: the answer is legitimately `false` in every DEBUG build (the install is
/// release-gated), so such a test is VACUOUS exactly where the whole workspace runs its suite. It
/// survived a full day of lanes for that reason — four of them saw `no constraint oracle installed`
/// and filed it as co-tenant churn.
///
/// Splitting the two makes the missing-call class detectable in a plain `cargo test`: whether the
/// arming point was reached is a property of the CALL GRAPH, identical in debug and release, while
/// whether an oracle came out of it depends on the target and the linked archive. `spween-dregg`'s
/// `constraint_oracle_armed` tooth asserts the first after a real world-cell deploy — delete the
/// `ensure_deployed_executor_oracles_installed()` call from [`AgentRuntime::new`] and it goes red in
/// debug, on a laptop, in seconds.
static ARMING_REACHED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Whether this process has passed through the deployed-executor arming point (an [`AgentRuntime`]
/// has been constructed, by any route). See the `ARMING_REACHED` note above for why this is asked
/// separately from "is the oracle installed".
///
/// `false` after driving a programmed-cell turn means the turn ran on a path that never reaches
/// [`AgentRuntime`] — a new host that builds a `dregg_turn::TurnExecutor` directly, say — and on a
/// native release build that path can only ever refuse.
pub fn deployed_executor_arming_attempted() -> bool {
    ARMING_REACHED.load(std::sync::atomic::Ordering::Relaxed)
}

/// **The one operator sentence a BINARY should print at startup**, or `None` when this build is
/// correctly configured (or is a build that legitimately has no oracle).
///
/// Arms the oracles (idempotent — an [`AgentRuntime`] anywhere in the process has already done it)
/// and then answers the only question that matters to whoever is watching a boot log: *can this
/// binary serve a programmed-cell turn at all?* The answer is `Some(_)` in exactly one
/// configuration — the build where `dregg_cell`'s
/// `constraint_subset_fails_closed_without_oracle()` holds and no oracle installed — and that
/// configuration cannot serve a single dungeon, Descent or campaign turn.
///
/// ⚑ THIS IS FOR BINARIES THAT MUST NOT REFUSE TO BOOT. `dreggnet-web-server` refuses to bind a
/// listener (`dreggnet_web::install_verified_settlement_gate`) and `dregg-node` refuses to run, both
/// correctly: they exist to serve turns. A chat bot does not — its identity, wallet, gallery and
/// explorer commands all work fine without an oracle — so it should say this LOUDLY at second zero
/// and keep serving what it can, rather than crash-loop. What it must never do is what the Discord
/// bot did for a week: boot, report `active`, and refuse every game silently.
pub fn deployed_executor_arming_deficiency() -> Option<String> {
    ensure_deployed_executor_oracles_installed();
    if !dregg_cell::program::constraint_subset_fails_closed_without_oracle() {
        return None;
    }
    if dregg_cell::program::constraint_oracle_installed() {
        return None;
    }
    Some(
        "NO VERIFIED CONSTRAINT ORACLE in this process, and this build fails CLOSED without one: \
         every programmed-cell turn will be refused — the dungeon, the Descent, the campaign, the \
         daily reveal — while every other command keeps working, so the process will look healthy. \
         EXACTLY ONE build lands here now: one whose linked `libdregg_lean.a` does not export \
         `dregg_constraint_admits` (a `DREGG_REQUIRE_LEAN=0` or stale-archive build degrades to \
         exactly this — check the `constraint oracle:` warning above). Rebuild against a \
         HEAD-matching archive before serving games. (There used to be a SECOND cause, and it was \
         the one an operator could not act on: a native build with `dregg-sdk`'s default-on \
         `exec-lean` feature resolved off, linking no verified executor at all. That feature is \
         deleted — the verified executor is a `[target.'cfg']` dependency now, so no native build \
         can be missing it and no feature selection can take it away.)"
            .to_string(),
    )
}

/// Perform the once-per-process ML-KEM DECAPS-core install at SDK agent-runtime startup, logging once.
fn ensure_verified_mlkem_decaps_core_installed() {
    use dregg_pq::MlKemDecapsCoreInstall as D;
    use std::sync::Once;
    static LOGGED: Once = Once::new();
    let outcome = install_verified_mlkem_decaps_core();
    LOGGED.call_once(|| match outcome {
        D::Installed => tracing::info!(
            "ML-KEM decaps: verified Lean REAL decaps core installed at SDK agent-runtime startup — the \
             extracted full-byte `MlKemDecaps.mlkemDecaps` is now the shared-secret AUTHORITY behind \
             `dregg_pq::ml_kem768_decaps` / `HybridResponder::finish` for this process; the `ml-kem` crate \
             is out of the SDK-hosted KEM-decaps TCB"
        ),
        D::AlreadyInstalled => tracing::debug!(
            "ML-KEM decaps: a verified Lean REAL decaps core was already installed this process (install is \
             once-per-process) — the `ml-kem` crate remains out of the SDK-hosted KEM-decaps TCB"
        ),
        D::ExportAbsent => tracing::warn!(
            "ML-KEM decaps: the linked Lean archive does NOT export the real decaps core \
             (`mlkem_decaps_real_core_available()` is false) — NO verified decaps core is installed, so any \
             ML-KEM decaps this process reaches will be REFUSED by dregg-pq's audit gate (process abort) \
             unless DREGG_ALLOW_UNAUDITED_PQ=1. Rebuild against a HEAD-matching archive to route decaps \
             through Lean."
        ),
    });
}

/// Build the `TurnExecutor` every [`AgentRuntime`] runs on, with the **real**
/// witnessed-predicate verifiers installed (not the fail-closed defaults).
///
/// This is the one behavioral default that makes `SenderAuthorized { PublicRoot }`
/// (and the other STARK-backed witnessed predicates whose backend lives in
/// `dregg-cell`/`dregg-circuit`) ENFORCE FOR REAL on the honest fire path: a
/// turn whose sender carries a genuine Poseidon2 Merkle-membership proof against
/// the authorized-set root is ACCEPTED, and a non-member's turn is rejected at
/// the STARK level — rather than every `SenderAuthorized` turn failing closed
/// because the default registry's `MerkleMembership` slot is a reject-everything
/// stub.
///
/// `registry_with_real_verifiers` rides `dregg-turn`'s existing `dregg-circuit`
/// dependency (the verifier links it), so this adds no new heavy dep to the SDK.
/// A host that needs fail-closed `SenderAuthorized` (e.g. a negative regression)
/// can opt out via `AgentRuntime::set_witnessed_registry(empty())`.
///
/// As of the executor-default change, `TurnExecutor::new()` ALREADY installs
/// `registry_with_real_verifiers()` (the bare executor is no longer a
/// reject-everything stub), so this helper is now just the plain constructor —
/// kept as a named seam so the SDK's intent stays explicit and so a host that
/// wants the host-context-full registry can find the upgrade path
/// (`registry_with_real_verifiers_full`) from here.
fn executor_with_real_verifiers(executor_signing_seed: Option<[u8; 32]>) -> TurnExecutor {
    let mut executor = TurnExecutor::new(ComputronCosts::default_costs());
    // ROUTE (ii): when the HOST supplies an executor signing seed, install it so
    // every committed `TurnReceipt` carries an Ed25519 `executor_signature` over
    // `canonical_executor_signed_message` (the exact bytes
    // `turn::verify_receipt_signature_with_keys` — and the forge check
    // `RequiredCheck::CommittedReceipt` — verify). `None` = today's UNSIGNED
    // behavior, byte-unchanged.
    if let Some(seed) = executor_signing_seed {
        executor.set_executor_signing_key(seed);
    }
    executor
}

/// Derive the Ed25519 executor PUBLIC key from a 32-byte signing seed — the key a
/// forge / auditor pins in `trusted_executor_keys` to admit receipts this runtime's
/// executor signed (`turn::verify_receipt_signature_with_keys`). This is exactly the
/// verifying key `TurnExecutor::maybe_sign_receipt` signs under, so a receipt this
/// runtime committed under `seed` verifies against `executor_pubkey_from_seed(&seed)`.
pub fn executor_pubkey_from_seed(seed: &[u8; 32]) -> [u8; 32] {
    ed25519_dalek::SigningKey::from_bytes(seed)
        .verifying_key()
        .to_bytes()
}

/// The default method a [`SubAgent`] is scoped to when no explicit set is
/// given: the `execute` verb its `execute()` path submits.
pub const DEFAULT_SUBAGENT_METHOD: &str = "execute";

/// Map a worker method NAME to the action string the executor's token verifier
/// matches against.
///
/// The executor binds `request.action = hex(action.method)` where
/// `action.method = symbol(name) = blake3(name)`. The biscuit authorizer fires
/// `allow if service($svc, $actions), request_service($svc), request_action($act),
/// $actions.contains($act)` — a RAW-STRING match — so the grant's action for a
/// method must be exactly `hex(symbol(name))`. Then a worker turn invoking a
/// method OUTSIDE its granted set has a `request_action` no grant `.contains`,
/// the default-deny fires, and the EXECUTOR rejects the turn.
fn method_scope_fragment(method_name: &str) -> String {
    hex::encode(symbol(method_name))
}

/// Whether an [`Attenuation`] would produce no caveats (an empty attenuation,
/// which the token backends reject). Mirrors the dimensions the macaroon /
/// biscuit caveat builders actually emit.
fn restrictions_are_empty(att: &Attenuation) -> bool {
    att.apps.is_empty()
        && att.services.is_empty()
        && att.features.is_empty()
        && att.not_after.is_none()
        && att.not_before.is_none()
        && att.confine_user.is_none()
        && att.oauth_providers.is_empty()
        && att.oauth_scopes.is_empty()
        && att.feature_globs.is_none()
        && att.budget.is_none()
}

/// Mint the ENFORCED capability credential a sub-agent carries on every turn it
/// submits: a public-key biscuit, granting `service(sub_cell, method)` for
/// EXACTLY the set of `methods` the worker may invoke.
///
/// This is the heart of internalizing the guarantee. The biscuit is minted under
/// a fresh issuer keypair; the sub-agent's cell records that issuer's public key
/// as its `verification_key` — the trust anchor the executor's
/// `verify_token_authorization` (`TokenKeyRef::BiscuitIssuer`) checks. The worker
/// presents the credential as `Authorization::Token` on its turn, so the EXECUTOR
/// — not an out-of-band `cap.verify()` — admits or rejects: a turn whose method
/// is outside the granted set has no covering `service(...)` grant, the biscuit's
/// default-deny fires, and the executor rejects with
/// `TokenInsufficientCapability`.
///
/// The service name is the sub-agent's cell id (hex) and each granted action is
/// `hex(symbol(method))`, mirroring exactly what the executor binds from
/// `(action.target, action.method)`.
///
/// Returns `(encoded_biscuit, issuer_pubkey)`.
fn mint_subagent_cap_token(
    sub_cell: CellId,
    methods: &[&str],
) -> Result<(Vec<u8>, [u8; 32]), SdkError> {
    mint_subagent_cap_token_with_keypair(sub_cell, methods, biscuit_auth::KeyPair::new())
}

fn mint_subagent_cap_token_seeded(
    sub_cell: CellId,
    methods: &[&str],
    issuer_seed: &[u8; 32],
) -> Result<(Vec<u8>, [u8; 32]), SdkError> {
    let private =
        biscuit_auth::PrivateKey::from_bytes(issuer_seed, biscuit_auth::Algorithm::Ed25519)
            .map_err(|error| {
                SdkError::MissingKey(format!(
                    "issuer seed is not a valid biscuit ed25519 private key: {error}"
                ))
            })?;
    mint_subagent_cap_token_with_keypair(sub_cell, methods, biscuit_auth::KeyPair::from(&private))
}

fn mint_subagent_cap_token_with_keypair(
    sub_cell: CellId,
    methods: &[&str],
    kp: biscuit_auth::KeyPair,
) -> Result<(Vec<u8>, [u8; 32]), SdkError> {
    let issuer: [u8; 32] = kp
        .public()
        .to_bytes()
        .try_into()
        .expect("ed25519 public key is 32 bytes");
    let svc = hex::encode(sub_cell.as_bytes());
    // One service grant per allowed method: `service(cell_hex, hex(symbol(m)))`.
    // The authorizer's `$actions.contains($act)` then matches exactly the
    // request action `hex(action.method)` for an in-scope verb and nothing else.
    let services: Vec<(String, String)> = methods
        .iter()
        .map(|m| (svc.clone(), method_scope_fragment(m)))
        .collect();
    let token = BiscuitToken::mint_dregg(&kp, &[], &services, &[], &[], &[], None)
        .map_err(SdkError::Token)?;
    let encoded = token.to_encoded().map_err(SdkError::Token)?.into_bytes();
    Ok((encoded, issuer))
}

/// The agent runtime: orchestrates cipherclerk, ledger, and execution.
///
/// This is the top-level coordination layer for an agent. It manages:
/// - The agent's cell in the local ledger
/// - Turn construction and execution
/// - Sub-agent spawning with attenuated capabilities
///
/// The cipherclerk is held behind an `Arc<RwLock<...>>` so that the runtime can
/// append receipts after successful turn execution (mutating the receipt chain
/// and IVC state), while still allowing shared read access for signing and
/// token operations.
///
/// # Example
///
/// ```no_run
/// use dregg_sdk::{AgentCipherclerk, AgentRuntime, Effect};
/// use dregg_types::CellId;
/// use std::sync::{Arc, RwLock};
///
/// let cipherclerk = Arc::new(RwLock::new(AgentCipherclerk::new()));
/// let runtime = AgentRuntime::new(cipherclerk, "my-domain");
///
/// // Execute effects against the local ledger
/// let receipt = runtime.execute(vec![
///     Effect::IncrementNonce { cell: runtime.cell_id() },
/// ]).unwrap();
/// ```
pub struct AgentRuntime {
    /// The agent's cipherclerk (read-write lock for receipt chain mutation).
    cipherclerk: Arc<RwLock<AgentCipherclerk>>,
    /// The agent's cell ID in the local domain.
    cell_id: CellId,
    /// The domain this runtime operates in.
    domain: String,
    /// The local ledger (shared, thread-safe).
    ledger: Arc<Mutex<Ledger>>,
    /// The turn executor.
    executor: TurnExecutor,
    /// Current nonce for the agent's cell (tracks submitted turns).
    nonce: Mutex<u64>,
    /// THE SWAP — producer mode (authority inversion). When `true`, [`Self::execute`] and
    /// [`Self::execute_turn`] make the VERIFIED Lean executor the authoritative state PRODUCER
    /// (`dregg_turn::lean_apply::produce_via_lean`): the committed ledger is reconstituted from the
    /// Lean FFI's post-state, and the Rust [`TurnExecutor`] is demoted to a parallel runtime
    /// DIFFERENTIAL cross-check (a divergence is logged loudly as a real soundness finding). The
    /// verified producer installs its state only for the swap-safe covered set; a root-gap or
    /// unmappable effect falls back to Rust for that turn. Default mirrors `DREGG_LEAN_PRODUCER`
    /// (ON unless `DREGG_LEAN_PRODUCER=0`); `false` is the legacy Rust-producer path. Only ever
    /// `true` on every native build (Lean unconditional; gated OUT only by `no-lean-link`); an unlinked archive
    /// self-falls-back per turn.
    lean_producer_enabled: bool,
    /// ROUTE (ii) — the HOST executor signing seed, or `None` for today's UNSIGNED
    /// default. When `Some`, this runtime's own executor AND every worker
    /// [`SubAgent`] it spawns (the grain drive path) sign every committed
    /// `TurnReceipt`'s `executor_signature` (Ed25519 over
    /// `canonical_executor_signed_message`), so a grain turn is forge-admissible
    /// (`turn::verify_receipt_signature_with_keys` against [`Self::executor_pubkey`]
    /// passes). Additive: `None` leaves the pre-existing behavior byte-unchanged.
    executor_signing_seed: Option<[u8; 32]>,
}

/// Validity horizon (wall-clock seconds) stamped onto turns this SDK constructs.
///
/// The Lean producer's wire marshal REQUIRES the turn envelope's `valid_until`
/// (`dregg_turn::lean_apply::produce_via_lean` / `lean_shadow::turn_to_wire_turn`); leaving it
/// `None` means every turn built this way falls off the verified Lean producer to the legacy
/// Rust producer, per-turn, forever — silently, since `ProducerOutcome::Fallback` is not
/// surfaced to the caller. Worse, on the real executor (`turn/src/executor/execute.rs:426`)
/// `None` skips the expiration check ENTIRELY — the turn never expires, no matter how stale.
/// Mirrors `default_valid_until` in `node/src/api.rs` (same rationale, same fix — see issue
/// #46): wall-clock now + a generous horizon, never a block height (which would already be in
/// the past as a timestamp and expire the turn immediately).
///
/// `pub(crate)` so every `Turn`-constructing site in this crate shares one horizon policy
/// instead of re-deriving (or omitting) it — originally scoped to `AgentRuntime::execute` /
/// `execute_on` / sub-agent submit, now also used by `cipherclerk.rs`'s sovereign/committed
/// turn builders and `committed_turn.rs`'s `CommittedTurnBuilder`, which had the identical
/// `None` sentinel at 7 more sites.
const SDK_TURN_VALIDITY_HORIZON_SECS: i64 = 3600;

pub(crate) fn default_valid_until() -> Option<i64> {
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0);
    Some(now + SDK_TURN_VALIDITY_HORIZON_SECS)
}

impl AgentRuntime {
    /// Create a new agent runtime with simplified ownership.
    ///
    /// This is a convenience constructor that wraps the cipherclerk in `Arc<RwLock<...>>`
    /// internally, so callers don't need to manage the synchronization primitives
    /// themselves.
    ///
    /// # Arguments
    ///
    /// * `cipherclerk` - The agent's cipherclerk (moved into the runtime).
    /// * `domain` - The domain this agent operates in (e.g., "compute", "storage").
    ///
    /// # Example
    ///
    /// ```no_run
    /// use dregg_sdk::{AgentCipherclerk, AgentRuntime};
    ///
    /// let cipherclerk = AgentCipherclerk::new();
    /// let runtime = AgentRuntime::new_simple(cipherclerk, "my-domain");
    /// ```
    pub fn new_simple(cipherclerk: AgentCipherclerk, domain: &str) -> Self {
        Self::new(Arc::new(RwLock::new(cipherclerk)), domain)
    }

    /// Create a new agent runtime.
    ///
    /// Initializes the local ledger with the agent's cell (funded with a default
    /// balance for local execution). The domain determines the agent's cell ID.
    ///
    /// # Arguments
    ///
    /// * `cipherclerk` - Shared read-write reference to the agent's cipherclerk.
    /// * `domain` - The domain this agent operates in (e.g., "compute", "storage").
    pub fn new(cipherclerk: Arc<RwLock<AgentCipherclerk>>, domain: &str) -> Self {
        // Arm every PQ direction this process can reach — verify (the executor's HybridSignature
        // admission, the wire silo, turn/captp receipts), sign, both keygens, and the session KEM.
        // ONE call, no subset: see [`install_verified_pq_cores`] for what choosing a subset cost.
        install_verified_pq_cores();
        // Install the DEPLOYED-EXECUTOR oracles (constraint + conservation). Without the first,
        // `dregg_cell::program::eval` fails CLOSED for the whole Lean-evaluated constraint subset on
        // a native RELEASE build, so every programmed-cell turn is refused -- which is how the
        // Telegram bot came to panic at startup and the Discord bot came to run for hours looking
        // healthy while its daily Descent reveal never fired. See the fn doc.
        ensure_deployed_executor_oracles_installed();
        let cell_id;
        let public_key;
        {
            // Recover from poisoned lock rather than cascading panics.
            // A poisoned RwLock means a writer panicked while holding the lock;
            // we accept the potentially-inconsistent state as preferable to
            // bringing down the entire runtime.
            let w = cipherclerk.read().unwrap_or_else(|e| e.into_inner());
            cell_id = w.cell_id(domain);
            public_key = w.public_key();
        }
        let mut ledger = Ledger::new();

        // Create the agent's cell with a generous initial balance for local use.
        let agent_cell = Cell::with_balance(
            public_key.0,
            *blake3::hash(domain.as_bytes()).as_bytes(),
            1_000_000, // 1M computrons initial balance
        );
        ledger
            .insert_cell(agent_cell)
            .expect("fresh ledger, no conflict");

        let executor = executor_with_real_verifiers(None);
        {
            let w = cipherclerk.read().unwrap_or_else(|e| e.into_inner());
            if let Some(head) = w.receipt_head() {
                executor.set_last_receipt_hash(cell_id, head.receipt_hash());
            }
        }

        AgentRuntime {
            cipherclerk,
            cell_id,
            domain: domain.to_string(),
            ledger: Arc::new(Mutex::new(ledger)),
            executor,
            nonce: Mutex::new(0),
            lean_producer_enabled: lean_producer_env_enabled(),
            executor_signing_seed: None,
        }
    }

    /// Create a runtime with a pre-existing ledger.
    ///
    /// Use this when the ledger is shared with other components or has been
    /// restored from persistent storage.
    pub fn with_ledger(
        cipherclerk: Arc<RwLock<AgentCipherclerk>>,
        domain: &str,
        ledger: Arc<Mutex<Ledger>>,
    ) -> Self {
        // Same once-per-process PQ arming as `new` (this is an independent construction path).
        install_verified_pq_cores();
        // Same deployed-executor oracle install as `new` (independent construction path). This one is
        // NOT optional cosmetics here: `with_ledger` is the path a DURABLE, restored-from-storage
        // host takes, which is exactly the shape both bots use -- so an oracle installed only in
        // `new` would have left them both unarmed anyway.
        ensure_deployed_executor_oracles_installed();
        let cell_id = cipherclerk
            .read()
            .unwrap_or_else(|e| e.into_inner())
            .cell_id(domain);
        let executor = executor_with_real_verifiers(None);

        AgentRuntime {
            cipherclerk,
            cell_id,
            domain: domain.to_string(),
            ledger,
            executor,
            nonce: Mutex::new(0),
            lean_producer_enabled: lean_producer_env_enabled(),
            executor_signing_seed: None,
        }
    }

    /// Create a runtime over an authenticated durable ledger and receipt log.
    ///
    /// Unlike [`Self::with_ledger`], this restores the two pieces of execution
    /// position that must agree with that image before another turn can run:
    /// the next agent nonce (from the restored agent cell) and the executor's
    /// causal receipt head (from the already-validated cipherclerk log). This
    /// constructor does not deserialize or trust either artifact itself; the
    /// caller must restore and authenticate both before invoking it.
    pub fn with_restored_ledger(
        cipherclerk: Arc<RwLock<AgentCipherclerk>>,
        domain: &str,
        ledger: Arc<Mutex<Ledger>>,
    ) -> Result<Self, SdkError> {
        let runtime = Self::with_ledger(cipherclerk, domain, ledger);
        let next_nonce = runtime
            .ledger
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .get(&runtime.cell_id)
            .ok_or_else(|| {
                SdkError::Wire("restored ledger is missing the runtime agent cell".to_owned())
            })?
            .state
            .nonce();
        *runtime
            .nonce
            .lock()
            .unwrap_or_else(|error| error.into_inner()) = next_nonce;

        let head = runtime
            .cipherclerk
            .read()
            .unwrap_or_else(|error| error.into_inner())
            .agent_receipt_head(&runtime.cell_id)
            .map(|receipt| receipt.receipt_hash());
        if let Some(head) = head {
            runtime
                .executor
                .set_last_receipt_hash(runtime.cell_id, head);
        }
        Ok(runtime)
    }

    /// ROUTE (ii) — install a HOST executor signing seed on this runtime (builder
    /// form), so every committed receipt — this runtime's own AND every worker
    /// [`SubAgent`] it spawns (the grain drive path) — is Ed25519-signed over
    /// `canonical_executor_signed_message`. This is what makes a grain turn's
    /// receipt FORGE-ADMISSIBLE: `turn::verify_receipt_signature_with_keys` against
    /// [`Self::executor_pubkey`] passes, exactly the check
    /// `RequiredCheck::CommittedReceipt` runs. Without it the runtime keeps today's
    /// UNSIGNED behavior (`executor_signature == None`) — additive, opt-in.
    pub fn with_executor_signing_key(mut self, seed: [u8; 32]) -> Self {
        self.executor_signing_seed = Some(seed);
        self.executor.set_executor_signing_key(seed);
        self
    }

    /// Install the HOST executor signing seed after construction (see
    /// [`Self::with_executor_signing_key`]). The signed path is opt-in; the seed
    /// threads into every worker [`SubAgent`] this runtime spawns AFTERWARD.
    pub fn set_executor_signing_key(&mut self, seed: [u8; 32]) {
        self.executor_signing_seed = Some(seed);
        self.executor.set_executor_signing_key(seed);
    }

    /// The HOST executor signing seed installed on this runtime, if any.
    pub fn executor_signing_seed(&self) -> Option<[u8; 32]> {
        self.executor_signing_seed
    }

    /// The Ed25519 executor PUBLIC key this runtime signs receipts under (derived
    /// from the installed seed via [`executor_pubkey_from_seed`]), or `None` if no
    /// seed is installed. A forge / auditor pins this in `trusted_executor_keys` to
    /// admit the runtime's — and its grains' — signed receipts.
    pub fn executor_pubkey(&self) -> Option<[u8; 32]> {
        self.executor_signing_seed
            .as_ref()
            .map(executor_pubkey_from_seed)
    }

    /// Get the agent's cell ID.
    pub fn cell_id(&self) -> CellId {
        self.cell_id
    }

    /// Get the domain this runtime operates in.
    pub fn domain(&self) -> &str {
        &self.domain
    }

    /// Get a reference to the ledger.
    pub fn ledger(&self) -> &Arc<Mutex<Ledger>> {
        &self.ledger
    }

    /// **This runtime's `TurnExecutor`** — the holder of the LIVE nullifier / commitment /
    /// revocation accumulator roots that
    /// [`dregg_turn::state_commit::consensus_state_commitment`] binds.
    ///
    /// Exposed for the paths that must stamp a receipt with THIS runtime's consensus anchor
    /// without going through [`Self::execute_turn`] — today that is
    /// `dregg_intent::fulfillment::execute_fulfillment_flow_verified`, whose value leg settles
    /// through the verified per-asset transition rather than the executor. Read-only: the
    /// executor's own interior mutability is its business, and nothing here hands out a `&mut`.
    pub fn executor(&self) -> &TurnExecutor {
        &self.executor
    }

    /// Get the agent's current nonce.
    pub fn nonce(&self) -> u64 {
        *self.nonce.lock().unwrap()
    }

    /// **What this runtime's executor will charge for `turn`** — [`TurnExecutor::estimate_cost`]
    /// over the turn's own call forest, at THIS runtime's installed
    /// [`ComputronCosts`](dregg_turn::executor::ComputronCosts) table.
    ///
    /// Exposed so a caller can price a turn BEFORE submitting it, rather than guessing a `fee`
    /// constant. The estimator and the executor's running meter walk the same four charge points
    /// in the same order (`action_base`, the authorization, then every effect —
    /// `executor/execute_tree.rs`), off the same cost table, so for a turn that runs to completion
    /// the estimate is the metered total exactly, not an upper bound. A caller that stamps this as
    /// the turn's `fee` therefore pays precisely what the turn costs; if the two ever diverge the
    /// executor says so by name (`BudgetExceeded { limit: <estimate>, used: <actual> }`) instead of
    /// failing quietly.
    ///
    /// Reads no ledger state and mutates nothing.
    pub fn estimate_turn_cost(&self, turn: &Turn) -> u64 {
        self.executor.estimate_cost(turn)
    }

    /// Get a reference to the cipherclerk (behind RwLock).
    ///
    /// Callers should use `.read().unwrap_or_else(|e| e.into_inner())` for read
    /// access or `.write().unwrap_or_else(|e| e.into_inner())` for mutation
    /// (e.g., enabling IVC, minting tokens).
    pub fn cipherclerk(&self) -> &Arc<RwLock<AgentCipherclerk>> {
        &self.cipherclerk
    }

    /// Legacy alias for [`Self::cipherclerk`].
    #[doc(hidden)]
    pub fn cclerk(&self) -> &Arc<RwLock<AgentCipherclerk>> {
        self.cipherclerk()
    }

    /// Attach a budget gate (Stingray bounded counter) to this runtime's executor.
    ///
    /// When set, each turn execution will check the silo's local budget slice
    /// before proceeding. If the slice cannot cover the turn fee, the turn is
    /// rejected with `TurnError::BudgetExhausted`.
    ///
    /// Call this when the agent's current silo has provided a budget slice via
    /// the StingrayCounter (dregg_coord::StingrayCounter).
    pub fn set_budget_gate(&mut self, silo_id: u32, slice: BudgetSlice) {
        self.executor
            .set_budget_gate(BudgetGate::new(silo_id, slice));
    }

    /// Set the federation id used by the embedded executor for signature
    /// verification. Must match the federation id used to sign actions.
    pub fn set_local_federation_id(&mut self, id: [u8; 32]) {
        self.executor.set_local_federation_id(id);
    }

    /// Federation id currently used to verify action signatures.
    pub fn local_federation_id(&self) -> [u8; 32] {
        self.executor.local_federation_id
    }

    /// Set the block height the embedded executor evaluates time-gated
    /// program constraints against (`TemporalGate` and friends, via
    /// `EvalContext.block_height`).
    ///
    /// A node-driven executor gets this from consensus; a local runtime
    /// defaults to 0. The settlement-cell timeout/deadline gates built by
    /// [`crate::factories`] read this height.
    pub fn set_block_height(&mut self, height: u64) {
        self.executor.set_block_height(height);
    }

    /// The block height the embedded executor currently evaluates
    /// time-gated program constraints against. Turn builders that must
    /// stamp the execution height (the identity pre-rotation rotate verb,
    /// [`crate::identity`]) read it here.
    pub fn block_height(&self) -> u64 {
        self.executor.block_height
    }

    /// The executor's recorded receipt-chain head for `agent` (the hash a
    /// directly-built [`Turn::previous_receipt_hash`] must carry to satisfy the
    /// executor's `check_previous_receipt_hash`), or `None` if `agent` has
    /// committed no turn yet.
    ///
    /// Callers who hand-assemble a [`Turn`] for an agent that has already acted
    /// (e.g. a governed identity cell that adopted itself, then is driven by a
    /// custom-authorized rotation) read the chain head here rather than passing
    /// `None` and tripping `ReceiptChainMismatch`.
    pub fn agent_receipt_head(&self, agent: &CellId) -> Option<[u8; 32]> {
        self.executor.get_last_receipt_hash(agent)
    }

    /// Replace this runtime's executor's witnessed-predicate registry.
    ///
    /// `AgentRuntime` defaults (via [`executor_with_real_verifiers`]) to the
    /// REAL STARK-backed registry, so `SenderAuthorized { PublicRoot }` and the
    /// other `dregg-circuit`-backed witnessed predicates enforce for real. Call
    /// this to install a different registry — e.g.
    /// `dregg_cell::WitnessedPredicateRegistry::empty()` for a negative test that
    /// wants fail-closed `SenderAuthorized`, or
    /// `dregg_turn::executor::registry_with_real_verifiers_full(..)` to add the
    /// host-context-dependent kinds (Dfa / Temporal / BlindedSet issuer-root).
    pub fn set_witnessed_registry(&mut self, registry: dregg_cell::WitnessedPredicateRegistry) {
        self.executor.set_witnessed_registry(registry);
    }

    /// Deploy a [`FactoryDescriptor`] into this runtime's executor.
    ///
    /// Once deployed, an `Effect::CreateCellFromFactory` referencing the
    /// descriptor's `factory_vk` is admitted (the executor validates the
    /// creation params against the descriptor and births the child cell with
    /// the descriptor's `state_constraints` installed as its `CellProgram`,
    /// so the factory's slot caveats bite on every subsequent turn). Returns
    /// the deployed `factory_vk`.
    pub fn deploy_factory(&mut self, descriptor: dregg_cell::FactoryDescriptor) -> [u8; 32] {
        self.executor.deploy_factory(descriptor)
    }

    /// THE SWAP — toggle producer mode on this runtime (authority inversion).
    ///
    /// When enabled, [`Self::execute`] / [`Self::execute_turn`] route the committed state through
    /// the VERIFIED Lean executor (`dregg_turn::lean_apply::produce_via_lean`) and demote the Rust
    /// `TurnExecutor` to a logged differential. The constructors default this to
    /// [`lean_producer_env_enabled`] (ON unless `DREGG_LEAN_PRODUCER=0`); use this to set it
    /// explicitly (e.g. an app that wires the producer path from its own config field rather than
    /// the env var).
    ///
    /// Has NO effect under the `no-lean-link` platform gate — there the
    /// producer path is not compiled in and execution always uses the legacy Rust producer.
    pub fn set_lean_producer(&mut self, enabled: bool) {
        self.lean_producer_enabled = enabled;
    }

    /// Whether producer mode (the verified Lean executor as the authoritative state producer) is
    /// active on this runtime. See [`Self::set_lean_producer`].
    pub fn lean_producer_enabled(&self) -> bool {
        self.lean_producer_enabled
    }

    /// Run one fully-built turn against `ledger`, choosing the PRODUCER per [`Self::lean_producer_enabled`].
    ///
    /// THE SWAP authority inversion (Stage 0) lives here: when producer mode is on (and the crate
    /// was built by default on native), on the COVERED set the VERIFIED Lean executor is
    /// AUTHORITATIVE via `dregg_turn::lean_apply::produce_via_lean` — its post-state AND its commit
    /// verdict are committed unconditionally — and the Rust `TurnExecutor` is demoted to a checked
    /// reference. A Lean↔Rust disagreement on a covered turn is a surfaced RUST BUG (`error!`), NOT a
    /// fallback to Rust: the verified verdict is what was committed. The returned [`TurnResult`]
    /// follows the AUTHORITATIVE (Lean) verdict, with the receipt's `post_state_hash` pinned to the
    /// installed Lean root.
    ///
    /// When producer mode is off — or the turn is outside the covered set (an uncovered/root-gap
    /// effect) — this is the legacy `self.executor.execute(turn, ledger)` path, explicitly FENCED
    /// (the uncovered partition is named + surfaced, not a silent Rust default).
    fn run_turn(&self, turn: &Turn, ledger: &mut Ledger) -> TurnResult {
        produce(&self.executor, turn, ledger, self.lean_producer_enabled)
    }

    /// Open the typed turn builder — the SDK's one public turn shape:
    /// `runtime.turn().transfer(..).write(..).sign()?.submit()` →
    /// [`crate::Receipt`].
    ///
    /// See [`crate::turns`] for the verbs. The legacy `execute*` methods
    /// below are the same authorized flow without the staging surface.
    pub fn turn(&self) -> TurnBuilder<'_> {
        TurnBuilder::new(self)
    }

    /// Sign `unsigned` over the canonical federation- and turn-nonce-bound
    /// message. `turn_nonce` must be the nonce the submitting turn carries.
    pub(crate) fn sign_action_for_runtime(&self, unsigned: Action, turn_nonce: u64) -> Action {
        self.cipherclerk
            .read()
            .unwrap_or_else(|e| e.into_inner())
            .sign_action_hybrid(unsigned, &self.executor.local_federation_id, turn_nonce)
    }

    pub(crate) fn next_agent_turn_nonce(&self) -> u64 {
        *self.nonce.lock().unwrap()
    }

    /// Submit a SIGNED root action as an ordinary agent turn: this agent
    /// pays `fee`, the turn rides the runtime nonce, and the committed
    /// receipt is appended to the identity's receipt chain.
    ///
    /// This is the shared core under [`Self::execute`], [`Self::execute_on`]
    /// and [`crate::turns::AuthorizedTurn::submit`].
    pub(crate) fn submit_signed_action_as_agent(
        &self,
        action: Action,
        fee: u64,
    ) -> Result<TurnReceipt, SdkError> {
        let mut forest = CallForest::new();
        forest.add_root(action);

        // LOCK ORDER: ledger → nonce → cipherclerk (canonical order to prevent deadlock).
        let mut ledger = self.ledger.lock().unwrap();

        let nonce = {
            let mut n = self.nonce.lock().unwrap();
            let current = *n;
            *n += 1;
            current
        };

        // Bind this turn to the receipt chain: read the latest receipt hash from the cipherclerk.
        let previous_receipt_hash = self
            .cipherclerk
            .read()
            .unwrap_or_else(|e| e.into_inner())
            .receipt_head()
            .map(|r| r.receipt_hash());

        let turn = Turn {
            agent: self.cell_id,
            nonce,
            call_forest: forest,
            fee,
            memo: None,
            valid_until: default_valid_until(),
            previous_receipt_hash,
            depends_on: Vec::new(),
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };

        // Execute against the local ledger (producer mode routes through the verified Lean executor
        // when enabled; otherwise the legacy Rust producer). See [`Self::run_turn`].
        let result = self.run_turn(&turn, &mut ledger);

        match result {
            TurnResult::Committed { receipt, .. } => {
                // Release ledger lock before taking cipherclerk write lock.
                drop(ledger);
                // Append the receipt to the cipherclerk's chain (write lock).
                // Strict mode: surface fork detection as an SdkError instead of
                // silently rewriting the receipt's `previous_receipt_hash`.
                self.cipherclerk
                    .write()
                    .unwrap_or_else(|e| e.into_inner())
                    .append_receipt(receipt.clone())?;
                Ok(receipt)
            }
            TurnResult::Rejected { reason, .. } => Err(SdkError::Turn(reason)),
            TurnResult::Expired => Err(SdkError::Rejected("turn expired".to_string())),
            TurnResult::Pending => Err(SdkError::Rejected("turn pending".to_string())),
        }
    }

    /// Submit a SIGNED root action as a cell-agent turn: `cell` is the turn
    /// agent and pays `fee` from its own balance; the receipt belongs to the
    /// cell's history (NOT appended to this identity's chain).
    pub(crate) fn submit_signed_action_as_cell(
        &self,
        cell: CellId,
        action: Action,
        fee: u64,
    ) -> Result<TurnReceipt, SdkError> {
        let mut forest = CallForest::new();
        forest.add_root(action);
        let mut ledger = self.ledger.lock().unwrap();
        // The turn nonce must equal the agent CELL's on-ledger replay counter.
        let nonce = ledger
            .get(&cell)
            .ok_or(SdkError::Turn(dregg_turn::TurnError::CellNotFound {
                id: cell,
            }))?
            .state
            .nonce();
        let turn = Turn {
            agent: cell,
            nonce,
            call_forest: forest,
            fee,
            memo: None,
            valid_until: default_valid_until(),
            previous_receipt_hash: None,
            depends_on: Vec::new(),
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };
        match self.run_turn(&turn, &mut ledger) {
            TurnResult::Committed { receipt, .. } => Ok(receipt),
            TurnResult::Rejected { reason, .. } => Err(SdkError::Turn(reason)),
            TurnResult::Expired => Err(SdkError::Rejected("turn expired".to_string())),
            TurnResult::Pending => Err(SdkError::Rejected("turn pending".to_string())),
        }
    }

    /// Execute a list of effects against the local ledger.
    ///
    /// Wraps the effects into a turn, signs it, and executes it atomically.
    /// On success, the ledger is updated and a receipt is returned.
    ///
    /// Equivalent to `self.turn().effects(effects).sign()?.submit()` minus
    /// the [`crate::Receipt`] wrapper — the typed builder is the preferred
    /// public shape.
    ///
    /// # Arguments
    ///
    /// * `effects` - The effects to execute (state changes, transfers, etc.)
    ///
    /// # Returns
    ///
    /// A [`TurnReceipt`] proving the turn was committed, or an error if
    /// execution was rejected.
    #[must_use = "dropping the TurnReceipt silently discards proof of execution"]
    pub fn execute(&self, effects: Vec<Effect>) -> Result<TurnReceipt, SdkError> {
        // Sign before acquiring the ledger lock since signing is pure.
        let action = self.sign_action_for_runtime(
            raw::unsigned_action_named(self.cell_id, "execute", effects),
            self.next_agent_turn_nonce(),
        );
        self.submit_signed_action_as_agent(action, 10_000)
    }

    /// Execute effects in a turn whose agent (and action target) is `cell`
    /// rather than this runtime's own agent cell — `cell` PAYS `fee` from its
    /// own balance, and `fee` is the turn's computron budget.
    ///
    /// The action is signed with this runtime's cipherclerk key, so this only
    /// commits for cells whose `owner_pubkey` IS this runtime's public key
    /// (the executor verifies the Ed25519 signature against the target cell's
    /// key). The canonical use is the one-time capability bootstrap of a
    /// factory-born cell (see [`crate::factories`]): the cell self-grants its
    /// creator a c-list capability, after which the creator drives it with
    /// ordinary agent-paid turns via [`Self::execute_on`].
    ///
    /// Differences from [`Self::execute`]:
    /// * `turn.agent = cell` — the turn nonce is the CELL's on-ledger replay
    ///   counter (read fresh under the ledger lock), not the runtime's;
    /// * `fee` is debited from the CELL (budget for the turn's computrons);
    /// * the receipt is returned but NOT appended to the runtime's receipt
    ///   chain (it belongs to `cell`'s history, not the agent's).
    #[must_use = "dropping the TurnReceipt silently discards proof of execution"]
    pub fn execute_as(
        &self,
        cell: CellId,
        effects: Vec<Effect>,
        fee: u64,
    ) -> Result<TurnReceipt, SdkError> {
        let turn_nonce = {
            let ledger = self.ledger.lock().unwrap();
            ledger
                .get(&cell)
                .ok_or(SdkError::Turn(dregg_turn::TurnError::CellNotFound {
                    id: cell,
                }))?
                .state
                .nonce()
        };
        let action = self.sign_action_for_runtime(
            raw::unsigned_action_named(cell, "execute", effects),
            turn_nonce,
        );
        self.submit_signed_action_as_cell(cell, action, fee)
    }

    /// Execute effects in an ordinary agent turn (this runtime's agent pays
    /// the fee) whose ACTION TARGETS `target` instead of the agent cell.
    ///
    /// This is the production shape for driving a cell the agent administers
    /// (the node's app-cell ingress uses it for factory-born cells): the
    /// action is signed with this runtime's key and the executor verifies it
    /// against `target`'s `owner_pubkey`, per-effect checks ride on
    /// `effect.cell == action.target`, and the parent gate requires the agent
    /// to hold a c-list capability on `target` (bootstrap one via the cell's
    /// self-grant — see [`crate::factories`] `adopt_effects`). The target
    /// cell's installed `CellProgram` decides whether the transition commits.
    #[must_use = "dropping the TurnReceipt silently discards proof of execution"]
    pub fn execute_on(
        &self,
        target: CellId,
        effects: Vec<Effect>,
    ) -> Result<TurnReceipt, SdkError> {
        let action = self.sign_action_for_runtime(
            raw::unsigned_action_named(target, "execute", effects),
            self.next_agent_turn_nonce(),
        );
        self.submit_signed_action_as_agent(action, 10_000)
    }

    /// Execute a pre-built turn against the local ledger.
    ///
    /// Use this when you need full control over the turn structure (multiple
    /// root actions, child actions, custom authorization, etc.)
    #[must_use = "dropping the TurnReceipt silently discards proof of execution"]
    pub fn execute_turn(&self, turn: &Turn) -> Result<TurnReceipt, SdkError> {
        // LOCK ORDER: ledger → nonce → cipherclerk (canonical order to prevent deadlock).
        let mut ledger = self.ledger.lock().unwrap();
        // The cipherclerk's make_turn paths default fee to 0 and nonce to 0;
        // if the caller hasn't set them, fill in sensible defaults so budget
        // and replay checks pass.
        let mut turn = turn.clone();
        if turn.fee == 0 {
            turn.fee = 10_000;
        }
        {
            let mut n = self.nonce.lock().unwrap();
            if turn.nonce == 0 && *n > 0 {
                turn.nonce = *n;
            }
            // Ensure the runtime nonce tracker stays ahead of this turn.
            if turn.nonce >= *n {
                *n = turn.nonce + 1;
            }
        }
        // Producer mode routes through the verified Lean executor when enabled (see `run_turn`).
        let result = self.run_turn(&turn, &mut ledger);

        match result {
            TurnResult::Committed { receipt, .. } => {
                // Release ledger lock before taking cipherclerk write lock.
                drop(ledger);
                // The cipherclerk holds THIS runtime agent's (`self.cell_id`)
                // receipt chain — a single linear history. A turn whose agent IS
                // this runtime's agent extends that chain. A turn that DRIVES a
                // DIFFERENT cell (e.g. a governed identity cell rotated by a
                // custom-auth attestation, `turn.agent != self.cell_id`) belongs
                // to THAT cell's own per-agent history; the executor already
                // tracks it under its own authority head (`last_receipt_hash`),
                // and the turn's `previous_receipt_hash` links to THAT head, not
                // this agent's. Appending it here would splice a foreign-agent
                // receipt onto this agent's linear chain (its `prev` points at the
                // driven cell's head, never this chain's head) — a spurious
                // `ReceiptChainMismatch`. This mirrors `submit_signed_action_as_cell`,
                // which deliberately does NOT append a cell-agent turn to this
                // identity's chain.
                if receipt.agent == self.cell_id {
                    // Strict mode: surface fork detection as an SdkError.
                    self.cipherclerk
                        .write()
                        .unwrap_or_else(|e| e.into_inner())
                        .append_receipt(receipt.clone())?;
                }
                Ok(receipt)
            }
            TurnResult::Rejected { reason, .. } => Err(SdkError::Turn(reason)),
            TurnResult::Expired => Err(SdkError::Rejected("turn expired".to_string())),
            TurnResult::Pending => Err(SdkError::Rejected("turn pending".to_string())),
        }
    }

    /// Spawn a sub-agent with attenuated capabilities.
    ///
    /// Creates a new agent (fresh cipherclerk + cell) with capabilities derived from
    /// this agent's tokens, narrowed by the given restrictions. The sub-agent
    /// operates on the same ledger but with reduced authority.
    ///
    /// The sub-agent is scoped to the single [`DEFAULT_SUBAGENT_METHOD`] verb its
    /// [`SubAgent::execute`] path uses. Use [`Self::spawn_sub_agent_scoped`] to
    /// grant a worker an explicit set of method verbs.
    ///
    /// # Arguments
    ///
    /// * `restrictions` - Restrictions to apply to the delegated token.
    /// * `token` - The parent token to delegate from.
    ///
    /// # Returns
    ///
    /// A [`SubAgent`] with its own cipherclerk and attenuated token.
    pub fn spawn_sub_agent(
        &self,
        restrictions: &Attenuation,
        token: &HeldToken,
    ) -> Result<SubAgent, SdkError> {
        self.spawn_sub_agent_scoped(restrictions, token, &[DEFAULT_SUBAGENT_METHOD])
    }

    /// Spawn a sub-agent scoped to an explicit set of method verbs.
    ///
    /// Identical to [`Self::spawn_sub_agent`], but the worker's ENFORCED
    /// capability credential (the public-key biscuit it presents as
    /// `Authorization::Token` on every turn) grants exactly `allowed_methods`.
    /// The EXECUTOR — not an out-of-band `cap.verify()` — rejects a worker turn
    /// whose method is outside this set (`TokenInsufficientCapability`). This is
    /// the in-runtime admission gate: the credential the worker carries IS the
    /// boundary.
    pub fn spawn_sub_agent_scoped(
        &self,
        restrictions: &Attenuation,
        token: &HeldToken,
        allowed_methods: &[&str],
    ) -> Result<SubAgent, SdkError> {
        self.spawn_sub_agent_scoped_with(
            restrictions,
            token,
            allowed_methods,
            AgentCipherclerk::new(),
            None,
        )
    }

    /// Deterministic worker construction for restart-reconstructible authority.
    pub fn spawn_sub_agent_scoped_seeded(
        &self,
        restrictions: &Attenuation,
        token: &HeldToken,
        allowed_methods: &[&str],
        worker_seed: [u8; 32],
        issuer_seed: [u8; 32],
    ) -> Result<SubAgent, SdkError> {
        let sub_cclerk = AgentCipherclerk::from_key_bytes(Zeroizing::new(worker_seed));
        let issuer_seed = Zeroizing::new(issuer_seed);
        self.spawn_sub_agent_scoped_with(
            restrictions,
            token,
            allowed_methods,
            sub_cclerk,
            Some(&issuer_seed),
        )
    }

    fn spawn_sub_agent_scoped_with(
        &self,
        restrictions: &Attenuation,
        token: &HeldToken,
        allowed_methods: &[&str],
        mut sub_cclerk: AgentCipherclerk,
        issuer_seed: Option<&[u8; 32]>,
    ) -> Result<SubAgent, SdkError> {
        let sub_pk = sub_cclerk.public_key();

        // The delegated (narration) HeldToken must carry at least one caveat —
        // an empty attenuation is rejected. When the caller relies purely on
        // `allowed_methods` and passes empty `restrictions`, narrow the
        // delegated token to those method verbs as a service grant so the
        // narration token is itself scoped and the attenuation is non-empty.
        let effective_restrictions = if restrictions_are_empty(restrictions) {
            // A `feature` caveat naming the worker's scope keeps the (legacy,
            // out-of-band) delegation token itself narrowed and the attenuation
            // non-empty. The ENFORCED gate is the biscuit `cap_token` minted
            // below; this token is the redundant defense-in-depth presentation.
            Attenuation {
                features: allowed_methods
                    .iter()
                    .map(|m| format!("subagent-method:{m}"))
                    .collect(),
                ..Default::default()
            }
        } else {
            restrictions.clone()
        };

        // Attenuate the token for the sub-agent.
        let decoded = token.decode()?;
        let attenuated_boxed = decoded.attenuate(&effective_restrictions)?;
        let encoded = attenuated_boxed.to_encoded()?;

        let token_id = format!("sub:{}:{}", token.id(), sub_pk.short_hex());
        let delegated_label = format!("delegated:{}", token.service());

        // SECURITY: The sub-agent receives an attenuated token with zeroed root_key.
        // It cannot mint new root tokens or bypass the attenuation chain.
        // However, it carries the derived issuer_key for ZK proof generation.
        // The issuer_key is always the derived proof key (never the raw root key).
        let issuer_key = *token.issuer_key();
        // Carry the parent's effect-mask authority projection forward (monotone — the
        // sub-agent's `granted` can never exceed the parent's `held`).
        // ⚑ The parent's `verified` bit is INHERITED, never asserted: attenuation narrows
        // authority and cannot manufacture a verification the parent never had. Until
        // 2026-07-30 `new_attenuated` hardcoded `verified: true` here.
        let delegated_token = HeldToken::new_attenuated(
            delegated_label.clone(),
            token.service().to_string(),
            encoded.clone(),
            token_id.clone(),
            issuer_key,
            token.narrowed_authority(),
            token.is_verified(),
        );

        // Pass through the issuer_key as the proof_key for the sub-agent's delegation.
        // Since issuer_key is already a one-way derivation (never the raw root key),
        // it's safe to transmit to the sub-agent.
        let proof_key = if issuer_key != [0u8; 32] {
            Some(issuer_key)
        } else {
            None
        };

        // Local (in-process) sub-agent spawning. We use the typed `LocalDelegation`
        // path so this code can never accidentally normalize an externally-sourced
        // unsigned token. The local envelope is still signature-bound (under a
        // distinct domain tag), and the receiver verifies it against the parent
        // cipherclerk's public key.
        let parent_pubkey = {
            let parent = self.cipherclerk.read().unwrap_or_else(|e| e.into_inner());
            parent.public_key()
        };
        let local = {
            let parent = self.cipherclerk.read().unwrap_or_else(|e| e.into_inner());
            parent.make_local_delegation(
                encoded,
                token.service().to_string(),
                delegated_label,
                token_id,
                sub_pk,
                effective_restrictions.clone(),
                proof_key,
                None, // no pre-generated membership proof in this path
                None, // no caveat_chain_hash; sub-agent operates on local state
            )
        };
        sub_cclerk.receive_local_delegation(local, &parent_pubkey)?;

        let sub_cell_id = sub_cclerk.cell_id(&self.domain);

        // Mint the ENFORCED capability credential the worker carries on every
        // turn: a public-key biscuit granting `service(sub_cell, method)` for
        // exactly `allowed_methods`. The worker presents this as
        // `Authorization::Token`, so the EXECUTOR's `verify_token_authorization`
        // — not an out-of-band `cap.verify()` — is the real admission gate.
        let federation_id = self.executor.local_federation_id;
        let (cap_token, cap_issuer) = match issuer_seed {
            None => mint_subagent_cap_token(sub_cell_id, allowed_methods)?,
            Some(seed) => mint_subagent_cap_token_seeded(sub_cell_id, allowed_methods, seed)?,
        };
        let cap_methods: Vec<String> = allowed_methods.iter().map(|m| m.to_string()).collect();

        // Create the sub-agent's cell in the ledger, recording the biscuit
        // issuer's public key as the cell's `verification_key` — the trust anchor
        // the executor checks (`TokenKeyRef::BiscuitIssuer` requires the issuer to
        // equal the target cell's pk or its verification key). This binds the
        // worker's credential to ITS OWN cell: a credential issued by any other
        // key is rejected by the executor.
        {
            let mut ledger = self.ledger.lock().unwrap();
            let mut sub_cell = Cell::with_balance(
                sub_pk.0,
                *blake3::hash(self.domain.as_bytes()).as_bytes(),
                100_000, // 100k computrons for sub-agent
            );
            sub_cell.verification_key = Some(VerificationKey {
                hash: *blake3::hash(&cap_issuer).as_bytes(),
                data: cap_issuer.to_vec(),
            });
            // Ignore error if cell already exists (idempotent).
            let _ = ledger.insert_cell(sub_cell);
        }

        Ok(SubAgent {
            cipherclerk: Arc::new(sub_cclerk),
            cell_id: sub_cell_id,
            token: delegated_token,
            cap_token,
            cap_issuer,
            cap_methods,
            parent: self
                .cipherclerk
                .read()
                .unwrap_or_else(|e| e.into_inner())
                .public_key(),
            domain: self.domain.clone(),
            federation_id,
            ledger: self.ledger.clone(),
            nonce: Mutex::new(0),
            last_receipt_hash: Mutex::new(None),
            // Inherit producer mode from the parent runtime so worker turns route
            // through the SAME producer-selection seam a runtime turn does.
            lean_producer_enabled: self.lean_producer_enabled,
            // ROUTE (ii) — inherit the host executor signing seed, so the FRESH
            // executor this worker builds per `execute_method` signs the committed
            // grain-turn receipt (forge-admissible). `None` = unsigned worker turns.
            executor_signing_seed: self.executor_signing_seed,
            // WAVE A / WELD — a freshly spawned worker is NOT enveloped until the
            // gateway pins the owner key (`admit_enveloped_owned`); default `None`.
            owner_envelope_pubkey: None,
        })
    }
}

/// Run one fully-built turn against `ledger`, choosing the PRODUCER per `lean_producer_enabled`.
///
/// This is the single producer-selection seam shared by [`AgentRuntime::run_turn`] and every
/// worker turn ([`SubAgent::execute_method`]). When producer mode is on, on the COVERED set the
/// VERIFIED Lean executor is AUTHORITATIVE via `dregg_exec_lean::produce_via_lean` — its post-state
/// AND commit verdict are committed unconditionally, and the Rust `TurnExecutor` is demoted to a
/// checked reference. A covered Lean↔Rust disagreement is a surfaced RUST BUG (`error!`), NOT a
/// fallback to Rust. Off the covered set (or with producer mode off, or on wasm32/zkvm) this is the
/// legacy `executor.execute(turn, ledger)` path — byte-identical to the pre-weld behavior.
///
/// ⚑ "the crate was built with `exec-lean`" IS NO LONGER A CONDITION. On every native target the
/// verified producer is compiled in; only wasm32 and the zkVM guest, which cannot link the archive,
/// take the legacy path. It used to be a default-on feature, so a resolve that did not happen to
/// enable it demoted a NATIVE build to the Rust producer with no line emitted anywhere.
#[cfg_attr(
    any(target_arch = "wasm32", target_os = "zkvm"),
    allow(unused_variables)
)]
fn produce(
    executor: &TurnExecutor,
    turn: &Turn,
    ledger: &mut Ledger,
    lean_producer_enabled: bool,
) -> TurnResult {
    #[cfg(not(any(target_arch = "wasm32", target_os = "zkvm")))]
    {
        if lean_producer_enabled {
            use dregg_exec_lean::{self as lean_apply, ProducerOutcome};
            let (result, outcome) = lean_apply::produce_via_lean(executor, turn, ledger);
            match &outcome {
                // ⚑ DESTRUCTURED FIELD-BY-FIELD ON PURPOSE — no `..`. `ProducerOutcome` is the
                // authority-inversion report; when it gains a leg (as it did on 2026-07-30 with
                // `divergence`, which broke this consumer while `dregg-exec-lean` stayed green),
                // this arm must go RED and be told about it rather than swallow it.
                ProducerOutcome::LeanAuthoritative {
                    committed,
                    rust_agreed,
                    divergence,
                    lean_root,
                    rust_root,
                    rust_committed,
                } => {
                    if *rust_agreed {
                        tracing::info!(
                            target: "dregg::sdk::lean_producer",
                            agent = ?turn.agent,
                            committed = *committed,
                            "THE SWAP producer mode (SDK): verified Lean executor is \
                             AUTHORITATIVE for this covered turn; Rust reference AGREES"
                        );
                    } else {
                        // THE AUTHORITY INVERSION's tooth: a covered Lean↔Rust disagreement is
                        // the Rust path being WRONG. The verified Lean verdict was committed;
                        // this surfaces the Rust bug — it is NOT a fallback to Rust.
                        tracing::error!(
                            target: "dregg::sdk::lean_producer",
                            agent = ?turn.agent,
                            lean_committed = *committed,
                            rust_committed = *rust_committed,
                            // WHICH LEG caught it (commit bit / anchor / ledger-at-cell) — the
                            // anchor is structurally blind to the third, so naming the leg is what
                            // makes this line diagnosable instead of just alarming.
                            divergence = ?divergence,
                            lean_root = ?lean_root,
                            rust_root = ?rust_root,
                            "THE SWAP authority inversion (SDK): verified Lean executor \
                             (AUTHORITATIVE) and the demoted Rust reference DISAGREE on a \
                             covered turn — the Rust path is BUGGY (REAL finding). The verified \
                             Lean verdict was committed; Rust was NOT allowed to override it"
                        );
                    }
                }
                ProducerOutcome::Fallback { reason } => {
                    tracing::warn!(
                        target: "dregg::sdk::lean_producer",
                        agent = ?turn.agent,
                        reason = %reason,
                        "THE SWAP producer mode (SDK): turn outside the swap-safe covered set \
                         — FENCED onto the legacy Rust path for this turn (explicit, surfaced; \
                         the named burning-down partition, not a silent Rust default)"
                    );
                }
            }
            return result;
        }
    }
    // Legacy Rust-producer path (also the only path under the `no-lean-link` platform gate).
    executor.execute(turn, ledger)
}

impl std::fmt::Debug for AgentRuntime {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AgentRuntime")
            .field("cell_id", &self.cell_id)
            .field("domain", &self.domain)
            .field("nonce", &self.nonce())
            .finish()
    }
}

/// A sub-agent spawned by a parent runtime with attenuated capabilities.
///
/// Sub-agents have their own identity and cipherclerk but operate on the same ledger
/// as their parent. Their token is strictly less powerful than the parent's.
///
/// Each sub-agent maintains its own receipt chain binding: every turn it executes
/// includes `previous_receipt_hash` linking to its last committed receipt. This
/// prevents reordering and replay of sub-agent turns.
// AUDIT[P2]: `SubAgent` exposes `pub cipherclerk: Arc<AgentCipherclerk>` and `pub token:
// HeldToken`. The `HeldToken` itself is now sealed-value (P0 fix), so its
// authority-affecting fields cannot be tampered with. But `pub federation_id:
// [u8; 32]` IS writable by an external caller holding a `&mut SubAgent`. This
// federation_id is used as the signing-message domain separator for turn
// signatures (see `SubAgent::execute`). An attacker who can mutate
// `federation_id` post-construct could cause the sub-agent to sign turns
// against the wrong federation, leading to cross-federation replay vectors.
// Severity P2: requires existing `&mut SubAgent` access, which is itself a
// privileged hold. Recommended fix: make all SubAgent fields private with
// read-only accessors (`pub fn federation_id(&self) -> [u8; 32]`).
#[derive(Debug)]
pub struct SubAgent {
    // P1-1, P1-2 (AUDIT-cipherclerk.md / AUDIT-sdk-rest.md): every field is now
    // `pub(crate)` so external callers can no longer rewrite `federation_id`
    // (the signing-message domain separator) or swap `cipherclerk` / `token`
    // post-construct. Access from outside the crate is via the read-only
    // accessor methods below.
    /// The sub-agent's cipherclerk.
    pub(crate) cipherclerk: Arc<AgentCipherclerk>,
    /// The sub-agent's cell ID.
    pub(crate) cell_id: CellId,
    /// The attenuated token this sub-agent holds.
    pub(crate) token: HeldToken,
    /// The ENFORCED capability credential: a public-key biscuit (encoded
    /// `eb2_…`) granting `service(sub_cell, method)` for exactly the method verbs
    /// the worker may invoke. Presented as [`Authorization::Token`] on every turn
    /// so the EXECUTOR's `verify_token_authorization` is the admission gate — an
    /// over-broad worker turn (a method outside `cap_methods`) is rejected by the
    /// executor itself, not by an out-of-band `cap.verify()`.
    pub(crate) cap_token: Vec<u8>,
    /// The biscuit issuer public key the worker's `cap_token` is signed under.
    /// Carried in the [`Authorization::Token`] as the
    /// [`TokenKeyRef::BiscuitIssuer`] anchor; the executor checks it against the
    /// sub-agent cell's `verification_key`.
    pub(crate) cap_issuer: [u8; 32],
    /// The method verbs the worker's `cap_token` grants (for diagnostics; the
    /// authoritative scope lives in the biscuit's `service(...)` grants).
    pub(crate) cap_methods: Vec<String>,
    /// The parent agent's public key.
    pub(crate) parent: PublicKey,
    /// The domain this sub-agent operates in.
    pub(crate) domain: String,
    /// The federation/group ID inherited from the parent runtime.
    ///
    /// In the unified lace model, this is equivalent to a `GroupId` (the
    /// reference group this agent belongs to). Used for signing messages
    /// with the correct group context. The field name is preserved for
    /// backward compatibility; semantically it is a group identifier.
    pub(crate) federation_id: [u8; 32],
    /// Shared ledger with the parent.
    ledger: Arc<Mutex<Ledger>>,
    /// Nonce counter for turn submission (incremented on each execute call).
    nonce: Mutex<u64>,
    /// The hash of the last committed receipt for this sub-agent.
    /// Used to bind each new turn to its predecessor, preventing reordering
    /// and replay of sub-agent turns.
    last_receipt_hash: Mutex<Option<[u8; 32]>>,
    /// Whether producer mode is active for this worker's turns — inherited from
    /// the parent runtime at spawn. When on (and on any native target), a
    /// worker turn on the covered set is produced by the VERIFIED Lean executor
    /// via [`produce`], exactly like a runtime turn through
    /// [`AgentRuntime::run_turn`]. This is what routes served/minted grain
    /// turns through the same producer-selection seam instead of the legacy
    /// direct Rust producer.
    lean_producer_enabled: bool,
    /// ROUTE (ii) — the HOST executor signing seed inherited from the parent
    /// runtime at spawn. When `Some`, the FRESH executor this worker builds per
    /// [`Self::execute_method`] signs the committed grain-turn receipt's
    /// `executor_signature` (Ed25519 over `canonical_executor_signed_message`), so a
    /// served / minted grain turn is forge-admissible. `None` = today's UNSIGNED
    /// worker receipts.
    executor_signing_seed: Option<[u8; 32]>,
    /// WAVE A / WELD — OWNER LIVENESS. When this worker was admitted ENVELOPED
    /// (`ToolGateway::admit_enveloped_owned`), the renter/owner ed25519 public key
    /// (`agent_platform::RenterAnchor.pubkey`) whose signature gates the worker's
    /// authority-widening turns. The FRESH executor this worker builds per
    /// [`Self::execute_method`] registers an owner-envelope verifier for this key
    /// (`dregg_turn::TurnExecutor::register_owner_envelope`), so a VALID
    /// owner-signed `Authorization::Custom` on a `Delegate`/`SetPermissions` turn
    /// RESOLVES and is accepted (liveness) — while the host, lacking the owner
    /// key, still cannot forge it (safety). `None` for a non-enveloped worker
    /// (byte-unchanged).
    owner_envelope_pubkey: Option<[u8; 32]>,
}

impl SubAgent {
    /// Get the sub-agent's public key.
    pub fn public_key(&self) -> PublicKey {
        self.cipherclerk.public_key()
    }

    /// Read-only access to the sub-agent's cipherclerk.
    pub fn cipherclerk(&self) -> &Arc<AgentCipherclerk> {
        &self.cipherclerk
    }

    /// Legacy alias for [`Self::cipherclerk`].
    #[doc(hidden)]
    pub fn cclerk(&self) -> &Arc<AgentCipherclerk> {
        self.cipherclerk()
    }

    /// Get the sub-agent's cell ID.
    pub fn cell_id(&self) -> CellId {
        self.cell_id
    }

    /// Get a reference to the sub-agent's held token.
    pub fn token(&self) -> &HeldToken {
        &self.token
    }

    /// Get the parent agent's public key.
    pub fn parent(&self) -> PublicKey {
        self.parent
    }

    /// Get the domain this sub-agent operates in.
    pub fn domain(&self) -> &str {
        &self.domain
    }

    /// Get the federation (group) id this sub-agent inherited.
    pub fn federation_id(&self) -> [u8; 32] {
        self.federation_id
    }

    /// Check whether the sub-agent's token authorizes a request.
    ///
    /// P1-4: previously delegated to [`AgentCipherclerk::verify_token`], which
    /// requires the token's `root_key` to be set (HMAC verification). Sub-agent
    /// tokens are delegated and carry a zeroed `root_key`, so `verify_token`
    /// always returned `false` — the method had no useful semantics.
    ///
    /// This implementation runs the Datalog evaluator on the structural
    /// caveat set (the same evaluator used by trusted-mode authorization),
    /// returning `true` if the request is `Allow`ed by the token's caveats and
    /// `false` for `Deny` / `Inconclusive` / parse failure. The durable
    /// binding is re-verified first so a post-receive tampering returns
    /// `false`.
    pub fn can_authorize(&self, request: &dregg_token::AuthRequest) -> bool {
        if self.token.reverify_delegation_binding().is_err() {
            return false;
        }
        match self
            .cipherclerk
            .authorize(&self.token, request, crate::VerificationMode::Trusted)
        {
            Ok(crate::AuthorizationPresentation::Trusted { trace, .. }) => {
                matches!(trace.conclusion, dregg_trace::Conclusion::Allow { .. })
            }
            // Any other presentation kind shouldn't occur from Trusted mode;
            // be conservative.
            Ok(_) => false,
            Err(_) => false,
        }
    }

    /// Read-only access to the worker's ENFORCED capability credential (the
    /// encoded biscuit presented as [`Authorization::Token`]).
    pub fn cap_token(&self) -> &[u8] {
        &self.cap_token
    }

    /// The method verbs the worker's capability credential grants (diagnostic;
    /// the authoritative scope is the biscuit's `service(...)` grants, enforced
    /// by the executor).
    pub fn cap_methods(&self) -> &[String] {
        &self.cap_methods
    }

    /// Build the [`Authorization::Token`] the worker presents on its turns.
    ///
    /// The credential is the public-key biscuit minted at spawn; the executor
    /// verifies it against the issuer anchored in the sub-agent cell's
    /// `verification_key` via [`TokenKeyRef::BiscuitIssuer`] and runs the
    /// biscuit's `service(cell, action)` cover against THIS call. An over-scope
    /// call is rejected by the executor itself.
    fn cap_authorization(&self) -> Authorization {
        Authorization::Token {
            encoded: self.cap_token.clone(),
            key_ref: TokenKeyRef::BiscuitIssuer {
                issuer_pubkey: self.cap_issuer,
            },
        }
    }

    /// Execute effects on the shared ledger using this sub-agent's cell, under
    /// the worker's default [`DEFAULT_SUBAGENT_METHOD`] scope.
    ///
    /// The worker presents its capability credential as [`Authorization::Token`],
    /// so the EXECUTOR's `verify_token_authorization` is the admission gate.
    /// Each turn is bound to this sub-agent's receipt chain via
    /// `previous_receipt_hash`, which prevents reordering and replay of
    /// sub-agent turns. The binding is updated after each successful commit.
    #[must_use = "dropping the TurnReceipt silently discards proof of execution"]
    pub fn execute(&self, effects: Vec<Effect>) -> Result<TurnReceipt, SdkError> {
        self.execute_method(DEFAULT_SUBAGENT_METHOD, effects)
    }

    /// WAVE A / WELD — pin the renter/owner ed25519 public key this worker's
    /// fresh executor registers as the owner-envelope verifier (see
    /// [`Self::owner_envelope_pubkey`]). Called by
    /// [`crate::ToolGateway::admit_enveloped_owned`] right after spawn, with the
    /// key that is ALSO stamped (hashed) into the worker cell's authority-widening
    /// permission slots — so the executor gate and the verifier answer for the
    /// SAME owner. Installs LIVENESS only; the fail-closed safety is unaffected.
    pub(crate) fn set_owner_envelope_pubkey(&mut self, owner_pubkey: [u8; 32]) {
        self.owner_envelope_pubkey = Some(owner_pubkey);
    }

    /// Execute effects under an explicit `method` verb.
    ///
    /// The worker presents its biscuit capability credential as
    /// [`Authorization::Token`]. If `method` is OUTSIDE the worker's granted
    /// scope (the biscuit's `service(cell, action)` grants fixed at spawn), the
    /// EXECUTOR rejects the turn with `TokenInsufficientCapability` — the
    /// credential is the boundary, not an out-of-band check.
    #[must_use = "dropping the TurnReceipt silently discards proof of execution"]
    pub fn execute_method(
        &self,
        method: &str,
        effects: Vec<Effect>,
    ) -> Result<TurnReceipt, SdkError> {
        let executor = {
            // ROUTE (ii): the fresh executor carries the host signing seed inherited
            // at spawn, so the committed grain-turn receipt is signed (forge-admissible).
            let mut e = executor_with_real_verifiers(self.executor_signing_seed);
            // Run under the runtime's federation id so the token verifier's
            // AuthRequest (which binds `app_id = hex(federation_id)`) and the
            // receipt-chain domain separation match the parent runtime. The
            // biscuit cover is keyed on `service(cell, action)` and the issuer
            // anchored in the cell's verification_key, so it verifies regardless
            // of federation — but keeping the executor on the same federation
            // keeps signing/domain context consistent.
            e.set_local_federation_id(self.federation_id);
            // WAVE A / WELD — OWNER LIVENESS: an ENVELOPED worker's fresh executor
            // registers the owner-envelope verifier for the renter/owner key pinned
            // at rent, so a VALID owner-signed `Authorization::Custom` on a
            // `Delegate`/`SetPermissions` turn RESOLVES and is accepted (instead of
            // `AuthModeNotRegistered`). The host, lacking the owner key, still cannot
            // forge the signature (safety unchanged). `None` = non-enveloped worker.
            if let Some(owner_pubkey) = self.owner_envelope_pubkey {
                e.register_owner_envelope(owner_pubkey);
            }
            e
        };

        let nonce = {
            let mut n = self.nonce.lock().unwrap();
            let current = *n;
            *n += 1;
            current
        };

        // Read the current receipt chain head for binding.
        let previous_receipt_hash = *self.last_receipt_hash.lock().unwrap();

        // Seed the FRESH executor's per-agent receipt-chain head from this
        // worker's last committed receipt. The executor stores the chain head
        // in-instance (`TurnExecutor::check_previous_receipt_hash` validates the
        // turn's `previous_receipt_hash` against `self`'s stored head), but we
        // build a fresh `TurnExecutor` per call, so without seeding the stored
        // head is always `None` and a worker's SECOND chained turn (which
        // presents `Some(prev)`) is rejected with `ReceiptChainMismatch`. Seeding
        // makes the per-worker provenance chain actually hold across turns — a
        // worker can submit a sequence of chained, tamper-evident turns, which is
        // exactly what an audit of a sub-agent's work trail needs.
        if let Some(prev) = previous_receipt_hash {
            executor.set_last_receipt_hash(self.cell_id, prev);
        }

        // The worker authorizes by PRESENTING its capability credential. No
        // signature is needed: a verified `Authorization::Token` is the complete
        // authorization (the executor's token path returns on success).
        let action = Action {
            target: self.cell_id,
            method: symbol(method),
            args: Vec::new(),
            authorization: self.cap_authorization(),
            preconditions: Default::default(),
            effects,
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };

        let mut forest = CallForest::new();
        forest.add_root(action);

        let turn = Turn {
            agent: self.cell_id,
            nonce,
            call_forest: forest,
            fee: 5_000,
            memo: None,
            valid_until: default_valid_until(),
            previous_receipt_hash,
            depends_on: Vec::new(),
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };

        let mut ledger = self.ledger.lock().unwrap();
        // Route the worker turn through the SAME producer-selection seam a runtime
        // turn owns (see [`produce`] / [`AgentRuntime::run_turn`]): under producer
        // mode, a covered worker turn (e.g. the served/minted grain turn) is
        // produced by the VERIFIED Lean executor, not the direct Rust producer.
        let result = produce(&executor, &turn, &mut ledger, self.lean_producer_enabled);

        match result {
            TurnResult::Committed { receipt, .. } => {
                // SECURITY: Update the receipt chain binding so the next turn
                // is linked to this one, preventing reordering and replay.
                *self.last_receipt_hash.lock().unwrap() = Some(receipt.receipt_hash());
                Ok(receipt)
            }
            TurnResult::Rejected { reason, .. } => Err(SdkError::Turn(reason)),
            TurnResult::Expired => Err(SdkError::Rejected("turn expired".to_string())),
            TurnResult::Pending => Err(SdkError::Rejected("turn pending".to_string())),
        }
    }

    /// Get the sub-agent's current nonce.
    pub fn nonce(&self) -> u64 {
        *self.nonce.lock().unwrap()
    }
}

/// Issue #46 (github.com/emberian/dregg): the SDK's turn-construction sites stamped
/// `valid_until: None`, which the Lean producer's wire marshal rejects — silently demoting
/// every SDK-built turn to the legacy Rust producer, forever. Pin `default_valid_until()`'s
/// contract directly so the sentinel can never regress back to `None` unnoticed.
#[cfg(test)]
mod default_valid_until_tests {
    use super::*;

    /// The sentinel must be `Some` (a `None` here is exactly the bug: it silently falls the
    /// turn off the verified Lean producer to the legacy Rust producer — see module docs on
    /// `default_valid_until`).
    #[test]
    fn default_valid_until_is_some() {
        assert!(
            default_valid_until().is_some(),
            "a None here silently falls every SDK-built turn off the verified Lean producer \
             (issue #46) — the sentinel must always be Some"
        );
    }

    /// The stamped deadline must be strictly in the future (wall-clock `now` at the call site,
    /// which is always <= `now` observed here) and within the declared horizon — never a block
    /// height (which would already be in the past as a timestamp and expire the turn on arrival).
    #[test]
    fn default_valid_until_is_a_future_wall_clock_horizon() {
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0);
        let stamped =
            default_valid_until().expect("must be Some, see default_valid_until_is_some");
        assert!(
            stamped > now,
            "stamped valid_until ({stamped}) must be strictly after now ({now}), or the turn \
             expires before it can ever be submitted"
        );
        assert!(
            stamped <= now + SDK_TURN_VALIDITY_HORIZON_SECS,
            "stamped valid_until ({stamped}) must not exceed the declared horizon (now={now} + \
             {SDK_TURN_VALIDITY_HORIZON_SECS}s)"
        );
    }

    /// Ratchet against the unbounded `valid_until` sentinel regrowing in a `Turn` literal
    /// this crate builds for production use.
    ///
    /// `default_valid_until()` above exists precisely so every `Turn`-constructing site in
    /// this crate can share ONE horizon policy instead of re-deriving (or omitting) it. This
    /// test doesn't re-assert that function's own contract (the two tests above already do) —
    /// it pins the narrower, source-level fact that regressed here twice already: `runtime.rs`
    /// itself (issue #46) and then `cipherclerk.rs` / `committed_turn.rs` (7 more sites, found
    /// in the same sweep that produced this test). `include_str!` reads each file at COMPILE
    /// time, so this cannot go stale against what actually ships — it fails the moment a
    /// `Turn { .. }` literal in any of these files spells out the sentinel again (`valid_until`
    /// bound to a bare `None`, trailing comma), by any author, in any function added later to
    /// these same files. This file (`runtime.rs`) is itself among the files scanned, which is
    /// why the needle below is assembled at runtime rather than written as one literal — a
    /// literal copy of it here would trivially match itself via `include_str!`.
    ///
    /// Deliberately excludes `sdk/src/tool_gateway.rs`: its one occurrence builds a `Turn`
    /// that is only ever `.hash()`-ed for local bookkeeping (`PendingTurnRegistry`) and never
    /// reaches a `TurnExecutor` — a real Turn-shaped value, but not an instance of this bug,
    /// so ratcheting it here would be scanning for the wrong thing.
    #[test]
    fn no_sdk_turn_builder_rebuilds_the_unbounded_valid_until_sentinel() {
        let files: &[(&str, &str)] = &[
            ("runtime.rs", include_str!("runtime.rs")),
            ("cipherclerk.rs", include_str!("cipherclerk.rs")),
            ("committed_turn.rs", include_str!("committed_turn.rs")),
        ];
        // Assembled rather than written as one literal: this file is itself in `files`
        // above, so a literal copy of the full needle here would match itself.
        let sentinel_field = "valid_until";
        let sentinel_value = "None";
        let needle = format!("{sentinel_field}: {sentinel_value},");
        for (name, src) in files {
            assert!(
                !src.contains(&needle),
                "{name} builds a Turn with `{sentinel_field}` bound to a bare `{sentinel_value}` \
                 — this turn will NEVER expire (the executor's expiration check is skipped \
                 entirely when this field is `{sentinel_value}`, turn/src/executor/execute.rs:426) \
                 and falls off the verified Lean producer (issue #46). Use \
                 `crate::runtime::default_valid_until()` instead, as every other Turn literal in \
                 these files now does."
            );
        }
    }
}
