//! # dregg-chutes-e2ee
//!
//! Attested, end-to-end-encrypted client for **Chutes** (Bittensor SN64) LLM inference.
//!
//! The transport encrypts an OpenAI chat request to a TEE-attested ML-KEM-768 key so that
//! only a **DCAP-verified enclave** can decrypt it. The crypto stack is a byte-compatible
//! port of the authoritative Chutes reference (`chutes_e2ee/crypto.py`): ML-KEM-768
//! (FIPS 203, via PQClean C — the SAME C the Python reference links) → HKDF-SHA256 →
//! ChaCha20-Poly1305 (IETF, 12-byte nonce, NO AAD) over gzip.
//!
//! ## Our value-add over the reference client: a fail-closed attestation gate
//!
//! The reference client encrypts to whatever `e2e_pubkey` discovery hands back — it never
//! attests. This client, before encrypting, fetches the instance's TDX quote
//! (`/chutes/{id}/evidence?nonce=<fresh 64-hex>`) and runs [`dregg_tee_verify`]'s DCAP
//! verifier, requiring: the full DCAP crypto chain to the pinned Intel SGX Root CA; the
//! FIXED report_data string binding `SHA-256(ascii(nonce_hex) ‖ ascii(e2e_pubkey_b64))`
//! (kills replay + proves the pubkey is the attested one); a measurement match against the
//! pinned Chutes registry; and an accepted TCB status. Only an attested `e2e_pubkey` is
//! encrypted to, and that instance is pinned as `X-Instance-Id`. Attestation failure →
//! `Err`, no request sent. See [`attested_chat_completion`].
//!
//! ## Entry points
//!
//! - [`attested_chat_completion`] — the full attested round trip (re-attests every call).
//! - [`ChutesTeeBackend`] — the same guarantee as a `dregg_narrator::ConverseBackend`, so the
//!   fiction engine's narrator can run inside the enclave. This is the path you want for
//!   repeated calls: it caches the verified instance ([`session::SessionCache`]) so a turn costs
//!   an ML-KEM encapsulation rather than a ~12.5s attestation.
//! - [`crypto::build_e2ee_request`] / [`crypto::decrypt_response`] — the transport-free
//!   crypto core (exact `crypto.py` port), independently testable offline.
//! - [`discovery::discover`] / [`discovery::resolve_chute_id`] — discovery + model mapping.
//! - [`attest::attest_chute`] — the attestation gate in isolation.
//! - [`client::invoke_encrypted`] — the per-request half ONLY (no attestation); sound only over
//!   an already-attested `e2e_pubkey`.
//!
//! ## Narrating through the enclave
//!
//! `DREGG_NARRATOR=chutes-tee` + `DREGG_NARRATOR_MODEL=<a -TEE chute>` + a Chutes key selects the
//! attested narrator; [`attested_narrator_from_env`] composes it into a `dregg_narrator::Narrator`
//! and returns `Err` (never a quiet downgrade to plain inference) if attestation is selected but
//! unavailable. See [`narrator_backend::TeeNarratorEnv`] for the full env surface, including the
//! attestation TTL and the pricing requirement.

pub mod attest;
pub mod client;
pub mod crypto;
pub mod discovery;
pub mod error;
pub mod gpu;
pub mod narrator_backend;
pub mod session;

pub use attest::{
    attest_chute, quote_sha256_hex, recheck_archived_binding, AttestationRecord, AttestedInstance,
    CollateralSource, VerifierConfig,
};
pub use client::{attested_chat_completion, invoke_encrypted, InvokeError, E2E_PATH};
pub use crypto::{
    build_e2ee_request, decrypt_response, decrypt_stream_chunk, decrypt_stream_init, CryptoError,
    E2eeRequest, INFO_REQ, INFO_RESP, INFO_STREAM, MLKEM_CT_SIZE, MLKEM_PK_SIZE, MLKEM_SK_SIZE,
    SHARED_SECRET_SIZE, TAG_SIZE,
};
pub use discovery::{
    discover, model_pricing, resolve_chute_id, InstanceInfo, Instances, ProviderPricing,
    DEFAULT_API_BASE, DEFAULT_MODELS_BASE,
};
pub use error::ClientError;
pub use gpu::{GpuAttestation, GpuCollateralSource, GpuEvidenceItem, GpuGate};
pub use narrator_backend::{attested_narrator_from_env, ChutesTeeBackend, Invoker, TeeNarratorEnv};
pub use session::{
    AttestedSession, Attestor, ChutesAttestor, Clock, Lease, SessionCache, DEFAULT_TTL_SECS,
};
