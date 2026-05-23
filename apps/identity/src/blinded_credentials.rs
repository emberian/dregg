//! Anonymous credential distribution via blinded queue.
//!
//! A university (issuer) batches N alumni credentials into a [`BlindedQueue`]
//! (via [`FairDistributionEndpoint`]). Each alumnus withdraws one credential
//! without the university learning which credential maps to which student.
//!
//! # Protocol
//!
//! 1. **Issuer commits**: for each credential, compute
//!    `commitment = blake3("blinded-queue-commitment" || cert_bytes || randomness)`
//!    and POST to `/queue/credentials/commit`.
//! 2. **Alumnus withdraws**: generate a nullifier and Merkle membership proof,
//!    POST to `/queue/credentials/consume`.
//! 3. **After N consumes**: the queue is empty; the (N+1)th consume fails.
//!
//! # Framework primitives used
//!
//! - `AppServer::with_blinded_endpoint(path, endpoint)` — mounts the endpoint.
//! - `FairDistributionEndpoint::new(capacity)` — wraps [`BlindedQueue`].

use pyana_app_framework::blinded_endpoint::FairDistributionEndpoint;

/// Build a credential-distribution blinded endpoint.
///
/// * `capacity` — maximum number of commitments (equal to batch size N).
pub fn credential_blinded_endpoint(capacity: usize) -> FairDistributionEndpoint {
    FairDistributionEndpoint::new(capacity)
}
