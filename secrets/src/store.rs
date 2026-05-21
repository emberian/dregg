//! Secret store trait and core types.

use std::collections::HashMap;
use std::fmt;

use serde::{Deserialize, Serialize};
use zeroize::{Zeroize, ZeroizeOnDrop, Zeroizing};

use crate::error::SecretStoreError;

/// Identifier for a stored secret, scoped by namespace and key.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SecretId {
    /// Namespace for grouping secrets (e.g., "oauth", "auth-server", "app").
    pub namespace: String,
    /// Key within the namespace (e.g., "github:client_secret", "signing_key").
    pub key: String,
}

impl SecretId {
    /// Create a new secret identifier.
    pub fn new(namespace: impl Into<String>, key: impl Into<String>) -> Self {
        Self {
            namespace: namespace.into(),
            key: key.into(),
        }
    }
}

impl fmt::Display for SecretId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", self.namespace, self.key)
    }
}

/// A secret value that automatically zeroes its memory on drop.
#[derive(Clone, Zeroize, ZeroizeOnDrop)]
pub struct SecretValue {
    inner: Vec<u8>,
}

impl SecretValue {
    /// Create a new secret value.
    pub fn new(data: Vec<u8>) -> Self {
        Self { inner: data }
    }

    /// Create from a string.
    pub fn from_str(s: &str) -> Self {
        Self::new(s.as_bytes().to_vec())
    }

    /// Access the raw bytes.
    pub fn as_bytes(&self) -> &[u8] {
        &self.inner
    }

    /// Try to interpret as UTF-8 string.
    pub fn as_str(&self) -> Option<&str> {
        std::str::from_utf8(&self.inner).ok()
    }

    /// Clone and return the inner bytes wrapped in [`Zeroizing`].
    ///
    /// The returned `Zeroizing<Vec<u8>>` will automatically zero its contents
    /// when dropped, ensuring secret material does not linger in memory after use.
    /// This is necessary because `SecretValue` implements `ZeroizeOnDrop`, which
    /// prevents moving the inner vec out directly.
    pub fn to_bytes(&self) -> Zeroizing<Vec<u8>> {
        Zeroizing::new(self.inner.clone())
    }

    /// Length of the secret value.
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Whether the secret value is empty.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
}

impl fmt::Debug for SecretValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SecretValue([REDACTED, {} bytes])", self.inner.len())
    }
}

/// Metadata about a stored secret.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SecretMetadata {
    /// The secret's identifier.
    pub id: SecretId,
    /// Creation timestamp (Unix seconds).
    pub created_at: i64,
    /// Last update timestamp (Unix seconds).
    pub updated_at: i64,
    /// User-defined labels.
    pub labels: HashMap<String, String>,
}

/// Pluggable secret storage backend.
///
/// Implementations must be thread-safe. All operations are synchronous
/// to keep the interface simple — async wrappers can be added at the
/// call site if needed.
pub trait SecretStore: Send + Sync {
    /// Store a secret. Overwrites if it already exists.
    fn put(&self, id: &SecretId, value: &[u8]) -> Result<(), SecretStoreError>;

    /// Retrieve a secret. Returns `None` if not found.
    fn get(&self, id: &SecretId) -> Result<Option<SecretValue>, SecretStoreError>;

    /// Delete a secret. Returns `true` if it existed.
    fn delete(&self, id: &SecretId) -> Result<bool, SecretStoreError>;

    /// Check if a secret exists.
    fn exists(&self, id: &SecretId) -> Result<bool, SecretStoreError>;

    /// List all secrets in a namespace.
    fn list(&self, namespace: &str) -> Result<Vec<SecretMetadata>, SecretStoreError>;
}

/// A composite secret store that tries multiple backends in order.
///
/// Typically: try keychain first, fall back to encrypted file.
///
/// # Timing side-channel
///
/// The `get()` and `exists()` methods return early when a key is found in an
/// earlier backend, which reveals to a timing observer which backend holds the
/// secret. This is an accepted trade-off for performance: the identity of the
/// backend (keychain vs. encrypted file) is not considered secret. If backend
/// identity must be hidden, use a single backend or add synthetic delays.
pub struct CompositeStore {
    backends: Vec<Box<dyn SecretStore>>,
}

impl CompositeStore {
    /// Create a new composite store with the given backends (tried in order).
    pub fn new(backends: Vec<Box<dyn SecretStore>>) -> Self {
        Self { backends }
    }
}

impl SecretStore for CompositeStore {
    fn put(&self, id: &SecretId, value: &[u8]) -> Result<(), SecretStoreError> {
        // Write to ALL backends for redundancy. If any backend succeeds,
        // the operation is considered successful. Errors from individual
        // backends are collected but only returned if ALL fail.
        if self.backends.is_empty() {
            return Err(SecretStoreError::StorePath("no backends configured".into()));
        }
        let mut last_err = None;
        let mut any_success = false;
        for backend in &self.backends {
            match backend.put(id, value) {
                Ok(()) => any_success = true,
                Err(e) => last_err = Some(e),
            }
        }
        if any_success {
            Ok(())
        } else {
            Err(last_err.expect("at least one backend was tried"))
        }
    }

    fn get(&self, id: &SecretId) -> Result<Option<SecretValue>, SecretStoreError> {
        // Try backends in order, return first found value. If a backend returns
        // Ok(None), continue to the next. Collect errors so that if ALL backends
        // fail (no Ok at all), we surface the last error instead of a misleading
        // Ok(None).
        let mut errors: Vec<SecretStoreError> = Vec::new();
        let mut any_ok = false;
        for backend in &self.backends {
            match backend.get(id) {
                Ok(Some(v)) => return Ok(Some(v)),
                Ok(None) => {
                    any_ok = true;
                    continue;
                }
                Err(e) => {
                    errors.push(e);
                    continue;
                }
            }
        }
        // If at least one backend responded Ok(None), the secret genuinely
        // doesn't exist in that backend — return None.
        if any_ok {
            return Ok(None);
        }
        // All backends errored — return the last error.
        match errors.pop() {
            Some(e) => Err(e),
            None => Ok(None), // no backends configured (shouldn't happen)
        }
    }

    fn delete(&self, id: &SecretId) -> Result<bool, SecretStoreError> {
        // Try to delete from ALL backends. If at least one succeeds, the
        // operation is considered successful. Errors are collected and only
        // returned if ALL backends fail.
        let mut deleted = false;
        let mut errors: Vec<SecretStoreError> = Vec::new();
        let mut any_ok = false;
        for backend in &self.backends {
            match backend.delete(id) {
                Ok(true) => {
                    deleted = true;
                    any_ok = true;
                }
                Ok(false) => {
                    any_ok = true;
                }
                Err(e) => {
                    errors.push(e);
                }
            }
        }
        if any_ok {
            return Ok(deleted);
        }
        // All backends errored — return the last error.
        match errors.pop() {
            Some(e) => Err(e),
            None => Ok(false), // no backends configured
        }
    }

    fn exists(&self, id: &SecretId) -> Result<bool, SecretStoreError> {
        // Try backends in order. If any reports Ok(true), return immediately.
        // If at least one returns Ok(false), the secret doesn't exist in that
        // backend. Errors are collected and returned only if ALL backends fail.
        let mut errors: Vec<SecretStoreError> = Vec::new();
        let mut any_ok = false;
        for backend in &self.backends {
            match backend.exists(id) {
                Ok(true) => return Ok(true),
                Ok(false) => {
                    any_ok = true;
                }
                Err(e) => {
                    errors.push(e);
                }
            }
        }
        if any_ok {
            return Ok(false);
        }
        // All backends errored — return the last error.
        match errors.pop() {
            Some(e) => Err(e),
            None => Ok(false), // no backends configured
        }
    }

    fn list(&self, namespace: &str) -> Result<Vec<SecretMetadata>, SecretStoreError> {
        // Merge results from all backends that succeed, dedup by ID. If at
        // least one backend succeeds, return the merged listing. If ALL
        // backends fail, return the last error.
        let mut seen = std::collections::HashSet::new();
        let mut result = Vec::new();
        let mut errors: Vec<SecretStoreError> = Vec::new();
        let mut any_ok = false;
        for backend in &self.backends {
            match backend.list(namespace) {
                Ok(entries) => {
                    any_ok = true;
                    for entry in entries {
                        if seen.insert(entry.id.clone()) {
                            result.push(entry);
                        }
                    }
                }
                Err(e) => {
                    errors.push(e);
                }
            }
        }
        if any_ok {
            return Ok(result);
        }
        // All backends errored — return the last error.
        match errors.pop() {
            Some(e) => Err(e),
            None => Ok(result), // no backends configured
        }
    }
}
