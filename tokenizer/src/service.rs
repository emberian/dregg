//! Tokenizer daemon service — holds private keys, serves seal/unseal over Unix socket.
//!
//! The daemon listens on a Unix domain socket. Clients connect and send
//! [`Request`] messages; the daemon processes them and returns [`Response`]
//! messages. The private key material never leaves this process.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{UnixListener, UnixStream};
use tokio::sync::{RwLock, watch};

use crate::encrypt::{SealedSecret, TokenizerKeypair};
use crate::error::TokenizerError;
use crate::protocol::{HEADER_SIZE, MAX_PAYLOAD_SIZE, Request, Response};

/// Configuration for the tokenizer service.
#[derive(Clone, Debug)]
pub struct ServiceConfig {
    /// Path to the Unix socket.
    pub socket_path: PathBuf,
    /// Path to the key store file (serialized keypairs).
    pub key_store_path: PathBuf,
}

impl ServiceConfig {
    /// Default socket path.
    pub fn default_socket_path() -> PathBuf {
        PathBuf::from("/tmp/pyana-tokenizer.sock")
    }

    /// Default key store path (~/.pyana/tokenizer-keys).
    pub fn default_key_store_path() -> PathBuf {
        directories::ProjectDirs::from("dev", "pyana", "pyana")
            .map(|d| d.data_dir().join("tokenizer-keys"))
            .unwrap_or_else(|| PathBuf::from("/tmp/pyana-tokenizer-keys"))
    }
}

impl Default for ServiceConfig {
    fn default() -> Self {
        Self {
            socket_path: Self::default_socket_path(),
            key_store_path: Self::default_key_store_path(),
        }
    }
}

/// The key ring holds the current and historical keypairs.
///
/// The newest keypair (last in the vec) is used for sealing.
/// All keypairs are tried (newest-first) for unsealing.
pub struct KeyRing {
    /// Keypairs ordered from oldest to newest.
    keypairs: Vec<TokenizerKeypair>,
}

impl KeyRing {
    /// Create a new keyring with a single generated keypair.
    pub fn generate() -> Self {
        Self {
            keypairs: vec![TokenizerKeypair::generate()],
        }
    }

    /// Create from persisted key bytes.
    ///
    /// Each entry is a 32-byte secret key.
    pub fn from_stored_keys(keys: Vec<[u8; 32]>) -> Self {
        let keypairs = keys.into_iter().map(TokenizerKeypair::from_bytes).collect();
        Self { keypairs }
    }

    /// Get the current (newest) public key.
    pub fn current_public_key(&self) -> [u8; 32] {
        self.keypairs
            .last()
            .expect("keyring must have at least one key")
            .public_key_bytes()
    }

    /// Seal plaintext with the current (newest) key.
    pub fn seal(&self, plaintext: &[u8]) -> Result<Vec<u8>, TokenizerError> {
        let kp = self
            .keypairs
            .last()
            .expect("keyring must have at least one key");
        let sealed = SealedSecret::seal(plaintext, kp.public_key())?;
        Ok(sealed.to_bytes())
    }

    /// Unseal by trying all keys (newest first).
    pub fn unseal(&self, sealed_bytes: &[u8]) -> Result<Vec<u8>, TokenizerError> {
        let sealed = SealedSecret::from_bytes(sealed_bytes)?;

        // Try newest key first (most likely to succeed).
        for kp in self.keypairs.iter().rev() {
            if let Ok(plaintext) = kp.unseal(&sealed) {
                return Ok(plaintext);
            }
        }

        Err(TokenizerError::Decryption(
            "no key in the ring could decrypt this secret".into(),
        ))
    }

    /// Rotate: generate a new keypair, append it, return new public key.
    pub fn rotate(&mut self) -> [u8; 32] {
        let new_kp = TokenizerKeypair::generate();
        let pk = new_kp.public_key_bytes();
        self.keypairs.push(new_kp);
        pk
    }

    /// Number of keys in the ring.
    pub fn len(&self) -> usize {
        self.keypairs.len()
    }

    /// Whether the ring is empty (should never be).
    pub fn is_empty(&self) -> bool {
        self.keypairs.is_empty()
    }
}

/// The running tokenizer service.
pub struct TokenizerService {
    config: ServiceConfig,
    keyring: Arc<RwLock<KeyRing>>,
    shutdown_tx: watch::Sender<bool>,
    shutdown_rx: watch::Receiver<bool>,
}

impl TokenizerService {
    /// Create a new service with the given config and keyring.
    pub fn new(config: ServiceConfig, keyring: KeyRing) -> Self {
        let (shutdown_tx, shutdown_rx) = watch::channel(false);
        Self {
            config,
            keyring: Arc::new(RwLock::new(keyring)),
            shutdown_tx,
            shutdown_rx,
        }
    }

    /// Start serving on the configured Unix socket.
    ///
    /// This runs until shutdown is signaled (via a `Shutdown` request or the
    /// returned handle is dropped).
    pub async fn serve(&self) -> Result<(), TokenizerError> {
        // Remove stale socket file if it exists.
        let _ = std::fs::remove_file(&self.config.socket_path);

        // Ensure parent directory exists.
        if let Some(parent) = self.config.socket_path.parent() {
            std::fs::create_dir_all(parent).map_err(|e| {
                TokenizerError::Protocol(format!(
                    "failed to create socket directory {}: {}",
                    parent.display(),
                    e
                ))
            })?;
        }

        let listener = UnixListener::bind(&self.config.socket_path).map_err(|e| {
            TokenizerError::Protocol(format!(
                "failed to bind {}: {}",
                self.config.socket_path.display(),
                e
            ))
        })?;

        // Set socket permissions to owner-only on Unix.
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let _ = std::fs::set_permissions(
                &self.config.socket_path,
                std::fs::Permissions::from_mode(0o600),
            );
        }

        eprintln!(
            "[tokenizer] listening on {}",
            self.config.socket_path.display()
        );

        let mut shutdown_rx = self.shutdown_rx.clone();

        loop {
            tokio::select! {
              accept_result = listener.accept() => {
                match accept_result {
                  Ok((stream, _addr)) => {
                    let keyring = Arc::clone(&self.keyring);
                    let shutdown_tx = self.shutdown_tx.clone();
                    tokio::spawn(async move {
                      if let Err(e) = handle_connection(stream, keyring, shutdown_tx).await {
                        eprintln!("[tokenizer] connection error: {}", e);
                      }
                    });
                  }
                  Err(e) => {
                    eprintln!("[tokenizer] accept error: {}", e);
                  }
                }
              }
              _ = shutdown_rx.changed() => {
                if *shutdown_rx.borrow() {
                  eprintln!("[tokenizer] shutting down");
                  break;
                }
              }
            }
        }

        // Cleanup socket file.
        let _ = std::fs::remove_file(&self.config.socket_path);
        Ok(())
    }

    /// Signal shutdown from outside.
    pub fn shutdown(&self) {
        let _ = self.shutdown_tx.send(true);
    }

    /// Get a reference to the keyring (for testing).
    pub fn keyring(&self) -> &Arc<RwLock<KeyRing>> {
        &self.keyring
    }

    /// Get the socket path.
    pub fn socket_path(&self) -> &Path {
        &self.config.socket_path
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keyring_seal_unseal_roundtrip() {
        let ring = KeyRing::generate();
        let plaintext = b"seal-unseal-test";
        let sealed = ring.seal(plaintext).unwrap();
        let decrypted = ring.unseal(&sealed).unwrap();
        assert_eq!(decrypted, plaintext);
    }

    #[test]
    fn keyring_sealed_differs_from_plaintext() {
        let ring = KeyRing::generate();
        let plaintext = b"not-identity";
        let sealed = ring.seal(plaintext).unwrap();
        assert_ne!(&sealed, plaintext);
        assert!(sealed.len() > plaintext.len());
    }

    #[test]
    fn keyring_wrong_key_fails() {
        let ring1 = KeyRing::generate();
        let ring2 = KeyRing::generate();

        let sealed = ring1.seal(b"secret-data").unwrap();
        let result = ring2.unseal(&sealed);
        assert!(result.is_err());
    }

    #[test]
    fn keyring_rotate_preserves_old_decryption() {
        let mut ring = KeyRing::generate();
        let sealed_before = ring.seal(b"before-rotate").unwrap();

        ring.rotate();
        assert_eq!(ring.len(), 2);

        // Old sealed data still decrypts after rotation.
        let decrypted = ring.unseal(&sealed_before).unwrap();
        assert_eq!(decrypted, b"before-rotate");
    }

    #[test]
    fn keyring_rotate_changes_public_key() {
        let mut ring = KeyRing::generate();
        let pk1 = ring.current_public_key();
        let pk2 = ring.rotate();
        assert_ne!(pk1, pk2);
        assert_eq!(ring.current_public_key(), pk2);
    }

    #[test]
    fn keyring_from_stored_keys() {
        // Generate a keypair, seal something, then reconstruct from stored bytes.
        let mut key_bytes = [0u8; 32];
        getrandom::fill(&mut key_bytes).unwrap();

        let ring = KeyRing::from_stored_keys(vec![key_bytes]);
        assert_eq!(ring.len(), 1);

        let sealed = ring.seal(b"stored-key-test").unwrap();
        let decrypted = ring.unseal(&sealed).unwrap();
        assert_eq!(decrypted, b"stored-key-test");

        // Reconstruct again -- same key bytes should produce same public key.
        let ring2 = KeyRing::from_stored_keys(vec![key_bytes]);
        assert_eq!(ring.current_public_key(), ring2.current_public_key());
        // And should decrypt the same sealed data.
        let decrypted2 = ring2.unseal(&sealed).unwrap();
        assert_eq!(decrypted2, b"stored-key-test");
    }

    #[test]
    fn keyring_multiple_rotations() {
        let mut ring = KeyRing::generate();
        let mut sealed_data = Vec::new();

        for i in 0..5 {
            let msg = format!("message-{}", i);
            sealed_data.push(ring.seal(msg.as_bytes()).unwrap());
            ring.rotate();
        }

        assert_eq!(ring.len(), 6); // 1 initial + 5 rotations

        // All sealed data should still decrypt.
        for (i, sealed) in sealed_data.iter().enumerate() {
            let decrypted = ring.unseal(sealed).unwrap();
            assert_eq!(decrypted, format!("message-{}", i).as_bytes());
        }
    }

    #[test]
    fn keyring_unseal_garbage_fails() {
        let ring = KeyRing::generate();
        let result = ring.unseal(&[0xDE, 0xAD, 0xBE, 0xEF]);
        assert!(result.is_err());
    }
}

/// Handle a single client connection.
async fn handle_connection(
    mut stream: UnixStream,
    keyring: Arc<RwLock<KeyRing>>,
    shutdown_tx: watch::Sender<bool>,
) -> Result<(), TokenizerError> {
    loop {
        // Read request.
        let request = match read_frame::<Request>(&mut stream).await {
            Ok(req) => req,
            Err(TokenizerError::ConnectionClosed) => return Ok(()),
            Err(e) => return Err(e),
        };

        // Process and respond.
        let response = process_request(&request, &keyring, &shutdown_tx).await;
        let is_shutdown = matches!(response, Response::ShutdownAck);

        write_frame(&mut stream, &response).await?;

        if is_shutdown {
            return Ok(());
        }
    }
}

/// Process a single request.
async fn process_request(
    request: &Request,
    keyring: &Arc<RwLock<KeyRing>>,
    shutdown_tx: &watch::Sender<bool>,
) -> Response {
    match request {
        Request::Seal { plaintext } => {
            let ring = keyring.read().await;
            match ring.seal(plaintext) {
                Ok(data) => Response::Sealed { data },
                Err(e) => Response::Error {
                    message: e.to_string(),
                },
            }
        }
        Request::Unseal { sealed } => {
            let ring = keyring.read().await;
            match ring.unseal(sealed) {
                Ok(plaintext) => Response::Unsealed { plaintext },
                Err(e) => Response::Error {
                    message: e.to_string(),
                },
            }
        }
        Request::GetPublicKey => {
            let ring = keyring.read().await;
            Response::PublicKey {
                key: ring.current_public_key(),
            }
        }
        Request::Rotate => {
            let mut ring = keyring.write().await;
            let new_pk = ring.rotate();
            Response::Rotated {
                new_public_key: new_pk,
            }
        }
        Request::Shutdown => {
            let _ = shutdown_tx.send(true);
            Response::ShutdownAck
        }
    }
}

// =============================================================================
// Framing helpers (same format as pyana-wire: 4-byte LE length + postcard)
// =============================================================================

/// Write a framed message.
pub(crate) async fn write_frame<T: serde::Serialize>(
    stream: &mut UnixStream,
    msg: &T,
) -> Result<(), TokenizerError> {
    let payload = postcard::to_allocvec(msg)
        .map_err(|e| TokenizerError::Encoding(format!("serialization failed: {}", e)))?;

    let len = payload.len() as u32;
    if len > MAX_PAYLOAD_SIZE {
        return Err(TokenizerError::Encoding(format!(
            "message too large: {} bytes (max {})",
            len, MAX_PAYLOAD_SIZE
        )));
    }

    stream
        .write_all(&len.to_le_bytes())
        .await
        .map_err(|e| TokenizerError::Protocol(e.to_string()))?;
    stream
        .write_all(&payload)
        .await
        .map_err(|e| TokenizerError::Protocol(e.to_string()))?;
    stream
        .flush()
        .await
        .map_err(|e| TokenizerError::Protocol(e.to_string()))?;

    Ok(())
}

/// Read a framed message.
pub(crate) async fn read_frame<T: serde::de::DeserializeOwned>(
    stream: &mut UnixStream,
) -> Result<T, TokenizerError> {
    let mut header = [0u8; HEADER_SIZE];
    match stream.read_exact(&mut header).await {
        Ok(_) => {}
        Err(e) if e.kind() == std::io::ErrorKind::UnexpectedEof => {
            return Err(TokenizerError::ConnectionClosed);
        }
        Err(e) => return Err(TokenizerError::Protocol(e.to_string())),
    }

    let payload_len = u32::from_le_bytes(header);
    if payload_len > MAX_PAYLOAD_SIZE {
        return Err(TokenizerError::Encoding(format!(
            "message too large: {} bytes (max {})",
            payload_len, MAX_PAYLOAD_SIZE
        )));
    }

    let mut payload = vec![0u8; payload_len as usize];
    stream
        .read_exact(&mut payload)
        .await
        .map_err(|e| TokenizerError::Protocol(e.to_string()))?;

    postcard::from_bytes(&payload)
        .map_err(|e| TokenizerError::Encoding(format!("deserialization failed: {}", e)))
}
