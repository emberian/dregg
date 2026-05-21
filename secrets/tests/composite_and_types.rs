//! Tests for CompositeStore and SecretValue/SecretId types.

use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use pyana_secrets::{
    CompositeStore, EncryptedFileStore, SecretId, SecretStore, SecretStoreError, SecretValue,
};

fn temp_dir_path() -> PathBuf {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!(
        "pyana-secrets-composite-test-{}-{}",
        std::process::id(),
        id
    ))
}

fn make_store(dir: &PathBuf) -> EncryptedFileStore {
    let _ = fs::remove_dir_all(dir);
    let mut key = [0u8; 32];
    getrandom::fill(&mut key).unwrap();
    EncryptedFileStore::new(dir.clone(), key)
}

#[test]
fn secret_value_from_str_roundtrip() {
    let sv = SecretValue::from_str("hello-world");
    assert_eq!(sv.as_str(), Some("hello-world"));
    assert_eq!(sv.as_bytes(), b"hello-world");
    assert_eq!(sv.len(), 11);
    assert!(!sv.is_empty());
}

#[test]
fn secret_value_debug_redacts() {
    let sv = SecretValue::new(b"super-secret".to_vec());
    let debug = format!("{:?}", sv);
    assert!(!debug.contains("super-secret"));
    assert!(debug.contains("REDACTED"));
    assert!(debug.contains("12 bytes"));
}

#[test]
fn secret_id_display() {
    let id = SecretId::new("oauth", "github:token");
    assert_eq!(format!("{}", id), "oauth/github:token");
}

#[test]
fn composite_store_put_get_with_single_backend() {
    let dir = temp_dir_path();
    let store = make_store(&dir);
    let composite = CompositeStore::new(vec![Box::new(store)]);

    let id = SecretId::new("test", "composite-single");
    composite.put(&id, b"composite-value").unwrap();

    let retrieved = composite.get(&id).unwrap().unwrap();
    assert_eq!(retrieved.as_bytes(), b"composite-value");

    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn composite_store_fallback_on_get() {
    let dir1 = temp_dir_path();
    let dir2 = temp_dir_path();
    let store1 = make_store(&dir1);
    let store2 = make_store(&dir2);

    // Put only in store2.
    let id = SecretId::new("test", "fallback");
    store2.put(&id, b"in-second").unwrap();

    let composite = CompositeStore::new(vec![Box::new(store1), Box::new(store2)]);
    let retrieved = composite.get(&id).unwrap().unwrap();
    assert_eq!(retrieved.as_bytes(), b"in-second");

    let _ = fs::remove_dir_all(&dir1);
    let _ = fs::remove_dir_all(&dir2);
}

#[test]
fn composite_store_delete_removes_from_all() {
    let dir1 = temp_dir_path();
    let dir2 = temp_dir_path();
    let store1 = make_store(&dir1);
    let store2 = make_store(&dir2);

    let id = SecretId::new("test", "delete-both");
    store1.put(&id, b"val").unwrap();
    store2.put(&id, b"val").unwrap();

    let composite = CompositeStore::new(vec![Box::new(store1), Box::new(store2)]);
    let deleted = composite.delete(&id).unwrap();
    assert!(deleted);

    assert!(composite.get(&id).unwrap().is_none());

    let _ = fs::remove_dir_all(&dir1);
    let _ = fs::remove_dir_all(&dir2);
}

#[test]
fn composite_store_list_merges_and_deduplicates() {
    let dir1 = temp_dir_path();
    let dir2 = temp_dir_path();
    let store1 = make_store(&dir1);
    let store2 = make_store(&dir2);

    store1.put(&SecretId::new("ns", "k1"), b"v1").unwrap();
    store1.put(&SecretId::new("ns", "k2"), b"v2").unwrap();
    store2.put(&SecretId::new("ns", "k2"), b"v2").unwrap();
    store2.put(&SecretId::new("ns", "k3"), b"v3").unwrap();

    let composite = CompositeStore::new(vec![Box::new(store1), Box::new(store2)]);
    let list = composite.list("ns").unwrap();
    // k2 is in both but should only appear once.
    assert_eq!(list.len(), 3);

    let _ = fs::remove_dir_all(&dir1);
    let _ = fs::remove_dir_all(&dir2);
}

#[test]
fn composite_store_exists() {
    let dir = temp_dir_path();
    let store = make_store(&dir);
    let id = SecretId::new("test", "exists-check");
    store.put(&id, b"val").unwrap();

    let composite = CompositeStore::new(vec![Box::new(store)]);
    assert!(composite.exists(&id).unwrap());
    assert!(!composite.exists(&SecretId::new("test", "nope")).unwrap());

    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn composite_store_no_backends_errors() {
    let composite = CompositeStore::new(vec![]);
    let id = SecretId::new("test", "no-backend");
    let result = composite.put(&id, b"val");
    assert!(result.is_err());
}

#[test]
fn wrong_key_returns_crypto_error_not_garbage() {
    let dir = temp_dir_path();
    let mut key_a = [0u8; 32];
    getrandom::fill(&mut key_a).unwrap();
    let store_a = EncryptedFileStore::new(dir.clone(), key_a);

    let id = SecretId::new("test", "wrong-key-integration");
    store_a.put(&id, b"confidential-data").unwrap();

    // Second store with different key, same dir.
    let mut key_b = [0u8; 32];
    getrandom::fill(&mut key_b).unwrap();
    let store_b = EncryptedFileStore::new(dir.clone(), key_b);

    match store_b.get(&id) {
        Ok(Some(_)) => panic!("decrypted with wrong key"),
        Ok(None) => panic!("file exists, should not be None"),
        Err(SecretStoreError::Crypto(_)) => {} // Expected.
        Err(e) => panic!("expected Crypto error, got: {:?}", e),
    }

    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn overwrite_replaces_value() {
    let dir = temp_dir_path();
    let store = make_store(&dir);
    let id = SecretId::new("test", "overwrite-value");

    store.put(&id, b"original").unwrap();
    assert_eq!(store.get(&id).unwrap().unwrap().as_bytes(), b"original");

    store.put(&id, b"replaced").unwrap();
    assert_eq!(store.get(&id).unwrap().unwrap().as_bytes(), b"replaced");

    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn encrypted_on_disk_is_not_plaintext() {
    let dir = temp_dir_path();
    let mut key = [0u8; 32];
    getrandom::fill(&mut key).unwrap();
    let store = EncryptedFileStore::new(dir.clone(), key);

    let id = SecretId::new("test", "not-plaintext");
    let secret = b"plaintext-value-here-1234567890";
    store.put(&id, secret).unwrap();

    // Read all files in the namespace directory; none should contain the plaintext.
    let ns_dir = dir.join("test");
    for entry in fs::read_dir(&ns_dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().map(|e| e == "enc").unwrap_or(false) {
            let raw = fs::read(&path).unwrap();
            // Encrypted data must differ from plaintext.
            assert_ne!(&raw[..], &secret[..]);
            // Must be larger due to nonce + tag overhead.
            assert!(raw.len() > secret.len());
        }
    }

    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn list_after_deletions_correct_count() {
    let dir = temp_dir_path();
    let store = make_store(&dir);

    store.put(&SecretId::new("ns", "k1"), b"v1").unwrap();
    store.put(&SecretId::new("ns", "k2"), b"v2").unwrap();
    store.put(&SecretId::new("ns", "k3"), b"v3").unwrap();
    assert_eq!(store.list("ns").unwrap().len(), 3);

    store.delete(&SecretId::new("ns", "k2")).unwrap();
    assert_eq!(store.list("ns").unwrap().len(), 2);

    store.delete(&SecretId::new("ns", "k1")).unwrap();
    store.delete(&SecretId::new("ns", "k3")).unwrap();
    assert_eq!(store.list("ns").unwrap().len(), 0);

    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn delete_nonexistent_returns_false() {
    let dir = temp_dir_path();
    let store = make_store(&dir);
    let id = SecretId::new("test", "never-stored");
    assert!(!store.delete(&id).unwrap());
    let _ = fs::remove_dir_all(&dir);
}
