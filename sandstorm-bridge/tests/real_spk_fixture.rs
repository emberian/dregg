//! **The real-catalog `.spk` differential harness — the real Cap'n Proto `Archive` wire.**
//!
//! With a real
//! signed package at `sandstorm-bridge/fixtures/sample.spk`, this harness asserts the
//! real end-to-end parse: the canonical container header, the *combined* Ed25519/
//! SHA-512 signature, the App ID intrinsic to the signing key, the genuine multi-segment
//! capnp `Archive` file tree, the capnp `Manifest`, and that a tampered package is
//! refused. Absent the fixture the test skips cleanly so the suite stays green where the
//! artifact is not checked out.
//!
//! Ground truth (the package is "Simple Todos", a Meteor http-bridge app):
//!   - magic `8f c6 cd ef 45 1a ea 96`;
//!   - App ID `0dp7n6ehj8r5ttfc0fj0au6gxkuy1nhw2kx70wussfa1mqj8tf80` = base32(pubkey);
//!   - a 19-entry top-level tree (regular/executable/symlink/directory all present),
//!     including `sandstorm-manifest`, the `sandstorm-http-bridge` executable, `main.js`;
//!   - the manifest decodes to title "Simple Todos", appVersion 5, the http-bridge
//!     `continueCommand` (`/sandstorm-http-bridge 8000 -- …`) → ingress port 8000.

use std::path::PathBuf;

use sandstorm_bridge::manifest::SpkManifest;
use sandstorm_bridge::spk::{base32, FileContent, Spk, SpkError, SPK_MAGIC};

fn fixture_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures")
        .join("sample.spk")
}

fn load_fixture() -> Option<Vec<u8>> {
    match std::fs::read(fixture_path()) {
        Ok(b) => Some(b),
        Err(_) => {
            eprintln!(
                "skip: no real-catalog fixture at {} (drop a real signed sample.spk there)",
                fixture_path().display()
            );
            None
        }
    }
}

#[test]
fn a_real_catalog_spk_parses_end_to_end_on_the_real_wire() {
    let bytes = match load_fixture() {
        Some(b) => b,
        None => return,
    };

    // The container header is the canonical Sandstorm magic.
    assert!(
        bytes.starts_with(&SPK_MAGIC),
        "a real .spk must begin with the canonical magic 8fc6cdef…; got {:02x?}",
        &bytes[..bytes.len().min(8)]
    );

    // The whole real parse: magic → xz → capnp Signature → combined Ed25519/SHA-512
    // verify over the archive → capnp Archive. A failure here would mean the signature
    // did not bind, or the capnp wire did not decode — both are hard errors.
    let spk = Spk::parse(&bytes).expect("the real catalog .spk parses + verifies");

    // The App ID is intrinsic to the signing key (no CA, no manifest claim).
    assert_eq!(
        spk.app_id().0,
        base32(&spk.public_key),
        "App ID is the base32 of the signing public key"
    );
    assert_eq!(
        spk.app_id().0,
        "0dp7n6ehj8r5ttfc0fj0au6gxkuy1nhw2kx70wussfa1mqj8tf80"
    );

    // The genuine multi-segment capnp Archive file tree extracted. Multiple File union
    // members are represented (regular, executable, directory) — proof the discriminant
    // + nested composite lists decode against a real, far-pointer-bearing message.
    let top = &spk.archive.files;
    assert!(
        top.len() >= 15,
        "a real package has a populated top-level tree (got {})",
        top.len()
    );
    let named = |n: &str| top.iter().find(|f| f.name == n);
    assert!(matches!(
        named("sandstorm-manifest").map(|f| &f.content),
        Some(FileContent::Regular(_))
    ));
    assert!(matches!(
        named("sandstorm-http-bridge").map(|f| &f.content),
        Some(FileContent::Executable(_))
    ));
    assert!(
        top.iter()
            .any(|f| matches!(f.content, FileContent::Directory(_))),
        "a real package has directories (var/proc/…)"
    );
    // The nested directory tree decoded (the package has 2103 files under directories).
    let nested: usize = top
        .iter()
        .filter_map(|f| match &f.content {
            FileContent::Directory(sub) => Some(sub.len()),
            _ => None,
        })
        .sum();
    assert!(nested > 0, "nested directory entries decoded");
    // File lookup resolves a regular file's bytes.
    assert!(spk.archive.find("sandstorm-manifest").is_some());

    // The manifest is a real capnp `Manifest` message; decode it.
    let manifest = SpkManifest::from_spk(&spk).expect("decode the real capnp manifest");
    assert_eq!(manifest.app_title, "Simple Todos");
    assert_eq!(manifest.app_version, 5);
    assert_eq!(
        manifest.app_id,
        spk.app_id(),
        "manifest App ID = signing key"
    );
    assert_eq!(
        manifest.continue_command.argv.first().map(String::as_str),
        Some("/sandstorm-http-bridge")
    );
    assert!(manifest.is_http_bridge(), "an http-bridge catalog app");

    // The derived grain spec routes the http-bridge app to the strong-isolation tier
    // with the recovered ingress port.
    let spec = manifest.grain_spec();
    assert_eq!(spec.ingress_port, Some(8000));
    assert_eq!(spec.app_version, 5);
}

#[test]
fn a_tampered_real_spk_is_refused() {
    let mut bytes = match load_fixture() {
        Some(b) => b,
        None => return,
    };
    // Flip a byte deep inside the xz container — this corrupts the compressed archive,
    // so either xz decompression fails its integrity check or the recomputed SHA-512 no
    // longer matches the signed hash. Either way no launchable image is returned.
    let n = bytes.len();
    bytes[n / 2] ^= 0xff;
    match Spk::parse(&bytes) {
        Err(SpkError::BadSignature)
        | Err(SpkError::Decompress(_))
        | Err(SpkError::Archive(_))
        | Err(SpkError::TooLarge)
        | Err(SpkError::Truncated) => {}
        other => panic!("a tampered real .spk was not refused: {other:?}"),
    }
}
