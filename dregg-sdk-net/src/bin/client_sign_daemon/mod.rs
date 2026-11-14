//! One warm profile, bounded newline-delimited JSON requests, durable retry IDs.
//! A persisted undecided request blocks subsequent nonce allocation after a crash.
use super::*;
use dregg_sdk_net::merkle_anchor::{Leaf, proofs};
use serde::{Deserialize, Serialize};
use std::os::unix::fs::{DirBuilderExt, FileTypeExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::{collections::BTreeMap, path::Path};
use tokio::io::{AsyncBufReadExt, AsyncWriteExt};

#[derive(Clone, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Request {
    id: String,
    topic: String,
    digest: String,
}
#[derive(Clone, Deserialize, Serialize)]
struct Entry {
    request: Request,
    response: serde_json::Value,
}
type Journal = BTreeMap<String, Entry>;

fn pin_configuration(directory: &Path, node_url: &str, topic: &str) -> Result<()> {
    use std::io::Write;
    let path = directory.join("config.json");
    let expected = serde_json::json!({"node_url":node_url,"anchor_topic":topic});
    if path.exists() {
        let stored: serde_json::Value = serde_json::from_slice(&std::fs::read(path)?)?;
        if stored != expected {
            return Err(err("profile-daemon-config-mismatch".into()));
        }
    } else {
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(path)?;
        file.write_all(&serde_json::to_vec(&expected)?)?;
        file.sync_all()?;
        std::fs::File::open(directory)?.sync_all()?;
    }
    Ok(())
}

fn persist(path: &Path, journal: &Journal) -> Result<()> {
    use std::io::Write;
    let temp = path.with_extension("tmp");
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .mode(0o600)
        .open(&temp)?;
    file.write_all(&serde_json::to_vec(journal)?)?;
    file.sync_all()?;
    std::fs::rename(temp, path)?;
    std::fs::File::open(path.parent().unwrap())?.sync_all()?;
    Ok(())
}
fn checked_receipt(hash: &str, row: serde_json::Value) -> Result<serde_json::Value> {
    // A matching turn_hash alone is not a receipt. Reuse the strict existing
    // shape checker; tentative is reported explicitly, never called final.
    match classify_commitment(hash, &serde_json::json!([row.clone()]), true) {
        Commitment::Committed { .. } => Ok(row),
        other => Err(err(format!("undecided: invalid receipt: {other:?}"))),
    }
}

fn undecided() -> serde_json::Value {
    serde_json::json!({"outcome":"undecided"})
}
fn retry(journal: &Journal, request: &Request) -> Option<serde_json::Value> {
    journal.get(&request.id).map(|entry| {
        if entry.request.topic == request.topic && entry.request.digest == request.digest {
            entry.response.clone()
        } else {
            serde_json::json!({"outcome":"refused", "error":"request-id-conflict"})
        }
    })
}
fn admission(journal: &Journal, request: &Request) -> Option<serde_json::Value> {
    retry(journal, request).or_else(|| {
        journal
            .values()
            .any(|e| e.response["outcome"] == "undecided")
            .then(
                || serde_json::json!({"outcome":"undecided","error":"profile-has-undecided-batch"}),
            )
    })
}

async fn reply(stream: &mut tokio::net::UnixStream, value: &serde_json::Value) {
    let mut bytes = serde_json::to_vec(value).unwrap();
    bytes.push(b'\n');
    let _ = tokio::time::timeout(std::time::Duration::from_secs(2), stream.write_all(&bytes)).await;
}
async fn read(stream: &mut tokio::net::UnixStream) -> Result<Request> {
    use tokio::io::AsyncReadExt;
    let mut bytes = Vec::new();
    let n = tokio::time::timeout(
        std::time::Duration::from_secs(2),
        tokio::io::BufReader::new(stream.take(4097)).read_until(b'\n', &mut bytes),
    )
    .await??;
    if n > 4096 || bytes.last() != Some(&b'\n') {
        return Err(err("request-size".into()));
    }
    let mut request: Request = serde_json::from_slice(&bytes)?;
    if request.id.is_empty() || request.id.len() > 128 || request.topic.len() > 256 {
        return Err(err("request-size".into()));
    }
    request.digest = hex::encode(parse_hash_hex("digest", &request.digest)?);
    Ok(request)
}

fn publish_socket(directory: &Path, socket: &str) -> Result<tokio::net::UnixListener> {
    // Remove only the socket inode this profile previously published. A second
    // daemon cannot get here while the identity lock is held.
    let socket_record = directory.join("socket.json");
    if let Ok(meta) = std::fs::symlink_metadata(socket) {
        let recorded: serde_json::Value = serde_json::from_slice(&std::fs::read(&socket_record)?)?;
        if !meta.file_type().is_socket()
            || recorded["path"] != socket
            || recorded["device"] != meta.dev()
            || recorded["inode"] != meta.ino()
        {
            return Err(err("socket-path-owned-by-another-endpoint".into()));
        }
        std::fs::remove_file(socket)?;
    }
    // Publish a socket already mode 0600. The private staging directory is on
    // the destination filesystem, so rename never depends on /tmp mount layout.
    let socket_path = Path::new(socket);
    let staging = socket_path.with_extension(format!("private-{}", std::process::id()));
    std::fs::DirBuilder::new().mode(0o700).create(&staging)?;
    let private_socket = staging.join("socket");
    let listener = tokio::net::UnixListener::bind(&private_socket)?;
    std::fs::set_permissions(&private_socket, std::fs::Permissions::from_mode(0o600))?;
    let meta = std::fs::symlink_metadata(&private_socket)?;
    let record = serde_json::to_vec(
        &serde_json::json!({"path":socket,"device":meta.dev(),"inode":meta.ino()}),
    )?;
    use std::io::Write;
    let mut record_file = std::fs::OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .mode(0o600)
        .open(&socket_record)?;
    record_file.write_all(&record)?;
    record_file.sync_all()?;
    std::fs::File::open(directory)?.sync_all()?;
    // hard_link is no-clobber, unlike rename; both names denote the same socket.
    std::fs::hard_link(&private_socket, socket)?;
    std::fs::remove_file(&private_socket)?;
    std::fs::remove_dir(&staging)?;
    std::fs::File::open(&directory)?.sync_all()?;
    Ok(listener)
}

async fn collect_batch(
    first: Request,
    stream: tokio::net::UnixStream,
    listener: &tokio::net::UnixListener,
    max_batch: usize,
    batch_window_ms: u64,
    journal: &mut Journal,
    journal_path: &Path,
) -> Result<Vec<(Request, tokio::net::UnixStream)>> {
    journal.insert(
        first.id.clone(),
        Entry {
            request: first.clone(),
            response: undecided(),
        },
    );
    persist(journal_path, journal)?;
    let mut batch = vec![(first, stream)];
    let deadline = tokio::time::Instant::now() + std::time::Duration::from_millis(batch_window_ms);
    while batch.len() < max_batch {
        let Ok(accepted) = tokio::time::timeout_at(deadline, listener.accept()).await else {
            break;
        };
        let (mut stream, _) = accepted?;
        match tokio::time::timeout_at(deadline, read(&mut stream)).await {
            Ok(Ok(r)) => {
                if let Some(response) = retry(journal, &r) {
                    reply(&mut stream, &response).await;
                    continue;
                }
                journal.insert(
                    r.id.clone(),
                    Entry {
                        request: r.clone(),
                        response: undecided(),
                    },
                );
                persist(journal_path, journal)?;
                batch.push((r, stream));
            }
            _ => {
                reply(
                    &mut stream,
                    &serde_json::json!({"outcome":"refused","error":"request-or-topic"}),
                )
                .await
            }
        }
    }
    Ok(batch)
}

pub(super) async fn run(f: Flags) -> Result<()> {
    no_positionals(&f, "daemon")?;
    if !(1..=4096).contains(&f.max_batch) || !(1..=60_000).contains(&f.batch_window_ms) {
        return Err(err(
            "daemon batch bounds: max-batch 1..4096, window 1..60000 ms".into(),
        ));
    }
    let socket = f
        .socket
        .as_deref()
        .ok_or_else(|| err("daemon requires --socket PATH".into()))?;
    let (name, clerk) = resolve_clerk(f.profile.as_deref(), false)?;
    // Use identity, not socket name: two socket paths must not yield two nonce streams.
    let directory =
        profiles::profiles_dir().join(format!("daemon-{}", hex::encode(clerk.public_key().0)));
    std::fs::create_dir_all(&directory)?;
    std::fs::set_permissions(&directory, std::fs::Permissions::from_mode(0o700))?;
    let lock = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .mode(0o600)
        .open(directory.join("lock"))?;
    lock.try_lock()
        .map_err(|_| err("profile-daemon-already-running".into()))?;
    pin_configuration(&directory, &f.node_url, &f.topic)?;
    let journal_path = directory.join("journal.json");
    let mut journal: Journal = if journal_path.exists() {
        serde_json::from_slice(&std::fs::read(&journal_path)?)?
    } else {
        BTreeMap::new()
    };
    let listener = publish_socket(&directory, socket)?;
    let http = reqwest::Client::new();
    let bearer = ensure_token(&http, &f.node_url, f.bearer_flags()).await?;
    eprintln!("[client-sign] daemon ready profile={name}");
    loop {
        let (mut stream, _) = listener.accept().await?;
        let first = match read(&mut stream).await {
            Ok(r) => r,
            Err(e) => {
                reply(
                    &mut stream,
                    &serde_json::json!({"outcome":"refused","error":e.to_string()}),
                )
                .await;
                continue;
            }
        };
        if let Some(response) = admission(&journal, &first) {
            reply(&mut stream, &response).await;
            continue;
        }
        let batch = collect_batch(
            first,
            stream,
            &listener,
            f.max_batch,
            f.batch_window_ms,
            &mut journal,
            &journal_path,
        )
        .await?;
        let leaves: Vec<_> = batch
            .iter()
            .map(|(r, _)| Leaf {
                topic: r.topic.clone(),
                digest: parse_hash_hex("digest", &r.digest).unwrap(),
            })
            .collect();
        let ps = proofs(&leaves).map_err(|e| err(e.into()))?;
        let result: Result<serde_json::Value> = async {
            let head = Head::fetch(&NodeHttpClient::new(&f.node_url), &clerk.cell_id("default"))
                .await
                .map_err(err)?;
            let prepared =
                prepare_send(&clerk, &head, &f.topic, &hex::encode(ps[0].root)).map_err(err)?;
            let hash = hex::encode(prepared.turn_hash);
            let witness = directory.join(format!("{hash}.turn"));
            write_new_file(
                witness.to_str().ok_or_else(|| err("witness-path".into()))?,
                &prepared.bytes,
            )?;
            for (i, (r, _)) in batch.iter().enumerate() {
                journal.get_mut(&r.id).unwrap().response = serde_json::json!({
                    "outcome":"undecided","turn_hash":hash,"witness":witness,
                    "node":f.node_url,"anchor_topic":f.topic,
                    "merkle_proof":ps[i], "leaf_index":i,"sibling_path":ps[i].sibling_path,
                });
            }
            persist(&journal_path, &journal)?;
            let url = format!(
                "{}/api/starbridge/receipts?limit=2&turn_hash={hash}",
                f.node_url
            );
            match post_signed(
                &http,
                &f.node_url,
                &bearer,
                prepared.bytes,
                &hash,
                Submitted::Prepared,
                &url,
            )
            .await?
            {
                Posted::Took => checked_receipt(
                    &hash,
                    await_receipt(&http, &url, &hash, Submitted::Prepared).await?,
                ),
                Posted::Refused(why) => Err(err(format!("batch-refused:{why}"))),
            }
        }
        .await;
        for (r, _) in &batch {
            let response = &mut journal.get_mut(&r.id).unwrap().response;
            match &result {
                Ok(row) => {
                    response["outcome"] = "receipted".into();
                    response["receipt_hash"] = row["receipt_hash"].clone();
                    response["finality"] = row["finality"].clone();
                }
                Err(e) => {
                    response["error"] = e.to_string().into();
                }
            }
        }
        persist(&journal_path, &journal)?;
        for (r, mut stream) in batch {
            reply(&mut stream, &journal[&r.id].response).await;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn daemon_journal_cannot_replay_receipts_from_a_different_node_or_anchor_topic() {
        let temp = tempfile::tempdir().unwrap();
        pin_configuration(temp.path(), "http://localhost:8899", "anchors").unwrap();
        pin_configuration(temp.path(), "http://localhost:8899", "anchors").unwrap();
        assert!(pin_configuration(temp.path(), "http://localhost:9999", "anchors").is_err());
        assert!(pin_configuration(temp.path(), "http://localhost:8899", "other").is_err());
    }

    #[test]
    fn daemon_never_promotes_an_incomplete_receipt_to_success() {
        let hash = "ab".repeat(32);
        let row = serde_json::json!({"turn_hash":hash,"receipt_hash":"cd".repeat(32),"chain_index":0,"finality":"tentative"});
        checked_receipt(&hash, row.clone()).unwrap();
        for field in ["receipt_hash", "chain_index", "finality", "turn_hash"] {
            let mut bad = row.clone();
            bad.as_object_mut().unwrap().remove(field);
            assert!(checked_receipt(&hash, bad).is_err());
        }
        assert!(checked_receipt(&"ef".repeat(32), row).is_err());
    }

    #[test]
    fn daemon_restart_keeps_undecided_and_retry_identity() {
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("journal.json");
        let request = Request {
            id: "retry-1".into(),
            topic: "audit".into(),
            digest: "00".repeat(32),
        };
        let mut journal = Journal::new();
        journal.insert(
            request.id.clone(),
            Entry {
                request: request.clone(),
                response: undecided(),
            },
        );
        persist(&path, &journal).unwrap();
        let recovered: Journal = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
        assert_eq!(retry(&recovered, &request).unwrap()["outcome"], "undecided");
        let mut next = request.clone();
        next.id = "new-batch".into();
        assert_eq!(
            admission(&recovered, &next).unwrap()["error"],
            "profile-has-undecided-batch"
        );
        let mut altered = request.clone();
        altered.digest = "11".repeat(32);
        assert_eq!(
            retry(&recovered, &altered).unwrap()["error"],
            "request-id-conflict"
        );
        journal.get_mut(&request.id).unwrap().response =
            serde_json::json!({"outcome":"receipted","turn_hash":"fixed"});
        assert_eq!(admission(&journal, &request).unwrap()["turn_hash"], "fixed");
        assert!(admission(&journal, &next).is_none());
    }
    #[tokio::test]
    async fn daemon_one_item_window_closes_without_a_second_caller() {
        let temp = tempfile::tempdir().unwrap();
        let listener = tokio::net::UnixListener::bind(temp.path().join("socket")).unwrap();
        let (stream, _peer) = tokio::net::UnixStream::pair().unwrap();
        let request = Request {
            id: "one".into(),
            topic: "a".into(),
            digest: "11".repeat(32),
        };
        let mut journal = Journal::new();
        let batch = tokio::time::timeout(
            std::time::Duration::from_secs(1),
            collect_batch(
                request,
                stream,
                &listener,
                8,
                10,
                &mut journal,
                &temp.path().join("journal"),
            ),
        )
        .await
        .unwrap()
        .unwrap();
        assert_eq!(batch.len(), 1);
        assert_eq!(journal["one"].response["outcome"], "undecided");
    }

    #[tokio::test]
    async fn daemon_duplicate_digests_with_distinct_ids_are_distinct_batch_members() {
        let temp = tempfile::tempdir().unwrap();
        let socket = temp.path().join("socket");
        let listener = tokio::net::UnixListener::bind(&socket).unwrap();
        let (stream, _peer) = tokio::net::UnixStream::pair().unwrap();
        let request = Request {
            id: "first".into(),
            topic: "a".into(),
            digest: "11".repeat(32),
        };
        let mut second = request.clone();
        second.id = "second".into();
        second.topic = "b".into();
        let mut client = tokio::net::UnixStream::connect(&socket).await.unwrap();
        let mut bytes = serde_json::to_vec(&second).unwrap();
        bytes.push(b'\n');
        client.write_all(&bytes).await.unwrap();
        let mut journal = Journal::new();
        let batch = collect_batch(
            request,
            stream,
            &listener,
            2,
            1000,
            &mut journal,
            &temp.path().join("journal"),
        )
        .await
        .unwrap();
        assert_eq!(batch.len(), 2);
        assert_eq!(journal.len(), 2);
        assert_eq!(batch[0].0.digest, batch[1].0.digest);
        assert_ne!(batch[0].0.id, batch[1].0.id);
    }

    #[tokio::test]
    async fn daemon_socket_is_private_and_restart_only_unlinks_its_own_inode() {
        let temp = tempfile::tempdir().unwrap();
        let socket = temp.path().join("endpoint");
        let socket = socket.to_str().unwrap();
        let listener = publish_socket(temp.path(), socket).unwrap();
        assert_eq!(
            std::fs::metadata(socket).unwrap().permissions().mode() & 0o777,
            0o600
        );
        let client = tokio::net::UnixStream::connect(socket).await.unwrap();
        let _accepted = listener.accept().await.unwrap();
        drop(client);
        drop(listener);
        let listener = publish_socket(temp.path(), socket).unwrap();
        drop(listener);
        std::fs::remove_file(socket).unwrap();
        std::fs::write(socket, b"unrelated file").unwrap();
        assert!(publish_socket(temp.path(), socket).is_err());
        assert_eq!(std::fs::read(socket).unwrap(), b"unrelated file");
    }

    #[test]
    fn daemon_profile_lock_excludes_second_owner() {
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("lock");
        let a = std::fs::File::create(&path).unwrap();
        a.try_lock().unwrap();
        let b = std::fs::File::open(&path).unwrap();
        assert!(b.try_lock().is_err());
        drop(a);
        b.try_lock().unwrap();
    }
}
