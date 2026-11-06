//! One `cp_verify` call under the auditor's own limits.
//!
//! FlashProve's `cp_verify` bounds neither its time nor its memory and follows symlinks
//! (`docs/limits.md`, "A hostile file can exhaust memory or time"), so the auditor sets both. A
//! call that is killed for either, that cannot be started, or whose proof is absent, comes back
//! with `exit: None` or a nonzero code; the Lean `verdictOf` reads it, never this module.

use std::io::Read;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

/// The files of one call.
#[derive(Clone, Debug)]
pub struct CallFiles {
    pub config: PathBuf,
    pub ivk: PathBuf,
    pub req: PathBuf,
    pub y: PathBuf,
    /// The proof file; a path that does not exist is a withheld proof (a real call, exit 2).
    pub proof: PathBuf,
}

/// What the call produced.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct CallOutcome {
    pub stdout: String,
    /// `None`: the process did not end with an exit status of its own (killed at the time or
    /// memory limit, killed by a signal, or never started).
    pub exit: Option<u32>,
    pub millis: u64,
    pub killed_for_time: bool,
}

/// Run `cp_verify CONFIG IVK REQ Y PROOF -id ID` with a wall-clock limit and an address-space
/// limit.
pub fn run_cp_verify(
    bin: &Path,
    f: &CallFiles,
    id: &str,
    limit: Duration,
    mem_bytes: u64,
) -> CallOutcome {
    let start = Instant::now();
    let mut cmd = Command::new(bin);
    cmd.arg(&f.config)
        .arg(&f.ivk)
        .arg(&f.req)
        .arg(&f.y)
        .arg(&f.proof)
        .arg("-id")
        .arg(id)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::null());
    // SAFETY: setrlimit is async-signal-safe; nothing else runs between fork and exec.
    unsafe {
        cmd.pre_exec(move || {
            let lim = libc::rlimit {
                rlim_cur: mem_bytes as libc::rlim_t,
                rlim_max: mem_bytes as libc::rlim_t,
            };
            if libc::setrlimit(libc::RLIMIT_AS, &lim) != 0 {
                return Err(std::io::Error::last_os_error());
            }
            Ok(())
        });
    }
    let mut child = match cmd.spawn() {
        Ok(c) => c,
        Err(_) => {
            return CallOutcome {
                stdout: String::new(),
                exit: None,
                millis: 0,
                killed_for_time: false,
            };
        }
    };
    let mut out = child.stdout.take().expect("piped stdout");
    let reader = std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = out.read_to_end(&mut buf);
        buf
    });
    let mut killed = false;
    let status = loop {
        match child.try_wait() {
            Ok(Some(st)) => break Some(st),
            Ok(None) if start.elapsed() >= limit => {
                // The child is ours, by handle: kill exactly it.
                let _ = child.kill();
                killed = true;
                break child.wait().ok();
            }
            Ok(None) => std::thread::sleep(Duration::from_millis(20)),
            Err(_) => break None,
        }
    };
    let buf = reader.join().unwrap_or_default();
    let exit = if killed {
        None
    } else {
        status.and_then(|s| s.code()).map(|c| c as u32)
    };
    CallOutcome {
        stdout: String::from_utf8_lossy(&buf).into_owned(),
        exit,
        millis: start.elapsed().as_millis() as u64,
        killed_for_time: killed,
    }
}

/// The SHA-256 digests of the files the auditor staged (`proof: None`: there was no proof file).
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Staged {
    pub req_sha256: String,
    pub y_sha256: String,
    pub proof_sha256: Option<String>,
}

/// The largest file the auditor will stage. A file that reaches it is not the committed one (no
/// committed proof is that large), so its digest is the digest of the first `cap + 1` bytes, which
/// cannot match: a symlink to `/dev/zero` costs one bounded read, not a hang.
pub const STAGE_CAP: u64 = 256 << 20;

fn copy_capped(from: &Path, to: &Path) -> std::io::Result<Option<String>> {
    use sha2::{Digest, Sha256};
    let f = match std::fs::File::open(from) {
        Ok(f) => f,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(e),
    };
    let mut buf = Vec::new();
    f.take(STAGE_CAP + 1).read_to_end(&mut buf)?;
    std::fs::write(to, &buf)?;
    Ok(Some(hex::encode(Sha256::digest(&buf))))
}

/// Copy the provider's files into `dir` (which only the auditor writes), reading each with the
/// size cap, and return the staged call files with their digests. The public files (`config`,
/// `ivk`) stay at the auditor's own pinned copies.
pub fn stage(src: &CallFiles, dir: &Path) -> std::io::Result<(CallFiles, Staged)> {
    std::fs::create_dir_all(dir)?;
    let req = dir.join("staged.req");
    let y = dir.join("staged.y");
    let proof = dir.join("staged.proof");
    let _ = std::fs::remove_file(&proof);
    let rs = copy_capped(&src.req, &req)?.unwrap_or_default();
    let ys = copy_capped(&src.y, &y)?.unwrap_or_default();
    let ps = copy_capped(&src.proof, &proof)?;
    Ok((
        CallFiles {
            config: src.config.clone(),
            ivk: src.ivk.clone(),
            req,
            y,
            proof,
        },
        Staged {
            req_sha256: rs,
            y_sha256: ys,
            proof_sha256: ps,
        },
    ))
}
