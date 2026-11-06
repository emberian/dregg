//! One `cp_verify` call under the auditor's own limits, on files the auditor staged itself.
//!
//! FlashProve's `cp_verify` bounds neither its time nor its memory and follows symlinks
//! (`docs/limits.md`, "A hostile file can exhaust memory or time"), so the auditor (a) stages the
//! provider's files into a fresh private directory, reading only regular files and at most
//! [`STAGE_CAP`] bytes of each, and (b) runs `cp_verify` in its own process group under a wall
//! clock, an address-space limit and an output cap. Every incomplete outcome (a staging failure,
//! a kill, a read error, an output over the cap, a spawn failure) comes back as `exit: None` or a
//! failed stage; the Lean decision reads it, never this module.

use std::io::Read;
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt};
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

/// The files of one call.
#[derive(Clone, Debug)]
pub struct CallFiles {
    pub config: PathBuf,
    pub ivk: PathBuf,
    pub req: PathBuf,
    pub y: PathBuf,
    /// The proof file; a path that does not exist means no proof was handed over.
    pub proof: PathBuf,
}

/// What the call produced.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct CallOutcome {
    pub stdout: String,
    /// `None`: the call did not end with an exit status of its own, or its output was not read
    /// whole (killed at the time or memory limit, killed by a signal, never started, a read
    /// error, output over the cap).
    pub exit: Option<u32>,
    pub millis: u64,
    pub killed_for_time: bool,
    /// Why the call was not made or not read whole, if so.
    pub fault: Option<String>,
}

impl CallOutcome {
    pub fn not_made(why: String) -> CallOutcome {
        CallOutcome {
            stdout: String::new(),
            exit: None,
            millis: 0,
            killed_for_time: false,
            fault: Some(why),
        }
    }
}

/// The largest standard output the auditor reads. `cp_verify` prints about 140 lines.
pub const OUTPUT_CAP: usize = 4 << 20;

/// Run `cp_verify CONFIG IVK REQ Y PROOF -id ID` in its own process group with a wall-clock limit,
/// an address-space limit and an output cap.
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
    // SAFETY: setpgid and setrlimit are async-signal-safe; nothing else runs between fork and exec.
    unsafe {
        cmd.pre_exec(move || {
            if libc::setpgid(0, 0) != 0 {
                return Err(std::io::Error::last_os_error());
            }
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
        Err(e) => return CallOutcome::not_made(format!("spawn: {e}")),
    };
    let pgid = child.id() as libc::pid_t;
    let mut out = child.stdout.take().expect("piped stdout");
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let mut buf = Vec::new();
        let r = (&mut out).take(OUTPUT_CAP as u64 + 1).read_to_end(&mut buf);
        let _ = tx.send((buf, r.is_ok()));
    });
    let mut killed = false;
    let mut fault = None;
    let status = loop {
        match child.try_wait() {
            Ok(Some(st)) => break Some(st),
            Ok(None) if start.elapsed() >= limit => {
                // The group is the one this call created for its own child: kill exactly it.
                unsafe { libc::kill(-pgid, libc::SIGKILL) };
                killed = true;
                break child.wait().ok();
            }
            Ok(None) => std::thread::sleep(Duration::from_millis(20)),
            Err(e) => {
                unsafe { libc::kill(-pgid, libc::SIGKILL) };
                fault = Some(format!("wait: {e}"));
                let _ = child.wait();
                break None;
            }
        }
    };
    // The reader ends when every holder of the pipe is gone; give it a bounded grace period.
    let grace = Duration::from_secs(5);
    let (buf, read_ok) = match rx.recv_timeout(grace) {
        Ok(v) => v,
        Err(_) => {
            unsafe { libc::kill(-pgid, libc::SIGKILL) };
            fault = Some("standard output did not close".into());
            (Vec::new(), false)
        }
    };
    if buf.len() > OUTPUT_CAP {
        fault = Some("standard output over the cap".into());
    } else if !read_ok && fault.is_none() {
        fault = Some("standard output read error".into());
    }
    let whole = fault.is_none() && !killed;
    let exit = if whole {
        status.and_then(|s| s.code()).map(|c| c as u32)
    } else {
        None
    };
    CallOutcome {
        stdout: String::from_utf8_lossy(&buf[..buf.len().min(OUTPUT_CAP)]).into_owned(),
        exit,
        millis: start.elapsed().as_millis() as u64,
        killed_for_time: killed,
        fault,
    }
}

/// The SHA-256 digests of the files the auditor staged (`proof: None`: there was no proof file).
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Staged {
    pub req_sha256: Option<String>,
    pub y_sha256: Option<String>,
    pub proof_sha256: Option<String>,
    /// Why staging failed, if it did. A failed stage is a failed opening in the Lean decision.
    pub fault: Option<String>,
}

/// The largest file the auditor will stage; a file over it is refused.
pub const STAGE_CAP: u64 = 256 << 20;

/// Read one provider file: it must be a regular file (opened without blocking, checked on the
/// descriptor), at most `STAGE_CAP` bytes. `Ok(None)`: it does not exist.
fn read_regular(from: &Path) -> Result<Option<Vec<u8>>, String> {
    let f = match std::fs::OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NONBLOCK)
        .open(from)
    {
        Ok(f) => f,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(format!("{}: {e}", from.display())),
    };
    let md = f
        .metadata()
        .map_err(|e| format!("{}: {e}", from.display()))?;
    if !md.file_type().is_file() {
        return Err(format!("{}: not a regular file", from.display()));
    }
    if md.len() > STAGE_CAP {
        return Err(format!("{}: over the size cap", from.display()));
    }
    let mut buf = Vec::new();
    f.take(STAGE_CAP + 1)
        .read_to_end(&mut buf)
        .map_err(|e| format!("{}: {e}", from.display()))?;
    if buf.len() as u64 > STAGE_CAP {
        return Err(format!("{}: grew past the size cap", from.display()));
    }
    Ok(Some(buf))
}

static STAGE_SEQ: AtomicU64 = AtomicU64::new(0);

/// A fresh private directory (mode 0700, refused if it exists) under `parent`.
pub fn private_dir(parent: &Path) -> std::io::Result<PathBuf> {
    std::fs::create_dir_all(parent)?;
    let n = STAGE_SEQ.fetch_add(1, Ordering::Relaxed);
    let tag = hex::encode(crate::record::os_random32()?);
    let d = parent.join(format!("stage-{}-{n}-{}", std::process::id(), &tag[..16]));
    std::fs::DirBuilder::new().mode(0o700).create(&d)?;
    Ok(d)
}

/// Stage the provider's files into a fresh private directory under `parent` and return the call
/// files with their digests. The request and token files are mandatory; a missing proof is
/// recorded as `None`. Any failure is returned in `Staged::fault` with no call files: the caller
/// hands that to the Lean decision as a failed opening, and no `cp_verify` call is made. The
/// public files (`config`, `ivk`) stay at the auditor's own pinned copies.
pub fn stage(src: &CallFiles, parent: &Path) -> (Option<CallFiles>, Staged) {
    use sha2::{Digest, Sha256};
    let fail = |why: String| {
        (
            None,
            Staged {
                req_sha256: None,
                y_sha256: None,
                proof_sha256: None,
                fault: Some(why),
            },
        )
    };
    let dir = match private_dir(parent) {
        Ok(d) => d,
        Err(e) => return fail(format!("staging directory: {e}")),
    };
    let mut digests = Vec::new();
    let mut paths = Vec::new();
    for (from, name, required) in [
        (&src.req, "staged.req", true),
        (&src.y, "staged.y", true),
        (&src.proof, "staged.proof", false),
    ] {
        let to = dir.join(name);
        match read_regular(from) {
            Ok(Some(buf)) => {
                let w = std::fs::OpenOptions::new()
                    .write(true)
                    .create_new(true)
                    .mode(0o600)
                    .open(&to)
                    .and_then(|mut f| std::io::Write::write_all(&mut f, &buf));
                if let Err(e) = w {
                    return fail(format!("{}: {e}", to.display()));
                }
                digests.push(Some(hex::encode(Sha256::digest(&buf))));
            }
            Ok(None) if !required => digests.push(None),
            Ok(None) => return fail(format!("{}: missing", from.display())),
            Err(e) => return fail(e),
        }
        paths.push(to);
    }
    (
        Some(CallFiles {
            config: src.config.clone(),
            ivk: src.ivk.clone(),
            req: paths[0].clone(),
            y: paths[1].clone(),
            proof: paths[2].clone(),
        }),
        Staged {
            req_sha256: digests[0].clone(),
            y_sha256: digests[1].clone(),
            proof_sha256: digests[2].clone(),
            fault: None,
        },
    )
}
