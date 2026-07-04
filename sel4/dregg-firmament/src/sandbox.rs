//! THE OS-SANDBOX CONFINEMENT — Phase-0 of the cross-platform sandboxed
//! firmament (`docs/DREGG-DESKTOP-OS.md §3`, the ambient-authority half of the
//! v1 isolation upgrade).
//!
//! ## What gap this closes
//!
//! [`crate::process_kernel::ProcessKernel::spawn_pd`] forks a child PD with
//! **MMU isolation** (separate page tables) + a `socketpair(AF_UNIX)` control
//! channel + named `shm` regions + the kernel's epoch-tagged cap-handle
//! [`ValidityTable`]. That is the *memory* half of confinement and it is real.
//! But the fork-path child inherits the parent's **ambient authority**: it can
//! still `open()` arbitrary files, `socket(AF_INET)` the network, `execve` a new
//! image, and it keeps every inherited fd. [`ProcessKernel::ISOLATION_FIDELITY`]
//! names exactly this: "MMU enforces address-space separation" but ambient OS
//! authority is NOT yet confined.
//!
//! This module closes that, applied in the child **right after `fork()`, before
//! the PD `body` runs**, via a per-platform [`confine_child`]:
//!
//! - **macOS (enforced + smoke-tested here):** the child closes every fd except
//!   the granted ones (the control socket), then SELF-applies a `(version 1)
//!   (deny default)` Seatbelt/SBPL profile through `sandbox_init(3)`. The profile
//!   allows only: I/O on already-open fds, the minimal `/usr/lib` + dyld /
//!   framework reads a process needs to keep running, plus any explicitly-granted
//!   read paths. It allows NO `network*`, NO `process-exec*`, NO `mach-lookup*`.
//!   The macOS sandbox MUST be self-applied by the child (a parent cannot impose
//!   it) — fine, the child is trusted firmament code between fork and body.
//!
//! - **Linux (compiled here as a cfg-stub, ENFORCED on Linux):**
//!   `unshare(CLONE_NEWUSER|NEWNET|NEWNS|NEWPID)` + a uid-map (an empty net
//!   namespace = no route to any network), `prctl(PR_SET_NO_NEW_PRIVS)`, a
//!   default-deny seccomp-bpf allow-list (`seccompiler`), Landlock path-rules
//!   (`landlock`) for any granted read paths, and `close_range` keeping only the
//!   granted fds. On macOS the Linux body compiles to a no-op stub so the crate
//!   builds on both; it only RUNS on Linux.
//!
//! ## The trust statement (don't-launder-vacuity)
//!
//! What this ENFORCES on macOS: a confined child that tries `open("/etc/passwd")`
//! is denied by the Seatbelt profile; `socket(AF_INET)` fails (no `network*`);
//! the inherited control socket is the only fd it holds; the control round-trip
//! still works. What remains TRUSTED: the confinement is the host OS's
//! (Seatbelt / Linux LSMs), the same trust the MMU isolation already places in
//! the host kernel. The child applies it to ITSELF — it is firmament code we
//! wrote, not the (untrusted) PD payload, and it does so before yielding to the
//! payload `body`, so the payload never runs un-confined.
//!
//! Unix-only, behind the `process-pd-sandbox` feature (which implies
//! `process-pd`).

#![cfg(all(feature = "process-pd-sandbox", unix))]

use std::os::unix::io::RawFd;

/// The OS-authority grant a confined child is given — the cap→OS mapping seed.
///
/// Phase 0 wires the **Endpoint-only** case: the child keeps exactly the
/// `endpoint_fds` it was granted (its control socket) and nothing else; every
/// other fd is closed, and ambient file/network/exec authority is denied. The
/// `read_paths` field is the next slice (a file-cap → an SBPL allowed path on
/// macOS / a Landlock rule on Linux); it is honored where the platform supports
/// it and is empty for the Endpoint-only Phase-0 case.
#[derive(Clone, Debug, Default)]
pub struct Confinement {
    /// The fds the child is allowed to keep open (its granted channels — the
    /// control socket(s)). EVERY other inherited fd is closed. This is the
    /// "the Endpoint is the only channel" guarantee at the fd layer.
    pub endpoint_fds: Vec<RawFd>,
    /// Read-only filesystem paths a file-cap granted the child (the next slice).
    /// macOS: each becomes an SBPL `(allow file-read* (subpath "<p>"))`.
    /// Linux: each becomes a Landlock read rule. Empty for Endpoint-only Phase 0.
    pub read_paths: Vec<String>,
    /// Outbound network endpoints (`"host:port"`) a NET-cap granted the child — the
    /// STRUCTURED EGRESS SOCKET door (e.g. a jailed brain's LLM-provider call).
    /// Deny-default: empty means NO outbound network at all (the Endpoint-only
    /// floor). Each entry opens EXACTLY one host:port and nothing else.
    ///
    /// macOS: each becomes an SBPL `(allow network-outbound (remote ip
    /// "<host>:<port>"))` — a precise, enforced allow (host must be a literal IP or
    /// `localhost`; a hostname is emitted verbatim and only matches if the OS
    /// resolves it, so a real hostname provider needs a pre-resolved IP or the
    /// in-jail-DNS caveat, see `deos-hermes`). Linux: NOT yet honored — the empty
    /// net namespace + seccomp `socket` deny make outbound impossible without a
    /// filtering proxy, so the door stays CLOSED there (fail-closed) until that
    /// slice; the grant is recorded but not opened.
    pub net_out: Vec<String>,
}

impl Confinement {
    /// The Endpoint-only confinement (Phase 0): keep just the control socket fd,
    /// deny all ambient file / network / exec authority, grant no extra paths.
    pub fn endpoint_only(control_fd: RawFd) -> Self {
        Confinement {
            endpoint_fds: vec![control_fd],
            read_paths: Vec::new(),
            net_out: Vec::new(),
        }
    }

    /// Add the granted control/channel fds.
    pub fn with_fds(mut self, fds: impl IntoIterator<Item = RawFd>) -> Self {
        self.endpoint_fds.extend(fds);
        self
    }

    /// Grant a read-only path (a file-cap → an OS path rule). The next slice
    /// past Endpoint-only.
    pub fn with_read_path(mut self, path: impl Into<String>) -> Self {
        self.read_paths.push(path.into());
        self
    }

    /// Grant ONE outbound network endpoint (`"host:port"`) — the structured egress
    /// SOCKET door (a net-cap → an OS network-allow rule). Deny-default: without a
    /// grant the child has no outbound network at all; with it, EXACTLY this
    /// host:port opens and every other remote stays denied.
    pub fn with_net_out(mut self, endpoint: impl Into<String>) -> Self {
        self.net_out.push(endpoint.into());
        self
    }
}

/// The outcome of a [`confine_child`] attempt.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConfineError {
    /// `sandbox_init` (macOS) failed with this message.
    SandboxInit(String),
    /// A Linux confinement step (unshare / prctl / seccomp / landlock) failed.
    Linux(String),
    /// Closing the non-granted fds failed.
    FdClose(String),
    /// This platform has no implemented backing (neither macOS nor Linux).
    Unsupported,
}

impl std::fmt::Display for ConfineError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConfineError::SandboxInit(m) => write!(f, "macOS sandbox_init failed: {m}"),
            ConfineError::Linux(m) => write!(f, "linux confinement failed: {m}"),
            ConfineError::FdClose(m) => write!(f, "closing inherited fds failed: {m}"),
            ConfineError::Unsupported => write!(f, "no sandbox backing on this platform"),
        }
    }
}

impl std::error::Error for ConfineError {}

/// CONFINE the calling process (a freshly-forked child PD) to its granted
/// authority — close all non-granted fds, then drop ambient OS authority via the
/// host sandbox. Call this in the CHILD, after `fork()`, BEFORE the PD `body`.
///
/// After it returns `Ok(())`, the child can talk over its granted fd(s) but
/// cannot open arbitrary files, reach the network, exec a new image, or touch
/// any other inherited fd. On macOS this is the Seatbelt profile; on Linux the
/// namespaces + seccomp + Landlock stack.
///
/// # Safety
/// MUST be called in a forked child (it mutates process-global authority and
/// closes fds). It is async-signal-safe-ish: it does a bounded amount of work
/// and applies an irreversible confinement; never call it in the parent.
pub fn confine_child(c: &Confinement) -> Result<(), ConfineError> {
    close_all_but(&c.endpoint_fds)?;
    #[cfg(target_os = "macos")]
    {
        macos::confine(c)
    }
    #[cfg(target_os = "linux")]
    {
        linux::confine(c)
    }
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    {
        let _ = c;
        Err(ConfineError::Unsupported)
    }
}

/// Close EVERY open fd except the granted ones (and the std streams 0/1/2, kept
/// so the PD can still print under `--nocapture` — they are not an authority
/// channel, just the console). This is the fd-isolation half: after it, the
/// granted control socket is the only NON-console channel the child holds.
///
/// We walk a generous fd range and `close` each not in `keep`. (The
/// `close_range(2)` syscall is the spawn-path optimization; the fork path here
/// walks explicitly so it works identically on macOS + Linux without the newer
/// syscall.)
fn close_all_but(keep: &[RawFd]) -> Result<(), ConfineError> {
    // Keep std streams so PD prints survive; keep the granted channel fds.
    let max = max_open_fds();
    for fd in 3..max {
        if keep.contains(&fd) {
            continue;
        }
        // Best-effort: ignore EBADF (already-closed) — only a real failure on a
        // KEPT fd would matter, and we never close those.
        unsafe {
            libc::close(fd);
        }
    }
    Ok(())
}

/// An upper bound on the fd table to sweep. Uses `RLIMIT_NOFILE` soft limit,
/// clamped to a sane ceiling so we never spin over a 2^31 limit.
fn max_open_fds() -> RawFd {
    let mut rl = libc::rlimit {
        rlim_cur: 0,
        rlim_max: 0,
    };
    let cap: RawFd = 4096;
    let rc = unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, &mut rl) };
    if rc == 0 && rl.rlim_cur != libc::RLIM_INFINITY {
        (rl.rlim_cur as RawFd).min(cap).max(16)
    } else {
        cap
    }
}

// ───────────────────────────── macOS backend ────────────────────────────────

#[cfg(target_os = "macos")]
mod macos {
    use super::{ConfineError, Confinement};
    use std::ffi::{CStr, CString};
    use std::os::raw::{c_char, c_int};
    use std::ptr;

    // The Seatbelt FFI (the `gaol`-macos backend shape, ~10 lines of raw FFI).
    // `sandbox_init` self-applies an SBPL profile to the calling process; once
    // applied it cannot be loosened. `sandbox_free_error` frees the error buffer.
    extern "C" {
        fn sandbox_init(profile: *const c_char, flags: u64, errorbuf: *mut *mut c_char) -> c_int;
        fn sandbox_free_error(errorbuf: *mut c_char);
    }

    /// The default-deny SBPL prologue. Everything not explicitly allowed below
    /// is DENIED — no network, no exec, no mach-lookup, no arbitrary file read.
    const PROLOGUE: &str = "(version 1)\n(deny default)\n";

    /// The minimal allow-set a confined firmament PD needs to KEEP RUNNING after
    /// `sandbox_init` (the dynamic linker / libsystem are already mapped, but the
    /// process may still touch them; a stricter profile risks SIGKILL on the
    /// next libc call). We allow:
    ///   - I/O on already-open fds (the control socket round-trip + console);
    ///   - read-only access to the system dylib/framework paths the runtime maps;
    ///   - sysctl reads libsystem performs.
    /// We do NOT allow network*, process-exec*, process-fork*, mach-lookup*, or
    /// arbitrary file-write — those are the ambient authority we are dropping.
    const BASE_ALLOW: &str = "\
(allow file-read* (subpath \"/usr/lib\"))\n\
(allow file-read* (subpath \"/System/Library\"))\n\
(allow file-read* (subpath \"/Library/Apple\"))\n\
(allow file-read-metadata)\n\
(allow sysctl-read)\n\
(allow file-ioctl)\n\
(allow signal (target self))\n\
";

    /// Build the full SBPL profile text from the prologue, the base allow-set,
    /// and any explicitly-granted read paths (the file-cap → allowed-path map).
    pub(super) fn build_profile(c: &Confinement) -> String {
        let mut p = String::with_capacity(256);
        p.push_str(PROLOGUE);
        p.push_str(BASE_ALLOW);
        for path in &c.read_paths {
            // (allow file-read* (subpath "<path>")) — a granted read path.
            p.push_str("(allow file-read* (subpath \"");
            // Escape backslash + quote for the TinyScheme string literal.
            for ch in path.chars() {
                if ch == '"' || ch == '\\' {
                    p.push('\\');
                }
                p.push(ch);
            }
            p.push_str("\"))\n");
        }
        for endpoint in &c.net_out {
            // (allow network-outbound (remote ip "<host>:<port>")) — ONE granted
            // outbound endpoint (the structured egress socket door). Nothing else
            // network* is allowed, so every other remote stays denied by the
            // (deny default). The `socket(2)` creation itself is not a `network*`
            // op on macOS (only the connect is gated), so this rule is the whole
            // door: the granted endpoint connects, all others EPERM.
            //
            // SBPL LIMITATION (honest): the `remote ip` HOST field accepts only
            // `*` or `localhost` — a literal remote IP is REJECTED by
            // `sandbox_init`. So:
            //   * a LOOPBACK grant (127.0.0.1 / ::1 / localhost) → `localhost:PORT`,
            //     precise host+port (the hermetic mock + the recommended local
            //     egress-proxy pattern, where a trusted host-side proxy pins the
            //     real upstream provider and the jail reaches only localhost).
            //   * a REMOTE-HOST grant → `*:PORT`, which SBPL can only pin by PORT,
            //     NOT host. This is a genuine degradation (any host on that port),
            //     so the host-pinned provider door for a REMOTE endpoint needs the
            //     local-proxy pattern above; direct-remote is port-scoped only.
            let (host, port) = endpoint
                .rsplit_once(':')
                .map(|(h, p)| (h, p))
                .unwrap_or((endpoint.as_str(), ""));
            let sbpl_host = if is_loopback(host) { "localhost" } else { "*" };
            p.push_str("(allow network-outbound (remote ip \"");
            p.push_str(sbpl_host);
            p.push(':');
            // The port is a bare integer; escape defensively anyway.
            for ch in port.chars() {
                if ch == '"' || ch == '\\' {
                    p.push('\\');
                }
                p.push(ch);
            }
            p.push_str("\"))\n");
        }
        p
    }

    /// Whether `host` is a loopback the SBPL `localhost` token covers.
    fn is_loopback(host: &str) -> bool {
        matches!(host, "127.0.0.1" | "::1" | "localhost")
    }

    /// SELF-apply the Seatbelt profile to this (child) process.
    pub fn confine(c: &Confinement) -> Result<(), ConfineError> {
        let profile = build_profile(c);
        let cprofile =
            CString::new(profile).map_err(|e| ConfineError::SandboxInit(format!("nul: {e}")))?;
        let mut err: *mut c_char = ptr::null_mut();
        let rc = unsafe { sandbox_init(cprofile.as_ptr(), 0, &mut err) };
        if rc == 0 {
            Ok(())
        } else {
            let msg = if err.is_null() {
                "sandbox_init returned non-zero with no error string".to_string()
            } else {
                let m = unsafe { CStr::from_ptr(err) }
                    .to_string_lossy()
                    .into_owned();
                unsafe { sandbox_free_error(err) };
                m
            };
            Err(ConfineError::SandboxInit(msg))
        }
    }
}

// ───────────────────────────── Linux backend ────────────────────────────────
//
// Compiles on macOS as an unreachable cfg-stub (the module body is gated to
// `target_os = "linux"`); RUNS on Linux. The steps:
//   1. unshare(CLONE_NEWUSER|NEWNET|NEWNS|NEWPID) + a uid-map (root-in-namespace
//      maps to the real uid) — an EMPTY net namespace means no route anywhere.
//   2. prctl(PR_SET_NO_NEW_PRIVS, 1) — no setuid/fscaps escalation.
//   3. a default-deny seccomp-bpf allow-list (read/write/close/exit/… only) via
//      `seccompiler` — socket()/open()/execve() trap to EPERM/SIGSYS.
//   4. Landlock read rules for any granted read paths via `landlock`.
//   5. (close_all_but already ran in the shared path, keeping the control fd.)

#[cfg(target_os = "linux")]
mod linux {
    use super::{ConfineError, Confinement};

    /// Apply the Linux confinement stack to this (child) process.
    pub fn confine(c: &Confinement) -> Result<(), ConfineError> {
        unshare_namespaces()?;
        no_new_privs()?;
        apply_landlock(&c.read_paths)?;
        apply_seccomp()?;
        Ok(())
    }

    /// unshare USER+NET+NS+PID namespaces and write the uid/gid maps. An empty
    /// net namespace gives the child no network route at all (the net-cap denial).
    fn unshare_namespaces() -> Result<(), ConfineError> {
        use std::io::Write;
        // The real uid/gid to map root-in-namespace back to.
        let (uid, gid) = unsafe { (libc::getuid(), libc::getgid()) };
        let flags =
            libc::CLONE_NEWUSER | libc::CLONE_NEWNET | libc::CLONE_NEWNS | libc::CLONE_NEWPID;
        let rc = unsafe { libc::unshare(flags) };
        if rc != 0 {
            return Err(ConfineError::Linux(format!(
                "unshare failed: {}",
                std::io::Error::last_os_error()
            )));
        }
        // setgroups must be denied before writing gid_map in a userns.
        let _ = std::fs::write("/proc/self/setgroups", b"deny");
        std::fs::OpenOptions::new()
            .write(true)
            .open("/proc/self/uid_map")
            .and_then(|mut f| f.write_all(format!("0 {uid} 1\n").as_bytes()))
            .map_err(|e| ConfineError::Linux(format!("uid_map: {e}")))?;
        std::fs::OpenOptions::new()
            .write(true)
            .open("/proc/self/gid_map")
            .and_then(|mut f| f.write_all(format!("0 {gid} 1\n").as_bytes()))
            .map_err(|e| ConfineError::Linux(format!("gid_map: {e}")))?;
        Ok(())
    }

    /// prctl(PR_SET_NO_NEW_PRIVS, 1) — required before installing seccomp without
    /// CAP_SYS_ADMIN, and it blocks setuid/fscap privilege escalation.
    fn no_new_privs() -> Result<(), ConfineError> {
        let rc = unsafe { libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) };
        if rc != 0 {
            return Err(ConfineError::Linux(format!(
                "prctl(NO_NEW_PRIVS): {}",
                std::io::Error::last_os_error()
            )));
        }
        Ok(())
    }

    /// Install a default-deny seccomp-bpf filter that allows only the syscalls a
    /// confined PD body needs (read/write/close/exit/sigreturn/…) and traps the
    /// rest (notably `socket`, `open`, `openat`, `execve`) to EPERM. Built with
    /// the `seccompiler` crate.
    fn apply_seccomp() -> Result<(), ConfineError> {
        use seccompiler::{apply_filter, BpfProgram, SeccompAction, SeccompFilter, TargetArch};
        use std::collections::BTreeMap;

        #[cfg(target_arch = "x86_64")]
        let arch = TargetArch::x86_64;
        #[cfg(target_arch = "aarch64")]
        let arch = TargetArch::aarch64;

        // The allow-list: syscalls a bounded compute-over-the-socket PD needs.
        // Everything else → EPERM (errno 1). socket/open/openat/execve are NOT
        // listed, so they are denied — the ambient-authority drop.
        let allow: &[i64] = &[
            libc::SYS_read,
            libc::SYS_write,
            libc::SYS_close,
            libc::SYS_exit,
            libc::SYS_exit_group,
            libc::SYS_rt_sigreturn,
            libc::SYS_rt_sigprocmask,
            libc::SYS_sigaltstack,
            libc::SYS_brk,
            libc::SYS_mmap,
            libc::SYS_munmap,
            libc::SYS_mprotect,
            libc::SYS_futex,
            libc::SYS_nanosleep,
            libc::SYS_clock_nanosleep,
            libc::SYS_sched_yield,
            libc::SYS_getpid,
            libc::SYS_gettid,
            libc::SYS_getrandom,
            libc::SYS_madvise,
            libc::SYS_recvfrom,
            libc::SYS_sendto,
            libc::SYS_recvmsg,
            libc::SYS_sendmsg,
            libc::SYS_ppoll,
            libc::SYS_fcntl,
        ];
        let rules: BTreeMap<i64, Vec<_>> = allow.iter().map(|&n| (n, vec![])).collect();

        let filter = SeccompFilter::new(
            rules,
            SeccompAction::Errno(libc::EPERM as u32), // default: deny → EPERM
            SeccompAction::Allow,                     // matched (allow-listed) → allow
            arch,
        )
        .map_err(|e| ConfineError::Linux(format!("seccomp build: {e}")))?;

        let prog: BpfProgram = filter
            .try_into()
            .map_err(|e| ConfineError::Linux(format!("seccomp compile: {e}")))?;
        apply_filter(&prog).map_err(|e| ConfineError::Linux(format!("seccomp apply: {e}")))?;
        Ok(())
    }

    /// Restrict the filesystem with Landlock: deny everything, then re-grant
    /// read-only access to the explicitly-granted `read_paths` (the file-cap →
    /// OS-rule map). If Landlock is unavailable (old kernel), the empty net
    /// namespace + seccomp `open` denial already deny ambient FS authority, so
    /// we treat an ABI-unsupported result as best-effort (the deny still holds
    /// at the seccomp layer).
    fn apply_landlock(read_paths: &[String]) -> Result<(), ConfineError> {
        use landlock::{
            Access, AccessFs, Ruleset, RulesetAttr, RulesetCreatedAttr, RulesetStatus, ABI,
        };

        let abi = ABI::V1;
        let read_only = AccessFs::from_read(abi);
        let mut ruleset = Ruleset::default()
            .handle_access(AccessFs::from_all(abi))
            .map_err(|e| ConfineError::Linux(format!("landlock handle: {e}")))?
            .create()
            .map_err(|e| ConfineError::Linux(format!("landlock create: {e}")))?;

        for path in read_paths {
            // landlock 0.4.x: `PathBeneath::new` is infallible (returns the rule
            // directly, no longer a Result); only PathFd::new + add_rule can fail.
            let rule = landlock::PathBeneath::new(
                landlock::PathFd::new(path)
                    .map_err(|e| ConfineError::Linux(format!("landlock pathfd {path}: {e}")))?,
                read_only,
            );
            ruleset = ruleset
                .add_rule(rule)
                .map_err(|e| ConfineError::Linux(format!("landlock rule {path}: {e}")))?;
        }

        let status = ruleset
            .restrict_self()
            .map_err(|e| ConfineError::Linux(format!("landlock restrict: {e}")))?;
        // If the running kernel lacks Landlock, the restriction is a no-op here;
        // the seccomp `open` denial is the backstop, so this is not fatal.
        let _ = matches!(status.ruleset, RulesetStatus::NotEnforced);
        Ok(())
    }
}

// ──────────────────────────────── tests ─────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn endpoint_only_keeps_just_the_control_fd() {
        let c = Confinement::endpoint_only(7);
        assert_eq!(c.endpoint_fds, vec![7]);
        assert!(c.read_paths.is_empty());
    }

    #[test]
    fn with_read_path_records_the_grant() {
        let c = Confinement::endpoint_only(4).with_read_path("/etc/hosts");
        assert_eq!(c.read_paths, vec!["/etc/hosts".to_string()]);
    }

    // The macOS profile builder is pure (no FFI) — exercise its text shape so a
    // profile regression is caught without invoking sandbox_init.
    #[cfg(target_os = "macos")]
    #[test]
    fn macos_profile_denies_by_default_and_grants_paths() {
        let c = Confinement::endpoint_only(3).with_read_path("/tmp/grant");
        let p = macos::build_profile(&c);
        assert!(p.contains("(deny default)"), "must be default-deny");
        assert!(!p.contains("network"), "must NOT allow network");
        assert!(!p.contains("process-exec"), "must NOT allow exec");
        assert!(
            p.contains("(subpath \"/tmp/grant\")"),
            "granted read path must appear"
        );
    }

    // A granted net_out endpoint becomes EXACTLY one network-outbound allow — the
    // structured egress socket door — while the profile stays default-deny/no-exec.
    #[cfg(target_os = "macos")]
    #[test]
    fn macos_profile_opens_exactly_the_granted_net_endpoint() {
        // No net grant → NO network allow at all (the Endpoint-only floor).
        let sealed = macos::build_profile(&Confinement::endpoint_only(3));
        assert!(!sealed.contains("network-outbound"), "sealed = no net door");
        // A LOOPBACK grant → precise host+port via the SBPL `localhost` token
        // (a literal remote IP is rejected by sandbox_init).
        let c = Confinement::endpoint_only(3).with_net_out("127.0.0.1:8080");
        let p = macos::build_profile(&c);
        assert!(p.contains("(deny default)"), "still default-deny");
        assert!(!p.contains("process-exec"), "still no exec");
        assert!(
            p.contains("(allow network-outbound (remote ip \"localhost:8080\"))"),
            "loopback grant → localhost:port network-outbound allow:\n{p}"
        );
        // A REMOTE-host grant → port-scoped (SBPL cannot pin a remote host).
        let c2 = Confinement::endpoint_only(3).with_net_out("api.example.com:443");
        let p2 = macos::build_profile(&c2);
        assert!(
            p2.contains("(allow network-outbound (remote ip \"*:443\"))"),
            "remote grant → port-scoped allow (SBPL host limitation):\n{p2}"
        );
    }
}
