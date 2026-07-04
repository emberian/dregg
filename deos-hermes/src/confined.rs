//! THE CONFINED LAUNCH — Hermes (or a stand-in ACP peer) running INSIDE an
//! OS-sandboxed firmament host-PD, reachable ONLY over its firmament Endpoint.
//!
//! This is the **ambient-authority confinement face** of a confined deos agent
//! (the [`crate::surface`] module-doc names the two faces). [`crate::bridge`]
//! owns the *authority* face — every tool-call is a cap-gated, metered,
//! receipted turn. This module owns the *ambient* face: the agent process runs
//! in a forked, OS-sandboxed protection-domain whose ONLY channel is a firmament
//! [`Endpoint`](dregg_firmament::process_kernel::PdProcess). Even if a tool-call
//! slipped the gate, the PD physically cannot `open` a file outside its caps,
//! `socket` the network, `execve`, or touch any inherited fd — the host OS
//! sandbox (macOS Seatbelt / Linux ns+seccomp+landlock) refuses it.
//!
//! # What is REAL here vs. a STAND-IN, honestly
//!
//! The confinement is **real**: [`spawn_hermes_in_pd`] launches the agent body
//! through [`ProcessKernel::spawn_pd_confined`], which (right after `fork()`,
//! before the body runs) closes every non-granted fd and self-applies the host
//! sandbox via `dregg_firmament::sandbox::confine_child`. After it returns the
//! child holds exactly one channel — its firmament Endpoint.
//!
//! The agent body run inside that PD is a **stand-in**, and deliberately so:
//!
//!   * A live `hermes acp` subprocess CANNOT be the body. The confined child has
//!     NO exec authority (macOS Seatbelt denies `process-exec*`; Linux seccomp
//!     denies `execve`) — that is the whole point of the sandbox. So the confined
//!     agent must BE a Rust ACP peer, not an `execve`'d external binary. (A
//!     production wiring would compile Hermes's agent loop into the PD body, or
//!     relax the sandbox to allow exec of exactly the agent image; both are out
//!     of scope for Phase-0, and the live `hermes acp` venv is broken in this
//!     environment anyway — `ModuleNotFoundError: No module named 'acp'`.)
//!   * So the body is [`stand_in_acp_peer`]: a small Rust ACP-mock that replays
//!     the SAME `acp_adapter` message shapes [`crate::MockHermesPeer`] does, but
//!     speaks them as ndjson over the firmament Endpoint (its only fd) instead of
//!     in-process. It proves the two things Phase-0 must prove:
//!       1. the child round-trips ACP over the Endpoint (a full
//!          `initialize`→`session/new`→`session/prompt` with permission requests
//!          the parent answers through the [`crate::HermesGateway`]);
//!       2. the child is OS-confined (it ALSO runs the four sandbox probes —
//!          `open(/etc/passwd)` denied, `socket(AF_INET)` denied, only the
//!          Endpoint fd open — and reports the verdict over the wire).
//!
//! # The wire: ACP ndjson over the firmament Endpoint
//!
//! The firmament Endpoint is a `socketpair(AF_UNIX)` — the kernel's end is
//! [`PdProcess::kernel_sock`], the child's end is its only surviving fd. Phase-0
//! repurposes that ONE channel as the ACP control channel: the parent (the deos
//! ACP client) reads/writes ndjson on `kernel_sock`; the confined child
//! reads/writes ndjson on its inherited fd. (The kernel-RPC framing the Endpoint
//! also speaks is NOT multiplexed here — a confined ACP agent uses the Endpoint
//! purely for ACP. A richer agent that also needs kernel RPC would carry a
//! second granted fd; that is the next slice past Endpoint-only.)
//!
//! [`PdAcpTransport`] is the parent-side [`AcpPeer`] over `kernel_sock`, so the
//! UNCHANGED [`crate::AcpClient`] drives the confined agent exactly as it drives
//! the in-process mock — the only difference is WHERE the peer runs.

#![cfg(unix)]

use std::io::{BufRead, BufReader, Write};
use std::os::unix::io::{FromRawFd, RawFd};
use std::os::unix::net::UnixStream;

use serde_json::{Value, json};

use crate::acp_client::{AcpError, AcpPeer, RpcMessage};
use dregg_firmament::process_kernel::{PdProcess, ProcessKernel};

/// The exit-code bitmask the confined stand-in folds its sandbox-probe verdict
/// into — mirrors `dregg-firmament/tests/process_sandbox.rs`. A confined child
/// cannot use a shm region to report (confinement closed every non-Endpoint fd
/// AND denies `shm_open`), so the exit code carries the verdict across the
/// process boundary.
pub mod probe {
    /// The control-socket (firmament Endpoint) ACP round-trip completed.
    pub const IPC_WORKS: i32 = 0x1;
    /// `open("/etc/passwd")` was DENIED by the sandbox profile.
    pub const OPEN_DENIED: i32 = 0x2;
    /// `socket(AF_INET)` failed / had no route (no `network*` authority).
    pub const NET_DENIED: i32 = 0x4;
    /// Exactly one non-std fd open — the firmament Endpoint.
    pub const ONLY_ENDPOINT_FD: i32 = 0x8;
    /// All four confinement teeth held.
    pub const ALL: i32 = IPC_WORKS | OPEN_DENIED | NET_DENIED | ONLY_ENDPOINT_FD;

    /// EGRESS tooth — the GRANTED egress subpath WAS readable inside the PD (the
    /// structured door is open). Only meaningful for a PD launched with an egress
    /// grant ([`super::launch_confined_with_egress`]); the four base teeth still
    /// assert the rest of the jail held around it.
    pub const EGRESS_GRANTED_OPEN: i32 = 0x10;
    /// EGRESS tooth — a path OUTSIDE the grant (a sibling of the granted door) was
    /// STILL DENIED inside the PD. Proves the door is to a specific resource, not a
    /// hole: granting one path does not open its neighbours.
    pub const EGRESS_SIBLING_DENIED: i32 = 0x20;

    /// EGRESS SOCKET tooth — the GRANTED provider endpoint (host:port) WAS
    /// reachable via `connect(2)` from inside the PD (the structured socket door is
    /// open). Only meaningful for a PD launched with a provider net grant
    /// ([`super::EgressPolicy::grant_provider`]); the base jail teeth still assert
    /// the rest of the network stayed denied around it.
    pub const EGRESS_NET_GRANTED_OPEN: i32 = 0x40;
    /// EGRESS SOCKET tooth — an outbound connect to a host:port OUTSIDE the grant
    /// was STILL DENIED inside the PD. Proves the socket door is to a SPECIFIC
    /// endpoint, not "the network": granting one provider does not open any other.
    pub const EGRESS_NET_SIBLING_DENIED: i32 = 0x80;
}

/// A handle on a confined agent PD: the forked, OS-sandboxed child + the
/// parent-side ACP transport over its firmament Endpoint. Drive it with a
/// [`crate::AcpClient`] exactly like any other [`AcpPeer`].
pub struct ConfinedAgent {
    /// The forked, confined child PD (its Endpoint = `kernel_sock`).
    pub pd: PdProcess,
}

impl ConfinedAgent {
    /// The parent-side ACP transport over the confined child's firmament
    /// Endpoint. Hand this to [`crate::AcpClient::new`] as the peer; the client
    /// drives the confined agent over ndjson on the Endpoint.
    pub fn transport(&self) -> std::io::Result<PdAcpTransport> {
        let sock = self.pd.kernel_sock.try_clone()?;
        Ok(PdAcpTransport::new(sock))
    }

    /// Reap the confined child and return its sandbox-probe verdict exit code
    /// (a [`probe`] bitmask; [`probe::ALL`] = every confinement tooth held). Call
    /// AFTER the ACP session has drained (the child exits once its scripted turn
    /// completes). Consumes the handle (it `wait`s the pid).
    pub fn join_verdict(self) -> std::io::Result<i32> {
        self.pd.join()
    }
}

/// LAUNCH a confined agent into an OS-sandboxed firmament host-PD.
///
/// The agent `body` runs inside a child forked by
/// [`ProcessKernel::spawn_pd_confined`]: the confinement (fd-close + host
/// sandbox) is applied BEFORE the body, so the body never runs un-confined. The
/// body's ONLY channel is the firmament Endpoint (`child_endpoint_fd`, recovered
/// inside the body as the single open non-std fd via [`recover_endpoint_fd`]).
///
/// `kernel` is the firmament process-kernel that forks the PD. The returned
/// [`ConfinedAgent`] holds the parent's end of the Endpoint; build its
/// [`PdAcpTransport`] and drive it with a [`crate::AcpClient`].
///
/// # The cwd-cap / net-cap seam
///
/// The original [`crate::surface`] seam named `spawn_hermes_in_pd(host_pd,
/// cwd_cap, net_cap)`. In Phase-0 (Endpoint-only confinement) the agent holds NO
/// file or net authority at all — the cwd-cap and net-cap would each become a
/// `Confinement::with_read_path` (a Seatbelt allow / Landlock rule) and a passed
/// socket fd kept open across the confinement. Those are the next slice past
/// Endpoint-only ([`dregg_firmament::sandbox::Confinement`] already models them);
/// see [`spawn_hermes_in_pd`] for the seam carrying them.
pub fn launch_confined<F>(kernel: &ProcessKernel, body: F) -> std::io::Result<ConfinedAgent>
where
    F: FnOnce(&mut UnixStream) -> i32,
{
    let pd = kernel
        .spawn_pd_confined(vec![], move |_client, _granted| {
            // ── CONFINED CHILD: confinement already applied (every non-Endpoint
            //    fd closed + the host sandbox self-applied). The body runs UNDER
            //    confinement. The `_client` KernelClient wraps the Endpoint fd in
            //    a Mutex we can't unwrap for ndjson, so we recover the raw fd —
            //    confinement guarantees it is the SINGLE open non-std fd. ──
            let fd = match recover_endpoint_fd() {
                Some(fd) => fd,
                None => return -1,
            };
            // SAFETY: `fd` is the inherited, owned Endpoint socketpair fd — the
            // single surviving non-std fd the confinement kept. Nothing else
            // closes it. We forget `_client` so its Drop does not double-close.
            std::mem::forget(_client);
            let mut sock = unsafe { UnixStream::from_raw_fd(fd) };
            body(&mut sock)
        })
        .map_err(|e| std::io::Error::other(e.to_string()))?;
    Ok(ConfinedAgent { pd })
}

/// LAUNCH a confined agent whose jail carries the host's STRUCTURED EGRESS grant —
/// the Endpoint-only jail PLUS exactly the read paths the [`EgressPolicy`] grants,
/// and nothing else.
///
/// This is [`launch_confined`] over the firmament egress knob
/// ([`ProcessKernel::spawn_pd_confined_with`]): the host folds its live egress
/// grants into the PD's sandbox profile via
/// [`EgressPolicy::confinement_for`](crate::egress::EgressPolicy::confinement_for),
/// so a granted host subpath becomes readable inside the PD while every other
/// ambient authority (other files, the network, exec, extra fds) stays denied.
///
/// A SEALED policy (the default) yields the same jail as [`launch_confined`] — no
/// door at all. The agent never mints its own egress; the door is the host's
/// granted, revocable capability.
pub fn launch_confined_with_egress<F>(
    kernel: &ProcessKernel,
    policy: &crate::egress::EgressPolicy,
    body: F,
) -> std::io::Result<ConfinedAgent>
where
    F: FnOnce(&mut UnixStream) -> i32,
{
    // The host builds the profile from its grants. The control fd is forced into
    // the keep-list by `spawn_pd_confined_with`; here we seed it with a placeholder
    // (`-1`) the kernel overrides, so only the GRANTED read paths matter to us.
    let confinement = policy.confinement_for(-1);
    let pd = kernel
        .spawn_pd_confined_with(vec![], confinement, move |_client, _granted| {
            let fd = match recover_endpoint_fd() {
                Some(fd) => fd,
                None => return -1,
            };
            std::mem::forget(_client);
            let mut sock = unsafe { UnixStream::from_raw_fd(fd) };
            body(&mut sock)
        })
        .map_err(|e| std::io::Error::other(e.to_string()))?;
    Ok(ConfinedAgent { pd })
}

/// Probe whether a host `path` is READABLE from inside the confined PD — the
/// egress check. Returns true iff `open(path, O_RDONLY)` succeeds. Run INSIDE a
/// confined body: a GRANTED path returns true (the door is open), an UNGRANTED one
/// returns false (the jail denied it). Public so a confined body can fold the
/// egress verdict bits ([`probe::EGRESS_GRANTED_OPEN`] /
/// [`probe::EGRESS_SIBLING_DENIED`]).
pub fn can_read_path(path: &str) -> bool {
    can_open(path)
}

/// Probe whether an outbound TCP `connect` to `host:port` SUCCEEDS from inside the
/// confined PD — the socket-egress check. `host` must be an IPv4 literal (the
/// provider door's precise form; a hostname would need in-jail DNS, denied). Run
/// INSIDE a confined body: a GRANTED endpoint returns true (the door is open, the
/// connect completes); an UNGRANTED one returns false (the jail EPERM'd the
/// `connect`). Public so a confined body can fold the socket-egress verdict bits
/// ([`probe::EGRESS_NET_GRANTED_OPEN`] / [`probe::EGRESS_NET_SIBLING_DENIED`]).
///
/// A refused connection (`ECONNREFUSED` — reached the host, nothing listening) is
/// treated as reachable (the door let the packet out); a sandbox denial
/// (`EPERM`/`EACCES`) or no route is NOT. So this bit means "the door let us reach
/// the endpoint", distinct from whether a server happened to be listening.
pub fn can_connect_tcp(host: &str, port: u16) -> bool {
    // Parse the dotted-quad IPv4 literal. A non-literal host is out of scope for
    // the in-jail probe (DNS is denied), so treat it as unreachable.
    let octets: Vec<u8> = host
        .split('.')
        .filter_map(|o| o.parse::<u8>().ok())
        .collect();
    if octets.len() != 4 {
        return false;
    }
    let fd = unsafe { libc::socket(libc::AF_INET, libc::SOCK_STREAM, 0) };
    if fd < 0 {
        return false;
    }
    let mut addr: libc::sockaddr_in = unsafe { std::mem::zeroed() };
    addr.sin_family = libc::AF_INET as libc::sa_family_t;
    addr.sin_port = port.to_be();
    addr.sin_addr.s_addr = u32::from_be_bytes([octets[0], octets[1], octets[2], octets[3]]).to_be();
    let rc = unsafe {
        libc::connect(
            fd,
            &addr as *const _ as *const libc::sockaddr,
            std::mem::size_of::<libc::sockaddr_in>() as libc::socklen_t,
        )
    };
    let errno = std::io::Error::last_os_error().raw_os_error().unwrap_or(0);
    unsafe { libc::close(fd) };
    if rc == 0 {
        return true; // connected — the door is open.
    }
    // The door let the packet out but nothing was listening ⇒ still "reachable".
    // A sandbox denial (EPERM/EACCES) or no route ⇒ the door is closed.
    matches!(
        errno,
        libc::ECONNREFUSED | libc::EINPROGRESS | libc::ETIMEDOUT
    )
}

/// LAUNCH HERMES (the stand-in ACP agent) into a confined host-PD — the
/// `spawn_hermes_in_pd` seam, made real.
///
/// This is the concrete realization of the `spawn_hermes_in_pd(host_pd, cwd_cap,
/// net_cap)` SEAM documented in [`crate::surface`]: it forks an OS-sandboxed
/// host-PD and runs the agent inside it, reachable only over its firmament
/// Endpoint. Because the confined child has no exec authority (and the live
/// `hermes acp` install is broken), the agent body is [`stand_in_acp_peer`] — a
/// Rust ACP peer that round-trips the real `acp_adapter` shapes over the Endpoint
/// AND runs the sandbox probes. `script` is the scripted tool-call turn it plays
/// (the SAME [`crate::ScriptedCall`] vocabulary the in-process mock uses).
///
/// `_cwd_cap` / `_net_cap` are the file / network grants a richer confinement
/// would honor (a `Confinement::with_read_path` + a passed socket fd). Phase-0 is
/// Endpoint-only, so they are accepted and recorded but not yet wired into the
/// sandbox profile — the seam carries them for the next slice.
pub fn spawn_hermes_in_pd(
    kernel: &ProcessKernel,
    session_id: &str,
    script: Vec<crate::ScriptedCall>,
    _cwd_cap: Option<&str>,
    _net_cap: Option<RawFd>,
) -> std::io::Result<ConfinedAgent> {
    let session_id = session_id.to_string();
    launch_confined(kernel, move |sock| {
        stand_in_acp_peer(sock, &session_id, script)
    })
}

/// Recover the firmament Endpoint fd inside a confined child: confinement closed
/// every non-std fd except the Endpoint, so it is the SINGLE open fd in `3..64`.
/// Returns `None` if zero or more than one is open (a confinement that did not
/// hold — fail-closed).
fn recover_endpoint_fd() -> Option<RawFd> {
    let mut found: Option<RawFd> = None;
    for fd in 3..64 {
        // F_GETFD returns >=0 for an open fd, -1 (EBADF) for a closed one.
        let rc = unsafe { libc::fcntl(fd, libc::F_GETFD) };
        if rc >= 0 {
            if found.is_some() {
                return None; // more than one non-std fd open — not confined.
            }
            found = Some(fd);
        }
    }
    found
}

// ───────────────────── the confined stand-in ACP agent ──────────────────────

/// THE STAND-IN ACP AGENT — runs INSIDE the confined PD, speaks ACP ndjson over
/// the firmament Endpoint, and runs the sandbox probes. Returns a [`probe`]
/// bitmask exit code (so the parent can assert confinement held).
///
/// It replays the `acp_adapter` message shapes (initialize / session/new /
/// session/prompt → streamed `session/update`s + `session/request_permission`
/// requests → a `PromptResponse`), the SAME shapes [`crate::MockHermesPeer`]
/// emits — but as ndjson on a real socket, from inside the sandbox.
pub fn stand_in_acp_peer(
    sock: &mut UnixStream,
    session_id: &str,
    script: Vec<crate::ScriptedCall>,
) -> i32 {
    let mut verdict = run_sandbox_probes();

    let reader_sock = match sock.try_clone() {
        Ok(s) => s,
        Err(_) => return verdict, // can't speak ACP; report the sandbox verdict.
    };
    let mut reader = BufReader::new(reader_sock);

    match run_acp_session(sock, &mut reader, session_id, &script) {
        Ok(()) => verdict |= probe::IPC_WORKS,
        Err(_) => { /* IPC did not complete; leave the IPC bit clear. */ }
    }
    verdict
}

/// Run the four sandbox probes (mirror of `tests/process_sandbox.rs`) and fold
/// the result into the probe bitmask. Runs INSIDE the confined child.
///
/// Public so the [`crate::mcp_server`] confined-`terminal` body can prove the
/// shell ran in the container (ambient-authority probes denied) from inside its
/// own PD, reusing the SAME teeth the stand-in agent reports.
pub fn run_sandbox_probes() -> i32 {
    let mut v = 0;
    if !can_open("/etc/passwd") {
        v |= probe::OPEN_DENIED;
    }
    if !can_inet_socket() {
        v |= probe::NET_DENIED;
    }
    // The Endpoint must be the ONLY non-std fd. We are about to clone it for the
    // reader, so probe BEFORE any clone (the caller runs probes first). Count
    // open fds in 3..64; exactly one (the Endpoint) is expected.
    if count_open_fds_above_std(64) == 1 {
        v |= probe::ONLY_ENDPOINT_FD;
    }
    v
}

/// Drive the ACP server half over the Endpoint: answer the client's
/// initialize / session/new / session/prompt, stream the scripted tool-call
/// permission requests, record outcomes, and send the final PromptResponse.
fn run_acp_session<R: BufRead>(
    sock: &mut UnixStream,
    reader: &mut R,
    session_id: &str,
    script: &[crate::ScriptedCall],
) -> Result<(), AcpError> {
    // 1. initialize.
    let init = recv_line(reader)?;
    let id = init.id.clone().unwrap_or(Value::Null);
    send_line(
        sock,
        &RpcMessage::response(
            id,
            json!({
                "protocolVersion": crate::acp_client::ACP_PROTOCOL_VERSION,
                "agentInfo": { "name": "hermes-agent", "version": "confined-stand-in" },
                "agentCapabilities": { "loadSession": true },
                "authMethods": []
            }),
        ),
    )?;

    // 2. session/new.
    let new_s = recv_line(reader)?;
    let id = new_s.id.clone().unwrap_or(Value::Null);
    send_line(
        sock,
        &RpcMessage::response(
            id,
            json!({ "sessionId": session_id, "models": [], "modes": [] }),
        ),
    )?;

    // 3. session/prompt → stream the turn.
    let prompt = recv_line(reader)?;
    let prompt_id = prompt.id.clone().unwrap_or(Value::Null);

    // opening agent chunk.
    send_line(
        sock,
        &update(
            session_id,
            json!({
                "sessionUpdate": "agent_message_chunk",
                "content": { "type": "text", "text": "working (confined)… " }
            }),
        ),
    )?;

    // each scripted call: a tool_call event + a request_permission the client
    // answers through the gateway; then a tool_call_update with the status.
    let mut next_perm_id = 9000i64;
    for (i, call) in script.iter().enumerate() {
        let tool_call_id = format!("tc-{}", i + 1);
        let kind = call.acp_kind_str();
        send_line(
            sock,
            &update(
                session_id,
                json!({
                    "sessionUpdate": "tool_call",
                    "toolCallId": tool_call_id,
                    "toolName": call.name,
                    "kind": kind,
                    "status": "pending",
                    "rawInput": call.raw_input,
                }),
            ),
        )?;
        next_perm_id += 1;
        send_line(
            sock,
            &RpcMessage::request(
                next_perm_id,
                "session/request_permission",
                json!({
                    "sessionId": session_id,
                    "toolCall": {
                        "toolCallId": tool_call_id,
                        "toolName": call.name,
                        "kind": kind,
                        "status": "pending",
                        "rawInput": call.raw_input,
                    },
                    "options": [
                        { "optionId": "allow_once", "kind": "allow_once", "name": "Allow once" },
                        { "optionId": "deny", "kind": "reject_once", "name": "Deny" }
                    ]
                }),
            ),
        )?;
        // The client answers the permission request (running it through the
        // gateway). Consume its response.
        let resp = recv_line(reader)?;
        let allowed = resp
            .result
            .as_ref()
            .and_then(|r| r.get("outcome"))
            .and_then(|o| o.get("optionId"))
            .and_then(|v| v.as_str())
            .map(|s| s == "allow_once" || s == "allow_always")
            .unwrap_or(false);
        send_line(
            sock,
            &update(
                session_id,
                json!({
                    "sessionUpdate": "tool_call_update",
                    "toolCallId": tool_call_id,
                    "status": if allowed { "completed" } else { "failed" },
                }),
            ),
        )?;
    }

    // closing chunk + the prompt response.
    send_line(
        sock,
        &update(
            session_id,
            json!({
                "sessionUpdate": "agent_message_chunk",
                "content": { "type": "text", "text": "done." }
            }),
        ),
    )?;
    send_line(
        sock,
        &RpcMessage::response(prompt_id, json!({ "stopReason": "end_turn" })),
    )?;
    Ok(())
}

/// A `session/update` notification frame.
fn update(session_id: &str, body: Value) -> RpcMessage {
    RpcMessage::notification(
        "session/update",
        json!({ "sessionId": session_id, "update": body }),
    )
}

/// Write one ndjson frame to the Endpoint.
fn send_line(sock: &mut UnixStream, msg: &RpcMessage) -> Result<(), AcpError> {
    let line = serde_json::to_string(msg).map_err(|e| AcpError::Parse(e.to_string()))?;
    sock.write_all(line.as_bytes())?;
    sock.write_all(b"\n")?;
    sock.flush()?;
    Ok(())
}

/// Read one ndjson frame from the Endpoint (skipping blank lines).
fn recv_line<R: BufRead>(reader: &mut R) -> Result<RpcMessage, AcpError> {
    let mut line = String::new();
    loop {
        line.clear();
        let n = reader.read_line(&mut line)?;
        if n == 0 {
            return Err(AcpError::Closed);
        }
        let t = line.trim();
        if t.is_empty() {
            continue;
        }
        return serde_json::from_str(t).map_err(|e| AcpError::Parse(e.to_string()));
    }
}

// ─────────────── serving an in-process AcpPeer over the Endpoint ─────────────

/// SERVE an in-process [`AcpPeer`] (the SERVER half — e.g. a brain-driven
/// [`crate::HermesAgentPeer`]) over the confined child's firmament Endpoint.
///
/// This is the inverse of [`PdAcpTransport`]: that adapter lets the PARENT drive a
/// peer that lives over the socket; this loop lets the CHILD run a peer that lives
/// IN-PROCESS (compiled into the jail) while its wire is the socket. It reads each
/// client frame off the Endpoint, feeds it to `peer.send` (the peer queues its
/// replies), then drains `peer.recv` back onto the wire — the exact call pattern
/// [`crate::AcpClient`] expects, just with the peer on the far side of a real fd.
///
/// It is how a REAL brain runs inside the exec-denied jail: the on-box
/// [`crate::LocalBrain`] is `execve`-free and does no ambient I/O, so it decides
/// entirely in-process; every tool-call it reaches for crosses this Endpoint as a
/// `session/request_permission` the PARENT answers through the
/// [`crate::HermesGateway`] (which stays OUTSIDE the jail, on the verified
/// executor). The credential/model side of a *live* brain cannot run here — the
/// jail denies the socket it would need — so the compiled-in brain is the on-box
/// one; a live provider would ride a granted egress socket (the next slice).
///
/// Returns when the brain's turn completes ([`crate::HermesAgentPeer::turn_complete`])
/// — so the confined body exits promptly without waiting on an EOF the still-open
/// client would never send — or `Ok(())` if the client hangs up first.
pub fn serve_acp_peer_over_endpoint<P: AcpPeer>(
    sock: &mut UnixStream,
    peer: &mut P,
    turn_complete: impl Fn(&P) -> bool,
) -> Result<(), AcpError> {
    let reader_sock = sock.try_clone()?;
    let mut reader = BufReader::new(reader_sock);
    loop {
        // Block for the next client frame (initialize / session/new /
        // session/prompt / a permission response). EOF ⇒ the client hung up.
        let msg = match recv_line(&mut reader) {
            Ok(m) => m,
            Err(AcpError::Closed) => return Ok(()),
            Err(e) => return Err(e),
        };
        peer.send(&msg)?;
        // Drain everything the peer queued in response and put it on the wire.
        loop {
            match peer.recv() {
                Ok(out) => send_line(sock, &out)?,
                Err(AcpError::Closed) => break, // nothing more queued right now.
                Err(e) => return Err(e),
            }
        }
        // The brain finished the turn and its final response is out — done.
        if turn_complete(peer) {
            return Ok(());
        }
    }
}

// ───────────────────── the parent-side ACP transport ────────────────────────

/// The parent-side [`AcpPeer`] over a confined agent's firmament Endpoint — real
/// ndjson JSON-RPC on the `kernel_sock` UnixStream. The UNCHANGED
/// [`crate::AcpClient`] drives the confined agent through this exactly as it
/// drives the in-process mock; the only difference is WHERE the peer runs.
pub struct PdAcpTransport {
    writer: UnixStream,
    reader: BufReader<UnixStream>,
}

impl PdAcpTransport {
    /// Wrap a clone of the kernel's end of the firmament Endpoint.
    pub fn new(sock: UnixStream) -> PdAcpTransport {
        let reader = BufReader::new(sock.try_clone().expect("clone Endpoint for reading"));
        PdAcpTransport {
            writer: sock,
            reader,
        }
    }
}

impl AcpPeer for PdAcpTransport {
    fn send(&mut self, msg: &RpcMessage) -> Result<(), AcpError> {
        let line = serde_json::to_string(msg).map_err(|e| AcpError::Parse(e.to_string()))?;
        self.writer.write_all(line.as_bytes())?;
        self.writer.write_all(b"\n")?;
        self.writer.flush()?;
        Ok(())
    }

    fn recv(&mut self) -> Result<RpcMessage, AcpError> {
        let mut line = String::new();
        loop {
            line.clear();
            let n = self.reader.read_line(&mut line)?;
            if n == 0 {
                return Err(AcpError::Closed);
            }
            let t = line.trim();
            if t.is_empty() {
                continue;
            }
            return serde_json::from_str(t).map_err(|e| AcpError::Parse(e.to_string()));
        }
    }
}

// ─────────────────────────── sandbox probe helpers ──────────────────────────
// Mirror dregg-firmament/tests/process_sandbox.rs — proven there; replicated
// here so the confined STAND-IN reports the same confinement teeth.

/// Try to `open` a path read-only; returns whether it SUCCEEDED. Under the
/// confinement an un-granted path must be denied (false).
fn can_open(path: &str) -> bool {
    let c = match std::ffi::CString::new(path) {
        Ok(c) => c,
        Err(_) => return false,
    };
    let fd = unsafe { libc::open(c.as_ptr(), libc::O_RDONLY) };
    if fd >= 0 {
        unsafe { libc::close(fd) };
        true
    } else {
        false
    }
}

/// Try to create an AF_INET socket and begin a connect to a public address;
/// returns whether the NETWORK was reachable. Under confinement either
/// `socket(2)` is denied (macOS Seatbelt) or there is no route (Linux empty net
/// namespace), so this is false.
fn can_inet_socket() -> bool {
    let fd = unsafe { libc::socket(libc::AF_INET, libc::SOCK_STREAM, 0) };
    if fd < 0 {
        return false;
    }
    let mut addr: libc::sockaddr_in = unsafe { std::mem::zeroed() };
    addr.sin_family = libc::AF_INET as libc::sa_family_t;
    addr.sin_port = (80u16).to_be();
    addr.sin_addr.s_addr = u32::from_be_bytes([1, 1, 1, 1]).to_be();
    let rc = unsafe {
        libc::connect(
            fd,
            &addr as *const _ as *const libc::sockaddr,
            std::mem::size_of::<libc::sockaddr_in>() as libc::socklen_t,
        )
    };
    let errno = std::io::Error::last_os_error().raw_os_error().unwrap_or(0);
    unsafe { libc::close(fd) };
    if rc == 0 {
        return true;
    }
    !matches!(
        errno,
        libc::ENETUNREACH | libc::EPERM | libc::EHOSTUNREACH | libc::EACCES | libc::EAFNOSUPPORT
    ) && matches!(
        errno,
        libc::EINPROGRESS | libc::ECONNREFUSED | libc::ETIMEDOUT
    )
}

/// Count open fds in `3..max` (above the std streams).
fn count_open_fds_above_std(max: libc::c_int) -> usize {
    let mut n = 0;
    for fd in 3..max {
        let rc = unsafe { libc::fcntl(fd, libc::F_GETFD) };
        if rc >= 0 {
            n += 1;
        }
    }
    n
}
