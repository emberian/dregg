//! PROVIDER-ONLY EGRESS — the structured SOCKET door for a jailed LIVE brain.
//!
//! The jail denies ALL ambient network. This slice adds ONE structured, revocable
//! door: the host may open EXACTLY the LLM provider's `host:port` and nothing else,
//! so a live brain's model-completion call rides the granted socket while execve /
//! open / every other host:port stay denied.
//!
//! Run (default, crisp OS-level door teeth — no network stack needed):
//!   `cd deos-hermes && cargo test --test provider_egress`
//! Run (the LIVE brain riding the door, against a hermetic local mock provider):
//!   `cd deos-hermes && cargo test --test provider_egress --features live-brain`
//!
//! The teeth:
//!   1. SEALED → the provider endpoint is DENIED from inside the jail (no door).
//!   2. GRANTED → the provider endpoint is reachable (the door is open)…
//!   3. …while a DIFFERENT host:port (a live listener outside the grant) STILL
//!      EPERMs — the door is to ONE endpoint, not "the network".
//!   4. REVOKE → the endpoint is denied again.
//!   5. The base jail holds around the door: execve / host-FS / arbitrary socket
//!      each denied; tool-calls still receipt through the gate.
//!   6. (live-brain) A real model inside the jail POSTs its completion over the
//!      granted socket to a local mock provider — and its tool-call still crosses
//!      the Endpoint to the gate as a receipted turn.

#![cfg(unix)]

use std::io::Read;
use std::net::TcpListener;
use std::sync::{Arc, RwLock};

use deos_hermes::host::escape;
use deos_hermes::{DreggHost, GrantRegistry, HermesGateway};
use dregg_firmament::process_kernel::ProcessKernel;
use dregg_sdk::{AgentCipherclerk, AgentRuntime, HeldToken};

fn grantor() -> (AgentRuntime, HeldToken) {
    let mut cclerk = AgentCipherclerk::new();
    let root = cclerk.mint_token(&[7u8; 32], "deos");
    let rt = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    (rt, root)
}

fn default_gateway(rt: &AgentRuntime, root: HeldToken) -> HermesGateway<'_> {
    let registry =
        GrantRegistry::default_for_session(1_000_000).with_standard_tool_grants(1_000_000);
    HermesGateway::new(rt, root, registry)
}

/// A bound, listening loopback socket the jail can be pointed at. Returns the port
/// and keeps the listener alive on a detached accept thread (so a granted connect
/// COMPLETES the handshake, and an ungranted one proves a SANDBOX denial — not a
/// mere connection-refused). The thread is abandoned at process exit.
fn spawn_listener() -> u16 {
    let listener = TcpListener::bind("127.0.0.1:0").expect("bind loopback listener");
    let port = listener.local_addr().unwrap().port();
    std::thread::spawn(move || {
        for stream in listener.incoming() {
            // Drain + drop; we only need the handshake to complete.
            if let Ok(mut s) = stream {
                let mut buf = [0u8; 256];
                let _ = s.read(&mut buf);
            }
        }
    });
    port
}

/// (1)+(2)+(3)+(5) The provider-only socket door: SEALED denies, GRANTED opens
/// EXACTLY the granted endpoint, a live sibling endpoint stays denied, and the base
/// jail (execve/host-FS/arbitrary-socket) holds around the door with receipts still
/// flowing.
#[test]
fn provider_socket_door_opens_exactly_one_endpoint() {
    let kernel = ProcessKernel::new();
    let granted_port = spawn_listener();
    let sibling_port = spawn_listener(); // a LIVE listener OUTSIDE the grant.

    // ── SEALED (default): the provider endpoint is DENIED — no door at all. ──
    let (rt, root) = grantor();
    let sealed = DreggHost::new();
    assert!(sealed.egress.is_sealed());
    let r = sealed
        .run_hosted_agent_net(
            &kernel,
            default_gateway(&rt, root),
            "read the source then run the build",
            Some(("127.0.0.1", granted_port)),
            None,
        )
        .expect("sealed hosted run");
    assert!(r.jailed, "still jailed; verdict=0x{:x}", r.verdict);
    assert!(
        !r.egress_net_granted_open,
        "SEALED host must DENY the provider socket (no door); verdict=0x{:x}",
        r.verdict
    );

    // ── GRANTED: the host opens a door to EXACTLY 127.0.0.1:granted_port. ──
    let (rt, root) = grantor();
    let host = DreggHost::new().with_egress_provider("127.0.0.1", granted_port);
    assert!(!host.egress.is_sealed());
    assert!(host.egress.admits_connect("127.0.0.1", granted_port));
    assert!(!host.egress.admits_connect("127.0.0.1", sibling_port));

    let r = host
        .run_hosted_agent_net(
            &kernel,
            default_gateway(&rt, root),
            "read the source then run the build",
            Some(("127.0.0.1", granted_port)),
            Some(("127.0.0.1", sibling_port)),
        )
        .expect("granted hosted run");

    // The base jail STILL holds around the door.
    assert!(
        r.jailed,
        "the base jail (file/other-net/exec/fd) still holds around the socket door; \
         verdict=0x{:x}",
        r.verdict
    );
    assert_eq!(
        r.verdict & escape::ALL_NEUTRALIZED,
        escape::ALL_NEUTRALIZED,
        "execve / host-FS read / arbitrary socket each still denied; verdict=0x{:x}",
        r.verdict
    );
    // THE GRANTED provider socket is reachable…
    assert!(
        r.egress_net_granted_open,
        "the GRANTED provider endpoint must be reachable inside the jail; verdict=0x{:x}",
        r.verdict
    );
    // …and a DIFFERENT live endpoint outside the grant STAYS DENIED (the door is
    // to ONE endpoint, not "the network").
    assert!(
        r.egress_net_sibling_denied,
        "a live host:port OUTSIDE the grant must STAY EPERM'd (specific door); verdict=0x{:x}",
        r.verdict
    );
    // Receipts still flow through the gate around the open door.
    assert!(
        r.admitted_count() >= 1 && r.receipts().iter().all(|h| h.len() == 64),
        "tool-calls still receipt through the gate; admits={}",
        r.admitted_count()
    );

    // ── REVOKE: the door closes; the next jail is sealed against it again. ──
    let (rt, root) = grantor();
    let mut revoked = DreggHost::new().with_egress_provider("127.0.0.1", granted_port);
    revoked.egress.revoke_provider("127.0.0.1", granted_port);
    assert!(revoked.egress.is_sealed(), "revoke closed the socket door");
    let r = revoked
        .run_hosted_agent_net(
            &kernel,
            default_gateway(&rt, root),
            "read the source",
            Some(("127.0.0.1", granted_port)),
            None,
        )
        .expect("revoked hosted run");
    assert!(
        !r.egress_net_granted_open,
        "after REVOKE the provider socket is DENIED again; verdict=0x{:x}",
        r.verdict
    );
}

// ─────────────────── the LIVE brain riding the provider door ──────────────────
//
// Behind `live-brain`: a REAL HttpLlm brain runs INSIDE the jail and POSTs its
// model completion over the granted socket to a HERMETIC local mock provider
// (a literal-IP loopback http endpoint — no DNS, no TLS). The mock returns an
// OpenAI-shaped tool-call, which the brain surfaces as a tool-call crossing the
// Endpoint to the gate → a receipted turn. execve / other-net stay denied.

#[cfg(feature = "live-brain")]
#[test]
fn live_brain_in_jail_rides_the_provider_door_to_a_mock() {
    use std::io::Write as _;
    use std::sync::atomic::{AtomicUsize, Ordering};

    // A hermetic mock OpenAI-compatible provider on loopback. Each POST to
    // /v1/chat/completions gets a `Connection: close` response: the FIRST is a
    // tool-call (read_file), later ones a plain-text finish. It records hit count.
    let listener = TcpListener::bind("127.0.0.1:0").expect("bind mock provider");
    let port = listener.local_addr().unwrap().port();
    let hits = Arc::new(AtomicUsize::new(0));
    let hits_srv = hits.clone();
    std::thread::spawn(move || {
        for stream in listener.incoming() {
            let Ok(mut s) = stream else { continue };
            // Read the request head (+ best-effort body) so the client isn't RST.
            let mut buf = Vec::new();
            let mut tmp = [0u8; 1024];
            loop {
                match s.read(&mut tmp) {
                    Ok(0) => break,
                    Ok(n) => {
                        buf.extend_from_slice(&tmp[..n]);
                        // Stop once we have the full head (+ whatever body arrived).
                        if buf.windows(4).any(|w| w == b"\r\n\r\n") {
                            break;
                        }
                    }
                    Err(_) => break,
                }
            }
            // Only a REAL completion POST counts (a bare liveness connect that
            // sends no request is not a completion and must not consume a response
            // slot).
            if !buf.windows(4).any(|w| w == b"POST") {
                continue;
            }
            let n = hits_srv.fetch_add(1, Ordering::SeqCst);
            let body = if n == 0 {
                // First completion: the model calls a tool.
                r#"{"choices":[{"message":{"role":"assistant","content":null,"tool_calls":[{"id":"c1","type":"function","function":{"name":"read_file","arguments":"{\"path\":\"src/lib.rs\"}"}}]}}]}"#
            } else {
                // Subsequent: the model finishes in text.
                r#"{"choices":[{"message":{"role":"assistant","content":"done — read the file."}}]}"#
            };
            let resp = format!(
                "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nConnection: close\r\nContent-Length: {}\r\n\r\n{}",
                body.len(),
                body
            );
            let _ = s.write_all(resp.as_bytes());
            let _ = s.flush();
        }
    });

    // Point the LIVE brain at the mock (provider-neutral OpenAI-compatible path).
    // SAFETY: single-threaded env mutation before any brain reads it; this test
    // binary is the only setter.
    unsafe {
        std::env::set_var("DREGG_LLM_API_KEY", "sk-DEOS-EGRESS-TEST-DONOTLEAK");
        std::env::set_var("DREGG_LLM_BASE", format!("http://127.0.0.1:{port}/v1"));
        std::env::set_var("DREGG_LLM_MODEL", "mock-model");
    }

    let kernel = ProcessKernel::new();
    let sibling_port = spawn_listener(); // a live endpoint OUTSIDE the grant.
    let (rt, root) = grantor();
    // The host opens the provider door to exactly the mock's host:port.
    let host = DreggHost::new().with_egress_provider("127.0.0.1", port);

    let report = host
        .run_hosted_agent_live(
            &kernel,
            default_gateway(&rt, root),
            "read the source file, please",
            // No raw granted-probe here: the LIVE reqwest completion IS the
            // door-reaches-provider proof (a raw probe would perturb the stateful
            // mock). The ungranted sibling still proves the door is specific.
            None,
            Some(("127.0.0.1", sibling_port)),
        )
        .expect("run a LIVE brain in the jail over the provider door");

    // THE JAIL STILL DENIES the rest — execve / host-FS / arbitrary socket.
    assert!(
        report.jailed,
        "still jailed; verdict=0x{:x}",
        report.verdict
    );
    assert_eq!(
        report.verdict & escape::ALL_NEUTRALIZED,
        escape::ALL_NEUTRALIZED,
        "execve / host-FS / arbitrary socket each still denied; verdict=0x{:x}",
        report.verdict
    );
    // THE DOOR IS SPECIFIC — the sibling endpoint stayed denied.
    assert!(
        report.egress_net_sibling_denied,
        "a live endpoint OUTSIDE the grant stayed denied; verdict=0x{:x}",
        report.verdict
    );

    // THE LIVE MODEL'S COMPLETION CALL RODE THE DOOR — the mock provider was hit
    // from INSIDE the jail (the granted socket carried the model request).
    assert!(
        hits.load(Ordering::SeqCst) >= 1,
        "the jailed brain reached the mock provider over the granted socket"
    );

    // …AND ITS TOOL-CALL STILL RECEIPTED THROUGH THE GATE — the model's read_file
    // crossed the Endpoint to the gateway as a cap-gated, receipted dregg turn.
    let read_call = report
        .tool_verdicts
        .iter()
        .find(|v| v.tool == "read_file")
        .expect("the live model reached for read_file");
    assert!(
        read_call.admitted,
        "the model's tool-call was admitted + receipted across the Endpoint"
    );
    assert!(
        report.receipts().iter().all(|h| h.len() == 64),
        "each admitted call carries a real 64-hex receipt"
    );

    unsafe {
        std::env::remove_var("DREGG_LLM_API_KEY");
        std::env::remove_var("DREGG_LLM_BASE");
        std::env::remove_var("DREGG_LLM_MODEL");
    }
}
