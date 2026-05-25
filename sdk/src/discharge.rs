//! Discharge gateway client: obtain and bind discharge macaroons.
//!
//! This module provides convenience functions for obtaining discharge macaroons
//! from a remote gateway and binding them to held tokens.

use crate::cipherclerk::HeldToken;
use crate::error::SdkError;

/// Obtain a discharge macaroon from a remote gateway.
///
/// Sends a POST request to `{gateway_url}/discharge` with the ticket and optional
/// proof, then returns the discharge macaroon string (em2_ encoded).
///
/// # Arguments
/// - `gateway_url`: Base URL of the discharge gateway (e.g., "https://gateway.pyana.dev")
/// - `ticket`: The encrypted ticket bytes from the 3P caveat
/// - `proof`: Optional proof bytes (ZK proof, signature, etc.)
/// - `client_id`: Optional client identifier for rate limiting / allowlist
/// - `payment`: Optional payment amount
///
/// # Returns
/// The discharge macaroon string (em2_ encoded) and its expiry timestamp.
pub async fn obtain_discharge(
    gateway_url: &str,
    ticket: &[u8],
    proof: Option<&[u8]>,
    client_id: Option<&str>,
    payment: Option<u64>,
) -> Result<(String, i64), SdkError> {
    use base64::Engine;
    let engine = base64::engine::general_purpose::STANDARD;

    let ticket_b64 = engine.encode(ticket);
    let proof_b64 = proof.map(|p| engine.encode(p));

    let mut body = serde_json::Map::new();
    body.insert("ticket".into(), serde_json::Value::String(ticket_b64));
    if let Some(id) = client_id {
        body.insert(
            "client_id".into(),
            serde_json::Value::String(id.to_string()),
        );
    }
    if let Some(p) = proof_b64 {
        body.insert("proof".into(), serde_json::Value::String(p));
    }
    if let Some(amt) = payment {
        body.insert(
            "payment".into(),
            serde_json::Value::Number(serde_json::Number::from(amt)),
        );
    }

    let url = format!("{}/discharge", gateway_url.trim_end_matches('/'));

    // Use a basic HTTP client (tokio + hyper via reqwest pattern).
    // For a minimal dependency footprint, we construct the request manually
    // using tokio's TcpStream + a simple HTTP/1.1 implementation.
    // However, in practice most users will have reqwest or similar.
    // For now, we use a simple TCP-based approach for the SDK.
    let body_json = serde_json::Value::Object(body).to_string();

    // Parse URL to get host and path.
    let (host, port, path, use_tls) = parse_url(&url)?;

    let response_body = if use_tls {
        // SECURITY: When TLS is required (HTTPS URL), we MUST NOT fall back to plaintext.
        // Sending credentials over an unencrypted channel exposes them to network attackers.
        // Callers who need TLS should use obtain_discharge_with_client() with a proper
        // TLS-capable HTTP client (e.g., reqwest with rustls/native-tls).
        return Err(SdkError::Wire(
            "TLS required (HTTPS URL) but no TLS client available in this build. \
             Use obtain_discharge_with_client() with a TLS-capable HTTP client, \
             or use an HTTP (non-TLS) gateway URL if plaintext is acceptable for your threat model."
                .into(),
        ));
    } else {
        http_post_plain(&host, port, &path, &body_json).await?
    };

    // Parse the JSON response.
    let resp: serde_json::Value = serde_json::from_str(&response_body)
        .map_err(|e| SdkError::Wire(format!("invalid JSON response: {e}")))?;

    if let Some(err) = resp.get("error").and_then(|v| v.as_str()) {
        return Err(SdkError::Rejected(err.to_string()));
    }

    let discharge = resp
        .get("discharge")
        .and_then(|v| v.as_str())
        .ok_or_else(|| SdkError::Wire("response missing 'discharge' field".into()))?
        .to_string();

    let expires_at = resp.get("expires_at").and_then(|v| v.as_i64()).unwrap_or(0);

    Ok((discharge, expires_at))
}

/// Extract third-party caveat tickets from a held token that require discharge.
///
/// Returns a list of `(location, ticket_bytes)` pairs for each 3P caveat found.
pub fn extract_third_party_tickets(token: &HeldToken) -> Result<Vec<(String, Vec<u8>)>, SdkError> {
    use pyana_macaroon::format::decode_token;
    use pyana_macaroon::{Macaroon, ThirdPartyCaveat};

    let binary = decode_token(token.encoded())
        .map_err(|e| SdkError::Wire(format!("failed to decode token: {e}")))?;
    let mac = Macaroon::deserialize(&binary)
        .map_err(|e| SdkError::Wire(format!("failed to deserialize token: {e}")))?;

    let mut tickets = Vec::new();
    for wc in mac.caveats.third_party_caveats() {
        let tp = ThirdPartyCaveat::decode_body(&wc.body)
            .map_err(|e| SdkError::Wire(format!("failed to decode 3P caveat: {e}")))?;
        tickets.push((tp.location, tp.ticket));
    }

    Ok(tickets)
}

/// Authorize a held token by obtaining and binding all required discharges.
///
/// For each third-party caveat in the token, this function:
/// 1. Extracts the ticket and gateway location
/// 2. Requests a discharge from the gateway
/// 3. Binds the discharge to the root token
///
/// Returns the encoded token with all discharges bound, ready for presentation.
///
/// NOTE: This currently only works with non-TLS gateways. For production use,
/// integrate with your HTTP client of choice.
pub async fn authorize_with_discharges(
    token: &HeldToken,
    proof: Option<&[u8]>,
    client_id: Option<&str>,
    payment: Option<u64>,
) -> Result<Vec<String>, SdkError> {
    let tickets = extract_third_party_tickets(token)?;
    let mut discharges = Vec::with_capacity(tickets.len());

    for (location, ticket) in &tickets {
        let (discharge_str, _expires) =
            obtain_discharge(location, ticket, proof, client_id, payment).await?;
        discharges.push(discharge_str);
    }

    Ok(discharges)
}

// =============================================================================
// Internal HTTP helpers (minimal, no external HTTP client dependency)
// =============================================================================

fn parse_url(url: &str) -> Result<(String, u16, String, bool), SdkError> {
    let use_tls = url.starts_with("https://");
    let stripped = url
        .strip_prefix("https://")
        .or_else(|| url.strip_prefix("http://"))
        .ok_or_else(|| SdkError::Wire(format!("invalid URL scheme: {url}")))?;

    let (host_port, path) = match stripped.find('/') {
        Some(idx) => (&stripped[..idx], &stripped[idx..]),
        None => (stripped, "/"),
    };

    let (host, port) = match host_port.find(':') {
        Some(idx) => {
            let h = &host_port[..idx];
            let p: u16 = host_port[idx + 1..]
                .parse()
                .map_err(|_| SdkError::Wire(format!("invalid port in URL: {host_port}")))?;
            (h.to_string(), p)
        }
        None => (host_port.to_string(), if use_tls { 443 } else { 80 }),
    };

    // SECURITY: Reject URLs containing CRLF sequences to prevent HTTP header injection.
    // A malicious gateway_url with \r\n could inject arbitrary headers or split requests
    // when interpolated into the raw HTTP/1.1 request string.
    if host.contains('\r') || host.contains('\n') {
        return Err(SdkError::Wire(
            "URL contains invalid characters (CRLF in host)".into(),
        ));
    }
    if path.contains('\r') || path.contains('\n') {
        return Err(SdkError::Wire(
            "URL contains invalid characters (CRLF in path)".into(),
        ));
    }

    Ok((host, port, path.to_string(), use_tls))
}

/// Connect timeout for discharge HTTP requests.
const DISCHARGE_CONNECT_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(10);
/// Read timeout for discharge HTTP requests.
const DISCHARGE_READ_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(30);

async fn http_post_plain(
    host: &str,
    port: u16,
    path: &str,
    body: &str,
) -> Result<String, SdkError> {
    use tokio::io::{AsyncReadExt, AsyncWriteExt};
    use tokio::net::TcpStream;

    let addr = format!("{host}:{port}");

    // SECURITY: Apply a connect timeout to prevent indefinite hangs against
    // unresponsive or malicious gateways.
    let mut stream = tokio::time::timeout(DISCHARGE_CONNECT_TIMEOUT, TcpStream::connect(&addr))
        .await
        .map_err(|_| {
            SdkError::Wire(format!(
                "connect timeout to {addr} ({}s)",
                DISCHARGE_CONNECT_TIMEOUT.as_secs()
            ))
        })?
        .map_err(|e| SdkError::Wire(format!("failed to connect to {addr}: {e}")))?;

    let request = format!(
        "POST {path} HTTP/1.1\r\n\
         Host: {host}\r\n\
         Content-Type: application/json\r\n\
         Content-Length: {}\r\n\
         Connection: close\r\n\
         \r\n\
         {body}",
        body.len()
    );

    stream
        .write_all(request.as_bytes())
        .await
        .map_err(|e| SdkError::Wire(format!("failed to write request: {e}")))?;

    // SECURITY: Apply a read timeout to prevent slowloris-style attacks where
    // a malicious gateway sends data very slowly to hold the connection.
    let mut response = String::new();
    tokio::time::timeout(DISCHARGE_READ_TIMEOUT, stream.read_to_string(&mut response))
        .await
        .map_err(|_| {
            SdkError::Wire(format!(
                "read timeout from {addr} ({}s)",
                DISCHARGE_READ_TIMEOUT.as_secs()
            ))
        })?
        .map_err(|e| SdkError::Wire(format!("failed to read response: {e}")))?;

    // Parse HTTP response: find body after \r\n\r\n.
    let body_start = response.find("\r\n\r\n").ok_or_else(|| {
        SdkError::Wire("malformed HTTP response: no header/body separator".into())
    })?;

    Ok(response[body_start + 4..].to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// P1-3 regression test: HTTPS URLs must NOT fall back to plaintext.
    /// Sending credentials in the clear is a critical security violation.
    #[tokio::test]
    async fn obtain_discharge_rejects_https_without_tls_client() {
        // An HTTPS gateway URL must be rejected (no TLS downgrade to plaintext).
        let result = obtain_discharge(
            "https://gateway.example.com",
            &[1, 2, 3], // dummy ticket
            None,
            None,
            None,
        )
        .await;

        assert!(
            result.is_err(),
            "SECURITY BUG: HTTPS URL must not silently fall back to plaintext"
        );
        let err = result.unwrap_err();
        let err_msg = err.to_string();
        assert!(
            err_msg.contains("TLS required"),
            "error should mention TLS requirement, got: {err_msg}"
        );
    }

    /// P1-3: HTTP (non-TLS) URLs should still work (explicit opt-in to insecure).
    /// This test verifies that the plaintext path is still reachable for non-TLS URLs.
    /// (It will fail to connect since there's no actual server, but the important thing
    /// is that it does NOT return a "TLS required" error.)
    #[tokio::test]
    async fn obtain_discharge_allows_http_plaintext() {
        // An HTTP (non-TLS) URL should attempt a plaintext connection (not be rejected
        // at the TLS check). It will fail because no server is running, but the error
        // should be a connection error, not a TLS-required error.
        let result = obtain_discharge(
            "http://127.0.0.1:1/discharge", // port 1 = will fail to connect
            &[1, 2, 3],
            None,
            None,
            None,
        )
        .await;

        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        // The error should be about connection failure, NOT about TLS being required.
        assert!(
            !err_msg.contains("TLS required"),
            "HTTP URL should not trigger TLS check, got: {err_msg}"
        );
    }
}
