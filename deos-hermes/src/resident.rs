//! THE RESIDENT'S BRAIN SELECTOR — the weld from the scripted stand-in to a REAL
//! closed-loop brain, offline-hermetic by default, BYO-key when the operator asks.
//!
//! The interactive dock ([`crate::cockpit_surface::HermesSession`]) and the
//! desktop hireling ([starbridge-v2's `resident_agent`]) both need to decide,
//! ONCE, which brain drives the confined ACP loop. Historically the dock built a
//! keyword-script [`crate::MockHermesPeer`] — a fake brain. Everything downstream
//! of that (the ACP wire, the [`crate::HermesGateway`] gate, the receipts) was
//! already real; only the decision-maker was stood in. This module retires the
//! stand-in.
//!
//! ## What it picks
//!
//! [`resident_brain_from_env`] reads the operator's environment and returns a
//! [`ResidentBrain`] — a single concrete type the [`crate::HermesAgentPeer`] can
//! be generic over — resolved in this order:
//!
//!   1. `ANTHROPIC_API_KEY` set → [`ResidentBrain::Anthropic`]: a live
//!      [`HttpLlm`] over the Anthropic Messages API (`/v1/messages`), the BYO key
//!      confined to the provider call. Model id from `ANTHROPIC_MODEL` /
//!      `HERMES_ACP_MODEL`, default [`DEFAULT_ANTHROPIC_MODEL`].
//!   2. `HERMES_API_KEY` set → [`ResidentBrain::OpenAiCompat`]: a live [`HttpLlm`]
//!      over any OpenAI-compatible chat/completions endpoint (`HERMES_ENDPOINT`,
//!      default a local proxy), reusing the crate's proven
//!      [`crate::OpenAICompatCaller`] translation.
//!   3. otherwise → [`ResidentBrain::OnBox`]: the deterministic reactive
//!      [`crate::LocalBrain`]. It needs NO key and NO network — the HERMETIC
//!      default, so `cargo test` / an offline `examples/resident` run drives a
//!      REAL decide→gate→observe loop with zero external state.
//!
//! The live paths POST over the operator's own `curl` (a "BYO HTTP stack" seam),
//! so this crate adds NO new dependency. The BYO key reaches ONLY the `curl`
//! invocation's auth header — never a tool-call, a receipt, the World the agent
//! drives, or the ACP wire the agent's reach travels (the brain-pocket invariant,
//! [`crate::LlmKeys`]). Its `Debug` is redacted by construction.
//!
//! HONEST NOTE ON THE `curl` SEAM: the key crosses `curl`'s argv (visible in a
//! local `ps` on the operator's own box), not the request body — a deliberate,
//! documented tradeoff to keep this dependency-free. A hardened deployment injects
//! an in-process [`crate::LlmHttpCaller`] (a real HTTP client) here instead.

use std::process::Command;

use serde_json::{Value, json};

use crate::brain::{
    AgentConvo, BrainStep, HttpLlm, LlmBrain, LlmHttpCaller, LlmKeys, LocalBrain,
    OpenAICompatCaller,
};

/// The default Anthropic model id the live BYO-key path drives (Anthropic's most
/// capable widely-released model). Overridable via `ANTHROPIC_MODEL` /
/// `HERMES_ACP_MODEL`.
pub const DEFAULT_ANTHROPIC_MODEL: &str = "claude-opus-4-8";

/// The Anthropic Messages API version header the caller stamps.
const ANTHROPIC_VERSION: &str = "2023-06-01";

/// The concrete `curl`-backed OpenAI-compatible caller type (a `fn`-pointer post
/// seam — the simplest impl of the [`crate::OpenAICompatCaller`] transport bound).
type OpenAiCurl = OpenAICompatCaller<fn(&str, &str, &Value) -> Result<Value, String>>;

/// THE RESIDENT'S BRAIN — one concrete enum the confined peer is generic over, so
/// the caller decides on-box vs. BYO-key ONCE and the rest of the rail is
/// unchanged. Implements [`LlmBrain`] by dispatch.
pub enum ResidentBrain {
    /// The deterministic reactive on-box brain — no key, no network (the default).
    OnBox(LocalBrain),
    /// A live Anthropic Messages-API brain (BYO `ANTHROPIC_API_KEY`).
    Anthropic(HttpLlm<AnthropicCaller>),
    /// A live OpenAI-compatible brain (BYO `HERMES_API_KEY` + `HERMES_ENDPOINT`).
    OpenAiCompat(HttpLlm<OpenAiCurl>),
}

impl ResidentBrain {
    /// A one-line, secret-free label for the room / wizard to render ("on-box",
    /// the provider name) — the credential never appears, only the provider.
    pub fn describe(&self) -> String {
        match self {
            ResidentBrain::OnBox(_) => "on-box LocalBrain (no key)".to_string(),
            ResidentBrain::Anthropic(_) => "Anthropic (BYO key)".to_string(),
            ResidentBrain::OpenAiCompat(_) => "OpenAI-compatible (BYO key)".to_string(),
        }
    }
}

impl Default for ResidentBrain {
    fn default() -> Self {
        ResidentBrain::OnBox(LocalBrain::new())
    }
}

impl LlmBrain for ResidentBrain {
    fn next_step(&mut self, convo: &AgentConvo) -> BrainStep {
        match self {
            ResidentBrain::OnBox(b) => b.next_step(convo),
            ResidentBrain::Anthropic(b) => b.next_step(convo),
            ResidentBrain::OpenAiCompat(b) => b.next_step(convo),
        }
    }
}

/// Resolve the resident's brain from the operator environment (see the module
/// doc for the precedence). Always succeeds: the on-box brain is the fail-safe
/// tail, so a keyless / offline environment still gets a REAL closed loop.
pub fn resident_brain_from_env() -> ResidentBrain {
    if let Some(keys) = LlmKeys::from_env("anthropic", "ANTHROPIC_API_KEY") {
        let model = std::env::var("ANTHROPIC_MODEL")
            .or_else(|_| std::env::var("HERMES_ACP_MODEL"))
            .unwrap_or_else(|_| DEFAULT_ANTHROPIC_MODEL.to_string());
        let endpoint = std::env::var("ANTHROPIC_ENDPOINT")
            .unwrap_or_else(|_| "https://api.anthropic.com/v1/messages".to_string());
        return ResidentBrain::Anthropic(HttpLlm::new(
            keys,
            &endpoint,
            &model,
            AnthropicCaller::new(),
        ));
    }
    if let Some(keys) = LlmKeys::from_env("hermes", "HERMES_API_KEY") {
        let model = std::env::var("HERMES_ACP_MODEL").unwrap_or_else(|_| "gpt-4o-mini".to_string());
        let endpoint = std::env::var("HERMES_ENDPOINT")
            .unwrap_or_else(|_| "http://localhost:11434/v1/chat/completions".to_string());
        let post: fn(&str, &str, &Value) -> Result<Value, String> = openai_curl_post;
        return ResidentBrain::OpenAiCompat(HttpLlm::new(
            keys,
            &endpoint,
            &model,
            OpenAICompatCaller::new(post),
        ));
    }
    ResidentBrain::default()
}

// ─────────────────────── the Anthropic Messages-API caller ───────────────────

/// A [`LlmHttpCaller`] for the Anthropic Messages API (`/v1/messages`), over the
/// operator's `curl`. [`HttpLlm`] emits a provider-neutral Messages-shaped request
/// and parses a `content`-block response — the Anthropic RESPONSE is already that
/// shape (`content: [{type:"tool_use"|"text", …}]`), so this caller only maps the
/// REQUEST into Anthropic's exact body (adding `max_tokens`, folding tool results
/// into `tool_result` blocks, giving tools an `input_schema`) and passes the
/// response straight back to [`crate::brain`]'s parser. The BYO key rides the
/// `x-api-key` header of the `curl` call and NOWHERE else.
pub struct AnthropicCaller {
    /// Tokens to request per turn. A small ceiling suffices for a tool-choosing
    /// brain (it emits a `tool_use` block, not prose).
    max_tokens: u64,
}

impl Default for AnthropicCaller {
    fn default() -> Self {
        AnthropicCaller::new()
    }
}

impl AnthropicCaller {
    /// A fresh caller with a modest per-turn token ceiling.
    pub fn new() -> AnthropicCaller {
        AnthropicCaller { max_tokens: 1024 }
    }

    /// Override the per-turn `max_tokens`.
    pub fn with_max_tokens(mut self, max_tokens: u64) -> AnthropicCaller {
        self.max_tokens = max_tokens;
        self
    }
}

impl LlmHttpCaller for AnthropicCaller {
    fn complete(
        &mut self,
        endpoint: &str,
        api_key: &str,
        request: &Value,
    ) -> Result<Value, String> {
        let body = messages_to_anthropic(request, self.max_tokens);
        // The key reaches ONLY here — the `x-api-key` header — never the body.
        curl_post(
            endpoint,
            &[
                ("x-api-key", api_key),
                ("anthropic-version", ANTHROPIC_VERSION),
            ],
            &body,
        )
    }
}

/// Translate [`HttpLlm`]'s provider-neutral Messages request into an Anthropic
/// `/v1/messages` body: `system` stays a top-level string; each Messages
/// `assistant`/`tool_use` becomes an assistant turn carrying a `tool_use` block
/// (a synthesized `tc-{n}` id) and each following `tool` message becomes a
/// `user` turn carrying the matching `tool_result` block; the `{name,description}`
/// tools gain an empty-object `input_schema`; `max_tokens` is added.
fn messages_to_anthropic(request: &Value, max_tokens: u64) -> Value {
    let mut messages = Vec::new();
    let mut tc_seq = 0u64;
    if let Some(src) = request.get("messages").and_then(|m| m.as_array()) {
        for msg in src {
            let role = msg.get("role").and_then(|r| r.as_str()).unwrap_or("");
            match role {
                "user" => messages.push(msg.clone()),
                "assistant" => {
                    let tool_use = msg.get("content").and_then(|c| c.as_array()).and_then(|a| {
                        a.iter()
                            .find(|b| b.get("type").and_then(|t| t.as_str()) == Some("tool_use"))
                    });
                    if let Some(tu) = tool_use {
                        tc_seq += 1;
                        let name = tu.get("name").and_then(|n| n.as_str()).unwrap_or("");
                        let input = tu.get("input").cloned().unwrap_or(Value::Null);
                        messages.push(json!({
                            "role": "assistant",
                            "content": [{
                                "type": "tool_use",
                                "id": format!("tc-{tc_seq}"),
                                "name": name,
                                "input": input,
                            }]
                        }));
                    } else {
                        messages.push(msg.clone());
                    }
                }
                "tool" => {
                    // A Messages `tool` result → Anthropic's user-turn tool_result,
                    // id-linked to the most recent tool_use.
                    let content = msg.get("content").and_then(|c| c.as_str()).unwrap_or("");
                    messages.push(json!({
                        "role": "user",
                        "content": [{
                            "type": "tool_result",
                            "tool_use_id": format!("tc-{tc_seq}"),
                            "content": content,
                        }]
                    }));
                }
                _ => messages.push(msg.clone()),
            }
        }
    }
    let tools = request
        .get("tools")
        .and_then(|t| t.as_array())
        .map(|specs| {
            specs
                .iter()
                .map(|s| {
                    json!({
                        "name": s.get("name").and_then(|n| n.as_str()).unwrap_or(""),
                        "description": s.get("description").and_then(|d| d.as_str()).unwrap_or(""),
                        "input_schema": { "type": "object", "properties": {} }
                    })
                })
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    let mut body = json!({
        "model": request.get("model").cloned().unwrap_or(Value::Null),
        "max_tokens": max_tokens,
        "messages": messages,
        "tools": tools,
    });
    if let Some(system) = request.get("system").and_then(|s| s.as_str()) {
        body["system"] = Value::String(system.to_string());
    }
    body
}

// ──────────────────────────── the shared curl seam ───────────────────────────

/// POST `body` to `endpoint` with the given auth headers over the operator's
/// `curl`, returning the parsed JSON response. The body rides `curl`'s stdin
/// (`--data-binary @-`), so a large request never crosses argv; the auth header
/// values DO cross argv (see the module-doc honesty note).
fn curl_post(endpoint: &str, auth_headers: &[(&str, &str)], body: &Value) -> Result<Value, String> {
    use std::io::Write;
    use std::process::Stdio;

    let payload = serde_json::to_vec(body).map_err(|e| format!("encode request: {e}"))?;
    let mut cmd = Command::new("curl");
    cmd.arg("-sS")
        .arg("-X")
        .arg("POST")
        .arg(endpoint)
        .arg("-H")
        .arg("content-type: application/json");
    for (k, v) in auth_headers {
        cmd.arg("-H").arg(format!("{k}: {v}"));
    }
    cmd.arg("--data-binary")
        .arg("@-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());

    let mut child = cmd.spawn().map_err(|e| format!("spawn curl: {e}"))?;
    child
        .stdin
        .take()
        .ok_or_else(|| "curl stdin unavailable".to_string())?
        .write_all(&payload)
        .map_err(|e| format!("write request body: {e}"))?;
    let out = child
        .wait_with_output()
        .map_err(|e| format!("await curl: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "curl POST failed: {}",
            String::from_utf8_lossy(&out.stderr).trim()
        ));
    }
    serde_json::from_slice(&out.stdout).map_err(|e| format!("parse provider response: {e}"))
}

/// The `fn`-pointer post seam for the OpenAI-compatible path: the BYO key rides
/// the `Authorization: Bearer` header of a `curl` POST; the body (already
/// OpenAI-shaped by [`crate::OpenAICompatCaller`]) rides stdin.
fn openai_curl_post(endpoint: &str, api_key: &str, body: &Value) -> Result<Value, String> {
    let bearer = format!("Bearer {api_key}");
    curl_post(endpoint, &[("authorization", &bearer)], body)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The generic Messages request maps to a valid Anthropic body: `max_tokens`
    /// is added, the tool gains an `input_schema`, and the key is NOT in the body
    /// (it rides the header, at the caller). A tool result folds to a `user`-turn
    /// `tool_result` id-linked to the preceding `tool_use` — the multi-step shape
    /// the confined loop needs. Pure translation, no network.
    #[test]
    fn messages_to_anthropic_shapes_a_valid_body() {
        // The exact shape `HttpLlm::request_body` emits after one refused write:
        let request = json!({
            "model": "claude-opus-4-8",
            "system": "You are a confined deos agent.",
            "messages": [
                { "role": "user", "content": "write the file" },
                { "role": "assistant", "content": [
                    { "type": "tool_use", "name": "write_file", "input": { "path": "x" } }
                ]},
                { "role": "tool", "tool": "write_file",
                  "content": "refused by confinement: denied by mandate" }
            ],
            "tools": [{ "name": "web_search", "description": "Search the web." }]
        });

        let body = messages_to_anthropic(&request, 512);

        assert_eq!(body["max_tokens"], 512, "the per-turn ceiling was added");
        assert_eq!(
            body["model"], "claude-opus-4-8",
            "the model id carried through"
        );
        assert_eq!(body["system"], "You are a confined deos agent.");
        assert_eq!(
            body["tools"][0]["input_schema"]["type"], "object",
            "tools gained an Anthropic input_schema"
        );

        let msgs = body["messages"].as_array().expect("messages array");
        // user, assistant(tool_use), user(tool_result)
        assert_eq!(msgs.len(), 3);
        assert_eq!(msgs[1]["content"][0]["type"], "tool_use");
        assert_eq!(msgs[1]["content"][0]["id"], "tc-1", "synthesized tool id");
        assert_eq!(msgs[2]["role"], "user", "a tool result is a user turn");
        assert_eq!(msgs[2]["content"][0]["type"], "tool_result");
        assert_eq!(
            msgs[2]["content"][0]["tool_use_id"], "tc-1",
            "the tool_result is id-linked to its tool_use"
        );

        // The secret never enters the translated body (it rides the header only).
        assert!(
            !body.to_string().contains("x-api-key"),
            "no auth material in the request body"
        );
    }

    /// With no keys in the environment-shaped inputs, the resolver's fail-safe
    /// tail is the on-box brain — a REAL closed loop that needs no network. (We
    /// assert the type of the default directly so the test is env-independent.)
    #[test]
    fn default_resident_brain_is_on_box() {
        let brain = ResidentBrain::default();
        assert!(matches!(brain, ResidentBrain::OnBox(_)));
        assert_eq!(brain.describe(), "on-box LocalBrain (no key)");
    }
}
