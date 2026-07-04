//! THE BRAIN-DRIVEN ACP PEER — the real confined agent, over the wire.
//!
//! [`HermesAgentPeer`] is the [`crate::AcpPeer`] that the prior scripted
//! [`crate::MockHermesPeer`] is replaced by. Where the mock replays a FIXED
//! `Vec<`[`crate::ScriptedCall`]`>`, this peer runs an [`LlmBrain`]'s CLOSED LOOP:
//! on `session/prompt` it asks the brain for its first step; each
//! [`BrainStep::CallTool`] becomes a streamed `tool_call` + a
//! `session/request_permission` REQUEST; the deos client answers it through the
//! [`crate::HermesGateway`] (a cap-gated, metered, receipted dregg turn or an
//! in-band refusal); the peer folds that verdict back into the conversation and
//! asks the brain for the NEXT step — until the brain returns
//! [`BrainStep::Finish`].
//!
//! It speaks the SAME `acp_adapter` message shapes the mock does, so the
//! UNCHANGED [`crate::AcpClient`] drives a real agent exactly as it drove the
//! script: the only difference is that the tool-calls now come from a brain that
//! reacts to the gate, not from a pre-written list. Run it in-process for the
//! hermetic tests, or (the next slice) inside the [`crate::confined`] jail in
//! place of `stand_in_acp_peer`.

use std::collections::VecDeque;

use serde_json::{Value, json};

use crate::acp_client::{AcpError, AcpPeer, RpcMessage};
use crate::brain::{AgentConvo, BrainStep, LlmBrain};

/// Where in an ACP session this peer is.
enum Phase {
    /// Awaiting `initialize`.
    Init,
    /// Awaiting `session/new`.
    NewSession,
    /// Awaiting `session/prompt`, then running the brain loop.
    Prompt,
    /// The brain finished; the prompt response is owed.
    Done,
}

/// A faithful Hermes ACP peer DRIVEN BY A BRAIN. Implements [`AcpPeer`], so
/// `AcpClient::run_prompt` drives a real confined agent over it.
pub struct HermesAgentPeer<B: LlmBrain> {
    phase: Phase,
    session_id: String,
    brain: B,
    /// The running conversation the brain decides over (prompt + verdicts seen).
    convo: AgentConvo,
    /// Frames queued for the client's next `recv`.
    outbox: VecDeque<RpcMessage>,
    /// The id of the in-flight `session/request_permission` (matched on the
    /// client's response).
    pending_permission_id: Option<i64>,
    /// The tool-call awaiting a verdict (name + args), so the verdict can be
    /// folded into the conversation under the right tool.
    pending_tool: Option<(String, Value)>,
    /// The client's `session/prompt` request id, answered with the final
    /// `PromptResponse` once the brain finishes.
    prompt_response_id: Option<Value>,
    next_id: i64,
    tool_call_seq: usize,
    /// The `mcpServers` the client registered on `session/new` (captured for a
    /// test to assert the deep-integration wire, mirroring the mock).
    registered_mcp_servers: Value,
    /// Every gate verdict the agent observed this turn (for inspection / tests).
    pub verdicts_seen: Vec<crate::brain::ToolObservation>,
}

impl<B: LlmBrain> HermesAgentPeer<B> {
    /// A brain-driven peer for a session. The brain decides every tool-call; the
    /// prompt + cwd are captured from the client's `session/prompt` /
    /// `session/new`.
    pub fn new(session_id: &str, brain: B) -> HermesAgentPeer<B> {
        HermesAgentPeer {
            phase: Phase::Init,
            session_id: session_id.into(),
            brain,
            convo: AgentConvo::default(),
            outbox: VecDeque::new(),
            pending_permission_id: None,
            pending_tool: None,
            prompt_response_id: None,
            next_id: 1000,
            tool_call_seq: 0,
            registered_mcp_servers: Value::Null,
            verdicts_seen: Vec::new(),
        }
    }

    /// The brain (post-run) — e.g. to inspect a [`crate::brain::HttpLlm`]'s
    /// `key_reached_provider` witness, or the on-box brain's held keys.
    pub fn brain(&self) -> &B {
        &self.brain
    }

    /// The conversation (post-run): the prompt + the verdict on each tool-call the
    /// brain made. The agent's whole reach, for a test to scan.
    pub fn convo(&self) -> &AgentConvo {
        &self.convo
    }

    /// The `mcpServers` the client registered on `session/new` (the model's tool
    /// source) — `Null` until a `session/new` arrived.
    pub fn registered_mcp_servers(&self) -> &Value {
        &self.registered_mcp_servers
    }

    /// Whether the brain finished the turn AND its final `PromptResponse` has been
    /// handed out over [`AcpPeer::recv`] — i.e. there is nothing more this peer will
    /// ever emit for this prompt. A socket-serve loop
    /// ([`crate::confined::serve_acp_peer_over_endpoint`]) uses this to return the
    /// instant a confined brain's turn completes, instead of blocking for an EOF
    /// that the driving client (still holding its end) will not send.
    pub fn turn_complete(&self) -> bool {
        matches!(self.phase, Phase::Done) && self.prompt_response_id.is_none()
    }

    fn alloc_id(&mut self) -> i64 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    /// Ask the brain for its next step and queue the matching wire frames: a
    /// tool-call's `session/update` + `session/request_permission`, or the final
    /// agent message + transition to `Done`.
    fn drive_brain_step(&mut self) {
        match self.brain.next_step(&self.convo) {
            BrainStep::CallTool { name, arguments } => {
                self.tool_call_seq += 1;
                let tool_call_id = format!("tc-{}", self.tool_call_seq);
                let kind = crate::acp::ToolKind::of_tool(&name);
                let kind_str = acp_kind_str(kind);

                // (a) the streamed tool_call lifecycle event.
                self.outbox.push_back(RpcMessage::notification(
                    "session/update",
                    json!({
                        "sessionId": self.session_id,
                        "update": {
                            "sessionUpdate": "tool_call",
                            "toolCallId": tool_call_id,
                            "toolName": name,
                            "kind": kind_str,
                            "status": "pending",
                            "rawInput": arguments,
                        }
                    }),
                ));

                // (b) the request_permission REQUEST the deos client answers.
                let perm_id = self.alloc_id();
                self.pending_permission_id = Some(perm_id);
                self.pending_tool = Some((name.clone(), arguments.clone()));
                self.outbox.push_back(RpcMessage::request(
                    perm_id,
                    "session/request_permission",
                    json!({
                        "sessionId": self.session_id,
                        "toolCall": {
                            "toolCallId": tool_call_id,
                            "toolName": name,
                            "kind": kind_str,
                            "status": "pending",
                            "rawInput": arguments,
                        },
                        "options": [
                            { "optionId": "allow_once", "kind": "allow_once", "name": "Allow once" },
                            { "optionId": "deny", "kind": "reject_once", "name": "Deny" }
                        ]
                    }),
                ));
            }
            BrainStep::Finish { text } => {
                // The brain's final message + the turn ends.
                self.outbox.push_back(RpcMessage::notification(
                    "session/update",
                    json!({
                        "sessionId": self.session_id,
                        "update": {
                            "sessionUpdate": "agent_message_chunk",
                            "content": { "type": "text", "text": text }
                        }
                    }),
                ));
                self.phase = Phase::Done;
            }
        }
    }

    /// Fold the client's permission verdict into the conversation, then ask the
    /// brain for its next step (which may call another tool or finish).
    fn on_permission_outcome(&mut self, outcome: &Value) {
        let option_id = outcome
            .get("optionId")
            .and_then(|v| v.as_str())
            .unwrap_or("deny");
        let allowed = option_id == "allow_once" || option_id == "allow_always";
        // The deos extension carries the receipt / refusal reason — the tool RESULT
        // the brain reasons over.
        let detail = if allowed {
            outcome
                .get("deosReceipt")
                .and_then(|v| v.as_str())
                .unwrap_or("(receipt)")
                .to_string()
        } else {
            outcome
                .get("deosRefusal")
                .and_then(|v| v.as_str())
                .unwrap_or("(refused)")
                .to_string()
        };

        let tool_call_id = format!("tc-{}", self.tool_call_seq);
        // Post-decision status echo (the editor would see completed/failed).
        self.outbox.push_back(RpcMessage::notification(
            "session/update",
            json!({
                "sessionId": self.session_id,
                "update": {
                    "sessionUpdate": "tool_call_update",
                    "toolCallId": tool_call_id,
                    "status": if allowed { "completed" } else { "failed" },
                }
            }),
        ));

        if let Some((name, args)) = self.pending_tool.take() {
            self.convo.observe(&name, args.clone(), allowed, &detail);
            self.verdicts_seen.push(crate::brain::ToolObservation {
                tool: name,
                arguments: args,
                allowed,
                detail,
            });
        }
        self.pending_permission_id = None;

        // The brain decides what to do with that result.
        self.drive_brain_step();
    }
}

impl<B: LlmBrain> AcpPeer for HermesAgentPeer<B> {
    fn send(&mut self, msg: &RpcMessage) -> Result<(), AcpError> {
        // A response to our pending permission request? Fold the verdict + step.
        if (msg.result.is_some() || msg.error.is_some())
            && msg.id == self.pending_permission_id.map(|i| json!(i))
        {
            let result = msg.result.clone().unwrap_or(Value::Null);
            let outcome = result.get("outcome").cloned().unwrap_or(Value::Null);
            self.on_permission_outcome(&outcome);
            return Ok(());
        }

        // Otherwise a client→peer REQUEST (initialize / session/new / set_model /
        // session/prompt).
        let id = msg.id.clone().unwrap_or(Value::Null);
        let method = msg.method.as_deref().unwrap_or("");
        match (&self.phase, method) {
            (Phase::Init, "initialize") => {
                self.outbox.push_back(RpcMessage::response(
                    id,
                    json!({
                        "protocolVersion": crate::acp_client::ACP_PROTOCOL_VERSION,
                        "agentInfo": { "name": "hermes-agent", "version": "brain-driven" },
                        "agentCapabilities": { "loadSession": true },
                        "authMethods": []
                    }),
                ));
                self.phase = Phase::NewSession;
                Ok(())
            }
            (Phase::NewSession, "session/new") => {
                let params = msg.params.clone().unwrap_or(Value::Null);
                self.registered_mcp_servers =
                    params.get("mcpServers").cloned().unwrap_or(Value::Null);
                self.convo.cwd = params
                    .get("cwd")
                    .and_then(|v| v.as_str())
                    .unwrap_or("")
                    .to_string();
                self.outbox.push_back(RpcMessage::response(
                    id,
                    json!({ "sessionId": self.session_id, "models": [], "modes": [] }),
                ));
                self.phase = Phase::Prompt;
                Ok(())
            }
            (_, "session/set_model") => {
                // The ACP unstable model-selection method — benign no-op result
                // (mirrors the live adapter + the mock).
                self.outbox.push_back(RpcMessage::response(id, json!({})));
                Ok(())
            }
            (Phase::Prompt, "session/prompt") => {
                // Capture the prompt, open the brain's reply, and run the first
                // brain step.
                let prompt = msg
                    .params
                    .as_ref()
                    .and_then(|p| p.get("prompt"))
                    .and_then(|p| p.as_array())
                    .and_then(|blocks| blocks.first())
                    .and_then(|b| b.get("text"))
                    .and_then(|t| t.as_str())
                    .unwrap_or("")
                    .to_string();
                self.convo.prompt = prompt;
                self.prompt_response_id = Some(id);

                // An opening "thinking" chunk so the chat pane shows the agent is
                // working before the first tool-call lands.
                self.outbox.push_back(RpcMessage::notification(
                    "session/update",
                    json!({
                        "sessionId": self.session_id,
                        "update": {
                            "sessionUpdate": "agent_message_chunk",
                            "content": { "type": "text", "text": "thinking… " }
                        }
                    }),
                ));
                self.drive_brain_step();
                Ok(())
            }
            _ => {
                self.outbox.push_back(RpcMessage::response(
                    id,
                    json!({ "error": format!("agent peer: unexpected {method} in this phase") }),
                ));
                Ok(())
            }
        }
    }

    fn recv(&mut self) -> Result<RpcMessage, AcpError> {
        if let Some(msg) = self.outbox.pop_front() {
            return Ok(msg);
        }
        // The brain finished and the prompt is outstanding → send the response.
        if matches!(self.phase, Phase::Done)
            && let Some(id) = self.prompt_response_id.take()
        {
            return Ok(RpcMessage::response(
                id,
                json!({ "stopReason": "end_turn" }),
            ));
        }
        Err(AcpError::Closed)
    }
}

/// The ACP `kind` string for a [`crate::acp::ToolKind`] (the wire form Hermes's
/// `tools.py::get_tool_kind` emits).
fn acp_kind_str(kind: crate::acp::ToolKind) -> &'static str {
    use crate::acp::ToolKind;
    match kind {
        ToolKind::Read => "read",
        ToolKind::Edit => "edit",
        ToolKind::Execute => "execute",
        ToolKind::Fetch => "fetch",
        ToolKind::Search => "search",
        ToolKind::Other => "other",
    }
}
