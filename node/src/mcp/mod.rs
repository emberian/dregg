//! MCP (Model Context Protocol) server for the dregg node.
//!
//! Exposes node capabilities as MCP tools over JSON-RPC 2.0 (stdio transport).
//! AI assistants (Claude, GPT, etc.) can discover and invoke tools to interact
//! with the dregg federation: authorize actions, submit turns, manage capabilities,
//! post intents, and more.
//!
//! ## Transport
//!
//! - **Stdio**: `dregg-node mcp` reads JSON-RPC from stdin and writes to stdout.
//!   This is the standard MCP transport for local tool-calling.
//!
//! ## Protocol
//!
//! Implements the MCP subset needed for tool serving:
//! - `initialize` — capability negotiation
//! - `notifications/initialized` — client readiness signal (no response)
//! - `tools/list` — enumerate available tools
//! - `tools/call` — invoke a tool

use serde::{Deserialize, Serialize};
use serde_json::Value;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tracing::{error, info};

use dregg_sdk::{Attenuation, CellId};
use dregg_turn::{CallForest, Turn};
use dregg_types::PublicKey;

use dregg_app_framework::AppCipherclerk;
use dregg_sdk::AgentCipherclerk;
use starbridge_governed_namespace::build_register_service_action as sb_build_register_service_action;
use starbridge_identity::{
    Credential as SbCredential, CredentialAttributes as SbCredentialAttributes,
    CredentialSchema as SbCredentialSchema, IssuerKeys as SbIssuerKeys,
    build_issue_credential_action as sb_build_issue_credential_action,
    employment_schema as sb_employment_schema, gov_id_schema as sb_gov_id_schema,
    issue as sb_issue, kyc_schema as sb_kyc_schema,
};
use starbridge_nameservice::build_register_with_credential_action as sb_build_register_with_credential_action;
use starbridge_subscription::{
    BountyState as SbBountyState, build_bounty_state_publish_action as sb_build_bounty_publish,
};

use crate::state::NodeState;

// Re-import x25519 and chacha for seal/unseal operations.

/// **THE DECISION POINTS THE VERIFICATION-CLAIM CONTROL NEEDS, AND NOTHING ELSE.**
///
/// `node/tests/mcp_verification_claims_are_earned.rs` is the permanent control for one
/// rule: a tool may only report a verification it actually ran. Measured 2026-07-30,
/// `dregg_compress_history` reported `"verification": "valid"` after verifying a fold
/// against a fingerprint recomputed from that same fold — the VK pin comparing a value
/// with itself, unable to fail.
///
/// Keeping the rule true needs the two decision points reachable from an integration
/// test WITHOUT a node, a ledger, or an hour of recursive proving — otherwise the control
/// is a heavyweight test that gets disabled, and this campaign has watched ten such
/// checks go silently unpointed. These are pure functions over JSON: no state, no
/// authority, nothing a caller could drive.
pub mod test_hooks {
    use serde_json::Value;

    /// See [`super::handlers_verify`]: the required caller-supplied VK anchor. `Err` when
    /// absent or malformed — there is no default and no self-mint.
    pub fn required_config_anchor(params: &Value) -> Result<[u8; 32], String> {
        super::handlers_verify::required_config_anchor(params)
    }

    /// See [`super::handlers_verify`]: the ONE place `"verification": "valid"` is written,
    /// and only when an anchored verify held.
    pub fn compress_history_report(
        fold: serde_json::Map<String, Value>,
        cell_id_hex: &str,
        anchored_verify_held: bool,
    ) -> Value {
        super::handlers_verify::compress_history_report(fold, cell_id_hex, anchored_verify_held)
    }

    /// The tool catalogue an agent plans from, as JSON. A description that outruns its
    /// handler is the same defect one layer out, so the control reads the served list.
    pub fn tool_catalogue() -> Value {
        serde_json::to_value(super::tools_def::tool_definitions())
            .expect("the tool catalogue serializes")
    }
}

mod dispatch;
mod handlers_act;
mod handlers_apps;
mod handlers_delegate;
/// The ENCRYPTED CALL AUCTION tools (`crate::dark_clearing_service` over MCP).
mod handlers_market;
mod handlers_orient;
mod handlers_privacy;
mod handlers_verify;
mod proof;
mod protocol;
/// Every MCP tool that commits a turn stamps its own `previous_receipt_hash`.
/// This drives the reachable ones through `dispatch_tool` after a foreign agent
/// has committed — the state a faucet grant leaves behind.
#[cfg(test)]
mod receipt_head_e2e;
/// Does a REFUSED MCP turn still charge? `execute`'s PHASE 1 is unjournaled, so
/// the caller owns the undo — and these eleven were the last callers that did
/// not perform it. Drives the refusal live and compares live RAM against the
/// durable image the node rebuilds at boot.
#[cfg(test)]
mod refused_turn_is_free_e2e;
mod tools_def;

// Re-import every submodule namespace so the shared helpers below, the
// `tests` module, and each sibling submodule (via its own `use super::*`)
// all see the full `mcp` surface — a pure-module-move convenience.
use dispatch::*;
use handlers_act::*;
use handlers_apps::*;
use handlers_delegate::*;
use handlers_market::*;
use handlers_orient::*;
use handlers_privacy::*;
use handlers_verify::*;
use proof::*;
use protocol::*;
use tools_def::*;

pub use protocol::run_stdio;

// =============================================================================
// Shared low-level helpers (used across every tool group).
// =============================================================================

/// Common helper: read the agent's own cell id from state. The caller
/// holds the lock; we just compute the derivation.
fn agent_cell_of(cclerk: &AgentCipherclerk) -> CellId {
    dregg_cell::CellId::derive_raw(&cclerk.public_key().0, &[0u8; 32])
}

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn hex_decode(s: &str) -> Result<[u8; 32], ()> {
    if s.len() != 64 {
        return Err(());
    }
    let mut out = [0u8; 32];
    for (i, chunk) in s.as_bytes().chunks(2).enumerate() {
        let high = nibble(chunk[0]).ok_or(())?;
        let low = nibble(chunk[1]).ok_or(())?;
        out[i] = (high << 4) | low;
    }
    Ok(out)
}

/// Decode a variable-length hex string into bytes.
fn hex_decode_var(s: &str) -> Result<Vec<u8>, ()> {
    if !s.len().is_multiple_of(2) {
        return Err(());
    }
    let mut out = Vec::with_capacity(s.len() / 2);
    for chunk in s.as_bytes().chunks(2) {
        let high = nibble(chunk[0]).ok_or(())?;
        let low = nibble(chunk[1]).ok_or(())?;
        out.push((high << 4) | low);
    }
    Ok(out)
}

fn nibble(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        b'A'..=b'F' => Some(b - b'A' + 10),
        _ => None,
    }
}

// =============================================================================
// THE ONE MCP APPLICATION GATE
// =============================================================================

/// Execute a turn against the LIVE node ledger under a restore point, keeping
/// the mutation only if it committed. Every mutating MCP tool goes through this
/// or [`mcp_execute_via_producer`]; none of them calls `executor.execute(&turn,
/// &mut s.ledger)` directly any more.
///
/// ⚑ WHY. `TurnExecutor::execute`'s PHASE 1 (fee debit + nonce tick) is
/// deliberately outside the effect journal, so a `Rejected` return hands the
/// caller a ledger that is ALREADY debited and bumped — undoing it is the
/// CALLER's job, and the callers do not agree. Eleven MCP tools armed no restore
/// point and simply dropped the state guard on their rejection arm, so a refused
/// MCP turn kept the debit and the nonce tick in live node RAM.
///
/// That is not a fee-policy question, which is the framing that kept it alive:
///
///   * The charge reaches NO durable state on any node. `node::mcp` writes no
///     `CommitRecord` (only `blocklace_sync`'s finalized path does) and never
///     calls `checkpoint_ledger` — `NodeState::persist_on_shutdown` is called
///     from `run_node` only, never from `run_mcp`. So the debit survives until
///     this process exits and then vanishes, while a peer that did not restart
///     keeps it, and `canonical_ledger_root` hashes the whole cell. That is an
///     attested-root split, by the argument written out at
///     `blocklace_sync.rs:7571-7586` and `:10229`.
///   * The anti-DoS reading does not rescue it. `run_mcp` force-unlocks the
///     cipherclerk precisely because "MCP stdio mode runs as a single-user CLI —
///     no remote attacker scenario applies" (`lib.rs:2887`), and the cell being
///     debited is the node operator's own. Charging the operator to slow the
///     operator is not a defence.
///
/// So MCP refuses for free, like every other ingress: `execute_finalized_turn`
/// discards its isolated `exec_ledger` candidate on `Rejected`,
/// `stage_signed_turn_admission` (`/turns/submit`) calls
/// `rollback_restore_point()` unconditionally, and `/turns/submit-encrypted`
/// rolls back on its rejection arm.
///
/// ⚠ NAMED RESIDUAL, NOT CLOSED HERE — a COMMITTED MCP turn is still an
/// application no other node performs. It mutates `s.ledger` in RAM and DURABLY
/// appends its receipt (the `set_receipt_persist` sink armed in `state.rs`)
/// while writing no `CommitRecord` and no ledger checkpoint. A restart of the
/// MCP process therefore leaves a durable receipt chain whose head names turns
/// the reconstructed ledger does not reflect. Resolving that is a decision about
/// what the MCP surface IS (an authoritative applier, or an admission-staging
/// client that hands turns to consensus like `/turns/submit` does) and is
/// recorded in `HORIZONLOG.md`, not silently picked here.
pub(super) fn mcp_execute(
    s: &mut crate::state::NodeStateInner,
    executor: &dregg_turn::TurnExecutor,
    turn: &Turn,
) -> dregg_turn::TurnResult {
    arm_mcp_turn(s);
    let result = executor.execute(turn, &mut s.ledger);
    settle_mcp_turn(s, result)
}

/// Open the guarded window EARLY, for a handler that writes to `s.ledger`
/// BEFORE it executes — today only `handlers_apps::run_starbridge_action`, whose
/// two `ensure_cell_in_ledger` stubs would otherwise survive a refusal as
/// RAM-only cells the durable image never holds.
///
/// ⚠ A handler that calls this MUST reach [`mcp_execute`] on every path, or it
/// leaves an armed restore point behind — and `Ledger::begin_restore_point`
/// rolls back an existing one before arming, so the NEXT tool call would undo
/// this one's committed work. Do not put a `return` between this and the
/// execute.
pub(super) fn mcp_begin_turn(s: &mut crate::state::NodeStateInner) {
    arm_mcp_turn(s);
}

/// Idempotent arm: a handler that opened the window early keeps ITS journal
/// (which holds the pre-execution writes), rather than having the gate discard
/// it. Re-arming would `rollback` first and lose exactly those writes.
fn arm_mcp_turn(s: &mut crate::state::NodeStateInner) {
    if !s.ledger.has_restore_point() {
        s.ledger.begin_restore_point();
    }
}

/// [`mcp_execute`] through the ONE producer gate (#171) — the verified Lean
/// executor is authoritative for the covered set and the Rust `TurnExecutor` is
/// the demoted differential reference.
///
/// ⚠ Only `handlers_act::tool_submit_turn` routes here; the other ten sites
/// still execute on a bare Rust `TurnExecutor`, so the "one producer gate" is
/// 1-of-11 on this surface. Closing that is a separate change (the Lean producer
/// has to cover those verbs) and is not what this gate is about.
pub(super) fn mcp_execute_via_producer(
    s: &mut crate::state::NodeStateInner,
    executor: &dregg_turn::TurnExecutor,
    turn: &Turn,
) -> dregg_turn::TurnResult {
    let lean_producer_enabled = s.lean_producer_enabled;
    arm_mcp_turn(s);
    let result = crate::executor_setup::execute_via_producer(
        executor,
        turn,
        &mut s.ledger,
        lean_producer_enabled,
    );
    settle_mcp_turn(s, result)
}

/// The same contract for the ONE mutating MCP path that is not a `Turn`:
/// `handlers_act::tool_fulfill_intent`'s verified settle edge
/// (`dregg_intent::fulfillment::execute_fulfillment_flow_verified`). It writes
/// the payer's post-balance and the recipient's in two separate `update_with`
/// calls and returns `Err` if the second fails — leaving the payer debited and
/// the recipient uncredited in live node RAM, which is the fee wound's shape
/// with value destroyed instead of a fee. The mutation now survives only if the
/// flow reports success.
pub(super) fn mcp_apply_to_ledger<T, E>(
    s: &mut crate::state::NodeStateInner,
    f: impl FnOnce(&mut dregg_cell::Ledger) -> Result<T, E>,
) -> Result<T, E> {
    arm_mcp_turn(s);
    let outcome = f(&mut s.ledger);
    if outcome.is_ok() {
        s.ledger.commit_restore_point();
    } else {
        s.ledger.rollback_restore_point();
    }
    outcome
}

/// Keep the mutation iff the turn committed. The non-`Committed`, non-`Rejected`
/// arms (`ProofPending` &c.) roll back too: they are not applications either, and
/// every MCP caller renders them as a refusal.
fn settle_mcp_turn(
    s: &mut crate::state::NodeStateInner,
    result: dregg_turn::TurnResult,
) -> dregg_turn::TurnResult {
    if result.is_committed() {
        s.ledger.commit_restore_point();
    } else {
        s.ledger.rollback_restore_point();
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Issue #72 regression. Pins the producer-side contract:
    /// `generate_effect_vm_proof` MUST emit `PI[IS_AGENT_CELL] == 1`.
    ///
    /// Background: the verifier's `check_receipt_pi_binding`
    /// (`verifier/src/lib.rs::check_receipt_pi_binding`) requires
    /// `PI[IS_AGENT_CELL] == 1` for the v1 single-proof-per-WR replay
    /// shape, since mcp's path produces a single per-cell proof for the
    /// actor's own state transition (the cell IS the agent here). The
    /// underlying `dregg_circuit::effect_vm::generate_effect_vm_trace`
    /// does not constrain this slot — it is an executor-asserted bundle
    /// tag — so mcp must set it explicitly before proving.
    ///
    /// ⚠ The clause that stood here — "without this, the standalone
    /// `dregg-verifier replay-chain` rejects the chain with 'PI[IS_AGENT_CELL]
    /// = 0 but single-proof replay requires 1'" — is FALSE at HEAD
    /// (2026-07-27; and `replay-chain` itself was DELETED 2026-08-05):
    /// `check_receipt_pi_binding` no longer compares
    /// `IS_AGENT_CELL`. The slot is PI 81 and a real rotated leg publishes
    /// 46-68 felts, so no proof that ships carries the offset at all.
    ///
    /// See also `turn/src/executor/proof_verify.rs::populate_pi` (line
    /// 164) and `demo/two-ai-handoff/silver_helper.rs::cmd_make_recursive_witness`
    /// (line 1275), which set the same slot on their own paths.
    ///
    /// ⚠ STATUS CORRECTION. `try_generate_effect_vm_proof` now returns `Err`
    /// UNCONDITIONALLY — the standalone v1 material is RETIRED — so the Issue-#72
    /// producer contract above has no live producer to pin. This test therefore pins the
    /// RETIREMENT itself: the helper must refuse BY NAME rather than fabricate material.
    /// If someone revives the v1 lane, this goes red and the `PI[IS_AGENT_CELL] == 1`
    /// assertion must be restored with it.
    ///
    /// ⚑ UNGATED + REPAIRED 2026-07-28, and the repair is the finding. This carried
    /// `#[cfg(not(feature = "prover"))]`; `dregg-node`'s `prover` feature was default-on with no
    /// `--no-default-features` consumer anywhere, and the OFF position did not even COMPILE
    /// (`blocklace_sync.rs` names the `exact_fnsp_v3_*` modules that `lib.rs` gated on the
    /// feature). So the one pin guarding the v1 retirement emitted no line in any run that has
    /// ever happened — and when it was finally compiled it FAILED, on `contains("retired")`
    /// against a message that says `is RETIRED`. A CASE MISMATCH. The pin could never have
    /// passed; it was not merely unrun, it was wrong, and nothing could say so.
    ///
    /// The comparison is case-folded, which is the claim the author wrote in the message
    /// ("must name the retirement"). It still goes red if the v1 lane is revived, if the helper
    /// starts returning `Ok`, or if the refusal stops naming why.
    #[test]
    fn standalone_v1_effect_vm_material_is_retired_and_refuses_by_name() {
        let vm_effects = vec![dregg_circuit::effect_vm::Effect::GrantCapability {
            cap_entry: grant_cap_entry_8(1),
            phase_b: None,
        }];
        let err = try_generate_effect_vm_proof(100, 0, &vm_effects).expect_err(
            "the standalone v1 effect-vm lane is retired; if it produces material again, \
             restore the Issue-#72 PI[IS_AGENT_CELL]==1 assertion this test replaced",
        );
        assert!(
            err.to_lowercase().contains("retired"),
            "the refusal must name the retirement, not fail for an incidental reason: {err}"
        );
    }

    /// Issue #72 second pin: confirm the bare trace generator does NOT
    /// populate IS_AGENT_CELL. This documents WHY the explicit assignment
    /// in `generate_effect_vm_proof` is required — if the trace generator
    /// is later changed to populate this slot itself, this test will fail
    /// and the explicit set can be removed.
    #[test]
    fn generate_effect_vm_trace_leaves_is_agent_cell_unset() {
        use dregg_circuit::effect_vm::pi as evm_pi;
        let state = dregg_circuit::effect_vm::CellState::new(100, 0);
        let effects = vec![dregg_circuit::effect_vm::Effect::GrantCapability {
            cap_entry: grant_cap_entry_8(1),
            phase_b: None,
        }];
        let (_trace, public_inputs) =
            dregg_circuit::effect_vm::generate_effect_vm_trace(&state, &effects);
        assert_eq!(
            public_inputs[evm_pi::IS_AGENT_CELL].as_u32(),
            0,
            "trace generator should leave IS_AGENT_CELL at zero (executor sets it). \
             If this fires, remove the explicit set in generate_effect_vm_proof."
        );
    }

    // =====================================================================
    // Cross-app starbridge-tool integration tests (Issue #106 closure).
    //
    // These tests drive the four new tools (dregg_register_name,
    // dregg_publish_subscription, dregg_issue_credential,
    // dregg_register_service) through `dispatch_tool` against a real
    // NodeState (a fresh ledger + cipherclerk in a tempdir) and assert each
    // produces a receipt with a non-empty `effect_vm_proof_hex` plus
    // populated `effect_vm_public_inputs` / `effect_vm_trace_rows` /
    // `effect_vm_witness_hash_hex`. This is the "smallest test that
    // proves the loop closes" path: if every starbridge tool produces a
    // proof here, the same tools called over MCP stdio from a re-targeted
    // cross_app_helper will produce the same proofs in the demo's
    // on-disk receipt chain, and `verify_real.py`'s
    // `replay-chain` will Verify (not Unwitnessable) each entry.
    // =====================================================================

    use crate::state::NodeState;

    /// Build a fresh NodeState in a tempdir, unlock the cipherclerk, seed the
    /// agent cell with enough balance to pay turn fees, and return it ready for
    /// tool dispatch.
    async fn fresh_unlocked_state() -> (NodeState, tempfile::TempDir) {
        let tmp = tempfile::tempdir().expect("tempdir");
        // Deterministic seed so the test is reproducible.
        let mut seed = [0u8; 32];
        seed[0] = 0xA1;
        let state =
            NodeState::with_cclerk(tmp.path(), vec![], seed).expect("NodeState::with_cclerk");
        // Flip the unlocked flag — `with_cclerk` defaults to locked,
        // but the test bypasses passphrase entry.
        {
            let mut s = state.write().await;
            s.unlocked = true;
            let pk_bytes = s.cclerk.public_key().0;
            let cell = dregg_cell::Cell::with_balance(pk_bytes, [0u8; 32], 1_000_000);
            s.ledger
                .insert_cell(cell)
                .expect("test agent cell insert must succeed");
        }
        (state, tmp)
    }

    async fn fresh_unlocked_state_without_agent_cell() -> (NodeState, tempfile::TempDir) {
        let tmp = tempfile::tempdir().expect("tempdir");
        let mut seed = [0u8; 32];
        seed[0] = 0xD7;
        let state =
            NodeState::with_cclerk(tmp.path(), vec![], seed).expect("NodeState::with_cclerk");
        {
            let mut s = state.write().await;
            s.unlocked = true;
        }
        (state, tmp)
    }

    fn extract_json(result: &McpToolResult) -> Value {
        assert!(
            !result.is_error.unwrap_or(false),
            "tool returned error: {}",
            result
                .content
                .first()
                .map(|c| c.text.as_str())
                .unwrap_or("(no content)")
        );
        let text = result
            .content
            .first()
            .map(|c| c.text.as_str())
            .unwrap_or("");
        serde_json::from_str(text).expect("tool result content must be JSON")
    }

    // =====================================================================
    // MCP per-tool capability gate — THE TEETH.
    //
    // Before this work, `tools/call` was a flat match over ~45 tools behind a
    // single global `unlocked` bit: once unlocked, any client could invoke any
    // tool with NO per-tool authority check. Now each tool declares a scope verb
    // (`tool_required_scope`) and `enforce_tool_cap` requires the caller's
    // presented `Authorization::Token` to COVER that scope, verified by the
    // EXECUTOR's `verify_token_for_scope`.
    //
    // The negative test (`mcp_overscope_cap_rejected_by_executor`) is the
    // deliverable: a client presenting a `read`-scoped biscuit is REJECTED when
    // it calls an `admin` tool — and the rejection is the executor's
    // capability-cover failure, not narration.
    // =====================================================================

    /// Mint an MCP tools-access biscuit for `scope_verb`, packaged as the `_cap`
    /// argument a `tools/call` presents.
    async fn cap_arg_for(state: &NodeState, scope_verb: &str) -> Value {
        let s = state.read().await;
        let node_pk = s.cclerk.public_key().0;
        let biscuit = mint_tool_cap(&s.cclerk, &node_pk, scope_verb).expect("mint tool cap");
        serde_json::json!({ "_cap": { "biscuit": biscuit } })
    }

    // =====================================================================
    // Best-practices surface tests: every advertised prompt resolves, the
    // ocap `_cap` argument is declared in each tool schema, and the
    // completion endpoint autocompletes live dregg handles.
    // =====================================================================

    /// Every prompt in `prompts/list` MUST resolve in `prompts/get` — an
    /// advertised capability that errors is a best-practice violation. This
    /// regression pins the `verify_turn` prompt (previously listed but
    /// unhandled, so it fell into the unknown-prompt error branch).
    #[test]
    fn every_advertised_prompt_resolves() {
        for spec in prompt_specs() {
            // Supply each required arg so the get path doesn't reject on a
            // missing one; the point is that the NAME is handled.
            let mut args = serde_json::Map::new();
            for (name, _desc, _req) in spec.arguments {
                args.insert((*name).to_string(), Value::String("dead".repeat(16)));
            }
            let resp = handle_prompts_get(
                Value::from(1),
                serde_json::json!({ "name": spec.name, "arguments": args }),
            );
            let v = serde_json::to_value(&resp).unwrap();
            assert!(
                v.get("error").is_none(),
                "advertised prompt '{}' must resolve in prompts/get, got error: {v}",
                spec.name
            );
            assert!(
                v.get("result")
                    .and_then(|r| r.get("messages"))
                    .and_then(|m| m.as_array())
                    .map(|a| !a.is_empty())
                    .unwrap_or(false),
                "prompt '{}' must render at least one message",
                spec.name
            );
        }
    }

    /// Every tool's input schema declares the ocap `_cap` argument, so an agent
    /// reading tools/list — and a schema-validating client — discovers the
    /// capability requirement at the tool boundary (not just in prose).
    #[test]
    fn every_tool_schema_declares_cap_argument() {
        for d in tool_definitions() {
            let cap = d.input_schema.get("properties").and_then(|p| p.get("_cap"));
            assert!(
                cap.is_some(),
                "tool '{}' input schema must declare the '_cap' ocap argument",
                d.name
            );
            // And the group/scope metadata an orienting agent reads.
            assert!(
                d.input_schema.get("x-dregg-scope").is_some(),
                "tool '{}' schema must stamp x-dregg-scope",
                d.name
            );
        }
    }

    #[tokio::test]
    async fn completion_completes_cell_ids_for_resource_template() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let agent_cell = {
            let s = state.read().await;
            hex_encode(
                dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32]).as_bytes(),
            )
        };
        // Complete the dregg://cell/{cell_id} template variable with a prefix of
        // the agent cell that's actually in the ledger.
        let prefix = &agent_cell[..6];
        let resp = handle_completion_complete(
            Value::from(1),
            serde_json::json!({
                "ref": { "type": "ref/resource", "uri": "dregg://cell/" },
                "argument": { "name": "cell_id", "value": prefix }
            }),
            &state,
        )
        .await;
        let v = serde_json::to_value(&resp).unwrap();
        let values = v["result"]["completion"]["values"]
            .as_array()
            .expect("completion values array");
        assert!(
            values
                .iter()
                .any(|x| x.as_str() == Some(agent_cell.as_str())),
            "completion must surface the in-ledger agent cell id; got {values:?}"
        );
    }

    #[tokio::test]
    async fn completion_unknown_ref_returns_well_formed_empty() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let resp = handle_completion_complete(
            Value::from(1),
            serde_json::json!({
                "ref": { "type": "ref/prompt", "name": "orient" },
                "argument": { "name": "nonexistent", "value": "x" }
            }),
            &state,
        )
        .await;
        let v = serde_json::to_value(&resp).unwrap();
        assert_eq!(
            v["result"]["completion"]["values"]
                .as_array()
                .map(|a| a.len()),
            Some(0)
        );
        assert_eq!(v["result"]["completion"]["hasMore"], Value::Bool(false));
    }

    #[tokio::test]
    async fn mcp_in_scope_cap_admitted_by_executor() {
        // POSITIVE tooth: a `read`-scoped biscuit covers a `read` tool. The gate
        // verifies the credential against the tool's scope via the executor and
        // ADMITS the call (Ok).
        let (state, _tmp) = fresh_unlocked_state().await;
        {
            state.write().await.mcp_cap_enforce = true;
        }
        let args = cap_arg_for(&state, "read").await;
        // dregg_get_status requires the "read" scope.
        assert_eq!(tool_required_scope("dregg_get_status"), "read");
        enforce_tool_cap("dregg_get_status", &args, &state)
            .await
            .expect("a read-scoped cap must cover a read tool (executor admits)");
    }

    #[tokio::test]
    async fn mcp_overscope_cap_rejected_by_executor() {
        // NEGATIVE tooth (THE deliverable): a `read`-scoped biscuit does NOT
        // cover an `admin` tool. The gate runs the EXECUTOR's
        // verify_token_for_scope, which denies the cover, and the call is
        // rejected — it never reaches the tool body.
        let (state, _tmp) = fresh_unlocked_state().await;
        {
            state.write().await.mcp_cap_enforce = true;
        }
        let args = cap_arg_for(&state, "read").await;
        // dregg_grant_capability requires the "admin" scope.
        assert_eq!(tool_required_scope("dregg_grant_capability"), "admin");
        let err = enforce_tool_cap("dregg_grant_capability", &args, &state)
            .await
            .expect_err("a read-scoped cap MUST NOT cover an admin tool");
        assert!(
            err.contains("does not cover"),
            "rejection must be the executor's capability-cover failure, got: {err}"
        );
    }

    #[tokio::test]
    async fn mcp_missing_cap_rejected_under_enforcement() {
        // With enforcement ON, a `tools/call` presenting NO `_cap` is rejected
        // fail-closed — the per-tool cap gate is a real boundary, not optional.
        let (state, _tmp) = fresh_unlocked_state().await;
        {
            state.write().await.mcp_cap_enforce = true;
        }
        let no_cap = serde_json::json!({});
        let err = enforce_tool_cap("dregg_grant_capability", &no_cap, &state)
            .await
            .expect_err("missing cap under enforcement must be rejected");
        assert!(
            err.contains("requires a covering"),
            "expected a missing-cap rejection, got: {err}"
        );
    }

    #[tokio::test]
    async fn mcp_wrong_issuer_cap_rejected() {
        // A biscuit minted under a DIFFERENT issuer key (not the node's MCP-cap
        // issuer) must be rejected: the executor's trust anchor requires the
        // issuer to equal the authority cell's verification key. This proves the
        // gate binds the credential to THIS node's granting authority.
        let (state, _tmp) = fresh_unlocked_state().await;
        {
            state.write().await.mcp_cap_enforce = true;
        }
        // Mint an admin-scoped biscuit under an unrelated keypair.
        let foreign_kp = dregg_token::biscuit_auth::KeyPair::new();
        let node_pk = { state.read().await.cclerk.public_key().0 };
        let authority_cell_id = dregg_cell::CellId::derive_raw(&node_pk, &[0u8; 32]);
        let svc = hex_encode(authority_cell_id.as_bytes());
        let action = hex_encode(dregg_turn::action::symbol("admin").as_slice());
        let foreign = {
            use dregg_token::traits::AuthToken;
            dregg_token::BiscuitToken::mint_dregg(
                &foreign_kp,
                &[],
                &[(svc, action)],
                &[],
                &[],
                &[],
                None,
            )
            .unwrap()
            .to_encoded()
            .unwrap()
        };
        let args = serde_json::json!({ "_cap": { "biscuit": foreign } });
        let err = enforce_tool_cap("dregg_grant_capability", &args, &state)
            .await
            .expect_err("a foreign-issuer cap MUST be rejected by the executor's trust anchor");
        assert!(
            err.contains("does not cover"),
            "expected an executor trust-anchor/cover rejection, got: {err}"
        );
    }

    /// R7 (temporal leg): a stored cap with a HEIGHT-BOUND expiry caveat must
    /// die when consensus passes the bound. The gate's verifying executor used
    /// to sit at its default `block_height = 0`, under which `time($t), $t < N`
    /// trivially holds forever — an expired cap verified FOREVER. The fix
    /// snapshots the CURRENT attested height into `McpCapContext` and binds the
    /// executor to it; this test pins both directions (admits inside the
    /// window, rejects past it).
    #[tokio::test]
    async fn mcp_height_expired_cap_rejected_at_current_height() {
        let (state, _tmp) = fresh_unlocked_state().await;
        {
            state.write().await.mcp_cap_enforce = true;
        }
        // Mint a read-scoped cap under the node's REAL MCP issuer key, with an
        // expiry caveat: valid only while the consensus height is < 5.
        let encoded = {
            let s = state.read().await;
            use dregg_token::traits::AuthToken;
            let kp = mcp_cap_issuer_keypair(&s.cclerk);
            let node_pk = s.cclerk.public_key().0;
            let authority_cell_id = dregg_cell::CellId::derive_raw(&node_pk, &[0u8; 32]);
            let svc = hex_encode(authority_cell_id.as_bytes());
            let action = hex_encode(dregg_turn::action::symbol("read").as_slice());
            let mut code =
                dregg_token::dregg::authority_datalog(&[], &[(svc, action)], &[], &[], &[], None)
                    .unwrap();
            code.push_str("check if time($t), $t < 5;\n");
            dregg_token::BiscuitToken::mint(&kp, &code)
                .unwrap()
                .to_encoded()
                .unwrap()
        };
        let args = serde_json::json!({ "_cap": { "biscuit": encoded } });

        let mut ctx = McpCapContext::snapshot(&state).await;
        let cred = parse_presented_cap(&args, &ctx.issuer_pubkey).expect("cap argument parses");

        // Inside the expiry window (fresh devnet, height 0 < 5): admitted.
        ctx.block_height = 0;
        ctx.cap_covers_tool(&cred, "dregg_get_status")
            .expect("an unexpired cap must cover the read tool inside its window");

        // Past the expiry bound (height 10 ≥ 5): the SAME stored cap is dead.
        ctx.block_height = 10;
        ctx.cap_covers_tool(&cred, "dregg_get_status")
            .expect_err("a height-expired cap MUST be rejected at the current height");
    }

    #[tokio::test]
    async fn bearer_cap_exercise_rejects_missing_agent_pre_state_before_commit() {
        let (state, _tmp) = fresh_unlocked_state_without_agent_cell().await;
        let target_cell = "11".repeat(32);
        let recipient_cell = "22".repeat(32);
        let params = serde_json::json!({
            "target_cell": target_cell,
            "method": "transfer",
            "delegation_chain": "33".repeat(64),
            "delegator_pk": "44".repeat(32),
            "bearer_pk": "55".repeat(32),
            "expires_at": 10_000u64,
            "effects": [{
                "type": "transfer",
                "from": "11".repeat(32),
                "to": recipient_cell,
                "amount": 1u64,
            }]
        });

        let result = dispatch_tool("dregg_exercise_bearer_cap", params, &state).await;
        let j = extract_json(&result);
        assert_eq!(
            j.get("activity_status").and_then(|v| v.as_str()),
            Some("rejected")
        );
        assert_eq!(
            j.get("proof_status").and_then(|v| v.as_str()),
            Some("missing_pre_state")
        );
        assert_eq!(j.get("exercised").and_then(|v| v.as_bool()), Some(false));
        assert!(
            j.get("effect_vm_proof_hex").is_none(),
            "missing pre-state must not surface a null proof as if the turn committed: {j}"
        );
        assert_eq!(
            state.read().await.cclerk.receipt_chain_length(),
            0,
            "truthful rejection must happen before the receipt chain advances"
        );
    }

    #[tokio::test]
    async fn grant_capability_rejects_missing_agent_pre_state_before_commit() {
        let (state, _tmp) = fresh_unlocked_state_without_agent_cell().await;
        let params = serde_json::json!({
            "to_agent": "77".repeat(32),
            "target_cell": "88".repeat(32),
            "permissions": "signature",
        });

        let result = dispatch_tool("dregg_grant_capability", params, &state).await;
        let j = extract_json(&result);
        eprintln!("grant witness artifact response: {j}");
        assert_eq!(
            j.get("activity_status").and_then(|v| v.as_str()),
            Some("rejected")
        );
        assert_eq!(
            j.get("proof_status").and_then(|v| v.as_str()),
            Some("missing_pre_state")
        );
        assert_eq!(
            state.read().await.cclerk.receipt_chain_length(),
            0,
            "grant rejection must happen before the receipt chain advances"
        );
    }

    #[tokio::test]
    async fn grant_capability_rejects_missing_recipient_pre_state_instead_of_stub() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let target_cell = {
            let s = state.read().await;
            let id = dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32]);
            hex_encode(&id.0)
        };
        let params = serde_json::json!({
            "to_agent": "77".repeat(32),
            "target_cell": target_cell,
            "permissions": "signature",
        });

        let result = dispatch_tool("dregg_grant_capability", params, &state).await;
        let j = extract_json(&result);
        assert_eq!(
            j.get("activity_status").and_then(|v| v.as_str()),
            Some("rejected")
        );
        assert_eq!(
            j.get("proof_status").and_then(|v| v.as_str()),
            Some("missing_pre_state")
        );
        assert_eq!(
            state.read().await.cclerk.receipt_chain_length(),
            0,
            "missing recipient pre-state must not be hidden behind a synthetic stub"
        );
    }

    #[tokio::test]
    async fn bearer_cap_exercise_rejects_missing_target_pre_state_instead_of_stub() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let params = serde_json::json!({
            "target_cell": "11".repeat(32),
            "method": "transfer",
            "delegation_chain": "33".repeat(64),
            "delegator_pk": "44".repeat(32),
            "bearer_pk": "55".repeat(32),
            "expires_at": 10_000u64,
            "effects": [{
                "type": "transfer",
                "from": "11".repeat(32),
                "to": "22".repeat(32),
                "amount": 1u64,
            }]
        });

        let result = dispatch_tool("dregg_exercise_bearer_cap", params, &state).await;
        let j = extract_json(&result);
        assert_eq!(
            j.get("activity_status").and_then(|v| v.as_str()),
            Some("rejected")
        );
        assert_eq!(
            j.get("proof_status").and_then(|v| v.as_str()),
            Some("missing_pre_state")
        );
        assert_eq!(
            state.read().await.cclerk.receipt_chain_length(),
            0,
            "missing bearer target pre-state must not be hidden behind a synthetic stub"
        );
    }

    #[tokio::test]
    async fn bilateral_action_rejects_missing_to_pre_state_instead_of_stub_commit() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let from_cell = {
            let s = state.read().await;
            dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32])
        };
        let params = serde_json::json!({
            "mode": "transfer",
            "from": hex_encode(&from_cell.0),
            "to": "66".repeat(32),
            "amount": 5u64,
        });

        let result = dispatch_tool("dregg_bilateral_action", params, &state).await;
        let j = extract_json(&result);
        assert_eq!(
            j.get("activity_status").and_then(|v| v.as_str()),
            Some("rejected")
        );
        assert_eq!(
            j.get("proof_status").and_then(|v| v.as_str()),
            Some("missing_pre_state")
        );
        assert_eq!(j.get("committed").and_then(|v| v.as_bool()), Some(false));
        assert!(
            j.get("to_side").is_none(),
            "a rejected bilateral action must not present null witnessed receipts: {j}"
        );
    }

    #[tokio::test]
    async fn handoff_cert_rejects_missing_target_pre_state_before_commit() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let mut seed = [0u8; 32];
        seed[0] = 0xE1;
        let params = serde_json::json!({
            "target_cell": "99".repeat(32),
            "introducer_sk": hex_encode(&seed),
            "permissions": "signature",
        });

        let result = dispatch_tool("dregg_exercise_handoff_cert", params, &state).await;
        let j = extract_json(&result);
        assert_eq!(
            j.get("activity_status").and_then(|v| v.as_str()),
            Some("rejected")
        );
        assert_eq!(
            j.get("proof_status").and_then(|v| v.as_str()),
            Some("missing_pre_state")
        );
        assert_eq!(j.get("exercised").and_then(|v| v.as_bool()), Some(false));
        assert_eq!(
            state.read().await.cclerk.receipt_chain_length(),
            0,
            "handoff rejection must happen before the receipt chain advances"
        );
    }

    #[tokio::test]
    async fn handoff_cert_rejects_missing_downstream_pre_state_instead_of_stub() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let target_cell = {
            let s = state.read().await;
            dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32])
        };
        let mut seed = [0u8; 32];
        seed[0] = 0xE2;
        let params = serde_json::json!({
            "target_cell": hex_encode(&target_cell.0),
            "introducer_sk": hex_encode(&seed),
            "permissions": "signature",
            "effects": [{
                "type": "transfer",
                "from": hex_encode(&target_cell.0),
                "to": "ab".repeat(32),
                "amount": 1u64,
            }]
        });

        let result = dispatch_tool("dregg_exercise_handoff_cert", params, &state).await;
        let j = extract_json(&result);
        assert_eq!(
            j.get("activity_status").and_then(|v| v.as_str()),
            Some("rejected")
        );
        assert_eq!(
            j.get("proof_status").and_then(|v| v.as_str()),
            Some("missing_pre_state")
        );
        assert_eq!(j.get("exercised").and_then(|v| v.as_bool()), Some(false));
        assert_eq!(
            state.read().await.cclerk.receipt_chain_length(),
            0,
            "missing downstream pre-state must not be hidden behind a synthetic stub"
        );
    }

    // ⚑ TOMBSTONE 2026-07-28 — THE `not(feature = "prover")` V1-FLOOR LANE WAS DELETED, AND
    // THE DEFECT IT WAS HIDING IS NOW FIXED (the suite below is the replacement).
    //
    // Nine tests and four helpers lived here behind `#[cfg(not(feature = "prover"))]`, and
    // `dregg-node`'s `prover` feature was `default = ["prover"]` with no `--no-default-features`
    // consumer in the tree — so they emitted no line in any run. Worse: the OFF position DID NOT
    // COMPILE. There was no configuration in which these tests existed.
    //
    // Un-gated and RUN before deleting, all nine FAILED for ONE reason:
    // `try_generate_effect_vm_proof` (`mcp/proof.rs`) returns `Err` UNCONDITIONALLY — no `cfg` —
    // because the standalone v1 `EffectVmAir` attestation is retired, and `require_effect_vm_proof`
    // turned that into an early return from the TOOL. Five tools therefore could not commit at
    // all. That helper is now DELETED: the tools commit and report the attestation truthfully
    // (`attestation_pending` / `attestation_unattested` / `attestation_not_required` /
    // `attestation_unprovable`), routed to the SAME async prove pool the HTTP submit path uses.
    //
    // The ninth, `exercise_handoff_cert_forged_introducer_pk_rejected`, was a FAKE SECURITY POLE:
    // it claimed a forged `introducer_pk` was refused by the executor, but the executor was never
    // reached — `exercised: false` was satisfied by the RETIREMENT, and its only discriminating
    // assertion was a substring match over the refusal prose. Its replacement below
    // (`exercise_handoff_cert_forged_introducer_pk_is_refused_by_variant`) drives the same tool,
    // reaches `authorize.rs`'s step-3b binding, and asserts `CapTpIntroducerKeyMismatch` BY
    // VARIANT. The turn-level pole for the same property remains
    // `turn/tests/captp_delivered_amplification.rs::a2_captp_cert_naming_a_federation_that_did_not_sign_it_is_refused`.

    // =====================================================================
    // THE FIVE TOOLS THAT COULD NOT COMMIT — driven, honest AND adversarial.
    //
    // Every test here dispatches the REAL tool through `dispatch_tool` against a real
    // NodeState. The honest calls assert `activity_status: "committed"`; the adversarial
    // ones assert the refusal BY `rejection_variant` (the serde variant name of the
    // executor's `TurnError`), never by substring — a substring cannot tell a forged key
    // from a dead lane, which is exactly how the deleted pole above fooled its reader.
    //
    // `proof_status` on a committed response is an ATTESTATION disposition, not a gate:
    // these tests install no prove pool, so the honest answer is `attestation_unattested`
    // (there is a transition to attest and nothing took the job) or
    // `attestation_not_required` (no effect touches the actor cell). Both are COMMITTED.
    // =====================================================================

    /// Every committed MCP tool response must carry an attestation disposition that
    /// (a) is one of the four `attestation_*` values, (b) agrees with the `attestation`
    /// block, and (c) does NOT resurrect the retired v1 field set.
    fn assert_committed_attestation_shape(j: &Value) {
        let status = j
            .get("proof_status")
            .and_then(|v| v.as_str())
            .unwrap_or("(missing)");
        assert!(
            matches!(
                status,
                "attestation_pending"
                    | "attestation_unattested"
                    | "attestation_not_required"
                    | "attestation_unprovable"
            ),
            "a committed tool response must report an attestation disposition, got '{status}': {j}"
        );
        assert_eq!(
            j.pointer("/attestation/status").and_then(|v| v.as_str()),
            Some(status),
            "the attestation block must agree with proof_status: {j}"
        );
        assert!(
            j.pointer("/attestation/leg")
                .and_then(|v| v.as_str())
                .is_some_and(|leg| leg.contains("prove_pool")),
            "the attestation must name the LEG a caller is waiting on: {j}"
        );
        for retired in [
            "effect_vm_proof_hex",
            "effect_vm_public_inputs",
            "effect_vm_trace_rows",
            "effect_vm_witness_hash_hex",
        ] {
            assert!(
                j.get(retired).is_none(),
                "the retired v1 field '{retired}' must not reappear (it can only ever be null): {j}"
            );
        }
    }

    fn rejection_variant_of(j: &Value) -> &str {
        j.get("rejection_variant")
            .and_then(|v| v.as_str())
            .unwrap_or_else(|| panic!("a rejected tool response must name the variant: {j}"))
    }

    /// Insert a cell owned by `pk` with `balance`, returning its id.
    async fn insert_cell(state: &NodeState, pk: [u8; 32], balance: i64) -> dregg_cell::CellId {
        let mut s = state.write().await;
        let cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], balance);
        let id = cell.id();
        s.ledger.insert_cell(cell).expect("cell insert");
        id
    }

    // ── dregg_grant_capability ───────────────────────────────────────────

    /// THE HONEST PATH. Before this work the same call returned
    /// `activity_status: "rejected"` / `proof_status: "v1_attestation_retired"` — a
    /// refusal that reads like an authorization failure, produced because an ADDITIVE
    /// attestation could not be minted.
    #[tokio::test]
    async fn grant_capability_commits_and_reports_its_attestation() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let (target_cell, recipient_cell) = {
            let s = state.read().await;
            let id = dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32]);
            drop(s);
            let recipient = insert_cell(&state, [0x77u8; 32], 0).await;
            (hex_encode(&id.0), hex_encode(&recipient.0))
        };
        let params = serde_json::json!({
            "to_agent": recipient_cell,
            "target_cell": target_cell,
            "permissions": "signature",
        });

        let result = dispatch_tool("dregg_grant_capability", params, &state).await;
        let j = extract_json(&result);
        assert_eq!(
            j.get("activity_status").and_then(|v| v.as_str()),
            Some("committed"),
            "an honest grant must COMMIT: {j}"
        );
        assert_eq!(j.get("granted").and_then(|v| v.as_bool()), Some(true));
        assert_committed_attestation_shape(&j);
        assert_eq!(
            state.read().await.cclerk.receipt_chain_length(),
            1,
            "a committed grant must advance the agent's receipt chain"
        );
    }

    /// THE POLE. A grant naming a target cell this agent has no authority over is
    /// refused BY THE EXECUTOR — and the refusal is reported by VARIANT, so it can be
    /// told apart from an unrelated failure.
    #[tokio::test]
    async fn grant_capability_over_a_foreign_cell_is_refused_by_variant() {
        let (state, _tmp) = fresh_unlocked_state().await;
        // A cell owned by SOMEONE ELSE's key, present in the ledger (so the
        // missing-pre-state guard cannot be what refuses).
        let foreign = insert_cell(&state, [0x5Au8; 32], 500).await;
        let recipient = insert_cell(&state, [0x77u8; 32], 0).await;
        let params = serde_json::json!({
            "to_agent": hex_encode(&recipient.0),
            "target_cell": hex_encode(&foreign.0),
            "permissions": "signature",
        });

        let result = dispatch_tool("dregg_grant_capability", params, &state).await;
        let j = extract_json(&result);
        assert_eq!(
            j.get("activity_status").and_then(|v| v.as_str()),
            Some("rejected"),
            "granting authority over a cell the agent does not hold must be refused: {j}"
        );
        assert_eq!(
            rejection_variant_of(&j),
            "CapabilityNotHeld",
            "the refusal must be the executor's authority check, named by variant: {j}"
        );
        assert_eq!(
            state.read().await.cclerk.receipt_chain_length(),
            0,
            "a refused grant must not advance the receipt chain"
        );
    }

    // ── dregg_exercise_bearer_cap ────────────────────────────────────────

    /// THE HONEST PATH: a self-delegation the node's own key signed, carrying a real
    /// downstream transfer. Before this work every bearer exercise CARRYING AN EFFECT
    /// was refused (and one carrying none was not — the gate fired on exactly the calls
    /// that did something).
    #[tokio::test]
    async fn exercise_bearer_cap_honest_delegation_commits() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let recipient = insert_cell(&state, [0x77u8; 32], 0).await;
        let (agent_cell, delegation_hex, delegator_pk_hex, bearer_pk_hex) = {
            let s = state.read().await;
            let agent_cell = dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32]);
            let bearer_pk = s.cclerk.public_key().0;
            let msg = dregg_turn::TurnExecutor::compute_bearer_delegation_message(
                &agent_cell,
                &dregg_cell::AuthRequired::Signature,
                &bearer_pk,
                10_000,
                &s.federation_id,
            );
            // The delegator IS this node's key: `cell_by_pubkey(delegator_pk)` must find
            // the agent cell (`Cell::with_balance(cclerk.public_key().0, …)`), and the
            // signature must verify under that same key.
            let sig = s.cclerk.sign_bytes(&msg);
            (
                hex_encode(&agent_cell.0),
                hex_encode(&sig.0),
                hex_encode(&bearer_pk),
                hex_encode(&bearer_pk),
            )
        };
        let params = serde_json::json!({
            "target_cell": agent_cell,
            "method": "transfer",
            "delegation_chain": delegation_hex,
            "delegator_pk": delegator_pk_hex,
            "bearer_pk": bearer_pk_hex,
            "expires_at": 10_000u64,
            "effects": [{
                "type": "transfer",
                "from": agent_cell,
                "to": hex_encode(&recipient.0),
                "amount": 5u64,
            }]
        });

        let result = dispatch_tool("dregg_exercise_bearer_cap", params, &state).await;
        let j = extract_json(&result);
        assert_eq!(
            j.get("activity_status").and_then(|v| v.as_str()),
            Some("committed"),
            "an honest bearer-cap exercise must COMMIT: {j}"
        );
        assert_eq!(j.get("exercised").and_then(|v| v.as_bool()), Some(true));
        assert_committed_attestation_shape(&j);
    }

    /// THE POLE: a forged delegation signature is refused by the executor's bearer-cap
    /// verify (`authorize.rs`), by VARIANT.
    #[tokio::test]
    async fn exercise_bearer_cap_forged_delegation_is_refused_by_variant() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let recipient = insert_cell(&state, [0x77u8; 32], 0).await;
        let (agent_cell, delegator_pk_hex, bearer_pk_hex) = {
            let s = state.read().await;
            let agent_cell = dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32]);
            (
                hex_encode(&agent_cell.0),
                hex_encode(&s.cclerk.public_key().0),
                hex_encode(&s.cclerk.public_key().0),
            )
        };
        let params = serde_json::json!({
            "target_cell": agent_cell,
            "method": "transfer",
            // A signature over nothing: the delegator never signed this delegation.
            "delegation_chain": "ab".repeat(64),
            "delegator_pk": delegator_pk_hex,
            "bearer_pk": bearer_pk_hex,
            "expires_at": 10_000u64,
            "effects": [{
                "type": "transfer",
                "from": agent_cell,
                "to": hex_encode(&recipient.0),
                "amount": 5u64,
            }]
        });

        let result = dispatch_tool("dregg_exercise_bearer_cap", params, &state).await;
        let j = extract_json(&result);
        assert_eq!(
            j.get("activity_status").and_then(|v| v.as_str()),
            Some("rejected"),
            "a forged delegation must be REFUSED: {j}"
        );
        assert_eq!(
            rejection_variant_of(&j),
            "BearerCapInvalidProof",
            "the refusal must be the bearer-cap proof check, named by variant: {j}"
        );
        assert_eq!(
            state.read().await.cclerk.receipt_chain_length(),
            0,
            "a forged delegation must not advance the receipt chain"
        );
    }

    // ── dregg_exercise_handoff_cert ──────────────────────────────────────

    /// The node's own signing key, as the `introducer_sk` hex the tool takes. The
    /// introducer must ACTUALLY hold authority over the target cell — a certificate
    /// from a key that owns nothing is refused (`CapTpIntroducerLacksCapability`),
    /// which is the executor being right, not the tool being broken.
    async fn node_sk_hex(state: &NodeState) -> String {
        let s = state.read().await;
        hex_encode(&s.cclerk.gossip_signing_key().to_bytes())
    }

    async fn node_agent_cell_hex(state: &NodeState) -> String {
        let s = state.read().await;
        hex_encode(&dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32]).0)
    }

    /// THE HONEST PATH (resurrected: the version of this test that existed was compiled
    /// by no configuration, and would have failed on the retirement if it had been —
    /// and its fixture was not honest either: it handed the tool a RANDOM introducer
    /// key, which the executor correctly refuses because that key holds no authority
    /// over the target. Nobody could see that, because the retirement refused first).
    #[tokio::test]
    async fn exercise_handoff_cert_honest_path_commits() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let target_cell = node_agent_cell_hex(&state).await;
        let params = serde_json::json!({
            "target_cell": target_cell,
            // The introducer OWNS the target cell, so the certificate delegates
            // authority it actually possesses.
            "introducer_sk": node_sk_hex(&state).await,
            "permissions": "signature",
        });

        let result = dispatch_tool("dregg_exercise_handoff_cert", params, &state).await;
        let j = extract_json(&result);
        assert_eq!(
            j.get("activity_status").and_then(|v| v.as_str()),
            Some("committed"),
            "an honest handoff-cert exercise must COMMIT: {j}"
        );
        assert_eq!(j.get("exercised").and_then(|v| v.as_bool()), Some(true));
        assert!(j.get("cert_hash").and_then(|v| v.as_str()).is_some());
        assert_committed_attestation_shape(&j);
    }

    /// THE POLE THAT WAS FAKE, MADE REAL — and it is the attack `authorize.rs` step 3b
    /// was written for: the presenter holds a real signing key (so the certificate
    /// SIGNATURE verifies under the pk it supplies) but names a FEDERATION IT DOES NOT
    /// CONTROL as the certificate's introducer. Until 2026-07-25 that delivery was
    /// ATTRIBUTED to the named federation, which never signed anything.
    ///
    /// Both refusals below are asserted BY VARIANT, and they are DIFFERENT variants —
    /// which is the whole point: the deleted version of this test matched the substrings
    /// `"rejected" | "introducer" | "invalid"` against a message produced by the v1
    /// RETIREMENT, so it could not tell a forged key from a dead lane, let alone one
    /// authorization failure from another.
    #[tokio::test]
    async fn exercise_handoff_cert_forged_introducer_pk_is_refused_by_variant() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let target_cell = node_agent_cell_hex(&state).await;
        let honest_sk = node_sk_hex(&state).await;

        // (a) NAMING A FEDERATION THAT DID NOT SIGN: the cert's `introducer` field is a
        //     federation the presenter does not hold, while the action carries the
        //     presenter's own (signature-valid) pk. Step 3b binds the two and refuses.
        let params = serde_json::json!({
            "target_cell": target_cell,
            "introducer_sk": honest_sk,
            "introducer_federation": "bb".repeat(32),
            "permissions": "signature",
        });
        let j = extract_json(&dispatch_tool("dregg_exercise_handoff_cert", params, &state).await);
        assert_eq!(
            j.get("activity_status").and_then(|v| v.as_str()),
            Some("rejected"),
            "a cert naming a federation that did not sign it must be REFUSED: {j}"
        );
        assert_eq!(j.get("exercised").and_then(|v| v.as_bool()), Some(false));
        assert_eq!(
            rejection_variant_of(&j),
            "CapTpIntroducerKeyMismatch",
            "the refusal must be the step-3b introducer binding, named by variant: {j}"
        );

        // (b) A pk the certificate was NOT signed under fails one step earlier, and is a
        //     DIFFERENT named refusal — not the same catch-all.
        let params = serde_json::json!({
            "target_cell": target_cell,
            "introducer_sk": honest_sk,
            "introducer_pk": "aa".repeat(32),
            "permissions": "signature",
        });
        let j = extract_json(&dispatch_tool("dregg_exercise_handoff_cert", params, &state).await);
        assert_eq!(
            j.get("activity_status").and_then(|v| v.as_str()),
            Some("rejected"),
            "a forged introducer_pk must be REFUSED: {j}"
        );
        assert_eq!(
            rejection_variant_of(&j),
            "InvalidAuthorization",
            "the certificate signature check must refuse this one, by variant: {j}"
        );

        assert_eq!(
            state.read().await.cclerk.receipt_chain_length(),
            0,
            "neither forged handoff may advance the receipt chain"
        );
    }

    // ── dregg_bilateral_action (both sides) ──────────────────────────────

    /// THE HONEST PATH. Both sides used to demand their own v1 per-cell proof before the
    /// turn ran, so this tool refused every call.
    #[tokio::test]
    async fn bilateral_action_transfer_commits_and_reports_the_schedule() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let from = {
            let s = state.read().await;
            dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32])
        };
        let to = insert_cell(&state, [0x77u8; 32], 0).await;
        let params = serde_json::json!({
            "mode": "transfer",
            "from": hex_encode(&from.0),
            "to": hex_encode(&to.0),
            "amount": 10u64,
        });

        let result = dispatch_tool("dregg_bilateral_action", params, &state).await;
        let j = extract_json(&result);
        assert_eq!(
            j.get("activity_status").and_then(|v| v.as_str()),
            Some("committed"),
            "an honest bilateral transfer must COMMIT: {j}"
        );
        assert_eq!(j.get("committed").and_then(|v| v.as_bool()), Some(true));
        assert_committed_attestation_shape(&j);
        assert_eq!(
            j.pointer("/from_side/outbound_transfer")
                .and_then(|v| v.as_u64()),
            Some(1),
            "the from-side schedule must record the outbound transfer: {j}"
        );
        assert_eq!(
            j.pointer("/to_side/inbound_transfer")
                .and_then(|v| v.as_u64()),
            Some(1),
            "the to-side schedule must record the inbound transfer: {j}"
        );
        // The retired two-sided artifacts must not come back as null placeholders.
        assert!(
            j.get("aggregated_bundle").is_none() && j.get("aggregation_status").is_none(),
            "the v1 aggregation keys are gone, not nulled: {j}"
        );
    }

    /// THE POLE: a transfer beyond the from-cell's balance is refused by the executor's
    /// conservation check, by VARIANT.
    #[tokio::test]
    async fn bilateral_action_over_balance_is_refused_by_variant() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let from = {
            let s = state.read().await;
            dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &[0u8; 32])
        };
        let to = insert_cell(&state, [0x77u8; 32], 0).await;
        let params = serde_json::json!({
            "mode": "transfer",
            "from": hex_encode(&from.0),
            "to": hex_encode(&to.0),
            "amount": 999_999_999_999u64,
        });

        let result = dispatch_tool("dregg_bilateral_action", params, &state).await;
        let j = extract_json(&result);
        assert_eq!(
            j.get("activity_status").and_then(|v| v.as_str()),
            Some("rejected"),
            "a transfer beyond the balance must be REFUSED: {j}"
        );
        assert_eq!(
            rejection_variant_of(&j),
            "InsufficientBalance",
            "the refusal must be the balance check, named by variant: {j}"
        );
        assert_eq!(
            state.read().await.cclerk.receipt_chain_length(),
            0,
            "an over-balance transfer must not advance the receipt chain"
        );
    }

    /// The starbridge-app commit path (`dregg_register_name` and its three siblings)
    /// consulted the retired v1 producer AFTER committing, chaining and gossiping, then
    /// reported `proof_status: "v1_attestation_retired"` forever. It now enqueues the
    /// LIVE attestation at the same seam the HTTP path uses.
    #[tokio::test]
    async fn register_name_commits_and_reports_a_live_attestation_disposition() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let params = serde_json::json!({
            "name": "alice.dregg",
            "expiry_height": 100_000u64,
        });
        let result = dispatch_tool("dregg_register_name", params, &state).await;
        let j = extract_json(&result);
        assert_eq!(
            j.get("committed").and_then(|v| v.as_bool()),
            Some(true),
            "register_name must commit: {j}"
        );
        assert_committed_attestation_shape(&j);
        assert!(
            j.get("effect_vm_proof_error").is_none(),
            "the retired-lane error field must be gone, not reported on every call: {j}"
        );
    }

    /// The cross-fed AttestedRoot quorum, made HYBRID (ed25519 ∧ ML-DSA-65).
    ///
    /// The cross-fed verifier checks `AttestedRoot.quorum_signatures` (ed25519)
    /// over `root.signing_message()`. Here a SELF-CONTAINED hybrid quorum (each
    /// signer's ed25519 signature AND its ML-DSA-65 signature + self-carried
    /// ML-DSA public key) over the SAME message is verified via the shared
    /// `dregg_federation::receipt::verify_hybrid_quorum_sigs` — the one place the
    /// classical ∧ pq rule lives. A forged or missing ML-DSA half is rejected
    /// even with a valid ed25519 half (the teeth), and a non-member signer is
    /// rejected. The wire `types::AttestedRoot` now carries this `hybrid_quorum`
    /// and `verify_cross_fed_bundle` (in `verifier/`) requires it — a
    /// classical-only root fails closed (postcard flag-day; see
    /// `dregg_types::AttestedRoot::hybrid_quorum`).
    #[test]
    fn cross_fed_attested_root_hybrid_quorum_teeth() {
        use dregg_federation::frost::MlDsaSigningKey;
        use dregg_federation::receipt::verify_hybrid_quorum_sigs;
        use dregg_types::{AttestedRoot, FederationId, HybridQuorumSig};

        let kps: Vec<(dregg_types::SigningKey, dregg_types::PublicKey)> = (0..3)
            .map(|i| {
                let mut s = [0u8; 32];
                s[0] = 0x51;
                s[1] = i as u8;
                let sk = dregg_types::SigningKey::from_bytes(&s);
                let pk = sk.public_key();
                (sk, pk)
            })
            .collect();
        let members: Vec<dregg_types::PublicKey> = kps.iter().map(|(_, pk)| *pk).collect();
        let pq: Vec<_> = (0..3)
            .map(|i| {
                let mut s = [0u8; 32];
                s[0] = 0x52;
                s[1] = i as u8;
                MlDsaSigningKey::from_seed(&s)
            })
            .collect();
        // The ENROLLED ML-DSA roster — aligned index-for-index with `members`.
        let ml_dsa_roster: Vec<dregg_federation::frost::MlDsaPublicKey> =
            pq.iter().map(|(pk, _)| pk.clone()).collect();
        let fed_id = dregg_federation::derive_federation_id_with_epoch(&members, 0);

        let root = AttestedRoot {
            merkle_root: [7u8; 32],
            note_tree_root: None,
            nullifier_set_root: None,
            height: 42,
            timestamp: 1_700_000_042,
            blocklace_block_id: Some([9u8; 32]),
            finality_round: Some(42),
            quorum_signatures: Vec::new(),
            threshold_qc: None,
            threshold: 2,
            federation_id: FederationId(fed_id),
            receipt_stream_root: None,
            hybrid_quorum: Vec::new(),
        };
        let message = root.signing_message();

        let make = |idxs: &[usize]| -> Vec<HybridQuorumSig> {
            idxs.iter()
                .map(|&i| HybridQuorumSig {
                    pubkey: kps[i].1,
                    signature: dregg_types::sign(&kps[i].0, &message),
                    ml_dsa_pubkey: pq[i].0.0.to_vec(),
                    pq_signature: pq[i].1.sign(&message).expect("ml-dsa sign"),
                })
                .collect()
        };

        // Honest 2-of-3 hybrid cross-fed quorum verifies (BOTH halves, PQ enrolled).
        assert!(
            verify_hybrid_quorum_sigs(&make(&[0, 1]), &message, &members, &ml_dsa_roster, 2),
            "honest hybrid cross-fed quorum must verify"
        );

        // TEETH: forge the ML-DSA half, keep a VALID ed25519 half → REJECT.
        let mut forged = make(&[0, 1]);
        forged[0].pq_signature[0] ^= 0xFF;
        assert!(
            !verify_hybrid_quorum_sigs(&forged, &message, &members, &ml_dsa_roster, 2),
            "forged ML-DSA half must reject even with a valid ed25519 half"
        );

        // TEETH: missing (empty) PQ half → REJECT.
        let mut missing = make(&[0, 1]);
        missing[1].pq_signature = Vec::new();
        assert!(
            !verify_hybrid_quorum_sigs(&missing, &message, &members, &ml_dsa_roster, 2),
            "missing ML-DSA half must reject"
        );

        // QUANTUM-FORGERY TEETH: enrolled member 0's ed25519 is "broken" (we reuse
        // its key) but the ML-DSA half carries a FRESH attacker key with a PQ
        // signature valid under it — REJECTED because it is not the enrolled key.
        let attacker = MlDsaSigningKey::from_seed(&[0xC3; 32]);
        let mut quantum = make(&[0, 1]);
        quantum[0].ml_dsa_pubkey = attacker.0.0.to_vec();
        quantum[0].pq_signature = attacker.1.sign(&message).expect("ml-dsa sign");
        assert!(
            !verify_hybrid_quorum_sigs(&quantum, &message, &members, &ml_dsa_roster, 2),
            "a self-carried attacker ML-DSA key (not the enrolled key) must reject"
        );

        // NO SILENT DOWNGRADE: an empty (misaligned) enrolled roster fails closed.
        assert!(
            !verify_hybrid_quorum_sigs(&make(&[0, 1]), &message, &members, &[], 2),
            "an unconfigured (empty) enrolled roster must fail closed"
        );

        // Non-member fully-valid hybrid signer → REJECT.
        let mut outs = [0u8; 32];
        outs[0] = 0xEE;
        let outsider_sk = dregg_types::SigningKey::from_bytes(&outs);
        let (out_pq_pk, out_pq_sk) = MlDsaSigningKey::from_seed(&[0xEF; 32]);
        let outsider = vec![HybridQuorumSig {
            pubkey: outsider_sk.public_key(),
            signature: dregg_types::sign(&outsider_sk, &message),
            ml_dsa_pubkey: out_pq_pk.0.to_vec(),
            pq_signature: out_pq_sk.sign(&message).expect("ml-dsa sign"),
        }];
        assert!(
            !verify_hybrid_quorum_sigs(&outsider, &message, &members, &ml_dsa_roster, 1),
            "non-member hybrid signer must reject"
        );
    }

    // (Deleted) `forged_proof_bytes_fail_to_deserialize`: a `not(feature = "prover")`
    // V1-FLOOR test whose sole purpose was pinning the DREG-magic v1 `StarkProof` wire
    // format via the legacy hand-STARK `proof_from_bytes` gate. That hand-STARK engine and
    // its wire format are retired; forged-proof rejection is now covered by the
    // descriptor-IR2 verify path (`verify_vm_descriptor2`) and the `*_emit_gate` tests.

    // =====================================================================
    // MCP best-practices surface tests: annotations, structured content,
    // resources (incl. self-orientation), prompts, pagination, cap-gating.
    // =====================================================================

    #[test]
    fn every_tool_has_title_annotations_group_and_scope() {
        let defs = tool_definitions();
        assert!(defs.len() >= 40, "expected the full dregg toolset");
        for d in &defs {
            assert!(d.title.is_some(), "tool {} missing title", d.name);
            let ann = d.annotations.expect("annotations present");
            // read-only tools must NOT be flagged destructive.
            if ann.read_only_hint {
                assert!(
                    ann.destructive_hint != Some(true),
                    "read-only tool {} flagged destructive",
                    d.name
                );
            }
            // group + scope stamped into schema metadata for self-orientation.
            let schema = &d.input_schema;
            assert!(
                schema
                    .get("x-dregg-group")
                    .and_then(|v| v.as_str())
                    .is_some(),
                "tool {} missing x-dregg-group",
                d.name
            );
            assert!(
                schema
                    .get("x-dregg-scope")
                    .and_then(|v| v.as_str())
                    .is_some(),
                "tool {} missing x-dregg-scope",
                d.name
            );
            assert_ne!(tool_group(d.name), "other", "tool {} ungrouped", d.name);
        }
    }

    #[test]
    fn read_tools_are_read_only_and_idempotent() {
        let ann = tool_annotations("dregg_read_cell");
        assert!(ann.read_only_hint && ann.idempotent_hint);
        // a mutating, irreversible tool is marked destructive + not read-only.
        let revoke = tool_annotations("dregg_revoke_capability");
        assert!(!revoke.read_only_hint && revoke.destructive_hint == Some(true));
        // bridging reaches the open world.
        assert_eq!(
            tool_annotations("dregg_peer_exchange").open_world_hint,
            Some(true)
        );
    }

    /// The new query tools are wired end-to-end: registered (dispatch + defs +
    /// metadata) AND return the right shape against a real ledger.
    #[tokio::test]
    async fn list_cells_surfaces_the_agent_cell() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let agent_cell = {
            let s = state.read().await;
            hex_encode(agent_cell_of(&s.cclerk).as_bytes())
        };
        let result = dispatch_tool("dregg_list_cells", serde_json::json!({}), &state).await;
        let j = extract_json(&result);
        let cells = j["cells"].as_array().expect("cells array");
        assert!(
            cells
                .iter()
                .any(|c| c["cell_id"].as_str() == Some(agent_cell.as_str())),
            "list_cells must surface the in-ledger agent cell; got {cells:?}"
        );
        // The agent cell is an ordinary cell (not a trustline/channel/sovereign).
        let entry = cells
            .iter()
            .find(|c| c["cell_id"].as_str() == Some(agent_cell.as_str()))
            .unwrap();
        assert_eq!(entry["kind"].as_str(), Some("cell"));
    }

    #[tokio::test]
    async fn cap_graph_defaults_to_agent_cell_and_returns_edges_shape() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let agent_cell = {
            let s = state.read().await;
            hex_encode(agent_cell_of(&s.cclerk).as_bytes())
        };
        // No cell_id ⇒ the node's own agent cell.
        let result = dispatch_tool("dregg_get_cap_graph", serde_json::json!({}), &state).await;
        let j = extract_json(&result);
        assert_eq!(j["cell_id"].as_str(), Some(agent_cell.as_str()));
        assert_eq!(j["found"].as_bool(), Some(true));
        assert!(j["edges"].is_array(), "edges must be an array");
        assert!(j["edge_count"].is_u64(), "edge_count must be present");
    }

    /// A non-organ cell is correctly REFUSED by the organ-status tools (the
    /// self-authenticating VK check rejects it), with an actionable error.
    #[tokio::test]
    async fn trustline_status_rejects_a_plain_cell() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let agent_cell = {
            let s = state.read().await;
            hex_encode(agent_cell_of(&s.cclerk).as_bytes())
        };
        let result = dispatch_tool(
            "dregg_get_trustline_status",
            serde_json::json!({ "trustline_cell": agent_cell }),
            &state,
        )
        .await;
        assert_eq!(
            result.is_error,
            Some(true),
            "a plain agent cell is not a trustline and must be refused"
        );
        let sc = result.structured_content.expect("actionable error payload");
        assert!(sc.get("error").is_some() && sc.get("hint").is_some());
    }

    /// The four new read tools require only the `read` scope (never write/admin)
    /// — so an orienting agent can survey the world with a read-only cap.
    #[test]
    fn new_query_tools_are_read_scoped_and_grouped() {
        for t in [
            "dregg_list_cells",
            "dregg_get_cap_graph",
            "dregg_get_trustline_status",
            "dregg_get_channel_status",
        ] {
            assert_eq!(tool_required_scope(t), "read", "{t} must be read-scoped");
            assert_eq!(tool_group(t), "orient", "{t} must be in the orient group");
            assert!(tool_annotations(t).read_only_hint, "{t} must be read-only");
        }
    }

    #[test]
    fn structured_content_mirrors_json_results() {
        let v = serde_json::json!({ "a": 1, "b": "x" });
        let r = McpToolResult::json(&v);
        assert_eq!(r.structured_content.as_ref(), Some(&v));
        assert!(r.is_error.is_none());
        // actionable errors carry error+hint structure.
        let e = McpToolResult::actionable_error("boom", "do X");
        assert_eq!(e.is_error, Some(true));
        let sc = e.structured_content.expect("error has structured content");
        assert_eq!(sc.get("error").and_then(|v| v.as_str()), Some("boom"));
        assert_eq!(sc.get("hint").and_then(|v| v.as_str()), Some("do X"));
    }

    #[test]
    fn initialize_advertises_tools_resources_prompts() {
        let resp = handle_initialize(serde_json::json!(1));
        let v = serde_json::to_value(&resp).unwrap();
        let caps = &v["result"]["capabilities"];
        assert!(caps.get("tools").is_some());
        assert!(caps.get("resources").is_some());
        assert!(caps.get("prompts").is_some());
        assert!(
            caps.get("completions").is_some(),
            "must advertise completions"
        );
        assert_eq!(v["result"]["protocolVersion"], "2025-06-18");
        // Server-level orientation instructions point the agent at its
        // self-orientation surface on connect.
        let instr = v["result"]["instructions"].as_str().unwrap_or("");
        assert!(
            instr.contains("dregg://about") && instr.contains("_cap"),
            "instructions must orient the agent (about + ocap convention)"
        );
    }

    #[tokio::test]
    async fn tools_list_paginates() {
        // With enforcement OFF (default), the full catalog is visible, so
        // pagination pages the whole tool set. Follow cursors to the end and
        // confirm the union reconstructs every tool exactly once.
        let (state, _tmp) = fresh_unlocked_state().await;
        let mut collected: Vec<String> = Vec::new();
        let mut cursor: Option<String> = None;
        let mut pages = 0;
        loop {
            let params = match &cursor {
                Some(c) => serde_json::json!({ "cursor": c }),
                None => serde_json::json!({}),
            };
            let r = handle_tools_list(serde_json::json!(1), params, &state).await;
            let v = serde_json::to_value(&r).unwrap();
            let page = v["result"]["tools"].as_array().unwrap();
            assert!(
                page.len() <= MCP_PAGE_SIZE,
                "no page may exceed MCP_PAGE_SIZE"
            );
            for t in page {
                collected.push(t["name"].as_str().unwrap().to_string());
            }
            pages += 1;
            match v["result"]["nextCursor"].as_str() {
                Some(c) => cursor = Some(c.to_string()),
                None => break,
            }
            assert!(pages < 100, "pagination must terminate");
        }
        assert!(
            pages >= 2,
            "46 tools at page size 20 must span multiple pages"
        );
        assert_eq!(
            collected.len(),
            tool_definitions().len(),
            "paging through all cursors must yield every tool exactly once"
        );
    }

    /// The ontology resource exposes a self-consistent effect catalog: a
    /// non-empty effect list whose length matches the advertised `effect_count`.
    /// (The exact count is generator-owned — `ontology-catalog.generated.json` —
    /// so this pins the INVARIANT, not a magic number that drifts every time the
    /// kernel grows an effect.)
    #[tokio::test]
    async fn ontology_resource_effect_catalog_is_self_consistent() {
        let (state, _tmp) = fresh_unlocked_state().await;
        let resp = handle_resources_read(
            serde_json::json!(1),
            serde_json::json!({ "uri": "dregg://ontology" }),
            &state,
        )
        .await;
        let v = serde_json::to_value(&resp).unwrap();
        let text = v["result"]["contents"][0]["text"].as_str().unwrap();
        let catalog: Value = serde_json::from_str(text).unwrap();
        let effects = catalog["effects"].as_array().expect("effects array");
        assert!(
            !effects.is_empty(),
            "ontology must advertise at least one effect"
        );
        assert_eq!(
            catalog["effect_count"].as_u64(),
            Some(effects.len() as u64),
            "advertised effect_count must match the effects array length",
        );
    }

    #[tokio::test]
    async fn identity_and_cell_resources_resolve() {
        let (state, _tmp) = fresh_unlocked_state().await;
        // identity resource reflects the node's own agent cell.
        let id_resp = handle_resources_read(
            serde_json::json!(1),
            serde_json::json!({ "uri": "dregg://identity" }),
            &state,
        )
        .await;
        let idv = serde_json::to_value(&id_resp).unwrap();
        let text = idv["result"]["contents"][0]["text"].as_str().unwrap();
        let ident: Value = serde_json::from_str(text).unwrap();
        let cell_hex = ident["agent_cell_id"].as_str().unwrap().to_string();
        // templated cell resource reads that same cell.
        let cell_resp = handle_resources_read(
            serde_json::json!(2),
            serde_json::json!({ "uri": format!("dregg://cell/{cell_hex}") }),
            &state,
        )
        .await;
        let cellv = serde_json::to_value(&cell_resp).unwrap();
        let ctext = cellv["result"]["contents"][0]["text"].as_str().unwrap();
        let cell: Value = serde_json::from_str(ctext).unwrap();
        assert_eq!(cell["found"], true, "agent cell should exist in ledger");
    }

    #[test]
    fn prompts_list_and_get_render() {
        let list = handle_prompts_list(serde_json::json!(1));
        let lv = serde_json::to_value(&list).unwrap();
        let names: Vec<&str> = lv["result"]["prompts"]
            .as_array()
            .unwrap()
            .iter()
            .map(|p| p["name"].as_str().unwrap())
            .collect();
        assert!(names.contains(&"orient"));
        assert!(names.contains(&"delegate_capability"));
        // get renders a user message with the substituted arg.
        let get = handle_prompts_get(
            serde_json::json!(2),
            serde_json::json!({
                "name": "submit_turn",
                "arguments": { "intent": "transfer 5 to bob" }
            }),
        );
        let gv = serde_json::to_value(&get).unwrap();
        let msg = gv["result"]["messages"][0]["content"]["text"]
            .as_str()
            .unwrap();
        assert!(msg.contains("transfer 5 to bob"));
    }

    #[tokio::test]
    async fn cap_gating_rejects_uncovered_token_but_allows_read_when_unenforced() {
        let (state, _tmp) = fresh_unlocked_state().await;
        // Enforcement OFF (default in tests): missing _cap passes the gate.
        assert!(
            enforce_tool_cap("dregg_read_cell", &serde_json::json!({}), &state)
                .await
                .is_ok(),
            "missing cap should pass when enforcement is off (back-compat)"
        );
        // A garbage presented credential is ALWAYS verified and REJECTED,
        // even with enforcement off — the per-tool gate never trusts an
        // un-covering token.
        let bogus = serde_json::json!({ "_cap": { "biscuit": "eb2_not_a_real_biscuit" } });
        assert!(
            enforce_tool_cap("dregg_grant_capability", &bogus, &state)
                .await
                .is_err(),
            "a non-covering/garbage _cap must be rejected"
        );
    }

    /// Ratchet against the `valid_until: None` sentinel regrowing in an MCP handler.
    ///
    /// Every `Turn` these handlers build is executed by a real `TurnExecutor`
    /// (`mcp_execute`, `mcp_execute_via_producer`), whose expiration check is
    /// `if let Some(valid_until) = turn.valid_until { ... }` (`turn/src/executor/execute.rs`,
    /// around line 426) — entirely SKIPPED on `None`. A turn built that way never expires,
    /// no matter how stale. This was a real, repeated bug: found and fixed at three other
    /// call sites (the thin-HTTP `/turn/submit` path, the SDK's `runtime::default_valid_until`
    /// for issue #46, and `tool_submit_turn` itself, above in this same handler set) before
    /// this pass swept the remaining ones.
    ///
    /// `default_valid_until()` (`api.rs`) exists precisely so every one of these sites can
    /// share ONE horizon policy instead of re-deriving (or omitting) it. This test does not
    /// re-assert that function's own contract — `api::tests::
    /// default_valid_until_is_some_and_an_expired_stamp_is_still_rejected` already pins that
    /// `Some` alone is not enough, an *expired* stamp must still be rejected — it pins the
    /// narrower, source-level fact that regressed here: no handler literally spells out the
    /// sentinel again. `include_str!` reads each file at COMPILE time, so this cannot go stale
    /// against what actually ships; it fails the moment a `Turn { .. }` literal in any of these
    /// files is written with `valid_until: None,` again, by any author, in any handler added
    /// later to these same files.
    #[test]
    fn no_mcp_handler_rebuilds_the_unbounded_valid_until_sentinel() {
        let files: &[(&str, &str)] = &[
            ("handlers_act.rs", include_str!("handlers_act.rs")),
            ("handlers_delegate.rs", include_str!("handlers_delegate.rs")),
            ("handlers_apps.rs", include_str!("handlers_apps.rs")),
            ("handlers_privacy.rs", include_str!("handlers_privacy.rs")),
            ("handlers_verify.rs", include_str!("handlers_verify.rs")),
        ];
        for (name, src) in files {
            assert!(
                !src.contains("valid_until: None,"),
                "{name} builds a Turn with `valid_until: None` — this turn will NEVER expire \
                 (the executor's expiration check is skipped entirely on `None`, \
                 turn/src/executor/execute.rs:426). Use `crate::api::default_valid_until()` \
                 instead, as every other Turn literal in the mcp handlers now does."
            );
        }
    }
}
