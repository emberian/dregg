//! # `grain-verify-wasm` — the crown weld, IN THE RENTER'S BROWSER.
//!
//! *docs/THE-GRAIN.md face #1 (Unfoolable), build item #3: "surface the renter
//! verify in the renter's browser — the real WASM verifier."*
//!
//! A hosted agent hands the renter a [`grain_verify::GrainAttestation`] — the
//! cumulative, signed receipt chain of its session. This crate lets the renter
//! re-witness it **in a browser tab, offline, re-running nothing**. It is a thin
//! `#[wasm_bindgen]` shell over the whole LANDED ladder: it deserializes the
//! attestation and calls the REAL grain-verify verifier for whichever rungs the
//! renter's pins select — [`GrainAttestation::verify`] (R0),
//! [`GrainAttestation::verify_for_renter`] (+R1, when the renter anchor is
//! supplied), [`GrainAttestation::verify_r2`] /
//! [`GrainAttestation::verify_r2_for_renter`] (+R2, when the executor's
//! committed-turn manifest is supplied). It reimplements NO check — every tooth
//! (the composed `verify_agent_run` chain check, the headroom + per-step budget
//! teeth, the R1 anti-rewrite / anti-truncation anchor teeth, the R2 kernel-turn
//! link teeth) runs inside the same code the native verifier runs.
//!
//! ## What it checks — and what it does NOT (honest scope)
//!
//! A PASS means, given the renter's independently-pinned signer key: the shown
//! report was **not mutated in transit** (every receipt signed + ordered + linked
//! under one signer, nothing spliced / reordered / hidden), the agent consumed
//! **within budget** at every step, and the headroom bound is exact (R0). With a
//! renter anchor it ALSO means the host neither **rewrote** nor **truncated** the
//! history relative to what the renter countersigned — that slice IS
//! host-independent (R1). With a committed-turn manifest it ALSO means every
//! admitted receipt is a view over a turn the executor committed (R2 — which
//! still trusts the executor host that produced the manifest).
//!
//! It does NOT establish **execution integrity** — that each receipted turn
//! corresponds to a genuine kernel transition — nor **completeness** ("nothing
//! else"). That is R3, the whole-history STARK leg
//! ([`grain_verify::WHOLE_HISTORY_GAP`]), not yet welded. This page is the landed
//! R0/R1/R2 ladder, not yet unfoolability.

use grain_verify::GrainAttestation;
use serde::Serialize;

/// The machine-readable verdict a renter's browser renders. Serializes to the
/// `{ok, summary, error, ...}` JS object [`verify_attestation`] returns.
#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct VerifyOutcome {
    /// Did the attestation re-witness cleanly under the pinned signer (and, in
    /// renter mode, the renter anchor; in kernel-linked mode, the R2 links)?
    pub ok: bool,
    /// Which rungs ran: `"tamper-evidence (R0)"`, `"renter-anchored (R0+R1)"`,
    /// `"kernel-linked (R0+R2)"`, or `"renter-anchored + kernel-linked (R0+R1+R2)"`.
    pub mode: String,
    /// A one-line human summary of what the renter learned (present iff `ok`).
    pub summary: Option<String>,
    /// A one-line human error (present iff `!ok`).
    pub error: Option<String>,
    /// The agent id whose session this was (iff `ok`).
    pub agent: Option<String>,
    /// Admitted actions re-witnessed (== receipt count) (iff `ok`).
    pub actions: Option<usize>,
    /// Budget consumed across the whole session (iff `ok`).
    pub consumed: Option<i64>,
    /// The budget ceiling (iff `ok`).
    pub budget: Option<i64>,
    /// Un-drawn headroom, `budget − consumed` (iff `ok`).
    pub headroom: Option<i64>,
    /// The signer key this verdict is anchored to, lowercase hex (iff `ok`).
    pub signer_hex: Option<String>,
    /// The chain tip — the 32-byte commitment to the whole session, hex (iff `ok`).
    pub tip_hex: Option<String>,
    /// Whether a renter anchor (pubkey + genesis nonce) was supplied and checked.
    pub renter_anchored: bool,
    /// In renter mode, whether the R1 anti-rewrite + anti-truncation teeth passed
    /// (always `Some(true)` on an `ok` renter-anchored verdict; `None` otherwise).
    pub anti_rewrite_anti_truncation: Option<bool>,
    /// In kernel-linked (R2) mode: how many admitted receipts were confirmed as
    /// views over turns in the supplied committed-turn manifest (iff `ok` with a
    /// manifest supplied; `None` otherwise).
    pub r2_linked: Option<usize>,
}

impl VerifyOutcome {
    fn failure(mode: &str, renter_anchored: bool, error: String) -> VerifyOutcome {
        VerifyOutcome {
            ok: false,
            mode: mode.to_string(),
            summary: None,
            error: Some(error),
            agent: None,
            actions: None,
            consumed: None,
            budget: None,
            headroom: None,
            signer_hex: None,
            tip_hex: None,
            renter_anchored,
            anti_rewrite_anti_truncation: None,
            r2_linked: None,
        }
    }
}

fn hex32(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

/// Parse a 32-byte lowercase/uppercase hex string (optionally `0x`-prefixed).
fn parse_hex32(label: &str, s: &str) -> Result<[u8; 32], String> {
    let cleaned = s.trim().trim_start_matches("0x");
    let raw = hex::decode(cleaned).map_err(|e| format!("{label}: not valid hex ({e})"))?;
    if raw.len() != 32 {
        return Err(format!(
            "{label}: expected 32 bytes (64 hex chars), got {} bytes",
            raw.len()
        ));
    }
    let mut out = [0u8; 32];
    out.copy_from_slice(&raw);
    Ok(out)
}

/// Treat empty / whitespace-only optional inputs as absent (a browser form
/// hands `""` for a blank field).
fn nonempty(s: Option<String>) -> Option<String> {
    s.and_then(|v| {
        let t = v.trim();
        if t.is_empty() {
            None
        } else {
            Some(t.to_string())
        }
    })
}

/// **The core renter check — pure, native-testable, no JS.** Deserializes the
/// attestation and calls the REAL grain-verify verifier. Returns a
/// [`VerifyOutcome`] instead of ever panicking, so a browser renders a verdict
/// on any input.
///
/// - `attestation_json` — the `GrainAttestation` the host handed back.
/// - `signer_hex` — the renter's out-of-band-pinned receipt-chain signer key (the
///   VK-anchor analogue). A valid chain by the WRONG key is refused.
/// - `renter_pubkey_hex` / `genesis_nonce_hex` — the R1 renter anchor. Supply
///   BOTH to run the R1 anti-rewrite + anti-truncation teeth (relative to a
///   renter-countersigned checkpoint); supply NEITHER to skip the rung. Supplying
///   exactly one is an error (an incomplete anchor).
/// - `committed_turns_json` — the R2 committed-turn manifest: a JSON array of
///   64-hex turn hashes the executor host committed for this session. When
///   supplied, every admitted receipt must be a VIEW over one of them
///   ([`GrainAttestation::verify_r2`] / `verify_r2_for_renter`).
pub fn verify_core(
    attestation_json: &str,
    signer_hex: &str,
    renter_pubkey_hex: Option<String>,
    genesis_nonce_hex: Option<String>,
    committed_turns_json: Option<String>,
) -> VerifyOutcome {
    let renter_pubkey_hex = nonempty(renter_pubkey_hex);
    let genesis_nonce_hex = nonempty(genesis_nonce_hex);
    let committed_turns_json = nonempty(committed_turns_json);
    let renter_mode = renter_pubkey_hex.is_some() || genesis_nonce_hex.is_some();
    let r2_mode = committed_turns_json.is_some();
    let mode = match (renter_mode, r2_mode) {
        (false, false) => "tamper-evidence (R0)",
        (true, false) => "renter-anchored (R0+R1)",
        (false, true) => "kernel-linked (R0+R2)",
        (true, true) => "renter-anchored + kernel-linked (R0+R1+R2)",
    };

    // Pinned signer (the trust anchor). Meaningful verification requires it.
    let pinned_signer = match parse_hex32("pinned signer", signer_hex) {
        Ok(s) => s,
        Err(e) => return VerifyOutcome::failure(mode, renter_mode, e),
    };

    // Deserialize the artifact the host handed back.
    let att: GrainAttestation = match serde_json::from_str(attestation_json) {
        Ok(a) => a,
        Err(e) => {
            return VerifyOutcome::failure(
                mode,
                renter_mode,
                format!("could not parse the attestation JSON: {e}"),
            );
        }
    };

    // Pin the signer (the VK-anchor analogue) BEFORE re-witnessing: a valid chain
    // by a key the host minted is refused. Mirrors verify_against_signer, and
    // composes with verify_for_renter (which does not itself pin the signer).
    if att.signer() != pinned_signer {
        return VerifyOutcome::failure(
            mode,
            renter_mode,
            format!(
                "the chain signer {} is not the renter's pinned key {} — wrong authority",
                hex32(&att.signer()),
                hex32(&pinned_signer)
            ),
        );
    }

    // R2 manifest: a JSON array of 64-hex committed turn hashes.
    let manifest: Option<Vec<[u8; 32]>> = match committed_turns_json {
        None => None,
        Some(json) => {
            let raw: Vec<String> = match serde_json::from_str(&json) {
                Ok(v) => v,
                Err(e) => {
                    return VerifyOutcome::failure(
                        mode,
                        renter_mode,
                        format!(
                            "could not parse the committed-turn manifest (expected a JSON array of 64-hex turn hashes): {e}"
                        ),
                    );
                }
            };
            let mut turns = Vec::with_capacity(raw.len());
            for (i, h) in raw.iter().enumerate() {
                match parse_hex32(&format!("committed turn #{i}"), h) {
                    Ok(t) => turns.push(t),
                    Err(e) => return VerifyOutcome::failure(mode, renter_mode, e),
                }
            }
            Some(turns)
        }
    };

    // Renter-anchored path: BOTH the renter pubkey and the genesis nonce are
    // required (an incomplete anchor is a user error, not a silent downgrade).
    let anchor: Option<([u8; 32], [u8; 32])> = if renter_mode {
        let (pk_hex, nonce_hex) = match (renter_pubkey_hex, genesis_nonce_hex) {
            (Some(pk), Some(n)) => (pk, n),
            (Some(_), None) => {
                return VerifyOutcome::failure(
                    mode,
                    true,
                    "renter-anchored verify needs the genesis nonce too (you gave the renter pubkey but not the nonce)".to_string(),
                );
            }
            (None, Some(_)) => {
                return VerifyOutcome::failure(
                    mode,
                    true,
                    "renter-anchored verify needs the renter pubkey too (you gave the genesis nonce but not the pubkey)".to_string(),
                );
            }
            (None, None) => unreachable!("renter_mode implies at least one is Some"),
        };
        let renter_pubkey = match parse_hex32("renter pubkey", &pk_hex) {
            Ok(v) => v,
            Err(e) => return VerifyOutcome::failure(mode, true, e),
        };
        let genesis_nonce = match parse_hex32("genesis nonce", &nonce_hex) {
            Ok(v) => v,
            Err(e) => return VerifyOutcome::failure(mode, true, e),
        };
        Some((renter_pubkey, genesis_nonce))
    } else {
        None
    };

    // Dispatch the ladder: whichever rungs the pins select, each including all
    // rungs below it (the REAL grain-verify composition, nothing reimplemented).
    let verified: Result<(grain_verify::GrainVerified, Option<usize>), _> =
        match (&anchor, &manifest) {
            (None, None) => att.verify().map(|v| (v, None)),
            (Some((pk, nonce)), None) => att.verify_for_renter(pk, nonce).map(|v| (v, None)),
            (None, Some(turns)) => att.verify_r2(turns).map(|r| (r.base, Some(r.linked))),
            (Some((pk, nonce)), Some(turns)) => att
                .verify_r2_for_renter(pk, nonce, turns)
                .map(|r| (r.base, Some(r.linked))),
        };

    match verified {
        Ok((v, r2_linked)) => VerifyOutcome {
            ok: true,
            mode: mode.to_string(),
            summary: Some(v.summary()),
            error: None,
            agent: Some(v.agent.clone()),
            actions: Some(v.actions),
            consumed: Some(v.consumed),
            budget: Some(v.budget),
            headroom: Some(v.headroom),
            signer_hex: Some(hex32(&v.signer)),
            tip_hex: v.tip.as_ref().map(hex32),
            renter_anchored: renter_mode,
            anti_rewrite_anti_truncation: if renter_mode { Some(true) } else { None },
            r2_linked,
        },
        Err(e) => VerifyOutcome::failure(mode, renter_mode, e.to_string()),
    }
}

/// **The browser entry point.** Deserializes a `GrainAttestation` and calls the
/// REAL grain-verify verifier, returning a JS object
/// `{ok, mode, summary, error, agent, actions, consumed, budget, headroom,
/// signer_hex, tip_hex, renter_anchored, anti_rewrite_anti_truncation, r2_linked}`.
///
/// Supply `renter_pubkey_hex` + `genesis_nonce_hex` (both, or neither) to run the
/// R1 anti-rewrite / anti-truncation anchor teeth, and/or `committed_turns_json`
/// (a JSON array of 64-hex committed turn hashes) to run the R2 kernel-turn link
/// teeth. Each supplied rung composes with all rungs below it; with nothing
/// optional supplied, the base R0 tamper-evidence check runs.
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen::prelude::wasm_bindgen]
pub fn verify_attestation(
    attestation_json: &str,
    signer_hex: &str,
    renter_pubkey_hex: Option<String>,
    genesis_nonce_hex: Option<String>,
    committed_turns_json: Option<String>,
) -> wasm_bindgen::JsValue {
    let outcome = verify_core(
        attestation_json,
        signer_hex,
        renter_pubkey_hex,
        genesis_nonce_hex,
        committed_turns_json,
    );
    serde_wasm_bindgen::to_value(&outcome).unwrap_or(wasm_bindgen::JsValue::NULL)
}

/// The honest-boundary text the browser page renders (what this verifier does
/// NOT yet prove). Re-exported so the page has one source of truth.
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen::prelude::wasm_bindgen]
pub fn whole_history_gap() -> String {
    grain_verify::WHOLE_HISTORY_GAP.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_agent::agent::{AgentAction, AgentSpec, PlannedBrain, ToolCall};
    use dregg_agent::session::Session;
    use dregg_agent::toolkit::Toolkit;
    use dregg_agent::tools::{OperatorTools, ShellOut};
    use grain_verify::{GenesisPin, countersign_checkpoint};
    use std::path::Path;

    fn echo_toolkit(wd: &Path) -> OperatorTools {
        OperatorTools::new(Toolkit::new(), wd).with_shell(|cmd: &str, _cwd: &Path| {
            Ok(ShellOut {
                exit: 0,
                stdout: format!("ran: {cmd}"),
                stderr: String::new(),
                new_cwd: None,
            })
        })
    }

    fn shell_plan(cmds: &[&str]) -> PlannedBrain {
        PlannedBrain::new(
            cmds.iter()
                .map(|c| {
                    AgentAction::Op(ToolCall::new("shell", [("cmd".to_string(), c.to_string())]))
                })
                .collect(),
        )
    }

    fn wd() -> std::path::PathBuf {
        let p = std::env::temp_dir().join(format!(
            "grain-verify-wasm-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&p).unwrap();
        p
    }

    fn driven_session(seed: [u8; 32], budget: i64) -> (Session, std::path::PathBuf) {
        let dir = wd();
        let tk = echo_toolkit(&dir);
        let spec = AgentSpec::new("ignored", budget).with_shell();
        let mut sess = Session::open_seeded(seed, "dga1_renter", spec).unwrap();
        sess.run_goal("goal one", &mut shell_plan(&["a", "b"]), &tk);
        sess.run_goal("goal two", &mut shell_plan(&["c", "d", "e"]), &tk);
        (sess, dir)
    }

    fn hex(b: &[u8; 32]) -> String {
        super::hex32(b)
    }

    // ── AGREEMENT: the wasm core AGREES with native grain-verify on a genuine
    //    attestation (PASS) ────────────────────────────────────────────────────
    #[test]
    fn core_agrees_with_native_on_a_genuine_attestation() {
        let (sess, dir) = driven_session([1u8; 32], 20);
        let att = GrainAttestation::attest(&sess);
        let native = att.verify().expect("native verifies the genuine chain");

        let json = serde_json::to_string(&att).unwrap();
        let out = verify_core(&json, &hex(&att.signer()), None, None, None);

        assert!(out.ok, "wasm core agrees: PASS");
        assert_eq!(out.actions, Some(native.actions));
        assert_eq!(out.consumed, Some(native.consumed));
        assert_eq!(out.budget, Some(native.budget));
        assert_eq!(out.headroom, Some(native.headroom));
        assert_eq!(out.signer_hex, Some(hex(&native.signer)));
        assert_eq!(out.agent.as_deref(), Some(native.agent.as_str()));
        assert!(!out.renter_anchored);

        std::fs::remove_dir_all(&dir).ok();
    }

    // ── AGREEMENT: the wasm core AGREES with native on a TAMPERED attestation
    //    (FAIL, and the SAME rejection) ─────────────────────────────────────────
    #[test]
    fn core_agrees_with_native_on_a_tampered_attestation() {
        let (sess, dir) = driven_session([2u8; 32], 20);
        let mut att = GrainAttestation::attest(&sess);
        // Forge what an action was → the signed body no longer matches.
        att.report.receipts[0].action = "shell:forged-i-never-ran-this".into();

        let native_err = att.verify().expect_err("native rejects the tamper");
        let json = serde_json::to_string(&att).unwrap();
        let out = verify_core(&json, &hex(&att.signer()), None, None, None);

        assert!(!out.ok, "wasm core agrees: FAIL");
        assert_eq!(
            out.error.as_deref(),
            Some(native_err.to_string().as_str()),
            "same human rejection as native"
        );

        std::fs::remove_dir_all(&dir).ok();
    }

    // ── PIN: a valid chain under the WRONG pinned signer is refused ────────────
    #[test]
    fn wrong_pinned_signer_is_refused() {
        let (sess, dir) = driven_session([3u8; 32], 20);
        let att = GrainAttestation::attest(&sess);
        let json = serde_json::to_string(&att).unwrap();

        let wrong = [0xABu8; 32];
        let out = verify_core(&json, &hex(&wrong), None, None, None);
        assert!(!out.ok);
        assert!(out.error.unwrap().contains("wrong authority"));

        std::fs::remove_dir_all(&dir).ok();
    }

    // ── R1: a genuine renter-anchored extension PASSES through verify_for_renter ─
    #[test]
    fn renter_anchored_genuine_extension_passes() {
        let dir = wd();
        let tk = echo_toolkit(&dir);
        let spec = AgentSpec::new("ignored", 40).with_shell();
        let mut sess = Session::open_seeded([21u8; 32], "dga1_renter", spec).unwrap();
        sess.run_goal("goal one", &mut shell_plan(&["a", "b"]), &tk);

        let early = GrainAttestation::attest(&sess);
        let cp = early
            .checkpoint_to_countersign()
            .expect("2-turn checkpoint");
        let renter_seed = [0x5au8; 32];
        let renter_nonce = [0x11u8; 32];
        let cs = countersign_checkpoint(renter_seed, cp);
        let renter_pub = cs.renter_pubkey;

        sess.run_goal("goal two", &mut shell_plan(&["c", "d", "e"]), &tk);
        let signer = GrainAttestation::attest(&sess).signer();
        let att = GrainAttestation::attest(&sess)
            .with_genesis(GenesisPin {
                renter_nonce,
                signer,
            })
            .with_checkpoint(cs);

        // native truth
        att.verify_for_renter(&renter_pub, &renter_nonce)
            .expect("native renter check passes");

        // wasm core agrees
        let json = serde_json::to_string(&att).unwrap();
        let out = verify_core(
            &json,
            &hex(&signer),
            Some(hex(&renter_pub)),
            Some(hex(&renter_nonce)),
            None,
        );
        assert!(out.ok, "renter-anchored PASS: {:?}", out.error);
        assert!(out.renter_anchored);
        assert_eq!(out.anti_rewrite_anti_truncation, Some(true));
        assert_eq!(out.mode, "renter-anchored (R0+R1)");

        std::fs::remove_dir_all(&dir).ok();
    }

    // ── R1: an incomplete anchor (pubkey without nonce) is a clear error ───────
    #[test]
    fn incomplete_anchor_is_rejected() {
        let (sess, dir) = driven_session([4u8; 32], 20);
        let att = GrainAttestation::attest(&sess);
        let json = serde_json::to_string(&att).unwrap();

        let out = verify_core(
            &json,
            &hex(&att.signer()),
            Some(hex(&[0x22u8; 32])),
            None,
            None,
        );
        assert!(!out.ok);
        assert!(out.renter_anchored);
        assert!(out.error.unwrap().contains("genesis nonce"));

        std::fs::remove_dir_all(&dir).ok();
    }

    // ── ROBUSTNESS: malformed inputs return a verdict, never panic ─────────────
    #[test]
    fn malformed_inputs_return_a_verdict() {
        let bad_json = verify_core("{not json", &"11".repeat(32), None, None, None);
        assert!(!bad_json.ok);
        assert!(bad_json.error.unwrap().contains("parse"));

        let bad_signer = verify_core("{}", "xyz", None, None, None);
        assert!(!bad_signer.ok);
        assert!(bad_signer.error.unwrap().contains("signer"));
    }

    // ── R2: the kernel-linked mode AGREES with native verify_r2, both polarities ─
    #[test]
    fn r2_kernel_linked_mode_agrees_with_native() {
        use dregg_agent::agent::SyntheticMinter;

        // A minted session: every admitted receipt links a committed turn.
        let dir = wd();
        let tk = echo_toolkit(&dir);
        let spec = AgentSpec::new("ignored", 20).with_shell();
        let mut sess = Session::open_seeded([5u8; 32], "dga1_renter", spec).unwrap();
        let mut minter = SyntheticMinter::new();
        sess.run_goal_minted(
            "goal",
            &mut shell_plan(&["a", "b", "c"]),
            &tk,
            Some(&mut minter),
        );
        let att = GrainAttestation::attest(&sess);
        let json = serde_json::to_string(&att).unwrap();
        let manifest_hex: Vec<String> = minter.committed_turns().iter().map(hex).collect();
        let manifest_json = serde_json::to_string(&manifest_hex).unwrap();

        // native truth
        let native = att
            .verify_r2(minter.committed_turns())
            .expect("native R2 passes");

        // PASS: the wasm core agrees, r2_linked matches, the mode names the rungs.
        let out = verify_core(&json, &hex(&att.signer()), None, None, Some(manifest_json));
        assert!(out.ok, "kernel-linked PASS: {:?}", out.error);
        assert_eq!(out.mode, "kernel-linked (R0+R2)");
        assert_eq!(out.r2_linked, Some(native.linked));
        assert_eq!(out.r2_linked, Some(3));
        assert!(!out.renter_anchored);

        // FAIL: a manifest that vouches for nothing → the same rejection as native.
        let native_err = att.verify_r2(&[]).expect_err("native rejects");
        let out_empty = verify_core(&json, &hex(&att.signer()), None, None, Some("[]".into()));
        assert!(!out_empty.ok);
        assert_eq!(
            out_empty.error.as_deref(),
            Some(native_err.to_string().as_str()),
            "same human rejection as native"
        );

        // FAIL: an UNMINTED session against any manifest — no receipt has a link.
        let (bare, dir2) = driven_session([6u8; 32], 20);
        let bare_att = GrainAttestation::attest(&bare);
        let bare_json = serde_json::to_string(&bare_att).unwrap();
        let out_bare = verify_core(
            &bare_json,
            &hex(&bare_att.signer()),
            None,
            None,
            Some("[]".into()),
        );
        assert!(!out_bare.ok);
        assert!(
            out_bare.error.as_deref().unwrap().contains("R2"),
            "the R2 tooth names itself: {:?}",
            out_bare.error
        );

        // FAIL: a malformed manifest is a clear input error, not a panic.
        let out_bad = verify_core(&json, &hex(&att.signer()), None, None, Some("{nope".into()));
        assert!(!out_bad.ok);
        assert!(out_bad.error.unwrap().contains("committed-turn manifest"));

        std::fs::remove_dir_all(&dir).ok();
        std::fs::remove_dir_all(&dir2).ok();
    }

    // ── R2+R1: the FULL landed ladder in the browser core ──────────────────────
    #[test]
    fn full_ladder_mode_composes_r1_and_r2() {
        use dregg_agent::agent::SyntheticMinter;
        use grain_verify::countersign_checkpoint;

        let dir = wd();
        let tk = echo_toolkit(&dir);
        let spec = AgentSpec::new("ignored", 40).with_shell();
        let mut sess = Session::open_seeded([7u8; 32], "dga1_renter", spec).unwrap();
        let mut minter = SyntheticMinter::new();
        sess.run_goal_minted("goal", &mut shell_plan(&["a", "b"]), &tk, Some(&mut minter));

        let base = GrainAttestation::attest(&sess);
        let cp = base.checkpoint_to_countersign().unwrap();
        let renter_seed = [0x5au8; 32];
        let renter_nonce = [0x11u8; 32];
        let cs = countersign_checkpoint(renter_seed, cp);
        let renter_pub = cs.renter_pubkey;
        let att = base
            .clone()
            .with_genesis(GenesisPin {
                renter_nonce,
                signer: base.signer(),
            })
            .with_checkpoint(cs);
        let json = serde_json::to_string(&att).unwrap();
        let manifest_hex: Vec<String> = minter.committed_turns().iter().map(hex).collect();
        let manifest_json = serde_json::to_string(&manifest_hex).unwrap();

        let out = verify_core(
            &json,
            &hex(&att.signer()),
            Some(hex(&renter_pub)),
            Some(hex(&renter_nonce)),
            Some(manifest_json),
        );
        assert!(out.ok, "full ladder PASS: {:?}", out.error);
        assert_eq!(out.mode, "renter-anchored + kernel-linked (R0+R1+R2)");
        assert!(out.renter_anchored);
        assert_eq!(out.anti_rewrite_anti_truncation, Some(true));
        assert_eq!(out.r2_linked, Some(2));

        std::fs::remove_dir_all(&dir).ok();
    }
}
