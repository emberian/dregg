//! # guard — the ABUSE-AUDIT reactor (the reactive twin of `invoke()`, AX5).
//!
//! The fifth axis (AX5) of a modern starbridge-app. Where the [`crate::service`] face
//! is the **command** front-door (a `consume` turn comes *in*, subject-driven), this
//! is the **reaction** front-door: a service that WATCHES the account cell and, when a
//! subject `consume`s its metered quota, REACTS by emitting an on-chain audit record —
//! event-driven, the automated-signal feed the operator-review queue reads.
//!
//! In the prior imperative module this was the `automated:<signal>` reporter that
//! filed into the review queue. Here it is a genuine event→reaction: a
//! [`GuardAbuseReactor`] reads the new meter value off the observed `consume`'s
//! committed `SetField` and emits a `quota-consumption-logged` event linking the audit
//! record back to the consuming turn's receipt. The audit is produced REACTIVELY from
//! the committed consume, not by trusting the subject to self-report — the tamper-
//! evident abuse trail an operator reviews before a governance takedown.
//!
//! Both front-doors are **userspace**: there is NO kernel `Effect::React` (just as
//! there is no `Effect::Invoke`). The reaction desugars to an ordinary
//! [`Effect::EmitEvent`] the kernel already enforces and the circuit already witnesses,
//! re-enforced by the installed account caveats (the audit turn writes no slot, so the
//! `WriteOnce` / `Monotonic` / `FieldLteField` caveats hold vacuously — an audit can
//! never perturb the meter it records, nor move the standing it may inform).

use dregg_app_framework::{
    AuthRequired, Effect, Event, FieldElement, ObservedReceipt, ReactionPlan, Reactor,
    ReceiptFilter, symbol,
};
use dregg_types::CellId;

use crate::CONSUMED_SLOT;

/// The reaction op the abuse-audit reactor emits (not a member of the command
/// interface — it is the reactor's own downstream op): a `quota-consumption-logged`
/// audit receipt.
pub const REACTION_AUDIT: &str = "audit_consume";

/// The wire method the reactor watches — the metered `consume_quota` turn (the method
/// [`crate::build_consume_action`] and [`crate::fire_consume`] submit).
pub const WATCHED_METHOD: &str = "consume_quota";

/// **An abuse-audit reactor** — watches a subject-account cell for committed
/// `consume_quota` ops and reacts by emitting an on-chain `quota-consumption-logged`
/// audit event recording the new meter value and linking back to the consuming turn.
///
/// The reactive analogue of a [`crate::service::GuardService`] consumer: it DECLARES
/// its watch ([`ReceiptFilter`] over the account's `consume_quota` method) and how it
/// reacts ([`Reactor::react`] → an audit [`ReactionPlan`]); the framework wires the
/// match → cap-gate → build → sign.
#[derive(Clone, Debug)]
pub struct GuardAbuseReactor {
    /// The account cell this reactor watches (and writes the audit receipt to).
    pub account: CellId,
}

impl GuardAbuseReactor {
    /// An abuse-audit reactor watching the account cell `account`.
    pub fn new(account: CellId) -> Self {
        GuardAbuseReactor { account }
    }
}

impl Reactor for GuardAbuseReactor {
    fn filter(&self) -> ReceiptFilter {
        // What it watches: the account cell, for the `consume_quota` op.
        ReceiptFilter::cell_methods(self.account, &[WATCHED_METHOD])
    }

    fn react(&self, observed: &ObservedReceipt) -> Option<ReactionPlan> {
        // Decode the new meter value off the observed consume's committed effect — the
        // `SetField` on CONSUMED is the metered counter the subject just advanced.
        let mut new_consumed: Option<FieldElement> = None;
        for effect in &observed.effects {
            if let Effect::SetField { index, value, .. } = effect
                && *index == CONSUMED_SLOT as usize
            {
                new_consumed = Some(*value);
            }
        }
        // No metered advance in the observed op → nothing to audit.
        let consumed = new_consumed?;
        Some(ReactionPlan {
            target: self.account,
            method: REACTION_AUDIT.into(),
            args: vec![],
            // The reaction desugars to an ordinary EmitEvent — the kernel / circuit
            // see only what they already know. It writes no slot, so the account
            // program re-enforces it vacuously (the audit cannot perturb the meter it
            // records). The event links the new meter value to the consuming turn's
            // receipt (provenance).
            effects: vec![Effect::EmitEvent {
                cell: self.account,
                event: Event::new(
                    symbol("quota-consumption-logged"),
                    vec![consumed, observed.turn_hash],
                ),
            }],
            auth_required: AuthRequired::Signature,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{
        AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, InvokeAuthority, ReactRefused,
        field_from_u64, react_build,
    };

    use crate::{CEILING_SLOT, build_consume_action, guard_born_cell_program};

    /// Deploy a flat-program (method-agnostic `Always`) account with a granted ceiling,
    /// so both a metered `consume` and the slot-less audit reaction commit (the flat
    /// program has no `Cases` default-deny — the reactor's `audit_consume` method is
    /// not a dispatch case and would be default-denied on the `Cases` floor).
    fn deploy(seed: u8) -> (AppCipherclerk, EmbeddedExecutor, CellId) {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
        let executor = EmbeddedExecutor::new(&cclerk, "default");
        let account = cclerk.cell_id();
        executor.install_program(account, guard_born_cell_program());
        executor.with_ledger_mut(|ledger| {
            if let Some(c) = ledger.get_mut(&account) {
                c.state.set_field(CEILING_SLOT as usize, field_from_u64(4));
                c.state.set_field(CONSUMED_SLOT as usize, field_from_u64(0));
            }
        });
        (cclerk, executor, account)
    }

    #[test]
    fn an_on_chain_consume_drives_the_reactor_to_audit_log() {
        // THE END-TO-END event-driven loop: a committed `consume` → the reactor sees it
        // via the observed receipt → its audit reaction emits a
        // `quota-consumption-logged` turn, committed through the real executor.
        let (cclerk, executor, account) = deploy(0x01);

        // 1) A subject consumes: meter 0 → 1.
        let receipt = executor
            .submit_action(&cclerk, build_consume_action(&cclerk, account, 0))
            .expect("the consume commits (meter advances under the ceiling)");
        assert_eq!(
            executor.cell_state(account).unwrap().fields[CONSUMED_SLOT as usize],
            field_from_u64(1),
            "the consume advanced the meter to 1"
        );

        // 2) The reactor OBSERVES the consume and reacts with an audit log.
        let observed = ObservedReceipt {
            cell: account,
            method: symbol(WATCHED_METHOD),
            effects: vec![Effect::SetField {
                cell: account,
                index: CONSUMED_SLOT as usize,
                value: field_from_u64(1),
            }],
            turn_hash: receipt.turn_hash,
            signer: cclerk.public_key().0,
        };
        let reactor = GuardAbuseReactor::new(account);
        let audit = react_build(&cclerk, &reactor, &observed, InvokeAuthority::Signature)
            .expect("a Signature-holding reactor is authorized")
            .expect("a watched consume reacts");

        // 3) The audit reaction commits without perturbing the meter it records.
        executor
            .submit_turn(&audit)
            .expect("the audit-log reaction turn commits (writes no slot)");
        assert_eq!(
            executor.cell_state(account).unwrap().fields[CONSUMED_SLOT as usize],
            field_from_u64(1),
            "the audit did not perturb the meter it recorded"
        );
    }

    #[test]
    fn the_reactor_only_watches_consume() {
        let (cclerk, _executor, account) = deploy(0x02);
        let reactor = GuardAbuseReactor::new(account);

        // An observed `constitute` (not the watched `consume_quota`) → no reaction.
        let off = ObservedReceipt {
            cell: account,
            method: symbol("constitute"),
            effects: vec![],
            turn_hash: [0u8; 32],
            signer: cclerk.public_key().0,
        };
        assert!(matches!(
            react_build(&cclerk, &reactor, &off, InvokeAuthority::Signature),
            Ok(None)
        ));
    }

    #[test]
    fn the_reaction_is_cap_gated_fail_closed() {
        let (cclerk, _executor, account) = deploy(0x03);
        let reactor = GuardAbuseReactor::new(account);

        let observed = ObservedReceipt {
            cell: account,
            method: symbol(WATCHED_METHOD),
            effects: vec![Effect::SetField {
                cell: account,
                index: CONSUMED_SLOT as usize,
                value: field_from_u64(1),
            }],
            turn_hash: [7u8; 32],
            signer: cclerk.public_key().0,
        };

        // A None-authority reactor cannot satisfy the Signature-required audit reaction.
        let refused = react_build(&cclerk, &reactor, &observed, InvokeAuthority::None)
            .expect_err("None authority cannot satisfy a Signature reaction");
        assert!(matches!(refused, ReactRefused::Unauthorized { .. }));
    }
}
