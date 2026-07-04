//! **Hatchery genesis-agent** — an agent that mints bounded sub-agents (docs/THE-GRAIN.md
//! §Commons: "a genesis-agent mints bounded sub-agents via the hatchery").
//!
//! A [`GenesisAgent`] holds two authorities: a **mint authority** (it can define new
//! verified cell-kinds) and a **powerbox root** (it holds a cap bundle it can attenuate
//! and hand down). It mints a [`HatchedSubAgent`] by pairing them:
//!
//! 1. **A forever-invariant, executor-enforced.** The kind is a
//!    [`dregg_sdk::hatchery_mint::MintedKind`]: the declared [`Invariant`] (e.g.
//!    "spend-rate never exceeds R") is baked into a `FactoryDescriptor`'s
//!    `state_constraints`, which the executor re-evaluates on *every* turn of the child
//!    for its whole life. [`HatchedSubAgent::evaluate_transition`] delegates straight to
//!    that kernel gate — a conforming turn is admitted, a violating turn is refused with
//!    a genuine `ConstraintViolated`. Enforcement is the kernel's, not this module's.
//! 2. **Caps that are a strict attenuation.** The child is endowed with an *attenuation*
//!    of the genesis agent's own cap bundle, minted on the real `dga1_` powerbox rail
//!    ([`sandstorm_bridge::HostAuthority`] → [`sandstorm_bridge::attenuate_grain_cap`]).
//!    The rail is attenuate-only by construction (a caveat chain only narrows), so the
//!    child can never hold a facet the parent lacks; [`GenesisAgent::granted_permissions`]
//!    reads back the *cryptographically* derived facet set to prove it.
//!
//! Both are composed, not reimplemented: the invariant machinery is the breadstuffs
//! Hatchery (Lean-backed — `metatheory/Dregg2/Deos/Hatchery.lean`), and the cap rail is
//! the real ed25519 credential chain.

pub use dregg_sdk::hatchery_mint::{HpresProof, Invariant, MintedKind};
use sandstorm_bridge::{attenuate_grain_cap, derive_permissions, HostAuthority};

/// An agent that holds a hatchery cap and mints bounded sub-agents.
pub struct GenesisAgent {
    /// The genesis agent's own grain cell id (the subject caps are sealed to).
    pub cell_id: String,
    /// The mint-authority seed — seeds each [`MintedKind`]'s factory VK (distinct
    /// authorities minting the same invariant produce distinct factories but the same
    /// enforced child invariant).
    mint_authority: [u8; 32],
    /// The powerbox root the genesis agent mints/attenuates its caps under.
    host: HostAuthority,
    /// The genesis agent's **own cap bundle** — the universe a sub-agent's caps must
    /// attenuate within. A sub-agent can never be granted a facet outside this set.
    facets: Vec<String>,
}

/// A sub-agent hatched by a [`GenesisAgent`] — a bounded child with a forever-invariant
/// and a strictly-attenuated cap bundle.
#[derive(Clone, Debug)]
pub struct HatchedSubAgent {
    /// The child grain cell id.
    pub cell_id: String,
    /// The subject the child's cap is sealed to (only it can present the cap).
    pub subject: String,
    /// The minted kind — the forever-invariant, baked into a `FactoryDescriptor` the
    /// executor enforces on every turn of this child's life.
    pub kind: MintedKind,
    /// The child's `dga1_` capability token (an attenuation of the genesis agent's cap
    /// bundle, sealed to `subject`, rooted at the genesis agent's powerbox).
    pub cap_token: String,
    /// The facets the child was endowed with (a subset of the genesis agent's bundle).
    pub granted_facets: Vec<String>,
    /// The genesis agent's full bundle at mint time (for the strict-attenuation check).
    pub parent_facets: Vec<String>,
}

impl HatchedSubAgent {
    /// **Enforce the child's forever-invariant on one transition** — the genuine kernel
    /// gate. A conforming transition returns `Ok(())`; a violating one returns
    /// `Err(ConstraintViolated)`, reproduced bit-for-bit by any re-executing validator.
    pub fn evaluate_transition(
        &self,
        new_state: &dregg_cell::CellState,
        old_state: Option<&dregg_cell::CellState>,
    ) -> Result<(), dregg_cell::ProgramError> {
        self.kind.evaluate_transition(new_state, old_state)
    }

    /// The content-addressed kind id — the invariant digest a registry listing pins so a
    /// renter can check the sub-agent carries the invariant it advertises.
    pub fn kind_id(&self) -> [u8; 32] {
        self.kind.kind_id()
    }

    /// Whether the child's grant is a **strict** attenuation of the parent's bundle: every
    /// child facet is in the parent bundle, and at least one parent facet was dropped.
    pub fn is_strict_attenuation(&self) -> bool {
        let all_within = self
            .granted_facets
            .iter()
            .all(|f| self.parent_facets.contains(f));
        let strictly_fewer = self
            .parent_facets
            .iter()
            .any(|f| !self.granted_facets.contains(f));
        all_within && strictly_fewer
    }
}

/// Why hatching a sub-agent was refused.
#[derive(Debug, PartialEq, Eq)]
pub enum HatchError {
    /// A requested child facet is outside the genesis agent's own cap bundle — that would
    /// be amplification, not attenuation. Refused (the powerbox rail could not mint it
    /// either; this is the fail-fast gate before the crypto).
    NotAttenuation { facet: String },
}

impl std::fmt::Display for HatchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HatchError::NotAttenuation { facet } => write!(
                f,
                "cannot endow sub-agent with facet '{facet}' outside the genesis agent's bundle"
            ),
        }
    }
}
impl std::error::Error for HatchError {}

impl GenesisAgent {
    /// A genesis agent with a mint-authority seed, a powerbox-root seed, and its own cap
    /// bundle (the universe sub-agents attenuate within).
    pub fn new(
        cell_id: impl Into<String>,
        mint_authority: [u8; 32],
        powerbox_seed: [u8; 32],
        facets: impl IntoIterator<Item = impl Into<String>>,
    ) -> Self {
        GenesisAgent {
            cell_id: cell_id.into(),
            mint_authority,
            host: HostAuthority::from_seed(powerbox_seed),
            facets: facets.into_iter().map(Into::into).collect(),
        }
    }

    /// The genesis agent's own cap bundle.
    pub fn facets(&self) -> &[String] {
        &self.facets
    }

    /// **Mint a bounded sub-agent.** Bakes `invariant` into a forever-enforced kind and
    /// endows the child with a strict attenuation of this agent's cap bundle down to
    /// `child_facets`, sealed to `subject`. Refuses any `child_facets` entry outside the
    /// genesis agent's bundle (amplification).
    pub fn mint_subagent(
        &self,
        child_cell_id: impl Into<String>,
        subject: impl Into<String>,
        invariant: Invariant,
        child_facets: impl IntoIterator<Item = impl Into<String>>,
    ) -> Result<HatchedSubAgent, HatchError> {
        let child_cell_id = child_cell_id.into();
        let subject = subject.into();
        let child_facets: Vec<String> = child_facets.into_iter().map(Into::into).collect();

        // Fail-fast gate: no child facet may lie outside the parent bundle.
        for f in &child_facets {
            if !self.facets.contains(f) {
                return Err(HatchError::NotAttenuation { facet: f.clone() });
            }
        }

        // 1. The forever-invariant kind (executor-enforced for the child's whole life).
        let kind = MintedKind::mint(invariant, &self.mint_authority);

        // 2. The cap: mint the genesis bundle over the child cell (sealed to subject),
        //    then ATTENUATE it to the child's facets on the real dga1_ rail. The chain is
        //    attenuate-only, so the token can never confer a facet outside the bundle.
        let parent_refs: Vec<&str> = self.facets.iter().map(String::as_str).collect();
        let child_refs: Vec<&str> = child_facets.iter().map(String::as_str).collect();
        let parent_cap = self
            .host
            .mint_grain_cap(&child_cell_id, &subject, &parent_refs, None);
        let child_cap = attenuate_grain_cap(parent_cap, &child_refs, None);
        let cap_token = child_cap.encode();

        Ok(HatchedSubAgent {
            cell_id: child_cell_id,
            subject,
            kind,
            cap_token,
            granted_facets: child_facets,
            parent_facets: self.facets.clone(),
        })
    }

    /// Read back the facets a hatched sub-agent's cap **cryptographically** confers, right
    /// now — the real-rail derive (verifies the ed25519 chain under this agent's powerbox
    /// root, binds the grain/subject context, and returns the facets the caveat lattice
    /// admits). The returned set is exactly the child's grant; a facet the parent dropped
    /// is provably absent (the rail intersects every `cap` caveat in the chain).
    pub fn granted_permissions(&self, sub: &HatchedSubAgent, now: u64) -> Vec<String> {
        // The declared universe to test against = the parent bundle (nothing outside it
        // could ever be granted anyway).
        derive_permissions(
            &sub.cap_token,
            &self.host.public(),
            &sub.cell_id,
            &sub.subject,
            &self.facets,
            now,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::ProgramError;
    use dregg_sdk::hatchery_mint::state_with_slot;

    const MINT_AUTH: [u8; 32] = [7u8; 32];
    const PB_SEED: [u8; 32] = [42u8; 32];
    const SPEND_SLOT: u8 = 0;

    fn genesis() -> GenesisAgent {
        // A genesis agent holding four tool facets.
        GenesisAgent::new(
            "cell:genesis",
            MINT_AUTH,
            PB_SEED,
            ["web.fetch", "web.search", "notes.write", "pay.send"],
        )
    }

    #[test]
    fn a_hatched_subagent_enforces_its_forever_invariant() {
        let g = genesis();
        // The sub-agent's forever-invariant: its spend slot never drops below 0
        // (a spend-cap floor — the "spend-rate <= R" family's shape).
        let sub = g
            .mint_subagent(
                "cell:sub-1",
                "u:sub-1",
                Invariant::BalanceNeverBelow {
                    slot: SPEND_SLOT,
                    floor: 50,
                },
                ["web.fetch"],
            )
            .unwrap();

        // A conforming turn (slot stays >= floor) is admitted by the KERNEL gate.
        sub.evaluate_transition(
            &state_with_slot(2, SPEND_SLOT, 100),
            Some(&state_with_slot(1, SPEND_SLOT, 100)),
        )
        .expect("a conforming turn must be admitted");

        // A violating turn (slot drops below the floor) is REFUSED — a real
        // ConstraintViolated the executor reproduces, for the child's whole life.
        let err = sub
            .evaluate_transition(
                &state_with_slot(2, SPEND_SLOT, 10),
                Some(&state_with_slot(1, SPEND_SLOT, 100)),
            )
            .expect_err("a violating turn must be refused by the executor");
        assert!(matches!(err, ProgramError::ConstraintViolated { .. }));

        // The kind id is a stable content-addressed digest (a listing pins it).
        assert_eq!(sub.kind_id(), sub.kind.kind_id());
    }

    #[test]
    fn a_subagents_caps_are_a_strict_attenuation() {
        let g = genesis();
        let sub = g
            .mint_subagent(
                "cell:sub-1",
                "u:sub-1",
                Invariant::MonotoneField { slot: 1 },
                ["web.fetch", "web.search"], // 2 of the parent's 4 facets
            )
            .unwrap();

        // Structurally strict: within the parent bundle, and strictly fewer.
        assert!(sub.is_strict_attenuation());

        // CRYPTOGRAPHICALLY strict: the real rail confers exactly the two granted
        // facets — and NONE of the dropped parent facets.
        let mut perms = g.granted_permissions(&sub, 1_000);
        perms.sort();
        assert_eq!(
            perms,
            vec!["web.fetch".to_string(), "web.search".to_string()]
        );
        assert!(!perms.contains(&"pay.send".to_string()));
        assert!(!perms.contains(&"notes.write".to_string()));
    }

    #[test]
    fn a_subagent_cannot_be_endowed_beyond_the_parent_bundle() {
        let g = genesis();
        // "admin" is not in the genesis agent's bundle — amplification, refused.
        let err = g
            .mint_subagent(
                "cell:sub-x",
                "u:sub-x",
                Invariant::MonotoneField { slot: 1 },
                ["web.fetch", "admin"],
            )
            .expect_err("a facet outside the bundle must be refused");
        assert_eq!(
            err,
            HatchError::NotAttenuation {
                facet: "admin".into()
            }
        );
    }

    #[test]
    fn a_forged_kind_membership_is_rejected() {
        // The forge-detector rides along: a cell claiming the sub-agent's kind but
        // installing a program that OMITS the invariant is rejected.
        let g = genesis();
        let sub = g
            .mint_subagent(
                "cell:sub-1",
                "u:sub-1",
                Invariant::MonotoneField { slot: 1 },
                ["web.fetch"],
            )
            .unwrap();
        // The kind's own program conforms.
        sub.kind
            .attest_membership(&sub.kind.child_program)
            .expect("the kind's own program is a member");
        // An empty program cannot host an invariant-bearing kind — a forge.
        assert!(sub
            .kind
            .attest_membership(&dregg_cell::CellProgram::None)
            .is_err());
    }
}
