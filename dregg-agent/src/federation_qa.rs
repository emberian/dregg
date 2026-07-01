//! `federation_qa` — **FEDERATION-ATTESTED QA**: an operator-independent proof
//! that a QA verdict is real.
//!
//! ## The residual this closes
//!
//! [`verify_witnessed_qa`](crate::agent::verify_witnessed_qa) (Layer 3) re-executes
//! a [`WitnessedRun`](crate::agent::WitnessedRun)'s bound `(command, code_root)`
//! and rejects a verdict the execution does not reproduce. But that re-execution
//! runs in **the same compute substrate** that produced the verdict. So Layer 3
//! proves "*this substrate* ran these tests on this code with this result" — not
//! that the result is **operator-independent**. A single lying operator whose
//! substrate is rigged to both record *and* re-reproduce a fabricated verdict is
//! not caught by a re-run in that same substrate.
//!
//! ## The fix: a quorum of independent operators
//!
//! The QA verdict is submitted to a quorum of independent operators. **Each
//! operator re-executes the bound `(command, code_root)` on its OWN substrate**,
//! gets its own `(exit, output_digest)`, and **signs that result**. A quorum
//! (e.g. threshold-3 of n=4) agreeing on the *same* `(exit, output_digest)` is the
//! **attested verdict** — a [`QuorumCert`], the same shape as the turn-finality
//! quorum certificate (`qc_votes` over a checkpoint in the live node API). Because
//! the operators are independent, a single lying operator's forged/divergent result
//! is **outvoted** by the honest majority *and* **detected** (its signed-but-divergent
//! attestation is evidence, not noise). Two operators backed by the rust and lean
//! executors respectively re-running the same QA and agreeing carries the
//! **rust↔lean differential** cross-check down to the QA layer.
//!
//! ## What this is TODAY — a primitive, not yet wired to remote nodes
//!
//! This module is the **quorum-QA primitive**: the signed-attestation type
//! ([`OperatorAttestation`]), the operator identity + re-exec oracle ([`Operator`]),
//! the quorum tally, and the fail-closed [`verify_quorum_cert`]. The verify LOGIC is
//! real and non-vacuous (ed25519-per-vote, threshold, dissenter naming). What does
//! **not** exist yet is the **remote wiring**: there is no code path that constructs a
//! [`Federation`] against real nodes over the network — [`Operator`]'s re-exec oracle is
//! an in-process closure, and the standalone census maps the intended federation onto
//! four node names (`edge` · `persvati` · `snoopy-lean` · `snoopy-rust`). The named
//! wiring step — an `Operator::remote(node_url, key)` that POSTs the [`WitnessedRun`] to
//! each node's re-exec endpoint and collects its signed `(exit, output_digest)` — is the
//! seam that turns this primitive into a live cross-machine quorum. Until then the quorum
//! is exercised in-process (the module's own tests build N keypairs + N oracles in one
//! process).
//!
//! So [`verify_quorum_cert`] proves: *a quorum of independent operators each
//! re-ran the declared tests on the declared code and agreed the result* —
//! operator-independent, no single substrate trusted.
//!
//! ## What each tooth bites
//!
//! - **honest quorum certifies** — every operator re-runs and agrees → the cert
//!   verifies, the verdict is attested ([`verify_quorum_cert`] → [`AttestedVerdict`]).
//! - **a lying operator is outvoted AND detected** — one operator's substrate
//!   returns a divergent result (a forged pass over a truly-failing suite, or
//!   vice-versa); the honest majority still certifies the true result, and the
//!   divergent operator is named in [`AttestedVerdict::divergent`] as evidence.
//! - **no quorum → refused** — when no single `(exit, output_digest)` reaches the
//!   threshold (the operators genuinely disagree), the verdict is **not** attested
//!   ([`QuorumError::NoQuorum`]); an un-attestable verdict is rejected fail-closed.
//! - **a forged attestation is rejected** — a co-signer's signature is bound to
//!   its `(command, code_root, exit, output_digest)`; tampering the payload after
//!   signing breaks the signature and the whole cert is refused
//!   ([`QuorumError::ForgedAttestation`]).
//!
//! ## The boundary — the deeper seam this does NOT close
//!
//! This is the **off-chain federation-attestation** half: operator-independence
//! via N independent re-runs + a quorum certificate. It does **not** make the
//! operators' re-execution *itself* in-circuit-witnessed — i.e. a pure light
//! client (rather than the operators) directly verifying that each re-run was
//! faithful. That deeper seam — the QA re-execution folded into the EffectVM /
//! recursion tree so a non-operator light client witnesses it — is the **swarm's
//! VK-epoch** (the in-circuit witness, the circuit-soundness lane). Here a verifier
//! still trusts that the federation operators are genuinely independent (distinct
//! keys, distinct substrates); the quorum makes *any single one* powerless to lie.

use crate::receipt::{BodyHasher, ReceiptSigner, verify_signature};

use crate::agent::{ReWitness, WitnessedRun};

// ---------------------------------------------------------------------------
// The signed-fact digest — what each operator's signature binds.
// ---------------------------------------------------------------------------

/// The domain-separated digest a federation operator signs: the bound
/// `(command, code_root)` it re-ran **and** the `(exit, output_digest)` its own
/// substrate produced. Binding all four means a co-signer cannot be replayed onto
/// a different QA, and tampering any field breaks its signature (caught by
/// [`verify_quorum_cert`]).
fn qa_result_hash(command: &str, code_root: &str, exit: i64, output_digest: &[u8; 32]) -> [u8; 32] {
    let mut h = BodyHasher::new(b"dregg-federation-qa-attestation-v1");
    h.field(command.as_bytes())
        .field(code_root.as_bytes())
        .u64(exit as u64)
        .field(output_digest);
    h.finalize()
}

// ---------------------------------------------------------------------------
// One operator's signed re-execution result.
// ---------------------------------------------------------------------------

/// A **signed re-execution result** by one independent federation operator — its
/// vote in the quorum. The operator re-ran the bound `(command, code_root)` on its
/// own substrate, got `(exit, output_digest)`, and signed
/// [`qa_result_hash`]`(command, code_root, exit, output_digest)` under its node
/// key. A *divergent* operator (a substrate that lies) still produces a perfectly
/// valid signature — over a *different* `(exit, output_digest)`; the quorum, not
/// the signature, is what outvotes it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OperatorAttestation {
    /// The federation node name (`edge` / `persvati` / `snoopy-lean` / `snoopy-rust`).
    pub operator: String,
    /// The operator's ed25519 public key (its federation identity).
    pub signer: [u8; 32],
    /// The command this operator re-executed (must equal the submitted run's).
    pub command: String,
    /// The code root this operator re-executed against (must equal the run's).
    pub code_root: String,
    /// The exit / failure count **this operator's** substrate produced (`0` = pass).
    pub exit: i64,
    /// The output digest **this operator's** substrate produced.
    pub output_digest: [u8; 32],
    /// ed25519 signature over `qa_result_hash(command, code_root, exit, output_digest)`.
    pub signature: Vec<u8>,
}

// ---------------------------------------------------------------------------
// An operator — a signing identity + an independent re-exec oracle.
// ---------------------------------------------------------------------------

/// An independent federation operator: a named signing identity plus its **own**
/// re-execution oracle (its substrate). [`re_execute`](Operator::re_execute) re-runs
/// a submitted [`WitnessedRun`] on this operator's substrate and signs the result.
///
/// The oracle is a supplied closure. The intended production oracle is the operator's
/// local tier run (`rewitness_run_tests` riding `crate::run_workload`) on its own node,
/// reached via the named-but-not-yet-built `Operator::remote(node_url, key)` wiring step
/// (see the module header) — today every caller (the crate's tests) supplies an
/// in-process closure. A *lying* operator is modelled by an oracle that returns a
/// divergent [`ReWitness`] — and it signs that divergence honestly (a valid signature
/// over a false result), exactly as a rigged substrate would.
pub struct Operator {
    name: String,
    signer: ReceiptSigner,
    rerun: Box<dyn Fn(&WitnessedRun) -> Option<ReWitness> + Send + Sync>,
}

impl Operator {
    /// A new operator named `name`, signing under `seed`, re-executing via `rerun`.
    /// `rerun` returns `None` when this operator cannot reproduce the run (no
    /// registered source for that `code_root`, or an execution error) — it then
    /// **abstains** (casts no vote) rather than guessing.
    pub fn new(
        name: impl Into<String>,
        seed: [u8; 32],
        rerun: impl Fn(&WitnessedRun) -> Option<ReWitness> + Send + Sync + 'static,
    ) -> Operator {
        Operator {
            name: name.into(),
            signer: ReceiptSigner::from_seed(seed),
            rerun: Box::new(rerun),
        }
    }

    /// The operator's federation identity (its public key).
    pub fn public(&self) -> [u8; 32] {
        self.signer.public()
    }

    /// The operator's node name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Re-execute `run` on this operator's substrate and **sign** the result, or
    /// `None` (abstain) if the substrate could not reproduce the run.
    fn re_execute(&self, run: &WitnessedRun) -> Option<OperatorAttestation> {
        let re = (self.rerun)(run)?;
        let signature = self.signer.sign_raw(&qa_result_hash(
            &run.command,
            &run.code_root,
            re.exit,
            &re.output_digest,
        ));
        Some(OperatorAttestation {
            operator: self.name.clone(),
            signer: self.signer.public(),
            command: run.command.clone(),
            code_root: run.code_root.clone(),
            exit: re.exit,
            output_digest: re.output_digest,
            signature,
        })
    }
}

// ---------------------------------------------------------------------------
// The quorum certificate — the same shape as turn-finality's QC.
// ---------------------------------------------------------------------------

/// A **quorum certificate over a QA result**: the bound run, the collected
/// per-operator attestations (agreeing + divergent), and the finality threshold.
/// Produced by [`Federation::attest`]; re-witnessed by [`verify_quorum_cert`]
/// against the known operator key set. The same multi-sig-over-a-fact shape the
/// turn-finality QC has (`qc_votes` meeting a threshold finalizes a checkpoint).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuorumCert {
    /// The command the federation was asked to re-attest.
    pub command: String,
    /// The code root the federation was asked to re-attest against.
    pub code_root: String,
    /// Every operator attestation collected (those agreeing on the certified
    /// result *and* any that diverged — kept as on-cert evidence).
    pub attestations: Vec<OperatorAttestation>,
    /// The finality threshold (the minimum agreeing operators for attestation).
    pub threshold: usize,
}

impl QuorumCert {
    /// The number of operators that cast a vote (re-ran + signed; abstainers excluded).
    pub fn votes(&self) -> usize {
        self.attestations.len()
    }
}

// ---------------------------------------------------------------------------
// The federation — the operator set + the threshold.
// ---------------------------------------------------------------------------

/// The live federation: the independent operators and the finality `threshold`
/// (e.g. 3-of-4). [`attest`](Federation::attest) fans a submitted QA verdict to
/// every operator (each re-runs on its own substrate + signs) and assembles the
/// [`QuorumCert`].
pub struct Federation {
    operators: Vec<Operator>,
    threshold: usize,
}

impl Federation {
    /// A federation over `operators` with finality `threshold`. Panics if
    /// `threshold` is `0` (a 0-of-n "quorum" would attest anything) or exceeds the
    /// operator count (unsatisfiable).
    pub fn new(operators: Vec<Operator>, threshold: usize) -> Federation {
        assert!(threshold > 0, "a quorum threshold must be positive");
        assert!(
            threshold <= operators.len(),
            "threshold {threshold} exceeds the {} operators",
            operators.len()
        );
        Federation {
            operators,
            threshold,
        }
    }

    /// The operator identity set `(name, public_key)` a verifier pins to re-witness
    /// a [`QuorumCert`] — the trust anchor [`verify_quorum_cert`] checks signatures
    /// against (an attestation from outside this set is not a federation vote).
    pub fn operator_set(&self) -> Vec<(String, [u8; 32])> {
        self.operators
            .iter()
            .map(|o| (o.name.clone(), o.public()))
            .collect()
    }

    /// The finality threshold.
    pub fn threshold(&self) -> usize {
        self.threshold
    }

    /// **Attest a QA verdict**: hand the submitted [`WitnessedRun`] to every
    /// operator, each of which re-executes the bound `(command, code_root)` on its
    /// own substrate and signs its result. Returns the [`QuorumCert`] of all cast
    /// votes (abstainers — operators that could not reproduce the run — are
    /// excluded). Whether the cert actually *attests* the verdict is decided
    /// independently by [`verify_quorum_cert`].
    pub fn attest(&self, run: &WitnessedRun) -> QuorumCert {
        let attestations = self
            .operators
            .iter()
            .filter_map(|op| op.re_execute(run))
            .collect::<Vec<_>>();
        QuorumCert {
            command: run.command.clone(),
            code_root: run.code_root.clone(),
            attestations,
            threshold: self.threshold,
        }
    }
}

// ---------------------------------------------------------------------------
// The attested verdict + the re-witness.
// ---------------------------------------------------------------------------

/// The result of re-witnessing a [`QuorumCert`]: the **operator-independent
/// verdict** a quorum agreed on, with the dissenters named.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttestedVerdict {
    /// The exit a quorum of independent operators agreed the re-execution produces.
    pub exit: i64,
    /// The output digest a quorum agreed on.
    pub output_digest: [u8; 32],
    /// How many independent operators agreed on the certified result (`>= threshold`).
    pub agreed: usize,
    /// The operators whose substrate signed a **different** result — outvoted, and
    /// surfaced as detected evidence of a lying / diverging operator. Empty on a
    /// unanimous federation.
    pub divergent: Vec<String>,
    /// The finality threshold the quorum met.
    pub threshold: usize,
    /// `true` iff the operator-independent verdict matches the *submitted* run's
    /// claimed `(exit, output_digest)` — i.e. the federation confirmed the
    /// submitter's own claim (not just *some* result). `false` flags a lying
    /// **submitter** whose claim the honest quorum refutes.
    pub matches_claim: bool,
}

impl AttestedVerdict {
    /// `true` iff the attested verdict is a pass (exit `0`).
    pub fn passed(&self) -> bool {
        self.exit == 0
    }
}

/// Why a [`QuorumCert`] failed to attest a QA verdict.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QuorumError {
    /// An attestation does not name the submitted `(command, code_root)` — it
    /// attests a *different* QA and cannot be counted toward this one.
    OffTopicAttestation {
        /// The dissenting operator.
        operator: String,
    },
    /// Two attestations were cast under the same operator identity (a stuffed
    /// cert — one operator, many votes). Each operator votes at most once.
    DuplicateOperator {
        /// The doubled operator.
        operator: String,
    },
    /// An attestation's signer is not in the pinned federation operator set — an
    /// outsider cannot contribute a federation vote.
    UnknownOperator {
        /// The unrecognized signer key.
        signer: [u8; 32],
    },
    /// An attestation's signature does not verify over its `(command, code_root,
    /// exit, output_digest)` — a forged / tampered vote. The whole cert is refused
    /// (a forgery cannot be laundered into a quorum).
    ForgedAttestation {
        /// The operator whose signature did not verify.
        operator: String,
    },
    /// No single `(exit, output_digest)` reached the threshold — the operators did
    /// not agree, so the verdict is **not attested** (refused fail-closed).
    NoQuorum {
        /// The largest agreeing block of operators (`< threshold`).
        best: usize,
        /// The threshold it failed to reach.
        threshold: usize,
    },
}

impl std::fmt::Display for QuorumError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            QuorumError::OffTopicAttestation { operator } => {
                write!(
                    f,
                    "{operator}: attestation names a different (command, code_root) than the submitted run"
                )
            }
            QuorumError::DuplicateOperator { operator } => {
                write!(
                    f,
                    "{operator}: voted more than once (a stuffed quorum cert)"
                )
            }
            QuorumError::UnknownOperator { signer } => {
                write!(
                    f,
                    "an attestation is signed by {}, not in the federation operator set",
                    hex8(signer)
                )
            }
            QuorumError::ForgedAttestation { operator } => {
                write!(
                    f,
                    "{operator}: the attestation signature does not verify over its result — forged / tampered"
                )
            }
            QuorumError::NoQuorum { best, threshold } => write!(
                f,
                "no quorum: the largest agreeing block is {best} operator(s), below the threshold {threshold} — the verdict is NOT attested"
            ),
        }
    }
}

impl std::error::Error for QuorumError {}

/// **Re-witness a quorum certificate** the way a non-witness does: given only the
/// cert, the submitted [`WitnessedRun`], and the pinned federation operator set,
/// confirm that a quorum of *independent* operators re-ran the declared tests on
/// the declared code and agreed the result. No single operator substrate is
/// trusted — that is the operator-independence this delivers.
///
/// It (1) checks every attestation is **for this run** (`command` + `code_root`),
/// is signed by a **known** operator, **once**, with a **valid signature** over
/// its result — any forged/tampered vote refuses the whole cert; then (2) groups
/// the valid votes by `(exit, output_digest)` and certifies the largest block iff
/// it meets the threshold. The dissenters (operators that signed a different
/// result) are **named** in [`AttestedVerdict::divergent`] — outvoted *and*
/// detected. Below threshold → [`QuorumError::NoQuorum`] (refused).
pub fn verify_quorum_cert(
    cert: &QuorumCert,
    run: &WitnessedRun,
    operator_set: &[(String, [u8; 32])],
    threshold: usize,
) -> Result<AttestedVerdict, QuorumError> {
    use std::collections::BTreeSet;

    let mut seen: BTreeSet<[u8; 32]> = BTreeSet::new();
    // Validate each attestation; tally votes per (exit, output_digest).
    // (exit, output_digest) → (count, operators) — BTreeMap keeps it order-stable.
    let mut tally: std::collections::BTreeMap<(i64, Vec<u8>), Vec<String>> = Default::default();

    for a in &cert.attestations {
        // (1) it must attest THIS run.
        if a.command != run.command || a.code_root != run.code_root {
            return Err(QuorumError::OffTopicAttestation {
                operator: a.operator.clone(),
            });
        }
        // (2) the signer must be a known federation operator.
        if !operator_set.iter().any(|(_, pk)| pk == &a.signer) {
            return Err(QuorumError::UnknownOperator { signer: a.signer });
        }
        // (3) one vote per operator identity.
        if !seen.insert(a.signer) {
            return Err(QuorumError::DuplicateOperator {
                operator: a.operator.clone(),
            });
        }
        // (4) the signature must verify over the bound result — a forged / tampered
        // vote refuses the whole cert (a forgery cannot ride into a quorum).
        let digest = qa_result_hash(&a.command, &a.code_root, a.exit, &a.output_digest);
        if !verify_signature(&a.signer, &digest, &a.signature) {
            return Err(QuorumError::ForgedAttestation {
                operator: a.operator.clone(),
            });
        }
        tally
            .entry((a.exit, a.output_digest.to_vec()))
            .or_default()
            .push(a.operator.clone());
    }

    // The largest agreeing block.
    let Some(((exit, output_digest), agreeing)) = tally
        .iter()
        .max_by_key(|(_, ops)| ops.len())
        .map(|(k, v)| (k.clone(), v.clone()))
    else {
        return Err(QuorumError::NoQuorum { best: 0, threshold });
    };
    let agreed = agreeing.len();
    if agreed < threshold {
        return Err(QuorumError::NoQuorum {
            best: agreed,
            threshold,
        });
    }

    // The dissenters: every voting operator NOT in the certified block — outvoted,
    // and surfaced as detected divergence.
    let divergent = cert
        .attestations
        .iter()
        .filter(|a| (a.exit, a.output_digest.to_vec()) != (exit, output_digest.clone()))
        .map(|a| a.operator.clone())
        .collect::<Vec<_>>();

    let mut digest = [0u8; 32];
    digest.copy_from_slice(&output_digest);
    // Did the operator-independent result confirm the submitter's own claim?
    let matches_claim = run.exit == exit && run.output_digest == digest;

    Ok(AttestedVerdict {
        exit,
        output_digest: digest,
        agreed,
        divergent,
        threshold,
        matches_claim,
    })
}

/// First 8 hex chars of a key — a short identifier for error messages.
fn hex8(b: &[u8; 32]) -> String {
    let mut s = String::with_capacity(16);
    for x in &b[..8] {
        s.push_str(&format!("{x:02x}"));
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The submitted QA verdict under test: a green `run_tests` over a fixed code root.
    fn green_run() -> WitnessedRun {
        WitnessedRun {
            command: "run_tests[lang=wat,tier=Sandboxed,entry=run]".into(),
            code_root: "deadbeef-deployed-root".into(),
            exit: 0,
            output_digest: [7u8; 32],
        }
    }

    /// An honest operator whose substrate reproduces the run's own result.
    fn honest(name: &str, seed: u8) -> Operator {
        Operator::new(name, [seed; 32], |run| {
            Some(ReWitness {
                exit: run.exit,
                output_digest: run.output_digest,
            })
        })
    }

    /// An operator whose substrate LIES: it always reports a green pass with a
    /// fabricated digest, regardless of what the suite actually does.
    fn liar_pass(name: &str, seed: u8) -> Operator {
        Operator::new(name, [seed; 32], |_run| {
            Some(ReWitness {
                exit: 0,
                output_digest: [0xAA; 32],
            })
        })
    }

    /// The four live federation nodes, all honest, threshold 3-of-4.
    fn honest_federation() -> Federation {
        Federation::new(
            vec![
                honest("edge", 1),
                honest("persvati", 2),
                honest("snoopy-lean", 3),
                honest("snoopy-rust", 4),
            ],
            3,
        )
    }

    // ── TOOTH 1: an honest quorum CERTIFIES (operator-independent) ────────────

    #[test]
    fn an_honest_quorum_certifies_the_verdict() {
        let fed = honest_federation();
        let run = green_run();
        let cert = fed.attest(&run);
        assert_eq!(cert.votes(), 4, "all four operators re-ran and signed");

        let verdict = verify_quorum_cert(&cert, &run, &fed.operator_set(), fed.threshold())
            .expect("an honest unanimous federation attests the verdict");
        assert_eq!(verdict.agreed, 4, "all four agreed");
        assert!(
            verdict.divergent.is_empty(),
            "no dissent on a unanimous federation"
        );
        assert!(verdict.passed(), "the attested verdict is a pass");
        assert!(
            verdict.matches_claim,
            "the quorum confirmed the submitter's own claim"
        );
    }

    /// The quorum is operator-INDEPENDENT: it attests on the threshold even with
    /// one operator abstaining (its substrate could not reproduce the run).
    #[test]
    fn the_quorum_holds_with_an_abstainer_at_threshold() {
        let fed = Federation::new(
            vec![
                honest("edge", 1),
                honest("persvati", 2),
                honest("snoopy-lean", 3),
                // snoopy-rust cannot reproduce the run → abstains (no vote).
                Operator::new("snoopy-rust", [4; 32], |_| None),
            ],
            3,
        );
        let run = green_run();
        let cert = fed.attest(&run);
        assert_eq!(cert.votes(), 3, "the abstainer cast no vote");
        let verdict =
            verify_quorum_cert(&cert, &run, &fed.operator_set(), fed.threshold()).unwrap();
        assert_eq!(verdict.agreed, 3, "exactly the threshold agreed");
    }

    // ── TOOTH 2: a lying operator is OUTVOTED and DETECTED ────────────────────

    #[test]
    fn a_lying_operator_is_outvoted_and_detected() {
        // The suite TRULY FAILS (exit 3). Three honest operators reproduce the
        // failure; one operator's substrate LIES, signing a green pass.
        let run = WitnessedRun {
            command: "run_tests[lang=wat,tier=Sandboxed,entry=run]".into(),
            code_root: "deployed-root".into(),
            exit: 3,
            output_digest: [3u8; 32],
        };
        let fed = Federation::new(
            vec![
                honest("edge", 1),
                honest("persvati", 2),
                honest("snoopy-lean", 3),
                liar_pass("snoopy-rust", 4), // rigged substrate: always "green"
            ],
            3,
        );
        let cert = fed.attest(&run);
        assert_eq!(cert.votes(), 4);

        let verdict = verify_quorum_cert(&cert, &run, &fed.operator_set(), fed.threshold())
            .expect("the honest majority still certifies");
        // The HONEST result (the real failure) is certified, not the liar's pass.
        assert_eq!(verdict.exit, 3, "the true failing result is certified");
        assert!(
            !verdict.passed(),
            "the liar did not flip the verdict to green"
        );
        assert_eq!(
            verdict.agreed, 3,
            "the three honest operators outvote the liar"
        );
        // The lying operator is DETECTED — named as evidence.
        assert_eq!(
            verdict.divergent,
            vec!["snoopy-rust".to_string()],
            "the liar is flagged"
        );
        assert!(
            verdict.matches_claim,
            "the certified result matches the honest submission"
        );
    }

    /// Symmetric: a truly GREEN suite with one operator lying that it FAILED is
    /// still certified green, and the saboteur is detected.
    #[test]
    fn a_false_failure_vote_is_outvoted_and_detected() {
        let run = green_run();
        let fed = Federation::new(
            vec![
                honest("edge", 1),
                honest("persvati", 2),
                honest("snoopy-lean", 3),
                // a saboteur signing a fabricated failure.
                Operator::new("snoopy-rust", [4; 32], |_| {
                    Some(ReWitness {
                        exit: 9,
                        output_digest: [0xFF; 32],
                    })
                }),
            ],
            3,
        );
        let cert = fed.attest(&run);
        let verdict =
            verify_quorum_cert(&cert, &run, &fed.operator_set(), fed.threshold()).unwrap();
        assert!(verdict.passed(), "the green verdict survives the saboteur");
        assert_eq!(verdict.agreed, 3);
        assert_eq!(verdict.divergent, vec!["snoopy-rust".to_string()]);
    }

    // ── TOOTH 3: no quorum → REFUSED ──────────────────────────────────────────

    #[test]
    fn no_quorum_is_refused() {
        // The federation splits 2–2: no result reaches the 3-of-4 threshold.
        let run = green_run();
        let fed = Federation::new(
            vec![
                honest("edge", 1),
                honest("persvati", 2),
                liar_pass("snoopy-lean", 3), // its own (0, 0xAA..) result
                Operator::new("snoopy-rust", [4; 32], |_| {
                    Some(ReWitness {
                        exit: 0,
                        output_digest: [0xAA; 32],
                    })
                }),
            ],
            3,
        );
        // edge+persvati agree on (0, [7;32]); the other two agree on (0, [0xAA;32]).
        let cert = fed.attest(&run);
        let err = verify_quorum_cert(&cert, &run, &fed.operator_set(), fed.threshold())
            .expect_err("a split federation attests nothing");
        assert!(
            matches!(
                err,
                QuorumError::NoQuorum {
                    best: 2,
                    threshold: 3
                }
            ),
            "{err}"
        );
    }

    /// Too many abstainers (only a sub-threshold block can vote) → refused.
    #[test]
    fn below_threshold_votes_are_refused() {
        let fed = Federation::new(
            vec![
                honest("edge", 1),
                honest("persvati", 2),
                Operator::new("snoopy-lean", [3; 32], |_| None),
                Operator::new("snoopy-rust", [4; 32], |_| None),
            ],
            3,
        );
        let run = green_run();
        let cert = fed.attest(&run);
        assert_eq!(cert.votes(), 2, "only two operators could re-run");
        let err =
            verify_quorum_cert(&cert, &run, &fed.operator_set(), fed.threshold()).unwrap_err();
        assert!(
            matches!(
                err,
                QuorumError::NoQuorum {
                    best: 2,
                    threshold: 3
                }
            ),
            "{err}"
        );
    }

    // ── TOOTH 4: a forged attestation refuses the whole cert ──────────────────

    #[test]
    fn a_forged_attestation_is_rejected() {
        let fed = honest_federation();
        let run = green_run();
        let mut cert = fed.attest(&run);
        // Tamper one operator's signed result AFTER it signed → signature breaks.
        cert.attestations[0].exit = 1;
        let err = verify_quorum_cert(&cert, &run, &fed.operator_set(), fed.threshold())
            .expect_err("a tampered attestation refuses the cert");
        assert!(
            matches!(err, QuorumError::ForgedAttestation { .. }),
            "{err}"
        );
    }

    /// An attestation from a signer outside the federation set is rejected.
    #[test]
    fn an_outsider_attestation_is_rejected() {
        let fed = honest_federation();
        let run = green_run();
        let mut cert = fed.attest(&run);
        // An outsider re-signs a (validly-signed) attestation under an unknown key.
        let outsider = ReceiptSigner::from_seed([99u8; 32]);
        let digest = qa_result_hash(&run.command, &run.code_root, 0, &[7u8; 32]);
        cert.attestations.push(OperatorAttestation {
            operator: "imposter".into(),
            signer: outsider.public(),
            command: run.command.clone(),
            code_root: run.code_root.clone(),
            exit: 0,
            output_digest: [7u8; 32],
            signature: outsider.sign_raw(&digest),
        });
        let err = verify_quorum_cert(&cert, &run, &fed.operator_set(), fed.threshold())
            .expect_err("an outsider is not a federation operator");
        assert!(matches!(err, QuorumError::UnknownOperator { .. }), "{err}");
    }

    /// A stuffed cert — one operator voting twice — is rejected.
    #[test]
    fn a_doubled_operator_vote_is_rejected() {
        let fed = honest_federation();
        let run = green_run();
        let mut cert = fed.attest(&run);
        cert.attestations.push(cert.attestations[0].clone());
        let err = verify_quorum_cert(&cert, &run, &fed.operator_set(), fed.threshold())
            .expect_err("one operator cannot vote twice");
        assert!(
            matches!(err, QuorumError::DuplicateOperator { .. }),
            "{err}"
        );
    }

    // ── A lying SUBMITTER (not operator) is refuted by the honest quorum ──────

    #[test]
    fn a_lying_submitter_claim_is_refuted_by_the_quorum() {
        // The submitter CLAIMS green (exit 0), but the suite truly fails: every
        // honest operator reproduces exit 5. The quorum certifies exit 5, and the
        // attested verdict does NOT match the submitter's claim.
        let claimed = WitnessedRun {
            command: "run_tests[x]".into(),
            code_root: "root".into(),
            exit: 0, // the submitter's false claim
            output_digest: [0u8; 32],
        };
        let fed = Federation::new(
            vec![
                Operator::new("edge", [1; 32], |_| {
                    Some(ReWitness {
                        exit: 5,
                        output_digest: [5; 32],
                    })
                }),
                Operator::new("persvati", [2; 32], |_| {
                    Some(ReWitness {
                        exit: 5,
                        output_digest: [5; 32],
                    })
                }),
                Operator::new("snoopy-lean", [3; 32], |_| {
                    Some(ReWitness {
                        exit: 5,
                        output_digest: [5; 32],
                    })
                }),
                Operator::new("snoopy-rust", [4; 32], |_| {
                    Some(ReWitness {
                        exit: 5,
                        output_digest: [5; 32],
                    })
                }),
            ],
            3,
        );
        let cert = fed.attest(&claimed);
        let verdict =
            verify_quorum_cert(&cert, &claimed, &fed.operator_set(), fed.threshold()).unwrap();
        assert_eq!(
            verdict.exit, 5,
            "the operator-independent result is the real failure"
        );
        assert!(
            !verdict.matches_claim,
            "the submitter's green claim is refuted by the quorum"
        );
    }

    // ── a degenerate operator set is rejected at construction ─────────────────

    #[test]
    #[should_panic(expected = "positive")]
    fn a_zero_threshold_is_rejected() {
        Federation::new(vec![honest("edge", 1)], 0);
    }

    #[test]
    #[should_panic(expected = "exceeds")]
    fn an_unsatisfiable_threshold_is_rejected() {
        Federation::new(vec![honest("edge", 1)], 2);
    }
}
