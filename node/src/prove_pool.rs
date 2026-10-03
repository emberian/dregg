//! Async STARK-proving task pool — moves full-turn proof generation OFF the
//! request/commit path (red-team finding F-DOS-1, task #109).
//!
//! ## The problem this closes
//!
//! The submit/commit handlers used to run the full `p3-batch-stark` prover
//! (`stark::try_prove`, ~750 ms per turn — see
//! `circuit/tests/turn_revalidation_vs_prove.rs`) **inline, while holding the
//! global `state.write()` lock**. A single submitted turn therefore pinned a
//! worker in proving and froze the whole runtime behind the write lock: on the
//! public devnet the node stopped producing blocks for ~5 minutes and served 0
//! bytes until a `systemctl restart` (red-team `MULTINODE-BYZANTINE-FINDINGS`
//! F-DOS-1). The STARK proof was a **per-turn commit gate** it never needed to
//! be.
//!
//! ## The fix (soundness-preserving)
//!
//! Proofs are *additive attestation*, not a per-step soundness gate. The commit
//! path's job is to make sure the committed state is *correct*; the authoritative
//! executor (`execute_via_producer → Committed`) already validated the turn and
//! committed the new state BEFORE this pool ever runs. The commit therefore needs
//! no inline STARK proving or FRI-free re-check — the executor IS the soundness
//! boundary. The full STARK proof — the attestation layer light-clients and
//! cross-trust peers consume — is generated **asynchronously** by this pool,
//! OFF the write lock, and attached to the receipt when it lands.
//!
//! ## The ROTATED leg (PATH-PRESERVE Phase 5b cutover)
//!
//! This pool no longer proves a bespoke v1 hand-AIR STARK over a trace re-derived
//! from pre-state. It proves the SAME composed `FullTurnProof` the finalized
//! commit path proves (`turn_proving::prove_and_verify_finalized_turn`): the
//! effect-vm leg goes through the LEAN-emitted ROTATED descriptor (a multi-table
//! `Ir2BatchProof`) when the caller threaded the per-turn rotation witness from
//! the REAL before/after `dregg_cell::Cell`s, and self-verifies before it is
//! attached. Under `not(recursion)` (or when the cell is not a rotatable cohort
//! member) the byte-identical v1 leg runs INSIDE `prove_and_verify_finalized_turn`
//! — this pool never touches the v1 effect-vm hand-AIR.
//!
//! Soundness is preserved because the executor already validated and committed
//! the state; the async proof only enriches the receipt with the succinct,
//! self-verified attestation.
//!
//! ## Pool shape
//!
//! A bounded MPSC queue feeds a fixed set of `spawn_blocking` workers (proving
//! is CPU-bound, so it must run on the blocking pool, never an async worker).
//! When the queue is full the job is dropped with a logged warning — the commit
//! has ALREADY happened and is sound; a dropped attestation is a *liveness*
//! degradation of the proof-enrichment layer, never a *safety* problem, and is
//! self-healing (a later finalized-turn prove pass / verifier re-request can
//! regenerate it). This bounds memory and CPU under a proving flood instead of
//! letting it wedge the node — the exact failure mode F-DOS-1 described.
//!
//! ## Operator knobs
//!
//! * `DREGG_PROVE_WORKERS` — concurrent proving jobs (default 2). **`0` turns
//!   async proving OFF**: no worker is spawned, `enqueue` accepts nothing, and
//!   every committed receipt stays committed-but-unattested. That is the same
//!   sound state a dropped job leaves (see above), chosen up front by a node
//!   whose consumers never read the attestation. Each proof costs whole
//!   CPU-seconds (measured ~16-25 CPU-s per turn on a 24-thread laptop), so a
//!   chat-style node that only needs the executor's commit pays that for
//!   nothing.
//! * `DREGG_PROVE_THREADS` — the rayon threads ONE proof may use. Unset (or
//!   `0`): the process-global rayon pool, which is sized to every logical CPU,
//!   so each proof bursts across all of them. Set: proving runs inside a
//!   dedicated pool of that many threads named `dregg-prove-N`, shared by the
//!   workers. Unlike `RAYON_NUM_THREADS`, this bounds the async prover alone
//!   and leaves every other rayon user in the process at full width.
//! * `DREGG_PROVE_QUEUE_DEPTH` — queued jobs before new ones drop (default 256).

use std::sync::Arc;

use dregg_types::CellId;
use tokio::sync::mpsc;

use crate::state::NodeState;

/// A single async proving job: everything `prove_and_verify_finalized_turn` needs
/// to (re-)build + self-verify the committed turn's composed `FullTurnProof` off
/// the lock, plus the receipt hash to attach the resulting `WitnessedReceipt` to
/// once proving completes. The executor already validated + committed this turn;
/// the proof is additive attestation (see module docs).
pub struct ProveJob {
    /// The actor cell whose whole-turn transition is proven.
    pub agent: CellId,
    /// The actor cell's balance captured BEFORE the executor mutated the ledger
    /// (the pre-state the proof's `old_commit` binds to).
    pub pre_balance: u64,
    /// The actor cell's nonce captured before execution.
    pub pre_nonce: u64,
    /// The turn's effects (the same `turn.call_forest.total_effects()` the
    /// executor ran), marshalled onto the actor inside the prover.
    pub effects: Vec<dregg_turn::Effect>,
    /// The turn hash the proof is bound to (replay binding).
    pub turn_hash: [u8; 32],
    /// The per-turn ROTATION producer witness built from the REAL before/after
    /// actor cells. `Some` ⇒ the effect-vm leg proves through the rotated
    /// descriptor; `None` ⇒ the byte-identical v1 leg runs inside the prover
    /// (a non-cohort cell, or `not(recursion)`).
    pub rotation: Option<dregg_sdk::RotationTurnWitness>,
    /// The committed receipt the proof attests (moved into the WitnessedReceipt).
    pub receipt: dregg_turn::TurnReceipt,
    /// Receipt hash key under which to store the proven WitnessedReceipt.
    pub receipt_hash: [u8; 32],
    /// Hex turn hash, for log correlation only.
    pub turn_hash_hex: String,
}

/// Handle to the async prove pool. Cheaply cloneable (wraps an mpsc sender).
/// `tx` is `None` when proving is switched off (`DREGG_PROVE_WORKERS=0`).
#[derive(Clone)]
pub struct ProvePool {
    tx: Option<mpsc::Sender<ProveJob>>,
}

/// Default number of concurrent proving workers. Proving is CPU-bound; we keep
/// this small so a proving flood cannot starve the async runtime's blocking
/// pool of threads needed for other I/O. Override with `DREGG_PROVE_WORKERS`.
const DEFAULT_PROVE_WORKERS: usize = 2;

/// Bounded job-queue depth. Past this, new jobs are dropped (the commit already
/// succeeded — see module docs). Override with `DREGG_PROVE_QUEUE_DEPTH`.
const DEFAULT_QUEUE_DEPTH: usize = 256;

/// The pool's shape, read once at spawn. Parsed from a lookup function rather
/// than the process environment so the parsing is testable without mutating
/// global state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProveConfig {
    /// Concurrent proving jobs. `0` = async proving off.
    pub workers: usize,
    /// Queued jobs before new ones drop.
    pub queue_depth: usize,
    /// Rayon threads per proof; `None` = the process-global rayon pool.
    pub threads: Option<usize>,
}

impl ProveConfig {
    /// Read `DREGG_PROVE_WORKERS`, `DREGG_PROVE_QUEUE_DEPTH` and
    /// `DREGG_PROVE_THREADS` from the process environment.
    pub fn from_env() -> Self {
        Self::from_lookup(|k| std::env::var(k).ok())
    }

    /// Parse the knobs through `get`. An unparsable value falls back to the
    /// default, exactly as an unset one does.
    pub fn from_lookup(get: impl Fn(&str) -> Option<String>) -> Self {
        let parse = |k: &str| get(k).and_then(|v| v.trim().parse::<usize>().ok());
        Self {
            workers: parse("DREGG_PROVE_WORKERS").unwrap_or(DEFAULT_PROVE_WORKERS),
            queue_depth: parse("DREGG_PROVE_QUEUE_DEPTH")
                .filter(|&n| n > 0)
                .unwrap_or(DEFAULT_QUEUE_DEPTH),
            threads: parse("DREGG_PROVE_THREADS").filter(|&n| n > 0),
        }
    }
}

/// The dedicated rayon pool one proof runs inside when `DREGG_PROVE_THREADS`
/// is set. Every `par_iter`/`join` the prover makes while `install`ed here is
/// scheduled on these `n` threads instead of the global pool.
fn prover_threads(n: usize) -> Result<rayon::ThreadPool, rayon::ThreadPoolBuildError> {
    rayon::ThreadPoolBuilder::new()
        .num_threads(n)
        .thread_name(|i| format!("dregg-prove-{i}"))
        .build()
}

impl ProvePool {
    /// Spawn the worker set and return a handle. `state` is captured so a
    /// completed proof can be stored back under its receipt hash (a brief lock
    /// acquisition for the `push_witnessed_receipt` write only — never held
    /// across the proving itself).
    pub fn spawn(state: NodeState) -> Self {
        Self::spawn_with(state, ProveConfig::from_env())
    }

    /// [`Self::spawn`] with an explicit shape instead of the environment.
    pub fn spawn_with(state: NodeState, config: ProveConfig) -> Self {
        let ProveConfig {
            workers,
            queue_depth: depth,
            threads,
        } = config;
        if workers == 0 {
            tracing::info!(
                "async STARK proving OFF (DREGG_PROVE_WORKERS=0): committed receipts stay \
                 unattested; the executor's commit is unchanged"
            );
            return Self { tx: None };
        }
        // A pool that cannot be built (the OS refused a thread) degrades to the
        // global pool rather than refusing to prove: the bound is a cost knob.
        let prover = threads.and_then(|n| match prover_threads(n) {
            Ok(p) => Some(Arc::new(p)),
            Err(e) => {
                tracing::warn!(threads = n, error = %e, "dedicated prover pool not built; proving on the global rayon pool");
                None
            }
        });
        let (tx, rx) = mpsc::channel::<ProveJob>(depth);
        let rx = Arc::new(tokio::sync::Mutex::new(rx));

        for worker_id in 0..workers {
            let rx = rx.clone();
            let state = state.clone();
            let prover = prover.clone();
            tokio::spawn(async move {
                loop {
                    // Take the next job. The receiver mutex is held only across
                    // the `recv().await`, never across proving.
                    let job = {
                        let mut guard = rx.lock().await;
                        guard.recv().await
                    };
                    let Some(job) = job else {
                        tracing::debug!(worker_id, "prove pool channel closed; worker exiting");
                        return;
                    };
                    run_job(worker_id, job, &state, prover.clone()).await;
                }
            });
        }

        tracing::info!(
            workers,
            queue_depth = depth,
            prover_threads = prover.as_ref().map(|p| p.current_num_threads()),
            "async STARK prove pool started (proving moved OFF the commit/request path)"
        );
        Self { tx: Some(tx) }
    }

    /// Whether this pool proves at all (`false` under `DREGG_PROVE_WORKERS=0`).
    pub fn is_enabled(&self) -> bool {
        self.tx.is_some()
    }

    /// Enqueue a proving job. Returns `true` if the job was accepted into the
    /// queue, `false` if the queue is full (job dropped — the commit is already
    /// sound; see module docs). Never blocks the caller.
    pub fn enqueue(&self, job: ProveJob) -> bool {
        let Some(tx) = &self.tx else {
            tracing::debug!(turn_hash = %job.turn_hash_hex, "async proving OFF; receipt left unattested");
            return false;
        };
        let turn_hash = job.turn_hash_hex.clone();
        match tx.try_send(job) {
            Ok(()) => {
                // Loud (info-level) job-lifecycle line: the pool's only other
                // success logs were debug-level, so a healthy pipeline looked
                // identical to a dead one at the default RUST_LOG=info.
                tracing::info!(
                    turn_hash = %turn_hash,
                    "async prove job ENQUEUED (proof attaches to the receipt when it lands)"
                );
                true
            }
            Err(mpsc::error::TrySendError::Full(job)) => {
                crate::metrics::inc_async_proofs_dropped();
                tracing::warn!(
                    turn_hash = %job.turn_hash_hex,
                    "async prove queue full; dropping proof-attestation job (commit already \
                     succeeded + was witness-revalidated — proof can be regenerated later)"
                );
                false
            }
            Err(mpsc::error::TrySendError::Closed(_)) => {
                tracing::error!("async prove pool channel closed; cannot enqueue proof job");
                false
            }
        }
    }
}

/// Run one proving job on the blocking pool, then attach the resulting
/// `WitnessedReceipt` back into state under a brief write-lock acquisition.
async fn run_job(
    worker_id: usize,
    job: ProveJob,
    state: &NodeState,
    prover: Option<Arc<rayon::ThreadPool>>,
) {
    let ProveJob {
        agent,
        pre_balance,
        pre_nonce,
        effects,
        turn_hash,
        rotation,
        receipt,
        receipt_hash,
        turn_hash_hex,
    } = job;

    let started = std::time::Instant::now();

    // Proving is CPU-bound: run it on the blocking pool so it never stalls the
    // async runtime's I/O workers. CRUCIALLY, no state lock is held here.
    //
    // The composed `FullTurnProof` is generated + self-verified by the SAME
    // helper the finalized commit path uses; its effect-vm leg proves through the
    // LEAN-emitted ROTATED descriptor when a rotation witness was threaded (else
    // the byte-identical v1 leg runs inside the helper). The resulting
    // `WitnessedReceipt` is a scope-1 attestation (proof + composed PI): the
    // executor already committed the state, and the inline-trace replay bundle is
    // a v1-only Silver-Vision artifact the rotated leg does not carry.
    //
    // ⚑ NAMED RESIDUAL, wider than twin#12 and NOT closed by it (2026-07-26). This
    // path calls the plain v1 entry point UNCONDITIONALLY. It has no routing match
    // at all — no `actor_consumed_cap`, no `bearer_consumed_cap`, no
    // `spent_nullifiers` arm — so on the async HTTP commit path the AUTHORITY leg
    // is NEVER attached, for a cap-gated turn or a bearer-delegated one alike, and
    // the freshness leg is likewise absent. `blocklace_sync.rs`'s finalized commit
    // path (which DOES route, and now REFUSES to publish a bearer turn's proof when
    // the delegator root is unresolvable — `bearer_authority_disposition`) is the
    // only path where the routing exists. Closing this needs the pre-state ledger
    // context the job does not carry (`full_turn_pre_cell`, the delegator cap-root
    // snapshot, the canonical spent set), so it is a real piece of work, not an
    // oversight to patch here. Stated at its actual resolution rather than left for
    // the next reader to rediscover: an attestation minted on this path claims the
    // STATE TRANSITION and nothing about authority.
    let prove_result = tokio::task::spawn_blocking(move || {
        let prove = || {
            crate::turn_proving::prove_and_verify_finalized_turn(
                &agent,
                pre_balance,
                pre_nonce,
                &effects,
                turn_hash,
                rotation,
            )
        };
        let proven = match &prover {
            Some(pool) => pool.install(prove),
            None => prove(),
        }
        .map_err(|e| format!("async full-turn proof generation failed: {e}"))?;
        let proof_bytes = proven.proof_bytes().to_vec();
        let public_inputs_u32: Vec<u32> = proven
            .proof
            .composed
            .public_inputs
            .iter()
            .map(|f| f.as_u32())
            .collect();
        let witnessed = dregg_turn::WitnessedReceipt::from_components(
            receipt,
            proof_bytes,
            public_inputs_u32,
            None,
        );
        Ok::<_, String>(witnessed)
    })
    .await;

    let witnessed = match prove_result {
        Ok(Ok(w)) => w,
        Ok(Err(e)) => {
            crate::metrics::inc_async_proofs_failed();
            tracing::warn!(
                worker_id,
                turn_hash = %turn_hash_hex,
                error = %e,
                "async proof generation failed; receipt stays committed-but-unattested"
            );
            return;
        }
        Err(join_err) => {
            crate::metrics::inc_async_proofs_failed();
            tracing::warn!(
                worker_id,
                turn_hash = %turn_hash_hex,
                error = %join_err,
                "async proving task panicked/cancelled; receipt stays committed-but-unattested"
            );
            return;
        }
    };

    // Brief write-lock ONLY to store the finished attestation + clear pending.
    {
        let mut s = state.write().await;
        s.push_witnessed_receipt(receipt_hash, witnessed);
        s.clear_proof_pending(&receipt_hash);
    }
    crate::metrics::inc_async_proofs_completed();
    crate::metrics::record_async_proof_duration(started.elapsed().as_secs_f64());

    // Notify subscribers that the attestation for this receipt is now available.
    state.emit(crate::state::NodeEvent::Receipt {
        hash: turn_hash_hex.clone(),
    });

    // Info-level so the live pipeline is visibly healthy: this is the line
    // operators (and the quickstart) watch for after submitting a turn.
    tracing::info!(
        worker_id,
        turn_hash = %turn_hash_hex,
        elapsed_ms = started.elapsed().as_millis(),
        "async proof attached to committed receipt (has_proof flips true)"
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    fn config(vars: &[(&str, &str)]) -> ProveConfig {
        ProveConfig::from_lookup(|k| {
            vars.iter()
                .find(|(name, _)| *name == k)
                .map(|(_, v)| v.to_string())
        })
    }

    #[test]
    fn unset_knobs_keep_the_defaults_and_the_global_pool() {
        assert_eq!(
            config(&[]),
            ProveConfig {
                workers: DEFAULT_PROVE_WORKERS,
                queue_depth: DEFAULT_QUEUE_DEPTH,
                threads: None,
            }
        );
    }

    #[test]
    fn zero_workers_means_proving_off_not_the_default() {
        assert_eq!(config(&[("DREGG_PROVE_WORKERS", "0")]).workers, 0);
        assert_eq!(config(&[("DREGG_PROVE_WORKERS", "3")]).workers, 3);
        assert_eq!(
            config(&[("DREGG_PROVE_WORKERS", "many")]).workers,
            DEFAULT_PROVE_WORKERS
        );
    }

    #[test]
    fn zero_depth_and_zero_threads_fall_back() {
        let c = config(&[("DREGG_PROVE_QUEUE_DEPTH", "0"), ("DREGG_PROVE_THREADS", "0")]);
        assert_eq!(c.queue_depth, DEFAULT_QUEUE_DEPTH);
        assert_eq!(c.threads, None);
        assert_eq!(config(&[("DREGG_PROVE_THREADS", " 4 ")]).threads, Some(4));
    }

    #[test]
    fn installed_prover_pool_bounds_parallel_work_to_its_own_threads() {
        use rayon::prelude::*;
        let pool = prover_threads(2).expect("pool");
        let (width, names): (usize, Vec<String>) = pool.install(|| {
            let names = (0..256)
                .into_par_iter()
                .map(|_| std::thread::current().name().unwrap_or("").to_string())
                .collect();
            (rayon::current_num_threads(), names)
        });
        assert_eq!(width, 2);
        assert!(
            names.iter().all(|n| n.starts_with("dregg-prove-")),
            "parallel work escaped the prover pool: {names:?}"
        );
    }

    #[tokio::test]
    async fn zero_workers_spawns_a_pool_that_accepts_nothing() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        let off = ProvePool::spawn_with(state.clone(), config(&[("DREGG_PROVE_WORKERS", "0")]));
        assert!(!off.is_enabled());
        let on = ProvePool::spawn_with(state, config(&[("DREGG_PROVE_WORKERS", "1")]));
        assert!(on.is_enabled());
    }
}
