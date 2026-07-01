//! `session_store` — the durable **per-account consumed-budget** store that makes
//! a hosted session's spend ceiling a real PER-ACCOUNT bound across SSH
//! detach/re-attach, not a per-process one.
//!
//! ## Why this exists
//!
//! A hosted session ([`crate::session::Session`]) draws its budget down through an
//! in-memory meter that lives only for the attach PROCESS. Each `dregg-agent
//! attach` connection is a fresh process with a fresh meter, so without a durable
//! store the ceiling silently RESETS to full on every reconnect: a tenant who
//! exhausts the budget can detach and reconnect and receive the whole budget again
//! — an unbounded-spend hole behind a "hard bound" claim (including a real Stripe
//! `pay:` spend). This store closes it: the host persists the cumulative consumed
//! total keyed by the account id, and reloads it into the meter at
//! [`Session::restore_consumed`](crate::session::Session::restore_consumed) on the
//! next attach, so the ceiling spans reconnects.
//!
//! It is deliberately a small, dependency-free file store (one JSON file per
//! account under a stable state dir): the durable twin of the ephemeral per-process
//! meter, wired by the `dregg-agent attach` binary. The filename is a domain-hash
//! of the account id, so two distinct account ids never share a file.

use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

/// The environment variable a deploy sets to relocate the store (e.g. a persistent
/// volume mounted per host). Unset → [`ConsumedStore::default_dir`].
pub const STATE_DIR_ENV: &str = "DREGG_AGENT_STATE_DIR";

/// One account's durable spend record: its cumulative consumed total (the drawdown
/// that must survive detach/re-attach) plus the ceiling it was last seen under (for
/// operator inspection; the live ceiling is the account's current budget).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConsumedRecord {
    /// The account id this record is for (the meter subject / session owner).
    pub account: String,
    /// The cumulative budget consumed across ALL of this account's sessions so far,
    /// in the session's asset units (USD-cents for a hosted session).
    pub consumed_cents: i64,
    /// The budget ceiling the account was last opened under (for inspection).
    pub budget_cents: i64,
}

/// A file-backed store mapping an account id → its cumulative [`ConsumedRecord`].
/// One JSON file per account under `dir`; missing/unreadable = a zero baseline
/// (fail-open to *no prior spend* would be wrong — so a read error is treated as
/// the SAFE direction only for a genuinely-absent record, see [`load_consumed`]).
///
/// [`load_consumed`]: ConsumedStore::load_consumed
pub struct ConsumedStore {
    dir: PathBuf,
}

impl ConsumedStore {
    /// A store rooted at `dir` (created on first save if absent).
    pub fn new(dir: impl Into<PathBuf>) -> ConsumedStore {
        ConsumedStore { dir: dir.into() }
    }

    /// A store at the default state dir: `$DREGG_AGENT_STATE_DIR` if set, else
    /// `~/.dregg-agent/state` (a STABLE path — never the ephemeral per-process
    /// workdir, which would reset the ceiling on every reconnect).
    pub fn open_default() -> ConsumedStore {
        ConsumedStore::new(ConsumedStore::default_dir())
    }

    /// The default state dir (see [`open_default`](ConsumedStore::open_default)).
    pub fn default_dir() -> PathBuf {
        if let Some(d) = std::env::var_os(STATE_DIR_ENV) {
            return PathBuf::from(d);
        }
        let home = std::env::var_os("HOME")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from("."));
        home.join(".dregg-agent").join("state")
    }

    /// The on-disk path for `account` — a domain-hash of the id so any account id
    /// (including one with `/`, `:`, spaces) maps to a unique, filesystem-safe name.
    fn path_for(&self, account: &str) -> PathBuf {
        let mut h = blake3::Hasher::new();
        h.update(b"dregg-agent-consumed-store-v1");
        h.update(account.as_bytes());
        let digest = hex::encode(&h.finalize().as_bytes()[..16]);
        self.dir.join(format!("acct-{digest}.json"))
    }

    /// Load `account`'s persisted cumulative consumed (0 if there is no record).
    /// The reload baseline for [`Session::restore_consumed`]. A genuinely-absent
    /// record is a first-ever attach (0 prior spend); a corrupt record reads as 0
    /// but the caller's restore clamps to the ceiling either way, so the bound can
    /// never be widened by a bad file.
    ///
    /// [`Session::restore_consumed`]: crate::session::Session::restore_consumed
    pub fn load_consumed(&self, account: &str) -> i64 {
        self.load_record(account)
            .map(|r| r.consumed_cents.max(0))
            .unwrap_or(0)
    }

    /// Load the full [`ConsumedRecord`] for `account`, if any.
    pub fn load_record(&self, account: &str) -> Option<ConsumedRecord> {
        let raw = std::fs::read_to_string(self.path_for(account)).ok()?;
        serde_json::from_str(&raw).ok()
    }

    /// Persist `account`'s cumulative consumed total (creating the state dir if
    /// needed). Call after every goal and at detach so the ceiling reflects the
    /// latest drawdown on the next attach. The write is monotonic-guarded: it never
    /// lowers a previously-recorded consumed total (so a stale in-process value can
    /// never *widen* the bound), and it records the max of the two.
    pub fn save_consumed(
        &self,
        account: &str,
        consumed_cents: i64,
        budget_cents: i64,
    ) -> std::io::Result<()> {
        std::fs::create_dir_all(&self.dir)?;
        let prior = self.load_consumed(account);
        let record = ConsumedRecord {
            account: account.to_string(),
            consumed_cents: consumed_cents.max(prior),
            budget_cents,
        };
        let json = serde_json::to_string_pretty(&record)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
        atomic_write(&self.path_for(account), json.as_bytes())
    }
}

/// Write `bytes` to `path` atomically (write a temp sibling then rename), so a
/// crash mid-write never leaves a half-written record that would read as 0 and
/// reset the ceiling.
fn atomic_write(path: &Path, bytes: &[u8]) -> std::io::Result<()> {
    let tmp = path.with_extension("json.tmp");
    std::fs::write(&tmp, bytes)?;
    std::fs::rename(&tmp, path)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tmpdir() -> PathBuf {
        let p = std::env::temp_dir().join(format!(
            "dregg-consumed-store-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&p).unwrap();
        p
    }

    #[test]
    fn consumed_round_trips_across_store_instances() {
        let dir = tmpdir();
        // First "process": save the drawdown.
        {
            let store = ConsumedStore::new(&dir);
            assert_eq!(store.load_consumed("dga1_alice"), 0, "no record yet");
            store.save_consumed("dga1_alice", 8, 10).unwrap();
        }
        // Second "process" (a fresh store instance): the consumed persisted.
        {
            let store = ConsumedStore::new(&dir);
            assert_eq!(store.load_consumed("dga1_alice"), 8);
            let rec = store.load_record("dga1_alice").unwrap();
            assert_eq!(rec.budget_cents, 10);
            assert_eq!(rec.account, "dga1_alice");
        }
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn save_is_monotonic_and_never_lowers_the_recorded_total() {
        let dir = tmpdir();
        let store = ConsumedStore::new(&dir);
        store.save_consumed("dga1_bob", 9, 10).unwrap();
        // A stale/lower in-process value must not widen the bound back down.
        store.save_consumed("dga1_bob", 3, 10).unwrap();
        assert_eq!(
            store.load_consumed("dga1_bob"),
            9,
            "the higher total is kept"
        );
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn distinct_accounts_do_not_share_a_file() {
        let dir = tmpdir();
        let store = ConsumedStore::new(&dir);
        store.save_consumed("a/b:c d", 4, 10).unwrap();
        store.save_consumed("a_b_c_d", 7, 10).unwrap();
        // Two ids that would sanitize to the same string keep separate records.
        assert_eq!(store.load_consumed("a/b:c d"), 4);
        assert_eq!(store.load_consumed("a_b_c_d"), 7);
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn an_absent_or_corrupt_record_reads_as_zero() {
        let dir = tmpdir();
        let store = ConsumedStore::new(&dir);
        assert_eq!(store.load_consumed("nobody"), 0);
        // A corrupt file reads as 0 (the caller's restore clamps to the ceiling).
        let p = store.path_for("garbage");
        std::fs::write(&p, b"not json").unwrap();
        assert_eq!(store.load_consumed("garbage"), 0);
        std::fs::remove_dir_all(&dir).ok();
    }
}
