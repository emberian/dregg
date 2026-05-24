//! Agreement matrix + structured failure narration.
//!
//! Each (predicate, input) pair becomes a [`RowReport`]: a map from backend
//! name to a [`BackendVerdict`]. When all non-`Skip` verdicts agree the row
//! is considered satisfied; otherwise the matrix records a structured
//! disagreement that the test harness panics with so CI can pinpoint the
//! offending backend.

use std::collections::BTreeMap;
use std::fmt;

/// Canonical backend identifier. We hold this as a `&'static str` rather
/// than an enum so the matrix scales as new backends are wired without a
/// pattern-match churn cycle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct BackendName(pub &'static str);

impl fmt::Display for BackendName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.0)
    }
}

/// Per-backend verdict for one (predicate, input) pair.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BackendVerdict {
    /// The backend's verifier ran and accepted.
    Accept,
    /// The backend's verifier ran and rejected.
    Reject,
    /// The backend cannot be verified in-process here. The `reason` is
    /// surfaced in disagreement reports so a reader can tell "this row had no
    /// say from gen_midnight because we don't bundle the Midnight proof
    /// server."
    Skip { reason: &'static str },
    /// The backend ran but produced a structured error (e.g. a generator
    /// rejected the input as out of range). Treated as a hard failure during
    /// agreement checking.
    Error(String),
}

impl BackendVerdict {
    pub fn is_terminal(&self) -> bool {
        matches!(self, Self::Accept | Self::Reject)
    }
}

impl fmt::Display for BackendVerdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Accept => f.write_str("Accept"),
            Self::Reject => f.write_str("Reject"),
            Self::Skip { reason } => write!(f, "Skip({reason})"),
            Self::Error(msg) => write!(f, "Error({msg})"),
        }
    }
}

/// One row of the agreement matrix: a single input fed to all backends.
pub struct RowReport {
    pub predicate: &'static str,
    pub input_label: String,
    pub verdicts: BTreeMap<BackendName, BackendVerdict>,
}

impl RowReport {
    pub fn new(predicate: &'static str, input_label: impl Into<String>) -> Self {
        Self {
            predicate,
            input_label: input_label.into(),
            verdicts: BTreeMap::new(),
        }
    }

    pub fn record(&mut self, backend: BackendName, verdict: BackendVerdict) {
        self.verdicts.insert(backend, verdict);
    }

    /// Returns `Ok(consensus)` if all terminal verdicts agree, otherwise
    /// `Err(reason)` with a human-readable description of who disagreed.
    pub fn check(&self) -> Result<BackendVerdict, String> {
        let mut accepts: Vec<BackendName> = Vec::new();
        let mut rejects: Vec<BackendName> = Vec::new();
        let mut errors: Vec<(BackendName, String)> = Vec::new();

        for (&name, verdict) in &self.verdicts {
            match verdict {
                BackendVerdict::Accept => accepts.push(name),
                BackendVerdict::Reject => rejects.push(name),
                BackendVerdict::Skip { .. } => {}
                BackendVerdict::Error(msg) => errors.push((name, msg.clone())),
            }
        }

        if !errors.is_empty() {
            let mut s = format!(
                "{} backend(s) errored on `{}` input {}:\n",
                errors.len(),
                self.predicate,
                self.input_label
            );
            for (name, msg) in errors {
                s.push_str(&format!("  - {name}: {msg}\n"));
            }
            return Err(s);
        }

        match (accepts.is_empty(), rejects.is_empty()) {
            (false, true) => Ok(BackendVerdict::Accept),
            (true, false) => Ok(BackendVerdict::Reject),
            (true, true) => {
                // No backend voted (everyone skipped). That's still a
                // problem — it means the predicate slipped through every
                // path without exercising anything.
                Err(format!(
                    "no backend produced a terminal verdict for `{}` input {}",
                    self.predicate, self.input_label
                ))
            }
            (false, false) => {
                let accept_list = accepts
                    .iter()
                    .map(|n| n.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                let reject_list = rejects
                    .iter()
                    .map(|n| n.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                Err(format!(
                    "DIFFERENTIAL DISAGREEMENT on predicate `{}`, input {}:\n  \
                     Accepted by: {accept_list}\n  Rejected by: {reject_list}\n",
                    self.predicate, self.input_label
                ))
            }
        }
    }
}

/// Full matrix across all (predicate, input) pairs run by the harness.
pub struct AgreementMatrix {
    rows: Vec<RowReport>,
}

impl Default for AgreementMatrix {
    fn default() -> Self {
        Self::new()
    }
}

impl AgreementMatrix {
    pub fn new() -> Self {
        Self { rows: Vec::new() }
    }

    pub fn push(&mut self, row: RowReport) {
        self.rows.push(row);
    }

    pub fn rows(&self) -> &[RowReport] {
        &self.rows
    }

    /// Render a compact human-readable summary: one row per (predicate,
    /// input) pair, with the consensus verdict, plus a breakdown of how many
    /// backends voted each way.
    pub fn summary(&self) -> String {
        let mut s = String::new();
        s.push_str(&format!(
            "Differential agreement matrix ({} rows)\n",
            self.rows.len()
        ));
        for row in &self.rows {
            let verdict = match row.check() {
                Ok(v) => format!("AGREE({v})"),
                Err(msg) => format!("DISAGREE\n{msg}"),
            };
            let mut accepts = 0usize;
            let mut rejects = 0usize;
            let mut skips = 0usize;
            for v in row.verdicts.values() {
                match v {
                    BackendVerdict::Accept => accepts += 1,
                    BackendVerdict::Reject => rejects += 1,
                    BackendVerdict::Skip { .. } => skips += 1,
                    BackendVerdict::Error(_) => {}
                }
            }
            s.push_str(&format!(
                "  {}::{:<24} accept={accepts:>2} reject={rejects:>2} skip={skips:>2}  {verdict}\n",
                row.predicate, row.input_label
            ));
        }
        s
    }

    /// Walk every row; collect every disagreement; panic with a single
    /// structured message if any are present.
    pub fn assert_all_agree(&self) {
        let mut failures: Vec<String> = Vec::new();
        for row in &self.rows {
            if let Err(msg) = row.check() {
                failures.push(format!(
                    "[{}] input {}\n{msg}",
                    row.predicate, row.input_label
                ));
            }
        }
        if !failures.is_empty() {
            panic!(
                "\n=== {} DIFFERENTIAL FAILURE(S) ===\n\n{}\n=== summary ===\n{}",
                failures.len(),
                failures.join("\n---\n"),
                self.summary(),
            );
        }
    }
}
