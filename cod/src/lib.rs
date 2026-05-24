//! Closable Overspending Detector for pyana shared resources.
//!
//! Scaffolding stub: this crate exists in the workspace so its
//! eventual API surface (close + detect on a shared budget) can be
//! wired in without later having to rearrange workspace membership.
//!
//! TODO: actual implementation. Today this is just `pub fn version()`
//! returning the crate's semver so `cargo check -p cod` is non-trivial.

/// Crate version (placeholder). Replaced when the real detector lands.
pub fn version() -> &'static str {
    env!("CARGO_PKG_VERSION")
}

#[cfg(test)]
mod tests {
    #[test]
    fn version_string_is_nonempty() {
        assert!(!super::version().is_empty());
    }
}
