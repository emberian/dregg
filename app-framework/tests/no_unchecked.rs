//! CI grep-guard: production framework source must never reference
//! `Authorization::Unchecked`.
//!
//! Background: the DSL audit (P0 #1) found that `EscrowManager` shipped every
//! turn it produced with `Authorization::Unchecked`, effectively making the
//! "managed escrow" framework unauthenticated. Stage 0f of the DSL redesign
//! introduces an `Authorizer` trait and removes every literal use of
//! `Unchecked` from production framework code.
//!
//! This test scans every `.rs` file under `app-framework/src/` and fails if
//! any of them mention `Authorization::Unchecked`. Tests, examples, and
//! application code can still use `Unchecked` if they want; only the
//! framework's *production* surface is fenced off.

use std::fs;
use std::path::{Path, PathBuf};

fn collect_rs_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = match fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return,
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_rs_files(&path, out);
        } else if path.extension().and_then(|s| s.to_str()) == Some("rs") {
            out.push(path);
        }
    }
}

#[test]
fn no_unchecked_authorization_in_framework_src() {
    let src_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src");
    assert!(
        src_dir.is_dir(),
        "expected src/ at {} to exist",
        src_dir.display()
    );

    let mut files = Vec::new();
    collect_rs_files(&src_dir, &mut files);
    assert!(
        !files.is_empty(),
        "no .rs files found under {}",
        src_dir.display()
    );

    // Substring we are scanning for. Use a runtime concatenation so this test
    // file itself does not contain the literal token (otherwise greps that
    // run over the whole crate would also flag this guard).
    let needle = ["Authorization", "::", "Unchecked"].concat();

    let mut offenders: Vec<(PathBuf, usize, String)> = Vec::new();
    for file in &files {
        let contents = match fs::read_to_string(file) {
            Ok(c) => c,
            Err(_) => continue,
        };
        for (lineno, line) in contents.lines().enumerate() {
            // Allow lines that are clearly documenting / fencing this off
            // (the docstring on the grep-guard helpers, and the placeholder
            // doc-comment in escrow.rs that explains why we *don't* use it).
            let trimmed = line.trim_start();
            if trimmed.starts_with("//") || trimmed.starts_with("///") {
                continue;
            }
            if line.contains(&needle) {
                offenders.push((file.clone(), lineno + 1, line.to_string()));
            }
        }
    }

    if !offenders.is_empty() {
        let mut msg = String::from(
            "framework source must not contain `Authorization::Unchecked`. Offenders:\n",
        );
        for (path, lineno, line) in &offenders {
            msg.push_str(&format!("  {}:{}  {}\n", path.display(), lineno, line.trim()));
        }
        msg.push_str(
            "\nIf you need an unauthenticated action in framework code, use an \
             `Authorizer` that explicitly produces the variant you want \
             (e.g. a custom one with a loud name) instead of a literal \
             `Authorization::Unchecked` in production code.\n",
        );
        panic!("{msg}");
    }
}
